import Heliod.Platform

/-!
# Syntax of the Heliod core language

Follows the grammar in `typing.tex` (commands, expressions, function declarations), extended
with the async/await constructs from the hardware-concurrency section.

The syntax is parameterised by
* `K`  — peripheral kinds (see `Heliod.Platform`),
* `St` — peripheral state names,
* `R`  — the cost/frequency domain (an abstract ordered semiring, see `Heliod.CostModel`);
  it appears in the syntax only because `clock f` mentions a frequency `f ∈ ℚ⁺`.

## Design choices

* **First-order value types.**  The paper's `τ` includes function types
  `(τ₁, s⃗₁) → (τ₂, s⃗₂)` and puts functions (and, later, thread ids) into `Γ`.  Functions are
  only ever introduced by top-level declarations and only ever used in `let x = g(e, p)`, so we
  keep `Ty` first-order and give function signatures (and async-thread summaries) their
  own contexts in the typing judgment.  This avoids storing cost functions inside `Ty`.
* **Peripheral handles are variables.**  `transition(x, st)`, `match p with …`, calls and
  `async(p)` name a handle variable; its kind is recorded in the peripheral context `Δ`
  (see `Heliod.Contexts`), not in `Ty`.
* **Concrete binary operators.**  The paper leaves `binop : τ₁ × τ₂ → τ` abstract; we fix a
  small representative set with a typing table `BinOp.HasTy`.
* **`skip`.**  Not in the source grammar but used by the operational semantics
  (E-SeqDone, E-Assign, …) as the terminal command, so it is part of `Cmd`.
* **Match arms as a mutual inductive.**  `match p with st₁ → c₁ | … | stₙ → cₙ` is represented
  with a mutual `Arms` type rather than `List (St × Cmd)`, so that the typing judgment (which
  must join the outputs of all arms) can be a plain mutual inductive with a usable induction
  principle.
* **Timeouts are natural numbers** (`timeout[n]`); the paper's `n > 0` premise is not needed.
-/

/-- Program variables: ordinary variables, peripheral handles, and thread ids. -/
abbrev Var := String

/-- Function names. -/
abbrev FName := String

/-- Value types `τ ::= int | bool | unit`.

The paper's peripheral type `ρ` is **not** a value type here: peripheral handles are tracked
exclusively by the peripheral context `Δ` (which records each handle's kind and possible
states), so the paper's premise `Γ ⊢ x : ρ` becomes "`x` is bound in `Δ`".  Handles are never
values (no aliasing, no passing except as the dedicated peripheral argument of a call).
`K` is kept as a parameter so that function signatures and contexts share one index set. -/
inductive Ty (K : Type) where
  | int
  | bool
  | unit
  deriving DecidableEq, Repr

/-- Runtime values.  Peripheral handles are not first-class values: they are only ever
passed by name (rust-style ownership, no aliasing), so they have no `Val` form. -/
inductive Val where
  | int (n : Int)
  | bool (b : Bool)
  | unit
  deriving DecidableEq, Repr

/-- The type of a value. -/
def Val.ty {K : Type} : Val → Ty K
  | .int _ => .int
  | .bool _ => .bool
  | .unit => .unit

/-- Binary operators (a representative instance of the paper's abstract `binop`). -/
inductive BinOp where
  | add | sub | mul
  | eq | lt
  | and | or
  deriving DecidableEq, Repr

/-- Typing table for binary operators: `binop : τ₁ × τ₂ → τ`. -/
inductive BinOp.HasTy {K : Type} : BinOp → Ty K → Ty K → Ty K → Prop where
  | add : BinOp.HasTy .add .int .int .int
  | sub : BinOp.HasTy .sub .int .int .int
  | mul : BinOp.HasTy .mul .int .int .int
  | eq  : BinOp.HasTy .eq  .int .int .bool
  | lt  : BinOp.HasTy .lt  .int .int .bool
  | and : BinOp.HasTy .and .bool .bool .bool
  | or  : BinOp.HasTy .or  .bool .bool .bool

/-- Expressions `e ::= x | v | e₁ binop e₂`. -/
inductive Expr where
  | var (x : Var)
  | val (v : Val)
  | binop (op : BinOp) (e₁ e₂ : Expr)
  deriving DecidableEq, Repr

mutual

/-- Commands.

| constructor   | paper syntax                                   |
|---------------|------------------------------------------------|
| `skip`        | (terminal command of the semantics)            |
| `assign`      | `let x = e`                                    |
| `call`        | `let x = g(e, p)`                              |
| `ite`         | `if e then c₁ else c₂`                         |
| `transition`  | `transition(p, st)`                            |
| `downgrade`   | `downgrade(p, st)`                             |
| `clock`       | `clock f`                                      |
| `matchSt`     | `match p with st₁ → c₁ \| … \| stₙ → cₙ`       |
| `seq`         | `c₁; c₂`                                       |
| `async`       | `let tid = async(p) { c }`                     |
| `await`       | `await tid timeout[n] { c_fb }`                |
-/
inductive Cmd (St R : Type) where
  | skip
  | assign (x : Var) (e : Expr)
  | call (x : Var) (g : FName) (e : Expr) (p : Var)
  | ite (e : Expr) (c₁ c₂ : Cmd St R)
  | transition (p : Var) (st : St)
  | downgrade (p : Var) (st : St)
  | clock (f : R)
  | matchSt (p : Var) (arms : Arms St R)
  | seq (c₁ c₂ : Cmd St R)
  | async (tid : Var) (p : Var) (body : Cmd St R)
  | await (tid : Var) (n : Nat) (fb : Cmd St R)

/-- The arms `st₁ → c₁ | … | stₙ → cₙ` of a `match`. -/
inductive Arms (St R : Type) where
  | nil
  | cons (st : St) (c : Cmd St R) (rest : Arms St R)

end

/-- The set of states covered by a list of match arms, `{st₁, …, stₙ}`.  T-Match requires it
to contain every possible current state of the matched peripheral (exhaustiveness). -/
def Arms.states {St R : Type} [DecidableEq St] : Arms St R → Finset St
  | .nil => ∅
  | .cons st _ rest => insert st rest.states

/-- A function declaration

  `fn g(x, p) : (τ₁, s⃗₁) → (τ₂, s⃗₂) { c; ret := e }`.

`pKind` records the kind of the peripheral parameter `p` (implicit in the paper, where `p`'s
type is determined by the states `s⃗₁`, `s⃗₂` it is annotated with).  The checking system uses
the annotations `sIn = s⃗₁`, `sOut = s⃗₂`; inline typing (`TypedI`, `Heliod.Inference`) ignores them. -/
structure FunDecl (K St R : Type) where
  name : FName
  arg : Var
  argTy : Ty K
  parg : Var
  pKind : K
  sIn : Finset St
  retTy : Ty K
  sOut : Finset St
  body : Cmd St R
  ret : Expr

/-- A whole program: peripheral handles with their kind and initial state (the `s_curr` of
E-PeriphDecl), function declarations `d`, and a main command. -/
structure Program (K St R : Type) where
  periphs : List (Var × K × St)
  funs : List (FunDecl K St R)
  main : Cmd St R
