import Heliod.Contexts

/-!
# The checking type system (synchronous fragment)

Paper judgment (`typing.tex`, "checking resource analysis system"):

  `Γ, Δ, f ⊢ c : τ ⇒ Γ', Δ', q, f'`

Our judgment, `Typed P M Ψ Γ Δ c Γ' Δ' Q F`, reads: under platform `P`, cost model `M` and
function signatures `Ψ`, command `c` started with value context `Γ` and peripheral context `Δ`
ends with `Γ'`, `Δ'`; started at clock `f`, with ambient background `b`, it costs at most
`Q f b` and ends at clock `F f`.

## Cost summaries (how the paper's `β` / `cost(·)` holes are expressed)

The paper makes costs parametric in two things a command's *caller* decides:
* the clock frequency in force when it starts (all costs are scaled by `f`), and
* the background cost of peripherals that are live but invisible to the current function
  (`β : amb`, charged through `cost(·) = C(β, f)` and instantiated at the call site by
  `C(β, f)[β ↦ Δ] = Σ_{p ∈ Δ} cost(p)·f`, i.e. `q_f[Δ_b]`).

We express this parametricity directly: a derivation yields a **cost summary**
`Q : R → R → R` (entry clock `f`, unscaled ambient background `b`) and a **clock summary**
`F : R → R` (exit clock as a function of the entry clock).  A function declaration is typed
**once** (`FunDeclTyped`, the paper's T-FunDecl) and its summary is stored in its signature;
T-Call instantiates it by function application, `Q_g f (b + cost(Δ ∖ p))`, which is the paper's
`q_f[Δ ∖ p]`.  Summaries are exact pointwise: e.g. T-If takes `max (Q₁ f b) (Q₂ f b)` for each
`f, b`, so branches of different duration are not over-approximated.

## Other design choices / deviations from the paper

* **No command type `τ`.**  Every command has type `unit` in the paper; we drop it.
* **Clock-parametric function summaries** resolve the paper's ambiguity about which clock a body
  is typed at (T-FunDecl uses the declaration-site `f`, T-Call adopts the callee's `f_f`): the
  body's summary is a function of the caller's clock.
* **No recursion.**  Declarations are typed in order (`DeclsTyped`), each seeing only earlier
  signatures, so a function cannot call itself — consistent with the paper.
* **Callee peripheral states.**  The body is typed with its peripheral parameter at the declared
  input states `s⃗₁` (T-FunDecl's `Δ[p : s⃗₁]`); the caller must have `Δ(p) ⊆ s⃗₁` (T-Call's
  `s⃗ ⊆ s⃗₁`).  The paper requires the body's final states to *equal* `s⃗₂`; we require
  `⊆ s⃗₂` and set the caller's `Δ(p)` to `s⃗₂`, which is sound and slightly more permissive.
* **Costs are scaled by the clock** (`f * …`), including the expression cost `q_e`.  The cost of
  `clock f'` is `clockCost f f'` (already clock-dependent, so not scaled again) plus the scaled
  background.  The argument of a call is evaluated at the caller's clock, the return expression
  at the callee's exit clock.  Both are steps that also charge every peripheral's background
  (`f·(q_e + cost(Δ) + b)` in T-Call, `F f·(q_ret + cost(Δ_b) + b)` in T-FunDecl), like T-Let.
  The paper's E-Call/E-Ret are free; charging expression cost *without* background would leave
  time during which no peripheral is charged (found while proving `Accounting.lean`).
* **Transition / downgrade charge `cost(Δ ∖ p)`** for the background — the moved peripheral is
  charged its transition cost instead of its background cost, so it is never counted twice.
  Both require the target state to be `stable`: unstable targets are T-Transition-Unstable,
  part of the async extension.  (The paper's checking T-Downgrade omits `stable(st)`; its
  inference version has it.)
* **`let` targets are not handles** (`Δ x = 0`), so a value binding cannot shadow a peripheral.
* **T-Match** types arm `i` with `Δ[p : {stᵢ}]` (the paper's `Δ, p : stᵢ`), requires
  exhaustiveness `Δ(p) ⊆ {st₁,…,stₙ}`, and joins the arms with `∩`, `∪` and pointwise `max`.
  **Refinement over the paper:** only *reachable* arms (`stᵢ ∈ Δ(p)`) are typed and charged;
  the paper types and charges every arm, so an expensive arm for a state that cannot occur would
  inflate the bound.  Arms are typed by the mutual judgment `ArmsTyped`, which requires at least
  one reachable arm.
* **`skip`** costs nothing and changes nothing (it is the semantics' terminal command).
* **Clock positivity.**  `clock f'` requires `0 < f'` (the paper's `f' ∈ ℚ⁺`).
-/

variable {K St R : Type} [DecidableEq K] [DecidableEq St]

/-- A function signature `(τ₁, s⃗₁) →ᵏ (τ₂, s⃗₂) ! (Q, F)`: argument and return types, the kind
and input/output states of the peripheral parameter, and the function's cost and clock
summaries (see the module doc). -/
structure FunSig (K St R : Type) where
  argTy : Ty K
  pKind : K
  sIn : Finset St
  retTy : Ty K
  sOut : Finset St
  cost : R → R → R
  clk : R → R

/-- Signature context: the functions in scope for typing (the paper keeps them in `Γ`). -/
abbrev SigCtx (K St R : Type) := FName → Option (FunSig K St R)

variable [CommSemiring R] [LinearOrder R] [OrderBot R]

mutual

/-- Command typing `Γ, Δ ⊢ c ⇒ Γ', Δ'; Q; F` (see the module doc). -/
inductive Typed (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtx K St R) :
    TCtx K → PCtx K St → Cmd St R → TCtx K → PCtx K St → (R → R → R) → (R → R) → Prop where
  /-- `skip` is free. -/
  | skip {Γ Δ} : Typed P M Ψ Γ Δ .skip Γ Δ (fun _ _ => 0) (fun f => f)
  /-- T-Let: `q_e + cost(Δ) + cost(·)`, scaled by `f`. -/
  | assign {Γ Δ x e τ} :
      HasTy Γ e τ → Δ x = 0 →
      Typed P M Ψ Γ Δ (.assign x e) (Γ.bind x τ) Δ
        (fun f b => f * (e.cost M + Δ.bg M + b)) (fun f => f)
  /-- T-If: both branches from the same contexts; join outputs; pointwise `max`. -/
  | ite {Γ Δ e c₁ c₂ Γ₁ Δ₁ Q₁ F₁ Γ₂ Δ₂ Q₂ F₂} :
      HasTy Γ e .bool →
      Typed P M Ψ Γ Δ c₁ Γ₁ Δ₁ Q₁ F₁ →
      Typed P M Ψ Γ Δ c₂ Γ₂ Δ₂ Q₂ F₂ →
      Typed P M Ψ Γ Δ (.ite e c₁ c₂) (Γ₁.inter Γ₂) (Δ₁.join Δ₂)
        (fun f b => max (Q₁ f b) (Q₂ f b) + f * (e.cost M + Δ.bg M + b))
        (fun f => max (F₁ f) (F₂ f))
  /-- T-Transition (stable target): every possible source state must be `≤ st`. -/
  | transition {Γ Δ p k S st} :
      Δ p = .live k S → P.stable k st → (∀ s ∈ S, P.le k s st) →
      Typed P M Ψ Γ Δ (.transition p st) Γ (Δ.set p k {st})
        (fun f b => f * (M.maxTrans k S st + (Δ.erase p).bg M + b)) (fun f => f)
  /-- T-Downgrade: every possible source state must be allowed to downgrade to `st` by `D`. -/
  | downgrade {Γ Δ p k S st} :
      Δ p = .live k S → P.stable k st → (∀ s ∈ S, P.dg k s st) →
      Typed P M Ψ Γ Δ (.downgrade p st) Γ (Δ.set p k {st})
        (fun f b => f * (M.maxTrans k S st + (Δ.erase p).bg M + b)) (fun f => f)
  /-- T-Clock: `cost(f, f') + cost(Δ) + cost(·)`; the new clock is `f'`. -/
  | clock {Γ Δ f'} :
      0 < f' →
      Typed P M Ψ Γ Δ (.clock f') Γ Δ
        (fun f b => M.clockCost f f' + f * (Δ.bg M + b)) (fun _ => f')
  /-- T-Seq: thread contexts; the second command starts at the first one's exit clock. -/
  | seq {Γ Δ c₁ c₂ Γ₁ Δ₁ Q₁ F₁ Γ₂ Δ₂ Q₂ F₂} :
      Typed P M Ψ Γ Δ c₁ Γ₁ Δ₁ Q₁ F₁ →
      Typed P M Ψ Γ₁ Δ₁ c₂ Γ₂ Δ₂ Q₂ F₂ →
      Typed P M Ψ Γ Δ (.seq c₁ c₂) Γ₂ Δ₂
        (fun f b => Q₁ f b + Q₂ (F₁ f) b) (fun f => F₂ (F₁ f))
  /-- T-Match: exhaustive arms, each typed with `p` narrowed to its state.  The `match` step's
  own background is charged per arm (inside `ArmsTyped`), with `p` narrowed too. -/
  | matchSt {Γ Δ p k S arms Γ' Δ' Q F} :
      Δ p = .live k S → S ⊆ arms.states →
      ArmsTyped P M Ψ Γ Δ p k S arms Γ' Δ' Q F →
      Typed P M Ψ Γ Δ (.matchSt p arms) Γ' Δ' Q F
  /-- T-Call: instantiate the callee's summary; the caller's other peripherals `Δ ∖ p` join
  the callee's ambient background (the paper's `q_f[Δ ∖ p]`). -/
  | call {Γ Δ x g e p sig S} :
      Ψ g = some sig →
      HasTy Γ e sig.argTy →
      Δ x = 0 →
      Δ p = .live sig.pKind S → S ⊆ sig.sIn →
      Typed P M Ψ Γ Δ (.call x g e p) (Γ.bind x sig.retTy) (Δ.set p sig.pKind sig.sOut)
        (fun f b => f * (e.cost M + Δ.bg M + b) + sig.cost f (b + (Δ.erase p).bg M)) sig.clk

/-- Typing of the arms of `match p with …`, where `p` has kind `k` and possible states `S`: the
joined result of the **reachable** arms (those whose state is in `S`).  Unreachable arms are
skipped — they are neither typed nor charged.  At least one reachable arm is required.

* `cons`: a reachable arm, joined with the rest;
* `last`: a reachable arm after which every remaining arm is unreachable;
* `skip`: an unreachable arm (`st ∉ S`), ignored.

Each reachable arm's summary includes the `match` step itself, `f·(cost(Δ[p : {st}]) + b)`:
when that arm runs, `p` is in state `st`, so its background is charged at `st` rather than at
the worst state of `S`.  (Charging `f·(cost(Δ) + b)` outside the `max` would be sound but could
exceed every arm's actual cost; see `IMPRECISION.md`.) -/
inductive ArmsTyped (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtx K St R) :
    TCtx K → PCtx K St → Var → K → Finset St → Arms St R →
    TCtx K → PCtx K St → (R → R → R) → (R → R) → Prop where
  | last {Γ Δ p k S st c rest Γ' Δ' Q F} :
      st ∈ S →
      Typed P M Ψ Γ (Δ.set p k {st}) c Γ' Δ' Q F →
      (∀ s ∈ rest.states, s ∉ S) →
      ArmsTyped P M Ψ Γ Δ p k S (.cons st c rest) Γ' Δ'
        (fun f b => Q f b + f * ((Δ.set p k {st}).bg M + b)) F
  | cons {Γ Δ p k S st c rest Γ₁ Δ₁ Q₁ F₁ Γ₂ Δ₂ Q₂ F₂} :
      st ∈ S →
      Typed P M Ψ Γ (Δ.set p k {st}) c Γ₁ Δ₁ Q₁ F₁ →
      ArmsTyped P M Ψ Γ Δ p k S rest Γ₂ Δ₂ Q₂ F₂ →
      ArmsTyped P M Ψ Γ Δ p k S (.cons st c rest) (Γ₁.inter Γ₂) (Δ₁.join Δ₂)
        (fun f b => max (Q₁ f b + f * ((Δ.set p k {st}).bg M + b)) (Q₂ f b))
        (fun f => max (F₁ f) (F₂ f))
  | skip {Γ Δ p k S st c rest Γ' Δ' Q F} :
      st ∉ S →
      ArmsTyped P M Ψ Γ Δ p k S rest Γ' Δ' Q F →
      ArmsTyped P M Ψ Γ Δ p k S (.cons st c rest) Γ' Δ' Q F

end

/-- T-FunDecl: `d` has signature `sig` if its body types from its argument and its peripheral
parameter at the declared input states, its return expression has the declared type, its
peripheral ends within the declared output states, and the summaries are the body's (plus the
cost of evaluating the return expression at the exit clock). -/
structure FunDeclTyped (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtx K St R)
    (d : FunDecl K St R) (sig : FunSig K St R) : Prop where
  argTy : sig.argTy = d.argTy
  pKind : sig.pKind = d.pKind
  sIn : sig.sIn = d.sIn
  retTy : sig.retTy = d.retTy
  sOut : sig.sOut = d.sOut
  body : ∃ Γb Δb Qb Fb S',
    Typed P M Ψ (TCtx.empty.bind d.arg d.argTy) (Finsupp.single d.parg (.live d.pKind d.sIn))
      d.body Γb Δb Qb Fb ∧
    HasTy Γb d.ret d.retTy ∧ Δb d.parg = .live d.pKind S' ∧ S' ⊆ d.sOut ∧
    sig.cost = (fun f b => Qb f b + Fb f * (d.ret.cost M + Δb.bg M + b)) ∧ sig.clk = Fb

/-- Typing a list of declarations in order, extending the signature context with each one.
A function's body sees only the functions declared before it. -/
inductive DeclsTyped (P : Platform K St) (M : CostModel K St R) :
    SigCtx K St R → List (FunDecl K St R) → SigCtx K St R → Prop where
  | nil {Ψ} : DeclsTyped P M Ψ [] Ψ
  | cons {Ψ d ds sig Ψ'} :
      FunDeclTyped P M Ψ d sig →
      DeclsTyped P M (Function.update Ψ d.name (some sig)) ds Ψ' →
      DeclsTyped P M Ψ (d :: ds) Ψ'

namespace Program

/-- The initial peripheral context: each declared handle in its initial state `s_curr`. -/
noncomputable def initPCtx (prog : Program K St R) : PCtx K St :=
  prog.periphs.foldr (fun h Δ => Δ.set h.1 h.2.1 {h.2.2}) 0

/-- A program is well typed with signatures `Ψ` and main summaries `Q`, `F`: function names are
distinct (so the typing's signatures and the semantics' declaration lookup agree), the
declarations type in order to `Ψ`, and `main` types from the empty value context and the
initial peripheral context.  Run at clock `f₀` with nothing ambient, it costs at most `Q f₀ 0`. -/
def Typed (P : Platform K St) (M : CostModel K St R) (prog : Program K St R)
    (Ψ : SigCtx K St R) (Γ' : TCtx K) (Δ' : PCtx K St) (Q : R → R → R) (F : R → R) : Prop :=
  (prog.funs.map (·.name)).Nodup ∧
  DeclsTyped P M (fun _ => none) prog.funs Ψ ∧
  _root_.Typed P M Ψ TCtx.empty prog.initPCtx prog.main Γ' Δ' Q F

end Program
