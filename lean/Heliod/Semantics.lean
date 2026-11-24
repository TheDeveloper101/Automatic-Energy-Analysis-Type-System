import Heliod.Contexts

/-!
# Big-step cost semantics (synchronous fragment)

`Eval M Ψ A σ S K c σ' S' q K'`: running command `c` in memory `σ`, with visible peripherals
`S`, ambient (invisible) peripherals `A` and clock `K`, terminates in memory `σ'`, peripherals
`S'`, clock `K'`, and costs exactly `q`.

## Relation to the paper's E-rules

The paper gives a small-step machine with a thread pool and frame stack, needed for async
(preemption, hardware steps).  For the synchronous fragment we use a big-step relation; the
frame machine comes with the async extension.  The costs follow the paper's E-rules:

| command      | cost charged                                          | paper            |
|--------------|-------------------------------------------------------|------------------|
| `let x = e`  | `K·(q_e + bg(S) + bg(A))`                             | E-Assign         |
| `if`         | `K·(q_e + bg(S) + bg(A))` + chosen branch              | E-IfTrue/False   |
| `transition` | `K·(cost(s, st) + bg(S ∖ p) + bg(A))`                 | E-Transition     |
| `downgrade`  | `K·(cost(s, st) + bg(S ∖ p) + bg(A))`                 | E-Downgrade      |
| `clock f'`   | `clockCost(K, f') + K·(bg(S) + bg(A))`                | E-Clock          |
| `match`      | `K·(bg(S) + bg(A))` + chosen arm                       | E-Match-i        |
| call         | `K·(q_e + bg(S) + bg(A))` + body + `K_b·(q_ret + bg(S_b) + bg(A_b))` | E-Call / E-Ret |
| `c₁; c₂`, `skip` | sum / `0`                                         | E-Seq / E-SeqDone|

## Design choices

* **Exact states.**  `S` maps each visible handle to its kind and *one* concrete state; the
  background cost `bg(S)` uses `bgCost` of that exact state (the paper's `bg(S)`).
* **Ambient peripherals `A`.**  A function body only sees its own peripheral parameter, but the
  caller's other peripherals still exist and draw background power.  The runtime counterpart of
  the paper's `β` is the multiset `A` of `(kind, state)` pairs of invisible peripherals; every
  step charges `bg(A)`.  A call evaluates the body with `A_body = A + entries(S ∖ p)`, mirroring
  T-Call's instantiation of the callee's summary at ambient background `b + cost(Δ ∖ p)`.
  Soundness bounds a run by the summary evaluated at `b = bg(A)`.
* **Per-frame memory.**  The paper's single memory `M` would let a callee's locals overwrite the
  caller's variables; here a call runs its body in a fresh memory `{x ↦ v}` and only the return
  value flows back (`σ[x ↦ r]`).
* **Expression evaluation is charged** (`K·q_e`), matching the typing rules; the paper's
  E-rules evaluate expressions for free.
* **No runtime typestate checks.**  As in the paper, `transition`/`downgrade` do not check the
  order or the downgrade policy at runtime — preventing invalid transitions is typing's job.
  Runtime failures that typing must rule out are modelled by the absence of a rule: an
  ill-typed expression, a missing function, a non-peripheral handle, or a `match` with no arm
  for the current state simply has no derivation.
* **Arm selection** takes the first arm whose state matches (`Arms.find?`).
-/

variable {K St R : Type}

/-! ### Values and expression evaluation -/

/-- Evaluation of binary operators; `none` on ill-typed operands. -/
def BinOp.eval : BinOp → Val → Val → Option Val
  | .add, .int a, .int b => some (.int (a + b))
  | .sub, .int a, .int b => some (.int (a - b))
  | .mul, .int a, .int b => some (.int (a * b))
  | .eq, .int a, .int b => some (.bool (decide (a = b)))
  | .lt, .int a, .int b => some (.bool (decide (a < b)))
  | .and, .bool a, .bool b => some (.bool (a && b))
  | .or, .bool a, .bool b => some (.bool (a || b))
  | _, _, _ => none

/-- A frame's value memory. -/
abbrev Mem := Var → Option Val

/-- `σ[x ↦ v]`. -/
def Mem.set (σ : Mem) (x : Var) (v : Val) : Mem := Function.update σ x (some v)

/-- The empty memory. -/
def Mem.empty : Mem := fun _ => none

/-- Expression evaluation (`M, S ⊢ e →* v` in the paper); `none` if stuck. -/
def Expr.eval (σ : Mem) : Expr → Option Val
  | .var x => σ x
  | .val v => some v
  | .binop op e₁ e₂ => do
      let v₁ ← e₁.eval σ
      let v₂ ← e₂.eval σ
      op.eval v₁ v₂

/-- The first arm of a `match` whose state is `s`. -/
def Arms.find? {R : Type} [DecidableEq St] (s : St) : Arms St R → Option (Cmd St R)
  | .nil => none
  | .cons st c rest => if st = s then some c else rest.find? s

/-! ### Runtime peripheral state -/

/-- Runtime entry for a handle: `at k s` — a kind-`k` peripheral currently in state `s`. -/
inductive REntry (K St : Type) where
  | absent
  | at (k : K) (s : St)
  deriving DecidableEq

instance : Zero (REntry K St) := ⟨.absent⟩

/-- Background cost of one runtime entry: `cb_s` of its exact state. -/
def REntry.bg [Zero R] (M : CostModel K St R) : REntry K St → R
  | .absent => 0
  | .at k s => M.bgCost k s

/-- The visible peripherals of a frame (the paper's peripheral map `S`). -/
abbrev RPeriphs (K St : Type) := Var →₀ REntry K St

namespace RPeriphs

/-- `S[p ↦ s]` for a kind-`k` handle `p`. -/
noncomputable def set (S : RPeriphs K St) (p : Var) (k : K) (s : St) : RPeriphs K St :=
  S.update p (.at k s)

/-- `S ∖ p`. -/
noncomputable def erase (S : RPeriphs K St) (p : Var) : RPeriphs K St :=
  Finsupp.erase p S

/-- `bg(S)`: total background cost of the visible peripherals in their current states. -/
noncomputable def bg [AddCommMonoid R] (M : CostModel K St R) (S : RPeriphs K St) : R :=
  S.sum (fun _ e => e.bg M)

/-- The `(kind, state)` pairs of all peripherals in `S`, forgetting their handle names — what
becomes ambient when `S` is hidden from a callee. -/
noncomputable def entries (S : RPeriphs K St) : Multiset (K × St) :=
  S.sum fun _ e =>
    match e with
    | .absent => 0
    | .at k s => {(k, s)}

end RPeriphs

/-- `bg(A)`: total background cost of the ambient (invisible) peripherals. -/
def ambBg [AddCommMonoid R] (M : CostModel K St R) (A : Multiset (K × St)) : R :=
  (A.map fun ks => M.bgCost ks.1 ks.2).sum

/-! ### Computation lemmas for runtime state (used by the soundness proof) -/

/-- Lookup after `σ[x ↦ v]`. -/
@[simp] theorem Mem.set_apply (σ : Mem) (x : Var) (v : Val) (y : Var) :
    σ.set x v y = if y = x then some v else σ y :=
  Function.update_apply σ x (some v) y

namespace RPeriphs

/-- Lookup after `S[p ↦ s]`. -/
@[simp] theorem set_apply (S : RPeriphs K St) (p : Var) (k : K) (s : St) (x : Var) :
    (S.set p k s) x = if x = p then .at k s else S x := by
  unfold RPeriphs.set; rw [Finsupp.update_apply]

/-- Lookup after `S ∖ p`. -/
@[simp] theorem erase_apply (S : RPeriphs K St) (p x : Var) :
    (S.erase p) x = if x = p then 0 else S x := by
  unfold RPeriphs.erase; rw [Finsupp.erase_apply]

/-- Setting a handle to the state it already has is a no-op.  Used in the `match` case of
soundness, where the arm runs with the matched peripheral's state made explicit. -/
theorem set_eq_self {S : RPeriphs K St} {p : Var} {k : K} {s : St} (h : S p = .at k s) :
    S.set p k s = S := by
  unfold RPeriphs.set; rw [← h]; exact Finsupp.update_self (f := S) (a := p)

end RPeriphs

/-- Ambient background cost is additive. -/
theorem ambBg_add [AddCommMonoid R] (M : CostModel K St R) (A₁ A₂ : Multiset (K × St)) :
    ambBg M (A₁ + A₂) = ambBg M A₁ + ambBg M A₂ := by
  simp [ambBg, Multiset.map_add, Multiset.sum_add]

/-- Hiding peripherals as ambient does not change their background cost:
`bg(entries S) = bg(S)`.  This is why the callee's ambient background at runtime,
`bg(A + entries(S ∖ p))`, matches T-Call's instantiation `b + cost(Δ ∖ p)`. -/
theorem ambBg_entries [AddCommMonoid R] (M : CostModel K St R) (S : RPeriphs K St) :
    ambBg M S.entries = S.bg M := by
  let H : Multiset (K × St) →+ R :=
    { toFun := ambBg M, map_zero' := by simp [ambBg], map_add' := ambBg_add M }
  have hH : ∀ a, H a = ambBg M a := fun _ => rfl
  change H (S.sum _) = _
  rw [map_finsuppSum]
  refine Finsupp.sum_congr (fun x _ => ?_)
  cases S x <;> (rw [hH]; simp [ambBg, REntry.bg])

/-- The call case of soundness: the callee's ambient cost is the caller's plus the background of
the caller's other peripherals. -/
theorem ambBg_add_entries [AddCommMonoid R] (M : CostModel K St R) (A : Multiset (K × St))
    (S : RPeriphs K St) : ambBg M (A + S.entries) = ambBg M A + S.bg M := by
  rw [ambBg_add, ambBg_entries]

/-! ### Big-step evaluation -/

variable [DecidableEq St] [CommSemiring R]

/-- Big-step cost semantics of commands (synchronous fragment).  See the module doc for the
cost of each rule. -/
inductive Eval (M : CostModel K St R) (Ψ : FCtx K St R) :
    Multiset (K × St) → Mem → RPeriphs K St → R → Cmd St R →
    Mem → RPeriphs K St → R → R → Prop where
  | skip {A σ S K} : Eval M Ψ A σ S K .skip σ S 0 K
  /-- E-Assign. -/
  | assign {A σ S K x e v} :
      e.eval σ = some v →
      Eval M Ψ A σ S K (.assign x e) (σ.set x v) S (K * (e.cost M + S.bg M + ambBg M A)) K
  /-- E-IfTrue. -/
  | iteTrue {A σ S K e c₁ c₂ σ' S' q K'} :
      e.eval σ = some (.bool true) →
      Eval M Ψ A σ S K c₁ σ' S' q K' →
      Eval M Ψ A σ S K (.ite e c₁ c₂) σ' S' (q + K * (e.cost M + S.bg M + ambBg M A)) K'
  /-- E-IfFalse. -/
  | iteFalse {A σ S K e c₁ c₂ σ' S' q K'} :
      e.eval σ = some (.bool false) →
      Eval M Ψ A σ S K c₂ σ' S' q K' →
      Eval M Ψ A σ S K (.ite e c₁ c₂) σ' S' (q + K * (e.cost M + S.bg M + ambBg M A)) K'
  /-- E-Transition. -/
  | transition {A σ S K p k s st} :
      S p = .at k s →
      Eval M Ψ A σ S K (.transition p st) σ (S.set p k st)
        (K * (M.transCost k s st + (S.erase p).bg M + ambBg M A)) K
  /-- E-Downgrade. -/
  | downgrade {A σ S K p k s st} :
      S p = .at k s →
      Eval M Ψ A σ S K (.downgrade p st) σ (S.set p k st)
        (K * (M.transCost k s st + (S.erase p).bg M + ambBg M A)) K
  /-- E-Clock. -/
  | clock {A σ S K f'} :
      Eval M Ψ A σ S K (.clock f') σ S (M.clockCost K f' + K * (S.bg M + ambBg M A)) f'
  /-- E-Seq / E-SeqDone, collapsed. -/
  | seq {A σ S K c₁ c₂ σ₁ S₁ q₁ K₁ σ₂ S₂ q₂ K₂} :
      Eval M Ψ A σ S K c₁ σ₁ S₁ q₁ K₁ →
      Eval M Ψ A σ₁ S₁ K₁ c₂ σ₂ S₂ q₂ K₂ →
      Eval M Ψ A σ S K (.seq c₁ c₂) σ₂ S₂ (q₁ + q₂) K₂
  /-- E-Match-i: run the arm for the peripheral's current state. -/
  | matchSt {A σ S K p arms k s c σ' S' q K'} :
      S p = .at k s → arms.find? s = some c →
      Eval M Ψ A σ S K c σ' S' q K' →
      Eval M Ψ A σ S K (.matchSt p arms) σ' S' (q + K * (S.bg M + ambBg M A)) K'
  /-- E-Call + E-Ret: the body runs in a fresh memory, seeing only its peripheral parameter
  (bound to `p`'s current state); the caller's other peripherals become ambient. -/
  | call {A σ S K x g e p d v k s σb Sb qb Kb r s'} :
      Ψ g = some d →
      e.eval σ = some v →
      S p = .at k s →
      Eval M Ψ (A + (S.erase p).entries) (Mem.empty.set d.arg v)
        (Finsupp.single d.parg (.at k s)) K d.body σb Sb qb Kb →
      d.ret.eval σb = some r →
      Sb d.parg = .at k s' →
      Eval M Ψ A σ S K (.call x g e p) (σ.set x r) (S.set p k s')
        (K * (e.cost M + S.bg M + ambBg M A) + qb
          + Kb * (d.ret.cost M + Sb.bg M + ambBg M (A + (S.erase p).entries))) Kb

namespace Program

/-- The initial runtime peripherals: each declared handle in its initial state. -/
noncomputable def initPeriphs (prog : Program K St R) : RPeriphs K St :=
  prog.periphs.foldr (fun h S => S.set h.1 h.2.1 h.2.2) 0

/-- Running a whole program from clock `K₀`: `main` in the empty memory with the declared
peripherals and nothing ambient. -/
def Eval (M : CostModel K St R) (prog : Program K St R) (K₀ : R)
    (σ' : Mem) (S' : RPeriphs K St) (q K' : R) : Prop :=
  _root_.Eval M prog.fctx 0 Mem.empty prog.initPeriphs K₀ prog.main σ' S' q K'

end Program
