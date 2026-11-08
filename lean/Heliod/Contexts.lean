import Heliod.CostModel
import Mathlib.Data.Finsupp.Single
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Typing contexts and expression typing

* `TCtx` — the value typing context `Γ : x → τ`.
* `PCtx` — the peripheral context `Δ : p → s⃗` (with each handle's kind).
* `FCtx` — function declarations by name (used by the semantics to run bodies; typing uses
  signatures with cost summaries, `SigCtx` in `Heliod.Typing`).
* Expression typing `Γ ⊢ e : τ` and expression cost `q_e`.

## Design choices

* **`Δ` is finitely supported** (`Var →₀ PEntry`).  The paper's background cost `cost(Δ)` sums
  over every peripheral in `Δ`, so `Δ` must have finite domain; `Finsupp` gives this for free,
  together with `update` (`Δ[p : s⃗]`), `erase` (`Δ \ p`) and pointwise `zipWith` (the join).
* **Entries record the kind.**  `PEntry.live k S` says the handle is a peripheral of kind `k`
  currently in one of the states `S`.  Costs are per kind, so `cost(Δ)` is computable from `Δ`
  alone.  The async extension will add a `cap` (captured) entry.
* **Join on mismatch drops the handle.**  The join `Δ₁ ∪ Δ₂` (T-If, T-Match) unions state sets
  pointwise.  If the two sides disagree on whether/at which kind a handle is bound, the result
  is `absent`.  This case is unreachable for well-typed sync commands, since typing never
  changes the domain or kinds of `Δ` (to be proved as a lemma alongside soundness).
* **Expression cost is a function**, not part of the expression judgment: `q_e` depends only on
  the syntax of `e`, so separating it keeps `HasTy` a plain typing relation.
-/

variable {K St R : Type}

/-- Value typing context `Γ`: a partial map from variables to value types. -/
abbrev TCtx (K : Type) := Var → Option (Ty K)

namespace TCtx

/-- `Γ[x : τ]`. -/
def bind [DecidableEq K] (Γ : TCtx K) (x : Var) (τ : Ty K) : TCtx K :=
  Function.update Γ x (some τ)

/-- Lookup after `Γ[x : τ]`. -/
@[simp] theorem bind_apply [DecidableEq K] (Γ : TCtx K) (x : Var) (τ : Ty K) (y : Var) :
    Γ.bind x τ y = if y = x then some τ else Γ y :=
  Function.update_apply Γ x (some τ) y

/-- `Γ₁ ∩ Γ₂`: keep a binding only where both branches agree (T-If, T-Match). -/
def inter [DecidableEq K] (Γ₁ Γ₂ : TCtx K) : TCtx K :=
  fun x => if Γ₁ x = Γ₂ x then Γ₁ x else none

/-- The empty context `·`. -/
def empty : TCtx K := fun _ => none

end TCtx

/-- An entry of the peripheral context.  `absent` is the `Finsupp` zero (handle not bound);
`live k S` is a handle to a kind-`k` peripheral known to be in one of the states `S`. -/
inductive PEntry (K St : Type) where
  | absent
  | live (k : K) (S : Finset St)
  deriving DecidableEq

instance : Zero (PEntry K St) := ⟨.absent⟩

namespace PEntry

/-- Pointwise join used for `Δ₁ ∪ Δ₂`: union the possible states of a handle bound at the same
kind on both sides; anything else becomes `absent` (see the module doc). -/
def join [DecidableEq K] [DecidableEq St] : PEntry K St → PEntry K St → PEntry K St
  | .live k S, .live k' S' => if k = k' then .live k (S ∪ S') else .absent
  | _, _ => .absent

/-- The join of two absent entries is absent — the side condition `Finsupp.zipWith` needs. -/
theorem join_zero [DecidableEq K] [DecidableEq St] :
    join (0 : PEntry K St) 0 = 0 := rfl

/-- Background cost contributed by one entry: `max_{s ∈ S} cbₛ` for a live handle. -/
def bg [Zero R] [LinearOrder R] [OrderBot R] (M : CostModel K St R) : PEntry K St → R
  | .absent => 0
  | .live k S => M.maxBg k S

end PEntry

/-- Peripheral context `Δ`: a finitely supported map from handle variables to entries. -/
abbrev PCtx (K St : Type) := Var →₀ PEntry K St

namespace PCtx

/-- `Δ[p : S]` — set handle `p` (of kind `k`) to the possible states `S`. -/
noncomputable def set (Δ : PCtx K St) (p : Var) (k : K) (S : Finset St) : PCtx K St :=
  Δ.update p (.live k S)

/-- `Δ \ p` — remove handle `p` (used for `cost(Δ \ p)`).  Defined on `PCtx` (rather than using
`Finsupp.erase` directly) so the result stays typed as a `PCtx` for dot notation. -/
noncomputable def erase (Δ : PCtx K St) (p : Var) : PCtx K St :=
  Finsupp.erase p Δ

/-- `Δ₁ ∪ Δ₂` — the pointwise join of the outputs of two branches. -/
noncomputable def join [DecidableEq K] [DecidableEq St] (Δ₁ Δ₂ : PCtx K St) : PCtx K St :=
  Finsupp.zipWith PEntry.join PEntry.join_zero Δ₁ Δ₂

/-- `cost(Δ)` (unscaled): the sum over all bound handles of their worst-case background cost.
The judgment multiplies this by the current clock `f`.  `cost(Δ \ p)` is `(Δ.erase p).bg M`. -/
noncomputable def bg [CommSemiring R] [LinearOrder R] [OrderBot R]
    (M : CostModel K St R) (Δ : PCtx K St) : R :=
  Δ.sum (fun _ e => e.bg M)

/-! ### Computation lemmas

These let `simp` evaluate lookups and background costs of concrete contexts (used by the worked
examples) and are the basic rewriting facts for the soundness proof. -/

/-- Lookup after `Δ[p : S]`. -/
@[simp] theorem set_apply (Δ : PCtx K St) (p : Var) (k : K) (S : Finset St) (x : Var) :
    (Δ.set p k S) x = if x = p then .live k S else Δ x := by
  unfold PCtx.set; rw [Finsupp.update_apply]

/-- Lookup after `Δ \ p`. -/
@[simp] theorem erase_apply (Δ : PCtx K St) (p x : Var) :
    (Δ.erase p) x = if x = p then 0 else Δ x := by
  unfold PCtx.erase; exact Finsupp.erase_apply

/-- Lookup in a join is the join of the lookups. -/
@[simp] theorem join_apply [DecidableEq K] [DecidableEq St] (Δ₁ Δ₂ : PCtx K St) (x : Var) :
    (Δ₁.join Δ₂) x = PEntry.join (Δ₁ x) (Δ₂ x) :=
  rfl

/-- Removing a handle that was just set forgets the update. -/
@[simp] theorem erase_set_self (Δ : PCtx K St) (p : Var) (k : K) (S : Finset St) :
    (Δ.set p k S).erase p = Δ.erase p := by
  unfold PCtx.set PCtx.erase; exact Finsupp.erase_update_eq_erase Δ p _

/-- Removing one handle commutes with setting a different one. -/
@[simp] theorem erase_set_ne (Δ : PCtx K St) {p x : Var} (h : x ≠ p) (k : K) (S : Finset St) :
    (Δ.set x k S).erase p = (Δ.erase p).set x k S := by
  unfold PCtx.set PCtx.erase; exact Finsupp.erase_update_of_ne Δ (Ne.symm h) _

/-- Removing from the empty context. -/
@[simp] theorem erase_zero (p : Var) : PCtx.erase (0 : PCtx K St) p = 0 := by
  unfold PCtx.erase; exact Finsupp.erase_zero p

/-- Removing the only handle of a singleton context. -/
@[simp] theorem erase_single_self (p : Var) (e : PEntry K St) :
    PCtx.erase (Finsupp.single p e) p = 0 := by
  unfold PCtx.erase; exact Finsupp.erase_single

/-- Joining an entry with itself is the identity (state-set union is idempotent). -/
@[simp] theorem _root_.PEntry.join_self [DecidableEq K] [DecidableEq St] (e : PEntry K St) :
    PEntry.join e e = e := by
  cases e <;> simp [PEntry.join]

/-- Joining a context with itself is the identity — e.g. after an `if` whose branches leave
`Δ` unchanged. -/
@[simp] theorem join_self [DecidableEq K] [DecidableEq St] (Δ : PCtx K St) : Δ.join Δ = Δ := by
  ext x; simp

/-- Removing a handle commutes with the join.  Needed to compute `cost(Δ \ p)` right after an
`if`/`match`, e.g. for a transition that follows a branch. -/
@[simp] theorem erase_join [DecidableEq K] [DecidableEq St] (Δ₁ Δ₂ : PCtx K St) (p : Var) :
    (Δ₁.join Δ₂).erase p = (Δ₁.erase p).join (Δ₂.erase p) := by
  ext x; by_cases h : x = p <;> simp [h]

variable [CommSemiring R] [LinearOrder R] [OrderBot R]

/-- The empty context has no background cost. -/
@[simp] theorem bg_zero (M : CostModel K St R) : PCtx.bg M (0 : PCtx K St) = 0 :=
  Finsupp.sum_zero_index

/-- Background cost of a singleton context (the initial context of a function body). -/
@[simp] theorem bg_single (M : CostModel K St R) (p : Var) (e : PEntry K St) :
    PCtx.bg M (Finsupp.single p e) = e.bg M :=
  Finsupp.sum_single_index (h := fun _ (e : PEntry K St) => e.bg M) rfl

/-- Background cost after `Δ[p : S]` splits into `p`'s worst case plus `cost(Δ \ p)`.  This is
the accounting identity behind "each peripheral is charged exactly once". -/
@[simp] theorem bg_set (M : CostModel K St R) (Δ : PCtx K St) (p : Var) (k : K) (S : Finset St) :
    (Δ.set p k S).bg M = M.maxBg k S + (Δ.erase p).bg M := by
  unfold bg
  rw [← Finsupp.add_sum_erase' (Δ.set p k S) p (fun _ e => e.bg M) (fun _ => rfl), set_apply]
  simp only [↓reduceIte, PEntry.bg, PCtx.set, PCtx.erase, Finsupp.erase_update_eq_erase]

end PCtx

/-- Function context: the declarations visible to calls.  Built from a program's declaration
list; the semantics looks bodies up here (typing uses `SigCtx`). -/
abbrev FCtx (K St R : Type) := FName → Option (FunDecl K St R)

/-- The function context of a program: look a name up in the declaration list.  Shared by the
typing judgment and the semantics. -/
def Program.fctx (prog : Program K St R) : FCtx K St R :=
  fun g => prog.funs.find? (fun d => d.name == g)

/-- Expression typing `Γ ⊢ e : τ` (T-Var, a value rule the paper omits, and T-BinOp). -/
inductive HasTy (Γ : TCtx K) : Expr → Ty K → Prop where
  | var {x τ} : Γ x = some τ → HasTy Γ (.var x) τ
  | val {v} : HasTy Γ (.val v) v.ty
  | binop {op e₁ e₂ τ₁ τ₂ τ} :
      HasTy Γ e₁ τ₁ → HasTy Γ e₂ τ₂ → BinOp.HasTy op τ₁ τ₂ τ → HasTy Γ (.binop op e₁ e₂) τ

/-- Expression cost `q_e` (unscaled): one `varCost` per variable read, one `valCost` per
literal, one `binopCost op` per operator — the `q₁ + q₂` of T-BinOp plus the operator itself. -/
def Expr.cost (M : CostModel K St R) [Add R] : Expr → R
  | .var _ => M.varCost
  | .val _ => M.valCost
  | .binop op e₁ e₂ => M.binopCost op + e₁.cost M + e₂.cost M
