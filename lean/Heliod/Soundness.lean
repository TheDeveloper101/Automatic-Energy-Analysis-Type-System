import Heliod.Typing
import Heliod.Semantics
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Soundness of the checking system (synchronous fragment)

**Status: complete, no `sorry`.**  `#print axioms` for `Program.soundness`, `Program.sigsValid`,
`eval_total` and `soundness` reports only `propext`, `Classical.choice`, `Quot.sound`.

Main results: `soundness` (cost bound for commands, given valid signatures), `eval_total`
(termination / type safety), `Program.sigsValid` (declarations typed in order yield valid
signatures), and `Program.soundness` (a well-typed program run from clock `K₀` costs at most
`Q K₀ 0`).

## Shape of the results

Cost summaries make the soundness statement *exact in its parameters*: if `c` has summaries
`Q, F` and runs from clock `K` with ambient peripherals `A`, then

  actual cost `≤ Q K (bg A)`  and  exit clock `≤ F K`.

A bound at a typed clock `f ≥ K` and an assumed ambient `b ≥ bg A` then follows from
**monotonicity** of summaries (`Typed.mono`), which is where `CostModel.WF` (monotonicity of
`clockCost` in its source frequency) is used.  Monotonicity is also needed *inside* the
soundness proof: in `c₁; c₂` the second command really starts at clock `K₁ ≤ F₁ K`.

## The invariant relating runtime states to typing contexts

* `MemOK Γ σ` — every variable typed by `Γ` holds a value of that type in `σ`.
* `PeriphsOK Δ S` — `S` and `Δ` bind the same handles, at the same kinds, and each handle's
  actual state is one of the states `Δ` allows.
* `SigsValid M Ψd Ψ` — every signature in `Ψ` is *valid* for the declaration `Ψd` runs: its
  body always terminates, ends in the declared output states, returns a value of the declared
  type, and costs at most the signature's summary (`SigValid`).  This replaces "the body's
  derivation is a sub-derivation of the call's": functions are typed once, at declaration,
  so the call case of soundness appeals to this invariant instead of the induction hypothesis.
  It is established declaration by declaration (`Program.sigsValid`).

## Proof plan for `soundness` (induction on the evaluation derivation, inverting typing)

* Primitive steps: the runtime cost is the summary at `(K, bg A)` with exact states in place of
  state sets: `transCost k s st ≤ maxTrans k S st`, `bg(S) ≤ bg(Δ)` (using `PeriphsOK`).
* `seq`: thread the invariant; use monotonicity of `Q₂` in its clock for `K₁ ≤ F₁ K`.
* `if` / `match`: the taken branch is bounded by its own summary, hence by the pointwise `max`;
  the final memory satisfies `Γᵢ` hence `Γ₁ ∩ Γ₂`; the final peripherals satisfy `Δᵢ` hence the
  join — this needs `Typed.shape_eq` (both branches keep the same handles and kinds).
* `call`: by `SigsValid`, the body's cost is `≤ Q_g K (bg A + bg(S ∖ p))` (its ambient is
  `A + entries(S ∖ p)`); then `bg(S ∖ p) ≤ bg(Δ ∖ p)` and monotonicity of `Q_g` in `b`.
-/

variable {K St R : Type} [DecidableEq K] [DecidableEq St]

/-! ### Runtime/typing agreement -/

/-- `σ ⊨ Γ`: every variable `Γ` types holds a value of that type. -/
def MemOK (Γ : TCtx K) (σ : Mem) : Prop :=
  ∀ x τ, Γ x = some τ → ∃ v, σ x = some v ∧ v.ty = τ

/-- A runtime entry is described by a typing entry: both absent, or same kind with the actual
state among the allowed ones. -/
def REntry.Approx : REntry K St → PEntry K St → Prop
  | .absent, .absent => True
  | .at k s, .live k' S => k = k' ∧ s ∈ S
  | _, _ => False

/-- `S ⊨ Δ`: pointwise agreement of the runtime peripherals with the peripheral context. -/
def PeriphsOK (Δ : PCtx K St) (S : RPeriphs K St) : Prop :=
  ∀ x, (S x).Approx (Δ x)

/-- The *shape* of a peripheral context: which handles are bound, and at which kind. -/
def PCtx.shape (Δ : PCtx K St) : Var → Option K :=
  fun x => match Δ x with
    | .absent => none
    | .live k _ => some k

variable [CommSemiring R] [LinearOrder R] [OrderBot R]
variable {P : Platform K St} {M : CostModel K St R}

/-- Summaries are monotone: a later clock never decreases the exit clock, and a faster entry
clock or a larger ambient background never decreases the cost bound. -/
def SummaryMono (Q : R → R → R) (F : R → R) : Prop :=
  Monotone F ∧ ∀ f f' b b', f ≤ f' → b ≤ b' → Q f b ≤ Q f' b'

/-- Semantic validity of signature `sig` for declaration `d` (functions looked up in `Ψd`):
from any argument of the declared type and any declared input state, at any clock `K` and with
any ambient peripherals `A`,
* the body always runs to completion (`total`), and
* every run returns a value of the declared type, leaves the peripheral in a declared output
  state, and costs (body plus return expression) at most `sig.cost K (bg A)`, exiting at a clock
  `≤ sig.clk K` (`bound`);
and the summaries are monotone (`mono`). -/
structure SigValid (M : CostModel K St R) (Ψd : FCtx K St R) (d : FunDecl K St R)
    (sig : FunSig K St R) : Prop where
  total : ∀ (A : Multiset (K × St)) K v s, v.ty = sig.argTy → s ∈ sig.sIn →
    ∃ σb Sb qb Kb, Eval M Ψd A (Mem.empty.set d.arg v)
      (Finsupp.single d.parg (.at sig.pKind s)) K d.body σb Sb qb Kb
  bound : ∀ (A : Multiset (K × St)) K v s σb Sb qb Kb, v.ty = sig.argTy → s ∈ sig.sIn →
    Eval M Ψd A (Mem.empty.set d.arg v) (Finsupp.single d.parg (.at sig.pKind s)) K
      d.body σb Sb qb Kb →
    ∃ r s', d.ret.eval σb = some r ∧ r.ty = sig.retTy ∧
      Sb d.parg = .at sig.pKind s' ∧ s' ∈ sig.sOut ∧
      qb + Kb * (d.ret.cost M + Sb.bg M + ambBg M A) ≤ sig.cost K (ambBg M A) ∧ Kb ≤ sig.clk K
  mono : SummaryMono sig.cost sig.clk

/-- Every signature in `Ψ` is valid for the declaration of the same name in `Ψd`. -/
def SigsValid (M : CostModel K St R) (Ψd : FCtx K St R) (Ψ : SigCtx K St R) : Prop :=
  ∀ g sig, Ψ g = some sig → ∃ d, Ψd g = some d ∧ SigValid M Ψd d sig

/-! ### Structural lemma -/

variable {Ψ : SigCtx K St R}

omit [DecidableEq K] [DecidableEq St] in
/-- Resetting a handle's state set does not change the shape: the shape of `Δ[p : S]` does not
depend on `S`.  Lets `ArmsTyped.shape_eq` compare arms narrowed to different states. -/
theorem PCtx.shape_set_set (Δ : PCtx K St) (p : Var) (k : K) (S S' : Finset St) :
    (Δ.set p k S).shape = (Δ.set p k S').shape := by
  funext x; by_cases h : x = p <;> simp [PCtx.shape, h]

omit [DecidableEq K] [DecidableEq St] in
/-- Resetting the state set of a handle already bound at kind `k` does not change the shape.
This covers `transition`, `downgrade`, `call` and the narrowing in `match`. -/
private theorem PCtx.shape_set_of {Δ : PCtx K St} {p : Var} {k : K} {S : Finset St}
    (hp : Δ p = .live k S) (S' : Finset St) : (Δ.set p k S').shape = Δ.shape := by
  funext x; by_cases h : x = p
  · subst h; simp [PCtx.shape, hp]
  · simp [PCtx.shape, h]

/-- Joining two contexts of the same shape keeps that shape (state sets are unioned, kinds agree).
The `if`/`match` cases of `shape_eq`. -/
private theorem PCtx.shape_join {Δ₁ Δ₂ : PCtx K St} (h : Δ₁.shape = Δ₂.shape) :
    (Δ₁.join Δ₂).shape = Δ₁.shape := by
  funext x
  have hx := congrFun h x
  simp only [PCtx.shape, PCtx.join_apply] at hx ⊢
  cases h₁ : Δ₁ x <;> cases h₂ : Δ₂ x <;> simp_all [PEntry.join]

mutual

/-- Typing never changes the shape of `Δ`: no handle is created, destroyed, or changes kind.
Needed in the `if`/`match` cases of soundness so that the join of the branch contexts is a
pointwise union (never the "mismatch → absent" case of `PEntry.join`). -/
theorem Typed.shape_eq {Γ Δ c Γ' Δ' Q F} :
    Typed P M Ψ Γ Δ c Γ' Δ' Q F → Δ'.shape = Δ.shape
  | .skip => rfl
  | .assign _ _ => rfl
  | .ite _ h₁ h₂ => by
      rw [PCtx.shape_join (h₁.shape_eq.trans h₂.shape_eq.symm), h₁.shape_eq]
  | .transition hp _ _ => PCtx.shape_set_of hp _
  | .downgrade hp _ _ => PCtx.shape_set_of hp _
  | .clock _ => rfl
  | .seq h₁ h₂ => h₂.shape_eq.trans h₁.shape_eq
  | .matchSt hp _ ha => ha.shape_eq.trans (PCtx.shape_set_of hp _)
  | .call _ _ _ hp _ => PCtx.shape_set_of hp _

/-- Arms version of `Typed.shape_eq`: every arm runs with `p` narrowed (`Δ[p : {stᵢ}]`), so the
joined result has the shape of `Δ` with `p` at kind `k`. -/
theorem ArmsTyped.shape_eq {Γ Δ p k S arms Γ' Δ' Q F} :
    ArmsTyped P M Ψ Γ Δ p k S arms Γ' Δ' Q F → Δ'.shape = (Δ.set p k ∅).shape
  | .last _ h _ => h.shape_eq.trans (PCtx.shape_set_set _ _ _ _ _)
  | .cons _ h ha => by
      have h₁ := h.shape_eq.trans (PCtx.shape_set_set _ _ _ _ ∅)
      rw [PCtx.shape_join (h₁.trans ha.shape_eq.symm), h₁]
  | .skip _ ha => ha.shape_eq

end

/-! ### Agreement lemmas

How runtime states that agree with typing contexts behave under the operations the rules perform.
Each is used in one or more cases of `soundness`. -/

omit [DecidableEq K] in
/-- **Expression typing is sound**: a well-typed expression evaluates, in any memory agreeing with
`Γ`, to a value of its type.  Used wherever a rule evaluates an expression (let, if, call). -/
theorem HasTy.eval {Γ : TCtx K} {σ : Mem} (hσ : MemOK Γ σ) :
    ∀ {e τ}, HasTy Γ e τ → ∃ v, e.eval σ = some v ∧ v.ty = τ
  | _, _, .var h => hσ _ _ h
  | _, _, .val => ⟨_, rfl, rfl⟩
  | _, _, .binop h₁ h₂ hop => by
      obtain ⟨v₁, he₁, ht₁⟩ := HasTy.eval hσ h₁
      obtain ⟨v₂, he₂, ht₂⟩ := HasTy.eval hσ h₂
      cases hop <;> cases v₁ <;> cases v₂ <;> simp_all [Expr.eval, BinOp.eval, Val.ty]

/-- Binding a variable to a value of the bound type preserves agreement (let, call). -/
theorem MemOK.bind {Γ : TCtx K} {σ : Mem} (hσ : MemOK Γ σ) {x : Var} {v : Val} {τ : Ty K}
    (hv : v.ty = τ) : MemOK (Γ.bind x τ) (σ.set x v) := by
  intro y τ' hy
  by_cases h : y = x
  · subst h; simp_all
  · simp only [TCtx.bind_apply, h, ↓reduceIte] at hy
    simpa [h] using hσ y τ' hy

/-- `Γ₁` is contained in `Γ₂`: every binding of `Γ₁` is in `Γ₂`.  The value contexts after an
`if`/`match` (`Γ₁ ∩ Γ₂`) are contained in each branch's. -/
def TCtx.Sub (Γ₁ Γ₂ : TCtx K) : Prop := ∀ x τ, Γ₁ x = some τ → Γ₂ x = some τ

omit [DecidableEq St] in
/-- `Γ₁ ∩ Γ₂ ⊆ Γ₁`. -/
theorem TCtx.inter_sub_left (Γ₁ Γ₂ : TCtx K) : (Γ₁.inter Γ₂).Sub Γ₁ := by
  intro x τ h; unfold TCtx.inter at h; split_ifs at h; simp_all

omit [DecidableEq St] in
/-- `Γ₁ ∩ Γ₂ ⊆ Γ₂`. -/
theorem TCtx.inter_sub_right (Γ₁ Γ₂ : TCtx K) : (Γ₁.inter Γ₂).Sub Γ₂ := by
  intro x τ h; unfold TCtx.inter at h; split_ifs at h with he; simp_all

omit [DecidableEq K] in
/-- Agreement with a context implies agreement with any smaller one. -/
theorem MemOK.mono {Γ Γ' : TCtx K} {σ : Mem} (hσ : MemOK Γ σ) (h : Γ'.Sub Γ) : MemOK Γ' σ :=
  fun x τ hx => hσ x τ (h x τ hx)

/-- Entry-wise precision order: same kind, smaller state set. -/
def PEntry.Le : PEntry K St → PEntry K St → Prop
  | .absent, .absent => True
  | .live k S, .live k' S' => k = k' ∧ S ⊆ S'
  | _, _ => False

/-- `Δ₁ ⊑ Δ₂`: same handles and kinds, each state set of `Δ₁` contained in `Δ₂`'s.  A branch's
output context is below the join (`le_join_left`/`right`), and agreement transfers upward. -/
def PCtx.Le (Δ₁ Δ₂ : PCtx K St) : Prop := ∀ x, (Δ₁ x).Le (Δ₂ x)

omit [DecidableEq K] [DecidableEq St] in
/-- `⊑` is reflexive. -/
theorem PCtx.Le.refl (Δ : PCtx K St) : Δ.Le Δ := by
  intro x; cases Δ x <;> simp [PEntry.Le]

omit [DecidableEq K] [DecidableEq St] in
/-- `⊑` is transitive (an arm's output is below the arms joined after it). -/
theorem PCtx.Le.trans {Δ₁ Δ₂ Δ₃ : PCtx K St} (h₁ : Δ₁.Le Δ₂) (h₂ : Δ₂.Le Δ₃) : Δ₁.Le Δ₃ := by
  intro x
  have a := h₁ x; have b := h₂ x
  revert a b
  cases Δ₁ x <;> cases Δ₂ x <;> cases Δ₃ x <;> simp only [PEntry.Le, imp_self, implies_true,
    imp_false, not_true, IsEmpty.forall_iff]
  exact fun a b => ⟨a.1.trans b.1, a.2.trans b.2⟩

/-- A branch's output is below the join, provided the two branches have the same shape. -/
theorem PCtx.le_join_left {Δ₁ Δ₂ : PCtx K St} (h : Δ₁.shape = Δ₂.shape) : Δ₁.Le (Δ₁.join Δ₂) := by
  intro x
  have hx := congrFun h x
  simp only [PCtx.shape, PCtx.join_apply] at hx ⊢
  cases h₁ : Δ₁ x <;> cases h₂ : Δ₂ x <;> simp_all [PEntry.join, PEntry.Le]

/-- Symmetric version of `le_join_left`. -/
theorem PCtx.le_join_right {Δ₁ Δ₂ : PCtx K St} (h : Δ₁.shape = Δ₂.shape) :
    Δ₂.Le (Δ₁.join Δ₂) := by
  intro x
  have hx := congrFun h x
  simp only [PCtx.shape, PCtx.join_apply] at hx ⊢
  cases h₁ : Δ₁ x <;> cases h₂ : Δ₂ x <;> simp_all [PEntry.join, PEntry.Le]

omit [DecidableEq K] [DecidableEq St] in
/-- Agreement transfers to a less precise context. -/
theorem PeriphsOK.mono {Δ Δ' : PCtx K St} {S : RPeriphs K St} (hS : PeriphsOK Δ S)
    (h : Δ.Le Δ') : PeriphsOK Δ' S := by
  intro x
  have a := hS x; have b := h x
  revert a b
  cases S x <;> cases Δ x <;> cases Δ' x <;> simp only [REntry.Approx, PEntry.Le, imp_self,
    implies_true, imp_false, not_true, IsEmpty.forall_iff]
  exact fun a b => ⟨a.1.trans b.1, b.2 a.2⟩

omit [DecidableEq K] [DecidableEq St] in
/-- Reading agreement at a handle: a runtime `at k s` against a typing `live k' T` means `k = k'`
and `s ∈ T`. -/
theorem PeriphsOK.at {Δ : PCtx K St} {S : RPeriphs K St} (hS : PeriphsOK Δ S) {p : Var}
    {k k' : K} {s : St} {T : Finset St} (hSp : S p = .at k s) (hp : Δ p = .live k' T) :
    k = k' ∧ s ∈ T := by
  have := hS p; rw [hSp, hp] at this; exact this

omit [DecidableEq K] [DecidableEq St] in
/-- Setting a handle to a state in the set the typing records preserves agreement
(transition, downgrade, call, match narrowing). -/
theorem PeriphsOK.set {Δ : PCtx K St} {S : RPeriphs K St} (hS : PeriphsOK Δ S) (p : Var) (k : K)
    {s : St} {T : Finset St} (hs : s ∈ T) : PeriphsOK (Δ.set p k T) (S.set p k s) := by
  intro x
  by_cases h : x = p
  · simp [h, REntry.Approx, hs]
  · simpa [h] using hS x

omit [DecidableEq K] [DecidableEq St] in
/-- Removing a handle on both sides preserves agreement (`cost(Δ ∖ p)` vs `bg(S ∖ p)`). -/
theorem PeriphsOK.erase {Δ : PCtx K St} {S : RPeriphs K St} (hS : PeriphsOK Δ S) (p : Var) :
    PeriphsOK (Δ.erase p) (S.erase p) := by
  intro x
  by_cases h : x = p
  · simp [h]; exact trivial
  · simpa [h] using hS x

omit [DecidableEq K] [DecidableEq St] in
/-- **The actual background cost is bounded by the typing's**: `bg(S) ≤ cost(Δ)` when `S`
agrees with `Δ`.  Each handle's exact state is among the allowed ones, so its `cb` is at most
their maximum.  Used in every rule that charges background. -/
theorem PeriphsOK.bg_le [IsOrderedRing R] {Δ : PCtx K St} {S : RPeriphs K St} (hS : PeriphsOK Δ S) :
    S.bg M ≤ Δ.bg M := by
  unfold RPeriphs.bg PCtx.bg
  rw [Finsupp.sum_of_support_subset S (Finset.subset_union_left (s₂ := Δ.support)) _
      (fun _ _ => rfl),
    Finsupp.sum_of_support_subset Δ (Finset.subset_union_right (s₁ := S.support)) _
      (fun _ _ => rfl)]
  refine Finset.sum_le_sum (fun x _ => ?_)
  have a := hS x
  cases e : S x <;> cases e' : Δ x <;> simp_all [REntry.Approx, REntry.bg, PEntry.bg]
  obtain ⟨rfl, hs⟩ := a
  exact M.bgCost_le_maxBg hs

omit [DecidableEq K] in
/-- `find?` only returns an arm whose state is listed — so an arm selected for a reachable state
can never lie among arms the refined T-Match ignored as unreachable. -/
theorem Arms.mem_states_of_find? {R : Type} :
    ∀ {arms : Arms St R} {s : St} {c : Cmd St R}, arms.find? s = some c → s ∈ arms.states
  | .nil, _, _, h => by simp [Arms.find?] at h
  | .cons st _ rest, s, c, h => by
      simp only [Arms.find?] at h
      split_ifs at h with hst
      · simp [Arms.states, hst]
      · simp [Arms.states, Arms.mem_states_of_find? h]

/-- **The arm a `match` runs is covered by the arms' joined typing.**  If `arms.find? s = some c`
for a reachable state `s ∈ S`, then `c` is typed with `p` narrowed to `s`, its summaries are below
the joined ones, and its output contexts are at least as precise as the joined ones.  (Skipped,
unreachable arms are never selected: their states are not in `S`.) -/
theorem ArmsTyped.find {Γ Δ p k S arms Γ' Δ' Q F} :
    ArmsTyped P M Ψ Γ Δ p k S arms Γ' Δ' Q F → ∀ {s c}, s ∈ S → arms.find? s = some c →
    ∃ Γc Δc Qc Fc, Typed P M Ψ Γ (Δ.set p k {s}) c Γc Δc Qc Fc ∧ Γ'.Sub Γc ∧ Δc.Le Δ' ∧
      (∀ f b, Qc f b + f * ((Δ.set p k {s}).bg M + b) ≤ Q f b) ∧ (∀ f, Fc f ≤ F f)
  | .last _ h hrest, s, c, hs, hf => by
      simp only [Arms.find?] at hf
      split_ifs at hf with hst
      · cases hf; subst hst
        exact ⟨_, _, _, _, h, fun _ _ hx => hx, PCtx.Le.refl _, fun _ _ => le_rfl,
          fun _ => le_rfl⟩
      · exact absurd hs (hrest s (Arms.mem_states_of_find? hf))
  | .cons _ h ha, s, c, hs, hf => by
      have hsh := (h.shape_eq.trans (PCtx.shape_set_set _ _ _ _ ∅)).trans ha.shape_eq.symm
      simp only [Arms.find?] at hf
      split_ifs at hf with hst
      · cases hf; subst hst
        exact ⟨_, _, _, _, h, TCtx.inter_sub_left _ _, PCtx.le_join_left hsh,
          fun _ _ => le_max_left _ _, fun _ => le_max_left _ _⟩
      · obtain ⟨Γc, Δc, Qc, Fc, hc, hΓ, hΔ, hQ, hF⟩ := ha.find hs hf
        exact ⟨Γc, Δc, Qc, Fc, hc, fun x τ hx => hΓ x τ (TCtx.inter_sub_right _ _ x τ hx),
          hΔ.trans (PCtx.le_join_right hsh), fun f b => (hQ f b).trans (le_max_right _ _),
          fun f => (hF f).trans (le_max_right _ _)⟩
  | .skip hst ha, s, c, hs, hf => by
      simp only [Arms.find?] at hf
      split_ifs at hf with hst'
      · exact absurd (hst' ▸ hs) hst
      · exact ha.find hs hf

omit [DecidableEq K] [OrderBot R] in
/-- Signatures valid for the declarations have monotone summaries — the hypothesis `Typed.mono`
needs, extracted from `SigsValid`. -/
theorem SigsValid.mono {Ψd : FCtx K St R} (hΨ : SigsValid M Ψd Ψ) :
    ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk := fun g sig h =>
  let ⟨_, _, hv⟩ := hΨ g sig h; hv.mono

/-! ### Main theorems -/

variable [IsOrderedRing R] [CanonicallyOrderedAdd R]

omit [OrderBot R] in
/-- A step that charges `f * x` at clock `f` is monotone in `f` and in its charge `x` — the
building block of every primitive rule's monotonicity (all costs are `≥ 0` in this domain). -/
private theorem mul_mono {f f' x x' : R} (hf : f ≤ f') (hx : x ≤ x') : f * x ≤ f' * x' :=
  mul_le_mul hf hx zero_le zero_le

-- `ArmsTyped.mono` needs the ordered-ring instances only through its mutual partner `Typed.mono`,
-- which the unused-variables linter does not see.
set_option linter.unusedSectionVars false in
mutual

/-- **Monotonicity of summaries.**  If every signature in scope has monotone summaries, so does
every derived summary.  This is what turns the exact statement of `soundness` (at the actual
clock and ambient cost) into a bound at any faster typed clock or larger assumed ambient, and it
is used inside `soundness` for `c₁; c₂`, whose second command starts at a clock `≤ F₁ K`. -/
theorem Typed.mono (hM : M.WF) (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk)
    {Γ Δ c Γ' Δ' Q F} : Typed P M Ψ Γ Δ c Γ' Δ' Q F → SummaryMono Q F
  | .skip => ⟨monotone_id, fun _ _ _ _ _ _ => le_rfl⟩
  | .assign _ _ => ⟨monotone_id, fun _ _ _ _ hf hb => mul_mono hf (add_le_add le_rfl hb)⟩
  | .ite _ h₁ h₂ =>
      have ⟨hF₁, hQ₁⟩ := h₁.mono hM hΨ
      have ⟨hF₂, hQ₂⟩ := h₂.mono hM hΨ
      ⟨fun _ _ hf => max_le_max (hF₁ hf) (hF₂ hf), fun _ _ _ _ hf hb =>
        add_le_add (max_le_max (hQ₁ _ _ _ _ hf hb) (hQ₂ _ _ _ _ hf hb))
          (mul_mono hf (add_le_add le_rfl hb))⟩
  | .transition _ _ _ => ⟨monotone_id, fun _ _ _ _ hf hb => mul_mono hf (add_le_add le_rfl hb)⟩
  | .downgrade _ _ _ => ⟨monotone_id, fun _ _ _ _ hf hb => mul_mono hf (add_le_add le_rfl hb)⟩
  | .clock _ => ⟨monotone_const, fun _ _ _ _ hf hb =>
      add_le_add (hM.clockCost_mono_left _ _ _ hf) (mul_mono hf (add_le_add le_rfl hb))⟩
  | .seq h₁ h₂ =>
      have ⟨hF₁, hQ₁⟩ := h₁.mono hM hΨ
      have ⟨hF₂, hQ₂⟩ := h₂.mono hM hΨ
      ⟨hF₂.comp hF₁, fun _ _ _ _ hf hb =>
        add_le_add (hQ₁ _ _ _ _ hf hb) (hQ₂ _ _ _ _ (hF₁ hf) hb)⟩
  | .matchSt _ _ ha => ha.mono hM hΨ
  | .call hg _ _ _ _ =>
      have ⟨hF, hQ⟩ := hΨ _ _ hg
      ⟨hF, fun _ _ _ _ hf hb =>
        add_le_add (mul_mono hf (add_le_add le_rfl hb)) (hQ _ _ _ _ hf (add_le_add hb le_rfl))⟩

/-- Arms version of `Typed.mono`: the joined summary is a pointwise `max` of monotone ones. -/
theorem ArmsTyped.mono (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk)
    {Γ Δ p k S arms Γ' Δ' Q F} : ArmsTyped P M Ψ Γ Δ p k S arms Γ' Δ' Q F → SummaryMono Q F
  | .last _ h _ =>
      have ⟨hF, hQ⟩ := h.mono hM hΨ
      ⟨hF, fun _ _ _ _ hf hb =>
        add_le_add (hQ _ _ _ _ hf hb) (mul_mono hf (add_le_add le_rfl hb))⟩
  | .cons _ h ha =>
      have ⟨hF₁, hQ₁⟩ := h.mono hM hΨ
      have ⟨hF₂, hQ₂⟩ := ha.mono hM hΨ
      ⟨fun _ _ hf => max_le_max (hF₁ hf) (hF₂ hf), fun _ _ _ _ hf hb =>
        max_le_max (add_le_add (hQ₁ _ _ _ _ hf hb) (mul_mono hf (add_le_add le_rfl hb)))
          (hQ₂ _ _ _ _ hf hb)⟩
  | .skip _ ha => ha.mono hM hΨ

end

/-- **Cost soundness.**  If `c` has summaries `Q`, `F` and runs from clock `K` with ambient
peripherals `A`, from a state that agrees with its typing contexts, then the actual cost is at
most `Q K (bg A)`, the exit clock is at most `F K`, and the final state agrees with the output
contexts (so results compose under `;`).  Combined with `Typed.mono`, the cost is also at most
`Q f b` for any typed clock `f ≥ K` and assumed ambient background `b ≥ bg A`.

Proof: induction on the evaluation, inverting the typing (see the module doc for the plan). -/
theorem soundness (hM : M.WF) {Ψd : FCtx K St R} (hΨ : SigsValid M Ψd Ψ)
    {Γ Δ c Γ' Δ' Q F} (ht : Typed P M Ψ Γ Δ c Γ' Δ' Q F)
    {A σ S K σ' S' q' K'} (he : Eval M Ψd A σ S K c σ' S' q' K')
    (hσ : MemOK Γ σ) (hS : PeriphsOK Δ S) :
    q' ≤ Q K (ambBg M A) ∧ MemOK Γ' σ' ∧ PeriphsOK Δ' S' ∧ K' ≤ F K := by
  induction he generalizing Γ Δ Γ' Δ' Q F with
  | skip => cases ht; exact ⟨le_rfl, hσ, hS, le_rfl⟩
  | assign hev =>
    cases ht with
    | assign hty _ =>
      obtain ⟨v', hev', hty'⟩ := HasTy.eval hσ hty
      rw [hev] at hev'; cases hev'
      exact ⟨mul_mono le_rfl (add_le_add (add_le_add le_rfl hS.bg_le) le_rfl),
        hσ.bind hty', hS, le_rfl⟩
  | iteTrue _ _ ih =>
    cases ht with
    | ite _ h₁ h₂ =>
      obtain ⟨hq, hσ', hS', hK⟩ := ih h₁ hσ hS
      have hsh := h₁.shape_eq.trans h₂.shape_eq.symm
      exact ⟨add_le_add (hq.trans (le_max_left _ _))
          (mul_mono le_rfl (add_le_add (add_le_add le_rfl hS.bg_le) le_rfl)),
        hσ'.mono (TCtx.inter_sub_left _ _), hS'.mono (PCtx.le_join_left hsh),
        hK.trans (le_max_left _ _)⟩
  | iteFalse _ _ ih =>
    cases ht with
    | ite _ h₁ h₂ =>
      obtain ⟨hq, hσ', hS', hK⟩ := ih h₂ hσ hS
      have hsh := h₁.shape_eq.trans h₂.shape_eq.symm
      exact ⟨add_le_add (hq.trans (le_max_right _ _))
          (mul_mono le_rfl (add_le_add (add_le_add le_rfl hS.bg_le) le_rfl)),
        hσ'.mono (TCtx.inter_sub_right _ _), hS'.mono (PCtx.le_join_right hsh),
        hK.trans (le_max_right _ _)⟩
  | transition hSp =>
    cases ht with
    | transition hp _ _ =>
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      exact ⟨mul_mono le_rfl (add_le_add (add_le_add (M.transCost_le_maxTrans hs)
          (hS.erase _).bg_le) le_rfl),
        hσ, hS.set _ _ (Finset.mem_singleton_self _), le_rfl⟩
  | downgrade hSp =>
    cases ht with
    | downgrade hp _ _ =>
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      exact ⟨mul_mono le_rfl (add_le_add (add_le_add (M.transCost_le_maxTrans hs)
          (hS.erase _).bg_le) le_rfl),
        hσ, hS.set _ _ (Finset.mem_singleton_self _), le_rfl⟩
  | clock =>
    cases ht with
    | clock _ =>
      exact ⟨add_le_add le_rfl (mul_mono le_rfl (add_le_add hS.bg_le le_rfl)), hσ, hS, le_rfl⟩
  | seq _ _ ih₁ ih₂ =>
    cases ht with
    | seq h₁ h₂ =>
      obtain ⟨hq₁, hσ₁, hS₁, hK₁⟩ := ih₁ h₁ hσ hS
      obtain ⟨hq₂, hσ₂, hS₂, hK₂⟩ := ih₂ h₂ hσ₁ hS₁
      obtain ⟨hF₂, hQ₂⟩ := h₂.mono hM hΨ.mono
      exact ⟨add_le_add hq₁ (hq₂.trans (hQ₂ _ _ _ _ hK₁ le_rfl)), hσ₂, hS₂, hK₂.trans (hF₂ hK₁)⟩
  | @matchSt A σ S K p arms k s c σ' S' q K' hSp hfind _ ih =>
    cases ht with
    | matchSt hp _ ha =>
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      obtain ⟨Γc, Δc, Qc, Fc, hc, hΓ, hΔ, hQ, hF⟩ := ha.find hs hfind
      have hSs : PeriphsOK (Δ.set p k {s}) S := by
        rw [← RPeriphs.set_eq_self hSp]; exact hS.set _ _ (Finset.mem_singleton_self _)
      obtain ⟨hq, hσ', hS', hK⟩ := ih hc hσ hSs
      exact ⟨(add_le_add hq (mul_mono le_rfl (add_le_add hSs.bg_le le_rfl))).trans (hQ _ _),
        hσ'.mono hΓ, hS'.mono hΔ, hK.trans (hF _)⟩
  | @call A σ S K x g e p d v k s σb Sb qb Kb r s' hgd hev hSp heb hret hSb _ =>
    cases ht with
    | call hg hty _ hp hsub =>
      obtain ⟨d', hd', hvalid⟩ := hΨ _ _ hg
      rw [hgd] at hd'; cases hd'
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      obtain ⟨v', hev', hty'⟩ := HasTy.eval hσ hty
      rw [hev] at hev'; cases hev'
      obtain ⟨r', s'', hret', hrty, hSb', hs'', hcost, hclk⟩ :=
        hvalid.bound _ _ _ _ _ _ _ _ hty' (hsub hs) heb
      rw [hret] at hret'; cases hret'
      rw [hSb] at hSb'; cases hSb'
      refine ⟨?_, hσ.bind hrty, hS.set _ _ hs'', hclk⟩
      rw [add_assoc]
      refine add_le_add (mul_mono le_rfl (add_le_add (add_le_add le_rfl hS.bg_le) le_rfl))
        (hcost.trans (hvalid.mono.2 _ _ _ _ le_rfl ?_))
      rw [ambBg_add_entries]
      exact add_le_add le_rfl (hS.erase p).bg_le

/-! ### Termination -/

omit [DecidableEq K] [DecidableEq St] in
/-- Every handle bound in `Δ` has a runtime state, among the allowed ones.  Lets the primitive
peripheral commands, `match` and calls take a step in `eval_total`. -/
theorem PeriphsOK.live {Δ : PCtx K St} {S : RPeriphs K St} (hS : PeriphsOK Δ S) {p : Var}
    {k : K} {T : Finset St} (hp : Δ p = .live k T) : ∃ s, S p = .at k s ∧ s ∈ T := by
  have := hS p
  rw [hp] at this
  rcases h : S p with _ | ⟨k', s⟩
  · rw [h] at this; exact absurd this (by simp [REntry.Approx])
  · rw [h] at this; obtain ⟨rfl, hs⟩ := this; exact ⟨s, rfl, hs⟩

omit [DecidableEq K] in
/-- A value of type `bool` is a boolean literal (the `if` case of `eval_total`). -/
theorem Val.eq_bool_of_ty {v : Val} (h : v.ty = (Ty.bool : Ty K)) : ∃ b, v = .bool b := by
  cases v <;> simp_all [Val.ty]

omit [DecidableEq K] [CommSemiring R] [LinearOrder R] [OrderBot R] [IsOrderedRing R]
  [CanonicallyOrderedAdd R] in
/-- Exhaustive arms cover every state: if `s` is among the arms' states, `find?` succeeds. -/
theorem Arms.find?_of_mem : ∀ {arms : Arms St R} {s : St}, s ∈ arms.states →
    ∃ c, arms.find? s = some c
  | .nil, _, h => by simp [Arms.states] at h
  | .cons st c rest, s, h => by
    simp only [Arms.find?]
    split_ifs with hst
    · exact ⟨c, rfl⟩
    · simp only [Arms.states, Finset.mem_insert] at h
      exact Arms.find?_of_mem (h.resolve_left (Ne.symm hst))

-- `ArmsTyped.arm_eval_total` needs the ordered-ring instances only through `eval_total`.
set_option linter.unusedSectionVars false in
mutual

/-- **Type safety (termination).**  A well-typed command always runs to completion from a state
that agrees with its typing contexts.  In the synchronous fragment there are no loops and
recursion is untypable, so "never gets stuck" and "terminates" coincide; this is the sync version
of "a well-typed program always has the resources to take a step".

`hM` is needed only because the `seq` case reuses `soundness` to know that the state after `c₁`
agrees with `c₂`'s typing; that agreement part does not depend on costs. -/
theorem eval_total (hM : M.WF) {Ψd : FCtx K St R} (hΨ : SigsValid M Ψd Ψ)
    {Γ Δ c Γ' Δ' Q F} : Typed P M Ψ Γ Δ c Γ' Δ' Q F →
    ∀ (A : Multiset (K × St)) σ S K, MemOK Γ σ → PeriphsOK Δ S →
    ∃ σ' S' q' K', Eval M Ψd A σ S K c σ' S' q' K'
  | .skip => fun _ _ _ _ _ _ => ⟨_, _, _, _, .skip⟩
  | .assign hty _ => fun _ _ _ _ hσ _ =>
      let ⟨_, hv, _⟩ := HasTy.eval hσ hty
      ⟨_, _, _, _, .assign hv⟩
  | .ite hty h₁ h₂ => fun _ _ _ _ hσ hS => by
      obtain ⟨v, hv, hvt⟩ := HasTy.eval hσ hty
      obtain ⟨b, rfl⟩ := Val.eq_bool_of_ty hvt
      cases b
      · obtain ⟨_, _, _, _, he⟩ := eval_total hM hΨ h₂ _ _ _ _ hσ hS
        exact ⟨_, _, _, _, .iteFalse hv he⟩
      · obtain ⟨_, _, _, _, he⟩ := eval_total hM hΨ h₁ _ _ _ _ hσ hS
        exact ⟨_, _, _, _, .iteTrue hv he⟩
  | .transition hp _ _ => fun _ _ _ _ _ hS =>
      let ⟨_, hSp, _⟩ := hS.live hp
      ⟨_, _, _, _, .transition hSp⟩
  | .downgrade hp _ _ => fun _ _ _ _ _ hS =>
      let ⟨_, hSp, _⟩ := hS.live hp
      ⟨_, _, _, _, .downgrade hSp⟩
  | .clock _ => fun _ _ _ _ _ _ => ⟨_, _, _, _, .clock⟩
  | .seq h₁ h₂ => fun _ _ _ _ hσ hS => by
      obtain ⟨_, _, _, _, he₁⟩ := eval_total hM hΨ h₁ _ _ _ _ hσ hS
      obtain ⟨-, hσ₁, hS₁, -⟩ := soundness hM hΨ h₁ he₁ hσ hS
      obtain ⟨_, _, _, _, he₂⟩ := eval_total hM hΨ h₂ _ _ _ _ hσ₁ hS₁
      exact ⟨_, _, _, _, .seq he₁ he₂⟩
  | .matchSt hp hsub ha => fun A _ S Kc hσ hS => by
      obtain ⟨s, hSp, hs⟩ := hS.live hp
      obtain ⟨c, hfind⟩ := Arms.find?_of_mem (hsub hs)
      obtain ⟨_, _, _, _, he⟩ := ArmsTyped.arm_eval_total hM hΨ ha hs hfind A _ S Kc hσ
        (by rw [← RPeriphs.set_eq_self hSp]; exact hS.set _ _ (Finset.mem_singleton_self _))
      exact ⟨_, _, _, _, .matchSt hSp hfind he⟩
  | .call hg hty _ hp hsub => fun _ _ _ _ hσ hS => by
      obtain ⟨d, hd, hvalid⟩ := hΨ _ _ hg
      obtain ⟨v, hv, hvt⟩ := HasTy.eval hσ hty
      obtain ⟨s, hSp, hs⟩ := hS.live hp
      obtain ⟨_, _, _, _, heb⟩ := hvalid.total _ _ _ _ hvt (hsub hs)
      obtain ⟨_, _, hret, -, hSb, -⟩ := hvalid.bound _ _ _ _ _ _ _ _ hvt (hsub hs) heb
      exact ⟨_, _, _, _, .call hd hv hSp heb hret hSb⟩

/-- Arms version of `eval_total`: for a reachable state `s ∈ S`, the arm `find?` selects runs to
completion when `p` is in state `s`.  (Named `arm_eval_total` so that, inside the mutual block,
`eval_total` refers unambiguously to the command version.) -/
theorem ArmsTyped.arm_eval_total (hM : M.WF) {Ψd : FCtx K St R} (hΨ : SigsValid M Ψd Ψ)
    {Γ Δ p k S arms Γ' Δ' Q F} : ArmsTyped P M Ψ Γ Δ p k S arms Γ' Δ' Q F →
    ∀ {s c}, s ∈ S → arms.find? s = some c → ∀ (A : Multiset (K × St)) σ Sr K, MemOK Γ σ →
    PeriphsOK (Δ.set p k {s}) Sr →
    ∃ σ' S' q' K', Eval M Ψd A σ Sr K c σ' S' q' K'
  | .last _ h hrest => fun hs hf _ _ _ _ hσ hS => by
      simp only [Arms.find?] at hf
      split_ifs at hf with hst
      · cases hf; subst hst
        exact eval_total hM hΨ h _ _ _ _ hσ hS
      · exact absurd hs (hrest _ (Arms.mem_states_of_find? hf))
  | .cons _ h ha => fun hs hf _ _ _ _ hσ hS => by
      simp only [Arms.find?] at hf
      split_ifs at hf with hst
      · cases hf; subst hst
        exact eval_total hM hΨ h _ _ _ _ hσ hS
      · exact ArmsTyped.arm_eval_total hM hΨ ha hs hf _ _ _ _ hσ hS
  | .skip hst ha => fun hs hf _ _ _ _ hσ hS => by
      simp only [Arms.find?] at hf
      split_ifs at hf with hst'
      · exact absurd (hst' ▸ hs) hst
      · exact ArmsTyped.arm_eval_total hM hΨ ha hs hf _ _ _ _ hσ hS

end

/-! ### Declarations and whole programs -/

/-- The empty memory extended with the argument agrees with a context binding only the argument
(the start of a function body). -/
theorem MemOK.arg {x : Var} {v : Val} {τ : Ty K} (hv : v.ty = τ) :
    MemOK (TCtx.empty.bind x τ) (Mem.empty.set x v) :=
  MemOK.bind (fun _ _ h => by simp [TCtx.empty] at h) hv

omit [DecidableEq K] [DecidableEq St] in
/-- A function body's initial peripheral contexts agree: the parameter in an allowed state. -/
theorem PeriphsOK.single {x : Var} {k : K} {s : St} {T : Finset St} (hs : s ∈ T) :
    PeriphsOK (Finsupp.single x (.live k T)) (Finsupp.single x (.at k s)) := by
  intro y
  by_cases h : y = x
  · subst h; simp [REntry.Approx, hs]
  · simp only [Finsupp.single_apply, Ne.symm h, ↓reduceIte]; exact trivial

/-- **T-FunDecl produces a valid signature**, provided the signatures its body was typed against
are valid: the body terminates (`eval_total`), its cost plus the return expression's is bounded
by the summary (`soundness`, `Kb ≤ Fb K`), and the summary is monotone (`Typed.mono`). -/
theorem FunDeclTyped.valid (hM : M.WF) {Ψd : FCtx K St R} (hΨ : SigsValid M Ψd Ψ)
    {d : FunDecl K St R} {sig : FunSig K St R} (hd : FunDeclTyped P M Ψ d sig) :
    SigValid M Ψd d sig := by
  obtain ⟨hargTy, hpKind, hsIn, hretTy, hsOut, Γb, Δb, Qb, Fb, S', hb, hret, hΔb, hS', hcost,
    hclk⟩ := hd
  obtain ⟨hFb, hQb⟩ := hb.mono hM hΨ.mono
  refine ⟨?total, ?bound, ?mono⟩
  case total =>
    intro A K v s hv hs
    rw [hargTy] at hv; rw [hsIn] at hs; rw [hpKind]
    exact eval_total hM hΨ hb _ _ _ _ (MemOK.arg hv) (PeriphsOK.single hs)
  case bound =>
    intro A K v s σb Sb qb Kb hv hs he
    rw [hargTy] at hv; rw [hsIn] at hs; rw [hpKind] at he ⊢
    obtain ⟨hq, hσb, hSb, hK⟩ := soundness hM hΨ hb he (MemOK.arg hv) (PeriphsOK.single hs)
    obtain ⟨r, hr, hrt⟩ := HasTy.eval hσb hret
    obtain ⟨s', hSbp, hs'⟩ := hSb.live hΔb
    refine ⟨r, s', hr, hretTy ▸ hrt, hSbp, hsOut ▸ hS' hs', ?_, hclk ▸ hK⟩
    rw [hcost]
    exact add_le_add hq (mul_mono hK (add_le_add (add_le_add le_rfl hSb.bg_le) le_rfl))
  case mono =>
    rw [hcost, hclk]
    exact ⟨hFb, fun _ _ _ _ hf hb' =>
      add_le_add (hQb _ _ _ _ hf hb') (mul_mono (hFb hf) (add_le_add le_rfl hb'))⟩

/-- Typing declarations in order preserves validity of the signature context, as long as the
semantics' lookup `Ψd` finds each declaration under its name. -/
theorem DeclsTyped.sigsValid (hM : M.WF) {Ψd : FCtx K St R} {Ψ₀ ds Ψ'}
    (hds : DeclsTyped P M Ψ₀ ds Ψ') (hΨ₀ : SigsValid M Ψd Ψ₀)
    (hmem : ∀ d ∈ ds, Ψd d.name = some d) : SigsValid M Ψd Ψ' := by
  induction hds with
  | nil => exact hΨ₀
  | @cons Ψ d ds sig Ψ' hd _ ih =>
    apply ih _ (fun d' hd' => hmem d' (List.mem_cons_of_mem _ hd'))
    intro g sig' hg
    by_cases h : g = d.name
    · subst h
      simp only [Function.update_self, Option.some.injEq] at hg
      subst hg
      exact ⟨d, hmem d (List.mem_cons_self ..), hd.valid hM hΨ₀⟩
    · rw [Function.update_of_ne h] at hg
      exact hΨ₀ g sig' hg

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R]
  [IsOrderedRing R] [CanonicallyOrderedAdd R] in
/-- In a declaration list with distinct names, looking a declaration's name up finds it. -/
private theorem find_name_of_mem {ds : List (FunDecl K St R)} (hnd : (ds.map (·.name)).Nodup)
    {d : FunDecl K St R} (hd : d ∈ ds) : ds.find? (fun d' => d'.name == d.name) = some d := by
  induction ds with
  | nil => simp at hd
  | cons d₀ ds ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hd with rfl | hd'
    · simp
    · have hne : d₀.name ≠ d.name := fun he => hnd.1 ⟨d, hd', he.symm⟩
      simp [hne, ih hnd.2 hd']

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R]
  [IsOrderedRing R] [CanonicallyOrderedAdd R] in
/-- With distinct names, the program's lookup finds each declaration under its own name, so the
semantics runs the declaration whose signature the typing used. -/
theorem Program.fctx_of_mem {prog : Program K St R} (hnd : (prog.funs.map (·.name)).Nodup)
    {d : FunDecl K St R} (hd : d ∈ prog.funs) : prog.fctx d.name = some d :=
  find_name_of_mem hnd hd

/-- **Declared signatures are valid.**  The signatures obtained by typing a program's
declarations in order are valid for the program's declarations. -/
theorem Program.sigsValid (hM : M.WF) {prog : Program K St R}
    {Ψ Γ' Δ' Q F} (ht : prog.Typed P M Ψ Γ' Δ' Q F) : SigsValid M prog.fctx Ψ :=
  DeclsTyped.sigsValid hM ht.2.1 (fun _ _ h => by simp at h)
    (fun _ hd => Program.fctx_of_mem ht.1 hd)

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R]
  [IsOrderedRing R] [CanonicallyOrderedAdd R] in
/-- The initial runtime peripherals agree with the initial peripheral context: both are built
from the same declarations, each handle in its initial state. -/
theorem Program.initOK (prog : Program K St R) : PeriphsOK prog.initPCtx prog.initPeriphs := by
  unfold Program.initPCtx Program.initPeriphs
  induction prog.periphs with
  | nil => intro x; exact trivial
  | cons h hs ih => exact ih.set _ _ (Finset.mem_singleton_self _)

/-- **Whole-program soundness.**  Running a well-typed program from clock `K₀` costs at most
`Q K₀ 0` (nothing is ambient at top level).  By monotonicity (`Typed.mono`), the bound at any
typed clock `f₀ ≥ K₀` is `Q f₀ 0`. -/
theorem Program.soundness (hM : M.WF) {prog : Program K St R}
    {Ψ Γ' Δ' Q F} (ht : prog.Typed P M Ψ Γ' Δ' Q F)
    {K₀ σ' S' q' K'} (he : prog.Eval M K₀ σ' S' q' K') :
    q' ≤ Q K₀ 0 := by
  have h := (_root_.soundness hM (Program.sigsValid hM ht) ht.2.2 he
    (fun _ _ hx => by simp [TCtx.empty] at hx) (Program.initOK prog)).1
  simpa [ambBg] using h
