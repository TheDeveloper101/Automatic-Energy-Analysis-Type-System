import Heliod.Slack
import Heliod.Accounting

/-!
# Necessity: the slack terms arise only where the type system lacks information

`Heliod.Slack` shows that along any path the summary is the path's cost plus a list of local
slack terms.  This file shows that the `state` terms — the ones caused by multi-state typing
contexts — are *necessary* given the information in the context, and arise only from a known
set of sources.  See `IMPRECISION.md` for the examples.

1. **Local attainment** (`PCtx.bg_attained`, `PCtx.trans_attained`).  Every typed charge of a
   step is the actual charge for *some* runtime state consistent with the context at that point:
   * `cost(Δ)` (the background charge of `let`, the condition of `if`, `clock`, the `match` step
     with `Δ[p : {s}]`, a call's argument step, a return step, and — for `Δ ∖ p` — the ambient
     instantiation of a call) is `bg(S)` for a worst-case `S ⊨ Δ`;
   * `maxTrans(k, Δ(p), st) + cost(Δ ∖ p)` (transition / downgrade) is
     `transCost(s, st) + bg(S ∖ p)` for a worst-case `S ⊨ Δ` with `S(p) = s`.
   So no single typed charge can be lowered without excluding a state the context allows: any
   sound analysis that knows only `Δ` at that point must charge at least this much.  Together
   with `PeriphsOK.bg_le` and `transCost_le_maxTrans`, the typed charge is exactly the maximum
   of the actual charge over the states consistent with `Δ`.
2. **No uncertainty, no state slack** (`PeriphsOK.bg_eq_of_pinned`, `maxTrans_singleton`).  If
   the context pins down every peripheral (`PCtx.Pinned`: single-state sets), the typed charge
   *is* the actual charge, so the `state` term there is `0`.
3. **Origin of uncertainty** (`Typed.pinned`).  Starting from a pinned context, typing produces
   a pinned context unless the command contains an `if` (whose join merges states) or calls a
   function with several possible output states; `match` with distinct arm states on a pinned
   handle selects a single arm and merges nothing.  Contrapositively, a multi-state context — the
   only cause of nonzero `state` slack — arises only from a multi-state function input, a merge
   after a branch, or a multi-state call output.
-/

variable {K St R : Type} [DecidableEq K] [DecidableEq St]
variable [CommSemiring R] [LinearOrder R] [OrderBot R]
variable {M : CostModel K St R}

/-! ### Background sums from pointwise facts -/

omit [DecidableEq K] [DecidableEq St] in
/-- Runtime and static background costs agree when they agree handle by handle.  Shared by
the attainment and the pinned-context lemmas. -/
theorem RPeriphs.bg_eq_of_pointwise {Δ : PCtx K St} {S : RPeriphs K St}
    (h : ∀ x, (S x).bg M = (Δ x).bg M) : S.bg M = Δ.bg M := by
  unfold RPeriphs.bg PCtx.bg
  rw [Finsupp.sum_of_support_subset S (Finset.subset_union_left (s₂ := Δ.support)) _
      (fun _ _ => rfl),
    Finsupp.sum_of_support_subset Δ (Finset.subset_union_right (s₁ := S.support)) _
      (fun _ _ => rfl)]
  exact Finset.sum_congr rfl fun x _ => h x

omit [DecidableEq St] [CommSemiring R] in
/-- A `sup` over a finite set is attained at a maximizing element. -/
private theorem sup_eq_of_max {T : Finset St} {f : St → R} {s : St} (hs : s ∈ T)
    (hmax : ∀ t ∈ T, f t ≤ f s) : T.sup f = f s :=
  le_antisymm (Finset.sup_le hmax) (Finset.le_sup hs)

/-! ### 1. Local attainment -/

/-- Every handle bound in `Δ` has at least one possible state.  (Needed for a consistent runtime
state to exist at all.) -/
def PCtx.NonEmpty (Δ : PCtx K St) : Prop :=
  ∀ x k T, Δ x = .live k T → T.Nonempty

open Classical in
/-- The runtime entry with the largest background cost among those a typing entry allows. -/
noncomputable def PEntry.worst (M : CostModel K St R) : PEntry K St → REntry K St
  | .absent => .absent
  | .live k T =>
      if h : T.Nonempty then .at k (Classical.choose (T.exists_max_image (M.bgCost k) h))
      else .absent

/-- A worst-case runtime state for `Δ`: every handle in a state of maximal background cost. -/
noncomputable def PCtx.worst (M : CostModel K St R) (Δ : PCtx K St) : RPeriphs K St :=
  Finsupp.mapRange (PEntry.worst M) rfl Δ

omit [DecidableEq K] [DecidableEq St] in
/-- Pointwise facts about `PCtx.worst`: it agrees with `Δ` and its background cost is the
worst case `maxBg`. -/
private theorem PCtx.worst_apply {Δ : PCtx K St} (hne : Δ.NonEmpty) (x : Var) :
    ((Δ.worst M) x).Approx (Δ x) ∧ ((Δ.worst M) x).bg M = (Δ x).bg M := by
  have e : (Δ.worst M) x = PEntry.worst M (Δ x) := Finsupp.mapRange_apply
  rw [e]
  rcases h : Δ x with _ | ⟨k, T⟩
  · exact ⟨trivial, rfl⟩
  · have hT := hne x k T h
    obtain ⟨hs, hmax⟩ := Classical.choose_spec (T.exists_max_image (M.bgCost k) hT)
    simp only [PEntry.worst, hT, ↓reduceDIte, REntry.Approx, REntry.bg, PEntry.bg,
      CostModel.maxBg]
    exact ⟨by simp [hs], (sup_eq_of_max hs hmax).symm⟩

omit [DecidableEq K] [DecidableEq St] in
/-- The worst-case state is consistent with the context. -/
theorem PCtx.worst_ok {Δ : PCtx K St} (hne : Δ.NonEmpty) : PeriphsOK Δ (Δ.worst M) :=
  fun x => (PCtx.worst_apply hne x).1

omit [DecidableEq K] [DecidableEq St] in
/-- **Background charges are attained.**  For every context with nonempty state sets there is a
consistent runtime state whose background cost is exactly the typed `cost(Δ)`.  So every typed
background charge (each `state` term's typed side involving `cost(Δ)`) is necessary given `Δ`. -/
theorem PCtx.bg_attained {Δ : PCtx K St} (hne : Δ.NonEmpty) :
    ∃ S, PeriphsOK Δ S ∧ S.bg M = Δ.bg M :=
  ⟨Δ.worst M, PCtx.worst_ok hne, RPeriphs.bg_eq_of_pointwise fun x => (PCtx.worst_apply hne x).2⟩

omit [DecidableEq K] [DecidableEq St] in
/-- Erasing a handle keeps state sets nonempty. -/
theorem PCtx.NonEmpty.erase {Δ : PCtx K St} (hne : Δ.NonEmpty) (p : Var) :
    (Δ.erase p).NonEmpty := by
  intro x k T h
  rw [PCtx.erase_apply] at h
  by_cases hx : x = p
  · simp only [hx, ↓reduceIte] at h; exact absurd h (fun h' => by cases h')
  · simp only [hx, ↓reduceIte] at h; exact hne x k T h

omit [DecidableEq K] [DecidableEq St] in
/-- Re-setting a handle to the entry it already has is a no-op. -/
private theorem PCtx.set_eq_self' {Δ : PCtx K St} {p : Var} {k : K} {T : Finset St}
    (h : Δ p = .live k T) : Δ.set p k T = Δ := by
  ext x
  rw [PCtx.set_apply]
  split_ifs with hx
  · subst hx; exact h.symm
  · rfl

omit [DecidableEq K] [DecidableEq St] in
/-- **Transition charges are attained.**  For `transition(p, st)` / `downgrade(p, st)` with
`Δ(p) = (k, T)`, there is a runtime state consistent with `Δ`, with `p` in some `s ∈ T`, whose
actual charge `transCost(s, st) + bg(S ∖ p)` is exactly the typed
`maxTrans(k, T, st) + cost(Δ ∖ p)`. -/
theorem PCtx.trans_attained {Δ : PCtx K St} (hne : Δ.NonEmpty) {p : Var} {k : K}
    {T : Finset St} (hp : Δ p = .live k T) (st : St) :
    ∃ S s, PeriphsOK Δ S ∧ S p = .at k s ∧
      M.transCost k s st + (S.erase p).bg M = M.maxTrans k T st + (Δ.erase p).bg M := by
  obtain ⟨s, hs, hmax⟩ := T.exists_max_image (fun s => M.transCost k s st) (hne p k T hp)
  refine ⟨(Δ.worst M).set p k s, s, ?_, by simp, ?_⟩
  · have := (PCtx.worst_ok (M := M) hne).set p k hs
    rwa [PCtx.set_eq_self' hp] at this
  · rw [RPeriphs.erase_set, CostModel.maxTrans, sup_eq_of_max hs hmax]
    congr 1
    refine RPeriphs.bg_eq_of_pointwise fun x => ?_
    rw [RPeriphs.erase_apply, PCtx.erase_apply]
    split_ifs
    · rfl
    · exact (PCtx.worst_apply hne x).2

/-! ### 2. Pinned contexts have no state slack -/

/-- `Δ` pins down every peripheral: each bound handle has exactly one possible state. -/
def PCtx.Pinned (Δ : PCtx K St) : Prop :=
  ∀ x k T, Δ x = .live k T → ∃ s, T = {s}

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] in
/-- With a single possible source state the worst-case transition cost is the actual one. -/
theorem maxTrans_singleton (M : CostModel K St R) (k : K) (s st : St) :
    M.maxTrans k {s} st = M.transCost k s st := by
  simp [CostModel.maxTrans]

omit [DecidableEq K] [DecidableEq St] in
/-- **No uncertainty, no state slack.**  If `Δ` pins down every peripheral, the typed background
charge `cost(Δ)` equals the actual `bg(S)` for the (unique) consistent runtime state. -/
theorem PeriphsOK.bg_eq_of_pinned {Δ : PCtx K St} {S : RPeriphs K St} (hS : PeriphsOK Δ S)
    (hpin : Δ.Pinned) : S.bg M = Δ.bg M := by
  refine RPeriphs.bg_eq_of_pointwise fun x => ?_
  have a := hS x
  rcases e : Δ x with _ | ⟨k, T⟩ <;> rcases e' : S x with _ | ⟨k', s⟩ <;>
    rw [e, e'] at a <;> simp only [REntry.Approx] at a
  · rfl
  · obtain ⟨s₀, rfl⟩ := hpin x k T e
    obtain ⟨rfl, hs⟩ := a
    rw [Finset.mem_singleton] at hs; subst hs
    simp [REntry.bg, PEntry.bg, CostModel.maxBg]

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] in
/-- Setting a handle to a single state keeps a context pinned. -/
theorem PCtx.Pinned.set {Δ : PCtx K St} (h : Δ.Pinned) (p : Var) (k : K) (s : St) :
    (Δ.set p k {s}).Pinned := by
  intro x k' T hx
  rw [PCtx.set_apply] at hx
  split_ifs at hx
  · cases hx; exact ⟨s, rfl⟩
  · exact h x k' T hx

/-! ### 3. Origin of uncertainty -/

/-- Match arms have pairwise distinct states (the well-formedness condition agreed for
`match`). -/
def Arms.Distinct {R : Type} : Arms St R → Prop
  | .nil => True
  | .cons st _ rest => st ∉ rest.states ∧ rest.Distinct

mutual

/-- Commands without merges: no `if`, and every `match` has distinct arm states (so on a pinned
handle it selects a single arm). -/
def Cmd.NoBranch {R : Type} : Cmd St R → Prop
  | .ite .. => False
  | .seq c₁ c₂ => c₁.NoBranch ∧ c₂.NoBranch
  | .matchSt _ arms => arms.Distinct ∧ arms.NoBranch
  | _ => True

/-- Every arm is merge-free. -/
def Arms.NoBranch {R : Type} : Arms St R → Prop
  | .nil => True
  | .cons _ c rest => c.NoBranch ∧ rest.NoBranch

end

variable {P : Platform K St} {Ψ : SigCtx K St R}


/-- A typed `match` has at least one reachable arm. -/
theorem ArmsTyped.exists_reachable {Γ Δ p k T arms Γ' Δ' Q F} :
    ArmsTyped P M Ψ Γ Δ p k T arms Γ' Δ' Q F → ∃ st ∈ arms.states, st ∈ T
  | .last (st := st) hst _ _ => ⟨st, by simp [Arms.states], hst⟩
  | .cons (st := st) hst _ _ => ⟨st, by simp [Arms.states], hst⟩
  | .skip _ ha =>
      have ⟨st, hm, hst⟩ := ha.exists_reachable
      ⟨st, by simp [Arms.states, hm], hst⟩

mutual

/-- **Origin of uncertainty.**  If every signature has a single possible output state, a
merge-free command (no `if`; `match` with distinct arms) typed from a pinned context ends in a
pinned context.  Contrapositively, multi-state contexts — the only cause of nonzero `state`
slack — come only from a multi-state starting context (a function's input states), a merge
after an `if`, or a call with several possible output states. -/
theorem Typed.pinned (hΨ1 : ∀ g sig, Ψ g = some sig → ∃ s, sig.sOut = {s})
    {Γ Δ c Γ' Δ' Q F} :
    Typed P M Ψ Γ Δ c Γ' Δ' Q F → c.NoBranch → Δ.Pinned → Δ'.Pinned
  | .skip, _, h => h
  | .assign _ _, _, h => h
  | .ite _ _ _, hc, _ => by simp [Cmd.NoBranch] at hc
  | .transition _ _ _, _, h => h.set _ _ _
  | .downgrade _ _ _, _, h => h.set _ _ _
  | .clock _, _, h => h
  | .seq h₁ h₂, hc, h => by
      simp only [Cmd.NoBranch] at hc
      exact h₂.pinned hΨ1 hc.2 (h₁.pinned hΨ1 hc.1 h)
  | .matchSt hp _ ha, hc, h => by
      simp only [Cmd.NoBranch] at hc
      obtain ⟨s, rfl⟩ := h _ _ _ hp
      exact ha.pinned hΨ1 hc.1 hc.2 h
  | .call hg _ _ _ _, _, h => by
      obtain ⟨s, hs⟩ := hΨ1 _ _ hg
      rw [hs]; exact h.set _ _ _

/-- Arms version of `Typed.pinned`: on a pinned handle (`T = {s}`) with distinct arm states only
one arm is reachable, so no join happens. -/
theorem ArmsTyped.pinned (hΨ1 : ∀ g sig, Ψ g = some sig → ∃ s, sig.sOut = {s})
    {Γ Δ p k s arms Γ' Δ' Q F} :
    ArmsTyped P M Ψ Γ Δ p k {s} arms Γ' Δ' Q F → arms.Distinct → arms.NoBranch →
    Δ.Pinned → Δ'.Pinned
  | .last _ h _, _, hn, hpin => by
      simp only [Arms.NoBranch] at hn
      exact h.pinned hΨ1 hn.1 (hpin.set _ _ _)
  | .cons hst _ ha, hd, _, _ => by
      simp only [Arms.Distinct] at hd
      obtain ⟨st', hm, hst'⟩ := ha.exists_reachable
      rw [Finset.mem_singleton] at hst hst'
      subst hst hst'
      exact absurd hm hd.1
  | .skip _ ha, hd, hn, hpin => by
      simp only [Arms.Distinct] at hd
      simp only [Arms.NoBranch] at hn
      exact ha.pinned hΨ1 hd.2 hn.2 hpin

end
