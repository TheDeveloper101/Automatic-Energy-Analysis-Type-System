import Heliod.AsyncSoundness

/-!
# Async soundness — piece 3a: invariants of the async typing

Pure lemmas about `TypedA` that the configuration typing (piece 3b) relies on.  See
`ASYNC_PROOF_PLAN.md`, "Configuration typing".

* **Frozen clock** (`TypedA.frozen_clk`): a frozen derivation never changes the clock (its exit
  clock summary is the identity), given that `stableClock` signatures have the identity as
  clock summary.  Async bodies and functions called while threads are pending are frozen, so
  the whole window runs at the spawn clock.
* **Window shapes** (`TypedA.winShape`): every pending thread's window has the shape of the
  current context, so joining a context into a window is a pointwise union.
* **Backward window bound** (`TypedA.ambOK_back`): if every thread pending at the end of a
  command has its window within its declared bound, so does every thread pending at the start.
  Windows only grow along the typing, and a thread awaited inside the command had its (larger)
  window checked by the `await`.  Since control stacks end with no pending threads, the bound
  holds at every point of a run.
* **Visited contexts** (`TypedA.le_W`): the input and output contexts are below the visited
  context `W`.
-/

variable {K St R : Type} [DecidableEq K] [DecidableEq St]
variable [CommSemiring R] [LinearOrder R] [OrderBot R]
variable {P : Platform K St} {M : CostModel K St R} {Ψ : SigCtxA K St R}

/-! ### Frozen clock -/

mutual

/-- **A frozen derivation never changes the clock.**  The clock rule requires `fz = false`; a
call in a frozen setting goes to a `stableClock` function, whose clock summary is the identity;
everything else composes identities. -/
theorem TypedA.frozen_clk
    (hΨc : ∀ g sig, Ψ g = some sig → sig.stableClock = true → ∀ f, sig.clk f = f)
    {fz Γ Δ Θ c Γ' Δ' Θ' W Q F} :
    TypedA P M Ψ fz Γ Δ Θ c Γ' Δ' Θ' W Q F → fz = true → ∀ f, F f = f
  | .skip, _, _ => rfl
  | .assign _ _, _, _ => rfl
  | .ite _ h₁ h₂ _, hfz, f => by
      simp [h₁.frozen_clk hΨc hfz f, h₂.frozen_clk hΨc hfz f]
  | .transition _ _ _ _, _, _ => rfl
  | .transitionU _ _ _ _, _, _ => rfl
  | .downgrade _ _ _ _, _, _ => rfl
  | .clock hfz' _ _, hfz, _ => by rw [hfz] at hfz'; cases hfz'
  | .seq h₁ h₂, hfz, f => by
      simp only [h₁.frozen_clk hΨc hfz f, h₂.frozen_clk hΨc hfz f]
  | .matchSt _ _ _ ha, hfz, f => ha.frozen_clk hΨc hfz f
  | .call hg _ _ _ _ _ hst, hfz, f => hΨc _ _ hg (hst (Or.inl hfz)) f
  | .async _ _ _ _ _ _ _ _ _ _, _, _ => rfl
  | .await _ _ _ hfb _ _ _, hfz, f => by simp [hfb.frozen_clk hΨc hfz f]

/-- Arms version of `TypedA.frozen_clk`. -/
theorem ArmsTypedA.frozen_clk
    (hΨc : ∀ g sig, Ψ g = some sig → sig.stableClock = true → ∀ f, sig.clk f = f)
    {fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F} :
    ArmsTypedA P M Ψ fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F → fz = true → ∀ f, F f = f
  | .last _ h _, hfz, f => h.frozen_clk hΨc hfz f
  | .cons _ h ha _, hfz, f => by
      simp [h.frozen_clk hΨc hfz f, ha.frozen_clk hΨc hfz f]
  | .skip _ ha, hfz, f => ha.frozen_clk hΨc hfz f

end

/-! ### Window shapes -/

/-- Every pending thread's window has shape `sh`. -/
def ThreadCtx.WinShape (Θ : ThreadCtx K St R) (sh : Var → Option K) : Prop :=
  ∀ t th, Θ t = some th → th.win.shape = sh

namespace ThreadCtx

omit [CommSemiring R] [LinearOrder R] [OrderBot R] in
/-- Observing a context of the same shape keeps window shapes. -/
theorem WinShape.observe {Θ : ThreadCtx K St R} {sh} (h : Θ.WinShape sh) {Δ : PCtx K St}
    (hΔ : Δ.shape = sh) : (Θ.observe Δ).WinShape sh := by
  intro t th ht
  simp only [ThreadCtx.observe, Option.map_eq_some_iff] at ht
  obtain ⟨th₀, h₀, rfl⟩ := ht
  exact (PCtx.shape_join ((h t th₀ h₀).trans hΔ.symm)).trans (h t th₀ h₀)

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] in
/-- Removing a thread keeps window shapes. -/
theorem WinShape.erase {Θ : ThreadCtx K St R} {sh} (h : Θ.WinShape sh) (t₀ : Var) :
    (Θ.erase t₀).WinShape sh := by
  intro t th ht
  unfold ThreadCtx.erase at ht
  by_cases e : t = t₀
  · subst e; simp at ht
  · rw [Function.update_of_ne e] at ht; exact h t th ht

omit [CommSemiring R] [LinearOrder R] [OrderBot R] in
/-- Joining two thread contexts with windows of the same shape keeps it. -/
theorem WinShape.join {Θ₁ Θ₂ : ThreadCtx K St R} {sh} (h₁ : Θ₁.WinShape sh)
    (h₂ : Θ₂.WinShape sh) : (Θ₁.join Θ₂).WinShape sh := by
  intro t th ht
  simp only [ThreadCtx.join] at ht
  split at ht
  · rename_i a b ha hb
    cases ht
    exact (PCtx.shape_join ((h₁ t a ha).trans (h₂ t b hb).symm)).trans (h₁ t a ha)
  · cases ht

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] in
/-- Adding a thread whose window has the shape. -/
theorem WinShape.update {Θ : ThreadCtx K St R} {sh} (h : Θ.WinShape sh) (t₀ : Var)
    (th₀ : ThreadTy K St R) (h₀ : th₀.win.shape = sh) :
    ThreadCtx.WinShape (Function.update Θ t₀ (some th₀)) sh := by
  intro t th ht
  by_cases e : t = t₀
  · subst e; simp only [Function.update_self, Option.some.injEq] at ht; subst ht; exact h₀
  · rw [Function.update_of_ne e] at ht; exact h t th ht

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] in
/-- No threads, nothing to check. -/
theorem WinShape.empty {sh : Var → Option K} :
    (ThreadCtx.empty : ThreadCtx K St R).WinShape sh :=
  fun _ _ h => by cases h

end ThreadCtx

mutual

/-- **Windows keep the shape of the context.**  Every rule joins into windows only contexts of
the input's shape (typing preserves shapes), and a spawn starts its window at the current
context. -/
theorem TypedA.winShape {fz Γ Δ Θ c Γ' Δ' Θ' W Q F} :
    TypedA P M Ψ fz Γ Δ Θ c Γ' Δ' Θ' W Q F → Θ.WinShape Δ.shape → Θ'.WinShape Δ.shape
  | .skip, h => h
  | .assign _ _, h => h
  | .ite _ h₁ h₂ _, h => (h₁.winShape h).join (h₂.winShape h)
  | .transition hp _ _ _, h => h.observe (PCtx.shape_set_of hp _)
  | .transitionU hp _ _ _, h => h.observe (PCtx.shape_set_of hp _)
  | .downgrade hp _ _ _, h => h.observe (PCtx.shape_set_of hp _)
  | .clock _ _ _, h => h
  | .seq h₁ h₂, h => by
      have h₁' := h₁.winShape h
      rw [← h₁.shape_eq.1] at h₁' ⊢
      exact h₂.winShape h₁'
  | .matchSt hp _ _ ha, h => by
      have e := PCtx.shape_set_of hp ∅
      rw [← e] at h ⊢
      exact ha.winShape h
  | .call _ _ _ hp _ _ _, h =>
      (h.observe (PCtx.shape_set_of hp _)).observe (PCtx.shape_set_of hp _)
  | .async hp _ _ _ _ _ _ _ _ _, h => by
      refine (h.observe (PCtx.shape_set_of hp _)).update _ _ ?_
      exact PCtx.shape_set_of hp _
  | .await _ hp _ hfb _ _ _, h =>
      ((h.erase _).observe (PCtx.shape_set_of hp _)).join (hfb.winShape (h.erase _))

/-- Arms version of `TypedA.winShape` (shape of `Δ` with `p` at kind `k`). -/
theorem ArmsTypedA.winShape {fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F} :
    ArmsTypedA P M Ψ fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F →
    Θ.WinShape (Δ.set p k ∅).shape → Θ'.WinShape (Δ.set p k ∅).shape
  | .last (st := st) _ hc _, h => by
      have e := PCtx.shape_set_set Δ p k (P.hwClose k {st}) ∅
      have h' := h.observe e
      rw [← e] at h' ⊢
      exact hc.winShape h'
  | .cons (st := st) _ hc ha _, h => by
      have e := PCtx.shape_set_set Δ p k (P.hwClose k {st}) ∅
      have h' := h.observe e
      rw [← e] at h'
      have := hc.winShape h'
      rw [e] at this
      exact this.join (ha.winShape h)
  | .skip _ ha, h => ha.winShape h

end

/-! ### Context precision and background cost -/

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] in
/-- The shape of `Δ ∖ p` depends only on the shape of `Δ`. -/
theorem PCtx.shape_erase_congr {Δ₁ Δ₂ : PCtx K St} (h : Δ₁.shape = Δ₂.shape) (p : Var) :
    (Δ₁.erase p).shape = (Δ₂.erase p).shape := by
  funext x
  have hx := congrFun h x
  simp only [PCtx.shape, PCtx.erase_apply] at hx ⊢
  split_ifs
  · rfl
  · exact hx

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] in
/-- Removing a handle preserves precision. -/
theorem PCtx.Le.erase {Δ₁ Δ₂ : PCtx K St} (h : Δ₁.Le Δ₂) (p : Var) :
    (Δ₁.erase p).Le (Δ₂.erase p) := by
  intro x
  simp only [PCtx.erase_apply]
  split_ifs
  · exact trivial
  · exact h x

/-- The kind of a typing entry, `none` if absent. -/
def PEntry.kindOf : PEntry K St → Option K
  | .absent => none
  | .live k _ => some k

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] in
/-- The shape of a context, pointwise. -/
theorem PCtx.shape_apply (Δ : PCtx K St) (x : Var) : Δ.shape x = (Δ x).kindOf := by
  unfold PCtx.shape; cases Δ x <;> rfl

omit [CommSemiring R] [LinearOrder R] [OrderBot R] in
/-- Entry joins are monotone in both arguments (for entries of the same kind or both absent). -/
theorem PEntry.join_le_join {A A' B B' : PEntry K St} (h₁ : A.Le A') (h₂ : B.Le B')
    (h₃ : A.kindOf = B.kindOf) :
    (PEntry.join A B).Le (PEntry.join A' B') := by
  rcases A with _ | ⟨k₁, S₁⟩ <;> rcases A' with _ | ⟨k₂, S₂⟩ <;>
    rcases B with _ | ⟨k₃, S₃⟩ <;> rcases B' with _ | ⟨k₄, S₄⟩
  all_goals try first
    | exact h₁.elim
    | exact h₂.elim
    | exact trivial
  all_goals
    obtain ⟨rfl, hS₁⟩ := h₁
    obtain ⟨rfl, hS₂⟩ := h₂
    cases h₃
    simp only [PEntry.join, ↓reduceIte, PEntry.Le, true_and]
    exact Finset.union_subset_union hS₁ hS₂

omit [CommSemiring R] [LinearOrder R] [OrderBot R] in
/-- Joins are monotone in both arguments (for contexts of one shape). -/
theorem PCtx.join_le_join {a a' b b' : PCtx K St} (ha : a.Le a') (hb : b.Le b')
    (hs : a.shape = b.shape) : (a.join b).Le (a'.join b') := by
  intro x
  have h₁ := ha x
  have h₂ := hb x
  have h₃ := congrFun hs x
  simp only [PCtx.join_apply]
  rw [PCtx.shape_apply, PCtx.shape_apply] at h₃
  revert h₁ h₂ h₃
  generalize a x = A
  generalize a' x = A'
  generalize b x = B
  generalize b' x = B'
  intro h₁ h₂ h₃
  exact PEntry.join_le_join h₁ h₂ h₃

variable [IsOrderedRing R]

omit [DecidableEq K] [DecidableEq St] [IsOrderedRing R] in
/-- A less precise entry costs at least as much. -/
theorem PEntry.Le.bg_le {e₁ e₂ : PEntry K St} (h : e₁.Le e₂) : e₁.bg M ≤ e₂.bg M := by
  cases e₁ <;> cases e₂
  · exact le_rfl
  · exact h.elim
  · exact h.elim
  · obtain ⟨rfl, hs⟩ := h
    exact M.maxBg_mono hs

omit [DecidableEq K] [DecidableEq St] in
/-- **A less precise context costs at least as much**: `Δ₁ ⊑ Δ₂ → cost(Δ₁) ≤ cost(Δ₂)`. -/
theorem PCtx.Le.bg_le {Δ₁ Δ₂ : PCtx K St} (h : Δ₁.Le Δ₂) : Δ₁.bg M ≤ Δ₂.bg M := by
  unfold PCtx.bg
  rw [Finsupp.sum_of_support_subset Δ₁ (Finset.subset_union_left (s₂ := Δ₂.support)) _
      (fun _ _ => rfl),
    Finsupp.sum_of_support_subset Δ₂ (Finset.subset_union_right (s₁ := Δ₁.support)) _
      (fun _ _ => rfl)]
  exact Finset.sum_le_sum fun x _ => PEntry.Le.bg_le (h x)

/-! ### The backward window bound -/

/-- Every pending thread's window, without its own device, fits the bound declared at the
spawn: `cost(win ∖ p) ≤ amb`. -/
def ThreadCtx.AmbOK (M : CostModel K St R) (Θ : ThreadCtx K St R) : Prop :=
  ∀ t th, Θ t = some th → (th.win.erase th.p).bg M ≤ th.amb

namespace ThreadCtx

/-- Before observing a context, windows were smaller. -/
theorem AmbOK.of_observe {Θ : ThreadCtx K St R} {sh} {Δ : PCtx K St}
    (h : (Θ.observe Δ).AmbOK M) (hw : Θ.WinShape sh) (hΔ : Δ.shape = sh) : Θ.AmbOK M := by
  intro t th ht
  have hb := h t { th with win := th.win.join Δ } (by simp [ThreadCtx.observe, ht])
  refine le_trans (PCtx.Le.bg_le ?_) hb
  show (th.win.erase th.p).Le ((th.win.join Δ).erase th.p)
  rw [PCtx.erase_join]
  exact PCtx.le_join_left (PCtx.shape_erase_congr ((hw t th ht).trans hΔ.symm) _)

/-- A branch's windows are within the joined ones. -/
theorem AmbOK.of_join {Θ₁ Θ₂ : ThreadCtx K St R} {sh} (h : (Θ₁.join Θ₂).AmbOK M)
    (hs : Θ₁.SameThreads Θ₂) (hw₁ : Θ₁.WinShape sh) (hw₂ : Θ₂.WinShape sh) : Θ₁.AmbOK M := by
  intro t a ha
  rcases hs t with ⟨e₁, _⟩ | ⟨a', b, e₁, e₂, _⟩
  · rw [ha] at e₁; cases e₁
  · rw [ha] at e₁; cases e₁
    have hb := h t { a with win := a.win.join b.win } (by simp [ThreadCtx.join, ha, e₂])
    refine le_trans (PCtx.Le.bg_le ?_) hb
    show (a.win.erase a.p).Le ((a.win.join b.win).erase a.p)
    rw [PCtx.erase_join]
    exact PCtx.le_join_left
      (PCtx.shape_erase_congr ((hw₁ t a ha).trans (hw₂ t b e₂).symm) _)

omit [DecidableEq K] [DecidableEq St] [IsOrderedRing R] in
/-- Removing an awaited thread whose window was checked. -/
theorem AmbOK.of_erase {Θ : ThreadCtx K St R} {t₀ : Var} (h : (Θ.erase t₀).AmbOK M)
    (h₀ : ∀ th, Θ t₀ = some th → (th.win.erase th.p).bg M ≤ th.amb) : Θ.AmbOK M := by
  intro t th ht
  by_cases e : t = t₀
  · subst e; exact h₀ th ht
  · exact h t th (by unfold ThreadCtx.erase; rw [Function.update_of_ne e]; exact ht)

omit [DecidableEq K] [DecidableEq St] [IsOrderedRing R] in
/-- A thread spawned under a fresh id was not pending before. -/
theorem AmbOK.of_update {Θ : ThreadCtx K St R} {t₀ : Var} {x : ThreadTy K St R}
    (h : ThreadCtx.AmbOK M (Function.update Θ t₀ (some x))) (h₀ : Θ t₀ = none) :
    Θ.AmbOK M := by
  intro t th ht
  have e : t ≠ t₀ := by rintro rfl; rw [h₀] at ht; cases ht
  exact h t th (by rw [Function.update_of_ne e]; exact ht)

end ThreadCtx

mutual

/-- **The backward window bound.**  If the threads pending after `c` have their windows within
their declared bounds, so do the threads pending before: windows only grow along the typing,
and a thread awaited in `c` had its larger window checked by the `await`. -/
theorem TypedA.ambOK_back {fz Γ Δ Θ c Γ' Δ' Θ' W Q F} :
    TypedA P M Ψ fz Γ Δ Θ c Γ' Δ' Θ' W Q F → Θ.WinShape Δ.shape → Θ'.AmbOK M → Θ.AmbOK M
  | .skip, _, h => h
  | .assign _ _, _, h => h
  | .ite _ h₁ h₂ hs, hw, h =>
      h₁.ambOK_back hw (h.of_join hs (h₁.winShape hw) (h₂.winShape hw))
  | .transition hp _ _ _, hw, h => h.of_observe hw (PCtx.shape_set_of hp _)
  | .transitionU hp _ _ _, hw, h => h.of_observe hw (PCtx.shape_set_of hp _)
  | .downgrade hp _ _ _, hw, h => h.of_observe hw (PCtx.shape_set_of hp _)
  | .clock _ _ _, _, h => h
  | .seq h₁ h₂, hw, h => by
      have hw₁ := h₁.winShape hw
      rw [← h₁.shape_eq.1] at hw₁
      exact h₁.ambOK_back hw (h₂.ambOK_back hw₁ h)
  | .matchSt hp _ _ ha, hw, h => by
      have e := PCtx.shape_set_of hp ∅
      rw [← e] at hw
      exact ha.ambOK_back hw h
  | .call _ _ _ hp _ _ _, hw, h =>
      (h.of_observe (hw.observe (PCtx.shape_set_of hp _)) (PCtx.shape_set_of hp _)).of_observe hw
        (PCtx.shape_set_of hp _)
  | .async hp _ hfresh _ _ _ _ _ _ _, hw, h =>
      (h.of_update (by simp [ThreadCtx.observe, hfresh])).of_observe hw (PCtx.shape_set_of hp _)
  | .await (tid := tid) (th := th) ht hp hamb hfb hs _ _, hw, h => by
      have hwe := (hw.erase tid).observe (PCtx.shape_set_of hp th.sOut)
      have hl := h.of_join (by
          intro t
          rcases hs t with ⟨e₁, e₂⟩ | ⟨a, b, e₁, e₂, hab⟩
          · exact Or.inl ⟨by simp [ThreadCtx.observe, e₁], e₂⟩
          · exact Or.inr ⟨{ a with win := a.win.join (Δ.set th.p th.k th.sOut) }, b,
              by simp [ThreadCtx.observe, e₁], e₂, hab⟩)
        hwe (hfb.winShape (hw.erase _))
      refine (hl.of_observe (hw.erase _) (PCtx.shape_set_of hp _)).of_erase ?_
      intro th' ht'
      rw [ht] at ht'; cases ht'
      exact hamb

/-- Arms version of `TypedA.ambOK_back`. -/
theorem ArmsTypedA.ambOK_back {fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F} :
    ArmsTypedA P M Ψ fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F →
    Θ.WinShape (Δ.set p k ∅).shape → Θ'.AmbOK M → Θ.AmbOK M
  | .last (st := st) _ hc _, hw, h => by
      have e := PCtx.shape_set_set Δ p k (P.hwClose k {st}) ∅
      have hw' := hw.observe e
      rw [← e] at hw'
      exact (hc.ambOK_back hw' h).of_observe hw e
  | .cons (st := st) _ hc ha hs, hw, h => by
      have e := PCtx.shape_set_set Δ p k (P.hwClose k {st}) ∅
      have hw' := hw.observe e
      rw [← e] at hw'
      have hw₁ := hc.winShape hw'
      rw [e] at hw₁
      exact (hc.ambOK_back hw' (h.of_join hs hw₁ (ha.winShape hw))).of_observe hw e
  | .skip _ ha, hw, h => ha.ambOK_back hw h

end

/-! ### Visited contexts -/

set_option linter.unusedSectionVars false in
mutual

/-- **Input and output contexts are below the visited context `W`.** -/
theorem TypedA.le_W {fz Γ Δ Θ c Γ' Δ' Θ' W Q F} :
    TypedA P M Ψ fz Γ Δ Θ c Γ' Δ' Θ' W Q F → Δ.Le W ∧ Δ'.Le W
  | .skip => ⟨PCtx.Le.refl _, PCtx.Le.refl _⟩
  | .assign _ _ => ⟨PCtx.Le.refl _, PCtx.Le.refl _⟩
  | .clock _ _ _ => ⟨PCtx.Le.refl _, PCtx.Le.refl _⟩
  | .ite _ h₁ h₂ _ =>
      have ⟨a₁, b₁⟩ := h₁.le_W
      have ⟨_, b₂⟩ := h₂.le_W
      have hW := h₁.shape_eq.2.trans h₂.shape_eq.2.symm
      ⟨a₁.trans (PCtx.le_join_left hW),
        PCtx.join_le_join b₁ b₂ (h₁.shape_eq.1.trans h₂.shape_eq.1.symm)⟩
  | .transition hp _ _ _ =>
      have h := PCtx.shape_set_of hp _
      ⟨PCtx.le_join_left h.symm, PCtx.le_join_right h.symm⟩
  | .transitionU hp _ _ _ =>
      have h := PCtx.shape_set_of hp _
      ⟨PCtx.le_join_left h.symm, PCtx.le_join_right h.symm⟩
  | .downgrade hp _ _ _ =>
      have h := PCtx.shape_set_of hp _
      ⟨PCtx.le_join_left h.symm, PCtx.le_join_right h.symm⟩
  | .seq h₁ h₂ =>
      have ⟨a₁, _⟩ := h₁.le_W
      have ⟨_, b₂⟩ := h₂.le_W
      have hW : _ := h₁.shape_eq.2.trans (h₂.shape_eq.2.trans h₁.shape_eq.1).symm
      ⟨a₁.trans (PCtx.le_join_left hW), b₂.trans (PCtx.le_join_right hW)⟩
  | .matchSt hp _ _ ha =>
      have hW : _ := (ha.shape_eq.2.trans (PCtx.shape_set_of hp ∅)).symm
      ⟨PCtx.le_join_left hW, ha.le_W.trans (PCtx.le_join_right hW)⟩
  | .call (sig := sig) _ _ _ hp _ _ _ =>
      have h₁ := PCtx.shape_set_of hp sig.visit
      have h₂ := PCtx.shape_set_of hp sig.sOut
      have hin := PCtx.shape_join h₁.symm
      ⟨(PCtx.le_join_left h₁.symm).trans (PCtx.le_join_left (hin.trans h₂.symm)),
        PCtx.le_join_right (hin.trans h₂.symm)⟩
  | .async hp _ _ _ _ _ _ _ _ _ =>
      have h := PCtx.shape_set_of hp _
      ⟨PCtx.le_join_left h.symm, PCtx.le_join_right h.symm⟩
  | .await (th := th) _ hp _ hfb _ _ _ =>
      have h := PCtx.shape_set_of hp th.sOut
      have hin := PCtx.shape_join h.symm
      have ⟨_, bf⟩ := hfb.le_W
      have hW : _ := hin.trans hfb.shape_eq.2.symm
      ⟨(PCtx.le_join_left h.symm).trans (PCtx.le_join_left hW),
        PCtx.join_le_join (PCtx.le_join_right h.symm) bf (h.trans hfb.shape_eq.1.symm)⟩

/-- Arms version of `TypedA.le_W`: the joined output is below the joined visited context. -/
theorem ArmsTypedA.le_W {fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F} :
    ArmsTypedA P M Ψ fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F → Δ'.Le W
  | .last _ hc _ => hc.le_W.2
  | .cons _ hc ha _ =>
      PCtx.join_le_join hc.le_W.2 ha.le_W
        ((hc.shape_eq.1.trans (PCtx.shape_set_set _ _ _ _ ∅)).trans ha.shape_eq.1.symm)
  | .skip _ ha => ha.le_W

end

/-! ### Closure under hardware steps -/

/-- Every state set in `Δ` is closed under hardware steps. -/
def PCtx.HWClosed (P : Platform K St) (Δ : PCtx K St) : Prop :=
  ∀ x k S, Δ x = .live k S → P.hwClose k S = S

/-- Every pending thread's exit states are closed under hardware steps. -/
def ThreadCtx.SOutClosed {R : Type} (P : Platform K St) (Θ : ThreadCtx K St R) : Prop :=
  ∀ t th, Θ t = some th → P.hwClose th.k th.sOut = th.sOut

/-- Every signature's output states are closed under hardware steps (T-FunDecl, option A). -/
def SigsClosedA (P : Platform K St) (Ψ : SigCtxA K St R) : Prop :=
  ∀ g sig, Ψ g = some sig → P.hwClose sig.pKind sig.sOut = sig.sOut

omit [DecidableEq K] [CommSemiring R] [LinearOrder R] [OrderBot R] [IsOrderedRing R] in
/-- Setting a handle to a closed set keeps a context closed. -/
theorem PCtx.HWClosed.set {Δ : PCtx K St} (h : Δ.HWClosed P) {p : Var} {k : K} {S : Finset St}
    (hS : P.hwClose k S = S) : (Δ.set p k S).HWClosed P := by
  intro x k' S' hx
  rw [PCtx.set_apply] at hx
  split_ifs at hx
  · cases hx; exact hS
  · exact h x k' S' hx

omit [CommSemiring R] [LinearOrder R] [OrderBot R] [IsOrderedRing R] in
/-- Joins of closed contexts are closed (`hwClose` distributes over unions). -/
theorem PCtx.HWClosed.join {Δ₁ Δ₂ : PCtx K St} (h₁ : Δ₁.HWClosed P) (h₂ : Δ₂.HWClosed P) :
    (Δ₁.join Δ₂).HWClosed P := by
  intro x k S hx
  rw [PCtx.join_apply] at hx
  rcases e₁ : Δ₁ x with _ | ⟨k₁, S₁⟩ <;> rcases e₂ : Δ₂ x with _ | ⟨k₂, S₂⟩ <;>
    rw [e₁, e₂] at hx <;> simp only [PEntry.join, reduceCtorEq] at hx
  split_ifs at hx with hk
  · cases hx
    subst hk
    rw [Platform.hwClose_union, h₁ x _ _ e₁, h₂ x _ _ e₂]

namespace ThreadCtx

omit [CommSemiring R] [LinearOrder R] [OrderBot R] [IsOrderedRing R] in
/-- Observing changes only windows. -/
theorem SOutClosed.observe {Θ : ThreadCtx K St R} (h : Θ.SOutClosed P) (Δ : PCtx K St) :
    (Θ.observe Δ).SOutClosed P := by
  intro t th ht
  simp only [ThreadCtx.observe, Option.map_eq_some_iff] at ht
  obtain ⟨th₀, h₀, rfl⟩ := ht
  exact h t th₀ h₀

omit [DecidableEq K] [CommSemiring R] [LinearOrder R] [OrderBot R] [IsOrderedRing R] in
/-- Removing a thread. -/
theorem SOutClosed.erase {Θ : ThreadCtx K St R} (h : Θ.SOutClosed P) (t₀ : Var) :
    (Θ.erase t₀).SOutClosed P := by
  intro t th ht
  unfold ThreadCtx.erase at ht
  by_cases e : t = t₀
  · subst e; simp at ht
  · rw [Function.update_of_ne e] at ht; exact h t th ht

omit [CommSemiring R] [LinearOrder R] [OrderBot R] [IsOrderedRing R] in
/-- A join keeps the left thread types. -/
theorem SOutClosed.join {Θ₁ : ThreadCtx K St R} (h : Θ₁.SOutClosed P) (Θ₂ : ThreadCtx K St R) :
    (Θ₁.join Θ₂).SOutClosed P := by
  intro t th ht
  simp only [ThreadCtx.join] at ht
  split at ht
  · rename_i a b ha hb
    cases ht
    exact h t a ha
  · cases ht

omit [DecidableEq K] [CommSemiring R] [LinearOrder R] [OrderBot R] [IsOrderedRing R] in
/-- Adding a thread with closed exit states. -/
theorem SOutClosed.update {Θ : ThreadCtx K St R} (h : Θ.SOutClosed P) (t₀ : Var)
    (th₀ : ThreadTy K St R) (h₀ : P.hwClose th₀.k th₀.sOut = th₀.sOut) :
    ThreadCtx.SOutClosed P (Function.update Θ t₀ (some th₀)) := by
  intro t th ht
  by_cases e : t = t₀
  · subst e; simp only [Function.update_self, Option.some.injEq] at ht; subst ht; exact h₀
  · rw [Function.update_of_ne e] at ht; exact h t th ht

end ThreadCtx

set_option linter.unusedSectionVars false in
mutual

/-- **Typing keeps contexts closed under hardware steps**, given closed signature outputs
(T-FunDecl, option A) and closed exit states of pending threads.  Every rule produces closed
sets: stable singletons, `hwClose {st}` (idempotent), `match` narrowing to `hwClose {st}`,
unions at joins, and the closed `sOut` of calls and awaits.  So an async body (typed from
closed transient states) and every function it calls (typed from closed `sIn`) only ever
describe its captured peripheral by closed sets, which hardware steps cannot leave. -/
theorem TypedA.hwClosed (hP : P.WF) (hΨ : SigsClosedA P Ψ) {fz Γ Δ Θ c Γ' Δ' Θ' W Q F} :
    TypedA P M Ψ fz Γ Δ Θ c Γ' Δ' Θ' W Q F → Δ.HWClosed P → Θ.SOutClosed P →
    Δ'.HWClosed P ∧ Θ'.SOutClosed P
  | .skip, hΔ, hΘ => ⟨hΔ, hΘ⟩
  | .assign _ _, hΔ, hΘ => ⟨hΔ, hΘ⟩
  | .ite _ h₁ h₂ _, hΔ, hΘ =>
      have ⟨a₁, b₁⟩ := h₁.hwClosed hP hΨ hΔ hΘ
      have ⟨a₂, _⟩ := h₂.hwClosed hP hΨ hΔ hΘ
      ⟨a₁.join a₂, b₁.join _⟩
  | .transition _ _ hst _, hΔ, hΘ =>
      ⟨hΔ.set (hP.hwClose_of_stable fun s hs => by
        rw [Finset.mem_singleton] at hs; subst hs; exact hst), hΘ.observe _⟩
  | .transitionU _ _ _ _, hΔ, hΘ => ⟨hΔ.set (hP.hwClose_idem _ _), hΘ.observe _⟩
  | .downgrade _ _ hst _, hΔ, hΘ =>
      ⟨hΔ.set (hP.hwClose_of_stable fun s hs => by
        rw [Finset.mem_singleton] at hs; subst hs; exact hst), hΘ.observe _⟩
  | .clock _ _ _, hΔ, hΘ => ⟨hΔ, hΘ⟩
  | .seq h₁ h₂, hΔ, hΘ =>
      have ⟨a₁, b₁⟩ := h₁.hwClosed hP hΨ hΔ hΘ
      h₂.hwClosed hP hΨ a₁ b₁
  | .matchSt _ _ _ ha, hΔ, hΘ => ha.hwClosed hP hΨ hΔ hΘ
  | .call hg _ _ _ _ _ _, hΔ, hΘ => ⟨hΔ.set (hΨ _ _ hg), (hΘ.observe _).observe _⟩
  | .async _ _ _ _ _ _ _ hstab _ _, hΔ, hΘ =>
      ⟨hΔ.set (hP.hwClose_idem _ _), (hΘ.observe _).update _ _ (hP.hwClose_of_stable hstab)⟩
  | .await ht _ _ hfb _ _ _, hΔ, hΘ =>
      have ⟨af, bf⟩ := hfb.hwClosed hP hΨ hΔ (hΘ.erase _)
      ⟨(hΔ.set (hΘ _ _ ht)).join af, (((hΘ.erase _).observe _)).join _⟩

/-- Arms version of `TypedA.hwClosed`: each arm runs with `p` narrowed to the closed
`hwClose {st}`. -/
theorem ArmsTypedA.hwClosed (hP : P.WF) (hΨ : SigsClosedA P Ψ)
    {fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F} :
    ArmsTypedA P M Ψ fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F → Δ.HWClosed P → Θ.SOutClosed P →
    Δ'.HWClosed P ∧ Θ'.SOutClosed P
  | .last _ hc _, hΔ, hΘ => hc.hwClosed hP hΨ (hΔ.set (hP.hwClose_idem _ _)) (hΘ.observe _)
  | .cons _ hc ha _, hΔ, hΘ =>
      have ⟨a₁, b₁⟩ := hc.hwClosed hP hΨ (hΔ.set (hP.hwClose_idem _ _)) (hΘ.observe _)
      have ⟨a₂, _⟩ := ha.hwClosed hP hΨ hΔ hΘ
      ⟨a₁.join a₂, b₁.join _⟩
  | .skip _ ha, hΔ, hΘ => ha.hwClosed hP hΨ hΔ hΘ

end

/-! ### Window cover -/

/-- **Window cover**: the current context, without a thread's own device, is below that
pending thread's window.  So while the thread runs, its spawner's other peripherals are in
states the window accounts for. -/
def ThreadCtx.WinCover {R : Type} (Θ : ThreadCtx K St R) (Δ : PCtx K St) : Prop :=
  ∀ t th, Θ t = some th → (Δ.erase th.p).Le (th.win.erase th.p)

namespace ThreadCtx

omit [CommSemiring R] [LinearOrder R] [OrderBot R] [IsOrderedRing R] in
/-- After observing a context, the windows cover it. -/
theorem WinCover.observe_self {Θ : ThreadCtx K St R} {Δ : PCtx K St}
    (hw : Θ.WinShape Δ.shape) : (Θ.observe Δ).WinCover Δ := by
  intro t th ht
  simp only [ThreadCtx.observe, Option.map_eq_some_iff] at ht
  obtain ⟨th₀, h₀, rfl⟩ := ht
  show (Δ.erase th₀.p).Le ((th₀.win.join Δ).erase th₀.p)
  rw [PCtx.erase_join]
  exact PCtx.le_join_right (PCtx.shape_erase_congr (hw t th₀ h₀) _)

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] [IsOrderedRing R] in
/-- Removing a thread keeps the cover of the others. -/
theorem WinCover.erase {Θ : ThreadCtx K St R} {Δ : PCtx K St} (h : Θ.WinCover Δ) (t₀ : Var) :
    (Θ.erase t₀).WinCover Δ := by
  intro t th ht
  unfold ThreadCtx.erase at ht
  by_cases e : t = t₀
  · subst e; simp at ht
  · rw [Function.update_of_ne e] at ht; exact h t th ht

omit [CommSemiring R] [LinearOrder R] [OrderBot R] [IsOrderedRing R] in
/-- Joined windows cover joined contexts. -/
theorem WinCover.join {Θ₁ Θ₂ : ThreadCtx K St R} {Δ₁ Δ₂ : PCtx K St} (h₁ : Θ₁.WinCover Δ₁)
    (h₂ : Θ₂.WinCover Δ₂) (hs : Θ₁.SameThreads Θ₂) (hΔ : Δ₁.shape = Δ₂.shape) :
    (Θ₁.join Θ₂).WinCover (Δ₁.join Δ₂) := by
  intro t th ht
  simp only [ThreadCtx.join] at ht
  split at ht
  · rename_i a b ha hb
    cases ht
    obtain ⟨hp, -⟩ := (show a.Same b by
      rcases hs t with ⟨e, _⟩ | ⟨a', b', e₁, e₂, hab⟩
      · rw [ha] at e; cases e
      · rw [ha] at e₁; rw [hb] at e₂; cases e₁; cases e₂; exact hab)
    show ((Δ₁.join Δ₂).erase a.p).Le ((a.win.join b.win).erase a.p)
    rw [PCtx.erase_join, PCtx.erase_join]
    have h₂' := h₂ t b hb
    rw [← hp] at h₂'
    exact PCtx.join_le_join (h₁ t a ha) h₂' (PCtx.shape_erase_congr hΔ _)
  · cases ht

end ThreadCtx

omit [CommSemiring R] [LinearOrder R] [OrderBot R] [IsOrderedRing R] in
/-- After spawning, the new thread's window (the current context) covers the current context,
and the observed windows of the other threads do too. -/
theorem ThreadCtx.WinCover.spawn {Θ : ThreadCtx K St R} {Δ : PCtx K St}
    (hw : Θ.WinShape Δ.shape) (tid : Var) (th : ThreadTy K St R) (hwin : th.win = Δ) :
    ThreadCtx.WinCover (Function.update (Θ.observe Δ) tid (some th)) Δ := by
  intro t th' ht
  by_cases e : t = tid
  · subst e
    simp only [Function.update_self, Option.some.injEq] at ht
    subst ht; rw [hwin]; exact PCtx.Le.refl _
  · rw [Function.update_of_ne e] at ht
    exact ThreadCtx.WinCover.observe_self hw t th' ht

set_option linter.unusedSectionVars false in
mutual

/-- **Typing preserves window cover**: if the input context is covered by every pending thread's
window, so is the output.  Every rule that changes the context observes the new one; a spawn
starts its window at the current context; branches join covered contexts into joined windows. -/
theorem TypedA.winCover {fz Γ Δ Θ c Γ' Δ' Θ' W Q F} :
    TypedA P M Ψ fz Γ Δ Θ c Γ' Δ' Θ' W Q F → Θ.WinShape Δ.shape → Θ.WinCover Δ →
    Θ'.WinCover Δ'
  | .skip, _, h => h
  | .assign _ _, _, h => h
  | .clock _ _ _, _, h => h
  | .ite _ h₁ h₂ hs, hw, h =>
      (h₁.winCover hw h).join (h₂.winCover hw h) hs
        (h₁.shape_eq.1.trans h₂.shape_eq.1.symm)
  | .transition (st := st) hp _ _ _, hw, _ => by
      have e := PCtx.shape_set_of hp {st}
      rw [← e] at hw
      exact ThreadCtx.WinCover.observe_self hw
  | .transitionU (k := k) (st := st) hp _ _ _, hw, _ => by
      have e := PCtx.shape_set_of hp (P.hwClose k {st})
      rw [← e] at hw
      exact ThreadCtx.WinCover.observe_self hw
  | .downgrade (st := st) hp _ _ _, hw, _ => by
      have e := PCtx.shape_set_of hp {st}
      rw [← e] at hw
      exact ThreadCtx.WinCover.observe_self hw
  | .seq h₁ h₂, hw, h => by
      have hw₁ := h₁.winShape hw
      rw [← h₁.shape_eq.1] at hw₁
      exact h₂.winCover hw₁ (h₁.winCover hw h)
  | .matchSt hp _ _ ha, hw, h => by
      have e := PCtx.shape_set_of hp ∅
      rw [← e] at hw
      exact ha.winCover hw
  | .call (sig := sig) _ _ _ hp _ _ _, hw, _ => by
      have e₁ := PCtx.shape_set_of hp sig.visit
      have e₂ := PCtx.shape_set_of hp sig.sOut
      have hw' := hw.observe e₁
      rw [← e₂] at hw'
      exact ThreadCtx.WinCover.observe_self hw'
  | .async (k := k) (Wp := Wp) hp _ _ _ _ _ _ _ _ _, hw, _ => by
      have e := PCtx.shape_set_of hp (P.hwClose k Wp)
      rw [← e] at hw
      exact ThreadCtx.WinCover.spawn hw _ _ rfl
  | .await (tid := tid) (th := th) _ hp _ hfb hs _ _, hw, h => by
      have e := PCtx.shape_set_of hp th.sOut
      have hwe := hw.erase tid
      have hf := hfb.winCover hwe (h.erase tid)
      rw [← e] at hwe
      refine ThreadCtx.WinCover.join (ThreadCtx.WinCover.observe_self hwe) hf ?_
        (e.trans hfb.shape_eq.1.symm)
      intro t
      rcases hs t with ⟨e₁, e₂⟩ | ⟨a, b, e₁, e₂, hab⟩
      · exact Or.inl ⟨by simp [ThreadCtx.observe, e₁], e₂⟩
      · exact Or.inr ⟨{ a with win := a.win.join (Δ.set th.p th.k th.sOut) }, b,
          by simp [ThreadCtx.observe, e₁], e₂, hab⟩

/-- Arms version of `TypedA.winCover`: the arms start from the narrowed context, which the
observed windows cover. -/
theorem ArmsTypedA.winCover {fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F} :
    ArmsTypedA P M Ψ fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F →
    Θ.WinShape (Δ.set p k ∅).shape → Θ'.WinCover Δ'
  | .last (st := st) _ hc _, hw => by
      have e := PCtx.shape_set_set Δ p k (P.hwClose k {st}) ∅
      rw [← e] at hw
      exact hc.winCover (hw.observe rfl) (ThreadCtx.WinCover.observe_self hw)
  | .cons (st := st) _ hc ha hs, hw => by
      have e := PCtx.shape_set_set Δ p k (P.hwClose k {st}) ∅
      have hw' := hw
      rw [← e] at hw'
      exact (hc.winCover (hw'.observe rfl) (ThreadCtx.WinCover.observe_self hw')).join
        (ha.winCover hw) hs
        ((hc.shape_eq.1.trans (PCtx.shape_set_set _ _ _ _ ∅)).trans ha.shape_eq.1.symm)
  | .skip _ ha, hw => ha.winCover hw

end

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R]
  [IsOrderedRing R] in
/-- No threads, nothing to cover. -/
theorem ThreadCtx.WinCover.empty {Δ : PCtx K St} :
    (ThreadCtx.empty : ThreadCtx K St R).WinCover Δ :=
  fun _ _ h => by cases h
