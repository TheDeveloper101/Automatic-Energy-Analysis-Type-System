import Heliod.AsyncTyping
import Heliod.Soundness

/-!
# Soundness of the async type system — step 1: structural lemmas for `TypedA`

Ports of the synchronous typing lemmas the soundness proof relies on:

* `TypedA.shape_eq` — typing never creates, destroys or re-kinds a handle; the output context
  and the visited context `W` have the shape of the input context.
* `TypedA.mono` — derived summaries are monotone in the clock and the ambient background.  The
  spawn charges the body's summary, which is monotone by the same lemma applied to the body.

These are the inputs to the potential-function argument (configuration typing and the per-step
potential inequality), which comes next.
-/

variable {K St R : Type} [DecidableEq K] [DecidableEq St]
variable [CommSemiring R] [LinearOrder R] [OrderBot R]
variable {P : Platform K St} {M : CostModel K St R} {Ψ : SigCtxA K St R}

/-! ### Shape preservation -/

mutual

/-- **Typing never changes the shape of `Δ`**, and everything a command visits has that shape
too.  As in the synchronous system, this makes every join after a branch a pointwise union. -/
theorem TypedA.shape_eq {fz Γ Δ Θ c Γ' Δ' Θ' W Q F} :
    TypedA P M Ψ fz Γ Δ Θ c Γ' Δ' Θ' W Q F → Δ'.shape = Δ.shape ∧ W.shape = Δ.shape
  | .skip => ⟨rfl, rfl⟩
  | .assign _ _ => ⟨rfl, rfl⟩
  | .ite _ h₁ h₂ _ =>
      have ⟨h₁Δ, h₁W⟩ := h₁.shape_eq
      have ⟨h₂Δ, h₂W⟩ := h₂.shape_eq
      ⟨(PCtx.shape_join (h₁Δ.trans h₂Δ.symm)).trans h₁Δ,
        (PCtx.shape_join (h₁W.trans h₂W.symm)).trans h₁W⟩
  | .transition (st := st) hp _ _ _ =>
      ⟨PCtx.shape_set_of hp {st}, PCtx.shape_join (PCtx.shape_set_of hp {st}).symm⟩
  | .transitionU (k := k) (st := st) hp _ _ _ =>
      ⟨PCtx.shape_set_of hp (P.hwClose k {st}),
        PCtx.shape_join (PCtx.shape_set_of hp (P.hwClose k {st})).symm⟩
  | .downgrade (st := st) hp _ _ _ =>
      ⟨PCtx.shape_set_of hp {st}, PCtx.shape_join (PCtx.shape_set_of hp {st}).symm⟩
  | .clock _ _ _ => ⟨rfl, rfl⟩
  | .seq h₁ h₂ =>
      have ⟨h₁Δ, h₁W⟩ := h₁.shape_eq
      have ⟨h₂Δ, h₂W⟩ := h₂.shape_eq
      ⟨h₂Δ.trans h₁Δ, (PCtx.shape_join (h₁W.trans (h₂W.trans h₁Δ).symm)).trans h₁W⟩
  | .matchSt hp _ _ ha =>
      have ⟨hΔ, hW⟩ := ha.shape_eq
      have h₀ := PCtx.shape_set_of hp ∅
      ⟨hΔ.trans h₀, PCtx.shape_join (hW.trans h₀).symm⟩
  | .call (sig := sig) _ _ _ hp _ _ _ =>
      have h₁ := PCtx.shape_set_of hp sig.visit
      have h₂ := PCtx.shape_set_of hp sig.sOut
      have hin := PCtx.shape_join h₁.symm
      ⟨h₂, (PCtx.shape_join (hin.trans h₂.symm)).trans hin⟩
  | .async (Wp := Wp) (k := k) hp _ _ _ _ _ _ _ _ _ =>
      ⟨PCtx.shape_set_of hp (P.hwClose k Wp),
        PCtx.shape_join (PCtx.shape_set_of hp (P.hwClose k Wp)).symm⟩
  | .await (th := th) _ hp _ hfb _ _ _ =>
      have ⟨hfΔ, hfW⟩ := hfb.shape_eq
      have h := PCtx.shape_set_of hp th.sOut
      have hin := PCtx.shape_join h.symm
      ⟨(PCtx.shape_join (h.trans hfΔ.symm)).trans h,
        (PCtx.shape_join (hin.trans hfW.symm)).trans hin⟩

/-- Arms version of `TypedA.shape_eq`. -/
theorem ArmsTypedA.shape_eq {fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F} :
    ArmsTypedA P M Ψ fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F →
    Δ'.shape = (Δ.set p k ∅).shape ∧ W.shape = (Δ.set p k ∅).shape
  | .last _ h _ => by
      obtain ⟨hΔ, hW⟩ := h.shape_eq
      exact ⟨hΔ.trans (PCtx.shape_set_set _ _ _ _ _), hW.trans (PCtx.shape_set_set _ _ _ _ _)⟩
  | .cons _ h ha _ => by
      obtain ⟨hΔ, hW⟩ := h.shape_eq
      obtain ⟨haΔ, haW⟩ := ha.shape_eq
      have h₁ := hΔ.trans (PCtx.shape_set_set _ _ _ _ ∅)
      have h₂ := hW.trans (PCtx.shape_set_set _ _ _ _ ∅)
      exact ⟨by rw [PCtx.shape_join (h₁.trans haΔ.symm), h₁],
        by rw [PCtx.shape_join (h₂.trans haW.symm), h₂]⟩
  | .skip _ ha => ha.shape_eq

end

/-! ### Monotonicity -/

variable [IsOrderedRing R] [CanonicallyOrderedAdd R]

omit [DecidableEq K] [DecidableEq St] [OrderBot R] in
/-- A charge `f * x` grows with `f` and `x` (all costs are `≥ 0`). -/
private theorem mul_mono₂ {f f' x x' : R} (hf : f ≤ f') (hx : x ≤ x') : f * x ≤ f' * x' :=
  mul_le_mul hf hx zero_le zero_le

-- `ArmsTypedA.mono` uses the ordered-ring instances only through `TypedA.mono`.
set_option linter.unusedSectionVars false in
mutual

/-- **Monotonicity of summaries (async).**  If every signature in scope has monotone
summaries, so does every derived summary.  The spawn charges the body's summary, which is
monotone by this lemma applied to the body. -/
theorem TypedA.mono (hM : M.WF) (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk)
    {fz Γ Δ Θ c Γ' Δ' Θ' W Q F} :
    TypedA P M Ψ fz Γ Δ Θ c Γ' Δ' Θ' W Q F → SummaryMono Q F
  | .skip => ⟨monotone_id, fun _ _ _ _ _ _ => le_rfl⟩
  | .assign _ _ => ⟨monotone_id, fun _ _ _ _ hf hb => mul_mono₂ hf (add_le_add le_rfl hb)⟩
  | .ite _ h₁ h₂ _ =>
      have ⟨hF₁, hQ₁⟩ := h₁.mono hM hΨ
      have ⟨hF₂, hQ₂⟩ := h₂.mono hM hΨ
      ⟨fun _ _ hf => max_le_max (hF₁ hf) (hF₂ hf), fun _ _ _ _ hf hb =>
        add_le_add (max_le_max (hQ₁ _ _ _ _ hf hb) (hQ₂ _ _ _ _ hf hb))
          (mul_mono₂ hf (add_le_add le_rfl hb))⟩
  | .transition _ _ _ _ =>
      ⟨monotone_id, fun _ _ _ _ hf hb => mul_mono₂ hf (add_le_add le_rfl hb)⟩
  | .transitionU _ _ _ _ =>
      ⟨monotone_id, fun _ _ _ _ hf hb => mul_mono₂ hf (add_le_add le_rfl hb)⟩
  | .downgrade _ _ _ _ =>
      ⟨monotone_id, fun _ _ _ _ hf hb => mul_mono₂ hf (add_le_add le_rfl hb)⟩
  | .clock _ _ _ =>
      ⟨monotone_const, fun _ _ _ _ hf hb =>
        add_le_add (hM.clockCost_mono_left _ _ _ hf) (mul_mono₂ hf (add_le_add le_rfl hb))⟩
  | .seq h₁ h₂ =>
      have ⟨hF₁, hQ₁⟩ := h₁.mono hM hΨ
      have ⟨hF₂, hQ₂⟩ := h₂.mono hM hΨ
      ⟨hF₂.comp hF₁, fun _ _ _ _ hf hb =>
        add_le_add (hQ₁ _ _ _ _ hf hb) (hQ₂ _ _ _ _ (hF₁ hf) hb)⟩
  | .matchSt _ _ _ ha => ha.mono hM hΨ
  | .call hg _ _ _ _ _ _ =>
      have ⟨hF, hQ⟩ := hΨ _ _ hg
      ⟨hF, fun _ _ _ _ hf hb =>
        add_le_add (mul_mono₂ hf (add_le_add le_rfl hb)) (hQ _ _ _ _ hf (add_le_add hb le_rfl))⟩
  | .async _ _ _ _ _ hb _ _ _ _ =>
      have ⟨_, hQa⟩ := hb.mono hM hΨ
      ⟨monotone_id, fun _ _ _ _ hf hb' =>
        add_le_add (mul_mono₂ hf (add_le_add le_rfl hb'))
          (hQa _ _ _ _ hf (add_le_add hb' le_rfl))⟩
  | .await _ _ _ hfb _ _ _ =>
      have ⟨hFf, hQf⟩ := hfb.mono hM hΨ
      ⟨fun _ _ hf => max_le_max (hFf hf) hf, fun _ _ _ _ hf hb =>
        add_le_add (mul_mono₂ (add_le_add le_rfl hf) (add_le_add le_rfl hb))
          (hQf _ _ _ _ hf hb)⟩

/-- Arms version of `TypedA.mono`. -/
theorem ArmsTypedA.mono (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk)
    {fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F} :
    ArmsTypedA P M Ψ fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F → SummaryMono Q F
  | .last _ h _ =>
      have ⟨hF, hQ⟩ := h.mono hM hΨ
      ⟨hF, fun _ _ _ _ hf hb =>
        add_le_add (hQ _ _ _ _ hf hb) (mul_mono₂ hf (add_le_add le_rfl hb))⟩
  | .cons _ h ha _ =>
      have ⟨hF₁, hQ₁⟩ := h.mono hM hΨ
      have ⟨hF₂, hQ₂⟩ := ha.mono hM hΨ
      ⟨fun _ _ hf => max_le_max (hF₁ hf) (hF₂ hf), fun _ _ _ _ hf hb =>
        max_le_max (add_le_add (hQ₁ _ _ _ _ hf hb) (mul_mono₂ hf (add_le_add le_rfl hb)))
          (hQ₂ _ _ _ _ hf hb)⟩
  | .skip _ ha => ha.mono hM hΨ

end
