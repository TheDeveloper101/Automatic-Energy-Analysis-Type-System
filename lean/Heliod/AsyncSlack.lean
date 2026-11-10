import Heliod.AsyncProgram

/-!
# Async slack (B1 + B2): what the schedule leaves unused

Soundness (`Program.MRun.soundnessA`) says a run costs at most `Q K₀ 0`.  This file splits the
gap: the bound is the run's cost, plus a list of **async slack items** released along the run,
plus a residual `r`:

  `Q K₀ 0 = q + Σ items + r`.

Each item has a kind and an amount that is a typed quantity of a configuration typing at the
step that released it (`ASlack.Spec`, `AsyncConfig.lean`):

* `wait` — unused waiting allowance of `main`'s waiting frame, priced at the frame's typed
  per-tick rate `cost(Δ) + b` (`WaitRate`): released while a thread runs above the frame (the
  time counts against the budget though nobody waits), by the rounding of a waiting tick, and
  in full when the awaited thread is joined;
* `fallback` — the summary of a fallback that never ran, because the thread finished
  (`FallbackSum`);
* `abandon` — the reservation of a thread abandoned at a timeout: its body's summary if it
  never ran, its stack's remaining potential if it was running (`AbandonSum`).

These are the schedule-dependent parts of T-Await's charge `Q_a + (n + f)·w + Q_fb`.  Every
await ends with a join or a timeout, so every await releases a `fallback` or an `abandon` item
(and, unless every tick of the budget was spent waiting, `wait` items): the sum is never tight.

The residual `r` is the slack of the sync kinds (state, branch, arm, clock, ambient, signature,
here also the captured device's envelope and a thread's window ambient), plus the final
potential; classifying it is future work (B3).

## Results

* `CfgTyped.stepsS` — along any run from a typed configuration, cost plus released items plus
  final potential is at most the initial potential; each item is specified at the step of the
  run that released it.
* `Program.slack_decompositionA` — for a whole program run: `Q K₀ 0 = q + Σ items + r`.
-/

set_option linter.unusedSectionVars false

variable {K St R : Type} [DecidableEq K] [DecidableEq St]
variable [CommSemiring R] [LinearOrder R] [OrderBot R]
variable [IsOrderedRing R] [CanonicallyOrderedAdd R] [Sub R] [OrderedSub R]
variable {P : Platform K St} {M : CostModel K St R}

/-- Total of a concatenation of slack lists. -/
theorem ASlack.total_append (L₁ L₂ : List (ASlack R)) :
    ASlack.total (L₁ ++ L₂) = ASlack.total L₁ + ASlack.total L₂ := by
  simp only [ASlack.total, List.map_append, List.sum_append]

/-- **Runs release slack**: along any run from a typed configuration with potential `Φ`, the
cost, plus the async slack items released by its steps, plus the final potential, is at most
`Φ`.  Each item is specified (`ASlack.Spec`) at the step of the run that released it. -/
theorem CfgTyped.stepsS {Ψ : SigCtxA K St R} (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk) {Ψd : FCtx K St R}
    (hP : P.WF) (hΨc : SigsClosedA P Ψ) (hΨd : SigsDerivedA P M Ψd Ψ)
    {Am : Multiset (K × St)} {c : Config K St R} {q : R} {c' : Config K St R}
    (h : Steps P M Ψd Am c q c') :
    ∀ {Φ : R}, CfgTyped P M Ψ Am c Φ → ∃ (Φ' : R) (L : List (ASlack R)),
      CfgTyped P M Ψ Am c' Φ' ∧
      (∀ i ∈ L, ∃ c₁ c₂ q₀ q₁, Steps P M Ψd Am c q₀ c₁ ∧ MStep P M Ψd Am c₁ q₁ c₂ ∧
        i.Spec P M Ψ Am c₁ c₂) ∧
      q + ASlack.total L + Φ' ≤ Φ := by
  induction h with
  | refl =>
    intro Φ hc
    exact ⟨Φ, [], hc, fun _ h => (by cases h), by simp [ASlack.total]⟩
  | @step c₀ q₀ c₁ q' c₂ hs _ ih =>
    intro Φ hc
    obtain ⟨Φ₁, L₁, h₁, hL₁, hle₁⟩ := hc.mstepS hM hΨ hP hΨc hΨd hs
    obtain ⟨Φ', L₂, h', hL₂, hle'⟩ := ih h₁
    refine ⟨Φ', L₁ ++ L₂, h', ?_, ?_⟩
    · intro i hi
      rcases List.mem_append.1 hi with hi | hi
      · exact ⟨c₀, c₁, 0, q₀, .refl, hs, hL₁ i hi⟩
      · obtain ⟨c₃, c₄, q₃, q₄, h₃, h₄, hsp⟩ := hL₂ i hi
        exact ⟨c₃, c₄, q₀ + q₃, q₄, .step hs h₃, h₄, hsp⟩
    · rw [ASlack.total_append]
      calc q₀ + q' + (ASlack.total L₁ + ASlack.total L₂) + Φ'
          = q₀ + ASlack.total L₁ + (q' + ASlack.total L₂ + Φ') := by ring
        _ ≤ q₀ + ASlack.total L₁ + Φ₁ := add_le_add le_rfl hle'
        _ ≤ Φ := hle₁

/-- **Async slack decomposition (B1 + B2).**  For a program well typed under `TypedA`, run to
completion on the machine from clock `K₀` (any schedule, any hardware behaviour), the bound is
the run's cost, plus the async slack items released along the run, plus a residual:
`Q K₀ 0 = q + Σ items + r`.  Each item is a typed quantity at the step of the run that released
it: unused waiting allowance at the frame's typed rate (`wait`), an unrun fallback's summary
(`fallback`), or an abandoned thread's reservation (`abandon`).  The residual is the slack of
the sync kinds plus the final potential. -/
theorem Program.slack_decompositionA (hM : M.WF) (hP : P.WF) {prog : Program K St R}
    {Ψ : SigCtxA K St R} {Γ' : TCtx K} {Δ' W : PCtx K St} {Q : R → R → R} {F : R → R}
    (ht : prog.TypedA P M Ψ Γ' Δ' W Q F) {K₀ q : R} {c : Config K St R}
    (h : prog.MRun P M K₀ c q) :
    ∃ (L : List (ASlack R)) (r : R), Q K₀ 0 = q + ASlack.total L + r ∧
      ∀ i ∈ L, ∃ c₁ c₂ q₀ q₁, Steps P M prog.fctx 0 (prog.initConfig K₀) q₀ c₁ ∧
        MStep P M prog.fctx 0 c₁ q₁ c₂ ∧ i.Spec P M Ψ 0 c₁ c₂ := by
  have hΨd := Program.sigsDerivedA ht
  obtain ⟨Φ', L, _, hL, hle⟩ := CfgTyped.stepsS hM (Program.sigsMonoA hM ht) hP hΨd.closed hΨd
    h.1 (Program.initCfgTyped ht K₀)
  rw [add_zero] at hle
  obtain ⟨r, hr⟩ := exists_add_of_le (le_trans le_self_add hle)
  exact ⟨L, r, hr, hL⟩
