import Heliod.AsyncProgram

/-!
# Async slack: where the bound exceeds a run's cost

Soundness (`Program.MRun.soundnessA`) says a run costs at most `Q K₀ 0`.  This file splits the
gap: the bound is the run's cost, plus a list of **slack items** released along the run, plus a
residual `r`:

  `Q K₀ 0 = q + Σ items + r`.

Each item has a kind and an amount that is a typed quantity minus an actual one, at the step that
released it (`ASlack.Spec`, `AsyncConfig.lean`).

**Schedule kinds** (B2), released by the `await` cases:
* `wait` — unused waiting allowance of `main`'s waiting frame at its typed per-tick rate
  (`WaitRate`): while a thread runs above the frame, by a waiting tick's rounding, and in full
  at the join;
* `fallback` — the summary of a fallback that never ran (`FallbackSum`);
* `abandon` — the reservation of a thread abandoned at a timeout (`AbandonSum`).

**Charge kinds** (B3), released by the charge of every step that charges: local commands,
calls, returns, spawns and waiting ticks (`LSpec` / `LFact`, per handle via
`PeriphsOK.bg_split`):
* `state` — a visible handle charged at the worst state of its typed set `T`, its device in
  `s ∈ T`: `K·(maxBg T − bg s)`;
* `envelope` — the same for a handle a pending thread has captured (`T` is the envelope `V`);
* `transition` — the moving device's worst-case transition against the actual one;
* `spawn` — the captured device's worst-case spawn cost against the actual one;
* `ambient` / `window` — the layer's typed ambient bound against the actual background of
  everything it cannot see, in a non-thread / thread layer (a thread's bound is `b + amb`).

**Structural kinds** (B3), dropped from the potential by a step:
* `branch` — at an `if`, the more expensive untaken branch: `max(Q₁, Q₂) − Q_taken`;
* `arm` — at a `match`, the joined arms' summary minus the arm taken;
* `clock` — the rest of the program charged at a typed exit-clock bound above the actual clock
  (after a branch or match, when a callee's exit bound tightens, after a join or timeout, and on
  a caller's continuation when an awaiting or spawning callee's exit bound tightens).

Items are specified at the head activation of a segment of the configuration before or after the
step (`HeadSpec`); the `wait` item of `awaitStart` and a callee's continuation items refer to the
activation after the step.

Attribution differs from the sync `SlackRun` in one respect: ambient slack is released per step
(the device-level gap at that moment), not once per call.

**The residual `r`** is the final potential plus whatever the remaining `≤` steps of the proof
leave.  Those steps drop only contributions that typing makes zero (a finished thread's empty
stack, a joined thread's `done` contribution) or keep the potential unchanged (scheduling,
hardware steps), and a final configuration's potential is `0` (its only stack is `main`'s, empty,
with no pending thread).  So `r` is expected to be `0`; proving `Q K₀ 0 = q + Σ items` exactly
would need every step lemma restated as an equality, which is not done.

## Results

* `CfgTyped.stepsS` — along any run from a typed configuration, cost plus released items plus
  final potential is at most the initial potential; each item is specified at the step of the
  run that released it.
* `Program.slack_decompositionA` — for a whole program run: `Q K₀ 0 = q + Σ items + r`, each
  item specified at the step of the run that released it.
-/

set_option linter.unusedSectionVars false

variable {K St R : Type} [DecidableEq K] [DecidableEq St]
variable [CommSemiring R] [LinearOrder R] [OrderBot R]
variable [IsOrderedRing R] [CanonicallyOrderedAdd R] [Sub R] [OrderedSub R]
variable {P : Platform K St} {M : CostModel K St R}

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
    obtain ⟨Φ₁, L₁, h₁, hL₁, hle₁, _⟩ := hc.mstepS hM hΨ hP hΨc hΨd hs
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

/-- **Async slack decomposition.**  For a program well typed under `TypedA`, run to
completion on the machine from clock `K₀` (any schedule, any hardware behaviour), the bound is
the run's cost, plus the async slack items released along the run, plus a residual:
`Q K₀ 0 = q + Σ items + r`.  Each item is a typed quantity at the step of the run that released
it (schedule kinds `wait`, `fallback`, `abandon`; charge kinds `state`, `envelope`, `transition`,
`ambient`, `window`; structural kinds `branch`, `arm`, `clock`).  The residual is the final
potential plus the few steps not yet itemized (see the module doc). -/
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
