import Heliod.AsyncProgram

/-!
# Async slack: where the bound exceeds a run's cost

Soundness (`Program.MRun.soundnessA`) says a run costs at most `Q K₀ 0`.  This file splits the
gap exactly: the bound is the run's cost plus a list of **slack items** released along the run:

  `Q K₀ 0 = q + Σ items`.

Each item has a kind and an amount, specified at the step that released it (`ASlack.Spec`,
`AsyncConfig.lean`).  For the charge kinds the amount is a typed charge minus the actual one;
`fallback` and `abandon` are typed quantities; the specifications of `wait` (a multiple of the
frame's typed rate) and `clock` (`g f₂ − g f₁` for some monotone `g` and `f₁ ≤ f₂`) are weak.

**Schedule kinds** (B2), released by the `await` cases:
* `wait` — unused waiting allowance of `main`'s waiting frame at its typed per-tick rate
  (`WaitRate`): at `awaitStart` when `n = 0`, while a thread runs above the frame, by a waiting
  tick's rounding, and in full at the join;
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

**Exactness.**  Every step lemma of the soundness proof is an equality: a step's cost plus the
items it releases is exactly the drop in potential (dropped thread contributions are zero by
typing: a finished stack, a joined `done` thread), and a final configuration has potential `0`
(`CfgTyped.final_zero`).  So the decomposition is exact: `Q K₀ 0 = q + Σ items`.

## Results

* `CfgTyped.stepsS` — along any run from a typed configuration, cost plus released items plus
  final potential *equals* the initial potential; each item is specified at the step of the run
  that released it.
* `CfgTyped.final_zero` — a final configuration has potential `0`.
* `Program.slack_decompositionA` — for a whole program run: `Q K₀ 0 = q + Σ items`, each item
  specified at the step of the run that released it.
-/

set_option linter.unusedSectionVars false

variable {K St R : Type} [DecidableEq K] [DecidableEq St]
variable [CommSemiring R] [LinearOrder R] [OrderBot R]
variable [IsOrderedRing R] [CanonicallyOrderedAdd R] [Sub R] [OrderedSub R]
variable {P : Platform K St} {M : CostModel K St R}

/-- **Runs release slack**: along any run from a typed configuration with potential `Φ`, the
cost, plus the async slack items released by its steps, plus the final potential, equals `Φ`.  Each item is specified (`ASlack.Spec`) at the step of the run that released it. -/
theorem CfgTyped.stepsS {Ψ : SigCtxA K St R} (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk) {Ψd : FCtx K St R}
    (hP : P.WF) (hΨc : SigsClosedA P Ψ) (hΨd : SigsDerivedA P M Ψd Ψ)
    {Am : Multiset (K × St)} {c : Config K St R} {q : R} {c' : Config K St R}
    (h : Steps P M Ψd Am c q c') :
    ∀ {Φ : R}, CfgTyped P M Ψ Am c Φ → ∃ (Φ' : R) (L : List (ASlack R)),
      CfgTyped P M Ψ Am c' Φ' ∧
      (∀ i ∈ L, ∃ c₁ c₂ q₀ q₁, Steps P M Ψd Am c q₀ c₁ ∧ MStep P M Ψd Am c₁ q₁ c₂ ∧
        i.Spec P M Ψ Am c₁ c₂) ∧
      q + ASlack.total L + Φ' = Φ := by
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
        _ = q₀ + ASlack.total L₁ + Φ₁ := by rw [hle']
        _ = Φ := hle₁

/-- **A finished stack's thread view has no pending thread** (its empty control stack's final
thread context is its starting one, which a bottom layer requires to be empty). -/
theorem StackOK.finished_tv {E : Option (DevEnv St)} {Am : Multiset (K × St)} {σ : Mem}
    {H : Var → Option Dev} {T : Var → Option ThreadId} {D Kc Φ X Θ Δ b bb tv Vs}
    (h : StackOK P M Ψ Am E [⟨σ, H, T, [], none⟩] D Kc Φ X Θ Δ b bb tv Vs) : tv.Θ.IsEmpty := by
  cases h with
  | base hct _ hΘf => cases hct; exact hΘf

/-- **A final configuration has potential `0`**: `main`'s stack is finished (summary `0`) and no
thread is pending. -/
theorem CfgTyped.final_zero {Am : Multiset (K × St)} {c : Config K St R} {Φ : R}
    (hc : CfgTyped P M Ψ Am c Φ) (hf : c.Final) : Φ = 0 := by
  obtain ⟨tsegs, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, hsegs, hst, htids, -, -, -, -, -,
    -, -, -, rfl⟩ := hc
  obtain ⟨σ, H, T, hs⟩ := hf
  rw [hs] at hsegs
  cases tsegs with
  | nil =>
    simp only [List.nil_append, List.cons.injEq, Seg.mk.injEq, true_and, and_true] at hsegs
    obtain ⟨rfl, rfl⟩ := hsegs
    have htE : tids = ∅ :=
      Finset.eq_empty_of_forall_notMem fun t ht => (htids t).1 ht (hst.finished_tv t)
    rw [hst.finished_zero, htE, Finset.sum_empty, add_zero]
  | cons s₀ t₀ =>
    simp only [List.cons_append, List.cons.injEq] at hsegs
    obtain ⟨-, h⟩ := hsegs
    cases t₀ <;> simp at h

/-- **Async slack decomposition, exact.**  For a program well typed under `TypedA`, run to
completion on the machine from clock `K₀` (any schedule, any hardware behaviour), the bound is
the run's cost plus the async slack items released along the run:
`Q K₀ 0 = q + Σ items`, with nothing left over.  Each item is a typed quantity at the step of
the run that released it (schedule kinds `wait`, `fallback`, `abandon`; charge kinds `state`,
`envelope`, `transition`, `spawn`, `ambient`, `window`; structural kinds `branch`, `arm`,
`clock`).  Every machine step's cost plus its released items equals the drop in potential, and
a final configuration's potential is `0`. -/
theorem Program.slack_decompositionA (hM : M.WF) (hP : P.WF) {prog : Program K St R}
    {Ψ : SigCtxA K St R} {Γ' : TCtx K} {Δ' W : PCtx K St} {Q : R → R → R} {F : R → R}
    (ht : prog.TypedA P M Ψ Γ' Δ' W Q F) {K₀ q : R} {c : Config K St R}
    (h : prog.MRun P M K₀ c q) :
    ∃ L : List (ASlack R), Q K₀ 0 = q + ASlack.total L ∧
      ∀ i ∈ L, ∃ c₁ c₂ q₀ q₁, Steps P M prog.fctx 0 (prog.initConfig K₀) q₀ c₁ ∧
        MStep P M prog.fctx 0 c₁ q₁ c₂ ∧ i.Spec P M Ψ 0 c₁ c₂ := by
  have hΨd := Program.sigsDerivedA ht
  obtain ⟨Φ', L, hc', hL, hle⟩ := CfgTyped.stepsS hM (Program.sigsMonoA hM ht) hP hΨd.closed hΨd
    h.1 (Program.initCfgTyped ht K₀)
  rw [hc'.final_zero h.2, add_zero, add_zero] at hle
  exact ⟨L, hle.symm, hL⟩
