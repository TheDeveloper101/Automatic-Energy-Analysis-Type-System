import Heliod.AsyncSlack
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Async necessity (B4): which slack is imprecision, which is inherent

`Heliod.AsyncSlack` splits the gap between the bound and a run's cost into items.  The bound must
hold for every schedule and every hardware behaviour, so an item in one run is imprecision only
if no run attains it.  This file proves:

**Part 1 — local necessity of the charge kinds** (the async counterpart of
`Heliod.Necessity`).
* *Attainment* (`LFact.charge_attained`): a `state`, `envelope`, `transition` or `spawn` item
  is zero for a worst state of its typed set — the typed charge is the actual charge of some
  state the typing allows, so no sound analysis knowing only that set can charge less.
* *Zero conditions* (`LFact.charge_zero_of_worst`, `LFact.charge_zero_of_pinned`,
  `LFact.amb_zero_of_tight`): the item vanishes when the device is in a worst state, in
  particular when its typed set is a single state; an `ambient` / `window` item vanishes when
  the layer's typed ambient bound equals the actual background it cannot see.

**Part 2a — every await leaves the body or the fallback unpaid** (`CfgTyped.stepsR`,
`Program.await_gap`).  A waiting frame is removed only by a join or a timeout (`mstepS`'s last
conclusion: any step after which `main` no longer waits released a `fallback` or `abandon`
item), and a final configuration has none (`Config.Final.not_waits`).  So in a complete run,
every await that started releases the fallback's typed summary (joined: the fallback never ran)
or the thread's reservation (timed out: the body never finished), and the run's cost plus that
item stays within the bound.  T-Await's `Q_a + (n + f)·w + Q_fb` pays for both; no schedule
uses both.

**Part 2b — the waiting allowance is rounded up** (for cost domains with additive cancellation,
`[AddLeftReflectLE R]`, as `ℕ`, `ℚ≥0`, `ℝ≥0`) (`waitAllow_tick_exact`, `waitAllow_last`,
`waitAllow_drain_exact`, `waitAllow_drain_last`).  While more than one tick of budget remains, a
waiting tick consumes exactly one tick of the frame's allowance (its `wait` item is `0`); the
tick that exhausts the budget releases the leftover budget `rem ∈ (0, K]` (times the frame's
rate).  So T-Await's `(n + f)·w` is never consumed exactly by waiting: discrete ticks always leave
some of the allowance unused.

**Part 3 — an adversarial schedule attains the waiting charge** (`Steps.waiting`,
`Steps.never_schedule`, `waiting_cost_bounds`; for an Archimedean cost domain and a positive
clock).  The schedule that never runs the awaited thread waits out the budget and times out:
`m` waiting ticks with `rem ≤ m·K ≤ rem + K`, store and clock unchanged, the thread dropped
without having run (its whole body reservation abandoned), and the fallback runs.  With the
devices at the frame's worst states the waiting costs between `rem·w` and `(rem + K)·w`, so
T-Await's waiting charge `(rem + K)·w` is attained up to one tick.  Together with Part 2a: the
timeout branch can (nearly) use the waiting and the fallback, the join branch the body, but no
schedule both — the motivation for a `max` form of T-Await.
-/

set_option linter.unusedSectionVars false

variable {K St R : Type} [DecidableEq K] [DecidableEq St]
variable [CommSemiring R] [LinearOrder R] [OrderBot R]
variable [IsOrderedRing R] [CanonicallyOrderedAdd R] [Sub R] [OrderedSub R]
variable {P : Platform K St} {M : CostModel K St R} {Ψ : SigCtxA K St R}
variable {Am : Multiset (K × St)}

/-! ### Part 1: local necessity of the charge kinds -/

/-- **Attainment of a typed state set's background**: some state of a non-empty set has the
set's worst background. -/
theorem CostModel.maxBg_attained (M : CostModel K St R) (k : K) {T : Finset St}
    (h : T.Nonempty) : ∃ s' ∈ T, M.bgCost k s' = M.maxBg k T := by
  obtain ⟨s', hs', he⟩ := Finset.exists_mem_eq_sup T h (M.bgCost k)
  exact ⟨s', hs', he.symm⟩

/-- Attainment of a worst-case transition cost. -/
theorem CostModel.maxTrans_attained (M : CostModel K St R) (k : K) {T : Finset St} (st : St)
    (h : T.Nonempty) : ∃ s' ∈ T, M.transCost k s' st = M.maxTrans k T st := by
  obtain ⟨s', hs', he⟩ := Finset.exists_mem_eq_sup T h (fun s => M.transCost k s st)
  exact ⟨s', hs', he.symm⟩

/-- Attainment of a worst-case spawn cost. -/
theorem CostModel.maxSpawn_attained (M : CostModel K St R) (k : K) {T : Finset St}
    (h : T.Nonempty) : ∃ s' ∈ T, M.spawnCost k s' = M.maxSpawn k T := by
  obtain ⟨s', hs', he⟩ := Finset.exists_mem_eq_sup T h (M.spawnCost k)
  exact ⟨s', hs', he.symm⟩

/-- **Local attainment of the charge kinds.**  A `state`, `envelope`, `transition` or `spawn`
item charges a handle at the worst state of its typed set `T`, its device being in `s ∈ T`;
some state `s' ∈ T` attains that worst case.  Had the device been in `s'` the item would be
zero, so the typed charge cannot be lowered without excluding a state the typing allows. -/
theorem LFact.charge_attained {cl fz Γ Δ Θ b H D Kc ctl} {i : ASlack R}
    (h : LFact P M Ψ Am cl fz Γ Δ Θ b H D Kc ctl i)
    (hk : i.kind = .state ∨ i.kind = .envelope ∨ i.kind = .transition ∨ i.kind = .spawn) :
    i.amount = 0 ∨ ∃ (k : K) (T : Finset St) (s : St), s ∈ T ∧
      ((∃ s' ∈ T, M.bgCost k s' = M.maxBg k T) ∧ i.amount = Kc * (M.maxBg k T - M.bgCost k s) ∨
       (∃ st, ∃ s' ∈ T, M.transCost k s' st = M.maxTrans k T st) ∨
       (∃ s' ∈ T, M.spawnCost k s' = M.maxSpawn k T)) := by
  obtain ⟨k₀, amt⟩ := i
  simp only at hk
  rcases hk with rfl | rfl | rfl | rfl
  · rcases h with h0 | ⟨_, k, T, s, _, _, _, hs, _, _, hamt⟩
    · exact Or.inl h0
    · exact Or.inr ⟨k, T, s, hs, Or.inl ⟨M.maxBg_attained k ⟨s, hs⟩, hamt⟩⟩
  · rcases h with h0 | ⟨_, k, T, s, _, _, _, hs, _, _, hamt⟩
    · exact Or.inl h0
    · exact Or.inr ⟨k, T, s, hs, Or.inl ⟨M.maxBg_attained k ⟨s, hs⟩, hamt⟩⟩
  · obtain ⟨_, k, T, s, st, _, _, _, hs, _, _⟩ := h
    exact Or.inr ⟨k, T, s, hs, Or.inr (Or.inl ⟨st, M.maxTrans_attained k st ⟨s, hs⟩⟩)⟩
  · obtain ⟨_, k, T, s, _, _, _, hs, _, _⟩ := h
    exact Or.inr ⟨k, T, s, hs, Or.inr (Or.inr (M.maxSpawn_attained k ⟨s, hs⟩))⟩

/-- **A device in a worst state releases no state slack**: a `state` or `envelope` item is
zero when its device's state has the typed set's worst background. -/
theorem LFact.charge_zero_of_worst {cl fz Γ Δ Θ b H D Kc ctl} {i : ASlack R}
    (h : LFact P M Ψ Am cl fz Γ Δ Θ b H D Kc ctl i)
    (hk : i.kind = .state ∨ i.kind = .envelope)
    (hworst : ∀ k T s, s ∈ T → M.bgCost k s = M.maxBg k T) : i.amount = 0 := by
  obtain ⟨k₀, amt⟩ := i
  simp only at hk
  rcases hk with rfl | rfl
  · rcases h with h0 | ⟨_, k, T, s, _, _, _, hs, _, _, hamt⟩
    · exact h0
    · rw [hamt, hworst k T s hs, tsub_self, mul_zero]
  · rcases h with h0 | ⟨_, k, T, s, _, _, _, hs, _, _, hamt⟩
    · exact h0
    · rw [hamt, hworst k T s hs, tsub_self, mul_zero]

/-- **No uncertainty, no state slack**: an item charging a single-state set is zero. -/
theorem charge_zero_of_pinned (Kc : R) (k : K) (s : St) :
    Kc * (M.maxBg k {s} - M.bgCost k s) = 0 := by
  rw [show M.maxBg k {s} = M.bgCost k s from Finset.sup_singleton, tsub_self, mul_zero]

/-- **A tight ambient bound releases no ambient slack**: an `ambient` or `window` item is zero
when the layer's typed ambient bound equals the actual background of what it cannot see.  For a
thread layer the bound is `b + amb`, so this needs the declared `amb` to be tight
(`amb = cost(win ∖ p)`) and the other devices at their worst window states. -/
theorem LFact.amb_zero_of_tight {cl fz Γ Δ Θ b H D Kc ctl} {i : ASlack R}
    (h : LFact P M Ψ Am cl fz Γ Δ Θ b H D Kc ctl i)
    (hk : i.kind = .ambient ∨ i.kind = .window)
    (htight : ∀ S Ae, Corr H D S Am Ae → ambBg M Ae = b) : i.amount = 0 := by
  obtain ⟨k₀, amt⟩ := i
  simp only at hk
  rcases hk with rfl | rfl
  · obtain ⟨_, S, Ae, hC, _, hamt⟩ := h
    rw [hamt, ← htight S Ae hC, tsub_self, mul_zero]
  · obtain ⟨_, S, Ae, hC, _, hamt⟩ := h
    rw [hamt, ← htight S Ae hC, tsub_self, mul_zero]

/-! ### Part 2b: the waiting allowance is rounded up -/

/-- **A waiting tick with more than a tick of budget left releases no wait slack**: it consumes
exactly one tick of the allowance, `waitAllow rem K = K + waitAllow (rem − K) K`. -/
theorem waitAllow_tick_exact {rem Kc : R} (h : Kc < rem) :
    Kc + waitAllow (rem - Kc) Kc = waitAllow rem Kc := by
  have hpos : rem - Kc ≠ 0 := (tsub_pos_of_lt h).ne'
  have hrem : rem ≠ 0 := (lt_of_le_of_lt zero_le h).ne'
  simp only [waitAllow, hpos, hrem, ↓reduceIte]
  rw [tsub_add_cancel_of_le h.le, add_comm]

/-- **The tick that exhausts the budget releases the leftover**: with `0 < rem ≤ K`, the wait
item `waitAllow rem K − (K + waitAllow (rem − K) K)` is exactly `rem` (times the frame's rate). -/
theorem waitAllow_last [AddLeftReflectLE R] {rem Kc : R} (h0 : 0 < rem) (h : rem ≤ Kc) :
    waitAllow rem Kc - (Kc + waitAllow (rem - Kc) Kc) = rem := by
  have hz : rem - Kc = 0 := tsub_eq_zero_of_le h
  simp only [waitAllow, h0.ne', hz, ↓reduceIte, add_zero]
  exact add_tsub_cancel_right rem Kc

/-- **Draining with budget to spare consumes exactly the drained time**: for `d < rem`, the wait
item released by a running thread's tick is exactly `d` (times the frame's rate). -/
theorem waitAllow_drain_exact [AddLeftReflectLE R] {rem d Kc : R} (h : d < rem) :
    waitAllow rem Kc - waitAllow (rem - d) Kc = d := by
  have hpos : rem - d ≠ 0 := (tsub_pos_of_lt h).ne'
  have hrem : rem ≠ 0 := (lt_of_le_of_lt zero_le h).ne'
  simp only [waitAllow, hpos, hrem, ↓reduceIte]
  rw [show rem + Kc = (rem - d + Kc) + d by rw [add_right_comm, tsub_add_cancel_of_le h.le]]
  exact add_tsub_cancel_left (rem - d + Kc) d

/-- **Draining that exhausts the budget releases the leftover plus the extra tick**: for
`0 < rem ≤ d`, the wait item is `rem + K`. -/
theorem waitAllow_drain_last {rem d Kc : R} (h0 : 0 < rem) (h : rem ≤ d) :
    waitAllow rem Kc - waitAllow (rem - d) Kc = rem + Kc := by
  have hz : rem - d = 0 := tsub_eq_zero_of_le h
  simp only [waitAllow, h0.ne', hz, ↓reduceIte, tsub_zero]

/-- **The waiting allowance is never consumed exactly.**  Whichever step exhausts a frame's
budget — a waiting tick (`awaitWait`, budget `rem ≤ K`) or a running thread's tick (drain,
`rem ≤ d`) — releases wait slack of at least the leftover budget `rem > 0`, times the frame's
per-tick rate.  So when that rate is positive, T-Await's waiting charge `(n + f)·w` always
exceeds what the waiting actually costs. -/
theorem waitAllow_exhaust_pos [AddLeftReflectLE R] {rem Kc : R} (h0 : 0 < rem) (h : rem ≤ Kc) :
    0 < waitAllow rem Kc - (Kc + waitAllow (rem - Kc) Kc) ∧
    ∀ {d : R}, rem ≤ d → 0 < waitAllow rem Kc - waitAllow (rem - d) Kc := by
  refine ⟨by rw [waitAllow_last h0 h]; exact h0, fun hd => ?_⟩
  rw [waitAllow_drain_last h0 hd]
  exact lt_of_lt_of_le h0 le_self_add

/-! ### Part 2a: every waiting frame ends in a join or a timeout -/

/-- A final configuration has no waiting frame. -/
theorem Config.Final.not_waits {c : Config K St R} (h : c.Final) : ¬ c.Waits := by
  obtain ⟨σ, H, T, hs⟩ := h
  rintro ⟨ss, σ', H', T', tid, id, rem, fb, rest, r, as, hs'⟩
  rw [hs] at hs'
  cases ss with
  | nil =>
    simp only [List.nil_append, List.cons.injEq, Seg.mk.injEq, Act.mk.injEq] at hs'
    obtain ⟨⟨-, ⟨⟨-, -, -, h, -⟩, -⟩⟩, -⟩ := hs'
    cases h
  | cons s₀ ss' =>
    simp only [List.cons_append, List.cons.injEq] at hs'
    obtain ⟨-, h⟩ := hs'
    cases ss' <;> simp at h

/-- **Runs release slack, and resolve waiting frames**: `CfgTyped.stepsS`, plus: if `main`
waits at the start and not at the end, the run released a `fallback` item (a join) or an
`abandon` item (a timeout). -/
theorem CfgTyped.stepsR (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk) {Ψd : FCtx K St R}
    (hP : P.WF) (hΨc : SigsClosedA P Ψ) (hΨd : SigsDerivedA P M Ψd Ψ)
    {c : Config K St R} {q : R} {c' : Config K St R} (h : Steps P M Ψd Am c q c') :
    ∀ {Φ : R}, CfgTyped P M Ψ Am c Φ → ∃ (Φ' : R) (L : List (ASlack R)),
      CfgTyped P M Ψ Am c' Φ' ∧
      (∀ i ∈ L, ∃ c₁ c₂ q₀ q₁, Steps P M Ψd Am c q₀ c₁ ∧ MStep P M Ψd Am c₁ q₁ c₂ ∧
        i.Spec P M Ψ Am c₁ c₂) ∧
      q + ASlack.total L + Φ' ≤ Φ ∧
      (c.Waits → ¬ c'.Waits → ∃ i ∈ L, i.kind = .fallback ∨ i.kind = .abandon) := by
  induction h with
  | refl =>
    intro Φ hc
    exact ⟨Φ, [], hc, fun _ h => (by cases h), by simp [ASlack.total], fun hw hn => (hn hw).elim⟩
  | @step c₀ q₀ c₁ q' c₂ hs _ ih =>
    intro Φ hc
    obtain ⟨Φ₁, L₁, h₁, hL₁, hle₁, hres₁⟩ := hc.mstepS hM hΨ hP hΨc hΨd hs
    obtain ⟨Φ', L₂, h', hL₂, hle', hres₂⟩ := ih h₁
    refine ⟨Φ', L₁ ++ L₂, h', ?_, ?_, fun hw hn => ?_⟩
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
    · by_cases hw₁ : c₁.Waits
      · obtain ⟨i, hi, hk⟩ := hres₂ hw₁ hn
        exact ⟨i, List.mem_append_right _ hi, hk⟩
      · obtain ⟨i, hi, hk⟩ := hres₁ hw hw₁
        exact ⟨i, List.mem_append_left _ hi, hk⟩

/-- **The T-Await gap on whole programs.**  Take a complete run of a well-typed program that
passes through a configuration where `main` waits on a thread.  The rest of the run releases a
`fallback` item (the thread was joined: the fallback's typed summary, never run) or an
`abandon` item (it timed out: the thread's reservation, unused), specified at the step that
released it — and the run's cost plus that item is still within the bound.  So T-Await's
charge `Q_a + (n + f)·w + Q_fb`, which pays for the body *and* the fallback, is never attained:
every await leaves one of them unused. -/
theorem Program.await_gap (hM : M.WF) (hP : P.WF) {prog : Program K St R}
    {Ψ : SigCtxA K St R} {Γ' : TCtx K} {Δ' W : PCtx K St} {Q : R → R → R} {F : R → R}
    (ht : prog.TypedA P M Ψ Γ' Δ' W Q F) {K₀ q₁ q₂ : R} {c₁ c : Config K St R}
    (h₁ : Steps P M prog.fctx 0 (prog.initConfig K₀) q₁ c₁) (hw : c₁.Waits)
    (h₂ : Steps P M prog.fctx 0 c₁ q₂ c) (hf : c.Final) :
    ∃ i : ASlack R, (i.kind = .fallback ∨ i.kind = .abandon) ∧
      (∃ c₃ c₄ q₃ q₄, Steps P M prog.fctx 0 c₁ q₃ c₃ ∧ MStep P M prog.fctx 0 c₃ q₄ c₄ ∧
        i.Spec P M Ψ 0 c₃ c₄) ∧
      q₁ + q₂ + i.amount ≤ Q K₀ 0 := by
  have hΨd := Program.sigsDerivedA ht
  obtain ⟨Φ₁, hc₁, hle₁⟩ := CfgTyped.steps hM (Program.sigsMonoA hM ht) hP hΨd.closed hΨd h₁
    (Program.initCfgTyped ht K₀)
  obtain ⟨Φ', L, _, hL, hle, hres⟩ :=
    CfgTyped.stepsR hM (Program.sigsMonoA hM ht) hP hΨd.closed hΨd h₂ hc₁
  obtain ⟨i, hi, hk⟩ := hres hw hf.not_waits
  refine ⟨i, hk, hL i hi, ?_⟩
  have hi' : i.amount ≤ ASlack.total L :=
    List.le_sum_of_mem (List.mem_map_of_mem hi)
  rw [add_zero] at hle₁
  calc q₁ + q₂ + i.amount ≤ q₁ + (q₂ + ASlack.total L + Φ') := by
        rw [add_assoc]
        exact add_le_add le_rfl (le_trans (add_le_add le_rfl hi') le_self_add)
    _ ≤ q₁ + Φ₁ := add_le_add le_rfl hle
    _ ≤ Q K₀ 0 := hle₁

/-! ### Part 3: an adversarial schedule attains the waiting charge

Under the schedule that never runs the awaited thread, `main` waits out its whole budget and
times out: the waiting costs `m` ticks with `rem ≤ m·K ≤ rem + K`, the thread's body never runs
(its entire reservation is abandoned), and the fallback runs.  So T-Await's waiting part
`(rem + K)·w` is attained up to one tick when the devices are at the frame's worst states, and
together with Part 2a the bound's `Q_a + (n + f)·w + Q_fb` is approached by the timeout branch
alone — the body's `Q_a` is the part no such schedule uses. -/

/-- **Waiting ticks to the end of the budget.**  If `main`'s running activation has a waiting
frame on a pending thread with budget `rem ≤ m·K`, the machine can wait it out: some `m'` ticks
(each costing `K·(bg(D) + bg(A))`, nothing else moving) bring the budget to `0`, with
`rem ≤ m'·K ≤ rem + K` (and no tick if the budget is already spent). -/
theorem Steps.waiting {Ψd : FCtx K St R} {σ : Mem} {H : Var → Option Dev}
    {T : Var → Option ThreadId} {tid : Var} {id : ThreadId} {fb : Cmd St R}
    {rest : List (Ctl St R)} {r : Option (Expr × Var)} {as : List (Act St R)}
    {pool : ThreadId → Option (PoolEntry St R)} {D : RPeriphs K St} {Kc : R}
    {e : PoolEntry St R} (hrest : CtlNoAwait rest) (has : ActsNoAwait as)
    (hpe : pool id = some e) (hpend : e.status = .pending) :
    ∀ (m : ℕ) (rem : R), rem ≤ m • Kc → ∃ m' : ℕ,
      Steps P M Ψd Am ⟨[⟨none, ⟨σ, H, T, .awaitW tid id rem fb :: rest, r⟩ :: as⟩], pool, D, Kc⟩
        (m' • (Kc * (D.bg M + ambBg M Am)))
        ⟨[⟨none, ⟨σ, H, T, .awaitW tid id 0 fb :: rest, r⟩ :: as⟩], pool, D, Kc⟩ ∧
      rem ≤ m' • Kc ∧ m' • Kc ≤ rem + Kc ∧ (rem = 0 → m' = 0) := by
  intro m
  induction m with
  | zero =>
    intro rem hrem
    rw [zero_nsmul, nonpos_iff_eq_zero] at hrem
    subst hrem
    exact ⟨0, by rw [zero_nsmul]; exact .refl, by simp, by simp, fun _ => rfl⟩
  | succ m ih =>
    intro rem hrem
    by_cases h0 : rem = 0
    · subst h0
      exact ⟨0, by rw [zero_nsmul]; exact .refl, by simp, by simp, fun _ => rfl⟩
    have hpos : 0 < rem := pos_iff_ne_zero.2 h0
    have hMS : MStep P M Ψd Am
        ⟨[⟨none, ⟨σ, H, T, .awaitW tid id rem fb :: rest, r⟩ :: as⟩], pool, D, Kc⟩
        (Kc * (D.bg M + ambBg M Am))
        ⟨[⟨none, ⟨σ, H, T, .awaitW tid id (rem - Kc) fb :: rest, r⟩ :: as⟩], pool, D, Kc⟩ :=
      ⟨true, _, .awaitWait hpe hpend hpos, by
        simp only [↓reduceIte]
        exact (Config.drain_main (K := K) (tsegs := []) (σ := σ) (H := H) (T := T)
          (x := .awaitW tid id rem fb) (r := r) (pool := pool) (D := D) (Kc := Kc) (d := Kc)
          (fun _ h => by cases h) hrest has).symm⟩
    have hrem' : rem - Kc ≤ m • Kc := by
      rw [succ_nsmul] at hrem; exact tsub_le_iff_right.2 hrem
    obtain ⟨m'', hs, h1, h2, h3⟩ := ih (rem - Kc) hrem'
    refine ⟨m'' + 1, ?_, ?_, ?_, fun h => absurd h h0⟩
    · refine (Steps.step hMS hs).cast ?_
      rw [succ_nsmul, add_comm]
    · rw [succ_nsmul]; exact tsub_le_iff_right.1 h1
    · rw [succ_nsmul]
      by_cases hle : rem ≤ Kc
      · rw [h3 (tsub_eq_zero_of_le hle), zero_nsmul, zero_add]; exact le_add_self
      · have hc := tsub_add_cancel_of_le (le_of_not_ge hle)
        exact add_le_add (hc ▸ h2) le_rfl

/-- **The adversarial schedule: never run the awaited thread.**  From a configuration where
`main` waits on a pending thread with budget `rem`, at a positive clock in an Archimedean cost
domain, there is a run that only waits and then times out into the fallback: its cost is `m`
waiting ticks with `rem ≤ m·K ≤ rem + K`, the store and clock are unchanged, and the thread is
dropped from the pool without ever having run (so its whole body reservation is abandoned). -/
theorem Steps.never_schedule [Archimedean R] {Ψd : FCtx K St R} {σ : Mem}
    {H : Var → Option Dev} {T : Var → Option ThreadId} {tid : Var} {id : ThreadId}
    {rem : R} {fb : Cmd St R} {rest : List (Ctl St R)} {r : Option (Expr × Var)}
    {as : List (Act St R)} {pool : ThreadId → Option (PoolEntry St R)} {D : RPeriphs K St}
    {Kc : R} {e : PoolEntry St R} (hK : 0 < Kc) (hrest : CtlNoAwait rest)
    (has : ActsNoAwait as) (hpe : pool id = some e) (hpend : e.status = .pending) :
    ∃ m : ℕ,
      Steps P M Ψd Am ⟨[⟨none, ⟨σ, H, T, .awaitW tid id rem fb :: rest, r⟩ :: as⟩], pool, D, Kc⟩
        ((m • Kc) * (D.bg M + ambBg M Am))
        ⟨[⟨none, ⟨σ, H, Function.update T tid none, .cmd fb :: rest, r⟩ :: as⟩],
          Function.update pool id none, D, Kc⟩ ∧
      rem ≤ m • Kc ∧ m • Kc ≤ rem + Kc := by
  obtain ⟨m₀, hm₀⟩ := Archimedean.arch rem hK
  obtain ⟨m, hs, h1, h2, _⟩ := Steps.waiting (P := P) (M := M) (Ψd := Ψd) (Am := Am)
    (σ := σ) (H := H) (T := T) (tid := tid) (fb := fb) (r := r) (D := D)
    hrest has hpe hpend m₀ rem hm₀
  have hto : MStep P M Ψd Am
      ⟨[⟨none, ⟨σ, H, T, .awaitW tid id 0 fb :: rest, r⟩ :: as⟩], pool, D, Kc⟩ 0
      ⟨[⟨none, ⟨σ, H, Function.update T tid none, .cmd fb :: rest, r⟩ :: as⟩],
        Function.update pool id none, D, Kc⟩ :=
    ⟨false, _, .awaitTimeout hpe hpend le_rfl, rfl⟩
  exact ⟨m, (hs.trans (Steps.single hto)).cast (by rw [add_zero, nsmul_eq_mul, nsmul_eq_mul, mul_assoc]), h1, h2⟩

/-- **The waiting charge is attained up to one tick.**  On the adversarial run, if the devices
are at the waiting frame's typed worst states (actual rate `bg(D) + bg(A)` equal to the frame's
typed rate `w`), the waiting costs between `rem·w` and `(rem + K)·w`; T-Await charges
`waitAllow rem K · w = (rem + K)·w`, so it is attained up to `K·w`, the rounding of Part 2b. -/
theorem waiting_cost_bounds {m : ℕ} {rem Kc w : R} (h1 : rem ≤ m • Kc) (h2 : m • Kc ≤ rem + Kc) :
    rem * w ≤ (m • Kc) * w ∧ (m • Kc) * w ≤ (rem + Kc) * w :=
  ⟨mul_le_mul_of_nonneg_right h1 zero_le, mul_le_mul_of_nonneg_right h2 zero_le⟩
