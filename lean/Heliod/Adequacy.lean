import Heliod.Machine
import Heliod.Accounting
import Heliod.Soundness

/-!
# Adequacy of the machine for the synchronous fragment

* **Forward** (`Eval.toMachine`, `Program.Eval.toMRun`): every big-step run of `Eval` is
  matched by a run of the small-step machine with the same cost, final memory and clock, ending
  in corresponding peripheral states.
* **Reverse** (`StepsN.toEval`, `Program.MRun.toEval`): every complete machine run of a
  synchronous program (no `async`/`await` in `main` or any function body) is a big-step run with
  the same cost.  Proved by strong induction on the number of machine steps: with no threads,
  each command's first step is determined, and a call's body run is followed by its return.
* **Consequence** (`Program.MRun.soundness`): cost soundness holds on the machine for
  synchronous programs; likewise the accounting and slack results transfer.

So the machine, built for async, does not change the meaning or the cost of synchronous code.

The reverse direction also needs `Rev`: every device an activation's handle map reaches is one
of its visible handles (so a machine step on a device is an `Eval` step on a handle).  The
machine's E-Call checks that the parameter's device holds a peripheral, as `Eval` does.

## Relating the two views of peripherals

`Eval` gives each activation a *view*: visible handles `S` and invisible ambient peripherals
`A_e`.  The machine has one global store `D` of devices, a handle map `H` per activation, and a
fixed outer ambient `A_m`.  `Corr H D S A_m A_e` says:

* every visible handle maps through `H` to a device whose entry is the handle's entry;
* distinct visible handles map to distinct devices;
* the populations agree: `entries(D) + A_m = entries(S) + A_e` (`Heliod.Accounting`).

The population equation is what makes every charge agree: `bg(S) + bg(A_e) = bg(D) + bg(A_m)`
(`Corr.bg_eq`), and after removing the moving peripheral on both sides, the same for transitions
(`Corr.erase_bg`).  At a call, `pop_call` shows the callee's view (its parameter plus the new
ambient `A_e + entries(S ∖ p)`) has the same population.

`Frame S H D D'`: a run changes only devices that visible handles map to.  This is what lets a
caller's other handles keep their states across a call.
-/

open RPeriphs

variable {K St R : Type} [DecidableEq St] [CommSemiring R] [LinearOrder R]
variable [Sub R]

/-! ### Configurations without waiting timers -/

/-- A control entry that is a command (not a waiting `await`). -/
def Ctl.IsCmd : Ctl St R → Prop
  | .cmd _ => True
  | .awaitW .. => False

/-- No waiting `await` in a control stack. -/
def CtlNoAwait (ctl : List (Ctl St R)) : Prop := ∀ x ∈ ctl, x.IsCmd

/-- No waiting `await` in a list of activations. -/
def ActsNoAwait (as : List (Act St R)) : Prop := ∀ a ∈ as, CtlNoAwait a.ctl

/-- No waiting `await` anywhere in a list of segments. -/
def SegsNoAwait (ss : List (Seg St R)) : Prop := ∀ s ∈ ss, ActsNoAwait s.acts

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
/-- Draining leaves a command entry unchanged. -/
theorem Ctl.drain_of_isCmd {d : R} {x : Ctl St R} (h : x.IsCmd) : x.drain d = x := by
  cases x
  · rfl
  · exact absurd h id

omit [DecidableEq St] [LinearOrder R] in
omit [CommSemiring R] in
/-- Without waiting `await`s, draining timers does nothing.  Synchronous runs never create a
waiting `await`, so their ticked steps leave the configuration as the step produced it. -/
theorem Config.drain_eq_self {d : R} {c : Config K St R} (h : SegsNoAwait c.segs) :
    c.drain d = c := by
  obtain ⟨segs, pool, D, Kc⟩ := c
  simp only [Config.drain, Config.mk.injEq, and_true]
  refine (List.map_congr_left ?_).trans (List.map_id segs)
  intro s hs
  obtain ⟨o, acts⟩ := s
  simp only [Seg.mk.injEq, true_and, id]
  refine (List.map_congr_left ?_).trans (List.map_id acts)
  intro a ha
  obtain ⟨σ, H, T, ctl, r⟩ := a
  simp only [Act.mk.injEq, true_and, and_true, id]
  refine (List.map_congr_left ?_).trans (List.map_id ctl)
  intro x hx
  exact Ctl.drain_of_isCmd (h _ hs _ ha _ hx)

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
omit [Sub R] in
/-- Building a waiting-free segment list from its top activation. -/
theorem segsNoAwait_cons {o : Option ThreadId} {σ : Mem} {H : Var → Option Dev}
    {T : Var → Option ThreadId} {ctl : List (Ctl St R)} {r : Option (Expr × Var)}
    {as : List (Act St R)} {ss : List (Seg St R)}
    (hctl : CtlNoAwait ctl) (has : ActsNoAwait as) (hss : SegsNoAwait ss) :
    SegsNoAwait (⟨o, ⟨σ, H, T, ctl, r⟩ :: as⟩ :: ss) := by
  intro s hs
  rcases List.mem_cons.1 hs with rfl | hs
  · intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hctl
    · exact has a ha
  · exact hss s hs

/-! ### Runs -/

section Runs

variable {P : Platform K St} {M : CostModel K St R} {Ψd : FCtx K St R} {A : Multiset (K × St)}

/-- Runs compose. -/
theorem Steps.trans {c c₁ c₂ : Config K St R} {q q' : R}
    (h₁ : Steps P M Ψd A c q c₁) (h₂ : Steps P M Ψd A c₁ q' c₂) :
    Steps P M Ψd A c (q + q') c₂ := by
  induction h₁ with
  | refl => simpa using h₂
  | step h _ ih => rw [add_assoc]; exact .step h (ih h₂)

/-- Transport a run along an equation between costs. -/
theorem Steps.cast {c c' : Config K St R} {q q' : R} (h : Steps P M Ψd A c q c')
    (hq : q = q') : Steps P M Ψd A c q' c' := hq ▸ h

/-- A single step is a run. -/
theorem Steps.single {c c' : Config K St R} {q : R} (h : MStep P M Ψd A c q c') :
    Steps P M Ψd A c q c' := by simpa using Steps.step h .refl

/-- A ticked step into a configuration without waiting timers is a machine step. -/
theorem MStep.of_tick {c c₁ : Config K St R} {q : R} (h : Step P M Ψd A c q true c₁)
    (hna : SegsNoAwait c₁.segs) : MStep P M Ψd A c q c₁ :=
  ⟨true, c₁, h, (Config.drain_eq_self hna).symm⟩

/-- An unticked step is a machine step. -/
theorem MStep.of_notick {c c₁ : Config K St R} {q : R} (h : Step P M Ψd A c q false c₁) :
    MStep P M Ψd A c q c₁ :=
  ⟨false, c₁, h, rfl⟩

end Runs

/-! ### The correspondence -/

/-- `Eval`'s view `(S, A_e)` of an activation corresponds to the machine's `(H, D, A_m)`. -/
structure Corr (H : Var → Option Dev) (D S : RPeriphs K St) (Am Ae : Multiset (K × St)) :
    Prop where
  vis : ∀ x, S x ≠ 0 → ∃ d, H x = some d ∧ D d = S x
  inj : ∀ x y d, S x ≠ 0 → S y ≠ 0 → H x = some d → H y = some d → x = y
  pop : RPeriphs.pop D Am = RPeriphs.pop S Ae

/-- A run changes only devices that visible handles map to. -/
def Frame (S : RPeriphs K St) (H : Var → Option Dev) (D D' : RPeriphs K St) : Prop :=
  ∀ dv, (∀ x, S x ≠ 0 → H x ≠ some dv) → D' dv = D dv

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
/-- A present entry is nonzero. -/
theorem REntry.at_ne_zero {k : K} {s : St} : (REntry.at k s : REntry K St) ≠ 0 :=
  fun h => by cases h

section Corr

variable {H : Var → Option Dev} {D S : RPeriphs K St} {Am Ae : Multiset (K × St)}

omit [DecidableEq St] [LinearOrder R] in
omit [Sub R] in
/-- **Background charges agree** under the correspondence. -/
theorem Corr.bg_eq (hC : Corr H D S Am Ae) (M : CostModel K St R) :
    S.bg M + ambBg M Ae = D.bg M + ambBg M Am := by
  rw [← ambBg_pop, ← ambBg_pop, hC.pop]

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
/-- A visible handle's device holds the handle's entry. -/
theorem Corr.lookup (hC : Corr H D S Am Ae) {p : Var} {k : K} {s : St} (h : S p = .at k s) :
    ∃ d, H p = some d ∧ D d = .at k s := by
  obtain ⟨d, h₁, h₂⟩ := hC.vis p (by rw [h]; exact REntry.at_ne_zero)
  exact ⟨d, h₁, h₂.trans h⟩

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
/-- Removing the moving peripheral from both views keeps the populations equal. -/
theorem Corr.erase_pop (hC : Corr H D S Am Ae) {p d : Var} {k : K} {s : St}
    (hS : S p = .at k s) (hD : D d = .at k s) :
    RPeriphs.pop (D.erase d) Am = RPeriphs.pop (S.erase p) Ae := by
  have h := hC.pop
  rw [pop_split hD, pop_split hS] at h
  exact (Multiset.cons_inj_right _).1 h

omit [DecidableEq St] [LinearOrder R] in
omit [Sub R] in
/-- **Transition charges agree** under the correspondence. -/
theorem Corr.erase_bg (hC : Corr H D S Am Ae) (M : CostModel K St R) {p d : Var} {k : K}
    {s : St} (hS : S p = .at k s) (hD : D d = .at k s) :
    (S.erase p).bg M + ambBg M Ae = (D.erase d).bg M + ambBg M Am := by
  rw [← ambBg_pop, ← ambBg_pop, hC.erase_pop hS hD]

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
/-- After `S[p ↦ st]`, a handle is visible iff it was. -/
theorem set_ne_zero {S : RPeriphs K St} {p x : Var} {k : K} {st : St} :
    (S.set p k st) x ≠ 0 → x ≠ p → S x ≠ 0 := by
  intro h hx; simpa [RPeriphs.set_apply, hx] using h

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
/-- **Moving a peripheral preserves the correspondence**, and changes only its device. -/
theorem Corr.set (hC : Corr H D S Am Ae) {p d : Var} {k : K} {s : St} (hS : S p = .at k s)
    (hH : H p = some d) (hD : D d = .at k s) (st : St) :
    Corr H (D.set d k st) (S.set p k st) Am Ae ∧ Frame S H D (D.set d k st) := by
  have hpv : S p ≠ 0 := by rw [hS]; exact REntry.at_ne_zero
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    by_cases hxp : x = p
    · subst hxp; exact ⟨d, hH, by simp⟩
    · have hx' := set_ne_zero hx hxp
      obtain ⟨d', hH', hD'⟩ := hC.vis x hx'
      have hne : d' ≠ d := fun h => hxp (hC.inj x p d hx' hpv (h ▸ hH') hH)
      exact ⟨d', hH', by simp [RPeriphs.set_apply, hne, hxp, hD']⟩
  · intro x y d' hx hy hHx hHy
    have hx' : S x ≠ 0 := by
      by_cases hxp : x = p
      · subst hxp; exact hpv
      · exact set_ne_zero hx hxp
    have hy' : S y ≠ 0 := by
      by_cases hyp : y = p
      · subst hyp; exact hpv
      · exact set_ne_zero hy hyp
    exact hC.inj x y d' hx' hy' hHx hHy
  · rw [pop_after_move, pop_after_move, hC.erase_pop hS hD]
  · intro dv hdv
    have hne : dv ≠ d := fun he => hdv p hpv (by rw [he]; exact hH)
    rw [RPeriphs.set_apply]
    simp [hne]

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
/-- **The callee's view corresponds too**: its parameter `q` maps to the caller's device for
`p`, and its population (parameter plus the new ambient) is the caller's. -/
theorem Corr.call (hC : Corr H D S Am Ae) {p d : Var} {k : K} {s : St} (hS : S p = .at k s)
    (hD : D d = .at k s) (q : Var) :
    Corr (fun y => if y = q then some d else none) D (Finsupp.single q (.at k s)) Am
      (Ae + (S.erase p).entries) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    by_cases hxq : x = q
    · subst hxq; exact ⟨d, by simp, by simp [hD]⟩
    · exact absurd (Finsupp.single_eq_of_ne hxq) hx
  · intro x y d' hx hy _ _
    have hxq : x = q := by
      by_contra hne; exact hx (Finsupp.single_eq_of_ne hne)
    have hyq : y = q := by
      by_contra hne; exact hy (Finsupp.single_eq_of_ne hne)
    rw [hxq, hyq]
  · rw [pop_call hS q Ae]; exact hC.pop

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
/-- The empty store has no entries. -/
theorem entries_zero : RPeriphs.entries (0 : RPeriphs K St) = 0 :=
  Finsupp.sum_zero_index

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
/-- **Returning restores the caller's view.**  If the callee's run corresponds and changed only
the caller's device for `p` (the only device it can reach), the caller's view with `p` in the
callee's final state `s'` corresponds to the final store. -/
theorem Corr.ret (hC : Corr H D S Am Ae) {p d q : Var} {k : K} {s s' : St} (hS : S p = .at k s)
    (hH : H p = some d) {Db Sb : RPeriphs K St}
    (hCb : Corr (fun y => if y = q then some d else none) Db Sb Am (Ae + (S.erase p).entries))
    (hSb : Sb q = .at k s') (hzero : ∀ x, x ≠ q → Sb x = 0)
    (hFb : Frame (Finsupp.single q (.at k s)) (fun y => if y = q then some d else none) D Db) :
    Corr H Db (S.set p k s') Am Ae ∧ Frame S H D Db := by
  have hpv : S p ≠ 0 := by rw [hS]; exact REntry.at_ne_zero
  have hDb : Db d = .at k s' := by
    obtain ⟨d', h₁, h₂⟩ := hCb.lookup hSb
    simp only [↓reduceIte, Option.some.injEq] at h₁
    rw [h₁]; exact h₂
  have hframe : ∀ dv, dv ≠ d → Db dv = D dv := by
    intro dv hne
    refine hFb dv fun y hy => ?_
    have hyq : y = q := by
      by_contra h; exact hy (Finsupp.single_eq_of_ne h)
    simp [hyq, Ne.symm hne]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    by_cases hxp : x = p
    · subst hxp; exact ⟨d, hH, by simp [hDb]⟩
    · have hx' := set_ne_zero hx hxp
      obtain ⟨d', hH', hD'⟩ := hC.vis x hx'
      have hne : d' ≠ d := fun h => hxp (hC.inj x p d hx' hpv (h ▸ hH') hH)
      exact ⟨d', hH', by rw [hframe d' hne, hD', RPeriphs.set_apply]; simp [hxp]⟩
  · intro x y d' hx hy hHx hHy
    have hx' : S x ≠ 0 := by
      by_cases hxp : x = p
      · subst hxp; exact hpv
      · exact set_ne_zero hx hxp
    have hy' : S y ≠ 0 := by
      by_cases hyp : y = p
      · subst hyp; exact hpv
      · exact set_ne_zero hy hyp
    exact hC.inj x y d' hx' hy' hHx hHy
  · have hz : Sb.erase q = 0 := by
      ext x
      rw [RPeriphs.erase_apply]
      split_ifs with hxq
      · rfl
      · exact hzero x hxq
    rw [hCb.pop, pop_split hSb, hz, pop_after_move]
    unfold RPeriphs.pop
    rw [entries_zero, zero_add, add_comm]
  · intro dv hdv
    exact hframe dv fun he => hdv p hpv (by rw [he]; exact hH)

end Corr

omit [CommSemiring R] [LinearOrder R] in
omit [Sub R] in
/-- A run keeps the set of visible handles (from `Eval.kind_eq`). -/
theorem Eval.ne_zero_iff [CommSemiring R] {M : CostModel K St R} {Ψd : FCtx K St R}
    {A σ S Kc c σ' S' q K'} (h : Eval M Ψd A σ S Kc c σ' S' q K') (x : Var) :
    S' x ≠ 0 ↔ S x ≠ 0 := by
  rw [ne_eq, ne_eq, ← REntry.kind_eq_none, ← REntry.kind_eq_none, h.kind_eq x]

/-! ### The simulation -/

/-- **Adequacy (forward).**  Every run of `Eval` from a view corresponding to a machine
activation is matched by a machine run executing the same command in that activation, with
the same cost, final memory and clock; the final store corresponds to the final view, and only
devices of visible handles changed.  Any context below the running command (further commands,
callers' activations, other segments, the thread pool) is untouched, as long as it has no
waiting `await` timer (which ticks would advance). -/
theorem Eval.toMachine (P : Platform K St) {M : CostModel K St R} {Ψd : FCtx K St R}
    {Ae σ S Kc c σ' S' q K'} (he : Eval M Ψd Ae σ S Kc c σ' S' q K') :
    ∀ {Am : Multiset (K × St)} {H : Var → Option Dev} {D : RPeriphs K St}
      {o : Option ThreadId} {T : Var → Option ThreadId} {ctl : List (Ctl St R)}
      {r : Option (Expr × Var)} {as : List (Act St R)} {ss : List (Seg St R)}
      {pool : ThreadId → Option (PoolEntry St R)},
    Corr H D S Am Ae → CtlNoAwait ctl → ActsNoAwait as → SegsNoAwait ss →
    ∃ D', Steps P M Ψd Am ⟨⟨o, ⟨σ, H, T, .cmd c :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩ q
        ⟨⟨o, ⟨σ', H, T, ctl, r⟩ :: as⟩ :: ss, pool, D', K'⟩ ∧
      Corr H D' S' Am Ae ∧ Frame S H D D' := by
  induction he with
  | skip =>
    intro Am H D o T ctl r as ss pool hC hctl has hss
    exact ⟨D, Steps.single (MStep.of_notick .skip), hC, fun _ _ => rfl⟩
  | assign hev =>
    intro Am H D o T ctl r as ss pool hC hctl has hss
    refine ⟨D, (Steps.single (MStep.of_tick (.assign hev)
      (segsNoAwait_cons hctl has hss))).cast ?_, hC, fun _ _ => rfl⟩
    rw [add_assoc, add_assoc, hC.bg_eq M]
  | iteTrue hev _ ih =>
    intro Am H D o T ctl r as ss pool hC hctl has hss
    obtain ⟨D', hrun, hC', hF⟩ := ih hC hctl has hss
    refine ⟨D', (Steps.trans (Steps.single (MStep.of_tick (.iteTrue hev)
      (segsNoAwait_cons (fun x hx => ?_) has hss))) hrun).cast ?_, hC', hF⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · trivial
      · exact hctl x hx
    · rw [add_comm, add_assoc, add_assoc, hC.bg_eq M]
  | iteFalse hev _ ih =>
    intro Am H D o T ctl r as ss pool hC hctl has hss
    obtain ⟨D', hrun, hC', hF⟩ := ih hC hctl has hss
    refine ⟨D', (Steps.trans (Steps.single (MStep.of_tick (.iteFalse hev)
      (segsNoAwait_cons (fun x hx => ?_) has hss))) hrun).cast ?_, hC', hF⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · trivial
      · exact hctl x hx
    · rw [add_comm, add_assoc, add_assoc, hC.bg_eq M]
  | transition hSp =>
    intro Am H D o T ctl r as ss pool hC hctl has hss
    obtain ⟨d, hH, hD⟩ := hC.lookup hSp
    obtain ⟨hC', hF⟩ := hC.set hSp hH hD _
    refine ⟨_, (Steps.single (MStep.of_tick (.transition hH hD)
      (segsNoAwait_cons hctl has hss))).cast ?_, hC', hF⟩
    rw [add_assoc, add_assoc, hC.erase_bg M hSp hD]
  | downgrade hSp =>
    intro Am H D o T ctl r as ss pool hC hctl has hss
    obtain ⟨d, hH, hD⟩ := hC.lookup hSp
    obtain ⟨hC', hF⟩ := hC.set hSp hH hD _
    refine ⟨_, (Steps.single (MStep.of_tick (.downgrade hH hD)
      (segsNoAwait_cons hctl has hss))).cast ?_, hC', hF⟩
    rw [add_assoc, add_assoc, hC.erase_bg M hSp hD]
  | clock =>
    intro Am H D o T ctl r as ss pool hC hctl has hss
    refine ⟨D, (Steps.single (MStep.of_tick .clock
      (segsNoAwait_cons hctl has hss))).cast ?_, hC, fun _ _ => rfl⟩
    rw [hC.bg_eq M]
  | @seq A σ S Kc c₁ c₂ σ₁ S₁ q₁ K₁ σ₂ S₂ q₂ K₂ h₁ _ ih₁ ih₂ =>
    intro Am H D o T ctl r as ss pool hC hctl has hss
    have hctl₂ : CtlNoAwait (.cmd c₂ :: ctl) := fun x hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · trivial
      · exact hctl x hx
    obtain ⟨D₁, hrun₁, hC₁, hF₁⟩ := ih₁ hC hctl₂ has hss
    obtain ⟨D₂, hrun₂, hC₂, hF₂⟩ := ih₂ hC₁ hctl has hss
    refine ⟨D₂, ((Steps.single (MStep.of_notick .seq)).trans
      (hrun₁.trans hrun₂)).cast (zero_add _), hC₂, fun dv hdv => ?_⟩
    rw [hF₂ dv fun x hx => hdv x ((h₁.ne_zero_iff x).1 hx), hF₁ dv hdv]
  | matchSt hSp hf _ ih =>
    intro Am H D o T ctl r as ss pool hC hctl has hss
    obtain ⟨d, hH, hD⟩ := hC.lookup hSp
    obtain ⟨D', hrun, hC', hF⟩ := ih hC hctl has hss
    refine ⟨D', (Steps.trans (Steps.single (MStep.of_tick (.matchSt hH hD hf)
      (segsNoAwait_cons (fun x hx => ?_) has hss))) hrun).cast ?_, hC', hF⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · trivial
      · exact hctl x hx
    · rw [add_comm, hC.bg_eq M]
  | @call A σ S Kc x g e p dcl v k s σb Sb qb Kb rv s' hg hev hSp hb hret hSb ih =>
    intro Am H D o T ctl r as ss pool hC hctl has hss
    obtain ⟨d, hH, hD⟩ := hC.lookup hSp
    have hCb := hC.call hSp hD dcl.parg
    -- run the body on top of the caller
    obtain ⟨Db, hrunb, hCb', hFb⟩ := ih (o := o) (T := fun _ => none) (ctl := [])
      (r := some (dcl.ret, x)) (as := ⟨σ, H, T, ctl, r⟩ :: as) (ss := ss) (pool := pool)
      hCb (fun _ h => by cases h) (fun a ha => by
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hctl
        · exact has a ha) hss
    have hzero : ∀ y, y ≠ dcl.parg → Sb y = 0 := by
      intro y hy
      by_contra hne
      exact (hb.ne_zero_iff y).1 hne (Finsupp.single_eq_of_ne hy)
    obtain ⟨hC', hF⟩ := hC.ret hSp hH hCb' hSb hzero hFb
    have hcall : MStep P M Ψd Am ⟨⟨o, ⟨σ, H, T, .cmd (.call x g e p) :: ctl, r⟩ :: as⟩ :: ss,
        pool, D, Kc⟩ (Kc * (e.cost M + D.bg M + ambBg M Am))
        ⟨⟨o, ⟨Mem.empty.set dcl.arg v, fun y => if y = dcl.parg then some d else none,
            fun _ => none, [.cmd dcl.body], some (dcl.ret, x)⟩ ::
          ⟨σ, H, T, ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩ := by
      refine MStep.of_tick (.call hg hev hH hD) ?_
      intro sg hsg
      rcases List.mem_cons.1 hsg with rfl | hsg
      · intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · trivial
          · cases hy
        · rcases List.mem_cons.1 ha with rfl | ha
          · exact hctl
          · exact has a ha
      · exact hss sg hsg
    have hretS : MStep P M Ψd Am ⟨⟨o, ⟨σb, fun y => if y = dcl.parg then some d else none,
            fun _ => none, [], some (dcl.ret, x)⟩ :: ⟨σ, H, T, ctl, r⟩ :: as⟩ :: ss, pool, Db, Kb⟩
        (Kb * (dcl.ret.cost M + Db.bg M + ambBg M Am))
        ⟨⟨o, ⟨σ.set x rv, H, T, ctl, r⟩ :: as⟩ :: ss, pool, Db, Kb⟩ :=
      MStep.of_tick (.ret hret) (segsNoAwait_cons hctl has hss)
    refine ⟨Db, ((Steps.single hcall).trans (hrunb.trans (Steps.single hretS))).cast ?_,
      hC', hF⟩
    have h₁ : Kc * (e.cost M + S.bg M + ambBg M A) = Kc * (e.cost M + D.bg M + ambBg M Am) := by
      rw [add_assoc, add_assoc, hC.bg_eq M]
    have h₂ : Kb * (dcl.ret.cost M + Sb.bg M + ambBg M (A + (S.erase p).entries)) =
        Kb * (dcl.ret.cost M + Db.bg M + ambBg M Am) := by
      rw [add_assoc, add_assoc, hCb'.bg_eq M]
    rw [h₁, h₂]
    exact (add_assoc _ _ _).symm

/-- **Adequacy for whole programs (forward).**  Every big-step run of a program is a complete
machine run with the same cost: `main` starts with each declared handle naming its own device,
so the initial view and store coincide. -/
theorem Program.Eval.toMRun (P : Platform K St) {M : CostModel K St R} {prog : Program K St R}
    {K₀ : R} {σ' : Mem} {S' : RPeriphs K St} {q K' : R} (he : prog.Eval M K₀ σ' S' q K') :
    ∃ c, prog.MRun P M K₀ c q := by
  have hC : Corr some prog.initPeriphs prog.initPeriphs 0 0 :=
    ⟨fun x _ => ⟨x, rfl, rfl⟩, fun _ _ _ _ _ hx hy => Option.some.inj (hx.trans hy.symm), rfl⟩
  obtain ⟨D', hrun, -, -⟩ := Eval.toMachine P he (o := none) (T := fun _ => none) (ctl := [])
    (r := none) (as := []) (ss := []) (pool := fun _ => none) hC (fun _ h => by cases h)
    (fun _ h => by cases h) (fun _ h => by cases h)
  exact ⟨_, hrun, _, _, _, rfl⟩

/-! ## Reverse direction: machine runs of synchronous code are `Eval` runs -/

/-! ### Synchronous commands -/

mutual

/-- Commands of the synchronous fragment: no `async` / `await`. -/
def Cmd.Sync : Cmd St R → Prop
  | .ite _ c₁ c₂ => c₁.Sync ∧ c₂.Sync
  | .seq c₁ c₂ => c₁.Sync ∧ c₂.Sync
  | .matchSt _ arms => arms.Sync
  | .async .. => False
  | .await .. => False
  | _ => True

/-- Every arm is synchronous. -/
def Arms.Sync : Arms St R → Prop
  | .nil => True
  | .cons _ c rest => c.Sync ∧ rest.Sync

end

omit [CommSemiring R] [LinearOrder R] in
omit [Sub R] in
/-- The arm a synchronous `match` selects is synchronous. -/
theorem Arms.Sync.find : ∀ {arms : Arms St R} {s : St} {c : Cmd St R},
    arms.Sync → arms.find? s = some c → c.Sync
  | .nil, _, _, _, hf => by cases hf
  | .cons st c' rest, s, c, h, hf => by
      simp only [Arms.Sync] at h
      simp only [Arms.find?] at hf
      split_ifs at hf
      · cases hf; exact h.1
      · exact Arms.Sync.find h.2 hf

/-! ### Runs with a step count -/

section StepsN

variable {P : Platform K St} {M : CostModel K St R} {Ψd : FCtx K St R} {A : Multiset (K × St)}

/-- Runs with their number of steps (for strong induction). -/
inductive StepsN (P : Platform K St) (M : CostModel K St R) (Ψd : FCtx K St R)
    (A : Multiset (K × St)) : Nat → Config K St R → R → Config K St R → Prop where
  | refl {c} : StepsN P M Ψd A 0 c 0 c
  | step {n c q c₁ q' c₂} :
      MStep P M Ψd A c q c₁ → StepsN P M Ψd A n c₁ q' c₂ → StepsN P M Ψd A (n + 1) c (q + q') c₂

/-- Every run has a step count. -/
theorem Steps.toN {c c' : Config K St R} {q : R} (h : Steps P M Ψd A c q c') :
    ∃ n, StepsN P M Ψd A n c q c' := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | step h _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step h hn⟩

omit [Sub R] in
/-- Ticked steps never create a waiting `await` (only the unticked `awaitStart` does). -/
theorem Step.noAwait_of_tick {c c₁ : Config K St R} {q : R} (h : Step P M Ψd A c q true c₁)
    (hna : SegsNoAwait c.segs) : SegsNoAwait c₁.segs := by
  have top : ∀ {o σ H T x ctl r as ss}, SegsNoAwait
      (⟨o, ⟨σ, H, T, x :: ctl, r⟩ :: as⟩ :: ss : List (Seg St R)) →
      CtlNoAwait ctl ∧ ActsNoAwait as ∧ SegsNoAwait ss := by
    intro o σ H T x ctl r as ss h
    refine ⟨fun y hy => h _ (List.mem_cons_self ..) _ (List.mem_cons_self ..) y
        (List.mem_cons_of_mem _ hy), fun a ha => h _ (List.mem_cons_self ..) a
        (List.mem_cons_of_mem _ ha), fun s hs => h s (List.mem_cons_of_mem _ hs)⟩
  have hd : ∀ {o σ H T x ctl r as ss}, SegsNoAwait
      (⟨o, ⟨σ, H, T, x :: ctl, r⟩ :: as⟩ :: ss : List (Seg St R)) → x.IsCmd := by
    intro o σ H T x ctl r as ss h
    exact h _ (List.mem_cons_self ..) _ (List.mem_cons_self ..) x (List.mem_cons_self ..)
  cases h with
  | assign => obtain ⟨h₁, h₂, h₃⟩ := top hna; exact segsNoAwait_cons h₁ h₂ h₃
  | iteTrue =>
    obtain ⟨h₁, h₂, h₃⟩ := top hna
    exact segsNoAwait_cons (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · trivial
      · exact h₁ y hy) h₂ h₃
  | iteFalse =>
    obtain ⟨h₁, h₂, h₃⟩ := top hna
    exact segsNoAwait_cons (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · trivial
      · exact h₁ y hy) h₂ h₃
  | transition => obtain ⟨h₁, h₂, h₃⟩ := top hna; exact segsNoAwait_cons h₁ h₂ h₃
  | downgrade => obtain ⟨h₁, h₂, h₃⟩ := top hna; exact segsNoAwait_cons h₁ h₂ h₃
  | clock => obtain ⟨h₁, h₂, h₃⟩ := top hna; exact segsNoAwait_cons h₁ h₂ h₃
  | matchSt =>
    obtain ⟨h₁, h₂, h₃⟩ := top hna
    exact segsNoAwait_cons (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · trivial
      · exact h₁ y hy) h₂ h₃
  | call =>
    obtain ⟨h₁, h₂, h₃⟩ := top hna
    refine segsNoAwait_cons (fun y hy => ?_) (fun a ha => ?_) h₃
    · rcases List.mem_cons.1 hy with rfl | hy
      · trivial
      · cases hy
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact h₁
      · exact h₂ a ha
  | ret =>
    have h' := hna
    refine segsNoAwait_cons (fun y hy => ?_) (fun a ha => ?_) (fun s hs => ?_)
    · exact h' _ (List.mem_cons_self ..) _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) y hy
    · exact h' _ (List.mem_cons_self ..) a (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha))
    · exact h' s (List.mem_cons_of_mem _ hs)
  | async => obtain ⟨h₁, h₂, h₃⟩ := top hna; exact segsNoAwait_cons h₁ h₂ h₃
  | awaitWait => exact absurd (hd hna) id

/-- Without waiting `await`s, a machine step is a plain step (draining changes nothing). -/
theorem MStep.toStep {c c' : Config K St R} {q : R} (h : MStep P M Ψd A c q c')
    (hna : SegsNoAwait c.segs) : ∃ tick, Step P M Ψd A c q tick c' := by
  obtain ⟨tick, c₁, hs, rfl⟩ := h
  cases tick
  · exact ⟨false, hs⟩
  · exact ⟨true, by simpa [Config.drain_eq_self (hs.noAwait_of_tick hna)] using hs⟩

end StepsN

/-! ### The converse correspondence -/

/-- Every device an activation's handle map reaches, if it holds a peripheral, is the device of
a visible handle with the same entry.  Together with `Corr` this makes the machine's view and
`Eval`'s view of an activation identical. -/
def Rev (H : Var → Option Dev) (D S : RPeriphs K St) : Prop :=
  ∀ x d, H x = some d → D d ≠ 0 → D d = S x

section Rev

variable {H : Var → Option Dev} {D S : RPeriphs K St} {Am Ae : Multiset (K × St)}

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
/-- A peripheral the machine finds through `H` is visible to `Eval` in the same state. -/
theorem Rev.lookup (hR : Rev H D S) {p d : Var} {k : K} {s : St} (hH : H p = some d)
    (hD : D d = .at k s) : S p = .at k s := by
  rw [← hD]; exact (hR p d hH (by rw [hD]; exact REntry.at_ne_zero)).symm

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
/-- Moving a peripheral preserves `Rev`. -/
theorem Rev.set (hR : Rev H D S) (hC : Corr H D S Am Ae) {p d : Var} {k : K} {s : St}
    (hS : S p = .at k s) (hH : H p = some d) (hD : D d = .at k s) (st : St) :
    Rev H (D.set d k st) (S.set p k st) := by
  have hpv : S p ≠ 0 := by rw [hS]; exact REntry.at_ne_zero
  intro x d' hx hne
  by_cases hd : d' = d
  · subst hd
    have hxv : S x ≠ 0 := by
      rw [← hR x d' hx (by rw [hD]; exact REntry.at_ne_zero)]
      rw [hD]; exact REntry.at_ne_zero
    have hxp : x = p := hC.inj x p d' hxv hpv hx hH
    subst hxp
    simp
  · have hne' : D d' ≠ 0 := by simpa [RPeriphs.set_apply, hd] using hne
    have hxp : x ≠ p := fun h => hd (Option.some.inj (hx.symm.trans (h ▸ hH)))
    simp only [RPeriphs.set_apply, hd, hxp, ↓reduceIte]
    exact hR x d' hx hne'

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
/-- The callee's handle map reaches only its parameter's device. -/
theorem Rev.call {d q : Var} {k : K} {s : St} (hD : D d = .at k s) :
    Rev (fun y => if y = q then some d else none) D (Finsupp.single q (.at k s)) := by
  intro x d' hx _
  by_cases hxq : x = q
  · subst hxq
    simp only [↓reduceIte, Option.some.injEq] at hx
    subst hx; simp [hD]
  · simp [hxq] at hx

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
/-- After the call, the caller's view again covers everything its handles reach. -/
theorem Rev.ret (hR : Rev H D S) (hC : Corr H D S Am Ae) {p d : Var} {k : K} {s s' : St}
    (hS : S p = .at k s) (hH : H p = some d) {Db : RPeriphs K St} (hDb : Db d = .at k s')
    (hframe : ∀ dv, dv ≠ d → Db dv = D dv) : Rev H Db (S.set p k s') := by
  have hpv : S p ≠ 0 := by rw [hS]; exact REntry.at_ne_zero
  intro x d' hx hne
  by_cases hd : d' = d
  · subst hd
    have hD : D d' = .at k s := by
      obtain ⟨d₀, h₁, h₂⟩ := hC.lookup hS; rw [hH] at h₁; cases h₁; exact h₂
    have hxv : S x ≠ 0 := by
      rw [← hR x d' hx (by rw [hD]; exact REntry.at_ne_zero), hD]; exact REntry.at_ne_zero
    have hxp : x = p := hC.inj x p d' hxv hpv hx hH
    subst hxp; simp [hDb]
  · have hxp : x ≠ p := fun h => hd (Option.some.inj (hx.symm.trans (h ▸ hH)))
    rw [hframe d' hd] at hne ⊢
    simp only [RPeriphs.set_apply, hxp, ↓reduceIte]
    exact hR x d' hx hne

end Rev

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
/-- An entry of kind `k` is a peripheral of kind `k` in some state. -/
theorem REntry.eq_at_of_kind {e : REntry K St} {k : K} (h : e.kind = some k) :
    ∃ s, e = .at k s := by
  rcases e with _ | ⟨k', s⟩
  · cases h
  · cases h; exact ⟨s, rfl⟩

omit [DecidableEq St] [CommSemiring R] [LinearOrder R] in
omit [Sub R] in
/-- No thread exists, so nothing can be scheduled and no hardware step can happen. -/
theorem no_thread {pool : ThreadId → Option (PoolEntry St R)} (hpool : ∀ id, pool id = none)
    {id : ThreadId} {e : PoolEntry St R} (h : pool id = some e) : False := by
  rw [hpool] at h; cases h

section Charges

variable {H : Var → Option Dev} {D S : RPeriphs K St} {Am Ae : Multiset (K × St)}

omit [DecidableEq St] [LinearOrder R] in
omit [Sub R] in
/-- A step charging `K·(x + bg)` costs the same in both views. -/
theorem Corr.charge_eq (hC : Corr H D S Am Ae) (M : CostModel K St R) (Kc x : R) :
    Kc * (x + S.bg M + ambBg M Ae) = Kc * (x + D.bg M + ambBg M Am) := by
  rw [add_assoc, add_assoc, hC.bg_eq M]

omit [DecidableEq St] [LinearOrder R] in
omit [Sub R] in
/-- A step moving one peripheral costs the same in both views. -/
theorem Corr.charge_erase_eq (hC : Corr H D S Am Ae) (M : CostModel K St R) (Kc x : R)
    {p d : Var} {k : K} {s : St} (hS : S p = .at k s) (hD : D d = .at k s) :
    Kc * (x + (S.erase p).bg M + ambBg M Ae) = Kc * (x + (D.erase d).bg M + ambBg M Am) := by
  rw [add_assoc, add_assoc, hC.erase_bg M hS hD]

end Charges

/-! ### The simulation -/

/-- **Adequacy (reverse).**  Take a complete machine run that starts by executing a synchronous
command `c` in an activation corresponding (`Corr`, `Rev`) to an `Eval` view, with no threads
and no waiting timers.  Then the run first executes `c` alone, as an `Eval` run with the same
cost, final memory and clock, arriving at the configuration with `c` popped; the rest of the
run continues from there.  Proof: strong induction on the number of steps; with no threads,
the first step of each command is determined. -/
theorem StepsN.toEval {P : Platform K St} {M : CostModel K St R} {Ψd : FCtx K St R}
    (hΨ : ∀ g d, Ψd g = some d → d.body.Sync) (n : Nat) :
    ∀ (c : Cmd St R), c.Sync →
    ∀ {σ : Mem} {S : RPeriphs K St} {Ae Am : Multiset (K × St)} {H : Var → Option Dev}
      {D : RPeriphs K St} {o : Option ThreadId} {T : Var → Option ThreadId}
      {ctl : List (Ctl St R)} {r : Option (Expr × Var)} {as : List (Act St R)}
      {ss : List (Seg St R)} {pool : ThreadId → Option (PoolEntry St R)} {Kc q : R}
      {Cf : Config K St R},
    StepsN P M Ψd Am n ⟨⟨o, ⟨σ, H, T, .cmd c :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩ q Cf →
    Cf.Final → Corr H D S Am Ae → Rev H D S → (∀ id, pool id = none) →
    CtlNoAwait ctl → ActsNoAwait as → SegsNoAwait ss →
    ∃ σ' S' q₁ K' D' m q₂, Eval M Ψd Ae σ S Kc c σ' S' q₁ K' ∧ m < n ∧
      StepsN P M Ψd Am m ⟨⟨o, ⟨σ', H, T, ctl, r⟩ :: as⟩ :: ss, pool, D', K'⟩ q₂ Cf ∧
      q = q₁ + q₂ ∧ Corr H D' S' Am Ae ∧ Rev H D' S' ∧ Frame S H D D' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hc σ S Ae Am H D o T ctl r as ss pool Kc q Cf hrun hfin hC hR hpool hctl has hss
  have hna : SegsNoAwait (⟨o, ⟨σ, H, T, .cmd c :: ctl, r⟩ :: as⟩ :: ss : List (Seg St R)) :=
    segsNoAwait_cons (fun x hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · trivial
      · exact hctl x hx) has hss
  cases hrun with
  | refl =>
    exfalso
    obtain ⟨_, _, _, h⟩ := hfin
    simp at h
  | @step m _ q₀ c₁ q' _ hm hrest =>
  obtain ⟨tick, hstep⟩ := hm.toStep hna
  cases c with
  | skip =>
    cases hstep
    all_goals try first
      | (exfalso; simp only [hpool, reduceCtorEq] at *; done)
      | (exfalso; simp [SegsNoAwait, ActsNoAwait, CtlNoAwait, Ctl.IsCmd] at hss; done)
    exact ⟨σ, S, 0, Kc, D, m, q', .skip, Nat.lt_succ_self m, hrest, rfl, hC, hR,
      fun _ _ => rfl⟩
  | assign x e =>
    cases hstep
    all_goals try first
      | (exfalso; simp only [hpool, reduceCtorEq] at *; done)
      | (exfalso; simp [SegsNoAwait, ActsNoAwait, CtlNoAwait, Ctl.IsCmd] at hss; done)
    rename_i v h₁
    have hev : e.eval σ = some v := by assumption
    refine ⟨σ.set x v, S, _, Kc, D, m, q', .assign hev, Nat.lt_succ_self m, hrest, ?_, hC, hR,
      fun _ _ => rfl⟩
    rw [hC.charge_eq M Kc (e.cost M)]
  | ite e c₁' c₂' =>
    simp only [Cmd.Sync] at hc
    cases hstep
    all_goals try first
      | (exfalso; simp only [hpool, reduceCtorEq] at *; done)
      | (exfalso; simp [SegsNoAwait, ActsNoAwait, CtlNoAwait, Ctl.IsCmd] at hss; done)
    · rename_i hev
      obtain ⟨σ', S', q₁, K', D', m', q₂, hE, hm', hrun', hq, hC', hR', hF⟩ :=
        ih m (Nat.lt_succ_self m) c₁' hc.1 hrest hfin hC hR hpool hctl has hss
      refine ⟨σ', S', _, K', D', m', q₂, .iteTrue hev hE, by omega, hrun', ?_, hC', hR', hF⟩
      rw [hq, hC.charge_eq M Kc (e.cost M)]
      ac_rfl
    · rename_i hev
      obtain ⟨σ', S', q₁, K', D', m', q₂, hE, hm', hrun', hq, hC', hR', hF⟩ :=
        ih m (Nat.lt_succ_self m) c₂' hc.2 hrest hfin hC hR hpool hctl has hss
      refine ⟨σ', S', _, K', D', m', q₂, .iteFalse hev hE, by omega, hrun', ?_, hC', hR', hF⟩
      rw [hq, hC.charge_eq M Kc (e.cost M)]
      ac_rfl
  | transition p st =>
    cases hstep
    all_goals try first
      | (exfalso; simp only [hpool, reduceCtorEq] at *; done)
      | (exfalso; simp [SegsNoAwait, ActsNoAwait, CtlNoAwait, Ctl.IsCmd] at hss; done)
    rename_i d k s h₁ h₂
    have hH : H p = some d := by assumption
    have hD : D d = .at k s := by assumption
    have hSp := hR.lookup hH hD
    obtain ⟨hC', hF⟩ := hC.set hSp hH hD st
    refine ⟨σ, _, _, Kc, _, m, q', .transition hSp, Nat.lt_succ_self m, hrest, ?_, hC',
      hR.set hC hSp hH hD st, hF⟩
    rw [hC.charge_erase_eq M Kc _ hSp hD]
  | downgrade p st =>
    cases hstep
    all_goals try first
      | (exfalso; simp only [hpool, reduceCtorEq] at *; done)
      | (exfalso; simp [SegsNoAwait, ActsNoAwait, CtlNoAwait, Ctl.IsCmd] at hss; done)
    rename_i d k s h₁ h₂
    have hH : H p = some d := by assumption
    have hD : D d = .at k s := by assumption
    have hSp := hR.lookup hH hD
    obtain ⟨hC', hF⟩ := hC.set hSp hH hD st
    refine ⟨σ, _, _, Kc, _, m, q', .downgrade hSp, Nat.lt_succ_self m, hrest, ?_, hC',
      hR.set hC hSp hH hD st, hF⟩
    rw [hC.charge_erase_eq M Kc _ hSp hD]
  | clock f' =>
    cases hstep
    all_goals try first
      | (exfalso; simp only [hpool, reduceCtorEq] at *; done)
      | (exfalso; simp [SegsNoAwait, ActsNoAwait, CtlNoAwait, Ctl.IsCmd] at hss; done)
    refine ⟨σ, S, _, f', D, m, q', .clock, Nat.lt_succ_self m, hrest, ?_, hC, hR,
      fun _ _ => rfl⟩
    rw [hC.bg_eq M]
  | seq c₁' c₂' =>
    simp only [Cmd.Sync] at hc
    cases hstep
    all_goals try first
      | (exfalso; simp only [hpool, reduceCtorEq] at *; done)
      | (exfalso; simp [SegsNoAwait, ActsNoAwait, CtlNoAwait, Ctl.IsCmd] at hss; done)
    have hctl₂ : CtlNoAwait (.cmd c₂' :: ctl) := fun x hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · trivial
      · exact hctl x hx
    obtain ⟨σ₁, S₁, q₁, K₁, D₁, m₁, q₂, hE₁, hm₁, hrun₁, hq₁, hC₁, hR₁, hF₁⟩ :=
      ih m (Nat.lt_succ_self m) c₁' hc.1 hrest hfin hC hR hpool hctl₂ has hss
    obtain ⟨σ₂, S₂, q₃, K₂, D₂, m₂, q₄, hE₂, hm₂, hrun₂, hq₂, hC₂, hR₂, hF₂⟩ :=
      ih m₁ (by omega) c₂' hc.2 hrun₁ hfin hC₁ hR₁ hpool hctl has hss
    refine ⟨σ₂, S₂, _, K₂, D₂, m₂, q₄, .seq hE₁ hE₂, by omega, hrun₂, ?_, hC₂, hR₂,
      fun dv hdv => ?_⟩
    · rw [hq₁, hq₂, zero_add, add_assoc]
    · rw [hF₂ dv fun x hx => hdv x ((hE₁.ne_zero_iff x).1 hx), hF₁ dv hdv]
  | matchSt p arms =>
    simp only [Cmd.Sync] at hc
    cases hstep
    all_goals try first
      | (exfalso; simp only [hpool, reduceCtorEq] at *; done)
      | (exfalso; simp [SegsNoAwait, ActsNoAwait, CtlNoAwait, Ctl.IsCmd] at hss; done)
    rename_i d k s c h₁ h₂ h₃
    have hH : H p = some d := by assumption
    have hD : D d = .at k s := by assumption
    have hf : arms.find? s = some c := by assumption
    have hSp := hR.lookup hH hD
    obtain ⟨σ', S', q₁, K', D', m', q₂, hE, hm', hrun', hq, hC', hR', hF⟩ :=
      ih m (Nat.lt_succ_self m) c (hc.find hf) hrest hfin hC hR hpool hctl has hss
    refine ⟨σ', S', _, K', D', m', q₂, .matchSt hSp hf hE, by omega, hrun', ?_, hC', hR', hF⟩
    rw [hq, hC.bg_eq M]
    ac_rfl
  | call x g e p =>
    cases hstep
    all_goals try first
      | (exfalso; simp only [hpool, reduceCtorEq] at *; done)
      | (exfalso; simp [SegsNoAwait, ActsNoAwait, CtlNoAwait, Ctl.IsCmd] at hss; done)
    rename_i dcl v d k s h₁ h₂ h₃ h₄
    have hg : Ψd g = some dcl := by assumption
    have hev : e.eval σ = some v := by assumption
    have hH : H p = some d := by assumption
    have hD : D d = .at k s := by assumption
    have hSp := hR.lookup hH hD
    -- the body runs first, on top of the caller
    obtain ⟨σb, Sb, qb, Kb, Db, m₁, q₂, hEb, hm₁, hrun₁, hqb, hCb, hRb, hFb⟩ :=
      ih m (Nat.lt_succ_self m) dcl.body (hΨ g dcl hg) hrest hfin (hC.call hSp hD dcl.parg)
        (Rev.call hD) hpool (fun _ h => by cases h)
        (fun a ha => by
          rcases List.mem_cons.1 ha with rfl | ha
          · exact hctl
          · exact has a ha) hss
    -- then the return step
    have hna₁ : SegsNoAwait (⟨o, ⟨σb, fun y => if y = dcl.parg then some d else none,
        fun _ => none, [], some (dcl.ret, x)⟩ :: ⟨σ, H, T, ctl, r⟩ :: as⟩ :: ss :
          List (Seg St R)) := by
      refine segsNoAwait_cons (fun _ h => by cases h) (fun a ha => ?_) hss
      rcases List.mem_cons.1 ha with rfl | ha
      · exact hctl
      · exact has a ha
    cases hrun₁ with
    | refl =>
      exfalso
      obtain ⟨_, _, _, h⟩ := hfin
      simp at h
    | @step m₂ _ q₃ c₃ q₄ _ hm₂ hrest₂ =>
    obtain ⟨tick₂, hstep₂⟩ := hm₂.toStep hna₁
    cases hstep₂
    all_goals try first
      | (exfalso; simp only [hpool, reduceCtorEq] at *; done)
      | (exfalso; simp [SegsNoAwait, ActsNoAwait, CtlNoAwait, Ctl.IsCmd] at hss; done)
    rename_i rv h₅
    have hret : dcl.ret.eval σb = some rv := by assumption
    -- the callee's final peripheral state
    obtain ⟨s', hSb⟩ := REntry.eq_at_of_kind (k := k) (by
      rw [hEb.kind_eq dcl.parg]; simp [REntry.kind])
    have hzero : ∀ y, y ≠ dcl.parg → Sb y = 0 := by
      intro y hy
      by_contra hne
      exact (hEb.ne_zero_iff y).1 hne (Finsupp.single_eq_of_ne hy)
    obtain ⟨hC', hF⟩ := hC.ret hSp hH hCb hSb hzero hFb
    have hDb : Db d = .at k s' := by
      obtain ⟨d', h₁, h₂⟩ := hCb.lookup hSb
      simp only [↓reduceIte, Option.some.injEq] at h₁
      rw [h₁]; exact h₂
    have hframe : ∀ dv, dv ≠ d → Db dv = D dv := by
      intro dv hne
      refine hFb dv fun y hy => ?_
      have hyq : y = dcl.parg := by
        by_contra h; exact hy (Finsupp.single_eq_of_ne h)
      simp [hyq, Ne.symm hne]
    refine ⟨σ.set x rv, S.set p k s', _, Kb, Db, m₂, q₄, .call hg hev hSp hEb hret hSb,
      by omega, hrest₂, ?_, hC', hR.ret hC hSp hH hDb hframe, hF⟩
    rw [hqb, hC.charge_eq M Kc (e.cost M), ← hCb.charge_eq M Kb (dcl.ret.cost M)]
    ac_rfl
  | async tid p c' => exact absurd hc id
  | await tid n' fb => exact absurd hc id

/-- **Adequacy for whole programs (reverse).**  Every complete machine run of a synchronous
program (synchronous `main` and function bodies) is a big-step run with the same cost.  So the
cost soundness, accounting and slack results proved for `Eval` hold for the machine on the
synchronous fragment. -/
theorem Program.MRun.toEval {P : Platform K St} {M : CostModel K St R} {prog : Program K St R}
    (hmain : prog.main.Sync) (hΨ : ∀ g d, prog.fctx g = some d → d.body.Sync)
    {K₀ q : R} {c : Config K St R} (h : prog.MRun P M K₀ c q) :
    ∃ σ' S' K', prog.Eval M K₀ σ' S' q K' := by
  obtain ⟨hrun, hfin⟩ := h
  obtain ⟨n, hn⟩ := hrun.toN
  have hC : Corr some prog.initPeriphs prog.initPeriphs 0 0 :=
    ⟨fun x _ => ⟨x, rfl, rfl⟩, fun _ _ _ _ _ hx hy => Option.some.inj (hx.trans hy.symm), rfl⟩
  have hR : Rev some prog.initPeriphs prog.initPeriphs := by
    intro x d hx _; cases hx; rfl
  obtain ⟨σ', S', q₁, K', D', m, q₂, hE, _, hrest, hq, -, -, -⟩ :=
    StepsN.toEval hΨ n prog.main hmain hn hfin hC hR (fun _ => rfl) (fun _ h => by cases h)
      (fun _ h => by cases h) (fun _ h => by cases h)
  -- the rest of the run starts final, so it is empty
  have hq₂ : q₂ = 0 := by
    cases hrest with
    | refl => rfl
    | step hm _ =>
      exfalso
      obtain ⟨tick, hs⟩ := hm.toStep (fun s hs => by
        simp at hs; subst hs; intro a ha; simp at ha; subst ha; intro x hx; cases hx)
      cases hs <;> simp_all
  exact ⟨σ', S', K', by rw [hq, hq₂, add_zero]; exact hE⟩

/-- **Cost soundness on the machine (synchronous programs).**  A well-typed synchronous program
run to completion on the machine from clock `K₀` costs at most `Q K₀ 0`: by reverse adequacy the
run is an `Eval` run, and `Program.soundness` bounds those. -/
theorem Program.MRun.soundness [DecidableEq K] [OrderBot R] [IsOrderedRing R]
    [CanonicallyOrderedAdd R] {P : Platform K St} {M : CostModel K St R} (hM : M.WF)
    {prog : Program K St R} {Ψ : SigCtx K St R} {Γ' : TCtx K} {Δ' : PCtx K St}
    {Q : R → R → R} {F : R → R} (ht : prog.Typed P M Ψ Γ' Δ' Q F)
    (hmain : prog.main.Sync) (hΨ : ∀ g d, prog.fctx g = some d → d.body.Sync)
    {K₀ q : R} {c : Config K St R} (h : prog.MRun P M K₀ c q) : q ≤ Q K₀ 0 := by
  obtain ⟨σ', S', K', he⟩ := h.toEval hmain hΨ
  exact Program.soundness hM ht he
