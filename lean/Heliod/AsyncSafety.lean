import Heliod.AsyncProgram

/-!
# Async type safety on the machine

Preservation is `CfgTyped.mstep`: a typed configuration steps to a typed configuration.  This
file proves **progress**: a typed configuration is final or can take a machine step.

* `progress_head` — the running activation's next control entry: a local command or a call
  steps (expressions evaluate, devices are found, a `match` finds its arm, the callee is
  declared); otherwise it is a spawn, an `await` or a waiting frame.
* `StackOK.progress` — a typed stack has finished (a single bottom activation with nothing to
  do), can step its running activation, or is at a spawn / `await` / waiting frame.
* `CfgTyped.fresh` — a typed configuration has a free runtime thread id (the pool's entries
  are reached from finitely many pending threads).
* `CfgTyped.progress` — the top segment steps: a thread runs or finishes; `main` runs, spawns,
  starts an `await`, waits, joins a finished thread or times out.
* `Program.typeSafetyA` — every configuration a well-typed program reaches is final or can step.
-/

set_option linter.unusedSectionVars false

variable {K St R : Type} [DecidableEq K] [DecidableEq St]
variable [CommSemiring R] [LinearOrder R] [OrderBot R] [Sub R]
variable [IsOrderedRing R] [CanonicallyOrderedAdd R] [OrderedSub R]
variable {P : Platform K St} {M : CostModel K St R} {Ψ : SigCtxA K St R}

/-- A handle typed live names a device holding a state of its set. -/
theorem ActOK.device {Γ : TCtx K} {Δ : PCtx K St} {b : R} {σ : Mem} {H : Var → Option Dev}
    {D : RPeriphs K St} {Am : Multiset (K × St)} (h : ActOK M Γ Δ b σ H D Am) {p : Var} {k : K}
    {T : Finset St} (hp : Δ p = .live k T) : ∃ d s, H p = some d ∧ D d = .at k s ∧ s ∈ T := by
  obtain ⟨_, S, _, hC, _, hS, _⟩ := h
  obtain ⟨s, hSp, hs⟩ := hS.live hp
  obtain ⟨d, hH, hD⟩ := hC.lookup hSp
  exact ⟨d, s, hH, hD, hs⟩

/-- **The running activation's next entry**: a local command or a call can step (its
expression evaluates, its device holds a peripheral, a `match` has an arm for the device's
state, a callee is declared); otherwise the entry is a spawn, an `await` or a waiting frame. -/
theorem progress_head {Ψd : FCtx K St R} (hΨd : SigsDerivedA P M Ψd Ψ) {Am : Multiset (K × St)}
    {C : PCtx K St → Prop} {cl : Bool} {fz Γ Δ Θ} {x : Ctl St R} {ctl : List (Ctl St R)}
    {Γf Δf Θf Q F} (hct : CtlTyped P M Ψ C cl fz Γ Δ Θ (x :: ctl) Γf Δf Θf Q F)
    {b : R} {σ : Mem} {H : Var → Option Dev} {D : RPeriphs K St} (hok : ActOK M Γ Δ b σ H D Am)
    {T : Var → Option ThreadId} {r : Option (Expr × Var)} {as : List (Act St R)} {Kc : R} :
    (∃ q tick as' D' K', TopOK (⟨σ, H, T, x :: ctl, r⟩ :: as) ∧
      ActStep M Ψd Am (⟨σ, H, T, x :: ctl, r⟩ :: as) D Kc q tick as' D' K') ∨
    (∃ tid p cb, x = .cmd (.async tid p cb)) ∨ (∃ tid n fb, x = .cmd (.await tid n fb)) ∨
    (∃ tid id rem fb, x = .awaitW tid id rem fb) := by
  cases x with
  | awaitW tid id rem fb => exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, rfl⟩))
  | cmd c =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := hct.cons_inv
    cases c with
    | async tid p cb => exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
    | await tid n fb => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩))
    | skip => exact Or.inl ⟨_, _, _, _, _, TopOK.cmd (Or.inl trivial), .skip⟩
    | seq c₁ c₂ => exact Or.inl ⟨_, _, _, _, _, TopOK.cmd (Or.inl trivial), .seq⟩
    | assign x e =>
      cases hc with
      | assign hty _ =>
        obtain ⟨v, hv, _⟩ := HasTy.eval hok.1 hty
        exact Or.inl ⟨_, _, _, _, _, TopOK.cmd (Or.inl trivial), .assign hv⟩
    | ite e c₁ c₂ =>
      cases hc with
      | ite hty _ _ _ =>
        obtain ⟨v, hv, hvt⟩ := HasTy.eval hok.1 hty
        obtain ⟨bv, rfl⟩ := Val.eq_bool_of_ty hvt
        cases bv
        · exact Or.inl ⟨_, _, _, _, _, TopOK.cmd (Or.inl trivial), .iteFalse hv⟩
        · exact Or.inl ⟨_, _, _, _, _, TopOK.cmd (Or.inl trivial), .iteTrue hv⟩
    | transition p st =>
      cases hc with
      | transition hp =>
        obtain ⟨d, s, hH, hD, _⟩ := hok.device hp
        exact Or.inl ⟨_, _, _, _, _, TopOK.cmd (Or.inl trivial), .transition hH hD⟩
      | transitionU hp =>
        obtain ⟨d, s, hH, hD, _⟩ := hok.device hp
        exact Or.inl ⟨_, _, _, _, _, TopOK.cmd (Or.inl trivial), .transition hH hD⟩
    | downgrade p st =>
      cases hc with
      | downgrade hp =>
        obtain ⟨d, s, hH, hD, _⟩ := hok.device hp
        exact Or.inl ⟨_, _, _, _, _, TopOK.cmd (Or.inl trivial), .downgrade hH hD⟩
    | clock f' => exact Or.inl ⟨_, _, _, _, _, TopOK.cmd (Or.inl trivial), .clock⟩
    | matchSt p arms =>
      cases hc with
      | matchSt hp _ hsub =>
        obtain ⟨d, s, hH, hD, hs⟩ := hok.device hp
        obtain ⟨c, hf⟩ := Arms.find?_of_mem (hsub hs)
        exact Or.inl ⟨_, _, _, _, _, TopOK.cmd (Or.inl trivial), .matchSt hH hD hf⟩
    | call x g e p =>
      cases hc with
      | call hg hty _ hp =>
        obtain ⟨dcl, hgd, _⟩ := hΨd g _ hg
        obtain ⟨v, hv, _⟩ := HasTy.eval hok.1 hty
        obtain ⟨d, s, hH, hD, _⟩ := hok.device hp
        exact Or.inl ⟨_, _, _, _, _, TopOK.cmd (Or.inr ⟨_, _, _, _, rfl⟩), .call hgd hv hH hD⟩

/-- `progress_head` for any control stack: it is empty, or its head steps, or its head is a
spawn, an `await` or a waiting frame.  (Used by `StackOK.progress`, where the control stack is
not named.) -/
theorem progress_ctl {Ψd : FCtx K St R} (hΨd : SigsDerivedA P M Ψd Ψ) {Am : Multiset (K × St)}
    {C : PCtx K St → Prop} {cl : Bool} {fz Γ Δ Θ} {ctl : List (Ctl St R)}
    {Γf Δf Θf Q F} (hct : CtlTyped P M Ψ C cl fz Γ Δ Θ ctl Γf Δf Θf Q F)
    {b : R} {σ : Mem} {H : Var → Option Dev} {D : RPeriphs K St} (hok : ActOK M Γ Δ b σ H D Am)
    {T : Var → Option ThreadId} {r : Option (Expr × Var)} {as : List (Act St R)} {Kc : R} :
    ctl = [] ∨
    (∃ q tick as' D' K', TopOK (⟨σ, H, T, ctl, r⟩ :: as) ∧
      ActStep M Ψd Am (⟨σ, H, T, ctl, r⟩ :: as) D Kc q tick as' D' K') ∨
    (∃ x ctl', ctl = x :: ctl' ∧ ((∃ tid p cb, x = .cmd (.async tid p cb)) ∨
      (∃ tid n fb, x = .cmd (.await tid n fb)) ∨ (∃ tid id rem fb, x = .awaitW tid id rem fb))) := by
  cases ctl with
  | nil => exact Or.inl rfl
  | cons x ctl =>
    rcases progress_head hΨd hct hok (T := T) (r := r) (as := as) (Kc := Kc) with hs | hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr ⟨_, _, rfl, hs⟩)

/-- **Progress for a typed stack**: it has finished (one bottom activation with nothing left
to do), or its running activation can step (a callee that has finished returns: its return
expression evaluates), or the running activation is at a spawn, an `await` or a waiting
frame. -/
theorem StackOK.progress {Ψd : FCtx K St R} (hΨd : SigsDerivedA P M Ψd Ψ)
    {Am : Multiset (K × St)} {E : Option (DevEnv St)} {as D Kc Φ X Θ Δ b bb tv Vs}
    (h : StackOK P M Ψ Am E as D Kc Φ X Θ Δ b bb tv Vs) :
    (∃ σ H T, as = [⟨σ, H, T, [], none⟩]) ∨
    (∃ q tick as' D' K', TopOK as ∧ ActStep M Ψd Am as D Kc q tick as' D' K') ∨
    (∃ σ H T x ctl r tl, as = ⟨σ, H, T, x :: ctl, r⟩ :: tl ∧
      ((∃ tid p cb, x = .cmd (.async tid p cb)) ∨ (∃ tid n fb, x = .cmd (.await tid n fb)) ∨
        (∃ tid id rem fb, x = .awaitW tid id rem fb))) := by
  cases h with
  | base hct _ _ hok =>
    rcases progress_ctl hΨd hct hok (as := []) (Kc := Kc) with rfl | hs | ⟨x, ctl, rfl, hs⟩
    · exact Or.inl ⟨_, _, _, rfl⟩
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr ⟨_, _, _, _, _, _, _, rfl, hs⟩)
  | push hct _ hok _ _ _ _ _ _ _ hret =>
    rcases progress_ctl hΨd hct hok (Kc := Kc) with rfl | hs | ⟨x, ctl, rfl, hs⟩
    · cases hct
      obtain ⟨v, hv, _⟩ := HasTy.eval hok.1 hret
      exact Or.inr (Or.inl ⟨_, _, _, _, _, TopOK.nil, .ret hv⟩)
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr ⟨_, _, _, _, _, _, _, rfl, hs⟩)

/-- **A typed configuration has a free runtime thread id**: every pool entry is reached from
one of finitely many pending threads, so an id beyond all of theirs is free. -/
theorem CfgTyped.fresh {Am : Multiset (K × St)} {c : Config K St R} {Φ : R}
    (hc : CfgTyped P M Ψ Am c Φ) : ∃ id, c.pool id = none := by
  obtain ⟨_, _, _, _, _, _, _, _, _, tv, _, tids, _, _, _, _, _, _, _, hpool, _⟩ := hc
  refine ⟨tids.sup (fun t => (tv.T t).getD 0) + 1, ?_⟩
  rcases he : c.pool _ with _ | e
  · rfl
  · obtain ⟨t, ht, hT⟩ := hpool _ e he
    have hle : (tv.T t).getD 0 ≤ tids.sup (fun t => (tv.T t).getD 0) := Finset.le_sup (f := fun t => (tv.T t).getD 0) ht
    rw [hT, Option.getD_some] at hle
    exact absurd hle (Nat.not_succ_le_self _)

/-- The top segment's running activation and typing, when `main` is on top. -/
theorem StackOK.head_typed {E : Option (DevEnv St)} {Am : Multiset (K × St)} {σ : Mem}
    {H : Var → Option Dev} {T : Var → Option ThreadId} {ctl : List (Ctl St R)}
    {r : Option (Expr × Var)} {tl D Kc Φ X Θ Δ b bb tv Vs}
    (h : StackOK P M Ψ Am E (⟨σ, H, T, ctl, r⟩ :: tl) D Kc Φ X Θ Δ b bb tv Vs) :
    ∃ (C : PCtx K St → Prop) (fz : Bool) (Γ : TCtx K), ∃ Γf Δf Θf Q F,
      CtlTyped P M Ψ C E.isSome fz Γ Δ Θ ctl Γf Δf Θf Q F ∧ ActOK M Γ Δ b σ H D Am := by
  cases h with
  | base hct _ _ hok => exact ⟨_, _, _, _, _, _, _, _, hct, hok⟩
  | push hct _ hok => exact ⟨_, _, _, _, _, _, _, _, hct, hok⟩

/-- **Progress for typed configurations**: a typed configuration that is not final can take a
machine step.  A thread on top runs its activation or, having finished, is marked done (spawns
and `await`s cannot occur in threads, nor waiting frames).  `main` on top runs its activation;
at a spawn its device is found and a fresh thread id exists; at an `await` its thread has a
runtime id; at a waiting frame its thread is pending (wait or time out, by the budget), or
done (join) — it cannot be running, since no thread segment is above `main`. -/
theorem CfgTyped.progress {Ψd : FCtx K St R} (hΨd : SigsDerivedA P M Ψd Ψ)
    {Am : Multiset (K × St)} {c : Config K St R} {Φ : R} (hc : CfgTyped P M Ψ Am c Φ)
    (hnf : ¬ c.Final) : ∃ q c', MStep P M Ψd Am c q c' := by
  suffices ∃ q tick c₁, Step P M Ψd Am c q tick c₁ by
    obtain ⟨q, tick, c₁, hs⟩ := this
    exact ⟨q, _, tick, c₁, hs, rfl⟩
  have hfresh := hc.fresh
  obtain ⟨segs, pool, D, Kc⟩ := c
  have hc₀ := hc
  obtain ⟨tsegs, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, hsegs, hst, htids, hthr, hdist,
    hown, hpool, hnaT, hnaM, hnaH, haw, rfl⟩ := hc
  dsimp only at hsegs hfresh hst hthr hpool hown
  subst hsegs
  cases tsegs with
  | cons s₁ t₁ =>
    -- a thread runs on top
    obtain ⟨t, ht, id, e, hTt, hown₁, hpe, hrun⟩ := hown s₁ List.mem_cons_self
    obtain ⟨o, acts⟩ := s₁
    simp only at hown₁
    subst hown₁
    obtain ⟨_, _, _, _, _, _, _, _, _, hstk, hΘe, hna⟩ := hc₀.thread_seg (by rfl)
    rcases hstk.progress hΨd with ⟨σ, H, T, rfl⟩ | ⟨q, tick, as', D', K', _, hs⟩ |
        ⟨σ, H, T, x, ctl, r, tl, rfl, hx⟩
    · exact ⟨_, _, _, .threadDone hpe⟩
    · exact ⟨_, _, _, hs.toStep _ _ _⟩
    · rcases hx with ⟨tid, p, cb, rfl⟩ | ⟨tid, n, fb, rfl⟩ | ⟨tid, id', rem, fb, rfl⟩
      · exact hstk.no_async.elim
      · exact (hstk.no_await hΘe).elim
      · exact (hna _ List.mem_cons_self _ List.mem_cons_self).elim
  | nil =>
    -- `main` runs on top
    rcases hst.progress hΨd with ⟨σ, H, T, has⟩ | ⟨q, tick, as', D', K', _, hs⟩ |
        ⟨σ, H, T, x, ctl, r, tl, has, hx⟩
    · exact absurd ⟨σ, H, T, by rw [List.nil_append, has]⟩ hnf
    · exact ⟨_, _, _, hs.toStep _ _ _⟩
    · obtain ⟨rfl, rfl⟩ := List.cons.inj has
      rcases hx with ⟨tid, p, cb, rfl⟩ | ⟨tid, n, fb, rfl⟩ | ⟨tid, id, rem, fb, rfl⟩
      · -- a spawn: the device is found and a thread id is free
        obtain ⟨_, _, _, _, _, _, _, _, hct, hok⟩ := hst.head_typed
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := hct.cons_inv
        cases hc with
        | async hp =>
          obtain ⟨d, s, hH, hD, _⟩ := hok.device hp
          obtain ⟨id, hid⟩ := hfresh
          exact ⟨_, _, _, .async hH hD hid⟩
      · -- an `await`: the thread has a runtime id
        obtain rfl := hst.await_tv (Or.inl ⟨_, _, _, rfl⟩)
        obtain ⟨_, _, _, _, _, _, _, _, hct, _⟩ := hst.head_typed
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := hct.cons_inv
        cases hc with
        | await hth =>
          obtain ⟨_, _, id, e, hTa, _⟩ := hthr tid ((htids tid).2 (by simp [hth])) _ hth
          exact ⟨_, _, _, .awaitStart hTa⟩
      · -- a waiting frame: its thread is pending or done
        obtain rfl := hst.await_tv (Or.inr ⟨_, _, _, _, rfl⟩)
        obtain ⟨_, _, _, _, _, _, _, _, hct, _⟩ := hst.head_typed
        have hTid : T tid = some id := haw tid id rem fb rfl
        cases hct with
        | awaitW hth =>
          obtain ⟨_, _, id', e, hTa, hpe, _, _, hst'⟩ :=
            hthr tid ((htids tid).2 (by simp [hth])) _ hth
          dsimp only at hTa; rw [hTid] at hTa; cases hTa
          revert hst'
          cases hes : e.status with
          | pending =>
            intro _
            by_cases hpos : 0 < rem
            · exact ⟨_, _, _, .awaitWait hpe hes hpos⟩
            · exact ⟨_, _, _, .awaitTimeout hpe hes (not_lt.1 hpos)⟩
          | done => intro _; exact ⟨_, _, _, .awaitDone hpe hes⟩
          | running =>
            rintro ⟨_, _, _, _, _, _, _, _, hf, _⟩
            simp at hf

/-- **Type safety of async programs on the machine**: every configuration a well-typed program
reaches (for any schedule and any hardware behaviour) is final or can take a step.
Preservation is `CfgTyped.steps` (reachable configurations stay typed), progress is
`CfgTyped.progress`. -/
theorem Program.typeSafetyA (hM : M.WF) (hP : P.WF) {prog : Program K St R}
    {Ψ : SigCtxA K St R} {Γ' : TCtx K} {Δ' W : PCtx K St} {Q : R → R → R} {F : R → R}
    (ht : prog.TypedA P M Ψ Γ' Δ' W Q F) {K₀ q : R} {c : Config K St R}
    (h : Steps P M prog.fctx 0 (prog.initConfig K₀) q c) :
    c.Final ∨ ∃ q' c', MStep P M prog.fctx 0 c q' c' := by
  have hΨd := Program.sigsDerivedA ht
  obtain ⟨Φ', hc, _⟩ := CfgTyped.steps hM (Program.sigsMonoA hM ht) hP hΨd.closed hΨd h
    (Program.initCfgTyped ht K₀)
  by_cases hf : c.Final
  · exact Or.inl hf
  · exact Or.inr (hc.progress hΨd hf)
