import Heliod.AsyncConfig

/-!
# Async soundness — 3d: whole programs

`CfgTyped.steps` bounds every run of a typed configuration by its potential.  This file
connects it to programs:

* **Signature facts from declarations.**  A program's declarations are typed in order, each
  against the signatures before it; typing survives a larger signature context
  (`TypedA.weaken`), so every signature is derived from its declaration against the final
  context (`Program.sigsDerivedA`), has monotone summaries (`Program.sigsMonoA`) and
  hardware-closed exit states (`SigsDerivedA.closed`).
* **The initial configuration is typed** (`Program.initCfgTyped`): only `main`, with the
  potential `Q K₀ 0` its typing gives.
* **`Program.MRun.soundnessA`**: a well-typed program (async included), run to completion on
  the machine from clock `K₀`, costs at most `Q K₀ 0` — for every schedule and every sequence
  of hardware steps.  -/

set_option linter.unusedSectionVars false

variable {K St R : Type} [DecidableEq K] [DecidableEq St]
variable [CommSemiring R] [LinearOrder R] [OrderBot R]
variable {P : Platform K St} {M : CostModel K St R}

/-! ### Weakening the signature context -/

/-- `Ψ ≤ Ψ'`: every signature of `Ψ` is also in `Ψ'`. -/
def SigCtxA.Le (Ψ Ψ' : SigCtxA K St R) : Prop :=
  ∀ g sig, Ψ g = some sig → Ψ' g = some sig

mutual

/-- **Async typing is preserved when signatures are added** (port of `Typed.weaken`): only
T-Call consults `Ψ`, and only to look signatures up. -/
theorem TypedA.weaken {Ψ Ψ' : SigCtxA K St R} (hle : SigCtxA.Le Ψ Ψ')
    {fz Γ Δ Θ c Γ' Δ' Θ' W Q F} :
    TypedA P M Ψ fz Γ Δ Θ c Γ' Δ' Θ' W Q F → TypedA P M Ψ' fz Γ Δ Θ c Γ' Δ' Θ' W Q F
  | .skip => .skip
  | .assign h₁ h₂ => .assign h₁ h₂
  | .ite h h₁ h₂ hs => .ite h (h₁.weaken hle) (h₂.weaken hle) hs
  | .transition a b c d => .transition a b c d
  | .transitionU a b c d => .transitionU a b c d
  | .downgrade a b c d => .downgrade a b c d
  | .clock a b c => .clock a b c
  | .seq h₁ h₂ => .seq (h₁.weaken hle) (h₂.weaken hle)
  | .matchSt a b c ha => .matchSt a b c (ha.weaken hle)
  | .call hg a b c d e f => .call (hle _ _ hg) a b c d e f
  | .async a b c d e hb g h i j => .async a b c d e (hb.weaken hle) g h i j
  | .await a b c hfb e f g => .await a b c (hfb.weaken hle) e f g

/-- Arms version of `TypedA.weaken`. -/
theorem ArmsTypedA.weaken {Ψ Ψ' : SigCtxA K St R} (hle : SigCtxA.Le Ψ Ψ')
    {fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F} :
    ArmsTypedA P M Ψ fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F →
    ArmsTypedA P M Ψ' fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F
  | .last h₁ h h₂ => .last h₁ (h.weaken hle) h₂
  | .cons h₁ h ha hs => .cons h₁ (h.weaken hle) (ha.weaken hle) hs
  | .skip h₁ ha => .skip h₁ (ha.weaken hle)

end

/-- A function declaration typed against `Ψ` is typed against any larger `Ψ'`. -/
theorem FunDeclTypedA.weaken {Ψ Ψ' : SigCtxA K St R} (hle : SigCtxA.Le Ψ Ψ')
    {d : FunDecl K St R} {sig : FunSigA K St R} (hd : FunDeclTypedA P M Ψ d sig) :
    FunDeclTypedA P M Ψ' d sig :=
  ⟨hd.argTy, hd.pKind, hd.sIn, hd.retTy, hd.sOut,
    have ⟨Γb, Δb, Wb, Qb, Fb, S', Sv, hb, rest⟩ := hd.body
    ⟨Γb, Δb, Wb, Qb, Fb, S', Sv, hb.weaken hle, rest⟩, hd.sInClosed, hd.sOutClosed⟩

/-- Adding a signature under a fresh name extends the context. -/
private theorem SigCtxA.le_update {Ψ : SigCtxA K St R} {g : FName} (hg : Ψ g = none)
    (sig : FunSigA K St R) : SigCtxA.Le Ψ (Function.update Ψ g (some sig)) := by
  intro g' sig' h
  have hne : g' ≠ g := by rintro rfl; rw [hg] at h; cases h
  rw [Function.update_of_ne hne]; exact h

/-- `≤` on signature contexts is transitive. -/
private theorem SigCtxA.Le.trans {Ψ₁ Ψ₂ Ψ₃ : SigCtxA K St R} (h₁ : SigCtxA.Le Ψ₁ Ψ₂)
    (h₂ : SigCtxA.Le Ψ₂ Ψ₃) : SigCtxA.Le Ψ₁ Ψ₃ :=
  fun g sig h => h₂ g sig (h₁ g sig h)

/-- Typing distinct, fresh declarations in order only adds signatures. -/
theorem DeclsTypedA.le {Ψ₀ ds Ψ'} (hds : DeclsTypedA P M Ψ₀ ds Ψ') :
    (ds.map (·.name)).Nodup → (∀ d ∈ ds, Ψ₀ d.name = none) → SigCtxA.Le Ψ₀ Ψ' := by
  induction hds with
  | nil => intro _ _ g sig h; exact h
  | @cons Ψ d ds sig Ψ' _ _ ih =>
    intro hnd hfresh
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    refine (SigCtxA.le_update (hfresh d (List.mem_cons_self ..)) sig).trans (ih hnd.2 ?_)
    intro d' hd'
    have hne : d'.name ≠ d.name := fun he => hnd.1 ⟨d', hd', he⟩
    rw [Function.update_of_ne hne]
    exact hfresh d' (List.mem_cons_of_mem _ hd')

/-- **Declarations typed in order give derived signatures** (async version): every signature
in the final context is the one T-FunDecl derives for its declaration, typed against the final
context. -/
theorem DeclsTypedA.sigsDerived {Ψd : FCtx K St R} {Ψ₀ ds Ψ'}
    (hds : DeclsTypedA P M Ψ₀ ds Ψ') :
    (ds.map (·.name)).Nodup → (∀ d ∈ ds, Ψ₀ d.name = none) →
    (∀ d ∈ ds, Ψd d.name = some d) →
    (∀ g sig, Ψ₀ g = some sig → ∃ d, Ψd g = some d ∧ FunDeclTypedA P M Ψ' d sig) →
    SigsDerivedA P M Ψd Ψ' := by
  induction hds with
  | nil => intro _ _ _ hΨ₀; exact hΨ₀
  | @cons Ψ d ds sig Ψ' hd hrest ih =>
    intro hnd hfresh hmem hΨ₀
    have hnd' := hnd
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd'
    have hfresh' : ∀ d' ∈ ds, Function.update Ψ d.name (some sig) d'.name = none := by
      intro d' hd'
      have hne : d'.name ≠ d.name := fun he => hnd'.1 ⟨d', hd', he⟩
      rw [Function.update_of_ne hne]
      exact hfresh d' (List.mem_cons_of_mem _ hd')
    have hle : SigCtxA.Le (Function.update Ψ d.name (some sig)) Ψ' := hrest.le hnd'.2 hfresh'
    have hle₀ : SigCtxA.Le Ψ Ψ' :=
      (SigCtxA.le_update (hfresh d (List.mem_cons_self ..)) sig).trans hle
    refine ih hnd'.2 hfresh' (fun d' hd' => hmem d' (List.mem_cons_of_mem _ hd')) ?_
    intro g sig' hg
    by_cases h : g = d.name
    · subst h
      simp only [Function.update_self, Option.some.injEq] at hg
      subst hg
      exact ⟨d, hmem d (List.mem_cons_self ..), hd.weaken hle₀⟩
    · rw [Function.update_of_ne h] at hg
      exact hΨ₀ g sig' hg

/-- A well-typed program's signatures are derived from its declarations. -/
theorem Program.sigsDerivedA {prog : Program K St R} {Ψ Γ' Δ' W Q F}
    (ht : prog.TypedA P M Ψ Γ' Δ' W Q F) : SigsDerivedA P M prog.fctx Ψ :=
  DeclsTypedA.sigsDerived ht.2.1 ht.1 (fun _ _ => rfl)
    (fun _ hd => Program.fctx_of_mem ht.1 hd) (fun _ _ h => by simp at h)

/-- Derived signatures have exit states closed under hardware steps (T-FunDecl, option A). -/
theorem SigsDerivedA.closed {Ψd : FCtx K St R} {Ψ : SigCtxA K St R}
    (h : SigsDerivedA P M Ψd Ψ) : SigsClosedA P Ψ := by
  intro g sig hg
  obtain ⟨d, _, hd⟩ := h g sig hg
  rw [hd.pKind, hd.sOut]
  exact hd.sOutClosed

/-! ### Monotone signatures -/

variable [IsOrderedRing R] [CanonicallyOrderedAdd R]

/-- **A declared signature has monotone summaries**, given monotone summaries for the
signatures its body may call: the body's summary is monotone (`TypedA.mono`), and so is the
return step `F f · (q_ret + cost(Δ_b) + b)`. -/
theorem FunDeclTypedA.mono (hM : M.WF) {Ψ : SigCtxA K St R}
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk)
    {d : FunDecl K St R} {sig : FunSigA K St R} (hd : FunDeclTypedA P M Ψ d sig) :
    SummaryMono sig.cost sig.clk := by
  obtain ⟨Γb, Δb, Wb, Qb, Fb, S', Sv, hb, _, _, _, _, _, hcost, hclk⟩ := hd.body
  obtain ⟨hF, hQ⟩ := hb.mono hM hΨ
  rw [hcost, hclk]
  exact ⟨hF, fun f f' b b' hf hb' => add_le_add (hQ _ _ _ _ hf hb')
    (mul_le_mul (hF hf) (add_le_add le_rfl hb') zero_le zero_le)⟩

/-- Declarations typed in order keep every signature's summaries monotone. -/
theorem DeclsTypedA.sigsMono (hM : M.WF) {Ψ₀ ds Ψ'} (hds : DeclsTypedA P M Ψ₀ ds Ψ') :
    (∀ g sig, Ψ₀ g = some sig → SummaryMono sig.cost sig.clk) →
    ∀ g sig, Ψ' g = some sig → SummaryMono sig.cost sig.clk := by
  induction hds with
  | nil => exact id
  | @cons Ψ d ds sig Ψ' hd _ ih =>
    intro hΨ
    refine ih fun g sig' hg => ?_
    by_cases h : g = d.name
    · subst h
      simp only [Function.update_self, Option.some.injEq] at hg
      subst hg
      exact hd.mono hM hΨ
    · rw [Function.update_of_ne h] at hg
      exact hΨ g sig' hg

/-- A well-typed program's signatures have monotone summaries. -/
theorem Program.sigsMonoA (hM : M.WF) {prog : Program K St R} {Ψ Γ' Δ' W Q F}
    (ht : prog.TypedA P M Ψ Γ' Δ' W Q F) :
    ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk :=
  ht.2.1.sigsMono hM (fun _ _ h => by simp at h)

/-! ### The initial configuration -/

variable [Sub R] [OrderedSub R]

/-- **A well-typed program's initial configuration is typed**, with potential `Q K₀ 0` (plus
the empty rest of the control stack).  Only `main` runs, its control stack is `[main]`, every
declared handle names its own device in its initial state (so `main` sees everything and its
ambient is empty), and there are no threads. -/
theorem Program.initCfgTyped {prog : Program K St R} {Ψ Γ' Δ' W Q F}
    (ht : prog.TypedA P M Ψ Γ' Δ' W Q F) (K₀ : R) :
    CfgTyped P M Ψ 0 (prog.initConfig K₀) (Q K₀ 0 + 0) := by
  have hC : Corr some prog.initPeriphs prog.initPeriphs 0 0 :=
    ⟨fun x _ => ⟨x, rfl, rfl⟩, fun _ _ _ _ _ hx hy => Option.some.inj (hx.trans hy.symm), rfl⟩
  have hR : Rev some prog.initPeriphs prog.initPeriphs := by
    intro x d hx _; cases hx; rfl
  have hok : ActOK M TCtx.empty prog.initPCtx 0 Mem.empty some prog.initPeriphs 0 :=
    ⟨fun x τ h => by simp [TCtx.empty] at h, prog.initPeriphs, 0, hC, hR, Program.initOK prog,
      by simp [ambBg]⟩
  have hst := StackOK.base (P := P) (M := M) (Ψ := Ψ) (Am := 0) (E := none)
    (T := fun _ => none) (Kc := K₀)
    (CtlTyped.cmd ht.2.2 ⟨DevEnv.Ceil.of_none, DevEnv.Ceil.of_none⟩ (fun _ _ h => h) (PCtx.Widen.refl _)
      (ThreadCtx.Le.refl _) ThreadCtx.WinShape.empty ThreadCtx.WinCover.empty
      (.nil ⟨DevEnv.Ceil.of_none, DevEnv.Ceil.of_none⟩))
    (fun e he => by cases he) ThreadCtx.empty_isEmpty hok ThreadCtx.WinShape.empty
    ThreadCtx.WinCover.empty (fun h => by cases h) ThreadCtx.CapOK.empty
    (fun e he => by cases he) (fun h => by cases h)
  exact CfgTyped.of_main rfl (fun _ => rfl) ThreadCtx.empty_isEmpty hst
    (actsNoAwait_cons.2 ⟨ctlNoAwait_cmd_cons.2 (fun _ h => by simp at h), fun _ h => by simp at h⟩)

/-- **Cost soundness of async programs on the machine.**  A program well typed under `TypedA`,
run to completion on the machine from clock `K₀`, costs at most `Q K₀ 0` — whatever the
schedule (when threads are preempted onto the stack), whatever the hardware does to captured
peripherals within their envelopes, and whether each `await` succeeds or times out.  The
initial configuration is typed with potential `Q K₀ 0` (`Program.initCfgTyped`), every step
pays for itself (`CfgTyped.steps`), and potentials are nonnegative.  Calls are allowed while
threads are pending (the callee must keep the clock fixed). -/
theorem Program.MRun.soundnessA (hM : M.WF) (hP : P.WF) {prog : Program K St R}
    {Ψ : SigCtxA K St R} {Γ' : TCtx K} {Δ' W : PCtx K St} {Q : R → R → R} {F : R → R}
    (ht : prog.TypedA P M Ψ Γ' Δ' W Q F) {K₀ q : R} {c : Config K St R}
    (h : prog.MRun P M K₀ c q) : q ≤ Q K₀ 0 := by
  have hΨd := Program.sigsDerivedA ht
  obtain ⟨Φ', _, hle⟩ := CfgTyped.steps hM (Program.sigsMonoA hM ht) hP hΨd.closed hΨd h.1
    (Program.initCfgTyped ht K₀)
  rw [add_zero] at hle
  exact le_trans le_self_add hle
