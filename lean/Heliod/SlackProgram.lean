import Heliod.Necessity

/-!
# Slack decomposition for whole programs

`slack_decomposition` assumes `SigsDerived`: each signature is the one T-FunDecl derives for
its declaration, typed against the whole signature context.  A program's declarations are
typed *in order*, each against the signatures declared before it.  Typing is preserved when the
signature context grows (`Typed.weaken`), so every declaration also types against the final
context, which gives `SigsDerived` for well-typed programs (`Program.sigsDerived`).

Main result: `Program.slack_decomposition` — a well-typed program run from clock `K₀` (along
any control-flow path, or any real execution: `Program.Eval.slack_decomposition`) costs exactly
`Q K₀ 0` minus its recorded slack.  `Program.initPinned`: a program starts with no state
uncertainty — every handle is declared with a single initial state.
-/

variable {K St R : Type} [DecidableEq K] [DecidableEq St]
variable [CommSemiring R] [LinearOrder R] [OrderBot R]
variable {P : Platform K St} {M : CostModel K St R}

/-! ### Weakening the signature context -/

/-- `Ψ ≤ Ψ'`: every signature of `Ψ` is also in `Ψ'`. -/
def SigCtx.Le (Ψ Ψ' : SigCtx K St R) : Prop :=
  ∀ g sig, Ψ g = some sig → Ψ' g = some sig

mutual

/-- **Typing is preserved when signatures are added.**  Only T-Call consults `Ψ`, and it only
looks signatures up.  Lets a declaration typed against earlier declarations be used as typed
against the program's full signature context. -/
theorem Typed.weaken {Ψ Ψ' : SigCtx K St R} (hle : SigCtx.Le Ψ Ψ')
    {Γ Δ c Γ' Δ' Q F} : Typed P M Ψ Γ Δ c Γ' Δ' Q F → Typed P M Ψ' Γ Δ c Γ' Δ' Q F
  | .skip => .skip
  | .assign h₁ h₂ => .assign h₁ h₂
  | .ite h h₁ h₂ => .ite h (h₁.weaken hle) (h₂.weaken hle)
  | .transition h₁ h₂ h₃ => .transition h₁ h₂ h₃
  | .downgrade h₁ h₂ h₃ => .downgrade h₁ h₂ h₃
  | .clock h => .clock h
  | .seq h₁ h₂ => .seq (h₁.weaken hle) (h₂.weaken hle)
  | .matchSt h₁ h₂ ha => .matchSt h₁ h₂ (ha.weaken hle)
  | .call hg h₁ h₂ h₃ h₄ => .call (hle _ _ hg) h₁ h₂ h₃ h₄

/-- Arms version of `Typed.weaken`. -/
theorem ArmsTyped.weaken {Ψ Ψ' : SigCtx K St R} (hle : SigCtx.Le Ψ Ψ')
    {Γ Δ p k T arms Γ' Δ' Q F} :
    ArmsTyped P M Ψ Γ Δ p k T arms Γ' Δ' Q F → ArmsTyped P M Ψ' Γ Δ p k T arms Γ' Δ' Q F
  | .last h₁ h h₂ => .last h₁ (h.weaken hle) h₂
  | .cons h₁ h ha => .cons h₁ (h.weaken hle) (ha.weaken hle)
  | .skip h₁ ha => .skip h₁ (ha.weaken hle)

end

/-- A function declaration typed against `Ψ` is typed against any larger `Ψ'`, with the same
signature. -/
theorem FunDeclTyped.weaken {Ψ Ψ' : SigCtx K St R} (hle : SigCtx.Le Ψ Ψ')
    {d : FunDecl K St R} {sig : FunSig K St R} (hd : FunDeclTyped P M Ψ d sig) :
    FunDeclTyped P M Ψ' d sig :=
  ⟨hd.argTy, hd.pKind, hd.sIn, hd.retTy, hd.sOut,
    have ⟨Γb, Δb, Qb, Fb, S', hb, rest⟩ := hd.body
    ⟨Γb, Δb, Qb, Fb, S', hb.weaken hle, rest⟩⟩

/-! ### Declarations typed in order give derived signatures -/

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] in
/-- Adding a signature under a fresh name extends the context. -/
private theorem SigCtx.le_update {Ψ : SigCtx K St R} {g : FName} (hg : Ψ g = none)
    (sig : FunSig K St R) : SigCtx.Le Ψ (Function.update Ψ g (some sig)) := by
  intro g' sig' h
  have hne : g' ≠ g := by rintro rfl; rw [hg] at h; cases h
  rw [Function.update_of_ne hne]; exact h

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] in
/-- `≤` on signature contexts is transitive. -/
private theorem SigCtx.Le.trans {Ψ₁ Ψ₂ Ψ₃ : SigCtx K St R} (h₁ : SigCtx.Le Ψ₁ Ψ₂)
    (h₂ : SigCtx.Le Ψ₂ Ψ₃) : SigCtx.Le Ψ₁ Ψ₃ :=
  fun g sig h => h₂ g sig (h₁ g sig h)

/-- Typing distinct, fresh declarations in order only adds signatures: the starting context is
below the final one. -/
theorem DeclsTyped.le {Ψ₀ ds Ψ'} (hds : DeclsTyped P M Ψ₀ ds Ψ') :
    (ds.map (·.name)).Nodup → (∀ d ∈ ds, Ψ₀ d.name = none) → SigCtx.Le Ψ₀ Ψ' := by
  induction hds with
  | nil => intro _ _ g sig h; exact h
  | @cons Ψ d ds sig Ψ' _ _ ih =>
    intro hnd hfresh
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    refine (SigCtx.le_update (hfresh d (List.mem_cons_self ..)) sig).trans (ih hnd.2 ?_)
    intro d' hd'
    have hne : d'.name ≠ d.name := fun he => hnd.1 ⟨d', hd', he⟩
    rw [Function.update_of_ne hne]
    exact hfresh d' (List.mem_cons_of_mem _ hd')

/-- **Declarations typed in order give derived signatures.**  Every signature in the final
context is the one T-FunDecl derives for its declaration, typed against the final context (by
weakening from the prefix it was actually typed against). -/
theorem DeclsTyped.sigsDerived {Ψd : FCtx K St R} {Ψ₀ ds Ψ'}
    (hds : DeclsTyped P M Ψ₀ ds Ψ') :
    (ds.map (·.name)).Nodup → (∀ d ∈ ds, Ψ₀ d.name = none) →
    (∀ d ∈ ds, Ψd d.name = some d) →
    (∀ g sig, Ψ₀ g = some sig → ∃ d, Ψd g = some d ∧ FunDeclTyped P M Ψ' d sig) →
    SigsDerived P M Ψd Ψ' := by
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
    have hle : SigCtx.Le (Function.update Ψ d.name (some sig)) Ψ' := hrest.le hnd'.2 hfresh'
    have hle₀ : SigCtx.Le Ψ Ψ' :=
      (SigCtx.le_update (hfresh d (List.mem_cons_self ..)) sig).trans hle
    refine ih hnd'.2 hfresh' (fun d' hd' => hmem d' (List.mem_cons_of_mem _ hd')) ?_
    intro g sig' hg
    by_cases h : g = d.name
    · subst h
      simp only [Function.update_self, Option.some.injEq] at hg
      subst hg
      exact ⟨d, hmem d (List.mem_cons_self ..), hd.weaken hle₀⟩
    · rw [Function.update_of_ne h] at hg
      exact hΨ₀ g sig' hg

/-- A well-typed program's signatures are derived (the hypothesis of `slack_decomposition`). -/
theorem Program.sigsDerived {prog : Program K St R} {Ψ Γ' Δ' Q F}
    (ht : prog.Typed P M Ψ Γ' Δ' Q F) : SigsDerived P M prog.fctx Ψ :=
  DeclsTyped.sigsDerived ht.2.1 ht.1 (fun _ _ => rfl) (fun _ hd => Program.fctx_of_mem ht.1 hd)
    (fun _ _ h => by simp at h)

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] in
/-- **Programs start with no state uncertainty.**  Every declared handle has a single initial
state, so the initial context is pinned; all `state` slack in a program run arises from merges
(after an `if`, or a `match` with repeated arm states), multi-state function inputs or
multi-state call outputs (`Typed.pinned`). -/
theorem Program.initPinned (prog : Program K St R) : prog.initPCtx.Pinned := by
  unfold Program.initPCtx
  induction prog.periphs with
  | nil => intro x k T h; cases h
  | cons h hs ih => exact ih.set _ _ _

/-! ### Whole programs -/

variable [IsOrderedRing R] [CanonicallyOrderedAdd R] [Sub R] [OrderedSub R]

/-- **Slack decomposition for whole programs.**  For a well-typed program and any control-flow
path of `main` from the initial peripherals at clock `K₀` (nothing ambient), the program's
summary is the path's cost plus the recorded slack: `Q K₀ 0 = q + Σ δᵢ`, all terms `≥ 0`. -/
theorem Program.slack_decomposition (hM : M.WF) {prog : Program K St R} {Ψ Γ' Δ' Q F}
    (ht : prog.Typed P M Ψ Γ' Δ' Q F) {K₀ S' q K'}
    (hp : Path M prog.fctx 0 prog.initPeriphs K₀ prog.main S' q K') :
    ∃ L, SlackRun P M Ψ prog.fctx TCtx.empty prog.initPCtx prog.main Γ' Δ' Q F
        0 prog.initPeriphs K₀ S' q K' L ∧
      (∀ i ∈ L, i.actual ≤ i.typed) ∧ Q K₀ 0 = q + slack L := by
  obtain ⟨L, hL, hle, hq⟩ := _root_.slack_decomposition hM (Program.sigsValid hM ht)
    (Program.sigsDerived ht) ht.2.2 hp (Program.initOK prog)
  refine ⟨L, hL, hle, ?_⟩
  simpa [ambBg] using hq

/-- **Slack decomposition for program executions.**  Every run of a well-typed program costs
exactly its summary `Q K₀ 0` minus the slack recorded along it. -/
theorem Program.Eval.slack_decomposition (hM : M.WF) {prog : Program K St R} {Ψ Γ' Δ' Q F}
    (ht : prog.Typed P M Ψ Γ' Δ' Q F) {K₀ σ' S' q K'} (he : prog.Eval M K₀ σ' S' q K') :
    ∃ L, SlackRun P M Ψ prog.fctx TCtx.empty prog.initPCtx prog.main Γ' Δ' Q F
        0 prog.initPeriphs K₀ S' q K' L ∧
      (∀ i ∈ L, i.actual ≤ i.typed) ∧ Q K₀ 0 = q + slack L :=
  Program.slack_decomposition hM ht he.toPath
