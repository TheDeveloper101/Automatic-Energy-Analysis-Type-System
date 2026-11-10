import Heliod.AsyncSafety
import Heliod.AsyncSlack

/-!
# Embedding the sync typing into the async typing

A command typed by the sync judgment `Typed` is typed by the async judgment `TypedA` with the
**same output contexts and the same summaries** `Q`, `F`: not frozen, with no pending threads
before or after, and some visited context `W` (which `Typed` does not track).  Lifted to
declarations and programs, every sync-typed program is `TypedA`-typed, so the async results on
the machine apply to it: cost soundness (`Program.MRun.soundnessA`), type safety
(`Program.typeSafetyA`) and the slack decomposition (`Program.slack_decompositionA`).

## Side condition: the program's declared states are stable

The two typings differ in one place: a `match` narrows the matched handle to `{st}` in `Typed`
but to `hwClose {st}` in `TypedA` (hardware may move a captured peripheral right after the
match), and async signatures must be closed under hardware steps.  For a stable state these
agree (`HWReach(st) = ∅`, `Platform.WF`).  Sync typing never introduces a transient state
(transition and downgrade targets must be stable), so it suffices that the states the program
*declares* are stable: the handles' initial states and every function's input and output
states.  Then every state set in every context of the derivation is stable (`PCtx.Stable`).

Without the condition, `TypedA` can give a strictly larger (still sound) summary.

## Signatures

A sync signature `sig` becomes the async signature `⟨sig, visit, false⟩`: `stableClock = false`
(no rule consults it when nothing is pending and the code is not frozen), and `visit` the
parameter's states in the body's visited context.  At call sites any `visit` works: with no
pending thread nothing observes it.
-/

set_option linter.unusedSectionVars false

variable {K St R : Type} [DecidableEq K] [DecidableEq St]
variable [CommSemiring R] [LinearOrder R] [OrderBot R]
variable {P : Platform K St} {M : CostModel K St R}

/-- Every state set of a context is made of stable states. -/
def PCtx.Stable (P : Platform K St) (Δ : PCtx K St) : Prop :=
  ∀ p k S, Δ p = .live k S → ∀ s ∈ S, P.stable k s

/-- Setting a handle to stable states keeps a context stable. -/
theorem PCtx.Stable.set {Δ : PCtx K St} (h : Δ.Stable P) {p : Var} {k : K} {S : Finset St}
    (hS : ∀ s ∈ S, P.stable k s) : (Δ.set p k S).Stable P := by
  intro x k' S' hx
  rw [PCtx.set_apply] at hx
  split_ifs at hx
  · cases hx; exact hS
  · exact h x k' S' hx

/-- Joins of stable contexts are stable. -/
theorem PCtx.Stable.join {Δ₁ Δ₂ : PCtx K St} (h₁ : Δ₁.Stable P) (h₂ : Δ₂.Stable P) :
    (Δ₁.join Δ₂).Stable P := by
  intro x k S hx
  rw [PCtx.join_apply] at hx
  cases e₁ : Δ₁ x with
  | absent => rw [e₁] at hx; cases hx
  | live k₁ S₁ =>
    cases e₂ : Δ₂ x with
    | absent => rw [e₁, e₂] at hx; cases hx
    | live k₂ S₂ =>
      rw [e₁, e₂] at hx
      simp only [PEntry.join] at hx
      split_ifs at hx with hk
      cases hx; subst hk
      intro s hs
      rcases Finset.mem_union.1 hs with hs | hs
      · exact h₁ x _ _ e₁ s hs
      · exact h₂ x _ _ e₂ s hs

/-- A single stable handle. -/
theorem PCtx.Stable.single {p : Var} {k : K} {S : Finset St} (hS : ∀ s ∈ S, P.stable k s) :
    PCtx.Stable P (Finsupp.single p (PEntry.live k S) : PCtx K St) := by
  intro x k' S' hx
  by_cases h : x = p
  · subst h; rw [Finsupp.single_eq_same] at hx; cases hx; exact hS
  · simp [Ne.symm h] at hx

/-- Stable states are closed under hardware steps (they have none). -/
theorem Platform.hwClose_of_stable (hP : P.WF) {k : K} {S : Finset St}
    (h : ∀ s ∈ S, P.stable k s) : P.hwClose k S = S := by
  ext x
  simp only [Platform.hwClose, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro (hx | ⟨s, hs, hx⟩)
    · exact hx
    · rw [hP.hwReach_stable k s (h s hs)] at hx; cases hx
  · exact Or.inl

/-- A stable singleton is closed under hardware steps. -/
theorem Platform.hwClose_single (hP : P.WF) {k : K} {st : St} (h : P.stable k st) :
    P.hwClose k {st} = {st} :=
  Platform.hwClose_of_stable hP fun s hs => by rw [Finset.mem_singleton.1 hs]; exact h

/-- The async signature of a sync signature. -/
def FunSig.toA (sig : FunSig K St R) (visit : Finset St) : FunSigA K St R :=
  ⟨sig, visit, false⟩

/-- `Ψa` embeds `Ψ`: every sync signature appears in `Ψa` as `sig.toA v` for some `v`, and its
output states are stable. -/
def SigsEmbed (P : Platform K St) (Ψ : SigCtx K St R) (Ψa : SigCtxA K St R) : Prop :=
  ∀ g sig, Ψ g = some sig → (∀ s ∈ sig.sOut, P.stable sig.pKind s) ∧
    ∃ v, Ψa g = some (sig.toA v)

variable {Ψ : SigCtx K St R} {Ψa : SigCtxA K St R}

mutual

/-- **Sync typing embeds into async typing**, with the same output contexts and summaries, not
frozen and with no pending threads, from a stable context (whose outputs stay stable). -/
theorem Typed.toA (hP : P.WF) (hΨ : SigsEmbed P Ψ Ψa) {Γ Δ c Γ' Δ' Q F} :
    Typed P M Ψ Γ Δ c Γ' Δ' Q F → Δ.Stable P →
    (∃ W, TypedA P M Ψa false Γ Δ ThreadCtx.empty c Γ' Δ' ThreadCtx.empty W Q F) ∧
      Δ'.Stable P
  | .skip, hΔ => ⟨⟨_, .skip⟩, hΔ⟩
  | .assign hty hx, hΔ => ⟨⟨_, .assign hty hx⟩, hΔ⟩
  | .ite hty h₁ h₂, hΔ =>
    have ⟨⟨_, d₁⟩, hs₁⟩ := h₁.toA hP hΨ hΔ
    have ⟨⟨_, d₂⟩, hs₂⟩ := h₂.toA hP hΨ hΔ
    ⟨⟨_, .ite hty d₁ d₂ (fun _ => Or.inl ⟨rfl, rfl⟩)⟩, hs₁.join hs₂⟩
  | .transition hp hst hle, hΔ =>
    ⟨⟨_, .transition hp (fun ⟨_, _, h, _⟩ => by cases h) hst hle⟩,
      hΔ.set fun s hs => by rw [Finset.mem_singleton.1 hs]; exact hst⟩
  | .downgrade hp hst hdg, hΔ =>
    ⟨⟨_, .downgrade hp (fun ⟨_, _, h, _⟩ => by cases h) hst hdg⟩,
      hΔ.set fun s hs => by rw [Finset.mem_singleton.1 hs]; exact hst⟩
  | .clock hf, hΔ => ⟨⟨_, .clock rfl (fun _ => rfl) hf⟩, hΔ⟩
  | .seq h₁ h₂, hΔ =>
    have ⟨⟨_, d₁⟩, hs₁⟩ := h₁.toA hP hΨ hΔ
    have ⟨⟨_, d₂⟩, hs₂⟩ := h₂.toA hP hΨ hs₁
    ⟨⟨_, .seq d₁ d₂⟩, hs₂⟩
  | .matchSt hp hsub harms, hΔ =>
    have ⟨⟨_, da⟩, hs⟩ := harms.toA hP hΨ hΔ hp
    ⟨⟨_, .matchSt hp (fun ⟨_, _, h, _⟩ => by cases h) hsub da⟩, hs⟩
  | .call hg hty hx hp hsub, hΔ =>
    have ⟨hout, _, hga⟩ := hΨ _ _ hg
    ⟨⟨_, .call hga hty hx hp hsub (fun ⟨_, _, h, _⟩ => by cases h)
      (fun h => h.elim (fun h => by cases h) (fun h => absurd (fun _ => rfl) h))⟩,
      hΔ.set hout⟩

/-- **Sync arms embed into async arms** (`Typed.toA` for `match`): the matched handle's states
are stable, so narrowing to `hwClose {st}` is narrowing to `{st}`. -/
theorem ArmsTyped.toA (hP : P.WF) (hΨ : SigsEmbed P Ψ Ψa) {Γ Δ p k S arms Γ' Δ' Q F} :
    ArmsTyped P M Ψ Γ Δ p k S arms Γ' Δ' Q F → Δ.Stable P → Δ p = .live k S →
    (∃ W, ArmsTypedA P M Ψa false Γ Δ ThreadCtx.empty p k S arms Γ' Δ' ThreadCtx.empty W Q F) ∧
      Δ'.Stable P
  | .last hst hc hrest, hΔ, hp =>
    have hstab := hΔ p k S hp _ hst
    have hcl := Platform.hwClose_single hP hstab
    have ⟨⟨_, d⟩, hs⟩ := hc.toA hP hΨ (hΔ.set fun s hs => by
      rw [Finset.mem_singleton.1 hs]; exact hstab)
    ⟨⟨_, by
      have h := ArmsTypedA.last (P := P) (M := M) (Ψ := Ψa) (fz := false) (Θ := ThreadCtx.empty)
        (rest := _) hst (by rw [hcl]; exact d) hrest
      rw [hcl] at h; exact h⟩, hs⟩
  | .cons hst hc hr, hΔ, hp =>
    have hstab := hΔ p k S hp _ hst
    have hcl := Platform.hwClose_single hP hstab
    have ⟨⟨_, d⟩, hs₁⟩ := hc.toA hP hΨ (hΔ.set fun s hs => by
      rw [Finset.mem_singleton.1 hs]; exact hstab)
    have ⟨⟨_, dr⟩, hs₂⟩ := hr.toA hP hΨ hΔ hp
    ⟨⟨_, by
      have h := ArmsTypedA.cons (P := P) (M := M) (Ψ := Ψa) (fz := false)
        (Θ := ThreadCtx.empty) hst (by rw [hcl]; exact d) dr (fun _ => Or.inl ⟨rfl, rfl⟩)
      rw [hcl] at h; exact h⟩, hs₁.join hs₂⟩
  | .skip hst hr, hΔ, hp =>
    have ⟨⟨_, dr⟩, hs⟩ := hr.toA hP hΨ hΔ hp
    ⟨⟨_, .skip hst dr⟩, hs⟩

end

/-- **A sync declaration embeds**: with stable input and output states, `d` is async-typed with
the signature `sig.toA v`, where `v` is the parameter's states in the body's visited context.
Stable state sets are closed under hardware steps, as `FunDeclTypedA` requires. -/
theorem FunDeclTyped.toA (hP : P.WF) (hΨ : SigsEmbed P Ψ Ψa) {d : FunDecl K St R}
    {sig : FunSig K St R} (h : FunDeclTyped P M Ψ d sig)
    (hin : ∀ s ∈ d.sIn, P.stable d.pKind s) (hout : ∀ s ∈ d.sOut, P.stable d.pKind s) :
    ∃ v, FunDeclTypedA P M Ψa d (sig.toA v) := by
  obtain ⟨hA, hK, hI, hR, hO, Γb, Δb, Qb, Fb, S', hb, hret, hΔb, hS', hcost, hclk⟩ := h
  obtain ⟨⟨Wb, db⟩, _⟩ := hb.toA hP hΨ (PCtx.Stable.single hin)
  have hsh := congrFun db.shape_eq.2 d.parg
  cases hW : Wb d.parg with
  | absent => simp only [PCtx.shape, hW, Finsupp.single_eq_same] at hsh; cases hsh
  | live k' Sv =>
    simp only [PCtx.shape, hW, Finsupp.single_eq_same, Option.some.injEq] at hsh
    subst hsh
    exact ⟨Sv, ⟨hA, hK, hI, hR, hO,
      ⟨Γb, Δb, Wb, Qb, Fb, S', Sv, db, hret, hΔb, hS', hW, subset_rfl, hcost, hclk⟩,
      Platform.hwClose_of_stable hP hin, Platform.hwClose_of_stable hP hout⟩⟩

/-- **Sync declarations embed**, in order: the async signature context embeds the sync one at
every step. -/
theorem DeclsTyped.toA (hP : P.WF) {Ψ Ψ' : SigCtx K St R} {ds : List (FunDecl K St R)}
    (h : DeclsTyped P M Ψ ds Ψ')
    (hds : ∀ d ∈ ds, (∀ s ∈ d.sIn, P.stable d.pKind s) ∧ (∀ s ∈ d.sOut, P.stable d.pKind s)) :
    ∀ {Ψa : SigCtxA K St R}, SigsEmbed P Ψ Ψa →
      ∃ Ψa', DeclsTypedA P M Ψa ds Ψa' ∧ SigsEmbed P Ψ' Ψa' := by
  induction h with
  | nil => intro Ψa hΨ; exact ⟨Ψa, .nil, hΨ⟩
  | @cons Ψ d ds sig Ψ' hd _ ih =>
    intro Ψa hΨ
    obtain ⟨hin, hout⟩ := hds d List.mem_cons_self
    obtain ⟨v, hdA⟩ := hd.toA hP hΨ hin hout
    have hΨ' : SigsEmbed P (Function.update Ψ d.name (some sig))
        (Function.update Ψa d.name (some (sig.toA v))) := by
      intro g sig' hg
      by_cases hgn : g = d.name
      · subst hgn
        rw [Function.update_self, Option.some.injEq] at hg
        subst hg
        refine ⟨fun s hs => ?_, v, by rw [Function.update_self]⟩
        rw [hd.pKind]; exact hout s (hd.sOut ▸ hs)
      · rw [Function.update_of_ne hgn] at hg ⊢
        exact hΨ g sig' hg
    obtain ⟨Ψa', hds', hΨa'⟩ := ih (fun d' h' => hds d' (List.mem_cons_of_mem _ h')) hΨ'
    exact ⟨Ψa', .cons hdA hds', hΨa'⟩

/-- Declaring handles in stable states gives a stable context. -/
theorem PCtx.Stable.foldr_set (l : List (Var × K × St)) (h : ∀ x ∈ l, P.stable x.2.1 x.2.2) :
    PCtx.Stable P (l.foldr (fun h Δ => Δ.set h.1 h.2.1 {h.2.2}) 0) := by
  induction l with
  | nil => intro p k S hp; cases hp
  | cons x xs ih =>
    exact (ih fun y hy => h y (List.mem_cons_of_mem _ hy)).set fun s hs => by
      rw [Finset.mem_singleton.1 hs]; exact h x List.mem_cons_self

/-- The initial context of a program whose handles start in stable states is stable. -/
theorem Program.initPCtx_stable {prog : Program K St R}
    (h : ∀ x ∈ prog.periphs, P.stable x.2.1 x.2.2) : prog.initPCtx.Stable P :=
  PCtx.Stable.foldr_set _ h

/-- **Sync-typed programs are async-typed, with the same summaries** (the declared states
being stable: the handles' initial states and the functions' input and output states). -/
theorem Program.Typed.toA (hP : P.WF) {prog : Program K St R} {Ψ : SigCtx K St R}
    {Γ' : TCtx K} {Δ' : PCtx K St} {Q : R → R → R} {F : R → R}
    (ht : prog.Typed P M Ψ Γ' Δ' Q F) (hper : ∀ x ∈ prog.periphs, P.stable x.2.1 x.2.2)
    (hds : ∀ d ∈ prog.funs,
      (∀ s ∈ d.sIn, P.stable d.pKind s) ∧ (∀ s ∈ d.sOut, P.stable d.pKind s)) :
    ∃ (Ψa : SigCtxA K St R) (W : PCtx K St), prog.TypedA P M Ψa Γ' Δ' W Q F := by
  obtain ⟨hnd, hdecl, hmain⟩ := ht
  obtain ⟨Ψa, hdA, hΨa⟩ := hdecl.toA hP hds (Ψa := fun _ => none) (fun _ _ h => by cases h)
  obtain ⟨⟨W, hmA⟩, _⟩ := hmain.toA hP hΨa (Program.initPCtx_stable hper)
  exact ⟨Ψa, W, hnd, hdA, hmA⟩

variable [IsOrderedRing R] [CanonicallyOrderedAdd R] [Sub R] [OrderedSub R]

/-- **Type safety on the machine for sync-typed programs**: every configuration reached is
final or can step (via the embedding and `Program.typeSafetyA`). -/
theorem Program.Typed.typeSafety (hM : M.WF) (hP : P.WF) {prog : Program K St R}
    {Ψ : SigCtx K St R} {Γ' : TCtx K} {Δ' : PCtx K St} {Q : R → R → R} {F : R → R}
    (ht : prog.Typed P M Ψ Γ' Δ' Q F) (hper : ∀ x ∈ prog.periphs, P.stable x.2.1 x.2.2)
    (hds : ∀ d ∈ prog.funs,
      (∀ s ∈ d.sIn, P.stable d.pKind s) ∧ (∀ s ∈ d.sOut, P.stable d.pKind s))
    {K₀ q : R} {c : Config K St R} (h : Steps P M prog.fctx 0 (prog.initConfig K₀) q c) :
    c.Final ∨ ∃ q' c', MStep P M prog.fctx 0 c q' c' := by
  obtain ⟨_, _, hA⟩ := ht.toA hP hper hds
  exact Program.typeSafetyA hM hP hA h

/-- **Cost soundness on the machine for sync-typed programs via the async proof**: the same
bound `Q K₀ 0` (independently of the sync adequacy route, `Program.MRun.soundness`). -/
theorem Program.Typed.soundnessA (hM : M.WF) (hP : P.WF) {prog : Program K St R}
    {Ψ : SigCtx K St R} {Γ' : TCtx K} {Δ' : PCtx K St} {Q : R → R → R} {F : R → R}
    (ht : prog.Typed P M Ψ Γ' Δ' Q F) (hper : ∀ x ∈ prog.periphs, P.stable x.2.1 x.2.2)
    (hds : ∀ d ∈ prog.funs,
      (∀ s ∈ d.sIn, P.stable d.pKind s) ∧ (∀ s ∈ d.sOut, P.stable d.pKind s))
    {K₀ q : R} {c : Config K St R} (h : prog.MRun P M K₀ c q) : q ≤ Q K₀ 0 := by
  obtain ⟨_, _, hA⟩ := ht.toA hP hper hds
  exact Program.MRun.soundnessA hM hP hA h
