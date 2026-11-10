import Heliod.AsyncInvariants
import Heliod.Necessity

/-!
# State inference (sync fragment): narrowing, inline calls, inferred entry states

The paper's state inference makes a function's cost **parametric in its entry state**: the
entry state is a state variable, solved at each call site together with the caller's knowledge
("lazy concretization"), so a call is charged for the states the caller actually passes rather
than for every state the function accepts.  We model the constraints by the state sets they
denote (`PAPER_DIFFERENCES.md`, section 6):

* **Narrowing** (`Typed.narrow`): typing from a more precise context — smaller state sets, more
  known variables — gives no larger summaries and more precise outputs (given monotone
  signature summaries, non-empty signature output sets, and non-empty narrowed state sets).
  This is the key new metatheorem; it is what makes call-site concretization never worse than
  declared signatures.

* **Inline typing** (`TypedI`, `soundnessI`): a call types the callee's body from the caller's
  current states (lazy concretization), with no declared `sIn` / `sOut`; sound like `Typed`.
* **Precision** (`Typed.toI`, `Program.Typed.precision`): every checked program is inline-typed
  with no larger summaries — call-site concretization is never worse than declared signatures.

* **Accepted entry states** (`Accepts`, `entrySet`): what a function accepts is a downward-closed
  predicate on entry-state sets (`Accepts.mono`, via `TypedI.narrow`) containing every non-empty
  subset of a declared `sIn` (`Program.Typed.accepts`).  It is not closed under union (path-insensitive joins), so
  there is no largest accepted set in general (`Heliod.Examples.EntrySets`).

The writeup's `log_data` under inline typing — called from `Idle`, charged at `Idle` — is
`Heliod.Examples.LogDataInline`.
-/

set_option linter.unusedSectionVars false

variable {K St R : Type} [DecidableEq K] [DecidableEq St]
variable [CommSemiring R] [LinearOrder R] [OrderBot R]
variable {P : Platform K St} {M : CostModel K St R}

/-! ### Context orders -/

omit [DecidableEq K] [DecidableEq St] in
/-- Expression typing survives a context with more bindings. -/
theorem HasTy.weaken {Γ Γ₀ : TCtx K} (hs : Γ.Sub Γ₀) {e : Expr} {τ : Ty K} :
    HasTy Γ e τ → HasTy Γ₀ e τ
  | .var h => .var (hs _ _ h)
  | .val => .val
  | .binop h₁ h₂ h => .binop (h₁.weaken hs) (h₂.weaken hs) h

omit [DecidableEq St] in
/-- Binding a variable keeps the order. -/
theorem TCtx.Sub.bind {Γ Γ₀ : TCtx K} (hs : Γ.Sub Γ₀) (x : Var) (τ : Ty K) :
    (Γ.bind x τ).Sub (Γ₀.bind x τ) := by
  intro y τ' h
  rw [TCtx.bind_apply] at h ⊢
  split_ifs at h ⊢
  · exact h
  · exact hs _ _ h

omit [DecidableEq St] in
/-- Intersections keep the order. -/
theorem TCtx.Sub.inter {Γ₁ Γ₂ Γ₁' Γ₂' : TCtx K} (h₁ : Γ₁.Sub Γ₁') (h₂ : Γ₂.Sub Γ₂') :
    (Γ₁.inter Γ₂).Sub (Γ₁'.inter Γ₂') := by
  intro x τ h
  unfold TCtx.inter at h ⊢
  split_ifs at h with he
  have h₁' := h₁ x τ h
  have h₂' := h₂ x τ (he ▸ h)
  simp only [h₁', h₂', ↓reduceIte]

omit [DecidableEq St] in
/-- The order is transitive. -/
theorem TCtx.Sub.trans {Γ₁ Γ₂ Γ₃ : TCtx K} (h₁ : Γ₁.Sub Γ₂) (h₂ : Γ₂.Sub Γ₃) : Γ₁.Sub Γ₃ :=
  fun x τ h => h₂ x τ (h₁ x τ h)

omit [DecidableEq K] [DecidableEq St] in
/-- Setting a handle keeps the order. -/
theorem PCtx.Le.set {Δ₀ Δ : PCtx K St} (h : Δ₀.Le Δ) (p : Var) (k : K) (S : Finset St) :
    (Δ₀.set p k S).Le (Δ.set p k S) := by
  intro x
  rw [PCtx.set_apply, PCtx.set_apply]
  split_ifs
  · simp [PEntry.Le]
  · exact h x

omit [DecidableEq K] [DecidableEq St] in
/-- Below an absent entry is an absent entry. -/
theorem PCtx.Le.absent {Δ₀ Δ : PCtx K St} (h : Δ₀.Le Δ) {x : Var} (hx : Δ x = 0) : Δ₀ x = 0 := by
  have a := h x
  rw [hx] at a
  cases e : Δ₀ x with
  | absent => rfl
  | live k S => rw [e] at a; exact a.elim

omit [DecidableEq K] [DecidableEq St] in
/-- Below a live entry is a live entry of the same kind with fewer states. -/
theorem PCtx.Le.live {Δ₀ Δ : PCtx K St} (h : Δ₀.Le Δ) {x : Var} {k : K} {S : Finset St}
    (hx : Δ x = .live k S) : ∃ S₀ ⊆ S, Δ₀ x = .live k S₀ := by
  have a := h x
  rw [hx] at a
  cases e : Δ₀ x with
  | absent => rw [e] at a; exact a.elim
  | live k₀ S₀ => rw [e] at a; obtain ⟨rfl, hs⟩ := a; exact ⟨S₀, hs, rfl⟩

omit [DecidableEq K] in
/-- Setting a handle to a non-empty set keeps state sets non-empty. -/
theorem PCtx.NonEmpty.set {Δ : PCtx K St} (h : Δ.NonEmpty) (p : Var) (k : K) {S : Finset St}
    (hS : S.Nonempty) : (Δ.set p k S).NonEmpty := by
  intro x k' T hx
  rw [PCtx.set_apply] at hx
  split_ifs at hx
  · cases hx; exact hS
  · exact h x k' T hx

/-- Joins of contexts with non-empty state sets have non-empty state sets. -/
theorem PCtx.NonEmpty.join {Δ₁ Δ₂ : PCtx K St} (h₁ : Δ₁.NonEmpty) (_h₂ : Δ₂.NonEmpty) :
    (Δ₁.join Δ₂).NonEmpty := by
  intro x k T hx
  rw [PCtx.join_apply] at hx
  cases e₁ : Δ₁ x with
  | absent => rw [e₁] at hx; cases hx
  | live k₁ S₁ =>
    cases e₂ : Δ₂ x with
    | absent => rw [e₁, e₂] at hx; cases hx
    | live k₂ S₂ =>
      rw [e₁, e₂] at hx
      simp only [PEntry.join] at hx
      split_ifs at hx
      cases hx
      exact (h₁ x _ _ e₁).mono Finset.subset_union_left

variable [IsOrderedRing R] [CanonicallyOrderedAdd R]
variable {Ψ : SigCtx K St R}

/-- Scaling by a non-negative factor is monotone. -/
private theorem mul_le_mul_left'' {f x x' : R} (hx : x ≤ x') : f * x ≤ f * x' :=
  mul_le_mul_of_nonneg_left hx zero_le

/-! ### Narrowing -/

/-- The conclusion of narrowing: from the more precise inputs, a derivation with more precise
outputs (more known variables, smaller state sets, still non-empty) and no larger summaries. -/
def Narrowed (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtx K St R) (Γ₀ : TCtx K)
    (Δ₀ : PCtx K St) (c : Cmd St R) (Γ' : TCtx K) (Δ' : PCtx K St) (Q : R → R → R) (F : R → R) :
    Prop :=
  ∃ Γ₀' Δ₀' Q₀ F₀, Typed P M Ψ Γ₀ Δ₀ c Γ₀' Δ₀' Q₀ F₀ ∧ Γ'.Sub Γ₀' ∧ Δ₀'.Le Δ' ∧
    Δ₀'.NonEmpty ∧ (∀ f b, Q₀ f b ≤ Q f b) ∧ (∀ f, F₀ f ≤ F f)

/-- Arms version of `Narrowed`. -/
def ArmsNarrowed (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtx K St R) (Γ₀ : TCtx K)
    (Δ₀ : PCtx K St) (p : Var) (k : K) (S₀ : Finset St) (arms : Arms St R) (Γ' : TCtx K)
    (Δ' : PCtx K St) (Q : R → R → R) (F : R → R) : Prop :=
  ∃ Γ₀' Δ₀' Q₀ F₀, ArmsTyped P M Ψ Γ₀ Δ₀ p k S₀ arms Γ₀' Δ₀' Q₀ F₀ ∧ Γ'.Sub Γ₀' ∧ Δ₀'.Le Δ' ∧
    Δ₀'.NonEmpty ∧ (∀ f b, Q₀ f b ≤ Q f b) ∧ (∀ f, F₀ f ≤ F f)

mutual

/-- **Narrowing**: a command typed from `Γ, Δ` is typed from any more precise `Γ₀ ⊇ Γ`,
`Δ₀ ⊑ Δ` (with non-empty state sets), with more precise outputs and no larger summaries.
Assumes every signature's summaries are monotone (`hΨm`) and its output set non-empty (`hΨne`).
Typing from fewer possible states can only drop cases: a `match` skips more arms, a join
unions smaller sets, transitions and downgrades take the worst case over fewer sources.  (The
non-emptiness keeps a `match` with at least one reachable arm.) -/
theorem Typed.narrow (hM : M.WF) (hΨm : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk)
    (hΨne : ∀ g sig, Ψ g = some sig → sig.sOut.Nonempty) {Γ Δ c Γ' Δ' Q F} :
    Typed P M Ψ Γ Δ c Γ' Δ' Q F → ∀ {Γ₀ Δ₀}, Γ.Sub Γ₀ → Δ₀.Le Δ → Δ₀.NonEmpty →
      Narrowed P M Ψ Γ₀ Δ₀ c Γ' Δ' Q F
  | .skip, _, _, hs, hle, hne => ⟨_, _, _, _, .skip, hs, hle, hne, fun _ _ => le_rfl, fun _ => le_rfl⟩
  | .assign hty hx, _, _, hs, hle, hne =>
    ⟨_, _, _, _, .assign (hty.weaken hs) (hle.absent hx), hs.bind _ _, hle, hne,
      fun _ _ => mul_le_mul_left'' (add_le_add (add_le_add le_rfl hle.bg_le) le_rfl),
      fun _ => le_rfl⟩
  | .ite hty h₁ h₂, _, _, hs, hle, hne => by
    obtain ⟨Γ₁, Δ₁, Q₁, F₁, d₁, hs₁, hle₁, hne₁, hQ₁, hF₁⟩ := h₁.narrow hM hΨm hΨne hs hle hne
    obtain ⟨Γ₂, Δ₂, Q₂, F₂, d₂, hs₂, hle₂, hne₂, hQ₂, hF₂⟩ := h₂.narrow hM hΨm hΨne hs hle hne
    exact ⟨_, _, _, _, .ite (hty.weaken hs) d₁ d₂, hs₁.inter hs₂,
      PCtx.join_le_join hle₁ hle₂ (d₁.shape_eq.trans d₂.shape_eq.symm), hne₁.join hne₂,
      fun f b => add_le_add (max_le_max (hQ₁ f b) (hQ₂ f b))
        (mul_le_mul_left'' (add_le_add (add_le_add le_rfl hle.bg_le) le_rfl)),
      fun f => max_le_max (hF₁ f) (hF₂ f)⟩
  | .transition hp hst hleS, _, _, hs, hle, hne => by
    obtain ⟨S₀, hS₀, hp₀⟩ := hle.live hp
    exact ⟨_, _, _, _, .transition hp₀ hst (fun s h => hleS s (hS₀ h)), hs, hle.set _ _ _,
      hne.set _ _ (Finset.singleton_nonempty _),
      fun f b => mul_le_mul_left'' (add_le_add (add_le_add (M.maxTrans_mono _ hS₀)
        (hle.erase _).bg_le) le_rfl), fun _ => le_rfl⟩
  | .downgrade hp hst hdg, _, _, hs, hle, hne => by
    obtain ⟨S₀, hS₀, hp₀⟩ := hle.live hp
    exact ⟨_, _, _, _, .downgrade hp₀ hst (fun s h => hdg s (hS₀ h)), hs, hle.set _ _ _,
      hne.set _ _ (Finset.singleton_nonempty _),
      fun f b => mul_le_mul_left'' (add_le_add (add_le_add (M.maxTrans_mono _ hS₀)
        (hle.erase _).bg_le) le_rfl), fun _ => le_rfl⟩
  | .clock hf, _, _, hs, hle, hne =>
    ⟨_, _, _, _, .clock hf, hs, hle, hne,
      fun _ _ => add_le_add le_rfl (mul_le_mul_left'' (add_le_add hle.bg_le le_rfl)),
      fun _ => le_rfl⟩
  | .seq h₁ h₂, _, _, hs, hle, hne => by
    obtain ⟨Γ₁, Δ₁, Q₁, F₁, d₁, hs₁, hle₁, hne₁, hQ₁, hF₁⟩ := h₁.narrow hM hΨm hΨne hs hle hne
    obtain ⟨Γ₂, Δ₂, Q₂, F₂, d₂, hs₂, hle₂, hne₂, hQ₂, hF₂⟩ :=
      h₂.narrow hM hΨm hΨne hs₁ hle₁ hne₁
    have ⟨hm₂F, hm₂Q⟩ := d₂.mono hM hΨm
    exact ⟨_, _, _, _, .seq d₁ d₂, hs₂, hle₂, hne₂,
      fun f b => add_le_add (hQ₁ f b) ((hm₂Q _ _ _ _ (hF₁ f) le_rfl).trans (hQ₂ _ b)),
      fun f => (hm₂F (hF₁ f)).trans (hF₂ _)⟩
  | .matchSt hp hsub ha, _, _, hs, hle, hne => by
    obtain ⟨S₀, hS₀, hp₀⟩ := hle.live hp
    obtain ⟨s, hs₀⟩ := hne _ _ _ hp₀
    obtain ⟨Γa, Δa, Qa, Fa, da, hsa, hlea, hnea, hQa, hFa⟩ :=
      ha.narrow hM hΨm hΨne hs hle hne hS₀ ⟨s, hs₀⟩ ⟨s, hs₀, hsub (hS₀ hs₀)⟩
    exact ⟨_, _, _, _, .matchSt hp₀ (hS₀.trans hsub) da, hsa, hlea, hnea, hQa, hFa⟩
  | .call hg hty hx hp hsub, _, _, hs, hle, hne => by
    obtain ⟨S₀, hS₀, hp₀⟩ := hle.live hp
    exact ⟨_, _, _, _, .call hg (hty.weaken hs) (hle.absent hx) hp₀ (hS₀.trans hsub),
      hs.bind _ _, hle.set _ _ _, hne.set _ _ (hΨne _ _ hg),
      fun f b => add_le_add (mul_le_mul_left'' (add_le_add (add_le_add le_rfl hle.bg_le) le_rfl))
        ((hΨm _ _ hg).2 _ _ _ _ le_rfl (add_le_add le_rfl (hle.erase _).bg_le)),
      fun _ => le_rfl⟩

/-- **Narrowing for `match` arms**: arms typed for the states `S` are typed for any non-empty
`S₀ ⊆ S` that still reaches an arm, with fewer arms taken (the others skipped) and no larger
summaries. -/
theorem ArmsTyped.narrow (hM : M.WF)
    (hΨm : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk)
    (hΨne : ∀ g sig, Ψ g = some sig → sig.sOut.Nonempty) {Γ Δ p k S arms Γ' Δ' Q F} :
    ArmsTyped P M Ψ Γ Δ p k S arms Γ' Δ' Q F → ∀ {Γ₀ Δ₀ S₀}, Γ.Sub Γ₀ → Δ₀.Le Δ →
      Δ₀.NonEmpty → S₀ ⊆ S → S₀.Nonempty → (∃ s ∈ S₀, s ∈ arms.states) →
      ArmsNarrowed P M Ψ Γ₀ Δ₀ p k S₀ arms Γ' Δ' Q F
  | @ArmsTyped.last _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st _ rest _ _ _ _ hst hc hrest, _, _, S₀, hs, hle, hne, hS₀,
      _, ⟨s, hs₀, hsa⟩ => by
    have hst₀ : st ∈ S₀ := by
      simp only [Arms.states, Finset.mem_insert] at hsa
      rcases hsa with rfl | hr
      · exact hs₀
      · exact absurd (hS₀ hs₀) (hrest s hr)
    obtain ⟨Γc, Δc, Qc, Fc, dc, hsc, hlec, hnec, hQc, hFc⟩ :=
      hc.narrow hM hΨm hΨne hs (hle.set p k {st}) (hne.set _ _ (Finset.singleton_nonempty _))
    exact ⟨_, _, _, _, .last hst₀ dc (fun s' hr h => hrest s' hr (hS₀ h)), hsc, hlec, hnec,
      fun f b => add_le_add (hQc f b)
        (mul_le_mul_left'' (add_le_add (hle.set p k {st}).bg_le le_rfl)), hFc⟩
  | @ArmsTyped.cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st _ rest _ _ _ _ _ _ _ _ hst hc hr, _, _, S₀, hs, hle, hne,
      hS₀, hS₀ne, ⟨s, hs₀, hsa⟩ => by
    have hsh := hc.shape_eq.trans ((PCtx.shape_set_set _ _ _ _ ∅).trans hr.shape_eq.symm)
    by_cases hst₀ : st ∈ S₀
    · obtain ⟨Γc, Δc, Qc, Fc, dc, hsc, hlec, hnec, hQc, hFc⟩ :=
        hc.narrow hM hΨm hΨne hs (hle.set p k {st}) (hne.set _ _ (Finset.singleton_nonempty _))
      by_cases hreach : ∃ s' ∈ S₀, s' ∈ rest.states
      · obtain ⟨Γr, Δr, Qr, Fr, dr, hsr, hler, hner, hQr, hFr⟩ :=
          hr.narrow hM hΨm hΨne hs hle hne hS₀ hS₀ne hreach
        have hsh₀ := dc.shape_eq.trans ((PCtx.shape_set_set _ _ _ _ ∅).trans dr.shape_eq.symm)
        exact ⟨_, _, _, _, .cons hst₀ dc dr, hsc.inter hsr, PCtx.join_le_join hlec hler hsh₀,
          hnec.join hner,
          fun f b => max_le_max (add_le_add (hQc f b)
            (mul_le_mul_left'' (add_le_add (hle.set p k {st}).bg_le le_rfl))) (hQr f b),
          fun f => max_le_max (hFc f) (hFr f)⟩
      · exact ⟨_, _, _, _, .last hst₀ dc (fun s' h₁ h₂ => hreach ⟨s', h₂, h₁⟩),
          (TCtx.inter_sub_left _ _).trans hsc, hlec.trans (PCtx.le_join_left hsh), hnec,
          fun f b => (add_le_add (hQc f b) (mul_le_mul_left''
            (add_le_add (hle.set p k {st}).bg_le le_rfl))).trans (le_max_left _ _),
          fun f => (hFc f).trans (le_max_left _ _)⟩
    · have hreach : ∃ s' ∈ S₀, s' ∈ rest.states := by
        simp only [Arms.states, Finset.mem_insert] at hsa
        rcases hsa with rfl | hra
        · exact absurd hs₀ hst₀
        · exact ⟨s, hs₀, hra⟩
      obtain ⟨Γr, Δr, Qr, Fr, dr, hsr, hler, hner, hQr, hFr⟩ :=
        hr.narrow hM hΨm hΨne hs hle hne hS₀ hS₀ne hreach
      exact ⟨_, _, _, _, .skip hst₀ dr, (TCtx.inter_sub_right _ _).trans hsr,
        hler.trans (PCtx.le_join_right hsh), hner,
        fun f b => (hQr f b).trans (le_max_right _ _),
        fun f => (hFr f).trans (le_max_right _ _)⟩
  | @ArmsTyped.skip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st _ rest _ _ _ _ hst hr, _, _, S₀, hs, hle, hne, hS₀, hS₀ne,
      ⟨s, hs₀, hsa⟩ => by
    have hst₀ : st ∉ S₀ := fun h => hst (hS₀ h)
    have hreach : ∃ s' ∈ S₀, s' ∈ rest.states := by
      simp only [Arms.states, Finset.mem_insert] at hsa
      rcases hsa with rfl | hra
      · exact absurd hs₀ hst₀
      · exact ⟨s, hs₀, hra⟩
    obtain ⟨Γr, Δr, Qr, Fr, dr, hsr, hler, hner, hQr, hFr⟩ :=
      hr.narrow hM hΨm hΨne hs hle hne hS₀ hS₀ne hreach
    exact ⟨_, _, _, _, .skip hst₀ dr, hsr, hler, hner, hQr, hFr⟩

end

/-! ### Inline typing: calls concretized at the caller's states

`TypedI` has the rules of `Typed`, except T-Call: instead of instantiating a declared signature,
a call types the callee's body (from its declaration in `Ψd`) starting from the caller's current
state set `Δ p` — the paper's lazy concretization `C_f[α ↦ solve(…)]`, with the constraints
read as the states they allow.  It needs no declared `sIn` / `sOut`: a call is well typed iff the
body types from the caller's states, and the callee's exit states are whatever the body yields.
The charge is T-Call's with T-FunDecl's summary. -/

mutual

/-- Command typing with inline (call-site concretized) calls; see the section doc. -/
inductive TypedI (P : Platform K St) (M : CostModel K St R) (Ψd : FCtx K St R) :
    TCtx K → PCtx K St → Cmd St R → TCtx K → PCtx K St → (R → R → R) → (R → R) → Prop where
  | skip {Γ Δ} : TypedI P M Ψd Γ Δ .skip Γ Δ (fun _ _ => 0) (fun f => f)
  | assign {Γ Δ x e τ} :
      HasTy Γ e τ → Δ x = 0 →
      TypedI P M Ψd Γ Δ (.assign x e) (Γ.bind x τ) Δ
        (fun f b => f * (e.cost M + Δ.bg M + b)) (fun f => f)
  | ite {Γ Δ e c₁ c₂ Γ₁ Δ₁ Q₁ F₁ Γ₂ Δ₂ Q₂ F₂} :
      HasTy Γ e .bool →
      TypedI P M Ψd Γ Δ c₁ Γ₁ Δ₁ Q₁ F₁ →
      TypedI P M Ψd Γ Δ c₂ Γ₂ Δ₂ Q₂ F₂ →
      TypedI P M Ψd Γ Δ (.ite e c₁ c₂) (Γ₁.inter Γ₂) (Δ₁.join Δ₂)
        (fun f b => max (Q₁ f b) (Q₂ f b) + f * (e.cost M + Δ.bg M + b))
        (fun f => max (F₁ f) (F₂ f))
  | transition {Γ Δ p k S st} :
      Δ p = .live k S → P.stable k st → (∀ s ∈ S, P.le k s st) →
      TypedI P M Ψd Γ Δ (.transition p st) Γ (Δ.set p k {st})
        (fun f b => f * (M.maxTrans k S st + (Δ.erase p).bg M + b)) (fun f => f)
  | downgrade {Γ Δ p k S st} :
      Δ p = .live k S → P.stable k st → (∀ s ∈ S, P.dg k s st) →
      TypedI P M Ψd Γ Δ (.downgrade p st) Γ (Δ.set p k {st})
        (fun f b => f * (M.maxTrans k S st + (Δ.erase p).bg M + b)) (fun f => f)
  | clock {Γ Δ f'} :
      0 < f' →
      TypedI P M Ψd Γ Δ (.clock f') Γ Δ
        (fun f b => M.clockCost f f' + f * (Δ.bg M + b)) (fun _ => f')
  | seq {Γ Δ c₁ c₂ Γ₁ Δ₁ Q₁ F₁ Γ₂ Δ₂ Q₂ F₂} :
      TypedI P M Ψd Γ Δ c₁ Γ₁ Δ₁ Q₁ F₁ →
      TypedI P M Ψd Γ₁ Δ₁ c₂ Γ₂ Δ₂ Q₂ F₂ →
      TypedI P M Ψd Γ Δ (.seq c₁ c₂) Γ₂ Δ₂
        (fun f b => Q₁ f b + Q₂ (F₁ f) b) (fun f => F₂ (F₁ f))
  | matchSt {Γ Δ p k S arms Γ' Δ' Q F} :
      Δ p = .live k S → S ⊆ arms.states →
      ArmsTypedI P M Ψd Γ Δ p k S arms Γ' Δ' Q F →
      TypedI P M Ψd Γ Δ (.matchSt p arms) Γ' Δ' Q F
  /-- T-Call, concretized at the caller's states `S = Δ p`. -/
  | call {Γ Δ x g e p d S Γb Δb Qb Fb S'} :
      Ψd g = some d →
      HasTy Γ e d.argTy →
      Δ x = 0 →
      Δ p = .live d.pKind S →
      TypedI P M Ψd (TCtx.empty.bind d.arg d.argTy) (Finsupp.single d.parg (.live d.pKind S))
        d.body Γb Δb Qb Fb →
      HasTy Γb d.ret d.retTy → Δb d.parg = .live d.pKind S' →
      TypedI P M Ψd Γ Δ (.call x g e p) (Γ.bind x d.retTy) (Δ.set p d.pKind S')
        (fun f b => f * (e.cost M + Δ.bg M + b) +
          (Qb f (b + (Δ.erase p).bg M) + Fb f * (d.ret.cost M + Δb.bg M + (b + (Δ.erase p).bg M))))
        Fb

/-- Arms of a `match`, inline typing (as `ArmsTyped`). -/
inductive ArmsTypedI (P : Platform K St) (M : CostModel K St R) (Ψd : FCtx K St R) :
    TCtx K → PCtx K St → Var → K → Finset St → Arms St R →
    TCtx K → PCtx K St → (R → R → R) → (R → R) → Prop where
  | last {Γ Δ p k S st c rest Γ' Δ' Q F} :
      st ∈ S →
      TypedI P M Ψd Γ (Δ.set p k {st}) c Γ' Δ' Q F →
      (∀ s ∈ rest.states, s ∉ S) →
      ArmsTypedI P M Ψd Γ Δ p k S (.cons st c rest) Γ' Δ'
        (fun f b => Q f b + f * ((Δ.set p k {st}).bg M + b)) F
  | cons {Γ Δ p k S st c rest Γ₁ Δ₁ Q₁ F₁ Γ₂ Δ₂ Q₂ F₂} :
      st ∈ S →
      TypedI P M Ψd Γ (Δ.set p k {st}) c Γ₁ Δ₁ Q₁ F₁ →
      ArmsTypedI P M Ψd Γ Δ p k S rest Γ₂ Δ₂ Q₂ F₂ →
      ArmsTypedI P M Ψd Γ Δ p k S (.cons st c rest) (Γ₁.inter Γ₂) (Δ₁.join Δ₂)
        (fun f b => max (Q₁ f b + f * ((Δ.set p k {st}).bg M + b)) (Q₂ f b))
        (fun f => max (F₁ f) (F₂ f))
  | skip {Γ Δ p k S st c rest Γ' Δ' Q F} :
      st ∉ S →
      ArmsTypedI P M Ψd Γ Δ p k S rest Γ' Δ' Q F →
      ArmsTypedI P M Ψd Γ Δ p k S (.cons st c rest) Γ' Δ' Q F

end

variable {Ψd : FCtx K St R}

mutual

/-- Inline typing preserves the shape of `Δ` (as `Typed.shape_eq`). -/
theorem TypedI.shape_eq {Γ Δ c Γ' Δ' Q F} :
    TypedI P M Ψd Γ Δ c Γ' Δ' Q F → Δ'.shape = Δ.shape
  | .skip => rfl
  | .assign _ _ => rfl
  | .ite _ h₁ h₂ => by
      rw [PCtx.shape_join (h₁.shape_eq.trans h₂.shape_eq.symm), h₁.shape_eq]
  | .transition hp _ _ => PCtx.shape_set_of hp _
  | .downgrade hp _ _ => PCtx.shape_set_of hp _
  | .clock _ => rfl
  | .seq h₁ h₂ => h₂.shape_eq.trans h₁.shape_eq
  | .matchSt hp _ ha => ha.shape_eq.trans (PCtx.shape_set_of hp _)
  | .call _ _ _ hp _ _ _ => PCtx.shape_set_of hp _

/-- Arms version of `TypedI.shape_eq`. -/
theorem ArmsTypedI.shape_eq {Γ Δ p k S arms Γ' Δ' Q F} :
    ArmsTypedI P M Ψd Γ Δ p k S arms Γ' Δ' Q F → Δ'.shape = (Δ.set p k ∅).shape
  | .last _ h _ => h.shape_eq.trans (PCtx.shape_set_set _ _ _ _ _)
  | .cons _ h ha => by
      have h₁ := h.shape_eq.trans (PCtx.shape_set_set _ _ _ _ ∅)
      rw [PCtx.shape_join (h₁.trans ha.shape_eq.symm), h₁]
  | .skip _ ha => ha.shape_eq

end

/-- The arm a `match` runs is covered by the arms' joined inline typing (as `ArmsTyped.find`). -/
theorem ArmsTypedI.find {Γ Δ p k S arms Γ' Δ' Q F} :
    ArmsTypedI P M Ψd Γ Δ p k S arms Γ' Δ' Q F → ∀ {s c}, s ∈ S → arms.find? s = some c →
    ∃ Γc Δc Qc Fc, TypedI P M Ψd Γ (Δ.set p k {s}) c Γc Δc Qc Fc ∧ Γ'.Sub Γc ∧ Δc.Le Δ' ∧
      (∀ f b, Qc f b + f * ((Δ.set p k {s}).bg M + b) ≤ Q f b) ∧ (∀ f, Fc f ≤ F f)
  | .last _ h hrest, s, c, hs, hf => by
      simp only [Arms.find?] at hf
      split_ifs at hf with hst
      · cases hf; subst hst
        exact ⟨_, _, _, _, h, fun _ _ hx => hx, PCtx.Le.refl _, fun _ _ => le_rfl,
          fun _ => le_rfl⟩
      · exact absurd hs (hrest s (Arms.mem_states_of_find? hf))
  | .cons _ h ha, s, c, hs, hf => by
      have hsh := (h.shape_eq.trans (PCtx.shape_set_set _ _ _ _ ∅)).trans ha.shape_eq.symm
      simp only [Arms.find?] at hf
      split_ifs at hf with hst
      · cases hf; subst hst
        exact ⟨_, _, _, _, h, TCtx.inter_sub_left _ _, PCtx.le_join_left hsh,
          fun _ _ => le_max_left _ _, fun _ => le_max_left _ _⟩
      · obtain ⟨Γc, Δc, Qc, Fc, hc, hΓ, hΔ, hQ, hF⟩ := ha.find hs hf
        exact ⟨Γc, Δc, Qc, Fc, hc, fun x τ hx => hΓ x τ (TCtx.inter_sub_right _ _ x τ hx),
          hΔ.trans (PCtx.le_join_right hsh), fun f b => (hQ f b).trans (le_max_right _ _),
          fun f => (hF f).trans (le_max_right _ _)⟩
  | .skip hst ha, s, c, hs, hf => by
      simp only [Arms.find?] at hf
      split_ifs at hf with hst'
      · exact absurd (hst' ▸ hs) hst
      · exact ha.find hs hf

/-- Scaling is monotone in both factors (costs are `≥ 0`). -/
private theorem mul_mono' {f f' x x' : R} (hf : f ≤ f') (hx : x ≤ x') : f * x ≤ f' * x' :=
  mul_le_mul hf hx zero_le zero_le

mutual

/-- **Inline summaries are monotone** in the clock and the ambient background (as
`Typed.mono`, with no signature hypothesis: a call's summary is its body's). -/
theorem TypedI.mono (hM : M.WF) {Γ Δ c Γ' Δ' Q F} :
    TypedI P M Ψd Γ Δ c Γ' Δ' Q F → SummaryMono Q F
  | .skip => ⟨monotone_id, fun _ _ _ _ _ _ => le_rfl⟩
  | .assign _ _ => ⟨monotone_id, fun _ _ _ _ hf hb => mul_mono' hf (add_le_add le_rfl hb)⟩
  | .ite _ h₁ h₂ =>
      have ⟨hF₁, hQ₁⟩ := h₁.mono hM
      have ⟨hF₂, hQ₂⟩ := h₂.mono hM
      ⟨fun _ _ hf => max_le_max (hF₁ hf) (hF₂ hf), fun _ _ _ _ hf hb =>
        add_le_add (max_le_max (hQ₁ _ _ _ _ hf hb) (hQ₂ _ _ _ _ hf hb))
          (mul_mono' hf (add_le_add le_rfl hb))⟩
  | .transition _ _ _ => ⟨monotone_id, fun _ _ _ _ hf hb => mul_mono' hf (add_le_add le_rfl hb)⟩
  | .downgrade _ _ _ => ⟨monotone_id, fun _ _ _ _ hf hb => mul_mono' hf (add_le_add le_rfl hb)⟩
  | .clock _ => ⟨monotone_const, fun _ _ _ _ hf hb =>
      add_le_add (hM.clockCost_mono_left _ _ _ hf) (mul_mono' hf (add_le_add le_rfl hb))⟩
  | .seq h₁ h₂ =>
      have ⟨hF₁, hQ₁⟩ := h₁.mono hM
      have ⟨hF₂, hQ₂⟩ := h₂.mono hM
      ⟨hF₂.comp hF₁, fun _ _ _ _ hf hb =>
        add_le_add (hQ₁ _ _ _ _ hf hb) (hQ₂ _ _ _ _ (hF₁ hf) hb)⟩
  | .matchSt _ _ ha => ha.mono hM
  | .call _ _ _ _ hb _ _ =>
      have ⟨hF, hQ⟩ := hb.mono hM
      ⟨hF, fun _ _ _ _ hf hb' =>
        add_le_add (mul_mono' hf (add_le_add le_rfl hb'))
          (add_le_add (hQ _ _ _ _ hf (add_le_add hb' le_rfl))
            (mul_mono' (hF hf) (add_le_add le_rfl (add_le_add hb' le_rfl))))⟩

/-- Arms version of `TypedI.mono`. -/
theorem ArmsTypedI.mono (hM : M.WF) {Γ Δ p k S arms Γ' Δ' Q F} :
    ArmsTypedI P M Ψd Γ Δ p k S arms Γ' Δ' Q F → SummaryMono Q F
  | .last _ h _ =>
      have ⟨hF, hQ⟩ := h.mono hM
      ⟨hF, fun _ _ _ _ hf hb =>
        add_le_add (hQ _ _ _ _ hf hb) (mul_mono' hf (add_le_add le_rfl hb))⟩
  | .cons _ h ha =>
      have ⟨hF₁, hQ₁⟩ := h.mono hM
      have ⟨hF₂, hQ₂⟩ := ha.mono hM
      ⟨fun _ _ hf => max_le_max (hF₁ hf) (hF₂ hf), fun _ _ _ _ hf hb =>
        max_le_max (add_le_add (hQ₁ _ _ _ _ hf hb) (mul_mono' hf (add_le_add le_rfl hb)))
          (hQ₂ _ _ _ _ hf hb)⟩
  | .skip _ ha => ha.mono hM

end

/-- **Soundness of inline typing.**  If `c` is inline-typed with summaries `Q`, `F` and runs
from clock `K` with ambient peripherals `A`, from a state agreeing with its typing contexts, the
actual cost is at most `Q K (bg A)`, the exit clock at most `F K`, and the final state agrees
with the output contexts.  As `soundness`, but a call is bounded by its body's inline summary at
the caller's states — the induction hypothesis for the body's evaluation, with no signature
validity assumption. -/
theorem soundnessI (hM : M.WF) {Γ Δ c Γ' Δ' Q F} (ht : TypedI P M Ψd Γ Δ c Γ' Δ' Q F)
    {A σ S K σ' S' q' K'} (he : Eval M Ψd A σ S K c σ' S' q' K')
    (hσ : MemOK Γ σ) (hS : PeriphsOK Δ S) :
    q' ≤ Q K (ambBg M A) ∧ MemOK Γ' σ' ∧ PeriphsOK Δ' S' ∧ K' ≤ F K := by
  induction he generalizing Γ Δ Γ' Δ' Q F with
  | skip => cases ht; exact ⟨le_rfl, hσ, hS, le_rfl⟩
  | assign hev =>
    cases ht with
    | assign hty _ =>
      obtain ⟨v', hev', hty'⟩ := HasTy.eval hσ hty
      rw [hev] at hev'; cases hev'
      exact ⟨mul_mono' le_rfl (add_le_add (add_le_add le_rfl hS.bg_le) le_rfl),
        hσ.bind hty', hS, le_rfl⟩
  | iteTrue _ _ ih =>
    cases ht with
    | ite _ h₁ h₂ =>
      obtain ⟨hq, hσ', hS', hK⟩ := ih h₁ hσ hS
      have hsh := h₁.shape_eq.trans h₂.shape_eq.symm
      exact ⟨add_le_add (hq.trans (le_max_left _ _))
          (mul_mono' le_rfl (add_le_add (add_le_add le_rfl hS.bg_le) le_rfl)),
        hσ'.mono (TCtx.inter_sub_left _ _), hS'.mono (PCtx.le_join_left hsh),
        hK.trans (le_max_left _ _)⟩
  | iteFalse _ _ ih =>
    cases ht with
    | ite _ h₁ h₂ =>
      obtain ⟨hq, hσ', hS', hK⟩ := ih h₂ hσ hS
      have hsh := h₁.shape_eq.trans h₂.shape_eq.symm
      exact ⟨add_le_add (hq.trans (le_max_right _ _))
          (mul_mono' le_rfl (add_le_add (add_le_add le_rfl hS.bg_le) le_rfl)),
        hσ'.mono (TCtx.inter_sub_right _ _), hS'.mono (PCtx.le_join_right hsh),
        hK.trans (le_max_right _ _)⟩
  | transition hSp =>
    cases ht with
    | transition hp _ _ =>
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      exact ⟨mul_mono' le_rfl (add_le_add (add_le_add (M.transCost_le_maxTrans hs)
          (hS.erase _).bg_le) le_rfl),
        hσ, hS.set _ _ (Finset.mem_singleton_self _), le_rfl⟩
  | downgrade hSp =>
    cases ht with
    | downgrade hp _ _ =>
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      exact ⟨mul_mono' le_rfl (add_le_add (add_le_add (M.transCost_le_maxTrans hs)
          (hS.erase _).bg_le) le_rfl),
        hσ, hS.set _ _ (Finset.mem_singleton_self _), le_rfl⟩
  | clock =>
    cases ht with
    | clock _ =>
      exact ⟨add_le_add le_rfl (mul_mono' le_rfl (add_le_add hS.bg_le le_rfl)), hσ, hS, le_rfl⟩
  | seq _ _ ih₁ ih₂ =>
    cases ht with
    | seq h₁ h₂ =>
      obtain ⟨hq₁, hσ₁, hS₁, hK₁⟩ := ih₁ h₁ hσ hS
      obtain ⟨hq₂, hσ₂, hS₂, hK₂⟩ := ih₂ h₂ hσ₁ hS₁
      obtain ⟨hF₂, hQ₂⟩ := h₂.mono hM
      exact ⟨add_le_add hq₁ (hq₂.trans (hQ₂ _ _ _ _ hK₁ le_rfl)), hσ₂, hS₂, hK₂.trans (hF₂ hK₁)⟩
  | @matchSt A σ S K p arms k s c σ' S' q K' hSp hfind _ ih =>
    cases ht with
    | matchSt hp _ ha =>
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      obtain ⟨Γc, Δc, Qc, Fc, hc, hΓ, hΔ, hQ, hF⟩ := ha.find hs hfind
      have hSs : PeriphsOK (Δ.set p k {s}) S := by
        rw [← RPeriphs.set_eq_self hSp]; exact hS.set _ _ (Finset.mem_singleton_self _)
      obtain ⟨hq, hσ', hS', hK⟩ := ih hc hσ hSs
      exact ⟨(add_le_add hq (mul_mono' le_rfl (add_le_add hSs.bg_le le_rfl))).trans (hQ _ _),
        hσ'.mono hΓ, hS'.mono hΔ, hK.trans (hF _)⟩
  | @call A σ S K x g e p d v k s σb Sb qb Kb r s' hgd hev hSp heb hret hSb ihb =>
    cases ht with
    | call hg hty _ hp hb hretT hΔb =>
      rw [hgd] at hg; cases hg
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      obtain ⟨v', hev', hty'⟩ := HasTy.eval hσ hty
      rw [hev] at hev'; cases hev'
      obtain ⟨hqb, hσb, hSb', hKb⟩ := ihb hb (MemOK.arg hty') (PeriphsOK.single hs)
      obtain ⟨r', hret', hrty⟩ := HasTy.eval hσb hretT
      rw [hret] at hret'; cases hret'
      obtain ⟨-, hs'⟩ := hSb'.at hSb hΔb
      have hamb : ambBg M (A + (S.erase p).entries) ≤ ambBg M A + (Δ.erase p).bg M := by
        rw [ambBg_add_entries]; exact add_le_add le_rfl (hS.erase p).bg_le
      obtain ⟨hFb, hQb⟩ := hb.mono hM
      refine ⟨?_, hσ.bind hrty, hS.set _ _ hs', hKb⟩
      rw [add_assoc]
      refine add_le_add (mul_mono' le_rfl (add_le_add (add_le_add le_rfl hS.bg_le) le_rfl))
        (add_le_add (hqb.trans (hQb _ _ _ _ le_rfl hamb)) ?_)
      exact mul_mono' hKb (add_le_add (add_le_add le_rfl hSb'.bg_le) hamb)

/-! ### Precision: inline typing is never worse than checking

A checking derivation (`Typed`, calls instantiating declared signatures) converts to an inline
derivation (`TypedI`) with no larger summaries.  The conversion is narrowing again (`Typed.toI`
copies `Typed.narrow` case by case), except at a call: there the callee's body, typed inline from
the caller's (narrowed) states `S₀ ⊆ S ⊆ sIn`, costs at most the declared signature
(`SigsInline`).  `SigsInline` holds for the signatures of a program's declarations, by induction
along the declarations (`DeclsTyped.sigsInline`): each body converts, by `Typed.toI` against the
earlier signatures, narrowed from `sIn` to the caller's `S`. -/

/-- Setting a handle to fewer states gives a more precise context. -/
theorem PCtx.set_le_set (Δ : PCtx K St) (p : Var) (k : K) {S S' : Finset St} (h : S ⊆ S') :
    (Δ.set p k S).Le (Δ.set p k S') := by
  intro x
  rw [PCtx.set_apply, PCtx.set_apply]
  split_ifs
  · exact ⟨rfl, h⟩
  · exact PCtx.Le.refl Δ x

/-- A single handle with fewer states is more precise (a callee's entry context, narrowed). -/
theorem PCtx.single_le_single (p : Var) (k : K) {S S' : Finset St} (h : S ⊆ S') :
    PCtx.Le (Finsupp.single p (PEntry.live k S)) (Finsupp.single p (PEntry.live k S')) := by
  intro x
  rw [Finsupp.single_apply, Finsupp.single_apply]
  split_ifs
  · exact ⟨rfl, h⟩
  · exact trivial

/-- A single handle with a non-empty state set has non-empty state sets. -/
theorem PCtx.NonEmpty.single (p : Var) (k : K) {S : Finset St} (h : S.Nonempty) :
    PCtx.NonEmpty (Finsupp.single p (PEntry.live k S)) := by
  intro x k' T hx
  rw [Finsupp.single_apply] at hx
  split_ifs at hx
  cases hx; exact h

/-- A callee's body, inline-typed from entry states `S`, fits the declared signature `sig`: it
returns the declared type, exits in (non-empty) declared output states, and its T-FunDecl
summary is at most `sig`'s. -/
def BodyInline (P : Platform K St) (M : CostModel K St R) (Ψd : FCtx K St R) (d : FunDecl K St R)
    (sig : FunSig K St R) (S : Finset St) : Prop :=
  ∃ Γb Δb Qb Fb S', TypedI P M Ψd (TCtx.empty.bind d.arg d.argTy)
      (Finsupp.single d.parg (.live d.pKind S)) d.body Γb Δb Qb Fb ∧
    HasTy Γb d.ret d.retTy ∧ Δb d.parg = .live d.pKind S' ∧ S' ⊆ sig.sOut ∧ S'.Nonempty ∧
    (∀ f b, Qb f b + Fb f * (d.ret.cost M + Δb.bg M + b) ≤ sig.cost f b) ∧ (∀ f, Fb f ≤ sig.clk f)

/-- Every signature in `Ψ` is matched by its declaration in `Ψd`, inline-typed from **any**
non-empty set of declared entry states (`BodyInline`).  The hypothesis that lets a checking call
be replaced by an inline one. -/
def SigsInline (P : Platform K St) (M : CostModel K St R) (Ψd : FCtx K St R)
    (Ψ : SigCtx K St R) : Prop :=
  ∀ g sig, Ψ g = some sig → ∃ d, Ψd g = some d ∧ sig.argTy = d.argTy ∧ sig.pKind = d.pKind ∧
    sig.retTy = d.retTy ∧ ∀ S, S ⊆ sig.sIn → S.Nonempty → BodyInline P M Ψd d sig S

/-- The conclusion of `Typed.toI`: as `Narrowed`, with an inline derivation. -/
def NarrowedI (P : Platform K St) (M : CostModel K St R) (Ψd : FCtx K St R) (Γ₀ : TCtx K)
    (Δ₀ : PCtx K St) (c : Cmd St R) (Γ' : TCtx K) (Δ' : PCtx K St) (Q : R → R → R) (F : R → R) :
    Prop :=
  ∃ Γ₀' Δ₀' Q₀ F₀, TypedI P M Ψd Γ₀ Δ₀ c Γ₀' Δ₀' Q₀ F₀ ∧ Γ'.Sub Γ₀' ∧ Δ₀'.Le Δ' ∧
    Δ₀'.NonEmpty ∧ (∀ f b, Q₀ f b ≤ Q f b) ∧ (∀ f, F₀ f ≤ F f)

/-- Arms version of `NarrowedI`. -/
def ArmsNarrowedI (P : Platform K St) (M : CostModel K St R) (Ψd : FCtx K St R) (Γ₀ : TCtx K)
    (Δ₀ : PCtx K St) (p : Var) (k : K) (S₀ : Finset St) (arms : Arms St R) (Γ' : TCtx K)
    (Δ' : PCtx K St) (Q : R → R → R) (F : R → R) : Prop :=
  ∃ Γ₀' Δ₀' Q₀ F₀, ArmsTypedI P M Ψd Γ₀ Δ₀ p k S₀ arms Γ₀' Δ₀' Q₀ F₀ ∧ Γ'.Sub Γ₀' ∧
    Δ₀'.Le Δ' ∧ Δ₀'.NonEmpty ∧ (∀ f b, Q₀ f b ≤ Q f b) ∧ (∀ f, F₀ f ≤ F f)

mutual

/-- **Precision of inline typing** (with narrowing): a checking derivation from `Γ, Δ` gives an
inline derivation from any more precise `Γ₀ ⊇ Γ`, `Δ₀ ⊑ Δ` (non-empty), with more precise outputs
and no larger summaries.  As `Typed.narrow`, except at calls, where `SigsInline` bounds the
callee's body typed from the caller's states by the declared signature.  Narrowing is built in
because after a call the inline output states (the body's actual exit states) are fewer than
the declared `sOut`, so the rest of the program is typed from a more precise context. -/
theorem Typed.toI (hM : M.WF) (hΨm : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk)
    (hI : SigsInline P M Ψd Ψ) {Γ Δ c Γ' Δ' Q F} :
    Typed P M Ψ Γ Δ c Γ' Δ' Q F → ∀ {Γ₀ Δ₀}, Γ.Sub Γ₀ → Δ₀.Le Δ → Δ₀.NonEmpty →
      NarrowedI P M Ψd Γ₀ Δ₀ c Γ' Δ' Q F
  | .skip, _, _, hs, hle, hne => ⟨_, _, _, _, .skip, hs, hle, hne, fun _ _ => le_rfl, fun _ => le_rfl⟩
  | .assign hty hx, _, _, hs, hle, hne =>
    ⟨_, _, _, _, .assign (hty.weaken hs) (hle.absent hx), hs.bind _ _, hle, hne,
      fun _ _ => mul_le_mul_left'' (add_le_add (add_le_add le_rfl hle.bg_le) le_rfl),
      fun _ => le_rfl⟩
  | .ite hty h₁ h₂, _, _, hs, hle, hne => by
    obtain ⟨Γ₁, Δ₁, Q₁, F₁, d₁, hs₁, hle₁, hne₁, hQ₁, hF₁⟩ := h₁.toI hM hΨm hI hs hle hne
    obtain ⟨Γ₂, Δ₂, Q₂, F₂, d₂, hs₂, hle₂, hne₂, hQ₂, hF₂⟩ := h₂.toI hM hΨm hI hs hle hne
    exact ⟨_, _, _, _, .ite (hty.weaken hs) d₁ d₂, hs₁.inter hs₂,
      PCtx.join_le_join hle₁ hle₂ (d₁.shape_eq.trans d₂.shape_eq.symm), hne₁.join hne₂,
      fun f b => add_le_add (max_le_max (hQ₁ f b) (hQ₂ f b))
        (mul_le_mul_left'' (add_le_add (add_le_add le_rfl hle.bg_le) le_rfl)),
      fun f => max_le_max (hF₁ f) (hF₂ f)⟩
  | .transition hp hst hleS, _, _, hs, hle, hne => by
    obtain ⟨S₀, hS₀, hp₀⟩ := hle.live hp
    exact ⟨_, _, _, _, .transition hp₀ hst (fun s h => hleS s (hS₀ h)), hs, hle.set _ _ _,
      hne.set _ _ (Finset.singleton_nonempty _),
      fun f b => mul_le_mul_left'' (add_le_add (add_le_add (M.maxTrans_mono _ hS₀)
        (hle.erase _).bg_le) le_rfl), fun _ => le_rfl⟩
  | .downgrade hp hst hdg, _, _, hs, hle, hne => by
    obtain ⟨S₀, hS₀, hp₀⟩ := hle.live hp
    exact ⟨_, _, _, _, .downgrade hp₀ hst (fun s h => hdg s (hS₀ h)), hs, hle.set _ _ _,
      hne.set _ _ (Finset.singleton_nonempty _),
      fun f b => mul_le_mul_left'' (add_le_add (add_le_add (M.maxTrans_mono _ hS₀)
        (hle.erase _).bg_le) le_rfl), fun _ => le_rfl⟩
  | .clock hf, _, _, hs, hle, hne =>
    ⟨_, _, _, _, .clock hf, hs, hle, hne,
      fun _ _ => add_le_add le_rfl (mul_le_mul_left'' (add_le_add hle.bg_le le_rfl)),
      fun _ => le_rfl⟩
  | .seq h₁ h₂, _, _, hs, hle, hne => by
    obtain ⟨Γ₁, Δ₁, Q₁, F₁, d₁, hs₁, hle₁, hne₁, hQ₁, hF₁⟩ := h₁.toI hM hΨm hI hs hle hne
    obtain ⟨Γ₂, Δ₂, Q₂, F₂, d₂, hs₂, hle₂, hne₂, hQ₂, hF₂⟩ := h₂.toI hM hΨm hI hs₁ hle₁ hne₁
    have ⟨hm₂F, hm₂Q⟩ := d₂.mono hM
    exact ⟨_, _, _, _, .seq d₁ d₂, hs₂, hle₂, hne₂,
      fun f b => add_le_add (hQ₁ f b) ((hm₂Q _ _ _ _ (hF₁ f) le_rfl).trans (hQ₂ _ b)),
      fun f => (hm₂F (hF₁ f)).trans (hF₂ _)⟩
  | .matchSt hp hsub ha, _, _, hs, hle, hne => by
    obtain ⟨S₀, hS₀, hp₀⟩ := hle.live hp
    obtain ⟨s, hs₀⟩ := hne _ _ _ hp₀
    obtain ⟨Γa, Δa, Qa, Fa, da, hsa, hlea, hnea, hQa, hFa⟩ :=
      ha.toI hM hΨm hI hs hle hne hS₀ ⟨s, hs₀⟩ ⟨s, hs₀, hsub (hS₀ hs₀)⟩
    exact ⟨_, _, _, _, .matchSt hp₀ (hS₀.trans hsub) da, hsa, hlea, hnea, hQa, hFa⟩
  | .call hg hty hx hp hsub, _, _, hs, hle, hne => by
    obtain ⟨S₀, hS₀, hp₀⟩ := hle.live hp
    obtain ⟨d, hgd, hA, hK, hRt, hbody⟩ := hI _ _ hg
    obtain ⟨Γb, Δb, Qb, Fb, S', db, hret, hΔb, hS', hS'ne, hQb, hFb⟩ :=
      hbody S₀ (hS₀.trans hsub) (hne _ _ _ hp₀)
    rw [hA] at hty
    rw [hK] at hp₀ ⊢
    rw [hRt]
    exact ⟨_, _, _, _, .call hgd (hty.weaken hs) (hle.absent hx) hp₀ db hret hΔb,
      hs.bind _ _, (hle.set _ _ _).trans (PCtx.set_le_set _ _ _ hS'), hne.set _ _ hS'ne,
      fun f b => add_le_add (mul_le_mul_left'' (add_le_add (add_le_add le_rfl hle.bg_le) le_rfl))
        ((hQb f _).trans ((hΨm _ _ hg).2 _ _ _ _ le_rfl (add_le_add le_rfl (hle.erase _).bg_le))),
      hFb⟩

/-- Arms version of `Typed.toI` (as `ArmsTyped.narrow`). -/
theorem ArmsTyped.toI (hM : M.WF)
    (hΨm : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk)
    (hI : SigsInline P M Ψd Ψ) {Γ Δ p k S arms Γ' Δ' Q F} :
    ArmsTyped P M Ψ Γ Δ p k S arms Γ' Δ' Q F → ∀ {Γ₀ Δ₀ S₀}, Γ.Sub Γ₀ → Δ₀.Le Δ →
      Δ₀.NonEmpty → S₀ ⊆ S → S₀.Nonempty → (∃ s ∈ S₀, s ∈ arms.states) →
      ArmsNarrowedI P M Ψd Γ₀ Δ₀ p k S₀ arms Γ' Δ' Q F
  | @ArmsTyped.last _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st _ rest _ _ _ _ hst hc hrest, _, _, S₀, hs, hle, hne, hS₀,
      _, ⟨s, hs₀, hsa⟩ => by
    have hst₀ : st ∈ S₀ := by
      simp only [Arms.states, Finset.mem_insert] at hsa
      rcases hsa with rfl | hr
      · exact hs₀
      · exact absurd (hS₀ hs₀) (hrest s hr)
    obtain ⟨Γc, Δc, Qc, Fc, dc, hsc, hlec, hnec, hQc, hFc⟩ :=
      hc.toI hM hΨm hI hs (hle.set p k {st}) (hne.set _ _ (Finset.singleton_nonempty _))
    exact ⟨_, _, _, _, .last hst₀ dc (fun s' hr h => hrest s' hr (hS₀ h)), hsc, hlec, hnec,
      fun f b => add_le_add (hQc f b)
        (mul_le_mul_left'' (add_le_add (hle.set p k {st}).bg_le le_rfl)), hFc⟩
  | @ArmsTyped.cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st _ rest _ _ _ _ _ _ _ _ hst hc hr, _, _, S₀, hs, hle, hne,
      hS₀, hS₀ne, ⟨s, hs₀, hsa⟩ => by
    have hsh := hc.shape_eq.trans ((PCtx.shape_set_set _ _ _ _ ∅).trans hr.shape_eq.symm)
    by_cases hst₀ : st ∈ S₀
    · obtain ⟨Γc, Δc, Qc, Fc, dc, hsc, hlec, hnec, hQc, hFc⟩ :=
        hc.toI hM hΨm hI hs (hle.set p k {st}) (hne.set _ _ (Finset.singleton_nonempty _))
      by_cases hreach : ∃ s' ∈ S₀, s' ∈ rest.states
      · obtain ⟨Γr, Δr, Qr, Fr, dr, hsr, hler, hner, hQr, hFr⟩ :=
          hr.toI hM hΨm hI hs hle hne hS₀ hS₀ne hreach
        have hsh₀ := dc.shape_eq.trans ((PCtx.shape_set_set _ _ _ _ ∅).trans dr.shape_eq.symm)
        exact ⟨_, _, _, _, .cons hst₀ dc dr, hsc.inter hsr, PCtx.join_le_join hlec hler hsh₀,
          hnec.join hner,
          fun f b => max_le_max (add_le_add (hQc f b)
            (mul_le_mul_left'' (add_le_add (hle.set p k {st}).bg_le le_rfl))) (hQr f b),
          fun f => max_le_max (hFc f) (hFr f)⟩
      · exact ⟨_, _, _, _, .last hst₀ dc (fun s' h₁ h₂ => hreach ⟨s', h₂, h₁⟩),
          (TCtx.inter_sub_left _ _).trans hsc, hlec.trans (PCtx.le_join_left hsh), hnec,
          fun f b => (add_le_add (hQc f b) (mul_le_mul_left''
            (add_le_add (hle.set p k {st}).bg_le le_rfl))).trans (le_max_left _ _),
          fun f => (hFc f).trans (le_max_left _ _)⟩
    · have hreach : ∃ s' ∈ S₀, s' ∈ rest.states := by
        simp only [Arms.states, Finset.mem_insert] at hsa
        rcases hsa with rfl | hra
        · exact absurd hs₀ hst₀
        · exact ⟨s, hs₀, hra⟩
      obtain ⟨Γr, Δr, Qr, Fr, dr, hsr, hler, hner, hQr, hFr⟩ :=
        hr.toI hM hΨm hI hs hle hne hS₀ hS₀ne hreach
      exact ⟨_, _, _, _, .skip hst₀ dr, (TCtx.inter_sub_right _ _).trans hsr,
        hler.trans (PCtx.le_join_right hsh), hner,
        fun f b => (hQr f b).trans (le_max_right _ _),
        fun f => (hFr f).trans (le_max_right _ _)⟩
  | @ArmsTyped.skip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st _ rest _ _ _ _ hst hr, _, _, S₀, hs, hle, hne, hS₀, hS₀ne,
      ⟨s, hs₀, hsa⟩ => by
    have hst₀ : st ∉ S₀ := fun h => hst (hS₀ h)
    have hreach : ∃ s' ∈ S₀, s' ∈ rest.states := by
      simp only [Arms.states, Finset.mem_insert] at hsa
      rcases hsa with rfl | hra
      · exact absurd hs₀ hst₀
      · exact ⟨s, hs₀, hra⟩
    obtain ⟨Γr, Δr, Qr, Fr, dr, hsr, hler, hner, hQr, hFr⟩ :=
      hr.toI hM hΨm hI hs hle hne hS₀ hS₀ne hreach
    exact ⟨_, _, _, _, .skip hst₀ dr, hsr, hler, hner, hQr, hFr⟩

end

/-- T-FunDecl's summaries are monotone when the earlier signatures' are: they are the body's
(`Typed.mono`) plus the return expression at the exit clock.  Carried along the declarations
in `DeclsTyped.sigsInline`, which needs it for each prefix. -/
theorem FunDeclTyped.mono (hM : M.WF) (hΨm : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk)
    {d : FunDecl K St R} {sig : FunSig K St R} (hd : FunDeclTyped P M Ψ d sig) :
    SummaryMono sig.cost sig.clk := by
  obtain ⟨Γb, Δb, Qb, Fb, S', hb, -, -, -, hcost, hclk⟩ := hd.body
  obtain ⟨hF, hQ⟩ := hb.mono hM hΨm
  rw [hcost, hclk]
  exact ⟨hF, fun _ _ _ _ hf hb' =>
    add_le_add (hQ _ _ _ _ hf hb') (mul_mono' (hF hf) (add_le_add le_rfl hb'))⟩

/-- **A checked declaration inlines at any of its entry states.**  If `d` checks against `sig`
(with the earlier signatures inlinable), its body, typed inline from any non-empty `S ⊆ sIn`,
fits `sig`: convert the body's checking derivation by `Typed.toI`, narrowed from `sIn` to `S`. -/
theorem FunDeclTyped.inline (hM : M.WF)
    (hΨm : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk) (hI : SigsInline P M Ψd Ψ)
    {d : FunDecl K St R} {sig : FunSig K St R} (hd : FunDeclTyped P M Ψ d sig) {S : Finset St}
    (hS : S ⊆ sig.sIn) (hne : S.Nonempty) : BodyInline P M Ψd d sig S := by
  obtain ⟨Γb, Δb, Qb, Fb, S', hb, hret, hΔb, hS', hcost, hclk⟩ := hd.body
  rw [hd.sIn] at hS
  obtain ⟨Γ₀, Δ₀, Q₀, F₀, db, hs, hle, hne', hQ, hF⟩ :=
    hb.toI hM hΨm hI (fun _ _ h => h) (PCtx.single_le_single _ _ hS) (PCtx.NonEmpty.single _ _ hne)
  obtain ⟨S₀, hS₀, hp₀⟩ := hle.live hΔb
  refine ⟨_, _, _, _, S₀, db, hret.weaken hs, hp₀, hS₀.trans (by rw [hd.sOut]; exact hS'),
    hne' _ _ _ hp₀, fun f b => ?_, fun f => (hF f).trans (le_of_eq (congrFun hclk f).symm)⟩
  rw [hcost]
  exact add_le_add (hQ f b) (mul_mono' (hF f) (add_le_add (add_le_add le_rfl hle.bg_le) le_rfl))

/-- **Declarations typed in order are inlinable.**  Along `DeclsTyped`, each new signature is
inlinable (`FunDeclTyped.inline`, against the prefix) and monotone (`FunDeclTyped.mono`), so if
the initial signatures are, every signature in the final context is. -/
theorem DeclsTyped.sigsInline (hM : M.WF) {Ψ₀ ds Ψ'} (hds : DeclsTyped P M Ψ₀ ds Ψ') :
    (∀ d ∈ ds, Ψd d.name = some d) →
    (∀ g sig, Ψ₀ g = some sig → SummaryMono sig.cost sig.clk) →
    SigsInline P M Ψd Ψ₀ → SigsInline P M Ψd Ψ' := by
  induction hds with
  | nil => intro _ _ h; exact h
  | @cons Ψ d ds sig Ψ' hd _ ih =>
    intro hmem hΨm hI
    refine ih (fun d' hd' => hmem d' (List.mem_cons_of_mem _ hd')) ?_ ?_
    · intro g sig' hg
      by_cases h : g = d.name
      · subst h
        simp only [Function.update_self, Option.some.injEq] at hg
        subst hg
        exact hd.mono hM hΨm
      · rw [Function.update_of_ne h] at hg
        exact hΨm g sig' hg
    · intro g sig' hg
      by_cases h : g = d.name
      · subst h
        simp only [Function.update_self, Option.some.injEq] at hg
        subst hg
        exact ⟨d, hmem d (List.mem_cons_self ..), hd.argTy, hd.pKind, hd.retTy,
          fun S hS hne => hd.inline hM hΨm hI hS hne⟩
      · rw [Function.update_of_ne h] at hg
        exact hI g sig' hg

/-- The initial peripheral context has non-empty state sets (each handle is in its one initial
state). -/
theorem Program.initPCtx_nonEmpty (prog : Program K St R) : prog.initPCtx.NonEmpty := by
  unfold Program.initPCtx
  induction prog.periphs with
  | nil => intro x k T hx; cases hx
  | cons h hs ih => exact ih.set _ _ (Finset.singleton_nonempty _)

/-- **Precision, whole programs.**  A checked program's `main` is inline-typed with no larger
summaries: inline typing — calls charged at the states the caller actually passes — never
bounds a program worse than the declared signatures do. -/
theorem Program.Typed.precision (hM : M.WF) {prog : Program K St R} {Ψ Γ' Δ' Q F}
    (ht : prog.Typed P M Ψ Γ' Δ' Q F) :
    ∃ Γ₀' Δ₀' Q₀ F₀, TypedI P M prog.fctx TCtx.empty prog.initPCtx prog.main Γ₀' Δ₀' Q₀ F₀ ∧
      Γ'.Sub Γ₀' ∧ Δ₀'.Le Δ' ∧ (∀ f b, Q₀ f b ≤ Q f b) ∧ (∀ f, F₀ f ≤ F f) := by
  have hΨm : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk := fun g sig h => by
    obtain ⟨_, _, hv⟩ := Program.sigsValid hM ht g sig h
    exact hv.mono
  have hI : SigsInline P M prog.fctx Ψ :=
    ht.2.1.sigsInline hM (fun _ hd => Program.fctx_of_mem ht.1 hd)
      (fun _ _ h => by simp at h) (fun _ _ h => by simp at h)
  obtain ⟨Γ₀', Δ₀', Q₀, F₀, d, hs, hle, -, hQ, hF⟩ :=
    ht.2.2.toI hM hΨm hI (fun _ _ h => h) (PCtx.Le.refl _) prog.initPCtx_nonEmpty
  exact ⟨Γ₀', Δ₀', Q₀, F₀, d, hs, hle, hQ, hF⟩

/-! ### Accepted entry states

What a function accepts is a **predicate on entry-state sets**, `Accepts d S`: the body
inline-types from `S` (and the return expression types after it).  It is closed downward
(`Accepts.mono`, from narrowing for `TypedI`), and every set of declared entry states is
accepted (`Program.Typed.accepts`).  It is **not** closed under union — the typing is
path-insensitive: a `match` intersects its arms' variable contexts, so states each accepted
alone can fail together (`Heliod.Examples.EntrySets`).  So there is in general no largest
accepted set; `entrySet d`, the states accepted one at a time, contains every accepted set but
need not be accepted itself.  Inline typing never needs a single entry set: each call site
types the body from its own states (T-Call's premise in `TypedI` is `Accepts` at the caller's
`Δ p`). -/

mutual

/-- **Narrowing for inline typing** (as `Typed.narrow`): an inline derivation from `Γ, Δ` gives
one from any more precise `Γ₀ ⊇ Γ`, `Δ₀ ⊑ Δ` (non-empty), with more precise outputs and no larger
summaries.  At a call, the callee's body is narrowed from the caller's states to the fewer ones
(a sub-derivation, so the recursion is structural). -/
theorem TypedI.narrow (hM : M.WF) {Γ Δ c Γ' Δ' Q F} :
    TypedI P M Ψd Γ Δ c Γ' Δ' Q F → ∀ {Γ₀ Δ₀}, Γ.Sub Γ₀ → Δ₀.Le Δ → Δ₀.NonEmpty →
      NarrowedI P M Ψd Γ₀ Δ₀ c Γ' Δ' Q F
  | .skip, _, _, hs, hle, hne => ⟨_, _, _, _, .skip, hs, hle, hne, fun _ _ => le_rfl, fun _ => le_rfl⟩
  | .assign hty hx, _, _, hs, hle, hne =>
    ⟨_, _, _, _, .assign (hty.weaken hs) (hle.absent hx), hs.bind _ _, hle, hne,
      fun _ _ => mul_le_mul_left'' (add_le_add (add_le_add le_rfl hle.bg_le) le_rfl),
      fun _ => le_rfl⟩
  | .ite hty h₁ h₂, _, _, hs, hle, hne => by
    obtain ⟨Γ₁, Δ₁, Q₁, F₁, d₁, hs₁, hle₁, hne₁, hQ₁, hF₁⟩ := h₁.narrow hM hs hle hne
    obtain ⟨Γ₂, Δ₂, Q₂, F₂, d₂, hs₂, hle₂, hne₂, hQ₂, hF₂⟩ := h₂.narrow hM hs hle hne
    exact ⟨_, _, _, _, .ite (hty.weaken hs) d₁ d₂, hs₁.inter hs₂,
      PCtx.join_le_join hle₁ hle₂ (d₁.shape_eq.trans d₂.shape_eq.symm), hne₁.join hne₂,
      fun f b => add_le_add (max_le_max (hQ₁ f b) (hQ₂ f b))
        (mul_le_mul_left'' (add_le_add (add_le_add le_rfl hle.bg_le) le_rfl)),
      fun f => max_le_max (hF₁ f) (hF₂ f)⟩
  | .transition hp hst hleS, _, _, hs, hle, hne => by
    obtain ⟨S₀, hS₀, hp₀⟩ := hle.live hp
    exact ⟨_, _, _, _, .transition hp₀ hst (fun s h => hleS s (hS₀ h)), hs, hle.set _ _ _,
      hne.set _ _ (Finset.singleton_nonempty _),
      fun f b => mul_le_mul_left'' (add_le_add (add_le_add (M.maxTrans_mono _ hS₀)
        (hle.erase _).bg_le) le_rfl), fun _ => le_rfl⟩
  | .downgrade hp hst hdg, _, _, hs, hle, hne => by
    obtain ⟨S₀, hS₀, hp₀⟩ := hle.live hp
    exact ⟨_, _, _, _, .downgrade hp₀ hst (fun s h => hdg s (hS₀ h)), hs, hle.set _ _ _,
      hne.set _ _ (Finset.singleton_nonempty _),
      fun f b => mul_le_mul_left'' (add_le_add (add_le_add (M.maxTrans_mono _ hS₀)
        (hle.erase _).bg_le) le_rfl), fun _ => le_rfl⟩
  | .clock hf, _, _, hs, hle, hne =>
    ⟨_, _, _, _, .clock hf, hs, hle, hne,
      fun _ _ => add_le_add le_rfl (mul_le_mul_left'' (add_le_add hle.bg_le le_rfl)),
      fun _ => le_rfl⟩
  | .seq h₁ h₂, _, _, hs, hle, hne => by
    obtain ⟨Γ₁, Δ₁, Q₁, F₁, d₁, hs₁, hle₁, hne₁, hQ₁, hF₁⟩ := h₁.narrow hM hs hle hne
    obtain ⟨Γ₂, Δ₂, Q₂, F₂, d₂, hs₂, hle₂, hne₂, hQ₂, hF₂⟩ := h₂.narrow hM hs₁ hle₁ hne₁
    have ⟨hm₂F, hm₂Q⟩ := d₂.mono hM
    exact ⟨_, _, _, _, .seq d₁ d₂, hs₂, hle₂, hne₂,
      fun f b => add_le_add (hQ₁ f b) ((hm₂Q _ _ _ _ (hF₁ f) le_rfl).trans (hQ₂ _ b)),
      fun f => (hm₂F (hF₁ f)).trans (hF₂ _)⟩
  | .matchSt hp hsub ha, _, _, hs, hle, hne => by
    obtain ⟨S₀, hS₀, hp₀⟩ := hle.live hp
    obtain ⟨s, hs₀⟩ := hne _ _ _ hp₀
    obtain ⟨Γa, Δa, Qa, Fa, da, hsa, hlea, hnea, hQa, hFa⟩ :=
      ha.narrow hM hs hle hne hS₀ ⟨s, hs₀⟩ ⟨s, hs₀, hsub (hS₀ hs₀)⟩
    exact ⟨_, _, _, _, .matchSt hp₀ (hS₀.trans hsub) da, hsa, hlea, hnea, hQa, hFa⟩
  | .call hg hty hx hp hb hret hΔb, _, _, hs, hle, hne => by
    obtain ⟨S₀, hS₀, hp₀⟩ := hle.live hp
    obtain ⟨Γb, Δb, Qb, Fb, db, hsb, hleb, hneb, hQb, hFb⟩ :=
      hb.narrow hM (fun _ _ h => h) (PCtx.single_le_single _ _ hS₀)
        (PCtx.NonEmpty.single _ _ (hne _ _ _ hp₀))
    obtain ⟨S₀', hS₀', hpb⟩ := hleb.live hΔb
    have ⟨_, hmQ⟩ := hb.mono hM
    exact ⟨_, _, _, _, .call hg (hty.weaken hs) (hle.absent hx) hp₀ db (hret.weaken hsb) hpb,
      hs.bind _ _, (hle.set _ _ _).trans (PCtx.set_le_set _ _ _ hS₀'), hne.set _ _ (hneb _ _ _ hpb),
      fun f b => add_le_add (mul_le_mul_left'' (add_le_add (add_le_add le_rfl hle.bg_le) le_rfl))
        (add_le_add ((hQb f _).trans (hmQ _ _ _ _ le_rfl (add_le_add le_rfl (hle.erase _).bg_le)))
          (mul_mono' (hFb f) (add_le_add (add_le_add le_rfl hleb.bg_le)
            (add_le_add le_rfl (hle.erase _).bg_le)))),
      hFb⟩

/-- Arms version of `TypedI.narrow` (as `ArmsTyped.narrow`). -/
theorem ArmsTypedI.narrow (hM : M.WF) {Γ Δ p k S arms Γ' Δ' Q F} :
    ArmsTypedI P M Ψd Γ Δ p k S arms Γ' Δ' Q F → ∀ {Γ₀ Δ₀ S₀}, Γ.Sub Γ₀ → Δ₀.Le Δ →
      Δ₀.NonEmpty → S₀ ⊆ S → S₀.Nonempty → (∃ s ∈ S₀, s ∈ arms.states) →
      ArmsNarrowedI P M Ψd Γ₀ Δ₀ p k S₀ arms Γ' Δ' Q F
  | @ArmsTypedI.last _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st _ rest _ _ _ _ hst hc hrest, _, _, S₀, hs, hle, hne, hS₀,
      _, ⟨s, hs₀, hsa⟩ => by
    have hst₀ : st ∈ S₀ := by
      simp only [Arms.states, Finset.mem_insert] at hsa
      rcases hsa with rfl | hr
      · exact hs₀
      · exact absurd (hS₀ hs₀) (hrest s hr)
    obtain ⟨Γc, Δc, Qc, Fc, dc, hsc, hlec, hnec, hQc, hFc⟩ :=
      hc.narrow hM hs (hle.set p k {st}) (hne.set _ _ (Finset.singleton_nonempty _))
    exact ⟨_, _, _, _, .last hst₀ dc (fun s' hr h => hrest s' hr (hS₀ h)), hsc, hlec, hnec,
      fun f b => add_le_add (hQc f b)
        (mul_le_mul_left'' (add_le_add (hle.set p k {st}).bg_le le_rfl)), hFc⟩
  | @ArmsTypedI.cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st _ rest _ _ _ _ _ _ _ _ hst hc hr, _, _, S₀, hs, hle, hne,
      hS₀, hS₀ne, ⟨s, hs₀, hsa⟩ => by
    have hsh := hc.shape_eq.trans ((PCtx.shape_set_set _ _ _ _ ∅).trans hr.shape_eq.symm)
    by_cases hst₀ : st ∈ S₀
    · obtain ⟨Γc, Δc, Qc, Fc, dc, hsc, hlec, hnec, hQc, hFc⟩ :=
        hc.narrow hM hs (hle.set p k {st}) (hne.set _ _ (Finset.singleton_nonempty _))
      by_cases hreach : ∃ s' ∈ S₀, s' ∈ rest.states
      · obtain ⟨Γr, Δr, Qr, Fr, dr, hsr, hler, hner, hQr, hFr⟩ :=
          hr.narrow hM hs hle hne hS₀ hS₀ne hreach
        have hsh₀ := dc.shape_eq.trans ((PCtx.shape_set_set _ _ _ _ ∅).trans dr.shape_eq.symm)
        exact ⟨_, _, _, _, .cons hst₀ dc dr, hsc.inter hsr, PCtx.join_le_join hlec hler hsh₀,
          hnec.join hner,
          fun f b => max_le_max (add_le_add (hQc f b)
            (mul_le_mul_left'' (add_le_add (hle.set p k {st}).bg_le le_rfl))) (hQr f b),
          fun f => max_le_max (hFc f) (hFr f)⟩
      · exact ⟨_, _, _, _, .last hst₀ dc (fun s' h₁ h₂ => hreach ⟨s', h₂, h₁⟩),
          (TCtx.inter_sub_left _ _).trans hsc, hlec.trans (PCtx.le_join_left hsh), hnec,
          fun f b => (add_le_add (hQc f b) (mul_le_mul_left''
            (add_le_add (hle.set p k {st}).bg_le le_rfl))).trans (le_max_left _ _),
          fun f => (hFc f).trans (le_max_left _ _)⟩
    · have hreach : ∃ s' ∈ S₀, s' ∈ rest.states := by
        simp only [Arms.states, Finset.mem_insert] at hsa
        rcases hsa with rfl | hra
        · exact absurd hs₀ hst₀
        · exact ⟨s, hs₀, hra⟩
      obtain ⟨Γr, Δr, Qr, Fr, dr, hsr, hler, hner, hQr, hFr⟩ :=
        hr.narrow hM hs hle hne hS₀ hS₀ne hreach
      exact ⟨_, _, _, _, .skip hst₀ dr, (TCtx.inter_sub_right _ _).trans hsr,
        hler.trans (PCtx.le_join_right hsh), hner,
        fun f b => (hQr f b).trans (le_max_right _ _),
        fun f => (hFr f).trans (le_max_right _ _)⟩
  | @ArmsTypedI.skip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st _ rest _ _ _ _ hst hr, _, _, S₀, hs, hle, hne, hS₀, hS₀ne,
      ⟨s, hs₀, hsa⟩ => by
    have hst₀ : st ∉ S₀ := fun h => hst (hS₀ h)
    have hreach : ∃ s' ∈ S₀, s' ∈ rest.states := by
      simp only [Arms.states, Finset.mem_insert] at hsa
      rcases hsa with rfl | hra
      · exact absurd hs₀ hst₀
      · exact ⟨s, hs₀, hra⟩
    obtain ⟨Γr, Δr, Qr, Fr, dr, hsr, hler, hner, hQr, hFr⟩ :=
      hr.narrow hM hs hle hne hS₀ hS₀ne hreach
    exact ⟨_, _, _, _, .skip hst₀ dr, hsr, hler, hner, hQr, hFr⟩

end

/-- `d` **accepts** the entry states `S`: `S` is non-empty and the body inline-types from the
argument and the peripheral parameter in `S`, after which the return expression has the declared
type.  This is exactly what an inline call from a caller with `Δ p = S` requires of `d`. -/
def Accepts (P : Platform K St) (M : CostModel K St R) (Ψd : FCtx K St R) (d : FunDecl K St R)
    (S : Finset St) : Prop :=
  S.Nonempty ∧ ∃ Γb Δb Qb Fb, TypedI P M Ψd (TCtx.empty.bind d.arg d.argTy)
    (Finsupp.single d.parg (.live d.pKind S)) d.body Γb Δb Qb Fb ∧ HasTy Γb d.ret d.retTy

/-- **Accepted sets are closed downward**: fewer (still some) entry states are accepted, by
narrowing the body (`TypedI.narrow`). -/
theorem Accepts.mono (hM : M.WF) {d : FunDecl K St R} {S S₀ : Finset St}
    (h : Accepts P M Ψd d S) (hS : S₀ ⊆ S) (hne : S₀.Nonempty) : Accepts P M Ψd d S₀ := by
  obtain ⟨_, Γb, Δb, Qb, Fb, hb, hret⟩ := h
  obtain ⟨Γ₀, Δ₀, Q₀, F₀, db, hs, -, -, -, -⟩ :=
    hb.narrow hM (fun _ _ h => h) (PCtx.single_le_single _ _ hS) (PCtx.NonEmpty.single _ _ hne)
  exact ⟨hne, Γ₀, Δ₀, Q₀, F₀, db, hret.weaken hs⟩

/-- The **entry states** of `d`: those it accepts on their own.  Contains every accepted set
(`Accepts.subset_entrySet`), but need not be accepted itself (accepted sets are not closed under
union; `Heliod.Examples.EntrySets`). -/
def entrySet (P : Platform K St) (M : CostModel K St R) (Ψd : FCtx K St R)
    (d : FunDecl K St R) : Set St :=
  {s | Accepts P M Ψd d {s}}

/-- Every accepted set lies within the entry states (downward closure, at singletons). -/
theorem Accepts.subset_entrySet (hM : M.WF) {d : FunDecl K St R} {S : Finset St}
    (h : Accepts P M Ψd d S) : (S : Set St) ⊆ entrySet P M Ψd d :=
  fun s hs => h.mono hM (Finset.singleton_subset_iff.2 hs) (Finset.singleton_nonempty s)

/-- A checked program's signatures are inlinable for its declarations (`DeclsTyped.sigsInline`
from the empty context). -/
theorem Program.Typed.sigsInline (hM : M.WF) {prog : Program K St R} {Ψ Γ' Δ' Q F}
    (ht : prog.Typed P M Ψ Γ' Δ' Q F) : SigsInline P M prog.fctx Ψ :=
  ht.2.1.sigsInline hM (fun _ hd => Program.fctx_of_mem ht.1 hd)
    (fun _ _ h => by simp at h) (fun _ _ h => by simp at h)

/-- **Declared entry states are accepted.**  In a checked program, each function accepts every
non-empty set of its declared entry states `sIn`, so `sIn` lies within its inferred entry
states: inference accepts at least what checking does. -/
theorem Program.Typed.accepts (hM : M.WF) {prog : Program K St R} {Ψ Γ' Δ' Q F}
    (ht : prog.Typed P M Ψ Γ' Δ' Q F) {g sig} (hg : Ψ g = some sig) :
    ∃ d, prog.fctx g = some d ∧
      (∀ S, S ⊆ sig.sIn → S.Nonempty → Accepts P M prog.fctx d S) ∧
      (sig.sIn : Set St) ⊆ entrySet P M prog.fctx d := by
  obtain ⟨d, hgd, -, -, -, hbody⟩ := ht.sigsInline hM g sig hg
  have hacc : ∀ S, S ⊆ sig.sIn → S.Nonempty → Accepts P M prog.fctx d S := fun S hS hne => by
    obtain ⟨Γb, Δb, Qb, Fb, -, db, hret, -⟩ := hbody S hS hne
    exact ⟨hne, Γb, Δb, Qb, Fb, db, hret⟩
  exact ⟨d, hgd, hacc, fun s hs =>
    hacc {s} (Finset.singleton_subset_iff.2 hs) (Finset.singleton_nonempty s)⟩
