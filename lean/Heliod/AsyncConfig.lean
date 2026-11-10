import Heliod.AsyncInvariants
import Heliod.Adequacy

/-!
# Async soundness — pieces 2–3c: typing machine configurations, and every step pays

The potential argument (`ASYNC_PROOF_PLAN.md`).  Main results: `CfgTyped.mstep` (a typed
configuration steps, timers drained, to a typed configuration whose potential plus the step's
cost is at most the old potential) and `CfgTyped.steps` (whole runs).  Calls are allowed while
threads are pending: the spawner may be suspended under frozen callees (`TView`, `StackOK`).
Building blocks:

* **Join algebra.**  `PCtx.join` is commutative and associative (`PCtx.join_comm`,
  `PCtx.join_assoc`).
* **Thread-context order** `ThreadCtx.Le Θ Θ'`: the same pending threads, each window in `Θ'`
  being the window in `Θ` joined with something.  Windows only ever grow by joins, so this is
  the order in which "the typing knows less" (`le_join_left` / `le_join_right` after branches).
* **`ArmsTypedA.find`**: the arm a `match` runs is typed with `p` narrowed, below the joined
  result (port of `ArmsTyped.find`).
* **Control-stack typing** `CtlTyped`: commands and waiting `await` frames typed in sequence,
  linked by `PCtx.Widen` (unchanged, or joined with the untaken branches' outputs).  This is
  what lets a branch's continuation, typed from the joined contexts, follow the branch actually
  taken.  `CtlTyped.mono`: its summary is monotone.
* **Stacks, threads, configurations**: `StackOK`, `ThreadOK`, `CfgTyped` (see the plan).
* **Activation agreement** `ActOK`: the activation's memory agrees with `Γ`, its view of the
  devices corresponds to the store (`Corr`, `Rev` from `Heliod.Adequacy`) and agrees with `Δ`,
  and the background of everything it cannot see is at most `b`.  `ActOK.bg_le`: the machine's
  background charge is at most the typed one.
-/

-- Lemmas here use the large section context (order, subtraction) selectively; tracking each
-- one's `omit` list is noise, so the unused-section-variable linter is off in this file.
set_option linter.unusedSectionVars false

variable {K St R : Type} [DecidableEq K] [DecidableEq St]

/-! ### Join algebra -/

/-- Entry joins commute. -/
theorem PEntry.join_comm (a b : PEntry K St) : PEntry.join a b = PEntry.join b a := by
  rcases a with _ | ⟨k, S⟩ <;> rcases b with _ | ⟨k', S'⟩ <;> simp only [PEntry.join]
  by_cases h : k = k'
  · subst h; simp [Finset.union_comm]
  · simp [h, Ne.symm h]

/-- Entry joins associate. -/
theorem PEntry.join_assoc (a b c : PEntry K St) :
    PEntry.join (PEntry.join a b) c = PEntry.join a (PEntry.join b c) := by
  rcases a with _ | ⟨k₁, S₁⟩ <;> rcases b with _ | ⟨k₂, S₂⟩ <;> rcases c with _ | ⟨k₃, S₃⟩ <;>
    simp only [PEntry.join] <;> split_ifs <;> simp_all [Finset.union_assoc]

/-- Context joins commute. -/
theorem PCtx.join_comm (Δ₁ Δ₂ : PCtx K St) : Δ₁.join Δ₂ = Δ₂.join Δ₁ := by
  ext x; simp [PEntry.join_comm]

/-- Context joins associate. -/
theorem PCtx.join_assoc (Δ₁ Δ₂ Δ₃ : PCtx K St) :
    (Δ₁.join Δ₂).join Δ₃ = Δ₁.join (Δ₂.join Δ₃) := by
  ext x; simp [PEntry.join_assoc]

/-! ### Thread-context order -/

omit [DecidableEq K] [DecidableEq St] in
/-- `Same` is reflexive. -/
theorem ThreadTy.Same.refl {R : Type} (a : ThreadTy K St R) : a.Same a :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [DecidableEq K] [DecidableEq St] in
/-- `Same` is symmetric. -/
theorem ThreadTy.Same.symm {R : Type} {a b : ThreadTy K St R} (h : a.Same b) : b.Same a :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

omit [DecidableEq K] [DecidableEq St] in
/-- `Same` is transitive. -/
theorem ThreadTy.Same.trans {R : Type} {a b c : ThreadTy K St R} (h₁ : a.Same b)
    (h₂ : b.Same c) : a.Same c :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    h₁.2.2.2.1.trans h₂.2.2.2.1, h₁.2.2.2.2.trans h₂.2.2.2.2⟩

/-- `Θ ⊑ Θ'`: the same pending threads, each window in `Θ'` being the corresponding window in
`Θ` joined with something.  The order in which the typing knows less. -/
def ThreadCtx.Le {R : Type} (Θ₁ Θ₂ : ThreadCtx K St R) : Prop :=
  ∀ t, (Θ₁ t = none ∧ Θ₂ t = none) ∨
    ∃ a b w, Θ₁ t = some a ∧ Θ₂ t = some b ∧ a.Same b ∧ b.win = a.win.join w

namespace ThreadCtx

variable {R : Type}

/-- `⊑` is reflexive. -/
theorem Le.refl (Θ : ThreadCtx K St R) : Θ.Le Θ := by
  intro t
  rcases h : Θ t with _ | a
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨a, a, a.win, rfl, rfl, ThreadTy.Same.refl a, (PCtx.join_self _).symm⟩

/-- `⊑` is transitive. -/
theorem Le.trans {Θ₁ Θ₂ Θ₃ : ThreadCtx K St R} (h₁ : Θ₁.Le Θ₂) (h₂ : Θ₂.Le Θ₃) : Θ₁.Le Θ₃ := by
  intro t
  rcases h₁ t with ⟨e₁, e₂⟩ | ⟨a, b, w₁, e₁, e₂, hab, hw₁⟩
  · rcases h₂ t with ⟨_, e₃⟩ | ⟨_, _, _, e₂', _, _, _⟩
    · exact Or.inl ⟨e₁, e₃⟩
    · rw [e₂] at e₂'; cases e₂'
  · rcases h₂ t with ⟨e₂', _⟩ | ⟨b', c, w₂, e₂', e₃, hbc, hw₂⟩
    · rw [e₂] at e₂'; cases e₂'
    · rw [e₂] at e₂'; cases e₂'
      exact Or.inr ⟨a, c, w₁.join w₂, e₁, e₃, hab.trans hbc,
        by rw [hw₂, hw₁, PCtx.join_assoc]⟩

/-- A branch's threads are below the join. -/
theorem le_join_left {Θ₁ Θ₂ : ThreadCtx K St R} (hs : Θ₁.SameThreads Θ₂) :
    Θ₁.Le (Θ₁.join Θ₂) := by
  intro t
  rcases hs t with ⟨e₁, _⟩ | ⟨a, b, e₁, e₂, _⟩
  · exact Or.inl ⟨e₁, by simp [ThreadCtx.join, e₁]⟩
  · exact Or.inr ⟨a, { a with win := a.win.join b.win }, b.win, e₁,
      by simp [ThreadCtx.join, e₁, e₂], ThreadTy.Same.refl a, rfl⟩

/-- The other branch's threads are below the join too. -/
theorem le_join_right {Θ₁ Θ₂ : ThreadCtx K St R} (hs : Θ₁.SameThreads Θ₂) :
    Θ₂.Le (Θ₁.join Θ₂) := by
  intro t
  rcases hs t with ⟨e₁, e₂⟩ | ⟨a, b, e₁, e₂, hab⟩
  · exact Or.inl ⟨e₂, by simp [ThreadCtx.join, e₁]⟩
  · refine Or.inr ⟨b, { a with win := a.win.join b.win }, a.win, e₂,
      by simp [ThreadCtx.join, e₁, e₂], ?_, ?_⟩
    · exact (show b.Same { a with win := a.win.join b.win } from hab.symm)
    · exact PCtx.join_comm _ _


/-- The same pending threads (same names, each with the same captured handle, kind, envelope,
exit states and declared bound; windows may differ). -/
def SameIds (Θ₁ Θ₂ : ThreadCtx K St R) : Prop :=
  ∀ t, (Θ₁ t = none ↔ Θ₂ t = none) ∧ ∀ a b, Θ₁ t = some a → Θ₂ t = some b → a.Same b

omit [DecidableEq K] [DecidableEq St] in
/-- `SameIds` is reflexive. -/
theorem SameIds.refl (Θ : ThreadCtx K St R) : Θ.SameIds Θ :=
  fun _ => ⟨Iff.rfl, fun a b ha hb => by rw [ha] at hb; cases hb; exact ThreadTy.Same.refl a⟩

omit [DecidableEq K] [DecidableEq St] in
/-- `SameIds` is transitive. -/
theorem SameIds.trans {Θ₁ Θ₂ Θ₃ : ThreadCtx K St R} (h₁ : Θ₁.SameIds Θ₂) (h₂ : Θ₂.SameIds Θ₃) :
    Θ₁.SameIds Θ₃ := by
  intro t
  refine ⟨(h₁ t).1.trans (h₂ t).1, fun a c ha hc => ?_⟩
  rcases e : Θ₂ t with _ | b
  · exact absurd ((h₁ t).1.2 e) (by rw [ha]; simp)
  · exact ((h₁ t).2 a b ha e).trans ((h₂ t).2 b c e hc)

/-- Thread contexts in the `⊑` order have the same threads. -/
theorem SameIds.of_le {Θ₁ Θ₂ : ThreadCtx K St R} (h : Θ₁.Le Θ₂) : Θ₁.SameIds Θ₂ := by
  intro t
  rcases h t with ⟨e₁, e₂⟩ | ⟨a, b, w, e₁, e₂, hab, _⟩
  · exact ⟨by simp [e₁, e₂], fun a b ha => by rw [e₁] at ha; cases ha⟩
  · refine ⟨by simp [e₁, e₂], fun a' b' ha hb => ?_⟩
    rw [e₁] at ha; rw [e₂] at hb; cases ha; cases hb; exact hab

/-- Observing a context keeps the threads. -/
theorem SameIds.observe (Θ : ThreadCtx K St R) (Δ : PCtx K St) : Θ.SameIds (Θ.observe Δ) := by
  intro t
  refine ⟨by simp [ThreadCtx.observe], fun a b ha hb => ?_⟩
  simp only [ThreadCtx.observe, ha, Option.map_some, Option.some.injEq] at hb
  subst hb
  exact ThreadTy.Same.refl a

omit [DecidableEq K] [DecidableEq St] in
/-- Two empty thread contexts have the same (no) threads. -/
theorem SameIds.of_empty {Θ₁ Θ₂ : ThreadCtx K St R} (h₁ : Θ₁.IsEmpty) (h₂ : Θ₂.IsEmpty) :
    Θ₁.SameIds Θ₂ :=
  fun t => ⟨by simp [h₁ t, h₂ t], fun a _ ha => by rw [h₁ t] at ha; cases ha⟩

/-- Emptiness is preserved upward in `⊑`. -/
theorem IsEmpty.of_le {Θ₁ Θ₂ : ThreadCtx K St R} (h : Θ₁.IsEmpty) (hle : Θ₁.Le Θ₂) :
    Θ₂.IsEmpty := fun t => ((SameIds.of_le hle t).1.1 (h t))

/-- Observing an empty thread context leaves it empty. -/
theorem IsEmpty.observe {Θ : ThreadCtx K St R} (h : Θ.IsEmpty) (Δ : PCtx K St) :
    (Θ.observe Δ).IsEmpty := fun t => by simp [ThreadCtx.observe, h t]

end ThreadCtx

variable [CommSemiring R] [LinearOrder R] [OrderBot R]
variable {P : Platform K St} {M : CostModel K St R} {Ψ : SigCtxA K St R}

/-! ### Captured handles keep their envelopes -/

namespace ThreadCtx

variable {R : Type}

/-- **Captured handles are tracked**: every pending thread's handle is bound, at the thread's
kind, to a set containing the thread's envelope `V`, and distinct pending threads capture
distinct handles.  The spawning activation's agreement then survives the captured device moving
anywhere in its envelope (by the thread, or by hardware) — `StackOK.move`. -/
def CapOK (Θ : ThreadCtx K St R) (Δ : PCtx K St) : Prop :=
  (∀ t th, Θ t = some th → ∃ V', Δ th.p = .live th.k V' ∧ th.V ⊆ V') ∧
  ∀ t₁ t₂ th₁ th₂, Θ t₁ = some th₁ → Θ t₂ = some th₂ → th₁.p = th₂.p → t₁ = t₂

/-- A thread of an observed context is a thread of the original, with a larger window. -/
theorem observe_some {Θ : ThreadCtx K St R} {Δo : PCtx K St} {t : Var} {th : ThreadTy K St R}
    (h : Θ.observe Δo t = some th) :
    ∃ a, Θ t = some a ∧ th = { a with win := a.win.join Δo } := by
  simp only [ThreadCtx.observe, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, ha, rfl⟩

omit [DecidableEq K] [DecidableEq St] in
/-- A thread of an erased context is a thread of the original. -/
theorem erase_some {Θ : ThreadCtx K St R} {t₀ t : Var} {th : ThreadTy K St R}
    (h : Θ.erase t₀ t = some th) : Θ t = some th ∧ t ≠ t₀ := by
  unfold ThreadCtx.erase at h
  by_cases e : t = t₀
  · subst e; simp at h
  · rw [Function.update_of_ne e] at h; exact ⟨h, e⟩

/-- A thread of a joined context comes from both sides. -/
theorem join_some {Θ₁ Θ₂ : ThreadCtx K St R} {t : Var} {th : ThreadTy K St R}
    (h : Θ₁.join Θ₂ t = some th) :
    ∃ a b, Θ₁ t = some a ∧ Θ₂ t = some b ∧ th = { a with win := a.win.join b.win } := by
  simp only [ThreadCtx.join] at h
  split at h
  · rename_i a b ha hb
    cases h
    exact ⟨a, b, ha, hb, rfl⟩
  · cases h

/-- A thread above in `⊑` comes from one below, the same spawned thread. -/
theorem le_some {Θ Θ' : ThreadCtx K St R} (hle : Θ.Le Θ') {t : Var} {b : ThreadTy K St R}
    (h : Θ' t = some b) : ∃ a, Θ t = some a ∧ a.Same b := by
  rcases hle t with ⟨_, e₂⟩ | ⟨a, b', _, e₁, e₂, hab, _⟩
  · rw [e₂] at h; cases h
  · rw [e₂] at h; cases h; exact ⟨a, e₁, hab⟩

/-- Observing keeps the captured handles. -/
theorem captures_of_observe {Θ : ThreadCtx K St R} {Δo : PCtx K St} {p : Var}
    (h : (Θ.observe Δo).Captures p) : Θ.Captures p := by
  obtain ⟨t, th, ht, rfl⟩ := h
  obtain ⟨a, ha, rfl⟩ := observe_some ht
  exact ⟨t, a, ha, rfl⟩

/-- Observing keeps `CapOK`. -/
theorem CapOK.observe {Θ : ThreadCtx K St R} {Δ : PCtx K St} (h : Θ.CapOK Δ)
    (Δo : PCtx K St) : (Θ.observe Δo).CapOK Δ := by
  refine ⟨fun t th ht => ?_, fun t₁ t₂ th₁ th₂ h₁ h₂ hp => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := observe_some ht
    exact h.1 t a ha
  · obtain ⟨a, ha, rfl⟩ := observe_some h₁
    obtain ⟨b, hb, rfl⟩ := observe_some h₂
    exact h.2 t₁ t₂ a b ha hb hp

omit [DecidableEq K] [DecidableEq St] in
/-- Setting a handle no pending thread captured keeps `CapOK`. -/
theorem CapOK.set {Θ : ThreadCtx K St R} {Δ : PCtx K St} (h : Θ.CapOK Δ) {p : Var}
    (hp : ¬ Θ.Captures p) (k : K) (S : Finset St) : Θ.CapOK (Δ.set p k S) := by
  refine ⟨fun t th ht => ?_, h.2⟩
  have hne : th.p ≠ p := fun e => hp ⟨t, th, ht, e⟩
  simp only [PCtx.set_apply, hne, ↓reduceIte]
  exact h.1 t th ht

omit [DecidableEq K] [DecidableEq St] in
/-- Removing a thread keeps `CapOK`. -/
theorem CapOK.erase {Θ : ThreadCtx K St R} {Δ : PCtx K St} (h : Θ.CapOK Δ) (t₀ : Var) :
    (Θ.erase t₀).CapOK Δ :=
  ⟨fun t th ht => h.1 t th (erase_some ht).1,
    fun t₁ t₂ th₁ th₂ h₁ h₂ hp => h.2 t₁ t₂ th₁ th₂ (erase_some h₁).1 (erase_some h₂).1 hp⟩

/-- Weakening the thread context and enlarging the peripheral context keeps `CapOK`. -/
theorem CapOK.of_le {Θ Θ' : ThreadCtx K St R} {Δ Δ' : PCtx K St} (h : Θ.CapOK Δ)
    (hΘ : Θ.Le Θ') (hΔ : Δ.Le Δ') : Θ'.CapOK Δ' := by
  refine ⟨fun t b hb => ?_, fun t₁ t₂ b₁ b₂ h₁ h₂ hp => ?_⟩
  · obtain ⟨a, ha, hab⟩ := le_some hΘ hb
    obtain ⟨hp, hk, hV, _, _⟩ := hab
    obtain ⟨V', hV', hsub⟩ := h.1 t a ha
    have hx := hΔ a.p
    rw [hV'] at hx
    cases hd : Δ' a.p with
    | absent => rw [hd] at hx; exact absurd hx (by simp [PEntry.Le])
    | live k'' V'' =>
      rw [hd] at hx
      obtain ⟨rfl, hsub'⟩ := hx
      exact ⟨V'', by rw [← hp, ← hk, hd], hV ▸ hsub.trans hsub'⟩
  · obtain ⟨a₁, ha₁, hab₁⟩ := le_some hΘ h₁
    obtain ⟨a₂, ha₂, hab₂⟩ := le_some hΘ h₂
    exact h.2 t₁ t₂ a₁ a₂ ha₁ ha₂ (hab₁.1.trans (hp.trans hab₂.1.symm))

/-- Joining two branches that agree on their threads keeps `CapOK` (each captured handle's
set is a union of two sets containing the envelope). -/
theorem CapOK.join {Θ₁ Θ₂ : ThreadCtx K St R} {Δ₁ Δ₂ : PCtx K St} (h₁ : Θ₁.CapOK Δ₁)
    (h₂ : Θ₂.CapOK Δ₂) (hs : Θ₁.SameThreads Θ₂) : (Θ₁.join Θ₂).CapOK (Δ₁.join Δ₂) := by
  refine ⟨fun t th ht => ?_, fun t₁ t₂ th₁ th₂ e₁ e₂ hp => ?_⟩
  · obtain ⟨a, b, ha, hb, rfl⟩ := join_some ht
    have hab : a.Same b := by
      rcases hs t with ⟨e, _⟩ | ⟨a', b', ea, eb, hs'⟩
      · rw [ha] at e; cases e
      · rw [ha] at ea; rw [hb] at eb; cases ea; cases eb; exact hs'
    obtain ⟨A, hA, hsubA⟩ := h₁.1 t a ha
    obtain ⟨B, hB, _⟩ := h₂.1 t b hb
    obtain ⟨hp, hk, _, _, _⟩ := hab
    rw [← hp, ← hk] at hB
    refine ⟨A ∪ B, ?_, hsubA.trans Finset.subset_union_left⟩
    show PEntry.join (Δ₁ a.p) (Δ₂ a.p) = _
    rw [hA, hB]
    simp [PEntry.join]
  · obtain ⟨a₁, _, ha₁, _, rfl⟩ := join_some e₁
    obtain ⟨a₂, _, ha₂, _, rfl⟩ := join_some e₂
    exact h₁.2 t₁ t₂ a₁ a₂ ha₁ ha₂ hp

/-- An observed context has the same threads as anything the original did. -/
theorem SameThreads.observe_left {Θ₁ Θ₂ : ThreadCtx K St R} (hs : Θ₁.SameThreads Θ₂)
    (Δo : PCtx K St) : (Θ₁.observe Δo).SameThreads Θ₂ := by
  intro t
  rcases hs t with ⟨e₁, e₂⟩ | ⟨a, b, e₁, e₂, hab⟩
  · exact Or.inl ⟨by simp [ThreadCtx.observe, e₁], e₂⟩
  · exact Or.inr ⟨{ a with win := a.win.join Δo }, b, by simp [ThreadCtx.observe, e₁], e₂, hab⟩

/-- **A spawn keeps `CapOK`**: the new thread captures a handle no other thread captured, bound
exactly to its envelope. -/
theorem CapOK.spawn {Θ : ThreadCtx K St R} {Δ : PCtx K St} (h : Θ.CapOK Δ) {p : Var}
    (hp : ¬ Θ.Captures p) (Δo : PCtx K St) (tid : Var) (th₀ : ThreadTy K St R) {k : K}
    {S : Finset St} (hp₀ : th₀.p = p) (hk₀ : th₀.k = k) (hV₀ : th₀.V = S) :
    ThreadCtx.CapOK (Function.update (Θ.observe Δo) tid (some th₀)) (Δ.set p k S) := by
  have hpo : ¬ (Θ.observe Δo).Captures p := fun hc => hp (captures_of_observe hc)
  have hO := (h.observe Δo).set hpo k S
  refine ⟨fun t th ht => ?_, fun t₁ t₂ th₁ th₂ e₁ e₂ hpe => ?_⟩
  · by_cases e : t = tid
    · subst e
      simp only [Function.update_self, Option.some.injEq] at ht
      subst ht
      exact ⟨S, by rw [hp₀, hk₀, PCtx.set_apply]; simp, hV₀ ▸ subset_rfl⟩
    · rw [Function.update_of_ne e] at ht
      exact hO.1 t th ht
  · by_cases a₁ : t₁ = tid <;> by_cases a₂ : t₂ = tid
    · exact a₁.trans a₂.symm
    · subst a₁
      simp only [Function.update_self, Option.some.injEq] at e₁
      subst e₁
      rw [Function.update_of_ne a₂] at e₂
      exact absurd ⟨t₂, th₂, e₂, hpe.symm.trans hp₀⟩ hpo
    · subst a₂
      simp only [Function.update_self, Option.some.injEq] at e₂
      subst e₂
      rw [Function.update_of_ne a₁] at e₁
      exact absurd ⟨t₁, th₁, e₁, hpe.trans hp₀⟩ hpo
    · rw [Function.update_of_ne a₁] at e₁
      rw [Function.update_of_ne a₂] at e₂
      exact hO.2 t₁ t₂ th₁ th₂ e₁ e₂ hpe

end ThreadCtx

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] in
/-- No pending threads: nothing captured. -/
theorem ThreadCtx.CapOK.empty {Δ : PCtx K St} : (ThreadCtx.empty : ThreadCtx K St R).CapOK Δ :=
  ⟨fun _ _ h => (by cases h), fun _ _ _ _ h => (by cases h)⟩

set_option linter.unusedSectionVars false in
mutual

/-- **Typing keeps captured handles tracked** (`ThreadCtx.CapOK`).  Commands never move a
captured handle (`¬ Captures` on transitions, matches, calls and spawns), joins only enlarge
its set, a spawn binds the new handle exactly to its envelope, and an `await` releases its
thread's handle (no other thread captured it). -/
theorem TypedA.capOK {fz Γ Δ Θ c Γ' Δ' Θ' W Q F} :
    TypedA P M Ψ fz Γ Δ Θ c Γ' Δ' Θ' W Q F → Θ.CapOK Δ → Θ'.CapOK Δ'
  | .skip, h => h
  | .assign _ _, h => h
  | .ite _ h₁ h₂ hs, h => (h₁.capOK h).join (h₂.capOK h) hs
  | .transition _ hnc _ _, h => (h.set hnc _ _).observe _
  | .transitionU _ hnc _ _, h => (h.set hnc _ _).observe _
  | .downgrade _ hnc _ _, h => (h.set hnc _ _).observe _
  | .clock _ _ _, h => h
  | .seq h₁ h₂, h => h₂.capOK (h₁.capOK h)
  | .matchSt _ hnc _ ha, h => ha.capOK h hnc
  | .call _ _ _ _ _ hnc _, h => ((h.set hnc _ _).observe _).observe _
  | .async _ hnc _ _ _ _ _ _ _ _, h => h.spawn hnc _ _ _ rfl rfl rfl
  | .await (th := th) (tid := tid) hth _ _ hfb hs _ _, h =>
      have hE := h.erase tid
      have hnc : ¬ (Θ.erase tid).Captures th.p := by
        rintro ⟨t', th', ht', hp'⟩
        obtain ⟨ht'', hne⟩ := ThreadCtx.erase_some ht'
        exact hne (h.2 t' tid th' th ht'' hth hp')
      ((hE.set hnc _ _).observe _).join (hfb.capOK hE) (hs.observe_left _)

/-- Arms version of `TypedA.capOK`: each arm runs with the uncaptured `p` narrowed. -/
theorem ArmsTypedA.capOK {fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F} :
    ArmsTypedA P M Ψ fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F → Θ.CapOK Δ → ¬ Θ.Captures p →
    Θ'.CapOK Δ'
  | .last _ hc _, h, hnc => hc.capOK ((h.set hnc _ _).observe _)
  | .cons _ hc ha hs, h, hnc => (hc.capOK ((h.set hnc _ _).observe _)).join (ha.capOK h hnc) hs
  | .skip _ ha, h, hnc => ha.capOK h hnc

end

/-! ### Links between control-stack entries -/

/-- **The links a control stack may use**, from one entry's output context `Δ` to the next
entry's input `Δ'`: either nothing changes (sequencing), or `Δ'` joins `Δ` with a sibling
context of the same shape — the other branches of an `if` / `match` the run did not take, whose
join the rest of the program was typed from.  These are exactly the links that stepping
creates.  With `cl` (thread stacks), siblings must be closed under hardware steps, so links
keep the current context closed and a hardware step on the thread's device stays within it.

(A more principled alternative is to have no links at all and retype the rest of the program
from the branch's own output, by a narrowing lemma; see `ASYNC_PROOF_PLAN.md`.) -/
def PCtx.Widen (P : Platform K St) (cl : Bool) (Δ Δ' : PCtx K St) : Prop :=
  Δ' = Δ ∨ ∃ Δ₂ : PCtx K St, Δ₂.shape = Δ.shape ∧ (cl = true → Δ₂.HWClosed P) ∧ Δ' = Δ.join Δ₂

namespace PCtx.Widen

variable {P : Platform K St} {cl : Bool}

/-- No change is a link. -/
theorem refl (Δ : PCtx K St) : PCtx.Widen P cl Δ Δ := Or.inl rfl

/-- Joining a sibling of the same shape is a link. -/
theorem join_left {Δ Δ₂ : PCtx K St} (hsh : Δ.shape = Δ₂.shape)
    (hc : cl = true → Δ₂.HWClosed P) : PCtx.Widen P cl Δ (Δ.join Δ₂) :=
  Or.inr ⟨Δ₂, hsh.symm, hc, rfl⟩

/-- Joining a sibling on the left is a link too (joins commute). -/
theorem join_right {Δ₁ Δ : PCtx K St} (hsh : Δ₁.shape = Δ.shape)
    (hc : cl = true → Δ₁.HWClosed P) : PCtx.Widen P cl Δ (Δ₁.join Δ) := by
  rw [PCtx.join_comm]; exact join_left hsh.symm hc

/-- A link only forgets information. -/
theorem le {Δ Δ' : PCtx K St} (h : PCtx.Widen P cl Δ Δ') : Δ.Le Δ' := by
  rcases h with rfl | ⟨Δ₂, hsh, _, rfl⟩
  · exact PCtx.Le.refl _
  · exact PCtx.le_join_left hsh.symm

/-- A link keeps the shape. -/
theorem shape_eq {Δ Δ' : PCtx K St} (h : PCtx.Widen P cl Δ Δ') : Δ'.shape = Δ.shape := by
  rcases h with rfl | ⟨Δ₂, hsh, _, rfl⟩
  · rfl
  · exact PCtx.shape_join hsh.symm

/-- Links compose (the siblings join). -/
theorem trans {Δ Δm Δ' : PCtx K St} (h₁ : PCtx.Widen P cl Δ Δm) (h₂ : PCtx.Widen P cl Δm Δ') :
    PCtx.Widen P cl Δ Δ' := by
  rcases h₁ with rfl | ⟨A, hA, hcA, rfl⟩
  · exact h₂
  rcases h₂ with rfl | ⟨B, hB, hcB, rfl⟩
  · exact Or.inr ⟨A, hA, hcA, rfl⟩
  refine Or.inr ⟨A.join B, ?_, fun h => (hcA h).join (hcB h), PCtx.join_assoc _ _ _⟩
  have hB' : B.shape = Δ.shape := hB.trans (PCtx.shape_join hA.symm)
  exact (PCtx.shape_join (hA.trans hB'.symm)).trans hA

/-- In a thread stack, a link from a closed context leads to a closed context. -/
theorem closed {Δ Δ' : PCtx K St} (h : PCtx.Widen P cl Δ Δ') (hcl : cl = true)
    (hΔ : Δ.HWClosed P) : Δ'.HWClosed P := by
  rcases h with rfl | ⟨Δ₂, _, hc, rfl⟩
  · exact hΔ
  · exact hΔ.join (hc hcl)

end PCtx.Widen

/-- Weakening a thread context keeps exit states, hence their closure. -/
theorem ThreadCtx.SOutClosed.of_le {R : Type} {P : Platform K St} {Θ Θ' : ThreadCtx K St R}
    (h : Θ.SOutClosed P) (hle : Θ.Le Θ') : Θ'.SOutClosed P := by
  intro t th ht
  rcases hle t with ⟨_, e₂⟩ | ⟨a, b, _, e₁, e₂, hab, _⟩
  · rw [e₂] at ht; cases ht
  · rw [e₂] at ht; cases ht
    obtain ⟨_, hk, _, hs, _⟩ := hab
    rw [← hk, ← hs]; exact h t a e₁

/-! ### The arm a `match` runs -/

/-- **The arm a `match` runs is covered by the arms' joined typing** (async version of
`ArmsTyped.find`): for a reachable state `s`, the selected arm is typed with `p` narrowed to
`hwClose {s}`, its outputs and visited context are below the joined ones, and its summary plus the narrowed `match`
step is below the joined summary.  The arm's output reaches the joined one by a link
(`PCtx.Widen`): the join with the other arms' outputs, which are closed under hardware steps
when the context is (`cl`). -/
theorem ArmsTypedA.find [IsOrderedRing R] (hP : P.WF) (hΨc : SigsClosedA P Ψ) {cl : Bool}
    {fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F} :
    ArmsTypedA P M Ψ fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F →
    (cl = true → Δ.HWClosed P ∧ Θ.SOutClosed P) → ∀ {s c}, s ∈ S →
    arms.find? s = some c →
    ∃ Γc Δc Θc Wc Qc Fc, TypedA P M Ψ fz Γ (Δ.set p k (P.hwClose k {s}))
        (Θ.observe (Δ.set p k (P.hwClose k {s}))) c Γc Δc Θc Wc Qc Fc ∧
      Γ'.Sub Γc ∧ PCtx.Widen P cl Δc Δ' ∧ Θc.Le Θ' ∧ Wc.Le W ∧
      (∀ f b, Qc f b + f * ((Δ.set p k (P.hwClose k {s})).bg M + b) ≤ Q f b) ∧
      (∀ f, Fc f ≤ F f)
  | .last _ h hrest, _, s, c, hs, hf => by
      simp only [Arms.find?] at hf
      split_ifs at hf with hst
      · cases hf; subst hst
        exact ⟨_, _, _, _, _, _, h, fun _ _ hx => hx, PCtx.Widen.refl _, ThreadCtx.Le.refl _, PCtx.Le.refl _,
          fun _ _ => le_rfl, fun _ => le_rfl⟩
      · exact absurd hs (hrest s (Arms.mem_states_of_find? hf))
  | .cons _ h ha hsame, hcl, s, c, hs, hf => by
      have hsh : _ := ((h.shape_eq.1.trans (PCtx.shape_set_set _ _ _ _ ∅)).trans
        ha.shape_eq.1.symm)
      have hshW : _ := (h.shape_eq.2.trans (PCtx.shape_set_set _ _ _ _ ∅)).trans
        ha.shape_eq.2.symm
      simp only [Arms.find?] at hf
      split_ifs at hf with hst
      · cases hf; subst hst
        exact ⟨_, _, _, _, _, _, h, TCtx.inter_sub_left _ _,
          PCtx.Widen.join_left hsh fun h' => (ha.hwClosed hP hΨc (hcl h').1 (hcl h').2).1,
          ThreadCtx.le_join_left hsame, PCtx.le_join_left hshW, fun _ _ => le_max_left _ _,
          fun _ => le_max_left _ _⟩
      · obtain ⟨Γc, Δc, Θc, Wc, Qc, Fc, hc, hΓ, hΔ, hΘ, hW, hQ, hF⟩ := ha.find hP hΨc hcl hs hf
        exact ⟨Γc, Δc, Θc, Wc, Qc, Fc, hc, fun x τ hx => hΓ x τ (TCtx.inter_sub_right _ _ x τ hx),
          hΔ.trans (PCtx.Widen.join_right hsh fun h' => (h.hwClosed hP hΨc
            ((hcl h').1.set (hP.hwClose_idem _ _)) ((hcl h').2.observe _)).1), hΘ.trans (ThreadCtx.le_join_right hsame),
          hW.trans (PCtx.le_join_right hshW),
          fun f b => (hQ f b).trans (le_max_right _ _), fun f => (hF f).trans (le_max_right _ _)⟩
  | .skip hst ha, hcl, s, c, hs, hf => by
      simp only [Arms.find?] at hf
      split_ifs at hf with hst'
      · exact absurd (hst' ▸ hs) hst
      · exact ha.find hP hΨc hcl hs hf

/-! ### Control stacks -/

variable [Sub R]
variable {C : PCtx K St → Prop} {cl : Bool}

/-- **The waiting allowance of an `await` frame** with remaining budget `rem` at clock `f`: `rem + f`
ticks' worth (T-Await-Timeout's `n + f`: the extra `f` pays for the last tick overshooting the
budget), and nothing once the budget is spent (`rem = 0`: the frame can only time out or finish). -/
def waitAllow (rem f : R) : R := if rem = 0 then 0 else rem + f

/-- **Typing of an activation's control stack**: its entries in sequence, each one's outputs
linked to the next one's inputs: `Γ`, `Θ` may forget information; `Δ` only by a `PCtx.Widen` link
(unchanged, or joined with a same-shape sibling — the untaken branches; with `cl`, closed under
hardware steps).  Summaries compose as in T-Seq.  Every visited context (and the final context)
satisfies the ceiling `C`.  Each link also records that the windows of pending threads have the context's shape and cover
it (invariants established by `TypedA.winShape` / `TypedA.winCover`).

* `cmd`: a command, typed by `TypedA`.
* `awaitW`: a waiting `await` frame for thread `tid` with remaining budget `rem`.  It is typed
  like T-Await-Timeout, except that the waiting allowance is `waitAllow rem f` ticks of
  `maxBg V + cost(Δ ∖ p) + b`. -/
inductive CtlTyped (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtxA K St R)
    (C : PCtx K St → Prop) (cl : Bool) :
    Bool → TCtx K → PCtx K St → ThreadCtx K St R → List (Ctl St R) →
    TCtx K → PCtx K St → ThreadCtx K St R → (R → R → R) → (R → R) → Prop where
  | nil {fz Γ Δ Θ} : C Δ → CtlTyped P M Ψ C cl fz Γ Δ Θ [] Γ Δ Θ (fun _ _ => 0) (fun f => f)
  | cmd {fz Γ Δ Θ c Γ₁ Δ₁ Θ₁ W Q₁ F₁ Γ₁' Δ₁' Θ₁' rest Γ₂ Δ₂ Θ₂ Q₂ F₂} :
      TypedA P M Ψ fz Γ Δ Θ c Γ₁ Δ₁ Θ₁ W Q₁ F₁ →
      C W →
      Γ₁'.Sub Γ₁ → PCtx.Widen P cl Δ₁ Δ₁' → Θ₁.Le Θ₁' →
      Θ₁'.WinShape Δ₁'.shape → Θ₁'.WinCover Δ₁' →
      CtlTyped P M Ψ C cl fz Γ₁' Δ₁' Θ₁' rest Γ₂ Δ₂ Θ₂ Q₂ F₂ →
      CtlTyped P M Ψ C cl fz Γ Δ Θ (.cmd c :: rest) Γ₂ Δ₂ Θ₂
        (fun f b => Q₁ f b + Q₂ (F₁ f) b) (fun f => F₂ (F₁ f))
  | awaitW {fz Γ Δ Θ tid id rem fb th Γf Δf Θf Wf Qf Ff Sfb Γ₁' Δ₁' Θ₁' rest Γ₂ Δ₂ Θ₂ Q₂ F₂} :
      Θ tid = some th → Δ th.p = .live th.k th.V →
      (th.win.erase th.p).bg M ≤ th.amb →
      TypedA P M Ψ fz Γ Δ (Θ.erase tid) fb Γf Δf Θf Wf Qf Ff →
      C Wf →
      (Θ.erase tid).SameThreads Θf →
      Δf th.p = .live th.k Sfb → (∀ s ∈ Sfb, P.stable th.k s) →
      Γ₁'.Sub (Γ.inter Γf) → PCtx.Widen P cl ((Δ.set th.p th.k th.sOut).join Δf) Δ₁' →
      (((Θ.erase tid).observe (Δ.set th.p th.k th.sOut)).join Θf).Le Θ₁' →
      Θ₁'.WinShape Δ₁'.shape → Θ₁'.WinCover Δ₁' →
      CtlTyped P M Ψ C cl fz Γ₁' Δ₁' Θ₁' rest Γ₂ Δ₂ Θ₂ Q₂ F₂ →
      CtlTyped P M Ψ C cl fz Γ Δ Θ (.awaitW tid id rem fb :: rest) Γ₂ Δ₂ Θ₂
        (fun f b => waitAllow rem f * (M.maxBg th.k th.V + (Δ.erase th.p).bg M + b) + Qf f b
          + Q₂ (max (Ff f) f) b)
        (fun f => F₂ (max (Ff f) f))

variable [IsOrderedRing R] [CanonicallyOrderedAdd R] [OrderedSub R]

omit [OrderBot R] [Sub R] [CanonicallyOrderedAdd R] [OrderedSub R] in
/-- The waiting allowance grows with the clock. -/
theorem waitAllow_mono {rem f f' : R} (h : f ≤ f') : waitAllow rem f ≤ waitAllow rem f' := by
  unfold waitAllow
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl h

omit [OrderBot R] [Sub R] [IsOrderedRing R] [OrderedSub R] in
/-- The waiting allowance is at most T-Await-Timeout's `n + f`. -/
theorem waitAllow_le {rem f : R} : waitAllow rem f ≤ rem + f := by
  unfold waitAllow
  split_ifs
  · exact zero_le
  · exact le_rfl

omit [OrderBot R] in
/-- **A waiting tick fits the allowance**: one tick `K` plus what is left after lowering the
budget by `K` is within the allowance before.  If the budget was at least `K`, the allowance
drops by exactly `K`; if the tick overshoots it, the budget is spent and the allowance becomes
`0` (the extra `f` of `rem + f` paid for the overshoot).  No cancellation is needed. -/
theorem waitAllow_tick {rem K : R} (h : 0 < rem) :
    K + waitAllow (rem - K) K ≤ waitAllow rem K := by
  unfold waitAllow
  simp only [ne_of_gt h, ↓reduceIte]
  split_ifs with h0
  · rw [add_zero]; exact le_add_self
  · have hK : K ≤ rem := by
      by_contra hlt
      exact h0 (tsub_eq_zero_of_le (le_of_lt (not_le.1 hlt)))
    rw [← add_assoc, add_tsub_cancel_of_le hK]

omit [Sub R] [OrderedSub R] in
/-- A control stack's summary is monotone (from `TypedA.mono`). -/
theorem CtlTyped.mono (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk)
    {fz Γ Δ Θ ctl Γ' Δ' Θ' Q F} (h : CtlTyped P M Ψ C cl fz Γ Δ Θ ctl Γ' Δ' Θ' Q F) :
    SummaryMono Q F := by
  induction h with
  | nil => exact ⟨monotone_id, fun _ _ _ _ _ _ => le_rfl⟩
  | cmd hc _ _ _ _ _ _ _ ih =>
    obtain ⟨hF₁, hQ₁⟩ := hc.mono hM hΨ
    obtain ⟨hF₂, hQ₂⟩ := ih
    exact ⟨hF₂.comp hF₁, fun _ _ _ _ hf hb =>
      add_le_add (hQ₁ _ _ _ _ hf hb) (hQ₂ _ _ _ _ (hF₁ hf) hb)⟩
  | awaitW _ _ _ hfb _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨hFf, hQf⟩ := hfb.mono hM hΨ
    obtain ⟨hF₂, hQ₂⟩ := ih
    exact ⟨fun _ _ hf => hF₂ (max_le_max (hFf hf) hf), fun _ _ _ _ hf hb =>
      add_le_add (add_le_add (mul_le_mul (waitAllow_mono hf)
        (add_le_add le_rfl hb) zero_le zero_le) (hQf _ _ _ _ hf hb))
        (hQ₂ _ _ _ _ (max_le_max (hFf hf) hf) hb)⟩
/-! ### Activations agreeing with their typing -/

/-- **An activation agrees with its typing.**  Memory agrees with `Γ`; the activation's view of
the devices (visible handles `S`, with the rest summarized as `Ae`) corresponds to the store
(`Corr`, `Rev`), agrees with `Δ`, and the background of everything the activation cannot see
is at most `b`. -/
def ActOK (M : CostModel K St R) (Γ : TCtx K) (Δ : PCtx K St) (b : R) (σ : Mem)
    (H : Var → Option Dev) (D : RPeriphs K St) (Am : Multiset (K × St)) : Prop :=
  MemOK Γ σ ∧ ∃ S Ae, Corr H D S Am Ae ∧ Rev H D S ∧ PeriphsOK Δ S ∧ ambBg M Ae ≤ b

omit [DecidableEq K] [DecidableEq St] [CanonicallyOrderedAdd R] [Sub R] [OrderedSub R] in
/-- **The machine's background charge is within the typed one**: every device plus the outer
ambient costs at most `cost(Δ) + b`. -/
theorem ActOK.bg_le {Γ Δ b σ H D Am} (h : ActOK M Γ Δ b σ H D Am) :
    D.bg M + ambBg M Am ≤ Δ.bg M + b := by
  obtain ⟨_, S, Ae, hC, _, hS, hb⟩ := h
  rw [← hC.bg_eq M]
  exact add_le_add hS.bg_le hb

omit [DecidableEq K] [DecidableEq St] [OrderBot R] [IsOrderedRing R] [CanonicallyOrderedAdd R] [Sub R]
  [OrderedSub R] in
/-- Agreement survives forgetting information (a less precise `Γ` and `Δ`). -/
theorem ActOK.weaken {Γ Γ' Δ Δ' b σ H D Am} (h : ActOK M Γ Δ b σ H D Am) (hΓ : Γ'.Sub Γ)
    (hΔ : Δ.Le Δ') : ActOK M Γ' Δ' b σ H D Am := by
  obtain ⟨hσ, S, Ae, hC, hR, hS, hb⟩ := h
  exact ⟨hσ.mono hΓ, S, Ae, hC, hR, hS.mono hΔ, hb⟩

/-! ### One step of an activation's local commands -/

/-- Commands that step within their activation: everything except calls (which push an
activation) and `async` / `await` (piece 3). -/
def Cmd.Local {St R : Type} : Cmd St R → Prop
  | .call .. => False
  | .async .. => False
  | .await .. => False
  | _ => True

omit [DecidableEq K] [DecidableEq St] [OrderBot R] [Sub R] [OrderedSub R] in
/-- A charge `f * x` grows with `x` (all costs are `≥ 0`). -/
private theorem mul_le_mul_left'' {f x x' : R} (hx : x ≤ x') : f * x ≤ f * x' :=
  mul_le_mul_of_nonneg_left hx zero_le

omit [DecidableEq K] [DecidableEq St] [LinearOrder R] [OrderBot R] [IsOrderedRing R] [Sub R]
  [CanonicallyOrderedAdd R] [OrderedSub R] in
/-- Rearranging the three parts of a sequential charge. -/
private theorem add_three (q A B : R) : q + (A + B) = A + q + B := by
  rw [← add_assoc, add_comm q A]

omit [CanonicallyOrderedAdd R] [Sub R] [OrderedSub R] in
/-- **In a thread stack, contexts stay closed under hardware steps across a command and its
link**: the command's output is closed (`TypedA.hwClosed`) and the link only joins closed
siblings.  This is what lets a hardware step on a running thread's device stay within the
thread's current context. -/
theorem CtlTyped.next_closed (hP : P.WF) (hΨc : SigsClosedA P Ψ)
    {fz Γ Δ Θ c Γ₁ Δ₁ Θ₁ W Q₁ F₁ Δ₁' Θ₁'}
    (hc : TypedA P M Ψ fz Γ Δ Θ c Γ₁ Δ₁ Θ₁ W Q₁ F₁) (hΔ : PCtx.Widen P cl Δ₁ Δ₁')
    (hΘ : Θ₁.Le Θ₁') (hcl : cl = true → Δ.HWClosed P ∧ Θ.SOutClosed P) :
    cl = true → Δ₁'.HWClosed P ∧ Θ₁'.SOutClosed P := fun h =>
  have hc' := hc.hwClosed hP hΨc (hcl h).1 (hcl h).2
  ⟨hΔ.closed h hc'.1, hc'.2.of_le hΘ⟩

omit [Sub R] [OrderedSub R] in
/-- **One step of an activation's local command pays for itself.**  If the activation's control
stack starting with a local command `c` is typed and the activation agrees with its typing,
then a step of the activation (`ActStep`; it does not involve other threads, the pool
or timers) leaves a typed control stack in an agreeing activation, with the step's cost plus the new potential at most
the old potential `Q K b`, and the exit-clock bound not larger.  The final contexts of the
control stack are unchanged. -/
theorem CtlTyped.step (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk) {Ψd : FCtx K St R}
    (hP : P.WF) (hΨc : SigsClosedA P Ψ)
    (hCd : ∀ W W' : PCtx K St, W'.Le W → C W → C W')
    {fz Γ Δ Θ} {c : Cmd St R} {rest Γf Δf Θf Q F b σ H D Am}
    (ht : CtlTyped P M Ψ C cl fz Γ Δ Θ (.cmd c :: rest) Γf Δf Θf Q F)
    (hok : ActOK M Γ Δ b σ H D Am) (hws₀ : Θ.WinShape Δ.shape) (hwc₀ : Θ.WinCover Δ)
    (hcl : cl = true → Δ.HWClosed P ∧ Θ.SOutClosed P) (hcap : Θ.CapOK Δ)
    (hloc : c.Local)
    {T r as Kc q tick acts' D' K'}
    (hstep : ActStep M Ψd Am (⟨σ, H, T, .cmd c :: rest, r⟩ :: as) D Kc q tick acts' D' K') :
    ∃ σ' ctl' Γ' Δ' Θ' Q' F',
      acts' = ⟨σ', H, T, ctl', r⟩ :: as ∧
      CtlTyped P M Ψ C cl fz Γ' Δ' Θ' ctl' Γf Δf Θf Q' F' ∧ ActOK M Γ' Δ' b σ' H D' Am ∧
      q + Q' K' b ≤ Q Kc b ∧ F' K' ≤ F Kc ∧ Θ'.WinShape Δ'.shape ∧ Θ'.WinCover Δ' ∧
      Θ.SameIds Θ' ∧ (cl = true → Δ'.HWClosed P ∧ Θ'.SOutClosed P) ∧
      (¬ Θ.IsEmpty → K' = Kc) ∧ Θ'.CapOK Δ' ∧ Δ'.shape = Δ.shape ∧
      (∀ t th d, Θ t = some th → H th.p = some d → D' d = D d) ∧
      (fz = true → K' = Kc) := by
  cases ht with
  | cmd hc hcW hΓ hΔ hΘ hws hwc hrest =>
  have ⟨hF₂, hQ₂⟩ := hrest.mono hM hΨ
  have hnext := CtlTyped.next_closed hP hΨc hc hΔ hΘ hcl
  have hcapn := (hc.capOK hcap).of_le hΘ hΔ.le
  have hshn := hΔ.shape_eq.trans hc.shape_eq.1
  cases c with
  | skip =>
    cases hstep
    cases hc
    exact ⟨_, _, _, _, _, _, _, rfl, hrest, hok.weaken hΓ hΔ.le, by simp, le_rfl, hws, hwc, .of_le hΘ, hnext, fun _ => rfl, hcapn, hshn, fun _ _ _ _ _ => rfl, fun _ => rfl⟩
  | seq c₁ c₂ =>
    cases hstep
    cases hc with
    | seq h₁ h₂ =>
      have hws₁ := h₁.winShape hws₀
      have hshW := h₁.shape_eq.2.trans (h₂.shape_eq.2.trans h₁.shape_eq.1).symm
      rw [← h₁.shape_eq.1] at hws₁
      exact ⟨_, _, _, _, _, _, _, rfl,
        .cmd h₁ (hCd _ _ (PCtx.le_join_left hshW) hcW) (fun _ _ h => h) (PCtx.Widen.refl _)
          (ThreadCtx.Le.refl _) hws₁ (h₁.winCover hws₀ hwc₀)
          (.cmd h₂ (hCd _ _ (PCtx.le_join_right hshW) hcW) hΓ hΔ hΘ hws hwc hrest), hok, by simp [add_assoc],
        le_rfl, hws₀, hwc₀, .refl _, hcl, fun _ => rfl, hcap, rfl, fun _ _ _ _ _ => rfl, fun _ => rfl⟩
  | assign x e =>
    cases hstep
    rename_i v hev
    cases hc with
    | assign hty _ =>
      obtain ⟨hσ, hper⟩ := hok
      obtain ⟨v', hev', hty'⟩ := HasTy.eval hσ hty
      rw [hev] at hev'; cases hev'
      have hok' : ActOK M _ _ b (σ.set x v) H D Am := ⟨hσ.bind hty', hper⟩
      refine ⟨_, _, _, _, _, _, _, rfl, hrest, hok'.weaken hΓ hΔ.le, ?_, le_rfl, hws, hwc, .of_le hΘ, hnext, fun _ => rfl, hcapn, hshn, fun _ _ _ _ _ => rfl, fun _ => rfl⟩
      refine add_le_add ?_ le_rfl
      refine mul_le_mul_left'' ?_
      rw [add_assoc, add_assoc]
      exact add_le_add le_rfl (ActOK.bg_le ⟨hσ, hper⟩)
  | ite e c₁ c₂ =>
    cases hstep
    · cases hc with
      | ite _ h₁ h₂ hsame =>
        have hsh := h₁.shape_eq.1.trans h₂.shape_eq.1.symm
        have hshW := h₁.shape_eq.2.trans h₂.shape_eq.2.symm
        have hFa := (h₁.mono hM hΨ).1
        refine ⟨_, _, _, _, _, _, _, rfl,
          .cmd h₁ (hCd _ _ (PCtx.le_join_left hshW) hcW) (fun x τ hx => TCtx.inter_sub_left _ _ x τ (hΓ x τ hx))
            ((PCtx.Widen.join_left hsh fun h =>
              (h₂.hwClosed hP hΨc (hcl h).1 (hcl h).2).1).trans hΔ) ((ThreadCtx.le_join_left hsame).trans hΘ) hws hwc hrest,
          hok, ?_, hF₂ (le_max_left _ _), hws₀, hwc₀, .refl _, hcl, fun _ => rfl, hcap, rfl, fun _ _ _ _ _ => rfl, fun _ => rfl⟩
        rw [add_three]
        refine add_le_add (add_le_add (le_max_left _ _) ?_) (hQ₂ _ _ _ _ (le_max_left _ _) le_rfl)
        refine mul_le_mul_left'' ?_
        rw [add_assoc, add_assoc]
        exact add_le_add le_rfl hok.bg_le
    · cases hc with
      | ite _ h₁ h₂ hsame =>
        have hsh := h₁.shape_eq.1.trans h₂.shape_eq.1.symm
        have hshW := h₁.shape_eq.2.trans h₂.shape_eq.2.symm
        refine ⟨_, _, _, _, _, _, _, rfl,
          .cmd h₂ (hCd _ _ (PCtx.le_join_right hshW) hcW) (fun x τ hx => TCtx.inter_sub_right _ _ x τ (hΓ x τ hx))
            ((PCtx.Widen.join_right hsh fun h =>
              (h₁.hwClosed hP hΨc (hcl h).1 (hcl h).2).1).trans hΔ) ((ThreadCtx.le_join_right hsame).trans hΘ) hws hwc hrest,
          hok, ?_, hF₂ (le_max_right _ _), hws₀, hwc₀, .refl _, hcl, fun _ => rfl, hcap, rfl, fun _ _ _ _ _ => rfl, fun _ => rfl⟩
        rw [add_three]
        refine add_le_add (add_le_add (le_max_right _ _) ?_)
          (hQ₂ _ _ _ _ (le_max_right _ _) le_rfl)
        refine mul_le_mul_left'' ?_
        rw [add_assoc, add_assoc]
        exact add_le_add le_rfl hok.bg_le
  | transition p st =>
    cases hstep
    rename_i d k s hH hD
    obtain ⟨hσ, S, Ae, hC, hR, hS, hb⟩ := hok
    have hSp := hR.lookup hH hD
    obtain ⟨hC', _⟩ := hC.set hSp hH hD st
    have hR' := hR.set hC hSp hH hD st
    cases hc with
    | transition hp hnc _ _ =>
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      have hne : ∀ t th d', Θ t = some th → H th.p = some d' → d' ≠ d := by
        rintro t th d' ht hH' rfl
        obtain ⟨V', hV', _⟩ := hcap.1 t th ht
        obtain ⟨s₁, hS1, _⟩ := hS.live hV'
        exact hnc ⟨t, th, ht, hC.inj th.p p d' (by rw [hS1]; exact REntry.at_ne_zero)
          (by rw [hSp]; exact REntry.at_ne_zero) hH' hH⟩
      refine ⟨_, _, _, _, _, _, _, rfl, hrest,
        ActOK.weaken ⟨hσ, _, Ae, hC', hR', hS.set _ _ (Finset.mem_singleton_self _), hb⟩ hΓ hΔ.le,
        add_le_add ?_ le_rfl, le_rfl, hws, hwc,
        (ThreadCtx.SameIds.observe _ _).trans (.of_le hΘ), hnext, fun _ => rfl, hcapn, hshn,
        fun t th d' ht hH' => (by simp [RPeriphs.set_apply, hne t th d' ht hH']), fun _ => rfl⟩
      beta_reduce
      rw [← hC.charge_erase_eq M Kc _ hSp hD, add_assoc, add_assoc]
      exact mul_le_mul_left'' (add_le_add (M.transCost_le_maxTrans hs)
        (add_le_add (hS.erase p).bg_le hb))
    | transitionU hp hnc _ _ =>
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      have hne : ∀ t th d', Θ t = some th → H th.p = some d' → d' ≠ d := by
        rintro t th d' ht hH' rfl
        obtain ⟨V', hV', _⟩ := hcap.1 t th ht
        obtain ⟨s₁, hS1, _⟩ := hS.live hV'
        exact hnc ⟨t, th, ht, hC.inj th.p p d' (by rw [hS1]; exact REntry.at_ne_zero)
          (by rw [hSp]; exact REntry.at_ne_zero) hH' hH⟩
      refine ⟨_, _, _, _, _, _, _, rfl, hrest,
        ActOK.weaken ⟨hσ, _, Ae, hC', hR',
          hS.set _ _ (Finset.mem_union_left _ (Finset.mem_singleton_self _)), hb⟩ hΓ hΔ.le,
        add_le_add ?_ le_rfl, le_rfl, hws, hwc,
        (ThreadCtx.SameIds.observe _ _).trans (.of_le hΘ), hnext, fun _ => rfl, hcapn, hshn,
        fun t th d' ht hH' => (by simp [RPeriphs.set_apply, hne t th d' ht hH']), fun _ => rfl⟩
      beta_reduce
      rw [← hC.charge_erase_eq M Kc _ hSp hD, add_assoc, add_assoc]
      exact mul_le_mul_left'' (add_le_add (M.transCost_le_maxTrans hs)
        (add_le_add (hS.erase p).bg_le hb))
  | downgrade p st =>
    cases hstep
    rename_i d k s hH hD
    obtain ⟨hσ, S, Ae, hC, hR, hS, hb⟩ := hok
    have hSp := hR.lookup hH hD
    obtain ⟨hC', _⟩ := hC.set hSp hH hD st
    have hR' := hR.set hC hSp hH hD st
    cases hc with
    | downgrade hp hnc _ _ =>
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      have hne : ∀ t th d', Θ t = some th → H th.p = some d' → d' ≠ d := by
        rintro t th d' ht hH' rfl
        obtain ⟨V', hV', _⟩ := hcap.1 t th ht
        obtain ⟨s₁, hS1, _⟩ := hS.live hV'
        exact hnc ⟨t, th, ht, hC.inj th.p p d' (by rw [hS1]; exact REntry.at_ne_zero)
          (by rw [hSp]; exact REntry.at_ne_zero) hH' hH⟩
      refine ⟨_, _, _, _, _, _, _, rfl, hrest,
        ActOK.weaken ⟨hσ, _, Ae, hC', hR', hS.set _ _ (Finset.mem_singleton_self _), hb⟩ hΓ hΔ.le,
        add_le_add ?_ le_rfl, le_rfl, hws, hwc,
        (ThreadCtx.SameIds.observe _ _).trans (.of_le hΘ), hnext, fun _ => rfl, hcapn, hshn,
        fun t th d' ht hH' => (by simp [RPeriphs.set_apply, hne t th d' ht hH']), fun _ => rfl⟩
      beta_reduce
      rw [← hC.charge_erase_eq M Kc _ hSp hD, add_assoc, add_assoc]
      exact mul_le_mul_left'' (add_le_add (M.transCost_le_maxTrans hs)
        (add_le_add (hS.erase p).bg_le hb))
  | clock f' =>
    cases hstep
    cases hc with
    | clock hfz hΘe _ =>
      refine ⟨_, _, _, _, _, _, _, rfl, hrest, hok.weaken hΓ hΔ.le,
        add_le_add (add_le_add le_rfl (mul_le_mul_left'' hok.bg_le)) le_rfl, le_rfl, hws, hwc, .of_le hΘ, hnext,
        fun h => absurd hΘe h, hcapn, hshn, fun _ _ _ _ _ => rfl,
        fun h => by rw [h] at hfz; cases hfz⟩
  | matchSt p arms =>
    cases hstep
    rename_i d k s c hH h₂ h₃
    have hD : D d = .at k s := by assumption
    have hf : arms.find? s = some c := by assumption
    obtain ⟨hσ, S, Ae, hC, hR, hS, hb⟩ := hok
    have hSp := hR.lookup hH hD
    cases hc with
    | matchSt hp hncm _ ha =>
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      obtain ⟨Γc, Δc, Θc, Wc, Qc, Fc, hct, hΓc, hΔc, hΘc, hWc, hQc, hFc⟩ := ha.find hP hΨc hcl hs hf
      have hshM := (ha.shape_eq.2.trans (PCtx.shape_set_of hp ∅)).symm
      have hSs : PeriphsOK (Δ.set p k (P.hwClose k {s})) S := by
        rw [← RPeriphs.set_eq_self hSp]
        exact hS.set _ _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      have hok' : ActOK M Γ (Δ.set p k (P.hwClose k {s})) b σ H D Am :=
        ⟨hσ, S, Ae, hC, hR, hSs, hb⟩
      have eN := PCtx.shape_set_of hp (P.hwClose k {s})
      have hwsN' : Θ.WinShape (Δ.set p k (P.hwClose k {s})).shape := by rw [eN]; exact hws₀
      have hwsN := hwsN'.observe rfl
      refine ⟨_, _, _, _, _, _, _, rfl,
        .cmd hct (hCd _ _ (hWc.trans (PCtx.le_join_right hshM)) hcW) (fun x τ hx => hΓc x τ (hΓ x τ hx)) (hΔc.trans hΔ) (hΘc.trans hΘ) hws hwc hrest,
        hok', ?_, hF₂ (hFc _), hwsN, ThreadCtx.WinCover.observe_self hwsN',
        ThreadCtx.SameIds.observe _ _,
        fun h => ⟨(hcl h).1.set (hP.hwClose_idem _ _), (hcl h).2.observe _⟩, fun _ => rfl,
        (hcap.set hncm _ _).observe _, PCtx.shape_set_of hp _,
        fun _ _ _ _ _ => rfl, fun _ => rfl⟩
      calc Kc * (D.bg M + ambBg M Am) + (Qc Kc b + _)
          = Qc Kc b + Kc * (D.bg M + ambBg M Am) + _ := add_three _ _ _
        _ ≤ Qc Kc b + Kc * ((Δ.set p k (P.hwClose k {s})).bg M + b) + _ :=
            add_le_add (add_le_add le_rfl (mul_le_mul_left'' hok'.bg_le)) le_rfl
        _ ≤ _ := add_le_add (hQc _ _) (hQ₂ _ _ _ _ (hFc _) le_rfl)
  | call x g e p => exact absurd hloc id
  | async tid p c₀ => exact absurd hloc id
  | await tid n fb => exact absurd hloc id

/-! ### Frames and the store -/

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R]
  [IsOrderedRing R] [CanonicallyOrderedAdd R] in
/-- Setting a device twice keeps the last. -/
theorem RPeriphs.set_set (D : RPeriphs K St) (d : Dev) (k k' : K) (s s' : St) :
    (D.set d k s).set d k' s' = D.set d k' s' := by
  ext x; simp only [RPeriphs.set_apply]; split_ifs <;> rfl

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R]
  [IsOrderedRing R] [CanonicallyOrderedAdd R] in
/-- Stores that agree off `d` agree once `d` is set. -/
theorem RPeriphs.set_eq_of_agree {D D' : RPeriphs K St} {d : Dev}
    (h : ∀ dv, dv ≠ d → D' dv = D dv) (k : K) (s : St) : D'.set d k s = D.set d k s := by
  ext x; simp only [RPeriphs.set_apply]; split_ifs with hx
  · rfl
  · exact h x hx

omit [DecidableEq K] [LinearOrder R] [OrderBot R] [IsOrderedRing R] [CanonicallyOrderedAdd R] [Sub R]
  [OrderedSub R] in
/-- **Local steps change only reachable devices.**  A step of an activation's local command
changes the store only at devices the activation's handle map reaches (a transition's or
downgrade's device). -/
theorem ActStep.local_frame {Ψd : FCtx K St R} {Am : Multiset (K × St)} {c : Cmd St R}
    (hloc : c.Local) {σ H T rest r as D Kc q tick acts' D' K'}
    (hstep : ActStep M Ψd Am (⟨σ, H, T, .cmd c :: rest, r⟩ :: as) D Kc q tick acts' D' K') :
    ∀ dv, (∀ y, H y ≠ some dv) → D' dv = D dv := by
  intro dv hdv
  cases c <;> cases hstep
  all_goals try rfl
  all_goals
    rename_i d k s hH hD
    have hne : dv ≠ d := fun h => hdv _ (h ▸ hH)
    simp [RPeriphs.set_apply, hne]

omit [IsOrderedRing R] [CanonicallyOrderedAdd R] [OrderedSub R] [Sub R] in
/-- Inverting the typing of a control stack that starts with a command: the command's typing,
the weakening link, and the rest's typing, with the summaries composed as in T-Seq. -/
theorem CtlTyped.cons_inv {fz Γ Δ Θ} {c : Cmd St R} {rest Γf Δf Θf Q F}
    (h : CtlTyped P M Ψ C cl fz Γ Δ Θ (.cmd c :: rest) Γf Δf Θf Q F) :
    ∃ Γ₁ Δ₁ Θ₁ W Q₁ F₁ Γ₁' Δ₁' Θ₁' Q₂ F₂, TypedA P M Ψ fz Γ Δ Θ c Γ₁ Δ₁ Θ₁ W Q₁ F₁ ∧ C W ∧
      Γ₁'.Sub Γ₁ ∧ PCtx.Widen P cl Δ₁ Δ₁' ∧ Θ₁.Le Θ₁' ∧ Θ₁'.WinShape Δ₁'.shape ∧ Θ₁'.WinCover Δ₁' ∧
      CtlTyped P M Ψ C cl fz Γ₁' Δ₁' Θ₁' rest Γf Δf Θf Q₂ F₂ ∧
      Q = (fun f b => Q₁ f b + Q₂ (F₁ f) b) ∧ F = (fun f => F₂ (F₁ f)) := by
  cases h with
  | cmd hc hcW hΓ hΔ hΘ hws hwc hrest =>
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, hc, hcW, hΓ, hΔ, hΘ, hws, hwc, hrest, rfl, rfl⟩

/-! ### Device envelopes (the ceiling of a thread's stack) -/

/-- **A thread's device envelope**: the captured device `dev`, the states it may take while the
thread runs (`env`, the envelope `V` the spawner's typing records for it) and the states it
must end in (`out`).  A thread's stack is typed under this ceiling; `main`'s under none. -/
structure DevEnv (St : Type) where
  dev : Dev
  env : Finset St
  out : Finset St

/-- **The ceiling of a layer** with handle map `H`: every handle naming the envelope's device
visits only states in `env`.  Used as the ceiling `C` of the layer's `CtlTyped`: each entry's
visited context satisfies it, so the device stays in its envelope however the remaining
commands move it.  Vacuous without an envelope. -/
def DevEnv.Ceil (E : Option (DevEnv St)) (H : Var → Option Dev) (W : PCtx K St) : Prop :=
  ∀ e ∈ E, ∀ x k S, H x = some e.dev → W x = .live k S → S ⊆ e.env

/-- **The exit condition of a bottom layer**: every handle naming the envelope's device ends in
`out`.  For a thread's body, the device then ends in `sOut` when the body finishes. -/
def DevEnv.Exit (E : Option (DevEnv St)) (H : Var → Option Dev) (Δ : PCtx K St) : Prop :=
  ∀ e ∈ E, ∀ x k S, H x = some e.dev → Δ x = .live k S → S ⊆ e.out

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] [Sub R] in
/-- The ceiling is downward closed: a context below one that respects it respects it too.  This
is what lets it survive steps, which only shrink the remaining visited context. -/
theorem DevEnv.Ceil.mono {E : Option (DevEnv St)} {H : Var → Option Dev} {W W' : PCtx K St}
    (h : DevEnv.Ceil E H W) (hle : W'.Le W) : DevEnv.Ceil E H W' := by
  intro e he x k S hx hW'
  have hx' := hle x
  rw [hW'] at hx'
  cases hWx : W x with
  | absent => rw [hWx] at hx'; exact absurd hx' (by simp [PEntry.Le])
  | live k' S' =>
    rw [hWx] at hx'
    exact hx'.2.trans (h e he x k' S' hx hWx)

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] [Sub R] in
/-- Without an envelope the ceiling holds trivially (`main`'s stack). -/
theorem DevEnv.Ceil.of_none {H : Var → Option Dev} {W : PCtx K St} :
    DevEnv.Ceil (none : Option (DevEnv St)) H W := fun _ he => absurd he (by simp)

omit [CommSemiring R] [LinearOrder R] [OrderBot R] [Sub R] in
/-- **A callee inherits its caller's ceiling.**  The call's visited context passes the parameter
through `sig.visit` (T-Call); the callee's body visits only states of `visit` at its parameter
(T-FunDecl).  So if the caller's call entry respects the ceiling, so does the callee body, whose
only handle is its parameter. -/
theorem DevEnv.Ceil.callee {E : Option (DevEnv St)} {H : Var → Option Dev} {Δ Wb : PCtx K St}
    {p parg : Var} {k k' : K} {S V O Sv : Finset St} {d : Dev}
    (hcW : DevEnv.Ceil E H ((Δ.join (Δ.set p k V)).join (Δ.set p k O)))
    (hp : Δ p = .live k S) (hH : H p = some d) (hWb : Wb parg = .live k' Sv) (hSv : Sv ⊆ V) :
    DevEnv.Ceil E (fun y => if y = parg then some d else none) Wb := by
  intro e he x k₁ S₁ hx hWx
  by_cases hxp : x = parg
  · subst hxp
    simp only [↓reduceIte, Option.some.injEq] at hx
    rw [hWb] at hWx; cases hWx
    have hle : (Δ.set p k V).Le ((Δ.join (Δ.set p k V)).join (Δ.set p k O)) :=
      (PCtx.le_join_right (PCtx.shape_set_of hp V).symm).trans
        (PCtx.le_join_left ((PCtx.shape_join (PCtx.shape_set_of hp V).symm).trans
          (PCtx.shape_set_of hp O).symm))
    exact hSv.trans (hcW.mono hle e he p k V (by rw [hH, hx]) (by simp))
  · simp [hxp] at hx

/-- **A thread layer sees only its device, through a live handle**: every handle of the layer
names the envelope's device, and one of them is live in the layer's context.  So the layer's
ambient is exactly "every other device, plus the outer ambient", whatever they are doing —
which is how a thread's agreement survives devices it cannot see moving (`StackOK.foreign`).
Vacuous without an envelope (`main`). -/
def DevEnv.Sees (E : Option (DevEnv St)) (H : Var → Option Dev) (Δ : PCtx K St) : Prop :=
  ∀ e ∈ E, (∀ x d, H x = some d → d = e.dev) ∧ ∃ x k S, H x = some e.dev ∧ Δ x = .live k S

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] [Sub R] in
/-- `Sees` depends on the context only through its shape (steps keep the shape). -/
theorem DevEnv.Sees.of_shape {E : Option (DevEnv St)} {H : Var → Option Dev}
    {Δ Δ' : PCtx K St} (h : DevEnv.Sees E H Δ) (hsh : Δ'.shape = Δ.shape) :
    DevEnv.Sees E H Δ' := by
  intro e he
  obtain ⟨h₁, x, k, S, hx, hΔ⟩ := h e he
  have hsx := congrFun hsh x
  cases hd : Δ' x with
  | absent => simp only [PCtx.shape, hd, hΔ] at hsx; cases hsx
  | live k' S' =>
    simp only [PCtx.shape, hd, hΔ, Option.some.injEq] at hsx
    subst hsx
    exact ⟨h₁, x, k', S', hx, hd⟩

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] [Sub R] in
/-- A callee sees what its caller passed it: the caller's device, through its parameter. -/
theorem DevEnv.Sees.callee {E : Option (DevEnv St)} {H : Var → Option Dev} {Δ : PCtx K St}
    (h : DevEnv.Sees E H Δ) {p : Var} {d : Dev} (hH : H p = some d) (q : Var) (k : K)
    (S : Finset St) :
    DevEnv.Sees E (fun y => if y = q then some d else none)
      (Finsupp.single q (PEntry.live k S) : PCtx K St) := by
  intro e he
  have hd : d = e.dev := (h e he).1 p d hH
  refine ⟨fun x d' hx => ?_, q, k, S, by simp [hd], by simp⟩
  by_cases hxq : x = q
  · simp only [hxq, ↓reduceIte, Option.some.injEq] at hx
    rw [← hx]; exact hd
  · simp [hxq] at hx

/-! ### Agreement survives captured devices moving -/

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R]
  [IsOrderedRing R] in
/-- Re-setting a handle to the set it already has is a no-op. -/
theorem PCtx.set_eq_self {Δ : PCtx K St} {p : Var} {k : K} {T : Finset St}
    (h : Δ p = .live k T) : Δ.set p k T = Δ := by
  ext x
  rw [PCtx.set_apply]
  split_ifs with hx
  · subst hx; exact h.symm
  · rfl

omit [DecidableEq K] [DecidableEq St] [OrderBot R] [IsOrderedRing R] [Sub R] [CanonicallyOrderedAdd R]
  [OrderedSub R] in
/-- **Agreement survives a visible captured device moving within its set.**  If handle `x` of the
activation names device `c` with typing entry `(k, V)`, the store may move `c` to any state of
`V` (a thread step or a hardware step) and the activation still agrees with its typing. -/
theorem ActOK.move {Γ Δ b σ H D Am} (h : ActOK M Γ Δ b σ H D Am) {x c : Var} {k : K}
    {V : Finset St} (hH : H x = some c) (hΔ : Δ x = .live k V) {s' : St} (hs' : s' ∈ V) :
    ActOK M Γ Δ b σ H (D.set c k s') Am := by
  obtain ⟨hσ, S, Ae, hC, hR, hS, hb⟩ := h
  obtain ⟨s, hSx, _⟩ := hS.live hΔ
  obtain ⟨c', hH', hD'⟩ := hC.lookup hSx
  rw [hH] at hH'; cases hH'
  have hPer := hS.set x k hs'
  rw [PCtx.set_eq_self hΔ] at hPer
  exact ⟨hσ, _, Ae, (hC.set hSx hH hD' s').1, hR.set hC hSx hH hD' s', hPer, hb⟩


/-! ### The backward window bound for control stacks -/

omit [DecidableEq K] [DecidableEq St] [CommSemiring R] [LinearOrder R] [OrderBot R] [Sub R]
  [IsOrderedRing R] [CanonicallyOrderedAdd R] [OrderedSub R] in
/-- Precision does not change shape. -/
theorem PCtx.Le.shape_eq {Δ₁ Δ₂ : PCtx K St} (h : Δ₁.Le Δ₂) : Δ₁.shape = Δ₂.shape := by
  funext x
  have hx := h x
  rw [PCtx.shape_apply, PCtx.shape_apply]
  revert hx
  generalize Δ₁ x = A
  generalize Δ₂ x = B
  intro hx
  rcases A with _ | ⟨k, S⟩ <;> rcases B with _ | ⟨k', S'⟩
  · rfl
  · exact hx.elim
  · exact hx.elim
  · obtain ⟨rfl, -⟩ := hx; rfl

omit [CommSemiring R] [LinearOrder R] [OrderBot R] [Sub R] [IsOrderedRing R]
  [CanonicallyOrderedAdd R] [OrderedSub R] in
/-- Joining something that keeps the shape only adds states. -/
theorem PCtx.le_join_of_shape {a w : PCtx K St} (h : (a.join w).shape = a.shape) :
    a.Le (a.join w) := by
  intro x
  have hx := congrFun h x
  rw [PCtx.shape_apply, PCtx.shape_apply, PCtx.join_apply] at hx
  rw [PCtx.join_apply]
  revert hx
  generalize a x = A
  generalize w x = B
  intro hx
  rcases A with _ | ⟨k, S⟩ <;> rcases B with _ | ⟨k', S'⟩
  · exact trivial
  · exact trivial
  · exact absurd hx (by simp [PEntry.join, PEntry.kindOf])
  · by_cases hk : k = k'
    · subst hk
      simp only [PEntry.join, ↓reduceIte, PEntry.Le, true_and]
      exact Finset.subset_union_left
    · exact absurd hx (by simp [PEntry.join, PEntry.kindOf, hk])

omit [Sub R] [CanonicallyOrderedAdd R] [OrderedSub R] in
/-- Windows below larger windows of the same shape are within their bounds too. -/
theorem ThreadCtx.AmbOK.of_le {Θ₁ Θ₂ : ThreadCtx K St R} {sh} (hle : Θ₁.Le Θ₂)
    (hw₁ : Θ₁.WinShape sh) (hw₂ : Θ₂.WinShape sh) (h : Θ₂.AmbOK M) : Θ₁.AmbOK M := by
  intro t a ha
  rcases hle t with ⟨e, _⟩ | ⟨a', b, w, e₁, e₂, hab, hwin⟩
  · rw [ha] at e; cases e
  · rw [ha] at e₁; cases e₁
    have hb := h t b e₂
    rw [← hab.1, ← hab.2.2.2.2] at hb
    refine le_trans (PCtx.Le.bg_le (PCtx.Le.erase ?_ _)) hb
    rw [hwin]
    exact PCtx.le_join_of_shape (by rw [← hwin, hw₂ t b e₂, hw₁ t a ha])

omit [Sub R] [CanonicallyOrderedAdd R] [OrderedSub R] in
/-- Through a waiting `await` frame: the awaited thread's window was checked, and every other
thread's window grows into the frame's output. -/
theorem ThreadCtx.AmbOK.of_await {fz : Bool} {Γ : TCtx K} {Δ : PCtx K St} {Θ : ThreadCtx K St R}
    {tid : Var} {th : ThreadTy K St R} {fb : Cmd St R} {Γf Δf Θf Wf Qf Ff Δ₁' Θ₁'}
    (hth : Θ tid = some th) (hp : Δ th.p = .live th.k th.V)
    (hamb : (th.win.erase th.p).bg M ≤ th.amb)
    (hfb : TypedA P M Ψ fz Γ Δ (Θ.erase tid) fb Γf Δf Θf Wf Qf Ff)
    (hs : (Θ.erase tid).SameThreads Θf)
    (hΔ : ((Δ.set th.p th.k th.sOut).join Δf).Le Δ₁')
    (hΘ : (((Θ.erase tid).observe (Δ.set th.p th.k th.sOut)).join Θf).Le Θ₁')
    (hws : Θ₁'.WinShape Δ₁'.shape) (h₁ : Θ₁'.AmbOK M) (hw : Θ.WinShape Δ.shape) :
    Θ.AmbOK M := by
  have e := PCtx.shape_set_of hp th.sOut
  have hwe := (hw.erase tid).observe e
  have hwf := hfb.winShape (hw.erase tid)
  have hj := hwe.join hwf
  have hsh : ((Δ.set th.p th.k th.sOut).join Δf).shape = Δ.shape :=
    (PCtx.shape_join (e.trans (hfb.shape_eq.1).symm)).trans e
  rw [← hsh, hΔ.shape_eq] at hj
  have hl := ThreadCtx.AmbOK.of_le hΘ hj hws h₁
  have hs' : ((Θ.erase tid).observe (Δ.set th.p th.k th.sOut)).SameThreads Θf := by
    intro t
    rcases hs t with ⟨e₁, e₂⟩ | ⟨a, b, e₁, e₂, hab⟩
    · exact Or.inl ⟨by simp [ThreadCtx.observe, e₁], e₂⟩
    · exact Or.inr ⟨{ a with win := a.win.join (Δ.set th.p th.k th.sOut) }, b,
        by simp [ThreadCtx.observe, e₁], e₂, hab⟩
  have hl' := hl.of_join hs' hwe hwf
  refine (hl'.of_observe (hw.erase tid) e).of_erase ?_
  intro th' ht'
  rw [hth] at ht'; cases ht'
  exact hamb

omit [CanonicallyOrderedAdd R] [OrderedSub R] [Sub R] in
/-- **The backward window bound for control stacks.**  A control stack ending with no pending
threads has, at its start, every pending thread's window within the bound declared at its
spawn.  (Through each command by `TypedA.ambOK_back`; through each weakening link because windows
only grow; through a waiting `await` because its thread's window was checked.) -/
theorem CtlTyped.ambOK {fz Γ Δ Θ ctl Γf Δf Θf Q F}
    (h : CtlTyped P M Ψ C cl fz Γ Δ Θ ctl Γf Δf Θf Q F) :
    Θf.IsEmpty → Θ.WinShape Δ.shape → Θ.AmbOK M := by
  induction h with
  | nil => intro he _ t th ht; rw [he t] at ht; cases ht
  | cmd hc _ _ hΔ hΘ hws _ _ ih =>
    intro he hw
    have hw₁ := hc.winShape hw
    rw [← hc.shape_eq.1, hΔ.le.shape_eq] at hw₁
    exact hc.ambOK_back hw (ThreadCtx.AmbOK.of_le hΘ hw₁ hws (ih he hws))
  | awaitW hth hp hamb hfb _ hs _ _ _ hΔ hΘ hws _ _ ih =>
    intro he hw
    exact ThreadCtx.AmbOK.of_await hth hp hamb hfb hs hΔ.le hΘ hws (ih he hws) hw

/-! ### Stacks of activations -/

/-- Every signature is the one T-FunDecl derives for its declaration (async version of
`SigsDerived`): calls can step into the callee's body derivation. -/
def SigsDerivedA (P : Platform K St) (M : CostModel K St R) (Ψd : FCtx K St R)
    (Ψ : SigCtxA K St R) : Prop :=
  ∀ g sig, Ψ g = some sig → ∃ d, Ψd g = some d ∧ FunDeclTypedA P M Ψ d sig

omit [DecidableEq K] [CommSemiring R] [LinearOrder R] [OrderBot R] [IsOrderedRing R]
  [CanonicallyOrderedAdd R] [Sub R] [OrderedSub R] in
/-- A single handle with a closed set is a closed context (a function body's or thread body's
starting context, from closed `sIn` / `S₀`). -/
theorem PCtx.HWClosed.single {x : Var} {k : K} {S : Finset St} (h : P.hwClose k S = S) :
    PCtx.HWClosed P (Finsupp.single x (PEntry.live k S) : PCtx K St) := by
  intro y k' S' hy
  rw [Finsupp.single_apply] at hy
  split_ifs at hy
  · cases hy; exact h

omit [DecidableEq K] [CommSemiring R] [LinearOrder R] [OrderBot R] [Sub R] [IsOrderedRing R]
  [CanonicallyOrderedAdd R] [OrderedSub R] in
/-- No pending threads: trivially closed exit states. -/
theorem ThreadCtx.SOutClosed.empty :
    (ThreadCtx.empty : ThreadCtx K St R).SOutClosed P := fun _ _ ht => by cases ht

/-! ### Thread views: who holds the pending threads -/

/-- **A thread view**: the typing view of the activation whose threads are pending (the
*spawner*) — its thread context, peripheral context, ambient bound, handle map and thread-id
map.  At most one activation of `main`'s stack has pending threads: an activation with pending
threads calls only frozen functions (`stableClock`), and frozen code cannot spawn. -/
structure TView (K St R : Type) where
  Θ : ThreadCtx K St R
  Δ : PCtx K St
  b : R
  H : Var → Option Dev
  T : Var → Option ThreadId

/-- **A suspended spawner's view agrees with the store**, and its typing invariants hold: its
agreement under the view's context and ambient bound, window shape and cover, captured handles
and the backward window bound. -/
def TView.OK (M : CostModel K St R) (Am : Multiset (K × St)) (tv : TView K St R)
    (D : RPeriphs K St) : Prop :=
  (∃ Γ σ, ActOK M Γ tv.Δ tv.b σ tv.H D Am) ∧ tv.Θ.WinShape tv.Δ.shape ∧
    tv.Θ.WinCover tv.Δ ∧ tv.Θ.CapOK tv.Δ ∧ tv.Θ.AmbOK M

/-- A device seen through a handle is in a state the handle's set allows. -/
theorem ActOK.state_in {Γ : TCtx K} {Δ : PCtx K St} {b : R} {σ : Mem} {H : Var → Option Dev}
    {D : RPeriphs K St} {Am : Multiset (K × St)} (h : ActOK M Γ Δ b σ H D Am) {x : Var}
    {d : Dev} {k : K} {s : St} (hH : H x = some d) (hD : D d = .at k s) :
    ∃ T, Δ x = .live k T ∧ s ∈ T := by
  obtain ⟨_, S, _, _, hR, hS, _⟩ := h
  have hSx : D d = S x := hR x d hH (by rw [hD]; exact REntry.at_ne_zero)
  rw [hD] at hSx
  have := hS x
  rw [← hSx] at this
  cases hΔ : Δ x with
  | absent => rw [hΔ] at this; exact absurd this id
  | live k' T => rw [hΔ] at this; obtain ⟨rfl, hs⟩ := this; exact ⟨T, rfl, hs⟩

/-- Re-typing a visible handle with a larger set containing its device's state keeps the
agreement (used for a spawner's suspended view, whose passed handle is typed at `visit`). -/
theorem ActOK.retype {Γ : TCtx K} {Δ : PCtx K St} {b : R} {σ : Mem} {H : Var → Option Dev}
    {D : RPeriphs K St} {Am : Multiset (K × St)} (h : ActOK M Γ Δ b σ H D Am) {p : Var}
    {d : Dev} {k : K} {s : St} {V : Finset St} (hH : H p = some d) (hD : D d = .at k s)
    (hs : s ∈ V) : ActOK M Γ (Δ.set p k V) b σ H D Am := by
  obtain ⟨hσ, S, Ae, hC, hR, hS, hb⟩ := h
  have hSp := hR.lookup hH hD
  refine ⟨hσ, S, Ae, hC, hR, ?_, hb⟩
  rw [← RPeriphs.set_eq_self hSp]
  exact hS.set _ _ hs

/-- Everything but one visible device, plus the outer ambient, costs at most the context
without its handle plus the ambient bound. -/
theorem ActOK.bg_erase_le {Γ : TCtx K} {Δ : PCtx K St} {b : R} {σ : Mem}
    {H : Var → Option Dev} {D : RPeriphs K St} {Am : Multiset (K × St)}
    (h : ActOK M Γ Δ b σ H D Am) {p : Var} {d : Dev} {k : K} {V : Finset St}
    (hH : H p = some d) (hΔ : Δ p = .live k V) :
    (D.erase d).bg M + ambBg M Am ≤ (Δ.erase p).bg M + b := by
  obtain ⟨_, S, Ae, hC, _, hS, hb⟩ := h
  obtain ⟨s, hSp, _⟩ := hS.live hΔ
  obtain ⟨d', hd', hD'⟩ := hC.lookup hSp
  rw [hH] at hd'; cases hd'
  rw [← hC.erase_bg M hSp hD']
  exact add_le_add (hS.erase p).bg_le hb

/-- A pending thread's device and an uncaptured live handle's device differ. -/
theorem ActOK.dev_ne_free {Γ : TCtx K} {Δ : PCtx K St} {b : R} {σ : Mem}
    {H : Var → Option Dev} {D : RPeriphs K St} {Am : Multiset (K × St)}
    {Θ : ThreadCtx K St R} (h : ActOK M Γ Δ b σ H D Am) (hcap : Θ.CapOK Δ) {t : Var}
    {th : ThreadTy K St R} (ht : Θ t = some th) {p : Var} {k : K} {V : Finset St}
    (hp : Δ p = .live k V) (hnc : ¬ Θ.Captures p) {c d : Dev} (hc : H th.p = some c)
    (hd : H p = some d) : c ≠ d := by
  rintro rfl
  obtain ⟨_, S, _, hC, _, hS, _⟩ := h
  obtain ⟨V₁, hV₁, _⟩ := hcap.1 t th ht
  obtain ⟨s₁, hS₁, _⟩ := hS.live hV₁
  obtain ⟨s₂, hS₂, _⟩ := hS.live hp
  exact hnc ⟨t, th, ht, hC.inj th.p p c (by rw [hS₁]; exact REntry.at_ne_zero)
    (by rw [hS₂]; exact REntry.at_ne_zero) hc hd⟩

/-- A suspended view stays in agreement when the passed device moves within its set. -/
theorem TView.OK.move {Am : Multiset (K × St)} {tv : TView K St R} {D : RPeriphs K St}
    (h : TView.OK M Am tv D) {p : Var} {d : Dev} {k k' : K} {s s' : St} {V : Finset St}
    (hH : tv.H p = some d) (hΔ : tv.Δ p = .live k' V) (hD : D d = .at k s) (hs' : s' ∈ V) :
    TView.OK M Am tv (D.set d k s') := by
  obtain ⟨⟨Γ, σ, hok⟩, rest⟩ := h
  obtain ⟨T, hT, _⟩ := hok.state_in hH hD
  rw [hΔ] at hT; cases hT
  exact ⟨⟨Γ, σ, hok.move hH hΔ hs'⟩, rest⟩

/-- A callee's body visits only `visit` at its parameter (T-FunDecl), so it respects a ceiling
keeping the passed device within any set containing `visit`. -/
theorem DevEnv.Ceil.visit {Wb : PCtx K St} {parg : Var} {d : Dev} {k' : K} {Sv V O : Finset St}
    (hWb : Wb parg = .live k' Sv) (hSv : Sv ⊆ V) :
    DevEnv.Ceil (some ⟨d, V, O⟩) (fun y => if y = parg then some d else none) Wb := by
  intro e he x k₁ S₁ hx hW
  simp only [Option.mem_def, Option.some.injEq] at he; subst he
  by_cases hxp : x = parg
  · subst hxp; rw [hWb] at hW; cases hW; exact hSv
  · simp [hxp] at hx

/-- A call's visited context includes the callee's exit states at the passed handle, so a
ceiling on the caller bounds them. -/
theorem DevEnv.Ceil.call_out {E : Option (DevEnv St)} {H : Var → Option Dev} {Δ : PCtx K St}
    {p : Var} {k : K} {S V O : Finset St} {d : Dev}
    (hcW : DevEnv.Ceil E H ((Δ.join (Δ.set p k V)).join (Δ.set p k O)))
    (hp : Δ p = .live k S) (hH : H p = some d) : ∀ e ∈ E, e.dev = d → O ⊆ e.env := by
  intro e he hed
  have hle : (Δ.set p k O).Le ((Δ.join (Δ.set p k V)).join (Δ.set p k O)) :=
    PCtx.le_join_right ((PCtx.shape_join (PCtx.shape_set_of hp V).symm).trans
      (PCtx.shape_set_of hp O).symm)
  exact (hcW.mono hle) e he p k O (by rw [hH, hed]) (by simp)

/-- A handle bound in a context stays bound when the shape is unchanged. -/
theorem PCtx.exists_live_of_shape {Δ Δ' : PCtx K St} {x : Var}
    (h : ∃ k T, Δ x = .live k T) (hsh : Δ'.shape = Δ.shape) : ∃ k T, Δ' x = .live k T := by
  obtain ⟨k, T, hx⟩ := h
  have hs := congrFun hsh x
  cases hd : Δ' x with
  | absent => simp only [PCtx.shape, hd, hx] at hs; cases hs
  | live k' T' => exact ⟨k', T', rfl⟩

/-- **A typed stack of activations** (one segment), with its potential `Φ` (remaining typed
budget) at the current clock, an upper bound `X` on its exit clock, the running activation's
view `Θ Δ b`, the bottom layer's ambient bound `bb`, the **thread view** `tv` (the spawner's
view, possibly suspended below callees) and a **suspension ceiling** `Vs` (the set the
suspended spawner's passed device must stay in).

* `base`: a bottom activation (`main`, or a thread body) whose control stack is typed, ends
  with no pending threads, and agrees with the store; potential `Q K b`; its thread view is its
  own view.
* `push`: a called function on top of its caller, captured in a **continuation clause** (for
  any return value, final state of the passed device in `sOut`, and return clock up to the
  callee's exit bound, the caller is again a typed stack).  The callee inherits a thread view
  `tvb`: its caller's, if the caller has no pending threads (`tvb = tvc`), or, if the caller is a
  spawner, the caller's **suspended view** — its context with the passed handle at `visit`, which
  pending threads' windows observe at the call — whose agreement with the store is kept here
  (`TView.OK`), the callee and its own callees keeping the passed device within `visit` (the
  ceiling `Vs`), and whose threads are those of the caller after the return.  A callee under a
  suspended spawner is frozen.  The stack's thread view is `tvb`, or the callee's own view if it
  spawns (only when nothing below has pending threads).

In thread stacks (`E = some _`) every layer's current context is closed under hardware steps
(as are its pending threads' exit states), so a hardware step on the thread's device stays in
it.  The clause refers to the current store updated at the passed device; since the callee can
only change that device, the clause stays valid as the callee runs. -/
inductive StackOK (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtxA K St R)
    (Am : Multiset (K × St)) (E : Option (DevEnv St)) :
    List (Act St R) → RPeriphs K St → R → R → R → ThreadCtx K St R → PCtx K St → R → R →
    TView K St R → Option (DevEnv St) → Prop where
  | base {σ H T ctl fz Γ Δ Θ Γf Δf Θf Q F b D Kc} :
      CtlTyped P M Ψ (fun W => DevEnv.Ceil E H W ∧ DevEnv.Ceil (none : Option (DevEnv St)) H W)
        E.isSome fz Γ Δ Θ ctl Γf Δf Θf Q F →
      DevEnv.Exit E H Δf → Θf.IsEmpty →
      ActOK M Γ Δ b σ H D Am →
      Θ.WinShape Δ.shape → Θ.WinCover Δ → (E.isSome = true → Δ.HWClosed P ∧ Θ.SOutClosed P) →
      Θ.CapOK Δ →
      DevEnv.Sees E H Δ →
      (E.isSome = true → fz = true) →
      StackOK P M Ψ Am E [⟨σ, H, T, ctl, none⟩] D Kc (Q Kc b) (F Kc) Θ Δ b b ⟨Θ, Δ, b, H, T⟩ none
  | push {σ parg d T ctl e x σc Hc Tc ctlc rc rest fz Γ Δ Θ Γf Δf Θf Q F b D Kc τ k S' sOut}
      {Φc Xc : R → R} {Θc : ThreadCtx K St R} {Δc : PCtx K St} {bc bb : R}
      {tv tvb tvc : TView K St R} {Vs Vsc : Option (DevEnv St)} :
      CtlTyped P M Ψ (fun W => DevEnv.Ceil E (fun y => if y = parg then some d else none) W ∧
          DevEnv.Ceil Vs (fun y => if y = parg then some d else none) W) E.isSome fz Γ Δ Θ ctl
        Γf Δf Θf Q F → Θf.IsEmpty →
      ActOK M Γ Δ b σ (fun y => if y = parg then some d else none) D Am →
      Θ.WinShape Δ.shape → Θ.WinCover Δ → (E.isSome = true → Δ.HWClosed P ∧ Θ.SOutClosed P) →
      Θ.CapOK Δ →
      DevEnv.Sees E (fun y => if y = parg then some d else none) Δ →
      (∃ k₁ T₁, Δ parg = .live k₁ T₁) →
      (E.isSome = true → fz = true) →
      HasTy Γf e τ → Δf parg = .live k S' → S' ⊆ sOut →
      Monotone Φc → Monotone Xc → bb ≤ b →
      ((tvb = tvc ∧ Vs = Vsc) ∨ (tvc = ⟨Θc, Δc, bc, Hc, Tc⟩ ∧ tvb.b = bc ∧ tvb.H = Hc ∧
        tvb.T = Tc ∧ tvb.Θ.SameIds Θc)) →
      (∀ ev ∈ Vs, ev.dev = d ∧ ∃ p' k', tvb.H p' = some d ∧ tvb.Δ p' = .live k' ev.env ∧
        ¬ tvb.Θ.Captures p' ∧ tvb.b + (tvb.Δ.erase p').bg M ≤ b) →
      (¬ tvb.Θ.IsEmpty → Vs.isSome = true) →
      (¬ tvb.Θ.IsEmpty → fz = true) →
      (¬ tvb.Θ.IsEmpty → TView.OK M Am tvb D) →
      ((Θ.IsEmpty ∧ tv = tvb) ∨
        (tvb.Θ.IsEmpty ∧ tv = ⟨Θ, Δ, b, fun y => if y = parg then some d else none, T⟩)) →
      (∀ v s' K', v.ty = τ → s' ∈ sOut → K' ≤ F Kc →
        StackOK P M Ψ Am E (⟨σc.set x v, Hc, Tc, ctlc, rc⟩ :: rest) (D.set d k s') K'
          (Φc K') (Xc K') Θc Δc bc bb tvc Vsc) →
      StackOK P M Ψ Am E
        (⟨σ, fun y => if y = parg then some d else none, T, ctl, some (e, x)⟩ ::
          ⟨σc, Hc, Tc, ctlc, rc⟩ :: rest) D Kc
        (Q Kc b + F Kc * (e.cost M + Δf.bg M + b) + Φc (F Kc)) (Xc (F Kc)) Θ Δ b bb tv Vs

/-- The running activation's next control entry is a local command or a call (or there is
none).  `async` / `await` are handled in piece 3. -/
def TopOK (as : List (Act St R)) : Prop :=
  ∀ a ∈ as.head?, ∀ x ∈ a.ctl.head?,
    ∃ c, x = .cmd c ∧ (c.Local ∨ ∃ x g e p, c = .call x g e p)

/-- No pending threads: the empty thread context. -/
theorem ThreadCtx.empty_isEmpty {R : Type} : (ThreadCtx.empty : ThreadCtx K St R).IsEmpty :=
  fun _ => rfl

/-- The current context of a control stack respects its ceiling (its first entry's visited
context is above it; an empty stack's ceiling premise is on it directly). -/
theorem CtlTyped.ceil_view (hCd : ∀ W W' : PCtx K St, W'.Le W → C W → C W')
    {fz Γ Δ Θ ctl Γf Δf Θf Q F} (h : CtlTyped P M Ψ C cl fz Γ Δ Θ ctl Γf Δf Θf Q F) : C Δ := by
  cases h with
  | nil hC => exact hC
  | cmd hc hcW => exact hCd _ _ hc.le_W.1 hcW
  | awaitW _ _ _ hfb hcW => exact hCd _ _ hfb.le_W.1 hcW

/-- **The store after a step of the running activation**: unchanged, or one device it sees
moved to a new state of the same kind. -/
theorem ActStep.store {Ψd : FCtx K St R} {A : Multiset (K × St)} {a : Act St R}
    {as D Kc q tick as' D' K'} (h : ActStep M Ψd A (a :: as) D Kc q tick as' D' K') :
    D' = D ∨ ∃ x d k s st, a.H x = some d ∧ D d = .at k s ∧ D' = D.set d k st := by
  cases h with
  | transition hH hD => exact Or.inr ⟨_, _, _, _, _, hH, hD, rfl⟩
  | downgrade hH hD => exact Or.inr ⟨_, _, _, _, _, hH, hD, rfl⟩
  | _ => exact Or.inl rfl


/-- **One step of a typed stack pays for itself** (local commands, calls and returns, as
`ActStep`s — independent of other threads and the pool).  The step's cost plus the new
potential is at most the old potential, and the exit bound does not grow.  The thread view
keeps the same pending threads; while there are any, the spawner's ambient bound, handle and
thread-id maps, the clock and the threads' devices are unchanged. -/
theorem StackOK.step (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk) {Ψd : FCtx K St R}
    (hP : P.WF) (hΨc : SigsClosedA P Ψ)
    (hΨd : SigsDerivedA P M Ψd Ψ) {Am : Multiset (K × St)} {E : Option (DevEnv St)}
    {as D Kc Φ X Θ Δ b bb tv Vs} (h : StackOK P M Ψ Am E as D Kc Φ X Θ Δ b bb tv Vs) :
    ∀ {q tick as' D' K'}, TopOK as → ActStep M Ψd Am as D Kc q tick as' D' K' →
    ∃ Φ' X' Θ' Δ' b' tv' Vs', StackOK P M Ψ Am E as' D' K' Φ' X' Θ' Δ' b' bb tv' Vs' ∧
      q + Φ' ≤ Φ ∧ X' ≤ X ∧ tv.Θ.SameIds tv'.Θ ∧
      (¬ tv.Θ.IsEmpty → tv'.b = tv.b ∧ tv'.H = tv.H ∧ tv'.T = tv.T ∧ K' = Kc ∧
        ∀ t th d, tv.Θ t = some th → tv.H th.p = some d → D' d = D d) ∧
      (E.isSome = true → K' = Kc) := by
  cases h with
  | @base σ H T ctl fz Γ Δ Θ Γf Δf Θf Q F b D Kc hct hex hΘf hok hws hwc hclo hcapo hsees hfzo =>
    intro q tick as' D' K' htop hstep
    rcases ctl with _ | ⟨x₀, ctlr⟩
    · cases hstep
    obtain ⟨c, rfl, hc⟩ := htop _ rfl _ rfl
    rcases hc with hloc | ⟨x, g, e, p, rfl⟩
    · -- a local command
      obtain ⟨σ', ctl', Γ', Δ', Θ', Q', F', rfl, hct', hok', hq, hF, hws', hwc', hsame, hcl', hK',
        hcap', hsh', hcf, hKfz⟩ :=
        CtlTyped.step hM hΨ hP hΨc (fun _ _ hle hc => ⟨hc.1.mono hle, hc.2.mono hle⟩) hct hok hws
          hwc hclo hcapo hloc hstep
      exact ⟨_, _, _, _, _, _, _, .base hct' hex hΘf hok' hws' hwc' hcl' hcap'
        (hsees.of_shape hsh') hfzo, hq, hF, hsame, fun h => ⟨rfl, rfl, rfl, hK' h, hcf⟩,
        fun h => hKfz (hfzo h)⟩
    · -- a call: push the callee; the caller's continuation becomes its clause
      obtain ⟨Γ₁, Δ₁, Θ₁, W, Q₁, F₁, Γ₁', Δ₁', Θ₁', Q₂, F₂, hc, hcW, hΓ, hΔ, hΘ, hwsr, hwcr,
        hrest, rfl, rfl⟩ := hct.cons_inv
      have hnextc := CtlTyped.next_closed hP hΨc hc hΔ hΘ hclo
      have hcapc := (hc.capOK hcapo).of_le hΘ hΔ.le
      have hshc := hΔ.shape_eq.trans hc.shape_eq.1
      have hw₁ := hc.winShape hws
      rw [← hc.shape_eq.1, hΔ.le.shape_eq] at hw₁
      have hamb₁ : Θ₁.AmbOK M := ThreadCtx.AmbOK.of_le hΘ hw₁ hwsr (hrest.ambOK hΘf hwsr)
      cases hc with
      | @call _ _ _ _ _ _ _ _ sig S₀ hg hty hx hp hsub₀ hnc hfzs =>
      cases hstep
      rename_i dcl v d k s hgd hev hH hD
      obtain ⟨dcl', hd', hfd⟩ := hΨd g sig hg
      rw [hgd] at hd'; cases hd'
      obtain ⟨hargTy, hpKind, hsIn, hretTy, hsOut, ⟨Γb, Δb, Wb, Qb, Fb, S', Sv, hbody, hretT,
        hΔb, hS', hWbp, hSv, hcost, hclk⟩, hsInC, _⟩ := hfd
      have hok₀ := hok
      obtain ⟨hσ, S, Ae, hC, hR, hS, hb⟩ := hok
      have hSp := hR.lookup hH hD
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      obtain ⟨v', hev', hvty⟩ := HasTy.eval hσ hty
      rw [hev] at hev'; cases hev'
      have hF2 := hrest.mono hM hΨ
      have hCb := DevEnv.Ceil.callee hcW.1 hp hH hWbp hSv
      have hInSv : dcl.sIn ⊆ Sv := by
        have := hbody.le_W.1 dcl.parg
        rw [Finsupp.single_eq_same, hWbp] at this
        exact this.2
      have hsV : s ∈ sig.visit := hSv (hInSv (hsIn ▸ hsub₀ hs))
      have hqc : Kc * (e.cost M + D.bg M + ambBg M Am) ≤ Kc * (e.cost M + Δ.bg M + b) := by
        refine mul_le_mul_left'' ?_
        rw [add_assoc, add_assoc]
        exact add_le_add le_rfl (ActOK.bg_le ⟨hσ, S, Ae, hC, hR, hS, hb⟩)
      have hokb : ActOK M (TCtx.empty.bind dcl.arg dcl.argTy)
          (Finsupp.single dcl.parg (.live dcl.pKind dcl.sIn)) (b + (Δ.erase p).bg M)
          (Mem.empty.set dcl.arg v) (fun y => if y = dcl.parg then some d else none) D Am := by
        refine ⟨MemOK.arg (hargTy ▸ hvty), Finsupp.single dcl.parg (.at sig.pKind s),
          Ae + (S.erase p).entries, hC.call hSp hD dcl.parg, Rev.call hD, ?_, ?_⟩
        · rw [← hpKind]; exact PeriphsOK.single (hsIn ▸ hsub₀ hs)
        · rw [ambBg_add_entries]; exact add_le_add hb (hS.erase p).bg_le
      have hcont : ∀ v₁ s₁ K₁, v₁.ty = dcl.retTy → s₁ ∈ dcl.sOut → K₁ ≤ Fb Kc →
          StackOK P M Ψ Am E [⟨σ.set x v₁, H, T, ctlr, none⟩] (D.set d sig.pKind s₁) K₁
            (Q₂ K₁ b) (F₂ K₁) Θ₁' Δ₁' b b ⟨Θ₁', Δ₁', b, H, T⟩ none := by
        intro v₁ s₁ K₁ hv hs₁ _
        exact .base hrest hex hΘf (ActOK.weaken ⟨hσ.bind (hv.trans hretTy.symm), _, Ae,
          (hC.set hSp hH hD s₁).1, hR.set hC hSp hH hD s₁,
          hS.set p sig.pKind (by rw [hsOut]; exact hs₁), hb⟩ hΓ hΔ.le) hwsr hwcr hnextc hcapc
          (hsees.of_shape hshc) hfzo
      have hpot : Kc * (e.cost M + D.bg M + ambBg M Am) +
          ((Qb Kc (b + (Δ.erase p).bg M) + 0) +
            Fb Kc * (dcl.ret.cost M + Δb.bg M + (b + (Δ.erase p).bg M)) + Q₂ (Fb Kc) b) ≤
          Kc * (e.cost M + Δ.bg M + b) + sig.cost Kc (b + (Δ.erase p).bg M) +
            Q₂ (sig.clk Kc) b := by
        rw [hcost, hclk, add_zero]
        calc _ = Kc * (e.cost M + D.bg M + ambBg M Am) + (Qb Kc (b + (Δ.erase p).bg M)
                + Fb Kc * (dcl.ret.cost M + Δb.bg M + (b + (Δ.erase p).bg M))
                + Q₂ (Fb Kc) b) := by ring
          _ ≤ Kc * (e.cost M + Δ.bg M + b) + (Qb Kc (b + (Δ.erase p).bg M)
                + Fb Kc * (dcl.ret.cost M + Δb.bg M + (b + (Δ.erase p).bg M))
                + Q₂ (Fb Kc) b) := add_le_add hqc le_rfl
          _ = _ := by ring
      by_cases hΘe : Θ.IsEmpty
      · -- the caller has no pending threads: the callee inherits a thread-free view
        have hΘ₁ : Θ₁'.IsEmpty := ThreadCtx.IsEmpty.of_le ((hΘe.observe _).observe _) hΘ
        refine ⟨_, _, _, _, _, _, _,
          .push (Φc := fun K' => Q₂ K' b) (Xc := fun K' => F₂ K') (k := sig.pKind)
            (sOut := dcl.sOut) (Δc := Δ₁') (bc := b) (tvb := ⟨Θ₁', Δ₁', b, H, T⟩)
            (tvc := ⟨Θ₁', Δ₁', b, H, T⟩) (Vs := none) (Vsc := none)
            (.cmd hbody ⟨hCb, DevEnv.Ceil.of_none⟩ (fun _ _ h => h) (PCtx.Widen.refl _)
              (ThreadCtx.Le.refl _) ThreadCtx.WinShape.empty ThreadCtx.WinCover.empty
              (.nil ⟨hCb.mono hbody.le_W.2, DevEnv.Ceil.of_none⟩))
            ThreadCtx.empty_isEmpty hokb ThreadCtx.WinShape.empty ThreadCtx.WinCover.empty
            (fun _ => ⟨PCtx.HWClosed.single hsInC, ThreadCtx.SOutClosed.empty⟩)
            ThreadCtx.CapOK.empty (hsees.callee hH _ _ _) ⟨dcl.pKind, dcl.sIn, by simp⟩ (fun h => hfzs (Or.inl (hfzo h)))
            hretT (by rw [hpKind]; exact hΔb) hS' (fun _ _ h => hF2.2 _ _ _ _ h le_rfl) hF2.1
            le_self_add (Or.inl ⟨rfl, rfl⟩) (fun ev h => by cases h) (fun h => absurd hΘ₁ h)
            (fun h => absurd hΘ₁ h) (fun h => absurd hΘ₁ h)
            (Or.inl ⟨ThreadCtx.empty_isEmpty, rfl⟩) hcont, hpot, by simp only [hclk]; exact le_rfl,
          ThreadCtx.SameIds.of_empty hΘe hΘ₁, fun h => absurd hΘe h, fun _ => rfl⟩
      · -- the caller is a spawner: it is suspended, its view with `p` at `visit`
        have hws₁ : Θ.WinShape (Δ.set p sig.pKind sig.visit).shape := by
          rw [PCtx.shape_set_of hp]; exact hws
        have hambS : (Θ.observe (Δ.set p sig.pKind sig.visit)).AmbOK M :=
          hamb₁.of_observe (hws₁.observe rfl)
            ((PCtx.shape_set_of hp _).trans (PCtx.shape_set_of hp _).symm)
        refine ⟨_, _, _, _, _, _, _,
          .push (Φc := fun K' => Q₂ K' b) (Xc := fun K' => F₂ K') (k := sig.pKind)
            (sOut := dcl.sOut) (Δc := Δ₁') (bc := b)
            (tvb := ⟨Θ.observe (Δ.set p sig.pKind sig.visit), Δ.set p sig.pKind sig.visit, b,
              H, T⟩)
            (tvc := ⟨Θ₁', Δ₁', b, H, T⟩) (Vs := some ⟨d, sig.visit, ∅⟩) (Vsc := none)
            (.cmd hbody ⟨hCb, DevEnv.Ceil.visit hWbp hSv⟩ (fun _ _ h => h) (PCtx.Widen.refl _)
              (ThreadCtx.Le.refl _) ThreadCtx.WinShape.empty ThreadCtx.WinCover.empty
              (.nil ⟨hCb.mono hbody.le_W.2, (DevEnv.Ceil.visit hWbp hSv).mono hbody.le_W.2⟩))
            ThreadCtx.empty_isEmpty hokb ThreadCtx.WinShape.empty ThreadCtx.WinCover.empty
            (fun _ => ⟨PCtx.HWClosed.single hsInC, ThreadCtx.SOutClosed.empty⟩)
            ThreadCtx.CapOK.empty (hsees.callee hH _ _ _) ⟨dcl.pKind, dcl.sIn, by simp⟩ (fun h => hfzs (Or.inl (hfzo h)))
            hretT (by rw [hpKind]; exact hΔb) hS' (fun _ _ h => hF2.2 _ _ _ _ h le_rfl) hF2.1
            le_self_add
            (Or.inr ⟨rfl, rfl, rfl, rfl,
              (ThreadCtx.SameIds.observe _ _).trans (ThreadCtx.SameIds.of_le hΘ)⟩)
            ?_ (fun _ => rfl) (fun _ => hfzs (Or.inr hΘe))
            (fun _ => ⟨⟨Γ, σ, hok₀.retype hH hD hsV⟩, hws₁.observe rfl,
              ThreadCtx.WinCover.observe_self hws₁, (hcapo.set hnc _ _).observe _, hambS⟩)
            (Or.inl ⟨ThreadCtx.empty_isEmpty, rfl⟩) hcont, hpot, by simp only [hclk]; exact le_rfl,
          ThreadCtx.SameIds.observe _ _, fun _ => ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩,
          fun _ => rfl⟩
        intro ev hev
        simp only [Option.mem_def, Option.some.injEq] at hev; subst hev
        exact ⟨rfl, p, sig.pKind, hH, by simp,
          fun hc' => hnc (ThreadCtx.captures_of_observe hc'), by rw [PCtx.erase_set_self]⟩
  | @push σ parg d T ctl e x σc Hc Tc ctlc rc rest fz Γ Δ Θ Γf Δf Θf Q F b D Kc τ k S' sOut
      Φc Xc Θc Δc bc bb tv tvb tvc Vs Vsc hct hΘf hok hws hwc hclo hcapo hsees hplv hfzo hret hΔf hsub
      hΦc hXc hbb hlink hVs hVsS hfzb htvb htv hcl =>
    intro q tick as' D' K' htop hstep
    rcases ctl with _ | ⟨x₀, ctlr⟩
    · -- the callee is done: return to the caller through the clause
      cases hct
      cases hstep
      rename_i v hev
      obtain ⟨hσ, S, Ae, hC, hR, hS, hb⟩ := hok
      obtain ⟨v', hev', hvty⟩ := HasTy.eval hσ hret
      rw [hev] at hev'; cases hev'
      obtain ⟨s', hSp, hs'⟩ := hS.live hΔf
      obtain ⟨d', hH', hD'⟩ := hC.vis parg (by rw [hSp]; exact REntry.at_ne_zero)
      simp only [↓reduceIte, Option.some.injEq] at hH'
      subst hH'
      have hDd : D d = .at k s' := hD'.trans hSp
      have hcl' := hcl v s' Kc hvty (hsub hs') le_rfl
      rw [RPeriphs.set_eq_self hDd] at hcl'
      refine ⟨_, _, _, _, _, _, _, hcl', ?_, le_rfl, ?_, ?_, fun _ => rfl⟩
      · simp only [zero_add]
        refine add_le_add (mul_le_mul_left'' ?_) le_rfl
        rw [add_assoc, add_assoc]
        exact add_le_add le_rfl (ActOK.bg_le ⟨hσ, S, Ae, hC, hR, hS, hb⟩)
      · rcases htv with ⟨_, rfl⟩ | ⟨htvbE, rfl⟩
        · rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, _, _, _, hs⟩
          · exact ThreadCtx.SameIds.refl _
          · exact hs
        · refine ThreadCtx.SameIds.of_empty hΘf ?_
          rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, _, _, _, hs⟩
          · exact htvbE
          · exact fun t => ((hs t).1).1 (htvbE t)
      · intro hne
        rcases htv with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, hb', hH'', hT'', _⟩
          · exact ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩
          · exact ⟨hb'.symm, hH''.symm, hT''.symm, rfl, fun _ _ _ _ _ => rfl⟩
        · exact absurd hΘf hne
    obtain ⟨c, rfl, hc⟩ := htop _ rfl _ rfl
    rcases hc with hloc | ⟨x₁, g, e₁, p, rfl⟩
    · -- a local command of the callee
      have hfr := ActStep.local_frame hloc hstep
      have hstore := hstep.store
      obtain ⟨σ', ctl', Γ', Δ', Θ', Q', F', rfl, hct', hok', hq, hF, hws', hwc', hsame, hcl', hK',
        hcap', hsh', hcf, hKfz⟩ :=
        CtlTyped.step hM hΨ hP hΨc (fun _ _ hle hc => ⟨hc.1.mono hle, hc.2.mono hle⟩) hct hok hws
          hwc hclo hcapo hloc hstep
      have hagree : ∀ dv, dv ≠ d → D' dv = D dv := by
        intro dv hne
        refine hfr dv fun y => ?_
        by_cases hy : y = parg
        · simp [hy, Ne.symm hne]
        · simp [hy]
      -- the suspended view moves with the passed device, within the ceiling
      have hD'm : D' = D ∨ ∃ k₀ s₀ st, D d = .at k₀ s₀ ∧ D' = D.set d k₀ st := by
        rcases hstore with h₀ | ⟨x', d', k₀, s₀, st, hx', hD₀, rfl⟩
        · exact Or.inl h₀
        · have : d' = d := by
            by_cases hy : x' = parg
            · simp only [hy, ↓reduceIte, Option.some.injEq] at hx'; exact hx'.symm
            · simp [hy] at hx'
          subst this
          exact Or.inr ⟨k₀, s₀, st, hD₀, rfl⟩
      have htvb' : ¬ tvb.Θ.IsEmpty → TView.OK M Am tvb D' := by
        intro hne
        rcases hD'm with rfl | ⟨k₀, s₀, st, hD₀, rfl⟩
        · exact htvb hne
        · obtain ⟨ev, hev⟩ := Option.isSome_iff_exists.1 (hVsS hne)
          obtain ⟨hdev, p', k', hH', hΔ', _, _⟩ := hVs ev (by rw [hev]; rfl)
          have hceil := (hct'.ceil_view fun _ _ hle hc => ⟨hc.1.mono hle, hc.2.mono hle⟩).2
          obtain ⟨T₂, hT₂, hst⟩ := hok'.state_in (x := parg) (d := d) (k := k₀) (s := st)
            (by simp only [↓reduceIte]) (by simp [RPeriphs.set_apply])
          exact (htvb hne).move hH' hΔ' hD₀
            (hceil ev (by rw [hev]; rfl) parg _ _ (by simp [hdev]) hT₂ hst)
      rcases htv with ⟨hΘe, rfl⟩ | ⟨htvbE, rfl⟩
      · -- the thread view is inherited: unchanged
        have hΘe' : Θ'.IsEmpty := fun t => ((hsame t).1).1 (hΘe t)
        refine ⟨_, _, _, _, _, _, _,
          .push (Δc := Δc) (bc := bc) (tvc := tvc) (Vsc := Vsc) hct' hΘf hok' hws' hwc' hcl'
            hcap' (hsees.of_shape hsh') (PCtx.exists_live_of_shape hplv hsh') hfzo hret hΔf hsub hΦc hXc hbb hlink hVs hVsS hfzb htvb'
            (Or.inl ⟨hΘe', rfl⟩) (fun v s K'' hv hs hK => ?_), ?_, hXc hF,
          ThreadCtx.SameIds.refl _, fun hne => ⟨rfl, rfl, rfl, hKfz (hfzb hne), ?_⟩,
          fun h => hKfz (hfzo h)⟩
        · rw [RPeriphs.set_eq_of_agree hagree]
          exact hcl v s K'' hv hs (hK.trans hF)
        · calc _ = (q + Q' K' b) + F' K' * (e.cost M + Δf.bg M + b) + Φc (F' K') := by ring
            _ ≤ _ := add_le_add (add_le_add hq (mul_le_mul_of_nonneg_right hF zero_le)) (hΦc hF)
        · intro t th c' ht hc'
          rcases hD'm with rfl | ⟨k₀, s₀, st, hD₀, rfl⟩
          · rfl
          · obtain ⟨ev, hev⟩ := Option.isSome_iff_exists.1 (hVsS hne)
            obtain ⟨hdev, p', k', hH', hΔ', hnc', _⟩ := hVs ev (by rw [hev]; rfl)
            obtain ⟨⟨Γs, σs, hoks⟩, _, _, hcaps, _⟩ := htvb hne
            have hne' := hoks.dev_ne_free hcaps ht hΔ' hnc' hc' hH'
            simp [RPeriphs.set_apply, hne']
      · -- the callee's own view is the thread view
        refine ⟨_, _, _, _, _, _, _,
          .push (Δc := Δc) (bc := bc) (tvc := tvc) (Vsc := Vsc) hct' hΘf hok' hws' hwc' hcl'
            hcap' (hsees.of_shape hsh') (PCtx.exists_live_of_shape hplv hsh') hfzo hret hΔf hsub hΦc hXc hbb hlink hVs hVsS hfzb htvb'
            (Or.inr ⟨htvbE, rfl⟩) (fun v s K'' hv hs hK => ?_), ?_, hXc hF, hsame,
          fun hne => ⟨rfl, rfl, rfl, hK' hne, hcf⟩, fun h => hKfz (hfzo h)⟩
        · rw [RPeriphs.set_eq_of_agree hagree]
          exact hcl v s K'' hv hs (hK.trans hF)
        · calc _ = (q + Q' K' b) + F' K' * (e.cost M + Δf.bg M + b) + Φc (F' K') := by ring
            _ ≤ _ := add_le_add (add_le_add hq (mul_le_mul_of_nonneg_right hF zero_le)) (hΦc hF)
    · -- a nested call: push the new callee on top of this callee
      obtain ⟨Γ₁, Δ₁, Θ₁, W, Q₁, F₁, Γ₁', Δ₁', Θ₁', Q₂, F₂, hc, hcW, hΓ, hΔ, hΘ, hwsr, hwcr,
        hrest, rfl, rfl⟩ := hct.cons_inv
      have hnextc := CtlTyped.next_closed hP hΨc hc hΔ hΘ hclo
      have hcapc := (hc.capOK hcapo).of_le hΘ hΔ.le
      have hshc := hΔ.shape_eq.trans hc.shape_eq.1
      have hw₁ := hc.winShape hws
      rw [← hc.shape_eq.1, hΔ.le.shape_eq] at hw₁
      have hamb₁ : Θ₁.AmbOK M := ThreadCtx.AmbOK.of_le hΘ hw₁ hwsr (hrest.ambOK hΘf hwsr)
      cases hc with
      | @call _ _ _ _ _ _ _ _ sig S₀ hg hty hx hp hsub₀ hnc hfzs =>
      cases hstep
      rename_i dcl v d₁ k₁ s hgd hev hH hD
      have hpd : p = parg ∧ d₁ = d := by
        by_cases hp' : p = parg
        · subst hp'; simp only [↓reduceIte, Option.some.injEq] at hH; exact ⟨rfl, hH.symm⟩
        · simp [hp'] at hH
      obtain ⟨rfl, rfl⟩ := hpd
      obtain ⟨dcl', hd', hfd⟩ := hΨd g sig hg
      rw [hgd] at hd'; cases hd'
      obtain ⟨hargTy, hpKind, hsIn, hretTy, hsOut, ⟨Γb, Δb, Wb, Qb, Fb, S'', Sv, hbody, hretT,
        hΔb, hS'', hWbp, hSv, hcost, hclk⟩, hsInC, _⟩ := hfd
      have hok₀ := hok
      obtain ⟨hσ, S, Ae, hC, hR, hS, hb⟩ := hok
      have hSp := hR.lookup hH hD
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      obtain ⟨v', hev', hvty⟩ := HasTy.eval hσ hty
      rw [hev] at hev'; cases hev'
      have hF2 := hrest.mono hM hΨ
      have hCb := DevEnv.Ceil.callee hcW.1 hp hH hWbp hSv
      have hInSv : dcl.sIn ⊆ Sv := by
        have := hbody.le_W.1 dcl.parg
        rw [Finsupp.single_eq_same, hWbp] at this
        exact this.2
      have hsV : s ∈ sig.visit := hSv (hInSv (hsIn ▸ hsub₀ hs))
      have hqc : Kc * (e₁.cost M + D.bg M + ambBg M Am) ≤ Kc * (e₁.cost M + Δ.bg M + b) := by
        refine mul_le_mul_left'' ?_
        rw [add_assoc, add_assoc]
        exact add_le_add le_rfl (ActOK.bg_le ⟨hσ, S, Ae, hC, hR, hS, hb⟩)
      have hokb : ActOK M (TCtx.empty.bind dcl.arg dcl.argTy)
          (Finsupp.single dcl.parg (.live dcl.pKind dcl.sIn)) (b + (Δ.erase p).bg M)
          (Mem.empty.set dcl.arg v) (fun y => if y = dcl.parg then some d₁ else none) D Am := by
        refine ⟨MemOK.arg (hargTy ▸ hvty), Finsupp.single dcl.parg (.at sig.pKind s),
          Ae + (S.erase p).entries, hC.call hSp hD dcl.parg, Rev.call hD, ?_, ?_⟩
        · rw [← hpKind]; exact PeriphsOK.single (hsIn ▸ hsub₀ hs)
        · rw [ambBg_add_entries]; exact add_le_add hb (hS.erase p).bg_le
      have hpot : Kc * (e₁.cost M + D.bg M + ambBg M Am) +
          ((Qb Kc (b + (Δ.erase p).bg M) + 0) +
            Fb Kc * (dcl.ret.cost M + Δb.bg M + (b + (Δ.erase p).bg M)) +
            (Q₂ (Fb Kc) b + F₂ (Fb Kc) * (e.cost M + Δf.bg M + b) + Φc (F₂ (Fb Kc)))) ≤
          (Kc * (e₁.cost M + Δ.bg M + b) + sig.cost Kc (b + (Δ.erase p).bg M) +
            Q₂ (sig.clk Kc) b) + F₂ (sig.clk Kc) * (e.cost M + Δf.bg M + b) +
            Φc (F₂ (sig.clk Kc)) := by
        rw [hcost, hclk, add_zero]
        calc _ = Kc * (e₁.cost M + D.bg M + ambBg M Am) + (Qb Kc (b + (Δ.erase p).bg M)
                + Fb Kc * (dcl.ret.cost M + Δb.bg M + (b + (Δ.erase p).bg M))
                + (Q₂ (Fb Kc) b + F₂ (Fb Kc) * (e.cost M + Δf.bg M + b)
                  + Φc (F₂ (Fb Kc)))) := by ring
          _ ≤ Kc * (e₁.cost M + Δ.bg M + b) + (Qb Kc (b + (Δ.erase p).bg M)
                + Fb Kc * (dcl.ret.cost M + Δb.bg M + (b + (Δ.erase p).bg M))
                + (Q₂ (Fb Kc) b + F₂ (Fb Kc) * (e.cost M + Δf.bg M + b)
                  + Φc (F₂ (Fb Kc)))) := add_le_add hqc le_rfl
          _ = _ := by ring
      -- the caller's (this callee's) continuation after the nested call
      have hout : ∀ ev ∈ Vs, ev.dev = d₁ → dcl.sOut ⊆ ev.env := by
        intro ev hev hed
        rw [← hsOut]; exact DevEnv.Ceil.call_out hcW.2 hp hH ev hev hed
      by_cases hΘe : Θ.IsEmpty
      · -- this callee has no pending threads: the nested callee inherits its thread view
        have hΘ₁ : Θ₁'.IsEmpty := ThreadCtx.IsEmpty.of_le ((hΘe.observe _).observe _) hΘ
        have htvbD : ∀ s₁, s₁ ∈ dcl.sOut → ¬ tvb.Θ.IsEmpty →
            TView.OK M Am tvb (D.set d₁ sig.pKind s₁) := by
          intro s₁ hs₁ hne
          obtain ⟨ev, hev⟩ := Option.isSome_iff_exists.1 (hVsS hne)
          obtain ⟨hdev, p', k', hH', hΔ', _, _⟩ := hVs ev (by rw [hev]; rfl)
          exact (htvb hne).move hH' hΔ' hD (hout ev (by rw [hev]; rfl) hdev hs₁)
        have hcont : ∀ v₁ s₁ K₁, v₁.ty = dcl.retTy → s₁ ∈ dcl.sOut → K₁ ≤ Fb Kc →
            StackOK P M Ψ Am E (⟨σ.set x₁ v₁, fun y => if y = p then some d₁ else none, T,
              ctlr, some (e, x)⟩ :: ⟨σc, Hc, Tc, ctlc, rc⟩ :: rest) (D.set d₁ sig.pKind s₁) K₁
              (Q₂ K₁ b + F₂ K₁ * (e.cost M + Δf.bg M + b) + Φc (F₂ K₁)) (Xc (F₂ K₁)) Θ₁' Δ₁' b
              bb tvb Vs := by
          intro v₁ s₁ K₁ hv hs₁ hK
          refine .push (Δc := Δc) (bc := bc) (tvc := tvc) (Vsc := Vsc) hrest hΘf
            (ActOK.weaken ⟨hσ.bind (hv.trans hretTy.symm), _, Ae, (hC.set hSp hH hD s₁).1,
              hR.set hC hSp hH hD s₁, hS.set p sig.pKind (by rw [hsOut]; exact hs₁), hb⟩ hΓ
              hΔ.le) hwsr hwcr hnextc hcapc (hsees.of_shape hshc) (PCtx.exists_live_of_shape hplv hshc) hfzo hret hΔf hsub hΦc hXc hbb
            hlink hVs hVsS hfzb (htvbD s₁ hs₁) (Or.inl ⟨hΘ₁, rfl⟩)
            (fun v₂ s₂ K₂ hv₂ hs₂ hK₂ => ?_)
          rw [RPeriphs.set_set]
          refine hcl v₂ s₂ K₂ hv₂ hs₂ (hK₂.trans ?_)
          simp only [hclk]
          exact hF2.1 hK
        have hconc : tv.Θ.SameIds tvb.Θ ∧ (¬ tv.Θ.IsEmpty → tvb.b = tv.b ∧ tvb.H = tv.H ∧
            tvb.T = tv.T) := by
          rcases htv with ⟨_, rfl⟩ | ⟨htvbE, rfl⟩
          · exact ⟨ThreadCtx.SameIds.refl _, fun _ => ⟨rfl, rfl, rfl⟩⟩
          · exact ⟨ThreadCtx.SameIds.of_empty hΘe htvbE, fun h => absurd hΘe h⟩
        refine ⟨_, _, _, _, _, _, _,
          .push (Φc := fun K' => Q₂ K' b + F₂ K' * (e.cost M + Δf.bg M + b) + Φc (F₂ K'))
            (Xc := fun K' => Xc (F₂ K')) (k := sig.pKind) (sOut := dcl.sOut)
            (Δc := Δ₁') (bc := b) (tvb := tvb) (tvc := tvb) (Vs := Vs) (Vsc := Vs)
            (.cmd hbody ⟨hCb, DevEnv.Ceil.callee hcW.2 hp hH hWbp hSv⟩ (fun _ _ h => h)
              (PCtx.Widen.refl _) (ThreadCtx.Le.refl _) ThreadCtx.WinShape.empty
              ThreadCtx.WinCover.empty
              (.nil ⟨hCb.mono hbody.le_W.2,
                (DevEnv.Ceil.callee hcW.2 hp hH hWbp hSv).mono hbody.le_W.2⟩))
            ThreadCtx.empty_isEmpty hokb ThreadCtx.WinShape.empty ThreadCtx.WinCover.empty
            (fun _ => ⟨PCtx.HWClosed.single hsInC, ThreadCtx.SOutClosed.empty⟩)
            ThreadCtx.CapOK.empty (hsees.callee hH _ _ _) ⟨dcl.pKind, dcl.sIn, by simp⟩ (fun h => hfzs (Or.inl (hfzo h)))
            hretT (by rw [hpKind]; exact hΔb) hS''
            (fun _ _ h => add_le_add (add_le_add (hF2.2 _ _ _ _ h le_rfl)
              (mul_le_mul_of_nonneg_right (hF2.1 h) zero_le)) (hΦc (hF2.1 h)))
            (fun _ _ h => hXc (hF2.1 h)) (hbb.trans le_self_add) (Or.inl ⟨rfl, rfl⟩)
            (fun ev hev => by
              obtain ⟨h1, p', k', h2, h3, h4, h5⟩ := hVs ev hev
              exact ⟨h1, p', k', h2, h3, h4, h5.trans le_self_add⟩)
            hVsS (fun h => hfzs (Or.inl (hfzb h))) htvb (Or.inl ⟨ThreadCtx.empty_isEmpty, rfl⟩)
            hcont, hpot, by simp only [hclk]; exact le_rfl, hconc.1,
          fun h => ⟨(hconc.2 h).1, (hconc.2 h).2.1, (hconc.2 h).2.2, rfl,
            fun _ _ _ _ _ => rfl⟩, fun _ => rfl⟩
      · -- this callee is a spawner: it is suspended, its view with `p` at `visit`
        obtain ⟨htvbE, rfl⟩ : tvb.Θ.IsEmpty ∧
            tv = ⟨Θ, Δ, b, fun y => if y = p then some d₁ else none, T⟩ := by
          rcases htv with ⟨h, _⟩ | h
          · exact absurd h hΘe
          · exact h
        have hws₁ : Θ.WinShape (Δ.set p sig.pKind sig.visit).shape := by
          rw [PCtx.shape_set_of hp]; exact hws
        have hambS : (Θ.observe (Δ.set p sig.pKind sig.visit)).AmbOK M :=
          hamb₁.of_observe (hws₁.observe rfl)
            ((PCtx.shape_set_of hp _).trans (PCtx.shape_set_of hp _).symm)
        have hcont : ∀ v₁ s₁ K₁, v₁.ty = dcl.retTy → s₁ ∈ dcl.sOut → K₁ ≤ Fb Kc →
            StackOK P M Ψ Am E (⟨σ.set x₁ v₁, fun y => if y = p then some d₁ else none, T,
              ctlr, some (e, x)⟩ :: ⟨σc, Hc, Tc, ctlc, rc⟩ :: rest) (D.set d₁ sig.pKind s₁) K₁
              (Q₂ K₁ b + F₂ K₁ * (e.cost M + Δf.bg M + b) + Φc (F₂ K₁)) (Xc (F₂ K₁)) Θ₁' Δ₁' b
              bb ⟨Θ₁', Δ₁', b, fun y => if y = p then some d₁ else none, T⟩ Vs := by
          intro v₁ s₁ K₁ hv hs₁ hK
          refine .push (Δc := Δc) (bc := bc) (tvc := tvc) (Vsc := Vsc) hrest hΘf
            (ActOK.weaken ⟨hσ.bind (hv.trans hretTy.symm), _, Ae, (hC.set hSp hH hD s₁).1,
              hR.set hC hSp hH hD s₁, hS.set p sig.pKind (by rw [hsOut]; exact hs₁), hb⟩ hΓ
              hΔ.le) hwsr hwcr hnextc hcapc (hsees.of_shape hshc) (PCtx.exists_live_of_shape hplv hshc) hfzo hret hΔf hsub hΦc hXc hbb
            hlink hVs hVsS hfzb (fun h => absurd htvbE h) (Or.inr ⟨htvbE, rfl⟩)
            (fun v₂ s₂ K₂ hv₂ hs₂ hK₂ => ?_)
          rw [RPeriphs.set_set]
          refine hcl v₂ s₂ K₂ hv₂ hs₂ (hK₂.trans ?_)
          simp only [hclk]
          exact hF2.1 hK
        refine ⟨_, _, _, _, _, _, _,
          .push (Φc := fun K' => Q₂ K' b + F₂ K' * (e.cost M + Δf.bg M + b) + Φc (F₂ K'))
            (Xc := fun K' => Xc (F₂ K')) (k := sig.pKind) (sOut := dcl.sOut)
            (Δc := Δ₁') (bc := b)
            (tvb := ⟨Θ.observe (Δ.set p sig.pKind sig.visit), Δ.set p sig.pKind sig.visit,
              b, fun y => if y = p then some d₁ else none, T⟩)
            (tvc := ⟨Θ₁', Δ₁', b, fun y => if y = p then some d₁ else none, T⟩)
            (Vs := some ⟨d₁, sig.visit, ∅⟩) (Vsc := Vs)
            (.cmd hbody ⟨hCb, DevEnv.Ceil.visit hWbp hSv⟩ (fun _ _ h => h) (PCtx.Widen.refl _)
              (ThreadCtx.Le.refl _) ThreadCtx.WinShape.empty ThreadCtx.WinCover.empty
              (.nil ⟨hCb.mono hbody.le_W.2, (DevEnv.Ceil.visit hWbp hSv).mono hbody.le_W.2⟩))
            ThreadCtx.empty_isEmpty hokb ThreadCtx.WinShape.empty ThreadCtx.WinCover.empty
            (fun _ => ⟨PCtx.HWClosed.single hsInC, ThreadCtx.SOutClosed.empty⟩)
            ThreadCtx.CapOK.empty (hsees.callee hH _ _ _) ⟨dcl.pKind, dcl.sIn, by simp⟩ (fun h => hfzs (Or.inl (hfzo h)))
            hretT (by rw [hpKind]; exact hΔb) hS''
            (fun _ _ h => add_le_add (add_le_add (hF2.2 _ _ _ _ h le_rfl)
              (mul_le_mul_of_nonneg_right (hF2.1 h) zero_le)) (hΦc (hF2.1 h)))
            (fun _ _ h => hXc (hF2.1 h)) (hbb.trans le_self_add)
            (Or.inr ⟨rfl, rfl, rfl, rfl,
              (ThreadCtx.SameIds.observe _ _).trans (ThreadCtx.SameIds.of_le hΘ)⟩)
            ?_ (fun _ => rfl) (fun _ => hfzs (Or.inr hΘe))
            (fun _ => ⟨⟨Γ, σ, hok₀.retype hH hD hsV⟩, hws₁.observe rfl,
              ThreadCtx.WinCover.observe_self hws₁, (hcapo.set hnc _ _).observe _, hambS⟩)
            (Or.inl ⟨ThreadCtx.empty_isEmpty, rfl⟩) hcont, hpot, by simp only [hclk]; exact le_rfl,
          ThreadCtx.SameIds.observe _ _, fun _ => ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩,
          fun _ => rfl⟩
        intro ev hev
        simp only [Option.mem_def, Option.some.injEq] at hev; subst hev
        exact ⟨rfl, p, sig.pKind, by simp, by simp,
          fun hc' => hnc (ThreadCtx.captures_of_observe hc'), by rw [PCtx.erase_set_self]⟩

/-! ### Configuration typing -/

/-- **A pending thread is accounted for.**  The thread named `t` of the spawner (thread view
with ambient bound `b`, handle map `H`, thread-id map `T`), of type `th`, is reached through `T`; its pool entry captured
the device of `th.p` (which the body names by the same handle), and, by status:

* `pending`: the device is in a state of a hardware-closed set `S₀` from which the body is typed
  (frozen, from the closure memory, seeing only its handle), ending within `th.sOut` and
  visiting only `th.V`.  Its contribution is the body's summary at the ambient
  `b + th.amb` reserved at the spawn — what will be paid when it runs.
* `running`: exactly one segment belongs to it; that segment is a typed stack, with no pending
  threads, under the device envelope `(device, th.V, th.sOut)`, at the current store.  Its
  contribution is the stack's potential.
* `done`: the device rests in a stable state of `th.sOut`; it contributes nothing.

`b`, `H` and `T` are the spawner's; they do not change while threads are pending
(`StackOK.step`). -/
def ThreadOK (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtxA K St R)
    (Am : Multiset (K × St)) (tsegs : List (Seg St R))
    (pool : ThreadId → Option (PoolEntry St R)) (D : RPeriphs K St) (Kc b : R)
    (H : Var → Option Dev) (T : Var → Option ThreadId) (t : Var) (th : ThreadTy K St R) (φ : R) :
    Prop :=
  (∀ s ∈ th.sOut, P.stable th.k s) ∧ P.hwClose th.k th.V = th.V ∧
  ∃ id e, T t = some id ∧ pool id = some e ∧ H th.p = some e.dev ∧ e.p = th.p ∧
    match e.status with
    | .pending => ∃ (S₀ : Finset St) (s : St) (Γc Γb : TCtx K) (Δb Wb : PCtx K St)
        (Qa : R → R → R) (Fa : R → R) (Sout Wp : Finset St),
        D e.dev = .at th.k s ∧ s ∈ S₀ ∧ P.hwClose th.k S₀ = S₀ ∧ MemOK Γc e.σ ∧
        TypedA P M Ψ true Γc (Finsupp.single th.p (.live th.k S₀)) ThreadCtx.empty e.body
          Γb Δb ThreadCtx.empty Wb Qa Fa ∧
        Δb th.p = .live th.k Sout ∧ Sout ⊆ th.sOut ∧ Wb th.p = .live th.k Wp ∧ Wp ⊆ th.V ∧
        φ = Qa Kc (b + th.amb)
    | .running => ∃ (acts : List (Act St R)) (Φt Xt : R) (Θt : ThreadCtx K St R)
        (Δt : PCtx K St) (bt : R) (tvt : TView K St R) (Vst : Option (DevEnv St)),
        tsegs.filter (fun sg => sg.owner = some id) = [⟨some id, acts⟩] ∧
        StackOK P M Ψ Am (some ⟨e.dev, th.V, th.sOut⟩) acts D Kc Φt Xt Θt Δt bt
          (b + th.amb) tvt Vst ∧
        tvt.Θ.IsEmpty ∧ φ = Φt
    | .done => ∃ s, D e.dev = .at th.k s ∧ s ∈ th.sOut ∧ P.stable th.k s ∧ φ = 0

/-- **Typed machine configurations, with potential `Φ`.**  Every pending thread belongs to
`main`'s spawner (its thread view `tv`, possibly suspended below frozen callees).

* The segments are the thread segments `tsegs` above `main`'s segment; `main`'s activations
  `a :: ma` (running activation `a`) form a typed stack with no device envelope, with view
  `Θ Δ b`, thread view `tv`, potential `Φm`.
* `tids` lists exactly the pending threads of `tv.Θ`; each is accounted for (`ThreadOK`) with a
  contribution `φ t`; distinct names reach distinct runtime ids.
* Every thread segment belongs to a running thread of `tids`, and every pool entry is reached
  from `tids` (no stray entry whose device hardware could still move).
* Waiting `await` frames occur only at the head of `main`'s running activation (so draining
  timers touches nothing else).
* The potential is `main`'s plus the threads' contributions.

Running threads are typed at the current store; that this survives other threads' devices
moving (within their envelopes) is a lemma of the step proof, not part of the invariant. -/
def CfgTyped (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtxA K St R)
    (Am : Multiset (K × St)) (c : Config K St R) (Φ : R) : Prop :=
  ∃ (tsegs : List (Seg St R)) (a : Act St R) (ma : List (Act St R)) (Φm Xm : R)
    (Θ : ThreadCtx K St R) (Δ : PCtx K St) (b bm : R) (tv : TView K St R)
    (Vs : Option (DevEnv St)) (tids : Finset Var) (φ : Var → R),
    c.segs = tsegs ++ [⟨none, a :: ma⟩] ∧
    StackOK P M Ψ Am none (a :: ma) c.D c.K Φm Xm Θ Δ b bm tv Vs ∧
    (∀ t, t ∈ tids ↔ tv.Θ t ≠ none) ∧
    (∀ t ∈ tids, ∀ th, tv.Θ t = some th →
      ThreadOK P M Ψ Am tsegs c.pool c.D c.K tv.b tv.H tv.T t th (φ t)) ∧
    (∀ t₁ ∈ tids, ∀ t₂ ∈ tids, tv.T t₁ = tv.T t₂ → t₁ = t₂) ∧
    (∀ sg ∈ tsegs, ∃ t ∈ tids, ∃ id e, tv.T t = some id ∧ sg.owner = some id ∧
      c.pool id = some e ∧ e.status = .running) ∧
    (∀ id e, c.pool id = some e → ∃ t ∈ tids, tv.T t = some id) ∧
    SegsNoAwait tsegs ∧ ActsNoAwait ma ∧ CtlNoAwait a.ctl.tail ∧
    (∀ tid id rem fb, a.ctl.head? = some (.awaitW tid id rem fb) → tv.T tid = some id) ∧
    Φ = Φm + ∑ t ∈ tids, φ t

/-- **A thread-free configuration is typed by its `main` stack alone**: with no pending
threads, an empty pool and only `main`'s segment, `CfgTyped` reduces to `StackOK` (with no
device envelope), and the potential is `main`'s.  This is the shape of the initial
configuration, and of every configuration of a program that never spawns. -/
theorem CfgTyped.of_main {c : Config K St R} {a : Act St R} {ma : List (Act St R)}
    {Am : Multiset (K × St)} {Φm Xm : R} {Θ : ThreadCtx K St R} {Δ : PCtx K St} {b bm : R}
    {tv : TView K St R} {Vs : Option (DevEnv St)}
    (hsegs : c.segs = [⟨none, a :: ma⟩]) (hpool : ∀ id, c.pool id = none)
    (htv : tv.Θ.IsEmpty) (h : StackOK P M Ψ Am none (a :: ma) c.D c.K Φm Xm Θ Δ b bm tv Vs)
    (hcm : ActsNoAwait (a :: ma)) :
    CfgTyped P M Ψ Am c Φm := by
  refine ⟨[], a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, ∅, fun _ => 0, hsegs, h, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro t; simp [htv t]
  · intro t ht; simp at ht
  · intro t₁ ht; simp at ht
  · intro sg hsg; simp at hsg
  · intro id e he; rw [hpool id] at he; cases he
  · intro sg hsg; simp at hsg
  · intro a' ha'; exact hcm a' (List.mem_cons_of_mem _ ha')
  · intro x hx; exact hcm a List.mem_cons_self x (List.mem_of_mem_tail hx)
  · intro tid id rem fb hh
    exact (hcm a List.mem_cons_self _ (List.mem_of_mem_head? hh)).elim
  · simp

/-! ### Stacks survive a visible device moving within the typing -/

/-- Setting two different devices commutes. -/
theorem RPeriphs.set_comm (D : RPeriphs K St) {c d : Dev} (h : c ≠ d) (k k' : K) (s s' : St) :
    (D.set c k s).set d k' s' = (D.set d k' s').set c k s := by
  ext y; simp only [RPeriphs.set_apply]; split_ifs with h₁ h₂ <;> first | rfl | (subst h₁; subst h₂; exact absurd rfl h)

/-- **A thread-free stack survives its running activation's device moving within the
typing.**  If the running activation sees device `c` through handle `x`, typed `x : k{V}`, then
moving `c` to any state of `V` keeps the stack typed, with the same potential and view.  The
running layer's agreement moves with it (`ActOK.move`); a called function's continuation clause
already ranges over every final state of the callee's device, which is `c` itself.  Used for
hardware moving a running thread's own device. -/
theorem StackOK.move {E : Option (DevEnv St)} {Am : Multiset (K × St)}
    {as D Kc Φ X Θ Δ b bb tv Vs} (h : StackOK P M Ψ Am E as D Kc Φ X Θ Δ b bb tv Vs)
    (htvE : tv.Θ.IsEmpty) {a : Act St R}
    (ha : as.head? = some a) {x : Var} {c : Dev} {k : K} {V : Finset St} {s' : St}
    (hH : a.H x = some c) (hΔ : Δ x = .live k V) (hs' : s' ∈ V) :
    StackOK P M Ψ Am E as (D.set c k s') Kc Φ X Θ Δ b bb tv Vs := by
  cases h with
  | base hct hex hΘf hok hws hwc hclo hcapo hsees hfzo =>
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    exact .base hct hex hΘf (hok.move hH hΔ hs') hws hwc hclo hcapo hsees hfzo
  | @push σ parg d T ctl e x' σc Hc Tc ctlc rc rest fz Γ Δ Θ Γf Δf Θf Q F b D Kc τ k' S' sOut
      Φc Xc Θc Δc bc bb tv tvb tvc Vs Vsc hct hΘf hok hws hwc hclo hcapo hsees hplv hfzo hret hΔf
      hsub hΦc hXc hbb hlink hVs hVsS hfzb htvb htv hcl =>
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    have hcd : c = d := by
      by_cases hx : x = parg
      · simp only [hx, ↓reduceIte, Option.some.injEq] at hH; exact hH.symm
      · simp [hx] at hH
    subst hcd
    have htvbE : tvb.Θ.IsEmpty := by
      rcases htv with ⟨_, rfl⟩ | ⟨h, _⟩
      · exact htvE
      · exact h
    refine .push (Δc := Δc) (bc := bc) (tvc := tvc) (Vsc := Vsc) hct hΘf (hok.move hH hΔ hs')
      hws hwc hclo hcapo hsees hplv hfzo hret hΔf hsub hΦc hXc hbb hlink hVs hVsS hfzb
      (fun h => absurd htvbE h) htv (fun v s K' hv hs hK => ?_)
    rw [RPeriphs.set_set]
    exact hcl v s K' hv hs hK

/-! ### Thread stacks survive devices they cannot see changing -/

/-- **A thread layer's agreement survives every device it cannot see changing.**  The layer
sees only `dev`, through a live handle, so its visible part is exactly `dev`'s entry and its
ambient is exactly "every other device, plus the outer ambient" — whatever states those are
in.  If `dev` is unchanged and that ambient still fits the layer's bound, the layer agrees with
the new store. -/
theorem ActOK.foreign {Γ : TCtx K} {Δ : PCtx K St} {b : R} {σ : Mem} {H : Var → Option Dev}
    {D : RPeriphs K St} {Am : Multiset (K × St)} (h : ActOK M Γ Δ b σ H D Am) {dev : Dev}
    (hH : ∀ x d, H x = some d → d = dev) (hlive : ∃ x k S, H x = some dev ∧ Δ x = .live k S)
    {D' : RPeriphs K St} (hdev : D' dev = D dev)
    (hamb : (D'.erase dev).bg M + ambBg M Am ≤ b) : ActOK M Γ Δ b σ H D' Am := by
  obtain ⟨hσ, S, Ae, hC, hR, hS, _⟩ := h
  obtain ⟨x, k, T, hx, hΔx⟩ := hlive
  obtain ⟨s, hSx, _⟩ := hS.live hΔx
  obtain ⟨d', hd', hDd'⟩ := hC.lookup hSx
  rw [hx] at hd'; cases hd'
  have hzero : ∀ y, y ≠ x → S y = 0 := by
    intro y hy
    by_contra hne
    obtain ⟨d'', hd'', _⟩ := hC.vis y hne
    have hdd := hH y d'' hd''; subst hdd
    exact hy (hC.inj y x _ hne (by rw [hSx]; exact REntry.at_ne_zero) hd'' hx)
  have hent : S.entries = {(k, s)} := by
    rw [RPeriphs.entries_of hSx]
    have he : S.erase x = 0 := by
      ext y
      rw [RPeriphs.erase_apply]
      split_ifs with hy
      · rfl
      · exact hzero y hy
    rw [he]
    simp [RPeriphs.entries]
  have hD'dev : D' dev = .at k s := hdev.trans hDd'
  refine ⟨hσ, S, RPeriphs.pop (D'.erase dev) Am, ⟨?_, hC.inj, ?_⟩, ?_, hS, ?_⟩
  · intro y hy
    obtain ⟨d'', hd'', hD''⟩ := hC.vis y hy
    have hdd := hH y d'' hd''; subst hdd
    exact ⟨_, hd'', hdev.trans hD''⟩
  · rw [pop_split hD'dev]
    unfold RPeriphs.pop
    rw [hent]
    simp
  · intro y d'' hd'' hne
    have hdd := hH y d'' hd''; subst hdd
    rw [hdev] at hne ⊢
    exact hR y _ hd'' hne
  · rw [ambBg_pop]; exact hamb

/-- **A thread's stack survives every device it cannot see changing** (the ambient lemma).
Every layer of a thread stack sees only the thread's device (`DevEnv.Sees`); if that device is
unchanged and every other device, plus the outer ambient, fits the stack's *bottom* ambient
bound `bb` (every layer's bound is at least `bb`), the stack is typed at the new store with the
same potential and view.  Callers' continuation clauses range over the device's final state,
which commutes with the change.  (A thread stack has no pending threads.)

This is what keeps a running or preempted thread typed while another thread, or hardware, moves
other devices: the condition is supplied by the spawner's window cover and the declared bound
`cost(win ∖ p) ≤ amb`, with `bb = b + amb`. -/
theorem StackOK.foreign {e : DevEnv St} {Am : Multiset (K × St)} {as D Kc Φ X Θ Δ b bb tv Vs}
    (h : StackOK P M Ψ Am (some e) as D Kc Φ X Θ Δ b bb tv Vs) {D' : RPeriphs K St}
    (hdev : D' e.dev = D e.dev) (hamb : (D'.erase e.dev).bg M + ambBg M Am ≤ bb)
    (htvE : tv.Θ.IsEmpty) :
    StackOK P M Ψ Am (some e) as D' Kc Φ X Θ Δ b bb tv Vs := by
  induction h generalizing D' with
  | base hct hex hΘf hok hws hwc hclo hcapo hsees hfzo =>
    obtain ⟨hH, hlive⟩ := hsees e rfl
    exact .base hct hex hΘf (hok.foreign hH hlive hdev hamb) hws hwc hclo hcapo hsees hfzo
  | @push σ parg d T ctl e' x σc Hc Tc ctlc rc rest fz Γ Δ Θ Γf Δf Θf Q F b D Kc τ k S' sOut
      Φc Xc Θc Δc bc bb tv tvb tvc Vs Vsc hct hΘf hok hws hwc hclo hcapo hsees hplv hfzo hret hΔf
      hsub hΦc hXc hbb hlink hVs hVsS hfzb htvb htv hcl ih =>
    obtain ⟨hH, hlive⟩ := hsees e rfl
    have hd : d = e.dev := hH parg d (by simp)
    subst hd
    have htvbE : tvb.Θ.IsEmpty := by
      rcases htv with ⟨_, rfl⟩ | ⟨h, _⟩
      · exact htvE
      · exact h
    have htvcE : tvc.Θ.IsEmpty := by
      rcases hlink with ⟨rfl, _⟩ | ⟨rfl, _, _, _, hs⟩
      · exact htvbE
      · exact fun t => ((hs t).1).1 (htvbE t)
    refine .push (Δc := Δc) (bc := bc) (tvc := tvc) (Vsc := Vsc) hct hΘf
      (hok.foreign hH hlive hdev (hamb.trans hbb)) hws hwc hclo hcapo hsees hplv hfzo hret hΔf
      hsub hΦc hXc hbb hlink hVs hVsS hfzb (fun h => absurd htvbE h) htv
      (fun v s K' hv hs hK => ?_)
    refine ih v s K' hv hs hK ?_ ?_ htvcE
    · simp [RPeriphs.set_apply]
    · rw [RPeriphs.erase_set]; exact hamb

/-- **A stack survives a pending thread's device moving within the thread's envelope** (by
the thread, or by hardware).  The spawner sees the device through the captured handle, typed at
a superset of the envelope (`CapOK`), whether it is running or suspended under callees (its
suspended agreement moves too).  The callees above a suspended spawner cannot see the device;
their agreement is re-established from the spawner's (`ActOK.foreign`, its ambient within the
callee's bound).  The callers' continuation clauses commute with the move. -/
theorem StackOK.move_tv {E : Option (DevEnv St)} {Am : Multiset (K × St)}
    {as D Kc Φ X Θ Δ b bb tv Vs} (h : StackOK P M Ψ Am E as D Kc Φ X Θ Δ b bb tv Vs) :
    ∀ {t : Var} {th : ThreadTy K St R} {c : Dev} {s' : St}, tv.Θ t = some th →
      tv.H th.p = some c → s' ∈ th.V →
      StackOK P M Ψ Am E as (D.set c th.k s') Kc Φ X Θ Δ b bb tv Vs := by
  induction h with
  | base hct hex hΘf hok hws hwc hclo hcapo hsees hfzo =>
    intro t th c s' ht hH hs'
    obtain ⟨V', hV', hVV'⟩ := hcapo.1 t th ht
    exact .base hct hex hΘf (hok.move hH hV' (hVV' hs')) hws hwc hclo hcapo hsees hfzo
  | @push σ parg d T ctl e x σc Hc Tc ctlc rc rest fz Γ Δ Θ Γf Δf Θf Q F b D Kc τ k S' sOut
      Φc Xc Θc Δc bc bb tv tvb tvc Vs Vsc hct hΘf hok hws hwc hclo hcapo hsees hplv hfzo hret hΔf
      hsub hΦc hXc hbb hlink hVs hVsS hfzb htvb htv hcl ih =>
    intro t th c s' ht hH hs'
    rcases htv with ⟨hΘe, rfl⟩ | ⟨htvbE, rfl⟩
    · -- a suspended spawner below: move its agreement, re-establish the callee's
      have hne : ¬ tv.Θ.IsEmpty := fun h => by rw [h t] at ht; cases ht
      obtain ⟨⟨Γs, σs, hoks⟩, hwss, hwcs, hcaps, hambs⟩ := htvb hne
      obtain ⟨V', hV', hVV'⟩ := hcaps.1 t th ht
      obtain ⟨ev, hev⟩ := Option.isSome_iff_exists.1 (hVsS hne)
      obtain ⟨hdev, p', k', hH', hΔ', hnc', hchain⟩ := hVs ev (by rw [hev]; rfl)
      have hcd : c ≠ d := hoks.dev_ne_free hcaps ht hΔ' hnc' hH hH'
      obtain ⟨_, Sx, _, hCx, _, hSx, _⟩ := hoks
      obtain ⟨s₀, hSp, _⟩ := hSx.live hV'
      obtain ⟨c', hc', hDc⟩ := hCx.lookup hSp
      rw [hH] at hc'; cases hc'
      have htvb' : TView.OK M Am tv (D.set c th.k s') :=
        (htvb hne).move hH hV' hDc (hVV' hs')
      obtain ⟨Γs', σs', hoks'⟩ := htvb'.1
      have hamb' := hoks'.bg_erase_le hH' hΔ'
      refine .push (Δc := Δc) (bc := bc) (tvc := tvc) (Vsc := Vsc) hct hΘf
        (hok.foreign (dev := d) (fun y d' hy => ?_) ?_ (by simp [RPeriphs.set_apply, hcd.symm])
          (hamb'.trans (by rw [add_comm]; exact hchain)))
        hws hwc hclo hcapo hsees hplv hfzo hret hΔf hsub hΦc hXc hbb hlink hVs hVsS hfzb
        (fun _ => htvb') (Or.inl ⟨hΘe, rfl⟩) (fun v s K' hv hs hK => ?_)
      · by_cases hyp : y = parg
        · simp only [hyp, ↓reduceIte, Option.some.injEq] at hy; exact hy.symm
        · simp [hyp] at hy
      · obtain ⟨k₁, T₁, hT₁⟩ := hplv
        exact ⟨parg, k₁, T₁, by simp, hT₁⟩
      · rw [RPeriphs.set_comm _ hcd]
        rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, _, hHc, _, hsame⟩
        · exact ih v s K' hv hs hK ht hH hs'
        · obtain ⟨th', hth', hsth⟩ : ∃ th', Θc t = some th' ∧ th.Same th' := by
            rcases e' : Θc t with _ | th'
            · exact absurd ((hsame t).1.2 e') (by rw [ht]; simp)
            · exact ⟨th', rfl, (hsame t).2 th th' ht e'⟩
          obtain ⟨hp, hk, hV, _, _⟩ := hsth
          have hH₂ : Hc th'.p = some c := by rw [← hHc, ← hp]; exact hH
          have hs₂ : s' ∈ th'.V := by rw [← hV]; exact hs'
          have := ih v s K' hv hs hK hth' hH₂ hs₂
          rwa [← hk] at this
    · -- the callee is the spawner: its parameter's device is the captured one
      have hcd : c = d := by
        by_cases hx : th.p = parg
        · simp only [hx, ↓reduceIte, Option.some.injEq] at hH; exact hH.symm
        · simp [hx] at hH
      subst hcd
      obtain ⟨V', hV', hVV'⟩ := hcapo.1 t th ht
      refine .push (Δc := Δc) (bc := bc) (tvc := tvc) (Vsc := Vsc) hct hΘf
        (hok.move hH hV' (hVV' hs')) hws hwc hclo hcapo hsees hplv hfzo hret hΔf hsub hΦc hXc
        hbb hlink hVs hVsS hfzb (fun h => absurd htvbE h) (Or.inr ⟨htvbE, rfl⟩)
        (fun v s K' hv hs hK => ?_)
      rw [RPeriphs.set_set]
      exact hcl v s K' hv hs hK

/-! ### 3c, case 1: `main` runs alone -/

/-- A control stack whose head is a command and whose tail has no waiting `await` has none. -/
theorem CtlNoAwait.of_head {c : Cmd St R} {ctl : List (Ctl St R)} (h : CtlNoAwait ctl) :
    CtlNoAwait (.cmd c :: ctl) := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · trivial
  · exact h x hx

/-- No-`await` of a command-headed control stack is no-`await` of its tail. -/
theorem ctlNoAwait_cmd_cons {c : Cmd St R} {ctl : List (Ctl St R)} :
    CtlNoAwait (.cmd c :: ctl) ↔ CtlNoAwait ctl :=
  ⟨fun h x hx => h x (List.mem_cons_of_mem _ hx), CtlNoAwait.of_head⟩

/-- The empty control stack has no waiting `await`. -/
theorem ctlNoAwait_nil : CtlNoAwait ([] : List (Ctl St R)) ↔ True :=
  ⟨fun _ => trivial, fun _ x hx => by simp at hx⟩

/-- No-`await` of a list of activations, at a cons. -/
theorem actsNoAwait_cons {a : Act St R} {as : List (Act St R)} :
    ActsNoAwait (a :: as) ↔ CtlNoAwait a.ctl ∧ ActsNoAwait as := by
  refine ⟨fun h => ⟨h a List.mem_cons_self, fun a' ha' => h a' (List.mem_cons_of_mem _ ha')⟩,
    fun ⟨h₁, h₂⟩ a' ha' => ?_⟩
  rcases List.mem_cons.1 ha' with rfl | ha'
  · exact h₁
  · exact h₂ a' ha'

/-- **Steps of the running activation create no waiting `await`** (they run commands, push a
callee's body or return to a caller). -/
theorem ActStep.noAwait {Ψd : FCtx K St R} {A : Multiset (K × St)} {as D Kc q tick as' D' K'}
    (h : ActStep M Ψd A as D Kc q tick as' D' K') (hna : ActsNoAwait as) : ActsNoAwait as' := by
  cases h <;> simp only [actsNoAwait_cons, ctlNoAwait_cmd_cons, ctlNoAwait_nil, true_and] at hna ⊢ <;>
    tauto

/-- A typed stack has at least one activation. -/
theorem StackOK.cons {E : Option (DevEnv St)} {Am : Multiset (K × St)}
    {as D Kc Φ X Θ Δ b bb tv Vs} (h : StackOK P M Ψ Am E as D Kc Φ X Θ Δ b bb tv Vs) :
    ∃ a ma, as = a :: ma := by
  cases h <;> exact ⟨_, _, rfl⟩

/-- **A pending thread stays accounted for while `main` runs alone** (no thread segment): the
spawner's handle and thread-id maps and ambient bound are unchanged, the thread's type is the
same spawned thread (only its window may grow), and the store is unchanged at its device. -/
theorem ThreadOK.transfer_main {Am : Multiset (K × St)}
    {pool : ThreadId → Option (PoolEntry St R)} {D D' : RPeriphs K St} {Kc b φ : R}
    {H : Var → Option Dev} {T : Var → Option ThreadId} {t : Var} {th th' : ThreadTy K St R}
    (h : ThreadOK P M Ψ Am [] pool D Kc b H T t th φ) (hs : th.Same th')
    (hD : ∀ d, H th.p = some d → D' d = D d) :
    ThreadOK P M Ψ Am [] pool D' Kc b H T t th' φ := by
  obtain ⟨p, k, V, sOut, amb, win⟩ := th
  obtain ⟨p', k', V', sOut', amb', win'⟩ := th'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hs
  obtain ⟨hstab, hVc, id, e, hTa, hpe, hHa, hep, hst⟩ := h
  have hDe : D' e.dev = D e.dev := hD _ hHa
  refine ⟨hstab, hVc, id, e, hTa, hpe, hHa, hep, ?_⟩
  revert hst
  rcases e.status with _ | _ | _
  · rintro ⟨S₀, s, Γc, Γb, Δb, Wb, Qa, Fa, Sout, Wp, hDs, hrest⟩
    exact ⟨S₀, s, Γc, Γb, Δb, Wb, Qa, Fa, Sout, Wp, hDe.trans hDs, hrest⟩
  · rintro ⟨acts, Φt, Xt, Θt, Δt, bt, tvt, Vst, hf, _⟩
    simp at hf
  · rintro ⟨s, hDs, hrest⟩
    exact ⟨s, hDe.trans hDs, hrest⟩

/-- **3c, case 1: a step of `main` alone pays for itself.**  With no thread segment, `main`'s
running activation takes a local step, a call or a return.  `main`'s stack pays the step
(`StackOK.step`).  If no thread is pending the rest is vacuous.  Otherwise the spawner (running
or suspended under frozen callees) keeps its handle and thread-id maps and ambient bound, the
clock is frozen, the pending threads are the same, and their devices are not touched — so every
thread stays accounted for with the same contribution. -/
theorem CfgTyped.step_main (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk) {Ψd : FCtx K St R}
    (hP : P.WF) (hΨc : SigsClosedA P Ψ) (hΨd : SigsDerivedA P M Ψd Ψ)
    {Am : Multiset (K × St)} {c : Config K St R} {Φ : R} (hc : CfgTyped P M Ψ Am c Φ)
    {as : List (Act St R)} (hseg : c.segs = [⟨none, as⟩]) (htop : TopOK as)
    {q tick as' D' K'} (hstep : ActStep M Ψd Am as c.D c.K q tick as' D' K') :
    ∃ Φ', CfgTyped P M Ψ Am ⟨[⟨none, as'⟩], c.pool, D', K'⟩ Φ' ∧ q + Φ' ≤ Φ := by
  obtain ⟨tsegs, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, hsegs, hst, htids, hthr, hdist,
    hown, hpool, hnaT, hnaM, hnaH, _, rfl⟩ := hc
  rw [hseg] at hsegs
  obtain ⟨rfl, rfl⟩ : tsegs = [] ∧ as = a :: ma := by
    cases tsegs with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Seg.mk.injEq, true_and, and_true] at hsegs
      exact ⟨rfl, hsegs⟩
    | cons s t => simp at hsegs
  have hnaA : ActsNoAwait (a :: ma) := by
    intro a' ha'
    rcases List.mem_cons.1 ha' with rfl | ha'
    · obtain ⟨σ, H, T, ctl, r⟩ := a'
      cases ctl with
      | nil => intro x hx; simp at hx
      | cons x₀ ctl =>
        obtain ⟨c₀, rfl, _⟩ := htop _ rfl _ rfl
        exact CtlNoAwait.of_head hnaH
    · exact hnaM a' ha'
  have hnaA' := hstep.noAwait hnaA
  obtain ⟨Φ', X', Θ', Δ', b', tv', Vs', hst', hq, _, hsame, hrel, _⟩ :=
    hst.step hM hΨ hP hΨc hΨd htop hstep
  obtain ⟨a', ma', rfl⟩ := hst'.cons
  have hna' : ∀ tid id rem fb, a'.ctl.head? = some (.awaitW tid id rem fb) →
      tv'.T tid = some id := fun _ _ _ _ hh =>
    (hnaA' a' List.mem_cons_self _ (List.mem_of_mem_head? hh)).elim
  by_cases hΘ : tv.Θ.IsEmpty
  · -- no pending thread: the threads' part is empty before and after
    have htE : tids = ∅ :=
      Finset.eq_empty_of_forall_notMem fun t ht => (htids t).1 ht (hΘ t)
    subst htE
    have hΘ' : tv'.Θ.IsEmpty := fun t => ((hsame t).1).1 (hΘ t)
    refine ⟨Φ' + ∑ t ∈ (∅ : Finset Var), (fun _ => (0 : R)) t,
      ⟨[], a', ma', Φ', X', Θ', Δ', b', bm, tv', Vs', ∅, fun _ => 0, rfl, hst', ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, hna', rfl⟩, ?_⟩
    · intro t; simp [hΘ' t]
    · intro t ht; simp at ht
    · intro t ht; simp at ht
    · intro sg hsg; simp at hsg
    · intro id e he
      obtain ⟨t, ht, _⟩ := hpool id e he
      simp at ht
    · intro sg hsg; simp at hsg
    · intro a'' ha''; exact hnaA' a'' (List.mem_cons_of_mem _ ha'')
    · intro x hx; exact hnaA' a' List.mem_cons_self x (List.mem_of_mem_tail hx)
    · simp only [Finset.sum_empty, add_zero]; exact hq
  · -- threads pending: the spawner's maps, bound and the threads' devices are unchanged
    obtain ⟨hb', hH', hT', rfl, hfr⟩ := hrel hΘ
    refine ⟨Φ' + ∑ t ∈ tids, φ t,
      ⟨[], a', ma', Φ', X', Θ', Δ', b', bm, tv', Vs', tids, φ, rfl, hst', ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, hna', rfl⟩, ?_⟩
    · intro t; rw [htids t]; exact not_congr (hsame t).1
    · intro t ht th' hth'
      obtain ⟨th, hth⟩ := Option.ne_none_iff_exists'.1 ((htids t).1 ht)
      rw [hb', hH', hT']
      exact (hthr t ht th hth).transfer_main ((hsame t).2 th th' hth hth')
        (fun d hd => hfr t th d hth hd)
    · intro t₁ h₁ t₂ h₂ he
      exact hdist t₁ h₁ t₂ h₂ (by rwa [hT'] at he)
    · intro sg hsg; simp at hsg
    · intro id e he
      obtain ⟨t, ht, hT⟩ := hpool id e he
      exact ⟨t, ht, by rw [hT']; exact hT⟩
    · intro sg hsg; simp at hsg
    · intro a'' ha''; exact hnaA' a'' (List.mem_cons_of_mem _ ha'')
    · intro x hx; exact hnaA' a' List.mem_cons_self x (List.mem_of_mem_tail hx)
    · rw [← add_assoc]; exact add_le_add hq le_rfl

/-! ### 3c: generic tools for the remaining step cases -/

/-- **The running layer's facts**: agreement with the store, window cover, captured handles,
the backward window bound, what it sees, and its ceiling. -/
theorem StackOK.top {E : Option (DevEnv St)} {Am : Multiset (K × St)} {a : Act St R}
    {tl D Kc Φ X Θ Δ b bb tv Vs}
    (h : StackOK P M Ψ Am E (a :: tl) D Kc Φ X Θ Δ b bb tv Vs) :
    ∃ Γ, ActOK M Γ Δ b a.σ a.H D Am ∧ Θ.WinCover Δ ∧ Θ.CapOK Δ ∧ Θ.AmbOK M ∧
      DevEnv.Sees E a.H Δ ∧ DevEnv.Ceil E a.H Δ ∧
      (E.isSome = true → Δ.HWClosed P ∧ Θ.SOutClosed P) := by
  cases h with
  | base hct _ hΘf hok hws hwc hclo hcapo hsees =>
    exact ⟨_, hok, hwc, hcapo, hct.ambOK hΘf hws, hsees,
      (hct.ceil_view (fun _ _ hle hc => ⟨hc.1.mono hle, hc.2.mono hle⟩)).1, hclo⟩
  | push hct hΘf hok hws hwc hclo hcapo hsees =>
    exact ⟨_, hok, hwc, hcapo, hct.ambOK hΘf hws, hsees,
      (hct.ceil_view (fun _ _ hle hc => ⟨hc.1.mono hle, hc.2.mono hle⟩)).1, hclo⟩

/-- **The spawner's view agrees with the store** whenever threads are pending: the running
layer's own view if it is the spawner, or the suspended spawner's view kept by the callee
layer above it. -/
theorem StackOK.tvOK {E : Option (DevEnv St)} {Am : Multiset (K × St)}
    {as D Kc Φ X Θ Δ b bb tv Vs} (h : StackOK P M Ψ Am E as D Kc Φ X Θ Δ b bb tv Vs)
    (hne : ¬ tv.Θ.IsEmpty) : TView.OK M Am tv D := by
  cases h with
  | base hct _ hΘf hok hws hwc _ hcapo =>
    exact ⟨⟨_, _, hok⟩, hws, hwc, hcapo, hct.ambOK hΘf hws⟩
  | push hct hΘf hok hws hwc hclo hcapo hsees hplv hfzo hret hΔf hsub hΦc hXc hbb hlink hVs
      hVsS hfzb htvb htv hcl =>
    rcases htv with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact htvb hne
    · exact ⟨⟨_, _, hok⟩, hws, hwc, hcapo, hct.ambOK hΘf hws⟩

/-- With no pending threads in the thread view, the running layer has none either. -/
theorem StackOK.top_empty {E : Option (DevEnv St)} {Am : Multiset (K × St)}
    {as D Kc Φ X Θ Δ b bb tv Vs} (h : StackOK P M Ψ Am E as D Kc Φ X Θ Δ b bb tv Vs)
    (hE : tv.Θ.IsEmpty) : Θ.IsEmpty := by
  cases h with
  | base => exact hE
  | push hct hΘf hok hws hwc hclo hcapo hsees hplv hfzo hret hΔf hsub hΦc hXc hbb hlink hVs
      hVsS hfzb htvb htv hcl =>
    rcases htv with ⟨h, _⟩ | ⟨_, rfl⟩
    · exact h
    · exact hE

/-- **When the running layer has pending threads, it is the spawner**: the thread view is its
own view (callees under a suspended spawner have none). -/
theorem StackOK.tv_top {E : Option (DevEnv St)} {Am : Multiset (K × St)} {σ : Mem}
    {H : Var → Option Dev} {T : Var → Option ThreadId} {ctl : List (Ctl St R)}
    {r : Option (Expr × Var)} {tl D Kc Φ X Θ Δ b bb tv Vs}
    (h : StackOK P M Ψ Am E (⟨σ, H, T, ctl, r⟩ :: tl) D Kc Φ X Θ Δ b bb tv Vs)
    (hne : ¬ Θ.IsEmpty) : tv = ⟨Θ, Δ, b, H, T⟩ := by
  cases h with
  | base => rfl
  | push hct hΘf hok hws hwc hclo hcapo hsees hplv hfzo hret hΔf hsub hΦc hXc hbb hlink hVs
      hVsS hfzb htvb htv hcl =>
    rcases htv with ⟨h, _⟩ | ⟨_, rfl⟩
    · exact absurd h hne
    · rfl

/-- **The ambient a pending thread will see fits its declared bound**: in the spawner's
agreement, every device but the thread's own, plus the outer ambient, costs at most
`cost(Δ ∖ p) + b ≤ cost(win ∖ p) + b ≤ amb + b` (window cover, backward window bound). -/
theorem ActOK.thread_amb {Γ : TCtx K} {Δ : PCtx K St} {b : R} {σ : Mem}
    {H : Var → Option Dev} {D : RPeriphs K St} {Am : Multiset (K × St)}
    {Θ : ThreadCtx K St R} (h : ActOK M Γ Δ b σ H D Am) (hwc : Θ.WinCover Δ)
    (hcap : Θ.CapOK Δ) (hamb : Θ.AmbOK M) {t : Var} {th : ThreadTy K St R}
    (ht : Θ t = some th) {dev : Dev} (hH : H th.p = some dev) :
    (D.erase dev).bg M + ambBg M Am ≤ b + th.amb := by
  obtain ⟨V', hV', _⟩ := hcap.1 t th ht
  calc (D.erase dev).bg M + ambBg M Am ≤ (Δ.erase th.p).bg M + b := h.bg_erase_le hH hV'
    _ ≤ (th.win.erase th.p).bg M + b := add_le_add (PCtx.Le.bg_le (hwc t th ht)) le_rfl
    _ ≤ th.amb + b := add_le_add (hamb t th ht) le_rfl
    _ = b + th.amb := add_comm _ _

/-- **Distinct pending threads hold distinct devices**: they capture distinct handles, both
live, and live handles name distinct devices. -/
theorem ActOK.dev_ne {Γ : TCtx K} {Δ : PCtx K St} {b : R} {σ : Mem}
    {H : Var → Option Dev} {D : RPeriphs K St} {Am : Multiset (K × St)}
    {Θ : ThreadCtx K St R} (h : ActOK M Γ Δ b σ H D Am) (hcap : Θ.CapOK Δ)
    {t₁ t₂ : Var} {th₁ th₂ : ThreadTy K St R} (h₁ : Θ t₁ = some th₁) (h₂ : Θ t₂ = some th₂)
    (hne : t₁ ≠ t₂) {d₁ d₂ : Dev} (hH₁ : H th₁.p = some d₁) (hH₂ : H th₂.p = some d₂) :
    d₁ ≠ d₂ := by
  rintro rfl
  obtain ⟨_, S, _, hC, _, hS, _⟩ := h
  obtain ⟨V₁, hV₁, _⟩ := hcap.1 t₁ th₁ h₁
  obtain ⟨V₂, hV₂, _⟩ := hcap.1 t₂ th₂ h₂
  obtain ⟨s₁, hS₁, _⟩ := hS.live hV₁
  obtain ⟨s₂, hS₂, _⟩ := hS.live hV₂
  exact hne (hcap.2 t₁ t₂ th₁ th₂ h₁ h₂ (hC.inj th₁.p th₂.p d₁
    (by rw [hS₁]; exact REntry.at_ne_zero) (by rw [hS₂]; exact REntry.at_ne_zero) hH₁ hH₂))

/-- **A thread's device is in its envelope**: it is in the running layer's context, which is
under the stack's ceiling. -/
theorem StackOK.dev_in_env {e : DevEnv St} {Am : Multiset (K × St)} {as D Kc Φ X Θ Δ b bb tv Vs}
    (h : StackOK P M Ψ Am (some e) as D Kc Φ X Θ Δ b bb tv Vs) :
    ∃ k s, D e.dev = .at k s ∧ s ∈ e.env := by
  obtain ⟨a, tl, rfl⟩ := h.cons
  obtain ⟨_, hok, _, _, _, hsees, hceil, _⟩ := h.top
  obtain ⟨_, x, k, T, hx, hΔx⟩ := hsees e rfl
  obtain ⟨_, S, _, hC, _, hS, _⟩ := hok
  obtain ⟨s, hSx, hsT⟩ := hS.live hΔx
  obtain ⟨d', hd', hD'⟩ := hC.lookup hSx
  rw [hx] at hd'; cases hd'
  exact ⟨k, s, hD', hceil e rfl x k T hx hΔx hsT⟩

/-- The running layer of a thread stack sees only the thread's device. -/
theorem StackOK.head_dev {e : DevEnv St} {Am : Multiset (K × St)} {a : Act St R}
    {tl D Kc Φ X Θ Δ b bb tv Vs}
    (h : StackOK P M Ψ Am (some e) (a :: tl) D Kc Φ X Θ Δ b bb tv Vs) :
    ∀ x d, a.H x = some d → d = e.dev := by
  obtain ⟨_, _, _, _, _, hsees, _, _⟩ := h.top
  exact (hsees e rfl).1

/-- **Transferring a thread's accounting** to a new configuration: the same spawned thread,
reached through the same runtime id and handle, its pool entry unchanged, its device unchanged
unless it is running, and, if running, its stack carried over (by `hrun`) with the same
potential. -/
theorem ThreadOK.transfer {Am : Multiset (K × St)} {tsegs tsegs' : List (Seg St R)}
    {pool pool' : ThreadId → Option (PoolEntry St R)} {D D' : RPeriphs K St} {Kc b φ : R}
    {H H' : Var → Option Dev} {T T' : Var → Option ThreadId} {t : Var}
    {th th' : ThreadTy K St R}
    (h : ThreadOK P M Ψ Am tsegs pool D Kc b H T t th φ) (hs : th.Same th')
    (hT : T' t = T t) (hH : H' th.p = H th.p)
    (hpool : ∀ id, T t = some id → pool' id = pool id)
    (hD : ∀ id e, T t = some id → pool id = some e → e.status ≠ .running →
      D' e.dev = D e.dev)
    (hrun : ∀ id e acts Φt Xt Θt Δt bt tvt Vst, T t = some id → pool id = some e →
      e.status = .running → tsegs.filter (fun sg => sg.owner = some id) = [⟨some id, acts⟩] →
      StackOK P M Ψ Am (some ⟨e.dev, th.V, th.sOut⟩) acts D Kc Φt Xt Θt Δt bt (b + th.amb)
        tvt Vst →
      tvt.Θ.IsEmpty →
      ∃ acts' Xt' Θt' Δt' bt' tvt' Vst',
        tsegs'.filter (fun sg => sg.owner = some id) = [⟨some id, acts'⟩] ∧
        StackOK P M Ψ Am (some ⟨e.dev, th.V, th.sOut⟩) acts' D' Kc Φt Xt' Θt' Δt' bt'
          (b + th.amb) tvt' Vst' ∧ tvt'.Θ.IsEmpty) :
    ThreadOK P M Ψ Am tsegs' pool' D' Kc b H' T' t th' φ := by
  obtain ⟨p, k, V, sOut, amb, win⟩ := th
  obtain ⟨p', k', V', sOut', amb', win'⟩ := th'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hs
  obtain ⟨hstab, hVc, id, e, hTa, hpe, hHa, hep, hst⟩ := h
  refine ⟨hstab, hVc, id, e, hT.trans hTa, (hpool id hTa).trans hpe, hH.trans hHa, hep, ?_⟩
  revert hst
  cases hes : e.status with
  | pending =>
    rintro ⟨S₀, s, Γc, Γb, Δb, Wb, Qa, Fa, Sout, Wp, hDs, hrest⟩
    exact ⟨S₀, s, Γc, Γb, Δb, Wb, Qa, Fa, Sout, Wp,
      (hD id e hTa hpe (by rw [hes]; decide)).trans hDs, hrest⟩
  | running =>
    rintro ⟨acts, Φt, Xt, Θt, Δt, bt, tvt, Vst, hf, hstk, hΘe, hφ⟩
    obtain ⟨acts', Xt', Θt', Δt', bt', tvt', Vst', hf', hstk', hΘe'⟩ :=
      hrun id e acts Φt Xt Θt Δt bt tvt Vst hTa hpe hes hf hstk hΘe
    exact ⟨acts', Φt, Xt', Θt', Δt', bt', tvt', Vst', hf', hstk', hΘe', hφ⟩
  | done =>
    rintro ⟨s, hDs, hrest⟩
    exact ⟨s, (hD id e hTa hpe (by rw [hes]; decide)).trans hDs, hrest⟩

/-- **Replacing the running layer's control stack** (await frames, spawns): if the new control
stack is typed from a view reached from the old one — with the same final contexts, no more
potential (after paying `q`), no later exit, the same shape, and the view invariants — the
stack is typed with the new top, its potential down by at least `q`.  The store, clock, handle
map and ambient bound are unchanged; a caller-chosen property `Pr` of the new view is passed
through. -/
theorem StackOK.retop {E : Option (DevEnv St)} {Am : Multiset (K × St)} {σ : Mem}
    {H : Var → Option Dev} {T : Var → Option ThreadId} {ctl : List (Ctl St R)}
    {r : Option (Expr × Var)} {tl D Kc Φ X Θ Δ b bb tv Vs}
    (h : StackOK P M Ψ Am E (⟨σ, H, T, ctl, r⟩ :: tl) D Kc Φ X Θ Δ b bb tv Vs)
    (htvp : tv = ⟨Θ, Δ, b, H, T⟩ ∨ tv.Θ.IsEmpty)
    {σ' : Mem} {T' : Var → Option ThreadId} {ctl' : List (Ctl St R)}
    (Pr : R → ThreadCtx K St R → PCtx K St → Prop)
    (hnew : ∀ {C : PCtx K St → Prop} {fz Γ Γf Δf Θf Q F},
      (∀ W W' : PCtx K St, W'.Le W → C W → C W') →
      CtlTyped P M Ψ C E.isSome fz Γ Δ Θ ctl Γf Δf Θf Q F →
      ActOK M Γ Δ b σ H D Am → Θ.WinShape Δ.shape → Θ.WinCover Δ → Θ.CapOK Δ →
      (E.isSome = true → Δ.HWClosed P ∧ Θ.SOutClosed P) →
      ∃ q Γ' Δ' Θ' Q' F',
        CtlTyped P M Ψ C E.isSome fz Γ' Δ' Θ' ctl' Γf Δf Θf Q' F' ∧
        ActOK M Γ' Δ' b σ' H D Am ∧ q + Q' Kc b ≤ Q Kc b ∧ F' Kc ≤ F Kc ∧
        Θ'.WinShape Δ'.shape ∧ Θ'.WinCover Δ' ∧ Θ'.CapOK Δ' ∧ Δ'.shape = Δ.shape ∧
        (E.isSome = true → Δ'.HWClosed P ∧ Θ'.SOutClosed P) ∧ Pr q Θ' Δ') :
    ∃ q Φ' X' Θ' Δ', StackOK P M Ψ Am E (⟨σ', H, T', ctl', r⟩ :: tl) D Kc Φ' X' Θ' Δ' b bb
      ⟨Θ', Δ', b, H, T'⟩ Vs ∧ q + Φ' ≤ Φ ∧ X' ≤ X ∧ Pr q Θ' Δ' := by
  cases h with
  | base hct hex hΘf hok hws hwc hclo hcapo hsees hfzo =>
    obtain ⟨q, Γ', Δ', Θ', Q', F', hct', hok', hq, hF, hws', hwc', hcap', hsh, hcl', hpr⟩ :=
      hnew (fun _ _ hle hc => ⟨hc.1.mono hle, hc.2.mono hle⟩) hct hok hws hwc hcapo hclo
    exact ⟨q, _, _, Θ', Δ', .base hct' hex hΘf hok' hws' hwc' hcl' hcap' (hsees.of_shape hsh) hfzo,
      hq, hF, hpr⟩
  | @push _ parg d _ _ e x σc Hc Tc ctlc rc rest fz Γ Δ Θ Γf Δf Θf Q F b D Kc τ k S' sOut
      Φc Xc Θc Δc bc bb tv tvb tvc Vs Vsc hct hΘf hok hws hwc hclo hcapo hsees hplv hfzo hret hΔf
      hsub hΦc hXc hbb hlink hVs hVsS hfzb htvb htv hcl =>
    have htvbE : tvb.Θ.IsEmpty := by
      rcases htv with ⟨hΘe, rfl⟩ | ⟨h, _⟩
      · rcases htvp with h | h
        · rw [h]; exact hΘe
        · exact h
      · exact h
    obtain ⟨q, Γ', Δ', Θ', Q', F', hct', hok', hq, hF, hws', hwc', hcap', hsh, hcl', hpr⟩ :=
      hnew (fun _ _ hle hc => ⟨hc.1.mono hle, hc.2.mono hle⟩) hct hok hws hwc hcapo hclo
    refine ⟨q, _, _, Θ', Δ', .push (Δc := Δc) (bc := bc) (tvc := tvc) (Vsc := Vsc) hct' hΘf hok'
      hws' hwc' hcl' hcap' (hsees.of_shape hsh) (PCtx.exists_live_of_shape hplv hsh) hfzo hret hΔf
      hsub hΦc hXc hbb hlink hVs hVsS hfzb htvb (Or.inr ⟨htvbE, rfl⟩)
      (fun v s K'' hv hs hK => hcl v s K'' hv hs (hK.trans hF)), ?_, hXc hF, hpr⟩
    calc _ = (q + Q' Kc b) + F' Kc * (e.cost M + Δf.bg M + b) + Φc (F' Kc) := by ring
      _ ≤ _ := add_le_add (add_le_add hq (mul_le_mul_of_nonneg_right hF zero_le)) (hΦc hF)

/-- A control stack starting with an `await` (command or waiting frame) has pending threads:
T-Await and waiting frames need the awaited thread to be pending. -/
theorem CtlTyped.await_ne {C : PCtx K St → Prop} {cl : Bool} {fz Γ Δ Θ} {x : Ctl St R}
    {ctl : List (Ctl St R)} {Γf Δf Θf Q F}
    (h : CtlTyped P M Ψ C cl fz Γ Δ Θ (x :: ctl) Γf Δf Θf Q F)
    (hx : (∃ tid n fb, x = .cmd (.await tid n fb)) ∨ (∃ tid id rem fb, x = .awaitW tid id rem fb)) :
    ¬ Θ.IsEmpty := by
  rcases hx with ⟨tid, n, fb, rfl⟩ | ⟨tid, id, rem, fb, rfl⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := h.cons_inv
    cases hc with
    | await hth => intro hE; rw [hE] at hth; cases hth
  · cases h with
    | awaitW hth => intro hE; rw [hE] at hth; cases hth

/-- **At an `await`, the running activation is the spawner**: its view is the thread view. -/
theorem StackOK.await_tv {E : Option (DevEnv St)} {Am : Multiset (K × St)} {σ : Mem}
    {H : Var → Option Dev} {T : Var → Option ThreadId} {x : Ctl St R} {ctl : List (Ctl St R)}
    {r : Option (Expr × Var)} {tl D Kc Φ X Θ Δ b bb tv Vs}
    (h : StackOK P M Ψ Am E (⟨σ, H, T, x :: ctl, r⟩ :: tl) D Kc Φ X Θ Δ b bb tv Vs)
    (hx : (∃ tid n fb, x = .cmd (.await tid n fb)) ∨ (∃ tid id rem fb, x = .awaitW tid id rem fb)) :
    tv = ⟨Θ, Δ, b, H, T⟩ := by
  refine h.tv_top ?_
  cases h with
  | base hct => exact hct.await_ne hx
  | push hct => exact hct.await_ne hx

/-- **At an `async`, the running activation is the spawner, or no thread is pending**: a callee
under a suspended spawner is frozen, and T-AsyncFun needs an unfrozen setting. -/
theorem StackOK.async_tv {E : Option (DevEnv St)} {Am : Multiset (K × St)} {σ : Mem}
    {H : Var → Option Dev} {T : Var → Option ThreadId} {tid p : Var} {cb : Cmd St R}
    {ctl : List (Ctl St R)} {r : Option (Expr × Var)} {tl D Kc Φ X Θ Δ b bb tv Vs}
    (h : StackOK P M Ψ Am E (⟨σ, H, T, .cmd (.async tid p cb) :: ctl, r⟩ :: tl) D Kc Φ X Θ Δ b
      bb tv Vs) :
    tv = ⟨Θ, Δ, b, H, T⟩ ∨ tv.Θ.IsEmpty := by
  cases h with
  | base => exact Or.inl rfl
  | push hct hΘf hok hws hwc hclo hcapo hsees hplv hfzo hret hΔf hsub hΦc hXc hbb hlink hVs
      hVsS hfzb htvb htv hcl =>
    rcases htv with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · by_cases hE : tv.Θ.IsEmpty
      · exact Or.inr hE
      · exfalso
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := hct.cons_inv
        cases hc with
        | async _ _ _ _ _ _ _ _ _ hfz => rw [hfzb hE] at hfz; cases hfz
    · exact Or.inl rfl

/-! ### 3c, case 2: `await` frames of `main` -/

/-- Splitting a segment list at its last segment (`main`'s). -/
theorem segs_split {tsegs tsegs₀ : List (Seg St R)} {x y : Seg St R}
    (h : tsegs ++ [x] = tsegs₀ ++ [y]) : tsegs = tsegs₀ ∧ x = y := by
  obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
  exact ⟨h₁, List.cons.inj h₂ |>.1⟩

/-- Draining timers when only `main`'s running activation can have a waiting frame (at its
head): only that head changes. -/
theorem Config.drain_main {tsegs : List (Seg St R)} {σ : Mem} {H : Var → Option Dev}
    {T : Var → Option ThreadId} {x : Ctl St R} {rest : List (Ctl St R)}
    {r : Option (Expr × Var)} {as : List (Act St R)} {pool : ThreadId → Option (PoolEntry St R)}
    {D : RPeriphs K St} {Kc d : R} (hT : SegsNoAwait tsegs) (hrest : CtlNoAwait rest)
    (has : ActsNoAwait as) :
    (⟨tsegs ++ [⟨none, ⟨σ, H, T, x :: rest, r⟩ :: as⟩], pool, D, Kc⟩ : Config K St R).drain d =
      ⟨tsegs ++ [⟨none, ⟨σ, H, T, x.drain d :: rest, r⟩ :: as⟩], pool, D, Kc⟩ := by
  have hT' := (Config.drain_eq_self (d := d) (c := ⟨tsegs, pool, D, Kc⟩) hT)
  have hA := (Config.drain_eq_self (d := d)
    (c := ⟨[⟨none, ⟨σ, H, T, rest, r⟩ :: as⟩], pool, D, Kc⟩)
    (segsNoAwait_cons hrest has (fun _ h => by simp at h)))
  have hT'' := congrArg Config.segs hT'
  have hA' := congrArg Config.segs hA
  simp only [Config.drain, List.map_cons, List.map_nil] at hT'' hA'
  simp only [Config.drain, Config.mk.injEq, and_true, List.map_append, List.map_cons, List.map_nil,
    hT'']
  simp only [List.cons.injEq, Seg.mk.injEq, Act.mk.injEq, true_and, and_true] at hA'
  rw [hA'.1, hA'.2]

/-- A thread of the context after an `await` (and its link) is a thread of the context before,
other than the awaited one, the same spawned thread. -/
theorem ThreadCtx.after_await_some {Θ Θf Θ' : ThreadCtx K St R} {tid : Var} {Δo : PCtx K St}
    (hle : (((Θ.erase tid).observe Δo).join Θf).Le Θ') {t : Var} {th' : ThreadTy K St R}
    (h : Θ' t = some th') : t ≠ tid ∧ ∃ th, Θ t = some th ∧ th.Same th' := by
  obtain ⟨b, hb, hbs⟩ := ThreadCtx.le_some hle h
  obtain ⟨a₁, _, ha₁, _, rfl⟩ := ThreadCtx.join_some hb
  obtain ⟨a₀, ha₀, rfl⟩ := ThreadCtx.observe_some ha₁
  obtain ⟨ha, hne⟩ := ThreadCtx.erase_some ha₀
  exact ⟨hne, a₀, ha, (ThreadTy.Same.refl a₀).trans hbs⟩

/-- Every other pending thread is still pending after an `await` (and its link). -/
theorem ThreadCtx.after_await_ne {Θ Θf Θ' : ThreadCtx K St R} {tid : Var} {Δo : PCtx K St}
    (hle : (((Θ.erase tid).observe Δo).join Θf).Le Θ') (hs : (Θ.erase tid).SameThreads Θf)
    {t : Var} (hne : t ≠ tid) (h : Θ t ≠ none) : Θ' t ≠ none := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 h
  have he : (Θ.erase tid) t = some a := by
    unfold ThreadCtx.erase; rw [Function.update_of_ne hne]; exact ha
  have hj : (((Θ.erase tid).observe Δo).join Θf) t ≠ none := by
    rcases hs t with ⟨e₁, _⟩ | ⟨a', b, e₁, e₂, _⟩
    · rw [he] at e₁; cases e₁
    · simp [ThreadCtx.join, ThreadCtx.observe, e₁, e₂]
  exact fun h' => hj (((ThreadCtx.SameIds.of_le hle) t).1.2 h')

/-- `CapOK` after an `await` (the computation of `TypedA.capOK`'s `await` case). -/
theorem ThreadCtx.CapOK.await_out {Θ Θf : ThreadCtx K St R} {Δ Δf : PCtx K St}
    (hcap : Θ.CapOK Δ) {tid : Var} {th : ThreadTy K St R} (hth : Θ tid = some th)
    (hf : Θf.CapOK Δf) (hs : (Θ.erase tid).SameThreads Θf) :
    (((Θ.erase tid).observe (Δ.set th.p th.k th.sOut)).join Θf).CapOK
      ((Δ.set th.p th.k th.sOut).join Δf) := by
  have hnc : ¬ (Θ.erase tid).Captures th.p := by
    rintro ⟨t', th', ht', hp'⟩
    obtain ⟨ht'', hne⟩ := ThreadCtx.erase_some ht'
    exact hne (hcap.2 t' tid th' th ht'' hth hp')
  exact (((hcap.erase tid).set hnc _ _).observe _).join hf (hs.observe_left _)

/-! ### Async slack items

The await cases below also report how much of the typed reservation they release unused.
There are three schedule-dependent kinds; each item's amount is a typed quantity of a
configuration typing, named by its spec:

* `wait` — unused waiting allowance of `main`'s waiting frame, priced at the frame's typed
  per-tick rate `w = cost(Δ) + b` (T-Await's `maxBg V + cost(Δ ∖ p) + b`, since `Δ p = V`),
  where `Δ, b` type the frame and agree with the store (`WaitRate`).  Released by ticks
  of a running thread (its time counts against the budget), by the rounding of a waiting
  tick, and in full when the awaited thread is joined.
* `fallback` — the fallback's summary `Q_fb K b`, never run because the thread finished
  (`FallbackSum`).
* `abandon` — the contribution of a thread abandoned at a timeout: the body's reserved summary
  `Q_a K (b + amb)` if it never ran, or its stack's remaining potential (`AbandonSum`). -/

/-- Kinds of async slack. -/
inductive ASlackKind where
  | wait | fallback | abandon

/-- A slack item: its kind and amount. -/
structure ASlack (R : Type) where
  kind : ASlackKind
  amount : R

/-- Total amount of a list of slack items. -/
def ASlack.total (L : List (ASlack R)) : R := (L.map ASlack.amount).sum

/-- `w` is the typed per-tick rate of `main`'s waiting frame in `c`: the frame is typed from
context `Δ` at ambient bound `b` agreeing with the store, and `w = cost(Δ) + b`. -/
def WaitRate (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtxA K St R)
    (Am : Multiset (K × St)) (c : Config K St R) (w : R) : Prop :=
  ∃ tsegs σ H T tid id rem fb rest r as, c.segs = tsegs ++
      [⟨none, ⟨σ, H, T, .awaitW tid id rem fb :: rest, r⟩ :: as⟩] ∧
    ∃ C fz Γ Δ Θ Γf Δf Θf Q F b,
      CtlTyped P M Ψ C false fz Γ Δ Θ (.awaitW tid id rem fb :: rest) Γf Δf Θf Q F ∧
      ActOK M Γ Δ b σ H c.D Am ∧ w = Δ.bg M + b

/-- `x` is the summary `Q_fb K b` of the fallback of `main`'s waiting frame in `c`, typed from
the frame's context, which agrees with the store. -/
def FallbackSum (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtxA K St R)
    (Am : Multiset (K × St)) (c : Config K St R) (x : R) : Prop :=
  ∃ tsegs σ H T tid id rem fb rest r as, c.segs = tsegs ++
      [⟨none, ⟨σ, H, T, .awaitW tid id rem fb :: rest, r⟩ :: as⟩] ∧
    ∃ C fz Γ Δ Θ Γf Δf Θf Q F b Γa Δa Θa Wa Qa Fa,
      CtlTyped P M Ψ C false fz Γ Δ Θ (.awaitW tid id rem fb :: rest) Γf Δf Θf Q F ∧
      ActOK M Γ Δ b σ H c.D Am ∧
      TypedA P M Ψ fz Γ Δ (Θ.erase tid) fb Γa Δa Θa Wa Qa Fa ∧ x = Qa c.K b

/-- `x` is the contribution (`ThreadOK`) of the thread awaited by `main`'s waiting frame in
`c`: its body's reserved summary if pending, its stack's potential if running. -/
def AbandonSum (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtxA K St R)
    (Am : Multiset (K × St)) (c : Config K St R) (x : R) : Prop :=
  ∃ tsegs σ H T tid id rem fb rest r as, c.segs = tsegs ++
      [⟨none, ⟨σ, H, T, .awaitW tid id rem fb :: rest, r⟩ :: as⟩] ∧
    ∃ tsegs' b' H' T' t th, ThreadOK P M Ψ Am tsegs' c.pool c.D c.K b' H' T' t th x ∧
      T' t = some id

/-- What a slack item released by a step from `c` to `c'` means, by kind. -/
def ASlack.Spec (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtxA K St R)
    (Am : Multiset (K × St)) (c c' : Config K St R) (i : ASlack R) : Prop :=
  match i.kind with
  | .wait => ∃ u w, i.amount = u * w ∧ (WaitRate P M Ψ Am c w ∨ WaitRate P M Ψ Am c' w)
  | .fallback => FallbackSum P M Ψ Am c i.amount
  | .abandon => AbandonSum P M Ψ Am c i.amount

/-- **`awaitStart` changes no potential**: the `await` command becomes a waiting frame with
nothing elapsed, typed by the same premises with the same summary. -/
theorem CfgTyped.awaitStart {Am : Multiset (K × St)} {c : Config K St R} {Φ : R}
    (hc : CfgTyped P M Ψ Am c Φ) {σ : Mem} {H : Var → Option Dev} {T : Var → Option ThreadId}
    {tid : Var} {n : ℕ} {fb : Cmd St R} {rest : List (Ctl St R)} {r : Option (Expr × Var)}
    {as : List (Act St R)} {id : ThreadId}
    (hseg : c.segs = [⟨none, ⟨σ, H, T, .cmd (.await tid n fb) :: rest, r⟩ :: as⟩])
    (hT : T tid = some id) :
    ∃ Φ', CfgTyped P M Ψ Am
      ⟨[⟨none, ⟨σ, H, T, .awaitW tid id (n : R) fb :: rest, r⟩ :: as⟩], c.pool, c.D, c.K⟩ Φ' ∧
      Φ' ≤ Φ := by
  obtain ⟨tsegs, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, hsegs, hst, htids, hthr, hdist, hown,
    hpool, hnaT, hnaM, hnaH, _, rfl⟩ := hc
  rw [hseg, ← List.nil_append [_]] at hsegs
  obtain ⟨rfl, hseq⟩ := segs_split hsegs
  simp only [Seg.mk.injEq, List.cons.injEq, true_and] at hseq
  obtain ⟨rfl, rfl⟩ := hseq
  obtain rfl := hst.await_tv (Or.inl ⟨_, _, _, rfl⟩)
  obtain ⟨q, Φ', X', Θ', Δ', hst', hq, _, rfl, rfl, rfl⟩ := hst.retop (Or.inl rfl)
    (σ' := σ) (T' := T) (ctl' := .awaitW tid id (n : R) fb :: rest)
    (fun q Θ' Δ' => q = 0 ∧ Θ' = Θ ∧ Δ' = Δ) (by
      intro C fz Γ Γf Δf Θf Q F hCd hct hok hws hwc hcap hcl
      obtain ⟨Γ₁, Δ₁, Θ₁, W, Q₁, F₁, Γ₁', Δ₁', Θ₁', Q₂, F₂, hc, hcW, hΓ, hΔ, hΘ, hws', hwc',
        hrest, rfl, rfl⟩ := hct.cons_inv
      cases hc with
      | @await _ _ _ _ _ _ _ th Γa Δa Θa Wa Qa Fa Sa hth hp hamb hfb hs hΔf hstab =>
        have hsh : (Δ.join (Δ.set th.p th.k th.sOut)).shape = Wa.shape :=
          (PCtx.shape_join (PCtx.shape_set_of hp _).symm).trans hfb.shape_eq.2.symm
        refine ⟨0, Γ, Δ, Θ, _, _, .awaitW hth hp hamb hfb (hCd _ _ (PCtx.le_join_right hsh) hcW)
          hs hΔf hstab hΓ hΔ hΘ hws' hwc' hrest, hok, ?_, le_rfl, hws, hwc, hcap, rfl, hcl,
          rfl, rfl, rfl⟩
        simp only [zero_add]
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right waitAllow_le zero_le) le_rfl)
          le_rfl)
  refine ⟨Φ' + ∑ t ∈ tids, φ t, ⟨[], _, _, Φ', X', _, _, b, bm, _, Vs, tids, φ, rfl, hst', htids,
    fun t ht th hth => (hthr t ht th hth).transfer_main (ThreadTy.Same.refl _)
      (fun _ _ => rfl), hdist, hown, hpool, hnaT, hnaM, hnaH, ?_, rfl⟩, ?_⟩
  · intro tid' id' rem' fb' hh
    simp only [List.head?_cons, Option.some.injEq] at hh
    cases hh
    exact hT
  · simpa only [zero_add] using add_le_add hq (le_refl (∑ t ∈ tids, φ t))


/-- **A waiting tick pays for itself**: the tick charges every device's background, at most the
frame's per-tick allowance `maxBg V + cost(Δ ∖ p) + b` (the captured device is in its envelope
`V`); draining lowers the budget by the same clock, and the waiting allowance drops by at least
one tick (`waitAllow_tick`). -/
theorem CfgTyped.awaitWait {Am : Multiset (K × St)} {c : Config K St R} {Φ : R}
    (hc : CfgTyped P M Ψ Am c Φ) {σ : Mem} {H : Var → Option Dev} {T : Var → Option ThreadId}
    {tid : Var} {id : ThreadId} {rem : R} {fb : Cmd St R} {rest : List (Ctl St R)}
    {r : Option (Expr × Var)} {as : List (Act St R)}
    (hseg : c.segs = [⟨none, ⟨σ, H, T, .awaitW tid id rem fb :: rest, r⟩ :: as⟩])
    (hpos : 0 < rem) :
    ∃ Φ' x, CfgTyped P M Ψ Am (Config.drain c.K ⟨c.segs, c.pool, c.D, c.K⟩) Φ' ∧
      (∃ u w, x = u * w ∧ WaitRate P M Ψ Am c w) ∧
      c.K * (c.D.bg M + ambBg M Am) + x + Φ' ≤ Φ := by
  obtain ⟨tsegs, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, hsegs, hst, htids, hthr, hdist, hown,
    hpool, hnaT, hnaM, hnaH, haw, rfl⟩ := hc
  have hseg' := hseg
  rw [hseg, ← List.nil_append [_]] at hsegs
  obtain ⟨rfl, hseq⟩ := segs_split hsegs
  simp only [Seg.mk.injEq, List.cons.injEq, true_and] at hseq
  obtain ⟨rfl, rfl⟩ := hseq
  obtain rfl := hst.await_tv (Or.inr ⟨_, _, _, _, rfl⟩)
  rw [hseg', ← List.nil_append [_], Config.drain_main (rest := rest) (fun _ h => by simp at h)
    (by simpa using hnaH) hnaM]
  obtain ⟨q, Φ', X', Θ', Δ', hst', hq, _, ⟨x, rfl, hx⟩, rfl, rfl⟩ := hst.retop (Or.inl rfl)
    (σ' := σ) (T' := T) (ctl' := .awaitW tid id (rem - c.K) fb :: rest)
    (fun q Θ' Δ' => (∃ x, q = c.K * (c.D.bg M + ambBg M Am) + x ∧
      ∃ u w, x = u * w ∧ WaitRate P M Ψ Am c w) ∧ Θ' = Θ ∧ Δ' = Δ) (by
      intro C fz Γ Γf Δf Θf Q F hCd hct hok hws hwc hcap hcl
      have hct0 := hct
      cases hct with
      | @awaitW _ _ _ _ _ _ _ th Γa Δa Θa Wa Qa Fa Sa Γ₁' Δ₁' Θ₁' _ Γ₂ Δ₂ Θ₂ Q₂ F₂
          hth hp hamb hfb hCf hs hΔf hstab hΓ hΔ hΘ hws' hwc' hrest =>
        have hbgΔ : Δ.bg M = M.maxBg th.k th.V + (Δ.erase th.p).bg M := by
          have := PCtx.bg_set M Δ th.p th.k th.V
          rwa [PCtx.set_eq_self hp] at this
        have hbg : c.D.bg M + ambBg M Am ≤ M.maxBg th.k th.V + (Δ.erase th.p).bg M + b := by
          rw [← hbgΔ]; exact hok.bg_le
        have htick := waitAllow_tick (K := c.K) hpos
        refine ⟨_, Γ, Δ, Θ, _, _, .awaitW hth hp hamb hfb hCf hs hΔf hstab hΓ hΔ hΘ hws' hwc'
          hrest, hok, ?_, le_rfl, hws, hwc, hcap, rfl, hcl,
          ⟨_, rfl, waitAllow rem c.K - (c.K + waitAllow (rem - c.K) c.K), Δ.bg M + b,
            by rw [hbgΔ],
            ⟨[], σ, H, T, tid, id, rem, fb, rest, r, as, by rw [hseg]; rfl,
              _, _, _, _, _, _, _, _, _, _, b, hct0, hok, rfl⟩⟩, rfl, rfl⟩
        calc c.K * (c.D.bg M + ambBg M Am) +
              (waitAllow rem c.K - (c.K + waitAllow (rem - c.K) c.K)) *
                (M.maxBg th.k th.V + (Δ.erase th.p).bg M + b) + (waitAllow (rem - c.K) c.K *
                (M.maxBg th.k th.V + (Δ.erase th.p).bg M + b) + Qa c.K b + Q₂ (max (Fa c.K) c.K) b)
            ≤ c.K * (M.maxBg th.k th.V + (Δ.erase th.p).bg M + b) +
              (waitAllow rem c.K - (c.K + waitAllow (rem - c.K) c.K)) *
                (M.maxBg th.k th.V + (Δ.erase th.p).bg M + b) + (waitAllow (rem - c.K) c.K *
                (M.maxBg th.k th.V + (Δ.erase th.p).bg M + b) + Qa c.K b +
                Q₂ (max (Fa c.K) c.K) b) :=
              add_le_add (add_le_add (mul_le_mul_left'' hbg) le_rfl) le_rfl
          _ = (waitAllow rem c.K - (c.K + waitAllow (rem - c.K) c.K) +
                (c.K + waitAllow (rem - c.K) c.K)) *
                (M.maxBg th.k th.V + (Δ.erase th.p).bg M + b) + Qa c.K b +
                Q₂ (max (Fa c.K) c.K) b := by ring
          _ = _ := by rw [tsub_add_cancel_of_le htick])
  refine ⟨Φ' + ∑ t ∈ tids, φ t, x, ⟨[], _, _, Φ', X', _, _, b, bm, _, Vs, tids, φ, rfl, hst',
    htids, fun t ht th hth => (hthr t ht th hth).transfer_main (ThreadTy.Same.refl _)
      (fun _ _ => rfl), hdist, hown, hpool, hnaT, hnaM, hnaH, ?_, rfl⟩, hx, ?_⟩
  · intro tid' id' rem' fb' hh
    simp only [List.head?_cons, Option.some.injEq] at hh
    cases hh
    exact haw _ _ _ _ rfl
  · rw [← add_assoc]; exact add_le_add hq le_rfl

/-- A stack with no waiting `await` has none in its tail either. -/
theorem CtlNoAwait.tail {ctl : List (Ctl St R)} (h : CtlNoAwait ctl) : CtlNoAwait ctl.tail :=
  fun x hx => h x (List.mem_of_mem_tail hx)

/-- A stack with no waiting `await` does not start with one. -/
theorem CtlNoAwait.head {ctl : List (Ctl St R)} (h : CtlNoAwait ctl) {tid : Var} {id : ThreadId}
    {rem : R} {fb : Cmd St R} (hh : ctl.head? = some (.awaitW tid id rem fb)) : False :=
  h _ (List.mem_of_mem_head? hh)

/-- **An awaited thread that finished is joined at no cost**: the device is in a stable exit
state of `sOut`, so `main` agrees with its context after the `await` (the body's exit states
joined with the fallback's), the rest of `main`'s stack is typed from there, and the frame's
waiting allowance and fallback are no longer needed.  The thread's contribution (`0`, done) is
dropped. -/
theorem CfgTyped.awaitDone (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk) {Am : Multiset (K × St)}
    {c : Config K St R} {Φ : R} (hc : CfgTyped P M Ψ Am c Φ) {σ : Mem} {H : Var → Option Dev}
    {T : Var → Option ThreadId} {tid : Var} {id : ThreadId} {rem : R} {fb : Cmd St R}
    {rest : List (Ctl St R)} {r : Option (Expr × Var)} {as : List (Act St R)}
    {e : PoolEntry St R}
    (hseg : c.segs = [⟨none, ⟨σ, H, T, .awaitW tid id rem fb :: rest, r⟩ :: as⟩])
    (hpe : c.pool id = some e) (hdone : e.status = .done) :
    ∃ Φ' x₁ x₂, CfgTyped P M Ψ Am ⟨[⟨none, ⟨σ, H, Function.update T tid none, rest, r⟩ :: as⟩],
      Function.update c.pool id none, c.D, c.K⟩ Φ' ∧
      (∃ u w, x₁ = u * w ∧ WaitRate P M Ψ Am c w) ∧ FallbackSum P M Ψ Am c x₂ ∧
      x₁ + x₂ + Φ' ≤ Φ := by
  obtain ⟨tsegs, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, hsegs, hst, htids, hthr, hdist, hown,
    hpool, hnaT, hnaM, hnaH, haw, rfl⟩ := hc
  rw [hseg, ← List.nil_append [_]] at hsegs
  obtain ⟨rfl, hseq⟩ := segs_split hsegs
  simp only [Seg.mk.injEq, List.cons.injEq, true_and] at hseq
  obtain ⟨rfl, rfl⟩ := hseq
  obtain rfl := hst.await_tv (Or.inr ⟨_, _, _, _, rfl⟩)
  have hTid : T tid = some id := haw tid id rem fb rfl
  obtain ⟨q, Φ', X', Θ', Δ', hst', hq, _, ⟨x₁, x₂, rfl, hx₁, hx₂⟩, hsome, hne, htidΘ⟩ :=
    hst.retop (Or.inl rfl)
    (σ' := σ) (T' := Function.update T tid none) (ctl' := rest)
    (fun q Θ' _ => (∃ x₁ x₂, q = x₁ + x₂ ∧ (∃ u w, x₁ = u * w ∧ WaitRate P M Ψ Am c w) ∧
      FallbackSum P M Ψ Am c x₂) ∧ (∀ t th', Θ' t = some th' → t ≠ tid ∧ ∃ th, Θ t = some th ∧
      th.Same th') ∧ (∀ t, t ≠ tid → Θ t ≠ none → Θ' t ≠ none) ∧ Θ tid ≠ none) (by
      intro C fz Γ Γf Δf Θf Q F hCd hct hok hws hwc hcap hcl
      have hct0 := hct
      have hok0 := hok
      cases hct with
      | @awaitW _ _ _ _ _ _ _ th Γa Δa Θa Wa Qa Fa Sa Γ₁' Δ₁' Θ₁' _ Γ₂ Δ₂ Θ₂ Q₂ F₂
          hth hp hamb hfb hCf hs hΔf hstab hΓ hΔ hΘ hws' hwc' hrest =>
        have htid : tid ∈ tids := (htids tid).2 (by simp [hth])
        obtain ⟨_, _, id', e', hTa, hpe', hHa, _, hst⟩ := hthr tid htid th hth
        dsimp only at hTa hHa
        rw [hTid] at hTa; cases hTa
        rw [hpe] at hpe'; cases hpe'
        simp only [hdone] at hst
        obtain ⟨s, hDs, hsO, _, _⟩ := hst
        obtain ⟨hσ, S, Ae, hC, hR, hS, hb⟩ := hok
        obtain ⟨s₀, hSp, _⟩ := hS.live hp
        obtain ⟨d', hd', hD'⟩ := hC.lookup hSp
        rw [hHa] at hd'; cases hd'
        rw [hDs] at hD'; cases hD'
        have hS' : PeriphsOK (Δ.set th.p th.k th.sOut) S := by
          rw [← RPeriphs.set_eq_self hSp]; exact hS.set _ _ hsO
        have hsh : (Δ.set th.p th.k th.sOut).shape = Δa.shape :=
          (PCtx.shape_set_of hp _).trans hfb.shape_eq.1.symm
        have hF2 := hrest.mono hM hΨ
        have hbgΔ : Δ.bg M = M.maxBg th.k th.V + (Δ.erase th.p).bg M := by
          have := PCtx.bg_set M Δ th.p th.k th.V
          rwa [PCtx.set_eq_self hp] at this
        refine ⟨_, Γ₁', Δ₁', Θ₁', _, _, hrest,
          ActOK.weaken ⟨hσ, S, Ae, hC, hR, hS', hb⟩
            (fun x τ h => TCtx.inter_sub_left _ _ x τ (hΓ x τ h))
            ((PCtx.le_join_left hsh).trans hΔ.le), ?_, hF2.1 (le_max_right _ _), hws', hwc',
          (hcap.await_out hth (hfb.capOK (hcap.erase tid)) hs).of_le hΘ hΔ.le,
          hΔ.shape_eq.trans ((PCtx.shape_join hsh).trans (PCtx.shape_set_of hp _)),
          (fun h => by cases h),
          ⟨_, _, rfl, ⟨waitAllow rem c.K, Δ.bg M + b, by rw [hbgΔ],
            ⟨[], σ, H, T, tid, id, rem, fb, rest, r, as, by rw [hseg]; rfl,
              _, _, _, _, _, _, _, _, _, _, b, hct0, hok0, rfl⟩⟩,
            ⟨[], σ, H, T, tid, id, rem, fb, rest, r, as, by rw [hseg]; rfl,
              _, _, _, _, _, _, _, _, _, _, b, _, _, _, _, _, _, hct0, hok0, hfb, rfl⟩⟩,
          fun t th' h => ThreadCtx.after_await_some hΘ h,
          fun t ht h => ThreadCtx.after_await_ne hΘ hs ht h, by simp [hth]⟩
        exact add_le_add le_rfl (hF2.2 _ _ _ _ (le_max_right _ _) le_rfl))
  have htid : tid ∈ tids := (htids tid).2 htidΘ
  refine ⟨Φ' + ∑ t ∈ tids.erase tid, φ t, x₁, x₂, ⟨[], _, _, Φ', X', _, _, b, bm, _, Vs,
    tids.erase tid, φ, rfl, hst', ?_, ?_, ?_, fun sg h => by simp at h, ?_, hnaT, hnaM,
    (hnaH.tail : _), ?_, rfl⟩, hx₁, hx₂, ?_⟩
  · intro t
    constructor
    · intro ht
      obtain ⟨hne', ht'⟩ := Finset.mem_erase.1 ht
      exact hne t hne' ((htids t).1 ht')
    · intro ht
      obtain ⟨th', hth'⟩ := Option.ne_none_iff_exists'.1 ht
      obtain ⟨hne', th, hth, _⟩ := hsome t th' hth'
      exact Finset.mem_erase.2 ⟨hne', (htids t).2 (by simp [hth])⟩
  · intro t ht th' hth'
    obtain ⟨hne', th, hth, hs⟩ := hsome t th' hth'
    have ht' := (Finset.mem_erase.1 ht).2
    refine (hthr t ht' th hth).transfer hs ?_ rfl ?_ (fun _ _ _ _ _ => rfl) ?_
    · dsimp only; exact Function.update_of_ne hne' _ _
    · intro id' hT'
      dsimp only at hT' ⊢
      refine Function.update_of_ne (fun h => hne' (hdist t ht' tid htid ?_)) _ _
      dsimp only; rw [hT', hTid, h]
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ hf; simp at hf
  · intro t₁ h₁ t₂ h₂ he
    have h₁' := Finset.mem_erase.1 h₁
    have h₂' := Finset.mem_erase.1 h₂
    simp only [Function.update_of_ne h₁'.1, Function.update_of_ne h₂'.1] at he
    exact hdist t₁ h₁'.2 t₂ h₂'.2 he
  · intro id' e' he'
    by_cases hid : id' = id
    · subst hid; simp at he'
    · dsimp only at he'
      rw [Function.update_of_ne hid] at he'
      obtain ⟨t, ht, hT'⟩ := hpool id' e' he'
      dsimp only at hT'
      have hne' : t ≠ tid := fun h => hid (by subst h; rw [hTid] at hT'; cases hT'; rfl)
      exact ⟨t, Finset.mem_erase.2 ⟨hne', ht⟩, by dsimp only; rw [Function.update_of_ne hne']; exact hT'⟩
  · intro tid' id' rem' fb' hh
    exact (hnaH.head hh).elim
  · rw [← add_assoc]
    exact add_le_add hq (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))

/-- **A timed-out `await` runs its fallback**: whether the thread was never scheduled
(`awaitTimeout`) or was running directly above (`timeoutRunning`, whose segment is dropped),
the frame becomes its fallback command, typed from the same context without the thread; its
waiting allowance is forfeited, and so is the thread's contribution.  The abandoned device stays
where it is, in its envelope, which `main`'s context still describes. -/
theorem CfgTyped.timeout (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk) {Am : Multiset (K × St)}
    {c : Config K St R} {Φ : R} (hc : CfgTyped P M Ψ Am c Φ) {tsegs₀ : List (Seg St R)}
    {σ : Mem} {H : Var → Option Dev} {T : Var → Option ThreadId} {tid : Var} {id : ThreadId}
    {rem : R} {fb : Cmd St R} {rest : List (Ctl St R)} {r : Option (Expr × Var)}
    {as : List (Act St R)}
    (hseg : c.segs = tsegs₀ ++ [⟨none, ⟨σ, H, T, .awaitW tid id rem fb :: rest, r⟩ :: as⟩])
    (hown₀ : ∀ sg ∈ tsegs₀, sg.owner = some id) :
    ∃ Φ' x, CfgTyped P M Ψ Am
      ⟨[⟨none, ⟨σ, H, Function.update T tid none, .cmd fb :: rest, r⟩ :: as⟩],
        Function.update c.pool id none, c.D, c.K⟩ Φ' ∧ AbandonSum P M Ψ Am c x ∧
      x + Φ' ≤ Φ := by
  obtain ⟨tsegs, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, hsegs, hst, htids, hthr, hdist, hown,
    hpool, hnaT, hnaM, hnaH, haw, rfl⟩ := hc
  rw [hseg] at hsegs
  obtain ⟨rfl, hseq⟩ := segs_split hsegs
  simp only [Seg.mk.injEq, List.cons.injEq, true_and] at hseq
  obtain ⟨rfl, rfl⟩ := hseq
  obtain rfl := hst.await_tv (Or.inr ⟨_, _, _, _, rfl⟩)
  have hTid : T tid = some id := haw tid id rem fb rfl
  obtain ⟨q, Φ', X', Θ', Δ', hst', hq, _, rfl, rfl, rfl, htidΘ⟩ := hst.retop (Or.inl rfl)
    (σ' := σ) (T' := Function.update T tid none) (ctl' := .cmd fb :: rest)
    (fun q Θ' Δ' => q = 0 ∧ Θ' = Θ.erase tid ∧ Δ' = Δ ∧ Θ tid ≠ none) (by
      intro C fz Γ Γf Δf Θf Q F hCd hct hok hws hwc hcap hcl
      cases hct with
      | @awaitW _ _ _ _ _ _ _ th Γa Δa Θa Wa Qa Fa Sa Γ₁' Δ₁' Θ₁' _ Γ₂ Δ₂ Θ₂ Q₂ F₂
          hth hp hamb hfb hCf hs hΔf hstab hΓ hΔ hΘ hws' hwc' hrest =>
        have hsh : (Δ.set th.p th.k th.sOut).shape = Δa.shape :=
          (PCtx.shape_set_of hp _).trans hfb.shape_eq.1.symm
        have hF2 := hrest.mono hM hΨ
        refine ⟨0, Γ, Δ, Θ.erase tid, _, _,
          .cmd hfb hCf (fun x τ h => TCtx.inter_sub_right _ _ x τ (hΓ x τ h))
            ((PCtx.Widen.join_right hsh fun h => by cases h).trans hΔ)
            ((ThreadCtx.le_join_right (hs.observe_left _)).trans hΘ) hws' hwc' hrest,
          hok, ?_, hF2.1 (le_max_left _ _), hws.erase tid, hwc.erase tid, hcap.erase tid, rfl,
          (fun h => by cases h), rfl, rfl, rfl, by simp [hth]⟩
        rw [zero_add]
        exact add_le_add (le_add_left le_rfl) (hF2.2 _ _ _ _ (le_max_left _ _) le_rfl))
  have htid : tid ∈ tids := (htids tid).2 htidΘ
  have hab : AbandonSum P M Ψ Am c (φ tid) := by
    obtain ⟨th, hth⟩ := Option.ne_none_iff_exists'.1 htidΘ
    exact ⟨tsegs₀, σ, H, T, tid, id, rem, fb, rest, r, as, hseg, _, _, _, _, tid, th,
      hthr tid htid th hth, hTid⟩
  have hnorun : ∀ id', id' ≠ id → tsegs₀.filter (fun sg => sg.owner = some id') = [] := by
    intro id' hid'
    refine List.filter_eq_nil_iff.2 fun sg hsg => ?_
    simp only [hown₀ sg hsg, Option.some.injEq, decide_eq_true_eq]
    exact fun h => hid' h.symm
  refine ⟨Φ' + ∑ t ∈ tids.erase tid, φ t, φ tid, ⟨[], _, _, Φ', X', _, _, b, bm, _, Vs,
    tids.erase tid, φ, rfl, hst', ?_, ?_, ?_, fun sg h => by simp at h, ?_,
    fun _ h => by simp at h, hnaM, (hnaH : _), ?_, rfl⟩, hab, ?_⟩
  · intro t
    by_cases hne : t = tid
    · subst hne; simp [ThreadCtx.erase]
    · simp only [Finset.mem_erase, ne_eq, hne, not_false_eq_true, true_and, ThreadCtx.erase,
        Function.update_of_ne hne]
      exact htids t
  · intro t ht th' hth'
    obtain ⟨hth, hne'⟩ := ThreadCtx.erase_some hth'
    have ht' := (Finset.mem_erase.1 ht).2
    have hTne : ∀ id', T t = some id' → id' ≠ id := fun id' hT' h =>
      hne' (hdist t ht' tid htid (by dsimp only; rw [hT', hTid, h]))
    refine (hthr t ht' th' hth).transfer (ThreadTy.Same.refl _) ?_ rfl ?_ (fun _ _ _ _ _ => rfl) ?_
    · dsimp only; exact Function.update_of_ne hne' _ _
    · intro id' hT'; dsimp only at hT' ⊢; exact Function.update_of_ne (hTne id' hT') _ _
    · exact
      (fun id' _ acts _ _ _ _ _ _ _ hT' _ _ hf _ _ => by
        rw [hnorun id' (hTne id' hT')] at hf; cases hf)
  · intro t₁ h₁ t₂ h₂ he
    have h₁' := Finset.mem_erase.1 h₁
    have h₂' := Finset.mem_erase.1 h₂
    simp only [Function.update_of_ne h₁'.1, Function.update_of_ne h₂'.1] at he
    exact hdist t₁ h₁'.2 t₂ h₂'.2 he
  · intro id' e' he'
    by_cases hid : id' = id
    · subst hid; simp at he'
    · dsimp only at he'
      rw [Function.update_of_ne hid] at he'
      obtain ⟨t, ht, hT'⟩ := hpool id' e' he'
      dsimp only at hT'
      have hne' : t ≠ tid := fun h => hid (by subst h; rw [hTid] at hT'; cases hT'; rfl)
      exact ⟨t, Finset.mem_erase.2 ⟨hne', ht⟩, by dsimp only; rw [Function.update_of_ne hne']; exact hT'⟩
  · intro tid' id' rem' fb' hh
    simp only [List.head?_cons, Option.some.injEq] at hh
    cases hh
  · rw [zero_add] at hq
    rw [← Finset.add_sum_erase tids φ htid]
    calc φ tid + (Φ' + ∑ t ∈ tids.erase tid, φ t)
        = Φ' + (φ tid + ∑ t ∈ tids.erase tid, φ t) := by ring
      _ ≤ _ := add_le_add hq le_rfl

/-! ### 3c, case 3: spawning a thread -/

/-- **A spawn pays for itself and reserves its body**: the spawn step costs at most T-Async's
`f·(maxSpawn + cost(Δ ∖ p) + b)`, and the body's summary at the declared ambient,
`Q_a f (b + amb)`, moves from `main`'s potential to the new pending thread's contribution
(like a closure whose cost is paid when it is created).  The new thread is accounted for:
its device is in the spawn-time states, closed under hardware steps, from which the frozen body
is typed in the closure memory; the spawner's context records the envelope `hwClose W_p`. -/
theorem CfgTyped.async (hP : P.WF) {Am : Multiset (K × St)} {c : Config K St R} {Φ : R}
    (hc : CfgTyped P M Ψ Am c Φ) {σ : Mem} {H : Var → Option Dev} {T : Var → Option ThreadId}
    {tid p : Var} {cb : Cmd St R} {rest : List (Ctl St R)} {r : Option (Expr × Var)}
    {as : List (Act St R)} {d : Dev} {k : K} {s : St} {id : ThreadId}
    (hseg : c.segs = [⟨none, ⟨σ, H, T, .cmd (.async tid p cb) :: rest, r⟩ :: as⟩])
    (hH : H p = some d) (hD : c.D d = .at k s) (hfresh : c.pool id = none) :
    ∃ Φ', CfgTyped P M Ψ Am
      ⟨[⟨none, ⟨σ, H, Function.update T tid (some id), rest, r⟩ :: as⟩],
        Function.update c.pool id (some ⟨d, cb, σ, p, .pending⟩), c.D, c.K⟩ Φ' ∧
      c.K * (M.spawnCost k s + (c.D.erase d).bg M + ambBg M Am) + Φ' ≤ Φ := by
  obtain ⟨tsegs, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, hsegs, hst, htids, hthr, hdist, hown,
    hpool, hnaT, hnaM, hnaH, haw, rfl⟩ := hc
  rw [hseg, ← List.nil_append [_]] at hsegs
  obtain ⟨rfl, hseq⟩ := segs_split hsegs
  simp only [Seg.mk.injEq, List.cons.injEq, true_and] at hseq
  obtain ⟨rfl, rfl⟩ := hseq
  have htvp := hst.async_tv
  obtain ⟨htids0, hthr0, hdist0, hpool0⟩ : (∀ t, t ∈ tids ↔ Θ t ≠ none) ∧
      (∀ t ∈ tids, ∀ th, Θ t = some th →
        ThreadOK P M Ψ Am [] c.pool c.D c.K b H T t th (φ t)) ∧
      (∀ t₁ ∈ tids, ∀ t₂ ∈ tids, T t₁ = T t₂ → t₁ = t₂) ∧
      (∀ id e, c.pool id = some e → ∃ t ∈ tids, T t = some id) := by
    rcases htvp with rfl | htvE
    · exact ⟨htids, hthr, hdist, hpool⟩
    · have hΘE := hst.top_empty htvE
      have htE : tids = ∅ :=
        Finset.eq_empty_of_forall_notMem fun t ht => (htids t).1 ht (htvE t)
      subst htE
      refine ⟨fun t => by simp [hΘE t], fun t ht => by simp at ht, fun t ht => by simp at ht,
        fun id e he => ?_⟩
      obtain ⟨t, ht, _⟩ := hpool id e he
      simp at ht
  set pool' := Function.update c.pool id (some (⟨d, cb, σ, p, .pending⟩ : PoolEntry St R))
    with hpool'
  set a' : Act St R := ⟨σ, H, Function.update T tid (some id), rest, r⟩ with ha'
  set cost := c.K * (M.spawnCost k s + (c.D.erase d).bg M + ambBg M Am) with hcost
  obtain ⟨q, Φ', X', Θ', Δ', hst', hq, _, th', φt, htidN, hth', rfl, hthr0', hrel⟩ := hst.retop htvp
    (σ' := σ) (T' := Function.update T tid (some id)) (ctl' := rest)
    (fun q Θ' _ => ∃ th' φt, Θ tid = none ∧ Θ' tid = some th' ∧ q = cost + φt ∧
      ThreadOK P M Ψ Am [] pool' c.D c.K b H (Function.update T tid (some id)) tid th' φt ∧
      ∀ t, t ≠ tid → (Θ' t = none ↔ Θ t = none) ∧
        ∀ x y, Θ t = some x → Θ' t = some y → x.Same y) (by
      intro C fz Γ Γf Δf Θf Q F hCd hct hok hws hwc hcap hcl
      obtain ⟨Γ₁, Δ₁, Θ₁, W, Q₁, F₁, Γ₁', Δ₁', Θ₁', Q₂, F₂, hc, hcW, hΓ, hΔ, hΘ, hws', hwc',
        hrest, rfl, rfl⟩ := hct.cons_inv
      have hcapc := (hc.capOK hcap).of_le hΘ hΔ.le
      have hshc := hΔ.shape_eq.trans hc.shape_eq.1
      cases hc with
      | @async _ _ _ _ _ _ k' S _ Γb Δb Wb Qa Fa Sout Wp amb hp hnc htid hunst hclS hb hΔb hstab
          hWb hfz =>
        have hok₀ := hok
        obtain ⟨hσ, Sr, Ae, hC, hR, hS, hbA⟩ := hok
        obtain ⟨s₀, hSp, hs₀⟩ := hS.live hp
        obtain ⟨d', hd', hD'⟩ := hC.lookup hSp
        rw [hH] at hd'; cases hd'
        rw [hD] at hD'; cases hD'
        have hSW : S ⊆ Wp := by
          have := hb.le_W.1 p
          rw [Finsupp.single_eq_same, hWb] at this
          exact this.2
        have hsV : s ∈ P.hwClose k Wp := Finset.mem_union_left _ (hSW hs₀)
        have hS' : PeriphsOK (Δ.set p k (P.hwClose k Wp)) Sr := by
          rw [← RPeriphs.set_eq_self hSp]; exact hS.set _ _ hsV
        have hcostle : cost ≤ c.K * (M.maxSpawn k S + (Δ.erase p).bg M + b) := by
          refine mul_le_mul_left'' ?_
          rw [add_assoc, add_assoc]
          exact add_le_add (Finset.le_sup (f := M.spawnCost k) hs₀) (hok₀.bg_erase_le hH hp)
        refine ⟨cost + Qa c.K (b + amb), Γ₁', Δ₁', Θ₁', _, _, hrest,
          ActOK.weaken ⟨hσ, Sr, Ae, hC, hR, hS', hbA⟩ hΓ hΔ.le,
          add_le_add (add_le_add hcostle le_rfl) le_rfl, le_rfl, hws', hwc', hcapc, hshc,
          (fun h => by cases h), ?_⟩
        rcases hΘ tid with ⟨e₁, _⟩ | ⟨a₀, th', w, e₁, e₂, hab, _⟩
        · simp at e₁
        · simp only [Function.update_self, Option.some.injEq] at e₁
          subst e₁
          refine ⟨th', Qa c.K (b + amb), htid, e₂, rfl, ?_, ?_⟩
          · have h0 : ThreadOK P M Ψ Am [] pool' c.D c.K b H (Function.update T tid (some id)) tid
                ⟨p, k, P.hwClose k Wp, Sout, amb, Δ.set p k (P.hwClose k Wp)⟩ (Qa c.K (b + amb)) :=
              ⟨hstab, hP.hwClose_idem _ _, id, ⟨d, cb, σ, p, .pending⟩, by simp,
                by simp [hpool'], hH, rfl, S, s, Γ, Γb, Δb, Wb, Qa, Fa, Sout, Wp, hD, hs₀, hclS,
                hσ, hb, hΔb, subset_rfl, hWb, Finset.subset_union_left, rfl⟩
            exact h0.transfer hab rfl rfl (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)
              (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hf => by simp at hf)
          · intro t hne
            refine ⟨?_, ?_⟩
            · have h1 := ((ThreadCtx.SameIds.of_le hΘ) t).1
              rw [Function.update_of_ne hne] at h1
              simp only [ThreadCtx.observe, Option.map_eq_none_iff] at h1
              exact h1.symm
            · intro x y hx hy
              rcases hΘ t with ⟨e₁, _⟩ | ⟨a₁, b₁, _, e₁, e₂', hab', _⟩
              · rw [Function.update_of_ne hne] at e₁; simp [ThreadCtx.observe, hx] at e₁
              · rw [Function.update_of_ne hne] at e₁
                rw [hy] at e₂'; cases e₂'
                obtain ⟨x', hx', rfl⟩ := ThreadCtx.observe_some e₁
                rw [hx] at hx'; cases hx'
                exact (ThreadTy.Same.refl x).trans hab')
  have hnotin : tid ∉ tids := fun h => (htids0 tid).1 h htidN
  have hTne : ∀ t ∈ tids, T t ≠ some id := by
    intro t ht hT
    obtain ⟨th, hth⟩ := Option.ne_none_iff_exists'.1 ((htids0 t).1 ht)
    obtain ⟨_, _, id', e', hTa, hpe', _⟩ := hthr0 t ht th hth
    rw [hT] at hTa; cases hTa
    rw [hfresh] at hpe'; cases hpe'
  refine ⟨Φ' + ∑ t ∈ insert tid tids, Function.update φ tid φt t,
    ⟨[], a', _, Φ', X', _, _, b, bm, _, Vs, insert tid tids, Function.update φ tid φt, rfl, hst', ?_,
      ?_, ?_, fun sg h => by simp at h, ?_, hnaT, hnaM, hnaH.tail, ?_, rfl⟩, ?_⟩
  · intro t
    by_cases hne : t = tid
    · subst hne; simp [hth']
    · rw [Finset.mem_insert, htids0 t]
      simp only [hne, false_or]
      exact (not_congr (hrel t hne).1).symm
  · intro t ht th'' hth''
    by_cases hne : t = tid
    · subst hne
      change Θ' _ = some th'' at hth''
      rw [hth'] at hth''; cases hth''
      rw [Function.update_self]; exact hthr0'
    · have ht' : t ∈ tids := (Finset.mem_insert.1 ht).resolve_left hne
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 ((htids0 t).1 ht')
      rw [Function.update_of_ne hne]
      refine (hthr0 t ht' x hx).transfer ((hrel t hne).2 x th'' hx hth'') ?_ rfl ?_
        (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hf => by simp at hf)
      · simp [ha', Function.update_of_ne hne]
      · intro id' hT'
        dsimp only at hT' ⊢
        refine Function.update_of_ne (fun h => hTne t ht' (by rw [hT', h])) _ _
  · intro t₁ h₁ t₂ h₂ he
    dsimp only at he
    by_cases e₁ : t₁ = tid <;> by_cases e₂ : t₂ = tid
    · exact e₁.trans e₂.symm
    · subst e₁
      rw [Function.update_self, Function.update_of_ne e₂] at he
      exact absurd he.symm (hTne t₂ ((Finset.mem_insert.1 h₂).resolve_left e₂))
    · subst e₂
      rw [Function.update_self, Function.update_of_ne e₁] at he
      exact absurd he (hTne t₁ ((Finset.mem_insert.1 h₁).resolve_left e₁))
    · rw [Function.update_of_ne e₁, Function.update_of_ne e₂] at he
      exact hdist0 t₁ ((Finset.mem_insert.1 h₁).resolve_left e₁) t₂
        ((Finset.mem_insert.1 h₂).resolve_left e₂) he
  · intro id' e' he'
    dsimp only at he'
    by_cases hid : id' = id
    · subst hid
      exact ⟨tid, Finset.mem_insert_self _ _, by simp [ha']⟩
    · rw [hpool', Function.update_of_ne hid] at he'
      obtain ⟨t, ht, hT'⟩ := hpool0 id' e' he'
      have hne : t ≠ tid := fun h => hnotin (by rw [← h]; exact ht)
      exact ⟨t, Finset.mem_insert_of_mem ht, by simp [ha', Function.update_of_ne hne]; exact hT'⟩
  · intro tid' id' rem' fb' hh
    exact (hnaH.head hh).elim
  · have hsum : ∑ t ∈ tids, Function.update φ tid φt t = ∑ t ∈ tids, φ t :=
      Finset.sum_congr rfl fun t ht =>
        Function.update_of_ne (fun h => hnotin (by rw [← h]; exact ht)) _ _
    rw [Finset.sum_insert hnotin, Function.update_self, hsum]
    calc cost + (Φ' + (φt + ∑ t ∈ tids, φ t)) = (cost + φt + Φ') + ∑ t ∈ tids, φ t := by ring
      _ ≤ _ := add_le_add hq le_rfl

/-! ### 3c, case 4: scheduling, completion and hardware steps -/

/-- A hardware step from a state of a closed set stays in it. -/
theorem mem_of_hwClose {P : Platform K St} {k : K} {T : Finset St} (hcl : P.hwClose k T = T)
    {s s' : St} (hs : s ∈ T) (hs' : s' ∈ P.hwReach k s) : s' ∈ T := by
  rw [← hcl]
  exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨s, hs, hs'⟩)

/-- **A thread's first activation agrees with the store**: it sees only its device, through its
handle typed with the spawn-time states, and everything else (plus the outer ambient) is its
ambient. -/
theorem ActOK.thread_start {Γc : TCtx K} {σc : Mem} (hσ : MemOK Γc σc) {D : RPeriphs K St}
    {Am : Multiset (K × St)} {p : Var} {dev : Dev} {k : K} {s : St} {S₀ : Finset St} {b' : R}
    (hD : D dev = .at k s) (hs : s ∈ S₀) (hamb : (D.erase dev).bg M + ambBg M Am ≤ b') :
    ActOK M Γc (Finsupp.single p (.live k S₀)) b' σc
      (fun y => if y = p then some dev else none) D Am := by
  refine ⟨hσ, Finsupp.single p (.at k s), RPeriphs.pop (D.erase dev) Am, ⟨?_, ?_, ?_⟩, ?_,
    PeriphsOK.single hs, ?_⟩
  · intro x hx
    by_cases hxp : x = p
    · subst hxp; exact ⟨dev, by simp, by simp [hD]⟩
    · exact absurd (Finsupp.single_eq_of_ne hxp) hx
  · intro x y d hx hy _ _
    by_cases hxp : x = p
    · by_cases hyp : y = p
      · rw [hxp, hyp]
      · exact absurd (Finsupp.single_eq_of_ne hyp) hy
    · exact absurd (Finsupp.single_eq_of_ne hxp) hx
  · rw [pop_split hD]
    unfold RPeriphs.pop
    rw [RPeriphs.entries_single]
    simp
  · intro x d hx _
    by_cases hxp : x = p
    · subst hxp
      simp only [↓reduceIte, Option.some.injEq] at hx
      subst hx
      simp [hD]
    · simp [hxp] at hx
  · rw [ambBg_pop]; exact hamb

/-- **A finished thread's device is in an exit state**: its bottom layer has run out of
commands, so its context is its final one, which the exit condition bounds. -/
theorem StackOK.finished {e : DevEnv St} {Am : Multiset (K × St)} {σ : Mem}
    {H : Var → Option Dev} {T : Var → Option ThreadId} {D Kc Φ X Θ Δ b bb tv Vs}
    (h : StackOK P M Ψ Am (some e) [⟨σ, H, T, [], none⟩] D Kc Φ X Θ Δ b bb tv Vs) :
    ∃ k s, D e.dev = .at k s ∧ s ∈ e.out := by
  cases h with
  | base hct hex hΘf hok hws hwc hclo hcapo hsees =>
    cases hct with
    | nil _ =>
      obtain ⟨_, x, k, T', hx, hΔx⟩ := hsees e rfl
      obtain ⟨_, S, _, hC, _, hS, _⟩ := hok
      obtain ⟨s, hSx, hsT⟩ := hS.live hΔx
      obtain ⟨d', hd', hD'⟩ := hC.lookup hSx
      rw [hx] at hd'; cases hd'
      exact ⟨k, s, hD', hex e rfl x k T' hx hΔx hsT⟩

/-- **Hardware moving a running thread's own device keeps its stack typed**: the device is in
the running layer's context, which is closed under hardware steps. -/
theorem StackOK.hw_self {e : DevEnv St} {Am : Multiset (K × St)} {as D Kc Φ X Θ Δ b bb tv Vs}
    (h : StackOK P M Ψ Am (some e) as D Kc Φ X Θ Δ b bb tv Vs) (htvE : tv.Θ.IsEmpty) {k : K}
    {s s' : St} (hD : D e.dev = .at k s) (hs' : s' ∈ P.hwReach k s) :
    StackOK P M Ψ Am (some e) as (D.set e.dev k s') Kc Φ X Θ Δ b bb tv Vs := by
  obtain ⟨a, tl, rfl⟩ := h.cons
  obtain ⟨_, hok, _, _, _, hsees, _, hclo⟩ := h.top
  obtain ⟨_, x, k₂, T₂, hx, hΔx⟩ := hsees e rfl
  obtain ⟨_, S, _, hC, _, hS, _⟩ := hok
  obtain ⟨s₂, hSx, hsT⟩ := hS.live hΔx
  obtain ⟨d', hd', hD'⟩ := hC.lookup hSx
  rw [hx] at hd'; cases hd'
  rw [hD] at hD'; cases hD'
  exact h.move htvE rfl hx hΔx (mem_of_hwClose ((hclo rfl).1 x _ _ hΔx) hsT hs')

/-- **Scheduling a pending thread changes no potential**: its body, typed (frozen) from the
spawn-time states in the closure memory, becomes a typed stack under the device envelope, whose
ambient fits `b + amb` by the spawner's window cover and declared bound; its potential is the
reserved summary. -/
theorem CfgTyped.preempt {Am : Multiset (K × St)} {c : Config K St R} {Φ : R}
    (hc : CfgTyped P M Ψ Am c Φ) {id : ThreadId} {e : PoolEntry St R}
    (hpe : c.pool id = some e) (hpend : e.status = .pending) :
    ∃ Φ', CfgTyped P M Ψ Am
      ⟨⟨some id, [⟨e.σ, fun y => if y = e.p then some e.dev else none, fun _ => none,
          [.cmd e.body], none⟩]⟩ :: c.segs,
        Function.update c.pool id (some { e with status := .running }), c.D, c.K⟩ Φ' ∧
      Φ' ≤ Φ := by
  obtain ⟨tsegs, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, hsegs, hst, htids, hthr, hdist, hown,
    hpool, hnaT, hnaM, hnaH, haw, rfl⟩ := hc
  obtain ⟨t, ht, hTt⟩ := hpool id e hpe
  obtain ⟨th, hth⟩ := Option.ne_none_iff_exists'.1 ((htids t).1 ht)
  obtain ⟨hstab, hVc, id', e', hTa, hpe', hHa, hep, hst'⟩ := hthr t ht th hth
  rw [hTt] at hTa; cases hTa
  rw [hpe] at hpe'; cases hpe'
  rw [hpend] at hst'
  obtain ⟨S₀, s, Γc, Γb, Δb, Wb, Qa, Fa, Sout, Wp, hDs, hs, hclS, hσ, hb, hΔb, hSout, hWb,
    hWpV, hφ⟩ := hst'
  obtain ⟨⟨_, _, hokm⟩, _, hwcm, hcapm, hambm⟩ :=
    hst.tvOK (fun hE => by rw [hE t] at hth; cases hth)
  have hamb := hokm.thread_amb hwcm hcapm hambm hth hHa
  have hnoseg : ∀ sg ∈ tsegs, sg.owner ≠ some id := by
    intro sg hsg hown'
    obtain ⟨t', _, id'', e'', _, hown'', hpe'', hrun''⟩ := hown sg hsg
    rw [hown'] at hown''; cases hown''
    rw [hpe] at hpe''; cases hpe''
    rw [hpend] at hrun''; cases hrun''
  set H₀ : Var → Option Dev := fun y => if y = e.p then some e.dev else none with hH₀
  set E : Option (DevEnv St) := some ⟨e.dev, th.V, th.sOut⟩ with hE
  have hCb : DevEnv.Ceil E H₀ Wb := by
    intro e₁ he₁ x k₁ S₁ hx hW
    simp only [hE, Option.mem_def, Option.some.injEq] at he₁; subst he₁
    by_cases hxp : x = e.p
    · rw [hxp, hep, hWb] at hW; cases hW; exact hWpV
    · simp [hH₀, hxp] at hx
  have hex : DevEnv.Exit E H₀ Δb := by
    intro e₁ he₁ x k₁ S₁ hx hΔ
    simp only [hE, Option.mem_def, Option.some.injEq] at he₁; subst he₁
    by_cases hxp : x = e.p
    · rw [hxp, hep, hΔb] at hΔ; cases hΔ; exact hSout
    · simp [hH₀, hxp] at hx
  have hok : ActOK M Γc (Finsupp.single th.p (.live th.k S₀)) (tv.b + th.amb) e.σ H₀ c.D Am := by
    rw [hH₀, hep]; exact ActOK.thread_start hσ hDs hs hamb
  have hsees : DevEnv.Sees E H₀ (Finsupp.single th.p (.live th.k S₀) : PCtx K St) := by
    intro e₁ he₁
    simp only [hE, Option.mem_def, Option.some.injEq] at he₁; subst he₁
    refine ⟨fun x d hx => ?_, th.p, th.k, S₀, by simp [hH₀, hep], by simp⟩
    by_cases hxp : x = e.p
    · simp only [hH₀, hxp, ↓reduceIte, Option.some.injEq] at hx; exact hx.symm
    · simp [hH₀, hxp] at hx
  have hstk := StackOK.base (Am := Am) (E := E) (T := fun _ => none) (Kc := c.K)
    (CtlTyped.cmd hb ⟨hCb, DevEnv.Ceil.of_none⟩ (fun _ _ h => h) (PCtx.Widen.refl _) (ThreadCtx.Le.refl _)
      ThreadCtx.WinShape.empty ThreadCtx.WinCover.empty (.nil ⟨hCb.mono hb.le_W.2, DevEnv.Ceil.of_none⟩))
    hex ThreadCtx.empty_isEmpty hok ThreadCtx.WinShape.empty ThreadCtx.WinCover.empty
    (fun _ => ⟨PCtx.HWClosed.single hclS, ThreadCtx.SOutClosed.empty⟩) ThreadCtx.CapOK.empty
    hsees (fun _ => rfl)
  set nseg : Seg St R := ⟨some id, [⟨e.σ, H₀, fun _ => none, [.cmd e.body], none⟩]⟩ with hnseg
  have hfilt : (nseg :: tsegs).filter (fun sg => sg.owner = some id) = [nseg] := by
    rw [List.filter_cons_of_pos (by simp [hnseg])]
    congr 1
    exact List.filter_eq_nil_iff.2 fun sg hsg => by simpa using hnoseg sg hsg
  have hfilt' : ∀ id', id' ≠ id → (nseg :: tsegs).filter (fun sg => sg.owner = some id') =
      tsegs.filter (fun sg => sg.owner = some id') := by
    intro id' hne
    rw [List.filter_cons_of_neg (by simp [hnseg]; exact fun h => hne h.symm)]
  refine ⟨Φm + ∑ t ∈ tids, φ t, ⟨nseg :: tsegs, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ,
    by simp only [hsegs, List.cons_append], hst, htids, ?_, hdist, ?_, ?_, ?_, hnaM, hnaH, haw, rfl⟩, le_rfl⟩
  · intro t' ht' th' hth'
    by_cases htt : t' = t
    · subst htt
      rw [hth] at hth'; cases hth'
      refine ⟨hstab, hVc, id, { e with status := .running }, hTt, by simp, hHa, hep, ?_⟩
      refine ⟨_, _, _, _, _, _, _, _, hfilt, hstk, ThreadCtx.empty_isEmpty, ?_⟩
      simp only [hφ, add_zero]
    · have hTne : ∀ id', tv.T t' = some id' → id' ≠ id := fun id' hT' h =>
        htt (hdist t' ht' t ht (by rw [hT', hTt, h]))
      refine (hthr t' ht' th' hth').transfer (ThreadTy.Same.refl _) rfl rfl ?_
        (fun _ _ _ _ _ => rfl) ?_
      · intro id' hT'; exact Function.update_of_ne (hTne id' hT') _ _
      · intro id' e'' acts Φt Xt Θt Δt bt tvt Vst hT' _ _ hf hstk' hΘe
        exact ⟨acts, Xt, Θt, Δt, bt, tvt, Vst, by rw [hfilt' id' (hTne id' hT')]; exact hf, hstk', hΘe⟩
  · intro sg hsg
    rcases List.mem_cons.1 hsg with rfl | hsg
    · exact ⟨t, ht, id, { e with status := .running }, hTt, rfl, by simp, rfl⟩
    · obtain ⟨t', ht', id'', e'', hT'', hown'', hpe'', hrun''⟩ := hown sg hsg
      have hne : id'' ≠ id := fun h => hnoseg sg hsg (by rw [hown'', h])
      exact ⟨t', ht', id'', e'', hT'', hown'', by dsimp only; rw [Function.update_of_ne hne]; exact hpe'',
        hrun''⟩
  · intro id' e'' he''
    by_cases hid : id' = id
    · subst hid; exact ⟨t, ht, hTt⟩
    · dsimp only at he''; rw [Function.update_of_ne hid] at he''; exact hpool id' e'' he''
  · exact segsNoAwait_cons (ctlNoAwait_cmd_cons.2 (fun _ h => by simp at h))
      (fun _ h => by simp at h) hnaT

/-- **A finished thread is marked done**: its device is in a stable exit state (its bottom
layer's final context is bounded by the exit set); its contribution drops to `0`. -/
theorem CfgTyped.threadDone {Am : Multiset (K × St)} {c : Config K St R} {Φ : R}
    (hc : CfgTyped P M Ψ Am c Φ) {id : ThreadId} {σ : Mem} {H : Var → Option Dev}
    {T : Var → Option ThreadId} {ss : List (Seg St R)} {e : PoolEntry St R}
    (hseg : c.segs = ⟨some id, [⟨σ, H, T, [], none⟩]⟩ :: ss) (hpe : c.pool id = some e) :
    ∃ Φ', CfgTyped P M Ψ Am ⟨ss, Function.update c.pool id (some { e with status := .done }),
      c.D, c.K⟩ Φ' ∧ Φ' ≤ Φ := by
  obtain ⟨tsegs, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, hsegs, hst, htids, hthr, hdist, hown,
    hpool, hnaT, hnaM, hnaH, haw, rfl⟩ := hc
  obtain ⟨tsegs₁, rfl, hss⟩ : ∃ tsegs₁, tsegs = ⟨some id, [⟨σ, H, T, [], none⟩]⟩ :: tsegs₁ ∧
      ss = tsegs₁ ++ [⟨none, a :: ma⟩] := by
    rw [hseg] at hsegs
    cases tsegs with
    | nil => simp at hsegs
    | cons s₁ t₁ =>
      simp only [List.cons_append, List.cons.injEq] at hsegs
      exact ⟨t₁, by rw [hsegs.1], hsegs.2⟩
  subst hss
  set seg : Seg St R := ⟨some id, [⟨σ, H, T, [], none⟩]⟩ with hsegd
  obtain ⟨t, ht, id', e', hTt, hown₁, hpe', hrun⟩ := hown seg List.mem_cons_self
  simp only [hsegd, Option.some.injEq] at hown₁; subst hown₁
  rw [hpe] at hpe'; cases hpe'
  obtain ⟨th, hth⟩ := Option.ne_none_iff_exists'.1 ((htids t).1 ht)
  obtain ⟨hstab, hVc, id'', e'', hTa, hpe'', hHa, hep, hst'⟩ := hthr t ht th hth
  rw [hTt] at hTa; cases hTa
  rw [hpe] at hpe''; cases hpe''
  rw [hrun] at hst'
  obtain ⟨acts, Φt, Xt, Θt, Δt, bt, tvt, Vst, hf, hstk, _, hφ⟩ := hst'
  rw [List.filter_cons_of_pos (by simp [hsegd])] at hf
  simp only [List.cons.injEq, hsegd, Seg.mk.injEq, true_and] at hf
  obtain ⟨rfl, hf₁⟩ := hf
  obtain ⟨k, s, hDs, hs⟩ := hstk.finished
  obtain ⟨⟨_, _, hokm⟩, _, _, hcapm, _⟩ :=
    hst.tvOK (fun hE => by rw [hE t] at hth; cases hth)
  obtain ⟨V', hV', _⟩ := hcapm.1 t th hth
  obtain ⟨_, S, _, hC, _, hS, _⟩ := hokm
  obtain ⟨s₀, hSp, _⟩ := hS.live hV'
  obtain ⟨d', hd', hD'⟩ := hC.lookup hSp
  rw [hHa] at hd'; cases hd'
  rw [hDs] at hD'; cases hD'
  have hnoseg : ∀ sg ∈ tsegs₁, sg.owner ≠ some id := fun sg hsg h =>
    by rw [List.filter_eq_nil_iff] at hf₁; simpa [h] using hf₁ sg hsg
  refine ⟨Φm + ∑ t' ∈ tids, Function.update φ t 0 t', ⟨tsegs₁, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids,
    Function.update φ t 0, rfl, hst, htids, ?_, hdist, ?_, ?_, fun sg h => hnaT sg
      (List.mem_cons_of_mem _ h), hnaM, hnaH, haw, rfl⟩, ?_⟩
  · intro t' ht' th' hth'
    by_cases htt : t' = t
    · subst htt
      rw [hth] at hth'; cases hth'
      rw [Function.update_self]
      exact ⟨hstab, hVc, id, { e with status := .done }, hTt, by simp, hHa, hep, s, hDs, hs,
        hstab s hs, rfl⟩
    · have hTne : ∀ id', tv.T t' = some id' → id' ≠ id := fun id' hT' h =>
        htt (hdist t' ht' t ht (by rw [hT', hTt, h]))
      rw [Function.update_of_ne htt]
      refine (hthr t' ht' th' hth').transfer (ThreadTy.Same.refl _) rfl rfl ?_
        (fun _ _ _ _ _ => rfl) ?_
      · intro id' hT'; exact Function.update_of_ne (hTne id' hT') _ _
      · intro id' e₂ acts' Φt' Xt' Θt' Δt' bt' tvt' Vst' hT' _ _ hf' hstk' hΘe
        refine ⟨acts', Xt', Θt', Δt', bt', tvt', Vst', ?_, hstk', hΘe⟩
        rw [List.filter_cons_of_neg (by simp [hsegd]; exact fun h => hTne id' hT' h.symm)] at hf'
        exact hf'
  · intro sg hsg
    obtain ⟨t', ht', id₂, e₂, hT₂, hown₂, hpe₂, hrun₂⟩ := hown sg (List.mem_cons_of_mem _ hsg)
    have hne : id₂ ≠ id := fun h => hnoseg sg hsg (by rw [hown₂, h])
    exact ⟨t', ht', id₂, e₂, hT₂, hown₂, by dsimp only; rw [Function.update_of_ne hne]; exact hpe₂, hrun₂⟩
  · intro id₂ e₂ he₂
    by_cases hid : id₂ = id
    · subst hid; exact ⟨t, ht, hTt⟩
    · dsimp only at he₂; rw [Function.update_of_ne hid] at he₂; exact hpool id₂ e₂ he₂
  · refine add_le_add le_rfl (Finset.sum_le_sum fun t' _ => ?_)
    by_cases htt : t' = t
    · subst htt; rw [Function.update_self]; exact zero_le
    · rw [Function.update_of_ne htt]

/-- **Hardware steps change no potential**: hardware moves a pending or running thread's device
within the thread's envelope (closed under hardware steps).  `main`'s captured handle covers
the envelope (`StackOK.move`); a pending thread's spawn-time states and a running thread's
current context are closed (`StackOK.hw_self`); every other running thread survives a device it
cannot see moving, its ambient still within `b + amb` (`StackOK.foreign`); other devices are
untouched. -/
theorem CfgTyped.hw {Am : Multiset (K × St)} {c : Config K St R} {Φ : R}
    (hc : CfgTyped P M Ψ Am c Φ) {id : ThreadId} {e : PoolEntry St R} {k : K} {s s' : St}
    (hpe : c.pool id = some e) (hnd : e.status ≠ .done) (hD : c.D e.dev = .at k s)
    (hs' : s' ∈ P.hwReach k s) :
    ∃ Φ', CfgTyped P M Ψ Am ⟨c.segs, c.pool, c.D.set e.dev k s', c.K⟩ Φ' ∧ Φ' ≤ Φ := by
  obtain ⟨tsegs, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, hsegs, hst, htids, hthr, hdist, hown,
    hpool, hnaT, hnaM, hnaH, haw, rfl⟩ := hc
  obtain ⟨t, ht, hTt⟩ := hpool id e hpe
  obtain ⟨th, hth⟩ := Option.ne_none_iff_exists'.1 ((htids t).1 ht)
  have hthr₀ := hthr t ht th hth
  obtain ⟨hstab, hVc, id', e', hTa, hpe', hHa, hep, hst'⟩ := hthr₀
  rw [hTt] at hTa; cases hTa
  rw [hpe] at hpe'; cases hpe'
  obtain ⟨⟨_, _, hokm⟩, _, hwcm, hcapm, hambm⟩ :=
    hst.tvOK (fun hE => by rw [hE t] at hth; cases hth)
  obtain ⟨V', hV', hVV'⟩ := hcapm.1 t th hth
  have hkind : k = th.k := by
    obtain ⟨_, S, _, hC, _, hS, _⟩ := hokm
    obtain ⟨s₀, hSp, _⟩ := hS.live hV'
    obtain ⟨d', hd', hD'⟩ := hC.lookup hSp
    rw [hHa] at hd'; cases hd'
    rw [hD] at hD'; cases hD'; rfl
  subst hkind
  have hsV : s ∈ th.V := by
    revert hst'
    cases hes : e.status with
    | pending =>
      rintro ⟨S₀, s₁, Γc, Γb, Δb, Wb, Qa, Fa, Sout, Wp, hDs, hs₁, _, _, hb, _, _, hWb, hWpV, _⟩
      rw [hD] at hDs; cases hDs
      have := hb.le_W.1 th.p
      rw [Finsupp.single_eq_same, hWb] at this
      exact hWpV (this.2 hs₁)
    | running =>
      rintro ⟨acts, Φt, Xt, Θt, Δt, bt, tvt, Vst, _, hstk, _, _⟩
      obtain ⟨k₂, s₂, hD₂, hs₂⟩ := hstk.dev_in_env
      rw [hD] at hD₂; cases hD₂; exact hs₂
    | done => exact absurd hes hnd
  have hs'V : s' ∈ th.V := mem_of_hwClose hVc hsV hs'
  have hstm := hst.move_tv hth hHa hs'V
  obtain ⟨⟨_, _, hokm2⟩, _, hwcm2, hcapm2, hambm2⟩ :=
    hstm.tvOK (fun hE => by rw [hE t] at hth; cases hth)
  refine ⟨Φm + ∑ t ∈ tids, φ t, ⟨tsegs, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, hsegs, hstm,
    htids, ?_, hdist, hown, hpool, hnaT, hnaM, hnaH, haw, rfl⟩, le_rfl⟩
  intro t' ht' th' hth'
  by_cases htt : t' = t
  · subst htt
    rw [hth] at hth'; cases hth'
    refine ⟨hstab, hVc, id, e, hTt, hpe, hHa, hep, ?_⟩
    revert hst'
    cases hes : e.status with
    | pending =>
      rintro ⟨S₀, s₁, Γc, Γb, Δb, Wb, Qa, Fa, Sout, Wp, hDs, hs₁, hclS, hrest⟩
      rw [hD] at hDs; cases hDs
      exact ⟨S₀, s', Γc, Γb, Δb, Wb, Qa, Fa, Sout, Wp, by simp [RPeriphs.set_apply],
        mem_of_hwClose hclS hs₁ hs', hclS, hrest⟩
    | running =>
      rintro ⟨acts, Φt, Xt, Θt, Δt, bt, tvt, Vst, hf, hstk, hΘe, hφ⟩
      exact ⟨acts, Φt, Xt, Θt, Δt, bt, tvt, Vst, hf, hstk.hw_self hΘe hD hs', hΘe, hφ⟩
    | done => exact absurd hes hnd
  · obtain ⟨_, _, id₂, e₂, hT₂, hp₂, hH₂, _⟩ := hthr t' ht' th' hth'
    have hne : e₂.dev ≠ e.dev :=
      fun h => hokm.dev_ne hcapm hth' hth htt hH₂ (h ▸ hHa) rfl
    have hDD : ∀ id'' e'', tv.T t' = some id'' → c.pool id'' = some e'' →
        (c.D.set e.dev th.k s') e''.dev = c.D e''.dev := by
      intro id'' e'' hT'' hp''
      rw [hT₂] at hT''; cases hT''
      rw [hp₂] at hp''; cases hp''
      simp [RPeriphs.set_apply, hne]
    refine (hthr t' ht' th' hth').transfer (ThreadTy.Same.refl _) rfl rfl (fun _ _ => rfl)
      (fun id'' e'' hT'' hp'' _ => hDD id'' e'' hT'' hp'') ?_
    intro id'' e'' acts Φt Xt Θt Δt bt tvt Vst hT'' hp'' _ hf hstk hΘe
    refine ⟨acts, Xt, Θt, Δt, bt, tvt, Vst, hf, hstk.foreign (hDD id'' e'' hT'' hp'') ?_ hΘe, hΘe⟩
    rw [hT₂] at hT''; cases hT''
    rw [hp₂] at hp''; cases hp''
    exact hokm2.thread_amb hwcm2 hcapm2 hambm2 hth' hH₂

/-! ### 3c, case 5: a running thread's step, and draining timers -/

/-- A segment list with no waiting `await`, built from its head. -/
theorem segsNoAwait_cons' {sg : Seg St R} {ss : List (Seg St R)} (h₁ : ActsNoAwait sg.acts)
    (h₂ : SegsNoAwait ss) : SegsNoAwait (sg :: ss) := by
  intro s hs
  rcases List.mem_cons.1 hs with rfl | hs
  · exact h₁
  · exact h₂ s hs

/-- **A step of a running thread pays for itself**: the thread's stack pays it
(`StackOK.step`; frozen, so the clock is unchanged).  The store changes only at the thread's
own device, within its envelope, which `main`'s captured handle covers (`StackOK.move`); every
other running thread survives the change (`StackOK.foreign`, its ambient within `b + amb`), and
pending or finished threads hold other devices. -/
theorem CfgTyped.step_thread (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk) {Ψd : FCtx K St R}
    (hP : P.WF) (hΨc : SigsClosedA P Ψ) (hΨd : SigsDerivedA P M Ψd Ψ)
    {Am : Multiset (K × St)} {c : Config K St R} {Φ : R} (hc : CfgTyped P M Ψ Am c Φ)
    {id : ThreadId} {as : List (Act St R)} {ss : List (Seg St R)}
    (hseg : c.segs = ⟨some id, as⟩ :: ss) (htop : TopOK as)
    {q tick as' D' K'} (hstep : ActStep M Ψd Am as c.D c.K q tick as' D' K') :
    ∃ Φ', CfgTyped P M Ψ Am ⟨⟨some id, as'⟩ :: ss, c.pool, D', K'⟩ Φ' ∧ q + Φ' ≤ Φ := by
  obtain ⟨tsegs, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, hsegs, hst, htids, hthr, hdist, hown,
    hpool, hnaT, hnaM, hnaH, haw, rfl⟩ := hc
  obtain ⟨tsegs₁, rfl, hss⟩ : ∃ tsegs₁, tsegs = ⟨some id, as⟩ :: tsegs₁ ∧
      ss = tsegs₁ ++ [⟨none, a :: ma⟩] := by
    rw [hseg] at hsegs
    cases tsegs with
    | nil => simp at hsegs
    | cons s₁ t₁ =>
      simp only [List.cons_append, List.cons.injEq] at hsegs
      exact ⟨t₁, by rw [hsegs.1], hsegs.2⟩
  subst hss
  obtain ⟨t, ht, id', e, hTt, hown₁, hpe, hrun⟩ := hown _ List.mem_cons_self
  simp only [Option.some.injEq] at hown₁; subst hown₁
  obtain ⟨th, hth⟩ := Option.ne_none_iff_exists'.1 ((htids t).1 ht)
  obtain ⟨hstab, hVc, id'', e'', hTa, hpe', hHa, hep, hst'⟩ := hthr t ht th hth
  rw [hTt] at hTa; cases hTa
  rw [hpe] at hpe'; cases hpe'
  rw [hrun] at hst'
  obtain ⟨acts, Φt, Xt, Θt, Δt, bt, tvt, Vst, hf, hstk, hΘe, hφ⟩ := hst'
  rw [List.filter_cons_of_pos (by simp)] at hf
  simp only [List.cons.injEq, Seg.mk.injEq, true_and] at hf
  obtain ⟨rfl, hf₁⟩ := hf
  obtain ⟨Φt', Xt', Θt', Δt', bt', tvt', Vst', hstk', hq, _, hsame, _, hKfz⟩ :=
    hstk.step hM hΨ hP hΨc hΨd htop hstep
  obtain rfl : K' = c.K := hKfz rfl
  have hΘe' : tvt'.Θ.IsEmpty := fun t' => ((hsame t').1).1 (hΘe t')
  obtain ⟨⟨_, _, hokm⟩, _, hwcm, hcapm, hambm⟩ :=
    hst.tvOK (fun hE => by rw [hE t] at hth; cases hth)
  obtain ⟨V', hV', hVV'⟩ := hcapm.1 t th hth
  -- the store changes at most at the thread's device, within its envelope
  obtain ⟨hstm, hfr⟩ : StackOK P M Ψ Am none (a :: ma) D' c.K Φm Xm Θ Δ b bm tv Vs ∧
      ∀ d, d ≠ e.dev → D' d = c.D d := by
    obtain ⟨a₀, tl, rfl⟩ := hstk.cons
    rcases hstep.store with rfl | ⟨x, d, k, s, st, hx, hDd, rfl⟩
    · exact ⟨hst, fun _ _ => rfl⟩
    · have hd := hstk.head_dev x d hx
      subst hd
      have hkind : k = th.k := by
        obtain ⟨_, S, _, hC, _, hS, _⟩ := hokm
        obtain ⟨s₀, hSp, _⟩ := hS.live hV'
        obtain ⟨d', hd', hD'⟩ := hC.lookup hSp
        rw [hHa] at hd'; cases hd'
        rw [hDd] at hD'; cases hD'; rfl
      subst hkind
      obtain ⟨k₂, s₂, hD₂, hs₂⟩ := hstk'.dev_in_env
      simp only [RPeriphs.set_apply, ↓reduceIte] at hD₂
      cases hD₂
      exact ⟨hst.move_tv hth hHa hs₂, fun d hne => by simp [RPeriphs.set_apply, hne]⟩
  obtain ⟨⟨_, _, hokm2⟩, _, hwcm2, hcapm2, hambm2⟩ :=
    hstm.tvOK (fun hE => by rw [hE t] at hth; cases hth)
  have hnoseg : ∀ sg ∈ tsegs₁, sg.owner ≠ some id := fun sg hsg h => by
    rw [List.filter_eq_nil_iff] at hf₁; simpa [h] using hf₁ sg hsg
  refine ⟨Φm + ∑ t' ∈ tids, Function.update φ t Φt' t',
    ⟨⟨some id, as'⟩ :: tsegs₁, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, Function.update φ t Φt',
      rfl, hstm, htids, ?_, hdist, ?_, hpool, segsNoAwait_cons' (hstep.noAwait
        (hnaT _ List.mem_cons_self)) (fun sg h => hnaT sg (List.mem_cons_of_mem _ h)), hnaM,
      hnaH, haw, rfl⟩, ?_⟩
  · intro t' ht' th' hth'
    by_cases htt : t' = t
    · subst htt
      rw [hth] at hth'; cases hth'
      rw [Function.update_self]
      refine ⟨hstab, hVc, id, e, hTt, hpe, hHa, hep, ?_⟩
      rw [hrun]
      refine ⟨as', Φt', Xt', Θt', Δt', bt', tvt', Vst', ?_, hstk', hΘe', rfl⟩
      rw [List.filter_cons_of_pos (by simp), List.filter_eq_nil_iff.2 fun sg hsg => by
        simpa using hnoseg sg hsg]
    · obtain ⟨_, _, id₂, e₂, hT₂, hp₂, hH₂, _⟩ := hthr t' ht' th' hth'
      have hne : e₂.dev ≠ e.dev := fun h => hokm.dev_ne hcapm hth' hth htt hH₂ (h ▸ hHa) rfl
      have hid : id₂ ≠ id := fun h => htt (hdist t' ht' t ht (by rw [hT₂, hTt, h]))
      rw [Function.update_of_ne htt]
      refine (hthr t' ht' th' hth').transfer (ThreadTy.Same.refl _) rfl rfl (fun _ _ => rfl)
        ?_ ?_
      · intro id'' e'' hT'' hp'' _
        rw [hT₂] at hT''; cases hT''
        rw [hp₂] at hp''; cases hp''
        exact hfr _ hne
      · intro id'' e'' acts' Φt₂ Xt₂ Θt₂ Δt₂ bt₂ tvt₂ Vst₂ hT'' hp'' _ hf' hstk₂ hΘe₂
        rw [hT₂] at hT''; cases hT''
        rw [hp₂] at hp''; cases hp''
        rw [List.filter_cons_of_neg (by simp; exact fun h => hid h.symm)] at hf'
        refine ⟨acts', Xt₂, Θt₂, Δt₂, bt₂, tvt₂, Vst₂, ?_, hstk₂.foreign (hfr _ hne)
          (hokm2.thread_amb hwcm2 hcapm2 hambm2 hth' hH₂) hΘe₂, hΘe₂⟩
        rw [List.filter_cons_of_neg (by simp; exact fun h => hid h.symm)]
        exact hf'
  · intro sg hsg
    rcases List.mem_cons.1 hsg with rfl | hsg
    · exact ⟨t, ht, id, e, hTt, rfl, hpe, hrun⟩
    · exact hown sg (List.mem_cons_of_mem _ hsg)
  · have he1 := Finset.add_sum_erase tids (Function.update φ t Φt') ht
    have he2 := Finset.add_sum_erase tids φ ht
    have hsum : ∑ x ∈ tids.erase t, Function.update φ t Φt' x = ∑ x ∈ tids.erase t, φ x :=
      Finset.sum_congr rfl fun x hx => Function.update_of_ne (Finset.ne_of_mem_erase hx) _ _
    rw [← he1, ← he2, hsum, Function.update_self, hφ]
    calc q + (Φm + (Φt' + ∑ x ∈ tids.erase t, φ x))
        = Φm + ((q + Φt') + ∑ x ∈ tids.erase t, φ x) := by ring
      _ ≤ _ := add_le_add le_rfl (add_le_add hq le_rfl)

/-- Lowering a frame's budget never raises its waiting allowance. -/
theorem waitAllow_drain {rem d f : R} : waitAllow (rem - d) f ≤ waitAllow rem f := by
  unfold waitAllow
  split_ifs with h₁ h₂
  · exact le_rfl
  · exact zero_le
  · rename_i h₂; exact absurd (by rw [h₂]; exact zero_tsub d) h₁
  · exact add_le_add tsub_le_self le_rfl

/-- **Draining timers never raises the potential**: only `main`'s running activation can have a
waiting frame (at its head), and lowering its budget lowers its waiting allowance. -/
theorem CfgTyped.drain {Am : Multiset (K × St)} {c : Config K St R} {Φ : R}
    (hc : CfgTyped P M Ψ Am c Φ) (d : R) :
    ∃ Φ' x, CfgTyped P M Ψ Am (c.drain d) Φ' ∧
      (x = 0 ∨ ∃ u w, x = u * w ∧ WaitRate P M Ψ Am (c.drain d) w) ∧ x + Φ' ≤ Φ := by
  obtain ⟨segs, pool, D, Kc⟩ := c
  obtain ⟨tsegs, a, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, hsegs, hst, htids, hthr, hdist, hown,
    hpool, hnaT, hnaM, hnaH, haw, rfl⟩ := hc
  dsimp only at hsegs
  subst hsegs
  obtain ⟨σ, H, T, ctl, r⟩ := a
  cases ctl with
  | nil =>
    have hna : SegsNoAwait (tsegs ++ [⟨none, ⟨σ, H, T, [], r⟩ :: ma⟩]) := by
      intro s hs
      rcases List.mem_append.1 hs with hs | hs
      · exact hnaT s hs
      · simp only [List.mem_singleton] at hs; subst hs
        exact actsNoAwait_cons.2 ⟨fun _ h => by simp at h, hnaM⟩
    rw [Config.drain_eq_self (c := ⟨_, pool, D, Kc⟩) hna]
    exact ⟨_, 0, ⟨tsegs, _, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, rfl, hst, htids, hthr, hdist,
      hown, hpool, hnaT, hnaM, hnaH, haw, rfl⟩, Or.inl rfl, by rw [zero_add]⟩
  | cons x rest =>
    rw [Config.drain_main hnaT (by simpa using hnaH) hnaM]
    cases x with
    | cmd c₀ =>
      exact ⟨_, 0, ⟨tsegs, _, ma, Φm, Xm, Θ, Δ, b, bm, tv, Vs, tids, φ, rfl, hst, htids, hthr, hdist,
        hown, hpool, hnaT, hnaM, hnaH, haw, rfl⟩, Or.inl rfl, by rw [zero_add]⟩
    | awaitW tid id rem fb =>
      obtain rfl := hst.await_tv (Or.inr ⟨_, _, _, _, rfl⟩)
      obtain ⟨q, Φ', X', Θ', Δ', hst', hq, _, ⟨u, w, rfl, C, fz, Γ, Γf, Δf, Θf, Q, F, hctw, hokw, hw⟩,
          rfl, rfl⟩ := hst.retop (Or.inl rfl)
        (σ' := σ) (T' := T) (ctl' := .awaitW tid id (rem - d) fb :: rest)
        (fun q Θ' Δ' => (∃ u w, q = u * w ∧ ∃ C fz Γ Γf Δf Θf Q F,
          CtlTyped P M Ψ C false fz Γ Δ Θ (.awaitW tid id (rem - d) fb :: rest) Γf Δf Θf Q F ∧
          ActOK M Γ Δ b σ H D Am ∧ w = Δ.bg M + b) ∧ Θ' = Θ ∧ Δ' = Δ) (by
          intro C fz Γ Γf Δf Θf Q F hCd hct hok hws hwc hcap hcl
          cases hct with
          | @awaitW _ _ _ _ _ _ _ th Γa Δa Θa Wa Qa Fa Sa Γ₁' Δ₁' Θ₁' _ Γ₂ Δ₂ Θ₂ Q₂ F₂
              hth hp hamb hfb hCf hs hΔf hstab hΓ hΔ hΘ hws' hwc' hrest =>
            have hbgΔ : Δ.bg M = M.maxBg th.k th.V + (Δ.erase th.p).bg M := by
              have := PCtx.bg_set M Δ th.p th.k th.V
              rwa [PCtx.set_eq_self hp] at this
            have hctw := CtlTyped.awaitW (rem := rem - d) (id := id) hth hp hamb hfb hCf hs hΔf
              hstab hΓ hΔ hΘ hws' hwc' hrest
            refine ⟨_, Γ, Δ, Θ, _, _, hctw, hok, ?_, le_rfl, hws, hwc, hcap, rfl, hcl,
              ⟨waitAllow rem Kc - waitAllow (rem - d) Kc, Δ.bg M + b, by rw [hbgΔ],
                _, _, _, _, _, _, _, _, hctw, hok, rfl⟩, rfl, rfl⟩
            calc (waitAllow rem Kc - waitAllow (rem - d) Kc) *
                  (M.maxBg th.k th.V + (Δ.erase th.p).bg M + b) +
                  (waitAllow (rem - d) Kc * (M.maxBg th.k th.V + (Δ.erase th.p).bg M + b) +
                    Qa Kc b + Q₂ (max (Fa Kc) Kc) b)
                = (waitAllow rem Kc - waitAllow (rem - d) Kc + waitAllow (rem - d) Kc) *
                  (M.maxBg th.k th.V + (Δ.erase th.p).bg M + b) + Qa Kc b +
                    Q₂ (max (Fa Kc) Kc) b := by ring
              _ ≤ _ := le_of_eq (by rw [tsub_add_cancel_of_le waitAllow_drain]))
      refine ⟨Φ' + ∑ t ∈ tids, φ t, u * w, ⟨tsegs, _, ma, Φ', X', _, _, b, bm, _, Vs, tids, φ, rfl, hst',
        htids, fun t ht th hth => (hthr t ht th hth).transfer (ThreadTy.Same.refl _) rfl rfl
          (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)
          (fun _ _ acts _ _ _ _ _ _ _ _ _ _ hf hstk hΘe => ⟨acts, _, _, _, _, _, _, hf, hstk, hΘe⟩), hdist, hown, hpool,
        hnaT, hnaM, hnaH, ?_, rfl⟩, Or.inr ⟨u, w, rfl, tsegs, σ, H, T, tid, id, rem - d, fb, rest, r, ma,
          rfl, _, _, _, _, _, _, _, _, _, _, _, hctw, hokw, hw⟩, ?_⟩
      · intro tid' id' rem' fb' hh
        simp only [List.head?_cons, Option.some.injEq] at hh
        cases hh
        exact haw _ _ _ _ rfl
      · rw [← add_assoc]; exact add_le_add hq le_rfl

/-! ### 3c: every machine step pays for itself -/

/-- If `main`'s segment is on top, there is no thread segment (thread segments sit above it). -/
theorem CfgTyped.main_alone {Am : Multiset (K × St)} {c : Config K St R} {Φ : R}
    (hc : CfgTyped P M Ψ Am c Φ) {as : List (Act St R)} {ss : List (Seg St R)}
    (hseg : c.segs = ⟨none, as⟩ :: ss) : ss = [] := by
  obtain ⟨tsegs, a, ma, _, _, _, _, _, _, _, _, _, _, hsegs, _, _, _, _, hown, _⟩ := hc
  rw [hseg] at hsegs
  cases tsegs with
  | nil => simp only [List.nil_append, List.cons.injEq] at hsegs; exact hsegs.2.symm ▸ rfl
  | cons s₁ t₁ =>
    simp only [List.cons_append, List.cons.injEq] at hsegs
    obtain ⟨_, _, _, _, _, hown₁, _⟩ := hown s₁ List.mem_cons_self
    rw [← hsegs.1] at hown₁; cases hown₁

/-- **A thread segment on top is a typed thread stack** with no pending threads and no
waiting frame. -/
theorem CfgTyped.thread_seg {Am : Multiset (K × St)} {c : Config K St R} {Φ : R}
    (hc : CfgTyped P M Ψ Am c Φ) {id : ThreadId} {as : List (Act St R)}
    {ss : List (Seg St R)} (hseg : c.segs = ⟨some id, as⟩ :: ss) :
    ∃ e Φt Xt Θt Δt bt bb tvt Vst,
      StackOK P M Ψ Am (some e) as c.D c.K Φt Xt Θt Δt bt bb tvt Vst ∧
      Θt.IsEmpty ∧ ActsNoAwait as := by
  obtain ⟨tsegs, a, ma, _, _, Θ, _, _, _, tv, _, tids, _, hsegs, _, htids, hthr, _, hown, _,
    hnaT, _⟩ := hc
  rw [hseg] at hsegs
  cases tsegs with
  | nil => simp at hsegs
  | cons s₁ t₁ =>
    simp only [List.cons_append, List.cons.injEq] at hsegs
    obtain ⟨rfl, _⟩ := hsegs
    obtain ⟨t, ht, id', e, hTt, hown₁, hpe, hrun⟩ := hown _ List.mem_cons_self
    simp only [Option.some.injEq] at hown₁; subst hown₁
    obtain ⟨th, hth⟩ := Option.ne_none_iff_exists'.1 ((htids t).1 ht)
    obtain ⟨_, _, id'', e'', hTa, hpe', _, _, hst'⟩ := hthr t ht th hth
    rw [hTt] at hTa; cases hTa
    rw [hpe] at hpe'; cases hpe'
    rw [hrun] at hst'
    obtain ⟨acts, Φt, Xt, Θt, Δt, bt, tvt, Vst, hf, hstk, hΘe, _⟩ := hst'
    rw [List.filter_cons_of_pos (by simp)] at hf
    simp only [List.cons.injEq, Seg.mk.injEq, true_and] at hf
    obtain ⟨rfl, _⟩ := hf
    exact ⟨_, _, _, _, _, _, _, _, _, hstk, hstk.top_empty hΘe, hnaT _ List.mem_cons_self⟩

/-- A thread stack never runs an `async`: it is frozen, and T-Async needs an unfrozen setting
(no nested threads). -/
theorem StackOK.no_async {e : DevEnv St} {Am : Multiset (K × St)} {σ : Mem}
    {H : Var → Option Dev} {T : Var → Option ThreadId} {tid p : Var} {cb : Cmd St R}
    {ctl : List (Ctl St R)} {r : Option (Expr × Var)} {tl D Kc Φ X Θ Δ b bb tv Vs}
    (h : StackOK P M Ψ Am (some e) (⟨σ, H, T, .cmd (.async tid p cb) :: ctl, r⟩ :: tl) D Kc Φ X
      Θ Δ b bb tv Vs) : False := by
  cases h with
  | base hct _ _ _ _ _ _ _ _ hfzo =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := hct.cons_inv
    cases hc with
    | async _ _ _ _ _ _ _ _ _ hfz => rw [hfzo rfl] at hfz; cases hfz
  | push hct _ _ _ _ _ _ _ _ hfzo =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := hct.cons_inv
    cases hc with
    | async _ _ _ _ _ _ _ _ _ hfz => rw [hfzo rfl] at hfz; cases hfz

/-- A stack with no pending threads never runs an `await` (T-Await needs the awaited thread to
be pending). -/
theorem StackOK.no_await {E : Option (DevEnv St)} {Am : Multiset (K × St)} {σ : Mem}
    {H : Var → Option Dev} {T : Var → Option ThreadId} {tid : Var} {n : ℕ} {fb : Cmd St R}
    {ctl : List (Ctl St R)} {r : Option (Expr × Var)} {tl D Kc Φ X Θ Δ b bb tv Vs}
    (h : StackOK P M Ψ Am E (⟨σ, H, T, .cmd (.await tid n fb) :: ctl, r⟩ :: tl) D Kc Φ X
      Θ Δ b bb tv Vs) (hΘ : Θ.IsEmpty) : False := by
  cases h with
  | base hct =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := hct.cons_inv
    cases hc with
    | await hth => rw [hΘ] at hth; cases hth
  | push hct =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := hct.cons_inv
    cases hc with
    | await hth => rw [hΘ] at hth; cases hth

/-- A running activation whose next entry is a local command or a call. -/
theorem TopOK.cmd {σ : Mem} {H : Var → Option Dev} {T : Var → Option ThreadId} {c : Cmd St R}
    {ctl : List (Ctl St R)} {r : Option (Expr × Var)} {as : List (Act St R)}
    (h : c.Local ∨ ∃ x g e p, c = .call x g e p) : TopOK (⟨σ, H, T, .cmd c :: ctl, r⟩ :: as) := by
  intro a ha x hx
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
  subst ha
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
  subst hx
  exact ⟨c, rfl, h⟩

/-- A running activation that has run out of commands. -/
theorem TopOK.nil {σ : Mem} {H : Var → Option Dev} {T : Var → Option ThreadId}
    {r : Option (Expr × Var)} {as : List (Act St R)} : TopOK (⟨σ, H, T, [], r⟩ :: as) := by
  intro a ha x hx
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
  subst ha
  simp at hx

/-- **A step of the running activation** (local command, call or return) pays for itself,
whether it is `main`'s (case 1) or a running thread's (case 5). -/
theorem CfgTyped.step_act (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk) {Ψd : FCtx K St R}
    (hP : P.WF) (hΨc : SigsClosedA P Ψ) (hΨd : SigsDerivedA P M Ψd Ψ)
    {Am : Multiset (K × St)} {c : Config K St R} {Φ : R} (hc : CfgTyped P M Ψ Am c Φ)
    {o : Option ThreadId} {as : List (Act St R)} {ss : List (Seg St R)}
    (hseg : c.segs = ⟨o, as⟩ :: ss) (htop : TopOK as)
    {q tick as' D' K'} (hstep : ActStep M Ψd Am as c.D c.K q tick as' D' K') :
    ∃ Φ', CfgTyped P M Ψ Am ⟨⟨o, as'⟩ :: ss, c.pool, D', K'⟩ Φ' ∧ q + Φ' ≤ Φ := by
  cases o with
  | none =>
    obtain rfl := hc.main_alone hseg
    exact hc.step_main hM hΨ hP hΨc hΨd hseg htop hstep
  | some id => exact hc.step_thread hM hΨ hP hΨc hΨd hseg htop hstep

/-- The segments when a thread runs directly above `main`'s waiting frame. -/
theorem CfgTyped.timeout_shape {Am : Multiset (K × St)} {c : Config K St R} {Φ : R}
    (hc : CfgTyped P M Ψ Am c Φ) {id : ThreadId} {acts : List (Act St R)}
    {o : Option ThreadId} {σ : Mem} {H : Var → Option Dev} {T : Var → Option ThreadId}
    {tid : Var} {id' : ThreadId} {rem : R} {fb : Cmd St R} {ctl : List (Ctl St R)}
    {r : Option (Expr × Var)} {as : List (Act St R)} {ss : List (Seg St R)}
    (hseg : c.segs = ⟨some id, acts⟩ :: ⟨o, ⟨σ, H, T, .awaitW tid id' rem fb :: ctl, r⟩ :: as⟩ ::
      ss) : o = none ∧ ss = [] := by
  obtain ⟨tsegs, a, ma, _, _, _, _, _, _, _, _, _, _, hsegs, _, _, _, _, _, _, hnaT, _⟩ := hc
  rw [hseg] at hsegs
  cases tsegs with
  | nil => simp at hsegs
  | cons s₁ t₁ =>
    simp only [List.cons_append, List.cons.injEq] at hsegs
    cases t₁ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Seg.mk.injEq] at hsegs
      exact ⟨hsegs.2.1.1, hsegs.2.2⟩
    | cons s₂ t₂ =>
      simp only [List.cons_append, List.cons.injEq] at hsegs
      have h₂ := hnaT s₂ (List.mem_cons_of_mem _ List.mem_cons_self)
      rw [← hsegs.2.1] at h₂
      exact (h₂ _ List.mem_cons_self _ List.mem_cons_self).elim

/-- A `wait` item with its spec. -/
theorem ASlack.spec_wait {Am : Multiset (K × St)} {c c' : Config K St R} {x : R}
    (h : ∃ u w, x = u * w ∧ (WaitRate P M Ψ Am c w ∨ WaitRate P M Ψ Am c' w)) :
    (⟨.wait, x⟩ : ASlack R).Spec P M Ψ Am c c' := h

/-- A `fallback` item with its spec. -/
theorem ASlack.spec_fallback {Am : Multiset (K × St)} {c c' : Config K St R} {x : R}
    (h : FallbackSum P M Ψ Am c x) : (⟨.fallback, x⟩ : ASlack R).Spec P M Ψ Am c c' := h

/-- An `abandon` item with its spec. -/
theorem ASlack.spec_abandon {Am : Multiset (K × St)} {c c' : Config K St R} {x : R}
    (h : AbandonSum P M Ψ Am c x) : (⟨.abandon, x⟩ : ASlack R).Spec P M Ψ Am c c' := h

/-- **3c: every machine step pays for itself, and reports the async slack it releases.**  A
typed configuration with potential `Φ` steps (with timers drained after a ticked step) to a
typed configuration whose potential, plus the step's cost, plus the released slack items, is
at most `Φ`.  Items: the unused waiting allowance released by a waiting tick's rounding, by
draining the timer while a thread runs, and in full at `awaitDone` (`wait`); the unused
fallback at `awaitDone` (`fallback`); the abandoned thread's contribution at a timeout
(`abandon`).  Cases: steps of the running activation (`main`'s or a thread's), spawns, the
`await` frames, scheduling, completion, timeouts and hardware steps; the rest are impossible in
a typed configuration (threads never spawn or await, and only `main`'s running activation
waits). -/
theorem CfgTyped.mstepS (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk) {Ψd : FCtx K St R}
    (hP : P.WF) (hΨc : SigsClosedA P Ψ) (hΨd : SigsDerivedA P M Ψd Ψ)
    {Am : Multiset (K × St)} {c : Config K St R} {Φ : R} (hc : CfgTyped P M Ψ Am c Φ)
    {q : R} {c' : Config K St R} (h : MStep P M Ψd Am c q c') :
    ∃ (Φ' : R) (L : List (ASlack R)), CfgTyped P M Ψ Am c' Φ' ∧
      (∀ i ∈ L, i.Spec P M Ψ Am c c') ∧ q + ASlack.total L + Φ' ≤ Φ := by
  obtain ⟨tick, c₁, hstep, rfl⟩ := h
  have fin : ∀ {Φ₁ : R} {L₁ : List (ASlack R)}, CfgTyped P M Ψ Am c₁ Φ₁ →
      (∀ i ∈ L₁, ∀ c'', i.Spec P M Ψ Am c c'') → q + ASlack.total L₁ + Φ₁ ≤ Φ →
      ∃ (Φ' : R) (L : List (ASlack R)), CfgTyped P M Ψ Am (if tick then c₁.drain c.K else c₁) Φ' ∧
        (∀ i ∈ L, i.Spec P M Ψ Am c (if tick then c₁.drain c.K else c₁)) ∧
        q + ASlack.total L + Φ' ≤ Φ := by
    intro Φ₁ L₁ h₁ hL₁ hle
    split
    · obtain ⟨Φ', x, h', hx, hle'⟩ := h₁.drain c.K
      rcases hx with rfl | ⟨u, w, rfl, hw⟩
      · refine ⟨Φ', L₁, h', fun i hi => hL₁ i hi _, ?_⟩
        rw [zero_add] at hle'
        exact le_trans (add_le_add le_rfl hle') hle
      · refine ⟨Φ', L₁ ++ [⟨.wait, u * w⟩], h', ?_, ?_⟩
        · intro i hi
          rcases List.mem_append.1 hi with hi | hi
          · exact hL₁ i hi _
          · rw [List.mem_singleton] at hi; subst hi
            exact ASlack.spec_wait ⟨u, w, rfl, Or.inr hw⟩
        · calc q + ASlack.total (L₁ ++ [⟨.wait, u * w⟩]) + Φ'
              = q + ASlack.total L₁ + (u * w + Φ') := by
                simp only [ASlack.total, List.map_append, List.sum_append, List.map_cons,
                  List.map_nil, List.sum_cons, List.sum_nil, add_zero]
                ring
            _ ≤ q + ASlack.total L₁ + Φ₁ := add_le_add le_rfl hle'
            _ ≤ Φ := hle
    · exact ⟨Φ₁, L₁, h₁, fun i hi => hL₁ i hi _, hle⟩
  have nil : ∀ {Φ₁ : R}, CfgTyped P M Ψ Am c₁ Φ₁ → q + Φ₁ ≤ Φ →
      ∃ (Φ' : R) (L : List (ASlack R)), CfgTyped P M Ψ Am (if tick then c₁.drain c.K else c₁) Φ' ∧
        (∀ i ∈ L, i.Spec P M Ψ Am c (if tick then c₁.drain c.K else c₁)) ∧
        q + ASlack.total L + Φ' ≤ Φ := fun h₁ hle =>
    fin (L₁ := []) h₁ (fun _ h => by cases h) (by simpa [ASlack.total] using hle)
  have act : ∀ {o as ss pool D Kc as' D' K'},
      c = ⟨⟨o, as⟩ :: ss, pool, D, Kc⟩ → TopOK as →
      ActStep M Ψd Am as D Kc q tick as' D' K' → c₁ = ⟨⟨o, as'⟩ :: ss, pool, D', K'⟩ →
      ∃ (Φ' : R) (L : List (ASlack R)), CfgTyped P M Ψ Am (if tick then c₁.drain c.K else c₁) Φ' ∧
        (∀ i ∈ L, i.Spec P M Ψ Am c (if tick then c₁.drain c.K else c₁)) ∧
        q + ASlack.total L + Φ' ≤ Φ := by
    intro o as ss pool D Kc as' D' K' hcc htop hs hc₁
    subst hcc hc₁
    obtain ⟨Φ₁, h₁, hle⟩ := hc.step_act hM hΨ hP hΨc hΨd rfl htop hs
    exact nil h₁ hle
  cases hstep with
  | skip => exact act rfl (TopOK.cmd (Or.inl trivial)) .skip rfl
  | seq => exact act rfl (TopOK.cmd (Or.inl trivial)) .seq rfl
  | assign hev => exact act rfl (TopOK.cmd (Or.inl trivial)) (.assign hev) rfl
  | iteTrue hev => exact act rfl (TopOK.cmd (Or.inl trivial)) (.iteTrue hev) rfl
  | iteFalse hev => exact act rfl (TopOK.cmd (Or.inl trivial)) (.iteFalse hev) rfl
  | transition hH hD => exact act rfl (TopOK.cmd (Or.inl trivial)) (.transition hH hD) rfl
  | downgrade hH hD => exact act rfl (TopOK.cmd (Or.inl trivial)) (.downgrade hH hD) rfl
  | clock => exact act rfl (TopOK.cmd (Or.inl trivial)) .clock rfl
  | matchSt hH hD hf => exact act rfl (TopOK.cmd (Or.inl trivial)) (.matchSt hH hD hf) rfl
  | call hg hev hH hD =>
    exact act rfl (TopOK.cmd (Or.inr ⟨_, _, _, _, rfl⟩)) (.call hg hev hH hD) rfl
  | ret hev => exact act rfl TopOK.nil (.ret hev) rfl
  | @async o σ H T tid p cb ctl r as ss pool D Kc d k s id hH hD hfresh =>
    cases o with
    | none =>
      obtain rfl := hc.main_alone rfl
      obtain ⟨Φ₁, h₁, hle⟩ := hc.async hP rfl hH hD hfresh
      exact nil h₁ hle
    | some id' =>
      obtain ⟨_, _, _, _, _, _, _, _, _, hstk, _, _⟩ := hc.thread_seg rfl
      exact hstk.no_async.elim
  | @awaitStart o σ H T tid n fb ctl r as ss pool D Kc id hT =>
    cases o with
    | none =>
      obtain rfl := hc.main_alone rfl
      obtain ⟨Φ₁, h₁, hle⟩ := hc.awaitStart rfl hT
      exact nil h₁ (by rw [zero_add]; exact hle)
    | some id' =>
      obtain ⟨_, _, _, _, _, _, _, _, _, hstk, hΘe, _⟩ := hc.thread_seg rfl
      exact (hstk.no_await hΘe).elim
  | @awaitDone o σ H T tid id rem fb ctl r as ss pool D Kc e hpe hdone =>
    cases o with
    | none =>
      obtain rfl := hc.main_alone rfl
      obtain ⟨Φ₁, x₁, x₂, h₁, ⟨u, w, rfl, hw⟩, hfs, hle⟩ := hc.awaitDone hM hΨ rfl hpe hdone
      refine fin (L₁ := [⟨.wait, u * w⟩, ⟨.fallback, x₂⟩]) h₁ ?_ ?_
      · intro i hi c''
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ASlack.spec_wait ⟨u, w, rfl, Or.inl hw⟩
        · exact ASlack.spec_fallback hfs
      · simpa [ASlack.total, add_assoc] using hle
    | some id' =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hna⟩ := hc.thread_seg rfl
      exact (hna _ List.mem_cons_self _ List.mem_cons_self).elim
  | @awaitWait o σ H T tid id rem fb ctl r as ss pool D Kc e hpe hpend hpos =>
    cases o with
    | none =>
      obtain rfl := hc.main_alone rfl
      obtain ⟨Φ₁, x, h₁, ⟨u, w, rfl, hw⟩, hle⟩ := hc.awaitWait rfl hpos
      refine ⟨Φ₁, [⟨.wait, u * w⟩], h₁, ?_, by simpa [ASlack.total] using hle⟩
      intro i hi
      rw [List.mem_singleton] at hi; subst hi
      exact ASlack.spec_wait ⟨u, w, rfl, Or.inl hw⟩
    | some id' =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hna⟩ := hc.thread_seg rfl
      exact (hna _ List.mem_cons_self _ List.mem_cons_self).elim
  | @awaitTimeout o σ H T tid id rem fb ctl r as ss pool D Kc e hpe hpend hle0 =>
    cases o with
    | none =>
      obtain rfl := hc.main_alone rfl
      obtain ⟨Φ₁, x, h₁, hab, hle⟩ :=
        hc.timeout (tsegs₀ := []) hM hΨ rfl (fun _ h => by simp at h)
      refine fin (L₁ := [⟨.abandon, x⟩]) h₁ ?_ (by simpa [ASlack.total] using hle)
      intro i hi _
      rw [List.mem_singleton] at hi; subst hi
      exact ASlack.spec_abandon hab
    | some id' =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hna⟩ := hc.thread_seg rfl
      exact (hna _ List.mem_cons_self _ List.mem_cons_self).elim
  | @timeoutRunning id acts o σ H T tid rem fb ctl r as ss pool D Kc hle0 =>
    obtain ⟨rfl, rfl⟩ := hc.timeout_shape rfl
    obtain ⟨Φ₁, x, h₁, hab, hle⟩ := hc.timeout (tsegs₀ := [⟨some id, acts⟩]) hM hΨ rfl
      (fun sg h => by simp only [List.mem_singleton] at h; subst h; rfl)
    refine fin (L₁ := [⟨.abandon, x⟩]) h₁ ?_ (by simpa [ASlack.total] using hle)
    intro i hi _
    rw [List.mem_singleton] at hi; subst hi
    exact ASlack.spec_abandon hab
  | preempt hpe hpend =>
    obtain ⟨Φ₁, h₁, hle⟩ := hc.preempt hpe hpend
    exact nil h₁ (by rw [zero_add]; exact hle)
  | threadDone hpe =>
    obtain ⟨Φ₁, h₁, hle⟩ := hc.threadDone rfl hpe
    exact nil h₁ (by rw [zero_add]; exact hle)
  | hw hpe hnd hD hs' =>
    obtain ⟨Φ₁, h₁, hle⟩ := hc.hw hpe hnd hD hs'
    exact nil h₁ (by rw [zero_add]; exact hle)

/-- **3c: every machine step pays for itself** (`CfgTyped.mstepS` without the slack items). -/
theorem CfgTyped.mstep (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk) {Ψd : FCtx K St R}
    (hP : P.WF) (hΨc : SigsClosedA P Ψ) (hΨd : SigsDerivedA P M Ψd Ψ)
    {Am : Multiset (K × St)} {c : Config K St R} {Φ : R} (hc : CfgTyped P M Ψ Am c Φ)
    {q : R} {c' : Config K St R} (h : MStep P M Ψd Am c q c') :
    ∃ Φ', CfgTyped P M Ψ Am c' Φ' ∧ q + Φ' ≤ Φ := by
  obtain ⟨Φ', L, h', _, hle⟩ := hc.mstepS hM hΨ hP hΨc hΨd h
  exact ⟨Φ', h', le_trans (add_le_add le_self_add le_rfl) hle⟩

/-- **Runs of a typed configuration cost at most its potential** (3c iterated): along any run,
the accumulated cost plus the final potential is at most the initial potential. -/
theorem CfgTyped.steps (hM : M.WF)
    (hΨ : ∀ g sig, Ψ g = some sig → SummaryMono sig.cost sig.clk) {Ψd : FCtx K St R}
    (hP : P.WF) (hΨc : SigsClosedA P Ψ) (hΨd : SigsDerivedA P M Ψd Ψ)
    {Am : Multiset (K × St)} {c : Config K St R} {q : R} {c' : Config K St R}
    (h : Steps P M Ψd Am c q c') :
    ∀ {Φ : R}, CfgTyped P M Ψ Am c Φ → ∃ Φ', CfgTyped P M Ψ Am c' Φ' ∧ q + Φ' ≤ Φ := by
  induction h with
  | refl => intro Φ hc; exact ⟨Φ, hc, by rw [zero_add]⟩
  | step hs _ ih =>
    intro Φ hc
    obtain ⟨Φ₁, h₁, hle₁⟩ := hc.mstep hM hΨ hP hΨc hΨd hs
    obtain ⟨Φ', h', hle'⟩ := ih h₁
    exact ⟨Φ', h', by
      calc _ = _ + (_ + Φ') := add_assoc _ _ _
        _ ≤ _ + Φ₁ := add_le_add le_rfl hle'
        _ ≤ Φ := hle₁⟩
