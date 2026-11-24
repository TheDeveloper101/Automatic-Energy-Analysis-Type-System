import Heliod.AsyncProgram
import Mathlib.Tactic.Ring

/-!
# Worked example: sending on the radio while measuring (async / await)

A sanity check that the async rules of `Heliod.AsyncTyping` are not vacuous and derive the
cost the rules' docs predict.

```
platform: sensor  Off ≤ Idle ≤ Measure   (all stable, no hardware steps)
          radio   Off ≤ Tx ≤ Done        Tx, Done transient; hardware Tx → Done;
                                          downgrades Tx ↪ Off, Done ↪ Off

main (handles: radio : radio @ Off, temp : sensor @ Off) {
  transition(radio, Tx);                       -- transient: radio ∈ hwClose{Tx} = {Tx, Done}
  let h = async(radio) { downgrade(radio, Off) }
  transition(temp, Measure);                   -- main keeps working meanwhile
  downgrade(temp, Off);
  await h timeout[3] {
    match radio { Tx → downgrade(radio, Off) | Done → downgrade(radio, Off) | Off → skip }
  }
}
```

Exercised: T-Transition-Unstable (the radio's states become `hwClose {Tx}`); T-AsyncFun (spawn
states transient and HW-closed, the frozen body ends stable, the main thread sees the envelope
`V = {Tx, Done, Off}`); the window ambient (`temp` passes through `{Off, Measure}` while the
thread is pending, so the declared bound is `amb = maxBg sensor {Off, Measure}`); T-Await (the
fallback is typed from `V` and its `match` narrows each arm to `hwClose {st}`, so the `Tx` arm
sees `{Tx, Done}`); and `Program.TypedA`'s requirement that no thread is pending at the end.

The fallback must be a `match`: it is typed from `V`, which contains the body's exit state
`Off`, and `Off ↪ Off` is not a downgrade.  On timeout the body may already have powered the
radio off, so this case must be handled.  (The paper types the fallback from the spawn states,
all transient, where a plain `downgrade` passes.)

The cost model `M` is arbitrary; costs are in `ℕ`.
-/

namespace AsyncExample

/-- Peripheral kinds. -/
inductive Kind where
  | sensor | radio
  deriving DecidableEq

/-- States of both kinds. -/
inductive TS where
  | off | idle | measure | tx | done
  deriving DecidableEq

/-- Height in each kind's chain. -/
def rank : TS → ℕ
  | .off => 0
  | .idle => 1
  | .measure => 2
  | .tx => 1
  | .done => 2

/-- Each kind's states. -/
def states : Kind → Finset TS
  | .sensor => {.off, .idle, .measure}
  | .radio => {.off, .tx, .done}

/-- The radio-and-sensor platform: the radio's `Tx` and `Done` are transient, and hardware may
finish a transmission (`Tx → Done`). -/
def P : Platform Kind TS where
  states := states
  le k s s' := s ∈ states k ∧ s' ∈ states k ∧ rank s ≤ rank s'
  top
    | .sensor => .measure
    | .radio => .done
  dg k s' s := s = .off ∧ s' ≠ .off ∧ s' ∈ states k
  stable k s := ¬ (k = .radio ∧ (s = .tx ∨ s = .done))
  hwReach k s := if k = .radio ∧ s = .tx then {.done} else ∅

/-- The platform is well formed. -/
theorem P_wf : P.WF where
  le_refl k s h := ⟨h, h, le_rfl⟩
  le_trans _ _ _ _ h₁ h₂ := ⟨h₁.1, h₂.2.1, h₁.2.2.trans h₂.2.2⟩
  le_antisymm k s₁ s₂ h₁ h₂ := by
    obtain ⟨hm₁, hm₂, hr₁⟩ := h₁
    obtain ⟨_, _, hr₂⟩ := h₂
    cases k <;> cases s₁ <;> cases s₂ <;> simp_all [states, rank]
  le_mem _ _ _ h := ⟨h.1, h.2.1⟩
  top_mem k := by cases k <;> simp [P, states]
  le_top k s h := by
    refine ⟨h, ?_, ?_⟩ <;> cases k <;> cases s <;> simp_all [P, states, rank]
  dg_lt k s' s h := by
    obtain ⟨rfl, hne, hm⟩ := h
    refine ⟨⟨?_, hm, ?_⟩, fun h => hne h.symm⟩ <;> cases k <;> cases s' <;>
      simp_all [states, rank]
  hwReach_sub k s := by
    cases k <;> cases s <;> simp [P, states]
  hwReach_stable k s h := by
    cases k <;> cases s <;> simp_all [P]
  hwReach_closed k s s' h := by
    cases k <;> cases s <;> simp_all [P]

/-- The radio after a transient transition to `Tx`: hardware may already have finished. -/
theorem hwClose_tx : P.hwClose .radio {.tx} = {.tx, .done} := by decide

/-- The spawn states are already closed under hardware steps. -/
theorem hwClose_txd : P.hwClose .radio {.tx, .done} = {.tx, .done} := by decide

/-- The envelope: the spawn states plus the body's exit state. -/
theorem hwClose_V : P.hwClose .radio ({.tx, .done} ∪ {.off}) = {.off, .tx, .done} := by decide

/-- The fallback: power the radio off from wherever the body may have left it. -/
def fallback : Cmd TS ℕ :=
  .matchSt "radio" (.cons .tx (.downgrade "radio" .off)
    (.cons .done (.downgrade "radio" .off) (.cons .off .skip .nil)))

/-- The whole program. -/
def prog : Program Kind TS ℕ where
  periphs := [("radio", .radio, .off), ("temp", .sensor, .off)]
  funs := []
  main :=
    .seq (.transition "radio" .tx) <|
    .seq (.async "h" "radio" (.downgrade "radio" .off)) <|
    .seq (.transition "temp" .measure) <|
    .seq (.downgrade "temp" .off)
         (.await "h" 3 fallback)

/-- Every pending thread has captured `radio` (so `temp` stays available to `main`). -/
def RadioOnly (Θ : ThreadCtx Kind TS ℕ) : Prop := ∀ t th, Θ t = some th → th.p = "radio"

/-- No thread is pending at the start. -/
theorem RadioOnly.empty : RadioOnly ThreadCtx.empty := fun _ _ h => by cases h

/-- Recording a context in the windows keeps the captured handles. -/
theorem RadioOnly.observe {Θ : ThreadCtx Kind TS ℕ} (h : RadioOnly Θ) (Δ : PCtx Kind TS) :
    RadioOnly (Θ.observe Δ) := by
  intro t th ht
  simp only [ThreadCtx.observe, Option.map_eq_some_iff] at ht
  obtain ⟨th₀, h₀, rfl⟩ := ht
  exact h t th₀ h₀

/-- Spawning `h` on `radio`. -/
theorem RadioOnly.spawn {Θ : ThreadCtx Kind TS ℕ} (h : RadioOnly Θ) {th : ThreadTy Kind TS ℕ}
    (hp : th.p = "radio") : RadioOnly (Function.update Θ "h" (some th)) := by
  intro t th' ht
  by_cases e : t = "h"
  · subst e
    rw [Function.update_self, Option.some.injEq] at ht
    rw [← ht]; exact hp
  · rw [Function.update_of_ne e] at ht; exact h t th' ht

/-- `temp` is not captured. -/
theorem RadioOnly.not_temp {Θ : ThreadCtx Kind TS ℕ} (h : RadioOnly Θ) : ¬ Θ.Captures "temp" := by
  rintro ⟨t, th, ht, hp⟩
  rw [h t th ht] at hp
  exact absurd hp (by decide)

/-- Discharge `¬ Θ.Captures "temp"` along `main`'s thread contexts. -/
macro "not_captures_temp" : tactic =>
  `(tactic| (apply RadioOnly.not_temp; repeat (first | exact RadioOnly.empty | apply RadioOnly.observe | refine RadioOnly.spawn ?_ rfl)))

/-- No thread is pending. -/
def Quiet (Θ : ThreadCtx Kind TS ℕ) : Prop := ∀ t, Θ t = none

/-- At most thread `h` is pending. -/
def OnlyH (Θ : ThreadCtx Kind TS ℕ) : Prop := ∀ t, t ≠ "h" → Θ t = none

/-- Nothing is pending at the start. -/
theorem OnlyH.empty : OnlyH ThreadCtx.empty := fun _ _ => rfl

/-- Windows do not change which threads are pending. -/
theorem OnlyH.observe {Θ : ThreadCtx Kind TS ℕ} (h : OnlyH Θ) (Δ : PCtx Kind TS) :
    OnlyH (Θ.observe Δ) := fun t ht => by simp [ThreadCtx.observe, h t ht]

/-- Spawning `h`. -/
theorem OnlyH.spawn {Θ : ThreadCtx Kind TS ℕ} (h : OnlyH Θ) (th : ThreadTy Kind TS ℕ) :
    OnlyH (Function.update Θ "h" (some th)) := fun t ht => by
  rw [Function.update_of_ne ht]; exact h t ht

/-- Awaiting `h` leaves nothing pending. -/
theorem OnlyH.erase {Θ : ThreadCtx Kind TS ℕ} (h : OnlyH Θ) : Quiet (Θ.erase "h") := fun t => by
  by_cases ht : t = "h"
  · subst ht; simp [ThreadCtx.erase]
  · simp only [ThreadCtx.erase, Function.update_of_ne ht]; exact h t ht

/-- Windows of nothing are nothing. -/
theorem Quiet.observe {Θ : ThreadCtx Kind TS ℕ} (h : Quiet Θ) (Δ : PCtx Kind TS) :
    Quiet (Θ.observe Δ) := fun t => by simp [ThreadCtx.observe, h t]

/-- A join with nothing pending on the left has nothing pending. -/
theorem Quiet.join {Θ₁ : ThreadCtx Kind TS ℕ} (h : Quiet Θ₁) (Θ₂ : ThreadCtx Kind TS ℕ) :
    Quiet (Θ₁.join Θ₂) := fun t => by
  simp only [ThreadCtx.join, h t]

/-- Nothing pending captures nothing. -/
theorem Quiet.not_captures {Θ : ThreadCtx Kind TS ℕ} (h : Quiet Θ) (p : Var) :
    ¬ Θ.Captures p := by
  rintro ⟨t, th, ht, _⟩; rw [h t] at ht; cases ht

/-- Two branches with nothing pending agree on it. -/
theorem Quiet.same {Θ₁ Θ₂ : ThreadCtx Kind TS ℕ} (h₁ : Quiet Θ₁) (h₂ : Quiet Θ₂) :
    Θ₁.SameThreads Θ₂ := fun t => Or.inl ⟨h₁ t, h₂ t⟩

/-- Discharge `Quiet Θ` for the thread contexts after the `await`. -/
macro "quiet" : tactic => `(tactic| repeat (first | apply Quiet.observe | apply Quiet.join | apply OnlyH.erase | exact OnlyH.empty | apply OnlyH.observe | apply OnlyH.spawn))

/-- `hwClose` of the other singletons: no hardware steps. -/
theorem hwClose_done : P.hwClose .radio {.done} = {.done} := by decide

/-- See `hwClose_done`. -/
theorem hwClose_off : P.hwClose .radio {.off} = {.off} := by decide

/-- `hwClose` of the envelope as the derivation builds it. -/
theorem hwClose_V' : P.hwClose .radio (P.hwClose .radio {.tx} ∪ {.off}) = {.off, .tx, .done} := by
  decide

/-- `hwClose` of the envelope, with the union normalized. -/
theorem hwClose_V'' : P.hwClose .radio {.tx, .done, .off} = {.off, .tx, .done} := by decide

section Cost
variable (M : CostModel Kind TS ℕ)

/-- A single known state: its own background cost. -/
theorem maxBg_single (k : Kind) (s : TS) : M.maxBg k {s} = M.bgCost k s := Finset.sup_singleton

/-- A single known source state: its own transition cost. -/
theorem maxTrans_single (k : Kind) (s st : TS) : M.maxTrans k {s} st = M.transCost k s st :=
  Finset.sup_singleton

/-- Background cost of a state. -/
abbrev bg (k : Kind) (s : TS) : ℕ := M.bgCost k s
/-- Transition cost. -/
abbrev tr (k : Kind) (s s' : TS) : ℕ := M.transCost k s s'

/-- The fallback's cost: the worst of its three arms, each including the `match` step with the
radio narrowed to the arm's `hwClose {st}` (`temp` is `Off`). -/
def fallbackCost (f b : ℕ) : ℕ :=
  max (f * (M.maxTrans .radio {.tx, .done} .off + bg M .sensor .off + b)
        + f * (M.maxBg .radio {.tx, .done} + bg M .sensor .off + b))
    (max (f * (tr M .radio .done .off + bg M .sensor .off + b)
          + f * (bg M .radio .done + bg M .sensor .off + b))
      (f * (bg M .radio .off + bg M .sensor .off + b)))

/-- `main`'s cost at clock `f` with ambient `b`, step by step.  `V = {Off, Tx, Done}` is the
envelope of the captured radio; `amb = maxBg sensor {Off, Measure}` the declared window bound. -/
def mainCost (f b : ℕ) : ℕ :=
  -- transition(radio, Tx), temp Off
  f * (tr M .radio .off .tx + bg M .sensor .off + b)
  -- spawn, temp Off; the body (downgrade from {Tx, Done}) paid at the spawn at ambient b + amb
  + (f * (M.maxSpawn .radio {.tx, .done} + bg M .sensor .off + b)
     + f * (M.maxTrans .radio {.tx, .done} .off + (b + M.maxBg .sensor {.off, .measure})))
  -- transition(temp, Measure), radio at its worst captured state
  + f * (tr M .sensor .off .measure + M.maxBg .radio {.off, .tx, .done} + b)
  -- downgrade(temp, Off)
  + f * (tr M .sensor .measure .off + M.maxBg .radio {.off, .tx, .done} + b)
  -- await: up to `3 + f` waiting ticks, then the fallback
  + ((3 + f) * (M.maxBg .radio {.off, .tx, .done} + bg M .sensor .off + b) + fallbackCost M f b)

/-- **`main` type-checks under `TypedA` with summary `mainCost`.**  No thread is pending at the
end (the await removed `h`), the clock is unchanged, and the radio ends `Off`. -/
theorem main_typed :
    ∃ Γ' Δ' Θ' W Q F, TypedA P M (fun _ => none) false TCtx.empty prog.initPCtx
      ThreadCtx.empty prog.main Γ' Δ' Θ' W Q F ∧ Θ' = ThreadCtx.empty ∧ (∀ f, F f = f) ∧
      Δ' "radio" = .live .radio {.off} ∧ (∀ f b, Q f b = mainCost M f b) := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro
  refine ⟨?deriv, ?thr, ?clk, ?fin, ?cost⟩
  case deriv =>
    dsimp only [prog]
    apply TypedA.seq
    · -- transition(radio, Tx): transient target
      apply TypedA.transitionU (k := .radio) (S := {.off})
      · simp [Program.initPCtx]
      · rintro ⟨t, th, h, _⟩; cases h
      · simp [Platform.unstable, P]
      · simp [P, states, rank]
    apply TypedA.seq
    · -- let h = async(radio) { downgrade(radio, Off) }
      apply TypedA.async (k := .radio) (S := P.hwClose .radio {.tx}) (amb := M.maxBg .sensor {.off, .measure})
      · simp
      · rintro ⟨t, th, h, _⟩; simp [ThreadCtx.observe, ThreadCtx.empty] at h
      · simp [ThreadCtx.observe, ThreadCtx.empty]
      · rw [hwClose_tx]; simp [Platform.unstable, P]
      · rw [hwClose_tx, hwClose_txd]
      · apply TypedA.downgrade (k := .radio) (S := P.hwClose .radio {.tx})
        · simp
        · rintro ⟨t, th, h, _⟩; cases h
        · simp [P]
        · rw [hwClose_tx]; simp [P, states]
      · simp; rfl
      · simp [P]
      · simp; rfl
      · rfl
    apply TypedA.seq
    · -- transition(temp, Measure), radio captured
      apply TypedA.transition (k := .sensor) (S := {.off})
      · simp [Program.initPCtx]
      · not_captures_temp
      · simp [P]
      · simp [P, states, rank]
    apply TypedA.seq
    · -- downgrade(temp, Off)
      apply TypedA.downgrade (k := .sensor) (S := {.measure})
      · simp
      · not_captures_temp
      · simp [P]
      · simp [P, states]
    · -- await h timeout[3] { fallback }
      apply TypedA.await
      · rfl
      · simp
      · -- the window ambient: temp passed through {Off, Measure}
        dsimp only
        refine le_of_eq ?_
        convert PCtx.bg_single M "temp" (PEntry.live Kind.sensor {TS.off, TS.measure}) using 2
        case e'_3 => rfl
        ext x
        by_cases hx : x = "temp"
        · subst hx; simp [Program.initPCtx, PEntry.join]; decide
        · by_cases hr : x = "radio"
          · subst hr; simp
          · simp [Program.initPCtx, hx, PEntry.join]; rfl
      · -- the fallback, typed from the envelope V
        apply TypedA.matchSt (k := .radio) (S := {.off, .tx, .done})
        · simp [hwClose_tx]; decide
        · apply Quiet.not_captures; quiet
        · simp [Arms.states]; decide
        · apply ArmsTypedA.cons
          · simp
          · -- Tx arm: radio ∈ hwClose {Tx} = {Tx, Done}
            apply TypedA.downgrade (k := .radio) (S := P.hwClose .radio {.tx})
            · simp
            · apply Quiet.not_captures; quiet
            · simp [P]
            · rw [hwClose_tx]; simp [P, states]
          · apply ArmsTypedA.cons
            · simp
            · -- Done arm
              apply TypedA.downgrade (k := .radio) (S := P.hwClose .radio {.done})
              · simp
              · apply Quiet.not_captures; quiet
              · simp [P]
              · rw [hwClose_done]; simp [P, states]
            · -- Off arm
              apply ArmsTypedA.last
              · simp
              · exact TypedA.skip
              · simp [Arms.states]
            · apply Quiet.same <;> quiet
          · apply Quiet.same <;> quiet
      · apply Quiet.same <;> quiet
      · simp; rfl
      · intro s hs
        dsimp only
        rw [hwClose_off] at hs
        simp only [Finset.mem_union, Finset.mem_singleton, or_self] at hs
        subst hs; simp [P]
  case thr =>
    funext t; revert t; show Quiet _; quiet
  case clk => intro f; simp
  case fin => simp [PEntry.join, hwClose_off]
  case cost =>
    intro f b
    simp only [hwClose_tx, hwClose_done, hwClose_off]
    simp [mainCost, fallbackCost, Program.initPCtx, hwClose_V'', maxBg_single, maxTrans_single,
      bg, tr]
    ring_nf

/-- **The program type-checks** (`Program.TypedA`, no functions), with `main`'s summary
`mainCost`. -/
theorem prog_typed :
    ∃ Γ' Δ' W Q F, Program.TypedA P M prog (fun _ => none) Γ' Δ' W Q F ∧
      (∀ f b, Q f b = mainCost M f b) ∧ (∀ f, F f = f) ∧ Δ' "radio" = .live .radio {.off} := by
  obtain ⟨Γ', Δ', Θ', W, Q, F, hd, rfl, hF, hΔ, hQ⟩ := main_typed M
  exact ⟨Γ', Δ', W, Q, F, ⟨by simp [prog], .nil, hd⟩, hQ, hF, hΔ⟩

/-- **End to end: every run of the program on the machine costs at most `mainCost K₀ 0`**, for
every schedule (when `h` runs, whether it finishes or times out) and every hardware behaviour
(when the transmission finishes), by `Program.MRun.soundnessA`. -/
theorem cost_bound (hM : M.WF) {K₀ q : ℕ} {c : Config Kind TS ℕ}
    (h : prog.MRun P M K₀ c q) : q ≤ mainCost M K₀ 0 := by
  obtain ⟨Γ', Δ', W, Q, F, ht, hQ, _, _⟩ := prog_typed M
  rw [← hQ]
  exact Program.MRun.soundnessA hM P_wf ht h

end Cost

end AsyncExample
