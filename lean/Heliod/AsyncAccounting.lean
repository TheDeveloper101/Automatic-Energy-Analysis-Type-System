import Heliod.Machine
import Heliod.Accounting

/-!
# Accounting (A) on the machine: every device is charged exactly once per tick

The async analogue of `Heliod.Accounting`.  On the machine the device store `D` is global: it
holds every device — those of `main`, of suspended callers, of running callees, and the devices
captured by pending or running threads.  So the population of `Heliod.Accounting` at a step is
simply `pop D A = entries(D) + A`, whichever thread runs.

## Results

* `Step.accounting` — every machine step is one of:
  * **untimed** (sequencing, skip, scheduling, thread completion, `awaitStart`, `awaitDone`,
    both timeouts, hardware steps): no tick, cost `0`, clock unchanged, and the store is
    unchanged except that a hardware step moves the device of a pending or running thread
    within `HWReach`;
  * **a charge event** at the clock in force, whose population is *exactly* the current store
    plus the ambient, split into at most one mover (a transition or downgrade paying its
    transition cost, or a spawn paying its spawn cost) and the passive rest (each paying its
    background cost); afterwards the population is the store after the step.
* `Step.kind_eq` / `Steps.kind_eq` — no step creates, drops or re-kinds a device.
* `MStep.accounting` — the same for machine steps, with the time accounting: after a charge
  event every waiting timer is lowered by exactly the event's clock (`Config.drain`).
* `Steps.accounting` — **whole runs**: the cost of any run is the sum of its charge events, and
  every event charges a population with the same multiset of kinds as the start.

Compared with `Eval.whole_run_accounting`, no instrumented semantics is needed: the machine's
steps are already the events.
-/

set_option linter.unusedSectionVars false

variable {K St R : Type}

/-- How the active member of a machine event moves: a transition or downgrade to `st`, or a
spawn (which captures the device in place and pays its spawn cost). -/
inductive Move (St : Type) where
  | trans (st : St)
  | spawn

/-- One charge event of a machine run: the clock in force, the CPU cost, the active member
`(kind, state, move)` if any, and the passive rest of the population. -/
structure MEvent (K St R : Type) where
  clk : R
  cpu : R
  active : Option (K × St × Move St)
  passive : Multiset (K × St)

namespace MEvent

/-- The population an event charges: the active member in its source state plus the passive
ones. -/
def pop (e : MEvent K St R) : Multiset (K × St) :=
  match e.active with
  | none => e.passive
  | some (k, s, _) => (k, s) ::ₘ e.passive

/-- The population after the event: the active member in its target state (a spawned device
stays where it is) plus the passive ones. -/
def post (e : MEvent K St R) : Multiset (K × St) :=
  match e.active with
  | none => e.passive
  | some (k, _, .trans st) => (k, st) ::ₘ e.passive
  | some (k, s, .spawn) => (k, s) ::ₘ e.passive

variable [CommSemiring R]

/-- The active member's cost: its transition or spawn cost, or nothing. -/
def activeCost (M : CostModel K St R) : Option (K × St × Move St) → R
  | none => 0
  | some (k, s, .trans st) => M.transCost k s st
  | some (k, s, .spawn) => M.spawnCost k s

/-- What an event charges: CPU cost, plus `clk ·` (active member's cost + every passive
member's background cost).  Since `active` and `passive` partition the population, each member
is charged exactly once. -/
def charge (M : CostModel K St R) (e : MEvent K St R) : R :=
  e.cpu + e.clk * (activeCost M e.active + ambBg M e.passive)

/-- Total charge of a list of events. -/
def total (M : CostModel K St R) (L : List (MEvent K St R)) : R :=
  (L.map (charge M)).sum

/-- The total of a concatenation; used to sum events along a run. -/
theorem total_append (M : CostModel K St R) (L₁ L₂ : List (MEvent K St R)) :
    total M (L₁ ++ L₂) = total M L₁ + total M L₂ := by
  simp only [total, List.map_append, List.sum_append]

end MEvent

open RPeriphs

variable [CommSemiring R]

/-! ### Charge shapes of the machine's ticked steps -/

section Shapes
variable {M : CostModel K St R} {D : RPeriphs K St} {A : Multiset (K × St)} {Kc : R}

/-- An expression step (assign, if, call argument, return): CPU `Kc · q_e`, no mover. -/
private theorem ev_expr (y : R) : ∃ ev : MEvent K St R,
    Kc * (y + D.bg M + ambBg M A) = ev.charge M ∧ ev.clk = Kc ∧ ev.pop = pop D A ∧
      ev.post = pop D A :=
  ⟨⟨Kc, Kc * y, none, pop D A⟩, by
    simp only [MEvent.charge, MEvent.activeCost, ambBg_pop]; ring, rfl, rfl, rfl⟩

/-- A background-only step (match, a waiting tick): no CPU cost, no mover. -/
private theorem ev_bg : ∃ ev : MEvent K St R,
    Kc * (D.bg M + ambBg M A) = ev.charge M ∧ ev.clk = Kc ∧ ev.pop = pop D A ∧
      ev.post = pop D A :=
  ⟨⟨Kc, 0, none, pop D A⟩, by
    simp only [MEvent.charge, MEvent.activeCost, ambBg_pop]; ring, rfl, rfl, rfl⟩

/-- A clock change: CPU `clockCost`, no mover. -/
private theorem ev_clock (f' : R) : ∃ ev : MEvent K St R,
    M.clockCost Kc f' + Kc * (D.bg M + ambBg M A) = ev.charge M ∧ ev.clk = Kc ∧
      ev.pop = pop D A ∧ ev.post = pop D A :=
  ⟨⟨Kc, M.clockCost Kc f', none, pop D A⟩, by
    simp only [MEvent.charge, MEvent.activeCost, ambBg_pop]; ring, rfl, rfl, rfl⟩

/-- A transition or downgrade of device `d` to `st`: the mover pays its transition cost. -/
private theorem ev_move {d : Var} {k : K} {s : St} (h : D d = .at k s) (st : St) :
    ∃ ev : MEvent K St R,
      Kc * (M.transCost k s st + (D.erase d).bg M + ambBg M A) = ev.charge M ∧ ev.clk = Kc ∧
        ev.pop = pop D A ∧ ev.post = pop (D.set d k st) A :=
  ⟨⟨Kc, 0, some (k, s, .trans st), pop (D.erase d) A⟩, by
    simp only [MEvent.charge, MEvent.activeCost, ambBg_pop]; ring,
    rfl, (pop_split h A).symm, (pop_after_move k st A).symm⟩

/-- A spawn on device `d`: the captured device pays its spawn cost and stays in the store. -/
private theorem ev_spawn {d : Var} {k : K} {s : St} (h : D d = .at k s) :
    ∃ ev : MEvent K St R,
      Kc * (M.spawnCost k s + (D.erase d).bg M + ambBg M A) = ev.charge M ∧ ev.clk = Kc ∧
        ev.pop = pop D A ∧ ev.post = pop D A :=
  ⟨⟨Kc, 0, some (k, s, .spawn), pop (D.erase d) A⟩, by
    simp only [MEvent.charge, MEvent.activeCost, ambBg_pop]; ring,
    rfl, (pop_split h A).symm, (pop_split h A).symm⟩

end Shapes

variable [DecidableEq St] [LinearOrder R]
variable {P : Platform K St} {M : CostModel K St R} {Ψd : FCtx K St R} {A : Multiset (K × St)}

/-- **Per-step accounting on the machine.**  A step either takes no time and costs nothing
(the store unchanged, or a hardware move of a pending or running thread's device), or it is
one charge event at the clock in force whose population is exactly the current store plus the
ambient — every device, whichever thread owns or has captured it, charged once — and whose
post-population is the store after the step. -/
theorem Step.accounting {c c' : Config K St R} {q : R} {tick : Bool}
    (h : Step P M Ψd A c q tick c') :
    (tick = false ∧ q = 0 ∧ c'.K = c.K ∧
      (c'.D = c.D ∨ ∃ id e k s s', c.pool id = some e ∧ e.status ≠ .done ∧
        c.D e.dev = .at k s ∧ s' ∈ P.hwReach k s ∧ c'.D = c.D.set e.dev k s')) ∨
    (tick = true ∧ ∃ ev : MEvent K St R, q = ev.charge M ∧ ev.clk = c.K ∧
      ev.pop = pop c.D A ∧ ev.post = pop c'.D A) := by
  cases h with
  | skip => exact Or.inl ⟨rfl, rfl, rfl, Or.inl rfl⟩
  | seq => exact Or.inl ⟨rfl, rfl, rfl, Or.inl rfl⟩
  | awaitStart => exact Or.inl ⟨rfl, rfl, rfl, Or.inl rfl⟩
  | awaitDone => exact Or.inl ⟨rfl, rfl, rfl, Or.inl rfl⟩
  | awaitTimeout => exact Or.inl ⟨rfl, rfl, rfl, Or.inl rfl⟩
  | preempt => exact Or.inl ⟨rfl, rfl, rfl, Or.inl rfl⟩
  | threadDone => exact Or.inl ⟨rfl, rfl, rfl, Or.inl rfl⟩
  | timeoutRunning => exact Or.inl ⟨rfl, rfl, rfl, Or.inl rfl⟩
  | hw hpe hst hD hr => exact Or.inl ⟨rfl, rfl, rfl, Or.inr ⟨_, _, _, _, _, hpe, hst, hD, hr, rfl⟩⟩
  | assign => exact Or.inr ⟨rfl, ev_expr _⟩
  | iteTrue => exact Or.inr ⟨rfl, ev_expr _⟩
  | iteFalse => exact Or.inr ⟨rfl, ev_expr _⟩
  | call => exact Or.inr ⟨rfl, ev_expr _⟩
  | ret => exact Or.inr ⟨rfl, ev_expr _⟩
  | matchSt => exact Or.inr ⟨rfl, ev_bg⟩
  | awaitWait => exact Or.inr ⟨rfl, ev_bg⟩
  | clock => exact Or.inr ⟨rfl, ev_clock _⟩
  | transition _ hD => exact Or.inr ⟨rfl, ev_move hD _⟩
  | downgrade _ hD => exact Or.inr ⟨rfl, ev_move hD _⟩
  | async _ hD => exact Or.inr ⟨rfl, ev_spawn hD⟩

/-- **Conservation, handle-wise.**  A machine step keeps every device's kind and presence:
transitions, downgrades and hardware steps overwrite a device with its own kind; every other
step leaves the store alone. -/
theorem Step.kind_eq {c c' : Config K St R} {q : R} {tick : Bool}
    (h : Step P M Ψd A c q tick c') : ∀ x, (c'.D x).kind = (c.D x).kind := by
  cases h with
  | transition _ hD => exact kind_set hD _
  | downgrade _ hD => exact kind_set hD _
  | hw _ _ hD => exact kind_set hD _
  | _ => intro _; rfl

variable [Sub R]

/-- **Per-step accounting with time.**  A machine step is untimed and free, or one charge event
(as in `Step.accounting`) after which every waiting timer is lowered by exactly the event's
clock: the time charged is the time counted against every `await` budget. -/
theorem MStep.accounting {c c' : Config K St R} {q : R} (h : MStep P M Ψd A c q c') :
    (q = 0 ∧ Step P M Ψd A c 0 false c') ∨
    (∃ (c₁ : Config K St R) (ev : MEvent K St R), Step P M Ψd A c q true c₁ ∧ c' = c₁.drain ev.clk ∧
      q = ev.charge M ∧ ev.clk = c.K ∧ ev.pop = pop c.D A ∧ ev.post = pop c'.D A) := by
  obtain ⟨tick, c₁, hs, rfl⟩ := h
  rcases hs.accounting with ⟨rfl, rfl, _⟩ | ⟨rfl, ev, hq, hclk, hpop, hpost⟩
  · exact Or.inl ⟨rfl, hs⟩
  · refine Or.inr ⟨c₁, ev, hs, by rw [hclk]; rfl, hq, hclk, hpop, hpost⟩

/-- Conservation along machine steps (draining timers does not touch the store). -/
theorem MStep.kind_eq {c c' : Config K St R} {q : R} (h : MStep P M Ψd A c q c') :
    ∀ x, (c'.D x).kind = (c.D x).kind := by
  obtain ⟨tick, c₁, hs, rfl⟩ := h
  cases tick <;> exact hs.kind_eq

/-- **Conservation along runs**: no run creates, drops or re-kinds a device. -/
theorem Steps.kind_eq {c c' : Config K St R} {q : R} (h : Steps P M Ψd A c q c') :
    ∀ x, (c'.D x).kind = (c.D x).kind := by
  induction h with
  | refl => intro _; rfl
  | step h₁ _ ih => intro x; rw [ih x, MStep.kind_eq h₁ x]

/-- The kinds of a population are those of the store's devices plus the ambient's. -/
private theorem pop_kinds_eq {S S' : RPeriphs K St} (h : ∀ x, (S' x).kind = (S x).kind)
    (A : Multiset (K × St)) : (pop S' A).map Prod.fst = (pop S A).map Prod.fst := by
  unfold pop
  rw [Multiset.map_add, Multiset.map_add, kinds_eq_of h]

/-- **Whole-run accounting on the machine.**  The cost of any run — any schedule, any hardware
behaviour, any timeouts — is the sum of its charge events; every event charges a population
with the same multiset of kinds as the start (the active member, if any, pays its transition or
spawn cost once, every passive member its background cost once, nobody else is charged); and
the run ends with the same multiset of kinds.  (Ambient entries carry no name, so this is stated
for kinds.) -/
theorem Steps.accounting {c c' : Config K St R} {q : R} (h : Steps P M Ψd A c q c') :
    ∃ L : List (MEvent K St R), q = MEvent.total M L ∧
      (∀ ev ∈ L, ev.pop.map Prod.fst = (pop c.D A).map Prod.fst) ∧
      (pop c'.D A).map Prod.fst = (pop c.D A).map Prod.fst := by
  induction h with
  | refl => exact ⟨[], (by simp [MEvent.total]), fun _ h => (by cases h), rfl⟩
  | step h₁ hrest ih =>
    obtain ⟨L, hq, hL, hend⟩ := ih
    have hk := pop_kinds_eq (MStep.kind_eq h₁) A
    rcases MStep.accounting h₁ with ⟨rfl, _⟩ | ⟨_, ev, _, _, hq₁, _, hpop, _⟩
    · refine ⟨L, by rw [hq, zero_add], fun ev hev => by rw [hL ev hev, hk], by rw [hend, hk]⟩
    · refine ⟨ev :: L, ?_, ?_, by rw [hend, hk]⟩
      · rw [hq₁, hq]; simp only [MEvent.total, List.map_cons, List.sum_cons]
      · intro e he
        rcases List.mem_cons.1 he with rfl | he
        · rw [hpop]
        · rw [hL e he, hk]
