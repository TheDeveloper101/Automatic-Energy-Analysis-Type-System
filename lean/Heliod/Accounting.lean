import Heliod.Semantics
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Accounting (A): every peripheral is charged exactly once per step

`CLAUDE.md` asks for *completeness of accounted resources*: at each logical step every peripheral
must be charged (actively or in the background), and none twice.  This file proves the semantic
half of that claim for the big-step cost semantics `Eval`.

## The population

At any point of a run, the peripherals that physically exist are the frame's visible ones `S`
together with the ambient (caller-owned, invisible) ones `A`.  We call the multiset
`pop S A = entries(S) + A` of their `(kind, state)` pairs the **population**.

## Results

1. **Conservation** (`Eval.kind_eq`, `Eval.kinds_conserved`): a run never creates, destroys or
   re-kinds a peripheral; each handle keeps its kind, so the multiset of kinds in the population
   is invariant.  Only states change.
2. **Call boundary** (`pop_call`): the body of a call runs with exactly the caller's population —
   the callee's visible parameter plus the new ambient `A + entries(S ∖ p)` re-partitions the
   same peripherals, losing none and duplicating none.
3. **Per-step charges.**  Every rule of `Eval` charges peripherals in one of two shapes:
   * *static steps* (assign, if, clock, match, and the call's argument and return-expression
     evaluations): the charge is `K · bg(pop S A)`, i.e. every member
     of the population pays its background cost once (`charge_static`);
   * *mover steps* (transition, downgrade on handle `p` in state `s`): the population splits as
     `(k, s) ::ₘ rest` and the charge is `K · (transCost k s st + bg(rest))` — the moving peripheral
     pays its transition cost *instead of* its background cost, everyone else pays background
     once (`charge_move`).  Afterwards the mover is in the population with its new state
     (`pop_after_move`).
   `skip` and `seq` charge nothing themselves; the body of a call charges the population by (2).

Together these say that, at every step, the charge is a sum over the population in which each
member appears exactly once.

4. **Whole runs** (`Eval.whole_run_accounting`): an instrumented semantics `ETrace`, faithful to
   `Eval` in both directions (`ETrace.toEval`, `Eval.toTrace`), records a run as a list of charge
   events.  The run's cost is the sum of the events.  Each event splits its population into one
   optional mover (charged its transition) and the rest (each charged background), so each
   member is charged exactly once per event (by construction of `Event`); and every event's
   population has the same multiset of kinds as the run's start (`ETrace.pop_kinds`).
-/

variable {K St R : Type}

/-! ### Kinds of runtime entries -/

/-- The kind of a runtime entry, `none` for an absent handle. -/
def REntry.kind : REntry K St → Option K
  | .absent => none
  | .at k _ => some k

/-- An entry has no kind exactly when it is absent; used to show conserved kinds imply equal
supports. -/
theorem REntry.kind_eq_none {e : REntry K St} : e.kind = none ↔ e = 0 := by
  cases e <;> simp [REntry.kind]; rfl

namespace RPeriphs

/-- The population of a frame: its visible peripherals' `(kind, state)` pairs plus the ambient
ones. -/
noncomputable def pop (S : RPeriphs K St) (A : Multiset (K × St)) : Multiset (K × St) :=
  S.entries + A

/-- Splitting a `Finsupp.sum` at a present handle `p`.  The basic tool for peeling the matched or
moving peripheral off the population (`REntry` has no addition, so `erase_add_single` is not
available). -/
private theorem sum_split {M' : Type} [AddCommMonoid M'] (S : RPeriphs K St) (p : Var)
    (g : Var → REntry K St → M') (hp : S p ≠ 0) :
    S.sum g = g p (S p) + (S.erase p).sum g := by
  unfold Finsupp.sum RPeriphs.erase
  rw [Finsupp.support_erase, ← Finset.add_sum_erase _ _ (Finsupp.mem_support_iff.2 hp)]
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hx)]

/-- A present peripheral is one member of `entries`: `entries S = (k, s) ::ₘ entries (S ∖ p)`. -/
theorem entries_of {S : RPeriphs K St} {p : Var} {k : K} {s : St} (h : S p = .at k s) :
    S.entries = (k, s) ::ₘ (S.erase p).entries := by
  unfold RPeriphs.entries
  rw [sum_split S p _ (by rw [h]; exact fun h' => by cases h'), h]
  rfl

/-- A single handle contributes exactly its own entry. -/
theorem entries_single (q : Var) (k : K) (s : St) :
    RPeriphs.entries (Finsupp.single q (REntry.at k s)) = {(k, s)} := by
  unfold RPeriphs.entries
  exact Finsupp.sum_single_index rfl

/-- Overwriting `p` and then erasing it is the same as erasing it. -/
theorem erase_set (S : RPeriphs K St) (p : Var) (k : K) (s : St) :
    (S.set p k s).erase p = S.erase p := by
  ext x; simp only [erase_apply, set_apply]; split_ifs <;> rfl

/-- Pointwise kind preservation under `S[p ↦ st]` when `p` already has kind `k`.  The only way
`Eval` modifies the visible peripherals. -/
theorem kind_set {S : RPeriphs K St} {p : Var} {k : K} {s : St} (h : S p = .at k s) (st : St) :
    ∀ x, ((S.set p k st) x).kind = (S x).kind := by
  intro x
  rw [set_apply]
  split_ifs with hx
  · subst hx; rw [h]; rfl
  · rfl

/-- The multiset of a single entry's kind. -/
private def kindMS : Option K → Multiset K
  | none => 0
  | some k => {k}

/-- The kinds of `entries S` are determined by the handle-wise kinds. -/
private theorem entries_map_fst (S : RPeriphs K St) :
    S.entries.map Prod.fst = S.sum fun _ e => kindMS e.kind := by
  unfold RPeriphs.entries
  rw [← Multiset.coe_mapAddMonoidHom, map_finsuppSum]
  refine Finsupp.sum_congr fun x _ => ?_
  cases S x <;> rfl

/-- Handle-wise equal kinds give equal multisets of kinds. -/
theorem kinds_eq_of {S S' : RPeriphs K St} (h : ∀ x, (S' x).kind = (S x).kind) :
    S'.entries.map Prod.fst = S.entries.map Prod.fst := by
  rw [entries_map_fst, entries_map_fst]
  have hs : S'.support = S.support := Finset.ext fun x => by
    simp only [Finsupp.mem_support_iff, ne_eq, ← REntry.kind_eq_none, h x]
  unfold Finsupp.sum
  rw [hs]
  exact Finset.sum_congr rfl fun x _ => by show kindMS _ = kindMS _; rw [h x]

end RPeriphs

open RPeriphs

variable [CommSemiring R]

/-! ### (1) Conservation -/

/-- **Conservation, handle-wise.**  A run keeps every visible handle's kind (and presence): only
peripheral *states* change.  Transitions, downgrades and calls overwrite `p` with its own kind;
every other rule leaves `S` untouched or composes runs. -/
theorem Eval.kind_eq [DecidableEq St] {M : CostModel K St R} {Ψ : FCtx K St R} {A σ S Kc c σ' S' q K'}
    (h : Eval M Ψ A σ S Kc c σ' S' q K') : ∀ x, (S' x).kind = (S x).kind := by
  induction h with
  | skip => intro x; rfl
  | assign => intro x; rfl
  | iteTrue _ _ ih => exact ih
  | iteFalse _ _ ih => exact ih
  | transition hp => exact kind_set hp _
  | downgrade hp => exact kind_set hp _
  | clock => intro x; rfl
  | seq _ _ ih₁ ih₂ => intro x; rw [ih₂, ih₁]
  | matchSt _ _ _ ih => exact ih
  | call _ _ hp _ _ _ _ => exact kind_set hp _

/-- **Conservation of the population's kinds.**  The multiset of peripheral kinds in
`pop S A` is invariant under any run: no peripheral is created, lost or duplicated, up to its
kind.  (Ambient entries carry no name, so this is stated for kinds, not device identities.) -/
theorem Eval.kinds_conserved [DecidableEq St] {M : CostModel K St R} {Ψ : FCtx K St R} {A σ S Kc c σ' S' q K'}
    (h : Eval M Ψ A σ S Kc c σ' S' q K') :
    (pop S' A).map Prod.fst = (pop S A).map Prod.fst := by
  unfold pop
  rw [Multiset.map_add, Multiset.map_add, kinds_eq_of h.kind_eq]

/-! ### (2) The call boundary -/

/-- **Calls re-partition, never duplicate.**  In E-Call the body sees `{parg ↦ (k, s)}` and the
ambient `A + entries(S ∖ p)`; its population is exactly the caller's.  Hence the body's steps
charge the very same peripherals the caller's steps do — the moving handle once (as the callee's
parameter) and every other one once (as ambient). -/
theorem pop_call {S : RPeriphs K St} {p : Var} {k : K} {s : St} (h : S p = .at k s)
    (q : Var) (A : Multiset (K × St)) :
    pop (Finsupp.single q (REntry.at k s)) (A + (S.erase p).entries) = pop S A := by
  unfold pop
  rw [RPeriphs.entries_single, RPeriphs.entries_of h, ← Multiset.singleton_add]
  abel

/-! ### (3) Per-step charges -/

/-- Background cost of the population: visible plus ambient. -/
theorem ambBg_pop (M : CostModel K St R) (S : RPeriphs K St) (A : Multiset (K × St)) :
    ambBg M (pop S A) = S.bg M + ambBg M A := by
  unfold pop; rw [add_comm, ambBg_add_entries, add_comm]

/-- **Static steps charge each member's background once.**  The peripheral part
`K·(bg(S) + bg(A))` of E-Assign, E-If, E-Clock and E-Match is `K` times the sum of `bgCost` over
the population, each member counted once. -/
theorem charge_static (M : CostModel K St R) (S : RPeriphs K St) (A : Multiset (K × St))
    (Kc : R) :
    Kc * (S.bg M + ambBg M A) = Kc * ((pop S A).map fun ks => M.bgCost ks.1 ks.2).sum := by
  rw [← ambBg_pop]; rfl

/-- The population split off at a present handle `p`: `pop S A = (k, s) ::ₘ pop (S ∖ p) A`.
Shared by `charge_move` and the trace theorem `ETrace.pop_kinds`. -/
theorem pop_split {S : RPeriphs K St} {p : Var} {k : K} {s : St} (h : S p = .at k s)
    (A : Multiset (K × St)) : pop S A = (k, s) ::ₘ pop (S.erase p) A := by
  unfold pop; rw [entries_of h, Multiset.cons_add]

/-- **Mover steps charge the mover's transition and everyone else's background, once each.**
For E-Transition / E-Downgrade on `p` in state `s`: the population is `(k, s) ::ₘ rest`, and the
charge `K·(transCost k s st + bg(S ∖ p) + bg(A))` is `K·(transCost k s st + bg(rest))` — the
mover is not also charged background, and no other member is skipped. -/
theorem charge_move (M : CostModel K St R) {S : RPeriphs K St} {p : Var} {k : K} {s : St}
    (h : S p = .at k s) (A : Multiset (K × St)) (Kc : R) (st : St) :
    pop S A = (k, s) ::ₘ pop (S.erase p) A ∧
      Kc * (M.transCost k s st + (S.erase p).bg M + ambBg M A) =
        Kc * (M.transCost k s st + ambBg M (pop (S.erase p) A)) := by
  exact ⟨pop_split h A, by rw [ambBg_pop, add_assoc]⟩

/-- After a mover step the population is the same peripherals with the mover in its new state
`st`: `pop (S[p ↦ st]) A = (k, st) ::ₘ rest`. -/
theorem pop_after_move {S : RPeriphs K St} {p : Var} (k : K) (st : St)
    (A : Multiset (K × St)) :
    pop (S.set p k st) A = (k, st) ::ₘ pop (S.erase p) A := by
  have h : (S.set p k st) p = .at k st := by simp
  unfold pop; rw [entries_of h, erase_set, Multiset.cons_add]

/-! ### (4) Whole runs: an instrumented trace semantics

The identities above are per rule.  To state accounting for a *whole run* we record the charges
of a run as a list of events.  `ETrace` has exactly the rules of `Eval`, but instead of a summed
cost it outputs the list of charge events, each tagged with the population at that point.

An **event** `⟨clk, cpu, active, passive⟩` is one step at clock `clk` with CPU cost `cpu`.  Its
population is split into the (at most one) `active` peripheral, which moves from `s` to `st`,
and the `passive` rest.  It charges `cpu + clk · (transCost k s st + bg(passive))`: the active
member pays its transition cost and every passive member its background cost.  Because `active`
and `passive` partition the population, each member is charged exactly once **by
construction**; the theorems below show that the population recorded is the real one.

A call contributes an event for its argument evaluation (caller's frame), the body's events, and
an event for its return expression (callee's frame, whose population is again the caller's).

Results: `ETrace.toEval` / `Eval.toTrace` (the trace semantics is faithful: same runs, and the
events sum to the `Eval` cost), `ETrace.pop_kinds` (every event's population is the same set of
devices as the initial one), and the combination `Eval.whole_run_accounting`.
-/

/-- One charge event of a run; see the section doc. -/
structure Event (K St R : Type) where
  /-- The clock in force during the step. -/
  clk : R
  /-- CPU cost of the step (expression evaluation, clock change). -/
  cpu : R
  /-- The moving peripheral `(kind, from, to)`, if any. -/
  active : Option (K × St × St)
  /-- The other members of the population. -/
  passive : Multiset (K × St)

namespace Event

/-- The population an event charges: the active member (in its source state) plus the passive
ones. -/
def pop (e : Event K St R) : Multiset (K × St) :=
  match e.active with
  | none => e.passive
  | some (k, s, _) => (k, s) ::ₘ e.passive

/-- The cost of the active member: its transition cost, or nothing if no peripheral moves. -/
def activeCost (M : CostModel K St R) : Option (K × St × St) → R
  | none => 0
  | some (k, s, st) => M.transCost k s st

/-- What an event charges: CPU cost, plus `clk ·` (active member's transition cost + every
passive member's background cost). -/
def charge (M : CostModel K St R) (e : Event K St R) : R :=
  e.cpu + e.clk * (activeCost M e.active + ambBg M e.passive)

/-- Total charge of a list of events. -/
def total (M : CostModel K St R) (L : List (Event K St R)) : R :=
  (L.map (charge M)).sum

end Event

variable [DecidableEq St]

/-- Instrumented big-step semantics: the rules of `Eval`, outputting the list of charge events
instead of their sum.  Clock binders are named `Kc` (the `Eval` source reuses `K`). -/
inductive ETrace (M : CostModel K St R) (Ψ : FCtx K St R) :
    Multiset (K × St) → Mem → RPeriphs K St → R → Cmd St R →
    Mem → RPeriphs K St → List (Event K St R) → R → Prop where
  | skip {A σ S Kc} : ETrace M Ψ A σ S Kc .skip σ S [] Kc
  | assign {A σ S Kc x e v} :
      e.eval σ = some v →
      ETrace M Ψ A σ S Kc (.assign x e) (σ.set x v) S [⟨Kc, Kc * e.cost M, none, pop S A⟩] Kc
  | iteTrue {A σ S Kc e c₁ c₂ σ' S' L K'} :
      e.eval σ = some (.bool true) →
      ETrace M Ψ A σ S Kc c₁ σ' S' L K' →
      ETrace M Ψ A σ S Kc (.ite e c₁ c₂) σ' S' (⟨Kc, Kc * e.cost M, none, pop S A⟩ :: L) K'
  | iteFalse {A σ S Kc e c₁ c₂ σ' S' L K'} :
      e.eval σ = some (.bool false) →
      ETrace M Ψ A σ S Kc c₂ σ' S' L K' →
      ETrace M Ψ A σ S Kc (.ite e c₁ c₂) σ' S' (⟨Kc, Kc * e.cost M, none, pop S A⟩ :: L) K'
  | transition {A σ S Kc p k s st} :
      S p = .at k s →
      ETrace M Ψ A σ S Kc (.transition p st) σ (S.set p k st)
        [⟨Kc, 0, some (k, s, st), pop (S.erase p) A⟩] Kc
  | downgrade {A σ S Kc p k s st} :
      S p = .at k s →
      ETrace M Ψ A σ S Kc (.downgrade p st) σ (S.set p k st)
        [⟨Kc, 0, some (k, s, st), pop (S.erase p) A⟩] Kc
  | clock {A σ S Kc f'} :
      ETrace M Ψ A σ S Kc (.clock f') σ S [⟨Kc, M.clockCost Kc f', none, pop S A⟩] f'
  | seq {A σ S Kc c₁ c₂ σ₁ S₁ L₁ K₁ σ₂ S₂ L₂ K₂} :
      ETrace M Ψ A σ S Kc c₁ σ₁ S₁ L₁ K₁ →
      ETrace M Ψ A σ₁ S₁ K₁ c₂ σ₂ S₂ L₂ K₂ →
      ETrace M Ψ A σ S Kc (.seq c₁ c₂) σ₂ S₂ (L₁ ++ L₂) K₂
  | matchSt {A σ S Kc p arms k s c σ' S' L K'} :
      S p = .at k s → arms.find? s = some c →
      ETrace M Ψ A σ S Kc c σ' S' L K' →
      ETrace M Ψ A σ S Kc (.matchSt p arms) σ' S' (⟨Kc, 0, none, pop S A⟩ :: L) K'
  | call {A σ S Kc x g e p d v k s σb Sb Lb Kb r s'} :
      Ψ g = some d →
      e.eval σ = some v →
      S p = .at k s →
      ETrace M Ψ (A + (S.erase p).entries) (Mem.empty.set d.arg v)
        (Finsupp.single d.parg (.at k s)) Kc d.body σb Sb Lb Kb →
      d.ret.eval σb = some r →
      Sb d.parg = .at k s' →
      ETrace M Ψ A σ S Kc (.call x g e p) (σ.set x r) (S.set p k s')
        (⟨Kc, Kc * e.cost M, none, pop S A⟩ :: Lb ++
          [⟨Kb, Kb * d.ret.cost M, none, pop Sb (A + (S.erase p).entries)⟩]) Kb

/-- Transport an `Eval` derivation along an equation between costs. -/
private theorem Eval.cost_eq {M : CostModel K St R} {Ψ : FCtx K St R} {A σ S Kc c σ' S' q q' K'}
    (h : Eval M Ψ A σ S Kc c σ' S' q K') (hq : q = q') : Eval M Ψ A σ S Kc c σ' S' q' K' :=
  hq ▸ h

/-- **The trace is faithful (soundness direction).**  Every instrumented run is an `Eval` run
whose cost is the total of its events.  So the events neither invent nor drop charges. -/
theorem ETrace.toEval {M : CostModel K St R} {Ψ : FCtx K St R} {A σ S Kc c σ' S' L K'}
    (h : ETrace M Ψ A σ S Kc c σ' S' L K') : Eval M Ψ A σ S Kc c σ' S' (Event.total M L) K' := by
  induction h with
  | skip => exact Eval.skip
  | assign he =>
    refine (Eval.assign he).cost_eq ?_
    simp only [Event.total, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Event.charge, Event.activeCost, ambBg_pop]; ring
  | iteTrue he _ ih =>
    refine (Eval.iteTrue he ih).cost_eq ?_
    simp only [Event.total, List.map_cons, List.sum_cons, Event.charge, Event.activeCost,
      ambBg_pop]; ring
  | iteFalse he _ ih =>
    refine (Eval.iteFalse he ih).cost_eq ?_
    simp only [Event.total, List.map_cons, List.sum_cons, Event.charge, Event.activeCost,
      ambBg_pop]; ring
  | transition hp =>
    refine (Eval.transition hp).cost_eq ?_
    simp only [Event.total, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Event.charge, Event.activeCost, ambBg_pop]; ring
  | downgrade hp =>
    refine (Eval.downgrade hp).cost_eq ?_
    simp only [Event.total, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Event.charge, Event.activeCost, ambBg_pop]; ring
  | clock =>
    refine Eval.clock.cost_eq ?_
    simp only [Event.total, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Event.charge, Event.activeCost, ambBg_pop]; ring
  | seq _ _ ih₁ ih₂ =>
    refine (Eval.seq ih₁ ih₂).cost_eq ?_
    simp only [Event.total, List.map_append, List.sum_append]
  | matchSt hp hf _ ih =>
    refine (Eval.matchSt hp hf ih).cost_eq ?_
    simp only [Event.total, List.map_cons, List.sum_cons, Event.charge, Event.activeCost,
      ambBg_pop]; ring
  | call hg he hp _ hr hs ih =>
    refine (Eval.call hg he hp ih hr hs).cost_eq ?_
    simp only [Event.total, List.cons_append, List.map_cons, List.map_append, List.map_nil,
      List.sum_cons, List.sum_append, List.sum_nil, Event.charge, Event.activeCost, ambBg_pop]
    ring

/-- **The trace is faithful (completeness direction).**  Every `Eval` run can be instrumented,
and its cost is the total of the recorded events. -/
theorem Eval.toTrace {M : CostModel K St R} {Ψ : FCtx K St R} {A σ S Kc c σ' S' q K'}
    (h : Eval M Ψ A σ S Kc c σ' S' q K') :
    ∃ L, ETrace M Ψ A σ S Kc c σ' S' L K' ∧ Event.total M L = q := by
  induction h with
  | skip => exact ⟨_, ETrace.skip, rfl⟩
  | assign he =>
    refine ⟨_, ETrace.assign he, ?_⟩
    simp only [Event.total, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Event.charge, Event.activeCost, ambBg_pop]; ring
  | iteTrue he _ ih =>
    obtain ⟨L, hL, rfl⟩ := ih
    refine ⟨_, ETrace.iteTrue he hL, ?_⟩
    simp only [Event.total, List.map_cons, List.sum_cons, Event.charge, Event.activeCost,
      ambBg_pop]; ring
  | iteFalse he _ ih =>
    obtain ⟨L, hL, rfl⟩ := ih
    refine ⟨_, ETrace.iteFalse he hL, ?_⟩
    simp only [Event.total, List.map_cons, List.sum_cons, Event.charge, Event.activeCost,
      ambBg_pop]; ring
  | transition hp =>
    refine ⟨_, ETrace.transition hp, ?_⟩
    simp only [Event.total, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Event.charge, Event.activeCost, ambBg_pop]; ring
  | downgrade hp =>
    refine ⟨_, ETrace.downgrade hp, ?_⟩
    simp only [Event.total, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Event.charge, Event.activeCost, ambBg_pop]; ring
  | clock =>
    refine ⟨_, ETrace.clock, ?_⟩
    simp only [Event.total, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Event.charge, Event.activeCost, ambBg_pop]; ring
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨L₁, h₁, rfl⟩ := ih₁
    obtain ⟨L₂, h₂, rfl⟩ := ih₂
    refine ⟨_, ETrace.seq h₁ h₂, ?_⟩
    simp only [Event.total, List.map_append, List.sum_append]
  | matchSt hp hf _ ih =>
    obtain ⟨L, hL, rfl⟩ := ih
    refine ⟨_, ETrace.matchSt hp hf hL, ?_⟩
    simp only [Event.total, List.map_cons, List.sum_cons, Event.charge, Event.activeCost,
      ambBg_pop]; ring
  | call hg he hp _ hr hs ih =>
    obtain ⟨L, hL, rfl⟩ := ih
    refine ⟨_, ETrace.call hg he hp hL hr hs, ?_⟩
    simp only [Event.total, List.cons_append, List.map_cons, List.map_append, List.map_nil,
      List.sum_cons, List.sum_append, List.sum_nil, Event.charge, Event.activeCost, ambBg_pop]
    ring

/-- **Every event charges the real population.**  Each event of a run charges a population
with the same kinds as the run's initial population `pop S A`, including events inside called
functions and at their return (via `pop_call`) and after earlier state changes (via
`Eval.kinds_conserved`).  For transitions, the recorded population `(k, s) ::ₘ pop (S ∖ p) A` is
the current one by `pop_split`. -/
theorem ETrace.pop_kinds {M : CostModel K St R} {Ψ : FCtx K St R} {A σ S Kc c σ' S' L K'}
    (h : ETrace M Ψ A σ S Kc c σ' S' L K') :
    ∀ ev ∈ L, ev.pop.map Prod.fst = (pop S A).map Prod.fst := by
  induction h with
  | skip => intro _ hm; cases hm
  | assign => intro _ hm; rw [List.mem_singleton] at hm; subst hm; rfl
  | clock => intro _ hm; rw [List.mem_singleton] at hm; subst hm; rfl
  | transition hp =>
    intro _ hm; rw [List.mem_singleton] at hm; subst hm
    rw [pop_split hp _]; rfl
  | downgrade hp =>
    intro _ hm; rw [List.mem_singleton] at hm; subst hm
    rw [pop_split hp _]; rfl
  | iteTrue _ _ ih =>
    intro _ hm
    rcases List.mem_cons.1 hm with rfl | hm
    · rfl
    · exact ih _ hm
  | iteFalse _ _ ih =>
    intro _ hm
    rcases List.mem_cons.1 hm with rfl | hm
    · rfl
    · exact ih _ hm
  | matchSt _ _ _ ih =>
    intro _ hm
    rcases List.mem_cons.1 hm with rfl | hm
    · rfl
    · exact ih _ hm
  | seq h₁ _ ih₁ ih₂ =>
    intro _ hm
    rcases List.mem_append.1 hm with hm | hm
    · exact ih₁ _ hm
    · rw [ih₂ _ hm]; exact h₁.toEval.kinds_conserved
  | call _ _ hp hb _ _ ih =>
    intro _ hm
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hm
    rcases hm with rfl | hm | rfl
    · rfl
    · rw [ih _ hm, pop_call hp]
    · show (pop _ _).map Prod.fst = _
      rw [hb.toEval.kinds_conserved, pop_call hp]

/-- **Whole-run accounting.**  The cost of any run is the sum of its charge events, and every
event charges a population with the same multiset of kinds as the run's start: the active
member (if any) pays its transition cost once, every passive member pays its background cost
once, and nobody else is charged. -/
theorem Eval.whole_run_accounting {M : CostModel K St R} {Ψ : FCtx K St R}
    {A σ S Kc c σ' S' q K'} (h : Eval M Ψ A σ S Kc c σ' S' q K') :
    ∃ L, ETrace M Ψ A σ S Kc c σ' S' L K' ∧ q = Event.total M L ∧
      ∀ ev ∈ L, ev.pop.map Prod.fst = (pop S A).map Prod.fst := by
  obtain ⟨L, hL, hq⟩ := h.toTrace
  exact ⟨L, hL, hq.symm, hL.pop_kinds⟩
