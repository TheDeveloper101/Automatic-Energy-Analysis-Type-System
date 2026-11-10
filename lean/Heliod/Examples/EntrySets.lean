import Heliod.Inference
import Heliod.Examples.LogData

/-!
# Example: accepted entry sets are not closed under union

The typing is path-insensitive: after a `match`, the variable context is the intersection of
the arms' contexts, forgetting which arm ran.  So a body can type from each of two entry states
alone but not from both:

```
fn pick(a, s) : sensor {
  match s with
  | Idle    → let x = true
  | Measure → let x = 1;
  match s with
  | Idle    → if x then skip else skip     -- x : bool
  | Measure → let y = x + 1;               -- x : int
  ret := ()
}
```

From `{Idle}` (or `{Measure}`) only one arm of each `match` is reachable, and `x` has the type
that arm needs.  From `{Idle, Measure}` the first `match` joins `x : bool` with `x : int`, which
drops `x`, and the second `match` cannot type either arm.  Hence `Idle` and `Measure` are both in
`entrySet pick`, but `{Idle, Measure}` is not accepted: there is no largest accepted entry set.
Holds for every cost model and declaration context (no calls, no transitions are involved).
Reuses the kinds and states of `Heliod.Examples.LogData`.
-/

namespace EntrySetsExample

open LogDataExample

/-- The declaration `pick` (the `sIn` / `sOut` annotations are unused by inline typing). -/
def pick : FunDecl Kind TS ℕ where
  name := "pick"
  arg := "a"
  argTy := .int
  parg := "s"
  pKind := .sensor
  sIn := {.idle}
  retTy := .unit
  sOut := {.idle}
  body :=
    .seq (.matchSt "s" (.cons .idle (.assign "x" (.val (.bool true)))
                         (.cons .measure (.assign "x" (.val (.int 1))) .nil)))
         (.matchSt "s" (.cons .idle (.ite (.var "x") .skip .skip)
                         (.cons .measure (.assign "y" (.binop .add (.var "x") (.val (.int 1)))) .nil)))
  ret := .val .unit

variable {M : CostModel Kind TS ℕ} {Ψd : FCtx Kind TS ℕ}

/-- `pick` accepts `{Idle}`: each `match` takes its `Idle` arm, where `x : bool`. -/
theorem accepts_idle : Accepts P M Ψd pick {.idle} := by
  refine ⟨Finset.singleton_nonempty _, _, _, _, _,
    .seq (.matchSt (k := .sensor) (S := {.idle}) (by simp [pick]) (by simp [Arms.states])
          (.last (Finset.mem_singleton_self _) (.assign .val (by simp [pick]))
            (by simp [Arms.states])))
         (.matchSt (k := .sensor) (S := {.idle}) (by simp [pick]) (by simp [Arms.states])
          (.last (Finset.mem_singleton_self _)
            (.ite (.var (by simp [TCtx.bind, Val.ty])) .skip .skip) (by simp [Arms.states]))),
    .val⟩

/-- `pick` accepts `{Measure}`: each `match` takes its `Measure` arm, where `x : int`. -/
theorem accepts_measure : Accepts P M Ψd pick {.measure} := by
  refine ⟨Finset.singleton_nonempty _, _, _, _, _,
    .seq (.matchSt (k := .sensor) (S := {.measure}) (by simp [pick]) (by simp [Arms.states])
          (.skip (by simp)
            (.last (Finset.mem_singleton_self _)
              (.assign .val (by simp [pick])) (by simp [Arms.states]))))
         (.matchSt (k := .sensor) (S := {.measure}) (by simp [pick]) (by simp [Arms.states])
          (.skip (by simp)
            (.last (Finset.mem_singleton_self _)
              (.assign (.binop (.var (by simp [TCtx.bind, Val.ty])) .val .add)
                (by simp [pick]))
              (by simp [Arms.states])))),
    .val⟩

/-- **`pick` does not accept `{Idle, Measure}`.**  Both arms of the first `match` are reachable,
so `x` is bound at `bool` in one and `int` in the other and the join drops it; whichever arm of
the second `match` is typed then needs `x`. -/
theorem not_accepts_both : ¬ Accepts P M Ψd pick {.idle, .measure} := by
  rintro ⟨-, Γb, Δb, Qb, Fb, h, -⟩
  dsimp only [pick] at h
  cases h with
  | seq h₁ h₂ =>
  cases h₁ with
  | matchSt hp _ ha =>
  rw [Finsupp.single_eq_same] at hp
  cases hp
  -- first `match`: both arms are reachable, so it is `cons` (Idle) then `last` (Measure)
  cases ha with
  | last _ _ hrest => exact hrest .measure (by simp [Arms.states]) (by simp)
  | skip hst _ => simp at hst
  | cons _ hA ha =>
  cases ha with
  | skip hst _ => simp at hst
  | cons _ _ hn => cases hn
  | last _ hB _ =>
  cases hA with
  | assign hA _ =>
  cases hB with
  | assign hB _ =>
  cases hA; cases hB
  -- second `match`: whichever arm is typed reads `x`, which the join dropped
  cases h₂ with
  | matchSt _ _ ha =>
  cases ha with
  | last _ hc _ | cons _ hc _ =>
    cases hc with
    | ite hx _ _ =>
    cases hx with
    | var hx => simp [TCtx.inter, TCtx.bind, Val.ty] at hx
  | skip _ ha =>
    cases ha with
    | skip _ hn => cases hn
    | last _ hc _ | cons _ hc _ =>
      cases hc with
      | assign hx _ =>
      cases hx with
      | binop hx _ hop =>
      cases hop
      cases hx with
      | var hx => simp [TCtx.inter, TCtx.bind, Val.ty] at hx

/-- **No largest accepted entry set**: `Idle` and `Measure` are both entry states of `pick`,
yet the set of both is not accepted, so `entrySet pick` is not accepted. -/
theorem entrySet_not_accepted :
    TS.idle ∈ entrySet P M Ψd pick ∧ TS.measure ∈ entrySet P M Ψd pick ∧
      ¬ Accepts P M Ψd pick {.idle, .measure} :=
  ⟨accepts_idle, accepts_measure, not_accepts_both⟩

end EntrySetsExample
