import Heliod.Examples.LogData
import Mathlib.Tactic.Ring

/-!
# Worked example: `match` on peripheral state

Exercises T-Match / `ArmsTyped`: exhaustiveness, narrowing of the matched peripheral in each
arm, and the join of the arms' outputs (union of the resulting state sets).

```
fn settle(x, temp) : (int, {Idle, Measure}) → (int, {Measure}) {
  match temp with
  | Idle    → skip
  | Measure → downgrade(temp, Off);
  transition(temp, Measure);         -- from the joined states {Idle, Off}
  ret := x
}

main (handles: temp : sensor @ Off, aux : sensor @ Off) {
  transition(temp, Idle);
  let y = settle(0, temp)
}
```

Inside `settle`, `temp` may be `Idle` or `Measure`.  The `Idle` arm leaves it `Idle`, the
`Measure` arm downgrades it to `Off`, so after the `match` the typing knows only
`temp ∈ {Idle, Off}`; the following transition is charged the worst case over both.
Reuses the platform `P` and the cost abbreviations `bg`, `tr` of `Heliod.Examples.LogData`.
-/

namespace MatchExample

open LogDataExample

/-- `settle` as a declaration. -/
def settle : FunDecl Kind TS ℕ where
  name := "settle"
  arg := "x"
  argTy := .int
  parg := "temp"
  pKind := .sensor
  sIn := {.idle, .measure}
  retTy := .int
  sOut := {.measure}
  body :=
    .seq (.matchSt "temp" (.cons .idle .skip (.cons .measure (.downgrade "temp" .off) .nil)))
         (.transition "temp" .measure)
  ret := .var "x"

/-- The whole program. -/
def prog : Program Kind TS ℕ where
  periphs := [("temp", .sensor, .off), ("aux", .sensor, .off)]
  funs := [settle]
  main := .seq (.transition "temp" .idle) (.call "y" "settle" (.val (.int 0)) "temp")

section Cost
variable (M : CostModel Kind TS ℕ)

/-- `settle`'s cost at clock `f` with ambient background `b`.

* the `match` costs the worse of its arms — `skip` is free and takes no time, the downgrade
  costs `tr Measure Off` plus the ambient — plus the background of every peripheral at the
  `match` itself: `temp` at its worst possible state in `{Idle, Measure}`, and the ambient;
* the transition after the `match` starts from the joined states `{Idle, Off}`. -/
def settleCost (f b : ℕ) : ℕ :=
  -- match temp with Idle → skip | Measure → downgrade(temp, Off)
  f * (tr M .measure .off + b) + f * (max (bg M .idle) (bg M .measure) + b)
  -- transition(temp, Measure) from {Idle, Off}
  + f * (max (tr M .idle .measure) (tr M .off .measure) + b)
  -- ret := x
  + f * M.varCost

/-- `settle`'s signature. -/
def settleSig : FunSig Kind TS ℕ where
  argTy := .int
  pKind := .sensor
  sIn := {.idle, .measure}
  retTy := .int
  sOut := {.measure}
  cost := settleCost M
  clk := fun f => f

/-- **T-FunDecl for `settle`: its summary is `settleCost`.**  Exercises T-Match / `ArmsTyped`:
exhaustiveness, narrowing of `temp` in each arm, and the join `{Idle} ∪ {Off}` of the arms'
outputs, which the following transition must cover. -/
theorem settle_typed : FunDeclTyped P M (fun _ => none) settle (settleSig M) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  -- See `LogDataExample.logData_typed` for why the witnesses are introduced with `apply`.
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨{.measure}, ?deriv, ?ret, ?out, ?sub, ?cost, ?clk⟩
  case deriv =>
    apply Typed.seq
    · -- match temp with Idle → skip | Measure → downgrade(temp, Off)
      apply Typed.matchSt (k := .sensor) (S := {.idle, .measure})
      · simp [settle]
      · simp [Arms.states]
      · apply ArmsTyped.cons
        · exact Typed.skip
        · apply ArmsTyped.one
          apply Typed.downgrade (k := .sensor) (S := {.measure})
          · simp
          · trivial
          · simp [P]
    · -- transition(temp, Measure) from the joined states {Idle} ∪ {Off}
      apply Typed.transition (k := .sensor) (S := {.idle} ∪ {.off})
      · simp [PEntry.join]
      · trivial
      · simp [P, rank]
  case ret => exact HasTy.var (by simp [settle, TCtx.inter])
  case out => simp [settle]
  case sub => simp [settle]
  case cost =>
    funext f b
    simp [settleSig, settleCost, bg, tr, settle, Expr.cost, CostModel.maxTrans,
      CostModel.maxBg, PEntry.bg]
  case clk => funext f; simp [settleSig]

/-- The signatures after typing `prog`'s declarations. -/
noncomputable def sigs : SigCtx Kind TS ℕ :=
  Function.update (fun _ => none) "settle" (some (settleSig M))

/-- **The `match` example type-checks; `main` instantiates `settle`'s summary with ambient
`bg(aux)`.**  `temp` ends in `Measure`. -/
theorem prog_typed :
    ∃ Γ' Δ' Q F, Program.Typed P M prog (sigs M) Γ' Δ' Q F ∧
      (∀ f b, Q f b = f * (tr M .off .idle + bg M .off + b) + f * M.valCost
                      + settleCost M f (b + bg M .off)) ∧
      (∀ f, F f = f) ∧ Δ' "temp" = .live .sensor {.measure} := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨⟨?nodup, ?decls, ?main⟩, ?cost, ?clk, ?fin⟩
  case nodup => simp [prog, settle]
  case decls => exact DeclsTyped.cons (settle_typed M) DeclsTyped.nil
  case main =>
    dsimp only [prog]
    apply Typed.seq
    · -- main: transition(temp, Idle) from Off
      apply Typed.transition (k := .sensor) (S := {.off})
      · simp [Program.initPCtx]
      · trivial
      · simp [P, rank]
    · -- main: let y = settle(0, temp)
      apply Typed.call (sig := settleSig M) (S := {.idle})
      · simp [sigs]
      · exact HasTy.val
      · simp [Program.initPCtx]
      · simp [Program.initPCtx, settleSig]
      · simp [settleSig]
  case cost =>
    intro f b
    simp [settleSig, bg, tr, Program.initPCtx, Expr.cost, CostModel.maxTrans, CostModel.maxBg]
    ring
  case clk => intro f; simp [settleSig]
  case fin => simp [settleSig]

end Cost

end MatchExample
