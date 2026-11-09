import Heliod.Typing
import Mathlib.Tactic.Ring

/-!
# Worked example: the writeup's `log_data` (Figures 1–3 of `writeup.tex`)

A sanity check that the checking rules in `Heliod.Typing` are not vacuous and that the cost
they derive has the shape the writeup predicts.

```
fn log_data(x, temp) : (int, {Idle, Measure}) → (int, {Off}) {
  transition(temp, Measure);
  let res = 65;                 -- stands in for `temp.measure()` (not in the core language)
  let t = 0;
  if (res == 65) { let t = 1 } else { skip };
  downgrade(temp, Off);
  ret := t
}

main (handles: temp : sensor @ Off, aux : sensor @ Off) {
  transition(temp, Idle);
  let t = log_data(0, temp)
}
```

The extra handle `aux` stays `Off` throughout; it exercises parametricity in ambient
peripherals: inside `log_data` it is invisible, but its background cost must still be charged
at every step.  `log_data` is typed once, with a summary parametric in the ambient background
`b`; `main` instantiates it with `b = bg(aux)`.

The sensor lattice is `Off ≤ Idle ≤ Measure` with downgrades `Measure ↪ Off`, `Idle ↪ Off`.
The cost model `M` is left **arbitrary**, so the theorem pins down the symbolic cost.
The clock is `1` throughout and costs are in `ℕ`.
-/

namespace LogDataExample

/-- The single peripheral kind of the example. -/
inductive Kind where
  | sensor
  deriving DecidableEq

/-- Sensor states. -/
inductive TS where
  | off | idle | measure
  deriving DecidableEq

/-- Height in the lattice `Off ≤ Idle ≤ Measure`. -/
def rank : TS → ℕ
  | .off => 0
  | .idle => 1
  | .measure => 2

/-- The temperature-sensor platform. -/
def P : Platform Kind TS where
  states _ := {.off, .idle, .measure}
  le _ s s' := rank s ≤ rank s'
  top _ := .measure
  dg _ s' s := s = .off ∧ s' ≠ .off
  stable _ _ := True
  hwReach _ _ := ∅

/-- The platform encoding satisfies the paper's well-formedness conditions — a check that the
`Platform.WF` conditions are satisfiable by the writeup's own example. -/
theorem P_wf : P.WF where
  le_refl _ _ _ := Nat.le_refl _
  le_trans _ _ _ _ h₁ h₂ := Nat.le_trans h₁ h₂
  le_antisymm _ s₁ s₂ h₁ h₂ := by cases s₁ <;> cases s₂ <;> simp_all [P, rank]
  le_mem _ s₁ s₂ _ := by cases s₁ <;> cases s₂ <;> simp [P]
  top_mem _ := by simp [P]
  le_top _ s _ := by cases s <;> simp [P, rank]
  dg_lt _ s' s h := by
    obtain ⟨rfl, h⟩ := h
    cases s' <;> simp_all [P, rank]
  hwReach_sub _ _ := by simp [P]
  hwReach_stable _ _ _ := rfl

/-- `log_data` as a declaration. -/
def logData : FunDecl Kind TS ℕ where
  name := "log_data"
  arg := "x"
  argTy := .int
  parg := "temp"
  pKind := .sensor
  sIn := {.idle, .measure}
  retTy := .int
  sOut := {.off}
  body :=
    .seq (.transition "temp" .measure) <|
    .seq (.assign "res" (.val (.int 65))) <|
    .seq (.assign "t" (.val (.int 0))) <|
    .seq (.ite (.binop .eq (.var "res") (.val (.int 65))) (.assign "t" (.val (.int 1))) .skip)
         (.downgrade "temp" .off)
  ret := .var "t"

/-- The whole program. -/
def prog : Program Kind TS ℕ where
  periphs := [("temp", .sensor, .off), ("aux", .sensor, .off)]
  funs := [logData]
  main := .seq (.transition "temp" .idle) (.call "t" "log_data" (.val (.int 0)) "temp")

section Cost
variable (M : CostModel Kind TS ℕ)

/-- Background cost of a sensor state, `C(p : s)` in the writeup. -/
abbrev bg (s : TS) : ℕ := M.bgCost .sensor s
/-- Transition cost, `C(p : (s, s'))` in the writeup. -/
abbrev tr (s s' : TS) : ℕ := M.transCost .sensor s s'

/-! ### `log_data`'s cost summary — parametric in the caller's clock and ambient peripherals -/

/-- The cost of `log_data` when called at clock `f` while peripherals the function cannot see
draw background power `b`.  Each line is one costed step; every step charges `b`, so the
ambient peripherals cost exactly `7·f·b` — whatever they are.

Compared with the writeup's `C_l = C(temp:(α₀,Measure)) + 3·C(temp:Measure) + C_v + max(C_v,0)
+ C(temp:(Measure,Off))`:
* `C(temp:(α₀,Measure))` becomes the worst case over the declared inputs, `max(tr Idle Measure,
  tr Measure Measure)` — the checking system has no state variables;
* there is a 4th `bg .measure` because T-If charges `cost(Δ)` for evaluating the condition, a
  step the writeup's table does not cost;
* expression costs (`valCost`, `varCost`, `binopCost .eq`) are explicit;
* the `if` costs its `then` branch: the `else skip` branch is free and takes no time;
* evaluating the return expression is a step too: `temp` (now `Off`) and the ambient draw
  background while it runs. -/
def logDataCost (f b : ℕ) : ℕ :=
  -- transition(temp, Measure) from {Idle, Measure}
  f * (max (tr M .idle .measure) (tr M .measure .measure) + b)
  -- let res = 65; let t = 0
  + f * (M.valCost + bg M .measure + b)
  + f * (M.valCost + bg M .measure + b)
  -- if (res == 65) { let t = 1 } else { skip }: the then-branch, plus evaluating the condition
  + f * (M.valCost + bg M .measure + b)
  + f * (M.binopCost .eq + M.varCost + M.valCost + bg M .measure + b)
  -- downgrade(temp, Off)
  + f * (tr M .measure .off + b)
  -- ret := t, with temp now Off
  + f * (M.varCost + bg M .off + b)

/-- `log_data`'s signature: its cost summary is `logDataCost`, and it does not change the clock. -/
def logDataSig : FunSig Kind TS ℕ where
  argTy := .int
  pKind := .sensor
  sIn := {.idle, .measure}
  retTy := .int
  sOut := {.off}
  cost := logDataCost M
  clk := fun f => f

/-- **T-FunDecl for `log_data`: its summary is `logDataCost`, for every clock and every ambient
background.**  The declaration is typed once, with no knowledge of its callers; this is the
parametricity the paper expresses with `β` and `cost(·)`. -/
theorem logData_typed : FunDeclTyped P M (fun _ => none) logData (logDataSig M) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  -- `apply Exists.intro` leaves the witnesses as ordinary metavariables, which the derivation
  -- below assigns by unification (`refine ⟨?Γ, …⟩` would make them opaque).
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨{.off}, ?deriv, ?ret, ?out, ?sub, ?cost, ?clk⟩
  case deriv =>
    apply Typed.seq
    · -- transition(temp, Measure) from {Idle, Measure}
      apply Typed.transition (k := .sensor) (S := {.idle, .measure})
      · simp [logData]
      · trivial
      · simp [P, rank]
    apply Typed.seq
    · -- let res = 65
      apply Typed.assign HasTy.val
      simp [logData]
    apply Typed.seq
    · -- let t = 0
      apply Typed.assign HasTy.val
      simp [logData]
    apply Typed.seq
    · -- if (res == 65) { let t = 1 } else { skip }
      apply Typed.ite
      · exact HasTy.binop (HasTy.var (by simp [logData, Val.ty])) HasTy.val BinOp.HasTy.eq
      · apply Typed.assign HasTy.val
        simp [logData]
      · exact Typed.skip
    · -- downgrade(temp, Off) from {Measure}
      apply Typed.downgrade (k := .sensor) (S := {.measure})
      · simp [logData]
      · trivial
      · simp [P]
  case ret => exact HasTy.var (by simp [logData, Val.ty, TCtx.inter])
  case out => simp [logData]
  case sub => simp [logData]
  case cost =>
    funext f b
    simp [logDataSig, logDataCost, bg, tr, logData, Expr.cost, CostModel.maxTrans,
      CostModel.maxBg, PEntry.bg]
    ring
  case clk => funext f; simp [logDataSig]

/-! ### The whole program -/

/-- The signatures after typing `prog`'s declarations. -/
noncomputable def sigs : SigCtx Kind TS ℕ :=
  Function.update (fun _ => none) "log_data" (some (logDataSig M))

/-- The expected cost of the whole program at clock `1`: `main`'s transition, the argument, and
`log_data` called with `aux` ambient — `aux`'s background is charged once per step (7 steps
inside `log_data`, plus `main`'s transition and argument). -/
def expectedCost : ℕ :=
  -- main: transition(temp, Idle), aux in background
  (tr M .off .idle + bg M .off)
  -- main: evaluate the argument `0`, temp (Idle) and aux (Off) in background
  + (M.valCost + bg M .idle + bg M .off)
  -- log_data, with aux's background as its ambient cost
  + logDataCost M 1 (bg M .off)

/-- **The program type-checks; `main`'s summary instantiates `log_data`'s with ambient
`bg(aux)`.**  For every clock `f` and ambient `b` (nothing is ambient for `main` in practice,
`b = 0`), `main` costs its transition and argument plus `logDataCost f (b + bg Off)`; at clock
`1` with nothing ambient this is `expectedCost`.  The clock is unchanged and `temp` ends `Off`. -/
theorem prog_typed :
    ∃ Γ' Δ' Q F, Program.Typed P M prog (sigs M) Γ' Δ' Q F ∧
      (∀ f b, Q f b = f * (tr M .off .idle + bg M .off + b)
                      + f * (M.valCost + bg M .idle + bg M .off + b)
                      + logDataCost M f (b + bg M .off)) ∧
      Q 1 0 = expectedCost M ∧ (∀ f, F f = f) ∧ Δ' "temp" = .live .sensor {.off} := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨⟨?nodup, ?decls, ?main⟩, ?cost, ?cost1, ?clk, ?fin⟩
  case nodup => simp [prog, logData]
  case decls => exact DeclsTyped.cons (logData_typed M) DeclsTyped.nil
  case main =>
    dsimp only [prog]
    apply Typed.seq
    · -- main: transition(temp, Idle) from Off
      apply Typed.transition (k := .sensor) (S := {.off})
      · simp [Program.initPCtx]
      · trivial
      · simp [P, rank]
    · -- main: let t = log_data(0, temp), instantiating log_data's summary
      apply Typed.call (sig := logDataSig M) (S := {.idle})
      · simp [sigs]
      · exact HasTy.val
      · simp [Program.initPCtx]
      · simp [Program.initPCtx, logDataSig]
      · simp [logDataSig]
  case cost =>
    intro f b
    simp [logDataSig, bg, tr, Program.initPCtx, Expr.cost, CostModel.maxTrans, CostModel.maxBg]
    ring
  case cost1 =>
    simp [logDataSig, expectedCost, bg, tr, Program.initPCtx, Expr.cost, CostModel.maxTrans,
      CostModel.maxBg]
    ring
  case clk => intro f; simp [logDataSig]
  case fin => simp [logDataSig]

end Cost

end LogDataExample
