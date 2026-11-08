import Heliod.Examples.LogData
import Mathlib.Tactic.Ring

/-!
# Worked examples: parametricity in peripherals a function does not use

The paper's `β` / `cost(·)` holes make a function's background-cost analysis parametric in
the peripherals that are live at a call site but invisible to the function.  With cost
summaries (`Heliod.Typing`), a function is typed once and its summary `Q f b` is instantiated at
each call with `b + cost(Δ ∖ p)`.  These examples check that this behaves as intended.

1. **Different callers** (`callers_differ_by_ambient`): the same `log_data` called from a
   program with no other peripherals and from one with two extra sensors.  The costs differ by
   exactly the extra sensors' background × the number of steps that run while they exist
   (`7·f·(bg Off + bg Measure)`: `main`'s transition plus `log_data`'s 6 steps).
2. **Nested calls** (`progN_typed`): `main → wrap → log_data`.  `main`'s other sensor is
   charged inside `log_data`, two calls down.
3. **Branches of unequal duration** (`branchy_exact`): the summary keeps
   `max(q₁ + T₁·b, q₂ + T₂·b)` rather than the looser `max(q₁, q₂) + max(T₁, T₂)·b`; on a concrete
   cost model the bound is `20` where the looser form would give `30`.

Reuses the sensor platform `P`, the abbreviations `bg`, `tr`, and `log_data` with its summary
`logDataCost` from `Heliod.Examples.LogData`.
-/

namespace ParametricityExample

open LogDataExample

section Cost
variable (M : CostModel Kind TS ℕ)

/-! ### 1. Different callers -/

/-- **Ambient peripherals enter `log_data`'s cost linearly, with coefficient `6·f`** — one charge
per costed step, at the caller's clock — whatever those peripherals are.  This is the
parametricity property in its simplest form. -/
theorem logDataCost_ambient (f b e : ℕ) :
    logDataCost M f (b + e) = logDataCost M f b + 6 * f * e := by
  unfold logDataCost; ring

/-- `log_data` called from a program whose only peripheral is `temp`. -/
def progA : Program Kind TS ℕ where
  periphs := [("temp", .sensor, .off)]
  funs := [logData]
  main := .seq (.transition "temp" .idle) (.call "t" "log_data" (.val (.int 0)) "temp")

/-- The same call from a program with two extra sensors, one `Off` and one `Measure`. -/
def progB : Program Kind TS ℕ where
  periphs := [("temp", .sensor, .off), ("aux", .sensor, .off), ("aux2", .sensor, .measure)]
  funs := [logData]
  main := .seq (.transition "temp" .idle) (.call "t" "log_data" (.val (.int 0)) "temp")

/-- `progA`'s `main` instantiates `log_data`'s summary with no extra ambient cost. -/
theorem progA_typed :
    ∃ Γ' Δ' Q F, Program.Typed P M progA (sigs M) Γ' Δ' Q F ∧
      ∀ f b, Q f b = f * (tr M .off .idle + b) + f * M.valCost + logDataCost M f b := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨⟨?nodup, ?decls, ?main⟩, ?cost⟩
  case nodup => simp [progA, logData]
  case decls => exact DeclsTyped.cons (logData_typed M) DeclsTyped.nil
  case main =>
    dsimp only [progA]
    apply Typed.seq
    · apply Typed.transition (k := .sensor) (S := {.off})
      · simp [Program.initPCtx]
      · trivial
      · simp [P, rank]
    · apply Typed.call (sig := logDataSig M) (S := {.idle})
      · simp [sigs]
      · exact HasTy.val
      · simp [Program.initPCtx]
      · simp [Program.initPCtx, logDataSig]
      · simp [logDataSig]
  case cost =>
    intro f b
    simp [logDataSig, tr, Program.initPCtx, Expr.cost, CostModel.maxTrans]
    ring

/-- `progB`'s `main` instantiates the *same* summary with ambient `bg(aux) + bg(aux2)`. -/
theorem progB_typed :
    ∃ Γ' Δ' Q F, Program.Typed P M progB (sigs M) Γ' Δ' Q F ∧
      ∀ f b, Q f b = f * (tr M .off .idle + (bg M .off + bg M .measure) + b) + f * M.valCost
                      + logDataCost M f (b + (bg M .off + bg M .measure)) := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨⟨?nodup, ?decls, ?main⟩, ?cost⟩
  case nodup => simp [progB, logData]
  case decls => exact DeclsTyped.cons (logData_typed M) DeclsTyped.nil
  case main =>
    dsimp only [progB]
    apply Typed.seq
    · apply Typed.transition (k := .sensor) (S := {.off})
      · simp [Program.initPCtx]
      · trivial
      · simp [P, rank]
    · apply Typed.call (sig := logDataSig M) (S := {.idle})
      · simp [sigs]
      · exact HasTy.val
      · simp [Program.initPCtx]
      · simp [Program.initPCtx, logDataSig]
      · simp [logDataSig]
  case cost =>
    intro f b
    simp [logDataSig, bg, tr, Program.initPCtx, Expr.cost, CostModel.maxTrans, CostModel.maxBg]
    ring

/-- **The two callers' costs differ by exactly the extra sensors' background, charged once per
step while they exist**: 7 steps (`main`'s transition and `log_data`'s 6), at clock `f`.
`log_data` itself was typed once, with no knowledge of either caller. -/
theorem callers_differ_by_ambient :
    ∃ QA QB, (∃ Γ' Δ' F, Program.Typed P M progA (sigs M) Γ' Δ' QA F) ∧
      (∃ Γ' Δ' F, Program.Typed P M progB (sigs M) Γ' Δ' QB F) ∧
      ∀ f b, QB f b = QA f b + 7 * f * (bg M .off + bg M .measure) := by
  obtain ⟨ΓA, ΔA, QA, FA, hA, hQA⟩ := progA_typed M
  obtain ⟨ΓB, ΔB, QB, FB, hB, hQB⟩ := progB_typed M
  refine ⟨QA, QB, ⟨ΓA, ΔA, FA, hA⟩, ⟨ΓB, ΔB, FB, hB⟩, fun f b => ?_⟩
  rw [hQA, hQB, logDataCost_ambient]
  ring

/-! ### 2. Nested calls -/

/-- `fn wrap(x, temp) : (int, {Idle, Measure}) → (int, {Off}) { let y = log_data(x, temp); ret := y }`.
`wrap` has no peripherals of its own besides `temp`, so whatever is ambient for `wrap` is passed
on, unchanged, as ambient for `log_data`. -/
def wrap : FunDecl Kind TS ℕ where
  name := "wrap"
  arg := "x"
  argTy := .int
  parg := "temp"
  pKind := .sensor
  sIn := {.idle, .measure}
  retTy := .int
  sOut := {.off}
  body := .call "y" "log_data" (.var "x") "temp"
  ret := .var "y"

/-- `wrap`'s summary: read `x`, run `log_data` at the *same* ambient background `b`, read `y`. -/
def wrapCost (f b : ℕ) : ℕ :=
  f * M.varCost + logDataCost M f b + f * M.varCost

/-- `wrap`'s signature. -/
def wrapSig : FunSig Kind TS ℕ where
  argTy := .int
  pKind := .sensor
  sIn := {.idle, .measure}
  retTy := .int
  sOut := {.off}
  cost := wrapCost M
  clk := fun f => f

/-- **T-FunDecl for `wrap`, typed against `log_data`'s signature only.**  `wrap`'s own `Δ ∖ temp`
is empty, so `log_data` is instantiated at exactly `wrap`'s ambient background `b`. -/
theorem wrap_typed :
    FunDeclTyped P M (Function.update (fun _ => none) "log_data" (some (logDataSig M)))
      wrap (wrapSig M) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨{.off}, ?deriv, ?ret, ?out, ?sub, ?cost, ?clk⟩
  case deriv =>
    apply Typed.call (sig := logDataSig M) (S := {.idle, .measure})
    · simp
    · exact HasTy.var (by simp [wrap, logDataSig])
    · simp [wrap]
    · simp [wrap, logDataSig]
    · simp [logDataSig]
  case ret => exact HasTy.var (by simp [wrap, logDataSig])
  case out => simp [wrap, logDataSig]
  case sub => simp [wrap]
  case cost =>
    funext f b
    simp [wrapSig, wrapCost, logDataSig, wrap, Expr.cost]
  case clk => funext f; simp [wrapSig, logDataSig]

/-- `main → wrap → log_data`, with an extra sensor `aux` (`Off`) in `main`. -/
def progN : Program Kind TS ℕ where
  periphs := [("temp", .sensor, .off), ("aux", .sensor, .off)]
  funs := [logData, wrap]
  main := .seq (.transition "temp" .idle) (.call "t" "wrap" (.val (.int 0)) "temp")

/-- The signatures after typing `progN`'s declarations in order. -/
noncomputable def sigsN : SigCtx Kind TS ℕ :=
  Function.update (Function.update (fun _ => none) "log_data" (some (logDataSig M)))
    "wrap" (some (wrapSig M))

/-- **Peripherals two calls up are still charged.**  `main` instantiates `wrap` at ambient
`b + bg(aux)`, and `wrap` passes it on to `log_data`; unfolding, `aux` is charged once per step of
`log_data` (`6·f·bg Off`), plus once for `main`'s own transition. -/
theorem progN_typed :
    ∃ Γ' Δ' Q F, Program.Typed P M progN (sigsN M) Γ' Δ' Q F ∧
      (∀ f b, Q f b = f * (tr M .off .idle + bg M .off + b) + f * M.valCost
                      + wrapCost M f (b + bg M .off)) ∧
      (∀ f b, wrapCost M f (b + bg M .off)
                = 2 * f * M.varCost + logDataCost M f b + 6 * f * bg M .off) := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨⟨?nodup, ?decls, ?main⟩, ?cost, ?unfold⟩
  case nodup => simp [progN, logData, wrap]
  case decls =>
    exact DeclsTyped.cons (logData_typed M) (DeclsTyped.cons (wrap_typed M) DeclsTyped.nil)
  case main =>
    dsimp only [progN]
    apply Typed.seq
    · apply Typed.transition (k := .sensor) (S := {.off})
      · simp [Program.initPCtx]
      · trivial
      · simp [P, rank]
    · apply Typed.call (sig := wrapSig M) (S := {.idle})
      · simp [sigsN]
      · exact HasTy.val
      · simp [Program.initPCtx]
      · simp [Program.initPCtx, wrapSig]
      · simp [wrapSig]
  case cost =>
    intro f b
    simp [wrapSig, bg, tr, Program.initPCtx, Expr.cost, CostModel.maxTrans, CostModel.maxBg]
    ring
  case unfold =>
    intro f b
    rw [wrapCost, logDataCost_ambient]
    ring

/-! ### 3. Branches of unequal duration: the summary is exact -/

/-- `fn branchy(x, temp) : (int, {Idle}) → (int, {Idle, Measure})`:
```
if x == 0 then { let a = 1; let a = 2; let a = 3 }   -- long (3 steps), no peripheral work
          else { transition(temp, Measure) }          -- short (1 step), expensive
ret := x
```
-/
def branchy : FunDecl Kind TS ℕ where
  name := "branchy"
  arg := "x"
  argTy := .int
  parg := "temp"
  pKind := .sensor
  sIn := {.idle}
  retTy := .int
  sOut := {.idle, .measure}
  body :=
    .ite (.binop .eq (.var "x") (.val (.int 0)))
      (.seq (.assign "a" (.val (.int 1))) (.seq (.assign "a" (.val (.int 2))) (.assign "a" (.val (.int 3)))))
      (.transition "temp" .measure)
  ret := .var "x"

/-- `branchy`'s summary.  The ambient background `b` stays *inside* the `max`: the long branch
pays it three times, the short branch once. -/
def branchyCost (f b : ℕ) : ℕ :=
  max (f * (M.valCost + bg M .idle + b) + (f * (M.valCost + bg M .idle + b)
          + f * (M.valCost + bg M .idle + b)))
      (f * (tr M .idle .measure + b))
  + f * (M.binopCost .eq + M.varCost + M.valCost + bg M .idle + b)
  + f * M.varCost

/-- `branchy`'s signature. -/
def branchySig : FunSig Kind TS ℕ where
  argTy := .int
  pKind := .sensor
  sIn := {.idle}
  retTy := .int
  sOut := {.idle, .measure}
  cost := branchyCost M
  clk := fun f => f

/-- **T-FunDecl for `branchy`: its summary is `branchyCost`**, with the ambient term inside the
`max` over branches. -/
theorem branchy_typed : FunDeclTyped P M (fun _ => none) branchy (branchySig M) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨{.idle} ∪ {.measure}, ?deriv, ?ret, ?out, ?sub, ?cost, ?clk⟩
  case deriv =>
    apply Typed.ite
    · exact HasTy.binop (HasTy.var (by simp [branchy])) HasTy.val BinOp.HasTy.eq
    · apply Typed.seq
      · apply Typed.assign HasTy.val
        simp [branchy]
      apply Typed.seq
      · apply Typed.assign HasTy.val
        simp [branchy]
      · apply Typed.assign HasTy.val
        simp [branchy]
    · apply Typed.transition (k := .sensor) (S := {.idle})
      · simp [branchy]
      · trivial
      · simp [P, rank]
  case ret => exact HasTy.var (by simp [branchy, TCtx.inter])
  case out => simp [branchy, PEntry.join]
  case sub => simp [branchy]
  case cost =>
    funext f b
    simp [branchySig, branchyCost, bg, tr, branchy, Expr.cost, CostModel.maxTrans,
      CostModel.maxBg, PEntry.bg]
  case clk => funext f; simp [branchySig]

end Cost

/-- A concrete cost model for the exactness comparison: only `Off` draws background power (5),
only `Idle → Measure` costs anything (10); all CPU costs are 0. -/
def M₀ : CostModel Kind TS ℕ where
  stateCost _ _ := 0
  bgCost _ s := if s = .off then 5 else 0
  transCost _ s s' := if s = .idle ∧ s' = .measure then 10 else 0
  varCost := 0
  valCost := 0
  binopCost _ := 0
  clockCost _ _ := 0
  spawnCost _ _ := 0

/-- **The summary is exact at branches of unequal duration.**  Call `branchy` at clock `1` while one
`Off` sensor is ambient (`b = 5`).  The long branch costs `3·5 = 15` (ambient only), the short
branch `10 + 5 = 15`, and evaluating the condition `5`: the summary is `20`.  Splitting local cost
from duration would give `max(0, 10) + max(3, 1)·5 + 5 = 30` — it charges the long branch's
duration *and* the short branch's transition, which no single run does. -/
theorem branchy_exact :
    branchyCost M₀ 1 5 = 20 ∧ max 0 10 + max 3 1 * 5 + 5 = 30 := by
  simp [branchyCost, M₀, bg, tr]

end ParametricityExample
