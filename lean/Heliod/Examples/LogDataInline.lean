import Heliod.Inference
import Heliod.Examples.LogData

/-!
# Worked example: `log_data` under inline typing (lazy concretization)

The writeup's point about state inference: `log_data` accepts `temp ∈ {Idle, Measure}`, but
`main` calls it with `temp` in `Idle`, so its entry transition `transition(temp, Measure)`
should be charged `C(temp:(Idle, Measure))` — the paper solves `α₀ = Idle` at the call site.
The checking system (`Heliod.Examples.LogData`) charges the worst declared case,
`max(tr Idle Measure, tr Measure Measure)`.

Here the same program is typed with `TypedI`: the call types `log_data`'s body from `main`'s
current `{Idle}`, so the transition is charged `tr Idle Measure` (`logDataCostIdle`), and
nothing else changes.  Then:
* `main_inline`: the inline derivation of `main`, with its exact summary;
* `inline_le_check`: it is at most the checking summary (an instance of
  `Program.Typed.precision`, here by direct comparison);
* `cost_bound`: by `soundnessI`, running the program at clock `1` costs at most
  `expectedCostIdle`.
-/

namespace LogDataExample

section Inline
variable (M : CostModel Kind TS ℕ)

/-- `log_data`'s cost when entered with `temp` in `Idle`: `logDataCost` with the entry
transition charged from `Idle` alone. -/
def logDataCostIdle (f b : ℕ) : ℕ :=
  -- transition(temp, Measure) from {Idle}
  f * (tr M .idle .measure + b)
  -- the rest exactly as in `logDataCost`
  + f * (M.valCost + bg M .measure + b)
  + f * (M.valCost + bg M .measure + b)
  + f * (M.valCost + bg M .measure + b)
  + f * (M.binopCost .eq + M.varCost + M.valCost + bg M .measure + b)
  + f * (tr M .measure .off + b)
  + f * (M.varCost + bg M .off + b)

/-- Entering from `Idle` costs no more than the worst declared entry state. -/
theorem logDataCostIdle_le (f b : ℕ) : logDataCostIdle M f b ≤ logDataCost M f b := by
  unfold logDataCostIdle logDataCost
  gcongr
  exact le_max_left _ _

/-- The program's whole cost at clock `1`, inline: `expectedCost` with `log_data` charged from
`Idle`. -/
def expectedCostIdle : ℕ :=
  (tr M .off .idle + bg M .off)
  + (M.valCost + bg M .idle + bg M .off)
  + logDataCostIdle M 1 (bg M .off)

/-- **`main` is inline-typed, charging `log_data` at `Idle`.**  The call types `log_data`'s body
from `temp ∈ {Idle}` (the state `main` has just put it in); the summary is `main`'s transition and
argument plus `logDataCostIdle` with `aux`'s background ambient.  The clock is unchanged and
`temp` ends `Off`. -/
theorem main_inline :
    ∃ Γ' Δ' Q F, TypedI P M prog.fctx TCtx.empty prog.initPCtx prog.main Γ' Δ' Q F ∧
      (∀ f b, Q f b = f * (tr M .off .idle + bg M .off + b)
                      + f * (M.valCost + bg M .idle + bg M .off + b)
                      + logDataCostIdle M f (b + bg M .off)) ∧
      (∀ f, F f = f) ∧ Δ' "temp" = .live .sensor {.off} := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨?deriv, ?cost, ?clk, ?fin⟩
  case deriv =>
    dsimp only [prog]
    apply TypedI.seq
    · -- main: transition(temp, Idle) from Off
      apply TypedI.transition (k := .sensor) (S := {.off})
      · simp [Program.initPCtx]
      · trivial
      · simp [P, rank]
    · -- main: let t = log_data(0, temp), the body typed from temp ∈ {Idle}
      apply TypedI.call (d := logData) (S := {.idle}) (S' := {.off})
      · simp [Program.fctx, logData]
      · exact HasTy.val
      · simp [Program.initPCtx]
      · simp [Program.initPCtx, logData]
      · dsimp only [logData]
        apply TypedI.seq
        · -- transition(temp, Measure) from {Idle}
          apply TypedI.transition (k := .sensor) (S := {.idle})
          · simp
          · trivial
          · simp [P, rank]
        apply TypedI.seq
        · apply TypedI.assign HasTy.val
          simp
        apply TypedI.seq
        · apply TypedI.assign HasTy.val
          simp
        apply TypedI.seq
        · apply TypedI.ite
          · exact HasTy.binop (HasTy.var (by simp [Val.ty])) HasTy.val BinOp.HasTy.eq
          · apply TypedI.assign HasTy.val
            simp
          · exact TypedI.skip
        · apply TypedI.downgrade (k := .sensor) (S := {.measure})
          · simp
          · trivial
          · simp [P]
      · exact HasTy.var (by simp [logData, Val.ty, TCtx.inter])
      · simp [logData]
  case cost =>
    intro f b
    simp [logDataCostIdle, bg, tr, logData, Program.initPCtx, Expr.cost, CostModel.maxTrans,
      CostModel.maxBg, PEntry.bg]
    ring
  case clk => intro f; exact max_self f
  case fin => simp [logData]

/-- **Inline is never worse here**: `main`'s inline summary is at most its checking summary
(`prog_typed`), pointwise — the only difference is `log_data`'s entry transition. -/
theorem inline_le_check (f b : ℕ) :
    f * (tr M .off .idle + bg M .off + b) + f * (M.valCost + bg M .idle + bg M .off + b)
        + logDataCostIdle M f (b + bg M .off)
      ≤ f * (tr M .off .idle + bg M .off + b) + f * (M.valCost + bg M .idle + bg M .off + b)
        + logDataCost M f (b + bg M .off) :=
  add_le_add le_rfl (logDataCostIdle_le M f _)

/-- **Cost bound, inline.**  Any run of the program from clock `1` costs at most
`expectedCostIdle` — `log_data`'s entry transition charged from `Idle`, as the writeup's
inference predicts — by `soundnessI` on `main_inline`. -/
theorem cost_bound (hM : M.WF) {σ' S' q' K'} (he : prog.Eval M 1 σ' S' q' K') :
    q' ≤ expectedCostIdle M := by
  obtain ⟨Γ', Δ', Q, F, ht, hQ, -, -⟩ := main_inline M
  have h := (soundnessI hM ht he (fun _ _ hx => by simp [TCtx.empty] at hx)
    (Program.initOK prog)).1
  simp only [ambBg, Multiset.map_zero, Multiset.sum_zero, hQ] at h
  simpa [expectedCostIdle] using h

end Inline

end LogDataExample
