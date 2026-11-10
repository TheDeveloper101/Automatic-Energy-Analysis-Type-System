# Heliod Lean mechanization: status

Everything below builds with no `sorry`. The main theorems depend only on `propext`,
`Classical.choice` and `Quot.sound`. The default target (`lake build`) covers every file under
`Heliod/`, via the glob in `lakefile.toml`.

Other documents:
* `PAPER_DIFFERENCES.md`: every departure from `typing.tex` / `writeup.tex`, for the paper
  author.
* `IMPRECISION.md`: where the bounds are not tight, and the slack decomposition.
* `ASYNC_PROOF_PLAN.md`: the design of the async soundness proof (configuration typing).

## Build workflow

Edit in OneDrive, and build on the WSL mirror with `scripts/mirror-build.sh` (about 25 s, versus
about 7 min per file on OneDrive). With a file argument it runs `lake build Heliod.X`, which
rebuilds stale dependencies.

## What is proved

| area | files | main results |
|---|---|---|
| definitions | `Platform`, `Syntax`, `CostModel`, `Contexts` | `Platform.WF`, `CostModel.WF`, contexts `Γ` / `Δ`, `cost(Δ)` |
| checking typing (sync) | `Typing` | `Typed` / `ArmsTyped`, `FunDeclTyped`, `DeclsTyped`, `Program.Typed` |
| big-step semantics (sync) | `Semantics` | `Eval`, `Program.Eval` |
| sync soundness and termination | `Soundness` | `soundness`, `eval_total`, `Program.sigsValid`, `Program.soundness` |
| sync accounting | `Accounting` | `Eval.whole_run_accounting`: every event charges each device once |
| sync slack | `Slack`, `Necessity`, `SlackProgram` | `Program.slack_decomposition` (`Q K₀ 0 = cost + Σ δ`), local attainment, `Typed.pinned` |
| async typing | `AsyncTyping` | `TypedA` / `ArmsTypedA`, `FunDeclTypedA`, `Program.TypedA` |
| machine | `Machine`, `Adequacy` | small-step machine; machine ↔ `Eval` for the sync fragment, `Program.MRun.soundness` |
| async soundness | `AsyncSoundness`, `AsyncInvariants`, `AsyncConfig`, `AsyncProgram` | `CfgTyped.steps`, **`Program.MRun.soundnessA`** (every schedule and hardware behaviour) |
| async type safety | `AsyncSafety` | **`Program.typeSafetyA`** |
| async accounting | `AsyncAccounting` | `Steps.accounting` |
| async slack | `AsyncSlack`, `AsyncNecessity` | **`Program.slack_decompositionA`** (exact: `Q K₀ 0 = q + Σ items`), `Program.await_gap`, `Steps.never_schedule`, `waiting_cost_bounds` |
| sync → async | `Embed` | `Typed.toA`, `Program.Typed.toA`, `Program.Typed.typeSafety` (for programs whose declared states are stable) |
| state inference (sync) | `Inference` | `Typed.narrow`, `TypedI` + `soundnessI`, `Typed.toI` / `Program.Typed.precision`, `Accepts`, `entrySet`, `Program.Typed.accepts` |

Examples (`Heliod/Examples/`):

| file | what it shows |
|---|---|
| `LogData` | the writeup's `log_data`: closed-form summary, typed once and instantiated at the caller's ambient |
| `Match` | `match` with arms ending in different states |
| `Parametricity` | ambient enters linearly; the same function in different callers; ambient two calls deep; branches of unequal duration (`branchy_exact`) |
| `Async` | radio send while measuring; `cost_bound` via `soundnessA`; the fallback must handle the already-finished state |
| `LogDataInline` | `log_data` called from `Idle` is charged from `Idle` (lazy concretization) |
| `EntrySets` | acceptance is not closed under union: no largest entry set |

## Open items

Possible next steps, none in progress:

* **Async state inference**: an inline version of `TypedA`.
* **Path-sensitive typing**: would make accepted entry sets closed under union
  (`PAPER_DIFFERENCES.md` section 6.4).
* **T-Await tightening**: charge waiting `(n − d_min + f)·w`, given a lower bound `d_min` on the
  body's duration. This needs a new judgment component and a potential invariant for the
  thread's guaranteed running time. Not planned unless await-heavy programs need tight bounds.
* **`Steps.never_schedule`** is a machine-level existence result. It is not yet connected to the
  slack items of that run, because the items' specifications do not record the tick formula.
* **Example exercising `clock`**: summaries parametric in the clock, `clockCost`.
* **Small cleanups:**
  * `eval_total` takes `M.WF` only because its `seq` case reuses `soundness`; a cost-free
    preservation lemma would remove it.
  * `Program.eval_total` (whole programs terminate) is immediate from `eval_total`,
    `Program.sigsValid` and `Program.initOK`.

Decided against:

* **Narrowing refactor of `TypedA`** (replacing the `PCtx.Widen` links in configuration typing
  by narrowing). It would change no result and only move state slack into `branch` items.
* **A `max(join, timeout)` form for T-Await.** It is unsound (`PAPER_DIFFERENCES.md`
  section 5.5).
