# Async soundness proof: design

Goal: `Program.MRun.soundnessA` — a program well typed under `TypedA`, run to completion on
the machine from clock `K₀`, costs at most `Q K₀ 0`, for every schedule and every sequence of
hardware steps.

Method: a typing relation on whole machine configurations carrying a potential `Φ` (remaining
typed budget), and a one-step lemma

```
CfgTyped c Φ  →  MStep c q c'  →  ∃ Φ', CfgTyped c' Φ' ∧ q + Φ' ≤ Φ
```

Summed along a run, cost `≤ Φ(initial) = Q K₀ 0`.

## Status

| piece | content | status |
|---|---|---|
| 1 | spawn-time charge of async bodies; `TypedA.shape_eq`, `TypedA.mono` (`AsyncSoundness.lean`) | done |
| 2 | control-stack and activation-stack typing; local / call / return steps pay | done |
| 3a | typing invariants (`AsyncInvariants.lean`) | done |
| 3b | configuration typing `CfgTyped` (`AsyncConfig.lean`) | done |
| 3c | every machine step pays: `CfgTyped.mstep`, runs: `CfgTyped.steps` | done |
| 3d | initial configuration typed; `Program.MRun.soundnessA` (`AsyncProgram.lean`) | done |
| — | lift the staging restriction (calls while threads are pending) | done |
| — | machine type safety: `CfgTyped.progress`, `Program.typeSafetyA` (`AsyncSafety.lean`) | done |
| — | accounting (A) on the machine: `Steps.accounting` (`AsyncAccounting.lean`) | done |
| — | slack (B1 + B2): `Program.slack_decompositionA` (`AsyncSlack.lean`) — wait / fallback / abandon items | done |
| — | slack (B3): per-handle charge items and branch / arm / clock items from local, call and return steps | done |
| — | residual itemized: spawn charge, waiting-tick charge, join / timeout clock, await-start rounding, callee continuations | done |
| — | B4 Parts 1–2: local necessity, the await gap (`Program.await_gap`), rounding (`AsyncNecessity.lean`) | done |
| — | B4 Part 3: never-schedule run attains the waiting charge up to a tick (`Steps.never_schedule`) | done |
| — | exact decomposition `Q K₀ 0 = q + Σ items` (every step lemma an equality) | done |

Everything listed as done builds with no `sorry`; `Program.MRun.soundnessA` and `Program.typeSafetyA` depend only on
`propext`, `Classical.choice`, `Quot.sound`.

## Rule decisions in force (rationale in `PAPER_DIFFERENCES.md`, section 5)

* **Spawn-time charge**: T-AsyncFun charges the body's summary `Q_a f (b + amb)` at the spawn
  (a closure paid for when created); `amb` is a declared bound on the window ambient, checked
  at T-Await (`cost(win ∖ p) ≤ amb`).
* **Signatures closed under hardware steps (option A)**: `FunDeclTypedA` requires `sIn`, `sOut`
  closed under `HWReach`.
* **No nested threads (permanent)**: T-AsyncFun requires `fz = false`.
* **Calls while threads are pending** (the staging restriction `Θ.IsEmpty` on T-Call was lifted
  2026-11-09): the callee must have a stable clock, so it is frozen and cannot spawn.  At most
  one activation of `main`'s stack has pending threads — the *spawner* — possibly suspended
  under a chain of frozen callees.
* **Count-down timers** in the machine (as in the paper): a waiting frame `awaitW tid id rem fb`
  holds the remaining budget; drain lowers it by `K` (truncated); waiting continues while
  `0 < rem`; timeout at `rem ≤ 0`.

## Configuration typing (as implemented, `AsyncConfig.lean`)

* **`CtlTyped P M Ψ C cl fz Γ Δ Θ ctl Γf Δf Θf Q F`** — a control stack typed entry by entry.
  * Entries: `cmd` (a `TypedA` derivation) and `awaitW` (a waiting frame, typed like
    T-Await-Timeout with allowance `waitAllow rem f = rem + f`, or `0` once the budget is spent).
  * Links between entries: `Γ` may forget, `Θ` may grow windows, and `Δ` only by
    **`PCtx.Widen P cl`**: unchanged, or joined with a same-shape sibling (the untaken branches),
    which must be closed under hardware steps when `cl` (thread stacks).
  * **Ceiling `C`**: a downward-closed predicate every visited context (and the final context)
    satisfies.  Proof invariant only; no effect on summaries.
* **Thread view `TView`** (`Θ Δ b H T` of the spawner) and **`TView.OK`** (a suspended spawner's
  agreement with the store under its view with the passed handle at `visit`, plus window shape,
  cover, captured handles, backward window bound).
* **`StackOK P M Ψ Am E as D Kc Φ X Θ Δ b bb tv Vs`** — a typed stack of activations (one
  segment), with its thread view `tv` and suspension ceiling `Vs`.
  * Indices: potential `Φ`, exit-clock bound `X`, the running activation's view `Θ Δ b`, and
    the bottom layer's ambient bound `bb`.
  * `base` (bottom activation) and `push` (a callee over a continuation clause for its caller,
    like a closure).  A callee inherits the thread view: its caller's, or (if the caller is the
    spawner) the caller's suspended view, whose agreement the callee layer keeps (`TView.OK`)
    while the callee and its own callees keep the passed device within `visit` (ceiling `Vs`).
  * `E : Option DevEnv`: `none` for `main`; for a thread, its device, envelope `V` and exit set
    `sOut`.  Each layer's ceiling is `DevEnv.Ceil E H`; the bottom layer's final context
    satisfies `DevEnv.Exit E H`.
  * Per-layer premises: agreement with the store (`ActOK`), window shape and cover, closure
    under hardware steps (thread stacks), captured handles (`ThreadCtx.CapOK`), what the layer
    sees (`DevEnv.Sees`: thread layers see only their device, through a live handle), frozen
    (thread layers).
* **`ThreadOK`** — one pending thread of the spawner (keyed on the thread view's `b H T`), by
  pool status:
  * pending: the body typed (frozen) from a hardware-closed start set containing the device's
    state, in the closure memory; contributes `Q_a K (b + amb)`;
  * running: exactly one segment, a `StackOK` under the envelope with bottom bound `b + amb`;
    contributes its potential;
  * done: device in a stable exit state; contributes `0`.
* **`CfgTyped c Φ`** — segments are thread segments over `main`'s; `main`'s stack typed with
  `E = none`; pending threads accounted for; distinct runtime ids; every thread segment owned by
  a running thread; every pool entry reached from a pending thread; waiting frames only at the
  head of `main`'s running activation, naming their thread's id; `Φ = Φm + Σ φ t`.

## Key invariants and where they come from

| invariant | lemma(s) |
|---|---|
| frozen clock while threads are pending, and in thread layers | `TypedA.frozen_clk`; `CtlTyped.step` / `StackOK.step` conclusions |
| window shape and cover; backward window bound `cost(win ∖ p) ≤ amb` | `TypedA.winShape`, `TypedA.winCover`, `CtlTyped.ambOK` |
| captured handles hold their envelope; distinct threads, distinct handles | `ThreadCtx.CapOK`, `TypedA.capOK` |
| thread contexts closed under hardware steps | `TypedA.hwClosed`, `CtlTyped.next_closed`, `PCtx.Widen` |
| a thread's device stays in its envelope | ceiling `DevEnv.Ceil`, `StackOK.dev_in_env` |
| a thread's ambient fits `b + amb` | `ActOK.thread_amb` (main's agreement + window cover + bound) |
| foreign device moves keep thread stacks typed | `StackOK.foreign` |
| captured device moves keep `main` typed (spawner running or suspended) | `StackOK.move_tv` |
| at an `await` or `async`, the running activation is the spawner (or nothing is pending) | `StackOK.await_tv`, `StackOK.async_tv` |

## Step cases (`CfgTyped.mstep`)

| machine step | lemma |
|---|---|
| local / call / return of `main` | `CfgTyped.step_main` (via `step_act`) |
| local / call / return of a running thread | `CfgTyped.step_thread` (via `step_act`) |
| `async` | `CfgTyped.async` |
| `awaitStart` / waiting tick / `awaitDone` | `CfgTyped.awaitStart`, `CfgTyped.awaitWait`, `CfgTyped.awaitDone` |
| `awaitTimeout`, `timeoutRunning` | `CfgTyped.timeout` (+ `timeout_shape`) |
| `preempt` / `threadDone` / `hw` | `CfgTyped.preempt`, `CfgTyped.threadDone`, `CfgTyped.hw` |
| draining after a ticked step | `CfgTyped.drain` |
| impossible in typed configurations | `main_alone`, `thread_seg`, `StackOK.no_async`, `StackOK.no_await` |

## 3d: the initial configuration (done)

`Program.MRun` runs `prog.initConfig K₀` (only `main`, empty pool, store `prog.initPeriphs`,
outer ambient `0`).

1. **Signature facts from declarations** (async analogues of `SlackProgram.lean`):
   `TypedA.weaken` (typing survives a larger signature context), `DeclsTypedA.sigsDerived`
   (`SigsDerivedA`), signature summaries monotone (`TypedA.mono` along the declarations), and
   `SigsClosedA` (from `FunDeclTypedA.sOutClosed`).
2. **`main`'s stack**: from `Program.TypedA`, `StackOK.base` with control stack
   `[.cmd prog.main]`, ambient bound `0`, empty thread context; agreement from
   `Program.initOK` (every handle visible, empty ambient).
3. **`CfgTyped.of_main`** gives `CfgTyped (prog.initConfig K₀) (Q K₀ 0)`.
4. **`Program.MRun.soundnessA`**: `CfgTyped.steps` along the run; potentials are `≥ 0`, so the
   cost is at most `Q K₀ 0`.

## Type safety (done, `AsyncSafety.lean`)

* `progress_head` / `StackOK.progress`: a typed stack is finished, steps its running
  activation (values from `HasTy.eval`, devices from `PeriphsOK.live` + `Corr.lookup`, `match`
  arms from `Arms.find?_of_mem`, callees from `SigsDerivedA`, returns from the return type), or
  is at a spawn / `await` / waiting frame.
* `CfgTyped.fresh`: an id above every pending thread's is free in the pool.
* `CfgTyped.progress`: a thread on top steps or finishes (`threadDone`); spawns, `await`s and
  waiting frames cannot occur in threads.  `main` on top: spawn (device + fresh id),
  `awaitStart` (the thread has an id by `await_tv` + `ThreadOK`), waiting frame (pending:
  wait or time out by the budget; done: join; running impossible with no thread segments).
* `Program.typeSafetyA`: preservation (`CfgTyped.steps`) + progress.

## Open items

None for the proof itself.  Possible extensions (async state inference, a tighter T-Await) are
listed in `TODO.md`.
