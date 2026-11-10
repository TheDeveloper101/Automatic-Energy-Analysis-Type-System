# Async soundness: design and status (updated 2026-11-09)

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
| — | lift the staging restriction | **next** |
| — | type safety, accounting and slack for async | later |

Everything listed as done builds with no `sorry`, under the staging restriction below.

## Rule decisions in force (see `TODO.md` for the full rationale)

* **Spawn-time charge**: T-AsyncFun charges the body's summary `Q_a f (b + amb)` at the spawn
  (a closure paid for when created); `amb` is a declared bound on the window ambient, checked
  at T-Await (`cost(win ∖ p) ≤ amb`).
* **Signatures closed under hardware steps (option A)**: `FunDeclTypedA` requires `sIn`, `sOut`
  closed under `HWReach`.
* **No nested threads (permanent)**: T-AsyncFun requires `fz = false`.
* **STAGING RESTRICTION (temporary)**: T-Call requires `Θ.IsEmpty`.  Consequence used
  throughout: every pending or running thread belongs to the running activation of `main`'s
  segment.
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
* **`StackOK P M Ψ Am E as D Kc Φ X Θ Δ b bb`** — a typed stack of activations (one segment).
  * Indices: potential `Φ`, exit-clock bound `X`, the running activation's view `Θ Δ b`, and
    the bottom layer's ambient bound `bb`.
  * `base` (bottom activation) and `push` (a callee over a continuation clause for its caller,
    like a closure).
  * `E : Option DevEnv`: `none` for `main`; for a thread, its device, envelope `V` and exit set
    `sOut`.  Each layer's ceiling is `DevEnv.Ceil E H`; the bottom layer's final context
    satisfies `DevEnv.Exit E H`.
  * Per-layer premises: agreement with the store (`ActOK`), window shape and cover, closure
    under hardware steps (thread stacks), captured handles (`ThreadCtx.CapOK`), what the layer
    sees (`DevEnv.Sees`: thread layers see only their device, through a live handle), frozen
    (thread layers).
* **`ThreadOK`** — one pending thread of `main`'s running activation, by pool status:
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
| captured device moves keep `main` typed | `StackOK.move` |

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

## Open items

* **Lift the staging restriction.**  Calls while a thread is pending bring back the case of a
  spawner suspended inside a call: its parameter's device is in the callee's visited states,
  hence in `visit`, which the window observes at the call.  `StackOK.push` currently requires
  the caller's view to have no pending threads, and `StackOK.step` uses "no threads ⇒ local
  step" in several places; both need generalizing.  Some per-layer invariants may simplify then.
* **Future refactor (more principled than links):** drop `PCtx.Widen` links and retype the rest
  of the program from a branch's own output with a *narrowing lemma* (typed from `Δ'`,
  `Δ ⊑ Δ'` closed ⇒ typed from `Δ` with smaller outputs, windows and summaries).  The
  configuration would then be typed by an actual derivation chain, and the potential would be
  tighter after branches.  Costs: a mutual lemma over every `TypedA` / `ArmsTypedA` rule;
  `async` narrows `W_p`, hence the thread's `V` (breaks `SameIds`, changes `ThreadOK`); closure of
  the narrowed context remains a side condition.
* **Later:** type safety for the machine (every non-final typed configuration can step);
  embedding `Typed → TypedA`; accounting and slack for async (via "an async is a closure called
  at the spawn, at the window ambient").
