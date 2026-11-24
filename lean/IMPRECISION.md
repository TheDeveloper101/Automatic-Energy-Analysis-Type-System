# Where the cost bounds are not tight

Soundness (`Heliod/Soundness.lean`) says every run costs **at most** the typing's summary
`Q f b`. This note records where, and why, a summary can be strictly larger than the cost of
any run, and what is proved about it: the slack decomposition (every loss is itemized) and local
attainment (each single charge is the worst case of something the typing allows).

The synchronous rules come first; the async rules are in the last section. Rule changes relative
to the paper are listed in `PAPER_DIFFERENCES.md`. Statements below marked *(argued)* are
explanations, not Lean theorems.

## Three notions of "the bound is attained"

| notion | attained by … |
|---|---|
| **trace-tight** | some real execution (conditions evaluated for real) |
| **path-tight** | some control-flow path: each `if` may take either branch, whatever its condition evaluates to; costs do not depend on values |
| **segment-tight** | for a code segment on its own: some path through the segment, from some state consistent with the typing context at the segment's start |

*(Argued.)*
* Trace-tightness is out of reach for any static analysis that does not track correlations
  between conditions (Example A).
* Path-tightness fails where the context holds several possible states or clocks:
  * after a merge (Examples B, C);
  * from several possible input states (Example D).
* No theorem states segment-tightness. What is proved:
  * **Local attainment:** each single typed charge is attained by some state consistent with
    the context.
  * **The slack decomposition:** it names every place where the bound loses precision.

## Example A — correlated conditions (not trace-tight)

```
if e { transition(p, A); let flag = true } else { let flag = false };   -- p starts in I
if flag { skip } else { transition(p, B) }
```

* Each `if` is charged its costlier branch, so the bound contains `tr(I, A)` and a transition
  to `B`.
* No execution performs both transitions: the second happens only when the first did not.
* The control-flow path that takes *then* at the first `if` and *else* at the second does
  perform both.
* After the first `if`, `p ∈ {A, I}` (a merge, as in B). The path is therefore charged exactly
  only if that merge loses nothing there, e.g. when `tr(A, B) ≥ tr(I, B)` and `bg A ≥ bg I`.

With such costs the bound is path-tight but not trace-tight. Avoiding the loss would need a
relational analysis of the conditions (`flag` ↔ which branch ran).

## Example B — state merge after a branch (not path-tight)

```
if e { transition(p, A) } else { transition(p, B) };   -- p starts in I
transition(p, C)
```

Take `tr(I,A) = 10, tr(I,B) = 0, tr(A,C) = 0, tr(B,C) = 10`, with all other costs 0:

* The `if` is charged `max(10, 0) = 10`. Taking the max of the branches loses nothing here.
* After the `if` the typing knows only `p ∈ {A, B}` (the join `Δ₁ ∪ Δ₂`), so
  `transition(p, C)` is charged `max(tr(A,C), tr(B,C)) = 10`.
* The bound is `20`, while the two paths cost `10 + 0` and `0 + 10`.

The loss is not in the `max` but in **sequencing after the merge**: the merged state forgets
which branch produced it.

## Example C — clock merge after a branch (not path-tight)

```
if e { <expensive work>; clock(1) } else { clock(100) };
<work>
```

The summary charges the first part at the expensive branch's cost and the following work at
the faster clock `max(1, 100)`; no path is both. This is the same mechanism as B, with the exit
clock `F = max(F₁, F₂)` playing the role of the merged state.

## Example D — several possible input states (not path-tight)

A function typed once for `p ∈ {A, B}`:

```
let x = 1;            -- charges p's background at its worst state: max(bg A, bg B)
transition(p, C)      -- charges the worst transition:            max(tr(A,C), tr(B,C))
```

Take `bg A = 10, tr(A,C) = 0, bg B = 0, tr(B,C) = 10`, with all other costs 0. The bound is `20`,
while starting in `A` costs `10` and starting in `B` costs `10`. Each step's worst case is taken
independently, so the two maxima can come from different states. In the checking system this
affects every function declared for several input states (e.g. the writeup's `log_data`,
`{Idle, Measure}`).

The same happens *inside* a single `if`, because it is itself two charges in sequence:

```
if e { transition(p, C) } else { skip }     -- p ∈ {A, B}
```

It is charged `max(tr(A,C), tr(B,C), 0)` for the branches plus `f·max(bg A, bg B)` for the step
that evaluates the condition: again two maxima that may come from different states.

In the checking system a call is affected the same way: it charges its argument step at `p`'s
worst background, then the callee's summary, which was derived for the callee's own worst
declared input. `match p` is the exception (after the refinement below): its step and its arms
all see `p` narrowed to the arm's state.

## What would remove the losses

* **D at function boundaries is removed by state inference** (`Heliod/Inference.lean`).
  * Inline typing (`TypedI`) types a callee's body from the caller's actual states rather than
    from the declared `sIn`. So a function declared for `{A, B}` but called with `p ∈ {A}` is
    charged as if declared for `{A}` (`Examples/LogDataInline.lean`).
  * `Program.Typed.precision`: inline typing is never worse than checking.
  * D *inside* a body (several possible states at one step) remains.
* B, C and the rest of D come from summaries being functions of the clock and the ambient
  background only. *(Argued.)* Summaries indexed by the state, with branches kept apart instead
  of joined (a disjunctive, path-sensitive context), would remove them, at the price of
  exponential blow-up in general.
* Path-insensitivity also means a function has no largest set of entry states in general
  (`Examples/EntrySets.lean`).
* A needs relational reasoning about data and is out of scope.

## Two rule imprecisions we fixed in `match`

* **The `match` step's background.**
  * An earlier version of the rule charged the step outside the max over arms, with `p` at its
    worst state over the whole set: `max_arms(Q_arm) + f·(cost(Δ) + b)`.
  * The arm winning the max may be for a state with lower background, and then even a `match`
    on its own is not attained by any path.
  * The current rule charges the step inside each arm, with `p` narrowed to the arm's state:
    `max_arms(Q_arm + f·(cost(Δ[p : {sᵢ}]) + b))`.
  * It is never larger (an easy argument), and it is proved sound (the `match` step runs with
    `p` in state `sᵢ`).
* **Only reachable arms (`stᵢ ∈ Δ(p)`) are typed and charged.** The paper's rule charges every
  arm.
* **Not enforced: distinct arm states.** A second arm for the same state is typed and enters the
  max although it never runs (the semantics takes the first match). Only `Typed.pinned` below
  assumes distinct arms.

## The slack decomposition (proved: `Heliod/Slack.lean`, `Heliod/SlackProgram.lean`)

Instead of claiming the bound is tight under restrictions, we itemize the over-approximation.
**Along any control-flow path (`Path`), or any real execution (`Eval`), the summary equals the
path's cost plus a list of local slack terms, each of a known kind with an explicit formula:**

```
Q K (bg A) = cost(path) + Σ δᵢ        (slack_decomposition, Eval.slack_decomposition)
```

The command-level theorems assume valid signatures derived from declarations (`SigsValid`,
`SigsDerived`). The program-level versions discharge both.

| kind | recorded at | `δ` = typed − actual |
|---|---|---|
| `state` | every charged step | worst-case charge over the context `Δ` there, minus the charge at the actual state `S` |
| `branch` | every `if` | `max(Q₁, Q₂)` minus the summary of the branch taken |
| `arm` | every `match` | max over reachable arms minus the part containing the arm that runs |
| `clock` | after `c₁` in `c₁; c₂`, and before a return | rest charged at the typed exit clock minus at the actual one |
| `ambient` | every call | callee's summary at the caller's typed background for its other peripherals, minus at their actual background |
| `signature` | every call | signature's summary minus the callee's derived summary (0 for signatures derived by T-FunDecl) |

How the examples appear:
* A: `branch` terms on a real execution.
* B: the merge produces a multi-state context; the trailing transition gets a `state` term.
* C: a `clock` term.
* D: two `state` terms; no single starting state makes both zero.

**Necessity** (`Heliod/Necessity.lean`):
* *Local attainment* (`PCtx.bg_attained`, `PCtx.trans_attained`; contexts with non-empty state
  sets): each typed background or transition charge is the actual charge for *some* runtime
  state consistent with the context at that point. Together with the soundness lemmas, the typed
  charge is exactly the maximum of the actual charge over the states the context allows. An
  analysis that knows only `Δ` at that point cannot charge less.
* *No uncertainty, no state slack* (`PeriphsOK.bg_eq_of_pinned`, `maxTrans_singleton`): if `Δ`
  pins down every peripheral, typed and actual charges coincide.
* *Origin of uncertainty* (`Typed.pinned`): when every signature in `Ψ` has a single output
  state, a command without `if` whose `match`es have distinct arm states, typed from a pinned
  context, ends pinned. So multi-state contexts, the only cause of `state` slack, come only from:
  * multi-state function inputs;
  * merges after an `if`;
  * a `match` with repeated arm states;
  * signatures with several output states.
* *(Argued.)*
  * `branch` / `arm` terms come from not knowing which branch runs (path insensitivity).
  * `clock` terms come from clock merges.
  * `ambient` terms come from uncertainty about the caller's other peripherals (a `state`-type
    term propagated into the call).

**Exactness** (`SlackRun.exact`): with no slack, the bound equals the cost.

**Whole programs** (`Program.slack_decomposition` along any control-flow path,
`Program.Eval.slack_decomposition` for real runs; `Heliod/SlackProgram.lean`; assuming `M.WF`):
for a well-typed program from clock `K₀`, `Q K₀ 0 = cost + Σ δᵢ`. Programs start pinned
(`Program.initPinned`: each handle is declared with one initial state), so all `state` slack in a
program run comes from the sources listed under *Origin of uncertainty*.

## Async: the slack decomposition on the machine

(`Heliod/AsyncSlack.lean`, `Heliod/AsyncNecessity.lean`.) For any complete machine run
(`Program.MRun`) of a `TypedA`-typed program, under any schedule and hardware behaviour, assuming
`M.WF` and `P.WF`:

```
Q K₀ 0 = cost(run) + Σ items        (Program.slack_decompositionA — exact, no residual)
```

Each item is released by one machine step and satisfies a specification by kind (`ASlack.Spec`).
For the charge kinds the specification is "typed charge minus actual charge". The specifications
of `wait` (some multiple of the frame's typed rate) and `clock` (a difference `g f₂ − g f₁` for
some monotone `g`) are weak.

| kind | released by | item |
|---|---|---|
| `state`, `transition`, `branch`, `arm`, `clock`, `ambient` | local, call, return and spawn steps and waiting ticks; `clock` also after a join or timeout | like the sync kinds, but per handle, and `ambient` per step rather than per call |
| `envelope` | main-thread steps | a captured handle charged at `maxBg V` minus its actual background |
| `window` | thread steps | the declared window bound `amb` minus the actual ambient |
| `spawn` | the spawn step | worst spawn cost minus the actual one |
| `wait` | `awaitStart` (only when the timeout is `0`), waiting ticks, a thread running while `main` waits, the join | unused waiting allowance, as a multiple of the frame's typed rate |
| `fallback` | the join | the summary of the fallback that did not run |
| `abandon` | a timeout | the timed-out thread's remaining reserved budget |

**What is proved about necessity** (`AsyncNecessity.lean`):
* *Charge items.*
  * For `state`, `envelope`, `transition` and `spawn` items, the typed maximum over the item's
    state set is the actual cost of some state in that set (`LFact.charge_attained`).
  * `state` / `envelope` items are zero when the device is in a worst state (under a strong
    hypothesis, `LFact.charge_zero_of_worst`) or when the set is a single state
    (`LFact.charge_zero_of_pinned`).
  * `ambient` / `window` items are zero when the declared bound is tight
    (`LFact.amb_zero_of_tight`).
* *Some fallback or abandon item at every await.* In a complete run of a typed program, after
  any configuration where `main` waits, the rest of the run releases some `fallback` or
  `abandon` item, and the run's cost plus that item is within the bound (`Program.await_gap`).
  The item may be zero (e.g. a free fallback).
* *Rounding of the allowance* (cost domains with additive cancellation,
  `[AddLeftReflectLE R]`): the step that exhausts a waiting budget `rem > 0` leaves `rem` of the
  allowance unused (`waitAllow_exhaust_pos`).
  * This is an identity about the allowance `waitAllow`. It is linked to the released `wait`
    items only through the proofs of the step lemmas, since the item specification does not
    record the formula.
  * The released amount is that leftover times the frame's rate, so it is zero when the rate is
    zero.
* *A schedule that never runs the thread* (Archimedean cost domain, positive clock, `main` alone
  waiting on a pending thread): there is a run that only waits, `m` ticks with
  `rem ≤ m·K ≤ rem + K`, then times out and ends about to run the fallback, the thread never
  having run (`Steps.never_schedule`).
  * If the per-tick charge equalled the frame's typed rate `w`, that waiting would cost between
    `rem·w` and `(rem + K)·w`, so T-Await's waiting charge would be attained up to one tick
    (`waiting_cost_bounds`).
  * That theorem is only the arithmetic. The equality of the rates is not proved, and the run
    is not linked to its slack items.

**What T-Await over-counts** *(argued)*. Spawn to await costs at most `Q_a + (n + f)·w + Q_fb`.
This sum is nearly attained by the following run: wait most of the budget, run the body until
just before its last step, time out, then run the fallback. So a `max(join, timeout)` form would
be unsound. The over-count is:
* the overlap of the body's running time with the waiting budget (about `d·w` for a body of
  duration `d`; these are `wait` items released while a thread runs);
* the cut-off last step;
* the rounding of the last tick (the rounding of the allowance is proved; see above).

Removing the overlap would need a lower bound on the body's duration (`TODO.md`, open items).
