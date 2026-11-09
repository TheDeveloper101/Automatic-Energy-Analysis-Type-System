# Where the cost bounds are not tight — notes for the paper

Soundness (`Heliod/Soundness.lean`) says every run costs **at most** the typing's summary
`Q f b`.  This note records where, and why, a summary can be strictly larger than the cost of
any run, and what the tightness theorem (accounting part B) claims instead.  Worked out with
the user on 2026-11-08.

## Three notions of "the bound is attained"

| notion | attained by … |
|---|---|
| **trace-tight** | some real execution (conditions evaluated for real) |
| **path-tight** | some control-flow path: each `if` may take either branch, whatever its condition evaluates to; costs do not depend on values |
| **segment-tight** | for a code segment on its own: some path through the segment, from some state consistent with the typing context at the segment's start |

Trace-tightness is out of reach for any static analysis that does not track correlations
between conditions (example A).  Path-tightness fails exactly where code follows a *merge* of
states or clocks (examples B, C, D).  Segment-tightness is what the tightness theorem
establishes: precision is lost only at those merge points.

## Example A — correlated conditions (not trace-tight, but path-tight)

```
if p.state = Idle { transition(p, Rx); flag := true } else { skip };
if !flag          { transition(p, Tx) }               else { skip }
```

Each `if` is charged its worse branch, a transition, so the bound contains both transitions.
No execution performs both: the second transition happens only when the first did not.  The
control-flow path *then; then* does take both, so the bound is path-tight.  Avoiding this loss
would need a relational analysis of the conditions (`flag` ↔ the state of `p`).

## Example B — state merge after a branch (not path-tight)

```
if e { transition(p, A) } else { transition(p, B) };   -- p starts in I
transition(p, C)
```

With `tr(I,A) = 10, tr(I,B) = 0, tr(A,C) = 0, tr(B,C) = 10` (other costs 0):

* the `if` is charged `max(10, 0) = 10` — taking the max of the branches is exact;
* after the `if` the typing knows only `p ∈ {A, B}` (the join `Δ₁ ∪ Δ₂`), so
  `transition(p, C)` is charged `max(tr(A,C), tr(B,C)) = 10`;
* bound `20`, while the two paths cost `10 + 0` and `0 + 10`.

The loss is not in the `max` but in **sequencing after the merge**: the merged state forgets
which branch produced it.

## Example C — clock merge after a branch (not path-tight)

```
if e { <expensive work>; clock(1) } else { clock(100) };
<work>
```

The summary charges the first part at the expensive branch's cost and the following work at
the faster clock `max(1, 100)`; no path is both.  Same mechanism as B, with the exit clock
`F = max(F₁, F₂)` playing the role of the merged state.

## Example D — several possible input states (not path-tight)

A function typed once for `p ∈ {A, B}`:

```
let x = 1;            -- charges p's background at its worst state: max(bg A, bg B)
transition(p, C)      -- charges the worst transition:            max(tr(A,C), tr(B,C))
```

With `bg A = 10, tr(A,C) = 0, bg B = 0, tr(B,C) = 10`: bound `20`, while starting in `A` costs
`10` and starting in `B` costs `10`.  Each step's worst case is taken independently, so the two
maxima can come from different states.  This affects every function typed once for several
input states (e.g. the writeup's `log_data`, `{Idle, Measure}`).

The same happens *inside* a single `if` or call, because each is itself two charges in
sequence:

```
if e { transition(p, C) } else { skip }     -- p ∈ {A, B}
```

is charged `max(tr(A,C), tr(B,C), 0)` for the branches plus `f·max(bg A, bg B)` for the step
that evaluates the condition — again two maxima that may come from different states.  A call
charges its argument step at `p`'s worst background and then the callee's summary, which was
derived for the callee's own worst input.  `match p` is the exception (after the refinement
below): its step and its arms all see `p` narrowed to the arm's state.

## What would remove the losses

* B, C, D come from summaries being functions of the clock and the ambient background only.
  Summaries indexed by the input state (and branches kept apart instead of joined — a
  disjunctive context) would remove them, at the price of exponential blow-up in general.
  Possibly the place for the state-inference system with state variables `α` (roadmap step 5).
* A needs relational reasoning about data and is out of scope.

## A rule imprecision we fixed: the `match` step's background

The earlier T-Match charged the `match` step's own background outside the max over arms,
with `p` at its worst state over the whole set: `max_arms(Q_arm) + f·(cost(Δ) + b)`.  The arm
winning the max may be for a state whose background is lower, so even a `match` on its own was
not attained by any path.  The refined rule charges the step inside each arm, with `p` narrowed
to the arm's state: `max_arms(Q_arm + f·(cost(Δ[p : {sᵢ}]) + b))`.  It is never larger and is
still sound (the `match` step runs with `p` in state `sᵢ`).

Similarly, an earlier refinement types and charges only reachable arms (`stᵢ ∈ Δ(p)`); the
paper's rule charges every arm.  A remaining well-formedness assumption: **match arms have
distinct states** — otherwise a shadowed second arm for the same state is typed and enters the
max although it can never run.


## The slack decomposition (proved, `Heliod/Slack.lean`, `Heliod/Necessity.lean`)

Instead of claiming the bound is tight under restrictions, we bound the over-approximation
itself: **along any control-flow path, or any real execution, the summary equals the path's
cost plus a list of local slack terms, each of a known kind with an explicit formula.**

```
Q K (bg A) = cost(path) + Σ δᵢ        (slack_decomposition, Eval.slack_decomposition)
```

| kind | recorded at | `δ` = typed − actual |
|---|---|---|
| `state` | every charged step | worst-case charge over the context `Δ` there, minus the charge at the actual state `S` |
| `branch` | every `if` | `max(Q₁, Q₂)` minus the summary of the branch taken |
| `arm` | every `match` | max over reachable arms minus the part containing the arm that runs |
| `clock` | after `c₁` in `c₁; c₂`, and before a return | rest charged at the typed exit clock minus at the actual one |
| `ambient` | every call | callee's summary at the caller's typed background for its other peripherals, minus at their actual background |
| `signature` | every call | signature's summary minus the callee's derived summary (0 for signatures derived by T-FunDecl) |

How the examples appear:
* A: `branch` terms on a real execution; zero on the matching control-flow path.
* B: the merge produces a multi-state context; the trailing transition gets a `state` term.
* C: a `clock` term.
* D: two `state` terms; no single starting state makes both zero.

**Only as much as necessary** (`Heliod/Necessity.lean`):
* *Local attainment* — each typed charge is the actual charge for *some* runtime state
  consistent with the context at that point (`PCtx.bg_attained`, `PCtx.trans_attained`): the
  typed charge is exactly the maximum of the actual charge over the states the context allows.
  An analysis that knows only `Δ` at that point cannot charge less.
* *No uncertainty, no state slack* — if `Δ` pins down every peripheral, typed and actual
  charges coincide (`PeriphsOK.bg_eq_of_pinned`, `maxTrans_singleton`).
* *Origin of uncertainty* (`Typed.pinned`) — from a pinned context, a command without `if` and
  with distinct match arms, calling only functions with single output states, ends pinned.  So
  multi-state contexts (the only cause of `state` slack) come only from multi-state function
  inputs, merges after branches, or multi-state call outputs.
* `branch`/`arm` terms come from not knowing which branch runs (path insensitivity); `clock`
  terms only from clock merges; `ambient` terms from uncertainty about the caller's other
  peripherals (a `state`-type term propagated into the call).

**Exactness corollary** (`SlackRun.exact`): with no slack, the bound is the cost.

**Whole programs** (`Program.slack_decomposition`, `Heliod/SlackProgram.lean`): a well-typed
program run from clock `K₀` has `Q K₀ 0 = cost + Σ δᵢ`.  Programs start pinned
(`Program.initPinned`: each handle is declared with one initial state), so all `state` slack in a
program run comes from merges, multi-state function inputs, or multi-state call outputs.
