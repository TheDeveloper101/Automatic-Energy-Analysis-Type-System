# Heliod: how the Lean mechanization differs from the paper

This document lists every place where the Lean model (`lean/Heliod/`) departs from the
pen-and-paper system, so the paper can be updated. The paper side is `typing.tex` (the rules;
included by `main.tex`) and `writeup.tex` (the running example and state inference). Everything
in the Lean model is proved with no `sorry`, using only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

Each entry gives what the paper says, what Lean does, and why. Entries are tagged:

* **[sound]**: the paper's rule as written is unsound, or the proof needs the change.
* **[precise]**: Lean's rule gives a tighter bound than the paper's; the paper's is still sound.
* **[model]**: a modelling choice that fixes something the paper leaves open or ambiguous.
* **[typo]**: a presentation slip in the paper.

Lean names are given as `File.lean`: `name`; all files are under `lean/Heliod/`.

---

## 1. Summary of the changes that matter most

| # | change | tag | section |
|---|---|---|---|
| 1 | Costs are summaries `Q f b` (cost at entry clock `f`, ambient background `b`) and `F f` (exit clock), not numbers; this makes `cost(·)` / `β` and `q[Δ]` precise | model | 3.1 |
| 2 | Call argument and function return are steps that charge background; expression evaluation is charged in the semantics | sound | 3.7, 3.8, 4.1 |
| 3 | `match`: only reachable arms are typed and charged, and the `match` step is charged inside each arm with `p` narrowed | precise | 3.6 |
| 4 | T-Await-Timeout's `max(q_a, q_fb + q_t)` is unsound (argued; the paper's rule is not mechanized); Lean charges the body at the spawn and the await `(n + f)·w + q_fb` | sound | 5.4, 5.5 |
| 5 | The window ambient of an async body is bounded over the whole window, not instantiated at the spawn | sound | 5.3 |
| 6 | The fallback is typed from the captured states `V`, not the spawn states; the await's output joins whole contexts | sound | 5.6 |
| 7 | No clock change while a thread is pending | sound | 5.7 |
| 8 | `HWReach` must be closed under further hardware steps; function signatures closed under hardware steps | sound | 2.2, 5.9 |
| 9 | State inference is formalized semantically (state sets, not `Φ`/`α` stacks); the conjectured relation to checking is replaced by precision and acceptance theorems | model | 6 |
| 10 | There is in general **no** largest entry-state set for a function (acceptance is not closed under union) | sound | 6.4 |

---

## 2. Language, platform and cost model

### 2.1 Types and peripheral handles [model]

* **Paper:** `τ ::= int | bool | unit | ρ | (τ₁, s⃗₁) → (τ₂, s⃗₂)`. Rules check `Γ ⊢ x : ρ`.
  Functions are stored in `Γ`.
* **Lean:** value types are first-order, `int | bool | unit` (`Syntax.lean`: `Ty`). Peripheral
  handles are tracked only by the peripheral context `Δ`, which maps each handle to its kind
  and possible states. The paper's `Γ ⊢ x : ρ` becomes "`Δ x` is live". Function signatures
  have their own context `Ψ` (`Typing.lean`: `SigCtx`), and async threads have theirs, `Θ`
  (section 5).
* Because handles are not values, `let x = e` and `let x = g(e, p)` require that `x` is not a
  handle (`Δ x = 0`). Without this, rebinding a handle name would lose track of a device.
* **Why:** functions are only declared at top level and used in calls, so first-order types
  suffice and keep cost functions out of types. Handles are never passed as values (the paper's
  Rust-like ownership), so `Δ` is the single source of truth for them.

### 2.2 Platform: state order, downgrades, stability, hardware steps [model, sound]

* **Paper:** each peripheral declaration lists states with costs `{cᵢ, cbᵢ}`, an order `<`, and a
  downgrade policy `D`. The order is "a lattice with a unique `⊤`". A downgrade `s' ↪ s` assumes
  `s' > s`. Predicates `stable` / `unstable` and `HWReach(st)` are assumed, with `HWReach` of a
  stable state empty.
* **Lean:** `Platform.lean`: `Platform` gives, per kind `k`, the state set, the order `le`, a top
  state, the downgrade relation `dg`, `stable`, and `hwReach`. `Platform.WF` requires:
  * `le` is a partial order on the kind's states with a greatest element `top`. A lattice is not
    needed: no rule uses joins of states.
  * `dg k s' s` implies `s < s'`.
  * `hwReach` stays within the kind's states and is empty for stable states.
  * **`hwReach` is closed under further hardware steps** (`hwReach_closed`): if `s' ∈ HWReach(s)`
    then `HWReach(s') ⊆ HWReach(s)`. **[sound]** The semantics lets hardware step repeatedly
    (E-HWStep has no limit), while T-Transition-Unstable applies `HWReach` once. Without
    closure, a peripheral can reach a state the typing never charged.
* `unstable` is defined as `¬ stable`.
* **Open question for the authors:** the prose says `HWReach(st)` is the set of "reachable
  transient states". Should it contain only unstable states? Lean does not require it.

### 2.3 Cost model [model]

* **Paper:** costs are per-state annotations `cᵢ` (active) and `cbᵢ` (background), transition costs
  `cost(sᵢ, sⱼ)`, a clock-change cost, `C_spawn`, and `C_v` for values (writeup).
* **Lean:** `CostModel.lean`: `CostModel` has `bgCost k s`, `transCost k s s'`, `clockCost f f'`,
  `spawnCost k s`, and **expression costs** `varCost`, `valCost`, `binopCost op`
  (`Expr.cost`: one per variable read, value, and operator). `stateCost` (the active cost `cᵢ`)
  and `unstableCost` (a transcription of `C_unstable`) are defined, but **no rule uses them**
  (see 5.5).
* The cost domain is an abstract ordered commutative semiring in which costs are non-negative
  (`ℕ`, `ℚ≥0` and `ℝ≥0` all qualify). The machine and the async results also assume truncated
  subtraction, for the count-down timers.
* **Assumption** (`CostModel.WF`): `clockCost f f'` is monotone in the source clock `f`.
  Summaries are monotone in the clock only with it, and soundness of sequencing needs that.

### 2.4 Other syntax [model]

* `skip` is a command (the paper's semantics uses it; the grammar omits it).
* **Commands have no type.** The paper's judgment is `… ⊢ c : τ ⇒ …`, and T-If and T-Seq carry
  `τ`. Commands only produce output contexts, so Lean drops `τ`.
* Binary operators are a fixed set (`add`, `sub`, `mul`, `eq`, `lt`, `and`, `or`) with a typing
  table (`BinOp.HasTy`); the paper leaves `binop` abstract.
* `match` arms are an inductive list. They need not have distinct states; the semantics runs
  the first matching arm (`Arms.find?`). A shadowed arm with a repeated state is still typed,
  so arms with distinct states are recommended.
* A function declaration names its peripheral parameter's kind (`FunDecl.pKind`), which the
  paper leaves implicit in `s⃗₁`.
* `timeout[n]` takes any natural number `n`; the paper's `n > 0` premise is not needed for
  soundness.

---

## 3. The checking type system (synchronous fragment)

`Typing.lean`: `Typed P M Ψ Γ Δ c Γ' Δ' Q F`, with match arms `ArmsTyped`, declarations
`FunDeclTyped` / `DeclsTyped`, and programs `Program.Typed`.

### 3.1 Cost summaries replace `q`, `cost(·)`, `β` and `q[Δ]` [model]

* **Paper:** the judgment is `Γ, Δ, f ⊢ c ⇒ Γ', Δ', q, f'` (or `…, f', q`; the order varies
  between rules). `cost(·)` / `β : amb` stand for peripherals invisible to a function, filled in at
  the call site as `q_f[Δ ∖ p]`, with `C(β, f)[β ↦ Δ] = Σ_{p∈Δ} cost(p)·f`. Clock scaling is
  written `(f)` on some terms and left implicit on others.
* **Lean:** a derivation yields two functions:
  * `Q f b`: the cost when `c` starts at clock `f` while invisible peripherals draw background
    `b` per unit of clock;
  * `F f`: the exit clock.

  Every charged step contributes `f · (its cost + cost(Δ) + b)`, the paper's `cost(Δ) + cost(·)`,
  scaled by the clock. Sequencing is `Q₁ f b + Q₂ (F₁ f) b`, so the second command is charged at
  the first's exit clock.
* A function is typed once (T-FunDecl) with summaries `Q_g`, `F_g`. A call instantiates them as
  `Q_g f (b + cost(Δ ∖ p))`: the callee's ambient is the caller's ambient plus the caller's other
  peripherals. This is the paper's `q_f[Δ ∖ p]` made exact.
* **Why:** it makes "parametric in the caller's clock and invisible peripherals" a definition
  instead of a substitution on symbolic expressions. It also settles which clock a function's
  cost is evaluated at (the entry clock).
  * Lean keeps the ambient term inside each summary, so after a branch it is charged for the
    duration of the branch that wins the `max`. A split into "cost plus duration × ambient"
    can over-approximate at branches of unequal duration. `Examples/Parametricity.lean`:
    `branchy_exact` computes an example where the split gives 35 and the summary 25.
* **Exit clock after branches:** `F = max(F₁, F₂)`, as in the paper's `f* = max(f₁, f₂)`.

### 3.2 Expressions [model, typo]

* **Paper:** T-Var gives no cost. T-BinOp adds `q₁ + q₂` but no cost for the operator, and its
  premise writes `binop : τ₁, q₁ × τ₂, q₂ → …`. There is no rule for values.
* **Lean:** `Contexts.lean`: `HasTy` has rules for variables, values and binary operators (typing
  only). Cost is a separate function `Expr.cost` (variables, values and operators each cost
  something).

### 3.3 T-Let [model]

* **Lean:** `Q f b = f · (q_e + cost(Δ) + b)`. This is the paper's `q_e + cost(Δ) + cost(·)` with
  the clock made explicit.
* The checking judgment is declared as `Γ, Δ, f ⊢ c : τ ⇒ Γ', Δ', f', q'`. Only T-FunDecl's body
  premise and T-Await-Timeout's fallback premise follow that order; every other rule lists its
  outputs as `…, q, f` **[typo]**.

### 3.4 T-If [typo, model]

* **Paper:** `q = max(q₁, q₂) + q_e + cost(Δ) + cost(·)`. The checking T-If's premise for `c₁`
  and its conclusion both omit `f` **[typo]**.
* **Lean:** `Q f b = max(Q₁ f b, Q₂ f b) + f · (q_e + cost(Δ) + b)` and `F f = max(F₁ f, F₂ f)`.
  The condition step is charged at the clock and includes background. Same shape as the paper,
  with scaling explicit.

### 3.5 T-Transition, T-Downgrade, T-Clock [model, sound]

* **T-Transition:** as in the paper, `f · (max_{s∈S} cost(s, st) + cost(Δ ∖ p) + b)`. The target
  must be stable; the unstable case is T-Transition-Unstable (section 5).
* **T-Downgrade:** Lean requires the target to be stable **[sound]**. The paper's checking
  T-Downgrade does not, though its inference version does. A downgrade to a transient state
  would need the `HWReach` treatment of T-Transition-Unstable.
* **T-Clock:** `clockCost(f, f') + f · (cost(Δ) + b)`, with `f' > 0`. The step is charged at the
  old clock `f`; the exit clock is `f'`.

### 3.6 T-Match [precise]

* **Paper:** every arm is typed from `Δ, p : stᵢ`, and
  `q = max(q₁, …, qₙ) + cost(Δ) + cost(·)`.
* **Lean:** `ArmsTyped` has three rules, `cons`, `last` and `skip`. They have two effects:
  * **Only reachable arms (`stᵢ ∈ Δ(p)`) are typed and charged** [precise]. Arms for states
    that cannot occur are skipped, neither typed nor charged. At least one arm must be reachable.
    The paper's rule types every arm, so an expensive arm for an impossible state inflates the
    bound. It also requires every arm to type from a state `p` can never be in.
  * **The `match` step is charged inside each arm, with `p` narrowed** [precise]: arm `i`
    contributes `Q_i f b + f · (cost(Δ[p : {stᵢ}]) + b)`, and the rule takes the `max` over
    reachable arms. When arm `i` runs, `p` is in `stᵢ`, so the paper's charge at `p`'s worst
    state over all of `Δ(p)` over-charges every arm whose state is not the worst one. Lean's
    charge is never larger than the paper's `max(qᵢ) + cost(Δ) + …` (an easy argument; the
    paper's rule is not formalized), and soundness is proved for Lean's rule.
* Exhaustiveness (`Δ(p) ⊆ {st₁, …, stₙ}`), `Γ' = ∩ Γᵢ`, `Δ' = ∪ Δᵢ` and `F = max Fᵢ` are as in the
  paper, over the reachable arms.

### 3.7 T-Call [sound, typo]

* **Paper:** `q = q_e + q_f[Δ ∖ p]`, output `Δ[p : s₂]`.
* **Lean:** `Q f b = f · (q_e + cost(Δ) + b) + Q_g f (b + cost(Δ ∖ p))`, output `Δ[p : s⃗₂]`,
  exit clock `F_g f`.
  * **The argument evaluation is a step** and charges background [sound]. In the paper it is
    charged `q_e` only, so for that step no peripheral pays background.
  * `Δ[p : s₂]` should be `Δ[p : s⃗₂]` [typo].
  * Premise `Δ(p) ⊆ s⃗₁`, as in the paper.

### 3.8 T-FunDecl and declarations [sound, model]

* **Paper:** the body is typed from `Γ[x : τ₁], Δ[p : s⃗₁], β : amb`, and the rule requires
  `Δ'(p) = s⃗₂`. The summary is `q_f = q₁ + q₂`, where `q₂` is the return expression's cost.
* **Lean:** the body is typed from `{x : τ₁}` and `{p : s⃗₁}` only, with the earlier functions in
  `Ψ`.
  * **The output states may be fewer than declared:** `Δ'(p) ⊆ s⃗₂`, not `=`.
  * **The return expression is a step** [sound]. The summary is
    `Q_g f b = Q_body f b + F_body f · (q_ret + cost(Δ_body) + b)`: it is evaluated at the body's
    exit clock and charges background, like the call's argument.
  * Declarations are typed **in order**, so each body sees only earlier functions: no recursion,
    including self-calls. Function names must be distinct (`DeclsTyped`, `Program.Typed`).

---

## 4. Semantics

### 4.1 Synchronous big-step semantics (`Semantics.lean`: `Eval`) [sound, model]

* **Paper:** small-step frame rules. E-Assign, E-IfTrue/False and E-Match charge `bg(S)(K)`, and
  expression evaluation (`→*`) is free. E-Call and E-Ret cost `0`. A single memory `M` holds
  everyone's variables.
* **Lean:** big-step `Eval M Ψd A σ S K c σ' S' q K'` for the synchronous fragment, related to the
  small-step machine by `Adequacy.lean` in both directions.
  * **Expression evaluation is charged** `K · q_e` in `let`, the `if` condition, the call
    argument and the return expression, matching the typing rules.
  * **E-Call and E-Ret charge** `K · (q_e + bg(S) + bg(A))` and `K_b · (q_ret + bg(S_b) + bg(A_b))`
    [sound]. With the paper's free call and return, there are instants at which no peripheral
    pays background. This was found while proving that every peripheral is charged at every step
    (`Accounting.lean`).
  * **Ambient peripherals `A`**: the runtime counterpart of `β`, a multiset of `(kind, state)` of
    peripherals the current function cannot see. Every step charges `bg(A)`, and a call runs its
    body with `A + entries(S ∖ p)`.
  * **Per-frame memory**: a call runs its body in a fresh memory `{x ↦ v}`, and only the return
    value flows back [model]. With the paper's single `M`, a callee's locals overwrite the
    caller's.
  * No runtime typestate checks. Ill-typed situations simply have no derivation. A `match` runs
    the first arm whose state matches.

### 4.2 The small-step machine (`Machine.lean`) [model]

The paper's E-rules for async, with these choices:

* **Devices:** one global store of devices, named by their declaring handles. Activations map
  handle names to devices. Every charging (ticked) step charges the background of every device
  plus the ambient,
  except that a moved device pays its transition (or, at a spawn, the spawn cost) instead.
* **Activations:** each call and each thread body has its own memory, handle map and thread-id
  map. Calls and returns are machine steps with the costs of 4.1.
* **Segments:** the paper's single frame stack grouped by thread. A scheduled thread runs on top
  until it finishes, another pending thread is scheduled above it, or its awaiter times out
  (E-Timeout-Running).
* **Thread ids:** fresh runtime numbers bound to the `tid` name in the spawning activation, so
  name reuse in different activations cannot clash.
* **Ticks:** a step ticks if it charges. That is the paper's list (assign, if, transition,
  downgrade, clock, match, async, waiting) **plus call and return**, which the paper does not
  tick (they cost nothing there).
* **Timers** count down as in the paper. A waiting frame holds the remaining budget `rem`, which
  each ticked step lowers by the clock in force before the step (truncated). The await times out
  once `rem ≤ 0`. `rem` lives in the cost domain, not `ℕ`.
* **No elapsed-time component `T`:** the machine tracks cost, not time.
* **E-HWStep** applies to the device of any pending or running thread.
* **E-Call checks that the parameter's device holds a peripheral** (well-typed programs always
  pass). The reverse adequacy direction needs it.

---

## 5. Async / await and hardware steps (`AsyncTyping.lean`: `TypedA`)

`TypedA P M Ψ fz Γ Δ Θ c Γ' Δ' Θ' W Q F` extends `Typed` with a **thread context** `Θ` (pending
threads), a flag `fz` (clock frozen), and `W`, the join of every context `c` passes through. A
synchronous derivation is an async one with the same summaries, provided the program's declared
states are stable (`Embed.lean`: `Typed.toA`, `Program.Typed.toA`).

### 5.1 Async bodies are closures [model]

* **Paper:** the body shares the single memory `M`, which allows data races.
* **Lean:** the body runs in its own memory frame, with copies of the values it reads. There is
  no shared memory.

### 5.2 The captured peripheral [model]

* **Paper:** `Δ'(p) = cap(s⃗ᵢ, tid)`. `cost(cap(…))`, the background charge of a captured
  peripheral in the main thread's steps, is not defined.
* **Lean:** while captured, `p` may be in any state the body visits or that hardware reaches
  from one: `V = hwClose(W_body(p))`. The main thread sees `Δ(p) = V`, so its steps charge `p` at
  `maxBg V`, and it may not use `p` (`¬ Θ.Captures p`).

### 5.3 The window ambient is bounded over the whole window [sound]

* **Paper:** the inference version of T-AsyncFun (`typing.tex`, line 232) instantiates the body's
  cost with `β ↦ Δ ∖ p` **at the spawn**; the checking version leaves `q_a` uninstantiated. While the
  body runs, the main thread may move its other peripherals to costlier states. The body's steps
  then pay more background than the spawn-time `Δ ∖ p` accounts for.
* **Lean:** T-AsyncFun takes a declared bound `amb` and charges the body as `Q_a f (b + amb)`.
  Each pending thread's entry in `Θ` accumulates `win`, the join of every main-thread context
  since the spawn. T-Await-Timeout checks `cost(win ∖ p) ≤ amb`. The tightest choice is
  `amb = cost(win ∖ p)`.

### 5.4 T-AsyncFun: what is charged and when [sound]

* **Lean:** `f · (max_{s∈S} spawnCost(s) + cost(Δ ∖ p) + b) + Q_a f (b + amb)`. The paper's typing
  charges a constant `cost(async spawn)`, while its E-Async charges `C_spawn(p, S(p), K)`, which
  depends on the state. Lean takes the worst case over the spawn states `S`. The body's
  summary is paid at the spawn, like a closure paid for when it is created; the await does not
  charge it again. Paying at the spawn does not change the total. It lets the soundness proof
  give each pending thread its own reserved budget.
* Premises as in the paper: `p`'s states are all unstable, the body is typed from them seeing
  only `p`, and it must end in stable states. In addition:
  * `p`'s states are closed under hardware steps (`hwClose S = S`);
  * the body is typed **frozen** (5.7) with no pending threads of its own;
  * the spawn itself happens outside frozen code, so there are **no nested threads** (5.8).

### 5.5 T-Await-Timeout: the cost [sound]

* **Paper:** `max(q_a, q_t + q_fb)` with `q_t = n · (C_unstable(p) + cost(Δ ∖ p) + cost(·))`.
* **The `max` is unsound** (by the following argument; this is not a Lean theorem, since Lean
  never formalizes the paper's rule). A run can let the main thread wait almost the whole
  budget, run the body until just before its last step, time out, and run the fallback. That run
  pays almost all of `q_a`, plus the waiting not overlapped by the body, plus `q_fb`. When the
  body is expensive and the fallback is not trivial, this exceeds both `q_a` and `q_t + q_fb`.
  Also, when the body completes, the waiting ticks spent before the join are not part of
  `q_a`.
* **Lean:** `(n + f) · (maxBg V + cost(Δ ∖ p) + b) + Q_fb f b` at the await, with the body already
  paid at the spawn. `n + f` bounds the waiting: the timer counts down by `f` per tick and the
  last tick may overshoot. The exit clock is `max(F_fb f, f)`.
* **`C_unstable`:** the paper defines it as `max_{s ∈ st ∪ HWReach(st)} C(p : s)` over the spawn
  states. Lean charges `maxBg V`, the background cost over the captured states `V`. The active
  cost `cᵢ` (`stateCost`) is not used. If the paper intends `C_unstable` to use active costs, the
  machine's charge for a waiting tick would have to change accordingly.
* **What the Lean bound over-counts:**
  * the overlap of the body's running time with the waiting, about `d · w` for a body of
    duration `d` (argued, not proved);
  * the cut-off last step (argued, not proved);
  * rounding of the last tick: proved, for cost domains with additive cancellation
    (`[AddLeftReflectLE R]`): the tick that exhausts the budget leaves a positive part of the
    allowance unused (`waitAllow_exhaust_pos`, an identity about the allowance; the released
    `wait` items' specification does not record this formula).

  What is proved about attainment (`AsyncNecessity.lean`):
  * **The waiting charge is attained up to one tick, under a hypothesis.** Assume the cost
    domain is Archimedean, the clock is positive, and `main` alone is waiting on a pending
    thread with budget `rem`. Then there is a run that never schedules the thread: it only
    waits, `m` ticks with `rem ≤ m · f ≤ rem + f`, and times out to the start of the fallback
    (`Steps.never_schedule`). If the per-tick charge equalled the typed rate `w`, that waiting
    would cost between `rem · w` and `(rem + f) · w` (`waiting_cost_bounds`, which is only this
    arithmetic). The equality of the rates (devices at their worst typed states) is not proved
    from the typing.
  * **Some fallback or abandon item after every wait.** In any complete run of a typed program
    that passes through a configuration where `main` waits, the rest of the run releases either a
    `fallback` item (the summary of a fallback that did not run) or an `abandon` item (the
    timed-out thread's remaining reservation), and the run's cost plus that item is within the
    bound (`Program.await_gap`). The item may be zero, for example when the fallback is free.

  That the whole sum `Q_a + (n + f) · w + Q_fb` is nearly attained (by the run described under
  "The `max` is unsound") is an argument, not a Lean theorem.
  A tighter rule would charge `(n − d_min + f) · w`, given a lower bound `d_min` on the body's
  duration.

### 5.6 The fallback is typed from `V` [sound]

* **Paper:** `c_fb` is typed from `Δ[p : s⃗ᵢ]`, the spawn states.
* **Lean:** `c_fb` is typed from `Δ(p) = V`. After a timeout the body may have stopped anywhere,
  and it may already have finished: `V` contains the body's exit states.
  `Examples/Async.lean` illustrates the effect (in its documentation, not as a theorem): the
  fallback must handle the already-finished `Off` state, so a plain `downgrade` there does not
  type.
* **The output contexts** [sound]:
  * Peripherals: Lean's output is `Δ[p : s⃗_o] ∪ Δ_fb`, joining the whole context. The paper's
    `Δ[p : s⃗_fb ∪ s⃗_o]` changes only `p`, so it loses what the fallback does to other handles.
  * Variables: Lean's output is `Γ ∩ Γ_fb`. The paper's `(Γ ∪ Γ_fb) ∖ tid` keeps variables bound
    only in the fallback, which are unbound after a successful await.

### 5.6a Branches agree on pending threads [model]

`if` and `match` require their branches to leave the same threads pending
(`ThreadCtx.SameThreads`, in `TypedA.ite` and `ArmsTypedA.cons`). A fallback may not leave new
threads pending either. So an `if` in which only one branch spawns, or only one branch awaits,
is rejected. The paper does not say what happens to `tid` bindings across a join.

### 5.7 Frozen clock while a thread is pending [sound]

* **Paper:** the body may change the clock, and the await's exit clock is `max(f, f_a, f_fb)`.
  Main-thread steps typed at `f` would then run at the body's clock.
* **Lean:** no clock change while a thread is pending, in the body or in the main thread
  (T-Clock requires `fz = false` and `Θ` empty). Calls in frozen code must go to functions marked
  `stableClock`.

### 5.8 No nested threads [model]

Frozen code cannot spawn. Frozen code is every async body, and the body of every function
declared `stableClock`, even when such a function is called with nothing pending. Every spawner
is on the main side.

### 5.9 Hardware steps and `match` [sound]

* **T-Transition-Unstable:** the output is `Δ[p : hwClose{st}]`, where `hwClose{st} = {st} ∪ HWReach(st)`.
  The charge is `f · (max_{s∈Δ(p)} cost(s, st) + cost(Δ ∖ p) + b)`, the worst transition into
  `st`. The paper writes `max(cost(st', st⁺))`, a cost into the set `st⁺`, with no clock scaling;
  Lean reads `st⁺` as `st` [typo]. The hardware steps afterwards are free, as in E-HWStep.
* **`match` arms narrow to `hwClose{stᵢ}`**, not `{stᵢ}`. Hardware may move a captured
  peripheral right after the `match` reads it. For stable `stᵢ` this is `{stᵢ}`.

### 5.10 Function signatures in the async language [sound, model]

`FunSigA` adds two fields:

* `visit`: the states the parameter passes through during the call. Pending threads' windows
  observe them.
* `stableClock`: the body never changes the clock, so the function may be called in frozen code.

`FunDeclTypedA` requires `hwClose(s⃗₁) = s⃗₁` and `hwClose(s⃗₂) = s⃗₂`. A function called from an
async body on the captured peripheral runs while hardware may move it. For functions over
stable states this costs nothing.

A function may not leave a thread pending. **Calls while threads are pending are allowed**,
provided the callee has a stable clock.

---

## 6. State inference

### 6.1 Formulation [model]

* **Paper:** peripherals map to stacks of state variables `[α]`. Constraints `Φ` are collected,
  contexts are joined with `⊎`, costs are symbolic expressions `C(p : (α, st))`, and they are
  concretized lazily at calls (`C_f[α ↦ solve(…)]`).
* **Lean** (`Inference.lean`), a semantic formulation: a constraint on `α` is represented by the
  set of states it allows. The two pieces:
  * **Narrowing** (`Typed.narrow`, `TypedI.narrow`): typing from fewer possible states, or more
    known variables, gives more precise outputs and summaries that are no larger. (`Typed.narrow`
    assumes the signatures' summaries are monotone and their output sets non-empty, and the
    narrowed state sets must be non-empty.) This is the
    property that makes lazy concretization pay off.
  * **Inline typing** (`TypedI`): T-Call types the callee's **body** from the caller's current
    states `Δ(p)`, instead of instantiating a declared signature. This is lazy concretization
    with `solve(…) = Δ(p)`. Declared `s⃗₁` / `s⃗₂` are not used.
    * `soundnessI`: inline typing is sound, with no assumption about signatures.

  The symbolic cost language, the variable stacks and `⊎` are not formalized.
  * Eager concretization corresponds to the body being typed with concrete state sets
    throughout.
  * `C_f[α ↦ s⃗]` corresponds to the body's summary at entry set `s⃗`.

### 6.2 The relation to the checking system [model]

* **Paper:** "given checking and inference derivations of `c`, `solve(Φ|_p) ⊆ Δ(p)`".
* **Lean proves two statements instead:**
  * **Precision** (`Typed.toI`, `Program.Typed.precision`): every checked program is inline-typed
    with summaries no larger than the checked ones. Lazy concretization is never worse than
    declared signatures.
  * **Declared entry states are accepted** (`Program.Typed.accepts`): each function accepts every
    non-empty subset of its declared `s⃗₁`.

### 6.3 What a function accepts [model]

`Accepts d S`: the body inline-types from entry states `S`, and the return expression types
afterwards. It is exactly what an inline call from a caller with `Δ(p) = S` needs.

* `Accepts.mono`: closed downward (fewer states, at least one).
* `entrySet d = {s | Accepts d {s}}`: the states accepted one at a time. It contains every
  accepted set (`Accepts.subset_entrySet`).

### 6.4 There is no largest entry set [sound]

* **Paper:** inference T-FunDecl computes `s⃗₁ = solve(Φ_f|_{αᵢ})` as the function's entry states,
  implicitly a single set from which the body types.
* **Finding:** acceptance is **not closed under union**, so in general no single largest entry set
  exists. The cause is that `match` (and `if`) intersect their arms' variable contexts, forgetting
  which arm ran. Lean counterexample (`Examples/EntrySets.lean`: `entrySet_not_accepted`):

  ```
  match s | Idle → let x = true | Measure → let x = 1;
  match s | Idle → if x then … | Measure → let y = x + 1
  ```

  * From `{Idle}` or from `{Measure}`, only one arm of each `match` is reachable, and the body types.
  * From `{Idle, Measure}`, the first `match` intersects `x : bool` with `x : int`, which drops
    `x`, and the second `match` cannot type.
* **Consequence for the paper:** `solve(Φ_f|_{αᵢ})` cannot in general be read as "the" set of
  states the function accepts. Options:
  1. Check acceptance per call site (what Lean's `TypedI` does, and what lazy concretization
     suggests).
  2. Make the typing path-sensitive.
  3. Accept that the inferred `s⃗₁` is one maximal accepted set among several.

### 6.5 The running example [precise]

`Examples/LogDataInline.lean`: `main` calls `log_data` with `temp` in `Idle`, so the call
types `log_data`'s body from `{Idle}`:

* `main_inline` gives the inline summary in closed form. Its first transition is charged
  `C(temp : (Idle, Measure))`; the checking system charges
  `max(C(temp : (Idle, Measure)), C(temp : (Measure, Measure)))`. This matches the writeup's
  `C_l[α₀ ↦ Idle]`.
* `inline_le_check` compares the inline summary with the checking one.
* `cost_bound` gives the resulting bound on every run from clock `1`.

Compared with the writeup's table for `C_l` (Figure 3), Lean's summary for `log_data`
(`Examples/LogData.lean`: `logDataCost`) differs in these ways:

* `temp.measure()` (cost `C_m`) is not in the core language; the example uses `let res = 65`
  (cost `valCost`) in its place;
* expression costs are explicit (`C_v` becomes `valCost`, `varCost`, `binopCost`);
* there is a fourth `C(temp : Measure)`, for the `if` condition step;
* the `if` costs its `then` branch (`max(C_v, 0)`, with `skip` free);
* the return step is charged (`varCost + C(temp : Off)`);
* every step also charges the ambient `b`.

### 6.6 Not formalized

* Inference for the async rules (the inference versions of T-AsyncFun, T-Await-Timeout and
  T-Transition-Unstable).
* A solver. Lean states what a solution must satisfy, not how to compute one.

---

## 7. What is proved (for citing)

| paper claim | Lean theorem | notes |
|---|---|---|
| soundness: run cost `q' ≤ q` | `Soundness.lean`: `Program.soundness` (sync, big-step `Eval`; needs `M.WF`); `Adequacy.lean`: `Program.MRun.soundness` (sync programs on the machine); `AsyncProgram.lean`: `Program.MRun.soundnessA` (async, machine, every schedule and hardware behaviour; needs `M.WF`, `P.WF`) | bound is `Q K₀ 0`: the summary at the initial clock, nothing ambient |
| type safety | `Soundness.lean`: `eval_total` (a typed command from agreeing states has a big-step run, given valid signatures); `AsyncSafety.lean`: `Program.typeSafetyA` (every reachable machine configuration is final or steps; needs `M.WF`, `P.WF`); `Embed.lean`: `Program.Typed.typeSafety` (the same for sync programs whose declared states are stable) | |
| every peripheral charged once per step | `Accounting.lean`: `Eval.whole_run_accounting` (big-step runs); `AsyncAccounting.lean`: `Steps.accounting` (machine runs) | not stated in the paper |
| where the bound is loose | `SlackProgram.lean`: `Program.slack_decomposition` (sync, along any control-flow path, `Path`; `Program.Eval.slack_decomposition` for real runs); `AsyncSlack.lean`: `Program.slack_decompositionA` (machine runs) | `Q K₀ 0 = cost + Σ slack items`, each of a named kind with a formula; see `IMPRECISION.md` |
| local attainment | `Necessity.lean`: `PCtx.bg_attained`, `PCtx.trans_attained`; `AsyncNecessity.lean`: `LFact.charge_attained`, `LFact.amb_zero_of_tight` | each per-step background, transition or spawn charge equals the actual charge for some runtime state consistent with the context (non-empty state sets); `ambient` / `window` items vanish when the declared bound is tight. Not a claim that whole bounds are attained (see 5.5) |
| inference vs checking | `Inference.lean`: `Program.Typed.precision`, `Program.Typed.accepts`, `soundnessI` | section 6 |
