# Heliod Lean mechanization — status

## Done (builds, no `sorry`)
- `Heliod/Platform.lean` — peripheral kinds, state order, downgrade policy, stable/HWReach, `Platform.WF`.
- `Heliod/Syntax.lean` — types, values, binops, expressions, commands (incl. async/await), match arms, function decls, programs.
- `Heliod/CostModel.lean` — cost annotations, `CostModel.WF` (clock-cost monotonicity), max helpers + 4 small lemmas.
- `Heliod/Contexts.lean` — `Γ` (TCtx), `Δ` (PCtx = `Var →₀ PEntry`), join/erase/set, `cost(Δ)`, expression typing + cost; simp lemmas for lookups/erase/join and `cost(Δ)` (`bg_set`, `bg_single`, `bg_zero`, `erase_join`, …).
- `Heliod/Typing.lean` — **cost-summary** judgment `Typed P M Ψ Γ Δ c Γ' Δ' Q F` (`Q f b`: cost at entry clock `f`, ambient background `b`; `F f`: exit clock), mutual `ArmsTyped`, `FunSig`/`SigCtx`, `FunDeclTyped` (T-FunDecl), `DeclsTyped`, `Program.Typed`. Definitions only.
- `Heliod/Semantics.lean` — big-step cost semantics `Eval` for the sync fragment (per-frame memory, exact peripheral states, ambient multiset `A`), `Program.Eval`.
- `Heliod/Examples/LogData.lean` — writeup's `log_data`: `P_wf`; `logData_typed` gives `log_data`'s summary as a closed formula in `f` and `b` (typed once, parametric in callers); `prog_typed` shows `main` instantiates it at ambient `b + bg(aux)` and equals `expectedCost` at clock 1.
- `Heliod/Examples/Match.lean` — `match` with differing arm results; `settle_typed` summary + `prog_typed`.

## Proved in `Heliod/Soundness.lean`
- `Typed.shape_eq` / `ArmsTyped.shape_eq` — typing preserves handles and kinds of `Δ` (helpers: `shape_set_set`, `shape_set_of`, `shape_join`).
- `Typed.mono` / `ArmsTyped.mono` — derived summaries are monotone in `f` and `b` (uses `CostModel.WF`).
- Agreement lemmas: `HasTy.eval`, `MemOK.bind`/`mono`, `TCtx.Sub`, `PCtx.Le` (+ `le_join_left/right`), `PeriphsOK.mono/at/set/erase/bg_le`, `ArmsTyped.find`, `SigsValid.mono`; runtime lemmas in `Semantics.lean` (`RPeriphs.set_apply`/`erase_apply`/`set_eq_self`, `ambBg_add_entries`).
- **`soundness`** — actual cost `≤ Q K (bg A)`, exit clock `≤ F K`, final state agrees with output contexts; assumes `SigsValid`.
- **`eval_total`** (+ `ArmsTyped.arm_eval_total`) — well-typed commands always run to completion (sync termination / type safety); assumes `SigsValid` and `M.WF`.
- **`FunDeclTyped.valid`**, **`DeclsTyped.sigsValid`**, **`Program.sigsValid`** — declarations typed in order yield valid signatures.
- **`Program.soundness`** — a well-typed program run from clock `K₀` costs at most `Q K₀ 0`.
- `#print axioms` for all four main results: only `propext`, `Classical.choice`, `Quot.sound`. **The sync fragment has no `sorry`.**


## Proved in `Heliod/Accounting.lean` — accounting (A), semantic side, no `sorry`
- Population `pop S A = entries(S) + A` (visible + ambient peripherals).
- `Eval.kind_eq` / `Eval.kinds_conserved` — runs never create, drop or re-kind a peripheral; the multiset of kinds in the population is invariant.
- `pop_call` — a call's body runs with exactly the caller's population (parameter + new ambient re-partition it).
- `charge_static` — assign/if/clock/match and the call's argument/return evaluations charge `K · Σ_{m ∈ pop} bgCost m` (each member once).
- `charge_move` / `pop_after_move` — transition/downgrade: `pop = (k,s) ::ₘ rest`, charge `K·(transCost k s st + bg(rest))` (mover pays transition instead of background); afterwards the mover is in `pop` with its new state.
- **Whole runs:** `ETrace` (instrumented semantics recording charge events) is faithful to `Eval` (`ETrace.toEval`, `Eval.toTrace`). **`Eval.whole_run_accounting`**: a run's cost is the sum of its events; *every* event charges a population with the run's initial devices (`ETrace.pop_kinds`), split into one optional mover (transition cost) and the rest (background), so each device is charged exactly once per event.

## Open items for the sync fragment
- Accounting (B): **slack decomposition** (`Heliod/Slack.lean`). Done, no `sorry`: path semantics `Path` + `Eval.toPath`; slack judgment `SlackRun`/`ArmsSlack` (kinds: state, branch, arm, clock, ambient, signature); faithfulness `SlackRun.toTyped`/`toPath`; identity `SlackRun.decompose` (`Q K (bg A) = q + Σ δ`, given `actual ≤ typed` per item). Also done: existence `SlackRun.exists` (every typed path has a slack derivation with `actual ≤ typed`, assuming `SigsDerived`), `slack_decomposition` / `Eval.slack_decomposition`, exactness corollary `SlackRun.exact`. Necessity done in `Heliod/Necessity.lean`: `PCtx.bg_attained`, `PCtx.trans_attained` (local attainment), `PeriphsOK.bg_eq_of_pinned` (pinned ⇒ no state slack), `Typed.pinned` (origin of uncertainty). Programs (`Heliod/SlackProgram.lean`): `Typed.weaken`, `DeclsTyped.sigsDerived`, `Program.sigsDerived`, `Program.initPinned`, **`Program.slack_decomposition`** / `Program.Eval.slack_decomposition`. Accounting (B) is complete. Examples and discussion in `IMPRECISION.md`.
- Possible cleanup: `eval_total` takes `hM : M.WF` only because its `seq` case reuses `soundness` for state agreement; a cost-free *preservation* lemma would remove it.
- Possible addition: `Program.eval_total` (whole programs terminate) — immediate from `eval_total` + `Program.sigsValid` + `Program.initOK`.

## Parametricity examples (`Heliod/Examples/Parametricity.lean`, done, no `sorry`)
- `logDataCost_ambient`: ambient enters `log_data`'s cost linearly, `6·f·e`.
- `callers_differ_by_ambient`: same `log_data`, callers with/without two extra sensors; costs differ by exactly `7·f·(bg Off + bg Measure)`.
- `progN_typed`: `main → wrap → log_data`; `main`'s extra sensor is charged inside `log_data`, two calls down.
- `branchy_exact`: branches of unequal duration; summary keeps ambient inside the `max` (concrete model: bound 20 vs 30 for the cost/duration split).
- Still to do: an example exercising `clock` (clock-parametric summaries, `clockCost`).

## Build workflow
- Edit in OneDrive; build on the WSL mirror with `scripts/mirror-build.sh` (~25 s vs ~7 min per file). With a file argument it runs `lake build Heliod.X`, rebuilding stale dependencies (plain `lake env lean` would use stale imports).

## Roadmap
1. ~~Syntax + cost model~~
2. ~~Checking type system, sync fragment~~ — sanity-checked by `Examples/LogData.lean` (seq, let, if, transition, downgrade, call, ambient instantiation) and `Examples/Match.lean` (match/arms, join of differing arm states). `clock` is not yet exercised by an example.
3. ~~Cost semantics for sync fragment; cost soundness, termination~~ (done, no `sorry`); accounting (A) done in `Accounting.lean`; tightness (B) open.
4. Async / await / HW steps (typing + frame/thread-pool semantics).
5. State-inference system (α, Φ, symbolic costs, ⊎ join) and its relation to the checking system.

## Design decisions / questions for the paper authors
- **Cost summaries.** The paper's `β : amb` / `cost(·)` holes make costs parametric in the caller's clock and in peripherals invisible to the current function (`C(β,f)[β ↦ Δ] = Σ_{p∈Δ} cost(p)·f`). Lean: a derivation yields `Q f b` and `F f`; functions are typed once (T-FunDecl) and instantiated at calls as `Q_g f (b + cost(Δ ∖ p))` (the paper's `q_f[Δ ∖ p]`). Exact pointwise (chosen over a cost/duration split, which over-approximates at branches of unequal duration). Also resolves the T-FunDecl/T-Call clock ambiguity: summaries are functions of the entry clock.
- Should `HWReach(st)` contain only unstable states (prose says "reachable transient states")? Not imposed currently.
- Paper's T-Call requires the body's final states to equal `s⃗₂`; Lean requires `⊆ s⃗₂`.
- **Refined T-Match (2026-11-08):** only reachable arms (`stᵢ ∈ Δ(p)`) are typed and charged (`ArmsTyped` rules `cons` / `last` / `skip`). The paper types and charges every arm, so an expensive arm for a state that cannot occur inflates the bound.
- **Match step charged per arm (2026-11-08):** each reachable arm's summary includes the `match` step with `p` narrowed, `f·(cost(Δ[p : {stᵢ}]) + b)`, inside the max over arms (was `max(arms) + f·(cost(Δ) + b)`). Never larger, still sound; makes a `match` on a multi-state handle tight.
- `clockCost` must be monotone in its source frequency for summaries to be monotone (assumed in `CostModel.WF`).
- The semantics charges expression cost `K·q_e` (the paper's E-rules evaluate expressions for free) — chosen so typing and semantics charge the same CPU costs.
- Paper's single memory `M` lets a callee's locals overwrite the caller's; Lean uses per-frame memory.
- Paper rule typos fixed in the Lean version: T-If missing `f` on the `c₁` premise; T-Let/T-Call output order `q, f` vs judgment; T-Var has no cost; no value rule; checking T-Call `Δ[p : s₂]` should be `s⃗₂`.
- **Call / return charge background (2026-11-08):** E-Call charges `K·(q_e + bg(S) + bg(A))` for the argument and `Kb·(q_ret + bg(S_b) + bg(A_b))` for the return expression; T-Call charges `f·(q_e + cost(Δ) + b)` and T-FunDecl's summary adds `F f·(q_ret + cost(Δ_b) + b)`. Previously these expression costs were charged without background, leaving time in which no peripheral was charged (found while proving whole-run accounting). The paper's E-Call/E-Ret are free.
