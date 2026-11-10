import Heliod.Semantics

/-!
# Small-step machine with threads, preemption, hardware steps and timeouts

The paper's operational semantics for the async extension (E-Async, E-AsyncPreempt,
E-AsyncDone, E-AwaitStart, E-Await, E-AwaitWait, E-Await-Timeout, E-Timeout-Running, E-HWStep,
and E-Step with `tick`/`drain`), adapted to the design decisions of the Lean model.  The
synchronous big-step `Eval` remains the semantics of the sync fragment; `Heliod.Adequacy`
relates the two.

## Configuration

* **Devices and the store.**  Every peripheral is a device, named by the handle that declared it
  in the program (`Dev := Var`).  The store `D : RPeriphs K St` maps each device to its kind and
  current state.  There is one store for all threads and activations, so the *population* of
  `Heliod.Accounting` is simply `entries(D) + A`: every step charges the background of all
  devices (`bg(D) + bg(A)`), except that the device a step moves pays its transition instead.
* **Activations** (`Act`): one per function call or thread body — its own memory `σ` (per-frame
  memory, as in `Eval`), handle map `H` (handle name ↦ device), thread-id map `T` (`tid` name ↦
  runtime thread id), control stack `ctl`, and, for a called function, the return expression and
  the caller's target variable.
* **Segments** (`Seg`): the paper's single stack `C` of frames, grouped by thread.  The top
  segment is the running thread; the last is `main`.  A thread, once scheduled, runs on top until
  it finishes or its awaiter's timer expires (the paper's stack discipline).
* **Thread pool**: runtime thread id ↦ captured device, body, closure memory, handle name, and
  status (`pending` — spawned, not yet scheduled; `running`; `done`).
* **Clock** `K`.

## Costs (as in `Eval`)

| step | cost | tick |
|---|---|---|
| `let x = e`, `if`, `match` | `K·(q_e + bg(D) + bg(A))` (no `q_e` for `match`) | yes |
| `transition`/`downgrade` of device `d` | `K·(transCost(s, st) + bg(D ∖ d) + bg(A))` | yes |
| `clock f'` | `clockCost(K, f') + K·(bg(D) + bg(A))` | yes |
| call (argument), return | `K·(q_e + bg(D) + bg(A))` | yes |
| `async` on device `d` | `K·(spawnCost(s) + bg(D ∖ d) + bg(A))` | yes |
| waiting at `await` | `K·(bg(D) + bg(A))` | yes |
| sequencing, skip, scheduling, thread completion, timeouts, hardware steps | 0 | no |

After a ticked step every waiting `await` timer advances by the clock `K` in force before the
step (`Config.drain`).  As in the paper, timers count *down*: a waiting frame holds the remaining
budget `rem` (initially `n`), each ticked step lowers it by `K` (truncated subtraction), waiting
continues while `0 < rem`, and the await times out once `rem ≤ 0`.

## Departures from the paper (see `TODO.md`)

* Per-activation memory, closures for async bodies (copy of the spawner's memory).
* Runtime thread ids are fresh numbers bound to the `tid` name in the spawning activation, so
  name reuse across activations cannot clash.
* Hardware steps (E-HWStep) apply to the device of any pending or running thread.
-/

variable {K St R : Type}

/-- A device is named by the handle that declared it. -/
abbrev Dev := Var

/-- Runtime thread identifiers. -/
abbrev ThreadId := Nat

/-- Control-stack entries of an activation. -/
inductive Ctl (St R : Type) where
  /-- A command to execute. -/
  | cmd (c : Cmd St R)
  /-- `await•`: waiting for runtime thread `id` (bound to name `tid`) with time budget `n`,
  remaining budget `rem`, and fallback `fb`. -/
  | awaitW (tid : Var) (id : ThreadId) (rem : R) (fb : Cmd St R)

/-- An activation: a function call's or thread body's local state. -/
structure Act (St R : Type) where
  σ : Mem
  H : Var → Option Dev
  T : Var → Option ThreadId
  ctl : List (Ctl St R)
  /-- For a called function: the return expression and the caller's target variable. -/
  onRet : Option (Expr × Var)

/-- A thread's activations (top first); `owner = none` for `main`. -/
structure Seg (St R : Type) where
  owner : Option ThreadId
  acts : List (Act St R)

/-- Status of a spawned thread. -/
inductive TStatus where
  | pending | running | done
  deriving DecidableEq

/-- A thread-pool entry. -/
structure PoolEntry (St R : Type) where
  dev : Dev
  body : Cmd St R
  σ : Mem
  p : Var
  status : TStatus

/-- Machine configurations. -/
structure Config (K St R : Type) where
  segs : List (Seg St R)
  pool : ThreadId → Option (PoolEntry St R)
  D : RPeriphs K St
  K : R

section Drain
variable [Sub R]

/-- Lower a waiting timer by `d` (truncated). -/
def Ctl.drain (d : R) : Ctl St R → Ctl St R
  | .awaitW tid id rem fb => .awaitW tid id (rem - d) fb
  | c => c

/-- Lower every waiting timer of a configuration by `d` (the paper's `drain`). -/
def Config.drain (d : R) (c : Config K St R) : Config K St R :=
  { c with segs := c.segs.map fun s =>
      { s with acts := s.acts.map fun a => { a with ctl := a.ctl.map (Ctl.drain d) } } }

end Drain

variable [DecidableEq St] [CommSemiring R] [LinearOrder R]

/-- One machine step `c —q→ c'`, with `tick` telling whether it takes a time step.  The
running activation is the top activation of the top segment. -/
inductive Step (P : Platform K St) (M : CostModel K St R) (Ψd : FCtx K St R)
    (A : Multiset (K × St)) : Config K St R → R → Bool → Config K St R → Prop where
  /-- E-SeqDone. -/
  | skip {o σ H T ctl r as ss pool D Kc} :
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, .cmd .skip :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩ 0 false
        ⟨⟨o, ⟨σ, H, T, ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
  /-- E-Seq. -/
  | seq {o σ H T c₁ c₂ ctl r as ss pool D Kc} :
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, .cmd (.seq c₁ c₂) :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩ 0 false
        ⟨⟨o, ⟨σ, H, T, .cmd c₁ :: .cmd c₂ :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
  /-- E-Assign. -/
  | assign {o σ H T x e v ctl r as ss pool D Kc} :
      e.eval σ = some v →
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, .cmd (.assign x e) :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
        (Kc * (e.cost M + D.bg M + ambBg M A)) true
        ⟨⟨o, ⟨σ.set x v, H, T, ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
  /-- E-IfTrue. -/
  | iteTrue {o σ H T e c₁ c₂ ctl r as ss pool D Kc} :
      e.eval σ = some (.bool true) →
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, .cmd (.ite e c₁ c₂) :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
        (Kc * (e.cost M + D.bg M + ambBg M A)) true
        ⟨⟨o, ⟨σ, H, T, .cmd c₁ :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
  /-- E-IfFalse. -/
  | iteFalse {o σ H T e c₁ c₂ ctl r as ss pool D Kc} :
      e.eval σ = some (.bool false) →
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, .cmd (.ite e c₁ c₂) :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
        (Kc * (e.cost M + D.bg M + ambBg M A)) true
        ⟨⟨o, ⟨σ, H, T, .cmd c₂ :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
  /-- E-Transition (stable or transient target alike; typing decides what is allowed). -/
  | transition {o σ H T p st ctl r as ss pool D Kc d k s} :
      H p = some d → D d = .at k s →
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, .cmd (.transition p st) :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
        (Kc * (M.transCost k s st + (D.erase d).bg M + ambBg M A)) true
        ⟨⟨o, ⟨σ, H, T, ctl, r⟩ :: as⟩ :: ss, pool, D.set d k st, Kc⟩
  /-- E-Downgrade. -/
  | downgrade {o σ H T p st ctl r as ss pool D Kc d k s} :
      H p = some d → D d = .at k s →
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, .cmd (.downgrade p st) :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
        (Kc * (M.transCost k s st + (D.erase d).bg M + ambBg M A)) true
        ⟨⟨o, ⟨σ, H, T, ctl, r⟩ :: as⟩ :: ss, pool, D.set d k st, Kc⟩
  /-- E-Clock. -/
  | clock {o σ H T f' ctl r as ss pool D Kc} :
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, .cmd (.clock f') :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
        (M.clockCost Kc f' + Kc * (D.bg M + ambBg M A)) true
        ⟨⟨o, ⟨σ, H, T, ctl, r⟩ :: as⟩ :: ss, pool, D, f'⟩
  /-- E-Match-i: the arm for the device's current state. -/
  | matchSt {o σ H T p arms ctl r as ss pool D Kc d k s c} :
      H p = some d → D d = .at k s → arms.find? s = some c →
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, .cmd (.matchSt p arms) :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
        (Kc * (D.bg M + ambBg M A)) true
        ⟨⟨o, ⟨σ, H, T, .cmd c :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
  /-- E-Call: evaluate the argument and push the callee's activation, which sees only the
  device passed as its peripheral parameter. -/
  | call {o σ H T x g e p ctl r as ss pool D Kc dcl v d k s} :
      Ψd g = some dcl → e.eval σ = some v → H p = some d → D d = .at k s →
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, .cmd (.call x g e p) :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
        (Kc * (e.cost M + D.bg M + ambBg M A)) true
        ⟨⟨o, ⟨Mem.empty.set dcl.arg v, fun y => if y = dcl.parg then some d else none,
            fun _ => none, [.cmd dcl.body], some (dcl.ret, x)⟩ ::
          ⟨σ, H, T, ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
  /-- E-Ret: the callee's body is done; evaluate the return expression and resume the caller.
  The device states need no copying back: the store is global. -/
  | ret {o σ H T e x σc Hc Tc ctlc rc as ss pool D Kc v} :
      e.eval σ = some v →
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, [], some (e, x)⟩ :: ⟨σc, Hc, Tc, ctlc, rc⟩ :: as⟩ :: ss,
          pool, D, Kc⟩
        (Kc * (e.cost M + D.bg M + ambBg M A)) true
        ⟨⟨o, ⟨σc.set x v, Hc, Tc, ctlc, rc⟩ :: as⟩ :: ss, pool, D, Kc⟩
  /-- E-Async: spawn a thread on a fresh id, capturing the device and a copy of the memory. -/
  | async {o σ H T tid p c ctl r as ss pool D Kc d k s id} :
      H p = some d → D d = .at k s → pool id = none →
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, .cmd (.async tid p c) :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
        (Kc * (M.spawnCost k s + (D.erase d).bg M + ambBg M A)) true
        ⟨⟨o, ⟨σ, H, Function.update T tid (some id), ctl, r⟩ :: as⟩ :: ss,
          Function.update pool id (some ⟨d, c, σ, p, .pending⟩), D, Kc⟩
  /-- E-AwaitStart. -/
  | awaitStart {o σ H T tid n fb ctl r as ss pool D Kc id} :
      T tid = some id →
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, .cmd (.await tid n fb) :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
        0 false
        ⟨⟨o, ⟨σ, H, T, .awaitW tid id (n : R) fb :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
  /-- E-Await: the thread has finished. -/
  | awaitDone {o σ H T tid id rem fb ctl r as ss pool D Kc e} :
      pool id = some e → e.status = .done →
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, .awaitW tid id rem fb :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
        0 false
        ⟨⟨o, ⟨σ, H, Function.update T tid none, ctl, r⟩ :: as⟩ :: ss,
          Function.update pool id none, D, Kc⟩
  /-- E-AwaitWait: one tick of waiting while the thread has not been scheduled. -/
  | awaitWait {o σ H T tid id rem fb ctl r as ss pool D Kc e} :
      pool id = some e → e.status = .pending → 0 < rem →
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, .awaitW tid id rem fb :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
        (Kc * (D.bg M + ambBg M A)) true
        ⟨⟨o, ⟨σ, H, T, .awaitW tid id rem fb :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
  /-- E-Await-Timeout: the budget is used up before the thread was scheduled; abandon it and run
  the fallback. -/
  | awaitTimeout {o σ H T tid id rem fb ctl r as ss pool D Kc e} :
      pool id = some e → e.status = .pending → rem ≤ 0 →
      Step P M Ψd A ⟨⟨o, ⟨σ, H, T, .awaitW tid id rem fb :: ctl, r⟩ :: as⟩ :: ss, pool, D, Kc⟩
        0 false
        ⟨⟨o, ⟨σ, H, Function.update T tid none, .cmd fb :: ctl, r⟩ :: as⟩ :: ss,
          Function.update pool id none, D, Kc⟩
  /-- E-AsyncPreempt: schedule a pending thread on top of whatever is running.  Its body runs in
  the closure memory and sees only the captured device. -/
  | preempt {ss pool D Kc id e} :
      pool id = some e → e.status = .pending →
      Step P M Ψd A ⟨ss, pool, D, Kc⟩ 0 false
        ⟨⟨some id, [⟨e.σ, fun y => if y = e.p then some e.dev else none, fun _ => none,
            [.cmd e.body], none⟩]⟩ :: ss,
          Function.update pool id (some { e with status := .running }), D, Kc⟩
  /-- E-AsyncDone: a thread's body has finished. -/
  | threadDone {id σ H T ss pool D Kc e} :
      pool id = some e →
      Step P M Ψd A ⟨⟨some id, [⟨σ, H, T, [], none⟩]⟩ :: ss, pool, D, Kc⟩ 0 false
        ⟨ss, Function.update pool id (some { e with status := .done }), D, Kc⟩
  /-- E-Timeout-Running: the awaiter's budget is used up while the thread runs directly above
  it; abandon the thread and run the fallback. -/
  | timeoutRunning {id acts o σ H T tid rem fb ctl r as ss pool D Kc} :
      rem ≤ 0 →
      Step P M Ψd A
        ⟨⟨some id, acts⟩ :: ⟨o, ⟨σ, H, T, .awaitW tid id rem fb :: ctl, r⟩ :: as⟩ :: ss,
          pool, D, Kc⟩ 0 false
        ⟨⟨o, ⟨σ, H, Function.update T tid none, .cmd fb :: ctl, r⟩ :: as⟩ :: ss,
          Function.update pool id none, D, Kc⟩
  /-- E-HWStep: hardware moves a captured device to a state in `HWReach`. -/
  | hw {ss pool D Kc id e k s s'} :
      pool id = some e → e.status ≠ .done → D e.dev = .at k s → s' ∈ P.hwReach k s →
      Step P M Ψd A ⟨ss, pool, D, Kc⟩ 0 false ⟨ss, pool, D.set e.dev k s', Kc⟩

/-- **Steps of the running activation alone**: the rules of `Step` that read and write only the
running thread's activations, the store and the clock — local commands, calls and returns (no
threads, timers or scheduling).  The same costs as `Step`; `ActStep.toStep` embeds them.
Typing proofs reason about these, independently of the other threads and the pool. -/
inductive ActStep (M : CostModel K St R) (Ψd : FCtx K St R) (A : Multiset (K × St)) :
    List (Act St R) → RPeriphs K St → R → R → Bool → List (Act St R) → RPeriphs K St → R →
    Prop where
  | skip {σ H T ctl r as D Kc} :
      ActStep M Ψd A (⟨σ, H, T, .cmd .skip :: ctl, r⟩ :: as) D Kc 0 false
        (⟨σ, H, T, ctl, r⟩ :: as) D Kc
  | seq {σ H T c₁ c₂ ctl r as D Kc} :
      ActStep M Ψd A (⟨σ, H, T, .cmd (.seq c₁ c₂) :: ctl, r⟩ :: as) D Kc 0 false
        (⟨σ, H, T, .cmd c₁ :: .cmd c₂ :: ctl, r⟩ :: as) D Kc
  | assign {σ H T x e v ctl r as D Kc} :
      e.eval σ = some v →
      ActStep M Ψd A (⟨σ, H, T, .cmd (.assign x e) :: ctl, r⟩ :: as) D Kc
        (Kc * (e.cost M + D.bg M + ambBg M A)) true (⟨σ.set x v, H, T, ctl, r⟩ :: as) D Kc
  | iteTrue {σ H T e c₁ c₂ ctl r as D Kc} :
      e.eval σ = some (.bool true) →
      ActStep M Ψd A (⟨σ, H, T, .cmd (.ite e c₁ c₂) :: ctl, r⟩ :: as) D Kc
        (Kc * (e.cost M + D.bg M + ambBg M A)) true (⟨σ, H, T, .cmd c₁ :: ctl, r⟩ :: as) D Kc
  | iteFalse {σ H T e c₁ c₂ ctl r as D Kc} :
      e.eval σ = some (.bool false) →
      ActStep M Ψd A (⟨σ, H, T, .cmd (.ite e c₁ c₂) :: ctl, r⟩ :: as) D Kc
        (Kc * (e.cost M + D.bg M + ambBg M A)) true (⟨σ, H, T, .cmd c₂ :: ctl, r⟩ :: as) D Kc
  | transition {σ H T p st ctl r as D Kc d k s} :
      H p = some d → D d = .at k s →
      ActStep M Ψd A (⟨σ, H, T, .cmd (.transition p st) :: ctl, r⟩ :: as) D Kc
        (Kc * (M.transCost k s st + (D.erase d).bg M + ambBg M A)) true
        (⟨σ, H, T, ctl, r⟩ :: as) (D.set d k st) Kc
  | downgrade {σ H T p st ctl r as D Kc d k s} :
      H p = some d → D d = .at k s →
      ActStep M Ψd A (⟨σ, H, T, .cmd (.downgrade p st) :: ctl, r⟩ :: as) D Kc
        (Kc * (M.transCost k s st + (D.erase d).bg M + ambBg M A)) true
        (⟨σ, H, T, ctl, r⟩ :: as) (D.set d k st) Kc
  | clock {σ H T f' ctl r as D Kc} :
      ActStep M Ψd A (⟨σ, H, T, .cmd (.clock f') :: ctl, r⟩ :: as) D Kc
        (M.clockCost Kc f' + Kc * (D.bg M + ambBg M A)) true (⟨σ, H, T, ctl, r⟩ :: as) D f'
  | matchSt {σ H T p arms ctl r as D Kc d k s c} :
      H p = some d → D d = .at k s → arms.find? s = some c →
      ActStep M Ψd A (⟨σ, H, T, .cmd (.matchSt p arms) :: ctl, r⟩ :: as) D Kc
        (Kc * (D.bg M + ambBg M A)) true (⟨σ, H, T, .cmd c :: ctl, r⟩ :: as) D Kc
  | call {σ H T x g e p ctl r as D Kc dcl v d k s} :
      Ψd g = some dcl → e.eval σ = some v → H p = some d → D d = .at k s →
      ActStep M Ψd A (⟨σ, H, T, .cmd (.call x g e p) :: ctl, r⟩ :: as) D Kc
        (Kc * (e.cost M + D.bg M + ambBg M A)) true
        (⟨Mem.empty.set dcl.arg v, fun y => if y = dcl.parg then some d else none,
            fun _ => none, [.cmd dcl.body], some (dcl.ret, x)⟩ :: ⟨σ, H, T, ctl, r⟩ :: as) D Kc
  | ret {σ H T e x σc Hc Tc ctlc rc as D Kc v} :
      e.eval σ = some v →
      ActStep M Ψd A (⟨σ, H, T, [], some (e, x)⟩ :: ⟨σc, Hc, Tc, ctlc, rc⟩ :: as) D Kc
        (Kc * (e.cost M + D.bg M + ambBg M A)) true (⟨σc.set x v, Hc, Tc, ctlc, rc⟩ :: as) D Kc

/-- Steps of the running activation are machine steps, whatever the other threads, the pool
and the segment owner. -/
theorem ActStep.toStep {P : Platform K St} {M : CostModel K St R} {Ψd : FCtx K St R}
    {A : Multiset (K × St)} {acts D Kc q tick acts' D' K'}
    (h : ActStep M Ψd A acts D Kc q tick acts' D' K') (o : Option ThreadId)
    (ss : List (Seg St R)) (pool : ThreadId → Option (PoolEntry St R)) :
    Step P M Ψd A ⟨⟨o, acts⟩ :: ss, pool, D, Kc⟩ q tick ⟨⟨o, acts'⟩ :: ss, pool, D', K'⟩ := by
  cases h with
  | skip => exact .skip
  | seq => exact .seq
  | assign hev => exact .assign hev
  | iteTrue hev => exact .iteTrue hev
  | iteFalse hev => exact .iteFalse hev
  | transition hH hD => exact .transition hH hD
  | downgrade hH hD => exact .downgrade hH hD
  | clock => exact .clock
  | matchSt hH hD hf => exact .matchSt hH hD hf
  | call hg hev hH hD => exact .call hg hev hH hD
  | ret hev => exact .ret hev

variable [Sub R]

/-- E-Step: a step, followed by draining the waiting timers by the clock in force before the
step if it took a time step. -/
def MStep (P : Platform K St) (M : CostModel K St R) (Ψd : FCtx K St R)
    (A : Multiset (K × St)) (c : Config K St R) (q : R) (c' : Config K St R) : Prop :=
  ∃ tick c₁, Step P M Ψd A c q tick c₁ ∧ c' = if tick then c₁.drain c.K else c₁

/-- Multi-step runs, accumulating cost. -/
inductive Steps (P : Platform K St) (M : CostModel K St R) (Ψd : FCtx K St R)
    (A : Multiset (K × St)) : Config K St R → R → Config K St R → Prop where
  | refl {c} : Steps P M Ψd A c 0 c
  | step {c q c₁ q' c₂} :
      MStep P M Ψd A c q c₁ → Steps P M Ψd A c₁ q' c₂ → Steps P M Ψd A c (q + q') c₂

/-- A finished configuration: only `main`'s base activation is left, with nothing to do. -/
def Config.Final (c : Config K St R) : Prop :=
  ∃ σ H T, c.segs = [⟨none, [⟨σ, H, T, [], none⟩]⟩]

namespace Program

/-- The initial configuration: `main` in the empty memory, each declared handle naming its own
device in its initial state, no threads, clock `K₀`. -/
noncomputable def initConfig (prog : Program K St R) (K₀ : R) : Config K St R :=
  ⟨[⟨none, [⟨Mem.empty, some, fun _ => none, [.cmd prog.main], none⟩]⟩], fun _ => none,
    prog.initPeriphs, K₀⟩

/-- Running a whole program on the machine from clock `K₀` to a final configuration, at total
cost `q`. -/
def MRun (P : Platform K St) (M : CostModel K St R) (prog : Program K St R) (K₀ : R)
    (c : Config K St R) (q : R) : Prop :=
  Steps P M prog.fctx 0 (prog.initConfig K₀) q c ∧ c.Final

end Program
