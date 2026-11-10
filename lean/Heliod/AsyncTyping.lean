import Heliod.Typing

/-!
# Typing with async / await (hardware concurrency)

`TypedA` extends the synchronous judgment `Typed` with the paper's T-AsyncFun,
T-Await-Timeout and T-Transition-Unstable, following the design agreed with the user
(2026-11-08); departures from the paper are listed in `TODO.md`.

`TypedA P M Ψ fz Γ Δ Θ c Γ' Δ' Θ' W Q F` reads: with clock changes forbidden if `fz`
("frozen"), starting from value context `Γ`, peripheral context `Δ` and **thread context** `Θ`,
`c` ends with `Γ'`, `Δ'`, `Θ'`; `W` is the join of every peripheral context `c` passes through
(its **visited** context); `Q f b` and `F f` are the cost and clock summaries as in `Typed`.

## An async block is a closure that runs concurrently

`let tid = async(p) { c }` captures the handle `p` and the values its body reads (the body runs
in its own memory frame, like a function body, so there is no shared memory).  The body `c` is
typed **once**, from `p`'s states at spawn, with summary `Q_a`.  Unlike a call, the body runs
interleaved with the main thread until `await tid`:

* **Paid at the spawn, against a declared window bound.**  The body's steps pay the
  background of the main thread's peripherals, whose states change during the window.  The
  spawn charges the body's summary `Q_a f (b + amb)` — a closure call paid for when the closure
  is created — where `amb` is a declared bound on that window ambient.  Each pending thread's
  entry in `Θ` accumulates `win`, the join of every main-thread context since the spawn
  (`ThreadCtx.observe`, applied wherever `Δ` changes), and the await checks
  `cost(win ∖ p) ≤ amb`.  The tightest choice is `amb = cost(win ∖ p)`.  (Paying at the spawn
  rather than step by step does not change the total cost; it lets the soundness proof give a
  pending thread its own reserved budget.)
* **The captured peripheral.**  While captured, `p` may be in any state the body visits or that
  hardware reaches from one: `V = HWReach-closure(W_body(p))`.  The main thread sees `Δ(p) = V`,
  so its steps charge `p` at `maxBg V`; it may not use `p` (`¬ Θ.Captures p`).
* **The clock is frozen while a thread is pending.**  The body may not change the clock (it is
  typed with `fz = true`), and neither may the main thread while `Θ` is nonempty; calls in a
  frozen setting must go to functions marked `stableClock`.  So the whole window runs at the
  spawn clock `f`.
* **Await.**  `await tid timeout[n] { c_fb }` costs at most `n + f` worth of waiting ticks
  (`⌈n/K⌉` ticks of length `K` each), plus the fallback, which is typed from
  `p ∈ V` (after a timeout the body may have stopped anywhere).  The result joins the body's
  exit states with the fallback's.
* **Hardware steps.**  T-Transition-Unstable moves `p` to `hwClose {st} = {st} ∪ HWReach(st)`;
  a `match` arm for `st` narrows `p` to `hwClose {st}` (hardware may move a captured peripheral
  right after the match).  For stable `st` this is `{st}`.

Functions (`FunSigA`) additionally record `visit`, the states their peripheral parameter may
occupy during the call (needed to observe a call into pending threads' windows), and
`stableClock` (the body never changes the clock).
-/

variable {K St R : Type} [DecidableEq K] [DecidableEq St]

/-- Function signatures for the async language: a synchronous `FunSig` plus the states the
peripheral parameter may visit during the call and whether the call keeps the clock fixed. -/
structure FunSigA (K St R : Type) extends FunSig K St R where
  visit : Finset St
  stableClock : Bool

/-- Signature context for the async language. -/
abbrev SigCtxA (K St R : Type) := FName → Option (FunSigA K St R)

/-- The type of a pending thread `tid`: the captured handle `p` (of kind `k`), the states `V` it
may occupy while captured, the body's exit states `sOut`, the declared bound `amb` on the
window ambient (the body was charged at the spawn assuming its other peripherals cost at most
`amb`), and `win`, the join of the main thread's contexts since the spawn. -/
structure ThreadTy (K St R : Type) where
  p : Var
  k : K
  V : Finset St
  sOut : Finset St
  amb : R
  win : PCtx K St

/-- Thread context `Θ`: the pending threads. -/
abbrev ThreadCtx (K St R : Type) := Var → Option (ThreadTy K St R)

/-- Two thread types describe the same spawned thread (they may differ only in `win`). -/
def ThreadTy.Same (a b : ThreadTy K St R) : Prop :=
  a.p = b.p ∧ a.k = b.k ∧ a.V = b.V ∧ a.sOut = b.sOut ∧ a.amb = b.amb

namespace ThreadCtx

/-- No pending threads. -/
def empty : ThreadCtx K St R := fun _ => none

/-- `Θ` has no pending threads. -/
def IsEmpty (Θ : ThreadCtx K St R) : Prop := ∀ t, Θ t = none

/-- Handle `p` is captured by some pending thread. -/
def Captures (Θ : ThreadCtx K St R) (p : Var) : Prop := ∃ t th, Θ t = some th ∧ th.p = p

/-- Record that the main thread passed through context `Δ` in every pending thread's window. -/
noncomputable def observe (Θ : ThreadCtx K St R) (Δ : PCtx K St) : ThreadCtx K St R :=
  fun t => (Θ t).map fun th => { th with win := th.win.join Δ }

/-- Remove thread `t` (it has been awaited). -/
def erase (Θ : ThreadCtx K St R) (t : Var) : ThreadCtx K St R := Function.update Θ t none

/-- Branches agree on which threads are pending. -/
def SameThreads (Θ₁ Θ₂ : ThreadCtx K St R) : Prop :=
  ∀ t, (Θ₁ t = none ∧ Θ₂ t = none) ∨ ∃ a b, Θ₁ t = some a ∧ Θ₂ t = some b ∧ a.Same b

/-- Join after a branch: windows are joined (the body may have overlapped either branch). -/
noncomputable def join (Θ₁ Θ₂ : ThreadCtx K St R) : ThreadCtx K St R :=
  fun t => match Θ₁ t, Θ₂ t with
    | some a, some b => some { a with win := a.win.join b.win }
    | _, _ => none

end ThreadCtx

variable [CommSemiring R] [LinearOrder R] [OrderBot R]

mutual

/-- Command typing with async / await; see the module doc. -/
inductive TypedA (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtxA K St R) :
    Bool → TCtx K → PCtx K St → ThreadCtx K St R → Cmd St R →
    TCtx K → PCtx K St → ThreadCtx K St R → PCtx K St → (R → R → R) → (R → R) → Prop where
  | skip {fz Γ Δ Θ} :
      TypedA P M Ψ fz Γ Δ Θ .skip Γ Δ Θ Δ (fun _ _ => 0) (fun f => f)
  | assign {fz Γ Δ Θ x e τ} :
      HasTy Γ e τ → Δ x = 0 →
      TypedA P M Ψ fz Γ Δ Θ (.assign x e) (Γ.bind x τ) Δ Θ Δ
        (fun f b => f * (e.cost M + Δ.bg M + b)) (fun f => f)
  | ite {fz Γ Δ Θ e c₁ c₂ Γ₁ Δ₁ Θ₁ W₁ Q₁ F₁ Γ₂ Δ₂ Θ₂ W₂ Q₂ F₂} :
      HasTy Γ e .bool →
      TypedA P M Ψ fz Γ Δ Θ c₁ Γ₁ Δ₁ Θ₁ W₁ Q₁ F₁ →
      TypedA P M Ψ fz Γ Δ Θ c₂ Γ₂ Δ₂ Θ₂ W₂ Q₂ F₂ →
      Θ₁.SameThreads Θ₂ →
      TypedA P M Ψ fz Γ Δ Θ (.ite e c₁ c₂) (Γ₁.inter Γ₂) (Δ₁.join Δ₂) (Θ₁.join Θ₂)
        (W₁.join W₂)
        (fun f b => max (Q₁ f b) (Q₂ f b) + f * (e.cost M + Δ.bg M + b))
        (fun f => max (F₁ f) (F₂ f))
  /-- T-Transition, stable target. -/
  | transition {fz Γ Δ Θ p k S st} :
      Δ p = .live k S → ¬ Θ.Captures p → P.stable k st → (∀ s ∈ S, P.le k s st) →
      TypedA P M Ψ fz Γ Δ Θ (.transition p st) Γ (Δ.set p k {st})
        (Θ.observe (Δ.set p k {st})) (Δ.join (Δ.set p k {st}))
        (fun f b => f * (M.maxTrans k S st + (Δ.erase p).bg M + b)) (fun f => f)
  /-- T-Transition-Unstable: the target is transient, so hardware may move the peripheral on
  to any state in `HWReach(st)`. -/
  | transitionU {fz Γ Δ Θ p k S st} :
      Δ p = .live k S → ¬ Θ.Captures p → P.unstable k st → (∀ s ∈ S, P.le k s st) →
      TypedA P M Ψ fz Γ Δ Θ (.transition p st) Γ (Δ.set p k (P.hwClose k {st}))
        (Θ.observe (Δ.set p k (P.hwClose k {st}))) (Δ.join (Δ.set p k (P.hwClose k {st})))
        (fun f b => f * (M.maxTrans k S st + (Δ.erase p).bg M + b)) (fun f => f)
  | downgrade {fz Γ Δ Θ p k S st} :
      Δ p = .live k S → ¬ Θ.Captures p → P.stable k st → (∀ s ∈ S, P.dg k s st) →
      TypedA P M Ψ fz Γ Δ Θ (.downgrade p st) Γ (Δ.set p k {st})
        (Θ.observe (Δ.set p k {st})) (Δ.join (Δ.set p k {st}))
        (fun f b => f * (M.maxTrans k S st + (Δ.erase p).bg M + b)) (fun f => f)
  /-- T-Clock: only when not frozen and no thread is pending. -/
  | clock {fz Γ Δ Θ f'} :
      fz = false → Θ.IsEmpty → 0 < f' →
      TypedA P M Ψ fz Γ Δ Θ (.clock f') Γ Δ Θ Δ
        (fun f b => M.clockCost f f' + f * (Δ.bg M + b)) (fun _ => f')
  | seq {fz Γ Δ Θ c₁ c₂ Γ₁ Δ₁ Θ₁ W₁ Q₁ F₁ Γ₂ Δ₂ Θ₂ W₂ Q₂ F₂} :
      TypedA P M Ψ fz Γ Δ Θ c₁ Γ₁ Δ₁ Θ₁ W₁ Q₁ F₁ →
      TypedA P M Ψ fz Γ₁ Δ₁ Θ₁ c₂ Γ₂ Δ₂ Θ₂ W₂ Q₂ F₂ →
      TypedA P M Ψ fz Γ Δ Θ (.seq c₁ c₂) Γ₂ Δ₂ Θ₂ (W₁.join W₂)
        (fun f b => Q₁ f b + Q₂ (F₁ f) b) (fun f => F₂ (F₁ f))
  | matchSt {fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F} :
      Δ p = .live k S → ¬ Θ.Captures p → S ⊆ arms.states →
      ArmsTypedA P M Ψ fz Γ Δ Θ p k S arms Γ' Δ' Θ' W Q F →
      TypedA P M Ψ fz Γ Δ Θ (.matchSt p arms) Γ' Δ' Θ' (Δ.join W) Q F
  /-- T-Call.  The callee's parameter may pass through `sig.visit` during the call, which
  pending threads observe; in a frozen setting the callee must keep the clock fixed. -/
  | call {fz Γ Δ Θ x g e p sig S} :
      Ψ g = some sig →
      HasTy Γ e sig.argTy →
      Δ x = 0 →
      Δ p = .live sig.pKind S → S ⊆ sig.sIn →
      ¬ Θ.Captures p →
      (fz = true ∨ ¬ Θ.IsEmpty → sig.stableClock = true) →
      TypedA P M Ψ fz Γ Δ Θ (.call x g e p) (Γ.bind x sig.retTy) (Δ.set p sig.pKind sig.sOut)
        ((Θ.observe (Δ.set p sig.pKind sig.visit)).observe (Δ.set p sig.pKind sig.sOut))
        ((Δ.join (Δ.set p sig.pKind sig.visit)).join (Δ.set p sig.pKind sig.sOut))
        (fun f b => f * (e.cost M + Δ.bg M + b) + sig.cost f (b + (Δ.erase p).bg M)) sig.clk
  /-- T-AsyncFun.  The body is typed once, frozen, from `p`'s (transient, HW-closed) states,
  seeing only `p`; it must end stable with no pending threads.  Like a closure whose cost is
  paid when it is created, the spawn charges the body's summary `Q_a f (b + amb)`, where `amb`
  is a declared bound on the background of the peripherals the body cannot see during the
  window (checked at the await).  The main thread continues with `p` captured, in the states
  `V` the body may visit (closed under hardware steps). -/
  -- `fz = false`: frozen code (async bodies, and functions called while a thread is pending)
  -- cannot spawn; no nested threads (design decision 2026-11-09, simplification 1).
  | async {fz Γ Δ Θ tid p k S c Γb Δb Wb Qa Fa Sout Wp amb} :
      Δ p = .live k S → ¬ Θ.Captures p → Θ tid = none →
      (∀ s ∈ S, P.unstable k s) → P.hwClose k S = S →
      TypedA P M Ψ true Γ (Finsupp.single p (.live k S)) ThreadCtx.empty c
        Γb Δb ThreadCtx.empty Wb Qa Fa →
      Δb p = .live k Sout → (∀ s ∈ Sout, P.stable k s) →
      Wb p = .live k Wp →
      fz = false →
      TypedA P M Ψ fz Γ Δ Θ (.async tid p c) Γ (Δ.set p k (P.hwClose k Wp))
        (Function.update (Θ.observe (Δ.set p k (P.hwClose k Wp))) tid
          (some ⟨p, k, P.hwClose k Wp, Sout, amb, Δ.set p k (P.hwClose k Wp)⟩))
        (Δ.join (Δ.set p k (P.hwClose k Wp)))
        (fun f b => f * (M.maxSpawn k S + (Δ.erase p).bg M + b) + Qa f (b + amb)) (fun f => f)
  /-- T-Await-Timeout.  The window ambient must fit the bound declared at the spawn
  (`cost(win ∖ p) ≤ amb`).  Cost: at most `n + f` worth of waiting ticks with `p` at its worst
  captured state, plus the fallback, which is typed from `p ∈ V` and must end stable (the body
  itself was paid for at the spawn).  The result joins the body's exit states (success) with
  the fallback's (timeout). -/
  | await {fz Γ Δ Θ tid n fb th Γf Δf Θf Wf Qf Ff Sfb} :
      Θ tid = some th → Δ th.p = .live th.k th.V →
      (th.win.erase th.p).bg M ≤ th.amb →
      TypedA P M Ψ fz Γ Δ (Θ.erase tid) fb Γf Δf Θf Wf Qf Ff →
      (Θ.erase tid).SameThreads Θf →
      Δf th.p = .live th.k Sfb → (∀ s ∈ Sfb, P.stable th.k s) →
      TypedA P M Ψ fz Γ Δ Θ (.await tid n fb) (Γ.inter Γf)
        ((Δ.set th.p th.k th.sOut).join Δf)
        (((Θ.erase tid).observe (Δ.set th.p th.k th.sOut)).join Θf)
        ((Δ.join (Δ.set th.p th.k th.sOut)).join Wf)
        (fun f b => ((n : R) + f) * (M.maxBg th.k th.V + (Δ.erase th.p).bg M + b) + Qf f b)
        (fun f => max (Ff f) f)

/-- Arms of a `match` in the async language: as `ArmsTyped`, with `p` narrowed to
`hwClose {st}` in the arm for `st`, and thread contexts joined across arms. -/
inductive ArmsTypedA (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtxA K St R) :
    Bool → TCtx K → PCtx K St → ThreadCtx K St R → Var → K → Finset St → Arms St R →
    TCtx K → PCtx K St → ThreadCtx K St R → PCtx K St → (R → R → R) → (R → R) → Prop where
  | last {fz Γ Δ Θ p k S st c rest Γ' Δ' Θ' W Q F} :
      st ∈ S →
      TypedA P M Ψ fz Γ (Δ.set p k (P.hwClose k {st}))
        (Θ.observe (Δ.set p k (P.hwClose k {st}))) c Γ' Δ' Θ' W Q F →
      (∀ s ∈ rest.states, s ∉ S) →
      ArmsTypedA P M Ψ fz Γ Δ Θ p k S (.cons st c rest) Γ' Δ' Θ' W
        (fun f b => Q f b + f * ((Δ.set p k (P.hwClose k {st})).bg M + b)) F
  | cons {fz Γ Δ Θ p k S st c rest Γ₁ Δ₁ Θ₁ W₁ Q₁ F₁ Γ₂ Δ₂ Θ₂ W₂ Q₂ F₂} :
      st ∈ S →
      TypedA P M Ψ fz Γ (Δ.set p k (P.hwClose k {st}))
        (Θ.observe (Δ.set p k (P.hwClose k {st}))) c Γ₁ Δ₁ Θ₁ W₁ Q₁ F₁ →
      ArmsTypedA P M Ψ fz Γ Δ Θ p k S rest Γ₂ Δ₂ Θ₂ W₂ Q₂ F₂ →
      Θ₁.SameThreads Θ₂ →
      ArmsTypedA P M Ψ fz Γ Δ Θ p k S (.cons st c rest) (Γ₁.inter Γ₂) (Δ₁.join Δ₂)
        (Θ₁.join Θ₂) (W₁.join W₂)
        (fun f b => max (Q₁ f b + f * ((Δ.set p k (P.hwClose k {st})).bg M + b)) (Q₂ f b))
        (fun f => max (F₁ f) (F₂ f))
  | skip {fz Γ Δ Θ p k S st c rest Γ' Δ' Θ' W Q F} :
      st ∉ S →
      ArmsTypedA P M Ψ fz Γ Δ Θ p k S rest Γ' Δ' Θ' W Q F →
      ArmsTypedA P M Ψ fz Γ Δ Θ p k S (.cons st c rest) Γ' Δ' Θ' W Q F

end

/-- T-FunDecl for the async language.  The body starts and ends with no pending threads (a
function cannot leave a thread running); it is frozen iff the signature promises a fixed clock;
`visit` covers every state the parameter passes through.  Its input and output states must be
closed under hardware steps (`HWReach`), so that the function is sound even when called from an
async body on the captured peripheral (design decision 2026-11-09, option A). -/
structure FunDeclTypedA (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtxA K St R)
    (d : FunDecl K St R) (sig : FunSigA K St R) : Prop where
  argTy : sig.argTy = d.argTy
  pKind : sig.pKind = d.pKind
  sIn : sig.sIn = d.sIn
  retTy : sig.retTy = d.retTy
  sOut : sig.sOut = d.sOut
  body : ∃ Γb Δb Wb Qb Fb S' Sv,
    TypedA P M Ψ sig.stableClock (TCtx.empty.bind d.arg d.argTy)
      (Finsupp.single d.parg (.live d.pKind d.sIn)) ThreadCtx.empty d.body
      Γb Δb ThreadCtx.empty Wb Qb Fb ∧
    HasTy Γb d.ret d.retTy ∧ Δb d.parg = .live d.pKind S' ∧ S' ⊆ d.sOut ∧
    Wb d.parg = .live d.pKind Sv ∧ Sv ⊆ sig.visit ∧
    sig.cost = (fun f b => Qb f b + Fb f * (d.ret.cost M + Δb.bg M + b)) ∧ sig.clk = Fb
  /-- The input states are closed under hardware steps: if the body runs on a captured
  peripheral (called from an async body), hardware may move it at any time. -/
  sInClosed : P.hwClose d.pKind d.sIn = d.sIn
  /-- The output states are closed under hardware steps, for the same reason. -/
  sOutClosed : P.hwClose d.pKind d.sOut = d.sOut

/-- Declarations typed in order (async language). -/
inductive DeclsTypedA (P : Platform K St) (M : CostModel K St R) :
    SigCtxA K St R → List (FunDecl K St R) → SigCtxA K St R → Prop where
  | nil {Ψ} : DeclsTypedA P M Ψ [] Ψ
  | cons {Ψ d ds sig Ψ'} :
      FunDeclTypedA P M Ψ d sig →
      DeclsTypedA P M (Function.update Ψ d.name (some sig)) ds Ψ' →
      DeclsTypedA P M Ψ (d :: ds) Ψ'

/-- A well-typed program in the async language: distinct function names, declarations typed in
order, and `main` typed (not frozen) from the initial contexts with no pending threads at the
start or the end. -/
def Program.TypedA (P : Platform K St) (M : CostModel K St R) (prog : Program K St R)
    (Ψ : SigCtxA K St R) (Γ' : TCtx K) (Δ' W : PCtx K St) (Q : R → R → R) (F : R → R) :
    Prop :=
  (prog.funs.map (·.name)).Nodup ∧
  DeclsTypedA P M (fun _ => none) prog.funs Ψ ∧
  _root_.TypedA P M Ψ false TCtx.empty prog.initPCtx ThreadCtx.empty prog.main Γ' Δ'
    ThreadCtx.empty W Q F
