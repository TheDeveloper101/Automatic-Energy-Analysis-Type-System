import Mathlib.Data.Finset.Basic

/-!
# Peripheral declarations (the "platform")

Paper (`typing.tex`, grammar of peripheral declarations):

  `id { ⟨s₀ : {c₀, cb₀}, …, sₙ : {cₙ, cbₙ}⟩, <, D }`

i.e. a peripheral declaration names a set of states, each annotated with an active cost `cᵢ`
and a background cost `cbᵢ`, a transition order `<`, and a downgrade policy `D`.  The async
extension additionally assumes predicates `stable` / `unstable` and a function `HWReach`.

## Design choices (not fixed by the paper)

* **Kinds vs. handles.**  A declaration `id {…}` introduces a *peripheral kind* `k : K`
  (like an Abacus typestate type).  Programs manipulate *handles*: variables bound in the
  peripheral context `Δ` together with their kind (see `Heliod.Contexts`).  This lets a
  function `fn f(x, p)` be used with any handle of the right kind.
* **One global state namespace.**  States are drawn from a single type `St`; each kind `k`
  carves out its carrier `states k : Finset St`.  This avoids dependent types
  (`State : K → Type`) and the casts they would require at call sites, at the price of the
  well-formedness conditions in `Platform.WF`.
* **Costs are separate.**  The `cᵢ`/`cbᵢ` annotations live in `Heliod.CostModel`, so the
  platform only carries the order-theoretic / typestate structure.
* **Order instead of lattice.**  The paper says "lattice" but only ever uses `≤`, the unique
  `⊤`, and downgrades; no joins/meets of states are needed.  We therefore require a partial
  order with a top element on each carrier.
-/

/-- The peripheral kinds of a program together with their typestate structure.

* `states k` — the carrier of kind `k`'s state order (`⟨s₀,…,sₙ⟩`).
* `le k s s'` — `s ≤ s'`: a peripheral of kind `k` in state `s` may `transition` to `s'`.
* `top k`     — the unique `⊤` element of the order.
* `dg k s' s` — the downgrade policy `D`: `s' ↪ s` (a `downgrade` from `s'` to `s` is allowed).
* `stable k s` — `s` is a stable (non-transient) state; `unstable` is its negation.
* `hwReach k s` — `HWReach(s)`: the states hardware may move the peripheral to from `s`
  while it is captured by an async operation. -/
structure Platform (K St : Type) where
  states : K → Finset St
  le : K → St → St → Prop
  top : K → St
  dg : K → St → St → Prop
  stable : K → St → Prop
  hwReach : K → St → Finset St

namespace Platform

variable {K St : Type}

/-- A state is *unstable* (transient) iff it is not stable.  The paper defines a state to be
transient when it has at least one hardware-initiated outgoing transition; we take `stable`
as primitive and derive `unstable`, so the two are exhaustive and exclusive by construction. -/
def unstable (P : Platform K St) (k : K) (s : St) : Prop := ¬ P.stable k s

/-- Well-formedness of a platform: the conditions the paper states in prose.

* `le` is a partial order on `states k` with top `top k`, and only relates members of the
  carrier (so `transition` can never leave the declared state set);
* a downgrade `s' ↪ s` requires `s < s'` ("assuming that `s' > s`") — both are then members;
* `HWReach` stays inside the carrier and is empty on stable states ("`HWReach(st)` for a
  stable state `st` is the empty set").

**Open question (flagged, not imposed):** the prose says `HWReach(st)` is "the set of all
reachable transient states", which would force every state in `HWReach` to be unstable.
That would make it impossible for hardware alone to return a peripheral to a stable state,
so we do *not* require it here; T-AsyncFun's "body ends stable" premise is what guarantees
stability at the end of an async block. -/
structure WF (P : Platform K St) : Prop where
  le_refl : ∀ k s, s ∈ P.states k → P.le k s s
  le_trans : ∀ k s₁ s₂ s₃, P.le k s₁ s₂ → P.le k s₂ s₃ → P.le k s₁ s₃
  le_antisymm : ∀ k s₁ s₂, P.le k s₁ s₂ → P.le k s₂ s₁ → s₁ = s₂
  le_mem : ∀ k s₁ s₂, P.le k s₁ s₂ → s₁ ∈ P.states k ∧ s₂ ∈ P.states k
  top_mem : ∀ k, P.top k ∈ P.states k
  le_top : ∀ k s, s ∈ P.states k → P.le k s (P.top k)
  dg_lt : ∀ k s' s, P.dg k s' s → P.le k s s' ∧ s ≠ s'
  hwReach_sub : ∀ k s, P.hwReach k s ⊆ P.states k
  hwReach_stable : ∀ k s, P.stable k s → P.hwReach k s = ∅

/-- Downgrade sources and targets are declared states.  Used later to show that typing keeps
every peripheral's possible-state set inside its carrier. -/
theorem WF.dg_mem {P : Platform K St} (hP : P.WF) {k : K} {s' s : St} (h : P.dg k s' s) :
    s ∈ P.states k ∧ s' ∈ P.states k :=
  hP.le_mem k s s' (hP.dg_lt k s' s h).1

end Platform
