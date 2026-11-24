import Heliod.Syntax
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union

/-!
# Cost model

The paper assumes cost functions
* `cost(sᵢ, sⱼ)` — transition cost (upward when `sᵢ ≤ sⱼ`, downward for a downgrade `sⱼ ↪ sᵢ`),
* `cost(sᵢ)` — cost of being in state `sᵢ` (declared as `cᵢ`, with background cost `cbᵢ`),
* `cost(Δ)` — total cost of every peripheral being in its most expensive possible
  background state,
* `cost(f, f')` / `C_clock` — cost of changing the clock frequency,
* `C_spawn` — cost of spawning an async operation,
* (implicitly) the expression cost `q_e` in T-Let / T-If / T-Call,

and states that "all of the costs are scaled by the current clock frequency `f`".

## Design choices

* **Abstract cost domain** (assumptions introduced where needed, see the `variable` note).  Costs and frequencies live in an arbitrary `R` that is a
  commutative semiring with a linear order, ordered-ring compatibility, and canonical order
  (`a ≤ b ↔ ∃ c, b = a + c`).  The last makes every cost non-negative and gives `⊥ = 0`, which
  is what lets us take maxima over (possibly empty) finite sets with `Finset.sup`.
  Instances include `ℕ` and `ℚ≥0`.
* **Costs are attached to kinds**, not to handles: two sensors of the same kind cost the same.
* **Expression costs are explicit.**  The paper never says what `q_e` is; we charge a constant
  per variable read, per literal and per operator.
* **Frequency scaling is multiplication**: a cost `q` incurred at clock `f` contributes `f * q`.
  The helpers below are unscaled; the typing rules multiply by `f`.
* **Monotonicity assumption on clock-change cost** (`CostModel.WF`).  After a branch the paper
  joins clocks with `max(f₁, f₂)`.  A later `clock g` is then charged `cost(max(f₁,f₂), g)`,
  which is only an upper bound on the true `cost(fᵢ, g)` if clock-change cost is monotone in
  its source frequency.  Multiplicative scaling is monotone automatically in this domain.
-/

/-- The cost annotations of a program, for peripheral kinds `K`, states `St`, domain `R`.

* `stateCost k s` — `cᵢ`, cost of a peripheral of kind `k` actively being in state `s`
  (currently unused: T-Await charges a captured peripheral's background cost, see
  `PAPER_DIFFERENCES.md` section 5.5);
* `bgCost k s` — `cbᵢ`, background cost of state `s` (used by `cost(Δ)`);
* `transCost k s s'` — `cost(s, s')`, used for both `transition` and `downgrade`;
* `varCost`, `valCost`, `binopCost op` — expression evaluation costs;
* `clockCost f f'` — cost of `clock f'` when the current clock is `f`;
* `spawnCost k s` — `C_spawn`, cost of starting an async operation on a peripheral in `s`. -/
structure CostModel (K St R : Type) where
  stateCost : K → St → R
  bgCost : K → St → R
  transCost : K → St → St → R
  varCost : R
  valCost : R
  binopCost : BinOp → R
  clockCost : R → R → R
  spawnCost : K → St → R

namespace CostModel

variable {K St R : Type}
/- The helpers in this file only need maxima over finite sets, i.e. a linear order with `⊥`.
The full cost-domain assumptions
  `[CommSemiring R] [LinearOrder R] [IsOrderedRing R] [CanonicallyOrderedAdd R] [OrderBot R]`
are introduced by the typing/soundness files that actually scale and add costs.
(Mathlib does not derive `OrderBot` from `CanonicallyOrderedAdd`; it is a separate instance,
provably equal to `0` via `bot_eq_zero'`.  `ℕ` and `ℚ≥0` both provide it.) -/
variable [LinearOrder R] [OrderBot R]

/-- Assumptions on a cost model needed for soundness of the clock join (see module doc). -/
structure WF (M : CostModel K St R) : Prop where
  clockCost_mono_left : ∀ f₁ f₂ g : R, f₁ ≤ f₂ → M.clockCost f₁ g ≤ M.clockCost f₂ g

/-- `max_{s ∈ S} cbₛ`: the background cost of a peripheral of kind `k` known only to be in one
of the states `S` (the per-peripheral summand of the paper's `cost(Δ)`).  Empty `S` gives `0`. -/
def maxBg (M : CostModel K St R) (k : K) (S : Finset St) : R :=
  S.sup (M.bgCost k)

/-- `max_{s ∈ S} cost(s, st)`: worst-case cost of moving a peripheral of kind `k` from some
state in `S` to `st` (the `max(cost(sᵢ, st))` of T-Transition / T-Downgrade). -/
def maxTrans (M : CostModel K St R) (k : K) (S : Finset St) (st : St) : R :=
  S.sup (fun s => M.transCost k s st)

/-- `max_{s ∈ S} C_spawn(k, s)`: worst-case spawn cost (the paper's typing rule uses a constant
`cost(async spawn)`, the semantics uses `C_spawn(p, S(p), K)`; we bound the latter). -/
def maxSpawn (M : CostModel K St R) (k : K) (S : Finset St) : R :=
  S.sup (M.spawnCost k)

/-- `C_unstable(p : S)`: the worst active cost over every state a captured peripheral may be in,
i.e. `max_{s ∈ S ∪ HWReach(S)} cₛ`.  Not used by the rules: T-Await charges `maxBg` over the
captured states (see `PAPER_DIFFERENCES.md` section 5.5). -/
def unstableCost [DecidableEq St] (P : Platform K St) (M : CostModel K St R) (k : K)
    (S : Finset St) : R :=
  (S ∪ S.biUnion (P.hwReach k)).sup (M.stateCost k)

/-- Any single state's background cost is bounded by the max.  This is the basic fact that
lets the static `cost(Δ)` dominate the dynamic `bg(S)` when the actual state is in `Δ(p)`. -/
theorem bgCost_le_maxBg (M : CostModel K St R) {k : K} {S : Finset St} {s : St} (h : s ∈ S) :
    M.bgCost k s ≤ M.maxBg k S :=
  Finset.le_sup (f := M.bgCost k) h

/-- `maxBg` is monotone in the state set: a less precise typestate yields a larger (still
sound) background bound.  Needed when joining peripheral contexts after branches. -/
theorem maxBg_mono (M : CostModel K St R) {k : K} {S T : Finset St} (h : S ⊆ T) :
    M.maxBg k S ≤ M.maxBg k T :=
  Finset.sup_mono (f := M.bgCost k) h

/-- Transition analogue of `bgCost_le_maxBg`: the actual transition cost is bounded by the
static worst case whenever the actual source state is among the possible ones. -/
theorem transCost_le_maxTrans (M : CostModel K St R) {k : K} {S : Finset St} {s st : St}
    (h : s ∈ S) : M.transCost k s st ≤ M.maxTrans k S st :=
  Finset.le_sup (f := fun s => M.transCost k s st) h

/-- `maxTrans` is monotone in the source-state set (cf. `maxBg_mono`). -/
theorem maxTrans_mono (M : CostModel K St R) {k : K} {S T : Finset St} (st : St) (h : S ⊆ T) :
    M.maxTrans k S st ≤ M.maxTrans k T st :=
  Finset.sup_mono (f := fun s => M.transCost k s st) h

end CostModel
