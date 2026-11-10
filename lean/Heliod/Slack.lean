import Heliod.Soundness

/-!
# Slack: where, and by how much, the cost summaries over-approximate

Soundness says every run costs *at most* the summary `Q K (bg A)`.  This file makes the gap
exact: along any control-flow path (in particular any real execution), the summary is the
path's cost plus a list of **slack terms**, each recorded at a specific program point, with an
explicit formula and one of a fixed set of kinds:

  `Q K (bg A) = cost(path) + Σ δᵢ`.

See `IMPRECISION.md` for the examples behind each kind and the discussion of necessity.

## Kinds of slack (`SlackKind`)

* `state` — at every charged step: typed charge (worst case over the context `Δ` at that
  point) minus actual charge (at the runtime state `S`).  Zero when `Δ` pins down the states.
* `branch` — at every `if`: `max(Q₁, Q₂)` minus the summary of the branch taken.
* `arm` — at every `match`: the max over reachable arms minus the arm that runs (uncertainty
  about the matched peripheral).
* `clock` — after `c₁` in `c₁; c₂` and before a return: the rest is charged at the typed exit
  clock `F₁ K` instead of the actual one (nonzero only after a clock merge).
* `ambient` — at every call: the callee's summary at the caller's typed background for its
  other peripherals, minus at their actual background.
* `signature` — at every call: the signature's summary minus the callee body's derived summary
  (zero when signatures come from typing the declarations).

## Contents

* `Path`: control-flow paths — `Eval` without memory, where `if` may take either branch.
  `Eval.toPath`: every real run is a path.
* `SlackRun` / `ArmsSlack`: the slack judgment, pairing each typing rule with the matching path
  rule and fixing the slack items each step records.  `SlackRun.toTyped` / `SlackRun.toPath`:
  it is faithful to both.
* `SlackRun.decompose`: the identity `Q K (bg A) = q + slack L`, given `actual ≤ typed` for every
  item.
* `SlackRun.exists` (with `ArmsTyped.slack`): every path of a typed command, from a state
  agreeing with its context, has a slack derivation whose terms all satisfy `actual ≤ typed`.
  Assumes `SigsDerived` (signatures are the ones T-FunDecl derives, so calls descend into the
  callee's body derivation).
* `slack_decomposition` / `Eval.slack_decomposition`: the two combined, for paths and for real
  executions.  `SlackRun.exact`: with no slack, the bound is the cost.

**Status:** all of the above proved, no `sorry`.  Necessity is in `Heliod/Necessity.lean`, the
program-level version (`Program.slack_decomposition`) in `Heliod/SlackProgram.lean`.
-/

variable {K St R : Type} [DecidableEq K] [DecidableEq St]

/-! ### Control-flow paths -/

section Path

variable [CommSemiring R]

/-- Control-flow paths: the big-step semantics without memory, where `if` may take either
branch whatever its condition (costs do not depend on values).  `match` still selects the arm
by the peripheral's actual state.  Costs are exactly those of `Eval`. -/
inductive Path (M : CostModel K St R) (Ψd : FCtx K St R) :
    Multiset (K × St) → RPeriphs K St → R → Cmd St R → RPeriphs K St → R → R → Prop where
  | skip {A S Kc} : Path M Ψd A S Kc .skip S 0 Kc
  | assign {A S Kc x e} :
      Path M Ψd A S Kc (.assign x e) S (Kc * (e.cost M + S.bg M + ambBg M A)) Kc
  | iteTrue {A S Kc e c₁ c₂ S' q K'} :
      Path M Ψd A S Kc c₁ S' q K' →
      Path M Ψd A S Kc (.ite e c₁ c₂) S' (q + Kc * (e.cost M + S.bg M + ambBg M A)) K'
  | iteFalse {A S Kc e c₁ c₂ S' q K'} :
      Path M Ψd A S Kc c₂ S' q K' →
      Path M Ψd A S Kc (.ite e c₁ c₂) S' (q + Kc * (e.cost M + S.bg M + ambBg M A)) K'
  | transition {A S Kc p k s st} :
      S p = .at k s →
      Path M Ψd A S Kc (.transition p st) (S.set p k st)
        (Kc * (M.transCost k s st + (S.erase p).bg M + ambBg M A)) Kc
  | downgrade {A S Kc p k s st} :
      S p = .at k s →
      Path M Ψd A S Kc (.downgrade p st) (S.set p k st)
        (Kc * (M.transCost k s st + (S.erase p).bg M + ambBg M A)) Kc
  | clock {A S Kc f'} :
      Path M Ψd A S Kc (.clock f') S (M.clockCost Kc f' + Kc * (S.bg M + ambBg M A)) f'
  | seq {A S Kc c₁ c₂ S₁ q₁ K₁ S₂ q₂ K₂} :
      Path M Ψd A S Kc c₁ S₁ q₁ K₁ →
      Path M Ψd A S₁ K₁ c₂ S₂ q₂ K₂ →
      Path M Ψd A S Kc (.seq c₁ c₂) S₂ (q₁ + q₂) K₂
  | matchSt {A S Kc p arms k s c S' q K'} :
      S p = .at k s → arms.find? s = some c →
      Path M Ψd A S Kc c S' q K' →
      Path M Ψd A S Kc (.matchSt p arms) S' (q + Kc * (S.bg M + ambBg M A)) K'
  | call {A S Kc x g e p d k s Sb qb Kb s'} :
      Ψd g = some d →
      S p = .at k s →
      Path M Ψd (A + (S.erase p).entries) (Finsupp.single d.parg (.at k s)) Kc d.body Sb qb Kb →
      Sb d.parg = .at k s' →
      Path M Ψd A S Kc (.call x g e p) (S.set p k s')
        (Kc * (e.cost M + S.bg M + ambBg M A) + qb
          + Kb * (d.ret.cost M + Sb.bg M + ambBg M (A + (S.erase p).entries))) Kb

omit [DecidableEq K] in
/-- **Every real run is a control-flow path** with the same peripherals, cost and clock.  So the
slack decomposition, stated for paths, applies to actual executions. -/
theorem Eval.toPath {M : CostModel K St R} {Ψd : FCtx K St R} {A σ S Kc c σ' S' q K'}
    (h : Eval M Ψd A σ S Kc c σ' S' q K') : Path M Ψd A S Kc c S' q K' := by
  induction h with
  | skip => exact .skip
  | assign _ => exact .assign
  | iteTrue _ _ ih => exact .iteTrue ih
  | iteFalse _ _ ih => exact .iteFalse ih
  | transition hp => exact .transition hp
  | downgrade hp => exact .downgrade hp
  | clock => exact .clock
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | matchSt hp hf _ ih => exact .matchSt hp hf ih
  | call hg _ hp _ _ hs ih => exact .call hg hp ih hs

end Path

/-! ### Slack items -/

/-- The kinds of over-approximation; see the module doc. -/
inductive SlackKind where
  | state | branch | arm | clock | ambient | signature
  deriving DecidableEq, Repr

/-- One slack term: a kind, the typed charge (what the summary charges here) and the actual
charge (what the path incurs here, or the smaller quantity the summary is compared with). -/
structure SlackItem (R : Type) where
  kind : SlackKind
  typed : R
  actual : R

/-- The size of a slack term, `typed - actual` (truncated subtraction). -/
def SlackItem.delta [Sub R] (i : SlackItem R) : R := i.typed - i.actual

/-- Total slack of a list of terms. -/
def slack [AddCommMonoid R] [Sub R] (L : List (SlackItem R)) : R := (L.map SlackItem.delta).sum

section SlackSum
variable [AddCommMonoid R] [Sub R]

@[simp] theorem slack_nil : slack ([] : List (SlackItem R)) = 0 := rfl

@[simp] theorem slack_cons (i : SlackItem R) (L : List (SlackItem R)) :
    slack (i :: L) = i.delta + slack L := by simp [slack]

@[simp] theorem slack_append (L₁ L₂ : List (SlackItem R)) :
    slack (L₁ ++ L₂) = slack L₁ + slack L₂ := by simp [slack]

end SlackSum

/-! ### The slack judgment -/

variable [CommSemiring R] [LinearOrder R] [OrderBot R]

mutual

/-- `SlackRun … Γ Δ c Γ' Δ' Q F  A S K S' q K'  L`: `c` is typed with summaries `Q, F`, has a
control-flow path from `S` at clock `K` with ambient `A` to `S'` costing `q` and exiting at `K'`,
and `L` lists the slack terms along that path.  Each rule is a typing rule paired with the
matching path rule; the slack items it records are the formulas of the module doc. -/
inductive SlackRun (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtx K St R)
    (Ψd : FCtx K St R) :
    TCtx K → PCtx K St → Cmd St R → TCtx K → PCtx K St → (R → R → R) → (R → R) →
    Multiset (K × St) → RPeriphs K St → R → RPeriphs K St → R → R →
    List (SlackItem R) → Prop where
  | skip {Γ Δ A S Kc} :
      SlackRun P M Ψ Ψd Γ Δ .skip Γ Δ (fun _ _ => 0) (fun f => f) A S Kc S 0 Kc []
  | assign {Γ Δ x e τ A S Kc} :
      HasTy Γ e τ → Δ x = 0 →
      SlackRun P M Ψ Ψd Γ Δ (.assign x e) (Γ.bind x τ) Δ
        (fun f b => f * (e.cost M + Δ.bg M + b)) (fun f => f)
        A S Kc S (Kc * (e.cost M + S.bg M + ambBg M A)) Kc
        [⟨.state, Kc * (e.cost M + Δ.bg M + ambBg M A), Kc * (e.cost M + S.bg M + ambBg M A)⟩]
  | iteTrue {Γ Δ e c₁ c₂ Γ₁ Δ₁ Q₁ F₁ Γ₂ Δ₂ Q₂ F₂ A S Kc S' q K' L} :
      HasTy Γ e .bool →
      SlackRun P M Ψ Ψd Γ Δ c₁ Γ₁ Δ₁ Q₁ F₁ A S Kc S' q K' L →
      Typed P M Ψ Γ Δ c₂ Γ₂ Δ₂ Q₂ F₂ →
      SlackRun P M Ψ Ψd Γ Δ (.ite e c₁ c₂) (Γ₁.inter Γ₂) (Δ₁.join Δ₂)
        (fun f b => max (Q₁ f b) (Q₂ f b) + f * (e.cost M + Δ.bg M + b))
        (fun f => max (F₁ f) (F₂ f))
        A S Kc S' (q + Kc * (e.cost M + S.bg M + ambBg M A)) K'
        (⟨.state, Kc * (e.cost M + Δ.bg M + ambBg M A), Kc * (e.cost M + S.bg M + ambBg M A)⟩ ::
          ⟨.branch, max (Q₁ Kc (ambBg M A)) (Q₂ Kc (ambBg M A)), Q₁ Kc (ambBg M A)⟩ :: L)
  | iteFalse {Γ Δ e c₁ c₂ Γ₁ Δ₁ Q₁ F₁ Γ₂ Δ₂ Q₂ F₂ A S Kc S' q K' L} :
      HasTy Γ e .bool →
      Typed P M Ψ Γ Δ c₁ Γ₁ Δ₁ Q₁ F₁ →
      SlackRun P M Ψ Ψd Γ Δ c₂ Γ₂ Δ₂ Q₂ F₂ A S Kc S' q K' L →
      SlackRun P M Ψ Ψd Γ Δ (.ite e c₁ c₂) (Γ₁.inter Γ₂) (Δ₁.join Δ₂)
        (fun f b => max (Q₁ f b) (Q₂ f b) + f * (e.cost M + Δ.bg M + b))
        (fun f => max (F₁ f) (F₂ f))
        A S Kc S' (q + Kc * (e.cost M + S.bg M + ambBg M A)) K'
        (⟨.state, Kc * (e.cost M + Δ.bg M + ambBg M A), Kc * (e.cost M + S.bg M + ambBg M A)⟩ ::
          ⟨.branch, max (Q₁ Kc (ambBg M A)) (Q₂ Kc (ambBg M A)), Q₂ Kc (ambBg M A)⟩ :: L)
  | transition {Γ Δ p k T st A S Kc s} :
      Δ p = .live k T → P.stable k st → (∀ s ∈ T, P.le k s st) →
      S p = .at k s →
      SlackRun P M Ψ Ψd Γ Δ (.transition p st) Γ (Δ.set p k {st})
        (fun f b => f * (M.maxTrans k T st + (Δ.erase p).bg M + b)) (fun f => f)
        A S Kc (S.set p k st) (Kc * (M.transCost k s st + (S.erase p).bg M + ambBg M A)) Kc
        [⟨.state, Kc * (M.maxTrans k T st + (Δ.erase p).bg M + ambBg M A),
          Kc * (M.transCost k s st + (S.erase p).bg M + ambBg M A)⟩]
  | downgrade {Γ Δ p k T st A S Kc s} :
      Δ p = .live k T → P.stable k st → (∀ s ∈ T, P.dg k s st) →
      S p = .at k s →
      SlackRun P M Ψ Ψd Γ Δ (.downgrade p st) Γ (Δ.set p k {st})
        (fun f b => f * (M.maxTrans k T st + (Δ.erase p).bg M + b)) (fun f => f)
        A S Kc (S.set p k st) (Kc * (M.transCost k s st + (S.erase p).bg M + ambBg M A)) Kc
        [⟨.state, Kc * (M.maxTrans k T st + (Δ.erase p).bg M + ambBg M A),
          Kc * (M.transCost k s st + (S.erase p).bg M + ambBg M A)⟩]
  | clock {Γ Δ f' A S Kc} :
      0 < f' →
      SlackRun P M Ψ Ψd Γ Δ (.clock f') Γ Δ
        (fun f b => M.clockCost f f' + f * (Δ.bg M + b)) (fun _ => f')
        A S Kc S (M.clockCost Kc f' + Kc * (S.bg M + ambBg M A)) f'
        [⟨.state, M.clockCost Kc f' + Kc * (Δ.bg M + ambBg M A),
          M.clockCost Kc f' + Kc * (S.bg M + ambBg M A)⟩]
  | seq {Γ Δ c₁ c₂ Γ₁ Δ₁ Q₁ F₁ Γ₂ Δ₂ Q₂ F₂ A S Kc S₁ q₁ K₁ S₂ q₂ K₂ L₁ L₂} :
      SlackRun P M Ψ Ψd Γ Δ c₁ Γ₁ Δ₁ Q₁ F₁ A S Kc S₁ q₁ K₁ L₁ →
      SlackRun P M Ψ Ψd Γ₁ Δ₁ c₂ Γ₂ Δ₂ Q₂ F₂ A S₁ K₁ S₂ q₂ K₂ L₂ →
      SlackRun P M Ψ Ψd Γ Δ (.seq c₁ c₂) Γ₂ Δ₂
        (fun f b => Q₁ f b + Q₂ (F₁ f) b) (fun f => F₂ (F₁ f))
        A S Kc S₂ (q₁ + q₂) K₂
        (L₁ ++ ⟨.clock, Q₂ (F₁ Kc) (ambBg M A), Q₂ K₁ (ambBg M A)⟩ :: L₂)
  | matchSt {Γ Δ p k T arms Γ' Δ' Q F A S Kc s S' q K' L} :
      Δ p = .live k T → T ⊆ arms.states →
      S p = .at k s →
      ArmsSlack P M Ψ Ψd Γ Δ p k T arms Γ' Δ' Q F s A S Kc S' q K' L →
      SlackRun P M Ψ Ψd Γ Δ (.matchSt p arms) Γ' Δ' Q F
        A S Kc S' (q + Kc * (S.bg M + ambBg M A)) K'
        (⟨.state, Kc * ((Δ.set p k {s}).bg M + ambBg M A), Kc * (S.bg M + ambBg M A)⟩ :: L)
  | call {Γ Δ x g e p sig T A S Kc d s Γb Δb Qb Fb Sb qb Kb s' Lb} :
      Ψ g = some sig →
      HasTy Γ e sig.argTy →
      Δ x = 0 →
      Δ p = .live sig.pKind T → T ⊆ sig.sIn →
      Ψd g = some d →
      S p = .at sig.pKind s →
      SlackRun P M Ψ Ψd (TCtx.empty.bind d.arg d.argTy)
        (Finsupp.single d.parg (.live d.pKind d.sIn)) d.body Γb Δb Qb Fb
        (A + (S.erase p).entries) (Finsupp.single d.parg (.at sig.pKind s)) Kc Sb qb Kb Lb →
      Sb d.parg = .at sig.pKind s' →
      SlackRun P M Ψ Ψd Γ Δ (.call x g e p) (Γ.bind x sig.retTy) (Δ.set p sig.pKind sig.sOut)
        (fun f b => f * (e.cost M + Δ.bg M + b) + sig.cost f (b + (Δ.erase p).bg M)) sig.clk
        A S Kc (S.set p sig.pKind s')
        (Kc * (e.cost M + S.bg M + ambBg M A) + qb
          + Kb * (d.ret.cost M + Sb.bg M + ambBg M (A + (S.erase p).entries))) Kb
        (⟨.state, Kc * (e.cost M + Δ.bg M + ambBg M A), Kc * (e.cost M + S.bg M + ambBg M A)⟩ ::
          ⟨.ambient, sig.cost Kc (ambBg M A + (Δ.erase p).bg M),
            sig.cost Kc (ambBg M (A + (S.erase p).entries))⟩ ::
          ⟨.signature, sig.cost Kc (ambBg M (A + (S.erase p).entries)),
            Qb Kc (ambBg M (A + (S.erase p).entries))
              + Fb Kc * (d.ret.cost M + Δb.bg M + ambBg M (A + (S.erase p).entries))⟩ ::
          Lb ++
          [⟨.clock, Fb Kc * (d.ret.cost M + Δb.bg M + ambBg M (A + (S.erase p).entries)),
              Kb * (d.ret.cost M + Δb.bg M + ambBg M (A + (S.erase p).entries))⟩,
            ⟨.state, Kb * (d.ret.cost M + Δb.bg M + ambBg M (A + (S.erase p).entries)),
              Kb * (d.ret.cost M + Sb.bg M + ambBg M (A + (S.erase p).entries))⟩])

/-- Slack judgment for the arms of `match p with …` when `p` is actually in state `s`: descends
to the first arm for `s` (the one `Arms.find?` selects), recording at each reachable arm on the
way an `arm` slack term (the joined max minus the part containing the arm that runs).  The
matched arm's summary includes the `match` step with `p` narrowed (as in `ArmsTyped`). -/
inductive ArmsSlack (P : Platform K St) (M : CostModel K St R) (Ψ : SigCtx K St R)
    (Ψd : FCtx K St R) :
    TCtx K → PCtx K St → Var → K → Finset St → Arms St R →
    TCtx K → PCtx K St → (R → R → R) → (R → R) →
    St → Multiset (K × St) → RPeriphs K St → R → RPeriphs K St → R → R →
    List (SlackItem R) → Prop where
  /-- The arm for `s`, after which every arm is unreachable (`ArmsTyped.last`). -/
  | hitLast {Γ Δ p k T st c rest Γ' Δ' Q F A S Kc S' q K' L} :
      st ∈ T →
      SlackRun P M Ψ Ψd Γ (Δ.set p k {st}) c Γ' Δ' Q F A S Kc S' q K' L →
      (∀ s ∈ rest.states, s ∉ T) →
      ArmsSlack P M Ψ Ψd Γ Δ p k T (.cons st c rest) Γ' Δ'
        (fun f b => Q f b + f * ((Δ.set p k {st}).bg M + b)) F st A S Kc S' q K' L
  /-- The arm for `s`, joined with further reachable arms (`ArmsTyped.cons`). -/
  | hitCons {Γ Δ p k T st c rest Γ₁ Δ₁ Q₁ F₁ Γ₂ Δ₂ Q₂ F₂ A S Kc S' q K' L} :
      st ∈ T →
      SlackRun P M Ψ Ψd Γ (Δ.set p k {st}) c Γ₁ Δ₁ Q₁ F₁ A S Kc S' q K' L →
      ArmsTyped P M Ψ Γ Δ p k T rest Γ₂ Δ₂ Q₂ F₂ →
      ArmsSlack P M Ψ Ψd Γ Δ p k T (.cons st c rest) (Γ₁.inter Γ₂) (Δ₁.join Δ₂)
        (fun f b => max (Q₁ f b + f * ((Δ.set p k {st}).bg M + b)) (Q₂ f b))
        (fun f => max (F₁ f) (F₂ f)) st A S Kc S' q K'
        (⟨.arm, max (Q₁ Kc (ambBg M A) + Kc * ((Δ.set p k {st}).bg M + ambBg M A))
            (Q₂ Kc (ambBg M A)),
          Q₁ Kc (ambBg M A) + Kc * ((Δ.set p k {st}).bg M + ambBg M A)⟩ :: L)
  /-- A reachable arm for another state; the arm for `s` comes later (`ArmsTyped.cons`). -/
  | missCons {Γ Δ p k T st c rest Γ₁ Δ₁ Q₁ F₁ Γ₂ Δ₂ Q₂ F₂ s A S Kc S' q K' L} :
      st ∈ T → st ≠ s →
      Typed P M Ψ Γ (Δ.set p k {st}) c Γ₁ Δ₁ Q₁ F₁ →
      ArmsSlack P M Ψ Ψd Γ Δ p k T rest Γ₂ Δ₂ Q₂ F₂ s A S Kc S' q K' L →
      ArmsSlack P M Ψ Ψd Γ Δ p k T (.cons st c rest) (Γ₁.inter Γ₂) (Δ₁.join Δ₂)
        (fun f b => max (Q₁ f b + f * ((Δ.set p k {st}).bg M + b)) (Q₂ f b))
        (fun f => max (F₁ f) (F₂ f)) s A S Kc S' q K'
        (⟨.arm, max (Q₁ Kc (ambBg M A) + Kc * ((Δ.set p k {st}).bg M + ambBg M A))
            (Q₂ Kc (ambBg M A)), Q₂ Kc (ambBg M A)⟩ :: L)
  /-- An unreachable arm (`ArmsTyped.skip`). -/
  | skip {Γ Δ p k T st c rest Γ' Δ' Q F s A S Kc S' q K' L} :
      st ∉ T → st ≠ s →
      ArmsSlack P M Ψ Ψd Γ Δ p k T rest Γ' Δ' Q F s A S Kc S' q K' L →
      ArmsSlack P M Ψ Ψd Γ Δ p k T (.cons st c rest) Γ' Δ' Q F s A S Kc S' q K' L

end

variable {P : Platform K St} {M : CostModel K St R} {Ψ : SigCtx K St R} {Ψd : FCtx K St R}

/-! ### Faithfulness: a slack derivation is a typing derivation and a path -/

mutual

/-- **The slack judgment only annotates typing.**  Forgetting the path and the slack terms
leaves a typing derivation with the same summaries. -/
theorem SlackRun.toTyped {Γ Δ c Γ' Δ' Q F A S Kc S' q K' L} :
    SlackRun P M Ψ Ψd Γ Δ c Γ' Δ' Q F A S Kc S' q K' L → Typed P M Ψ Γ Δ c Γ' Δ' Q F
  | .skip => .skip
  | .assign hty hx => .assign hty hx
  | .iteTrue hty h₁ h₂ => .ite hty h₁.toTyped h₂
  | .iteFalse hty h₁ h₂ => .ite hty h₁ h₂.toTyped
  | .transition hp hst hle _ => .transition hp hst hle
  | .downgrade hp hst hle _ => .downgrade hp hst hle
  | .clock hf => .clock hf
  | .seq h₁ h₂ => .seq h₁.toTyped h₂.toTyped
  | .matchSt hp hsub _ ha => .matchSt hp hsub ha.toTyped
  | .call hg hty hx hp hsub _ _ _ _ => .call hg hty hx hp hsub

/-- Arms version of `SlackRun.toTyped`. -/
theorem ArmsSlack.toTyped {Γ Δ p k T arms Γ' Δ' Q F s A S Kc S' q K' L} :
    ArmsSlack P M Ψ Ψd Γ Δ p k T arms Γ' Δ' Q F s A S Kc S' q K' L →
    ArmsTyped P M Ψ Γ Δ p k T arms Γ' Δ' Q F
  | .hitLast hst h hrest => .last hst h.toTyped hrest
  | .hitCons hst h ha => .cons hst h.toTyped ha
  | .missCons hst _ h ha => .cons hst h ha.toTyped
  | .skip hst _ ha => .skip hst ha.toTyped

end

mutual

/-- **The slack judgment only annotates a path.**  Forgetting typing and slack terms leaves a
control-flow path with the same cost and clocks. -/
theorem SlackRun.toPath {Γ Δ c Γ' Δ' Q F A S Kc S' q K' L} :
    SlackRun P M Ψ Ψd Γ Δ c Γ' Δ' Q F A S Kc S' q K' L → Path M Ψd A S Kc c S' q K'
  | .skip => .skip
  | .assign _ _ => .assign
  | .iteTrue _ h₁ _ => .iteTrue h₁.toPath
  | .iteFalse _ _ h₂ => .iteFalse h₂.toPath
  | .transition _ _ _ hS => .transition hS
  | .downgrade _ _ _ hS => .downgrade hS
  | .clock _ => .clock
  | .seq h₁ h₂ => .seq h₁.toPath h₂.toPath
  | .matchSt _ _ hS ha =>
      have ⟨_, hf, hc⟩ := ha.toPath
      .matchSt hS hf hc
  | .call _ _ _ _ _ hd hS hb hSb => .call hd hS hb.toPath hSb

/-- Arms version of `SlackRun.toPath`: the arm the slack derivation descends to is the one
`Arms.find?` selects, and it has the recorded path. -/
theorem ArmsSlack.toPath {Γ Δ p k T arms Γ' Δ' Q F s A S Kc S' q K' L} :
    ArmsSlack P M Ψ Ψd Γ Δ p k T arms Γ' Δ' Q F s A S Kc S' q K' L →
    ∃ c, arms.find? s = some c ∧ Path M Ψd A S Kc c S' q K'
  | .hitLast (c := c) _ h _ => ⟨c, by simp [Arms.find?], h.toPath⟩
  | .hitCons (c := c) _ h _ => ⟨c, by simp [Arms.find?], h.toPath⟩
  | .missCons _ hne _ ha =>
      have ⟨c, hf, hc⟩ := ha.toPath
      ⟨c, by simp [Arms.find?, hne, hf], hc⟩
  | .skip _ hne ha =>
      have ⟨c, hf, hc⟩ := ha.toPath
      ⟨c, by simp [Arms.find?, hne, hf], hc⟩

end

/-! ### The decomposition identity -/

section Decompose

variable [Sub R] [OrderedSub R] [CanonicallyOrderedAdd R]

omit [OrderBot R] in
/-- Splitting a typed charge into the actual charge plus the slack term: the arithmetic step
used at every item of the decomposition. -/
private theorem split {a t : R} (h : a ≤ t) : ∃ d, t - a = d ∧ t = a + d :=
  ⟨t - a, rfl, (add_tsub_cancel_of_le h).symm⟩

mutual

/-- **Slack decomposition.**  Along a path recorded by a slack derivation, the summary at the
path's actual clock and ambient background is the path's cost plus the total slack:
`Q K (bg A) = q + Σ δᵢ`.  The hypothesis that every term has `actual ≤ typed` is what makes the
truncated subtractions exact; the existence theorem establishes it for every typed path. -/
theorem SlackRun.decompose {Γ Δ c Γ' Δ' Q F A S Kc S' q K' L} :
    SlackRun P M Ψ Ψd Γ Δ c Γ' Δ' Q F A S Kc S' q K' L →
    (∀ i ∈ L, i.actual ≤ i.typed) → Q Kc (ambBg M A) = q + slack L
  | .skip, _ => by simp
  | .assign _ _, hle => by
      simp only [List.forall_mem_cons] at hle
      obtain ⟨d, hd, ht⟩ := split hle.1
      simp only [slack_cons, slack_nil, SlackItem.delta]
      rw [hd, ht, add_zero]
  | .transition _ _ _ _, hle => by
      simp only [List.forall_mem_cons] at hle
      obtain ⟨d, hd, ht⟩ := split hle.1
      simp only [slack_cons, slack_nil, SlackItem.delta]
      rw [hd, ht, add_zero]
  | .downgrade _ _ _ _, hle => by
      simp only [List.forall_mem_cons] at hle
      obtain ⟨d, hd, ht⟩ := split hle.1
      simp only [slack_cons, slack_nil, SlackItem.delta]
      rw [hd, ht, add_zero]
  | .clock _, hle => by
      simp only [List.forall_mem_cons] at hle
      obtain ⟨d, hd, ht⟩ := split hle.1
      simp only [slack_cons, slack_nil, SlackItem.delta]
      rw [hd, ht, add_zero]
  | .iteTrue _ h₁ _, hle => by
      simp only [List.forall_mem_cons] at hle
      obtain ⟨h₁le, h₂le, hL⟩ := hle
      obtain ⟨d₁, hd₁, ht₁⟩ := split h₁le
      obtain ⟨d₂, hd₂, ht₂⟩ := split h₂le
      have ih := h₁.decompose hL
      simp only [slack_cons, SlackItem.delta]
      rw [hd₁, hd₂, ht₁, ht₂, ih]
      ac_rfl
  | .iteFalse _ _ h₂, hle => by
      simp only [List.forall_mem_cons] at hle
      obtain ⟨h₁le, h₂le, hL⟩ := hle
      obtain ⟨d₁, hd₁, ht₁⟩ := split h₁le
      obtain ⟨d₂, hd₂, ht₂⟩ := split h₂le
      have ih := h₂.decompose hL
      simp only [slack_cons, SlackItem.delta]
      rw [hd₁, hd₂, ht₁, ht₂, ih]
      ac_rfl
  | .seq h₁ h₂, hle => by
      simp only [List.forall_mem_append, List.forall_mem_cons] at hle
      obtain ⟨hL₁, hcle, hL₂⟩ := hle
      obtain ⟨d, hd, ht⟩ := split hcle
      have ih₁ := h₁.decompose hL₁
      have ih₂ := h₂.decompose hL₂
      simp only [slack_append, slack_cons, SlackItem.delta]
      rw [hd, ht, ih₁, ih₂]
      ac_rfl
  | .matchSt _ _ _ ha, hle => by
      simp only [List.forall_mem_cons] at hle
      obtain ⟨hsle, hL⟩ := hle
      obtain ⟨d, hd, ht⟩ := split hsle
      have ih := ha.decompose hL
      simp only [slack_cons, SlackItem.delta]
      rw [hd, ih, ht]
      ac_rfl
  | .call _ _ _ _ _ _ _ hb _, hle => by
      simp only [List.forall_mem_cons, List.forall_mem_append] at hle
      obtain ⟨⟨h₁le, h₂le, h₃le, hLb⟩, h₄le, h₅le, -⟩ := hle
      obtain ⟨d₁, hd₁, ht₁⟩ := split h₁le
      obtain ⟨d₂, hd₂, ht₂⟩ := split h₂le
      obtain ⟨d₃, hd₃, ht₃⟩ := split h₃le
      obtain ⟨d₄, hd₄, ht₄⟩ := split h₄le
      obtain ⟨d₅, hd₅, ht₅⟩ := split h₅le
      have ih := hb.decompose hLb
      simp only [slack_append, slack_cons, slack_nil, SlackItem.delta]
      rw [hd₁, hd₂, hd₃, hd₄, hd₅, ht₁, ht₂, ht₃, ih, ht₄, ht₅]
      ac_rfl

/-- Arms version of `SlackRun.decompose`: the joined summary is the selected arm's cost, plus
the `match` step charged with `p` narrowed to its actual state `s`, plus the slack. -/
theorem ArmsSlack.decompose {Γ Δ p k T arms Γ' Δ' Q F s A S Kc S' q K' L} :
    ArmsSlack P M Ψ Ψd Γ Δ p k T arms Γ' Δ' Q F s A S Kc S' q K' L →
    (∀ i ∈ L, i.actual ≤ i.typed) →
    Q Kc (ambBg M A) = q + Kc * ((Δ.set p k {s}).bg M + ambBg M A) + slack L
  | .hitLast _ h _, hle => by
      have ih := h.decompose hle
      simp only
      rw [ih]
      ac_rfl
  | .hitCons _ h _, hle => by
      simp only [List.forall_mem_cons] at hle
      obtain ⟨hale, hL⟩ := hle
      obtain ⟨d, hd, ht⟩ := split hale
      have ih := h.decompose hL
      simp only [slack_cons, SlackItem.delta]
      rw [hd, ht, ih]
      ac_rfl
  | .missCons _ _ _ ha, hle => by
      simp only [List.forall_mem_cons] at hle
      obtain ⟨hale, hL⟩ := hle
      obtain ⟨d, hd, ht⟩ := split hale
      have ih := ha.decompose hL
      simp only [slack_cons, SlackItem.delta]
      rw [hd, ht, ih]
      ac_rfl
  | .skip _ _ ha, hle => ha.decompose hle

end

end Decompose

/-! ### Existence: every typed path has a slack derivation with valid terms -/

section Existence

variable [IsOrderedRing R] [CanonicallyOrderedAdd R]

/-- Every signature in `Ψ` is the one T-FunDecl derives for the declaration of the same name in
`Ψd`, typed against `Ψ` itself.  This is what lets the slack of a call descend into the callee's
body derivation (the `signature` term is then `0`).  Programs satisfy it (see the program-level
results), since declarations typed against a prefix of `Ψ` remain typed against `Ψ`. -/
def SigsDerived (P : Platform K St) (M : CostModel K St R) (Ψd : FCtx K St R)
    (Ψ : SigCtx K St R) : Prop :=
  ∀ g sig, Ψ g = some sig → ∃ d, Ψd g = some d ∧ FunDeclTyped P M Ψ d sig

omit [OrderBot R] in
/-- A charge `f * x` grows with `f` and `x` (all costs are `≥ 0`). -/
private theorem mul_mono' {f f' x x' : R} (hf : f ≤ f') (hx : x ≤ x') : f * x ≤ f' * x' :=
  mul_le_mul hf hx zero_le zero_le

omit [CommSemiring R] [OrderBot R] [IsOrderedRing R] [CanonicallyOrderedAdd R] in
/-- No term in the empty list. -/
private theorem ok_nil : ∀ j ∈ ([] : List (SlackItem R)), j.actual ≤ j.typed :=
  fun _ h => by cases h

omit [CommSemiring R] [OrderBot R] [IsOrderedRing R] [CanonicallyOrderedAdd R] in
/-- Valid terms are closed under `::`. -/
private theorem ok_cons {i : SlackItem R} {L : List (SlackItem R)} (h : i.actual ≤ i.typed)
    (hL : ∀ j ∈ L, j.actual ≤ j.typed) : ∀ j ∈ i :: L, j.actual ≤ j.typed :=
  List.forall_mem_cons.2 ⟨h, hL⟩

omit [CommSemiring R] [OrderBot R] [IsOrderedRing R] [CanonicallyOrderedAdd R] in
/-- Valid terms are closed under `++`. -/
private theorem ok_append {L₁ L₂ : List (SlackItem R)} (h₁ : ∀ j ∈ L₁, j.actual ≤ j.typed)
    (h₂ : ∀ j ∈ L₂, j.actual ≤ j.typed) : ∀ j ∈ L₁ ++ L₂, j.actual ≤ j.typed :=
  List.forall_mem_append.2 ⟨h₁, h₂⟩

omit [IsOrderedRing R] [CanonicallyOrderedAdd R] in
/-- **Arms step of the existence theorem.**  Given the joined typing of a `match`'s arms and a
slack derivation for whatever typing the selected arm has (supplied by the induction hypothesis
of `SlackRun.exists`), build the arms' slack derivation.  Every `arm` term is valid because the
selected arm's part is one argument of the `max`. -/
theorem ArmsTyped.slack {Γ Δ p k T arms Γ' Δ' Q F} :
    ArmsTyped P M Ψ Γ Δ p k T arms Γ' Δ' Q F →
    ∀ {s c A S Kc S' q K'}, s ∈ T → arms.find? s = some c →
    (∀ {Γc Δc Qc Fc}, Typed P M Ψ Γ (Δ.set p k {s}) c Γc Δc Qc Fc →
      ∃ L, SlackRun P M Ψ Ψd Γ (Δ.set p k {s}) c Γc Δc Qc Fc A S Kc S' q K' L ∧
        (∀ i ∈ L, i.actual ≤ i.typed) ∧ K' ≤ Fc Kc ∧ PeriphsOK Δc S') →
    ∃ L, ArmsSlack P M Ψ Ψd Γ Δ p k T arms Γ' Δ' Q F s A S Kc S' q K' L ∧
      (∀ i ∈ L, i.actual ≤ i.typed) ∧ K' ≤ F Kc ∧ PeriphsOK Δ' S'
  | .last hst h hrest, s, c, A, S, Kc, S', q, K', hs, hf, hc => by
      simp only [Arms.find?] at hf
      split_ifs at hf with hst'
      · cases hf; subst hst'
        obtain ⟨L, hL, hle, hK, hS'⟩ := hc h
        exact ⟨L, .hitLast hst hL hrest, hle, hK, hS'⟩
      · exact absurd hs (hrest s (Arms.mem_states_of_find? hf))
  | .cons hst h ha, s, c, A, S, Kc, S', q, K', hs, hf, hc => by
      have hsh := (h.shape_eq.trans (PCtx.shape_set_set _ _ _ _ ∅)).trans ha.shape_eq.symm
      simp only [Arms.find?] at hf
      split_ifs at hf with hst'
      · cases hf; subst hst'
        obtain ⟨L, hL, hle, hK, hS'⟩ := hc h
        exact ⟨_, .hitCons hst hL ha, ok_cons (le_max_left _ _) hle,
          hK.trans (le_max_left _ _), hS'.mono (PCtx.le_join_left hsh)⟩
      · obtain ⟨L, hL, hle, hK, hS'⟩ := ArmsTyped.slack ha hs hf hc
        exact ⟨_, .missCons hst hst' h hL, ok_cons (le_max_right _ _) hle,
          hK.trans (le_max_right _ _), hS'.mono (PCtx.le_join_right hsh)⟩
  | .skip hst ha, s, c, A, S, Kc, S', q, K', hs, hf, hc => by
      simp only [Arms.find?] at hf
      split_ifs at hf with hst'
      · exact absurd (hst' ▸ hs) hst
      · obtain ⟨L, hL, hle, hK, hS'⟩ := ArmsTyped.slack ha hs hf hc
        exact ⟨L, .skip hst hst' hL, hle, hK, hS'⟩

/-- **Existence of the slack decomposition.**  Every control-flow path of a typed command,
from a state that agrees with its typing context, has a slack derivation all of whose terms
satisfy `actual ≤ typed` (so `SlackRun.decompose` applies); the path also exits no later than
the typed clock and ends in a state agreeing with the output context.

Proof: induction on the path, inverting the typing — the structure of `soundness`, with each
`≤` step of that proof becoming a recorded slack term. -/
theorem SlackRun.exists (hM : M.WF) (hΨv : SigsValid M Ψd Ψ) (hΨd : SigsDerived P M Ψd Ψ)
    {A S Kc c S' q K'} (hp : Path M Ψd A S Kc c S' q K') :
    ∀ {Γ Δ Γ' Δ' Q F}, Typed P M Ψ Γ Δ c Γ' Δ' Q F → PeriphsOK Δ S →
    ∃ L, SlackRun P M Ψ Ψd Γ Δ c Γ' Δ' Q F A S Kc S' q K' L ∧
      (∀ i ∈ L, i.actual ≤ i.typed) ∧ K' ≤ F Kc ∧ PeriphsOK Δ' S' := by
  induction hp with
  | skip =>
    intro _ _ _ _ _ _ ht hS
    cases ht
    exact ⟨[], .skip, ok_nil, le_rfl, hS⟩
  | assign =>
    intro _ _ _ _ _ _ ht hS
    cases ht with
    | assign hty hx =>
      exact ⟨_, .assign hty hx,
        ok_cons (mul_mono' le_rfl (add_le_add (add_le_add le_rfl hS.bg_le) le_rfl)) ok_nil,
        le_rfl, hS⟩
  | iteTrue _ ih =>
    intro _ _ _ _ _ _ ht hS
    cases ht with
    | ite hty h₁ h₂ =>
      obtain ⟨L, hL, hle, hK, hS'⟩ := ih h₁ hS
      have hsh := h₁.shape_eq.trans h₂.shape_eq.symm
      exact ⟨_, .iteTrue hty hL h₂,
        ok_cons (mul_mono' le_rfl (add_le_add (add_le_add le_rfl hS.bg_le) le_rfl))
          (ok_cons (le_max_left _ _) hle),
        hK.trans (le_max_left _ _), hS'.mono (PCtx.le_join_left hsh)⟩
  | iteFalse _ ih =>
    intro _ _ _ _ _ _ ht hS
    cases ht with
    | ite hty h₁ h₂ =>
      obtain ⟨L, hL, hle, hK, hS'⟩ := ih h₂ hS
      have hsh := h₁.shape_eq.trans h₂.shape_eq.symm
      exact ⟨_, .iteFalse hty h₁ hL,
        ok_cons (mul_mono' le_rfl (add_le_add (add_le_add le_rfl hS.bg_le) le_rfl))
          (ok_cons (le_max_right _ _) hle),
        hK.trans (le_max_right _ _), hS'.mono (PCtx.le_join_right hsh)⟩
  | transition hSp =>
    intro _ _ _ _ _ _ ht hS
    cases ht with
    | transition hp hst hle =>
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      exact ⟨_, .transition hp hst hle hSp,
        ok_cons (mul_mono' le_rfl (add_le_add (add_le_add (M.transCost_le_maxTrans hs)
          (hS.erase _).bg_le) le_rfl)) ok_nil,
        le_rfl, hS.set _ _ (Finset.mem_singleton_self _)⟩
  | downgrade hSp =>
    intro _ _ _ _ _ _ ht hS
    cases ht with
    | downgrade hp hst hle =>
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      exact ⟨_, .downgrade hp hst hle hSp,
        ok_cons (mul_mono' le_rfl (add_le_add (add_le_add (M.transCost_le_maxTrans hs)
          (hS.erase _).bg_le) le_rfl)) ok_nil,
        le_rfl, hS.set _ _ (Finset.mem_singleton_self _)⟩
  | clock =>
    intro _ _ _ _ _ _ ht hS
    cases ht with
    | clock hf =>
      exact ⟨_, .clock hf,
        ok_cons (add_le_add le_rfl (mul_mono' le_rfl (add_le_add hS.bg_le le_rfl))) ok_nil,
        le_rfl, hS⟩
  | seq _ _ ih₁ ih₂ =>
    intro _ _ _ _ _ _ ht hS
    cases ht with
    | seq t₁ t₂ =>
      obtain ⟨L₁, hL₁, hle₁, hK₁, hS₁⟩ := ih₁ t₁ hS
      obtain ⟨L₂, hL₂, hle₂, hK₂, hS₂⟩ := ih₂ t₂ hS₁
      obtain ⟨hF₂, hQ₂⟩ := t₂.mono hM hΨv.mono
      exact ⟨_, .seq hL₁ hL₂, ok_append hle₁ (ok_cons (hQ₂ _ _ _ _ hK₁ le_rfl) hle₂),
        hK₂.trans (hF₂ hK₁), hS₂⟩
  | @matchSt A S Kc p arms k s c S' q K' hSp hf _ ih =>
    intro _ Δ _ _ _ _ ht hS
    cases ht with
    | matchSt hp hsub ha =>
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      have hSs : PeriphsOK (Δ.set p k {s}) S := by
        rw [← RPeriphs.set_eq_self hSp]; exact hS.set _ _ (Finset.mem_singleton_self _)
      obtain ⟨L, hL, hle, hK, hS'⟩ := ha.slack hs hf (fun hc => ih hc hSs)
      exact ⟨_, .matchSt hp hsub hSp hL,
        ok_cons (mul_mono' le_rfl (add_le_add hSs.bg_le le_rfl)) hle, hK, hS'⟩
  | @call A S Kc x g e p d k s Sb qb Kb s' hd hSp _ hSb ih =>
    intro _ Δ _ _ _ _ ht hS
    cases ht with
    | @call _ _ _ _ _ _ sig _ hg hty hx hp hsub =>
      obtain ⟨rfl, hs⟩ := hS.at hSp hp
      obtain ⟨d', hd', hdt⟩ := hΨd _ _ hg
      rw [hd] at hd'; cases hd'
      obtain ⟨_, hpKind, hsIn, _, hsOut, Γb, Δb, Qb, Fb, Sout, hbt, _, hΔb, hSout, hcost,
        hclk⟩ := hdt
      have hsb : PeriphsOK (Finsupp.single d.parg (.live d.pKind d.sIn))
          (Finsupp.single d.parg (.at sig.pKind s)) := by
        rw [hpKind]; exact PeriphsOK.single (hsIn ▸ hsub hs)
      obtain ⟨Lb, hLb, hleb, hKb, hSb'⟩ := ih hbt hsb
      obtain ⟨s'', hSbp, hs''⟩ := hSb'.live hΔb
      rw [hSb] at hSbp
      obtain ⟨-, rfl⟩ := REntry.at.inj hSbp
      have hmono := hΨv.mono _ _ hg
      refine ⟨_, .call hg hty hx hp hsub hd hSp hLb hSb, ?_, ?_,
        hS.set _ _ (hsOut ▸ hSout hs'')⟩
      · refine ok_append (ok_cons ?_ (ok_cons ?_ (ok_cons ?_ hleb)))
          (ok_cons ?_ (ok_cons ?_ ok_nil))
        · exact mul_mono' le_rfl (add_le_add (add_le_add le_rfl hS.bg_le) le_rfl)
        · refine hmono.2 _ _ _ _ le_rfl ?_
          rw [ambBg_add_entries]
          exact add_le_add le_rfl (hS.erase p).bg_le
        · show _ ≤ sig.cost _ _
          rw [hcost]
        · exact mul_mono' hKb le_rfl
        · exact mul_mono' le_rfl (add_le_add (add_le_add le_rfl hSb'.bg_le) le_rfl)
      · rw [hclk]; exact hKb

end Existence

/-! ### Main results -/

section Main

variable [IsOrderedRing R] [CanonicallyOrderedAdd R] [Sub R] [OrderedSub R]

/-- **Slack decomposition theorem.**  For a typed command and any control-flow path from a state
agreeing with its typing context, the summary at the path's clock and ambient background is the
path's cost plus the slack recorded along it: `Q K (bg A) = q + Σ δᵢ`, where the terms `L` are
fixed by the rules of `SlackRun` (each one local, of a known kind, with an explicit formula)
and each is `≥ 0`.  This is soundness made exact: it says not only that the bound holds but
where, and by how much, it exceeds the cost. -/
theorem slack_decomposition (hM : M.WF) (hΨv : SigsValid M Ψd Ψ) (hΨd : SigsDerived P M Ψd Ψ)
    {Γ Δ c Γ' Δ' Q F} (ht : Typed P M Ψ Γ Δ c Γ' Δ' Q F)
    {A S Kc S' q K'} (hp : Path M Ψd A S Kc c S' q K') (hS : PeriphsOK Δ S) :
    ∃ L, SlackRun P M Ψ Ψd Γ Δ c Γ' Δ' Q F A S Kc S' q K' L ∧
      (∀ i ∈ L, i.actual ≤ i.typed) ∧ Q Kc (ambBg M A) = q + slack L :=
  have ⟨L, hL, hle, _, _⟩ := SlackRun.exists hM hΨv hΨd hp ht hS
  ⟨L, hL, hle, hL.decompose hle⟩

/-- **The decomposition for real executions.**  Every run of `Eval` is a path, so its cost is the
summary minus exactly the recorded slack. -/
theorem Eval.slack_decomposition (hM : M.WF) (hΨv : SigsValid M Ψd Ψ)
    (hΨd : SigsDerived P M Ψd Ψ) {Γ Δ c Γ' Δ' Q F} (ht : Typed P M Ψ Γ Δ c Γ' Δ' Q F)
    {A σ S Kc σ' S' q K'} (he : Eval M Ψd A σ S Kc c σ' S' q K') (hS : PeriphsOK Δ S) :
    ∃ L, SlackRun P M Ψ Ψd Γ Δ c Γ' Δ' Q F A S Kc S' q K' L ∧
      (∀ i ∈ L, i.actual ≤ i.typed) ∧ Q Kc (ambBg M A) = q + slack L :=
  _root_.slack_decomposition hM hΨv hΨd ht he.toPath hS

omit [IsOrderedRing R] in
/-- **Exactness when there is no slack.**  If every recorded term has `typed = actual` — e.g.
all contexts along the path pin down the states, the path takes the costlier branch at each
`if`, and no clock is merged — the summary is exactly the path's cost. -/
theorem SlackRun.exact {Γ Δ c Γ' Δ' Q F A S Kc S' q K' L}
    (hL : SlackRun P M Ψ Ψd Γ Δ c Γ' Δ' Q F A S Kc S' q K' L)
    (h0 : ∀ i ∈ L, i.typed = i.actual) : Q Kc (ambBg M A) = q := by
  have hz : slack L = 0 := by
    unfold slack
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    simp only [SlackItem.delta, h0 i hi, tsub_self]
  rw [hL.decompose (fun i hi => (h0 i hi).ge), hz, add_zero]

end Main
