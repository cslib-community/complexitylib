/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.PolyTime.BooleanAnalysis.SparsePolyCounter
public import Complexity.Computability.PolyTime.GreedyLabelSchedule
public import Complexity.Computability.PolyTime.LinearAlgebra.ReplacementDesignBuilder
public import Complexity.Computability.PolyTime.LinearAlgebra.BooleanMeasurements
public import Complexity.Computability.PolyTime.CommonCountingAccum
public import Complexity.Computability.PolyTime.SparseMonomialJet
public import Complexity.Computability.GenericRAM.Native.MeasurementFold
public import Complexity.Computability.GenericRAM.Native.SubsetPairFold
public import Complexity.Foundations.BooleanAnalysis.SparseHermiteRecovery
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Executable bounded-incidence branch evaluator and Stage-1 design refinement (Proposition 5.3)

Pure executable bounded-incidence branch evaluator
`evalBoundedIncidenceBranch : BranchEvalInput → ℕ`, entry and design-shape guards
(`validBranchEvalParams`, `validDesignShape`), unconditional cube bound
`evalBoundedIncidenceBranch_le_two_pow`, Stage-1 parameter unclamping and `ReplacementDesign`
refinement on feasible prepared inputs (`prepareBranchEvalInput (n', eqs')` under
`checkBranchFeasible N₀_branch (n', eqs') = true`), and Stage-2 local assignment/cube bridges for
Proposition 5.3 of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
(§§3.4–3.5, §4.6, §§5.3–5.5, Proposition 5.3, and Appendix B.2–B.3, pp. 24–26, 33–34, 37–39,
48–50). Invalid raw inputs return `0`, `validDesignShape` enforces unary resource-dimension bounds
rather than semantic validity of arbitrary designs, and exact root-count recovery on feasible
prepared inputs follows in `BoundedIncidenceExactness`.

Given `inp = ((n', k'), (b, w, M', β), (r, Q, R, A₀), eqs') : BranchEvalInput`:

1. **Entry guard and unary-clamped parameters**: `validBranchEvalParams` checks the structural and
   schedule range invariants (including `r_u ^ (2 * Q_u) ≤ n'`, variable bounds `< n'`,
   canonicality, and `sysMaxDegree eqs' ≤ k'`), clamping `(Q, R, r, A₀, D)` from the left against
   unary expressions in `n'` so resource certificates remain uniform across all `BranchEvalInput`
   tuples.
2. **Greedy balanced schedule and Lemma 4.7 replacement design**: augments equation scopes with
   neutral singletons via `withNeutralScopesList`, constructs balanced variable/factor schedules via
   `BalancedSchedules.constructBalancedSchedules`, builds `ReplacementDesignData` via
   `buildReplacementDesignData`, and precomputes per-equation replacement-row lookup tables.
3. **Two-pass measurement-fiber jet accumulation and Hermite–Cramer recovery**: for each node
   `t < Q_u` (`node = t + 1`), folds over subset pairs `(E, U, oddSign)` via `SubsetPairFold.run`
   and signed measurement tuples via `MeasurementFold.run`; Pass 1 finds unrestricted local fiber
   representatives via `BooleanMeasurements.search`, Pass 2 streams restricted local fiber jet sums
   via `CommonCountingAccum.streamGroupJetSum` using `evalAffineInputZJetTable` and
   `evalEquationParityFactorJet`, multiplies group jets via `CommonCountingAccum.prodJet`, and
   recovers the count modulo `2 ^ (n' + 1)` via
   `CommonCountingAccum.recoverOuterJetSumModPowTwo`.

## Main definitions

* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.validBranchEvalParams`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.validDesignShape`: Boolean entry and unary
  design-shape guards on `BranchEvalInput` and `ReplacementDesignData`.
* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.applyGroupBits`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.buildBaseAssignment`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.checkRestrictedGroup`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.buildEqRowTables`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.groupEquationsAt`: local group bit
  overrides, restricted-cube test, and precomputed per-equation replacement-row tables.
* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.GroupEvalCtx`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.MeasStepCtx`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.SubsetStepCtx`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.evalGroupFactorJet`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.measurementStepBody`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.subsetPairStepBody`: closed step contexts
  and step bodies for `CommonCountingAccum.streamGroupJetSum`, `MeasurementFold.run`, and
  `SubsetPairFold.run`.
* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.evalBoundedIncidenceBranch`: executable
  Proposition 5.3 branch evaluator `BranchEvalInput → ℕ`.

## Main results

* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.evalBoundedIncidenceBranch_le_two_pow`:
  unconditional upper bound `evalBoundedIncidenceBranch inp ≤ 2 ^ inp.1.1`.
* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.validBranchEvalParams_prepare_of_feasible`:
  passing `checkBranchFeasible` implies `validBranchEvalParams` on `prepareBranchEvalInput`.
* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.exists_refines_prepare_of_feasible`:
  Stage-1 `ReplacementDesignData.Refines` witness and unclamped parameter identities on feasible
  prepared inputs.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §§3.4–3.5, §4.6, §§5.3–5.5,
  Proposition 5.3, and Appendix B.2–B.3.
-/

@[expose] public section

namespace Cslib.Complexity.SubexponentialSAT.SparsePolyCounter

open Finset Cslib Cslib.BitString Cslib.Complexity Cslib.GenericRAM Cslib.LinearAlgebra

/-! ### 1. Entry Guard, Clamped Parameters, and Stage-1/Stage-2 Helpers -/

/-- Entry guard on `inp = ((n', k'), (b, w, M', β), (r, Q, R, A₀), eqs') : BranchEvalInput`
verifying structural nondegeneracy, unary parameter bounds against `n'`, auxiliary dimension bound
`r_u ^ (2 * Q_u) ≤ n'`, variable range `< n'`, canonicality, and degree bound `≤ k'`. -/
def validBranchEvalParams (inp : BranchEvalInput) : Bool :=
  let n' := inp.1.1
  let k' := inp.1.2
  let r := inp.2.2.1.1
  let Q := inp.2.2.1.2.1
  let R := inp.2.2.1.2.2.1
  let A₀ := inp.2.2.1.2.2.2
  let eqs' := inp.2.2.2
  let Q_u := min n' Q
  let r_u := min n' r
  decide (1 ≤ n') && decide (2 ≤ r) && decide (1 ≤ R) && decide (R < Q) &&
    decide (Q ≤ n') && decide (r ≤ n') && decide (A₀ + R ≤ Q + 1) &&
    decide (r_u ^ (2 * Q_u) ≤ n') &&
    checkVarsLt n' eqs' && checkCanonicalSystem eqs' && decide (sysMaxDegree eqs' ≤ k')

/-- Design-shape guard checking unary measurement-dimension and local-group size bounds on
`ReplacementDesignData` (both hold automatically under `ReplacementParams.Feasible`). -/
def validDesignShape (n' r_u m_eq : ℕ) (data : ReplacementDesignData) : Bool :=
  decide (r_u * data.measurementMatrix.length ≤ 4 * (n' + 1) * (m_eq * n' + n' + 1)) &&
    data.varGroups.all fun gs => gs.all fun Vg => decide (Vg.length ≤ 2 * n')

/-- Override coordinates `v ∈ Vg` of `base` (of length `n'`) using local bits `ug`. -/
def applyGroupBits (n' : ℕ) (Vg : List ℕ) (ug : List Bool) (base : List Bool) : List Bool :=
  (List.range n').map fun v =>
    (List.range Vg.length).foldl
      (fun cur j => if Vg.getD j n' == v then ug.getD j false else cur)
      (base.getD v false)

/-- Assemble the baseline length-`n'` assignment `x^*` from per-group representatives `reps`. -/
def buildBaseAssignment (n' r_u : ℕ) (vGroups_t : List (List ℕ)) (reps : List (List Bool)) :
    List Bool :=
  (List.range r_u).foldl
    (fun acc g => applyGroupBits n' (vGroups_t.getD g []) (reps.getD g []) acc)
    (List.replicate n' false)

/-- Check `restrictedLocalCube` membership on `Vg`: every `Vg[j]` marked in `indE` has
`ug[j] = true`. -/
def checkRestrictedGroup (n' : ℕ) (indE : List Bool) (Vg : List ℕ) (ug : List Bool) : Bool :=
  (List.range Vg.length).all fun j => !(indE.getD (Vg.getD j n') false) || ug.getD j false

/-- Precompute for each equation `f < eqs'.length` and variable `v < n'` the cleared replacement
row table `data.lookupReplacementRow f v`. -/
def buildEqRowTables (n' : ℕ) (eqs' : List (List (List ℕ))) (data : ReplacementDesignData) :
    List (List (List (List ℤ))) :=
  (List.range eqs'.length).map fun f =>
    (List.range n').map fun v => data.lookupReplacementRow f v

/-- Context bundle for `evalGroupFactorJet` inside `CommonCountingAccum.streamGroupJetSum`:
`((n', J, ℓ, k'), (node, denom), (Vg, Ctg, yg), (indE, indU, xStar), groupEqsWithTables)` where
each pair in `groupEqsWithTables` is `(eq, rowsCoeffs_f)` for an equation in group `g` at `t`. -/
abbrev GroupEvalCtx : Type :=
  (ℕ × ℕ × ℕ × ℕ) × (ℤ × ℤ) × (List ℕ × List (List ℤ) × List ℤ) ×
    (List Bool × List Bool × List Bool) × List (List (List ℕ) × List (List (List ℤ)))

/-- Closed local-cube summand for `CommonCountingAccum.streamGroupJetSum`: returns `0` unless `ug`
belongs to the `indE`-restricted local cube and matches measurement slice `yg`, in which case it
evaluates the product of cleared parity-factor jets over equations assigned to group `g` at `t`. -/
def evalGroupFactorJet (p : GroupEvalCtx × (ℕ × List Bool)) : JetRows :=
  let ctx := p.1
  let ug := p.2.2
  let n' := ctx.1.1
  let J := ctx.1.2.1
  let ℓ := ctx.1.2.2.1
  let k' := ctx.1.2.2.2
  let node := ctx.2.1.1
  let dDen := ctx.2.1.2
  let Vg := ctx.2.2.1.1
  let Ctg := ctx.2.2.1.2.1
  let yg := ctx.2.2.1.2.2
  let indE := ctx.2.2.2.1.1
  let indU := ctx.2.2.2.1.2.1
  let xStar := ctx.2.2.2.1.2.2
  let grpEqs := ctx.2.2.2.2
  if checkRestrictedGroup n' indE Vg ug &&
      decide (BooleanMeasurements.evalBoolMatrix Ctg ug = yg) then
    let x := applyGroupBits n' Vg ug xStar
    let factors := grpEqs.map fun eqPair =>
      let varJets := evalAffineInputZJetTable J node eqPair.2 indU x
      evalEquationParityFactorJet J ℓ k' dDen varJets eqPair.1
    CommonCountingAccum.prodJet J ℓ factors
  else
    zeroJet J ℓ

/-- Precollect `(eq, rowsCoeffs_f)` for equations `f < eqs'.length` assigned to group `g` at `t`. -/
def groupEquationsAt (eqs' : List (List (List ℕ))) (factorGroups : List (List ℕ))
    (eqRowTables : List (List (List (List ℤ)))) (t g : ℕ) :
    List (List (List ℕ) × List (List (List ℤ))) :=
  ((List.range eqs'.length).filter fun f =>
      decide ((factorGroups.getD f []).getD t 0 = g)).map fun f =>
    (eqs'.getD f [], eqRowTables.getD f [])

/-- Context bundle carried unchanged through `MeasurementFold.run` at fixed `(t, E, U)`:
`((n', r_u, m_rows), (J, ℓ, k'), (node, dDen), (vGroups_t, grpMeas_t), (indE, indU), grpEqs)`. -/
abbrev MeasStepCtx : Type :=
  (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × (ℤ × ℤ) × (List (List ℕ) × List (List (List ℤ))) ×
    (List Bool × List Bool) × List (List (List (List ℕ) × List (List (List ℤ))))

/-- Closed step body for `MeasurementFold.run`: slices `word` into per-group targets `yg`, runs
Pass 1 (`BooleanMeasurements.search`) across all `g < r_u`, and when all fibers are nonempty runs
Pass 2 (`CommonCountingAccum.streamGroupJetSum`) across all `g < r_u` and adds their `prodJet`. -/
def measurementStepBody (inp : ((ℕ × ℕ) × List ℤ) × (MeasStepCtx × JetRows)) :
    MeasStepCtx × JetRows :=
  let word := inp.1.2
  let ctx := inp.2.1
  let acc := inp.2.2
  let n' := ctx.1.1
  let r_u := ctx.1.2.1
  let m_rows := ctx.1.2.2
  let J := ctx.2.1.1
  let ℓ := ctx.2.1.2.1
  let k' := ctx.2.1.2.2
  let node := ctx.2.2.1.1
  let dDen := ctx.2.2.1.2
  let vGroups_t := ctx.2.2.2.1.1
  let grpMeas_t := ctx.2.2.2.1.2
  let indE := ctx.2.2.2.2.1.1
  let indU := ctx.2.2.2.2.1.2
  let grpEqLists := ctx.2.2.2.2.2
  let repOpts : List (Option (List Bool)) := (List.range r_u).map fun g =>
    let Vg := vGroups_t.getD g []
    let dg := min (2 * n') Vg.length
    let Ctg := grpMeas_t.getD g []
    let yg := (word.drop (g * m_rows)).take m_rows
    BooleanMeasurements.search Prod.fst Prod.snd ((Ctg, yg), dg)
  if repOpts.all Option.isSome then
    let reps := repOpts.map fun o => o.getD []
    let xStar := buildBaseAssignment n' r_u vGroups_t reps
    let groupJets := (List.range r_u).map fun g =>
      let Vg := vGroups_t.getD g []
      let dg := min (2 * n') Vg.length
      let Ctg := grpMeas_t.getD g []
      let yg := (word.drop (g * m_rows)).take m_rows
      let grpCtx : GroupEvalCtx :=
        ((n', J, ℓ, k'), (node, dDen), (Vg, Ctg, yg), (indE, indU, xStar), grpEqLists.getD g [])
      CommonCountingAccum.streamGroupJetSum evalGroupFactorJet J ℓ dg grpCtx
    (ctx, addJet J ℓ acc (CommonCountingAccum.prodJet J ℓ groupJets))
  else
    (ctx, acc)

/-- Context bundle carried unchanged through `SubsetPairFold.run` at fixed node `t`:
`((n', r_u, m_rows), (c_meas, D_cap), (J, ℓ, k'), (node, dDen), (vGroups_t, grpMeas_t), eqs)`. -/
abbrev SubsetStepCtx : Type :=
  (ℕ × ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ × ℕ) × (ℤ × ℤ) × (List (List ℕ) × List (List (List ℤ))) ×
    List (List (List (List ℕ) × List (List (List ℤ))))

/-- Closed step body for `SubsetPairFold.run`: accumulates the signed measurement-fiber jet sum at
`(indE, indU, oddSign)` via `MeasurementFold.run`. -/
def subsetPairStepBody (inp : SubsetPairFold.DecodedPair × (SubsetStepCtx × JetRows)) :
    SubsetStepCtx × JetRows :=
  let indE := inp.1.1
  let indU := inp.1.2.1
  let oddSign := inp.1.2.2
  let ctx := inp.2.1
  let acc := inp.2.2
  let n' := ctx.1.1
  let r_u := ctx.1.2.1
  let m_rows := ctx.1.2.2
  let c_meas := ctx.2.1.1
  let D_cap := ctx.2.1.2
  let J := ctx.2.2.1.1
  let ℓ := ctx.2.2.1.2.1
  let k' := ctx.2.2.1.2.2
  let node := ctx.2.2.2.1.1
  let dDen := ctx.2.2.2.1.2
  let vGroups_t := ctx.2.2.2.2.1.1
  let grpMeas_t := ctx.2.2.2.2.1.2
  let grpEqLists := ctx.2.2.2.2.2
  let measCtx : MeasStepCtx :=
    ((n', r_u, m_rows), (J, ℓ, k'), (node, dDen), (vGroups_t, grpMeas_t), (indE, indU), grpEqLists)
  let measJet :=
    (MeasurementFold.run measurementStepBody (c_meas, D_cap) (measCtx, zeroJet J ℓ)).2.2.2
  let signedJet := if oddSign then smulJet J ℓ (-1) measJet else measJet
  (ctx, addJet J ℓ acc signedJet)

/-- **Proposition 5.3 executable bounded-incidence branch evaluator**
([OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §§5.3–5.5, Proposition 5.3,
pp. 37–39): on feasible prepared inputs (`prepareBranchEvalInput (n', eqs')` when
`checkBranchFeasible N₀_branch (n', eqs') = true`), evaluates the exact number of common `𝔽₂`
roots of `eqs'` on `{0, 1}^{n'}` via greedy balanced scheduling, Lemma 4.7 replacement-design
construction, two-pass measurement-fiber Taylor jet accumulation, and Hermite–Cramer modular
recovery. Invalid raw `BranchEvalInput` tuples fail `validBranchEvalParams` or the unary
resource-dimension guard `validDesignShape` (which bounds measurement and group dimensions rather
than certifying arbitrary designs) and return `0`. -/
def evalBoundedIncidenceBranch (inp : BranchEvalInput) : ℕ :=
  if !validBranchEvalParams inp then 0
  else
    let n' := inp.1.1
    let k' := inp.1.2
    let b := inp.2.1.1
    let w := inp.2.1.2.1
    let r := inp.2.2.1.1
    let Q := inp.2.2.1.2.1
    let R := inp.2.2.1.2.2.1
    let A₀ := inp.2.2.1.2.2.2
    let eqs' := inp.2.2.2
    let Q_u := min n' Q
    let R_u := min n' R
    let r_u := min n' r
    let A₀_u := min (n' + 1) A₀
    let D_cap := min n' (r_u ^ (2 * Q_u))
    let ℓ := n' + 1
    let q := (k' * (R_u - 1)) * (eqs'.length + 2 * n') / max 1 Q_u
    let J := q + 1
    let scopes := eqs'.map equationVars
    let augScopes := withNeutralScopesList scopes n'
    let edges := scopeIncidencesList n' augScopes
    let scheds := BalancedSchedules.constructBalancedSchedules
      n' augScopes.length Q_u r_u (b + w) edges
    let data := buildReplacementDesignData
      n' D_cap Q_u r_u A₀_u R_u augScopes scheds.1 scheds.2
    if !validDesignShape n' r_u eqs'.length data then 0
    else
      let m_rows := data.measurementMatrix.length
      let c_meas := min (4 * (n' + 1) * (eqs'.length * n' + n' + 1)) (r_u * m_rows)
      let eqRowTables := buildEqRowTables n' eqs' data
      let nodes : List ℤ := (List.range Q_u).map fun (t : ℕ) => ((t : ℤ) + 1)
      let nodeJets : List JetRows := (List.range Q_u).map fun (t : ℕ) =>
        let node : ℤ := (t : ℤ) + 1
        let vGroups_t := data.varGroups.getD t []
        let grpMeas_t := data.groupMeasurementMatrices.getD t []
        let grpEqLists := (List.range r_u).map fun g =>
          groupEquationsAt eqs' data.factorGroups eqRowTables t g
        let subCtx : SubsetStepCtx :=
          ((n', r_u, m_rows), (c_meas, D_cap), (J, ℓ, k'), (node, data.denom),
            (vGroups_t, grpMeas_t), grpEqLists)
        (SubsetPairFold.run subsetPairStepBody n' q (subCtx, zeroJet J ℓ)).2
      let Ω : ℤ := ((data.denom ^ k') ^ (2 * ℓ - 1)) ^ eqs'.length
      let recCount := CommonCountingAccum.recoverOuterJetSumModPowTwo nodes J ℓ Ω nodeJets
      min (2 ^ n') recCount.toNat

/-! ### 2. Unconditional Cube Upper Bound -/

/-- `evalBoundedIncidenceBranch inp` never exceeds the ambient Boolean cube size `2 ^ n'`. -/
theorem evalBoundedIncidenceBranch_le_two_pow (inp : BranchEvalInput) :
    evalBoundedIncidenceBranch inp ≤ 2 ^ inp.1.1 := by
  unfold evalBoundedIncidenceBranch
  dsimp only
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.min_le_left _ _

/-! ### 3. Stage-1 Parameter Unclamping and `ReplacementDesignData` Refinement -/

section Stage1

open Cslib.BalancedSchedules

private theorem getD_map_range {α : Type*} (f : ℕ → α) (d : α) {n i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  have hi' : i < ((List.range n).map f).length := by
    simpa only [List.length_map, List.length_range] using hi
  rw [List.getD_eq_getElem _ _ hi', List.getElem_map, List.getElem_range]

private theorem auxDim_le_of_twenty_le {n' : ℕ} (hn : 20 ≤ n') :
    ReplacementParams.auxDim n' ≤ n' := by
  have h5 : 5 ≤ Nat.clog 2 n' := by
    calc 5 = Nat.clog 2 20 := by decide
      _ ≤ Nat.clog 2 n' := Nat.clog_mono_right 2 hn
  have hdiv : Nat.clog 2 n' / 128 ≤ Nat.clog 2 n' - 1 := by omega
  calc ReplacementParams.auxDim n'
      ≤ 2 ^ (Nat.clog 2 n' / 128) := ReplacementParams.auxDim_le_two_pow n'
    _ ≤ 2 ^ (Nat.clog 2 n' - 1) := Nat.pow_le_pow_right (by omega) hdiv
    _ ≤ n' := (Nat.pow_pred_clog_lt_self (by omega : 1 < 2) (by omega : 1 < n')).le

/-- Passing `checkBranchFeasible` implies `validBranchEvalParams` on `prepareBranchEvalInput`. -/
theorem validBranchEvalParams_prepare_of_feasible {N₀_branch n' : ℕ}
    {eqs' : List (List (List ℕ))} (hfeas : checkBranchFeasible N₀_branch (n', eqs') = true) :
    validBranchEvalParams (prepareBranchEvalInput (n', eqs')) = true := by
  have hf := feasible_of_checkBranchFeasible hfeas
  dsimp only [prepareBranchEvalInput] at hf
  obtain ⟨_, _, _, hF⟩ := hf
  have hchk := hfeas
  unfold checkBranchFeasible at hchk
  simp only [Bool.and_eq_true] at hchk
  have hvars_b : checkVarsLt n' eqs' = true := hchk.1.1.2
  have hcan_b : checkCanonicalSystem eqs' = true := hchk.1.2
  set β := ParameterCheck.chooseBeta (Nat.clog 2 n')
    (branchMaxFactorIncidence n' eqs') (branchMaxFactorWidth n' eqs')
  have h20 : 20 ≤ n' := hF.twenty_le
  have h1n : 1 ≤ n' := hF.one_le_n
  have hr2 : 2 ≤ ReplacementParams.numGroups n' := hF.two_le_numGroups
  have hR1 : 1 ≤ ReplacementParams.rowBound β n' := hF.one_le_rowBound
  have hRQ : ReplacementParams.rowBound β n' < ReplacementParams.numNodes n' :=
    hF.rowBound_lt_numNodes
  have hvb : 2 * ReplacementParams.numNodes n' * ReplacementParams.numGroups n' ^ 2 ≤ n' :=
    hF.var_balance
  have hQ1 : 1 ≤ ReplacementParams.numNodes n' := by omega
  have hr_sq : 4 ≤ ReplacementParams.numGroups n' ^ 2 := by nlinarith
  have hQn : ReplacementParams.numNodes n' ≤ n' := by nlinarith
  have hrn : ReplacementParams.numGroups n' ≤ n' := by nlinarith
  have hI : ReplacementParams.intervalStart β n' + (ReplacementParams.rowBound β n' - 1) ≤
      ReplacementParams.numNodes n' :=
    hF.intervalStart_add_le_numNodes (by omega)
  have hIR : ReplacementParams.intervalStart β n' + ReplacementParams.rowBound β n' ≤
      ReplacementParams.numNodes n' + 1 := by omega
  have haux : ReplacementParams.numGroups n' ^ (2 * ReplacementParams.numNodes n') ≤ n' :=
    auxDim_le_of_twenty_le h20
  unfold validBranchEvalParams prepareBranchEvalInput ParameterCheck.computeScheduleParams
  dsimp only
  rw [Nat.min_eq_right hQn, Nat.min_eq_right hrn]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1n, hr2⟩, hR1⟩, hRQ⟩, hQn⟩, hrn⟩, hIR⟩, haux⟩, hvars_b⟩, hcan_b⟩, le_rfl⟩

private theorem listScopeFamily_map_equationVars (n' : ℕ) (eqs' : List (List (List ℕ)))
    (f : Fin eqs'.length) :
    listScopeFamily n' (eqs'.map equationVars) ⟨f.1, by simp only [List.length_map]; exact f.2⟩ =
      equationScope (HeavyBranchFold.toFinsetEquation n' eqs'[f]) := by
  ext v
  simp only [listScopeFamily, mem_filter, mem_univ, true_and, Fin.getElem_fin, List.getElem_map,
    mem_equationVars, equationScope, HeavyBranchFold.toFinsetEquation, mem_biUnion,
    List.mem_toFinset, List.mem_map]
  exact ⟨fun ⟨m, hm, hv⟩ => ⟨univ.filter fun i : Fin n' => (i : ℕ) ∈ m, ⟨m, hm, rfl⟩,
      mem_filter.mpr ⟨mem_univ _, hv⟩⟩,
    fun ⟨_, ⟨m, hm, rfl⟩, hv⟩ => ⟨m, hm, (mem_filter.mp hv).2⟩⟩

private theorem sum_card_listScopeFamily_augScopes (n' : ℕ) (eqs' : List (List (List ℕ))) :
    let augScopes := withNeutralScopesList (eqs'.map equationVars) n'
    (∑ f : Fin augScopes.length, #(listScopeFamily n' augScopes f)) =
      branchAugmentedIncidence n' eqs' := by
  intro augScopes
  let scopes := eqs'.map equationVars
  change totalIncidence univ (listScopeFamily n' (withNeutralScopesList scopes n')) = _
  rw [totalIncidence_listScopeFamily_withNeutralScopesList, branchAugmentedIncidence]
  congr 1
  rw [totalIncidence, ← Equiv.sum_comp (finCongr (List.length_map equationVars).symm)]
  have hsum : (∑ f : Fin eqs'.length,
        #(equationScope (HeavyBranchFold.toFinsetEquation n' eqs'[f]))) =
      (eqs'.map (scopeWidthOn n')).sum := by
    rw [← List.toFinset_finRange, List.sum_toFinset _ (List.nodup_finRange _)]
    conv_rhs => rw [← (List.ofFn_eq_map.symm.trans (List.ofFn_getElem (xs := eqs'))), List.map_map]
    exact congrArg List.sum (List.map_congr_left fun i _ => by
      simp only [Function.comp_apply, Fin.getElem_fin, card_equationScope_toFinsetEquation])
  rw [← hsum]
  exact Finset.sum_congr rfl fun f _ =>
    congrArg Finset.card (listScopeFamily_map_equationVars n' eqs' f)

private theorem varIncidence_listScopeFamily_augScopes_le (n' : ℕ) (eqs' : List (List (List ℕ)))
    (v : Fin n') :
    let augScopes := withNeutralScopesList (eqs'.map equationVars) n'
    #{f : Fin augScopes.length | v ∈ listScopeFamily n' augScopes f} ≤
      branchMaxFactorIncidence n' eqs' := by
  intro augScopes
  let scopes := eqs'.map equationVars
  change varIncidence univ (listScopeFamily n' (withNeutralScopesList scopes n')) v ≤ _
  rw [varIncidence_listScopeFamily_withNeutralScopesList, branchMaxFactorIncidence]
  refine Nat.succ_le_succ ?_
  have hdeg : varIncidence univ (listScopeFamily n' scopes) v = varDegree v.1 eqs' := by
    have hfil : ({f ∈ (List.finRange scopes.length).toFinset |
        v ∈ listScopeFamily n' scopes f} : Finset (Fin scopes.length)) =
        ((List.finRange scopes.length).filter fun f =>
          decide (v.1 ∈ scopes[f])).toFinset := by
      ext f
      simp only [mem_filter, List.mem_toFinset, List.mem_filter, listScopeFamily, mem_univ,
        true_and, decide_eq_true_eq]
    rw [varIncidence, ← List.toFinset_finRange, hfil,
      List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _),
      ← List.countP_eq_length_filter, varDegree]
    have hmap : eqs'.map equationVars = scopes := rfl
    conv_rhs =>
      change List.countP ((fun vs => decide (v.1 ∈ vs)) ∘ equationVars) eqs'
      rw [← List.countP_map, hmap,
        ← (List.ofFn_eq_map.symm.trans (List.ofFn_getElem (xs := scopes))), List.countP_map]
    exact List.countP_congr fun i _ => by simp only [Function.comp_apply, Fin.getElem_fin]
  rw [hdeg]
  exact le_foldl_max_of_mem (List.mem_map_of_mem (List.mem_range.mpr v.isLt))

private theorem card_listScopeFamily_augScopes_le (n' : ℕ) (eqs' : List (List (List ℕ))) :
    let augScopes := withNeutralScopesList (eqs'.map equationVars) n'
    ∀ f : Fin augScopes.length, #(listScopeFamily n' augScopes f) ≤
      branchMaxFactorWidth n' eqs' := by
  intro augScopes f
  let scopes := eqs'.map equationVars
  let eqv := withNeutralScopesIndexEquiv scopes n'
  have hf_eq : f = eqv (eqv.symm f) := (eqv.apply_symm_apply f).symm
  rw [hf_eq, listScopeFamily_withNeutralScopesList]
  rcases eqv.symm f with g | v
  · dsimp only [withNeutralScope]
    have hg : g.1 < eqs'.length := by simpa only [scopes, List.length_map] using g.2
    have hsc := listScopeFamily_map_equationVars n' eqs' ⟨g.1, hg⟩
    change listScopeFamily n' scopes g = _ at hsc
    rw [hsc, card_equationScope_toFinsetEquation, branchMaxFactorWidth]
    exact le_foldl_max_of_mem (List.mem_map_of_mem (List.getElem_mem hg))
  · dsimp only [withNeutralScope]
    rw [card_singleton]
    exact one_le_branchMaxFactorWidth n' eqs'

private theorem balancedSchedule_construct_of_scopes {n' Q r b w : ℕ}
    (augScopes : List (List ℕ)) (hn : 1 ≤ n') (hr : 1 ≤ r) (hQ : 1 ≤ Q) (hbw : 0 < b + w)
    (hb : ∀ v : Fin n', #{f : Fin augScopes.length | v ∈ listScopeFamily n' augScopes f} ≤ b)
    (hw : ∀ f : Fin augScopes.length, #(listScopeFamily n' augScopes f) ≤ w)
    (hinc : 2 * (b + w) * (r ^ (2 * Q)) ^ 2 ≤
      ∑ f : Fin augScopes.length, #(listScopeFamily n' augScopes f))
    (hgrp : 2 * Q * r ^ 2 ≤ n') :
    let edges := scopeIncidencesList n' augScopes
    let scheds := BalancedSchedules.constructBalancedSchedules
      n' augScopes.length Q r (b + w) edges
    BalancedSchedule hr n' Q augScopes scheds.1 scheds.2 := by
  intro edges scheds
  let scope := listScopeFamily n' augScopes
  let edge : Fin edges.length → Fin augScopes.length × Fin n' := fun i =>
    let e := finToScopeIncidence n' augScopes i
    (scopeFactorOf scope e, scopeVarOf scope e)
  have hedges_eq : BalancedSchedules.edgesOfFin edge = edges := by
    refine List.ext_getElem (by simp only [BalancedSchedules.edgesOfFin, List.length_ofFn])
      fun i hi _ => ?_
    simp only [BalancedSchedules.edgesOfFin, List.getElem_ofFn, edge, scopeFactorOf, scopeVarOf,
      finToScopeIncidence, edges]
  have hinj_edge : Function.Injective edge := by
    intro i₁ i₂ heq
    have hbij := (bijective_finToScopeIncidence n' augScopes).1
    apply hbij
    have h1 : scopeFactorOf scope (finToScopeIncidence n' augScopes i₁) =
        scopeFactorOf scope (finToScopeIncidence n' augScopes i₂) := congrArg Prod.fst heq
    have h2 : scopeVarOf scope (finToScopeIncidence n' augScopes i₁) =
        scopeVarOf scope (finToScopeIncidence n' augScopes i₂) := congrArg Prod.snd heq
    rcases he1 : finToScopeIncidence n' augScopes i₁ with ⟨f₁, v₁, hv₁⟩
    rcases he2 : finToScopeIncidence n' augScopes i₂ with ⟨f₂, v₂, hv₂⟩
    rw [he1, he2] at h1 h2
    dsimp only [scopeFactorOf, scopeVarOf] at h1 h2
    subst h1; subst h2; rfl
  have hb_edge : ∀ e : Fin edges.length,
      #{e' : Fin edges.length | (edge e').2 = (edge e).2} ≤ b := fun e => by
    have hsub : (univ.filter fun e' : Fin edges.length => (edge e').2 = (edge e).2).image
        (fun e' => (edge e').1) ⊆ univ.filter fun f => (edge e).2 ∈ scope f := by
      intro f hf
      obtain ⟨e', he', rfl⟩ := mem_image.mp hf
      rw [mem_filter] at he' ⊢
      refine ⟨mem_univ _, ?_⟩
      rw [← he'.2]
      exact (finToScopeIncidence n' augScopes e').2.2
    have hinj_on : Set.InjOn (fun e' : Fin edges.length => (edge e').1)
        ↑(univ.filter fun e' : Fin edges.length => (edge e').2 = (edge e).2) := by
      intro e₁ he₁ e₂ he₂ hf_eq
      rw [mem_coe, mem_filter] at he₁ he₂
      exact hinj_edge (Prod.ext hf_eq (he₁.2.trans he₂.2.symm))
    exact (Finset.card_image_of_injOn hinj_on).symm.trans_le
      ((card_le_card hsub).trans (hb (edge e).2))
  have hw_edge : ∀ e : Fin edges.length,
      #{e' : Fin edges.length | (edge e').1 = (edge e).1} ≤ w := fun e => by
    have hsub : (univ.filter fun e' : Fin edges.length => (edge e').1 = (edge e).1).image
        (fun e' => (edge e').2) ⊆ scope (edge e).1 := by
      intro v hv
      obtain ⟨e', he', rfl⟩ := mem_image.mp hv
      rw [mem_filter] at he'
      rw [← he'.2]
      exact (finToScopeIncidence n' augScopes e').2.2
    have hinj_on : Set.InjOn (fun e' : Fin edges.length => (edge e').2)
        ↑(univ.filter fun e' : Fin edges.length => (edge e').1 = (edge e).1) := by
      intro e₁ he₁ e₂ he₂ hv_eq
      rw [mem_coe, mem_filter] at he₁ he₂
      exact hinj_edge (Prod.ext (he₁.2.trans he₂.2.symm) hv_eq)
    exact (Finset.card_image_of_injOn hinj_on).symm.trans_le
      ((card_le_card hsub).trans (hw (edge e).1))
  have hinc' : 2 * (b + w) * ((r ^ Q) ^ 2) ^ 2 ≤ edges.length := by
    rw [length_scopeIncidencesList]
    have hpow : ((r ^ Q) ^ 2) ^ 2 = (r ^ (2 * Q)) ^ 2 := by
      rw [← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      omega
    rwa [hpow]
  obtain ⟨hempty, hocc_inc, hocc_grp⟩ :=
    BalancedSchedules.constructBalancedSchedules_balanced hr hQ hn edge hb_edge hw_edge hbw
      hinc' hgrp
  have hwf := BalancedSchedules.wf_constructBalancedSchedules n' augScopes.length Q r (b + w) edges
  let a := BalancedSchedules.constructedVarSchedule hr n' augScopes.length Q (b + w) edges
  let d := BalancedSchedules.constructedFactorSchedule hr n' augScopes.length Q (b + w) edges
  have ha_eq : varAssignOfList hr n' Q scheds.1 = a := by
    funext v t; apply Fin.ext
    dsimp only [scheds]
    have hv_lt : v.1 < (BalancedSchedules.constructBalancedSchedules
        n' augScopes.length Q r (b + w) edges).1.length := by
      rw [BalancedSchedules.length_fst_constructBalancedSchedules]; exact v.2
    obtain ⟨hlen_w, hlt_w⟩ := hwf.1 _ (List.getElem_mem hv_lt)
    have ht_lt : t.1 < (BalancedSchedules.constructBalancedSchedules
        n' augScopes.length Q r (b + w) edges).1[v.1].length := by rw [hlen_w]; exact t.2
    have hx_lt : (BalancedSchedules.constructBalancedSchedules
        n' augScopes.length Q r (b + w) edges).1[v.1][t.1] < r := by
      simpa only [Nat.max_eq_left hr] using hlt_w _ (List.getElem_mem ht_lt)
    simp only [val_varAssignOfList, normalizeVarSchedules, getD_map_range _ [] v.2,
      List.getD_eq_getElem _ [] hv_lt, normalizeScheduleWord, getD_map_range _ 0 t.2,
      List.getD_eq_getElem _ 0 ht_lt, Nat.max_eq_left hr, Nat.mod_eq_of_lt hx_lt, a,
      BalancedSchedules.constructedVarSchedule, BalancedSchedules.wordToSchedule, hx_lt,
      ↓reduceDIte]
  have hd_eq : factorAssignOfList hr n' Q augScopes scheds.2 = d := by
    funext f t; apply Fin.ext
    dsimp only [scheds]
    by_cases hemp : scope f = ∅
    · have hno_e : ¬ ∃ e : Fin edges.length, (edge e).1 = f := by
        rintro ⟨e, rfl⟩
        have hmem : (edge e).2 ∈ scope (edge e).1 := (finToScopeIncidence n' augScopes e).2.2
        rw [hemp] at hmem
        exact notMem_empty _ hmem
      have hd0 : d f = fun _ => ⟨0, hr⟩ := by
        dsimp only [d]; rw [← hedges_eq]; exact hempty f hno_e
      rw [factorAssignOfList_of_empty hr n' Q augScopes _ hemp t, hd0]
    · have hf_lt : f.1 < (BalancedSchedules.constructBalancedSchedules
          n' augScopes.length Q r (b + w) edges).2.length := by
        rw [BalancedSchedules.length_snd_constructBalancedSchedules]; exact f.2
      obtain ⟨hlen_w, hlt_w⟩ := hwf.2 _ (List.getElem_mem hf_lt)
      have ht_lt : t.1 < (BalancedSchedules.constructBalancedSchedules
          n' augScopes.length Q r (b + w) edges).2[f.1].length := by rw [hlen_w]; exact t.2
      have hx_lt : (BalancedSchedules.constructBalancedSchedules
          n' augScopes.length Q r (b + w) edges).2[f.1][t.1] < r := by
        simpa only [Nat.max_eq_left hr] using hlt_w _ (List.getElem_mem ht_lt)
      have hfalse : (canonicalScopeVars n' (augScopes.getD f.1 [])).isEmpty = false :=
        Bool.eq_false_iff.mpr fun h => hemp ((canonicalScopeVars_isEmpty_iff n' augScopes f).mp h)
      simp only [val_factorAssignOfList, normalizeScopeSchedules, getD_map_range _ [] f.2,
        hfalse, Bool.false_eq_true, ↓reduceIte, List.getD_eq_getElem _ [] hf_lt,
        normalizeScheduleWord, getD_map_range _ 0 t.2, List.getD_eq_getElem _ 0 ht_lt,
        Nat.max_eq_left hr, Nat.mod_eq_of_lt hx_lt, d,
        BalancedSchedules.constructedFactorSchedule, BalancedSchedules.wordToSchedule, hx_lt,
        ↓reduceDIte]
  refine ⟨fun u => ?_, fun t g => ?_⟩
  · rw [ha_eq, hd_eq]
    have hcard_inc : Fintype.card (ScopeIncidence scope) = edges.length := by
      simpa only [Fintype.card_fin] using Fintype.card_congr (scopeIncidenceEquivFin n' augScopes)
    have hocc_eq : occupancy (incidenceLabel (scopeVarOf scope) (scopeFactorOf scope) a d) u =
        occupancy (fun i : Fin edges.length => (a (edge i).2, d (edge i).1)) u := by
      unfold occupancy
      exact Fintype.card_congr
        { toFun := fun ⟨e, he⟩ =>
            ⟨scopeIncidenceEquivFin n' augScopes e, by
              simpa only [edge, finToScopeIncidence_scopeIncidenceEquivFin,
                incidenceLabel] using he⟩
          invFun := fun ⟨i, hi⟩ =>
            ⟨finToScopeIncidence n' augScopes i, by simpa only [incidenceLabel, edge] using hi⟩
          left_inv := fun ⟨e, _⟩ =>
            Subtype.ext (finToScopeIncidence_scopeIncidenceEquivFin _ _ e)
          right_inv := fun ⟨i, _⟩ =>
            Subtype.ext (scopeIncidenceEquivFin_finToScopeIncidence _ _ i) }
    have hu := hocc_inc u
    rw [hedges_eq] at hu
    have hpow : (r ^ Q) ^ 2 = r ^ (2 * Q) := by rw [← pow_mul, mul_comm Q 2]
    rw [hcard_inc, hocc_eq, ← hpow]
    exact hu
  · rw [ha_eq]
    have hg := hocc_grp t g
    rwa [hedges_eq] at hg

/-- Under `checkBranchFeasible N₀_branch (n', eqs') = true`, the clamped schedule parameters in
`evalBoundedIncidenceBranch (prepareBranchEvalInput (n', eqs'))` equal the unclamped schedule
parameters, `buildReplacementDesignData` refines a concrete `ReplacementDesign` on
`withNeutralScopesList (eqs'.map equationVars) n'`, its measurement matrix has
`D.h * #(measurementIndices Q r A₀ R)` rows with `r * data.measurementMatrix.length ≤ n'`, and
`validDesignShape` returns `true`. -/
theorem exists_refines_prepare_of_feasible {N₀_branch n' : ℕ} {eqs' : List (List (List ℕ))}
    (hfeas : checkBranchFeasible N₀_branch (n', eqs') = true) :
    let inp := prepareBranchEvalInput (n', eqs')
    let b := inp.2.1.1
    let w := inp.2.1.2.1
    let r := inp.2.2.1.1
    let Q := inp.2.2.1.2.1
    let R := inp.2.2.1.2.2.1
    let A₀ := inp.2.2.1.2.2.2
    let augScopes := withNeutralScopesList (eqs'.map equationVars) n'
    let edges := scopeIncidencesList n' augScopes
    let scheds := BalancedSchedules.constructBalancedSchedules
      n' augScopes.length (min n' Q) (min n' r) (b + w) edges
    let data := buildReplacementDesignData
      n' (min n' ((min n' r) ^ (2 * min n' Q))) (min n' Q) (min n' r)
      (min (n' + 1) A₀) (min n' R) augScopes scheds.1 scheds.2
    Q ≤ n' ∧ R ≤ n' ∧ r ≤ n' ∧ A₀ ≤ n' + 1 ∧ r ^ (2 * Q) ≤ n' ∧
      validDesignShape n' (min n' r) eqs'.length data = true ∧
      ∃ D : ReplacementDesign (listScopeFamily n' augScopes) Q r A₀ R (ReplacementParams.tauRat n'),
        data.Refines augScopes D ∧
        data.measurementMatrix.length = D.h * #(measurementIndices Q r A₀ R) ∧
        r * data.measurementMatrix.length ≤ n' := by
  have hf := feasible_of_checkBranchFeasible hfeas
  dsimp only [prepareBranchEvalInput] at hf
  obtain ⟨_, _, _, hF⟩ := hf
  dsimp only [prepareBranchEvalInput, ParameterCheck.computeScheduleParams]
  set b := branchMaxFactorIncidence n' eqs'
  set w := branchMaxFactorWidth n' eqs'
  set M' := branchAugmentedIncidence n' eqs'
  set β := ParameterCheck.chooseBeta (Nat.clog 2 n') b w
  set r := ReplacementParams.numGroups n'
  set Q := ReplacementParams.numNodes n'
  set R := ReplacementParams.rowBound β n'
  set A₀ := ReplacementParams.intervalStart β n'
  have h1n : 1 ≤ n' := hF.one_le_n
  have hr2 : 2 ≤ r := hF.two_le_numGroups
  have hr1 : 1 ≤ r := by omega
  have hR1 : 1 ≤ R := hF.one_le_rowBound
  have hRQ : R < Q := hF.rowBound_lt_numNodes
  have hQ1 : 1 ≤ Q := by omega
  have hvb : 2 * Q * r ^ 2 ≤ n' := hF.var_balance
  have hr_sq : 4 ≤ r ^ 2 := by nlinarith
  have hQn : Q ≤ n' := by nlinarith
  have hRn : R ≤ n' := by omega
  have hrn : r ≤ n' := by nlinarith
  have hI_top : A₀ + (R - 1) ≤ Q := hF.intervalStart_add_le_numNodes (by omega)
  have hA₀n : A₀ ≤ n' + 1 := by omega
  have haux : r ^ (2 * Q) ≤ n' := auxDim_le_of_twenty_le hF.twenty_le
  let augScopes := withNeutralScopesList (eqs'.map equationVars) n'
  have hsum_aug : (∑ f : Fin augScopes.length, #(listScopeFamily n' augScopes f)) = M' :=
    sum_card_listScopeFamily_augScopes n' eqs'
  have hb_aug :
      ∀ v : Fin n', #{f : Fin augScopes.length | v ∈ listScopeFamily n' augScopes f} ≤ b :=
    varIncidence_listScopeFamily_augScopes_le n' eqs'
  have hw_aug : ∀ f : Fin augScopes.length, #(listScopeFamily n' augScopes f) ≤ w :=
    card_listScopeFamily_augScopes_le n' eqs'
  have hb1 : 1 ≤ b := one_le_branchMaxFactorIncidence n' eqs'
  have hbw : 0 < b + w := by omega
  have hinc_aug : 2 * (b + w) * (r ^ (2 * Q)) ^ 2 ≤
      ∑ f : Fin augScopes.length, #(listScopeFamily n' augScopes f) := by
    rw [hsum_aug]
    exact hF.aux_balance
  have hM_le : (∑ f : Fin augScopes.length, #(listScopeFamily n' augScopes f)) ≤ b * n' := by
    rw [hsum_aug]
    exact branchAugmentedIncidence_le_mul n' eqs'
  have hI : ∀ a < R - 1, A₀ + a ≤ Q := fun a ha => hF.intervalStart_add_le_numNodes (by omega)
  have hτ : (0 : ℚ) ≤ ReplacementParams.tauRat n' := hF.tauRat_pos.le
  have htail : binomTailProb Q r A₀ R ≤ ReplacementParams.tauRat n' / ((r : ℚ) * (b : ℚ)) :=
    hF.binomTailProb_lt.le
  have hbal := balancedSchedule_construct_of_scopes augScopes h1n hr1 hQ1 hbw hb_aug hw_aug
    hinc_aug hvb
  let scheds := BalancedSchedules.constructBalancedSchedules
    n' augScopes.length Q r (b + w) (scopeIncidencesList n' augScopes)
  let D := constructedReplacementDesign augScopes scheds.1 scheds.2 hr1 hQ1 hb1 hτ hI hM_le
    htail hbal
  let data0 := buildReplacementDesignData n' (r ^ (2 * Q)) Q r A₀ R augScopes scheds.1 scheds.2
  have href : data0.Refines augScopes D :=
    buildReplacementDesignData_spec augScopes scheds.1 scheds.2 le_rfl hr1 hR1 hQ1 hb1 hτ hI
      htail hM_le hbal
  have hmeas_len : data0.measurementMatrix.length = D.h * #(measurementIndices Q r A₀ R) := by
    have hcopy : data0.copyCount = D.h := href.1
    dsimp only [data0, buildReplacementDesignData] at hcopy ⊢
    rw [CopyPlacement.length_pullbackMeasurementMatrix, hcopy,
      auxMeasurementRowsBounded_eq_auxMeasurementRows le_rfl,
      (isTableShape_auxMeasurementRows Q r A₀ R).1]
  have hrmeas_le : r * data0.measurementMatrix.length ≤ n' := by
    have hrat := D.total_measurement_rows_le
    have htau_half := hF.tauRat_le_half
    have hn_nonneg : (0 : ℚ) ≤ (n' : ℚ) := Nat.cast_nonneg n'
    have hrat_le : ((r * (D.h * #(measurementIndices Q r A₀ R)) : ℕ) : ℚ) ≤ (n' : ℚ) := by
      nlinarith
    rw [hmeas_len]
    exact_mod_cast hrat_le
  have hshape : validDesignShape n' r eqs'.length data0 = true := by
    unfold validDesignShape
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨?_, ?_⟩
    · have h0 : 0 ≤ eqs'.length * n' := Nat.zero_le _
      have hbound : n' ≤ 4 * (n' + 1) * (eqs'.length * n' + n' + 1) := by nlinarith
      exact hrmeas_le.trans hbound
    · intro gs hgs Vg hVg
      dsimp only [data0, buildReplacementDesignData] at hgs
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hgs
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hVg
      have hlen_vs : (normalizeVarSchedules n' Q r scheds.1).length = n' := by
        simp only [normalizeVarSchedules, List.length_map, List.length_range]
      have hlen_vg :
          (CopyPlacement.varGroupList (normalizeVarSchedules n' Q r scheds.1) t g).length ≤ n' := by
        unfold CopyPlacement.varGroupList
        exact List.length_filter_le _ _ |>.trans_eq (List.length_range.trans hlen_vs)
      omega
  refine ⟨hQn, hRn, hrn, hA₀n, haux, ?_, D, ?_, ?_, ?_⟩
  · simpa only [Nat.min_eq_right hQn, Nat.min_eq_right hRn, Nat.min_eq_right hrn,
      Nat.min_eq_right hA₀n, Nat.min_eq_right haux] using hshape
  · simpa only [Nat.min_eq_right hQn, Nat.min_eq_right hRn, Nat.min_eq_right hrn,
      Nat.min_eq_right hA₀n, Nat.min_eq_right haux] using href
  · simpa only [Nat.min_eq_right hQn, Nat.min_eq_right hRn, Nat.min_eq_right hrn,
      Nat.min_eq_right hA₀n, Nat.min_eq_right haux] using hmeas_len
  · simpa only [Nat.min_eq_right hQn, Nat.min_eq_right hRn, Nat.min_eq_right hrn,
      Nat.min_eq_right hA₀n, Nat.min_eq_right haux] using hrmeas_le

private theorem groupMeasurementMatrices_spec {n' D_cap Q r A₀ R : ℕ}
    (augScopes sv ss : List (List ℕ)) (hr : 1 ≤ r) (hD_cap : r ^ (2 * Q) ≤ D_cap)
    (t : Fin Q) (g : Fin r) :
    let data := buildReplacementDesignData n' D_cap Q r A₀ R augScopes sv ss
    let Vg := (data.varGroups.getD t.1 []).getD g.1 []
    let Ctg := (data.groupMeasurementMatrices.getD t.1 []).getD g.1 []
    (∀ w ∈ Vg, w < n') ∧ Ctg.length = data.measurementMatrix.length ∧
      ∀ row ∈ Ctg, row.length = Vg.length ∧ (row.map Int.natAbs).sum ≤ r ^ (2 * Q) := by
  intro data Vg Ctg
  let varScheds := normalizeVarSchedules n' Q r sv
  have hVg_eq : Vg = CopyPlacement.varGroupList varScheds t.1 g.1 := by
    dsimp only [Vg, data, buildReplacementDesignData, varScheds]
    rw [getD_map_range _ [] t.2, getD_map_range _ [] g.2]
  have hVg_lt : ∀ w ∈ Vg, w < n' := fun w hw => by
    rw [hVg_eq, CopyPlacement.mem_varGroupList] at hw
    simpa only [varScheds, length_normalizeVarSchedules] using hw.1
  have hVg_nodup : Vg.Nodup := by
    rw [hVg_eq]
    exact CopyPlacement.nodup_varGroupList varScheds t.1 g.1
  have hCtg_eq : Ctg = CopyPlacement.restrictGroupColumns Vg data.measurementMatrix := by
    dsimp only [Ctg, data, buildReplacementDesignData]
    rw [List.map_map, getD_map_range _ [] t.2, Function.comp_apply, List.map_map,
      getD_map_range _ [] g.2, Function.comp_apply, ← hVg_eq]
  refine ⟨hVg_lt, ?_, fun row hrow => ?_⟩
  · rw [hCtg_eq, CopyPlacement.restrictGroupColumns, List.length_map]
  · rw [hCtg_eq, CopyPlacement.restrictGroupColumns, List.mem_map] at hrow
    obtain ⟨fullRow, hfull, rfl⟩ := hrow
    refine ⟨List.length_map _,
      (CopyPlacement.sum_natAbs_restrictGroupRow_le hVg_nodup fullRow).trans ?_⟩
    dsimp only [data, buildReplacementDesignData] at hfull
    rw [CopyPlacement.pullbackMeasurementMatrix, List.mem_flatMap] at hfull
    obtain ⟨c, _, hfull_map⟩ := hfull
    obtain ⟨auxRow, haux, rfl⟩ := List.mem_map.mp hfull_map
    have haux_abs : ∀ z ∈ auxRow, |z| ≤ 1 := fun z hz =>
      abs_mem_auxMeasurementRowsBounded_le_one haux hz
    rw [auxMeasurementRowsBounded_eq_auxMeasurementRows hD_cap] at haux
    have haux_len : auxRow.length = r ^ (2 * Q) :=
      (isTableShape_auxMeasurementRows Q r A₀ R).2 auxRow haux
    let labels := incidenceLabelsList n' Q r augScopes sv ss
    have hpls_nodup : ((CopyPlacement.fiberRanks labels).zip labels).Nodup :=
      CopyPlacement.nodup_zip_fiberRanks labels
    have hpls_lt : ∀ p ∈ (CopyPlacement.fiberRanks labels).zip labels, p.2 < auxRow.length := by
      intro p hp
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hp
      have hl : idx < labels.length := by
        simpa only [List.length_zip, CopyPlacement.length_fiberRanks, Nat.min_self] using hidx
      let l := labels[idx]
      have hmem : l ∈ incidenceLabelsList n' Q r augScopes sv ss := List.getElem_mem hl
      rw [haux_len, List.getElem_zip]
      rw [incidenceLabelsList_eq_ofFn hr] at hmem
      obtain ⟨i, hi_eq⟩ := List.mem_ofFn.mp hmem
      change l < r ^ (2 * Q)
      rw [← hi_eq]
      exact encodeAuxLabel_lt _
    have haux_sum : ∀ xs : List ℤ, (∀ z ∈ xs, |z| ≤ 1) → (xs.map Int.natAbs).sum ≤ xs.length := by
      intro xs hxs
      induction xs with
      | nil => exact le_rfl
      | cons z zs ih =>
        have hz : z.natAbs ≤ 1 := Int.ofNat_le.mp (Int.natCast_natAbs z ▸ hxs z List.mem_cons_self)
        have hzs := ih fun w hw => hxs w (List.mem_cons_of_mem z hw)
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
    exact (CopyPlacement.sum_natAbs_pullbackMeasurementRow_le hpls_nodup hpls_lt c).trans
      ((haux_sum auxRow haux_abs).trans_eq haux_len)

end Stage1

/-! ### 4. Stage-2 Local Group Overrides, Measurement Fibers, and Jet Fold Equivalence -/

section Stage2Local

private theorem getD_applyGroupBits_mem {n' : ℕ} {Vg : List ℕ} (hnodup : Vg.Nodup)
    (hlt : ∀ w ∈ Vg, w < n') (ug base : List Bool) (j₀ : Fin Vg.length) :
    (applyGroupBits n' Vg ug base).getD Vg[j₀] false = ug.getD j₀.1 false := by
  have hv_lt : Vg[j₀] < n' := hlt Vg[j₀] (List.getElem_mem j₀.2)
  rw [applyGroupBits, getD_map_range _ false hv_lt]
  suffices ∀ k ≤ Vg.length,
      (List.range k).foldl (fun cur j => if Vg.getD j n' == Vg[j₀] then ug.getD j false else cur)
        (base.getD Vg[j₀] false) =
      if j₀.1 < k then ug.getD j₀.1 false else base.getD Vg[j₀] false by
    simpa only [j₀.2, ↓reduceIte] using this Vg.length le_rfl
  intro k hk
  induction k with
  | zero => simp only [List.range_zero, List.foldl_nil, Nat.not_lt_zero, ↓reduceIte]
  | succ k ih =>
    have hk_lt : k < Vg.length := by omega
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega),
      List.getD_eq_getElem Vg n' hk_lt]
    by_cases hkj : k = j₀.1
    · subst hkj
      simp only [Fin.getElem_fin, beq_self_eq_true, ↓reduceIte, Nat.lt_succ_self]
    · have hne : Vg[k] ≠ Vg[j₀] := fun heq =>
        hkj ((hnodup.getElem_inj_iff (hi := hk_lt) (hj := j₀.2)).mp heq)
      have hbeq : (Vg[k] == Vg[j₀]) = false := beq_false_of_ne hne
      have hiff : (j₀.1 < k + 1) ↔ (j₀.1 < k) := by omega
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, hiff]

private theorem getD_applyGroupBits_not_mem {n' v : ℕ} {Vg : List ℕ} (hv_lt : v < n')
    (hnot : v ∉ Vg) (ug base : List Bool) :
    (applyGroupBits n' Vg ug base).getD v false = base.getD v false := by
  rw [applyGroupBits, getD_map_range _ false hv_lt]
  suffices ∀ k ≤ Vg.length,
      (List.range k).foldl (fun cur j => if Vg.getD j n' == v then ug.getD j false else cur)
        (base.getD v false) = base.getD v false from this Vg.length le_rfl
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk_lt : k < Vg.length := by omega
    have hne : Vg[k] ≠ v := fun heq => hnot (heq ▸ List.getElem_mem hk_lt)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega),
      List.getD_eq_getElem Vg n' hk_lt, beq_false_of_ne hne]
    rfl

private noncomputable def groupIdxEquiv {n' r : ℕ} {vGroups_t : List (List ℕ)}
    {varAssign : Fin n' → Fin r}
    (hVG : ∀ g : Fin r, (vGroups_t.getD g.1 []).Nodup ∧ (∀ w ∈ vGroups_t.getD g.1 [], w < n') ∧
      ∀ v : Fin n', v.1 ∈ vGroups_t.getD g.1 [] ↔ varAssign v = g)
    (g : Fin r) :
    Fin (vGroups_t.getD g.1 []).length ≃ {v : Fin n' // varAssign v = g} :=
  Equiv.ofBijective
    (fun j => ⟨⟨(vGroups_t.getD g.1 [])[j], (hVG g).2.1 _ (List.getElem_mem j.2)⟩,
      ((hVG g).2.2 _).mp (List.getElem_mem j.2)⟩)
    ⟨fun j₁ j₂ heq => Fin.ext (((hVG g).1.getElem_inj_iff (hi := j₁.2) (hj := j₂.2)).mp
        (congrArg (fun x => x.1.1) heq)),
     fun ⟨v, hv⟩ => by
       obtain ⟨j, hj, hj_eq⟩ := List.getElem_of_mem (((hVG g).2.2 v).mpr hv)
       exact ⟨⟨j, hj⟩, Subtype.ext (Fin.ext hj_eq)⟩⟩

private theorem val_groupIdxEquiv {n' r : ℕ} {vGroups_t : List (List ℕ)}
    {varAssign : Fin n' → Fin r}
    (hVG : ∀ g : Fin r, (vGroups_t.getD g.1 []).Nodup ∧ (∀ w ∈ vGroups_t.getD g.1 [], w < n') ∧
      ∀ v : Fin n', v.1 ∈ vGroups_t.getD g.1 [] ↔ varAssign v = g)
    (g : Fin r) (j : Fin (vGroups_t.getD g.1 []).length) :
    ((groupIdxEquiv hVG g j).1 : ℕ) = (vGroups_t.getD g.1 [])[j] :=
  rfl

private noncomputable def localBitsEquiv {n' r : ℕ} {vGroups_t : List (List ℕ)}
    {varAssign : Fin n' → Fin r}
    (hVG : ∀ g : Fin r, (vGroups_t.getD g.1 []).Nodup ∧ (∀ w ∈ vGroups_t.getD g.1 [], w < n') ∧
      ∀ v : Fin n', v.1 ∈ vGroups_t.getD g.1 [] ↔ varAssign v = g) :
    (∀ g : Fin r, BitString (vGroups_t.getD g.1 []).length) ≃ (Fin n' → Bool) :=
  (Equiv.piCongrRight fun g => Equiv.arrowCongr (groupIdxEquiv hVG g) (Equiv.refl Bool)).trans
    (Cslib.ReplacementCounting.piGroupEquiv varAssign)

private theorem localBitsEquiv_apply {n' r : ℕ} {vGroups_t : List (List ℕ)}
    {varAssign : Fin n' → Fin r}
    (hVG : ∀ g : Fin r, (vGroups_t.getD g.1 []).Nodup ∧ (∀ w ∈ vGroups_t.getD g.1 [], w < n') ∧
      ∀ v : Fin n', v.1 ∈ vGroups_t.getD g.1 [] ↔ varAssign v = g)
    (u : ∀ g : Fin r, BitString (vGroups_t.getD g.1 []).length) (v : Fin n') :
    localBitsEquiv hVG u v =
      u (varAssign v) ((groupIdxEquiv hVG (varAssign v)).symm ⟨v, rfl⟩) :=
  Cslib.ReplacementCounting.piGroupEquiv_apply_of_eq varAssign _ rfl

private theorem getD_buildBaseAssignment {n' r : ℕ} {vGroups_t : List (List ℕ)}
    {varAssign : Fin n' → Fin r}
    (hVG : ∀ g : Fin r, (vGroups_t.getD g.1 []).Nodup ∧ (∀ w ∈ vGroups_t.getD g.1 [], w < n') ∧
      ∀ v : Fin n', v.1 ∈ vGroups_t.getD g.1 [] ↔ varAssign v = g)
    (rep : ∀ g : Fin r, BitString (vGroups_t.getD g.1 []).length) {reps : List (List Bool)}
    (hreps : ∀ g : Fin r, reps.getD g.1 [] = List.ofFn (rep g)) (v : Fin n') :
    (buildBaseAssignment n' r vGroups_t reps).getD v.1 false = localBitsEquiv hVG rep v := by
  let g₀ := varAssign v
  let j₀ := (groupIdxEquiv hVG g₀).symm ⟨v, rfl⟩
  have hj₀_val : (vGroups_t.getD g₀.1 [])[j₀] = v.1 := by
    have h := congrArg (fun x => (x.1 : ℕ)) ((groupIdxEquiv hVG g₀).apply_symm_apply ⟨v, rfl⟩)
    exact h
  rw [localBitsEquiv_apply hVG rep v, buildBaseAssignment]
  suffices ∀ k ≤ r,
      ((List.range k).foldl
        (fun acc g => applyGroupBits n' (vGroups_t.getD g []) (reps.getD g []) acc)
        (List.replicate n' false)).getD v.1 false =
      if g₀.1 < k then rep g₀ j₀ else false by
    simpa only [g₀.2, ↓reduceIte] using this r le_rfl
  intro k hk
  induction k with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, Nat.not_lt_zero, ↓reduceIte]
    rw [List.getD_eq_getElem _ false (by simp only [List.length_replicate]; exact v.2),
      List.getElem_replicate]
  | succ k ih =>
    have hk_lt : k < r := by omega
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hkg : k = g₀.1
    · subst hkg
      have hg_eq : (⟨g₀.1, hk_lt⟩ : Fin r) = g₀ := Fin.ext rfl
      rw [← hj₀_val, getD_applyGroupBits_mem (hVG g₀).1 (hVG g₀).2.1, hreps g₀]
      simp only [Nat.lt_succ_self, ↓reduceIte]
      rw [List.getD_eq_getElem _ false (by simp only [List.length_ofFn]; exact j₀.2),
        List.getElem_ofFn]
    · have hne : varAssign v ≠ ⟨k, hk_lt⟩ := fun heq => hkg (congrArg Fin.val heq).symm
      have hnot : v.1 ∉ vGroups_t.getD k [] := fun hm => hne (((hVG ⟨k, hk_lt⟩).2.2 v).mp hm)
      rw [getD_applyGroupBits_not_mem v.2 hnot, ih (by omega)]
      have hiff : (g₀.1 < k + 1) ↔ (g₀.1 < k) := by omega
      simp only [hiff]

private theorem getD_applyGroupBits_buildBaseAssignment {n' r : ℕ} {vGroups_t : List (List ℕ)}
    {varAssign : Fin n' → Fin r}
    (hVG : ∀ g : Fin r, (vGroups_t.getD g.1 []).Nodup ∧ (∀ w ∈ vGroups_t.getD g.1 [], w < n') ∧
      ∀ v : Fin n', v.1 ∈ vGroups_t.getD g.1 [] ↔ varAssign v = g)
    (rep : ∀ g : Fin r, BitString (vGroups_t.getD g.1 []).length) {reps : List (List Bool)}
    (hreps : ∀ g : Fin r, reps.getD g.1 [] = List.ofFn (rep g))
    (g : Fin r) (ug : BitString (vGroups_t.getD g.1 []).length) (v : Fin n') :
    (applyGroupBits n' (vGroups_t.getD g.1 []) (List.ofFn ug)
      (buildBaseAssignment n' r vGroups_t reps)).getD v.1 false =
      localBitsEquiv hVG (Function.update rep g ug) v := by
  rw [localBitsEquiv_apply hVG]
  by_cases hvg : varAssign v = g
  · subst hvg
    let j₀ := (groupIdxEquiv hVG (varAssign v)).symm ⟨v, rfl⟩
    have hj₀_val : (vGroups_t.getD (varAssign v).1 [])[j₀] = v.1 :=
      congrArg (fun x => (x.1 : ℕ)) ((groupIdxEquiv hVG (varAssign v)).apply_symm_apply ⟨v, rfl⟩)
    rw [← hj₀_val, getD_applyGroupBits_mem (hVG _).1 (hVG _).2.1, Function.update_self,
      List.getD_eq_getElem _ false (by simp only [List.length_ofFn]; exact j₀.2), List.getElem_ofFn]
  · have hnot : v.1 ∉ vGroups_t.getD g.1 [] := fun hm => hvg (((hVG g).2.2 v).mp hm)
    rw [getD_applyGroupBits_not_mem v.2 hnot, getD_buildBaseAssignment hVG rep hreps v,
      localBitsEquiv_apply hVG, Function.update_of_ne hvg]

private theorem checkRestrictedGroup_ofFn_iff {n' : ℕ} (indE : List Bool) {Vg : List ℕ}
    (hlt : ∀ w ∈ Vg, w < n') (ug : BitString Vg.length) :
    checkRestrictedGroup n' indE Vg (List.ofFn ug) = true ↔
      ∀ j : Fin Vg.length,
        (⟨Vg[j], hlt _ (List.getElem_mem j.2)⟩ : Fin n') ∈ supportOfList n' indE →
          ug j = true := by
  simp only [checkRestrictedGroup, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', mem_supportOfList]
  refine ⟨fun h j hj => ?_, fun h j hj => ?_⟩
  · rcases h j.1 j.2 with hfalse | htrue
    · rw [List.getD_eq_getElem Vg n' j.2, ← Fin.getElem_fin, hj] at hfalse
      cases hfalse
    · rwa [List.getD_eq_getElem (List.ofFn ug) false (by simp only [List.length_ofFn]; exact j.2),
        List.getElem_ofFn] at htrue
  · rw [List.getD_eq_getElem Vg n' hj,
      List.getD_eq_getElem (List.ofFn ug) false (by simp only [List.length_ofFn]; exact hj),
      List.getElem_ofFn]
    by_cases he : indE.getD Vg[j] false = true
    · exact Or.inr (h ⟨j, hj⟩ he)
    · exact Or.inl (Bool.eq_false_iff.mpr he)

end Stage2Local

end Cslib.Complexity.SubexponentialSAT.SparsePolyCounter
