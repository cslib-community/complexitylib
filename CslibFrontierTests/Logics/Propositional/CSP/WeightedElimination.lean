/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests for candidate weighted CSP variable elimination)

import CslibFrontier.Logics.Propositional.CSP
import CslibFrontier.Logics.Propositional.CSP.PartitionFunction.Properties
import CslibFrontier.Logics.Propositional.CSP.FactorTable
import CslibFrontier.Algorithms.Lean.CSP.VariableElimination
import CslibFrontier.Algorithms.Lean.CSP.WeightCost
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Weighted CSP Partition Function and Variable Elimination Tests

Kernel-checked examples exercising:
1. Partition function vs. `modelCountOn`, relabeling, isolated variables, and separator
   conditioning (`Cslib.Logic.PL.CSP`).
2. `FactorTable` evaluation, repeated scopes, empty scopes, and bridges to
   `ExplicitTensorNetwork` and `DescribedNetwork`.
3. Elimination-order sensitivity on a 6-variable Boolean star (`[0, 1, 2, 3, 4, 5]` vs.
   `[1, 2, 3, 4, 5, 0]`), comparing exact values and `TimeM` / `peakLiveEntries` /
   `maxOutScopeLen` / `maxJointScopeLen` / `totalArithOps` resource costs.
4. Exact signed `ℤ`, modular `ZMod 5`, and cleared-denominator `ℚ` elimination with `enc_structure`
   codec injectivity and bit-length bounds.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.WeightedElimination

open Cslib.Logic.PL
open Cslib.Logic.PL.CSP
open Cslib.Circuits.Frontier
open Cslib.Algorithms.Lean.CSP
open Turing
open Turing.MultiTapeTM

section PartitionAndSeparator

private def booleRel (r : Bool) : List Bool → Bool
  | [a, b] => if r then a || b else (!a) || b
  | _ => false

private def orWt (r : Bool) (xs : List Bool) : ℕ :=
  if booleRel r xs then 1 else 0

private def satCSP : CSP Bool ℕ := [(true, [0, 1]), (false, [0, 1])]

private theorem satCSP_vars : satCSP.vars.toFinset = {0, 1} := by
  decide

theorem partitionFunctionOn_satCSP_isolated :
    CSP.partitionFunctionOn (R := ℕ) orWt satCSP ({0, 1, 2} : Finset ℕ) = 4 ∧
    CSP.modelCountOn booleRel satCSP ({0, 1, 2} : Finset ℕ) = 4 := by
  have hsub : satCSP.vars.toFinset ⊆ ({0, 1, 2} : Finset ℕ) := by
    rw [satCSP_vars]
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
    rcases hv with rfl | rfl <;> simp
  have hboole :=
    CSP.partitionFunctionOn_boole booleRel satCSP ({0, 1, 2} : Finset ℕ)
  change CSP.partitionFunctionOn (R := ℕ) orWt satCSP ({0, 1, 2} : Finset ℕ) =
      CSP.modelCountOn booleRel satCSP ({0, 1, 2} : Finset ℕ) at hboole
  have hcard :=
    CSP.partitionFunctionOn_eq_card_pow_mul_partitionFunction (D := Bool) orWt hsub
  have hsdiff : ({0, 1, 2} : Finset ℕ) \ satCSP.vars.toFinset = {2} := by
    rw [satCSP_vars]
    decide
  rw [hsdiff, Finset.card_singleton, Fintype.card_bool, pow_one] at hcard
  have hpart : satCSP.partitionFunction orWt = 2 := by
    have h1 := result_eliminateOrderM_ofCSP 2 finTwoEquiv.symm orWt
      (F := satCSP) (declared := [0, 1]) (order := [0, 1]) (by simp [satCSP_vars])
      Finset.Subset.rfl
    have hvars : ([0, 1] : List ℕ).toFinset = satCSP.vars.toFinset := by
      rw [satCSP_vars]
      decide
    rw [CSP.partitionFunction_eq_partitionFunctionOn, ← hvars, ← h1]
    decide
  have hval : CSP.partitionFunctionOn (R := ℕ) orWt satCSP ({0, 1, 2} : Finset ℕ) = 4 := by
    rw [hcard, hpart]
    simp
  exact ⟨hval, hboole.symm.trans hval⟩

theorem partitionFunction_satCSP_relabel :
    (satCSP.relabel (fun v : ℕ => v + 10)).partitionFunction orWt =
      satCSP.partitionFunction orWt := by
  let e : ℕ ≃ ℕ := (Equiv.swap 0 10).trans (Equiv.swap 1 11)
  have he0 : e 0 = 10 := by decide
  have he1 : e 1 = 11 := by decide
  have hcongr : satCSP.relabel (fun v : ℕ => v + 10) = satCSP.relabel e := by
    simp only [satCSP, CSP.relabel, Constraint.relabel, List.map_cons, List.map_nil, he0, he1]
  rw [hcongr]
  exact CSP.partitionFunction_relabel_equiv orWt e satCSP

private def chainWt (_ : Unit) : List Bool → ℕ
  | [false, false] => 2
  | [false, true] => 1
  | [true, false] => 3
  | [true, true] => 5
  | _ => 0

private def sepF1 : CSP Unit ℕ := [((), [0, 1])]
private def sepF2 : CSP Unit ℕ := [((), [1, 2])]

theorem separator_chain_factorization :
    (CSP.partitionFunction chainWt (sepF1 ++ sepF2) =
      ∑ α : ({1} : Finset ℕ) → Bool,
        let ext : ℕ → Bool := fun v => if h : v ∈ ({1} : Finset ℕ) then α ⟨v, h⟩ else default
        (CSP.restrictOn {1} ext sepF1).partitionFunction (CSP.pinnedWeight chainWt) *
          (CSP.restrictOn {1} ext sepF2).partitionFunction (CSP.pinnedWeight chainWt)) ∧
    CSP.partitionFunction chainWt (sepF1 ++ sepF2) = 63 := by
  constructor
  · exact CSP.partitionFunction_separator chainWt (by decide) (by decide)
  · have hvars : ([0, 1, 2] : List ℕ).toFinset = (sepF1 ++ sepF2).vars.toFinset := by
      decide
    have h1 := result_eliminateOrderM_ofCSP 2 finTwoEquiv.symm chainWt
      (F := sepF1 ++ sepF2) (declared := [0, 1, 2]) (order := [0, 1, 2]) (by rw [hvars])
      Finset.Subset.rfl
    rw [CSP.partitionFunction_eq_partitionFunctionOn, ← hvars, ← h1]
    decide

end PartitionAndSeparator

section FactorTablesAndNetworks

example : Nat.ofDigits 3 [2, 1, 0] = 5 := by decide
example : lsbDecode 3 3 5 = [2, 1, 0] := by decide
example : Nat.ofDigits 2 ([true, false, true].map Bool.toNat) =
    Cslib.BitString.lsbValue [true, false, true] :=
  ofDigits_two_eq_lsbValue _

private def edgeTableFactors : List (FactorTable ℕ ℕ) :=
  [ { scope := [], entries := #[3] },
    { scope := [0, 0], entries := #[2, 99, 99, 5] },
    { scope := [0, 1], entries := #[1, 4, 2, 7] } ]

theorem contraction_edgeTableFactors_exact :
    FactorTable.contractionOn 2 edgeTableFactors ({0, 1, 2} : Finset ℕ) = 366 := by
  have h2 := result_eliminateOrder_of_subset (R := ℕ) 2
    (s := ElimState.ofFactors edgeTableFactors [0, 1, 2]) (order := [0, 1, 2]) (by decide)
  have hdec : ([0, 1, 2] : List ℕ).toFinset = ({0, 1, 2} : Finset ℕ) := by decide
  simp only [ElimState.eval, ElimState.ofFactors, one_mul] at h2
  rw [hdec] at h2
  rw [← h2, ← ret_eliminateOrderM]
  decide

private def sampleExpNet : ExplicitTensorNetwork ℕ :=
  { numEdges := 2
    vertices := [([0, 0], [2, 99, 99, 5]), ([0, 1], [1, 4, 2, 7])] }

theorem contraction_sampleExpNet_exact :
    sampleExpNet.contraction = 61 := by
  rw [← FactorTable.contractionOn_ofExplicitTensorNetwork]
  have h2 := result_eliminateOrder_of_subset (R := ℕ) 2
    (s := ElimState.ofFactors (FactorTable.ofExplicitTensorNetwork sampleExpNet) [0, 1])
    (order := [0, 1]) (by decide)
  have hdec : ([0, 1] : List ℕ).toFinset = Finset.range sampleExpNet.numEdges := by
    decide
  simp only [ElimState.eval, ElimState.ofFactors, one_mul] at h2
  rw [hdec] at h2
  rw [← h2, ← ret_eliminateOrderM]
  decide

private def sampleDescNet : DescribedNetwork (List ℕ) :=
  { numEdges := 2
    vertices := [([0, 1], [1, 4, 2, 7]), ([1], [3, 5])] }

private def tblEval (tbl : List ℕ) (bs : List Bool) : ℕ :=
  tbl.getD (Cslib.BitString.lsbValue bs) 0

theorem contraction_sampleDescNet_exact :
    DescribedNetwork.contraction tblEval sampleDescNet = 60 := by
  have heval : ∀ v ∈ sampleDescNet.vertices, ∀ bs : List Bool, bs.length = v.1.length →
      tblEval v.2 bs = (Array.ofFn fun i : Fin (2 ^ v.1.length) =>
        tblEval v.2 ((lsbDecode 2 v.1.length i.1).map fun k => decide (k ≠ 0))).getD
          (Cslib.BitString.lsbValue bs) 0 := by
    intro v hv bs hlen
    simp only [sampleDescNet, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
      cases b0 <;> cases b1 <;> decide
    · rcases bs with _ | ⟨b0, _ | ⟨_, _⟩⟩ <;> simp at hlen
      cases b0 <;> decide
  rw [← FactorTable.contractionOn_ofDescribedNetwork tblEval sampleDescNet heval]
  let fs : List (FactorTable ℕ ℕ) := sampleDescNet.vertices.map fun v =>
    { scope := v.1
      entries := Array.ofFn fun i : Fin (2 ^ v.1.length) =>
        tblEval v.2 ((lsbDecode 2 v.1.length i.1).map fun k => decide (k ≠ 0)) }
  have h2 := result_eliminateOrder_of_subset (R := ℕ) 2
    (s := ElimState.ofFactors fs [0, 1]) (order := [0, 1]) (by decide)
  have hdec : ([0, 1] : List ℕ).toFinset = Finset.range sampleDescNet.numEdges := by
    decide
  simp only [ElimState.eval, ElimState.ofFactors, one_mul] at h2
  rw [hdec] at h2
  change FactorTable.contractionOn 2 fs (Finset.range sampleDescNet.numEdges) = 60
  rw [← h2, ← ret_eliminateOrderM]
  decide

example :
    (FactorTable.relabel (fun n => n + 5)
      ({ scope := [0, 1], entries := #[1, 2, 3, 4] } : FactorTable ℕ ℕ)).scope = [5, 6] := by
  simp only [FactorTable.relabel_scope, List.map_cons, List.map_nil]

end FactorTablesAndNetworks

section OrderSensitivity

private def starFactors : List (FactorTable ℕ ℕ) :=
  [ { scope := [0, 1], entries := #[1, 2, 3, 4] },
    { scope := [0, 2], entries := #[1, 3, 2, 5] },
    { scope := [0, 3], entries := #[2, 1, 4, 3] },
    { scope := [0, 4], entries := #[1, 1, 2, 1] },
    { scope := [0, 5], entries := #[2, 1, 1, 2] } ]

private def starInit : ElimState ℕ ℕ :=
  ElimState.ofFactors starFactors [0, 1, 2, 3, 4, 5]

private def hubFirst : List ℕ := [0, 1, 2, 3, 4, 5]
private def leavesFirst : List ℕ := [1, 2, 3, 4, 5, 0]

theorem star_both_orders_equal_value :
    (eliminateOrderM 2 hubFirst starInit).ret.result =
      (eliminateOrderM 2 leavesFirst starInit).ret.result ∧
    (eliminateOrderM 2 leavesFirst starInit).ret.result = 1800 := by
  constructor <;> decide

theorem star_hubFirst_vs_leavesFirst_cost_gap :
    maxOutScopeLen 2 leavesFirst starInit < maxOutScopeLen 2 hubFirst starInit ∧
    maxJointScopeLen 2 leavesFirst starInit < maxJointScopeLen 2 hubFirst starInit ∧
    peakLiveEntries 2 leavesFirst starInit < peakLiveEntries 2 hubFirst starInit ∧
    totalArithOps 2 leavesFirst starInit < totalArithOps 2 hubFirst starInit ∧
    (eliminateOrderM 2 leavesFirst starInit).time <
      (eliminateOrderM 2 hubFirst starInit).time := by
  decide

theorem star_leavesFirst_bounds :
    totalArithOps 2 leavesFirst starInit ≤
      leavesFirst.length +
        (starInit.live.length + 2 * leavesFirst.length) *
          2 ^ maxJointScopeLen 2 leavesFirst starInit ∧
    peakLiveEntries 2 leavesFirst starInit ≤
      starInit.live.length *
        max (maxTableEntries starInit.live) (2 ^ maxOutScopeLen 2 leavesFirst starInit) ∧
    (eliminateOrderM 2 leavesFirst starInit).time ≤
      leavesFirst.length * (starInit.live.length + 1) +
        2 ^ maxJointScopeLen 2 leavesFirst starInit *
          ((maxJointScopeLen 2 leavesFirst starInit + 1) * leavesFirst.length +
            (starInit.live.length + leavesFirst.length) *
              (max (maxScopeLen starInit.live) (maxJointScopeLen 2 leavesFirst starInit) + 1)) :=
  ⟨totalArithOps_le_of_intermediate (by decide) leavesFirst starInit,
   peakLiveEntries_le (by decide) leavesFirst starInit,
   time_eliminateOrderM_le (by decide) leavesFirst starInit⟩

end OrderSensitivity

section WeightCostsAndEncodings

private def intFactors : List (FactorTable ℤ ℕ) :=
  [ { scope := [0, 1], entries := #[-2, 1, 3, -4] },
    { scope := [1, 2], entries := #[2, -1, 0, 3] } ]

theorem int_elimination_exact_and_bounded :
    (eliminateOrderM 2 [0, 1, 2] (ElimState.ofFactors intFactors [0, 1, 2])).ret.result = -4 ∧
    (eliminateOrder 2 [0, 1, 2] (ElimState.ofFactors intFactors [0, 1, 2])).result.natAbs ≤
      2 ^ 3 * 4 ^ 2 := by
  constructor
  · decide
  · exact natAbs_result_eliminateOrder_le (by decide) (by decide) intFactors [0, 1, 2] [0, 1, 2]
      (by decide)

private def modFactors : List (FactorTable (ZMod 5) ℕ) :=
  [ { scope := [0, 1], entries := #[2, 4, 3, 1] },
    { scope := [1], entries := #[4, 2] } ]

theorem mod5_elimination_exact_and_bounded :
    (eliminateOrderM 2 [0, 1] (ElimState.ofFactors modFactors [0, 1])).ret.result = (2 : ZMod 5) ∧
    0 < liveFieldBits 5
      (eliminateOrder 2 (([0, 1] : List ℕ).take 1) (ElimState.ofFactors modFactors [0, 1])).live ∧
    ∀ k : ℕ,
      liveFieldBits 5 (eliminateOrder 2 (([0, 1] : List ℕ).take k)
          (ElimState.ofFactors modFactors [0, 1])).live ≤
        peakLiveEntries 2 [0, 1] (ElimState.ofFactors modFactors [0, 1]) * (5 : ℕ).size ∧
      liveFieldBits 5 (eliminateOrder 2 (([0, 1] : List ℕ).take k)
          (ElimState.ofFactors modFactors [0, 1])).live ≤
        modFactors.length *
          max (maxTableEntries modFactors)
            (2 ^ maxOutScopeLen 2 [0, 1] (ElimState.ofFactors modFactors [0, 1])) *
          (5 : ℕ).size := by
  refine ⟨by decide, by decide, fun k =>
    ⟨liveFieldBits_eliminateOrder_take_le_peak 2 [0, 1] (ElimState.ofFactors modFactors [0, 1]) k,
     liveFieldBits_eliminateOrder_le (by decide) [0, 1]
       (ElimState.ofFactors modFactors [0, 1]) k⟩⟩

private def ratDenoms : List ℕ := [2, 3]

private def ratIntFactors : List (FactorTable ℤ ℕ) :=
  [ { scope := [0, 1], entries := #[1, -3, 2, 5] },
    { scope := [1], entries := #[1, 4] } ]

private def ratScaledFactors : List (FactorTable ℚ ℕ) :=
  List.zipWith (fun (q : ℕ) f =>
    scaleFactor ((q : ℚ)⁻¹) (mapFactorHom (Int.castRingHom ℚ) f)) ratDenoms ratIntFactors

theorem rat_cleared_elimination_exact_and_bounded :
    (eliminateOrder 2 [0, 1] (ElimState.ofFactors ratScaledFactors [0, 1])).result = (13 : ℚ) / 3 ∧
    (encRat (eliminateOrder 2 [0, 1]
      (ElimState.ofFactors ratScaledFactors [0, 1])).result).length ≤
      2 * (([0, 1] : List ℕ).length * (2 : ℕ).size +
        ratIntFactors.length * (5 : ℕ).size) +
        ratIntFactors.length * (3 : ℕ).size + 8 := by
  have hscaled := result_eliminateOrder_ratScaled (V := ℕ) 2 ratDenoms ratIntFactors [0, 1]
    [0, 1] rfl Finset.Subset.rfl
  change (eliminateOrder 2 [0, 1] (ElimState.ofFactors ratScaledFactors [0, 1])).result =
    ((eliminateOrder 2 [0, 1] (ElimState.ofFactors ratIntFactors [0, 1])).result : ℚ) /
      ((ratDenoms.prod : ℕ) : ℚ) at hscaled
  have hz : (eliminateOrder 2 [0, 1] (ElimState.ofFactors ratIntFactors [0, 1])).result = 26 := by
    rw [← ret_eliminateOrderM]
    decide
  rw [hz] at hscaled
  constructor
  · rw [hscaled]
    simp only [ratDenoms, List.prod_cons, List.prod_nil, mul_one, Int.cast_ofNat, Nat.cast_mul,
      Nat.cast_ofNat]
    ring
  · exact length_encRat_cleared_result_le (by decide) (by decide)
      ratDenoms ratIntFactors [0, 1] [0, 1] rfl (by decide) (by decide) (by decide)
      Finset.Subset.rfl

private def sampleNatRec : NatFactorRecord := ⟨[0, 1], [1, 4, 2, 7]⟩
private def sampleNatRec' : NatFactorRecord := ⟨[0, 1], [1, 4, 2, 8]⟩
private def sampleIntRec : IntFactorRecord := ⟨[0, 1], [-2, 1, 3, -4]⟩
private def sampleRatRec : RatFactorRecord := ⟨[0], [mkRat 1 2, mkRat (-3) 4]⟩
private def sampleModRec : ModFactorRecord := ⟨5, [1], [4, 2]⟩

example : encNatFactorRecord sampleNatRec ≠ encNatFactorRecord sampleNatRec' := by
  intro h
  have := encNatFactorRecord.injective h
  cases this

example : (encIntFactorRecord sampleIntRec).length ≤
    2 * (sampleIntRec.scope.length * (2 * 1 + 1)) + 1 +
      sampleIntRec.entries.length * (2 * 4 + 1) :=
  length_encIntFactorRecord_le sampleIntRec (by decide) (by decide)

example : ∀ f ∈ (eliminateOrder 2 [0] (ElimState.ofFactors intFactors [0, 1, 2])).live,
    ∀ z ∈ f.entries.toList,
      (encIntBin z).length ≤ ([0] : List ℕ).length * (2 : ℕ).size +
        intFactors.length * (4 : ℕ).size + 3 :=
  fun _ hf _ hz => length_encIntBin_entry_eliminateOrder_le (by decide) (by decide)
    intFactors [0, 1, 2] [0] (by decide) hf hz

example : (Cslib.TreeEval.Ary.Iter.encField 5 (4 : ZMod 5)).length ≤ (5 : ℕ).size :=
  Cslib.TreeEval.Ary.Iter.length_encField_le 5 (4 : ZMod 5)

example : (encRatFactorRecord sampleRatRec).length ≤
    2 * (sampleRatRec.scope.length * (2 * 1 + 1)) + 1 +
      sampleRatRec.entries.length * (2 * 13 + 1) :=
  length_encRatFactorRecord_le sampleRatRec (by decide) fun q hq => by
    simp only [sampleRatRec, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact le_trans (length_encRat_le (mkRat 1 2) (A := 1) (B := 2) (by decide) (by decide))
        (by decide)
    · exact le_trans (length_encRat_le (mkRat (-3) 4) (A := 3) (B := 4) (by decide) (by decide))
        (by decide)

example : (encModFactorRecord sampleModRec).length ≤
    2 * sampleModRec.modulus.size + 1 + 2 * (sampleModRec.scope.length * (2 * 1 + 1)) + 1 +
      sampleModRec.entries.length * (2 * sampleModRec.modulus.size + 1) :=
  length_encModFactorRecord_le sampleModRec (by decide) (by decide)

example : sampleIntRec.toFactorTable ∈ intFactors := by
  simp [intFactors, IntFactorRecord.toFactorTable, sampleIntRec]

end WeightCostsAndEncodings

end CslibFrontierTests.WeightedElimination
