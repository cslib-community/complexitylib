/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.Correctness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Tactic.PolyTime
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Binary incidence input for source weighted set cover

A dense incidence matrix and binary rational weights/dual prices are an external
encoding of the finite source WSC instance in [Wang2027], Section 3 and Theorem 4,
PDF pp. 4, 10–11. The converter computes the internal unary element lists. It
preserves original candidate positions and ground labels, including empty rows,
and ignores excess mask bits as the finite source universe requires.

This is a concrete binary incidence format, not a claim about every possible
external serializer or about noncomputable real-valued algorithmic input.

## Main definitions

* `Input`, `encoding`: original incidence bits and binary rational data.
* `toNative`: computed internal WSC representation, with no supplied proposals.

## Main results

* `computable_toNative`: one native polynomial converter for all input sizes.
* `elements_toNative`: the original incidence relation is preserved exactly.
* `valid_toNative`: external finite WSC promises imply native dual validity.
-/

public section
namespace Cslib.Probability.StochasticOracle.NativeRetention.SourceEncoding
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Source incidence matrix, weights and supplied feasible dual data.
The dual length declares the universe size; row positions are original set labels. -/
structure Input where
  /-- Each original candidate's element membership bits. -/
  incidence : List (List Bool)
  /-- Binary rational original candidate weights. -/
  weights : List ℚ
  /-- Binary rational element dual prices, declaring the finite universe. -/
  dual : List ℚ
  /-- Binary rational local certification factor. -/
  rho : ℚ
  deriving DecidableEq

/-- Framed incidence bit strings, then framed binary rational weights, dual and factor. -/
enc_structure encoding : Input where incidence : (encList encBits),
  weights : (encList encRatBin), dual : (encList encRatBin), rho : encRatBin

/-- Convert each source row by scanning exactly the original finite universe. -/
@[expose] def row (n : ℕ) (mask : List Bool) : List ℕ :=
  (List.range n).filter fun e => mask[e]?.getD false

/-- Original WSC data translated to unary incidence labels, before any response. -/
@[expose] def toNative (x : Input) : NativeRetention.Input :=
  ⟨x.incidence.map (row x.dual.length), x.weights, x.dual, x.rho, []⟩

private theorem fields : ComputableInPolyTime
    (fun x : Input => (x.incidence, x.weights, x.dual, x.rho)) encoding
    (encPair (encList encBits)
      (encPair (encList encRatBin) (encPair (encList encRatBin) encRatBin))) :=
  .of_eq fun _ => rfl

private theorem row_computable : ComputableInPolyTime
    (fun p : ℕ × List Bool => row p.1 p.2) (encPair encUnary encBits)
    (encList encUnary) := by
  unfold row
  apply filterWithInput (by fun_prop)
  simpa only [List.getD_eq_getElem?_getD] using
    (bitsGetDWithInput (by fun_prop) (by fun_prop) false)

/-- Native conversion is polynomial in the actual external bit encoding.
In particular, unary output indices are bounded by the input dual-vector length. -/
theorem computable_toNative : ComputableInPolyTime toNative encoding encInput := by
  have hi := fields.fst'
  have hw := fields.snd'.fst'
  have hd := fields.snd'.snd'.fst'
  have hr := fields.snd'.snd'.snd'
  have hn := (length_list encRatBin).comp hd
  have hrows : ComputableInPolyTime (fun x : Input => x.incidence.map (row x.dual.length))
      encoding (encList (encList encUnary)) := by
    apply mapWithInput hi
    exact row_computable.comp
      ((hn.comp (ComputableInPolyTime.fst encoding encBits)).prod
        (ComputableInPolyTime.snd encoding encBits))
  have hnil : ComputableInPolyTime (fun _ : Input => ([] : List (List ℕ)))
      encoding (encList (encList encUnary)) := .const []
  have hrest := hw.prod (hd.prod (hr.prod hnil))
  exact (hrows.prod hrest).of_enc_eq fun _ => rfl

/-- Original candidate and element indices survive the conversion exactly. -/
theorem elements_toNative (x : Input) (j e : ℕ) :
    e ∈ elements (toNative x) j ↔
      e < x.dual.length ∧ ((x.incidence.getD j [])[e]?.getD false = true) := by
  cases h : x.incidence[j]? <;>
    simp [elements, ground, toNative, row, List.getD_eq_getElem?_getD,
      List.getElem?_map, h]

/-- Conversion preserves every source candidate position, even an empty row. -/
theorem rows_length (x : Input) : (toNative x).rows.length = x.incidence.length :=
  List.length_map _

/-- Source incidence relation on the original finite universe. -/
@[expose] def sourceSet (x : Input) (j : ℕ) : Finset ℕ :=
  (Finset.range x.dual.length).filter fun e => (x.incidence.getD j [])[e]?.getD false

/-- Native incidence lists represent exactly the external source set. -/
theorem elements_eq (x : Input) (j : ℕ) : elements (toNative x) j = sourceSet x j := by
  ext e
  rw [elements_toNative]
  simp [sourceSet]

/-- Standard finite rational WSC promises, stated on the external incidence data. -/
structure Valid (x : Input) : Prop where
  /-- Each original candidate has its original weight. -/
  weights_length : x.weights.length = x.incidence.length
  /-- Nonnegative weights on the original candidates. -/
  weight_nonneg : ∀ j < x.incidence.length, 0 ≤ x.weights.getD j 0
  /-- Nonnegative prices on the source universe. -/
  dual_nonneg : ∀ e < x.dual.length, 0 ≤ x.dual.getD e 0
  /-- Dual feasibility for every original candidate. -/
  feasible : ∀ j < x.incidence.length,
    ∑ e ∈ sourceSet x j, x.dual.getD e 0 ≤ x.weights.getD j 0

/-- Source promises imply native validity; no internal-parser or native-validity
certificate is supplied to the conversion theorem. -/
theorem valid_toNative (x : Input) (hx : Valid x) : NativeRetention.Valid (toNative x) := by
  constructor
  · intro j
    change 0 ≤ x.weights.getD j 0
    by_cases hj : j < x.incidence.length
    · exact hx.weight_nonneg j hj
    · rw [List.getD_eq_default _ _ (by rw [hx.weights_length]; omega)]
  · intro e
    change 0 ≤ x.dual.getD e 0
    by_cases he : e < x.dual.length
    · exact hx.dual_nonneg e he
    · rw [List.getD_eq_default _ _ (by omega)]
  · intro j
    rw [elements_eq]
    change (∑ e ∈ sourceSet x j, x.dual.getD e 0) ≤ x.weights.getD j 0
    by_cases hj : j < x.incidence.length
    · exact hx.feasible j hj
    · have he : x.weights.length ≤ j := by rw [hx.weights_length]; omega
      have hs : sourceSet x j = ∅ := by
        unfold sourceSet
        rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hj)]
        simp
      rw [hs, List.getD_eq_default _ _ he]
      simp

end Cslib.Probability.StochasticOracle.NativeRetention.SourceEncoding
