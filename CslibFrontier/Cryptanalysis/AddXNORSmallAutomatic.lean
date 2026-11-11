/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORSmallDP
-- Read the existing original-input encoding and parameterized DP constructor during composition.
import all CslibFrontier.Cryptanalysis.AddXNORSmallDP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Mathlib.Data.List.Fold

/-!
# Small-operand decision with no supplied magnitude parameter

Compute the maximum binary length of the operands after the seed, and install
that derived unary parameter before the actual narrow DP. This completes the
original-input algorithm of [WangLvShenZhang2027], Proposition 4 (PDF pp. 20–21):
the unrestricted seed does not contribute to the computed magnitude bound.

## Main results

* `original_correct`: exact decision on every original typed instance, without a bound premise.
* `source_parameter_bounds`: time and every-prefix workspace $2^s P(m+q+1)$ when operands fit `s`.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.SmallAutomatic
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Maximum physical binary operand length, computed from the original tape, excluding the seed. -/
def computedBound (input : SortedQuarterMachine.Input) : ℕ :=
  let (_, operands) := input
  streamRecordLength encNat operands

/-- Supply only the magnitude parameter computed by the machine itself. -/
def prepare (input : SortedQuarterMachine.Input) : SmallDP.Input := (computedBound input, input)

/-- Original-input small-operand decision, with no magnitude advice. -/
def run (input : SortedQuarterMachine.Input) : Bool := SmallDP.run (prepare input)

private theorem fold_width (rows : List ℕ) :
    rows.foldl (fun n a => max n a.size) 0 = streamRecordLength encNat rows := by
  rw [show (fun n a : ℕ => max n a.size) = (fun n a => max n ((encNat a).length)) from
    funext fun n => funext fun a => by simp [encNat_apply, Nat.size_eq_bits_len]]
  rw [← List.foldl_map, List.foldl_eq_foldr]
  rfl

private theorem width_polyTime : ComputableInPolyTime (streamRecordLength encNat)
    (encList encNat) encUnary := by
  have body : ComputableTidilyInPolyTime
      (fun q : (Bool × ℕ) × ℕ => max q.1.2 q.2.size)
      (encPair (encPair encBool encUnary) encNat) encUnary := by
    have size : ComputableTidilyInPolyTime
        (fun q : (Bool × ℕ) × ℕ => q.2.size)
        (encPair (encPair encBool encUnary) encNat) encUnary :=
      (ComputableInPolyTime.binary_size.comp (by fun_prop)).tidy
    have previous : ComputableTidilyInPolyTime
        (fun q : (Bool × ℕ) × ℕ => q.1.2)
        (encPair (encPair encBool encUnary) encNat) encUnary := by fun_prop
    exact ComputableTidilyInPolyTime.unary_max.comp (previous.prod size)
  have h := ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (encA := encNat) (encL := encList encNat) (encB := encUnary) (encP := encBool)
    (step := fun _ n a => max n a.size) (.const false) .id' (.const 0) body
    (growth := fun rows : List ℕ => (encList encNat rows).length) .self
    (fun rows n a member => by
      have value := SizedListEncoding.length_elem_le (encA := encNat)
        (encL := encList encNat) rows a member
      simp only [encUnary_apply, List.length_replicate]
      simp only [encNat_apply, Nat.size_eq_bits_len] at value
      omega)
  simpa only [fold_width] using h.computableInPolyTime

private theorem prepare_polyTime : ComputableInPolyTime prepare SortedQuarterMachine.encoding
    SmallDP.encoding := by
  have bound : ComputableInPolyTime computedBound SortedQuarterMachine.encoding encUnary :=
    width_polyTime.comp (by fun_prop)
  exact bound.prod ComputableInPolyTime.id'

/-- One fixed native machine computes the threshold, projects, counts and reads the answer.
The new threshold header and all original data/materialization are charged preprocessing. -/
noncomputable def runCertificate : NativeCertificate run SortedQuarterMachine.encoding encBool :=
  SmallDP.runCertificate.comp (NativeCertificate.ofPolyTime prepare_polyTime)

private theorem computed_words {m : ℕ} (seed : BitVec m) (as : List (BitVec m)) :
    computedBound ((m, seed.toNat), as.map BitVec.toNat) =
      listMax (fun a : BitVec m => a.toNat.size) as := by
  simp only [computedBound, streamRecordLength, listMax, List.map_map,
    Function.comp_def, encNat_apply, Nat.size_eq_bits_len]

/-- No supplied magnitude, projected instance, table, witness or execution conclusion is needed. -/
theorem original_correct {m : ℕ} (seed : BitVec m) (as : List (BitVec m)) :
    run ((m, seed.toNat), as.map BitVec.toNat) = true ↔ Solvable as seed 0 := by
  apply SmallDP.original_correct
  intro a ha
  have size : a.toNat.size ≤ computedBound ((m, seed.toNat), as.map BitVec.toNat) := by
    rw [computed_words]
    exact le_listMax (f := fun a : BitVec m => a.toNat.size) ha
  exact (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) size)

/-- Proposition 4's original-input native bit resources, including computing the magnitude.
The source's operand inequality is the only problem restriction; the seed is unrestricted. -/
theorem source_parameter_bounds : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m s (seed : BitVec m) (as : List (BitVec m)), (∀ a ∈ as, a.toNat < 2^s) →
      runCertificate.time ((m, seed.toNat), as.map BitVec.toNat) ≤ 2^s*P (m+as.length+1) ∧
      runCertificate.space ((m, seed.toNat), as.map BitVec.toNat) ≤ 2^s*P (m+as.length+1) := by
  obtain ⟨A, hpA, mA, bound⟩ := SmallDP.source_parameter_bounds
  obtain ⟨D, hpD, mD, prepBound⟩ := exists_mono_poly_cert prepare_polyTime
  let R := fun b => 10*(b+1)^2
  let P := fun b => A (2*b)+D (R b)
  have hp : Cslib.PolynomiallyBounded P := by dsimp only [P, R]; fun_prop
  have mr : Monotone R := fun _ _ h => Nat.mul_le_mul_left 10
    (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2)
  have mp : Monotone P := fun _ _ h => Nat.add_le_add (mA (Nat.mul_le_mul_left 2 h)) (mD (mr h))
  refine ⟨P, hp, mp, fun m s seed as small => ?_⟩
  let input : SortedQuarterMachine.Input := ((m, seed.toNat), as.map BitVec.toNat)
  let B := computedBound input
  have bm : B ≤ m := by
    dsimp only [B, input]
    rw [computed_words]
    exact listMax_le fun a _ => Nat.size_le.mpr a.isLt
  have bs : B ≤ s := by
    dsimp only [B, input]
    rw [computed_words]
    exact listMax_le fun a ha => Nat.size_le.mpr (small a ha)
  have words := length_encList_le encNat (as.map BitVec.toNat) (b := m) (by
    intro n hn
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hn
    exact length_encNat_le_of_lt_two_pow a.isLt)
  rw [List.length_map] at words
  have seedBits := length_encNat_le_of_lt_two_pow seed.isLt
  have wire : (SortedQuarterMachine.encoding input).length ≤ R (m+as.length+1) := by
    simp only [input, SortedQuarterMachine.encoding, length_encPair, encUnary_apply,
      List.length_replicate]
    dsimp only [R]
    nlinarith only [words, seedBits, Nat.zero_le (m^2), Nat.zero_le (as.length^2)]
  have actual := bound m B seed as
  have smallP := Nat.mul_le_mul
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) bs)
    (mA (show m+B+as.length+1 ≤ 2*(m+as.length+1) by omega))
  have prep := prepBound input
  have prepP := mD wire
  have copy := Nat.mul_le_mul_right (D (R (m+as.length+1)))
    (show 1 ≤ 2^s from Nat.one_le_two_pow)
  change (NativeCertificate.ofPolyTime prepare_polyTime).time input+
      SmallDP.runCertificate.time (SmallDP.ofWords B seed as) ≤ 2^s*P (m+as.length+1) ∧
    (NativeCertificate.ofPolyTime prepare_polyTime).space input+
      SmallDP.runCertificate.space (SmallDP.ofWords B seed as) ≤ 2^s*P (m+as.length+1)
  constructor <;> dsimp only [P] <;>
    nlinarith only [actual.1, actual.2, prep.1, prep.2, smallP, prepP, copy]

end Cslib.Cryptanalysis.AddXNOR.SmallAutomatic
