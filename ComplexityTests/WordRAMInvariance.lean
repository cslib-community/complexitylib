/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.P.WordRAM
import Complexity.Computability.Complexity.Problems.ElementDistinctness
import Complexity.Computability.Circuit.Boolean.ACC0

/-!
# `P` and polynomial time on the word RAM, in both directions

Parity, proved in `P` with a Turing machine, gets an additive word-RAM decider on its bits and
returns to `P` through the simulation of the word RAM. Element distinctness, placed in `P` from a
word-RAM algorithm over its words, gets an additive decider on its bits. The decider of every
problem in `P` answers on every instance at some word size, so the word-RAM contract is not
vacuous. The extra operations of `Basis.standard` do not enlarge uniform polynomial time on bits.
At the level of functions, binary addition has a polynomial-time word-RAM program.
-/

namespace ComplexityTests.WordRAMInvariance

open Cslib Cslib.WordRAM Turing.MultiTapeTM

/-! ## A problem in `P` through a Turing machine -/

/-- Parity has a uniform polynomial-time decider over `Basis.additive`, on its bits. -/
theorem parity_uniformPolynomialTime :
    UniformPolynomialTime .additive (Language.ofSlices parity : Set (List Bool))
      (fun _ l => l.map Bool.toNat) (fun l => l.length) :=
  uniformPolynomialTime_of_mem_P Circuits.Boolean.parity_mem_P

/-- The round trip: the word-RAM decider of parity places parity back in `P`. -/
example : (Language.ofSlices parity : Set (List Bool)) ∈ Complexity.P encBits :=
  parity_uniformPolynomialTime.mem_P
    (Basis.standard.restrict_checkedOp_polyTime _ checkedOp_polyTime) PolyBounded.self
    (computableInPolyTime_map_toNat encBits)

/-- Over `Basis.arithmetic` too. -/
example : UniformPolynomialTime .arithmetic (Language.ofSlices parity : Set (List Bool))
    (fun _ l => l.map Bool.toNat) (fun l => l.length) :=
  mem_P_iff_uniformPolynomialTime_arithmetic.1 Circuits.Boolean.parity_mem_P

/-! ## A problem in `P` through the word RAM -/

open Cslib.Algorithms.WordRAM.ElementDistinctness in
/-- Element distinctness, in `P` from a word-RAM algorithm on its words, has an additive word-RAM
decider on the bits of its encoding. -/
example : UniformPolynomialTime .additive {l : Input | l.1.Nodup}
    (fun _ l => (inputEncoding l).map Bool.toNat) (fun l => (inputEncoding l).length) :=
  uniformPolynomialTime_of_mem_P nodup_mem_P

/-! ## Nonvacuity -/

/-- The word-RAM decider of a problem in `P` answers on every instance, at some word size the
instance fits. -/
example {α : Type} {encIn : α ↪ List Bool} {A : Set α} (h : A ∈ Complexity.P encIn) :
    ∃ (r : ℕ) (p : Program .additive r) (T : ℕ → ℕ), PolynomiallyBounded T ∧
      ∀ a, ∃ w, p.Answers w ((encIn a).map Bool.toNat) (a ∈ A) (T (encIn a).length) := by
  obtain ⟨T, hT, k, -, r, p, hp⟩ := uniformPolynomialTime_of_mem_P h
  refine ⟨r, p, T, hT, fun a => ⟨logWidth k (encIn a).length + (encIn a).length + 1,
    hp a _ (by dsimp only; omega) ⟨?_, fun v hv => ?_⟩⟩⟩
  · rw [List.length_map]
    exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hv
    exact (Bool.toNat_le b).trans_lt (Nat.one_lt_two_pow_iff.2 (by omega))

/-! ## The basis does not matter -/

/-- Uniform polynomial time on bits over `Basis.standard` is uniform polynomial time over
`Basis.additive`: multiplication, division, bitwise operations, shifts and reading the word size
add no power here. -/
example {α : Type} {encIn : α ↪ List Bool} {A : Set α}
    (h : UniformPolynomialTime .standard A (fun _ a => (encIn a).map Bool.toNat)
      (fun a => (encIn a).length)) :
    UniformPolynomialTime .additive A (fun _ a => (encIn a).map Bool.toNat)
      (fun a => (encIn a).length) :=
  mem_P_iff_uniformPolynomialTime_additive.1 (mem_P_iff_uniformPolynomialTime_standard.2 h)

/-! ## Functions -/

/-- Binary addition has a polynomial-time word-RAM program over `Basis.standard`, on the bits of
the encoded pair, at polynomial word sizes. -/
example : ∃ (r : ℕ) (p : Program .standard r) (T W : ℕ → ℕ), PolynomiallyBounded T ∧
    PolynomiallyBounded W ∧
      p.ComputesInTime (fun _ x => (encPair encNat encNat x).map Bool.toNat)
        (fun x _ => T (encPair encNat encNat x).length)
        (fun x w => W (encPair encNat encNat x).length ≤ w) (fun x : ℕ × ℕ => x.1 + x.2) :=
  (turingComputableInPolyTime_iff_exists_computesInTime Basis.additiveHomStandard
    checkedOp_polyTime).1 ComputableInPolyTime.binary_add

end ComplexityTests.WordRAMInvariance
