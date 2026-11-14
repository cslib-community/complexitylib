/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.NativeRecovery
public import CslibFrontier.Computability.Circuit.Arithmetic.Formula

/-!
# Balanced recovery numerator products

The numerator of tapered recovery is a sequential fold in `NativeRecovery.basisNum`.
Here its factors are indexed by the original node numbers: the two excluded nodes contribute
one. This removes filtered-list indexing and permits a balanced multiplication skeleton of
at most `a + 1` levels. The skeleton has the factors as inputs; constructing or querying the
factors, multiplication bit complexity, and native machine navigation are separate obligations.
-/

public section

namespace Cslib.Circuits.Frontier.NativeRecovery

open Cslib.GaloisRingArith

/-- One numerator factor at its original node index, with identity padding at excluded nodes. -/
@[expose] def basisFactor (N : ℕ) (fl : List ℕ) (a u h k j : ℕ) : List ℕ :=
  if j ≠ 2 ^ a ∧ j ≠ k then
    pow N fl (mul N fl (diffConst N fl (2 ^ a) j) (slopeConst N fl a k j)) (mult a u h j)
  else one fl

/-- Balance the numerator product over all node indices, without constructing `others`. -/
@[expose] def balancedBasisNum (N : ℕ) (fl : List ℕ) (a u h k : ℕ) : List ℕ :=
  (List.range (2 ^ (a + 1))).balancedFold (mul N fl) (one fl)
    (basisFactor N fl a u h k)

/-- The balanced numerator agrees with the existing sequential procedure in the quotient ring.
No irreducibility hypothesis is needed for this reassociation. -/
theorem val_balancedBasisNum (N : ℕ) (fl : List ℕ) (a u h k : ℕ) :
    val N fl (balancedBasisNum N fl a u h k) = val N fl (basisNum N fl a u h k) := by
  rw [balancedBasisNum, List.balancedFold_hom (val N fl) (val_mul), val_one,
    List.balancedFold_eq_foldr]
  change ((List.range (2 ^ (a + 1))).map
    (fun j => val N fl (basisFactor N fl a u h k j))).prod = _
  simp only [basisFactor, apply_ite, val_one]
  rw [List.prod_map_ite]
  simp only [List.map_const', List.prod_replicate, one_pow, mul_one]
  rw [basisNum, val_foldl_mul, val_one, one_mul]
  rfl

/-- The product of a contiguous interval of original node numbers. The interval is described
by two integers; this definition does not require a filtered list of surviving nodes. -/
noncomputable def basisIntervalValue (N : ℕ) (fl : List ℕ) (a u h k offset size : ℕ) : Ring N fl :=
  ∏ j ∈ Finset.range size, val N fl (basisFactor N fl a u h k (offset + j))

/-- A singleton interval reads exactly one directly indexed factor. -/
theorem basisIntervalValue_one (N : ℕ) (fl : List ℕ) (a u h k offset : ℕ) :
    basisIntervalValue N fl a u h k offset 1 =
      val N fl (basisFactor N fl a u h k offset) := by
  simp [basisIntervalValue]

/-- Local routing in the balanced product: halve the interval and select its left or right half.
A path has exactly `d + 1` such steps until a singleton, with no filtered-index lookup. -/
theorem basisIntervalValue_split (N : ℕ) (fl : List ℕ) (a u h k offset d : ℕ) :
    basisIntervalValue N fl a u h k offset (2 ^ (d + 1)) =
      basisIntervalValue N fl a u h k offset (2 ^ d) *
        basisIntervalValue N fl a u h k (offset + 2 ^ d) (2 ^ d) := by
  simp only [basisIntervalValue, pow_succ, Nat.mul_two, Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Nat.add_assoc]

/-- The root interval has exactly the quotient-ring value of the original numerator fold. -/
theorem basisIntervalValue_root (N : ℕ) (fl : List ℕ) (a u h k : ℕ) :
    basisIntervalValue N fl a u h k 0 (2 ^ (a + 1)) =
      val N fl (basisNum N fl a u h k) := by
  rw [← val_balancedBasisNum N fl a u h k, balancedBasisNum,
    List.balancedFold_hom (val N fl) (val_mul), val_one, List.balancedFold_eq_foldr]
  simp only [basisIntervalValue, Nat.zero_add, Function.comp_def]
  rw [← List.prod_eq_foldr]
  rw [← List.prod_toFinset _ List.nodup_range]
  congr 1
  ext j
  simp

/-- The balanced numerator's multiplication skeleton; input `j` denotes `basisFactor ... j`.
The only constant is the empty-product identity, which is unused for the nonempty grid. -/
@[expose] def basisProductFormula (a : ℕ) : Formula (arithSignature ℕ) (2 ^ (a + 1)) :=
  Formula.balanced .mul rfl (.gate (.const 1) Fin.elim0)
    ((List.finRange (2 ^ (a + 1))).map Formula.input)

/-- The skeleton computes the recovery numerator from directly indexed factor inputs. -/
theorem eval_basisProductFormula (N : ℕ) (fl : List ℕ) (a u h k : ℕ) :
    (basisProductFormula a).eval (arithInterpretationWith ℕ (Nat.cast : ℕ → Ring N fl))
      (fun j => val N fl (basisFactor N fl a u h k j)) =
        val N fl (basisNum N fl a u h k) := by
  rw [basisProductFormula, Formula.eval_balanced]
  simp only [Fin.cast_eq_self, arithInterpretationWith_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Formula.eval_gate, arithInterpretationWith_const, Nat.cast_one]
  change (((List.finRange (2 ^ (a + 1))).map Formula.input).balancedFold
    (· * ·) (1 : Ring N fl)
    (fun F => F.eval (arithInterpretationWith ℕ (Nat.cast : ℕ → Ring N fl))
      (fun j => val N fl (basisFactor N fl a u h k j)))) = _
  rw [List.balancedFold_eq_foldr]
  simp only [List.map_map, Function.comp_def, Formula.eval_input]
  rw [← val_balancedBasisNum N fl a u h k, balancedBasisNum,
    List.balancedFold_hom (val N fl) (val_mul), val_one, List.balancedFold_eq_foldr]
  simp only [Function.comp_def]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- The numerator multiplication skeleton has at most `a + 1` levels. This bounds algebraic
multiplication depth only, not native bit-evaluation time or the depth of the factor inputs. -/
theorem depth_basisProductFormula_le (a : ℕ) : (basisProductFormula a).depth ≤ a + 1 := by
  have h := Formula.depthWith_balanced_le (σ := arithSignature ℕ) (n := 2 ^ (a + 1))
    (op := ArithOp.mul) (hop := rfl) (cost := 1)
    (d := 0) (.gate (.const (1 : ℕ)) Fin.elim0)
    (l := (List.finRange (2 ^ (a + 1))).map Formula.input)
    (by intro F hF; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hF; simp)
    (by intro he; have := congrArg List.length he; simp at this)
  simpa [basisProductFormula, List.length_finRange, Nat.clog_pow] using h

end Cslib.Circuits.Frontier.NativeRecovery
