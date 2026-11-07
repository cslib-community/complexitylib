/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SetFamily/Oddtown.lean`)

public import Complexity.Init
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Card
import Complexity.Foundations.LinearAlgebra.Matrix.UniformGram
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Oddtown and the uniform Fisher inequality

Two linear algebra bounds on families of subsets of a finite set `κ`, both obtained from the
characteristic vectors of the sets, whose dot products are the intersection sizes, and the rank
bound `Fintype.card_le_of_dotProduct_eq_ite`:

* **Oddtown**: if every set has odd size and any two distinct members meet in an even number of
  points, the family has at most `|κ|` members. Over `ZMod 2` the Gram matrix is the identity.
  This is the classical oddtown theorem of the linear algebra method [Jukna2011, Chapter 13]; the
  exact theorem or exercise number there was not verified.
* **Uniform Fisher inequality**: if every set has size `d` and any two distinct members meet in
  exactly `c < d` points, the family has at most `|κ|` members. Over `ℚ` the Gram matrix is
  `(d - c) I + c J`, which is positive definite [Jukna2011, §7.3].

Families are indexed, `A : ι → Finset κ`; the hypotheses force `A` to be injective, so the bound is
on the number of distinct sets. Jukna's Fisher inequality allows sets of different sizes; only the
uniform case is formalized here.

## Main results

* `Fintype.card_le_of_odd_card_of_even_card_inter`: the oddtown theorem.
* `Fintype.card_le_of_card_eq_of_card_inter_eq`: the uniform Fisher inequality.

## References

* [S. Jukna, *Extremal Combinatorics*][Jukna2011]
-/

public section

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The characteristic vector of a finite set over a field `K`. -/
private def charVec (K : Type*) [Field K] (A : Finset κ) : κ → K := fun x => if x ∈ A then 1 else 0

private theorem charVec_dotProduct (K : Type*) [Field K] (A B : Finset κ) :
    charVec K A ⬝ᵥ charVec K B = (#(A ∩ B) : K) := by
  simp only [dotProduct, charVec, mul_ite, mul_one, mul_zero, ← ite_and]
  rw [sum_boole]
  congr 2
  ext x
  simp [and_comm]

/-- **Oddtown**: a family of odd-size subsets of `κ` whose distinct members pairwise meet in an even
number of points has at most `|κ|` members [Jukna2011, Chapter 13]. -/
theorem Fintype.card_le_of_odd_card_of_even_card_inter (A : ι → Finset κ)
    (hodd : ∀ i, Odd #(A i)) (heven : ∀ i j, i ≠ j → Even #(A i ∩ A j)) :
    Fintype.card ι ≤ Fintype.card κ := by
  classical
  refine Fintype.card_le_of_dotProduct_eq_ite (K := ZMod 2) (fun i => charVec (ZMod 2) (A i)) 1 0
    (fun i j => ?_) one_ne_zero (by simp)
  rw [charVec_dotProduct]
  split_ifs with h
  · subst h; rw [inter_self]; exact (ZMod.natCast_eq_one_iff_odd).2 (hodd i)
  · exact (ZMod.natCast_eq_zero_iff_even).2 (heven i j h)

/-- **Fisher's inequality**, uniform case: a family of `d`-subsets of `κ` whose distinct members
pairwise meet in exactly `c < d` points has at most `|κ|` members [Jukna2011, §7.3]. -/
theorem Fintype.card_le_of_card_eq_of_card_inter_eq (A : ι → Finset κ) {d c : ℕ} (hcd : c < d)
    (hcard : ∀ i, #(A i) = d) (hinter : ∀ i j, i ≠ j → #(A i ∩ A j) = c) :
    Fintype.card ι ≤ Fintype.card κ := by
  classical
  refine Fintype.card_le_of_dotProduct_eq_ite (K := ℚ) (fun i => charVec ℚ (A i)) d c
    (fun i j => ?_) (by exact_mod_cast hcd.ne') ?_
  · rw [charVec_dotProduct]
    split_ifs with h
    · subst h; rw [inter_self, hcard]
    · rw [hinter i j h]
  · have h1 : (0 : ℚ) < d - c := by
      have : (c : ℚ) < d := by exact_mod_cast hcd
      linarith
    have h2 : (0 : ℚ) ≤ (Fintype.card ι : ℚ) * c := by positivity
    linarith

end
