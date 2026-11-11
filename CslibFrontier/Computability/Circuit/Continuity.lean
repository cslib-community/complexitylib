/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Complexity
public import Mathlib.Data.Nat.Dist
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Foundations.Data.Hamming

/-!
# The modulus of continuity of circuit complexity

Over a finite carrier `U` and a complete interpretation `I`, the *modulus of continuity* of circuit
complexity, `ω_{I,n,m}(r)` (`Cslib.Circuits.complexityModulus`), is the largest change
`|C_I(f) - C_I(g)|` in the complexity of two functions with `n` inputs and `m` outputs that differ
on at most `r` inputs, that is, at Hamming distance at most `r` as functions of their inputs. It is
a natural number, it is attained (`Cslib.Circuits.exists_dist_complexity_eq_complexityModulus`), it
increases with `r` and vanishes at `r = 0`, and it is subadditive,
`ω(r + s) ≤ ω(r) + ω(s)` (`Cslib.Circuits.complexityModulus_add_le`): a change on `r + s` inputs
is a change on `r` inputs followed by a change on `s` inputs. In particular `ω(r) ≤ r ω(1)`.

A function with one output is at the Hamming distance of its single value
(`Cslib.Circuits.hammingDist_single`), so the modulus for one output measures changes of
single-valued functions. For the De Morgan basis the modulus at the square root of the number of
inputs is located in `CslibFrontier.Computability.Circuit.Boolean.Continuity`.

## Main definitions

* `Cslib.Circuits.complexityModulus`: the modulus of continuity of circuit complexity.

## Main results

* `Cslib.Circuits.dist_complexity_le_complexityModulus`,
  `Cslib.Circuits.complexityModulus_le_iff`,
  `Cslib.Circuits.exists_dist_complexity_eq_complexityModulus`: the modulus is the least bound and
  is attained.
* `Cslib.Circuits.complexityModulus_mono`, `Cslib.Circuits.complexityModulus_zero`,
  `Cslib.Circuits.complexityModulus_add_le`, `Cslib.Circuits.complexityModulus_le_mul`: monotone,
  zero at zero, subadditive.
* `Cslib.Circuits.hammingDist_single`: the Hamming distance of functions with one output.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

open Finset

variable {σ : Signature} {U : Type*} [Fintype U] [DecidableEq U] {n m r s : ℕ}

/-- A function with one output is at the Hamming distance of its single value. -/
@[simp] theorem hammingDist_single (f g : (Fin n → U) → U) :
    hammingDist (single f) (single g) = hammingDist f g :=
  hammingDist_comp (fun _ b _ => b) fun _ _ _ h => congrFun h 0

variable (I : Interpretation σ U) [I.IsComplete]

/-- The **modulus of continuity** `ω_{I,n,m}(r)` of circuit complexity: the largest change
`|C_I(f) - C_I(g)|` in the complexity of two functions with `n` inputs and `m` outputs over a
finite carrier `U` that differ on at most `r` inputs. -/
noncomputable def complexityModulus (n m r : ℕ) : ℕ :=
  ((univ : Finset (((Fin n → U) → Fin m → U) × ((Fin n → U) → Fin m → U))).filter
    fun fg => hammingDist fg.1 fg.2 ≤ r).sup fun fg =>
      Nat.dist (complexity I fg.1) (complexity I fg.2)

variable {I}

/-- Functions that differ on at most `r` inputs have complexities at most `ω(r)` apart. -/
theorem dist_complexity_le_complexityModulus {f g : (Fin n → U) → Fin m → U}
    (h : hammingDist f g ≤ r) :
    Nat.dist (complexity I f) (complexity I g) ≤ complexityModulus I n m r :=
  le_sup (f := fun fg : ((Fin n → U) → Fin m → U) × ((Fin n → U) → Fin m → U) =>
    Nat.dist (complexity I fg.1) (complexity I fg.2)) (mem_filter.2 ⟨mem_univ (f, g), h⟩)

/-- The modulus is the least bound on the change in complexity over changes on at most `r`
inputs. -/
theorem complexityModulus_le_iff {k : ℕ} :
    complexityModulus I n m r ≤ k ↔ ∀ f g : (Fin n → U) → Fin m → U, hammingDist f g ≤ r →
      Nat.dist (complexity I f) (complexity I g) ≤ k := by
  simp only [complexityModulus, Finset.sup_le_iff, mem_filter, mem_univ, true_and, Prod.forall]

/-- **The modulus is attained.** -/
theorem exists_dist_complexity_eq_complexityModulus [Nonempty U] :
    ∃ f g : (Fin n → U) → Fin m → U, hammingDist f g ≤ r ∧
      Nat.dist (complexity I f) (complexity I g) = complexityModulus I n m r := by
  have hne : ((univ : Finset (((Fin n → U) → Fin m → U) × ((Fin n → U) → Fin m → U))).filter
      fun fg => hammingDist fg.1 fg.2 ≤ r).Nonempty :=
    ⟨(fun _ _ => Classical.arbitrary U, fun _ _ => Classical.arbitrary U), by simp⟩
  obtain ⟨⟨f, g⟩, hfg, heq⟩ := exists_mem_eq_sup _ hne fun fg =>
    Nat.dist (complexity I fg.1) (complexity I fg.2)
  exact ⟨f, g, (mem_filter.1 hfg).2, heq.symm⟩

/-- The modulus increases with the number of changed inputs. -/
theorem complexityModulus_mono : Monotone (complexityModulus I n m) := fun _ _ hrs =>
  complexityModulus_le_iff.2 fun _ _ h => dist_complexity_le_complexityModulus (h.trans hrs)

/-- Changing no input does not change the complexity. -/
@[simp] theorem complexityModulus_zero : complexityModulus I n m 0 = 0 :=
  Nat.le_zero.1 <| complexityModulus_le_iff.2 fun f g h => by
    rw [Nat.le_zero, hammingDist_eq_zero] at h
    rw [h, Nat.dist_self]

/-- **The modulus is subadditive**: `ω(r + s) ≤ ω(r) + ω(s)`. -/
theorem complexityModulus_add_le :
    complexityModulus I n m (r + s) ≤ complexityModulus I n m r + complexityModulus I n m s :=
  complexityModulus_le_iff.2 fun _ _ h => by
    obtain ⟨k, hfk, hkg⟩ := exists_hammingDist_le_and_hammingDist_le h
    exact (Nat.dist.triangle_inequality _ (complexity I k) _).trans
      (add_le_add (dist_complexity_le_complexityModulus hfk)
        (dist_complexity_le_complexityModulus hkg))

/-- The change in complexity is at most `ω(1)` per changed input. -/
theorem complexityModulus_le_mul : complexityModulus I n m r ≤ r * complexityModulus I n m 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.succ_mul]
    exact (complexityModulus_add_le (r := r) (s := 1)).trans (Nat.add_le_add_right ih _)

end Cslib.Circuits
