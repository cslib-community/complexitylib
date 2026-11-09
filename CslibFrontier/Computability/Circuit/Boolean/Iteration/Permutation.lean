/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.Encoded
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Inverting permutations and testing periodicity

The inverse of a permutation `p` of a finite type is the power `p^[k! - 1]`, where `k` is the
number of elements (`iterate_factorial_pred_eq_symm`). The fixed-power bound does not depend on
the exponent, so a permutation computed by a circuit of size `s` has an inverse circuit within
the same bound (`permutation_inverse`), also through a supplied encoding of an arbitrary finite
type (`permutation_inverse_encoded`). Similarly, `x` is a periodic point exactly when
`f^[(2 ^ n)!] x = x`, which one more equality test decides (`periodicPts_circuit`).

## Main results

* `Cslib.Circuits.Boolean.Iteration.permutation_inverse`: inverting a permutation circuit.
* `Cslib.Circuits.Boolean.Iteration.permutation_inverse_encoded`: inverting through an encoding.
* `Cslib.Circuits.Boolean.Iteration.periodicPts_circuit`: deciding periodicity.

## References

* Adapted from lean/Proofs/Applications.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

universe u

variable {α : Type u} [Fintype α] {n : ℕ}

/-- The inverse of a permutation of a finite type is its `(card α)! - 1`-st power. -/
theorem iterate_factorial_pred_eq_symm (p : Equiv.Perm α) :
    (p : α → α)^[Nat.factorial (Fintype.card α) - 1] = p.symm := by
  funext x
  have h := congrFun (Function.injective_iff_iterate_factorial_card_eq_id.mp p.injective)
    (p.symm x)
  have hpos := Nat.factorial_pos (Fintype.card α)
  rw [show Nat.factorial (Fintype.card α) = (Nat.factorial (Fintype.card α) - 1) + 1 by omega,
    Function.iterate_succ_apply, p.apply_symm_apply] at h
  exact h

/-- **Permutation inversion.** A permutation computed by a circuit of size `s` has an inverse
circuit of size at most `40000 * powerBudget n s (2 ^ n) L`. -/
theorem permutation_inverse (c : Circuit signature n n) (p : Equiv.Perm (BitString n))
    (hc : c.Computes interpretation p) (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n n,
      out.Computes interpretation p.symm ∧
      out.size ≤ 40000 * powerBudget n c.size (2 ^ n) L := by
  obtain ⟨out, hout, hs⟩ :=
    fixed_power n c (Nat.factorial (Fintype.card (BitString n)) - 1) L hL hLN
  have he : c.eval interpretation = p := funext hc
  exact ⟨out, by simpa only [he, iterate_factorial_pred_eq_symm] using hout, hs⟩

/-- **Encoded permutation inversion.** A permutation of a finite type of any universe, realized
by a circuit on an injective encoding, has an inverse circuit whose storage term counts the
type. -/
theorem permutation_inverse_encoded (p : Equiv.Perm α) (e : α → BitString n)
    (he : Function.Injective e) (c : Circuit signature n n)
    (hc : ∀ x, c.eval interpretation (e x) = e (p x)) (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n n,
      (∀ x, out.eval interpretation (e x) = e (p.symm x)) ∧
      out.size ≤ 40000 * powerBudget n c.size (Fintype.card α) L := by
  obtain ⟨out, hout, hs⟩ := fixed_power_encoded p Finset.univ e he.injOn c
    (fun _ _ => Finset.mem_univ _) (fun x _ => hc x)
    (Nat.factorial (Fintype.card α) - 1) L hL hLN
  refine ⟨out, fun x => ?_, by simpa using hs⟩
  simpa only [iterate_factorial_pred_eq_symm] using hout x (Finset.mem_univ x)

/-- **Periodic points.** Whether a state is periodic for a circuit's map is decided by one
fixed power and an equality test. -/
theorem periodicPts_circuit (c : Circuit signature n n) (L : ℕ) (hL : 0 < L)
    (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n 1,
      (∀ x, out.eval interpretation x 0 = true ↔
        x ∈ Function.periodicPts (c.eval interpretation)) ∧
      out.size ≤ 40000 * powerBudget n c.size (2 ^ n) L + (6 * n + 1) := by
  classical
  obtain ⟨pow, hp, hs⟩ := fixed_power n c (Nat.factorial (Fintype.card (BitString n))) L hL hLN
  have hpow := Synthesis.circuit (I := interpretation) (s := inputs n) pow (fun i x => x i)
    fun bit => ⟨bit, rfl⟩
  have heq := synthesis_bits_eq (inputs n ∪ wires (pow.eval interpretation))
    (pow.eval interpretation) id (fun _ h => Or.inr h) fun _ h => Or.inl h
  obtain ⟨out, hout, hsize⟩ := (hpow.trans heq).exists_circuit
  refine ⟨out, fun x => ?_, hsize.trans (Nat.add_le_add_right hs _)⟩
  rw [hout x]
  change decide (pow.eval interpretation x = x) = true ↔ _
  rw [decide_eq_true_eq, hp x]
  exact Function.mem_periodicPts_iff_isPeriodicPt_factorial_card.symm

end Cslib.Circuits.Boolean.Iteration
