/-
Copyright (c) 2026 Vincent Palma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.Nullstellensatz.Proof
public import CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.Proof
import CslibFrontier.Foundations.Data.MvPolynomial.Support
import Mathlib.Tactic.Ring.RingNF

/-!
# Simulating Nullstellensatz proofs in polynomial calculus

An NS certificate for a nonzero polynomial `q`, of size at most `s` and degree at most `d`,
yields a PC proof containing `q`, of size at most `s ^ 2 + (d + 1) * s` and degree at most `d`
(`Cslib.Logic.PL.PC.exists_isProof_of_ns`). Both bounds hold for
the same PC proof. The construction expands each multiplier into monomials, derives the
corresponding monomial multiples of the inputs, and combines them with their coefficients.
The refutation case `q = 1` over nontrivial coefficients is
`Cslib.Logic.PL.PC.exists_refutation_of_ns`.

A size bound alone uses a replacement certificate. If every input has total degree at most
`d₀`, `Cslib.Logic.PL.NS.IsProof.exists_degree_le_mul_size` gives an NS refutation
of no larger size and degree at most `d₀ * s`. Simulating it gives PC size at most
`(d₀ + 1) * s ^ 2 + s` (`Cslib.Logic.PL.PC.RefutableInSize.of_ns`).
The degree-only corollary preserves the NS degree bound
(`Cslib.Logic.PL.PC.RefutableInDegree.of_ns`).

## Relation to the source

[de Rezende et al., Fact 8.1, p. 218][DeRezendeEtAl2021] states, over a field, that an NS proof
of a polynomial from `n`-variate inputs yields a PC proof of size `poly(s, n)`, preserving
degree or block-degree. Here nonzero targets are handled for total degree over a commutative
semiring, with the explicit degree-dependent bounds above. `NS.size` follows the
source's size convention `∑ i, ‖p i‖ * ‖f i‖`. The size-only corollary additionally uses an
input-degree bound and the auxiliary gap-truncation lemma proved in
`CslibFrontier.Logics.Propositional.Algebraic.Nullstellensatz.Proof`.

The refutation simulations assume nontrivial coefficients. Over the trivial semiring the empty
input list has an NS refutation, since its empty sum equals `1`, but no PC refutation, since a
PC proof from no inputs has no lines.

## Main results

* `Cslib.Logic.PL.PC.exists_isProof_of_ns`: simultaneous size and
  degree bounds for one PC proof of a nonzero NS target.
* `Cslib.Logic.PL.PC.exists_refutation_of_ns`: the refutation specialization over
  nontrivial coefficients.
* `Cslib.Logic.PL.PC.RefutableInSize.of_ns`: PC size at most
  `(d₀ + 1) * s ^ 2 + s` from NS size at most `s` and input degrees at most `d₀`.
* `Cslib.Logic.PL.PC.RefutableInDegree.of_ns`: PC refutability
  within the NS degree bound.

## References

* [S. F. de Rezende, M. Göös, J. Nordström, T. Pitassi, R. Robere, D. Sokolov,
  *Automating Algebraic Proof Systems Is NP-Hard*, STOC 2021, Fact 8.1, p. 218][DeRezendeEtAl2021]
-/

public section

namespace Cslib.Logic.PL.PC

variable {V R : Type*} [CommSemiring R]

open MvPolynomial

/-- An NS certificate for a nonzero polynomial `q`, of size at most `s` and degree at most `d`,
yields a PC proof containing `q`, of size at most `s ^ 2 + (d + 1) * s` and degree at most `d`.
Both bounds hold for the same PC proof. This gives a simulation related to
[DeRezendeEtAl2021, Fact 8.1], with an explicit degree-dependent size bound. -/
theorem exists_isProof_of_ns {s d : ℕ} {F : List (MvPolynomial V R)}
    {P : Fin F.length → MvPolynomial V R} {q : MvPolynomial V R}
    (hP : NS.IsProof F P q) (hq : q ≠ 0)
    (hs : NS.size F P ≤ s) (hd : NS.degree F P ≤ d) :
    ∃ ls : List (MvPolynomial V R), IsProof F ls ∧ q ∈ ls ∧
      size ls ≤ s ^ 2 + (d + 1) * s ∧ degree ls ≤ d := by
  classical
  let t := Finset.univ.sigma fun i : Fin F.length => (P i).support
  let p : (Σ _ : Fin F.length, V →₀ ℕ) → MvPolynomial V R :=
    fun x => monomial x.2 1 * F.get x.1
  let a : (Σ _ : Fin F.length, V →₀ ℕ) → R := fun x => (P x.1).coeff x.2
  let w : (Σ _ : Fin F.length, V →₀ ℕ) → ℕ := fun x => (F.get x.1).support.card
  have hsum : ∑ x ∈ t, C (a x) * p x = q := by
    dsimp only [t, p, a]
    rw [Finset.sum_sigma]
    calc
      _ = ∑ i, F.get i * P i := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [← mul_assoc, C_mul_monomial, mul_one]
        rw [← Finset.sum_mul, support_sum_monomial_coeff, mul_comm]
      _ = q := hP
  have hw : ∑ x ∈ t, w x = NS.size F P := by
    dsimp only [t, w]
    rw [Finset.sum_sigma]
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, NS.size, Nat.mul_comm]
  have hsupport (x) (_ : x ∈ t) : (p x).support.card ≤ w x :=
    card_support_monomial_mul_le _ _ _
  have hproof x (hx : x ∈ t) (_ : p x ≠ 0) :
      ∃ ls, IsProof F ls ∧ p x ∈ ls ∧ size ls ≤ (d + 1) * w x ∧ degree ls ≤ d := by
    have hmx : x.2 ∈ (P x.1).support := (Finset.mem_sigma.mp hx).2
    have hdx : (F.get x.1).totalDegree + x.2.degree ≤ d :=
      (Finset.le_sup_of_le (Finset.mem_univ x.1)
        (Finset.le_sup (f := fun m => (F.get x.1).totalDegree + m.degree) hmx)).trans hd
    obtain ⟨ls, hls, hm, hs', hd'⟩ := exists_isProof_monomial_mul (List.get_mem F x.1) x.2
    refine ⟨ls, hls, hm, hs'.trans ?_, hd'.trans hdx⟩
    exact Nat.mul_le_mul_right _ (by omega)
  obtain ⟨ls, hls, hmem, hs', hd'⟩ :=
    exists_isProof_sum t p a w (fun x => (d + 1) * w x) d hsupport hproof
      (hsum.symm ▸ hq)
  refine ⟨ls, hls, hsum ▸ hmem, hs'.trans ?_, hd'⟩
  rw [← Finset.mul_sum, hw]
  exact Nat.add_le_add (Nat.pow_le_pow_left hs 2) (Nat.mul_le_mul_left _ hs)

variable [Nontrivial R]

/-- An NS refutation certificate of size at most `s` and degree at most `d` yields
a PC refutation satisfying both bounds `s ^ 2 + (d + 1) * s` and `d`. -/
theorem exists_refutation_of_ns {s d : ℕ} {F : List (MvPolynomial V R)}
    {P : Fin F.length → MvPolynomial V R} (hP : NS.IsProof F P 1)
    (hs : NS.size F P ≤ s) (hd : NS.degree F P ≤ d) :
    ∃ ls : List (MvPolynomial V R), IsProof F ls ∧ 1 ∈ ls ∧
      size ls ≤ s ^ 2 + (d + 1) * s ∧ degree ls ≤ d :=
  exists_isProof_of_ns hP one_ne_zero hs hd

/-- An NS refutation of size at most `s` yields a PC refutation of size at most
`(d₀ + 1) * s ^ 2 + s` when every input polynomial has total degree at most `d₀`.
The construction first replaces the NS certificate without increasing its size. -/
theorem RefutableInSize.of_ns {s d₀ : ℕ} {F : List (MvPolynomial V R)}
    (hd₀ : ∀ f ∈ F, f.totalDegree ≤ d₀) (hs : NS.RefutableInSize F s) :
    RefutableInSize F ((d₀ + 1) * s ^ 2 + s) := by
  obtain ⟨P, hP, hs⟩ := hs
  obtain ⟨Q, hQ, hsize, hdeg⟩ := hP.exists_degree_le_mul_size hd₀
  obtain ⟨ls, hls, h1, hS, _⟩ := exists_refutation_of_ns (s := s) (d := d₀ * s)
    hQ (hsize.trans hs) (hdeg.trans (Nat.mul_le_mul_left d₀ hs))
  refine ⟨ls, hls, h1, hS.trans_eq ?_⟩
  ring

/-- An NS refutation of degree at most `d` yields a PC refutation of degree at most `d`. -/
theorem RefutableInDegree.of_ns {d : ℕ} {F : List (MvPolynomial V R)}
    (hs : NS.RefutableInDegree F d) : RefutableInDegree F d := by
  obtain ⟨P, hP, hd⟩ := hs
  obtain ⟨ls, hls, h1, _, hd'⟩ := exists_refutation_of_ns hP le_rfl hd
  exact ⟨ls, hls, h1, hd'⟩

end Cslib.Logic.PL.PC
