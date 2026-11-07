/-
Copyright (c) 2026 Vincent Palma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Finsupp.Weight
import Complexity.Foundations.Data.Finset.NatGap
import Complexity.Foundations.Data.MvPolynomial.TruncateTotalDegree

/-!
# Nullstellensatz proofs

A *Nullstellensatz proof* of a polynomial `q` from a list `F` of input polynomials is an
identity `∑ i, F.get i * P i = q` (`Cslib.Logic.PL.NS.IsProof`), where the
certificate `P` is a family of polynomial multipliers. A *refutation* proves `1`, expressing a
contradiction from the input equations `f = 0`. Proofs are sound: every common zero of the inputs
is a zero of the proved polynomial, so over nontrivial coefficients a refutable system has no
common zero.

Coefficients lie in a commutative semiring. The certificate identity uses addition and
multiplication, and input equations supply the axioms for the chosen encoding and basis.
The standard field setting is described in [de Rezende et al., §8.1, p. 217][DeRezendeEtAl2021].

The *size* follows the source's definition `∑ i, ‖p i‖ * ‖f i‖`, where `‖g‖` counts the nonzero
monomials of `g`. It counts pairs of input and multiplier monomials before the products are
collected. The *degree* bounds input degree plus multiplier degree for each nonzero multiplier,
and is `0` when every multiplier is zero. A nonzero multiplier of a zero input still contributes
its degree. These measures concern formal polynomials before any Boolean reduction.

If every input has total degree at most `d₀`, a refutation can be replaced without increasing
its size by one of degree at most `d₀` times the original size
(`NS.IsProof.exists_degree_le_mul_size`). The auxiliary gap-truncation argument proved here
replaces the multipliers by their low-degree parts.

## Main definitions

* `Cslib.Logic.PL.NS.IsProof`: the identity giving a Nullstellensatz proof.
* `Cslib.Logic.PL.NS.size`, `Cslib.Logic.PL.NS.degree`: size and
  degree of a certificate.
* `Cslib.Logic.PL.NS.RefutableInSize`,
  `Cslib.Logic.PL.NS.RefutableInDegree`: refutability with a bound on size or
  degree.

## Main results

* `Cslib.Logic.PL.NS.degree_le_iff`: characterize a degree bound by the nonzero
  multipliers.
* `Cslib.Logic.PL.NS.IsProof.single`, `Cslib.Logic.PL.NS.IsProof.add`,
  `Cslib.Logic.PL.NS.IsProof.mul_left`: input proofs, addition and polynomial
  multiplication.
* `Cslib.Logic.PL.NS.IsProof.eval_eq_zero`,
  `Cslib.Logic.PL.NS.IsProof.exists_eval_ne_zero`: soundness.
* `Cslib.Logic.PL.NS.IsProof.exists_degree_le_mul_size`: replace a refutation by one of no
  larger size with degree controlled by the original size and the input degrees.

## References

* [S. F. de Rezende, M. Göös, J. Nordström, T. Pitassi, R. Robere, D. Sokolov,
  *Automating Algebraic Proof Systems Is NP-Hard*, STOC 2021, §8.1, p. 217][DeRezendeEtAl2021]
-/

public section

namespace Cslib.Logic.PL.NS

variable {V R : Type*} [CommSemiring R]

/-! ### Complexity measures -/

/-- The monomial size of an NS certificate, the sum of products of input and multiplier
support sizes, as in [DeRezendeEtAl2021, §8.1]. -/
@[expose] def size (F : List (MvPolynomial V R)) (P : Fin F.length → MvPolynomial V R) : ℕ :=
  ∑ i, (F.get i).support.card * (P i).support.card

/-- The degree of an NS certificate, ignoring zero multipliers and returning `0` when every
multiplier is zero. A nonzero multiplier of a zero input polynomial still contributes its degree. -/
@[expose] def degree (F : List (MvPolynomial V R)) (P : Fin F.length → MvPolynomial V R) : ℕ :=
  Finset.univ.sup fun i => (P i).support.sup fun m => (F.get i).totalDegree + m.degree

/-- An NS certificate has degree at most `d` exactly when every term with a nonzero multiplier
has input degree plus multiplier degree at most `d`. -/
theorem degree_le_iff {F : List (MvPolynomial V R)} {P : Fin F.length → MvPolynomial V R}
    {d : ℕ} :
    degree F P ≤ d ↔ ∀ i, P i ≠ 0 → (F.get i).totalDegree + (P i).totalDegree ≤ d := by
  simp only [degree, Finset.sup_le_iff, Finset.mem_univ, forall_const]
  constructor
  · intro h i hi
    obtain ⟨m, hm, hdeg⟩ :=
      (P i).support.exists_mem_eq_sup (MvPolynomial.support_nonempty.mpr hi) Finsupp.degree
    have htot : (P i).totalDegree = m.degree := hdeg
    exact htot ▸ h i m hm
  · intro h i m hm
    exact (Nat.add_le_add_left (MvPolynomial.le_totalDegree hm) _).trans
      (h i (MvPolynomial.support_nonempty.mp ⟨m, hm⟩))

/-! ### Proofs -/

/-- The certificate `P` forms a **Nullstellensatz proof** of `q` from `F`:
`∑ i, F.get i * P i = q`. -/
@[expose] def IsProof (F : List (MvPolynomial V R)) (P : Fin F.length → MvPolynomial V R)
    (q : MvPolynomial V R) : Prop :=
  (∑ i, F.get i * P i) = q

namespace IsProof

/-- An input polynomial has a proof with multiplier `1` at its index and `0` elsewhere. -/
theorem single (F : List (MvPolynomial V R)) (i : Fin F.length) :
    IsProof F (Pi.single i 1) (F.get i) := by
  classical
  simp [IsProof, Pi.single_apply]

/-- Adding NS proofs gives a proof of the sum of their target polynomials. -/
theorem add {F : List (MvPolynomial V R)} {P Q : Fin F.length → MvPolynomial V R}
    {p q : MvPolynomial V R} (hP : IsProof F P p) (hQ : IsProof F Q q) :
    IsProof F (fun i => P i + Q i) (p + q) := by
  simp only [IsProof, mul_add, Finset.sum_add_distrib] at *
  rw [hP, hQ]

/-- Multiplying every multiplier by `p` proves `p` times the original target. -/
theorem mul_left {F : List (MvPolynomial V R)} {P : Fin F.length → MvPolynomial V R}
    {q : MvPolynomial V R} (h : IsProof F P q) (p : MvPolynomial V R) :
    IsProof F (fun i => p * P i) (p * q) := by
  unfold IsProof at *
  simp only [mul_left_comm (F.get _), ← Finset.mul_sum, h]

/-- **Soundness.** Every common zero of the inputs is a zero of the proved polynomial. -/
theorem eval_eq_zero {F : List (MvPolynomial V R)} {P : Fin F.length → MvPolynomial V R}
    {q : MvPolynomial V R} (h : IsProof F P q) {x : V → R}
    (hx : ∀ f ∈ F, MvPolynomial.eval x f = 0) : MvPolynomial.eval x q = 0 := by
  rw [← h, map_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [map_mul, hx _ (List.get_mem F i), zero_mul]

/-- Over nontrivial coefficients, a refutation leaves no common zero of the inputs: at every
point some input does not vanish. -/
theorem exists_eval_ne_zero [Nontrivial R] {F : List (MvPolynomial V R)}
    {P : Fin F.length → MvPolynomial V R} (h : IsProof F P 1) (x : V → R) :
    ∃ f ∈ F, MvPolynomial.eval x f ≠ 0 := by
  by_contra! hx
  simpa using h.eval_eq_zero hx

/-- If every input has degree at most `d₀`, an NS refutation has a replacement certificate
of no larger size and degree at most `d₀ * size F P`. This auxiliary bound is proved by
truncating the multipliers at a gap in their monomial degrees. -/
theorem exists_degree_le_mul_size {F : List (MvPolynomial V R)}
    {P : Fin F.length → MvPolynomial V R} (hP : IsProof F P 1) {d₀ : ℕ}
    (hd₀ : ∀ f ∈ F, f.totalDegree ≤ d₀) :
    ∃ Q, IsProof F Q 1 ∧ size F Q ≤ size F P ∧ degree F Q ≤ d₀ * size F P := by
  classical
  let T : Finset ℕ := Finset.univ.biUnion fun i =>
    if F.get i = 0 then ∅ else (P i).support.image Finsupp.degree
  have hcard : T.card ≤ size F P := by
    refine Finset.card_biUnion_le.trans ?_
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : F.get i = 0
    · simp only [hi, ite_true, Finset.card_empty, MvPolynomial.support_zero, zero_mul, le_refl]
    · simp only [hi, ite_false]
      have hpos : 1 ≤ (F.get i).support.card :=
        Finset.card_pos.mpr (MvPolynomial.support_nonempty.mpr hi)
      exact Finset.card_image_le.trans
        (by simpa using Nat.mul_le_mul_right (P i).support.card hpos)
  obtain ⟨D, hD, hgap⟩ := T.exists_gap_le_mul_card d₀
  have hD' : D ≤ d₀ * size F P := hD.trans (Nat.mul_le_mul_left d₀ hcard)
  have hgap' (i : Fin F.length) (hi : F.get i ≠ 0) (m) (hm : m ∈ (P i).support) :
      m.degree + (F.get i).totalDegree ≤ D ∨ D < m.degree := by
    have hmT : m.degree ∈ T := Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, by simp only [hi, ite_false]; exact Finset.mem_image_of_mem _ hm⟩
    exact (hgap _ hmT).imp_left
      ((Nat.add_le_add_left (hd₀ _ (List.get_mem ..)) _).trans ·)
  let Q : Fin F.length → MvPolynomial V R := fun i =>
    if F.get i = 0 then 0 else MvPolynomial.truncateTotalDegree D (P i)
  have hQmem (i : Fin F.length) (m : V →₀ ℕ) :
      m ∈ (Q i).support ↔ F.get i ≠ 0 ∧ m ∈ (P i).support ∧ m.degree ≤ D := by
    simp only [Q, List.get_eq_getElem]
    split_ifs with hi <;> simp [hi, MvPolynomial.support_truncateTotalDegree]
  refine ⟨Q, ?_, ?_, ?_⟩
  · change (∑ i, F.get i * Q i) = 1
    calc
      (∑ i, F.get i * Q i) =
          ∑ i, MvPolynomial.truncateTotalDegree D (F.get i * P i) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : F.get i = 0
        · simp only [Q, hi, ite_true, zero_mul, MvPolynomial.truncateTotalDegree_zero]
        · simpa only [Q, hi, ite_false] using
            (MvPolynomial.truncateTotalDegree_mul_of_gap D (F.get i) (P i) (hgap' i hi)).symm
      _ = MvPolynomial.truncateTotalDegree D (∑ i, F.get i * P i) :=
        (MvPolynomial.truncateTotalDegree_sum D Finset.univ _).symm
      _ = 1 := by rw [show (∑ i, F.get i * P i) = 1 from hP]; simp
  · exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _
      (Finset.card_le_card fun m hm => ((hQmem i m).mp hm).2.1)
  · simp only [degree, Finset.sup_le_iff, Finset.mem_univ, forall_const]
    intro i m hm
    obtain ⟨hi, hm, hdeg⟩ := (hQmem i m).mp hm
    have hlow := (hgap' i hi m hm).resolve_right (Nat.not_lt_of_ge hdeg)
    exact (Nat.add_comm _ _ ▸ hlow).trans hD'

end IsProof

/-- `F` has a Nullstellensatz refutation of size at most `s`. -/
@[expose] def RefutableInSize (F : List (MvPolynomial V R)) (s : ℕ) : Prop :=
  ∃ P, IsProof F P 1 ∧ size F P ≤ s

/-- `F` has a Nullstellensatz refutation of degree at most `d`. -/
@[expose] def RefutableInDegree (F : List (MvPolynomial V R)) (d : ℕ) : Prop :=
  ∃ P, IsProof F P 1 ∧ degree F P ≤ d

end Cslib.Logic.PL.NS
