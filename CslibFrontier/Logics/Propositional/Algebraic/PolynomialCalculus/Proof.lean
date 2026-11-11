/-
Copyright (c) 2026 Vincent Palma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Finsupp.Weight
import CslibFrontier.Foundations.Data.MvPolynomial.Support

/-!
# Polynomial Calculus proofs

A *Polynomial Calculus proof* from a list `F` of input polynomials is a sequence in which each
line is an input, a scalar linear combination of two earlier lines, or an earlier line
multiplied by a variable (`Cslib.Logic.PL.PC.IsProof`). Proofs are listed from
their last line to their first, so that a new line is added in front. A *refutation* contains
the polynomial `1`. Proofs are sound: every line vanishes at every common zero of the inputs.

The *size* is the sum of the numbers of supported monomials across all lines, counting repeated
lines separately. The *degree* is the largest total degree of a line, with value `0` for the
empty proof. Polynomials are formal.

## Relation to the source

[de Rezende et al., §8.1, p. 217][DeRezendeEtAl2021] works over a field, with the same two rules
(scalar linear combination and multiplication by a variable), the same size `∑ i, ‖p i‖` and the
same degree; a refutation there ends with `1`, while here it contains `1`, which is equivalent
after discarding the lines above it. Coefficients here lie in an arbitrary commutative semiring:
the rules use only addition and multiplication. Over the trivial semiring every nonempty input
list is refutable.

Proofs from the same inputs concatenate. Derivations of monomial multiples and nonzero finite
linear combinations come with size and degree bounds, providing the constructions used to
simulate Nullstellensatz refutations.

## Main definitions

* `Cslib.Logic.PL.PC.IsProof`: polynomial calculus proofs.
* `Cslib.Logic.PL.PC.size`, `Cslib.Logic.PL.PC.degree`: size
  and degree of a proof.
* `Cslib.Logic.PL.PC.RefutableInSize`,
  `Cslib.Logic.PL.PC.RefutableInDegree`: refutability with a bound on size or
  degree.

## Main results

* `Cslib.Logic.PL.PC.degree_le_iff`: characterize a degree bound by the degrees
  of the lines.
* `Cslib.Logic.PL.PC.IsProof.append`: concatenate proofs from the same input
  system.
* `Cslib.Logic.PL.PC.IsProof.eval_eq_zero`,
  `Cslib.Logic.PL.PC.IsProof.exists_eval_ne_zero`: soundness.
* `Cslib.Logic.PL.PC.exists_isProof_monomial_mul`: derive a monomial multiple of
  an input, with bounds on proof size and degree.
* `Cslib.Logic.PL.PC.exists_isProof_sum`: derive a nonzero linear combination
  from proofs of its nonzero input polynomials, with bounds on proof size and degree.

## References

* [S. F. de Rezende, M. Göös, J. Nordström, T. Pitassi, R. Robere, D. Sokolov,
  *Automating Algebraic Proof Systems Is NP-Hard*, STOC 2021, §8.1, p. 217][DeRezendeEtAl2021]
-/

public section

namespace Cslib.Logic.PL.PC

variable {V R : Type*} [CommSemiring R]

open MvPolynomial

/-! ### Complexity measures -/

/-- The size of a PC proof: the sum of support sizes across all lines, counting
repeated lines separately. -/
@[expose] def size (ls : List (MvPolynomial V R)) : ℕ :=
  (ls.map fun p => p.support.card).sum

/-- The degree of a PC proof: the maximum total degree of a line, with value `0` for the
empty list. -/
@[expose] def degree (ls : List (MvPolynomial V R)) : ℕ :=
  (ls.map MvPolynomial.totalDegree).foldr max 0

/-- A PC proof has degree at most `d` exactly when every line has total degree at most `d`. -/
theorem degree_le_iff {ls : List (MvPolynomial V R)} {d : ℕ} :
    degree ls ≤ d ↔ ∀ p ∈ ls, p.totalDegree ≤ d := by
  constructor
  · intro h p hp
    exact (List.le_max_of_le (List.mem_map.mpr ⟨p, hp, rfl⟩) le_rfl).trans h
  · intro h
    apply List.max_le_of_forall_le
    simpa only [List.forall_mem_map] using h

/-! ### Proofs -/

/-- A **Polynomial Calculus proof** from `F`, listed from its last line to its first:
every line is an input from `F`, a scalar linear combination of two lines below it, or a line
below it multiplied by a variable. -/
inductive IsProof (F : List (MvPolynomial V R)) : List (MvPolynomial V R) → Prop
  /-- The empty proof. -/
  | nil : IsProof F []
  /-- An axiom of `F` is a new line. -/
  | mem {ls p} (h : IsProof F ls) (hp : p ∈ F) :
      IsProof F (p :: ls)
  /-- A linear combination of two earlier lines. -/
  | linear {ls p q} (a b : R) (h : IsProof F ls) (hp : p ∈ ls) (hq : q ∈ ls) :
      IsProof F ((C a * p + C b * q) :: ls)
  /-- Multiplication of an earlier line by a variable. -/
  | mulVar {ls p} (v : V) (h : IsProof F ls) (hp : p ∈ ls) :
      IsProof F ((X v * p) :: ls)

/-- The empty proof has size zero. -/
@[simp] theorem size_nil : size ([] : List (MvPolynomial V R)) = 0 := rfl

/-- Adding a line adds its size. -/
@[simp] theorem size_cons (p : MvPolynomial V R) (ls : List (MvPolynomial V R)) :
    size (p :: ls) = p.support.card + size ls := rfl

/-- Sizes add under concatenation. -/
@[simp] theorem size_append (ls ls' : List (MvPolynomial V R)) :
    size (ls ++ ls') = size ls + size ls' := by simp [size]

/-- The empty proof has degree zero. -/
@[simp] theorem degree_nil : degree ([] : List (MvPolynomial V R)) = 0 := rfl

/-- Adding a line takes the maximum of its degree and the previous proof's degree. -/
@[simp] theorem degree_cons (p : MvPolynomial V R) (ls : List (MvPolynomial V R)) :
    degree (p :: ls) = max p.totalDegree (degree ls) := rfl

namespace IsProof

/-- A proof placed above another proof from the same input system gives a proof. -/
theorem append {F ls ls' : List (MvPolynomial V R)}
    (h : IsProof F ls) (h' : IsProof F ls') : IsProof F (ls ++ ls') := by
  induction h with
  | nil => exact h'
  | mem _ hp ih => exact ih.mem hp
  | linear a b _ hp hq ih =>
    exact ih.linear a b (List.mem_append_left _ hp) (List.mem_append_left _ hq)
  | mulVar v _ hp ih => exact ih.mulVar v (List.mem_append_left _ hp)

/-- **Soundness.** Every line of a proof vanishes at every common zero of the inputs. -/
theorem eval_eq_zero {F ls : List (MvPolynomial V R)} (h : IsProof F ls) {x : V → R}
    (hx : ∀ f ∈ F, eval x f = 0) : ∀ p ∈ ls, eval x p = 0 := by
  induction h with
  | nil => simp
  | mem _ hp ih => exact List.forall_mem_cons.mpr ⟨hx _ hp, ih⟩
  | linear a b _ hp hq ih =>
    exact List.forall_mem_cons.mpr ⟨by simp [ih _ hp, ih _ hq], ih⟩
  | mulVar v _ hp ih => exact List.forall_mem_cons.mpr ⟨by simp [ih _ hp], ih⟩

/-- Over nontrivial coefficients, a refutation leaves no common zero of the inputs: at every
point some input does not vanish. -/
theorem exists_eval_ne_zero [Nontrivial R] {F ls : List (MvPolynomial V R)} (h : IsProof F ls)
    (h1 : 1 ∈ ls) (x : V → R) : ∃ f ∈ F, eval x f ≠ 0 := by
  by_contra! hx
  simpa using h.eval_eq_zero hx 1 h1

end IsProof

/-- A monomial multiple of an input polynomial has a PC proof of size at most
`(m.degree + 1) * f.support.card` and degree at most `f.totalDegree + m.degree`. The proof
starts with `f` and multiplies by variables. -/
theorem exists_isProof_monomial_mul {F : List (MvPolynomial V R)}
    {f : MvPolynomial V R} (hf : f ∈ F) (m : V →₀ ℕ) :
    ∃ ls, IsProof F ls ∧ monomial m 1 * f ∈ ls ∧
      size ls ≤ (m.degree + 1) * f.support.card ∧ degree ls ≤ f.totalDegree + m.degree := by
  classical
  induction m using Finsupp.induction with
  | zero =>
    refine ⟨[f], IsProof.nil.mem hf, ?_, ?_, ?_⟩ <;> simp
  | single_add v k m _ _ ih =>
    have hm (n : ℕ) : ∃ ls, IsProof F ls ∧
        monomial (Finsupp.single v n + m) 1 * f ∈ ls ∧
        size ls ≤ ((Finsupp.single v n + m).degree + 1) * f.support.card ∧
        degree ls ≤ f.totalDegree + (Finsupp.single v n + m).degree := by
      induction n with
      | zero => simpa using ih
      | succ n ihn =>
        obtain ⟨ls, hls, hmem, hs, hd⟩ := ihn
        let q := monomial (Finsupp.single v n + m) 1 * f
        have heq : monomial (Finsupp.single v (n + 1) + m) 1 * f = X v * q := by
          rw [show Finsupp.single v (n + 1) + m =
              Finsupp.single v 1 + (Finsupp.single v n + m) by
                rw [Finsupp.single_add]; abel,
            monomial_single_add, pow_one, mul_assoc]
        have hcard : (X v * q).support.card ≤ f.support.card := by
          rw [← heq]
          exact card_support_monomial_mul_le _ _ _
        refine ⟨X v * q :: ls, hls.mulVar v hmem, ?_, ?_, ?_⟩
        · rw [heq]; exact List.mem_cons_self
        · simp only [size_cons, map_add, Finsupp.degree_single, Nat.add_mul, Nat.one_mul]
            at hs ⊢
          omega
        · rw [degree_cons, max_le_iff]
          constructor
          · rw [← heq]
            have hmono : (monomial (Finsupp.single v (n + 1) + m) (1 : R)).totalDegree ≤
                (Finsupp.single v (n + 1) + m).degree := totalDegree_monomial_le _ _
            exact (totalDegree_mul _ _).trans
              ((Nat.add_le_add_right hmono _).trans_eq (Nat.add_comm _ _))
          · simp only [map_add, Finsupp.degree_single] at hd ⊢
            omega
    exact hm k

/-- Derive the nonzero sum `∑ i ∈ t, C (a i) * p i` in one PC proof of degree at most `d`
and size at most `(∑ i ∈ t, w i) ^ 2 + ∑ i ∈ t, c i`, given support bounds `w i`
and proofs of size at most `c i` and degree at most `d` for every nonzero `p i` in `t`. -/
theorem exists_isProof_sum {ι : Type*} {F : List (MvPolynomial V R)}
    (t : Finset ι) (p : ι → MvPolynomial V R) (a : ι → R) (w c : ι → ℕ) (d : ℕ)
    (hw : ∀ i ∈ t, (p i).support.card ≤ w i)
    (hp : ∀ i ∈ t, p i ≠ 0 → ∃ ls, IsProof F ls ∧ p i ∈ ls ∧
      size ls ≤ c i ∧ degree ls ≤ d)
    (hne : ∑ i ∈ t, C (a i) * p i ≠ 0) :
    ∃ ls, IsProof F ls ∧ (∑ i ∈ t, C (a i) * p i) ∈ ls ∧
      size ls ≤ (∑ i ∈ t, w i) ^ 2 + ∑ i ∈ t, c i ∧ degree ls ≤ d := by
  classical
  have hscale (i : ι) : (C (a i) * p i).support.card ≤ (p i).support.card := by
    rw [C_mul']
    exact Finset.card_le_card support_smul
  have hsum (u : Finset ι) (hu : ∀ i ∈ u, (p i).support.card ≤ w i) :
      (∑ i ∈ u, C (a i) * p i).support.card ≤ ∑ i ∈ u, w i := by
    exact (Finset.card_le_card support_sum).trans
      (Finset.card_biUnion_le.trans
        (Finset.sum_le_sum fun i hi => (hscale i).trans (hu i hi)))
  induction t using Finset.induction with
  | empty => simp at hne
  | @insert i t hit ih =>
    have hwt : ∀ j ∈ t, (p j).support.card ≤ w j :=
      fun j hj => hw j (Finset.mem_insert_of_mem hj)
    have hpt (j) (hj : j ∈ t) := hp j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hit] at hne ⊢
    rw [Finset.sum_insert hit, Finset.sum_insert hit]
    by_cases hpi : p i = 0
    · simp only [hpi, mul_zero, zero_add] at hne ⊢
      obtain ⟨ls, hls, hmem, hs, hd⟩ := ih hwt hpt hne
      refine ⟨ls, hls, hmem, hs.trans ?_, hd⟩
      exact Nat.add_le_add (Nat.pow_le_pow_left (by omega) 2) (by omega)
    have hpos : 1 ≤ w i :=
      (Finset.one_le_card.mpr (support_nonempty.mpr hpi)).trans
        (hw i (Finset.mem_insert_self i t))
    have hsq : (∑ j ∈ t, w j) ^ 2 + (w i + ∑ j ∈ t, w j) ≤
        (w i + ∑ j ∈ t, w j) ^ 2 := by
      have := Nat.mul_le_mul_right (w i + ∑ j ∈ t, w j) hpos
      simp only [one_mul, pow_two, Nat.add_mul, Nat.mul_add] at this ⊢
      omega
    obtain ⟨ls, hls, hmem, hs, hd⟩ := hp i (Finset.mem_insert_self i t) hpi
    have hdpi : (C (a i) * p i).totalDegree ≤ d :=
      (totalDegree_mul _ _).trans (by simpa using degree_le_iff.mp hd _ hmem)
    have hcard : (C (a i) * p i + ∑ j ∈ t, C (a j) * p j).support.card ≤
        w i + ∑ j ∈ t, w j := by
      simpa only [Finset.sum_insert hit] using hsum (insert i t) hw
    by_cases hzero : ∑ j ∈ t, C (a j) * p j = 0
    · refine ⟨C (a i) * p i :: ls, ?_, ?_, ?_, ?_⟩
      · simpa using hls.linear (a i) 0 hmem hmem
      · simp [hzero]
      · simp only [size_cons]
        have hc : (C (a i) * p i).support.card ≤ w i :=
          (hscale i).trans (hw i (Finset.mem_insert_self i t))
        omega
      · exact max_le hdpi hd
    · obtain ⟨ls', hls', hmem', hs', hd'⟩ := ih hwt hpt hzero
      refine ⟨(C (a i) * p i + ∑ j ∈ t, C (a j) * p j) :: (ls ++ ls'), ?_,
        List.mem_cons_self, ?_, ?_⟩
      · simpa using (hls.append hls').linear (a i) 1
          (List.mem_append_left _ hmem) (List.mem_append_right _ hmem')
      · rw [size_cons, size_append]
        omega
      · rw [degree_cons, max_le_iff]
        constructor
        · exact (totalDegree_add _ _).trans
            (max_le hdpi (degree_le_iff.mp hd' _ hmem'))
        · exact degree_le_iff.mpr (List.forall_mem_append.mpr
            ⟨degree_le_iff.mp hd, degree_le_iff.mp hd'⟩)

/-- `F` has a Polynomial Calculus refutation of size at most `s`. -/
@[expose] def RefutableInSize (F : List (MvPolynomial V R)) (s : ℕ) : Prop :=
  ∃ ls, IsProof F ls ∧ 1 ∈ ls ∧ size ls ≤ s

/-- `F` has a Polynomial Calculus refutation of degree at most `d`. -/
@[expose] def RefutableInDegree (F : List (MvPolynomial V R)) (d : ℕ) : Prop :=
  ∃ ls, IsProof F ls ∧ 1 ∈ ls ∧ degree ls ≤ d

end Cslib.Logic.PL.PC
