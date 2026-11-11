/-
Copyright (c) 2026 Vincent Palma, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.Proof

/-!
# Composing polynomial calculus proofs

`PC.IsProof.comp` continues a proof with a derivation whose inputs already occur among its
lines. The old lines are shared, rather than copied once for each use. Repeated input lines in
the continuation are justified by the scalar linear-combination rule.

`PC.IsProof.exists_prod_mul` applies the existing bounded monomial-multiplication construction
to a line of a proof, preserving all its old lines and bounding the additional monomial count.
These are the proof-composition operations used by the resolution-to-PCR simulation.

## Main results

* `Cslib.Logic.PL.PC.degree_append`: degree of concatenated proof lists.
* `Cslib.Logic.PL.PC.IsProof.comp`: substitute already proved inputs into a derivation.
* `Cslib.Logic.PL.PC.IsProof.exists_prod_mul`: extend a proof by a product of variables.
-/

public section

namespace Cslib.Logic.PL.PC

open MvPolynomial

variable {V R : Type*} [CommSemiring R]

/-- The degree of concatenated proof lists is the larger of their degrees. -/
@[simp] theorem degree_append (ls ls' : List (MvPolynomial V R)) :
    degree (ls ++ ls') = max (degree ls) (degree ls') := by
  induction ls with
  | nil => simp
  | cons p ls ih => simp [ih, max_assoc]

/-- Continue a proof with a derivation whose inputs already occur in it. Its old lines remain
as a shared suffix, and its length and size are exactly those of the concatenation. -/
theorem IsProof.comp {F G ls ls' : List (MvPolynomial V R)}
    (h : IsProof F ls) (h' : IsProof G ls') (hG : G ⊆ ls) : IsProof F (ls' ++ ls) := by
  induction h' with
  | nil => exact h
  | @mem ms p _ hp ih =>
    simpa using ih.linear 1 0 (List.mem_append_right ms (hG hp))
      (List.mem_append_right ms (hG hp))
  | linear a b _ hp hq ih =>
    exact ih.linear a b (List.mem_append_left _ hp) (List.mem_append_left _ hq)
  | mulVar v _ hp ih => exact ih.mulVar v (List.mem_append_left _ hp)

/-- Multiply an already proved line by the variables indexed by a finite set, preserving all
old lines. The extension adds at most `(#s + 1) * p.support.card` monomials: it repeats `p`
once and then multiplies by one variable at a time. Repeated variables in `v` are allowed. -/
theorem IsProof.exists_prod_mul {F ls : List (MvPolynomial V R)} {p : MvPolynomial V R}
    (h : IsProof F ls) (hp : p ∈ ls) {ι : Type*} (s : Finset ι) (v : ι → V) :
    ∃ ms, IsProof F ms ∧ ls ⊆ ms ∧ (∏ i ∈ s, X (v i)) * p ∈ ms ∧
      size ms ≤ size ls + (s.card + 1) * p.support.card ∧
      degree ms ≤ max (degree ls) (p.totalDegree + s.card) := by
  classical
  let m : V →₀ ℕ := ∑ i ∈ s, Finsupp.single (v i) 1
  have hm : m.degree = s.card := by simp [m]
  obtain ⟨ns, hns, hn, hs, hd⟩ :=
    exists_isProof_monomial_mul (F := [p]) (List.mem_singleton_self p) m
  have hprod : (monomial m (1 : R)) = ∏ i ∈ s, X (v i) := by
    rw [show m = ∑ i ∈ s, Finsupp.single (v i) 1 from rfl, monomial_sum_one]
    rfl
  refine ⟨ns ++ ls, h.comp hns ?_, List.subset_append_right _ _, ?_, ?_, ?_⟩
  · intro q hq
    obtain rfl := List.mem_singleton.1 hq
    exact hp
  · rw [← hprod]
    exact List.mem_append_left _ hn
  · rw [size_append]
    rw [hm] at hs
    omega
  · rw [hm] at hd
    rw [degree_append]
    exact max_le (hd.trans (le_max_right _ _)) (le_max_left _ _)

end Cslib.Logic.PL.PC
