/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Algebraic.Nullstellensatz.Proof

/-!
# Nullstellensatz certificates from finite combinations

A Nullstellensatz proof (`Cslib.Logic.PL.NS.IsProof`) assigns one multiplier to each position of
the input list. Certificates are often easier to write as a finite sum `∑ t ∈ s, f t * g t` with
every `f t` an input, where the same input may occur for several `t`.
`Cslib.Logic.PL.NS.exists_isProof_of_sum` turns such a sum into a certificate. If every term with
a nonzero multiplier has `deg (f t) + deg (g t) ≤ d`, the certificate has degree at most `d`
(`Cslib.Logic.PL.NS.degree`). Each multiplier `g t` is added at one position holding `f t`.
In particular, refutability in degree `d` is monotone in the input list
(`Cslib.Logic.PL.NS.RefutableInDegree.mono`).

## Main results

* `Cslib.Logic.PL.NS.exists_isProof_of_sum`: a certificate from a finite combination of inputs.
* `Cslib.Logic.PL.NS.RefutableInDegree.mono`: monotonicity in the inputs and the degree.
-/

public section

namespace Cslib.Logic.PL.NS

open MvPolynomial

variable {V R : Type*} [CommSemiring R]

/-- **A certificate from a finite combination.** If `q = ∑ t ∈ s, f t * g t` with every `f t` in
`F`, and every term with `g t ≠ 0` has `deg (f t) + deg (g t) ≤ d`, then `q` has a
Nullstellensatz proof from `F` of degree at most `d`. -/
theorem exists_isProof_of_sum {κ : Type*} {F : List (MvPolynomial V R)} (s : Finset κ)
    (f g : κ → MvPolynomial V R) (hf : ∀ t ∈ s, f t ∈ F) {d : ℕ}
    (hd : ∀ t ∈ s, g t ≠ 0 → (f t).totalDegree + (g t).totalDegree ≤ d) :
    ∃ P, IsProof F P (∑ t ∈ s, f t * g t) ∧ degree F P ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_, ?_⟩
    · simp [IsProof]
    · rw [degree_le_iff]
      intro i hi
      exact absurd rfl hi
  | insert t s hts ih =>
    obtain ⟨P, hP, hPd⟩ := ih (fun t' ht' => hf t' (Finset.mem_insert_of_mem ht'))
      (fun t' ht' => hd t' (Finset.mem_insert_of_mem ht'))
    obtain ⟨i, hi⟩ := List.get_of_mem (hf t (Finset.mem_insert_self t s))
    have hdt := hd t (Finset.mem_insert_self t s)
    refine ⟨fun j => (Pi.single i (g t) : Fin F.length → MvPolynomial V R) j + P j, ?_, ?_⟩
    · have h1 : IsProof F (Pi.single i (g t)) (F.get i * g t) := by
        simp [IsProof, Pi.single_apply]
      have h := h1.add hP
      rw [Finset.sum_insert hts]
      rwa [hi] at h
    · rw [degree_le_iff] at hPd ⊢
      intro j hj
      by_cases hji : j = i
      · subst hji
        rw [Pi.single_eq_same] at hj ⊢
        rw [hi]
        by_cases hg : g t = 0
        · rw [hg, zero_add] at hj ⊢
          have := hPd j hj
          rwa [hi] at this
        by_cases hPj : P j = 0
        · rw [hPj, add_zero]
          exact hdt hg
        have h2 := hPd j hPj
        rw [hi] at h2
        have h3 := hdt hg
        have := totalDegree_add (g t) (P j)
        omega
      · rw [Pi.single_eq_of_ne hji, zero_add] at hj ⊢
        exact hPd j hj

/-- Nullstellensatz refutability in degree `d` is monotone in the input list and in `d`. -/
theorem RefutableInDegree.mono {F G : List (MvPolynomial V R)} {d e : ℕ}
    (h : RefutableInDegree F d) (hFG : F ⊆ G) (hde : d ≤ e) : RefutableInDegree G e := by
  obtain ⟨P, hP, hd⟩ := h
  rw [degree_le_iff] at hd
  obtain ⟨Q, hQ, hQd⟩ := exists_isProof_of_sum (F := G) Finset.univ (fun i => F.get i) P
    (fun i _ => hFG (List.get_mem F i)) (fun i _ hi => (hd i hi).trans hde)
  exact ⟨Q, hQ.trans hP, hQd⟩

end Cslib.Logic.PL.NS
