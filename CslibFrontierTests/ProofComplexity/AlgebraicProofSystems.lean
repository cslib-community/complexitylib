/-
Copyright (c) 2026 Vincent Palma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.Nullstellensatz.PolynomialCalculus
public import CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.Nullstellensatz
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Certificates, simulations and coefficient assumptions for algebraic proof systems

Refutations over the natural-number semiring and a ring with zero divisors exercise the
generalized coefficient interface. Nonconstant refutations and a nonzero target exercise the
resource-preserving simulation and the removal of high-degree cancellation. Soundness shows that
an input system with a common zero has no refutation. The final check shows why the refutation
simulation, unlike the proof predicates, assumes nontrivial coefficients.
-/

public section

namespace Cslib.Logic.PL

open MvPolynomial

/-- NS certificates and both resource measures work over a semiring without subtraction. -/
example : NS.RefutableInSize ([1] : List (MvPolynomial Unit ℕ)) 1 ∧
    NS.RefutableInDegree ([1] : List (MvPolynomial Unit ℕ)) 0 := by
  constructor
  · refine ⟨fun _ => 1, ?_, ?_⟩
    · simp [NS.IsProof]
    · simp [NS.size, MvPolynomial.support_one]
  · refine ⟨fun _ => 1, ?_, ?_⟩
    · simp [NS.IsProof]
    · rw [NS.degree_le_iff]
      intro i _
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simp

local instance : Fact (1 < 6) := ⟨by decide⟩

/-- PC proofs and both resource measures work over a nontrivial ring with zero divisors. -/
example : PC.RefutableInSize ([1] : List (MvPolynomial Unit (ZMod 6))) 1 ∧
    PC.RefutableInDegree ([1] : List (MvPolynomial Unit (ZMod 6))) 0 := by
  constructor
  · refine ⟨[1], .mem .nil (by simp), by simp, ?_⟩
    simp [PC.size, MvPolynomial.support_one]
  · refine ⟨[1], .mem .nil (by simp), by simp, ?_⟩
    simp [PC.degree]

/-- A single variable vanishes at `0`, so by soundness it has neither an NS nor a PC
refutation, over any nontrivial semiring. -/
example {R : Type*} [CommSemiring R] [Nontrivial R] :
    (∀ d, ¬NS.RefutableInDegree ([X ()] : List (MvPolynomial Unit R)) d) ∧
    ∀ d, ¬PC.RefutableInDegree ([X ()] : List (MvPolynomial Unit R)) d := by
  constructor
  · rintro d ⟨P, hP, -⟩
    obtain ⟨f, hf, hne⟩ := hP.exists_eval_ne_zero (fun _ => 0)
    simp_all
  · rintro d ⟨ls, hls, h1, -⟩
    obtain ⟨f, hf, hne⟩ := hls.exists_eval_ne_zero h1 (fun _ => 0)
    simp_all

private theorem quadratic_ns_certificate :
    NS.IsProof ([X (), 1 - X () ^ 2] : List (MvPolynomial Unit (ZMod 6)))
      (fun i => if i = 0 then X () else 1) 1 ∧
    NS.size ([X (), 1 - X () ^ 2] : List (MvPolynomial Unit (ZMod 6)))
      (fun i => if i = 0 then X () else 1) ≤ 3 ∧
    NS.degree ([X (), 1 - X () ^ 2] : List (MvPolynomial Unit (ZMod 6)))
      (fun i => if i = 0 then X () else 1) ≤ 2 := by
  have hcard : ((1 - X () ^ 2) : MvPolynomial Unit (ZMod 6)).support.card ≤ 2 := by
    exact (Finset.card_le_card (support_sub Unit 1 (X () ^ 2))).trans
      ((Finset.card_union_le _ _).trans (by simp [support_one, support_X_pow]))
  refine ⟨?_, ?_, ?_⟩
  · simp [NS.IsProof, Fin.sum_univ_succ, pow_two]
  · simpa [NS.size, Fin.sum_univ_succ, support_one, support_X_pow, support_X] using
      Nat.add_le_add_left hcard 1
  · rw [NS.degree_le_iff]
    intro i _
    fin_cases i
    · simp
    · change (1 - X () ^ 2 : MvPolynomial Unit (ZMod 6)).totalDegree +
        (1 : MvPolynomial Unit (ZMod 6)).totalDegree ≤ 2
      rw [totalDegree_one, add_zero]
      calc
        _ ≤ max (1 : MvPolynomial Unit (ZMod 6)).totalDegree
            (X () ^ 2 : MvPolynomial Unit (ZMod 6)).totalDegree := totalDegree_sub _ _
        _ = 2 := by simp

/-- A nonconstant certificate over a ring with zero divisors converts to a single PC proof
meeting both resource bounds, and that proof converts back to an NS certificate. -/
example : ∃ ls : List (MvPolynomial Unit (ZMod 6)),
    PC.IsProof [X (), 1 - X () ^ 2] ls ∧ 1 ∈ ls ∧
      PC.size ls ≤ 18 ∧ PC.degree ls ≤ 2 ∧
      ∃ Q : Fin 2 → MvPolynomial Unit (ZMod 6),
        NS.IsProof [X (), 1 - X () ^ 2] Q 1 := by
  obtain ⟨hP, hs, hd⟩ := quadratic_ns_certificate
  obtain ⟨ls, hls, h1, hs', hd'⟩ := PC.exists_refutation_of_ns hP hs hd
  exact ⟨ls, hls, h1, hs', hd', NS.exists_isProof_of_pc hls h1⟩

/-- The simulation also proves a nonconstant nonzero target from a satisfiable input system,
over a semiring without subtraction, preserving both resource bounds in the same proof. -/
example : ∃ ls : List (MvPolynomial Unit ℕ),
    PC.IsProof [X ()] ls ∧ X () ^ 2 ∈ ls ∧ PC.size ls ≤ 4 ∧ PC.degree ls ≤ 2 := by
  have hP : NS.IsProof [X ()] (fun _ => X ()) (X () ^ 2 : MvPolynomial Unit ℕ) := by
    simp [NS.IsProof, pow_two]
  have hs : NS.size [X ()] (fun _ => (X () : MvPolynomial Unit ℕ)) ≤ 1 := by
    simp [NS.size, support_X]
  have hd : NS.degree [X ()] (fun _ => (X () : MvPolynomial Unit ℕ)) ≤ 2 := by
    simp [NS.degree, support_X]
  exact PC.exists_isProof_of_ns hP (by simp) hs hd

/-- High-degree cancellation between nonzero inputs can be discarded without increasing size. -/
example : ∃ Q : Fin 3 → MvPolynomial Unit ℤ,
    NS.IsProof [1, 1, 1] Q 1 ∧ NS.size [1, 1, 1] Q ≤ 3 ∧
      NS.degree [1, 1, 1] Q ≤ 0 := by
  let P : Fin 3 → MvPolynomial Unit ℤ := ![1, X () ^ 7, -(X () ^ 7)]
  have hP : NS.IsProof [1, 1, 1] P 1 := by
    simp [NS.IsProof, P, Fin.sum_univ_succ]
  have hs : NS.size [1, 1, 1] P ≤ 3 := by
    simp [NS.size, P, Fin.sum_univ_succ, support_one, support_X_pow, support_neg]
  obtain ⟨Q, hQ, hs', hd⟩ := hP.exists_degree_le_mul_size (d₀ := 0) (by simp)
  exact ⟨Q, hQ, hs'.trans hs, by simpa using hd⟩

/-- The size-only simulation accepts certificates containing unused high-degree multipliers. -/
example : PC.RefutableInSize ([1, 0] : List (MvPolynomial Unit ℕ)) 2 := by
  apply PC.RefutableInSize.of_ns (s := 1) (d₀ := 0) (by simp)
  refine ⟨fun i => if i = 0 then 1 else X () ^ 7, ?_, ?_⟩
  · simp [NS.IsProof, Fin.sum_univ_succ]
  · simp [NS.size, Fin.sum_univ_succ, support_one]

/-- Unused input axioms do not increase NS degree. -/
example :
    NS.degree ([X () ^ 7] : List (MvPolynomial Unit ℕ)) (fun _ => 0) = 0 := by
  simp [NS.degree, MvPolynomial.support_zero]

/-- The chosen NS convention still counts a nonzero multiplier of a zero input polynomial. -/
example :
    NS.degree ([0] : List (MvPolynomial Unit ℕ)) (fun _ => X () ^ 7) = 7 := by
  simp [NS.degree, MvPolynomial.support_X_pow]

/-- PC size counts repeated lines, while degree takes a maximum and has an empty-list value. -/
example : PC.size ([1, 1] : List (MvPolynomial Unit ℕ)) = 2 ∧
    PC.degree ([1, X () ^ 7, 1] : List (MvPolynomial Unit ℕ)) = 7 ∧
    PC.degree ([] : List (MvPolynomial Unit ℕ)) = 0 := by
  simp [PC.size, PC.degree, MvPolynomial.support_one,
    MvPolynomial.totalDegree_X_pow]

/-- Over the trivial ring the empty input list has an NS refutation but no PC refutation, so the
NS-to-PC simulation needs nontrivial coefficients. -/
example : NS.RefutableInDegree ([] : List (MvPolynomial Unit Unit)) 0 ∧
    ¬PC.RefutableInDegree ([] : List (MvPolynomial Unit Unit)) 0 := by
  have hnil (ls : List (MvPolynomial Unit Unit)) (hls : PC.IsProof [] ls) :
      ls = [] := by
    induction hls with
    | nil => rfl
    | mem _ hp => simp at hp
    | linear _ _ _ hp _ ih => subst ih; simp at hp
    | mulVar _ _ hp ih => subst ih; simp at hp
  refine ⟨⟨fun _ => 0, Subsingleton.elim _ _, by simp [NS.degree]⟩, ?_⟩
  rintro ⟨ls, hls, h1, -⟩
  rw [hnil ls hls] at h1
  cases h1

end Cslib.Logic.PL
