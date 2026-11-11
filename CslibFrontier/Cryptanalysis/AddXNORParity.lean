/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORCounting
public import CslibFrontier.Foundations.Data.BitString.Parity
public import CslibFrontier.Foundations.Data.BitString.Weight
import Mathlib.Algebra.BigOperators.Fin

/-!
# Parity classes and Hamming geometry of Add/XNOR solutions

[WangLvShenZhang2027], Corollary 1 (PDF p. 7) and Corollary 3
(PDF p. 14): at positive width all solutions lie in one operator-parity class,
which has exactly half the operator words when at least one operator is free.
Every solution pair has even Hamming distance. These are counting/geometry
statements; a parity restriction alone is not an algorithm runtime certificate.

## Main results

* `parity_class_card`, `solutionCount_le_half`: exact permitted-class size and solution bound.
* `solution_hamming_even`: even Hamming distance between every pair of zero solutions.
-/

public section

open scoped BigOperators

namespace Cslib.Cryptanalysis.AddXNOR

/-- The chain's operator parity is the existing Boolean-function parity. -/
theorem xnorParity_steps {m q : ℕ} (bs : Fin q → Bool) (as : Fin q → BitVec m) :
    xnorParity (steps bs as) = Cslib.parity q bs := by
  rw [Cslib.parity, Cslib.parityOn_eq_sum]
  induction q with
  | zero => simp [steps, xnorParity, Bool.zero_eq_false]
  | succ q ih =>
    simp only [steps, List.ofFn_succ, xnorParity, Fin.sum_univ_succ]
    change bs 0 + xnorParity (steps (fun i => bs i.succ) (fun i => as i.succ)) = _
    rw [ih]

/-- The operand-dependent parity class containing every zero solution. -/
@[expose] def requiredParity {m q : ℕ} (as : Fin q → BitVec m) (s : BitVec m) : Bool :=
  s.getLsbD 0 ^^ (operandsXor (steps (fun _ => false) as)).getLsbD 0

private theorem operandsXor_steps {m q : ℕ} (bs cs : Fin q → Bool) (as : Fin q → BitVec m) :
    operandsXor (steps bs as) = operandsXor (steps cs as) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [steps, List.ofFn_succ, operandsXor]
    congr 1
    exact ih _ _ _

/-- Actual full-width evaluation forces this class, without any sampling hypothesis. -/
theorem solution_parity_class {m q : ℕ} (hm : 0 < m) (bs : Fin q → Bool)
    (as : Fin q → BitVec m) (s : BitVec m) (h : eval (steps bs as) s = 0) :
    Cslib.parity q bs = requiredParity as s := by
  have hp := solution_parity hm (steps bs as) s h
  rw [xnorParity_steps, operandsXor_steps bs (fun _ => false) as] at hp
  exact hp

/-- Exactly half the operator strings have the required parity, including an
unsatisfiable instance whose permitted class contains no solution. -/
theorem parity_class_card {m q : ℕ} (hq : 0 < q) (as : Fin q → BitVec m) (s : BitVec m) :
    (Finset.univ.filter fun bs : Fin q → Bool => Cslib.parity q bs = requiredParity as s).card =
      2 ^ (q - 1) := by
  exact (Cslib.card_filter_parityOn_eq
    (s := Finset.univ) ⟨⟨0, hq⟩, Finset.mem_univ _⟩ (requiredParity as s)).trans (by simp)

/-- No positive-width instance has more than half of all operator strings as solutions. -/
theorem solutionCount_le_half {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (as : Fin q → BitVec m) (s : BitVec m) : solutionCount as s 0 ≤ 2 ^ (q - 1) := by
  change (∑ bs : Fin q → Bool, if eval (steps bs as) s = 0 then 1 else 0) ≤ _
  rw [← Finset.card_filter, ← parity_class_card hq as s]
  apply Finset.card_le_card
  intro bs hbs
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
    solution_parity_class hm bs as s (Finset.mem_filter.1 hbs).2⟩

/-- Every pair of zero solutions has even Hamming distance (hence never distance one). -/
theorem solution_hamming_even {m q : ℕ} (hm : 0 < m) (bs cs : Fin q → Bool)
    (as : Fin q → BitVec m) (s : BitVec m)
    (hb : eval (steps bs as) s = 0) (hc : eval (steps cs as) s = 0) :
    Even (hammingDist bs cs) := by
  have he : Cslib.parity q bs = Cslib.parity q cs :=
    (solution_parity_class hm bs as s hb).trans (solution_parity_class hm cs as s hc).symm
  have hz : Cslib.parity q (bs + cs) = false := by
    rw [Cslib.parity, Cslib.parityOn_add]
    change (Cslib.parity q bs ^^ Cslib.parity q cs) = false
    rw [he, Bool.xor_self]
  rw [Cslib.BitString.hammingDist_eq_weight_add, Nat.even_iff]
  change (Finset.univ.filter fun i => (bs + cs) i = true).card % 2 = 0
  change decide ((Finset.univ.filter fun i => (bs + cs) i = true).card % 2 = 1) = false at hz
  simp only [decide_eq_false_iff_not] at hz
  omega

end Cslib.Cryptanalysis.AddXNOR
