/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORChain
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Uniform solution counts and planted Add/XNOR instances

[WangLvShenZhang2027], Propositions 1–2 (PDF p. 8). All words,
including the initial word, are independently uniform; operator strings are
indexed by all functions `Fin q → Bool`. Counts retain distinct operator strings
even when their evaluations coincide. The planting operation below solves for
the initial word by actual inverse evaluation. Its exact instance mass is the
same size-biased law as the manuscript's final-operand planting, not a claim
that uniform and planted instances have the same distribution.

## Main definitions

* `solutionCount`: count of distinct solving operator strings.
* `plantedLast`, `plantedLastMass`: actual final-operand planting and its instance mass.

## Main results

* `uniform_mean_solutionCount`, `uniform_solution_probability_le`: uniform counts and union bound.
* `plantedLastMass_size_bias`: the manuscript's exact planted size-bias identity.
-/

public section

open scoped BigOperators

namespace Cslib.Cryptanalysis.AddXNOR

/-- A fixed-length operator string on a fixed-length list of actual operands. -/
@[expose] def steps {m q : ℕ} (bs : Fin q → Bool) (as : Fin q → BitVec m) :
    List (Bool × BitVec m) := List.ofFn fun i => (bs i, as i)

private theorem card_word (m : ℕ) : Fintype.card (BitVec m) = 2 ^ m :=
  (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)

/-- A fixed operator string has exactly uniform output, conditional on every
noninitial operand. The target is arbitrary and width zero is included. -/
theorem fixed_output_mass {m : ℕ} (xs : List (Bool × BitVec m)) (t : BitVec m) :
    (𝔼 s : BitVec m, if eval xs s = t then (1 : ℚ) else 0) = 1 / 2 ^ m := by
  calc
    _ = 𝔼 v : BitVec m, if v = t then (1 : ℚ) else 0 :=
      Fintype.expect_bijective (eval xs) (eval_bijective xs) _ _ (fun _ => rfl)
    _ = _ := by simp [Finset.expect_eq_sum_div_card, card_word]

/-- Number of solutions for a full-width instance and a general target. -/
@[expose] def solutionCount {m q : ℕ} (as : Fin q → BitVec m) (s t : BitVec m) : ℕ :=
  ∑ bs : Fin q → Bool, if eval (steps bs as) s = t then 1 else 0

/-- The exact conditional mean count is `2^q / 2^m`; independence across
operator strings is neither required nor asserted. -/
theorem mean_solutionCount {m q : ℕ} (as : Fin q → BitVec m) (t : BitVec m) :
    (𝔼 s : BitVec m, (solutionCount as s t : ℚ)) = 2 ^ q / 2 ^ m := by
  simp only [solutionCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.expect_sum_comm]
  simp [fixed_output_mass, nsmul_eq_mul, div_eq_mul_inv]

/-- Proposition 1: the actual independent uniform-instance mean. -/
theorem uniform_mean_solutionCount (m q : ℕ) (t : BitVec m) :
    (𝔼 as : Fin q → BitVec m, 𝔼 s : BitVec m, (solutionCount as s t : ℚ)) =
      2 ^ q / 2 ^ m := by simp [mean_solutionCount]

/-- The balanced model has q=N−1 and m=N, so its mean count is one half. -/
theorem balanced_mean_solutionCount (q : ℕ) (t : BitVec (q + 1)) :
    (𝔼 as : Fin q → BitVec (q + 1), 𝔼 s : BitVec (q + 1),
      (solutionCount as s t : ℚ)) = 1 / 2 := by
  rw [uniform_mean_solutionCount, pow_succ]
  field_simp

/-- The event of having a solution is bounded pointwise by the count. -/
theorem solution_event_le_count {m q : ℕ} (as : Fin q → BitVec m) (s t : BitVec m) :
    (if 0 < solutionCount as s t then (1 : ℚ) else 0) ≤ solutionCount as s t := by
  split
  · exact_mod_cast (show 1 ≤ solutionCount as s t by omega)
  · exact Nat.cast_nonneg _

/-- Proposition 1's Markov/union bound, on the literal independent uniform inputs. -/
theorem uniform_solution_probability_le (m q : ℕ) (t : BitVec m) :
    (𝔼 as : Fin q → BitVec m, 𝔼 s : BitVec m,
      if 0 < solutionCount as s t then (1 : ℚ) else 0) ≤ 2 ^ q / 2 ^ m := by
  rw [← uniform_mean_solutionCount m q t]
  apply Finset.expect_le_expect
  intro as _
  exact Finset.expect_le_expect fun s _ => solution_event_le_count as s t

/-- Plant a solution by uniquely completing the initial word. Other operands
and the operator string are the independent seed; target is fixed. -/
@[expose] def plantedInitial {m q : ℕ} (bs : Fin q → Bool)
    (as : Fin q → BitVec m) (t : BitVec m) : BitVec m := backward (steps bs as) t

/-- Every planting seed produces a valid solution. -/
theorem plantedInitial_solves {m q : ℕ} (bs : Fin q → Bool)
    (as : Fin q → BitVec m) (t : BitVec m) : eval (steps bs as) (plantedInitial bs as t) = t :=
  eval_backward _ _

/-- Uniform seed mass of one full instance under initial-word planting. -/
@[expose] def plantedMass {m q : ℕ} (as : Fin q → BitVec m) (s t : BitVec m) : ℚ :=
  𝔼 bs : Fin q → Bool, 𝔼 fresh : Fin q → BitVec m,
    if fresh = as ∧ plantedInitial bs fresh t = s then 1 else 0

/-- Uniform instance mass. Initial word and all q remaining operands are independent. -/
@[expose] def uniformMass (m q : ℕ) : ℚ := 1 / (2 ^ m) ^ (q + 1)

/-- Proposition 2's exact size-bias identity, derived by counting actual planting seeds. -/
theorem plantedMass_size_bias {m q : ℕ} (as : Fin q → BitVec m) (s t : BitVec m) :
    plantedMass as s t = (2 ^ m / 2 ^ q) * solutionCount as s t * uniformMass m q := by
  have hclose (bs : Fin q → Bool) : plantedInitial bs as t = s ↔ eval (steps bs as) s = t := by
    constructor
    · intro h; rw [← h]; exact plantedInitial_solves bs as t
    · intro h; rw [plantedInitial, ← h, backward_eval]
  simp only [plantedMass, Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, card_word]
  simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hclose]
  simp only [← Finset.sum_div]
  have hc : (solutionCount as s t : ℚ) =
      ∑ bs : Fin q → Bool, if eval (steps bs as) s = t then (1 : ℚ) else 0 := by
    simp [solutionCount]
  rw [← hc]
  unfold uniformMass
  push_cast
  rw [pow_succ]
  field_simp

/-- The unique last operand completing a prefix and prescribed last operator. -/
@[expose] def plantedLast {m q : ℕ} (bs : Fin (q + 1) → Bool)
    (as : Fin q → BitVec m) (s t : BitVec m) : BitVec m :=
  unstep (bs (Fin.last q)) t (eval (steps (fun i => bs i.castSucc) as) s)

/-- Operand symmetry gives a unique completing final operand for either operation. -/
theorem step_comm {m : ℕ} (b : Bool) (s a : BitVec m) : step b s a = step b a s := by
  cases b <;> simp [step, BitVec.add_comm, BitVec.xor_comm]

private theorem steps_snoc {m q : ℕ} (bs : Fin (q + 1) → Bool)
    (as : Fin q → BitVec m) (a : BitVec m) :
    steps bs (Fin.snoc as a) = steps (fun i => bs i.castSucc) as ++ [(bs (Fin.last q), a)] := by
  unfold steps
  rw [List.ofFn_succ_last]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- A source-style planting seed completes precisely those full instances solved
by its operator string; no independence of different strings is assumed. -/
theorem plantedLast_eq_iff {m q : ℕ} (bs : Fin (q + 1) → Bool)
    (as : Fin q → BitVec m) (s t a : BitVec m) :
    plantedLast bs as s t = a ↔ eval (steps bs (Fin.snoc as a)) s = t := by
  rw [steps_snoc, eval_append]
  simp only [eval]
  rw [step_comm (bs (Fin.last q))]
  constructor
  · intro h; rw [← h]; exact step_unstep _ _ _
  · intro h; rw [plantedLast, ← h, unstep_step]

/-- The literal manuscript planting: independent operator bits and the first
q+1 operands, then the unique final operand. Here there are q+1 operators. -/
@[expose] def plantedLastMass {m q : ℕ} (as : Fin q → BitVec m)
    (s t a : BitVec m) : ℚ :=
  𝔼 bs : Fin (q + 1) → Bool, 𝔼 first : BitVec m, 𝔼 fresh : Fin q → BitVec m,
    if first = s ∧ fresh = as ∧ plantedLast bs fresh first t = a then 1 else 0

/-- Proposition 2 for the manuscript's actual final-operand planting distribution. -/
theorem plantedLastMass_size_bias {m q : ℕ} (as : Fin q → BitVec m) (s t a : BitVec m) :
    plantedLastMass as s t a =
      (2 ^ m / 2 ^ (q + 1)) * solutionCount (Fin.snoc as a) s t * uniformMass m (q + 1) := by
  simp only [plantedLastMass, Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, card_word]
  simp only [ite_and, plantedLast_eq_iff]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Finset.sum_const_zero, ← Finset.sum_div]
  have hc : (solutionCount (Fin.snoc as a) s t : ℚ) =
      ∑ bs : Fin (q + 1) → Bool, if eval (steps bs (Fin.snoc as a)) s = t then (1 : ℚ) else 0 := by
    simp [solutionCount]
  rw [← hc]
  unfold uniformMass
  push_cast
  simp only [pow_succ]
  field_simp

end Cslib.Cryptanalysis.AddXNOR
