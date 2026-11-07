/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Languages.Probabilistic.Oracle.QueryCount
public import Complexity.Languages.Probabilistic.Semantics

/-!
# Expected query cost

`OracleComp.expectedCost h cost program` is the expected total cost of the calls of `program` when
each call `q` is answered by an independent sample of `h q` and costs `cost q`. It is the
average-case companion of the worst-case budget `OracleComp.IsCostBounded`: a budget of `n` bounds
the expected cost by `n` (`OracleComp.expectedCost_le_of_isCostBounded`). Unlike a budget, the
expected cost depends on the answers, so it is taken with respect to the distributions `h`, as in
`OracleComp.evalWith`.

The expected cost is defined by recursion on the tree of calls. It is additive under sequencing,
weighting the continuation by the output distribution of the first program (Wald's identity,
`OracleComp.expectedCost_bind`), linear in the cost, and monotone in it. Replacing each call by a
program over another interface turns the expected cost into the expected cost of the original calls,
each priced at the expected cost of its replacement (`OracleComp.expectedCost_interpret`).

With a cost that is `1` on the reads of one position of an oracle and `0` elsewhere, the expected
cost is the expected number of times a program reads that position, which is how the smoothness of
a local decoder is measured.

## Main definitions

* `Cslib.OracleComp.expectedCost`: the expected total cost of the calls.

## Main results

* `Cslib.OracleComp.expectedCost_bind`: expected costs add under sequencing.
* `Cslib.OracleComp.expectedCost_le_of_isCostBounded`: a budget bounds the expected cost.
* `Cslib.OracleComp.expectedCost_sum`, `Cslib.OracleComp.expectedCost_mono`: linearity and
  monotonicity in the cost.
* `Cslib.OracleComp.expectedCost_interpret`: the expected cost of a program run through a handler.
-/

public section

open scoped ENNReal

namespace Cslib.OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α β : Type v}

/-- The expected total cost of the calls of `program` when each call `q` is answered by an
independent sample of `h q` and costs `cost q`. -/
noncomputable def expectedCost (h : (q : ι) → PMF (spec q)) (cost : ι → ℝ≥0∞) :
    OracleComp spec α → ℝ≥0∞
  | .pure _ => 0
  | .liftBind q cont => cost q + ∑' a, h q a * expectedCost h cost (cont a)

section Basic

variable (h : (q : ι) → PMF (spec q)) (cost : ι → ℝ≥0∞)

/-- Returning a value makes no call. -/
@[simp] theorem expectedCost_pure (a : α) :
    expectedCost h cost (pure a : OracleComp spec α) = 0 := by
  rw [expectedCost.eq_def]
  rfl

/-- A call costs its cost, followed by the expected cost of the continuation at its answer. -/
theorem expectedCost_query_bind (q : ι) (cont : spec q → OracleComp spec α) :
    expectedCost h cost (query q >>= cont) =
      cost q + ∑' a, h q a * expectedCost h cost (cont a) := by
  rw [expectedCost.eq_def]
  rfl

/-- A single call costs its cost. -/
@[simp] theorem expectedCost_query (q : ι) :
    expectedCost h cost (query (spec := spec) q) = cost q := by
  rw [← bind_pure (query q), expectedCost_query_bind]
  simp

/-- **Wald's identity** for oracle programs: the expected cost of a sequence is the expected cost
of the first program plus the expected cost of the continuation at its result. -/
theorem expectedCost_bind (program : OracleComp spec α) (next : α → OracleComp spec β) :
    expectedCost h cost (program >>= next) =
      expectedCost h cost program +
        ∑' a, evalWith h program a * expectedCost h cost (next a) := by
  induction program using OracleComp.induction with
  | pure a =>
    rw [pure_bind, evalWith_pure, expectedCost_pure, zero_add,
      tsum_eq_single a fun b hb => by rw [PMF.pure_apply_of_ne _ _ hb, zero_mul],
      PMF.pure_apply_self, one_mul]
  | query_bind q cont ih =>
    rw [bind_assoc, expectedCost_query_bind, expectedCost_query_bind, evalWith_bind,
      evalWith_query, add_assoc]
    congr 1
    simp only [ih, mul_add, tsum_add, PMF.bind_apply]
    congr 1
    simp only [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right, mul_assoc]
    exact tsum_comm

/-- Postprocessing the result makes no call. -/
@[simp] theorem expectedCost_map (f : α → β) (program : OracleComp spec α) :
    expectedCost h cost (f <$> program) = expectedCost h cost program := by
  rw [← bind_pure_comp, expectedCost_bind]
  simp

/-- A budget bounds the expected cost, whatever the distributions of the answers. -/
theorem expectedCost_le_of_isCostBounded {cost : ι → ℕ} {program : OracleComp spec α} {n : ℕ}
    (hb : IsCostBounded cost program n) :
    expectedCost h (fun q => (cost q : ℝ≥0∞)) program ≤ n := by
  induction hb with
  | pure a n => simp
  | liftBind q cont n _ ih =>
    rw [expectedCost_query_bind, Nat.cast_add, add_comm (n : ℝ≥0∞)]
    gcongr
    calc ∑' a, h q a * expectedCost h _ (cont a) ≤ ∑' a, h q a * n :=
          tsum_le_tsum fun a => by gcongr; exact ih a
      _ = n := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- A program whose calls all cost nothing under one cost has zero expected cost under every cost
that vanishes on the same calls. -/
theorem expectedCost_eq_zero_of_isCostBounded {cost' : ι → ℕ} {program : OracleComp spec α}
    (hb : IsCostBounded cost' program 0) (hcost : ∀ q, cost' q = 0 → cost q = 0) :
    expectedCost h cost program = 0 := by
  induction program using OracleComp.induction with
  | pure a => rfl
  | query_bind q cont ih =>
    obtain ⟨hle, hcont⟩ := IsCostBounded.liftBind_iff.mp hb
    rw [expectedCost_query_bind, hcost q (by omega)]
    simp [ih _ ((hcont _).mono (by omega))]

end Basic

section Cost

variable (h : (q : ι) → PMF (spec q))

/-- Calls that cost nothing have zero expected cost. -/
@[simp] theorem expectedCost_zero (program : OracleComp spec α) :
    expectedCost h 0 program = 0 :=
  expectedCost_eq_zero_of_isCostBounded h 0
    (IsCostBounded.of_forall_cost_eq_zero (cost := fun _ => 0) (fun _ => rfl) program)
    fun _ _ => rfl

/-- The expected cost is additive in the cost. -/
theorem expectedCost_add (cost cost' : ι → ℝ≥0∞) (program : OracleComp spec α) :
    expectedCost h (cost + cost') program =
      expectedCost h cost program + expectedCost h cost' program := by
  induction program using OracleComp.induction with
  | pure a => simp
  | query_bind q cont ih =>
    simp only [expectedCost_query_bind, ih, mul_add, tsum_add, Pi.add_apply]
    ring

/-- The expected cost of a finite sum of costs is the sum of the expected costs. -/
theorem expectedCost_sum {κ : Type*} (s : Finset κ) (cost : κ → ι → ℝ≥0∞)
    (program : OracleComp spec α) :
    expectedCost h (∑ k ∈ s, cost k) program = ∑ k ∈ s, expectedCost h (cost k) program := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, expectedCost_add, ih]

/-- The expected cost is monotone in the cost. -/
theorem expectedCost_mono {cost cost' : ι → ℝ≥0∞} (hcost : cost ≤ cost')
    (program : OracleComp spec α) : expectedCost h cost program ≤ expectedCost h cost' program := by
  induction program using OracleComp.induction with
  | pure a => simp
  | query_bind q cont ih =>
    simp only [expectedCost_query_bind]
    gcongr with a
    · exact hcost q
    · exact ih a

end Cost

/-- The expected cost of a program whose calls were replaced by programs over another interface is
the expected cost of the original calls, each priced at the expected cost of its replacement and
answered with the distribution of its replacement. -/
theorem expectedCost_interpret {κ : Type u} {target : OracleSpec.{u, v} κ}
    (handler : (q : ι) → OracleComp target (spec q)) (h : (q : κ) → PMF (target q))
    (cost : κ → ℝ≥0∞) (program : OracleComp spec α) :
    expectedCost h cost (interpret handler program) =
      expectedCost (fun q => evalWith h (handler q)) (fun q => expectedCost h cost (handler q))
        program := by
  induction program using OracleComp.induction with
  | pure a => rfl
  | query_bind q cont ih =>
    rw [interpret_bind, interpret_query, expectedCost_bind, expectedCost_query_bind]
    simp only [ih]

end Cslib.OracleComp

namespace Cslib.ProbOracleComp

open OracleComp

variable {Query α : Type} {spec : Query → Type}

/-- Private coins are free: a closed sampler has zero expected cost under every cost of the external
queries. -/
@[simp] theorem expectedCost_sample (h : (q : ℕ ⊕ Query) → PMF (probOracleSpec spec q))
    (cost : Query → ℝ≥0∞) (program : ProbComp α) :
    expectedCost h (Sum.elim 0 cost) (sample (spec := spec) program) = 0 :=
  expectedCost_eq_zero_of_isCostBounded h _ (IsQueryBounded.sample program) fun q hq => by
    cases q with
    | inl n => rfl
    | inr q => simp at hq

end Cslib.ProbOracleComp
