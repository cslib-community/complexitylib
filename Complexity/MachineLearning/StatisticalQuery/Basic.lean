/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Sign
public import Complexity.Languages.Probabilistic.QueryCount
public import Complexity.Languages.Probabilistic.Semantics
public import Cslib.MachineLearning.PACLearning.Defs
import Complexity.Languages.Probabilistic.QueriesWith
import Complexity.Probability.PMF

/-!
# Learning from statistical queries

In Kearns's statistical query model [Kearns1998] a learner does not see labelled examples of the
unknown target `c : X → Bool`. Instead it asks an oracle for the expectations
`E_{x ∼ D} [φ (x, c x)]` of bounded functions `φ` of a labelled example, and the oracle may answer
any value within a tolerance `τ` of the truth. Here:

* a statistical query (`StatisticalQuery.Query`) is a function `φ : X → Bool → ℝ` with
  `|φ x y| ≤ 1`, and its expectation under the distribution `D` labelled by `c` is
  `StatisticalQuery.expect D c φ`;
* a learner (`StatisticalQuery.Algorithm`) is a deterministic program whose calls are queries,
  answered by reals, and which returns a hypothesis `X → Bool`; its number of queries is bounded by
  `OracleComp.IsQueryBounded`;
* a learner learns a concept class `C` under `D` with tolerance `τ` and error `ε`
  (`StatisticalQuery.Learns`) if for every target `c ∈ C` and every way of answering each call
  within `τ` of the expectation, possibly adaptively, the hypothesis disagrees with `c` on a set of
  `D`-probability at most `ε` (`StatisticalQuery.disagreement`).

Kearns's queries are predicates `χ : X × {0, 1} → {0, 1}` and those of [Reyzin, Definition 2]
[Reyzin2020] take values in `{-1, 1}`; both are queries here, as are their affine images. Kearns
attaches a tolerance to each query; a learner whose tolerances are all at least `τ` is in
particular a learner with the single tolerance `τ`, so lower bounds for the single tolerance apply
to it. As in Kearns's Definition 3 there is no confidence parameter: the oracle is adversarial but
always within tolerance. A learner that is correct against every fixed answer function within
tolerance (`StatisticalQuery.LearnsStateless`) is all that the lower bounds need, and every learner
satisfying `StatisticalQuery.Learns` is one (`StatisticalQuery.Learns.learnsStateless`).

The correlation `StatisticalQuery.corr D f g` of two concepts is `E_D [f · g]` for their `±1`
values (`Cslib.BitString.signVal`); it is `1 - 2 · disagreement D f g`
(`StatisticalQuery.corr_eq_one_sub_two_mul_disagreement`).

## Main definitions

* `Cslib.MachineLearning.StatisticalQuery.Query`: a statistical query.
* `Cslib.MachineLearning.StatisticalQuery.Algorithm`: a deterministic statistical query learner.
* `Cslib.MachineLearning.StatisticalQuery.expect`: the expectation of a query.
* `Cslib.MachineLearning.StatisticalQuery.valid`: the answers within tolerance.
* `Cslib.MachineLearning.StatisticalQuery.run`: running a learner against an answer function.
* `Cslib.MachineLearning.StatisticalQuery.disagreement`,
  `Cslib.MachineLearning.StatisticalQuery.corr`: the error of a hypothesis and the correlation of
  two concepts.
* `Cslib.MachineLearning.StatisticalQuery.Learns`,
  `Cslib.MachineLearning.StatisticalQuery.LearnsStateless`: learning from statistical queries.

## Main results

* `Cslib.MachineLearning.StatisticalQuery.corr_eq_one_sub_two_mul_disagreement`.
* `Cslib.MachineLearning.StatisticalQuery.Learns.learnsStateless`: a learner against adaptive
  answers is a learner against answer functions.
* `Cslib.MachineLearning.StatisticalQuery.Learns.mono`: learning is monotone in the class, the
  tolerance and the error.

## References

* [M. Kearns, *Efficient noise-tolerant learning from statistical queries*][Kearns1998]
* [L. Reyzin, *Statistical queries and statistical algorithms: foundations and
  applications*][Reyzin2020]
-/

@[expose] public section

namespace Cslib.MachineLearning.StatisticalQuery

open Finset

/-- A statistical query about labelled examples of `X`: a function of a point and its label with
values in `[-1, 1]`. -/
structure Query (X : Type) where
  /-- The value of the query at a point and a label. -/
  toFun : X → Bool → ℝ
  /-- The values lie in `[-1, 1]`. -/
  abs_le_one' : ∀ x y, |toFun x y| ≤ 1

instance (X : Type) : CoeFun (Query X) (fun _ => X → Bool → ℝ) := ⟨Query.toFun⟩

/-- The values of a query lie in `[-1, 1]`. -/
theorem Query.abs_le_one {X : Type} (φ : Query X) (x : X) (y : Bool) : |φ x y| ≤ 1 :=
  φ.abs_le_one' x y

/-- The interface of a statistical query learner: a query is answered by a real number. -/
abbrev spec (X : Type) : OracleSpec (Query X) := fun _ => ℝ

/-- A deterministic statistical query learner: a program making queries and returning a
hypothesis. -/
abbrev Algorithm (X : Type) := OracleComp (spec X) (X → Bool)

variable {X : Type} [Fintype X]

/-- The expectation `E_{x ∼ D} [φ (x, c x)]` of the query `φ` on examples of the target `c` drawn
from `D`. -/
noncomputable def expect (D : PMF X) (c : X → Bool) (φ : Query X) : ℝ :=
  ∑ x, (D x).toReal * φ x (c x)

/-- The answers to the query `φ` within the tolerance `τ` of its expectation. -/
def valid (D : PMF X) (c : X → Bool) (τ : ℝ) (φ : Query X) : Set ℝ :=
  {a | |a - expect D c φ| ≤ τ}

/-- The hypothesis returned by the learner `A` when every query `φ` is answered by `answer φ`. -/
def run (A : Algorithm X) (answer : Query X → ℝ) : X → Bool :=
  OracleComp.interpret (m := Id) answer A

/-- The `D`-probability that `f` and `g` disagree: the error of the hypothesis `g` for the target
`f`, or of `f` for `g`. -/
noncomputable def disagreement (D : PMF X) (f g : X → Bool) : ℝ :=
  ∑ x, (D x).toReal * (if f x = g x then 0 else 1)

/-- The correlation `E_D [f · g]` of two concepts, read as `±1`-valued functions. -/
noncomputable def corr (D : PMF X) (f g : X → Bool) : ℝ :=
  ∑ x, (D x).toReal * (BitString.signVal (f x) * BitString.signVal (g x))

/-- Correlation is one minus twice the disagreement. -/
theorem corr_eq_one_sub_two_mul_disagreement (D : PMF X) (f g : X → Bool) :
    corr D f g = 1 - 2 * disagreement D f g := by
  have h : corr D f g =
      ∑ x, ((D x).toReal - 2 * ((D x).toReal * (if f x = g x then 0 else 1))) := by
    simp only [corr, BitString.signVal_mul_signVal]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  rw [h, sum_sub_distrib, Cslib.Probability.PMF.sum_toReal, ← mul_sum]
  rfl

/-- Correlation is symmetric. -/
theorem corr_comm (D : PMF X) (f g : X → Bool) : corr D f g = corr D g f := by
  simp only [corr, mul_comm (BitString.signVal (f _))]

/-- A concept has correlation `1` with itself. -/
@[simp] theorem corr_self (D : PMF X) (f : X → Bool) : corr D f f = 1 := by
  simp only [corr, BitString.signVal_mul_self, mul_one, Cslib.Probability.PMF.sum_toReal]

/-- The learner `A` learns the concept class `C` under `D` from statistical queries of tolerance
`τ` with error `ε`: for every target `c ∈ C`, whatever answers within `τ` of the expectations the
oracle gives, possibly depending on the earlier calls, the hypothesis disagrees with `c` with
probability at most `ε` [Kearns1998, Definition 3]. -/
def Learns (A : Algorithm X) (D : PMF X) (C : PACLearning.ConceptClass X Bool) (τ ε : ℝ) :
    Prop :=
  ∀ c ∈ C, ∀ h ∈ OracleComp.supportWith (valid D c τ) A, disagreement D c h ≤ ε

/-- The learner `A` learns `C` under `D` with tolerance `τ` and error `ε` against every answer
function within tolerance: an oracle answering each query by a fixed value within `τ` of its
expectation. This is weaker than `Learns` (`Learns.learnsStateless`), so lower bounds stated for
it apply to `Learns`. -/
def LearnsStateless (A : Algorithm X) (D : PMF X) (C : PACLearning.ConceptClass X Bool)
    (τ ε : ℝ) : Prop :=
  ∀ c ∈ C, ∀ answer : Query X → ℝ, (∀ φ, |answer φ - expect D c φ| ≤ τ) →
    disagreement D c (run A answer) ≤ ε

/-- A learner against adaptive answers is a learner against answer functions. -/
theorem Learns.learnsStateless {A : Algorithm X} {D : PMF X}
    {C : PACLearning.ConceptClass X Bool} {τ ε : ℝ} (h : Learns A D C τ ε) :
    LearnsStateless A D C τ ε := fun c hc _ hanswer =>
  h c hc _ (OracleComp.interpret_id_mem_supportWith hanswer A)

/-- Learning is monotone: a smaller class, a smaller tolerance and a larger error. -/
theorem Learns.mono {A : Algorithm X} {D : PMF X} {C C' : PACLearning.ConceptClass X Bool}
    {τ τ' ε ε' : ℝ} (h : Learns A D C τ ε) (hC : C' ⊆ C) (hτ : τ' ≤ τ) (hε : ε ≤ ε') :
    Learns A D C' τ' ε' := by
  intro c hc g hg
  have hsub : ∀ φ, valid D c τ' φ ⊆ valid D c τ φ := fun _ _ ha => le_trans ha hτ
  exact (h c (hC hc) g (OracleComp.supportWith_mono hsub A hg)).trans hε

end Cslib.MachineLearning.StatisticalQuery
