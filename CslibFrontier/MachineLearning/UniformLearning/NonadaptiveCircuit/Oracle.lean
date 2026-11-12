/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Oracle.FixedQueries
public import CslibFrontier.MachineLearning.UniformLearning.NonadaptiveCircuit

/-!
# Non-adaptive learners as oracle circuits

A learner with a circuit (`UniformLearning.QueryLearner.HasCircuit`) is, on every seed, an oracle
circuit in the sense of [Chen et al., Definition 3, p. 12]
[ChenHiraharaOliveiraPichRajgopalSanthanam2020]: one round of `q` oracle gates asking about fixed
words, followed by the learner's De Morgan circuit (`Boolean.fixedQueryCircuit`). Its queries do
not depend on the answers to other queries, so it uses non-adaptive membership queries; in the
measures of [Chen et al., Definition 11, p. 13][ChenHiraharaOliveiraPichRajgopalSanthanam2020] it
has `q` oracle gates, each with `n` arguments, and adaptivity at most one. The exported fan-in bound
`max n 2` also covers the De Morgan gates.

The statement holds for every oracle whose slice at the input length is the target, since only that
slice is queried; `Language.ofSlices` gives such an oracle for any target. It bounds size and the
oracle measures only: neither depth nor running time is certified.

## Main results

* `Cslib.MachineLearning.UniformLearning.QueryLearner.HasCircuit.exists_oracleCircuit`: on every
  seed, an oracle circuit with at most `S + q + 2` gates, `q` of them oracle gates at oracle depth
  at most one, computes the learner's hypothesis with the target as oracle.

## References

* [L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal and R. Santhanam, *Beyond Natural
  Proofs: Hardness Magnification and Locality*][ChenHiraharaOliveiraPichRajgopalSanthanam2020]
-/

public section

namespace Cslib.MachineLearning.UniformLearning.QueryLearner.HasCircuit

open Cslib.Circuits Cslib.Circuits.Boolean

variable {n : ℕ} {Ω : Type*} {A : QueryLearner (Fin n) Ω} {q S : ℕ}

/-- **A learner with a circuit is a non-adaptive oracle circuit** [Chen et al., Definition 3,
p. 12][ChenHiraharaOliveiraPichRajgopalSanthanam2020]: on every seed, an oracle circuit with at
most `S + q + 2` gates, of which `q` are oracle gates with at most one on any path, and fan-in at
most `max n 2`, computes the hypothesis of the learner run on `f`, under every oracle whose slice at
length `n` is `f`. -/
theorem exists_oracleCircuit (hA : A.HasCircuit q S) (ω : Ω) :
    ∃ C : Circuit oracleSignature n 1,
      C.size ≤ S + q + 2 ∧ C.program.cost OracleOp.queryWeight = q ∧
        C.depthWith OracleOp.queryWeight ≤ 1 ∧ C.FanInAtMost (max n 2) ∧
          ∀ (O : Language Bool) (f : BooleanFunction n), O.slice n = f →
            ∀ x, C.eval (oracleInterpretation O) x 0 = (A ω).eval f x := by
  obtain ⟨pts, F, hF, hev⟩ := hA ω
  obtain ⟨c, hc, hsize⟩ := (complexity_le_iff (I := interpretation)).1 hF
  refine ⟨fixedQueryCircuit pts c, ?_, cost_program_fixedQueryCircuit pts c,
    depthWith_fixedQueryCircuit_le pts c, fanInAtMost_fixedQueryCircuit pts c,
    fun O f hO x => ?_⟩
  · rw [size_fixedQueryCircuit]
    omega
  · rw [eval_fixedQueryCircuit, hc, single_apply, hev, hO]

end Cslib.MachineLearning.UniformLearning.QueryLearner.HasCircuit
