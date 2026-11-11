/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.UniformLearning.MembershipQuery
public import Cslib.Computability.Circuit.Boolean.Complexity
import CslibFrontier.Computability.Circuit.Boolean.Substitution

/-!
# Non-adaptive learners computed by small circuits

A membership-query learner *has a circuit* of size `S` with `q` queries
(`UniformLearning.QueryLearner.HasCircuit`) when, on every seed, it queries `q` points fixed by the
seed and computes its hypothesis at `x` from the answers and `x` by a De Morgan circuit with at most
`S` gates. This is the learner-level form of learning by circuits with non-adaptive membership
queries [Chen et al., Definition 3, p. 12][ChenHiraharaOliveiraPichRajgopalSanthanam2020]. The
oracle-circuit form, one round of `q` oracle gates on fixed words followed by that circuit, is
`UniformLearning.QueryLearner.HasCircuit.exists_oracleCircuit`.

The definition differs from the source's in the following ways.
* **Per seed.** The circuit may depend on the seed, which is fixed first; the source has one
  randomized circuit reading its random bits. A consumer that fixes the seed, such as the
  Adleman-style step of [Chen et al., Lemma 34, pp. 25–27]
  [ChenHiraharaOliveiraPichRajgopalSanthanam2020], needs only the per-seed form.
* **Evaluation.** The circuit computes the hypothesis's value at `x` from the answers and `x`; the
  source's learner outputs a description of the hypothesis.
* **Size.** The size is De Morgan circuit complexity (`Circuits.complexity`). Only size is
  bounded: neither the depth of the circuit nor the learner's running time is certified.
* **Semantic.** The definition constrains the hypothesis as a function of the target, not the
  decision tree: `HasCircuit` does not bound the queries of the tree itself, which
  `UniformLearning.QueryLearner.QueriesAtMost` does.

The size of every hypothesis is at most `S + 2`
(`UniformLearning.QueryLearner.HasCircuit.complexity_eval_le`), since fixing the answers costs the
two constants. A learner built from point lists by `UniformLearning.QueryLearner.ofNonadaptive`
has a circuit when its hypothesis does (`UniformLearning.QueryLearner.hasCircuit_ofNonadaptive`).

## Main definitions

* `Cslib.MachineLearning.UniformLearning.QueryLearner.HasCircuit`: on every seed, `q` fixed queries
  and a circuit with at most `S` gates from the answers and the point to the hypothesis.

## Main results

* `Cslib.MachineLearning.UniformLearning.QueryLearner.HasCircuit.mono`,
  `Cslib.MachineLearning.UniformLearning.QueryLearner.HasCircuit.pad`: more gates or more queries.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.HasCircuit.complexity_eval_le`: every
  hypothesis has at most `S + 2` gates.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.hasCircuit_ofNonadaptive`: the non-adaptive
  learner of a list of points.

## References

* [L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal and R. Santhanam, *Beyond Natural
  Proofs: Hardness Magnification and Locality*][ChenHiraharaOliveiraPichRajgopalSanthanam2020]
-/

public section

namespace Cslib.MachineLearning.UniformLearning.QueryLearner

open Cslib.Circuits Cslib.Circuits.Boolean

variable {n : ℕ} {Ω : Type*}

/-- **A non-adaptive learner computed by a small circuit**: on every seed `ω`, the learner's
hypothesis at `x` is computed from the answers of the target at `q` points fixed by `ω`, followed
by `x`, with a De Morgan circuit of at most `S` gates. Exposed: clients build and take apart the
witnesses. -/
@[expose] def HasCircuit (A : QueryLearner (Fin n) Ω) (q S : ℕ) : Prop :=
  ∀ ω, ∃ (pts : Fin q → BitString n) (F : BooleanFunction (q + n)),
    complexity interpretation (single F) ≤ S ∧
      ∀ (f : BooleanFunction n) x, (A ω).eval f x = F (Fin.append (fun i => f (pts i)) x)

namespace HasCircuit

variable {A : QueryLearner (Fin n) Ω} {q S : ℕ}

theorem mono (hA : A.HasCircuit q S) {S' : ℕ} (h : S ≤ S') : A.HasCircuit q S' := fun ω => by
  obtain ⟨pts, F, hF, hev⟩ := hA ω
  exact ⟨pts, F, hF.trans h, hev⟩

/-- More queries: the extra points are queried and ignored. -/
theorem pad (hA : A.HasCircuit q S) {q' : ℕ} (h : q ≤ q') : A.HasCircuit q' S := fun ω => by
  obtain ⟨pts, F, hF, hev⟩ := hA ω
  let embed : Fin (q + n) → Fin (q' + n) :=
    Fin.append (fun i => Fin.castAdd n (Fin.castLE h i)) (Fin.natAdd q')
  refine ⟨fun i => if hi : i.1 < q then pts ⟨i.1, hi⟩ else fun _ => false,
    fun z => F (z ∘ embed), ?_, fun f x => ?_⟩
  · calc complexity interpretation (single fun z => F (z ∘ embed))
        = complexity interpretation (single F ∘ fun z => z ∘ embed) := rfl
      _ ≤ complexity interpretation (fun z : BitString (q' + n) => z ∘ embed) +
          complexity interpretation (single F) := complexity_comp_le _ _
      _ ≤ S := by rw [complexity_wiring, zero_add]; exact hF
  · rw [hev]
    congr 1
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [embed, Fin.append_left]
    · simp [embed, Fin.append_right]

/-- **Every hypothesis is small**: fixing the answers of a circuit with at most `S` gates costs
the two constants. -/
theorem complexity_eval_le (hA : A.HasCircuit q S) (f : BooleanFunction n) (ω : Ω) :
    complexity interpretation (single ((A ω).eval f)) ≤ S + 2 := by
  obtain ⟨pts, F, hF, hev⟩ := hA ω
  let ρ : Fin (q + n) → Fin n ⊕ Bool := Fin.append (fun i => .inr (f (pts i))) .inl
  have e : (A ω).eval f = fun x => F (substitute ρ x) := by
    funext x
    rw [hev]
    congr 1
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [ρ, substitute]
  rw [e]
  exact (complexity_substitute_le ρ F).trans (Nat.add_le_add_right hF 2)

end HasCircuit

/-- **The non-adaptive learner of a list of points** has a circuit when its hypothesis is computed
from the answers at `q` points and the input by a circuit with at most `S` gates, provided the
hypothesis reads the target only at the listed points. -/
theorem hasCircuit_ofNonadaptive {points : Ω → List (BitString n)}
    {hyp : BooleanFunction n → Ω → BooleanFunction n}
    (hhyp : ∀ ω g g', (∀ x ∈ points ω, g x = g' x) → hyp g ω = hyp g' ω) {q S : ℕ}
    (hF : ∀ ω, ∃ (pts : Fin q → BitString n) (F : BooleanFunction (q + n)),
      complexity interpretation (single F) ≤ S ∧
        ∀ f x, hyp f ω x = F (Fin.append (fun i => f (pts i)) x)) :
    (ofNonadaptive points hyp).HasCircuit q S := fun ω => by
  obtain ⟨pts, F, hS, hev⟩ := hF ω
  exact ⟨pts, F, hS, fun f x => by rw [eval_ofNonadaptive hhyp, hev]⟩

end Cslib.MachineLearning.UniformLearning.QueryLearner
