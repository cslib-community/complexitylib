/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.UniformStructure
public import CslibFrontier.Probability.PMF.Coin
public import CslibFrontier.Probability.Product

/-!
# Random structures with constant probabilities per relation symbol

For a relational language `L` with finitely many relation symbols and a probability
`p R ∈ [0, 1]` for each relation symbol `R`, `Cslib.Logic.FO.bernoulliStructure p n` is the random
`L`-structure on `Fin n` in which every atomic fact `R(a₁, …, aₗ)` holds independently with
probability `p R`: the independent product (`Cslib.Probability.PMF.pi`) of the coins
`Cslib.Probability.PMF.coin (p R)`, one for each atomic fact. When every `p R` is `1/2` it is the
uniform random structure `Cslib.Logic.FO.uniformStructure`
(`Cslib.Logic.FO.bernoulliStructure_eq_uniformStructure`).

For `L = Language.graph` this is a random *directed* graph with loops: each of the `n²` ordered
pairs is an edge with probability `p`. It is not the binomial random simple graph `G(n, p)` of
`CslibFrontier.Logics.FirstOrder.ZeroOneLaw.BinomialRandomGraph`.

A nullary relation symbol `R` is a single atomic fact, true with probability exactly `p R` for
every `n` (`Cslib.Logic.FO.sentenceProb_bernoulliStructure_nullary`). So when `0 < p R < 1` the
vocabulary has no 0-1 law (`Cslib.Logic.FO.not_zero_one_law_bernoulliStructure_of_nullary`); the
uniform case is `Cslib.Logic.FO.not_zero_one_law_of_nullary`.

## Main definitions

* `Cslib.Logic.FO.bernoulliStructure`: the random structure on `Fin n` in which each atomic fact
  `R(t)` holds independently with probability `p R`.

## Main results

* `Cslib.Logic.FO.bernoulliStructure_eq_uniformStructure`,
  `Cslib.Logic.FO.bernoulliStructure_const_half`: at `p = 1/2` it is the uniform random structure.
* `Cslib.Logic.FO.structProb_bernoulliStructure_relMap`: each atomic fact `R(t)` has probability
  `p R`.
* `Cslib.Logic.FO.not_zero_one_law_bernoulliStructure_of_nullary`,
  `Cslib.Logic.FO.not_zero_one_law_of_nullary`: a nullary relation symbol with `0 < p R < 1`
  breaks the 0-1 law.

## References

* [R. Fagin, *Probabilities on finite models*][Fagin1976]
-/

public section

open FirstOrder Language Structure Cslib.Probability Filter
open scoped unitInterval

namespace Cslib.Logic.FO

universe u v

variable {L : Language.{u, v}} [L.IsRelational] [Finite (Σ l, L.Relations l)]

/-- The random structure on `Fin n` in which every atomic fact `R(a₁, …, aₗ)` holds independently
with probability `p R`. -/
noncomputable def bernoulliStructure (p : (Σ l, L.Relations l) → I) (n : ℕ) :
    PMF (L.Structure (Fin n)) :=
  have := Fintype.ofFinite (Σ l, L.Relations l)
  (PMF.pi fun a : Atom L n => PMF.coin (p a.1)).map atomStructure

/-- `bernoulliStructure p n` is the image of the independent coins under `atomStructure`, for any
`Fintype` instance on the atomic facts. -/
theorem bernoulliStructure_eq_map (p : (Σ l, L.Relations l) → I) (n : ℕ) [Fintype (Atom L n)] :
    bernoulliStructure p n = (PMF.pi fun a : Atom L n => PMF.coin (p a.1)).map atomStructure := by
  rw [bernoulliStructure]
  congr
  exact Subsingleton.elim _ _

/-- **At `p = 1/2` the random structure is uniform**: fair coins on the atomic facts give
`Cslib.Logic.FO.uniformStructure`. -/
theorem bernoulliStructure_eq_uniformStructure {p : (Σ l, L.Relations l) → I}
    (hp : ∀ R, (p R : ℝ) = 1 / 2) (n : ℕ) : bernoulliStructure p n = uniformStructure n := by
  classical
  have := Fintype.ofFinite (Σ l, L.Relations l)
  rw [bernoulliStructure_eq_map, uniformStructure_eq_map]
  simp only [PMF.coin_eq_uniformOfFintype (hp _)]
  rw [PMF.pi_uniformOfFintype]

/-- The constant probability `1/2` gives the uniform random structure. -/
theorem bernoulliStructure_const_half (n : ℕ) :
    bernoulliStructure (L := L) (fun _ => ⟨1 / 2, by norm_num, by norm_num⟩) n =
      uniformStructure n :=
  bernoulliStructure_eq_uniformStructure (fun _ => rfl) n

/-- Each atomic fact `R(t)` holds in `bernoulliStructure p n` with probability `p R`. -/
theorem structProb_bernoulliStructure_relMap (p : (Σ l, L.Relations l) → I) {n l : ℕ}
    (R : L.Relations l) (t : Fin l → Fin n) :
    structProb (bernoulliStructure p n) (fun S => @RelMap L (Fin n) S l R t) = p ⟨l, R⟩ := by
  have := Fintype.ofFinite (Σ l, L.Relations l)
  let a : Atom L n := ⟨⟨l, R⟩, t⟩
  rw [structProb_def, bernoulliStructure_eq_map, PMF.toOuterMeasure_map_apply]
  change ((PMF.pi fun a : Atom L n => PMF.coin (p a.1)).toOuterMeasure
    ((fun y : Atom L n → Bool => y a) ⁻¹' {true})).toReal = _
  rw [← PMF.toOuterMeasure_map_apply, PMF.pi_map_eval (fun a : Atom L n => PMF.coin (p a.1)) a,
    PMF.toOuterMeasure_apply_singleton, PMF.coin_apply_toReal]
  rfl

/-- Each atomic fact holds in the uniform random structure with probability `1/2`. -/
theorem structProb_uniformStructure_relMap {n l : ℕ} (R : L.Relations l) (t : Fin l → Fin n) :
    structProb (uniformStructure n) (fun S => @RelMap L (Fin n) S l R t) = 1 / 2 := by
  rw [← bernoulliStructure_const_half, structProb_bernoulliStructure_relMap]

/-- A nullary relation symbol `R` holds in `bernoulliStructure p n` with probability exactly
`p R`, for every `n`. -/
theorem sentenceProb_bernoulliStructure_nullary (p : (Σ l, L.Relations l) → I)
    (R : L.Relations 0) (n : ℕ) :
    sentenceProb (bernoulliStructure p n) (Relations.formula R Fin.elim0) = p ⟨0, R⟩ := by
  rw [sentenceProb_def, ← structProb_bernoulliStructure_relMap p R (Fin.elim0 : Fin 0 → Fin n)]
  congr 1 with S : 1
  let := S
  refine propext ?_
  rw [Sentence.Realize, Formula.realize_rel]
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

/-- A nullary relation symbol holds in the uniform random structure with probability exactly `1/2`,
for every `n`. -/
theorem sentenceProb_uniformStructure_nullary (R : L.Relations 0) (n : ℕ) :
    sentenceProb (uniformStructure n) (Relations.formula R Fin.elim0) = 1 / 2 := by
  rw [← bernoulliStructure_const_half, sentenceProb_bernoulliStructure_nullary]

/-- **Nullary relation symbols break the 0-1 law.** If `L` has a nullary relation symbol `R` with
`0 < p R < 1`, then the sentence `R` holds in `bernoulliStructure p n` with probability exactly
`p R` for every `n`, so its probability tends neither to `0` nor to `1`. -/
theorem not_zero_one_law_bernoulliStructure_of_nullary {p : (Σ l, L.Relations l) → I}
    (R : L.Relations 0) (hp0 : 0 < (p ⟨0, R⟩ : ℝ)) (hp1 : (p ⟨0, R⟩ : ℝ) < 1) :
    ¬∀ φ : L.Sentence,
      Tendsto (fun n => sentenceProb (bernoulliStructure p n) φ) atTop (nhds 0) ∨
        Tendsto (fun n => sentenceProb (bernoulliStructure p n) φ) atTop (nhds 1) := by
  intro h
  have hconst : (fun n => sentenceProb (bernoulliStructure p n)
      (Relations.formula R Fin.elim0)) = fun _ => (p ⟨0, R⟩ : ℝ) :=
    funext (sentenceProb_bernoulliStructure_nullary p R)
  rcases h (Relations.formula R Fin.elim0) with h | h <;> rw [hconst] at h <;>
    have := tendsto_nhds_unique tendsto_const_nhds h
  · exact hp0.ne' this
  · exact hp1.ne this

/-- **Nullary relation symbols break the 0-1 law.** If `L` has a nullary relation symbol `R`,
then the sentence `R` holds in the uniform random structure on `Fin n` with probability exactly
`1/2`, so its probability tends neither to `0` nor to `1`. -/
theorem not_zero_one_law_of_nullary (R : L.Relations 0) :
    ¬∀ φ : L.Sentence,
      Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 0) ∨
        Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 1) := by
  simp only [← bernoulliStructure_const_half]
  exact not_zero_one_law_bernoulliStructure_of_nullary R (by norm_num) (by norm_num)

end Cslib.Logic.FO
