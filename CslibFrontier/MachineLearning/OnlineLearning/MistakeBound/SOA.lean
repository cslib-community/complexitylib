/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Littlestone

/-!
# The standard optimal algorithm

The **standard optimal algorithm** (SOA) [Littlestone1988, §3, Algorithm 2] keeps the version
space `V` of the history. On instance `x`, it compares the Littlestone dimensions of the two
restrictions `V₀ = {c ∈ V | c x = false}` and `V₁ = {c ∈ V | c x = true}` and predicts `true` iff
`K(V₁) > K(V₀)`, with Littlestone's convention `K(∅) = -1`. Here `littlestoneDim ∅ = 0`, so the
convention appears as the explicit emptiness checks in `soa`: it predicts `true` iff `V₁` is
nonempty and either `V₀` is empty or `littlestoneDim V₀ < littlestoneDim V₁`.

After a mistake on a realizable sequence, the version space is the restriction with the larger
dimension. Both restrictions are nonempty, and a complete tree for each would combine into a
deeper tree for `V`, so the dimension drops by at least one (`littlestoneDim_add_one_le_of_soa_ne`).
Hence SOA makes at most `littlestoneDim C` mistakes [Littlestone1988, §3, Lemma 2]. With the lower
bound of `CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Littlestone`, this gives
**Littlestone's theorem**: `optimalMistakeBound C = littlestoneDim C`, and SOA attains it
[Littlestone1988, §3, Theorem 3]. Littlestone states the theorem for finite classes. The proof
here works for every class, with both sides possibly `⊤`, as in
[ShalevShwartzBenDavid2014, §21.1].

`soa` is a noncomputable specification: it decides emptiness and compares Littlestone dimensions
of arbitrary classes classically. The running time of the algorithm is not modelled.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.soa`: the standard optimal algorithm.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.mistakeBound_soa`: SOA makes exactly
  `littlestoneDim C` mistakes in the worst case.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.optimalMistakeBound_eq_littlestoneDim`:
  [Littlestone1988, §3, Theorem 3], the optimal mistake bound is the Littlestone dimension.

## References

* [N. Littlestone, *Learning quickly when irrelevant attributes abound: a new linear-threshold
  algorithm*][Littlestone1988]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

open PACLearning (ConceptClass)

variable {α : Type*}

open Classical in
/-- The standard optimal algorithm [Littlestone1988, §3, Algorithm 2]. After the history `h`,
predict `true` on `x` iff the concepts consistent with `h ++ [(x, true)]` exist and, when the
concepts consistent with `h ++ [(x, false)]` exist too, have the larger Littlestone dimension. -/
noncomputable def soa (C : ConceptClass α Bool) : OnlineLearner α := fun h x =>
  decide ((versionSpace C (h ++ [(x, true)])).Nonempty ∧
    ((versionSpace C (h ++ [(x, false)])).Nonempty →
      littlestoneDim (versionSpace C (h ++ [(x, false)])) <
        littlestoneDim (versionSpace C (h ++ [(x, true)]))))

/-- After a mistake of SOA on an example `(x, y)` consistent with some concept of the version
space, the Littlestone dimension of the version space drops by at least one. -/
theorem littlestoneDim_add_one_le_of_soa_ne (C : ConceptClass α Bool) (h : List (α × Bool))
    (x : α) (y : Bool) (hne : soa C h x ≠ y) (hy : (versionSpace C (h ++ [(x, y)])).Nonempty) :
    littlestoneDim (versionSpace C (h ++ [(x, y)])) + 1 ≤ littlestoneDim (versionSpace C h) := by
  rw [versionSpace_append] at hy ⊢
  cases y with
  | true =>
    have hfalse : soa C h x = false := by simpa using hne
    simp only [soa, versionSpace_append, decide_eq_false_iff_not, not_and, not_imp,
      not_lt] at hfalse
    obtain ⟨h0, hle⟩ := hfalse hy
    have := min_littlestoneDim_add_one_le (versionSpace C h) x h0 hy
    rwa [min_eq_right hle] at this
  | false =>
    have htrue : soa C h x = true := by simpa using hne
    simp only [soa, versionSpace_append, decide_eq_true_eq] at htrue
    obtain ⟨h1, hlt⟩ := htrue
    have := min_littlestoneDim_add_one_le (versionSpace C h) x hy h1
    rwa [min_eq_left (hlt hy).le] at this

/-- After the history `h`, SOA makes at most `littlestoneDim (versionSpace C h)` mistakes on
rounds `S` such that `h ++ S` is realizable [Littlestone1988, §3, Lemma 2]. -/
theorem mistakesFrom_soa_le (C : ConceptClass α Bool) (h S : List (α × Bool))
    (hS : Realizable C (h ++ S)) :
    (mistakesFrom (soa C) h S : ℕ∞) ≤ littlestoneDim (versionSpace C h) := by
  induction S generalizing h with
  | nil => simp
  | cons p S ih =>
    obtain ⟨x, y⟩ := p
    have hS' : Realizable C ((h ++ [(x, y)]) ++ S) := by simpa using hS
    have ih' := ih _ hS'
    have hy : (versionSpace C (h ++ [(x, y)])).Nonempty := by
      obtain ⟨c, hc⟩ := hS'
      rw [versionSpace_append] at hc
      exact ⟨c, hc.1⟩
    rw [mistakesFrom_cons]
    split
    · rw [zero_add]
      refine ih'.trans (littlestoneDim_mono ?_)
      rw [versionSpace_append]
      exact versionSpace_subset _ _
    · rename_i hne
      have hdrop := littlestoneDim_add_one_le_of_soa_ne C h x y hne hy
      push_cast
      rw [add_comm]
      calc ((mistakesFrom (soa C) (h ++ [(x, y)]) S : ℕ∞) + 1)
          ≤ littlestoneDim (versionSpace C (h ++ [(x, y)])) + 1 := by gcongr
        _ ≤ _ := hdrop

theorem mistakeBound_soa_le (C : ConceptClass α Bool) :
    mistakeBound (soa C) C ≤ littlestoneDim C :=
  mistakeBound_le_iff.mpr fun S hS => by
    have := mistakesFrom_soa_le C [] S (by simpa using hS)
    rwa [versionSpace_nil] at this

/-- SOA makes exactly `littlestoneDim C` mistakes in the worst case. -/
theorem mistakeBound_soa (C : ConceptClass α Bool) :
    mistakeBound (soa C) C = littlestoneDim C :=
  le_antisymm (mistakeBound_soa_le C) (littlestoneDim_le_mistakeBound _ C)

/-- **Littlestone's theorem** [Littlestone1988, §3, Theorem 3]: the optimal mistake bound of a
concept class is its Littlestone dimension. Littlestone states it for finite classes; this version
holds for every class, both sides being `⊤` when there are complete mistake trees of every
height. -/
theorem optimalMistakeBound_eq_littlestoneDim (C : ConceptClass α Bool) :
    optimalMistakeBound C = littlestoneDim C :=
  le_antisymm ((optimalMistakeBound_le (soa C) C).trans (mistakeBound_soa_le C))
    (littlestoneDim_le_optimalMistakeBound C)

/-- SOA is an optimal learner. -/
theorem mistakeBound_soa_eq_optimalMistakeBound (C : ConceptClass α Bool) :
    mistakeBound (soa C) C = optimalMistakeBound C := by
  rw [mistakeBound_soa, optimalMistakeBound_eq_littlestoneDim]

end Cslib.MachineLearning.OnlineLearning.MistakeBound
