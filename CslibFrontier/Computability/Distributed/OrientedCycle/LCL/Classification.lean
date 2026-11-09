/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.OrientedCycle.LCL.Flexible
public import CslibFrontier.Computability.Distributed.OrientedCycle.LCL.Linear

/-!
# Classification of LCL problems on oriented cycles

The classification of LCL problems without inputs on directed cycles by
[Chang, Studený and Suomela][ChangStudenySuomela2023] (Table 1), assembled from
`CslibFrontier.Computability.Distributed.OrientedCycle.LCL.Basic`,
`CslibFrontier.Computability.Distributed.OrientedCycle.LCL.Flexible` and
`CslibFrontier.Computability.Distributed.OrientedCycle.LCL.Linear`. For a problem `R` with finitely
many labels, exactly one of the following holds (`LCL.trichotomy`):

1. `R` has a loop `R a a`, and the constant algorithm solves `R` in `0` rounds on every cycle.
2. `R` has no loop but a flexible state `q` with flexibility `K`. On every cycle with `n ≥ K`
   nodes some algorithm solves `R` in `(K - 1) (⌈log* n / 2⌉ + 2 · 3 ^ (K - 1) + 2) + 1` rounds,
   and every `t`-round algorithm has `log* n ≤ 2t + log* |L|`: round complexity `Θ(log* n)`.
3. `R` has no flexible state. On every cycle where `R` is solvable, some algorithm solves `R` in
   `⌊n / 2⌋` rounds, and every `t`-round algorithm has `n ≤ (|L| + 1) (2t + 1)`: round
   complexity `Θ(n)`.

The cases are mutually exclusive by their first conjuncts, since a loop is a flexible state
(`LCL.IsFlexible.of_loop`). The bounds are stated for each `n`, and the algorithms of cases 2 and
3 may depend on `n`.

Case 3 also contains the problems that are solvable on no cycle at all, those without a
*repeatable* state (a closed walk `q ⇝ q`); for them both clauses hold vacuously. The source lists
these separately as unsolvable in Table 1. Case 3 is non-vacuous exactly when some state is
repeatable, as for 2-colouring, since a closed walk of length `m` gives solutions on every cycle
whose length is a positive multiple of `m`.

To destructure `trichotomy`, fix the universes of the state types in the lower-bound clauses
explicitly, e.g. `trichotomy.{0, 0, 0} R`; otherwise Lean reports universe level metavariables.

## Main results

* `Cslib.Distributed.OrientedCycle.LCL.trichotomy`: the `O(1)` / `Θ(log* n)` / `Θ(n)`
  classification.

## References

* [Y.-J. Chang, J. Studený and J. Suomela, *Distributed graph problems through an
  automata-theoretic lens*][ChangStudenySuomela2023]
-/

public section

namespace Cslib.Distributed.OrientedCycle.LCL

/-- **Classification of LCL problems on oriented cycles** ([Chang, Studený and
Suomela][ChangStudenySuomela2023], Table 1, directed cycles). Every problem with finitely many
labels has a loop and round complexity `0`; or no loop, a flexible state and round complexity
`Θ(log* n)`; or no flexible state and round complexity `Θ(n)` on the cycles where it is
solvable. The last case also contains the problems solvable on no cycle, which the source lists
separately as unsolvable; it is non-vacuous exactly when some state has a closed walk. -/
theorem trichotomy {L : Type*} [Fintype L] (R : L → L → Prop) :
    (∃ a, R a a ∧ ∀ n t, (Algorithm.const a : Algorithm ℕ Unit L).SolvesLCL R n t) ∨
    ((∀ a, ¬R a a) ∧ ∃ q K, IsFlexible R q K ∧ ∀ n, K ≤ n →
      (∃ (S : Type) (A : Algorithm ℕ S L),
        A.SolvesLCL R n ((K - 1) * ((Nat.logStar n + 1) / 2 + 2 * 3 ^ (K - 1) + 2) + 1)) ∧
      ∀ {S : Type*} (A : Algorithm ℕ S L) (t : ℕ), A.SolvesLCL R n t →
        Nat.logStar n ≤ 2 * t + Nat.logStar (Fintype.card L)) ∨
    ((∀ q K, ¬IsFlexible R q K) ∧ ∀ n, (∃ ℓ : ZMod n → L, IsSolution R ℓ) →
      (∃ A : Algorithm ℕ (ℤ → ℕ) L, A.SolvesLCL R n (n / 2)) ∧
      ∀ {S : Type*} (A : Algorithm ℕ S L) (t : ℕ), A.SolvesLCL R n t →
        n ≤ (Fintype.card L + 1) * (2 * t + 1)) := by
  by_cases hloop : ∃ a, R a a
  · obtain ⟨a, ha⟩ := hloop
    exact Or.inl ⟨a, ha, fun n t => Algorithm.solvesLCL_const ha n t⟩
  push Not at hloop
  by_cases hflex : ∃ q K, IsFlexible R q K
  · obtain ⟨q, K, hq⟩ := hflex
    exact Or.inr (Or.inl ⟨hloop, q, K, hq, fun n hKn =>
      hq.exists_solvesLCL_and_logStar_le hloop hKn⟩)
  push Not at hflex
  exact Or.inr (Or.inr ⟨hflex, fun n ⟨ℓ, hℓ⟩ =>
    hℓ.exists_solvesLCL_and_le_of_forall_not_isFlexible hflex⟩)

end Cslib.Distributed.OrientedCycle.LCL
