/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Distributed.OrientedCycle.ColeVishkin
public import Complexity.Computability.Distributed.OrientedCycle.Linial

/-!
# The round complexity of 3-colouring oriented cycles

Deterministic LOCAL algorithms 3-colour oriented `n`-cycles with identifiers `{0, …, n - 1}` in
`Θ(log* n)` rounds. The Cole–Vishkin algorithm of [Cole and Vishkin][ColeVishkin1986] needs
`log* n + 3` rounds, and with two reduction steps per round `⌈(log* n) / 2⌉ + 3` rounds. By the
lower bound of [Linial][Linial1992], in the form of
[Laurinharju and Suomela][LaurinharjuSuomela2014], any `t`-round algorithm has
`log* n ≤ 2t + 2`. The upper and lower bounds on the least number of
rounds differ by at most `4`.

## Main results

* `Cslib.Distributed.OrientedCycle.threeColoring_colorsCycle`: Cole–Vishkin 3-colours in
  `log* n + 3` rounds.
* `Cslib.Distributed.OrientedCycle.fastThreeColoring_colorsCycle`: two steps per round 3-colour in
  `⌈(log* n) / 2⌉ + 3` rounds.
* `Cslib.Distributed.OrientedCycle.exists_colorsCycle_three_and_logStar_le`: the `Θ(log* n)`
  round complexity of 3-colouring oriented `n`-cycles.

## References

* [R. Cole and U. Vishkin, *Deterministic coin tossing with applications to optimal parallel list
  ranking*][ColeVishkin1986]
* [N. Linial, *Locality in distributed graph algorithms*][Linial1992]
* [J. Laurinharju and J. Suomela, *Brief announcement: Linial's lower bound made
  easy*][LaurinharjuSuomela2014]
-/

public section

namespace Cslib.Distributed.OrientedCycle

/-- **Cole–Vishkin** [Cole and Vishkin][ColeVishkin1986]: on oriented `n`-cycles, `n ≠ 1`, with
identifiers `{0, …, n - 1}`, the algorithm `threeColoring (log* n)` 3-colours within `log* n + 3`
rounds. -/
theorem threeColoring_colorsCycle {n : ℕ} (hn : n ≠ 1) {t : ℕ} (ht : Nat.logStar n + 3 ≤ t) :
    (threeColoring (Nat.logStar n)).ColorsCycle n t 3 := fun _ hx hxn =>
  threeColoring_run_of_injective hx hn hxn ht

/-- **Cole–Vishkin with two steps per round**: on oriented `n`-cycles, `n ≠ 1`, with identifiers
`{0, …, n - 1}`, the algorithm `fastThreeColoring s` 3-colours within `s + 3` rounds when
`log* n ≤ 2 s`, for instance for `s = ⌈(log* n) / 2⌉`. -/
theorem fastThreeColoring_colorsCycle {n s : ℕ} (hn : n ≠ 1) (hs : Nat.logStar n ≤ 2 * s) {t : ℕ}
    (ht : s + 3 ≤ t) : (fastThreeColoring s).ColorsCycle n t 3 := fun _ hx hxn =>
  fastThreeColoring_run (IsProperColoring.of_injective hx hn) hxn hs ht

/-- **The round complexity of 3-colouring oriented cycles is `Θ(log* n)`.** For `n ≠ 1`, some
deterministic LOCAL algorithm properly 3-colours every oriented `n`-cycle with identifiers
`{0, …, n - 1}` within `⌈(log* n) / 2⌉ + 3` rounds [Cole and Vishkin][ColeVishkin1986], and every
algorithm doing so within `t` rounds has `log* n ≤ 2t + 2` [Linial][Linial1992]. -/
theorem exists_colorsCycle_three_and_logStar_le {n : ℕ} (hn : n ≠ 1) :
    (∃ (S : Type) (A : Algorithm ℕ S ℕ), A.ColorsCycle n ((Nat.logStar n + 1) / 2 + 3) 3) ∧
      ∀ {S : Type*} (A : Algorithm ℕ S ℕ) (t : ℕ), A.ColorsCycle n t 3 →
        Nat.logStar n ≤ 2 * t + 2 :=
  ⟨⟨_, _, fastThreeColoring_colorsCycle hn (by omega) le_rfl⟩,
    fun _ _ hA => hA.logStar_le_of_three⟩

end Cslib.Distributed.OrientedCycle
