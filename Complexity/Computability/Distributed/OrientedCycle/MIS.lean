/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Distributed.OrientedCycle.ColeVishkin
public import Complexity.Computability.Distributed.OrientedCycle.Graph
public import Complexity.Computability.Distributed.OrientedCycle.Linial

/-!
# Maximal independent sets on oriented cycles

A maximal independent set (MIS) of the oriented `n`-cycle is computed by deterministic LOCAL
algorithms in `Θ(log* n)` rounds, like a 3-colouring, and the two problems reduce to each other in
a constant number of rounds.

* From a proper colouring with colours below `k`, the greedy colour-class algorithm
  `misOfColoring` (colour `0` joins at once, and in round `r + 1` a node of colour `r + 1` joins
  unless a neighbour has joined) marks an MIS within `k - 1` rounds (`misOfColoring_run`).
  Composed with the Cole–Vishkin algorithm of [Cole and Vishkin][ColeVishkin1986] this finds an MIS
  within `⌈(log* n) / 2⌉ + 5` rounds (`misAlgorithm_findsMIS`).
* From an MIS one round gives a proper 3-colouring (`colorOfMIS`: members get colour `0`, nodes
  whose predecessor is a member colour `1`, the others colour `2`). Hence the 3-colouring lower
  bound of [Linial][Linial1992], in the form `log* n ≤ 2t + 2` of
  [Laurinharju and Suomela][LaurinharjuSuomela2014], gives `log* n ≤ 2t + 4` for every `t`-round
  MIS algorithm (`Algorithm.FindsMIS.logStar_le`). These reductions are standard.

`IsMIS` is the local description used by algorithms. For `n ≠ 1` it agrees with Mathlib's maximal
independent sets of `OrientedCycle.graph n` (`isMIS_iff_maximal`). On the one-node cycle the only
node is its own neighbour, and no set is an `IsMIS`.

## Main definitions

* `Cslib.Distributed.OrientedCycle.IsMIS`: `s` marks a maximal independent set.
* `Cslib.Distributed.OrientedCycle.Algorithm.FindsMIS`: `A` marks an MIS of every oriented
  `n`-cycle with identifiers `{0, …, n - 1}` in `t` rounds.
* `Cslib.Distributed.OrientedCycle.misOfColoring`: greedy colour classes.
* `Cslib.Distributed.OrientedCycle.misAlgorithm`: Cole–Vishkin followed by greedy colour classes.
* `Cslib.Distributed.OrientedCycle.colorOfMIS`: one round from an MIS to a 3-colouring.

## Main results

* `Cslib.Distributed.OrientedCycle.isMIS_iff_maximal`: `IsMIS` is Mathlib's
  `Maximal (graph n).IsIndepSet`, for `n ≠ 1`.
* `Cslib.Distributed.OrientedCycle.misOfColoring_run`: a proper `k`-colouring gives an MIS within
  `k - 1` rounds.
* `Cslib.Distributed.OrientedCycle.misAlgorithm_findsMIS`: an MIS within `s + 5` rounds when
  `log* n ≤ 2s`.
* `Cslib.Distributed.OrientedCycle.IsMIS.colorOfMIS`: an MIS gives a proper 3-colouring in one
  round.
* `Cslib.Distributed.OrientedCycle.Algorithm.FindsMIS.logStar_le`: every `t`-round MIS algorithm
  has `log* n ≤ 2t + 4`.
* `Cslib.Distributed.OrientedCycle.exists_findsMIS_and_logStar_le`: the `Θ(log* n)` round
  complexity of MIS on oriented cycles.

## References

* [R. Cole and U. Vishkin, *Deterministic coin tossing with applications to optimal parallel list
  ranking*][ColeVishkin1986]
* [N. Linial, *Locality in distributed graph algorithms*][Linial1992]
* [J. Laurinharju and J. Suomela, *Brief announcement: Linial's lower bound made
  easy*][LaurinharjuSuomela2014]
-/

public section

namespace Cslib.Distributed.OrientedCycle

/-! ### Maximal independent sets -/

/-- `s` marks a maximal independent set of the oriented `n`-cycle: no node and its successor are
both marked, and every node is marked or has a marked neighbour. -/
@[expose] def IsMIS {n : ℕ} (s : ZMod n → Bool) : Prop :=
  (∀ v, s v = true → s (v + 1) = false) ∧ ∀ v, s v = true ∨ s (v - 1) = true ∨ s (v + 1) = true

instance {n : ℕ} [NeZero n] (s : ZMod n → Bool) : Decidable (IsMIS s) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem isIndepSet_graph_iff {n : ℕ} (hn : n ≠ 1) {s : ZMod n → Bool} :
    (graph n).IsIndepSet {v | s v = true} ↔ ∀ v, s v = true → s (v + 1) = false := by
  constructor
  · intro h v hv
    by_contra hv1
    exact h hv (Bool.not_eq_false _ ▸ hv1 : s (v + 1) = true) (self_ne_add_one hn v)
      (graph_adj_add_one hn v)
  · intro h u hu v hv _ huv
    rcases (graph_adj.1 huv).2 with rfl | rfl
    · exact absurd hu (by simp [h v hv])
    · exact absurd hv (by simp [h u hu])

/-- For `n ≠ 1`, `IsMIS` is Mathlib's notion of a maximal independent set of `graph n`. -/
theorem isMIS_iff_maximal {n : ℕ} (hn : n ≠ 1) {s : ZMod n → Bool} :
    IsMIS s ↔ Maximal (graph n).IsIndepSet {v | s v = true} := by
  constructor
  · rintro ⟨hi, hd⟩
    refine ⟨(isIndepSet_graph_iff hn).2 hi, fun t ht hst w hw => ?_⟩
    rcases hd w with h | h | h
    · exact h
    · have h' := graph_adj_add_one hn (w - 1)
      rw [sub_add_cancel] at h'
      exact absurd h' (ht (hst h) hw h'.ne)
    · exact absurd (graph_adj_add_one hn w) (ht hw (hst h) (graph_adj_add_one hn w).ne)
  · intro hmax
    refine ⟨(isIndepSet_graph_iff hn).1 hmax.1, fun w => ?_⟩
    by_contra hw
    simp only [not_or, Bool.not_eq_true] at hw
    obtain ⟨hw0, hwm, hwp⟩ := hw
    have hind : (graph n).IsIndepSet (insert w {v | s v = true}) := by
      refine Set.pairwise_insert.2 ⟨hmax.1, fun b hb _ => ⟨fun hwb => ?_, fun hbw => ?_⟩⟩
      · rcases (graph_adj.1 hwb).2 with h | h
        · rw [h, add_sub_cancel_right] at hwm
          simp_all
        · rw [h] at hb
          simp_all
      · rcases (graph_adj.1 hbw).2 with h | h
        · rw [h] at hb
          simp_all
        · rw [h, add_sub_cancel_right] at hwm
          simp_all
    have := hmax.2 hind (Set.subset_insert _ _) (Set.mem_insert w _)
    simp_all

/-- After `t` rounds, `A` marks a maximal independent set of every oriented `n`-cycle whose nodes
carry distinct identifiers from `{0, …, n - 1}`. Like `Algorithm.ColorsCycle`, this is vacuous for
`n = 0`; `misOfColoring_run` covers the infinite oriented path. -/
@[expose] def Algorithm.FindsMIS {S : Type*} (A : Algorithm ℕ S Bool) (n t : ℕ) : Prop :=
  ∀ x : ZMod n → ℕ, Function.Injective x → (∀ v, x v < n) → IsMIS (A.run x t)

/-! ### From a colouring to a maximal independent set -/

/-- Greedy colour classes. A node of colour `0` joins at once; in round `r + 1` a node of colour
`r + 1` joins unless a neighbour has joined. The state is the colour and whether the node has
joined; the output is whether it has joined. -/
@[expose] def misOfColoring : Algorithm ℕ (ℕ × Bool) Bool where
  init c := (c, decide (c = 0))
  step r p s q := (s.1, s.2 || (decide (s.1 = r + 1) && !p.2 && !q.2))
  output s := s.2

namespace misOfColoring

variable {n : ℕ} (x : ZMod n → ℕ)

@[simp] theorem state_fst (r : ℕ) (v : ZMod n) : (misOfColoring.state x r v).1 = x v := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih => exact ih v

theorem state_snd_succ (r : ℕ) (v : ZMod n) :
    (misOfColoring.state x (r + 1) v).2 = ((misOfColoring.state x r v).2 ||
      (decide (x v = r + 1) && !(misOfColoring.state x r (v - 1)).2 &&
        !(misOfColoring.state x r (v + 1)).2)) := by
  rw [Algorithm.state_succ, ← state_fst x r v]
  rfl

/-- The invariant after `r` rounds: joined nodes have colour at most `r`, every node of colour at
most `r` has joined or has a joined neighbour, and no two neighbours have joined. -/
theorem invariant {x : ZMod n → ℕ} (hx : IsProperColoring x) (r : ℕ) :
    (∀ v, (misOfColoring.state x r v).2 = true → x v ≤ r) ∧
    (∀ v, x v ≤ r → (misOfColoring.state x r v).2 = true ∨
      (misOfColoring.state x r (v - 1)).2 = true ∨ (misOfColoring.state x r (v + 1)).2 = true) ∧
    (∀ v, (misOfColoring.state x r v).2 = true → (misOfColoring.state x r (v + 1)).2 = false) := by
  induction r with
  | zero =>
    have hJ : ∀ v, (misOfColoring.state x 0 v).2 = decide (x v = 0) := fun v => rfl
    refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · rw [hJ] at hv
      simp_all
    · left
      rw [hJ]
      simp_all
    · rw [hJ] at hv ⊢
      have := hx v
      simp only [decide_eq_true_eq] at hv
      simp only [decide_eq_false_iff_not]
      omega
  | succ r ih =>
    obtain ⟨ha, hb, hc⟩ := ih
    refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · rw [state_snd_succ] at hv
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hv
      rcases hv with hv | ⟨⟨hv, -⟩, -⟩
      · exact (ha v hv).trans (Nat.le_succ r)
      · exact hv.le
    · simp only [state_snd_succ, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true']
      rcases Nat.lt_or_ge (x v) (r + 1) with hlt | hge
      · rcases hb v (by omega) with h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inr (Or.inl h))
      · have hxv : x v = r + 1 := le_antisymm hv hge
        by_cases h1 : (misOfColoring.state x r (v - 1)).2 = true
        · exact Or.inr (Or.inl (Or.inl h1))
        by_cases h2 : (misOfColoring.state x r (v + 1)).2 = true
        · exact Or.inr (Or.inr (Or.inl h2))
        simp only [Bool.not_eq_true] at h1 h2
        exact Or.inl (Or.inr ⟨⟨hxv, h1⟩, h2⟩)
    · rw [state_snd_succ] at hv ⊢
      have hxv : x v = r + 1 → x (v + 1) ≠ r + 1 := fun h h' => hx v (h.trans h'.symm)
      have hc' := hc v
      have hpred : misOfColoring.state x r (v + 1 - 1) = misOfColoring.state x r v := by
        rw [add_sub_cancel_right]
      rw [hpred]
      revert hv hc'
      cases misOfColoring.state x r v with
      | mk a b =>
      cases b <;> cases (misOfColoring.state x r (v + 1)).2 <;>
        cases (misOfColoring.state x r (v + 1 + 1)).2 <;>
        cases (misOfColoring.state x r (v - 1)).2 <;> simp_all

end misOfColoring

/-- **Colouring to MIS.** From a proper colouring with colours below `k`, `misOfColoring` marks a
maximal independent set within `k - 1` rounds, on every oriented cycle and on the infinite oriented
path. -/
theorem misOfColoring_run {n k : ℕ} {x : ZMod n → ℕ} (hx : IsProperColoring x)
    (hk : ∀ v, x v < k) {r : ℕ} (hr : k - 1 ≤ r) : IsMIS (misOfColoring.run x r) := by
  obtain ⟨-, hb, hc⟩ := misOfColoring.invariant hx r
  exact ⟨hc, fun v => hb v (by have := hk v; omega)⟩

/-- Cole–Vishkin with two reductions per round (`fastThreeColoring s`) for `s + 3` rounds, then
greedy colour classes on the resulting 3-colouring. -/
@[expose] def misAlgorithm (s : ℕ) : Algorithm ℕ (((ℤ → ℕ) × ℕ) × (ℕ × Bool)) Bool :=
  (fastThreeColoring s).seq (s + 3) misOfColoring

/-- From a proper colouring with colours below `N`, `misAlgorithm s` marks an MIS within `s + 5`
rounds when `log* N ≤ 2s`. -/
theorem misAlgorithm_run {n N s : ℕ} {x : ZMod n → ℕ} (hx : IsProperColoring x)
    (hN : ∀ v, x v < N) (hs : Nat.logStar N ≤ 2 * s) {r : ℕ} (hr : s + 5 ≤ r) :
    IsMIS ((misAlgorithm s).run x r) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
  have hrun : (misAlgorithm s).run x (s + 5 + j) =
      misOfColoring.run ((fastThreeColoring s).run x (s + 3)) (2 + j) := by
    funext v
    rw [show s + 5 + j = s + 3 + (2 + j) by omega, misAlgorithm, Algorithm.seq_run]
  obtain ⟨h1, h2⟩ := fastThreeColoring_run hx hN hs le_rfl
  rw [hrun]
  exact misOfColoring_run h1 h2 (by omega)

/-- **MIS upper bound.** On oriented `n`-cycles, `n ≠ 1`, with identifiers `{0, …, n - 1}`,
`misAlgorithm s` finds an MIS within `s + 5` rounds when `log* n ≤ 2s`, for instance for
`s = ⌈(log* n) / 2⌉`. -/
theorem misAlgorithm_findsMIS {n s : ℕ} (hn : n ≠ 1) (hs : Nat.logStar n ≤ 2 * s) {t : ℕ}
    (ht : s + 5 ≤ t) : (misAlgorithm s).FindsMIS n t := fun _ hx hxn =>
  misAlgorithm_run (IsProperColoring.of_injective hx hn) hxn hs ht

/-! ### From a maximal independent set to a 3-colouring -/

/-- One round from a maximal independent set to a 3-colouring: members get colour `0`, nodes whose
predecessor is a member colour `1`, and the remaining nodes colour `2`. -/
@[expose] def colorOfMIS : LocalRule Bool ℕ 1 where
  toFun w := if w 0 = true then 0 else if w (-1) = true then 1 else 2
  dependsOn w w' h := by
    change (if w 0 = true then 0 else if w (-1) = true then 1 else 2) =
      (if w' 0 = true then 0 else if w' (-1) = true then 1 else 2)
    rw [h 0 ⟨by decide, by decide⟩, h (-1) ⟨by decide, by decide⟩]

theorem colorOfMIS_apply {n : ℕ} (s : ZMod n → Bool) (v : ZMod n) :
    colorOfMIS.apply s v = if s v = true then 0 else if s (v - 1) = true then 1 else 2 := by
  change (if s (v + ((0 : ℤ) : ZMod n)) = true then 0
    else if s (v + ((-1 : ℤ) : ZMod n)) = true then 1 else 2) = _
  rw [Int.cast_zero, add_zero, Int.cast_neg, Int.cast_one, ← sub_eq_add_neg]

theorem colorOfMIS_apply_lt {n : ℕ} (s : ZMod n → Bool) (v : ZMod n) :
    colorOfMIS.apply s v < 3 := by
  rw [colorOfMIS_apply]
  split_ifs <;> decide

/-- **MIS to 3-colouring.** `colorOfMIS` turns a maximal independent set into a proper colouring.
-/
theorem IsMIS.colorOfMIS {n : ℕ} {s : ZMod n → Bool} (hs : IsMIS s) :
    IsProperColoring (colorOfMIS.apply s) := by
  intro v
  rw [colorOfMIS_apply, colorOfMIS_apply, add_sub_cancel_right]
  have hi := hs.1 v
  have hd := hs.2 v
  revert hi hd
  cases s v <;> cases s (v + 1) <;> cases s (v - 1) <;> simp

/-- **MIS lower bound.** A `t`-round MIS algorithm followed by `colorOfMIS` 3-colours in `t + 1`
rounds, so the 3-colouring lower bound `Algorithm.ColorsCycle.logStar_le_of_three` of
[Linial][Linial1992] gives `log* n ≤ 2t + 4`. -/
theorem Algorithm.FindsMIS.logStar_le {S : Type*} {A : Algorithm ℕ S Bool} {n t : ℕ}
    (hA : A.FindsMIS n t) : Nat.logStar n ≤ 2 * t + 4 := by
  have hC : (A.seq t colorOfMIS.toAlgorithm).ColorsCycle n (t + 1) 3 := by
    intro x hx hxn
    have hrun : (A.seq t colorOfMIS.toAlgorithm).run x (t + 1) = colorOfMIS.apply (A.run x t) := by
      funext v
      rw [Algorithm.seq_run, LocalRule.toAlgorithm_run]
    rw [hrun]
    exact ⟨(hA x hx hxn).colorOfMIS, colorOfMIS_apply_lt _⟩
  have := hC.logStar_le_of_three
  omega

/-- **The round complexity of MIS on oriented cycles is `Θ(log* n)`.** For `n ≠ 1`, some
deterministic LOCAL algorithm marks a maximal independent set of every oriented `n`-cycle with
identifiers `{0, …, n - 1}` within `⌈(log* n) / 2⌉ + 5` rounds, and every algorithm doing so within
`t` rounds has `log* n ≤ 2t + 4`. -/
theorem exists_findsMIS_and_logStar_le {n : ℕ} (hn : n ≠ 1) :
    (∃ (S : Type) (A : Algorithm ℕ S Bool), A.FindsMIS n ((Nat.logStar n + 1) / 2 + 5)) ∧
      ∀ {S : Type*} (A : Algorithm ℕ S Bool) (t : ℕ), A.FindsMIS n t →
        Nat.logStar n ≤ 2 * t + 4 :=
  ⟨⟨_, _, misAlgorithm_findsMIS hn (by omega) le_rfl⟩, fun _ _ hA => hA.logStar_le⟩

end Cslib.Distributed.OrientedCycle
