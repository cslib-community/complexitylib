/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Distributed.OrientedCycle.Linial
public import Cslib.Foundations.Relation.RelatesInSteps

/-!
# Locally checkable labellings on oriented cycles

A *locally checkable labelling* (LCL) problem without inputs on consistently oriented cycles is
given by a label type `L` and a relation `R : L → L → Prop`. A labelling `ℓ` of the oriented
`n`-cycle solves `R` if `R (ℓ v) (ℓ (v + 1))` holds for every node `v` (`LCL.IsSolution`). In
other words, a solution is a closed walk of length `n` in the digraph `R` on `L`.

This is the automaton view of [Chang, Studený and Suomela][ChangStudenySuomela2023]. Their
node-edge-checkable problems (Def. 2.1 and 2.2 of arXiv:2002.07659v3) are the instance
`LCL.nodeEdge`. A node is labelled by the port labels of its outgoing edge, and on these labels
the relation `R` is the automaton `M_Π` of their §2.2 (`LCL.nodeEdge_iff`). Proper `k`-colourings
(`R := (· ≠ ·)` on `Fin k`) and maximal independent sets (`L := Bool × Bool`, see the tests) are
examples. A loop of `M_Π` (their Def. 3.3) is a label `a` with `R a a`. A flexible state
(their Def. 3.2, credited to [Brandt et al.][BrandtEtAl2017]) is a label `q` with closed walks
`q ⇝ q` of every length `m ≥ K` (`LCL.IsFlexible`), stated with cslib's
`Relation.RelatesInSteps`.

This file proves the first gap of their classification on directed cycles (Table 1):

* With a loop `R a a`, the constant algorithm solves `R` in `0` rounds on every cycle
  (`Algorithm.solvesLCL_const`; [Chang, Studený and Suomela][ChangStudenySuomela2023], Thm 6.9).
* Without a loop, every solution is a proper colouring with `|L|` colours, so every `t`-round
  algorithm solving `R` on the `n`-cycle has `log* n ≤ 2t + log* |L|`
  (`Algorithm.SolvesLCL.logStar_le`). This is their Thm 6.1. Their proof reduces to edge
  3-colouring; here the bound comes from the speedup-lemma proof of the lower bound of
  [Linial][Linial1992] by [Laurinharju and Suomela][LaurinharjuSuomela2014], already in the
  library.
* Hence an algorithm faster than `½ (log* n − log* |L|)` rounds forces a loop
  (`Algorithm.SolvesLCL.exists_loop`). With `0` rounds, `n > |L|` suffices
  (`Algorithm.SolvesLCL.exists_loop_of_zero`).

Flexible problems are solved in `O(log* n)` rounds in
`Complexity.Computability.Distributed.OrientedCycle.LCL.Flexible`. Problems without a flexible
state need `Θ(n)` rounds (`Complexity.Computability.Distributed.OrientedCycle.LCL.Linear`), and
`Complexity.Computability.Distributed.OrientedCycle.LCL.Classification` assembles the
three-way classification.

## Main definitions

* `Cslib.Distributed.OrientedCycle.LCL.IsSolution`: `ℓ` solves `R` on the oriented `n`-cycle.
* `Cslib.Distributed.OrientedCycle.LCL.nodeEdge`: node-edge-checkable problems as LCLs.
* `Cslib.Distributed.OrientedCycle.LCL.IsFlexible`: `q` is a flexible state with flexibility `K`.
* `Cslib.Distributed.OrientedCycle.Algorithm.SolvesLCL`: `A` solves `R` on every oriented
  `n`-cycle with identifiers `{0, …, n - 1}` in `t` rounds.

## Main results

* `Cslib.Distributed.OrientedCycle.LCL.isSolution_nodeEdge_iff`: solutions of `nodeEdge` are the
  solutions of the node-edge-checkable problem.
* `Cslib.Distributed.OrientedCycle.LCL.IsFlexible.of_two_three`: closed walks of lengths `2` and
  `3` make a state flexible with flexibility `2`.
* `Cslib.Distributed.OrientedCycle.Algorithm.solvesLCL_const`: a loop gives a 0-round algorithm.
* `Cslib.Distributed.OrientedCycle.Algorithm.SolvesLCL.logStar_le`: without a loop,
  `log* n ≤ 2t + log* |L|`.
* `Cslib.Distributed.OrientedCycle.Algorithm.SolvesLCL.exists_loop`: the `ω(1)`/`o(log* n)` gap.

## References

* [Y.-J. Chang, J. Studený and J. Suomela, *Distributed graph problems through an
  automata-theoretic lens*][ChangStudenySuomela2023]
* [S. Brandt et al., *LCL problems on grids*][BrandtEtAl2017]
* [N. Linial, *Locality in distributed graph algorithms*][Linial1992]
* [J. Laurinharju and J. Suomela, *Brief announcement: Linial's lower bound made
  easy*][LaurinharjuSuomela2014]
-/

public section

namespace Cslib.Distributed.OrientedCycle

namespace LCL

variable {L : Type*} {R : L → L → Prop}

/-- A labelling `ℓ` of the oriented `n`-cycle solves the LCL problem `R` if every node and its
successor are related by `R`. -/
@[expose] def IsSolution (R : L → L → Prop) {n : ℕ} (ℓ : ZMod n → L) : Prop :=
  ∀ v : ZMod n, R (ℓ v) (ℓ (v + 1))

instance (R : L → L → Prop) [DecidableRel R] {n : ℕ} [NeZero n] (ℓ : ZMod n → L) :
    Decidable (IsSolution R ℓ) :=
  inferInstanceAs (Decidable (∀ v : ZMod n, R (ℓ v) (ℓ (v + 1))))

/-- Without a loop, a solution is a proper colouring. -/
theorem IsSolution.isProperColoring (hR : ∀ a, ¬R a a) {n : ℕ} {ℓ : ZMod n → L}
    (h : IsSolution R ℓ) : IsProperColoring ℓ := fun v hv => hR _ (hv ▸ h v)

/-! ### Node-edge-checkable problems -/

/-- The node-edge-checkable problem with edge constraint `Cedge` and node constraint `Cnode` on
directed cycles ([Chang, Studený and Suomela][ChangStudenySuomela2023], Def. 2.1 and 2.2), as an
LCL. Node `v` is labelled by the pair `(tail port, head port)` of labels of its outgoing edge
`(v, v + 1)`. The edge `(v, v + 1)` is checked by `Cedge`, and node `v + 1`, whose head port lies
on the edge `(v, v + 1)` and whose tail port lies on the edge `(v + 1, v + 2)`, by `Cnode`. -/
@[expose] def nodeEdge {Γ : Type*} (Cedge Cnode : Γ → Γ → Prop) (p p' : Γ × Γ) : Prop :=
  Cedge p.1 p.2 ∧ Cnode p.2 p'.1 ∧ Cedge p'.1 p'.2

instance {Γ : Type*} (Cedge Cnode : Γ → Γ → Prop) [DecidableRel Cedge] [DecidableRel Cnode] :
    DecidableRel (nodeEdge Cedge Cnode) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Solutions of `nodeEdge Cedge Cnode` are the solutions of the node-edge-checkable problem: every
edge satisfies `Cedge` and every node satisfies `Cnode`. -/
theorem isSolution_nodeEdge_iff {Γ : Type*} {Cedge Cnode : Γ → Γ → Prop} {n : ℕ}
    (ℓ : ZMod n → Γ × Γ) :
    IsSolution (nodeEdge Cedge Cnode) ℓ ↔
      (∀ v, Cedge (ℓ v).1 (ℓ v).2) ∧ ∀ v, Cnode (ℓ v).2 (ℓ (v + 1)).1 :=
  ⟨fun h => ⟨fun v => (h v).1, fun v => (h v).2.1⟩, fun h v => ⟨h.1 v, h.2 v, h.1 (v + 1)⟩⟩

/-- On the states `C_edge`, `nodeEdge` is the transition relation of the automaton `M_Π` of
[Chang, Studený and Suomela][ChangStudenySuomela2023], §2.2: `(a, b) → (c, d)` iff
`(b, c) ∈ C_node`. Labels outside `C_edge` have no transitions. -/
theorem nodeEdge_iff {Γ : Type*} {Cedge Cnode : Γ → Γ → Prop} {a b c d : Γ} (hab : Cedge a b)
    (hcd : Cedge c d) : nodeEdge Cedge Cnode (a, b) (c, d) ↔ Cnode b c :=
  ⟨fun h => h.2.1, fun h => ⟨hab, h, hcd⟩⟩

/-! ### Flexibility -/

/-- The state `q` is *flexible* with flexibility `K` if there are closed walks `q ⇝ q` of every
length `m ≥ K` ([Chang, Studený and Suomela][ChangStudenySuomela2023], Def. 3.2, credited to
[Brandt et al.][BrandtEtAl2017]). A walk of length exactly `m` is cslib's
`Relation.RelatesInSteps R q q m`. -/
@[expose] def IsFlexible (R : L → L → Prop) (q : L) (K : ℕ) : Prop :=
  ∀ m, K ≤ m → Relation.RelatesInSteps R q q m

theorem IsFlexible.mono {q : L} {K K' : ℕ} (h : IsFlexible R q K) (hK : K ≤ K') :
    IsFlexible R q K' := fun m hm => h m (hK.trans hm)

/-- A loop is flexible with flexibility `0`. -/
theorem IsFlexible.of_loop {q : L} (h : R q q) : IsFlexible R q 0 := by
  intro m _
  induction m with
  | zero => exact .refl q
  | succ m ih => exact .tail _ q q m (ih (Nat.zero_le _)) h

/-- Closed walks of lengths `2` and `3` make `q` flexible with flexibility `2`. -/
theorem IsFlexible.of_two_three {q : L} (h2 : Relation.RelatesInSteps R q q 2)
    (h3 : Relation.RelatesInSteps R q q 3) : IsFlexible R q 2 := by
  intro m hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 4 with hm4 | hm4
    · obtain rfl | rfl : m = 2 ∨ m = 3 := by omega
      · exact h2
      · exact h3
    · have := (ih (m - 2) (by omega) (by omega)).trans h2
      rwa [Nat.sub_add_cancel (by omega)] at this

end LCL

/-! ### Algorithms solving LCL problems -/

/-- After `t` rounds, `A` solves the LCL problem `R` on every oriented `n`-cycle whose nodes carry
distinct identifiers from `{0, …, n - 1}`. This is vacuous for `n = 0`. -/
@[expose] def Algorithm.SolvesLCL {S L : Type*} (A : Algorithm ℕ S L) (R : L → L → Prop)
    (n t : ℕ) : Prop :=
  ∀ x : ZMod n → ℕ, Function.Injective x → (∀ v, x v < n) → LCL.IsSolution R (A.run x t)

/-- **Problems with a loop** ([Chang, Studený and Suomela][ChangStudenySuomela2023], Thm 6.9). If
`R a a`, the algorithm with constant output `a` solves `R` in `0` rounds. -/
theorem Algorithm.solvesLCL_const {L : Type*} {R : L → L → Prop} {a : L} (ha : R a a) (n t : ℕ) :
    (Algorithm.const a : Algorithm ℕ Unit L).SolvesLCL R n t := fun _ _ _ _ => ha

namespace Algorithm.SolvesLCL

variable {S L : Type*} [Fintype L] {A : Algorithm ℕ S L} {R : L → L → Prop} {n t : ℕ}

/-- Without a loop, a `t`-round algorithm solving `R` on the `n`-cycle has
`n ≤ 2 ^ 2 ^ ⋯ ^ |L|` with `2t` exponentials. -/
theorem le_iterate (hR : ∀ a, ¬R a a) (hA : A.SolvesLCL R n t) :
    n ≤ (2 ^ ·)^[2 * t] (Fintype.card L) :=
  A.le_iterate_of_isProperColoring fun x hx hxn => (hA x hx hxn).isProperColoring hR

/-- **Problems without a loop need `Ω(log* n)` rounds** ([Chang, Studený and
Suomela][ChangStudenySuomela2023], Thm 6.1), via the lower bound of [Linial][Linial1992] in the
form of [Laurinharju and Suomela][LaurinharjuSuomela2014]: a `t`-round algorithm solving `R` on
the `n`-cycle has `log* n ≤ 2t + log* |L|`. The source also assumes a repeatable state, so that
solvable instances of every size exist. This per-`n` form does not need it: if the `n`-cycle has
no solution, then no algorithm solves `R` on it. -/
theorem logStar_le (hR : ∀ a, ¬R a a) (hA : A.SolvesLCL R n t) :
    Nat.logStar n ≤ 2 * t + Nat.logStar (Fintype.card L) :=
  Nat.logStar_le_iff.2 ((hA.le_iterate hR).trans (Nat.iterate_two_pow_le_twoTower _ _))

/-- **The `ω(1)`/`o(log* n)` gap.** An algorithm solving `R` on the `n`-cycle in fewer than
`½ (log* n − log* |L|)` rounds forces a loop `R a a`, and then `0` rounds suffice
(`Algorithm.solvesLCL_const`). -/
theorem exists_loop (hA : A.SolvesLCL R n t)
    (ht : 2 * t + Nat.logStar (Fintype.card L) < Nat.logStar n) : ∃ a, R a a := by
  by_contra h
  push Not at h
  exact absurd (hA.logStar_le h) (by omega)

/-- A 0-round algorithm solving `R` on a cycle with more than `|L|` nodes forces a loop. -/
theorem exists_loop_of_zero (hA : A.SolvesLCL R n 0) (hn : Fintype.card L < n) : ∃ a, R a a := by
  by_contra h
  push Not at h
  have := hA.le_iterate h
  rw [Nat.mul_zero, Function.iterate_zero, id_eq] at this
  omega

end Algorithm.SolvesLCL

end Cslib.Distributed.OrientedCycle
