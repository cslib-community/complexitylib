/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Pigeonhole.Extension
public import CslibFrontier.Logics.Propositional.Resolution.ExistentialPebble
public import CslibFrontier.Logics.Propositional.Resolution.Space
import CslibFrontier.Logics.Propositional.Resolution.SpaceWidth

/-!
# Width and clause space of the extended pigeonhole formula

**The extended pigeonhole formula needs width and clause space at least the number of holes**
[Atserias and Dalmau, Lemma 6 and Theorem 3][AtseriasDalmau2008]. The extended pigeonhole formula
`EPHP^m_n` (`Cslib.Logic.PL.CNF.pigeonholeExt`) is a `3`-CNF encoding of the pigeonhole principle
with `n` holes. For every number of pigeons, every resolution refutation of it has width at least
`n` (`Cslib.Logic.PL.CNF.le_of_refutableInWidth_pigeonholeExt`) and clause space at least `n`
(`Cslib.Logic.PL.CNF.le_of_refutableInSpace_pigeonholeExt`). It is unsatisfiable exactly when
`m > n` (`Cslib.Logic.PL.CNF.satisfiable_pigeonholeExt_iff`).

Atserias and Dalmau prove the width bound by a winning strategy for Duplicator in the Boolean
existential pebble game (their Lemma 6), and note after their space–width inequality (Theorem 3)
that width lower bounds give space lower bounds, for the pigeonhole principle among others.

**The strategy** (`Cslib.Logic.PL.CNF.pigeonholeExtStrategy`), with `n + 1` holes and `n + 1`
pebbles, consists of the partial assignments that agree on their at most `n + 1` variables with
the placement `Cslib.Logic.PL.CNF.pigeonholeExtAssign f` of a map `f` from pigeons to holes
injective on the pigeons of these variables. Such a placement falsifies no clause on these
variables. To extend a position on fewer than `n + 1` variables by a variable of a new pigeon,
place that pigeon in a hole not used by the at most `n` pigeons of the position. With `n + 1`
pebbles this rules out refutations of width `n`
(`Cslib.Logic.PL.CNF.DuplicatorStrategy.not_refutableInWidth`). The space bound follows from the
Atserias–Dalmau inequality with the constant of Filmus, Lauria, Mikša, Nordström and Vinyals
(`Cslib.Logic.PL.CNF.RefutableInSpace.add_four_le`), for clauses of width at most `3`.

The mathematical symbols of the available copy of Atserias and Dalmau's paper do not extract, so
neither the exact clauses of their encoding nor the exact number of pebbles in their Lemma 6 is
quoted; the encoding, the strategy and the constants here are ours. Alekhnovich, Ben-Sasson,
Razborov and Wigderson [AlekhnovichBenSassonRazborovWigderson2002] proved clause-space lower bounds
for pigeonhole formulas directly; that paper was not inspected for this formalization. The exact
clause space `n + 2` of the wide formula `PHP^m_n` itself, after Torán, is in
`CslibFrontier.Logics.Propositional.Resolution.WidePigeonholeSpace`.

## Main definitions

* `Cslib.Logic.PL.CNF.pigeonholeExtStrategy`: Duplicator's strategy on `EPHP^m_{n+1}`.

## Main results

* `Cslib.Logic.PL.CNF.width_le_three_of_mem_pigeonholeExt`: the clauses of `EPHP^m_n` have width at
  most `3`.
* `Cslib.Logic.PL.CNF.not_refutableInWidth_pigeonholeExt`,
  `Cslib.Logic.PL.CNF.le_of_refutableInWidth_pigeonholeExt`: refutations of `EPHP^m_n` have width at
  least `n`.
* `Cslib.Logic.PL.CNF.le_of_refutableInSpace_pigeonholeExt`: refutations of `EPHP^m_n` need clause
  space at least `n`.

## References

* [A. Atserias, V. Dalmau, *A combinatorial characterization of resolution
  width*][AtseriasDalmau2008]
* [M. Alekhnovich, E. Ben-Sasson, A. Razborov, A. Wigderson, *Space complexity in propositional
  calculus*][AlekhnovichBenSassonRazborovWigderson2002]
* [Y. Filmus, M. Lauria, M. Mikša, J. Nordström, M. Vinyals, *From small space to small width in
  resolution*][FilmusLauriaMiksaNordstromVinyals2014]
-/

public section

namespace Cslib.Logic.PL

open scoped Finset

namespace CNF

variable {m n : ℕ}

/-- The clauses of `EPHP^m_n` have width at most `3`. -/
theorem width_le_three_of_mem_pigeonholeExt {c : Clause (PHPExtVar m n)}
    (hc : c ∈ pigeonholeExt m n) : c.width ≤ 3 :=
  (List.toFinset_card_le c).trans (length_le_three_of_mem_pigeonholeExt hc)

/-- A placement injective on the pigeons of `d` falsifies no clause of `EPHP^m_n` on `d`. -/
private theorem not_falsifies_pigeonholeExtAssign {f : Fin m → Fin n} {d : Finset (PHPExtVar m n)}
    (hf : Set.InjOn f (d.image PHPExtVar.pigeon)) {c : Clause (PHPExtVar m n)}
    (hc : c ∈ pigeonholeExt m n) : ¬ Falsifies (pigeonholeExtAssign f) d c := by
  intro h
  rcases mem_pigeonholeExt.1 hc with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, j, rfl⟩ | ⟨i, i', j, hii', rfl⟩
  · have := (h _ List.mem_cons_self).2
    simp [pigeonholeExtAssign] at this
  · have h₁ := (h _ List.mem_cons_self).2
    have h₂ := (f i).isLt
    simp only [pigeonholeExtAssign, Fin.val_last, ne_eq, Bool.not_eq_false, decide_eq_true_eq] at h₁
    omega
  · have h₁ := (h (.inr (i, j.castSucc), false) (by simp [phpStepClause])).2
    have h₂ := (h (.inl (i, j), true) (by simp [phpStepClause])).2
    have h₃ := (h (.inr (i, j.succ), true) (by simp [phpStepClause])).2
    simp only [pigeonholeExtAssign, ne_eq, Bool.not_eq_false, decide_eq_true_eq, Fin.val_castSucc,
      Fin.val_succ, Fin.ext_iff] at h₁ h₂ h₃
    omega
  · have h₁ := h (.inl (i, j), false) (by simp [phpExtHoleClause])
    have h₂ := h (.inl (i', j), false) (by simp [phpExtHoleClause])
    simp only [pigeonholeExtAssign, ne_eq, decide_eq_false_iff_not, not_not] at h₁ h₂
    exact hii'.ne (hf (Finset.mem_coe.2 (Finset.mem_image_of_mem _ h₁.1))
      (Finset.mem_coe.2 (Finset.mem_image_of_mem _ h₂.1)) (h₁.2.trans h₂.2.symm))

/-- The positions of Duplicator's strategy on `EPHP^m_{n+1}`: partial assignments on at most
`n + 1` variables that agree with the placement of a map injective on their pigeons. -/
private def PHPPos (n : ℕ) (σ : PHPExtVar m (n + 1) → Bool) (d : Finset (PHPExtVar m (n + 1))) :
    Prop :=
  #d ≤ n + 1 ∧ ∃ f : Fin m → Fin (n + 1), Set.InjOn f (d.image PHPExtVar.pigeon) ∧
    ∀ x ∈ d, σ x = pigeonholeExtAssign f x

/-- **Duplicator's strategy on the extended pigeonhole formula** with `n + 1` holes and `n + 1`
pebbles: partial assignments that agree with the placement of a map from pigeons to holes injective
on their pigeons. A new pigeon goes to a hole not used by the at most `n` pigeons already
pebbled. -/
def pigeonholeExtStrategy (m n : ℕ) : DuplicatorStrategy (pigeonholeExt m (n + 1)) (n + 1) where
  Mem := PHPPos n
  nonempty := ⟨fun _ => false, ∅, by simp, fun _ => 0, by simp, by simp⟩
  card_le h := h.1
  restrict := by
    rintro σ d e ⟨hcard, f, hf, hσ⟩ hed
    exact ⟨(Finset.card_le_card hed).trans hcard, f,
      hf.mono (Finset.coe_subset.2 (Finset.image_subset_image hed)), fun x hx => hσ x (hed hx)⟩
  extend := by
    rintro σ d ⟨-, f, hf, hσ⟩ hd v
    by_cases hv : v.pigeon ∈ d.image PHPExtVar.pigeon
    · -- the pigeon of `v` is already placed
      refine ⟨pigeonholeExtAssign f, fun x hx => (hσ x hx).symm, ?_, f, ?_, fun x _ => rfl⟩
      · exact (Finset.card_insert_le _ _).trans hd
      · rwa [Finset.image_insert, Finset.insert_eq_of_mem hv]
    · -- place the pigeon of `v` in a hole used by no pigeon of `d`
      obtain ⟨j, hj⟩ : ∃ j, j ∉ (d.image PHPExtVar.pigeon).image f := by
        by_contra! hall
        have := (Finset.card_le_card fun j (_ : j ∈ Finset.univ) => hall j).trans
          (Finset.card_image_le.trans Finset.card_image_le)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        omega
      refine ⟨pigeonholeExtAssign (Function.update f v.pigeon j), fun x hx => ?_, ?_,
        Function.update f v.pigeon j, ?_, fun x _ => rfl⟩
      · have hx' : x.pigeon ≠ v.pigeon := fun he => hv (he ▸ Finset.mem_image_of_mem _ hx)
        rw [hσ x hx]
        rcases x with ⟨i, k⟩ | ⟨i, k⟩
        · have hi : i ≠ v.pigeon := hx'
          simp only [pigeonholeExtAssign, Function.update_of_ne hi]
        · have hi : i ≠ v.pigeon := hx'
          simp only [pigeonholeExtAssign, Function.update_of_ne hi]
      · exact (Finset.card_insert_le _ _).trans hd
      · rw [Finset.image_insert, Finset.coe_insert, Set.injOn_insert (by simpa using hv)]
        have heq : Set.EqOn f (Function.update f v.pigeon j) ↑(d.image PHPExtVar.pigeon) :=
          fun x hx => (Function.update_of_ne (fun he : x = v.pigeon => hv
            (by rw [← he]; exact Finset.mem_coe.1 hx)) _ _).symm
        refine ⟨hf.congr heq, ?_⟩
        rw [← heq.image_eq, Function.update_self, ← Finset.coe_image, Finset.mem_coe]
        exact hj
  not_falsifies := by
    rintro σ d ⟨-, f, hf, hσ⟩ c hc hfal
    exact not_falsifies_pigeonholeExtAssign hf hc (hfal.congr fun x hx => (hσ x hx).symm)

/-- **`EPHP^m_{n+1}` has no refutation of width `n`** [Atserias and Dalmau, Lemmas 3 and 6]
[AtseriasDalmau2008]. -/
theorem not_refutableInWidth_pigeonholeExt (m n : ℕ) :
    ¬ (pigeonholeExt m (n + 1)).RefutableInWidth n :=
  (pigeonholeExtStrategy m n).not_refutableInWidth

/-- **Refutations of the extended pigeonhole formula have width at least the number of holes**
[Atserias and Dalmau, Lemmas 3 and 6][AtseriasDalmau2008]: if `EPHP^m_n` is refutable in width
`w`, then `n ≤ w`. -/
theorem le_of_refutableInWidth_pigeonholeExt {w : ℕ}
    (h : (pigeonholeExt m n).RefutableInWidth w) : n ≤ w := by
  obtain _ | n := n
  · exact Nat.zero_le _
  · by_contra! hw
    exact not_refutableInWidth_pigeonholeExt m n (h.mono (by omega))

/-- **Refutations of the extended pigeonhole formula need clause space at least the number of
holes** [Atserias and Dalmau, Lemma 6 and Theorem 3][AtseriasDalmau2008]: if `EPHP^m_n` is
refutable in clause space `s`, then `n ≤ s`. This is the width bound through the Atserias–Dalmau
inequality with the constant of Filmus, Lauria, Mikša, Nordström and Vinyals, Theorem 1
[FilmusLauriaMiksaNordstromVinyals2014], for clauses of width at most `3`. -/
theorem le_of_refutableInSpace_pigeonholeExt {s : ℕ}
    (h : (pigeonholeExt m n).RefutableInSpace s) : n ≤ s := by
  obtain _ | n := n
  · exact Nat.zero_le _
  · have := h.add_four_le (fun _ hc => width_le_three_of_mem_pigeonholeExt hc)
      (not_refutableInWidth_pigeonholeExt m n)
    omega

end CNF

end Cslib.Logic.PL
