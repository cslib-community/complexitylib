/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Resolution.Space
public import Complexity.Logics.Propositional.Resolution.TreeLike
public import Mathlib.Data.Nat.Log

/-!
# Clause space of tree-like refutations

**Esteban and Torán's bound**: clause space is at most logarithmic in tree-like size. In the form of
[Torán, Theorem 9][Toran2004], credited there to Esteban and Torán [EstebanToran2001], an
unsatisfiable formula `F` has `tree-size(F) ≥ 2 ^ space(F) - 1`.

The proof in that survey pebbles a tree-like refutation with `d + 1` pebbles, where `d` is the
height of the largest complete binary tree embedded in it. This is the **Horton–Strahler number**
of the derivation (`Cslib.Logic.PL.CNF.Derivation.strahler`): `0` at a leaf, and at a resolution
step the larger of the numbers of the two premises, plus one if they are equal. It is the
Ehrenfeucht–Haussler rank (`Cslib.DecisionTree.rank`) of the decision tree of the derivation
(`Cslib.Logic.PL.CNF.Derivation.strahler_eq_rank_toDecisionTree`). To derive the conclusion, derive
first the premise of larger number, keep it, and derive the other
(`Cslib.Logic.PL.CNF.Derivation.exists_configLTS_mTr`). A derivation of Strahler number `r` embeds
a complete binary tree of height `r`, so it has at least `2 ^ (r + 1) - 1` nodes
(`Cslib.Logic.PL.CNF.Derivation.two_pow_strahler_add_one_le`, from
`Cslib.DecisionTree.two_pow_rank_le_leafCount`).

**Convention.** The pebble game of the survey [Torán, Definition 7 and Lemma 8][Toran2004] lets an
inference shift a pebble from a premise to the resolvent, so `x ∧ ¬x` is refuted with two pebbles.
Configurations here (`Cslib.Logic.PL.CNF.configLTS`) keep both premises while they add the
resolvent, as in Filmus, Lauria, Mikša, Nordström and Vinyals
[FilmusLauriaMiksaNordstromVinyals2014], so `x ∧ ¬x` needs clause space `3`
(`Cslib.Logic.PL.CNF.RefutableInSpace.three_le`), and every bound below is one larger than its
counterpart in the survey:

* a tree-like refutation of Strahler number `r` gives clause space `r + 2`
  (`Cslib.Logic.PL.CNF.Derivation.refutableInSpace`), as the complete binary tree of height `h ≥ 1`
  has black pebbling price `h + 2` (`Cslib.Pebbling.blackPebblingPrice_completeBinaryTree_root`);
* a tree-like refutation of `S` nodes gives clause space `log₂ (S + 1) + 1`
  (`Cslib.Logic.PL.CNF.Derivation.refutableInSpace_log`);
* equivalently, if `φ` is not refutable in clause space `s`, every tree-like refutation has
  `2 ^ s ≤ S + 1` nodes (`Cslib.Logic.PL.CNF.Derivation.two_pow_le_size_add_one`). This is the
  inequality of the survey in this convention; `x ∧ ¬x` attains it.

**Every unsatisfiable formula on `n` variables is refutable in clause space `n + 2`**
(`Cslib.Logic.PL.CNF.refutableInSpace_of_not_satisfiable`), the survey's bound `n + 1`
[Torán, Section 4][Toran2004] in this convention: splitting on a variable gives a tree-like
refutation of Strahler number at most `n` (`Cslib.Logic.PL.CNF.exists_derivation_strahler_le`).

The original paper of Esteban and Torán was not inspected for this formalization.

## Main definitions

* `Cslib.Logic.PL.CNF.Derivation.strahler`: the Horton–Strahler number of a tree-like derivation.

## Main results

* `Cslib.Logic.PL.CNF.Derivation.strahler_eq_rank_toDecisionTree`: the Strahler number is the
  Ehrenfeucht–Haussler rank of the decision tree of the derivation.
* `Cslib.Logic.PL.CNF.Derivation.two_pow_strahler_add_one_le`: `2 ^ (r + 1) ≤ S + 1`.
* `Cslib.Logic.PL.CNF.Derivation.exists_configLTS_mTr`,
  `Cslib.Logic.PL.CNF.Derivation.refutableInSpace`: clause space at most `r + 2`.
* `Cslib.Logic.PL.CNF.Derivation.refutableInSpace_log`,
  `Cslib.Logic.PL.CNF.Derivation.two_pow_le_size_add_one`: **Esteban and Torán's bound**.
* `Cslib.Logic.PL.CNF.Derivation.exists_of_restrict`: lifting a tree-like derivation from a
  restriction, preserving its Strahler number.
* `Cslib.Logic.PL.CNF.exists_derivation_strahler_le`,
  `Cslib.Logic.PL.CNF.refutableInSpace_of_not_satisfiable`: clause space at most `n + 2`.

## References

* [J. L. Esteban, J. Torán, *Space bounds for resolution*][EstebanToran2001]
* [Y. Filmus, M. Lauria, M. Mikša, J. Nordström, M. Vinyals, *From small space to small width in
  resolution*][FilmusLauriaMiksaNordstromVinyals2014]
* [J. Torán, *Space and width in propositional resolution*][Toran2004]
-/

@[expose] public section

namespace Cslib.Logic.PL

open scoped Finset

variable {V : Type*} [DecidableEq V]

namespace CNF

variable {φ : CNF V} {c : Clause V}

namespace Derivation

/-! ### The Horton–Strahler number -/

/-- The **Horton–Strahler number** of a tree-like derivation: `0` at a leaf, and at a resolution
step the larger of the numbers of the two premises, plus one if they are equal. It is the height of
the largest complete binary tree embedded in the derivation [Torán, Theorem 9][Toran2004], and the
Ehrenfeucht–Haussler rank `Cslib.DecisionTree.rank` of the decision tree of the derivation
(`Cslib.Logic.PL.CNF.Derivation.strahler_eq_rank_toDecisionTree`). -/
def strahler : {c : Clause V} → φ.Derivation c → ℕ
  | _, mem _ => 0
  | _, resolvent _ d₁ d₂ _ _ =>
    if d₁.strahler = d₂.strahler then d₁.strahler + 1 else max d₁.strahler d₂.strahler

/-- A leaf has Strahler number `0`. -/
@[simp] theorem strahler_mem (hc : c ∈ φ) : (mem hc).strahler = 0 := rfl

/-- The Strahler number of a resolution step. -/
theorem strahler_resolvent {c₁ c₂ : Clause V} (v : V) (d₁ : φ.Derivation c₁)
    (d₂ : φ.Derivation c₂) (hv₁ : (v, true) ∈ c₁) (hv₂ : (v, false) ∈ c₂) :
    (resolvent v d₁ d₂ hv₁ hv₂).strahler =
      if d₁.strahler = d₂.strahler then d₁.strahler + 1 else max d₁.strahler d₂.strahler := rfl

/-- The Strahler number of a tree-like derivation is the Ehrenfeucht–Haussler rank of its decision
tree. -/
theorem strahler_eq_rank_toDecisionTree : {c : Clause V} → (d : φ.Derivation c) →
    d.strahler = d.toDecisionTree.rank
  | _, mem _ => rfl
  | _, resolvent v d₁ d₂ _ _ => by
    rw [strahler_resolvent, strahler_eq_rank_toDecisionTree d₁, strahler_eq_rank_toDecisionTree d₂]
    rfl

/-- A tree-like derivation of Strahler number `r` has at least `2 ^ (r + 1) - 1` nodes: its decision
tree has at least `2 ^ r` leaves (`Cslib.DecisionTree.two_pow_rank_le_leafCount`). -/
theorem two_pow_strahler_add_one_le {c : Clause V} (d : φ.Derivation c) :
    2 ^ (d.strahler + 1) ≤ d.size + 1 := by
  have h₁ := d.toDecisionTree.two_pow_rank_le_leafCount
  have h₂ := d.two_mul_leafCount_toDecisionTree
  rw [strahler_eq_rank_toDecisionTree, pow_succ]
  omega

/-! ### Clause space -/

/-- Deriving two clauses one after the other from `K`, the one of larger Strahler number first. -/
private theorem exists_mTr_pair {ca cb : Clause V} {ra rb r : ℕ}
    (ha : ∀ K : Finset (Clause V), ∃ ms, (φ.configLTS (#K + ra + 2)).MTr K ms (insert ca K))
    (hb : ∀ K : Finset (Clause V), ∃ ms, (φ.configLTS (#K + rb + 2)).MTr K ms (insert cb K))
    (hra : ra ≤ r) (hrb : rb + 1 ≤ r) (K : Finset (Clause V)) :
    ∃ ms, (φ.configLTS (#K + r + 2)).MTr K ms (insert cb (insert ca K)) := by
  obtain ⟨ms₁, h₁⟩ := ha K
  obtain ⟨ms₂, h₂⟩ := hb (insert ca K)
  have := Finset.card_insert_le ca K
  exact ⟨ms₁ ++ ms₂, LTS.MTr.comp _ (configLTS_mTr_mono (t := #K + r + 2) (by omega) h₁)
    (configLTS_mTr_mono (t := #K + r + 2) (by omega) h₂)⟩

/-- A tree-like derivation of `c` of Strahler number `r` runs from any configuration `K` to
`insert c K` with at most `|K| + r + 2` clauses at a time: derive the premise of larger number,
then the other, resolve them, and erase both. -/
theorem exists_configLTS_mTr : {c : Clause V} → (d : φ.Derivation c) → (K : Finset (Clause V)) →
    ∃ ms, (φ.configLTS (#K + d.strahler + 2)).MTr K ms (insert c K)
  | _, mem hc, K => ⟨[.download _], .stepL ⟨.download hc, by
      rw [strahler_mem]; exact (Finset.card_insert_le _ _).trans (by omega)⟩ .refl⟩
  | _, resolvent (c₁ := c₁) (c₂ := c₂) v d₁ d₂ hv₁ hv₂, K => by
    have ih₁ := exists_configLTS_mTr d₁
    have ih₂ := exists_configLTS_mTr d₂
    have hr := strahler_resolvent v d₁ d₂ hv₁ hv₂
    set r := (resolvent v d₁ d₂ hv₁ hv₂).strahler
    obtain ⟨ms, hms⟩ : ∃ ms, (φ.configLTS (#K + r + 2)).MTr K ms (insert c₂ (insert c₁ K)) := by
      by_cases h : d₂.strahler ≤ d₁.strahler
      · exact exists_mTr_pair ih₁ ih₂ (by split_ifs at hr <;> omega)
          (by split_ifs at hr <;> omega) K
      · rw [Finset.insert_comm]
        exact exists_mTr_pair ih₂ ih₁ (by split_ifs at hr <;> omega)
          (by split_ifs at hr <;> omega) K
    have hr1 : 1 ≤ r := by split_ifs at hr <;> omega
    have hK : #(insert c₂ (insert c₁ K)) ≤ #K + 2 :=
      (Finset.card_insert_le _ _).trans (by have := Finset.card_insert_le c₁ K; omega)
    have hinf : (φ.configLTS (#K + r + 2)).Tr (insert c₂ (insert c₁ K)) (.infer c₁ c₂ v)
        (insert (c₁.resolvent c₂ v) (insert c₂ (insert c₁ K))) :=
      ⟨.infer v (by simp) (by simp) hv₁ hv₂, (Finset.card_insert_le _ _).trans (by omega)⟩
    obtain ⟨ms', hms'⟩ := exists_configLTS_mTr_of_subset (φ := φ) (s := #K + r + 2)
      (N := insert (c₁.resolvent c₂ v) K)
      (Finset.insert_subset_insert _ fun _ hx =>
        Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
      ((Finset.card_insert_le _ (insert c₂ (insert c₁ K))).trans (by omega))
    exact ⟨ms ++ .infer c₁ c₂ v :: ms', LTS.MTr.comp _ hms (.stepL hinf hms')⟩

/-- **A tree-like refutation of Strahler number `r` gives clause space `r + 2`.** -/
theorem refutableInSpace (d : φ.Derivation []) : φ.RefutableInSpace (d.strahler + 2) := by
  obtain ⟨ms, h⟩ := d.exists_configLTS_mTr ∅
  exact ⟨ms, insert [] ∅, by simpa only [Finset.card_empty, zero_add] using h,
    Finset.mem_insert_self _ _⟩

/-- **Esteban and Torán's bound** [Torán, Theorem 9][Toran2004] [EstebanToran2001]: a tree-like
refutation of `S` nodes gives clause space `log₂ (S + 1) + 1`. The space of the survey, for a pebble
game that shifts a pebble from a premise to the resolvent, is at most one less than clause space
here, so its bound `log₂ (S + 1)` implies this one. -/
theorem refutableInSpace_log (d : φ.Derivation []) :
    φ.RefutableInSpace (Nat.log 2 (d.size + 1) + 1) :=
  d.refutableInSpace.mono <| by
    have := Nat.le_log_of_pow_le (by norm_num) d.two_pow_strahler_add_one_le
    omega

/-- **Esteban and Torán's bound** [Torán, Theorem 9][Toran2004] [EstebanToran2001], as a lower bound
on tree-like size: if `φ` is not refutable in clause space `s`, every tree-like refutation of `φ`
has at least `2 ^ s - 1` nodes. The survey states `tree-size(F) ≥ 2 ^ space(F) - 1` for a pebble
game that shifts a pebble from a premise to the resolvent, whose space is at most one less than
clause space here. -/
theorem two_pow_le_size_add_one (d : φ.Derivation []) {s : ℕ} (h : ¬ φ.RefutableInSpace s) :
    2 ^ s ≤ d.size + 1 := by
  have hs : s ≤ d.strahler + 1 := by
    by_contra hs
    exact h (d.refutableInSpace.mono (by omega))
  exact (Nat.pow_le_pow_right (by norm_num) hs).trans d.two_pow_strahler_add_one_le

/-! ### Formulas on `n` variables -/

/-- **Lifting a tree-like derivation**: a tree-like derivation from `φ` with `v` fixed to `b` lifts
to a tree-like derivation from `φ` of the same Strahler number, whose conclusion contains the
original one and has, besides its literals, at most the literal `(v, !b)` falsified by `b`. -/
theorem exists_of_restrict {v : V} {b : Bool} (d : (φ.restrict v b).Derivation c) :
    ∃ (c' : Clause V) (d' : φ.Derivation c'), (∀ l ∈ c', l ∈ c ∨ l = (v, !b)) ∧
      (∀ l ∈ c, l ∈ c') ∧ d'.strahler = d.strahler := by
  induction d with
  | mem hc =>
    obtain ⟨d, hd, -, rfl⟩ := mem_restrict.1 hc
    refine ⟨d, .mem hd, fun l hl => ?_, fun l hl => (List.mem_filter.1 hl).1, rfl⟩
    by_cases hlv : l = (v, !b)
    · exact Or.inr hlv
    · exact Or.inl (List.mem_filter.2 ⟨hl, by simpa using hlv⟩)
  | @resolvent c₁ c₂ u e₁ e₂ hu₁ hu₂ ih₁ ih₂ =>
    obtain ⟨d₁, f₁, h₁, h₁', hs₁⟩ := ih₁
    obtain ⟨d₂, f₂, h₂, h₂', hs₂⟩ := ih₂
    refine ⟨d₁.resolvent d₂ u, .resolvent u f₁ f₂ (h₁' _ hu₁) (h₂' _ hu₂), fun l hl => ?_,
      fun l hl => ?_, by rw [strahler_resolvent, strahler_resolvent, hs₁, hs₂]⟩
    · rcases Clause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
      · exact (h₁ l hl).imp_left fun hl' => Clause.mem_resolvent.2 (Or.inl ⟨hl', hne⟩)
      · exact (h₂ l hl).imp_left fun hl' => Clause.mem_resolvent.2 (Or.inr ⟨hl', hne⟩)
    · rcases Clause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
      · exact Clause.mem_resolvent.2 (Or.inl ⟨h₁' l hl, hne⟩)
      · exact Clause.mem_resolvent.2 (Or.inr ⟨h₂' l hl, hne⟩)

end Derivation

/-- The induction behind `exists_derivation_strahler_le`, with the conclusion of the refutation as
a variable: split on a variable, refute both restrictions, lift the refutations, and resolve. -/
private theorem exists_derivation_strahler_le_aux (φ : CNF V) (h : ¬ φ.Satisfiable) :
    ∃ (c : Clause V) (d : φ.Derivation c), c = [] ∧ d.strahler ≤ #φ.vars.toFinset := by
  rcases hφ : φ.vars with _ | ⟨v, _⟩
  · exact ⟨_, .mem (nil_mem_of_vars_eq_nil hφ h), rfl, Nat.zero_le _⟩
  have hv : v ∈ φ.vars.toFinset := by simp [hφ]
  have hlt (b : Bool) : #(φ.restrict v b).vars.toFinset < #φ.vars.toFinset :=
    (Finset.card_le_card vars_restrict_subset).trans_lt (Finset.card_erase_lt_of_mem hv)
  obtain ⟨_, e₀, rfl, he₀⟩ := exists_derivation_strahler_le_aux (φ.restrict v false)
    (not_satisfiable_restrict h)
  obtain ⟨_, e₁, rfl, he₁⟩ := exists_derivation_strahler_le_aux (φ.restrict v true)
    (not_satisfiable_restrict h)
  obtain ⟨d₀, f₀, h₀, -, hs₀⟩ := e₀.exists_of_restrict
  obtain ⟨d₁, f₁, h₁, -, hs₁⟩ := e₁.exists_of_restrict
  -- `d₀` only has `v` and `d₁` only has `¬v`; either one is empty, or they resolve to `[]`
  have h₀' : ∀ l ∈ d₀, l = (v, true) := fun l hl => (h₀ l hl).resolve_left List.not_mem_nil
  have h₁' : ∀ l ∈ d₁, l = (v, false) := fun l hl => (h₁ l hl).resolve_left List.not_mem_nil
  have hl₀ := hlt false
  have hl₁ := hlt true
  rw [hφ] at hl₀ hl₁
  by_cases hv₀ : (v, true) ∈ d₀
  · by_cases hv₁ : (v, false) ∈ d₁
    · refine ⟨_, .resolvent v f₀ f₁ hv₀ hv₁,
        List.eq_nil_iff_forall_not_mem.2 fun l hl => ?_, ?_⟩
      · rcases Clause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
        · exact hne (h₀' l hl)
        · exact hne (h₁' l hl)
      · rw [Derivation.strahler_resolvent]
        split_ifs <;> omega
    · exact ⟨_, f₁, List.eq_nil_iff_forall_not_mem.2 fun l hl => hv₁ (h₁' l hl ▸ hl), by omega⟩
  · exact ⟨_, f₀, List.eq_nil_iff_forall_not_mem.2 fun l hl => hv₀ (h₀' l hl ▸ hl), by omega⟩
termination_by #φ.vars.toFinset
decreasing_by
  · exact hlt false
  · exact hlt true

/-- An unsatisfiable formula on `n` variables has a tree-like refutation of Strahler number at most
`n`. -/
theorem exists_derivation_strahler_le (h : ¬ φ.Satisfiable) :
    ∃ d : φ.Derivation [], d.strahler ≤ #φ.vars.toFinset := by
  obtain ⟨_, d, rfl, hd⟩ := exists_derivation_strahler_le_aux φ h
  exact ⟨d, hd⟩

/-- **Every unsatisfiable formula on `n` variables is refutable in clause space `n + 2`**: the bound
`n + 1` of [Torán, Section 4][Toran2004], for a pebble game that shifts a pebble from a premise to
the resolvent, in the convention of `Cslib.Logic.PL.CNF.configLTS`. -/
theorem refutableInSpace_of_not_satisfiable (h : ¬ φ.Satisfiable) :
    φ.RefutableInSpace (#φ.vars.toFinset + 2) := by
  obtain ⟨d, hd⟩ := exists_derivation_strahler_le h
  exact d.refutableInSpace.mono (by omega)

end CNF

end Cslib.Logic.PL
