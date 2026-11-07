/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.MachineLearning.OnlineLearning.MistakeBound.Basic

/-!
# Mistake trees and the Littlestone dimension

A complete `k`-mistake tree for a concept class `C` [Littlestone1988, §3, Definition 2] is a
complete binary tree of height `k`. Its root is `C`, each internal node `C'` is labelled with an
instance `x`, the two children of `C'` are the subclasses of `C'` with `c x = false` and with
`c x = true`, and every node is nonempty. `HasMistakeTree d C` states that such a tree of height
`d` exists. It is defined by recursion on `d`, so it needs no tree data type: a tree of height
`d + 1` is a root instance `x` such that both restrictions `versionSpace C [(x, y)]` have trees of
height `d`. `hasMistakeTree_iff_exists_tree` relates it to the explicit form of
[ShalevShwartzBenDavid2014, §21.1]: an instance tree, given as a map from the paths
`List Bool` to the instances, whose root-to-leaf paths of length `d` are all realizable by `C`.

The **Littlestone dimension** `littlestoneDim C : ℕ∞` is the supremum of the heights of the
complete mistake trees for `C`. Littlestone writes it `K(C)` and sets `K(∅) = -1`; here
`littlestoneDim ∅ = 0`, and a class with complete mistake trees of every height has dimension `⊤`.

**Lower bound** [Littlestone1988, §3, Lemma 1]. An adversary walking down a complete `d`-mistake
tree forces every deterministic learner to err `d` times: at each node it presents the label of
the node and then reveals the opposite of the learner's prediction
(`exists_realizable_mistakes_eq`). Hence `littlestoneDim C ≤ mistakeBound A C` for every learner
`A` (`littlestoneDim_le_mistakeBound`), and `littlestoneDim C ≤ optimalMistakeBound C`. The matching
upper bound, attained by the standard optimal algorithm, is in
`Complexity.MachineLearning.OnlineLearning.MistakeBound.SOA`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.HasMistakeTree`: existence of a complete
  mistake tree of a given height.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.littlestoneDim`: the Littlestone dimension.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.hasMistakeTree_iff_exists_tree`: the explicit
  form of mistake trees.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.exists_realizable_mistakes_eq`: a complete
  `d`-mistake tree forces `d` mistakes on a realizable sequence of length `d`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.littlestoneDim_le_mistakeBound`:
  [Littlestone1988, §3, Lemma 1], every deterministic learner makes at least `littlestoneDim C`
  mistakes in the worst case.

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

/-- `HasMistakeTree d C`: the class `C` has a complete mistake tree of height `d`
[Littlestone1988, §3, Definition 2]. A tree of height `0` is a nonempty root; a tree of height
`d + 1` labels the root with an instance `x` and has, for both labels `y`, a tree of height `d` for
the concepts of `C` with `c x = y`. -/
@[expose] def HasMistakeTree : ℕ → ConceptClass α Bool → Prop
  | 0, C => C.Nonempty
  | d + 1, C => ∃ x : α, ∀ y : Bool, HasMistakeTree d (versionSpace C [(x, y)])

@[simp] theorem hasMistakeTree_zero {C : ConceptClass α Bool} :
    HasMistakeTree 0 C ↔ C.Nonempty := Iff.rfl

theorem hasMistakeTree_succ {d : ℕ} {C : ConceptClass α Bool} :
    HasMistakeTree (d + 1) C ↔ ∃ x : α, ∀ y : Bool, HasMistakeTree d (versionSpace C [(x, y)]) :=
  Iff.rfl

theorem HasMistakeTree.nonempty {d : ℕ} {C : ConceptClass α Bool} (h : HasMistakeTree d C) :
    C.Nonempty := by
  induction d generalizing C with
  | zero => exact h
  | succ d ih =>
    obtain ⟨x, hx⟩ := h
    exact Set.Nonempty.mono (versionSpace_subset _ _) (ih (hx true))

theorem HasMistakeTree.mono {d : ℕ} {C C' : ConceptClass α Bool} (h : HasMistakeTree d C)
    (hCC' : C ⊆ C') : HasMistakeTree d C' := by
  induction d generalizing C C' with
  | zero => exact Set.Nonempty.mono hCC' h
  | succ d ih =>
    obtain ⟨x, hx⟩ := h
    exact ⟨x, fun y => ih (hx y) (versionSpace_mono hCC' _)⟩

/-- Pruning a complete mistake tree gives complete mistake trees of every smaller height. -/
theorem HasMistakeTree.of_le {d e : ℕ} {C : ConceptClass α Bool} (h : HasMistakeTree d C)
    (hed : e ≤ d) : HasMistakeTree e C := by
  induction e generalizing d C with
  | zero => exact h.nonempty
  | succ e ih =>
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨x, hx⟩ := h
    exact ⟨x, fun y => ih (hx y) (by omega)⟩

/-! ### The explicit form -/

/-- The labelled path through the instance tree `T : List Bool → α` along the labels `ys`: the
node reached by the labels `zs` is labelled with the instance `T zs`. -/
@[expose] def treePath (T : List Bool → α) : List Bool → List (α × Bool)
  | [] => []
  | y :: ys => (T [], y) :: treePath (fun zs => T (y :: zs)) ys

@[simp] theorem treePath_nil (T : List Bool → α) : treePath T [] = [] := rfl

@[simp] theorem treePath_cons (T : List Bool → α) (y : Bool) (ys : List Bool) :
    treePath T (y :: ys) = (T [], y) :: treePath (fun zs => T (y :: zs)) ys := rfl

/-- The explicit form of mistake trees [ShalevShwartzBenDavid2014, §21.1]: `C` has a complete
mistake tree of height `d` iff some instance tree has all its labelled root-to-leaf paths of
length `d` realizable by `C`. The instance space must be nonempty to label the leaves when
`d = 0`. -/
theorem hasMistakeTree_iff_exists_tree [Nonempty α] {d : ℕ} {C : ConceptClass α Bool} :
    HasMistakeTree d C ↔
      ∃ T : List Bool → α, ∀ ys : List Bool, ys.length = d → Realizable C (treePath T ys) := by
  induction d generalizing C with
  | zero =>
    constructor
    · intro hC
      refine ⟨fun _ => Classical.arbitrary α, fun ys hys => ?_⟩
      rw [List.length_eq_zero_iff] at hys
      subst hys
      simpa using hC
    · rintro ⟨T, hT⟩
      simpa using hT [] rfl
  | succ d ih =>
    constructor
    · rintro ⟨x, hx⟩
      choose T hT using fun y => ih.mp (hx y)
      refine ⟨fun ys => match ys with
        | [] => x
        | y :: zs => T y zs, fun ys hys => ?_⟩
      rcases ys with _ | ⟨y, ys⟩
      · simp at hys
      · exact realizable_cons.mpr (hT y ys (by simpa using hys))
    · rintro ⟨T, hT⟩
      refine ⟨T [], fun y => ih.mpr ⟨fun zs => T (y :: zs), fun ys hys => ?_⟩⟩
      exact realizable_cons.mp (hT (y :: ys) (by simp [hys]))

/-! ### The Littlestone dimension -/

/-- The Littlestone dimension `K(C)` [Littlestone1988, §3]: the supremum of the heights of the
complete mistake trees for `C`, in `ℕ∞`. It is `0` for the empty class, where Littlestone sets
`K(∅) = -1`. -/
noncomputable def littlestoneDim (C : ConceptClass α Bool) : ℕ∞ :=
  ⨆ (d : ℕ) (_ : HasMistakeTree d C), (d : ℕ∞)

theorem le_littlestoneDim_of_hasMistakeTree {d : ℕ} {C : ConceptClass α Bool}
    (h : HasMistakeTree d C) : (d : ℕ∞) ≤ littlestoneDim C :=
  le_iSup₂ (f := fun (d : ℕ) (_ : HasMistakeTree d C) => (d : ℕ∞)) d h

theorem littlestoneDim_le_iff {C : ConceptClass α Bool} {m : ℕ∞} :
    littlestoneDim C ≤ m ↔ ∀ d : ℕ, HasMistakeTree d C → (d : ℕ∞) ≤ m := by
  simp [littlestoneDim]

theorem hasMistakeTree_of_le_littlestoneDim {d : ℕ} {C : ConceptClass α Bool} (hC : C.Nonempty)
    (hd : (d : ℕ∞) ≤ littlestoneDim C) : HasMistakeTree d C := by
  by_contra hnot
  have hlt : ∀ e : ℕ, HasMistakeTree e C → e < d := fun e he => by
    by_contra hed
    exact hnot (he.of_le (by omega))
  rcases d with _ | d
  · exact hnot hC
  · have : littlestoneDim C ≤ (d : ℕ∞) := littlestoneDim_le_iff.mpr fun e he => by
      exact_mod_cast Nat.lt_succ_iff.mp (hlt e he)
    have := hd.trans this
    norm_cast at this
    omega

/-- For a nonempty class, `d ≤ littlestoneDim C` iff `C` has a complete mistake tree of
height `d`. -/
theorem natCast_le_littlestoneDim_iff {d : ℕ} {C : ConceptClass α Bool} (hC : C.Nonempty) :
    (d : ℕ∞) ≤ littlestoneDim C ↔ HasMistakeTree d C :=
  ⟨hasMistakeTree_of_le_littlestoneDim hC, le_littlestoneDim_of_hasMistakeTree⟩

theorem littlestoneDim_mono {C C' : ConceptClass α Bool} (h : C ⊆ C') :
    littlestoneDim C ≤ littlestoneDim C' :=
  littlestoneDim_le_iff.mpr fun _ hd => le_littlestoneDim_of_hasMistakeTree (hd.mono h)

@[simp] theorem littlestoneDim_empty : littlestoneDim (∅ : ConceptClass α Bool) = 0 :=
  le_antisymm
    (littlestoneDim_le_iff.mpr fun _ hd => absurd hd.nonempty Set.not_nonempty_empty) bot_le

/-- If both restrictions of `C` at `x` are nonempty, the Littlestone dimension of `C` exceeds the
smaller of their dimensions: complete trees for both combine under a root labelled `x`. -/
theorem min_littlestoneDim_add_one_le (C : ConceptClass α Bool) (x : α)
    (h0 : (versionSpace C [(x, false)]).Nonempty) (h1 : (versionSpace C [(x, true)]).Nonempty) :
    min (littlestoneDim (versionSpace C [(x, false)]))
        (littlestoneDim (versionSpace C [(x, true)])) + 1 ≤ littlestoneDim C := by
  have key : ∀ n : ℕ, (n : ℕ∞) ≤ min (littlestoneDim (versionSpace C [(x, false)]))
      (littlestoneDim (versionSpace C [(x, true)])) → ((n + 1 : ℕ) : ℕ∞) ≤ littlestoneDim C := by
    intro n hn
    rw [le_min_iff] at hn
    refine le_littlestoneDim_of_hasMistakeTree ⟨x, fun y => ?_⟩
    cases y
    · exact hasMistakeTree_of_le_littlestoneDim h0 hn.1
    · exact hasMistakeTree_of_le_littlestoneDim h1 hn.2
  generalize hm : min (littlestoneDim (versionSpace C [(x, false)]))
    (littlestoneDim (versionSpace C [(x, true)])) = m at key
  induction m using ENat.recTopCoe with
  | top =>
    rw [top_add, top_le_iff]
    refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
    exact (key n le_top).trans' (by exact_mod_cast Nat.le_succ n)
  | coe m => exact_mod_cast key m le_rfl

/-! ### The lower bound -/

/-- From a complete `d`-mistake tree, an adversary forces any learner, after any history, to err
on each of `d` rounds of a sequence realizable by `C` [Littlestone1988, §3, proof of Lemma 1]. -/
theorem exists_realizable_mistakesFrom_eq (A : OnlineLearner α) {d : ℕ}
    {C : ConceptClass α Bool} (hd : HasMistakeTree d C) (h : List (α × Bool)) :
    ∃ S : List (α × Bool), S.length = d ∧ Realizable C S ∧ mistakesFrom A h S = d := by
  induction d generalizing C h with
  | zero => exact ⟨[], rfl, by simpa using hd, rfl⟩
  | succ d ih =>
    obtain ⟨x, hx⟩ := hd
    let y := !A h x
    obtain ⟨S, hlen, hreal, hmis⟩ := ih (hx y) (h ++ [(x, y)])
    refine ⟨(x, y) :: S, by simp [hlen], realizable_cons.mpr hreal, ?_⟩
    rw [mistakesFrom_cons, hmis]
    simp [y, add_comm]

/-- A complete `d`-mistake tree for `C` forces every deterministic learner to err on all `d`
rounds of some sequence of length `d` realizable by `C`. -/
theorem exists_realizable_mistakes_eq (A : OnlineLearner α) {d : ℕ}
    {C : ConceptClass α Bool} (hd : HasMistakeTree d C) :
    ∃ S : List (α × Bool), S.length = d ∧ Realizable C S ∧ mistakes A S = d :=
  exists_realizable_mistakesFrom_eq A hd []

/-- **Littlestone's lower bound** [Littlestone1988, §3, Lemma 1]: every deterministic learner
makes at least `littlestoneDim C` mistakes in the worst case. -/
theorem littlestoneDim_le_mistakeBound (A : OnlineLearner α) (C : ConceptClass α Bool) :
    littlestoneDim C ≤ mistakeBound A C := littlestoneDim_le_iff.mpr fun d hd => by
  obtain ⟨S, -, hS, hm⟩ := exists_realizable_mistakes_eq A hd
  exact hm ▸ mistakes_le_mistakeBound hS

theorem littlestoneDim_le_optimalMistakeBound (C : ConceptClass α Bool) :
    littlestoneDim C ≤ optimalMistakeBound C :=
  le_optimalMistakeBound_iff.mpr fun A => littlestoneDim_le_mistakeBound A C

end Cslib.MachineLearning.OnlineLearning.MistakeBound
