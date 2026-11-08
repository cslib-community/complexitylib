/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.MachineLearning.PACLearning.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin

/-!
# The realizable mistake-bound model

This file sets up Littlestone's model of online learning in the realizable case
[Littlestone1988, §3] [ShalevShwartzBenDavid2014, §21.1]. Learning proceeds in rounds. In each
round an adversary presents an instance `x`, the learner predicts a label in `Bool`, and then the
adversary reveals the true label `y`. The learner errs when its prediction differs from `y`. The
labels must stay consistent with some target concept `c` of a known concept class
`C : ConceptClass α Bool`. The quantity of interest is the worst-case number of mistakes.

A deterministic learner is a function `OnlineLearner α := List (α × Bool) → α → Bool`. It sees the
labelled history of the previous rounds and the current instance. `mistakes A S` counts the rounds
of the labelled sequence `S` on which `A` errs. `S` is *realizable* by `C` when its version space
`versionSpace C S`, the set of concepts of `C` that agree with every example of `S`, is nonempty.
The mistake bound of `A` on `C` is the supremum of `mistakes A S` over all finite realizable `S`,
in `ℕ∞`. The optimal mistake bound of `C` is the infimum of the mistake bounds over all
deterministic learners. Littlestone writes these as `M_A(C)`, defined just before Definition 1,
and `opt(C)`, Definition 1 [Littlestone1988, §3]. The supremum ranges over all finite sequences,
so `mistakeBound A C ≤ m` says that `A` makes at most `m` mistakes on every realizable sequence of
every length, matching Littlestone's quantification over all sequences. Littlestone sets
`M_A(∅) = -1`; here the empty class has no realizable sequence, so its mistake bound is `0`
(`mistakeBound_empty`).

Since the learner is deterministic, adaptivity gives the adversary nothing more. An `Adversary`
chooses each instance and each label as a function of the history and of the learner's
prediction. `mistakeBound_eq_iSup_adversary` shows that the mistake bound is also the supremum over
adversaries and horizons of the mistakes on the realizable transcripts.
`mistakeBound_eq_iSup_concept` restates the bound in Littlestone's form: the target concept `c ∈ C`
is fixed and the adversary chooses only the instances.

**Relation to other models.** The library's `PACLearning.VersionSpace` and `PACLearning.Realizable`
(cslib) are the batch analogues of `versionSpace` and `Realizable`, indexed by `Fin m`. The list
form here follows the online history directly. This model differs from prediction with expert
advice, which compares the learner with the best of a set of experts on arbitrary outcomes and
measures regret. Here a single learner competes with the requirement of realizability and pays
for each mistake absolutely; there are no experts and no losses beyond the mistake count.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.OnlineLearner`: deterministic online learners.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.mistakes`: the number of mistakes on a
  labelled sequence.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.versionSpace`: the concepts consistent with a
  labelled sequence.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.Realizable`: realizability by a concept class.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.mistakeBound`: the worst-case number of
  mistakes, `M_A(C)`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.optimalMistakeBound`: the optimal mistake
  bound, `opt(C)`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.Adversary`: adaptive adversaries and their
  transcripts.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.mistakes_eq_card`: the mistake count as the
  number of rounds `t` on which the prediction from the first `t` examples is wrong.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.mistakeBound_eq_iSup_concept`: the mistake
  bound with a fixed target concept and chosen instances.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.mistakeBound_eq_iSup_adversary`: adaptive
  adversaries are no stronger than realizable sequences.

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

/-- A deterministic online learner: from the labelled history of the previous rounds and the
current instance, it predicts a label. -/
abbrev OnlineLearner (α : Type*) := List (α × Bool) → α → Bool

/-- `mistakesFrom A h S`: the number of mistakes of `A` on the rounds `S`, after the history `h`.
Each round predicts from the history so far and then appends its example to it. -/
@[expose] def mistakesFrom (A : OnlineLearner α) : List (α × Bool) → List (α × Bool) → ℕ
  | _, [] => 0
  | h, (x, y) :: S => (if A h x = y then 0 else 1) + mistakesFrom A (h ++ [(x, y)]) S

/-- The number of mistakes of the learner `A` on the labelled sequence `S`, started from the empty
history. -/
@[expose] def mistakes (A : OnlineLearner α) (S : List (α × Bool)) : ℕ := mistakesFrom A [] S

/-- The version space: the concepts of `C` that agree with every example of `S`. -/
@[expose] def versionSpace (C : ConceptClass α Bool) (S : List (α × Bool)) : ConceptClass α Bool :=
  {c | c ∈ C ∧ ∀ p ∈ S, c p.1 = p.2}

/-- A labelled sequence is realizable by `C` if some concept of `C` agrees with all of it. -/
@[expose] def Realizable (C : ConceptClass α Bool) (S : List (α × Bool)) : Prop :=
  (versionSpace C S).Nonempty

/-- The mistake bound `M_A(C)` of the learner `A` on the class `C` [Littlestone1988, §3]: the
supremum of the mistakes of `A` over all finite sequences realizable by `C`. For the empty class
this is `0`, where Littlestone sets `M_A(∅) = -1`. -/
noncomputable def mistakeBound (A : OnlineLearner α) (C : ConceptClass α Bool) : ℕ∞ :=
  ⨆ (S : List (α × Bool)) (_ : Realizable C S), (mistakes A S : ℕ∞)

/-- The optimal mistake bound `opt(C)` [Littlestone1988, §3, Definition 1]: the least mistake
bound of a deterministic learner on `C`. -/
noncomputable def optimalMistakeBound (C : ConceptClass α Bool) : ℕ∞ :=
  ⨅ A : OnlineLearner α, mistakeBound A C

/-! ### Mistake counts -/

@[simp] theorem mistakesFrom_nil (A : OnlineLearner α) (h : List (α × Bool)) :
    mistakesFrom A h [] = 0 := rfl

theorem mistakesFrom_cons (A : OnlineLearner α) (h : List (α × Bool)) (x : α) (y : Bool)
    (S : List (α × Bool)) :
    mistakesFrom A h ((x, y) :: S) =
      (if A h x = y then 0 else 1) + mistakesFrom A (h ++ [(x, y)]) S := rfl

@[simp] theorem mistakes_nil (A : OnlineLearner α) : mistakes A [] = 0 := rfl

theorem mistakesFrom_le_length (A : OnlineLearner α) (h S : List (α × Bool)) :
    mistakesFrom A h S ≤ S.length := by
  induction S generalizing h with
  | nil => simp
  | cons p S ih =>
    obtain ⟨x, y⟩ := p
    rw [mistakesFrom_cons]
    have := ih (h ++ [(x, y)])
    simp only [List.length_cons]
    split <;> omega

theorem mistakes_le_length (A : OnlineLearner α) (S : List (α × Bool)) :
    mistakes A S ≤ S.length :=
  mistakesFrom_le_length A [] S

/-- The mistakes on `S ++ S'` are those on `S`, then those on `S'` after the history `h ++ S`. -/
theorem mistakesFrom_append (A : OnlineLearner α) (h S S' : List (α × Bool)) :
    mistakesFrom A h (S ++ S') = mistakesFrom A h S + mistakesFrom A (h ++ S) S' := by
  induction S generalizing h with
  | nil => simp
  | cons p S ih =>
    obtain ⟨x, y⟩ := p
    rw [List.cons_append, mistakesFrom_cons, mistakesFrom_cons, ih]
    simp only [List.append_assoc, List.singleton_append, Nat.add_assoc]

/-- After the history `h`, the mistakes on `S` are the rounds `t` on which the prediction from
`h` and the first `t` examples of `S` is wrong. -/
theorem mistakesFrom_eq_card (A : OnlineLearner α) (h S : List (α × Bool)) :
    mistakesFrom A h S =
      (Finset.univ.filter fun t : Fin S.length =>
        A (h ++ S.take t) S[t].1 ≠ S[t].2).card := by
  classical
  induction S generalizing h with
  | nil => simp
  | cons p S ih =>
    obtain ⟨x, y⟩ := p
    rw [mistakesFrom_cons, ih, Finset.card_filter, Finset.card_filter]
    refine Eq.trans ?_ (Fin.sum_univ_succ (n := S.length) _).symm
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs <;> simp_all

/-- The mistakes of `A` on `S` are the rounds `t` on which the prediction from the first `t`
examples is wrong. -/
theorem mistakes_eq_card (A : OnlineLearner α) (S : List (α × Bool)) :
    mistakes A S =
      (Finset.univ.filter fun t : Fin S.length => A (S.take t) S[t].1 ≠ S[t].2).card := by
  simpa [mistakes] using mistakesFrom_eq_card A [] S

/-! ### Version spaces -/

theorem mem_versionSpace {C : ConceptClass α Bool} {S : List (α × Bool)} {c : α → Bool} :
    c ∈ versionSpace C S ↔ c ∈ C ∧ ∀ p ∈ S, c p.1 = p.2 := Iff.rfl

@[simp] theorem versionSpace_nil (C : ConceptClass α Bool) : versionSpace C [] = C := by
  ext c; simp [versionSpace]

theorem versionSpace_append (C : ConceptClass α Bool) (S T : List (α × Bool)) :
    versionSpace C (S ++ T) = versionSpace (versionSpace C S) T := by
  ext c
  simp only [versionSpace, Set.mem_ofPred_eq, List.mem_append]
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨⟨hc, fun p hp => h p (Or.inl hp)⟩, fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨⟨hc, h1⟩, h2⟩
    exact ⟨hc, fun p hp => hp.elim (h1 p) (h2 p)⟩

theorem versionSpace_cons (C : ConceptClass α Bool) (p : α × Bool) (S : List (α × Bool)) :
    versionSpace C (p :: S) = versionSpace (versionSpace C [p]) S :=
  versionSpace_append C [p] S

theorem versionSpace_subset (C : ConceptClass α Bool) (S : List (α × Bool)) :
    versionSpace C S ⊆ C := fun _ hc => hc.1

theorem versionSpace_mono {C C' : ConceptClass α Bool} (h : C ⊆ C') (S : List (α × Bool)) :
    versionSpace C S ⊆ versionSpace C' S := fun _ hc => ⟨h hc.1, hc.2⟩

theorem mem_versionSpace_singleton {C : ConceptClass α Bool} {x : α} {y : Bool} {c : α → Bool} :
    c ∈ versionSpace C [(x, y)] ↔ c ∈ C ∧ c x = y := by
  simp [versionSpace]

/-! ### Realizability -/

theorem realizable_iff {C : ConceptClass α Bool} {S : List (α × Bool)} :
    Realizable C S ↔ ∃ c ∈ C, ∀ p ∈ S, c p.1 = p.2 := by
  simp [Realizable, Set.Nonempty, versionSpace]

@[simp] theorem realizable_nil {C : ConceptClass α Bool} : Realizable C [] ↔ C.Nonempty := by
  simp [Realizable]

theorem realizable_cons {C : ConceptClass α Bool} {p : α × Bool} {S : List (α × Bool)} :
    Realizable C (p :: S) ↔ Realizable (versionSpace C [p]) S := by
  rw [Realizable, Realizable, versionSpace_cons]

theorem Realizable.mono {C C' : ConceptClass α Bool} {S : List (α × Bool)} (hS : Realizable C S)
    (h : C ⊆ C') : Realizable C' S :=
  Set.Nonempty.mono (versionSpace_mono h S) hS

/-- A sequence labelled by a concept of `C` is realizable by `C`. -/
theorem realizable_map {C : ConceptClass α Bool} {c : α → Bool} (hc : c ∈ C) (xs : List α) :
    Realizable C (xs.map fun x => (x, c x)) :=
  realizable_iff.mpr ⟨c, hc, by simp⟩

/-! ### Mistake bounds -/

theorem mistakes_le_mistakeBound {A : OnlineLearner α} {C : ConceptClass α Bool}
    {S : List (α × Bool)} (hS : Realizable C S) : (mistakes A S : ℕ∞) ≤ mistakeBound A C :=
  le_iSup₂ (f := fun S (_ : Realizable C S) => (mistakes A S : ℕ∞)) S hS

theorem mistakeBound_le_iff {A : OnlineLearner α} {C : ConceptClass α Bool} {m : ℕ∞} :
    mistakeBound A C ≤ m ↔ ∀ S, Realizable C S → (mistakes A S : ℕ∞) ≤ m := by
  simp [mistakeBound]

theorem mistakeBound_mono (A : OnlineLearner α) {C C' : ConceptClass α Bool} (h : C ⊆ C') :
    mistakeBound A C ≤ mistakeBound A C' :=
  mistakeBound_le_iff.mpr fun _ hS => mistakes_le_mistakeBound (hS.mono h)

/-- The empty class has no realizable sequence, so every learner has mistake bound `0` on it.
Littlestone's convention `M_A(∅) = -1` is not used. -/
@[simp] theorem mistakeBound_empty (A : OnlineLearner α) : mistakeBound A ∅ = 0 :=
  nonpos_iff_eq_zero.mp <| mistakeBound_le_iff.mpr fun _ hS => (hS.mono le_rfl).elim
    fun _ h => (versionSpace_subset ∅ _ h).elim

theorem optimalMistakeBound_le (A : OnlineLearner α) (C : ConceptClass α Bool) :
    optimalMistakeBound C ≤ mistakeBound A C := iInf_le _ A

theorem le_optimalMistakeBound_iff {C : ConceptClass α Bool} {m : ℕ∞} :
    m ≤ optimalMistakeBound C ↔ ∀ A : OnlineLearner α, m ≤ mistakeBound A C := le_iInf_iff

theorem optimalMistakeBound_mono {C C' : ConceptClass α Bool} (h : C ⊆ C') :
    optimalMistakeBound C ≤ optimalMistakeBound C' :=
  iInf_mono fun A => mistakeBound_mono A h

@[simp] theorem optimalMistakeBound_empty : optimalMistakeBound (∅ : ConceptClass α Bool) = 0 :=
  nonpos_iff_eq_zero.mp <| (optimalMistakeBound_le (fun _ _ => false) ∅).trans_eq
    (mistakeBound_empty _)

/-- The mistake bound in Littlestone's form [Littlestone1988, §3]: the target `c ∈ C` is fixed and
the adversary chooses the instances, each labelled by `c`. -/
theorem mistakeBound_eq_iSup_concept (A : OnlineLearner α) (C : ConceptClass α Bool) :
    mistakeBound A C = ⨆ (c ∈ C) (xs : List α), (mistakes A (xs.map fun x => (x, c x)) : ℕ∞) := by
  apply le_antisymm
  · refine mistakeBound_le_iff.mpr fun S hS => ?_
    obtain ⟨c, hc, hcS⟩ := realizable_iff.mp hS
    have hS' : List.map (fun x => (x, c x)) (List.map Prod.fst S) = S := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id S]
      refine List.map_congr_left fun p hp => ?_
      simp [hcS p hp]
    calc (mistakes A S : ℕ∞)
        = mistakes A (List.map (fun x => (x, c x)) (List.map Prod.fst S)) := by rw [hS']
      _ ≤ _ := le_iSup₂_of_le (f := fun c (_ : c ∈ C) => ⨆ xs : List α,
          (mistakes A (xs.map fun x => (x, c x)) : ℕ∞)) c hc
            (le_iSup (fun xs : List α => (mistakes A (xs.map fun x => (x, c x)) : ℕ∞)) _)
  · exact iSup₂_le fun c hc => iSup_le fun xs => mistakes_le_mistakeBound (realizable_map hc xs)

/-! ### Adaptive adversaries -/

/-- An adaptive adversary. From the labelled history it chooses the next instance (`next`), and
from the history and the learner's prediction it chooses the label (`label`). -/
structure Adversary (α : Type*) where
  /-- The next instance, as a function of the history. -/
  next : List (α × Bool) → α
  /-- The label, as a function of the history and of the learner's prediction. -/
  label : List (α × Bool) → Bool → Bool

/-- The labelled history after `t` rounds of the learner `A` against the adversary `B`. -/
def Adversary.transcript (B : Adversary α) (A : OnlineLearner α) : ℕ → List (α × Bool)
  | 0 => []
  | t + 1 =>
    let h := B.transcript A t
    h ++ [(B.next h, B.label h (A h (B.next h)))]

@[simp] theorem Adversary.transcript_zero (B : Adversary α) (A : OnlineLearner α) :
    B.transcript A 0 = [] := by
  rw [Adversary.transcript]

theorem Adversary.transcript_succ (B : Adversary α) (A : OnlineLearner α) (t : ℕ) :
    B.transcript A (t + 1) =
      B.transcript A t ++
        [(B.next (B.transcript A t),
          B.label (B.transcript A t) (A (B.transcript A t) (B.next (B.transcript A t))))] := by
  rw [Adversary.transcript]

@[simp] theorem Adversary.length_transcript (B : Adversary α) (A : OnlineLearner α) (t : ℕ) :
    (B.transcript A t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [Adversary.transcript_succ, ih]

/-- The oblivious adversary that presents the fixed sequence `S`, then repeats `p₀`. -/
def Adversary.ofList (S : List (α × Bool)) (p₀ : α × Bool) : Adversary α where
  next h := (S.getD h.length p₀).1
  label h _ := (S.getD h.length p₀).2

theorem Adversary.transcript_ofList (A : OnlineLearner α) (S : List (α × Bool)) (p₀ : α × Bool)
    {t : ℕ} (ht : t ≤ S.length) : (Adversary.ofList S p₀).transcript A t = S.take t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih := ih (by omega)
    have hlen : (S.take t).length = t := by rw [List.length_take]; omega
    rw [Adversary.transcript_succ, ih, List.take_add_one,
      List.getElem?_eq_getElem (by omega : t < S.length)]
    simp only [Adversary.ofList, hlen, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : t < S.length), Option.getD_some, Option.toList_some]

/-- Adaptive adversaries are no stronger than realizable sequences: the mistake bound of a
deterministic learner is the supremum, over adversaries `B` and horizons `t`, of its mistakes on
the transcripts that are realizable by `C`. -/
theorem mistakeBound_eq_iSup_adversary (A : OnlineLearner α) (C : ConceptClass α Bool) :
    mistakeBound A C = ⨆ (B : Adversary α) (t : ℕ) (_ : Realizable C (B.transcript A t)),
      (mistakes A (B.transcript A t) : ℕ∞) := by
  apply le_antisymm
  · refine mistakeBound_le_iff.mpr fun S hS => ?_
    rcases S with _ | ⟨p₀, S'⟩
    · simp
    · set B := Adversary.ofList (p₀ :: S') p₀
      have ht : B.transcript A (p₀ :: S').length = p₀ :: S' := by
        rw [Adversary.transcript_ofList A (p₀ :: S') p₀ le_rfl, List.take_length]
      have hB : Realizable C (B.transcript A (p₀ :: S').length) := by rw [ht]; exact hS
      calc (mistakes A (p₀ :: S') : ℕ∞) = mistakes A (B.transcript A (p₀ :: S').length) := by
            rw [ht]
        _ ≤ _ := le_iSup₂_of_le (f := fun (t : ℕ) (_ : Realizable C (B.transcript A t)) =>
            (mistakes A (B.transcript A t) : ℕ∞)) _ hB le_rfl
        _ ≤ _ := le_iSup (fun B : Adversary α => ⨆ (t : ℕ)
            (_ : Realizable C (B.transcript A t)), (mistakes A (B.transcript A t) : ℕ∞)) B
  · exact iSup_le fun B => iSup_le fun t => iSup_le fun hB => mistakes_le_mistakeBound hB

end Cslib.MachineLearning.OnlineLearning.MistakeBound
