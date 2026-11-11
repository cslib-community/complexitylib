/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.List.Append
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.Reduce

/-!
# Post's correspondence problem

A *domino* is a pair of words over an alphabet `α`, its top and its bottom. An instance of
**Post's correspondence problem** (PCP) is a finite list `P` of dominoes. It is *solvable* when some
nonempty sequence of dominoes of `P`, repetitions allowed, has equal top and bottom concatenations
[Post1946]; [Sipser2013, §5.2]. The **modified correspondence problem** (MPCP) of [Sipser2013, §5.2]
additionally fixes the first domino of the match. Here an MPCP instance is a start domino and a
list of dominoes that may follow it, so the start domino may recur only if it is also in the list;
Sipser's MPCP, where the start domino belongs to the instance, is the case where it is.

Instances are encoded through `Primcodable` instances, so the two decision problems are predicates
for Mathlib's `ComputablePred` and many-one reducibility `≤₀`. Their undecidability is proved in
`CslibFrontier.Computability.PostCorrespondence.Undecidable`.

## Main definitions

* `Cslib.PostCorrespondence.Domino`: a pair of words.
* `Cslib.PostCorrespondence.tops`, `Cslib.PostCorrespondence.bottoms`: the concatenations of the
  top and the bottom words of a sequence of dominoes.
* `Cslib.PostCorrespondence.Solvable`: solvability of a PCP instance.
* `Cslib.PostCorrespondence.MInstance`, `Cslib.PostCorrespondence.MInstance.Solvable`: MPCP
  instances, a start domino and a list of dominoes, and their solvability.

## Main results

* `Cslib.PostCorrespondence.solvable_iff_exists_indices`: solvability in the index form
  `t_{i₁} ⋯ t_{iₖ} = b_{i₁} ⋯ b_{iₖ}` of the textbooks.
* `Cslib.PostCorrespondence.not_solvable_of_length_lt`: an instance whose every domino has a
  shorter bottom than top is not solvable.

## References

* [E. L. Post, *A variant of a recursively unsolvable problem*][Post1946]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.PostCorrespondence

variable {α : Type*}

/-! ### Dominoes and instances -/

-- Exposed so that `decide` can evaluate the derived `DecidableEq` instance in client modules.
@[expose] public section DominoDef

/-- A domino: a pair of words, its top and its bottom. -/
structure Domino (α : Type*) where
  /-- The top word. -/
  top : List α
  /-- The bottom word. -/
  bottom : List α
deriving DecidableEq

end DominoDef

/-- The concatenation of the top words of a sequence of dominoes. -/
@[expose] def tops (ds : List (Domino α)) : List α := ds.flatMap Domino.top

/-- The concatenation of the bottom words of a sequence of dominoes. -/
@[expose] def bottoms (ds : List (Domino α)) : List α := ds.flatMap Domino.bottom

@[simp] theorem tops_nil : tops ([] : List (Domino α)) = [] := rfl
@[simp] theorem bottoms_nil : bottoms ([] : List (Domino α)) = [] := rfl
@[simp] theorem tops_cons (d : Domino α) (ds : List (Domino α)) :
    tops (d :: ds) = d.top ++ tops ds := List.flatMap_cons
@[simp] theorem bottoms_cons (d : Domino α) (ds : List (Domino α)) :
    bottoms (d :: ds) = d.bottom ++ bottoms ds := List.flatMap_cons
@[simp] theorem tops_append (ds es : List (Domino α)) : tops (ds ++ es) = tops ds ++ tops es :=
  List.flatMap_append
@[simp] theorem bottoms_append (ds es : List (Domino α)) :
    bottoms (ds ++ es) = bottoms ds ++ bottoms es :=
  List.flatMap_append

/-- A PCP instance `P`, a list of dominoes, is solvable when some nonempty sequence of dominoes of
`P`, repetitions allowed, has equal top and bottom concatenations. -/
@[expose] def Solvable (P : List (Domino α)) : Prop :=
  ∃ ds : List (Domino α), ds ≠ [] ∧ (∀ d ∈ ds, d ∈ P) ∧ tops ds = bottoms ds

private theorem exists_indices {P : List α} :
    ∀ {l : List α}, (∀ a ∈ l, a ∈ P) → ∃ is : List (Fin P.length), is.map P.get = l
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (h a List.mem_cons_self)
    obtain ⟨is, his⟩ := exists_indices fun b hb => h b (List.mem_cons_of_mem a hb)
    exact ⟨i :: is, by rw [List.map_cons, hi, his]⟩

/-- Solvability in the index form of the textbooks: a nonempty sequence of indices `i₁, …, iₖ`
with `t_{i₁} ⋯ t_{iₖ} = b_{i₁} ⋯ b_{iₖ}`. -/
theorem solvable_iff_exists_indices (P : List (Domino α)) :
    Solvable P ↔ ∃ is : List (Fin P.length), is ≠ [] ∧
      tops (is.map P.get) = bottoms (is.map P.get) := by
  constructor
  · rintro ⟨ds, hne, hmem, heq⟩
    obtain ⟨is, rfl⟩ := exists_indices hmem
    exact ⟨is, fun h => hne (by rw [h, List.map_nil]), heq⟩
  · rintro ⟨is, hne, heq⟩
    refine ⟨is.map P.get, fun h => hne (List.map_eq_nil_iff.mp h), fun d hd => ?_, heq⟩
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hd
    exact List.get_mem P i

private theorem length_bottoms_add_le {P : List (Domino α)}
    (hP : ∀ d ∈ P, d.bottom.length < d.top.length) :
    ∀ {ds : List (Domino α)}, (∀ d ∈ ds, d ∈ P) →
      (bottoms ds).length + ds.length ≤ (tops ds).length
  | [], _ => le_rfl
  | d :: ds, h => by
    have hd := hP d (h d List.mem_cons_self)
    have ih := length_bottoms_add_le hP fun e he => h e (List.mem_cons_of_mem d he)
    simp only [bottoms_cons, tops_cons, List.length_append, List.length_cons]
    omega

/-- An instance whose every domino has a shorter bottom than top has no match: the top of a
nonempty sequence of its dominoes is longer than the bottom. -/
theorem not_solvable_of_length_lt {P : List (Domino α)}
    (hP : ∀ d ∈ P, d.bottom.length < d.top.length) : ¬Solvable P := by
  rintro ⟨ds, hne, hmem, heq⟩
  have h := length_bottoms_add_le hP hmem
  rw [heq] at h
  have := List.length_pos_iff.mpr hne
  omega

/-- An instance of the modified correspondence problem (MPCP): a start domino and a list of
dominoes. -/
structure MInstance (α : Type*) where
  /-- The domino every match starts with. -/
  start : Domino α
  /-- The dominoes that may follow it. -/
  dominoes : List (Domino α)

/-- An MPCP instance is solvable when the start domino followed by some sequence of its dominoes
has equal top and bottom concatenations. The start domino occurs again only if it is listed in
`dominoes`. -/
@[expose] def MInstance.Solvable (I : MInstance α) : Prop :=
  ∃ ds : List (Domino α), (∀ d ∈ ds, d ∈ I.dominoes) ∧
    I.start.top ++ tops ds = I.start.bottom ++ bottoms ds

/-! ### Encodings -/

/-- Dominoes as pairs of words. -/
def Domino.equivProd : Domino α ≃ List α × List α where
  toFun d := (d.top, d.bottom)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Primcodable α] : Primcodable (Domino α) := Primcodable.ofEquiv _ Domino.equivProd

/-- MPCP instances as pairs of a domino and a list of dominoes. -/
def MInstance.equivProd : MInstance α ≃ Domino α × List (Domino α) where
  toFun I := (I.start, I.dominoes)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Primcodable α] : Primcodable (MInstance α) := Primcodable.ofEquiv _ MInstance.equivProd

section Primrec

variable [Primcodable α]

theorem Domino.primrec_top : Primrec (Domino.top : Domino α → List α) :=
  Primrec.fst.comp Primrec.of_equiv

theorem Domino.primrec_bottom : Primrec (Domino.bottom : Domino α → List α) :=
  Primrec.snd.comp Primrec.of_equiv

theorem Domino.primrec₂_mk : Primrec₂ (Domino.mk : List α → List α → Domino α) :=
  (Primrec.of_equiv_symm.comp Primrec.id : Primrec (Domino.equivProd (α := α)).symm).comp₂
    Primrec₂.pair

theorem MInstance.primrec_start : Primrec (MInstance.start : MInstance α → Domino α) :=
  Primrec.fst.comp Primrec.of_equiv

theorem MInstance.primrec_dominoes :
    Primrec (MInstance.dominoes : MInstance α → List (Domino α)) :=
  Primrec.snd.comp Primrec.of_equiv

theorem MInstance.primrec₂_mk :
    Primrec₂ (MInstance.mk : Domino α → List (Domino α) → MInstance α) :=
  (Primrec.of_equiv_symm.comp Primrec.id : Primrec (MInstance.equivProd (α := α)).symm).comp₂
    Primrec₂.pair

end Primrec

end Cslib.PostCorrespondence
