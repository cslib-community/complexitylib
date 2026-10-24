/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Extension

/-!
# Finite certificates for semi-ultrafilter covers

A certificate labels both components and the intersection of each cover pair. A fixed additional
empty set is rejected. Invalid labels are detected by a rejected superset of an accepted or
required set, or two rejected sets covering the carrier. All pairs, including equal pairs and
the fixed empty set, participate in these tests. A valid certificate extends to a semi-ultrafilter;
if it also preserves every listed pair it contradicts a cover above a target point.

## Main definitions

* `Cslib.Circuits.Fusion.PairCertificate.size`,
  `Cslib.Circuits.Fusion.PairCertificate.left`,
  `Cslib.Circuits.Fusion.PairCertificate.right`,
  `Cslib.Circuits.Fusion.PairCertificate.inter`: the certificate bit count and the indices for each
  pair's first set, second set, and intersection.
* `Cslib.Circuits.Fusion.PairCertificate.sets`,
  `Cslib.Circuits.Fusion.PairCertificate.label`,
  `Cslib.Circuits.Fusion.PairCertificate.pointLabels`: the three sets per pair and fixed empty set,
  extended certificate labels, and point-membership labels.
* `Cslib.Circuits.Fusion.PairCertificate.Invalid`: the grouped consistency violations.
* `Cslib.Circuits.Fusion.PairCertificate.BreaksPair`: failure of pair preservation.

## Main results

* `Cslib.Circuits.Fusion.PairCertificate.exists_filter_of_not_invalid`: realize a valid certificate.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*][CavalarOliveira2025], Theorem 45, credited there to Karchmer.
-/

@[expose] public section

namespace Cslib.Circuits.Fusion.PairCertificate

variable {U : Type*} (pairs : List (Set U × Set U))

/-- Three certificate bits per pair: its first set, second set and intersection. -/
abbrev size := pairs.length + (pairs.length + pairs.length)

/-- The first-component certificate index. -/
def left (i : Fin pairs.length) : Fin (size pairs) := Fin.castAdd _ i

/-- The second-component certificate index. -/
def right (i : Fin pairs.length) : Fin (size pairs) :=
  Fin.natAdd _ (Fin.castAdd _ i)

/-- The intersection certificate index. -/
def inter (i : Fin pairs.length) : Fin (size pairs) := Fin.natAdd _ (Fin.natAdd _ i)

/-- A fixed empty set supplements the three sets for each pair. -/
def sets : Option (Fin (size pairs)) → Set U
  | none => ∅
  | some i => Fin.append (fun i => (pairs.get i).1)
      (Fin.append (fun i => (pairs.get i).2) (fun i => (pairs.get i).1 ∩ (pairs.get i).2)) i

/-- The fixed empty set has label false. -/
def label (y : Fin (size pairs) → Bool) : Option (Fin (size pairs)) → Bool
  | none => false
  | some i => y i

/-- The set at `left pairs i` is the first component of the `i`-th pair. -/
@[simp] theorem sets_left (i : Fin pairs.length) :
    sets pairs (some (left pairs i)) = (pairs.get i).1 := Fin.append_left ..

/-- The set at `right pairs i` is the second component of the `i`-th pair. -/
@[simp] theorem sets_right (i : Fin pairs.length) :
    sets pairs (some (right pairs i)) = (pairs.get i).2 := by simp [sets, right]

/-- The set at `inter pairs i` is the intersection of the two components of the `i`-th pair. -/
@[simp] theorem sets_inter (i : Fin pairs.length) :
    sets pairs (some (inter pairs i)) = (pairs.get i).1 ∩ (pairs.get i).2 := by
  simp only [sets, inter, Fin.append_right]

/-- Consistency violations, grouped by a rejected set. The sources marked true must be accepted. -/
def Invalid {n : ℕ} (sources : Fin n → Set U) (x : Fin n → Bool)
    (y : Fin (size pairs) → Bool) : Prop :=
  ∃ j, label pairs y j = false ∧
    ((∃ i, sets pairs i ⊆ sets pairs j ∧ label pairs y i = true) ∨
      (∃ k, sets pairs j ∪ sets pairs k = Set.univ ∧ label pairs y k = false) ∨
      (∃ l, sources l ⊆ sets pairs j ∧ x l = true))

/-- An accepted pair with rejected intersection. -/
def BreaksPair (y : Fin (size pairs) → Bool) : Prop :=
  ∃ i, y (left pairs i) = true ∧ y (right pairs i) = true ∧ y (inter pairs i) = false

/-- Every valid labeling is realized by a semi-ultrafilter accepting all required sources. -/
theorem exists_filter_of_not_invalid {n : ℕ} (sources : Fin n → Set U) (x : Fin n → Bool)
    (y : Fin (size pairs) → Bool) (h : ¬ Invalid pairs sources x y) :
    ∃ F : Semifilter U, F.IsUltra ∧ (∀ i, F (sets pairs i) ↔ label pairs y i = true) ∧
      ∀ l, x l = true → F (sources l) := by
  have hmono : ∀ i j, sets pairs i ⊆ sets pairs j →
      label pairs y i = true → label pairs y j = true := by
    intro i j hij hi
    by_contra hj
    exact h ⟨j, by simpa using hj, Or.inl ⟨i, hij, hi⟩⟩
  have hcover : ∀ i j, sets pairs i ∪ sets pairs j = Set.univ →
      label pairs y i = true ∨ label pairs y j = true := by
    intro i j hij
    by_contra h'
    have hi : label pairs y i = false := by simpa using (not_or.mp h').1
    have hj : label pairs y j = false := by simpa using (not_or.mp h').2
    exact h ⟨i, hi, Or.inr (Or.inl ⟨j, hij, hj⟩)⟩
  obtain ⟨F, hF, hl, hmax⟩ := Semifilter.exists_isUltra_of_labels
    (sets pairs) (label pairs y) none rfl rfl hmono hcover
  refine ⟨F, hF, hl, fun l hx => (hmax _).mpr ?_⟩
  intro j hj hsub
  exact h ⟨j, hj, Or.inr (Or.inr ⟨l, hsub, hx⟩)⟩

/-- A point supplies a consistent certificate, including when the pair list is empty. -/
noncomputable def pointLabels (u : U) (i : Fin (size pairs)) : Bool :=
  @decide (u ∈ sets pairs (some i)) (Classical.propDecidable _)

/-- The extended point certificate labels `i` by `true` if and only if `u ∈ sets pairs i`. -/
@[simp] theorem label_pointLabels (u : U) (i : Option (Fin (size pairs))) :
    label pairs (pointLabels pairs u) i = true ↔ u ∈ sets pairs i := by
  cases i with
  | none => simp [label, sets]
  | some i => simp only [label, pointLabels, decide_eq_true_eq]

/-- Point membership has no consistency violation whenever all required sources contain it. -/
theorem not_invalid_pointLabels {n : ℕ} (sources : Fin n → Set U) (x : Fin n → Bool)
    (u : U) (hx : ∀ l, x l = true → u ∈ sources l) :
    ¬ Invalid pairs sources x (pointLabels pairs u) := by
  rintro ⟨j, hj, h | h | h⟩
  · obtain ⟨i, hij, hi⟩ := h
    have := (label_pointLabels pairs u j).mpr (hij ((label_pointLabels pairs u i).mp hi))
    simp_all
  · obtain ⟨k, hjk, hk⟩ := h
    have hu : u ∈ sets pairs j ∪ sets pairs k := hjk ▸ Set.mem_univ u
    rcases hu with hu | hu
    · have := (label_pointLabels pairs u j).mpr hu
      simp_all
    · have := (label_pointLabels pairs u k).mpr hu
      simp_all
  · obtain ⟨l, hlj, hl⟩ := h
    have := (label_pointLabels pairs u j).mpr (hlj (hx l hl))
    simp_all

/-- Point membership preserves every intersection pair. -/
theorem not_breaksPair_pointLabels (u : U) : ¬ BreaksPair pairs (pointLabels pairs u) := by
  rintro ⟨i, hi, hj, hk⟩
  have hi' : u ∈ (pairs.get i).1 := by simpa [pointLabels] using hi
  have hj' : u ∈ (pairs.get i).2 := by simpa [pointLabels] using hj
  have hk' : pointLabels pairs u (inter pairs i) = true := by
    simpa only [pointLabels, sets_inter, decide_eq_true_eq, Set.mem_inter_iff] using
      And.intro hi' hj'
  simp_all

end Cslib.Circuits.Fusion.PairCertificate

namespace Cslib.Circuits.Fusion

open PairCertificate

/-- Above a target point, every certificate either is inconsistent or breaks a cover pair. -/
theorem PairCover.invalid_or_breaksPair {X : Type*} {n : ℕ} {target : Set X}
    {input : Fin n → Set X} (c : PairCover target input Semifilter.IsUltra) (x : target)
    (y : Fin (size c.pairs) → Bool) :
    Invalid c.pairs (fun i => Subtype.val ⁻¹' input i)
      (fun i => @decide (x.val ∈ input i) (Classical.propDecidable _)) y ∨
      BreaksPair c.pairs y := by
  classical
  by_contra h
  obtain ⟨F, hF, hl, ha⟩ := exists_filter_of_not_invalid c.pairs _ _ y (not_or.mp h).1
  let w : SemifilterWitness target input Semifilter.IsUltra :=
    ⟨x, F, hF, fun i hi => ha i (by simpa using hi)⟩
  apply c.isCover w
  intro p hp hleft hright
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
  by_contra hinter
  have hi : y (left c.pairs i) = true :=
    (hl (some (left c.pairs i))).mp (by simpa using hleft)
  have hj : y (right c.pairs i) = true :=
    (hl (some (right c.pairs i))).mp (by simpa using hright)
  have hk : y (inter c.pairs i) = false := by
    by_contra hk
    apply hinter
    have := (hl (some (inter c.pairs i))).mpr (by simpa [label] using hk)
    simpa using this
  exact (not_or.mp h).2 ⟨i, hi, hj, hk⟩

end Cslib.Circuits.Fusion
