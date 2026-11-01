/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Codes
public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.FinRange

/-!
# Finite prefixes for the native sparse box query

Tasks retain an ordinary list of existing tensor terms. Their machine fields are its
length, little-endian decimal code, number of non-P0 inner choices, and initial P0 count.
The definitions describe finite prefix data, with no execution or resource certificates.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Finset Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Extend an output beyond its real depth only to make prefix operations total. -/
@[expose] def outAt {L : ℕ} (η : OutStr L) (k : ℕ) : OutVar :=
  if h : k < L then η ⟨k, h⟩ else .z 0 0

@[simp] theorem outAt_fin {L : ℕ} (η : OutStr L) (k : Fin L) :
    outAt η k.val = η k := by simp [outAt, k.isLt]

/-- Existing native term digits accumulated in least-significant-first order. -/
@[expose] def prefixCode (xs : List Term) : ℕ :=
  Nat.ofDigits 10 (xs.map fun lam => (Encoding.termDigits.symm lam).val)

/-- Number of inner non-P0 choices in a prefix beginning at the supplied level. -/
@[expose] def usedFrom {L : ℕ} (η : OutStr L) : ℕ → List Term → ℕ
  | _, [] => 0
  | k, lam :: xs =>
    (if (outAt η k).IsInner ∧ lam ≠ .P0 then 1 else 0) + usedFrom η (k + 1) xs

/-- Initial inner P0 choices, ending at the first non-P0 inner coordinate. -/
@[expose] def starsFrom {L : ℕ} (η : OutStr L) : ℕ → List Term → ℕ
  | _, [] => 0
  | k, lam :: xs =>
    if (outAt η k).IsInner then
      if lam = .P0 then 1 + starsFrom η (k + 1) xs else 0
    else starsFrom η (k + 1) xs

/-- Prefix compatibility uses the existing tensor contribution relation at each coordinate. -/
@[expose] def Compatible {L : ℕ} (η : OutStr L) : ℕ → List Term → Prop
  | _, [] => True
  | k, lam :: xs => lam.Contributes (outAt η k) ∧ Compatible η (k + 1) xs

instance {L : ℕ} (η : OutStr L) (k : ℕ) (xs : List Term) :
    Decidable (Compatible η k xs) := by
  induction xs generalizing k with
  | nil => exact isTrue trivial
  | cons lam xs ih => exact inferInstanceAs
      (Decidable (lam.Contributes (outAt η k) ∧ Compatible η (k + 1) xs))

/-- A valid logical task is a compatible prefix within the original order budget. -/
@[expose] def Good {L : ℕ} (η : OutStr L) (t : ℕ) (xs : List Term) : Prop :=
  xs.length ≤ L ∧ Compatible η 0 xs ∧ usedFrom η 0 xs ≤ t

instance {L : ℕ} (η : OutStr L) (t : ℕ) (xs : List Term) : Decidable (Good η t xs) :=
  inferInstanceAs (Decidable (xs.length ≤ L ∧ Compatible η 0 xs ∧ usedFrom η 0 xs ≤ t))

@[simp] theorem prefixCode_nil : prefixCode [] = 0 := rfl

/-- Appending one real term gives the actual native add/multiply code update. -/
theorem prefixCode_append (xs : List Term) (lam : Term) :
    prefixCode (xs ++ [lam]) = prefixCode xs +
      (Encoding.termDigits.symm lam).val * 10 ^ xs.length := by
  simp only [prefixCode, List.map_append, List.map_cons, List.map_nil,
    Nat.ofDigits_append, List.length_map, Nat.ofDigits_singleton]
  rw [Nat.mul_comm]

/-- Every partial code is below the next actual decimal power. -/
theorem prefixCode_lt (xs : List Term) : prefixCode xs < 10 ^ xs.length := by
  simpa only [prefixCode, List.length_map] using Nat.ofDigits_lt_base_pow_length
    (l := xs.map fun lam => (Encoding.termDigits.symm lam).val)
    (by decide : 1 < (10 : ℕ)) (by
      intro x hx
      obtain ⟨lam, _, rfl⟩ := List.mem_map.mp hx
      exact (Encoding.termDigits.symm lam).isLt)

theorem usedFrom_le {L : ℕ} (η : OutStr L) (k : ℕ) (xs : List Term) :
    usedFrom η k xs ≤ xs.length := by
  induction xs generalizing k with
  | nil => simp [usedFrom]
  | cons lam xs ih =>
    simp only [usedFrom, List.length_cons]
    split <;> have := ih (k + 1) <;> omega

theorem starsFrom_le {L : ℕ} (η : OutStr L) (k : ℕ) (xs : List Term) :
    starsFrom η k xs ≤ xs.length := by
  induction xs generalizing k with
  | nil => simp [starsFrom]
  | cons lam xs ih =>
    simp only [starsFrom, List.length_cons]
    split
    · split <;> have := ih (k + 1) <;> omega
    · exact (ih (k + 1)).trans (by omega)

/-- Inner-choice counts add across adjacent prefix segments. -/
theorem usedFrom_append {L : ℕ} (η : OutStr L) (k : ℕ) (xs ys : List Term) :
    usedFrom η k (xs ++ ys) = usedFrom η k xs + usedFrom η (k + xs.length) ys := by
  induction xs generalizing k with
  | nil => simp [usedFrom]
  | cons lam xs ih =>
    simp [usedFrom, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Initial stars continue into a later segment exactly while no inner non-P0 occurred. -/
theorem starsFrom_append {L : ℕ} (η : OutStr L) (k : ℕ) (xs ys : List Term) :
    starsFrom η k (xs ++ ys) = starsFrom η k xs +
      if usedFrom η k xs = 0 then starsFrom η (k + xs.length) ys else 0 := by
  induction xs generalizing k with
  | nil => simp [starsFrom, usedFrom]
  | cons lam xs ih =>
    simp only [List.cons_append, starsFrom, usedFrom, List.length_cons]
    have hshift : k + (xs.length + 1) = k + 1 + xs.length := by omega
    rw [hshift]
    by_cases hi : (outAt η k).IsInner <;> by_cases hp : lam = .P0
    all_goals simp [hi, hp, ih, Nat.add_assoc]

/-- Compatibility composes along real adjacent coordinates. -/
theorem compatible_append {L : ℕ} (η : OutStr L) (k : ℕ) (xs ys : List Term) :
    Compatible η k (xs ++ ys) ↔ Compatible η k xs ∧ Compatible η (k + xs.length) ys := by
  induction xs generalizing k with
  | nil => simp [Compatible]
  | cons lam xs ih =>
    simp [Compatible, ih, Nat.add_left_comm, Nat.add_comm, and_assoc]

/-- The actual used-count update when a child term is appended. -/
theorem usedFrom_append_one {L : ℕ} (η : OutStr L) (xs : List Term) (lam : Term) :
    usedFrom η 0 (xs ++ [lam]) = usedFrom η 0 xs +
      if (outAt η xs.length).IsInner ∧ lam ≠ .P0 then 1 else 0 := by
  simp [usedFrom_append, usedFrom]

/-- The actual initial-star update needed by a threshold box key. -/
theorem starsFrom_append_one {L : ℕ} (η : OutStr L) (xs : List Term) (lam : Term) :
    starsFrom η 0 (xs ++ [lam]) = starsFrom η 0 xs +
      if (outAt η xs.length).IsInner ∧ lam = .P0 ∧ usedFrom η 0 xs = 0 then 1 else 0 := by
  rw [starsFrom_append]
  by_cases hused : usedFrom η 0 xs = 0 <;>
    by_cases hi : (outAt η xs.length).IsInner <;> by_cases hp : lam = .P0
  all_goals simp [starsFrom, hused, hi, hp]

/-- Permitted child terms, expressed using existing contribution and the real order budget. -/
@[expose] def allowedTerms {L : ℕ} (η : OutStr L) (t : ℕ) (xs : List Term) : Finset Term :=
  univ.filter fun lam => lam.Contributes (outAt η xs.length) ∧
    usedFrom η 0 xs + (if (outAt η xs.length).IsInner ∧ lam ≠ .P0 then 1 else 0) ≤ t

/-- Each actual child has precisely the same finite validity test as the prefix invariant. -/
theorem good_append_iff {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (hk : xs.length < L) (lam : Term) :
    Good η t (xs ++ [lam]) ↔ lam ∈ allowedTerms η t xs := by
  simp only [Good, List.length_append, List.length_singleton, compatible_append,
    Nat.zero_add, Compatible, and_true, usedFrom_append_one, allowedTerms,
    mem_filter, mem_univ, true_and]
  exact ⟨fun h => ⟨h.2.1.2, h.2.2⟩,
    fun h => ⟨by omega, ⟨hx.2.1, h.1⟩, h.2⟩⟩

/-- At an inner coordinate, P0 is always available and indexed terms require spare budget. -/
theorem mem_allowedTerms_inner {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : usedFrom η 0 xs ≤ t) (hi : (outAt η xs.length).IsInner) (lam : Term) :
    lam ∈ allowedTerms η t xs ↔ lam = .P0 ∨ usedFrom η 0 xs < t := by
  have hc : lam.Contributes (outAt η xs.length) :=
    (Term.contributes_iff _ _).mpr (Or.inl hi)
  simp only [allowedTerms, mem_filter, mem_univ, true_and, hc, hi, true_and]
  by_cases hp : lam = .P0
  · simp [hp, hx]
  · rw [ite_eq_left hp]
    simp only [hp, false_or]
    omega

/-- At an outer coordinate only its existing private term is permitted. -/
theorem mem_allowedTerms_outer {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : usedFrom η 0 xs ≤ t) (hi : ¬(outAt η xs.length).IsInner) (lam : Term) :
    lam ∈ allowedTerms η t xs ↔ lam = (outAt η xs.length).privateTerm := by
  simp [allowedTerms, Term.contributes_iff, hi, hx]

/-- Every internal valid task has a child, independently of the remaining order budget. -/
theorem allowedTerms_nonempty {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) : (allowedTerms η t xs).Nonempty := by
  by_cases hi : (outAt η xs.length).IsInner
  · exact ⟨.P0, (mem_allowedTerms_inner hx.2.2 hi _).mpr (Or.inl rfl)⟩
  · exact ⟨_, (mem_allowedTerms_outer hx.2.2 hi _).mpr rfl⟩

theorem card_allowedTerms_le {L : ℕ} (η : OutStr L) (t : ℕ) (xs : List Term) :
    (allowedTerms η t xs).card ≤ 10 := by
  simpa only [card_univ, card_term] using card_le_univ (allowedTerms η t xs)

private theorem indexed_ne_P0 (d : Fin 9) :
    Encoding.termDigits ⟨d.val, by omega⟩ ≠ Term.P0 := by decide +revert

private theorem ne_P0_iff_indexed (lam : Term) :
    lam ≠ .P0 ↔ ∃ d : Fin 9, Encoding.termDigits ⟨d.val, by omega⟩ = lam := by
  decide +revert

/-- Ordered children matching the native push order, with P0 first at inner coordinates. -/
@[expose] def children {L : ℕ} (η : OutStr L) (t : ℕ) (xs : List Term) : List (List Term) :=
  if (outAt η xs.length).IsInner then
    (xs ++ [.P0]) :: (if usedFrom η 0 xs < t then
      List.ofFn fun d : Fin 9 => xs ++ [Encoding.termDigits ⟨d.val, by omega⟩] else [])
  else [xs ++ [(outAt η xs.length).privateTerm]]

/-- The ordered native family contains exactly the existing permitted terms. -/
theorem mem_children {L t : ℕ} {η : OutStr L} {xs ys : List Term}
    (hx : usedFrom η 0 xs ≤ t) :
    ys ∈ children η t xs ↔ ∃ lam ∈ allowedTerms η t xs, ys = xs ++ [lam] := by
  by_cases hi : (outAt η xs.length).IsInner
  · rw [children, ite_eq_left hi]
    by_cases hu : usedFrom η 0 xs < t
    · simp only [hu, ite_true, List.mem_cons, List.mem_ofFn]
      constructor
      · rintro (rfl | ⟨d, rfl⟩)
        · exact ⟨.P0, (mem_allowedTerms_inner hx hi _).mpr (Or.inl rfl), rfl⟩
        · exact ⟨_, (mem_allowedTerms_inner hx hi _).mpr (Or.inr hu), rfl⟩
      · rintro ⟨lam, _, rfl⟩
        by_cases hp : lam = .P0
        · exact Or.inl (by rw [hp])
        · obtain ⟨d, hd⟩ := (ne_P0_iff_indexed lam).mp hp
          exact Or.inr ⟨d, by rw [hd]⟩
    · simp only [hu, ite_false, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro rfl
        exact ⟨.P0, (mem_allowedTerms_inner hx hi _).mpr (Or.inl rfl), rfl⟩
      · rintro ⟨lam, hlam, rfl⟩
        have hp := ((mem_allowedTerms_inner hx hi lam).mp hlam).resolve_right hu
        rw [hp]
  · rw [children, ite_eq_right hi]
    simp only [List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨_, (mem_allowedTerms_outer hx hi _).mpr rfl, rfl⟩
    · rintro ⟨lam, hlam, rfl⟩
      rw [(mem_allowedTerms_outer hx hi lam).mp hlam]

/-- Each native child is a valid later prefix. -/
theorem good_of_mem_children {L t : ℕ} {η : OutStr L} {xs ys : List Term}
    (hx : Good η t xs) (hk : xs.length < L) (hy : ys ∈ children η t xs) : Good η t ys := by
  obtain ⟨lam, hlam, rfl⟩ := (mem_children hx.2.2).mp hy
  exact (good_append_iff hx hk lam).mpr hlam

/-- Each child advances exactly one original level. -/
theorem length_of_mem_children {L t : ℕ} {η : OutStr L} {xs ys : List Term}
    (hx : usedFrom η 0 xs ≤ t) (hy : ys ∈ children η t xs) : ys.length = xs.length + 1 := by
  obtain ⟨lam, _, rfl⟩ := (mem_children hx).mp hy
  simp

/-- Distinct native labels give distinct children, including the distinguished P0 branch. -/
theorem children_nodup {L : ℕ} (η : OutStr L) (t : ℕ) (xs : List Term) :
    (children η t xs).Nodup := by
  let indexed := List.ofFn fun d : Fin 9 => xs ++ [Encoding.termDigits ⟨d.val, by omega⟩]
  have hinj : (fun d : Fin 9 => xs ++ [Encoding.termDigits ⟨d.val, by omega⟩]).Injective := by
    intro i j hij
    have hd : Encoding.termDigits ⟨i.val, by omega⟩ =
        Encoding.termDigits ⟨j.val, by omega⟩ := by
      simpa only [List.cons.injEq, and_true] using List.append_cancel_left hij
    exact Fin.ext (congrArg (fun z : Fin 10 => z.val) (Encoding.termDigits.injective hd))
  have hn : indexed.Nodup := List.nodup_ofFn.mpr hinj
  have hnot : xs ++ [.P0] ∉ indexed := by
    intro h
    obtain ⟨d, hd⟩ := List.mem_ofFn.mp h
    have hp : Encoding.termDigits ⟨d.val, by omega⟩ = Term.P0 := by
      simpa only [List.cons.injEq, and_true] using List.append_cancel_left hd
    exact indexed_ne_P0 d hp
  unfold children
  split
  · split
    · exact List.nodup_cons.mpr ⟨hnot, hn⟩
    · simp
  · simp

/-- The native constant-size fanout never exceeds ten tasks. -/
theorem children_length_le {L : ℕ} (η : OutStr L) (t : ℕ) (xs : List Term) :
    (children η t xs).length ≤ 10 := by
  unfold children
  split
  · split <;> simp
  · simp

/-- The ordered native children are the image of the finite permitted label set. -/
theorem children_toFinset {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : usedFrom η 0 xs ≤ t) :
    (children η t xs).toFinset = (allowedTerms η t xs).image (fun lam => xs ++ [lam]) := by
  ext ys
  simp only [List.mem_toFinset, mem_image]
  rw [mem_children hx]
  exact exists_congr fun lam => and_congr_right fun _ => eq_comm

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
