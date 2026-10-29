/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SubsetSum.Mask
public import Complexity.Computability.Complexity.Problems.ThreeSAT
public import Complexity.Logics.Propositional.CNF.ModelCount
import Complexity.Computability.Complexity.Problems.SubsetSum.Digits
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Logics.Propositional.CNF.PolyTime
import Mathlib.Data.List.GetD

/-!
# Subset sum

`SubsetSum` is the set of pairs `(a, t)` of a list `a` of natural numbers, possibly with
repetitions, and a target `t` such that some sub-multiset of `a` sums to `t` [Sipser, Section
7.3][Sipser2013]. All numbers are encoded in binary (`Turing.MultiTapeTM.encNat`, digits least
significant first); the `NP`-hardness proved here is for this encoding and is not strong
`NP`-hardness. A certificate is a mask selecting entries of `a` (`Cslib.Complexity.maskSelect`),
and the verifier adds the selected numbers in binary.

Sipser's reduction from 3SAT [Sipser, Theorem 7.56][Sipser2013] gives each of the `n` variables
of a formula, numbered by first occurrence (`Cslib.Logic.PL.CNF.distinctVars`), and each of its `m`
clauses a digit position. Each variable has two literal numbers, with digit one at the position of
the variable and at the positions of the clauses containing the literal (`ThreeSAT.literalDigits`);
each clause has two slack numbers with digit one at its position only. The target has digit one
at every variable position and three at every clause position. At each position, all numbers
together have at most five digits one, so no subfamily produces carries in any base above five
(`Cslib.Complexity.sum_sum_pow_eq_iff`). We use base 8 rather than Sipser's base 10, so that
digits are blocks of three bits; every number has at most `n + m` base-8 digits
(`ThreeSAT.lt_of_mem_digitNumbers`, `ThreeSAT.digitTarget_lt`). Variable labels only enter through
their order of first occurrence, so large binary labels do not enlarge the numbers. A literal
repeated in a clause counts once, and a clause containing both literals of a variable is covered
by both of its literal numbers. Formulas with a clause of more than three literals are not in
`ThreeSAT` and are mapped to an instance without solutions.

## Main definitions

* `Cslib.Complexity.SubsetSum`, `Cslib.Complexity.SubsetSum.verifier`.
* `Cslib.Complexity.ThreeSAT.literalDigits`,
  `Cslib.Complexity.ThreeSAT.digitNumbers`, `Cslib.Complexity.ThreeSAT.digitTarget`.
* `Cslib.Complexity.ThreeSAT.toSubsetSum`: Sipser's reduction.

## Main results

* `Cslib.Complexity.mem_SubsetSum_iff_sublist`: solutions are subsequences of the numbers.
* `Cslib.Complexity.SubsetSum.isVerifier`, `Cslib.Complexity.SubsetSum.mem_NP`:
  `SubsetSum ∈ NP (encPair (encList encNat) encNat)`.
* `Cslib.Complexity.ThreeSAT.digit_mem_SubsetSum_iff_counts`,
  `Cslib.Complexity.ThreeSAT.counts_iff_satisfiable`: the digit construction has a solution
  exactly when the digit positions can be filled, exactly when the formula is satisfiable.
* `Cslib.Complexity.ThreeSAT.toSubsetSum_mem_iff`: correctness of Sipser's reduction.
* `Cslib.Complexity.ThreeSAT.lt_of_mem_digitNumbers`, `Cslib.Complexity.ThreeSAT.digitTarget_lt`:
  the numbers have `O(n + m)` digits.
* `Cslib.Complexity.ThreeSAT.computableInPolyTime_toSubsetSum`: the reduction is
  polynomial-time.
* `Cslib.Complexity.polyTimeReducible_ThreeSAT_SubsetSum`, `Cslib.Complexity.SubsetSum_npHard`,
  `Cslib.Complexity.SubsetSum_npComplete`: `SubsetSum` is `NP`-complete.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime
open scoped List

/-- The instances `(a, t)` of subset sum: some sub-multiset of the numbers `a` sums to `t`
[Karp1972], [Sipser, Chapter 7][Sipser2013]. -/
def SubsetSum : Set (List ℕ × ℕ) := {x | ∃ s ≤ (x.1 : Multiset ℕ), s.sum = x.2}

theorem mem_SubsetSum {x : List ℕ × ℕ} :
    x ∈ SubsetSum ↔ ∃ s ≤ (x.1 : Multiset ℕ), s.sum = x.2 :=
  Iff.rfl

/-- Subset sum asks for a subsequence of the numbers with the target sum. -/
theorem mem_SubsetSum_iff_sublist {x : List ℕ × ℕ} :
    x ∈ SubsetSum ↔ ∃ s, s <+ x.1 ∧ s.sum = x.2 := by
  simpa only [Multiset.sum_coe] using
    mem_SubsetSum.trans (exists_le_coe_iff_exists_sublist (fun s => s.sum = x.2))

/-- A sub-multiset of the values of a duplicate-free list sums to `t` exactly when a subset of
the list does. -/
theorem map_mem_SubsetSum_iff {ι : Type*} [DecidableEq ι] {xs : List ι} (hxs : xs.Nodup)
    (f : ι → ℕ) (t : ℕ) :
    (xs.map f, t) ∈ SubsetSum ↔ ∃ F ⊆ xs.toFinset, ∑ x ∈ F, f x = t := by
  rw [mem_SubsetSum_iff_sublist]
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨ys, hys, rfl⟩ := List.sublist_map_iff.1 hs
    exact ⟨ys.toFinset, fun x hx => List.mem_toFinset.2 (hys.subset (List.mem_toFinset.1 hx)),
      List.sum_toFinset _ (hxs.sublist hys)⟩
  · rintro ⟨F, hF, rfl⟩
    refine ⟨(xs.filter (· ∈ F)).map f, (List.filter_sublist).map f, ?_⟩
    rw [← List.sum_toFinset _ (hxs.filter _)]
    congr 1
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.1 (hF h), h⟩⟩

/-- A list has no more entries than the length of its encoding paired with any second
component. -/
theorem length_le_length_encPair {α β : Type} (encA : α ↪ List Bool) (enc : β ↪ List Bool)
    (x : List α × β) : x.1.length ≤ (encPair (encList encA) enc x).length := by
  have := length_le_length_encList encA x.1
  simp only [length_encPair]
  lia

namespace SubsetSum

/-- The verifier for `SubsetSum`: the numbers selected by the certificate mask sum to the
target. -/
def verifier (x : (List ℕ × ℕ) × List Bool) : Bool := decide ((maskSelect x.1.1 x.2).sum = x.1.2)

/-- `SubsetSum.verifier` verifies `SubsetSum` with certificates as long as the encoded
instance. -/
theorem isVerifier :
    IsVerifier (encPair (encList encNat) encNat) Polynomial.X verifier SubsetSum := by
  intro x
  simp only [mem_SubsetSum, Polynomial.eval_X, verifier, decide_eq_true_eq]
  simpa only [Multiset.sum_coe] using exists_le_iff_exists_maskSelect
    (length_le_length_encPair encNat encNat x) (fun s => s.sum = x.2)

/-- The `SubsetSum` verifier is polynomial-time: it selects the masked numbers, adds them in
binary and compares the sum with the target. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier
      (encPair (encPair (encList encNat) encNat) encBits) encBool := by
  unfold verifier
  fun_prop

/-- `SubsetSum` belongs to `NP`. -/
theorem mem_NP : SubsetSum ∈ NP (encPair (encList encNat) encNat) :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end SubsetSum

namespace ThreeSAT

/-! ### The digit construction -/

/-- Whether clause `j` of `φ` contains the literal of sign `b` of variable number `i` of
`φ.distinctVars`. -/
def covers (φ : CNF ℕ) (i : ℕ) (b : Bool) (j : ℕ) : Bool :=
  (φ.getD j []).any fun l => φ.distinctVars.idxOf l.1 == i && l.2 == b

/-- The digit positions of the number of a literal: the position `i` of its variable, and the
position `φ.distinctVars.length + j` of every clause `j` containing it. -/
def literalDigits (φ : CNF ℕ) (i : ℕ) (b : Bool) : List ℕ :=
  i :: ((List.range φ.length).filter (covers φ i b)).map (φ.distinctVars.length + ·)

/-- The number whose base-8 digits are one at the positions `ps` and zero elsewhere, for distinct
positions. -/
def octal (ps : List ℕ) : ℕ := (ps.map (8 ^ ·)).sum

/-- The numbers of the digit construction: two literal numbers for each variable, and two slack
numbers with the single digit of each clause. -/
def digitNumbers (φ : CNF ℕ) : List ℕ :=
  ((List.range φ.distinctVars.length).flatMap fun i =>
      [octal (literalDigits φ i true), octal (literalDigits φ i false)]) ++
    (List.range φ.length).flatMap fun j =>
      [8 ^ (φ.distinctVars.length + j), 8 ^ (φ.distinctVars.length + j)]

/-- The target of the digit construction: digit one at each variable position and digit three at
each clause position. -/
def digitTarget (φ : CNF ℕ) : ℕ :=
  ((List.range φ.distinctVars.length).map (8 ^ ·)).sum +
    ((List.range φ.length).map fun j => 3 * 8 ^ (φ.distinctVars.length + j)).sum

/-- Sipser's reduction from `ThreeSAT` to `SubsetSum`: the digit construction for formulas whose
clauses have at most three literals, and an instance without solutions otherwise. -/
def toSubsetSum (φ : CNF ℕ) : List ℕ × ℕ :=
  if φ.all fun c => decide (c.length ≤ 3) then (digitNumbers φ, digitTarget φ) else ([], 1)

/-! ### Correctness -/

section Correctness

open Finset

variable {φ : CNF ℕ}

/-- The variable of every literal of `φ` is listed in `φ.distinctVars`. -/
private theorem mem_distinctVars_of_mem {j : ℕ} {l : Literal ℕ} (hl : l ∈ φ.getD j []) :
    l.1 ∈ φ.distinctVars := by
  refine CNF.mem_distinctVars.2 ?_
  rcases Nat.lt_or_ge j φ.length with hj | hj
  · rw [List.getD_eq_getElem _ _ hj] at hl
    exact List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨_, List.getElem_mem hj, hl⟩, rfl⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj] at hl
    simp at hl

/-- Clause `j` covers the literal number `(i, b)` when it contains a literal of sign `b` whose
variable is number `i` of `φ.distinctVars`. -/
theorem covers_eq_true_iff {i : ℕ} {b : Bool} {j : ℕ} :
    covers φ i b j = true ↔ ∃ l ∈ φ.getD j [], φ.distinctVars.idxOf l.1 = i ∧ l.2 = b := by
  simp [covers]

/-- A clause covers at most as many literal numbers as it has literals. -/
private theorem card_filter_covers_le (A : Finset (ℕ × Bool)) (j : ℕ) :
    #{a ∈ A | covers φ a.1 a.2 j} ≤ (φ.getD j []).length := by
  classical
  calc #{a ∈ A | covers φ a.1 a.2 j}
      ≤ #(((φ.getD j []).map fun l => (φ.distinctVars.idxOf l.1, l.2)).toFinset) := by
        refine card_le_card fun a ha => ?_
        obtain ⟨l, hl, hi, hb⟩ := covers_eq_true_iff.1 (mem_filter.1 ha).2
        exact List.mem_toFinset.2 (List.mem_map.2 ⟨l, hl, by rw [hi, hb]⟩)
    _ ≤ _ := (List.toFinset_card_le _).trans (List.length_map ..).le

private theorem card_filter_fst_le (A : Finset (ℕ × Bool)) (i : ℕ) : #{a ∈ A | a.1 = i} ≤ 2 := by
  calc #{a ∈ A | a.1 = i} ≤ #({(i, true), (i, false)} : Finset (ℕ × Bool)) :=
        card_le_card fun a ha => by
          obtain ⟨a₁, a₂⟩ := a
          obtain rfl : a₁ = i := (mem_filter.1 ha).2
          cases a₂ <;> simp
    _ ≤ 2 := card_le_two

/-- The positions of the digits one of a literal number. -/
private theorem mem_literalDigits {i : ℕ} {b : Bool} {p : ℕ} :
    p ∈ literalDigits φ i b ↔
      p = i ∨ ∃ j < φ.length, covers φ i b j = true ∧ p = φ.distinctVars.length + j := by
  simp only [literalDigits, List.mem_cons, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro (h | ⟨j, ⟨hj, hc⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, hc, rfl⟩
  · rintro (h | ⟨j, hj, hc, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, ⟨hj, hc⟩, rfl⟩

private theorem nodup_literalDigits {i : ℕ} (hi : i < φ.distinctVars.length) (b : Bool) :
    (literalDigits φ i b).Nodup := by
  refine List.nodup_cons.2 ⟨fun h => ?_, ((List.nodup_range).filter _).map
    (fun _ _ h => Nat.add_left_cancel h)⟩
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 h
  lia

/-- The items of the digit construction: literal numbers `(i, b)` and slack numbers `(j, c)`. -/
abbrev Item : Type := (ℕ × Bool) ⊕ (ℕ × Bool)

/-- The digit positions of an item. -/
private def itemDigits (φ : CNF ℕ) : Item → List ℕ :=
  Sum.elim (fun a => literalDigits φ a.1 a.2) fun c => [φ.distinctVars.length + c.1]

/-- The items of the digit construction, in the order of `digitNumbers`. -/
private def items (φ : CNF ℕ) : List Item :=
  ((List.range φ.distinctVars.length).flatMap fun i => [.inl (i, true), .inl (i, false)]) ++
    (List.range φ.length).flatMap fun j => [.inr (j, true), .inr (j, false)]

private theorem digitNumbers_eq_map : digitNumbers φ = (items φ).map fun x => octal
    (itemDigits φ x) := by
  simp [digitNumbers, items, List.map_flatMap, itemDigits, octal]

/-- All items, as a finite set. -/
private def itemSet (φ : CNF ℕ) : Finset Item :=
  (range φ.distinctVars.length ×ˢ univ).disjSum (range φ.length ×ˢ univ)

private theorem mem_items {x : Item} : x ∈ items φ ↔ x ∈ itemSet φ := by
  rcases x with ⟨i, b⟩ | ⟨j, c⟩
  · cases b <;> simp [items, itemSet]
  · cases c <;> simp [items, itemSet]

private theorem nodup_items : (items φ).Nodup := by
  refine List.Nodup.append ?_ ?_ ?_
  · refine List.nodup_flatMap.2 ⟨fun i _ => by simp, ?_⟩
    exact List.nodup_range.pairwise_of_forall_ne fun i _ i' _ h => by
      simpa [Function.onFun] using h.symm
  · refine List.nodup_flatMap.2 ⟨fun j _ => by simp, ?_⟩
    exact List.nodup_range.pairwise_of_forall_ne fun j _ j' _ h => by
      simpa [Function.onFun] using h.symm
  · simp [List.disjoint_left]

/-- The digit positions of an item, as a finite set. -/
private def itemCol (φ : CNF ℕ) (x : Item) : Finset ℕ := (itemDigits φ x).toFinset

private theorem octal_itemDigits {x : Item} (hx : x ∈ itemSet φ) :
    octal (itemDigits φ x) = ∑ p ∈ itemCol φ x, 8 ^ p := by
  rw [itemCol, List.sum_toFinset _ ?_, octal]
  rcases x with a | c
  · exact nodup_literalDigits (by simpa [itemSet] using hx) a.2
  · simp [itemDigits]

private theorem itemCol_subset {x : Item} (hx : x ∈ itemSet φ) :
    itemCol φ x ⊆ range (φ.distinctVars.length + φ.length) := by
  intro p hp
  rw [itemCol, List.mem_toFinset] at hp
  rw [mem_range]
  rcases x with a | c
  · have ha : a.1 < φ.distinctVars.length := by simpa [itemSet] using hx
    rcases mem_literalDigits.1 hp with rfl | ⟨j, hj, -, rfl⟩ <;> lia
  · have hc : c.1 < φ.length := by simpa [itemSet] using hx
    simp only [itemDigits, Sum.elim_inr, List.mem_singleton] at hp
    lia

/-- Membership of a variable position in the digits of a literal number. -/
private theorem mem_itemCol_inl_of_lt {a : ℕ × Bool} {i : ℕ} (hi : i < φ.distinctVars.length) :
    i ∈ itemCol φ (.inl a) ↔ a.1 = i := by
  rw [itemCol, List.mem_toFinset, itemDigits, Sum.elim_inl]
  refine ⟨fun h => ?_, fun h => mem_literalDigits.2 (Or.inl h.symm)⟩
  rcases mem_literalDigits.1 h with h | ⟨j, -, -, rfl⟩
  · exact h.symm
  · lia

/-- Membership of a clause position in the digits of a literal number. -/
private theorem mem_itemCol_inl_clause {a : ℕ × Bool} (ha : a.1 < φ.distinctVars.length) {j : ℕ}
    (hj : j < φ.length) :
    φ.distinctVars.length + j ∈ itemCol φ (.inl a) ↔ covers φ a.1 a.2 j = true := by
  rw [itemCol, List.mem_toFinset, itemDigits, Sum.elim_inl, mem_literalDigits]
  constructor
  · rintro (h | ⟨j', -, hc, h⟩)
    · lia
    · rwa [Nat.add_left_cancel h]
  · exact fun h => Or.inr ⟨j, hj, h, rfl⟩

private theorem mem_itemCol_inr {c : ℕ × Bool} {p : ℕ} :
    p ∈ itemCol φ (.inr c) ↔ p = φ.distinctVars.length + c.1 := by
  simp [itemCol, itemDigits]

/-- Column counts split into literal numbers and slack numbers. -/
private theorem card_filter_disjSum (A B : Finset (ℕ × Bool)) (p : ℕ) :
    #{x ∈ A.disjSum B | p ∈ itemCol φ x} =
      #{a ∈ A | p ∈ itemCol φ (.inl a)} + #{c ∈ B | p ∈ itemCol φ (.inr c)} := by
  rw [← card_disjSum]
  congr 1
  ext x
  rcases x with a | c <;> simp

/-- The target as a number with base-8 digits: one at variable positions, three at clause
positions. -/
private theorem digitTarget_eq :
    digitTarget φ = ∑ p ∈ range (φ.distinctVars.length + φ.length),
      (if p < φ.distinctVars.length then 1 else 3) * 8 ^ p := by
  have hlist (n : ℕ) (f : ℕ → ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
    rw [sum_eq_multiset_sum, range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]
  rw [sum_range_add, digitTarget, hlist, hlist]
  congr 1
  · exact sum_congr rfl fun p hp => by simp [mem_range.1 hp]
  · exact sum_congr rfl fun j _ => by simp

/-- **Size of the digit construction.** Every number has at most
`φ.distinctVars.length + φ.length` base-8 digits, that is, three binary digits per variable and
per clause. -/
theorem lt_of_mem_digitNumbers {a : ℕ} (ha : a ∈ digitNumbers φ) :
    a < 8 ^ (φ.distinctVars.length + φ.length) := by
  classical
  rw [digitNumbers_eq_map] at ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  have hx' := mem_items.1 hx
  calc octal (itemDigits φ x)
      = ∑ p ∈ range (φ.distinctVars.length + φ.length),
          (if p ∈ itemCol φ x then 1 else 0) * 8 ^ p := by
        simp only [ite_mul, one_mul, zero_mul]
        rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.2 (itemCol_subset hx'),
          octal_itemDigits hx']
    _ < _ := Nat.sum_range_mul_pow_lt fun p _ => by split <;> lia

/-- The target has at most `φ.distinctVars.length + φ.length` base-8 digits. -/
theorem digitTarget_lt : digitTarget φ < 8 ^ (φ.distinctVars.length + φ.length) := by
  rw [digitTarget_eq]
  exact Nat.sum_range_mul_pow_lt fun p _ => by split <;> lia

/-- The count at a variable position. -/
private theorem card_filter_var {A B : Finset (ℕ × Bool)} {i : ℕ}
    (hi : i < φ.distinctVars.length) :
    #{x ∈ A.disjSum B | i ∈ itemCol φ x} = #{a ∈ A | a.1 = i} := by
  rw [card_filter_disjSum]
  simp_rw [mem_itemCol_inl_of_lt hi, mem_itemCol_inr]
  have hB : ({c ∈ B | i = φ.distinctVars.length + c.1} : Finset (ℕ × Bool)) = ∅ :=
    filter_false_of_mem fun c _ => by lia
  rw [hB, card_empty, Nat.add_zero]

/-- The count at a clause position. -/
private theorem card_filter_clause {A B : Finset (ℕ × Bool)}
    (hA : A ⊆ range φ.distinctVars.length ×ˢ univ) {j : ℕ} (hj : j < φ.length) :
    #{x ∈ A.disjSum B | φ.distinctVars.length + j ∈ itemCol φ x} =
      #{a ∈ A | covers φ a.1 a.2 j} + #{c ∈ B | c.1 = j} := by
  rw [card_filter_disjSum,
    filter_congr fun a ha => mem_itemCol_inl_clause (by simpa using (mem_product.1 (hA ha)).1) hj]
  simp_rw [mem_itemCol_inr, Nat.add_left_cancel_iff, eq_comm (a := j)]

private theorem forall_lt_add_iff {L k : ℕ} {P : ℕ → Prop} :
    (∀ p < L + k, P p) ↔ (∀ i < L, P i) ∧ ∀ j < k, P (L + j) := by
  refine ⟨fun h => ⟨fun i hi => h i (by lia), fun j hj => h _ (by lia)⟩, fun h p hp => ?_⟩
  rcases Nat.lt_or_ge p L with hpL | hpL
  · exact h.1 p hpL
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hpL
    exact h.2 j (by lia)

/-- The digit construction in terms of column counts: a solution chooses literal numbers `A` and
slack numbers `B` so that each variable position holds one chosen literal number and each clause
position three chosen numbers. -/
theorem digit_mem_SubsetSum_iff_counts (hφ : ∀ c ∈ φ, c.length ≤ 3) :
    (digitNumbers φ, digitTarget φ) ∈ SubsetSum ↔
      ∃ A ⊆ range φ.distinctVars.length ×ˢ (univ : Finset Bool),
        ∃ B ⊆ range φ.length ×ˢ (univ : Finset Bool),
          (∀ i < φ.distinctVars.length, #{a ∈ A | a.1 = i} = 1) ∧
            ∀ j < φ.length, #{a ∈ A | covers φ a.1 a.2 j} + #{c ∈ B | c.1 = j} = 3 := by
  classical
  have hT : ∀ p < φ.distinctVars.length + φ.length,
      (if p < φ.distinctVars.length then 1 else 3) < 8 := fun p _ => by split <;> lia
  have hU : ∀ p < φ.distinctVars.length + φ.length, #{x ∈ itemSet φ | p ∈ itemCol φ x} < 8 := by
    refine forall_lt_add_iff.2 ⟨fun i hi => ?_, fun j hj => ?_⟩
    · rw [itemSet, card_filter_var hi]
      exact (card_filter_fst_le _ _).trans_lt (by lia)
    · rw [itemSet, card_filter_clause subset_rfl hj]
      have h₁ := card_filter_covers_le (φ := φ)
        (range φ.distinctVars.length ×ˢ (univ : Finset Bool)) j
      rw [List.getD_eq_getElem _ _ hj] at h₁
      have h₂ := hφ _ (List.getElem_mem hj)
      have h₃ := card_filter_fst_le (range φ.length ×ˢ (univ : Finset Bool)) j
      lia
  have hcounts {A B : Finset (ℕ × Bool)} (hA : A ⊆ range φ.distinctVars.length ×ˢ univ) :
      (∀ p < φ.distinctVars.length + φ.length, #{x ∈ A.disjSum B | p ∈ itemCol φ x} =
        if p < φ.distinctVars.length then 1 else 3) ↔
      (∀ i < φ.distinctVars.length, #{a ∈ A | a.1 = i} = 1) ∧
        ∀ j < φ.length, #{a ∈ A | covers φ a.1 a.2 j} + #{c ∈ B | c.1 = j} = 3 := by
    rw [forall_lt_add_iff]
    refine and_congr (forall₂_congr fun i hi => ?_) (forall₂_congr fun j hj => ?_)
    · rw [card_filter_var hi, ite_eq_left hi]
    · rw [card_filter_clause hA hj, ite_eq_right (by lia)]
  have hset : (items φ).toFinset = itemSet φ := by ext x; simp [mem_items]
  rw [digitNumbers_eq_map, map_mem_SubsetSum_iff nodup_items, digitTarget_eq, hset]
  constructor
  · rintro ⟨F, hF, hsum⟩
    rw [sum_congr rfl fun x hx => octal_itemDigits (hF hx),
      sum_sum_pow_eq_iff hF (fun x hx => itemCol_subset hx) hU hT] at hsum
    obtain ⟨hA, hB⟩ := subset_disjSum.1 hF
    rw [← toLeft_disjSum_toRight (u := F), hcounts hA] at hsum
    exact ⟨_, hA, _, hB, hsum⟩
  · rintro ⟨A, hA, B, hB, hcount⟩
    have hF : A.disjSum B ⊆ itemSet φ := disjSum_mono hA hB
    refine ⟨A.disjSum B, hF, ?_⟩
    rw [sum_congr rfl fun x hx => octal_itemDigits (hF hx),
      sum_sum_pow_eq_iff hF (fun x hx => itemCol_subset hx) hU hT, hcounts hA]
    exact hcount

/-- Column counts as in `digit_mem_SubsetSum_iff_counts` exist exactly when the formula is
satisfiable: the chosen literal numbers are the true literals, and slack numbers fill each clause
position up to three. -/
theorem counts_iff_satisfiable (hφ : ∀ c ∈ φ, c.length ≤ 3) :
    (∃ A ⊆ range φ.distinctVars.length ×ˢ (univ : Finset Bool),
      ∃ B ⊆ range φ.length ×ˢ (univ : Finset Bool),
        (∀ i < φ.distinctVars.length, #{a ∈ A | a.1 = i} = 1) ∧
          ∀ j < φ.length, #{a ∈ A | covers φ a.1 a.2 j} + #{c ∈ B | c.1 = j} = 3) ↔
      φ.Satisfiable := by
  classical
  constructor
  · rintro ⟨A, hA, B, -, hvar, hclause⟩
    -- Each variable position holds the number of exactly one of its literals.
    have hnot : ∀ i, (i, false) ∈ A → (i, true) ∉ A := by
      intro i hf ht
      have hi : i < φ.distinctVars.length := mem_range.1 (mem_product.1 (hA ht)).1
      have h₂ : 2 ≤ #{a ∈ A | a.1 = i} := by
        calc 2 = #({(i, true), (i, false)} : Finset (ℕ × Bool)) := by simp
          _ ≤ _ := card_le_card fun a ha => by
            simp only [mem_insert, mem_singleton] at ha
            rcases ha with rfl | rfl <;> simpa
      have := hvar i hi
      lia
    refine ⟨fun v => decide ((φ.distinctVars.idxOf v, true) ∈ A),
      (CNF.eval_eq_true_iff _ _).2 fun c hc => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    -- Some literal number of the clause is chosen, since slack numbers fill at most two.
    have hpos : 0 < #{a ∈ A | covers φ a.1 a.2 j} := by
      have := hclause j hj
      have := card_filter_fst_le B j
      lia
    obtain ⟨⟨i, b⟩, ha⟩ := card_pos.1 hpos
    obtain ⟨haA, hcov⟩ := mem_filter.1 ha
    obtain ⟨l, hl, hi, hb⟩ := covers_eq_true_iff.1 hcov
    rw [List.getD_eq_getElem _ _ hj] at hl
    refine (Clause.eval_eq_true_iff _ _).2 ⟨l, hl, ?_⟩
    simp only at hi hb
    rw [hi, hb]
    cases b
    · exact decide_eq_false (hnot i haA)
    · exact decide_eq_true haA
  · rintro ⟨σ, hσ⟩
    -- Choose the true literal of each variable, then fill each clause position with slack.
    set b : ℕ → Bool := fun i => σ (φ.distinctVars.getD i 0) with hb
    set A : Finset (ℕ × Bool) := (range φ.distinctVars.length).image fun i => (i, b i) with hA
    have hmemA : ∀ a, a ∈ A ↔ a.1 < φ.distinctVars.length ∧ a.2 = b a.1 := by
      rintro ⟨i, c⟩
      simp only [hA, mem_image, mem_range, Prod.mk.injEq]
      constructor
      · rintro ⟨i, hi, rfl, rfl⟩
        exact ⟨hi, rfl⟩
      · rintro ⟨hi, rfl⟩
        exact ⟨i, hi, rfl, rfl⟩
    set cnt : ℕ → ℕ := fun j => #{a ∈ A | covers φ a.1 a.2 j} with hcnt
    set B : Finset (ℕ × Bool) := (range φ.length ×ˢ univ).filter
      (fun c => cnt c.1 + (!c.2).toNat ≤ 2) with hB
    refine ⟨A, fun a ha => ?_, B, filter_subset _ _, fun i hi => ?_, fun j hj => ?_⟩
    · exact mem_product.2 ⟨mem_range.2 ((hmemA a).1 ha).1, mem_univ _⟩
    · refine card_eq_one.2 ⟨(i, b i), ?_⟩
      ext ⟨i', c⟩
      simp only [mem_filter, hmemA, mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨-, rfl⟩, rfl⟩
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨⟨hi, rfl⟩, rfl⟩
    · have hle : cnt j ≤ 3 := (card_filter_covers_le A j).trans
        (by rw [List.getD_eq_getElem _ _ hj]; exact hφ _ (List.getElem_mem hj))
      have hpos : 1 ≤ cnt j := by
        obtain ⟨l, hl, hσl⟩ := (Clause.eval_eq_true_iff _ _).1
          ((CNF.eval_eq_true_iff _ _).1 hσ _ (List.getElem_mem hj))
        have hl' : l ∈ φ.getD j [] := by rwa [List.getD_eq_getElem _ _ hj]
        have hidx : φ.distinctVars.idxOf l.1 < φ.distinctVars.length :=
          List.idxOf_lt_length_iff.2 (mem_distinctVars_of_mem hl')
        refine card_pos.2 ⟨(φ.distinctVars.idxOf l.1, l.2), mem_filter.2 ⟨(hmemA _).2
          ⟨hidx, ?_⟩, covers_eq_true_iff.2 ⟨l, hl', rfl, rfl⟩⟩⟩
        simp only [hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx,
          List.getElem_idxOf hidx, Option.getD_some, hσl]
      have hBj : ({c ∈ B | c.1 = j} : Finset (ℕ × Bool)) =
          ({c ∈ (univ : Finset Bool) | cnt j + (!c).toNat ≤ 2}).image (Prod.mk j) := by
        ext ⟨j', c⟩
        simp only [hB, mem_filter, mem_product, mem_range, mem_univ, and_true, mem_image,
          true_and, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨-, h⟩, rfl⟩
          exact ⟨c, h, rfl, rfl⟩
        · rintro ⟨c, h, rfl, rfl⟩
          exact ⟨⟨hj, h⟩, rfl⟩
      change cnt j + _ = 3
      rw [hBj, card_image_of_injective _ (Prod.mk_right_injective j),
        card_filter _ (univ : Finset Bool), Fintype.sum_bool]
      simp only [Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.toNat_true]
      split_ifs <;> lia

/-- **Correctness of Sipser's reduction.** A formula belongs to `ThreeSAT` exactly when its
digit construction has a sub-multiset summing to the target. -/
theorem toSubsetSum_mem_iff (φ : CNF ℕ) : toSubsetSum φ ∈ SubsetSum ↔ φ ∈ ThreeSAT := by
  unfold toSubsetSum
  split_ifs with h
  · have hφ : ∀ c ∈ φ, c.length ≤ 3 := by simpa using h
    rw [digit_mem_SubsetSum_iff_counts hφ, counts_iff_satisfiable hφ]
    exact ⟨fun hs => ⟨hφ, hs⟩, fun h => h.2⟩
  · refine iff_of_false ?_ fun h' => h (by simpa using h'.1)
    rintro ⟨s, hs, hsum⟩
    rw [Multiset.coe_nil, Multiset.le_zero] at hs
    simp [hs] at hsum

end Correctness

/-! ### Polynomial time -/

/-- `8 ^ p` in binary, from `p` in unary. -/
@[local fun_prop]
private theorem eight_pow : ComputableInPolyTime (fun p : ℕ => 8 ^ p) encUnary encNat := by
  have h : (fun p : ℕ => 8 ^ p) = fun p => 2 ^ (3 * p) := funext fun p => by rw [pow_mul]; rfl
  rw [h]
  fun_prop

/-- Testing whether a clause contains a literal is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_covers :
    ComputableInPolyTime
      (fun p : ((CNF ℕ × ℕ) × Bool) × ℕ => covers p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encCNF encUnary) encBool) encUnary) encBool := by
  unfold covers encCNF
  apply anyWithInput (encA := encPair encNat encBool)
  · exact (listGetD (encA := encList (encPair encNat encBool)) []).comp
      (show ComputableInPolyTime (fun x : ((CNF ℕ × ℕ) × Bool) × ℕ => (x.1.1.1, x.2)) _
        (encPair (encList (encList (encPair encNat encBool))) encUnary) by fun_prop)
  · fun_prop

/-- Listing the digit positions of a literal number is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_literalDigits :
    ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × Bool => literalDigits p.1.1 p.1.2 p.2)
      (encPair (encPair encCNF encUnary) encBool) (encList encUnary) := by
  unfold literalDigits
  fun_prop

/-- Composition rule for `literalDigits`. -/
@[fun_prop]
theorem computableInPolyTime_literalDigits' {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {i : α → ℕ} {b : α → Bool}
    (hφ : ComputableInPolyTime φ input encCNF)
    (hi : ComputableInPolyTime i input encUnary)
    (hb : ComputableInPolyTime b input encBool) :
    ComputableInPolyTime (fun a => literalDigits (φ a) (i a) (b a)) input
      (encList encUnary) :=
  computableInPolyTime_literalDigits.comp ((hφ.prod hi).prod hb)

/-- A number with digits zero and one is computed in binary from its unary digit positions. -/
@[fun_prop]
theorem computableInPolyTime_octal :
    ComputableInPolyTime octal (encList encUnary) encNat := by
  unfold octal
  fun_prop

/-- The numbers of the digit construction are computed in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_digitNumbers :
    ComputableInPolyTime digitNumbers encCNF (encList encNat) := by
  unfold digitNumbers
  apply listAppend'
  · apply flatMapWithInput (by fun_prop)
    fun_prop
  · apply flatMapWithInput (by fun_prop)
    fun_prop

/-- The target of the digit construction is computed in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_digitTarget :
    ComputableInPolyTime digitTarget encCNF encNat := by
  unfold digitTarget
  fun_prop

/-- Sipser's reduction is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toSubsetSum :
    ComputableInPolyTime toSubsetSum encCNF (encPair (encList encNat) encNat) := by
  unfold toSubsetSum encCNF
  fun_prop

end ThreeSAT

/-- `ThreeSAT` reduces to `SubsetSum` in polynomial time by Sipser's digit construction. -/
theorem polyTimeReducible_ThreeSAT_SubsetSum :
    PolyTimeReducible encCNF (encPair (encList encNat) encNat) ThreeSAT SubsetSum :=
  ⟨ThreeSAT.toSubsetSum, ThreeSAT.computableInPolyTime_toSubsetSum,
    fun φ => (ThreeSAT.toSubsetSum_mem_iff φ).symm⟩

/-- `SubsetSum` is `NP`-hard. -/
theorem SubsetSum_npHard : NPHard (encPair (encList encNat) encNat) SubsetSum :=
  ThreeSAT_npHard.trans polyTimeReducible_ThreeSAT_SubsetSum

/-- **Subset sum is NP-complete**, with the numbers and the target in binary [Karp1972],
[Sipser, Theorem 7.56][Sipser2013]. -/
theorem SubsetSum_npComplete : NPComplete (encPair (encList encNat) encNat) SubsetSum :=
  ⟨SubsetSum.mem_NP, SubsetSum_npHard⟩

end Cslib.Complexity
