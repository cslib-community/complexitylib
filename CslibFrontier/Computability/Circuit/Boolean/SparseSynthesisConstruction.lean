/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Complexity
import CslibFrontier.Computability.Circuit.Boolean.Synthesis
import CslibFrontier.Computability.Circuit.Complexity
import CslibFrontier.Foundations.Combinatorics.FiniteCover
import CslibFrontier.Probability.BitString.LinearHash.Collisions
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.BitString.Parity
import Cslib.Computability.Circuit.Boolean.Synthesis
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset

/-!
# Sparse and partial synthesis: the constructions

This file builds De Morgan circuits, with explicit gate budgets, for two kinds of Boolean functions
that carry little information: the indicator of a small set of inputs
(`complexity_indicator_le_indicatorBound`), and a function that only has to be correct on a small
set of inputs (`complexityOn_le_partialBound`). The file
`CslibFrontier.Computability.Circuit.Boolean.SparseSynthesis` chooses the parameters and shows that,
for sets of `2 ^ p` of the `2 ^ (2 p)` inputs, the budgets are `(1 + o(1)) 2 ^ p` and
`(1 + o(1)) 2 ^ p / p`. No asymptotics happen here. The constructions follow Chashkin's account
[Chashkin, Sections 2 and 3][Chashkin2024] of the methods of Lupanov [Lupanov1965], Nechiporuk
[Nechiporuk1965], Sholomov [Sholomov1969] and Andreev [Andreev1989].

## Tables

Split `k + l` input bits into `k` column bits and `l` row bits, and view a truth table as a
matrix with `2 ^ l` rows and `2 ^ k` columns. Every column minterm and every row minterm is built
once. Each row is a disjunction of *patterns*, sets of columns that are built once from the
column minterms and shared by all rows, so beyond a fixed overhead a table costs one gate per
pattern chosen in a row.

* A *sparse table* computes the indicator of a set `D`: the true entries of each row are cut into
  chunks of `K`, and every set of at most `K` columns is a pattern. About `|D| / K` patterns are
  chosen.
* A *partial table* computes a function given on a set `D`: the given entries of each row are cut
  into chunks of `J` consecutive entries. On a chunk, the function agrees with some assignment to
  all columns from a bank of `(2 · 2 ^ k + 1) 2 ^ J` assignments, chosen by a covering bound,
  which extends every assignment to at most `J` columns [Chashkin, Lemma 2.1][Chashkin2024].
  Masked to the
  interval of columns spanned by the chunk, that assignment is a pattern and does not interfere
  with the other chunks [Chashkin, Lemma 2.2][Chashkin2024]. About `|D| / J` patterns are
  chosen.

## Hashing

A table only has few patterns when it has few columns, so the inputs are first hashed to `k + l`
bits by a linear map over the field with two elements. Two distinct inputs collide under a
`2 ^ -(k + l)` fraction of the linear maps, so some linear map makes at most that fraction of any
given pairs of distinct inputs collide [Chashkin, Lemmas 2.3 and 2.4][Chashkin2024].

* For a function given on `D`, tabulate it on the image of `D` under one hash, and correct, by
  explicit minterms, the few inputs of `D` whose hash collides with that of another input of `D`.
* For the indicator of a set `B` with `|B| ≤ 2 ^ p`, a hash to `k + l = p + a` bits followed by a
  sparse table for the image of `B` is a *filter*: true on `B`, and on at most a `2 ^ -a` fraction
  of the other inputs. The conjunction of `t` filters wrongly accepts at most `2 ^ n / 2 ^ (a t)`
  inputs, which are removed by explicit minterms [Chashkin, Lemma 3.3][Chashkin2024].

The collision bound uses the shared `BitString.LinearHash` API; the circuit implementation
uses finite-set parity masks to retain its exact gate bound.

## Main definitions

* `Cslib.Circuits.Boolean.SparseSynthesis.sparseTableBound`,
  `Cslib.Circuits.Boolean.SparseSynthesis.partialTableBound`: the budgets of the tables.
* `Cslib.Circuits.Boolean.SparseSynthesis.indicatorBound`: the budget for sparse indicators.
* `Cslib.Circuits.Boolean.SparseSynthesis.partialBound`: the budget for partial functions.

## Main results

* `Cslib.Circuits.Boolean.SparseSynthesis.complexity_indicator_le_indicatorBound`: the indicator
  of a set of at most `2 ^ p` inputs costs at most `indicatorBound n k l K p a t` gates.
* `Cslib.Circuits.Boolean.SparseSynthesis.complexityOn_le_partialBound`: a function on a set `D`
  of inputs costs at most `partialBound n k l J |D|` gates on `D`.

## References

* [A. V. Chashkin, *On computing partial Boolean functions*][Chashkin2024]
* [O. B. Lupanov, *On an approach to the synthesis of control systems: the principle of local
  coding*][Lupanov1965]
* [E. I. Nechiporuk, *On the complexity of gating circuits realizing Boolean matrices with
  undefined elements*][Nechiporuk1965]
* [L. A. Sholomov, *On the realization of incompletely defined Boolean functions by circuits of
  functional elements*][Sholomov1969]
* [A. E. Andreev, *On the complexity of the realization of partial Boolean functions by circuits
  of functional elements*][Andreev1989]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.SparseSynthesis

open Finset

/-! ### Tables with shared column patterns -/

section Table

variable {k l : ℕ}

/-- The column of an input of a table: the number of its first `k` bits. -/
private def column (x : BitString (k + l)) : Fin (2 ^ k) :=
  BitString.equivFin k fun i => x (Fin.castAdd l i)

/-- The row of an input of a table: its last `l` bits. -/
private def row (x : BitString (k + l)) : BitString l :=
  fun i => x (Fin.natAdd k i)

/-- The input in row `r` and column `c` of a table. -/
private def entry (r : BitString l) (c : Fin (2 ^ k)) : BitString (k + l) :=
  Fin.append ((BitString.equivFin k).symm c) r

@[simp] private theorem entry_row_column (x : BitString (k + l)) :
    entry (row x) (column x) = x := by
  simp only [entry, column, Equiv.symm_apply_apply]
  exact Fin.append_castAdd_natAdd

@[simp] private theorem row_entry (r : BitString l) (c : Fin (2 ^ k)) : row (entry r c) = r := by
  funext i
  simp [row, entry]

@[simp] private theorem column_entry (r : BitString l) (c : Fin (2 ^ k)) :
    column (entry r c) = c := by
  simp [column, entry]

/-- The columns of row `r` whose entries lie in `D`. -/
private def rowSupport (D : Finset (BitString (k + l))) (r : BitString l) : Finset (Fin (2 ^ k)) :=
  {c | entry r c ∈ D}

private theorem mem_rowSupport {D : Finset (BitString (k + l))} {x : BitString (k + l)} :
    column x ∈ rowSupport D (row x) ↔ x ∈ D := by
  simp [rowSupport]

/-- The rows of a table split its entries. -/
private theorem sum_card_rowSupport (D : Finset (BitString (k + l))) :
    ∑ r, #(rowSupport D r) = #D := by
  let e : BitString l × Fin (2 ^ k) ≃ BitString (k + l) :=
    ⟨fun rc => entry rc.1 rc.2, fun x => (row x, column x), fun rc => by simp,
      fun x => by simp⟩
  calc ∑ r, #(rowSupport D r)
      = ∑ rc : BitString l × Fin (2 ^ k), if e rc ∈ D then 1 else 0 := by
        simp only [rowSupport, card_filter, Fintype.sum_prod_type]
        rfl
    _ = ∑ x : BitString (k + l), if x ∈ D then 1 else 0 :=
        Fintype.sum_equiv e _ _ fun _ => rfl
    _ = #D := by simp

/-- The function of a table whose rows are disjunctions of column patterns: true at `x` when the
column of `x` lies in one of the patterns chosen for the row of `x`. -/
private def table {B : Type*} (pattern : B → Finset (Fin (2 ^ k)))
    (chosen : BitString l → Finset B) : BooleanFunction (k + l) :=
  fun x => decide (∃ b ∈ chosen (row x), column x ∈ pattern b)

/-- A table costs `2 (k + l) + 1` gates for the minterm of every column and every row, `w + 1`
gates for each of the patterns, of at most `w` columns each, which are built once and shared by
the rows, one gate per pattern chosen in a row, three gates per row, and a constant. -/
private theorem synthesis_table {B : Type*} [Fintype B] (pattern : B → Finset (Fin (2 ^ k)))
    {w : ℕ} (hw : ∀ b, #(pattern b) ≤ w) (chosen : BitString l → Finset B) :
    Synthesis interpretation (inputs (k + l)) {table pattern chosen}
      ((2 ^ k + 2 ^ l) * (2 * (k + l) + 1) + Fintype.card B * (w + 1) +
        ∑ r, #(chosen r) + 3 * 2 ^ l + 1) := by
  let test : Fin (2 ^ k) ⊕ BitString l → BooleanFunction (k + l)
    | .inl c => fun x => decide (column x = c)
    | .inr r => fun x => decide (row x = r)
  have htest : Synthesis interpretation (inputs (k + l)) (Set.range test)
      ((2 ^ k + 2 ^ l) * (2 * (k + l) + 1)) := by
    have h (t : Fin (2 ^ k) ⊕ BitString l) :
        Synthesis interpretation (inputs (k + l)) {test t} (2 * (k + l) + 1) := by
      cases t with
      | inl c =>
        have heq : test (.inl c) =
            fun x => decide ((fun i => x (Fin.castAdd l i)) = (BitString.equivFin k).symm c) := by
          funext x
          exact Bool.eq_iff_iff.mpr (by
            rw [decide_eq_true_iff, decide_eq_true_iff, Equiv.eq_symm_apply]; rfl)
        rw [heq]
        exact (synthesis_minterm _ _).mono Set.Subset.rfl Set.Subset.rfl (by omega)
      | inr r => exact (synthesis_minterm _ r).mono Set.Subset.rfl Set.Subset.rfl (by omega)
    simpa using Synthesis.family test _ h
  let bank (b : B) : BooleanFunction (k + l) := fun x => decide (column x ∈ pattern b)
  have hbank : Synthesis interpretation (Set.range test) (Set.range bank)
      (Fintype.card B * (w + 1)) := by
    have h (b : B) : Synthesis interpretation (Set.range test) {bank b} (w + 1) := by
      have h := Synthesis.exists_mem (pattern b) (fun c => test (.inl c)) (fun _ => 0)
        fun c _ => Synthesis.of_mem (s := Set.range test) ⟨.inl c, rfl⟩
      refine h.mono Set.Subset.rfl (by simp [bank, test]) ?_
      simpa using hw b
    simpa using Synthesis.family bank _ h
  let rowValue (r : BitString l) : BooleanFunction (k + l) :=
    fun x => test (.inr r) x && decide (∃ b ∈ chosen r, bank b x = true)
  have hrow (r : BitString l) : Synthesis interpretation (Set.range test ∪ Set.range bank)
      {rowValue r} (#(chosen r) + 2) := by
    have h := Synthesis.exists_mem (chosen r) bank (fun _ => 0)
      fun b _ => Synthesis.of_mem (s := Set.range test ∪ Set.range bank) (Or.inr ⟨b, rfl⟩)
    simpa [rowValue] using
      (Synthesis.of_mem (s := Set.range test ∪ Set.range bank) (Or.inl ⟨.inr r, rfl⟩)).and h
  have hrows := Synthesis.exists_mem univ rowValue _ fun r _ => hrow r
  have hall := htest.comp (hbank.mono Set.subset_union_right Set.Subset.rfl le_rfl)
  refine (hall.trans (hrows.mono Set.subset_union_right
    (Set.singleton_subset_singleton.mpr (funext fun x => by simp [rowValue, test, bank, table]))
    le_rfl)).mono Set.Subset.rfl Set.Subset.rfl (le_of_eq ?_)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, smul_eq_mul]
  ring

/-- A sum of quotients is at most the quotient of the sum. -/
private theorem sum_div_le_div_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ) (K : ℕ) :
    ∑ i ∈ s, f i / K ≤ (∑ i ∈ s, f i) / K := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · exact (Nat.le_div_iff_mul_le hK).mpr
      (sum_mul s _ K ▸ sum_le_sum fun i _ => Nat.div_mul_le_self _ _)

end Table

/-! ### Blocks of consecutive elements -/

section Blocks

variable {N : ℕ}

/-- The elements named by a tuple of optional elements. -/
private def tupleSupport {K : ℕ} (v : Fin K → Option (Fin N)) : Finset (Fin N) :=
  univ.biUnion fun i => (v i).toFinset

private theorem card_tupleSupport_le {K : ℕ} (v : Fin K → Option (Fin N)) :
    #(tupleSupport v) ≤ K :=
  calc #(tupleSupport v) ≤ ∑ i, #(v i).toFinset := card_biUnion_le
    _ ≤ ∑ _i : Fin K, 1 := sum_le_sum fun i _ => by cases v i <;> simp
    _ = K := by simp

/-- Block `b` of `C` in increasing order: the elements of ranks `b K, …, b K + K - 1`, padded
with `none` past the end of `C`. -/
private def block (C : Finset (Fin N)) (K b : ℕ) : Fin K → Option (Fin N) :=
  fun i => if h : b * K + i < #C then some (C.orderEmbOfFin rfl ⟨b * K + i, h⟩) else none

/-- The first `#C / K + 1` blocks of `C` cover `C`, and nothing else. -/
private theorem exists_mem_tupleSupport_block_iff (C : Finset (Fin N)) {K : ℕ} (hK : 0 < K)
    (c : Fin N) : (∃ b ∈ range (#C / K + 1), c ∈ tupleSupport (block C K b)) ↔ c ∈ C := by
  simp only [tupleSupport, mem_biUnion, mem_univ, true_and, Option.mem_toFinset,
    Option.mem_def, block]
  constructor
  · rintro ⟨b, -, i, hi⟩
    split_ifs at hi with h
    exact Option.some.inj hi ▸ C.orderEmbOfFin_mem rfl _
  · intro hc
    obtain ⟨ρ, rfl⟩ : c ∈ Set.range (C.orderEmbOfFin rfl) := by
      rwa [range_orderEmbOfFin]
    have hρ : ρ.val / K * K + ρ.val % K = ρ.val := Nat.div_add_mod' _ _
    refine ⟨ρ.val / K, mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right ρ.isLt.le)),
      ⟨ρ.val % K, Nat.mod_lt _ hK⟩, ?_⟩
    simp only [hρ, ρ.isLt, dite_true]

/-- The position of the element of rank `i` of `C`, or the end `N` if `C` has fewer elements. -/
private def cut (C : Finset (Fin N)) (i : ℕ) : Fin (N + 1) :=
  if h : i < #C then (C.orderEmbOfFin rfl ⟨i, h⟩).castSucc else Fin.last N

private theorem cut_le_iff (C : Finset (Fin N)) (i : ℕ) (ρ : Fin #C) :
    cut C i ≤ (C.orderEmbOfFin rfl ρ).castSucc ↔ i ≤ ρ := by
  unfold cut
  split_ifs with h
  · rw [Fin.castSucc_le_castSucc_iff, OrderEmbedding.le_iff_le, Fin.le_def]
  · rw [Fin.last_le_iff]
    exact iff_of_false (Fin.castSucc_lt_last _).ne
      (not_le.mpr (ρ.isLt.trans_le (not_lt.mp h)))

/-- The elements of `C` whose ranks lie between `b J` and `b J + J - 1`. -/
private def rankBlock (C : Finset (Fin N)) (J b : ℕ) : Finset (Fin N) :=
  ({ρ : Fin #C | b * J ≤ ρ ∧ ρ < (b + 1) * J} : Finset (Fin #C)).map
    (C.orderEmbOfFin rfl).toEmbedding

private theorem card_rankBlock_le (C : Finset (Fin N)) (J b : ℕ) : #(rankBlock C J b) ≤ J := by
  rw [rankBlock, card_map]
  calc #({ρ : Fin #C | b * J ≤ ρ ∧ ρ < (b + 1) * J} : Finset (Fin #C))
      ≤ #(Ico (b * J) ((b + 1) * J)) :=
        card_le_card_of_injOn Fin.val (fun ρ hρ => by simpa using (mem_filter.mp hρ).2)
          Fin.val_injective.injOn
    _ = J := by simp [Nat.add_mul]

end Blocks

/-! ### Sparse tables -/

/-- The gate budget of a sparse table on `k + l` inputs with `w` true entries and chunks of `K`
columns: the shared minterms of the `2 ^ k` columns and the `2 ^ l` rows, every one of the
`(2 ^ k + 1) ^ K` patterns of at most `K` columns, one gate per chunk, about `w / K` of them, and
four gates per row. -/
def sparseTableBound (k l K w : ℕ) : ℕ :=
  (2 ^ k + 2 ^ l) * (2 * (k + l) + 1) + (2 ^ k + 1) ^ K * (K + 1) + w / K + 4 * 2 ^ l + 1

private theorem sparseTableBound_mono {k l K w w' : ℕ} (h : w ≤ w') :
    sparseTableBound k l K w ≤ sparseTableBound k l K w' := by
  have := Nat.div_le_div_right (c := K) h
  unfold sparseTableBound
  omega

/-- **Sparse tables.** Split each row of the truth table of the indicator of `D` into chunks of
`K` true entries; each chunk is one of the shared patterns of at most `K` columns. -/
private theorem complexity_indicator_le_sparseTableBound {k l : ℕ} (D : Finset (BitString (k + l)))
    {K : ℕ} (hK : 0 < K) :
    complexity interpretation (single fun x => decide (x ∈ D)) ≤
      sparseTableBound k l K #D := by
  let chosen (r : BitString l) : Finset (Fin K → Option (Fin (2 ^ k))) :=
    (range (#(rowSupport D r) / K + 1)).image (block (rowSupport D r) K)
  have h := synthesis_table tupleSupport card_tupleSupport_le chosen
  have heq : table tupleSupport chosen = fun x => decide (x ∈ D) := by
    funext x
    have := exists_mem_tupleSupport_block_iff (rowSupport D (row x)) hK (column x)
    simp only [table, chosen, exists_mem_image, this, mem_rowSupport]
  rw [heq] at h
  refine h.complexity_le.trans ?_
  have hsum : ∑ r, #(chosen r) ≤ #D / K + 2 ^ l := by
    calc ∑ r, #(chosen r) ≤ ∑ r, (#(rowSupport D r) / K + 1) :=
          sum_le_sum fun r _ => card_image_le.trans (card_range _).le
      _ ≤ #D / K + 2 ^ l := by
          rw [sum_add_distrib, ← sum_card_rowSupport D]
          simpa using sum_div_le_div_sum univ (fun r => #(rowSupport D r)) K
  simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, sparseTableBound]
  omega

/-! ### Banks of extensions -/

section Cover

variable {α β : Type*} [Fintype α] [Nonempty α] (cover : α → β → Prop)
  [∀ x b, Decidable (cover x b)] {a : ℕ}

/-- If each of at most `4 ^ L` targets is covered by at least a `1 / a` fraction of the
candidates, then `(2 L + 1) a` candidates cover every target. -/
private theorem exists_cover (ha : 0 < a) {L : ℕ} (s : Finset β) (hsL : #s ≤ 4 ^ L)
    (hs : ∀ b ∈ s, Fintype.card α ≤ a * #{x | cover x b}) :
    ∃ chosen : Finset α, #chosen ≤ (2 * L + 1) * a ∧ ∀ b ∈ s, ∃ x ∈ chosen, cover x b := by
  classical
  obtain ⟨tests, htests⟩ := Cslib.exists_cover_of_density
    (S := α) (W := s) (fun x b => cover x b) a (2 * L) ha
    (by simpa only [Fintype.card_coe, pow_mul, Nat.reducePow] using hsL)
    (fun b => by simpa only [Fintype.card_subtype] using hs b b.property)
  refine ⟨univ.image tests, ?_, ?_⟩
  · simpa only [card_univ, Fintype.card_fin, Nat.mul_comm] using
      (card_image_le (s := univ) (f := tests))
  · intro b hb
    obtain ⟨i, hi⟩ := htests ⟨b, hb⟩
    exact ⟨tests i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, hi⟩

end Cover

/-- Every assignment to at most `J` of `N` positions has at least a `2 ^ -J` fraction of the
assignments to all positions as extensions. -/
private theorem two_pow_le_mul_card_extensions {N J : ℕ} {C : Finset (Fin N)} (hC : #C ≤ J)
    (v : Fin N → Bool) : 2 ^ N ≤ 2 ^ J * #{e : Fin N → Bool | ∀ i ∈ C, e i = v i} := by
  have heq : ({e : Fin N → Bool | ∀ i ∈ C, e i = v i} : Finset (Fin N → Bool)) =
      Fintype.piFinset fun i => if i ∈ C then {v i} else univ := by
    ext e
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    exact forall_congr' fun i => by split_ifs with h <;> simp [h]
  have hcard : #{e : Fin N → Bool | ∀ i ∈ C, e i = v i} = 2 ^ #Cᶜ := by
    rw [heq, Fintype.card_piFinset]
    simp [apply_ite card, prod_ite, filter_not, compl_eq_univ_sdiff]
  rw [hcard, card_compl, Fintype.card_fin, ← pow_add]
  have := (card_le_univ C).trans_eq (Fintype.card_fin N)
  exact Nat.pow_le_pow_right two_pos (by omega)

/-- **Extension banks.** At most `(2 N + 1) 2 ^ J` assignments to `N` positions include an
extension of every assignment to at most `J` of the positions. -/
private theorem exists_extension_bank (N J : ℕ) :
    ∃ bank : Finset (Fin N → Bool), #bank ≤ (2 * N + 1) * 2 ^ J ∧
      ∀ C : Finset (Fin N), #C ≤ J → ∀ v : Fin N → Bool, ∃ e ∈ bank, ∀ i ∈ C, e i = v i := by
  let targets : Finset (Finset (Fin N) × (Fin N → Bool)) := {t | #t.1 ≤ J}
  have htargets : #targets ≤ 4 ^ N := by
    calc #targets ≤ Fintype.card (Finset (Fin N) × (Fin N → Bool)) := card_le_univ _
      _ = 4 ^ N := by simp [← mul_pow]
  obtain ⟨bank, hcard, hbank⟩ := exists_cover
    (fun (e : Fin N → Bool) (t : Finset (Fin N) × (Fin N → Bool)) => ∀ i ∈ t.1, e i = t.2 i)
    (Nat.two_pow_pos J) targets htargets fun t ht => by
      simpa using two_pow_le_mul_card_extensions (mem_filter.mp ht).2 t.2
  exact ⟨bank, hcard, fun C hC v => hbank (C, v) (mem_filter.mpr ⟨mem_univ _, hC⟩)⟩

/-! ### Partial tables -/

/-- The gate budget of a partial table on `k + l` inputs with `w` specified entries and chunks of
`J` specified entries: the shared minterms of the columns and the rows, the at most
`(2 ^ k + 1) ^ 2 (2 · 2 ^ k + 1) 2 ^ J` patterns given by an interval of columns and an assignment
from a bank of extensions, each of at most `2 ^ k` columns, one gate per chunk, about `w / J` of
them, and four gates per row. -/
def partialTableBound (k l J w : ℕ) : ℕ :=
  (2 ^ k + 2 ^ l) * (2 * (k + l) + 1) + (2 ^ k + 1) ^ 3 * (2 * 2 ^ k + 1) * 2 ^ J + w / J +
    4 * 2 ^ l + 1

private theorem partialTableBound_mono {k l J w w' : ℕ} (h : w ≤ w') :
    partialTableBound k l J w ≤ partialTableBound k l J w' := by
  have := Nat.div_le_div_right (c := J) h
  unfold partialTableBound
  omega

/-- **Partial tables.** Split the specified entries of each row into chunks of `J` consecutive
entries. On each chunk, the function agrees with some assignment from a bank of extensions of all
assignments to at most `J` columns; masking that assignment to the interval of columns spanned by
the chunk keeps it from interfering with the other chunks. -/
private theorem exists_eqOn_complexity_le_partialTableBound {k l : ℕ}
    (D : Finset (BitString (k + l))) (u : BooleanFunction (k + l)) {J : ℕ} (hJ : 0 < J) :
    ∃ φ : BooleanFunction (k + l), Set.EqOn φ u D ∧
      complexity interpretation (single φ) ≤ partialTableBound k l J #D := by
  obtain ⟨bank, hbank_card, hbank⟩ := exists_extension_bank (2 ^ k) J
  let pattern (β : Fin (2 ^ k + 1) × Fin (2 ^ k + 1) × bank) : Finset (Fin (2 ^ k)) :=
    {c | β.1 ≤ c.castSucc ∧ c.castSucc < β.2.1 ∧ β.2.2.1 c = true}
  have hext (r : BitString l) (b : ℕ) :
      ∃ e ∈ bank, ∀ c ∈ rankBlock (rowSupport D r) J b, e c = u (entry r c) :=
    hbank _ (card_rankBlock_le _ _ _) _
  choose ext hext_mem hext_eq using hext
  let chosen (r : BitString l) : Finset (Fin (2 ^ k + 1) × Fin (2 ^ k + 1) × bank) :=
    (range (#(rowSupport D r) / J + 1)).image fun b =>
      (cut (rowSupport D r) (b * J), cut (rowSupport D r) ((b + 1) * J), ⟨ext r b, hext_mem r b⟩)
  refine ⟨table pattern chosen, fun x hx => ?_, ?_⟩
  · obtain ⟨ρ, hρ⟩ : column x ∈ Set.range ((rowSupport D (row x)).orderEmbOfFin rfl) := by
      rw [range_orderEmbOfFin]
      exact mem_rowSupport.mpr hx
    have hblock (b : ℕ) : (cut (rowSupport D (row x)) (b * J) ≤ (column x).castSucc ∧
        (column x).castSucc < cut (rowSupport D (row x)) ((b + 1) * J)) ↔
          b * J ≤ ρ ∧ ρ < (b + 1) * J := by
      rw [← hρ, cut_le_iff, ← not_le, cut_le_iff, not_le]
    have hvalue (b : ℕ) (hb : b * J ≤ ρ ∧ ρ < (b + 1) * J) :
        ext (row x) b (column x) = u x := by
      have hmem : column x ∈ rankBlock (rowSupport D (row x)) J b := by
        rw [← hρ]
        exact mem_map_of_mem _ (mem_filter.mpr ⟨mem_univ _, hb⟩)
      rw [hext_eq _ _ _ hmem, entry_row_column]
    apply Bool.eq_iff_iff.mpr
    simp only [table, chosen, decide_eq_true_eq, exists_mem_image, pattern, mem_filter,
      mem_univ, true_and, mem_range]
    constructor
    · rintro ⟨b, -, h₁, h₂, h₃⟩
      rwa [← hvalue b ((hblock b).mp ⟨h₁, h₂⟩)]
    · intro hu
      have hb : ρ.val / J * J ≤ ρ ∧ ρ < (ρ.val / J + 1) * J :=
        ⟨Nat.div_mul_le_self _ _, by rw [Nat.add_mul, one_mul]; exact Nat.lt_div_mul_add hJ⟩
      refine ⟨ρ.val / J, Nat.lt_succ_of_le (Nat.div_le_div_right ρ.isLt.le),
        (hblock _).mpr hb |>.1, (hblock _).mpr hb |>.2, ?_⟩
      rwa [hvalue _ hb]
  · refine (synthesis_table pattern (w := 2 ^ k)
      (fun β => (card_le_univ _).trans (by simp)) chosen).complexity_le.trans ?_
    have hsum : ∑ r, #(chosen r) ≤ #D / J + 2 ^ l := by
      calc ∑ r, #(chosen r) ≤ ∑ r, (#(rowSupport D r) / J + 1) :=
            sum_le_sum fun r _ => card_image_le.trans (card_range _).le
        _ ≤ #D / J + 2 ^ l := by
            rw [sum_add_distrib, ← sum_card_rowSupport D]
            simpa using sum_div_le_div_sum univ (fun r => #(rowSupport D r)) J
    have hcard : Fintype.card (Fin (2 ^ k + 1) × Fin (2 ^ k + 1) × bank) * (2 ^ k + 1) ≤
        (2 ^ k + 1) ^ 3 * (2 * 2 ^ k + 1) * 2 ^ J := by
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
      calc (2 ^ k + 1) * ((2 ^ k + 1) * #bank) * (2 ^ k + 1) = (2 ^ k + 1) ^ 3 * #bank := by ring
        _ ≤ (2 ^ k + 1) ^ 3 * ((2 * 2 ^ k + 1) * 2 ^ J) := Nat.mul_le_mul_left _ hbank_card
        _ = (2 ^ k + 1) ^ 3 * (2 * 2 ^ k + 1) * 2 ^ J := by ring
    unfold partialTableBound
    omega

/-! ### Linear hashing -/

section Hash

variable {n m : ℕ}

/-- The linear map over the field with two elements whose output `j` is the parity of the bits
in `A j`. -/
private def linearMap (A : Fin m → Finset (Fin n)) (x : BitString n) : BitString m :=
  fun j => parityOn (A j) x

/-- Finite-set parity masks implement the shared Boolean-matrix hash. -/
private theorem linearMap_filter_eq_hash (rows : Fin m → BitString n) (x : BitString n) :
    linearMap (fun j => univ.filter fun i => rows j i = true) x =
      BitString.LinearHash.hash rows x := by
  funext j
  simp only [linearMap, parityOn_eq_sum, BitString.LinearHash.hash, dotProduct, sum_filter]
  apply sum_congr rfl
  intro i _
  cases rows j i <;> cases x i <;> rfl

/-- Some linear map collides on at most a `2⁻ᵐ` fraction of any specified distinct pairs. -/
private theorem exists_card_filter_linearMap_mul_le (P : Finset (BitString n × BitString n))
    (hP : ∀ z ∈ P, z.1 ≠ z.2) (m : ℕ) :
    ∃ A : Fin m → Finset (Fin n), #{z ∈ P | linearMap A z.1 = linearMap A z.2} * 2 ^ m ≤ #P := by
  obtain ⟨rows, hrows⟩ := BitString.LinearHash.exists_card_collisions_le (m := m) P hP
  refine ⟨fun j => univ.filter fun i => rows j i = true, ?_⟩
  simpa only [linearMap_filter_eq_hash, Nat.mul_comm] using hrows

/-- The parity on `S` costs four gates per bit of `S` and a constant. -/
private theorem synthesis_parityOn (S : Finset (Fin n)) :
    Synthesis interpretation (inputs n) {parityOn S} (4 * #S + 1) := by
  induction S using Finset.induction_on with
  | empty =>
    have heq : parityOn (∅ : Finset (Fin n)) = fun _ => false := funext parityOn_empty
    simpa [heq] using Synthesis.const (s := inputs n) false
  | insert i S hi ih =>
    have heq : parityOn (insert i S) = fun x => x i ^^ parityOn S x :=
      funext (parityOn_insert hi)
    rw [heq, card_insert_of_notMem hi]
    exact ((Synthesis.of_mem (s := inputs n) ⟨i, rfl⟩).xor ih).mono Set.Subset.rfl
      Set.Subset.rfl (by omega)

/-- A linear map to `m` bits costs at most `4 n + 1` gates per output. -/
private theorem complexity_linearMap_le (A : Fin m → Finset (Fin n)) :
    complexity interpretation (linearMap A) ≤ m * (4 * n + 1) := by
  refine (complexity_pi_le (I := interpretation) fun j => parityOn (A j)).trans ?_
  calc ∑ j, complexity interpretation (single (parityOn (A j)))
      ≤ ∑ _j : Fin m, (4 * n + 1) := sum_le_sum fun j _ =>
        (synthesis_parityOn (A j)).complexity_le.trans
          (by have := (card_le_univ (A j)).trans_eq (Fintype.card_fin n); omega)
    _ = m * (4 * n + 1) := by simp

end Hash

/-! ### Sparse indicators -/

/-- The indicator of a set `R` of inputs costs `2 n + 2` gates per element of `R`, and a
constant. -/
private theorem complexity_indicator_le_card_mul {n : ℕ} (R : Finset (BitString n)) :
    complexity interpretation (single fun x => decide (x ∈ R)) ≤ #R * (2 * n + 2) + 1 := by
  have h := Synthesis.exists_mem R (fun a x => decide ((fun i => x (id i)) = a))
    (fun _ => 2 * n + 1) fun a _ => synthesis_minterm id a
  have heq : (fun x => decide (∃ a ∈ R, decide ((fun i => x (id i)) = a) = true)) =
      fun x => decide (x ∈ R) := by
    funext x
    simp
  rw [heq] at h
  exact h.complexity_le.trans (by simp)

/-- **One filter.** Hash to `k + l` bits and look the hash up in the image of `B`, by a sparse
table. This keeps all of `B` and, for a suitable hash, at most a `|B| / 2 ^ (k + l)` fraction
of `A`. -/
private theorem exists_filter {n : ℕ} (A B : Finset (BitString n)) (hAB : Disjoint A B)
    (k l : ℕ) {K : ℕ} (hK : 0 < K) :
    ∃ φ : BooleanFunction n, (∀ x ∈ B, φ x = true) ∧
      #{x ∈ A | φ x = true} * 2 ^ (k + l) ≤ #A * #B ∧
      complexity interpretation (single φ) ≤
        (k + l) * (4 * n + 1) + sparseTableBound k l K #B := by
  obtain ⟨H, hH⟩ := exists_card_filter_linearMap_mul_le (A ×ˢ B)
    (fun z hz h => disjoint_left.mp hAB (mem_product.mp hz).1 (h ▸ (mem_product.mp hz).2))
    (k + l)
  let φ : BooleanFunction n := fun x => decide (linearMap H x ∈ B.image (linearMap H))
  refine ⟨φ, fun x hx => decide_eq_true (mem_image_of_mem _ hx), ?_, ?_⟩
  · have hsub : ({x ∈ A | φ x = true} : Finset (BitString n)) ⊆
        ({z ∈ A ×ˢ B | linearMap H z.1 = linearMap H z.2} :
          Finset (BitString n × BitString n)).image Prod.fst := by
      intro x hx
      obtain ⟨hxA, hφ⟩ := mem_filter.mp hx
      obtain ⟨y, hyB, hy⟩ := mem_image.mp (of_decide_eq_true hφ)
      exact mem_image.mpr ⟨(x, y), mem_filter.mpr ⟨mem_product.mpr ⟨hxA, hyB⟩, hy.symm⟩, rfl⟩
    calc #{x ∈ A | φ x = true} * 2 ^ (k + l)
        ≤ #{z ∈ A ×ˢ B | linearMap H z.1 = linearMap H z.2} * 2 ^ (k + l) :=
          Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_image_le)
      _ ≤ #A * #B := hH.trans (card_product A B).le
  · have hcomp : single φ =
        (single fun y => decide (y ∈ B.image (linearMap H))) ∘ linearMap H := rfl
    rw [hcomp]
    refine (complexity_comp_le _ _).trans (Nat.add_le_add (complexity_linearMap_le H) ?_)
    exact (complexity_indicator_le_sparseTableBound _ hK).trans
      (sparseTableBound_mono card_image_le)

/-- **Repeated filters.** If `|B| ≤ 2 ^ p` and the hashes have `k + l = p + a` bits, then `t`
filters keep all of `B` and at most a `2 ^ -(a t)` fraction of `A`. -/
private theorem exists_filters {n p a k l K : ℕ} (B : Finset (BitString n)) (hB : #B ≤ 2 ^ p)
    (hkl : k + l = p + a) (hK : 0 < K) (t : ℕ) :
    ∀ A : Finset (BitString n), Disjoint A B → ∃ φ : BooleanFunction n,
      (∀ x ∈ B, φ x = true) ∧ #{x ∈ A | φ x = true} * 2 ^ (a * t) ≤ #A ∧
      complexity interpretation (single φ) ≤
        t * ((k + l) * (4 * n + 1) + sparseTableBound k l K (2 ^ p) + 1) + 1 := by
  induction t with
  | zero =>
    intro A _
    refine ⟨fun _ => true, by simp, by simp, ?_⟩
    simpa using (Synthesis.const (s := inputs n) true).complexity_le
  | succ t ih =>
    intro A hAB
    obtain ⟨φ, hφB, hφA, hφ⟩ := exists_filter A B hAB k l hK
    let rest := A.filter fun x => φ x = true
    obtain ⟨ψ, hψB, hψA, hψ⟩ := ih rest (disjoint_of_subset_left (filter_subset _ _) hAB)
    refine ⟨fun x => φ x && ψ x, fun x hx => by simp [hφB x hx, hψB x hx], ?_, ?_⟩
    · have heq : ({x ∈ A | (φ x && ψ x) = true} : Finset (BitString n)) =
          {x ∈ rest | ψ x = true} := by
        ext x
        simp [rest, and_assoc]
      have hrest : #rest * 2 ^ a ≤ #A := by
        have h : #rest * 2 ^ a * 2 ^ p ≤ #A * 2 ^ p :=
          calc #rest * 2 ^ a * 2 ^ p = #rest * 2 ^ (k + l) := by rw [hkl, pow_add]; ring
            _ ≤ #A * #B := hφA
            _ ≤ #A * 2 ^ p := Nat.mul_le_mul_left _ hB
        exact Nat.le_of_mul_le_mul_right h (Nat.two_pow_pos p)
      rw [heq, Nat.mul_succ, pow_add]
      calc #{x ∈ rest | ψ x = true} * (2 ^ (a * t) * 2 ^ a)
          = #{x ∈ rest | ψ x = true} * 2 ^ (a * t) * 2 ^ a := by ring
        _ ≤ #rest * 2 ^ a := Nat.mul_le_mul_right _ hψA
        _ ≤ #A := hrest
    · refine (complexity_and_le φ ψ).trans ?_
      have := hφ.trans (Nat.add_le_add_left (sparseTableBound_mono (K := K) (l := l) hB) _)
      rw [Nat.succ_mul]
      omega

/-- The gate budget of the construction for the indicator of a set of at most `2 ^ p` of the
`2 ^ n` inputs: `t` filters, each hashing to `k + l = p + a` bits and looking the hash up in a
sparse table with chunks of `K` columns, and explicit minterms for the at most
`2 ^ n / 2 ^ (a t)` inputs that wrongly pass every filter. -/
def indicatorBound (n k l K p a t : ℕ) : ℕ :=
  t * ((k + l) * (4 * n + 1) + sparseTableBound k l K (2 ^ p) + 1) +
    2 ^ n / 2 ^ (a * t) * (2 * n + 2) + 4

/-- **Sparse indicators.** The indicator of a set of at most `2 ^ p` inputs costs at most
`indicatorBound n k l K p a t` gates, whenever `k + l = p + a` and `K > 0`. -/
theorem complexity_indicator_le_indicatorBound {n p a k l K : ℕ} (B : Finset (BitString n))
    (hB : #B ≤ 2 ^ p) (hkl : k + l = p + a) (hK : 0 < K) (t : ℕ) :
    complexity interpretation (single fun x => decide (x ∈ B)) ≤
      indicatorBound n k l K p a t := by
  obtain ⟨φ, hφB, hφA, hφ⟩ := exists_filters B hB hkl hK t Bᶜ disjoint_compl_left
  let R := Bᶜ.filter fun x => φ x = true
  have hR : #R ≤ 2 ^ n / 2 ^ (a * t) :=
    (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr
      (hφA.trans ((card_le_univ _).trans (by simp)))
  have heq : (fun x => decide (x ∈ B)) = fun x => φ x && !decide (x ∈ R) := by
    funext x
    by_cases hx : x ∈ B
    · simp [R, hx, hφB x hx]
    · cases h : φ x <;> simp [R, hx, h]
  rw [heq]
  have hR' := (complexity_not_le _).trans
    (Nat.add_le_add_right (complexity_indicator_le_card_mul R) 1)
  refine (complexity_and_le _ _).trans
    (le_trans (Nat.add_le_add_right (Nat.add_le_add hφ hR') 1) ?_)
  have := Nat.mul_le_mul_right (2 * n + 2) hR
  unfold indicatorBound
  omega

/-! ### Partial functions -/

/-- The gate budget of the construction for a function on a set of `w` of the `2 ^ n` inputs:
a hash to `k + l` bits, a partial table with chunks of `J` entries for the values on the
image, and explicit minterms correcting the at most `w ^ 2 / 2 ^ (k + l)` inputs whose hashes
collide with others. -/
def partialBound (n k l J w : ℕ) : ℕ :=
  (k + l) * (4 * n + 1) + partialTableBound k l J w + w * w / 2 ^ (k + l) * (2 * n + 2) + 5

/-- **Partial functions.** A Boolean function on a set `D` of inputs costs at most
`partialBound n k l J |D|` gates on `D`, whenever `J > 0`. -/
theorem complexityOn_le_partialBound {n : ℕ} (k l : ℕ) {J : ℕ} (D : Finset (BitString n))
    (u : BooleanFunction n) (hJ : 0 < J) :
    complexityOn interpretation D (single u) ≤ partialBound n k l J #D := by
  obtain ⟨H, hH⟩ := exists_card_filter_linearMap_mul_le D.offDiag
    (fun z hz => (mem_offDiag.mp hz).2.2) (k + l)
  let T := D.image (linearMap H)
  have hpre (y : BitString (k + l)) (hy : y ∈ T) : ∃ x ∈ D, linearMap H x = y := mem_image.mp hy
  choose rep hrep_mem hrep using hpre
  let label (y : BitString (k + l)) : Bool := if hy : y ∈ T then u (rep y hy) else false
  obtain ⟨φ, hφ, hφc⟩ := exists_eqOn_complexity_le_partialTableBound T label hJ
  let E := D.filter fun x => φ (linearMap H x) ≠ u x
  have hE : #E * 2 ^ (k + l) ≤ #D * #D := by
    have hsub : E ⊆ ({z ∈ D.offDiag | linearMap H z.1 = linearMap H z.2} :
        Finset (BitString n × BitString n)).image Prod.fst := by
      intro x hx
      obtain ⟨hxD, hne⟩ := mem_filter.mp hx
      have hy : linearMap H x ∈ T := mem_image_of_mem _ hxD
      refine mem_image.mpr ⟨(x, rep _ hy), mem_filter.mpr ⟨mem_offDiag.mpr ⟨hxD,
        hrep_mem _ hy, fun h => hne ?_⟩, (hrep _ hy).symm⟩, rfl⟩
      rw [hφ hy]
      simp only [label, hy, dite_true]
      exact congrArg u h.symm
    calc #E * 2 ^ (k + l)
        ≤ #{z ∈ D.offDiag | linearMap H z.1 = linearMap H z.2} * 2 ^ (k + l) :=
          Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_image_le)
      _ ≤ #D.offDiag := hH
      _ ≤ #D * #D := by rw [offDiag_card]; exact Nat.sub_le _ _
  have hEc := (complexity_indicator_le_card_mul E).trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right (2 * n + 2) ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr hE)) 1)
  have hcongr : Set.EqOn (single u) (single fun x => φ (linearMap H x) ^^ decide (x ∈ E))
      (D : Set (BitString n)) := by
    intro x hx
    funext j
    have hx : x ∈ D := hx
    by_cases h : φ (linearMap H x) = u x
    · simp [E, hx, h]
    · simp only [single_apply, E, mem_filter, hx, true_and]
      cases hu : u x <;> cases hv : φ (linearMap H x) <;> simp_all
  rw [complexityOn_congr hcongr]
  refine complexityOn_le_complexity.trans ((complexity_xor_le _ _).trans ?_)
  have hcomp : single (fun x => φ (linearMap H x)) = single φ ∘ linearMap H := rfl
  rw [hcomp]
  have hHφ := (complexity_comp_le (I := interpretation) (linearMap H) (single φ)).trans
    (Nat.add_le_add (complexity_linearMap_le H)
      (hφc.trans (partialTableBound_mono card_image_le)))
  unfold partialBound
  omega

end Cslib.Circuits.Boolean.SparseSynthesis
