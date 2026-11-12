/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Log
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

/-!
# Covering a Boolean matrix by halving

Let `M` be a Boolean matrix with rows `R` and columns `C`. Either few columns together have a
zero in every row, or few rows together have a one in every column
(`Finset.exists_cover_zero_or_one`). Concretely, either at most `⌈log₂ (|R| + 1)⌉` columns
suffice, or at most `⌈log₂ (|C| + 1)⌉` rows.

The proof is greedy and follows [ChukhinKulikovMihajlinSmal2026], proof of Theorem 1.5 (printed
pp. 8–9; PDF pp. 9–10), which adapts [BeimelBenDanielKushilevitzWeinreb2010], Theorem 4. If at
least half of the entries are zeros, some column has zeros in at least half of the rows; pick it
and drop those rows. Otherwise some row has ones in more than half of the columns; pick it and
drop those columns. Each pick halves its side, so a side becomes empty after the stated number of
picks, and the picks on that side form the cover.

## Main results

* `Finset.exists_cover_zero_or_one`: the halving cover.
-/

public section

namespace Finset

variable {α β : Type*}

/-- One halving step costs one level of `⌈log₂ (· + 1)⌉`: if `2 r' ≤ r` and `r ≥ 1`, then
`⌈log₂ (r' + 1)⌉ + 1 ≤ ⌈log₂ (r + 1)⌉`. -/
theorem clog_succ_add_one_le {r r' : ℕ} (h : 2 * r' ≤ r) (hr : 0 < r) :
    Nat.clog 2 (r' + 1) + 1 ≤ Nat.clog 2 (r + 1) := by
  set K := Nat.clog 2 (r + 1)
  have hK : 0 < K := Nat.clog_pos one_lt_two (by omega)
  have hle : r + 1 ≤ 2 ^ K := Nat.le_pow_clog one_lt_two _
  obtain ⟨K', hK'⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  rw [hK', pow_succ] at hle
  have : r' + 1 ≤ 2 ^ K' := by omega
  have := Nat.clog_le_of_le_pow this
  omega

/-- **The halving cover.** For a Boolean matrix `M` on rows `R` and columns `C`, either some list
of at most `⌈log₂ (|R| + 1)⌉` columns of `C` has, for every row of `R`, a column where that row
is `false`, or some list of at most `⌈log₂ (|C| + 1)⌉` rows of `R` has, for every column of `C`, a
row where that column is `true`. -/
theorem exists_cover_zero_or_one (M : α → β → Bool) (R : Finset α) (C : Finset β) :
    (∃ cs : List β, (∀ c ∈ cs, c ∈ C) ∧ cs.length ≤ Nat.clog 2 (#R + 1) ∧
        ∀ a ∈ R, ∃ c ∈ cs, M a c = false) ∨
      ∃ rs : List α, (∀ a ∈ rs, a ∈ R) ∧ rs.length ≤ Nat.clog 2 (#C + 1) ∧
        ∀ c ∈ C, ∃ a ∈ rs, M a c = true := by
  induction hN : #R + #C using Nat.strong_induction_on generalizing R C with
  | _ N ih =>
  rcases R.eq_empty_or_nonempty with rfl | hR
  · exact .inl ⟨[], by simp, by simp, by simp⟩
  rcases C.eq_empty_or_nonempty with rfl | hC
  · exact .inr ⟨[], by simp, by simp, by simp⟩
  have hR0 : 0 < #R := hR.card_pos
  have hC0 : 0 < #C := hC.card_pos
  by_cases hcol : ∃ c ∈ C, #R ≤ 2 * #{a ∈ R | M a c = false}
  · -- Pick a column with zeros in at least half of the rows and drop those rows.
    obtain ⟨c, hc, hz⟩ := hcol
    set R' := {a ∈ R | M a c = true}
    have hsplit : #R' + #{a ∈ R | M a c = false} = #R := by
      have := card_filter_add_card_filter_not (s := R) (p := fun a => M a c = true)
      simp only [Bool.not_eq_true] at this
      exact this
    have hlt : #R' < #R := by omega
    rcases ih (#R' + #C) (by omega) R' C rfl with ⟨cs, hcs, hlen, hcov⟩ | ⟨rs, hrs, hlen, hcov⟩
    · refine .inl ⟨c :: cs, ?_, ?_, fun a ha => ?_⟩
      · simpa using ⟨hc, hcs⟩
      · have := clog_succ_add_one_le (r' := #R') (by omega) hR0
        simp only [List.length_cons]
        omega
      · cases hac : M a c
        · exact ⟨c, by simp, hac⟩
        · obtain ⟨c', hc', h'⟩ := hcov a (by simp [R', ha, hac])
          exact ⟨c', by simp [hc'], h'⟩
    · exact .inr ⟨rs, fun a ha => (mem_filter.1 (hrs a ha)).1, hlen, hcov⟩
  · -- Otherwise some row has ones in more than half of the columns: double counting.
    push Not at hcol
    have hrow : ∃ a ∈ R, #C < 2 * #{c ∈ C | M a c = true} := by
      have hones (c : β) (hc : c ∈ C) : #R < 2 * #{a ∈ R | M a c = true} := by
        have := hcol c hc
        have hsplit := card_filter_add_card_filter_not (s := R)
          (p := fun a => M a c = true)
        simp only [Bool.not_eq_true] at hsplit
        omega
      have hsum : ∑ c ∈ C, #{a ∈ R | M a c = true} = ∑ a ∈ R, #{c ∈ C | M a c = true} :=
        (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (r := fun a c => M a c = true)).symm
      have hlt : ∑ _a ∈ R, #C < ∑ a ∈ R, 2 * #{c ∈ C | M a c = true} := by
        rw [sum_const, smul_eq_mul, ← mul_sum, ← hsum, mul_sum]
        calc #R * #C = ∑ _c ∈ C, #R := by rw [sum_const, smul_eq_mul, mul_comm]
          _ < ∑ c ∈ C, 2 * #{a ∈ R | M a c = true} := sum_lt_sum_of_nonempty hC hones
      obtain ⟨a, ha, h⟩ := exists_lt_of_sum_lt hlt
      exact ⟨a, ha, h⟩
    obtain ⟨a, ha, ho⟩ := hrow
    set C' := {c ∈ C | M a c = false}
    have hsplit : #{c ∈ C | M a c = true} + #C' = #C := by
      have := card_filter_add_card_filter_not (s := C) (p := fun c => M a c = true)
      simp only [Bool.not_eq_true] at this
      exact this
    have hlt : #C' < #C := by omega
    rcases ih (#R + #C') (by omega) R C' rfl with ⟨cs, hcs, hlen, hcov⟩ | ⟨rs, hrs, hlen, hcov⟩
    · exact .inl ⟨cs, fun c hc => (mem_filter.1 (hcs c hc)).1, hlen, hcov⟩
    · refine .inr ⟨a :: rs, ?_, ?_, fun c hc => ?_⟩
      · simpa using ⟨ha, hrs⟩
      · have := clog_succ_add_one_le (r' := #C') (by omega) hC0
        simp only [List.length_cons]
        omega
      · cases hac : M a c
        · obtain ⟨a', ha', h'⟩ := hcov c (by simp [C', hc, hac])
          exact ⟨a', by simp [ha'], h'⟩
        · exact ⟨a, by simp, hac⟩

end Finset
