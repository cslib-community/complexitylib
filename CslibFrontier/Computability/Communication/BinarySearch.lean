/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Operations

/-!
# Binary search for a coordinate where a sum drops

Alice holds `x` and Bob holds `y`, and each index `i` of a list carries Alice's integer `f x i` and
Bob's integer `g y i`. If Bob's sum is smaller than Alice's, some index has `g y i < f x i`, and the
players find one by binary search: they compare the sums over the first half of the list, recurse
into the first half if Bob's sum is smaller there and into the second half otherwise. If comparing
the sums over a sublist takes `c` bits, finding the index takes `⌈log₂ |l|⌉ · c` bits
(`Cslib.Communication.Protocol.exists_search_lt`).

This is the search step in the proof of Krajíček's interpolation theorem for cutting planes
[Krajíček, Theorem 6.4][Krajicek1997], where `f x i` and `g y i` are the contributions `aᵢ uᵢ` and
`aᵢ vᵢ` of a shared variable to a linear inequality, and the comparison costs
`⌈log₂ (2 M n + 1)⌉ + 1` bits for coefficients at most `M` in absolute value.

## Main results

* `Cslib.Communication.Protocol.exists_search_lt`: binary search for an index where Bob's summand is
  smaller than Alice's.

## References

* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*, Theorem 6.4][Krajicek1997]
-/

public section

namespace Cslib.Communication.Protocol

variable {X Y ι : Type*}

/-- **Binary search for a coordinate where a sum drops.** Suppose that for every list of at most
`L` indices, Alice holding `x` and Bob holding `y` can decide with `c` bits whether
`∑ g y < ∑ f x` over the list. Then for every list `l` of at most `L` indices they can find, with
`⌈log₂ |l|⌉ · c` bits, an index `i` with `g y i < f x i` whenever `∑ g y < ∑ f x` over `l`. -/
theorem exists_search_lt (f : X → ι → ℤ) (g : Y → ι → ℤ) (L c : ℕ)
    (hcmp : ∀ l : List ι, l.length ≤ L → ∃ p : Protocol X Y Bool, p.depth ≤ c ∧
      ∀ x y, p.run x y = true ↔ (l.map (g y)).sum < (l.map (f x)).sum)
    (l : List ι) (hl : l.length ≤ L) :
    ∃ p : Protocol X Y (Option ι), p.depth ≤ Nat.clog 2 l.length * c ∧
      ∀ x y, (l.map (g y)).sum < (l.map (f x)).sum → ∃ i ∈ p.run x y, g y i < f x i := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ m ih =>
    obtain rfl | rfl | hm2 : m = 0 ∨ m = 1 ∨ 2 ≤ m := by omega
    · rw [List.length_eq_zero_iff] at h
      subst h
      exact ⟨.output none, by simp, fun x y h => by simp at h⟩
    · obtain ⟨i, rfl⟩ := List.length_eq_one_iff.1 h
      exact ⟨.output (some i), by simp, fun x y h => ⟨i, rfl, by simpa using h⟩⟩
    · have hlt₁ : (l.take (m / 2)).length < m := by
        rw [List.length_take]; omega
      have hlt₂ : (l.drop (m / 2)).length < m := by
        rw [List.length_drop]; omega
      have hL₁ : (l.take (m / 2)).length ≤ L := by rw [List.length_take]; omega
      have hL₂ : (l.drop (m / 2)).length ≤ L := by rw [List.length_drop]; omega
      obtain ⟨p₁, hp₁d, hp₁⟩ := ih _ hlt₁ (l.take (m / 2)) hL₁ rfl
      obtain ⟨p₂, hp₂d, hp₂⟩ := ih _ hlt₂ (l.drop (m / 2)) hL₂ rfl
      obtain ⟨q, hqd, hq⟩ := hcmp (l.take (m / 2)) hL₁
      refine ⟨q.bind fun b => bif b then p₁ else p₂, ?_, fun x y hxy => ?_⟩
      · have hc : Nat.clog 2 m = Nat.clog 2 ((m + 2 - 1) / 2) + 1 :=
          Nat.clog_of_two_le one_lt_two hm2
        have hc₁ : Nat.clog 2 (l.take (m / 2)).length ≤ Nat.clog 2 m - 1 := by
          rw [hc, Nat.add_sub_cancel]
          refine Nat.clog_mono_right 2 ?_
          rw [List.length_take]; omega
        have hc₂ : Nat.clog 2 (l.drop (m / 2)).length ≤ Nat.clog 2 m - 1 := by
          rw [hc, Nat.add_sub_cancel]
          refine Nat.clog_mono_right 2 ?_
          rw [List.length_drop]; omega
        have hpos : 1 ≤ Nat.clog 2 m := by omega
        refine (depth_bind_le (d := (Nat.clog 2 m - 1) * c) fun b => ?_).trans ?_
        · cases b
          · exact hp₂d.trans (Nat.mul_le_mul_right c hc₂)
          · exact hp₁d.trans (Nat.mul_le_mul_right c hc₁)
        · calc q.depth + (Nat.clog 2 m - 1) * c ≤ c + (Nat.clog 2 m - 1) * c := by omega
            _ = Nat.clog 2 m * c := by
              conv_rhs => rw [← Nat.sub_add_cancel hpos]
              ring
      · have hsplit (h : ι → ℤ) : (l.map h).sum =
            ((l.take (m / 2)).map h).sum + ((l.drop (m / 2)).map h).sum := by
          rw [← List.sum_append, ← List.map_append, List.take_append_drop]
        rw [run_bind]
        cases hb : q.run x y
        · have h₁ : ¬ ((l.take (m / 2)).map (g y)).sum < ((l.take (m / 2)).map (f x)).sum := by
            rw [← hq]; simp [hb]
          refine hp₂ x y ?_
          rw [hsplit, hsplit] at hxy
          omega
        · exact hp₁ x y ((hq x y).1 hb)

end Cslib.Communication.Protocol
