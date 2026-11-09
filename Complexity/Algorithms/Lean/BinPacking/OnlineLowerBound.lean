/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.BinPacking.Online
import Mathlib.Tactic.Linarith

/-!
# Yao's `3/2` lower bound for online bin packing

No deterministic online bin-packing algorithm has asymptotic competitive ratio below `3/2`:
the abstract of [Yao][Yao1980] defines `r(S)` as the maximum ratio `S(L) / L*` for large `L*` and
states that every on-line algorithm `S` has `r(S) ≥ 3/2`. The construction uses the item types
`1/7 + ε`, `1/3 + ε` and `1/2 + ε`, as reported in
[Balogh, Békési, Dósa, Epstein and Levin, Section 1][BaloghBekesiDosaEpsteinLevin2018]; Yao's full
text, and so his theorem number and proof, were not inspected.
The input has three phases of `6 * m` items each, of sizes just above `1/7`, `1/3` and `1/2`.
Here the capacity is `41` and the sizes are `6`, `14` and `21`. These give the same 20 feasible
bin patterns (counts of the three sizes that fit into one bin) as `1/7 + ε`, `1/3 + ε` and
`1/2 + ε` with capacity `1`, and `41` is the smallest capacity with this property. The optima
after the three phases are `m`, `3 * m` and `6 * m` (`isPacking_yao₁` and
`le_length_of_isPacking_yao₁`, and so on).

`OnlinePacker.yao_lower_bound`: for every online packer `A` and every `m`, after one of the three
phases `A` uses at least `3/2` times the optimum, exactly, with no additive constant. Since the
packer only sees a prefix, it cannot tell at which phase the input stops.

**The certificate.** Give the items of sizes `6`, `14` and `21` the weights `1`, `2` and `2`
(`yaoWeight`). For every bin `b` with `b.sum ≤ 41`,

  `weight b ≤ 2 + 2 * [b has a 6] + 2 * [b has a 6 or a 14]`  (`sum_map_yaoWeight_le`).

`omega` checks this from `6 * #6 + 14 * #14 + 21 * #21 ≤ 41`, so the certificate is checked
against all 20 feasible patterns `(#6, #14, #21)`; the test file also lists the 20 patterns and
checks the inequality on each by `decide`. Equality holds for the patterns `(6, 0, 0)`,
`(4, 1, 0)`, `(2, 2, 0)`, `(0, 2, 0)`, `(0, 1, 1)` and `(0, 0, 1)`. Summed over the final bins,
the left side is the total weight `30 * m`.
Bins holding a `6` already exist after the first phase, and bins holding a `6` or a `14` after the
second (`OnlinePacker.countP_any_runFrom`). So, writing `F₁`, `F₂` and `F₃` for the numbers of
bins after the three phases, `30 * m ≤ 2 * F₁ + 2 * F₂ + 2 * F₃`
(`OnlinePacker.sum_map_yaoWeight_le_run`). If `2 * F₁ < 3 * m`, `2 * F₂ < 9 * m` and
`2 * F₃ < 18 * m`, then `2 * F₁ + 2 * F₂ + 2 * F₃ < 30 * m`, a contradiction. In linear-programming
terms, the weights are the dual multipliers `3/10`, `3/5` and `3/5` of the three item counts and
the factor `2` is the multiplier `3/5` of each phase's ratio constraint, scaled by `10/3`; an exact
rational LP over the 20 patterns gives the optimal ratio `3/2` for this input, so the certificate
is optimal, and the test file checks an online packer attaining `3/2` after every phase.
The integer instance and the explicit certificate are a presentation chosen here; the bound and the
item types are Yao's.

The last two phases alone give `4/3` (`OnlinePacker.four_thirds_lower_bound`), by the same
certificate.

`OnlinePacker.exists_ratio_violation_of_lt` restates the bound: for `a / b < 3/2` and every
additive constant `c`, every online packer violates `b * ALG ≤ a * OPT + c` on some input.

## Main definitions

* `Cslib.Algorithms.Lean.BinPacking.yaoWeight`: the weights of the certificate.

## Main results

* `Cslib.Algorithms.Lean.BinPacking.sum_map_yaoWeight_le`: the certificate for one bin.
* `Cslib.Algorithms.Lean.BinPacking.OnlinePacker.yao_lower_bound`: Yao's `3/2` lower bound.
* `Cslib.Algorithms.Lean.BinPacking.OnlinePacker.exists_optimal_three_mul_le`: for every `m`, an
  input whose optimum is at least `m` on which an online packer uses at least `3/2` times the
  optimum.
* `Cslib.Algorithms.Lean.BinPacking.OnlinePacker.exists_ratio_violation_of_lt`: no ratio below
  `3/2` with any additive constant.
* `Cslib.Algorithms.Lean.BinPacking.OnlinePacker.four_thirds_lower_bound`: the two-phase `4/3`.
* `Cslib.Algorithms.Lean.BinPacking.OnlinePacker.sum_map_yaoWeight_le_run`: Yao's counting, for
  every three-phase input whose later phases avoid the earlier sizes.
* `Cslib.Algorithms.Lean.BinPacking.isPacking_yao₁` and
  `Cslib.Algorithms.Lean.BinPacking.le_length_of_isPacking_yao₁` (and `₂`, `₃`): the optima `m`,
  `3 * m` and `6 * m` after the three phases.
* `Cslib.Algorithms.Lean.BinPacking.isPacking_twoPhase₁` and
  `Cslib.Algorithms.Lean.BinPacking.le_length_of_isPacking_twoPhase₁` (and `₂`): the optima
  `3 * m` and `6 * m` of the two-phase input.

## References

* [A. C.-C. Yao, *New algorithms for bin packing*][Yao1980]
* [J. Balogh, J. Békési, G. Dósa, L. Epstein, A. Levin, *A new lower bound for classic online bin
  packing*][BaloghBekesiDosaEpsteinLevin2018]
-/

public section

namespace Cslib.Algorithms.Lean.BinPacking

open List

/-- The weight of an item in Yao's certificate: `1` for size `6`, `2` for sizes `14` and `21`,
and `0` otherwise. -/
@[expose] def yaoWeight (a : ℕ) : ℕ := if a = 6 then 1 else if a = 14 ∨ a = 21 then 2 else 0

private theorem sum_map_yaoWeight (b : List ℕ) :
    (b.map yaoWeight).sum = b.count 6 + 2 * b.count 14 + 2 * b.count 21 := by
  induction b with
  | nil => simp
  | cons a b ih =>
    simp only [map_cons, sum_cons, ih, count_cons, yaoWeight, beq_iff_eq]
    split_ifs <;> omega

private theorem six_mul_count_add_le_sum (b : List ℕ) :
    6 * b.count 6 + 14 * b.count 14 + 21 * b.count 21 ≤ b.sum := by
  induction b with
  | nil => simp
  | cons a b ih =>
    simp only [sum_cons, count_cons, beq_iff_eq]
    split_ifs <;> omega

/-- **The certificate.** A bin of capacity `41` has weight at most `2`, plus `2` if it holds a
`6`, plus `2` if it holds a `6` or a `14`. -/
theorem sum_map_yaoWeight_le {b : List ℕ} (hb : b.sum ≤ 41) :
    (b.map yaoWeight).sum ≤ 2 + 2 * (if b.any (· == 6) then 1 else 0) +
      2 * (if b.any (fun a => a == 6 || a == 14) then 1 else 0) := by
  have h := six_mul_count_add_le_sum b
  rw [sum_map_yaoWeight]
  have e1 : b.any (· == 6) = true ↔ 6 ∈ b := by simp
  have e2 : b.any (fun a => a == 6 || a == 14) = true ↔ 6 ∈ b ∨ 14 ∈ b := by
    simp only [any_eq_true, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨x, hx, rfl | rfl⟩
      exacts [Or.inl hx, Or.inr hx]
    · rintro (hx | hx)
      exacts [⟨6, hx, Or.inl rfl⟩, ⟨14, hx, Or.inr rfl⟩]
  split_ifs with h1 h2 h2
  · omega
  · exact absurd (e2.2 (Or.inl (e1.1 h1))) h2
  · have := count_eq_zero.2 fun h => h1 (e1.2 h)
    omega
  · have := count_eq_zero.2 fun h => h1 (e1.2 h)
    have := count_eq_zero.2 fun h => h2 (e2.2 (Or.inr h))
    omega

private theorem sum_map_le_of_le {f : List ℕ → ℕ} {p q : List ℕ → Bool} :
    ∀ {B : List (List ℕ)}, (∀ b ∈ B, f b ≤ 2 + 2 * (if p b then 1 else 0) +
      2 * (if q b then 1 else 0)) →
      (B.map f).sum ≤ 2 * B.length + 2 * B.countP p + 2 * B.countP q
  | [], _ => by simp
  | b :: B, h => by
    simp only [map_cons, sum_cons, length_cons, countP_cons]
    have ih := sum_map_le_of_le (fun c hc => h c (mem_cons_of_mem _ hc))
    have hb := h b mem_cons_self
    split_ifs at hb ⊢ <;> omega

namespace OnlinePacker

variable (A : OnlinePacker 41)

/-- **Yao's counting.** If the second phase has no `6` and the third has no `6` or `14`, the total
weight is at most twice the sum of the numbers of bins after the three phases. -/
theorem sum_map_yaoWeight_le_run {l₁ l₂ l₃ : List ℕ} (h₂ : 6 ∉ l₂) (h₃ : 6 ∉ l₃ ∧ 14 ∉ l₃)
    (hle : ∀ a ∈ l₁ ++ l₂ ++ l₃, a ≤ 41) :
    ((l₁ ++ l₂ ++ l₃).map yaoWeight).sum ≤ 2 * (A.run l₁).length +
      2 * (A.run (l₁ ++ l₂)).length + 2 * (A.run (l₁ ++ l₂ ++ l₃)).length := by
  have hP := A.isPacking_run hle
  rw [← (hP.perm.map yaoWeight).sum_eq, map_flatten, sum_flatten, map_map]
  have key := sum_map_le_of_le (f := sum ∘ map yaoWeight)
    (p := fun b => b.any (· == 6)) (q := fun b => b.any (fun a => a == 6 || a == 14))
    (B := A.run (l₁ ++ l₂ ++ l₃)) fun b hb => sum_map_yaoWeight_le (hP.sum_le b hb)
  have c1 : (A.run (l₁ ++ l₂ ++ l₃)).countP (fun b => b.any (· == 6)) =
      (A.run l₁).countP (fun b => b.any (· == 6)) := by
    rw [append_assoc, run_append]
    refine A.countP_any_runFrom fun a ha => ?_
    have : a ≠ 6 := by grind
    simpa using this
  have c2 : (A.run (l₁ ++ l₂ ++ l₃)).countP (fun b => b.any (fun a => a == 6 || a == 14)) =
      (A.run (l₁ ++ l₂)).countP (fun b => b.any (fun a => a == 6 || a == 14)) := by
    rw [run_append]
    refine A.countP_any_runFrom fun a ha => ?_
    have h6 : a ≠ 6 := by rintro rfl; exact h₃.1 ha
    have h14 : a ≠ 14 := by rintro rfl; exact h₃.2 ha
    simpa using ⟨h6, h14⟩
  have d1 := countP_le_length (p := fun b => b.any (· == 6)) (l := A.run l₁)
  have d2 := countP_le_length (p := fun b => b.any (fun a => a == 6 || a == 14))
    (l := A.run (l₁ ++ l₂))
  omega

/-- **Yao's lower bound.** Against `6 * m` items of size `6`, then `6 * m` of size `14`, then
`6 * m` of size `21`, in bins of capacity `41`, every online packer uses at least `3/2` times the
optimum after one of the three phases. The optima are `m`, `3 * m` and `6 * m`
(`le_length_of_isPacking_yao₁` and `isPacking_yao₁`, and so on). -/
theorem yao_lower_bound (m : ℕ) :
    3 * m ≤ 2 * (A.run (replicate (6 * m) 6)).length ∨
      3 * (3 * m) ≤ 2 * (A.run (replicate (6 * m) 6 ++ replicate (6 * m) 14)).length ∨
      3 * (6 * m) ≤ 2 * (A.run (replicate (6 * m) 6 ++ replicate (6 * m) 14 ++
        replicate (6 * m) 21)).length := by
  have h := A.sum_map_yaoWeight_le_run (l₁ := replicate (6 * m) 6)
    (l₂ := replicate (6 * m) 14) (l₃ := replicate (6 * m) 21)
    (by simp [mem_replicate]) (by simp [mem_replicate]) (by
      intro a ha
      simp only [mem_append, mem_replicate] at ha
      omega)
  have hw : ((replicate (6 * m) 6 ++ replicate (6 * m) 14 ++ replicate (6 * m) 21).map
      yaoWeight).sum = 30 * m := by
    simp [yaoWeight]
    omega
  omega

/-- **The two-phase bound `4/3`.** Against `6 * m` items of size `14`, then `6 * m` of size
`21`, every online packer uses at least `4/3` times the optimum (`3 * m`, then `6 * m`, by
`isPacking_twoPhase₁` and `le_length_of_isPacking_twoPhase₁`, and so on) after one of the two
phases. -/
theorem four_thirds_lower_bound (m : ℕ) :
    4 * (3 * m) ≤ 3 * (A.run (replicate (6 * m) 14)).length ∨
      4 * (6 * m) ≤ 3 * (A.run (replicate (6 * m) 14 ++ replicate (6 * m) 21)).length := by
  have h := A.sum_map_yaoWeight_le_run (l₁ := []) (l₂ := replicate (6 * m) 14)
    (l₃ := replicate (6 * m) 21) (by simp [mem_replicate]) (by simp [mem_replicate]) (by
      intro a ha
      simp only [nil_append, mem_append, mem_replicate] at ha
      omega)
  have hw : ((replicate (6 * m) 14 ++ replicate (6 * m) 21).map yaoWeight).sum = 24 * m := by
    simp [yaoWeight]
    omega
  simp only [nil_append, run_nil, length_nil] at h
  omega

end OnlinePacker

private theorem count_six_le {b : List ℕ} (hb : b.sum ≤ 41) : b.count 6 ≤ 6 := by
  have := six_mul_count_add_le_sum b
  omega

private theorem count_fourteen_le {b : List ℕ} (hb : b.sum ≤ 41) : b.count 14 ≤ 2 := by
  have := six_mul_count_add_le_sum b
  omega

private theorem count_twentyOne_le {b : List ℕ} (hb : b.sum ≤ 41) : b.count 21 ≤ 1 := by
  have := six_mul_count_add_le_sum b
  omega

/-- The first phase fits into `m` bins. -/
theorem isPacking_yao₁ (m : ℕ) :
    IsPacking 41 (replicate (6 * m) 6) (replicate m (replicate 6 6)) := by
  refine ⟨perm_iff_count.2 fun x => ?_, fun b hb => ?_⟩
  · simp only [count_flatten, map_replicate, sum_replicate, count_replicate]
    split_ifs <;> simp [Nat.mul_comm]
  · rw [eq_of_mem_replicate hb]
    decide

/-- The first two phases fit into `3 * m` bins. -/
theorem isPacking_yao₂ (m : ℕ) :
    IsPacking 41 (replicate (6 * m) 6 ++ replicate (6 * m) 14)
      (replicate (3 * m) [6, 6, 14, 14]) := by
  refine ⟨perm_iff_count.2 fun x => ?_, fun b hb => ?_⟩
  · by_cases h6 : x = 6
    · subst h6; simp [count_flatten, count_replicate]; omega
    by_cases h14 : x = 14
    · subst h14; simp [count_flatten, count_replicate]; omega
    simp [count_flatten, count_replicate, Ne.symm h6, Ne.symm h14]
  · rw [eq_of_mem_replicate hb]
    decide

/-- All three phases fit into `6 * m` bins. -/
theorem isPacking_yao₃ (m : ℕ) :
    IsPacking 41 (replicate (6 * m) 6 ++ replicate (6 * m) 14 ++ replicate (6 * m) 21)
      (replicate (6 * m) [6, 14, 21]) := by
  refine ⟨perm_iff_count.2 fun x => ?_, fun b hb => ?_⟩
  · by_cases h6 : x = 6
    · subst h6; simp [count_flatten, count_replicate]
    by_cases h14 : x = 14
    · subst h14; simp [count_flatten, count_replicate]
    by_cases h21 : x = 21
    · subst h21; simp [count_flatten, count_replicate]
    simp [count_flatten, count_replicate, Ne.symm h6, Ne.symm h14, Ne.symm h21]
  · rw [eq_of_mem_replicate hb]
    decide

/-- Every packing of the first phase has at least `m` bins: a bin holds at most six items of
size `6`. -/
theorem le_length_of_isPacking_yao₁ {m : ℕ} {Q : List (List ℕ)}
    (hQ : IsPacking 41 (replicate (6 * m) 6) Q) : m ≤ Q.length := by
  have := hQ.count_le_mul_length 6 fun b hb => count_six_le hb
  simp at this
  omega

/-- Every packing of the first two phases has at least `3 * m` bins: a bin holds at most two
items of size `14`. -/
theorem le_length_of_isPacking_yao₂ {m : ℕ} {Q : List (List ℕ)}
    (hQ : IsPacking 41 (replicate (6 * m) 6 ++ replicate (6 * m) 14) Q) : 3 * m ≤ Q.length := by
  have := hQ.count_le_mul_length 14 fun b hb => count_fourteen_le hb
  simp [count_replicate] at this
  omega

/-- Every packing of all three phases has at least `6 * m` bins: a bin holds at most one item of
size `21`. -/
theorem le_length_of_isPacking_yao₃ {m : ℕ} {Q : List (List ℕ)}
    (hQ : IsPacking 41 (replicate (6 * m) 6 ++ replicate (6 * m) 14 ++ replicate (6 * m) 21) Q) :
    6 * m ≤ Q.length := by
  have := hQ.count_le_mul_length 21 fun b hb => count_twentyOne_le hb
  simp [count_replicate] at this
  omega

/-- The `6 * m` items of size `14` of the two-phase input fit into `3 * m` bins. -/
theorem isPacking_twoPhase₁ (m : ℕ) :
    IsPacking 41 (replicate (6 * m) 14) (replicate (3 * m) [14, 14]) := by
  refine ⟨perm_iff_count.2 fun x => ?_, fun b hb => ?_⟩
  · by_cases h14 : x = 14
    · subst h14; simp [count_flatten]; omega
    simp [count_flatten, count_replicate, Ne.symm h14]
  · rw [eq_of_mem_replicate hb]
    decide

/-- Both phases of the two-phase input fit into `6 * m` bins. -/
theorem isPacking_twoPhase₂ (m : ℕ) :
    IsPacking 41 (replicate (6 * m) 14 ++ replicate (6 * m) 21) (replicate (6 * m) [14, 21]) := by
  refine ⟨perm_iff_count.2 fun x => ?_, fun b hb => ?_⟩
  · by_cases h14 : x = 14
    · subst h14; simp [count_flatten, count_replicate]
    by_cases h21 : x = 21
    · subst h21; simp [count_flatten, count_replicate]
    simp [count_flatten, count_replicate, Ne.symm h14, Ne.symm h21]
  · rw [eq_of_mem_replicate hb]
    decide

/-- Every packing of `6 * m` items of size `14` has at least `3 * m` bins. -/
theorem le_length_of_isPacking_twoPhase₁ {m : ℕ} {Q : List (List ℕ)}
    (hQ : IsPacking 41 (replicate (6 * m) 14) Q) : 3 * m ≤ Q.length := by
  have := hQ.count_le_mul_length 14 fun b hb => count_fourteen_le hb
  simp at this
  omega

/-- Every packing of both phases of the two-phase input has at least `6 * m` bins. -/
theorem le_length_of_isPacking_twoPhase₂ {m : ℕ} {Q : List (List ℕ)}
    (hQ : IsPacking 41 (replicate (6 * m) 14 ++ replicate (6 * m) 21) Q) : 6 * m ≤ Q.length := by
  have := hQ.count_le_mul_length 21 fun b hb => count_twentyOne_le hb
  simp [count_replicate] at this
  omega

namespace OnlinePacker

variable (A : OnlinePacker 41)

/-- **Yao's lower bound, packaged.** For every `m` there are items with an optimal packing `Q` of
at least `m` bins on which the online packer `A` uses at least `3/2 * Q.length` bins. -/
theorem exists_optimal_three_mul_le (m : ℕ) :
    ∃ (l : List ℕ) (Q : List (List ℕ)), IsPacking 41 l Q ∧
      (∀ Q', IsPacking 41 l Q' → Q.length ≤ Q'.length) ∧ m ≤ Q.length ∧
      3 * Q.length ≤ 2 * (A.run l).length := by
  rcases A.yao_lower_bound m with h | h | h
  · exact ⟨_, _, isPacking_yao₁ m, fun Q' hQ' => by simpa using le_length_of_isPacking_yao₁ hQ',
      by simp, by simpa using h⟩
  · exact ⟨_, _, isPacking_yao₂ m, fun Q' hQ' => by simpa using le_length_of_isPacking_yao₂ hQ',
      by simp; omega, by simpa using h⟩
  · exact ⟨_, _, isPacking_yao₃ m, fun Q' hQ' => by simpa using le_length_of_isPacking_yao₃ hQ',
      by simp; omega, by simpa using h⟩

/-- **No online ratio below `3/2`.** If `a / b < 3/2`, then for every additive constant `c` some
input has an optimal packing `Q` with `a * Q.length + c < b * ALG`. -/
theorem exists_ratio_violation_of_lt {a b : ℕ} (hab : 2 * a < 3 * b) (c : ℕ) :
    ∃ (l : List ℕ) (Q : List (List ℕ)), IsPacking 41 l Q ∧
      (∀ Q', IsPacking 41 l Q' → Q.length ≤ Q'.length) ∧
      a * Q.length + c < b * (A.run l).length := by
  obtain ⟨l, Q, hQ, hopt, hm, h⟩ := A.exists_optimal_three_mul_le (2 * c + 1)
  refine ⟨l, Q, hQ, hopt, ?_⟩
  have h1 : b * (3 * Q.length) ≤ b * (2 * (A.run l).length) := Nat.mul_le_mul_left b h
  have h2 : (2 * a + 1) * Q.length ≤ 3 * b * Q.length := Nat.mul_le_mul_right _ hab
  nlinarith

end OnlinePacker

end Cslib.Algorithms.Lean.BinPacking
