/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Formula
public import Complexity.Computability.Circuit.Boolean.Parity
public import Complexity.Foundations.Data.BitString.Threshold
public import Complexity.Foundations.Data.Hamming
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Khrapchenko's bound

**Khrapchenko's theorem** says that a De Morgan formula (see
`Complexity/Computability/Circuit/Boolean/Formula.lean`) that
is true on a set `A` of inputs and false on a set `B` has leaf size at least
`|E(A, B)| ^ 2 / (|A| |B|)`, where `E(A, B)` are the pairs of `A × B` at Hamming distance one
(`Formula.sq_card_hammingEdges_le`, stated without division) [Khrapchenko1971b],
[Jukna, Section 6.8][Jukna2012]. An input leaf can only separate along its own coordinate, so its
edges form a matching; a binary gate splits one side, and the Cauchy–Schwarz inequality makes the
measure subadditive; a negation exchanges the sides.

If every input of `A` has at least `s₁` neighbors in `B` and every input of `B` has at least `s₀`
neighbors in `A`, a formula separating them has leaf size at least `s₀ s₁`
(`Formula.mul_le_leafSize`). So "at least `k` of `n` bits" needs leaf size `k (n + 1 - k)`
(`mul_le_leafSize_of_computes_threshold`) and majority needs leaf size `⌊(n + 1) ^ 2 / 4⌋`
(`sq_div_four_le_leafSize_of_computes_majority`) [Khrapchenko1971b], and the parity of `n` bits,
which changes with every bit, needs leaf size `n ^ 2` (`sq_le_leafSize_of_computes_parity`)
[Khrapchenko1971].
Splitting the bits in halves, `x ⊕ y = (x ∧ ¬y) ∨ (¬x ∧ y)` gives formulas of leaf size exactly
`n ^ 2` when `n` is a power of two (`isLeast_leafSize_parity_two_pow`).

Since a formula of depth `d` has at most `2 ^ d` leaves, formulas for parity have depth at least
`2 log₂ n` (`two_mul_log_le_depth_of_computes_parity`). Here the depth counts negations; for the
textbook bound, where negations are free, see
`Complexity/Computability/Circuit/Boolean/KhrapchenkoDepth.lean`: the
formula depth of the parity of `2 ^ k` bits is exactly `2 k` (`formulaDepth_parity_two_pow`).

## Main definitions

* `Cslib.Circuits.Boolean.parityFormula`: formulas for parity of leaf size `4 ^ k` on `2 ^ k` bits.

## Main results

* `Cslib.Circuits.Formula.sq_card_hammingEdges_le`: Khrapchenko's bound.
* `Cslib.Circuits.Formula.mul_le_leafSize`: the bound in terms of neighbor counts.
* `Cslib.Circuits.Boolean.mul_le_leafSize_of_computes_threshold`: formulas for the threshold
  function `Th^n_k` have leaf size at least `k (n + 1 - k)`.
* `Cslib.Circuits.Boolean.sq_div_four_le_leafSize_of_computes_majority`: formulas for the majority
  of `n` bits have leaf size at least `⌊(n + 1) ^ 2 / 4⌋`.
* `Cslib.Circuits.Boolean.sq_le_leafSize_of_computes_parity`: formulas for parity have leaf size
  at least `n ^ 2`.
* `Cslib.Circuits.Boolean.isLeast_leafSize_parity_two_pow`: the least leaf size of a formula for
  the parity of `2 ^ k` bits is `(2 ^ k) ^ 2`.

## References

* [V. M. Khrapchenko, *Method of determining lower bounds for the complexity of
  Π-schemes*][Khrapchenko1971b]
* [V. M. Khrapchenko, *Complexity of the realization of a linear function in the class of
  Π-circuits*][Khrapchenko1971]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

open Finset Function Boolean

variable {n : ℕ} {A B : Finset (BitString n)}

/-! ### Khrapchenko's theorem -/

/-- If bit `i` is set on `A` and clear on `B`, the edges between them form a matching. -/
private theorem card_hammingEdges_le_of_forall {i : Fin n} (hA : ∀ a ∈ A, a i = true)
    (hB : ∀ b ∈ B, b i = false) : #(hammingEdges A B) ^ 2 ≤ #A * #B := by
  have key {a b : BitString n} (ha : a ∈ A) (hb : b ∈ B) (h : hammingDist a b = 1) (j : Fin n)
      (hj : j ≠ i) : a j = b j := by
    obtain ⟨l, hl, hother⟩ := hammingDist_eq_one_iff.1 h
    have hli : l = i := by
      by_contra hli
      exact absurd (hother i (Ne.symm hli)) (by rw [hA a ha, hB b hb]; decide)
    exact hother j (hli ▸ hj)
  rw [sq]
  refine Nat.mul_le_mul (card_le_card_of_injOn Prod.fst (fun e he => (mem_hammingEdges.1 he).1) ?_)
    (card_le_card_of_injOn Prod.snd (fun e he => (mem_hammingEdges.1 he).2.1) ?_)
  · rintro ⟨a, b⟩ he ⟨a', b'⟩ he' (rfl : a = a')
    obtain ⟨ha, hb, h⟩ := mem_hammingEdges.1 he
    obtain ⟨-, hb', h'⟩ := mem_hammingEdges.1 he'
    refine Prod.ext rfl (funext fun j => ?_)
    change b j = b' j
    by_cases hj : j = i
    · subst hj
      rw [hB b hb, hB b' hb']
    · exact (key ha hb h j hj).symm.trans (key ha hb' h' j hj)
  · rintro ⟨a, b⟩ he ⟨a', b'⟩ he' (rfl : b = b')
    obtain ⟨ha, hb, h⟩ := mem_hammingEdges.1 he
    obtain ⟨ha', -, h'⟩ := mem_hammingEdges.1 he'
    refine Prod.ext (funext fun j => ?_) rfl
    change a j = a' j
    by_cases hj : j = i
    · subst hj
      rw [hA a ha, hA a' ha']
    · exact (key ha hb h j hj).trans (key ha' hb h' j hj).symm

/-- The Cauchy–Schwarz step: the Khrapchenko measure is subadditive. -/
private theorem sq_add_le_mul {e₁ e₂ L₁ L₂ a b₁ b₂ : ℕ} (h₁ : e₁ ^ 2 ≤ L₁ * a * b₁)
    (h₂ : e₂ ^ 2 ≤ L₂ * a * b₂) : (e₁ + e₂) ^ 2 ≤ (L₁ + L₂) * a * (b₁ + b₂) := by
  have h4 : 4 * ((L₁ * a * b₂) * (L₂ * a * b₁)) ≤ (L₁ * a * b₂ + L₂ * a * b₁) ^ 2 := by
    zify
    nlinarith [sq_nonneg ((L₁ * a * b₂ : ℤ) - L₂ * a * b₁)]
  have hX : (2 * (e₁ * e₂)) ^ 2 ≤ (L₁ * a * b₂ + L₂ * a * b₁) ^ 2 :=
    calc (2 * (e₁ * e₂)) ^ 2 = 4 * (e₁ ^ 2 * e₂ ^ 2) := by ring
      _ ≤ 4 * ((L₁ * a * b₁) * (L₂ * a * b₂)) := by gcongr
      _ = 4 * ((L₁ * a * b₂) * (L₂ * a * b₁)) := by ring
      _ ≤ _ := h4
  have h₃ := (Nat.pow_le_pow_iff_left two_ne_zero).1 hX
  calc (e₁ + e₂) ^ 2 = e₁ ^ 2 + 2 * (e₁ * e₂) + e₂ ^ 2 := by ring
    _ ≤ L₁ * a * b₁ + (L₁ * a * b₂ + L₂ * a * b₁) + L₂ * a * b₂ := by gcongr
    _ = (L₁ + L₂) * a * (b₁ + b₂) := by ring

private theorem sum_and (f : Fin (signature.Arity Op.and) → ℕ) : ∑ j, f j = f 0 + f 1 :=
  Fin.sum_univ_two f

private theorem sum_or (f : Fin (signature.Arity Op.or) → ℕ) : ∑ j, f j = f 0 + f 1 :=
  Fin.sum_univ_two f

private theorem sum_not (f : Fin (signature.Arity Op.not) → ℕ) : ∑ j, f j = f 0 :=
  Fin.sum_univ_one f

/-- **Khrapchenko's bound.** A De Morgan formula that is true on `A` and false on `B` has leaf
size at least `|E(A, B)| ^ 2 / (|A| |B|)`, where `E(A, B)` are the pairs at Hamming distance
one. -/
theorem Formula.sq_card_hammingEdges_le (F : Formula signature n)
    (hA : ∀ a ∈ A, F.eval interpretation a = true) (hB : ∀ b ∈ B, F.eval interpretation b = false) :
    #(hammingEdges A B) ^ 2 ≤ F.leafSize * #A * #B := by
  induction F generalizing A B with
  | input i =>
    rw [Formula.leafSize_input, one_mul]
    exact card_hammingEdges_le_of_forall hA hB
  | gate op args ih =>
    cases op with
    | const c =>
      rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
      · simp [hammingEdges]
      rcases B.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
      · simp [hammingEdges]
      exact absurd ((hA a ha).symm.trans (hB b hb)) (by decide)
    | not =>
      have := ih 0 (A := B) (B := A) (fun b hb => by simpa [interpretation] using hB b hb)
        fun a ha => by simpa [interpretation] using hA a ha
      rw [card_hammingEdges_comm, Formula.leafSize_gate, sum_not]
      exact this.trans_eq (mul_right_comm _ _ _)
    | and =>
      have hA' : ∀ a ∈ A, (args 0).eval interpretation a = true ∧
          (args 1).eval interpretation a = true := fun a ha => by
        simpa [interpretation] using hA a ha
      have h₁ := ih 0 (A := A) (B := B.filter fun b => (args 0).eval interpretation b = false)
        (fun a ha => (hA' a ha).1) fun b hb => (mem_filter.1 hb).2
      have h₂ := ih 1 (A := A) (B := B.filter fun b => ¬(args 0).eval interpretation b = false)
        (fun a ha => (hA' a ha).2) fun b hb => by
          obtain ⟨hb, h0⟩ := mem_filter.1 hb
          simpa [interpretation, Bool.not_eq_false _ ▸ h0] using hB b hb
      rw [← card_hammingEdges_filter_add_card_hammingEdges_filter_not
        (fun b => (args 0).eval interpretation b = false),
        ← card_filter_add_card_filter_not (s := B)
        (fun b => (args 0).eval interpretation b = false), Formula.leafSize_gate, sum_and]
      exact sq_add_le_mul h₁ h₂
    | or =>
      have hB' : ∀ b ∈ B, (args 0).eval interpretation b = false ∧
          (args 1).eval interpretation b = false := fun b hb => by
        simpa [interpretation] using hB b hb
      have h₁ := ih 0 (A := A.filter fun a => (args 0).eval interpretation a = true)
        (B := B) (fun a ha => (mem_filter.1 ha).2) fun b hb => (hB' b hb).1
      have h₂ := ih 1 (A := A.filter fun a => ¬(args 0).eval interpretation a = true)
        (B := B) (fun a ha => by
          obtain ⟨ha, h0⟩ := mem_filter.1 ha
          simpa [interpretation, Bool.not_eq_true _ ▸ h0] using hA a ha)
        fun b hb => (hB' b hb).2
      rw [card_hammingEdges_comm] at h₁ h₂ ⊢
      rw [← card_hammingEdges_filter_add_card_hammingEdges_filter_not
        (fun a => (args 0).eval interpretation a = true),
        ← card_filter_add_card_filter_not (s := A)
        (fun a => (args 0).eval interpretation a = true), Formula.leafSize_gate, sum_or]
      exact (sq_add_le_mul (h₁.trans_eq (mul_right_comm _ _ _))
        (h₂.trans_eq (mul_right_comm _ _ _))).trans_eq (mul_right_comm _ _ _)

/-- If every input of a nonempty `A` has at least `s₁` neighbors in `B` and every input of `B` has
at least `s₀` neighbors in `A`, a De Morgan formula that is true on `A` and false on `B` has leaf
size at least `s₀ s₁`. -/
theorem Formula.mul_le_leafSize (F : Formula signature n) {s₀ s₁ : ℕ}
    (hA : ∀ a ∈ A, F.eval interpretation a = true) (hB : ∀ b ∈ B, F.eval interpretation b = false)
    (hAne : A.Nonempty) (h₁ : ∀ a ∈ A, s₁ ≤ #{b ∈ B | hammingDist a b = 1})
    (h₀ : ∀ b ∈ B, s₀ ≤ #{a ∈ A | hammingDist b a = 1}) :
    s₀ * s₁ ≤ F.leafSize := by
  rcases B.eq_empty_or_nonempty with rfl | hBne
  · obtain ⟨a, ha⟩ := hAne
    have := h₁ a ha
    simp only [filter_empty, card_empty, Nat.le_zero] at this
    simp [this]
  have e₁ : #A • s₁ ≤ #(hammingEdges A B) := by
    rw [card_hammingEdges_eq_sum_card_filter]
    exact card_nsmul_le_sum _ _ _ h₁
  have e₀ : #B • s₀ ≤ #(hammingEdges A B) := by
    rw [card_hammingEdges_comm, card_hammingEdges_eq_sum_card_filter]
    exact card_nsmul_le_sum _ _ _ h₀
  rw [smul_eq_mul] at e₁ e₀
  have := F.sq_card_hammingEdges_le hA hB
  have hpos : 0 < #A * #B := Nat.mul_pos (card_pos.2 hAne) (card_pos.2 hBne)
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc s₀ * s₁ * (#A * #B) = (#B * s₀) * (#A * s₁) := by ring
    _ ≤ #(hammingEdges A B) * #(hammingEdges A B) := Nat.mul_le_mul e₀ e₁
    _ = #(hammingEdges A B) ^ 2 := (sq _).symm
    _ ≤ F.leafSize * #A * #B := this
    _ = F.leafSize * (#A * #B) := by ring

namespace Boolean

/-- Changing bits to new values at different positions gives different inputs. -/
private theorem injOn_update {a : BitString n} {s : Set (Fin n)} {v : Fin n → Bool}
    (hv : ∀ i ∈ s, v i ≠ a i) : s.InjOn fun i => update a i (v i) := fun i hi j _ h => by
  by_contra hij
  have := congrFun h i
  simp only [update_self, update_of_ne hij] at this
  exact hv i hi this

/-! ### Threshold functions -/

private theorem le_card_neighbors_weight_pred {k : ℕ} {a : BitString n}
    (ha : a ∈ BitString.weightLayer n k) :
    k ≤ #{b ∈ BitString.weightLayer n (k - 1) | hammingDist a b = 1} := by
  have ha' : BitString.weight a = k := BitString.mem_weightLayer.1 ha
  calc k = #(univ.filter fun j => a j = true) := ha'.symm
    _ ≤ _ := card_le_card_of_injOn (fun i => update a i false) (fun i hi => by
        have hai : a i = true := (mem_filter.1 hi).2
        simp only [coe_filter, BitString.mem_weightLayer, Set.mem_ofPred_eq]
        refine ⟨?_, hammingDist_update_of_ne (by simp [hai])⟩
        have := BitString.weight_update_false hai
        omega)
      (injOn_update fun i hi => by simp [(mem_filter.1 hi).2])

private theorem le_card_neighbors_weight_succ {k : ℕ} {b : BitString n}
    (hb : b ∈ BitString.weightLayer n k) :
    n - k ≤ #{a ∈ BitString.weightLayer n (k + 1) | hammingDist b a = 1} := by
  have hb' : BitString.weight b = k := BitString.mem_weightLayer.1 hb
  have hz : #(univ.filter fun j => ¬b j = true) = n - k := by
    have := BitString.weight_not b
    simp only [Fintype.card_fin, hb'] at this
    rw [← this, BitString.weight]
    simp
  calc n - k = #(univ.filter fun j => ¬b j = true) := hz.symm
    _ ≤ _ := card_le_card_of_injOn (fun i => update b i true) (fun i hi => by
        have hbi : b i = false := by simpa using (mem_filter.1 hi).2
        simp only [coe_filter, BitString.mem_weightLayer, Set.mem_ofPred_eq]
        refine ⟨?_, hammingDist_update_of_ne (by simp [hbi])⟩
        rw [BitString.weight_update_true hbi, hb'])
      (injOn_update fun i hi => by simpa using (mem_filter.1 hi).2)

/-- **Khrapchenko's bound for threshold functions.** A De Morgan formula computing "at least `k` of
the `n` bits are true" has leaf size at least `k (n + 1 - k)`. -/
theorem mul_le_leafSize_of_computes_threshold {k : ℕ} {F : Formula signature n}
    (hF : F.Computes interpretation (threshold n k)) : k * (n + 1 - k) ≤ F.leafSize := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rcases lt_or_ge n k with hkn | hkn
  · simp [show n + 1 - k = 0 by omega]
  rw [mul_comm, show n + 1 - k = n - (k - 1) by omega]
  refine F.mul_le_leafSize (A := BitString.weightLayer n k)
    (B := BitString.weightLayer n (k - 1))
    (fun a ha => (hF a).trans (by simp [threshold_apply, BitString.mem_weightLayer.1 ha]))
    (fun b hb => (hF b).trans (by
      simp only [threshold_apply, BitString.mem_weightLayer.1 hb, decide_eq_false_iff_not,
        not_le]
      omega))
    (BitString.weightLayer_nonempty hkn) (fun a ha => le_card_neighbors_weight_pred ha)
    fun b hb => ?_
  have := le_card_neighbors_weight_succ hb
  rwa [Nat.sub_add_cancel hk] at this

/-- One half of `⌊m ^ 2 / 4⌋ = ⌊m / 2⌋ ⌈m / 2⌉`. -/
private theorem sq_div_four_le (m : ℕ) : m ^ 2 / 4 ≤ m / 2 * (m - m / 2) := by
  rcases Nat.even_or_odd' m with ⟨t, rfl | rfl⟩
  · rw [show 2 * t / 2 = t by omega, show 2 * t - t = t by omega]
    exact Nat.div_le_of_le_mul (le_of_eq (by ring))
  · rw [show (2 * t + 1) / 2 = t by omega, show 2 * t + 1 - t = t + 1 by omega]
    exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by norm_num)).2 (by nlinarith))

/-- **Khrapchenko's bound for majority.** A De Morgan formula computing the majority of `n` bits
has leaf size at least `⌊(n + 1) ^ 2 / 4⌋ = ⌊(n + 1) / 2⌋ ⌈(n + 1) / 2⌉`. -/
theorem sq_div_four_le_leafSize_of_computes_majority {F : Formula signature n}
    (hF : F.Computes interpretation (majority n)) : (n + 1) ^ 2 / 4 ≤ F.leafSize :=
  (sq_div_four_le (n + 1)).trans (mul_le_leafSize_of_computes_threshold hF)

/-! ### Parity -/

/-- Every input has `n` neighbors of the other parity. -/
private theorem le_card_neighbors_parity (a : BitString n) {c : Bool} (hc : parity n a ≠ c) :
    n ≤ #{b ∈ (univ.filter fun b => parity n b = c) | hammingDist a b = 1} := by
  calc n = #(univ : Finset (Fin n)) := by simp
    _ ≤ _ := card_le_card_of_injOn (fun i => update a i !a i) (fun i _ => by
        simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq]
        refine ⟨?_, hammingDist_update_of_ne (by simp)⟩
        rw [parity, parityOn_update_not (mem_univ i)]
        cases h : parityOn univ a <;> cases c <;> simp_all [parity])
      (injOn_update fun i _ => by simp)

/-- **Khrapchenko's bound for parity.** A De Morgan formula computing the parity of `n` bits has
leaf size at least `n ^ 2`. -/
theorem sq_le_leafSize_of_computes_parity {F : Formula signature n}
    (hF : F.Computes interpretation (parity n)) : n ^ 2 ≤ F.leafSize := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hne : (univ.filter fun b : BitString n => parity n b = true).Nonempty := by
    by_contra h
    refine not_isConst_parityOn (s := (univ : Finset (Fin n))) ⟨⟨0, hn⟩, mem_univ _⟩ false
      fun x y => ?_
    have hx : parity n x = false := Bool.not_eq_true _ ▸ fun h' => h ⟨x, by simpa using h'⟩
    have hy : parity n y = false := Bool.not_eq_true _ ▸ fun h' => h ⟨y, by simpa using h'⟩
    simp only [Bool.false_xor]
    exact hx.trans hy.symm
  rw [sq]
  refine F.mul_le_leafSize (A := univ.filter fun b => parity n b = true)
    (B := univ.filter fun b => parity n b = false)
    (fun a ha => (hF a).trans (mem_filter.1 ha).2) (fun b hb => (hF b).trans (mem_filter.1 hb).2)
    hne (fun a ha => le_card_neighbors_parity a ?_) fun b hb => le_card_neighbors_parity b ?_
  · rw [(mem_filter.1 ha).2]
    decide
  · rw [(mem_filter.1 hb).2]
    decide

/-- A De Morgan formula computing the parity of `n` bits has depth at least `2 log₂ n`, counting
negations. -/
theorem two_mul_log_le_depth_of_computes_parity {F : Formula signature n}
    (hF : F.Computes interpretation (parity n)) : 2 * Nat.log 2 n ≤ F.depth := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hpow : 2 ^ (2 * Nat.log 2 n) ≤ 2 ^ F.depth :=
    calc 2 ^ (2 * Nat.log 2 n) = (2 ^ Nat.log 2 n) ^ 2 := by rw [mul_comm, pow_mul]
      _ ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn.ne') 2
      _ ≤ F.leafSize := sq_le_leafSize_of_computes_parity hF
      _ ≤ 2 ^ F.depth := F.leafSize_le_pow_depth Boolean.arity_le_two
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 hpow

/-! ### Formulas for parity -/

/-- The parity of the `a + b` consecutive bits from `o` on is the exclusive or of the parities of
the first `a` and the last `b` of them. -/
theorem parityOn_consecutive_add (o a b : ℕ) (x : BitString n) :
    parityOn ({i | o ≤ (i : ℕ) ∧ (i : ℕ) < o + (a + b)} : Finset (Fin n)) x =
      (parityOn ({i | o ≤ (i : ℕ) ∧ (i : ℕ) < o + a} : Finset (Fin n)) x ^^
        parityOn ({i | o + a ≤ (i : ℕ) ∧ (i : ℕ) < o + a + b} : Finset (Fin n)) x) := by
  have hsplit : ({i | o ≤ (i : ℕ) ∧ (i : ℕ) < o + (a + b)} : Finset (Fin n)) =
      ({i | o ≤ (i : ℕ) ∧ (i : ℕ) < o + a} : Finset (Fin n)) ∪
        ({i | o + a ≤ (i : ℕ) ∧ (i : ℕ) < o + a + b} : Finset (Fin n)) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_union]
    omega
  rw [hsplit, parityOn_union]
  rw [disjoint_left]
  intro i hi hi'
  simp only [mem_filter, mem_univ, true_and] at hi hi'
  omega

/-- The parity of the single bit `o` is that bit. -/
theorem parityOn_consecutive_one (o : ℕ) (h : o < n) (x : BitString n) :
    parityOn ({i | o ≤ (i : ℕ) ∧ (i : ℕ) < o + 1} : Finset (Fin n)) x = x ⟨o, h⟩ := by
  have : ({i | o ≤ (i : ℕ) ∧ (i : ℕ) < o + 1} : Finset (Fin n)) = insert ⟨o, h⟩ ∅ := by
    ext i
    simp only [mem_filter, mem_univ, true_and, insert_empty, mem_singleton, Fin.ext_iff]
    omega
  rw [this, parityOn_insert (notMem_empty _), parityOn_empty, Bool.xor_false]

/-- A De Morgan formula for the parity of the `2 ^ k` bits from `o` on, of leaf size `4 ^ k`. -/
def parityFormula : (k o : ℕ) → o + 2 ^ k ≤ n → Formula signature n
  | 0, o, h => .input ⟨o, by rw [pow_zero] at h; omega⟩
  | k + 1, o, h =>
    (parityFormula k o (by rw [pow_succ] at h; omega)).xor
      (parityFormula k (o + 2 ^ k) (by rw [pow_succ] at h; omega))

/-- The formula `parityFormula k o` computes the parity of the `2 ^ k` bits from `o` on. -/
theorem eval_parityFormula (k o : ℕ) (h : o + 2 ^ k ≤ n) (x : BitString n) :
    (parityFormula k o h).eval interpretation x =
      parityOn ({i | o ≤ (i : ℕ) ∧ (i : ℕ) < o + 2 ^ k} : Finset (Fin n)) x := by
  induction k generalizing o with
  | zero =>
    rw [pow_zero, parityOn_consecutive_one o (by rw [pow_zero] at h; omega)]
    rfl
  | succ k ih =>
    rw [parityFormula, Formula.eval_xor, ih, ih, ← parityOn_consecutive_add]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, pow_succ]
    omega

/-- The formula `parityFormula k o` has leaf size `4 ^ k`. -/
private theorem leafSize_parityFormula (k o : ℕ) (h : o + 2 ^ k ≤ n) :
    (parityFormula k o h).leafSize = 4 ^ k := by
  induction k generalizing o with
  | zero => rfl
  | succ k ih =>
    rw [parityFormula, Formula.leafSize_xor, ih, ih, pow_succ]
    ring

/-- **Khrapchenko's bound is tight for parity**: the parity of `2 ^ k` bits has a De Morgan formula
of leaf size `(2 ^ k) ^ 2`. -/
theorem exists_formula_parity_two_pow (k : ℕ) :
    ∃ F : Formula signature (2 ^ k), F.Computes interpretation (parity (2 ^ k)) ∧
      F.leafSize = (2 ^ k) ^ 2 := by
  refine ⟨parityFormula k 0 (by simp), fun x => ?_, ?_⟩
  · rw [eval_parityFormula]
    congr 1
    ext i
    simp
  · rw [leafSize_parityFormula, ← pow_mul, mul_comm, pow_mul]
    norm_num

/-- The least leaf size of a De Morgan formula for the parity of `2 ^ k` bits is `(2 ^ k) ^ 2`. -/
theorem isLeast_leafSize_parity_two_pow (k : ℕ) :
    IsLeast {L | ∃ F : Formula signature (2 ^ k),
      F.Computes interpretation (parity (2 ^ k)) ∧ F.leafSize = L} ((2 ^ k) ^ 2) :=
  ⟨exists_formula_parity_two_pow k, fun _ ⟨_, hF, hL⟩ => hL ▸ sq_le_leafSize_of_computes_parity hF⟩

end Boolean

end Cslib.Circuits
