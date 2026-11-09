/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Spira's theorem: balancing formulas

**Spira's theorem** [Spira1971], [Jukna, Chapter 6][Jukna2012]: every De Morgan formula with
`L` leaves has an equivalent formula with at most `4 ⌈log₂ L⌉` AND and OR gates on every path
(`Boolean.exists_formula_depthWith_le_four_mul_clog`). Conversely a formula with at most `d` AND
and OR gates on every path has at most `2 ^ d` leaves
(`Boolean.leafSize_le_two_pow_depthWith_binaryCost`). So the formula depth of a function is at most
four times the logarithm of the leaf size of any formula for it
(`Boolean.formulaDepth_le_four_mul_clog`), and some formula for it has at most `2` to the formula
depth leaves (`Boolean.exists_computes_leafSize_le_two_pow_formulaDepth`).

The proof splits a formula `F` with `L` leaves at a subformula `G` with between `L / 3` and
`2 L / 3` leaves, found by walking from the root towards the argument with the most leaves
(`Formula.exists_split`, for any basis of fan-in at most two). Then
`F ≡ (G ∧ F[G := 1]) ∨ (¬G ∧ F[G := 0])`, where each of the three formulas has at most `2 L / 3`
leaves and is balanced recursively, at the cost of two AND and OR gates per level.

## Main results

* `Cslib.Circuits.Formula.exists_split`: a subformula with between a third and two thirds of the
  leaves, and its context.
* `Cslib.Circuits.Boolean.exists_formula_depthWith_le_four_mul_clog`: Spira's theorem.
* `Cslib.Circuits.Boolean.leafSize_le_two_pow_depthWith_binaryCost`: the converse bound.
* `Cslib.Circuits.Boolean.formulaDepth_le_four_mul_clog`,
  `Cslib.Circuits.Boolean.exists_computes_leafSize_le_two_pow_formulaDepth`: formula depth and the
  logarithm of formula leaf size agree up to a factor of four.

## References

* [P. M. Spira, *On time-hardware complexity tradeoffs for Boolean functions*][Spira1971]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

namespace Formula

open Finset

variable {n : ℕ}

section Split

variable {σ : Signature}

/-- **A balanced split.** In a formula over a basis of fan-in at most two with more than `2 L / 3`
leaves, for `L ≥ 2`, walking towards the argument with the most leaves reaches a subformula `G`
with more than `L / 3` and at most `2 L / 3` leaves. The rest of the formula is a context `C`
with one hole, its last input: plugging `G` into `C` gives back the formula, and plugging a
formula `K` into `C` replaces the leaves of `G` by those of `K`. -/
theorem exists_split (hσ : ∀ op, σ.Arity op ≤ 2) {L : ℕ} (hL : 2 ≤ L) (H : Formula σ n)
    (hH : 2 * L < 3 * H.leafSize) :
    ∃ (G : Formula σ n) (C : Formula σ (n + 1)), C.substLast G = H ∧
      L < 3 * G.leafSize ∧ 3 * G.leafSize ≤ 2 * L ∧
      ∀ K, (C.substLast K).leafSize + G.leafSize = H.leafSize + K.leafSize := by
  induction H with
  | input i =>
    simp only [leafSize_input] at hH
    omega
  | gate op args ih =>
    rw [leafSize_gate] at hH
    have hne : (univ : Finset (Fin (σ.Arity op))).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty.1 h, sum_empty] at hH
      omega
    -- the argument with the most leaves has at least half of them
    obtain ⟨a, -, ha⟩ := exists_max_image univ (fun j => (args j).leafSize) hne
    have hhalf : ∑ j, (args j).leafSize ≤ 2 * (args a).leafSize :=
      (sum_le_card_nsmul univ _ _ fun j _ => ha j (mem_univ j)).trans (by
        rw [card_univ, Fintype.card_fin, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (hσ op))
    -- stop at it, or keep walking
    obtain ⟨G, C, hC, h₁, h₂, hls⟩ : ∃ (G : Formula σ n) (C : Formula σ (n + 1)),
        C.substLast G = args a ∧ L < 3 * G.leafSize ∧ 3 * G.leafSize ≤ 2 * L ∧
        ∀ K, (C.substLast K).leafSize + G.leafSize = (args a).leafSize + K.leafSize := by
      by_cases hA : 2 * L < 3 * (args a).leafSize
      · exact ih a hA
      · exact ⟨args a, input (Fin.last n), input_last_substLast _, by omega, by omega,
          fun K => by rw [input_last_substLast, add_comm]⟩
    refine ⟨G, gate op (Function.update (fun j => (args j).lift) a C), ?_, h₁, h₂, fun K => ?_⟩
    · rw [gate_substLast]
      congr 1 with j : 1
      by_cases hj : j = a
      · subst hj
        simpa using hC
      · simp [Function.update_of_ne hj]
    · have hsum : (fun j => ((Function.update (fun j => (args j).lift) a C j).substLast
            K).leafSize) =
          Function.update (fun j => (args j).leafSize) a (C.substLast K).leafSize := by
        funext j
        by_cases hj : j = a
        · subst hj
          simp
        · simp [Function.update_of_ne hj]
      rw [gate_substLast, leafSize_gate, leafSize_gate, hsum, sum_update_of_mem (mem_univ a),
        sum_eq_add_sum_sdiff_singleton_of_mem (mem_univ a) fun j => (args j).leafSize]
      have := hls K
      omega

end Split

end Formula

namespace Boolean

open Finset Formula

variable {n : ℕ}

/-- `G` followed by the one-bit function `g`, without adding AND or OR gates: a constant, `G`, or
its negation. -/
private def postcomp (G : Formula signature n) (g : Bool → Bool) : Formula signature n :=
  if g false = g true then const (g false) else if g true then G else G.not

private theorem eval_postcomp (G : Formula signature n) (g : Bool → Bool) (x : BitString n) :
    (postcomp G g).eval interpretation x = g (G.eval interpretation x) := by
  cases h₀ : g false <;> cases h₁ : g true <;> cases hG : G.eval interpretation x <;>
    simp [postcomp, h₀, h₁, hG]

private theorem depthWith_postcomp_le (G : Formula signature n) (g : Bool → Bool) :
    (postcomp G g).depthWith binaryCost ≤ G.depthWith binaryCost := by
  unfold postcomp
  split_ifs <;> simp

/-- A formula with at most one leaf has an equivalent formula without AND or OR gates. -/
private theorem exists_depthWith_eq_zero (F : Formula signature n) (hF : F.leafSize ≤ 1) :
    ∃ G : Formula signature n, (∀ x, G.eval interpretation x = F.eval interpretation x) ∧
      G.depthWith binaryCost = 0 := by
  induction F with
  | input i => exact ⟨input i, fun _ => rfl, rfl⟩
  | gate op args ih =>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hF with h₀ | h₁
    · exact ⟨const ((gate op args).eval interpretation fun _ => false),
        fun x => eval_eq_of_leafSize_eq_zero h₀ interpretation (fun _ => false) x, by simp⟩
    -- one argument has the leaf, and the others compute constants
    rw [leafSize_gate] at h₁
    obtain ⟨b, -, hb⟩ := exists_ne_zero_of_sum_ne_zero (h₁ ▸ one_ne_zero)
    rw [sum_eq_add_sum_sdiff_singleton_of_mem (mem_univ b)] at h₁
    have hrest' : ∑ j ∈ univ \ {b}, (args j).leafSize = 0 := by omega
    have hrest : ∀ j ≠ b, (args j).leafSize = 0 := fun j hj =>
      sum_eq_zero_iff.1 hrest' j (by simp [hj])
    obtain ⟨G, hG, hd⟩ := ih b (by omega)
    refine ⟨postcomp G fun v => interpretation op
      (Function.update (fun j => (args j).eval interpretation fun _ => false) b v),
      fun x => ?_, Nat.le_zero.1 ((depthWith_postcomp_le _ _).trans hd.le)⟩
    rw [eval_postcomp, hG, eval_gate]
    congr 1 with j : 1
    by_cases hj : j = b
    · subst hj
      simp
    · rw [Function.update_of_ne hj]
      exact eval_eq_of_leafSize_eq_zero (hrest j hj) interpretation _ x

/-- Balancing with `2 k` levels of AND and OR gates when `L ≤ (3 / 2) ^ k`. -/
private theorem exists_depthWith_le_two_mul (k : ℕ) (F : Formula signature n)
    (hF : 2 ^ k * F.leafSize ≤ 3 ^ k) :
    ∃ G : Formula signature n, (∀ x, G.eval interpretation x = F.eval interpretation x) ∧
      G.depthWith binaryCost ≤ 2 * k := by
  induction k generalizing F with
  | zero =>
    obtain ⟨G, hG, hd⟩ := exists_depthWith_eq_zero F (by simpa using hF)
    exact ⟨G, hG, hd.le⟩
  | succ k ih =>
    by_cases hL : F.leafSize ≤ 1
    · obtain ⟨G, hG, hd⟩ := exists_depthWith_eq_zero F hL
      exact ⟨G, hG, by omega⟩
    obtain ⟨G, C, hC, h₁, h₂, hls⟩ := exists_split Boolean.arity_le_two
      (L := F.leafSize) (by omega) F (by omega)
    -- a third of the leaves less is small enough for `k`
    have shrink : ∀ m, 3 * m ≤ 2 * F.leafSize → 2 ^ k * m ≤ 3 ^ k := fun m hm => by
      refine Nat.le_of_mul_le_mul_left (?_ : 3 * (2 ^ k * m) ≤ 3 * 3 ^ k) (by decide)
      calc 3 * (2 ^ k * m) = 2 ^ k * (3 * m) := by ring
        _ ≤ 2 ^ k * (2 * F.leafSize) := Nat.mul_le_mul_left _ hm
        _ = 2 ^ (k + 1) * F.leafSize := by ring
        _ ≤ 3 ^ (k + 1) := hF
        _ = 3 * 3 ^ k := by ring
    have hfill (c : Bool) : 2 ^ k * (C.substLast (const c)).leafSize ≤ 3 ^ k :=
      shrink _ (by have := hls (const c); simp only [leafSize_const] at this; omega)
    obtain ⟨G', hG', hGd⟩ := ih G (shrink _ h₂)
    obtain ⟨C₁, hC₁, hC₁d⟩ := ih _ (hfill true)
    obtain ⟨C₀, hC₀, hC₀d⟩ := ih _ (hfill false)
    refine ⟨(G'.and C₁).or (G'.not.and C₀), fun x => ?_, ?_⟩
    · rw [← hC]
      simp only [eval_or, eval_and, eval_not, hG', hC₁, hC₀, eval_substLast, eval_const]
      cases G.eval interpretation x <;> simp
    · simp only [depthWith_or, depthWith_and, depthWith_not, binaryCost_and, binaryCost_or,
        binaryCost_not]
      omega

/-- **Spira's theorem.** Every De Morgan formula with `L` leaves has an equivalent formula with at
most `4 ⌈log₂ L⌉` AND and OR gates on every path. -/
theorem exists_formula_depthWith_le_four_mul_clog (F : Formula signature n) :
    ∃ G : Formula signature n, (∀ x, G.eval interpretation x = F.eval interpretation x) ∧
      G.depthWith binaryCost ≤ 4 * Nat.clog 2 F.leafSize := by
  set j := Nat.clog 2 F.leafSize
  obtain ⟨G, hG, hd⟩ := exists_depthWith_le_two_mul (2 * j) F (by
    calc 2 ^ (2 * j) * F.leafSize ≤ 2 ^ (2 * j) * 2 ^ j :=
          Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) _)
      _ = 8 ^ j := by rw [← pow_add, show 2 * j + j = 3 * j by ring, pow_mul]; rfl
      _ ≤ 9 ^ j := Nat.pow_le_pow_left (by decide) j
      _ = 3 ^ (2 * j) := by rw [pow_mul]; rfl)
  exact ⟨G, hG, hd.trans (by omega)⟩

/-- A De Morgan formula with at most `d` AND and OR gates on every path has at most `2 ^ d`
leaves. -/
theorem leafSize_le_two_pow_depthWith_binaryCost (F : Formula signature n) :
    F.leafSize ≤ 2 ^ F.depthWith binaryCost := by
  induction F with
  | input i => simp
  | gate op args ih =>
    have hle (j : Fin (signature.Arity op)) :
        (args j).leafSize ≤ 2 ^ (univ.sup fun j => (args j).depthWith binaryCost) :=
      (ih j).trans (Nat.pow_le_pow_right (by decide)
        (le_sup (f := fun j => (args j).depthWith binaryCost) (mem_univ j)))
    rw [leafSize_gate, depthWith_gate]
    cases op with
    | const c => simp
    | not => simpa using hle 0
    | and | or =>
      simp only [binaryCost_and, binaryCost_or]
      rw [Fin.sum_univ_two, pow_succ, mul_two]
      exact Nat.add_le_add (hle _) (hle _)

/-- The formula depth of a function is at most `4 ⌈log₂ L⌉` for every formula with `L` leaves
computing it. -/
theorem formulaDepth_le_four_mul_clog {f : BooleanFunction n} {F : Formula signature n}
    (hF : F.Computes interpretation f) : formulaDepth f ≤ 4 * Nat.clog 2 F.leafSize := by
  obtain ⟨G, hG, hd⟩ := exists_formula_depthWith_le_four_mul_clog F
  exact (formulaDepth_le fun x => (hG x).trans (hF x)).trans hd

/-- Conversely, some formula for a function has at most `2 ^ d` leaves, where `d` is its formula
depth. -/
theorem exists_computes_leafSize_le_two_pow_formulaDepth (f : BooleanFunction n) :
    ∃ F : Formula signature n, F.Computes interpretation f ∧ F.leafSize ≤ 2 ^ formulaDepth f := by
  obtain ⟨F, hF, hd⟩ := exists_computes_depthWith_eq_formulaDepth f
  exact ⟨F, hF, hd ▸ leafSize_le_two_pow_depthWith_binaryCost F⟩

end Boolean

end Cslib.Circuits
