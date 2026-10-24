/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PP
public import Complexity.Computability.Complexity.Classes.PP.Closure
public import Complexity.Computability.Complexity.Classes.SharpP
public import Complexity.Computability.Complexity.Reduction.TruthTable
public import Complexity.Foundations.Order.BooleanSubalgebra
import Complexity.Computability.Complexity.Classes.PP.Characterization
import Complexity.Computability.Complexity.Classes.SharpP.Products
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Cslib.Foundations.Data.Polynomial.Monotone
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity

/-!
# Closure of PP under polynomial-time truth-table reductions

`PP` is closed under polynomial-time truth-table reductions
[Fortnow and Reingold][FortnowReingold1996], generalizing the theorem of Beigel, Reingold and
Spielman that `PP` is closed under Boolean operations
[Beigel, Reingold and Spielman][BeigelReingoldSpielman1995].

Given an indexed language `A ∈ PP (encPair enc encUnary)`, a polynomial-time unary query count `r`,
and a polynomial-time Boolean combiner `d`, let `g₀ ∈ GapP (encPair enc encUnary)` witness `A` via
`0 < g₀ x ↔ x ∈ A`, and set `g x = 2 * g₀ x - 1`. Then `g x` is never zero, has the sign of
membership in `A`, and satisfies `|g (a, i)| ≤ 2 ^ M a` for all `i < r a` for a polynomial-time
unary bound `M a`. Evaluating Newman's polynomial [Newman][Newman1964]
$$\operatorname{newmanPoly}(M, z) = \prod_{j=0}^{M} (2^j + z)$$
and raising to the even exponent `2 * (r a + 1)` yields nonnegative `GapP` weights
`A⁺ (a, i)` and `A⁻ (a, i)` such that at each query `i < r a`, the weight matching the true
membership answer `decide ((a, i) ∈ A)` is at least `1` and exceeds the opposite weight by a factor
of at least `2 ^ (2 * (r a + 1))`. Multiplying the selected weights across `i ∈ range (r a)` for
each guessed answer word `w : Fin (r a) → Bool` makes the weight of the true answer word
`truthTableAnswers A r a` strictly exceed the sum of the weights of all `2 ^ (r a) - 1` incorrect
words. Summing `(if d (a, List.ofFn w) then 1 else -1)` times the word weight over all `w` via
`GapP.sum_bits_mem` produces a `GapP` function whose sign is determined by the single term for
`truthTableAnswers A r a`.

## Main definitions

* `Cslib.Complexity.newmanPoly`: Newman's integer polynomial `∏ j ∈ range (M + 1), (2 ^ j + z)`
  [Newman][Newman1964].

## Main results

* `Cslib.Complexity.truthTable_mem_PP`: `PP` is closed under polynomial-time Boolean combinations
  of a polynomial-time unary batch of queries to an indexed `PP` family.
* `Cslib.Complexity.PolyTimeTruthTableReducible.mem_PP`: `PP` is closed under polynomial-time
  truth-table reductions [Fortnow and Reingold][FortnowReingold1996].
* `Cslib.Complexity.forall_lt_mem_PP`, `Cslib.Complexity.exists_lt_mem_PP`: `PP` is closed under
  polynomial-time bounded universal and existential quantifiers.
* `Cslib.Complexity.inter_mem_PP`, `Cslib.Complexity.union_mem_PP`,
  `Cslib.Complexity.diff_mem_PP`, `Cslib.Complexity.symmDiff_mem_PP`: `PP` is closed under finite
  Boolean operations [Beigel, Reingold and Spielman][BeigelReingoldSpielman1995].

## References

* [R. Beigel, N. Reingold, D. Spielman,
  *PP is closed under intersection*][BeigelReingoldSpielman1995]
* [L. Fortnow, N. Reingold, *PP is closed under truth-table reductions*][FortnowReingold1996]
* [D. J. Newman, *Rational approximation to |x|*][Newman1964]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Finset

variable {α : Type} {enc : α ↪ List Bool}

/-! ### Newman's polynomial and amplified weights -/

/-- Newman's polynomial `∏ j ∈ range (M + 1), (2 ^ j + z)` [Newman][Newman1964], used to
rationalize the sign of an integer `z` with `1 ≤ |z| ≤ 2 ^ M`. -/
def newmanPoly (M : ℕ) (z : ℤ) : ℤ :=
  ∏ j ∈ range (M + 1), ((2 : ℤ) ^ j + z)

/-- Even-power amplification of `newmanPoly`, ensuring nonnegativity and a multiplicative dominance
ratio of at least `2 ^ (2 * K)`. -/
private def newmanAmp (M K : ℕ) (z : ℤ) : ℤ :=
  newmanPoly M z ^ (2 * K)

private theorem exists_two_pow_interval {M : ℕ} {z : ℤ} (hz₁ : 1 ≤ z) (hz₂ : z ≤ (2 : ℤ) ^ M) :
    ∃ k ∈ range (M + 1), (2 : ℤ) ^ k ≤ z ∧ z ≤ 2 * (2 : ℤ) ^ k := by
  induction M with
  | zero =>
    exact ⟨0, mem_range.mpr (by omega), by simpa using hz₁, by simpa using hz₂.trans (by omega)⟩
  | succ M ih =>
    by_cases hle : z ≤ (2 : ℤ) ^ M
    · obtain ⟨k, hk, hk₁, hk₂⟩ := ih hle
      exact ⟨k, mem_range.mpr (Nat.lt_succ_of_lt (mem_range.mp hk)), hk₁, hk₂⟩
    · refine ⟨M, mem_range.mpr (by omega), by omega, ?_⟩
      simpa [pow_succ'] using hz₂

/-- Newman's polynomial is at least `1` at every positive integer. -/
private theorem one_le_newmanPoly {M : ℕ} {z : ℤ} (hz : 1 ≤ z) : 1 ≤ newmanPoly M z :=
  one_le_prod₀ fun j _ => by
    have : (0 : ℤ) ≤ (2 : ℤ) ^ j := by positivity
    omega

/-- **Newman's inequality:** for `1 ≤ z ≤ 2 ^ M`, twice `|newmanPoly M (-z)|` is at most
`newmanPoly M z`. -/
theorem two_mul_abs_newmanPoly_neg_le {M : ℕ} {z : ℤ} (hz₁ : 1 ≤ z) (hz₂ : z ≤ (2 : ℤ) ^ M) :
    2 * |newmanPoly M (-z)| ≤ newmanPoly M z := by
  obtain ⟨k, hk, hk₁, hk₂⟩ := exists_two_pow_interval hz₁ hz₂
  unfold newmanPoly
  rw [← mul_prod_erase (range (M + 1)) (fun j => (2 : ℤ) ^ j + -z) hk,
    ← mul_prod_erase (range (M + 1)) (fun j => (2 : ℤ) ^ j + z) hk,
    abs_mul, ← mul_assoc]
  have hhead : 2 * |(2 : ℤ) ^ k + -z| ≤ (2 : ℤ) ^ k + z := by
    rcases abs_cases ((2 : ℤ) ^ k + -z) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have htail : |∏ x ∈ (range (M + 1)).erase k, ((2 : ℤ) ^ x + -z)| ≤
      ∏ x ∈ (range (M + 1)).erase k, ((2 : ℤ) ^ x + z) := by
    rw [abs_prod]
    refine prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => ?_
    have : (0 : ℤ) ≤ (2 : ℤ) ^ j := by positivity
    rcases abs_cases ((2 : ℤ) ^ j + -z) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  exact mul_le_mul hhead htail (abs_nonneg _) (by omega)

/-- The amplified weight is nonnegative, being an even power. -/
private theorem newmanAmp_nonneg (M K : ℕ) (z : ℤ) : 0 ≤ newmanAmp M K z :=
  Even.pow_nonneg (even_two_mul K) _

/-- The amplified weight is at least `1` at every positive integer. -/
private theorem one_le_newmanAmp {M K : ℕ} {z : ℤ} (hz : 1 ≤ z) : 1 ≤ newmanAmp M K z :=
  one_le_pow₀ (one_le_newmanPoly hz)

/-- For `1 ≤ z ≤ 2 ^ M`, the amplified weight at `z` exceeds the weight at `-z` by a factor of
at least `2 ^ (2 * K)`. -/
private theorem two_pow_mul_newmanAmp_neg_le {M K : ℕ} {z : ℤ} (hz₁ : 1 ≤ z)
    (hz₂ : z ≤ (2 : ℤ) ^ M) :
    (2 : ℤ) ^ (2 * K) * newmanAmp M K (-z) ≤ newmanAmp M K z := by
  unfold newmanAmp
  rw [← Even.pow_abs (even_two_mul K) (newmanPoly M (-z)), ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (two_mul_abs_newmanPoly_neg_le hz₁ hz₂) (2 * K)

private theorem newmanAmp_mem_GapP {M r : α → ℕ} {h : α × ℕ → ℤ}
    (hh : h ∈ GapP (encPair enc encUnary))
    (hM : ComputableTidilyInPolyTime M enc encUnary)
    (hr : ComputableTidilyInPolyTime r enc encUnary) :
    (fun x : α × ℕ => newmanAmp (M x.1) (r x.1 + 1) (h x)) ∈ GapP (encPair enc encUnary) := by
  have htwo : (fun _ : (α × ℕ) × ℕ => (2 : ℤ)) ∈
      GapP (encPair (encPair enc encUnary) encUnary) :=
    GapP.add_mem GapP.one_mem GapP.one_mem
  have hpow2 : (fun p : (α × ℕ) × ℕ => (2 : ℤ) ^ p.2) ∈
      GapP (encPair (encPair enc encUnary) encUnary) :=
    GapP.pow_mem_polyTime htwo (.of_tidy (.snd (encPair enc encUnary) encUnary))
  have hbody : (fun p : (α × ℕ) × ℕ => (2 : ℤ) ^ p.2 + h p.1) ∈
      GapP (encPair (encPair enc encUnary) encUnary) :=
    GapP.add_mem hpow2 (GapP.comp_mem hh (.of_tidy (.fst (encPair enc encUnary) encUnary)))
  have hprod : (fun x : α × ℕ => newmanPoly (M x.1) (h x)) ∈ GapP (encPair enc encUnary) :=
    GapP.prod_range_mem hbody (.of_tidy (by fun_prop))
  exact GapP.pow_mem_polyTime hprod (.of_tidy (by fun_prop))

/-! ### Word weights and truth-table gap construction -/

private def ppWordWeight (M r : α → ℕ) (g : α × ℕ → ℤ) (a : α) (w : Fin (r a) → Bool) : ℤ :=
  ∏ i ∈ range (r a),
    if (List.ofFn w).getD i false then
      newmanAmp (M a) (r a + 1) (g (a, i))
    else
      newmanAmp (M a) (r a + 1) (-g (a, i))

private def ppTruthTableGap (M r : α → ℕ) (g : α × ℕ → ℤ) (d : α × List Bool → Bool) (a : α) : ℤ :=
  ∑ w : Fin (r a) → Bool, (if d (a, List.ofFn w) then 1 else -1) * ppWordWeight M r g a w

private theorem ppTruthTableGap_mem {M r : α → ℕ} {g : α × ℕ → ℤ} {d : α × List Bool → Bool}
    (hg : g ∈ GapP (encPair enc encUnary))
    (hM : ComputableTidilyInPolyTime M enc encUnary)
    (hr : ComputableTidilyInPolyTime r enc encUnary)
    (hd : ComputableTidilyInPolyTime d (encPair enc encBits) encBool) :
    ppTruthTableGap M r g d ∈ GapP enc := by
  let q : (α × List Bool) × ℕ → α × ℕ := fun x => (x.1.1, x.2)
  have hq : ComputableTidilyInPolyTime q
      (encPair (encPair enc encBits) encUnary) (encPair enc encUnary) := by dsimp [q]; fun_prop
  have hpos := newmanAmp_mem_GapP hg hM hr
  have hneg := newmanAmp_mem_GapP (GapP.neg_mem hg) hM hr
  have hs : (fun x : (α × List Bool) × ℕ =>
      if x.1.2.getD x.2 false then
        newmanAmp (M x.1.1) (r x.1.1 + 1) (g (x.1.1, x.2))
      else
        newmanAmp (M x.1.1) (r x.1.1 + 1) (-g (x.1.1, x.2))) ∈
      GapP (encPair (encPair enc encBits) encUnary) :=
    GapP.ite_mem (.of_tidy (by fun_prop)) (GapP.comp_mem hpos (.of_tidy hq))
      (GapP.comp_mem hneg (.of_tidy hq))
  have hp := GapP.prod_range_mem hs (.of_tidy (hr.comp (.fst enc encBits)))
  have hw : ComputableTidilyInPolyTime
      (fun x => if d x then (1 : ℤ) else -1) (encPair enc encBits) encIntBin := by fun_prop
  exact GapP.sum_bits_mem (GapP.mul_mem (mem_GapP_of_polyTime (.of_tidy hw)) hp) (.of_tidy hr)

private theorem ppWordWeight_eq_prod_univ (M r : α → ℕ) (g : α × ℕ → ℤ) (a : α)
    (w : Fin (r a) → Bool) :
    ppWordWeight M r g a w =
      ∏ i : Fin (r a),
        if w i then newmanAmp (M a) (r a + 1) (g (a, i.1))
        else newmanAmp (M a) (r a + 1) (-g (a, i.1)) := by
  unfold ppWordWeight
  rw [← Fin.prod_univ_eq_prod_range]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left, Fin.isLt,
    Option.getD_some]

private theorem ppWordWeight_nonneg (M r : α → ℕ) (g : α × ℕ → ℤ) (a : α)
    (w : Fin (r a) → Bool) : 0 ≤ ppWordWeight M r g a w := by
  rw [ppWordWeight_eq_prod_univ]
  refine prod_nonneg fun i _ => ?_
  split_ifs <;> exact newmanAmp_nonneg _ _ _

private theorem sum_erase_ppWordWeight_lt {A : Set (α × ℕ)} {M r : α → ℕ} {g : α × ℕ → ℤ}
    {a : α}
    (hpos : ∀ i < r a, (a, i) ∈ A → 1 ≤ g (a, i))
    (hneg : ∀ i < r a, (a, i) ∉ A → 1 ≤ -g (a, i))
    (hbnd : ∀ i < r a, |g (a, i)| ≤ (2 : ℤ) ^ M a) :
    letI := Classical.decPred (· ∈ A)
    let v : Fin (r a) → Bool := fun i => decide ((a, i.1) ∈ A)
    ∑ w ∈ univ.erase v, ppWordWeight M r g a w < ppWordWeight M r g a v := by
  classical
  intro v
  let factor (w : Fin (r a) → Bool) (i : Fin (r a)) : ℤ :=
    if w i then newmanAmp (M a) (r a + 1) (g (a, i.1))
    else newmanAmp (M a) (r a + 1) (-g (a, i.1))
  have hfactor_nonneg (w : Fin (r a) → Bool) (i : Fin (r a)) : 0 ≤ factor w i := by
    dsimp [factor]
    split_ifs <;> exact newmanAmp_nonneg _ _ _
  have hfactor_v_pos (i : Fin (r a)) : 1 ≤ factor v i := by
    dsimp [factor, v]
    by_cases hi : (a, i.1) ∈ A
    · simp only [decide_eq_true hi, ↓reduceIte]
      exact one_le_newmanAmp (hpos i.1 i.2 hi)
    · simp only [decide_eq_false hi, Bool.false_eq_true, ↓reduceIte]
      exact one_le_newmanAmp (hneg i.1 i.2 hi)
  have hfactor_mismatch (w : Fin (r a) → Bool) (i : Fin (r a)) (hne : w i ≠ v i) :
      (2 : ℤ) ^ (2 * (r a + 1)) * factor w i ≤ factor v i := by
    have habs := abs_le.mp (hbnd i.1 i.2)
    dsimp [factor, v] at hne ⊢
    by_cases hi : (a, i.1) ∈ A
    · have hw : w i = false := by simpa [hi] using hne
      simp only [hw, Bool.false_eq_true, ↓reduceIte, decide_eq_true hi]
      exact two_pow_mul_newmanAmp_neg_le (hpos i.1 i.2 hi) habs.2
    · have hw : w i = true := by simpa [hi] using hne
      simp only [hw, ↓reduceIte, decide_eq_false hi, Bool.false_eq_true]
      simpa only [neg_neg] using two_pow_mul_newmanAmp_neg_le (hneg i.1 i.2 hi) (by omega)
  have hfactor_le (w : Fin (r a) → Bool) (i : Fin (r a)) : factor w i ≤ factor v i := by
    by_cases h : w i = v i
    · dsimp [factor]; rw [h]
    · have hpow : (1 : ℤ) ≤ (2 : ℤ) ^ (2 * (r a + 1)) := one_le_pow₀ (by omega)
      exact (le_mul_of_one_le_left (hfactor_nonneg w i) hpow).trans (hfactor_mismatch w i h)
  have hPv_pos : 1 ≤ ppWordWeight M r g a v := by
    rw [ppWordWeight_eq_prod_univ]
    exact one_le_prod₀ fun i _ => hfactor_v_pos i
  have hdom (w : Fin (r a) → Bool) (hw : w ∈ univ.erase v) :
      2 * (2 : ℤ) ^ r a * ppWordWeight M r g a w ≤ ppWordWeight M r g a v := by
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, w i₀ ≠ v i₀ := Function.ne_iff.mp (mem_erase.mp hw).1
    have hpow_le : 2 * (2 : ℤ) ^ r a ≤ (2 : ℤ) ^ (2 * (r a + 1)) := by
      rw [show (2 : ℤ) * (2 : ℤ) ^ r a = (2 : ℤ) ^ (r a + 1) by ring]
      exact pow_le_pow_right₀ (by omega) (by omega)
    have hprod_dom : (2 : ℤ) ^ (2 * (r a + 1)) * ppWordWeight M r g a w ≤
        ppWordWeight M r g a v := by
      rw [ppWordWeight_eq_prod_univ, ppWordWeight_eq_prod_univ]
      change (2 : ℤ) ^ (2 * (r a + 1)) * ∏ i : Fin (r a), factor w i ≤
        ∏ i : Fin (r a), factor v i
      rw [← mul_prod_erase univ (factor w) (mem_univ i₀),
        ← mul_prod_erase univ (factor v) (mem_univ i₀), ← mul_assoc]
      exact mul_le_mul (hfactor_mismatch w i₀ hi₀)
        (prod_le_prod₀ (fun i _ => hfactor_nonneg w i) (fun i _ => hfactor_le w i))
        (prod_nonneg fun i _ => hfactor_nonneg w i)
        (by have := hfactor_v_pos i₀; omega)
    exact (mul_le_mul_of_nonneg_right hpow_le (ppWordWeight_nonneg M r g a w)).trans hprod_dom
  have hsum_le : 2 * (2 : ℤ) ^ r a * ∑ w ∈ univ.erase v, ppWordWeight M r g a w ≤
      (2 : ℤ) ^ r a * ppWordWeight M r g a v := by
    rw [mul_sum]
    refine (sum_le_sum hdom).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have hcard : ((univ.erase v).card : ℤ) ≤ (2 : ℤ) ^ r a := by
      have hc : (univ.erase v).card ≤ 2 ^ r a := by simp
      exact_mod_cast hc
    exact mul_le_mul_of_nonneg_right hcard (by omega)
  have h2pow_pos : (0 : ℤ) < (2 : ℤ) ^ r a := by positivity
  nlinarith

/-! ### Main theorems -/

variable {A : Set (α × ℕ)} {r : α → ℕ} {d : α × List Bool → Bool}

/-- **Truth-table closure for indexed `PP` families:** for `A ∈ PP (encPair enc encUnary)`, a
polynomial-time unary query count `r`, and a polynomial-time Boolean combiner `d`, the language
`{a | d (a, truthTableAnswers A r a) = true}` belongs to `PP enc`. -/
theorem truthTable_mem_PP (hA : A ∈ PP (encPair enc encUnary))
    (hr : ComputableInPolyTime r enc encUnary)
    (hd : ComputableInPolyTime d (encPair enc encBits) encBool) :
    {a | d (a, truthTableAnswers A r a) = true} ∈ PP enc := by
  have hr := hr.tidy
  have hd := hd.tidy
  classical
  obtain ⟨g₀, hg₀, hAg₀⟩ := mem_PP_iff_exists_GapP.mp hA
  let g : α × ℕ → ℤ := fun x => (g₀ x + g₀ x) - 1
  have hg : g ∈ GapP (encPair enc encUnary) :=
    GapP.sub_mem' (GapP.add_mem hg₀ hg₀) GapP.one_mem
  obtain ⟨p, hp⟩ := GapP.exists_abs_le_two_pow hg
  let M : α → ℕ := fun a => p.eval (2 * (enc a).length + 1 + r a)
  have hM : ComputableTidilyInPolyTime M enc encUnary := by dsimp [M]; fun_prop
  refine mem_PP_iff_exists_GapP.mpr ⟨ppTruthTableGap M r g d, ppTruthTableGap_mem hg hM hr hd,
    fun a => ?_⟩
  let v : Fin (r a) → Bool := fun i => decide ((a, i.1) ∈ A)
  have hv_ofFn : List.ofFn v = truthTableAnswers A r a := rfl
  have hdom : ∑ w ∈ univ.erase v, ppWordWeight M r g a w < ppWordWeight M r g a v := by
    refine sum_erase_ppWordWeight_lt (A := A)
      (fun i _ hi => ?_) (fun i _ hi => ?_) (fun i hi => ?_)
    · have := (hAg₀ (a, i)).mp hi
      dsimp [g]; omega
    · have : ¬ 0 < g₀ (a, i) := fun h => hi ((hAg₀ (a, i)).mpr h)
      dsimp [g]; omega
    · refine (hp (a, i)).trans (pow_le_pow_right₀ (by omega) (Polynomial.eval_mono _ ?_))
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      omega
  unfold ppTruthTableGap
  rw [← add_sum_erase univ _ (mem_univ v), hv_ofFn]
  have hrest_lower : -(∑ w ∈ univ.erase v, ppWordWeight M r g a w) ≤
      ∑ w ∈ univ.erase v, (if d (a, List.ofFn w) then 1 else -1) * ppWordWeight M r g a w := by
    rw [← sum_neg_distrib]
    refine sum_le_sum fun w _ => ?_
    have := ppWordWeight_nonneg M r g a w
    split_ifs <;> omega
  have hrest_upper :
      ∑ w ∈ univ.erase v, (if d (a, List.ofFn w) then 1 else -1) * ppWordWeight M r g a w ≤
      ∑ w ∈ univ.erase v, ppWordWeight M r g a w := by
    refine sum_le_sum fun w _ => ?_
    have := ppWordWeight_nonneg M r g a w
    split_ifs <;> omega
  change d (a, truthTableAnswers A r a) = true ↔ _
  cases hd_val : d (a, truthTableAnswers A r a) <;> simp only [Bool.false_eq_true,
    ↓reduceIte, one_mul, neg_one_mul, true_iff, false_iff, not_lt] <;> omega

/-- **Fortnow–Reingold theorem:** `PP` is closed under polynomial-time truth-table reductions
[Fortnow and Reingold][FortnowReingold1996]. -/
theorem PolyTimeTruthTableReducible.mem_PP {β : Type} {encB : β ↪ List Bool}
    {L : Set α} {B : Set β} (h : PolyTimeTruthTableReducible enc encB L B)
    (hB : B ∈ PP encB) : L ∈ PP enc := by
  obtain ⟨r, q, d, hr, hq, hd, hL⟩ := h
  have hqB : q ⁻¹' B ∈ PP (encPair enc encUnary) :=
    PolyTimeReducible.mem_PP ⟨q, hq, fun _ => Iff.rfl⟩ hB
  convert truthTable_mem_PP hqB hr hd using 1
  ext a
  exact hL a

/-! ### Bounded quantifiers and Boolean closure -/

/-- `PP` is closed under polynomial-time bounded universal quantification. -/
theorem forall_lt_mem_PP (hA : A ∈ PP (encPair enc encUnary))
    (hr : ComputableInPolyTime r enc encUnary) :
    {a | ∀ i < r a, (a, i) ∈ A} ∈ PP enc := by
  have hr := hr.tidy
  have hd : ComputableTidilyInPolyTime (fun x : α × List Bool => x.2.all id)
      (encPair enc encBits) encBool :=
    ComputableTidilyInPolyTime.allWithEncoding (encP := encBool) (encA := encBool) (encL := encBits)
      (test := fun p : Bool × Bool => p.2) (by fun_prop) (.const false) (.snd enc encBits)
  convert truthTable_mem_PP hA (.of_tidy hr) (.of_tidy hd) using 1
  ext a
  simp [truthTableAnswers, List.all_eq_true, Fin.forall_iff]

/-- `PP` is closed under polynomial-time bounded existential quantification. -/
theorem exists_lt_mem_PP (hA : A ∈ PP (encPair enc encUnary))
    (hr : ComputableInPolyTime r enc encUnary) :
    {a | ∃ i < r a, (a, i) ∈ A} ∈ PP enc := by
  have hr := hr.tidy
  have hd : ComputableTidilyInPolyTime (fun x : α × List Bool => x.2.any id)
      (encPair enc encBits) encBool :=
    ComputableTidilyInPolyTime.anyWithEncoding (encP := encBool) (encA := encBool) (encL := encBits)
      (test := fun p : Bool × Bool => p.2) (by fun_prop) (.const false) (.snd enc encBits)
  convert truthTable_mem_PP hA (.of_tidy hr) (.of_tidy hd) using 1
  ext a
  simp [truthTableAnswers, List.any_eq_true, Fin.exists_iff]

/-- **Beigel–Reingold–Spielman theorem:** `PP` is closed under intersection
[Beigel, Reingold and Spielman][BeigelReingoldSpielman1995]. -/
theorem inter_mem_PP {A B : Set α} (hA : A ∈ PP enc) (hB : B ∈ PP enc) :
    A ∩ B ∈ PP enc := by
  classical
  obtain ⟨gA, hgA, hAg⟩ := mem_PP_iff_exists_GapP.mp hA
  obtain ⟨gB, hgB, hBg⟩ := mem_PP_iff_exists_GapP.mp hB
  let C : Set (α × ℕ) := {x | if x.2 = 0 then x.1 ∈ A else x.1 ∈ B}
  have hC : C ∈ PP (encPair enc encUnary) := by
    refine mem_PP_iff_exists_GapP.mpr ⟨fun x => if decide (x.2 = 0) then gA x.1 else gB x.1,
      GapP.ite_mem (.of_tidy (by fun_prop)) (GapP.comp_mem hgA (.of_tidy (.fst enc encUnary)))
        (GapP.comp_mem hgB (.of_tidy (.fst enc encUnary))), fun x => ?_⟩
    by_cases h : x.2 = 0 <;> simp [C, h, hAg x.1, hBg x.1]
  have hd : ComputableTidilyInPolyTime
      (fun x : α × List Bool => x.2.getD 0 false && x.2.getD 1 false)
      (encPair enc encBits) encBool := by fun_prop
  convert truthTable_mem_PP (r := fun _ => 2) hC (.of_tidy (by fun_prop)) (.of_tidy hd) using 1
  ext a
  simp [C, truthTableAnswers]

/-- `PP` as a Boolean subalgebra of `Set α`. -/
def PP.booleanSubalgebra (enc : α ↪ List Bool) : BooleanSubalgebra (Set α) :=
  .ofComplInf (PP enc) (BPP_subset_PP (P_subset_BPP empty_mem_P)) (fun _ => compl_mem_PP)
    (fun _ _ => inter_mem_PP)

@[simp]
theorem PP.coe_booleanSubalgebra : (PP.booleanSubalgebra enc : Set (Set α)) = PP enc := rfl

@[simp]
theorem PP.mem_booleanSubalgebra {A : Set α} : A ∈ PP.booleanSubalgebra enc ↔ A ∈ PP enc := Iff.rfl

/-- `PP` is closed under union [Beigel, Reingold and Spielman][BeigelReingoldSpielman1995]. -/
theorem union_mem_PP {A B : Set α} (hA : A ∈ PP enc) (hB : B ∈ PP enc) :
    A ∪ B ∈ PP enc :=
  (PP.booleanSubalgebra enc).sup_mem hA hB

/-- `PP` is closed under set difference. -/
theorem diff_mem_PP {A B : Set α} (hA : A ∈ PP enc) (hB : B ∈ PP enc) :
    A \ B ∈ PP enc :=
  (PP.booleanSubalgebra enc).sdiff_mem hA hB

/-- `PP` is closed under symmetric difference. -/
theorem symmDiff_mem_PP {A B : Set α} (hA : A ∈ PP enc) (hB : B ∈ PP enc) :
    symmDiff A B ∈ PP enc :=
  (PP.booleanSubalgebra enc).symmDiff_mem hA hB

end Cslib.Complexity
