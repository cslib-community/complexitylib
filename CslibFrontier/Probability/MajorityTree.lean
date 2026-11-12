/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Union
import Mathlib.Tactic

/-!
# Amplification by random majority trees

Valiant's amplification [Valiant1984Majority]: if a random leaf `h ∼ Λ` predicts `f z` correctly
with probability at least `1/2 + ε` at every point `z` of a finite set, then a complete ternary
tree of three-input majorities with independent random leaves is correct everywhere with positive
probability. Its height is `m₁ + m₂` where `(11/8)^m₁ ε ≥ 1/4` and `|Z| (3/4)^(2^m₂) < 3`, i.e.
`O(log (1/ε) + log log |Z|)` (`exists_height_eq_forall_eval_eq`, with
`card_mul_three_quarters_pow_lt` choosing `m₂`).

A level maps a correctness probability `p` to `amplify p = p² (3 - 2p)` (`map_eval_random_succ`,
`maj3Law_true_toReal`). Near `1/2` this multiplies the advantage by `11/8`; above `3/4` the error
`q` becomes at most `3 q²`.

This is the form of [ChukhinKulikovMihajlinSmal2026], Lemma 3.7 (printed p. 8; PDF p. 9), used in
the proof of its Theorem 1.2. Leaves are elements of an arbitrary type `H` rather than formula
variables; three-input majority is the monotone formula `(a ∧ b) ∨ (c ∧ (a ∨ b))`.

## Main definitions

* `Cslib.Probability.MajorityTree`: ternary trees of three-input majorities with leaves in `H`.
* `Cslib.Probability.MajorityTree.random`: the complete tree of a given height with independent
  leaves.

## Main results

* `Cslib.Probability.MajorityTree.exists_height_eq_forall_eval_eq`: Valiant's amplification.

## References

* [L. G. Valiant, *Short monotone formulae for the majority function*][Valiant1984Majority]
-/

public section

namespace Cslib.Probability

/-- Three-input majority, as the monotone formula `(a ∧ b) ∨ (c ∧ (a ∨ b))`. -/
@[expose] def maj3 (a b c : Bool) : Bool := (a && b) || (c && (a || b))

/-- Majority commutes with comparing every input against a fixed bit. -/
theorem maj3_beq (a b c d : Bool) : maj3 (a == d) (b == d) (c == d) = (maj3 a b c == d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- A ternary tree of three-input majorities whose leaves carry elements of `H`. -/
inductive MajorityTree (H : Type*) where
  /-- A single leaf. -/
  | leaf (h : H)
  /-- The majority of three subtrees. -/
  | node (a b c : MajorityTree H)

namespace MajorityTree

variable {H Z : Type*}

/-- The value of a tree when each leaf `h` has value `g h`. -/
@[expose] def eval (g : H → Bool) : MajorityTree H → Bool
  | leaf h => g h
  | node a b c => maj3 (a.eval g) (b.eval g) (c.eval g)

/-- The height of a tree: the number of majority gates on a longest root-leaf path. -/
@[expose] def height : MajorityTree H → ℕ
  | leaf _ => 0
  | node a b c => max (max a.height b.height) c.height + 1

/-- A tree is correct against `b` at a leaf valuation exactly when it evaluates to `true` on the
leaf correctness bits. -/
theorem eval_beq (g : H → Bool) (b : Bool) (t : MajorityTree H) :
    t.eval (fun h => g h == b) = (t.eval g == b) := by
  induction t with
  | leaf h => rfl
  | node a c d iha ihc ihd => simp only [eval, iha, ihc, ihd, maj3_beq]

/-- The complete tree of height `m` whose leaves are drawn independently from `Λ`. -/
noncomputable def random (Λ : PMF H) : ℕ → PMF (MajorityTree H)
  | 0 => Λ.map leaf
  | m + 1 => do
      let a ← random Λ m
      let b ← random Λ m
      let c ← random Λ m
      return node a b c

/-- Every random tree of height `m` has height exactly `m`. -/
theorem height_of_mem_support (Λ : PMF H) :
    ∀ {m : ℕ} {t : MajorityTree H}, t ∈ (random Λ m).support → t.height = m
  | 0, t, ht => by
    simp only [random, PMF.support_map, Set.mem_image] at ht
    obtain ⟨h, -, rfl⟩ := ht
    rfl
  | m + 1, t, ht => by
    simp only [random, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.support_bind,
      PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at ht
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := ht
    simp [height, height_of_mem_support Λ ha, height_of_mem_support Λ hb,
      height_of_mem_support Λ hc]

/-- The majority of three independent draws from a Boolean distribution. -/
noncomputable def maj3Law (μ : PMF Bool) : PMF Bool := do
  let a ← μ
  let b ← μ
  let c ← μ
  return maj3 a b c

/-- One level of majority on a correctness probability `p`: `p³ + 3 p² (1 - p)`. -/
@[expose] def amplify (p : ℝ) : ℝ := p ^ 2 * (3 - 2 * p)

/-- The majority of three independent draws is `true` with probability `amplify`. -/
theorem maj3Law_true_toReal (μ : PMF Bool) :
    (maj3Law μ true).toReal = amplify (μ true).toReal := by
  have hsum := Cslib.Probability.PMF.apply_true_add_apply_false μ
  have hfalse := Cslib.Probability.PMF.toReal_false_eq_one_sub μ
  have htrue : maj3Law μ true = μ true ^ 3 + 3 * (μ true ^ 2 * μ false) := by
    simp only [maj3Law, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_apply, tsum_bool,
      PMF.pure_apply, maj3]
    simp only [Bool.and_true, Bool.or_true, Bool.and_false, Bool.or_false, ite_true]
    norm_num
    ring
  have hne (b : Bool) : μ b ≠ ⊤ := PMF.apply_ne_top μ b
  have hne' : 3 * (μ true ^ 2 * μ false) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (ENNReal.pow_ne_top (hne _)) (hne _))
  rw [htrue, amplify, ENNReal.toReal_add (ENNReal.pow_ne_top (hne _)) hne', ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, hfalse]
  norm_num
  ring

/-- Evaluating a random tree one level higher draws three independent subtree values and takes
their majority. -/
theorem map_eval_random_succ (Λ : PMF H) (g : H → Bool) (m : ℕ) :
    (random Λ (m + 1)).map (eval g) = maj3Law ((random Λ m).map (eval g)) := by
  simp only [random, maj3Law, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind,
    PMF.bind_map, PMF.pure_map, Function.comp_def, eval]

/-- `amplify` is monotone on `[0, 1]`. -/
theorem amplify_mono {p p' : ℝ} (h0 : 0 ≤ p) (h : p ≤ p') (h1 : p' ≤ 1) :
    amplify p ≤ amplify p' := by
  unfold amplify
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h), mul_nonneg (sub_nonneg.mpr h)
    (sub_nonneg.mpr h1), mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr h)) (sub_nonneg.mpr h1)]

/-- Near `1/2`, a level multiplies the advantage by at least `11/8`. -/
theorem half_add_le_amplify {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1 / 4) :
    1 / 2 + 11 / 8 * e ≤ amplify (1 / 2 + e) := by
  unfold amplify
  nlinarith [mul_nonneg h0 (mul_nonneg h0 h0), mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.mpr h1)]

/-- A level squares the error up to a factor `3`. -/
theorem one_sub_amplify_le {p : ℝ} (h1 : p ≤ 1) :
    1 - amplify p ≤ 3 * (1 - p) ^ 2 := by
  unfold amplify
  nlinarith [mul_nonneg (sq_nonneg (1 - p)) (sub_nonneg.mpr h1)]

/-- Phase one: along probabilities that follow `amplify`, the advantage over `1/2` grows by
`11/8` per level until it reaches `1/4`. -/
private theorem half_add_min_le {P : ℕ → ℝ} {ε : ℝ} (hP1 : ∀ j, P j ≤ 1)
    (hstep : ∀ j, P (j + 1) = amplify (P j)) (hε : 0 ≤ ε) (h0 : 1 / 2 + ε ≤ P 0) (j : ℕ) :
    1 / 2 + min (1 / 4) ((11 / 8) ^ j * ε) ≤ P j := by
  induction j with
  | zero => simpa using le_trans (by simp) h0
  | succ j ih =>
    set c := min (1 / 4) ((11 / 8) ^ j * ε)
    have hc0 : 0 ≤ c := le_min (by norm_num) (by positivity)
    have hc1 : c ≤ 1 / 4 := min_le_left _ _
    have hmono := amplify_mono (by linarith) ih (hP1 j)
    have hgrow := half_add_le_amplify hc0 hc1
    have hmin : min (1 / 4) ((11 / 8) ^ (j + 1) * ε) ≤ 11 / 8 * c := by
      rcases min_choice (1 / 4 : ℝ) ((11 / 8) ^ j * ε) with h | h
      · rw [show c = 1 / 4 from h]; exact (min_le_left _ _).trans (by norm_num)
      · rw [show c = (11 / 8) ^ j * ε from h, pow_succ]
        exact (min_le_right _ _).trans (le_of_eq (by ring))
    rw [hstep]
    linarith

/-- Phase two: once a probability following `amplify` reaches `3/4`, three times its error is at
most `(3/4)^(2^i)` after `i` more levels. -/
private theorem three_mul_one_sub_le {P : ℕ → ℝ} (hP1 : ∀ j, P j ≤ 1)
    (hstep : ∀ j, P (j + 1) = amplify (P j)) {j₀ : ℕ} (hstart : 3 / 4 ≤ P j₀) (i : ℕ) :
    3 * (1 - P (j₀ + i)) ≤ (3 / 4) ^ 2 ^ i := by
  induction i with
  | zero => simp only [add_zero, pow_zero, pow_one]; linarith
  | succ i ih =>
    have hq0 : 0 ≤ 3 * (1 - P (j₀ + i)) := by linarith [hP1 (j₀ + i)]
    have hpow : (3 / 4 : ℝ) ^ 2 ^ i ≤ 3 / 4 :=
      pow_le_of_le_one (by norm_num) (by norm_num) (by positivity)
    have hsq := one_sub_amplify_le (hP1 (j₀ + i))
    rw [← add_assoc, hstep, pow_succ, pow_mul]
    nlinarith [mul_le_mul ih ih hq0 (by positivity)]

/-- `(3/4)^(2^m)` is below `3 / N` once `2^m ≥ 4 ⌈log₂ N⌉`, i.e. for `m = 2 + ⌈log₂ ⌈log₂ N⌉⌉`. -/
theorem card_mul_three_quarters_pow_lt (N : ℕ) :
    (N : ℝ) * (3 / 4) ^ 2 ^ (2 + Nat.clog 2 (Nat.clog 2 N)) < 3 := by
  set L := Nat.clog 2 N
  have hN : (N : ℝ) ≤ 2 ^ L := by exact_mod_cast Nat.le_pow_clog one_lt_two N
  have hL : 4 * L ≤ 2 ^ (2 + Nat.clog 2 L) := by
    rw [pow_add]
    exact Nat.mul_le_mul_left _ (Nat.le_pow_clog one_lt_two L)
  have hq : (3 / 4 : ℝ) ^ 2 ^ (2 + Nat.clog 2 L) ≤ ((3 / 4) ^ 4) ^ L := by
    rw [← pow_mul]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hL
  have h81 : ((3 / 4 : ℝ) ^ 4) ^ L ≤ (1 / 2) ^ L :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) L
  have hhalf : (2 : ℝ) ^ L * (1 / 2) ^ L = 1 := by rw [← mul_pow]; norm_num
  calc (N : ℝ) * (3 / 4) ^ 2 ^ (2 + Nat.clog 2 L) ≤ 2 ^ L * (1 / 2) ^ L :=
        mul_le_mul hN (hq.trans h81) (by positivity) (by positivity)
    _ < 3 := by rw [hhalf]; norm_num

/-- **Valiant's amplification** ([ChukhinKulikovMihajlinSmal2026], Lemma 3.7, in tree form).
If a leaf drawn from `Λ` predicts `f z` with probability at least `1/2 + ε` at every point `z` of
a finite type, then some majority tree of height `m₁ + m₂` predicts `f` correctly everywhere,
whenever `(11/8)^m₁ ε ≥ 1/4` and `|Z| (3/4)^(2^m₂) < 3`. Its leaves are possible draws of `Λ`. -/
theorem exists_height_eq_forall_eval_eq [Fintype Z] (Λ : PMF H) (v : H → Z → Bool)
    (f : Z → Bool) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ z, 1 / 2 + ε ≤ ((Λ.map fun h => v h z == f z) true).toReal)
    {m₁ m₂ : ℕ} (hm₁ : 1 / 4 ≤ (11 / 8) ^ m₁ * ε)
    (hm₂ : (Fintype.card Z : ℝ) * (3 / 4) ^ 2 ^ m₂ < 3) :
    ∃ t ∈ (random Λ (m₁ + m₂)).support, ∀ z, t.eval (fun h => v h z) = f z := by
  classical
  -- Correctness probabilities at each point follow `amplify`.
  set P : Z → ℕ → ℝ := fun z j =>
    (((random Λ j).map (eval fun h => v h z == f z)) true).toReal with hPdef
  have hP1 (z : Z) (j : ℕ) : P z j ≤ 1 := Cslib.Probability.PMF.toReal_apply_le_one _ _
  have hstep (z : Z) (j : ℕ) : P z (j + 1) = amplify (P z j) := by
    simp only [hPdef, map_eval_random_succ, maj3Law_true_toReal]
  have hP0 (z : Z) : 1 / 2 + ε ≤ P z 0 := by
    have h0 : (random Λ 0).map (eval fun h => v h z == f z) = Λ.map fun h => v h z == f z := by
      rw [random, PMF.map_comp]
      rfl
    simpa only [hPdef, h0] using h z
  have hmid (z : Z) : 3 / 4 ≤ P z m₁ := by
    have := half_add_min_le (hP1 z) (hstep z) hε (hP0 z) m₁
    rw [min_eq_left hm₁] at this
    linarith
  have herr (z : Z) : 3 * (1 - P z (m₁ + m₂)) ≤ (3 / 4) ^ 2 ^ m₂ :=
    three_mul_one_sub_le (hP1 z) (hstep z) (hmid z) m₂
  -- The union bound over the finitely many points.
  let wrong : Z → Set (MajorityTree H) := fun z => {t | t.eval (fun h => v h z) ≠ f z}
  have hwrong (z : Z) : ((random Λ (m₁ + m₂)).toOuterMeasure (wrong z)).toReal =
      1 - P z (m₁ + m₂) := by
    have hc := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl (random Λ (m₁ + m₂))
      (wrong z)
    have hmap : P z (m₁ + m₂) =
        ((random Λ (m₁ + m₂)).toOuterMeasure (wrong z)ᶜ).toReal := by
      simp only [hPdef]
      rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
      congr 3
      ext t
      simp [wrong, eval_beq]
    linarith
  have hunion := Cslib.Probability.PMF.toOuterMeasure_toReal_biUnion_finset_le
    (random Λ (m₁ + m₂)) Finset.univ wrong
  have hsum : ∑ z, ((random Λ (m₁ + m₂)).toOuterMeasure (wrong z)).toReal < 1 := by
    simp only [hwrong]
    calc ∑ z, (1 - P z (m₁ + m₂)) ≤ ∑ _z : Z, (3 / 4 : ℝ) ^ 2 ^ m₂ / 3 :=
          Finset.sum_le_sum fun z _ => by linarith [herr z]
      _ < 1 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; linarith
  have hpos : 0 < ((random Λ (m₁ + m₂)).toOuterMeasure (⋃ z ∈ Finset.univ, wrong z)ᶜ).toReal := by
    have := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl (random Λ (m₁ + m₂))
      (⋃ z ∈ Finset.univ, wrong z)
    linarith
  obtain ⟨t, ht, hsupp⟩ := (Cslib.Probability.PMF.toOuterMeasure_toReal_pos_iff _ _).mp hpos
  refine ⟨t, hsupp, fun z => ?_⟩
  by_contra hz
  exact ht (Set.mem_biUnion (Finset.mem_univ z) hz)

end MajorityTree

end Cslib.Probability
