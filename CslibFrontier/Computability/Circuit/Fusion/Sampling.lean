/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Fusion.Semifilter
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-!
# The fixed-distribution counting barrier for Fusion

An explicit distribution on pairs covers each semifilter accepting the literals of a positive
input with probability at least `1 / (8 * n + 8)`. Averaging against any fixed nonnegative
weighted family of witnesses gives a pair of at least that relative mass. Consequently the
reciprocal of a uniform bound on covered probability is at most `8 * n + 8`.

This formalizes the conclusions of [Oliveira2018Approximation, Lemma 3 and Theorem 6], following
[Razborov1989], by a direct cylinder argument adapted from their random-function proof. Exact
literal consistency is not needed: acceptance of the matching literal for each coordinate
suffices. The pair sampler is fixed before the witness is chosen. The conclusion bounds this
fixed-distribution counting certificate, not pair-cover complexity or circuit complexity;
certificates whose capacity constraint ranges only over a particular circuit's gate pairs are
outside its scope.

For a random full truth table `h` and a positive input `v`, reveal the coordinates of the
negative input one at a time, leaving the remaining coordinates fixed to `v`. When `h(v)` is
true but the semifilter rejects the final truth set, some adjacent cylinders lose acceptance.
Intersecting the previous cylinder with the matching literal gives a covering pair. A suffix
bit flip shows that each cylinder has the same marginal law as a cylinder with zero suffix.
Independently flipping the truth-table entry at `v` shows that the error probability is half
the rejection probability, because `v` is outside the negative carrier. Pairing a random set
with its complement accounts for the remaining probability. Union bounds and averaging give
the stated constant. No efficient sampling or construction bound is asserted.

## Main definitions

* `Cslib.Circuits.Fusion.booleanPairSample`: the fixed finite sampler, including the
  complementary-set case.

## Main results

* `Cslib.Circuits.Fusion.le_booleanPairSample_expect`: the random-pair guarantee, with the sampling
  lemma proved.
* `Cslib.Circuits.Fusion.exists_pair_weight_ge`: weighted double counting against any finite
  witness family.
* `Cslib.Circuits.Fusion.fixedDistribution_counting_bound`: positivity of capacity and the
  reciprocal bound `8n+8`.

## References

* [Igor Carboni Oliveira, *Notes on the Method of Approximations and the Emergence of the
  Fusion Method*][Oliveira2018Approximation], Lemma 3, Theorem 6, and Appendix A.
* [Alexander A. Razborov, *On the method of approximations*][Razborov1989].
-/

@[expose] public section

open scoped BigOperators
open Finset
namespace Cslib.Circuits.Fusion

variable {n : ℕ} {target : Set (Fin n → Bool)}

private noncomputable def hit {U : Type*} (F : Semifilter U) (p : Set U × Set U) : ℝ :=
  open Classical in if ¬ F.PreservesPair p then 1 else 0

private def splice (k : ℕ) (v x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i.val < k then x i else v i

private def cylinder (target : Set (Fin n → Bool)) (k : ℕ) (v : Fin n → Bool)
    (h : (Fin n → Bool) → Bool) : Set ↥(targetᶜ) :=
  {x | h (splice k v x.val) = true}

private theorem cylinder_step (F : Semifilter ↥(targetᶜ)) (v : Fin n → Bool)
    (hv : ∀ i, F {x | x.val i = v i}) (h : (Fin n → Bool) → Bool) (k : Fin n)
    (hprev : F (cylinder target k.val v h))
    (hnext : ¬ F (cylinder target (k.val + 1) v h)) :
    ¬ F.PreservesPair (cylinder target k.val v h, {x | x.val k = v k}) := by
  intro hp
  apply hnext
  apply F.monotone _ (hp hprev (hv k))
  intro x hx
  change h (splice (k.val + 1) v x.val) = true
  have heq : splice (k.val + 1) v x.val = splice k.val v x.val := by
    funext i
    unfold splice
    split_ifs with h1 h2
    · rfl
    · have hi : i = k := Fin.ext (by lia)
      subst i
      exact hx.2
    · lia
    · rfl
  rw [heq]
  exact hx.1

private theorem path_cover (F : Semifilter ↥(targetᶜ)) (v : Fin n → Bool)
    (hv : ∀ i, F {x | x.val i = v i}) (h : (Fin n → Bool) → Bool)
    (hh : h v = true) (hF : ¬ F {x | h x.val = true}) :
    ∃ k : Fin n, ¬ F.PreservesPair
      (cylinder target k.val v h, {x | x.val k = v k}) := by
  by_contra! hnone
  have all : ∀ k, k ≤ n → F (cylinder target k v h) := by
    intro k hk
    induction k with
    | zero =>
      have heq : cylinder target 0 v h = Set.univ := by
        ext x
        have hp : splice 0 v x.val = v := by ext i; simp [splice]
        simp [cylinder, hp, hh]
      rw [heq]
      exact F.apply_univ
    | succ k ih =>
      by_contra hn
      exact cylinder_step F v hv h ⟨k, by lia⟩ (ih (by lia)) hn (hnone ⟨k, by lia⟩)
  apply hF
  have heq : cylinder target n v h = {x | h x.val = true} := by
    ext x
    have hp : splice n v x.val = x.val := by ext i; simp [splice, i.isLt]
    simp [cylinder, hp]
  rw [← heq]
  exact all n le_rfl


private noncomputable def oneIf (p : Prop) : ℝ :=
  open Classical in if p then 1 else 0

private theorem expect_involution {Ω : Type*} [Fintype Ω] (e : Ω → Ω)
    (he : Function.Involutive e) (f : Ω → ℝ) : (𝔼 x, f (e x)) = 𝔼 x, f x :=
  Fintype.expect_bijective e he.bijective _ _ (fun _ => rfl)

private def flipAt (v : Fin n → Bool) (h : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) : Bool := if x = v then !h x else h x

private theorem flipAt_involutive (v : Fin n → Bool) : Function.Involutive (flipAt v) := by
  intro h
  funext x
  by_cases hx : x = v <;> simp [flipAt, hx]

private theorem flipAt_restrict (v : target) (h : (Fin n → Bool) → Bool) :
    {x : ↥(targetᶜ) | flipAt v.val h x.val = true} = {x | h x.val = true} := by
  ext x
  have hx : x.val ≠ v.val := fun h => x.property (h ▸ v.property)
  simp [flipAt, hx]

private theorem rejection_eq_twice_error (F : Semifilter ↥(targetᶜ)) (v : target) :
    (𝔼 h : (Fin n → Bool) → Bool, oneIf (¬ F {x | h x.val = true})) =
      2 * 𝔼 h : (Fin n → Bool) → Bool,
        oneIf (h v.val = true ∧ ¬ F {x | h x.val = true}) := by
  classical
  let err := fun h : (Fin n → Bool) → Bool =>
    oneIf (h v.val = true ∧ ¬ F {x | h x.val = true})
  have pointwise (h : (Fin n → Bool) → Bool) :
      oneIf (¬ F {x | h x.val = true}) = err h + err (flipAt v.val h) := by
    dsimp only [err]
    rw [flipAt_restrict v h]
    by_cases hf : F {x | h x.val = true} <;> cases hv : h v.val <;>
      simp [oneIf, flipAt, hf, hv]
  simp_rw [pointwise]
  rw [Finset.expect_add_distrib, expect_involution _ (flipAt_involutive v.val)]
  change (𝔼 h, err h) + (𝔼 h, err h) = 2 * 𝔼 h, err h
  ring

private theorem complement_estimate (F : Semifilter ↥(targetᶜ)) :
    1 ≤ 2 * (𝔼 h : (Fin n → Bool) → Bool, oneIf (¬ F {x | h x.val = true})) +
      𝔼 h : (Fin n → Bool) → Bool,
        hit F ({x | h x.val = true}, {x | h x.val ≠ true}) := by
  classical
  have pointwise (h : (Fin n → Bool) → Bool) :
      (1 : ℝ) ≤ oneIf (¬ F {x | h x.val = true}) +
        oneIf (¬ F {x | (!h x.val) = true}) +
        hit F ({x | h x.val = true}, {x | h x.val ≠ true}) := by
    have hcomp : {x : ↥(targetᶜ) | (!h x.val) = true} = {x | h x.val ≠ true} := by
      ext x
      cases h x.val <;> simp
    rw [hcomp]
    have hempty : ({x : ↥(targetᶜ) | h x.val = true} ∩ {x | h x.val ≠ true}) = ∅ := by
      ext x
      simp
    by_cases ha : F {x | h x.val = true} <;>
      by_cases hb : F {x | h x.val ≠ true} <;>
      simp only [oneIf, hit, Semifilter.PreservesPair, ha, hb, hempty,
        F.not_apply_empty, not_true_eq_false, not_false_eq_true, true_implies,
        false_implies, ite_true, ite_false] <;> norm_num
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun h _ => pointwise h)
  rw [Fintype.expect_const, Finset.expect_add_distrib, Finset.expect_add_distrib] at hh
  have hnot : Function.Involutive (fun h : (Fin n → Bool) → Bool => fun x => !h x) := by
    intro h
    funext x
    simp
  have he := expect_involution _ hnot
    (fun h => oneIf (¬ F {x | h x.val = true}))
  rw [he] at hh
  linarith


private def shiftTable (k : ℕ) (v : Fin n → Bool) (h : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) : Bool :=
  h (fun i => if i.val < k then x i else x i ^^ v i)

private theorem shiftTable_involutive (k : ℕ) (v : Fin n → Bool) :
    Function.Involutive (shiftTable k v) := by
  intro h
  funext x
  apply congrArg h
  funext i
  by_cases hi : i.val < k <;> simp [hi]

private theorem cylinder_shift (k : ℕ) (v : Fin n → Bool) (h : (Fin n → Bool) → Bool) :
    cylinder target k (fun _ => false) (shiftTable k v h) = cylinder target k v h := by
  ext x
  change (h _ = true) ↔ (h _ = true)
  have he : (fun i => if i.val < k then splice k (fun _ => false) x.val i
      else splice k (fun _ => false) x.val i ^^ v i) = splice k v x.val := by
    funext i
    by_cases hi : i.val < k <;> simp [splice, hi]
  rw [he]

private theorem expect_cylinder (F : Semifilter ↥(targetᶜ)) (k : Fin n)
    (v : Fin n → Bool) (b : Bool) :
    (𝔼 h : (Fin n → Bool) → Bool,
      hit F (cylinder target k.val v h, {x | x.val k = b})) =
    𝔼 h : (Fin n → Bool) → Bool,
      hit F (cylinder target k.val (fun _ => false) h, {x | x.val k = b}) := by
  have he := expect_involution (shiftTable k.val v) (shiftTable_involutive k.val v)
    (fun h => hit F (cylinder target k.val (fun _ => false) h, {x | x.val k = b}))
  simpa only [cylinder_shift] using he

private theorem error_le_hits (F : Semifilter ↥(targetᶜ)) (v : Fin n → Bool)
    (hv : ∀ i, F {x | x.val i = v i}) :
    (𝔼 h : (Fin n → Bool) → Bool,
      oneIf (h v = true ∧ ¬ F {x | h x.val = true})) ≤
    ∑ k : Fin n, 𝔼 h : (Fin n → Bool) → Bool,
      hit F (cylinder target k.val (fun _ => false) h, {x | x.val k = v k}) := by
  classical
  have pointwise (h : (Fin n → Bool) → Bool) :
      oneIf (h v = true ∧ ¬ F {x | h x.val = true}) ≤
        ∑ k : Fin n, hit F (cylinder target k.val v h, {x | x.val k = v k}) := by
    by_cases hh : h v = true ∧ ¬ F {x | h x.val = true}
    · obtain ⟨k, hk⟩ := path_cover F v hv h hh.1 hh.2
      have hle := Finset.single_le_sum (f := fun k : Fin n =>
        hit F (cylinder target k.val v h, {x | x.val k = v k}))
        (fun k _ => by unfold hit; split_ifs <;> norm_num) (Finset.mem_univ k)
      simpa only [oneIf, hh, ite_true, hit, hk, not_false_eq_true, and_self] using hle
    · simp only [oneIf, hh, ite_false]
      exact Finset.sum_nonneg fun _ _ => by unfold hit; split_ifs <;> norm_num
  have he := Finset.expect_le_expect (s := Finset.univ) (fun h _ => pointwise h)
  rw [Finset.expect_sum_comm] at he
  simpa only [expect_cylinder] using he


/-- A fixed sampler for pairs over the negative inputs. Sample its three arguments independently
and uniformly: a coordinate or the extra complement case, a polarity, and a full truth table.
The sampler depends on the target, but not on any witness or distribution of witnesses. -/
def booleanPairSample (target : Set (Fin n → Bool)) (level : Option (Fin n))
    (b : Bool) (h : (Fin n → Bool) → Bool) : Set ↥(targetᶜ) × Set ↥(targetᶜ) :=
  match level with
  | none => ({x | h x.val = true}, {x | h x.val ≠ true})
  | some k => ({x | h (fun i => if i.val < k.val then x.val i else false) = true},
      {x | x.val k = b})

private theorem sample_sum (F : Semifilter ↥(targetᶜ)) :
    (∑ level : Option (Fin n), ∑ b : Bool,
      𝔼 h : (Fin n → Bool) → Bool, hit F (booleanPairSample target level b h)) =
    (∑ k : Fin n, ∑ b : Bool, 𝔼 h : (Fin n → Bool) → Bool,
      hit F (cylinder target k.val (fun _ => false) h, {x | x.val k = b})) +
    2 * (𝔼 h : (Fin n → Bool) → Bool,
      hit F ({x | h x.val = true}, {x | h x.val ≠ true})) := by
  simp only [Fintype.sum_option, booleanPairSample, Fintype.sum_bool]
  unfold cylinder splice
  ring

private theorem sample_sum_bound (F : Semifilter ↥(targetᶜ)) (v : target)
    (hv : ∀ i, F {x | x.val i = v.val i}) :
    1 ≤ 4 * ∑ level : Option (Fin n), ∑ b : Bool,
      𝔼 h : (Fin n → Bool) → Bool, hit F (booleanPairSample target level b h) := by
  have he := error_le_hits F v.val hv
  have hr := rejection_eq_twice_error F v
  have hc := complement_estimate F
  rw [hr] at hc
  have hnonneg (p : Set ↥(targetᶜ) × Set ↥(targetᶜ)) : 0 ≤ hit F p := by
    unfold hit
    split_ifs <;> norm_num
  have hsum : (∑ k : Fin n, 𝔼 h : (Fin n → Bool) → Bool,
        hit F (cylinder target k.val (fun _ => false) h, {x | x.val k = v.val k})) ≤
      ∑ k : Fin n, ∑ b : Bool, 𝔼 h : (Fin n → Bool) → Bool,
        hit F (cylinder target k.val (fun _ => false) h, {x | x.val k = b}) := by
    apply Finset.sum_le_sum
    intro k _
    exact Finset.single_le_sum (f := fun b : Bool =>
      𝔼 h : (Fin n → Bool) → Bool,
        hit F (cylinder target k.val (fun _ => false) h, {x | x.val k = b}))
      (fun b _ => Finset.expect_nonneg fun h _ => hnonneg _)
      (Finset.mem_univ (v.val k))
  have hroot : 0 ≤ 𝔼 h : (Fin n → Bool) → Bool,
      hit F ({x | h x.val = true}, {x | h x.val ≠ true}) :=
    Finset.expect_nonneg fun h _ => hnonneg _
  rw [sample_sum]
  linarith

open Classical in
/-- Uniformly sampling the level, polarity, and full truth table covers every matching-literal
semifilter with probability at least `1/(8n+8)`. The target may be arbitrary; existence of the
positive point and semifilter provides the nontriviality needed by the proof. -/
theorem le_booleanPairSample_expect (F : Semifilter ↥(targetᶜ)) (v : target)
    (hv : ∀ i, F {x | x.val i = v.val i}) :
    (1 : ℝ) / (8 * n + 8) ≤ 𝔼 level : Option (Fin n), 𝔼 b : Bool,
      𝔼 h : (Fin n → Bool) → Bool,
        if ¬ F.PreservesPair (booleanPairSample target level b h) then 1 else 0 := by
  change (1 : ℝ) / (8 * n + 8) ≤ 𝔼 level : Option (Fin n), 𝔼 b : Bool,
    𝔼 h : (Fin n → Bool) → Bool, hit F (booleanPairSample target level b h)
  have hb := sample_sum_bound F v hv
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  simp_rw [Fintype.expect_eq_sum_div_card (fun b : Bool => _)]
  simp only [Fintype.card_bool, Nat.cast_ofNat, ← Finset.sum_div]
  have hpos : (0 : ℝ) < n + 1 := by positivity
  apply (div_le_div_iff₀ (by positivity) hpos).mpr
  nlinarith


open Classical in
/-- For any nonnegative weights on a finite family of matching-literal witnesses, some pair
covers at least `1/(8n+8)` of their total weight. No normalization is required. -/
theorem exists_pair_weight_ge {W : Type*} [Fintype W]
    (F : W → Semifilter ↥(targetᶜ)) (v : W → target)
    (hv : ∀ w i, F w {x | x.val i = (v w).val i})
    (μ : W → ℝ) (hμ : ∀ w, 0 ≤ μ w) :
    ∃ p : Set ↥(targetᶜ) × Set ↥(targetᶜ),
      (∑ w, μ w) / (8 * n + 8) ≤
        ∑ w, μ w * if ¬ (F w).PreservesPair p then 1 else 0 := by
  have hb : (∑ w, μ w) / (8 * n + 8) ≤
      ∑ w, μ w * (𝔼 level : Option (Fin n), 𝔼 b : Bool,
        𝔼 h : (Fin n → Bool) → Bool, hit (F w) (booleanPairSample target level b h)) := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun w _ => by
      simpa only [div_eq_mul_inv, one_mul, hit] using
        mul_le_mul_of_nonneg_left (le_booleanPairSample_expect (F w) (v w) (hv w)) (hμ w)
  have he : (∑ w, μ w) / (8 * n + 8) ≤
      𝔼 level : Option (Fin n), 𝔼 b : Bool, 𝔼 h : (Fin n → Bool) → Bool,
        ∑ w, μ w * hit (F w) (booleanPairSample target level b h) := by
    simpa only [Finset.mul_expect, Finset.expect_sum_comm] using hb
  obtain ⟨level, _, hl⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty he
  obtain ⟨b, _, hb⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hl
  obtain ⟨h, _, hh⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hb
  exact ⟨booleanPairSample target level b h, hh⟩

open Classical in
/-- A fixed probability distribution on matching-literal witnesses cannot give a reciprocal
pair-capacity certificate larger than `8n+8`. In particular its maximum covered probability is
positive. This does not bound the minimum number of pairs covering the witnesses. -/
theorem fixedDistribution_counting_bound {W : Type*} [Fintype W]
    (F : W → Semifilter ↥(targetᶜ)) (v : W → target)
    (hv : ∀ w i, F w {x | x.val i = (v w).val i})
    (μ : W → ℝ) (hμ : ∀ w, 0 ≤ μ w) (hprob : ∑ w, μ w = 1)
    {d : ℝ} (hd : ∀ p : Set ↥(targetᶜ) × Set ↥(targetᶜ),
      ∑ w, μ w * (if ¬ (F w).PreservesPair p then 1 else 0) ≤ d) :
    0 < d ∧ 1 / d ≤ 8 * n + 8 := by
  obtain ⟨p, hp⟩ := exists_pair_weight_ge F v hv μ hμ
  rw [hprob] at hp
  have hden : (0 : ℝ) < 8 * n + 8 := by positivity
  have hle := hp.trans (hd p)
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hle
  refine ⟨hdpos, (div_le_iff₀ hdpos).mpr ?_⟩
  have hh := (div_le_iff₀ hden).mp hle
  nlinarith

end Cslib.Circuits.Fusion
