/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.HintDecoding
public import CslibFrontier.Foundations.Data.Code.LocalDecoding
import CslibFrontier.Foundations.Data.Finset.Markov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Local list decoding of Reed–Muller codes along lines with advice

Let `p` be a polynomial of total degree at most `d` in `m` variables over a field `F` with `q`
elements, and let `g` agree with `p` on a set `A` of `a` points, a small fraction of the
`Q = q ^ m` points. Local list decoding [SudanTrevisanVadhan2001] recovers `p(x)` at most points
`x` by decoding `g` along the line through `x` and a fixed point `z`, using the advice `p(z)` to
single out `p` among the polynomials that agree with `g` on the line.

The decoder `Cslib.Code.lineListDecode g d D z a x` parametrizes the line by
`t ↦ x + t • v`, where `v` is `z - x` scaled so that its first nonzero entry is `1`
(`Cslib.LinearAlgebra.firstNonzero`); then `z = x + c • v` for `c` the first nonzero entry of
`z - x`. It runs Sudan decoding with the hint `a` at `c` on the restriction of `g` to the line
(`Cslib.Code.hintDecode`). The direction `v` and the received word depend only on `x` and the line,
not on the position of `z` on it, so the hint position `c` is uniformly distributed over `F ∖ {0}`
given the line.

Two things can go wrong for a pair `(x, z)`: the line can have at most `D` agreements, or the hint
position can be one of the at most `D - d` bad positions of `Cslib.Code.card_hintDecode_ne_le`.
Points of a random line are pairwise independent and uniform, so the number `N` of agreements on
the line through a random point in a random direction has mean `μ = q * a / Q` and variance at most
`μ`, and Chebyshev's inequality bounds the first event
(`Cslib.Code.card_filter_lineAgree_le_mul_sq_le`). The second has probability at most
`(D - d) / (q - 1)` given the line. Averaging over `z`
(`Cslib.Code.exists_card_lineListDecode_ne_le`), some advice point `z` makes the decoder, with the
advice `p(z)`, correct at all but
`1 + (q * a * (Q - 1) / (μ - D) ^ 2 + Q * (Q - 1) * (D - d) / (q - 1)) / Q` points.

## Main definitions

* `Cslib.Code.lineAgree`: the number of points of a line in a set.
* `Cslib.Code.lineListDecode`: the local list decoder with advice.

## Main results

* `Cslib.Code.card_filter_lineAgree_le_mul_sq_le`: random lines sample a set well.
* `Cslib.Code.lineListDecode_eq`: the decoder is correct on good lines and hint positions.
* `Cslib.Code.exists_card_lineListDecode_ne_le`: **local list decoding of Reed–Muller codes**.

## References

* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
-/

@[expose] public section

namespace Cslib.Code

open Finset Polynomial Cslib.LinearAlgebra

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

/-! ### Random lines sample well -/

/-- The number of points of the line `t ↦ x + t • u` in `A`. -/
def lineAgree (A : Finset (Fin m → F)) (x u : Fin m → F) : ℕ := #{t : F | x + t • u ∈ A}

/-- The nonzero directions with a base point. -/
private def seeds (m : ℕ) (F : Type*) [Fintype F] [DecidableEq F] [Zero F] :
    Finset ((Fin m → F) × (Fin m → F)) := univ.filter fun xu => xu.2 ≠ 0

private theorem card_seeds : #(seeds m F) = Fintype.card F ^ m * (Fintype.card F ^ m - 1) := by
  rw [seeds, show (univ.filter fun xu : (Fin m → F) × (Fin m → F) => xu.2 ≠ 0) =
    univ ×ˢ (univ.filter fun u : Fin m → F => u ≠ 0) by ext; simp, card_product, card_univ,
    Fintype.card_fun, Fintype.card_fin, filter_ne', card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fun, Fintype.card_fin]

/-- Each point of a random line is uniformly distributed. -/
private theorem card_seeds_mem (A : Finset (Fin m → F)) (t : F) :
    #{xu ∈ seeds m F | xu.1 + t • xu.2 ∈ A} = #A * (Fintype.card F ^ m - 1) := by
  have h : ({xu ∈ seeds m F | xu.1 + t • xu.2 ∈ A} : Finset _) =
      (univ.filter fun u : Fin m → F => u ≠ 0).biUnion fun u =>
        (A.image fun y => y - t • u).map ⟨fun x => (x, u), fun _ _ h => (Prod.ext_iff.1 h).1⟩ := by
    ext ⟨x, u⟩
    simp only [seeds, mem_filter, mem_univ, true_and, mem_biUnion, mem_map, mem_image]
    constructor
    · rintro ⟨hu, hA⟩
      exact ⟨u, hu, x, ⟨_, hA, by abel⟩, rfl⟩
    · rintro ⟨u', hu', x', ⟨y, hy, rfl⟩, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h
      refine ⟨hu', ?_⟩
      change y - t • u' + t • u' ∈ A
      simpa using hy
  rw [h, card_biUnion]
  · simp only [card_map]
    rw [sum_congr rfl fun u _ => card_image_of_injective _ (sub_left_injective (b := t • u)),
      sum_const, smul_eq_mul, filter_ne', card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fun, Fintype.card_fin, mul_comm]
  · intro u _ u' _ huu'
    simp only [Function.onFun, disjoint_left, mem_map, mem_image, not_exists, not_and]
    rintro _ ⟨x, -, rfl⟩ x' - h
    exact huu' (Prod.ext_iff.1 h).2.symm

omit [Fintype F] [DecidableEq F] in
/-- The base point and direction of the line through `y` at `t` and `y'` at `t'`. -/
private theorem line_through {t t' : F} (hsub : t - t' ≠ 0) (y y' : Fin m → F) :
    y - t • (t - t')⁻¹ • (y - y') + t • (t - t')⁻¹ • (y - y') = y ∧
      y - t • (t - t')⁻¹ • (y - y') + t' • (t - t')⁻¹ • (y - y') = y' := by
  have h1 : (t - t') • (t - t')⁻¹ • (y - y') = y - y' := by
    rw [smul_smul, mul_inv_cancel₀ hsub, one_smul]
  refine ⟨sub_add_cancel _ _, ?_⟩
  calc y - t • (t - t')⁻¹ • (y - y') + t' • (t - t')⁻¹ • (y - y') =
      y - (t - t') • (t - t')⁻¹ • (y - y') := by rw [sub_smul]; abel
    _ = y' := by rw [h1]; abel

/-- Two distinct points of a random line are a uniformly random pair of distinct points. -/
private theorem card_seeds_mem_mem (A : Finset (Fin m → F)) {t t' : F} (htt : t ≠ t') :
    #{xu ∈ seeds m F | xu.1 + t • xu.2 ∈ A ∧ xu.1 + t' • xu.2 ∈ A} = #A * #A - #A := by
  rw [← offDiag_card]
  have hsub : t - t' ≠ 0 := sub_ne_zero.2 htt
  have hdir : ∀ x u : Fin m → F, (t - t')⁻¹ • (x + t • u - (x + t' • u)) = u := fun x u => by
    rw [show x + t • u - (x + t' • u) = (t - t') • u by rw [sub_smul]; abel, smul_smul,
      inv_mul_cancel₀ hsub, one_smul]
  refine card_nbij' (fun xu => (xu.1 + t • xu.2, xu.1 + t' • xu.2))
    (fun yy => (yy.1 - t • (t - t')⁻¹ • (yy.1 - yy.2), (t - t')⁻¹ • (yy.1 - yy.2)))
    (fun xu hxu => ?_) (fun yy hyy => ?_) (fun xu _ => ?_) (fun yy _ => ?_)
  · obtain ⟨x, u⟩ := xu
    rw [mem_coe, seeds, filter_filter, mem_filter] at hxu
    rw [mem_coe, mem_offDiag]
    refine ⟨hxu.2.2.1, hxu.2.2.2, fun heq => hxu.2.1 ?_⟩
    have heq' : x + t • u = x + t' • u := heq
    change u = 0
    rw [← hdir x u, heq', sub_self, smul_zero]
  · obtain ⟨y, y'⟩ := yy
    rw [mem_coe, mem_offDiag] at hyy
    rw [mem_coe, seeds, filter_filter, mem_filter]
    obtain ⟨h₁, h₂⟩ := line_through hsub y y'
    refine ⟨mem_univ _, fun h0 => hyy.2.2 ?_, by simpa only [h₁] using hyy.1,
      by simpa only [h₂] using hyy.2.1⟩
    rcases smul_eq_zero.1 h0 with h0 | h0
    · exact absurd h0 (inv_ne_zero hsub)
    · exact sub_eq_zero.1 h0
  · obtain ⟨x, u⟩ := xu
    simp only [hdir, Prod.mk.injEq, and_true]
    abel
  · obtain ⟨y, y'⟩ := yy
    obtain ⟨h₁, h₂⟩ := line_through hsub y y'
    exact Prod.ext h₁ h₂

/-- The first moment of `lineAgree A` over `seeds m F`. -/
private theorem sum_lineAgree_seeds (A : Finset (Fin m → F)) :
    ∑ xu ∈ seeds m F, (lineAgree A xu.1 xu.2 : ℝ) =
      Fintype.card F * (#A * ((Fintype.card F : ℝ) ^ m - 1)) := by
  have hN (xu : (Fin m → F) × (Fin m → F)) :
      (lineAgree A xu.1 xu.2 : ℝ) = ∑ t : F, if xu.1 + t • xu.2 ∈ A then (1 : ℝ) else 0 := by
    simp [lineAgree, sum_boole]
  simp only [hN]
  rw [sum_comm]
  simp only [sum_boole]
  rw [sum_congr rfl fun t _ => by rw [card_seeds_mem A t], sum_const, card_univ, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos)]
  simp

/-- The second moment of `lineAgree A` over `seeds m F`. -/
private theorem sum_lineAgree_sq_seeds (A : Finset (Fin m → F)) :
    ∑ xu ∈ seeds m F, (lineAgree A xu.1 xu.2 : ℝ) ^ 2 =
      Fintype.card F * (#A * ((Fintype.card F : ℝ) ^ m - 1)) +
        Fintype.card F * (Fintype.card F - 1) * (#A * #A - #A) := by
  have hdiagN (t : F) : ∑ t' : F,
      #{xu ∈ seeds m F | xu.1 + t • xu.2 ∈ A ∧ xu.1 + t' • xu.2 ∈ A} =
        #A * (Fintype.card F ^ m - 1) + (Fintype.card F - 1) * (#A * #A - #A) := by
    rw [← add_sum_erase _ _ (mem_univ t)]
    simp only [and_self, card_seeds_mem A t]
    rw [sum_congr rfl fun t' ht' => card_seeds_mem_mem A (Ne.symm (ne_of_mem_erase ht')),
      sum_const, card_erase_of_mem (mem_univ _), card_univ, smul_eq_mul]
  have hsq (xu : (Fin m → F) × (Fin m → F)) :
      (lineAgree A xu.1 xu.2 : ℝ) ^ 2 = ∑ t : F, ∑ t' : F,
        if xu.1 + t • xu.2 ∈ A ∧ xu.1 + t' • xu.2 ∈ A then (1 : ℝ) else 0 := by
    have hN : (lineAgree A xu.1 xu.2 : ℝ) =
        ∑ t : F, if xu.1 + t • xu.2 ∈ A then (1 : ℝ) else 0 := by simp [lineAgree, sum_boole]
    rw [hN, sq, sum_mul_sum]
    refine sum_congr rfl fun t _ => sum_congr rfl fun t' _ => ?_
    split_ifs <;> simp_all
  simp only [hsq]
  rw [sum_comm]
  refine (sum_congr rfl fun _ _ => sum_comm).trans ?_
  simp only [sum_boole]
  have hrow (t : F) : ∑ t' : F,
      ((#{xu ∈ seeds m F | xu.1 + t • xu.2 ∈ A ∧ xu.1 + t' • xu.2 ∈ A} : ℕ) : ℝ) =
        #A * ((Fintype.card F : ℝ) ^ m - 1) + (Fintype.card F - 1) * (#A * #A - #A) := by
    rw [← Nat.cast_sum, hdiagN t, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos), Nat.cast_sub Fintype.card_pos,
      Nat.cast_sub (Nat.le_mul_self _)]
    simp
  rw [sum_congr rfl fun t _ => hrow t, sum_const, card_univ, nsmul_eq_mul]
  ring

/-- The centered second moment of `lineAgree A` over `seeds m F`. -/
private theorem sum_lineAgree_sub_sq_le (A : Finset (Fin m → F)) :
    ∑ xu ∈ seeds m F,
        ((lineAgree A xu.1 xu.2 : ℝ) - Fintype.card F * #A / Fintype.card F ^ m) ^ 2 ≤
      Fintype.card F * #A * (Fintype.card F ^ m - 1) := by
  set q : ℝ := (Fintype.card F : ℝ)
  set Q : ℝ := (Fintype.card F : ℝ) ^ m
  set a : ℝ := (#A : ℝ)
  set μ := q * a / Q
  have hQpos : (0 : ℝ) < Q := by positivity
  have haQ : a ≤ Q := by
    have := card_le_univ A; rw [Fintype.card_fun, Fintype.card_fin] at this
    simp only [a, Q]; exact_mod_cast this
  have hq1 : (1 : ℝ) ≤ q := by simp only [q]; exact_mod_cast Fintype.card_pos
  let N : (Fin m → F) × (Fin m → F) → ℝ := fun xu => lineAgree A xu.1 xu.2
  have hcardS : (#(seeds m F) : ℝ) = Q * (Q - 1) := by
    rw [card_seeds, Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos)]; simp [Q]
  have hexp : ∑ xu ∈ seeds m F, (N xu - μ) ^ 2 =
      ∑ xu ∈ seeds m F, N xu ^ 2 - 2 * μ * ∑ xu ∈ seeds m F, N xu + μ ^ 2 * #(seeds m F) := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← sum_mul,
      ← mul_sum]
    ring
  change ∑ xu ∈ seeds m F, (N xu - μ) ^ 2 ≤ q * a * (Q - 1)
  rw [hexp, sum_lineAgree_seeds A, sum_lineAgree_sq_seeds A, hcardS]
  change q * (a * (Q - 1)) + q * (q - 1) * (a * a - a) - 2 * μ * (q * (a * (Q - 1))) +
      μ ^ 2 * (Q * (Q - 1)) ≤ q * a * (Q - 1)
  simp only [μ]
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ a by positivity) with ha0 | hapos
  · rw [← ha0]; field_simp; nlinarith
  have ha1 : 1 ≤ a := by
    have : 0 < #A := by simp only [a] at hapos; exact_mod_cast hapos
    simp only [a]; exact_mod_cast this
  have h₀ : (q - 1) * (a - 1) * Q ≤ q * a * (Q - 1) := by nlinarith
  have key : q * (q - 1) * (a * a - a) * Q ≤ q * q * a * a * (Q - 1) :=
    calc q * (q - 1) * (a * a - a) * Q = q * a * ((q - 1) * (a - 1) * Q) := by ring
      _ ≤ q * a * (q * a * (Q - 1)) := mul_le_mul_of_nonneg_left h₀ (by positivity)
      _ = _ := by ring
  have hfin : q * (q - 1) * (a * a - a) ≤ q * q * a * a * (Q - 1) / Q :=
    (le_div_iff₀ hQpos).2 (by linarith)
  have e1 : (q * a / Q) ^ 2 * (Q * (Q - 1)) = q * q * a * a * (Q - 1) / Q := by field_simp
  have e2 : 2 * (q * a / Q) * (q * (a * (Q - 1))) = 2 * (q * q * a * a * (Q - 1) / Q) := by
    field_simp
  rw [e1, e2]; linarith

/-- **Random lines sample a set well.** Over all points `x` and nonzero directions `u`, the
number of pairs for which the line `t ↦ x + t • u` has at most `D` points in `A` is at most
`q * a * (Q - 1) / (μ - D) ^ 2`, where `a = #A`, `Q = q ^ m` and `μ = q * a / Q > D` is the mean
number of points of a line in `A`. -/
theorem card_filter_lineAgree_le_mul_sq_le (A : Finset (Fin m → F)) {D : ℝ}
    (hD : D < Fintype.card F * #A / Fintype.card F ^ m) :
    (#{xu : (Fin m → F) × (Fin m → F) | xu.2 ≠ 0 ∧ (lineAgree A xu.1 xu.2 : ℝ) ≤ D} : ℝ) *
        (Fintype.card F * #A / Fintype.card F ^ m - D) ^ 2 ≤
      Fintype.card F * #A * (Fintype.card F ^ m - 1) := by
  have hfilter : ({xu : (Fin m → F) × (Fin m → F) |
      xu.2 ≠ 0 ∧ (lineAgree A xu.1 xu.2 : ℝ) ≤ D} : Finset _) =
      {xu ∈ seeds m F | (lineAgree A xu.1 xu.2 : ℝ) ≤ D} := by rw [seeds, filter_filter]
  rw [hfilter]
  refine (card_filter_mul_le_sum _ _ _ (fun _ _ => sq_nonneg _) fun xu _ hxu => ?_).trans
    (sum_lineAgree_sub_sq_le A)
  nlinarith [sq_nonneg ((lineAgree A xu.1 xu.2 : ℝ) - Fintype.card F * #A / Fintype.card F ^ m)]

/-! ### The decoder -/

/-- **The local list decoder with advice.** To decode at `x` with advice `a` at `z`: parametrize
the line through `x` and `z` as `t ↦ x + t • v`, with `v` the normalization of `z - x`, and run
Sudan decoding with the hint `a` at the position `c = firstNonzero (z - x)` of `z` on the
restriction of `g` to the line. -/
noncomputable def lineListDecode (g : (Fin m → F) → F) (d D : ℕ) (z : Fin m → F) (a : F)
    (x : Fin m → F) : F :=
  hintDecode id (fun t : F => g (x + t • (firstNonzero (z - x))⁻¹ • (z - x))) d D
    (firstNonzero (z - x)) a

/-- Scaling the direction by a nonzero constant does not change the number of points of a line in
a set. -/
theorem lineAgree_smul (A : Finset (Fin m → F)) (x u : Fin m → F) {c : F} (hc : c ≠ 0) :
    lineAgree A x (c • u) = lineAgree A x u := by
  refine card_nbij' (fun t => t * c) (fun t => t * c⁻¹) (fun t ht => ?_) (fun t ht => ?_)
    (fun t _ => by simp [hc]) (fun t _ => by simp [hc])
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
    rwa [mul_smul]
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
    rwa [smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]

/-- **The decoder at a pair of points.** For `z ≠ x`, with `c = firstNonzero (z - x)` and
`v = c⁻¹ • (z - x)`, the decoder with advice `p z` is Sudan decoding with the hint `p (x + c • v)`
at `c` on the line `t ↦ x + t • v`. -/
theorem lineListDecode_eq (g p : (Fin m → F) → F) (d D : ℕ) {x z : Fin m → F} (hxz : z ≠ x) :
    lineListDecode g d D z (p z) x =
      hintDecode id (fun t : F => g (x + t • (firstNonzero (z - x))⁻¹ • (z - x))) d D
        (firstNonzero (z - x))
        (p (x + firstNonzero (z - x) • (firstNonzero (z - x))⁻¹ • (z - x))) := by
  rw [firstNonzero_smul_inv_smul (sub_ne_zero.2 hxz), add_sub_cancel]
  rfl

/-- **Few bad hint positions on a good line.** If the line `t ↦ x + t • v` has more than `D`
points where `g` agrees with the Reed–Muller codeword `p`, then Sudan decoding with the hint
`p (x + τ • v)` at `τ` returns `p x` for all but at most `D - d` positions `τ`. -/
private theorem card_hintDecode_line_ne_le {d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card F < #(Sudan.monomials d D)) (hDq : D < Fintype.card F)
    {p : (Fin m → F) → F} (hp : p ∈ reedMuller F m d) (g : (Fin m → F) → F) (x v : Fin m → F)
    (hagree : D < lineAgree {y | g y = p y} x v) :
    #{τ | hintDecode id (fun t : F => g (x + t • v)) d D τ (p (x + τ • v)) ≠ p x} ≤ D - d := by
  obtain ⟨P, hP, hPeval⟩ := exists_natDegree_le_eval_eq_of_mem_reedMuller hp x v
  have hx : p x = P.eval 0 := by rw [hPeval, zero_smul, add_zero]
  have hag : #{t : F | P.eval (id t) = g (x + t • v)} = lineAgree {y | g y = p y} x v := by
    unfold lineAgree
    congr 1
    ext t
    simp [hPeval, eq_comm]
  have h := card_hintDecode_ne_le (α := id) (w := fun t : F => g (x + t • v))
    Function.injective_id hd hn hDq hP (by rw [hag]; exact hagree)
  simp only [← hPeval, hx]
  exact h

/-- The normalized directions: those whose first nonzero entry is `1`. -/
private def normDirs (m : ℕ) (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Finset (Fin m → F) := univ.filter fun v => firstNonzero v = 1

/-- There are at most `(Q - 1) / (q - 1)` normalized directions. -/
private theorem card_normDirs_mul_le :
    #(normDirs m F) * (Fintype.card F - 1) ≤ Fintype.card F ^ m - 1 := by
  have h := card_le_card_of_injOn (s := normDirs m F ×ˢ (univ.erase (0 : F)))
    (t := (univ : Finset (Fin m → F)).erase 0) (fun vc => vc.2 • vc.1) (fun vc hvc => by
      simp only [coe_product, Set.mem_prod, mem_coe, normDirs, mem_filter, mem_univ, true_and,
        mem_erase, ne_eq, and_true] at hvc ⊢
      intro h0
      rcases smul_eq_zero.1 h0 with h0 | h0
      · exact hvc.2 h0
      · rw [h0] at hvc
        simp [firstNonzero, firstFlags] at hvc) (fun vc hvc vc' hvc' heq => by
      simp only [coe_product, Set.mem_prod, mem_coe, normDirs, mem_filter, mem_univ, true_and,
        mem_erase, ne_eq, and_true] at hvc hvc'
      have hc : vc.2 = vc'.2 := by
        have := congrArg firstNonzero heq
        simp only [firstNonzero_smul, hvc.1, hvc'.1, mul_one] at this
        exact this
      have := congrArg (fun u => vc.2⁻¹ • u) heq
      simp only [smul_smul, hc, inv_mul_cancel₀ hvc'.2, one_smul] at this
      exact Prod.ext this hc)
  rwa [card_product, card_erase_of_mem (mem_univ _), card_erase_of_mem (mem_univ _), card_univ,
    card_univ, Fintype.card_fun, Fintype.card_fin] at h

/-- For a fixed `x`, at most `#(normDirs m F) * (D - d)` points `z ≠ x` lie on a line through `x`
with more than `D` agreements yet make `lineListDecode` fail at `x`. -/
private theorem card_filter_lineListDecode_ne_of_lt_lineAgree_le {d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card F < #(Sudan.monomials d D)) (hDq : D < Fintype.card F)
    {p : (Fin m → F) → F} (hp : p ∈ reedMuller F m d) (g : (Fin m → F) → F) (x : Fin m → F) :
    #{z | z ≠ x ∧ D < lineAgree {y | g y = p y} x (z - x) ∧
      lineListDecode g d D z (p z) x ≠ p x} ≤ #(normDirs m F) * (D - d) := by
  set A : Finset (Fin m → F) := {y | g y = p y}
  let bad (v : Fin m → F) : Finset F :=
    {τ | hintDecode id (fun t : F => g (x + t • v)) d D τ (p (x + τ • v)) ≠ p x}
  calc #{z | z ≠ x ∧ D < lineAgree A x (z - x) ∧ lineListDecode g d D z (p z) x ≠ p x}
      ≤ #(((normDirs m F).filter (fun v => D < lineAgree A x v)).sigma bad) := by
        refine card_le_card_of_injOn
          (fun z => ⟨(firstNonzero (z - x))⁻¹ • (z - x), firstNonzero (z - x)⟩)
          (fun z hz => ?_) (fun z hz z' hz' heq => ?_)
        · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hz
          obtain ⟨hne, hD, hdec⟩ := hz
          have hl : firstNonzero (z - x) ≠ 0 :=
            firstNonzero_eq_zero_iff.not.2 (sub_ne_zero.2 hne)
          simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, normDirs, mem_univ,
            true_and, bad]
          rw [lineListDecode_eq g p d D hne] at hdec
          exact ⟨⟨by rw [firstNonzero_smul, inv_mul_cancel₀ hl],
            by rwa [lineAgree_smul A _ _ (inv_ne_zero hl)]⟩, hdec⟩
        · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hz hz'
          have e1 := firstNonzero_smul_inv_smul (sub_ne_zero.2 hz.1)
          have e2 := firstNonzero_smul_inv_smul (sub_ne_zero.2 hz'.1)
          have h1 := congrArg Sigma.fst heq
          have h2 := congrArg Sigma.snd heq
          simp only at h1 h2
          have hsub : z - x = z' - x := by rw [← e1, h1, h2, e2]
          exact sub_left_injective hsub
    _ = ∑ v ∈ (normDirs m F).filter (fun v => D < lineAgree A x v), #(bad v) := card_sigma _ _
    _ ≤ ∑ v ∈ (normDirs m F).filter (fun v => D < lineAgree A x v), (D - d) :=
        sum_le_sum fun v hv => card_hintDecode_line_ne_le hd hn hDq hp g x v (mem_filter.1 hv).2
    _ ≤ #(normDirs m F) * (D - d) := by
        rw [sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (card_filter_le _ _)

/-- Over all pairs `(x, z)`, the number of pairs where `lineListDecode` fails is at most the
diagonal (`q ^ m`), plus the pairs on lines with at most `D` agreements, plus at most
`q ^ m * #(normDirs m F) * (D - d)` pairs on good lines with a bad hint position. -/
private theorem sum_card_filter_lineListDecode_ne_le {d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card F < #(Sudan.monomials d D)) (hDq : D < Fintype.card F)
    {p : (Fin m → F) → F} (hp : p ∈ reedMuller F m d) (g : (Fin m → F) → F) :
    ∑ z : Fin m → F, #{x | lineListDecode g d D z (p z) x ≠ p x} ≤
      Fintype.card F ^ m +
        #{xu : (Fin m → F) × (Fin m → F) |
          xu.2 ≠ 0 ∧ (lineAgree {y | g y = p y} xu.1 xu.2 : ℝ) ≤ (D : ℝ)} +
        Fintype.card F ^ m * (#(normDirs m F) * (D - d)) := by
  set A : Finset (Fin m → F) := {y | g y = p y}
  have hswap : (∑ z : Fin m → F, #{x | lineListDecode g d D z (p z) x ≠ p x}) =
      ∑ x : Fin m → F, #{z | lineListDecode g d D z (p z) x ≠ p x} := by
    simp only [card_eq_sum_ones, sum_filter]; exact sum_comm
  have hpt (x : Fin m → F) : #{z | lineListDecode g d D z (p z) x ≠ p x} ≤
      1 + #{u : Fin m → F | u ≠ 0 ∧ (lineAgree A x u : ℝ) ≤ (D : ℝ)} +
        #(normDirs m F) * (D - d) := by
    have hsub : ({z | lineListDecode g d D z (p z) x ≠ p x} : Finset _) ⊆
        ({x} : Finset _) ∪ ({z | z ≠ x ∧ lineAgree A x (z - x) ≤ D} : Finset _) ∪
          ({z | z ≠ x ∧ D < lineAgree A x (z - x) ∧
            lineListDecode g d D z (p z) x ≠ p x} : Finset _) := by
      intro z hz
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton] at hz ⊢
      by_cases hzx : z = x; · exact Or.inl (Or.inl hzx)
      by_cases hlow : lineAgree A x (z - x) ≤ D; · exact Or.inl (Or.inr ⟨hzx, hlow⟩)
      exact Or.inr ⟨hzx, not_le.1 hlow, hz⟩
    have hshift : #{z | z ≠ x ∧ lineAgree A x (z - x) ≤ D} =
        #{u : Fin m → F | u ≠ 0 ∧ (lineAgree A x u : ℝ) ≤ (D : ℝ)} := by
      simp only [card_eq_sum_ones, sum_filter]
      exact Fintype.sum_equiv (Equiv.subRight x) _ _ fun z => by
        simp [Equiv.subRight_apply, sub_ne_zero]
    calc #{z | lineListDecode g d D z (p z) x ≠ p x}
        ≤ #({x} : Finset _) + #{z | z ≠ x ∧ lineAgree A x (z - x) ≤ D} +
            #{z | z ≠ x ∧ D < lineAgree A x (z - x) ∧ lineListDecode g d D z (p z) x ≠ p x} :=
          (card_le_card hsub).trans
            ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
      _ ≤ 1 + #{u : Fin m → F | u ≠ 0 ∧ (lineAgree A x u : ℝ) ≤ (D : ℝ)} +
            #(normDirs m F) * (D - d) := by
          rw [card_singleton, hshift]
          exact Nat.add_le_add_left
            (card_filter_lineListDecode_ne_of_lt_lineAgree_le hd hn hDq hp g x) _
  have hS₂ : (∑ x : Fin m → F, #{u : Fin m → F | u ≠ 0 ∧ (lineAgree A x u : ℝ) ≤ (D : ℝ)}) =
      #{xu : (Fin m → F) × (Fin m → F) | xu.2 ≠ 0 ∧ (lineAgree A xu.1 xu.2 : ℝ) ≤ (D : ℝ)} := by
    simp only [card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  rw [hswap]; refine (sum_le_sum fun x _ => hpt x).trans ?_
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul,
    mul_one, hS₂, le_rfl]

/-- In `ℝ`, the number of normalized directions is at most `(q ^ m - 1) / (q - 1)`. -/
private theorem card_normDirs_le_real :
    (#(normDirs m F) : ℝ) ≤ ((Fintype.card F : ℝ) ^ m - 1) / (Fintype.card F - 1) := by
  have hq1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  rw [le_div_iff₀ (by linarith)]
  have h := card_normDirs_mul_le (m := m) (F := F)
  have h1 : ((Fintype.card F - 1 : ℕ) : ℝ) = Fintype.card F - 1 := by
    rw [Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  have h2 : ((Fintype.card F ^ m - 1 : ℕ) : ℝ) = (Fintype.card F : ℝ) ^ m - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos), Nat.cast_pow, Nat.cast_one]
  rw [← h1, ← h2]; exact_mod_cast h

/-- **Local list decoding of Reed–Muller codes**, a variant of [SudanTrevisanVadhan2001]. Let
`p` be a codeword of the Reed–Muller code of degree `d ≥ 1` in `m` variables over a field with `q`
elements, `Q = q ^ m`, and let `g` agree with `p` on `a` points. Let `D < q` be such that there
are more than `q` monomials of `(1, d)`-weighted degree at most `D`, and suppose
`D < μ = q * a / Q`. Then for some advice point `z`, the decoder `lineListDecode g d D z (p z)`
computes `p` at all but
`1 + (q * a * (Q - 1) / (μ - D) ^ 2 + Q * (Q - 1) * (D - d) / (q - 1)) / Q` points. -/
theorem exists_card_lineListDecode_ne_le {d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card F < #(Sudan.monomials d D)) (hDq : D < Fintype.card F)
    {p : (Fin m → F) → F} (hp : p ∈ reedMuller F m d) (g : (Fin m → F) → F)
    (hμ : (D : ℝ) < Fintype.card F * #{y | g y = p y} / Fintype.card F ^ m) :
    ∃ z, (#{x | lineListDecode g d D z (p z) x ≠ p x} : ℝ) ≤
      1 + (Fintype.card F * #{y | g y = p y} * (Fintype.card F ^ m - 1) /
          (Fintype.card F * #{y | g y = p y} / Fintype.card F ^ m - D) ^ 2 +
        Fintype.card F ^ m * (Fintype.card F ^ m - 1) * (D - d : ℕ) / (Fintype.card F - 1)) /
          Fintype.card F ^ m := by
  set A : Finset (Fin m → F) := {y | g y = p y}
  set q : ℝ := (Fintype.card F : ℝ)
  set Q : ℝ := (Fintype.card F : ℝ) ^ m
  set μ := q * #A / Q
  have hQpos : (0 : ℝ) < Q := by positivity
  have hμD : 0 < μ - D := by linarith
  have hlow : (#{xu : (Fin m → F) × (Fin m → F) |
      xu.2 ≠ 0 ∧ (lineAgree A xu.1 xu.2 : ℝ) ≤ (D : ℝ)} : ℝ) ≤
      q * #A * (Q - 1) / (μ - D) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    exact card_filter_lineAgree_le_mul_sq_le A hμ
  have hbad : Q * (#(normDirs m F) * (D - d : ℕ)) ≤ Q * (Q - 1) * (D - d : ℕ) / (q - 1) := by
    rw [mul_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hQpos.le
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right (card_normDirs_le_real (m := m) (F := F)) (by positivity)
  have htot : (∑ z : Fin m → F, (#{x | lineListDecode g d D z (p z) x ≠ p x} : ℝ)) ≤
      Q + (#{xu : (Fin m → F) × (Fin m → F) |
        xu.2 ≠ 0 ∧ (lineAgree A xu.1 xu.2 : ℝ) ≤ (D : ℝ)} : ℝ) +
        Q * (#(normDirs m F) * (D - d : ℕ)) := by
    have hle := Nat.cast_le (α := ℝ).2 (sum_card_filter_lineListDecode_ne_le hd hn hDq hp g)
    simpa [Q] using hle
  have hsum : (∑ z : Fin m → F, (#{x | lineListDecode g d D z (p z) x ≠ p x} : ℝ)) ≤
      Q * (1 + (q * #A * (Q - 1) / (μ - D) ^ 2 +
        Q * (Q - 1) * (D - d : ℕ) / (q - 1)) / Q) := by
    calc (∑ z : Fin m → F, (#{x | lineListDecode g d D z (p z) x ≠ p x} : ℝ))
        ≤ Q + q * #A * (Q - 1) / (μ - D) ^ 2 + Q * (Q - 1) * (D - d : ℕ) / (q - 1) := by linarith
      _ = Q * (1 + (q * #A * (Q - 1) / (μ - D) ^ 2 +
            Q * (Q - 1) * (D - d : ℕ) / (q - 1)) / Q) := by
          rw [mul_add, mul_one, mul_div_cancel₀ _ hQpos.ne']; ring
  obtain ⟨z, -, hz⟩ := exists_le_of_sum_le (s := (univ : Finset (Fin m → F))) univ_nonempty
    (f := fun z => (#{x | lineListDecode g d D z (p z) x ≠ p x} : ℝ))
    (g := fun _ => 1 + (q * #A * (Q - 1) / (μ - D) ^ 2 +
      Q * (Q - 1) * (D - d : ℕ) / (q - 1)) / Q) (by
      rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast; exact hsum)
  exact ⟨z, hz⟩

end Cslib.Code
