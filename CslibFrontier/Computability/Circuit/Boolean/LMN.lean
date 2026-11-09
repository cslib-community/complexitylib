/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Hastad
public import CslibFrontier.Foundations.BooleanAnalysis.FourierRestriction
import CslibFrontier.Computability.DecisionTree.Fourier
import CslibFrontier.Foundations.Combinatorics.Hypergeometric
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Linial–Mansour–Nisan theorem

A function computed by a small circuit of constant depth with unbounded fan-in has almost all of
its Fourier weight on small sets of coordinates [LinialMansourNisan1993],
[O'Donnell, Section 4.5][ODonnell2014]: for a circuit of depth `d` with `g` gates, `s ≥ 2` and
`n ≥ 1`, the weight on the sets of at least `k` coordinates is at most `2 g / 2 ^ s` once
`max 8 (2 s) n ≤ k ⌊n / (16 s + 1) ^ d⌋` (`Unbounded.sum_fourierCoeff_sq_le_of_computes`). For
fixed `d` it is `g 2 ^ (-Ω(k ^ (1 / (d + 1))))`: the exponent is weaker than the `k ^ (1 / d)` of
Linial, Mansour and Nisan, since depth counts every gate on a path, negations included, and each
stage leaves a `1 / (16 s + 1)` fraction of the free bits (as in
`Unbounded.two_pow_le_size_of_computes_parity`).

The proof draws a random set `J` of `ℓ = ⌊n / (16 s + 1) ^ d⌋` coordinates and fixes the others
to a random word `z`, a random restriction (partial assignment)
(`PartialAssignment.sum_card_filter_outside`). A set `U` of at least `k` coordinates meets `J` in at
least `s` of them for at least half of the `J` (`Cslib.two_mul_card_filter_card_inter_lt_le`), so
the weight on such `U` is at most twice the expected weight of the restriction on sets of at least
`s` coordinates (`BitString.expect_sum_fourierCoeff_piecewise_sq`). That is zero when the
restriction has a decision tree of depth below `s` (`DecisionTree.fourierCoeff_eq_zero_of_depth_lt`)
and at most one otherwise (Parseval), and the restriction is deep with probability at most
`g / 2 ^ s` (`Unbounded.two_pow_mul_card_filter_exists_not_shallow_le`).

## Main results

* `Cslib.Circuits.Boolean.Unbounded.sum_fourierCoeff_sq_le_of_computes`: the
  Linial–Mansour–Nisan theorem.
* `Cslib.Circuits.Boolean.Unbounded.sum_fourierCoeff_sq_le_of_computes_of_depth_le`: the bound
  above the explicit degree `2 max 8 (2 s) (16 s + 1) ^ d - 1`, for every number of inputs.

## References

* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset

variable {n : ℕ}

namespace Unbounded

open BitString
open scoped BigOperators

/-- The weight of a restriction of a `±1`-valued function on sets of at least `s` coordinates is
zero if the restriction is `s`-shallow, and at most one otherwise. -/
private theorem sum_fourierCoeff_sq_le_ite (f : BooleanFunction n) (J : Finset (Fin n))
    (z : BitString n) (s : ℕ) :
    ∑ S with s ≤ #S, fourierCoeff (fun x => signVal (f (J.piecewise x z))) S ^ 2 ≤
      if Shallow s (PartialAssignment.outside J z) f then 0 else 1 := by
  split_ifs with h
  · -- a decision tree of depth below `s` has no weight on sets of `s` coordinates
    obtain ⟨t, ht, hd⟩ := h.exists_tree
    refine (sum_eq_zero fun S hS => ?_).le
    have hfun : (fun x => signVal (f (J.piecewise x z))) = fun x => signVal (t.eval x) := by
      funext x
      rw [ht, PartialAssignment.fill_outside]
    rw [hfun, DecisionTree.fourierCoeff_eq_zero_of_depth_lt signVal t
      (hd.trans_le (mem_filter.1 hS).2)]
    simp
  · rw [← sum_fourierCoeff_sq_signVal fun x => f (J.piecewise x z)]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _

/-- For a fixed set `J` of free coordinates, the weight of a `±1`-valued function on the sets
meeting `J` in at least `s` coordinates is at most the fraction of the words `z` that leave `f`
deep when fixing the coordinates outside `J` to `z`. -/
private theorem sum_fourierCoeff_sq_le_card (f : BooleanFunction n) (J : Finset (Fin n)) (s : ℕ) :
    ∑ U with s ≤ #(U ∩ J), fourierCoeff (fun x => signVal (f x)) U ^ 2 ≤
      ((univ.filter fun z : BitString n =>
        ¬ Shallow s (PartialAssignment.outside J z) f).card : ℝ) / 2 ^ n := by
  rw [← expect_sum_fourierCoeff_piecewise_sq (fun x => signVal (f x)) J s]
  calc 𝔼 z, ∑ S with s ≤ #S, fourierCoeff (fun x => signVal (f (J.piecewise x z))) S ^ 2
      ≤ 𝔼 z : BitString n, (if Shallow s (PartialAssignment.outside J z) f then 0 else 1 : ℝ) :=
        expect_le_expect fun z _ => sum_fourierCoeff_sq_le_ite f J z s
    _ = _ := by
        rw [expect_eq_sum_div_card, sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul,
          mul_one]
        simp

/-- **The Linial–Mansour–Nisan theorem.** Let `f` be computed by a circuit of negations and
unbounded fan-in conjunctions and disjunctions of depth `d` with `g` gates, let `s ≥ 2` and
`n ≥ 1`, and let `ℓ = ⌊n / (16 s + 1) ^ d⌋`. Then the Fourier weight of `f`, read as `±1`, on the
sets of at least `k` coordinates is at most `2 g / 2 ^ s`, whenever `max 8 (2 s) n ≤ k ℓ`. -/
theorem sum_fourierCoeff_sq_le_of_computes {f : BooleanFunction n} {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single f)) {s : ℕ} (hs : 2 ≤ s) (hn0 : 0 < n) {k : ℕ}
    (hk : max 8 (2 * s) * n ≤ k * (n / (16 * s + 1) ^ C.depth)) :
    ∑ U with k ≤ #U, fourierCoeff (fun x => signVal (f x)) U ^ 2 ≤ 2 * C.size / 2 ^ s := by
  -- there is no weight on more than `n` coordinates
  rcases Nat.lt_or_ge n k with hkn | hkn
  · rw [sum_eq_zero fun U hU => absurd ((mem_filter.1 hU).2.trans (card_le_univ U))
      (by simpa using hkn)]
    positivity
  set ℓ := n / (16 * s + 1) ^ C.depth
  have hsℓ : s ≤ ℓ := by
    have h : n * (2 * s) ≤ n * ℓ :=
      calc n * (2 * s) = 2 * s * n := by ring
        _ ≤ max 8 (2 * s) * n := Nat.mul_le_mul_right _ (le_max_right _ _)
        _ ≤ k * ℓ := hk
        _ ≤ n * ℓ := Nat.mul_le_mul_right _ hkn
    have := Nat.le_of_mul_le_mul_left h hn0
    omega
  have hn : s * (16 * s + 1) ^ C.depth ≤ n :=
    (Nat.le_div_iff_mul_le (Nat.pow_pos (by omega))).1 hsℓ
  set P := (univ : Finset (Fin n)).powersetCard ℓ
  set N := n.choose ℓ
  set a : Finset (Fin n) → ℝ := fun U => fourierCoeff (fun x => signVal (f x)) U ^ 2
  set bad := (PartialAssignment.withFree (Fin n) ℓ).filter fun ρ => ¬ Shallow s ρ f
  have ha : ∀ U, 0 ≤ a U := fun U => by simp only [a]; positivity
  have hℓn : ℓ ≤ n := Nat.div_le_self _ _
  have hN : 0 < N := Nat.choose_pos hℓn
  -- the counted stages: few restrictions leave the output deep
  have hbad : 2 ^ s * bad.card ≤ C.size * (PartialAssignment.withFree (Fin n) ℓ).card := by
    have h := two_pow_mul_card_filter_exists_not_shallow_le (p := C.program) hs hn C.depth le_rfl
    refine (Nat.mul_le_mul_left _ (card_le_card fun ρ hρ => ?_)).trans
      (h.trans (Nat.mul_le_mul_right _ ((card_filter_le _ _).trans (by simp))))
    obtain ⟨hρW, hdeep⟩ := mem_filter.1 hρ
    refine mem_filter.2 ⟨hρW, ?_⟩
    have hf : f = fun x => C.program.trace interpretation x (C.outputs 0) :=
      funext fun x => (congrFun (hC x) 0).symm
    rw [hf] at hdeep
    by_contra hall
    push Not at hall
    exact hdeep (shallow_output hs hall)
  -- the weight on sets meeting a random `J` in at least `s` coordinates
  have hupper : ∑ J ∈ P, ∑ U with s ≤ #(U ∩ J), a U ≤ (2 ^ ℓ * bad.card : ℝ) / 2 ^ n := by
    calc ∑ J ∈ P, ∑ U with s ≤ #(U ∩ J), a U
        ≤ ∑ J ∈ P, ((univ.filter fun z : BitString n =>
            ¬ Shallow s (PartialAssignment.outside J z) f).card : ℝ) / 2 ^ n :=
          sum_le_sum fun J _ => sum_fourierCoeff_sq_le_card f J s
      _ = (2 ^ ℓ * bad.card : ℝ) / 2 ^ n := by
          rw [← sum_div]
          congr 1
          exact_mod_cast PartialAssignment.sum_card_filter_outside (fun ρ => ¬ Shallow s ρ f) ℓ
  -- for the sets of at least `k` coordinates, at least half of the `J` meet them in `s`
  have hlower : (N : ℝ) / 2 * ∑ U with k ≤ #U, a U ≤ ∑ J ∈ P, ∑ U with s ≤ #(U ∩ J), a U := by
    have hswap : ∑ J ∈ P, ∑ U with s ≤ #(U ∩ J), a U =
        ∑ U, a U * (P.filter fun J => s ≤ #(U ∩ J)).card := by
      simp only [sum_filter]
      rw [sum_comm]
      refine sum_congr rfl fun U _ => ?_
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    rw [hswap, mul_sum, sum_filter]
    refine sum_le_sum fun U _ => ?_
    split_ifs with hU
    · have hcount := two_mul_card_filter_card_inter_lt_le (s := univ) (U := U) (ℓ := ℓ)
        (m := s) (subset_univ U) (by simpa using hn0)
        (by
          have : 8 * n ≤ k * ℓ := (Nat.mul_le_mul_right _ (le_max_left _ _)).trans hk
          simpa using this.trans (Nat.mul_le_mul_right _ hU))
        (by
          have : 2 * s * n ≤ k * ℓ := (Nat.mul_le_mul_right _ (le_max_right _ _)).trans hk
          simpa using this.trans (Nat.mul_le_mul_right _ hU))
      have hcount' : 2 * (P.filter fun J => #(U ∩ J) < s).card ≤ N := by
        simpa [P, N] using hcount
      have hsplit := card_filter_add_card_filter_not (s := P) (fun J => s ≤ #(U ∩ J))
      have hPN : P.card = N := by simp [P, N]
      have hneg : (P.filter fun J => ¬ s ≤ #(U ∩ J)) = P.filter fun J => #(U ∩ J) < s := by
        congr 1
        ext J
        simp
      rw [hneg, hPN] at hsplit
      have h2 : (N : ℝ) ≤ 2 * (P.filter fun J => s ≤ #(U ∩ J)).card := by
        have : N ≤ 2 * (P.filter fun J => s ≤ #(U ∩ J)).card := by omega
        exact_mod_cast this
      nlinarith [ha U]
    · exact mul_nonneg (ha U) (Nat.cast_nonneg _)
  -- combine: `N / 2 · W ≤ 2 ^ ℓ #bad / 2 ^ n ≤ g N / 2 ^ s`
  have hW := hlower.trans hupper
  have hbadR : (2 ^ s : ℝ) * bad.card ≤ C.size * (N * 2 ^ (n - ℓ)) := by
    have := hbad
    rw [PartialAssignment.card_withFree, Fintype.card_fin] at this
    exact_mod_cast this
  have h2n : (2 : ℝ) ^ ℓ * 2 ^ (n - ℓ) = 2 ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' hℓn]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : (0 : ℝ) < 2 ^ s := by positivity
  have hpown : (0 : ℝ) < 2 ^ n := by positivity
  have hpowℓ : (0 : ℝ) < 2 ^ ℓ := by positivity
  rw [le_div_iff₀ hpow]
  have key : (N : ℝ) / 2 * (∑ U with k ≤ #U, a U) * 2 ^ s ≤ C.size * N := by
    have h1 : (N : ℝ) / 2 * (∑ U with k ≤ #U, a U) * 2 ^ n ≤ 2 ^ ℓ * bad.card := by
      rwa [le_div_iff₀ hpown] at hW
    have h3 : (2 : ℝ) ^ ℓ * bad.card * 2 ^ s ≤ 2 ^ ℓ * (C.size * (N * 2 ^ (n - ℓ))) := by
      nlinarith
    have h4 : (N : ℝ) / 2 * (∑ U with k ≤ #U, a U) * 2 ^ s * 2 ^ n ≤ C.size * N * 2 ^ n := by
      calc (N : ℝ) / 2 * (∑ U with k ≤ #U, a U) * 2 ^ s * 2 ^ n
          = (N / 2 * (∑ U with k ≤ #U, a U) * 2 ^ n) * 2 ^ s := by ring
        _ ≤ 2 ^ ℓ * bad.card * 2 ^ s := by gcongr
        _ ≤ 2 ^ ℓ * (C.size * (N * 2 ^ (n - ℓ))) := h3
        _ = C.size * N * (2 ^ ℓ * 2 ^ (n - ℓ)) := by ring
        _ = C.size * N * 2 ^ n := by rw [h2n]
    exact le_of_mul_le_mul_right h4 hpown
  nlinarith

/-- **The Linial–Mansour–Nisan theorem above an explicit degree.** Let `f` be computed by a
circuit of negations and unbounded fan-in conjunctions and disjunctions of depth at most `d`, and
let `s ≥ 2`. Then the Fourier weight of `f`, read as signs, on the sets of more than `t`
coordinates is at most `2 g / 2 ^ s`, where `g` is the number of gates, whenever
`2 max 8 (2 s) (16 s + 1) ^ d ≤ t + 1`. -/
theorem sum_fourierCoeff_sq_le_of_computes_of_depth_le {f : BooleanFunction n}
    {C : Circuit signature n 1} (hC : C.Computes interpretation (single f)) {s d t : ℕ}
    (hs : 2 ≤ s) (hd : C.depth ≤ d) (ht : 2 * max 8 (2 * s) * (16 * s + 1) ^ d ≤ t + 1) :
    ∑ U with t < #U, fourierCoeff (fun x => signVal (f x)) U ^ 2 ≤ 2 * C.size / 2 ^ s := by
  set q := (16 * s + 1) ^ C.depth
  set M := max 8 (2 * s)
  have hq : 0 < q := by positivity
  have hqd : q ≤ (16 * s + 1) ^ d := Nat.pow_le_pow_right (by omega) hd
  have hMq : 2 * M * q ≤ t + 1 := (Nat.mul_le_mul_left _ hqd).trans ht
  have hM : 8 ≤ M := le_max_left _ _
  rcases Nat.lt_or_ge n q with hnq | hqn
  · -- every set has at most `n ≤ t` coordinates
    have htn : n ≤ t := by nlinarith
    rw [sum_eq_zero fun U hU => absurd ((mem_filter.1 hU).2.trans_le
      ((card_le_univ U).trans (by simpa using htn))) (lt_irrefl t)]
    positivity
  · have hr : 1 ≤ n / q := Nat.div_pos hqn hq
    have hk : M * n ≤ (t + 1) * (n / q) :=
      calc M * n ≤ M * (q * (n / q + 1)) :=
            Nat.mul_le_mul_left _ (Nat.lt_mul_div_succ n hq).le
        _ ≤ M * (q * (2 * (n / q))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
        _ = 2 * M * q * (n / q) := by ring
        _ ≤ (t + 1) * (n / q) := Nat.mul_le_mul_right _ hMq
    simpa only [Nat.add_one_le_iff] using
      sum_fourierCoeff_sq_le_of_computes hC hs (hq.trans_le hqn) hk

end Unbounded

end Cslib.Circuits.Boolean
