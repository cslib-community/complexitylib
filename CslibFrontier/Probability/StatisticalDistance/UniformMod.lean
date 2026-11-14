/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StatisticalDistance
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.ZMod.Basic

/-!
# Reducing a uniform value modulo `q`

A uniform value below `N`, read in `ZMod q`, is close to uniform: each residue has `⌊N / q⌋` or
`⌊N / q⌋ + 1` preimages, so the statistical distance to the uniform distribution on `ZMod q` is at
most `(N mod q) / N`, and hence at most `q / N` (`dist_map_natCast_uniformOfFintype_le`). With
`N = 2 ^ ℓ` fair bits this gives an efficient approximately uniform sampler for `ZMod q`, with
distance at most `q / 2 ^ ℓ`; strict PPT machines cannot sample `ZMod q` exactly when `q` is not
a power of two.

## Main results

* `Cslib.Probability.PMF.uniformOfFintype_fin_bind`: for nonzero `M`, uniform draws from `Fin M`
  and `ZMod M` agree.
* `Cslib.Probability.PMF.dist_map_natCast_uniformOfFintype_le`: distance at most `(N mod q) / N`.
* `Cslib.Probability.PMF.dist_map_natCast_uniformOfFintype_le_div`: distance at most `q / N`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 3.11.
-/

public section

namespace Cslib.Probability.PMF

/-- A uniform draw from `Fin M` is a uniform draw from `ZMod M`, read through `val`. -/
theorem uniformOfFintype_fin_bind {α : Type*} (M : ℕ) [NeZero M] (f : ℕ → PMF α) :
    ((PMF.uniformOfFintype (Fin M)).bind fun i => f i.val) =
      (PMF.uniformOfFintype (ZMod M)).bind fun r => f r.val := by
  rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne M) with ⟨m, rfl⟩
  rfl

/-- The mass of a residue: `⌊N / q⌋` preimages, plus one for the residues below `N mod q`. -/
private theorem toReal_map_natCast_apply (N q : ℕ) [NeZero N] [NeZero q] (r : ZMod q) :
    (((PMF.uniformOfFintype (Fin N)).map fun x => (x.val : ZMod q)) r).toReal =
      ((N / q + if r.val < N % q then 1 else 0 : ℕ) : ℝ) / N := by
  classical
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum fun x _ => by
    split <;> simp [PMF.uniformOfFintype_apply, NeZero.ne N]]
  have hfilter : (Finset.range N).filter (fun k => ((k : ℕ) : ZMod q) = r) =
      (Finset.range N).filter (fun k => k ≡ r.val [MOD q]) :=
    Finset.filter_congr fun k _ => by
      rw [show ((k : ℕ) : ZMod q) = r ↔ ((k : ℕ) : ZMod q) = ((r.val : ℕ) : ZMod q) by
        rw [ZMod.natCast_zmod_val], ZMod.natCast_eq_natCast_iff']
      rfl
  have hfin : (∑ x : Fin N, if ((x : ℕ) : ZMod q) = r then (1 : ℝ) else 0) =
      ((N / q + if r.val < N % q then 1 else 0 : ℕ) : ℝ) := by
    have hcount := Nat.count_modEq_card (b := N) (NeZero.pos q) r.val
    rw [Nat.mod_eq_of_lt (ZMod.val_lt r)] at hcount
    rw [← hcount, Nat.count_eq_card_filter_range, ← hfilter,
      Fin.sum_univ_eq_sum_range (fun k => if ((k : ℕ) : ZMod q) = r then (1 : ℝ) else 0) N,
      Finset.sum_boole]
  rw [← hfin, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : ((x : ℕ) : ZMod q) = r
  · simp [h, PMF.uniformOfFintype_apply]
  · simp [h, Ne.symm h]

/-- **A uniform value reduced modulo `q`.** A uniform value below `N`, read in `ZMod q`, is within
statistical distance `(N mod q) / N` of the uniform distribution on `ZMod q`. -/
theorem dist_map_natCast_uniformOfFintype_le (N q : ℕ) [NeZero N] [NeZero q] :
    dist ((PMF.uniformOfFintype (Fin N)).map fun x => (x.val : ZMod q))
      (PMF.uniformOfFintype (ZMod q)) ≤ (N % q : ℕ) / N := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hdiv : (N : ℝ) = q * (N / q : ℕ) + (N % q : ℕ) := by
    exact_mod_cast (Nat.div_add_mod N q).symm
  have hterm (r : ZMod q) :
      |(((PMF.uniformOfFintype (Fin N)).map fun x => (x.val : ZMod q)) r).toReal -
        (PMF.uniformOfFintype (ZMod q) r).toReal| ≤
        (if r.val < N % q then (1 : ℝ) else 0) / N + (N % q : ℕ) / (q * N) := by
    rw [toReal_map_natCast_apply, PMF.uniformOfFintype_apply, ZMod.card, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    have hsplit : ((N / q + if r.val < N % q then 1 else 0 : ℕ) : ℝ) / N - (q : ℝ)⁻¹ =
        (if r.val < N % q then (1 : ℝ) else 0) / N - (N % q : ℕ) / (q * N) := by
      split_ifs <;> push_cast <;> field_simp <;> linarith [hdiv]
    rw [hsplit]
    have h1 : (0 : ℝ) ≤ (if r.val < N % q then (1 : ℝ) else 0) / N := by positivity
    have h2 : (0 : ℝ) ≤ (N % q : ℕ) / (q * N) := by positivity
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hcount : (∑ r : ZMod q, if r.val < N % q then (1 : ℝ) else 0) ≤ (N % q : ℕ) := by
    rw [Finset.sum_boole]
    exact_mod_cast (Finset.card_le_card_of_injOn ZMod.val (t := Finset.range (N % q))
      (fun r hr => by simpa using hr) (ZMod.val_injective q).injOn).trans
        (Finset.card_range _).le
  rw [dist_eq]
  calc (∑ r, |(((PMF.uniformOfFintype (Fin N)).map fun x => (x.val : ZMod q)) r).toReal -
        (PMF.uniformOfFintype (ZMod q) r).toReal|) / 2
      ≤ (∑ r : ZMod q, ((if r.val < N % q then (1 : ℝ) else 0) / N +
          (N % q : ℕ) / (q * N))) / 2 := by
        gcongr with r
        exact hterm r
    _ = ((∑ r : ZMod q, if r.val < N % q then (1 : ℝ) else 0) / N +
          q * ((N % q : ℕ) / (q * N))) / 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
          ZMod.card, nsmul_eq_mul]
    _ ≤ ((N % q : ℕ) / N + q * ((N % q : ℕ) / (q * N))) / 2 := by
        gcongr
    _ = (N % q : ℕ) / N := by
        field_simp
        ring

/-- A uniform value below `N`, read in `ZMod q`, is within statistical distance `q / N` of the
uniform distribution on `ZMod q`. -/
theorem dist_map_natCast_uniformOfFintype_le_div (N q : ℕ) [NeZero N] [NeZero q] :
    dist ((PMF.uniformOfFintype (Fin N)).map fun x => (x.val : ZMod q))
      (PMF.uniformOfFintype (ZMod q)) ≤ q / N := by
  refine (dist_map_natCast_uniformOfFintype_le N q).trans ?_
  gcongr
  exact_mod_cast (Nat.mod_lt N (NeZero.pos q)).le

end Cslib.Probability.PMF
