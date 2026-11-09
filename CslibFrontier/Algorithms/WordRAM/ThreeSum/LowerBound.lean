/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Footprint
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Admissible
public import CslibFrontier.Algorithms.ThreeSum.Defs
public import CslibFrontier.Computability.WordRAM.Time
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Native 3SUM input-reading lower bound

On the negative input `[1, -1, 1, …, 1]`, changing any tail position to zero creates a
distinct-position 3SUM witness. Consequently every correct native program must read every tail
cell. The proof uses actual flat runs, canonical signed encoding and the existing `Admissible`
domain: width is the same for the two inputs, and every width above the size-only threshold is
admitted. Width-reading instructions, arbitrary basis operations and writes are permitted.

This adapts the unread-cell adversary argument in the source module
`ModelChecks.ThreeSumLowerBound`, `oddVec` through `not_solvedInTimeAt_threeSum`, in
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. It does not import that
source's signed modular RAM or its time predicate. Here a load reads one unsigned memory word,
the input is length-prefixed, registers start zero, overflow faults, and the halt is charged.

## Main results

* `decidesInTime_lowerBound`: the negative length-`n+2` input needs at least `n+1` instructions.
* `not_uniformDecidableInO_sublinear`: no exponent below one gives uniform native decision.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum

open Cslib.WordRAM Cslib.Algorithms.ThreeSum

/-- A negative 3SUM instance with `n` independently sensitive tail positions. -/
@[expose] def hardInput (n : ℕ) : List ℤ := 1 :: (-1) :: List.replicate n 1

@[simp] theorem length_hardInput (n : ℕ) : (hardInput n).length = n + 2 := by
  simp [hardInput]

private theorem hardInput_values {n : ℕ} {z : ℤ} (h : z ∈ hardInput n) : z = 1 ∨ z = -1 := by
  simp only [hardInput, List.mem_cons, List.mem_replicate] at h
  tauto

/-- An odd sum of values in `{1, -1}` cannot vanish. -/
theorem hardInput_no_solution (n : ℕ) :
    ¬HasSolution (fun i : Fin (hardInput n).length => (hardInput n)[i]) := by
  rintro ⟨i, j, k, _, _, _, hs⟩
  have hi := hardInput_values (List.getElem_mem i.isLt)
  have hj := hardInput_values (List.getElem_mem j.isLt)
  have hk := hardInput_values (List.getElem_mem k.isLt)
  simp only [Fin.getElem_fin] at hs
  rcases hi with hi | hi <;> rcases hj with hj | hj <;> rcases hk with hk | hk <;>
    simp only [hi, hj, hk] at hs <;> omega

/-- Replacing any tail entry by zero produces the witness at positions `0`, `1`, `i+2`. -/
theorem hardInput_set_solution (n i : ℕ) (hi : i < n) :
    HasSolution (fun j : Fin ((hardInput n).set (i + 2) 0).length =>
      ((hardInput n).set (i + 2) 0)[j]) := by
  refine ⟨⟨0, by simp⟩, ⟨1, by simp⟩, ⟨i + 2, by simpa using hi⟩,
    Fin.ne_of_val_ne (by decide : 0 ≠ 1),
    Fin.ne_of_val_ne (by omega : 1 ≠ i + 2),
    Fin.ne_of_val_ne (by omega : 0 ≠ i + 2), ?_⟩
  simp [hardInput]

private theorem hardInput_admissible (κ n w : ℕ)
    (hw : Decision.width κ 123357 (n + 2) ≤ w) : Decision.Admissible κ (hardInput n) w := by
  refine ⟨by simpa using hw, ?_⟩
  intro z hz
  have hpow : 1 ≤ (n + 2 + 2) ^ κ := Nat.one_le_pow _ _ (by omega)
  rcases hardInput_values hz with rfl | rfl <;> simp only [abs_one, abs_neg, length_hardInput]
    <;> exact_mod_cast hpow

private theorem hardInput_set_admissible (κ n i w : ℕ)
    (hw : Decision.width κ 123357 (n + 2) ≤ w) :
    Decision.Admissible κ ((hardInput n).set (i + 2) 0) w := by
  refine ⟨by simpa using hw, ?_⟩
  intro z hz
  rcases List.mem_or_eq_of_mem_set hz with hz | rfl
  · have h := (hardInput_admissible κ n w hw).2 z hz
    simpa using h
  · simp only [abs_zero]
    positivity

private theorem init_map_set_agree {r : ℕ} (input : List ℤ) (i : ℕ) (z : ℤ) :
    (Data.init (input.map Signed.encode) : Data r).AgreeOutside {i + 1}
      (Data.init ((input.set i z).map Signed.encode)) := by
  refine ⟨rfl, ?_⟩
  intro a ha
  have hne : a ≠ i + 1 := by simpa using ha
  by_cases hzero : a = 0
  · subst a
    simp
  · have hindex : i ≠ a - 1 := by omega
    simp [Data.init, hzero, List.map_set, List.getD_eq_getElem?_getD, hindex]

/-- Every deterministic native program deciding the existing admitted 3SUM problem has a
linear worst-case input-reading cost. The `n` tail reads and final halt are all charged.
The statement holds over any basis, even one with arbitrary unit-cost arithmetic. -/
theorem decidesInTime_lowerBound {B : Basis} {r κ n w : ℕ} {p : Program B r}
    {time : List ℤ → ℕ → ℕ}
    (h : p.DecidesInTime (fun _ input => input.map Signed.encode)
      {input | HasSolution (fun i : Fin input.length => input[i])}
      time (Decision.Admissible κ))
    (hw : Decision.width κ 123357 (n + 2) ≤ w) : n + 1 ≤ time (hardInput n) w := by
  have ha := hardInput_admissible κ n w hw
  obtain ⟨v, steps, he, ht, _, hv⟩ := h (hardInput n) w ha ha.inputFits
  obtain ⟨R, hR, hrep⟩ := he.exists_readFootprint
  have htail : (Finset.range n).image (· + 3) ⊆ R := by
    intro a ha'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha'
    have hi' := Finset.mem_range.mp hi
    by_contra hn
    have ha' := hardInput_set_admissible κ n i w hw
    obtain ⟨v', steps', he', _, _, hv'⟩ :=
      h ((hardInput n).set (i + 2) 0) w ha' ha'.inputFits
    have herep : Executes w p
        (.init (((hardInput n).set (i + 2) 0).map Signed.encode)) v steps :=
      hrep {i + 3} _ (by simpa using hn) rfl
        (by simpa only [State.init, Nat.add_assoc] using
          init_map_set_agree (r := r) (hardInput n) (i + 2) 0)
    have heq := (herep.unique he').1
    have hyes : v' = 1 := hv'.mpr (hardInput_set_solution n i hi')
    exact hardInput_no_solution n (hv.mp (heq.trans hyes))
  have hcard : n ≤ R.card := by
    calc n = ((Finset.range n).image (· + 3)).card := by
            rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h),
              Finset.card_range]
         _ ≤ R.card := Finset.card_le_card htail
  omega

private theorem exists_sublinear_bound {a : ℝ} (ha : a < 1) (c N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ c * ⌈(n : ℝ) ^ a⌉₊ + 2 < n := by
  have hlim := ((tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul ((c : ℝ) + 1)
  have hp : -(1 - a) = a - 1 := by ring
  simp only [hp, mul_zero, Function.comp_apply] at hlim
  have hsmall := hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, (2 * (c : ℝ) + 6) < n :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  obtain ⟨n, hn, hs, hl⟩ :=
    ((Filter.eventually_ge_atTop N).and (hsmall.and hlarge)).exists
  refine ⟨n, hn, ?_⟩
  have hnpos : (0 : ℝ) < n := by linarith
  rw [Real.rpow_sub hnpos, Real.rpow_one] at hs
  have hpow : ((c : ℝ) + 1) * (n : ℝ) ^ a < (n : ℝ) / 2 := by
    have := (div_lt_iff₀ hnpos).mp (show (((c : ℝ) + 1) * (n : ℝ) ^ a) / n < 1 / 2 by
      simpa only [mul_div_assoc] using hs)
    linarith
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity) a)
  have hnonneg := Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity) a
  have hbound : (c : ℝ) * ⌈(n : ℝ) ^ a⌉₊ + 2 < n := by
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    nlinarith
  exact_mod_cast hbound

/-- The established native 3SUM decision notion cannot hold at any exponent below one.
The magnitude exponent is arbitrary, including zero. Both adversarial inputs fit the same
physical width; no input-dependent width or advice is assumed. -/
theorem not_uniformDecidableInO_sublinear (B : Basis) (κ : ℕ) {a : ℝ} (ha : a < 1) :
    ¬UniformDecidableInO B
      {input : List ℤ | HasSolution (fun i : Fin input.length => input[i])}
      (fun _ input => input.map Signed.encode) List.length
      (fun n _ => ⌈(n : ℝ) ^ a⌉₊) (Decision.Admissible κ) := by
  rintro ⟨time, ⟨r, p, hp⟩, c, N, _, hbound⟩
  obtain ⟨m, hm, hlt⟩ := exists_sublinear_bound ha c (N + 2)
  have hm2 : 2 ≤ m := by omega
  have he : m - 2 + 2 = m := by omega
  let w := Decision.width κ 123357 m
  have hw : Decision.width κ 123357 (m - 2 + 2) ≤ w := by simp only [he, w, le_refl]
  have hlo := decidesInTime_lowerBound (n := m - 2) hp hw
  have hhi := hbound (hardInput (m - 2)) w (by simp only [length_hardInput]; omega)
    (hardInput_admissible κ (m - 2) w hw)
  simp only [length_hardInput, he] at hhi
  omega

end Cslib.Algorithms.WordRAM.ThreeSum
