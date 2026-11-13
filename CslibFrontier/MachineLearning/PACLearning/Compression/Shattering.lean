/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.Compression.Basic
public import Cslib.MachineLearning.PACLearning.VCDimension
import CslibFrontier.Foundations.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Sample compression schemes bound the VC dimension

A binary class with a sample compression scheme of size `k` shatters no large set. If `C`
shatters an `n`-point set `W`, run the scheme on the `2 ^ n` samples that list the points of `W`
with every labeling. Each compressed sample is a list of at most `k` indices into `W`, read with
their labels, and the reconstructed hypothesis recovers the labeling. So the `2 ^ n` labelings
inject into the lists of at most `k` (point, label) pairs over `W`, of which there are at most
`(2 n + 1) ^ k`. Since `2 ^ n` eventually exceeds `(2 n + 1) ^ k`, the shattered sets are bounded.

This is the standard counting argument. Together with the theorem of Moran and Yehudayoff that
every class of finite VC dimension has a compression scheme of finite size (being formalized under
issue #4914), it shows that a binary class has a sample compression scheme of finite size if and
only if it has finite VC dimension. No measurability is involved.

## Main results

- `SampleCompressionScheme.two_pow_card_le_of_setShatters`: if `C` has a scheme of size `k` and
  shatters a finite set `W`, then `2 ^ |W| ≤ (2 |W| + 1) ^ k`.
- `SampleCompressionScheme.hasFiniteVCDim`: a binary class with a sample compression scheme of
  finite size has finite VC dimension.

-/

public section

open Set

namespace Cslib.MachineLearning.PACLearning

namespace SampleCompressionScheme

variable {α : Type*} {C : ConceptClass α Bool} {k : ℕ}

/-- **A compression scheme bounds the shattered sets**: if `C` has a sample compression scheme of
size `k` and shatters the finite set `W`, then `2 ^ |W| ≤ (2 |W| + 1) ^ k`. The labelings of `W`
inject into the lists of at most `k` labeled points of `W`. -/
theorem two_pow_card_le_of_setShatters (κ : SampleCompressionScheme C k) {W : Finset α}
    (hW : SetShatters C ↑W) : 2 ^ W.card ≤ (2 * W.card + 1) ^ k := by
  classical
  set n := W.card
  let e : Fin n ≃ W := W.equivFin.symm
  -- The sample listing the points of `W` with the labeling `v`.
  let S (v : Fin n → Bool) : LabeledSample α Bool n := fun i => ((e i : α), v i)
  -- Every such sample is realized by `C`.
  have hS (v : Fin n → Bool) : Realizable C (S v) := by
    obtain ⟨c, hc, hcW⟩ := hW ((fun i => (e i : α)) '' {i | v i = true}) (by
      rintro _ ⟨i, -, rfl⟩
      exact (e i).2)
    refine ⟨c, hc, fun i => ?_⟩
    have hmem : (e i : α) ∈ c ⁻¹' {true} ∩ ↑W ↔
        (e i : α) ∈ (fun i => (e i : α)) '' {i | v i = true} := by
      rw [hcW]
    have hinj : ∀ j, (e j : α) = (e i : α) → j = i := fun j h => e.injective (Subtype.ext h)
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, Finset.mem_coe, (e i).2, and_true,
      mem_image, mem_ofPred_eq] at hmem
    change v i = c (e i)
    cases hv : v i <;> cases hc' : c (e i) <;> simp_all
  -- The encoding: the kept indices, each with its label.
  let enc (v : Fin n → Bool) : Σ j : Fin (k + 1), Fin j → Fin n × Bool :=
    ⟨⟨(κ.compress (S v)).length, Nat.lt_succ_of_le (κ.length_compress_le _ (hS v))⟩,
      fun t => ((κ.compress (S v)).get t, v ((κ.compress (S v)).get t))⟩
  -- The reconstruction recovers the labeling from the encoding.
  have hdec (v : Fin n → Bool) (i : Fin n) :
      κ.reconstruct (List.ofFn fun t => ((e ((enc v).2 t).1 : α), ((enc v).2 t).2)) (e i) =
        v i := by
    have h := κ.reconstruct_correct (S v) (hS v) i
    convert h using 2
    exact List.ext_getElem (by simp [enc]) fun t _ _ => by simp [enc, S]
  have henc : Function.Injective enc := by
    intro v w hvw
    funext i
    rw [← hdec v i, ← hdec w i, hvw]
  calc 2 ^ n = Fintype.card (Fin n → Bool) := by simp
    _ ≤ Fintype.card (Σ j : Fin (k + 1), Fin j → Fin n × Bool) :=
        Fintype.card_le_of_injective _ henc
    _ ≤ (2 * n + 1) ^ k := by
      simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin, Fintype.card_prod,
        Fintype.card_bool]
      rw [Fin.sum_univ_eq_sum_range (fun j => (n * 2) ^ j), mul_comm 2 n]
      exact Cslib.sum_range_pow_le_add_one_pow _ k

/-- `2 ^ n` eventually exceeds `(2 n + 1) ^ k`. -/
private theorem exists_forall_pow_lt_two_pow (k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, (2 * n + 1) ^ k < 2 ^ n := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)).const_mul
    ((3 : ℝ) ^ k)
  rw [mul_zero] at h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h.eventually (gt_mem_nhds zero_lt_one))
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hlt := hN n (le_of_max_le_left hn)
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [← mul_div_assoc, div_lt_one h2, ← mul_pow] at hlt
  have : ((2 * n + 1 : ℕ) : ℝ) ^ k < ((2 ^ n : ℕ) : ℝ) :=
    calc ((2 * n + 1 : ℕ) : ℝ) ^ k ≤ (3 * n : ℝ) ^ k := by
          gcongr
          push_cast
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          linarith
      _ < 2 ^ n := hlt
      _ = ((2 ^ n : ℕ) : ℝ) := by push_cast; rfl
  exact_mod_cast this

/-- **A sample compression scheme of finite size bounds the VC dimension**: a binary class with a
scheme of size `k` has finite VC dimension. -/
theorem hasFiniteVCDim (κ : SampleCompressionScheme C k) : HasFiniteVCDim C := by
  obtain ⟨N, hN⟩ := exists_forall_pow_lt_two_pow k
  refine hasFiniteVCDim_iff.2 ⟨N, fun W hW => ?_⟩
  by_contra hlt
  exact (hN _ (le_of_not_ge hlt)).not_ge (κ.two_pow_card_le_of_setShatters hW)

end SampleCompressionScheme

end Cslib.MachineLearning.PACLearning
