/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Entropy
public import Complexity.Probability.UniversalHash
import Mathlib.Analysis.SpecificLimits.Basic
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map

/-!
# Hashing isolates preimages

Given an image `f x`, a universal hash can isolate `x` among its other preimages. On successful
isolation, every predicate of `x` is determined by the revealed information. Consequently, the
remaining conditional entropy of a bit is bounded by the probability of a hash collision inside
the fiber. The seed stays public; a predicate may depend on it, so it can include a fresh parity
query as well as the hash matrix.

## Main results

* `Cslib.Probability.IsTwoUniversal.fiber_collision_le`: failure to isolate a preimage.
* `Cslib.Probability.IsTwoUniversal.conditionalEntropy_hash_le`: entropy bounded by collisions.
* `Cslib.Probability.conditionalEntropy_random_hash_le`: entropy averaged over public hash lengths.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Section 4, proof of Lemma 3.
  The isolation and averaged entropy bounds allow arbitrary two-universal families and
  input distributions, retaining the sampled hash length as public information.

Adapted from Probability/HashIsolation.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.

-/

@[expose] public section

namespace Cslib.Probability

open Cslib.Probability.PMF

variable {Seed Input Image Output : Type*}
  [Fintype Seed] [Fintype Input] [Finite Image] [Fintype Output]

private theorem sum_isolation_error_le (size count : ℕ) (hsize : 0 < size) :
    (∑ i ∈ Finset.range count, min 1 ((size - 1 : ℕ) / (2 : ℝ) ^ (i + 1))) ≤
      Real.logb 2 size + 2 := by
  let cutoff := Nat.log 2 size
  let mass : ℝ := size - 1
  have hmass : 0 ≤ mass := by
    have h : (1 : ℝ) ≤ size := by exact_mod_cast (Nat.succ_le_iff.mpr hsize)
    dsimp [mass]
    linarith
  have hcast : (size - 1 : ℕ) = mass := by simp [mass, Nat.cast_sub (by lia : 1 ≤ size)]
  have htail : (∑ i ∈ Finset.range count, mass / (2 : ℝ) ^ (cutoff + i + 1)) ≤
      mass / 2 ^ cutoff := by
    calc
      _ = mass / 2 ^ (cutoff + 1) * ∑ i ∈ Finset.range count, (1 / (2 : ℝ)) ^ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [show cutoff + i + 1 = (cutoff + 1) + i by lia, pow_add, div_pow, one_pow]
        field_simp
      _ ≤ mass / 2 ^ (cutoff + 1) * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le count) (by positivity)
      _ = _ := by rw [pow_succ]; field_simp
  have hratio : mass / (2 : ℝ) ^ cutoff ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) size
    have hr : (size : ℝ) < 2 ^ (cutoff + 1) := by exact_mod_cast h
    rw [pow_succ] at hr
    dsimp [mass]
    linarith
  calc
    _ ≤ ∑ i ∈ Finset.range (cutoff + count), min 1 (mass / (2 : ℝ) ^ (i + 1)) := by
      rw [hcast]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by lia))
      intro i _ _
      exact le_min (by norm_num) (by positivity)
    _ = (∑ i ∈ Finset.range cutoff, min 1 (mass / (2 : ℝ) ^ (i + 1))) +
        ∑ i ∈ Finset.range count, min 1 (mass / (2 : ℝ) ^ (cutoff + i + 1)) :=
      Finset.sum_range_add _ _ _
    _ ≤ cutoff + mass / 2 ^ cutoff := by
      apply add_le_add
      · exact (Finset.sum_le_sum (fun i _ => min_le_left _ _)).trans_eq (by simp)
      · exact (Finset.sum_le_sum (fun i _ => min_le_right _ _)).trans htail
    _ ≤ Real.logb 2 size + 2 := add_le_add (Real.natLog_le_logb size 2) hratio

omit [Finite Image] in
open Classical in
/-- The chance that a hash fails to isolate a preimage is at most the number of its competitors
divided by the hash alphabet size, capped at one. No assumption on the fiber sizes is needed. -/
theorem IsTwoUniversal.fiber_collision_le {seed : PMF Seed} {hash : Seed → Input → Output}
    (hhash : IsTwoUniversal seed hash) (f : Input → Image) (x : Input) :
    (∑ s, if ∃ y, y ≠ x ∧ f y = f x ∧ hash s y = hash s x then (seed s).toReal else 0) ≤
      min 1 ((Nat.card {y // f y = f x} - 1 : ℕ) / (Fintype.card Output : ℝ)) := by
  apply le_min
  · calc
      _ ≤ ∑ s, (seed s).toReal := Finset.sum_le_sum (fun s _ => by
        split_ifs <;> simp only [le_refl, ENNReal.toReal_nonneg])
      _ = 1 := sum_toReal seed
  · have h := hhash.collision_with_set_le (Finset.univ.filter (fun y => f y = f x)) x
    have hx : x ∈ Finset.univ.filter (fun y => f y = f x) := by simp
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_erase_of_mem hx,
      ← Fintype.card_subtype, Nat.card_eq_fintype_card, and_comm, and_left_comm, and_assoc] using h

omit [Fintype Seed] in
/-- Conditional entropy after revealing the seed, the function image, and the hash value is
bounded by the expected probability that the hash leaves more than one possible preimage. -/
theorem IsTwoUniversal.conditionalEntropy_hash_le [Finite Seed] {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash)
    (source : PMF Input) (f : Input → Image) (predicate : Seed → Input → Bool) :
    conditionalEntropy (seed.bind (fun s => source.map
      (fun x => ((s, f x, hash s x), predicate s x)))) ≤
      ∑ x, (source x).toReal *
        min 1 ((Nat.card {y // f y = f x} - 1 : ℕ) / (Fintype.card Output : ℝ)) := by
  classical
  let := Fintype.ofFinite Seed
  let pair := seed.bind (fun s => source.map (s, ·))
  let observe (p : Seed × Input) := (p.1, f p.2, hash p.1 p.2)
  have hcollision (s : Seed) (x : Input) :
      (∃ p : Seed × Input, p ≠ (s, x) ∧ observe p = observe (s, x)) ↔
        ∃ y, y ≠ x ∧ f y = f x ∧ hash s y = hash s x := by
    constructor
    · rintro ⟨⟨t, y⟩, hne, heq⟩
      obtain ⟨rfl, heq⟩ := Prod.mk.inj heq
      exact ⟨y, fun hy => hne (hy ▸ rfl), Prod.mk.inj heq⟩
    · rintro ⟨y, hy, hf, hh⟩
      exact ⟨(s, y), fun heq => hy (congrArg Prod.snd heq), by simp [observe, hf, hh]⟩
  have hmass (s : Seed) (x : Input) : (pair (s, x)).toReal =
      (seed s).toReal * (source x).toReal := by
    simp only [pair, bind_map_prodMk_apply, ENNReal.toReal_mul]
  have h := conditionalEntropy_map_le_collision pair observe (fun p => predicate p.1 p.2)
  simp only [Fintype.sum_prod_type, hmass, hcollision, Fintype.card_bool,
    Nat.cast_ofNat, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
  have hjoint : pair.map (fun p => (observe p, predicate p.1 p.2)) =
      seed.bind (fun s => source.map (fun x => ((s, f x, hash s x), predicate s x))) := by
    simp only [pair, observe, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [hjoint] at h
  apply h.trans
  calc
    _ = ∑ x, (source x).toReal *
        ∑ s, if ∃ y, y ≠ x ∧ f y = f x ∧ hash s y = hash s x then (seed s).toReal else 0 := by
      rw [Finset.sum_comm]
      congr 2 with x
      simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero,
        mul_comm (seed _).toReal (source x).toReal]
    _ ≤ _ := Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_left (hhash.fiber_collision_le f x) ENNReal.toReal_nonneg)

omit [Fintype Seed] [Fintype Output] in
/-- Averaging over hash lengths `1, …, count` leaves at most the average logarithmic fiber size
plus two bits, divided by `count`. This is the entropy bound in Holenstein's Lemma 3. -/
private theorem mean_conditionalEntropy_hash_le [Finite Seed] (count : ℕ) (seed : PMF Seed)
    (source : PMF Input)
    (f : Input → Image) (hash : (i : Fin count) → Seed → Input → (Fin (i.val + 1) → Bool))
    (hhash : ∀ i, IsTwoUniversal seed (hash i)) (predicate : Fin count → Seed → Input → Bool) :
    (∑ i, conditionalEntropy (seed.bind (fun s => source.map
      (fun x => ((s, f x, hash i s x), predicate i s x))))) / count ≤
      ((∑ x, (source x).toReal * Real.logb 2 (Nat.card {y // f y = f x})) + 2) / count := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg count)
  calc
    _ ≤ ∑ i : Fin count, ∑ x, (source x).toReal *
        min 1 ((Nat.card {y // f y = f x} - 1 : ℕ) / (2 : ℝ) ^ (i.val + 1)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa [Fintype.card_fun] using (hhash i).conditionalEntropy_hash_le source f (predicate i)
    _ = ∑ x, (source x).toReal * ∑ i ∈ Finset.range count,
        min 1 ((Nat.card {y // f y = f x} - 1 : ℕ) / (2 : ℝ) ^ (i + 1)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.mul_sum]
      congr 1
      exact Fin.sum_univ_eq_sum_range (fun i =>
        min 1 ((Nat.card {y // f y = f x} - 1 : ℕ) / (2 : ℝ) ^ (i + 1))) count
    _ ≤ ∑ x, (source x).toReal * (Real.logb 2 (Nat.card {y // f y = f x}) + 2) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      apply sum_isolation_error_le
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr ⟨⟨x, rfl⟩⟩
    _ = _ := by simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_toReal, one_mul]

omit [Fintype Seed] [Fintype Output] in
/-- The averaged bound applies to the actual joint experiment with a public uniform hash
length. The dependent observation type records exactly the number of revealed hash bits. -/
theorem conditionalEntropy_random_hash_le [Finite Seed] (count : ℕ) [NeZero count]
    (seed : PMF Seed) (source : PMF Input) (f : Input → Image)
    (hash : (i : Fin count) → Seed → Input → (Fin (i.val + 1) → Bool))
    (hhash : ∀ i, IsTwoUniversal seed (hash i)) (predicate : Fin count → Seed → Input → Bool) :
    conditionalEntropy ((PMF.uniformOfFintype (Fin count)).bind (fun i =>
      seed.bind (fun s => source.map (fun x =>
        ((⟨i, (s, f x, hash i s x)⟩ : Σ i : Fin count, Seed × Image × (Fin (i.val + 1) → Bool)),
          predicate i s x))))) ≤
      ((∑ x, (source x).toReal * Real.logb 2 (Nat.card {y // f y = f x})) + 2) / count := by
  let kernel (i : Fin count) := seed.bind (fun s => source.map
    (fun x => ((s, f x, hash i s x), predicate i s x)))
  have havg := conditionalEntropy_bind_sigma (PMF.uniformOfFintype (Fin count)) kernel
  simp only [kernel, PMF.map_bind, PMF.map_comp, Function.comp_def,
    PMF.uniformOfFintype_apply, Fintype.card_fin,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ← Finset.mul_sum] at havg
  rw [havg, ← div_eq_inv_mul]
  exact mean_conditionalEntropy_hash_le count seed source f hash hhash predicate

end Cslib.Probability
