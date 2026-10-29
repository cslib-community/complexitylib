/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ThreeSum.ThreeSets
public import Complexity.Computability.WordRAM.Signed.Encoding
public import Complexity.Computability.WordRAM.ListArray
public import Mathlib.Data.List.Nodup

/-!
# Finite specifications for the native distinct-position frontend

The mathematical sets are the existing `ThreeSum.splitA`, `ThreeSum.splitB`,
`ThreeSum.twiceSet` and `ThreeSum.zeroSet`. Native keys remain in unsigned encoding order.
The specifications here describe compact subsequences of the radix key/count arrays.

## Main definitions

* `label`: compute the shifted label from a canonical signed key.
* `twice`: the canonical key of twice the represented integer.
* `select`: compact selections from full key/count pairs.

## Main results

* `label_encode`: native label arithmetic agrees with the existing mathematical label.
* `twice_encode`: doubling has the required positive sign.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend

open Cslib.WordRAM
namespace Math

/-- Shift a sign-and-magnitude key into the nonnegative label interval. -/
def label (U u : ℕ) : ℕ := if u % 2 = 0 then 2 * U + u / 2 else 2 * U - u / 2

/-- The canonical key for twice the integer represented by a canonical key. -/
def twice (u : ℕ) : ℕ := 2 * u - u % 2

/-- A mode selects A, B₀, B₁, repeated nonzero values, repeated zero, or all values.
Mode six is reserved for the separately written constant singleton zero. -/
def flag (a b v mode : ℕ) (p : ℕ × ℕ) : Bool :=
  match mode with
  | 0 => decide (a = v)
  | 1 => decide (a ≠ v ∧ b = 0)
  | 2 => decide (a ≠ v ∧ b = 1)
  | 3 => decide (p.1 ≠ 0 ∧ 2 ≤ p.2)
  | 4 => decide (p.1 = 0 ∧ 3 ≤ p.2)
  | 5 => true
  | _ => false

/-- Selection from the two native label digits. -/
def keep (U β β' v mode : ℕ) (p : ℕ × ℕ) : Bool :=
  flag ((label U p.1 >>> β) % 2) ((label U p.1 >>> β') % 2) v mode p

/-- Key transformation after selection; only the repeated-nonzero mode doubles values. -/
def value (mode u : ℕ) : ℕ := if mode = 3 then twice u else u

/-- Compact output of one native scan. Multiplicities are never truncated. -/
def select (U β β' v mode : ℕ) (rs : List (ℕ × ℕ)) : List ℕ :=
  ((rs.filter (keep U β β' v mode)).map fun p => value mode p.1)

/-- A single scan writes at most one cell per key/count pair. -/
theorem length_select_le (U β β' v mode : ℕ) (rs : List (ℕ × ℕ)) :
    (select U β β' v mode rs).length ≤ rs.length := by
  simpa only [select, List.length_map] using List.length_filter_le (keep U β β' v mode) rs

/-- Native label arithmetic, including the absence of subtraction underflow. -/
theorem label_encode {U : ℕ} {z : ℤ} (hz : |z| ≤ (U : ℤ)) :
    label U (Signed.encode z) = Cslib.Algorithms.ThreeSum.lab (2 * U) z := by
  have hn : z.natAbs ≤ U := by
    exact_mod_cast (show (z.natAbs : ℤ) ≤ (U : ℤ) by simpa only [Int.natCast_natAbs] using hz)
  by_cases hneg : z < 0
  · have habs : z = -(z.natAbs : ℤ) := by
      rw [Int.ofNat_natAbs_of_nonpos (by omega : z ≤ 0)]
      omega
    simp only [label, Signed.encode_mod_two, hneg, ↓reduceIte, one_ne_zero,
      Signed.encode_div_two, Cslib.Algorithms.ThreeSum.lab]
    omega
  · have habs := Int.eq_natAbs_of_nonneg (by omega : 0 ≤ z)
    simp only [label, Signed.encode_mod_two, hneg, ↓reduceIte,
      Signed.encode_div_two, Cslib.Algorithms.ThreeSum.lab]
    omega

/-- The transient unsigned double is corrected by its low sign bit. -/
theorem twice_encode (z : ℤ) : twice (Signed.encode z) = Signed.encode (2 * z) := by
  have hs : (2 * z < 0) ↔ z < 0 := by omega
  rw [twice, Signed.encode_mod_two]
  simp only [Signed.encode, Int.natAbs_mul, show (2 : ℤ).natAbs = 2 from rfl, hs]
  split_ifs <;> omega

/-- Label arithmetic and the transient double stay within a common explicit bound. -/
theorem key_bounds {U : ℕ} {z : ℤ} (hz : |z| ≤ (U : ℤ)) :
    Signed.encode z ≤ 2 * U + 1 ∧ label U (Signed.encode z) ≤ 3 * U ∧
      Signed.encode z / 2 ≤ 2 * U ∧ 2 * Signed.encode z ≤ 4 * U + 2 := by
  have hn : z.natAbs ≤ U := by
    exact_mod_cast (show (z.natAbs : ℤ) ≤ (U : ℤ) by simpa only [Int.natCast_natAbs] using hz)
  simp only [label, Signed.encode]
  split_ifs <;> omega

/-- The unsigned transformation is injective, even before restricting to canonical keys. -/
theorem twice_injective : Function.Injective twice := by
  intro a b h
  have ha := Nat.mod_lt a (by decide : 0 < 2)
  have hb := Nat.mod_lt b (by decide : 0 < 2)
  dsimp only [twice] at h
  omega

/-- Every output value transformation preserves injectivity. -/
theorem value_injective (mode : ℕ) : Function.Injective (value mode) := by
  intro a b h
  by_cases hm : mode = 3
  · exact twice_injective (by simpa only [value, hm, ↓reduceIte] using h)
  · simpa only [value, hm, ↓reduceIte] using h

/-- Every compact scan enumerates its output without repetitions. -/
theorem select_nodup (U β β' v mode : ℕ) {rs : List (ℕ × ℕ)}
    (h : (rs.map Prod.fst).Nodup) : (select U β β' v mode rs).Nodup := by
  have hk : ((rs.filter (keep U β β' v mode)).map Prod.fst).Nodup :=
    h.sublist ((List.filter_sublist).map _)
  simpa only [select, List.map_map, Function.comp_def] using
    hk.map (value_injective mode)

/-- The supplied radix contracts identify every run with its exact input multiplicity. -/
theorem mem_runs {input : List ℤ} {rs : List (ℕ × ℕ)}
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hcounts : ∀ p ∈ rs, (input.map Signed.encode).count p.1 = p.2)
    (p : ℕ × ℕ) :
    p ∈ rs ↔ ∃ z ∈ input, p = (Signed.encode z, input.count z) := by
  constructor
  · intro hp
    obtain ⟨z, hz, he⟩ := List.mem_map.mp ((hkeys p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩))
    have hc := hcounts p hp
    rw [← he, List.count_map_of_injective _ _ Signed.encode_injective] at hc
    exact ⟨z, hz, Prod.ext he.symm hc.symm⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨p, hp, he⟩ := List.mem_map.mp ((hkeys (Signed.encode z)).mpr
      (List.mem_map.mpr ⟨z, hz, rfl⟩))
    have hc := hcounts p hp
    rw [he, List.count_map_of_injective _ _ Signed.encode_injective] at hc
    have hp' : p = (Signed.encode z, input.count z) := Prod.ext he hc.symm
    exact hp' ▸ hp

/-- A compact native selection represents precisely its finite filtered image. -/
theorem select_decoded {input : List ℤ} {rs : List (ℕ × ℕ)}
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hcounts : ∀ p ∈ rs, (input.map Signed.encode).count p.1 = p.2)
    (U β β' v mode : ℕ) :
    ((select U β β' v mode rs).map Signed.decode).toFinset =
      (input.toFinset.filter fun z => keep U β β' v mode
        (Signed.encode z, input.count z) = true).image
          (fun z => Signed.decode (value mode (Signed.encode z))) := by
  ext z
  simp only [List.mem_toFinset, List.mem_map, select, List.mem_filter, Finset.mem_image,
    Finset.mem_filter, mem_runs hkeys hcounts]
  constructor
  · rintro ⟨u, ⟨p, ⟨⟨a, ha, rfl⟩, hkeep⟩, rfl⟩, rfl⟩
    exact ⟨a, ⟨ha, hkeep⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hkeep⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨⟨a, ha, rfl⟩, hkeep⟩, rfl⟩, rfl⟩

/-- List multiplicity is exactly the number of original input positions. -/
theorem count_positions (input : List ℤ) (z : ℤ) :
    (Finset.univ.filter fun i : Fin input.length => input[i] = z).card = input.count z :=
  Fin.card_filter_univ_eq_vector_get_eq_count z ⟨input, rfl⟩

/-- Original input values are precisely the image of its positions. -/
theorem input_values (input : List ℤ) :
    Finset.univ.image (fun i : Fin input.length => input[i]) = input.toFinset := by
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset]
  constructor
  · rintro ⟨i, rfl⟩
    exact List.getElem_mem i.isLt
  · intro hz
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hz
    exact ⟨⟨i, hi⟩, he⟩

/-- Native division/shift digits agree with the existing Boolean bit operation. -/
theorem digit_eq (u β : ℕ) (v : Bool) : (u >>> β) % 2 = v.toNat ↔ u.testBit β = v := by
  rw [Nat.shiftRight_eq_div_pow, ← Nat.toNat_testBit]
  cases u.testBit β <;> cases v <;> decide

/-- Zero has exactly one canonical key. -/
theorem encode_eq_zero (z : ℤ) : Signed.encode z = 0 ↔ z = 0 := by
  change Signed.encode z = Signed.encode 0 ↔ z = 0
  exact Signed.encode_injective.eq_iff

/-- Exact bridge from the repeated-nonzero native scan to the existing `twiceSet`. -/
theorem select_twice {input : List ℤ} {rs : List (ℕ × ℕ)}
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hcounts : ∀ p ∈ rs, (input.map Signed.encode).count p.1 = p.2)
    (U β β' v : ℕ) :
    ((select U β β' v 3 rs).map Signed.decode).toFinset =
      Cslib.Algorithms.ThreeSum.twiceSet (fun i : Fin input.length => input[i]) := by
  rw [select_decoded hkeys hcounts]
  simp only [keep, flag, decide_eq_true_eq, ne_eq, encode_eq_zero, value, ↓reduceIte,
    twice_encode, Signed.decode_encode, Cslib.Algorithms.ThreeSum.twiceSet,
    input_values, count_positions]

/-- The original-set scan preserves every distinct input value. -/
theorem select_original {input : List ℤ} {rs : List (ℕ × ℕ)}
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hcounts : ∀ p ∈ rs, (input.map Signed.encode).count p.1 = p.2)
    (U β β' v : ℕ) :
    ((select U β β' v 5 rs).map Signed.decode).toFinset =
      Finset.univ.image (fun i : Fin input.length => input[i]) := by
  rw [select_decoded hkeys hcounts, input_values]
  simp [keep, flag, value]

/-- The zero scan uses the full original multiplicity and threshold three. -/
theorem select_zero {input : List ℤ} {rs : List (ℕ × ℕ)}
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hcounts : ∀ p ∈ rs, (input.map Signed.encode).count p.1 = p.2)
    (U β β' v : ℕ) :
    ((select U β β' v 4 rs).map Signed.decode).toFinset =
      Cslib.Algorithms.ThreeSum.zeroSet (fun i : Fin input.length => input[i]) := by
  rw [select_decoded hkeys hcounts]
  simp only [keep, flag, decide_eq_true_eq, encode_eq_zero, value, Nat.reduceEqDiff,
    ↓reduceIte, Signed.decode_encode, Finset.image_id', Cslib.Algorithms.ThreeSum.zeroSet,
    count_positions]
  by_cases hc : 3 ≤ input.count 0
  · have hm : (0 : ℤ) ∈ input := List.count_pos_iff.mp (by omega)
    ext z
    simp only [hc, ↓reduceIte, Finset.mem_filter, List.mem_toFinset, Finset.mem_singleton]
    constructor
    · exact fun h => h.2.1
    · rintro rfl
      exact ⟨hm, rfl, hc⟩
  · ext z
    simp only [hc, ↓reduceIte, Finset.mem_filter, List.mem_toFinset, Finset.notMem_empty,
      iff_false, not_and]
    intro _ hz
    subst z
    exact hc

/-- The A scan represents the exact existing bit split. -/
theorem select_A {input : List ℤ} {rs : List (ℕ × ℕ)} {U : ℕ}
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hcounts : ∀ p ∈ rs, (input.map Signed.encode).count p.1 = p.2)
    (hvalues : ∀ z ∈ input, |z| ≤ (U : ℤ)) (β β' : ℕ) (v : Bool) :
    ((select U β β' v.toNat 0 rs).map Signed.decode).toFinset =
      Cslib.Algorithms.ThreeSum.splitA (2 * U) β v
        (Finset.univ.image (fun i : Fin input.length => input[i])) := by
  rw [select_decoded hkeys hcounts, input_values]
  simp only [value, Nat.reduceEqDiff, ↓reduceIte, Signed.decode_encode, Finset.image_id']
  apply Finset.filter_congr
  intro z hz
  simp only [List.mem_toFinset] at hz
  simp only [keep, flag, decide_eq_true_eq, label_encode (hvalues z hz), digit_eq]

/-- Both B scans represent the exact existing two-bit split, including `β=β'`. -/
theorem select_B {input : List ℤ} {rs : List (ℕ × ℕ)} {U : ℕ}
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hcounts : ∀ p ∈ rs, (input.map Signed.encode).count p.1 = p.2)
    (hvalues : ∀ z ∈ input, |z| ≤ (U : ℤ)) (β β' : ℕ) (v w : Bool) :
    ((select U β β' v.toNat (if w then 2 else 1) rs).map Signed.decode).toFinset =
      Cslib.Algorithms.ThreeSum.splitB (2 * U) β β' v w
        (Finset.univ.image (fun i : Fin input.length => input[i])) := by
  rw [select_decoded hkeys hcounts, input_values]
  cases w
  all_goals simp only [Bool.false_eq_true, ↓reduceIte, value, Nat.reduceEqDiff,
    Signed.decode_encode, Finset.image_id']
  all_goals apply Finset.filter_congr
  all_goals intro z hz
  all_goals simp only [List.mem_toFinset] at hz
  all_goals simp only [keep, flag, decide_eq_true_eq, label_encode (hvalues z hz)]
  all_goals simp only [ne_eq, digit_eq _ _ v]
  all_goals cases v <;> cases (Cslib.Algorithms.ThreeSum.lab (2 * U) z).testBit β <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, not_true_eq_false,
      true_and, false_and, Bool.not_true, Bool.not_false]
  all_goals first | exact digit_eq _ _ false | exact digit_eq _ _ true

end Math
end Cslib.Algorithms.WordRAM.ThreeSum.Frontend
