/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Params

/-!
# Circular Tail-to-Dense Compaction Bijection, Key Reconstruction, and `CompactedRep`

This module defines the circular tail-to-dense bijection (`denseOfCirc`, `WindowInv`,
`TailDenseInv`), direct $O(1)$ owner-bucket and logical-slot recovery on dense slots `d ∈ [0, n)`
(`ownerBucketOfDense`, `logicalIdxOfDense`), and the array-coupling invariants (`WindowCoupled`,
`FixedCoupled`) for the resizable succinct dynamic dictionary of [Bender, Farach-Colton,
J. Kuszmaul and W. Kuszmaul, SOSA 2024][BenderFarachColtonKuszmaulKuszmaul2024].

## Design

1. **Circular `[b_win, b_win + n_win)` tail window (`denseOfCirc`, `WindowInv`):**
   Active full-slab slots `phys < gm 0 * slabSize N` map directly to dense index `d = phys`.
   Active tail slots `phys = N - 1 - t` (`t < gm 1`) store a circular residue `c = td t < M`
   (`M = maxTailItems N`) and resolve to `d = denseOfCirc M b_win c ∈ [b_win, b_win + n_win)`,
   with inverse `dt (d % M) = t`. Shifting `b_win` by `± 1` (`winGrowLeft`, `winShrinkLeft`) or
   resizing `n_win` by `± 1` (`winGrowRight`, `winShrinkRight`) updates only $O(1)$ entries of
   `(td, dt)` without reindexing untouched tail items.
2. **Array-level coupling (`WindowCoupled`, `FixedCoupled`):**
   `WindowCoupled` separates `metaBase` from `itemBase` so both resting in-epoch states and
   single-tape epoch migration (Zone 1 metadata + Zone 3 shared item arena) couple directly to the
   fixed-capacity `Succinct` array extractors (`gmAt`, `lmAt`, `quotAt`, `valAt`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.denseOfCirc`, `WindowInv`,
  `TailDenseInv`, `canonTD`, `canonDT`, `denseOfPhys`, `physByBase`, `winGrowRight`, `winGrowLeft`,
  `winShrinkRight`, `winShrinkLeft`: circular tail-to-dense bijection and $O(1)$ window updates.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ownerBucketOfDense`,
  `logicalIdxOfDense`: $O(1)$ owner-bucket and logical-slot recovery on dense slots `d ∈ [0, n)`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ghostW`, `WindowCoupled`,
  `FixedCoupled`: fixed-capacity array coupling invariants.

## Main results

* `winGrowRight_spec`, `winGrowLeft_spec`, `winShrinkRight_spec`, `winShrinkLeft_spec`,
  `physByBase_winGrowRight`, `physByBase_winGrowLeft`, `physByBase_winShrinkRight`,
  `physByBase_winShrinkLeft`: invariant preservation and slot-mapping laws for window transitions.
* `ownerBucketOfDense_lt_and_slotOf`, `denseOfPhys_slotOf_lt_and_inv`,
  `physOfDense_eq_slotOf_owner`: exact bijection between dense slots and active bucket slots.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM

/-! ## Section 1: Circular Tail-to-Dense Window Bijection (`denseOfCirc`, `WindowInv`) -/

/-- Recover the unique `d ∈ [base_tail, base_tail + M)` with `d % M = c` (for `0 < M`, `c < M`). -/
@[expose] def denseOfCirc (M base_tail c : ℕ) : ℕ :=
  if M = 0 then base_tail else base_tail + (c + M - base_tail % M) % M

theorem denseOfCirc_ge (M b c : ℕ) : b ≤ denseOfCirc M b c := by
  unfold denseOfCirc; split_ifs <;> omega

theorem denseOfCirc_mod_self {M base_tail d : ℕ} (hM : 0 < M)
    (hlo : base_tail ≤ d) (hhi : d < base_tail + M) :
    denseOfCirc M base_tail (d % M) = d := by
  have hM0 : M ≠ 0 := Nat.ne_of_gt hM
  unfold denseOfCirc
  rw [ite_eq_right hM0]
  set δ := d - base_tail
  have hδ_lt : δ < M := by omega
  have hd_eq : d = base_tail + δ := (Nat.add_sub_of_le hlo).symm
  set r := base_tail % M
  have hr_lt : r < M := Nat.mod_lt base_tail hM
  have hd_mod : d % M = (r + δ) % M := by
    conv_lhs => rw [hd_eq, ← Nat.div_add_mod base_tail M, Nat.add_assoc, Nat.mul_add_mod]
  have hmod : (d % M + M - r) % M = δ := by
    by_cases hlt : r + δ < M
    · have hrm : (r + δ) % M = r + δ := Nat.mod_eq_of_lt hlt
      have h1 : (r + δ) + M - r = δ + 1 * M := by omega
      rw [hd_mod, hrm, h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hδ_lt]
    · have hrm : (r + δ) % M = r + δ - M := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      have h1 : (r + δ - M) + M - r = δ := by omega
      rw [hd_mod, hrm, h1, Nat.mod_eq_of_lt hδ_lt]
  omega

theorem denseOfCirc_mod {M base_tail c : ℕ} (hM : 0 < M) (hc : c < M) :
    denseOfCirc M base_tail c % M = c := by
  have hM0 : M ≠ 0 := Nat.ne_of_gt hM
  unfold denseOfCirc
  rw [ite_eq_right hM0]
  have hbm : base_tail % M < M := Nat.mod_lt base_tail hM
  have hdiv_b := Nat.div_add_mod base_tail M
  by_cases hle : base_tail % M ≤ c
  · have h1 : (c + M - base_tail % M) % M = c - base_tail % M := by
      have heq : c + M - base_tail % M = (c - base_tail % M) + 1 * M := by omega
      rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    have hsum : base_tail + (c - base_tail % M) = c + M * (base_tail / M) := by omega
    rw [hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  · have h1 : (c + M - base_tail % M) % M = c + M - base_tail % M := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have hsum : base_tail + (c + M - base_tail % M) = c + M * (base_tail / M + 1) := by
      calc base_tail + (c + M - base_tail % M)
          = (M * (base_tail / M) + base_tail % M) + (c + M - base_tail % M) := by rw [hdiv_b]
        _ = c + M * (base_tail / M + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

theorem denseOfCirc_eq_self_iff {M b c d : ℕ} (hM : 0 < M) (hc : c < M)
    (hlo : b ≤ d) (hhi : d < b + M) :
    denseOfCirc M b c = d ↔ c = d % M :=
  ⟨fun heq => by rw [← heq, denseOfCirc_mod hM hc], fun h => h ▸ denseOfCirc_mod_self hM hlo hhi⟩

theorem denseOfCirc_succ_of_ne_mod {M b c : ℕ} (hM : 0 < M) (hc : c < M)
    (hhi : denseOfCirc M b c < b + M) (hne : c ≠ b % M) :
    denseOfCirc M (b + 1) c = denseOfCirc M b c := by
  set d := denseOfCirc M b c
  have hlo : b ≤ d := denseOfCirc_ge M b c
  have hne_d : d ≠ b := fun hd => hne ((denseOfCirc_eq_self_iff hM hc le_rfl (by omega)).mp hd)
  rw [← denseOfCirc_mod (base_tail := b) hM hc]
  exact denseOfCirc_mod_self hM (by omega) (by omega)

theorem denseOfCirc_pred_of_lt {M b c : ℕ} (hM : 0 < M) (hc : c < M)
    (hhi : denseOfCirc M (b + 1) c < b + M) :
    denseOfCirc M b c = denseOfCirc M (b + 1) c ∧ c ≠ b % M := by
  set d := denseOfCirc M (b + 1) c
  have hlo : b + 1 ≤ d := denseOfCirc_ge M (b + 1) c
  have hmod : d % M = c := denseOfCirc_mod hM hc
  have heq : denseOfCirc M b c = d := by rw [← hmod]; exact denseOfCirc_mod_self hM (by omega) hhi
  refine ⟨heq, fun hmod_b => ?_⟩
  have hdb : denseOfCirc M b c = b := by
    rw [hmod_b]; exact denseOfCirc_mod_self hM le_rfl (by omega)
  omega

/-- Circular tail-to-dense bijection invariant on `[b, b + n)` modulo `M`. -/
structure WindowInv (M b n : ℕ) (td dt : ℕ → ℕ) : Prop where
  td_lt : ∀ t < n, td t < M
  dense_lt : ∀ t < n, denseOfCirc M b (td t) < b + n
  dt_td : ∀ t < n, dt (td t) = t
  owner_valid : ∀ d, b ≤ d → d < b + n → dt (d % M) < n ∧ td (dt (d % M)) = d % M

/-- Specialization of `WindowInv` to the resting tail window `[n_slabs * slabSize N, +n_tails)`. -/
@[expose] def TailDenseInv (N n_slabs n_tails : ℕ) (td dt : ℕ → ℕ) : Prop :=
  WindowInv (maxTailItems N) (n_slabs * slabSize N) n_tails td dt

theorem windowInv_zero (M b : ℕ) (td dt : ℕ → ℕ) : WindowInv M b 0 td dt :=
  ⟨by omega, by omega, by omega, by omega⟩

/-- Canonical `td` mapping `(b + t) % M` for initial / rebuilt epochs. -/
@[expose] def canonTD (M b t : ℕ) : ℕ := if M = 0 then 0 else (b + t) % M

/-- Canonical `dt` mapping `(c + M - b % M) % M` for initial / rebuilt epochs. -/
@[expose] def canonDT (M b c : ℕ) : ℕ := if M = 0 then 0 else (c + M - b % M) % M

theorem windowInv_canon {M b n : ℕ} (hn : n ≤ M) :
    WindowInv M b n (canonTD M b) (canonDT M b) ∧
    (∀ i, canonTD M b i < max M 1) ∧ (∀ i, canonDT M b i < max M 1) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · obtain rfl : n = 0 := by omega
    refine ⟨windowInv_zero 0 b _ _, fun _ => ?_, fun _ => ?_⟩ <;> simp [canonTD, canonDT]
  · have hM0 : M ≠ 0 := Nat.ne_of_gt hM
    have hmax : max M 1 = M := max_eq_left hM
    have htd_eq : ∀ t, canonTD M b t = (b + t) % M := fun _ => by simp [canonTD, hM0]
    have hdt_eq : ∀ c, canonDT M b c = (c + M - b % M) % M := fun _ => by simp [canonDT, hM0]
    have hcirc : ∀ c, denseOfCirc M b c = b + canonDT M b c := fun c => by
      unfold denseOfCirc; rw [ite_eq_right hM0, hdt_eq]
    refine ⟨⟨fun t _ => by rw [htd_eq]; exact Nat.mod_lt _ hM, fun t ht => ?_, fun t ht => ?_,
      fun d hlo hhi => ?_⟩,
      fun i => by rw [hmax, htd_eq]; exact Nat.mod_lt _ hM,
      fun i => by rw [hmax, hdt_eq]; exact Nat.mod_lt _ hM⟩
    · rw [htd_eq, denseOfCirc_mod_self hM (by omega) (by omega)]; omega
    · have h1 : denseOfCirc M b (canonTD M b t) = b + t := by
        rw [htd_eq]; exact denseOfCirc_mod_self hM (by omega) (by omega)
      rw [hcirc] at h1; omega
    · have h1 := denseOfCirc_mod_self hM hlo (by omega : d < b + M)
      rw [hcirc] at h1
      have hdt_val : canonDT M b (d % M) = d - b := by omega
      rw [hdt_val]; refine ⟨by omega, ?_⟩; rw [htd_eq, Nat.add_sub_of_le hlo]

/-- Map a physical slot `phys < N` to its dense index `d < n`:
when `bucketBits N = 0`, `phys`; else `phys` on full slabs `< gm 0 * slabSize N` and
`denseOfCirc (maxTailItems N) (gm 0 * slabSize N) (td (N - 1 - phys))` on tail slots. -/
@[expose] def denseOfPhys (N : ℕ) (gm td : ℕ → ℕ) (phys : ℕ) : ℕ :=
  if bucketBits N = 0 then phys
  else if phys < gm 0 * slabSize N then phys
  else denseOfCirc (maxTailItems N) (gm 0 * slabSize N) (td (N - 1 - phys))

/-- Physical slot of dense item `d` parameterized by tail window base `b_tail`. -/
@[expose] def physByBase (N b_tail : ℕ) (dt : ℕ → ℕ) (d : ℕ) : ℕ :=
  if bucketBits N = 0 then d
  else if d < b_tail then d
  else N - 1 - dt (d % maxTailItems N)

/-- Resting specialization `physByBase N (gm 0 * slabSize N) dt`. -/
@[expose] def physOfDense (N : ℕ) (gm dt : ℕ → ℕ) (d : ℕ) : ℕ :=
  physByBase N (gm 0 * slabSize N) dt d

/-- Grow the circular window `[b, b + n)` on the right by 1 to `[b, b + (n + 1))`. -/
@[expose] def winGrowRight (M b n : ℕ) : (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → ℕ) × (ℕ → ℕ)
  | (td, dt) =>
    let c := (b + n) % M
    (Function.update td n c, Function.update dt c n)

theorem winGrowRight_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M b n td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    match winGrowRight M b n (td, dt) with
    | (td', dt') => WindowInv M b (n + 1) td' dt' ∧ (∀ i, td' i < M) ∧ (∀ i, dt' i < M) := by
  dsimp only [winGrowRight]
  have hM_pos : 0 < M := by omega
  set c_new := (b + n) % M
  have hc_lt : c_new < M := Nat.mod_lt (b + n) hM_pos
  have hcirc_new : denseOfCirc M b c_new = b + n :=
    denseOfCirc_mod_self hM_pos (by omega) (by omega)
  have htd_ne : ∀ t < n, td t ≠ c_new := fun t ht heq => by
    have := hw.dense_lt t ht; rw [heq, hcirc_new] at this; omega
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun d hlo hhi => ?_⟩,
    fun i => ?_, fun i => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht')]; exact hw.td_lt t ht'
    · rw [Function.update_self]; exact hc_lt
  · rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht')]; have := hw.dense_lt t ht'; omega
    · rw [Function.update_self, hcirc_new]; omega
  · rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht'), Function.update_of_ne (htd_ne t ht')]
      exact hw.dt_td t ht'
    · rw [Function.update_self, Function.update_self]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp (show d < b + n + 1 by omega) with hd_lt | rfl
    · have hown := hw.owner_valid d hlo hd_lt
      have hne_c : d % M ≠ c_new := by rw [← hown.2]; exact htd_ne _ hown.1
      rw [Function.update_of_ne hne_c, Function.update_of_ne (Nat.ne_of_lt hown.1)]
      exact ⟨by omega, hown.2⟩
    · rw [Function.update_self, Function.update_self]; exact ⟨Nat.lt_succ_self n, rfl⟩
  · by_cases hi : i = n
    · subst hi; rw [Function.update_self]; exact hc_lt
    · rw [Function.update_of_ne hi]; exact htd_b i
  · by_cases hi : i = c_new
    · subst hi; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hi]; exact hdt_b i

/-- Grow the circular window `[b + 1, b + 1 + n)` on the left by 1 to `[b, b + (n + 1))`. -/
@[expose] def winGrowLeft (M b n : ℕ) : (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → ℕ) × (ℕ → ℕ)
  | (td, dt) =>
    let c := b % M
    (Function.update td n c, Function.update dt c n)

theorem winGrowLeft_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M (b + 1) n td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    match winGrowLeft M b n (td, dt) with
    | (td', dt') => WindowInv M b (n + 1) td' dt' ∧ (∀ i, td' i < M) ∧ (∀ i, dt' i < M) := by
  dsimp only [winGrowLeft]
  have hM_pos : 0 < M := by omega
  set c_new := b % M
  have hc_lt : c_new < M := Nat.mod_lt b hM_pos
  have hcirc_new : denseOfCirc M b c_new = b := denseOfCirc_mod_self hM_pos le_rfl (by omega)
  have hpred : ∀ t < n, denseOfCirc M b (td t) = denseOfCirc M (b + 1) (td t) ∧ td t ≠ c_new :=
    fun t ht => denseOfCirc_pred_of_lt hM_pos (hw.td_lt t ht) (by have := hw.dense_lt t ht; omega)
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun d hlo hhi => ?_⟩,
    fun i => ?_, fun i => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht')]; exact hw.td_lt t ht'
    · rw [Function.update_self]; exact hc_lt
  · rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht'), (hpred t ht').1]
      have := hw.dense_lt t ht'; omega
    · rw [Function.update_self, hcirc_new]; omega
  · rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht'), Function.update_of_ne (hpred t ht').2]
      exact hw.dt_td t ht'
    · rw [Function.update_self, Function.update_self]
  · rcases eq_or_lt_of_le hlo with rfl | hd_gt
    · rw [Function.update_self, Function.update_self]; exact ⟨Nat.lt_succ_self n, rfl⟩
    · have hown := hw.owner_valid d hd_gt (by omega)
      have hne_c : d % M ≠ c_new := by rw [← hown.2]; exact (hpred _ hown.1).2
      rw [Function.update_of_ne hne_c, Function.update_of_ne (Nat.ne_of_lt hown.1)]
      exact ⟨by omega, hown.2⟩
  · by_cases hi : i = n
    · subst hi; rw [Function.update_self]; exact hc_lt
    · rw [Function.update_of_ne hi]; exact htd_b i
  · by_cases hi : i = c_new
    · subst hi; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hi]; exact hdt_b i

/-- Shrink the circular window `[b, b + (n + 1))` on the right by 1 to `[b, b + n)`. -/
@[expose] def winShrinkRight (M b n : ℕ) : (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → ℕ) × (ℕ → ℕ)
  | (td, dt) =>
    let c_rem := (b + n) % M
    let t_rem := dt c_rem
    let c_last := td n
    (Function.update td t_rem c_last, Function.update dt c_last t_rem)

private theorem winShrink_core_spec {M b b' n : ℕ} {td dt : ℕ → ℕ} {c_rem : ℕ}
    (hw : WindowInv M b (n + 1) td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M)
    (hown_rem : dt c_rem < n + 1 ∧ td (dt c_rem) = c_rem)
    (hlt_b' : ∀ t < n + 1, t ≠ dt c_rem → denseOfCirc M b' (td t) < b' + n)
    (hne_crem : ∀ d, b' ≤ d → d < b' + n → d % M ≠ c_rem)
    (howner : ∀ d, b' ≤ d → d < b' + n → dt (d % M) < n + 1 ∧ td (dt (d % M)) = d % M) :
    let t_rem := dt c_rem
    let c_last := td n
    let td' := Function.update td t_rem c_last
    let dt' := Function.update dt c_last t_rem
    WindowInv M b' n td' dt' ∧ (∀ i, td' i < M) ∧ (∀ i, dt' i < M) := by
  intro t_rem c_last td' dt'
  have hM_pos : 0 < M := by omega
  have ht_rem_lt : t_rem < n + 1 := hown_rem.1
  have htd_trem : td t_rem = c_rem := hown_rem.2
  have hc_last_lt : c_last < M := hw.td_lt n (Nat.lt_succ_self n)
  have htd_inj : ∀ t₁ < n + 1, ∀ t₂ < n + 1, td t₁ = td t₂ → t₁ = t₂ := fun t₁ ht₁ t₂ ht₂ heq => by
    rw [← hw.dt_td t₁ ht₁, ← hw.dt_td t₂ ht₂, heq]
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun d hlo hhi => ?_⟩,
    fun i => ?_, fun i => ?_⟩
  · by_cases heq : t = t_rem
    · subst heq; dsimp only [td']; rw [Function.update_self]; exact hc_last_lt
    · dsimp only [td']; rw [Function.update_of_ne heq]; exact hw.td_lt t (by omega)
  · by_cases heq : t = t_rem
    · subst heq; dsimp only [td']; rw [Function.update_self]
      exact hlt_b' n (Nat.lt_succ_self n) (by omega)
    · dsimp only [td']; rw [Function.update_of_ne heq]; exact hlt_b' t (by omega) heq
  · by_cases heq : t = t_rem
    · subst heq; dsimp only [td', dt']; rw [Function.update_self, Function.update_self]
    · dsimp only [td', dt']; rw [Function.update_of_ne heq]
      have hne_c : td t ≠ c_last := fun hc =>
        Nat.ne_of_lt ht (htd_inj t (by omega) n (Nat.lt_succ_self n) hc)
      rw [Function.update_of_ne hne_c]; exact hw.dt_td t (by omega)
  · have hown := howner d hlo hhi
    have hne_c := hne_crem d hlo hhi
    have hne_trem : dt (d % M) ≠ t_rem := fun heq => hne_c (by rw [← hown.2, heq, htd_trem])
    by_cases hclast : d % M = c_last
    · dsimp only [dt', td']; rw [hclast, Function.update_self, Function.update_self]
      have : t_rem ≠ n := fun heq => hne_c (by rw [hclast, ← htd_trem, heq])
      exact ⟨by omega, rfl⟩
    · dsimp only [dt', td']; rw [Function.update_of_ne hclast, Function.update_of_ne hne_trem]
      have : dt (d % M) ≠ n := fun heq => hclast (by rw [← hown.2, heq])
      exact ⟨by omega, hown.2⟩
  · by_cases hi : i = t_rem
    · subst hi; dsimp only [td']; rw [Function.update_self]; exact hc_last_lt
    · dsimp only [td']; rw [Function.update_of_ne hi]; exact htd_b i
  · by_cases hi : i = c_last
    · subst hi; dsimp only [dt']; rw [Function.update_self]; exact hdt_b c_rem
    · dsimp only [dt']; rw [Function.update_of_ne hi]; exact hdt_b i

theorem winShrinkRight_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M b (n + 1) td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    match winShrinkRight M b n (td, dt) with
    | (td', dt') => WindowInv M b n td' dt' ∧ (∀ i, td' i < M) ∧ (∀ i, dt' i < M) := by
  dsimp only [winShrinkRight]
  have hM_pos : 0 < M := by omega
  have hown_rem := hw.owner_valid (b + n) (by omega) (by omega)
  have htd_inj : ∀ t₁ < n + 1, ∀ t₂ < n + 1, td t₁ = td t₂ → t₁ = t₂ := fun t₁ ht₁ t₂ ht₂ heq => by
    rw [← hw.dt_td t₁ ht₁, ← hw.dt_td t₂ ht₂, heq]
  have hlt_bn : ∀ t < n + 1, t ≠ dt ((b + n) % M) → denseOfCirc M b (td t) < b + n :=
    fun t ht hne => by
    have hlt := hw.dense_lt t ht
    have hne_d : denseOfCirc M b (td t) ≠ b + n := fun hd => by
      have hmod := (denseOfCirc_eq_self_iff hM_pos (hw.td_lt t ht) (by omega) (by omega)).mp hd
      exact hne (htd_inj t ht (dt ((b + n) % M)) hown_rem.1 (hmod.trans hown_rem.2.symm))
    omega
  have hne_crem : ∀ d, b ≤ d → d < b + n → d % M ≠ (b + n) % M := fun d hlo hhi heq => by
    have hd_eq := denseOfCirc_mod_self hM_pos hlo (by omega : d < b + M)
    have hrem_eq := denseOfCirc_mod_self (base_tail := b) (d := b + n) hM_pos (by omega) (by omega)
    rw [heq, hrem_eq] at hd_eq; omega
  exact winShrink_core_spec hw hM htd_b hdt_b hown_rem hlt_bn hne_crem
    (fun d hlo hhi => hw.owner_valid d hlo (by omega))

/-- Shrink the circular window `[b, b + (n + 1))` on the left by 1 to `[b + 1, b + 1 + n)`. -/
@[expose] def winShrinkLeft (M b n : ℕ) : (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → ℕ) × (ℕ → ℕ)
  | (td, dt) =>
    let c_rem := b % M
    let t_rem := dt c_rem
    let c_last := td n
    (Function.update td t_rem c_last, Function.update dt c_last t_rem)

theorem winShrinkLeft_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M b (n + 1) td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    match winShrinkLeft M b n (td, dt) with
    | (td', dt') => WindowInv M (b + 1) n td' dt' ∧ (∀ i, td' i < M) ∧ (∀ i, dt' i < M) := by
  dsimp only [winShrinkLeft]
  have hM_pos : 0 < M := by omega
  have hown_rem := hw.owner_valid b le_rfl (by omega)
  have htd_inj : ∀ t₁ < n + 1, ∀ t₂ < n + 1, td t₁ = td t₂ → t₁ = t₂ := fun t₁ ht₁ t₂ ht₂ heq => by
    rw [← hw.dt_td t₁ ht₁, ← hw.dt_td t₂ ht₂, heq]
  have hsucc : ∀ t < n + 1, t ≠ dt (b % M) → denseOfCirc M (b + 1) (td t) < b + 1 + n :=
    fun t ht hne => by
      have hlt := hw.dense_lt t ht
      have hne_c : td t ≠ b % M := fun hc =>
        hne (htd_inj t ht (dt (b % M)) hown_rem.1 (hc.trans hown_rem.2.symm))
      rw [denseOfCirc_succ_of_ne_mod hM_pos (hw.td_lt t ht) (by omega) hne_c]; omega
  have hne_crem : ∀ d, b + 1 ≤ d → d < b + 1 + n → d % M ≠ b % M := fun d hlo hhi heq => by
    have hd_eq := denseOfCirc_mod_self hM_pos (by omega) (by omega : d < b + M)
    have hrem_eq := denseOfCirc_mod_self (base_tail := b) (d := b) hM_pos le_rfl (by omega)
    rw [heq, hrem_eq] at hd_eq; omega
  exact winShrink_core_spec hw hM htd_b hdt_b hown_rem hsucc hne_crem
    (fun d hlo hhi => hw.owner_valid d (by omega) (by omega))

theorem physByBase_winGrowRight {N b n : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hM : n + 1 ≤ maxTailItems N) :
    match winGrowRight (maxTailItems N) b n (td, dt) with
    | (_, dt') =>
      physByBase N b dt' (b + n) = N - 1 - n ∧
      (∀ d < b + n, physByBase N b dt' d = physByBase N b dt d) := by
  dsimp only [winGrowRight]
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hM_pos : 0 < maxTailItems N := by omega
  refine ⟨?_, fun d hd => ?_⟩
  · unfold physByBase; rw [ite_eq_right hb0, ite_eq_right (by omega), Function.update_self]
  · simp only [physByBase, hb0, ↓reduceIte]
    split_ifs with hlt
    · rfl
    · have hlo : b ≤ d := Nat.le_of_not_lt hlt
      have hne : d % maxTailItems N ≠ (b + n) % maxTailItems N := fun heq => by
        have h1 := denseOfCirc_mod_self hM_pos hlo (by omega : d < b + maxTailItems N)
        have h2 := denseOfCirc_mod_self (base_tail := b) (d := b + n) hM_pos (by omega) (by omega)
        rw [heq, h2] at h1; omega
      rw [Function.update_of_ne hne]

theorem physByBase_winGrowLeft {N b n : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hM : n + 1 ≤ maxTailItems N) :
    match winGrowLeft (maxTailItems N) b n (td, dt) with
    | (_, dt') =>
      physByBase N b dt' b = N - 1 - n ∧
      (∀ d < b + 1 + n, d ≠ b → physByBase N b dt' d = physByBase N (b + 1) dt d) := by
  dsimp only [winGrowLeft]
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hM_pos : 0 < maxTailItems N := by omega
  refine ⟨?_, fun d hd hne => ?_⟩
  · unfold physByBase; rw [ite_eq_right hb0, ite_eq_right (by omega), Function.update_self]
  · simp only [physByBase, hb0, ↓reduceIte]
    by_cases hlt : d < b
    · have hlt1 : d < b + 1 := by omega
      simp only [hlt, hlt1, ↓reduceIte]
    · have hgt : ¬d < b + 1 := by omega
      simp only [hlt, hgt, ↓reduceIte]
      have hlo : b ≤ d := by omega
      have hne_mod : d % maxTailItems N ≠ b % maxTailItems N := fun heq => by
        have h1 := denseOfCirc_mod_self hM_pos hlo (by omega : d < b + maxTailItems N)
        have h2 := denseOfCirc_mod_self (base_tail := b) (d := b) hM_pos le_rfl (by omega)
        rw [heq, h2] at h1; exact hne h1.symm
      rw [Function.update_of_ne hne_mod]

theorem physByBase_winShrinkRight {N b n : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hw : WindowInv (maxTailItems N) b (n + 1) td dt)
    (hM : n + 1 ≤ maxTailItems N) :
    match winShrinkRight (maxTailItems N) b n (td, dt) with
    | (_, dt') =>
      let d_last := denseOfCirc (maxTailItems N) b (td n)
      d_last < b + n + 1 ∧
      physByBase N b dt' d_last = physByBase N b dt (b + n) ∧
      (∀ d < b + n, d ≠ d_last → physByBase N b dt' d = physByBase N b dt d) := by
  dsimp only [winShrinkRight]
  set M := maxTailItems N
  set d_last := denseOfCirc M b (td n)
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hM_pos : 0 < M := by omega
  have hd_last_lt : d_last < b + n + 1 := hw.dense_lt n (Nat.lt_succ_self n)
  have hd_last_ge : b ≤ d_last := denseOfCirc_ge M b (td n)
  have hc_last_lt : td n < M := hw.td_lt n (Nat.lt_succ_self n)
  have hd_last_mod : d_last % M = td n := denseOfCirc_mod hM_pos hc_last_lt
  refine ⟨hd_last_lt, ?_, fun d hd hne => ?_⟩
  · have hnot1 : ¬d_last < b := by omega
    have hnot2 : ¬(b + n) < b := by omega
    simp only [physByBase, hb0, hnot1, hnot2, ↓reduceIte]
    change N - 1 - Function.update dt (td n) (dt ((b + n) % M)) (d_last % M) =
      N - 1 - dt ((b + n) % M)
    rw [hd_last_mod, Function.update_self]
  · simp only [physByBase, hb0, ↓reduceIte]
    split_ifs with hlt
    · rfl
    · have hlo : b ≤ d := Nat.le_of_not_lt hlt
      have hne_mod : d % M ≠ td n := fun heq => hne <| by
        rw [← (denseOfCirc_eq_self_iff hM_pos hc_last_lt hlo (by omega : d < b + M)).mpr heq.symm]
      change N - 1 - Function.update dt (td n) (dt ((b + n) % M)) (d % M) = N - 1 - dt (d % M)
      rw [Function.update_of_ne hne_mod]

theorem physByBase_winShrinkLeft {N b n : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hw : WindowInv (maxTailItems N) b (n + 1) td dt)
    (hM : n + 1 ≤ maxTailItems N) :
    match winShrinkLeft (maxTailItems N) b n (td, dt) with
    | (_, dt') =>
      let d_last := denseOfCirc (maxTailItems N) b (td n)
      b ≤ d_last ∧ d_last < b + n + 1 ∧
      (b < d_last → physByBase N (b + 1) dt' d_last = N - 1 - dt (b % maxTailItems N)) ∧
      (∀ d < b + 1 + n, d ≠ b → d ≠ d_last →
        physByBase N (b + 1) dt' d = physByBase N b dt d) := by
  dsimp only [winShrinkLeft]
  set M := maxTailItems N
  set d_last := denseOfCirc M b (td n)
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hM_pos : 0 < M := by omega
  have hd_last_lt : d_last < b + n + 1 := hw.dense_lt n (Nat.lt_succ_self n)
  have hd_last_ge : b ≤ d_last := denseOfCirc_ge M b (td n)
  have hc_last_lt : td n < M := hw.td_lt n (Nat.lt_succ_self n)
  have hd_last_mod : d_last % M = td n := denseOfCirc_mod hM_pos hc_last_lt
  refine ⟨hd_last_ge, hd_last_lt, fun hgt => ?_, fun d hd hneb hne => ?_⟩
  · have hnot : ¬d_last < b + 1 := by omega
    simp only [physByBase, hb0, hnot, ↓reduceIte]
    change N - 1 - Function.update dt (td n) (dt (b % M)) (d_last % M) = N - 1 - dt (b % M)
    rw [hd_last_mod, Function.update_self]
  · simp only [physByBase, hb0, ↓reduceIte]
    by_cases hlt : d < b
    · have hlt1 : d < b + 1 := by omega
      simp only [hlt, hlt1, ↓reduceIte]
    · have hnot1 : ¬d < b + 1 := by omega
      simp only [hlt, hnot1, ↓reduceIte]
      have hd_ge_b : b ≤ d := by omega
      have hne_mod : d % M ≠ td n := fun heq => hne <| by
        rw [← (denseOfCirc_eq_self_iff hM_pos hc_last_lt hd_ge_b
          (by omega : d < b + M)).mpr heq.symm]
      change N - 1 - Function.update dt (td n) (dt (b % M)) (d % M) = N - 1 - dt (d % M)
      rw [Function.update_of_ne hne_mod]

/-! ## Section 2: Direct $O(1)$ Bucket-Owner and Logical-Slot Inversion on Dense Indices -/

/-- Recover the owning Feistel bucket `b < numBuckets N` of dense index `d < totalSlots N gm` from
`GlobalMeta` (`gm`) and `DenseToTail` (`dt`). -/
@[expose] def ownerBucketOfDense (N : ℕ) (gm dt : ℕ → ℕ) (d : ℕ) : ℕ :=
  if bucketBits N = 0 then 0
  else if d < gm 0 * slabSize N then gm (gmSlabOwnerBIdx N (d / slabSize N))
  else gm (gmTailOwnerIdx N (dt (d % maxTailItems N))) / tailCapPerBucket N

/-- Recover the logical within-bucket slot index `j < bCount N gm b` of dense index `d`. -/
@[expose] def logicalIdxOfDense (N : ℕ) (gm dt : ℕ → ℕ) (d : ℕ) : ℕ :=
  if bucketBits N = 0 then d
  else if d < gm 0 * slabSize N then
    let p := d / slabSize N
    gm (gmSlabOwnerSIdx N p) * slabSize N + (slabSize N - 1 - d % slabSize N)
  else
    let desc := gm (gmTailOwnerIdx N (dt (d % maxTailItems N)))
    let b := desc / tailCapPerBucket N
    gm (gmQIdx b) * slabSize N + desc % tailCapPerBucket N

theorem denseOfPhys_slab {N : ℕ} (gm td : ℕ → ℕ) {g : ℕ} (hg : g < gm 0 * slabSize N) :
    denseOfPhys N gm td g = g := by
  unfold denseOfPhys; split_ifs <;> rfl

theorem denseOfPhys_tail {N : ℕ} (hb : 0 < bucketBits N) {gm : ℕ → ℕ}
    (hSN : gm 0 * slabSize N + gm 1 ≤ N) (td : ℕ → ℕ) {t : ℕ} (ht : t < gm 1) :
    denseOfPhys N gm td (N - 1 - t) =
      denseOfCirc (maxTailItems N) (gm 0 * slabSize N) (td t) := by
  have hb0 : bucketBits N ≠ 0 := by omega
  have hnotS : ¬(N - 1 - t < gm 0 * slabSize N) := by omega
  have hsub : N - 1 - (N - 1 - t) = t := by omega
  unfold denseOfPhys; rw [ite_eq_right hb0, ite_eq_right hnotS, hsub]

theorem physOfDense_denseOfPhys_slab {N : ℕ} (gm td dt : ℕ → ℕ) {g : ℕ}
    (hg : g < gm 0 * slabSize N) :
    physOfDense N gm dt (denseOfPhys N gm td g) = g := by
  rw [denseOfPhys_slab gm td hg]
  unfold physOfDense physByBase; split_ifs <;> rfl

theorem physOfDense_denseOfPhys_tail {N : ℕ} {gm td dt : ℕ → ℕ}
    (htd : TailDenseInv N (gm 0) (gm 1) td dt) (hb : 0 < bucketBits N)
    (hSN : gm 0 * slabSize N + gm 1 ≤ N) {t : ℕ} (ht : t < gm 1) :
    physOfDense N gm dt (denseOfPhys N gm td (N - 1 - t)) = N - 1 - t := by
  rw [denseOfPhys_tail hb hSN td ht]
  have hb0 : bucketBits N ≠ 0 := by omega
  have hc_lt : td t < maxTailItems N := htd.td_lt t ht
  have hM_pos : 0 < maxTailItems N := by omega
  have hge := denseOfCirc_ge (maxTailItems N) (gm 0 * slabSize N) (td t)
  have hnotS : ¬(denseOfCirc (maxTailItems N) (gm 0 * slabSize N) (td t) < gm 0 * slabSize N) :=
    by omega
  unfold physOfDense physByBase
  rw [ite_eq_right hb0, ite_eq_right hnotS, denseOfCirc_mod hM_pos hc_lt, htd.dt_td t ht]

/-- Active slot count (`= Succinct.totalSlots N gm`). -/
abbrev epochTotalSlots (N : ℕ) (gm : ℕ → ℕ) : ℕ :=
  if bucketBits N = 0 then gm 0 else gm 0 * slabSize N + gm 1

/-- Under `SlotStoreInv N gm` and `TailDenseInv N (gm 0) (gm 1) td dt`, every dense index
`d < epochTotalSlots N gm` maps via `(ownerBucketOfDense, logicalIdxOfDense)` to a valid active
bucket slot `(b, j)` with `denseOfPhys N gm td (slotOf N gm b j) = d`. -/
theorem ownerBucketOfDense_lt_and_slotOf {N : ℕ} {gm td dt : ℕ → ℕ}
    (hslot : SlotStoreInv N gm) (htd : 0 < bucketBits N → TailDenseInv N (gm 0) (gm 1) td dt)
    {d : ℕ} (hd : d < epochTotalSlots N gm) :
    let b := ownerBucketOfDense N gm dt d
    let j := logicalIdxOfDense N gm dt d
    b < numBuckets N ∧ j < bCount N gm b ∧ denseOfPhys N gm td (slotOf N gm b j) = d := by
  intro b j
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · have hB1 : numBuckets N = 1 := by simp [numBuckets, hb0]
    have hb_eq : b = 0 := by simp [b, ownerBucketOfDense, hb0]
    have hj_eq : j = d := by simp [j, logicalIdxOfDense, hb0]
    unfold epochTotalSlots at hd; simp only [hb0, ↓reduceIte] at hd
    refine ⟨by omega, ?_, ?_⟩
    · unfold bCount; simp only [hb0, hb_eq, hj_eq, ↓reduceIte]; exact hd
    · unfold denseOfPhys slotOf; simp [hb0, hj_eq]
  · have htd' := htd hb_pos
    have hb_ne : bucketBits N ≠ 0 := by omega
    unfold epochTotalSlots at hd; rw [ite_eq_right hb_ne] at hd
    have hK : 0 < slabSize N := slabSize_pos N
    have hslab := hslot.multi_slab hb_pos
    have htail := hslot.multi_tail hb_pos
    have hSN := hslot.multi_total_le hb_pos
    by_cases hdS : d < gm 0 * slabSize N
    · have hp_lt : d / slabSize N < gm 0 := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hrem_lt : d % slabSize N < slabSize N := Nat.mod_lt d hK
      obtain ⟨hb_lt, hs_lt, hptr_eq⟩ := hslab.owner_valid (d / slabSize N)
        (by rwa [← hslab.nslabs_eq])
      have hb_def : b = gm (gmSlabOwnerBIdx N (d / slabSize N)) := by
        simp [b, ownerBucketOfDense, hb_ne, hdS]
      have hj_def : j = gm (gmSlabOwnerSIdx N (d / slabSize N)) * slabSize N +
          (slabSize N - 1 - d % slabSize N) := by simp [j, logicalIdxOfDense, hb_ne, hdS]
      have hj_slab : j < gm (gmQIdx b) * slabSize N := by
        rw [hj_def, hb_def]
        have h1 := Nat.mul_le_mul_right (slabSize N) hs_lt
        rw [Nat.add_one_mul] at h1; omega
      have hj_bc : j < bCount N gm b := by
        unfold bCount; rw [ite_eq_right hb_ne, ite_eq_left (by omega)]; omega
      have hj_div : j / slabSize N = gm (gmSlabOwnerSIdx N (d / slabSize N)) := by
        rw [hj_def, Nat.add_comm, Nat.add_mul_div_right _ _ hK,
          Nat.div_eq_of_lt (by omega), Nat.zero_add]
      have hj_mod : j % slabSize N = slabSize N - 1 - d % slabSize N := by
        rw [hj_def, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have hslot_eq : slotOf N gm b j = d := by
        unfold slotOf
        rw [ite_eq_right hb_ne, ite_eq_left hj_slab, hj_div, hj_mod,
          show slabPtrOf N gm b (gm (gmSlabOwnerSIdx N (d / slabSize N))) = d / slabSize N by
            rw [hb_def]; exact hptr_eq]
        have hdiv_mod := Nat.div_add_mod d (slabSize N)
        have hcomm : (d / slabSize N) * slabSize N = slabSize N * (d / slabSize N) :=
          Nat.mul_comm _ _
        omega
      exact ⟨by omega, hj_bc, by rw [hslot_eq, denseOfPhys_slab gm td hdS]⟩
    · have hd_ge : gm 0 * slabSize N ≤ d := by omega
      obtain ⟨ht_lt, htd_eq⟩ := htd'.owner_valid d hd_ge hd
      set t := dt (d % maxTailItems N)
      set desc := gm (gmTailOwnerIdx N t)
      obtain ⟨hb_lt, hr_lt, hptr_eq⟩ := htail.owner_valid t (by rwa [← htail.ntails_eq])
      have hb_def : b = desc / tailCapPerBucket N := by
        simp [b, ownerBucketOfDense, hb_ne, hdS, t, desc]
      have hb_lt' : b < numBuckets N := hb_def ▸ hb_lt
      have hr_lt' : desc % tailCapPerBucket N < gm (gmRIdx b) := hb_def ▸ hr_lt
      have hj_def : j = gm (gmQIdx b) * slabSize N + desc % tailCapPerBucket N := by
        simp [j, logicalIdxOfDense, hb_ne, hdS, t, desc, hb_def]
      have hj_not_slab : ¬(j < gm (gmQIdx b) * slabSize N) := by omega
      have hj_bc : j < bCount N gm b := by
        unfold bCount; rw [ite_eq_right hb_ne, ite_eq_left hb_lt']; omega
      have hj_sub : j - gm (gmQIdx b) * slabSize N = desc % tailCapPerBucket N := by omega
      have hdesc_eq : b * tailCapPerBucket N + desc % tailCapPerBucket N = desc := by
        rw [hb_def, Nat.mul_comm, Nat.div_add_mod]
      have hslot_eq : slotOf N gm b j = N - 1 - t := by
        unfold slotOf; rw [ite_eq_right hb_ne, ite_eq_right hj_not_slab, hj_sub]
        unfold gmTailPtrIdx; rw [hdesc_eq]
        change N - 1 - gm (gmTailPtrFlatIdx N (gm (gmTailOwnerIdx N t))) = N - 1 - t
        rw [hptr_eq]
      have hM_pos : 0 < maxTailItems N := by have := htd'.td_lt t ht_lt; omega
      have hM_le : gm 1 ≤ maxTailItems N := htail.ntails_eq.trans_le htail.ntails_le
      refine ⟨hb_lt', hj_bc, ?_⟩
      rw [hslot_eq, denseOfPhys_tail hb_pos hSN td ht_lt, htd_eq]
      exact denseOfCirc_mod_self hM_pos hd_ge (by omega)

theorem physOfDense_denseOfPhys_slotOf {N : ℕ} {gm td dt : ℕ → ℕ}
    (hslot : SlotStoreInv N gm) (htd : 0 < bucketBits N → TailDenseInv N (gm 0) (gm 1) td dt)
    {b j : ℕ} (hb : b < numBuckets N) (hj : j < bCount N gm b) :
    physOfDense N gm dt (denseOfPhys N gm td (slotOf N gm b j)) = slotOf N gm b j := by
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · simp [physOfDense, physByBase, denseOfPhys, hb0]
  · have hb_ne : bucketBits N ≠ 0 := by omega
    have hK : 0 < slabSize N := slabSize_pos N
    have hslab := hslot.multi_slab hb_pos
    have htail := hslot.multi_tail hb_pos
    have hSN := hslot.multi_total_le hb_pos
    unfold bCount at hj; simp only [hb_ne, ↓reduceIte, hb] at hj
    by_cases hj_slab : j < gm (gmQIdx b) * slabSize N
    · have hs_lt : j / slabSize N < gm (gmQIdx b) := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hp_lt : slabPtrOf N gm b (j / slabSize N) < gm 0 := by
        rw [hslab.nslabs_eq]; exact hslab.ptr_lt b hb _ hs_lt
      have hmod_lt : j % slabSize N < slabSize N := Nat.mod_lt j hK
      have hslot_lt_S : slotOf N gm b j < gm 0 * slabSize N := by
        unfold slotOf; rw [ite_eq_right hb_ne, ite_eq_left hj_slab]
        have h1 := Nat.mul_le_mul_right (slabSize N) hp_lt
        rw [Nat.add_one_mul] at h1; omega
      exact physOfDense_denseOfPhys_slab gm td dt hslot_lt_S
    · have hr_lt : j - gm (gmQIdx b) * slabSize N < gm (gmRIdx b) := by omega
      have ht_lt : gm (gmTailPtrIdx N b (j - gm (gmQIdx b) * slabSize N)) < gm 1 := by
        rw [htail.ntails_eq]; exact htail.ptr_lt b hb _ hr_lt
      have hslot_eq : slotOf N gm b j =
          N - 1 - gm (gmTailPtrIdx N b (j - gm (gmQIdx b) * slabSize N)) := by
        unfold slotOf; rw [ite_eq_right hb_ne, ite_eq_right hj_slab]
      rw [hslot_eq]; exact physOfDense_denseOfPhys_tail (htd hb_pos) hb_pos hSN ht_lt

theorem denseOfPhys_slotOf_lt_and_inv {N : ℕ} {gm td dt : ℕ → ℕ}
    (hslot : SlotStoreInv N gm) (htd : 0 < bucketBits N → TailDenseInv N (gm 0) (gm 1) td dt)
    {b j : ℕ} (hb : b < numBuckets N) (hj : j < bCount N gm b) :
    let d := denseOfPhys N gm td (slotOf N gm b j)
    d < epochTotalSlots N gm ∧ ownerBucketOfDense N gm dt d = b ∧
      logicalIdxOfDense N gm dt d = j := by
  intro d
  have hd_lt : d < epochTotalSlots N gm := by
    rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
    · have hb_eq : b = 0 := by simp only [numBuckets, hb0, pow_zero] at hb; omega
      subst hb_eq; unfold bCount at hj; simp only [hb0, ↓reduceIte] at hj
      simpa [d, denseOfPhys, slotOf, epochTotalSlots, hb0] using hj
    · have hb_ne : bucketBits N ≠ 0 := by omega
      unfold epochTotalSlots; rw [ite_eq_right hb_ne]
      have hK : 0 < slabSize N := slabSize_pos N
      have hslab := hslot.multi_slab hb_pos
      have htail := hslot.multi_tail hb_pos
      have hSN := hslot.multi_total_le hb_pos
      unfold bCount at hj; simp only [hb_ne, ↓reduceIte, hb] at hj
      by_cases hj_slab : j < gm (gmQIdx b) * slabSize N
      · have hs_lt : j / slabSize N < gm (gmQIdx b) := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
        have hp_lt : slabPtrOf N gm b (j / slabSize N) < gm 0 := by
          rw [hslab.nslabs_eq]; exact hslab.ptr_lt b hb _ hs_lt
        have hmod_lt : j % slabSize N < slabSize N := Nat.mod_lt j hK
        have hslot_lt_S : slotOf N gm b j < gm 0 * slabSize N := by
          unfold slotOf; rw [ite_eq_right hb_ne, ite_eq_left hj_slab]
          have h1 := Nat.mul_le_mul_right (slabSize N) hp_lt
          rw [Nat.add_one_mul] at h1; omega
        have hd_eq : d = slotOf N gm b j := denseOfPhys_slab gm td hslot_lt_S
        omega
      · have hr_lt : j - gm (gmQIdx b) * slabSize N < gm (gmRIdx b) := by omega
        have ht_lt : gm (gmTailPtrIdx N b (j - gm (gmQIdx b) * slabSize N)) < gm 1 := by
          rw [htail.ntails_eq]; exact htail.ptr_lt b hb _ hr_lt
        have hslot_eq : slotOf N gm b j =
            N - 1 - gm (gmTailPtrIdx N b (j - gm (gmQIdx b) * slabSize N)) := by
          unfold slotOf; rw [ite_eq_right hb_ne, ite_eq_right hj_slab]
        change denseOfPhys N gm td (slotOf N gm b j) < gm 0 * slabSize N + gm 1
        rw [hslot_eq, denseOfPhys_tail hb_pos hSN td ht_lt]
        exact (htd hb_pos).dense_lt _ ht_lt
  obtain ⟨hb'_lt, hj'_lt, hd_round⟩ := ownerBucketOfDense_lt_and_slotOf hslot htd hd_lt
  set b' := ownerBucketOfDense N gm dt d
  set j' := logicalIdxOfDense N gm dt d
  have hvirt_eq := congrArg (physOfDense N gm dt) hd_round
  rw [physOfDense_denseOfPhys_slotOf hslot htd hb'_lt hj'_lt,
    physOfDense_denseOfPhys_slotOf hslot htd hb hj] at hvirt_eq
  obtain ⟨hb_eq, hj_eq⟩ := (slotOf_lt_and_injective hslot).2 b' hb'_lt j' hj'_lt b hb j hj hvirt_eq
  exact ⟨hd_lt, hb_eq, hj_eq⟩

theorem physOfDense_eq_slotOf_owner {N : ℕ} {gm td dt : ℕ → ℕ}
    (hslot : SlotStoreInv N gm) (htd : 0 < bucketBits N → TailDenseInv N (gm 0) (gm 1) td dt)
    {d : ℕ} (hd : d < epochTotalSlots N gm) :
    physOfDense N gm dt d =
      slotOf N gm (ownerBucketOfDense N gm dt d) (logicalIdxOfDense N gm dt d) := by
  obtain ⟨hb_lt, hj_lt, hd_eq⟩ := ownerBucketOfDense_lt_and_slotOf hslot htd hd
  conv_lhs => rw [← hd_eq]
  exact physOfDense_denseOfPhys_slotOf hslot htd hb_lt hj_lt

/-! ## Section 3: Fixed-Capacity Array Coupling Invariants (`WindowCoupled`, `FixedCoupled`) -/

/-- Ghost word width `w + 16` used for the mathematical fixed-capacity reference state `s_fix`,
ensuring `Fits (ghostW w) (Succinct.space U V (ghostW w) N)` for all `N ≤ U ≤ 2 ^ w`. -/
@[expose] def ghostW (w : ℕ) : ℕ := w + 16

/-- Coupling invariant between a fixed-capacity state `s_fix` (at `base = 0`, `ghostW w`)
and a compacted state `s` at `(metaBase, itemBase)` over window `[b_win, b_win + n_win)`. -/
structure WindowCoupled (metaBase itemBase U V w N b_win n_win m_items : ℕ)
    (s_fix s : Memory.State) : Prop where
  gm_eq : compGmAt metaBase U w N s.mem =
    gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
  lm_eq : compLmAt metaBase U w N s.mem =
    lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
  win_inv : WindowInv (maxTailItems N) b_win n_win
    (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem)
  td_lt : ∀ i, compTDAt metaBase U w N s.mem i < max (maxTailItems N) 1
  dt_lt : ∀ i, compDTAt metaBase U w N s.mem i < max (maxTailItems N) 1
  quot_eq : ∀ d < m_items, compQuotAt itemBase U V w N m_items s.mem d =
    quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
      (physByBase N b_win (compDTAt metaBase U w N s.mem) d)
  val_eq : ∀ d < m_items, compValAt itemBase U V w N m_items s.mem d =
    valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
      (physByBase N b_win (compDTAt metaBase U w N s.mem) d)

/-- Resting window coupling (`b_win = gm 0 * slabSize N`, and `n_win = gm 1` when
`0 < bucketBits N`). -/
@[expose] def FixedCoupled (metaBase itemBase U V w N : ℕ) (s_fix s : Memory.State) : Prop :=
  let gm := compGmAt metaBase U w N s.mem
  WindowCoupled metaBase itemBase U V w N (gm 0 * slabSize N)
    (if bucketBits N = 0 then 0 else gm 1) (epochTotalSlots N gm) s_fix s

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
