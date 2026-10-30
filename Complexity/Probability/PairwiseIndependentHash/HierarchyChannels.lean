/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.DetectedHierarchy
public import Complexity.Probability.PairwiseIndependentHash.DetectorChannels
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.Bertrand

/-!
# Affine channels for every stage of the hierarchy

The stage bound `Matrix.sub_hierarchyReward_le` of the correction-and-copy hierarchy needs
retention channels at every rate `q⁻¹ ^ l`, `q = 2 ^ H`, with constants that do not depend on the
stage. This file supplies them with the affine channels over prime fields
(`Cslib.Probability.retentionChannels_affineRetains`), following the OpenAI preprint (2026-09-23),
Sections 2–3 [OpenAI2026LogSpace]: stage `l` hashes numerical identifiers into a prime field
`𝔽_(P_l)` with `P_l ≥ 2 ^ l` larger than every identifier, and retains at side
`L_l = ⌈P_l 2^(-l)⌉`, so at rate `(2^(-l)) ^ H = q⁻¹ ^ l`. The constants are those of the affine
channels, `c_π = 1`, `C_π = C_pair = 2 ^ H` and `C_var = 4`, at every stage
(`Cslib.Probability.retentionChannels_stageChannel`).

With these channels the stage bound holds without any channel hypothesis
(`Matrix.sub_hierarchyReward_le_affine`). For radix identifiers, stage `l` is
`Fin (n (m + 1) ^ l)`, where the copy `y` of the parent `x` is the number `y + (m + 1) x`
(`Matrix.radixCopyEquiv`) [OpenAI2026LogSpace, Section 4.5: appending a radix-`D₀` digit]. This
gives a fully concrete instance of the hierarchy and its bound
(`Matrix.sub_hierarchyReward_le_radix`). This instantiates the reduced algebraic-stage bound;
the preprint's full threshold ladder and later-estimation root/complement regularity for `Q`
and the cutoffs remain separate requirements. The modulus is the least prime at least
`max (2 ^ l) (M l)`, obtained by computable natural-number search. Bertrand's postulate gives
`P_l ≤ 2 * max (2 ^ l) (M l)`, hence explicit logarithm and binary-length bounds. The side is
computed by natural ceiling division and proved equal to the real-ceiling formula above.
These arithmetic definitions and value bounds do not certify a machine-space implementation.

## Main definitions

* `Cslib.Probability.stageModulus`, `Cslib.Probability.stageSide`: the least-prime modulus and
  natural ceiling-division side of stage `l`.
* `Cslib.Probability.stageChannel`: the affine channel on identifiers below `M l`.

## Main results

* `Cslib.Probability.retentionChannels_stageChannel`: the channel interface at rate
  `(2 ^ H)⁻¹ ^ l` with uniform constants.
* `Cslib.Probability.le_stageModulus`, `Cslib.Probability.stageModulus_le_of_prime`: the modulus
  meets both lower bounds and is the least prime that does so.
* `Cslib.Probability.stageModulus_le_two_mul`, `Cslib.Probability.log2_stageModulus_le`,
  `Cslib.Probability.size_stageModulus_le`: quantitative modulus and binary-length bounds.
* `Cslib.Probability.stageSide_eq_ceil`: the exact real-ceiling identity for the computable side.
* `Matrix.sub_hierarchyReward_le_affine`: the stage bound with these channels.
* `Matrix.sub_hierarchyReward_le_radix`: the stage bound on radix identifiers.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 2–3, Section 4.5 and Proposition 4.7 (preprint, not peer reviewed)
-/

public section

open Finset

namespace Cslib.Probability

variable (H : ℕ) (M : ℕ → ℕ)

/-- The least prime modulus of stage `l`: at least `2 ^ l` and the identifier bound `M l`.
The definition is computable natural-number search; no machine-space bound is asserted. -/
def stageModulus (l : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (max (2 ^ l) (M l)))

theorem stageModulus_prime (l : ℕ) : (stageModulus M l).Prime :=
  (Nat.find_spec (Nat.exists_infinite_primes (max (2 ^ l) (M l)))).2

/-- The modulus meets both the stage-rate and identifier bounds. -/
theorem le_stageModulus (l : ℕ) : max (2 ^ l) (M l) ≤ stageModulus M l :=
  (Nat.find_spec (Nat.exists_infinite_primes (max (2 ^ l) (M l)))).1

/-- No larger prime is selected when a smaller prime already meets both bounds. -/
theorem stageModulus_le_of_prime (l : ℕ) {p : ℕ} (hp : p.Prime)
    (hbound : max (2 ^ l) (M l) ≤ p) : stageModulus M l ≤ p :=
  Nat.find_min' (Nat.exists_infinite_primes (max (2 ^ l) (M l))) ⟨hbound, hp⟩

/-- Bertrand's postulate bounds the least admissible prime by twice the lower bound. -/
theorem stageModulus_le_two_mul (l : ℕ) : stageModulus M l ≤ 2 * max (2 ^ l) (M l) := by
  have hbound : 0 < max (2 ^ l) (M l) := (pow_pos (by norm_num) l).trans_le (le_max_left _ _)
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul _ hbound.ne'
  exact (stageModulus_le_of_prime M l hp hlt.le).trans hle

/-- The base-two logarithm costs at most one above the larger input logarithm. -/
theorem log2_stageModulus_le (l : ℕ) :
    (stageModulus M l).log2 ≤ max l (M l).log2 + 1 := by
  have hbound : 0 < max (2 ^ l) (M l) := (pow_pos (by norm_num) l).trans_le (le_max_left _ _)
  simp only [Nat.log2_eq_log_two]
  calc Nat.log 2 (stageModulus M l) ≤ Nat.log 2 (2 * max (2 ^ l) (M l)) :=
      Nat.log_monotone (stageModulus_le_two_mul M l)
    _ = Nat.log 2 (max (2 ^ l) (M l)) + 1 := by
      rw [Nat.mul_comm, Nat.log_mul_base (by norm_num) hbound.ne']
    _ = max l (Nat.log 2 (M l)) + 1 := by
      rw [(Nat.log_monotone (b := 2)).map_max, Nat.log_pow (by norm_num)]

/-- The binary length is at most one more than the larger input length. -/
theorem size_stageModulus_le (l : ℕ) :
    (stageModulus M l).size ≤ max (l + 1) (M l).size + 1 := by
  have hbound : 0 < max (2 ^ l) (M l) := (pow_pos (by norm_num) l).trans_le (le_max_left _ _)
  have hsize : Monotone Nat.size := fun _ _ h => Nat.size_le_size h
  calc (stageModulus M l).size ≤ (2 * max (2 ^ l) (M l)).size :=
      Nat.size_le_size (stageModulus_le_two_mul M l)
    _ = (max (2 ^ l) (M l) <<< 1).size := by rw [Nat.shiftLeft_eq]; norm_num [Nat.mul_comm]
    _ = (max (2 ^ l) (M l)).size + 1 := Nat.size_shiftLeft hbound.ne' 1
    _ = max (l + 1) (M l).size + 1 := by rw [hsize.map_max, Nat.size_pow]

/-- The stage modulus is prime, so its finite-field and seed instances are available to
importers. -/
instance (l : ℕ) : Fact (stageModulus M l).Prime := ⟨stageModulus_prime M l⟩

/-- The retention-box side, computed by natural ceiling division `P_l ⌈/⌉ 2^l`. -/
abbrev stageSide (l : ℕ) : ℕ := stageModulus M l ⌈/⌉ (2 ^ l)

/-- Natural ceiling division gives exactly the original real-ceiling retention-box side. -/
theorem stageSide_eq_ceil (l : ℕ) :
    stageSide M l = ⌈(stageModulus M l : ℝ) * (2⁻¹ : ℝ) ^ l⌉₊ := by
  apply eq_of_forall_ge_iff
  intro n
  rw [stageSide, ceilDiv_le_iff_le_mul (by positivity : 0 < (2 : ℕ) ^ l), Nat.ceil_le,
    inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ l)]
  norm_cast
  rw [Nat.mul_comm]

theorem stageSide_le_stageModulus (l : ℕ) : stageSide M l ≤ stageModulus M l := by
  apply (ceilDiv_le_iff_le_mul (by positivity : 0 < (2 : ℕ) ^ l)).2
  exact Nat.le_mul_of_pos_left _ (by positivity)

theorem stageSide_pos (l : ℕ) : 0 < stageSide M l := by
  by_contra h
  have hz : stageSide M l ≤ 0 := Nat.le_of_not_gt h
  have hp := (ceilDiv_le_iff_le_mul (by positivity : 0 < (2 : ℕ) ^ l)).1 hz
  have hprime := (stageModulus_prime M l).pos
  omega

/-- The seeds of the affine channel of stage `l`: affine maps `𝔽_(P_l) → 𝔽_(P_l) ^ H`. -/
abbrev stageSeed (l : ℕ) : Type :=
  Matrix (Fin H) (Fin 1) (ZMod (stageModulus M l)) × (Fin H → ZMod (stageModulus M l))

/-- **The affine channel of stage `l`**: the seed `s` retains a vertex `v` when it retains its
identifier `ident l v`, read in `𝔽_(P_l)`. -/
abbrev stageChannel {V : ℕ → Type*} (ident : ∀ l, V l → ℕ) (l : ℕ) (s : stageSeed H M l)
    (v : V l) : Prop :=
  affineRetains (stageModulus M l) H (stageSide M l) s (ident l v)

variable {H M}

/-- **The stage channels satisfy the interface with uniform constants.** If the identifiers of
stage `l` are injective and below `M l`, the affine channel of stage `l` satisfies
`RetentionChannels` at rate `(2 ^ H)⁻¹ ^ l` with `c_π = 1`, `C_π = C_pair = 2 ^ H` and
`C_var = 4`. -/
theorem retentionChannels_stageChannel {V : ℕ → Type*} {ident : ∀ l, V l → ℕ}
    (hident : ∀ l, Function.Injective (ident l)) (hM : ∀ l v, ident l v < M l) (l : ℕ) :
    RetentionChannels (stageChannel H M ident l) (stageChannel H M ident l)
      (((2 : ℝ) ^ H)⁻¹ ^ l) ((((stageSide M l : ℕ) : ℝ) / stageModulus M l) ^ H) 1 (2 ^ H)
      (2 ^ H) 4 := by
  set P := stageModulus M l
  have hP : max (2 ^ l) (M l) ≤ P := le_stageModulus M l
  have hinj : Function.Injective fun v => ((ident l v : ℕ) : ZMod P) := by
    intro a b hab
    have h := congrArg ZMod.val hab
    simp only at h
    rw [ZMod.val_cast_of_lt ((hM l a).trans_le ((le_max_right _ _).trans hP)),
      ZMod.val_cast_of_lt ((hM l b).trans_le ((le_max_right _ _).trans hP))] at h
    exact hident l h
  have hPa : 1 ≤ (P : ℝ) * (2⁻¹ : ℝ) ^ l := by
    have h2 : ((2 : ℝ) ^ l) ≤ P := by exact_mod_cast (le_max_left _ _).trans hP
    calc (1 : ℝ) = 2 ^ l * (2⁻¹ : ℝ) ^ l := by rw [← mul_pow]; norm_num
      _ ≤ P * (2⁻¹ : ℝ) ^ l := mul_le_mul_of_nonneg_right h2 (by positivity)
  have h := retentionChannels_affineRetains (P := P) (H := H) hinj hPa
    (pow_le_one₀ (by norm_num) (by norm_num))
  have hrate : ((2⁻¹ : ℝ) ^ l) ^ H = ((2 : ℝ) ^ H)⁻¹ ^ l := by
    rw [← pow_mul, ← inv_pow, ← pow_mul, mul_comm]
  rw [hrate] at h
  unfold stageChannel
  rw [stageSide_eq_ceil]
  exact h

end Cslib.Probability

namespace Matrix

open Cslib.Probability

/-- **The stage bound with affine channels** [OpenAI2026LogSpace, Proposition 4.7]. Run the
hierarchy with the affine stage channels on identifiers `ident l` that are injective and below
`M l`, and with parameters for `q = 2 ^ (c + 1)` and the affine constants. Then for every
strictly upper triangular, nonnegative, substochastic `S` and `(1 - S) p = e₀` with `0 ≤ p ≤ 1`,
`0 ≤ p x - W_l (x̄_l) ≤ |V 0| (2 ^ c)⁻¹ ^ l`, with no remaining channel hypothesis. -/
theorem sub_hierarchyReward_le_affine {c : ℕ}
    (P : HierarchyParams (2 ^ (c + 1)) 1 (2 ^ (c + 1)) (2 ^ (c + 1)) 4) {V : ℕ → Type*}
    [∀ l, Fintype (V l)] [∀ l, LinearOrder (V l)] {e : ∀ l, V (l + 1) ≃ Lex (V l × Fin (P.m + 1))}
    (he : ∀ l a b, e l a < e l b → a < b) {ident : ∀ l, V l → ℕ}
    (hident : ∀ l, Function.Injective (ident l)) {M : ℕ → ℕ} (hM : ∀ l v, ident l v < M l)
    {S : Matrix (V 0) (V 0) ℝ} (hS : S.IsStrictUpperTriangular) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : S *ᵥ 1 ≤ 1) {p e₀ : V 0 → ℝ} (hp : (1 - S) *ᵥ p = e₀) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : V 0) (l : ℕ) :
    0 ≤ p x - (rewardTransport (hierarchyProj P e (stageChannel (c + 1) M ident)
        (stageChannel (c + 1) M ident) S) (hierarchyCorrection P e (stageChannel (c + 1) M ident)
          (stageChannel (c + 1) M ident) S) l *ᵥ e₀) (primaryCopy P e x l) ∧
      p x - (rewardTransport (hierarchyProj P e (stageChannel (c + 1) M ident)
        (stageChannel (c + 1) M ident) S) (hierarchyCorrection P e (stageChannel (c + 1) M ident)
          (stageChannel (c + 1) M ident) S) l *ᵥ e₀) (primaryCopy P e x l) ≤
        Fintype.card (V 0) * ((2 : ℝ) ^ c)⁻¹ ^ l :=
  sub_hierarchyReward_le he rfl (retentionChannels_stageChannel hident hM) (by positivity) hS
    hS0 hS1 hp hp0 hp1 x l

/-- **The stage bound on radix identifiers**: a fully concrete hierarchy. Stage `l` is
`Fin (n (m + 1) ^ l)` with radix identifiers, the channels are the affine stage channels on the
identifiers themselves, and the bound `0 ≤ p x - W_l (x̄_l) ≤ n (2 ^ c)⁻¹ ^ l` holds for every
strictly upper triangular, nonnegative, substochastic `S` on `Fin (n (m + 1) ^ 0)`. -/
theorem sub_hierarchyReward_le_radix {c n : ℕ}
    (P : HierarchyParams (2 ^ (c + 1)) 1 (2 ^ (c + 1)) (2 ^ (c + 1)) 4)
    {S : Matrix (Fin (n * (P.m + 1) ^ 0)) (Fin (n * (P.m + 1) ^ 0)) ℝ}
    (hS : S.IsStrictUpperTriangular) (hS0 : ∀ x y, 0 ≤ S x y) (hS1 : S *ᵥ 1 ≤ 1)
    {p e₀ : Fin (n * (P.m + 1) ^ 0) → ℝ} (hp : (1 - S) *ᵥ p = e₀) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : Fin (n * (P.m + 1) ^ 0)) (l : ℕ) :
    let X := stageChannel (c + 1) (fun l => n * (P.m + 1) ^ l)
      (V := fun l => Fin (n * (P.m + 1) ^ l)) fun _ v => v.val
    0 ≤ p x - (rewardTransport (hierarchyProj P (radixCopyEquiv n P.m) X X S)
        (hierarchyCorrection P (radixCopyEquiv n P.m) X X S) l *ᵥ e₀)
        (primaryCopy P (V := fun l => Fin (n * (P.m + 1) ^ l))
          (radixCopyEquiv n P.m) x l) ∧
      p x - (rewardTransport (hierarchyProj P (radixCopyEquiv n P.m) X X S)
        (hierarchyCorrection P (radixCopyEquiv n P.m) X X S) l *ᵥ e₀)
        (primaryCopy P (V := fun l => Fin (n * (P.m + 1) ^ l))
          (radixCopyEquiv n P.m) x l) ≤ n * ((2 : ℝ) ^ c)⁻¹ ^ l := by
  intro X
  have h := sub_hierarchyReward_le_affine P (V := fun l => Fin (n * (P.m + 1) ^ l))
    (e := radixCopyEquiv n P.m) (fun l _ _ h => radixCopyEquiv_lt n P.m l h)
    (ident := fun _ v => v.val) (fun _ => Fin.val_injective) (M := fun l => n * (P.m + 1) ^ l)
    (fun _ v => v.isLt) hS hS0 hS1 hp hp0 hp1 x l
  simpa using h

end Matrix
