/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.DetectedHierarchy
public import Complexity.Probability.PairwiseIndependentHash.DetectorChannels
import Mathlib.Data.Nat.Prime.Infinite

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
and all step cutoffs remain separate requirements. The prime at each stage is chosen
noncomputably; no prime-size or machine-resource bound is supplied.

## Main definitions

* `Cslib.Probability.stageModulus`, `Cslib.Probability.stageChannel`: the affine channel of stage
  `l` on identifiers below `M l`.

## Main results

* `Cslib.Probability.retentionChannels_stageChannel`: the channel interface at rate
  `(2 ^ H)⁻¹ ^ l` with uniform constants.
* `Matrix.sub_hierarchyReward_le_affine`: the stage bound with these channels.
* `Matrix.sub_hierarchyReward_le_radix`: the stage bound on radix identifiers.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 2–3, Section 4.5 and Proposition 4.7 (preprint, not peer reviewed)
-/

public section

open Finset

namespace Cslib.Probability

/-- A prime at least `n` (Euclid). -/
private noncomputable def primeAtLeast (n : ℕ) : ℕ :=
  Classical.choose (Nat.exists_infinite_primes n)

private theorem le_primeAtLeast (n : ℕ) : n ≤ primeAtLeast n :=
  (Classical.choose_spec (Nat.exists_infinite_primes n)).1

private theorem primeAtLeast_prime (n : ℕ) : (primeAtLeast n).Prime :=
  (Classical.choose_spec (Nat.exists_infinite_primes n)).2

private instance (n : ℕ) : Fact (primeAtLeast n).Prime := ⟨primeAtLeast_prime n⟩

variable (H : ℕ) (M : ℕ → ℕ)

/-- The prime modulus of stage `l`: at least `2 ^ l` and at least the identifier bound `M l`. -/
noncomputable def stageModulus (l : ℕ) : ℕ := primeAtLeast (max (2 ^ l) (M l))

/-- The stage modulus is prime, so its finite-field and seed instances are available to
importers. -/
instance (l : ℕ) : Fact (stageModulus M l).Prime := ⟨primeAtLeast_prime _⟩

/-- The side `⌈P_l 2^(-l)⌉` of the retention box of stage `l`. -/
noncomputable abbrev stageSide (l : ℕ) : ℕ := ⌈(stageModulus M l : ℝ) * (2⁻¹ : ℝ) ^ l⌉₊

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
  have hP : max (2 ^ l) (M l) ≤ P := le_primeAtLeast _
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
