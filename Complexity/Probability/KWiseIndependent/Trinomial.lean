/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Foundations.FieldTheory.Finite.Trinomial
public import Complexity.Probability.KWiseIndependent.Polynomial

/-!
# Exact `k`-wise independent hashing over explicit trinomial binary fields

By evaluating degree-`< k` polynomials over the explicit binary field
`Cslib.TrinomialField t = AdjoinRoot (X ^ (2 * 3 ^ t) + X ^ (3 ^ t) + 1)` and projecting the result
to its low `M ≤ 2 * 3 ^ t` coordinates in the power basis, we obtain an explicit, zero-bias
`k`-wise independent hash family (`Cslib.Probability.trinomialPolyHash`) from `Fin U` onto
`Fin (2 ^ M)` whenever `U ≤ 2 ^ (2 * 3 ^ t)` and `M ≤ 2 * 3 ^ t`
(`Cslib.Probability.isKWiseIndependentHash_trinomialPolyHash`)
[Vadhan, Section 3.5.5][Vadhan2012]; [Wegman and Carter][WegmanCarter1981].

Because the coordinate map
`Cslib.TrinomialField.equivBits t : TrinomialField t ≃+ BitString (2 * 3 ^ t)`
and the bit-prefix projection `BitString (2 * 3 ^ t) →+ BitString M` are surjective additive group
homomorphisms over `𝔽₂`, every output bucket in `Fin (2 ^ M)` has the exact same preimage size in
`TrinomialField t`. Consequently, projecting to the low `M` bits preserves exact `k`-wise
independence without modulo bias.

We also provide `Cslib.Probability.trinomialStep U M`, which selects a trinomial parameter `t`
satisfying `U ≤ 2 ^ (2 * 3 ^ t)`, `M ≤ 2 * 3 ^ t`, and
`2 * 3 ^ t ≤ 3 * max (Nat.clog 2 (max U 2)) (max M 1)`.

## Main definitions

* `Cslib.Probability.trinomialStep`: selects `t : ℕ` so that `2 * 3 ^ t` covers both `log₂ U` and
  `M` within a factor of `3`.
* `Cslib.Probability.trinomialDeg`: the field degree `2 * 3 ^ trinomialStep U M`.
* `Cslib.Probability.trinomialPolyEval`: degree-`< k` polynomial evaluation over
  `Cslib.TrinomialField t` on natural-number word coordinates.
* `Cslib.Probability.trinomialPolyHash`: the `k`-wise independent trinomial polynomial hash family
  from `Fin U` to `Fin (2 ^ M)`.

## Main results

* `Cslib.Probability.isKWiseIndependentHash_trinomialPolyHash`: `trinomialPolyHash t k U M` is
  `k`-wise independent whenever `U ≤ 2 ^ (2 * 3 ^ t)` and `M ≤ 2 * 3 ^ t`.
* `Cslib.Probability.le_two_pow_trinomialDeg`, `Cslib.Probability.le_trinomialDeg`,
  `Cslib.Probability.trinomialDeg_le`: degree bounds for `trinomialStep U M`.

## References

* [S. P. Vadhan, *Pseudorandomness*, Section 3.5.5][Vadhan2012]
* [M. N. Wegman, J. L. Carter, *New hash functions and their use in authentication and set
  equality*][WegmanCarter1981]
-/

public section

namespace Cslib.Probability

open BitString Finset

/-! ## Trinomial degree selection -/

/-- Smallest exponent `t : ℕ` such that `B ≤ 2 * 3 ^ t`. -/
@[expose] def trinomialStepAux (B : ℕ) : ℕ :=
  if B ≤ 2 then 0
  else trinomialStepAux ((B + 2) / 3) + 1
decreasing_by omega

/-- `2 * 3 ^ trinomialStepAux B` is at least `B`. -/
theorem le_two_mul_three_pow_trinomialStepAux (B : ℕ) :
    B ≤ 2 * 3 ^ trinomialStepAux B := by
  induction B using Nat.strong_induction_on with
  | _ B ih =>
    rw [trinomialStepAux]
    split_ifs with hB
    · simp [hB]
    · have hrec := ih ((B + 2) / 3) (by omega)
      rw [pow_succ, ← mul_assoc]
      omega

/-- When `2 < B`, `trinomialStepAux B` is positive and `2 * 3 ^ (trinomialStepAux B - 1) < B`. -/
private theorem two_mul_three_pow_pred_lt_of_two_lt {B : ℕ} (hB : 2 < B) :
    0 < trinomialStepAux B ∧ 2 * 3 ^ (trinomialStepAux B - 1) < B := by
  induction B using Nat.strong_induction_on with
  | _ B ih =>
    have hle : ¬ B ≤ 2 := not_le.mpr hB
    rw [trinomialStepAux, ite_eq_right hle]
    refine ⟨Nat.succ_pos _, ?_⟩
    rw [Nat.add_sub_cancel]
    by_cases hB' : (B + 2) / 3 ≤ 2
    · have h0 : trinomialStepAux ((B + 2) / 3) = 0 := by
        rw [trinomialStepAux, ite_eq_left hB']
      rw [h0]
      omega
    · obtain ⟨ht', hlt'⟩ := ih ((B + 2) / 3) (by omega) (not_le.mp hB')
      have hpow : 3 ^ trinomialStepAux ((B + 2) / 3) =
          3 ^ (trinomialStepAux ((B + 2) / 3) - 1) * 3 := by
        conv_lhs => rw [← Nat.sub_add_cancel ht', pow_succ]
      omega

/-- `2 * 3 ^ trinomialStepAux B` is at most `3 * max B 1`. -/
theorem two_mul_three_pow_trinomialStepAux_le (B : ℕ) :
    2 * 3 ^ trinomialStepAux B ≤ 3 * max B 1 := by
  by_cases hB : B ≤ 2
  · rw [trinomialStepAux, ite_eq_left hB]
    omega
  · obtain ⟨ht, hlt⟩ := two_mul_three_pow_pred_lt_of_two_lt (not_le.mp hB)
    have hpow : 3 ^ trinomialStepAux B = 3 ^ (trinomialStepAux B - 1) * 3 := by
      conv_lhs => rw [← Nat.sub_add_cancel ht, pow_succ]
    omega

/-- Target bit-width needed to embed `Fin U` and project to `M` bits. -/
@[expose] def trinomialTargetBits (U M : ℕ) : ℕ :=
  max (Nat.clog 2 (max U 2)) (max M 1)

/-- Selected trinomial parameter `t` for universe size `U` and output bit-length `M`. -/
@[expose] def trinomialStep (U M : ℕ) : ℕ :=
  trinomialStepAux (trinomialTargetBits U M)

/-- Selected trinomial field degree `2 * 3 ^ trinomialStep U M`. -/
@[expose] def trinomialDeg (U M : ℕ) : ℕ :=
  2 * 3 ^ trinomialStep U M

/-- The selected trinomial degree is at least `trinomialTargetBits U M`. -/
theorem trinomialTargetBits_le_trinomialDeg (U M : ℕ) :
    trinomialTargetBits U M ≤ trinomialDeg U M :=
  le_two_mul_three_pow_trinomialStepAux (trinomialTargetBits U M)

/-- The universe size `U` fits inside `2 ^ trinomialDeg U M`. -/
theorem le_two_pow_trinomialDeg (U M : ℕ) :
    U ≤ 2 ^ trinomialDeg U M := by
  have hclog : Nat.clog 2 (max U 2) ≤ trinomialDeg U M :=
    (le_max_left _ _).trans (trinomialTargetBits_le_trinomialDeg U M)
  calc U ≤ max U 2 := le_max_left U 2
    _ ≤ 2 ^ Nat.clog 2 (max U 2) := Nat.le_pow_clog one_lt_two (max U 2)
    _ ≤ 2 ^ trinomialDeg U M := Nat.pow_le_pow_right two_pos hclog

/-- The output bit-length `M` is at most `trinomialDeg U M`. -/
theorem le_trinomialDeg (U M : ℕ) :
    M ≤ trinomialDeg U M :=
  ((le_max_left M 1).trans (le_max_right _ _)).trans (trinomialTargetBits_le_trinomialDeg U M)

/-- The selected trinomial degree is within a factor of `3` of `trinomialTargetBits U M`. -/
theorem trinomialDeg_le_three_mul (U M : ℕ) :
    trinomialDeg U M ≤ 3 * max (Nat.clog 2 (max U 2)) (max M 1) := by
  have h1 : 1 ≤ trinomialTargetBits U M :=
    (le_max_right M 1).trans (le_max_right _ _)
  have hle := two_mul_three_pow_trinomialStepAux_le (trinomialTargetBits U M)
  rwa [max_eq_left h1] at hle

/-- The selected trinomial degree is at most `6 * max (Nat.clog 2 (max U 2)) (max M 1)`. -/
theorem trinomialDeg_le (U M : ℕ) :
    trinomialDeg U M ≤ 6 * max (Nat.clog 2 (max U 2)) (max M 1) := by
  have h := trinomialDeg_le_three_mul U M
  omega

/-! ## Bit-prefix projection of `BitString` -/

/-- Projecting a `q`-bit string to its first `M ≤ q` bits as an additive group homomorphism. -/
@[expose] def restrictBitsAddHom {q M : ℕ} (hM : M ≤ q) : BitString q →+ BitString M where
  toFun v j := v (Fin.castLE hM j)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Zero-extending an `M`-bit string to `q ≥ M` bits is a right inverse to
`restrictBitsAddHom hM`. -/
theorem restrictBitsAddHom_zeroExtend {q M : ℕ} (hM : M ≤ q) (w : BitString M) :
    restrictBitsAddHom hM (BitString.zeroExtend w) = w := by
  ext j
  simp [restrictBitsAddHom, BitString.zeroExtend, j.isLt]

/-- `restrictBitsAddHom hM` is surjective whenever `M ≤ q`. -/
theorem restrictBitsAddHom_surjective {q M : ℕ} (hM : M ≤ q) :
    Function.Surjective (restrictBitsAddHom hM) :=
  fun w => ⟨BitString.zeroExtend w, restrictBitsAddHom_zeroExtend hM w⟩

/-- Helper: `(b + 2 * x) % 2 ^ (M + 1) = b + 2 * (x % 2 ^ M)` for `b < 2`. -/
private theorem add_two_mul_mod_two_pow_succ {b : ℕ} (hb : b < 2) (x M : ℕ) :
    (b + 2 * x) % 2 ^ (M + 1) = b + 2 * (x % 2 ^ M) := by
  have hdiv : (b + 2 * x) / 2 ^ (M + 1) = x / 2 ^ M := by
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    have h1 : (b + 2 * x) / 2 = x := by omega
    rw [h1]
  have hmul : 2 ^ (M + 1) * (x / 2 ^ M) = 2 * (2 ^ M * (x / 2 ^ M)) := by
    rw [pow_succ', mul_assoc]
  have hmod1 := Nat.div_add_mod (b + 2 * x) (2 ^ (M + 1))
  have hmod2 := Nat.div_add_mod x (2 ^ M)
  rw [hdiv, hmul] at hmod1
  omega

/-- Taking the first `M ≤ q` bits of `v : BitString q` corresponds to taking its unsigned integer
value modulo `2 ^ M`. -/
theorem val_equivFin_restrictBitsAddHom {q M : ℕ} (hM : M ≤ q) (v : BitString q) :
    (BitString.equivFin M (restrictBitsAddHom hM v)).val =
      (BitString.equivFin q v).val % 2 ^ M := by
  induction M generalizing q with
  | zero =>
    have hlt := (BitString.equivFin 0 (restrictBitsAddHom hM v)).isLt
    omega
  | succ M ih =>
    cases q with
    | zero => omega
    | succ q =>
      have hM' : M ≤ q := Nat.le_of_succ_le_succ hM
      have hcons : restrictBitsAddHom hM v =
          Fin.cons (v 0) (restrictBitsAddHom hM' (Fin.tail v)) := by
        ext j
        refine Fin.cases ?_ ?_ j
        · rfl
        · intro i
          rfl
      conv_rhs => rw [← Fin.cons_self_tail v]
      rw [hcons, BitString.val_equivFin_cons, BitString.val_equivFin_cons, ih hM' (Fin.tail v)]
      have hb : (v 0).toNat < 2 := by cases v 0 <;> decide
      exact (add_two_mul_mod_two_pow_succ hb _ M).symm

/-! ## Trinomial polynomial hashing -/

/-- Evaluate the degree-`< k` polynomial with seed coefficients `c : Fin k → Fin (2 ^ (2 * 3 ^ t))`
over `TrinomialField t` at the key `u : Fin U`, returning the `2 * 3 ^ t`-bit result as an element
of `Fin (2 ^ (2 * 3 ^ t))`. -/
@[expose] noncomputable def trinomialPolyEval (t k U : ℕ)
    (c : Fin k → Fin (2 ^ (2 * 3 ^ t))) (u : Fin U) : Fin (2 ^ (2 * 3 ^ t)) :=
  TrinomialField.equivFin t
    (polynomialHash (fun j => (TrinomialField.equivFin t).symm (c j))
      (AdjoinRoot.mk (trinomial t) (polyOfCode u.val)))

/-- **The `k`-wise independent trinomial polynomial hash family** from `Fin U` to `Fin (2 ^ M)`:
evaluates a degree-`< k` polynomial over `TrinomialField t` and projects to the low `M` bits. -/
@[expose] noncomputable def trinomialPolyHash (t k U M : ℕ)
    (c : Fin k → Fin (2 ^ (2 * 3 ^ t))) (u : Fin U) : Fin (2 ^ M) :=
  ⟨(trinomialPolyEval t k U c u).val % 2 ^ M, Nat.mod_lt _ (by positivity)⟩

/-- The numeric output of `trinomialPolyHash` is the bitwise mask `&&& (2 ^ M - 1)` of
`trinomialPolyEval`. -/
theorem val_trinomialPolyHash (t k U M : ℕ)
    (c : Fin k → Fin (2 ^ (2 * 3 ^ t))) (u : Fin U) :
    (trinomialPolyHash t k U M c u).val =
      (trinomialPolyEval t k U c u).val &&& (2 ^ M - 1) := by
  simp [trinomialPolyHash, Nat.and_two_pow_sub_one_eq_mod]

/-- When `M ≤ 2 * 3 ^ t`, `trinomialPolyHash` agrees with projecting the power-basis bits of the
field polynomial evaluation to the first `M` bits. -/
theorem trinomialPolyHash_eq_equivFin_restrictBits {t k U M : ℕ} (hM : M ≤ 2 * 3 ^ t)
    (c : Fin k → Fin (2 ^ (2 * 3 ^ t))) (u : Fin U) :
    trinomialPolyHash t k U M c u =
      BitString.equivFin M (restrictBitsAddHom hM (TrinomialField.equivBits t
        (polynomialHash (fun j => (TrinomialField.equivFin t).symm (c j))
          (AdjoinRoot.mk (trinomial t) (polyOfCode u.val))))) := by
  apply Fin.ext
  rw [val_equivFin_restrictBitsAddHom hM]
  rfl

/-- **`trinomialPolyHash t k U M` is an exact `k`-wise independent hash family** onto `Fin (2 ^ M)`
whenever `U ≤ 2 ^ (2 * 3 ^ t)` and `M ≤ 2 * 3 ^ t`. -/
theorem isKWiseIndependentHash_trinomialPolyHash {t k U M : ℕ}
    (hU : U ≤ 2 ^ (2 * 3 ^ t)) (hM : M ≤ 2 * 3 ^ t) :
    IsKWiseIndependentHash k (trinomialPolyHash t k U M) := by
  have hpoly : IsKWiseIndependentHash k
      (polynomialHash : (Fin k → TrinomialField t) → TrinomialField t → TrinomialField t) :=
    isKWiseIndependentHash_polynomialHash k
  have hseed := hpoly.reindex_equiv
    (Equiv.piCongrRight fun _ : Fin k => (TrinomialField.equivFin t).symm)
  have hkey := hseed.comp_injective (TrinomialField.embedFin hU).injective
  let proj : TrinomialField t →+ BitString M :=
    (restrictBitsAddHom hM).comp (TrinomialField.equivBits t).toAddMonoidHom
  have hproj_surj : Function.Surjective proj :=
    (restrictBitsAddHom_surjective hM).comp (TrinomialField.equivBits t).surjective
  have hbits := (hkey.comp_surjective_addMonoidHom proj hproj_surj).map_equiv (BitString.equivFin M)
  have heq : trinomialPolyHash t k U M = fun c u =>
      BitString.equivFin M (proj
        (polynomialHash (fun j => (TrinomialField.equivFin t).symm (c j))
          (TrinomialField.embedFin hU u))) := by
    funext c u
    rw [trinomialPolyHash_eq_equivFin_restrictBits hM, TrinomialField.embedFin_apply hU]
    rfl
  rwa [heq]

end Cslib.Probability
