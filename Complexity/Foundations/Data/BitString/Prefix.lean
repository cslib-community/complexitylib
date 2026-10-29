/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.BitString.Basic

/-!
# Bit-prefix projection of bit strings as an additive homomorphism

When `M ≤ q`, taking the first `M` bits of a `q`-bit word `v : BitString q` agrees with
`Cslib.BitString.zeroExtend (d' := M) v`, forms a surjective additive group homomorphism
`Cslib.BitString.restrictBitsAddHom hM : BitString q →+ BitString M`, and reduces the unsigned
integer value `Cslib.BitString.equivFin q v` modulo `2 ^ M`
(`Cslib.BitString.val_equivFin_restrictBitsAddHom`).

Placing these declarations in a dedicated topic module avoids expanding the public interface of the
widely imported `Complexity/Foundations/Data/BitString/Basic.lean`.

## Main definitions

* `Cslib.BitString.restrictBitsAddHom`: projecting `BitString q` to its first `M ≤ q` bits as an
  additive group homomorphism `BitString q →+ BitString M`.

## Main results

* `Cslib.BitString.restrictBitsAddHom_eq_zeroExtend`: `restrictBitsAddHom hM v` agrees with
  `zeroExtend (d' := M) v`.
* `Cslib.BitString.restrictBitsAddHom_zeroExtend`, `Cslib.BitString.restrictBitsAddHom_surjective`:
  `zeroExtend` is a right inverse to `restrictBitsAddHom hM`, which is therefore surjective.
* `Cslib.BitString.val_equivFin_restrictBitsAddHom`: the unsigned value of `restrictBitsAddHom hM v`
  is `(equivFin q v).val % 2 ^ M`.
-/

public section

namespace Cslib.BitString

/-- Projecting a `q`-bit string to its first `M ≤ q` bits as an additive group homomorphism. -/
@[expose] def restrictBitsAddHom {q M : ℕ} (hM : M ≤ q) : BitString q →+ BitString M where
  toFun v j := v (Fin.castLE hM j)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- When `M ≤ q`, `restrictBitsAddHom hM v` agrees pointwise with `zeroExtend (d' := M) v`. -/
theorem restrictBitsAddHom_eq_zeroExtend {q M : ℕ} (hM : M ≤ q) (v : BitString q) :
    restrictBitsAddHom hM v = zeroExtend (d' := M) v := by
  funext j
  have hj : j.val < q := lt_of_lt_of_le j.isLt hM
  simp [restrictBitsAddHom, zeroExtend, hj, Fin.castLE]

/-- Zero-extending an `M`-bit string to `q ≥ M` bits is a right inverse to
`restrictBitsAddHom hM`. -/
@[simp]
theorem restrictBitsAddHom_zeroExtend {q M : ℕ} (hM : M ≤ q) (w : BitString M) :
    restrictBitsAddHom hM (zeroExtend w) = w := by
  ext j
  simp [restrictBitsAddHom, zeroExtend, j.isLt]

/-- `restrictBitsAddHom hM` is surjective whenever `M ≤ q`. -/
theorem restrictBitsAddHom_surjective {q M : ℕ} (hM : M ≤ q) :
    Function.Surjective (restrictBitsAddHom hM) :=
  fun w => ⟨zeroExtend w, restrictBitsAddHom_zeroExtend hM w⟩

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
    (equivFin M (restrictBitsAddHom hM v)).val = (equivFin q v).val % 2 ^ M := by
  induction M generalizing q with
  | zero =>
    have hlt := (equivFin 0 (restrictBitsAddHom hM v)).isLt
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
      rw [hcons, val_equivFin_cons, val_equivFin_cons, ih hM' (Fin.tail v)]
      have hb : (v 0).toNat < 2 := by cases v 0 <;> decide
      exact (add_two_mul_mod_two_pow_succ hb _ M).symm

/-- Taking the `M`-bit prefix of `v : BitString q` via `zeroExtend` when `M ≤ q` reduces its
unsigned integer value modulo `2 ^ M`. -/
theorem val_equivFin_zeroExtend_of_le {q M : ℕ} (hM : M ≤ q) (v : BitString q) :
    (equivFin M (zeroExtend v)).val = (equivFin q v).val % 2 ^ M := by
  rw [← restrictBitsAddHom_eq_zeroExtend hM v, val_equivFin_restrictBitsAddHom hM v]

end Cslib.BitString
