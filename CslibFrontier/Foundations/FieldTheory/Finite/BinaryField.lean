/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.ZModTwo
public import Cslib.Foundations.Data.BitString
public import Mathlib.RingTheory.AdjoinRoot
import CslibFrontier.Foundations.Data.BitString.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Explicit binary fields of every degree

A binary polynomial is coded by the natural number whose binary digits, least significant first,
are its coefficients (`Cslib.polyOfCode`). The irreducible polynomial of degree `w` with the least
code (`Cslib.leastIrreducible`) is found by exhaustive search through the `2 ^ w` codes in
`[2 ^ w, 2 ^ (w + 1))` (`Cslib.exists_code_leastIrreducible`).

`Cslib.BinaryField w` is the field `𝔽₂[X] / (g)` for `g = Cslib.leastIrreducible w`. For `w ≠ 0`
its power basis `1, α, …, α ^ (w - 1)` at the root `α` of `g` (`Cslib.BinaryField.basis`) encodes
its elements by `w` bits via an additive equivalence (`Cslib.BinaryField.equivBits`), so it has
`2 ^ w` elements (`Cslib.BinaryField.card`); the class of a binary polynomial of degree less than
`w` is encoded by its coefficients (`Cslib.BinaryField.equivBits_mk`). Bit strings of length
`b ≤ w` embed as the polynomials of degree less than `b` (`Cslib.BinaryField.embed`).

The modulus is explicit: its code is the least code of an irreducible binary polynomial of degree
`w`, which is computed by trial division (`Cslib.AffineDisperser.leastIrreducibleCode`), so the
field arithmetic is a computation on bit strings. This is why the field is the quotient
`AdjoinRoot g` rather than Mathlib's `GaloisField 2 w`: the splitting field of `X ^ (2 ^ w) - X`
comes with no basis. In `AdjoinRoot g` the power basis is the coefficient list itself, for every
degree `w`.

For `w = 0` the modulus is `X` and the field has two elements; the basis and the encoding by bits
need `w ≠ 0`.

## Main definitions

* `Cslib.polyOfCode`: the binary polynomial with a given code.
* `Cslib.leastIrreducible`: the irreducible binary polynomial of degree `w` with the least code
  (`X` when `w = 0`).
* `Cslib.BinaryField`: the explicit binary field of degree `w`.
* `Cslib.BinaryField.basis`: its power basis over `𝔽₂`.
* `Cslib.BinaryField.equivBits`: its additive equivalence with `BitString w`.
* `Cslib.BinaryField.embed`: the embedding of bit strings of length `b ≤ w`.

## Main results

* `Cslib.monic_of_ne_zero`: every nonzero binary polynomial is monic.
* `Cslib.irreducible_leastIrreducible`, `Cslib.monic_leastIrreducible`,
  `Cslib.natDegree_leastIrreducible`: `leastIrreducible w` is monic and irreducible, of degree `w`
  when `w ≠ 0`.
* `Cslib.exists_code_leastIrreducible`: the code of `leastIrreducible p` lies in
  `[2 ^ p, 2 ^ (p + 1))`, and no smaller code is irreducible of degree `p`.
* `Cslib.BinaryField.card`: the field has `2 ^ w` elements.
* `Cslib.BinaryField.equivBits_mk`: the encoding of a polynomial of degree less than `w` is its list
  of coefficients.

## References

* [R. Lidl, H. Niederreiter, *Finite Fields*, Chapters 1 and 3][LidlNiederreiter1997]
-/

@[expose] public section

namespace Cslib

open BitString Module Polynomial

/-- The binary polynomial whose coefficients, from the constant term up, are the binary digits of
`m`, least significant first. -/
noncomputable def polyOfCode (m : ℕ) : (ZMod 2)[X] :=
  if m = 0 then 0 else C (m : ZMod 2) + X * polyOfCode (m / 2)
decreasing_by omega

/-- The code `0` gives the zero polynomial. -/
@[simp]
theorem polyOfCode_zero : polyOfCode 0 = 0 := by
  rw [polyOfCode, ite_eq_left rfl]

/-- Appending the bit `b` below the code `m` multiplies by `X` and adds the constant `b`. -/
theorem polyOfCode_two_mul_add (m : ℕ) (b : ZMod 2) :
    polyOfCode (2 * m + b.val) = C b + X * polyOfCode m := by
  have hb : b.val < 2 := ZMod.val_lt b
  rcases Nat.eq_zero_or_pos (2 * m + b.val) with h | h
  · have hm : m = 0 := by omega
    have hb0 : b = 0 := (ZMod.val_eq_zero b).1 (by omega)
    subst hm hb0
    simp [polyOfCode_zero]
  · rw [polyOfCode, ite_eq_right h.ne', show (2 * m + b.val) / 2 = m by omega]
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add, ZMod.natCast_zmod_val]

/-- The code `m ≠ 0` gives a nonzero polynomial of degree `⌊log₂ m⌋`. -/
theorem polyOfCode_ne_zero_and_natDegree {m : ℕ} (hm : m ≠ 0) :
    polyOfCode m ≠ 0 ∧ (polyOfCode m).natDegree = Nat.log 2 m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases lt_or_ge m 2 with h | h
    · obtain rfl : m = 1 := by omega
      have h1 : polyOfCode 1 = 1 := by
        simpa [polyOfCode_zero, ZMod.val_one] using polyOfCode_two_mul_add 0 1
      rw [h1, Nat.log_one_right]
      exact ⟨one_ne_zero, natDegree_one⟩
    · obtain ⟨hne, hdeg⟩ := ih (m / 2) (by omega) (by omega)
      have heq : polyOfCode m = X * polyOfCode (m / 2) + C (m : ZMod 2) := by
        rw [polyOfCode, ite_eq_right hm, add_comm]
      have hd : (polyOfCode m).natDegree = Nat.log 2 m := by
        rw [heq, natDegree_add_C, natDegree_X_mul hne, hdeg,
          ← Nat.log_of_one_lt_of_le one_lt_two h]
      refine ⟨fun h0 => ?_, hd⟩
      rw [h0, natDegree_zero, Nat.log_of_one_lt_of_le one_lt_two h] at hd
      omega

/-- The code `m ≠ 0` gives a polynomial of degree `⌊log₂ m⌋`. -/
theorem natDegree_polyOfCode {m : ℕ} (hm : m ≠ 0) : (polyOfCode m).natDegree = Nat.log 2 m :=
  (polyOfCode_ne_zero_and_natDegree hm).2

/-- Every binary polynomial has a code. -/
theorem polyOfCode_surjective : Function.Surjective polyOfCode := by
  intro g
  induction hd : g.natDegree using Nat.strong_induction_on generalizing g with
  | _ d ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · refine ⟨(g.coeff 0).val, ?_⟩
      have := polyOfCode_two_mul_add 0 (g.coeff 0)
      rw [mul_zero, zero_add, polyOfCode_zero, mul_zero, add_zero] at this
      rw [this, ← eq_C_of_natDegree_eq_zero hd]
    · obtain ⟨m, hm⟩ := ih (d - 1) (by omega) g.divX
        (by rw [natDegree_divX_eq_natDegree_tsub_one, hd])
      refine ⟨2 * m + (g.coeff 0).val, ?_⟩
      rw [polyOfCode_two_mul_add, hm, add_comm, X_mul_divX_add]

/-- There is an irreducible binary polynomial of every positive degree `p`: the minimal polynomial
of a primitive element of `𝔽_{2 ^ p}`. -/
theorem exists_irreducible_natDegree_eq {p : ℕ} (hp : p ≠ 0) :
    ∃ g : (ZMod 2)[X], Irreducible g ∧ g.natDegree = p := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top (ZMod 2) (GaloisField 2 p)
  have hint : IsIntegral (ZMod 2) α := .of_finite _ α
  refine ⟨minpoly (ZMod 2) α, minpoly.irreducible hint, ?_⟩
  rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top',
    GaloisField.finrank 2 hp]

open Classical in
/-- The irreducible binary polynomial of degree `p` with the least code (`X` when `p = 0`, where no
irreducible polynomial exists). -/
noncomputable def leastIrreducible (p : ℕ) : (ZMod 2)[X] :=
  if h : ∃ m, Irreducible (polyOfCode m) ∧ (polyOfCode m).natDegree = p then
    polyOfCode (Nat.find h)
  else X

theorem exists_code_irreducible {p : ℕ} (hp : p ≠ 0) :
    ∃ m, Irreducible (polyOfCode m) ∧ (polyOfCode m).natDegree = p := by
  obtain ⟨g, hg, hgp⟩ := exists_irreducible_natDegree_eq hp
  obtain ⟨m, rfl⟩ := polyOfCode_surjective g
  exact ⟨m, hg, hgp⟩

open Classical in
private theorem leastIrreducible_eq {p : ℕ} (hp : p ≠ 0) :
    leastIrreducible p = polyOfCode (Nat.find (exists_code_irreducible hp)) := by
  rw [leastIrreducible, dite_eq_left (exists_code_irreducible hp)]

/-- The least irreducible binary polynomial of degree zero is `X`, by the convention of
`Cslib.leastIrreducible`. -/
theorem leastIrreducible_zero : leastIrreducible 0 = X := by
  classical
  rw [leastIrreducible, dite_eq_right]
  rintro ⟨m, hm, hdeg⟩
  rw [natDegree_eq_zero] at hdeg
  obtain ⟨c, hc⟩ := hdeg
  rw [← hc] at hm
  rcases eq_or_ne c 0 with rfl | hc0
  · exact hm.ne_zero (by simp)
  · exact hm.not_isUnit (isUnit_C.2 (Ne.isUnit hc0))

/-- `leastIrreducible w` is irreducible for every degree `w`, including `w = 0`. -/
theorem irreducible_leastIrreducible (w : ℕ) : Irreducible (leastIrreducible w) := by
  classical
  rcases eq_or_ne w 0 with rfl | hw
  · rw [leastIrreducible_zero]
    exact irreducible_X
  · rw [leastIrreducible_eq hw]
    exact (Nat.find_spec (exists_code_irreducible hw)).1

/-- For `p ≠ 0`, `leastIrreducible p` has degree `p`. -/
theorem natDegree_leastIrreducible {p : ℕ} (hp : p ≠ 0) : (leastIrreducible p).natDegree = p := by
  classical
  rw [leastIrreducible_eq hp]
  exact (Nat.find_spec (exists_code_irreducible hp)).2

/-- **The exhaustive search**: `leastIrreducible p` is `polyOfCode m` for a code
`2 ^ p ≤ m < 2 ^ (p + 1)` such that no smaller code is irreducible of degree `p`. -/
theorem exists_code_leastIrreducible {p : ℕ} (hp : p ≠ 0) :
    ∃ m, 2 ^ p ≤ m ∧ m < 2 ^ (p + 1) ∧ leastIrreducible p = polyOfCode m ∧
      ∀ m' < m, ¬ (Irreducible (polyOfCode m') ∧ (polyOfCode m').natDegree = p) := by
  classical
  have hspec := Nat.find_spec (exists_code_irreducible hp)
  set m := Nat.find (exists_code_irreducible hp)
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, polyOfCode_zero] at hspec
    exact hspec.1.ne_zero rfl
  have hlog := (natDegree_polyOfCode hm0).symm.trans hspec.2
  refine ⟨m, ?_, ?_, leastIrreducible_eq hp, fun m' hm' => Nat.find_min _ hm'⟩
  · exact hlog ▸ Nat.pow_log_le_self 2 hm0
  · exact hlog ▸ Nat.lt_pow_succ_log_self one_lt_two m

/-- Every nonzero binary polynomial is monic. -/
theorem monic_of_ne_zero {q : (ZMod 2)[X]} (hq : q ≠ 0) : q.Monic :=
  (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ (leadingCoeff_ne_zero.2 hq)

/-- `leastIrreducible w` is monic for every degree `w`, as every nonzero binary polynomial is. -/
theorem monic_leastIrreducible (w : ℕ) : (leastIrreducible w).Monic :=
  monic_of_ne_zero (irreducible_leastIrreducible w).ne_zero

/-- **The explicit binary field of degree `w`**: binary polynomials modulo the irreducible
polynomial of degree `w` with the least code. -/
abbrev BinaryField (w : ℕ) : Type := AdjoinRoot (leastIrreducible w)

namespace BinaryField

/-- The modulus is irreducible, so the quotient is a field. -/
instance (w : ℕ) : Fact (Irreducible (leastIrreducible w)) :=
  ⟨irreducible_leastIrreducible w⟩

/-- The explicit binary field is a field. -/
noncomputable instance (w : ℕ) : Field (BinaryField w) := AdjoinRoot.instField

/-- The explicit binary field is finite, through its coordinates in the power basis. -/
noncomputable instance (w : ℕ) : Fintype (BinaryField w) :=
  Fintype.ofEquiv _
    (AdjoinRoot.powerBasisAux' (monic_leastIrreducible w)).equivFun.toEquiv.symm

-- `BinaryField w` is an abbreviation, so this classical instance applies to
-- `AdjoinRoot (leastIrreducible w)`; it is only used for counting and for `Finset.filter`, and
-- the programs computing in the field compare coordinate lists instead.
/-- Equality in the explicit binary field, decided classically. -/
noncomputable instance (w : ℕ) : DecidableEq (BinaryField w) := Classical.decEq _

/-- The explicit binary field has characteristic two. -/
instance (w : ℕ) : CharP (BinaryField w) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (BinaryField w)).injective 2

/-- **The power basis** `1, α, …, α ^ (w - 1)` at the root `α` of the modulus, for `w ≠ 0`. -/
noncomputable def basis {w : ℕ} (hw : w ≠ 0) : Module.Basis (Fin w) (ZMod 2) (BinaryField w) :=
  (AdjoinRoot.powerBasisAux' (monic_leastIrreducible w)).reindex
    (finCongr (natDegree_leastIrreducible hw))

/-- The basis vector `i` is the power `α ^ i` of the root. -/
theorem basis_apply {w : ℕ} (hw : w ≠ 0) (i : Fin w) :
    basis hw i = AdjoinRoot.root (leastIrreducible w) ^ (i : ℕ) := by
  rw [basis, Module.Basis.reindex_apply]
  exact (AdjoinRoot.powerBasis' (monic_leastIrreducible w)).basis_eq_pow
    ((finCongr (natDegree_leastIrreducible hw)).symm i)

/-- **The encoding by bits**: the `w` coordinates in the power basis, for `w ≠ 0`, as an additive
equivalence `BinaryField w ≃+ BitString w`. -/
noncomputable def equivBits {w : ℕ} (hw : w ≠ 0) : BinaryField w ≃+ BitString w :=
  (basis hw).equivFun.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => bitEquiv.toAddEquiv)

/-- Bit `j` of an element is its coordinate `j` in the power basis. -/
theorem equivBits_apply {w : ℕ} (hw : w ≠ 0) (x : BinaryField w) (j : Fin w) :
    equivBits hw x j = bitEquiv ((basis hw).repr x j) :=
  rfl

/-- The element with given bits is the combination of the basis vectors selected by the bits. -/
theorem equivBits_symm_apply {w : ℕ} (hw : w ≠ 0) (v : BitString w) :
    (equivBits hw).symm v = ∑ j, bitEquiv.symm (v j) • basis hw j := by
  simp [equivBits, Module.Basis.equivFun_symm_apply]

/-- **The explicit binary field of degree `w ≠ 0` has `2 ^ w` elements.** -/
theorem card {w : ℕ} (hw : w ≠ 0) : Fintype.card (BinaryField w) = 2 ^ w := by
  rw [Fintype.card_congr (equivBits hw).toEquiv, BitString.card]

/-- The encoding of the class of a binary polynomial of degree less than `w` is its list of
coefficients. -/
theorem equivBits_mk {w : ℕ} (hw : w ≠ 0) {p : (ZMod 2)[X]} (hp : p.degree < w) (j : Fin w) :
    equivBits hw (AdjoinRoot.mk (leastIrreducible w) p) j = bitEquiv (p.coeff j) := by
  have hdeg : p.degree < (leastIrreducible w).degree := by
    rw [degree_eq_natDegree (irreducible_leastIrreducible w).ne_zero,
      natDegree_leastIrreducible hw]
    exact hp
  rw [equivBits_apply, basis, Module.Basis.repr_reindex_apply,
    AdjoinRoot.powerBasisAux'_repr_apply_to_fun, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff (monic_leastIrreducible w)).2 hdeg]
  rfl

/-- **The embedding of bit strings of length `b ≤ w`**: a bit string is the polynomial with these
coefficients, padded with zeros to length `w`. -/
noncomputable def embed {w b : ℕ} (hw : w ≠ 0) (hbw : b ≤ w) : BitString b ↪ BinaryField w where
  toFun a := (equivBits hw).symm fun j => if h : (j : ℕ) < b then a ⟨j, h⟩ else false
  inj' a a' h := by
    have := congrArg (equivBits hw) h
    simp only [AddEquiv.apply_symm_apply] at this
    funext i
    have := congrFun this ⟨i, i.2.trans_le hbw⟩
    simpa [i.2] using this

/-- The embedded bit string is the element whose bits are those of the string, padded with
zeros. -/
theorem embed_apply {w b : ℕ} (hw : w ≠ 0) (hbw : b ≤ w) (a : BitString b) :
    embed hw hbw a = (equivBits hw).symm fun j => if h : (j : ℕ) < b then a ⟨j, h⟩ else false :=
  rfl

end BinaryField

end Cslib
