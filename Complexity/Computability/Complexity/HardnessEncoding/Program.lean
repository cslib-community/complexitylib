/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.HardnessAmplification.Schedule
public import Complexity.Computability.Complexity.AffineDisperser.BinaryPolynomial
public import Complexity.Computability.Complexity.AffineDisperser.Coordinates
public import Complexity.Foundations.Data.BitString.Block
public import Complexity.Foundations.Data.BitString.Enumeration
import Mathlib.Algebra.CharP.Two
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.FieldTheory.Finite.Basic

/-!
# The worst-case-to-average-case encoding as a program on bit lists

The encoded slices `Cslib.HardnessEncoding.encodedSlice L M` of a language `L` are computed by a
program on bit lists (`Cslib.HardnessEncoding.encodedProgram`) that makes `2 ^ (M b)` queries to a
decider of `L` and otherwise only does arithmetic in the explicit binary field `Cslib.BinaryField`
of degree `w = 4 b`, in coordinates:

* the modulus is found by trial division (`Cslib.AffineDisperser.leastIrreducibleCode`), and the
  multiplication table of the power basis lists the remainders of `X ^ (u + v)`
  (`Cslib.HardnessEncoding.fieldTable`, `Cslib.HardnessEncoding.isMulTable_fieldTable`);
* sums are `Cslib.BitString.listXor`, products `Cslib.AffineDisperser.fieldMul`, and inverses the
  powers `y ^ (2 ^ w - 2)` (`Cslib.HardnessEncoding.fieldInv`);
* the Lagrange basis polynomial of a node `a` among the embedded bit strings of length `b`, at a
  point `t`, is the product of `t - a'` over the other nodes `a'`, divided by the product of
  `a - a'` (`Cslib.HardnessEncoding.lagrangeVal`);
* the low-degree extension of the truth table at a point is the sum, over the inputs `z` accepted
  by the decider, of the products over the blocks of `z` of the Lagrange basis polynomials
  (`Cslib.HardnessEncoding.ldeVal`), and the output is the parity of the bits of that value
  selected by the last `w` input bits (`Cslib.AffineDisperser.traceBit`, the parity of the
  coordinates selected by a bit list).

On every input `y`, with the length parameter `|y|`, the program computes the encoded slice of `L`
at length `|y|` (`Cslib.HardnessEncoding.encodedProgram_eq`).

## Main definitions

* `Cslib.HardnessEncoding.fieldTable`: the multiplication table of the explicit binary field.
* `Cslib.HardnessEncoding.lagrangeVal`: a Lagrange basis polynomial at a point, in coordinates.
* `Cslib.HardnessEncoding.ldeVal`: the low-degree extension of a truth table at a point.
* `Cslib.HardnessEncoding.encodedProgram`: the program.

## Main results

* `Cslib.HardnessEncoding.isMulTable_fieldTable`: the table multiplies.
* `Cslib.HardnessEncoding.fieldOfBits_ldeVal`: the program computes the low-degree extension.
* `Cslib.HardnessEncoding.encodedProgram_eq`: the program computes the encoded slices.

## References

* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
* [R. Lidl, H. Niederreiter, *Finite Fields*, Chapters 1 and 3][LidlNiederreiter1997]
-/

@[expose] public section

namespace Cslib.HardnessEncoding

open Finset Polynomial Cslib.AffineDisperser Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.BitString (bitEquiv bitEquiv_symm_false bitEquiv_symm_true listXor)

/-! ### The program -/

/-- The multiplication table of the power basis modulo the binary polynomial with coefficient
list `g`: entry `(u, v)` lists the coefficients of the remainder of `X ^ (u + v)`. -/
def powerMulTable (g : List Bool) : List (List (List Bool)) :=
  (List.range (g.length - 1)).map fun u => (List.range (g.length - 1)).map fun v =>
    (powerTable g).getD (u + v) []

/-- The coefficient list of the modulus of the explicit binary field of degree `w`. -/
def modulusBits (w : ℕ) : List Bool := (leastIrreducibleCode (2 ^ (w + 1)) w).bits

/-- The multiplication table of the explicit binary field of degree `w`. -/
def fieldTable (w : ℕ) : List (List (List Bool)) := powerMulTable (modulusBits w)

/-- The inverse in coordinates: `y ^ (2 ^ w - 2)`, as the square of `y ^ (2 ^ (w - 1) - 1)`. -/
def fieldInv (tab : List (List (List Bool))) (w : ℕ) (y : List Bool) : List Bool :=
  fieldMul tab (powerPred tab y (w - 2)) (powerPred tab y (w - 2))

/-- The product of `t + a'` over the words `a'` of `E` other than `a`, in coordinates. -/
def lagrangeNum (tab : List (List (List Bool))) (w : ℕ) (E : List (List Bool))
    (a t : List Bool) : List Bool :=
  E.foldl (fun acc a' => if a' = a then acc else fieldMul tab acc (listXor w [t, a'])) [true]

/-- **A Lagrange basis polynomial at a point, in coordinates**: the value at `t` of the Lagrange
basis polynomial of the node `a` among the nodes `E`. -/
def lagrangeVal (tab : List (List (List Bool))) (w : ℕ) (E : List (List Bool))
    (a t : List Bool) : List Bool :=
  fieldMul tab (lagrangeNum tab w E a t) (fieldInv tab w (lagrangeNum tab w E a a))

/-- The product over the blocks `i < M` of `z` of the Lagrange basis polynomial of block `i` at
the point `xs i`. -/
def termVal (tab : List (List (List Bool))) (w b M : ℕ) (E xs : List (List Bool))
    (z : List Bool) : List Bool :=
  (List.range M).foldl
    (fun acc i =>
      fieldMul tab acc (lagrangeVal tab w E (BitString.listBlock b z i) (xs.getD i []))) [true]

/-- **The low-degree extension at a point, in coordinates**: the sum of the terms of the inputs
`pts` accepted by the truth table. -/
def ldeVal (tab : List (List (List Bool))) (w b M : ℕ) (E pts xs : List (List Bool)) :
    List Bool :=
  listXor w (pts.map (termVal tab w b M E xs))

/-- **The encoding program** with block length `b`: on the input `y`, the parity of the bits,
selected by the last `w = 4 b` bits of `y`, of the low-degree extension over the binary field of
degree `w` of the truth table of `gL` on `M b` bits, at the point whose coordinates are the first
`M` blocks of `w` bits of `y`. -/
def encodedProgramAt (M : ℕ) (gL : List Bool → Bool) (y : List Bool) (b : ℕ) : Bool :=
  if b = 0 then false else
    traceBit ((y.drop (M * (4 * b))).take (4 * b))
      (ldeVal (fieldTable (4 * b)) (4 * b) b M (BitString.enumList b)
        ((BitString.enumList (M * b)).filter fun z => gL (z.take (M * b)))
        ((List.range M).map fun i => (y.drop (i * (4 * b))).take (4 * b)))

/-- **The encoding program** with length parameter `ℓ`: block length `blockLength M ℓ`. -/
def encodedProgram (M : ℕ) (gL : List Bool → Bool) (y : List Bool) (ℓ : ℕ) : Bool :=
  encodedProgramAt M gL y (blockLength M ℓ)

/-! ### The explicit binary field in coordinates -/

/-- The coefficient list of the modulus is the coefficient list of `leastIrreducible w`. -/
private theorem polyOfBits_modulusBits {w : ℕ} (hw : w ≠ 0) :
    polyOfBits (modulusBits w) = leastIrreducible w := by
  rw [modulusBits, polyOfBits_bits, polyOfCode_leastIrreducibleCode hw le_rfl]

/-- The coefficient list of the modulus has length `w + 1` and ends with a one. -/
private theorem exists_modulusBits_eq {w : ℕ} (hw : w ≠ 0) :
    ∃ l : List Bool, modulusBits w = l ++ [true] ∧ l.length = w := by
  have hne : leastIrreducibleCode (2 ^ (w + 1)) w ≠ 0 := by
    intro h
    have := polyOfCode_leastIrreducibleCode hw (le_refl (2 ^ (w + 1)))
    rw [h, polyOfCode_zero] at this
    exact (irreducible_leastIrreducible w).ne_zero this.symm
  obtain ⟨l, hl⟩ := exists_bits_eq_append_true hne
  refine ⟨l, hl, ?_⟩
  have := natDegree_polyOfBits_append_true l
  rw [← hl, ← modulusBits, polyOfBits_modulusBits hw, natDegree_leastIrreducible hw] at this
  exact this.symm

/-- The basis of the explicit binary field used by the program. -/
local notation "𝔅" => BinaryField.basis

/-- **The table multiplies**: `fieldTable w` is a multiplication table of the power basis of the
explicit binary field of degree `w`. -/
theorem isMulTable_fieldTable {w : ℕ} (hw : w ≠ 0) : IsMulTable (𝔅 hw) (fieldTable w) := by
  obtain ⟨l, hl, hlen⟩ := exists_modulusBits_eq hw
  subst hlen
  have hglen : (modulusBits l.length).length - 1 = l.length := by simp [hl]
  refine ⟨by simp [fieldTable, powerMulTable, hglen], fun u v => ?_⟩
  set α := AdjoinRoot.root (leastIrreducible l.length)
  have hα : aeval α (polyOfBits (l ++ [true])) = 0 := by
    rw [← hl, polyOfBits_modulusBits hw, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have huv : (u : ℕ) + v < 2 * l.length := by omega
  have hentry : tableEntry (fieldTable l.length) u v =
      (powerTable (l ++ [true])).getD (u + v) [] := by
    simp [tableEntry, fieldTable, powerMulTable, hglen, ← hl, List.getD_eq_getElem?_getD]
  rw [BinaryField.basis_apply, BinaryField.basis_apply, ← pow_add,
    pow_eq_sum_powerTable l hα huv, fieldOfBits, ofBits, hentry, Finset.sum_range]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [BinaryField.basis_apply]

variable {w : ℕ}

/-- The element with given coordinates in the power basis is the element with these bits. -/
private theorem fieldOfBits_basis (hw : w ≠ 0) (a : List Bool) :
    fieldOfBits (𝔅 hw) a = (BinaryField.equivBits hw).symm fun j => a.getD j false := by
  rw [fieldOfBits, ofBits, BinaryField.equivBits_symm_apply]

/-- The bits of the element with given coordinates. -/
private theorem equivBits_fieldOfBits (hw : w ≠ 0) (a : List Bool) (j : Fin w) :
    BinaryField.equivBits hw (fieldOfBits (𝔅 hw) a) j = a.getD j false := by
  rw [BinaryField.equivBits_apply, repr_fieldOfBits, RingEquiv.apply_symm_apply]

/-- The coordinates `[true]` are those of `1`. -/
private theorem fieldOfBits_one (hw : w ≠ 0) : fieldOfBits (𝔅 hw) [true] = 1 := by
  rw [fieldOfBits, ofBits, Fintype.sum_eq_single ⟨0, Nat.pos_of_ne_zero hw⟩]
  · simp [BinaryField.basis_apply, bitEquiv_symm_true]
  · intro u hu
    have : (u : ℕ) ≠ 0 := fun h => hu (Fin.ext h)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
    simp [hk, bitEquiv_symm_false]

/-- Addition in coordinates: `listXor w [a, b]` has the sum of the coordinates. -/
private theorem fieldOfBits_listXor_pair (hw : w ≠ 0) (a b : List Bool) :
    fieldOfBits (𝔅 hw) (listXor w [a, b]) = fieldOfBits (𝔅 hw) a + fieldOfBits (𝔅 hw) b := by
  rw [fieldOfBits_listXor]
  simp

/-- In a field of `2 ^ w` elements, `w ≥ 2`, the inverse is the power `2 ^ w - 2`. -/
private theorem fieldOfBits_fieldInv (hw : 2 ≤ w) (a : List Bool) :
    fieldOfBits (𝔅 (by omega : w ≠ 0)) (fieldInv (fieldTable w) w a) =
      (fieldOfBits (𝔅 (by omega : w ≠ 0)) a)⁻¹ := by
  have hw0 : w ≠ 0 := by omega
  have htab := isMulTable_fieldTable hw0
  rw [fieldInv, fieldOfBits_fieldMul htab, fieldOfBits_powerPred htab, ← pow_add,
    show w - 2 + 1 = w - 1 by omega]
  have hq : Fintype.card (BinaryField w) = 2 ^ w := BinaryField.card hw0
  have he : 2 ^ (w - 1) - 1 + (2 ^ (w - 1) - 1) = 2 ^ w - 2 := by
    have h1 : 2 ^ w = 2 * 2 ^ (w - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ w)]
    have h2 : 1 ≤ 2 ^ (w - 1) := Nat.one_le_two_pow
    omega
  rw [he]
  generalize fieldOfBits (𝔅 hw0) a = x
  rcases eq_or_ne x 0 with hx | hx
  · rw [hx, inv_zero, zero_pow]
    have : 4 ≤ 2 ^ w := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
    omega
  · rw [← hq]; exact FiniteField.pow_card_sub_two_eq_inv x hx

/-! ### Correctness -/

/-- The embedded bit string is the element with its bits as coordinates. -/
private theorem embed_eq_fieldOfBits (hw : w ≠ 0) {b : ℕ} (hbw : b ≤ w) (a : BitString b) :
    BinaryField.embed hw hbw a = fieldOfBits (𝔅 hw) (List.ofFn a) := by
  rw [BinaryField.embed_apply, fieldOfBits_basis]
  congr 1
  funext j
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> rfl

/-- The element with the bits of `v` as coordinates. -/
theorem fieldOfBits_ofFn (hw : w ≠ 0) (v : BitString w) :
    fieldOfBits (𝔅 hw) (List.ofFn v) = (BinaryField.equivBits hw).symm v := by
  simp [fieldOfBits_basis]

/-- The numerator of a Lagrange basis polynomial: the product of `t - a'` over the other nodes. -/
private theorem fieldOfBits_lagrangeNum (hw : w ≠ 0) {b : ℕ} (hbw : b ≤ w) (a : BitString b)
    (t : List Bool) :
    fieldOfBits (𝔅 hw) (lagrangeNum (fieldTable w) w (BitString.enumList b) (List.ofFn a) t) =
      ∏ a' ∈ univ.erase a, (fieldOfBits (𝔅 hw) t - BinaryField.embed hw hbw a') := by
  classical
  rw [lagrangeNum, BitString.enumList, List.foldl_map]
  simp only [List.ofFn_inj]
  rw [fieldOfBits_foldl_ite (isMulTable_fieldTable hw) (· = a), fieldOfBits_one, one_mul,
    ← List.prod_toFinset _ ((BitString.nodup_enum b).filter _)]
  have hset : ((BitString.enum b).filter fun x => !decide (x = a)).toFinset = univ.erase a := by
    ext x
    simp
  rw [hset]
  refine Finset.prod_congr rfl fun a' _ => ?_
  rw [fieldOfBits_listXor_pair, embed_eq_fieldOfBits hw hbw, CharTwo.sub_eq_add]

/-- **A Lagrange basis polynomial at a point**: `lagrangeVal` computes the value at `t` of the
Lagrange basis polynomial of the node `a` among the embedded bit strings of length `b`. -/
theorem fieldOfBits_lagrangeVal (hw : 2 ≤ w) {b : ℕ} (hbw : b ≤ w) (a : BitString b)
    (t : List Bool) :
    fieldOfBits (𝔅 (by omega : w ≠ 0))
        (lagrangeVal (fieldTable w) w (BitString.enumList b) (List.ofFn a) t) =
      (Lagrange.basis univ (BinaryField.embed (by omega : w ≠ 0) hbw) a).eval
        (fieldOfBits (𝔅 (by omega : w ≠ 0)) t) := by
  have hw0 : w ≠ 0 := by omega
  rw [lagrangeVal, fieldOfBits_fieldMul (isMulTable_fieldTable hw0), fieldOfBits_fieldInv hw,
    fieldOfBits_lagrangeNum hw0 hbw, fieldOfBits_lagrangeNum hw0 hbw,
    ← embed_eq_fieldOfBits hw0 hbw, Lagrange.basis, eval_prod, ← prod_inv_distrib,
    ← prod_mul_distrib]
  refine Finset.prod_congr rfl fun a' _ => ?_
  rw [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C, mul_comm]

/-- **A term of the extension**: `termVal` computes the product over the blocks of `z` of the
Lagrange basis polynomials at the coordinates of the point. -/
private theorem fieldOfBits_termVal (hw : 2 ≤ w) {M b : ℕ} (hbw : b ≤ w) (xs : List (List Bool))
    (z : BitString (M * b)) :
    fieldOfBits (𝔅 (by omega : w ≠ 0))
        (termVal (fieldTable w) w b M (BitString.enumList b) xs (List.ofFn z)) =
      ∏ i : Fin M, (Lagrange.basis univ (BinaryField.embed (by omega : w ≠ 0) hbw)
        (BitString.block z i)).eval (fieldOfBits (𝔅 (by omega : w ≠ 0)) (xs.getD i [])) := by
  have hw0 : w ≠ 0 := by omega
  rw [termVal, fieldOfBits_foldl_fieldMul (isMulTable_fieldTable hw0), fieldOfBits_one, one_mul,
    ← List.prod_toFinset _ List.nodup_range, List.toFinset_range, Finset.prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [BitString.listBlock_ofFn, fieldOfBits_lagrangeVal hw]

/-- **The program computes the low-degree extension**: `ldeVal` on the accepted inputs of a
decider `gL` of `L` is the extension of the truth table of `L` on `M b` bits at the point with
coordinates `xs`. -/
theorem fieldOfBits_ldeVal (hw : 2 ≤ w) {M b : ℕ} (hbw : b ≤ w) {L : Language Bool}
    {gL : List Bool → Bool} (hgL : ∀ z, z ∈ L ↔ gL z = true) (xs : List (List Bool)) :
    fieldOfBits (𝔅 (by omega : w ≠ 0)) (ldeVal (fieldTable w) w b M (BitString.enumList b)
        ((BitString.enumList (M * b)).filter fun z => gL (z.take (M * b))) xs) =
      truthTableExtension (BinaryField.embed (by omega : w ≠ 0) hbw) (L.slice (M * b))
        fun i => fieldOfBits (𝔅 (by omega : w ≠ 0)) (xs.getD i []) := by
  classical
  have hw0 : w ≠ 0 := by omega
  set e := BinaryField.embed hw0 hbw
  set x : Fin M → BinaryField w := fun i => fieldOfBits (𝔅 hw0) (xs.getD i [])
  rw [ldeVal, fieldOfBits_listXor, List.map_map,
    show BitString.enumList (M * b) = (BitString.enum (M * b)).map List.ofFn from rfl,
    List.filter_map, List.map_map]
  have hfilter : ((fun z : List Bool => gL (z.take (M * b))) ∘ List.ofFn) =
      fun z : BitString (M * b) => gL (List.ofFn z) := by
    funext z
    rw [Function.comp_apply, List.take_of_length_le (by simp)]
  rw [hfilter, ← List.sum_toFinset _ ((BitString.nodup_enum _).filter _)]
  simp only [Function.comp_apply, fieldOfBits_termVal hw hbw]
  rw [truthTableExtension, Code.lowDegreeExtension]
  rw [← Equiv.sum_comp BitString.blocksEquiv]
  simp only [Equiv.symm_apply_apply]
  simp only [BitString.blocksEquiv_apply, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun z _ => rfl
  ext z
  simp [Language.slice_eq_true_iff, hgL]

/-- The coordinates of block `i` of the input are its bits: the program reads the point of the
encoding. -/
private theorem fieldOfBits_drop_take (hw : w ≠ 0) {M : ℕ} {y : List Bool}
    {Y : BitString (M * w + w)}
    (hY : ∀ k, Y k = y.getD k false) (i : Fin M) :
    fieldOfBits (𝔅 hw) ((y.drop (i * w)).take w) =
      (BitString.pointEquiv (BinaryField.equivBits hw).toEquiv).symm
        (fun k => Y (Fin.castAdd w k)) i := by
  rw [fieldOfBits_basis, BitString.pointEquiv_symm_apply]
  apply congrArg (BinaryField.equivBits hw).symm
  funext j
  rw [BitString.block_apply, hY, Fin.val_castAdd, finProdFinEquiv_apply_val,
    List.getD_take_drop y (i * w) j.2 false]
  congr 1
  ring

/-- The last `w` bits of the input, as a list. -/
private theorem drop_take_eq_ofFn {M : ℕ} {y : List Bool} {Y : BitString (M * w + w)}
    (hY : ∀ k, Y k = y.getD k false) (hle : M * w + w ≤ y.length) :
    (y.drop (M * w)).take w = List.ofFn fun j => Y (Fin.natAdd (M * w) j) := by
  refine List.ext_getElem (by
    simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega) fun j h₁ h₂ => ?_
  rw [List.getElem_take, List.getElem_drop, List.getElem_ofFn, hY, Fin.val_natAdd,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_ofFn] at h₂; omega)]
  rfl

/-- The parity selected by the last `w` bits is the dot product of the bits of the field element
with them. -/
private theorem traceBit_eq (hw : w ≠ 0) {a : List Bool} (ha : a.length = w) (r : BitString w) :
    traceBit (List.ofFn r) a = BinaryField.equivBits hw (fieldOfBits (𝔅 hw) a) ⬝ᵥ r := by
  rw [BitString.dotProduct_eq_foldl, traceBit]
  congr 1
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp only [List.length_map, List.length_range, List.length_ofFn] at h₁
  rw [List.getElem_map, List.getElem_range, List.getElem_zipWith, List.getElem_ofFn,
    List.getElem_ofFn, equivBits_fieldOfBits, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem (by simpa using h₁)]
  simp only [Option.getD_some, List.getElem_ofFn]

/-- **The program computes the encoded slices**: on every input `y`, with a decider `gL` of `L`
and the length parameter `|y|`, the program returns the encoded slice of `L` at length `|y|`. -/
theorem encodedProgram_eq {L : Language Bool} {gL : List Bool → Bool}
    (hgL : ∀ z, z ∈ L ↔ gL z = true) (M : ℕ) (y : List Bool) :
    encodedProgram M gL y y.length = encodedSlice L M y.length fun i => y[i] := by
  rw [encodedProgram, encodedProgramAt, encodedSlice]
  by_cases hb : blockLength M y.length = 0
  · rw [ite_eq_left hb, dite_eq_left hb]
  rw [ite_eq_right hb, dite_eq_right hb]
  have hw : 2 ≤ 4 * blockLength M y.length := by omega
  have hw0 : 4 * blockLength M y.length ≠ 0 := by omega
  have hle := encodedLength_le M y.length
  have hY : ∀ k, (fun i : Fin y.length => y[i]) (Fin.castLE hle k) = y.getD k false := fun k => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by have := k.2; omega)]
    rfl
  have hlen : (ldeVal (fieldTable (4 * blockLength M y.length)) (4 * blockLength M y.length)
      (blockLength M y.length) M (BitString.enumList (blockLength M y.length))
      ((BitString.enumList (M * blockLength M y.length)).filter
        fun z => gL (z.take (M * blockLength M y.length)))
      ((List.range M).map fun i =>
        (y.drop (i * (4 * blockLength M y.length))).take (4 * blockLength M y.length))).length =
      4 * blockLength M y.length := by
    rw [ldeVal, BitString.length_listXor]
  rw [hardnessEncode, drop_take_eq_ofFn hY hle, traceBit_eq hw0 hlen,
    fieldOfBits_ldeVal hw (by omega) hgL]
  apply congrArg (· ⬝ᵥ _)
  apply congrArg (BinaryField.equivBits hw0)
  apply congrArg (truthTableExtension _ _)
  funext i
  rw [List.getD_map_range _ [] i.2, fieldOfBits_drop_take hw0 hY]

end Cslib.HardnessEncoding
