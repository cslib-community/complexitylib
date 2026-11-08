/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.List.GetD

/-!
# Binary polynomials as bit lists

The executable side of the explicit binary fields. A binary polynomial is represented by its list
of coefficients, constant term first (`Cslib.AffineDisperser.polyOfBits`); the binary digits of
a code `m` are the coefficients of `polyOfCode m` (`Cslib.AffineDisperser.polyOfBits_bits`).

Reduction modulo a polynomial `g` of degree `m` uses one primitive, multiplication by `X` modulo
`g` on coefficient lists of length `m` (`Cslib.AffineDisperser.mulXMod`): shift up and add `g`
when the top coefficient overflows. The remainder of `f` is the sum of the remainders of the powers
`X ^ j` with `f j = 1` (`Cslib.AffineDisperser.modBits`), so `g ∣ f` exactly when that sum vanishes
(`Cslib.AffineDisperser.modBits_all_false_iff`). Trial division by the polynomials of degree at
most half the degree decides irreducibility (`Cslib.AffineDisperser.isIrreducibleCode_iff`), and
an exhaustive search over codes finds the irreducible polynomial of least code
(`Cslib.AffineDisperser.polyOfCode_leastIrreducibleCode`). The remainders of `X ^ e`,
`e < 2 m`, give the arithmetic of `𝔽₂[X] / (g)` in the power basis
(`Cslib.AffineDisperser.pow_eq_sum_powerTable`).

## Main definitions

* `Cslib.AffineDisperser.polyOfBits`: the binary polynomial with a given coefficient list.
* `Cslib.AffineDisperser.mulXMod`, `Cslib.AffineDisperser.modBits`: reduction modulo a binary
  polynomial.
* `Cslib.AffineDisperser.isIrreducibleCode`: the irreducibility test by trial division.
* `Cslib.AffineDisperser.leastIrreducibleCode`: the exhaustive search for the least code.
* `Cslib.AffineDisperser.powerTable`: the remainders of the powers of `X`.

## Main results

* `Cslib.AffineDisperser.mk_polyOfBits_modBits`: `modBits g f` is congruent to `f` modulo `g`.
* `Cslib.AffineDisperser.modBits_all_false_iff`: the divisibility test.
* `Cslib.AffineDisperser.isIrreducibleCode_iff`: trial division decides irreducibility.
* `Cslib.AffineDisperser.polyOfCode_leastIrreducibleCode`: the search finds `leastIrreducible p`.
* `Cslib.AffineDisperser.pow_eq_sum_powerTable`: powers of a root in the power basis.

## References

* [R. Lidl, H. Niederreiter, *Finite Fields*, Chapters 1 and 3][LidlNiederreiter1997]
-/

@[expose] public section

namespace Cslib.AffineDisperser

open BitString Polynomial

/-- The binary polynomial with coefficient list `l`, constant term first. -/
noncomputable def polyOfBits : List Bool → (ZMod 2)[X]
  | [] => 0
  | b :: l => C (bitEquiv.symm b) + X * polyOfBits l

@[simp]
theorem polyOfBits_nil : polyOfBits [] = 0 := rfl

@[simp]
theorem polyOfBits_cons (b : Bool) (l : List Bool) :
    polyOfBits (b :: l) = C (bitEquiv.symm b) + X * polyOfBits l := rfl

private theorem polyOfBits_append (l l' : List Bool) :
    polyOfBits (l ++ l') = polyOfBits l + X ^ l.length * polyOfBits l' := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.cons_append, polyOfBits_cons, polyOfBits_cons, ih, List.length_cons, pow_succ]
    ring

@[simp]
theorem polyOfBits_replicate_false (k : ℕ) : polyOfBits (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih, bitEquiv_symm_false]

/-- The coefficient list of the monomial `X ^ k`. -/
private theorem polyOfBits_replicate_append_true (k : ℕ) :
    polyOfBits (List.replicate k false ++ [true]) = X ^ k := by
  simp [polyOfBits_append, bitEquiv_symm_true]

private theorem polyOfBits_zipWith_xor {l l' : List Bool} (h : l.length = l'.length) :
    polyOfBits (l.zipWith xor l') = polyOfBits l + polyOfBits l' := by
  induction l generalizing l' with
  | nil => cases l' <;> simp_all
  | cons b l ih =>
    cases l' with
    | nil => simp at h
    | cons b' l' =>
      simp only [List.zipWith_cons_cons, polyOfBits_cons, List.length_cons,
        Nat.add_right_cancel_iff] at h ⊢
      rw [ih h, show bitEquiv.symm (b ^^ b') = bitEquiv.symm b + bitEquiv.symm b' by
        cases b <;> cases b' <;> decide, C_add]
      ring

theorem polyOfBits_eq_zero_iff {l : List Bool} : polyOfBits l = 0 ↔ ∀ b ∈ l, b = false := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [polyOfBits_cons, List.forall_mem_cons, ← ih]
    constructor
    · intro h
      have h0 := congrArg (coeff · 0) h
      simp only [coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero, coeff_zero] at h0
      have hb : b = false := by revert h0; cases b <;> decide
      subst hb
      rw [bitEquiv_symm_false, C_0, zero_add] at h
      exact ⟨rfl, (mul_eq_zero.1 h).resolve_left X_ne_zero⟩
    · rintro ⟨rfl, h⟩
      rw [h, bitEquiv_symm_false]
      simp

private theorem degree_polyOfBits_lt (l : List Bool) : (polyOfBits l).degree < l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [polyOfBits_cons, List.length_cons]
    refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · exact (degree_C_le).trans_lt (by exact_mod_cast Nat.succ_pos _)
    · rcases eq_or_ne (polyOfBits l) 0 with h | h
      · rw [h, mul_zero, degree_zero]
        exact WithBot.bot_lt_coe _
      · rw [degree_mul, degree_X, degree_eq_natDegree h]
        rw [degree_eq_natDegree h] at ih
        have : (polyOfBits l).natDegree < l.length := by exact_mod_cast ih
        rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_lt]
        omega

/-- Dropping a top coefficient that is zero does not change the polynomial. -/
private theorem polyOfBits_take_of_getD {l : List Bool} {m : ℕ} (hl : l.length = m + 1)
    (htop : l.getD m false = false) : polyOfBits (l.take m) = polyOfBits l := by
  conv_rhs => rw [← List.take_append_drop m l]
  have hdrop : l.drop m = [false] := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
    rw [List.getD_eq_getElem _ _ (by omega)] at htop
    rw [htop]
  rw [hdrop, polyOfBits_append]
  simp [bitEquiv_symm_false]

private theorem aeval_polyOfBits {A : Type*} [CommSemiring A] [Algebra (ZMod 2) A] (α : A)
    (l : List Bool) :
    aeval α (polyOfBits l) =
      ∑ d ∈ Finset.range l.length, bitEquiv.symm (l.getD d false) • α ^ d := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [polyOfBits_cons, map_add, map_mul, aeval_C, aeval_X, ih, List.length_cons,
      Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero,
      Algebra.algebraMap_eq_smul_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [mul_smul_comm, pow_succ']

/-- The coefficient list of the code `m`, its binary digits, gives the polynomial with code `m`. -/
theorem polyOfBits_bits (m : ℕ) : polyOfBits m.bits = polyOfCode m := by
  induction m using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn, polyOfBits_cons, ih, Nat.bit_val]
    have := polyOfCode_two_mul_add n (bitEquiv.symm b)
    rw [show (bitEquiv.symm b).val = b.toNat by cases b <;> rfl] at this
    rw [this, add_comm]

/-- The binary digits of a nonzero number end with a one. -/
theorem exists_bits_eq_append_true {m : ℕ} (hm : m ≠ 0) : ∃ l, m.bits = l ++ [true] := by
  induction m using Nat.binaryRec' with
  | zero => exact absurd rfl hm
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    rcases eq_or_ne n 0 with rfl | hn0
    · exact ⟨[], by simp [hn rfl]⟩
    · obtain ⟨l, hl⟩ := ih hn0
      exact ⟨b :: l, by rw [hl, List.cons_append]⟩

theorem natDegree_polyOfBits_append_true (l : List Bool) :
    (polyOfBits (l ++ [true])).natDegree = l.length := by
  rw [polyOfBits_append]
  simp only [polyOfBits_cons, bitEquiv_symm_true, map_one, polyOfBits_nil, mul_zero, add_zero,
    mul_one]
  rw [add_comm, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_polyOfBits_lt l


/-! ### Reduction modulo a binary polynomial -/

/-- Multiplication by `X` modulo the polynomial with coefficient list `g`, on coefficient lists of
length `g.length - 1`: shift up, add `g` when the coefficient of degree `g.length - 1` is one, and
drop that coefficient. -/
def mulXMod (g r : List Bool) : List Bool :=
  (if (false :: r).getD (g.length - 1) false then (false :: r).zipWith xor g
    else false :: r).take (g.length - 1)

private theorem length_mulXMod (l r : List Bool) (h : r.length = l.length) :
    (mulXMod (l ++ [true]) r).length = l.length := by
  unfold mulXMod
  split_ifs <;> simp [h]

private theorem mk_polyOfBits_mulXMod (l r : List Bool) (h : r.length = l.length) :
    AdjoinRoot.mk (polyOfBits (l ++ [true])) (polyOfBits (mulXMod (l ++ [true]) r)) =
      AdjoinRoot.mk (polyOfBits (l ++ [true])) (X * polyOfBits r) := by
  have hlen : (l ++ [true]).length - 1 = l.length := by simp
  have hs : (false :: r).length = l.length + 1 := by simp [h]
  have hX : polyOfBits (false :: r) = X * polyOfBits r := by
    simp [bitEquiv_symm_false]
  unfold mulXMod
  rw [hlen]
  split_ifs with htop
  · have hz : ((false :: r).zipWith xor (l ++ [true])).length = l.length + 1 := by simp [h]
    have htop' : ((false :: r).zipWith xor (l ++ [true])).getD l.length false = false := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getElem_zipWith]
      rw [List.getD_eq_getElem _ _ (by omega)] at htop
      rw [htop, List.getElem_append_right (by simp)]
      simp
    rw [polyOfBits_take_of_getD hz htop', polyOfBits_zipWith_xor (by simp [h]), hX, map_add,
      AdjoinRoot.mk_self, add_zero]
  · rw [polyOfBits_take_of_getD hs (by simpa using htop), hX]

/-- One step of `modBits`: the next power of `X` modulo `g`, and the partial remainder. -/
def modStep (g : List Bool) (state : List Bool × List Bool) (b : Bool) :
    List Bool × List Bool :=
  (mulXMod g state.1, if b then state.2.zipWith xor state.1 else state.2)

/-- The remainder of the polynomial with coefficient list `f` modulo the one with coefficient list
`g`, as a coefficient list of length `g.length - 1`: the sum of the remainders of the powers
`X ^ j` with `f j = 1`, computed by repeated multiplication by `X` modulo `g`. -/
def modBits (g f : List Bool) : List Bool :=
  (f.foldl (modStep g)
    ((true :: List.replicate (g.length - 2) false).take (g.length - 1),
      List.replicate (g.length - 1) false)).2

private theorem modStep_foldl (l f p a : List Bool) (hp : p.length = l.length)
    (ha : a.length = l.length) :
    (f.foldl (modStep (l ++ [true])) (p, a)).1.length = l.length ∧
      (f.foldl (modStep (l ++ [true])) (p, a)).2.length = l.length ∧
      AdjoinRoot.mk (polyOfBits (l ++ [true]))
          (polyOfBits (f.foldl (modStep (l ++ [true])) (p, a)).1) =
        AdjoinRoot.mk (polyOfBits (l ++ [true])) (X ^ f.length * polyOfBits p) ∧
      AdjoinRoot.mk (polyOfBits (l ++ [true]))
          (polyOfBits (f.foldl (modStep (l ++ [true])) (p, a)).2) =
        AdjoinRoot.mk (polyOfBits (l ++ [true])) (polyOfBits a + polyOfBits p * polyOfBits f) := by
  induction f generalizing p a with
  | nil => simp [hp, ha]
  | cons b f ih =>
    have hp' := length_mulXMod l p hp
    have ha' : (if b then a.zipWith xor p else a).length = l.length := by
      split_ifs <;> simp [ha, hp]
    obtain ⟨h1, h2, h3, h4⟩ := ih _ _ hp' ha'
    refine ⟨h1, h2, ?_, ?_⟩
    · rw [List.foldl_cons, modStep, h3, map_mul, mk_polyOfBits_mulXMod l p hp, map_mul,
        List.length_cons, pow_succ, map_mul, map_mul]
      ring
    · rw [List.foldl_cons, modStep, h4, map_add, map_mul, mk_polyOfBits_mulXMod l p hp,
        polyOfBits_cons]
      split_ifs with hb
      · subst hb
        rw [polyOfBits_zipWith_xor (by rw [ha, hp]), bitEquiv_symm_true]
        simp only [map_add, map_mul, map_one]
        ring
      · rw [Bool.not_eq_true] at hb
        subst hb
        rw [bitEquiv_symm_false]
        simp only [map_add, map_mul, map_zero]
        ring

private theorem length_modBits (l f : List Bool) : (modBits (l ++ [true]) f).length = l.length := by
  have hlen : (l ++ [true]).length - 1 = l.length := by simp
  unfold modBits
  rw [hlen]
  exact (modStep_foldl l f _ _ (by simp; omega) (by simp)).2.1

private theorem mk_polyOfBits_one (l : List Bool) :
    AdjoinRoot.mk (polyOfBits (l ++ [true]))
      (polyOfBits ((true :: List.replicate ((l ++ [true]).length - 2) false).take l.length)) =
      1 := by
  rcases l.eq_nil_or_concat with rfl | ⟨l', b, rfl⟩
  · have h1 : polyOfBits ([] ++ [true]) = 1 := by simp [bitEquiv_symm_true]
    rw [h1, ← map_one (AdjoinRoot.mk (1 : (ZMod 2)[X])), AdjoinRoot.mk_eq_mk]
    exact one_dvd _
  · rw [List.length_append, List.length_singleton, List.length_concat, List.take_succ_cons]
    simp [bitEquiv_symm_true]

/-- For a coefficient list `g = l ++ [true]` with top coefficient one, `modBits g f` is congruent
to `f` modulo the polynomial of `g`: both have the same image in `AdjoinRoot (polyOfBits g)`. -/
theorem mk_polyOfBits_modBits (l f : List Bool) :
    AdjoinRoot.mk (polyOfBits (l ++ [true])) (polyOfBits (modBits (l ++ [true]) f)) =
      AdjoinRoot.mk (polyOfBits (l ++ [true])) (polyOfBits f) := by
  have hlen : (l ++ [true]).length - 1 = l.length := by simp
  unfold modBits
  rw [hlen]
  rw [(modStep_foldl l f _ _ (by simp; omega) (by simp)).2.2.2, map_add, map_mul, mk_polyOfBits_one]
  simp


private theorem polyOfBits_append_true_ne_zero (l : List Bool) : polyOfBits (l ++ [true]) ≠ 0 := by
  rw [Ne, polyOfBits_eq_zero_iff]
  intro h
  exact Bool.true_eq_false.mp (h true (by simp))

/-- **The divisibility test**: the polynomial with coefficient list `l ++ [true]` divides the one
with coefficient list `f` exactly when the remainder `modBits` vanishes. -/
theorem modBits_all_false_iff (l f : List Bool) :
    (∀ b ∈ modBits (l ++ [true]) f, b = false) ↔ polyOfBits (l ++ [true]) ∣ polyOfBits f := by
  rw [← polyOfBits_eq_zero_iff, ← AdjoinRoot.mk_eq_zero, ← mk_polyOfBits_modBits,
    AdjoinRoot.mk_eq_zero]
  refine ⟨fun h => h ▸ dvd_zero _, fun h => eq_zero_of_dvd_of_degree_lt h ?_⟩
  rw [degree_eq_natDegree (polyOfBits_append_true_ne_zero l), natDegree_polyOfBits_append_true,
    ← length_modBits l f]
  exact degree_polyOfBits_lt _

private theorem natDegree_polyOfCode_eq_log (m : ℕ) : (polyOfCode m).natDegree = Nat.log 2 m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · exact natDegree_polyOfCode hm

private theorem polyOfCode_one : polyOfCode 1 = 1 := by
  rw [← polyOfBits_bits, Nat.one_bits]
  simp [bitEquiv_symm_true]

/-- The divisibility test on codes: for `d ≠ 0`, some coefficient of the remainder of `f` modulo
the polynomial with code `d` is one exactly when that polynomial does not divide `f`. -/
theorem any_modBits_bits_iff {d : ℕ} (hd : d ≠ 0) (f : List Bool) :
    (modBits d.bits f).any id = true ↔ ¬ polyOfCode d ∣ polyOfBits f := by
  obtain ⟨l, hl⟩ := exists_bits_eq_append_true hd
  rw [← polyOfBits_bits, hl, ← modBits_all_false_iff]
  simp only [List.any_eq_true, id_eq]
  constructor
  · rintro ⟨b, hb, rfl⟩ h
    exact Bool.true_eq_false.mp (h true hb)
  · intro h
    push Not at h
    obtain ⟨b, hb, hb'⟩ := h
    exact ⟨b, hb, by simpa using hb'⟩

/-- **Trial division**: whether the binary polynomial with code `m` is irreducible. It is when
`m ≥ 2` and no polynomial of degree between `1` and half the degree of `m` (a code `d < m`)
divides it. -/
def isIrreducibleCode (m : ℕ) : Bool :=
  decide (2 ≤ m) && (List.range m).all fun d =>
    decide (d < 2) || decide (Nat.log 2 m / 2 < Nat.log 2 d) || (modBits d.bits m.bits).any id

/-- **Trial division decides irreducibility**: `isIrreducibleCode m` holds exactly when the binary
polynomial with code `m` is irreducible. -/
theorem isIrreducibleCode_iff (m : ℕ) :
    isIrreducibleCode m = true ↔ Irreducible (polyOfCode m) := by
  unfold isIrreducibleCode
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true]
  rcases lt_or_ge m 2 with hm | hm
  · simp only [not_le.2 hm, false_and, false_iff]
    obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
    · simp
    · rw [polyOfCode_one]
      exact not_irreducible_one
  have hm0 : m ≠ 0 := by omega
  have hdeg : (polyOfCode m).natDegree = Nat.log 2 m := natDegree_polyOfCode hm0
  have hlog : 1 ≤ Nat.log 2 m := Nat.le_log_of_pow_le one_lt_two (by simpa using hm)
  have hF0 : polyOfCode m ≠ 0 := (polyOfCode_ne_zero_and_natDegree hm0).1
  rw [irreducible_iff_lt_natDegree_lt hF0 (not_isUnit_of_natDegree_pos _ (by omega)), hdeg,
    ← polyOfBits_bits m]
  simp only [hm, true_and]
  constructor
  · intro h q hq hdq hdvd
    obtain ⟨d, rfl⟩ := polyOfCode_surjective q
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hq.ne_zero polyOfCode_zero
    rw [natDegree_polyOfCode hd0, Finset.mem_Ioc] at hdq
    have hd2 : 2 ≤ d := by
      have := Nat.pow_log_le_self 2 hd0
      have : 2 ^ 1 ≤ 2 ^ Nat.log 2 d := Nat.pow_le_pow_right two_pos hdq.1
      omega
    have hdm : d < m :=
      calc d < 2 ^ (Nat.log 2 d + 1) := Nat.lt_pow_succ_log_self one_lt_two d
        _ ≤ 2 ^ Nat.log 2 m := Nat.pow_le_pow_right two_pos (by omega)
        _ ≤ m := Nat.pow_log_le_self 2 hm0
    rcases h d hdm with (h | h) | h
    · omega
    · omega
    · exact (any_modBits_bits_iff hd0 _).1 h hdvd
  · intro h d hdm
    by_contra hc
    simp only [not_or, not_lt, Bool.not_eq_true] at hc
    obtain ⟨⟨hd2, hdlog⟩, hany⟩ := hc
    have hd0 : d ≠ 0 := by omega
    have hd : polyOfCode d ≠ 0 := (polyOfCode_ne_zero_and_natDegree hd0).1
    refine h (polyOfCode d) (monic_of_ne_zero hd) ?_ ?_
    · rw [natDegree_polyOfCode hd0, Finset.mem_Ioc]
      exact ⟨Nat.log_pos one_lt_two hd2, hdlog⟩
    · by_contra hndvd
      rw [← any_modBits_bits_iff hd0] at hndvd
      rw [hndvd] at hany
      exact Bool.true_eq_false.mp hany

/-- **The exhaustive search**: the least code `m < B` of an irreducible binary polynomial of degree
`p`, by trial division (`0` if there is none). -/
def leastIrreducibleCode (B p : ℕ) : ℕ :=
  ((List.range B).find? fun m => Nat.log 2 m == p && isIrreducibleCode m).getD 0

/-- The search finds the code of `leastIrreducible p` once its range contains all codes of degree
`p`. -/
theorem polyOfCode_leastIrreducibleCode {B p : ℕ} (hp : p ≠ 0) (hB : 2 ^ (p + 1) ≤ B) :
    polyOfCode (leastIrreducibleCode B p) = leastIrreducible p := by
  obtain ⟨m, -, hm2, hm3, hmin⟩ := exists_code_leastIrreducible hp
  have hP : ∀ j, (Nat.log 2 j == p && isIrreducibleCode j) = true ↔
      Irreducible (polyOfCode j) ∧ (polyOfCode j).natDegree = p := by
    intro j
    rw [Bool.and_eq_true, beq_iff_eq, isIrreducibleCode_iff, natDegree_polyOfCode_eq_log, and_comm]
  have hfind :
      (List.range B).find? (fun m => Nat.log 2 m == p && isIrreducibleCode m) = some m := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨(hP m).2 ⟨hm3 ▸ irreducible_leastIrreducible p, hm3 ▸ natDegree_leastIrreducible hp⟩,
      m, by simp; omega, by simp, fun j hj => ?_⟩
    rw [List.getElem_range, Bool.not_eq_true']
    by_contra h
    exact hmin j hj ((hP j).1 (by simpa using h))
  rw [leastIrreducibleCode, hfind, Option.getD_some, hm3]

/-! ### Remainders of powers -/

/-- The coefficient lists of the remainders of `X ^ e`, `e < 2 (g.length - 1)`, modulo the
polynomial with coefficient list `g`. -/
def powerTable (g : List Bool) : List (List Bool) :=
  (List.range (2 * (g.length - 1))).map fun e => modBits g (List.replicate e false ++ [true])

private theorem length_powerTable (g : List Bool) : (powerTable g).length = 2 * (g.length - 1) := by
  simp [powerTable]

/-- At a root `α` of the polynomial with coefficient list `l ++ [true]`, the power `α ^ e`,
`e < 2 l.length`, is the combination of the powers below `l.length` given by `powerTable`. -/
theorem pow_eq_sum_powerTable {A : Type*} [CommRing A] [Algebra (ZMod 2) A] (l : List Bool)
    {α : A} (hα : aeval α (polyOfBits (l ++ [true])) = 0) {e : ℕ} (he : e < 2 * l.length) :
    α ^ e = ∑ d ∈ Finset.range l.length,
      bitEquiv.symm (((powerTable (l ++ [true])).getD e []).getD d false) • α ^ d := by
  have hlen : (l ++ [true]).length - 1 = l.length := by simp
  have hget : (powerTable (l ++ [true])).getD e [] =
      modBits (l ++ [true]) (List.replicate e false ++ [true]) := by
    rw [List.getD_eq_getElem _ _ (by rw [length_powerTable, hlen]; exact he)]
    simp [powerTable]
  rw [hget, ← length_modBits l (List.replicate e false ++ [true]), ← aeval_polyOfBits]
  have h := mk_polyOfBits_modBits l (List.replicate e false ++ [true])
  rw [AdjoinRoot.mk_eq_mk, polyOfBits_replicate_append_true] at h
  have h0 := aeval_eq_zero_of_dvd_aeval_eq_zero h hα
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, aeval_X_pow]

end Cslib.AffineDisperser
