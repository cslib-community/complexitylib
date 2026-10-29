/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.AffineDisperser.Program
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Prime
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.GetD

/-!
# The explicit affine disperser in polynomial time

The program `Cslib.AffineDisperser.explicitDisperserProgram` computes the explicit affine
disperser (`Cslib.AffineDisperser.explicitDisperserProgram_eq`); this file certifies it in the
polynomial-time calculus of multi-tape machines, with input bits in `encBits` and natural
numbers in unary. All runtime sizes are polynomial in the input length `N`:

* the parameters (`⌊log₂ N⌋`, the primes in `(L, 4 L]` by trial division, the greedy choice and
  the field degree `n ≤ N + 1`) are unary arithmetic on numbers at most `N + 1`;
* each irreducible polynomial is found by exhaustive search over the codes below
  `2 ^ (4 L + 1) ≤ 2 (N + 1) ^ 2` (`Cslib.AffineDisperser.codeBound_le`), each tested by trial
  division with remainders computed by repeated multiplication by `X`;
* the multiplication table has `n ^ 3` entries, each a product over the prime factors of `n`;
* a field multiplication sums at most `n ^ 2` table entries, uniformly in the table
  (`Cslib.AffineDisperser.computableInPolyTime_fieldMul`); the `r` powers take at most
  `2 r` multiplications each, the elementary symmetric polynomial `r t` more, and the trace reads
  the diagonals of the table.

Every loop is certified with a bound on its intermediate states, so the certificate charges the
whole computation, including every field operation
(`Cslib.AffineDisperser.computableInPolyTime_explicitDisperser`). The exponent of the
polynomial is not computed.

## Main definitions

* `Cslib.AffineDisperser.selectStep`: one step of the greedy choice of primes, as a fold.
* `Cslib.AffineDisperser.encTable`: the encoding of multiplication tables.

## Main results

* `Cslib.AffineDisperser.computableInPolyTime_leastIrreducibleCode`: the search for the
  irreducible polynomials.
* `Cslib.AffineDisperser.computableInPolyTime_explicitTable`: the multiplication table.
* `Cslib.AffineDisperser.computableInPolyTime_traceSymCoords`: `traceSym 1 r t` in
  coordinates, uniformly in the multiplication table.
* `Cslib.AffineDisperser.computableInPolyTime_explicitDisperser`: the explicit disperser is
  computable in polynomial time.
* `Cslib.AffineDisperser.setOf_explicitDisperser_mem_P`: it decides a problem in `P`.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.AffineDisperser

open Turing.MultiTapeTM ComputableInPolyTime Explicit

/-! ### Binary polynomials -/

/-- Multiplication by `X` modulo a binary polynomial, on coefficient lists. -/
@[fun_prop]
theorem computableInPolyTime_mulXMod :
    ComputableInPolyTime (fun p : List Bool × List Bool => mulXMod p.1 p.2)
      (encPair encBits encBits) encBits := by
  unfold mulXMod
  fun_prop

private theorem length_mulXMod_le (g r : List Bool) : (mulXMod g r).length ≤ g.length - 1 :=
  List.length_take_le _ _

/-- The remainder modulo a binary polynomial, by a left fold over the coefficients whose state, the
current power of `X` and the partial remainder, never exceeds the degree of the modulus. -/
@[fun_prop]
theorem computableInPolyTime_modBits :
    ComputableInPolyTime (fun p : List Bool × List Bool => modBits p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hstep : ComputableInPolyTime
      (fun q : (List Bool × (List Bool × List Bool)) × Bool => modStep q.1.1 q.1.2 q.2)
      (encPair (encPair encBits (encPair encBits encBits)) encBool)
      (encPair encBits encBits) := by
    unfold modStep
    fun_prop
  have hinit : ComputableInPolyTime (fun p : List Bool × List Bool =>
      ((true :: List.replicate (p.1.length - 2) false).take (p.1.length - 1),
        List.replicate (p.1.length - 1) false))
      (encPair encBits encBits) (encPair encBits encBits) := by
    fun_prop
  have h := (foldlWith_spec (encA := encBool) (encL := encBits) (par := Prod.fst)
    (list := Prod.snd) (step := modStep) (fst encBits encBits) (snd encBits encBits) hinit hstep
    (fun p _ state => state.1.length ≤ p.1.length - 1 ∧ state.2.length ≤ p.1.length - 1)
    (fun p => by simp) (fun p consumed state value _ h => by
      refine ⟨length_mulXMod_le _ _, ?_⟩
      simp only [modStep]
      split_ifs
      · simp only [List.length_zipWith]
        omega
      · exact h.2)
    (size := fun p => 3 * p.1.length + 1) (.of_forall_le 3 1 fun p => by simp; omega)
    (fun p consumed state _ h => by simp [encPair_apply]; omega)).1
  exact (snd encBits encBits).comp h

/-- The binary digits of a unary natural. -/
theorem computableInPolyTime_bits_unary :
    ComputableInPolyTime Nat.bits encUnary encBits :=
  (of_eq (f := Nat.bits) (encIn := encNat) (encOut := encBits) fun _ => rfl).comp
    unary_to_binary

/-- The irreducibility test by trial division, on a unary code. -/
@[fun_prop]
theorem computableInPolyTime_isIrreducibleCode :
    ComputableInPolyTime isIrreducibleCode encUnary encBool := by
  unfold isIrreducibleCode
  have := computableInPolyTime_bits_unary
  fun_prop

/-- The exhaustive search for the least irreducible code below a unary bound. -/
@[fun_prop]
theorem computableInPolyTime_leastIrreducibleCode :
    ComputableInPolyTime (fun q : ℕ × ℕ => leastIrreducibleCode q.1 q.2)
      (encPair encUnary encUnary) encUnary := by
  unfold leastIrreducibleCode
  fun_prop

/-- The remainders of the powers of `X`. -/
@[fun_prop]
theorem computableInPolyTime_powerTable :
    ComputableInPolyTime powerTable encBits (encList encBits) := by
  unfold powerTable
  fun_prop


/-! ### Lists of unary naturals -/

/-- The product of a computed list of positive unary naturals, when the product is polynomially
bounded: every partial product is at most the whole product. -/
private theorem computableInPolyTime_prod_of_le {α : Type} {input : α ↪ List Bool}
    {list : α → List ℕ}
    (hlist : ComputableInPolyTime list input (encList encUnary))
    (hpos : ∀ a, ∀ p ∈ list a, 0 < p) {B : α → ℕ}
    (hB : PolyBounded (fun a => (input a).length) B) (hle : ∀ a, (list a).prod ≤ B a) :
    ComputableInPolyTime (fun a => (list a).prod) input encUnary := by
  have h := foldl' (encA := encUnary) (encL := encList encUnary) (step := fun s p => s * p)
    hlist (const 1) unary_mul hB (fun a i _ => by
      rw [encUnary_apply, List.length_replicate, ← List.prod_eq_foldl]
      refine le_trans ?_ (hle a)
      rw [← List.prod_take_mul_prod_drop (list a) i]
      exact Nat.le_mul_of_pos_right _
        (List.prod_pos fun p hp => hpos a p (List.mem_of_mem_drop hp)))
  simpa only [← List.prod_eq_foldl] using h

/-! ### The parameters -/

/-- The primes in `(a, b]`, from unary bounds. -/
@[fun_prop]
theorem computableInPolyTime_primesIoc :
    ComputableInPolyTime (fun q : ℕ × ℕ => primesIoc q.1 q.2)
      (encPair encUnary encUnary) (encList encUnary) := by
  simp_rw [primesIoc, List.range'_eq_map_range]
  fun_prop

/-- One step of the greedy choice of primes: the remaining budget and the primes chosen. -/
def selectStep (state : ℕ × List ℕ) (p : ℕ) : ℕ × List ℕ :=
  if p ≤ state.1 then (state.1 / p, state.2 ++ [p]) else state

private theorem foldl_selectStep (T : ℕ) (ps chosen : List ℕ) :
    (ps.foldl selectStep (T, chosen)).2 = chosen ++ selectBelow T ps := by
  induction ps generalizing T chosen with
  | nil => simp [selectBelow]
  | cons p ps ih =>
    rw [List.foldl_cons, selectStep, selectBelow]
    split_ifs
    · rw [ih, List.append_assoc, List.singleton_append]
    · exact ih T chosen

/-- The greedy choice of primes below a unary budget. -/
@[fun_prop]
theorem computableInPolyTime_selectBelow :
    ComputableInPolyTime (fun q : ℕ × List ℕ => selectBelow q.1 q.2)
      (encPair encUnary (encList encUnary)) (encList encUnary) := by
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × List ℕ) × ℕ => selectStep q.1 q.2)
      (encPair (encPair encUnary (encList encUnary)) encUnary)
      (encPair encUnary (encList encUnary)) := by
    unfold selectStep
    fun_prop
  have h := (foldl_spec (encA := encUnary) (encL := encList encUnary)
    (list := fun q : ℕ × List ℕ => q.2) (init := fun q => (q.1, []))
    (snd encUnary (encList encUnary)) (by fun_prop) hstep
    (fun q consumed state => state.1 ≤ q.1 ∧ state.2.Sublist consumed)
    (fun q => by simp) (fun q consumed state value _ h => by
      simp only [selectStep]
      split_ifs
      · exact ⟨(Nat.div_le_self _ _).trans h.1, h.2.append (List.Sublist.refl _)⟩
      · exact ⟨h.1, h.2.trans (List.sublist_append_left _ _)⟩)
    (size := fun q => (encPair encUnary (encList encUnary) q).length) .self
    (fun q consumed state hprefix h => by
      have hsub := ((h.2.trans hprefix.sublist).map fun a => 2 * (encUnary a).length + 1)
      have := hsub.sum_le_sum (fun _ _ => Nat.zero_le _)
      simp only [length_encPair, length_encList, encUnary_apply, List.length_replicate] at this ⊢
      omega)).1
  simpa only [Function.comp_def, foldl_selectStep, List.nil_append] using
    (snd encUnary (encList encUnary)).comp h

/-- The prime bound `L = ⌊⌊log₂ N⌋ / 3⌋` of unary `N`. -/
@[fun_prop]
theorem computableInPolyTime_primeBound :
    ComputableInPolyTime primeBound encUnary encUnary := by
  unfold primeBound
  fun_prop

/-- The primes of the field degree on `N` bits, `N` in unary. -/
@[fun_prop]
theorem computableInPolyTime_degreePrimes :
    ComputableInPolyTime degreePrimes encUnary (encList encUnary) := by
  unfold degreePrimes
  fun_prop

private theorem selectBelow_zero {ps : List ℕ} (hps : ∀ p ∈ ps, 0 < p) : selectBelow 0 ps = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [selectBelow, ite_eq_right_iff.2 (by have := hps p List.mem_cons_self; omega)]
    exact ih fun q hq => hps q (List.mem_cons_of_mem _ hq)

private theorem prod_degreePrimes_le (N : ℕ) : (degreePrimes N).prod ≤ N + 1 := by
  rcases Nat.eq_zero_or_pos (N / (Nat.log 2 N + 1) ^ 2) with hT | hT
  · rw [degreePrimes, hT, selectBelow_zero fun p hp => (mem_primesIoc.1 hp).2.2.pos]
    simp
  · exact (prod_selectBelow_le hT _).trans ((Nat.div_le_self _ _).trans (Nat.le_succ N))

/-- The field degree on `N` bits, `N` in unary: a product of at most `N + 1`. -/
@[fun_prop]
theorem computableInPolyTime_fieldDegree :
    ComputableInPolyTime fieldDegree encUnary encUnary := by
  have h := computableInPolyTime_prod_of_le computableInPolyTime_degreePrimes
    (fun N p hp => (prime_of_mem_degreePrimes hp).2.2.pos) (B := fun N => N + 1)
    (.of_forall_le 1 1 fun N => by simp) prod_degreePrimes_le
  simpa only [← fieldDegree_eq_prod] using h

/-- The number of blocks on `N` bits, `N` in unary. -/
@[fun_prop]
theorem computableInPolyTime_numBlocks :
    ComputableInPolyTime numBlocks encUnary encUnary := by
  unfold numBlocks
  fun_prop

/-- The degree of the elementary symmetric polynomial on `N` bits, `N` in unary. -/
@[fun_prop]
theorem computableInPolyTime_symDegree :
    ComputableInPolyTime symDegree encUnary encUnary := by
  unfold symDegree
  fun_prop

/-- The search range is polynomial: `2 ^ (4 L + 1) ≤ 2 (N + 1) ^ 2`, as `4 L ≤ 2 ⌊log₂ N⌋`. -/
theorem codeBound_le (N : ℕ) : codeBound N ≤ 2 * (N + 1) * (N + 1) := by
  have hlog : 2 ^ Nat.log 2 N ≤ N + 1 := by
    rcases eq_or_ne N 0 with rfl | hN
    · simp
    · exact (Nat.pow_log_le_self 2 hN).trans (Nat.le_succ N)
  calc codeBound N = 2 * 2 ^ (4 * primeBound N) := by rw [codeBound, pow_succ, mul_comm]
    _ ≤ 2 * 2 ^ (2 * Nat.log 2 N) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos (by unfold primeBound; omega))
    _ = 2 * (2 ^ Nat.log 2 N * 2 ^ Nat.log 2 N) := by rw [← pow_add, ← two_mul]
    _ ≤ 2 * ((N + 1) * (N + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hlog hlog)
    _ = 2 * (N + 1) * (N + 1) := by ring

/-- The search range `2 ^ (4 L + 1)` on `N` bits, in unary, from `N` in unary. -/
@[fun_prop]
theorem computableInPolyTime_codeBound :
    ComputableInPolyTime codeBound encUnary encUnary := by
  have hvalue : ComputableInPolyTime codeBound encUnary encNat := by
    unfold codeBound
    have := ComputableInPolyTime.binary_two_pow
    fun_prop
  exact ComputableInPolyTime.binary_to_unary_bounded hvalue
    (bound := fun N => 2 * (N + 1) * (N + 1)) (by fun_prop)
    codeBound_le

/-! ### The multiplication table -/

/-- The tables of remainders of powers of `X` on `N` bits, `N` in unary: the search for each
irreducible polynomial ranges over the `2 ^ (4 L + 1) ≤ 2 (N + 1) ^ 2` codes below `codeBound N`. -/
@[fun_prop]
theorem computableInPolyTime_explicitPowerTables :
    ComputableInPolyTime explicitPowerTables encUnary (encList (encList encBits)) := by
  unfold explicitPowerTables
  have := computableInPolyTime_bits_unary
  fun_prop

/-- The mixed-radix digits in the radix of the field degree on `N` bits; every partial product of
the radix is at most `N + 1`. -/
private theorem computableInPolyTime_mixedDigit_degreePrimes :
    ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ => mixedDigit (degreePrimes q.1.1) q.1.2 q.2)
      (encPair (encPair encUnary encUnary) encUnary) encUnary := by
  have htake : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ => (degreePrimes q.1.1).take q.2)
      (encPair (encPair encUnary encUnary) encUnary) (encList encUnary) := by
    fun_prop
  have hprod := computableInPolyTime_prod_of_le htake
    (fun q p hp => (prime_of_mem_degreePrimes (List.mem_of_mem_take hp)).2.2.pos)
    (B := fun q => q.1.1 + 1) (.of_forall_le 1 1 fun q => by simp [encPair_apply]; omega)
    (fun q => by
      refine le_trans ?_ (prod_degreePrimes_le q.1.1)
      rw [← List.prod_take_mul_prod_drop (degreePrimes q.1.1) q.2]
      exact Nat.le_mul_of_pos_right _ (List.prod_pos fun p hp =>
        (prime_of_mem_degreePrimes (List.mem_of_mem_drop hp)).2.2.pos))
  unfold mixedDigit
  fun_prop

/-- Mixed-radix digits in the radix of the field degree, as a composition rule. -/
@[fun_prop]
theorem computableInPolyTime_mixedDigit_degreePrimes' {α : Type} {input : α ↪ List Bool}
    {N u i : α → ℕ} (hN : ComputableInPolyTime N input encUnary)
    (hu : ComputableInPolyTime u input encUnary)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => mixedDigit (degreePrimes (N a)) (u a) (i a)) input
      encUnary :=
  computableInPolyTime_mixedDigit_degreePrimes.comp ((hN.prod hu).prod hi)

/-- Coordinates of the products of monomials of the explicit field on `N` bits, `N` in unary. -/
private theorem computableInPolyTime_monomialBit_explicit : ComputableInPolyTime
    (fun q : ((ℕ × ℕ) × ℕ) × ℕ =>
      monomialBit (degreePrimes q.1.1.1) (explicitPowerTables q.1.1.1) q.1.1.2 q.1.2 q.2)
    (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encBool := by
  unfold monomialBit
  fun_prop

/-- Coordinates of the products of monomials of the explicit field, as a composition rule. -/
@[fun_prop]
theorem computableInPolyTime_monomialBit_explicit' {α : Type} {input : α ↪ List Bool}
    {N u w v : α → ℕ} (hN : ComputableInPolyTime N input encUnary)
    (hu : ComputableInPolyTime u input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hv : ComputableInPolyTime v input encUnary) :
    ComputableInPolyTime
      (fun a => monomialBit (degreePrimes (N a)) (explicitPowerTables (N a)) (u a) (w a) (v a))
      input encBool :=
  computableInPolyTime_monomialBit_explicit.comp (((hN.prod hu).prod hw).prod hv)

/-- The multiplication table of the explicit field on `N` bits, `N` in unary: its `n ^ 3`
entries, `n ≤ N + 1`, are products over the prime factors of `n`. -/
@[fun_prop]
theorem computableInPolyTime_explicitTable :
    ComputableInPolyTime explicitTable encUnary (encList (encList encBits)) := by
  unfold explicitTable monomialTable
  simp_rw [← fieldDegree_eq_prod]
  fun_prop

/-! ### Field arithmetic in coordinates -/

/-- A multiplication table, as a list of rows of coordinate words. -/
abbrev encTable : List (List (List Bool)) ↪ List Bool :=
  encList (encList encBits)

/-- An entry of a computed multiplication table. -/
@[fun_prop]
theorem computableInPolyTime_tableEntry {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {u w : α → ℕ}
    (htab : ComputableInPolyTime tab input encTable)
    (hu : ComputableInPolyTime u input encUnary)
    (hw : ComputableInPolyTime w input encUnary) :
    ComputableInPolyTime (fun a => tableEntry (tab a) (u a) (w a)) input encBits :=
  ComputableInPolyTime.listGetDWithInput (ComputableInPolyTime.listGetDWithInput htab hu []) hw []

/-- **Multiplication in coordinates**, uniformly in the multiplication table: the sum of at most
`n ^ 2` table entries, `n` the number of rows. -/
theorem computableInPolyTime_fieldMul : ComputableInPolyTime
    (fun p : List (List (List Bool)) × List Bool × List Bool => fieldMul p.1 p.2.1 p.2.2)
    (encPair encTable (encPair encBits encBits)) encBits := by
  unfold fieldMul
  fun_prop

/-- Multiplication in coordinates, as a composition rule. -/
@[fun_prop]
theorem computableInPolyTime_fieldMul' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {a b : α → List Bool}
    (htab : ComputableInPolyTime tab input encTable)
    (ha : ComputableInPolyTime a input encBits)
    (hb : ComputableInPolyTime b input encBits) :
    ComputableInPolyTime (fun x => fieldMul (tab x) (a x) (b x)) input encBits := by
  simpa only [Function.comp_def] using computableInPolyTime_fieldMul.comp (htab.prod (ha.prod hb))

theorem length_fieldMul (tab : List (List (List Bool))) (a b : List Bool) :
    (fieldMul tab a b).length = tab.length := by
  simp [fieldMul]

/-- The powers `y ^ (2 ^ (k + 1) - 1)`, by `k` multiplications and squarings; every
intermediate power has `n` coordinates. -/
private theorem computableInPolyTime_powerPred : ComputableInPolyTime
    (fun p : List (List (List Bool)) × List Bool × ℕ => powerPred p.1 p.2.1 p.2.2)
    (encPair encTable (encPair encBits encUnary)) encBits := by
  unfold powerPred
  refine iterateWithInput_of_bounded_growth (by fun_prop) (by fun_prop) (by fun_prop)
    ⟨(length_list (encList encBits)).comp (fst _ _) |>.polyBounded, fun p z => ?_⟩
  simp [length_fieldMul]

/-- Powers in coordinates, as a composition rule. -/
@[fun_prop]
theorem computableInPolyTime_powerPred' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {y : α → List Bool} {k : α → ℕ}
    (htab : ComputableInPolyTime tab input encTable)
    (hy : ComputableInPolyTime y input encBits)
    (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun x => powerPred (tab x) (y x) (k x)) input encBits := by
  simpa only [Function.comp_def] using
    computableInPolyTime_powerPred.comp (htab.prod (hy.prod hk))

/-- One step of the dynamic program for the elementary symmetric polynomials. -/
private theorem computableInPolyTime_esymmStep : ComputableInPolyTime
    (fun p : (List (List (List Bool)) × List (List Bool)) × List Bool =>
      esymmStep p.1.1 p.1.2 p.2)
    (encPair (encPair encTable (encList encBits)) encBits) (encList encBits) := by
  unfold esymmStep
  fun_prop

private theorem length_esymmStep (tab : List (List (List Bool))) (E : List (List Bool))
    (z : List Bool) : (esymmStep tab E z).length = E.length := by
  simp [esymmStep]

/-- **The elementary symmetric polynomial `e_t` in coordinates**: the dynamic program keeps `t`
words of at most `n` coordinates. -/
private theorem computableInPolyTime_esymmCoords : ComputableInPolyTime
    (fun p : (List (List (List Bool)) × ℕ) × List (List Bool) => esymmCoords p.1.1 p.1.2 p.2)
    (encPair (encPair encTable encUnary) (encList encBits)) encBits := by
  have hsize : ComputableInPolyTime
      (fun p : (List (List (List Bool)) × ℕ) × List (List Bool) =>
        p.1.2 * (2 * p.1.1.length + 1))
      (encPair (encPair encTable encUnary) (encList encBits)) encUnary := by
    fun_prop
  have h := (foldlWith_spec (encIn := encPair (encPair encTable encUnary) (encList encBits))
    (encA := encBits) (encL := encList encBits)
    (par := fun p : (List (List (List Bool)) × ℕ) × List (List Bool) => p.1.1)
    (list := Prod.snd) (init := fun p => List.replicate p.1.2 []) (step := esymmStep)
    (by fun_prop) (by fun_prop) (by fun_prop) computableInPolyTime_esymmStep
    (fun p _ state => state.length = p.1.2 ∧ ∀ e ∈ state, e.length ≤ p.1.1.length)
    (fun p => by simp) (fun p consumed state value _ h => by
      refine ⟨by rw [length_esymmStep, h.1], fun e he => ?_⟩
      simp only [esymmStep, List.mem_map, List.mem_range] at he
      obtain ⟨j, -, rfl⟩ := he
      simp)
    (size := fun p => p.1.2 * (2 * p.1.1.length + 1)) hsize.polyBounded
    (fun p consumed state _ h => by
      rw [length_encList, ← h.1]
      refine (List.sum_le_length_nsmul _ (2 * p.1.1.length + 1) fun x hx => ?_).trans ?_
      · simp only [List.mem_map] at hx
        obtain ⟨e, he, rfl⟩ := hx
        have := h.2 e he
        simp only [encBits_apply]
        omega
      · simp)).1
  unfold esymmCoords
  exact listGetDWithInput h (by fun_prop) []

/-- The elementary symmetric polynomial in coordinates, as a composition rule. -/
@[fun_prop]
theorem computableInPolyTime_esymmCoords' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {t : α → ℕ} {zs : α → List (List Bool)}
    (htab : ComputableInPolyTime tab input encTable)
    (ht : ComputableInPolyTime t input encUnary)
    (hzs : ComputableInPolyTime zs input (encList encBits)) :
    ComputableInPolyTime (fun x => esymmCoords (tab x) (t x) (zs x)) input encBits := by
  simpa only [Function.comp_def] using
    computableInPolyTime_esymmCoords.comp ((htab.prod ht).prod hzs)

/-- The traces of the basis elements, from the diagonals of the multiplication table. -/
private theorem computableInPolyTime_traceVector :
    ComputableInPolyTime traceVector encTable encBits := by
  unfold traceVector
  fun_prop

/-- The traces of the basis elements, as a composition rule. -/
@[fun_prop]
theorem computableInPolyTime_traceVector' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} (htab : ComputableInPolyTime tab input encTable) :
    ComputableInPolyTime (fun x => traceVector (tab x)) input encBits := by
  simpa only [Function.comp_def] using computableInPolyTime_traceVector.comp htab

/-- The trace as a bit. -/
private theorem computableInPolyTime_traceBit : ComputableInPolyTime
    (fun p : List Bool × List Bool => traceBit p.1 p.2) (encPair encBits encBits) encBool := by
  unfold traceBit
  fun_prop

/-- The trace as a bit, as a composition rule. -/
@[fun_prop]
theorem computableInPolyTime_traceBit' {α : Type} {input : α ↪ List Bool}
    {τ a : α → List Bool} (hτ : ComputableInPolyTime τ input encBits)
    (ha : ComputableInPolyTime a input encBits) :
    ComputableInPolyTime (fun x => traceBit (τ x) (a x)) input encBool := by
  simpa only [Function.comp_def] using computableInPolyTime_traceBit.comp (hτ.prod ha)

/-- **`traceSym 1 r t` in coordinates**, uniformly in the multiplication table, `r` and `t` in
unary, and the input bits. -/
theorem computableInPolyTime_traceSymCoords : ComputableInPolyTime
    (fun p : ((List (List (List Bool)) × ℕ) × ℕ) × List Bool =>
      traceSymCoords p.1.1.1 p.1.1.2 p.1.2 p.2)
    (encPair (encPair (encPair encTable encUnary) encUnary) encBits) encBool := by
  let encP := encPair (encPair (encPair encTable encUnary) encUnary) encBits
  let encQ := encPair encP encUnary
  have htabP : ComputableInPolyTime (fun p => p.1.1.1) encP encTable :=
    (fst _ _).comp ((fst _ _).comp (fst _ _))
  have hrP : ComputableInPolyTime (fun p => p.1.1.2) encP encUnary :=
    (snd _ _).comp ((fst _ _).comp (fst _ _))
  have htP : ComputableInPolyTime (fun p => p.1.2) encP encUnary :=
    (snd _ _).comp (fst _ _)
  have htabQ : ComputableInPolyTime (fun q => q.1.1.1.1) encQ encTable :=
    htabP.comp (fst _ _)
  have hlenQ : ComputableInPolyTime (fun q => q.1.1.1.1.length) encQ encUnary :=
    (length_list (encList encBits)).comp htabQ
  have hxQ : ComputableInPolyTime (fun q => q.1.2) encQ encBits :=
    (snd _ _).comp (fst _ _)
  have hiQ : ComputableInPolyTime (fun q => q.2) encQ encUnary := snd _ _
  have hrQ : ComputableInPolyTime (fun q => q.1.1.1.2) encQ encUnary :=
    hrP.comp (fst _ _)
  unfold traceSymCoords
  refine computableInPolyTime_traceBit' (computableInPolyTime_traceVector' htabP)
    (computableInPolyTime_esymmCoords' htabP htP ?_)
  refine mapWithInput (unary_range' hrP) ?_
  exact computableInPolyTime_powerPred' htabQ
    (bitsTakeWithInput (bitsDropWithInput hxQ (unary_mul.comp (hlenQ.prod hiQ))) hlenQ)
    (unary_sub.comp (hrQ.prod hiQ))

/-! ### The explicit disperser -/

/-- **The explicit affine disperser is computable in polynomial time**: on a bit list `x` of length
`N`, the value `explicitDisperser N x` is computed by a multi-tape machine in time polynomial in
`N`. The certificate charges the whole computation: the parameters, the exhaustive searches for
the irreducible polynomials by trial division, the remainders of the powers of `X`, the
multiplication table, and every field operation of `traceSym 1 r t`. -/
theorem computableInPolyTime_explicitDisperser :
    ComputableInPolyTime
      (fun x : List Bool => explicitDisperser x.length (BitString.ofList x.length x))
      encBits encBool := by
  rw [← funext explicitDisperserProgram_eq]
  unfold explicitDisperserProgram
  simpa only [Function.comp_def] using computableInPolyTime_traceSymCoords.comp
    ((((computableInPolyTime_explicitTable.comp length_bits).prod
      (computableInPolyTime_numBlocks.comp length_bits)).prod
      (computableInPolyTime_symDegree.comp length_bits)).prod id')

/-- **The explicit affine disperser is in `P`**: the bit lists `x` with
`explicitDisperser x.length (BitString.ofList x.length x) = true` form a problem in `P`. -/
theorem setOf_explicitDisperser_mem_P :
    {x : List Bool | explicitDisperser x.length (BitString.ofList x.length x) = true} ∈
      Cslib.Complexity.P encBits :=
  ⟨_, computableInPolyTime_explicitDisperser, fun _ => Iff.rfl⟩

end Cslib.AffineDisperser
