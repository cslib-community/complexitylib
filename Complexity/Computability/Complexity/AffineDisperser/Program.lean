/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.AffineDisperser.BinaryPolynomial
public import Complexity.Computability.Complexity.AffineDisperser.Coordinates
public import Complexity.Foundations.Combinatorics.AffineDisperser.Explicit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD

/-!
# The explicit affine disperser as a computable function

The explicit disperser on `N` bits works in the field `𝔽_{2 ^ n}`, `n = p₁ ⋯ pₖ`, with the monomial
basis `∏ᵢ αᵢ ^ Jᵢ` in roots `αᵢ` of the least-code irreducible polynomials `gᵢ` of the prime
degrees `pᵢ`. Its multiplication table depends only on the `gᵢ`: coordinate `M` of the product of
the monomials `J` and `K` is the product over `i` of the coefficient of `X ^ Mᵢ` in the remainder of
`X ^ (Jᵢ + Kᵢ)` modulo `gᵢ` (`Cslib.prodPowBasis_mul_prodPowBasis`). With the
monomials numbered in the mixed radix `(p₁, …, pₖ)` (`Cslib.AffineDisperser.mixedDigit`), the
table is computed from the remainders of the powers of `X` (`Cslib.AffineDisperser.monomialTable`,
`Cslib.AffineDisperser.isMulTable_monomialTable`), and the polynomials `gᵢ` by exhaustive search
with trial division among the codes below `2 ^ (4 L + 1)`.

The function `Cslib.AffineDisperser.explicitDisperserProgram`, a plain Lean function on bit lists
(not a `FreeM` program), reads `N` from the length of its input, computes the parameters, the
irreducible polynomials, the remainders and the multiplication table, and evaluates
`traceSym 1 r t` in coordinates. It computes the explicit disperser
(`Cslib.AffineDisperser.explicitDisperserProgram_eq`). Since the computation does not involve the
roots, every choice of roots gives the same function
(`Cslib.AffineDisperser.traceSymBits_rootBasis_eq_explicitDisperser`): the root chosen in
`Cslib.AffineDisperser.binaryRoot` does not matter.

## Main definitions

* `Cslib.AffineDisperser.monomialTable`: the multiplication table of a monomial basis.
* `Cslib.AffineDisperser.explicitTable`: the multiplication table of the explicit field.
* `Cslib.AffineDisperser.rootBasis`: the monomial basis in any roots of the irreducible
  polynomials.
* `Cslib.AffineDisperser.explicitDisperserProgram`: the explicit disperser, as a computable
  function on bit lists.

## Main results

* `Cslib.AffineDisperser.isMulTable_monomialTable`: the monomial table is a multiplication table.
* `Cslib.AffineDisperser.traceSymCoords_explicitTable`: the coordinate computation with the
  explicit table is the explicit disperser.
* `Cslib.AffineDisperser.traceSymBits_rootBasis_eq_explicitDisperser`: independence of the roots.
* `Cslib.AffineDisperser.explicitDisperserProgram_eq`: the function computes the explicit
  disperser.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
-/

@[expose] public section

namespace Cslib.AffineDisperser

open Function Module Polynomial Explicit Cslib.BitString

/-! ### The multiplication table of a monomial basis -/

/-- Digit `i` of `u` in the mixed radix `ms`, least significant digit first. -/
def mixedDigit (ms : List ℕ) (u i : ℕ) : ℕ :=
  u / (ms.take i).prod % ms.getD i 0

/-- Coordinate `v` of the product of the monomials `u` and `w` (numbered in the mixed radix `ms`):
the product over the factors `i` of the coefficient of `X ^ vᵢ` in the remainder of
`X ^ (uᵢ + wᵢ)`, read from the table `R i` of remainders of powers. -/
def monomialBit (ms : List ℕ) (R : List (List (List Bool))) (u w v : ℕ) : Bool :=
  (List.range ms.length).all fun i =>
    ((R.getD i []).getD (mixedDigit ms u i + mixedDigit ms w i) []).getD (mixedDigit ms v i) false

/-- The multiplication table of the monomial basis with mixed radix `ms` and tables of remainders
of powers `R`. -/
def monomialTable (ms : List ℕ) (R : List (List (List Bool))) : List (List (List Bool)) :=
  (List.range ms.prod).map fun u => (List.range ms.prod).map fun w =>
    (List.range ms.prod).map fun v => monomialBit ms R u w v

/-- The mixed-radix digits are the components of `finPiFinEquiv.symm`. -/
private theorem mixedDigit_eq (ms : List ℕ) (u : Fin (∏ i, ms.get i)) (i : Fin ms.length) :
    mixedDigit ms u i = (finPiFinEquiv.symm u i : ℕ) := by
  have hprod : ∏ j : Fin i, ms.get (Fin.castLE i.is_lt.le j) = (ms.take i).prod := by
    rw [← List.prod_ofFn]
    congr 1
    apply List.ext_getElem (by simp)
    intro a h1 h2
    simp
  change _ = u / (∏ j : Fin i, ms.get (Fin.castLE i.is_lt.le j)) % ms.get i
  rw [hprod, mixedDigit, List.getD_eq_getElem _ _ i.2]
  rfl

private theorem bitEquiv_symm_all (k : ℕ) (p : ℕ → Bool) :
    bitEquiv.symm ((List.range k).all p) = ∏ i : Fin k, bitEquiv.symm (p i) := by
  by_cases h : (List.range k).all p = true
  · rw [h, bitEquiv_symm_true, eq_comm]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [List.all_eq_true.1 h i (List.mem_range.2 i.2), bitEquiv_symm_true]
  · rw [Bool.not_eq_true] at h
    rw [h, bitEquiv_symm_false, eq_comm]
    obtain ⟨i, hi, hpi⟩ := List.all_eq_false.1 h
    refine Finset.prod_eq_zero (i := ⟨i, List.mem_range.1 hi⟩) (Finset.mem_univ _) ?_
    rw [Bool.not_eq_true] at hpi
    simp [hpi]

private theorem tableEntry_monomialTable {ms : List ℕ} {R : List (List (List Bool))} {u w : ℕ}
    (hu : u < ms.prod) (hw : w < ms.prod) :
    tableEntry (monomialTable ms R) u w = (List.range ms.prod).map (monomialBit ms R u w) := by
  simp [tableEntry, monomialTable, List.getD_eq_getElem?_getD, hu, hw]

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F]

/-- **The monomial table is a multiplication table**: for roots `αᵢ` whose powers `αᵢ ^ e`,
`e < 2 mᵢ`, have the coordinates `R i e` in the power basis, `monomialTable ms R` is the
multiplication table of the monomial basis, numbered by `finPiFinEquiv`. -/
theorem isMulTable_monomialTable (ms : List ℕ) (R : List (List (List Bool)))
    {α : Fin ms.length → F} (hm : Pairwise (Nat.Coprime on ms.get))
    (hE : finrank (ZMod 2) F = ∏ i, ms.get i)
    (hα : ∀ i, (minpoly (ZMod 2) (α i)).natDegree = ms.get i)
    (hR : ∀ i : Fin ms.length, ∀ e < 2 * ms.get i, α i ^ e = ∑ d ∈ Finset.range (ms.get i),
      bitEquiv.symm (((R.getD i []).getD e []).getD d false) • α i ^ d) :
    IsMulTable ((prodPowBasis hm hE hα).reindex finPiFinEquiv) (monomialTable ms R) := by
  refine ⟨by simp [monomialTable], fun u w => ?_⟩
  set c : (i : Fin ms.length) → ℕ → Fin (ms.get i) → ZMod 2 :=
    fun i e d => bitEquiv.symm (((R.getD i []).getD e []).getD d false)
  have hc : ∀ i, ∀ e < 2 * ms.get i, α i ^ e = ∑ d, c i e d • α i ^ (d : ℕ) := fun i e he => by
    rw [hR i e he, Finset.sum_range (fun d => bitEquiv.symm (((R.getD i []).getD e []).getD d false)
      • α i ^ d)]
  rw [Basis.reindex_apply, Basis.reindex_apply, prodPowBasis_mul_prodPowBasis hm hE hα c hc,
    fieldOfBits, ofBits, ← Equiv.sum_comp finPiFinEquiv]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [Basis.reindex_apply, Equiv.symm_apply_apply]
  congr 1
  have hms := Fin.prod_univ_getElem ms
  have hv : (finPiFinEquiv M : ℕ) < ms.prod := (finPiFinEquiv M).2.trans_eq hms
  have hu : (u : ℕ) < ms.prod := u.2.trans_eq hms
  have hw : (w : ℕ) < ms.prod := w.2.trans_eq hms
  rw [tableEntry_monomialTable hu hw, List.getD_eq_getElem _ _ (by simpa using hv),
    List.getElem_map, List.getElem_range, monomialBit, bitEquiv_symm_all]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mixedDigit_eq ms u i, mixedDigit_eq ms w i, mixedDigit_eq ms (finPiFinEquiv M) i,
    Equiv.symm_apply_apply]

/-! ### The explicit field -/

/-- The codes searched for the irreducible polynomials on `N` bits: those below `2 ^ (4 L + 1)`,
which contain the codes of all polynomials of degree at most `4 L`. -/
def codeBound (N : ℕ) : ℕ :=
  2 ^ (4 * primeBound N + 1)

/-- The tables of remainders of powers of `X` modulo the least-code irreducible polynomials of the
prime degrees on `N` bits. -/
def explicitPowerTables (N : ℕ) : List (List (List Bool)) :=
  (degreePrimes N).map fun p => powerTable (leastIrreducibleCode (codeBound N) p).bits

/-- The multiplication table of the monomial basis of the explicit field on `N` bits. -/
def explicitTable (N : ℕ) : List (List (List Bool)) :=
  monomialTable (degreePrimes N) (explicitPowerTables N)

theorem coprime_degreePrime (N : ℕ) : Pairwise (Nat.Coprime on degreePrime N) :=
  fun i j hij => (Nat.coprime_primes (degreePrime_prime N i) (degreePrime_prime N j)).2
    ((degreePrime_injective N).ne hij)

theorem natDegree_minpoly_of_aeval_eq_zero {N : ℕ} {j : Fin (degreePrimes N).length}
    {a : ExplicitField N} (ha : aeval a (leastIrreducible (degreePrime N j)) = 0) :
    (minpoly (ZMod 2) a).natDegree = degreePrime N j := by
  have hp := (degreePrime_prime N j).ne_zero
  rw [← minpoly.eq_of_irreducible_of_monic (irreducible_leastIrreducible _) ha
    (monic_leastIrreducible _), natDegree_leastIrreducible hp]

/-- The monomial basis of `ExplicitField N` in any roots `α j` of the least-code irreducible
polynomials of the prime degrees. -/
noncomputable def rootBasis (N : ℕ) (α : (j : Fin (degreePrimes N).length) → ExplicitField N)
    (hα : ∀ j, aeval (α j) (leastIrreducible (degreePrime N j)) = 0) :
    Basis (ExplicitMonomial N) (ZMod 2) (ExplicitField N) :=
  prodPowBasis (coprime_degreePrime N) (GaloisField.finrank 2 (fieldDegree_ne_zero N))
    fun j => natDegree_minpoly_of_aeval_eq_zero (hα j)

theorem aeval_binaryRoot_degreePrime (N : ℕ) (j : Fin (degreePrimes N).length) :
    aeval (binaryRoot (degreePrime N j) (fieldDegree N)) (leastIrreducible (degreePrime N j)) =
      0 := by
  rw [← minpoly_binaryRoot (degreePrime_prime N j).ne_zero (fieldDegree_ne_zero N)
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))]
  exact minpoly.aeval _ _

/-- The basis of the explicit disperser is the monomial basis in the roots `binaryRoot`. -/
private theorem explicitBasis_eq_rootBasis (N : ℕ) :
    explicitBasis N = rootBasis N (fun j => binaryRoot (degreePrime N j) (fieldDegree N))
      (aeval_binaryRoot_degreePrime N) :=
  rfl

/-- The explicit table is the multiplication table of the monomial basis in any roots. -/
private theorem isMulTable_explicitTable (N : ℕ)
    (α : (j : Fin (degreePrimes N).length) → ExplicitField N)
    (hα : ∀ j, aeval (α j) (leastIrreducible (degreePrime N j)) = 0) :
    IsMulTable ((rootBasis N α hα).reindex finPiFinEquiv) (explicitTable N) := by
  refine isMulTable_monomialTable _ _ _ _ _ fun i e he => ?_
  change e < 2 * degreePrime N i at he
  change _ = ∑ d ∈ Finset.range (degreePrime N i), _
  set p := degreePrime N i
  have hp : p ≠ 0 := (degreePrime_prime N i).ne_zero
  have hpL : p ≤ 4 * primeBound N := (prime_of_mem_degreePrimes (List.get_mem _ i)).2.1
  set code := leastIrreducibleCode (codeBound N) p
  have hcode : polyOfCode code = leastIrreducible p :=
    polyOfCode_leastIrreducibleCode hp (Nat.pow_le_pow_right two_pos (by omega))
  have hcode0 : code ≠ 0 := by
    intro h
    rw [h, polyOfCode_zero] at hcode
    exact (irreducible_leastIrreducible p).ne_zero hcode.symm
  obtain ⟨l, hl⟩ := exists_bits_eq_append_true hcode0
  have hpoly : polyOfBits (l ++ [true]) = leastIrreducible p := by
    rw [← hl, polyOfBits_bits, hcode]
  have hlen : l.length = p := by
    rw [← natDegree_polyOfBits_append_true l, hpoly, natDegree_leastIrreducible hp]
  have hR : (explicitPowerTables N).getD i [] = powerTable (l ++ [true]) := by
    rw [explicitPowerTables, List.getD_eq_getElem _ _ (by simp), List.getElem_map, ← hl]
    rfl
  rw [hR]
  rw [← hlen] at he ⊢
  exact pow_eq_sum_powerTable l (hpoly ▸ hα i) he

/-! ### The computable function -/

omit [FiniteDimensional (ZMod 2) F] in
/-- Reindexing the basis and the reading positions together does not change `traceSymBits`. -/
private theorem traceSymBits_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] {r t N : ℕ} (μ : F)
    (b : Basis ι (ZMod 2) F) (e : ι ≃ ι') (pos : Fin r × ι' → Fin N) (x : BitString N) :
    traceSymBits μ r t (b.reindex e) pos x =
      traceSymBits μ r t b (fun q => pos (q.1, e q.2)) x := by
  have h : readField (b.reindex e) pos x = readField b (fun q => pos (q.1, e q.2)) x := by
    funext i
    rw [readField, readField, ofBits, ofBits, ← Equiv.sum_comp e]
    simp [Basis.reindex_apply]
  rw [traceSymBits, traceSymBits, h]

/-- The coordinate computation with the explicit table is `traceSymBits` in the monomial basis in
any roots `α` of the least-code irreducible polynomials, read on the first `N` bits of `x` (missing
bits are zero). -/
private theorem traceSymCoords_explicitTable_eq_traceSymBits (N : ℕ)
    (α : (j : Fin (degreePrimes N).length) → ExplicitField N)
    (hα : ∀ j, aeval (α j) (leastIrreducible (degreePrime N j)) = 0) (x : List Bool) :
    traceSymCoords (explicitTable N) (numBlocks N) (symDegree N) x =
      traceSymBits (1 : ExplicitField N) (numBlocks N) (symDegree N) (rootBasis N α hα)
        (explicitPos N) (ofList N x) := by
  rw [traceSymCoords_eq (isMulTable_explicitTable N α hα)
    (show 0 < symDegree N from Nat.succ_pos _) (numBlocks_mul_le N),
    traceSymBits_reindex]
  rfl

/-- **The coordinate computation with the explicit table is the explicit disperser** on the first
`N` bits of `x` (missing bits are zero). -/
theorem traceSymCoords_explicitTable (N : ℕ) (x : List Bool) :
    traceSymCoords (explicitTable N) (numBlocks N) (symDegree N) x =
      explicitDisperser N (ofList N x) := by
  rw [traceSymCoords_explicitTable_eq_traceSymBits N _ (aeval_binaryRoot_degreePrime N),
    explicitDisperser, explicitBasis_eq_rootBasis]

/-- **The choice of roots does not matter**: the monomial basis in any roots of the least-code
irreducible polynomials gives the explicit disperser. In particular the root chosen by
`binaryRoot` is immaterial. -/
theorem traceSymBits_rootBasis_eq_explicitDisperser (N : ℕ)
    (α : (j : Fin (degreePrimes N).length) → ExplicitField N)
    (hα : ∀ j, aeval (α j) (leastIrreducible (degreePrime N j)) = 0) :
    traceSymBits (1 : ExplicitField N) (numBlocks N) (symDegree N) (rootBasis N α hα)
      (explicitPos N) = explicitDisperser N := by
  funext x
  rw [← ofList_ofFn x, ← traceSymCoords_explicitTable_eq_traceSymBits N α hα,
    traceSymCoords_explicitTable]

/-- **The explicit disperser as a computable function** on bit lists: the input length `N` fixes
the parameters, and the function finds the irreducible polynomials, builds the multiplication table
and evaluates `traceSym 1 r t` in coordinates. -/
def explicitDisperserProgram (x : List Bool) : Bool :=
  traceSymCoords (explicitTable x.length) (numBlocks x.length) (symDegree x.length) x

/-- **The computable function is the explicit disperser.** -/
theorem explicitDisperserProgram_eq (x : List Bool) :
    explicitDisperserProgram x = explicitDisperser x.length (ofList x.length x) :=
  traceSymCoords_explicitTable _ x

end Cslib.AffineDisperser
