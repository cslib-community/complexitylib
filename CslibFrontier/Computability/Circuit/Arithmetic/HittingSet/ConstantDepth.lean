/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.CircuitLowerBound
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.HardnessToHittingSet
public import CslibFrontier.Foundations.Combinatorics.Design.ReedSolomon
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Bertrand

/-!
# Subexponential hitting sets for constant-depth formulas

Over a field of characteristic zero, for every product-depth `Δ`, exponent `c` and `t ≥ 1`, and
for all sufficiently large `n`, an explicit set of at most `2 ^ (n ^ (1 / t))` points of `Kⁿ`
hits every nonzero polynomial computed by a formula of product-depth at most `Δ` with at most
`n ^ c` nodes (`eventually_isHittingSet_constantDepthHittingSet`,
`eventually_card_constantDepthHittingSet_le`). At the exponent `(c + 2)(2Δ + 1)` it also hits
every nonzero polynomial computed by a simple circuit of product-depth at most `Δ` with at most
`n ^ c` gates (`eventually_isHittingSet_constantDepthHittingSet_circuit`). For a real `ε > 0`
the same holds with `2 ^ (n ^ ε)` points, at `t = ⌈ε⁻¹⌉`
(`eventually_isHittingSet_constantDepthHittingSet_rpow` and its circuit form). This is a finite
form of Corollary 6 of Limaye, Srinivasan and Tavenas [LimayeSrinivasanTavenas2021]: their lower
bound for iterated matrix multiplication, fed into the hardness-to-randomness route of Chou,
Kumar and Solomon [ChouKumarSolomon2019, Theorem 2.3], with the root step of
[BhattacharjeeEtAl2025, Theorem 4.1]; see "Departures from the sources" below.

## Construction

Let `L = ⌊log₂ n⌋`, `ν = 2 ^ ⌊L / 8t⌋`, `δ = ⌊log₂ ⌊log₂ ν⌋⌋` and `m = δ ν²`. The hard
polynomial `f` is `IMM_{ν,δ}` on `m` variables (`immFormula`), multilinear of degree `δ`. The
`n` blocks of the Nisan–Wigderson generator are the graphs, on the first `m` points, of `n`
distinct polynomials of degree less than `8t + 2` over `ZMod q`, `q` the least prime at least
`max m 2` (`ConstantDepthHittingSet.block`, a Reed–Solomon design, `rsDesign`); two blocks meet
in at most `8t + 1` points. The hitting set is `generatorHittingSet f block (n ^ c δ)`, the
values of the generator on the grid `{0, …, n ^ c δ} ^ (m q)`.

## Proof

* **Hitting.** By `isHittingSet_generatorHittingSet_of_hard` it suffices that `f` has no formula
  of product-depth `Δ + 2` with at most `rootCost (n ^ c (2 ^ (8t + 1) (8t + 2) + 2)) δ` nodes.
  Since `n < (2 ν) ^ 8t`, this cost is at most `ν ^ (64 t c + 7)` for large `ν`, and the lower
  bound `SPFormula.eventually_pow_lt_nodeCount_of_imm` at `ν` excludes such formulas; `ν` grows
  with `n`. The blocks are indexed by coefficient vectors, which are distinct once
  `n ≤ q ^ (8t + 2)`, true since `q ≥ ν²`; the restricted graphs themselves need not be
  distinct (there are at most `q ^ m` of them), and only the intersection bound is used.
* **Size.** The set has at most `(n ^ c δ + 1) ^ (m q)` points, with `m q ≤ 6 ν ^ 6` and
  `n ^ c δ + 1 ≤ 2 ^ ((L + 1)(c + 1))`; the exponent `(L + 1)(c + 1) · 6 ν ^ 6` is at most
  `2 ^ ⌊L / t⌋ ≤ n ^ (1 / t)` for large `n`, since `ν ^ 8 ≤ 2 ^ ⌊L / t⌋`.

## Departures from the sources

* [LimayeSrinivasanTavenas2021, Corollary 6] assumes characteristic zero and gives a
  deterministic identity test for circuits of size `s`, depth `Δ = o(log log log n)` and `n`
  variables in time `(s ^ (Δ + 1) n) ^ O(n ^ μ)`; it derives this from
  [ChouKumarSolomon2019, Theorem 2.3] (stated for circuits over `ℚ`, with running time
  `(s n D) ^ O(n ^ (2 ε))` from hardness at depth `Δ + 5`). [BhattacharjeeEtAl2025, Theorem 6.1]
  states the hardness-to-randomness step over fields of characteristic zero or large enough.
* Here: formulas (`SPFormula`) of constant product-depth, and simple circuits
  (`SPCircuit.IsSimple`) through their unfolding into formulas; characteristic zero; and the
  existence and size of an explicit set of points for each `n`, with thresholds "for all large
  `n`" that are not explicit. No running time, uniformity or bit complexity is formalized.
* The exponent is `ε = 1 / t` for a natural number `t ≥ 1` in the main theorems; the corollaries
  `eventually_isHittingSet_constantDepthHittingSet_rpow` and
  `eventually_isHittingSet_constantDepthHittingSet_circuit_rpow` take any real `ε > 0`, with
  `t = ⌈ε⁻¹⌉`.
* The set does not depend on the product-depth `Δ`: one set serves all `Δ`, for `n` large
  enough depending on `Δ`.

## Main definitions

* `Cslib.Circuits.Arithmetic.constantDepthHittingSet`: the hitting set.
* `Cslib.Circuits.Arithmetic.ConstantDepthHittingSet.block`: the blocks of its generator.

## Main results

* `Cslib.Circuits.Arithmetic.eventually_isHittingSet_constantDepthHittingSet`: it hits
  constant-depth formulas of polynomial size.
* `Cslib.Circuits.Arithmetic.eventually_card_constantDepthHittingSet_le`: it has at most
  `2 ^ (n ^ (1 / t))` points.
* `Cslib.Circuits.Arithmetic.eventually_isHittingSet_constantDepthHittingSet_circuit`: it hits
  simple constant-depth circuits of polynomial size.
* `Cslib.Circuits.Arithmetic.eventually_isHittingSet_constantDepthHittingSet_rpow`,
  `Cslib.Circuits.Arithmetic.eventually_isHittingSet_constantDepthHittingSet_circuit_rpow`: both
  properties together, for every real `ε > 0`.

## References

* [N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth algebraic
  circuits*][LimayeSrinivasanTavenas2021], ECCC TR21-081 revision 1, Corollary 6 (printed p. 5)
  and §6, Lemma 18 (printed p. 13)
* [C.-N. Chou, M. Kumar, N. Solomon, *Closure results for polynomial
  factorization*][ChouKumarSolomon2019], Theorem 2.3 (arXiv:1803.05933v1, printed p. 3)
* [S. Bhattacharjee, M. Kumar, S. Rai, V. Ramanathan, R. Saptharishi, S. Saraf, *Closure under
  factorization from a result of Furstenberg*][BhattacharjeeEtAl2025], Theorems 4.1 and 6.1
  (arXiv:2506.23214v1, printed pp. 19–20 and 28; unrefereed preprint)
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

namespace ConstantDepthHittingSet

/-- The size `ν = 2 ^ ⌊⌊log₂ n⌋ / 8t⌋` of the matrices of the hard polynomial. -/
def dim (t n : ℕ) : ℕ :=
  2 ^ (Nat.log 2 n / (8 * t))

/-- `ν` is positive. -/
instance (t n : ℕ) : NeZero (dim t n) :=
  ⟨pow_ne_zero _ two_ne_zero⟩

/-- The number `δ = ⌊log₂ ⌊log₂ ν⌋⌋` of matrices of the hard polynomial. -/
def depth (t n : ℕ) : ℕ :=
  Nat.log 2 (Nat.log 2 (dim t n))

/-- The number `m = δ ν²` of variables of the hard polynomial. -/
abbrev numVars (t n : ℕ) : ℕ :=
  depth t n * (dim t n * dim t n)

/-- The least prime `q` at least `max m 2`: the blocks lie in `Fin m × ZMod q`. -/
def prime (t n : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (max (numVars t n) 2))

/-- `q` is prime. -/
instance (t n : ℕ) : Fact (prime t n).Prime :=
  ⟨(Nat.find_spec (Nat.exists_infinite_primes (max (numVars t n) 2))).2⟩

/-- The coefficients of the polynomial of degree less than `8t + 2` over `ZMod q` of block `i`:
the coefficient vector numbered `i` modulo their number `q ^ (8t + 2)`. -/
noncomputable def coeffs (t n : ℕ) (i : Fin n) : Fin (8 * t + 2) → ZMod (prime t n) :=
  (Fintype.equivFin _).symm
    ⟨i % Fintype.card (Fin (8 * t + 2) → ZMod (prime t n)), Nat.mod_lt _ Fintype.card_pos⟩

/-- The block `i` of the generator: the graph `x ↦ (x, p_i(x))` on the first `m` points of the
polynomial `p_i` with coefficients `coeffs t n i`, a set of the Reed–Solomon design
`rsDesign`. -/
noncomputable def block (t n : ℕ) (i : Fin n) :
    Fin (numVars t n) ↪ Fin (numVars t n) × ZMod (prime t n) :=
  ⟨fun x => (x, ∑ j, coeffs t n i j * ((x : ℕ) : ZMod (prime t n)) ^ (j : ℕ)),
    fun _ _ h => (Prod.ext_iff.1 h).1⟩

end ConstantDepthHittingSet

open ConstantDepthHittingSet in
/-- The **subexponential hitting set for constant-depth formulas**
([LimayeSrinivasanTavenas2021], Corollary 6): the values of the Nisan–Wigderson generator of
`IMM_{ν,δ}` on the Reed–Solomon blocks `ConstantDepthHittingSet.block`, at the points of the grid
`{0, …, n ^ c δ} ^ (m q)`, with `ν = 2 ^ ⌊⌊log₂ n⌋ / 8t⌋`, `δ = ⌊log₂ ⌊log₂ ν⌋⌋`, `m = δ ν²` and
`q` the least prime at least `max m 2`. -/
noncomputable def constantDepthHittingSet (K : Type*) [Field K] (c t n : ℕ) :
    Finset (Fin n → K) :=
  generatorHittingSet (immFormula K (dim t n) (depth t n)).polynomial (block t n)
    (n ^ c * depth t n)

end Cslib.Circuits.Arithmetic

end

public section

namespace Cslib.Circuits.Arithmetic

open Filter Finset MvPolynomial ConstantDepthHittingSet

variable {t n : ℕ}

/-! ### Parameters -/

/-- `n < (2 ν) ^ 8t`. -/
private theorem lt_two_mul_dim_pow (ht : 1 ≤ t) (n : ℕ) : n < (2 * dim t n) ^ (8 * t) := by
  have hL := Nat.lt_mul_div_succ (Nat.log 2 n) (by omega : 0 < 8 * t)
  calc n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self one_lt_two n
    _ ≤ 2 ^ ((Nat.log 2 n / (8 * t) + 1) * (8 * t)) :=
        Nat.pow_le_pow_right two_pos (by rw [mul_comm]; omega)
    _ = (2 * dim t n) ^ (8 * t) := by rw [pow_mul, dim, pow_succ, mul_comm]

/-- `δ + 1 ≤ ν`. -/
private theorem depth_succ_le_dim (t n : ℕ) : depth t n + 1 ≤ dim t n :=
  Nat.succ_le_of_lt ((Nat.log_le_self 2 _).trans_lt (Nat.log_lt_self 2 (NeZero.ne _)))

/-- `⌊log₂ n⌋ / 8t` grows without bound. -/
private theorem tendsto_log_div (ht : 1 ≤ t) :
    Tendsto (fun n => Nat.log 2 n / (8 * t)) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ⟨2 ^ (8 * t * b), fun n hn => ?_⟩
  have hL : 8 * t * b ≤ Nat.log 2 n := Nat.le_log_of_pow_le one_lt_two hn
  exact (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact hL)

/-- `ν` grows without bound. -/
private theorem tendsto_dim (ht : 1 ≤ t) : Tendsto (dim t) atTop atTop :=
  tendsto_atTop_mono (fun _ => Nat.lt_two_pow_self.le) (tendsto_log_div ht)

/-- `max m 2 ≤ q`. -/
private theorem le_prime (t n : ℕ) : max (numVars t n) 2 ≤ prime t n :=
  (Nat.find_spec (Nat.exists_infinite_primes (max (numVars t n) 2))).1

/-- `q ≤ 2 max m 2`, by Bertrand's postulate. -/
private theorem prime_le (t n : ℕ) : prime t n ≤ 2 * max (numVars t n) 2 := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (max (numVars t n) 2 - 1)
    (by omega)
  exact (Nat.find_min' _ ⟨by omega, hp⟩).trans (by omega)

/-! ### The hard polynomial -/

/-- The hard polynomial is multilinear. -/
private theorem degreeOf_immFormula_le (K : Type*) [Field K] (t n : ℕ)
    (v : Fin (numVars t n)) :
    (immFormula K (dim t n) (depth t n)).polynomial.degreeOf v ≤ 1 :=
  (isSetMultilinear_immFormula (K := K) (dim t n)).isSetMultilinear_polynomial.degreeOf_le_one v

/-- The hard polynomial has total degree at most `δ`. -/
private theorem totalDegree_immFormula_le (K : Type*) [Field K] (t n : ℕ) :
    (immFormula K (dim t n) (depth t n)).polynomial.totalDegree ≤ depth t n := by
  have := (isSetMultilinear_immFormula (K := K) (d := depth t n)
    (dim t n)).isSetMultilinear_polynomial.totalDegree_le
  simpa using this

/-! ### Hardness -/

/-- The size bound of the hardness hypothesis is at most `ν ^ (64 t c + 7)` once `ν` is large. -/
private theorem rootCost_le_dim_pow {c B : ℕ} (ht : 1 ≤ t) (hn : 1 ≤ n)
    (hν : 2 ^ 36 * (B + 1) ^ 8 * 2 ^ (64 * t * c) ≤ dim t n) :
    SPFormula.rootCost (n ^ c * B) (depth t n) ≤ dim t n ^ (64 * t * c + 7) := by
  set ν := dim t n
  have hnc : n ^ c ≤ 2 ^ (8 * t * c) * ν ^ (8 * t * c) := by
    rw [← mul_pow, pow_mul]
    exact Nat.pow_le_pow_left (lt_two_mul_dim_pow ht n).le c
  have h1 : 1 ≤ n ^ c := Nat.one_le_pow _ _ hn
  have hs : n ^ c * B + 1 ≤ (B + 1) * (2 ^ (8 * t * c) * ν ^ (8 * t * c)) := by nlinarith
  calc SPFormula.rootCost (n ^ c * B) (depth t n)
      = 2 ^ 36 * (n ^ c * B + 1) ^ 8 * (depth t n + 1) ^ 6 := rfl
    _ ≤ 2 ^ 36 * ((B + 1) * (2 ^ (8 * t * c) * ν ^ (8 * t * c))) ^ 8 * ν ^ 6 := by
        gcongr
        exact depth_succ_le_dim t n
    _ = 2 ^ 36 * (B + 1) ^ 8 * 2 ^ (64 * t * c) * ν ^ (64 * t * c + 6) := by ring
    _ ≤ ν * ν ^ (64 * t * c + 6) := by gcongr
    _ = ν ^ (64 * t * c + 7) := by ring

/-- For large `n`, the hard polynomial has no formula of product-depth `Δ + 2` within the size
bound of the hardness hypothesis. -/
private theorem eventually_rootCost_lt_nodeCount (K : Type*) [Field K] (Δ c B : ℕ)
    (ht : 1 ≤ t) :
    ∀ᶠ n in atTop, ∀ G : SPFormula K (numVars t n),
      G.polynomial = (immFormula K (dim t n) (depth t n)).polynomial →
      G.productDepth ≤ Δ + 2 → SPFormula.rootCost (n ^ c * B) (depth t n) < G.nodeCount := by
  filter_upwards [(tendsto_dim ht).eventually
      (SPFormula.eventually_pow_lt_nodeCount_of_imm K (Δ + 2) (64 * t * c + 7)),
    (tendsto_dim ht).eventually (eventually_ge_atTop (2 ^ 36 * (B + 1) ^ 8 * 2 ^ (64 * t * c))),
    eventually_ge_atTop 1] with n hlb hν hn G hG hGΔ
  refine (rootCost_le_dim_pow ht hn hν).trans_lt ?_
  exact hlb (immVarEquiv (dim t n) (depth t n)) G hGΔ
    (by rw [hG]; exact rename_polynomial_immFormula (K := K) (dim t n))

/-! ### The design -/

/-- The coefficient vectors of distinct blocks are distinct once `n ≤ q ^ (8t + 2)`. -/
private theorem coeffs_injective (h : n ≤ prime t n ^ (8 * t + 2)) :
    Function.Injective (coeffs t n) := by
  intro i j hij
  have hcard : Fintype.card (Fin (8 * t + 2) → ZMod (prime t n)) = prime t n ^ (8 * t + 2) := by
    simp
  have := congrArg Fin.val ((Fintype.equivFin _).symm.injective hij)
  simp only [hcard] at this
  rw [Nat.mod_eq_of_lt (i.2.trans_le h), Nat.mod_eq_of_lt (j.2.trans_le h)] at this
  exact Fin.ext this

/-- Two distinct blocks meet in at most `8t + 1` points once `n ≤ q ^ (8t + 2)`. -/
private theorem card_inter_block_le (h : n ≤ prime t n ^ (8 * t + 2)) {i j : Fin n}
    (hij : i ≠ j) :
    #(univ.map (block t n i) ∩ univ.map (block t n j)) ≤ 8 * t + 1 :=
  (isDesign_rsDesign (k := 8 * t + 2) ((le_max_left _ _).trans (le_prime t n))).2 _ _
    ((coeffs_injective h).ne hij)

/-- For large `n`, `n ≤ q ^ (8t + 2)`. -/
private theorem eventually_le_prime_pow (ht : 1 ≤ t) :
    ∀ᶠ n in atTop, n ≤ prime t n ^ (8 * t + 2) := by
  filter_upwards [(tendsto_dim ht).eventually (eventually_ge_atTop 4)] with n hν
  set ν := dim t n
  have hδ : 1 ≤ depth t n :=
    Nat.le_log_of_pow_le one_lt_two (Nat.le_log_of_pow_le one_lt_two hν)
  have hq : ν * ν ≤ prime t n :=
    le_trans (by nlinarith) ((le_max_left _ _).trans (le_prime t n))
  calc n ≤ (2 * ν) ^ (8 * t) := (lt_two_mul_dim_pow ht n).le
    _ ≤ (ν * ν) ^ (8 * t) := by gcongr; omega
    _ ≤ (ν * ν) ^ (8 * t + 2) := Nat.pow_le_pow_right (by nlinarith) (by omega)
    _ ≤ prime t n ^ (8 * t + 2) := by gcongr

/-! ### Size -/

/-- The hitting set has at most `2 ^ 2 ^ ⌊L / t⌋` points once `48 t (c + 1) (r + 1) ≤ 2 ^ r` for
`r = ⌊L / 8t⌋`. -/
private theorem card_le_two_pow_two_pow (K : Type*) [Field K] (c : ℕ) (ht : 1 ≤ t) (hn : 1 ≤ n)
    (hr : 48 * t * (c + 1) * (Nat.log 2 n / (8 * t) + 1) ≤ 2 ^ (Nat.log 2 n / (8 * t))) :
    #(constantDepthHittingSet K c t n) ≤ 2 ^ 2 ^ (Nat.log 2 n / t) := by
  set L := Nat.log 2 n
  set r := L / (8 * t)
  have hνr : dim t n = 2 ^ r := rfl
  set ν := dim t n
  set δ := depth t n
  set q := prime t n
  have h1 := card_generatorHittingSet_le (immFormula K ν δ).polynomial (block t n) (n ^ c * δ)
  rw [Fintype.card_prod, Fintype.card_fin, ZMod.card] at h1
  -- the grid size
  have hD : n ^ c * δ + 1 ≤ 2 ^ ((L + 1) * (c + 1)) := by
    have hnc : n ^ c ≤ 2 ^ ((L + 1) * c) := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self one_lt_two n).le c
    have hδ : δ + 1 ≤ 2 ^ (L + 1) := by
      refine (depth_succ_le_dim t n).trans (Nat.pow_le_pow_right two_pos ?_)
      exact (Nat.div_le_self _ _).trans (Nat.le_succ _)
    have h1 : 1 ≤ n ^ c := Nat.one_le_pow _ _ hn
    calc n ^ c * δ + 1 ≤ n ^ c * (δ + 1) := by nlinarith
      _ ≤ 2 ^ ((L + 1) * c) * 2 ^ (L + 1) := Nat.mul_le_mul hnc hδ
      _ = 2 ^ ((L + 1) * (c + 1)) := by rw [← pow_add]; ring_nf
  -- the number of seed variables
  have hmq : numVars t n * q ≤ 6 * ν ^ 6 := by
    have hδν : δ ≤ ν := (Nat.le_succ _).trans (depth_succ_le_dim t n)
    have hm : numVars t n ≤ ν ^ 3 := by
      calc numVars t n = δ * (ν * ν) := rfl
        _ ≤ ν * (ν * ν) := Nat.mul_le_mul_right _ hδν
        _ = ν ^ 3 := by ring
    have hν1 : 1 ≤ ν ^ 3 := Nat.one_le_pow _ _ (NeZero.pos ν)
    have hq : q ≤ 6 * ν ^ 3 := by
      have := prime_le t n
      omega
    calc numVars t n * q ≤ ν ^ 3 * (6 * ν ^ 3) := Nat.mul_le_mul hm hq
      _ = 6 * ν ^ 6 := by ring
  -- the exponent
  have hE : (L + 1) * (c + 1) * (numVars t n * q) ≤ 2 ^ (L / t) := by
    have hL1 : L + 1 ≤ 8 * t * (r + 1) := Nat.lt_mul_div_succ L (by omega)
    have h8r : 8 * r ≤ L / t :=
      (Nat.le_div_iff_mul_le (by omega)).2 (by
        calc 8 * r * t = r * (8 * t) := by ring
          _ ≤ L := Nat.div_mul_le_self L (8 * t))
    calc (L + 1) * (c + 1) * (numVars t n * q) ≤ 8 * t * (r + 1) * (c + 1) * (6 * ν ^ 6) := by
          gcongr
      _ = 48 * t * (c + 1) * (r + 1) * 2 ^ (6 * r) := by rw [hνr, ← pow_mul]; ring
      _ ≤ 2 ^ r * 2 ^ (6 * r) := by gcongr
      _ = 2 ^ (7 * r) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (L / t) := Nat.pow_le_pow_right two_pos (by omega)
  calc #(constantDepthHittingSet K c t n) ≤ (n ^ c * δ + 1) ^ (numVars t n * q) := h1
    _ ≤ (2 ^ ((L + 1) * (c + 1))) ^ (numVars t n * q) := Nat.pow_le_pow_left hD _
    _ = 2 ^ ((L + 1) * (c + 1) * (numVars t n * q)) := by rw [← pow_mul]
    _ ≤ 2 ^ 2 ^ (L / t) := Nat.pow_le_pow_right two_pos hE

/-! ### Main results -/

/-- **Subexponential hitting sets for constant-depth formulas** ([LimayeSrinivasanTavenas2021],
Corollary 6, via [ChouKumarSolomon2019], Theorem 2.3): over a field of characteristic zero, for
every product-depth `Δ`, exponent `c` and `t ≥ 1`, for all sufficiently large `n`,
`constantDepthHittingSet K c t n` hits every nonzero polynomial computed by a formula over `K`
in `n` variables of product-depth at most `Δ` with at most `n ^ c` nodes. -/
theorem eventually_isHittingSet_constantDepthHittingSet (K : Type*) [Field K] [CharZero K]
    (Δ c t : ℕ) (ht : 1 ≤ t) :
    ∀ᶠ n in atTop, IsHittingSet (constantDepthHittingSet K c t n)
      {p | ∃ C : SPFormula K n, C.polynomial = p ∧ C.productDepth ≤ Δ ∧ C.nodeCount ≤ n ^ c} := by
  filter_upwards [eventually_rootCost_lt_nodeCount K Δ c (2 ^ (8 * t + 1) * (8 * t + 1 + 1) + 2)
    ht, eventually_le_prime_pow ht] with n hhard hq
  exact isHittingSet_generatorHittingSet_of_hard (degreeOf_immFormula_le K t n)
    (totalDegree_immFormula_le K t n) (fun i j hij => card_inter_block_le hq hij) hhard

/-- **The hitting set is subexponential**: for `t ≥ 1` and all sufficiently large `n`,
`constantDepthHittingSet K c t n` has at most `2 ^ (n ^ (1 / t))` points. -/
theorem eventually_card_constantDepthHittingSet_le (K : Type*) [Field K] (c t : ℕ)
    (ht : 1 ≤ t) :
    ∀ᶠ n in atTop, ((constantDepthHittingSet K c t n).card : ℝ) ≤ 2 ^ ((n : ℝ) ^ (1 / t : ℝ)) := by
  filter_upwards [(tendsto_log_div ht).eventually
      (eventually_mul_sq_le_two_pow (48 * t * (c + 1))), eventually_ge_atTop 1] with n hr hn
  have hcard := card_le_two_pow_two_pow K c ht hn
    ((Nat.mul_le_mul_left _ (Nat.le_self_pow two_ne_zero _)).trans hr)
  have hexp : ((2 ^ (Nat.log 2 n / t) : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / t : ℝ) := by
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have h2L : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    calc ((2 ^ (Nat.log 2 n / t) : ℕ) : ℝ) = (2 : ℝ) ^ ((Nat.log 2 n / t : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]; push_cast; rfl
      _ ≤ (2 : ℝ) ^ ((Nat.log 2 n : ℝ) / t) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two Nat.cast_div_le
      _ = ((2 ^ Nat.log 2 n : ℕ) : ℝ) ^ (1 / t : ℝ) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            mul_one_div]
      _ ≤ (n : ℝ) ^ (1 / t : ℝ) := Real.rpow_le_rpow (by positivity) h2L (by positivity)
  calc ((constantDepthHittingSet K c t n).card : ℝ) ≤ ((2 ^ 2 ^ (Nat.log 2 n / t) : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = (2 : ℝ) ^ (((2 ^ (Nat.log 2 n / t) : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast]; push_cast; rfl
    _ ≤ 2 ^ ((n : ℝ) ^ (1 / t : ℝ)) := Real.rpow_le_rpow_of_exponent_le one_le_two hexp

/-- **Subexponential hitting sets for simple constant-depth circuits**: for every product-depth
`Δ`, exponent `c` and `t ≥ 1`, for all sufficiently large `n`, the hitting set
`constantDepthHittingSet K ((c + 2) (2 Δ + 1)) t n` hits every nonzero polynomial computed by a
simple circuit over `K` with `n` inputs, of product-depth at most `Δ` and at most `n ^ c` gates.
Such a circuit unfolds to a formula of at most `n ^ ((c + 2) (2 Δ + 1))` nodes. -/
theorem eventually_isHittingSet_constantDepthHittingSet_circuit (K : Type*) [Field K]
    [CharZero K] (Δ c t : ℕ) (ht : 1 ≤ t) :
    ∀ᶠ n in atTop, IsHittingSet (constantDepthHittingSet K ((c + 2) * (2 * Δ + 1)) t n)
      {p | ∃ C : SPCircuit K n, C.IsSimple ∧ C.polynomial = p ∧ C.productDepth ≤ Δ ∧
        C.size ≤ n ^ c} := by
  filter_upwards [eventually_isHittingSet_constantDepthHittingSet K Δ ((c + 2) * (2 * Δ + 1)) t
    ht, eventually_ge_atTop 2] with n hH hn
  refine hH.mono subset_rfl ?_
  rintro _ ⟨C, hC, rfl, hCΔ, hs⟩
  refine ⟨C.toSPFormula, SPCircuit.polynomial_toSPFormula C,
    (SPCircuit.productDepth_toSPFormula_le C).trans hCΔ, ?_⟩
  have h1 : 1 ≤ n ^ c := Nat.one_le_pow _ _ (by omega)
  have hbase : C.size + n + 1 ≤ n ^ (c + 2) := by
    have h2 : n + 2 ≤ n ^ 2 := by nlinarith
    have h3 := Nat.mul_le_mul_left (n ^ c) h2
    have h4 := Nat.mul_le_mul_right n h1
    rw [pow_add]
    nlinarith
  calc C.toSPFormula.nodeCount ≤ (C.size + n + 1) ^ (2 * C.productDepth + 1) :=
        SPCircuit.nodeCount_toSPFormula_le hC
    _ ≤ (n ^ (c + 2)) ^ (2 * Δ + 1) :=
        (Nat.pow_le_pow_left hbase _).trans
          (Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by omega)) (by omega))
    _ = n ^ ((c + 2) * (2 * Δ + 1)) := by rw [← pow_mul]

/-- From an exponent `1 / t` to every real exponent `ε ≥ 1 / t`: `n ^ (1 / t) ≤ n ^ ε` for
`n ≥ 1`. -/
private theorem two_rpow_rpow_le {ε : ℝ} {t : ℕ} (ht : 1 / (t : ℝ) ≤ ε) {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx : x ≤ 2 ^ ((n : ℝ) ^ (1 / t : ℝ))) : x ≤ 2 ^ ((n : ℝ) ^ ε) :=
  hx.trans (Real.rpow_le_rpow_of_exponent_le one_le_two
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) ht))

/-- `t = ⌈ε⁻¹⌉` satisfies `1 ≤ t` and `1 / t ≤ ε`. -/
private theorem one_le_ceil_inv_and {ε : ℝ} (hε : 0 < ε) :
    1 ≤ ⌈ε⁻¹⌉₊ ∧ 1 / (⌈ε⁻¹⌉₊ : ℝ) ≤ ε := by
  have hpos : (0 : ℝ) < ⌈ε⁻¹⌉₊ := (inv_pos.2 hε).trans_le (Nat.le_ceil _)
  refine ⟨by exact_mod_cast hpos, ?_⟩
  rw [one_div, inv_le_comm₀ hpos hε]
  exact Nat.le_ceil _

/-- **Subexponential hitting sets for constant-depth formulas, for every `ε > 0`**
([LimayeSrinivasanTavenas2021], Corollary 6, in this finite form): over a field of characteristic
zero, for every product-depth `Δ`, exponent `c` and real `ε > 0`, for all sufficiently large `n`
the explicit set `constantDepthHittingSet K c ⌈ε⁻¹⌉ n` has at most `2 ^ (n ^ ε)` points and hits
every nonzero polynomial computed by a formula over `K` in `n` variables of product-depth at most
`Δ` with at most `n ^ c` nodes. -/
theorem eventually_isHittingSet_constantDepthHittingSet_rpow (K : Type*) [Field K] [CharZero K]
    (Δ c : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      IsHittingSet (constantDepthHittingSet K c ⌈ε⁻¹⌉₊ n)
        {p | ∃ C : SPFormula K n, C.polynomial = p ∧ C.productDepth ≤ Δ ∧ C.nodeCount ≤ n ^ c} ∧
      ((constantDepthHittingSet K c ⌈ε⁻¹⌉₊ n).card : ℝ) ≤ 2 ^ ((n : ℝ) ^ ε) := by
  obtain ⟨ht, htε⟩ := one_le_ceil_inv_and hε
  filter_upwards [eventually_isHittingSet_constantDepthHittingSet K Δ c _ ht,
    eventually_card_constantDepthHittingSet_le K c _ ht, eventually_ge_atTop 1] with n hH hc hn
  exact ⟨hH, two_rpow_rpow_le htε hn hc⟩

/-- **Subexponential hitting sets for simple constant-depth circuits, for every `ε > 0`**: for
every product-depth `Δ`, exponent `c` and real `ε > 0`, for all sufficiently large `n` the
explicit set `constantDepthHittingSet K ((c + 2) (2 Δ + 1)) ⌈ε⁻¹⌉ n` has at most `2 ^ (n ^ ε)`
points and hits every nonzero polynomial computed by a simple circuit over `K` with `n` inputs,
of product-depth at most `Δ` and at most `n ^ c` gates. -/
theorem eventually_isHittingSet_constantDepthHittingSet_circuit_rpow (K : Type*) [Field K]
    [CharZero K] (Δ c : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      IsHittingSet (constantDepthHittingSet K ((c + 2) * (2 * Δ + 1)) ⌈ε⁻¹⌉₊ n)
        {p | ∃ C : SPCircuit K n, C.IsSimple ∧ C.polynomial = p ∧ C.productDepth ≤ Δ ∧
          C.size ≤ n ^ c} ∧
      ((constantDepthHittingSet K ((c + 2) * (2 * Δ + 1)) ⌈ε⁻¹⌉₊ n).card : ℝ) ≤
        2 ^ ((n : ℝ) ^ ε) := by
  obtain ⟨ht, htε⟩ := one_le_ceil_inv_and hε
  filter_upwards [eventually_isHittingSet_constantDepthHittingSet_circuit K Δ c _ ht,
    eventually_card_constantDepthHittingSet_le K ((c + 2) * (2 * Δ + 1)) _ ht,
    eventually_ge_atTop 1] with n hH hc hn
  exact ⟨hH, two_rpow_rpow_le htε hn hc⟩

end Cslib.Circuits.Arithmetic

end
