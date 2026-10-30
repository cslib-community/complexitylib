/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactLog
public import Complexity.Algorithms.WordRAM.Hashing.Tabulation
public import Complexity.Foundations.FieldTheory.Finite.Trinomial
public import Complexity.Probability.KWiseIndependent.Trinomial
import Complexity.Probability.PMF.Map

/-!
# Self-contained Word-RAM `k`-wise independent hashing

This file implements self-contained Word-RAM `k`-wise independent hashing over
`Cslib.WordRAM.Basis.exact` by evaluating degree-`(k - 1)` polynomials over the characteristic-`2`
finite field $\mathbb{F}_{2^{2 \cdot 3^t}} = \mathbb{F}_2[X] / (X^{2 \cdot 3^t} + X^{3^t} + 1)$
(`Cslib.TrinomialField t`, where `t = trinomialStep U M` is chosen at runtime so that
$q = 2 \cdot 3^t \ge \max(\lceil \log_2 \max(U, 2) \rceil, \max(M, 1))$) and projecting to the low
`M` bits (`Cslib.Probability.trinomialPolyHash`). The binary-field polynomial construction and
bit-prefix projection follow [Vadhan, Section 3.5.5, Construction 3.32 / Proposition 3.33 and
Corollary 3.34][Vadhan2012] and [Wegman and Carter][WegmanCarter1981], building on the universal
hashing framework of [Carter and Wegman, pp. 144–145][CarterWegman1979] and finite-field arithmetic
in [Lidl and Niederreiter][LidlNiederreiter1997].

Because `Basis.exact` lacks a hardware carryless-multiplication instruction, `initTableCode k`
precomputes a Four-Russians carryless multiplication table `clmulTab[0 .. 2 ^ (2 * b) - 1]` for
$b$-bit chunks (`b = chunkBits n_max = max 1 (⌊log₂ (max n_max 2)⌋ / 3)`). This table uses at most
$\max(4, n_{\max})$ words for all $n_{\max}$ (`two_pow_two_mul_chunkBits_le`) and satisfies the
sublinear cube bound $(2^{2b})^3 \le n_{\max}^2$, i.e., $2^{2b} \le n_{\max}^{2/3}$, whenever
$n_{\max} \ge 8$ (`two_pow_two_mul_chunkBits_pow_three_le`). Each $q$-bit field multiplication
splits its operands into $L = \lceil q / b \rceil$ limbs of $b$ bits, accumulates the $L \times L$
chunk products from `clmulTab`, and reduces the resulting $< 2^{2q}$ polynomial modulo
$X^{2r} + X^r + 1$ in 8 bit operations (`reduceTrinomialCode`). Under the closed-form bound
`evalSteps n_max U M k = ((11 * L + 12) * L + 30) * k + 19`, each field multiplication takes
$O(L^2)$ instructions, which is $O(1)$ instructions when both $U \le n_{\max}^c$ and
$M \le c \log_2 n_{\max}$ for a fixed constant $c$.

The initialization is factored into two reusable stages:
1. **`initTableCode k`**: deterministically computes $r = 3^t$, $q = 2r$, $b$, masks, and populates
   `clmulTab[0 .. 2 ^ (2 * b) - 1]` in `initTableSteps n_max U M`
   ($= O(n_{\max} + \log U + \log M)$) deterministic instructions from `(base, n_max, U, M)` alone.
2. **`resampleCode k`**: samples the $k$ polynomial coefficients `seed[0 .. k - 1]` uniformly and
   independently in `Fin (2 ^ q)` using $k$ `Code.rand` calls in $5k + 10 = O(k)$ instructions while
   preserving `clmulTab`, so rehashing takes $O(k)$ instructions without rebuilding `clmulTab`.
3. **`initCode k := .seq (initTableCode k) (resampleCode k)`**: full one-shot initialization.
4. **`evalCode k`**: evaluates Horner's rule for `trinomialPolyHash` in `evalSteps n_max U M k`
   ($= O(k \cdot L^2 + 1)$) deterministic instructions, preserving all memory and writing
   `(trinomialPolyHash (trinomialStep U M) k U M c u).val` into `regOut`.

## Main definitions

* `Cslib.Algorithms.WordRAM.Hashing.KWise.chunkBits`,
  `Cslib.Algorithms.WordRAM.Hashing.KWise.limbCount`,
  `Cslib.Algorithms.WordRAM.Hashing.KWise.space`: chunk bit-width, limb count, and memory footprint.
* `Cslib.Algorithms.WordRAM.Hashing.KWise.TableRep`,
  `Cslib.Algorithms.WordRAM.Hashing.KWise.SeedRep`,
  `Cslib.Algorithms.WordRAM.Hashing.KWise.Rep`: memory representation predicates separating the
  deterministic `clmulTab` / header from the $k$ random seed words.
* `Cslib.Algorithms.WordRAM.Hashing.KWise.initTableCode`,
  `Cslib.Algorithms.WordRAM.Hashing.KWise.resampleCode`,
  `Cslib.Algorithms.WordRAM.Hashing.KWise.initCode`,
  `Cslib.Algorithms.WordRAM.Hashing.KWise.evalCode`,
  `Cslib.Algorithms.WordRAM.Hashing.KWise.evalHashOut`: structured Word-RAM programs over
  `Basis.exact` and the induced deterministic hash output map.

## Main results

* `Cslib.Algorithms.WordRAM.Hashing.KWise.two_pow_two_mul_chunkBits_le`,
  `Cslib.Algorithms.WordRAM.Hashing.KWise.two_pow_two_mul_chunkBits_pow_three_le`: coarse
  $\max(4, n_{\max})$ and sublinear $n_{\max}^{2/3}$ bounds on the Four-Russians table size.
* `Cslib.Algorithms.WordRAM.Hashing.KWise.initTableCode_execWithin`: deterministic
  `initTableSteps n_max U M` ($= O(n_{\max} + \log U + \log M)$) table construction establishing
  `TableRep`.
* `Cslib.Algorithms.WordRAM.Hashing.KWise.resampleCode_execRand`,
  `Cslib.Algorithms.WordRAM.Hashing.KWise.map_extractSeeds_eval_resampleComp`,
  `Cslib.Algorithms.WordRAM.Hashing.KWise.resampleCode_execRandWithin`: $(5k + 10)$-step, $k$-query
  seed resampling preserving `TableRep` and inducing `PMF.uniformOfFintype (Fin k → Fin (2 ^ q))`.
* `Cslib.Algorithms.WordRAM.Hashing.KWise.evalCode_execWithin`,
  `Cslib.Algorithms.WordRAM.Hashing.KWise.evalHashOut_eq_trinomialPolyHash`: deterministic
  `evalSteps n_max U M k` ($= O(k \cdot L^2 + 1)$) Horner evaluation matching `trinomialPolyHash`.
* `Cslib.Algorithms.WordRAM.Hashing.KWise.map_evalHashOut_eval_resampleComp`,
  `Cslib.Algorithms.WordRAM.Hashing.KWise.isKWiseIndependentHash_eval`: composed Word-RAM $k$-wise
  independence theorem proving that for every set $T$ of at most $k$ keys, the restricted tuple of
  `evalCode k` outputs after `resampleCode k` is uniformly distributed on $T \to \text{Fin}(2^M)$.

## References

* [S. P. Vadhan, *Pseudorandomness*, Section 3.5.5][Vadhan2012]
* [J. L. Carter and M. N. Wegman, *Universal Classes of Hash Functions*][CarterWegman1979]
* [M. N. Wegman and J. L. Carter, *New Hash Functions and Their Use in Authentication and Set
  Equality*][WegmanCarter1981]
* [R. Lidl and H. Niederreiter, *Finite Fields*][LidlNiederreiter1997]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

public section

namespace Cslib.Algorithms.WordRAM.Hashing.KWise

open Cslib.WordRAM Cslib.Probability
open Cslib.Algorithms.WordRAM.ExactLog
open Cslib.Algorithms.WordRAM.Hashing.Tabulation
open scoped ENNReal

/-! ## Section 1: Parameters, bounds, and memory layout -/

/-- Chunk bit-width `b = max 1 (⌊log₂ (max n_max 2)⌋ / 3)` for Four-Russians carryless
multiplication, ensuring `1 ≤ b` and `2 ^ (2 * b) ≤ max 4 n_max`. -/
@[expose] def chunkBits (n_max : ℕ) : ℕ :=
  max 1 (Nat.log 2 (max n_max 2) / 3)

/-- `chunkBits n_max` is always at least `1`. -/
theorem one_le_chunkBits (n_max : ℕ) : 1 ≤ chunkBits n_max :=
  Nat.le_max_left 1 _

/-- `chunkBits n_max` is always positive. -/
theorem chunkBits_pos (n_max : ℕ) : 0 < chunkBits n_max :=
  one_le_chunkBits n_max

/-- The Four-Russians carryless multiplication table size `2 ^ (2 * chunkBits n_max)` is at most
`max 4 n_max` for all `n_max`. -/
theorem two_pow_two_mul_chunkBits_le (n_max : ℕ) :
    2 ^ (2 * chunkBits n_max) ≤ max 4 n_max := by
  by_cases hdiv : Nat.log 2 (max n_max 2) / 3 ≤ 1
  · have hcb : chunkBits n_max = 1 := by simp [chunkBits]; omega
    rw [hcb]
    exact Nat.le_max_left 4 n_max
  · have hcb : chunkBits n_max = Nat.log 2 (max n_max 2) / 3 := by simp [chunkBits]; omega
    have h2cb : 2 * chunkBits n_max ≤ Nat.log 2 (max n_max 2) := by omega
    calc
      2 ^ (2 * chunkBits n_max) ≤ 2 ^ Nat.log 2 (max n_max 2) :=
        Nat.pow_le_pow_right (by decide) h2cb
      _ ≤ max n_max 2 := Nat.pow_log_le_self 2 (by omega)
      _ ≤ max 4 n_max := by omega

/-- For `8 ≤ n_max`, the Four-Russians table size `2 ^ (2 * chunkBits n_max)` satisfies the
sublinear cube bound `(2 ^ (2 * chunkBits n_max)) ^ 3 ≤ n_max ^ 2` (i.e.,
`2 ^ (2 * chunkBits n_max) ≤ n_max ^ (2 / 3)`). -/
theorem two_pow_two_mul_chunkBits_pow_three_le {n_max : ℕ} (hn : 8 ≤ n_max) :
    (2 ^ (2 * chunkBits n_max)) ^ 3 ≤ n_max ^ 2 := by
  have hmax : max n_max 2 = n_max := Nat.max_eq_left (by omega)
  have hlog3 : 3 ≤ Nat.log 2 n_max :=
    Nat.le_log_of_pow_le (by decide) (by omega)
  have hcb : chunkBits n_max = Nat.log 2 n_max / 3 := by
    simp only [chunkBits, hmax]
    omega
  have hexp : 2 * chunkBits n_max * 3 ≤ Nat.log 2 n_max * 2 := by omega
  calc
    (2 ^ (2 * chunkBits n_max)) ^ 3 = 2 ^ (2 * chunkBits n_max * 3) := (pow_mul 2 _ 3).symm
    _ ≤ 2 ^ (Nat.log 2 n_max * 2) := Nat.pow_le_pow_right (by decide) hexp
    _ = (2 ^ Nat.log 2 n_max) ^ 2 := pow_mul 2 _ 2
    _ ≤ n_max ^ 2 := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) 2

/-- Number of `b`-bit limbs `L = ⌈q / b⌉ = (q + b - 1) / b` needed to cover a `q`-bit field
element. -/
@[expose] def limbCountFromB (b q : ℕ) : ℕ :=
  (q + b - 1) / b

/-- Number of `chunkBits n_max`-bit limbs covering `trinomialDeg U M` bits. -/
@[expose] def limbCount (n_max U M : ℕ) : ℕ :=
  limbCountFromB (chunkBits n_max) (trinomialDeg U M)

/-- When `0 < b`, `limbCountFromB b q * b` is at least `q`. -/
theorem le_limbCountFromB_mul {b : ℕ} (hb : 0 < b) (q : ℕ) :
    q ≤ limbCountFromB b q * b := by
  dsimp only [limbCountFromB]
  have hmod := Nat.div_add_mod (q + b - 1) b
  have hlt : (q + b - 1) % b < b := Nat.mod_lt _ hb
  rw [Nat.mul_comm]
  omega

/-- `limbCount n_max U M * chunkBits n_max` covers all `trinomialDeg U M` bits. -/
theorem trinomialDeg_le_limbCount_mul_chunkBits (n_max U M : ℕ) :
    trinomialDeg U M ≤ limbCount n_max U M * chunkBits n_max :=
  le_limbCountFromB_mul (chunkBits_pos n_max) (trinomialDeg U M)

/-- Memory footprint `8 + k + 2 ^ (2 * b)` words for `k`-wise independent hashing with chunk width
`b`: 8 header words, `k` seed words, and `2 ^ (2 * b)` carryless multiplication table entries. -/
@[expose] def spaceFromB (b k : ℕ) : ℕ :=
  8 + k + 2 ^ (2 * b)

/-- Memory footprint `8 + k + 2 ^ (2 * chunkBits n_max)` words at capacity parameter `n_max`. -/
@[expose] def space (n_max k : ℕ) : ℕ :=
  spaceFromB (chunkBits n_max) k

/-- `space n_max k` is at most `8 + k + max 4 n_max = O(n_max + k)`. -/
theorem space_le (n_max k : ℕ) : space n_max k ≤ 8 + k + max 4 n_max := by
  dsimp only [space, spaceFromB]
  have := two_pow_two_mul_chunkBits_le n_max
  omega

/-- Deterministic table representation predicate `TableRep base b U M k mem`:
stores the 8 header parameters `(r, q, 2 ^ r - 1, 2 ^ q - 1, 2 ^ M - 1, b, 2 ^ b - 1, L)` at
`base + 0 .. base + 7` and the Four-Russians carryless multiplication table
`clmul (idx >>> b) (idx &&& (2 ^ b - 1))` at `base + 8 + k + idx` for `idx < 2 ^ (2 * b)`. -/
@[expose] def TableRep (base b U M k : ℕ) (mem : ℕ → ℕ) : Prop :=
  let r := 3 ^ trinomialStep U M
  let q := trinomialDeg U M
  mem base = r ∧
  mem (base + 1) = q ∧
  mem (base + 2) = 2 ^ r - 1 ∧
  mem (base + 3) = 2 ^ q - 1 ∧
  mem (base + 4) = 2 ^ M - 1 ∧
  mem (base + 5) = b ∧
  mem (base + 6) = 2 ^ b - 1 ∧
  mem (base + 7) = limbCountFromB b q ∧
  ∀ idx < 2 ^ (2 * b),
    mem (base + 8 + k + idx) = clmul (idx >>> b) (idx &&& (2 ^ b - 1))

/-- Seed representation predicate `SeedRep base U M k c mem`: stores the `k` polynomial
coefficients `(c j).val < 2 ^ (trinomialDeg U M)` at `base + 8 + j.val`. -/
@[expose] def SeedRep (base U M k : ℕ)
    (c : Fin k → Fin (2 ^ trinomialDeg U M)) (mem : ℕ → ℕ) : Prop :=
  ∀ j : Fin k, mem (base + 8 + j.val) = (c j).val

/-- Full representation predicate combining `TableRep` and `SeedRep`. -/
@[expose] def Rep (base b U M k : ℕ)
    (c : Fin k → Fin (2 ^ trinomialDeg U M)) (mem : ℕ → ℕ) : Prop :=
  TableRep base b U M k mem ∧ SeedRep base U M k c mem

/-- Extract the `k`-tuple of seeds `Fin k → Fin (2 ^ trinomialDeg U M)` from
`[base + 8, base + 8 + k)`. -/
@[expose] def extractSeeds (base U M k : ℕ) (mem : ℕ → ℕ) :
    Fin k → Fin (2 ^ trinomialDeg U M) :=
  extractSlice (base + 8) (trinomialDeg U M) k mem

/-! ## Section 2: Helper loops for `initTableCode` -/

/-- Final remainder reached by `trinomialStepAux` when repeatedly mapping `B ↦ (B + 2) / 3` until
`≤ 2`. -/
@[expose] def trinomialStepRem (B : ℕ) : ℕ :=
  if B ≤ 2 then B else trinomialStepRem ((B + 2) / 3)
decreasing_by omega

/-- `trinomialStepRem B` is always at most `2`. -/
theorem trinomialStepRem_le_two (B : ℕ) : trinomialStepRem B ≤ 2 := by
  induction B using Nat.strong_induction_on with
  | _ B ih =>
    rw [trinomialStepRem]
    split_ifs with hB
    · exact hB
    · exact ih ((B + 2) / 3) (by omega)

/-- `trinomialStepAux B` is at most `B`. -/
theorem trinomialStepAux_le (B : ℕ) : trinomialStepAux B ≤ B := by
  induction B using Nat.strong_induction_on with
  | _ B ih =>
    rw [trinomialStepAux]
    split_ifs with hB
    · exact Nat.zero_le B
    · have := ih ((B + 2) / 3) (by omega)
      omega

/-- Body of `trinomialStepLoop` on `Data 4` (`reg 0 = rem`, `reg 1 = r`, `reg 2 = 2`,
`reg 3 = 3`): updates `rem ← (rem + 2) / 3` and `r ← r * 3`. -/
@[expose] def trinomialStepBody : Code .exact 4 :=
  .seq (.op (.exactBin .add 0 0 2))
  (.seq (.op (.exactBin .div 0 0 3))
        (.op (.exactBin .mul 1 1 3)))

/-- Loop `while 2 < rem do [ rem ← (rem + 2) / 3; r ← r * 3 ]` computing
`3 ^ trinomialStepAux B`. -/
@[expose] def trinomialStepLoop : Code .exact 4 :=
  .loop (.lt 2 0) trinomialStepBody

/-- Closed-form final state of `trinomialStepLoop`. -/
@[expose] def trinomialStepLoopData (B acc : ℕ) (x : Data 4) : Data 4 :=
  (x.set 0 (trinomialStepRem B)).set 1 (acc * 3 ^ trinomialStepAux B)

/-- `trinomialStepLoop` executes deterministically in `5 * trinomialStepAux B + 2` instructions,
accumulating `acc * 3 ^ trinomialStepAux B` into register `1` and preserving all memory. -/
theorem trinomialStepLoop_exec {w : ℕ} (B : ℕ) {acc : ℕ} {x : Data 4}
    (hrem : x.regs 0 = B) (hacc : x.regs 1 = acc) (htwo : x.regs 2 = 2) (hthree : x.regs 3 = 3)
    (hfit_B2 : Fits w (B + 2)) (hfit_res : Fits w (acc * 3 ^ trinomialStepAux B)) :
    Exec w trinomialStepLoop x (trinomialStepLoopData B acc x)
      (5 * trinomialStepAux B + 2) := by
  induction B using Nat.strong_induction_on generalizing acc x with
  | _ B ih =>
    by_cases hlt : 2 < B
    · have hc : (Cond.lt (2 : Fin 4) 0).Holds x := by
        simp [Cond.Holds, hrem, htwo, hlt]
      have hstep : trinomialStepAux B = trinomialStepAux ((B + 2) / 3) + 1 := by
        rw [trinomialStepAux, ite_eq_right (by omega)]
      have hrem_step : trinomialStepRem B = trinomialStepRem ((B + 2) / 3) := by
        rw [trinomialStepRem, ite_eq_right (by omega)]
      have hmul_eq : (acc * 3) * 3 ^ trinomialStepAux ((B + 2) / 3) =
          acc * 3 ^ trinomialStepAux B := by
        rw [hstep, Nat.pow_succ']
        ring
      have hfit_div2 : Fits w ((B + 2) / 3 + 2) := hfit_B2.of_le (by omega)
      have hfit_div : Fits w ((B + 2) / 3) := hfit_div2.of_le (by omega)
      have hfit_acc3 : Fits w (acc * 3) := by
        have hpos : 1 ≤ 3 ^ trinomialStepAux ((B + 2) / 3) := Nat.one_le_pow _ 3 (by decide)
        have hle : acc * 3 ≤ (acc * 3) * 3 ^ trinomialStepAux ((B + 2) / 3) :=
          Nat.le_mul_of_pos_right _ hpos
        exact hfit_res.of_le (hmul_eq ▸ hle)
      set d1 := x.set 0 (B + 2)
      have s1 : Exec w (.op (.exactBin .add 0 0 2) : Code .exact 4) x d1 1 :=
        exec_exactBin (by simp [hrem, htwo]) hfit_B2
      set d2 := d1.set 0 ((B + 2) / 3)
      have s2 : Exec w (.op (.exactBin .div 0 0 3) : Code .exact 4) d1 d2 1 :=
        exec_exactBin (by simp +decide [d1, hthree]) hfit_div
      set d3 := d2.set 1 (acc * 3)
      have s3 : Exec w (.op (.exactBin .mul 1 1 3) : Code .exact 4) d2 d3 1 :=
        exec_exactBin (by simp +decide [d2, d1, hacc, hthree]) hfit_acc3
      have hrec := ih ((B + 2) / 3) (by omega) (acc := acc * 3) (x := d3)
        (by simp +decide [d3, d2])
        (by simp +decide [d3])
        (by simp +decide [d3, d2, d1, htwo])
        (by simp +decide [d3, d2, d1, hthree])
        hfit_div2
        (by rwa [hmul_eq])
      have hd : trinomialStepLoopData ((B + 2) / 3) (acc * 3) d3 =
          trinomialStepLoopData B acc x := by
        ext i : 2
        · fin_cases i
          · simp +decide [trinomialStepLoopData, d3, d2, d1, hrem_step]
          · simp +decide [trinomialStepLoopData, d3, d2, d1, hmul_eq]
          · simp +decide [trinomialStepLoopData, d3, d2, d1]
          · simp +decide [trinomialStepLoopData, d3, d2, d1]
        · rfl
      rw [hd] at hrec
      have hiter := Exec.loop_iter hc (s1.seq (s2.seq s3)) hrec
      simpa only [trinomialStepLoop, trinomialStepBody, hstep,
        show 1 + (1 + 1) + (5 * trinomialStepAux ((B + 2) / 3) + 2) + 2 =
          5 * (trinomialStepAux ((B + 2) / 3) + 1) + 2 by omega] using hiter
    · have hc : ¬(Cond.lt (2 : Fin 4) 0).Holds x := by
        simp [Cond.Holds, hrem, htwo, hlt]
      have hstep0 : trinomialStepAux B = 0 := by
        rw [trinomialStepAux, ite_eq_left (by omega)]
      have hrem0 : trinomialStepRem B = B := by
        rw [trinomialStepRem, ite_eq_left (by omega)]
      have hd : trinomialStepLoopData B acc x = x := by
        ext i : 2
        · fin_cases i
          · simp +decide [trinomialStepLoopData, hrem0, hrem]
          · simp +decide [trinomialStepLoopData, hstep0, hacc]
          · simp +decide [trinomialStepLoopData]
          · simp +decide [trinomialStepLoopData]
        · rfl
      rw [hd, hstep0]
      exact Exec.loop_exit hc

/-- Bitwise decomposition of `idx < 2 ^ (2 * b)` into high `b`-bit chunk `u = idx >>> b` and low
`b`-bit chunk `v = idx &&& (2 ^ b - 1)`, together with properties of
`prevIdx = (u <<< b) + (v >>> 1)`. -/
private theorem clmulTab_index_props {b idx : ℕ} (hidx : idx < 2 ^ (2 * b)) :
    let u := idx >>> b
    let v := idx &&& (2 ^ b - 1)
    let prevIdx := (u <<< b) + (v >>> 1)
    u < 2 ^ b ∧
    v < 2 ^ b ∧
    (u <<< b) + v = idx ∧
    prevIdx ≤ idx ∧
    (v ≠ 0 → prevIdx < idx) ∧
    (v = 0 → prevIdx = idx) ∧
    prevIdx >>> b = u ∧
    prevIdx &&& (2 ^ b - 1) = v >>> 1 := by
  intro u v prevIdx
  have hpow_pos : 0 < 2 ^ b := Nat.two_pow_pos b
  have hu_eq : u = idx / 2 ^ b := Nat.shiftRight_eq_div_pow idx b
  have hv_eq : v = idx % 2 ^ b := Nat.and_two_pow_sub_one_eq_mod idx b
  have hu_lt : u < 2 ^ b := by
    rw [hu_eq]
    apply Nat.div_lt_of_lt_mul
    rwa [← pow_add, ← two_mul]
  have hv_lt : v < 2 ^ b := by
    rw [hv_eq]
    exact Nat.mod_lt idx hpow_pos
  have huv_eq : (u <<< b) + v = idx := by
    rw [Nat.shiftLeft_eq, hu_eq, hv_eq, Nat.div_add_mod' idx (2 ^ b)]
  have hv_shr : v >>> 1 = v / 2 := Nat.shiftRight_eq_div_pow v 1
  have hv_shr_lt : v >>> 1 < 2 ^ b := by
    rw [hv_shr]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self v 2) hv_lt
  have hprev_eq : prevIdx = u * 2 ^ b + (v >>> 1) := by
    dsimp only [prevIdx]
    rw [Nat.shiftLeft_eq]
  have hprev_le : prevIdx ≤ idx := by
    have : v >>> 1 ≤ v := by rw [hv_shr]; exact Nat.div_le_self v 2
    dsimp only [prevIdx]
    omega
  have hprev_lt : v ≠ 0 → prevIdx < idx := by
    intro hv0
    have : v >>> 1 < v := by rw [hv_shr]; omega
    dsimp only [prevIdx]
    omega
  have hprev_zero : v = 0 → prevIdx = idx := by
    intro hv0
    have : v >>> 1 = 0 := by rw [hv_shr, hv0]
    dsimp only [prevIdx]
    omega
  have hprev_u : prevIdx >>> b = u := by
    rw [Nat.shiftRight_eq_div_pow, hprev_eq, Nat.add_comm,
      Nat.add_mul_div_right _ _ hpow_pos, Nat.div_eq_of_lt hv_shr_lt, zero_add]
  have hprev_v : prevIdx &&& (2 ^ b - 1) = v >>> 1 := by
    rw [Nat.and_two_pow_sub_one_eq_mod, hprev_eq, Nat.add_comm,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv_shr_lt]
  exact ⟨hu_lt, hv_lt, huv_eq, hprev_le, hprev_lt, hprev_zero, hprev_u, hprev_v⟩

/-- Step recurrence for `clmul u v` in `clmulTabBody`:
`((v &&& 1) * u) ^^^ (clmul u (v >>> 1) <<< 1)` equals `clmul u v`. -/
private theorem clmul_eq_bit_mul_xor (u v : ℕ) :
    ((v &&& 1) * u) ^^^ (clmul u (v >>> 1) <<< 1) = clmul u v := by
  rw [clmul_step u v]
  congr 1
  have hand : v &&& 1 = v % 2 := Nat.and_two_pow_sub_one_eq_mod v 1
  rw [hand]
  rcases Nat.mod_two_eq_zero_or_one v with h0 | h1
  · simp [h0]
  · simp [h1]

/-- Body of `clmulTabLoop` on `Data 18` (`reg 0 = tabBase`, `reg 1 = idx`, `reg 2 = tabSize`,
`reg 3 = b`, `reg 4 = 2 ^ b - 1`, `reg 5 = 1`, `reg 6..9` scratch): populates
`mem[tabBase + idx] ← clmul (idx >>> b) (idx &&& (2 ^ b - 1))` using previously filled entry
`prevIdx = ((idx >>> b) <<< b) + ((idx &&& (2 ^ b - 1)) >>> 1)` and increments `idx`. -/
@[expose] def clmulTabBody : Code .exact 18 :=
  .seq (.op (.exactBin .add 6 0 1))
  (.seq (.op (.const 9 0))
  (.seq (.op (.store 6 9))
  (.seq (.op (.exactBin .shiftRight 7 1 3))
  (.seq (.op (.exactBin .and 8 1 4))
  (.seq (.op (.exactBin .shiftRight 9 8 5))
  (.seq (.op (.exactBin .shiftLeft 6 7 3))
  (.seq (.op (.exactBin .add 9 6 9))
  (.seq (.op (.exactBin .add 9 0 9))
  (.seq (.op (.load 9 9))
  (.seq (.op (.exactBin .shiftLeft 9 9 5))
  (.seq (.op (.exactBin .and 8 8 5))
  (.seq (.op (.exactBin .mul 8 8 7))
  (.seq (.op (.exactBin .xor 9 8 9))
  (.seq (.op (.exactBin .add 6 0 1))
  (.seq (.op (.store 6 9))
        (.op (.exactBin .add 1 1 5)))))))))))))))))

/-- Loop `while idx < tabSize do clmulTabBody` populating the Four-Russians carryless
multiplication table `clmulTab[0 .. 2 ^ (2 * b) - 1]`. -/
@[expose] def clmulTabLoop : Code .exact 18 :=
  .loop (.lt 1 2) clmulTabBody

/-- `clmulTabLoop` executes deterministically in `19 * (2 ^ (2 * b) - idx) + 2` instructions,
filling `mem[tabBase + i] = clmul (i >>> b) (i &&& (2 ^ b - 1))` for all `i < 2 ^ (2 * b)` and
preserving `reg 0 = tabBase` and memory outside `[tabBase + idx, tabBase + 2 ^ (2 * b))`. -/
theorem clmulTabLoop_exec {w tabBase b : ℕ}
    (hfit_end : Fits w (tabBase + 2 ^ (2 * b))) :
    ∀ rem idx : ℕ, ∀ x : Data 18,
      idx + rem = 2 ^ (2 * b) →
      x.regs 0 = tabBase →
      x.regs 1 = idx →
      x.regs 2 = 2 ^ (2 * b) →
      x.regs 3 = b →
      x.regs 4 = 2 ^ b - 1 →
      x.regs 5 = 1 →
      (∀ i < idx, x.mem (tabBase + i) = clmul (i >>> b) (i &&& (2 ^ b - 1))) →
      ∃ y : Data 18,
        Exec w clmulTabLoop x y (19 * rem + 2) ∧
        y.regs 0 = tabBase ∧
        (∀ i < 2 ^ (2 * b), y.mem (tabBase + i) = clmul (i >>> b) (i &&& (2 ^ b - 1))) ∧
        (∀ a, (a < tabBase + idx ∨ tabBase + 2 ^ (2 * b) ≤ a) → y.mem a = x.mem a) := by
  intro rem
  induction rem with
  | zero =>
    intro idx x hsum h0 h1 h2 _ _ _ hinv
    have hidx_eq : idx = 2 ^ (2 * b) := by omega
    have hc : ¬(Cond.lt (1 : Fin 18) 2).Holds x := by
      simp [Cond.Holds, h1, h2, hidx_eq]
    refine ⟨x, Exec.loop_exit hc, h0, ?_, fun _ _ => rfl⟩
    intro i hi
    exact hinv i (hidx_eq ▸ hi)
  | succ rem ih =>
    intro idx x hsum h0 h1 h2 h3 h4 h5 hinv
    have hidx_lt : idx < 2 ^ (2 * b) := by omega
    have hc : (Cond.lt (1 : Fin 18) 2).Holds x := by
      simp [Cond.Holds, h1, h2, hidx_lt]
    obtain ⟨hu_lt, hv_lt, huv_eq, hprev_le, hprev_lt, hprev_zero, hprev_u, hprev_v⟩ :=
      clmulTab_index_props hidx_lt
    set u := idx >>> b
    set v := idx &&& (2 ^ b - 1)
    set prevIdx := (u <<< b) + (v >>> 1)
    have hpow_le : 2 ^ b ≤ 2 ^ (2 * b) := Nat.pow_le_pow_right (by decide) (by omega)
    have hfit_idx : Fits w idx := hfit_end.of_le (by omega)
    have hfit_addr : Fits w (tabBase + idx) := hfit_end.of_le (by omega)
    have hfit_0 : Fits w 0 := hfit_end.of_le (Nat.zero_le _)
    have hfit_u : Fits w u := hfit_end.of_le (by omega)
    have hfit_v : Fits w v := hfit_end.of_le (by omega)
    have hfit_vshr : Fits w (v >>> 1) := hfit_v.of_le (Nat.shiftRight_le v 1)
    have hfit_ushl : Fits w (u <<< b) := hfit_idx.of_le (by omega)
    have hfit_prev : Fits w prevIdx := hfit_idx.of_le hprev_le
    have hfit_prevAddr : Fits w (tabBase + prevIdx) := hfit_addr.of_le (by omega)
    have hprev_val_lt : clmul u (v >>> 1) < 2 ^ (2 * b - 1) := by
      by_cases hb0 : b = 0
      · subst hb0
        have hu0 : u = 0 := by omega
        simp [hu0]
      · have hv_shr_lt : v >>> 1 < 2 ^ (b - 1) := by
          rw [Nat.shiftRight_eq_div_pow, pow_one]
          apply Nat.div_lt_of_lt_mul
          rwa [← pow_succ', Nat.sub_add_cancel (by omega)]
        have hlt := clmul_lt_two_pow hu_lt hv_shr_lt
        rwa [show b + (b - 1) = 2 * b - 1 by omega] at hlt
    have hsh_lt : clmul u (v >>> 1) <<< 1 < 2 ^ (2 * b) := by
      by_cases hb0 : b = 0
      · subst hb0
        have hu0 : u = 0 := by omega
        simp [hu0]
      · rw [Nat.shiftLeft_eq, pow_one]
        have hpow_split : 2 ^ (2 * b) = 2 ^ (2 * b - 1) * 2 := by
          conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ 2 * b by omega), pow_succ]
        omega
    have hfit_sh : Fits w (clmul u (v >>> 1) <<< 1) := hfit_end.of_le (by omega)
    have hfit_vbit : Fits w (v &&& 1) := hfit_v.of_le Nat.and_le_left
    have hbit_le : (v &&& 1) * u ≤ u := by
      calc (v &&& 1) * u ≤ 1 * u := Nat.mul_le_mul_right u Nat.and_le_right
        _ = u := Nat.one_mul u
    have hfit_term : Fits w ((v &&& 1) * u) := hfit_u.of_le hbit_le
    have hval_lt : clmul u v < 2 ^ (2 * b) := clmul_lt_two_pow_two_mul hu_lt hv_lt
    have hfit_val : Fits w (clmul u v) := hfit_end.of_le (by omega)
    have hfit_idx1 : Fits w (idx + 1) := hfit_end.of_le (by omega)
    set s1 := x.set 6 (tabBase + idx)
    have e1 : Exec w (.op (.exactBin .add 6 0 1) : Code .exact 18) x s1 1 :=
      exec_exactBin (by simp [h0, h1]) hfit_addr
    set s2 := s1.set 9 0
    have e2 : Exec w (.op (.const 9 0) : Code .exact 18) s1 s2 1 := Exec.const hfit_0
    set s3 := s2.write (tabBase + idx) 0
    have e3 : Exec w (.op (.store 6 9) : Code .exact 18) s2 s3 1 := by
      simpa +decide [s3, s2, s1] using
        (Exec.store (B := .exact) (w := w) (a := 6) (s := 9) (x := s2))
    have hprev_mem : s3.mem (tabBase + prevIdx) = clmul u (v >>> 1) := by
      dsimp only [s3, s2, s1, Data.write, Data.set]
      by_cases hv0 : v = 0
      · have hpeq : prevIdx = idx := hprev_zero hv0
        have hv_shr0 : v >>> 1 = 0 := by rw [hv0]; rfl
        simp [hpeq, hv_shr0]
      · have hplt : prevIdx < idx := hprev_lt hv0
        have hne : tabBase + prevIdx ≠ tabBase + idx := by omega
        rw [Function.update_of_ne hne, hinv prevIdx hplt, hprev_u, hprev_v]
    set s4 := s3.set 7 u
    have e4 : Exec w (.op (.exactBin .shiftRight 7 1 3) : Code .exact 18) s3 s4 1 :=
      exec_exactBin (by simp +decide [s3, s2, s1, h1, h3, u]) hfit_u
    set s5 := s4.set 8 v
    have e5 : Exec w (.op (.exactBin .and 8 1 4) : Code .exact 18) s4 s5 1 :=
      exec_exactBin (by simp +decide [s4, s3, s2, s1, h1, h4, v]) hfit_v
    set s6 := s5.set 9 (v >>> 1)
    have e6 : Exec w (.op (.exactBin .shiftRight 9 8 5) : Code .exact 18) s5 s6 1 :=
      exec_exactBin (by simp +decide [s5, s4, s3, s2, s1, h5]) hfit_vshr
    set s7 := s6.set 6 (u <<< b)
    have e7 : Exec w (.op (.exactBin .shiftLeft 6 7 3) : Code .exact 18) s6 s7 1 :=
      exec_exactBin (by simp +decide [s6, s5, s4, s3, s2, s1, h3]) hfit_ushl
    set s8 := s7.set 9 prevIdx
    have e8 : Exec w (.op (.exactBin .add 9 6 9) : Code .exact 18) s7 s8 1 :=
      exec_exactBin (by simp +decide [s7, s6, prevIdx]) hfit_prev
    set s9 := s8.set 9 (tabBase + prevIdx)
    have e9 : Exec w (.op (.exactBin .add 9 0 9) : Code .exact 18) s8 s9 1 :=
      exec_exactBin (by simp +decide [s8, s7, s6, s5, s4, s3, s2, s1, h0]) hfit_prevAddr
    set s10 := s9.set 9 (clmul u (v >>> 1))
    have e10 : Exec w (.op (.load 9 9) : Code .exact 18) s9 s10 1 := by
      simpa +decide [s10, s9, s8, s7, s6, s5, s4, hprev_mem] using
        (Exec.load (B := .exact) (w := w) (d := 9) (a := 9) (x := s9))
    set s11 := s10.set 9 (clmul u (v >>> 1) <<< 1)
    have e11 : Exec w (.op (.exactBin .shiftLeft 9 9 5) : Code .exact 18) s10 s11 1 :=
      exec_exactBin (by simp +decide [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h5]) hfit_sh
    set s12 := s11.set 8 (v &&& 1)
    have e12 : Exec w (.op (.exactBin .and 8 8 5) : Code .exact 18) s11 s12 1 :=
      exec_exactBin (by simp +decide [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h5]) hfit_vbit
    set s13 := s12.set 8 ((v &&& 1) * u)
    have e13 : Exec w (.op (.exactBin .mul 8 8 7) : Code .exact 18) s12 s13 1 :=
      exec_exactBin (by simp +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4]) hfit_term
    have hxor_eq : s13.regs 8 ^^^ s13.regs 9 = clmul u v := by
      simpa +decide [s13, s12, s11] using clmul_eq_bit_mul_xor u v
    set s14 := s13.set 9 (clmul u v)
    have e14 : Exec w (.op (.exactBin .xor 9 8 9) : Code .exact 18) s13 s14 1 :=
      exec_exactBin (by simp [hxor_eq]) hfit_val
    set s15 := s14.set 6 (tabBase + idx)
    have e15 : Exec w (.op (.exactBin .add 6 0 1) : Code .exact 18) s14 s15 1 :=
      exec_exactBin
        (by simp +decide [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0, h1])
        hfit_addr
    set s16 := s15.write (tabBase + idx) (clmul u v)
    have e16 : Exec w (.op (.store 6 9) : Code .exact 18) s15 s16 1 := by
      simpa +decide [s16, s15, s14] using
        (Exec.store (B := .exact) (w := w) (a := 6) (s := 9) (x := s15))
    set s17 := s16.set 1 (idx + 1)
    have e17 : Exec w (.op (.exactBin .add 1 1 5) : Code .exact 18) s16 s17 1 :=
      exec_exactBin
        (by simp +decide [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
          h1, h5])
        hfit_idx1
    have hbody :=
      e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq (e10.seq
        (e11.seq (e12.seq (e13.seq (e14.seq (e15.seq (e16.seq e17)))))))))))))))
    have hs17_mem : s17.mem = Function.update x.mem (tabBase + idx) (clmul u v) := by
      dsimp only [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
        Data.write, Data.set]
      rw [Function.update_idem]
    have hinv' : ∀ i < idx + 1, s17.mem (tabBase + i) = clmul (i >>> b) (i &&& (2 ^ b - 1)) := by
      intro i hi
      rw [hs17_mem]
      rcases eq_or_ne i idx with rfl | hne
      · simp [u, v]
      · have hilt : i < idx := by omega
        rw [Function.update_of_ne (by omega)]
        exact hinv i hilt
    have hs17_0 : s17.regs 0 = tabBase := by
      simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0]
    have hs17_1 : s17.regs 1 = idx + 1 := by simp +decide [s17]
    have hs17_2 : s17.regs 2 = 2 ^ (2 * b) := by
      simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h2]
    have hs17_3 : s17.regs 3 = b := by
      simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h3]
    have hs17_4 : s17.regs 4 = 2 ^ b - 1 := by
      simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h4]
    have hs17_5 : s17.regs 5 = 1 := by
      simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h5]
    obtain ⟨y, hrec, hy0, hytab, hyout⟩ :=
      ih (idx + 1) s17 (by omega) hs17_0 hs17_1 hs17_2 hs17_3 hs17_4 hs17_5 hinv'
    have hiter := Exec.loop_iter hc hbody hrec
    refine ⟨y, ?_, hy0, hytab, ?_⟩
    · simpa only [clmulTabLoop, clmulTabBody,
        show 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 +
          (1 + (1 + (1 + (1 + (1 + 1))))))))))))))) + (19 * rem + 2) + 2 =
            19 * (rem + 1) + 2 by omega] using hiter
    · intro a ha
      have ha' : a < tabBase + (idx + 1) ∨ tabBase + 2 ^ (2 * b) ≤ a := by omega
      have hne : a ≠ tabBase + idx := by omega
      rw [hyout a ha', hs17_mem, Function.update_of_ne hne]

/-! ## Section 3: Table construction (`initTableCode`) and seed resampling (`resampleCode`) -/

/-- Register `0`: holds the base memory address `base`. -/
abbrev regBase : Fin 18 := 0

/-- Register `1`: holds `n_max` on entry to `initTableCode` (and `key` on entry to `evalCode`). -/
abbrev regNMax : Fin 18 := 1

/-- Register `2`: holds `U` on entry to `initTableCode` (and output in `evalCode`). -/
abbrev regU : Fin 18 := 2

/-- Register `3`: holds `M` on entry to `initTableCode`. -/
abbrev regM : Fin 18 := 3

/-- Subprogram on `Data 18` computing `chunkBits n_max` into register `5` and `1` into register `6`
from `n_max` in register `1`, while preserving registers `0, 1, 2, 3` and memory. -/
@[expose] def chunkBitsCode : Code .exact 18 :=
  .seq (.op (.const 4 2))
  (.seq (maxCode 4 1 4)
  (.seq (.op (.const 5 0))
  (.seq (.op (.const 6 1))
  (.seq (log2Loop.rename ![4, 5, 6])
  (.seq (.op (.const 4 3))
  (.seq (.op (.exactBin .div 5 5 4))
        (maxCode 5 6 5)))))))

/-- `chunkBitsCode` executes deterministically in `4 * Nat.log 2 (max n_max 2) + 13` steps. -/
theorem chunkBitsCode_exec {w base n_max U M : ℕ} {x : Data 18}
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = n_max) (h2 : x.regs 2 = U) (h3 : x.regs 3 = M)
    (hfit_n : Fits w (max n_max 2)) (hfit_3 : Fits w 3) :
    ∃ y : Data 18,
      Exec w chunkBitsCode x y (4 * Nat.log 2 (max n_max 2) + 13) ∧
      y.regs 0 = base ∧
      y.regs 2 = U ∧
      y.regs 3 = M ∧
      y.regs 5 = chunkBits n_max ∧
      y.regs 6 = 1 ∧
      y.mem = x.mem := by
  have hfit_2 : Fits w 2 := hfit_3.of_le (by decide)
  have hfit_1 : Fits w 1 := hfit_3.of_le (by decide)
  have hfit_0 : Fits w 0 := hfit_3.of_le (by decide)
  have hlog_le : Nat.log 2 (max n_max 2) ≤ max n_max 2 := Nat.log_le_self 2 _
  have hfit_log : Fits w (0 + Nat.log 2 (max n_max 2)) := hfit_n.of_le (by omega)
  have hfit_div : Fits w (Nat.log 2 (max n_max 2) / 3) := hfit_n.of_le (by omega)
  set s1 := x.set 4 2
  have e1 : Exec w (.op (.const 4 2) : Code .exact 18) x s1 1 := Exec.const hfit_2
  set s2 := s1.set 4 (max n_max 2)
  have e2 : Exec w (maxCode 4 1 4) s1 s2 3 := by
    simpa +decide [s2, s1, h1] using maxCode_exec (w := w) 4 1 4 s1
  set s3 := s2.set 5 0
  have e3 : Exec w (.op (.const 5 0) : Code .exact 18) s2 s3 1 := Exec.const hfit_0
  set s4 := s3.set 6 1
  have e4 : Exec w (.op (.const 6 1) : Code .exact 18) s3 s4 1 := Exec.const hfit_1
  set f : Fin 3 → Fin 18 := ![4, 5, 6]
  have hmap_inj : Function.Injective f := by decide
  have hloop_inner := log2Loop_exec (w := w) (max n_max 2) (acc := 0)
    (x := s4.comap f)
    (by simp +decide [s4, s3, s2, f, Data.comap])
    (by simp +decide [s4, s3, f, Data.comap])
    (by simp +decide [s4, f, Data.comap])
    hfit_n hfit_log
  have e5 := hloop_inner.rename hmap_inj
  set s5 := (log2LoopData (max n_max 2) 0 (s4.comap f)).extend f s4
  have hs5_5 : s5.regs 5 = Nat.log 2 (max n_max 2) := by
    change (s5.comap f).regs 1 = Nat.log 2 (max n_max 2)
    rw [Data.comap_extend hmap_inj]
    simp +decide [log2LoopData, s4, s3, s2, s1, f, Data.comap]
  have hs5_6 : s5.regs 6 = 1 := by
    change (s5.comap f).regs 2 = 1
    rw [Data.comap_extend hmap_inj]
    simp +decide [log2LoopData, s4, s3, s2, s1, f, Data.comap]
  have hs5_0 : s5.regs 0 = base := by
    simp +decide [s5, Data.extend, f, s4, s3, s2, s1, h0]
  have hs5_2 : s5.regs 2 = U := by
    simp +decide [s5, Data.extend, f, s4, s3, s2, s1, h2]
  have hs5_3 : s5.regs 3 = M := by
    simp +decide [s5, Data.extend, f, s4, s3, s2, s1, h3]
  set s6 := s5.set 4 3
  have e6 : Exec w (.op (.const 4 3) : Code .exact 18) s5 s6 1 := Exec.const hfit_3
  set s7 := s6.set 5 (Nat.log 2 (max n_max 2) / 3)
  have e7 : Exec w (.op (.exactBin .div 5 5 4) : Code .exact 18) s6 s7 1 :=
    exec_exactBin (by simp +decide [s6, hs5_5]) hfit_div
  set s8 := s7.set 5 (chunkBits n_max)
  have e8 : Exec w (maxCode 5 6 5) s7 s8 3 := by
    simpa +decide [s8, s7, s6, hs5_6, chunkBits] using maxCode_exec (w := w) 5 6 5 s7
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))
  refine ⟨s8, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [chunkBitsCode, f,
      show 1 + (3 + (1 + (1 + (4 * Nat.log 2 (max n_max 2) + 2 + (1 + (1 + 3)))))) =
        4 * Nat.log 2 (max n_max 2) + 13 by omega] using hall
  · simp +decide [s8, s7, s6, hs5_0]
  · simp +decide [s8, s7, s6, hs5_2]
  · simp +decide [s8, s7, s6, hs5_3]
  · simp +decide [s8]
  · simp +decide [s8, s7, s6, hs5_6]
  · rfl

private theorem add_two_le_two_pow {q : ℕ} (hq : 2 ≤ q) : q + 2 ≤ 2 ^ q := by
  induction q with
  | zero => omega
  | succ n ih =>
    rcases (by omega : n < 2 ∨ 2 ≤ n) with hlt | hge
    · have hn1 : n = 1 := by omega
      subst hn1
      decide
    · have hrec := ih hge
      have hpos : 2 ≤ 2 ^ n :=
        calc 2 = 2 ^ 1 := by decide
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      rw [pow_succ]
      omega

/-- Subprogram on `Data 18` computing `r = 3 ^ trinomialStep U M` into register `1`,
`q = trinomialDeg U M` into register `2`, and `2` into register `4` from `U` in register `2`,
`M` in register `3`, and `1` in register `6`, while preserving `reg 0 = base`, `reg 3 = M`,
`reg 5 = b`, `reg 6 = 1`, and memory. -/
@[expose] def trinomialParamsCode : Code .exact 18 :=
  .seq (.op (.const 4 2))
  (.seq (maxCode 7 2 4)
  (.seq (.op (.const 8 0))
  (.seq (clog2Loop.rename ![7, 8, 6])
  (.seq (maxCode 7 3 6)
  (.seq (maxCode 7 8 7)
  (.seq (.op (.const 1 1))
  (.seq (.op (.const 8 3))
  (.seq (trinomialStepLoop.rename ![7, 1, 4, 8])
        (.op (.exactBin .mul 2 4 1))))))))))

/-- `trinomialParamsCode` executes deterministically in
`5 * Nat.clog 2 (max U 2) + 5 * trinomialStep U M + 18` steps. -/
theorem trinomialParamsCode_exec {w base U M b : ℕ} {x : Data 18}
    (h0 : x.regs 0 = base) (h2 : x.regs 2 = U) (h3 : x.regs 3 = M)
    (h5 : x.regs 5 = b) (h6 : x.regs 6 = 1)
    (hfit_U : Fits w (max U 2 + 1)) (hfit_q : Fits w (2 ^ trinomialDeg U M)) :
    ∃ y : Data 18,
      Exec w trinomialParamsCode x y
        (5 * Nat.clog 2 (max U 2) + 5 * trinomialStep U M + 18) ∧
      y.regs 0 = base ∧
      y.regs 1 = 3 ^ trinomialStep U M ∧
      y.regs 2 = trinomialDeg U M ∧
      y.regs 3 = M ∧
      y.regs 4 = 2 ∧
      y.regs 5 = b ∧
      y.regs 6 = 1 ∧
      y.mem = x.mem := by
  set B := trinomialTargetBits U M
  have hB_le_q : B ≤ trinomialDeg U M := trinomialTargetBits_le_trinomialDeg U M
  have hq_ge_2 : 2 ≤ trinomialDeg U M := by
    dsimp only [trinomialDeg]
    have : 1 ≤ 3 ^ trinomialStep U M := Nat.one_le_pow _ 3 (by decide)
    omega
  have hpow_q : trinomialDeg U M + 2 ≤ 2 ^ trinomialDeg U M := add_two_le_two_pow hq_ge_2
  have hfit_q2 : Fits w (trinomialDeg U M + 2) := hfit_q.of_le hpow_q
  have hfit_B2 : Fits w (B + 2) := hfit_q2.of_le (by omega)
  have hclog_le_B : Nat.clog 2 (max U 2) ≤ B := le_max_left _ _
  have hfit_clog : Fits w (0 + Nat.clog 2 (max U 2)) := hfit_B2.of_le (by omega)
  have hr_le_q : 3 ^ trinomialStepAux B ≤ trinomialDeg U M := by
    change 3 ^ trinomialStep U M ≤ 2 * 3 ^ trinomialStep U M
    omega
  have hfit_r : Fits w (1 * 3 ^ trinomialStepAux B) := by
    rw [Nat.one_mul]
    exact hfit_q2.of_le (by omega)
  have hfit_q_val : Fits w (trinomialDeg U M) := hfit_q2.of_le (by omega)
  have hfit_3 : Fits w 3 := hfit_q2.of_le (by omega)
  have hfit_2 : Fits w 2 := hfit_q2.of_le (by omega)
  have hfit_1 : Fits w 1 := hfit_q2.of_le (by omega)
  have hfit_0 : Fits w 0 := hfit_q2.of_le (by omega)
  set s1 := x.set 4 2
  have e1 : Exec w (.op (.const 4 2) : Code .exact 18) x s1 1 := Exec.const hfit_2
  set s2 := s1.set 7 (max U 2)
  have e2 : Exec w (maxCode 7 2 4) s1 s2 3 := by
    simpa +decide [s2, s1, h2] using maxCode_exec (w := w) 7 2 4 s1
  set s3 := s2.set 8 0
  have e3 : Exec w (.op (.const 8 0) : Code .exact 18) s2 s3 1 := Exec.const hfit_0
  set f1 : Fin 3 → Fin 18 := ![7, 8, 6]
  have hmap1 : Function.Injective f1 := by decide
  have hclog_inner := clog2Loop_exec (w := w) (max U 2) (acc := 0)
    (x := s3.comap f1)
    (by simp +decide [s3, s2, f1, Data.comap])
    (by simp +decide [s3, f1, Data.comap])
    (by simp +decide [s3, s2, s1, h6, f1, Data.comap])
    hfit_U hfit_clog
  have e4 := hclog_inner.rename hmap1
  set s4 := (clog2LoopData (max U 2) 0 (s3.comap f1)).extend f1 s3
  have hs4_8 : s4.regs 8 = Nat.clog 2 (max U 2) := by
    change (s4.comap f1).regs 1 = Nat.clog 2 (max U 2)
    rw [Data.comap_extend hmap1]
    simp +decide [clog2LoopData, s3, s2, s1, f1, Data.comap]
  have hs4_6 : s4.regs 6 = 1 := by
    change (s4.comap f1).regs 2 = 1
    rw [Data.comap_extend hmap1]
    simp +decide [clog2LoopData, s3, s2, s1, h6, f1, Data.comap]
  have hs4_0 : s4.regs 0 = base := by
    simp +decide [s4, Data.extend, f1, s3, s2, s1, h0]
  have hs4_3 : s4.regs 3 = M := by
    simp +decide [s4, Data.extend, f1, s3, s2, s1, h3]
  have hs4_4 : s4.regs 4 = 2 := by
    simp +decide [s4, Data.extend, f1, s3, s2, s1]
  have hs4_5 : s4.regs 5 = b := by
    simp +decide [s4, Data.extend, f1, s3, s2, s1, h5]
  set s5 := s4.set 7 (max M 1)
  have e5 : Exec w (maxCode 7 3 6) s4 s5 3 := by
    simpa +decide [s5, hs4_3, hs4_6] using maxCode_exec (w := w) 7 3 6 s4
  set s6 := s5.set 7 B
  have e6 : Exec w (maxCode 7 8 7) s5 s6 3 := by
    simpa +decide [s6, s5, hs4_8, B, trinomialTargetBits] using maxCode_exec (w := w) 7 8 7 s5
  set s7 := s6.set 1 1
  have e7 : Exec w (.op (.const 1 1) : Code .exact 18) s6 s7 1 := Exec.const hfit_1
  set s8 := s7.set 8 3
  have e8 : Exec w (.op (.const 8 3) : Code .exact 18) s7 s8 1 := Exec.const hfit_3
  set f2 : Fin 4 → Fin 18 := ![7, 1, 4, 8]
  have hmap2 : Function.Injective f2 := by decide
  have hstep_inner := trinomialStepLoop_exec (w := w) B (acc := 1)
    (x := s8.comap f2)
    (by simp +decide [s8, s7, s6, f2, Data.comap])
    (by simp +decide [s8, s7, f2, Data.comap])
    (by simp +decide [s8, s7, s6, s5, hs4_4, f2, Data.comap])
    (by simp +decide [s8, f2, Data.comap])
    hfit_B2 hfit_r
  have e9 := hstep_inner.rename hmap2
  set s9 := (trinomialStepLoopData B 1 (s8.comap f2)).extend f2 s8
  have hs9_1 : s9.regs 1 = 3 ^ trinomialStep U M := by
    change (s9.comap f2).regs 1 = 3 ^ trinomialStep U M
    rw [Data.comap_extend hmap2]
    simp +decide [trinomialStepLoopData, trinomialStep, B, s8, s7, f2, Data.comap]
  have hs9_4 : s9.regs 4 = 2 := by
    change (s9.comap f2).regs 2 = 2
    rw [Data.comap_extend hmap2]
    simp +decide [trinomialStepLoopData, s8, s7, s6, s5, hs4_4, f2, Data.comap]
  have hs9_0 : s9.regs 0 = base := by
    simp +decide [s9, Data.extend, f2, s8, s7, s6, s5, hs4_0]
  have hs9_3 : s9.regs 3 = M := by
    simp +decide [s9, Data.extend, f2, s8, s7, s6, s5, hs4_3]
  have hs9_5 : s9.regs 5 = b := by
    simp +decide [s9, Data.extend, f2, s8, s7, s6, s5, hs4_5]
  have hs9_6 : s9.regs 6 = 1 := by
    simp +decide [s9, Data.extend, f2, s8, s7, s6, s5, hs4_6]
  set s10 := s9.set 2 (trinomialDeg U M)
  have e10 : Exec w (.op (.exactBin .mul 2 4 1) : Code .exact 18) s9 s10 1 :=
    exec_exactBin (by simp +decide [hs9_4, hs9_1, trinomialDeg]) hfit_q_val
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq e10))))))))
  refine ⟨s10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [trinomialParamsCode, trinomialStep, B, f1, f2,
      show 1 + (3 + (1 + (5 * Nat.clog 2 (max U 2) + 2 + (3 + (3 + (1 + (1 +
        (5 * trinomialStepAux (trinomialTargetBits U M) + 2 + 1)))))))) =
        5 * Nat.clog 2 (max U 2) +
          5 * trinomialStepAux (trinomialTargetBits U M) + 18 by omega] using hall
  · simp +decide [s10, hs9_0]
  · simp +decide [s10, hs9_1]
  · simp +decide [s10]
  · simp +decide [s10, hs9_3]
  · simp +decide [s10, hs9_4]
  · simp +decide [s10, hs9_5]
  · simp +decide [s10, hs9_6]
  · rfl

/-- First 17-instruction header-store block: writes `r, q, 2 ^ r - 1, 2 ^ q - 1, 2 ^ M - 1, b` to
`base + 0 .. base + 5`. -/
@[expose] def storeHeaderPart1 : Code .exact 18 :=
  .seq (.op (.store 0 1))
  (.seq (.op (.exactBin .add 7 0 6))
  (.seq (.op (.store 7 2))
  (.seq (.op (.exactBin .shiftLeft 8 6 1))
  (.seq (.op (.exactBin .sub 8 8 6))
  (.seq (.op (.exactBin .add 7 7 6))
  (.seq (.op (.store 7 8))
  (.seq (.op (.exactBin .shiftLeft 8 6 2))
  (.seq (.op (.exactBin .sub 8 8 6))
  (.seq (.op (.exactBin .add 7 7 6))
  (.seq (.op (.store 7 8))
  (.seq (.op (.exactBin .shiftLeft 8 6 3))
  (.seq (.op (.exactBin .sub 8 8 6))
  (.seq (.op (.exactBin .add 7 7 6))
  (.seq (.op (.store 7 8))
  (.seq (.op (.exactBin .add 7 7 6))
        (.op (.store 7 5)))))))))))))))))

/-- Second 17-instruction header-store and loop-prep block: writes `2 ^ b - 1` and
`limbCountFromB b q` to `base + 6, base + 7` and sets registers `0..5` for `clmulTabLoop`. -/
@[expose] def storeHeaderPart2 (k : ℕ) : Code .exact 18 :=
  .seq (.op (.exactBin .shiftLeft 8 6 5))
  (.seq (.op (.exactBin .sub 8 8 6))
  (.seq (.op (.exactBin .add 7 7 6))
  (.seq (.op (.store 7 8))
  (.seq (.op (.exactBin .sub 9 2 6))
  (.seq (.op (.exactBin .div 9 9 5))
  (.seq (.op (.exactBin .add 9 9 6))
  (.seq (.op (.exactBin .add 7 7 6))
  (.seq (.op (.store 7 9))
  (.seq (.op (.exactBin .mul 2 4 5))
  (.seq (.op (.exactBin .shiftLeft 2 6 2))
  (.seq (.op (.copy 3 5))
  (.seq (.op (.copy 4 8))
  (.seq (.op (.copy 5 6))
  (.seq (.op (.const 1 0))
  (.seq (.op (.const 9 (8 + k)))
        (.op (.exactBin .add 0 0 9)))))))))))))))))

/-- When `0 < b` and `0 < q`, `(q - 1) / b + 1 = limbCountFromB b q`. -/
private theorem div_pred_add_one_eq_limbCountFromB {b q : ℕ} (hb : 0 < b) (hq : 0 < q) :
    (q - 1) / b + 1 = limbCountFromB b q := by
  dsimp only [limbCountFromB]
  have h : q + b - 1 = (q - 1) + 1 * b := by omega
  rw [h, Nat.add_mul_div_right _ _ hb]

/-- `storeHeaderPart1` executes deterministically in `17` steps. -/
theorem storeHeaderPart1_exec {w base r q M b : ℕ} {x : Data 18}
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = r) (h2 : x.regs 2 = q)
    (h3 : x.regs 3 = M) (h4 : x.regs 4 = 2) (h5 : x.regs 5 = b) (h6 : x.regs 6 = 1)
    (hr_le : r ≤ q) (hM_le : M ≤ q)
    (hfit_end : Fits w (base + 8)) (hfit_q : Fits w (2 ^ q)) :
    ∃ y : Data 18,
      Exec w storeHeaderPart1 x y 17 ∧
      y.regs 0 = base ∧
      y.regs 2 = q ∧
      y.regs 4 = 2 ∧
      y.regs 5 = b ∧
      y.regs 6 = 1 ∧
      y.regs 7 = base + 5 ∧
      y.mem base = r ∧
      y.mem (base + 1) = q ∧
      y.mem (base + 2) = 2 ^ r - 1 ∧
      y.mem (base + 3) = 2 ^ q - 1 ∧
      y.mem (base + 4) = 2 ^ M - 1 ∧
      y.mem (base + 5) = b ∧
      (∀ a, (a < base ∨ base + 6 ≤ a) → y.mem a = x.mem a) := by
  have hpow_r : 2 ^ r ≤ 2 ^ q := Nat.pow_le_pow_right (by decide) hr_le
  have hpow_M : 2 ^ M ≤ 2 ^ q := Nat.pow_le_pow_right (by decide) hM_le
  have hpos_r : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hpos_q : 1 ≤ 2 ^ q := Nat.one_le_two_pow
  have hpos_M : 1 ≤ 2 ^ M := Nat.one_le_two_pow
  have hfit_pow_r : Fits w (2 ^ r) := hfit_q.of_le hpow_r
  have hfit_mask_r : Fits w (2 ^ r - 1) := hfit_pow_r.of_le (by omega)
  have hfit_mask_q : Fits w (2 ^ q - 1) := hfit_q.of_le (by omega)
  have hfit_pow_M : Fits w (2 ^ M) := hfit_q.of_le hpow_M
  have hfit_mask_M : Fits w (2 ^ M - 1) := hfit_pow_M.of_le (by omega)
  have hfit_b1 : Fits w (base + 1) := hfit_end.of_le (by omega)
  have hfit_b2 : Fits w (base + 2) := hfit_end.of_le (by omega)
  have hfit_b3 : Fits w (base + 3) := hfit_end.of_le (by omega)
  have hfit_b4 : Fits w (base + 4) := hfit_end.of_le (by omega)
  have hfit_b5 : Fits w (base + 5) := hfit_end.of_le (by omega)
  set s1 := x.write base r
  have e1 : Exec w (.op (.store 0 1) : Code .exact 18) x s1 1 := by
    simpa +decide [s1, h0, h1] using (Exec.store (B := .exact) (w := w) (a := 0) (s := 1) (x := x))
  set s2 := s1.set 7 (base + 1)
  have e2 : Exec w (.op (.exactBin .add 7 0 6) : Code .exact 18) s1 s2 1 :=
    exec_exactBin (by simp +decide [s1, h0, h6]) hfit_b1
  set s3 := s2.write (base + 1) q
  have e3 : Exec w (.op (.store 7 2) : Code .exact 18) s2 s3 1 := by
    simpa +decide [s3, s2, s1, h2] using
      (Exec.store (B := .exact) (w := w) (a := 7) (s := 2) (x := s2))
  set s4 := s3.set 8 (2 ^ r)
  have e4 : Exec w (.op (.exactBin .shiftLeft 8 6 1) : Code .exact 18) s3 s4 1 :=
    exec_exactBin (by simp +decide [s3, s2, s1, h6, h1, Nat.shiftLeft_eq]) hfit_pow_r
  set s5 := s4.set 8 (2 ^ r - 1)
  have e5 : Exec w (.op (.exactBin .sub 8 8 6) : Code .exact 18) s4 s5 1 :=
    exec_exactBin (by simp +decide [s4, s3, s2, s1, h6, hpos_r]) hfit_mask_r
  set s6 := s5.set 7 (base + 2)
  have e6 : Exec w (.op (.exactBin .add 7 7 6) : Code .exact 18) s5 s6 1 :=
    exec_exactBin (by simp +decide [s5, s4, s3, s2, s1, h6, Nat.add_assoc]) hfit_b2
  set s7 := s6.write (base + 2) (2 ^ r - 1)
  have e7 : Exec w (.op (.store 7 8) : Code .exact 18) s6 s7 1 := by
    simpa +decide [s7, s6, s5] using
      (Exec.store (B := .exact) (w := w) (a := 7) (s := 8) (x := s6))
  set s8 := s7.set 8 (2 ^ q)
  have e8 : Exec w (.op (.exactBin .shiftLeft 8 6 2) : Code .exact 18) s7 s8 1 :=
    exec_exactBin (by simp +decide [s7, s6, s5, s4, s3, s2, s1, h6, h2, Nat.shiftLeft_eq]) hfit_q
  set s9 := s8.set 8 (2 ^ q - 1)
  have e9 : Exec w (.op (.exactBin .sub 8 8 6) : Code .exact 18) s8 s9 1 :=
    exec_exactBin (by simp +decide [s8, s7, s6, s5, s4, s3, s2, s1, h6, hpos_q]) hfit_mask_q
  set s10 := s9.set 7 (base + 3)
  have e10 : Exec w (.op (.exactBin .add 7 7 6) : Code .exact 18) s9 s10 1 :=
    exec_exactBin (by simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, h6, Nat.add_assoc]) hfit_b3
  set s11 := s10.write (base + 3) (2 ^ q - 1)
  have e11 : Exec w (.op (.store 7 8) : Code .exact 18) s10 s11 1 := by
    simpa +decide [s11, s10, s9] using
      (Exec.store (B := .exact) (w := w) (a := 7) (s := 8) (x := s10))
  set s12 := s11.set 8 (2 ^ M)
  have e12 : Exec w (.op (.exactBin .shiftLeft 8 6 3) : Code .exact 18) s11 s12 1 :=
    exec_exactBin
      (by simp +decide [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h6, h3, Nat.shiftLeft_eq])
      hfit_pow_M
  set s13 := s12.set 8 (2 ^ M - 1)
  have e13 : Exec w (.op (.exactBin .sub 8 8 6) : Code .exact 18) s12 s13 1 :=
    exec_exactBin (by simp +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h6, hpos_M])
      hfit_mask_M
  set s14 := s13.set 7 (base + 4)
  have e14 : Exec w (.op (.exactBin .add 7 7 6) : Code .exact 18) s13 s14 1 :=
    exec_exactBin
      (by simp +decide [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h6, Nat.add_assoc])
      hfit_b4
  set s15 := s14.write (base + 4) (2 ^ M - 1)
  have e15 : Exec w (.op (.store 7 8) : Code .exact 18) s14 s15 1 := by
    simpa +decide [s15, s14, s13] using
      (Exec.store (B := .exact) (w := w) (a := 7) (s := 8) (x := s14))
  set s16 := s15.set 7 (base + 5)
  have e16 : Exec w (.op (.exactBin .add 7 7 6) : Code .exact 18) s15 s16 1 :=
    exec_exactBin
      (by simp +decide [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h6,
        Nat.add_assoc])
      hfit_b5
  set s17 := s16.write (base + 5) b
  have e17 : Exec w (.op (.store 7 5) : Code .exact 18) s16 s17 1 := by
    simpa +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h5]
      using (Exec.store (B := .exact) (w := w) (a := 7) (s := 5) (x := s16))
  have hall :=
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq (e10.seq
      (e11.seq (e12.seq (e13.seq (e14.seq (e15.seq (e16.seq e17)))))))))))))))
  refine ⟨s17, hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0]
  · simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h2]
  · simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h4]
  · simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h5]
  · simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h6]
  · simp +decide [s17, s16]
  · simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
  · simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
  · simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
  · simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
  · simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
  · simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
  · intro a ha
    dsimp only [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
      Data.write, Data.set]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-- `storeHeaderPart2 k` executes deterministically in `17` steps. -/
theorem storeHeaderPart2_exec {w base q b k : ℕ} {x : Data 18}
    (hb : 0 < b) (hq : 0 < q)
    (h0 : x.regs 0 = base) (h2 : x.regs 2 = q) (h4 : x.regs 4 = 2)
    (h5 : x.regs 5 = b) (h6 : x.regs 6 = 1) (h7 : x.regs 7 = base + 5)
    (hfit_space : Fits w (base + spaceFromB b k)) (hfit_q : Fits w q) :
    ∃ y : Data 18,
      Exec w (storeHeaderPart2 k) x y 17 ∧
      y.regs 0 = base + 8 + k ∧
      y.regs 1 = 0 ∧
      y.regs 2 = 2 ^ (2 * b) ∧
      y.regs 3 = b ∧
      y.regs 4 = 2 ^ b - 1 ∧
      y.regs 5 = 1 ∧
      y.mem (base + 6) = 2 ^ b - 1 ∧
      y.mem (base + 7) = limbCountFromB b q ∧
      (∀ a, (a < base + 6 ∨ base + 8 ≤ a) → y.mem a = x.mem a) := by
  have hpow_le : 2 ^ b ≤ 2 ^ (2 * b) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos_b : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have h2b_lt : 2 * b < 2 ^ (2 * b) := Nat.lt_two_pow_self
  have hfit_pow2b : Fits w (2 ^ (2 * b)) := hfit_space.of_le (by simp [spaceFromB]; omega)
  have hfit_powb : Fits w (2 ^ b) := hfit_pow2b.of_le hpow_le
  have hfit_maskb : Fits w (2 ^ b - 1) := hfit_powb.of_le (by omega)
  have hfit_b6 : Fits w (base + 6) := hfit_space.of_le (by simp [spaceFromB]; omega)
  have hfit_b7 : Fits w (base + 7) := hfit_space.of_le (by simp [spaceFromB]; omega)
  have hfit_qm1 : Fits w (q - 1) := hfit_q.of_le (by omega)
  have hfit_div : Fits w ((q - 1) / b) := hfit_qm1.of_le (Nat.div_le_self _ _)
  have hdiv1_le : (q - 1) / b + 1 ≤ q := by
    have := Nat.div_le_self (q - 1) b
    omega
  have hfit_L : Fits w (limbCountFromB b q) := by
    rw [← div_pred_add_one_eq_limbCountFromB hb hq]
    exact hfit_q.of_le hdiv1_le
  have hfit_2b : Fits w (2 * b) := hfit_pow2b.of_le (le_of_lt h2b_lt)
  have hfit_0 : Fits w 0 := hfit_space.of_le (Nat.zero_le _)
  have hfit_8k : Fits w (8 + k) := hfit_space.of_le (by simp [spaceFromB]; omega)
  have hfit_tabBase : Fits w (base + 8 + k) := hfit_space.of_le (by simp [spaceFromB]; omega)
  set s1 := x.set 8 (2 ^ b)
  have e1 : Exec w (.op (.exactBin .shiftLeft 8 6 5) : Code .exact 18) x s1 1 :=
    exec_exactBin (by simp +decide [h6, h5, Nat.shiftLeft_eq]) hfit_powb
  set s2 := s1.set 8 (2 ^ b - 1)
  have e2 : Exec w (.op (.exactBin .sub 8 8 6) : Code .exact 18) s1 s2 1 :=
    exec_exactBin (by simp +decide [s1, h6, hpos_b]) hfit_maskb
  set s3 := s2.set 7 (base + 6)
  have e3 : Exec w (.op (.exactBin .add 7 7 6) : Code .exact 18) s2 s3 1 :=
    exec_exactBin (by simp +decide [s2, s1, h7, h6, Nat.add_assoc]) hfit_b6
  set s4 := s3.write (base + 6) (2 ^ b - 1)
  have e4 : Exec w (.op (.store 7 8) : Code .exact 18) s3 s4 1 := by
    simpa +decide [s4, s3, s2] using
      (Exec.store (B := .exact) (w := w) (a := 7) (s := 8) (x := s3))
  set s5 := s4.set 9 (q - 1)
  have e5 : Exec w (.op (.exactBin .sub 9 2 6) : Code .exact 18) s4 s5 1 :=
    exec_exactBin (by simp +decide [s4, s3, s2, s1, h2, h6]; omega) hfit_qm1
  set s6 := s5.set 9 ((q - 1) / b)
  have e6 : Exec w (.op (.exactBin .div 9 9 5) : Code .exact 18) s5 s6 1 :=
    exec_exactBin (by simp +decide [s5, s4, s3, s2, s1, h5, hb.ne']) hfit_div
  set s7 := s6.set 9 (limbCountFromB b q)
  have e7 : Exec w (.op (.exactBin .add 9 9 6) : Code .exact 18) s6 s7 1 :=
    exec_exactBin
      (by simp +decide [s6, s5, s4, s3, s2, s1, h6, div_pred_add_one_eq_limbCountFromB hb hq])
      hfit_L
  set s8 := s7.set 7 (base + 7)
  have e8 : Exec w (.op (.exactBin .add 7 7 6) : Code .exact 18) s7 s8 1 :=
    exec_exactBin (by simp +decide [s7, s6, s5, s4, s3, s2, s1, h6, Nat.add_assoc]) hfit_b7
  set s9 := s8.write (base + 7) (limbCountFromB b q)
  have e9 : Exec w (.op (.store 7 9) : Code .exact 18) s8 s9 1 := by
    simpa +decide [s9, s8, s7] using
      (Exec.store (B := .exact) (w := w) (a := 7) (s := 9) (x := s8))
  set s10 := s9.set 2 (2 * b)
  have e10 : Exec w (.op (.exactBin .mul 2 4 5) : Code .exact 18) s9 s10 1 :=
    exec_exactBin (by simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, h4, h5]) hfit_2b
  set s11 := s10.set 2 (2 ^ (2 * b))
  have e11 : Exec w (.op (.exactBin .shiftLeft 2 6 2) : Code .exact 18) s10 s11 1 :=
    exec_exactBin
      (by simp +decide [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h6, Nat.shiftLeft_eq])
      hfit_pow2b
  set s12 := s11.set 3 b
  have e12 : Exec w (.op (.copy 3 5) : Code .exact 18) s11 s12 1 := by
    simpa +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h5] using
      (Exec.copy (B := .exact) (w := w) (d := 3) (s := 5) (x := s11))
  set s13 := s12.set 4 (2 ^ b - 1)
  have e13 : Exec w (.op (.copy 4 8) : Code .exact 18) s12 s13 1 := by
    simpa +decide [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2] using
      (Exec.copy (B := .exact) (w := w) (d := 4) (s := 8) (x := s12))
  set s14 := s13.set 5 1
  have e14 : Exec w (.op (.copy 5 6) : Code .exact 18) s13 s14 1 := by
    simpa +decide [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h6] using
      (Exec.copy (B := .exact) (w := w) (d := 5) (s := 6) (x := s13))
  set s15 := s14.set 1 0
  have e15 : Exec w (.op (.const 1 0) : Code .exact 18) s14 s15 1 := Exec.const hfit_0
  set s16 := s15.set 9 (8 + k)
  have e16 : Exec w (.op (.const 9 (8 + k)) : Code .exact 18) s15 s16 1 := Exec.const hfit_8k
  set s17 := s16.set 0 (base + 8 + k)
  have e17 : Exec w (.op (.exactBin .add 0 0 9) : Code .exact 18) s16 s17 1 :=
    exec_exactBin
      (by simp +decide [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0,
        Nat.add_assoc])
      hfit_tabBase
  have hall :=
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq (e10.seq
      (e11.seq (e12.seq (e13.seq (e14.seq (e15.seq (e16.seq e17)))))))))))))))
  refine ⟨s17, hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [s17]
  · simp +decide [s17, s16, s15]
  · simp +decide [s17, s16, s15, s14, s13, s12, s11]
  · simp +decide [s17, s16, s15, s14, s13, s12]
  · simp +decide [s17, s16, s15, s14, s13]
  · simp +decide [s17, s16, s15, s14]
  · simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4]
  · simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9]
  · intro a ha
    dsimp only [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
      Data.write, Data.set]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-- 2-instruction suffix restoring `regBase = base` from `base + 8 + k`. -/
@[expose] def restoreBaseCode (k : ℕ) : Code .exact 18 :=
  .seq (.op (.const 9 (8 + k)))
        (.op (.exactBin .sub 0 0 9))

/-- Complete deterministic table initialization program `initTableCode k`: computes
`(r, q, b, L)` and masks from `(base, n_max, U, M)` in registers `0..3` and populates
`clmulTab[0 .. 2 ^ (2 * b) - 1]`. -/
@[expose] def initTableCode (k : ℕ) : Code .exact 18 :=
  .seq chunkBitsCode
  (.seq trinomialParamsCode
  (.seq storeHeaderPart1
  (.seq (storeHeaderPart2 k)
  (.seq clmulTabLoop
        (restoreBaseCode k)))))

/-- Exact step count of `initTableCode k`. -/
@[expose] def initTableSteps (n_max U M : ℕ) : ℕ :=
  19 * 2 ^ (2 * chunkBits n_max) +
    4 * Nat.log 2 (max n_max 2) +
    5 * Nat.clog 2 (max U 2) +
    5 * trinomialStep U M + 69

/-- **`KWise.initTableCode k` correctness and complexity**: from `reg 0 = base`, `reg 1 = n_max`,
`reg 2 = U`, `reg 3 = M`, `initTableCode k` halts deterministically in
`initTableSteps n_max U M = O(n_max + log U + log M)` instructions, establishing
`TableRep base (chunkBits n_max) U M k y.mem`, preserving `reg 0 = base`, and modifying memory
only within `[base, base + space n_max k)`. -/
theorem initTableCode_execWithin {w base n_max U M k : ℕ} {x : Data 18}
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = n_max) (h2 : x.regs 2 = U) (h3 : x.regs 3 = M)
    (hfit_space : Fits w (base + space n_max k))
    (hfit_n : Fits w (max n_max 2)) (hfit_U : Fits w (max U 2 + 1))
    (hfit_q : Fits w (2 ^ trinomialDeg U M)) :
    ∃ y : Data 18,
      ExecWithin w (initTableCode k) x y (initTableSteps n_max U M) ∧
      TableRep base (chunkBits n_max) U M k y.mem ∧
      y.regs 0 = base ∧
      (∀ a, (a < base ∨ base + space n_max k ≤ a) → y.mem a = x.mem a) := by
  set b := chunkBits n_max
  set r := 3 ^ trinomialStep U M
  set q := trinomialDeg U M
  have hb_pos : 0 < b := chunkBits_pos n_max
  have hq_pos : 0 < q := by
    dsimp only [q, trinomialDeg]
    have : 1 ≤ 3 ^ trinomialStep U M := Nat.one_le_pow _ 3 (by decide)
    omega
  have hr_le : r ≤ q := by dsimp only [q, trinomialDeg, r]; omega
  have hM_le : M ≤ q := le_trinomialDeg U M
  have hsp : space n_max k = 8 + k + 2 ^ (2 * b) := rfl
  have hpow_pos : 0 < 2 ^ (2 * b) := by positivity
  have hfit_3 : Fits w 3 := hfit_space.of_le (by omega)
  have hfit_end8 : Fits w (base + 8) := hfit_space.of_le (by omega)
  have hfit_qval : Fits w q := hfit_q.of_le (le_of_lt Nat.lt_two_pow_self)
  have hfit_tabEnd : Fits w (base + 8 + k + 2 ^ (2 * b)) := hfit_space.of_le (by omega)
  have hfit_8k : Fits w (8 + k) := hfit_space.of_le (by omega)
  have hfit_base : Fits w base := hfit_space.of_le (by omega)
  obtain ⟨d1, e1, hd1_0, hd1_2, hd1_3, hd1_5, hd1_6, hd1_mem⟩ :=
    chunkBitsCode_exec h0 h1 h2 h3 hfit_n hfit_3
  obtain ⟨d2, e2, hd2_0, hd2_1, hd2_2, hd2_3, hd2_4, hd2_5, hd2_6, hd2_mem⟩ :=
    trinomialParamsCode_exec hd1_0 hd1_2 hd1_3 hd1_5 hd1_6 hfit_U hfit_q
  obtain ⟨d3, e3, hd3_0, hd3_2, hd3_4, hd3_5, hd3_6, hd3_7,
      hm0, hm1, hm2, hm3, hm4, hm5, hd3_out⟩ :=
    storeHeaderPart1_exec hd2_0 hd2_1 hd2_2 hd2_3 hd2_4 hd2_5 hd2_6 hr_le hM_le
      hfit_end8 hfit_q
  obtain ⟨d4, e4, hd4_0, hd4_1, hd4_2, hd4_3, hd4_4, hd4_5, hm6, hm7, hd4_out⟩ :=
    storeHeaderPart2_exec hb_pos hq_pos hd3_0 hd3_2 hd3_4 hd3_5 hd3_6 hd3_7 hfit_space hfit_qval
  obtain ⟨d5, e5, hd5_0, htab, hd5_out⟩ :=
    clmulTabLoop_exec hfit_tabEnd (2 ^ (2 * b)) 0 d4 (by omega)
      hd4_0 hd4_1 hd4_2 hd4_3 hd4_4 hd4_5 (by intro i hi; omega)
  set d6 := d5.set 9 (8 + k)
  have er1 : Exec w (.op (.const 9 (8 + k)) : Code .exact 18) d5 d6 1 := Exec.const hfit_8k
  set d7 := d6.set 0 base
  have er2 : Exec w (.op (.exactBin .sub 0 0 9) : Code .exact 18) d6 d7 1 :=
    exec_exactBin (by simp +decide [d6, hd5_0]; omega) hfit_base
  have e6 := er1.seq er2
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))
  have hmem_hdr : ∀ j < 8, d7.mem (base + j) = d4.mem (base + j) := by
    intro j hj
    exact hd5_out (base + j) (Or.inl (by omega))
  refine ⟨d7, ⟨_, ?_, hall⟩, ?_, by simp +decide [d7], ?_⟩
  · dsimp only [initTableSteps, b]
    omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hmem_hdr 0 (by decide)
      rw [Nat.add_zero] at this
      rw [this, hd4_out base (Or.inl (by omega)), hm0]
    · rw [hmem_hdr 1 (by decide), hd4_out (base + 1) (Or.inl (by omega)), hm1]
    · rw [hmem_hdr 2 (by decide), hd4_out (base + 2) (Or.inl (by omega)), hm2]
    · rw [hmem_hdr 3 (by decide), hd4_out (base + 3) (Or.inl (by omega)), hm3]
    · rw [hmem_hdr 4 (by decide), hd4_out (base + 4) (Or.inl (by omega)), hm4]
    · rw [hmem_hdr 5 (by decide), hd4_out (base + 5) (Or.inl (by omega)), hm5]
    · rw [hmem_hdr 6 (by decide), hm6]
    · rw [hmem_hdr 7 (by decide), hm7]
    · intro idx hidx
      exact htab idx hidx
  · intro a ha
    have ha_eq : a < base ∨ base + (8 + k + 2 ^ (2 * b)) ≤ a := by
      simpa only [space, spaceFromB, b] using ha
    have ha_d5 : a < base + 8 + k + 0 ∨ base + 8 + k + 2 ^ (2 * b) ≤ a := by omega
    have ha_d4 : a < base + 6 ∨ base + 8 ≤ a := by omega
    have ha_d3 : a < base ∨ base + 6 ≤ a := by omega
    calc d7.mem a = d5.mem a := rfl
      _ = d4.mem a := hd5_out a ha_d5
      _ = d3.mem a := hd4_out a ha_d4
      _ = d2.mem a := hd3_out a ha_d3
      _ = x.mem a := by rw [hd2_mem, hd1_mem]

/-- Setup prefix for `resampleCode k`: loads `2 ^ q - 1` from `base + 3` into register `1` and
initializes `ptr = base + 8` (`reg 2`), `end = base + 8 + k` (`reg 3`), and `one = 1` (`reg 4`). -/
@[expose] def resampleSetupCode (k : ℕ) : Code .exact 18 :=
  .seq (.op (.const 1 3))
  (.seq (.op (.exactBin .add 1 0 1))
  (.seq (.op (.load 1 1))
  (.seq (.op (.const 2 8))
  (.seq (.op (.exactBin .add 2 0 2))
  (.seq (.op (.const 3 k))
  (.seq (.op (.exactBin .add 3 2 3))
        (.op (.const 4 1))))))))

/-- Closed-form state after `resampleSetupCode k`. -/
@[expose] def resampleSetupData (base U M k : ℕ) (x : Data 18) : Data 18 :=
  ((((x.set 1 (2 ^ trinomialDeg U M - 1)).set 2 (base + 8)).set 3 (base + 8 + k)).set 4 1)

/-- Injective register map embedding `randFillLoop` into `Data 18` so `regExtra` (`5`) maps to
`regBase` (`0`). -/
@[expose] def resampleMap : Fin 6 → Fin 18 :=
  ![2, 3, 1, 4, 5, 0]

theorem injective_resampleMap : Function.Injective resampleMap := by
  decide

/-- Seed-resampling program `resampleCode k`: samples the `k` polynomial coefficients
`seed[0 .. k - 1]` uniformly in `Fin (2 ^ trinomialDeg U M)` using `k` `Code.rand` calls in
`5 * k + 10` instructions while preserving `TableRep` and `regBase = base`. -/
@[expose] def resampleCode (k : ℕ) : Code .exact 18 :=
  .seq (resampleSetupCode k) (randFillLoop.rename resampleMap)

/-- Exact `ProbComp` semantics of `resampleCode k`. -/
@[expose] noncomputable def resampleComp (base U M k : ℕ) (x : Data 18) : ProbComp (Data 18 × ℕ) :=
  let d0 := resampleSetupData base U M k x
  (fun z : Data 6 × ℕ => (z.1.extend resampleMap d0, 8 + z.2)) <$>
    randFillComp (trinomialDeg U M) (base + 8) k (d0.comap resampleMap)

/-- `resampleSetupCode k` executes deterministically in `8` steps. -/
theorem resampleSetupCode_exec {w base b U M k : ℕ} {x : Data 18}
    (htab : TableRep base b U M k x.mem) (h0 : x.regs 0 = base)
    (hfit_end : Fits w (base + 8 + k)) :
    Exec w (resampleSetupCode k) x (resampleSetupData base U M k x) 8 := by
  have hfit_3 : Fits w 3 := hfit_end.of_le (by omega)
  have hfit_b3 : Fits w (base + 3) := hfit_end.of_le (by omega)
  have hfit_8 : Fits w 8 := hfit_end.of_le (by omega)
  have hfit_b8 : Fits w (base + 8) := hfit_end.of_le (by omega)
  have hfit_k : Fits w k := hfit_end.of_le (by omega)
  have hfit_1 : Fits w 1 := hfit_end.of_le (by omega)
  have hm3 : x.mem (base + 3) = 2 ^ trinomialDeg U M - 1 := htab.2.2.2.1
  set s1 := x.set 1 3
  have e1 : Exec w (.op (.const 1 3) : Code .exact 18) x s1 1 := Exec.const hfit_3
  set s2 := s1.set 1 (base + 3)
  have e2 : Exec w (.op (.exactBin .add 1 0 1) : Code .exact 18) s1 s2 1 :=
    exec_exactBin (by simp +decide [s1, h0]) hfit_b3
  set s3 := s2.set 1 (2 ^ trinomialDeg U M - 1)
  have e3 : Exec w (.op (.load 1 1) : Code .exact 18) s2 s3 1 := by
    simpa +decide [s3, s2, s1, hm3] using
      (Exec.load (B := .exact) (w := w) (d := 1) (a := 1) (x := s2))
  set s4 := s3.set 2 8
  have e4 : Exec w (.op (.const 2 8) : Code .exact 18) s3 s4 1 := Exec.const hfit_8
  set s5 := s4.set 2 (base + 8)
  have e5 : Exec w (.op (.exactBin .add 2 0 2) : Code .exact 18) s4 s5 1 :=
    exec_exactBin (by simp +decide [s4, s3, s2, s1, h0]) hfit_b8
  set s6 := s5.set 3 k
  have e6 : Exec w (.op (.const 3 k) : Code .exact 18) s5 s6 1 := Exec.const hfit_k
  set s7 := s6.set 3 (base + 8 + k)
  have e7 : Exec w (.op (.exactBin .add 3 2 3) : Code .exact 18) s6 s7 1 :=
    exec_exactBin (by simp +decide [s6, s5, Nat.add_assoc]) hfit_end
  set s8 := s7.set 4 1
  have e8 : Exec w (.op (.const 4 1) : Code .exact 18) s7 s8 1 := Exec.const hfit_1
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))
  have hd : s8 = resampleSetupData base U M k x := by
    ext i : 2
    · fin_cases i <;> rfl
    · rfl
  rwa [hd] at hall

/-- **`KWise.resampleCode k` exact randomized execution**: executes with exact `ProbComp`
semantics `resampleComp base U M k x`. -/
theorem resampleCode_execRand {w base b U M k : ℕ} {x : Data 18}
    (htab : TableRep base b U M k x.mem) (h0 : x.regs 0 = base)
    (hfit_end : Fits w (base + 8 + k)) (hfit_q : Fits w (2 ^ trinomialDeg U M)) :
    ExecRand w (resampleCode k) x (resampleComp base U M k x) := by
  have hsetup := resampleSetupCode_exec htab h0 hfit_end
  set d0 := resampleSetupData base U M k x
  have hfit_mask : Fits w (2 ^ trinomialDeg U M - 1) := hfit_q.of_le (Nat.sub_le _ 1)
  have hloop0 := randFillLoop_execRand (w := w) (bits := trinomialDeg U M) (arrBase := base + 8)
    k (x := d0.comap resampleMap)
    (by simp +decide [d0, resampleSetupData, resampleMap, Data.comap, regPtr])
    (by simp +decide [d0, resampleSetupData, resampleMap, Data.comap, regEnd])
    (by simp +decide [d0, resampleSetupData, resampleMap, Data.comap, regMask])
    (by simp +decide [d0, resampleSetupData, resampleMap, Data.comap, regOne])
    hfit_end hfit_mask
  have hloop := hloop0.rename injective_resampleMap
  have hseq := hsetup.seqRand hloop
  simpa only [resampleCode, resampleComp, d0, Functor.map_map] using hseq

/-- **Uniformity of resampled seeds**: under `(resampleComp base U M k x).eval`, the extracted seed
tuple `extractSeeds base U M k z.1.mem` is uniformly distributed over
`Fin k → Fin (2 ^ trinomialDeg U M)`. -/
theorem map_extractSeeds_eval_resampleComp (base U M k : ℕ) (x : Data 18) :
    ((resampleComp base U M k x).eval).map (fun z => extractSeeds base U M k z.1.mem) =
      PMF.uniformOfFintype (Fin k → Fin (2 ^ trinomialDeg U M)) := by
  dsimp only [resampleComp, extractSeeds]
  rw [ProbComp.eval_map, PMF.map_comp]
  exact map_extractSlice_eval_randFillComp (trinomialDeg U M) (base + 8) k _

/-- Every outcome `z ∈ (resampleComp base U M k x).support` preserves `TableRep base b U M k`,
establishes `Rep base b U M k (extractSeeds base U M k z.1.mem) z.1.mem`, sets `z.1.regs 0 = base`,
modifies memory only within `[base + 8, base + 8 + k)`, and takes at most `5 * k + 10` steps. -/
theorem mem_support_resampleComp {base b U M k : ℕ} {x : Data 18}
    (htab : TableRep base b U M k x.mem) (h0 : x.regs 0 = base)
    {z : Data 18 × ℕ} (hz : z ∈ (resampleComp base U M k x).support) :
    (Rep base b U M k (extractSeeds base U M k z.1.mem) z.1.mem ∧
      z.1.regs 0 = base ∧
      (∀ a, (a < base + 8 ∨ base + 8 + k ≤ a) → z.1.mem a = x.mem a)) ∧
    z.2 ≤ 5 * k + 10 := by
  dsimp only [resampleComp] at hz
  obtain ⟨z0, hz0, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  obtain ⟨hsteps, -, -, -, -, hextra, hlt, hout⟩ := mem_support_randFillComp hz0
  have htab' : TableRep base b U M k z0.1.mem := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hout base (Or.inl (by omega))]; exact htab.1
    · rw [hout (base + 1) (Or.inl (by omega))]; exact htab.2.1
    · rw [hout (base + 2) (Or.inl (by omega))]; exact htab.2.2.1
    · rw [hout (base + 3) (Or.inl (by omega))]; exact htab.2.2.2.1
    · rw [hout (base + 4) (Or.inl (by omega))]; exact htab.2.2.2.2.1
    · rw [hout (base + 5) (Or.inl (by omega))]; exact htab.2.2.2.2.2.1
    · rw [hout (base + 6) (Or.inl (by omega))]; exact htab.2.2.2.2.2.2.1
    · rw [hout (base + 7) (Or.inl (by omega))]; exact htab.2.2.2.2.2.2.2.1
    · intro idx hidx
      rw [hout (base + 8 + k + idx) (Or.inr (by omega))]
      exact htab.2.2.2.2.2.2.2.2 idx hidx
  have hseed : SeedRep base U M k (extractSeeds base U M k z0.1.mem) z0.1.mem := by
    intro j
    simp [extractSeeds, extractSlice, hlt j.val j.isLt]
  have hbase' : (z0.1.extend resampleMap (resampleSetupData base U M k x)).regs 0 = base := by
    change ((z0.1.extend resampleMap (resampleSetupData base U M k x)).comap
      resampleMap).regs regExtra = base
    rw [Data.comap_extend injective_resampleMap, hextra]
    simpa +decide [resampleSetupData, resampleMap, Data.comap, regExtra] using h0
  exact ⟨⟨⟨htab', hseed⟩, hbase', hout⟩, by omega⟩

/-- **`KWise.resampleCode k` Hoare-style specification**: halts in `5 * k + 10 = O(k)` steps and `k`
`rand` queries, preserving `TableRep base b U M k`, establishing
`Rep base b U M k (extractSeeds base U M k z.1.mem) z.1.mem`, preserving `reg 0 = base`, and
modifying memory only within `[base + 8, base + 8 + k)`. -/
theorem resampleCode_execRandWithin {w base b U M k : ℕ} {x : Data 18}
    (htab : TableRep base b U M k x.mem) (h0 : x.regs 0 = base)
    (hfit_end : Fits w (base + 8 + k)) (hfit_q : Fits w (2 ^ trinomialDeg U M)) :
    ExecRandWithin w (resampleCode k) x
      (fun y =>
        Rep base b U M k (extractSeeds base U M k y.mem) y.mem ∧
        y.regs 0 = base ∧
        (∀ a, (a < base + 8 ∨ base + 8 + k ≤ a) → y.mem a = x.mem a))
      (5 * k + 10) k := by
  refine ⟨resampleComp base U M k x, resampleCode_execRand htab h0 hfit_end hfit_q, ?_, ?_⟩
  · dsimp only [resampleComp]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      (isQueryBounded_randFillComp (trinomialDeg U M) (base + 8) k _)
  · intro z hz
    exact mem_support_resampleComp htab h0 hz

/-- Full one-shot initialization program `initCode k := .seq (initTableCode k) (resampleCode k)`. -/
@[expose] def initCode (k : ℕ) : Code .exact 18 :=
  .seq (initTableCode k) (resampleCode k)

/-- **`KWise.initCode k` Hoare-style specification**: runs `initTableCode k` followed by
`resampleCode k` in `initTableSteps n_max U M + (5 * k + 10)` steps and `k` `rand` calls. -/
theorem initCode_execRandWithin {w base n_max U M k : ℕ} {x : Data 18}
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = n_max) (h2 : x.regs 2 = U) (h3 : x.regs 3 = M)
    (hfit_space : Fits w (base + space n_max k))
    (hfit_n : Fits w (max n_max 2)) (hfit_U : Fits w (max U 2 + 1))
    (hfit_q : Fits w (2 ^ trinomialDeg U M)) :
    ExecRandWithin w (initCode k) x
      (fun y =>
        Rep base (chunkBits n_max) U M k (extractSeeds base U M k y.mem) y.mem ∧
        y.regs 0 = base ∧
        (∀ a, (a < base ∨ base + space n_max k ≤ a) → y.mem a = x.mem a))
      (initTableSteps n_max U M + (5 * k + 10)) k := by
  obtain ⟨dTab, ⟨s1, hs1, he1⟩, htab, hdTab_0, hdTab_out⟩ :=
    initTableCode_execWithin h0 h1 h2 h3 hfit_space hfit_n hfit_U hfit_q
  have hsp : space n_max k = 8 + k + 2 ^ (2 * chunkBits n_max) := rfl
  have hpow_pos : 0 < 2 ^ (2 * chunkBits n_max) := by positivity
  have hfit_end : Fits w (base + 8 + k) := hfit_space.of_le (by omega)
  obtain ⟨m2, he2, hqb, hsupp⟩ := resampleCode_execRandWithin htab hdTab_0 hfit_end hfit_q
  refine ⟨(fun z : Data 18 × ℕ => (z.1, s1 + z.2)) <$> m2, he1.seqRand he2,
    (OracleComp.isCostBounded_map_iff _ _ _).mpr hqb, ?_⟩
  intro z hz
  obtain ⟨z0, hz0, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  obtain ⟨⟨hrep, hz0_0, hz0_out⟩, hz0_steps⟩ := hsupp z0 hz0
  refine ⟨⟨hrep, hz0_0, ?_⟩, by omega⟩
  intro a ha
  have ha' : a < base + 8 ∨ base + 8 + k ≤ a := by omega
  rw [hz0_out a ha', hdTab_out a ha]

/-! ## Section 4: Deterministic Horner evaluation (`evalCode`) and `k`-wise independence -/

/-- Register `1`: holds the input key `u < U` on entry to `evalCode`. -/
abbrev regKey : Fin 18 := 1

/-- Register `2`: holds the output hash value `< 2 ^ M` on exit from `evalCode`. -/
abbrev regOut : Fin 18 := 2

private theorem and_xor_shiftRight_shiftLeft (a b : ℕ) :
    (a &&& (2 ^ b - 1)) ^^^ ((a >>> b) <<< b) = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : i < b
  · have hge : ¬ b ≤ i := not_le.mpr h
    simp [h, hge]
  · have hge : b ≤ i := le_of_not_gt h
    simp [h, hge, Nat.add_sub_of_le hge]

private theorem clmul_split_right (x y b : ℕ) :
    clmul x y = clmul x (y &&& (2 ^ b - 1)) ^^^ (clmul x (y >>> b) <<< b) := by
  conv_lhs => rw [← and_xor_shiftRight_shiftLeft y b]
  rw [clmul_xor_right, clmul_shiftLeft_right]

private theorem clmul_split_left (x y b : ℕ) :
    clmul x y = clmul (x &&& (2 ^ b - 1)) y ^^^ (clmul (x >>> b) y <<< b) := by
  conv_lhs => rw [← and_xor_shiftRight_shiftLeft x b]
  rw [clmul_xor_left, clmul_shiftLeft_left]

private theorem shiftLeft_add_eq (a m n : ℕ) :
    a <<< (m + n) = (a <<< m) <<< n := by
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, pow_add, ← mul_assoc]

private theorem xor_shiftLeft_eq (a b k : ℕ) :
    (a ^^^ b) <<< k = (a <<< k) ^^^ (b <<< k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftLeft, Nat.testBit_xor, Nat.testBit_xor,
    Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  by_cases h : i ≥ k <;> simp [h]

private theorem shiftLeft_xor_parts {u v b : ℕ} (hu : u < 2 ^ b) (hv : v < 2 ^ b) :
    (u <<< b) ^^^ v < 2 ^ (2 * b) ∧
    ((u <<< b) ^^^ v) >>> b = u ∧
    ((u <<< b) ^^^ v) &&& (2 ^ b - 1) = v := by
  have hush : u <<< b < 2 ^ (2 * b) := by
    rw [Nat.shiftLeft_eq, two_mul, pow_add]
    exact Nat.mul_lt_mul_of_pos_right hu (by positivity)
  have hv2 : v < 2 ^ (2 * b) :=
    lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨Nat.xor_lt_two_pow hush hv2, ?_, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_shiftRight, Nat.testBit_xor, Nat.testBit_shiftLeft]
    have hge : b + i ≥ b := Nat.le_add_right b i
    have hsub : b + i - b = i := Nat.add_sub_cancel_left b i
    have hv_false : v.testBit (b + i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hge))
    simp [hge, hsub, hv_false]
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_xor, Nat.testBit_shiftLeft]
    by_cases hi : i < b
    · have hge : ¬ i ≥ b := not_le.mpr hi
      simp [hi, hge]
    · have hge : b ≤ i := le_of_not_gt hi
      have hv_false : v.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hge))
      simp [hi, hv_false]

private theorem shiftRight_mul_two_pow_add_le (a b s : ℕ) :
    (a >>> b) * 2 ^ (s + b) ≤ a * 2 ^ s := by
  rw [Nat.shiftRight_eq_div_pow, pow_add, ← mul_assoc, mul_comm (a / 2 ^ b) (2 ^ s), mul_assoc,
    mul_comm a (2 ^ s)]
  exact Nat.mul_le_mul_left (2 ^ s) (Nat.div_mul_le_self a (2 ^ b))

private theorem shiftRight_lt_two_pow_mul {a rem b : ℕ} (ha : a < 2 ^ ((rem + 1) * b)) :
    a >>> b < 2 ^ (rem * b) := by
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.div_lt_of_lt_mul
  rwa [← pow_add, show b + rem * b = (rem + 1) * b by ring]

private theorem lt_two_pow_sub_of_mul_two_pow_lt {c s q : ℕ} (hc : 0 < c)
    (h : c * 2 ^ s < 2 ^ q) : s ≤ q ∧ c < 2 ^ (q - s) := by
  have hs : s ≤ q := by
    by_contra hlt
    have hle : 2 ^ q ≤ c * 2 ^ s :=
      calc 2 ^ q ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) (by omega)
        _ ≤ c * 2 ^ s := Nat.le_mul_of_pos_left _ hc
    omega
  refine ⟨hs, ?_⟩
  apply Nat.lt_of_mul_lt_mul_right (a := 2 ^ s)
  rwa [← pow_add, Nat.sub_add_cancel hs]

private theorem clmul_and_shiftLeft_lt {x_rem y_rem sh_x sh_y b q : ℕ}
    (hx : x_rem * 2 ^ sh_x < 2 ^ q) (hy : y_rem * 2 ^ sh_y < 2 ^ q) :
    clmul (x_rem &&& (2 ^ b - 1)) (y_rem &&& (2 ^ b - 1)) <<< (sh_x + sh_y) < 2 ^ (2 * q) := by
  set xc := x_rem &&& (2 ^ b - 1)
  set yc := y_rem &&& (2 ^ b - 1)
  rcases eq_or_ne xc 0 with hxc | hxc
  · simp [hxc]
  · rcases eq_or_ne yc 0 with hyc | hyc
    · simp [hyc]
    · have hxc_lt : xc * 2 ^ sh_x < 2 ^ q :=
        (Nat.mul_le_mul_right (2 ^ sh_x) Nat.and_le_left).trans_lt hx
      have hyc_lt : yc * 2 ^ sh_y < 2 ^ q :=
        (Nat.mul_le_mul_right (2 ^ sh_y) Nat.and_le_left).trans_lt hy
      obtain ⟨hsx, hxc'⟩ := lt_two_pow_sub_of_mul_two_pow_lt (Nat.pos_of_ne_zero hxc) hxc_lt
      obtain ⟨hsy, hyc'⟩ := lt_two_pow_sub_of_mul_two_pow_lt (Nat.pos_of_ne_zero hyc) hyc_lt
      have hcl := clmul_lt_two_pow hxc' hyc'
      rw [Nat.shiftLeft_eq]
      calc clmul xc yc * 2 ^ (sh_x + sh_y)
          < 2 ^ (q - sh_x + (q - sh_y)) * 2 ^ (sh_x + sh_y) :=
            Nat.mul_lt_mul_of_pos_right hcl (by positivity)
        _ = 2 ^ (2 * q) := by
            rw [← pow_add]
            congr 1
            omega

private theorem fits_of_lt_two_pow_two_mul {w q v : ℕ} (hw : 2 * q ≤ w)
    (hv : v < 2 ^ (2 * q)) : Fits w v :=
  lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hw)

/-- Body of `innerClmulLoop`: looks up `clmul (x_rem &&& mask_b) (y_rem &&& mask_b)` in `clmulTab`,
shifts left by `shift_j`, XORs into `acc` (`reg 2`), shifts `y_rem` right by `b`, advances
`shift_j` by `b`, and decrements `rem_j`. -/
@[expose] def innerClmulBody : Code .exact 18 :=
  .seq (.op (.exactBin .and 17 15 5))
  (.seq (.op (.exactBin .xor 17 13 17))
  (.seq (.op (.exactBin .add 17 7 17))
  (.seq (.op (.load 17 17))
  (.seq (.op (.exactBin .shiftLeft 17 17 16))
  (.seq (.op (.exactBin .xor 2 2 17))
  (.seq (.op (.exactBin .shiftRight 15 15 4))
  (.seq (.op (.exactBin .add 16 16 4))
        (.op (.exactBin .sub 14 14 8)))))))))

/-- Inner Four-Russians loop `while 0 < rem_j do innerClmulBody`. -/
@[expose] def innerClmulLoop : Code .exact 18 :=
  .loop (.lt 9 14) innerClmulBody

/-- `innerClmulLoop` executes deterministically in `11 * rem_j + 2` steps, XORing
`clmul (x_rem &&& (2 ^ b - 1)) y_rem <<< (sh_x + sh_y)` into `reg 2` (`acc`). -/
theorem innerClmulLoop_exec {w tabBase b q x_rem sh_x : ℕ}
    (hb : 0 < b) (hw : 2 * q ≤ w)
    (hfit_tabEnd : Fits w (tabBase + 2 ^ (2 * b)))
    (hx_bound : x_rem * 2 ^ sh_x < 2 ^ q) :
    ∀ rem_j y_rem sh_y acc : ℕ, ∀ s : Data 18,
      y_rem < 2 ^ (rem_j * b) →
      y_rem * 2 ^ sh_y < 2 ^ q →
      acc < 2 ^ (2 * q) →
      Fits w (sh_x + sh_y + rem_j * b) →
      s.regs 2 = acc →
      s.regs 4 = b →
      s.regs 5 = 2 ^ b - 1 →
      s.regs 7 = tabBase →
      s.regs 8 = 1 →
      s.regs 9 = 0 →
      s.regs 13 = (x_rem &&& (2 ^ b - 1)) <<< b →
      s.regs 14 = rem_j →
      s.regs 15 = y_rem →
      s.regs 16 = sh_x + sh_y →
      (∀ i < 2 ^ (2 * b), s.mem (tabBase + i) = clmul (i >>> b) (i &&& (2 ^ b - 1))) →
      ∃ y : Data 18,
        Exec w innerClmulLoop s y (11 * rem_j + 2) ∧
        y.regs 2 = acc ^^^ (clmul (x_rem &&& (2 ^ b - 1)) y_rem <<< (sh_x + sh_y)) ∧
        (∀ r : Fin 18, r ≠ 2 ∧ r ≠ 14 ∧ r ≠ 15 ∧ r ≠ 16 ∧ r ≠ 17 → y.regs r = s.regs r) ∧
        y.mem = s.mem := by
  intro rem_j
  induction rem_j with
  | zero =>
    intro y_rem sh_y acc s hy_lt _ _ _ h2 _ _ _ _ h9 _ h14 _ _ _
    have hy0 : y_rem = 0 := by
      rw [Nat.zero_mul, pow_zero] at hy_lt
      omega
    have hc : ¬(Cond.lt (9 : Fin 18) 14).Holds s := by
      simp [Cond.Holds, h9, h14]
    refine ⟨s, Exec.loop_exit hc, ?_, fun _ _ => rfl, rfl⟩
    simp [h2, hy0]
  | succ rem_j ih =>
    intro y_rem sh_y acc s hy_lt hy_bound hacc_lt hfit_sh h2 h4 h5 h7 h8 h9 h13 h14 h15 h16 htab
    have hc : (Cond.lt (9 : Fin 18) 14).Holds s := by
      simp [Cond.Holds, h9, h14]
    set xc := x_rem &&& (2 ^ b - 1)
    set yc := y_rem &&& (2 ^ b - 1)
    set idx := (xc <<< b) ^^^ yc
    have hxc_lt : xc < 2 ^ b := by
      dsimp only [xc]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by positivity)
    have hyc_lt : yc < 2 ^ b := by
      dsimp only [yc]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by positivity)
    obtain ⟨hidx_lt, hidx_u, hidx_v⟩ := shiftLeft_xor_parts hxc_lt hyc_lt
    have hpow_le : 2 ^ b ≤ 2 ^ (2 * b) := Nat.pow_le_pow_right (by decide) (by omega)
    have hyc_lt2 : yc < 2 ^ (2 * b) := lt_of_lt_of_le hyc_lt hpow_le
    have hidx_lt' : idx < 2 ^ (2 * b) := hidx_lt
    have hfit_yc : Fits w yc := hfit_tabEnd.of_le (by omega)
    have hfit_idx : Fits w idx := hfit_tabEnd.of_le (by omega)
    have hfit_addr : Fits w (tabBase + idx) := hfit_tabEnd.of_le (by omega)
    have hval_sh_lt : clmul xc yc <<< (sh_x + sh_y) < 2 ^ (2 * q) :=
      clmul_and_shiftLeft_lt hx_bound hy_bound
    have hfit_val_sh : Fits w (clmul xc yc <<< (sh_x + sh_y)) :=
      fits_of_lt_two_pow_two_mul hw hval_sh_lt
    have hacc'_lt : acc ^^^ (clmul xc yc <<< (sh_x + sh_y)) < 2 ^ (2 * q) :=
      Nat.xor_lt_two_pow hacc_lt hval_sh_lt
    have hfit_acc' : Fits w (acc ^^^ (clmul xc yc <<< (sh_x + sh_y))) :=
      fits_of_lt_two_pow_two_mul hw hacc'_lt
    have hy_shr_lt : y_rem >>> b < 2 ^ (rem_j * b) := shiftRight_lt_two_pow_mul hy_lt
    have hy_shr_bound : (y_rem >>> b) * 2 ^ (sh_y + b) < 2 ^ q :=
      (shiftRight_mul_two_pow_add_le y_rem b sh_y).trans_lt hy_bound
    have hy_shr_lt_2q : y_rem >>> b < 2 ^ (2 * q) := by
      have hy_lt_q : y_rem < 2 ^ q :=
        (Nat.le_mul_of_pos_right _ (by positivity)).trans_lt hy_bound
      exact (Nat.shiftRight_le y_rem b).trans_lt
        (lt_of_lt_of_le hy_lt_q (Nat.pow_le_pow_right (by decide) (by omega)))
    have hfit_y_shr : Fits w (y_rem >>> b) := fits_of_lt_two_pow_two_mul hw hy_shr_lt_2q
    have hsh_le : sh_x + sh_y + b ≤ sh_x + sh_y + (rem_j + 1) * b := by
      rw [Nat.succ_mul]
      omega
    have hfit_sh_next : Fits w (sh_x + sh_y + b) := hfit_sh.of_le hsh_le
    have hfit_rem : Fits w rem_j := by
      have : rem_j * 1 ≤ (rem_j + 1) * b := Nat.mul_le_mul (by omega) hb
      exact hfit_sh.of_le (by omega)
    set s1 := s.set 17 yc
    have e1 : Exec w (.op (.exactBin .and 17 15 5) : Code .exact 18) s s1 1 :=
      exec_exactBin (by simp [h15, h5, yc]) hfit_yc
    set s2 := s1.set 17 idx
    have e2 : Exec w (.op (.exactBin .xor 17 13 17) : Code .exact 18) s1 s2 1 :=
      exec_exactBin (by simp +decide [s1, h13, xc, idx]) hfit_idx
    set s3 := s2.set 17 (tabBase + idx)
    have e3 : Exec w (.op (.exactBin .add 17 7 17) : Code .exact 18) s2 s3 1 :=
      exec_exactBin (by simp +decide [s2, s1, h7]) hfit_addr
    set s4 := s3.set 17 (clmul xc yc)
    have hmem_idx : s3.mem (tabBase + idx) = clmul xc yc := by
      change s.mem (tabBase + idx) = clmul xc yc
      rw [htab idx hidx_lt, hidx_u, hidx_v]
    have e4 : Exec w (.op (.load 17 17) : Code .exact 18) s3 s4 1 := by
      simpa +decide [s4, s3, hmem_idx] using
        (Exec.load (B := .exact) (w := w) (d := 17) (a := 17) (x := s3))
    set s5 := s4.set 17 (clmul xc yc <<< (sh_x + sh_y))
    have e5 : Exec w (.op (.exactBin .shiftLeft 17 17 16) : Code .exact 18) s4 s5 1 :=
      exec_exactBin (by simp +decide [s4, s3, s2, s1, h16]) hfit_val_sh
    set s6 := s5.set 2 (acc ^^^ (clmul xc yc <<< (sh_x + sh_y)))
    have e6 : Exec w (.op (.exactBin .xor 2 2 17) : Code .exact 18) s5 s6 1 :=
      exec_exactBin (by simp +decide [s5, s4, s3, s2, s1, h2]) hfit_acc'
    set s7 := s6.set 15 (y_rem >>> b)
    have e7 : Exec w (.op (.exactBin .shiftRight 15 15 4) : Code .exact 18) s6 s7 1 :=
      exec_exactBin (by simp +decide [s6, s5, s4, s3, s2, s1, h15, h4]) hfit_y_shr
    set s8 := s7.set 16 (sh_x + sh_y + b)
    have e8 : Exec w (.op (.exactBin .add 16 16 4) : Code .exact 18) s7 s8 1 :=
      exec_exactBin (by simp +decide [s7, s6, s5, s4, s3, s2, s1, h16, h4]) hfit_sh_next
    set s9 := s8.set 14 rem_j
    have e9 : Exec w (.op (.exactBin .sub 14 14 8) : Code .exact 18) s8 s9 1 :=
      exec_exactBin (by simp +decide [s8, s7, s6, s5, s4, s3, s2, s1, h14, h8]) hfit_rem
    have hbody := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq e9)))))))
    have hfit_sh' : Fits w (sh_x + (sh_y + b) + rem_j * b) := by
      rwa [show sh_x + (sh_y + b) + rem_j * b = sh_x + sh_y + (rem_j + 1) * b by ring]
    obtain ⟨y, hrec, hy2, hy_regs, hy_mem⟩ :=
      ih (y_rem >>> b) (sh_y + b) (acc ^^^ (clmul xc yc <<< (sh_x + sh_y))) s9
        hy_shr_lt hy_shr_bound hacc'_lt hfit_sh'
        (by simp +decide [s9, s8, s7, s6])
        (by simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, h4])
        (by simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, h5])
        (by simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, h7])
        (by simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, h8])
        (by simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, h9])
        (by simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, h13, xc])
        (by simp +decide [s9])
        (by simp +decide [s9, s8, s7])
        (by simp +decide [s9, s8, Nat.add_assoc])
        htab
    have hiter := Exec.loop_iter hc hbody hrec
    refine ⟨y, ?_, ?_, ?_, hy_mem⟩
    · simpa only [innerClmulLoop, innerClmulBody,
        show 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))) + (11 * rem_j + 2) + 2 =
          11 * (rem_j + 1) + 2 by omega] using hiter
    · rw [hy2, Nat.xor_assoc]
      congr 1
      calc (clmul xc yc <<< (sh_x + sh_y)) ^^^ (clmul xc (y_rem >>> b) <<< (sh_x + (sh_y + b)))
          = (clmul xc yc <<< (sh_x + sh_y)) ^^^
              ((clmul xc (y_rem >>> b) <<< b) <<< (sh_x + sh_y)) := by
            rw [show sh_x + (sh_y + b) = b + (sh_x + sh_y) by omega,
              shiftLeft_add_eq _ b (sh_x + sh_y)]
        _ = (clmul xc yc ^^^ (clmul xc (y_rem >>> b) <<< b)) <<< (sh_x + sh_y) := by
            rw [← xor_shiftLeft_eq]
        _ = clmul xc y_rem <<< (sh_x + sh_y) := by
            rw [← clmul_split_right]
    · intro r hr
      rcases hr with ⟨hr2, hr14, hr15, hr16, hr17⟩
      rw [hy_regs r ⟨hr2, hr14, hr15, hr16, hr17⟩]
      simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, Data.set,
        Function.update_of_ne hr2, Function.update_of_ne hr14,
        Function.update_of_ne hr15, Function.update_of_ne hr16,
        Function.update_of_ne hr17]

/-- Body of `outerClmulLoop`: computes `x_chunk_sh = (x_rem &&& mask_b) <<< b`, initializes the
inner loop over `L` limbs of `u` starting at shift `shift_i`, runs `innerClmulLoop`, and advances
`x_rem`, `shift_i`, and `rem_i`. -/
@[expose] def outerClmulBody : Code .exact 18 :=
  .seq (.op (.exactBin .and 13 11 5))
  (.seq (.op (.exactBin .shiftLeft 13 13 4))
  (.seq (.op (.copy 14 6))
  (.seq (.op (.copy 15 1))
  (.seq (.op (.copy 16 12))
  (.seq innerClmulLoop
  (.seq (.op (.exactBin .shiftRight 11 11 4))
  (.seq (.op (.exactBin .add 12 12 4))
        (.op (.exactBin .sub 10 10 8)))))))))

/-- Outer Four-Russians loop `while 0 < rem_i do outerClmulBody`. -/
@[expose] def outerClmulLoop : Code .exact 18 :=
  .loop (.lt 9 10) outerClmulBody

/-- `outerClmulLoop` executes deterministically in `(11 * L + 12) * rem_i + 2` steps, XORing
`clmul x_rem u <<< sh_x` into `reg 2` (`acc`). -/
theorem outerClmulLoop_exec {w tabBase b q L u : ℕ}
    (hb : 0 < b) (hw : 2 * q ≤ w)
    (hfit_tabEnd : Fits w (tabBase + 2 ^ (2 * b)))
    (hu_limbs : u < 2 ^ (L * b)) (hu_bound : u < 2 ^ q) :
    ∀ rem_i x_rem sh_x acc : ℕ, ∀ s : Data 18,
      x_rem < 2 ^ (rem_i * b) →
      x_rem * 2 ^ sh_x < 2 ^ q →
      acc < 2 ^ (2 * q) →
      Fits w (sh_x + rem_i * b + L * b) →
      s.regs 1 = u →
      s.regs 2 = acc →
      s.regs 4 = b →
      s.regs 5 = 2 ^ b - 1 →
      s.regs 6 = L →
      s.regs 7 = tabBase →
      s.regs 8 = 1 →
      s.regs 9 = 0 →
      s.regs 10 = rem_i →
      s.regs 11 = x_rem →
      s.regs 12 = sh_x →
      (∀ i < 2 ^ (2 * b), s.mem (tabBase + i) = clmul (i >>> b) (i &&& (2 ^ b - 1))) →
      ∃ y : Data 18,
        Exec w outerClmulLoop s y ((11 * L + 12) * rem_i + 2) ∧
        y.regs 2 = acc ^^^ (clmul x_rem u <<< sh_x) ∧
        (∀ r : Fin 18, r.val < 10 ∧ r ≠ 2 → y.regs r = s.regs r) ∧
        y.mem = s.mem := by
  intro rem_i
  induction rem_i with
  | zero =>
    intro x_rem sh_x acc s hx_lt _ _ _ _ h2 _ _ _ _ _ h9 h10 _ _ _
    have hx0 : x_rem = 0 := by
      rw [Nat.zero_mul, pow_zero] at hx_lt
      omega
    have hc : ¬(Cond.lt (9 : Fin 18) 10).Holds s := by
      simp [Cond.Holds, h9, h10]
    refine ⟨s, Exec.loop_exit hc, ?_, fun _ _ => rfl, rfl⟩
    simp [h2, hx0]
  | succ rem_i ih =>
    intro x_rem sh_x acc s hx_lt hx_bound hacc_lt hfit_sh h1 h2 h4 h5 h6 h7 h8 h9 h10 h11 h12 htab
    have hc : (Cond.lt (9 : Fin 18) 10).Holds s := by
      simp [Cond.Holds, h9, h10]
    set xc := x_rem &&& (2 ^ b - 1)
    have hxc_lt : xc < 2 ^ b := by
      dsimp only [xc]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by positivity)
    have hxc_sh_lt : xc <<< b < 2 ^ (2 * b) := by
      rw [Nat.shiftLeft_eq, two_mul, pow_add]
      exact Nat.mul_lt_mul_of_pos_right hxc_lt (by positivity)
    have hpow_le : 2 ^ b ≤ 2 ^ (2 * b) := Nat.pow_le_pow_right (by decide) (by omega)
    have hxc_lt2 : xc < 2 ^ (2 * b) := lt_of_lt_of_le hxc_lt hpow_le
    have hfit_xc : Fits w xc := hfit_tabEnd.of_le (by omega)
    have hfit_xc_sh : Fits w (xc <<< b) := hfit_tabEnd.of_le (by omega)
    set s1 := s.set 13 xc
    have e1 : Exec w (.op (.exactBin .and 13 11 5) : Code .exact 18) s s1 1 :=
      exec_exactBin (by simp [h11, h5, xc]) hfit_xc
    set s2 := s1.set 13 (xc <<< b)
    have e2 : Exec w (.op (.exactBin .shiftLeft 13 13 4) : Code .exact 18) s1 s2 1 :=
      exec_exactBin (by simp +decide [s1, h4]) hfit_xc_sh
    set s3 := s2.set 14 L
    have e3 : Exec w (.op (.copy 14 6) : Code .exact 18) s2 s3 1 := by
      simpa +decide [s3, s2, s1, h6] using
        (Exec.copy (B := .exact) (w := w) (d := 14) (s := 6) (x := s2))
    set s4 := s3.set 15 u
    have e4 : Exec w (.op (.copy 15 1) : Code .exact 18) s3 s4 1 := by
      simpa +decide [s4, s3, s2, s1, h1] using
        (Exec.copy (B := .exact) (w := w) (d := 15) (s := 1) (x := s3))
    set s5 := s4.set 16 sh_x
    have e5 : Exec w (.op (.copy 16 12) : Code .exact 18) s4 s5 1 := by
      simpa +decide [s5, s4, s3, s2, s1, h12] using
        (Exec.copy (B := .exact) (w := w) (d := 16) (s := 12) (x := s4))
    have hfit_inner_sh : Fits w (sh_x + 0 + L * b) :=
      hfit_sh.of_le (by omega)
    obtain ⟨s6, e6, hs6_2, hs6_regs, hs6_mem⟩ :=
      innerClmulLoop_exec hb hw hfit_tabEnd hx_bound L u 0 acc s5
        hu_limbs (by simpa using hu_bound) hacc_lt hfit_inner_sh
        (by simp +decide [s5, s4, s3, s2, s1, h2])
        (by simp +decide [s5, s4, s3, s2, s1, h4])
        (by simp +decide [s5, s4, s3, s2, s1, h5])
        (by simp +decide [s5, s4, s3, s2, s1, h7])
        (by simp +decide [s5, s4, s3, s2, s1, h8])
        (by simp +decide [s5, s4, s3, s2, s1, h9])
        (by simp +decide [s5, s4, s3, s2, xc])
        (by simp +decide [s5, s4, s3])
        (by simp +decide [s5, s4])
        (by simp +decide [s5])
        htab
    rw [Nat.add_zero] at hs6_2
    have hs6_4 : s6.regs 4 = b := by
      rw [hs6_regs 4 (by decide)]
      simp +decide [s5, s4, s3, s2, s1, h4]
    have hs6_8 : s6.regs 8 = 1 := by
      rw [hs6_regs 8 (by decide)]
      simp +decide [s5, s4, s3, s2, s1, h8]
    have hs6_10 : s6.regs 10 = rem_i + 1 := by
      rw [hs6_regs 10 (by decide)]
      simp +decide [s5, s4, s3, s2, s1, h10]
    have hs6_11 : s6.regs 11 = x_rem := by
      rw [hs6_regs 11 (by decide)]
      simp +decide [s5, s4, s3, s2, s1, h11]
    have hs6_12 : s6.regs 12 = sh_x := by
      rw [hs6_regs 12 (by decide)]
      simp +decide [s5, s4, s3, s2, s1, h12]
    have hx_shr_lt : x_rem >>> b < 2 ^ (rem_i * b) := shiftRight_lt_two_pow_mul hx_lt
    have hx_shr_bound : (x_rem >>> b) * 2 ^ (sh_x + b) < 2 ^ q :=
      (shiftRight_mul_two_pow_add_le x_rem b sh_x).trans_lt hx_bound
    have hx_shr_lt_2q : x_rem >>> b < 2 ^ (2 * q) := by
      have hx_lt_q : x_rem < 2 ^ q :=
        (Nat.le_mul_of_pos_right _ (by positivity)).trans_lt hx_bound
      exact (Nat.shiftRight_le x_rem b).trans_lt
        (lt_of_lt_of_le hx_lt_q (Nat.pow_le_pow_right (by decide) (by omega)))
    have hfit_x_shr : Fits w (x_rem >>> b) := fits_of_lt_two_pow_two_mul hw hx_shr_lt_2q
    have hfit_sh_next : Fits w (sh_x + b) :=
      hfit_sh.of_le (by rw [Nat.succ_mul]; omega)
    have hfit_rem_i : Fits w rem_i := by
      have : rem_i * 1 ≤ (rem_i + 1) * b := Nat.mul_le_mul (by omega) hb
      exact hfit_sh.of_le (by omega)
    set s7 := s6.set 11 (x_rem >>> b)
    have e7 : Exec w (.op (.exactBin .shiftRight 11 11 4) : Code .exact 18) s6 s7 1 :=
      exec_exactBin (by simp +decide [hs6_11, hs6_4]) hfit_x_shr
    set s8 := s7.set 12 (sh_x + b)
    have e8 : Exec w (.op (.exactBin .add 12 12 4) : Code .exact 18) s7 s8 1 :=
      exec_exactBin (by simp +decide [s7, hs6_12, hs6_4]) hfit_sh_next
    set s9 := s8.set 10 rem_i
    have e9 : Exec w (.op (.exactBin .sub 10 10 8) : Code .exact 18) s8 s9 1 :=
      exec_exactBin (by simp +decide [s8, s7, hs6_10, hs6_8]) hfit_rem_i
    have hbody := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq e9)))))))
    have hcl_xc_u_lt : clmul xc u <<< sh_x < 2 ^ (2 * q) := by
      rcases eq_or_ne xc 0 with hxc0 | hxc0
      · simp [hxc0]
      · have hxc_q : xc * 2 ^ sh_x < 2 ^ q :=
          (Nat.mul_le_mul_right (2 ^ sh_x) Nat.and_le_left).trans_lt hx_bound
        obtain ⟨hsx, hxc'⟩ := lt_two_pow_sub_of_mul_two_pow_lt (Nat.pos_of_ne_zero hxc0) hxc_q
        have hcl := clmul_lt_two_pow hxc' hu_bound
        rw [Nat.shiftLeft_eq]
        calc clmul xc u * 2 ^ sh_x
            < 2 ^ (q - sh_x + q) * 2 ^ sh_x := Nat.mul_lt_mul_of_pos_right hcl (by positivity)
          _ = 2 ^ (2 * q) := by
              rw [← pow_add]
              congr 1
              omega
    have hacc'_lt : acc ^^^ (clmul xc u <<< sh_x) < 2 ^ (2 * q) :=
      Nat.xor_lt_two_pow hacc_lt hcl_xc_u_lt
    have hfit_sh' : Fits w (sh_x + b + rem_i * b + L * b) := by
      rwa [show sh_x + b + rem_i * b + L * b = sh_x + (rem_i + 1) * b + L * b by ring]
    have hs9_low : ∀ r : Fin 18, r.val < 10 ∧ r ≠ 2 → s9.regs r = s.regs r := by
      intro r ⟨hr_lt, hr2⟩
      have hr10 : r ≠ 10 := by omega
      have hr11 : r ≠ 11 := by omega
      have hr12 : r ≠ 12 := by omega
      have hr13 : r ≠ 13 := by omega
      have hr14 : r ≠ 14 := by omega
      have hr15 : r ≠ 15 := by omega
      have hr16 : r ≠ 16 := by omega
      have hr17 : r ≠ 17 := by omega
      calc s9.regs r = s6.regs r := by
            simp only [s9, s8, s7, Data.set,
              Function.update_of_ne hr10, Function.update_of_ne hr11, Function.update_of_ne hr12]
        _ = s5.regs r := hs6_regs r ⟨hr2, hr14, hr15, hr16, hr17⟩
        _ = s.regs r := by
            simp only [s5, s4, s3, s2, s1, Data.set,
              Function.update_of_ne hr13, Function.update_of_ne hr14,
              Function.update_of_ne hr15, Function.update_of_ne hr16]
    have hs9_2 : s9.regs 2 = acc ^^^ (clmul xc u <<< sh_x) := by
      change s6.regs 2 = acc ^^^ (clmul xc u <<< sh_x)
      exact hs6_2
    obtain ⟨y, hrec, hy2, hy_regs, hy_mem⟩ :=
      ih (x_rem >>> b) (sh_x + b) (acc ^^^ (clmul xc u <<< sh_x)) s9
        hx_shr_lt hx_shr_bound hacc'_lt hfit_sh'
        (by rw [hs9_low 1 ⟨by decide, by decide⟩, h1])
        hs9_2
        (by rw [hs9_low 4 ⟨by decide, by decide⟩, h4])
        (by rw [hs9_low 5 ⟨by decide, by decide⟩, h5])
        (by rw [hs9_low 6 ⟨by decide, by decide⟩, h6])
        (by rw [hs9_low 7 ⟨by decide, by decide⟩, h7])
        (by rw [hs9_low 8 ⟨by decide, by decide⟩, h8])
        (by rw [hs9_low 9 ⟨by decide, by decide⟩, h9])
        (by simp +decide [s9])
        (by simp +decide [s9, s8, s7])
        (by simp +decide [s9, s8])
        (by rw [show s9.mem = s.mem from hs6_mem]; exact htab)
    have hiter := Exec.loop_iter hc hbody hrec
    refine ⟨y, ?_, ?_, ?_, by rw [hy_mem]; exact hs6_mem⟩
    · simpa only [outerClmulLoop, outerClmulBody,
        show 1 + (1 + (1 + (1 + (1 + ((11 * L + 2) + (1 + (1 + 1))))))) +
          ((11 * L + 12) * rem_i + 2) + 2 = (11 * L + 12) * (rem_i + 1) + 2 by ring] using hiter
    · rw [hy2, Nat.xor_assoc]
      congr 1
      calc (clmul xc u <<< sh_x) ^^^ (clmul (x_rem >>> b) u <<< (sh_x + b))
          = (clmul xc u <<< sh_x) ^^^ ((clmul (x_rem >>> b) u <<< b) <<< sh_x) := by
            rw [show sh_x + b = b + sh_x by omega, shiftLeft_add_eq _ b sh_x]
        _ = (clmul xc u ^^^ (clmul (x_rem >>> b) u <<< b)) <<< sh_x := by
            rw [← xor_shiftLeft_eq]
        _ = clmul x_rem u <<< sh_x := by
            rw [← clmul_split_left]
    · intro r hr
      rw [hy_regs r hr, hs9_low r hr]

/-- 16-instruction straight-line reduction block on `Data 18`: loads `r`, `q = 2 * r`,
`2 ^ r - 1`, and `2 ^ q - 1` from `base + 0 .. base + 3` into registers `10..13` and replaces `c`
in `reg 2` with `reduceTrinomialCode (trinomialStep U M) c`, preserving registers `0, 1, 3..9` and
memory. -/
@[expose] def reduceStepCode : Code .exact 18 :=
  .seq (.op (.load 10 0))
  (.seq (.op (.exactBin .add 15 0 8))
  (.seq (.op (.load 11 15))
  (.seq (.op (.exactBin .add 15 15 8))
  (.seq (.op (.load 12 15))
  (.seq (.op (.exactBin .add 15 15 8))
  (.seq (.op (.load 13 15))
  (.seq (.op (.exactBin .add 14 11 10))
  (.seq (.op (.exactBin .shiftRight 15 2 14))
  (.seq (.op (.exactBin .shiftRight 16 2 11))
  (.seq (.op (.exactBin .and 16 16 12))
  (.seq (.op (.exactBin .and 2 2 13))
  (.seq (.op (.exactBin .xor 2 2 15))
  (.seq (.op (.exactBin .xor 2 2 16))
  (.seq (.op (.exactBin .shiftLeft 16 16 10))
        (.op (.exactBin .xor 2 2 16))))))))))))))))

/-- `reduceStepCode` executes deterministically in `16` instructions, replacing `c` in `reg 2`
with `reduceTrinomialCode (trinomialStep U M) c`. -/
theorem reduceStepCode_exec {w base b U M k c : ℕ} {s : Data 18}
    (htab : TableRep base b U M k s.mem)
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_end8 : Fits w (base + 8))
    (hc : c < 2 ^ (2 * trinomialDeg U M))
    (h0 : s.regs 0 = base) (h2 : s.regs 2 = c) (h8 : s.regs 8 = 1) :
    ∃ y : Data 18,
      Exec w reduceStepCode s y 16 ∧
      y.regs 2 = reduceTrinomialCode (trinomialStep U M) c ∧
      (∀ r : Fin 18, r.val < 10 ∧ r ≠ 2 → y.regs r = s.regs r) ∧
      y.mem = s.mem := by
  set t := trinomialStep U M
  set r := 3 ^ t
  set q := trinomialDeg U M
  have hq_eq : q = 2 * r := rfl
  have hm0 : s.mem base = r := htab.1
  have hm1 : s.mem (base + 1) = q := htab.2.1
  have hm2 : s.mem (base + 2) = 2 ^ r - 1 := htab.2.2.1
  have hm3 : s.mem (base + 3) = 2 ^ q - 1 := htab.2.2.2.1
  have hfit_b1 : Fits w (base + 1) := hfit_end8.of_le (by omega)
  have hfit_b2 : Fits w (base + 2) := hfit_end8.of_le (by omega)
  have hfit_b3 : Fits w (base + 3) := hfit_end8.of_le (by omega)
  have h3r_lt : q + r < 2 ^ (2 * q) := by
    have : 1 ≤ r := Nat.one_le_pow t 3 (by decide)
    have h2q : q + r ≤ 2 * q := by omega
    exact lt_of_le_of_lt h2q Nat.lt_two_pow_self
  have hfit_3r : Fits w (q + r) := fits_of_lt_two_pow_two_mul hw h3r_lt
  set c3 := c >>> (q + r)
  set c2_raw := c >>> q
  set c2 := c2_raw &&& (2 ^ r - 1)
  set cLow := c &&& (2 ^ q - 1)
  have hfit_c : Fits w c := fits_of_lt_two_pow_two_mul hw hc
  have hfit_c3 : Fits w c3 := hfit_c.of_le (Nat.shiftRight_le _ _)
  have hfit_c2_raw : Fits w c2_raw := hfit_c.of_le (Nat.shiftRight_le _ _)
  have hfit_c2 : Fits w c2 := hfit_c2_raw.of_le Nat.and_le_left
  have hfit_cLow : Fits w cLow := hfit_c.of_le Nat.and_le_left
  have hcLow_lt : cLow < 2 ^ q := by
    dsimp only [cLow]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hc3_lt : c3 < 2 ^ q := by
    have hlt : c >>> (q + r) < 2 ^ r := by
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      rw [← pow_add 2 (q + r) r, show q + r + r = 2 * q by omega]
      exact hc
    exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
  have hc2_r_lt : c2 < 2 ^ r := by
    dsimp only [c2]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hc2_lt : c2 < 2 ^ q :=
    lt_of_lt_of_le hc2_r_lt (Nat.pow_le_pow_right (by decide) (by omega))
  have hc2_sh_lt : c2 <<< r < 2 ^ q := by
    rw [Nat.shiftLeft_eq, hq_eq, two_mul, pow_add]
    exact Nat.mul_lt_mul_of_pos_right hc2_r_lt (by positivity)
  have hpow_q_le : 2 ^ q ≤ 2 ^ (2 * q) := Nat.pow_le_pow_right (by decide) (by omega)
  have hfit_xor1 : Fits w (cLow ^^^ c3) :=
    fits_of_lt_two_pow_two_mul hw ((Nat.xor_lt_two_pow hcLow_lt hc3_lt).trans_le hpow_q_le)
  have hfit_xor2 : Fits w ((cLow ^^^ c3) ^^^ c2) :=
    fits_of_lt_two_pow_two_mul hw
      ((Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hcLow_lt hc3_lt) hc2_lt).trans_le hpow_q_le)
  have hfit_c2_sh : Fits w (c2 <<< r) :=
    fits_of_lt_two_pow_two_mul hw (hc2_sh_lt.trans_le hpow_q_le)
  have hfit_xor3 : Fits w (((cLow ^^^ c3) ^^^ c2) ^^^ (c2 <<< r)) :=
    fits_of_lt_two_pow_two_mul hw
      ((Nat.xor_lt_two_pow
        (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hcLow_lt hc3_lt) hc2_lt) hc2_sh_lt).trans_le
        hpow_q_le)
  set s1 := s.set 10 r
  have e1 : Exec w (.op (.load 10 0) : Code .exact 18) s s1 1 := by
    simpa +decide [s1, h0, hm0] using (Exec.load (B := .exact) (w := w) (d := 10) (a := 0) (x := s))
  set s2 := s1.set 15 (base + 1)
  have e2 : Exec w (.op (.exactBin .add 15 0 8) : Code .exact 18) s1 s2 1 :=
    exec_exactBin (by simp +decide [s1, h0, h8]) hfit_b1
  set s3 := s2.set 11 q
  have e3 : Exec w (.op (.load 11 15) : Code .exact 18) s2 s3 1 := by
    simpa +decide [s3, s2, s1, hm1] using
      (Exec.load (B := .exact) (w := w) (d := 11) (a := 15) (x := s2))
  set s4 := s3.set 15 (base + 2)
  have e4 : Exec w (.op (.exactBin .add 15 15 8) : Code .exact 18) s3 s4 1 :=
    exec_exactBin (by simp +decide [s3, s2, s1, h8, Nat.add_assoc]) hfit_b2
  set s5 := s4.set 12 (2 ^ r - 1)
  have e5 : Exec w (.op (.load 12 15) : Code .exact 18) s4 s5 1 := by
    simpa +decide [s5, s4, s3, s2, s1, hm2] using
      (Exec.load (B := .exact) (w := w) (d := 12) (a := 15) (x := s4))
  set s6 := s5.set 15 (base + 3)
  have e6 : Exec w (.op (.exactBin .add 15 15 8) : Code .exact 18) s5 s6 1 :=
    exec_exactBin (by simp +decide [s5, s4, s3, s2, s1, h8, Nat.add_assoc]) hfit_b3
  set s7 := s6.set 13 (2 ^ q - 1)
  have e7 : Exec w (.op (.load 13 15) : Code .exact 18) s6 s7 1 := by
    simpa +decide [s7, s6, s5, s4, s3, s2, s1, hm3] using
      (Exec.load (B := .exact) (w := w) (d := 13) (a := 15) (x := s6))
  set s8 := s7.set 14 (q + r)
  have e8 : Exec w (.op (.exactBin .add 14 11 10) : Code .exact 18) s7 s8 1 :=
    exec_exactBin (by simp +decide [s7, s6, s5, s4, s3, s2, s1]) hfit_3r
  set s9 := s8.set 15 c3
  have e9 : Exec w (.op (.exactBin .shiftRight 15 2 14) : Code .exact 18) s8 s9 1 :=
    exec_exactBin (by simp +decide [s8, s7, s6, s5, s4, s3, s2, s1, h2, c3]) hfit_c3
  set s10 := s9.set 16 c2_raw
  have e10 : Exec w (.op (.exactBin .shiftRight 16 2 11) : Code .exact 18) s9 s10 1 :=
    exec_exactBin (by simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, h2, c2_raw]) hfit_c2_raw
  set s11 := s10.set 16 c2
  have e11 : Exec w (.op (.exactBin .and 16 16 12) : Code .exact 18) s10 s11 1 :=
    exec_exactBin (by simp +decide [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, c2]) hfit_c2
  set s12 := s11.set 2 cLow
  have e12 : Exec w (.op (.exactBin .and 2 2 13) : Code .exact 18) s11 s12 1 :=
    exec_exactBin (by simp +decide [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h2, cLow])
      hfit_cLow
  set s13 := s12.set 2 (cLow ^^^ c3)
  have e13 : Exec w (.op (.exactBin .xor 2 2 15) : Code .exact 18) s12 s13 1 :=
    exec_exactBin (by simp +decide [s12, s11, s10, s9]) hfit_xor1
  set s14 := s13.set 2 ((cLow ^^^ c3) ^^^ c2)
  have e14 : Exec w (.op (.exactBin .xor 2 2 16) : Code .exact 18) s13 s14 1 :=
    exec_exactBin (by simp +decide [s13, s12, s11]) hfit_xor2
  set s15 := s14.set 16 (c2 <<< r)
  have e15 : Exec w (.op (.exactBin .shiftLeft 16 16 10) : Code .exact 18) s14 s15 1 :=
    exec_exactBin (by simp +decide [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1])
      hfit_c2_sh
  set s16 := s15.set 2 (((cLow ^^^ c3) ^^^ c2) ^^^ (c2 <<< r))
  have e16 : Exec w (.op (.exactBin .xor 2 2 16) : Code .exact 18) s15 s16 1 :=
    exec_exactBin (by simp +decide [s15, s14]) hfit_xor3
  have hall :=
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq (e10.seq
      (e11.seq (e12.seq (e13.seq (e14.seq (e15.seq e16))))))))))))))
  refine ⟨s16, hall, ?_, ?_, rfl⟩
  · simp only [s16, Data.set, Function.update_self, reduceTrinomialCode,
      cLow, c3, c2, c2_raw, q, trinomialDeg, r, t,
      show 2 * 3 ^ trinomialStep U M + 3 ^ trinomialStep U M = 3 * 3 ^ trinomialStep U M by ring]
  · intro reg ⟨hreg_lt, hreg2⟩
    have hr10 : reg ≠ 10 := by omega
    have hr11 : reg ≠ 11 := by omega
    have hr12 : reg ≠ 12 := by omega
    have hr13 : reg ≠ 13 := by omega
    have hr14 : reg ≠ 14 := by omega
    have hr15 : reg ≠ 15 := by omega
    have hr16 : reg ≠ 16 := by omega
    simp only [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Data.set,
      Function.update_of_ne hreg2, Function.update_of_ne hr10, Function.update_of_ne hr11,
      Function.update_of_ne hr12, Function.update_of_ne hr13, Function.update_of_ne hr14,
      Function.update_of_ne hr15, Function.update_of_ne hr16]

/-- Body of `hornerLoop` on `Data 18`: decrements `j` (`reg 3`), multiplies `acc` (`reg 2`) by
`u` (`reg 1`) in `TrinomialField (trinomialStep U M)` via `outerClmulLoop` and `reduceStepCode`,
and adds `seed[j]` from `mem[base + 8 + j]`. -/
@[expose] def hornerBody : Code .exact 18 :=
  .seq (.op (.exactBin .sub 3 3 8))
  (.seq (.op (.copy 11 2))
  (.seq (.op (.copy 2 9))
  (.seq (.op (.copy 10 6))
  (.seq (.op (.copy 12 9))
  (.seq outerClmulLoop
  (.seq reduceStepCode
  (.seq (.op (.const 15 8))
  (.seq (.op (.exactBin .add 15 0 15))
  (.seq (.op (.exactBin .add 15 15 3))
  (.seq (.op (.load 15 15))
        (.op (.exactBin .xor 2 2 15))))))))))))

/-- Horner evaluation loop `while 0 < j do hornerBody`. -/
@[expose] def hornerLoop : Code .exact 18 :=
  .loop (.lt 9 3) hornerBody

/-- `hornerLoop` executes deterministically in `((11 * L + 12) * L + 30) * m + 2` instructions,
updating `reg 2` from `(equivFin t acc).val` to
`(equivFin t (acc * x ^ m + ∑ i : Fin m, c_field (Fin.castLE hm i) * x ^ (i : ℕ))).val`. -/
theorem hornerLoop_exec {w base b U M k : ℕ}
    {c : Fin k → Fin (2 ^ trinomialDeg U M)} (u : Fin U)
    (hb : 0 < b) (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + spaceFromB b k)) :
    let t := trinomialStep U M
    let q := trinomialDeg U M
    let L := limbCountFromB b q
    let c_field : Fin k → TrinomialField t := fun j => (TrinomialField.equivFin t).symm (c j)
    let x_field : TrinomialField t := AdjoinRoot.mk (trinomial t) (polyOfCode u.val)
    ∀ m : ℕ, ∀ hm : m ≤ k, ∀ acc : TrinomialField t, ∀ s : Data 18,
      Rep base b U M k c s.mem →
      s.regs 0 = base →
      s.regs 1 = u.val →
      s.regs 2 = (TrinomialField.equivFin t acc).val →
      s.regs 3 = m →
      s.regs 4 = b →
      s.regs 5 = 2 ^ b - 1 →
      s.regs 6 = L →
      s.regs 7 = base + 8 + k →
      s.regs 8 = 1 →
      s.regs 9 = 0 →
      ∃ y : Data 18,
        Exec w hornerLoop s y (((11 * L + 12) * L + 30) * m + 2) ∧
        y.regs 0 = base ∧
        y.regs 1 = u.val ∧
        y.regs 2 = (TrinomialField.equivFin t
          (acc * x_field ^ m + ∑ i : Fin m, c_field (Fin.castLE hm i) * x_field ^ (i : ℕ))).val ∧
        y.mem = s.mem := by
  intro t q L c_field x_field m
  induction m with
  | zero =>
    intro hm acc s _ h0 h1 h2 h3 _ _ _ _ _ h9
    have hc : ¬(Cond.lt (9 : Fin 18) 3).Holds s := by
      simp [Cond.Holds, h9, h3]
    refine ⟨s, Exec.loop_exit hc, h0, h1, ?_, rfl⟩
    simp [h2]
  | succ m ih =>
    intro hm acc s hrep h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    have hc : (Cond.lt (9 : Fin 18) 3).Holds s := by
      simp [Cond.Holds, h9, h3]
    obtain ⟨htab, hseed⟩ := hrep
    have hpow_pos : 0 < 2 ^ (2 * b) := by positivity
    have hfit_tabEnd : Fits w (base + 8 + k + 2 ^ (2 * b)) :=
      hfit_space.of_le (by dsimp only [spaceFromB]; omega)
    have hfit_end8 : Fits w (base + 8) :=
      hfit_space.of_le (by dsimp only [spaceFromB]; omega)
    have hfit_end_k : Fits w (base + 8 + k) :=
      hfit_space.of_le (by dsimp only [spaceFromB]; omega)
    have hfit_m : Fits w m := hfit_end_k.of_le (by omega)
    have hq_le_Lb : q ≤ L * b := le_limbCountFromB_mul hb q
    have hpow_q_Lb : 2 ^ q ≤ 2 ^ (L * b) := Nat.pow_le_pow_right (by decide) hq_le_Lb
    have hu_bound : u.val < 2 ^ q :=
      lt_of_lt_of_le u.isLt (le_two_pow_trinomialDeg U M)
    have hu_limbs : u.val < 2 ^ (L * b) := lt_of_lt_of_le hu_bound hpow_q_Lb
    set acc_val := (TrinomialField.equivFin t acc).val
    have hacc_bound : acc_val < 2 ^ q := (TrinomialField.equivFin t acc).isLt
    have hacc_limbs : acc_val < 2 ^ (L * b) := lt_of_lt_of_le hacc_bound hpow_q_Lb
    have hLb_le : L * b ≤ q + b := by
      dsimp only [L, limbCountFromB]
      have := Nat.div_mul_le_self (q + b - 1) b
      omega
    have h2b_lt_w : 2 * b < w := by
      apply (Nat.pow_lt_pow_iff_right one_lt_two).mp
      exact lt_of_le_of_lt (by dsimp only [spaceFromB]; omega) hfit_space
    have hq_ge_2 : 2 ≤ q := by
      dsimp only [q, trinomialDeg]
      have : 1 ≤ 3 ^ trinomialStep U M := Nat.one_le_pow _ 3 (by decide)
      omega
    have hw_pos : 1 ≤ w := by omega
    have hw_le_pow : w ≤ 2 ^ (w - 1) := by
      have hlt : w - 1 < 2 ^ (w - 1) := Nat.lt_two_pow_self
      omega
    have h2b_lt_pow : 2 * b < 2 ^ (w - 1) :=
      calc 2 * b < 2 ^ (2 * b) := Nat.lt_two_pow_self
        _ ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hpow_w_eq : 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := by
      conv_rhs => rw [← Nat.sub_add_cancel hw_pos, pow_succ]
      omega
    have hfit_2Lb : Fits w (0 + L * b + L * b) := by
      dsimp only [Fits]
      omega
    set s1 := s.set 3 m
    have e1 : Exec w (.op (.exactBin .sub 3 3 8) : Code .exact 18) s s1 1 :=
      exec_exactBin (by simp +decide [h3, h8]) hfit_m
    set s2 := s1.set 11 acc_val
    have e2 : Exec w (.op (.copy 11 2) : Code .exact 18) s1 s2 1 := by
      simpa +decide [s2, s1, h2, acc_val] using
        (Exec.copy (B := .exact) (w := w) (d := 11) (s := 2) (x := s1))
    set s3 := s2.set 2 0
    have e3 : Exec w (.op (.copy 2 9) : Code .exact 18) s2 s3 1 := by
      simpa +decide [s3, s2, s1, h9] using
        (Exec.copy (B := .exact) (w := w) (d := 2) (s := 9) (x := s2))
    set s4 := s3.set 10 L
    have e4 : Exec w (.op (.copy 10 6) : Code .exact 18) s3 s4 1 := by
      simpa +decide [s4, s3, s2, s1, h6] using
        (Exec.copy (B := .exact) (w := w) (d := 10) (s := 6) (x := s3))
    set s5 := s4.set 12 0
    have e5 : Exec w (.op (.copy 12 9) : Code .exact 18) s4 s5 1 := by
      simpa +decide [s5, s4, s3, s2, s1, h9] using
        (Exec.copy (B := .exact) (w := w) (d := 12) (s := 9) (x := s4))
    obtain ⟨s6, e6, hs6_2, hs6_low, hs6_mem⟩ :=
      outerClmulLoop_exec hb hw hfit_tabEnd hu_limbs hu_bound L acc_val 0 0 s5
        hacc_limbs (by simpa using hacc_bound) (by positivity) hfit_2Lb
        (by simp +decide [s5, s4, s3, s2, s1, h1])
        (by simp +decide [s5, s4, s3])
        (by simp +decide [s5, s4, s3, s2, s1, h4])
        (by simp +decide [s5, s4, s3, s2, s1, h5])
        (by simp +decide [s5, s4, s3, s2, s1, h6])
        (by simp +decide [s5, s4, s3, s2, s1, h7])
        (by simp +decide [s5, s4, s3, s2, s1, h8])
        (by simp +decide [s5, s4, s3, s2, s1, h9])
        (by simp +decide [s5, s4])
        (by simp +decide [s5, s4, s3, s2])
        (by simp +decide [s5])
        htab.2.2.2.2.2.2.2.2
    simp only [Nat.shiftLeft_zero, Nat.zero_xor] at hs6_2
    have hcl_lt : clmul acc_val u.val < 2 ^ (2 * q) :=
      clmul_lt_two_pow_two_mul hacc_bound hu_bound
    have hs6_0 : s6.regs 0 = base := by
      rw [hs6_low 0 ⟨by decide, by decide⟩]
      simp +decide [s5, s4, s3, s2, s1, h0]
    have hs6_8 : s6.regs 8 = 1 := by
      rw [hs6_low 8 ⟨by decide, by decide⟩]
      simp +decide [s5, s4, s3, s2, s1, h8]
    have htab_s6 : TableRep base b U M k s6.mem := by
      rw [hs6_mem]
      exact htab
    obtain ⟨s7, e7, hs7_2, hs7_low, hs7_mem⟩ :=
      reduceStepCode_exec htab_s6 hw hfit_end8 hcl_lt hs6_0 hs6_2 hs6_8
    have hs7_low_eq : ∀ r : Fin 18, r.val < 10 ∧ r ≠ 2 → s7.regs r = s5.regs r := by
      intro r hr
      rw [hs7_low r hr, hs6_low r hr]
    have hs7_0 : s7.regs 0 = base := by
      rw [hs7_low_eq 0 ⟨by decide, by decide⟩]
      simp +decide [s5, s4, s3, s2, s1, h0]
    have hs7_3 : s7.regs 3 = m := by
      rw [hs7_low_eq 3 ⟨by decide, by decide⟩]
      simp +decide [s5, s4, s3, s2, s1]
    have hfit_8 : Fits w 8 := hfit_end8.of_le (by omega)
    have hfit_b8m : Fits w (base + 8 + m) := hfit_end_k.of_le (by omega)
    have hm_lt : m < k := by omega
    have hmem_seed : s7.mem (base + 8 + m) = (c ⟨m, hm_lt⟩).val := by
      rw [hs7_mem, hs6_mem]
      exact hseed ⟨m, hm_lt⟩
    have hx_val : (TrinomialField.equivFin t x_field).val = u.val :=
      TrinomialField.val_equivFin_mk_polyOfCode t hu_bound
    have hmul_val : reduceTrinomialCode t (clmul acc_val u.val) =
        (TrinomialField.equivFin t (acc * x_field)).val := by
      rw [TrinomialField.val_equivFin_mul, hx_val]
    have hseed_val : (c ⟨m, hm_lt⟩).val =
        (TrinomialField.equivFin t (c_field ⟨m, hm_lt⟩)).val := by
      have h : TrinomialField.equivFin t (c_field ⟨m, hm_lt⟩) = c ⟨m, hm_lt⟩ :=
        (TrinomialField.equivFin t).apply_symm_apply (c ⟨m, hm_lt⟩)
      exact (congrArg Fin.val h).symm
    set acc_next := acc * x_field + c_field ⟨m, hm_lt⟩
    have hxor_val : reduceTrinomialCode t (clmul acc_val u.val) ^^^ (c ⟨m, hm_lt⟩).val =
        (TrinomialField.equivFin t acc_next).val := by
      rw [hmul_val, hseed_val, ← TrinomialField.val_equivFin_add]
    have hacc_next_lt_q : (TrinomialField.equivFin t acc_next).val < 2 ^ q :=
      (TrinomialField.equivFin t acc_next).isLt
    have hfit_acc_next : Fits w (TrinomialField.equivFin t acc_next).val :=
      fits_of_lt_two_pow_two_mul hw
        (lt_of_lt_of_le hacc_next_lt_q
          (Nat.pow_le_pow_right (by decide) (by omega)))
    set s8 := s7.set 15 8
    have e8 : Exec w (.op (.const 15 8) : Code .exact 18) s7 s8 1 := Exec.const hfit_8
    set s9 := s8.set 15 (base + 8)
    have e9 : Exec w (.op (.exactBin .add 15 0 15) : Code .exact 18) s8 s9 1 :=
      exec_exactBin (by simp +decide [s8, hs7_0]) hfit_end8
    set s10 := s9.set 15 (base + 8 + m)
    have e10 : Exec w (.op (.exactBin .add 15 15 3) : Code .exact 18) s9 s10 1 :=
      exec_exactBin (by simp +decide [s9, s8, hs7_3]) hfit_b8m
    set s11 := s10.set 15 (c ⟨m, hm_lt⟩).val
    have e11 : Exec w (.op (.load 15 15) : Code .exact 18) s10 s11 1 := by
      simpa +decide [s11, s10, s9, s8, hmem_seed] using
        (Exec.load (B := .exact) (w := w) (d := 15) (a := 15) (x := s10))
    set s12 := s11.set 2 (TrinomialField.equivFin t acc_next).val
    have e12 : Exec w (.op (.exactBin .xor 2 2 15) : Code .exact 18) s11 s12 1 :=
      exec_exactBin (by simp +decide [s11, s10, s9, s8, hs7_2, t, hxor_val]) hfit_acc_next
    have hbody :=
      e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq (e10.seq
        (e11.seq e12))))))))))
    have hs12_low : ∀ r : Fin 18, r.val < 10 ∧ r ≠ 2 → s12.regs r = s5.regs r := by
      intro r ⟨hr_lt, hr2⟩
      have hr15 : r ≠ 15 := by omega
      calc s12.regs r = s7.regs r := by
            simp only [s12, s11, s10, s9, s8, Data.set,
              Function.update_of_ne hr2, Function.update_of_ne hr15]
        _ = s5.regs r := hs7_low_eq r ⟨hr_lt, hr2⟩
    have hs12_mem : s12.mem = s.mem := by
      change s7.mem = s.mem
      rw [hs7_mem, hs6_mem]
      rfl
    have hm_le : m ≤ k := Nat.le_of_succ_le hm
    obtain ⟨y, hrec, hy0, hy1, hy2, hy_mem⟩ :=
      ih hm_le acc_next s12
        (by rw [hs12_mem]; exact ⟨htab, hseed⟩)
        (by rw [hs12_low 0 ⟨by decide, by decide⟩]; simp +decide [s5, s4, s3, s2, s1, h0])
        (by rw [hs12_low 1 ⟨by decide, by decide⟩]; simp +decide [s5, s4, s3, s2, s1, h1])
        (by simp only [s12, Data.set, Function.update_self])
        (by rw [hs12_low 3 ⟨by decide, by decide⟩]; simp +decide [s5, s4, s3, s2, s1])
        (by rw [hs12_low 4 ⟨by decide, by decide⟩]; simp +decide [s5, s4, s3, s2, s1, h4])
        (by rw [hs12_low 5 ⟨by decide, by decide⟩]; simp +decide [s5, s4, s3, s2, s1, h5])
        (by rw [hs12_low 6 ⟨by decide, by decide⟩]; simp +decide [s5, s4, s3, s2, s1, h6])
        (by rw [hs12_low 7 ⟨by decide, by decide⟩]; simp +decide [s5, s4, s3, s2, s1, h7])
        (by rw [hs12_low 8 ⟨by decide, by decide⟩]; simp +decide [s5, s4, s3, s2, s1, h8])
        (by rw [hs12_low 9 ⟨by decide, by decide⟩]; simp +decide [s5, s4, s3, s2, s1, h9])
    have hiter := Exec.loop_iter hc hbody hrec
    refine ⟨y, ?_, hy0, hy1, ?_, by rw [hy_mem, hs12_mem]⟩
    · simpa only [hornerLoop, hornerBody,
        show 1 + (1 + (1 + (1 + (1 + (((11 * L + 12) * L + 2) +
          (16 + (1 + (1 + (1 + (1 + 1)))))))))) + (((11 * L + 12) * L + 30) * m + 2) + 2 =
          ((11 * L + 12) * L + 30) * (m + 1) + 2 by ring] using hiter
    · rw [hy2]
      congr 2
      rw [Fin.sum_univ_castSucc]
      simp only [acc_next, Fin.val_castSucc, Fin.val_last, pow_succ]
      have hcast : ∀ i : Fin m, Fin.castLE hm i.castSucc = Fin.castLE hm_le i :=
        fun _ => rfl
      have hlast : Fin.castLE hm (Fin.last m) = ⟨m, hm_lt⟩ := rfl
      simp only [hcast, hlast]
      ring

/-- 13-instruction setup block for `evalCode k`: initializes `reg 8 = 1`, `reg 9 = 0`,
`reg 2 = 0`, `reg 3 = k`, loads `b`, `2 ^ b - 1`, `L` from `base + 5 .. base + 7` into `reg 4..6`,
and sets `reg 7 = base + 8 + k`. -/
@[expose] def evalSetupCode (k : ℕ) : Code .exact 18 :=
  .seq (.op (.const 8 1))
  (.seq (.op (.const 9 0))
  (.seq (.op (.copy 2 9))
  (.seq (.op (.const 3 k))
  (.seq (.op (.const 15 5))
  (.seq (.op (.exactBin .add 15 0 15))
  (.seq (.op (.load 4 15))
  (.seq (.op (.exactBin .add 15 15 8))
  (.seq (.op (.load 5 15))
  (.seq (.op (.exactBin .add 15 15 8))
  (.seq (.op (.load 6 15))
  (.seq (.op (.const 7 (8 + k)))
        (.op (.exactBin .add 7 0 7)))))))))))))

/-- 4-instruction suffix for `evalCode k`: loads `2 ^ M - 1` from `base + 4` and masks `reg 2`. -/
@[expose] def evalMaskCode : Code .exact 18 :=
  .seq (.op (.const 15 4))
  (.seq (.op (.exactBin .add 15 0 15))
  (.seq (.op (.load 15 15))
        (.op (.exactBin .and 2 2 15))))

/-- Deterministic evaluation program `evalCode k`: given `reg 0 = base` and `reg 1 = u.val`,
evaluates `trinomialPolyHash (trinomialStep U M) k U M c u` into `reg 2` (`regOut`) in
`evalStepsFromB b U M k` instructions while preserving `reg 0 = base`, `reg 1 = u.val`, and
all memory. -/
@[expose] def evalCode (k : ℕ) : Code .exact 18 :=
  .seq (evalSetupCode k) (.seq hornerLoop evalMaskCode)

/-- Exact instruction count of `evalCode k` for chunk width `b`, universe `U`, output bits `M`,
and independence parameter `k`. -/
@[expose] def evalStepsFromB (b U M k : ℕ) : ℕ :=
  let L := limbCountFromB b (trinomialDeg U M)
  ((11 * L + 12) * L + 30) * k + 19

/-- Exact instruction count of `evalCode k` for capacity `n_max`, universe `U`, output bits `M`,
and independence parameter `k`. -/
@[expose] def evalSteps (n_max U M k : ℕ) : ℕ :=
  evalStepsFromB (chunkBits n_max) U M k

/-- `evalSetupCode k` executes deterministically in `13` steps. -/
theorem evalSetupCode_exec {w base b U M k : ℕ} {x : Data 18}
    (htab : TableRep base b U M k x.mem) (h0 : x.regs 0 = base)
    (hfit_end : Fits w (base + 8 + k)) :
    ∃ y : Data 18,
      Exec w (evalSetupCode k) x y 13 ∧
      y.regs 0 = base ∧
      y.regs 1 = x.regs 1 ∧
      y.regs 2 = 0 ∧
      y.regs 3 = k ∧
      y.regs 4 = b ∧
      y.regs 5 = 2 ^ b - 1 ∧
      y.regs 6 = limbCountFromB b (trinomialDeg U M) ∧
      y.regs 7 = base + 8 + k ∧
      y.regs 8 = 1 ∧
      y.regs 9 = 0 ∧
      y.mem = x.mem := by
  have hfit_1 : Fits w 1 := hfit_end.of_le (by omega)
  have hfit_0 : Fits w 0 := hfit_end.of_le (by omega)
  have hfit_k : Fits w k := hfit_end.of_le (by omega)
  have hfit_5 : Fits w 5 := hfit_end.of_le (by omega)
  have hfit_b5 : Fits w (base + 5) := hfit_end.of_le (by omega)
  have hfit_b6 : Fits w (base + 6) := hfit_end.of_le (by omega)
  have hfit_b7 : Fits w (base + 7) := hfit_end.of_le (by omega)
  have hfit_8k : Fits w (8 + k) := hfit_end.of_le (by omega)
  have hm5 : x.mem (base + 5) = b := htab.2.2.2.2.2.1
  have hm6 : x.mem (base + 6) = 2 ^ b - 1 := htab.2.2.2.2.2.2.1
  have hm7 : x.mem (base + 7) = limbCountFromB b (trinomialDeg U M) := htab.2.2.2.2.2.2.2.1
  set s1 := x.set 8 1
  have e1 : Exec w (.op (.const 8 1) : Code .exact 18) x s1 1 := Exec.const hfit_1
  set s2 := s1.set 9 0
  have e2 : Exec w (.op (.const 9 0) : Code .exact 18) s1 s2 1 := Exec.const hfit_0
  set s3 := s2.set 2 0
  have e3 : Exec w (.op (.copy 2 9) : Code .exact 18) s2 s3 1 := by
    simpa +decide [s3, s2] using (Exec.copy (B := .exact) (w := w) (d := 2) (s := 9) (x := s2))
  set s4 := s3.set 3 k
  have e4 : Exec w (.op (.const 3 k) : Code .exact 18) s3 s4 1 := Exec.const hfit_k
  set s5 := s4.set 15 5
  have e5 : Exec w (.op (.const 15 5) : Code .exact 18) s4 s5 1 := Exec.const hfit_5
  set s6 := s5.set 15 (base + 5)
  have e6 : Exec w (.op (.exactBin .add 15 0 15) : Code .exact 18) s5 s6 1 :=
    exec_exactBin (by simp +decide [s5, s4, s3, s2, s1, h0]) hfit_b5
  set s7 := s6.set 4 b
  have e7 : Exec w (.op (.load 4 15) : Code .exact 18) s6 s7 1 := by
    simpa +decide [s7, s6, s5, s4, s3, s2, s1, hm5] using
      (Exec.load (B := .exact) (w := w) (d := 4) (a := 15) (x := s6))
  set s8 := s7.set 15 (base + 6)
  have e8 : Exec w (.op (.exactBin .add 15 15 8) : Code .exact 18) s7 s8 1 :=
    exec_exactBin (by simp +decide [s7, s6, s5, s4, s3, s2, s1, Nat.add_assoc]) hfit_b6
  set s9 := s8.set 5 (2 ^ b - 1)
  have e9 : Exec w (.op (.load 5 15) : Code .exact 18) s8 s9 1 := by
    simpa +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, hm6] using
      (Exec.load (B := .exact) (w := w) (d := 5) (a := 15) (x := s8))
  set s10 := s9.set 15 (base + 7)
  have e10 : Exec w (.op (.exactBin .add 15 15 8) : Code .exact 18) s9 s10 1 :=
    exec_exactBin (by simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, Nat.add_assoc]) hfit_b7
  set s11 := s10.set 6 (limbCountFromB b (trinomialDeg U M))
  have e11 : Exec w (.op (.load 6 15) : Code .exact 18) s10 s11 1 := by
    simpa +decide [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hm7] using
      (Exec.load (B := .exact) (w := w) (d := 6) (a := 15) (x := s10))
  set s12 := s11.set 7 (8 + k)
  have e12 : Exec w (.op (.const 7 (8 + k)) : Code .exact 18) s11 s12 1 := Exec.const hfit_8k
  set s13 := s12.set 7 (base + 8 + k)
  have e13 : Exec w (.op (.exactBin .add 7 0 7) : Code .exact 18) s12 s13 1 :=
    exec_exactBin
      (by simp +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0, Nat.add_assoc])
      hfit_end
  have hall :=
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq (e10.seq
      (e11.seq (e12.seq e13)))))))))))
  refine ⟨s13, hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp +decide [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0]
  · simp +decide [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
  · simp +decide [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3]
  · simp +decide [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4]
  · simp +decide [s13, s12, s11, s10, s9, s8, s7]
  · simp +decide [s13, s12, s11, s10, s9]
  · simp +decide [s13, s12, s11]
  · simp +decide [s13]
  · simp +decide [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
  · simp +decide [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2]

/-- **`KWise.evalCode k` correctness and complexity (general `b`)**: from
`Rep base b U M k c x.mem`, `x.regs 0 = base`, and `x.regs 1 = u.val` (`u : Fin U`), `evalCode k`
halts deterministically in `evalStepsFromB b U M k = O(k * L ^ 2 + 1)` instructions, writing
`(trinomialPolyHash (trinomialStep U M) k U M c u).val` into `reg 2` (`regOut`) and preserving
`reg 0 = base`, `reg 1 = u.val`, and all memory (`y.mem = x.mem`). -/
theorem evalCode_execWithin_fromB {w base b U M k : ℕ}
    {c : Fin k → Fin (2 ^ trinomialDeg U M)} (u : Fin U) {x : Data 18}
    (hb : 0 < b) (hrep : Rep base b U M k c x.mem)
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = u.val)
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + spaceFromB b k)) :
    ∃ y : Data 18,
      ExecWithin w (evalCode k) x y (evalStepsFromB b U M k) ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = (trinomialPolyHash (trinomialStep U M) k U M c u).val ∧
      y.mem = x.mem := by
  have hpow_pos : 0 < 2 ^ (2 * b) := by positivity
  have hfit_end : Fits w (base + 8 + k) :=
    hfit_space.of_le (by dsimp only [spaceFromB]; omega)
  obtain ⟨d1, e1, hd1_0, hd1_1, hd1_2, hd1_3, hd1_4, hd1_5, hd1_6, hd1_7,
      hd1_8, hd1_9, hd1_mem⟩ :=
    evalSetupCode_exec hrep.1 h0 hfit_end
  rw [h1] at hd1_1
  set t := trinomialStep U M
  have hzero_val : (TrinomialField.equivFin t 0).val = 0 := by
    have h0_eq : (0 : TrinomialField t) = AdjoinRoot.mk (trinomial t) (polyOfCode 0) := by
      simp
    rw [h0_eq]
    exact TrinomialField.val_equivFin_mk_polyOfCode t (by positivity)
  have hd1_2' : d1.regs 2 = (TrinomialField.equivFin t 0).val := by
    rw [hd1_2, hzero_val]
  obtain ⟨d2, e2, hd2_0, hd2_1, hd2_2, hd2_mem⟩ :=
    hornerLoop_exec u hb hw hfit_space k le_rfl 0 d1
      (by rw [hd1_mem]; exact hrep)
      hd1_0 hd1_1 hd1_2' hd1_3 hd1_4 hd1_5 hd1_6 hd1_7 hd1_8 hd1_9
  have hpoly_eq : (0 : TrinomialField t) *
      (AdjoinRoot.mk (trinomial t) (polyOfCode u.val)) ^ k +
      ∑ i : Fin k, (TrinomialField.equivFin t).symm (c (Fin.castLE le_rfl i)) *
        (AdjoinRoot.mk (trinomial t) (polyOfCode u.val)) ^ (i : ℕ) =
      polynomialHash (fun j => (TrinomialField.equivFin t).symm (c j))
        (AdjoinRoot.mk (trinomial t) (polyOfCode u.val)) := by
    rw [zero_mul, zero_add]
    rfl
  have hd2_eval : d2.regs 2 = (trinomialPolyEval t k U c u).val := by
    rw [hd2_2, hpoly_eq]
    rfl
  have hfit_4 : Fits w 4 := hfit_end.of_le (by omega)
  have hfit_b4 : Fits w (base + 4) := hfit_end.of_le (by omega)
  have hm4 : d2.mem (base + 4) = 2 ^ M - 1 := by
    rw [hd2_mem, hd1_mem]
    exact hrep.1.2.2.2.2.1
  have heval_lt :
      (trinomialPolyEval t k U c u).val &&& (2 ^ M - 1) < 2 ^ (2 * trinomialDeg U M) :=
    lt_of_le_of_lt Nat.and_le_left
      (lt_of_lt_of_le (trinomialPolyEval t k U c u).isLt
        (Nat.pow_le_pow_right (by decide) (by dsimp only [trinomialDeg, t]; omega)))
  have hfit_out : Fits w ((trinomialPolyEval t k U c u).val &&& (2 ^ M - 1)) :=
    fits_of_lt_two_pow_two_mul hw heval_lt
  set s1 := d2.set 15 4
  have em1 : Exec w (.op (.const 15 4) : Code .exact 18) d2 s1 1 := Exec.const hfit_4
  set s2 := s1.set 15 (base + 4)
  have em2 : Exec w (.op (.exactBin .add 15 0 15) : Code .exact 18) s1 s2 1 :=
    exec_exactBin (by simp +decide [s1, hd2_0]) hfit_b4
  set s3 := s2.set 15 (2 ^ M - 1)
  have em3 : Exec w (.op (.load 15 15) : Code .exact 18) s2 s3 1 := by
    simpa +decide [s3, s2, s1, hm4] using
      (Exec.load (B := .exact) (w := w) (d := 15) (a := 15) (x := s2))
  set s4 := s3.set 2 ((trinomialPolyEval t k U c u).val &&& (2 ^ M - 1))
  have em4 : Exec w (.op (.exactBin .and 2 2 15) : Code .exact 18) s3 s4 1 :=
    exec_exactBin (by simp +decide [s3, s2, s1, hd2_eval]) hfit_out
  have e3 := em1.seq (em2.seq (em3.seq em4))
  have hall := e1.seq (e2.seq e3)
  refine ⟨s4, ⟨_, ?_, hall⟩, ?_, ?_, ?_, ?_⟩
  · dsimp only [evalStepsFromB]
    omega
  · simp +decide [s4, s3, s2, s1, hd2_0]
  · simp +decide [s4, s3, s2, s1, hd2_1]
  · simp only [s4, Data.set, Function.update_self, t]
    exact (val_trinomialPolyHash (trinomialStep U M) k U M c u).symm
  · change d2.mem = x.mem
    rw [hd2_mem, hd1_mem]

/-- **`KWise.evalCode k` correctness and complexity**: from
`Rep base (chunkBits n_max) U M k c x.mem`, `x.regs 0 = base`, and `x.regs 1 = u.val`
(`u : Fin U`), `evalCode k` halts deterministically in `evalSteps n_max U M k = O(k * L ^ 2 + 1)`
instructions, writing `(trinomialPolyHash (trinomialStep U M) k U M c u).val` into `reg 2`
(`regOut`) and preserving `reg 0 = base`, `reg 1 = u.val`, and all memory (`y.mem = x.mem`). -/
theorem evalCode_execWithin {w base n_max U M k : ℕ}
    {c : Fin k → Fin (2 ^ trinomialDeg U M)} (u : Fin U) {x : Data 18}
    (hrep : Rep base (chunkBits n_max) U M k c x.mem)
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = u.val)
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + space n_max k)) :
    ∃ y : Data 18,
      ExecWithin w (evalCode k) x y (evalSteps n_max U M k) ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = (trinomialPolyHash (trinomialStep U M) k U M c u).val ∧
      y.mem = x.mem :=
  evalCode_execWithin_fromB u (chunkBits_pos n_max) hrep h0 h1 hw hfit_space

/-- Output of deterministic `evalCode k` execution at word size `w` from state `y` with
`reg 0 ← base` and `reg 1 ← u.val`, reduced modulo `2 ^ M` into `Fin (2 ^ M)`. -/
noncomputable def evalHashOut (w base k U M : ℕ) (y : Data 18) (u : Fin U) : Fin (2 ^ M) :=
  open Classical in
  let x_u := (y.set 0 base).set 1 u.val
  if h : ∃ z n, Exec w (evalCode k) x_u z n then
    ⟨(Classical.choose h).regs 2 % 2 ^ M, Nat.mod_lt _ (Nat.two_pow_pos M)⟩
  else
    ⟨0, Nat.two_pow_pos M⟩

/-- On any machine state `y` satisfying `Rep base (chunkBits n_max) U M k c y.mem`, the
deterministic `evalCode k` output `evalHashOut w base k U M y u` equals
`trinomialPolyHash (trinomialStep U M) k U M c u`. -/
theorem evalHashOut_eq_trinomialPolyHash {w base n_max U M k : ℕ}
    {c : Fin k → Fin (2 ^ trinomialDeg U M)} {y : Data 18}
    (hrep : Rep base (chunkBits n_max) U M k c y.mem)
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + space n_max k))
    (u : Fin U) :
    evalHashOut w base k U M y u = trinomialPolyHash (trinomialStep U M) k U M c u := by
  let x_u := (y.set 0 base).set 1 u.val
  have hrep_u : Rep base (chunkBits n_max) U M k c x_u.mem := hrep
  have h0_u : x_u.regs 0 = base := by simp +decide [x_u]
  have h1_u : x_u.regs 1 = u.val := by simp +decide [x_u]
  obtain ⟨z, ⟨n, _, hexec⟩, -, -, hz2, -⟩ :=
    evalCode_execWithin u hrep_u h0_u h1_u hw hfit_space
  have hex : ∃ z n, Exec w (evalCode k) x_u z n := ⟨z, n, hexec⟩
  obtain ⟨n', hexec'⟩ := Classical.choose_spec hex
  have huniq : Classical.choose hex = z := (hexec'.unique hexec).1
  ext
  simp only [evalHashOut, x_u, hex, ↓reduceDIte, huniq, hz2,
    Nat.mod_eq_of_lt (trinomialPolyHash _ k U M c u).isLt]

/-- Under `resampleComp base U M k x`, the Word-RAM hash function `evalHashOut w base k U M z.1`
has the exact distribution of `trinomialPolyHash (trinomialStep U M) k U M c` for a uniform seed
`c : Fin k → Fin (2 ^ trinomialDeg U M)`. -/
theorem map_evalHashOut_eval_resampleComp {w base n_max U M k : ℕ} {x : Data 18}
    (htab : TableRep base (chunkBits n_max) U M k x.mem)
    (h0 : x.regs 0 = base)
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + space n_max k)) :
    ((resampleComp base U M k x).eval).map (fun z => evalHashOut w base k U M z.1) =
      (PMF.uniformOfFintype (Fin k → Fin (2 ^ trinomialDeg U M))).map
        (trinomialPolyHash (trinomialStep U M) k U M) := by
  rw [← map_extractSeeds_eval_resampleComp base U M k x]
  dsimp only [trinomialDeg, extractSeeds, extractSlice]
  rw [PMF.map_comp]
  refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun z hz => ?_
  rw [ProbComp.support_eval] at hz
  have hrep := (mem_support_resampleComp htab h0 hz).1.1
  funext u
  exact evalHashOut_eq_trinomialPolyHash hrep hw hfit_space u

/-- For any `k`-wise independent hash family `h : ι → X → Y` and any set `T : Finset X` of at most
`k` points, restricting `h i` to `T` under a uniform seed `i ← PMF.uniformOfFintype ι` yields the
uniform distribution `PMF.uniformOfFintype (T → Y)`. -/
theorem uniformOfFintype_map_restrict_of_isKWiseIndependentHash
    {ι X Y : Type*} [Fintype ι] [Nonempty ι] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {k : ℕ} {h : ι → X → Y} (hh : IsKWiseIndependentHash k h)
    {T : Finset X} (hT : Finset.card T ≤ k) :
    (PMF.uniformOfFintype ι).map (fun i => T.restrict (h i)) =
      PMF.uniformOfFintype (T → Y) := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [Cslib.Probability.PMF.toReal_uniformOfFintype_map_apply, hh.dens_filter_restrict_eq hT y]
  simp

/-- **Composed Word-RAM `k`-wise independence of `resampleCode` and `evalCode`
(`isKWiseIndependentHash_eval`)**:
from any machine state `x` satisfying `TableRep base (chunkBits n_max) U M k x.mem` and
`x.regs 0 = base`, under the resampling distribution `(resampleComp base U M k x).eval` of
`resampleCode k`, for every set `T : Finset (Fin U)` of at most `k` keys (`T.card ≤ k`), the
restricted tuple of deterministic `evalCode k` outputs `T.restrict (evalHashOut w base k U M z.1)`
is uniformly distributed on `T → Fin (2 ^ M)` (`PMF.uniformOfFintype (T → Fin (2 ^ M))`). -/
theorem isKWiseIndependentHash_eval {w base n_max U M k : ℕ} {x : Data 18}
    (htab : TableRep base (chunkBits n_max) U M k x.mem)
    (h0 : x.regs 0 = base)
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + space n_max k))
    {T : Finset (Fin U)} (hT : Finset.card T ≤ k) :
    ((resampleComp base U M k x).eval).map (fun z => T.restrict (evalHashOut w base k U M z.1)) =
      PMF.uniformOfFintype (T → Fin (2 ^ M)) := by
  have hmap := congrArg (PMF.map T.restrict)
    (map_evalHashOut_eval_resampleComp htab h0 hw hfit_space)
  dsimp only [trinomialDeg] at hmap
  rw [PMF.map_comp, PMF.map_comp] at hmap
  exact hmap.trans (uniformOfFintype_map_restrict_of_isKWiseIndependentHash
    (isKWiseIndependentHash_trinomialPolyHash (le_two_pow_trinomialDeg U M) (le_trinomialDeg U M))
    hT)

end Cslib.Algorithms.WordRAM.Hashing.KWise
