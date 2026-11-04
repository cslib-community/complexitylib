/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.InaccessibleEntropy.EntropyReduction
public import Complexity.Crypto.Computational.InaccessibleEntropy.OneWay
public import Complexity.Crypto.Computational.InaccessibleEntropy.Repetition
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Complexity.Crypto.Negligible.Basic
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Probability.PMF.Uniform

/-!
# Gap amplification and candidate grid for 1-bit shrinking collision resistance

Combining parallel repetition (`Repetition.lean`, Lemma 5.3), two-universal input hashing, and
1-bit shrinking output hashing (`EntropyReduction.lean`, Lemmas 5.4 and 5.5), this module
formalizes STEPS 1–3 of `[HHRVW2020]`, Section 5.1.5, Proof of Theorem 5.1 (pp. 30–31):

1. **Concrete parameter schedule** (`ampSlack`, `ampReps`, `ampGridCount`): from any
   `InaccessibleEntropyFamily` $F$ with input width $n_0(n)$ and gap denominator $D(n) \ge 1$, set
   $$\Delta(n) = 3 (n + 2) D(n) (n_0(n) + 1)^2, \qquad
     t(n) = 6 D(n) \Delta(n), \qquad
     \kappa(n) = 6 D(n) (n_0(n) + 1) + 3.$$
   At security parameters $n \ge N_0$ where $H(Z \mid F_0(Z)) - \mathbb{E}[\log_2 |L_0(Z)|] \ge
   1 / D(n)$, repeating $t(n)$ times amplifies the expected entropy gap to at least $6 \Delta(n)$,
   while the Hoeffding exponent $2 \Delta(n)^2 / (t(n) \cdot n_0(n)^2)$ exceeds $n + 2$.
2. **Uniform polynomial-time candidate grid** (`ShrinkingCollisionGrid`): because the real entropy
   $k_0(n) = H(Z \mid F_0(Z))$ need not be efficiently computable, the grid exposes $\kappa(n)$
   uniformly polynomial-time candidates $F_3^{(q \cdot \Delta(n))}$ ($0 \le q < \kappa(n)$), all
   sharing the same input width `inLen n` and output width `outLen n` with `outLen n + 1 = inLen n`
   and `n + 1 ≤ outLen n`.
3. **Existence of a collision-resistant candidate on random inputs**
   (`InaccessibleEntropyFamily.exists_shrinkingCollisionGrid`,
   `OneWay.exists_shrinkingCollisionGrid`): the grid index
   $q^*(n) = \lfloor t(n) a_0(n) / \Delta(n) \rfloor_+ + 3 < \kappa(n)$ places
   $j^*(n) = q^*(n) \Delta(n)$ strictly inside $[t a_0 + 2 \Delta, t k_0 - 3 \Delta]$, making
   candidate $q^*(n)$ collision-resistant on random inputs against all uniform strict-PPT
   adversaries (note that neither `shrunkHashEscapeInverter` nor `repEscapeInverter` reads $q^*$).
   Target shifts, length-increasing cascades, and $\kappa(n)$-way concatenation for target
   collision resistance and Rompel's signature theorem build on `ShrinkingCollisionGrid` in
   `Complexity.Crypto.Computational.InaccessibleEntropy.TargetCollision` and
   `Complexity.Crypto.Computational.Rompel`.

## Main definitions

* `Cslib.Crypto.ampSlack`, `Cslib.Crypto.ampReps`, `Cslib.Crypto.ampGridCount`: pure-`ℕ`
  amplification and grid-size schedule for an `InaccessibleEntropyFamily`.
* `Cslib.Crypto.ShrinkingCollisionGrid`: uniform polynomial-time grid of strictly `1`-bit shrinking
  candidates containing an index sequence collision-resistant on random inputs.

## Main results

* `Cslib.Crypto.InaccessibleEntropyFamily.exists_shrinkingCollisionGrid`: STEPS 1–3 of Theorem 5.1
  from any `InaccessibleEntropyFamily`.
* `Cslib.Crypto.OneWay.exists_shrinkingCollisionGrid`: STEPS 1–3 of Theorem 5.1 composed with
  the constant-threshold adaptation of Theorem 4.5 (`OneWay.exists_inaccessibleEntropyFamily`).

## References

* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Sections 5.1.1–5.1.3 and 5.1.5, Theorem 5.1 STEPS 1–3,
  pp. 26–31][HHRVW2020]
-/

public section

namespace Cslib.Crypto

open Cslib.Probability Finset Turing.MultiTapeTM
open scoped BigOperators ENNReal NNReal

/-! ### Amplification parameter schedule and candidate-grid interface -/

/-- Concentration and hash-truncation slack
$\Delta(n) = 3 (n + 2) D(n) (n_0(n) + 1)^2$ (`[HHRVW2020]`, Section 5.1.5, STEP 1, p. 30). -/
@[expose] def ampSlack (F : InaccessibleEntropyFamily) (n : ℕ) : ℕ :=
  3 * (n + 2) * F.denom n * ((F.inLen n + 1) * (F.inLen n + 1))

/-- Parallel repetition count $t(n) = 6 D(n) \Delta(n)$ (`[HHRVW2020]`, Section 5.1.5, STEP 1,
p. 30). -/
@[expose] def ampReps (F : InaccessibleEntropyFamily) (n : ℕ) : ℕ :=
  6 * F.denom n * ampSlack F n

/-- Number of candidate truncation indices $\kappa(n) = 6 D(n) (n_0(n) + 1) + 3$ (`[HHRVW2020]`,
Section 5.1.5, STEP 5, p. 31). -/
@[expose] def ampGridCount (F : InaccessibleEntropyFamily) (n : ℕ) : ℕ :=
  6 * F.denom n * (F.inLen n + 1) + 3

/-- Effective repeated input bit width: equals `ampReps F n * F.inLen n` whenever `1 ≤ F.inLen n`
(in particular for all `n ≥ N₀`), with a fallback `n + 2` when `F.inLen n = 0` so `1`-bit shrinkage
holds unconditionally at every `n : ℕ`. -/
@[expose] def ampRepInLen (F : InaccessibleEntropyFamily) (n : ℕ) : ℕ :=
  if F.inLen n = 0 then n + 2 else ampReps F n * F.inLen n

/-- Effective repeated output bit width matching `ampRepInLen`. -/
@[expose] def ampRepOutLen (F : InaccessibleEntropyFamily) (n : ℕ) : ℕ :=
  if F.inLen n = 0 then n + 2 else ampReps F n * F.outLen n

/-- Effective repeated word evaluator matching `ampRepInLen` and `ampRepOutLen`. -/
@[expose] def ampRepEvalWord (F : InaccessibleEntropyFamily) (n : ℕ) (u : List Bool) : List Bool :=
  if F.inLen n = 0 then List.replicate (n + 2) false
  else repEvalWord (ampReps F n) (F.inLen n) (F.evalWord n) u

/-- A uniform polynomial-time candidate grid of strictly `1`-bit shrinking hash functions
$F_3^{(n, q)} : \{0, 1\}^{\mathrm{inLen}(n)} \to \{0, 1\}^{\mathrm{outLen}(n)}$ ($0 \le q <
\mathrm{gridCount}(n)$) containing a sequence `goodIdx` of candidate indices that is
collision-resistant on random inputs against all uniform strict-PPT adversaries (`[HHRVW2020]`,
Section 5.1.5, STEPS 1–3 and STEP 5, pp. 30–31). -/
structure ShrinkingCollisionGrid where
  /-- Input bit width $N_3(n)$ shared by all candidates at security parameter $n$. -/
  inLen : ℕ → ℕ
  /-- Output bit width $M_3(n) = N_3(n) - 1$ shared by all candidates at security parameter $n$. -/
  outLen : ℕ → ℕ
  /-- Polynomially bounded number of candidate indices $\kappa(n) \ge 1$. -/
  gridCount : ℕ → ℕ
  /-- Uniform word-level evaluator `(n, q, raw) ↦ evalGrid n q raw`. -/
  evalGrid : ℕ → ℕ → List Bool → List Bool
  /-- Plain polynomial-time unary input-length certificate. -/
  polyTime_inLen : ComputableInPolyTime inLen encUnary encUnary
  /-- Plain polynomial-time unary output-length certificate. -/
  polyTime_outLen : ComputableInPolyTime outLen encUnary encUnary
  /-- Plain polynomial-time unary grid-count certificate. -/
  polyTime_gridCount : ComputableInPolyTime gridCount encUnary encUnary
  /-- Plain polynomial-time uniform grid-evaluation certificate. -/
  polyTime_evalGrid : ComputableInPolyTime
    (fun ⟨n, q, raw⟩ => evalGrid n q raw)
    (encPair encUnary (encPair encUnary encBits)) encBits
  /-- Nonempty candidate range at every security parameter. -/
  gridCount_pos : ∀ n, 1 ≤ gridCount n
  /-- Nontrivial output length growing with the security parameter. -/
  le_outLen : ∀ n, n + 1 ≤ outLen n
  /-- Strict `1`-bit shrinkage at every security parameter. -/
  outLen_add_one : ∀ n, outLen n + 1 = inLen n
  /-- Exact output length `outLen n` for every candidate and raw word. -/
  length_evalGrid : ∀ n q raw, (evalGrid n q raw).length = outLen n
  /-- Existence of an in-range candidate sequence `goodIdx` that is collision-resistant on random
  inputs against every uniform strict-PPT adversary. -/
  exists_good_candidate : ∃ goodIdx : ℕ → ℕ, (∀ n, goodIdx n < gridCount n) ∧
    ∀ B : ℕ → List Bool → ProbComp (List Bool), IsPPT encBits B →
      Negligible (fun n =>
        Game.succProbability (ProbComp.eval
          (randomCollisionGame (fun k => evalGrid k (goodIdx k)) inLen B n)))

/-! ### Polynomial-time certificates and dimension bounds -/

@[fun_prop]
theorem computableInPolyTime_ampSlack (F : InaccessibleEntropyFamily) :
    ComputableInPolyTime (ampSlack F) encUnary encUnary := by
  unfold ampSlack
  have hid := ComputableInPolyTime.id' (encIn := encUnary)
  have hn2 := ComputableInPolyTime.unary_add' hid (ComputableInPolyTime.const 2)
  have hw1 := ComputableInPolyTime.unary_add' F.polyTime_inLen (ComputableInPolyTime.const 1)
  have hsq := ComputableInPolyTime.unary_mul' hw1 hw1
  exact ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 3) hn2)
      F.polyTime_denom)
    hsq

@[fun_prop]
theorem computableInPolyTime_ampReps (F : InaccessibleEntropyFamily) :
    ComputableInPolyTime (ampReps F) encUnary encUnary := by
  unfold ampReps
  exact ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 6) F.polyTime_denom)
    (computableInPolyTime_ampSlack F)

@[fun_prop]
theorem computableInPolyTime_ampGridCount (F : InaccessibleEntropyFamily) :
    ComputableInPolyTime (ampGridCount F) encUnary encUnary := by
  unfold ampGridCount
  have hw1 := ComputableInPolyTime.unary_add' F.polyTime_inLen (ComputableInPolyTime.const 1)
  exact ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 6) F.polyTime_denom)
      hw1)
    (ComputableInPolyTime.const 3)

@[fun_prop]
theorem computableInPolyTime_ampRepInLen (F : InaccessibleEntropyFamily) :
    ComputableInPolyTime (ampRepInLen F) encUnary encUnary := by
  unfold ampRepInLen
  exact ComputableInPolyTime.ite_decide
    (ComputableInPolyTime.unary_eq' F.polyTime_inLen (ComputableInPolyTime.const 0))
    (ComputableInPolyTime.unary_add' .id' (ComputableInPolyTime.const 2))
    (ComputableInPolyTime.unary_mul' (computableInPolyTime_ampReps F) F.polyTime_inLen)

@[fun_prop]
theorem computableInPolyTime_ampRepOutLen (F : InaccessibleEntropyFamily) :
    ComputableInPolyTime (ampRepOutLen F) encUnary encUnary := by
  unfold ampRepOutLen
  exact ComputableInPolyTime.ite_decide
    (ComputableInPolyTime.unary_eq' F.polyTime_inLen (ComputableInPolyTime.const 0))
    (ComputableInPolyTime.unary_add' .id' (ComputableInPolyTime.const 2))
    (ComputableInPolyTime.unary_mul' (computableInPolyTime_ampReps F) F.polyTime_outLen)

@[fun_prop]
theorem computableInPolyTime_ampRepEvalWord (F : InaccessibleEntropyFamily) :
    ComputableInPolyTime (fun p : ℕ × List Bool => ampRepEvalWord F p.1 p.2)
      (encPair encUnary encBits) encBits := by
  unfold ampRepEvalWord
  have hfst := ComputableInPolyTime.fst encUnary encBits
  have hsnd := ComputableInPolyTime.snd encUnary encBits
  exact ComputableInPolyTime.ite_decide
    (ComputableInPolyTime.unary_eq' (F.polyTime_inLen.comp hfst) (ComputableInPolyTime.const 0))
    ((ComputableInPolyTime.bitsReplicate false).comp
      (ComputableInPolyTime.unary_add' hfst (ComputableInPolyTime.const 2)))
    (computableInPolyTime_repEvalWord
      ((computableInPolyTime_ampReps F).comp hfst)
      (F.polyTime_inLen.comp hfst)
      hfst F.polyTime_evalWord hsnd)

private theorem le_ampSlack (F : InaccessibleEntropyFamily) (n : ℕ) :
    3 * (n + 2) ≤ ampSlack F n := by
  have hd : 1 ≤ F.denom n := F.denom_pos n
  have hsq : 1 ≤ (F.inLen n + 1) * (F.inLen n + 1) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  calc
    3 * (n + 2) = 3 * (n + 2) * 1 * 1 := by ring
    _ ≤ 3 * (n + 2) * F.denom n * ((F.inLen n + 1) * (F.inLen n + 1)) := by gcongr

private theorem le_ampRepInLen (F : InaccessibleEntropyFamily) (n : ℕ) :
    n + 2 ≤ ampRepInLen F n := by
  unfold ampRepInLen
  split_ifs with h0
  · exact le_rfl
  · have hw : 1 ≤ F.inLen n := Nat.pos_of_ne_zero h0
    have hd : 1 ≤ F.denom n := F.denom_pos n
    have hslack : 3 * (n + 2) ≤ ampSlack F n := le_ampSlack F n
    have hreps : n + 2 ≤ ampReps F n := by
      unfold ampReps
      calc
        n + 2 ≤ 6 * 1 * (3 * (n + 2)) := by omega
        _ ≤ 6 * F.denom n * ampSlack F n := by gcongr
    calc
      n + 2 = (n + 2) * 1 := (Nat.mul_one _).symm
      _ ≤ ampReps F n * F.inLen n := by gcongr

/-! ### Entropy and exponential helper bounds -/

private theorem conditionalEntropy_le_inLen {w m : ℕ} (f : BitString w → BitString m) :
    PMF.conditionalEntropy ((PMF.uniformOfFintype (BitString w)).map fun z => (f z, z)) ≤
      (w : ℝ) := by
  rw [← expected_realSampleEntropy_eq_conditionalEntropy f]
  have hpoint (z : BitString w) : realSampleEntropy f z ≤ (w : ℝ) := by
    have hpos : (0 : ℝ) < #(fiberSet f (f z)) := by exact_mod_cast card_fiberSet_pos f z
    have hle : (#(fiberSet f (f z)) : ℝ) ≤ (2 : ℝ) ^ w := by
      have hc : #(fiberSet f (f z)) ≤ Fintype.card (BitString w) := card_le_univ _
      have hw : Fintype.card (BitString w) = 2 ^ w := by simp [BitString]
      exact_mod_cast hc.trans hw.le
    exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hpos).mpr
      (by simpa only [Real.rpow_natCast] using hle)
  calc
    (∑ z : BitString w, ((PMF.uniformOfFintype (BitString w)) z).toReal * realSampleEntropy f z)
      ≤ ∑ z : BitString w, ((PMF.uniformOfFintype (BitString w)) z).toReal * (w : ℝ) :=
        sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpoint z) ENNReal.toReal_nonneg
    _ = (w : ℝ) := by rw [← sum_mul, PMF.sum_toReal, one_mul]

private theorem exp_neg_le_half_pow (n : ℕ) {x : ℝ} (hx : x ≤ -(n : ℝ)) :
    Real.exp x ≤ (1 / 2 : ℝ) ^ n := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
    calc
      (2 : ℝ) ^ n ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) h2 n
      _ = Real.exp (n : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
  calc
    Real.exp x ≤ Real.exp (-(n : ℝ)) := Real.exp_le_exp.mpr hx
    _ = (Real.exp (n : ℝ))⁻¹ := Real.exp_neg (n : ℝ)
    _ ≤ ((2 : ℝ) ^ n)⁻¹ := inv_anti₀ (by positivity) hpow
    _ = (1 / 2 : ℝ) ^ n := by rw [one_div, inv_pow]

private theorem two_rpow_neg_le_half_pow (n : ℕ) {x : ℝ} (hx : x ≤ -(n : ℝ)) :
    (2 : ℝ) ^ x ≤ (1 / 2 : ℝ) ^ n := by
  calc
    (2 : ℝ) ^ x ≤ (2 : ℝ) ^ (-(n : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hx
    _ = ((2 : ℝ) ^ (n : ℝ))⁻¹ := Real.rpow_neg (by norm_num) (n : ℝ)
    _ = (1 / 2 : ℝ) ^ n := by rw [Real.rpow_natCast, one_div, inv_pow]

/-! ### Main grid theorem: STEPS 1–3 of Theorem 5.1 -/

private theorem computableInPolyTime_shrunkHashInLen_amp (F : InaccessibleEntropyFamily) :
    ComputableInPolyTime
      (fun n => shrunkHashInLen (ampRepInLen F n) (ampRepOutLen F n)) encUnary encUnary := by
  unfold shrunkHashInLen inputHashInLen inputHashOutLen outHashLen
  have hn₁ := computableInPolyTime_ampRepInLen F
  have hm₁ := computableInPolyTime_ampRepOutLen F
  have hsq := ComputableInPolyTime.unary_mul' hn₁ hn₁
  have hin₂ := ComputableInPolyTime.unary_add' hn₁ hsq
  have hout₂ := ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add' hm₁ hsq) hn₁
  have houtH := ComputableInPolyTime.unary_sub' hin₂ (ComputableInPolyTime.const 1)
  exact ComputableInPolyTime.unary_add' hin₂ (ComputableInPolyTime.unary_mul' houtH hout₂)

private theorem computableInPolyTime_shrunkHashOutLen_amp (F : InaccessibleEntropyFamily) :
    ComputableInPolyTime
      (fun n => shrunkHashOutLen (ampRepInLen F n) (ampRepOutLen F n)) encUnary encUnary := by
  unfold shrunkHashOutLen outHashLen inputHashInLen inputHashOutLen
  have hn₁ := computableInPolyTime_ampRepInLen F
  have hm₁ := computableInPolyTime_ampRepOutLen F
  have hsq := ComputableInPolyTime.unary_mul' hn₁ hn₁
  have hin₂ := ComputableInPolyTime.unary_add' hn₁ hsq
  have hout₂ := ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add' hm₁ hsq) hn₁
  have houtH := ComputableInPolyTime.unary_sub' hin₂ (ComputableInPolyTime.const 1)
  exact ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' houtH hout₂) houtH

private theorem computableInPolyTime_shrunkHashEvalWord_amp (F : InaccessibleEntropyFamily) :
    ComputableInPolyTime
      (fun ⟨n, q, raw⟩ => shrunkHashEvalWord (ampRepInLen F n) (ampRepOutLen F n)
        (ampRepEvalWord F n) (q * ampSlack F n) raw)
      (encPair encUnary (encPair encUnary encBits)) encBits := by
  have hn := ComputableInPolyTime.fst encUnary (encPair encUnary encBits)
  have hrest := ComputableInPolyTime.snd encUnary (encPair encUnary encBits)
  have hq := (ComputableInPolyTime.fst encUnary encBits).comp hrest
  have hraw := (ComputableInPolyTime.snd encUnary encBits).comp hrest
  exact computableInPolyTime_shrunkHashEvalWord
    ((computableInPolyTime_ampRepInLen F).comp hn)
    ((computableInPolyTime_ampRepOutLen F).comp hn)
    hn
    (ComputableInPolyTime.unary_mul' hq ((computableInPolyTime_ampSlack F).comp hn))
    (computableInPolyTime_ampRepEvalWord F)
    hraw

private noncomputable def ampGoodIdx (F : InaccessibleEntropyFamily) (N₀ n : ℕ) : ℕ :=
  if n < N₀ then 0
  else Nat.floor
    (((ampReps F n : ℝ) * accessibleSetExpectation (F.accSet n)) / (ampSlack F n : ℝ)) + 3

private theorem ampGoodIdx_lt_ampGridCount (F : InaccessibleEntropyFamily) {N₀ : ℕ}
    (hN₀ : ∀ n ≥ N₀, accessibleSetExpectation (F.accSet n) ≤
      PMF.conditionalEntropy ((PMF.uniformOfFintype (BitString (F.inLen n))).map fun z =>
        (wordToFinMap (F.inLen n) (F.outLen n) (F.evalWord n) z, z)) - 1 / (F.denom n : ℝ))
    (n : ℕ) : ampGoodIdx F N₀ n < ampGridCount F n := by
  dsimp only [ampGoodIdx]
  split_ifs with hlt
  · unfold ampGridCount; omega
  · have ha_le : accessibleSetExpectation (F.accSet n) ≤ (F.inLen n : ℝ) := by
      have hgap := hN₀ n (not_lt.mp hlt)
      have hk_le := conditionalEntropy_le_inLen
        (wordToFinMap (F.inLen n) (F.outLen n) (F.evalWord n))
      have hd_pos : (0 : ℝ) ≤ 1 / (F.denom n : ℝ) := by positivity
      linarith
    have hΔ_pos : (0 : ℝ) < ampSlack F n := by
      have h := le_ampSlack F n
      exact_mod_cast (show 0 < ampSlack F n by omega)
    have hdiv_le : ((ampReps F n : ℝ) * accessibleSetExpectation (F.accSet n)) /
        (ampSlack F n : ℝ) ≤ ((6 * F.denom n * F.inLen n : ℕ) : ℝ) := by
      have ht_eq : (ampReps F n : ℝ) = 6 * (F.denom n : ℝ) * (ampSlack F n : ℝ) := by
        simp only [ampReps, Nat.cast_mul, Nat.cast_ofNat]
      rw [ht_eq, mul_assoc, mul_comm ((ampSlack F n : ℝ)), ← mul_assoc,
        mul_div_cancel_right₀ _ hΔ_pos.ne', Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
      gcongr
    have hfl := Nat.floor_le_of_le hdiv_le
    have hd : 1 ≤ F.denom n := F.denom_pos n
    unfold ampGridCount
    nlinarith

private theorem amp_hoeffding_exponent_le (F : InaccessibleEntropyFamily) {n : ℕ}
    (hw₀_pos : 1 ≤ F.inLen n) :
    -2 * (ampSlack F n : ℝ) ^ 2 / ((ampReps F n : ℝ) * (F.inLen n : ℝ) ^ 2) ≤ -(n : ℝ) := by
  let w₀ := F.inLen n
  let D := F.denom n
  let t := ampReps F n
  let Δ := ampSlack F n
  have hD_pos : (0 : ℝ) < D := by exact_mod_cast F.denom_pos n
  have hΔ_ge : (3 * (n + 2) : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast le_ampSlack F n
  have hΔ_pos : (0 : ℝ) < Δ := by linarith
  have ht_real : (t : ℝ) = 6 * (D : ℝ) * (Δ : ℝ) := by
    dsimp only [t, ampReps]; push_cast; ring
  have hw₀_pos_r : (0 : ℝ) < w₀ := by exact_mod_cast hw₀_pos
  have ht_pos_r : (0 : ℝ) < t := by rw [ht_real]; positivity
  rw [div_le_iff₀ (mul_pos ht_pos_r (pow_pos hw₀_pos_r 2))]
  have hΔ_def : (Δ : ℝ) = 3 * ((n : ℝ) + 2) * (D : ℝ) * ((w₀ : ℝ) + 1) ^ 2 := by
    dsimp only [Δ, ampSlack]; push_cast; ring
  have hsq_le : (w₀ : ℝ) ^ 2 ≤ ((w₀ : ℝ) + 1) ^ 2 := by nlinarith
  have hkey : (n : ℝ) * ((t : ℝ) * (w₀ : ℝ) ^ 2) ≤ 2 * (Δ : ℝ) ^ 2 := by
    calc
      (n : ℝ) * ((t : ℝ) * (w₀ : ℝ) ^ 2)
        ≤ ((n : ℝ) + 2) * ((6 * (D : ℝ) * (Δ : ℝ)) * ((w₀ : ℝ) + 1) ^ 2) := by
          rw [← ht_real]; gcongr; linarith
      _ = 2 * (Δ : ℝ) * (3 * ((n : ℝ) + 2) * (D : ℝ) * ((w₀ : ℝ) + 1) ^ 2) := by ring
      _ = 2 * (Δ : ℝ) ^ 2 := by rw [← hΔ_def]; ring
  linarith

private theorem amp_randomCollisionGame_succProbability_le
    (F : InaccessibleEntropyFamily) {N₀ : ℕ}
    (hN₀ : ∀ n ≥ N₀, accessibleSetExpectation (F.accSet n) ≤
      PMF.conditionalEntropy ((PMF.uniformOfFintype (BitString (F.inLen n))).map fun z =>
        (wordToFinMap (F.inLen n) (F.outLen n) (F.evalWord n) z, z)) - 1 / (F.denom n : ℝ))
    (B : ℕ → List Bool → ProbComp (List Bool)) {n : ℕ} (hn : N₀ ≤ n) :
    Game.succProbability (ProbComp.eval
      (randomCollisionGame
        (fun k => shrunkHashEvalWord (ampRepInLen F k) (ampRepOutLen F k)
          (ampRepEvalWord F k) (ampGoodIdx F N₀ k * ampSlack F k))
        (fun k => shrunkHashInLen (ampRepInLen F k) (ampRepOutLen F k)) B n)) ≤
      (dyadicSize (ampReps F n) : ℝ≥0) *
        Game.succProbability (ProbComp.eval
          (accessibleEscapeGame F.evalWord F.inLen F.accSet
            (repEscapeInverter (ampReps F) F.inLen
              (shrunkHashEscapeInverter
                (fun k => ampReps F k * F.inLen k)
                (fun k => ampReps F k * F.outLen k) B)) n)) +
      (6 : ℝ≥0) * (1 / 2 : ℝ≥0) ^ n := by
  let n₁True (k : ℕ) : ℕ := ampReps F k * F.inLen k
  let m₁True (k : ℕ) : ℕ := ampReps F k * F.outLen k
  let B₁ := shrunkHashEscapeInverter n₁True m₁True B
  let w₀ := F.inLen n
  let m₀ := F.outLen n
  let D := F.denom n
  let t := ampReps F n
  let Δ := ampSlack F n
  let f₀ := wordToFinMap w₀ m₀ (F.evalWord n)
  let a₀ := accessibleSetExpectation (F.accSet n)
  let k₀ := PMF.conditionalEntropy ((PMF.uniformOfFintype (BitString w₀)).map fun z => (f₀ z, z))
  have ha₀_nonneg : 0 ≤ a₀ :=
    accessibleSetExpectation_nonneg fun z => ⟨z, F.self_mem_accSet n z⟩
  have hgap₀ : a₀ ≤ k₀ - 1 / (D : ℝ) := hN₀ n hn
  have hk₀_le : k₀ ≤ (w₀ : ℝ) := conditionalEntropy_le_inLen f₀
  have hD_pos : (0 : ℝ) < D := by exact_mod_cast F.denom_pos n
  have hw₀_ne_zero : w₀ ≠ 0 := by
    intro h0
    have hdiv_pos : (0 : ℝ) < 1 / (D : ℝ) := by positivity
    have hw0_real : (w₀ : ℝ) = 0 := by exact_mod_cast h0
    linarith
  have hw₀_pos : 1 ≤ w₀ := Nat.pos_of_ne_zero hw₀_ne_zero
  have hn₁_eq : ampRepInLen F n = n₁True n := by
    simp only [ampRepInLen, n₁True, hw₀_ne_zero, ↓reduceIte, w₀]
  have hm₁_eq : ampRepOutLen F n = m₁True n := by
    simp only [ampRepOutLen, m₁True, hw₀_ne_zero, ↓reduceIte, w₀]
  have heval₁_eq : ampRepEvalWord F n = repEvalWord t w₀ (F.evalWord n) := by
    funext u; simp only [ampRepEvalWord, hw₀_ne_zero, ↓reduceIte, t, w₀]
  have hgame_eq :
      randomCollisionGame
        (fun k => shrunkHashEvalWord (ampRepInLen F k) (ampRepOutLen F k)
          (ampRepEvalWord F k) (ampGoodIdx F N₀ k * ampSlack F k))
        (fun k => shrunkHashInLen (ampRepInLen F k) (ampRepOutLen F k)) B n =
      randomCollisionGame
        (fun k => shrunkHashEvalWord (n₁True k) (m₁True k)
          (repEvalWord (ampReps F k) (F.inLen k) (F.evalWord k))
          (ampGoodIdx F N₀ k * ampSlack F k))
        (fun k => shrunkHashInLen (n₁True k) (m₁True k)) B n := by
    simp only [randomCollisionGame, hn₁_eq, hm₁_eq, heval₁_eq, t, w₀]
  let A_max : ℝ := (t : ℝ) * a₀ + (Δ : ℝ)
  let K_min : ℝ := (t : ℝ) * k₀ - (Δ : ℝ)
  have hn₁True_pos : 1 ≤ n₁True n := by
    have ht_pos : 1 ≤ t := by
      have hslack := le_ampSlack F n
      have hd := F.denom_pos n
      dsimp only [t, ampReps]; nlinarith
    exact Nat.mul_le_mul ht_pos hw₀_pos
  have hlen_rep (u : List Bool) (_ : u.length = n₁True n) :
      (repEvalWord t w₀ (F.evalWord n) u).length = m₁True n :=
    length_repEvalWord (F.length_evalWord n) u
  have hcoll := shrunkHash_randomCollision_le n₁True m₁True
    (fun k => ampGoodIdx F N₀ k * ampSlack F k)
    (fun k => repEvalWord (ampReps F k) (F.inLen k) (F.evalWord k))
    (fun k => repBitAccessibleSet (ampReps F k) (F.inLen k) (F.accSet k))
    B n hn₁True_pos hlen_rep A_max K_min
  have hrep_esc := repEscape_le_dyadicSize_mul_escape (ampReps F) F.inLen F.outLen F.evalWord
    F.accSet B₁ n (F.length_evalWord n)
  have hΔ_ge : (3 * (n + 2) : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast le_ampSlack F n
  have hΔ_pos : (0 : ℝ) < Δ := by linarith
  have ht_real : (t : ℝ) = 6 * (D : ℝ) * (Δ : ℝ) := by
    dsimp only [t, ampReps]; push_cast; ring
  have hgap_scaled : 6 * (Δ : ℝ) ≤ (t : ℝ) * k₀ - (t : ℝ) * a₀ := by
    have hmul : (t : ℝ) * (1 / (D : ℝ)) ≤ (t : ℝ) * (k₀ - a₀) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hcancel : (t : ℝ) * (1 / (D : ℝ)) = 6 * (Δ : ℝ) := by
      rw [ht_real]; field_simp [hD_pos.ne']
    linarith
  have hgood_eq : ampGoodIdx F N₀ n = Nat.floor (((t : ℝ) * a₀) / (Δ : ℝ)) + 3 := by
    simp only [ampGoodIdx, not_lt.mpr hn, ↓reduceIte, t, a₀, Δ]
  let qFloor := Nat.floor (((t : ℝ) * a₀) / (Δ : ℝ))
  have hfloor_le : (qFloor : ℝ) * (Δ : ℝ) ≤ (t : ℝ) * a₀ :=
    (le_div_iff₀ hΔ_pos).mp
      (Nat.floor_le (div_nonneg (mul_nonneg (Nat.cast_nonneg t) ha₀_nonneg) hΔ_pos.le))
  have hlt_floor_succ : (t : ℝ) * a₀ < ((qFloor : ℝ) + 1) * (Δ : ℝ) :=
    (div_lt_iff₀ hΔ_pos).mp (Nat.lt_floor_add_one _)
  let j₀ : ℕ := ampGoodIdx F N₀ n * Δ
  have hj₀_real : (j₀ : ℝ) = ((qFloor : ℝ) + 3) * (Δ : ℝ) := by
    dsimp only [j₀]; rw [hgood_eq]; push_cast; ring
  have hj₀_le_n₁ : j₀ ≤ n₁True n := by
    have htw : (t : ℝ) * k₀ ≤ (n₁True n : ℝ) := by
      dsimp only [n₁True]; rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left hk₀_le (by positivity)
    exact_mod_cast (show (j₀ : ℝ) ≤ (n₁True n : ℝ) by linarith)
  have hmin_eq : (min j₀ (n₁True n) : ℝ) = (j₀ : ℝ) := by
    rw [← Nat.cast_min, Nat.min_eq_left hj₀_le_n₁]
  have hhoeff_exp := amp_hoeffding_exponent_le F hw₀_pos
  have htail_acc :=
    (repBitAccessibleSet_logb_card_ge_prob t w₀ (F.accSet n) (F.self_mem_accSet n)
      hΔ_pos.le).trans (exp_neg_le_half_pow n hhoeff_exp)
  have htail_ent :=
    (repEvalWord_realSampleEntropy_le_prob (F.length_evalWord n) hΔ_pos.le).trans
      (exp_neg_le_half_pow n hhoeff_exp)
  have hpow_in : (2 : ℝ) ^ (A_max - (min j₀ (n₁True n) : ℝ)) ≤ (1 / 2 : ℝ) ^ n :=
    two_rpow_neg_le_half_pow n (by rw [hmin_eq]; dsimp only [A_max]; linarith)
  have hpow_out : (2 : ℝ) ^ ((min j₀ (n₁True n) : ℝ) - K_min) ≤ (1 / 2 : ℝ) ^ n :=
    two_rpow_neg_le_half_pow n (by rw [hmin_eq]; dsimp only [K_min]; linarith)
  rw [hgame_eq, ← NNReal.coe_le_coe]
  dsimp only [n₁True, m₁True, B₁, t, w₀, m₀, j₀, Δ]
    at hcoll hrep_esc htail_acc htail_ent hpow_in hpow_out ⊢
  push_cast at hcoll hrep_esc hpow_in hpow_out ⊢
  linarith [hcoll, hrep_esc, htail_acc, htail_ent, hpow_in, hpow_out]

/-- **`[HHRVW2020]`, Section 5.1.5, Proof of Theorem 5.1, STEPS 1–3 (pp. 30–31)**: every
`InaccessibleEntropyFamily` yields a uniform polynomial-time `ShrinkingCollisionGrid` of strictly
`1`-bit shrinking hash candidates containing a sequence `goodIdx` that is collision-resistant on
random inputs against all uniform strict-PPT adversaries. -/
theorem InaccessibleEntropyFamily.exists_shrinkingCollisionGrid (F : InaccessibleEntropyFamily) :
    Nonempty ShrinkingCollisionGrid := by
  obtain ⟨N₀, hN₀⟩ := F.eventually_entropy_gap
  refine ⟨{
    inLen := fun n => shrunkHashInLen (ampRepInLen F n) (ampRepOutLen F n)
    outLen := fun n => shrunkHashOutLen (ampRepInLen F n) (ampRepOutLen F n)
    gridCount := ampGridCount F
    evalGrid := fun n q raw =>
      shrunkHashEvalWord (ampRepInLen F n) (ampRepOutLen F n)
        (ampRepEvalWord F n) (q * ampSlack F n) raw
    polyTime_inLen := computableInPolyTime_shrunkHashInLen_amp F
    polyTime_outLen := computableInPolyTime_shrunkHashOutLen_amp F
    polyTime_gridCount := computableInPolyTime_ampGridCount F
    polyTime_evalGrid := computableInPolyTime_shrunkHashEvalWord_amp F
    gridCount_pos := fun n => by unfold ampGridCount; omega
    le_outLen := fun n => by
      have hn₁ : n + 2 ≤ ampRepInLen F n := le_ampRepInLen F n
      have houtH : n + 1 ≤ outHashLen (ampRepInLen F n) := by
        unfold outHashLen inputHashInLen; omega
      unfold shrunkHashOutLen; omega
    outLen_add_one := fun n =>
      shrunkHashOutLen_add_one (by have := le_ampRepInLen F n; omega) (ampRepOutLen F n)
    length_evalGrid := fun n q raw => length_shrunkHashEvalWord _ _ _ _ _
    exists_good_candidate := ⟨ampGoodIdx F N₀, ampGoodIdx_lt_ampGridCount F hN₀, fun B hB => ?_⟩
  }⟩
  have hn₁True_poly : ComputableInPolyTime (fun k => ampReps F k * F.inLen k) encUnary encUnary :=
    ComputableInPolyTime.unary_mul' (computableInPolyTime_ampReps F) F.polyTime_inLen
  have hm₁True_poly : ComputableInPolyTime (fun k => ampReps F k * F.outLen k) encUnary encUnary :=
    ComputableInPolyTime.unary_mul' (computableInPolyTime_ampReps F) F.polyTime_outLen
  have hB₁_ppt := isPPT_shrunkHashEscapeInverter hn₁True_poly hm₁True_poly hB
  have hB₀_ppt := isPPT_repEscapeInverter (computableInPolyTime_ampReps F) F.polyTime_inLen hB₁_ppt
  have hesc_neg := F.escape_negligible _ hB₀_ppt
  have hdyad_pb : Cslib.PolynomiallyBounded (fun n => dyadicSize (ampReps F n)) :=
    dyadicSize_polynomiallyBounded.comp (computableInPolyTime_ampReps F).polynomiallyBounded
  have hgeom_neg : Negligible (fun n => (6 : ℝ≥0) * (1 / 2 : ℝ≥0) ^ n) :=
    (negligible_geometric (ratio := (1 / 2 : ℝ≥0)) (by norm_num)).const_mul 6
  refine negligible_of_eventually_le ((hesc_neg.polynomiallyBounded_mul hdyad_pb).add hgeom_neg) ?_
  filter_upwards [Filter.eventually_ge_atTop N₀] with n hn
  exact amp_randomCollisionGame_succProbability_le F hN₀ B hn

/-- **Constant-threshold adaptation of `[HHRVW2020]`, Section 4.2, Theorem 4.5 (p. 21) composed
with Section 5.1.5, Theorem 5.1, STEPS 1–3 (pp. 30–31)**: every uniform `OneWay` function yields a
uniform polynomial-time `ShrinkingCollisionGrid` of strictly `1`-bit shrinking hash candidates
containing a sequence that is collision-resistant on random inputs against all uniform strict-PPT
adversaries. -/
theorem OneWay.exists_shrinkingCollisionGrid {f : List Bool → List Bool} (hf : OneWay f) :
    Nonempty ShrinkingCollisionGrid :=
  let ⟨F⟩ := hf.exists_inaccessibleEntropyFamily
  F.exists_shrinkingCollisionGrid

end Cslib.Crypto
