/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
import Complexity.Computability.Complexity.FineGrained.CountingSparsificationUniform
import Complexity.Computability.Complexity.FineGrained.CountingParameterBounds
import Complexity.Computability.PolyTime.FineGrained.ParameterCheck
import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingParametersPolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.PolyTime.CNF.BranchedSparseCNFCounter
import Complexity.Computability.Complexity.FineGrained.SparseCountingScale
public import Complexity.Computability.Complexity.FineGrained.CountingEndpoint
import Complexity.Computability.Complexity.FineGrained.CountingSparsification
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceCounter
import Complexity.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceExactness
public import Complexity.Logics.Propositional.CNF.ModelCount.Declared

/-!
# Native declared-variable counting and the ETH/SETH consequences

For every fixed clause-width bound `k`, this module constructs one native counter on the full
external input `(N, φ)`, encoded by `encPair encUnary encCNF`. It returns the number of satisfying
assignments on `Finset.range N` when `validDeclaredInput k N φ` holds, and zero otherwise.
The contract covers every input, including small and zero declared sizes.

Time is bounded by `c * (2 ^ (A * interpolationScale N) * (L + 1) ^ e) + c`, and independent
workspace by `a * (L + 1) ^ b`, where `L` is the original external encoded input length. The
counter, both natural-valued resource functions, and all natural constants are fixed before the
input is supplied. No leaf, branch, schedule, certificate, or semantic hypothesis remains.

The proof combines uniform counting sparsification with Anton Kovsharov's concrete bounded-
incidence branch evaluator, its native resource certificates and exactness theorem, and the
normalized sparse leaf interface. The selected validity guard avoids charging invalid-support
inputs for their occurring-support search clock. The downstream bridge charges dense relabeling
in the original CNF encoding and derives subexponential-time `k`-SAT, zero SAT exponents, `¬ETH`,
and `¬SETH`.

The quantitative bound is the interpolation-scale conclusion of Sections 3–6 and Appendices A–B
of [OpenAI2026ETH]. It does not assert the sharper Appendix D runtime from Theorem 1.1.

## Main results

* `CountingNativeEndpoint.exists_declaredCounter`: exact guarded declared counting with fixed
  native witnesses and independent time and polynomial workspace on every input.
* `CountingNativeEndpoint.decidableInSubexpTime_KSAT`: subexponential-time `k`-SAT for every `k`.
* `CountingNativeEndpoint.satExponent_eq_zero`, `CountingNativeEndpoint.not_ETH`, and
  `CountingNativeEndpoint.not_SETH`: the fine-grained complexity consequences.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Sections 3–6 and
  Appendices A–B, through the imported counting and leaf interfaces.
-/

/-! ## Parameters, original input charges, and selected guard -/

namespace Cslib.Complexity.CountingNativeEndpointPrep

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification
open Cslib.Logic.PL.CNF (validDeclaredInput validDeclaredInput_eq_true_iff)
open Cslib.Logic.PL.ClauseSet.Sparsification Turing.MultiTapeTM
open CountingSparsify SubexponentialSAT SubexponentialSAT.ReplacementParams
open SubexponentialSAT.SparseCountingScale Filter

private abbrev Input := ℕ × CNF ℕ
private abbrev Context := Unit × ℕ
private abbrev FullInput := Unit × ℕ × CNF ℕ
private abbrev encInput := encPair encUnary encCNF
private abbrev encContext := encPair encUnit encUnary
private abbrev encFullInput := encPair encUnit encInput

private def inputSize (x : Input) : ℕ := (encInput x).length
private def width (k : ℕ) : ℕ := max 2 k
private def divisor (p : Context) : ℕ := BranchedSparseCNFCounter.leafSearchDivisor p.2
private def thresholdBase (k : ℕ) (p : Context) : ℕ :=
  BranchedSparseCNFCounter.leafThresholdBase k p.2
private def depthCoeff (k : ℕ) (p : Context) : ℕ := countingDepthCoeff (width k) (thresholdBase k p)
private def prepare (x : Input) : FullInput := ((), x)

private theorem two_le_width (k : ℕ) : 2 ≤ width k := le_max_left _ _
private theorem le_width (k : ℕ) : k ≤ width k := le_max_right _ _
private theorem one_le_divisor (p : Context) : 1 ≤ divisor p := le_max_left _ _
private theorem two_le_thresholdBase (k : ℕ) (p : Context) : 2 ≤ thresholdBase k p :=
  two_le_countingThresholdBase _ _

private theorem computableInPolyTime_divisor_unary :
    ComputableInPolyTime divisor encContext encUnary := by
  have hn : ComputableInPolyTime (fun p : Context => p.2) encContext encNat :=
    ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _)
  have hs := ParameterCheck.computableInPolyTime_numGroups_unary.comp hn
  have h : ComputableInPolyTime
      (fun p : Context => 1 + (numGroups p.2 - 1)) encContext encUnary := by fun_prop
  refine h.of_enc_eq fun p => congrArg encUnary ?_
  change max 1 (numGroups p.2) = 1 + (numGroups p.2 - 1)
  omega

private theorem computableInPolyTime_divisor :
    ComputableInPolyTime divisor encContext encNat :=
  ComputableInPolyTime.unary_to_binary.comp computableInPolyTime_divisor_unary

private theorem computableInPolyTime_thresholdBase (k : ℕ) :
    ComputableInPolyTime (thresholdBase k) encContext encNat :=
  (computableInPolyTime_countingThresholdBase (width k)).comp computableInPolyTime_divisor

private theorem computableInPolyTime_thresholdCompare (k : ℕ) :
    ComputableInPolyTime
      (fun x : Context × ℕ × ℕ => decide (countingThreshold (thresholdBase k x.1) x.2.1 ≤ x.2.2))
      (encPair encContext (encPair encUnary encUnary)) encBool :=
  computableInPolyTime_countingThreshold_le_binary.comp
    (((computableInPolyTime_thresholdBase k).comp (ComputableInPolyTime.fst _ _)).prod
      (ComputableInPolyTime.snd _ _))

private theorem treeBound (k : ℕ) (p : Context) :
    CountingTreeBound (thresholdBase k p) (width k) (divisor p) (depthCoeff k p)
      ((by decide : 1 ≤ 2).trans (two_le_thresholdBase k p))
      ((by decide : 1 ≤ 2).trans (two_le_width k)) :=
  countingTreeBound_countingThresholdBase _ (one_le_divisor p)

private theorem declaredSize_le_inputSize (x : Input) : x.1 ≤ inputSize x := by
  simp only [inputSize, encInput, length_encPair, encUnary_apply, List.length_replicate]
  omega

private theorem polyBounded_depthCoeff (k : ℕ) :
    PolyBounded inputSize (fun x => depthCoeff k ((), x.1)) :=
  polyBounded_countingDepthCoeff_numGroups (two_le_width k)
    (PolyBounded.self.mono declaredSize_le_inputSize)

private theorem polyBounded_depthCoeff_full (k : ℕ) :
    PolyBounded (fun x : FullInput => (encFullInput x).length)
      (fun x => depthCoeff k (x.1, x.2.1)) :=
  polyBounded_countingDepthCoeff_numGroups_encPair encUnit encCNF (two_le_width k)

private theorem computableInPolyTime_prepare :
    ComputableInPolyTime prepare encInput encFullInput := by
  unfold prepare
  fun_prop

private theorem length_prepare (x : Input) :
    (encFullInput (prepare x)).length = inputSize x + 1 := by
  simp [encFullInput, prepare, inputSize, encUnit_apply]

private theorem length_leaf_input (N : ℕ) (ψ : CNF ℕ) :
    (encPair encContext encCNF (((), N), ψ)).length = 2 * N + 3 + (encCNF ψ).length := by
  simp only [encContext, length_encPair, encUnit_apply, List.length_nil, encUnary_apply,
    List.length_replicate]
  omega

private theorem divisor_eq_numGroups {p : Context} (h : 1 ≤ numGroups p.2) :
    divisor p = numGroups p.2 := max_eq_right h

private theorem finite_clamped_sizes : {N : ℕ | divisor ((), N) ≠ numGroups N}.Finite :=
  (finite_numGroups_lt 1).subset fun N h => by
    change numGroups N < 1
    by_contra hn
    exact h (divisor_eq_numGroups (p := ((), N)) (Nat.le_of_not_gt hn))

private theorem computableInPolyTime_valid (k : ℕ) :
    ComputableInPolyTime (fun x : Input => validDeclaredInput k x.1 x.2) encInput encBool := by
  have hN := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.fst encUnary encCNF)
  have hlt : ComputableInPolyTime
      (fun x : Input × ℕ => decide (x.2 < x.1.1)) (encPair encInput encNat) encBool :=
    ComputableInPolyTime.binary_lt.comp
      ((ComputableInPolyTime.snd _ _).prod (hN.comp (ComputableInPolyTime.fst _ _)))
  have hs : ComputableInPolyTime
      (fun x : Input => x.2.vars.all fun v => decide (v < x.1)) encInput encBool :=
    ComputableInPolyTime.allWithInput (by fun_prop) hlt
  unfold validDeclaredInput
  fun_prop

private theorem numVars_le_of_valid {k : ℕ} {x : Input}
    (hx : validDeclaredInput k x.1 x.2 = true) : x.2.numVars ≤ x.1 := by
  have hsub := (validDeclaredInput_eq_true_iff.mp hx).2
  simpa only [CNF.numVars, Finset.card_range] using Finset.card_le_card hsub

/-- Polynomial workspace in the full Unit context remains polynomial in the original external
encoding. Guarding the false branch adds only the external input-length charge. -/
private theorem polyBounded_selectedSpace (k d : ℕ) {S : FullInput → ℕ}
    (hS : PolyBounded (fun x => (encFullInput x).length) S) :
    PolyBounded inputSize (fun x => (inputSize x + 1) ^ d +
      if validDeclaredInput k x.1 x.2 then S (prepare x) else inputSize x) := by
  have hprepared : PolyBounded inputSize (fun x => S (prepare x)) :=
    hS.comp computableInPolyTime_prepare.polyBounded_length
  have hbranch : PolyBounded inputSize
      (fun x => if validDeclaredInput k x.1 x.2 then S (prepare x) else inputSize x) :=
    (hprepared.add PolyBounded.self).mono fun x => by split_ifs <;> omega
  exact ((PolyBounded.self.add (.const 1)).pow d).add hbranch

/-- Reapply the already-present input guard to retain the cost of only the selected branch.
This avoids charging an invalid-support input for its unbounded occurring-support clock. -/
private theorem exists_computableInO_selectedSearch (k : ℕ)
    (g : Context × CNF ℕ → ℕ) {T S : FullInput → ℕ}
    (hsearch : ComputableInO
      (fun x : FullInput => searchDeclaredWith Prod.snd (thresholdBase k) divisor (width k) k g
        (x.1, x.2.1) x.2.2) encFullInput encNat T S) :
    ∃ d, ComputableInO
      (fun x : Input => searchDeclaredWith Prod.snd (thresholdBase k) divisor (width k) k g
        ((), x.1) x.2) encInput encNat
      (fun x => (inputSize x + 1) ^ d +
        if validDeclaredInput k x.1 x.2 then T (prepare x) else inputSize x)
      (fun x => (inputSize x + 1) ^ d +
        if validDeclaredInput k x.1 x.2 then S (prepare x) else inputSize x) := by
  obtain ⟨dp, _, hp⟩ := computableInPolyTime_prepare.exists_degree
  obtain ⟨dv, _, hv⟩ := (computableInPolyTime_valid k).exists_degree
  have hcore := hsearch.comp hp.inO
  have hguard := hv.inO.ite hcore
    (ComputableInO.const (encIn := encInput) 0)
  have hsum (x : Input) : (inputSize x + 1) ^ dv + (inputSize x + 1) ^ dp ≤
      2 * (inputSize x + 1) ^ (dv + dp) := by
    have hv' := Nat.pow_le_pow_right (by omega : 1 ≤ inputSize x + 1) (Nat.le_add_right dv dp)
    have hp' := Nat.pow_le_pow_right (by omega : 1 ≤ inputSize x + 1) (Nat.le_add_left dp dv)
    omega
  refine ⟨dv + dp, (hguard.mono 2 (fun x => ?_) (fun x => ?_)).of_enc_eq ?_⟩
  · change (inputSize x + 1) ^ dv +
      (if validDeclaredInput k x.1 x.2 then (inputSize x + 1) ^ dp + T (prepare x)
       else inputSize x) ≤ _
    split_ifs <;> have := hsum x <;> omega
  · change (inputSize x + 1) ^ dv +
      (if validDeclaredInput k x.1 x.2 then (inputSize x + 1) ^ dp + S (prepare x)
       else inputSize x) ≤ _
    split_ifs <;> have := hsum x <;> omega
  · intro x
    by_cases hx : validDeclaredInput k x.1 x.2 = true <;>
      simp [Function.comp_apply, prepare, searchDeclaredWith, hx]

end Cslib.Complexity.CountingNativeEndpointPrep

/-! ## All-input clamped round estimate -/

namespace Cslib.Complexity.SubexponentialSAT

open Filter ReplacementParams

/-- One fixed natural coefficient bounds the clamped round count, including its extra terminal
step, for every `N` and `v ≤ N`. No lower bound on `N` or `numGroups N` is assumed. -/
private theorem exists_clamped_rounds_le_interpolationScale :
    ∃ C : ℕ, 0 < C ∧ ∀ N v : ℕ, v ≤ N →
      ((2 ^ (v / max 1 (numGroups N) + 2) + 1 : ℕ) : ℝ) ≤
        (C : ℝ) * (2 : ℝ) ^ (16 * interpolationScale N) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (SparseCountingScale.eventually_two_le_numGroups.and
      SparseCountingScale.eventually_div_numGroups_le)
  let C : ℕ := 2 ^ (N₀ + 2) + 5
  refine ⟨C, by dsimp [C]; positivity, fun N v hv => ?_⟩
  have hscale : (1 : ℝ) ≤ (2 : ℝ) ^ (16 * interpolationScale N) :=
    Real.one_le_rpow one_le_two (mul_nonneg (by norm_num) (interpolationScale_nonneg N))
  by_cases hN : N < N₀
  · have hexp : v / max 1 (numGroups N) + 2 ≤ N₀ + 2 :=
      Nat.add_le_add_right ((Nat.div_le_self _ _).trans (hv.trans hN.le)) 2
    have hrounds : 2 ^ (v / max 1 (numGroups N) + 2) + 1 ≤ C := by
      have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp
      dsimp [C]
      omega
    exact (Nat.cast_le.mpr hrounds).trans
      (le_mul_of_one_le_right (Nat.cast_nonneg C) hscale)
  · obtain ⟨hgroups, hdiv⟩ := hN₀ N (Nat.le_of_not_lt hN)
    have hclamp : max 1 (numGroups N) = numGroups N := max_eq_right (by omega)
    have hexp : ((v / max 1 (numGroups N) : ℕ) : ℝ) ≤ 16 * interpolationScale N := by
      calc
        ((v / max 1 (numGroups N) : ℕ) : ℝ) ≤ (v : ℝ) / (max 1 (numGroups N) : ℕ) :=
          Nat.cast_div_le
        _ ≤ (N : ℝ) / (numGroups N : ℝ) := by
          rw [hclamp]
          exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hv) (Nat.cast_nonneg _)
        _ ≤ 16 * interpolationScale N := hdiv
    have htwo : (2 : ℝ) ^ (v / max 1 (numGroups N)) ≤
        (2 : ℝ) ^ (16 * interpolationScale N) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two hexp
    have hrounds : ((2 ^ (v / max 1 (numGroups N) + 2) + 1 : ℕ) : ℝ) ≤
        5 * (2 : ℝ) ^ (16 * interpolationScale N) := by
      push_cast
      rw [pow_add]
      norm_num
      nlinarith
    have hC : (5 : ℝ) ≤ C := Nat.cast_le.mpr (Nat.le_add_left 5 _)
    exact hrounds.trans (mul_le_mul_of_nonneg_right hC (by positivity))

end Cslib.Complexity.SubexponentialSAT

/-! ## Dense counting and SAT consequences -/

namespace Cslib.Complexity.CountingNativeEndpointConsequencesPrep

open Cslib.Logic.PL Turing.MultiTapeTM CountingSparsify SubexponentialSAT
open Cslib.Logic.PL.CNF (validDeclaredInput validDeclaredInput_eq_true_iff)

private abbrev Input := ℕ × CNF ℕ
private abbrev encInput := encPair encUnary encCNF
private def declareInput (φ : CNF ℕ) : Input := (φ.numVars, φ)

private theorem computableInPolyTime_declareInput :
    ComputableInPolyTime declareInput encCNF encInput := by
  unfold declareInput
  fun_prop

private theorem length_declareInput (φ : CNF ℕ) :
    (encInput (declareInput φ)).length + 1 ≤ 3 * ((encCNF φ).length + 1) := by
  have hn := φ.numVars_le_length_vars.trans (SAT.length_vars_le φ)
  simp only [declareInput, encInput, length_encPair, encUnary_apply, List.length_replicate]
  omega

private theorem dense_spec {k : ℕ} {count : Input → ℕ}
    (hspec : ∀ x, count x = if validDeclaredInput k x.1 x.2 then
      x.2.modelCountOn (Finset.range x.1) else 0)
    {ψ : CNF ℕ} (hw : ∀ cl ∈ ψ, cl.length ≤ k)
    (hdense : ψ.vars.toFinset = Finset.range ψ.numVars) :
    count (declareInput ψ) = ψ.modelCountOn (Finset.range ψ.numVars) := by
  have hv := validDeclaredInput_eq_true_iff.mpr ⟨hw, hdense.subset⟩
  simpa only [declareInput, hv, ↓reduceIte] using hspec (declareInput ψ)

/-- Construct the common allowance needed by the existing dense-counting bridge only after
charging preparation and transferring the independent workspace bound to `encCNF`. -/
private theorem exists_common_dense_resources {count : Input → ℕ} {T S : Input → ℕ}
    (hcount : ComputableInO count encInput encNat T S) {A c e a b : ℕ}
    (hT : ∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
      (((encInput x).length : ℝ) + 1) ^ e) + c)
    (hS : ∀ x, S x ≤ a * ((encInput x).length + 1) ^ b) :
    ∃ t : CNF ℕ → ℕ, ∃ C E : ℕ,
      ComputableInO (fun φ => count (declareInput φ)) encCNF encNat t t ∧
      ∀ φ, (t φ : ℝ) ≤ C * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars) *
        (((encCNF φ).length : ℝ) + 1) ^ E) + C := by
  obtain ⟨d, _, hp⟩ := computableInPolyTime_declareInput.exists_degree
  have hcomp := hcount.comp hp.inO
  let P (φ : CNF ℕ) := ((encCNF φ).length + 1) ^ d + S (declareInput φ)
  have hspace : PolyBounded (fun x => (encInput x).length) S :=
    PolyBounded.of_forall_le a b hS
  have hP : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) P :=
    ((PolyBounded.self.add (.const 1)).pow d).add
      (hspace.comp computableInPolyTime_declareInput.polyBounded_length)
  obtain ⟨p, q, hP⟩ := hP.exists_le
  let t (φ : CNF ℕ) := P φ + T (declareInput φ)
  let C := p + c * 3 ^ e + c
  refine ⟨t, C, q + e, hcomp.mono_le (fun φ => ?_) (fun φ => ?_), fun φ => ?_⟩
  · dsimp only [t, P]
    omega
  · dsimp only [t, P]
    omega
  · let Y : ℝ := (encCNF φ).length + 1
    let X : ℝ := (2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars)
    have hY : 1 ≤ Y := by dsimp [Y]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hX : 1 ≤ X :=
      Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg A) (interpolationScale_nonneg _))
    have hYq : Y ^ q ≤ Y ^ (q + e) := pow_le_pow_right₀ hY (by omega)
    have hYe : Y ^ e ≤ Y ^ (q + e) := pow_le_pow_right₀ hY (by omega)
    have hYP : Y ^ (q + e) ≤ X * Y ^ (q + e) :=
      le_mul_of_one_le_left (by positivity) hX
    have hPr : (P φ : ℝ) ≤ p * Y ^ q := by
      dsimp only [Y]
      exact_mod_cast hP φ
    have hlen : ((encInput (declareInput φ)).length : ℝ) + 1 ≤ 3 * Y := by
      dsimp only [Y]
      exact_mod_cast length_declareInput φ
    have hpower : (((encInput (declareInput φ)).length : ℝ) + 1) ^ e ≤
        (3 : ℝ) ^ e * Y ^ (q + e) := by
      calc
        _ ≤ (3 * Y) ^ e := pow_le_pow_left₀ (by positivity) hlen e
        _ = 3 ^ e * Y ^ e := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hYe (by positivity)
    have hPfinal : (P φ : ℝ) ≤ p * (X * Y ^ (q + e)) :=
      hPr.trans (mul_le_mul_of_nonneg_left (hYq.trans hYP) (Nat.cast_nonneg p))
    have hTfinal : (T (declareInput φ) : ℝ) ≤
        (c : ℝ) * 3 ^ e * (X * Y ^ (q + e)) + c := by
      have hT' := hT (declareInput φ)
      change (T (declareInput φ) : ℝ) ≤
        c * (X * (((encInput (declareInput φ)).length : ℝ) + 1) ^ e) + c at hT'
      refine hT'.trans ?_
      have hmul := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ X)) (Nat.cast_nonneg c)
      nlinarith
    have hc : (c : ℝ) ≤ C := by exact_mod_cast (show c ≤ C by dsimp [C]; omega)
    have hcoeff : (p : ℝ) + c * 3 ^ e ≤ C := by
      exact_mod_cast (show p + c * 3 ^ e ≤ C by dsimp [C]; omega)
    have hfactor : 0 ≤ X * Y ^ (q + e) := by positivity
    change ((P φ + T (declareInput φ) : ℕ) : ℝ) ≤ C * (X * Y ^ (q + e)) + C
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hfactor]

private theorem KSAT_of_declared_contract {k : ℕ} {count : Input → ℕ} {T S : Input → ℕ}
    (hcount : ComputableInO count encInput encNat T S)
    (hspec : ∀ x, count x = if validDeclaredInput k x.1 x.2 then
      x.2.modelCountOn (Finset.range x.1) else 0) {A c e a b : ℕ}
    (hT : ∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
      (((encInput x).length : ℝ) + 1) ^ e) + c)
    (hS : ∀ x, S x ≤ a * ((encInput x).length + 1) ^ b) :
    DecidableInSubexpTime (KSAT k) encCNF CNF.numVars := by
  obtain ⟨t, C, E, hc, ht⟩ := exists_common_dense_resources hcount hT hS
  exact DecidableInSubexpTime.KSAT_of_dense_modelCount_interpolationScale hc
    (fun _ hw hdense => dense_spec hspec hw hdense) ht

/-- The complete accepted contract is still a premise here. These downstream consequences become
unconditional only when the native construction supplies that contract for every fixed width. -/
private theorem consequences_of_declared_contract
    (h : ∀ k : ℕ, ∃ count : Input → ℕ, ∃ T S : Input → ℕ, ∃ A c e a b : ℕ,
      ComputableInO count encInput encNat T S ∧
      (∀ x, count x = if validDeclaredInput k x.1 x.2 then
        x.2.modelCountOn (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encInput x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encInput x).length + 1) ^ b)) :
    (∀ k, satExponent k = 0) ∧ ¬ETH ∧ ¬SETH := by
  have hSAT (k : ℕ) : DecidableInSubexpTime (KSAT k) encCNF CNF.numVars := by
    obtain ⟨count, T, S, A, c, e, a, b, hc, hspec, hT, hS⟩ := h k
    exact KSAT_of_declared_contract hc hspec hT hS
  exact ⟨fun k => satExponent_eq_zero_of_decidableInSubexpTime (hSAT k),
    not_ETH_of_decidableInSubexpTime (hSAT 3), not_SETH_of_forall_decidableInSubexpTime hSAT⟩

end Cslib.Complexity.CountingNativeEndpointConsequencesPrep

/-! ## Uniform search and normalized leaf assembly -/

namespace Cslib.Complexity.CountingNativeEndpointPrep

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Logic.PL.CNF.Sparsification
open Cslib.Logic.PL.ClauseSet.Sparsification Turing.MultiTapeTM Cslib.GenericRAM
open CountingSparsify SubexponentialSAT SubexponentialSAT.SparsePolyCounter
open BranchedSparseCNFCounter

private abbrev LeafInput := Context × CNF ℕ
private abbrev encLeafInput := encPair encContext encCNF

/-- The prefix-size charge includes the original declared unary size and retained Unit context. -/
private def leafSize (k : ℕ) (x : FullInput) : ℕ :=
  2 * x.2.1 + 3 + nodeBound (width k) (depthCoeff k (x.1, x.2.1)) x.2.2

private theorem polyBounded_leafSize (k : ℕ) :
    PolyBounded (fun x : FullInput => (encFullInput x).length) (leafSize k) := by
  have hN : PolyBounded (fun x : FullInput => (encFullInput x).length) (fun x => x.2.1) :=
    PolyBounded.self.mono fun x => by
      simp only [encFullInput, encInput, length_encPair, encUnary_apply, List.length_replicate]
      omega
  have hL : PolyBounded (fun x : FullInput => (encFullInput x).length)
      (fun x => (encCNF x.2.2).length) :=
    PolyBounded.self.mono fun x =>
      (length_le_encPair_right encUnary encCNF x.2).trans
        (length_le_encPair_right encUnit encInput x)
  have hn := hL.mono fun x => x.2.2.numVars_le_length_vars.trans (SAT.length_vars_le x.2.2)
  have hm := hL.mono fun x => length_le_length_encList _ x.2.2
  have hnode := ((hm.add (.const 1)).add
    ((PolyBounded.const (width k)).mul ((polyBounded_depthCoeff_full k).mul hn))).mul
    (((PolyBounded.const 2).mul ((PolyBounded.const (width k)).mul
      (((PolyBounded.const 2).mul hL).add (.const 1)))).add (.const 1))
  exact (((PolyBounded.const 2).mul hN).add (.const 3)).add hnode

/-- Every active prefix, including the terminal prefix, meets the exact supplier clause cap. -/
private theorem prefix_leaf_bounds (k : ℕ) (g : LeafInput → ℕ) (x : FullInput)
    (hx : validDeclaredInput k x.2.1 x.2.2 = true) (i : ℕ)
    (hactive : let p := (x.1, x.2.1)
      let st := (step (thresholdBase k p) (width k) (fun ψ => g (p, ψ)))^[i] (init k x.2.2)
      st.2.1.isEmpty = false ∧ isSparse (countingThreshold (thresholdBase k p)) (width k)
        (st.2.1.headD []) = true) :
    let p := (x.1, x.2.1)
    let ψ := ((step (thresholdBase k p) (width k) (fun ψ => g (p, ψ)))^[i]
      (init k x.2.2)).2.1.headD []
    ψ.length ≤ leafOccBound k x.2.1 * x.2.1 + 1 ∧
      (encLeafInput (p, ψ)).length ≤ leafSize k x := by
  have hb := (iterate_step_prefix_bounds
    ((by decide : 1 ≤ 2).trans (two_le_thresholdBase k (x.1, x.2.1)))
    ((by decide : 1 ≤ 2).trans (two_le_width k))
    (two_le_thresholdBase k (x.1, x.2.1)) (le_width k) (treeBound k (x.1, x.2.1))
    (fun ψ => g ((x.1, x.2.1), ψ)) x.2.2 i).2.2.2 hactive
  have hn := numVars_le_of_valid (x := x.2) hx
  refine ⟨?_, ?_⟩
  · rw [leafOccBound_eq_occBound]
    exact hb.2.2.2.1.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hn) 1)
  · simp only [encLeafInput, encContext, length_encPair, encUnit_apply,
      List.length_nil, encUnary_apply, List.length_replicate, leafSize]
    have := hb.2.2.2.2
    omega

/-- The polynomial part of the selected search cost and the ceiled leaf envelope combine with
one fixed all-input round estimate. Small declared sizes are already absorbed in that estimate. -/
private theorem selected_time_envelope (k d c e Cₜ dₜ Aₜ : ℕ) :
    let U (x : FullInput) := Cₜ * (leafSize k x + 1) ^ dₜ
    let R (x : FullInput) := ⌈(U x : ℝ) * (2 : ℝ) ^ ((Aₜ : ℝ) * interpolationScale x.2.1)⌉₊
    let W (x : FullInput) := c * ((encFullInput x).length + 1) ^ e
    ∃ C E : ℕ, ∀ x : Input,
      (((inputSize x + 1) ^ d + if validDeclaredInput k x.1 x.2 then
        W (prepare x) + (rounds (divisor ((), x.1)) x.2 + 1) *
          (W (prepare x) + R (prepare x)) else inputSize x : ℕ) : ℝ) ≤
        C * ((2 : ℝ) ^ (((Aₜ + 16 : ℕ) : ℝ) * interpolationScale x.1) *
          ((inputSize x : ℝ) + 1) ^ E) + C := by
  dsimp only
  let U (x : FullInput) := Cₜ * (leafSize k x + 1) ^ dₜ
  let R (x : FullInput) := ⌈(U x : ℝ) * (2 : ℝ) ^ ((Aₜ : ℝ) * interpolationScale x.2.1)⌉₊
  let W (x : FullInput) := c * ((encFullInput x).length + 1) ^ e
  let P (x : Input) := (inputSize x + 1) ^ d + W (prepare x) + U (prepare x) + 1 + inputSize x
  have hW : PolyBounded (fun x : FullInput => (encFullInput x).length) W :=
    (PolyBounded.const c).mul ((PolyBounded.self.add (.const 1)).pow e)
  have hU : PolyBounded (fun x : FullInput => (encFullInput x).length) U :=
    (PolyBounded.const Cₜ).mul (((polyBounded_leafSize k).add (.const 1)).pow dₜ)
  have hP : PolyBounded inputSize P :=
    (((((PolyBounded.self.add (.const 1)).pow d).add
      (hW.comp computableInPolyTime_prepare.polyBounded_length)).add
      (hU.comp computableInPolyTime_prepare.polyBounded_length)).add (.const 1)).add
        PolyBounded.self
  obtain ⟨Cₚ, E, hP⟩ := hP.exists_le
  obtain ⟨Cq, _, hq⟩ := exists_clamped_rounds_le_interpolationScale
  refine ⟨(Cq + 1) * Cₚ, E, fun x => ?_⟩
  let X : ℝ := (2 : ℝ) ^ ((Aₜ : ℝ) * interpolationScale x.1)
  let Y : ℝ := (2 : ℝ) ^ (16 * interpolationScale x.1)
  let p : ℝ := Cₚ * ((inputSize x : ℝ) + 1) ^ E
  have hX : 1 ≤ X := Real.one_le_rpow one_le_two
    (mul_nonneg (Nat.cast_nonneg Aₜ) (interpolationScale_nonneg _))
  have hY : 1 ≤ Y := Real.one_le_rpow one_le_two
    (mul_nonneg (by norm_num) (interpolationScale_nonneg _))
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hPXY : p ≤ p * (X * Y) :=
    le_mul_of_one_le_right hp (one_le_mul_of_one_le_of_one_le hX hY)
  have hPr : (P x : ℝ) ≤ p := by
    dsimp only [p]
    exact_mod_cast hP x
  have hceil : (R (prepare x) : ℝ) ≤ (U (prepare x) : ℝ) * X + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (U (prepare x) : ℝ) * X)).le
  have hjoin : X * Y = (2 : ℝ) ^ (((Aₜ + 16 : ℕ) : ℝ) * interpolationScale x.1) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  have htarget : (Cq + 1 : ℝ) * p * (X * Y) ≤
      (((Cq + 1) * Cₚ : ℕ) : ℝ) *
        ((2 : ℝ) ^ (((Aₜ + 16 : ℕ) : ℝ) * interpolationScale x.1) *
          ((inputSize x : ℝ) + 1) ^ E) + ((Cq + 1) * Cₚ : ℕ) := by
    rw [hjoin]
    dsimp only [p]
    push_cast
    nlinarith [show (0 : ℝ) ≤ (Cq + 1) * Cₚ by positivity]
  by_cases hx : validDeclaredInput k x.1 x.2 = true
  · have hround : ((rounds (divisor ((), x.1)) x.2 + 1 : ℕ) : ℝ) ≤ Cq * Y := by
      simpa only [rounds, CNF.length_distinctVars, divisor, leafSearchDivisor, Y] using
        hq x.1 x.2.numVars (numVars_le_of_valid hx)
    have hpol : (((inputSize x + 1) ^ d + W (prepare x) : ℕ) : ℝ) ≤ p := by
      apply le_trans _ hPr
      exact_mod_cast (show (inputSize x + 1) ^ d + W (prepare x) ≤ P x by dsimp [P]; omega)
    have hinside : ((W (prepare x) + R (prepare x) : ℕ) : ℝ) ≤ p * X := by
      have hWU : ((W (prepare x) + U (prepare x) + 1 : ℕ) : ℝ) ≤ p := by
        apply le_trans _ hPr
        exact_mod_cast (show W (prepare x) + U (prepare x) + 1 ≤ P x by dsimp [P]; omega)
      have hscale := mul_le_mul_of_nonneg_right hWU (by positivity : 0 ≤ X)
      push_cast at hscale ⊢
      nlinarith [mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg (W (prepare x)))]
    have hprod := mul_le_mul hround hinside (by positivity) (by positivity)
    have hwhole := add_le_add hpol hprod
    change (((inputSize x + 1) ^ d + if validDeclaredInput k x.1 x.2 then
      W (prepare x) + (rounds (divisor ((), x.1)) x.2 + 1) *
        (W (prepare x) + R (prepare x)) else inputSize x : ℕ) : ℝ) ≤ _
    simp only [hx, ↓reduceIte, Nat.cast_add, Nat.cast_mul]
    push_cast at hwhole htarget ⊢
    apply le_trans _ htarget
    nlinarith
  · change (((inputSize x + 1) ^ d + if validDeclaredInput k x.1 x.2 then
      W (prepare x) + (rounds (divisor ((), x.1)) x.2 + 1) *
        (W (prepare x) + R (prepare x)) else inputSize x : ℕ) : ℝ) ≤ _
    simp only [hx, Bool.false_eq_true, ↓reduceIte]
    have hf : (((inputSize x + 1) ^ d + inputSize x : ℕ) : ℝ) ≤ p := by
      apply le_trans _ hPr
      exact_mod_cast (show (inputSize x + 1) ^ d + inputSize x ≤ P x by dsimp [P]; omega)
    apply hf.trans (hPXY.trans (le_trans ?_ htarget))
    calc
      p * (X * Y) ≤ ((Cq : ℝ) + 1) * (p * (X * Y)) :=
        le_mul_of_one_le_left (by positivity) (le_add_of_nonneg_left (Nat.cast_nonneg Cq))
      _ = _ := by ring

/-- Private generic join; its leaf premises are discharged by the frozen #1337 interface below. -/
private theorem exists_declared_contract_of_leaf (k : ℕ) (g : LeafInput → ℕ)
    (cg : NativeCertificate g encLeafInput encNat)
    (hcorrect : ∀ p ψ, (∀ cl ∈ ψ, cl.length ≤ k) →
      ψ.vars.toFinset ⊆ Finset.range p.2 → g (p, ψ) = ψ.modelCount)
    (hcap : ∀ x, g x ≤ 2 ^ x.2.numVars)
    (hspace : PolyBounded (fun x => (encLeafInput x).length) cg.space)
    (Cₜ dₜ Aₜ : ℕ)
    (htime : ∀ x, x.2.length ≤ leafOccBound k x.1.2 * x.1.2 + 1 →
      (cg.time x : ℝ) ≤ Cₜ * (((encLeafInput x).length : ℝ) + 1) ^ dₜ *
        (2 : ℝ) ^ ((Aₜ : ℝ) * interpolationScale x.1.2)) :
    ∃ (count : Input → ℕ) (T S : Input → ℕ) (A c e a b : ℕ),
      ComputableInO count encInput encNat T S ∧
      (∀ x, count x = if validDeclaredInput k x.1 x.2 then
        x.2.modelCountOn (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encInput x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encInput x).length + 1) ^ b) := by
  let R (x : FullInput) := ⌈((Cₜ * (leafSize k x + 1) ^ dₜ : ℕ) : ℝ) *
    (2 : ℝ) ^ ((Aₜ : ℝ) * interpolationScale x.2.1)⌉₊
  obtain ⟨Cₛ, dₛ, hspace⟩ := hspace.exists_le
  let Q (x : FullInput) := Cₛ * (leafSize k x + 1) ^ dₛ
  have hQ : PolyBounded (fun x : FullInput => (encFullInput x).length) Q :=
    (PolyBounded.const Cₛ).mul (((polyBounded_leafSize k).add (.const 1)).pow dₛ)
  obtain ⟨c, e, hsearch, hS⟩ := exists_computableInO_searchDeclaredWith
    (computableInPolyTime_divisor) (computableInPolyTime_thresholdCompare k)
    (fun p => (by decide : 1 ≤ 2).trans (two_le_thresholdBase k p))
    ((by decide : 1 ≤ 2).trans (two_le_width k)) (two_le_thresholdBase k) (le_width k)
    (treeBound k) (polyBounded_depthCoeff_full k) cg.computes
    (fun x _ i _ _ => hcap _) (R := R) (Q := Q)
    (fun x hx i _ ha => by
      obtain ⟨hclause, hlen⟩ := prefix_leaf_bounds k g x hx i ha
      let ψ := ((step (thresholdBase k (x.1, x.2.1)) (width k)
        (fun ψ => g ((x.1, x.2.1), ψ)))^[i] (init k x.2.2)).2.1.headD []
      have ht := htime ((x.1, x.2.1), ψ) hclause
      have hlenr : ((encLeafInput ((x.1, x.2.1), ψ)).length : ℝ) + 1 ≤
          (leafSize k x : ℝ) + 1 := by
        exact_mod_cast Nat.add_le_add_right hlen 1
      have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
        ((encLeafInput ((x.1, x.2.1), ψ)).length : ℝ) + 1) hlenr dₜ
      suffices hr : (cg.time ((x.1, x.2.1), ψ) : ℝ) ≤ (R x : ℝ) from Nat.cast_le.mp hr
      apply (ht.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg Cₜ)) (by positivity))).trans
      simpa only [R, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
        (Nat.le_ceil (((Cₜ * (leafSize k x + 1) ^ dₜ : ℕ) : ℝ) *
          (2 : ℝ) ^ ((Aₜ : ℝ) * interpolationScale x.2.1))))
    (fun x hx i _ ha => by
      have hlen := (prefix_leaf_bounds k g x hx i ha).2
      exact (hspace ((x.1, x.2.1), ((step (thresholdBase k (x.1, x.2.1)) (width k)
        (fun ψ => g ((x.1, x.2.1), ψ)))^[i] (init k x.2.2)).2.1.headD [])).trans
        (Nat.mul_le_mul_left Cₛ
        (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) dₛ))) hQ
  obtain ⟨d, hselected⟩ := exists_computableInO_selectedSearch k g hsearch
  obtain ⟨a, b, hab⟩ := (polyBounded_selectedSpace k d hS).exists_le
  obtain ⟨C, E, hT⟩ := selected_time_envelope k d c e Cₜ dₜ Aₜ
  refine ⟨_, _, _, Aₜ + 16, C, E, a, b, hselected, ?_, hT, hab⟩
  intro x
  exact searchDeclaredWith_eq_ite_modelCountOn
    ((by decide : 1 ≤ 2).trans (two_le_thresholdBase k ((), x.1)))
    ((by decide : 1 ≤ 2).trans (two_le_width k)) (two_le_thresholdBase k ((), x.1))
    (le_width k) (treeBound k ((), x.1)) (fun ψ hw _ hsub => hcorrect _ ψ hw hsub) x.2

/-- The accepted full declared-count telescope, conditional privately only on the remaining
concrete branch evaluator obligations. No leaf, prefix, clock or final-guard premise remains. -/
private theorem exists_declared_contract (k N₀_branch : ℕ) {branchEval : BranchEvalInput → ℕ}
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbranch : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) = HeavyBranchFold.rootCount n' eqs')
    (hs_br : PolyBounded (fun x => (encBranchEvalInput x).length) cBranch.space)
    (hbr_time : BranchPolylogTimeBound N₀_branch cBranch) :
    ∃ (count : Input → ℕ) (T S : Input → ℕ) (A c e a b : ℕ),
      ComputableInO count encInput encNat T S ∧
      (∀ x, count x = if validDeclaredInput k x.1 x.2 then
        x.2.modelCountOn (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encInput x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encInput x).length + 1) ^ b) := by
  have hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n' := by
    intro n' eqs' hf
    rw [hbranch n' eqs' hf]
    exact HeavyBranchFold.rootCount_le_two_pow n' eqs'
  obtain ⟨N₀_leaf, N₀_top, Cₜ, dₜ, Aₜ, _, ht⟩ :=
    exists_branchedSparseCNF_time_bound k N₀_branch cBranch hbound hs_br hbr_time
  exact exists_declared_contract_of_leaf k
    (branchedSparseCNFLeafCounter k N₀_leaf N₀_top N₀_branch branchEval)
    (branchedSparseCNFLeafCertificate k N₀_leaf N₀_top N₀_branch cBranch hbound)
    (fun p ψ hw hsub => branchedSparseCNFLeafCounter_eq_modelCount hbranch p.1 p.2 ψ hw hsub)
    (branchedSparseCNFLeafCounter_le_two_pow_numVars k N₀_leaf N₀_top N₀_branch branchEval)
    (polyBounded_branchedSparseCNFLeafCertificate_space k N₀_leaf N₀_top N₀_branch
      cBranch hbound hs_br) Cₜ dₜ Aₜ (fun x hx => (ht x hx).2)

/-- Reuse the existing dense-relabeling bridge; arbitrary raw variable labels are never assumed
already dense. The same remaining concrete branch premises stay explicit and private. -/
private theorem consequences_of_branch_contract (N₀_branch : ℕ)
    {branchEval : BranchEvalInput → ℕ}
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbranch : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) = HeavyBranchFold.rootCount n' eqs')
    (hs_br : PolyBounded (fun x => (encBranchEvalInput x).length) cBranch.space)
    (hbr_time : BranchPolylogTimeBound N₀_branch cBranch) :
    (∀ k, satExponent k = 0) ∧ ¬ETH ∧ ¬SETH :=
  CountingNativeEndpointConsequencesPrep.consequences_of_declared_contract
    (fun k => exists_declared_contract k N₀_branch cBranch hbranch hs_br hbr_time)

end Cslib.Complexity.CountingNativeEndpointPrep

/-! ## Concrete bounded-incidence resources -/

namespace Cslib.Complexity.CountingNativeEndpointPrep

open Cslib.Logic.PL.CNF Cslib.GenericRAM Turing.MultiTapeTM
open SubexponentialSAT SubexponentialSAT.SparsePolyCounter

/-- Specialize the reviewed declared-count contract to the published native bounded-incidence
resources. Its local exactness premise is discharged by the public endpoint below. No restriction
is added to the external inputs or to the global polynomial workspace bound. -/
private theorem exists_declared_contract_of_boundedIncidence (k N₀_branch : ℕ)
    (hbranch : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      evalBoundedIncidenceBranch (prepareBranchEvalInput (n', eqs')) =
        HeavyBranchFold.rootCount n' eqs') :
    ∃ (count : Input → ℕ) (T S : Input → ℕ) (A c e a b : ℕ),
      ComputableInO count encInput encNat T S ∧
      (∀ x, count x = if validDeclaredInput k x.1 x.2 then
        x.2.modelCountOn (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encInput x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encInput x).length + 1) ^ b) :=
  exists_declared_contract k N₀_branch boundedIncidenceBranchCertificate hbranch
    polyBounded_boundedIncidenceBranchCertificate_space
    (branchPolylogTimeBound_boundedIncidenceBranchCertificate N₀_branch)

end Cslib.Complexity.CountingNativeEndpointPrep

/-! ## Unconditional native endpoint -/

namespace Cslib.Complexity.CountingNativeEndpoint

open Cslib.Logic.PL Cslib.Logic.PL.CNF Turing.MultiTapeTM
open SubexponentialSAT SubexponentialSAT.SparsePolyCounter

/-- For each fixed width bound, one native counter computes the exact guarded declared-variable
model count on every unary-size/CNF input. Both resource functions and all constants are fixed
before the input; time uses the interpolation scale and workspace is polynomial in the original
external encoded input length. -/
public theorem exists_declaredCounter (k : ℕ) :
    ∃ (count : ℕ × CNF ℕ → ℕ) (T S : ℕ × CNF ℕ → ℕ) (A c e a b : ℕ),
      ComputableInO count (encPair encUnary encCNF) encNat T S ∧
      (∀ x, count x = if validDeclaredInput k x.1 x.2 then
        x.2.modelCountOn (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encPair encUnary encCNF x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encPair encUnary encCNF x).length + 1) ^ b) :=
  CountingNativeEndpointPrep.exists_declared_contract_of_boundedIncidence k 0
    (fun _ _ hfeas => evalBoundedIncidenceBranch_eq_rootCount hfeas)

/-- Every fixed-width `k`-SAT problem is decidable in subexponential time in its number of
occurring variables, with the CNF encoded in the native model. Arbitrary variable labels are
handled by the existing dense-relabeling bridge. -/
public theorem decidableInSubexpTime_KSAT (k : ℕ) :
    DecidableInSubexpTime (KSAT k) encCNF CNF.numVars := by
  obtain ⟨count, T, S, A, c, e, a, b, hc, hspec, hT, hS⟩ := exists_declaredCounter k
  exact CountingNativeEndpointConsequencesPrep.KSAT_of_declared_contract hc hspec hT hS

/-- The SAT exponent vanishes for every fixed clause width. -/
public theorem satExponent_eq_zero (k : ℕ) : satExponent k = 0 :=
  satExponent_eq_zero_of_decidableInSubexpTime (decidableInSubexpTime_KSAT k)

/-- The native counting construction refutes the Exponential Time Hypothesis. -/
public theorem not_ETH : ¬ETH :=
  not_ETH_of_decidableInSubexpTime (decidableInSubexpTime_KSAT 3)

/-- The native counting construction refutes the Strong Exponential Time Hypothesis. -/
public theorem not_SETH : ¬SETH :=
  not_SETH_of_forall_decidableInSubexpTime decidableInSubexpTime_KSAT

end Cslib.Complexity.CountingNativeEndpoint
