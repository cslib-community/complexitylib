/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.GapETH
public import CslibFrontier.Computability.Complexity.FineGrained.SingleSubexp
public import CslibFrontier.Computability.Complexity.Problems.SAT.Declared
public import CslibFrontier.Computability.PolyTime.CNF.DeclaredInput
public import CslibFrontier.Logics.Propositional.CNF.ModelCount.Declared
import CslibFrontier.Computability.Complexity.FineGrained.CountingNativeEndpoint
import CslibFrontier.Computability.Complexity.FineGrained.CountingNativeModelCount
import CslibFrontier.Computability.Complexity.FineGrained.SparseCountingScale
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.Nat.Power

/-!
# Native model-counter consequences across counting, single-machine, randomized, and gap hypotheses

`CslibFrontier.Computability.Complexity.FineGrained.CountingExponents`, `SingleSubexp`,
`Randomized`, and `GapETH` develop the classical fine-grained rate, error-model, and reduction
hierarchy without importing `CountingNativeEndpoint`. Mirroring how `CountingNativeEndpoint`
instantiates `Exponents`, this leaf module connects `CountingNativeEndpoint.exists_declaredCounter`
and `CountingNativeEndpoint.exists_modelCounter` to those interfaces:

1. **Single-machine `2 ^ o(n)` counting and decision:** because `exists_declaredCounter` adapts its
   branching divisor dynamically with the declared variable count (`interpolationScale =o[atTop]
   id`), a *single* native multi-tape machine solves `SharpDeclaredKSAT k`, `SharpKSAT k`, and
   `KSAT k` in time `2 ^ o(n) · poly(L)` for each fixed clause width `k`.
2. **Vanishing exponents and refuted hypotheses:** `sharpSatExponent k = 0`, `rpSatExponent k = 0`,
   `rSatExponent k = 0`, and `gapSatExponent` / `rGapSatExponent` vanish on every
   perfect-completeness specification `GapKSATSpec.perfect k s`, yielding `¬SharpETH`,
   `¬SharpSETH`, `¬SingleETH`, `¬SingleSharpETH`, `¬rETH`, `¬rSETH`, `¬GapETH`, and `¬rGapETH`.

## Main definitions

* `Cslib.Complexity.SharpDeclaredKSAT`: guarded fixed-width counting on the canonical
  `DeclaredCNF` instances encoded by `encDeclaredCNF`.

## Main results

* `Cslib.Complexity.computableInSingleSubexpTime_SharpDeclaredKSAT`,
  `Cslib.Complexity.computableInSingleSubexpTime_SharpKSAT`,
  `Cslib.Complexity.computableInSubexpTime_SharpKSAT`,
  `Cslib.Complexity.decidableInSingleSubexpTime_KSAT`: unconditional single-machine and family
  subexponential bounds.
* `Cslib.Complexity.sharpSatExponent_eq_zero`, `Cslib.Complexity.rpSatExponent_eq_zero`,
  `Cslib.Complexity.rSatExponent_eq_zero`, `Cslib.Complexity.gapSatExponent_perfect_eq_zero`,
  `Cslib.Complexity.rGapSatExponent_perfect_eq_zero`: vanishing fixed-width exponents.
* `Cslib.Complexity.not_SharpETH`, `Cslib.Complexity.not_SharpSETH`,
  `Cslib.Complexity.not_SingleETH`, `Cslib.Complexity.not_SingleSharpETH`,
  `Cslib.Complexity.not_rETH`, `Cslib.Complexity.not_rSETH`, `Cslib.Complexity.not_GapETH`,
  `Cslib.Complexity.not_rGapETH`: unconditional hypothesis consequences.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Sections 3–6 and
  Appendices A–B, through the imported counting interfaces.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM Filter Asymptotics

/-! ### 1. Structured declared-variable counting and single-machine `2 ^ o(n)` bounds -/

/-- Guarded model count of `x.formula` on `Finset.range x.numVars` when `x.formula` has clause
width `≤ k` and all variables `< x.numVars`, and `0` otherwise. -/
@[expose] def SharpDeclaredKSAT (k : ℕ) (x : DeclaredCNF) : ℕ :=
  if CNF.validDeclaredInput k x.numVars x.formula then
    x.modelCount
  else 0

/-- On valid declared inputs, `SharpDeclaredKSAT k x` scales `x.formula.modelCount` by the
`2 ^ (x.numVars - x.formula.numVars)` assignments to unused declared variables. -/
theorem SharpDeclaredKSAT_of_valid {k : ℕ} {x : DeclaredCNF}
    (hw : ∀ c ∈ x.formula, c.length ≤ k) (hv : ∀ v ∈ x.formula.vars, v < x.numVars) :
    SharpDeclaredKSAT k x = x.formula.modelCount * 2 ^ (x.numVars - x.formula.numVars) := by
  have hsub : x.formula.vars.toFinset ⊆ Finset.range x.numVars := fun v hmem =>
    Finset.mem_range.mpr (hv v (List.mem_toFinset.mp hmem))
  have hval : CNF.validDeclaredInput k x.numVars x.formula = true :=
    CNF.validDeclaredInput_eq_true_iff.mpr ⟨hw, hsub⟩
  simp only [SharpDeclaredKSAT, hval, ↓reduceIte, DeclaredCNF.modelCount,
    CNF.modelCountOn_eq_mul_modelCount x.formula _ hsub, Finset.card_range, Nat.mul_comm]

/-- On invalid declared inputs (`CNF.validDeclaredInput = false`), `SharpDeclaredKSAT k x = 0`. -/
theorem SharpDeclaredKSAT_of_not_valid {k : ℕ} {x : DeclaredCNF}
    (h : CNF.validDeclaredInput k x.numVars x.formula = false) :
    SharpDeclaredKSAT k x = 0 := by
  simp only [SharpDeclaredKSAT, h, Bool.false_eq_true, ↓reduceIte]

/-- **Unconditional single-machine declared model counting.** For each fixed width `k`, one native
multi-tape machine computes `SharpDeclaredKSAT k` in time `2 ^ o(numVars) · poly(L)`. -/
theorem computableInSingleSubexpTime_SharpDeclaredKSAT (k : ℕ) :
    ComputableInSingleSubexpTime (SharpDeclaredKSAT k) encDeclaredCNF encNat
      DeclaredCNF.numVars := by
  open SubexponentialSAT in
  obtain ⟨count, T, S, A, c, e, _, _, hcountO, hspec, hT, -⟩ :=
    CountingNativeEndpoint.exists_declaredCounter k
  have htoPair : ComputableInPolyTime (fun x : DeclaredCNF => (x.numVars, x.formula))
      encDeclaredCNF (encPair encUnary encCNF) :=
    encDeclaredCNF_fields_deg.computableInPolyTime
  obtain ⟨dg, _, hdg⟩ := htoPair.exists_degree
  obtain ⟨p, q, hp⟩ := htoPair.polyBounded_length.exists_le
  have hcompO := (hcountO.comp hdg.inO).of_enc_eq (g := SharpDeclaredKSAT k) fun x =>
    congrArg encNat (hspec (x.numVars, x.formula)).symm
  let s (N : ℕ) : ℝ := (A : ℝ) * interpolationScale N
  have hs_nn : ∀ N, 0 ≤ s N := fun N =>
    mul_nonneg (Nat.cast_nonneg A) (interpolationScale_nonneg N)
  have hs_o : s =o[atTop] fun N : ℕ => (N : ℝ) :=
    isLittleO_interpolationScale.const_mul_left (A : ℝ)
  refine ⟨s, dg + q * e, hs_nn, hs_o,
    (ComputableInTimeO.of_computableInO hcompO fun _ => le_rfl).mono
      (1 + c * (p + 1) ^ e + c) (fun x => ?_) fun _ => by positivity⟩
  set L : ℕ := (encDeclaredCNF x).length
  have hL1 : 1 ≤ L + 1 := Nat.le_add_left 1 L
  have hLR1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by exact_mod_cast hL1
  have hX1 : (1 : ℝ) ≤ 2 ^ s x.numVars := Real.one_le_rpow (by norm_num) (hs_nn _)
  have hpow : ((encPair encUnary encCNF (x.numVars, x.formula)).length + 1) ^ e ≤
      (p + 1) ^ e * (L + 1) ^ (q * e) :=
    Nat.add_one_pow_le_of_le_mul_pow hL1 (hp x) e
  have hqe : ((L : ℝ) + 1) ^ (q * e) ≤ ((L : ℝ) + 1) ^ (dg + q * e) :=
    pow_le_pow_right₀ hLR1 (Nat.le_add_left _ _)
  have hdg_le : ((L : ℝ) + 1) ^ dg ≤ 2 ^ s x.numVars * ((L : ℝ) + 1) ^ (dg + q * e) :=
    (pow_le_pow_right₀ hLR1 (Nat.le_add_right _ _)).trans
      (le_mul_of_one_le_left (by positivity) hX1)
  have hpowR : (((encPair encUnary encCNF (x.numVars, x.formula)).length : ℝ) + 1) ^ e ≤
      ((p + 1) ^ e : ℕ) * ((L : ℝ) + 1) ^ (dg + q * e) := by
    have h1 : (((encPair encUnary encCNF (x.numVars, x.formula)).length : ℝ) + 1) ^ e ≤
        ((p + 1) ^ e : ℕ) * ((L : ℝ) + 1) ^ (q * e) := by exact_mod_cast hpow
    exact h1.trans (mul_le_mul_of_nonneg_left hqe (Nat.cast_nonneg _))
  have hTR : (T (x.numVars, x.formula) : ℝ) ≤
      ((c * (p + 1) ^ e : ℕ) : ℝ) * (2 ^ s x.numVars * ((L : ℝ) + 1) ^ (dg + q * e)) + c := by
    have h0 := hT (x.numVars, x.formula)
    have hmul : (2 : ℝ) ^ s x.numVars *
        (((encPair encUnary encCNF (x.numVars, x.formula)).length : ℝ) + 1) ^ e ≤
        ((p + 1) ^ e : ℕ) * (2 ^ s x.numVars * ((L : ℝ) + 1) ^ (dg + q * e)) := by
      have hm := mul_le_mul_of_nonneg_left hpowR (by positivity : (0 : ℝ) ≤ 2 ^ s x.numVars)
      linarith [show (2 : ℝ) ^ s x.numVars * (((p + 1) ^ e : ℕ) * ((L : ℝ) + 1) ^ (dg + q * e))
        = ((p + 1) ^ e : ℕ) * (2 ^ s x.numVars * ((L : ℝ) + 1) ^ (dg + q * e)) by ring]
    have hmulc := mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg c)
    push_cast at hmulc ⊢
    dsimp only [s] at *
    linarith
  have hc1 : (c : ℝ) ≤ c * (2 ^ s x.numVars * ((L : ℝ) + 1) ^ (dg + q * e)) :=
    le_mul_of_one_le_right (Nat.cast_nonneg c)
      (one_le_mul_of_one_le_of_one_le hX1 (one_le_pow₀ hLR1))
  have hconst_nn : (0 : ℝ) ≤ (1 + c * (p + 1) ^ e + c : ℕ) := Nat.cast_nonneg _
  change ((((encDeclaredCNF x).length + 1) ^ dg +
    T (x.numVars, x.formula) : ℕ) : ℝ) ≤ _
  push_cast at hTR hconst_nn ⊢
  dsimp only [L] at *
  linarith

/-- **Unconditional single-machine `#k-SAT` model counting.** For each fixed width `k`, a *single*
native multi-tape machine computes `SharpKSAT k` in time `2 ^ o(n) · poly(L)` (`n = φ.numVars`). -/
theorem computableInSingleSubexpTime_SharpKSAT (k : ℕ) :
    ComputableInSingleSubexpTime (SharpKSAT k) encCNF encNat CNF.numVars := by
  open SubexponentialSAT in
  obtain ⟨count, A, e, _, hspec, hcountO⟩ := CountingNativeEndpoint.exists_modelCounter k
  let s (n : ℕ) : ℝ := (A : ℝ) * interpolationScale n
  have hs_nn : ∀ n, 0 ≤ s n := fun n =>
    mul_nonneg (Nat.cast_nonneg A) (interpolationScale_nonneg n)
  have hs_o : s =o[atTop] fun n : ℕ => (n : ℝ) :=
    isLittleO_interpolationScale.const_mul_left (A : ℝ)
  have hraw : ComputableInSingleSubexpTime count encCNF encNat CNF.numVars := by
    refine ⟨s, e, hs_nn, hs_o,
      (ComputableInTimeO.of_computableInO hcountO fun _ => le_rfl).mono 2
        (fun φ => ?_) fun _ => by positivity⟩
    set X : ℝ := (2 : ℝ) ^ s φ.numVars
    have hX1 : 1 ≤ X := Real.one_le_rpow (by norm_num) (hs_nn _)
    have hceil : (⌈X⌉₊ : ℝ) ≤ 2 * X := by
      have hlt := (Nat.ceil_lt_add_one (by positivity : 0 ≤ X)).le
      linarith
    have hmul := mul_le_mul_of_nonneg_right hceil
      (by positivity : (0 : ℝ) ≤ (((encCNF φ).length : ℝ) + 1) ^ e)
    push_cast
    dsimp only [X, s] at hmul ⊢
    linarith
  have hguarded := hraw.ite_polyTime (computableInPolyTime_all_length_le k)
    (ComputableInPolyTime.const 0)
  have heq : (fun φ : CNF ℕ => if φ.all (fun c => decide (c.length ≤ k)) then count φ else 0) =
      SharpKSAT k := by
    funext φ
    unfold SharpKSAT SharpSAT
    split_ifs with hw
    · simp only [List.all_eq_true, decide_eq_true_eq] at hw
      exact hspec φ hw
    · rfl
  rwa [heq] at hguarded

/-- Every fixed-width `#k-SAT` problem is computable in subexponential time in `numVars`. -/
theorem computableInSubexpTime_SharpKSAT (k : ℕ) :
    ComputableInSubexpTime (SharpKSAT k) encCNF encNat CNF.numVars :=
  (computableInSingleSubexpTime_SharpKSAT k).computableInSubexpTime

/-- **Unconditional single-machine `k`-SAT decision.** For each fixed width `k`, a *single* native
multi-tape machine decides `KSAT k` in time `2 ^ o(n) · poly(L)` (`n = φ.numVars`). -/
theorem decidableInSingleSubexpTime_KSAT (k : ℕ) :
    DecidableInSingleSubexpTime (KSAT k) encCNF CNF.numVars :=
  DecidableInSingleSubexpTime.KSAT_of_SharpKSAT (computableInSingleSubexpTime_SharpKSAT k)

/-! ### 2. Vanishing exponents and refuted exponential-time hypotheses -/

/-- The `#k-SAT` exponent vanishes for every fixed clause width `k`. -/
theorem sharpSatExponent_eq_zero (k : ℕ) : sharpSatExponent k = 0 :=
  sharpSatExponent_eq_zero_iff_computableInSubexpTime.mpr (computableInSubexpTime_SharpKSAT k)

/-- `rpSatExponent k = 0` for every fixed clause width `k`. -/
theorem rpSatExponent_eq_zero (k : ℕ) : rpSatExponent k = 0 :=
  le_antisymm
    ((rpSatExponent_le_satExponent k).trans_eq (CountingNativeEndpoint.satExponent_eq_zero k))
    (rpSatExponent_nonneg k)

/-- `rSatExponent k = 0` for every fixed clause width `k`. -/
theorem rSatExponent_eq_zero (k : ℕ) : rSatExponent k = 0 :=
  le_antisymm
    ((rSatExponent_le_rpSatExponent k).trans_eq (rpSatExponent_eq_zero k))
    (rSatExponent_nonneg k)

/-- Every perfect-completeness `GapKSAT (GapKSATSpec.perfect k s hs0 hs1)` is solvable
deterministically in subexponential time in `φ.numVars`. -/
theorem solvesPromiseInSubexpTime_GapKSAT_perfect (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    SolvesPromiseInSubexpTime (GapKSAT (GapKSATSpec.perfect k s hs0 hs1)) encCNF CNF.numVars :=
  fun δ hδ => .GapKSAT_perfect_of_KSAT hs0 hs1 hδ.le
    (CountingNativeEndpoint.decidableInSubexpTime_KSAT k δ hδ)

/-- Every perfect-completeness `GapKSAT (GapKSATSpec.perfect k s hs0 hs1)` is solvable in
subexponential time under any error profile `E`. -/
theorem solvesWithErrorInSubexpTime_GapKSAT_perfect (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (E : ErrorModel) :
    SolvesWithErrorInSubexpTime (GapKSAT (GapKSATSpec.perfect k s hs0 hs1)) encCNF E
      CNF.numVars :=
  fun δ hδ =>
    (solvesPromiseInSubexpTime_GapKSAT_perfect k hs0 hs1 δ hδ).solvesWithErrorInExpTime hδ.le E

/-- Every perfect-completeness `GapKSAT` specification has `gapSatExponent = 0`. -/
theorem gapSatExponent_perfect_eq_zero (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    gapSatExponent (GapKSATSpec.perfect k s hs0 hs1) = 0 :=
  le_antisymm
    ((gapSatExponent_perfect_le_satExponent k hs0 hs1).trans
      (le_of_eq (CountingNativeEndpoint.satExponent_eq_zero k)))
    (gapSatExponent_nonneg _)

/-- Every perfect-completeness `GapKSAT` specification has `rGapSatExponent = 0`. -/
theorem rGapSatExponent_perfect_eq_zero (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    rGapSatExponent (GapKSATSpec.perfect k s hs0 hs1) = 0 :=
  le_antisymm
    ((rGapSatExponent_le_gapSatExponent _).trans
      (le_of_eq (gapSatExponent_perfect_eq_zero k hs0 hs1)))
    (rGapSatExponent_nonneg _)

/-- The native model counter refutes `#ETH`. -/
theorem not_SharpETH : ¬SharpETH := by
  rw [SharpETH_iff_sharpSatExponent_pos, sharpSatExponent_eq_zero 3]
  exact lt_irrefl 0

/-- The native model counter refutes `#SETH`. -/
theorem not_SharpSETH : ¬SharpSETH := by
  rintro h
  obtain ⟨k, hk⟩ := h (1 / 2) (by norm_num)
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hhalf] at hk
  exact hk (computableInSubexpTime_SharpKSAT k (1 / 2) (by norm_num))

/-- The single-machine native `3`-SAT solver refutes `SingleETH`. -/
theorem not_SingleETH : ¬SingleETH := fun h => h (decidableInSingleSubexpTime_KSAT 3)

/-- The single-machine native `#3-SAT` counter refutes `SingleSharpETH`. -/
theorem not_SingleSharpETH : ¬SingleSharpETH := fun h =>
  h (computableInSingleSubexpTime_SharpKSAT 3)

/-- The native `3`-SAT solver refutes `rETH`. -/
theorem not_rETH : ¬rETH := fun h => CountingNativeEndpoint.not_ETH h.eth

/-- The native `k`-SAT solvers refute `rSETH`. -/
theorem not_rSETH : ¬rSETH := fun h => CountingNativeEndpoint.not_SETH h.seth

/-- **`GapETH` is false** for native multi-tape Turing machines on `encCNF`. -/
theorem not_GapETH : ¬GapETH := fun h => CountingNativeEndpoint.not_ETH h.eth

/-- **`rGapETH` is false** for native multi-tape Turing machines on `encCNF`. -/
theorem not_rGapETH : ¬rGapETH := fun h => not_GapETH h.gapETH

end Cslib.Complexity
