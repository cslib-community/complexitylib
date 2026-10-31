/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace.Randomized.ConfigurationReader
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.FairCoin.Table
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Deterministic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Injective
import Complexity.Foundations.LinearAlgebra.Matrix.ClosedSubmatrix

/-!
# Fair-coin matrices on the entire compact configuration box

The matrix is indexed by every bounded compact ID, as enumerated by the initialized native
`coinTable` writer. Invalid IDs have zero rows, and transitions leaving the box are omitted.
Fixed-coin determinism makes every row substochastic, without a reachable-view premise.
For a logarithmic-space run the box contains every reachable view; restriction to that closed
image therefore proves exact finite-time acceptance for the ambient matrix.

This supplies the enumerated base matrix of [OpenAI2026LogSpace, Lemma 2.1]. Clocking and the
terminal reward are treated separately; `Randomized.ClockedTable` supplies the initialized native
clocked matrix payload. Complete instance packaging, paired ports and the recursive estimator
remain separate.

## Main definitions

* `Turing.MultiTapePTM.ConfigurationGraph.compactCoinMatrix`: half the actual compact coin count.
* `Turing.MultiTapePTM.ConfigurationGraph.compactAcceptVec`: the accepting-halt indicator.

## Main results

* `Turing.MultiTapePTM.ConfigurationGraph.compactCoinMatrix_eq_coinTable`: exact native table
  interpretation.
* `Turing.MultiTapePTM.ConfigurationGraph.compactCoinMatrix_mulVec_one_le`: the entire matrix is
  substochastic, including unreachable and invalid IDs.
* `Turing.MultiTapePTM.ConfigurationGraph.compactCoinMatrix_pow_accept`: exact finite-time
  acceptance on the ambient box, from the original logarithmic-space witness.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 2, Lemma 2.1, `model.tex` (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph Matrix

variable {k : ℕ} {State : Type} [Fintype State] (machine : MultiTapePTM k Bool State)
  (R : Type*) [Field R]

/-- The actual fair-coin transition probabilities on every ID in the radix box. Invalid IDs
and overflowing transitions have zero entries; coincident coin successors have weight one. -/
@[expose] noncomputable def compactCoinMatrix (B : ℕ) (w : List Bool) :
    Matrix (Fin (vertexBound (k := k) B)) (Fin (vertexBound (k := k) B)) R :=
  fun u v => (coinCountWithSymbol machine B w.length u v
    w[queryIndex (k := k) B u]? : R) / 2

variable {machine}

/-- The accepting-halt indicator on the entire box, with invalid IDs assigned zero. -/
@[expose] noncomputable def compactAcceptVec (B n : ℕ) :
    Fin (vertexBound (k := k) B) → R :=
  fun u => if bad (k := k) (State := State) B n u then 1 else 0

variable {R}

/-- The two bits written by the initialized native table give this matrix entry exactly. -/
theorem compactCoinMatrix_eq_coinTable (D : ℕ) (w : List Bool)
    (u v : Fin (vertexBound (k := k) (radix D w.length))) :
    compactCoinMatrix machine R (radix D w.length) w u v =
      (((coinTable machine D w).getD
          (2 * (u.val * vertexBound (k := k) (radix D w.length) + v.val)) false).toNat +
        ((coinTable machine D w).getD
          (2 * (u.val * vertexBound (k := k) (radix D w.length) + v.val) + 1)
          false).toNat : ℕ) / 2 := by
  rw [coinTable_count]
  rfl

section Ordered

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- Every ambient entry is nonnegative. -/
theorem compactCoinMatrix_nonneg (B : ℕ) (w : List Bool) :
    ∀ u v, 0 ≤ compactCoinMatrix machine R B w u v := by
  intro u v
  unfold compactCoinMatrix
  positivity

/-- The ambient row sum is at most one. This includes malformed and unreachable sources and
sources whose successor would overflow the radix. -/
theorem compactCoinMatrix_mulVec_one_le (B : ℕ) (w : List Bool) :
    compactCoinMatrix machine R B w *ᵥ 1 ≤ 1 := by
  intro u
  have hfalse := sum_edgeWithSymbol_le_one (machine.withCoin false).toTM B w.length u
    w[queryIndex (k := k) B u]?
  have htrue := sum_edgeWithSymbol_le_one (machine.withCoin true).toTM B w.length u
    w[queryIndex (k := k) B u]?
  have hcount : ∑ v : Fin (vertexBound (k := k) B),
      coinCountWithSymbol machine B w.length u v w[queryIndex (k := k) B u]? ≤ 2 := by
    simp only [coinCountWithSymbol, Finset.sum_add_distrib]
    omega
  have hcast : (∑ v : Fin (vertexBound (k := k) B),
      (coinCountWithSymbol machine B w.length u v w[queryIndex (k := k) B u]? : R)) ≤ 2 := by
    exact_mod_cast hcount
  simpa only [mulVec, dotProduct, compactCoinMatrix, Pi.one_apply, mul_one,
    ← Finset.sum_div] using (div_le_one (by norm_num : (0 : R) < 2)).mpr hcast

/-- The accepting reward is bounded at every ambient ID. -/
theorem compactAcceptVec_mem_Icc (B n : ℕ) :
    compactAcceptVec (k := k) (State := State) R B n ∈ Set.Icc 0 1 := by
  constructor <;> intro u <;> unfold compactAcceptVec <;> split_ifs <;> simp

end Ordered

variable (machine)

/-- The actual initial compact ID at the standard logarithmic-space radix. The space witness
derives the required bound internally; no separately supplied ID or fit premise is needed. -/
@[expose] noncomputable def compactStart (c : ℕ) {w : List Bool}
    (hs : machine.toNTM.RunsInSpace w (c * (Nat.log2 w.length + 1))) :
    Fin (vertexBound (k := k) (radix (radixExponent State c) w.length)) :=
  ⟨startID machine.toNTM (radix (radixExponent State c) w.length), by
    rw [← vertexID_init machine.toNTM _ w]
    exact vertexID_lt (fits_of_runsInSpace c hs .refl)⟩

variable {machine}

/-- The ambient compact matrix has exactly the machine's finite-time acceptance probability
at its actual start. Only the original logarithmic-space witness is assumed; the finite reachable
set, canonical representations, fit bounds and start-ID bound are all derived in the proof. -/
theorem compactCoinMatrix_pow_accept (c : ℕ) {w : List Bool}
    (hs : machine.toNTM.RunsInSpace w (c * (Nat.log2 w.length + 1))) (t : ℕ) :
    let B := radix (radixExponent State c) w.length
    (compactCoinMatrix machine R B w ^ t *ᵥ
      compactAcceptVec (k := k) (State := State) R B w.length) (compactStart machine c hs) =
        (machine.acceptCoins w t : R) / 2 ^ t := by
  classical
  let B := radix (radixExponent State c) w.length
  obtain ⟨V, hreach, hclosedV, _⟩ := machine.exists_finset_reachable hs
  have hinit : machine.toNTM.initView w ∈ V := (hreach _).mpr .refl
  have hr (v : V) := (hreach v).mp v.property
  have hinput (v : V) : v.val.input = w := input_of_reachable (hr v)
  have hfit (v : V) : Fits B (registers v.val) := fits_of_runsInSpace c hs (hr v)
  let e : V ↪ Fin (vertexBound (k := k) B) :=
    ⟨fun v => ⟨vertexID B v.val, vertexID_lt (hfit v)⟩, by
      intro v z hvz
      apply Subtype.ext
      exact vertexID_injective ((hinput v).trans (hinput z).symm)
        (canonical_of_reachable machine (hr v)) (canonical_of_reachable machine (hr z))
        (hfit v) (hfit z) (congrArg Fin.val hvz)⟩
  have hclosed (v : V) (z : Fin (vertexBound (k := k) B)) (hz : z ∉ Set.range e) :
      compactCoinMatrix machine R B w (e v) z = 0 := by
    have hzero (bit : Bool) : edgeWithSymbol (machine.withCoin bit).toTM.toMultiTapeNTM
        B w.length (vertexID B v.val) z w[queryIndex (k := k) B (vertexID B v.val)]? = false := by
      apply Bool.eq_false_iff.mpr
      intro hedge
      have hedge' : Edge (machine.withCoin bit).toTM.toMultiTapeNTM B v.val.input
          (vertexID B v.val) z := by
        simpa only [Edge, hinput v] using hedge
      obtain ⟨next, hstep, _, hid, _⟩ := edge_sound (hfit v) hedge'
      have hnext := (viewStep_withCoin_iff machine bit).mp hstep
      have hn : next ∈ V := (hreach next).mpr
        ((hr v).tail (machine.viewStep_toNTM_iff.mpr ⟨bit, hnext⟩))
      exact hz ⟨⟨next, hn⟩, Fin.ext hid.symm⟩
    change (coinCountWithSymbol machine B w.length (vertexID B v.val) z
      w[queryIndex (k := k) B (vertexID B v.val)]? : R) / 2 = 0
    simp [coinCountWithSymbol, hzero]
  have hmatrix : (compactCoinMatrix machine R B w).submatrix e e =
      (2 : R)⁻¹ • machine.configMatrix R V := by
    ext v z
    change (coinCountWithSymbol machine B w.length (vertexID B v.val) (vertexID B z.val)
      w[queryIndex (k := k) B (vertexID B v.val)]? : R) / 2 =
        (2 : R)⁻¹ * machine.configMatrix R V v z
    rw [coinCountWithSymbol_eq_configMatrix_of_reachable machine c hs
      (fun v hv => (hreach v).mp hv) v z, div_eq_inv_mul]
  have hreward : compactAcceptVec (k := k) (State := State) R B w.length ∘ e =
      FiniteCfg.acceptVec R V := by
    funext v
    have hb := bad_vertexID (hfit v)
    rw [hinput v] at hb
    change (if bad (k := k) (State := State) B w.length (vertexID B v.val)
      then (1 : R) else 0) = FiniteCfg.acceptVec R V v
    simp only [hb, FiniteCfg.acceptVec]
  have he : e ⟨machine.toNTM.initView w, hinit⟩ = compactStart machine c hs := by
    apply Fin.ext
    exact vertexID_init machine.toNTM B w
  have hp := Matrix.submatrix_pow_mulVec_of_closed (compactCoinMatrix machine R B w) e
    hclosed (compactAcceptVec (k := k) (State := State) R B w.length) t
  rw [hmatrix, hreward] at hp
  have hv := congrFun hp ⟨machine.toNTM.initView w, hinit⟩
  rw [Function.comp_apply, he] at hv
  exact hv.symm.trans
    (machine.acceptCoins_div_eq_configMatrix_pow_mulVec R hclosedV hinit t).symm

end Turing.MultiTapePTM.ConfigurationGraph
