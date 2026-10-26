/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.ACC0.Basic
public import Complexity.Computability.Circuit.Boolean.ThresholdNC1
import Complexity.Computability.Circuit.Boolean.PPolyHard
import Complexity.Foundations.Data.Nat.PolynomialBound.Log

/-!
# Simulation of `MOD_q` circuits in `AC¹`, `NC²`, and `P/poly`

Replacing the majority gate in `modCircuitOfMajority` by the logarithmic-depth De Morgan majority
circuit (`majorityDeMorganCircuit`) simulates each operation of the `MOD_q` multiplicity basis over
`Unbounded.signature` in polynomial size and logarithmic depth (`Unbounded.modMultUnboundedCircuit`,
`Unbounded.exists_unbounded_simulation_modGate`) and over the De Morgan fan-in-two basis in
polynomial size (`Unbounded.exists_deMorgan_simulation_modGate`).

This yields the hierarchy inclusions `ACMod q i ⊆ AC (i + 1)` (`ACMod_subset_AC_succ`),
`ACC0 ⊆ AC 1 ⊆ NC 2 ⊆ PPoly` (`ACC0_subset_AC_one`, `ACC0_subset_NC_two`, `ACC0_subset_PPoly`), and
the polynomial-size simulation `SIZEMod_subset_SIZE` of unbounded-depth `MOD_q` circuits by De
Morgan circuits.

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.modMultUnboundedCircuit`: logarithmic-depth unbounded-fan-in
  simulation of a single `MOD_q` multiplicity operation.
* `Cslib.Circuits.Boolean.SIZEMod`: languages decided by `MOD_q` circuits of size at most `s n`.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.exists_unbounded_simulation_modGate`,
  `Cslib.Circuits.Boolean.Unbounded.exists_deMorgan_simulation_modGate`: gate-by-gate simulations of
  `MOD_q` circuits.
* `Cslib.Circuits.Boolean.ACMod_subset_AC_succ`, `Cslib.Circuits.Boolean.ACC0_subset_AC_one`,
  `Cslib.Circuits.Boolean.ACC0_subset_NC_two`, `Cslib.Circuits.Boolean.ACC0_subset_PPoly`.
* `Cslib.Circuits.Boolean.SIZEMod_subset_SIZE`: simulating `SIZEMod q` in De Morgan `SIZE`.

## References

* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Set Finset BitString Unbounded

namespace Unbounded

/-- A circuit over the unbounded fan-in basis simulating each operation of the `MOD_q` multiplicity
basis, using `majorityDeMorganCircuit` mapped into `Unbounded.signature` inside
`modCircuitOfMajority`. -/
def modMultUnboundedCircuit (q : ℕ) :
    (op : MultOp) → Circuit Unbounded.signature (multSignature.Arity op) 1
  | .ac op => Circuit.oneGate (σ := Unbounded.signature) op id
  | .gate _ mult =>
    let K := ∑ i, modMult q (mult i)
    (modCircuitOfMajority (Signature.Hom.id _) q
      ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded)).comp
      (Circuit.wiring Unbounded.signature (expandIndex fun i => modMult q (mult i)))

/-- `modMultUnboundedCircuit q op` computes `op` under `Unbounded.interpretation`. -/
theorem computes_modMultUnboundedCircuit (q : ℕ) (op : MultOp) :
    (modMultUnboundedCircuit q op).Computes Unbounded.interpretation
      (single (multInterpretation (modCount q) op)) := by
  cases op with
  | ac op =>
    intro x
    funext o
    rw [Subsingleton.elim o 0]
    rfl
  | gate N mult =>
    intro x
    set K := ∑ i, modMult q (mult i)
    have hM : ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded).Computes
        Unbounded.interpretation (single (majority (K + (K + 2)))) :=
      (computes_majorityDeMorganCircuit (K + (K + 2))).mapOp
    rw [modMultUnboundedCircuit, Circuit.eval_comp, Circuit.eval_wiring,
      computes_modCircuitOfMajority hM q]
    funext o
    simp only [single, multInterpretation_gate, modGate_eq_modCount, modCount]
    rw [weight_comp_expandIndex, decide_eq_decide]
    exact multWeight_modMult_mod_ne_zero_iff q mult x

/-- Polynomial size bound for `modMultUnboundedCircuit q op`. -/
theorem size_modMultUnboundedCircuit_le (q : ℕ) (op : MultOp) :
    (modMultUnboundedCircuit q op).size ≤
      2100 * (max q 1 * multSignature.Arity op + 1) ^ 3 := by
  cases op with
  | ac op =>
    simp only [modMultUnboundedCircuit, Circuit.size_oneGate]
    have : 1 ≤ (max q 1 * multSignature.Arity (.ac op) + 1) ^ 3 :=
      Nat.one_le_pow _ _ (by omega)
    linarith
  | gate N mult =>
    rw [modMultUnboundedCircuit, Circuit.size_comp, Circuit.size_wiring, zero_add]
    set K := ∑ i : Fin N, modMult q (mult i)
    have hK : K ≤ max q 1 * N := by
      simpa [K, mul_comm] using Finset.sum_le_card_nsmul (univ : Finset (Fin N))
        (fun i => modMult q (mult i)) (max q 1) fun i _ => modMult_le q _
    have hM : (((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded).size) ≤
        65 * (2 * K + 3) ^ 2 := by
      rw [Circuit.size_mapOp, show 2 * K + 3 = K + (K + 2) + 1 by omega]
      exact size_majorityDeMorganCircuit_le_sq (K + (K + 2))
    change (modCircuitOfMajority (Signature.Hom.id _) q
      ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded)).size ≤
      2100 * (max q 1 * N + 1) ^ 3
    have hcube : (K + 1) ^ 3 ≤ (max q 1 * N + 1) ^ 3 :=
      Nat.pow_le_pow_left (Nat.add_le_add_right hK 1) 3
    calc (modCircuitOfMajority (Signature.Hom.id _) q
          ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded)).size
        ≤ 1 + (K + 1) * (2 * (2 +
            ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded).size) + 2) :=
          size_modCircuitOfMajority_le q
      _ ≤ 1 + (K + 1) * (2 * (2 + 65 * (2 * K + 3) ^ 2) + 2) := by gcongr
      _ ≤ 2100 * (K + 1) ^ 3 := by
        have hring : 2100 * (K + 1) ^ 3 =
            1 + (K + 1) * (2 * (2 + 65 * (2 * K + 3) ^ 2) + 2) +
              (1580 * K ^ 3 + 4220 * K ^ 2 + 3564 * K + 923) := by ring
        omega
      _ ≤ 2100 * (max q 1 * N + 1) ^ 3 := Nat.mul_le_mul_left 2100 hcube

/-- Logarithmic depth bound for `modMultUnboundedCircuit q op`. -/
theorem depth_modMultUnboundedCircuit_le (q : ℕ) (op : MultOp) :
    (modMultUnboundedCircuit q op).depth ≤
      6 + 23 * Nat.clog 2 (2 * max q 1 * multSignature.Arity op + 3) := by
  cases op with
  | ac op =>
    simp only [modMultUnboundedCircuit, Circuit.depth_oneGate]
    omega
  | gate N mult =>
    refine (Circuit.depth_comp_le _ _).trans ?_
    rw [Circuit.depth_wiring, add_zero]
    set K := ∑ i : Fin N, modMult q (mult i)
    have hK : K ≤ max q 1 * N := by
      simpa [K, mul_comm] using Finset.sum_le_card_nsmul (univ : Finset (Fin N))
        (fun i => modMult q (mult i)) (max q 1) fun i _ => modMult_le q _
    have h2K : 2 * K ≤ 2 * max q 1 * N := by linarith
    have hM : (((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded).depth) ≤
        2 + 23 * Nat.clog 2 (2 * max q 1 * N + 3) := by
      rw [Circuit.depth_mapOp]
      refine (depth_majorityDeMorganCircuit_le (K + (K + 2))).trans ?_
      have hclog : Nat.clog 2 (K + (K + 2) + 1) ≤ Nat.clog 2 (2 * max q 1 * N + 3) :=
        Nat.clog_mono_right 2 (by omega)
      omega
    have hd := depth_modCircuitOfMajority_le (φ := Signature.Hom.id _)
      (M := (majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded) q
    change (modCircuitOfMajority (Signature.Hom.id _) q
      ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded)).depth ≤
      6 + 23 * Nat.clog 2 (2 * max q 1 * N + 3)
    omega

/-- **Unbounded fan-in circuits simulate `MOD_q` gates in logarithmic depth**: a circuit with
`MOD_q` gates of `n` inputs, `s` gates and depth `d` has an equivalent circuit over the unbounded
fan-in basis of at most `2100 * s * (max q 1 * (n + s) + 1) ^ 3` gates and depth at most
`(6 + 23 * ⌈log₂ (2 * max q 1 * (n + s) + 3)⌉) * d`. -/
theorem exists_unbounded_simulation_modGate {n m : ℕ} (q : ℕ) (C : Circuit extSignature n m) :
    ∃ D : Circuit Unbounded.signature n m,
      D.eval Unbounded.interpretation = C.eval (extInterpretation (modGate q)) ∧
      D.size ≤ C.size * (2100 * (max q 1 * (n + C.size) + 1) ^ 3) ∧
      D.depth ≤ (6 + 23 * Nat.clog 2 (2 * max q 1 * (n + C.size) + 3)) * C.depth := by
  refine ⟨(multCircuit C).simulate (modMultUnboundedCircuit q), ?_, ?_, ?_⟩
  · rw [Circuit.eval_simulate _ _ (computes_modMultUnboundedCircuit q),
      eval_multCircuit (G := modCount q) (modGate_eq_modCount q)]
  · rw [Circuit.size_simulate, Program.cost_eq_sum]
    refine (Finset.sum_le_sum (g := fun _ => 2100 * (max q 1 * (n + C.size) + 1) ^ 3)
      fun k _ => (size_modMultUnboundedCircuit_le q _).trans ?_).trans_eq
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, size_multCircuit])
    have har := arity_lines_multCircuit_le C k
    gcongr
  · refine (Circuit.depth_simulate_le _ _).trans
      (((multCircuit C).depthWith_le_mul_depth fun k =>
        (depth_modMultUnboundedCircuit_le q _).trans ?_).trans
        (Nat.mul_le_mul_left _ (depth_multCircuit_le C)))
    have har := arity_lines_multCircuit_le C k
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_left 23
        (Nat.clog_mono_right 2 (Nat.add_le_add_right (Nat.mul_le_mul_left (2 * max q 1) har) 3))) 6

/-- **De Morgan circuits simulate `MOD_q` circuits in polynomial size**: every circuit over the
`AC⁰[q]` basis of `n` inputs and `s` gates has an equivalent fan-in-two De Morgan circuit of size
at most `(2100 * (max q 1) ^ 3) ^ 2 * (n + s + 1) ^ 8`. -/
theorem exists_deMorgan_simulation_modGate {n m : ℕ} (q : ℕ) (C : Circuit extSignature n m) :
    ∃ D : Circuit Boolean.signature n m,
      D.eval Boolean.interpretation = C.eval (extInterpretation (modGate q)) ∧
      D.size ≤ (2100 * (max q 1) ^ 3) ^ 2 * (n + C.size + 1) ^ 8 := by
  obtain ⟨U, hUe, hUs, -⟩ := exists_unbounded_simulation_modGate q C
  obtain ⟨D, hDe, hDs, -⟩ := exists_deMorgan_simulation U
  refine ⟨D, hDe.trans hUe, hDs.trans ?_⟩
  have hQ : 1 ≤ max q 1 := le_max_right q 1
  have hK : max q 1 * (n + C.size) + 1 ≤ max q 1 * (n + C.size + 1) := by nlinarith
  have hU1 : U.size ≤ 2100 * (max q 1) ^ 3 * (n + C.size + 1) ^ 4 := by
    have h1 : C.size ≤ n + C.size + 1 := by omega
    have h2 : (max q 1 * (n + C.size) + 1) ^ 3 ≤ (max q 1) ^ 3 * (n + C.size + 1) ^ 3 := by
      calc (max q 1 * (n + C.size) + 1) ^ 3
          ≤ (max q 1 * (n + C.size + 1)) ^ 3 := Nat.pow_le_pow_left hK 3
        _ = (max q 1) ^ 3 * (n + C.size + 1) ^ 3 := by ring
    calc U.size ≤ C.size * (2100 * (max q 1 * (n + C.size) + 1) ^ 3) := hUs
      _ ≤ (n + C.size + 1) * (2100 * ((max q 1) ^ 3 * (n + C.size + 1) ^ 3)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul_left 2100 h2)
      _ = 2100 * (max q 1) ^ 3 * (n + C.size + 1) ^ 4 := by ring
  have hnU : n + U.size ≤ 2100 * (max q 1) ^ 3 * (n + C.size + 1) ^ 4 := by
    have hQ3 : 1 ≤ (max q 1) ^ 3 := Nat.one_le_pow 3 _ hQ
    have hpow4 : n + 1 ≤ (n + C.size + 1) ^ 4 := by
      calc n + 1 ≤ (n + C.size + 1) ^ 1 := by simp
        _ ≤ (n + C.size + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : C.size * (2100 * (max q 1 * (n + C.size) + 1) ^ 3) ≤
        2100 * (max q 1) ^ 3 * C.size * (n + C.size + 1) ^ 3 := by
      have h2 : (max q 1 * (n + C.size) + 1) ^ 3 ≤ (max q 1) ^ 3 * (n + C.size + 1) ^ 3 := by
        calc (max q 1 * (n + C.size) + 1) ^ 3
            ≤ (max q 1 * (n + C.size + 1)) ^ 3 := Nat.pow_le_pow_left hK 3
          _ = (max q 1) ^ 3 * (n + C.size + 1) ^ 3 := by ring
      calc C.size * (2100 * (max q 1 * (n + C.size) + 1) ^ 3)
          ≤ C.size * (2100 * ((max q 1) ^ 3 * (n + C.size + 1) ^ 3)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2100 h2)
        _ = 2100 * (max q 1) ^ 3 * C.size * (n + C.size + 1) ^ 3 := by ring
    have h3 : (n + 1) + C.size * (n + C.size + 1) ^ 3 ≤ (n + C.size + 1) ^ 4 := by
      have : (n + 1) * 1 + C.size * (n + C.size + 1) ^ 3 ≤
          (n + 1) * (n + C.size + 1) ^ 3 + C.size * (n + C.size + 1) ^ 3 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left (n + 1) (Nat.one_le_pow 3 _ (by omega))) _
      calc (n + 1) + C.size * (n + C.size + 1) ^ 3
          ≤ (n + 1) * (n + C.size + 1) ^ 3 + C.size * (n + C.size + 1) ^ 3 := by simpa using this
        _ = (n + C.size + 1) ^ 4 := by ring
    nlinarith
  calc U.size * (n + U.size)
      ≤ (2100 * (max q 1) ^ 3 * (n + C.size + 1) ^ 4) *
          (2100 * (max q 1) ^ 3 * (n + C.size + 1) ^ 4) := Nat.mul_le_mul hU1 hnU
    _ = (2100 * (max q 1) ^ 3) ^ 2 * (n + C.size + 1) ^ 8 := by ring

end Unbounded

/-- **`ACⁱ[q] ⊆ ACⁱ⁺¹`**: polynomial-size circuits with `MOD_q` gates of depth `O((log n) ^ i)` are
simulated by polynomial-size circuits over the unbounded fan-in basis of depth
`O((log n) ^ (i + 1))`. -/
theorem ACMod_subset_AC_succ (q i : ℕ) : ACMod q i ⊆ AC (i + 1) := by
  rintro L ⟨c, s, hs, hC⟩
  obtain ⟨e, he⟩ := PolynomiallyBounded.exists_clog_le_mul_log
    (s := fun n => 2 * max q 1 * (n + s n) + 3) (by fun_prop)
  refine ⟨(23 * e + 6) * c, fun n => s n * (2100 * (max q 1 * (n + s n) + 1) ^ 3),
    by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  obtain ⟨D, hDe, hDs, hDd⟩ := Unbounded.exists_unbounded_simulation_modGate q C
  refine ⟨D, fun x => (congrFun hDe x).trans (hCc x), ?_, ?_⟩
  · have hmono := Nat.add_le_add_right
      (Nat.mul_le_mul_left (2 * max q 1) (Nat.add_le_add_left hCs n)) 3
    have hclog : Nat.clog 2 (2 * max q 1 * (n + C.size) + 3) ≤ e * (Nat.log 2 n + 1) :=
      (Nat.clog_mono_right 2 hmono).trans (he n)
    have hlog : 6 + 23 * Nat.clog 2 (2 * max q 1 * (n + C.size) + 3) ≤
        (23 * e + 6) * (Nat.log 2 n + 1) := by nlinarith
    calc D.depth ≤ (6 + 23 * Nat.clog 2 (2 * max q 1 * (n + C.size) + 3)) * C.depth := hDd
      _ ≤ ((23 * e + 6) * (Nat.log 2 n + 1)) * (c * (Nat.log 2 n + 1) ^ i) :=
        Nat.mul_le_mul hlog hCd
      _ = (23 * e + 6) * c * (Nat.log 2 n + 1) ^ (i + 1) := by ring
  · refine hDs.trans ?_
    beta_reduce
    gcongr

/-- **`AC⁰[q] ⊆ AC¹`.** -/
theorem AC0Mod_subset_AC_one (q : ℕ) : AC0Mod q ⊆ AC 1 := by
  rw [← ACMod_zero]
  exact ACMod_subset_AC_succ q 0

/-- **`ACC⁰ ⊆ AC¹`.** -/
theorem ACC0_subset_AC_one : ACC0 ⊆ AC 1 :=
  iUnion₂_subset fun q _ => AC0Mod_subset_AC_one q

/-- **`AC⁰[q] ⊆ NC²`.** -/
theorem AC0Mod_subset_NC_two (q : ℕ) : AC0Mod q ⊆ NC 2 :=
  (AC0Mod_subset_AC_one q).trans (AC_subset_NC_succ 1)

/-- **`ACC⁰ ⊆ NC²`.** -/
theorem ACC0_subset_NC_two : ACC0 ⊆ NC 2 :=
  ACC0_subset_AC_one.trans (AC_subset_NC_succ 1)

/-- **`AC⁰[q] ⊆ P/poly`** for every modulus `q`. -/
theorem AC0Mod_subset_PPoly (q : ℕ) : AC0Mod q ⊆ PPoly :=
  (AC0Mod_subset_AC_one q).trans (AC_subset_PPoly 1)

/-- **`ACC⁰ ⊆ P/poly`.** -/
theorem ACC0_subset_PPoly : ACC0 ⊆ PPoly :=
  ACC0_subset_AC_one.trans (AC_subset_PPoly 1)

/-- **Some language over `Bool` is not in `ACC⁰`** (by Shannon's counting argument and
`ACC0 ⊆ PPoly`). -/
theorem exists_notMem_ACC0 : ∃ L : Language Bool, L ∉ ACC0 := by
  obtain ⟨L, hL⟩ := PPoly.exists_not_mem
  exact ⟨L, fun h => hL (ACC0_subset_PPoly h)⟩

/-! ### Unbounded-depth `MOD_q` circuit size classes (`SIZEMod`) -/

/-- The class of languages over `Bool` decided at every input length `n` by circuits over the
`AC⁰[q]` basis (`Unbounded.extInterpretation (modGate q)`) of size at most `s n` (of arbitrary
depth). -/
def SIZEMod (q : ℕ) (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∀ n, ∃ C : Circuit extSignature n 1,
    C.Computes (extInterpretation (modGate q)) (single (L.slice n)) ∧ C.size ≤ s n}

/-- `SIZEMod q` is monotone in the size bound. -/
theorem SIZEMod_mono (q : ℕ) : Monotone (SIZEMod q) := by
  intro s₁ s₂ hs L hL n
  obtain ⟨C, hCc, hCs⟩ := hL n
  exact ⟨C, hCc, hCs.trans (hs n)⟩

/-- **Simulating `SIZEMod q` in De Morgan `SIZE`**: a circuit with `MOD_q` gates of size at most
`c * (n + 1) ^ k` is simulated by a fan-in-two De Morgan circuit of size at most
`(2100 * (max q 1) ^ 3) ^ 2 * (c + 1) ^ 8 * (n + 1) ^ (8 * (k + 1))`. -/
theorem SIZEMod_subset_SIZE (q c k : ℕ) :
    SIZEMod q (fun n => c * (n + 1) ^ k) ⊆
      SIZE (fun n => (2100 * (max q 1) ^ 3) ^ 2 * (c + 1) ^ 8 * (n + 1) ^ (8 * (k + 1))) := by
  intro L hL n
  obtain ⟨C, hCc, hCs⟩ := hL n
  obtain ⟨D, hDe, hDs⟩ := Unbounded.exists_deMorgan_simulation_modGate q C
  have hDc : D.Computes Boolean.interpretation (single (L.slice n)) :=
    fun x => (congrFun hDe x).trans (hCc x)
  refine (complexity_le_of_computes D hDc).trans (hDs.trans ?_)
  have hn1 : n + 1 ≤ (n + 1) ^ (k + 1) := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (Nat.succ_pos k)
  have hk1 : (n + 1) ^ k ≤ (n + 1) ^ (k + 1) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_succ k)
  have hsum : n + C.size + 1 ≤ (c + 1) * (n + 1) ^ (k + 1) := by
    dsimp only at hCs
    calc n + C.size + 1 ≤ (n + 1) + c * (n + 1) ^ k := by omega
      _ ≤ 1 * (n + 1) ^ (k + 1) + c * (n + 1) ^ (k + 1) := by
        rw [one_mul]
        exact Nat.add_le_add hn1 (Nat.mul_le_mul_left c hk1)
      _ = (c + 1) * (n + 1) ^ (k + 1) := by ring
  calc (2100 * (max q 1) ^ 3) ^ 2 * (n + C.size + 1) ^ 8
      ≤ (2100 * (max q 1) ^ 3) ^ 2 * ((c + 1) * (n + 1) ^ (k + 1)) ^ 8 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 8)
    _ = (2100 * (max q 1) ^ 3) ^ 2 * (c + 1) ^ 8 * (n + 1) ^ (8 * (k + 1)) := by
        rw [mul_pow, ← pow_mul]
        ring

end Cslib.Circuits.Boolean
