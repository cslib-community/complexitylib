/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AC0
public import Complexity.Foundations.Data.BitString.Threshold
import Complexity.Foundations.Data.BitString.Parity.Weight
import Complexity.Foundations.Data.Fin.Append
import Mathlib.Data.Fintype.Fin

/-!
# Parity reduces to majority in constant depth

Over a basis containing the unbounded fan-in basis (through a meaning-preserving map `φ`),
padding the input with constants turns a circuit for majority on `2 n + 2` bits into every
threshold function on `n` bits (`thresholdCircuitOfMajority`), two thresholds give "exactly `k`
bits are true" (`exactlyCircuitOfMajority`), and parity is the disjunction of these for odd `k`
(`parityCircuitOfMajority`) [ChandraStockmeyerVishkin1984]. The circuit for parity has depth `4`
more and size polynomially larger than the circuit for majority, so if majority has
polynomial-size constant-depth circuits then so does parity
(`ConstDepth.parity_mem_of_majority_mem`). Over the unbounded fan-in basis itself this contradicts
`Cslib.Circuits.Boolean.parity_notMem_AC0`: **majority is not in AC⁰** [FurstSaxeSipser1984].

## Main definitions

* `Cslib.Circuits.Boolean.padCircuit`: pad an `n`-bit input with `a` copies of `true` and
  `n + 2 - a` copies of `false`.
* `Cslib.Circuits.Boolean.parityCircuitOfMajority`: parity from a circuit for majority.

## Main results

* `Cslib.Circuits.Boolean.ConstDepth.parity_mem_of_majority_mem`: over a basis containing the
  unbounded fan-in basis, parity has polynomial-size constant-depth circuits if majority does.
* `Cslib.Circuits.Boolean.majority_notMem_AC0`: majority is not in AC⁰.

## References

* [A. K. Chandra, L. Stockmeyer, U. Vishkin, *Constant depth reducibility*]
  [ChandraStockmeyerVishkin1984]
* [M. Furst, J. B. Saxe, M. Sipser, *Parity, circuits, and the polynomial-time
  hierarchy*][FurstSaxeSipser1984]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset Unbounded

variable {n : ℕ} {σ : Signature} (φ : Unbounded.signature.Hom σ) {I : Interpretation σ Bool}

/-- The inputs followed by `a` copies of `true` and then copies of `false`, `n + 2` constants in
all, read from two constant gates. -/
def padCircuit (n a : ℕ) : Circuit σ n (n + (n + 2)) :=
  (Circuit.id σ n).append ((Circuit.wiring σ fun j : Fin (n + 2) => if j.val < a then 0 else 1).comp
    ((constCircuit φ true).append (constCircuit φ false)))

/-- The threshold function `Th^n_k` for `k ≤ n + 1`, from a circuit `M` for majority on
`n + (n + 2)` bits. -/
def thresholdCircuitOfMajority (M : Circuit σ (n + (n + 2)) 1) (k : ℕ) : Circuit σ n 1 :=
  M.comp (padCircuit φ n (n + 1 - k))

/-- Whether exactly `k` of the bits are true, from a circuit for majority. -/
def exactlyCircuitOfMajority (M : Circuit σ (n + (n + 2)) 1) (k : ℕ) : Circuit σ n 1 :=
  binCircuit φ (.and 2) rfl (thresholdCircuitOfMajority φ M k)
    (notCircuit φ (thresholdCircuitOfMajority φ M (k + 1)))

/-- **Parity from majority**: the disjunction, over odd `k ≤ n`, of "exactly `k` bits are true". -/
def parityCircuitOfMajority (M : Circuit σ (n + (n + 2)) 1) : Circuit σ n 1 :=
  ((Circuit.oneGate (Unbounded.Op.or (n + 1) : Unbounded.signature.Op) id).mapOp φ).comp
    (Circuit.pi fun k : Fin (n + 1) =>
      if k.val % 2 = 1 then exactlyCircuitOfMajority φ M k else constCircuit φ false)

variable {φ} {M : Circuit σ (n + (n + 2)) 1}

/-- Padding costs two gates, one for each constant. -/
@[simp] theorem size_padCircuit (a : ℕ) : (padCircuit φ n a).size = 2 := by
  simp [padCircuit]

/-- Padding has depth at most one. -/
theorem depth_padCircuit_le (a : ℕ) : (padCircuit φ n a).depth ≤ 1 :=
  (Circuit.depth_append_le _ _).trans (max_le (by simp) ((Circuit.depth_comp_le _ _).trans (by
    simpa using (Circuit.depth_append_le _ _).trans
      (max_le (depth_constCircuit_le true) (depth_constCircuit_le false)))))

/-- A threshold costs the padding and the majority circuit. -/
theorem size_thresholdCircuitOfMajority (k : ℕ) :
    (thresholdCircuitOfMajority φ M k).size = 2 + M.size := by
  rw [thresholdCircuitOfMajority, Circuit.size_comp, size_padCircuit]

/-- A threshold is one deeper than the majority circuit. -/
theorem depth_thresholdCircuitOfMajority_le (k : ℕ) :
    (thresholdCircuitOfMajority φ M k).depth ≤ M.depth + 1 :=
  (Circuit.depth_comp_le _ _).trans (Nat.add_le_add_left (depth_padCircuit_le _) _)

/-- "Exactly `k`" costs two thresholds and two gates. -/
theorem size_exactlyCircuitOfMajority (k : ℕ) :
    (exactlyCircuitOfMajority φ M k).size = 2 * (2 + M.size) + 2 := by
  rw [exactlyCircuitOfMajority, size_binCircuit, size_notCircuit,
    size_thresholdCircuitOfMajority, size_thresholdCircuitOfMajority]
  ring

/-- "Exactly `k`" is three deeper than the majority circuit. -/
theorem depth_exactlyCircuitOfMajority_le (k : ℕ) :
    (exactlyCircuitOfMajority φ M k).depth ≤ M.depth + 3 :=
  (depth_binCircuit_le _ _ _ _).trans (by
    have := depth_thresholdCircuitOfMajority_le (φ := φ) (M := M) k
    have := (depth_notCircuit_le (φ := φ) _).trans
      (Nat.add_le_add_right (depth_thresholdCircuitOfMajority_le (φ := φ) (M := M) (k + 1)) 1)
    omega)

/-- Parity costs `n + 1` circuits for "exactly `k`" and one disjunction. -/
theorem size_parityCircuitOfMajority_le :
    (parityCircuitOfMajority φ M).size ≤ 1 + (n + 1) * (2 * (2 + M.size) + 2) := by
  rw [parityCircuitOfMajority, Circuit.size_comp, Circuit.size_pi, Circuit.size_mapOp,
    Circuit.size_oneGate, add_comm]
  refine Nat.add_le_add_left ((sum_le_card_nsmul univ _ (2 * (2 + M.size) + 2)
    fun k _ => ?_).trans_eq (by rw [card_univ, Fintype.card_fin, smul_eq_mul])) _
  split_ifs
  · exact (size_exactlyCircuitOfMajority _).le
  · rw [size_constCircuit]
    omega

/-- Parity is four deeper than the majority circuit. -/
theorem depth_parityCircuitOfMajority_le : (parityCircuitOfMajority φ M).depth ≤ M.depth + 4 :=
  (Circuit.depth_comp_le _ _).trans (by
    have := Circuit.depth_pi_le (fun k : Fin (n + 1) =>
      if k.val % 2 = 1 then exactlyCircuitOfMajority φ M k else constCircuit φ false)
      (D := M.depth + 3) fun k => by
        split_ifs
        · exact depth_exactlyCircuitOfMajority_le _
        · exact (depth_constCircuit_le _).trans (by omega)
    rw [Circuit.depth_mapOp, Circuit.depth_oneGate]
    omega)

section Eval

variable [φ.Preserves Unbounded.interpretation I]
  (hM : M.Computes I (single (majority (n + (n + 2)))))
include hM

omit hM in
/-- Evaluating `padCircuit φ n a` appends `a` copies of `true` followed by `n + 2 - a` copies of
`false` to the input `x`. -/
theorem eval_padCircuit (a : ℕ) (x : BitString n) :
    (padCircuit φ n a).eval I x = Fin.append x fun j => decide (j.val < a) := by
  simp only [padCircuit, Circuit.eval_append, Circuit.eval_comp, Circuit.eval_wiring,
    Function.comp_id]
  congr 1
  funext j
  rw [Function.comp_apply]
  split_ifs with h
  · exact (eval_constCircuit true x 0).trans (decide_eq_true h).symm
  · exact (eval_constCircuit false x 0).trans (decide_eq_false h).symm

omit hM in
/-- The threshold circuit computes the threshold function. -/
theorem eval_thresholdCircuitOfMajority
    (hM : M.Computes I (single (majority (n + (n + 2))))) {k : ℕ} (hk : k ≤ n + 1)
    (x : BitString n) : (thresholdCircuitOfMajority φ M k).eval I x 0 = threshold n k x := by
  rw [thresholdCircuitOfMajority, Circuit.eval_comp, hM, eval_padCircuit]
  simp only [single, majority, threshold_apply]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  simp only [BitString.weight, Fin.card_filter_append (· = true), decide_eq_true_eq,
    Fin.card_filter_val_lt]
  rw [show (n + (n + 2) + 1) / 2 = n + 1 by omega]
  omega

/-- The circuit for "exactly `k`" decides whether exactly `k` bits are true. -/
theorem eval_exactlyCircuitOfMajority {k : ℕ} (hk : k ≤ n) (x : BitString n) :
    (exactlyCircuitOfMajority φ M k).eval I x 0 = decide (BitString.weight x = k) := by
  rw [exactlyCircuitOfMajority, eval_binCircuit_and, eval_notCircuit,
    eval_thresholdCircuitOfMajority hM (by omega), eval_thresholdCircuitOfMajority hM (by omega)]
  simp only [threshold_apply]
  by_cases h : BitString.weight x = k
  · simp [h]
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · simp [h, show ¬ k ≤ BitString.weight x by omega]
    · simp [h, show k ≤ BitString.weight x by omega, show k + 1 ≤ BitString.weight x by omega]

/-- The parity circuit computes parity. -/
theorem computes_parityCircuitOfMajority :
    (parityCircuitOfMajority φ M).Computes I (single (parity n)) := by
  intro x
  funext j
  rw [parityCircuitOfMajority, Circuit.eval_comp,
    Circuit.eval_mapOp (I := Unbounded.interpretation), Circuit.eval_oneGate, Circuit.eval_pi]
  simp only [single, interpretation_or, id]
  set c := BitString.weight x
  have hc : c ≤ n := BitString.weight_le_length x
  rw [parity_eq_decide_weight, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨k, hk⟩
    split_ifs at hk with hodd
    · rw [eval_exactlyCircuitOfMajority hM (by omega)] at hk
      simpa [c, ← of_decide_eq_true hk] using hodd
    · simp at hk
  · intro hodd
    refine ⟨⟨c, by omega⟩, ?_⟩
    simp only [show c % 2 = 1 from by simpa [c] using hodd, ↓reduceIte]
    rw [eval_exactlyCircuitOfMajority hM hc]
    simp [c]

end Eval

/-- **Parity reduces to majority**: over a basis containing the unbounded fan-in basis, parity has
polynomial-size constant-depth circuits if majority does. -/
theorem ConstDepth.parity_mem_of_majority_mem (φ : Unbounded.signature.Hom σ)
    [φ.Preserves Unbounded.interpretation I] (h : Language.ofSlices majority ∈ ConstDepth I) :
    Language.ofSlices parity ∈ ConstDepth I := by
  obtain ⟨d, size, hsize, hC⟩ := ConstDepth.mem_iff.1 h
  refine ConstDepth.mem_iff.2 ⟨d + 4,
    fun n => 1 + (n + 1) * (2 * (2 + size (n + (n + 2))) + 2), by fun_prop, fun n => ?_⟩
  obtain ⟨M, hM, hMd, hMs⟩ := hC (n + (n + 2))
  rw [Language.slice_ofSlices] at hM
  refine ⟨parityCircuitOfMajority φ M, ?_, depth_parityCircuitOfMajority_le.trans (by omega),
    size_parityCircuitOfMajority_le.trans ?_⟩
  · rw [Language.slice_ofSlices]
    exact computes_parityCircuitOfMajority hM
  · beta_reduce
    gcongr

/-- **Majority is not in AC⁰.** -/
theorem majority_notMem_AC0 : Language.ofSlices majority ∉ AC0 :=
  fun h => parity_notMem_AC0 (ConstDepth.parity_mem_of_majority_mem (Signature.Hom.id _) h)

end Cslib.Circuits.Boolean
