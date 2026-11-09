/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.IntThreshold
public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.SmallWeights
import CslibFrontier.Computability.Circuit.Simulation
import CslibFrontier.Computability.Circuit.SimulationDepth
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log
import Mathlib.Data.Nat.Size

/-!
# `TCⁱ ⊆ NCⁱ⁺¹`

A majority gate of a `TC` circuit may read a wire many times, so after reading each wire once it
is a threshold gate whose weights are the multiplicities, which may be exponentially large in the
size of the circuit. By Muroga's theorem (`Cslib.SmallWeights.exists_small_threshold`) the same
function is a strict threshold function of its distinct wires with integer weights and bias of
absolute value at most `(N + 1) · (N + 1)!` for `N` distinct wires [Muroga][Muroga1971]; their
binary numerals have `O(N log N)` bits. Conjunctions, disjunctions and negations are threshold
gates with weights `±1`. Every gate of a `TC` circuit therefore becomes an integer threshold gate on
its distinct wires (`Cslib.Circuits.Boolean.Unbounded.thresholdLine`), of arity at most the number
of inputs and gates, and without deepening the circuit.

An integer threshold gate has a De Morgan circuit of logarithmic depth
(`Cslib.Circuits.Boolean.IntThreshold.Op.deMorganCircuit`), so replacing every gate gives a De
Morgan circuit of polynomial size and depth `O(d log (n + s))`
(`Cslib.Circuits.Boolean.Unbounded.exists_deMorgan_simulation_tc`): **TCⁱ ⊆ NCⁱ⁺¹**
(`Cslib.Circuits.Boolean.TC_subset_NC_succ`) [Vollmer, Chapter 4][Vollmer1999].

## Main definitions

* `Cslib.Circuits.Boolean.IntThreshold.ofExtOp`: the integer threshold gate on the distinct wires
  of a `TC` gate.
* `Cslib.Circuits.Boolean.Unbounded.thresholdLine`: a `TC` line as an integer threshold line.

## Main results

* `Cslib.Circuits.Boolean.IntThreshold.interpretation_ofExtOp`: the integer threshold gate
  computes the `TC` gate.
* `Cslib.Circuits.Boolean.IntThreshold.width_ofExtOp_le`: its word width is polynomial in its
  arity.
* `Cslib.Circuits.Boolean.Unbounded.exists_deMorgan_simulation_tc`: De Morgan circuits simulate
  `TC` circuits.
* `Cslib.Circuits.Boolean.TC_subset_NC_succ`, `Cslib.Circuits.Boolean.TC0_subset_NC_one`.

## References

* [S. Muroga, *Threshold Logic and Its Applications*][Muroga1971]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

namespace IntThreshold

open Finset

variable {α : Type*} [DecidableEq α]

/-- The distinct wires of a gate, in order of first appearance. -/
abbrev distinct {m : ℕ} (w : Fin m → α) : List α := (List.ofFn w).dedup

/-- Small integer weights and bias for the majority of `m` wires, read on their distinct
wires with the multiplicities as weights. -/
noncomputable def majorityWeights {m : ℕ} (w : Fin m → α) :
    (Fin (distinct w).length → ℤ) × ℤ :=
  have h := SmallWeights.exists_small_threshold
    (fun j : Fin (distinct w).length => (List.ofFn w).count ((distinct w).get j)) ((m + 1) / 2)
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

theorem majorityWeights_spec {m : ℕ} (w : Fin m → α) :
    (∀ i, |(majorityWeights w).1 i| ≤ SmallWeights.weightBound (distinct w).length) ∧
      |(majorityWeights w).2| ≤ SmallWeights.weightBound (distinct w).length ∧
      ∀ x : Fin (distinct w).length → Bool,
        ((m + 1) / 2 ≤ ∑ j, (List.ofFn w).count ((distinct w).get j) * (x j).toNat ↔
          (majorityWeights w).2 < ∑ j, (majorityWeights w).1 j * (x j).toNat) :=
  Classical.choose_spec (Classical.choose_spec (SmallWeights.exists_small_threshold
    (fun j : Fin (distinct w).length => (List.ofFn w).count ((distinct w).get j)) ((m + 1) / 2)))

/-- The weights of the integer threshold gate equivalent to a `TC` gate on its distinct wires. -/
noncomputable def weightsOf :
    (op : Unbounded.ExtOp) → (w : Fin op.arity → α) → Fin (distinct w).length → ℤ
  | .ac .not, _ => fun _ => -1
  | .ac (.and _), _ => fun _ => 1
  | .ac (.or _), _ => fun _ => 1
  | .gate _, w => (majorityWeights w).1

/-- The bias of the integer threshold gate equivalent to a `TC` gate on its distinct wires. -/
noncomputable def biasOf : (op : Unbounded.ExtOp) → (w : Fin op.arity → α) → ℤ
  | .ac .not, _ => -1
  | .ac (.and _), w => (distinct w).length - 1
  | .ac (.or _), _ => 0
  | .gate _, w => (majorityWeights w).2

/-- The integer threshold gate on the distinct wires of a `TC` gate. -/
noncomputable def ofExtOp (op : Unbounded.ExtOp) (w : Fin op.arity → α) : Op :=
  ⟨(distinct w).length, weightsOf op w, biasOf op w⟩

/-- A sum over the distinct wires of a gate is a sum over its set of wires. -/
theorem sum_distinct {m : ℕ} (w : Fin m → α) {M : Type*} [AddCommMonoid M] (f : α → M) :
    ∑ j : Fin (distinct w).length, f ((distinct w).get j) = ∑ a ∈ (List.ofFn w).toFinset, f a := by
  rw [← List.sum_ofFn, List.ofFn_comp', List.ofFn_get, ← List.sum_toFinset _ (List.nodup_dedup _),
    List.toFinset_dedup]

theorem sum_toNat_distinct {m : ℕ} (w : Fin m → α) (v : α → Bool) :
    ∑ j : Fin (distinct w).length, ((v ((distinct w).get j)).toNat : ℤ) =
      (((List.ofFn w).toFinset.filter fun a => v a = true).card : ℤ) := by
  rw [sum_distinct w (fun a => ((v a).toNat : ℤ)), Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl fun a _ => by cases v a <;> rfl

theorem card_toFinset_ofFn {m : ℕ} (w : Fin m → α) :
    (List.ofFn w).toFinset.card = (distinct w).length := by
  rw [← List.toFinset_dedup, List.toFinset_card_of_nodup (List.nodup_dedup _)]

theorem mem_toFinset_ofFn {m : ℕ} (w : Fin m → α) (a : α) :
    a ∈ (List.ofFn w).toFinset ↔ ∃ j, w j = a := by
  simp [List.mem_ofFn]

theorem interpretation_ofExtOp_eq (op : Unbounded.ExtOp) (w : Fin op.arity → α) (v : α → Bool) :
    interpretation (ofExtOp op w) (v ∘ (distinct w).get) = decide (biasOf op w <
      ∑ j : Fin (distinct w).length, weightsOf op w j * ((v ((distinct w).get j)).toNat : ℤ)) :=
  rfl

/-- **The integer threshold gate on the distinct wires computes the `TC` gate.** -/
theorem interpretation_ofExtOp (op : Unbounded.ExtOp) (w : Fin op.arity → α) (v : α → Bool) :
    interpretation (ofExtOp op w) (v ∘ (distinct w).get) =
      Unbounded.extInterpretation majority op (v ∘ w) := by
  rw [interpretation_ofExtOp_eq]
  match op, w with
  | .ac .not, w =>
    have hT : (List.ofFn w).toFinset = {w 0} := by
      ext a
      simp
    simp only [weightsOf, biasOf, Function.comp_apply, neg_mul,
      one_mul, Finset.sum_neg_distrib, Unbounded.extInterpretation_ac,
      Unbounded.interpretation_not]
    rw [sum_toNat_distinct, hT]
    cases h : v (w 0) <;> simp [Finset.filter_singleton, h]
  | .ac (.and k), w =>
    simp only [weightsOf, biasOf, Function.comp_apply, one_mul,
      Unbounded.extInterpretation_ac, Unbounded.interpretation]
    rw [sum_toNat_distinct]
    have hcard := card_toFinset_ofFn w
    refine decide_eq_decide.mpr ⟨fun h j => ?_, fun h => ?_⟩
    · by_contra hj
      have hlt : ((List.ofFn w).toFinset.filter fun a => v a = true).card <
          (List.ofFn w).toFinset.card :=
        Finset.card_lt_card (Finset.filter_ssubset.mpr
          ⟨w j, (mem_toFinset_ofFn w _).mpr ⟨j, rfl⟩, hj⟩)
      omega
    · have : (List.ofFn w).toFinset.filter (fun a => v a = true) = (List.ofFn w).toFinset :=
        Finset.filter_true_of_mem fun a ha => by
          obtain ⟨j, rfl⟩ := (mem_toFinset_ofFn w a).mp ha
          exact h j
      rw [this, hcard]
      omega
  | .ac (.or k), w =>
    simp only [weightsOf, biasOf, Function.comp_apply, one_mul,
      Unbounded.extInterpretation_ac, Unbounded.interpretation]
    rw [sum_toNat_distinct]
    refine decide_eq_decide.mpr ⟨fun h => ?_, fun ⟨j, hj⟩ => ?_⟩
    · have hpos : 0 < ((List.ofFn w).toFinset.filter fun a => v a = true).card := by omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
      obtain ⟨ha, hva⟩ := Finset.mem_filter.mp ha
      obtain ⟨j, rfl⟩ := (mem_toFinset_ofFn w a).mp ha
      exact ⟨j, hva⟩
    · have : 0 < ((List.ofFn w).toFinset.filter fun a => v a = true).card :=
        Finset.card_pos.mpr ⟨w j, Finset.mem_filter.mpr ⟨(mem_toFinset_ofFn w _).mpr ⟨j, rfl⟩, hj⟩⟩
      omega
  | .gate m, w =>
    simp only [weightsOf, biasOf, Function.comp_apply,
      Unbounded.extInterpretation_gate, majority, threshold, BitString.weight_eq_sum_toNat]
    have hsum : ∑ j : Fin m, (v (w j)).toNat =
        ∑ j : Fin (distinct w).length,
          (List.ofFn w).count ((distinct w).get j) * (v ((distinct w).get j)).toNat := by
      rw [sum_distinct w (fun a => (List.ofFn w).count a * (v a).toNat)]
      have := Finset.sum_list_map_count (List.ofFn w) fun a => (v a).toNat
      simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, smul_eq_mul] at this
      exact this
    rw [hsum]
    exact (decide_eq_decide.mpr ((majorityWeights_spec w).2.2 (v ∘ (distinct w).get))).symm

/-- The weight bound is at least the number of inputs plus one. -/
theorem le_weightBound (k : ℕ) : k + 1 ≤ SmallWeights.weightBound k :=
  Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)

theorem weightBound_mono {k K : ℕ} (h : k ≤ K) :
    SmallWeights.weightBound k ≤ SmallWeights.weightBound K :=
  Nat.mul_le_mul (by omega) (Nat.factorial_le (by omega))

/-- The weights and bias of the gate on the distinct wires are bounded by the weight bound of its
arity. -/
theorem bounded_ofExtOp (op : Unbounded.ExtOp) (w : Fin op.arity → α) :
    (∀ i, |(ofExtOp op w).weight i| ≤ SmallWeights.weightBound (ofExtOp op w).arity) ∧
      |(ofExtOp op w).bias| ≤ SmallWeights.weightBound (ofExtOp op w).arity := by
  have h1 := le_weightBound (distinct w).length
  match op, w with
  | .ac .not, w => exact ⟨fun _ => by simp [ofExtOp, weightsOf]; omega,
      by simp [ofExtOp, biasOf]; omega⟩
  | .ac (.and _), w => exact ⟨fun _ => by simp [ofExtOp, weightsOf]; omega,
      by simp only [ofExtOp, biasOf]; rw [abs_le]; constructor <;> omega⟩
  | .ac (.or _), w => exact ⟨fun _ => by simp [ofExtOp, weightsOf]; omega,
      by simp [ofExtOp, biasOf]⟩
  | .gate _, w => exact ⟨(majorityWeights_spec w).1, (majorityWeights_spec w).2.1⟩

/-- **A gate of bounded arity has bounded width**: `width ≤ (K + 2) ^ 2` for arity at most `K`. -/
theorem width_ofExtOp_le (op : Unbounded.ExtOp) (w : Fin op.arity → α) {K : ℕ}
    (hK : (ofExtOp op w).arity ≤ K) : (ofExtOp op w).width ≤ (K + 2) ^ 2 := by
  obtain ⟨hw, hb⟩ := bounded_ofExtOp op w
  have hB := weightBound_mono hK
  refine ((ofExtOp op w).width_le (B := SmallWeights.weightBound K)
    (fun i => (hw i).trans (by exact_mod_cast hB)) (hb.trans (by exact_mod_cast hB))).trans ?_
  rw [Nat.size_le]
  -- `(2 K + 2) ((K + 1) (K + 1)! + 1) < 2 ^ ((K + 2) ^ 2)`
  have hfact : (K + 1).factorial ≤ (K + 1) ^ (K + 1) := Nat.factorial_le_pow _
  have hpow : K + 1 < 2 ^ (K + 1) := Nat.lt_two_pow_self
  have h1 : (K + 1) ^ (K + 1) ≤ 2 ^ ((K + 1) * (K + 1)) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hpow.le _
  have h2 : SmallWeights.weightBound K + 1 ≤ 2 ^ (K + 1 + (K + 1) * (K + 1)) := by
    have : (K + 1) * (K + 1).factorial < 2 ^ (K + 1) * 2 ^ ((K + 1) * (K + 1)) :=
      Nat.mul_lt_mul_of_lt_of_le hpow (hfact.trans h1) (by positivity)
    rw [pow_add]
    simp only [SmallWeights.weightBound]
    omega
  have h4 : 2 * K + 2 ≤ 2 ^ (K + 1) := by
    have : K < 2 ^ K := Nat.lt_two_pow_self
    rw [pow_succ]
    omega
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _
    (show 2 * (ofExtOp op w).arity + 2 ≤ 2 * K + 2 by omega)) ?_
  calc (2 * K + 2) * (SmallWeights.weightBound K + 1)
      ≤ 2 ^ (K + 1) * 2 ^ (K + 1 + (K + 1) * (K + 1)) := Nat.mul_le_mul h4 h2
    _ = 2 ^ (K + 1 + (K + 1 + (K + 1) * (K + 1))) := by rw [← pow_add]
    _ < 2 ^ ((K + 2) ^ 2) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)

end IntThreshold

namespace Unbounded

open IntThreshold

variable {n g : ℕ}

/-- **A `TC` gate as an integer threshold gate on its distinct wires.** -/
noncomputable def thresholdLine (line : Line extSignature n g) : Line IntThreshold.signature n g :=
  ⟨ofExtOp line.op line.wires, (distinct line.wires).get⟩

theorem eval_thresholdLine (line : Line extSignature n g) (x : Fin n → Bool)
    (gates : Fin g → Bool) :
    (thresholdLine line).eval IntThreshold.interpretation x gates =
      line.eval (extInterpretation majority) x gates :=
  interpretation_ofExtOp line.op line.wires (Wire.elim x gates)

theorem depth_thresholdLine_le (line : Line extSignature n g) (depths : Wire n g → ℕ) :
    (thresholdLine line).depth depths ≤ line.depth depths := by
  have hpos := line.depth_pos depths
  have hle : ∀ a, depths (line.wires a) ≤ line.depth depths - 1 := fun a => by
    have := line.wireDepth_lt_depth depths a
    omega
  refine ((Line.depth_le_add_one_iff _ depths (d := line.depth depths - 1)).2 fun j => ?_).trans
    (by omega)
  have hmem : (distinct line.wires).get j ∈ List.ofFn line.wires :=
    List.mem_dedup.mp (List.get_mem _ _)
  obtain ⟨a, ha⟩ := List.mem_ofFn.mp hmem
  change depths ((distinct line.wires).get j) ≤ _
  rw [← ha]
  exact hle a

theorem arity_thresholdLine_le (line : Line extSignature n g) :
    (thresholdLine line).op.arity ≤ n + g :=
  (List.nodup_dedup _).length_le_card.trans_eq Wire.card

/-- Every line of a mapped program has the operation of a mapped line. -/
theorem forall_lines_mapLines {σ τ : Signature} (f : ∀ {g : ℕ}, Line σ n g → Line τ n g)
    (P : ℕ → τ.Op → Prop) (hP : ∀ {g : ℕ} (line : Line σ n g), P g (f line).op)
    (hmono : ∀ {g g'} {op}, g ≤ g' → P g op → P g' op)
    (p : Program σ n g) (k : Fin g) : P g ((p.mapLines f).lines k).op := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    induction k using Fin.lastCases with
    | last =>
      rw [Program.mapLines_gate, Program.lines_gate_last, Line.mapWires_op]
      exact hmono (Nat.le_succ _) (hP line)
    | cast k =>
      rw [Program.mapLines_gate, Program.lines_gate_castSucc, Line.mapWires_op]
      exact hmono (Nat.le_succ _) (ih k)

/-- **De Morgan circuits simulate `TC` circuits**: a `TC` circuit with `n` inputs, `s` gates and
depth `d` has an equivalent De Morgan circuit with at most
`s · 70 (K + 1) ((K + 2) ^ 2 + 2) ^ 2` gates and depth at most
`(9 + 2 ⌈log₂ ((K + 2) ^ 2 + 2)⌉ + 12 ⌈log₂ (K + 1)⌉) d`, where `K = n + s`. -/
theorem exists_deMorgan_simulation_tc {m : ℕ} (C : Circuit extSignature n m) :
    ∃ D : Circuit Boolean.signature n m,
      D.eval Boolean.interpretation = C.eval (extInterpretation majority) ∧
      D.size ≤ C.size * (70 * (n + C.size + 1) * ((n + C.size + 2) ^ 2 + 2) ^ 2) ∧
      D.depth ≤ (9 + 2 * Nat.clog 2 ((n + C.size + 2) ^ 2 + 2) +
        12 * Nat.clog 2 (n + C.size + 1)) * C.depth := by
  set K := n + C.size
  let C' := C.mapLines thresholdLine
  refine ⟨C'.simulate fun op => op.deMorganCircuit, ?_, ?_, ?_⟩
  · rw [Circuit.eval_simulate _ _ fun op x => by
      funext o
      rw [Subsingleton.elim o 0]
      exact Op.eval_deMorganCircuit op x]
    exact Circuit.eval_mapLines eval_thresholdLine C
  · -- every line has arity at most `K` and width at most `(K + 2) ^ 2`
    have hline (k : Fin C.size) : ((C'.program.lines k).op).arity ≤ K ∧
        (C'.program.lines k).op.width ≤ (K + 2) ^ 2 := by
      have := forall_lines_mapLines thresholdLine
        (fun g op => op.arity ≤ n + g ∧ op.width ≤ (n + g + 2) ^ 2)
        (fun line => ⟨arity_thresholdLine_le line,
          width_ofExtOp_le _ _ (arity_thresholdLine_le line)⟩)
        (fun hg h => ⟨h.1.trans (by omega), h.2.trans (Nat.pow_le_pow_left (by omega) 2)⟩)
        C.program k
      exact this
    rw [Circuit.size_simulate, Program.cost_eq_sum]
    calc ∑ k, (C'.program.lines k).op.deMorganCircuit.size
        ≤ ∑ _k : Fin C.size, 70 * (K + 1) * ((K + 2) ^ 2 + 2) ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          obtain ⟨h1, h2⟩ := hline k
          refine (Op.size_deMorganCircuit_le _).trans ?_
          gcongr
      _ = C.size * (70 * (K + 1) * ((K + 2) ^ 2 + 2) ^ 2) := by simp
  · have hline (k : Fin C.size) : ((C'.program.lines k).op).arity ≤ K ∧
        (C'.program.lines k).op.width ≤ (K + 2) ^ 2 :=
      forall_lines_mapLines thresholdLine
        (fun g op => op.arity ≤ n + g ∧ op.width ≤ (n + g + 2) ^ 2)
        (fun line => ⟨arity_thresholdLine_le line,
          width_ofExtOp_le _ _ (arity_thresholdLine_le line)⟩)
        (fun hg h => ⟨h.1.trans (by omega), h.2.trans (Nat.pow_le_pow_left (by omega) 2)⟩)
        C.program k
    refine (Circuit.depth_simulate_le _ _).trans
      ((Circuit.depthWith_le_mul_depth _ fun k => ?_).trans
        (Nat.mul_le_mul_left _ (Circuit.depth_mapLines_le depth_thresholdLine_le C)))
    obtain ⟨h1, h2⟩ := hline k
    refine (Op.depth_deMorganCircuit_le _).trans ?_
    have := Nat.clog_mono_right 2 (show (C'.program.lines k).op.width + 2 ≤ (K + 2) ^ 2 + 2 by
      omega)
    have := Nat.clog_mono_right 2 (show (C'.program.lines k).op.arity + 1 ≤ K + 1 by omega)
    omega

end Unbounded

/-- **TCⁱ ⊆ NCⁱ⁺¹** [Vollmer, Chapter 4][Vollmer1999]: a polynomial-size circuit of depth
`O((log n) ^ i)` with majority gates becomes, after reading each gate's distinct wires with
small integer weights [Muroga][Muroga1971], a polynomial-size De Morgan circuit of depth
`O((log n) ^ (i + 1))`. -/
theorem TC_subset_NC_succ (i : ℕ) : TC i ⊆ NC (i + 1) := by
  rintro L ⟨c, s, hs, hC⟩
  have hK : PolynomiallyBounded fun n => (n + s n + 2) ^ 2 + 2 + (n + s n + 1) := by fun_prop
  obtain ⟨e, he⟩ := PolynomiallyBounded.exists_clog_le_mul_log hK
  refine ⟨c * (14 * e + 9), fun n => s n * (70 * (n + s n + 1) * ((n + s n + 2) ^ 2 + 2) ^ 2),
    by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  obtain ⟨D, hDe, hDs, hDd⟩ := Unbounded.exists_deMorgan_simulation_tc C
  refine ⟨D, fun x => (congrFun hDe x).trans (hCc x), ?_, ?_⟩
  · have h1 : Nat.clog 2 ((n + C.size + 2) ^ 2 + 2) ≤ e * (Nat.log 2 n + 1) :=
      (Nat.clog_mono_right 2 (Nat.add_le_add_right (Nat.pow_le_pow_left (by omega) 2) 2)).trans
        ((Nat.clog_mono_right 2 (Nat.le_add_right _ _)).trans (he n))
    have h2 : Nat.clog 2 (n + C.size + 1) ≤ e * (Nat.log 2 n + 1) :=
      (Nat.clog_mono_right 2 (show n + C.size + 1 ≤ (n + s n + 2) ^ 2 + 2 + (n + s n + 1) by
        omega)).trans (he n)
    calc D.depth ≤ (9 + 2 * Nat.clog 2 ((n + C.size + 2) ^ 2 + 2) +
          12 * Nat.clog 2 (n + C.size + 1)) * C.depth := hDd
      _ ≤ ((14 * e + 9) * (Nat.log 2 n + 1)) * (c * (Nat.log 2 n + 1) ^ i) := by
          refine Nat.mul_le_mul ?_ hCd
          nlinarith
      _ = c * (14 * e + 9) * (Nat.log 2 n + 1) ^ (i + 1) := by ring
  · refine hDs.trans ?_
    beta_reduce
    gcongr

/-- **TC⁰ ⊆ NC¹**. -/
theorem TC0_subset_NC_one : TC0 ⊆ NC 1 :=
  TC_zero.symm.subset.trans (TC_subset_NC_succ 0)

end Cslib.Circuits.Boolean
