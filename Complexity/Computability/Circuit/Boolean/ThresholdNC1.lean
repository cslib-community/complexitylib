/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.CarrySave
public import Complexity.Computability.Circuit.Boolean.Comparison
public import Complexity.Computability.Circuit.Boolean.FanInTwo
public import Complexity.Computability.Circuit.Boolean.Threshold
import Complexity.Computability.Circuit.CompositionDepth
import Complexity.Computability.Circuit.Simulation
import Complexity.Foundations.Data.Nat.PolynomialBound.Log

/-!
# Threshold and majority circuits in `NC¹`

Combining the logarithmic-depth carry-save Hamming weight circuit (`weightCircuit`) with the
comparator (`leCircuit`) yields a fan-in-two De Morgan circuit `thresholdDeMorganCircuit k j`
computing the `k`-bit threshold function `threshold k j` in size `O(k log k)` and depth
`O(log k)` (`computes_thresholdDeMorganCircuit`, `size_thresholdDeMorganCircuit_le`,
`depth_thresholdDeMorganCircuit_le`) [Chandra et al.][ChandraStockmeyerVishkin1984],
[Vollmer, Chapter 4][Vollmer1999]. Specializing to cutoff `⌈k / 2⌉` gives a De Morgan circuit
`majorityDeMorganCircuit k` for `majority k`.

Consequently, any threshold slice family `fun n => threshold n (t n)` lies in **NC¹**
(`threshold_mem_NC_one`), and in particular **MAJ ∈ NC¹** (`majority_mem_NC_one`) and
**strictMajority ∈ NC¹** (`strictMajority_mem_NC_one`). Replacing each gate of a fan-in-bounded
threshold or majority circuit by `thresholdDeMorganCircuit` simulates depth `d` and fan-in `F`
in De Morgan depth `O(d log F)` and size `O(s F log F)`
(`Threshold.exists_deMorgan_simulation_of_fanInAtMost`,
`Unbounded.exists_deMorgan_simulation_majority_of_fanInAtMost`).

## Main definitions

* `Cslib.Circuits.Boolean.wordConstCircuit`: a constant `w`-bit word circuit of size `2` and depth
  at most `1`.
* `Cslib.Circuits.Boolean.thresholdDeMorganCircuit`: a De Morgan circuit of size `O(k log k)` and
  depth `O(log k)` computing `threshold k j`.
* `Cslib.Circuits.Boolean.majorityDeMorganCircuit`: a De Morgan circuit of size `O(k log k)` and
  depth `O(log k)` computing `majority k`.
* `Cslib.Circuits.Boolean.Threshold.Op.deMorganCircuit`: a De Morgan circuit for each operation of
  the threshold basis.
* `Cslib.Circuits.Boolean.Unbounded.ExtOp.majorityDeMorganCircuit`: a De Morgan circuit for each
  operation of the `TC` basis.

## Main results

* `Cslib.Circuits.Boolean.computes_thresholdDeMorganCircuit`,
  `size_thresholdDeMorganCircuit_le`, `depth_thresholdDeMorganCircuit_le`.
* `Cslib.Circuits.Boolean.computes_majorityDeMorganCircuit`,
  `size_majorityDeMorganCircuit_le`, `depth_majorityDeMorganCircuit_le`.
* `Cslib.Circuits.Boolean.threshold_mem_NC_one`, `majority_mem_NC_one`,
  `strictMajority_mem_NC_one`.
* `Cslib.Circuits.Boolean.Threshold.exists_deMorgan_simulation_of_fanInAtMost`,
  `Cslib.Circuits.Boolean.Unbounded.exists_deMorgan_simulation_majority_of_fanInAtMost`.
* `Cslib.Circuits.Boolean.mem_NC_succ_of_threshold_fanInAtMost`,
  `Cslib.Circuits.Boolean.mem_NC_succ_of_majority_fanInAtMost`.

## References

* [A. K. Chandra, L. Stockmeyer, U. Vishkin, *Constant depth reducibility*]
  [ChandraStockmeyerVishkin1984]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {n m w : ℕ}

/-! ### Constant word circuit -/

/-- Constant `w`-bit word circuit on `n` inputs: computes `false` and `true` once and wires each
output bit `i` to the corresponding constant gate. -/
def wordConstCircuit (n : ℕ) (y : BitString w) : Circuit signature n w :=
  (Circuit.wiring signature fun i : Fin w =>
      if y i then Fin.natAdd 1 (0 : Fin 1) else Fin.castAdd 1 (0 : Fin 1)).comp
    ((Circuit.oneGate (Op.const false) Fin.elim0).append
      (Circuit.oneGate (Op.const true) Fin.elim0))

/-- `wordConstCircuit n y` evaluates to the constant bit string `y` on every input. -/
@[simp] theorem eval_wordConstCircuit (y : BitString w) (x : BitString n) :
    (wordConstCircuit n y).eval interpretation x = y := by
  funext i
  rw [wordConstCircuit, Circuit.eval_comp, Circuit.eval_wiring, Circuit.eval_append,
    Function.comp_apply]
  cases y i <;> rfl

/-- `wordConstCircuit n y` uses `2` gates (one `false` and one `true` constant gate). -/
@[simp] theorem size_wordConstCircuit (n : ℕ) (y : BitString w) :
    (wordConstCircuit n y).size = 2 :=
  rfl

/-- `wordConstCircuit n y` has depth at most `1`. -/
theorem depth_wordConstCircuit_le (n : ℕ) (y : BitString w) :
    (wordConstCircuit n y).depth ≤ 1 := by
  refine (Circuit.depth_comp_le _ _).trans ?_
  rw [Circuit.depth_wiring, zero_add]
  exact (Circuit.depth_append_le _ _).trans (by simp)

/-! ### Threshold and majority circuits in `NC¹` -/

/-- **Logarithmic-depth threshold circuit**: computes `threshold k j` over the De Morgan basis of
fan-in two by computing the `⌈log₂ (k + 1)⌉`-bit binary numeral of the input's Hamming weight
(`weightCircuit k`) and comparing it against `j` (`leCircuit`). When `k < j`, the threshold cannot
be met and a single `false` gate is used. -/
def thresholdDeMorganCircuit (k j : ℕ) : Circuit signature k 1 :=
  if h : j ≤ k then
    let w := Nat.clog 2 (k + 1)
    have hj : j < 2 ^ w :=
      (Nat.lt_succ_of_le h).trans_le (Nat.le_pow_clog one_lt_two (k + 1))
    (leCircuit w).comp
      ((wordConstCircuit k ((BitString.equivFin w).symm ⟨j, hj⟩)).append (weightCircuit k))
  else
    Circuit.oneGate (Op.const false) Fin.elim0

/-- `thresholdDeMorganCircuit k j` computes `threshold k j`. -/
theorem computes_thresholdDeMorganCircuit (k j : ℕ) :
    (thresholdDeMorganCircuit k j).Computes interpretation (single (threshold k j)) := by
  intro x
  funext o
  dsimp [thresholdDeMorganCircuit]
  split_ifs with h
  · rw [Circuit.eval_comp, Circuit.eval_append, eval_wordConstCircuit, eval_leCircuit]
    simp only [threshold, Equiv.apply_symm_apply, Fin.le_iff_val_le_val,
      val_eval_weightCircuit]
  · simp only [Circuit.eval_oneGate, interpretation, threshold_eq_false_of_lt (not_le.1 h)]

/-- Evaluating `thresholdDeMorganCircuit k j` on `x` yields `single (threshold k j) x`. -/
@[simp] theorem eval_thresholdDeMorganCircuit (k j : ℕ) (x : BitString k) :
    (thresholdDeMorganCircuit k j).eval interpretation x = single (threshold k j) x :=
  computes_thresholdDeMorganCircuit k j x

/-- `thresholdDeMorganCircuit k j` uses `O(k log k)` gates. -/
theorem size_thresholdDeMorganCircuit_le (k j : ℕ) :
    (thresholdDeMorganCircuit k j).size ≤
      4 + k + 40 * k * Nat.clog 2 (k + 1) +
        Nat.clog 2 (k + 1) * (20 * Nat.clog 2 (k + 1) + 6) := by
  dsimp [thresholdDeMorganCircuit]
  split_ifs with h
  · rw [Circuit.size_comp, Circuit.size_append, size_leCircuit, size_wordConstCircuit]
    have hw := size_weightCircuit_le k
    have hmax : max 1 k ≤ 1 + k := max_le (Nat.le_add_right 1 k) (Nat.le_add_left k 1)
    nlinarith
  · rw [Circuit.size_oneGate]
    omega

/-- `thresholdDeMorganCircuit k j` has depth at most `2 + 23 ⌈log₂ (k + 1)⌉`. -/
theorem depth_thresholdDeMorganCircuit_le (k j : ℕ) :
    (thresholdDeMorganCircuit k j).depth ≤ 2 + 23 * Nat.clog 2 (k + 1) := by
  dsimp [thresholdDeMorganCircuit]
  split_ifs with h
  · refine (Circuit.depth_comp_le _ _).trans ?_
    have hle := depth_leCircuit_le (Nat.clog 2 (k + 1))
    have happ := (Circuit.depth_append_le
        (wordConstCircuit k ((BitString.equivFin (Nat.clog 2 (k + 1))).symm
          ⟨j, (Nat.lt_succ_of_le h).trans_le (Nat.le_pow_clog one_lt_two (k + 1))⟩))
        (weightCircuit k)).trans
      (max_le ((depth_wordConstCircuit_le _ _).trans (Nat.le_add_right 1 _))
        (depth_weightCircuit_le k))
    omega
  · rw [Circuit.depth_oneGate]
    omega

/-- **Logarithmic-depth majority circuit**: computes `majority k` over the De Morgan basis of
fan-in two in size `O(k log k)` and depth `O(log k)`. -/
def majorityDeMorganCircuit (k : ℕ) : Circuit signature k 1 :=
  thresholdDeMorganCircuit k ((k + 1) / 2)

/-- `majorityDeMorganCircuit k` computes `majority k`. -/
theorem computes_majorityDeMorganCircuit (k : ℕ) :
    (majorityDeMorganCircuit k).Computes interpretation (single (majority k)) :=
  computes_thresholdDeMorganCircuit k ((k + 1) / 2)

/-- Evaluating `majorityDeMorganCircuit k` on `x` yields `single (majority k) x`. -/
@[simp] theorem eval_majorityDeMorganCircuit (k : ℕ) (x : BitString k) :
    (majorityDeMorganCircuit k).eval interpretation x = single (majority k) x :=
  computes_majorityDeMorganCircuit k x

/-- `majorityDeMorganCircuit k` uses `O(k log k)` gates. -/
theorem size_majorityDeMorganCircuit_le (k : ℕ) :
    (majorityDeMorganCircuit k).size ≤
      4 + k + 40 * k * Nat.clog 2 (k + 1) +
        Nat.clog 2 (k + 1) * (20 * Nat.clog 2 (k + 1) + 6) :=
  size_thresholdDeMorganCircuit_le k ((k + 1) / 2)

/-- Quadratic upper bound on the size of `majorityDeMorganCircuit k`. -/
theorem size_majorityDeMorganCircuit_le_sq (k : ℕ) :
    (majorityDeMorganCircuit k).size ≤ 65 * (k + 1) ^ 2 := by
  have h := size_majorityDeMorganCircuit_le k
  have hclog : Nat.clog 2 (k + 1) ≤ k + 1 :=
    (Nat.clog_le_iff_le_pow one_lt_two).2 Nat.lt_two_pow_self.le
  nlinarith

/-- `majorityDeMorganCircuit k` has depth at most `2 + 23 ⌈log₂ (k + 1)⌉`. -/
theorem depth_majorityDeMorganCircuit_le (k : ℕ) :
    (majorityDeMorganCircuit k).depth ≤ 2 + 23 * Nat.clog 2 (k + 1) :=
  depth_thresholdDeMorganCircuit_le k ((k + 1) / 2)

/-- Every family of threshold functions `fun n => threshold n (t n)` belongs to **NC¹**. -/
theorem threshold_mem_NC_one (t : ℕ → ℕ) :
    Language.ofSlices (fun n => threshold n (t n)) ∈ NC 1 := by
  refine ⟨25, fun n =>
      4 + n + 40 * n * Nat.clog 2 (n + 1) +
        Nat.clog 2 (n + 1) * (20 * Nat.clog 2 (n + 1) + 6),
    by fun_prop, fun n => ?_⟩
  refine ⟨thresholdDeMorganCircuit n (t n), ?_, ?_,
    size_thresholdDeMorganCircuit_le n (t n)⟩
  · simpa only [Language.slice_ofSlices] using computes_thresholdDeMorganCircuit n (t n)
  · have hclog : Nat.clog 2 (n + 1) ≤ Nat.log 2 n + 1 :=
      (Nat.clog_le_iff_le_pow one_lt_two).2 (Nat.lt_pow_succ_log_self one_lt_two n)
    have hd := depth_thresholdDeMorganCircuit_le n (t n)
    dsimp only
    rw [pow_one]
    omega

/-- **Majority is in NC¹.** -/
theorem majority_mem_NC_one : Language.ofSlices majority ∈ NC 1 :=
  threshold_mem_NC_one fun n => (n + 1) / 2

/-- **Strict majority is in NC¹.** -/
theorem strictMajority_mem_NC_one : Language.ofSlices strictMajority ∈ NC 1 :=
  threshold_mem_NC_one fun n => n / 2 + 1

/-! ### Simulating fan-in-bounded threshold and majority circuits -/

namespace Threshold

/-- A De Morgan circuit of fan-in two for each operation of the threshold basis: one negation gate
for `.not`, and `thresholdDeMorganCircuit m j` for `.threshold m j`. -/
def Op.deMorganCircuit : (op : Op) → Circuit Boolean.signature op.arity 1
  | .not => Circuit.oneGate .not id
  | .threshold m j => thresholdDeMorganCircuit m j

/-- The De Morgan circuit of a threshold operation computes it. -/
theorem Op.computes_deMorganCircuit (op : Op) :
    op.deMorganCircuit.Computes Boolean.interpretation (single (interpretation op)) := by
  cases op with
  | not =>
    intro x
    funext o
    rw [Subsingleton.elim o 0]
    rfl
  | threshold m j => exact computes_thresholdDeMorganCircuit m j

/-- The De Morgan circuit of a threshold operation of arity `k` uses `O(k log k)` gates. -/
theorem Op.size_deMorganCircuit_le (op : Op) :
    op.deMorganCircuit.size ≤
      4 + op.arity + 40 * op.arity * Nat.clog 2 (op.arity + 1) +
        Nat.clog 2 (op.arity + 1) * (20 * Nat.clog 2 (op.arity + 1) + 6) := by
  cases op with
  | not =>
    simp only [deMorganCircuit, Circuit.size_oneGate]
    omega
  | threshold m j => exact size_thresholdDeMorganCircuit_le m j

/-- The De Morgan circuit of a threshold operation of arity `k` has depth at most
`2 + 23 ⌈log₂ (k + 1)⌉`. -/
theorem Op.depth_deMorganCircuit_le (op : Op) :
    op.deMorganCircuit.depth ≤ 2 + 23 * Nat.clog 2 (op.arity + 1) := by
  cases op with
  | not =>
    simp only [deMorganCircuit, Circuit.depth_oneGate]
    omega
  | threshold m j => exact depth_thresholdDeMorganCircuit_le m j

/-- **De Morgan circuits simulate fan-in-bounded threshold circuits**: a circuit over the threshold
basis of `n` inputs, `s` gates, depth `d`, and fan-in at most `F` has an equivalent De Morgan
circuit of fan-in two with at most
`s (4 + F + 40 F ⌈log₂ (F + 1)⌉ + ⌈log₂ (F + 1)⌉ (20 ⌈log₂ (F + 1)⌉ + 6))` gates and depth at most
`(2 + 23 ⌈log₂ (F + 1)⌉) d`. -/
theorem exists_deMorgan_simulation_of_fanInAtMost {F : ℕ} (C : Circuit signature n m)
    (hF : C.FanInAtMost F) :
    ∃ D : Circuit Boolean.signature n m,
      D.eval Boolean.interpretation = C.eval interpretation ∧
      D.size ≤ C.size * (4 + F + 40 * F * Nat.clog 2 (F + 1) +
        Nat.clog 2 (F + 1) * (20 * Nat.clog 2 (F + 1) + 6)) ∧
      D.depth ≤ (2 + 23 * Nat.clog 2 (F + 1)) * C.depth := by
  have hlines := Program.fanInAtMost_iff.1 hF
  refine ⟨C.simulate Op.deMorganCircuit, ?_, ?_, ?_⟩
  · exact Circuit.eval_simulate _ _ Op.computes_deMorganCircuit
  · rw [Circuit.size_simulate, Program.cost_eq_sum]
    refine (Finset.sum_le_sum (g := fun _ =>
        4 + F + 40 * F * Nat.clog 2 (F + 1) +
          Nat.clog 2 (F + 1) * (20 * Nat.clog 2 (F + 1) + 6)) fun k _ => ?_).trans_eq
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Circuit.size])
    have hk : (C.program.lines k).op.arity ≤ F := hlines k
    have hclog : Nat.clog 2 ((C.program.lines k).op.arity + 1) ≤ Nat.clog 2 (F + 1) :=
      Nat.clog_mono_right 2 (Nat.add_le_add_right hk 1)
    refine (Op.size_deMorganCircuit_le _).trans ?_
    gcongr
  · refine (Circuit.depth_simulate_le _ _).trans
      (C.depthWith_le_mul_depth fun k => (Op.depth_deMorganCircuit_le _).trans ?_)
    have hk : (C.program.lines k).op.arity ≤ F := hlines k
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_left 23 (Nat.clog_mono_right 2 (Nat.add_le_add_right hk 1))) 2

end Threshold

namespace Unbounded

/-- A De Morgan circuit of fan-in two for each operation of the `TC` basis: balanced trees for the
unbounded fan-in operations, and `majorityDeMorganCircuit m` for `.gate m`. -/
def ExtOp.majorityDeMorganCircuit : (op : ExtOp) → Circuit Boolean.signature op.arity 1
  | .ac op => op.deMorganFormula.toCircuit
  | .gate m => Boolean.majorityDeMorganCircuit m

/-- The De Morgan circuit of a `TC` operation computes it. -/
theorem ExtOp.computes_majorityDeMorganCircuit (op : ExtOp) :
    op.majorityDeMorganCircuit.Computes Boolean.interpretation
      (single (extInterpretation majority op)) := by
  cases op with
  | ac op => exact (Op.computes_deMorganFormula op).toCircuit
  | gate m => exact Boolean.computes_majorityDeMorganCircuit m

/-- The De Morgan circuit of a `TC` operation of arity `k` uses `O(k log k)` gates. -/
theorem ExtOp.size_majorityDeMorganCircuit_le (op : ExtOp) :
    op.majorityDeMorganCircuit.size ≤
      4 + op.arity + 40 * op.arity * Nat.clog 2 (op.arity + 1) +
        Nat.clog 2 (op.arity + 1) * (20 * Nat.clog 2 (op.arity + 1) + 6) := by
  cases op with
  | ac op =>
    rw [majorityDeMorganCircuit, Formula.size_toCircuit]
    have h1 := Op.size_deMorganFormula_le op
    have h2 : max 1 op.arity ≤ 1 + op.arity := max_le (Nat.le_add_right 1 _) (Nat.le_add_left _ 1)
    change op.deMorganFormula.size ≤
      4 + op.arity + 40 * op.arity * Nat.clog 2 (op.arity + 1) +
        Nat.clog 2 (op.arity + 1) * (20 * Nat.clog 2 (op.arity + 1) + 6)
    omega
  | gate m => exact Boolean.size_majorityDeMorganCircuit_le m

/-- The De Morgan circuit of a `TC` operation of arity `k` has depth at most
`2 + 23 ⌈log₂ (k + 1)⌉`. -/
theorem ExtOp.depth_majorityDeMorganCircuit_le (op : ExtOp) :
    op.majorityDeMorganCircuit.depth ≤ 2 + 23 * Nat.clog 2 (op.arity + 1) := by
  cases op with
  | ac op =>
    refine (Formula.depth_toCircuit_le _).trans ((Op.depth_deMorganFormula_le op).trans ?_)
    have hclog : Nat.clog 2 op.arity ≤ Nat.clog 2 (op.arity + 1) :=
      Nat.clog_mono_right 2 (Nat.le_succ _)
    change max 1 (Nat.clog 2 op.arity) ≤ 2 + 23 * Nat.clog 2 (op.arity + 1)
    omega
  | gate m => exact Boolean.depth_majorityDeMorganCircuit_le m

/-- **De Morgan circuits simulate fan-in-bounded majority circuits**: a circuit over the `TC` basis
(unbounded `AND`, `OR`, `NOT`, and `MAJ` gates) of `n` inputs, `s` gates, depth `d`, and fan-in at
most `F` has an equivalent De Morgan circuit of fan-in two of size `O(s F log F)` and depth
`O(d log F)`. -/
theorem exists_deMorgan_simulation_majority_of_fanInAtMost {F : ℕ}
    (C : Circuit extSignature n m) (hF : C.FanInAtMost F) :
    ∃ D : Circuit Boolean.signature n m,
      D.eval Boolean.interpretation = C.eval (extInterpretation majority) ∧
      D.size ≤ C.size * (4 + F + 40 * F * Nat.clog 2 (F + 1) +
        Nat.clog 2 (F + 1) * (20 * Nat.clog 2 (F + 1) + 6)) ∧
      D.depth ≤ (2 + 23 * Nat.clog 2 (F + 1)) * C.depth := by
  obtain ⟨D, he, hs, hd⟩ := Threshold.exists_deMorgan_simulation_of_fanInAtMost
    (C.mapOp Threshold.ofMajority) (by simpa using hF)
  exact ⟨D, he.trans (funext fun x => Circuit.eval_mapOp C x),
    by simpa using hs, by simpa using hd⟩

end Unbounded

/-- Any language decided by polynomial-size, polynomially fan-in-bounded threshold circuits of
depth `O((log n) ^ i)` belongs to **NCⁱ⁺¹** [Vollmer, Theorem 4.22][Vollmer1999]. -/
theorem mem_NC_succ_of_threshold_fanInAtMost {L : Language Bool} {i c : ℕ} {s F : ℕ → ℕ}
    (hs : PolynomiallyBounded s) (hF : PolynomiallyBounded F)
    (hC : ∀ n, ∃ C : Circuit Threshold.signature n 1,
      C.Computes Threshold.interpretation (single (L.slice n)) ∧
      C.depth ≤ c * (Nat.log 2 n + 1) ^ i ∧ C.size ≤ s n ∧ C.FanInAtMost (F n)) :
    L ∈ NC (i + 1) := by
  obtain ⟨e, he⟩ := PolynomiallyBounded.exists_clog_le_mul_log
    (s := fun n => F n + 1) (by fun_prop)
  refine ⟨c * (23 * e + 2), fun n =>
      s n * (4 + F n + 40 * F n * Nat.clog 2 (F n + 1) +
        Nat.clog 2 (F n + 1) * (20 * Nat.clog 2 (F n + 1) + 6)),
    by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs, hCf⟩ := hC n
  obtain ⟨D, hDe, hDs, hDd⟩ := Threshold.exists_deMorgan_simulation_of_fanInAtMost C hCf
  refine ⟨D, fun x => (congrFun hDe x).trans (hCc x), ?_, ?_⟩
  · have hlog : 2 + 23 * Nat.clog 2 (F n + 1) ≤ (23 * e + 2) * (Nat.log 2 n + 1) := by
      have h1 := he n
      nlinarith
    calc D.depth ≤ (2 + 23 * Nat.clog 2 (F n + 1)) * C.depth := hDd
      _ ≤ ((23 * e + 2) * (Nat.log 2 n + 1)) * (c * (Nat.log 2 n + 1) ^ i) :=
        Nat.mul_le_mul hlog hCd
      _ = c * (23 * e + 2) * (Nat.log 2 n + 1) ^ (i + 1) := by ring
  · refine hDs.trans ?_
    beta_reduce
    gcongr

/-- Any language decided by polynomial-size, polynomially fan-in-bounded `TC` circuits of depth
`O((log n) ^ i)` belongs to **NCⁱ⁺¹** [Vollmer, Theorem 4.22][Vollmer1999]. -/
theorem mem_NC_succ_of_majority_fanInAtMost {L : Language Bool} {i c : ℕ} {s F : ℕ → ℕ}
    (hs : PolynomiallyBounded s) (hF : PolynomiallyBounded F)
    (hC : ∀ n, ∃ C : Circuit Unbounded.extSignature n 1,
      C.Computes (Unbounded.extInterpretation majority) (single (L.slice n)) ∧
      C.depth ≤ c * (Nat.log 2 n + 1) ^ i ∧ C.size ≤ s n ∧ C.FanInAtMost (F n)) :
    L ∈ NC (i + 1) := by
  apply mem_NC_succ_of_threshold_fanInAtMost (c := c) (s := s) (F := F) hs hF
  intro n
  obtain ⟨C, hc, hd, hs, hf⟩ := hC n
  exact ⟨C.mapOp Threshold.ofMajority, hc.mapOp,
    by simpa using hd, by simpa using hs, by simpa using hf⟩

end Cslib.Circuits.Boolean
