/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Multiplicity
import Complexity.Computability.Circuit.Simulation


import Diag1155.Measure
/-!
# `MOD_q` gates from majority gates: ACⁱ[q] ⊆ TCⁱ

Over a basis containing the unbounded fan-in basis, the `MOD_q` function on `n` bits is the
disjunction, over the `k ≤ n` not divisible by `q`, of "exactly `k` bits are true", each of which is
two thresholds, so two majority gates on padded inputs (`modCircuitOfMajority`)
[Chandra, Stockmeyer and Vishkin][ChandraStockmeyerVishkin1984]. With a single majority gate this
is a circuit of `8 n + 9` gates and depth five.

A `MOD_q` gate depends on how often it reads each wire, but only modulo `q` (for `q = 0`, only on
whether it reads it at all): after aggregating multiplicities (`Unbounded.multCircuit`), a gate
reading `N` distinct wires is a `MOD_q` function of at most `max q 1 · N` bits, wired from its
arguments (`Unbounded.modMultCircuit`). Replacing every gate of a polynomial-size circuit with
`MOD_q` gates, of depth `d`, gives a polynomial-size circuit with majority gates of depth at most
`5 d`: **ACⁱ[q] ⊆ TCⁱ** (`ACMod_subset_TC`) [Vollmer, Chapter 4][Vollmer1999], in particular
**AC⁰[q] ⊆ TC⁰** (`AC0Mod_subset_TC0`).

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.modCount`, `Unbounded.modMult`, `Unbounded.expandIndex`:
  modulus-`q` count predicate, reduced wire multiplicity, and expansion index map.
* `Cslib.Circuits.Boolean.Unbounded.modMultCircuit`: a circuit with majority gates for every
  operation of the basis with `MOD_q` gates and multiplicities.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.exists_majority_simulation_modGate`: a circuit with `MOD_q`
  gates of `n` inputs, `s` gates and depth `d` has an equivalent circuit with majority gates of at
  most `s (9 + 8 max q 1 · (n + s))` gates and depth at most `5 d`.
* `Cslib.Circuits.Boolean.ACMod_subset_TC`: **ACⁱ[q] ⊆ TCⁱ**.
* `Cslib.Circuits.Boolean.AC0Mod_subset_TC0`: **AC⁰[q] ⊆ TC⁰**.

## References

* [A. K. Chandra, L. Stockmeyer, U. Vishkin, *Constant depth reducibility*]
  [ChandraStockmeyerVishkin1984]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
-/


diag1155_install
@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset Unbounded

namespace Unbounded

/-- The count of true arguments that a `MOD_q` gate sees: whether it is divisible by `q`. -/
def modCount (q _ c : ℕ) : Bool :=
  decide (c % q ≠ 0)

/-- The `MOD_q` gate computes `modCount q` of the number of its true arguments. -/
theorem modGate_eq_modCount (q m : ℕ) (x : Fin m → Bool) :
    modGate q m x = modCount q m (BitString.weight x) :=
  rfl

/-- The multiplicity of a wire that matters to a `MOD_q` gate: modulo `q`, and for `q = 0` whether
it is read at all. -/
def modMult (q k : ℕ) : ℕ :=
  if q = 0 then min k 1 else k % q

/-- The reduced multiplicity `modMult q k` is at most `max q 1`. -/
theorem modMult_le (q k : ℕ) : modMult q k ≤ max q 1 := by
  unfold modMult
  split_ifs with hq
  · exact (min_le_right _ _).trans (le_max_right _ _)
  · exact (Nat.mod_lt _ (Nat.pos_of_ne_zero hq)).le.trans (le_max_left _ _)

/-- Reducing multiplicities with `modMult` keeps divisibility of the weighted count by `q`. -/
theorem multWeight_modMult_mod_ne_zero_iff {N : ℕ} (q : ℕ) (mult : Fin N → ℕ) (x : Fin N → Bool) :
    multWeight (fun i => modMult q (mult i)) x % q ≠ 0 ↔ multWeight mult x % q ≠ 0 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [Nat.mod_zero, ne_eq, multWeight, modMult, ↓reduceIte, Finset.sum_eq_zero_iff,
      Finset.mem_univ, true_imp_iff, mul_eq_zero, not_iff_not]
    refine forall_congr' fun i => ?_
    omega
  · have : multWeight (fun i => modMult q (mult i)) x % q = multWeight mult x % q := by
      simp only [multWeight, modMult, hq.ne', ↓reduceIte]
      rw [Finset.sum_nat_mod, Finset.sum_nat_mod (s := univ) (f := fun i => mult i * (x i).toNat)]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    rw [this]

/-- The argument of a symmetric gate read by each of its `∑ i, r i` copies. -/
def expandIndex {N : ℕ} (r : Fin N → ℕ) (j : Fin (∑ i, r i)) : Fin N :=
  (finSigmaFinEquiv.symm j).1

/-- Repeating the `i`th argument `r i` times counts it with multiplicity `r i`. -/
theorem weight_comp_expandIndex {N : ℕ} (r : Fin N → ℕ) (x : Fin N → Bool) :
    BitString.weight (x ∘ expandIndex r) = multWeight r x := by
  rw [BitString.weight_eq_sum_toNat, multWeight]
  simp only [Function.comp_apply, expandIndex]
  rw [Equiv.sum_comp finSigmaFinEquiv.symm (fun p => (x p.1).toNat), Fintype.sum_sigma]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- A circuit with majority gates for each operation of the basis with `MOD_q` gates and
multiplicities: an operation of the unbounded fan-in basis is one gate, and a `MOD_q` gate is
`modCircuitOfMajority` on its arguments repeated with their multiplicities reduced by `modMult`. -/
def modMultCircuit (q : ℕ) : (op : MultOp) → Circuit extSignature (multSignature.Arity op) 1
  | .ac op => Circuit.oneGate (σ := extSignature) (.ac op) id
  | .gate _ mult => (modCircuitOfMajority toExt q
      (Circuit.oneGate (σ := extSignature) (.gate _) id)).comp
      (Circuit.wiring extSignature (expandIndex fun i => modMult q (mult i)))

/-- The circuit of an operation computes it. -/
theorem computes_modMultCircuit (q : ℕ) (op : MultOp) :
    (modMultCircuit q op).Computes (extInterpretation majority)
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
    have hM : (Circuit.oneGate (σ := extSignature) (.gate (K + (K + 2))) id).Computes
        (extInterpretation majority) (single (majority (K + (K + 2)))) := fun y => by
      funext o
      rw [Subsingleton.elim o 0]
      rfl
    rw [modMultCircuit, Circuit.eval_comp, Circuit.eval_wiring,
      computes_modCircuitOfMajority hM q]
    funext o
    simp only [single, multInterpretation_gate, modGate_eq_modCount, modCount]
    rw [weight_comp_expandIndex, decide_eq_decide]
    exact multWeight_modMult_mod_ne_zero_iff q mult x

/-- The circuit of an operation reading `N` wires has at most `9 + 8 max q 1 · N` gates. -/
theorem size_modMultCircuit_le (q : ℕ) (op : MultOp) :
    (modMultCircuit q op).size ≤ 9 + 8 * max q 1 * multSignature.Arity op := by
  cases op with
  | ac op =>
    simp only [modMultCircuit, Circuit.size_oneGate]
    omega
  | gate N mult =>
    rw [modMultCircuit, Circuit.size_comp, Circuit.size_wiring, zero_add]
    refine (size_modCircuitOfMajority_le q).trans ?_
    have hK : ∑ i : Fin N, modMult q (mult i) ≤ max q 1 * N := by
      simpa [mul_comm] using Finset.sum_le_card_nsmul (univ : Finset (Fin N))
        (fun i => modMult q (mult i)) (max q 1) fun i _ => modMult_le q _
    simp only [Circuit.size_oneGate]
    change 1 + (∑ i, modMult q (mult i) + 1) * (2 * (2 + 1) + 2) ≤ 9 + 8 * max q 1 * N
    nlinarith

/-- The circuit of an operation has depth at most five. -/
theorem depth_modMultCircuit_le (q : ℕ) (op : MultOp) : (modMultCircuit q op).depth ≤ 5 := by
  cases op with
  | ac op => simp [modMultCircuit]
  | gate N mult =>
    refine (Circuit.depth_comp_le _ _).trans ?_
    rw [Circuit.depth_wiring, add_zero]
    exact (depth_modCircuitOfMajority_le q).trans (by simp)

/-- **Majority gates simulate `MOD_q` gates** [Vollmer, Chapter 4][Vollmer1999]: a circuit with
`MOD_q` gates of `n` inputs, `s` gates and depth `d` has an equivalent circuit with majority gates
of at most `s (9 + 8 max q 1 · (n + s))` gates and depth at most `5 d`. Its gates are first made to
read their distinct wires with multiplicities (`multCircuit`), and then replaced by
`modMultCircuit`. -/
theorem exists_majority_simulation_modGate {n m : ℕ} (q : ℕ) (C : Circuit extSignature n m) :
    ∃ D : Circuit extSignature n m,
      D.eval (extInterpretation majority) = C.eval (extInterpretation (modGate q)) ∧
      D.size ≤ C.size * (9 + 8 * max q 1 * (n + C.size)) ∧
      D.depth ≤ 5 * C.depth := by
  refine ⟨(multCircuit C).simulate (modMultCircuit q), ?_, ?_, ?_⟩
  · rw [Circuit.eval_simulate _ _ (computes_modMultCircuit q),
      eval_multCircuit (G := modCount q) (modGate_eq_modCount q)]
  · rw [Circuit.size_simulate, Program.cost_eq_sum]
    refine (Finset.sum_le_sum (g := fun _ => 9 + 8 * max q 1 * (n + C.size)) fun k _ =>
      (size_modMultCircuit_le q _).trans ?_).trans_eq
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, size_multCircuit])
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (arity_lines_multCircuit_le C k)) _
  · exact (Circuit.depth_simulate_le _ _).trans
      (((multCircuit C).depthWith_le_mul_depth fun k => depth_modMultCircuit_le q _).trans
        (Nat.mul_le_mul_left 5 (depth_multCircuit_le C)))

end Unbounded

/-- **ACⁱ[q] ⊆ TCⁱ** [Vollmer, Chapter 4][Vollmer1999]: polynomial-size circuits with `MOD_q`
gates of depth `O((log n) ^ i)` are simulated by polynomial-size circuits with majority gates of
depth `O((log n) ^ i)`. -/
theorem ACMod_subset_TC (q i : ℕ) : ACMod q i ⊆ TC i := by
  rintro L ⟨c, s, hs, hC⟩
  refine ⟨5 * c, fun n => s n * (9 + 8 * max q 1 * (n + s n)), by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  obtain ⟨D, hDe, hDs, hDd⟩ := exists_majority_simulation_modGate q C
  refine ⟨D, fun x => (congrFun hDe x).trans (hCc x), ?_, ?_⟩
  · calc D.depth ≤ 5 * C.depth := hDd
      _ ≤ 5 * (c * (Nat.log 2 n + 1) ^ i) := Nat.mul_le_mul_left 5 hCd
      _ = 5 * c * (Nat.log 2 n + 1) ^ i := by ring
  · refine hDs.trans ?_
    beta_reduce
    gcongr

/-- **AC⁰[q] ⊆ TC⁰.** -/
theorem AC0Mod_subset_TC0 (q : ℕ) : AC0Mod q ⊆ TC0 := by
  rw [← ACMod_zero, ← TC_zero]
  exact ACMod_subset_TC q 0

end Cslib.Circuits.Boolean
