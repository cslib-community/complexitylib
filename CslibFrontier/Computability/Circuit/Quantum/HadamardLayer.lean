/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Parallel
public import CslibFrontier.Computability.Circuit.Quantum.Uniform
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# A layer of Hadamard gates

The gate codes `hadamardCodes o p` put one Hadamard gate on each of the qubits `o, …, o + p - 1`.
On a basis state whose qubits `o, …, o + p - 1` are zero, the layer prepares the uniform
superposition of the `2^p` strings on those qubits, each with amplitude `2^{-p/2}`
(`Cslib.Quantum.eval_hadamardCodes_ket`). This is how a quantum circuit simulates `p` fair coins:
Hadamard gates on fresh qubits, followed by a classical circuit reading them
[Watrous][Watrous2008], Section IV.3.

## Main definitions

* `Cslib.Quantum.hadamardCodes`: Hadamard gates on a block of qubits.

## Main results

* `Cslib.Quantum.eval_hadamardCodes_ket`: the layer on zero qubits prepares the uniform
  superposition.
* `Cslib.Quantum.computableInPolyTime_hadamardCodes`: the codes are computable in polynomial time
  from the block in unary.

## References

* [J. Watrous, *Quantum computational complexity*][Watrous2008]
-/

@[expose] public section

namespace Cslib.Quantum

open Finset GateCode Turing.MultiTapeTM

variable {N : ℕ}

/-- Hadamard gate codes on the qubits `o, …, o + p - 1`. -/
def hadamardCodes (o p : ℕ) : List GateCode := (List.range p).map fun j => (true, o + j, [])

/-- **A layer of Hadamard gates on zero qubits** prepares the uniform superposition: on a basis
state `|X⟩` whose qubits `o, …, o + p - 1` are zero, it gives `2^{-p/2} ∑_r |X with r on them⟩`. -/
theorem eval_hadamardCodes_ket {o p : ℕ} (h : o + p ≤ N) (X : Fin N → Bool)
    (hX : ∀ i : Fin p, X (blockEmb o h i) = false) :
    Circuit.eval (Circuit.ofCodes N (hadamardCodes o p)) (ket X) =
      ∑ r : Fin p → Bool, (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ p • ket (glue (blockEmb o h) r X) := by
  induction p with
  | zero =>
    have hg (r : Fin 0 → Bool) : glue (blockEmb o h) r X = X := by
      funext i
      rw [glue_blockEmb_apply]
      exact dite_eq_right_iff.mpr fun h => by omega
    simp [hadamardCodes, hg]
  | succ p ih =>
    have h' : o + p ≤ N := by omega
    have ht : o + p < N := by omega
    rw [hadamardCodes, List.range_succ, List.map_append, Circuit.ofCodes_append,
      Circuit.eval_append]
    rw [show (List.range p).map (fun j => ((true, o + j, []) : GateCode)) = hadamardCodes o p
      from rfl, ih h' fun i => by
        rw [show blockEmb o h' i = blockEmb o h (Fin.castSucc i) from Fin.ext (by simp)]
        exact hX _]
    obtain ⟨g, hg⟩ : ∃ g, toPlacedGate? N (true, o + p, []) = some g :=
      Option.isSome_iff_exists.mp (isSome_toPlacedGate?_iff.mpr ⟨ht, rfl⟩)
    have hC : Circuit.ofCodes N [(true, o + p, [])] = [g] := by
      simp [Circuit.ofCodes, hg]
    simp only [List.map_cons, List.map_nil, hC, map_sum, map_smul, Circuit.eval_cons,
      Circuit.eval_nil, eval_toPlacedGate_hadamard_ket hg ht]
    have hlast (r : Fin p → Bool) : glue (blockEmb o h') r X ⟨o + p, ht⟩ = false := by
      rw [glue_blockEmb_apply, dite_eq_right (by simp), show (⟨o + p, ht⟩ : Fin N) =
        blockEmb o h (Fin.last p) from Fin.ext (by simp; omega)]
      exact hX _
    have hupd (r : Fin p → Bool) (c : Bool) :
        Function.update (glue (blockEmb o h') r X) ⟨o + p, ht⟩ c =
          glue (blockEmb o h) (Fin.snoc r c) X := by
      funext i
      by_cases hi : (i : ℕ) = o + p
      · rw [show i = ⟨o + p, ht⟩ from Fin.ext hi, Function.update_self, glue_blockEmb_apply,
          dite_eq_left (by simp)]
        simp [Fin.snoc]
      · rw [Function.update_of_ne (fun h => hi (congrArg Fin.val h)), glue_blockEmb_apply,
          glue_blockEmb_apply]
        by_cases hi' : o ≤ (i : ℕ) ∧ (i : ℕ) < o + p
        · rw [dite_eq_left hi', dite_eq_left ⟨hi'.1, by omega⟩]
          rw [show (⟨i - o, by omega⟩ : Fin (p + 1)) = Fin.castSucc ⟨i - o, by omega⟩ from rfl,
            Fin.snoc_castSucc]
        · rw [dite_eq_right hi', dite_eq_right (by omega)]
    simp only [hlast, Bool.false_and, Bool.false_eq_true, ite_false, one_mul, hupd, smul_sum,
      smul_smul, ← pow_succ]
    rw [← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, sum_comm]
    rfl

/-- The Hadamard codes on a block are computable in polynomial time from the block in unary. -/
theorem computableInPolyTime_hadamardCodes {γ : Type} {enc : γ ↪ List Bool} {o p : γ → ℕ}
    (ho : ComputableInPolyTime o enc encUnary) (hp : ComputableInPolyTime p enc encUnary) :
    ComputableInPolyTime (fun c => hadamardCodes (o c) (p c)) enc (encList encGateCode) := by
  unfold hadamardCodes
  fun_prop

end Cslib.Quantum
