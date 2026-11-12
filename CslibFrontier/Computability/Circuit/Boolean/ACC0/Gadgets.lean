/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ModGates
public import CslibFrontier.Foundations.Data.BitString.Parity.DotProduct
import Mathlib.Data.Finset.Sort

/-!
# Small AC⁰[2] circuits

Building blocks for circuits over `Unbounded.extSignature` read with `MOD₂` gates,
`Unbounded.extInterpretation (modGate 2)`, the basis of AC⁰[2]:

* `Unbounded.parityOnCircuit s`: one `MOD₂` gate on the inputs in `s`, computing `parityOn s`.
* `Unbounded.andCircuit i j`: one binary conjunction of two inputs.
* `Unbounded.constsCircuit φ z`: the bits of a fixed string `z`, from one constant gate
  (`Unbounded.constCircuit`) for each value, so two gates whatever the length of `z`. It is built
  over any basis containing the unbounded fan-in basis.
* `Unbounded.innerProductCircuit k`: the inner product `b ⬝ᵥ r` over GF(2) of two strings of `k`
  bits, as `k` conjunctions under one `MOD₂` gate.

The first three have depth at most one and the inner product depth at most two. Gates count
towards the size; wires do not.

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.parityOnCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.andCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.constsCircuit`: a parity, a conjunction and fixed bits.
* `Cslib.Circuits.Boolean.Unbounded.innerProductCircuit`: the inner product over GF(2).

## Main results

* `Cslib.Circuits.Boolean.Unbounded.eval_parityOnCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.eval_andCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.eval_constsCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.eval_innerProductCircuit`: what they compute.
* `Cslib.Circuits.Boolean.Unbounded.size_innerProductCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.depth_innerProductCircuit_le`: the inner product has `k + 1`
  gates and depth at most two.
-/

public section

namespace Cslib.Circuits.Boolean.Unbounded

open Finset

variable {n : ℕ}

/-! ### Parity of some inputs -/

/-- One `MOD₂` gate on the inputs in `s`, listed in increasing order. -/
def parityOnCircuit (s : Finset (Fin n)) : Circuit extSignature n 1 :=
  Circuit.oneGate (.gate #s) fun a => s.orderEmbOfFin rfl a

/-- With `MOD₂` gates, `parityOnCircuit s` computes the parity of the inputs in `s`. -/
@[simp] theorem eval_parityOnCircuit (s : Finset (Fin n)) (x : BitString n) (o : Fin 1) :
    (parityOnCircuit s).eval (extInterpretation (modGate 2)) x o = parityOn s x := by
  rw [parityOnCircuit, Circuit.eval_oneGate, extInterpretation_gate, modGate_two_eq_parity,
    parity, parityOn_eq_sum, parityOn_eq_sum]
  have h := sum_map univ (s.orderEmbOfFin rfl).toEmbedding x
  rw [map_orderEmbOfFin_univ] at h
  exact h.symm

/-- `parityOnCircuit s` is one gate. -/
@[simp] theorem size_parityOnCircuit (s : Finset (Fin n)) : (parityOnCircuit s).size = 1 :=
  Circuit.size_oneGate _ _

/-- `parityOnCircuit s` has depth one. -/
@[simp] theorem depth_parityOnCircuit (s : Finset (Fin n)) : (parityOnCircuit s).depth = 1 :=
  Circuit.depth_oneGate _ _

/-! ### Conjunction of two inputs -/

/-- One conjunction of the inputs `i` and `j`. -/
def andCircuit (i j : Fin n) : Circuit extSignature n 1 :=
  binCircuit toExt (.and 2) rfl (Circuit.wiring _ fun _ => i) (Circuit.wiring _ fun _ => j)

/-- `andCircuit i j` computes the conjunction of the inputs `i` and `j`, whatever the extra
gates compute. -/
@[simp] theorem eval_andCircuit (g : ∀ m, BooleanFunction m) (i j : Fin n) (x : BitString n)
    (o : Fin 1) : (andCircuit i j).eval (extInterpretation g) x o = (x i && x j) := by
  rw [andCircuit, eval_binCircuit_and]
  rfl

/-- `andCircuit i j` is one gate. -/
@[simp] theorem size_andCircuit (i j : Fin n) : (andCircuit i j).size = 1 := by
  simp [andCircuit]

/-- `andCircuit i j` has depth at most one. -/
theorem depth_andCircuit_le (i j : Fin n) : (andCircuit i j).depth ≤ 1 :=
  (depth_binCircuit_le _ _ _ _).trans (by simp)

/-! ### Fixed bits -/

section Consts

variable {σ : Signature} (φ : signature.Hom σ)

/-- The bits of `z`, each wired from one of two constant gates (`Unbounded.constCircuit`), over
any basis containing the unbounded fan-in basis along `φ`. -/
def constsCircuit {m : ℕ} (z : BitString m) : Circuit σ n m :=
  (Circuit.wiring σ fun i => if z i then Fin.castAdd 1 0 else Fin.natAdd 1 0).comp
    ((constCircuit φ true).append (constCircuit φ false))

variable {φ}

/-- `constsCircuit φ z` outputs `z` on every input. -/
@[simp] theorem eval_constsCircuit {I : Interpretation σ Bool} [φ.Preserves interpretation I]
    {m : ℕ} (z : BitString m) (x : BitString n) : (constsCircuit φ z).eval I x = z := by
  funext i
  rw [constsCircuit, Circuit.eval_comp, Circuit.eval_wiring, Function.comp_apply,
    Circuit.eval_append]
  cases z i
  · exact (Fin.append_right _ _ (0 : Fin 1)).trans (eval_constCircuit _ _ _)
  · exact (Fin.append_left _ _ (0 : Fin 1)).trans (eval_constCircuit _ _ _)

/-- `constsCircuit φ z` has two gates. -/
@[simp] theorem size_constsCircuit {m : ℕ} (z : BitString m) :
    (constsCircuit (n := n) φ z).size = 2 := by
  simp [constsCircuit]

/-- `constsCircuit φ z` has depth at most one. -/
theorem depth_constsCircuit_le {m : ℕ} (z : BitString m) :
    (constsCircuit (n := n) φ z).depth ≤ 1 := by
  refine (Circuit.depth_comp_le _ _).trans ?_
  rw [Circuit.depth_wiring, zero_add]
  exact (Circuit.depth_append_le _ _).trans
    (max_le (depth_constCircuit_le _) (depth_constCircuit_le _))

end Consts

/-! ### Inner product over GF(2) -/

/-- On inputs `(b, r)` of `k` bits each, the conjunctions `bᵢ ∧ rᵢ` under one `MOD₂` gate. -/
def innerProductCircuit (k : ℕ) : Circuit extSignature (k + k) 1 :=
  (parityOnCircuit univ).comp (Circuit.pi fun i => andCircuit (Fin.castAdd k i) (Fin.natAdd k i))

/-- With `MOD₂` gates, `innerProductCircuit k` computes the inner product over GF(2). -/
@[simp] theorem eval_innerProductCircuit {k : ℕ} (b r : BitString k) (o : Fin 1) :
    (innerProductCircuit k).eval (extInterpretation (modGate 2)) (Fin.append b r) o = b ⬝ᵥ r := by
  rw [innerProductCircuit, Circuit.eval_comp, eval_parityOnCircuit, Circuit.eval_pi,
    parityOn_eq_sum]
  simp only [eval_andCircuit, Fin.append_left, Fin.append_right]
  rfl

/-- `innerProductCircuit k` has `k + 1` gates. -/
@[simp] theorem size_innerProductCircuit (k : ℕ) : (innerProductCircuit k).size = k + 1 := by
  simp [innerProductCircuit]

/-- `innerProductCircuit k` has depth at most two. -/
theorem depth_innerProductCircuit_le (k : ℕ) : (innerProductCircuit k).depth ≤ 2 := by
  refine (Circuit.depth_comp_le _ _).trans ?_
  rw [depth_parityOnCircuit]
  exact Nat.add_le_add_left (Circuit.depth_pi_le _ fun i => depth_andCircuit_le _ _) 1

end Cslib.Circuits.Boolean.Unbounded
