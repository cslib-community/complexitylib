/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Parallel

/-!
# The real encoding of quantum circuits

A complex amplitude `a + ib` can be stored in two real amplitudes on one extra qubit. The *real
encoding* of an `m`-qubit state `ψ` is the `(m + 1)`-qubit state whose amplitude on `|x 0⟩` is
`Re ψ_x` and on `|x 1⟩` is `Im ψ_x` (`Cslib.Quantum.realEncode`); the last qubit says which part is
stored. A matrix entry `a` acts on such pairs as the real block `[[Re a, -Im a], [Im a, Re a]]`
(`Cslib.Quantum.realEntry`), so a matrix whose entries are these blocks acts on encoded states as
the original matrix does on states (`Cslib.Quantum.mulVec_realEncode`). Aharonov attributes the
encoding to Bernstein and Vazirani [Bernstein, Vazirani][BernsteinVazirani1997]; the blocks are
the real version `Ũ` of a gate `U` in Definition 1 of [Aharonov][Aharonov2003], with the encoding
qubit last.

A circuit `C'` on `m + 1` qubits *simulates* a circuit `C` on `m` qubits through the encoding when
it maps the encoding of every state to the encoding of its image under `C`
(`Cslib.Quantum.Circuit.RealSimulates`). Simulation is preserved by running circuits in sequence,
and a circuit started in `|x 0⟩` then ends in the encoding of the final state of the simulated
circuit started in `|x⟩` (`Cslib.Quantum.Circuit.RealSimulates.run_snoc_false`). The encoding
preserves the probability of every measurement of the first `m` qubits, since
`(Re a)² + (Im a)² = |a|²` (`Cslib.Quantum.measureProb_realEncode`).

A gate with real entries simulates itself: placed on the same qubits of the larger register, away
from the encoding qubit (`Cslib.Quantum.PlacedGate.mapWires` along `Fin.castSuccEmb`), it acts on
the real and the imaginary parts separately
(`Cslib.Quantum.PlacedGate.realSimulates_mapWires_castSuccEmb`). The Hadamard, NOT, CNOT and
Toffoli gates are real, and `CslibFrontier/Computability/Circuit/Quantum/PhaseCode.lean` simulates
the
controlled phase gates by four of them.

## Main definitions

* `Cslib.Quantum.realEncode`: the real encoding of a state, on one more qubit.
* `Cslib.Quantum.realEntry`: the real block of a complex matrix entry.
* `Cslib.Quantum.Circuit.RealSimulates`: simulation of a circuit through the real encoding.

## Main results

* `Cslib.Quantum.realEncode_ket`: the encoding of `|x⟩` is `|x 0⟩`.
* `Cslib.Quantum.measureProb_realEncode`: the encoding preserves the measurement probabilities of
  the first `m` qubits.
* `Cslib.Quantum.mulVec_realEncode`: a matrix of real blocks acts on encoded states as the
  original matrix does on states.
* `Cslib.Quantum.Circuit.realSimulates_of_matrix`: a circuit whose unitary consists of the real
  blocks of another's simulates it.
* `Cslib.Quantum.Circuit.RealSimulates.append`,
  `Cslib.Quantum.Circuit.RealSimulates.run_snoc_false`: simulation of sequences, and of runs from
  basis states.
* `Cslib.Quantum.PlacedGate.realSimulates_mapWires_castSuccEmb`: a gate with real entries
  simulates itself.

## References

* [D. Aharonov, *A simple proof that Toffoli and Hadamard are quantum universal*][Aharonov2003],
  arXiv:quant-ph/0301040v1, Definition 1
* [E. Bernstein, U. Vazirani, *Quantum complexity theory*][BernsteinVazirani1997]
-/

public section

namespace Cslib.Quantum

open Matrix Finset

variable {m : ℕ}

/-! ### The real encoding of states -/

/-- **The real encoding of a state**: on `m + 1` qubits, the amplitude `a + ib` of `|x⟩` becomes
the amplitude `a` of `|x 0⟩` and the amplitude `b` of `|x 1⟩`. -/
noncomputable def realEncode (ψ : Qubits m) : Qubits (m + 1) :=
  WithLp.toLp 2 fun z =>
    if z (Fin.last m) then ((ψ.ofLp (Fin.init z)).im : ℂ) else ((ψ.ofLp (Fin.init z)).re : ℂ)

theorem realEncode_apply (ψ : Qubits m) (z : Fin (m + 1) → Bool) :
    (realEncode ψ).ofLp z = if z (Fin.last m) then ((ψ.ofLp (Fin.init z)).im : ℂ)
      else ((ψ.ofLp (Fin.init z)).re : ℂ) := by
  simp only [realEncode, WithLp.ofLp_toLp]

@[simp] theorem realEncode_apply_snoc (ψ : Qubits m) (x : Fin m → Bool) (b : Bool) :
    (realEncode ψ).ofLp (Fin.snoc x b) =
      if b then ((ψ.ofLp x).im : ℂ) else ((ψ.ofLp x).re : ℂ) := by
  simp [realEncode_apply]

/-- A bit string on `m + 1` qubits is `x b` exactly when its first `m` bits are `x` and its last
bit is `b`. -/
theorem eq_snoc_iff {z : Fin (m + 1) → Bool} {x : Fin m → Bool} {b : Bool} :
    z = Fin.snoc x b ↔ Fin.init z = x ∧ z (Fin.last m) = b := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨rfl, rfl⟩
    exact (Fin.snoc_init_self z).symm

/-- **The encoding of a basis state** `|x⟩` is `|x 0⟩`. -/
@[simp] theorem realEncode_ket (x : Fin m → Bool) :
    realEncode (ket x) = ket (Fin.snoc x false) := by
  ext z
  obtain ⟨y, b, rfl⟩ : ∃ y b, z = Fin.snoc y b :=
    ⟨Fin.init z, z (Fin.last m), (Fin.snoc_init_self z).symm⟩
  rw [realEncode_apply_snoc]
  simp only [ket_apply, eq_snoc_iff, Fin.init_snoc, Fin.snoc_last]
  by_cases h : y = x <;> cases b <;> simp [h]

/-- A sum over the bit strings of `m + 1` qubits, split along the last qubit. -/
theorem sum_bitString_succ {M : Type*} [AddCommMonoid M] (f : (Fin (m + 1) → Bool) → M) :
    ∑ z, f z = ∑ x : Fin m → Bool, (f (Fin.snoc x false) + f (Fin.snoc x true)) := by
  rw [← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← sum_add_distrib]
  simp [add_comm]

/-- **The encoding preserves the measurement probabilities of the first `m` qubits**: measuring the
encoding of `ψ` gives first `m` bits in `S` with the probability that measuring `ψ` gives an
outcome in `S`. -/
theorem measureProb_realEncode (ψ : Qubits m) (S : Finset (Fin m → Bool)) :
    measureProb (realEncode ψ) (univ.filter fun z => Fin.init z ∈ S) = measureProb ψ S := by
  unfold measureProb
  have hS : ∑ y ∈ S, ‖ψ.ofLp y‖ ^ 2 = ∑ y, if y ∈ S then ‖ψ.ofLp y‖ ^ 2 else 0 := by
    rw [← sum_filter, filter_mem_eq_inter, univ_inter]
  rw [sum_filter, sum_bitString_succ, hS]
  refine sum_congr rfl fun x _ => ?_
  simp only [Fin.init_snoc]
  split_ifs with hx
  · rw [realEncode_apply_snoc, realEncode_apply_snoc, Complex.sq_norm (ψ.ofLp x),
      Complex.normSq_apply]
    simp only [Bool.false_eq_true, ite_false, ite_true, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
    ring
  · simp

/-! ### The real encoding of matrices -/

/-- **The real block of a matrix entry**: the entry `a` acts on the pair of real and imaginary
parts as `[[Re a, -Im a], [Im a, Re a]]`; the arguments are the encoding bits of the output (row)
and of the input (column). -/
noncomputable def realEntry (a : ℂ) : Bool → Bool → ℂ
  | false, false => (a.re : ℂ)
  | true, true => (a.re : ℂ)
  | true, false => (a.im : ℂ)
  | false, true => (-a.im : ℝ)

@[simp] theorem realEntry_false_false (a : ℂ) : realEntry a false false = (a.re : ℂ) := by
  simp only [realEntry]
@[simp] theorem realEntry_true_true (a : ℂ) : realEntry a true true = (a.re : ℂ) := by
  simp only [realEntry]
@[simp] theorem realEntry_true_false (a : ℂ) : realEntry a true false = (a.im : ℂ) := by
  simp only [realEntry]
@[simp] theorem realEntry_false_true (a : ℂ) : realEntry a false true = ((-a.im : ℝ) : ℂ) := by
  simp only [realEntry]

/-- The real block of a real entry is the entry on the diagonal. -/
theorem realEntry_of_im_eq_zero {a : ℂ} (ha : a.im = 0) (b c : Bool) :
    realEntry a b c = if b = c then a else 0 := by
  have hre : ((a.re : ℝ) : ℂ) = a := Complex.ext rfl (by simp [ha])
  cases b <;> cases c <;> simp [realEntry, hre, ha]

/-- **A matrix of real blocks acts on encoded states** as the original matrix acts on states. -/
theorem mulVec_realEncode {M' : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℂ}
    {M : Matrix (Fin m → Bool) (Fin m → Bool) ℂ}
    (h : ∀ z z', M' z z' =
      realEntry (M (Fin.init z) (Fin.init z')) (z (Fin.last m)) (z' (Fin.last m)))
    (ψ : Qubits m) :
    M' *ᵥ (realEncode ψ).ofLp = (realEncode (WithLp.toLp 2 (M *ᵥ ψ.ofLp))).ofLp := by
  funext z
  rw [realEncode_apply]
  simp only [mulVec, dotProduct]
  rw [sum_bitString_succ]
  simp only [h, Fin.init_snoc, Fin.snoc_last, realEncode_apply_snoc, Bool.false_eq_true, ite_false,
    ite_true]
  cases z (Fin.last m)
  · simp only [Bool.false_eq_true, ite_false, realEntry, Complex.re_sum, Complex.ofReal_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [Complex.mul_re]
    push_cast
    ring
  · simp only [ite_true, realEntry, Complex.im_sum, Complex.ofReal_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [Complex.mul_im]
    push_cast
    ring

/-! ### Simulation of circuits -/

namespace Circuit

/-- The circuit `C'` on `m + 1` qubits **simulates** the circuit `C` on `m` qubits **through the
real encoding**: it maps the encoding of every state to the encoding of its image under `C`. -/
def RealSimulates (C' : Circuit (m + 1)) (C : Circuit m) : Prop :=
  ∀ ψ, C'.eval (realEncode ψ) = realEncode (C.eval ψ)

/-- **A circuit whose unitary consists of the real blocks of another's simulates it.** -/
theorem realSimulates_of_matrix {C' : Circuit (m + 1)} {C : Circuit m}
    (h : ∀ z z' : Fin (m + 1) → Bool, (C'.matrix : Matrix _ _ ℂ) z z' =
      realEntry ((C.matrix : Matrix _ _ ℂ) (Fin.init z) (Fin.init z')) (z (Fin.last m))
        (z' (Fin.last m))) :
    C'.RealSimulates C := fun ψ => by
  ext z
  simp only [eval, unitaryEquiv_apply]
  exact congrFun (mulVec_realEncode h ψ) z

theorem RealSimulates.nil : RealSimulates ([] : Circuit (m + 1)) [] := fun ψ => by
  simp

/-- **Simulation of sequences**: running two simulating circuits in sequence simulates running the
simulated circuits in sequence. -/
theorem RealSimulates.append {C' D' : Circuit (m + 1)} {C D : Circuit m}
    (hC : C'.RealSimulates C) (hD : D'.RealSimulates D) : (C' ++ D').RealSimulates (C ++ D) :=
  fun ψ => by rw [eval_append, eval_append, hC, hD]

/-- **Simulation of runs**: a simulating circuit started in `|x 0⟩` ends in the encoding of the
final state of the simulated circuit started in `|x⟩`. -/
theorem RealSimulates.run_snoc_false {C' : Circuit (m + 1)} {C : Circuit m}
    (h : C'.RealSimulates C) (x : Fin m → Bool) :
    C'.run (Fin.snoc x false) = realEncode (C.run x) := by
  rw [run, run, ← realEncode_ket, h]

end Circuit

/-! ### Gates with real entries -/

namespace PlacedGate

/-- The entries of a gate placed on the first `m` of `m + 1` qubits: it leaves the last qubit
alone. -/
theorem matrix_mapWires_castSuccEmb (g : PlacedGate m) (z z' : Fin (m + 1) → Bool) :
    ((g.mapWires Fin.castSuccEmb).matrix : Matrix _ _ ℂ) z z' =
      if z (Fin.last m) = z' (Fin.last m) then (g.matrix : Matrix _ _ ℂ) (Fin.init z) (Fin.init z')
      else 0 := by
  have h : AgreeOff Fin.castSuccEmb z z' ↔ z (Fin.last m) = z' (Fin.last m) := by
    refine ⟨fun h => h _ fun i => Fin.castSucc_ne_last i, fun h j hj => ?_⟩
    obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last j
    · exact absurd rfl (hj j)
    · exact h
  rw [matrix_mapWires, if_congr h rfl rfl]
  rfl

/-- **A gate with real entries simulates itself** through the real encoding, placed on the same
qubits away from the encoding qubit. -/
theorem realSimulates_mapWires_castSuccEmb (g : PlacedGate m)
    (hg : ∀ y x, ((g.gate : Matrix (Fin g.arity → Bool) (Fin g.arity → Bool) ℂ) y x).im = 0) :
    Circuit.RealSimulates [g.mapWires Fin.castSuccEmb] [g] := by
  have hreal (y x : Fin m → Bool) : ((g.matrix : Matrix _ _ ℂ) y x).im = 0 := by
    rw [matrix_apply]
    split_ifs
    · exact hg _ _
    · rfl
  refine Circuit.realSimulates_of_matrix fun z z' => ?_
  simp only [Circuit.matrix_cons, Circuit.matrix_nil, one_mul]
  rw [matrix_mapWires_castSuccEmb, realEntry_of_im_eq_zero (hreal _ _)]

end PlacedGate

end Cslib.Quantum
