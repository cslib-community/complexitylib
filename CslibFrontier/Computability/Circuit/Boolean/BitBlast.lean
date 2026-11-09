/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Synthesis
public import CslibFrontier.Computability.Circuit.Synthesis
public import Cslib.Computability.Circuit.Full

/-!
# Bit-blasting circuits over a finite carrier

Let `enc : F ≃ BitString w` encode the elements of a carrier `F` by `w` bits. A circuit over the
full binary basis of `F` (`fullInterpretation (k := 2)`, where every constant and every operation
with at most two arguments is a gate) is simulated by a De Morgan circuit on the encodings: each
gate is replaced by `w` circuits, one for each bit of its value, each a function of the `2 * w`
bits of the gate's arguments and so computable with `2 ^ (2 * w) * (4 * w + 2) + 1` gates by its
disjunctive normal form (`Cslib.Circuits.Synthesis.selected`). A gate of the full basis therefore
costs at most `bitBlastCost w = w * (2 ^ (2 * w) * (4 * w + 2) + 1)` De Morgan gates. For a field
`F` with `q = 2 ^ w` elements this is `O(w ^ 2 * q ^ 2)` gates per field operation, a polynomial
in `q`, which suffices for reconstruction arguments whose circuits are polynomial in `q` anyway.

The simulation is stated as a synthesis bound (`Cslib.Circuits.Synthesis.bitBlast`): if the bits
of the `F`-valued functions feeding the circuit's inputs are available, then the bits of all its
outputs can be made available with `size * bitBlastCost w` further gates.

## Main definitions

* `Cslib.Circuits.bitsOf`: the bits of an `F`-valued function under an encoding.
* `Cslib.Circuits.bitBlastCost`: the De Morgan cost of one gate of the full binary basis.

## Main results

* `Cslib.Circuits.Synthesis.bitBlast_program`: the bits of every wire of a program over the full
  binary basis.
* `Cslib.Circuits.Synthesis.bitBlast`: the bits of every output of a circuit over the full binary
  basis.
* `Cslib.Circuits.Synthesis.bitBlast_synthesis`: the same for a synthesis bound over the full
  binary basis.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
-/

@[expose] public section

namespace Cslib.Circuits

open Boolean

variable {F : Type*} {w n : ℕ}

/-- The `j`-th bit, under the encoding `enc`, of an `F`-valued function `φ` of the inputs. -/
def bitsOf (enc : F ≃ BitString w) (φ : (Fin n → Bool) → F) (j : Fin w) : BooleanFunction n :=
  fun x => enc (φ x) j

/-- The number of De Morgan gates that simulate one gate of the full binary basis on `w`-bit
symbols: each of the `w` bits of the value is a function of the `2 * w` bits of the arguments. -/
def bitBlastCost (w : ℕ) : ℕ := w * (2 ^ (2 * w) * (4 * w + 2) + 1)

namespace Synthesis

/-- One bit of a gate of the full binary basis, as a Boolean function of the bits of the gate's
arguments, costs at most `2 ^ (2 * w) * (4 * w + 2) + 1` gates on top of these bits. -/
private theorem bitBlast_gateBit (enc : F ≃ BitString w) {s : Set (BooleanFunction n)}
    (op : FullOp 2 F) (args : Fin ((fullSignature 2 F).Arity op) → (Fin n → Bool) → F)
    (hargs : ∀ a j, bitsOf enc (args a) j ∈ s) (j : Fin w) :
    Synthesis interpretation s
      {bitsOf enc (fun x => fullInterpretation op fun a => args a x) j}
      (2 ^ (2 * w) * (4 * w + 2) + 1) := by
  have hk : (fullSignature 2 F).Arity op ≤ 2 := by
    rcases op with _ | _ <;> simp [fullSignature]
  let ψ : BooleanFunction ((fullSignature 2 F).Arity op * w) := fun y =>
    enc (fullInterpretation op fun a => enc.symm fun j' => y (finProdFinEquiv (a, j'))) j
  obtain ⟨c, hc, hsize⟩ := (selected (n := (fullSignature 2 F).Arity op * w) id ψ).exists_circuit
  have h := Synthesis.circuit (I := interpretation) c
    (fun idx => bitsOf enc (args (finProdFinEquiv.symm idx).1) (finProdFinEquiv.symm idx).2)
    (fun idx => hargs _ _)
  refine h.mono Set.Subset.rfl (Set.singleton_subset_iff.2 ⟨0, ?_⟩) (hsize.trans ?_)
  · funext x
    refine (congrFun (hc _) 0).trans ?_
    simp only [single_apply, Function.comp_id, ψ, bitsOf, Equiv.symm_apply_apply]
  · have hkw : (fullSignature 2 F).Arity op * w ≤ 2 * w := Nat.mul_le_mul_right w hk
    have hpow : 2 ^ ((fullSignature 2 F).Arity op * w) ≤ 2 ^ (2 * w) :=
      Nat.pow_le_pow_right (by decide) hkw
    have : 2 * ((fullSignature 2 F).Arity op * w) + 2 ≤ 4 * w + 2 := by omega
    exact Nat.add_le_add_right (Nat.mul_le_mul hpow this) 1

/-- **Bit-blasting a program.** If the bits of the functions `φ i` feeding the inputs of a
program over the full binary basis of `F` are available, then the bits of the values of all its
wires can be made available with `bitBlastCost w` De Morgan gates for each of its gates. -/
theorem bitBlast_program (enc : F ≃ BitString w) {s : Set (BooleanFunction n)} {N g : ℕ}
    (p : Program (fullSignature 2 F) N g) (φ : Fin N → (Fin n → Bool) → F)
    (hφ : ∀ i j, bitsOf enc (φ i) j ∈ s) :
    Synthesis interpretation s
      (Set.range fun wj : Wire N g × Fin w =>
        bitsOf enc (fun x => p.trace fullInterpretation (fun i => φ i x) wj.1) wj.2)
      (g * bitBlastCost w) := by
  induction p with
  | empty =>
    rw [zero_mul]
    refine of_subset ?_
    rintro _ ⟨⟨wire, j⟩, rfl⟩
    cases wire with
    | input i => exact hφ i j
    | gate j' => exact j'.elim0
  | @gate g p line ih =>
    let T : Set (BooleanFunction n) := Set.range fun wj : Wire N g × Fin w =>
      bitsOf enc (fun x => p.trace fullInterpretation (fun i => φ i x) wj.1) wj.2
    have hnew : Synthesis interpretation (s ∪ T)
        (Set.range fun j => bitsOf enc (fun x => line.eval fullInterpretation (fun i => φ i x)
          (p.eval fullInterpretation fun i => φ i x)) j) (bitBlastCost w) := by
      have := family (I := interpretation) (s := s ∪ T)
        (fun j => bitsOf enc (fun x => line.eval fullInterpretation (fun i => φ i x)
          (p.eval fullInterpretation fun i => φ i x)) j)
        (fun _ => 2 ^ (2 * w) * (4 * w + 2) + 1)
        (fun j => bitBlast_gateBit enc line.op
          (fun a x => p.trace fullInterpretation (fun i => φ i x) (line.wires a))
          (fun a j' => Set.mem_union_right s (⟨(line.wires a, j'), rfl⟩ : _ ∈ T)) j)
      simpa [bitBlastCost, Finset.sum_const, Finset.card_univ, Fintype.card_fin] using this
    refine (ih.comp hnew).mono Set.Subset.rfl ?_ (by rw [Nat.succ_mul])
    rintro _ ⟨⟨wire, j⟩, rfl⟩
    induction wire using Wire.lastCases with
    | last =>
      refine Set.mem_union_right _ ⟨j, ?_⟩
      funext x
      simp only [bitsOf, Program.trace_gateWire, Program.gateFunction_gate_last]
    | castSucc wire =>
      refine Set.mem_union_left _ ⟨(wire, j), ?_⟩
      funext x
      simp only [bitsOf, Program.trace_gate_castSucc]

/-- **Bit-blasting a circuit.** If the bits of the functions `φ i` feeding the inputs of a circuit
over the full binary basis of `F` are available, then the bits of all its outputs can be made
available with `c.size * bitBlastCost w` De Morgan gates. -/
theorem bitBlast (enc : F ≃ BitString w) {s : Set (BooleanFunction n)} {N M : ℕ}
    (c : Circuit (fullSignature 2 F) N M) (φ : Fin N → (Fin n → Bool) → F)
    (hφ : ∀ i j, bitsOf enc (φ i) j ∈ s) :
    Synthesis interpretation s
      (Set.range fun oj : Fin M × Fin w =>
        bitsOf enc (fun x => c.eval fullInterpretation (fun i => φ i x) oj.1) oj.2)
      (c.size * bitBlastCost w) := by
  refine (bitBlast_program enc c.program φ hφ).mono Set.Subset.rfl ?_ le_rfl
  rintro _ ⟨⟨o, j⟩, rfl⟩
  exact ⟨(c.outputs o, j), rfl⟩

/-- **Bit-blasting a synthesis bound.** If a family `Ψ` of functions of `N` field inputs is
synthesized over the full binary basis from the input projections with `cost` gates, and the bits
of the functions `φ i` feeding the inputs are available, then the bits of all `Ψ o (φ ·)` can be
made available with `cost * bitBlastCost w` De Morgan gates. -/
theorem bitBlast_synthesis (enc : F ≃ BitString w) {N : ℕ} {ι : Type*} [Finite ι]
    (Ψ : ι → (Fin N → F) → F) {cost : ℕ}
    (h : Synthesis (fullInterpretation (k := 2)) (inputs N) (Set.range Ψ) cost)
    {s : Set (BooleanFunction n)} (φ : Fin N → (Fin n → Bool) → F)
    (hφ : ∀ i j, bitsOf enc (φ i) j ∈ s) :
    Synthesis interpretation s
      (Set.range fun oj : ι × Fin w => bitsOf enc (fun x => Ψ oj.1 (fun i => φ i x)) oj.2)
      (cost * bitBlastCost w) := by
  classical
  have := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  have h' : Synthesis (fullInterpretation (k := 2)) (inputs N)
      (Set.range fun j => Ψ (e.symm j)) cost :=
    h.mono Set.Subset.rfl (by rintro _ ⟨j, rfl⟩; exact ⟨_, rfl⟩) le_rfl
  obtain ⟨c, hc, hsize⟩ := h'.exists_circuit_outputs
  refine (bitBlast enc c φ hφ).mono Set.Subset.rfl ?_ (Nat.mul_le_mul_right _ hsize)
  rintro _ ⟨⟨o, j⟩, rfl⟩
  refine ⟨(e o, j), ?_⟩
  funext x
  simp only [bitsOf]
  rw [hc (fun i => φ i x)]
  simp only [e.symm_apply_apply]

end Synthesis

end Cslib.Circuits
