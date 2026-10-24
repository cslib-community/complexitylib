/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CircuitValue
public import Complexity.Computability.Complexity.Classes.LogSpace
public import Complexity.Computability.Circuit.Boolean.Tableau.Correct
public import Complexity.Computability.Circuit.Boolean.Tableau.Space
public import Complexity.Computability.Complexity.Problems.CircuitValue.Writer
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Mathlib.Data.List.GetD
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# The circuit value problem is `P`-complete

Ladner proved [Ladner1975] that the circuit value problem is `P`-complete under
logarithmic-space many-one reductions [Arora and Barak, Section 6.7][AroraBarak09],
[Papadimitriou, Theorem 8.1][Papadimitriou94].

A problem `A ∈ P enc` is decided by a machine `tm` within `C (n + 1) ^ d` steps on encoded
instances of length `n`. The reduction maps an instance `a` to the tableau circuit of `tm` for
`C (n + 1) ^ d + n + 1` steps on inputs of length `n = |enc a|`
(`Cslib.Circuits.Boolean.Tableau.circuit`), together with the input `enc a`. The circuit outputs
whether `tm`, started on `enc a`, has written exactly `[true]` after that many steps
(`Cslib.Circuits.Boolean.Tableau.eval_circuit`); since `tm` has halted by then with the answer on
its output, this is whether `a ∈ A`. The circuit reads the bits of `enc a` as its inputs; it does
not hardwire them as constants. The reduction is
computable in logarithmic space: a read machine (`Turing.ReadMachine`) on the framed input counts
its length `n`, then writes the gates one by one, keeping only the number of the current gate,
since each gate is computed from its number within work space linear in the binary lengths of `n`,
the time bound and the number (`Cslib.Circuits.Boolean.Tableau.gateCode_inSpace`), and finally
copies the input.

## Main definitions

* `Cslib.Complexity.CircuitValue.tableauInstance`: the instance of the circuit value problem for
  an input of a machine.
* `Cslib.Complexity.CircuitValue.writer`: the read machine writing the instance.
* `Cslib.Complexity.CircuitValue.tableauCode`: the circuit code, with all input wires free.

## Main results

* `Cslib.Complexity.CircuitValue.run_writer`: the writer writes the encoded instance.
* `Cslib.Complexity.CircuitValue.computableInLogSpace_tableauInstance`: the instances are
  computable in logarithmic space.
* `Cslib.Complexity.CircuitValue.computableInPolyTime_tableauCode`: the whole code is
  constructed in polynomial time from the unary input length.
* `Cslib.Complexity.CircuitValue.exists_uniformCircuits`: polynomial-time Boolean functions
  admit polynomial-time circuit constructors, correct on the encoding's image.
* `Cslib.Complexity.CircuitValue.logSpaceHard`: the circuit value problem is `P`-hard under
  logarithmic-space reductions.
* `Cslib.Complexity.CircuitValue.logSpaceComplete`: the circuit value problem is `P`-complete
  under logarithmic-space reductions.
* `Cslib.Complexity.CircuitValue.mem_L_iff_forall_P_eq_L`: the circuit value problem is in `L`
  exactly when `P = L`.

## References

* [R. E. Ladner, *The circuit value problem is log space complete for P*][Ladner1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Sections 6.1 and 6.7][AroraBarak09]
* [C. H. Papadimitriou, *Computational Complexity*, Theorem 8.1][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing MultiTapeTM Circuits Circuits.Boolean

namespace CircuitValue

/-! ### The writer -/

section Writer

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State) (C d : ℕ)

/-- The number of steps of the tableau for inputs of length `n`: `C (n + 1) ^ d + n + 1`. -/
def timeBound (C d n : ℕ) : ℕ := C * (n + 1) ^ d + n + 1

/-- **The instance of the circuit value problem** for the input `w`: the tableau circuit of `tm`
for `timeBound C d |w|` steps on inputs of length `|w|`, with the input `w`. -/
noncomputable def tableauInstance (w : List Bool) : Σ n, Circuit signature n 1 × BitString n :=
  ⟨w.length, Tableau.circuit tm w.length (timeBound C d w.length), fun i => w[i]⟩

/-- Gate `i` of the tableau, as the writer emits it. -/
noncomputable def gateChunk (n i : ℕ) : List Bool :=
  doubled (doubled (frame (encGate (Tableau.gateCode tm n (timeBound C d n) i))))

variable (k State) in
/-- What the writer emits after the gates: the end of the gate list and the output wire. -/
noncomputable def trailer (n : ℕ) : List Bool :=
  [true, false] ++ doubled (frame (encNat (Tableau.outWire k State n (timeBound C d n)))) ++ [false]

/-- **The encoded instance**: the length in unary, the gates and the output wire, framed twice,
and the input. -/
theorem encCircuitValue_tableauInstance (w : List Bool) :
    encCircuitValue (tableauInstance tm C d w) =
      (List.replicate w.length [true, true, true, true]).flatten ++ [true, false] ++
        ((List.range (Tableau.numGates k State (timeBound C d w.length))).map
          (gateChunk tm C d w.length)).flatten ++ trailer k State C d w.length ++ w := by
  rw [encCircuitValue_apply]
  simp only [tableauInstance, Tableau.code_circuit, encPair_apply, encUnary_apply, encList_cons,
    encList_nil, List.append_nil, encBits_apply, frame_eq_doubled, doubled_append, Tableau.gates,
    trailer]
  have hw : List.ofFn (fun i : Fin w.length => w[i]) = w := List.ofFn_getElem
  rw [hw, doubled_doubled_replicate]
  have hl : encList encGate ((List.range (Tableau.numGates k State (timeBound C d w.length))).map
      (Tableau.gateCode tm w.length (timeBound C d w.length))) =
      ((List.range (Tableau.numGates k State (timeBound C d w.length))).map fun i =>
        frame (encGate (Tableau.gateCode tm w.length (timeBound C d w.length) i))).flatten := by
    generalize List.range (Tableau.numGates k State (timeBound C d w.length)) = L
    induction L with
    | nil => rfl
    | cons i L ih => simp [ih]
  have hc : gateChunk tm C d w.length = fun i =>
      doubled (doubled (doubled
        (encGate (Tableau.gateCode tm w.length (timeBound C d w.length) i)))) ++
        doubled (doubled [false]) := by
    funext i
    simp only [gateChunk, frame_eq_doubled, doubled_append]
  rw [hl, doubled_flatten, doubled_flatten, List.map_map, List.map_map, hc]
  simp only [frame_eq_doubled, Function.comp_def, doubled_append, List.append_assoc, doubled_false]

/-- The uniform writer specification for tableau circuit instances. -/
noncomputable def tableauSpec : WriterSpec where
  countUnit := [true, true, true, true]
  countEnd := [true, false]
  numChunks n := Tableau.numGates k State (timeBound C d n)
  chunk := gateChunk tm C d
  trailer := trailer k State C d
  copyBit b := [b]

/-- **The writer** of encoded tableau instances, on framed inputs. -/
noncomputable def writer : ReadMachine (ℕ × ℕ × ℕ) := (tableauSpec tm C d).machine

/-- The number of steps of the writer on an input of length `n`. -/
def writerRounds (n : ℕ) : ℕ :=
  (n + 1) + (Tableau.numGates k State (timeBound C d n) + 1) + (n + 1)

private theorem tableauSpec_output (w : List Bool) :
    encCircuitValue (tableauInstance tm C d w) = (tableauSpec tm C d).output w := by
  rw [encCircuitValue_tableauInstance]
  simp [WriterSpec.output, tableauSpec]

/-- The writer halts with the encoded tableau instance. -/
theorem run_writer (w : List Bool) :
    (writer tm C d).run (frame w) (writerRounds (k := k) (State := State) C d w.length) =
      ⟨(3, w.length, 0), encCircuitValue (tableauInstance tm C d w)⟩ := by
  rw [tableauSpec_output]
  exact (tableauSpec tm C d).run_machine w


end Writer

/-! ### The writer in logarithmic space -/

section Space

open ComputableTidilyInSpace Tableau

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State) (C d : ℕ)

section Components

variable {α : Type} {encIn : α ↪ List Bool} {Bs : α → ℕ}
  (hin : (fun x => (encIn x).length) ≼ Bs)
include hin

/-- Evaluating the fixed polynomial tableau time bound preserves a space budget. -/
theorem timeBound_inSpace {n : α → ℕ} (hn : ComputableInSpace n encIn encNat Bs) :
    ComputableInSpace (fun x => timeBound C d (n x)) encIn encNat Bs := by
  have hn := hn.tidy
  exact .of_tidy (budget_natAdd (budget_natAdd (budget_natMul (budget_const C hin)
    (budget_natPow (budget_natAdd hn (budget_const 1 hin)) hin d)) hn) (budget_const 1 hin))

omit [DecidableEq State] in
/-- Computing the tableau gate count preserves a space budget. -/
theorem numGates_inSpace {T : α → ℕ} (hT : ComputableInSpace T encIn encNat Bs) :
    ComputableInSpace (fun x => numGates k State (T x)) encIn encNat Bs := by
  have hT := hT.tidy
  exact .of_tidy
    (budget_natAdd (budget_const 2 hin) (budget_natMul (budget_natAdd hT (budget_const 1 hin))
    (blockSize_inSpace (k := k) (State := State) (.of_tidy hT) hin).tidy))

private theorem gateChunk_inSpace {n i : α → ℕ} (hn : ComputableTidilyInSpace n encIn encNat Bs)
    (hi : ComputableTidilyInSpace i encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => gateChunk tm C d (n x) (i x)) encIn encBits Bs := by
  have hframe : ComputableTidilyInSpace (fun g => frame (encGate g)) encGate encBits
      fun g => (encGate g).length :=
    of_inO (.of_linear (.of_frame fun _ => rfl))
  exact budget_comp_linear doubled_inSpace (budget_comp_linear doubled_inSpace
    (budget_comp_linear (g := fun g => frame (encGate g)) hframe
      (gateCode_inSpace tm (.of_tidy hn) (timeBound_inSpace C d hin (.of_tidy hn)) hin
        (.of_tidy hi)).tidy))

omit [DecidableEq State] in
private theorem trailer_inSpace {n : α → ℕ} (hn : ComputableTidilyInSpace n encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => trailer k State C d (n x)) encIn encBits Bs := by
  have hT := (timeBound_inSpace C d hin (.of_tidy hn)).tidy
  have ho : ComputableTidilyInSpace (fun x => outWire k State (n x) (timeBound C d (n x)))
      encIn encNat Bs :=
    budget_natAdd (budget_natAdd (budget_natAdd hn (budget_const 2 hin))
      (budget_natMul hT (blockSize_inSpace (k := k) (State := State) (.of_tidy hT) hin).tidy))
      (budget_natAdd (gfStart_inSpace (k := k) (State := State) (.of_tidy hT) hin).tidy
        (budget_const _ hin))
  have hframe : ComputableTidilyInSpace (fun m => frame (encNat m)) encNat encBits
      fun m => (encNat m).length :=
    of_inO (.of_linear (.of_frame fun _ => rfl))
  have hmid := budget_comp_linear doubled_inSpace
    (budget_comp_linear (g := fun m => frame (encNat m)) hframe ho)
  have h₁ := (budget_const (encB := encBits) [true, false] hin).append hmid
    (g := fun x => [true, false] ++ doubled (frame (encNat (outWire k State (n x)
      (timeBound C d (n x)))))) (encD := encBits) fun _ => rfl
  have h₂ := (h₁.weaken (.add (.refl _) (.refl _))).append
    (budget_const (encB := encBits) [false] hin) (encD := encBits)
    (g := fun x => trailer k State C d (n x)) fun _ => rfl
  exact h₂.weaken (.add (.refl _) (.refl _))

end Components

attribute [local fun_prop] ComputableInPolySpace.tidy in
attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- **The instances are computable in logarithmic space**, from the framed input. -/
theorem computableInLogSpace_tableauInstance :
    ComputableInLogSpace (tableauInstance tm C d) (encFramed encBits) encCircuitValue := by
  have hin : (fun p => (WriterSpec.encStepIn p).length) ≼ fun p => wBudget p.1 :=
    .of_le_linear 2 0 fun p => by
      simp only [length_encPair, encBool_apply, wBudget]
      simp only [encNat_apply, List.length_cons, List.length_nil, zero_add, add_zero,
        Order.add_one_le_iff]
      omega
  have hs := (ComputableTidilyInSpace.fst encWState encBool).weaken hin
  have hn := fst' (snd' hs)
  have hi := snd' (snd' hs)
  refine (tableauSpec tm C d).computableInLogSpace (tableauSpec_output tm C d)
    (numGates_inSpace (k := k) (State := State) hin (timeBound_inSpace C d hin (.of_tidy hn)))
    (.of_tidy (gateChunk_inSpace tm C d hin hn hi))
    (.of_tidy (trailer_inSpace (k := k) (State := State) C d hin hn)) ?_
  change PolynomiallyBounded fun n => numGates k State (timeBound C d n)
  simp only [numGates, blockSize, colStart, gfStart, globStart, numCols, timeBound]
  fun_prop

end Space

/-! ### Constructing circuit codes -/

section Construction

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State) (C d : ℕ)

/-- The tableau code for inputs of length `n`. The input wires remain free; the constructor
receives only the length, in unary, rather than any assignment to those wires. -/
noncomputable def tableauCode (n : ℕ) : List (Op × List ℕ) × List ℕ :=
  (Tableau.circuit tm n (timeBound C d n)).code

/-- Writing the tableau code takes polynomial time in the unary input length. This reuses the
certified logarithmic-space writer and discards its dummy input assignment. -/
theorem computableInPolyTime_tableauCode :
    ComputableInPolyTime (tableauCode tm C d) encUnary encCode := by
  refine .of_tidy ?_
  have hwriter := (computableInLogSpace_tableauInstance tm C d).computableTidilyInPolyTime
  have hcode := ComputableTidilyInPolyTime.dropFrame.comp
    (ComputableTidilyInPolyTime.unframe.comp hwriter.encoded)
  have hframe : ComputableTidilyInPolyTime (fun w : List Bool => w)
      encBits (encFramed encBits) :=
    .of_linear (.of_frame fun _ => rfl)
  refine (hcode.comp (hframe.comp (ComputableTidilyInPolyTime.bitsReplicate false))).of_enc_eq
    fun n => ?_
  simp [tableauCode, tableauInstance, encCircuitValue_apply, encPair_apply,
    unframe_frame_append, dropFrame_frame_append, Tableau.code_circuit, List.length_replicate]

/-- Every polynomial-time Boolean function has circuits whose codes are constructed in
polynomial time from the unary encoded input length. Correctness is required on the encoding's
image; no decoder or efficient membership test for that image is assumed. -/
theorem exists_uniformCircuits {α : Type} {enc : α ↪ List Bool} {f : α → Bool}
    (hf : ComputableInPolyTime f enc encBool) :
    ∃ circuits : (n : ℕ) → Circuit signature n 1,
      ComputableInPolyTime (fun n => (circuits n).code) encUnary encCode ∧
      ∀ a, (circuits (enc a).length).eval interpretation (fun i => (enc a)[i]) 0 = f a := by
  have hf := hf.tidy
  have this : ∃ circuits : (n : ℕ) → Circuit signature n 1, ComputableTidilyInPolyTime
      (fun n => (circuits n).code) encUnary encCode ∧ ∀ a, (circuits (enc a).length).eval
      interpretation (fun i => (enc a)[i]) 0 = f a := by
    obtain ⟨t, s, ht, -, tapes, Control, hfin, machine, hmachine⟩ := hf
    have := Fintype.ofFinite Control
    classical
    obtain ⟨C, d, hbound⟩ := ht.exists_le
    refine ⟨fun n => Tableau.circuit machine n (timeBound C d n),
      (computableInPolyTime_tableauCode machine C d).tidy, fun a => ?_⟩
    rw [Tableau.eval_circuit machine (by simp only [timeBound]; omega)]
    have hw : List.ofFn (fun i : Fin (enc a).length => (enc a)[i]) = enc a := List.ofFn_getElem
    rw [hw]
    obtain ⟨hhalt, hout⟩ := ComputesTidilyInTimeAndSpace.runFrom_initCfg (hmachine a)
    have hle : t a ≤ timeBound C d (enc a).length := by
      have h := hbound a
      dsimp only [timeBound]
      omega
    rw [MultiTapeTM.runFrom_eq_of_halt machine _ hle hhalt, hout, encBool_apply]
    cases f a <;> simp [OutView.ofList]
  simpa only [computableInPolyTime_iff_computableTidilyInPolyTime] using this

end Construction

/-! ### `P`-completeness -/

/-- **Every problem in `P` reduces to the circuit value problem in logarithmic space**: an
instance is mapped to the tableau circuit of a polynomial-time decider on inputs of the length of
the encoded instance, with the encoded instance as its input. -/
theorem logSpaceReducible_of_mem_P {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ P enc) : LogSpaceReducible enc encCircuitValue A CircuitValue := by
  obtain ⟨f, hfpoly, hAf⟩ := hA
  obtain ⟨t, s, ht, -, k, State, hfin, tm, htm⟩ := hfpoly.tidy
  have := Fintype.ofFinite State
  classical
  obtain ⟨C, d, htle⟩ := ht.exists_le
  refine ⟨fun a => tableauInstance tm C d (enc a),
    (computableInLogSpace_tableauInstance tm C d).comp (computableInLogSpace_frame enc),
    fun a => ?_⟩
  rw [hAf a, mem_CircuitValue]
  simp only [tableauInstance]
  have hw : List.ofFn (fun i : Fin (enc a).length => (enc a)[i]) = enc a := List.ofFn_getElem
  rw [Tableau.eval_circuit tm (by simp only [timeBound]; omega), hw]
  obtain ⟨hhalt, hout⟩ := ComputesTidilyInTimeAndSpace.runFrom_initCfg (htm a)
  have hle : t a ≤ timeBound C d (enc a).length := by
    have := htle a
    simp only [timeBound]
    omega
  rw [MultiTapeTM.runFrom_eq_of_halt tm _ hle hhalt, hout, encBool_apply]
  cases f a <;> simp [OutView.ofList]

/-- **The circuit value problem is `P`-hard under logarithmic-space reductions** [Ladner1975]. -/
theorem logSpaceHard : LogSpaceHard @P encCircuitValue CircuitValue :=
  fun _ _ _ hA => logSpaceReducible_of_mem_P hA

/-- **The circuit value problem is `P`-complete under logarithmic-space
reductions** [Ladner1975], [Arora and Barak, Section 6.7][AroraBarak09]. -/
theorem logSpaceComplete : LogSpaceComplete @P encCircuitValue CircuitValue :=
  ⟨mem_P, logSpaceHard⟩

/-- **The circuit value problem is in `L` exactly when `P = L`**, for every encoding of instances
[Arora and Barak, Section 6.7][AroraBarak09]. -/
theorem mem_L_iff_forall_P_eq_L :
    CircuitValue ∈ L encCircuitValue ↔ ∀ {α : Type} (enc : α ↪ List Bool), P enc = L enc := by
  constructor
  · intro h α enc
    ext A
    exact ⟨fun hA => (logSpaceReducible_of_mem_P hA).mem_L h, fun hA => L_subset_P hA⟩
  · intro h
    rw [← h]
    exact mem_P

end CircuitValue

end Cslib.Complexity
