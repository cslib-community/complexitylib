/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.MonotoneCircuitValue
public import Complexity.Computability.Complexity.Problems.CircuitValue.Completeness
public import Complexity.Computability.Circuit.Monotone.DualRail

/-!
# The monotone circuit value problem is `P`-complete

**Goldschlager's theorem** [Goldschlager1977]: the monotone circuit value problem is `P`-complete
under logarithmic-space many-one reductions [Arora and Barak, Section 6.7][AroraBarak09].

A problem `A ∈ P enc` reduces to the circuit value problem by the tableau of its decider
(`Complexity/Computability/Complexity/Problems/CircuitValue/Completeness.lean`); the dual-rail
translation of the tableau
(`Cslib.Circuits.Monotone.dualRail`) is a monotone circuit computing the same function on the
dual-rail inputs, the constant `true` followed by each input bit and its negation. The reduction
maps an instance `a` to the dual-rail translation of the tableau for inputs of length
`n = |enc a|`, with the dual-rail inputs of `enc a`
(`Cslib.Complexity.MonotoneCircuitValue.dualTableauInstance`). It is computed in logarithmic space
by a writer (`Cslib.Complexity.CircuitValue.WriterSpec`) emitting, for each gate of the tableau,
its two translated gates, each computed from the number of the gate within work space linear in
the binary lengths of `n`, the time bound and the number. In particular the circuit value problem
reduces to the monotone circuit value problem in logarithmic space
(`Cslib.Complexity.MonotoneCircuitValue.circuitValue_logSpaceReducible`), through the tableau of
its decider rather than by translating the given circuit directly.

## Main definitions

* `Cslib.Complexity.MonotoneCircuitValue.dualTableauInstance`: the instance of the monotone
  problem for an input of a machine.

## Main results

* `Cslib.Complexity.MonotoneCircuitValue.computableInLogSpace_dualTableauInstance`: the instances
  are computable in logarithmic space.
* `Cslib.Complexity.MonotoneCircuitValue.logSpaceReducible_of_mem_P`: every problem in `P`
  reduces to monotone circuit value in logarithmic space.
* `Cslib.Complexity.MonotoneCircuitValue.logSpaceHard`,
  `Cslib.Complexity.MonotoneCircuitValue.logSpaceComplete`: the monotone circuit value problem is
  `P`-hard and `P`-complete under logarithmic-space reductions.
* `Cslib.Complexity.MonotoneCircuitValue.circuitValue_logSpaceReducible`: the circuit value
  problem reduces to the monotone one.
* `Cslib.Complexity.MonotoneCircuitValue.mem_L_iff_forall_P_eq_L`: the monotone circuit value
  problem is in `L` exactly when `P = L`.

## References

* [L. M. Goldschlager, *The monotone and planar circuit value problems are log space complete
  for P*][Goldschlager1977]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.7][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.MonotoneCircuitValue

open Turing MultiTapeTM Circuits Circuits.Boolean ComputableInSpace CircuitValue

/-! ### The translated gates in the De Morgan basis -/

/-- The operation of the gate translating a De Morgan operation positively (`b = true`) or
negatively, read in the De Morgan basis. -/
def dualOp (b : Bool) : Boolean.Op → Boolean.Op
  | .const c => .const (if b then c else !c)
  | .not => .or
  | .and => if b then .and else .or
  | .or => if b then .or else .and

/-- The gate translating a De Morgan gate positively (`b = true`) or negatively
(`Cslib.Circuits.Monotone.dualGates`), read in the De Morgan basis. -/
def dualGateDM (b : Bool) (g : Boolean.Op × List ℕ) : Boolean.Op × List ℕ :=
  (dualOp b g.1, if decide (Boolean.signature.Arity g.1 = 0) then []
    else if decide (g.1 = .not) then
      [Monotone.railWire (!b) (g.2.getD 0 0), Monotone.railWire (!b) (g.2.getD 0 0)]
    else [Monotone.railWire b (g.2.getD 0 0), Monotone.railWire b (g.2.getD 1 0)])

private theorem map_dualGates (g : Boolean.Op × List ℕ) :
    (Monotone.dualGates g).map (fun h => (Monotone.toDeMorgan h.1, h.2)) =
      [dualGateDM true g, dualGateDM false g] := by
  rcases g with ⟨(_ | _) | _ | _ | _, args⟩ <;> rfl

section

variable {α : Type} {encIn : α ↪ List Bool} {Bs : α → ℕ}

/-- **The translated gates within a budget**, from a gate within the budget. -/
private theorem dualGateDM_inSpace (b : Bool) {g : α → Boolean.Op × List ℕ}
    (hg : ComputableInSpace g encIn encGate Bs) (hin : (fun x => (encIn x).length) ≼ Bs) :
    ComputableInSpace (fun x => dualGateDM b (g x)) encIn encGate Bs := by
  have hop := fst' hg
  have hargs := snd' hg
  have ha := budget_headD 0 hargs
  have hb := budget_headD 0 (budget_tail hargs)
  have hrail (c : Bool) {w : α → ℕ} (hw : ComputableInSpace w encIn encNat Bs) :
      ComputableInSpace (fun x => Monotone.railWire c (w x)) encIn encNat Bs :=
    (budget_natAdd (budget_natMul (budget_const (encB := encNat) 2 hin) hw)
      (budget_const (encB := encNat) (if c then 1 else 2) hin)).of_enc_eq fun _ => rfl
  have hnil := budget_const (encB := encList encNat) ([] : List ℕ) hin
  have hcons {a : α → ℕ} {L : α → List ℕ} (ha : ComputableInSpace a encIn encNat Bs)
      (hL : ComputableInSpace L encIn (encList encNat) Bs) :=
    budget_cons ha hL
  have hargs' := budget_ite
    (budget_finite (encC := encBool) (fun op => decide (Boolean.signature.Arity op = 0)) hop) hnil
    (budget_ite (budget_finite (encC := encBool) (fun op : Boolean.Op => decide (op = .not)) hop)
      (hcons (hrail (!b) ha) (hcons (hrail (!b) ha) hnil))
      (hcons (hrail b ha) (hcons (hrail b hb) hnil)))
  refine (budget_prod (budget_finite (encC := encOp) (dualOp b) hop) hargs').of_enc_eq
    fun x => ?_
  have h₀ (l : List ℕ) : l.getD 0 0 = l.headD 0 := by cases l <;> rfl
  have h₁ (l : List ℕ) : l.getD 1 0 = l.tail.headD 0 := by rcases l with _ | ⟨_, _ | _⟩ <;> rfl
  simp only [dualGateDM, h₀, h₁]

end

/-! ### The instances -/

section Instance

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State) (C d : ℕ)

/-- **The instance of the monotone circuit value problem** for the input `w`: the dual-rail
translation of the tableau circuit of `tm` for `timeBound C d |w|` steps on inputs of length
`|w|`, with the dual-rail inputs of `w`. -/
noncomputable def dualTableauInstance (w : List Bool) :
    Σ n, Circuit Monotone.signature n 1 × BitString n :=
  ⟨2 * w.length + 1, Monotone.dualRail (Tableau.circuit tm w.length (timeBound C d w.length)),
    Monotone.railBitString fun i => w[i]⟩

/-- The dual-rail instance is a yes-instance exactly when the tableau instance is. -/
theorem mem_dualTableauInstance_iff (w : List Bool) :
    dualTableauInstance tm C d w ∈ MonotoneCircuitValue ↔
      tableauInstance tm C d w ∈ CircuitValue := by
  rw [mem_MonotoneCircuitValue, mem_CircuitValue]
  simp only [dualTableauInstance, tableauInstance]
  rw [Monotone.eval_dualRail]

/-- The two translated gates of gate `j` of the tableau, as the writer emits them. -/
noncomputable def dualChunk (n j : ℕ) : List Bool :=
  doubled (doubled (frame
    (encGate (dualGateDM true (Tableau.gateCode tm n (timeBound C d n) j))))) ++
    doubled (doubled (frame
      (encGate (dualGateDM false (Tableau.gateCode tm n (timeBound C d n) j)))))

/-- **The writer of the dual-rail instances.** -/
noncomputable def dualSpec : WriterSpec where
  countUnit := List.replicate 8 true
  countEnd := [true, true, true, true, true, false]
  numChunks n := Tableau.numGates k State (timeBound C d n)
  chunk := dualChunk tm C d
  trailer n := [true, false] ++
    doubled (frame (encNat (Monotone.railWire true
      (Tableau.outWire k State n (timeBound C d n))))) ++
      [false, true]
  copyBit b := [b, !b]

private theorem flatten_replicate_two_mul_add_one {β : Type*} (a : List β) (n : ℕ) :
    (List.replicate (2 * n + 1) a).flatten = (List.replicate n (a ++ a)).flatten ++ a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by omega, List.replicate_succ (n := 2 * n + 1 + 1),
      List.replicate_succ (n := 2 * n + 1), List.flatten_cons, List.flatten_cons, ih,
      List.replicate_succ (n := n), List.flatten_cons]
    simp only [List.append_assoc]

/-- **The encoded dual-rail instance** is the word written by the writer. -/
private theorem encMonotoneCircuitValue_dualTableauInstance (w : List Bool) :
    encMonotoneCircuitValue (dualTableauInstance tm C d w) = (dualSpec tm C d).output w := by
  rw [encMonotoneCircuitValue_apply, encCircuitValue_apply]
  simp only [toDeMorgan, dualTableauInstance, Circuit.code_mapOp, Monotone.code_dualRail,
    Tableau.code_circuit, Tableau.gates, encPair_apply, encUnary_apply, encBits_apply,
    Monotone.ofFn_railBitString, List.map_cons, List.map_nil, encList_cons, encList_nil,
    List.append_nil, frame_eq_doubled, doubled_append]
  have hw : List.ofFn (fun i : Fin w.length => w[i]) = w := List.ofFn_getElem
  rw [hw]
  rw [doubled_doubled_replicate, flatten_replicate_two_mul_add_one]
  have hcode (gs : List (Boolean.Op × List ℕ)) :
      doubled (doubled (encList encGate
        ((Monotone.dualCode gs).map fun g => (Monotone.toDeMorgan g.1, g.2)))) =
        (gs.map fun g => doubled (doubled (frame (encGate (dualGateDM true g)))) ++
          doubled (doubled (frame (encGate (dualGateDM false g))))).flatten := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      simp only [Monotone.dualCode, List.flatMap_cons, List.map_append]
      rw [map_dualGates g]
      simp only [List.cons_append, List.nil_append, encList_cons, doubled_append,
        List.map_cons, List.flatten_cons]
      simp only [Monotone.dualCode] at ih
      rw [ih]
      simp only [List.append_assoc]
  rw [hcode]
  simp only [WriterSpec.output, dualSpec, List.map_map, Function.comp_def]
  change _ = (List.replicate w.length (List.replicate 8 true)).flatten ++
    [true, true, true, true, true, false] ++
    ((List.range (Tableau.numGates k State (timeBound C d w.length))).map
      fun i => dualChunk tm C d w.length i).flatten ++
    ([true, false] ++ doubled (frame (encNat (Monotone.railWire true
      (Tableau.outWire k State w.length (timeBound C d w.length))))) ++ [false, true]) ++
    w.flatMap (fun b => [b, !b])
  simp [dualChunk, frame_eq_doubled, doubled_append, Monotone.railBits, List.append_assoc]

section Space

variable {α : Type} {encIn : α ↪ List Bool} {Bs : α → ℕ}
  (hin : (fun x => (encIn x).length) ≼ Bs)
include hin

private theorem dualChunk_inSpace {n j : α → ℕ}
    (hn : ComputableInSpace n encIn encNat Bs)
    (hj : ComputableInSpace j encIn encNat Bs) :
    ComputableInSpace (fun x => dualChunk tm C d (n x) (j x)) encIn encBits Bs := by
  have hg := Tableau.gateCode_inSpace tm hn (timeBound_inSpace C d hin hn) hin hj
  have hrail (b : Bool) := budget_comp_linear doubled_inSpace
    (budget_comp_linear doubled_inSpace
      (budget_comp_linear (ComputableInSpace.frame encGate) (dualGateDM_inSpace b hg hin)))
  exact ((hrail true).append (hrail false) (g := fun x => dualChunk tm C d (n x) (j x))
    (encD := encBits) fun _ => rfl).weaken (.add (.refl _) (.refl _))

private theorem dualTrailer_inSpace {n : α → ℕ}
    (hn : ComputableInSpace n encIn encNat Bs) :
    ComputableInSpace (fun x => (dualSpec tm C d).trailer (n x)) encIn encBits Bs := by
  have hT := timeBound_inSpace C d hin hn
  have ho : ComputableInSpace (fun x => Tableau.outWire k State (n x)
      (timeBound C d (n x))) encIn encNat Bs :=
    budget_natAdd (budget_natAdd (budget_natAdd hn (budget_const 2 hin))
      (budget_natMul hT (Tableau.blockSize_inSpace (k := k) (State := State) hT hin)))
      (budget_natAdd (Tableau.gfStart_inSpace (k := k) (State := State) hT hin)
        (budget_const _ hin))
  have hr : ComputableInSpace (fun x => Monotone.railWire true
      (Tableau.outWire k State (n x) (timeBound C d (n x)))) encIn encNat Bs :=
    budget_natAdd (budget_natMul (budget_const 2 hin) ho) (budget_const 1 hin)
  have hmid := budget_comp_linear doubled_inSpace
    (budget_comp_linear (ComputableInSpace.frame encNat) hr)
  have h₁ := (budget_const (encB := encBits) [true, false] hin).append hmid
    (g := fun x => [true, false] ++ doubled (Turing.MultiTapeTM.frame (encNat
      (Monotone.railWire true (Tableau.outWire k State (n x) (timeBound C d (n x)))))))
    (encD := encBits) fun _ => rfl
  exact ((h₁.weaken (.add (.refl _) (.refl _))).append
    (budget_const (encB := encBits) [false, true] hin)
    (g := fun x => (dualSpec tm C d).trailer (n x)) (encD := encBits)
    fun _ => rfl).weaken (.add (.refl _) (.refl _))

end Space

/-- The dual-rail tableau instances are computable in logarithmic space from framed inputs. -/
theorem computableInLogSpace_dualTableauInstance :
    ComputableInLogSpace (dualTableauInstance tm C d) (encFramed encBits)
      encMonotoneCircuitValue := by
  have hin : (fun p => (WriterSpec.encStepIn p).length) ≼ fun p => wBudget p.1 :=
    .of_le_linear 2 0 fun p => by
      simp only [length_encPair, encBool_apply, wBudget]
      simp only [encNat_apply, List.length_cons, List.length_nil, zero_add, add_zero,
        Order.add_one_le_iff]
      omega
  have hs := (ComputableInSpace.fst encNat3 encBool).weaken hin
  have hn := fst' (snd' hs)
  have hi := snd' (snd' hs)
  refine (dualSpec tm C d).computableInLogSpace
    (encMonotoneCircuitValue_dualTableauInstance tm C d)
    (numGates_inSpace (k := k) (State := State) hin (timeBound_inSpace C d hin hn))
    (dualChunk_inSpace tm C d hin hn hi) (dualTrailer_inSpace tm C d hin hn) ?_
  change PolynomiallyBounded fun n => Tableau.numGates k State (timeBound C d n)
  simp only [Tableau.numGates, Tableau.blockSize, Tableau.colStart, Tableau.gfStart,
    Tableau.globStart, Tableau.numCols, timeBound]
  fun_prop

end Instance

/-- Every problem in `P` reduces to monotone circuit value in logarithmic space, by the
positive and negative rails of its decider's tableau. -/
theorem logSpaceReducible_of_mem_P {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ P enc) : LogSpaceReducible enc encMonotoneCircuitValue A MonotoneCircuitValue := by
  obtain ⟨f, hfpoly, hAf⟩ := hA
  obtain ⟨t, _, ht, -, k, State, hfin, tm, htm⟩ := hfpoly
  have := Fintype.ofFinite State
  classical
  obtain ⟨C, d, htle⟩ := polynomiallyBounded_iff_le.mp ht
  refine ⟨fun a => dualTableauInstance tm C d (enc a),
    (computableInLogSpace_dualTableauInstance tm C d).comp (computableInLogSpace_frame enc),
    fun a => ?_⟩
  rw [mem_dualTableauInstance_iff, hAf a, mem_CircuitValue]
  simp only [tableauInstance]
  have hw : List.ofFn (fun i : Fin (enc a).length => (enc a)[i]) = enc a := List.ofFn_getElem
  rw [Tableau.eval_circuit tm (by simp only [timeBound]; omega), hw]
  have hle : t (enc a).length ≤ timeBound C d (enc a).length := by
    have := htle (enc a).length
    simp only [timeBound]
    omega
  obtain ⟨-, hout⟩ := (htm a).runFrom_of_le hle
  rw [hout, encBool_apply]
  cases f a <;> simp [OutView.ofList]

/-- Monotone circuit value is `P`-hard under logarithmic-space reductions [Goldschlager1977]. -/
theorem logSpaceHard : LogSpaceHard @P encMonotoneCircuitValue MonotoneCircuitValue :=
  fun _ _ _ hA => logSpaceReducible_of_mem_P hA

/-- Monotone circuit value is `P`-complete under logarithmic-space reductions [Goldschlager1977]. -/
theorem logSpaceComplete : LogSpaceComplete @P encMonotoneCircuitValue MonotoneCircuitValue :=
  ⟨mem_P, logSpaceHard⟩

/-- General circuit value reduces to monotone circuit value in logarithmic space. -/
theorem circuitValue_logSpaceReducible :
    LogSpaceReducible encCircuitValue encMonotoneCircuitValue CircuitValue MonotoneCircuitValue :=
  logSpaceReducible_of_mem_P CircuitValue.mem_P

/-- Monotone circuit value is in `L` exactly when `P = L`, for every encoding of instances. -/
theorem mem_L_iff_forall_P_eq_L :
    MonotoneCircuitValue ∈ L encMonotoneCircuitValue ↔
      ∀ {α : Type} (enc : α ↪ List Bool), P enc = L enc := by
  constructor
  · intro h α enc
    ext A
    exact ⟨fun hA => (logSpaceReducible_of_mem_P hA).mem_L h, fun hA => L_subset_P hA⟩
  · intro h
    rw [← h]
    exact mem_P

end Cslib.Complexity.MonotoneCircuitValue
