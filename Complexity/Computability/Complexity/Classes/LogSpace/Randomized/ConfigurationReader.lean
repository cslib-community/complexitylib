/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace.Randomized.ConfigurationMatrix
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.FairCoin
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Injective

/-!
# Reading the fair-coin configuration matrix from compact IDs

The native compact-ID query `coinCountWithSymbol` agrees with the actual configuration matrix of
`MultiTapePTM`, counting both coins even when they select the same successor. Its live variant
agrees with the live configuration matrix. The correspondence uses the original input only at
the compact graph's `queryIndex`.

For views reachable under a logarithmic space bound, the prescribed polynomial radix fits every
view and the output is already summarized. The final two corollaries derive these representation
conditions from the machine's space bound and reachability, so they apply to the reachable-view
sets in `exists_configMatrix_of_mem_BPL`.

The count matrix gives halted views an absorbing edge of multiplicity two. The live matrix gives
halted views a zero row. These are the two conventions of `ConfigurationMatrix`, and do not assert
that halted executions consume further coins. This module supplies local access with the native
space certificates of `ConfigurationGraph.FairCoin`; bounded enumeration, time layering and the
full estimator remain separate constructions.

## Main results

* `Turing.MultiTapePTM.viewStep_withCoin_iff`: a fixed-coin native view edge is its coin successor.
* `Turing.MultiTapePTM.ConfigurationGraph.coinCountWithSymbol_eq_configMatrix`,
  `Turing.MultiTapePTM.ConfigurationGraph.liveCoinCountWithSymbol_eq_liveConfigMatrix`:
  exact matrix entries at fitting canonical views.
* The corresponding `*_of_reachable` results: the native logspace machine discharges the
  representation hypotheses at its polynomial radix.
-/

public section

namespace Turing.MultiTapePTM

open MultiTapeNTM

variable {k : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)

/-- Fixing the coin gives exactly the corresponding deterministic view successor. -/
theorem viewStep_withCoin_iff {a b : FiniteCfg k Bool State} (bit : Bool) :
    (machine.withCoin bit).toTM.toMultiTapeNTM.ViewStep a b ↔
      machine.viewCoinStep a bit = b := by
  cases hs : a.state <;>
    simp [MultiTapeNTM.ViewStep, viewCoinStep, hs, MultiTapeTM.tr_iff, eq_comm]

private theorem outputClass_idem (w : List Bool) : outputClass (outputClass w) = outputClass w := by
  simpa only [Option.toList_none, List.append_nil] using outputClass_append w none

private theorem viewCoinStep_input (a : FiniteCfg k Bool State) (bit : Bool) :
    (machine.viewCoinStep a bit).input = a.input := by
  cases hs : a.state <;> simp [viewCoinStep, hs, FiniteCfg.summarizeOutput, FiniteCfg.step]

private theorem viewCoinStep_canonical {a : FiniteCfg k Bool State}
    (ha : outputClass a.output = a.output) (bit : Bool) :
    outputClass (machine.viewCoinStep a bit).output = (machine.viewCoinStep a bit).output := by
  cases hs : a.state <;>
    simp [viewCoinStep, hs, FiniteCfg.summarizeOutput, outputClass_idem, ha]

namespace ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph

variable [Fintype State]

/-- The local edge test for one fixed coin is exact on fitting canonical views. -/
theorem edgeWithSymbol_withCoin_iff {B : ℕ} {a b : FiniteCfg k Bool State}
    (hinput : a.input = b.input) (ha : outputClass a.output = a.output)
    (hb : outputClass b.output = b.output)
    (hfitA : Fits B (registers a)) (hfitB : Fits B (registers b)) (bit : Bool) :
    edgeWithSymbol (machine.withCoin bit).toTM.toMultiTapeNTM B a.input.length
      (vertexID B a) (vertexID B b) a.input[queryIndex (k := k) B (vertexID B a)]? = true ↔
        machine.viewCoinStep a bit = b := by
  change Edge (machine.withCoin bit).toTM.toMultiTapeNTM B a.input
    (vertexID B a) (vertexID B b) ↔ _
  constructor
  · intro he
    obtain ⟨next, hstep, _, hid, hfit⟩ := edge_sound hfitA he
    have hnext : machine.viewCoinStep a bit = next := (viewStep_withCoin_iff machine bit).mp hstep
    subst next
    exact vertexID_injective ((viewCoinStep_input machine a bit).trans hinput)
      (viewCoinStep_canonical machine ha bit) hb hfit hfitB hid.symm
  · intro he
    exact edge_complete hfitA hfitB ((viewStep_withCoin_iff machine bit).mpr he)

variable {R : Type*} [CommSemiring R]

/-- The certified local coin count, cast to the coefficient semiring, is the actual matrix entry.
No closedness assumption on `V` is needed for this individual-entry identity. -/
theorem coinCountWithSymbol_eq_configMatrix {B : ℕ} {V : Finset (FiniteCfg k Bool State)}
    (x y : V) (hinput : (x : FiniteCfg k Bool State).input = y.val.input)
    (hx : outputClass x.val.output = x.val.output) (hy : outputClass y.val.output = y.val.output)
    (hfitX : Fits B (registers x.val)) (hfitY : Fits B (registers y.val)) :
    (coinCountWithSymbol machine B x.val.input.length (vertexID B x.val) (vertexID B y.val)
      x.val.input[queryIndex (k := k) B (vertexID B x.val)]? : R) =
        machine.configMatrix R V x y := by
  classical
  have hcoin (bit : Bool) :
      ((edgeWithSymbol (machine.withCoin bit).toTM.toMultiTapeNTM B x.val.input.length
        (vertexID B x.val) (vertexID B y.val)
        x.val.input[queryIndex (k := k) B (vertexID B x.val)]?).toNat : R) =
          if machine.viewCoinStep x bit = y then 1 else 0 := by
    have he := edgeWithSymbol_withCoin_iff machine hinput hx hy hfitX hfitY bit
    by_cases hb : machine.viewCoinStep x bit = y
    · simp [he.mpr hb, hb]
    · have hf : edgeWithSymbol (machine.withCoin bit).toTM.toMultiTapeNTM B x.val.input.length
          (vertexID B x.val) (vertexID B y.val)
          x.val.input[queryIndex (k := k) B (vertexID B x.val)]? = false :=
        Bool.eq_false_iff.mpr fun h => hb (he.mp h)
      simp [hf, hb]
  rw [coinCountWithSymbol, Nat.cast_add, hcoin false, hcoin true, configMatrix,
    Matrix.coinStepMatrix, Fintype.sum_bool]
  exact add_comm _ _

/-- The certified local count with halted rows removed is the actual live matrix entry. -/
theorem liveCoinCountWithSymbol_eq_liveConfigMatrix {B : ℕ}
    {V : Finset (FiniteCfg k Bool State)} (x y : V)
    (hinput : x.val.input = y.val.input)
    (hx : outputClass x.val.output = x.val.output) (hy : outputClass y.val.output = y.val.output)
    (hfitX : Fits B (registers x.val)) (hfitY : Fits B (registers y.val)) :
    (liveCoinCountWithSymbol machine B x.val.input.length (vertexID B x.val) (vertexID B y.val)
      x.val.input[queryIndex (k := k) B (vertexID B x.val)]? : R) =
        machine.liveConfigMatrix R V x y := by
  classical
  rw [liveCoinCountWithSymbol, readRegisters_vertexID hfitX]
  change ((if stateCode x.val.state = stateCode (none : Option State) then (0 : ℕ)
    else coinCountWithSymbol machine B x.val.input.length (vertexID B x.val) (vertexID B y.val)
      x.val.input[queryIndex (k := k) B (vertexID B x.val)]? : ℕ) : R) = _
  by_cases hs : x.val.state = none
  · simp [hs, liveConfigMatrix, Matrix.liveCoinStepMatrix]
  · have hcode : stateCode x.val.state ≠ stateCode (none : Option State) :=
      fun h => hs (stateCode_injective h)
    rw [ite_eq_right hcode, liveConfigMatrix, Matrix.liveCoinStepMatrix, ite_eq_left hs]
    exact coinCountWithSymbol_eq_configMatrix (R := R) machine x y hinput hx hy hfitX hfitY

omit [Fintype State] in
private theorem canonical_of_reachable {input : List Bool} {v : FiniteCfg k Bool State}
    (hv : Relation.ReflTransGen machine.toNTM.ViewStep (machine.toNTM.initView input) v) :
    outputClass v.output = v.output := by
  obtain ⟨p, hrep⟩ := exists_computationPath_of_viewStep hv
  rw [hrep.output, outputClass_idem]

/-- Reachability and the native logarithmic space bound supply every representation hypothesis
for the count-matrix reader at the standard polynomial radix. -/
theorem coinCountWithSymbol_eq_configMatrix_of_reachable (c : ℕ) {input : List Bool}
    (hs : machine.toNTM.RunsInSpace input (c * (Nat.log2 input.length + 1)))
    {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ v ∈ V, Relation.ReflTransGen machine.toNTM.ViewStep (machine.toNTM.initView input) v)
    (x y : V) :
    let B := radix (radixExponent State c) input.length
    (coinCountWithSymbol machine B input.length (vertexID B x.val) (vertexID B y.val)
      input[queryIndex (k := k) B (vertexID B x.val)]? : R) = machine.configMatrix R V x y := by
  dsimp only
  have hx := hV x x.property
  have hy := hV y y.property
  have hix : x.val.input = input := input_of_reachable hx
  have hiy : y.val.input = input := input_of_reachable hy
  simpa only [hix] using coinCountWithSymbol_eq_configMatrix machine x y (hix.trans hiy.symm)
    (canonical_of_reachable machine hx) (canonical_of_reachable machine hy)
    (fits_of_runsInSpace c hs hx) (fits_of_runsInSpace c hs hy)

/-- The same reachable-view corollary for the live configuration matrix. -/
theorem liveCoinCountWithSymbol_eq_liveConfigMatrix_of_reachable (c : ℕ) {input : List Bool}
    (hs : machine.toNTM.RunsInSpace input (c * (Nat.log2 input.length + 1)))
    {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ v ∈ V, Relation.ReflTransGen machine.toNTM.ViewStep (machine.toNTM.initView input) v)
    (x y : V) :
    let B := radix (radixExponent State c) input.length
    (liveCoinCountWithSymbol machine B input.length (vertexID B x.val) (vertexID B y.val)
      input[queryIndex (k := k) B (vertexID B x.val)]? : R) = machine.liveConfigMatrix R V x y := by
  dsimp only
  have hx := hV x x.property
  have hy := hV y y.property
  have hix : x.val.input = input := input_of_reachable hx
  have hiy : y.val.input = input := input_of_reachable hy
  simpa only [hix] using
    liveCoinCountWithSymbol_eq_liveConfigMatrix machine x y (hix.trans hiy.symm)
      (canonical_of_reachable machine hx) (canonical_of_reachable machine hy)
      (fits_of_runsInSpace c hs hx) (fits_of_runsInSpace c hs hy)

end ConfigurationGraph

end Turing.MultiTapePTM
