/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Kolmogorov.SingleTape
import Complexity.Computability.Machines.Turing.MultiTape.Halting
import Complexity.Computability.Machines.Turing.MultiTape.Halting.Partrec
import Complexity.Computability.Machines.Turing.MultiTape.SingleTape
import Complexity.Computability.Machines.Turing.SingleTape.Partrec
import Complexity.Computability.Machines.Turing.SingleTape.PostTuringMachine
import Complexity.Foundations.Data.BiTape
import Complexity.Foundations.Data.StackTape

/-!
# Tests for Mathlib `TM0`/`TM1` integration, single-to-multi-tape simulation, `Partrec` bridges,
and Kolmogorov complexity invariance

Concrete single-tape and multi-tape machines, tape equivalences, `TM0`/`TM1` translations,
time-and-space preserving simulations, `Partrec`/`Computable`/`ManyOneReducible` bridges,
and machine-backed Kolmogorov complexity simulations.
-/

namespace ComplexityTests.PostTuringMachine

open Cslib.Turing _root_.Turing Cslib.Kolmogorov.DescriptionMethod

/-! ### Tape equivalences (`StackTape` ↔ `ListBlank`, `BiTape` ↔ `Turing.Tape`) -/

example :
    (StackTape.mapSome [true, false]).equivListBlank =
      ListBlank.mk ([true, false].map some) ∧
    BiTape.equivTape (BiTape.mk₁ [true, false]) =
      Tape.mk₁ ([true, false].map some) ∧
    (BiTape.mk₁ [true, false]).extractWord = some [true, false] :=
  ⟨StackTape.equivListBlank_mapSome [true, false],
   BiTape.equivTape_mk₁ [true, false],
   rfl⟩

/-! ### Concrete `SingleTapeTM`, `TM0`, and `TM1` machines -/

/-- A concrete single-tape Turing machine that halts immediately on any input, leaving the input
unchanged on the tape (`id`). -/
def haltId : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ a := (⟨a, none⟩, none)

theorem haltId_outputsWithinTime (l : List Bool) :
    haltId.OutputsWithinTime l l 1 := by
  refine ⟨1, le_rfl, ?_⟩
  refine Relation.RelatesInSteps.tail _ (haltId.initCfg l) (haltId.haltCfg l) 0 (.refl _) ?_
  cases l <;> rfl

theorem haltId_outputs (l : List Bool) :
    haltId.Outputs l l := by
  obtain ⟨_, _, h⟩ := haltId_outputsWithinTime l
  exact h.reflTransGen

example (l : List Bool) :
    (∃ v, Nonempty (StateTransition.EvalsToInTime (_root_.Turing.TM1.step haltId.toTM1)
      (_root_.Turing.TM1.init (l.map some)) (some (haltId.toTM1Cfg (haltId.haltCfg l) v)) 1)) ∧
    ListBlank.mk (l.map some) ∈ _root_.Turing.TM0.eval haltId.toTM0 (l.map some) :=
  ⟨(haltId.outputsWithinTime_iff_evalsToInTime_toTM1 l l 1).mp (haltId_outputsWithinTime l),
   haltId.outputs_imp_mem_eval_toTM0 (haltId_outputs l)⟩

def haltIdTimeComputable : SingleTapeTM.TimeComputable (id : List Bool → List Bool) where
  tm := haltId
  timeBound _ := 1
  outputsFunInTime l := haltId_outputsWithinTime l

noncomputable def haltIdPolyTimeComputable :
    SingleTapeTM.PolyTimeComputable (id : List Bool → List Bool) where
  tm := haltId
  timeBound _ := 1
  outputsFunInTime l := haltId_outputsWithinTime l
  poly := 1
  bounds _ := by simp

/-! ### Single-tape to multi-tape simulation -/

example (l : List Bool) :
    let T := 2 * l.length + 4 + (1 + (l.length + 1))
    (MultiTapeTM.ofSingleTapeTM haltId).ComputesInTimeAndSpace l l T (T + 1) ∧
    MultiTapeTM.ComputableInTimeAndSpace (id : List Bool → List Bool)
      (Function.Embedding.refl (List Bool)) (Function.Embedding.refl (List Bool))
      (fun a => 3 * a.length + 2 * 1 + 6) (fun a => 3 * a.length + 2 * 1 + 7) ∧
    MultiTapeTM.ComputableInPolyTime (id : List Bool → List Bool)
      (Function.Embedding.refl (List Bool)) (Function.Embedding.refl (List Bool)) :=
  ⟨MultiTapeTM.computesInTimeAndSpace_ofSingleTapeTM haltId (haltId_outputsWithinTime l),
   haltIdTimeComputable.computableInTimeAndSpace
     (Function.Embedding.refl (List Bool)) (Function.Embedding.refl (List Bool)) id (fun _ => rfl),
   haltIdPolyTimeComputable.computableInPolyTime_id⟩

/-! ### `Partrec` / `Computable` / `ManyOneReducible` bridges -/

example :
    Partrec haltId.eval ∧
    Computable (id : List Bool → List Bool) ∧
    ManyOneReducible (· ∈ MultiTapeTM.selfHaltingProblem) (· ∈ MultiTapeTM.selfHaltingProblem) :=
  ⟨haltId.partrec_eval,
   MultiTapeTM.IsComputable.computable_bits
     haltIdPolyTimeComputable.computableInPolyTime_id.isComputable,
   (MultiTapeTM.MappingReducible.refl MultiTapeTM.encBits
     MultiTapeTM.selfHaltingProblem).manyOneReducible_bits⟩

/-! ### Kolmogorov complexity simulations and optimality -/

example :
    (ofMultiTapeTM (MultiTapeTM.ofSingleTapeTM haltId)).ecomplexity [true, false] ≤
      (ofSingleTapeTM haltId).ecomplexity [true, false] ∧
    ∃ c : ℕ, ∀ n : ℕ,
      universal.ecomplexity n ≤ (ofSingleTapeTM haltId).ecomplexity n.bits + c :=
  ⟨ecomplexity_ofMultiTapeTM_ofSingleTapeTM_le haltId [true, false],
   exists_ecomplexity_universal_le_ofSingleTapeTM_bits haltId⟩

end ComplexityTests.PostTuringMachine
