/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
public import CslibFrontier.Cryptanalysis.AddXNORIdealPlantedUniqueness
import CslibFrontier.Languages.Probabilistic.Oracle.Norm

/-! # Actual planted uniqueness boundary and counter-candidate clients -/

public section

open Cslib Cslib.Probability Cslib.OracleComp Cslib.RandomPermutation
open Cslib.Cryptanalysis.AddXNOR.IdealChain

example (perms : Label 0 → Equiv.Perm (Fin 5)) :
    (some (fun i => Fin.elim0 i), (⟨[], [], perms⟩ : Replay.State (Label 0) (Fin 5))) ∈
      (ProbOracleComp.runWith Replay.answer
        (PlantedUniqueness.experiment 0 (fun i => Fin.elim0 i)
          (fun _ _ => pure (fun i => Fin.elim0 i))) ⟨[], [], perms⟩).support := by
  simp [PlantedUniqueness.experiment, walk]

/-- A concrete wrong word cannot be accepted in a collision-free execution. -/
example (perms : Label 3 → Equiv.Perm (Fin 7)) (final : Replay.State (Label 3) (Fin 7))
    (hout : (some (fun _ => true), final) ∈ (ProbOracleComp.runWith Replay.answer
      (PlantedUniqueness.experiment 0 (fun _ => false)
        (fun _ _ => pure (fun _ => true))) ⟨[], [], perms⟩).support) :
    ¬Forest.NoCollision {0} final.records := by
  intro hc
  have he := PlantedUniqueness.accepted_eq perms 0 (fun _ => false) (fun _ => true)
    (fun _ _ => pure (fun _ => true)) final hout hc
  have hi := congrFun he (0 : Fin 3)
  contradiction

/-- The transport works for a private-coin candidate, without assuming its query budget. -/
example :
    ((plantedSearch (fun (_ _ : Fin 5) => do
        let coin ← ProbOracleComp.sample (ProbComp.unifFin 1)
        return (fun _ : Fin 3 => decide (coin.val = 0)))) true).toReal ≤
      (((challenges.bind fun draw => PlantedUniqueness.audit draw (1 : Fin 3)
        (fun (_ _ : Fin 5) => do
          let coin ← ProbOracleComp.sample (ProbComp.unifFin 1)
          return (fun _ : Fin 3 => decide (coin.val = 0)))).map
        (fun r => r.stopped || r.collided)) true).toReal +
      (((challenges.bind fun draw => PlantedUniqueness.audit draw (1 : Fin 3)
        (fun (_ _ : Fin 5) => do
          let coin ← ProbOracleComp.sample (ProbComp.unifFin 1)
          return (fun _ : Fin 3 => decide (coin.val = 0)))).map
        (fun r => r.guessed && !r.stopped)) true).toReal := by
  exact PlantedUniqueness.search_transport 1 _
