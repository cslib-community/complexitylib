/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Probability.Product.Reindex

/-!
# Sampling independent programs over a finite type

This module provides `sampleEach`, which runs an independent probabilistic program for each element
of a finite type, generalizing `OracleComp.pi` which runs over `Fin m`.
-/

public section

open Cslib Cslib.Probability

namespace Cslib.ProbComp

/-- Run one program for each element of a finite type, independently. -/
noncomputable def sampleEach {ι β : Type} [Fintype ι] (programs : ι → ProbComp β) :
    ProbComp (ι → β) :=
  (fun x i => x (Fintype.equivFin ι i)) <$>
    OracleComp.pi fun k => programs ((Fintype.equivFin ι).symm k)

/-- The programs run by `sampleEach` are independent. -/
theorem eval_sampleEach {ι β : Type} [Fintype ι] [Finite β] (programs : ι → ProbComp β) :
    eval (sampleEach programs) = PMF.pi fun i => eval (programs i) := by
  rw [sampleEach, eval_map, eval_pi]
  have h := PMF.pi_map_piCongrLeft_symm
    (fun k => eval (programs ((Fintype.equivFin ι).symm k))) (Fintype.equivFin ι)
  simp only [Equiv.symm_apply_apply] at h
  rw [← h]
  rfl

end Cslib.ProbComp
