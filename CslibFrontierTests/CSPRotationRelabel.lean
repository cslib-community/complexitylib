/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Relabel
import CslibFrontier.Logics.Propositional.CNF.Compact.Relabel

/-! Actual incidence/checker transport and the original CNF compact relabel clients. -/

namespace CslibFrontierTests.CSPRotationRelabel

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity
open Cslib.Complexity.CSP

-- The renamed statement still applies directly to the original literal occurrence mapper.
example {Rel V W : Type} (F : CSP Rel V) (f : V → W) :
    (F.relabel f).occurrences = F.occurrences.map (fun o => (o.1, o.2.1, f o.2.2)) :=
  CSP.occurrences_relabel F f

private def rename (n : ℕ) : ℕ := if n = 7 then 11 else 10
private def F : CSP Unit ℕ := [((), [2, 7, 2]), ((), [])]
private def φ : CNF ℕ := [[(2, true), (7, false), (2, false)], []]

private theorem usedInjection : Set.InjOn rename {v | v ∈ F.vars} := by
  intro x hx y hy
  simp only [Set.mem_ofPred_eq, F, CSP.vars, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp [rename]

example : incidenceGraph (F.relabel rename) = incidenceGraph F :=
  incidenceGraph_relabel_of_injOn _ _ usedInjection

example : verifyRotationCertificate (F.relabel rename) ⟨[4, 3, 2, 5, 0, 1]⟩ = true := by
  rw [verifyRotationCertificate_relabel_of_injOn F rename usedInjection]
  decide +kernel

example : (φ.relabel rename).distinctVars = φ.distinctVars.map rename :=
  CNF.distinctVars_relabel_of_injOn _ _ usedInjection

example : φ.compact.distinctVars = φ.distinctVars.map φ.vars.idxOf :=
  CNF.distinctVars_compact _

end CslibFrontierTests.CSPRotationRelabel
