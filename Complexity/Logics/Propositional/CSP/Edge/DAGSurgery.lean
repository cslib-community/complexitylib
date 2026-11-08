/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Edge.DAG
import Complexity.Foundations.Data.BitString.DeltaMatroid.Operations

/-!
# Surgery on timestamped edge-CSP DAGs

The four-coordinate consequences of even exchange are applied to actual positional tuples.
These are the local arguments in Lemmas 35 and 37 of [KazdaKolmogorovRolinek2018],
arXiv:1602.03124v6, printed pp. 16–19. They permit arbitrary common local parity.
No surgery conclusion or path validity is included among the DAG invariant's assumptions.
-/

public section

namespace Cslib.Logic.PL.CSP.DAG

open BitString Finset

variable {Rel V : Type*} {F : CSP Rel V}

private theorem occurrence_ne {i : Fin F.length} {a b : Fin F[i].2.length} (h : a ≠ b) :
    (⟨i, a⟩ : Occurrence F) ≠ ⟨i, b⟩ := by
  intro he
  cases he
  exact h rfl

private theorem localTuple_pairFlip (f : OccurrenceLabeling F Bool) (i : Fin F.length)
    (a b : Fin F[i].2.length) (hab : a ≠ b) :
    localTuple (pairFlip f ⟨i, a⟩ ⟨i, b⟩) i =
      List.ofFn (flipOn {a, b} (fun j => f ⟨i, j⟩)) := by
  rw [pairFlip_eq f (occurrence_ne hab)]
  apply congrArg List.ofFn
  funext j
  simp [flipOn_apply]

/-- Feasibility of a two-port move is exactly local feasibility at its positional constraint. -/
theorem validLabeling_pairFlip_iff {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f)
    (i : Fin F.length) (a b : Fin F[i].2.length) (hab : a ≠ b) :
    ValidLabeling sem (pairFlip f ⟨i, a⟩ ⟨i, b⟩) ↔
      sem F[i].1 (List.ofFn (flipOn {a, b} (fun j => f ⟨i, j⟩))) = true := by
  constructor
  · intro hv
    have h := hv i
    rwa [localTuple_pairFlip f i a b hab] at h
  · intro hv
    rw [pairFlip_eq f (occurrence_ne hab)]
    exact EdgeInstance.validLabeling_flipOn_pair hf i a b hv

private theorem four_eq (f : OccurrenceLabeling F Bool) (i : Fin F.length)
    {a b c d : Fin F[i].2.length}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    flipOn {c, d} (fun j => pairFlip f ⟨i, a⟩ ⟨i, b⟩ ⟨i, j⟩) =
      flipOn {a, b, c, d} (fun j => f ⟨i, j⟩) := by
  funext j
  by_cases ha : j = a <;> by_cases hb : j = b <;>
    by_cases hc : j = c <;> by_cases hd : j = d <;>
    simp_all [pairFlip, flipOn_apply]

/-- The substantive property-(5) transfer in KKR Lemmas 35 and 37.
The two forbidden old-incoming cross-pairs force the four-coordinate move. -/
theorem valid_pairFlip_pairFlip_of_no_cross {sem : Rel → List Bool → Bool}
    (hM : EdgeInstance.EvenConstraints sem F) {f : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (i : Fin F.length) {a b c d : Fin F[i].2.length}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (habf : ValidLabeling sem (pairFlip f ⟨i, a⟩ ⟨i, b⟩))
    (hcdf : ValidLabeling sem (pairFlip f ⟨i, c⟩ ⟨i, d⟩))
    (hacf : ¬ ValidLabeling sem (pairFlip f ⟨i, a⟩ ⟨i, c⟩))
    (hadf : ¬ ValidLabeling sem (pairFlip f ⟨i, a⟩ ⟨i, d⟩)) :
    ValidLabeling sem (pairFlip (pairFlip f ⟨i, a⟩ ⟨i, b⟩) ⟨i, c⟩ ⟨i, d⟩) := by
  apply (validLabeling_pairFlip_iff habf i c d hcd).mpr
  rw [four_eq f i hab hac had hbc hbd hcd]
  exact (hM i).mem_flipOn_four_of_not_mem_cross hab hac had hbc hbd hcd
    ((validLabeling_pairFlip_iff hf i a b hab).mp habf)
    ((validLabeling_pairFlip_iff hf i c d hcd).mp hcdf)
    (fun h => hacf ((validLabeling_pairFlip_iff hf i a c hac).mpr h))
    (fun h => hadf ((validLabeling_pairFlip_iff hf i a d had).mpr h))

/-- The substantive no-shortcut transfer in KKR Lemmas 35 and 37.
Exchange toward the feasible base would produce one of three forbidden pairs. -/
theorem not_valid_pairFlip_pairFlip_of_no_cross {sem : Rel → List Bool → Bool}
    (hM : EdgeInstance.EvenConstraints sem F) {f : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (i : Fin F.length) {a b c d : Fin F[i].2.length}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (habf : ValidLabeling sem (pairFlip f ⟨i, a⟩ ⟨i, b⟩))
    (hcdf : ¬ ValidLabeling sem (pairFlip f ⟨i, c⟩ ⟨i, d⟩))
    (hacf : ¬ ValidLabeling sem (pairFlip f ⟨i, a⟩ ⟨i, c⟩))
    (hadf : ¬ ValidLabeling sem (pairFlip f ⟨i, a⟩ ⟨i, d⟩)) :
    ¬ ValidLabeling sem (pairFlip (pairFlip f ⟨i, a⟩ ⟨i, b⟩) ⟨i, c⟩ ⟨i, d⟩) := by
  intro h
  have hfour := (validLabeling_pairFlip_iff habf i c d hcd).mp h
  rw [four_eq f i hab hac had hbc hbd hcd] at hfour
  rcases (hM i).mem_pair_or_mem_cross_of_mem_flipOn_four hab hac had hbc hbd hcd
      (hf i) hfour with h | h | h
  · exact hcdf ((validLabeling_pairFlip_iff hf i c d hcd).mpr h)
  · exact hacf ((validLabeling_pairFlip_iff hf i a c hac).mpr h)
  · exact hadf ((validLabeling_pairFlip_iff hf i a d had).mpr h)

end Cslib.Logic.PL.CSP.DAG
