/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.MCSP.PartialHardness.EvaluatorPolyTime
public import CslibFrontier.Computability.MCSP.PartialHardness.Seeded

/-! Tests for the seeded step of the reductions from `GapCMMSA`. -/

public section

namespace CslibFrontierTests.CMMSASeeded

open Cslib Cslib.Complexity Cslib.PartialMCSP.FromCMMSA Turing.MultiTapeTM

/-- The pattern is polynomial-time in the pair of the instance and the random string, the input
shape of `rpReducible_of_seeded`. -/
example (lam₀ Δ k : ℕ) :
    ComputableInPolyTime (fun p : CMMSAInstance × List Bool => seededPattern lam₀ Δ k p.1 p.2)
      (encPair CMMSAInstance.encoding encBits) PartialMCSP.encTable :=
  computableInPolyTime_seededPattern lam₀ Δ k (ComputableInPolyTime.fst _ _)
    (ComputableInPolyTime.snd _ _)

/-- The same by `fun_prop`, with the instance and the random string projected out of a larger
context. -/
example (lam₀ Δ k : ℕ) :
    ComputableInPolyTime
      (fun p : (CMMSAInstance × ℕ) × List Bool => seededPattern lam₀ Δ k p.1.1 p.2)
      (encPair (encPair CMMSAInstance.encoding encUnary) encBits) PartialMCSP.encTable := by
  fun_prop

/-- The computability hypothesis of `rpReducible_of_seeded` for the partial MCSP map
`out I f = toInstance I Δ k (lamOf λ₀ I) P f`, the client in `PartialHardness/Reduction.lean`. -/
example (lam₀ Δ k P : ℕ) :
    ComputableInPolyTime (fun p : CMMSAInstance × List Bool =>
        toInstance p.1 Δ k (lamOf lam₀ p.1) P (seededFunctions lam₀ p.1 p.2))
      (encPair CMMSAInstance.encoding encBits) PartialMCSP.enc := by
  have hfst := ComputableInPolyTime.fst CMMSAInstance.encoding encBits
  exact computableInPolyTime_toInstance Δ k P hfst (computableInPolyTime_lamOf _ hfst)
    (computableInPolyTime_seededTables _ hfst (ComputableInPolyTime.snd _ _))
    fun p => isVarTable_seededTables _ p.1 p.2

/-- The pattern is a map `out I f` of the instance and the functions, so it meets the computability
hypothesis of `rpReducible_of_seeded` as stated. Here every instance is a yes-instance of both
problems, so the other two hypotheses hold trivially. -/
example (lam₀ Δ k : ℕ) :
    PromiseProblem.RPReducible CMMSAInstance.encoding PartialMCSP.encTable
      ⟨Set.univ, ∅, by simp⟩ ⟨Set.univ, ∅, by simp⟩ :=
  rpReducible_of_seeded lam₀
    (fun I f => List.ofFn fun i => entry (Δ := Δ) (k := k) f ((BitString.equivFin _).symm i))
    (by
      simpa only [seededPattern_eq_ofFn] using
        computableInPolyTime_seededPattern lam₀ Δ k (ComputableInPolyTime.fst _ _)
          (ComputableInPolyTime.snd _ _))
    (fun _ _ _ => trivial) (fun _ h => h.elim)

/-- The random string for an empty encoding has `2 (λ₀ + 1)` bits. -/
example (lam₀ : ℕ) : (seedLen lam₀).eval 0 = 2 * (lam₀ + 1) := by
  simp [seedLen_eval]

end CslibFrontierTests.CMMSASeeded
