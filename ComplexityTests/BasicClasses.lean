/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.P.Closure
import Complexity.Computability.Complexity.Classes.NP.Closure
import Complexity.Computability.Complexity.Classes.ParityP.Closure
import Complexity.Computability.Complexity.Classes.UP
import Complexity.Computability.Complexity.Classes.CeqP
import Complexity.Computability.Complexity.Problems.SATUNSAT
import Complexity.Computability.Complexity.Classes.SharpP.Combinators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Concrete clients for Boolean closure, exact count preservation, unambiguity, exact counting
and DP completeness. -/

namespace ComplexityTests.BasicClasses

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM
open scoped symmDiff

private theorem head_mem_P : {w : List Bool | w.headD false = true} ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

private theorem tail_mem_P : {w : List Bool | w.tail.headD false = true} ∈ P encBits :=
  ⟨fun w => w.tail.headD false, by fun_prop, fun _ => Iff.rfl⟩

example :
    ({w : List Bool | w.headD false = true} ∩ {w | w.tail.headD false = true} ∈ P encBits ∧
      {w : List Bool | w.headD false = true} ∪ {w | w.tail.headD false = true} ∈ P encBits) ∧
    (SAT ∩ SAT ∈ NP encCNF ∧ SAT ∪ SAT ∈ NP encCNF) ∧
    (UNSAT ∩ UNSAT ∈ coNP encCNF ∧ UNSAT ∪ UNSAT ∈ coNP encCNF) ∧
    {w : List Bool | w.headD false = true} ∆ {w | w.tail.headD false = true} ∈ ParityP encBits :=
  ⟨⟨inter_mem_P head_mem_P tail_mem_P, union_mem_P head_mem_P tail_mem_P⟩,
   ⟨inter_mem_NP SAT.mem_NP SAT.mem_NP, union_mem_NP SAT.mem_NP SAT.mem_NP⟩,
   ⟨inter_mem_coNP UNSAT_mem_coNP UNSAT_mem_coNP,
    union_mem_coNP UNSAT_mem_coNP UNSAT_mem_coNP⟩,
   symmDiff_mem_ParityP (P_subset_ParityP head_mem_P) (P_subset_ParityP tail_mem_P)⟩

/-- A variable-length precomposition preserves the count `2 ^ |tail w|` without a padding factor. -/
example : (fun w : List Bool => 2 ^ w.tail.length) ∈ SharpP encBits := by
  simpa [Function.comp_def] using SharpP.comp_mem (SharpP.two_pow_mem (enc := encBits) Polynomial.X)
    (show ComputableInPolyTime List.tail encBits encBits by fun_prop)

/-- Requiring padding to be false gives exactly one extension, including zero padding. -/
example (n : ℕ) : acceptCount
    (andVerifier (fun _ : Unit => 1) (fun x => x.2.headD false) allFalseVerifier)
      () (1 + n) = 1 := by
  rw [acceptCount_andVerifier_allFalseVerifier]
  decide

example : (fun w : List Bool => (2 ^ w.tail.length : ℕ) - (1 : ℤ)) ∈ GapP encBits := by
  simpa [Function.comp_def] using GapP.comp_mem
    (GapP.natCast_sub_natCast_mem (SharpP.two_pow_mem (enc := encBits) Polynomial.X) SharpP.one_mem)
    (show ComputableInPolyTime List.tail encBits encBits by fun_prop)

example :
    ({w : List Bool | w.headD false = true} ∈ UP encBits ∧
      Set.univ ∈ UP encBits ∧
      (∅ : Set (List Bool)) ∈ UP encBits ∧
      {w : List Bool | w.headD false = true} ∈ NP encBits ∩ ParityP encBits) ∧
    (Set.univ ∈ CeqP encBits ∧
      (∅ : Set (List Bool)) ∈ CeqP encBits ∧
      UNSAT ∈ CeqP encCNF ∧
      UNSAT ∈ PP encCNF) :=
  have hup := P_subset_UP head_mem_P
  ⟨⟨(PolyTimeReducible.refl _ _).mem_UP hup,
    ⟨1, SharpP.one_mem, fun _ => le_rfl, fun _ => by simp⟩,
    ⟨0, SharpP.zero_mem, fun _ => by simp, fun _ => by simp⟩,
    ⟨UP_subset_NP hup, UP_subset_ParityP hup⟩⟩,
   ⟨⟨0, GapP.zero_mem, fun _ => by simp⟩,
    ⟨1, GapP.one_mem, fun _ => by simp⟩,
    coNP_subset_CeqP UNSAT_mem_coNP,
    CeqP_subset_PP (coNP_subset_CeqP UNSAT_mem_coNP)⟩⟩

/-- Satisfiable and unsatisfiable instances both exist in the concrete product language. -/
example : (([] : CNF ℕ), ([[]] : CNF ℕ)) ∈ SATUNSAT := by
  constructor
  · exact ⟨fun _ => true, rfl⟩
  · rintro ⟨σ, h⟩
    simp [CNF.eval, Clause.eval] at h

example : (([] : CNF ℕ), ([] : CNF ℕ)) ∉ SATUNSAT := by
  rintro ⟨-, h⟩
  exact h ⟨fun _ => true, rfl⟩

example :
    PolyTimeReducible encCNF (encPair encCNF encCNF) (SAT ∩ UNSAT) SATUNSAT ∧
    (SATUNSAT ∩ SATUNSAT) ∈ DP (encPair encCNF encCNF) ∧
    SATUNSAT ∈ DP (encPair encCNF encCNF) :=
  ⟨SATUNSAT_dpComplete.2 encCNF (SAT ∩ UNSAT) ⟨SAT, SAT.mem_NP, UNSAT, UNSAT_mem_coNP, rfl⟩,
   inter_mem_DP SATUNSAT_dpComplete.1 SATUNSAT_dpComplete.1,
   (PolyTimeReducible.refl _ _).mem_DP SATUNSAT_dpComplete.1⟩

end ComplexityTests.BasicClasses
