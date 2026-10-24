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
  ⟨fun w => w.tail.headD false, .of_tidy (by fun_prop), fun _ => Iff.rfl⟩

example : {w : List Bool | w.headD false = true} ∩ {w | w.tail.headD false = true} ∈ P encBits :=
  inter_mem_P head_mem_P tail_mem_P

example : {w : List Bool | w.headD false = true} ∪ {w | w.tail.headD false = true} ∈ P encBits :=
  union_mem_P head_mem_P tail_mem_P

example : SAT ∩ SAT ∈ NP encCNF := inter_mem_NP SAT.mem_NP SAT.mem_NP
example : SAT ∪ SAT ∈ NP encCNF := union_mem_NP SAT.mem_NP SAT.mem_NP
example : UNSAT ∩ UNSAT ∈ coNP encCNF := inter_mem_coNP UNSAT_mem_coNP UNSAT_mem_coNP
example : UNSAT ∪ UNSAT ∈ coNP encCNF := union_mem_coNP UNSAT_mem_coNP UNSAT_mem_coNP

example : {w : List Bool | w.headD false = true} ∆ {w | w.tail.headD false = true} ∈
    ParityP encBits :=
  symmDiff_mem_ParityP (P_subset_ParityP head_mem_P) (P_subset_ParityP tail_mem_P)

/-- A variable-length precomposition preserves the count `2 ^ |tail w|` without a padding factor. -/
example : (fun w : List Bool => 2 ^ w.tail.length) ∈ SharpP encBits := by
  simpa [Function.comp_def] using SharpP.comp_mem (SharpP.two_pow_mem (enc := encBits) Polynomial.X)
    (.of_tidy (show ComputableTidilyInPolyTime List.tail encBits encBits by fun_prop))

/-- Requiring padding to be false gives exactly one extension, including zero padding. -/
example (n : ℕ) : acceptCount
    (andVerifier (fun _ : Unit => 1) (fun x => x.2.headD false) allFalseVerifier)
      () (1 + n) = 1 := by
  rw [acceptCount_andVerifier_allFalseVerifier]
  decide

example : (fun w : List Bool => (2 ^ w.tail.length : ℕ) - (1 : ℤ)) ∈ GapP encBits := by
  simpa [Function.comp_def] using GapP.comp_mem
    (GapP.natCast_sub_natCast_mem (SharpP.two_pow_mem (enc := encBits) Polynomial.X) SharpP.one_mem)
    (.of_tidy (show ComputableTidilyInPolyTime List.tail encBits encBits by fun_prop))

example : {w : List Bool | w.headD false = true} ∈ UP encBits := P_subset_UP head_mem_P

example : Set.univ ∈ UP encBits :=
  ⟨1, SharpP.one_mem, fun _ => le_rfl, fun _ => by simp⟩

example : (∅ : Set (List Bool)) ∈ UP encBits :=
  ⟨0, SharpP.zero_mem, fun _ => by simp, fun _ => by simp⟩

example : {w : List Bool | w.headD false = true} ∈ NP encBits ∩ ParityP encBits :=
  ⟨UP_subset_NP (P_subset_UP head_mem_P), UP_subset_ParityP (P_subset_UP head_mem_P)⟩

example : {w : List Bool | w.headD false = true} ∈ UP encBits :=
  (PolyTimeReducible.refl _ _).mem_UP (P_subset_UP head_mem_P)

example : Set.univ ∈ CeqP encBits := ⟨0, GapP.zero_mem, fun _ => by simp⟩
example : (∅ : Set (List Bool)) ∈ CeqP encBits := ⟨1, GapP.one_mem, fun _ => by simp⟩
example : UNSAT ∈ CeqP encCNF := coNP_subset_CeqP UNSAT_mem_coNP
example : UNSAT ∈ PP encCNF := CeqP_subset_PP (coNP_subset_CeqP UNSAT_mem_coNP)

/-- Satisfiable and unsatisfiable instances both exist in the concrete product language. -/
example : (([] : CNF ℕ), ([[]] : CNF ℕ)) ∈ SATUNSAT := by
  constructor
  · exact ⟨fun _ => true, rfl⟩
  · rintro ⟨σ, h⟩
    simp [CNF.eval, Clause.eval] at h

example : (([] : CNF ℕ), ([] : CNF ℕ)) ∉ SATUNSAT := by
  rintro ⟨-, h⟩
  exact h ⟨fun _ => true, rfl⟩

example : DPComplete (encPair encCNF encCNF) SATUNSAT := SATUNSAT_dpComplete

example : (SATUNSAT ∩ SATUNSAT) ∈ DP (encPair encCNF encCNF) :=
  inter_mem_DP SATUNSAT_dpComplete.1 SATUNSAT_dpComplete.1

example : SATUNSAT ∈ DP (encPair encCNF encCNF) :=
  (PolyTimeReducible.refl _ _).mem_DP SATUNSAT_dpComplete.1

/-! Axiom guards for the batch's headline results. -/

/--
info: 'Cslib.Complexity.SharpP.comp_mem' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SharpP.comp_mem

/--
info: 'Cslib.Complexity.GapP.comp_mem' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GapP.comp_mem

/--
info: 'Cslib.Complexity.inter_mem_P' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.inter_mem_P

/--
info: 'Cslib.Complexity.union_mem_NP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.union_mem_NP

/--
info: 'Cslib.Complexity.inter_mem_coNP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.inter_mem_coNP

/--
info: 'Cslib.Complexity.symmDiff_mem_ParityP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.symmDiff_mem_ParityP

/--
info: 'Cslib.Complexity.P_subset_UP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.P_subset_UP

/--
info: 'Cslib.Complexity.UP_subset_NP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.UP_subset_NP

/--
info: 'Cslib.Complexity.UP_subset_ParityP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.UP_subset_ParityP

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_UP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_UP

/--
info: 'Cslib.Complexity.coNP_subset_CeqP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.coNP_subset_CeqP

/--
info: 'Cslib.Complexity.inter_mem_CeqP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.inter_mem_CeqP

/--
info: 'Cslib.Complexity.CeqP_subset_PP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CeqP_subset_PP

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_CeqP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_CeqP

/--
info: 'Cslib.Complexity.NPComplete.dpComplete_prod' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NPComplete.dpComplete_prod

/--
info: 'Cslib.Complexity.SATUNSAT_dpComplete' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SATUNSAT_dpComplete

end ComplexityTests.BasicClasses
