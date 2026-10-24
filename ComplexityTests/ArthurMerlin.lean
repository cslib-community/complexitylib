/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.ArthurMerlin.Collapse
import Complexity.Computability.Complexity.Classes.ArthurMerlin.GraphNonIsomorphism
import Complexity.Computability.Complexity.Classes.ArthurMerlin.PH
import Complexity.Computability.Complexity.Classes.ArthurMerlin.SetLowerBound
import Complexity.Computability.Complexity.Classes.BPP
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial

/-! Concrete clients for the Arthur–Merlin classes: nonempty classes, satisfiable error-exponent
conditions, reductions, and axiom guards for the headline inclusions. -/

namespace ComplexityTests.ArthurMerlin

open Cslib Cslib.Complexity Turing.MultiTapeTM

private theorem head_mem_P : {w : List Bool | w.headD false = true} ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

private theorem head_mem_MA : {w : List Bool | w.headD false = true} ∈ MA encBits :=
  BPP_subset_MA (P_subset_BPP head_mem_P)

/-- An explicit verifier with a one-bit proof and one coin, both ignored. -/
private theorem head_mem_MA_direct : {w : List Bool | w.headD false = true} ∈ MA encBits := by
  have hcard (w : List Bool) : 2 * 2 ^ (1 : Polynomial ℕ).eval (encBits w).length ≤
      3 * (Finset.univ :
        Finset (Fin ((1 : Polynomial ℕ).eval (encBits w).length) → Bool)).card := by
    rw [Finset.card_univ, BitString.card, Polynomial.eval_one]
    decide
  refine ⟨1, 1, fun x => x.1.headD false, by fun_prop, fun w => ⟨fun hw => ?_, fun hw y => ?_⟩⟩
  · refine ⟨fun _ => true, ?_⟩
    rw [Finset.filter_true_of_mem fun r _ => by simpa using hw]
    exact hcard w
  · rw [Finset.filter_true_of_mem fun r _ => by simpa using hw]
    exact hcard w

example : {w : List Bool | w.headD false = true} ∈ AM encBits := MA_subset_AM head_mem_MA_direct

example : {w : List Bool | w.headD false = true} ∈ SBP encBits := MA_subset_SBP head_mem_MA

example : {w : List Bool | w.headD false = true} ∈ SigmaP 2 encBits ∩ PiP 2 encBits :=
  MA_subset_SigmaP_two_inter_PiP_two head_mem_MA

example : {w : List Bool | w.headD false = true}ᶜ ∈ MA encBits :=
  BPP_subset_MA (compl_mem_BPP (P_subset_BPP head_mem_P))

example : SAT ∈ MA encCNF := NP_subset_MA SAT.mem_NP

example : SAT ∈ AM encCNF := NP_subset_AM SAT.mem_NP

example : SAT ∈ PiP 2 encCNF := AM_subset_PiP_two (NP_subset_AM SAT.mem_NP)

private theorem tail_reduces_head : PolyTimeReducible encBits encBits
    {w : List Bool | w.tail.headD false = true} {w | w.headD false = true} :=
  ⟨List.tail, by fun_prop, fun _ => Iff.rfl⟩

example : {w : List Bool | w.tail.headD false = true} ∈ MA encBits :=
  tail_reduces_head.mem_MA head_mem_MA_direct

example : {w : List Bool | w.tail.headD false = true} ∈ AM encBits :=
  tail_reduces_head.mem_AM (MA_subset_AM head_mem_MA_direct)

/-- The error-exponent conditions are satisfiable, for every error exponent. -/
example : ∃ q : Polynomial ℕ, ∀ e : Polynomial ℕ, ∃ (p : Polynomial ℕ)
    (V : List Bool × List Bool → Bool),
    ComputableInPolyTime V (encPair encBits encBits) encBool ∧
      IsMerlinArthurVerifierWithErrorExponent encBits e q p V
        {w : List Bool | w.headD false = true} :=
  mem_MA_iff_exists_forall_errorExponent.mp head_mem_MA_direct

example (e : Polynomial ℕ) : ∃ (p q : Polynomial ℕ) (V : _ × List Bool → Bool),
    ComputableInPolyTime V (encPair encCNF encBits) encBool ∧
      IsArthurMerlinVerifierWithErrorExponent encCNF e p q V SAT :=
  mem_AM_iff_forall_errorExponent.mp (NP_subset_AM SAT.mem_NP) e

example : {w : List Bool | w.headD false = true} ∈ AM encBits :=
  SBP_subset_AM (MA_subset_SBP head_mem_MA)

example : GraphNonIsomorphism ∈ PiP 2 (encPair encGraph encGraph) :=
  AM_subset_PiP_two GraphNonIsomorphism.mem_AM

/-- Projecting an `AM` problem on pairs: the words whose first bit, followed by one more bit, is
`true`. -/
example : {w : List Bool | ∃ v : List Bool, v.length = (1 : Polynomial ℕ).eval (encBits w).length ∧
    (w, v) ∈ {y : List Bool × List Bool | y.1.headD false = true}} ∈ AM encBits := by
  refine mem_AM_of_exists (MA_subset_AM (BPP_subset_MA (P_subset_BPP ?_))) 1
  exact ⟨fun y => y.1.headD false, by fun_prop, fun _ => Iff.rfl⟩

/-- The threshold `2 n!` of the protocol for graph non-isomorphism, computed in binary. -/
example : ComputableTidilyInPolyTime (fun n : ℕ => 2 * n.factorial) encUnary encNat :=
  (ComputableTidilyInPolyTime.const 2).binary_mul' ComputableTidilyInPolyTime.binary_factorial

/-- The hypothesis of the graph-isomorphism collapse follows from a reduction of `SAT` to graph
isomorphism. -/
example (h : PolyTimeReducible encCNF (encPair encGraph encGraph) SAT GraphIsomorphism) :
    PH encBits = SigmaP 2 encBits :=
  PH_eq_SigmaP_two_of_npComplete_GraphIsomorphism
    ⟨GraphIsomorphism.mem_NP, CookLevin.SAT_npHard.trans h⟩

/-! ### Axiom guards -/

/-- info: 'Cslib.Complexity.NP_subset_MA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.NP_subset_MA

/-- info: 'Cslib.Complexity.BPP_subset_MA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.BPP_subset_MA

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_MA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_MA

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_AM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_AM

/--
info: 'Cslib.Complexity.mem_MA_iff_exists_forall_errorExponent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.mem_MA_iff_exists_forall_errorExponent

/--
info: 'Cslib.Complexity.mem_AM_iff_forall_errorExponent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.mem_AM_iff_forall_errorExponent

/-- info: 'Cslib.Complexity.MA_subset_AM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.MA_subset_AM

/-- info: 'Cslib.Complexity.MA_subset_SBP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.MA_subset_SBP

/--
info: 'Cslib.Complexity.MA_subset_SigmaP_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.MA_subset_SigmaP_two

/--
info: 'Cslib.Complexity.AM_subset_PiP_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.AM_subset_PiP_two

/--
info: 'Cslib.Complexity.MA_subset_SigmaP_two_inter_PiP_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.MA_subset_SigmaP_two_inter_PiP_two

/-- info: 'Cslib.Complexity.NP_subset_AM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.NP_subset_AM

/-- info: 'Cslib.Complexity.BPP_subset_AM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.BPP_subset_AM

/--
info: 'Cslib.Complexity.MA_subset_PiP_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.MA_subset_PiP_two

/-- info: 'Cslib.Complexity.AM_subset_PH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.AM_subset_PH

/--
info: 'Cslib.Complexity.mem_AM_of_card_certifiedSet' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.mem_AM_of_card_certifiedSet

/-- info: 'Cslib.Complexity.SBP_subset_AM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.SBP_subset_AM

/--
info: 'Cslib.Complexity.GraphNonIsomorphism.mem_AM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.GraphNonIsomorphism.mem_AM

/--
info: 'Cslib.Complexity.mem_AM_of_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.mem_AM_of_exists

/--
info: 'Cslib.Complexity.SigmaP_two_subset_AM_of_coNP_subset_AM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SigmaP_two_subset_AM_of_coNP_subset_AM

/--
info: 'Cslib.Complexity.PH_eq_SigmaP_two_of_coNP_subset_AM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PH_eq_SigmaP_two_of_coNP_subset_AM

/--
info: 'Cslib.Complexity.SigmaP_two_eq_AM_of_coNP_subset_AM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SigmaP_two_eq_AM_of_coNP_subset_AM

/--
info: 'Cslib.Complexity.PH_eq_SigmaP_two_of_npComplete_GraphIsomorphism' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PH_eq_SigmaP_two_of_npComplete_GraphIsomorphism

/--
info: 'Cslib.Complexity.PiP_two_subset_SigmaP_two_of_coNP_subset_AM' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PiP_two_subset_SigmaP_two_of_coNP_subset_AM

/--
info: 'Cslib.Complexity.PiP_two_eq_SigmaP_two_of_coNP_subset_AM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PiP_two_eq_SigmaP_two_of_coNP_subset_AM

end ComplexityTests.ArthurMerlin
