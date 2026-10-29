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
conditions and reductions. -/

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
    dsimp only [BoundedErrorAt]
    rw [Finset.filter_true_of_mem fun r _ => by simpa using hw]
    exact hcard w
  · dsimp only [BoundedErrorAt]
    rw [Finset.filter_true_of_mem fun r _ => by simpa using hw]
    exact hcard w

private theorem tail_reduces_head : PolyTimeReducible encBits encBits
    {w : List Bool | w.tail.headD false = true} {w | w.headD false = true} :=
  ⟨List.tail, by fun_prop, fun _ => Iff.rfl⟩

/-- `MA`, `AM`, `SBP`, `Σ₂`, and `Π₂` containments and reduction pullbacks on bit-string, `SAT`,
and `GraphNonIsomorphism` witnesses. -/
example :
    ({w : List Bool | w.headD false = true} ∈ AM encBits ∧
      {w : List Bool | w.headD false = true} ∈ SBP encBits ∧
      {w : List Bool | w.headD false = true} ∈ SigmaP 2 encBits ∩ PiP 2 encBits ∧
      {w : List Bool | w.headD false = true}ᶜ ∈ MA encBits) ∧
    (SAT ∈ MA encCNF ∧ SAT ∈ AM encCNF ∧ SAT ∈ PiP 2 encCNF) ∧
    ({w : List Bool | w.tail.headD false = true} ∈ MA encBits ∧
      {w : List Bool | w.tail.headD false = true} ∈ AM encBits) ∧
    ({w : List Bool | w.headD false = true} ∈ AM encBits ∧
      GraphNonIsomorphism ∈ PiP 2 (encPair encGraph encGraph)) :=
  ⟨⟨MA_subset_AM head_mem_MA_direct,
    MA_subset_SBP head_mem_MA,
    MA_subset_SigmaP_two_inter_PiP_two head_mem_MA,
    BPP_subset_MA (compl_mem_BPP (P_subset_BPP head_mem_P))⟩,
   ⟨NP_subset_MA SAT.mem_NP,
    NP_subset_AM SAT.mem_NP,
    AM_subset_PiP_two (NP_subset_AM SAT.mem_NP)⟩,
   ⟨tail_reduces_head.mem_MA head_mem_MA_direct,
    tail_reduces_head.mem_AM (MA_subset_AM head_mem_MA_direct)⟩,
   ⟨SBP_subset_AM (MA_subset_SBP head_mem_MA),
    AM_subset_PiP_two GraphNonIsomorphism.mem_AM⟩⟩

/-- The error-exponent conditions are satisfiable, for every error exponent. -/
example (e : Polynomial ℕ) :
    (∃ q : Polynomial ℕ, ∀ e : Polynomial ℕ, ∃ (p : Polynomial ℕ)
      (V : List Bool × List Bool → Bool),
      ComputableInPolyTime V (encPair encBits encBits) encBool ∧
        IsMerlinArthurVerifierWithErrorExponent encBits e q p V
          {w : List Bool | w.headD false = true}) ∧
    (∃ (p q : Polynomial ℕ) (V : _ × List Bool → Bool),
      ComputableInPolyTime V (encPair encCNF encBits) encBool ∧
        IsArthurMerlinVerifierWithErrorExponent encCNF e p q V SAT) :=
  ⟨mem_MA_iff_exists_forall_errorExponent.mp head_mem_MA_direct,
   mem_AM_iff_forall_errorExponent.mp (NP_subset_AM SAT.mem_NP) e⟩

/-- Projecting an `AM` problem on pairs: the words whose first bit, followed by one more bit, is
`true`. -/
example : {w : List Bool | ∃ v : List Bool, v.length = (1 : Polynomial ℕ).eval (encBits w).length ∧
    (w, v) ∈ {y : List Bool × List Bool | y.1.headD false = true}} ∈ AM encBits := by
  refine mem_AM_of_exists (MA_subset_AM (BPP_subset_MA (P_subset_BPP ?_))) 1
  exact ⟨fun y => y.1.headD false, by fun_prop, fun _ => Iff.rfl⟩

/-- The threshold `2 n!` of the protocol for graph non-isomorphism, computed in binary. -/
example : ComputableInPolyTime (fun n : ℕ => 2 * n.factorial) encUnary encNat :=
  .of_tidy
    ((ComputableTidilyInPolyTime.const 2).binary_mul' ComputableTidilyInPolyTime.binary_factorial)

/-- The hypothesis of the graph-isomorphism collapse follows from a reduction of `SAT` to graph
isomorphism, placing `GraphNonIsomorphism` in `Σ₂`. -/
example (h : PolyTimeReducible encCNF (encPair encGraph encGraph) SAT GraphIsomorphism) :
    GraphNonIsomorphism ∈ SigmaP 2 (encPair encGraph encGraph) :=
  PH_eq_SigmaP_two_of_npComplete_GraphIsomorphism
    ⟨GraphIsomorphism.mem_NP, CookLevin.SAT_npHard.trans h⟩ ▸
    PiP_subset_PH 2 (AM_subset_PiP_two GraphNonIsomorphism.mem_AM)

/-- `IsArthurMerlinVerifier` and `IsArthurMerlinVerifierWithErrorExponent` reduce to `BPP`'s
bounded-error and error-exponent predicates on `arthurMerlinSlice`. -/
example : ∃ (p q : Polynomial ℕ) (V : _ × List Bool → Bool),
    ComputableInPolyTime V (encPair encCNF encBits) encBool ∧
      DecidesWithBoundedError encCNF p (arthurMerlinSlice encCNF q V) SAT := by
  obtain ⟨p, q, V, hV, hAM⟩ := NP_subset_AM SAT.mem_NP
  exact ⟨p, q, V, hV, isArthurMerlinVerifier_iff_decidesWithBoundedError.mp hAM⟩

example (e : Polynomial ℕ) : ∃ (p q : Polynomial ℕ) (V : _ × List Bool → Bool),
    ComputableInPolyTime V (encPair encCNF encBits) encBool ∧
      DecidesWithErrorExponent encCNF e p (arthurMerlinSlice encCNF q V) SAT := by
  obtain ⟨p, q, V, hV, hAM⟩ :=
    mem_AM_iff_forall_errorExponent.mp (NP_subset_AM SAT.mem_NP) e
  exact ⟨p, q, V, hV, isArthurMerlinVerifierWithErrorExponent_iff_decidesWithErrorExponent.mp hAM⟩

end ComplexityTests.ArthurMerlin
