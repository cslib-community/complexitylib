/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BPP.KarpLipton
import Complexity.Computability.Complexity.Classes.Oracle.PolyTime
import Complexity.Computability.Complexity.Classes.Oracle.PP
import Complexity.Computability.Complexity.Classes.SPP.FewP
import Complexity.Computability.Complexity.Classes.ValiantVazirani.Collapse

/-! Structural corollaries of the class theorems: clients of the collapses on concrete encodings,
and axiom guards. -/

namespace ComplexityTests.ClassCorollaries

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-! ### `NP ⊆ BPP ⇒ PH = Σ₂` -/

example (h : SAT ∈ BPP encCNF) : PH encBits = SigmaP 2 encBits :=
  PH_eq_SigmaP_two_of_SAT_mem_BPP h

/-- The collapse applies to languages over `Bool`, with words encoded as themselves. -/
example (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ BPP encB) :
    PH encBits = SigmaP 2 encBits :=
  PH_eq_SigmaP_two_of_NP_subset_BPP h

/-! ### Oracles in `P` -/

/-- Every word: decided by the constant `true`. -/
theorem univ_mem_P : (Set.univ : Set (List Bool)) ∈ P encBits :=
  ⟨fun _ => true, .const true, fun _ => by simp⟩

example {α : Type} (enc : α ↪ List Bool) : PWithOracle Set.univ enc = P enc :=
  PWithOracle_eq_P univ_mem_P enc

example {α : Type} (enc : α ↪ List Bool) : NPWithOracle Set.univ enc = NP enc :=
  NPWithOracle_eq_NP univ_mem_P enc

example {α : Type} (enc : α ↪ List Bool) : RPWithOracle Set.univ enc = RP enc :=
  RPWithOracle_eq_RP univ_mem_P enc

open Classical in
/-- The decision problem of all numbers, as a promise problem in `PromiseP` under the binary
encoding, is solved by an oracle language in `P`. -/
example : ∃ A ∈ P encBits,
    (PromiseProblem.ofSet (Set.univ : Set ℕ)).SolvedBy fun n => decide (encNat n ∈ A) :=
  exists_mem_P_solvedBy_of_mem_PromiseP Decoder.nat
    (ofSet_mem_PromiseP.2 ⟨fun _ => true, .const true, fun _ => by simp⟩)

/-- `RP` relative to the promise problem of all numbers is `RP`. -/
example {α : Type} (enc : α ↪ List Bool) :
    RPWithPromiseOracle (PromiseProblem.ofSet (Set.univ : Set ℕ)) encNat enc = RP enc :=
  RPWithPromiseOracle_eq_RP Decoder.nat
    (ofSet_mem_PromiseP.2 ⟨fun _ => true, .const true, fun _ => by simp⟩) enc

/-! ### Valiant–Vazirani collapses -/

example (h : PromiseUSAT ∈ PromiseP encCNF) : NP encBits = RP encBits :=
  NP_eq_RP_of_PromiseUSAT_mem_PromiseP h encBits

example (h : USAT ∈ P encCNF) : NP encCNF = RP encCNF :=
  NP_eq_RP_of_USAT_mem_P h encCNF

/-! ### `P^PP` and Toda's theorem -/

example : (Set.univ : Set (List Bool)) ∈ PWithPPOracle encBits :=
  P_subset_PWithPPOracle univ_mem_P

example : (Set.univ : Set (List Bool)) ∈ PWithPPOracle encBits :=
  PP_subset_PWithPPOracle (BPP_subset_PP (P_subset_BPP univ_mem_P))

example {α : Type} (enc : α ↪ List Bool) : PWithOracle Set.univ enc ⊆ PWithPPOracle enc :=
  PWithOracle_subset_PWithPPOracle (BPP_subset_PP (P_subset_BPP univ_mem_P))

example {α : Type} {enc : α ↪ List Bool} {L : Set α} (hL : L ∈ PWithPPOracle enc) :
    ∃ (β : Type) (encβ : β ↪ List Bool) (B : Set β), B ∈ PP encβ ∧
      L ∈ PWithOracle (encβ '' B) enc :=
  exists_mem_PP_mem_PWithOracle_image hL

/-- Binary search for the constant `1 ∈ #P` reads its bit `0`. -/
example : (Set.univ : Set (List Bool)) ∈ PWithPPOracle encBits :=
  mem_PWithPPOracle_of_testBit SharpP.one_mem (p := 0) fun _ => by simp

/-- Binary search terminates on the value. -/
example : (BinarySearch.step 5)^[3] (0, 3) = (5, 0) := by decide

example {α : Type} (enc : α ↪ List Bool) : PH enc ⊆ PWithPPOracle enc :=
  PH_subset_PWithPPOracle

example {α : Type} (enc : α ↪ List Bool) :
    BPOp enc (ParityP (encPair enc encBits)) ⊆ PWithPPOracle enc :=
  BPOp_ParityP_subset_PWithPPOracle

/-- Binary search on the codes of a word, with one round more than its length, is strict oracle
PPT. -/
example : IsOraclePPTOn encBits encNat (fun w => OracleComp.interpret ProbOracleComp.query
    (BinarySearch.search w (w.length + 1))) :=
  BinarySearch.isOraclePPTOn_search (.of_tidy ComputableTidilyInPolyTime.id')
    (.of_tidy (by fun_prop))

example {α : Type} (enc : α ↪ List Bool) : PWithSharpPOracle enc ⊆ PWithPPOracle enc :=
  PWithSharpPOracle_subset_PWithPPOracle

open Classical in
/-- Binary search against the oracle of `k ≤ 5`, on codes `(u, k)`, finds `5` in three rounds. -/
example (u : List Bool) :
    OracleComp.interpret (m := Id) (languageOracle {w | ∃ k ≤ 5, w = encPair encBits encNat (u, k)})
      (BinarySearch.search u 3) = 5 :=
  BinarySearch.interpret_id_search (fun k => ⟨fun ⟨j, hj, h⟩ =>
    (Prod.mk.inj ((encPair encBits encNat).injective h)).2 ▸ hj, fun hk => ⟨k, hk, rfl⟩⟩)
    (by norm_num)

/-! ### `FewP ⊆ SPP` -/

/-- A problem in `P`, hence in `UP` and `FewP`, is in `SPP`. -/
example : (Set.univ : Set (List Bool)) ∈ SPP encBits :=
  FewP_subset_SPP (UP_subset_FewP (P_subset_UP univ_mem_P))

/-- Every word has exactly two accepted certificates of length one, so the problem of all words
is in `FewP` with ambiguity two. -/
theorem univ_mem_FewP_two : (Set.univ : Set (List Bool)) ∈ FewP encBits :=
  ⟨fun _ => 2, ⟨1, fun _ => true, .const true, fun _ => by simp⟩, 2, fun _ => by simp,
    fun _ => by simp⟩

/-- A problem of `FewP` with two witnesses on every instance is in `SPP`. -/
example : (Set.univ : Set (List Bool)) ∈ SPP encBits :=
  FewP_subset_SPP univ_mem_FewP_two

/-! ### Axiom guards -/

/--
info: 'Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_BPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_BPP

/--
info: 'Cslib.Complexity.ComputableInPolyTimeWithOracle.computableInPolyTime' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ComputableInPolyTimeWithOracle.computableInPolyTime

/--
info: 'Cslib.Complexity.PWithOracle_eq_P' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PWithOracle_eq_P

/--
info: 'Cslib.Complexity.NPWithOracle_eq_NP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NPWithOracle_eq_NP

/--
info: 'Cslib.Complexity.RPWithOracle_eq_RP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.RPWithOracle_eq_RP

/--
info: 'Cslib.Complexity.NP_eq_RP_of_PromiseUSAT_mem_PromiseP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NP_eq_RP_of_PromiseUSAT_mem_PromiseP

/--
info: 'Cslib.Complexity.NP_eq_RP_of_USAT_mem_P' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NP_eq_RP_of_USAT_mem_P

/--
info: 'Cslib.Complexity.FewP_subset_SPP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.FewP_subset_SPP

/--
info: 'Cslib.Complexity.setOf_le_mem_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.setOf_le_mem_PP

/--
info: 'Cslib.Complexity.mem_PWithPPOracle_of_testBit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_PWithPPOracle_of_testBit

/--
info: 'Cslib.Complexity.PWithSharpPOracle_subset_PWithPPOracle' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PWithSharpPOracle_subset_PWithPPOracle

/--
info: 'Cslib.Complexity.PH_subset_PWithPPOracle' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_subset_PWithPPOracle

/--
info: 'Cslib.Complexity.PH_eq_SigmaP_two_of_SAT_mem_BPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_eq_SigmaP_two_of_SAT_mem_BPP

/--
info: 'Cslib.Complexity.RPWithPromiseOracle_eq_RP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.RPWithPromiseOracle_eq_RP

/--
info: 'Cslib.Complexity.PP_subset_PWithPPOracle' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PP_subset_PWithPPOracle

/--
info: 'Cslib.Complexity.PWithOracle_subset_PWithPPOracle' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PWithOracle_subset_PWithPPOracle

/--
info: 'Cslib.Complexity.exists_mem_PP_mem_PWithOracle_image' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.exists_mem_PP_mem_PWithOracle_image

/--
info: 'Cslib.Complexity.BinarySearch.isOraclePPTOn_search' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BinarySearch.isOraclePPTOn_search

/--
info: 'Cslib.Complexity.BinarySearch.interpret_id_search' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BinarySearch.interpret_id_search

/--
info: 'Cslib.Complexity.BPOp_ParityP_subset_PWithPPOracle' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BPOp_ParityP_subset_PWithPPOracle

end ComplexityTests.ClassCorollaries
