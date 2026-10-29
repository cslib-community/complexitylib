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

/-! Structural corollaries of the class theorems: clients of the collapses on concrete encodings.
-/

namespace ComplexityTests.ClassCorollaries

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-! ### `NP ⊆ BPP ⇒ PH = Σ₂` -/

/-- If `SAT ∈ BPP` (or `NP ⊆ BPP` uniformly), the polynomial hierarchy collapses to `Σ₂`,
so `Σ₃ ⊆ Σ₂` on bit strings. -/
example :
    (SAT ∈ BPP encCNF →
      PH encBits = SigmaP 2 encBits ∧ SigmaP 3 encBits ⊆ SigmaP 2 encBits) ∧
    ((∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ BPP encB) →
      PH encBits = SigmaP 2 encBits ∧ SigmaP 3 encBits ⊆ SigmaP 2 encBits) :=
  ⟨fun h =>
    have hcol := PH_eq_SigmaP_two_of_SAT_mem_BPP h
    ⟨hcol, fun _ hL => hcol ▸ SigmaP_subset_PH 3 hL⟩,
   fun h =>
    have hcol := PH_eq_SigmaP_two_of_NP_subset_BPP h
    ⟨hcol, fun _ hL => hcol ▸ SigmaP_subset_PH 3 hL⟩⟩

/-! ### Oracles in `P` -/

/-- Every word: decided by the constant `true`. -/
theorem univ_mem_P : (Set.univ : Set (List Bool)) ∈ P encBits :=
  ⟨fun _ => true, .const true, fun _ => by simp⟩

example {α : Type} (enc : α ↪ List Bool) :
    PWithOracle Set.univ enc = P enc ∧
    NPWithOracle Set.univ enc = NP enc ∧
    RPWithOracle Set.univ enc = RP enc :=
  ⟨PWithOracle_eq_P univ_mem_P enc,
   NPWithOracle_eq_NP univ_mem_P enc,
   RPWithOracle_eq_RP univ_mem_P enc⟩

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

example :
    (PromiseUSAT ∈ PromiseP encCNF →
      NP encBits = RP encBits ∧ SAT ∈ RP encCNF) ∧
    (USAT ∈ P encCNF →
      NP encCNF = RP encCNF ∧ SAT ∈ RP encCNF) :=
  ⟨fun h =>
    ⟨NP_eq_RP_of_PromiseUSAT_mem_PromiseP h encBits,
     NP_eq_RP_of_PromiseUSAT_mem_PromiseP h encCNF ▸ SAT.mem_NP⟩,
   fun h =>
    have hcol := NP_eq_RP_of_USAT_mem_P h encCNF
    ⟨hcol, hcol ▸ SAT.mem_NP⟩⟩

/-! ### `P^PP` and Toda's theorem -/

example {α : Type} (enc : α ↪ List Bool) :
    (Set.univ : Set (List Bool)) ∈ PWithPPOracle encBits ∧
    PWithOracle Set.univ enc ⊆ PWithPPOracle enc ∧
    (∃ (β : Type) (encβ : β ↪ List Bool) (B : Set β), B ∈ PP encβ ∧
      (Set.univ : Set (List Bool)) ∈ PWithOracle (encβ '' B) encBits) ∧
    SAT ∈ PWithPPOracle encCNF :=
  ⟨PP_subset_PWithPPOracle (BPP_subset_PP (P_subset_BPP univ_mem_P)),
   PWithOracle_subset_PWithPPOracle (BPP_subset_PP (P_subset_BPP univ_mem_P)),
   exists_mem_PP_mem_PWithOracle_image (P_subset_PWithPPOracle univ_mem_P),
   PH_subset_PWithPPOracle (NP_subset_PH SAT.mem_NP)⟩

/-- Binary search for the constant `1 ∈ #P` reads its bit `0` and terminates in three steps
on `5`. -/
example :
    (Set.univ : Set (List Bool)) ∈ PWithPPOracle encBits ∧
    (BinarySearch.step 5)^[3] (0, 3) = (5, 0) :=
  ⟨mem_PWithPPOracle_of_testBit SharpP.one_mem (p := 0) fun _ => by simp, by decide⟩

example {α : Type} (enc : α ↪ List Bool) :
    BPP enc ⊆ PWithPPOracle enc ∧ NP enc ⊆ PWithPPOracle enc :=
  ⟨(BPOp_P.symm.subset.trans (BPOp_mono P_subset_ParityP)).trans
     BPOp_ParityP_subset_PWithPPOracle,
   (NP_subset_PH.trans PH_subset_PWithSharpPOracle).trans PWithSharpPOracle_subset_PWithPPOracle⟩

/-- Binary search on the codes of a word, with one round more than its length, is strict oracle
PPT. -/
example : IsOraclePPTOn encBits encNat (fun w => OracleComp.interpret ProbOracleComp.query
    (BinarySearch.search w (w.length + 1))) :=
  BinarySearch.isOraclePPTOn_search .id' (by fun_prop)

open Classical in
/-- Binary search against the oracle of `k ≤ 5`, on codes `(u, k)`, finds `5` in three rounds. -/
example (u : List Bool) :
    OracleComp.interpret (m := Id) (languageOracle {w | ∃ k ≤ 5, w = encPair encBits encNat (u, k)})
      (BinarySearch.search u 3) = 5 :=
  BinarySearch.interpret_id_search (fun k => ⟨fun ⟨j, hj, h⟩ =>
    (Prod.mk.inj ((encPair encBits encNat).injective h)).2 ▸ hj, fun hk => ⟨k, hk, rfl⟩⟩)
    (by norm_num)

/-! ### `FewP ⊆ SPP` -/

/-- Every word has exactly two accepted certificates of length one, so the problem of all words
is in `FewP` with ambiguity two. -/
theorem univ_mem_FewP_two : (Set.univ : Set (List Bool)) ∈ FewP encBits :=
  ⟨fun _ => 2, ⟨1, fun _ => true, .const true, fun _ => by simp⟩, 2, fun _ => by simp,
    fun _ => by simp⟩

/-- `P ⊆ UP ⊆ FewP ⊆ SPP` places `Set.univ` in `SPP`. -/
example : (Set.univ : Set (List Bool)) ∈ SPP encBits :=
  FewP_subset_SPP (UP_subset_FewP (P_subset_UP univ_mem_P))

/-- A two-witness `FewP` certificate also places `Set.univ` in `SPP`. -/
example : (Set.univ : Set (List Bool)) ∈ SPP encBits :=
  FewP_subset_SPP univ_mem_FewP_two

end ComplexityTests.ClassCorollaries
