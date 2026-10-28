/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Classes.Inclusions
public import Complexity.Computability.Complexity.Classes.Oracle.Closure
public import Complexity.Computability.Complexity.Classes.Oracle.Lowness
public import Complexity.Computability.Complexity.Classes.Oracle.PolyTime
public import Complexity.Computability.Complexity.Classes.PP.Closure
public import Complexity.Computability.Complexity.Classes.Space
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Complexity.Reduction.OneOne
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Polynomial-time Turing reductions and the Turing bridge

A polynomial-time Turing reduction (Cook reduction) `A ≤ᵖ_T B` allows adaptive queries to an
oracle for `B` within polynomial time [Ladner, Lynch and Selman][LadnerLynchSelman1975],
[Arora and Barak, Section 3.4][AroraBarak09].

## Main definitions

* `Cslib.Complexity.PolyTimeTuringReducible`: polynomial-time Turing reducibility.
* `Cslib.Complexity.PolyTimeTuringHard`, `Cslib.Complexity.PolyTimeTuringComplete`: hardness and
  completeness under polynomial-time Turing reductions.
* `Cslib.Complexity.NPTuringHard`, `Cslib.Complexity.NPTuringComplete`: Turing hardness and
  completeness for `NP`.
* `Cslib.Complexity.PPTuringHard`, `Cslib.Complexity.PPTuringComplete`: Turing hardness and
  completeness for `PP`.
* `Cslib.Complexity.PSPACETuringHard`, `Cslib.Complexity.PSPACETuringComplete`: Turing hardness and
  completeness for `PSPACE`.

## Main results

* `Cslib.Complexity.polyTimeTuringReducible_iff_mem_PWithOracle`: **the Turing bridge**,
  `A ≤ᵖ_T B ↔ A ∈ P^(encB '' B)`.
* `Cslib.Complexity.polyTimeTuringReducible_bits_iff_mem_PWithOracle`: for word languages,
  `A ≤ᵖ_T B ↔ A ∈ P^B`.
* `Cslib.Complexity.PolyTimeReducible.polyTimeTuringReducible`: many-one reductions are Turing
  reductions (`≤ₘ ⇒ ≤_T`).
* `Cslib.Complexity.PolyTimeOneOneReducible.polyTimeTuringReducible`: one-one reductions are Turing
  reductions (`≤₁ ⇒ ≤_T`).
* `Cslib.Complexity.PolyTimeTuringReducible.refl`: reflexivity.
* `Cslib.Complexity.PolyTimeReducible.trans_turing`: pre-composition with a many-one reduction
  (`≤ₘ ∘ ≤_T ⇒ ≤_T`).
* `Cslib.Complexity.PolyTimeTuringReducible.compl_left`: complementation of the source language.
* `Cslib.Complexity.PolyTimeTuringReducible.compl_self`: a language's complement Turing-reduces to
  the language itself (`Aᶜ ≤_T A`).
* `Cslib.Complexity.PolyTimeTuringReducible.mem_P`: `P` is closed under Turing reductions to word
  languages.
* `Cslib.Complexity.PolyTimeHard.polyTimeTuringHard`: many-one hardness implies Turing hardness.
* `Cslib.Complexity.PolyTimeHard.polyTimeTuringHard_of_turing`: transferring many-one hardness
  across a Turing reduction.
* Hardness transfer to `P`:
  * `Cslib.Complexity.NPHard.P_eq_NP_of_turing_mem_P`: if an NP-hard problem Turing-reduces to a
    problem in `P`, then `P = NP`.
  * `Cslib.Complexity.PolyTimeHard_PP.P_eq_PP_of_turing_mem_P`: if a PP-hard problem Turing-reduces
    to a problem in `P`, then `P = PP`.
  * `Cslib.Complexity.PSPACEHard.P_eq_PSPACE_of_turing_mem_P`: if a PSPACE-hard problem
    Turing-reduces to a problem in `P`, then `P = PSPACE`.
* `Cslib.Complexity.NPHard.NP_eq_coNP_of_turing_mem_NP_inter_coNP`: if an NP-hard problem
  Turing-reduces to a problem in `NP ∩ coNP`, then `NP = coNP`.

## References

* [R. E. Ladner, N. A. Lynch, A. L. Selman, *A comparison of polynomial time
  reducibilities*][LadnerLynchSelman1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β γ : Type}
variable {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : γ ↪ List Bool}
variable {A : Set α} {B : Set β} {L : Set γ}

/-- `A` is polynomial-time Turing reducible to `B` (`A ≤ᵖ_T B`): some algorithm deciding `A` runs
in polynomial time relative to an oracle for the encoded language of `B`
[Ladner, Lynch and Selman][LadnerLynchSelman1975]. -/
def PolyTimeTuringReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α)
    (B : Set β) : Prop :=
  ∃ f : α → Bool, ComputableInPolyTimeWithOracle (encB '' B) f encA encBool ∧
    ∀ a, a ∈ A ↔ f a = true

/-- **The Turing bridge**: `A ≤ᵖ_T B` if and only if `A ∈ P^B` with respect to the encoded oracle
language `encB '' B`. -/
theorem polyTimeTuringReducible_iff_mem_PWithOracle :
    PolyTimeTuringReducible encA encB A B ↔ A ∈ PWithOracle (encB '' B) encA :=
  Iff.rfl

/-- On bitstring languages with the default encoding `encBits`, `A ≤ᵖ_T B` is exactly `A ∈ P^B`. -/
theorem polyTimeTuringReducible_bits_iff_mem_PWithOracle {B : Set (List Bool)} :
    PolyTimeTuringReducible encA encBits A B ↔ A ∈ PWithOracle B encA := by
  have : encBits '' B = B := Set.image_id B
  rw [polyTimeTuringReducible_iff_mem_PWithOracle, this]

open Classical in
/-- Every polynomial-time many-one reduction is a polynomial-time Turing reduction making a
single query to the oracle. -/
theorem PolyTimeReducible.polyTimeTuringReducible
    (h : PolyTimeReducible encA encB A B) : PolyTimeTuringReducible encA encB A B := by
  obtain ⟨f, hf, hAB⟩ := h
  refine ⟨fun a => decide (encB (f a) ∈ encB '' B), ?_, fun a => ?_⟩
  · rw [computableInPolyTimeWithOracle_iff_polyTimeOracleProgram]
    refine PolyTimeOracleProgram.of_query (req := fun a => encB (f a)) ?_ fun _ hA => hA ▸ rfl
    exact .of_tidy hf.tidy
  · dsimp
    rw [decide_eq_true_iff, encB.injective.mem_set_image, hAB a]

/-- A one-one reduction is a polynomial-time Turing reduction. -/
theorem PolyTimeOneOneReducible.polyTimeTuringReducible
    (h : PolyTimeOneOneReducible encA encB A B) : PolyTimeTuringReducible encA encB A B :=
  h.polyTimeReducible.polyTimeTuringReducible

/-- Every problem reduces to itself under polynomial-time Turing reductions. -/
@[refl]
theorem PolyTimeTuringReducible.refl (encA : α ↪ List Bool) (A : Set α) :
    PolyTimeTuringReducible encA encA A A :=
  (PolyTimeReducible.refl encA A).polyTimeTuringReducible

/-- Pre-composing a polynomial-time Turing reduction with a polynomial-time many-one reduction
yields a polynomial-time Turing reduction. -/
theorem PolyTimeReducible.trans_turing
    (hAL : PolyTimeReducible encA encL A L)
    (hLB : PolyTimeTuringReducible encL encB L B) :
    PolyTimeTuringReducible encA encB A B :=
  hAL.mem_PWithOracle hLB

/-- Negating the boolean output of the decider reduces the complement `Aᶜ` to `B`. -/
theorem PolyTimeTuringReducible.compl_left
    (h : PolyTimeTuringReducible encA encB A B) :
    PolyTimeTuringReducible encA encB Aᶜ B := by
  obtain ⟨f, hf, hA⟩ := h
  refine ⟨fun a => !f a, hf.map (g := (!·)) (by fun_prop), fun a => ?_⟩
  simp [Set.mem_compl_iff, hA a]

/-- A language's complement is polynomial-time Turing reducible to the language itself. -/
theorem PolyTimeTuringReducible.compl_self (encA : α ↪ List Bool) (A : Set α) :
    PolyTimeTuringReducible encA encA Aᶜ A :=
  (PolyTimeTuringReducible.refl encA A).compl_left

/-- **`P` is closed under polynomial-time Turing reductions to word languages.** -/
theorem PolyTimeTuringReducible.mem_P {B : Set (List Bool)}
    (h : PolyTimeTuringReducible encA encBits A B) (hB : B ∈ P encBits) : A ∈ P encA := by
  rw [polyTimeTuringReducible_bits_iff_mem_PWithOracle] at h
  rwa [← PWithOracle_eq_P hB encA]

/-- `B` is hard for the class `C` under polynomial-time Turing reductions: every problem in `C`
Turing-reduces to `B`. -/
def PolyTimeTuringHard (C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α))
    (encB : β ↪ List Bool) (B : Set β) : Prop :=
  HardUnder (fun enc => PolyTimeTuringReducible enc encB) @C B

/-- `B` is complete for the class `C` under polynomial-time Turing reductions: it belongs to `C`
and is Turing-hard for `C`. -/
def PolyTimeTuringComplete (C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α))
    (encB : β ↪ List Bool) (B : Set β) : Prop :=
  CompleteUnder (fun enc => PolyTimeTuringReducible enc encB) @C encB B

/-- Hardness for `NP` under polynomial-time Turing reductions. -/
abbrev NPTuringHard (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeTuringHard @NP encB B

/-- Completeness for `NP` under polynomial-time Turing reductions. -/
abbrev NPTuringComplete (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeTuringComplete @NP encB B

/-- Hardness for `PP` under polynomial-time Turing reductions. -/
abbrev PPTuringHard (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeTuringHard PP encB B

/-- Completeness for `PP` under polynomial-time Turing reductions. -/
abbrev PPTuringComplete (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeTuringComplete PP encB B

/-- Hardness for `PSPACE` under polynomial-time Turing reductions. -/
abbrev PSPACETuringHard (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeTuringHard @PSPACE encB B

/-- Completeness for `PSPACE` under polynomial-time Turing reductions. -/
abbrev PSPACETuringComplete (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeTuringComplete @PSPACE encB B

/-- Every problem hard for `C` under polynomial-time many-one reductions is also hard for `C`
under polynomial-time Turing reductions. -/
theorem PolyTimeHard.polyTimeTuringHard {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    (h : PolyTimeHard C encB B) : PolyTimeTuringHard C encB B :=
  HardUnder.mono (fun _ _ hr => hr.polyTimeTuringReducible) h

/-- A problem that is Turing-reducible from a many-one hard problem is Turing-hard. -/
theorem PolyTimeHard.polyTimeTuringHard_of_turing {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    (hL : PolyTimeHard C encL L) (hLB : PolyTimeTuringReducible encL encB L B) :
    PolyTimeTuringHard C encB B :=
  HardUnder.trans (fun _ _ hr h_t => hr.trans_turing h_t) hL hLB

/-- **Hardness transfer to `P`**: if a problem hard for `C` under many-one reductions Turing-reduces
to a problem `B ∈ P`, then `C ⊆ P`. -/
theorem PolyTimeHard.subset_P_of_turing_mem_P
    {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    {B : Set (List Bool)} (hL : PolyTimeHard C encL L)
    (hLB : PolyTimeTuringReducible encL encBits L B) (hB : B ∈ P encBits)
    {α : Type} (encA : α ↪ List Bool) : C encA ⊆ P encA :=
  fun A hA => (hL.polyTimeTuringHard_of_turing hLB encA A hA).mem_P hB

/-- **NP-hardness transfer**: if an NP-hard problem Turing-reduces to a language in `P`, then
`P = NP`. -/
theorem NPHard.P_eq_NP_of_turing_mem_P {B : Set (List Bool)}
    (hL : NPHard encL L) (hLB : PolyTimeTuringReducible encL encBits L B)
    (hB : B ∈ P encBits) : P encBits = NP encBits :=
  Set.Subset.antisymm P_subset_NP (hL.subset_P_of_turing_mem_P hLB hB encBits)

/-- `P` is contained in `PP`. -/
theorem P_subset_PP {α : Type} {enc : α ↪ List Bool} : P enc ⊆ PP enc :=
  P_subset_NP.trans NP_subset_PP

/-- **PP-hardness transfer**: if a PP-hard problem Turing-reduces to a language in `P`, then
`P = PP`. -/
theorem PolyTimeHard_PP.P_eq_PP_of_turing_mem_P {B : Set (List Bool)}
    (hL : PolyTimeHard PP encL L) (hLB : PolyTimeTuringReducible encL encBits L B)
    (hB : B ∈ P encBits) : P encBits = PP encBits :=
  Set.Subset.antisymm P_subset_PP (hL.subset_P_of_turing_mem_P hLB hB encBits)

/-- **PSPACE-hardness transfer**: if a PSPACE-hard problem Turing-reduces to a language in `P`,
then `P = PSPACE`. -/
theorem PSPACEHard.P_eq_PSPACE_of_turing_mem_P {B : Set (List Bool)}
    (hL : PSPACEHard encL L) (hLB : PolyTimeTuringReducible encL encBits L B)
    (hB : B ∈ P encBits) : P encBits = PSPACE encBits :=
  Set.Subset.antisymm P_subset_PSPACE (hL.subset_P_of_turing_mem_P hLB hB encBits)

/-- A problem that is Turing-hard for `C` and belongs to `P` forces `C ⊆ P`. -/
theorem PolyTimeTuringHard.subset_P_of_mem_P
    {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    {B : Set (List Bool)} (hB_hard : PolyTimeTuringHard C encBits B) (hB : B ∈ P encBits)
    {α : Type} (encA : α ↪ List Bool) : C encA ⊆ P encA :=
  fun A hA => (hB_hard encA A hA).mem_P hB

/-- If an NP-Turing-hard problem is in `P`, then `P = NP`. -/
theorem NPTuringHard.P_eq_NP_of_mem_P {B : Set (List Bool)}
    (hB_hard : NPTuringHard encBits B) (hB : B ∈ P encBits) : P encBits = NP encBits :=
  Set.Subset.antisymm P_subset_NP (hB_hard.subset_P_of_mem_P hB encBits)

/-- If a PP-Turing-hard problem is in `P`, then `P = PP`. -/
theorem PPTuringHard.P_eq_PP_of_mem_P {B : Set (List Bool)}
    (hB_hard : PPTuringHard encBits B) (hB : B ∈ P encBits) : P encBits = PP encBits :=
  Set.Subset.antisymm P_subset_PP (hB_hard.subset_P_of_mem_P hB encBits)

/-- If a PSPACE-Turing-hard problem is in `P`, then `P = PSPACE`. -/
theorem PSPACETuringHard.P_eq_PSPACE_of_mem_P {B : Set (List Bool)}
    (hB_hard : PSPACETuringHard encBits B) (hB : B ∈ P encBits) : P encBits = PSPACE encBits :=
  Set.Subset.antisymm P_subset_PSPACE (hB_hard.subset_P_of_mem_P hB encBits)

/-- If an NP-hard problem Turing-reduces to a problem in `NP ∩ coNP`, then `NP = coNP`. -/
theorem NPHard.NP_eq_coNP_of_turing_mem_NP_inter_coNP {B : Set (List Bool)}
    (hL : NPHard encL L) (hLB : PolyTimeTuringReducible encL encBits L B)
    (hB_np : B ∈ NP encBits) (hB_conp : B ∈ coNP encBits) :
    NP encBits = coNP encBits := by
  have hsub : NP encBits ⊆ coNP encBits := fun A hA => by
    have ht : PolyTimeTuringReducible encBits encBits A B :=
      hL.polyTimeTuringHard_of_turing hLB encBits A hA
    rw [polyTimeTuringReducible_bits_iff_mem_PWithOracle] at ht
    exact (PWithOracle_subset_NP_inter_coNP hB_np hB_conp ht).2
  ext A
  constructor
  · exact fun hA => hsub hA
  · intro hA
    rw [mem_coNP] at hA
    have hAc := hsub hA
    rw [mem_coNP, compl_compl] at hAc
    exact hAc

end Cslib.Complexity
