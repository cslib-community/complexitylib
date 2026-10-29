/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Machines.Turing.MultiTape.Halting
import Complexity.Computability.Machines.Turing.MultiTape.Halting.Rice

/-! Concrete machines that halt and loop, their descriptions inside and outside the halting and
acceptance problems, the machines diverging on a verdict, the diagonal machine against candidate
deciders, a nontrivial property of self-applied behavior for Rice's theorem, decidable sets and
reductions, input prefixes built into descriptions, the recursion theorem, and Rice's theorem for
a nontrivial property of behavior. -/

namespace ComplexityTests.Halting

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-! ### A machine that halts and a machine that loops -/

/-- Halt at once with output `[b]`. -/
def answer (b : Bool) : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := some b, state := none }

/-- Stay in place forever. -/
def spin : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := none, state := some () }

theorem answer_computes (b : Bool) (x : List Bool) : (answer b).Computes x [b] := by
  refine ⟨1, ?_, ?_⟩ <;>
  · rw [runFrom_one, MultiTapeTM.step_of_state (q := ()) rfl]
    simp [answer, Action.apply]

theorem not_halts_spin (x : List Bool) : ¬spin.Halts x := by
  rintro ⟨t, ht⟩
  refine MultiTapeTM.not_halts_of_repeat_nonhalt (tm := spin) (spin.initCfg x) (by simp) 0 ?_ t ht
  rw [zero_add, runFrom_one, MultiTapeTM.step_of_state (q := ()) rfl]
  exact Cfg.ext_zero_tapes (by simp [spin, Action.apply]) (by simp [spin, Action.apply])
    (by simp [spin, Action.apply])

/-- Halting, deterministic uniqueness, and bounded time/space witnesses for `answer b`. -/
example (b : Bool) (x : List Bool) :
    (answer b).Halts x ∧
    ¬(answer false).Computes x [true] ∧
    ∃ t s, (answer b).ComputesInTimeAndSpace x [b] t s :=
  ⟨(answer_computes b x).halts,
   fun h => by simpa using (answer_computes false x).unique h,
   (answer_computes b x).exists_computesInTimeAndSpace⟩

/-! ### Descriptions in and out of the problems -/

/-- The numbering of the single state. -/
def unitNum : Unit ↪ ℕ := ⟨fun _ => 0, fun _ _ _ => rfl⟩

/-- Concrete descriptions of `answer b` and `spin` inside and outside the halting and acceptance
problems. -/
example (b : Bool) (x : List Bool) :
    (eDesc (desc unitNum eBit (answer b)), x) ∈ haltingProblem ∧
    (eDesc (desc unitNum eBit spin), x) ∉ haltingProblem ∧
    eDesc (desc unitNum eBit (answer b)) ∈ selfHaltingProblem ∧
    eDesc (desc unitNum eBit spin) ∉ selfHaltingProblem ∧
    (eDesc (desc unitNum eBit (answer true)), x) ∈ acceptanceProblem ∧
    (eDesc (desc unitNum eBit (answer false)), x) ∉ acceptanceProblem ∧
    eDesc (desc unitNum eBit (answer true)) ∈ selfAcceptanceProblem ∧
    eDesc (desc unitNum eBit spin) ∉ selfAcceptanceProblem :=
  ⟨(desc_mem_haltingProblem_iff unitNum (answer b) x).mpr (answer_computes b x).halts,
   fun h => not_halts_spin x ((desc_mem_haltingProblem_iff unitNum spin x).mp h),
   (desc_mem_selfHaltingProblem_iff unitNum (answer b)).mpr (answer_computes b _).halts,
   fun h => not_halts_spin _ ((desc_mem_selfHaltingProblem_iff unitNum spin).mp h),
   (desc_mem_acceptanceProblem_iff unitNum (answer true) x).mpr (answer_computes true x),
   fun h => by
     simpa using (answer_computes false x).unique
       ((desc_mem_acceptanceProblem_iff unitNum (answer false) x).mp h),
   (desc_mem_selfAcceptanceProblem_iff unitNum (answer true)).mpr (answer_computes true _),
   fun h => not_halts_spin _ ((desc_mem_selfAcceptanceProblem_iff unitNum spin).mp h).halts⟩

/-! ### Diverging on a verdict -/

/-- The numbering of the states of a machine diverging on a verdict. -/
noncomputable def pNum : Option Unit × Option Bool ↪ ℕ :=
  (Fintype.equivFin _).toEmbedding.trans Fin.valEmbedding

/-- After verdict `true`, `(answer true).partialize` loops (including on its own description);
after verdict `false`, `(answer false).partialize` halts with empty output (and halts on its own
description). -/
example (x : List Bool) :
    ¬(answer true).partialize.Halts x ∧
    (answer false).partialize.Computes x [] ∧
    ¬(answer true).partialize.Halts (eDesc (desc pNum eBit (answer true).partialize)) ∧
    (answer false).partialize.Halts (eDesc (desc pNum eBit (answer false).partialize)) :=
  ⟨by rw [Computes.halts_partialize (r := none) (answer_computes true x)]; simp,
   (Computes.partialize (r := some []) (answer_computes false x) []).mpr rfl,
   by rw [Computes.halts_partialize (r := none) (answer_computes true _)]; simp,
   by rw [Computes.halts_partialize (r := some []) (answer_computes false _)]; rfl⟩

/-! ### Rice's theorem for the behavior on self-descriptions -/

/-- The words whose machine halts on them with the empty output. -/
def haltsEmpty : Set (List Bool) := {w | (decodeDesc w).Computes (w.map eBit) []}

theorem desc_mem_haltsEmpty_iff {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) :
    eDesc (desc eS eBit tm) ∈ haltsEmpty ↔ tm.Computes (eDesc (desc eS eBit tm)) [] := by
  change (decodeDesc (eDesc (desc eS eBit tm))).Computes ((eDesc (desc eS eBit tm)).map eBit)
    (([] : List Bool).map eBit) ↔ _
  rw [decodeDesc_eDesc, Desc.computes_desc]

/-- `haltsEmpty` holds for `(answer false).partialize`, fails for `spin`, and separates divergence
from halting with empty output, so it is undecidable. -/
example :
    eDesc (desc pNum eBit (answer false).partialize) ∈ haltsEmpty ∧
    eDesc (desc unitNum eBit spin) ∉ haltsEmpty ∧
    ¬IsDecidable haltsEmpty encBits :=
  ⟨(desc_mem_haltsEmpty_iff pNum _).mpr
     ((Computes.partialize (r := some []) (answer_computes false _) []).mpr rfl),
   fun h => not_halts_spin _ ((desc_mem_haltsEmpty_iff unitNum spin).mp h).halts,
   not_isDecidable_of_separates_self_desc none (some [])
     (fun _ _ _ eS tm h hmem => nomatch (h []).mp ((desc_mem_haltsEmpty_iff eS tm).mp hmem))
     fun _ _ _ eS tm h => (desc_mem_haltsEmpty_iff eS tm).mpr ((h []).mpr rfl)⟩

/-! ### Decidable sets and reductions -/

/-- Decidable sets (`{w | w.isEmpty = true}` and `∅`), undecidability of `haltingProblemᶜ` and
`acceptanceProblem`, and mapping reductions between halting problems (including from a
polynomial-time reduction). -/
example :
    IsDecidable {w : List Bool | w.isEmpty = true} encBits ∧
    IsDecidable (∅ : Set (List Bool)) encBits ∧
    ¬IsDecidable haltingProblemᶜ (encPair encBits encBits) ∧
    ¬IsDecidable acceptanceProblem (encPair encBits encBits) ∧
    MappingReducible encBits (encPair encBits encBits) selfHaltingProblemᶜ haltingProblemᶜ ∧
    MappingReducible encBits (encPair encBits encBits) selfHaltingProblem haltingProblem ∧
    MappingReducible encBits encBits selfHaltingProblem selfHaltingProblem :=
  ⟨isDecidable_iff.mpr ⟨List.isEmpty,
     (ComputableTidilyInDegree.isEmpty (enc₁ := encBool) (enc := encBits)).isComputable,
     fun _ => Iff.rfl⟩,
   isDecidable_iff.mpr ⟨fun _ => false, (ComputableTidilyInDegree.const false).isComputable,
     fun _ => by simp⟩,
   by rw [isDecidable_compl_iff]; exact not_isDecidable_haltingProblem,
   not_isDecidable_acceptanceProblem,
   selfHaltingProblem_mappingReducible.compl,
   (MappingReducible.refl encBits _).trans selfHaltingProblem_mappingReducible,
   let ⟨f, hf, hself⟩ := Cslib.Complexity.PolyTimeReducible.refl encBits selfHaltingProblem
   ⟨f, hf.tidy.isComputable, hself⟩⟩

/-! ### Input prefixes built into descriptions -/

/-- Halt at once if the input starts with `true`, and stay in place forever otherwise. -/
def firstBit : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ i _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := none,
      state := if i = some true then none else some () }

theorem halts_firstBit (x : List Bool) : firstBit.Halts (true :: x) :=
  ⟨1, by
    rw [runFrom_one, MultiTapeTM.step_of_state (q := ()) rfl]
    simp [firstBit, Action.apply, Cfg.Halted, MultiTapeNTM.initCfg, Cfg.inputSymbol]⟩

theorem not_halts_firstBit (x : List Bool) : ¬firstBit.Halts (false :: x) := by
  rintro ⟨t, ht⟩
  refine MultiTapeTM.not_halts_of_repeat_nonhalt (tm := firstBit) (firstBit.initCfg _) (by simp) 0
    ?_ t ht
  rw [zero_add, runFrom_one, MultiTapeTM.step_of_state (q := ()) rfl]
  exact Cfg.ext_zero_tapes
    (by simp [firstBit, Action.apply, MultiTapeNTM.initCfg, Cfg.inputSymbol])
    (by simp [firstBit, Action.apply]) (by simp [firstBit, Action.apply])

/-- With `[true]` hardwired, `firstBit` halts on every input; with `[false]` hardwired, on none;
building in a prefix preserves `answer b`'s output and is polynomial-time computable. -/
example (b : Bool) (p x : List Bool) :
    (hardwire (desc unitNum eBit firstBit) [true]).Halts (x.map eBit) ∧
    ¬(hardwire (desc unitNum eBit firstBit) [false]).Halts (x.map eBit) ∧
    (hardwire (desc unitNum eBit (answer b)) p).Computes (x.map eBit) [eBit b] ∧
    ComputableTidilyInPolyTime (fun q : List Bool => hardwire (desc unitNum eBit firstBit) q)
      encBits eDesc :=
  ⟨(Desc.halts_hardwire _ _ x).mpr ((Desc.halts_desc unitNum eBit firstBit (true :: x)).mpr
     (halts_firstBit x)),
   fun h => by
     rw [Desc.halts_hardwire, List.singleton_append, Desc.halts_desc] at h
     exact not_halts_firstBit x h,
   (Desc.computes_hardwire _ p x _).mpr
     ((Desc.computes_desc unitNum eBit (answer b) (p ++ x) [b]).mpr (answer_computes b _)),
   computableTidilyInPolyTime_hardwire.comp
     ((ComputableTidilyInPolyTime.const (desc unitNum eBit firstBit)).prod
       (ComputableTidilyInPolyTime.of_eq fun _ => rfl))⟩

/-! ### The recursion theorem and Rice's theorem -/

theorem behavior_answer (b : Bool) (x : List Bool) :
    behavior (eDesc (desc unitNum eBit (answer b))) x [eBit b] := by
  rw [behavior, decodeDesc_eDesc, ← List.map_singleton, Desc.computes_desc]
  exact answer_computes b x

theorem not_behavior_spin (x : List Bool) (o : List ℕ) :
    ¬behavior (eDesc (desc unitNum eBit spin)) x o := fun h => by
  rw [behavior, decodeDesc_eDesc] at h
  exact not_halts_spin x ((Desc.halts_desc unitNum eBit spin x).mp
    (Desc.halts_iff_exists_computes.mpr ⟨o, h⟩))

/-- A machine behaving as the description chosen by a constant verdict. -/
example : ∃ e : List Bool, ∀ (x : List Bool) (o : List ℕ),
    (decodeDesc e).Computes (x.map eBit) o ↔
      (desc unitNum eBit (answer true)).Computes (x.map eBit) o :=
  exists_behavior_eq (f := fun _ => true) (ComputableTidilyInDegree.const true).isComputable
    fun _ => desc unitNum eBit (answer true)

/-- **Rice's theorem** for the nontrivial property of halting on the empty input: the description
of `answer false` has it and that of `spin` does not, so it is undecidable. -/
example : ¬IsDecidable {w | behavior w ∈ {B : List Bool → List ℕ → Prop | ∃ o, B [] o}}
    encBits :=
  rice (w₀ := eDesc (desc unitNum eBit spin)) (w₁ := eDesc (desc unitNum eBit (answer false)))
    (fun ⟨o, h⟩ => not_behavior_spin [] o h) ⟨_, behavior_answer false []⟩

/-- The descriptions of machines accepting every input are undecidable. -/
example : ¬IsDecidable {w | ∀ x, behavior w x [eBit true]} encBits :=
  not_isDecidable_of_behavior (fun _ _ h hw x => h ▸ hw x)
    (w₀ := eDesc (desc unitNum eBit spin)) (w₁ := eDesc (desc unitNum eBit (answer true)))
    (fun h => not_behavior_spin [] _ (h [])) (behavior_answer true)

/-- Halting on the empty input is undecidable, as Mathlib's `ComputablePred.halting_problem` says
for partial recursive codes. -/
example : ¬IsDecidable {w | (decodeDesc w).Halts (([] : List Bool).map eBit)} encBits :=
  not_isDecidable_halts []

end ComplexityTests.Halting
