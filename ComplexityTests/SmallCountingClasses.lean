/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.SPP
import Complexity.Computability.Complexity.Classes.FewP
import Complexity.Computability.Complexity.Classes.ModP
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Concrete clients for small counting classes, including nonconstant characteristic functions,
multiple witnesses, prime and composite moduli, and degenerate moduli. -/

namespace ComplexityTests.SmallCountingClasses

open Cslib Cslib.Complexity Turing.MultiTapeTM

private theorem head_mem_P : {w : List Bool | w.headD false = true} ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

private theorem head_mem_SPP : {w : List Bool | w.headD false = true} ∈ SPP encBits :=
  UP_subset_SPP (P_subset_UP head_mem_P)

private theorem tail_reduces_head : PolyTimeReducible encBits encBits
    {w : List Bool | w.tail.headD false = true} {w | w.headD false = true} :=
  ⟨List.tail, by fun_prop, fun _ => Iff.rfl⟩

/-- `SPP` Boolean closures, endpoint witnesses, reduction pullback, and `CeqP ∩ coCeqP`
containment. -/
example :
    ({w : List Bool | w.headD false = true}ᶜ ∈ SPP encBits ∧
      {w : List Bool | w.headD false = true} ∪ {w | w.headD false = true}ᶜ ∈ SPP encBits ∧
      {w : List Bool | w.headD false = true} ∩ {w | w.headD false = true}ᶜ ∈ SPP encBits) ∧
    (Set.univ ∈ SPP encBits ∧ (∅ : Set (List Bool)) ∈ SPP encBits) ∧
    ({w : List Bool | w.headD false = true} ∈ CeqP encBits ∩ coCeqP encBits ∧
      {w : List Bool | w.tail.headD false = true} ∈ SPP encBits) :=
  have hc := compl_mem_SPP head_mem_SPP
  ⟨⟨hc, union_mem_SPP head_mem_SPP hc, inter_mem_SPP head_mem_SPP hc⟩,
   ⟨⟨1, GapP.one_mem, fun _ => Or.inr rfl, fun _ => by simp⟩,
    ⟨0, GapP.zero_mem, fun _ => Or.inl rfl, fun _ => by simp⟩⟩,
   ⟨⟨SPP_subset_CeqP head_mem_SPP, SPP_subset_coCeqP head_mem_SPP⟩,
    tail_reduces_head.mem_SPP head_mem_SPP⟩⟩

/-- A verifier with two accepting certificates satisfies FewP's bound; no uniqueness is assumed. -/
private theorem univ_mem_FewP : Set.univ ∈ FewP encBits := by
  refine mem_FewP.mpr ⟨1, 2, fun _ => true, .const true, ?_, ?_⟩ <;> intro a <;> simp

/-- `FewP` Boolean closures and reduction pullback, together with `coUP` and `coCeqP`
containments. -/
example :
    ((∅ : Set (List Bool)) ∈ FewP encBits ∧
      {w : List Bool | w.headD false = true} ∪ Set.univ ∈ FewP encBits ∧
      {w : List Bool | w.headD false = true} ∩ Set.univ ∈ FewP encBits ∧
      {w : List Bool | w.tail.headD false = true} ∈ FewP encBits) ∧
    ({w : List Bool | w.headD false = true}ᶜ ∈ coUP encBits ∧
      SAT ∈ coCeqP encCNF ∧ SAT ∈ PP encCNF) :=
  have hf := UP_subset_FewP (P_subset_UP head_mem_P)
  ⟨⟨⟨0, SharpP.zero_mem, 0, fun _ => by simp, fun _ => by simp⟩,
    union_mem_FewP hf univ_mem_FewP,
    inter_mem_FewP hf univ_mem_FewP,
    tail_reduces_head.mem_FewP hf⟩,
   ⟨compl_mem_coUP.mpr (P_subset_UP head_mem_P),
    NP_subset_coCeqP SAT.mem_NP,
    coCeqP_subset_PP (NP_subset_coCeqP SAT.mem_NP)⟩⟩

/-- Prime, composite, and degenerate moduli in `ModP`. -/
example :
    (Set.univ ∈ ModP 3 encBits ∧
      {w : List Bool | w.headD false = true} ∈ ModP 6 encBits ∧
      {w : List Bool | w.tail.headD false = true} ∈ ModP 6 encBits) ∧
    ({w : List Bool | w.headD false = true} ∈ ParityP encBits ∧
      SAT ∈ ModP 0 encCNF ∧
      (∅ : Set (List Bool)) ∈ ModP 1 encBits ∧
      Set.univ ∉ ModP 1 encBits) ∧
    ({w : List Bool | w.headD false = true}ᶜ ∈ ModP 3 encBits ∧
      {w : List Bool | w.headD false = true} ∩ {w | w.headD false = true}ᶜ ∈ ModP 3 encBits ∧
      {w : List Bool | w.headD false = true} ∪ {w | w.headD false = true}ᶜ ∈ ModP 3 encBits) :=
  have hm6 := P_subset_ModP (by decide) head_mem_P
  have hm3 := P_subset_ModP (by decide) head_mem_P
  have hcm3 := compl_mem_ModP (by decide) hm3
  ⟨⟨⟨2, SharpP.natCast_mem 2, fun _ => by norm_num⟩,
    hm6, tail_reduces_head.mem_ModP hm6⟩,
   ⟨ModP_two ▸ P_subset_ModP (by decide) head_mem_P,
    ModP_zero.symm ▸ SAT.mem_NP,
    mem_ModP_one.mpr rfl,
    by simp [mem_ModP_one]⟩,
   ⟨hcm3, inter_mem_ModP (by decide) hm3 hcm3, union_mem_ModP (by decide) hm3 hcm3⟩⟩

/-- Why the product argument needs primality: two nonzero residues can multiply to zero. -/
example : 2 % 6 ≠ 0 ∧ 3 % 6 ≠ 0 ∧ (2 * 3) % 6 = 0 := by decide

end ComplexityTests.SmallCountingClasses
