/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Inclusions
import Complexity.Computability.Complexity.Classes.Ladner
import Complexity.Computability.Complexity.Classes.ZPP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-! The parametric time classes and their polynomial unions, exponential time, `ZPP`, and the
inclusions between the standard classes, with concrete members witnessing that the classes are
not vacuous. -/

namespace ComplexityTests.ResourceClasses

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-- Everything is decided by the constant `true`. -/
theorem univ_mem_P : (Set.univ : Set (List Bool)) ∈ P encBits :=
  ⟨fun _ => true, .const true, fun _ => by simp⟩

/-- The words starting with `true`: neither empty nor everything. -/
theorem headD_mem_P : {w : List Bool | w.headD false = true} ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

/-! ### Time classes -/

/-- Fair-coin and nondeterministic polynomial-time machines decide `Set.univ` and the words
starting with `true`. -/
example :
    (∃ k, (Set.univ : Set (List Bool)) ∈ BPTIME encBits (· ^ k)) ∧
    (∃ k, (Set.univ : Set (List Bool)) ∈ NTIME encBits (· ^ k)) ∧
    (∃ k, {w : List Bool | w.headD false = true} ∈ BPTIME encBits (· ^ k)) ∧
    (∃ k, {w : List Bool | w.headD false = true} ∈ NTIME encBits (· ^ k)) :=
  ⟨mem_BPP_iff_exists_mem_BPTIME.mp (P_subset_BPP univ_mem_P),
    mem_NP_iff_exists_mem_NTIME.mp (P_subset_NP univ_mem_P),
    mem_BPP_iff_exists_mem_BPTIME.mp (P_subset_BPP headD_mem_P),
    mem_NP_iff_exists_mem_NTIME.mp (P_subset_NP headD_mem_P)⟩

/-- The diagonal problem, outside `P`, is decided within time `O(2 ^ (4 n))`. -/
theorem setOf_diagonal_mem_DTIME :
    {x | diagonal x = true} ∈ DTIME encBits fun n => 2 ^ (4 * n) :=
  setOf_mem_DTIME_of_computableInO computableInO_diagonal fun _ => le_rfl

/-- The diagonal problem lies in `NTIME (2 ^ (4 n))`, `E`, `NE`, and `NEXP`, separating `E` from
`P`. -/
example :
    {x | diagonal x = true} ∈ NTIME encBits (fun n => 2 ^ (4 * n)) ∧
    {x | diagonal x = true} ∈ E encBits ∧
    {x | diagonal x = true} ∈ NE encBits ∧
    {x | diagonal x = true} ∈ NEXP encBits ∧
    E encBits ≠ P encBits :=
  ⟨DTIME_subset_NTIME setOf_diagonal_mem_DTIME,
    mem_E_iff.mpr ⟨4, setOf_diagonal_mem_DTIME⟩,
    E_subset_NE (mem_E_iff.mpr ⟨4, setOf_diagonal_mem_DTIME⟩),
    EXP_subset_NEXP setOf_diagonal_mem_EXP,
    fun h => diagonal_notMem_P (h ▸ mem_E_iff.mpr ⟨4, setOf_diagonal_mem_DTIME⟩)⟩

/-! ### Exponential time -/

example :
    {w : List Bool | w.headD false = true} ∈ E encBits ∧
    {w : List Bool | w.headD false = true} ∈ EXP encBits ∧
    {w : List Bool | w.headD false = true} ∈ NE encBits ∧
    {w : List Bool | w.headD false = true} ∈ NEXP encBits :=
  ⟨P_subset_E headD_mem_P, E_subset_EXP (P_subset_E headD_mem_P),
    NP_subset_NE (P_subset_NP headD_mem_P),
    NE_subset_NEXP (NP_subset_NE (P_subset_NP headD_mem_P))⟩

/-! ### `ZPP` -/

/-- Answering `some true` on every random string decides everything with zero error: the
zero-error condition is satisfiable. -/
theorem univ_mem_ZPP : (Set.univ : Set (List Bool)) ∈ ZPP encBits :=
  ⟨0, fun _ => some true, .const _, fun a => ⟨fun _ _ hb => by simp_all, by
    simp only [Option.isSome_some, Finset.filter_true, Polynomial.eval_zero, pow_zero]
    refine le_trans (by norm_num) (Nat.mul_le_mul_left 2 (Finset.card_pos.mpr ?_))
    exact Finset.univ_nonempty⟩⟩

/-- Its complement is in `ZPP` too, and both lie in `RP ∩ coRP`. -/
example :
    (∅ : Set (List Bool)) ∈ ZPP encBits ∧
    (Set.univ : Set (List Bool)) ∈ RP encBits ∩ coRP encBits ∧
    (∅ : Set (List Bool)) ∈ RP encBits ∩ coRP encBits :=
  ⟨by simpa using compl_mem_ZPP univ_mem_ZPP,
    ZPP_eq_RP_inter_coRP ▸ univ_mem_ZPP,
    ZPP_eq_RP_inter_coRP ▸ by simpa using compl_mem_ZPP univ_mem_ZPP⟩

/-! ### Probabilistic, space, and exponential-time inclusions -/

example :
    {w : List Bool | w.headD false = true} ∈ BPP encBits ∧
    {w : List Bool | w.headD false = true} ∈ PP encBits ∧
    {w : List Bool | w.headD false = true}ᶜ ∈ PP encBits ∧
    {w : List Bool | w.headD false = true} ∈ NP encBits ∧
    {w : List Bool | w.headD false = true} ∈ PSPACE encBits :=
  ⟨P_subset_BPP headD_mem_P,
    NP_subset_PP (P_subset_NP headD_mem_P),
    compl_mem_PP (NP_subset_PP (P_subset_NP headD_mem_P)),
    P_subset_NP headD_mem_P,
    PH_subset_PSPACE (P_subset_PH headD_mem_P)⟩

/-- `coNP ⊆ PP` and `coNP ⊆ PSPACE`, by closure under complement. -/
example {α : Type} (enc : α ↪ List Bool) :
    coNP enc ⊆ PP enc ∧ coNP enc ⊆ PSPACE enc :=
  ⟨fun _ hA => by simpa using compl_mem_PP (NP_subset_PP hA),
    fun _ hA => by simpa using compl_mem_PSPACE (NP_subset_PSPACE hA)⟩

/-- The bounded existential over a problem in `PSPACE`: the words with an extension of their own
length in a `PSPACE` problem. -/
example {B : Set (List Bool × List Bool)} (hB : B ∈ PSPACE (encPair encBits encBits)) :
    {x | ∃ w : List Bool, w.length = x.length ∧ (x, w) ∈ B} ∈ PSPACE encBits :=
  setOf_exists_mem_PSPACE hB (ComputableInPolyTime.encoding_length encBits)

end ComplexityTests.ResourceClasses
