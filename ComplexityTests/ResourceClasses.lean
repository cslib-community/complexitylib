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

example {α : Type} (enc : α ↪ List Bool) (A : Set α) :
    A ∈ NP enc ↔ ∃ k, A ∈ NTIME enc (· ^ k) :=
  mem_NP_iff_exists_mem_NTIME

example {α : Type} (enc : α ↪ List Bool) (A : Set α) :
    A ∈ BPP enc ↔ ∃ k, A ∈ BPTIME enc (· ^ k) :=
  mem_BPP_iff_exists_mem_BPTIME

example {α : Type} (enc : α ↪ List Bool) (t : ℕ → ℕ) : DTIME enc t ⊆ NTIME enc t :=
  DTIME_subset_NTIME

/-- A fair-coin machine decides everything with bounded error in polynomial time: the
bounded-error condition on fair-coin machines is satisfiable. -/
example : ∃ k, (Set.univ : Set (List Bool)) ∈ BPTIME encBits (· ^ k) :=
  mem_BPP_iff_exists_mem_BPTIME.mp (P_subset_BPP univ_mem_P)

/-- A nondeterministic machine decides everything in polynomial time. -/
example : ∃ k, (Set.univ : Set (List Bool)) ∈ NTIME encBits (· ^ k) :=
  mem_NP_iff_exists_mem_NTIME.mp (P_subset_NP univ_mem_P)

/-- The words starting with `true` are decided with bounded error in polynomial time. -/
example : ∃ k, {w : List Bool | w.headD false = true} ∈ BPTIME encBits (· ^ k) :=
  mem_BPP_iff_exists_mem_BPTIME.mp (P_subset_BPP headD_mem_P)

/-- The words starting with `true` are decided nondeterministically in polynomial time. -/
example : ∃ k, {w : List Bool | w.headD false = true} ∈ NTIME encBits (· ^ k) :=
  mem_NP_iff_exists_mem_NTIME.mp (P_subset_NP headD_mem_P)

/-- The diagonal problem, outside `P`, is in nondeterministic exponential time. -/
example : {x | diagonal x = true} ∈ NEXP encBits ∧ {x | diagonal x = true} ∉ P encBits :=
  ⟨EXP_subset_NEXP setOf_diagonal_mem_EXP, diagonal_notMem_P⟩

/-- The diagonal problem is decided within time `O(2 ^ (4 n))`, by its tidy machine. -/
theorem setOf_diagonal_mem_DTIME :
    {x | diagonal x = true} ∈ DTIME encBits fun n => 2 ^ (4 * n) :=
  setOf_mem_DTIME_of_computableInO computableInO_diagonal fun _ => le_rfl

/-- A deterministic machine is a nondeterministic one: the diagonal problem, outside `P`, is in
`NTIME (2 ^ (4 n))`. -/
example : {x | diagonal x = true} ∈ NTIME encBits fun n => 2 ^ (4 * n) :=
  DTIME_subset_NTIME setOf_diagonal_mem_DTIME

/-! ### Exponential time -/

example {α : Type} (enc : α ↪ List Bool) : P enc ⊆ E enc ∧ E enc ⊆ EXP enc :=
  ⟨P_subset_E, E_subset_EXP⟩

example {α : Type} (enc : α ↪ List Bool) : NP enc ⊆ NE enc ∧ NE enc ⊆ NEXP enc :=
  ⟨NP_subset_NE, NE_subset_NEXP⟩

example {α : Type} (enc : α ↪ List Bool) : E enc ⊆ NE enc ∧ EXP enc ⊆ NEXP enc :=
  ⟨E_subset_NE, EXP_subset_NEXP⟩

/-- The diagonal problem, outside `P`, is in linear exponential time `E`, with `k = 4`. -/
example : {x | diagonal x = true} ∈ E encBits := mem_E_iff.mpr ⟨4, setOf_diagonal_mem_DTIME⟩

/-- The diagonal problem, outside `P`, is in `NE` through `NTIME (2 ^ (4 n))`. -/
example : {x | diagonal x = true} ∈ NE encBits ∧ {x | diagonal x = true} ∉ P encBits :=
  ⟨mem_NE_iff.mpr ⟨4, DTIME_subset_NTIME setOf_diagonal_mem_DTIME⟩, diagonal_notMem_P⟩

example : {w : List Bool | w.headD false = true} ∈ NE encBits :=
  NP_subset_NE (P_subset_NP headD_mem_P)

/-! ### `ZPP` -/

example {α : Type} (enc : α ↪ List Bool) : ZPP enc = RP enc ∩ coRP enc := ZPP_eq_RP_inter_coRP

/-- Answering `some true` on every random string decides everything with zero error: the
zero-error condition is satisfiable. -/
theorem univ_mem_ZPP : (Set.univ : Set (List Bool)) ∈ ZPP encBits :=
  ⟨0, fun _ => some true, .const _, fun a => ⟨fun _ _ hb => by simp_all, by
    simp only [Option.isSome_some, Finset.filter_true, Polynomial.eval_zero, pow_zero]
    refine le_trans (by norm_num) (Nat.mul_le_mul_left 2 (Finset.card_pos.mpr ?_))
    exact Finset.univ_nonempty⟩⟩

/-- Its complement is in `ZPP` too, so `ZPP` has a member outside `RP`'s trivial witnesses. -/
example : (∅ : Set (List Bool)) ∈ ZPP encBits := by
  simpa using compl_mem_ZPP univ_mem_ZPP

example : (Set.univ : Set (List Bool)) ∈ RP encBits ∩ coRP encBits :=
  ZPP_eq_RP_inter_coRP ▸ univ_mem_ZPP

/-! ### Probabilistic inclusions -/

example {α : Type} (enc : α ↪ List Bool) : P enc ⊆ BPP enc := P_subset_BPP

example {α : Type} (enc : α ↪ List Bool) : NP enc ⊆ PP enc := NP_subset_PP

example {α : Type} (enc : α ↪ List Bool) (A : Set α) (hA : A ∈ PP enc) : Aᶜ ∈ PP enc :=
  compl_mem_PP hA

/-- `coNP ⊆ PP`, by closure under complement. -/
example {α : Type} (enc : α ↪ List Bool) : coNP enc ⊆ PP enc := fun A hA => by
  simpa using compl_mem_PP (NP_subset_PP hA)

/-! ### Space and exponential time -/

/-- The chain `P ⊆ NP ⊆ PSPACE ⊆ EXP`. -/
example {α : Type} (enc : α ↪ List Bool) :
    P enc ⊆ NP enc ∧ NP enc ⊆ PSPACE enc ∧ PSPACE enc ⊆ EXP enc :=
  ⟨P_subset_NP, NP_subset_PSPACE, PSPACE_subset_EXP⟩

example {α : Type} (enc : α ↪ List Bool) : PH enc ⊆ PSPACE enc := PH_subset_PSPACE

/-- `coNP ⊆ PSPACE`, by closure under complement. -/
example {α : Type} (enc : α ↪ List Bool) : coNP enc ⊆ PSPACE enc := fun A hA => by
  simpa using compl_mem_PSPACE (NP_subset_PSPACE hA)

/-- The bounded existential over a problem in `PSPACE`: the words with an extension of their own
length in a `PSPACE` problem. -/
example {B : Set (List Bool × List Bool)} (hB : B ∈ PSPACE (encPair encBits encBits)) :
    {x | ∃ w : List Bool, w.length = x.length ∧ (x, w) ∈ B} ∈ PSPACE encBits :=
  setOf_exists_mem_PSPACE hB (.of_tidy (ComputableTidilyInPolyTime.encoding_length encBits))

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.mem_NP_iff_exists_mem_NTIME' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_NP_iff_exists_mem_NTIME

/--
info: 'Cslib.Complexity.mem_BPP_iff_exists_mem_BPTIME' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_BPP_iff_exists_mem_BPTIME

/--
info: 'Cslib.Complexity.DTIME_subset_NTIME' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.DTIME_subset_NTIME

/--
info: 'Cslib.Complexity.NP_subset_NEXP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NP_subset_NEXP

/--
info: 'Cslib.Complexity.ZPP_eq_RP_inter_coRP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ZPP_eq_RP_inter_coRP

/--
info: 'Cslib.Complexity.compl_mem_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.compl_mem_PP

/--
info: 'Cslib.Complexity.NP_subset_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NP_subset_PP

/--
info: 'Cslib.Complexity.P_subset_BPP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.P_subset_BPP

/--
info: 'Cslib.Complexity.NP_subset_PSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NP_subset_PSPACE

/--
info: 'Cslib.Complexity.PSPACE_subset_EXP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PSPACE_subset_EXP

/--
info: 'Cslib.Complexity.setOf_exists_mem_PSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.setOf_exists_mem_PSPACE

/--
info: 'Cslib.Complexity.PH_subset_PSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_subset_PSPACE

end ComplexityTests.ResourceClasses
