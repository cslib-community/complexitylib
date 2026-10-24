/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Parameterized.VertexCover

/-!
# Tests: fixed-parameter tractability

`SAT` and `k`-SAT in `FPT` and `XP` for the number of variables, and for a larger parameter; a
problem in `P` in `FPT` for every parameter; the classes for a bounded parameter; a concrete
fpt-reduction from 3SAT to SAT, its composition with itself, and the closure of `FPT` under it;
Boolean closure on concrete problems; kernelizations (`IsKernelization`, `HasKernel`,
`HasPolyKernel`) and the Cai–Chen–Downey–Fellows equivalence; `VertexCover` by bounded search tree;
and the axioms of the headline theorems.
-/

namespace ComplexityTests.Parameterized

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Satisfiability parameterized by the number of variables -/

example : SAT ∈ FPT encCNF CNF.numVars := SAT_mem_FPT

example : KSAT 3 ∈ FPT encCNF CNF.numVars := KSAT_mem_FPT 3

example : SAT ∈ XP encCNF CNF.numVars := FPT_subset_XP SAT_mem_FPT

/-- A larger parameter: the number of occurrences of variables bounds the number of distinct
variables. -/
example : SAT ∈ FPT encCNF fun φ => φ.vars.length :=
  FPT_subset_FPT_of_le_comp (h := id) CNF.numVars_le_length_vars SAT_mem_FPT

example : SATᶜ ∈ FPT encCNF CNF.numVars := compl_mem_FPT SAT_mem_FPT

/-- The fpt bound of exhaustive search can be read off with a monotone function. -/
example : ∃ f : ℕ → ℕ, Monotone f ∧ ∃ c : ℕ, DecidableInTimeO SAT encCNF
    fun φ => f φ.numVars * ((encCNF φ).length + 1) ^ c :=
  mem_FPT_iff_exists_monotone.mp SAT_mem_FPT

/-! ### A problem in `P` -/

/-- The formulas whose clauses have at most three literals. -/
private def Narrow : Set (CNF ℕ) := {φ | ∀ c ∈ φ, c.length ≤ 3}

private theorem narrow_mem_P : Narrow ∈ P encCNF :=
  ⟨_, (computableInPolyTime_all_length_le 3), fun φ => by simp [Narrow]⟩

example : Narrow ∈ FPT encCNF CNF.numVars := P_subset_FPT narrow_mem_P

/-- Every parameter works for a problem in `P`, even the length of the formula. -/
example : Narrow ∈ FPT encCNF List.length := P_subset_FPT narrow_mem_P

example : KSAT 3 = Narrow ∩ SAT := by
  ext φ
  rfl

/-- 3SAT is the intersection of a problem in `P` and one in `FPT`. -/
example : KSAT 3 ∈ FPT encCNF CNF.numVars := by
  have : KSAT 3 = Narrow ∩ SAT := Set.ext fun _ => Iff.rfl
  rw [this]
  exact inter_mem_FPT (P_subset_FPT narrow_mem_P) SAT_mem_FPT

example : Narrow ∪ SAT ∈ FPT encCNF CNF.numVars :=
  union_mem_FPT (P_subset_FPT narrow_mem_P) SAT_mem_FPT

/-! ### Bounded parameters -/

example : FPT encCNF (fun _ => 0) = P encCNF := FPT_eq_P_of_le (K := 0) fun _ => le_rfl

example : XP encCNF (fun _ => 5) = P encCNF := XP_eq_P_of_le (K := 5) fun _ => le_rfl

/-- `SAT ∈ FPT` for a constant parameter would put `SAT` in `P`. -/
example (h : SAT ∈ FPT encCNF fun _ => 7) : SAT ∈ P encCNF :=
  FPT_eq_P_of_le (K := 7) (fun _ => le_rfl) ▸ h

/-! ### An fpt-reduction from 3SAT to SAT -/

/-- Formulas with clauses of at most three literals are kept; the others go to the empty clause. -/
private def toSAT (φ : CNF ℕ) : CNF ℕ :=
  if φ.all (fun c => decide (c.length ≤ 3)) then φ else [[]]

private theorem toSAT_polyTime : ComputableTidilyInPolyTime toSAT encCNF encCNF :=
  ComputableTidilyInPolyTime.ite' (computableInPolyTime_all_length_le 3).tidy
    ComputableTidilyInPolyTime.id' (ComputableTidilyInPolyTime.const _)

private theorem numVars_toSAT_le (φ : CNF ℕ) : (toSAT φ).numVars ≤ φ.numVars := by
  unfold toSAT
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

private theorem mem_SAT_toSAT (φ : CNF ℕ) : φ ∈ ThreeSAT ↔ toSAT φ ∈ SAT := by
  rw [← KSAT_three]
  unfold toSAT
  by_cases hφ : ∀ c ∈ φ, c.length ≤ 3
  · have hw : (φ.all fun c => decide (c.length ≤ 3)) = true := by simpa using hφ
    simp only [hw, ite_true]
    exact ⟨fun h => h.2, fun h => ⟨hφ, h⟩⟩
  · have hw : (φ.all fun c => decide (c.length ≤ 3)) = false := by simpa using hφ
    simp only [hw, Bool.false_eq_true, ite_false]
    exact ⟨fun h => (hφ h.1).elim, fun ⟨σ, hσ⟩ => by simp at hσ⟩

private theorem threeSAT_fptReducible_SAT :
    FPTReducible encCNF encCNF CNF.numVars CNF.numVars ThreeSAT SAT :=
  FPTReducible.of_computableInPolyTime (.of_tidy toSAT_polyTime) (h := id) numVars_toSAT_le
    mem_SAT_toSAT

/-- The reduction does not map the formula `x₀ ∧ (x₀ ∨ x₁ ∨ x₂ ∨ x₃)` to itself. -/
example : toSAT [[(0, true)], [(0, true), (1, true), (2, true), (3, true)]] = [[]] := by decide

example : toSAT [[(0, true)], [(0, false), (1, true)]] = [[(0, true)], [(0, false), (1, true)]] :=
  by decide

example : ThreeSAT ∈ FPT encCNF CNF.numVars :=
  threeSAT_fptReducible_SAT.mem_FPT SAT_mem_FPT

example : ThreeSATᶜ ∈ XP encCNF CNF.numVars :=
  threeSAT_fptReducible_SAT.compl.mem_XP (FPT_subset_XP (compl_mem_FPT SAT_mem_FPT))

example : FPTReducible encCNF encCNF CNF.numVars CNF.numVars ThreeSAT ThreeSAT :=
  .refl _ _ _

/-- Composing the reduction with the identity reduction on SAT. -/
example : FPTReducible encCNF encCNF CNF.numVars CNF.numVars ThreeSAT SAT :=
  threeSAT_fptReducible_SAT.trans (.refl _ _ _)

/-! ### Kernelization -/

example : HasKernel encCNF CNF.numVars SAT := hasKernel_of_mem_FPT SAT_mem_FPT

example : HasPolyKernel encCNF CNF.numVars Narrow := hasPolyKernel_of_mem_P narrow_mem_P

example : HasKernel encCNF CNF.numVars Narrow := (hasPolyKernel_of_mem_P narrow_mem_P).hasKernel

/-- A concrete kernelization for `Narrow`: map every narrow formula to `[]` and every other formula
to a single four-literal clause. -/
private def narrowNo : CNF ℕ := [[(0, true), (0, true), (0, true), (0, true)]]

private def narrowKernel (φ : CNF ℕ) : CNF ℕ :=
  if φ.all (fun c => decide (c.length ≤ 3)) then [] else narrowNo

private theorem isKernelization_narrowKernel :
    IsKernelization encCNF CNF.numVars Narrow narrowKernel
      fun _ => (encCNF ([] : CNF ℕ)).length + (encCNF narrowNo).length + 1 := by
  refine ⟨.of_tidy (ComputableTidilyInPolyTime.ite' (computableInPolyTime_all_length_le 3).tidy
    (ComputableTidilyInPolyTime.const []) (ComputableTidilyInPolyTime.const narrowNo)),
    fun φ => ?_, fun φ => ?_, fun φ => ?_⟩
  · unfold narrowKernel
    by_cases hφ : ∀ c ∈ φ, c.length ≤ 3
    · have hw : (φ.all fun c => decide (c.length ≤ 3)) = true := by simpa using hφ
      simp only [hw, ↓reduceIte]
      exact ⟨fun _ => hφ, fun _ _ hc => by simp at hc⟩
    · have hw : (φ.all fun c => decide (c.length ≤ 3)) = false := by simpa using hφ
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      refine ⟨fun h => ?_, fun h => (hφ h).elim⟩
      have := h [(0, true), (0, true), (0, true), (0, true)] (by simp [narrowNo])
      simp at this
  · unfold narrowKernel
    split_ifs <;> omega
  · unfold narrowKernel
    split_ifs
    · have : CNF.numVars ([] : CNF ℕ) = 0 := by decide
      omega
    · have : CNF.numVars narrowNo = 1 := by decide
      omega

example : FPTReducible encCNF encCNF CNF.numVars CNF.numVars Narrow Narrow :=
  isKernelization_narrowKernel.fptReducible

example : Narrow ∈ FPT encCNF CNF.numVars ↔ HasKernel encCNF CNF.numVars Narrow := by
  obtain ⟨k, hk⟩ := mem_P_iff_exists_mem_DTIME.mp narrow_mem_P
  exact mem_FPT_iff_hasKernel hk

/-! ### Vertex cover parameterized by target size -/

/-- The triangle on `{0, 1, 2}`. -/
private def triangle : Graph := ([0, 1, 2], [(0, 1), (1, 2), (0, 2)])

example : VertexCover.search (triangle, 1) = false := by decide

example : VertexCover.search (triangle, 2) = true := by decide

example : VertexCover.search (triangle, 3) = true := by decide

/-- Targets exceeding the number of distinct declared vertices are rejected. -/
example : VertexCover.search (triangle, 4) = false := by decide

example : (triangle, 2) ∈ VertexCover :=
  (VertexCover.search_eq_true_iff (triangle, 2)).mp (by decide)

example : (triangle, 1) ∉ VertexCover := by
  rw [← VertexCover.search_eq_true_iff]
  decide

example : DecidableInExpTime VertexCover (encPair encGraph encNat) Prod.snd 1 :=
  VertexCover_decidableInExpTime_one

example : VertexCover ∈ FPT (encPair encGraph encNat) Prod.snd := VertexCover_mem_FPT

example : HasKernel (encPair encGraph encNat) Prod.snd VertexCover := VertexCover_hasKernel

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.P_subset_FPT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.P_subset_FPT

/--
info: 'Cslib.Complexity.FPT_eq_P_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.FPT_eq_P_of_le

/--
info: 'Cslib.Complexity.XP_eq_P_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.XP_eq_P_of_le

/--
info: 'Cslib.Complexity.DecidableInExpTime.mem_FPT' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.DecidableInExpTime.mem_FPT

/--
info: 'Cslib.Complexity.SAT_mem_FPT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SAT_mem_FPT

/--
info: 'Cslib.Complexity.inter_mem_FPT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.inter_mem_FPT

/--
info: 'Cslib.Complexity.compl_mem_XP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.compl_mem_XP

/--
info: 'Cslib.Complexity.FPTReducible.trans' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.FPTReducible.trans

/--
info: 'Cslib.Complexity.FPTReducible.mem_FPT' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.FPTReducible.mem_FPT

/--
info: 'Cslib.Complexity.FPTReducible.mem_XP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.FPTReducible.mem_XP

/--
info: 'Cslib.Complexity.IsKernelization.mem_FPT' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.IsKernelization.mem_FPT

/--
info: 'Cslib.Complexity.HasKernel.mem_FPT' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.HasKernel.mem_FPT

/--
info: 'Cslib.Complexity.hasKernel_of_mem_FPT' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.hasKernel_of_mem_FPT

/--
info: 'Cslib.Complexity.mem_FPT_iff_hasKernel' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_FPT_iff_hasKernel

/--
info: 'Cslib.Complexity.hasPolyKernel_of_mem_P' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.hasPolyKernel_of_mem_P

/--
info: 'Cslib.Complexity.VertexCover.search_eq_true_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.VertexCover.search_eq_true_iff

/--
info: 'Cslib.Complexity.VertexCover_decidableInExpTime_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.VertexCover_decidableInExpTime_one

/--
info: 'Cslib.Complexity.VertexCover_mem_FPT' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.VertexCover_mem_FPT

/--
info: 'Cslib.Complexity.VertexCover_hasKernel' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.VertexCover_hasKernel

end ComplexityTests.Parameterized
