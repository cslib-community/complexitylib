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
`HasPolyKernel`) and the Cai–Chen–Downey–Fellows equivalence; and `VertexCover` by bounded
search tree.
-/

namespace ComplexityTests.Parameterized

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Satisfiability parameterized by the number of variables -/

/-- A larger parameter: the number of occurrences of variables bounds the number of distinct
variables, placing `SAT` in `FPT` and `SATᶜ` in `XP`. -/
example :
    SAT ∈ FPT encCNF (fun φ => φ.vars.length) ∧
      SATᶜ ∈ XP encCNF (fun φ => φ.vars.length) :=
  ⟨FPT_subset_FPT_of_le_comp (h := id) CNF.numVars_le_length_vars SAT_mem_FPT,
    FPT_subset_XP (compl_mem_FPT
      (FPT_subset_FPT_of_le_comp (h := id) CNF.numVars_le_length_vars SAT_mem_FPT))⟩

/-! ### A problem in `P` -/

/-- The formulas whose clauses have at most three literals. -/
private def Narrow : Set (CNF ℕ) := {φ | ∀ c ∈ φ, c.length ≤ 3}

private theorem narrow_mem_P : Narrow ∈ P encCNF :=
  ⟨_, (computableInPolyTime_all_length_le 3), fun φ => by simp [Narrow]⟩

/-- Every parameter works for a problem in `P`, and 3SAT is the intersection of `Narrow` and `SAT`
so both `KSAT 3` and `Narrow ∪ SAT` lie in `FPT`. -/
example :
    Narrow ∈ FPT encCNF List.length ∧
      KSAT 3 = Narrow ∩ SAT ∧
      KSAT 3 ∈ FPT encCNF CNF.numVars ∧
      Narrow ∪ SAT ∈ FPT encCNF CNF.numVars := by
  refine ⟨P_subset_FPT narrow_mem_P, by ext φ; rfl, ?_,
    union_mem_FPT (P_subset_FPT narrow_mem_P) SAT_mem_FPT⟩
  have : KSAT 3 = Narrow ∩ SAT := Set.ext fun _ => Iff.rfl
  rw [this]
  exact inter_mem_FPT (P_subset_FPT narrow_mem_P) SAT_mem_FPT

/-! ### Bounded parameters -/

/-- Constant-parameter `FPT` and `XP` both collapse to `P`, so they coincide and contain
`Narrow`. -/
example :
    FPT encCNF (fun _ => 7) = XP encCNF (fun _ => 5) ∧
      Narrow ∈ XP encCNF (fun _ => 5) :=
  ⟨(FPT_eq_P_of_le (K := 7) fun _ => le_rfl).trans (XP_eq_P_of_le (K := 5) fun _ => le_rfl).symm,
    (XP_eq_P_of_le (K := 5) fun _ => le_rfl).symm ▸ narrow_mem_P⟩

/-! ### An fpt-reduction from 3SAT to SAT -/

/-- Formulas with clauses of at most three literals are kept; the others go to the empty clause. -/
private def toSAT (φ : CNF ℕ) : CNF ℕ :=
  if φ.all (fun c => decide (c.length ≤ 3)) then φ else [[]]

private theorem toSAT_polyTime : ComputableInPolyTime toSAT encCNF encCNF :=
  ComputableInPolyTime.ite' (computableInPolyTime_all_length_le 3)
    ComputableInPolyTime.id' (ComputableInPolyTime.const _)

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
  FPTReducible.of_computableInPolyTime toSAT_polyTime (h := id) numVars_toSAT_le
    mem_SAT_toSAT

/-- `toSAT` collapses non-3CNF formulas while preserving 3CNF formulas, yielding `ThreeSAT ∈ FPT`,
`ThreeSATᶜ ∈ XP`, and transitive `FPTReducible` closure. -/
example :
    toSAT [[(0, true)], [(0, true), (1, true), (2, true), (3, true)]] = [[]] ∧
      toSAT [[(0, true)], [(0, false), (1, true)]] = [[(0, true)], [(0, false), (1, true)]] ∧
      ThreeSAT ∈ FPT encCNF CNF.numVars ∧
      ThreeSATᶜ ∈ XP encCNF CNF.numVars ∧
      FPTReducible encCNF encCNF CNF.numVars CNF.numVars ThreeSAT SAT :=
  ⟨by decide, by decide,
    threeSAT_fptReducible_SAT.mem_FPT SAT_mem_FPT,
    threeSAT_fptReducible_SAT.compl.mem_XP (FPT_subset_XP (compl_mem_FPT SAT_mem_FPT)),
    threeSAT_fptReducible_SAT.trans (.refl _ _ _)⟩

/-! ### Kernelization -/

/-- A concrete kernelization for `Narrow`: map every narrow formula to `[]` and every other formula
to a single four-literal clause. -/
private def narrowNo : CNF ℕ := [[(0, true), (0, true), (0, true), (0, true)]]

private def narrowKernel (φ : CNF ℕ) : CNF ℕ :=
  if φ.all (fun c => decide (c.length ≤ 3)) then [] else narrowNo

private theorem isKernelization_narrowKernel :
    IsKernelization encCNF CNF.numVars Narrow narrowKernel
      fun _ => (encCNF ([] : CNF ℕ)).length + (encCNF narrowNo).length + 1 := by
  refine ⟨ComputableInPolyTime.ite' (computableInPolyTime_all_length_le 3)
    (ComputableInPolyTime.const []) (ComputableInPolyTime.const narrowNo),
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

example :
    HasKernel encCNF CNF.numVars Narrow ∧
      FPTReducible encCNF encCNF CNF.numVars CNF.numVars Narrow Narrow ∧
      (Narrow ∈ FPT encCNF CNF.numVars ↔ HasKernel encCNF CNF.numVars Narrow) := by
  refine ⟨(hasPolyKernel_of_mem_P narrow_mem_P).hasKernel,
    isKernelization_narrowKernel.fptReducible, ?_⟩
  obtain ⟨k, hk⟩ := mem_P_iff_exists_mem_DTIME.mp narrow_mem_P
  exact mem_FPT_iff_hasKernel hk

/-! ### Vertex cover parameterized by target size -/

/-- The triangle on `{0, 1, 2}`. -/
private def triangle : Graph := ([0, 1, 2], [(0, 1), (1, 2), (0, 2)])

/-- Bounded search tree evaluations and membership witnesses on the triangle graph, plus `XP`
closure for `VertexCoverᶜ`. -/
example :
    VertexCover.search (triangle, 1) = false ∧
      VertexCover.search (triangle, 2) = true ∧
      VertexCover.search (triangle, 3) = true ∧
      VertexCover.search (triangle, 4) = false ∧
      (triangle, 2) ∈ VertexCover ∧
      (triangle, 1) ∉ VertexCover ∧
      VertexCoverᶜ ∈ XP (encPair encGraph encNat) Prod.snd := by
  refine ⟨by decide, by decide, by decide, by decide,
    (VertexCover.search_eq_true_iff (triangle, 2)).mp (by decide), ?_,
    FPT_subset_XP (compl_mem_FPT VertexCover_mem_FPT)⟩
  rw [← VertexCover.search_eq_true_iff]
  decide

end ComplexityTests.Parameterized
