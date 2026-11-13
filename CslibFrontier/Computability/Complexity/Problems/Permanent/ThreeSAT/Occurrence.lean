/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT.Construction
public import Mathlib.Data.List.GetD

/-!
# Occurrences and tracks of the 3CNF matrix

Basic facts about the construction of
`CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT.Construction` for a
well-formed formula: the padded literals of a clause are exactly its literals, every variable
occurs, first and next occurrences are characterized by minimality, the entry and exit indices
are distinct vertices, and the track edges stay among the vertices.
-/

public section

namespace Cslib.Complexity.PermanentThreeSAT

open Cslib.Logic.PL

variable {φ : CNF ℕ}

/-- The padded literals of a clause belong to it. -/
theorem litAt_mem (hφ : WellFormed φ) {o : ℕ} (ho : o < numOcc φ) :
    litAt φ o ∈ φ[o / 3]'(by unfold numOcc at ho; omega) := by
  have hj : o / 3 < φ.length := by unfold numOcc at ho; omega
  have hc := hφ _ (List.getElem_mem hj)
  rw [litAt, List.getD_eq_getElem _ _ hj]
  have hp : min (o % 3) ((φ[o / 3]).length - 1) < (φ[o / 3]).length := by omega
  rw [List.getD_eq_getElem _ _ hp]
  exact List.getElem_mem hp

/-- Every literal of a clause is a padded literal of it. -/
theorem exists_litAt_eq (hφ : WellFormed φ) {j : ℕ} (hj : j < φ.length) {l : Literal ℕ}
    (hl : l ∈ φ[j]) : ∃ p < 3, litAt φ (3 * j + p) = l := by
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hl
  have hc := hφ _ (List.getElem_mem hj)
  refine ⟨p, by omega, ?_⟩
  have h1 : (3 * j + p) / 3 = j := by omega
  have h2 : (3 * j + p) % 3 = p := by omega
  have h3 : min p ((φ[j]).length - 1) = p := by omega
  rw [litAt, h1, h2, List.getD_eq_getElem _ _ hj, h3, List.getD_eq_getElem _ _ hp]

/-- The variable of an occurrence is listed. -/
theorem fst_litAt_mem_varList (hφ : WellFormed φ) {o : ℕ} (ho : o < numOcc φ) :
    (litAt φ o).1 ∈ varList φ := by
  rw [varList, CNF.mem_distinctVars, CNF.mem_vars]
  exact ⟨_, List.getElem_mem _, (litAt φ o).2, litAt_mem hφ ho⟩

/-- Every listed variable occurs. -/
theorem exists_occ_of_mem_varList (hφ : WellFormed φ) {x : ℕ} (hx : x ∈ varList φ) :
    ∃ o < numOcc φ, (litAt φ o).1 = x := by
  rw [varList, CNF.mem_distinctVars, CNF.mem_vars] at hx
  obtain ⟨c, hc, b, hb⟩ := hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨p, hp, hl⟩ := exists_litAt_eq hφ hj hb
  exact ⟨3 * j + p, by unfold numOcc; omega, by rw [hl]⟩

theorem varList_nodup (φ : CNF ℕ) : (varList φ).Nodup := CNF.nodup_distinctVars _

/-- The listed variable at its index. -/
theorem getD_varList_idxOf {x : ℕ} (hx : x ∈ varList φ) :
    (varList φ).getD ((varList φ).idxOf x) 0 = x := by
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.2 hx), List.getElem_idxOf]

/-- The index of the listed variable at an index. -/
theorem idxOf_getD_varList {i : ℕ} (hi : i < numAux φ) :
    (varList φ).idxOf ((varList φ).getD i 0) = i := by
  unfold numAux at hi
  rw [List.getD_eq_getElem _ _ hi, (varList_nodup φ).idxOf_getElem]

theorem getD_varList_mem {i : ℕ} (hi : i < numAux φ) : (varList φ).getD i 0 ∈ varList φ := by
  unfold numAux at hi
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-! ### First and next occurrences -/

theorem firstOcc_eq_some {ℓ : Literal ℕ} {o : ℕ} :
    firstOcc φ ℓ = some o ↔ o < numOcc φ ∧ litAt φ o = ℓ ∧ ∀ o' < o, litAt φ o' ≠ ℓ := by
  simp only [firstOcc, List.find?_range_eq_some, beq_iff_eq, List.mem_range, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq]
  tauto

theorem firstOcc_eq_none {ℓ : Literal ℕ} :
    firstOcc φ ℓ = none ↔ ∀ o < numOcc φ, litAt φ o ≠ ℓ := by
  simp [firstOcc]

theorem nextOcc_eq_some {o o' : ℕ} :
    nextOcc φ o = some o' ↔ o' < numOcc φ ∧ o < o' ∧ litAt φ o' = litAt φ o ∧
      ∀ o'' < o', o < o'' → litAt φ o'' ≠ litAt φ o := by
  simp only [nextOcc, List.find?_range_eq_some, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.mem_range, Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq,
    beq_eq_false_iff_ne, ne_eq]
  tauto

theorem nextOcc_eq_none {o : ℕ} :
    nextOcc φ o = none ↔ ∀ o' < numOcc φ, o < o' → litAt φ o' ≠ litAt φ o := by
  simp only [nextOcc, List.find?_range_eq_none, Bool.not_eq_true', Bool.and_eq_false_imp,
    decide_eq_true_eq, beq_eq_false_iff_ne, ne_eq]

/-- An occurrence that is not the first of its literal has a predecessor whose next occurrence
it is. -/
theorem exists_nextOcc_eq {o : ℕ} (ho : o < numOcc φ)
    (h : ∃ o' < o, litAt φ o' = litAt φ o) :
    ∃ o' < o, litAt φ o' = litAt φ o ∧ nextOcc φ o' = some o := by
  classical
  let P : ℕ → Prop := fun o' => o' < o ∧ litAt φ o' = litAt φ o
  obtain ⟨o₀, ho₀, hl₀⟩ := h
  have hex : ∃ o', P o' := ⟨o₀, ho₀, hl₀⟩
  let g := Nat.findGreatest P o
  have hg : P g := Nat.findGreatest_spec (P := P) (m := o₀) ho₀.le ⟨ho₀, hl₀⟩
  refine ⟨g, hg.1, hg.2, nextOcc_eq_some.2 ⟨ho, hg.1, hg.2.symm, fun o'' ho'' hgo'' hl => ?_⟩⟩
  exact Nat.findGreatest_is_greatest (P := P) hgo'' ho''.le ⟨ho'', hl.trans hg.2⟩

/-! ### Vertex indices -/

theorem entryIdx_injective (φ : CNF ℕ) : Function.Injective (entryIdx φ) := by
  intro o o' h
  unfold entryIdx at h
  omega

theorem exitIdx_injective (φ : CNF ℕ) : Function.Injective (exitIdx φ) := by
  intro o o' h
  unfold exitIdx at h
  omega

theorem entryIdx_ne_exitIdx (φ : CNF ℕ) (o o' : ℕ) : entryIdx φ o ≠ exitIdx φ o' := by
  unfold entryIdx exitIdx
  omega

theorem numAux_le_entryIdx (φ : CNF ℕ) (o : ℕ) : numAux φ ≤ entryIdx φ o := by
  unfold entryIdx; omega

theorem numAux_le_exitIdx (φ : CNF ℕ) (o : ℕ) : numAux φ ≤ exitIdx φ o := by
  unfold exitIdx; omega

theorem entryIdx_lt_size {o : ℕ} (ho : o < numOcc φ) : entryIdx φ o < size φ := by
  unfold entryIdx size; unfold numOcc at ho; omega

theorem exitIdx_lt_size {o : ℕ} (ho : o < numOcc φ) : exitIdx φ o < size φ := by
  unfold exitIdx size; unfold numOcc at ho; omega

theorem exitOcc_exitIdx (φ : CNF ℕ) (o : ℕ) : exitOcc φ (exitIdx φ o) = o := by
  unfold exitOcc exitIdx; omega

/-- A vertex in an exit position is the exit of an occurrence. -/
theorem exitIdx_exitOcc {k : ℕ} (hk : numAux φ ≤ k) (h3 : 3 ≤ (k - numAux φ) % 8)
    (h6 : (k - numAux φ) % 8 < 6) : exitIdx φ (exitOcc φ k) = k := by
  unfold exitOcc exitIdx; omega

theorem exitOcc_lt {k : ℕ} (hn : numAux φ ≤ k) (hk : k < size φ) (h6 : (k - numAux φ) % 8 < 6) :
    exitOcc φ k < numOcc φ := by
  unfold exitOcc numOcc; unfold size at hk; omega

/-! ### Track edges -/

theorem auxSucc_eq_some {i : ℕ} {b : Bool} {o : ℕ}
    (h : firstOcc φ ((varList φ).getD i 0, b) = some o) : auxSucc φ i b = entryIdx φ o := by
  unfold auxSucc; rw [h]

theorem auxSucc_eq_none {i : ℕ} {b : Bool} (h : firstOcc φ ((varList φ).getD i 0, b) = none) :
    auxSucc φ i b = i := by
  unfold auxSucc; rw [h]

theorem exitSucc_eq_some {o o' : ℕ} (h : nextOcc φ o = some o') :
    exitSucc φ o = entryIdx φ o' := by
  unfold exitSucc; rw [h]

theorem exitSucc_eq_none {o : ℕ} (h : nextOcc φ o = none) :
    exitSucc φ o = (varList φ).idxOf (litAt φ o).1 := by
  unfold exitSucc; rw [h]

theorem auxSucc_lt_size {i : ℕ} (hi : i < numAux φ) (b : Bool) : auxSucc φ i b < size φ := by
  rcases h : firstOcc φ ((varList φ).getD i 0, b) with _ | o
  · rw [auxSucc_eq_none h]; unfold size; omega
  · rw [auxSucc_eq_some h]; exact entryIdx_lt_size (firstOcc_eq_some.1 h).1

theorem exitSucc_lt_size (hφ : WellFormed φ) {o : ℕ} (ho : o < numOcc φ) :
    exitSucc φ o < size φ := by
  rcases h : nextOcc φ o with _ | o'
  · rw [exitSucc_eq_none h]
    have := List.idxOf_lt_length_iff.2 (fst_litAt_mem_varList hφ ho)
    unfold size; unfold numAux; omega
  · rw [exitSucc_eq_some h]; exact entryIdx_lt_size (nextOcc_eq_some.1 h).1

/-- The two track edges leaving an auxiliary vertex have different heads. -/
theorem auxSucc_true_ne_false (hφ : WellFormed φ) {i : ℕ} (hi : i < numAux φ) :
    auxSucc φ i true ≠ auxSucc φ i false := by
  obtain ⟨o, ho, hx⟩ := exists_occ_of_mem_varList hφ (getD_varList_mem hi)
  have key : ∀ b, firstOcc φ ((varList φ).getD i 0, b) ≠ none →
      ∀ o₁, firstOcc φ ((varList φ).getD i 0, b) = some o₁ →
      auxSucc φ i (!b) ≠ entryIdx φ o₁ := by
    intro b _ o₁ h₁ h
    rcases h₂ : firstOcc φ ((varList φ).getD i 0, !b) with _ | o₂
    · rw [auxSucc_eq_none h₂] at h
      have := numAux_le_entryIdx φ o₁
      omega
    · rw [auxSucc_eq_some h₂] at h
      have := entryIdx_injective φ h
      subst this
      have e := (firstOcc_eq_some.1 h₁).2.1
      rw [(firstOcc_eq_some.1 h₂).2.1] at e
      simp at e
  have hb : firstOcc φ ((varList φ).getD i 0, (litAt φ o).2) ≠ none := by
    rw [ne_eq, firstOcc_eq_none]
    exact fun h => h o ho (by rw [← hx])
  obtain ⟨o₁, h₁⟩ := Option.ne_none_iff_exists'.1 hb
  have h1 := auxSucc_eq_some h₁
  have h2 := key _ hb o₁ h₁
  cases hb' : (litAt φ o).2
  · rw [hb'] at h1 h2; simp only [Bool.not_false] at h2; rw [h1]; exact h2
  · rw [hb'] at h1 h2; simp only [Bool.not_true] at h2; rw [h1]; exact fun h => h2 h.symm

end Cslib.Complexity.PermanentThreeSAT
