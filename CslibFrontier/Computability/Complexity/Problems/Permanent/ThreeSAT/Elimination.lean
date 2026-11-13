/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT.Gadget
public import CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT.Tracks
public import CslibFrontier.Logics.Propositional.CNF.ModelCount

/-!
# The permanent of the 3CNF matrix

For a well-formed formula `φ` with `m` clauses, the clause gadgets of the matrix of `φ` are
eliminated one at a time (`PermanentGadget.permOn_gadget_add`), each contributing a factor `12`
and a choice of a nonempty set of its literals. After all `m` gadgets, what remains is the track
matrix between the auxiliary vertices with the exits and with the entries of the chosen
occurrences, which counts the assignments whose true occurrences are exactly the chosen ones
(`permOn_trackMatrix`). Summing over the choices in which every clause has a chosen literal
gives the satisfying assignments: `permanent_fullMatrix` proves
`(fullMatrix φ).permanent = 12 ^ m * φ.modelCount`. This is Goldreich's argument for
Proposition 6.21 [Goldreich, Section 6.2.1][Goldreich2007Draft], carried out on matrices.

## Main results

* `Cslib.Complexity.PermanentThreeSAT.permanent_fullMatrix`: the permanent of the matrix of a
  well-formed formula is `12 ^ m` times its number of satisfying assignments.
-/

@[expose] public section

open Finset Matrix

namespace Cslib.Complexity.PermanentThreeSAT

open Cslib.Logic.PL PermanentGadget

variable {φ : CNF ℕ}

/-- The matrix of `φ` on its vertices. -/
def fullMatrix (φ : CNF ℕ) : Matrix (Fin (size φ)) (Fin (size φ)) ℤ :=
  fun k l => matrixEntry φ k l

/-- The gadget entries of the clauses from `k` on. -/
def gadgetFrom (φ : CNF ℕ) (k u v : ℕ) : ℤ :=
  if numAux φ ≤ u ∧ numAux φ ≤ v ∧ (u - numAux φ) / 8 = (v - numAux φ) / 8 ∧
      k ≤ (u - numAux φ) / 8 then
    gadgetEntry ((u - numAux φ) % 8) ((v - numAux φ) % 8)
  else 0

/-- The gadget entries of clause `k`. -/
def gadgetAt (φ : CNF ℕ) (k u v : ℕ) : ℤ :=
  if numAux φ ≤ u ∧ numAux φ ≤ v ∧ (u - numAux φ) / 8 = k ∧ (v - numAux φ) / 8 = k then
    gadgetEntry ((u - numAux φ) % 8) ((v - numAux φ) % 8)
  else 0

/-- The gadget of clause `k`, as a matrix. -/
def gadgetMat (φ : CNF ℕ) (k : ℕ) : Matrix (Fin (size φ)) (Fin (size φ)) ℤ :=
  fun u v => gadgetAt φ k u v

/-- The matrix after the gadgets of the clauses before `k` are eliminated. -/
def stageMatrix (φ : CNF ℕ) (k : ℕ) : Matrix (Fin (size φ)) (Fin (size φ)) ℤ :=
  fun u v => gadgetFrom φ k u v + trackEntry φ u v

/-- The vertices of the gadget of clause `k`. -/
def gadgetEmb (φ : CNF ℕ) (k : ℕ) (hk : k < φ.length) : Fin 8 ↪ Fin (size φ) :=
  ⟨fun a => ⟨numAux φ + 8 * k + a, by unfold size; omega⟩, fun a b h => by
    simp only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩

/-- The rows after eliminating the gadgets before `k`, keeping the exits of `P`. -/
def stageRows (φ : CNF ℕ) (k : ℕ) (P : Finset ℕ) : Finset (Fin (size φ)) :=
  univ.filter fun u => u.val < numAux φ ∨ k ≤ (u.val - numAux φ) / 8 ∨ ∃ o ∈ P, u.val = exitIdx φ o

/-- The columns after eliminating the gadgets before `k`, keeping the entries of `P`. -/
def stageCols (φ : CNF ℕ) (k : ℕ) (P : Finset ℕ) : Finset (Fin (size φ)) :=
  univ.filter fun u =>
    u.val < numAux φ ∨ k ≤ (u.val - numAux φ) / 8 ∨ ∃ o ∈ P, u.val = entryIdx φ o

/-- The occurrences `P` meet every clause before `k`. -/
def Covers (k : ℕ) (P : Finset ℕ) : Prop := ∀ j < k, ∃ p < 3, 3 * j + p ∈ P

instance (k : ℕ) : DecidablePred (Covers k) := fun _ => by unfold Covers; infer_instance

/-- The choices of literal sets for the clauses before `k`: occurrences below `3 k` meeting every
clause before `k`. -/
def stageChoices (k : ℕ) : Finset (Finset ℕ) :=
  (range (3 * k)).powerset.filter (Covers k)

theorem fullMatrix_eq_stageMatrix_zero : fullMatrix φ = stageMatrix φ 0 := by
  funext u v
  simp only [fullMatrix, stageMatrix, matrixEntry, gadgetPart, gadgetFrom, Nat.zero_le, and_true]

theorem gadgetFrom_succ (k u v : ℕ) :
    gadgetFrom φ k u v = gadgetAt φ k u v + gadgetFrom φ (k + 1) u v := by
  unfold gadgetFrom gadgetAt
  split_ifs <;> first | (exfalso; omega) | simp

theorem stageMatrix_succ {k : ℕ} :
    stageMatrix φ k = gadgetMat φ k + stageMatrix φ (k + 1) := by
  funext u v
  simp only [stageMatrix, gadgetMat, Matrix.add_apply]
  rw [gadgetFrom_succ, add_assoc]

theorem stageMatrix_length : stageMatrix φ φ.length = trackMatrix φ := by
  funext u v
  have := u.2
  unfold size at this
  simp only [stageMatrix, gadgetFrom, trackMatrix]
  rw [ite_eq_right (by omega), zero_add]

/-- Track edges never end at a gadget vertex that is not an entry. -/
theorem trackEntry_eq_zero_of_not_entry (u : ℕ) {l : ℕ} (hl : numAux φ < l)
    (hne : ∀ o, l ≠ entryIdx φ o) : trackEntry φ u l = 0 := by
  have hidx : ∀ x, (varList φ).idxOf x ≠ l := fun x h => by
    have := List.idxOf_le_length (a := x) (l := varList φ)
    unfold numAux at hl; omega
  have haux : ∀ b, auxSucc φ u b ≠ l ∨ u ≥ numAux φ := fun b => by
    by_cases hu : u < numAux φ
    · left
      rcases h : firstOcc φ ((varList φ).getD u 0, b) with _ | o
      · rw [auxSucc_eq_none h]; omega
      · rw [auxSucc_eq_some h]; exact fun e => hne o e.symm
    · right; omega
  have hex : ∀ o, exitSucc φ o ≠ l := fun o => by
    rcases h : nextOcc φ o with _ | o'
    · rw [exitSucc_eq_none h]; exact hidx _
    · rw [exitSucc_eq_some h]; exact fun e => hne o' e.symm
  by_cases hu : u < numAux φ
  · rw [trackEntry_aux hu]
    have ht := (haux true).resolve_right (by omega)
    have hf := (haux false).resolve_right (by omega)
    simp [ht, hf]
  · unfold trackEntry
    rw [ite_eq_right hu]
    split_ifs with h h'
    · exact absurd h' (hex _)
    · rfl
    · rfl

theorem gadgetEmb_val {k : ℕ} (hk : k < φ.length) (a : Fin 8) :
    (gadgetEmb φ k hk a).val = numAux φ + 8 * k + a := rfl

section Step

variable {k : ℕ} (hk : k < φ.length)

theorem gadgetAt_emb (a b : Fin 8) :
    gadgetMat φ k (gadgetEmb φ k hk a) (gadgetEmb φ k hk b) = gadget a b := by
  simp only [gadgetMat, gadgetAt, gadget]
  rw [ite_eq_left (by simp only [gadgetEmb_val]; omega)]
  congr 2 <;> rw [gadgetEmb_val] <;> omega

theorem gadgetAt_row (u : Fin (size φ)) (hu : ∀ a, u ≠ gadgetEmb φ k hk a) (v : Fin (size φ)) :
    gadgetMat φ k u v = 0 := by
  unfold gadgetMat gadgetAt
  rw [ite_eq_right]
  intro h
  refine hu ⟨(u.val - numAux φ) % 8, by omega⟩ (Fin.ext ?_)
  rw [gadgetEmb_val]
  simp only
  omega

theorem gadgetAt_col (v : Fin (size φ)) (hv : ∀ b, v ≠ gadgetEmb φ k hk b) (u : Fin (size φ)) :
    gadgetMat φ k u v = 0 := by
  unfold gadgetMat gadgetAt
  rw [ite_eq_right]
  intro h
  refine hv ⟨(v.val - numAux φ) % 8, by omega⟩ (Fin.ext ?_)
  rw [gadgetEmb_val]
  simp only
  omega

theorem stageMatrix_succ_row (a : Fin 8) (ha : ∀ p, a ≠ exitE p) (v : Fin (size φ)) :
    stageMatrix φ (k + 1) (gadgetEmb φ k hk a) v = 0 := by
  have ha' : a.val < 3 ∨ 6 ≤ a.val := by
    by_contra h
    exact ha ⟨a.val - 3, by omega⟩ (Fin.ext (by
      change a.val = a.val - 3 + 3
      omega))
  simp only [stageMatrix, gadgetFrom]
  rw [ite_eq_right (by simp only [gadgetEmb_val]; omega), zero_add, trackEntry,
    ite_eq_right (by simp only [gadgetEmb_val]; omega),
    ite_eq_right (by simp only [gadgetEmb_val]; omega)]

theorem stageMatrix_succ_col (b : Fin 8) (hb : ∀ p, b ≠ entryE p) (u : Fin (size φ)) :
    stageMatrix φ (k + 1) u (gadgetEmb φ k hk b) = 0 := by
  have hb' : 3 ≤ b.val := by
    by_contra h
    exact hb ⟨b.val, by omega⟩ (Fin.ext rfl)
  simp only [stageMatrix, gadgetFrom]
  rw [ite_eq_right (by simp only [gadgetEmb_val]; omega), zero_add]
  refine trackEntry_eq_zero_of_not_entry _ (by rw [gadgetEmb_val]; omega) fun o h => ?_
  rw [gadgetEmb_val] at h
  unfold entryIdx at h
  omega

theorem mem_gadget (u : Fin (size φ)) :
    u ∈ univ.map (gadgetEmb φ k hk) ↔ numAux φ ≤ u.val ∧ (u.val - numAux φ) / 8 = k := by
  have hu := u.2
  unfold size at hu
  simp only [mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    rw [gadgetEmb_val]
    omega
  · intro h
    exact ⟨⟨(u.val - numAux φ) % 8, by omega⟩, Fin.ext (by rw [gadgetEmb_val]; simp only; omega)⟩

theorem mem_gadgetExits (Q : Finset (Fin 3)) (u : Fin (size φ)) :
    u ∈ (Q.map exitE).map (gadgetEmb φ k hk) ↔ ∃ p ∈ Q, u.val = exitIdx φ (3 * k + p.val) := by
  simp only [mem_map]
  constructor
  · rintro ⟨b, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨p, hp, ?_⟩
    rw [gadgetEmb_val]
    change numAux φ + 8 * k + (p.val + 3) = _
    unfold exitIdx
    omega
  · rintro ⟨p, hp, he⟩
    refine ⟨exitE p, ⟨p, hp, rfl⟩, Fin.ext ?_⟩
    rw [gadgetEmb_val, he]
    change numAux φ + 8 * k + (p.val + 3) = _
    unfold exitIdx
    omega

theorem mem_gadgetEntries (Q : Finset (Fin 3)) (u : Fin (size φ)) :
    u ∈ (Q.map entryE).map (gadgetEmb φ k hk) ↔ ∃ p ∈ Q, u.val = entryIdx φ (3 * k + p.val) := by
  simp only [mem_map]
  constructor
  · rintro ⟨b, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨p, hp, ?_⟩
    rw [gadgetEmb_val]
    change numAux φ + 8 * k + p.val = _
    unfold entryIdx
    omega
  · rintro ⟨p, hp, he⟩
    refine ⟨entryE p, ⟨p, hp, rfl⟩, Fin.ext ?_⟩
    rw [gadgetEmb_val, he]
    change numAux φ + 8 * k + p.val = _
    unfold entryIdx
    omega

/-- The kept vertices after eliminating the gadgets before `k`, keeping the vertices `idx o` of the
occurrences `o ∈ P`; `stageRows` and `stageCols` are the instances `idx = exitIdx φ` and
`idx = entryIdx φ`. -/
private def stageSet (φ : CNF ℕ) (idx : ℕ → ℕ) (k : ℕ) (P : Finset ℕ) : Finset (Fin (size φ)) :=
  univ.filter fun u => u.val < numAux φ ∨ k ≤ (u.val - numAux φ) / 8 ∨ ∃ o ∈ P, u.val = idx o

/-- The common set decomposition behind `stageRows_step` and `stageCols_step`: replacing the
`k`-th gadget by its vertices `idx (3 * k + p)`, `p ∈ Q`, extends the kept occurrences by those of
the `k`-th clause, provided `idx o` lies in the gadget of clause `o / 3`. -/
private theorem stage_step (idx : ℕ → ℕ)
    (hidx : ∀ o, numAux φ ≤ idx o ∧ (idx o - numAux φ) / 8 = o / 3)
    {G E : Finset (Fin (size φ))} {P : Finset ℕ} (hP : P ⊆ range (3 * k)) {Q : Finset (Fin 3)}
    (hG : ∀ u, u ∈ G ↔ numAux φ ≤ u.val ∧ (u.val - numAux φ) / 8 = k)
    (hE : ∀ u, u ∈ E ↔ ∃ p ∈ Q, u.val = idx (3 * k + p.val)) :
    stageSet φ idx k P \ G ∪ E =
      stageSet φ idx (k + 1) (P ∪ Q.image fun p : Fin 3 => 3 * k + p.val) := by
  ext u
  rw [mem_union, mem_sdiff, hG, hE]
  simp only [stageSet, mem_filter, mem_univ, true_and, mem_union, mem_image]
  constructor
  · rintro (⟨h | h | ⟨o, ho, he⟩, hnot⟩ | ⟨p, hp, he⟩)
    · exact Or.inl h
    · by_cases hun : u.val < numAux φ
      · exact Or.inl hun
      · right; left; omega
    · exact Or.inr (Or.inr ⟨o, Or.inl ho, he⟩)
    · exact Or.inr (Or.inr ⟨3 * k + p.val, Or.inr ⟨p, hp, rfl⟩, he⟩)
  · rintro (h | h | ⟨o, ho | ⟨p, hp, rfl⟩, he⟩)
    · exact Or.inl ⟨Or.inl h, by omega⟩
    · exact Or.inl ⟨Or.inr (Or.inl (by omega)), by omega⟩
    · have := mem_range.1 (hP ho)
      have := hidx o
      have : o / 3 < k := by omega
      exact Or.inl ⟨Or.inr (Or.inr ⟨o, ho, he⟩), by omega⟩
    · exact Or.inr ⟨p, hp, he⟩

theorem stageRows_step {P : Finset ℕ} (hP : P ⊆ range (3 * k)) (Q : Finset (Fin 3)) :
    stageRows φ k P \ univ.map (gadgetEmb φ k hk) ∪ (Q.map exitE).map (gadgetEmb φ k hk) =
      stageRows φ (k + 1) (P ∪ Q.image fun p : Fin 3 => 3 * k + p.val) :=
  stage_step (exitIdx φ) (fun o => by unfold exitIdx; omega) hP (mem_gadget hk)
    (mem_gadgetExits hk Q)

theorem stageCols_step {P : Finset ℕ} (hP : P ⊆ range (3 * k)) (Q : Finset (Fin 3)) :
    stageCols φ k P \ univ.map (gadgetEmb φ k hk) ∪ (Q.map entryE).map (gadgetEmb φ k hk) =
      stageCols φ (k + 1) (P ∪ Q.image fun p : Fin 3 => 3 * k + p.val) :=
  stage_step (entryIdx φ) (fun o => by unfold entryIdx; omega) hP (mem_gadget hk)
    (mem_gadgetEntries hk Q)

theorem gadget_subset_stageRows (P : Finset ℕ) :
    univ.map (gadgetEmb φ k hk) ⊆ stageRows φ k P := fun u hu => by
  rw [mem_gadget] at hu
  simp only [stageRows, mem_filter, mem_univ, true_and]
  right; left; omega

theorem gadget_subset_stageCols (P : Finset ℕ) :
    univ.map (gadgetEmb φ k hk) ⊆ stageCols φ k P := fun u hu => by
  rw [mem_gadget] at hu
  simp only [stageCols, mem_filter, mem_univ, true_and]
  right; left; omega

include hk in
/-- One elimination step. -/
theorem permOn_stage_succ {P : Finset ℕ} (hP : P ⊆ range (3 * k)) :
    permOn (stageMatrix φ k) (stageRows φ k P) (stageCols φ k P) =
      12 * ∑ Q ∈ univ.filter fun Q : Finset (Fin 3) => Q.Nonempty,
        permOn (stageMatrix φ (k + 1))
          (stageRows φ (k + 1) (P ∪ Q.image fun p : Fin 3 => 3 * k + p.val))
          (stageCols φ (k + 1) (P ∪ Q.image fun p : Fin 3 => 3 * k + p.val)) := by
  rw [stageMatrix_succ, permOn_gadget_add (gadgetEmb φ k hk) _ _ (gadgetAt_emb hk)
    (fun u hu v => gadgetAt_row hk u hu v) (fun v hv u => gadgetAt_col hk v hv u)
    (fun a ha v => stageMatrix_succ_row hk a ha v) (fun b hb u => stageMatrix_succ_col hk b hb u)
    (gadget_subset_stageRows hk P) (gadget_subset_stageCols hk P)]
  refine congrArg _ (sum_congr rfl fun Q _ => ?_)
  rw [stageRows_step hk hP, stageCols_step hk hP]

end Step

theorem stageChoices_succ (k : ℕ) :
    stageChoices (k + 1) =
      (stageChoices k ×ˢ univ.filter fun Q : Finset (Fin 3) => Q.Nonempty).image
      fun x => x.1 ∪ x.2.image fun p : Fin 3 => 3 * k + p.val := by
  ext P'
  simp only [stageChoices, Covers, mem_filter, mem_powerset, mem_image, mem_product, mem_univ,
    true_and]
  constructor
  · rintro ⟨hsub, hcov⟩
    refine ⟨(P'.filter (· < 3 * k), univ.filter fun p : Fin 3 => 3 * k + p ∈ P'),
      ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro o ho; simp only [mem_filter] at ho; exact mem_range.2 ho.2
    · intro j hj
      obtain ⟨p, hp, hm⟩ := hcov j (by omega)
      exact ⟨p, hp, mem_filter.2 ⟨hm, by omega⟩⟩
    · obtain ⟨p, hp, hm⟩ := hcov k (by omega)
      exact ⟨⟨p, hp⟩, by simpa using hm⟩
    · ext o
      simp only [mem_union, mem_filter, mem_image, mem_univ, true_and]
      constructor
      · rintro (⟨h, -⟩ | ⟨p, hp, rfl⟩)
        · exact h
        · exact hp
      · intro ho
        have := mem_range.1 (hsub ho)
        by_cases hlt : o < 3 * k
        · exact Or.inl ⟨ho, hlt⟩
        · exact Or.inr ⟨⟨o - 3 * k, by omega⟩, by simpa [show 3 * k + (o - 3 * k) = o by omega]
            using ho, by simp; omega⟩
  · rintro ⟨⟨P, Q⟩, ⟨⟨hsub, hcov⟩, hQ⟩, rfl⟩
    refine ⟨fun o ho => ?_, fun j hj => ?_⟩
    · rcases mem_union.1 ho with h | h
      · have := mem_range.1 (hsub h); exact mem_range.2 (by omega)
      · obtain ⟨p, -, rfl⟩ := mem_image.1 h; exact mem_range.2 (by omega)
    · by_cases hjk : j < k
      · obtain ⟨p, hp, hm⟩ := hcov j hjk
        exact ⟨p, hp, mem_union_left _ hm⟩
      · obtain ⟨p, hp⟩ := hQ
        refine ⟨p, p.2, mem_union_right _ (mem_image.2 ⟨p, hp, ?_⟩)⟩
        rw [show j = k by omega]

/-- After eliminating the gadgets of the first `k` clauses. -/
theorem permanent_fullMatrix_stage {k : ℕ} (hk : k ≤ φ.length) :
    (fullMatrix φ).permanent = 12 ^ k * ∑ P ∈ stageChoices k,
      permOn (stageMatrix φ k) (stageRows φ k P) (stageCols φ k P) := by
  induction k with
  | zero =>
    have h0 : stageChoices 0 = {∅} := by
      ext P
      simp [stageChoices, Covers]
    have hR : stageRows φ 0 ∅ = univ := by
      ext u; simp [stageRows]
    have hC : stageCols φ 0 ∅ = univ := by
      ext u; simp [stageCols]
    rw [h0, sum_singleton, hR, hC, pow_zero, one_mul, ← fullMatrix_eq_stageMatrix_zero,
      permanent_eq_permOn]
  | succ k ih =>
    have hk' : k < φ.length := by omega
    rw [ih (by omega), stageChoices_succ, sum_image, sum_product, pow_succ, mul_assoc]
    · congr 1
      rw [mul_sum]
      refine sum_congr rfl fun P hP => ?_
      have hPsub : P ⊆ range (3 * k) := (mem_powerset.1 (mem_filter.1 hP).1)
      exact permOn_stage_succ hk' hPsub
    · rintro ⟨P₁, Q₁⟩ h₁ ⟨P₂, Q₂⟩ h₂ h
      simp only [coe_product, Set.mem_prod, mem_coe, stageChoices, Covers, mem_filter,
        mem_powerset] at h₁ h₂
      simp only at h
      have hsplit : ∀ (P : Finset ℕ) (Q : Finset (Fin 3)), P ⊆ range (3 * k) →
          (P ∪ Q.image fun p : Fin 3 => 3 * k + p.val).filter (· < 3 * k) = P ∧
          univ.filter (fun p : Fin 3 => 3 * k + p ∈ P ∪ Q.image fun p : Fin 3 => 3 * k + p.val) =
            Q := by
        intro P Q hP
        constructor
        · ext o
          simp only [mem_filter, mem_union, mem_image]
          constructor
          · rintro ⟨h | ⟨p, -, rfl⟩, hlt⟩
            · exact h
            · omega
          · intro h; exact ⟨Or.inl h, mem_range.1 (hP h)⟩
        · ext p
          simp only [mem_filter, mem_univ, true_and, mem_union, mem_image]
          constructor
          · rintro (h | ⟨q, hq, he⟩)
            · have := mem_range.1 (hP h); omega
            · rwa [Fin.ext (by omega : q.val = p.val)] at hq
          · intro h; exact Or.inr ⟨p, h, rfl⟩
      obtain ⟨e₁, f₁⟩ := hsplit P₁ Q₁ h₁.1.1
      obtain ⟨e₂, f₂⟩ := hsplit P₂ Q₂ h₂.1.1
      rw [h] at e₁ f₁
      exact Prod.ext (e₁.symm.trans e₂) (f₁.symm.trans f₂)

/-- After all gadgets are eliminated. -/
theorem permanent_fullMatrix_tracks (hφ : WellFormed φ) :
    (fullMatrix φ).permanent = 12 ^ φ.length * ∑ P ∈ stageChoices φ.length,
      ((univ : Finset (Fin (numAux φ) → Bool)).filter (TrueExactly φ P)).card := by
  rw [permanent_fullMatrix_stage le_rfl, stageMatrix_length]
  push_cast
  congr 1
  refine sum_congr rfl fun P hP => ?_
  have hPsub : P ⊆ range (numOcc φ) := mem_powerset.1 (mem_filter.1 hP).1
  have hR : stageRows φ φ.length P = rowSet φ P := by
    ext u; have := u.2; unfold size at this
    rw [stageRows, rowSet, mem_filter, mem_filter]
    simp only [mem_univ, true_and]
    unfold InRows
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · omega
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  have hC : stageCols φ φ.length P = colSet φ P := by
    ext u; have := u.2; unfold size at this
    rw [stageCols, colSet, mem_filter, mem_filter]
    simp only [mem_univ, true_and]
    unfold InCols
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · omega
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  rw [hR, hC, permOn_trackMatrix hφ hPsub]

/-- Every clause has a true padded literal. -/
def SatOcc (φ : CNF ℕ) (a : Fin (numAux φ) → Bool) : Prop :=
  ∀ j < φ.length, ∃ p < 3, Literal.eval (assignVal φ a) (litAt φ (3 * j + p)) = true

instance : DecidablePred (SatOcc φ) := fun _ => by unfold SatOcc; infer_instance

theorem sum_card_trueExactly :
    ∑ P ∈ stageChoices φ.length,
      ((univ : Finset (Fin (numAux φ) → Bool)).filter (TrueExactly φ P)).card =
      ((univ : Finset (Fin (numAux φ) → Bool)).filter (SatOcc φ)).card := by
  classical
  let g : (Fin (numAux φ) → Bool) → Finset ℕ := fun a =>
    (range (numOcc φ)).filter fun o => Literal.eval (assignVal φ a) (litAt φ o) = true
  rw [card_eq_sum_card_fiberwise (f := g) (t := stageChoices φ.length)]
  · refine sum_congr rfl fun P hP => ?_
    simp only [stageChoices, Covers, mem_filter, mem_powerset] at hP
    congr 1
    ext a
    simp only [mem_filter, mem_univ, true_and, TrueExactly, g]
    constructor
    swap
    · rintro ⟨-, rfl⟩ o ho
      simp [mem_range.2 ho]
    · intro h
      have hgP : g a = P := by
        ext o
        simp only [g, mem_filter, mem_range]
        constructor
        · rintro ⟨ho, ht⟩; exact (h o ho).2 ht
        · intro hoP
          have ho := mem_range.1 (hP.1 hoP)
          exact ⟨ho, (h o ho).1 hoP⟩
      refine ⟨fun j hj => ?_, hgP⟩
      obtain ⟨p, hp, hm⟩ := hP.2 j hj
      have ho : 3 * j + p < numOcc φ := by unfold numOcc; omega
      exact ⟨p, hp, (h _ ho).1 hm⟩
  · intro a ha
    replace ha : SatOcc φ a := (mem_filter.1 ha).2
    rw [stageChoices, mem_coe, mem_filter, mem_powerset]
    refine ⟨filter_subset _ _, fun j hj => ?_⟩
    obtain ⟨p, hp, ht⟩ := ha j hj
    exact ⟨p, hp, mem_filter.2 ⟨mem_range.2 (by unfold numOcc; omega), ht⟩⟩

theorem card_satOcc (hφ : WellFormed φ) :
    ((univ : Finset (Fin (numAux φ) → Bool)).filter (SatOcc φ)).card = φ.modelCount := by
  symm
  refine CNF.modelCount_eq_card_filter
    (fun σ (i : Fin (numAux φ)) => σ ((varList φ).getD i 0)) (SatOcc φ)
    (fun σ τ _ _ => ?_) (fun a => ?_)
  · constructor
    · intro h v hv
      have hv' : v ∈ varList φ := CNF.mem_distinctVars.2 hv
      have hi := List.idxOf_lt_length_iff.2 hv'
      have := congrFun h ⟨_, hi⟩
      simpa only [getD_varList_idxOf hv'] using this
    · intro h
      funext i
      exact h _ (CNF.mem_distinctVars.1 (getD_varList_mem i.2))
  · constructor
    · intro ha
      refine ⟨assignVal φ a, ?_, funext fun i => assignVal_getD a i.2⟩
      rw [CNF.eval_eq_true_iff]
      intro c hc
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
      obtain ⟨p, hp, ht⟩ := ha j hj
      have ho : 3 * j + p < numOcc φ := by unfold numOcc; omega
      have hmem := litAt_mem hφ ho
      have hj' : (3 * j + p) / 3 = j := by omega
      simp only [hj'] at hmem
      rw [Clause.eval_eq_true_iff]
      exact ⟨_, hmem, (Literal.eval_eq_true_iff _ _).1 ht⟩
    · rintro ⟨σ, hσ, rfl⟩ j hj
      rw [CNF.eval_eq_true_iff] at hσ
      obtain ⟨l, hl, hlt⟩ := (Clause.eval_eq_true_iff _ _).1 (hσ _ (List.getElem_mem hj))
      obtain ⟨p, hp, hlp⟩ := exists_litAt_eq hφ hj hl
      refine ⟨p, hp, ?_⟩
      rw [hlp, Literal.eval_eq_true_iff]
      have hv : l.1 ∈ varList φ :=
        CNF.mem_distinctVars.2 (CNF.mem_vars.2 ⟨_, List.getElem_mem hj, l.2, hl⟩)
      have hi := List.idxOf_lt_length_iff.2 hv
      unfold assignVal
      rw [dite_eq_left (show _ < numAux φ from hi)]
      simp only [getD_varList_idxOf hv]
      exact hlt

/-- **The permanent of the matrix of a formula** (Goldreich, Proposition 6.21): `12 ^ m` times
the number of satisfying assignments of the variables of `φ`. -/
theorem permanent_fullMatrix (hφ : WellFormed φ) :
    (fullMatrix φ).permanent = 12 ^ φ.length * φ.modelCount := by
  rw [permanent_fullMatrix_tracks hφ, sum_card_trueExactly, card_satOcc hφ]

end Cslib.Complexity.PermanentThreeSAT
