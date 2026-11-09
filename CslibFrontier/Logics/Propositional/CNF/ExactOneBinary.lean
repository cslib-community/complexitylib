/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ExactOneElimination
public import CslibFrontier.Computability.PolyTime.Int.Rectangular
import CslibFrontier.Foundations.Data.List.OfFn
import Mathlib.Data.List.GetD

/-!
# Integer encoding of signed exact-one systems

The signed equations of [ChenJiangZhu2027], Theorem 5.2 and Theorem 6.3
(PDF pp. 16–17 and 20–21), have integral coefficients. `integerRows` and
`integerRhs` materialize these equations directly, so no denominator-clearing
advice is required. `binaryConsistent_iff` connects the binary-certified
rectangular solver to the existing signed semantics. `binaryPreprocess` executes
all direct and two-query branches; its correctness and syntax budgets are proved.
This does not certify the
runtime of closure listing or query construction.
-/

public section

namespace Cslib.Logic.PL.ExactOne

open Matrix Cslib.LinearSystem Cslib.Circuits.Rational

variable {n m : ℕ} (S : Fin m → Finset (Fin n)) (p : Fin m → Fin n → Bool)

/-- Signed coefficients, materialized without rational arithmetic. -/
@[expose] def integerRows : List (List ℤ) :=
  List.ofFn fun i => List.ofFn fun v =>
    if v ∈ S i then if p i v then (1 : ℤ) else -1 else 0

/-- The constant from each negative literal is moved to the right side. -/
@[expose] def integerRhs : List ℤ :=
  List.ofFn fun i => 1 - ((S i).filter fun v => p i v = false).card

@[simp] theorem integerRows_length : (integerRows S p).length = m := by
  simp [integerRows]

/-- The materialized integer rows are precisely the existing rational rows. -/
theorem integerRows_entry (i : Fin m) (v : Fin n) :
    (rowEntry (integerRows S p) i v : ℚ) = coefficients (S i) (p i) v := by
  simp only [integerRows, rowEntry, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    i.isLt, v.isLt, ↓reduceDIte, Option.getD_some, coefficients]
  split_ifs <;> norm_num

/-- The integer right-hand side preserves the signed literal constants. -/
theorem integerRhs_entry (i : Fin m) :
    ((integerRhs S p).getD i 0 : ℚ) = rhs (S i) (p i) := by
  simp [integerRhs, rhs, List.getD_eq_getElem?_getD, i.isLt]

/-- Binary consistency tests exactly the original rational equations. -/
theorem binaryConsistent_iff :
    rectangularConsistent n (integerRows S p) (integerRhs S p) = true ↔
      ∃ z : Fin n → ℚ, ∀ i, coefficients (S i) (p i) ⬝ᵥ z = rhs (S i) (p i) := by
  rw [rectangularConsistent_correct]
  apply exists_congr
  intro z
  constructor
  · intro h i
    have he := h ⟨i, by simp⟩
    simpa only [integerRows_entry, integerRhs_entry] using he
  · intro h i
    have hi : (i : ℕ) < m := by simpa using i.isLt
    change (fun j : Fin n => (rowEntry (integerRows S p) (⟨i, hi⟩ : Fin m) j : ℚ)) ⬝ᵥ z =
      ((integerRhs S p).getD (⟨i, hi⟩ : Fin m) 0 : ℚ)
    simpa only [integerRows_entry S p ⟨i, hi⟩, integerRhs_entry S p ⟨i, hi⟩] using h ⟨i, hi⟩

/-- The actual binary candidate solves every signed equation upon acceptance. -/
theorem binaryPoint_correct
    (hc : rectangularConsistent n (integerRows S p) (integerRhs S p) = true) :
    ∀ i, coefficients (S i) (p i) ⬝ᵥ
      rectangularPoint n (integerRows S p) (integerRhs S p) = rhs (S i) (p i) := by
  intro i
  have he := rectangularPoint_correct n (integerRows S p) (integerRhs S p) hc
    ⟨i, by simp⟩
  simpa only [integerRows_entry, integerRhs_entry] using he

/-- Original indices selected by the binary Gram scan, with bounds checked by its
membership theorem rather than truncation or a default row. -/
@[expose] def binaryIndices : List (Fin m) :=
  (gramRowBasis n (integerRows S p)).attach.map fun i =>
    ⟨i.val, by simpa using gramRowBasis_mem n (integerRows S p) i.val i.property⟩

@[simp] theorem binaryIndices_length :
    (binaryIndices S p).length = (gramRowBasis n (integerRows S p)).length := by
  simp [binaryIndices]

/-- Selected signed constraints preserve all Boolean solutions when the computed
consistency check accepts. No supplied solution or basis is a hypothesis. -/
theorem binaryIndices_selected
    (hc : rectangularConsistent n (integerRows S p) (integerRhs S p) = true)
    (x : Fin n → Bool) :
    (∀ i ∈ binaryIndices S p, Holds (S i) (p i) x) ↔ ∀ i, Holds (S i) (p i) x := by
  obtain ⟨z, hz⟩ := (rectangularConsistent_correct n (integerRows S p) (integerRhs S p)).mp hc
  have he := gramRowBasis_selected_iff n (integerRows S p) (integerRhs S p) z hz
    (rationalPoint x)
  constructor
  · intro h i
    have hall := he.mp (fun t => by
      have ht : (gramRowBasis n (integerRows S p)).getD t 0 ∈
          gramRowBasis n (integerRows S p) := by
        rw [List.getD_eq_getElem _ _ t.isLt]
        exact List.getElem_mem t.isLt
      have hb : (gramRowBasis n (integerRows S p)).getD t 0 < m := by
        simpa using gramRowBasis_mem n (integerRows S p) _ ht
      have hm : (⟨_, hb⟩ : Fin m) ∈ binaryIndices S p := by
        apply List.mem_map.mpr
        exact ⟨⟨_, ht⟩, by simp, rfl⟩
      have hh := (equation_iff _ _ _).mpr (h _ hm)
      change (fun j : Fin n => (rowEntry (integerRows S p) (⟨_, hb⟩ : Fin m) j : ℚ)) ⬝ᵥ
        rationalPoint x = ((integerRhs S p).getD (⟨_, hb⟩ : Fin m) 0 : ℚ)
      simpa only [integerRows_entry S p ⟨_, hb⟩, integerRhs_entry S p ⟨_, hb⟩] using hh)
    have hh := hall ⟨i, by simp⟩
    apply (equation_iff _ _ _).mp
    simpa only [integerRows_entry S p i, integerRhs_entry S p i] using hh
  · intro h i _; exact h i

/-- Execute all counting branches with the binary rectangular backend. The
rational point is used only for interpreting the recovered binary certificate. -/
@[expose] def binaryPreprocess (B : CNF (Fin n)) : CountPlan (Fin n) :=
  if n ≤ 1 then .direct (smallCount B S p) else
    if rectangularConsistent n (integerRows S p) (integerRhs S p) then
      if (binaryIndices S p).length = n then
        .direct (checkCandidate B S p (rectangularPoint n (integerRows S p) (integerRhs S p)))
      else selectedPlan B S p (binaryIndices S p)
    else .direct 0

private theorem binaryCandidate_correct (B : CNF (Fin n))
    (hc : rectangularConsistent n (integerRows S p) (integerRhs S p) = true)
    (hl : (binaryIndices S p).length = n) :
    checkCandidate B S p (rectangularPoint n (integerRows S p) (integerRhs S p)) =
      sourceCount B S p := by
  classical
  let z := rectangularPoint n (integerRows S p) (integerRhs S p)
  have he : ∀ x : Fin n → Bool, (∀ i, Holds (S i) (p i) x) → candidateBits z = x := by
    intro x hx
    have hz := rectangular_unique n (integerRows S p) (integerRhs S p)
      (by simpa using hl) (rationalPoint x) z ?_
      (rectangularPoint_correct n (integerRows S p) (integerRhs S p) hc)
    · rw [← hz]
      funext v
      cases hv : x v <;> simp [candidateBits, rationalPoint, hv]
    · intro i
      have hi : (i : ℕ) < m := by simpa using i.isLt
      have hh := (equation_iff _ _ _).mpr (hx ⟨i, hi⟩)
      simpa only [integerRows_entry S p ⟨i, hi⟩, integerRhs_entry S p ⟨i, hi⟩] using hh
  let P := fun x : Fin n → Bool => B.eval x = true ∧ ∀ i, Holds (S i) (p i) x
  have hcount : sourceCount B S p = Fintype.card {x // P x} :=
    by simp only [sourceCount, ← Nat.card_eq_fintype_card, P]
  rw [hcount]
  have hu : ∀ x, P x → x = candidateBits z := fun x hx => (he x hx.2).symm
  let : Subsingleton {x // P x} := ⟨fun x y => Subtype.ext
    ((hu x x.property).trans (hu y y.property).symm)⟩
  have hle : Fintype.card {x // P x} ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  unfold checkCandidate
  split_ifs with hb
  · have hpos : 0 < Fintype.card {x // P x} := Fintype.card_pos_iff.mpr ⟨⟨_, hb⟩⟩
    omega
  · symm
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun x => hb ((hu x x.property) ▸ x.property)⟩

/-- Exact counting from the actual binary-selected original equations. All
branches, including inconsistent and deficient systems, preserve declared bits. -/
theorem binaryPreprocess_correct (B : CNF (Fin n)) :
    (binaryPreprocess S p B).value = sourceCount B S p := by
  unfold binaryPreprocess
  split_ifs with hs hc hl
  · simp only [CountPlan.value, CountPlan.execute, smallCount, sourceCount]
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp
  · exact binaryCandidate_correct S p B hc hl
  · exact selectedPlan_correct B S p _ (binaryIndices_selected S p hc)
  · change 0 = sourceCount B S p
    symm
    apply count_eq_zero_of_inconsistent
    exact fun h => hc ((binaryConsistent_iff S p).mpr h)

/-- The binary backend retains the same declared-variable, width and clause
budgets as rational preprocessing. -/
theorem binaryPreprocess_budget (B : CNF (Fin n)) (hb : ∀ c ∈ B, c.length ≤ 2) :
    (binaryPreprocess S p B).Budget n := by
  unfold binaryPreprocess
  split_ifs with hs hc hl
  · trivial
  · trivial
  · have hle : (binaryIndices S p).length ≤ n := by
      simpa using gramRowBasis_length n (integerRows S p)
    simpa only [Fintype.card_fin] using selectedPlan_budget B hb S p _
      (by simpa only [Fintype.card_fin] using hs)
      (by simp only [Fintype.card_fin]; omega)
  · trivial

end Cslib.Logic.PL.ExactOne
