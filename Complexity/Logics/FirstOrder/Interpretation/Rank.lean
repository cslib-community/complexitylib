/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Interpretation
public import Complexity.Logics.FirstOrder.Encoding
public import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Nth

/-!
# Numbering the elements of an interpreted structure

A first-order interpretation `I` of dimension `ι` interprets, in a structure on `Fin n`, a structure
whose elements are the tuples `ι → Fin n` satisfying the domain formula. Fixing an enumeration
`e : ι ≃ Fin d` of the coordinates, a tuple has an index below `n ^ d` (`Cslib.Logic.tupleIndex`),
and the elements of the interpreted structure are numbered by the rank of their index among the
indices of the domain (`Cslib.Logic.FO.Interpretation.rankEquiv`): the number of indices of the
domain below it. This is the numbering an algorithm computes by counting, as a logarithmic-space
transducer for the interpretation does.

## Main definitions

* `Cslib.Logic.FO.Interpretation.InDomain`: the indices of the tuples of the domain.
* `Cslib.Logic.FO.Interpretation.domainRank`, `Cslib.Logic.FO.Interpretation.modelCard`: the number
  of indices of the domain below a bound, and the total cardinality of the interpreted domain.
* `Cslib.Logic.FO.Interpretation.rankOf`, `Cslib.Logic.FO.Interpretation.rankEquiv`: the rank of an
  interpreted element and the numbering equivalence of the interpreted structure by ranks.

## Main results

* `Cslib.Logic.FO.Interpretation.domainRank_succ`: ranks count the indices of the domain.
* `Cslib.Logic.FO.Interpretation.rankEquiv_symm_val`: the element of a given rank is the tuple
  whose index has that rank.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v u' v'

open FirstOrder Language Structure

namespace Cslib.Logic.FO.Interpretation

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {ι : Type*} {d : ℕ}
  (I : Interpretation L L' ι) (e : ι ≃ Fin d)

variable (n : ℕ) [L.Structure (Fin n)]

/-- The number `u` is the index of a tuple of the domain of `I`. -/
def InDomain (u : ℕ) : Prop := ∃ h : u < n ^ d, I.domain.Realize ((tupleEquiv e).symm ⟨u, h⟩)

open scoped Classical in
/-- The number of indices of tuples of the domain below `u`. -/
noncomputable def domainRank (u : ℕ) : ℕ := Nat.count (I.InDomain e n) u

variable {I e n}

/-- There are zero domain indices below `0`. -/
theorem domainRank_zero : I.domainRank e n 0 = 0 := by simp [domainRank]

/-- Ranks count the indices of the domain: the rank of `u + 1` is that of `u`, plus one when `u`
indexes a tuple of the domain. -/
theorem domainRank_succ (u : ℕ) [Decidable (I.InDomain e n u)] :
    I.domainRank e n (u + 1) = I.domainRank e n u + if I.InDomain e n u then 1 else 0 := by
  by_cases h : I.InDomain e n u <;> simp [domainRank, Nat.count_succ, h]

/-- `I.domainRank e n` is monotone. -/
theorem domainRank_mono {u u' : ℕ} (h : u ≤ u') : I.domainRank e n u ≤ I.domainRank e n u' := by
  classical
  exact Nat.count_monotone (I.InDomain e n) h

/-- If `u` belongs to `I.InDomain e n` and `u < u'`, then
`I.domainRank e n u < I.domainRank e n u'`. -/
theorem domainRank_lt_of_inDomain {u u' : ℕ} (hu : I.InDomain e n u) (h : u < u') :
    I.domainRank e n u < I.domainRank e n u' := by
  classical
  exact Nat.count_strict_mono hu h

/-- For any `x : I.Model (Fin n)`, the tuple index `(tupleEquiv e x.1).val` satisfies
`I.InDomain e n`. -/
theorem inDomain_tupleEquiv (x : I.Model (Fin n)) : I.InDomain e n (tupleEquiv e x.1).val :=
  ⟨(tupleEquiv e x.1).isLt, by simpa only [Fin.eta, Equiv.symm_apply_apply] using x.2⟩

variable (I e n) in
/-- The number of elements of the interpreted structure: the number of indices of the domain. -/
noncomputable def modelCard : ℕ := I.domainRank e n (n ^ d)

/-- The cardinality `modelCard I e n` of the interpreted domain is at most `n ^ d`. -/
theorem modelCard_le_pow : modelCard I e n ≤ n ^ d := by
  classical
  exact Nat.count_le (I.InDomain e n)

/-- The rank of the index of an element of the interpreted structure. -/
noncomputable def rankOf (x : I.Model (Fin n)) : Fin (modelCard I e n) :=
  ⟨I.domainRank e n (tupleEquiv e x.1).val, domainRank_lt_of_inDomain (inDomain_tupleEquiv x)
    (tupleEquiv e x.1).isLt⟩

/-- `rankOf` is injective on `I.Model (Fin n)`. -/
theorem rankOf_injective : Function.Injective (rankOf (I := I) (e := e) (n := n)) := by
  classical
  intro x y h
  apply Model.ext
  apply (tupleEquiv e).injective
  exact Fin.ext (Nat.count_injective (inDomain_tupleEquiv x) (inDomain_tupleEquiv y)
    (congrArg Fin.val h))

/-- Every rank below the number of elements is the rank of an index of the domain. -/
theorem exists_inDomain_of_lt {r : ℕ} (hr : r < modelCard I e n) :
    ∃ u, I.InDomain e n u ∧ I.domainRank e n u = r := by
  classical
  have hbound (hf : (Set.ofPred (I.InDomain e n)).Finite) : r < hf.toFinset.card :=
    hr.trans_le (Nat.count_le_card hf (n ^ d))
  exact ⟨Nat.nth (I.InDomain e n) r, Nat.nth_mem _ hbound, Nat.count_nth hbound⟩

/-- `rankOf` is surjective onto `Fin (modelCard I e n)`. -/
theorem rankOf_surjective : Function.Surjective (rankOf (I := I) (e := e) (n := n)) := by
  intro r
  obtain ⟨u, ⟨hu, hdom⟩, hr⟩ := exists_inDomain_of_lt r.2
  refine ⟨⟨(tupleEquiv e).symm ⟨u, hu⟩, hdom⟩, Fin.ext ?_⟩
  simp only [rankOf, Equiv.apply_symm_apply, hr]

variable (I e n) in
/-- **The numbering of the interpreted structure by ranks**: an element is numbered by the number
of indices of the domain below its index. -/
noncomputable def rankEquiv : I.Model (Fin n) ≃ Fin (modelCard I e n) :=
  Equiv.ofBijective rankOf ⟨rankOf_injective, rankOf_surjective⟩

/-- The underlying natural number of `rankEquiv I e n x` is
`I.domainRank e n (tupleEquiv e x.1).val`. -/
@[simp]
theorem rankEquiv_apply_val (x : I.Model (Fin n)) :
    (rankEquiv I e n x).val = I.domainRank e n (tupleEquiv e x.1).val := rfl

/-- **The element of a given rank** is the tuple whose index is in the domain and has that rank. -/
theorem rankEquiv_symm_val {r : Fin (modelCard I e n)} {u : ℕ} (hu : I.InDomain e n u)
    (hr : I.domainRank e n u = r) :
    (rankEquiv I e n).symm r = ⟨(tupleEquiv e).symm ⟨u, hu.1⟩, hu.2⟩ := by
  apply (rankEquiv I e n).injective
  rw [Equiv.apply_symm_apply]
  refine Fin.ext ?_
  change r.val = I.domainRank e n (tupleEquiv e ((tupleEquiv e).symm ⟨u, hu.1⟩)).val
  rw [Equiv.apply_symm_apply, hr]

end Cslib.Logic.FO.Interpretation
