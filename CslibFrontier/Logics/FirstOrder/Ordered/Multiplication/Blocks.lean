/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Multiplication.Columns
public import CslibFrontier.Logics.FirstOrder.Ordered.Packing
import Mathlib.Tactic.Linarith

/-!
# Native verification of multiplication carry blocks

Sixteen local words encode all carries in a short block. Its first and last carries must agree
with the same global eight-word tuple used by every block. Native PLUS and exact shifts derive
the local column equations; no multiplication relation occurs in the formula.

## Main definitions

* `Cslib.Logic.FO.Ordered.Multiplication.blockChecks`: verify one carry block and its endpoints.

## Main results

* `Cslib.Logic.FO.Ordered.Multiplication.realize_blockChecks`: exact block semantics.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Theorem 1.17(1).
  This is the carry-table variant of the source's packed short sums.
-/

namespace Cslib.Logic.FO.Ordered.Multiplication

open FirstOrder Language Structure

variable (L : Language)

private noncomputable def localChecks {α : Type*} (h e s x y z j : (language L).Term α)
    (w : Fin 16 → (language L).Term α) : (language L).Formula α := Formula.iAlls (Fin 5)
  (((le L (s.relabel Sum.inl) (.var (.inr 0))).not ⊓
    addEq L (.var (.inr 0)) (one L) (.var (.inr 1)) ⊓
    addEq L (j.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 2)) ⊓
    shiftLeft L (.var (.inr 0)) (e.relabel Sum.inl) (.var (.inr 3)) ⊓
    shiftLeft L (.var (.inr 1)) (e.relabel Sum.inl) (.var (.inr 4))).imp
  (Formula.iExs (Fin 2)
    (packedField L (h.relabel (Sum.inl ∘ Sum.inl))
       (fun r => (w r).relabel (Sum.inl ∘ Sum.inl)) (.var (.inl (.inr 3)))
       (s.relabel (Sum.inl ∘ Sum.inl)) (.var (.inr 0)) ⊓
     packedField L (h.relabel (Sum.inl ∘ Sum.inl))
       (fun r => (w r).relabel (Sum.inl ∘ Sum.inl)) (.var (.inl (.inr 4)))
       (s.relabel (Sum.inl ∘ Sum.inl)) (.var (.inr 1)) ⊓
     carryStep L (x.relabel (Sum.inl ∘ Sum.inl)) (y.relabel (Sum.inl ∘ Sum.inl))
       (z.relabel (Sum.inl ∘ Sum.inl)) (.var (.inl (.inr 2))) (.var (.inr 0)) (.var (.inr 1)))))

/-- Check every local carry equation and match both ends with the global boundary words. -/
public noncomputable def blockChecks {α : Type*} (h e s x y z j : (language L).Term α)
    (g : Fin 8 → (language L).Term α) : (language L).Formula α :=
  Formula.iExs (Fin 16 ⊕ Fin 4) (
    let w := fun r : Fin 16 => Term.var (.inr (.inl r))
    let a : (language L).Term (α ⊕ (Fin 16 ⊕ Fin 4)) := .var (.inr (.inr 0))
    let b := .var (.inr (.inr 1))
    let j' := .var (.inr (.inr 2))
    let t' := .var (.inr (.inr 3))
    addEq L (j.relabel Sum.inl) (s.relabel Sum.inl) j' ⊓
    shiftLeft L (s.relabel Sum.inl) (e.relabel Sum.inl) t' ⊓
    packedField L (h.relabel Sum.inl) (fun r => (g r).relabel Sum.inl)
      (j.relabel Sum.inl) (s.relabel Sum.inl) a ⊓
    packedField L (h.relabel Sum.inl) w (zero L) (s.relabel Sum.inl) a ⊓
    packedField L (h.relabel Sum.inl) (fun r => (g r).relabel Sum.inl) j'
      (s.relabel Sum.inl) b ⊓
    packedField L (h.relabel Sum.inl) w t' (s.relabel Sum.inl) b ⊓
    localChecks L (h.relabel Sum.inl) (e.relabel Sum.inl) (s.relabel Sum.inl)
      (x.relabel Sum.inl) (y.relabel Sum.inl) (z.relabel Sum.inl) (j.relabel Sum.inl) w)

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {α : Type*}

private theorem realize_localChecks (h e s x y z j : (language L).Term α)
    (w : Fin 16 → (language L).Term α) (v : α → Fin n)
    (hs : (s.realize v).val = 2 ^ (e.realize v).val)
    (hcap : ((s.realize v).val + 1) * (s.realize v).val < n)
    (hj : (j.realize v).val + (s.realize v).val < n)
    (hwidth : 2 ^ (s.realize v).val < n) (hspace : 16 * (h.realize v).val < n) :
    (localChecks L h e s x y z j w).Realize v ↔
      let c := fun t => BitString.readPackedField (h.realize v).val
        (fun r => ((w r).realize v).val) (t * (s.realize v).val) (s.realize v).val
      ∀ t < (s.realize v).val,
        c t + BitString.mulColumn (x.realize v).val (y.realize v).val ((j.realize v).val + t) =
          ((z.realize v).val.testBit ((j.realize v).val + t)).toNat + 2 * c (t + 1) ∧
        c t + BitString.mulColumn (x.realize v).val (y.realize v).val
          ((j.realize v).val + t) < n := by
  simp (disch := (simp only [Term.realize_var, Term.realize_relabel, Function.comp_def,
      Sum.elim_inl, Sum.elim_inr]; exact hspace)) only
    [localChecks, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
      Formula.realize_not, Formula.realize_iExs, realize_le, realize_addEq, realize_shiftLeft,
      realize_packedField, realize_carryStep, Term.realize_var, Term.realize_relabel,
      Function.comp_def, Sum.elim_inl, Sum.elim_inr, realize_one_val, not_le, and_assoc]
  constructor
  · intro hf t ht
    have ht1 : t + 1 < n := lt_of_le_of_lt (by lia) (s.realize v).isLt
    have htn : t < n := by lia
    have hit : (j.realize v).val + t < n := by lia
    have hta : t * (s.realize v).val < n := by nlinarith
    have hta' : (t + 1) * (s.realize v).val < n := by nlinarith
    let u : Fin 5 → Fin n := ![⟨t, htn⟩, ⟨t + 1, ht1⟩, ⟨_, hit⟩, ⟨_, hta⟩, ⟨_, hta'⟩]
    obtain ⟨a, ha, hb, he, hn⟩ := hf u ⟨ht, rfl, rfl, by dsimp [u]; rw [hs],
      by dsimp [u]; rw [hs]⟩
    simpa [ha, hb, u] using And.intro he hn
  · intro hf u ⟨ht, ht1, hi, ha, hb⟩
    have ha' : (u 3).val = (u 0).val * (s.realize v).val := by rw [hs]; exact ha.symm
    have hb' : (u 4).val = ((u 0).val + 1) * (s.realize v).val := by rw [ht1, hs]; exact hb.symm
    let a := BitString.readPackedField (h.realize v).val
      (fun r => ((w r).realize v).val) (u 3).val (s.realize v).val
    let b := BitString.readPackedField (h.realize v).val
      (fun r => ((w r).realize v).val) (u 4).val (s.realize v).val
    have han : a < n := lt_trans (BitString.readPackedField_lt ..) hwidth
    have hbn : b < n := lt_trans (BitString.readPackedField_lt ..) hwidth
    refine ⟨![⟨a, han⟩, ⟨b, hbn⟩], rfl, rfl, ?_⟩
    simpa [a, b, ha', hb', ← hi] using hf (u 0).val ht

/-- The two decoded endpoints agree with the global words, and every interior step is exact. -/
@[fo_realize]
public theorem realize_blockChecks (h e s x y z j : (language L).Term α)
    (g : Fin 8 → (language L).Term α) (v : α → Fin n)
    (hs : (s.realize v).val = 2 ^ (e.realize v).val)
    (hcap : ((s.realize v).val + 1) * (s.realize v).val < n)
    (hj : (j.realize v).val + (s.realize v).val < n)
    (hwidth : 2 ^ (s.realize v).val < n) (hspace : 16 * (h.realize v).val < n) :
    (blockChecks L h e s x y z j g).Realize v ↔ ∃ w : Fin 16 → Fin n,
      let c := fun t => BitString.readPackedField (h.realize v).val (fun r => (w r).val)
        (t * (s.realize v).val) (s.realize v).val
      c 0 = BitString.readPackedField (h.realize v).val (fun r => ((g r).realize v).val)
        (j.realize v).val (s.realize v).val ∧
      c (s.realize v).val = BitString.readPackedField (h.realize v).val
        (fun r => ((g r).realize v).val) ((j.realize v).val + (s.realize v).val)
        (s.realize v).val ∧
      ∀ t < (s.realize v).val,
        c t + BitString.mulColumn (x.realize v).val (y.realize v).val ((j.realize v).val + t) =
          ((z.realize v).val.testBit ((j.realize v).val + t)).toNat + 2 * c (t + 1) ∧
        c t + BitString.mulColumn (x.realize v).val (y.realize v).val
          ((j.realize v).val + t) < n := by
  simp (disch := (simp only [Term.realize_var, Term.realize_relabel, Function.comp_def,
      Sum.elim_inl, Sum.elim_inr]; first | assumption | lia)) only
    [blockChecks, Formula.realize_iExs, Formula.realize_inf, realize_addEq, realize_shiftLeft,
      realize_packedField, realize_localChecks, Term.realize_var, Term.realize_relabel,
      Function.comp_def, Sum.elim_inl, Sum.elim_inr, realize_zero_val, and_assoc]
  constructor
  · rintro ⟨u, hj', ht', ha, ha', hb, hb', hl⟩
    refine ⟨(fun r => u (.inl r)), ?_, ?_, hl⟩
    · simpa only [Nat.zero_mul] using ha'.symm.trans ha
    · simpa only [← ht', ← hj', ← hs] using hb'.symm.trans hb
  · rintro ⟨w, h0, hs', hl⟩
    let a := BitString.readPackedField (h.realize v).val (fun r => ((g r).realize v).val)
      (j.realize v).val (s.realize v).val
    let b := BitString.readPackedField (h.realize v).val (fun r => ((g r).realize v).val)
      ((j.realize v).val + (s.realize v).val) (s.realize v).val
    have ha : a < n := lt_trans (BitString.readPackedField_lt ..) hwidth
    have hb : b < n := lt_trans (BitString.readPackedField_lt ..) hwidth
    have ht : (s.realize v).val * (s.realize v).val < n := by nlinarith
    let u : (Fin 16 ⊕ Fin 4) → Fin n :=
      Sum.elim w ![⟨a, ha⟩, ⟨b, hb⟩, ⟨_, hj⟩, ⟨_, ht⟩]
    refine ⟨u, rfl, ?_, rfl, ?_, rfl, ?_, hl⟩
    · dsimp [u]
      rw [hs]
    · simpa [u, a] using h0.symm
    · exact hs'.symm

end Cslib.Logic.FO.Ordered.Multiplication
