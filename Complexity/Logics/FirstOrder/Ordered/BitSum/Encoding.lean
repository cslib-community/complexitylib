/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Packing
public import Complexity.Foundations.Data.Nat.Bitwise.SumTree
import Mathlib.Tactic.Linarith

/-!
# Native access to packed bit-sum trees

Eight first-order variables represent eight fixed-width bit strings. Their access formula uses
a fixed disjunction and fixed chains of PLUS formulas, never a variable multiplication relation.
The tree address uses the proved exact shift formula. Node decoding constrains all bits above
the node's level to zero.

## Main definitions

* `Cslib.Logic.FO.Ordered.BitSum.treeAddress`: native bit-plane addressing.
* `Cslib.Logic.FO.Ordered.BitSum.packedBit`: native access to eight packed words.
* `Cslib.Logic.FO.Ordered.BitSum.nodeValue`, `Cslib.Logic.FO.Ordered.BitSum.EncodesNode`:
  decoding a node's entire value and its bitwise specification.

## Main results

* `Cslib.Logic.FO.Ordered.BitSum.realize_treeAddress`: exact natural-number addresses.
* `Cslib.Logic.FO.Ordered.BitSum.realize_packedBit`: exact fixed-width word access.
* `Cslib.Logic.FO.Ordered.BitSum.realize_nodeValue`: exact decoding, including high zero bits.
* `Cslib.Logic.FO.Ordered.BitSum.encodesNode_sumTree`: constructed witnesses encode every node.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Lemma 1.18, historically due to
  Barrington, Immerman and Straubing. This module uses the balanced-tree packing variant.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered.BitSum

open FirstOrder Language Structure

variable (L : Language)

/-- A bit-plane address, using only PLUS, a literal three, and an exact binary shift. -/
noncomputable def treeAddress {α : Type*} (m j b q a : (language L).Term α) :
    (language L).Formula α := Formula.iExs (Fin 5)
  (addEq L (j.relabel Sum.inl) (.var (.inr 0)) (m.relabel Sum.inl) ⊓
   addEq L (j.relabel Sum.inl) (b.relabel Sum.inl) (.var (.inr 1)) ⊓
   natEq L 3 (.var (.inr 2)) ⊓
   addEq L (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) ⊓
   shiftLeft L (.var (.inr 3)) (.var (.inr 0)) (.var (.inr 4)) ⊓
   addEq L (.var (.inr 4)) (q.relabel Sum.inl) (a.relabel Sum.inl))

/-- Read an address in eight fixed-width words. The eight scales are syntactic literals. -/
noncomputable def packedBit {α : Type*} (h : (language L).Term α)
    (w : Fin 8 → (language L).Term α) (a : (language L).Term α) : (language L).Formula α :=
  Ordered.packedBit L h w a

/-- Decode the whole node value, explicitly zeroing all bits above its level. -/
noncomputable def nodeValue {α : Type*} (m h : (language L).Term α)
    (w : Fin 8 → (language L).Term α) (j q z : (language L).Term α) :
    (language L).Formula α := Formula.iAlls Unit
  ((bit L (z.relabel Sum.inl) (.var (.inr ()))).iff
    (le L (.var (.inr ())) (j.relabel Sum.inl) ⊓
      Formula.iExs Unit
        (treeAddress L (m.relabel (Sum.inl ∘ Sum.inl)) (j.relabel (Sum.inl ∘ Sum.inl))
          (.var (.inl (.inr ()))) (q.relabel (Sum.inl ∘ Sum.inl)) (.var (.inr ())) ⊓
         packedBit L (h.relabel (Sum.inl ∘ Sum.inl))
           (fun r => (w r).relabel (Sum.inl ∘ Sum.inl)) (.var (.inr ())))))

/-- The explicit bitwise meaning of the packed node decoder. -/
def EncodesNode (m h : ℕ) (w : Fin 8 → ℕ) (j q z : ℕ) : Prop :=
  ∀ b, z.testBit b = true ↔ b ≤ j ∧ ∃ r : Fin 8, ∃ t,
    r.val * h + t = BitString.sumTreeAddress m j b q ∧ t < h ∧ (w r).testBit t = true

/-- A packed node has at most one value, including all its high bits. -/
theorem EncodesNode.unique {m h : ℕ} {w : Fin 8 → ℕ} {j q z z' : ℕ}
    (hz : EncodesNode m h w j q z) (hz' : EncodesNode m h w j q z') : z = z' := by
  apply Nat.eq_of_testBit_eq
  intro b
  exact Bool.eq_iff_iff.mpr ((hz b).trans (hz' b).symm)

/-- The actual packed tree decodes to the actual sum at every valid node. -/
theorem encodesNode_sumTree (f : ℕ → Bool) {m h j q : ℕ}
    (hspace : 4 * 2 ^ m ≤ 8 * h) (hj : j ≤ m) (hq : q < 2 ^ (m - j)) :
    EncodesNode m h (BitString.sumTreeWords f m h) j q (BitString.sumTree f j q) := by
  intro b
  constructor
  · intro hz
    have hb : b ≤ j := by
      have hp := Nat.ge_two_pow_of_testBit hz
      have ht := BitString.sumTree_lt f j q
      have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (lt_of_le_of_lt hp ht)
      lia
    have ha := lt_of_lt_of_le (BitString.sumTreeAddress_lt hj hb hq) hspace
    obtain ⟨r, t, he⟩ := BitString.exists_sumTreeWords_address ha
    refine ⟨hb, r, t.val, he, t.isLt, ?_⟩
    rw [BitString.sumTreeWords_testBit _ _ _ _ t.isLt, he,
      BitString.sumTreeBits_address _ hj hb hq]
    exact hz
  · rintro ⟨hb, r, t, he, ht, hw⟩
    rw [BitString.sumTreeWords_testBit _ _ _ _ ht, he,
      BitString.sumTreeBits_address _ hj hb hq] at hw
    exact hw

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {α : Type*}

/-- `treeAddress L m j b q a` holds exactly when `j ≤ m` and `a` is the address
`BitString.sumTreeAddress m j b q`. -/
@[simp, fo_realize]
theorem realize_treeAddress (m j b q a : (language L).Term α) (v : α → Fin n) :
    (treeAddress L m j b q a).Realize v ↔ (j.realize v).val ≤ (m.realize v).val ∧
      BitString.sumTreeAddress (m.realize v).val (j.realize v).val (b.realize v).val
        (q.realize v).val = (a.realize v).val := by
  simp only [treeAddress, Formula.realize_iExs, Formula.realize_inf, realize_addEq,
    realize_natEq, realize_shiftLeft, Term.realize_var, Term.realize_relabel, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, and_assoc]
  constructor
  · rintro ⟨u, h0, h1, h2, h3, h4, h5⟩
    have he : (u 0).val = (m.realize v).val - (j.realize v).val := by lia
    refine ⟨by lia, ?_⟩
    dsimp [BitString.sumTreeAddress]
    rw [← he]
    have hc : (j.realize v).val + (b.realize v).val + 3 = (u 3).val := by lia
    rw [hc, h4]
    exact h5
  · rintro ⟨hj, ha⟩
    let e := (m.realize v).val - (j.realize v).val
    let c := (j.realize v).val + (b.realize v).val + 3
    let s := c * 2 ^ e
    have hs : s < n := by
      have := (a.realize v).isLt
      change s + (q.realize v).val = (a.realize v).val at ha
      lia
    have hc : c < n := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos e)) hs
    have he : e < n := lt_of_le_of_lt (Nat.sub_le _ _) (m.realize v).isLt
    have hjb : (j.realize v).val + (b.realize v).val < n := by dsimp [c] at hc; lia
    have hthree : 3 < n := by dsimp [c] at hc; lia
    refine ⟨![⟨e, he⟩, ⟨_, hjb⟩, ⟨3, hthree⟩, ⟨c, hc⟩, ⟨s, hs⟩], ?_⟩
    exact ⟨by dsimp [e]; lia, rfl, rfl, rfl, rfl, ha⟩

/-- `packedBit L h w a` holds exactly when position `a` falls in one of the eight words `w`, of
width `h`, at a set bit. -/
@[simp, fo_realize]
theorem realize_packedBit (h : (language L).Term α) (w : Fin 8 → (language L).Term α)
    (a : (language L).Term α) (v : α → Fin n) :
    (packedBit L h w a).Realize v ↔ ∃ r : Fin 8, ∃ b : Fin n,
      r.val * (h.realize v).val + b.val = (a.realize v).val ∧
        b.val < (h.realize v).val ∧ ((w r).realize v).val.testBit b.val = true :=
  Ordered.realize_packedBit h w a v

/-- When `j ≤ m` and eight words of width `h` fit in the universe, `nodeValue L m h w j q z`
holds exactly when the words encode the value `z` at node `j` (`EncodesNode`). -/
@[fo_realize]
theorem realize_nodeValue (m h : (language L).Term α) (w : Fin 8 → (language L).Term α)
    (j q z : (language L).Term α) (v : α → Fin n)
    (hj : (j.realize v).val ≤ (m.realize v).val) (hspace : 8 * (h.realize v).val < n) :
    (nodeValue L m h w j q z).Realize v ↔
      EncodesNode (m.realize v).val (h.realize v).val (fun r => ((w r).realize v).val)
        (j.realize v).val (q.realize v).val (z.realize v).val := by
  simp only [nodeValue, Formula.realize_iAlls, Formula.realize_iff, Formula.realize_inf,
    Formula.realize_iExs, realize_bit, realize_le, realize_treeAddress, realize_packedBit,
    Term.realize_var, Term.realize_relabel, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    hj, true_and]
  constructor
  · intro hn b
    constructor
    · intro hz
      have hb : b < n := lt_trans
        (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.ge_two_pow_of_testBit hz)) (z.realize v).isLt
      obtain ⟨hbj, a, ha, r, t, ht, hth, hw⟩ := (hn (fun _ => ⟨b, hb⟩)).mp hz
      exact ⟨hbj, r, t.val, ht.trans ha.symm, hth, hw⟩
    · rintro ⟨hbj, r, t, ht, hth, hw⟩
      have hb : b < n := lt_of_le_of_lt hbj (j.realize v).isLt
      have htn : t < n := lt_trans hth (h.realize v).isLt
      have ha : BitString.sumTreeAddress (m.realize v).val (j.realize v).val b
          (q.realize v).val < n := by
        have hr := r.isLt
        nlinarith
      apply (hn (fun _ => ⟨b, hb⟩)).mpr
      exact ⟨hbj, (fun _ => ⟨_, ha⟩), rfl, r, ⟨t, htn⟩, ht, hth, hw⟩
  · intro hn b
    constructor
    · intro hz
      obtain ⟨hbj, r, t, ht, hth, hw⟩ := (hn (b ()).val).mp hz
      have htn : t < n := lt_trans hth (h.realize v).isLt
      have ha : BitString.sumTreeAddress (m.realize v).val (j.realize v).val (b ()).val
          (q.realize v).val < n := by
        have hr := r.isLt
        nlinarith
      exact ⟨hbj, (fun _ => ⟨_, ha⟩), rfl, r, ⟨t, htn⟩, ht, hth, hw⟩
    · rintro ⟨hbj, a, ha, r, t, ht, hth, hw⟩
      exact (hn (b ()).val).mpr ⟨hbj, r, t.val, ht.trans ha.symm, hth, hw⟩

end Cslib.Logic.FO.Ordered.BitSum
