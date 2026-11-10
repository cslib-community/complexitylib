/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.BitSum.Encoding
import CslibFrontier.Tactic.FirstOrder
import Mathlib.Tactic.Linarith

/-!
# The native Bit Sum formula

The Bit Sum Lemma states that the number of set bits of a natural-number index is first-order
definable from order and BIT. The construction here encodes an entire balanced addition tree in
eight element variables and checks every node using the native PLUS formula. The bit-plane
layout needs only exact shifts and fixed literal multiples, never a multiplication predicate.

The packed witnesses are constructed for every universe of size at least 257. A fixed finite
formula handles all smaller input numerals, giving one formula for every canonical `Fin n`,
`n ≥ 2`, including non-power-of-two sizes. Native TIMES and full-tuple BIT build on this
prerequisite in `Ordered.Multiplication` and `Ordered.TupleBit`.

## Main definitions

* `Cslib.Logic.FO.Ordered.bitSum`: a single native formula counting set bits.

## Main results

* `Cslib.Logic.FO.Ordered.realize_bitSum`: exact natural-number bit-count semantics.
* `Cslib.Logic.FO.Ordered.existsUnique_bitSum`: every input has exactly one output.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Lemma 1.18 (Bit Sum Lemma),
  a prerequisite for Theorem 1.17(1). The historical notes credit Barrington, Immerman and
  Straubing; see also [Barrington, Immerman and Straubing][BarringtonImmermanStraubing1990].
  The balanced-tree bit-plane packing here is a proved variant of the source's packed
  running-sum construction, not a transcription of its proof.
-/

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

namespace BitSum

variable (L : Language)

private noncomputable def leafChecks {α : Type*} (m h k : (language L).Term α)
    (w : Fin 8 → (language L).Term α) (x : (language L).Term α) : (language L).Formula α :=
  Formula.iAlls Unit ((le L (k.relabel Sum.inl) (.var (.inr ()))).not.imp
    ((bit L (x.relabel Sum.inl) (.var (.inr ())) ⊓
      nodeValue L (m.relabel Sum.inl) (h.relabel Sum.inl) (fun r => (w r).relabel Sum.inl)
        (zero L) (.var (.inr ())) (one L)) ⊔
     ((bit L (x.relabel Sum.inl) (.var (.inr ()))).not ⊓
      nodeValue L (m.relabel Sum.inl) (h.relabel Sum.inl) (fun r => (w r).relabel Sum.inl)
        (zero L) (.var (.inr ())) (zero L))))

private noncomputable def nodeChecks {α : Type*} (m h : (language L).Term α)
    (w : Fin 8 → (language L).Term α) : (language L).Formula α :=
  Formula.iAlls (Fin 7)
    ((addEq L (.var (.inr 0)) (one L) (.var (.inr 2)) ⊓
      addEq L (.var (.inr 2)) (.var (.inr 3)) (m.relabel Sum.inl) ⊓
      powerOfTwo L (.var (.inr 4)) (.var (.inr 3)) ⊓
      (le L (.var (.inr 4)) (.var (.inr 1))).not ⊓
      addEq L (.var (.inr 1)) (.var (.inr 1)) (.var (.inr 5)) ⊓
      addEq L (.var (.inr 5)) (one L) (.var (.inr 6))).imp
    (Formula.iExs (Fin 3)
      (nodeValue L (m.relabel (Sum.inl ∘ Sum.inl)) (h.relabel (Sum.inl ∘ Sum.inl))
        (fun r => (w r).relabel (Sum.inl ∘ Sum.inl))
        (.var (.inl (.inr 0))) (.var (.inl (.inr 5))) (.var (.inr 0)) ⊓
       nodeValue L (m.relabel (Sum.inl ∘ Sum.inl)) (h.relabel (Sum.inl ∘ Sum.inl))
        (fun r => (w r).relabel (Sum.inl ∘ Sum.inl))
        (.var (.inl (.inr 0))) (.var (.inl (.inr 6))) (.var (.inr 1)) ⊓
       nodeValue L (m.relabel (Sum.inl ∘ Sum.inl)) (h.relabel (Sum.inl ∘ Sum.inl))
        (fun r => (w r).relabel (Sum.inl ∘ Sum.inl))
        (.var (.inl (.inr 2))) (.var (.inl (.inr 1))) (.var (.inr 2)) ⊓
       addEq L (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)))))

private noncomputable def packedFormula : (language L).Formula (Fin 2) :=
  Formula.iExs (Fin 5 ⊕ Fin 8) (
    let h : (language L).Term (Fin 2 ⊕ (Fin 5 ⊕ Fin 8)) := .var (.inr (.inl 0))
    let m := .var (.inr (.inl 1))
    let k := .var (.inr (.inl 2))
    let d := .var (.inr (.inl 3))
    let o := .var (.inr (.inl 4))
    let w := fun r : Fin 8 => Term.var (.inr (.inr r))
    highestBit L (max L) h ⊓ powerOfTwo L k m ⊓ (le L k h).not ⊓
    scaleEq L 2 h d ⊓ le L k d ⊓ scaleEq L 8 h o ⊓
    leafChecks L m h k w (.var (.inl 0)) ⊓ nodeChecks L m h w ⊓
    nodeValue L m h w m (zero L) (.var (.inl 1)))

private noncomputable def smallFormula : (language L).Formula (Fin 2) :=
  Formula.iSup fun a : Fin 256 => natEq L a.val (.var 0) ⊓
    natEq L a.val.bitIndices.length (.var 1)

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {α : Type*}

private theorem realize_leafChecks (m h k : (language L).Term α)
    (w : Fin 8 → (language L).Term α) (x : (language L).Term α) (v : α → Fin n)
    (hspace : 8 * (h.realize v).val < n) :
    (leafChecks L m h k w x).Realize v ↔ ∀ q : Fin n, q.val < (k.realize v).val →
      EncodesNode (m.realize v).val (h.realize v).val (fun r => ((w r).realize v).val)
        0 q.val ((x.realize v).val.testBit q.val).toNat := by
  have hd (u : Unit → Fin n) (z : (language L).Term (α ⊕ Unit)) :=
    realize_nodeValue (m.relabel Sum.inl) (h.relabel Sum.inl)
      (fun r => (w r).relabel Sum.inl) (zero L) (.var (.inr ())) z (Sum.elim v u)
      (by simp) (by simpa only [Term.realize_relabel, Function.comp_def, Sum.elim_inl] using hspace)
  fo_simp [leafChecks, hd, Function.comp_def, not_le]
  constructor
  · intro hc q hq
    rcases hc (fun _ => q) hq with ⟨hx, hn⟩ | ⟨hx, hn⟩
    · simpa only [hx, Bool.toNat_true] using hn
    · have hx' : (x.realize v).val.testBit q.val = false := Bool.eq_false_iff.mpr hx
      simpa only [hx', Bool.toNat_false] using hn
  · intro hc q hq
    have hn := hc (q ()) hq
    cases hx : (x.realize v).val.testBit (q ()).val with
    | false => exact Or.inr ⟨by decide, by simpa only [hx, Bool.toNat_false] using hn⟩
    | true => exact Or.inl ⟨rfl, by simpa only [hx, Bool.toNat_true] using hn⟩

private theorem realize_nodeChecks (m h : (language L).Term α)
    (w : Fin 8 → (language L).Term α) (v : α → Fin n)
    (hspace : 8 * (h.realize v).val < n) :
    (nodeChecks L m h w).Realize v ↔ ∀ u : Fin 7 → Fin n,
      ((u 0).val + 1 = (u 2).val ∧ (u 2).val + (u 3).val = (m.realize v).val ∧
       (u 4).val = 2 ^ (u 3).val ∧ (u 1).val < (u 4).val ∧
       (u 1).val + (u 1).val = (u 5).val ∧ (u 5).val + 1 = (u 6).val) →
      ∃ a : Fin 3 → Fin n,
        EncodesNode (m.realize v).val (h.realize v).val (fun r => ((w r).realize v).val)
          (u 0).val (u 5).val (a 0).val ∧
        EncodesNode (m.realize v).val (h.realize v).val (fun r => ((w r).realize v).val)
          (u 0).val (u 6).val (a 1).val ∧
        EncodesNode (m.realize v).val (h.realize v).val (fun r => ((w r).realize v).val)
          (u 2).val (u 1).val (a 2).val ∧ (a 0).val + (a 1).val = (a 2).val := by
  fo_simp [nodeChecks, Function.comp_def, not_le, and_assoc]
  refine forall_congr' fun u => imp_congr_right fun hu => ?_
  refine exists_congr fun a => ?_
  fo_simp (disch := (simp only [Term.realize_var, Term.realize_relabel, Function.comp_def,
      Sum.elim_inl, Sum.elim_inr]; lia)) [Function.comp_def]

omit [Fact (2 ≤ n)] in
private theorem count_eq_of_checks (m h k x : Fin n) (w : Fin 8 → ℕ)
    (hk : k.val = 2 ^ m.val)
    (hleaf : ∀ q : Fin n, q.val < k.val →
      EncodesNode m.val h.val w 0 q.val (x.val.testBit q.val).toNat)
    (hstep : ∀ u : Fin 7 → Fin n,
      ((u 0).val + 1 = (u 2).val ∧ (u 2).val + (u 3).val = m.val ∧
       (u 4).val = 2 ^ (u 3).val ∧ (u 1).val < (u 4).val ∧
       (u 1).val + (u 1).val = (u 5).val ∧ (u 5).val + 1 = (u 6).val) →
      ∃ a : Fin 3 → Fin n,
        EncodesNode m.val h.val w (u 0).val (u 5).val (a 0).val ∧
        EncodesNode m.val h.val w (u 0).val (u 6).val (a 1).val ∧
        EncodesNode m.val h.val w (u 2).val (u 1).val (a 2).val ∧
        (a 0).val + (a 1).val = (a 2).val)
    {j q z : ℕ} (hj : j ≤ m.val) (hq : q < 2 ^ (m.val - j))
    (hz : EncodesNode m.val h.val w j q z) : z = BitString.sumTree x.val.testBit j q := by
  induction j generalizing q z with
  | zero =>
    have hqk : q < k.val := by simpa only [hk, Nat.sub_zero] using hq
    exact hz.unique (hleaf ⟨q, lt_trans hqk k.isLt⟩ hqk)
  | succ j ih =>
    have hj' : j < m.val := by lia
    have hp : 2 ^ (m.val - (j + 1)) ≤ k.val := by
      rw [hk]
      exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    have hqk : q < k.val := lt_of_lt_of_le hq hp
    have hp' : 2 ^ (m.val - j) ≤ k.val := by
      rw [hk]
      exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    have he : m.val - j = m.val - (j + 1) + 1 := by lia
    have hl : 2 * q < 2 ^ (m.val - j) := by rw [he, pow_succ]; lia
    have hr : 2 * q + 1 < 2 ^ (m.val - j) := by rw [he, pow_succ]; lia
    let u : Fin 7 → Fin n := ![
      ⟨j, lt_trans hj' m.isLt⟩,
      ⟨q, lt_trans hqk k.isLt⟩,
      ⟨j + 1, lt_of_le_of_lt hj m.isLt⟩,
      ⟨m.val - (j + 1), lt_of_le_of_lt (Nat.sub_le _ _) m.isLt⟩,
      ⟨2 ^ (m.val - (j + 1)), lt_of_le_of_lt hp k.isLt⟩,
      ⟨2 * q, lt_of_lt_of_le hl hp' |>.trans k.isLt⟩,
      ⟨2 * q + 1, lt_of_lt_of_le hr hp' |>.trans k.isLt⟩]
    obtain ⟨a, ha, hb, hc, hab⟩ := hstep u
      ⟨rfl, by dsimp [u]; lia, rfl, hq, by dsimp [u]; lia, rfl⟩
    have ha' := ih (by lia) hl ha
    have hb' := ih (by lia) hr hb
    calc
      z = (a 2).val := hz.unique hc
      _ = (a 0).val + (a 1).val := hab.symm
      _ = BitString.sumTree x.val.testBit (j + 1) q := by rw [ha', hb', BitString.sumTree]

private theorem eight_mul_le_pow {h : ℕ} (hh : 8 ≤ h) : 8 * h ≤ 2 ^ h := by
  induction h, hh using Nat.le_induction with
  | base => decide
  | succ h hh ih =>
    rw [pow_succ]
    lia

private theorem exists_parameters {n : ℕ} (hn : 257 ≤ n) :
    ∃ h m : ℕ, 2 ^ h ≤ n - 1 ∧ n - 1 < 2 ^ (h + 1) ∧
      h < 2 ^ m ∧ 2 ^ m ≤ 2 * h ∧ 8 * h < n ∧ m < n := by
  let h := (n - 1).log2
  have hn0 : n - 1 ≠ 0 := by lia
  have hh8 : 8 ≤ h := (Nat.le_log2 hn0).mpr (by norm_num; lia)
  have hp : 2 ^ h ≤ n - 1 := Nat.log2_self_le hn0
  have hhi : n - 1 < 2 ^ (h + 1) := (Nat.log2_lt hn0).mp (by dsimp [h]; lia)
  have hspace : 8 * h < n := lt_of_le_of_lt (eight_mul_le_pow hh8) (by lia)
  have hh0 : h ≠ 0 := by lia
  have hk : h < 2 ^ (h.log2 + 1) := (Nat.log2_lt hh0).mp (by lia)
  have hk' : 2 ^ (h.log2 + 1) ≤ 2 * h := by
    rw [pow_succ]
    have := Nat.log2_self_le hh0
    lia
  have hm : h.log2 + 1 ≤ h := by
    have := (Nat.log2_lt hh0).mpr (Nat.lt_two_pow_self (n := h))
    lia
  exact ⟨h, h.log2 + 1, hp, hhi, hk, hk', hspace, by lia⟩

private theorem packedFormula_sound (v : Fin 2 → Fin n)
    (hf : (packedFormula L).Realize v) : (v 1).val = (v 0).val.bitIndices.length := by
  fo_simp [packedFormula, not_le, and_assoc] at hf
  obtain ⟨u, hp, hmax, hk, hhk, hd, hkd, ho, hleaf, hstep, hroot⟩ := hf
  have hspace : 8 * (u (.inl 0)).val < n := by have := (u (.inl 4)).isLt; lia
  rw [realize_leafChecks _ _ _ _ _ _ hspace] at hleaf
  rw [realize_nodeChecks _ _ _ _ hspace] at hstep
  rw [realize_nodeValue _ _ _ _ _ _ _ (by rfl) hspace] at hroot
  fo_simp at hleaf hstep hroot
  have ht := count_eq_of_checks (u (.inl 1)) (u (.inl 0)) (u (.inl 2)) (v 0)
    (fun r => (u (.inr r)).val) hk hleaf hstep (le_refl _) (by simp) hroot
  have hx : (v 0).val < 2 ^ (2 ^ (u (.inl 1)).val) := by
    have hxmax : (v 0).val ≤ n - 1 := by have := (v 0).isLt; lia
    have hle : (u (.inl 0)).val + 1 ≤ 2 ^ (u (.inl 1)).val := by lia
    exact lt_of_lt_of_le (lt_of_le_of_lt hxmax hmax)
      (Nat.pow_le_pow_right (by decide) hle)
  exact ht.trans (BitString.sumTree_testBit hx)

private theorem packedFormula_complete (v : Fin 2 → Fin n) (hn : 257 ≤ n)
    (hy : (v 1).val = (v 0).val.bitIndices.length) : (packedFormula L).Realize v := by
  obtain ⟨h, m, hp, hmax, hhk, hkd, hspace, hm⟩ := exists_parameters hn
  have hh : h < n := by lia
  have hk : 2 ^ m < n := by lia
  have hd : 2 * h < n := by lia
  have h4 : 4 * 2 ^ m ≤ 8 * h := by lia
  let w : Fin 8 → Fin n := fun r =>
    ⟨BitString.sumTreeWords (v 0).val.testBit m h r,
      lt_of_lt_of_le (BitString.sumTreeWords_lt _ _ _ _) (by lia : 2 ^ h ≤ n)⟩
  let u : Fin 5 ⊕ Fin 8 → Fin n := Sum.elim
    ![⟨h, hh⟩, ⟨m, hm⟩, ⟨2 ^ m, hk⟩, ⟨2 * h, hd⟩, ⟨8 * h, hspace⟩] w
  have hx : (v 0).val < 2 ^ (2 ^ m) := by
    have hxmax : (v 0).val ≤ n - 1 := by have := (v 0).isLt; lia
    exact lt_of_lt_of_le (lt_of_le_of_lt hxmax hmax)
      (Nat.pow_le_pow_right (by decide) (by lia))
  have hcount (j q : ℕ) (hj : j ≤ m) : BitString.sumTree (v 0).val.testBit j q < n :=
    lt_of_le_of_lt ((BitString.sumTree_le _ _ _).trans
      (Nat.pow_le_pow_right (by decide) hj)) hk
  fo_simp [packedFormula, not_le, and_assoc]
  refine ⟨u, hp, hmax, rfl, hhk, rfl, hkd, rfl, ?_, ?_, ?_⟩
  · rw [realize_leafChecks _ _ _ _ _ _ hspace]
    change ∀ q : Fin n, q.val < 2 ^ m →
      EncodesNode m h (BitString.sumTreeWords (v 0).val.testBit m h)
        0 q.val ((v 0).val.testBit q.val).toNat
    intro q hq
    simpa only [BitString.sumTree] using encodesNode_sumTree (v 0).val.testBit
      h4 (Nat.zero_le m) (by simpa only [Nat.sub_zero] using hq)
  · rw [realize_nodeChecks _ _ _ _ hspace]
    simp only [Term.realize_var, Sum.elim_inr]
    intro t ht
    obtain ⟨ht0, ht1, ht2, ht3, ht4, ht5⟩ := ht
    have hj : (t 0).val ≤ m := by change (t 2).val + (t 3).val = m at ht1; lia
    have hj' : (t 2).val ≤ m := by change (t 2).val + (t 3).val = m at ht1; lia
    have he : m - (t 2).val = (t 3).val := by
      change (t 2).val + (t 3).val = m at ht1
      lia
    have hq : (t 1).val < 2 ^ (m - (t 2).val) := by rw [he, ← ht2]; exact ht3
    have he' : m - (t 0).val = (t 3).val + 1 := by
      change (t 2).val + (t 3).val = m at ht1
      lia
    have hl : (t 5).val < 2 ^ (m - (t 0).val) := by
      rw [he', pow_succ, ← ht2]
      lia
    have hr : (t 6).val < 2 ^ (m - (t 0).val) := by
      rw [he', pow_succ, ← ht2]
      lia
    let a : Fin 3 → Fin n := ![
      ⟨BitString.sumTree (v 0).val.testBit (t 0).val (t 5).val, hcount _ _ hj⟩,
      ⟨BitString.sumTree (v 0).val.testBit (t 0).val (t 6).val, hcount _ _ hj⟩,
      ⟨BitString.sumTree (v 0).val.testBit (t 2).val (t 1).val, hcount _ _ hj'⟩]
    refine ⟨a, encodesNode_sumTree _ h4 hj hl, encodesNode_sumTree _ h4 hj hr,
      encodesNode_sumTree _ h4 hj' hq, ?_⟩
    change BitString.sumTree (v 0).val.testBit (t 0).val (t 5).val +
      BitString.sumTree (v 0).val.testBit (t 0).val (t 6).val =
        BitString.sumTree (v 0).val.testBit (t 2).val (t 1).val
    rw [← ht0, BitString.sumTree]
    congr 2 <;> lia
  · rw [realize_nodeValue _ _ _ _ _ _ _ (by rfl) hspace]
    change EncodesNode m h (BitString.sumTreeWords (v 0).val.testBit m h) m 0 (v 1).val
    rw [hy, ← BitString.sumTree_testBit hx]
    exact encodesNode_sumTree _ h4 (le_refl m) (by simp)

private theorem realize_smallFormula (v : Fin 2 → Fin n) :
    (smallFormula L).Realize v ↔
      (v 0).val < 256 ∧ (v 1).val = (v 0).val.bitIndices.length := by
  fo_simp [smallFormula]
  constructor
  · rintro ⟨a, ha, hy⟩
    exact ⟨ha ▸ a.isLt, by simpa only [ha] using hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨(v 0).val, hx⟩, rfl, hy⟩

end BitSum

/-- The number of set bits, defined uniformly from canonical order and BIT. -/
public noncomputable def bitSum (L : Language) : (language L).Formula (Fin 2) :=
  BitSum.smallFormula L ⊔ BitSum.packedFormula L

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]

/-- The native Bit Sum formula counts all set bits, for every canonical universe size. -/
@[simp, fo_realize]
public theorem realize_bitSum (v : Fin 2 → Fin n) :
    (bitSum L).Realize v ↔ (v 1).val = (v 0).val.bitIndices.length := by
  rw [bitSum, Formula.realize_sup, BitSum.realize_smallFormula]
  constructor
  · rintro (⟨_, hy⟩ | hf)
    · exact hy
    · exact BitSum.packedFormula_sound v hf
  · intro hy
    by_cases hx : (v 0).val < 256
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr (BitSum.packedFormula_complete v (by have := (v 0).isLt; lia) hy)

/-- The bit count always fits in the input's universe and is uniquely defined. -/
public theorem existsUnique_bitSum (x : Fin n) :
    ∃! y : Fin n, (bitSum L).Realize ![x, y] := by
  have hle : x.val.bitIndices.length ≤ x.val := by
    have h := List.length_le_sum_of_one_le (x.val.bitIndices.map (fun i => 2 ^ i)) (by
      intro i hi
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
      exact Nat.one_le_two_pow)
    simpa only [List.length_map, Nat.sum_map_two_pow_bitIndices] using h
  refine ⟨⟨_, lt_of_le_of_lt hle x.isLt⟩, ?_, ?_⟩
  · exact (realize_bitSum _).mpr rfl
  · intro y hy
    apply Fin.ext
    simpa only [realize_bitSum, Matrix.cons_val_one, Matrix.cons_val_zero] using hy

end Cslib.Logic.FO.Ordered
