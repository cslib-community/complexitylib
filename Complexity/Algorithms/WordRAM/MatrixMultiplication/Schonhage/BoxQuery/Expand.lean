/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.ExpandMemory

/-!
# Complete native expansion of one query prefix

The program decodes the actual output digit, then pushes exactly the existing ordered
child family. This theorem covers all native setup, branch, descriptor and stack-store
instructions. It preserves older pending tasks and every word outside the new records.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

private theorem output_digit_nine_iff (z : OutVar) :
    (PrunedQuery.outputDigits.symm z).val = 9 ↔ z.IsInner := by decide +revert

/-- Native division and remainder read the existing output-coordinate digit exactly. -/
theorem query_digit_at {L k : ℕ} (η : OutStr L) (hk : k < L) :
    (PrunedQuery.queryIndex η).val / 10 ^ k % 10 =
      (PrunedQuery.outputDigits.symm (outAt η k)).val := by
  have hd := finFunctionFinEquiv_symm_apply_val (PrunedQuery.queryIndex η) (⟨k, hk⟩ : Fin L)
  simpa [PrunedQuery.queryIndex, Encoding.leafIndex, privateLeaf, outAt, hk,
    PrunedQuery.outputDigits] using hd.symm

/-- Registers that may change while computing and pushing the complete child family. -/
@[expose] def ExpandLocal (i : Fin registers) : Prop :=
  ExpandSetupLocal i ∨ IndexedPushLocal i

instance (i : Fin registers) : Decidable (ExpandLocal i) :=
  inferInstanceAs (Decidable (ExpandSetupLocal i ∨ IndexedPushLocal i))

private theorem expand_preserves (i : Fin registers) :
    ¬ExpandLocal i → expand.Preserves i := by decide +revert

/-- The actual internal-node code prepends exactly its genuine children, with no layout oracle. -/
theorem exec_expand {w L t F : ℕ} (η : OutStr L) (xs : List Term)
    (rest : List (List Term)) (x : Data registers)
    (hx : Good η t xs) (hk : xs.length < L)
    (hrest : StackMemory η F rest x.mem)
    (hF : x.regs Reg.stack = F) (hn : x.regs Reg.top = rest.length)
    (hq : x.regs Reg.query = (PrunedQuery.queryIndex η).val)
    (ht : x.regs BoxTable.Reg.threshold = t)
    (hdepth : x.regs Reg.depth = xs.length) (hc : x.regs Reg.code = prefixCode xs)
    (hu : x.regs Reg.used = usedFrom η 0 xs) (he : x.regs Reg.stars = starsFrom η 0 xs)
    (hp : x.regs Reg.power = 10 ^ xs.length)
    (h5 : x.regs Reg.five = 5) (h1 : x.regs BoxTable.Reg.one = 1)
    (h10 : x.regs BoxTable.Reg.ten = 10) (h9 : x.regs BoxTable.Reg.nine = 9)
    (h0 : x.regs BoxTable.Reg.nil = 0)
    (hfit : Fits w (F + 5 * (rest.length + 11) + 10 ^ (xs.length + 1) + xs.length +
      t + (PrunedQuery.queryIndex η).val + 32)) :
    ∃ y, ExecWithin w expand x y 178 ∧
      y.regs Reg.top = rest.length + (children η t xs).length ∧
      StackMemory η F (children η t xs ++ rest) y.mem ∧
      (∀ q, ¬(F + rest.length * 5 ≤ q ∧
        q < F + (rest.length + (children η t xs).length) * 5) → y.mem q = x.mem q) ∧
      (∀ i, ¬ExpandLocal i → y.regs i = x.regs i) := by
  have hused := hx.2.2
  have hstars := starsFrom_le η 0 xs
  have hcode := prefixCode_lt xs
  have hcode' : prefixCode xs + 9 * 10 ^ xs.length ≤ 10 ^ (xs.length + 1) := by
    rw [pow_succ]
    omega
  have hcommon : Fits w (F + 5 * (rest.length + 11) + prefixCode xs +
      9 * 10 ^ xs.length + usedFrom η 0 xs + starsFrom η 0 xs + 32) :=
    hfit.of_le (by omega)
  have hdecode : Fits w ((PrunedQuery.queryIndex η).val + xs.length +
      10 * 10 ^ xs.length + 16) := hfit.of_le (by rw [pow_succ]; omega)
  obtain ⟨a, ha, ad, ak, ap, am, af⟩ := exec_expandSetup x hq hdepth hp h1 h10 hdecode
  have aF : a.regs Reg.stack = F := (af _ (by decide)).trans hF
  have an : a.regs Reg.top = rest.length := (af _ (by decide)).trans hn
  have ac : a.regs Reg.code = prefixCode xs := (af _ (by decide)).trans hc
  have au : a.regs Reg.used = usedFrom η 0 xs := (af _ (by decide)).trans hu
  have ae : a.regs Reg.stars = starsFrom η 0 xs := (af _ (by decide)).trans he
  have app : a.regs Reg.power = 10 ^ xs.length := (af _ (by decide)).trans hp
  have a5 : a.regs Reg.five = 5 := (af _ (by decide)).trans h5
  have a1 : a.regs BoxTable.Reg.one = 1 := (af _ (by decide)).trans h1
  have a9 : a.regs BoxTable.Reg.nine = 9 := (af _ (by decide)).trans h9
  have a0 : a.regs BoxTable.Reg.nil = 0 := (af _ (by decide)).trans h0
  have athreshold : a.regs BoxTable.Reg.threshold = t := (af _ (by decide)).trans ht
  have adigit : a.regs Reg.digit = (PrunedQuery.outputDigits.symm
      (outAt η xs.length)).val := ad.trans (query_digit_at η hk)
  have apow : a.regs Reg.childPower = 10 ^ (xs.length + 1) := by
    simpa only [pow_succ] using ap
  have arest : StackMemory η F rest a.mem := by simpa only [am] using hrest
  by_cases hi : (outAt η xs.length).IsInner
  · have acond : (Cond.eq Reg.digit BoxTable.Reg.nine).Holds a := by
      simp only [Cond.holds_eq, adigit, a9]
      exact (output_digit_nine_iff _).mpr hi
    by_cases hspare : usedFrom η 0 xs < t
    · obtain ⟨b, hb, bn, bm, bf⟩ := exec_nineChildren (F := F) (n := rest.length)
        (k := xs.length + 1) (c := prefixCode xs) (u := usedFrom η 0 xs)
        (e := starsFrom η 0 xs) (p := 10 ^ xs.length) (cp := 10 ^ (xs.length + 1))
        a aF an ak ac au ae app apow a5 a1
        (hcommon.of_le (by omega))
      have bF : b.regs Reg.stack = F := (bf _ (by decide)).trans aF
      have bk : b.regs Reg.depth = xs.length + 1 := (bf _ (by decide)).trans ak
      have bc : b.regs Reg.code = prefixCode xs := (bf _ (by decide)).trans ac
      have bu : b.regs Reg.used = usedFrom η 0 xs := (bf _ (by decide)).trans au
      have be : b.regs Reg.stars = starsFrom η 0 xs := (bf _ (by decide)).trans ae
      have bp : b.regs Reg.power = 10 ^ xs.length := (bf _ (by decide)).trans app
      have bcp : b.regs Reg.childPower = 10 ^ (xs.length + 1) := (bf _ (by decide)).trans apow
      have b5 : b.regs Reg.five = 5 := (bf _ (by decide)).trans a5
      have b1 : b.regs BoxTable.Reg.one = 1 := (bf _ (by decide)).trans a1
      have b9 : b.regs BoxTable.Reg.nine = 9 := (bf _ (by decide)).trans a9
      have b0 : b.regs BoxTable.Reg.nil = 0 := (bf _ (by decide)).trans a0
      obtain ⟨y, hy, yn, ym, _⟩ := exec_p0Child (F := F) (n := rest.length + 9)
        (k := xs.length + 1) (c := prefixCode xs) (u := usedFrom η 0 xs)
        (e := starsFrom η 0 xs) (p := 10 ^ xs.length) (cp := 10 ^ (xs.length + 1))
        b bF bn bk bc bu be bp bcp b5 b1 b9 b0
        (hcommon.of_le (by omega))
      have hsparecond : (Cond.lt Reg.used BoxTable.Reg.threshold).Holds a := by
        simp only [Cond.holds_lt, au, athreshold]
        exact hspare
      have hb' : ExecWithin w (.branch (.lt Reg.used BoxTable.Reg.threshold)
          nineChildren (ram[ Reg.temporary ← Reg.temporary ])) a b 155 :=
        hb.branch_pos hsparecond
      have hex : ExecWithin w expand x y 178 :=
        (ha.seq ((hb'.seq hy).branch_pos acond)).mono (by omega)
      refine ⟨y, hex, ?_, ?_, ?_, fun i h => hex.regs_eq (expand_preserves i h)⟩
      · simpa [children, hi, hspare, Nat.add_assoc] using yn
      · have hs := arest.indexedChildren xs hi
          (List.ofFn fun i : Fin 9 => (⟨8 - i.val, by omega⟩ : Fin 9))
        rw [reverse_nineChildren] at hs
        have bs : StackMemory η F
            ((List.ofFn fun d : Fin 9 => xs ++ [Encoding.termDigits ⟨d.val, by omega⟩]) ++ rest)
            b.mem := by simpa only [bm] using hs
        have hpush := bs.p0Child xs hi
        simp only [List.length_append, List.length_ofFn] at hpush
        rw [show 9 + rest.length = rest.length + 9 by omega] at hpush
        rw [ym]
        simpa only [children, ite_eq_left hi, ite_eq_left hspare, List.cons_append] using hpush
      · intro q hqout
        have hlen : (children η t xs).length = 10 := by simp [children, hi, hspare]
        rw [ym, writeTask_frame, bm, writeIndexedChildren_frame, am]
        · simp only [List.length_ofFn]
          rw [hlen] at hqout
          omega
        · rw [hlen] at hqout
          omega
    · let b := a.set Reg.temporary (a.regs Reg.temporary)
      have hb : ExecWithin (B := .standard) w
          (ram[ Reg.temporary ← Reg.temporary ]) a b 1 := ExecWithin.copy
      have bframe (i : Fin registers) (h : i ≠ Reg.temporary) : b.regs i = a.regs i := by
        simp only [b, Data.set_regs, Function.update_of_ne h]
      obtain ⟨y, hy, yn, ym, _⟩ := exec_p0Child (F := F) (n := rest.length)
        (k := xs.length + 1) (c := prefixCode xs) (u := usedFrom η 0 xs)
        (e := starsFrom η 0 xs) (p := 10 ^ xs.length) (cp := 10 ^ (xs.length + 1)) b
        ((bframe _ (by decide)).trans aF) ((bframe _ (by decide)).trans an)
        ((bframe _ (by decide)).trans ak) ((bframe _ (by decide)).trans ac)
        ((bframe _ (by decide)).trans au) ((bframe _ (by decide)).trans ae)
        ((bframe _ (by decide)).trans app) ((bframe _ (by decide)).trans apow)
        ((bframe _ (by decide)).trans a5) ((bframe _ (by decide)).trans a1)
        ((bframe _ (by decide)).trans a9) ((bframe _ (by decide)).trans a0)
        (hcommon.of_le (by omega))
      have hsparecond : ¬(Cond.lt Reg.used BoxTable.Reg.threshold).Holds a := by
        simp only [Cond.holds_lt, au, athreshold]
        exact hspare
      have hb' : ExecWithin w (.branch (.lt Reg.used BoxTable.Reg.threshold)
          nineChildren (ram[ Reg.temporary ← Reg.temporary ])) a b 3 :=
        hb.branch_neg hsparecond
      have hex : ExecWithin w expand x y 178 :=
        (ha.seq ((hb'.seq hy).branch_pos acond)).mono (by omega)
      refine ⟨y, hex, ?_, ?_, ?_, fun i h => hex.regs_eq (expand_preserves i h)⟩
      · simpa [children, hi, hspare] using yn
      · rw [ym]
        simpa only [b, Data.set_mem, children, ite_eq_left hi, ite_eq_right hspare,
          List.cons_append, List.nil_append] using arest.p0Child xs hi
      · intro q hqout
        rw [ym, writeTask_frame]
        · exact congrFun am q
        · simp only [children, ite_eq_left hi, ite_eq_right hspare, List.length_cons,
            List.length_nil] at hqout
          omega
  · have acond : ¬(Cond.eq Reg.digit BoxTable.Reg.nine).Holds a := by
      simp only [Cond.holds_eq, adigit, a9]
      exact fun h => hi ((output_digit_nine_iff _).mp h)
    have hd : (PrunedQuery.outputDigits.symm (outAt η xs.length)).val ≤ 9 :=
      Nat.le_of_lt_succ (PrunedQuery.outputDigits.symm _).isLt
    obtain ⟨y, hy, yn, ym, _⟩ := exec_privateChild (F := F) (n := rest.length)
      (k := xs.length + 1) (c := prefixCode xs) (u := usedFrom η 0 xs)
      (e := starsFrom η 0 xs) (p := 10 ^ xs.length) (cp := 10 ^ (xs.length + 1))
      a hd aF an ak ac au ae app apow
      adigit a5 a1 (hcommon.of_le (by omega))
    have hex : ExecWithin w expand x y 178 := (ha.seq (hy.branch_neg acond)).mono (by omega)
    refine ⟨y, hex, ?_, ?_, ?_, fun i h => hex.regs_eq (expand_preserves i h)⟩
    · simpa [children, hi] using yn
    · rw [ym]
      simpa only [children, ite_eq_right hi, List.singleton_append] using arest.privateChild xs hi
    · intro q hqout
      rw [ym, writeTask_frame, am]
      simp only [children, ite_eq_right hi, List.length_singleton] at hqout
      omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
