/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Select

/-!
# Compact native frontend scans

Each pass reads both canonical keys and their full multiplicities. It appends only selected
keys to a disjoint destination. The singleton-zero arrays are written separately, so empty
input needs no exceptional semantics.

## Main definitions

* `Scan.program`: charged compact selection from the radix output.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend.Scan

open Cslib.WordRAM Select

/-- Key pointer, count pointer and number of distinct keys. -/
abbrev keys : Fin 48 := 20
@[inherit_doc keys] abbrev counts : Fin 48 := 21
@[inherit_doc keys] abbrev len : Fin 48 := 22
/-- Output pointer, input cursor and output length. -/
abbrev dst : Fin 48 := 23
@[inherit_doc dst] abbrev idx : Fin 48 := 24
@[inherit_doc dst] abbrev out : Fin 48 := 25
/-- Address scratch. -/
abbrev addr : Fin 48 := 26

/-- Load one full key/count pair, compute its selection, optionally append, and advance. -/
def body : Code .standard 48 :=
  .seq (ram[ addr ← keys + idx; key ← *addr; addr ← counts + idx; count ← *addr ])
    (.seq Select.program (ram[
      if take = one then [ addr ← dst + out; *addr ← key; out ← out + one ]
        else [ addr ← addr ]; idx ← idx + one ]))

/-- Reset both cursors and scan all distinct keys. -/
def program : Code .standard 48 :=
  .seq (ram[ idx ← #0; out ← #0 ]) (.loop (.lt idx len) body)

/-- One charged compacting iteration. -/
theorem step {w : ℕ} (x : Data 48)
    (hz : x.regs zero = 0) (h1 : x.regs one = 1) (h2 : x.regs two = 2)
    (h3 : x.regs three = 3) (h4 : x.regs four = 4) (h5 : x.regs five = 5)
    (hsmall : Fits w 5)
    (hkaddr : Fits w (x.regs keys + x.regs idx))
    (hcaddr : Fits w (x.regs counts + x.regs idx))
    (hdaddr : Fits w (x.regs dst + x.regs out))
    (hi : Fits w (x.regs idx + 1)) (ho : Fits w (x.regs out + 1))
    (hkey : Fits w (x.mem (x.regs keys + x.regs idx)))
    (habs : x.mem (x.regs keys + x.regs idx) / 2 ≤ 2 * x.regs magnitude)
    (hfit : Fits w (4 * x.regs magnitude + 2))
    (hdouble : Fits w (2 * x.mem (x.regs keys + x.regs idx))) :
    let p := (x.mem (x.regs keys + x.regs idx), x.mem (x.regs counts + x.regs idx))
    let k := Math.keep (x.regs magnitude) (x.regs beta) (x.regs beta')
      (x.regs digit) (x.regs mode) p
    ∃ y, ExecWithin w body x y 41 ∧
      y.regs idx = x.regs idx + 1 ∧ y.regs out = x.regs out + k.toNat ∧
      y.mem = (if k then Function.update x.mem (x.regs dst + x.regs out)
        (Math.value (x.regs mode) p.1) else x.mem) := by
  dsimp only
  let p := (x.mem (x.regs keys + x.regs idx), x.mem (x.regs counts + x.regs idx))
  let a := (((x.set addr (x.regs keys + x.regs idx)).set key p.1).set
    addr (x.regs counts + x.regs idx)).set count p.2
  have ha : ExecWithin w
      (ram[ addr ← keys + idx; key ← *addr; addr ← counts + idx; count ← *addr ]) x a 4 := by
    ram_eval [a, p, hkaddr, hcaddr, hkey]
  obtain ⟨u, hu, hut, huk, hum⟩ := Select.exec a
    (by simpa +decide [a] using hz) (by simpa +decide [a] using h1)
    (by simpa +decide [a] using h2) (by simpa +decide [a] using h3)
    (by simpa +decide [a] using h4) (by simpa +decide [a] using h5)
    hkey (by simpa +decide [a, p] using habs) (by simpa +decide [a] using hfit)
    hdouble hsmall
  have hui : u.regs idx = x.regs idx := by
    simpa +decide [a] using hu.regs_eq (i := idx) (by decide)
  have huo : u.regs out = x.regs out := by
    simpa +decide [a] using hu.regs_eq (i := out) (by decide)
  have hud : u.regs dst = x.regs dst := by
    simpa +decide [a] using hu.regs_eq (i := dst) (by decide)
  have hu1 : u.regs one = 1 := by
    simpa +decide [a] using (hu.regs_eq (i := one) (by decide)).trans
      (show a.regs one = 1 by simpa +decide [a] using h1)
  simp +decide only [a, Data.set_regs, Function.update_apply, ↓reduceIte] at hut huk hum
  let k := Math.keep (x.regs magnitude) (x.regs beta) (x.regs beta')
    (x.regs digit) (x.regs mode) p
  have hv : Fits w (Math.value (x.regs mode) p.1) := by
    dsimp only [Math.value, Math.twice]
    split_ifs
    · exact hdouble.of_le (Nat.sub_le _ _)
    · exact hkey
  have hdo : Fits w (u.regs dst + u.regs out) := by simpa only [hud, huo] using hdaddr
  have hii : Fits w (u.regs idx + 1) := by simpa only [hui] using hi
  have hoo : Fits w (u.regs out + 1) := by simpa only [huo] using ho
  have hvu : Fits w (u.regs key) := by rw [huk]; exact hv
  by_cases he : k = true
  · have ht : u.regs take = 1 := by rw [hut]; change k.toNat = 1; simp [he]
    have ht' : ExecWithin w
        (ram[ if take = one then [ addr ← dst + out; *addr ← key; out ← out + one ]
          else [ addr ← addr ]; idx ← idx + one ]) u ?posY 6 := by
      ram_eval [ht, hu1, hdo, hii, hoo, hvu]
    refine ⟨?posY, ha.seq (hu.seq ht'), ?_, ?_, ?_⟩
    · simp +decide [Data.set_regs, hui]
    · simp +decide [Data.set_regs, huo, k, p, he]
    · simp +decide [Data.set_mem, Data.write_mem, hud, huo, huk, hum, k, p, he]
  · have he' : k = false := Bool.eq_false_iff.mpr he
    have ht : u.regs take = 0 := by rw [hut]; change k.toNat = 0; simp [he']
    have ht' : ExecWithin w
        (ram[ if take = one then [ addr ← dst + out; *addr ← key; out ← out + one ]
          else [ addr ← addr ]; idx ← idx + one ]) u ?negY 6 := by
      ram_eval [ht, hu1, hii]
    refine ⟨?negY, ha.seq (hu.seq ht'), ?_, ?_, ?_⟩
    · simp +decide [Data.set_regs, hui]
    · simp +decide [Data.set_regs, huo, k, p, he']
    · simpa only [k, p, he', Bool.false_eq_true, ↓reduceIte, Data.set_mem] using hum

/-- Complete compact scan, with arbitrary old output/scratch memory and an exact memory frame.
The source key/count blocks precede the output; their contents and all caller registers that
the body does not write are retained. -/
theorem exec {w : ℕ} (rs : List (ℕ × ℕ)) (x : Data 48)
    (hn : x.regs len = rs.length)
    (hz : x.regs zero = 0) (h1 : x.regs one = 1) (h2 : x.regs two = 2)
    (h3 : x.regs three = 3) (h4 : x.regs four = 4) (h5 : x.regs five = 5)
    (hk : Block.HoldsList (x.regs keys) (rs.map Prod.fst) x.mem)
    (hc : Block.HoldsList (x.regs counts) (rs.map Prod.snd) x.mem)
    (hkey : ∀ p ∈ rs, Fits w p.1)
    (habs : ∀ p ∈ rs, p.1 / 2 ≤ 2 * x.regs magnitude)
    (hdouble : ∀ p ∈ rs, Fits w (2 * p.1))
    (hfit : Fits w (4 * x.regs magnitude + 2)) (hsmall : Fits w 5)
    (hka : Fits w (x.regs keys + rs.length))
    (hca : Fits w (x.regs counts + rs.length))
    (hda : Fits w (x.regs dst + rs.length + 1))
    (hkd : x.regs keys + rs.length ≤ x.regs dst)
    (hcd : x.regs counts + rs.length ≤ x.regs dst) :
    ∃ y, ExecWithin w program x y (43 * rs.length + 4) ∧
      Block.HoldsList (x.regs dst)
        (Math.select (x.regs magnitude) (x.regs beta) (x.regs beta')
          (x.regs digit) (x.regs mode) rs) y.mem ∧
      y.regs out = (Math.select (x.regs magnitude) (x.regs beta) (x.regs beta')
          (x.regs digit) (x.regs mode) rs).length ∧
      Modifies (Block.mk (x.regs dst) rs.length).footprint x.mem y.mem ∧
      (∀ j, body.Preserves j → y.regs j = x.regs j) := by
  let selected (i : ℕ) := Math.select (x.regs magnitude) (x.regs beta) (x.regs beta')
    (x.regs digit) (x.regs mode) (rs.take i)
  have hselected (i : ℕ) : (selected i).length ≤ min i rs.length :=
    (Math.length_select_le _ _ _ _ _ _).trans_eq List.length_take
  let I (y : Data 48) : Prop :=
    (∀ j, body.Preserves j → y.regs j = x.regs j) ∧
    y.regs idx ≤ rs.length ∧ y.regs out = (selected (y.regs idx)).length ∧
    Block.HoldsList (x.regs keys) (rs.map Prod.fst) y.mem ∧
    Block.HoldsList (x.regs counts) (rs.map Prod.snd) y.mem ∧
    Block.HoldsList (x.regs dst) (selected (y.regs idx)) y.mem ∧
    Modifies (Block.mk (x.regs dst) rs.length).footprint x.mem y.mem
  have hbody (y : Data 48) (hy : I y) (ht : (Cond.lt idx len).Holds y) :
      ∃ z, ExecWithin w body y z 41 ∧ I z ∧
        rs.length - z.regs idx < rs.length - y.regs idx := by
    obtain ⟨hr, hle, hout, hkeys, hcounts, hacc, hframe⟩ := hy
    have hyl := (hr len (by decide)).trans hn
    have hys := hr keys (by decide)
    have hyc := hr counts (by decide)
    have hyd := hr dst (by decide)
    have hyU := hr magnitude (by decide)
    have hyb := hr beta (by decide)
    have hyb' := hr beta' (by decide)
    have hyv := hr digit (by decide)
    have hym := hr mode (by decide)
    have hi : y.regs idx < rs.length := by simpa only [Cond.holds_lt, hyl] using ht
    have hgetk : y.mem (y.regs keys + y.regs idx) = rs[y.regs idx].1 := by
      rw [hys]
      exact (hkeys.get (y.regs idx) (by simpa using hi)).trans (List.getElem_map _)
    have hgetc : y.mem (y.regs counts + y.regs idx) = rs[y.regs idx].2 := by
      rw [hyc]
      exact (hcounts.get (y.regs idx) (by simpa using hi)).trans (List.getElem_map _)
    have hu : y.regs out ≤ y.regs idx := by
      rw [hout]; exact (hselected _).trans (min_le_left _ _)
    obtain ⟨z, he, hzi, hzo, hzm⟩ := step y
      ((hr zero (by decide)).trans hz) ((hr one (by decide)).trans h1)
      ((hr two (by decide)).trans h2) ((hr three (by decide)).trans h3)
      ((hr four (by decide)).trans h4) ((hr five (by decide)).trans h5) hsmall
      (hka.of_le (by rw [hys]; omega)) (hca.of_le (by rw [hyc]; omega))
      (hda.of_le (by rw [hyd]; omega)) (hka.of_le (by omega)) (hda.of_le (by omega))
      (by rw [hgetk]; exact hkey _ (List.getElem_mem hi))
      (by rw [hgetk, hyU]; exact habs _ (List.getElem_mem hi))
      (by simpa only [hyU] using hfit)
      (by rw [hgetk]; exact hdouble _ (List.getElem_mem hi))
    dsimp only at hzo hzm
    rw [hyU, hyb, hyb', hyv, hym, hgetk, hgetc] at hzo hzm
    let k := Math.keep (x.regs magnitude) (x.regs beta) (x.regs beta')
      (x.regs digit) (x.regs mode) rs[y.regs idx]
    change z.regs out = y.regs out + k.toNat at hzo
    change z.mem = (if k then Function.update y.mem (y.regs dst + y.regs out)
      (Math.value (x.regs mode) rs[y.regs idx].1) else y.mem) at hzm
    have hsuc : selected (y.regs idx + 1) = selected (y.regs idx) ++
        (if k then [Math.value (x.regs mode) rs[y.regs idx].1] else []) := by
      dsimp only [selected]
      rw [List.take_succ_eq_append_getElem hi]
      simp only [Math.select, List.filter_append, List.map_append, List.filter_cons,
        List.filter_nil]
      split_ifs <;> rfl
    have hf (a : ℕ) (hne : a ≠ x.regs dst + y.regs out) : z.mem a = y.mem a := by
      rw [hzm, hyd]
      split_ifs <;> simp only [Function.update_of_ne hne]
    refine ⟨z, he, ?_, by omega⟩
    refine ⟨?_, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      exact (he.regs_eq hj).trans (hr j hj)
    · rw [hzi, hsuc, List.length_append, hzo, hout]
      cases k <;> simp
    · apply hkeys.frame
      intro a hlo hhi
      apply hf
      simp only [List.length_map] at hhi
      omega
    · apply hcounts.frame
      intro a hlo hhi
      apply hf
      simp only [List.length_map] at hhi
      omega
    · rw [hzi, hsuc]
      by_cases htake : k = true
      · rw [ite_eq_left htake]
        have hm : z.mem = Function.update y.mem (x.regs dst + (selected (y.regs idx)).length)
            (Math.value (x.regs mode) rs[y.regs idx].1) := by
          simpa only [htake, ↓reduceIte, hyd, hout] using hzm
        rw [hm]
        exact hacc.append_one _
      · have hfalse : k = false := Bool.eq_false_iff.mpr htake
        rw [ite_eq_right htake, List.append_nil]
        have hm : z.mem = y.mem := by simpa only [hfalse, Bool.false_eq_true, ↓reduceIte]
          using hzm
        simpa only [hm] using hacc
    · intro a hnot
      have hne : a ≠ x.regs dst + y.regs out := by
        intro ha
        apply hnot
        apply Block.mem_footprint.mpr
        change x.regs dst ≤ a ∧ a < x.regs dst + rs.length
        omega
      exact (hf a hne).trans (hframe a hnot)
  let x₀ := (x.set idx 0).set out 0
  have hx₀ : I x₀ := by
    refine ⟨?_, ?_, ?_, hk, hc, ?_, Modifies.refl _ _⟩
    · intro j hj
      have hji : j ≠ idx := by rintro rfl; exact (by decide : ¬body.Preserves idx) hj
      have hjo : j ≠ out := by rintro rfl; exact (by decide : ¬body.Preserves out) hj
      simp only [x₀, Data.set_regs, Function.update_of_ne hji, Function.update_of_ne hjo]
    · simp +decide [x₀]
    · simp +decide [x₀, selected, Math.select]
    · simpa +decide [x₀, selected, Math.select] using Block.holdsList_nil (x.regs dst) x.mem
  obtain ⟨y, he, hy, ht⟩ := ExecWithin.loop_invariant I
    (fun y => rs.length - y.regs idx) hbody hx₀
  obtain ⟨hr, hle, hout, _, _, hacc, hframe⟩ := hy
  have hend : y.regs idx = rs.length := by
    have hyl := (hr len (by decide)).trans hn
    simp only [Cond.holds_lt, hyl] at ht
    omega
  have hinit : ExecWithin (B := .standard) w (ram[ idx ← #0; out ← #0 ]) x x₀ 2 := by
    ram_eval [x₀]
  refine ⟨y, ?_, ?_, ?_, hframe, hr⟩
  · convert hinit.seq he using 1
    · rfl
    · simp +decide only [x₀, Data.set_regs, Function.update_apply, ↓reduceIte, Nat.sub_zero]
      omega
  · simpa only [hend, selected, List.take_length] using hacc
  · simpa only [hend, selected, List.take_length] using hout

end Cslib.Algorithms.WordRAM.ThreeSum.Frontend.Scan
