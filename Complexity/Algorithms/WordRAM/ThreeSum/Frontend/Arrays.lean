/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Program

/-!
# Native frontend array and descriptor execution

## Main results

The compact scan contract is composed with every array setup and descriptor store.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend.Arrays

open Cslib.WordRAM Select Scan

/-- Local arithmetic budget covers array addresses, native labels and loop setup. -/
def budget (l : Layout) (U : ℕ) : ℕ := l.endpoint + 8 * U + 8 * l.digits + 64

/-- The hypotheses of a concrete compact scan, before choosing its bit coordinates and mode. -/
structure ScanReady (w : ℕ) (rs : List (ℕ × ℕ)) (x : Data 48) : Prop where
  /-- The source length is the distinct-key count. -/
  length : x.regs len = rs.length
  /-- Native small constants. -/
  constants : x.regs zero = 0 ∧ x.regs one = 1 ∧ x.regs two = 2 ∧
    x.regs three = 3 ∧ x.regs four = 4 ∧ x.regs five = 5
  /-- Both radix arrays have exact contents. -/
  keys : Block.HoldsList (x.regs Scan.keys) (rs.map Prod.fst) x.mem
  counts : Block.HoldsList (x.regs Scan.counts) (rs.map Prod.snd) x.mem
  /-- Every key and the native label arithmetic fit. -/
  words : ∀ p ∈ rs, Fits w p.1
  absolute : ∀ p ∈ rs, p.1 / 2 ≤ 2 * x.regs magnitude
  double : ∀ p ∈ rs, Fits w (2 * p.1)
  labels : Fits w (4 * x.regs magnitude + 2)
  small : Fits w 5
  /-- Source and output endpoints fit. -/
  keyAddress : Fits w (x.regs Scan.keys + rs.length)
  countAddress : Fits w (x.regs Scan.counts + rs.length)
  outputAddress : Fits w (x.regs dst + rs.length + 1)
  /-- Both source blocks precede the output. -/
  keysBefore : x.regs Scan.keys + rs.length ≤ x.regs dst
  countsBefore : x.regs Scan.counts + rs.length ≤ x.regs dst

/-- Parameters changed by split/mode setup. -/
def ScanParametersPreserved (x y : Data 48) : Prop :=
  y.mem = x.mem ∧ ∀ j, j.val < 27 → j ≠ beta → j ≠ beta' → j ≠ digit → j ≠ mode →
    y.regs j = x.regs j

/-- A mode/bit setup preserves every actual scan precondition. -/
theorem ScanReady.transfer {w : ℕ} {rs : List (ℕ × ℕ)} {x y : Data 48}
    (h : ScanReady w rs x) (he : ScanParametersPreserved x y) : ScanReady w rs y := by
  obtain ⟨hm, hr⟩ := he
  have eq (j : Fin 48) (hlt : j.val < 27) (hj : j ≠ beta ∧ j ≠ beta' ∧ j ≠ digit ∧ j ≠ mode) :
      y.regs j = x.regs j := hr j hlt hj.1 hj.2.1 hj.2.2.1 hj.2.2.2
  constructor
  · simpa only [eq len (by decide) (by decide)] using h.length
  · simpa only [eq zero (by decide) (by decide), eq one (by decide) (by decide),
    eq two (by decide) (by decide),
      eq three (by decide) (by decide), eq four (by decide) (by decide),
        eq five (by decide) (by decide)] using h.constants
  · simpa only [eq Scan.keys (by decide) (by decide), hm] using h.keys
  · simpa only [eq Scan.counts (by decide) (by decide), hm] using h.counts
  · exact h.words
  · simpa only [eq magnitude (by decide) (by decide)] using h.absolute
  · exact h.double
  · simpa only [eq magnitude (by decide) (by decide)] using h.labels
  · exact h.small
  · simpa only [eq Scan.keys (by decide) (by decide)] using h.keyAddress
  · simpa only [eq Scan.counts (by decide) (by decide)] using h.countAddress
  · simpa only [eq dst (by decide) (by decide)] using h.outputAddress
  · simpa only [eq Scan.keys (by decide) (by decide),
    eq dst (by decide) (by decide)] using h.keysBefore
  · simpa only [eq Scan.counts (by decide) (by decide),
    eq dst (by decide) (by decide)] using h.countsBefore

/-- Invoke the proved native scan from its actual arithmetic/layout context. -/
theorem ScanReady.exec {w : ℕ} {rs : List (ℕ × ℕ)} {x : Data 48}
    (h : ScanReady w rs x) :
    ∃ y, ExecWithin w Scan.program x y (43 * rs.length + 4) ∧
      Block.HoldsList (x.regs dst) (Math.select (x.regs magnitude) (x.regs beta)
        (x.regs beta') (x.regs digit) (x.regs mode) rs) y.mem ∧
      y.regs out = (Math.select (x.regs magnitude) (x.regs beta)
        (x.regs beta') (x.regs digit) (x.regs mode) rs).length ∧
      Modifies (Block.mk (x.regs dst) rs.length).footprint x.mem y.mem ∧
      (∀ j, Scan.body.Preserves j → y.regs j = x.regs j) :=
  Scan.exec rs x h.length h.constants.1 h.constants.2.1 h.constants.2.2.1
    h.constants.2.2.2.1 h.constants.2.2.2.2.1 h.constants.2.2.2.2.2
    h.keys h.counts h.words h.absolute h.double h.labels h.small h.keyAddress
    h.countAddress h.outputAddress h.keysBefore h.countsBefore

private theorem exec_mode {w m : ℕ} (r : Fin 48) (x : Data 48) (rs : List (ℕ × ℕ))
    (h : ScanReady w rs x) (hr : x.regs r = m) :
    ∃ y, ExecWithin w (.seq (ram[ mode ← r ]) Scan.program) x y (43 * rs.length + 5) ∧
      Block.HoldsList (x.regs dst) (Math.select (x.regs magnitude) (x.regs beta)
        (x.regs beta') (x.regs digit) m rs) y.mem ∧
      y.regs out = (Math.select (x.regs magnitude) (x.regs beta)
        (x.regs beta') (x.regs digit) m rs).length ∧
      Modifies (Block.mk (x.regs dst) rs.length).footprint x.mem y.mem := by
  let a := x.set mode m
  have ha : ExecWithin (B := .standard) w (ram[ mode ← r ]) x a 1 := by
    ram_eval [a, hr]
  have har : ScanParametersPreserved x a := by
    refine ⟨rfl, ?_⟩
    intro j _ _ _ _ hj
    exact Function.update_of_ne hj _ _
  obtain ⟨y, hy, hmem, hout, hframe, _⟩ := (h.transfer har).exec
  refine ⟨y, (ha.seq hy).mono (by omega), ?_, ?_, hframe⟩
  · simpa +decide [a] using hmem
  · simpa +decide [a] using hout

private theorem exec_singleton {w : ℕ} (x : Data 48) (rs : List (ℕ × ℕ))
    (h : ScanReady w rs x) :
    ∃ y, ExecWithin w singleton x y 2 ∧
      Block.HoldsList (x.regs dst) [0] y.mem ∧ y.regs out = 1 ∧
      Modifies (Block.mk (x.regs dst) (rs.length + 1)).footprint x.mem y.mem := by
  have f1 : Fits w 1 := h.small.of_le (by decide)
  have fd : Fits w (x.regs dst) := h.outputAddress.of_le (by omega)
  refine ⟨?_, ?run, ?_, ?_, ?_⟩
  case run => ram_eval [singleton, h.constants.1, h.constants.2.1, f1, fd]
  · intro i
    simp [Block.read, Data.set_mem, Data.write_mem]
  · simp
  · intro a ha
    have hne : a ≠ x.regs dst := by
      intro he
      apply ha
      apply Block.mem_footprint.mpr
      change x.regs dst ≤ a ∧ a < x.regs dst + (rs.length + 1)
      omega
    simp only [Data.set_mem, Data.write_mem, Function.update_of_ne hne]

/-- Select exactly the array named by one physical slot. Every split/multiplicity setup is
executed; the width and label budget are scalar runtime values, independent of code size. -/
theorem pick_exec {w U Λ j : ℕ} (x : Data 48) (rs : List (ℕ × ℕ))
    (h : ScanReady w rs x) (hU : x.regs magnitude = U)
    (hΛ : x.regs digits = Λ) (hs : x.regs splits = 2 * Λ ^ 2)
    (ht : x.regs triple = j / 3) (hslot : x.regs slot = j % 3)
    (hjfit : Fits w j) :
    ∃ y, ExecWithin w pick x y (43 * rs.length + 20) ∧
      Block.HoldsList (x.regs dst) (Math.array U Λ rs j) y.mem ∧
      y.regs out = (Math.array U Λ rs j).length ∧
      Modifies (Block.mk (x.regs dst) (rs.length + 1)).footprint x.mem y.mem := by
  have hz := h.constants.1
  have h1 := h.constants.2.1
  have h2 := h.constants.2.2.1
  have h3 := h.constants.2.2.2.1
  have h4 := h.constants.2.2.2.2.1
  have h5 := h.constants.2.2.2.2.2
  have frame {mem : ℕ → ℕ}
      (hf : Modifies (Block.mk (x.regs dst) rs.length).footprint x.mem mem) :
      Modifies (Block.mk (x.regs dst) (rs.length + 1)).footprint x.mem mem := by
    intro a ha
    apply hf a
    intro hmem
    apply ha
    rw [Block.mem_footprint] at hmem ⊢
    dsimp only [Block.Owns] at hmem ⊢
    omega
  by_cases hsplit : j / 3 < 2 * Λ ^ 2
  · let a := ((((x.set beta (j / 3 / 2)).set beta' (j / 3 / 2 % Λ)).set
      beta (j / 3 / 2 / Λ)).set digit (j / 3 % 2)).set mode (j % 3)
    have f0 := hjfit.of_le (show j / 3 / 2 ≤ j by omega)
    have f1' := hjfit.of_le (show j / 3 / 2 % Λ ≤ j from
      (Nat.mod_le _ _).trans (by omega))
    have f2' := hjfit.of_le (show j / 3 / 2 / Λ ≤ j from
      (Nat.div_le_self _ _).trans (by omega))
    have f3' := h.small.of_le (show j / 3 % 2 ≤ 5 by omega)
    have f4' := h.small.of_le (show j % 3 ≤ 5 by omega)
    have ha : ExecWithin w splitSetup x a 5 := by
      ram_eval [splitSetup, a, h2, ht, hslot, hΛ, f0, f1', f2', f3', f4']
    have har : ScanParametersPreserved x a := by
      refine ⟨rfl, ?_⟩
      intro i _ hb hb' hv hm
      simp only [a, Data.set_regs, Function.update_of_ne hb, Function.update_of_ne hb',
        Function.update_of_ne hv, Function.update_of_ne hm]
    obtain ⟨y, hy, hm, ho, hf, _⟩ := (h.transfer har).exec
    have he : Math.array U Λ rs j = Math.select U (j / 3 / 2 / Λ)
        (j / 3 / 2 % Λ) (j / 3 % 2) (j % 3) rs := by
      have hn : j % 3 ≠ 6 := by omega
      simp [Math.array, Math.mode, Math.beta, Math.beta', Math.digit, hsplit, hn]
    refine ⟨y, ?_, ?_, ?_, frame hf⟩
    · exact ((ha.seq hy).branch_pos (by simpa only [Cond.holds_lt, ht, hs] using hsplit)).mono
        (by omega)
    · simpa +decide [a, hU, he] using hm
    · simpa +decide [a, hU, he] using ho
  · have hcond : ¬(Cond.lt triple splits).Holds x := by
      simpa only [Cond.holds_lt, ht, hs] using hsplit
    by_cases htwice : j / 3 = 2 * Λ ^ 2
    · by_cases hzero : j % 3 = 0
      · obtain ⟨y, hy, hm, ho, hf⟩ := exec_mode three x rs h h3
        have he : Math.array U Λ rs j = Math.select U (x.regs beta) (x.regs beta')
            (x.regs digit) 3 rs := by
          simp [Math.array, Math.mode, htwice, hzero, Math.select_extra]
        refine ⟨y, ?_, ?_, ?_, frame hf⟩
        · exact (((hy.branch_pos (by simpa only [Cond.holds_eq, hslot, hz] using hzero)).branch_pos
            (by simpa only [Cond.holds_eq, ht, hs] using htwice)).branch_neg hcond).mono (by omega)
        · simpa only [hU, he] using hm
        · simpa only [hU, he] using ho
      · by_cases hone : j % 3 = 1
        · obtain ⟨y, hy, hm, ho, hf⟩ := exec_singleton x rs h
          have he : Math.array U Λ rs j = [0] := by
            simp [Math.array, Math.mode, htwice, hone]
          refine ⟨y, ?_, by simpa only [he] using hm, by simpa only [he,
            List.length_singleton] using ho, hf⟩
          exact ((((hy.branch_pos (by simpa only [Cond.holds_eq, hslot, h1] using hone)).branch_neg
            (by simpa only [Cond.holds_eq, hslot, hz] using hzero)).branch_pos
            (by simpa only [Cond.holds_eq, ht, hs] using htwice)).branch_neg hcond).mono (by omega)
        · obtain ⟨y, hy, hm, ho, hf⟩ := exec_mode five x rs h h5
          have he : Math.array U Λ rs j = Math.select U (x.regs beta) (x.regs beta')
              (x.regs digit) 5 rs := by
            simp [Math.array, Math.mode, htwice, hzero, hone, Math.select_extra]
          refine ⟨y, ?_, ?_, ?_, frame hf⟩
          · exact ((((hy.branch_neg (by simpa only [Cond.holds_eq, hslot,
            h1] using hone)).branch_neg
              (by simpa only [Cond.holds_eq, hslot, hz] using hzero)).branch_pos
              (by simpa only [Cond.holds_eq, ht,
                hs] using htwice)).branch_neg hcond).mono (by omega)
          · simpa only [hU, he] using hm
          · simpa only [hU, he] using ho
    · by_cases hzero : j % 3 = 0
      · obtain ⟨y, hy, hm, ho, hf⟩ := exec_mode four x rs h h4
        have he : Math.array U Λ rs j = Math.select U (x.regs beta) (x.regs beta')
            (x.regs digit) 4 rs := by
          simp [Math.array, Math.mode, hsplit, htwice, hzero, Math.select_extra]
        refine ⟨y, ?_, ?_, ?_, frame hf⟩
        · exact (((hy.branch_pos (by simpa only [Cond.holds_eq, hslot, hz] using hzero)).branch_neg
            (by simpa only [Cond.holds_eq, ht, hs] using htwice)).branch_neg hcond).mono (by omega)
        · simpa only [hU, he] using hm
        · simpa only [hU, he] using ho
      · obtain ⟨y, hy, hm, ho, hf⟩ := exec_singleton x rs h
        have he : Math.array U Λ rs j = [0] := by
          simp [Math.array, Math.mode, hsplit, htwice, hzero]
        refine ⟨y, ?_, by simpa only [he] using hm, by simpa only [he,
          List.length_singleton] using ho, hf⟩
        exact (((hy.branch_neg (by simpa only [Cond.holds_eq, hslot, hz] using hzero)).branch_neg
          (by simpa only [Cond.holds_eq, ht, hs] using htwice)).branch_neg hcond).mono (by omega)

private theorem write_exec {w : ℕ} (x : Data 48) (h1 : x.regs one = 1)
    (ha : Fits w (x.regs descriptors + 2 * x.regs current + 2))
    (hh : Fits w (x.regs heap + x.regs capacity))
    (hi : Fits w (x.regs current + 1)) :
    ∃ y, ExecWithin w writeDescriptor x y 7 ∧
      y.regs current = x.regs current + 1 ∧
      y.regs heap = x.regs heap + x.regs capacity ∧
      y.mem = Function.update (Function.update x.mem
        (x.regs descriptors + 2 * x.regs current) (x.regs out))
        (x.regs descriptors + 2 * x.regs current + 1) (x.regs dst) := by
  have f0 := ha.of_le (show x.regs current + x.regs current ≤
    x.regs descriptors + 2 * x.regs current + 2 by omega)
  have f1 := ha.of_le (show x.regs current + x.regs current + x.regs descriptors ≤
    x.regs descriptors + 2 * x.regs current + 2 by omega)
  have f2 := ha.of_le (show x.regs current + x.regs current + x.regs descriptors + 1 ≤
    x.regs descriptors + 2 * x.regs current + 2 by omega)
  refine ⟨?_, ?run, ?_, ?_, ?_⟩
  case run => ram_eval [writeDescriptor, h1, f0, f1, f2, hh, hi]
  all_goals simp +decide [Data.set_regs, Data.set_mem, Data.write_mem,
    show x.regs current + x.regs current + x.regs descriptors =
      x.regs descriptors + 2 * x.regs current by omega]

/-- One complete array, its exact descriptor words, allocation advance and local frame. -/
theorem body_exec {w U Λ j : ℕ} (x : Data 48) (rs : List (ℕ × ℕ))
    (hready : ScanReady w rs (x.set dst (x.regs heap)))
    (hU : x.regs magnitude = U) (hΛ : x.regs digits = Λ)
    (hs : x.regs splits = 2 * Λ ^ 2) (hj : x.regs current = j)
    (hcap : rs.length + 1 ≤ x.regs capacity)
    (hbefore : x.regs descriptors + 2 * j + 2 ≤ x.regs heap)
    (ha : Fits w (x.regs descriptors + 2 * j + 2))
    (hh : Fits w (x.regs heap + x.regs capacity)) (hi : Fits w (j + 1)) :
    ∃ y, ExecWithin w body x y (43 * rs.length + 30) ∧
      y.regs current = j + 1 ∧ y.regs heap = x.regs heap + x.regs capacity ∧
      y.mem (x.regs descriptors + 2 * j) = (Math.array U Λ rs j).length ∧
      y.mem (x.regs descriptors + 2 * j + 1) = x.regs heap ∧
      Block.HoldsList (x.regs heap) (Math.array U Λ rs j) y.mem ∧
      (∀ a, (a < x.regs heap ∨ x.regs heap + x.regs capacity ≤ a) →
        a ≠ x.regs descriptors + 2 * j → a ≠ x.regs descriptors + 2 * j + 1 →
        y.mem a = x.mem a) := by
  have h3 : x.regs three = 3 := by
    simpa +decide using hready.constants.2.2.2.1
  have h1 : x.regs one = 1 := by simpa +decide using hready.constants.2.1
  let a := ((x.set triple (j / 3)).set slot (j % 3)).set dst (x.regs heap)
  have f0 := hi.of_le (show j / 3 ≤ j + 1 by omega)
  have f1 := hi.of_le (show j % 3 ≤ j + 1 from (Nat.mod_le _ _).trans (by omega))
  have he : ExecWithin w
      (ram[ triple ← current / three; slot ← current % three; dst ← heap ]) x a 3 := by
    ram_eval [a, h3, hj, f0, f1]
  have hr : ScanReady w rs a := by
    apply hready.transfer
    refine ⟨rfl, ?_⟩
    intro i hil _ _ _ _
    have hit : i ≠ triple := by intro h; subst i; norm_num [triple] at hil
    have his : i ≠ slot := by intro h; subst i; norm_num [slot] at hil
    simp only [a, Data.set_regs, Function.update_apply]
    by_cases hid : i = dst
    · subst i; simp +decide
    · simp only [hid, hit, his, ↓reduceIte]
  obtain ⟨u, hu, hmem, hout, hf⟩ := pick_exec (j := j) a rs hr
    (by simpa +decide [a] using hU) (by simpa +decide [a] using hΛ)
    (by simpa +decide [a] using hs) (by simp +decide [a]) (by simp +decide [a])
    (hi.of_le (by omega))
  have hreg (i : Fin 48) (hp : pick.Preserves i)
      (ht : i ≠ triple) (hs : i ≠ slot) (hd : i ≠ dst) : u.regs i = x.regs i := by
    simpa only [a, Data.set_regs, Function.update_of_ne ht, Function.update_of_ne hs,
      Function.update_of_ne hd] using hu.regs_eq hp
  have huc : u.regs current = j := (hreg current (by decide) (by decide) (by decide)
    (by decide)).trans hj
  have huh : u.regs heap = x.regs heap := hreg heap (by decide) (by decide) (by decide) (by decide)
  have hucap := hreg capacity (by decide) (by decide) (by decide) (by decide)
  have hudesc := hreg descriptors (by decide) (by decide) (by decide) (by decide)
  have hu1 : u.regs one = 1 := (hreg one (by decide) (by decide) (by decide) (by decide)).trans h1
  have hud : u.regs dst = x.regs heap := by
    simpa +decide [a] using hu.regs_eq (i := dst) (by decide)
  have hum : Block.HoldsList (x.regs heap) (Math.array U Λ rs j) u.mem := by
    simpa +decide [a] using hmem
  obtain ⟨y, hy, hyc, hyh, hym⟩ := write_exec u hu1
    (by simpa only [huc, hudesc] using ha) (by simpa only [huh, hucap] using hh)
    (by simpa only [huc] using hi)
  rw [huc, hudesc, hout, hud] at hym
  refine ⟨y, (he.seq (hu.seq hy)).mono (by omega), by simpa only [huc] using hyc,
    by simpa only [huh, hucap] using hyh, ?_, ?_, ?_, ?_⟩
  · rw [hym, Function.update_of_ne (by omega), Function.update_self]
  · rw [hym, Function.update_self]
  · apply hum.frame
    intro b hlo hhi
    rw [hym, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · intro b hb hb0 hb1
    rw [hym, Function.update_of_ne hb1, Function.update_of_ne hb0]
    apply hf b
    rw [Block.mem_footprint]
    change ¬(a.regs dst ≤ b ∧ b < a.regs dst + (rs.length + 1))
    have had : a.regs dst = x.regs heap := by simp [a]
    rw [had]
    omega

end Cslib.Algorithms.WordRAM.ThreeSum.Frontend.Arrays
