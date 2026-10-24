/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Model
public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Program
public import Complexity.Algorithms.Lean.VanEmdeBoas.Insert

/-!
# Native van Emde Boas insertion descent

Insertion updates local extrema in place and recurses at most once per level: either into the
summary when the target cluster was empty (after installing the cluster's singleton extrema
directly), or into the already-occupied target cluster. Repeated insertion of a local minimum
terminates immediately.

## Main definitions

* `InsertEntry`: the insertion-loop register invariant.
* `insertNext`: a mathematical description of one native insertion iteration.

## Main results

* `insertBody_exec`: an actual insertion iteration takes at most 37 instructions.
* `insertLoop_spec`: insertion takes at most `39 * (d + 1) + 2` loop instructions,
  produces a valid memory representation of `tree.insert key`, and preserves all memory outside
  `[base, base + span d)`.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.VanEmdeBoas

open Cslib.WordRAM
open Cslib.Algorithms.Lean.VanEmdeBoas

/-- The constant and traversal registers at entry to an unfinished insertion. -/
structure InsertEntry (base key : ℕ) (s : Data 32) : Prop where
  zero_eq : s.regs zero = 0
  one_eq : s.regs one = 1
  two_eq : s.regs two = 2
  three_eq : s.regs three = 3
  four_eq : s.regs four = 4
  five_eq : s.regs five = 5
  p_eq : s.regs p = base
  x_eq : s.regs x = key
  runFlag_eq : s.regs runFlag = 1

/-- Mathematical description of one native insertion iteration. -/
def insertNext (s : Data 32) (base key : ℕ) : Data 32 :=
  let a := s.set present (s.mem base)
  if s.mem base = 0 then
    let a₁ := a.write base 1
    let a₂ := (a₁.set addr (base + 1)).write (base + 1) key
    let a₃ := (a₂.set addr (base + 2)).write (base + 2) key
    a₃.set runFlag 0
  else
    let b := (a.set addr (base + 1)).set mn (s.mem (base + 1))
    if key = s.mem (base + 1) then b.set runFlag 0 else
      let displaced := if key < s.mem (base + 1) then s.mem (base + 1) else key
      let b₁ := if key < s.mem (base + 1) then
        ((b.set addr (base + 1)).write (base + 1) key).set x (s.mem (base + 1))
      else b.set x key
      let c := (b₁.set addr (base + 2)).set mx (s.mem (base + 2))
      let c₁ := if s.mem (base + 2) < displaced then
        (c.set addr (base + 2)).write (base + 2) displaced
      else c.set mx (s.mem (base + 2))
      let e := (c₁.set addr (base + 3)).set q (s.mem (base + 3))
      if s.mem (base + 3) = 0 then e.set runFlag 0 else
        let f := (e.set addr (base + 4)).set t (s.mem (base + 4))
        let hi := displaced / s.mem (base + 3)
        let lo := displaced % s.mem (base + 3)
        let g := (((f.set high hi).set low lo).set tmp (hi + 1)).set tmp
          ((hi + 1) * s.mem (base + 4))
        let ch := base + 5 + (hi + 1) * s.mem (base + 4)
        let h := ((g.set child (base + 5)).set child ch).set present (s.mem ch)
        if s.mem ch = 0 then
          let h₁ := h.write ch 1
          let h₂ := (h₁.set addr (ch + 1)).write (ch + 1) lo
          let h₃ := (h₂.set addr (ch + 2)).write (ch + 2) lo
          (h₃.set p (base + 5)).set x hi
        else (h.set p ch).set x lo

/-- Constant registers are preserved by an insertion iteration. -/
private theorem insertNext_constants {base key : ℕ} {s : Data 32}
    (hs : InsertEntry base key s) :
    (insertNext s base key).regs zero = 0 ∧
    (insertNext s base key).regs one = 1 ∧
    (insertNext s base key).regs two = 2 ∧
    (insertNext s base key).regs three = 3 ∧
    (insertNext s base key).regs four = 4 ∧
    (insertNext s base key).regs five = 5 := by
  obtain ⟨hz, ho, ht, hthree, hfour, hfive, _⟩ := hs
  simp only [insertNext]
  split_ifs <;> simp +decide [hz, ho, ht, hthree, hfour, hfive]

/-- Updating `base + 1` and `base + 2` in place on a valid occupied header agrees with
`writeBounds` at every memory cell. -/
private theorem writeBounds_update_min_max {mem : ℕ → ℕ} {base m M key : ℕ}
    (hpres : mem base = 1) (hm : mem (base + 1) = m) (hM : mem (base + 2) = M)
    (hle : m ≤ M) :
    (let m₁ := if key < m then Function.update mem (base + 1) key else mem
     let displaced := if key < m then m else key
     if M < displaced then Function.update m₁ (base + 2) displaced else m₁) =
      writeBounds mem base (some (min m key, max M key)) := by
  funext a
  simp only [writeBounds, Function.update_apply, ite_apply]
  rcases eq_or_ne a base with rfl | h0
  · split_ifs <;> omega
  rcases eq_or_ne a (base + 1) with rfl | h1
  · split_ifs <;> omega
  rcases eq_or_ne a (base + 2) with rfl | h2
  · split_ifs <;> omega
  split_ifs <;> omega

/-- An occupied node's displaced key `max m key` has valid cluster coordinates and lies in the
parent record interval whenever `key < universeSize (d + 1)`. -/
private theorem insert_descent_safe {d base m M key : ℕ} {s : Tree d}
    {c : Fin (universeSize d) → Tree d}
    (ht : (Tree.node (some (m, M)) s c).Valid) (hkey : key < universeSize (d + 1)) :
    let displaced := max m key
    displaced / universeSize d < universeSize d ∧
      displaced % universeSize d < universeSize d ∧
      base + clusterOffset d (displaced / universeSize d) + span d ≤ base + span (d + 1) := by
  have hm_lt : m < universeSize (d + 1) := ht.contains_lt (ht.contains_minimum rfl)
  have hdisp : max m key < universeSize d * universeSize d := by
    simpa only [universeSize_succ] using max_lt hm_lt hkey
  have hi : max m key / universeSize d < universeSize d :=
    (Nat.div_lt_iff_lt_mul (universeSize_pos d)).mpr hdisp
  refine ⟨hi, Nat.mod_lt _ (universeSize_pos d), ?_⟩
  simpa only [Nat.add_assoc] using Nat.add_le_add_left (cluster_end_le_span d hi) base

/-- One actual insertion iteration, including all branches and address calculations, executes
within 37 instructions. -/
theorem insertBody_exec {d w base key : ℕ} {tree : Tree d} {s : Data 32}
    (hs : InsertEntry base key s) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hkey : key < universeSize d) (ha : Fits w (base + span d)) :
    ExecWithin w insertBody s (insertNext s base key) 37 := by
  obtain ⟨hz, ho, htwo, hthree, hfour, hfive, hp, hx, _⟩ := hs
  have h₁ : Fits w (base + 1) := ha.of_le (by have := five_le_span d; omega)
  have h₂ : Fits w (base + 2) := ha.of_le (by have := five_le_span d; omega)
  have h₃ : Fits w (base + 3) := ha.of_le (by have := five_le_span d; omega)
  have h₄ : Fits w (base + 4) := ha.of_le (by have := five_le_span d; omega)
  have hheader := hr.header
  cases tree with
  | leaf b =>
    cases b with
    | none =>
      have he : s.mem base = 0 := hheader.1
      ram_eval [insertBody, insertNext, writeAt, hp, hx, hz, ho, htwo, he, h₁, h₂]
    | some bounds =>
      obtain ⟨m, M⟩ := bounds
      obtain ⟨he, ⟨hm, hM⟩, hq, _⟩ := hheader
      by_cases heq : key = m
      · ram_eval [insertBody, insertNext, readAt, hp, hx, hz, ho, he, hm, heq, h₁]
      · by_cases hlt : key < m
        · by_cases hmx : M < m
          · ram_eval [insertBody, insertNext, readAt, writeAt, hp, hx, hz, ho, htwo, hthree,
              he, hm, hM, hq, splitSize, heq, hlt, hmx, h₁, h₂, h₃, Nat.add_left_cancel_iff]
          · ram_eval [insertBody, insertNext, readAt, writeAt, hp, hx, hz, ho, htwo, hthree,
              he, hm, hM, hq, splitSize, heq, hlt, hmx, h₁, h₂, h₃, Nat.add_left_cancel_iff]
        · by_cases hmx : M < key
          · ram_eval [insertBody, insertNext, readAt, writeAt, hp, hx, hz, ho, htwo, hthree,
              he, hm, hM, hq, splitSize, heq, hlt, hmx, h₁, h₂, h₃, Nat.add_left_cancel_iff]
          · ram_eval [insertBody, insertNext, readAt, writeAt, hp, hx, hz, ho, htwo, hthree,
              he, hm, hM, hq, splitSize, heq, hlt, hmx, h₁, h₂, h₃, Nat.add_left_cancel_iff]
  | @node d b summary cluster =>
    cases b with
    | none =>
      have he : s.mem base = 0 := hheader.1
      ram_eval [insertBody, insertNext, writeAt, hp, hx, hz, ho, htwo, he, h₁, h₂]
    | some bounds =>
      obtain ⟨m, M⟩ := bounds
      obtain ⟨he, ⟨hm, hM⟩, hq, hspan⟩ := hheader
      by_cases heq : key = m
      · ram_eval [insertBody, insertNext, readAt, hp, hx, hz, ho, he, hm, heq, h₁]
      · have hsafe := insert_descent_safe (base := base) ht hkey
        have hqne : universeSize d ≠ 0 := Nat.ne_of_gt (universeSize_pos d)
        have hbase : Fits w (base + 5) := ha.of_le (by have := five_le_span (d + 1); omega)
        by_cases hlt : key < m
        · have hd_eq : max m key = m := max_eq_left (Nat.le_of_lt hlt)
          have hi : m / universeSize d < universeSize d := by simpa only [hd_eq] using hsafe.1
          have hlo_lt : m % universeSize d < universeSize d := by simpa only [hd_eq] using hsafe.2.1
          have hend : base + clusterOffset d (m / universeSize d) + span d ≤
              base + span (d + 1) := by simpa only [hd_eq] using hsafe.2.2
          have hu := universeSize_le_span d
          have hu' := span_le_succ d
          have hhi : Fits w (m / universeSize d) := ha.of_le (by omega)
          have hlo : Fits w (m % universeSize d) := ha.of_le (by omega)
          have hnext : Fits w (m / universeSize d + 1) := ha.of_le (by omega)
          have hprod : Fits w ((m / universeSize d + 1) * span d) := by
            apply ha.of_le; dsimp only [clusterOffset] at hend; omega
          have hchild : Fits w (base + 5 + (m / universeSize d + 1) * span d) := by
            apply ha.of_le; dsimp only [clusterOffset] at hend; omega
          have hch1 : Fits w (base + 5 + (m / universeSize d + 1) * span d + 1) := by
            apply ha.of_le; have := five_le_span d; dsimp only [clusterOffset] at hend; omega
          have hch2 : Fits w (base + 5 + (m / universeSize d + 1) * span d + 2) := by
            apply ha.of_le; have := five_le_span d; dsimp only [clusterOffset] at hend; omega
          let ch := base + 5 + (m / universeSize d + 1) * span d
          have hch_ne1 : ch ≠ base + 1 := by dsimp only [ch]; omega
          have hch_ne2 : ch ≠ base + 2 := by dsimp only [ch]; omega
          by_cases hmx : M < m <;> by_cases hch0 : s.mem ch = 0
          · ram_eval [insertBody, insertNext, readAt, writeAt, coordinates, hp, hx, hz, ho,
              htwo, hthree, hfour, hfive, he, hm, hM, hq, hspan, splitSize, childSpan,
              heq, hlt, hmx, hqne, hch0, hch_ne1, hch_ne2, ch, h₁, h₂, h₃, h₄, hhi, hlo,
              hnext, hprod, hbase, hchild, hch1, hch2, Nat.add_left_cancel_iff]
          · ram_eval [insertBody, insertNext, readAt, writeAt, coordinates, hp, hx, hz, ho,
              htwo, hthree, hfour, hfive, he, hm, hM, hq, hspan, splitSize, childSpan,
              heq, hlt, hmx, hqne, hch0, hch_ne1, hch_ne2, ch, h₁, h₂, h₃, h₄, hhi, hlo,
              hnext, hprod, hbase, hchild, Nat.add_left_cancel_iff]
          · ram_eval [insertBody, insertNext, readAt, writeAt, coordinates, hp, hx, hz, ho,
              htwo, hthree, hfour, hfive, he, hm, hM, hq, hspan, splitSize, childSpan,
              heq, hlt, hmx, hqne, hch0, hch_ne1, hch_ne2, ch, h₁, h₂, h₃, h₄, hhi, hlo,
              hnext, hprod, hbase, hchild, hch1, hch2, Nat.add_left_cancel_iff]
          · ram_eval [insertBody, insertNext, readAt, writeAt, coordinates, hp, hx, hz, ho,
              htwo, hthree, hfour, hfive, he, hm, hM, hq, hspan, splitSize, childSpan,
              heq, hlt, hmx, hqne, hch0, hch_ne1, hch_ne2, ch, h₁, h₂, h₃, h₄, hhi, hlo,
              hnext, hprod, hbase, hchild, Nat.add_left_cancel_iff]
        · have hd_eq : max m key = key := max_eq_right (Nat.le_of_not_lt hlt)
          have hi : key / universeSize d < universeSize d := by simpa only [hd_eq] using hsafe.1
          have hlo_lt : key % universeSize d < universeSize d := by
            simpa only [hd_eq] using hsafe.2.1
          have hend : base + clusterOffset d (key / universeSize d) + span d ≤
              base + span (d + 1) := by simpa only [hd_eq] using hsafe.2.2
          have hu := universeSize_le_span d
          have hu' := span_le_succ d
          have hhi : Fits w (key / universeSize d) := ha.of_le (by omega)
          have hlo : Fits w (key % universeSize d) := ha.of_le (by omega)
          have hnext : Fits w (key / universeSize d + 1) := ha.of_le (by omega)
          have hprod : Fits w ((key / universeSize d + 1) * span d) := by
            apply ha.of_le; dsimp only [clusterOffset] at hend; omega
          have hchild : Fits w (base + 5 + (key / universeSize d + 1) * span d) := by
            apply ha.of_le; dsimp only [clusterOffset] at hend; omega
          have hch1 : Fits w (base + 5 + (key / universeSize d + 1) * span d + 1) := by
            apply ha.of_le; have := five_le_span d; dsimp only [clusterOffset] at hend; omega
          have hch2 : Fits w (base + 5 + (key / universeSize d + 1) * span d + 2) := by
            apply ha.of_le; have := five_le_span d; dsimp only [clusterOffset] at hend; omega
          let ch := base + 5 + (key / universeSize d + 1) * span d
          have hch_ne1 : ch ≠ base + 1 := by dsimp only [ch]; omega
          have hch_ne2 : ch ≠ base + 2 := by dsimp only [ch]; omega
          by_cases hmx : M < key <;> by_cases hch0 : s.mem ch = 0
          · ram_eval [insertBody, insertNext, readAt, writeAt, coordinates, hp, hx, hz, ho,
              htwo, hthree, hfour, hfive, he, hm, hM, hq, hspan, splitSize, childSpan,
              heq, hlt, hmx, hqne, hch0, hch_ne1, hch_ne2, ch, h₁, h₂, h₃, h₄, hhi, hlo,
              hnext, hprod, hbase, hchild, hch1, hch2, Nat.add_left_cancel_iff]
          · ram_eval [insertBody, insertNext, readAt, writeAt, coordinates, hp, hx, hz, ho,
              htwo, hthree, hfour, hfive, he, hm, hM, hq, hspan, splitSize, childSpan,
              heq, hlt, hmx, hqne, hch0, hch_ne1, hch_ne2, ch, h₁, h₂, h₃, h₄, hhi, hlo,
              hnext, hprod, hbase, hchild, Nat.add_left_cancel_iff]
          · ram_eval [insertBody, insertNext, readAt, writeAt, coordinates, hp, hx, hz, ho,
              htwo, hthree, hfour, hfive, he, hm, hM, hq, hspan, splitSize, childSpan,
              heq, hlt, hmx, hqne, hch0, hch_ne1, hch_ne2, ch, h₁, h₂, h₃, h₄, hhi, hlo,
              hnext, hprod, hbase, hchild, hch1, hch2, Nat.add_left_cancel_iff]
          · ram_eval [insertBody, insertNext, readAt, writeAt, coordinates, hp, hx, hz, ho,
              htwo, hthree, hfour, hfive, he, hm, hM, hq, hspan, splitSize, childSpan,
              heq, hlt, hmx, hqne, hch0, hch_ne1, hch_ne2, ch, h₁, h₂, h₃, h₄, hhi, hlo,
              hnext, hprod, hbase, hchild, Nat.add_left_cancel_iff]

private theorem insertLoop_finish {d w base key : ℕ} {tree' : Tree d} {s : Data 32}
    (hs : InsertEntry base key s)
    (he : ExecWithin w insertBody s (insertNext s base key) 37)
    (hk : (insertNext s base key).regs runFlag = 0)
    (hrep : Rep tree' base (insertNext s base key).mem)
    (hframe : ∀ a, a < base ∨ base + span d ≤ a → (insertNext s base key).mem a = s.mem a) :
    ∃ z, ExecWithin w insertLoop s z 41 ∧ Rep tree' base z.mem ∧
      (∀ a, a < base ∨ base + span d ≤ a → z.mem a = s.mem a) := by
  have hz := (insertNext_constants hs).1
  refine ⟨_, he.loop_once (cond := .lt zero runFlag) ?_ ?_, hrep, hframe⟩
  · simp only [Cond.holds_lt, hs.zero_eq, hs.runFlag_eq]
    decide
  · simp only [Cond.holds_lt, hz, hk, lt_self_iff_false, not_false_eq_true]

/-- The insertion loop is correct for every depth and arbitrary surrounding memory.
It executes within `39 * (d + 1) + 2` instructions, establishes `Rep (tree.insert key) base z.mem`,
and leaves all memory outside `[base, base + span d)` unchanged. -/
theorem insertLoop_spec {d w base key : ℕ} {tree : Tree d} {s : Data 32}
    (hs : InsertEntry base key s) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hkey : key < universeSize d) (ha : Fits w (base + span d)) :
    ∃ z, ExecWithin w insertLoop s z (39 * (d + 1) + 2) ∧
      Rep (tree.insert key) base z.mem ∧
      (∀ a, a < base ∨ base + span d ≤ a → z.mem a = s.mem a) := by
  induction d generalizing base key s with
  | zero =>
    have he := insertBody_exec hs ht hr hkey ha
    cases tree with
    | leaf b =>
      cases b with
      | none =>
        have hempty : s.mem base = 0 := hr.1
        have hmem_eq : (insertNext s base key).mem = writeBounds s.mem base (some (key, key)) := by
          simp [insertNext, hempty, writeBounds, Data.write_mem, Data.set_mem]
        apply insertLoop_finish hs he
        · simp +decide [insertNext, hempty]
        · rw [hmem_eq]
          simpa only [Tree.insert, Tree.withBounds] using rep_writeBounds hr (some (key, key))
        · intro a ha'
          rw [hmem_eq]
          exact writeBounds_away (some (key, key)) (by simp only [span_zero] at ha'; omega)
      | some bounds =>
        obtain ⟨m, M⟩ := bounds
        have ⟨hpres, ⟨hm, hM⟩, hq, _⟩ := hr
        have hle : m ≤ M := by
          have hext := ht.extrema
          simp only [Tree.Extrema, Tree.bounds] at hext
          exact hext.1
        by_cases heq : key = m
        · apply insertLoop_finish hs he
          · simp +decide [insertNext, hpres, hm, heq]
          · have hmem_eq : (insertNext s base key).mem = s.mem := by
              simp [insertNext, hpres, hm, heq]
            rw [hmem_eq]
            have hins : (Tree.leaf (some (m, M))).insert key = Tree.leaf (some (m, M)) := by
              simp only [Tree.insert, heq, min_self, max_eq_left hle]
            rw [hins]
            exact hr
          · intro a _
            simp [insertNext, hpres, hm, heq]
        · have hmem_eq : (insertNext s base key).mem =
              writeBounds s.mem base (some (min m key, max M key)) := by
            rw [← writeBounds_update_min_max hpres hm hM hle]
            simp only [insertNext, hpres, hm, hM, hq, splitSize, Option.isSome_some,
              ↓reduceIte, one_ne_zero, heq]
            split_ifs <;> rfl
          apply insertLoop_finish hs he
          · simp only [insertNext, hpres, hm, hM, hq, splitSize, Option.isSome_some,
              ↓reduceIte, one_ne_zero, heq]
            split_ifs <;> simp +decide
          · rw [hmem_eq]
            simpa only [Tree.insert, Tree.withBounds] using
              rep_writeBounds hr (some (min m key, max M key))
          · intro a ha'
            rw [hmem_eq]
            exact writeBounds_away (some (min m key, max M key))
              (by simp only [span_zero] at ha'; omega)
  | succ d ih =>
    have he := insertBody_exec hs ht hr hkey ha
    have finish (hk : (insertNext s base key).regs runFlag = 0)
        (hrep : Rep (tree.insert key) base (insertNext s base key).mem)
        (hframe : ∀ a, a < base ∨ base + span (d + 1) ≤ a →
          (insertNext s base key).mem a = s.mem a) :
        ∃ z, ExecWithin w insertLoop s z (39 * (d + 1 + 1) + 2) ∧
          Rep (tree.insert key) base z.mem ∧
          (∀ a, a < base ∨ base + span (d + 1) ≤ a → z.mem a = s.mem a) := by
      obtain ⟨z, hz, hr', hf'⟩ := insertLoop_finish hs he hk hrep hframe
      exact ⟨z, hz.mono (by omega), hr', hf'⟩
    cases tree with
    | node bounds summary cluster =>
      cases bounds with
      | none =>
        have hempty : s.mem base = 0 := hr.1.1
        have hmem_eq : (insertNext s base key).mem = writeBounds s.mem base (some (key, key)) := by
          simp [insertNext, hempty, writeBounds, Data.write_mem, Data.set_mem]
        apply finish
        · simp +decide [insertNext, hempty]
        · rw [hmem_eq]
          simpa only [Tree.insert, Tree.withBounds] using rep_writeBounds hr (some (key, key))
        · intro a ha'
          rw [hmem_eq]
          have := five_le_span (d + 1)
          exact writeBounds_away (some (key, key)) (by omega)
      | some bounds =>
        obtain ⟨m, M⟩ := bounds
        obtain ⟨hpres, ⟨hm, hM⟩, hq, hspan⟩ := hr.1
        have hle : m ≤ M := by
          have hext := ht.extrema
          simp only [Tree.Extrema, Tree.bounds] at hext
          exact hext.1
        by_cases heq : key = m
        · apply finish
          · simp +decide [insertNext, hpres, hm, heq]
          · have hmem_eq : (insertNext s base key).mem = s.mem := by
              simp [insertNext, hpres, hm, heq]
            rw [hmem_eq]
            simp only [Tree.insert, heq, ↓reduceIte]
            exact hr
          · intro a _
            simp [insertNext, hpres, hm, heq]
        · have hsafe := insert_descent_safe (base := base) ht hkey
          have hi : max m key / universeSize d < universeSize d := hsafe.1
          have hlo_lt : max m key % universeSize d < universeSize d := hsafe.2.1
          have hend : base + clusterOffset d (max m key / universeSize d) + span d ≤
              base + span (d + 1) := hsafe.2.2
          let i : Fin (universeSize d) := ⟨max m key / universeSize d, hi⟩
          let lo := max m key % universeSize d
          let ch := base + clusterOffset d i.val
          let m₁ := writeBounds s.mem base (some (min m key, max M key))
          have hr₁ : Rep (.node (some (min m key, max M key)) summary cluster) base m₁ :=
            rep_writeBounds hr (some (min m key, max M key))
          have hdisp_eq : (if key < m then m else key) = max m key := by
            rcases lt_or_ge key m with h | h
            · rw [ite_eq_left h, max_eq_left (Nat.le_of_lt h)]
            · rw [ite_eq_right (not_lt.mpr h), max_eq_right h]
          have hqne : universeSize d ≠ 0 := Nat.ne_of_gt (universeSize_pos d)
          let next := insertNext s base key
          cases hcb : (cluster i).bounds with
          | none =>
            have hch0 : s.mem ch = 0 := by
              have hh := (hr.2.2 i).header.1
              simpa only [ch, hcb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using hh
            have hch0' : s.mem (base + 5 + (max m key / universeSize d + 1) * span d) = 0 := by
              simpa only [ch, clusterOffset, i, Nat.add_assoc] using hch0
            have hnext_mem : next.mem = writeBounds m₁ ch (some (lo, lo)) := by
              dsimp only [next, m₁, ch, clusterOffset, i, lo]
              rw [← writeBounds_update_min_max hpres hm hM hle, ← Nat.add_assoc]
              simp only [insertNext, hpres, hm, hM, hq, hspan, splitSize, childSpan,
                Option.isSome_some, ↓reduceIte, one_ne_zero, heq, hqne, hdisp_eq, hch0',
                writeBounds]
              split_ifs <;> rfl
            have hentry : InsertEntry (base + summaryOffset) i.val next := by
              obtain ⟨hz, ho, ht', hthree, hfour, hfive⟩ := insertNext_constants hs
              refine ⟨hz, ho, ht', hthree, hfour, hfive, ?_, ?_, ?_⟩
              · simp +decide [next, insertNext, hpres, hm, hM, hq, hspan, splitSize, childSpan,
                  heq, hqne, hdisp_eq, hch0', summaryOffset]
              · simp +decide [next, insertNext, hpres, hm, hM, hq, hspan, splitSize, childSpan,
                  heq, hqne, hdisp_eq, hch0', i]
              · simp only [next, insertNext, hpres, hm, hM, hq, hspan, splitSize, childSpan,
                  Option.isSome_some, ↓reduceIte, one_ne_zero, heq, hqne, hdisp_eq, hch0']
                split_ifs <;> simp +decide [hs.runFlag_eq]
            have hrc_up : Rep ((cluster i).withBounds (some (lo, lo))) ch next.mem := by
              rw [hnext_mem]
              exact rep_writeBounds (hr₁.2.2 i) (some (lo, lo))
            have hr₂ : Rep (.node (some (min m key, max M key)) summary
                (Function.update cluster i ((cluster i).withBounds (some (lo, lo)))))
                base next.mem := by
              apply rep_replace_cluster hr₁ i hrc_up
              intro a ha'
              rw [hnext_mem]
              have := five_le_span d
              exact writeBounds_away (some (lo, lo)) (by dsimp only [ch]; omega)
            have hfit_sum : Fits w (base + summaryOffset + span d) :=
              ha.of_le (by have := summary_end_le_span d; omega)
            obtain ⟨z, hz, hrs_z, hframe_z⟩ := ih hentry ht.2.1 hr₂.2.1 i.isLt hfit_sum
            refine ⟨z, (he.loop_iter (cond := .lt zero runFlag) ?_ hz).mono (by omega), ?_, ?_⟩
            · simp only [Cond.holds_lt, hs.zero_eq, hs.runFlag_eq]
              decide
            · have hr_final := rep_replace_summary hr₂ hrs_z hframe_z
              dsimp only [i] at hcb
              simpa only [Tree.insert, heq, ↓reduceIte, hi, ↓reduceDIte, i, lo, hcb] using hr_final
            · intro a ha'
              have hsum_end := summary_end_le_span d
              have hf1 : z.mem a = next.mem a := by
                apply hframe_z a
                dsimp only [summaryOffset] at hsum_end ⊢
                omega
              have hf2 : next.mem a = m₁ a := by
                rw [hnext_mem]
                have := five_le_span d
                exact writeBounds_away (some (lo, lo)) (by dsimp only [ch, i] at hend ⊢; omega)
              have hf3 : m₁ a = s.mem a := by
                have := five_le_span (d + 1)
                exact writeBounds_away (some (min m key, max M key)) (by omega)
              exact hf1.trans (hf2.trans hf3)
          | some cbounds =>
            have hch1 : s.mem ch = 1 := by
              have hh := (hr.2.2 i).header.1
              simpa only [ch, hcb, Option.isSome_some, ↓reduceIte] using hh
            have hch_ne0 : s.mem ch ≠ 0 := by omega
            have hch_ne0' : s.mem (base + 5 + (max m key / universeSize d + 1) * span d) ≠ 0 := by
              simpa only [ch, clusterOffset, i, Nat.add_assoc] using hch_ne0
            have hnext_mem : next.mem = m₁ := by
              dsimp only [next, m₁]
              rw [← writeBounds_update_min_max hpres hm hM hle]
              simp only [insertNext, hpres, hm, hM, hq, hspan, splitSize, childSpan,
                Option.isSome_some, ↓reduceIte, one_ne_zero, heq, hqne, hdisp_eq, hch_ne0']
              split_ifs <;> rfl
            have hentry : InsertEntry ch lo next := by
              obtain ⟨hz, ho, ht', hthree, hfour, hfive⟩ := insertNext_constants hs
              refine ⟨hz, ho, ht', hthree, hfour, hfive, ?_, ?_, ?_⟩
              · dsimp only [ch, clusterOffset, i]
                rw [← Nat.add_assoc]
                simp +decide [next, insertNext, hpres, hm, hM, hq, hspan, splitSize, childSpan,
                  heq, hqne, hdisp_eq, hch_ne0']
              · simp +decide [next, insertNext, hpres, hm, hM, hq, hspan, splitSize, childSpan,
                  heq, hqne, hdisp_eq, hch_ne0', lo]
              · simp only [next, insertNext, hpres, hm, hM, hq, hspan, splitSize, childSpan,
                  Option.isSome_some, ↓reduceIte, one_ne_zero, heq, hqne, hdisp_eq, hch_ne0']
                split_ifs <;> simp +decide [hs.runFlag_eq]
            have hrc_next : Rep (cluster i) ch next.mem := by
              rw [hnext_mem]
              exact hr₁.2.2 i
            have hfit_cl : Fits w (ch + span d) := ha.of_le hend
            obtain ⟨z, hz, hrc_z, hframe_z⟩ := ih hentry (ht.2.2.1 i) hrc_next hlo_lt hfit_cl
            refine ⟨z, (he.loop_iter (cond := .lt zero runFlag) ?_ hz).mono (by omega), ?_, ?_⟩
            · simp only [Cond.holds_lt, hs.zero_eq, hs.runFlag_eq]
              decide
            · have hr_final : Rep (.node (some (min m key, max M key)) summary
                  (Function.update cluster i ((cluster i).insert lo))) base z.mem := by
                apply rep_replace_cluster hr₁ i hrc_z
                intro a ha'
                rw [← hnext_mem]
                exact hframe_z a ha'
              dsimp only [i] at hcb
              simpa only [Tree.insert, heq, ↓reduceIte, hi, ↓reduceDIte, i, lo, hcb] using hr_final
            · intro a ha'
              have hf1 : z.mem a = next.mem a := by
                apply hframe_z a
                have hstart : 5 ≤ clusterOffset d i.val := by dsimp only [clusterOffset]; omega
                dsimp only [ch, i] at hend ⊢
                omega
              have hf2 : next.mem a = s.mem a := by
                rw [hnext_mem]
                have := five_le_span (d + 1)
                exact writeBounds_away (some (min m key, max M key)) (by omega)
              exact hf1.trans hf2

end Cslib.Algorithms.WordRAM.VanEmdeBoas
