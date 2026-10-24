/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Model
public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Program

/-!
# Native van Emde Boas membership descent

The proof state records only the registers required by membership; all other registers and
all memory outside the represented tree may be arbitrary. Queries need not belong to the
tree universe. The maximum guard is checked before any cluster address is calculated.

## Main definitions

* `MemberEntry`: the membership-loop register invariant.
* `memberNext`: a mathematical description of one native iteration, not a machine instruction.

## Main results

* `memberBody_exec`: an actual iteration takes at most 26 instructions.
* `memberLoop_spec`: membership takes at most `28 * (d + 1) + 2` loop instructions,
  gives the functional answer and preserves all memory.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.VanEmdeBoas

open Cslib.WordRAM
open Cslib.Algorithms.Lean.VanEmdeBoas

/-- The constant, traversal and result registers at entry to an unfinished lookup. -/
structure MemberEntry (base query : ℕ) (s : Data 32) : Prop where
  zero_eq : s.regs zero = 0
  one_eq : s.regs one = 1
  two_eq : s.regs two = 2
  three_eq : s.regs three = 3
  four_eq : s.regs four = 4
  five_eq : s.regs five = 5
  p_eq : s.regs p = base
  x_eq : s.regs x = query
  out_eq : s.regs out = 0
  runFlag_eq : s.regs runFlag = 1

/-- A description of one native iteration. Each update corresponds to an instruction in
`memberBody`; the description itself is used only in proofs. -/
def memberNext (s : Data 32) (base query : ℕ) : Data 32 :=
  let a := s.set present (s.mem base)
  if s.mem base = 0 then a.set runFlag 0 else
    let b := (a.set addr (base + 1)).set mn (s.mem (base + 1))
    if query = s.mem (base + 1) then (b.set out 1).set runFlag 0 else
      let c := (b.set addr (base + 2)).set mx (s.mem (base + 2))
      if query = s.mem (base + 2) then (c.set out 1).set runFlag 0 else
        if query < s.mem (base + 2) then
          let e := (c.set addr (base + 3)).set q (s.mem (base + 3))
          if s.mem (base + 3) = 0 then e.set runFlag 0 else
            let f := (e.set addr (base + 4)).set t (s.mem (base + 4))
            let hi := query / s.mem (base + 3)
            let lo := query % s.mem (base + 3)
            let g := (((f.set high hi).set low lo).set tmp (hi + 1)).set tmp
              ((hi + 1) * s.mem (base + 4))
            (((g.set child (base + 5)).set child
              (base + 5 + (hi + 1) * s.mem (base + 4))).set p
              (base + 5 + (hi + 1) * s.mem (base + 4))).set x lo
        else c.set runFlag 0

/-- Membership performs no writes, including on unsuccessful or out-of-universe queries. -/
@[simp]
theorem memberNext_mem (s : Data 32) (base query : ℕ) :
    (memberNext s base query).mem = s.mem := by
  simp only [memberNext]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · split <;> rfl
        · rfl

/-- One real membership iteration, including all branches and address computations.
The sole address-fit assumption covers the represented record endpoint. -/
theorem memberBody_exec {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : MemberEntry base query s) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) :
    ExecWithin w memberBody s (memberNext s base query) 26 := by
  obtain ⟨hz, ho, htwo, hthree, hfour, hfive, hp, hx, _, _⟩ := hs
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
      ram_eval [memberBody, memberNext, hp, hx, hz, he]
    | some bounds =>
      obtain ⟨m, M⟩ := bounds
      obtain ⟨he, ⟨hm, hM⟩, hq, _⟩ := hheader
      by_cases heq : query = m
      · ram_eval [memberBody, memberNext, readAt, hp, hx, hz, ho, he, hm, heq, h₁]
      · by_cases heq' : query = M
        · have hneM : M ≠ m := by simpa only [heq'] using heq
          ram_eval [memberBody, memberNext, readAt, hp, hx, hz, ho, htwo, he, hm, hM,
            heq, heq', hneM, h₁, h₂]
        · by_cases hlt : query < M
          · ram_eval [memberBody, memberNext, readAt, hp, hx, hz, ho, htwo, hthree,
              he, hm, hM, hq, splitSize, heq, heq', hlt, h₁, h₂, h₃]
          · ram_eval [memberBody, memberNext, readAt, hp, hx, hz, ho, htwo,
              he, hm, hM, heq, heq', hlt, h₁, h₂]
  | @node d b summary cluster =>
    cases b with
    | none =>
      have he : s.mem base = 0 := hheader.1
      ram_eval [memberBody, memberNext, hp, hx, hz, he]
    | some bounds =>
      obtain ⟨m, M⟩ := bounds
      obtain ⟨he, ⟨hm, hM⟩, hq, hspan⟩ := hheader
      by_cases heq : query = m
      · ram_eval [memberBody, memberNext, readAt, hp, hx, hz, ho, he, hm, heq, h₁]
      · by_cases heq' : query = M
        · have hneM : M ≠ m := by simpa only [heq'] using heq
          ram_eval [memberBody, memberNext, readAt, hp, hx, hz, ho, htwo, he, hm, hM,
            heq, heq', hneM, h₁, h₂]
        · by_cases hlt : query < M
          · have hsafe := member_descent_safe ht hr (by simpa only [hM] using hlt)
            have hi := hsafe.1
            have hu := universeSize_le_span d
            have hu' := span_le_succ d
            have hhi : Fits w (query / universeSize d) := ha.of_le (by omega)
            have hlo : Fits w (query % universeSize d) := ha.of_le (by omega)
            have hnext : Fits w (query / universeSize d + 1) := ha.of_le (by omega)
            have hprod : Fits w ((query / universeSize d + 1) * span d) := by
              apply ha.of_le
              dsimp only [clusterOffset] at hsafe
              omega
            have hbase : Fits w (base + 5) := ha.of_le (by have := five_le_span (d+1); omega)
            have hchild : Fits w (base + 5 + (query / universeSize d + 1) * span d) := by
              apply ha.of_le
              dsimp only [clusterOffset] at hsafe
              omega
            have hqne : universeSize d ≠ 0 := Nat.ne_of_gt (universeSize_pos d)
            ram_eval [memberBody, memberNext, readAt, coordinates, hp, hx, hz, ho,
              htwo, hthree, hfour, hfive, he, hm, hM, hq, hspan, splitSize, childSpan,
              heq, heq', hlt, hqne, h₁, h₂, h₃, h₄, hhi, hlo, hnext, hprod, hbase, hchild]
          · ram_eval [memberBody, memberNext, readAt, hp, hx, hz, ho, htwo,
              he, hm, hM, heq, heq', hlt, h₁, h₂]

/-- Constant registers are preserved by a membership iteration. -/
private theorem memberNext_constants {base query : ℕ} {s : Data 32}
    (hs : MemberEntry base query s) :
    (memberNext s base query).regs zero = 0 ∧
    (memberNext s base query).regs one = 1 ∧
    (memberNext s base query).regs two = 2 ∧
    (memberNext s base query).regs three = 3 ∧
    (memberNext s base query).regs four = 4 ∧
    (memberNext s base query).regs five = 5 := by
  obtain ⟨hz, ho, ht, hthree, hfour, hfive, _⟩ := hs
  simp only [memberNext]
  split_ifs <;> simp +decide [hz, ho, ht, hthree, hfour, hfive]

/-- A query above the cached maximum is absent; this fact uses validity, not outside memory. -/
private theorem member_eq_false_of_max_lt {d m M query : ℕ} {tree : Tree d}
    (ht : tree.Valid) (hb : tree.bounds = some (m, M)) (hx : M < query) :
    tree.member query = false := by
  have hnot : ¬tree.Contains query := by
    intro hc
    have he := ht.extrema
    simp only [Tree.Extrema, hb] at he
    have := (he.2.2.2.2 query hc).2
    omega
  cases he : tree.member query
  · rfl
  · exact False.elim (hnot ((Tree.member_iff_contains ht query).mp he))

/-- The cached maximum is a valid early successful membership result. -/
private theorem member_maximum {d m M : ℕ} {tree : Tree d}
    (ht : tree.Valid) (hb : tree.bounds = some (m, M)) : tree.member M = true :=
  (Tree.member_iff_contains ht M).mpr (ht.contains_maximum hb)

private theorem memberLoop_finish {w base query answer : ℕ} {s : Data 32}
    (hs : MemberEntry base query s)
    (he : ExecWithin w memberBody s (memberNext s base query) 26)
    (hk : (memberNext s base query).regs runFlag = 0)
    (hout : (memberNext s base query).regs out = answer) :
    ∃ z, ExecWithin w memberLoop s z 30 ∧ z.regs out = answer ∧ z.mem = s.mem := by
  have hz := (memberNext_constants hs).1
  refine ⟨_, he.loop_once (cond := .lt zero runFlag) ?_ ?_,
    hout, memberNext_mem _ _ _⟩
  · simp only [Cond.holds_lt, hs.zero_eq, hs.runFlag_eq]
    decide
  · simp only [Cond.holds_lt, hz, hk, lt_self_iff_false, not_false_eq_true]

/-- The membership loop is correct for every depth and arbitrary surrounding memory.
Its bound charges each body, loop test and jump; setup, dispatch and halt are separate. -/
theorem memberLoop_spec {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : MemberEntry base query s) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) :
    ∃ z, ExecWithin w memberLoop s z (28 * (d + 1) + 2) ∧
      z.regs out = (if tree.member query then 1 else 0) ∧ z.mem = s.mem := by
  induction d generalizing base query s with
  | zero =>
    have he := memberBody_exec hs ht hr ha
    cases tree with
    | leaf b =>
      cases b with
      | none =>
        have hempty : s.mem base = 0 := hr.1
        apply memberLoop_finish hs he
        · simp +decide [memberNext, hempty]
        · simp +decide [memberNext, hempty, Tree.member, hs.out_eq]
      | some bounds =>
        obtain ⟨m, M⟩ := bounds
        obtain ⟨hpres, ⟨hm, hM⟩, hq, _⟩ := hr
        have hk : (memberNext s base query).regs runFlag = 0 := by
          simp only [memberNext, hpres, hm, hM, hq, splitSize,
            Option.isSome_some, ↓reduceIte]
          split_ifs <;> simp +decide
        apply memberLoop_finish hs he hk
        simp only [memberNext, hpres, hm, hM, hq, splitSize,
          Option.isSome_some, ↓reduceIte, Tree.member]
        split_ifs <;> simp_all +decide [hs.out_eq]
  | succ d ih =>
    have he := memberBody_exec hs ht hr ha
    have finish (hk : (memberNext s base query).regs runFlag = 0)
        (hout : (memberNext s base query).regs out = (if tree.member query then 1 else 0)) :
        ∃ z, ExecWithin w memberLoop s z (28 * (d + 1 + 1) + 2) ∧
          z.regs out = (if tree.member query then 1 else 0) ∧ z.mem = s.mem := by
      obtain ⟨z, hz, ho, hm⟩ := memberLoop_finish hs he hk hout
      exact ⟨z, hz.mono (by omega), ho, hm⟩
    cases tree with
    | node bounds summary cluster =>
      cases bounds with
      | none =>
        have hempty : s.mem base = 0 := hr.1.1
        apply finish
        · simp +decide [memberNext, hempty]
        · simp +decide [memberNext, hempty, Tree.member, hs.out_eq]
      | some bounds =>
        obtain ⟨m, M⟩ := bounds
        obtain ⟨hpres, ⟨hm, hM⟩, hq, hspan⟩ := hr.1
        by_cases hmin : query = m
        · apply finish
          · simp +decide [memberNext, hpres, hm, hmin]
          · simp +decide [memberNext, hpres, hm, hmin, Tree.member]
        by_cases hmax : query = M
        · have hn : M ≠ m := by simpa only [hmax] using hmin
          have hmem := member_maximum ht rfl
          apply finish
          · simp +decide [memberNext, hpres, hm, hM, hmax, hn]
          · simp +decide [memberNext, hpres, hm, hM, hmax, hn, hmem]
        by_cases hlt : query < M
        · have hi := (member_descent_safe ht hr (by simpa only [hM] using hlt)).1
          let i : Fin (universeSize d) := ⟨query / universeSize d, hi⟩
          let next := memberNext s base query
          have hqne : universeSize d ≠ 0 := Nat.ne_of_gt (universeSize_pos d)
          have hentry : MemberEntry (base + clusterOffset d i.val)
              (query % universeSize d) next := by
            obtain ⟨hz, ho, ht, hthree, hfour, hfive⟩ := memberNext_constants hs
            refine ⟨hz, ho, ht, hthree, hfour, hfive, ?_, ?_, ?_, ?_⟩ <;>
              simp +decide [next, memberNext, hpres, hm, hM, hq, hspan, splitSize,
                childSpan, hmin, hmax, hlt, hqne, clusterOffset, i, Nat.add_assoc,
                hs.out_eq, hs.runFlag_eq]
          have hrep : Rep (cluster i) (base + clusterOffset d i.val) next.mem := by
            simpa only [next, memberNext_mem] using hr.2.2 i
          have hfit : Fits w (base + clusterOffset d i.val + span d) :=
            ha.of_le (by have := cluster_end_le_span d hi; dsimp only [i]; omega)
          obtain ⟨z, hz, ho, hmem⟩ := ih hentry (ht.2.2.1 i) hrep hfit
          refine ⟨z, (he.loop_iter (cond := .lt zero runFlag) ?_ hz).mono (by omega),
            ?_, hmem.trans (memberNext_mem _ _ _)⟩
          · simp only [Cond.holds_lt, hs.zero_eq, hs.runFlag_eq]
            decide
          · simpa only [Tree.member, hmin, hi, ↓reduceDIte, ↓reduceIte] using ho
        · have habsent := member_eq_false_of_max_lt (query := query) ht rfl (by omega)
          apply finish
          · simp +decide [memberNext, hpres, hm, hM, hmin, hmax, hlt]
          · simp +decide [memberNext, hpres, hm, hM, hmin, hmax, hlt, habsent, hs.out_eq]

end Cslib.Algorithms.WordRAM.VanEmdeBoas
