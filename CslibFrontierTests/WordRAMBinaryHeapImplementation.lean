/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Implementation

/-! Actual same-code method executions through the completed raw implementation. Each call
starts from the existing, explicitly uncharged prepared-argument convention. These fixtures
do not claim a charged native controller or allocated-client implementation. -/

namespace CslibFrontierTests.WordRAMBinaryHeapImplementation

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
open Cslib.DataStructure.PriorityQueue.BinaryHeap (space)

noncomputable section

private def initial (n base : ℕ) (mem : ℕ → ℕ) : Data Program.registers :=
  ⟨fun i => if i = Program.code.frontierReg then base else
    if i = Program.code.nReg then n else 0, mem⟩

private theorem initial_bounded {w n base : ℕ} (mem : ℕ → ℕ)
    (hn : Fits w n) (hb : Fits w base) (hm : ∀ a, Fits w (mem a)) :
    (initial n base mem).Bounded w := by
  refine ⟨fun i => ?_, hm⟩
  dsimp only [initial]
  split_ifs
  · exact hb
  · exact hn
  · exact fits_zero _

private theorem initial_frontier (n base : ℕ) (mem : ℕ → ℕ) :
    (initial n base mem).regs Program.code.frontierReg = base := by
  simp only [initial, ite_true]

private theorem initial_params (n base : ℕ) (mem : ℕ → ℕ) (i : Fin 1) :
    (initial n base mem).regs (Program.code.initParams i) = (![n] : Fin 1 → ℕ) i := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp only [Program.code.initParams_eq, Matrix.cons_val_zero,
    initial, ite_eq_right Program.code.nReg_ne_frontier, ite_true]

private def prepared {w n K base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K)
    (o : IndexedMinPQ.Op n) (x : Data Program.registers) : Data Program.registers :=
  ⟨(subroutineImpl hS hK).prepareRegs o x.regs, x.mem⟩

private theorem prepared_ready {w n K base : ℕ}
    (hS : Fits w (base + space n)) (hK : Fits w K)
    {s : IndexedMinPQ.State n} {x : Data Program.registers} (o : IndexedMinPQ.Op n)
    (hr : (subroutineImpl hS hK).rep s x) (hv : IndexedMinPQ.valid K s o) :
    (subroutineImpl hS hK).rep s (prepared hS hK o x) ∧
      (subroutineImpl hS hK).argMatch o (prepared hS hK o x).regs := by
  let I := subroutineImpl hS hK
  have hx := I.bounded hr
  have hb : (prepared hS hK o x).Bounded w := by
    refine ⟨fun i => ?_, hx.2⟩
    change Fits w (if Program.code.input i then I.encode o i else x.regs i)
    split_ifs with hi
    · exact I.arguments_fit o hv i hi
    · exact hx.1 i
  refine ⟨I.rep_supported (x := x) (x' := prepared hS hK o x)
    ?_ (fun _ _ => rfl) hb hr, ?_⟩
  · intro i hi
    change (if Program.code.input i then I.encode o i else x.regs i) = x.regs i
    simp only [hi, Bool.false_eq_true, ite_false]
  · exact I.encode_matches o x.regs

private theorem live_call {w n K base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K)
    {s : IndexedMinPQ.State n} {x : Data Program.registers} (o : IndexedMinPQ.Op n)
    (hr : (subroutineImpl hS hK).rep s x) (hv : IndexedMinPQ.valid K s o)
    (ha : (subroutineImpl hS hK).argMatch o x.regs) :
    ∃ y N, Exec w Program.code.code x y N ∧
      Program.code.decode (K_max := K) o y.regs = some (IndexedMinPQ.step s o).2 ∧
      (subroutineImpl hS hK).rep (IndexedMinPQ.step s o).1 y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      N ≤ Backend.factor Program.family * (memoryBound o + 1) + 8 := by
  let I := subroutineImpl hS hK
  obtain ⟨y, s', a, N, he, hstep, hd, hr', hm, hb⟩ := I.step_exec o hr hv ha
  have hp : (s', a) = IndexedMinPQ.step s o :=
    ((indexedMinPQSpec n K).step_iff_stepFn s o s' a).mp hstep
  have hstate := congrArg Prod.fst hp
  have hanswer := congrArg Prod.snd hp
  change s' = (IndexedMinPQ.step s o).1 at hstate
  change a = (IndexedMinPQ.step s o).2 at hanswer
  rw [hstate] at hr'
  rw [hanswer] at hd
  change (subroutineImpl hS hK).toSubroutineBase.decode o y.regs = _ at hd
  rw [subroutineImpl_toBase, subroutineBase_decode] at hd
  change Modifies (Block.mk base (subroutineImpl hS hK).toSubroutineBase.space).footprint
    x.mem y.mem at hm
  rw [subroutineImpl_toBase, subroutineBase_space] at hm
  change N + (subroutineImpl hS hK).toSubroutineBase.potential y ≤
    (subroutineImpl hS hK).toSubroutineBase.charge s o +
      (subroutineImpl hS hK).toSubroutineBase.potential x at hb
  rw [subroutineImpl_toBase, subroutineBase_potential, subroutineBase_potential,
    subroutineBase_charge, Nat.add_zero, Nat.add_zero] at hb
  exact ⟨y, N, he, hd, hr', hm, hb⟩

private theorem call {w n K base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K)
    {s : IndexedMinPQ.State n} {x : Data Program.registers} (o : IndexedMinPQ.Op n)
    (hr : (subroutineImpl hS hK).rep s x) (hv : IndexedMinPQ.valid K s o) :
    ∃ y N, Exec w Program.code.code (prepared hS hK o x) y N ∧
      Program.code.decode (K_max := K) o y.regs = some (IndexedMinPQ.step s o).2 ∧
      (subroutineImpl hS hK).rep (IndexedMinPQ.step s o).1 y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      N ≤ Backend.factor Program.family * (memoryBound o + 1) + 8 := by
  obtain ⟨hr', ha⟩ := prepared_ready hS hK o hr hv
  exact live_call hS hK o hr' hv ha

private def prepared7 {n K base : ℕ} (hS : Fits 3 (base + space n)) (hK : Fits 3 K)
    (v : Fin n) (x : Data Program.registers) : Data Program.registers :=
  (prepared hS hK (.getKey v) x).set Program.code.tag0 7

private theorem prepared7_ready {n K base : ℕ} (hS : Fits 3 (base + space n)) (hK : Fits 3 K)
    {s : IndexedMinPQ.State n} {x : Data Program.registers} (v : Fin n)
    (hr : (subroutineImpl hS hK).rep s x) :
    (subroutineImpl hS hK).rep s (prepared7 hS hK v x) ∧
      (subroutineImpl hS hK).argMatch (.getKey v) (prepared7 hS hK v x).regs := by
  let I := subroutineImpl hS hK
  let p := prepared hS hK (.getKey v) x
  obtain ⟨hp, ha⟩ := prepared_ready hS hK (.getKey v) hr trivial
  have hb : (prepared7 hS hK v x).Bounded 3 :=
    (Exec.const (B := Basis.exact) (x := p) (d := Program.code.tag0)
      (show Fits 3 7 by decide)).bounded (I.bounded hp)
  have hr' : I.rep s (prepared7 hS hK v x) := I.rep_supported
    (x := p) (x' := prepared7 hS hK v x) (by
      intro i hi
      have hne : i ≠ Program.code.tag0 := by
        intro he
        subst i
        rw [Program.code.tag0_input] at hi
        contradiction
      exact Function.update_of_ne hne _ _) (fun _ _ => rfl) hb hp
  change I.toSubroutineBase.argMatch (.getKey v) p.regs at ha
  rw [subroutineImpl_toBase, subroutineBase_argMatch] at ha
  rcases ha with ⟨h2, h1, _, hv⟩
  have hn2 := (List.nodup_cons.mp Program.code.args_nodup).1
  have hn1 := (List.nodup_cons.mp (List.nodup_cons.mp Program.code.args_nodup).2).1
  have hn0 := (List.nodup_cons.mp
    (List.nodup_cons.mp (List.nodup_cons.mp Program.code.args_nodup).2).2).1
  have h20 : Program.code.tag2 ≠ Program.code.tag0 := by
    intro he
    exact hn2 (by simp [he])
  have h10 : Program.code.tag1 ≠ Program.code.tag0 := by
    intro he
    exact hn1 (by simp [he])
  have hv0 : Program.code.argV ≠ Program.code.tag0 := by
    intro he
    exact hn0 (by simp [he])
  refine ⟨hr', ?_⟩
  change I.toSubroutineBase.argMatch (.getKey v) (prepared7 hS hK v x).regs
  rw [subroutineImpl_toBase, subroutineBase_argMatch]
  change (p.set Program.code.tag0 7).regs Program.code.tag2 = 0 ∧
    (p.set Program.code.tag0 7).regs Program.code.tag1 = 0 ∧
    (p.set Program.code.tag0 7).regs Program.code.tag0 ≠ 0 ∧
    (p.set Program.code.tag0 7).regs Program.code.argV = v.val
  simpa only [Data.set_regs, Function.update_of_ne h20, Function.update_of_ne h10,
    Function.update_of_ne hv0, Function.update_self] using
    (show p.regs Program.code.tag2 = 0 ∧ p.regs Program.code.tag1 = 0 ∧
      (7 : ℕ) ≠ 0 ∧ p.regs Program.code.argV = v.val from ⟨h2, h1, by decide, hv⟩)

private def zeroHeapMem (a : ℕ) : ℕ := if a = 100 then 1 else 0

-- Capacity zero still executes actual extraction on the one-bit compact domain.
example : ∃ x y N,
    (subroutineImpl (n := 0) (base := 0) (show Fits 1 (0 + space 0) by decide)
      (show Fits 1 0 by decide)).rep (IndexedMinPQ.empty 0) x ∧
    Exec 1 Program.code.code
      (prepared (show Fits 1 (0 + space 0) by decide) (show Fits 1 0 by decide) .extractMin x) y N ∧
    Program.code.decode (n := 0) (K_max := 0) .extractMin y.regs = some none ∧ y.mem 100 = 1 := by
  let hS : Fits 1 (0 + space 0) := by decide
  let hK : Fits 1 0 := by decide
  let I := subroutineImpl hS hK
  have hx := initial_bounded zeroHeapMem (show Fits 1 0 by decide)
    (show Fits 1 0 by decide) (fun a => by unfold zeroHeapMem; split <;> decide)
  have hspace : I.space = space 0 := by
    rw [subroutineImpl_toBase, subroutineBase_space]
  obtain ⟨x, _, _, hr, _, hmInit⟩ := I.initFresh_exec hx
    (initial_frontier _ _ _) (initial_params _ _ _) (by
      rw [hspace]
      intro a ha
      rw [Block.mem_footprint] at ha
      have ha0 : a = 0 := by dsimp only [Block.Owns, space] at ha; omega
      subst a
      rfl)
  have hnot : 100 ∉ (Block.mk 0 (space 0)).footprint := by
    rw [Block.mem_footprint]
    dsimp only [Block.Owns, space]
    omega
  obtain ⟨y, N, he, hd, _, hm, _⟩ := call hS hK .extractMin hr trivial
  have hmin : IndexedMinPQ.findMin (IndexedMinPQ.empty 0) = none := rfl
  refine ⟨x, y, N, hr, he, ?_, ?_⟩
  · simpa only [IndexedMinPQ.step, hmin] using hd
  · have hi := hmInit 100 (by rwa [hspace])
    exact (hm 100 hnot).trans hi

private def shiftedMem (a : ℕ) : ℕ := if a = 0 then 5 else if a = 100 then 7 else 0

private theorem shifted_bounded (a : ℕ) : Fits 3 (shiftedMem a) := by
  unfold shiftedMem
  split_ifs <;> decide

private theorem shifted_zero (a : ℕ) (ha : a ∈ (Block.mk 3 (space 1)).footprint) :
    shiftedMem a = 0 := by
  rw [Block.mem_footprint] at ha
  dsimp only [Block.Owns, space] at ha
  unfold shiftedMem
  split_ifs <;> omega

-- The same program inserts maximal key7, looks it up with positive tag7, decreases it to2 and
-- extracts the typed handle, retaining outside sentinels. Argument preparation stays explicit.
example : ∃ x₀ x₁ x₂ x₃ x₄ N₁ N₂ N₃ N₄,
    let hS : Fits 3 (3 + space 1) := by decide
    let hK : Fits 3 7 := by decide
    Exec 3 Program.code.code (prepared hS hK (.insert 0 7) x₀) x₁ N₁ ∧
    Exec 3 Program.code.code (prepared7 hS hK 0 x₁) x₂ N₂ ∧
    Exec 3 Program.code.code (prepared hS hK (.decreaseKey 0 2) x₂) x₃ N₃ ∧
    Exec 3 Program.code.code (prepared hS hK .extractMin x₃) x₄ N₄ ∧
    Program.code.decode (n := 1) (K_max := 7) (.getKey 0) x₂.regs = some (some 7) ∧
    Program.code.decode (n := 1) (K_max := 7) .extractMin x₄.regs =
      some (some ((0 : Fin 1), 2)) ∧
    (subroutineImpl hS hK).rep (IndexedMinPQ.empty 1) x₄ ∧ x₄.mem 0 = 5 ∧ x₄.mem 100 = 7 ∧
    N₁ + N₂ + N₃ + N₄ ≤ 35 * Backend.factor Program.family + 32 := by
  let hS : Fits 3 (3 + space 1) := by decide
  let hK : Fits 3 7 := by decide
  let I := subroutineImpl hS hK
  have hx := initial_bounded shiftedMem (show Fits 3 1 by decide)
    (show Fits 3 3 by decide) shifted_bounded
  have hspace : I.space = space 1 := by
    rw [subroutineImpl_toBase, subroutineBase_space]
  obtain ⟨x₀, _, _, hr₀, _, hmInit⟩ := I.initFresh_exec hx
    (initial_frontier _ _ _) (initial_params _ _ _) (by rw [hspace]; exact shifted_zero)
  let s₁ := Function.update (IndexedMinPQ.empty 1) (0 : Fin 1) (some 7)
  let s₂ := Function.update s₁ (0 : Fin 1) (some 2)
  obtain ⟨x₁, N₁, he₁, _, hr₁, hm₁, hb₁⟩ := call hS hK (.insert 0 7) hr₀ ⟨rfl, le_rfl⟩
  change I.rep s₁ x₁ at hr₁
  obtain ⟨hready7, harg7⟩ := prepared7_ready hS hK (0 : Fin 1) hr₁
  obtain ⟨x₂, N₂, he₂, hd₂, hr₂, hm₂, hb₂⟩ := live_call hS hK (.getKey 0) hready7 trivial harg7
  change I.rep s₁ x₂ at hr₂
  have hv : IndexedMinPQ.valid 7 s₁ (.decreaseKey 0 2) :=
    ⟨⟨7, rfl, by decide⟩, by decide⟩
  obtain ⟨x₃, N₃, he₃, _, hr₃, hm₃, hb₃⟩ := call hS hK (.decreaseKey 0 2) hr₂ hv
  change I.rep s₂ x₃ at hr₃
  have hmin : IndexedMinPQ.findMin s₂ = some ((0 : Fin 1), 2) := by
    apply IndexedMinPQ.findMin_eq_some_iff.mpr
    refine ⟨rfl, ?_⟩
    intro v k hv
    have he : v = 0 := Subsingleton.elim _ _
    subst v
    have hk : 2 = k := Option.some.inj hv
    subst k
    exact Or.inr ⟨rfl, le_rfl⟩
  obtain ⟨x₄, N₄, he₄, hd₄, hr₄, hm₄, hb₄⟩ := call hS hK .extractMin hr₃ trivial
  have hemp : Function.update s₂ (0 : Fin 1) none = IndexedMinPQ.empty 1 := by
    funext v
    have he : v = 0 := Subsingleton.elim _ _
    subst v
    rfl
  have hnot (a : ℕ) (ha : a = 0 ∨ a = 100) : a ∉ (Block.mk 3 (space 1)).footprint := by
    rw [Block.mem_footprint]
    dsimp only [Block.Owns, space]
    omega
  have houtside (a : ℕ) (ha : a = 0 ∨ a = 100) : x₄.mem a = shiftedMem a := by
    have hn := hnot a ha
    have hi := hmInit a (by rwa [hspace])
    exact (hm₄ a hn).trans ((hm₃ a hn).trans ((hm₂ a hn).trans ((hm₁ a hn).trans hi)))
  refine ⟨x₀, x₁, x₂, x₃, x₄, N₁, N₂, N₃, N₄, he₁, he₂, he₃, he₄, ?_, ?_, ?_,
    houtside 0 (Or.inl rfl), houtside 100 (Or.inr rfl), ?_⟩
  · simpa only [IndexedMinPQ.step, s₁, Function.update_self] using hd₂
  · simpa only [IndexedMinPQ.step, hmin] using hd₄
  · simpa only [IndexedMinPQ.step, hmin, hemp] using hr₄
  · norm_num [memoryBound, Cslib.DataStructure.PriorityQueue.BinaryHeap.Memory.opCost]
      at hb₁ hb₂ hb₃ hb₄
    omega

end

end CslibFrontierTests.WordRAMBinaryHeapImplementation
