/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Stack
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases

/-!
# Fixed-length records on the bounded word-RAM stack

Record transfers reuse `Stack.program` and its top-first list representation. A record bank is
disjoint from the nine dispatcher registers. Pushing visits the bank in reverse order; popping
visits it in forward order, restoring the same record order. Argument delivery and result copies
are actual instructions. A final self-copy on `idle` supplies the empty-bank case.

The reserved stack memory may be dirty outside its live prefix, and popped cells are not cleared.
All transfers retain the same reserved footprint. Their costs exclude the final program halt.

## Main definitions

* `Stack.pushRecord`, `Stack.popRecord`: native transfers of a finite register bank.

## Main results

* `Stack.pushRecord_exec`: push `n` words in `9 * n + 1` instructions, preserving caller registers.
* `Stack.popRecord_exec`: pop `n` words in `14 * n + 1` instructions, preserving other registers.
* `Stack.pushRecord_not_readsWidth`, `Stack.popRecord_not_readsWidth`: width-independent code.

The native argument-delivery and framing proofs are extracted from the Chan–He traversal
controller. They use the existing bounded stack certificate, not another stack representation.
-/

public section

namespace Cslib.WordRAM.Stack

variable {r n : ℕ}

private def pushWord (reg : Fin 9 → Fin r) (src : Fin r) : Code .standard r :=
  let tagReg := reg tag
  let argReg := reg arg
  .seq (ram[ tagReg ← #0; argReg ← src ]) (program.rename reg)

private def popWord (reg : Fin 9 → Fin r) (dst : Fin r) : Code .standard r :=
  let tagReg := reg tag
  let argReg := reg arg
  .seq (ram[ tagReg ← #1; argReg ← #0 ])
    (.seq (program.rename reg) (.op (.copy dst (reg out))))

private theorem pushWord_exec (reg : Fin 9 → Fin r) (hi : Function.Injective reg)
    (src : Fin r) (hd : ∀ j, src ≠ reg j) {w base capacity : ℕ} (x : Data r) (vs : List ℕ)
    (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    (hr : Rep w base capacity vs (x.comap reg)) (hw : Fits w (x.regs src))
    (hv : vs.length < capacity) :
    ∃ y, Exec w (pushWord reg src) x y 9 ∧
      Rep w base capacity (x.regs src :: vs) (y.comap reg) ∧
      Modifies (footprint base capacity) x.mem y.mem ∧
      ∀ j, (∀ i, j ≠ reg i) → y.regs j = x.regs j := by
  let q := (x.set (reg tag) 0).set (reg arg) (x.regs src)
  have hp : Exec (B := .standard) w
      (.seq (.op (.const (reg tag) 0)) (.op (.copy (reg arg) src))) x q 2 := by
    ram_eval [q, hd tag]
  have hq : q.comap reg = (implementation w capacity).prepare (.push (x.regs src))
      (x.comap reg) := by
    ext j
    · fin_cases j <;>
        simp +decide [q, Data.comap, Data.set, hi.eq_iff, implementation,
          DynamicProgram.prepare, tag, arg]
    · rfl
  obtain ⟨a, ha, _, hra, hframe⟩ := execute h2 hcap hr (.push (x.regs src)) ⟨hv, hw⟩
  have hcall : Exec w program (q.comap reg) a 7 := by
    simpa only [hq, bodyCost] using ha
  let y := a.extend reg q
  refine ⟨y, hp.seq (hcall.rename hi), ?_, hframe, ?_⟩
  · simpa only [y, Data.comap_extend hi] using hra
  · intro j hj
    rw [show (a.extend reg q).regs j = q.regs j from
      Function.extend_apply' _ _ _ (by rintro ⟨i, rfl⟩; exact hj i rfl)]
    simp only [q, Data.set_regs, Function.update_of_ne (hj arg), Function.update_of_ne (hj tag)]

private theorem popWord_exec (reg : Fin 9 → Fin r) (hi : Function.Injective reg)
    (dst : Fin r) (hd : ∀ j, dst ≠ reg j) {w base capacity : ℕ}
    (x : Data r) (v : ℕ) (vs : List ℕ) (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    (hr : Rep w base capacity (v :: vs) (x.comap reg)) :
    ∃ y, Exec w (popWord reg dst) x y 14 ∧
      Rep w base capacity vs (y.comap reg) ∧ y.regs dst = v ∧
      Modifies (footprint base capacity) x.mem y.mem ∧
      ∀ j, (∀ i, j ≠ reg i) → j ≠ dst → y.regs j = x.regs j := by
  let q := (x.set (reg tag) 1).set (reg arg) 0
  have h1 : Fits w 1 := h2.of_le (by decide)
  have hp : Exec (B := .standard) w
      (.seq (.op (.const (reg tag) 1)) (.op (.const (reg arg) 0))) x q 2 := by
    ram_eval [q, h1]
  have hq : q.comap reg = (implementation w capacity).prepare .pop (x.comap reg) := by
    ext j
    · fin_cases j <;>
        simp +decide [q, Data.comap, Data.set, hi.eq_iff, implementation,
          DynamicProgram.prepare, tag, arg]
    · rfl
  obtain ⟨a, ha, hans, hra, hframe⟩ := execute h2 hcap hr .pop trivial
  have hcall : Exec w program (q.comap reg) a 11 := by
    simpa only [hq, bodyCost, List.cons_ne_nil, ↓reduceIte] using ha
  have hout : a.regs out = v := by
    change some (if a.regs present = 0 then none else some (a.regs out)) = some (some v) at hans
    split at hans
    · cases hans
    · exact Option.some.inj (Option.some.inj hans)
  have hread : (a.extend reg q).regs (reg out) = v := by
    change Function.extend reg a.regs q.regs (reg out) = v
    rw [hi.extend_apply, hout]
  let y := (a.extend reg q).set dst v
  have hcopy : Exec (B := .standard) w
      (.op (.copy dst (reg out))) (a.extend reg q) y 1 := by
    simpa only [y, hread] using
      (Exec.copy (B := Basis.standard) (w := w) (x := a.extend reg q) (d := dst) (s := reg out))
  have hrep : y.comap reg = a := by
    ext j
    · change Function.update (a.extend reg q).regs dst v (reg j) = a.regs j
      rw [Function.update_of_ne (hd j).symm]
      exact hi.extend_apply _ _ j
    · rfl
  refine ⟨y, hp.seq ((hcall.rename hi).seq hcopy), ?_, Function.update_self .., hframe, ?_⟩
  · simpa only [hrep, List.tail_cons] using hra
  · intro j hj hji
    change Function.update (a.extend reg q).regs dst v j = x.regs j
    rw [Function.update_of_ne hji,
      show (a.extend reg q).regs j = q.regs j from
        Function.extend_apply' _ _ _ (by rintro ⟨i, rfl⟩; exact hj i rfl)]
    simp only [q, Data.set_regs, Function.update_of_ne (hj arg), Function.update_of_ne (hj tag)]

/-- Push a register bank in reverse order, leaving its words in forward order at the stack top.
The terminal self-copy preserves the entire state, including for a zero-length record. -/
@[expose] def pushRecord (reg : Fin 9 → Fin r) :
    {n : ℕ} → (Fin n → Fin r) → Fin r → Code .standard r
  | 0, _, idle => .op (.copy idle idle)
  | n + 1, src, idle =>
    let tagReg := reg tag
    let argReg := reg arg
    let word := src (Fin.last n)
    .seq (.seq (ram[ tagReg ← #0; argReg ← word ]) (program.rename reg))
      (pushRecord reg (fun i : Fin n => src i.castSucc) idle)

/-- Pop into successive record registers, charging dispatch and delivery for every word.
The terminal self-copy supplies the zero-length case. -/
@[expose] def popRecord (reg : Fin 9 → Fin r) :
    {n : ℕ} → (Fin n → Fin r) → Fin r → Code .standard r
  | 0, _, idle => .op (.copy idle idle)
  | n + 1, dst, idle =>
    let tagReg := reg tag
    let argReg := reg arg
    .seq (.seq (ram[ tagReg ← #1; argReg ← #0 ])
      (.seq (program.rename reg) (.op (.copy (dst 0) (reg out)))))
      (popRecord reg (fun i : Fin n => dst i.succ) idle)

/-- Pushing a fixed record does not inspect the physical word width. -/
theorem pushRecord_not_readsWidth (reg : Fin 9 → Fin r) (src : Fin n → Fin r) (idle : Fin r) :
    ¬(pushRecord reg src idle).ReadsWidth := by
  induction n with
  | zero => simp [pushRecord, Code.ReadsWidth, Op.ReadsWidth]
  | succ n ih =>
    simp [pushRecord, Code.ReadsWidth, Op.ReadsWidth, ih, program, Code.rename, Op.rename,
      writeAt, readAt, Op.bin]

/-- Popping a fixed record does not inspect the physical word width. -/
theorem popRecord_not_readsWidth (reg : Fin 9 → Fin r) (dst : Fin n → Fin r) (idle : Fin r) :
    ¬(popRecord reg dst idle).ReadsWidth := by
  induction n with
  | zero => simp [popRecord, Code.ReadsWidth, Op.ReadsWidth]
  | succ n ih =>
    simp [popRecord, Code.ReadsWidth, Op.ReadsWidth, ih, program, Code.rename, Op.rename,
      writeAt, readAt, Op.bin]

/-- Push all record words with exact instruction cost, preserving caller registers and memory
outside the reserved stack. Repeated source registers are permitted. -/
theorem pushRecord_exec (reg : Fin 9 → Fin r) (hi : Function.Injective reg)
    (src : Fin n → Fin r) (idle : Fin r) (hd : ∀ i j, src i ≠ reg j)
    {w base capacity : ℕ} (x : Data r) (vs : List ℕ)
    (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    (hr : Rep w base capacity vs (x.comap reg))
    (hw : ∀ i, Fits w (x.regs (src i))) (hv : n + vs.length ≤ capacity) :
    ∃ y, Exec w (pushRecord reg src idle) x y (9 * n + 1) ∧
      Rep w base capacity (List.ofFn (fun i => x.regs (src i)) ++ vs) (y.comap reg) ∧
      Modifies (footprint base capacity) x.mem y.mem ∧
      ∀ j, (∀ i, j ≠ reg i) → y.regs j = x.regs j := by
  induction n generalizing x vs with
  | zero =>
    have he : Exec (B := .standard) w (.op (.copy idle idle)) x x 1 := by
      convert (Exec.copy (B := Basis.standard) (w := w) (x := x) (d := idle) (s := idle)) using 1
      ext j <;> simp [Data.set]
    exact ⟨x, he, hr, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨z, hz, hrz, hfz, hpz⟩ :=
      pushWord_exec reg hi (src (Fin.last n)) (hd _) x vs h2 hcap hr (hw _) (by omega)
    obtain ⟨y, hy, hry, hfy, hpy⟩ := ih (fun i : Fin n => src i.castSucc)
      (fun i => hd i.castSucc) z (x.regs (src (Fin.last n)) :: vs) hrz
      (fun i => by rw [hpz _ (hd i.castSucc)]; exact hw i.castSucc)
      (by simp only [List.length_cons]; omega)
    refine ⟨y, ?_, ?_, ?_, fun j hj => (hpy j hj).trans (hpz j hj)⟩
    · simpa only [pushRecord, pushWord, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hz.seq hy
    · have hslots : (fun i : Fin n => z.regs (src i.castSucc)) =
          fun i : Fin n => x.regs (src i.castSucc) := funext fun i => hpz _ (hd i.castSucc)
      simpa only [hslots, List.ofFn_succ', List.concat_eq_append, List.append_assoc,
        List.singleton_append] using hry
    · intro a ha
      exact (hfy a ha).trans (hfz a ha)

/-- Pop a complete record into distinct registers with exact cost. Memory outside the reserved
stack and registers outside the dispatcher and destination bank are preserved. -/
theorem popRecord_exec (reg : Fin 9 → Fin r) (hi : Function.Injective reg)
    (dst : Fin n → Fin r) (idle : Fin r) (hinj : Function.Injective dst)
    (hd : ∀ i j, dst i ≠ reg j) {w base capacity : ℕ}
    (x : Data r) (vs : List ℕ) (a : Fin n → ℕ) (h2 : Fits w 2)
    (hcap : Fits w (base + capacity))
    (hr : Rep w base capacity (List.ofFn a ++ vs) (x.comap reg)) :
    ∃ y, Exec w (popRecord reg dst idle) x y (14 * n + 1) ∧
      Rep w base capacity vs (y.comap reg) ∧ (∀ i, y.regs (dst i) = a i) ∧
      Modifies (footprint base capacity) x.mem y.mem ∧
      ∀ j, (∀ i, j ≠ reg i) → (∀ i, j ≠ dst i) → y.regs j = x.regs j := by
  induction n generalizing x with
  | zero =>
    have he : Exec (B := .standard) w (.op (.copy idle idle)) x x 1 := by
      convert (Exec.copy (B := Basis.standard) (w := w) (x := x) (d := idle) (s := idle)) using 1
      ext j <;> simp [Data.set]
    exact ⟨x, he, hr, fun i => Fin.elim0 i, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ n ih =>
    rw [List.ofFn_succ, List.cons_append] at hr
    obtain ⟨z, hz, hrz, hout, hfz, hpz⟩ :=
      popWord_exec reg hi (dst 0) (hd 0) x (a 0) (List.ofFn (fun i => a i.succ) ++ vs)
        h2 hcap hr
    obtain ⟨y, hy, hry, hya, hfy, hpy⟩ := ih (fun i : Fin n => dst i.succ)
      (fun i j h => Fin.succ_injective _ (hinj h)) (fun i => hd i.succ)
      z (fun i => a i.succ) hrz
    refine ⟨y, ?_, hry, ?_, ?_, ?_⟩
    · simpa only [popRecord, popWord, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hz.seq hy
    · intro i
      refine Fin.cases ?_ (fun j => hya j) i
      rw [hpy (dst 0) (hd 0) (fun j h => Fin.succ_ne_zero j (hinj h).symm)]
      exact hout
    · intro a ha
      exact (hfy a ha).trans (hfz a ha)
    · intro j hj hdst
      exact (hpy j hj (fun i => hdst i.succ)).trans (hpz j hj (hdst 0))

end Cslib.WordRAM.Stack
