/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalInvariant

/-!
# Shared native initialization of a Chan–He root

The catalogue producer and in-place consumer execute the same four setup instructions and
seven-word root push. This boundary proves their actual 68-instruction prefix once, retaining
the root's word order, persistent registers and stack write frame.

## Main definitions

* `initializeRoot`: the existing setup and root push, without a traversal loop.

## Main results

* `initializeRoot_exec`: exact charged initialization and root-stack readback.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- The common four-instruction setup and actual seven-word push. -/
@[expose] def initializeRoot : Code .standard 128 :=
  let ptr := registers WordStack.ptr
  let len := registers WordStack.len
  .seq (ram[ zero ← #0; one ← #1; ptr ← stackBase; len ← #0 ]) pushFrame

/-- Initialize the existing stack from an actual loaded descriptor, preserving every register
outside the stack dispatcher and changing memory only in its reserved footprint. -/
theorem initializeRoot_exec {a : Arena} {w : ℕ} (x : Data 128) (e : Entry)
    (hx : x.Bounded w) (hc : a.Controls x) (hl : e.Loaded x)
    (h2 : Fits w 2) (hcap : Fits w (a.stack + a.capacity)) (hcapacity : 7 ≤ a.capacity) :
    ∃ b, Exec w initializeRoot x b 68 ∧
      WordStack.Rep w a.stack a.capacity e.words (b.comap registers) ∧
      a.Controls b ∧ Modifies (WordStack.footprint a.stack a.capacity) x.mem b.mem ∧
      ∀ i, Outside i → b.regs i = x.regs i := by
  let p := (((x.set zero 0).set one 1).set (registers WordStack.ptr) (x.regs stackBase)).set
    (registers WordStack.len) 0
  let ptr := registers WordStack.ptr
  let len := registers WordStack.len
  have h1 : Fits w 1 := h2.of_le (by decide)
  have hp : Exec (B := .standard) w
      (ram[ zero ← #0; one ← #1; ptr ← stackBase; len ← #0 ]) x p 4 := by
    ram_eval [p, ptr, len, zero, one, registers, WordStack.ptr, WordStack.len, stackBase, h1]
  have pmeta (i : Fin 128) (hi : Outside i) : p.regs i = x.regs i := by
    have hne (j : Fin 9) : i ≠ registers j := by
      intro he
      have hv := congrArg Fin.val he
      dsimp only [registers] at hv
      rcases hi with hi | hi <;> omega
    simp only [p, Data.set_regs, Function.update_of_ne (hne WordStack.len),
      Function.update_of_ne (hne WordStack.ptr)]
    by_cases hz : i = zero
    · subst i
      simpa +decide [Data.set, zero, one] using hc.2.2.2.2.2.2.2.2.2.1.symm
    · by_cases ho : i = one
      · subst i
        simpa +decide [Data.set, zero, one] using hc.2.2.2.2.2.2.2.2.2.2.symm
      · simp only [Function.update_of_ne ho, Function.update_of_ne hz]
  have ploaded : e.Loaded p := by
    refine ⟨(pmeta _ (Or.inl (by decide))).trans hl.1, ?_, ?_⟩
    · intro j
      exact (pmeta _ (Or.inl (by dsimp [arraySource, slot]; omega))).trans (hl.2.1 j)
    · intro j
      exact (pmeta _ (Or.inl (by dsimp [arrayLength, slot]; omega))).trans (hl.2.2 j)
  have pstack : WordStack.Rep w a.stack a.capacity [] (p.comap registers) := by
    refine ⟨⟨fun i => (hp.bounded hx).1 (registers i), (hp.bounded hx).2⟩,
      ?_, ?_, Nat.zero_le _, fun i => Fin.elim0 i⟩
    · simpa +decide [p, Data.comap, Data.set, registers, WordStack.ptr, WordStack.len,
        zero, one] using hc.2.2.2.2.2.2.2.1
    · simp +decide [p, Data.comap, Data.set, registers, WordStack.ptr, WordStack.len, zero, one]
  obtain ⟨b, hb, hs, hf, hr⟩ := pushFrame_exec p [] h2 hcap pstack
    (fun i => (hp.bounded hx).1 (slot i)) (by simpa only [List.length_nil] using hcapacity)
  have bm (i : Fin 128) (hi : Outside i) : b.regs i = x.regs i :=
    (hr i hi).trans (pmeta i hi)
  refine ⟨b, hp.seq hb, ?_, hc.congr (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    exact bm i (Or.inl (by omega))), hf, bm⟩
  simpa only [Entry.loaded_words ploaded, List.append_nil] using hs

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
