/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.WordRAM.Realization.Bind
import CslibFrontier.Computability.WordRAM.Realization.Primitive
import CslibFrontier.Computability.WordRAM.Realization.Backend

/-!
A pointer read supplies the continuation's address at runtime. The supplied deterministic
witness uses five backend registers, including frontier, input and result, instead of the
old disjoint construction's six. These are body guarantees: installation and halt are separate.
The same code is checked on maximum-word, zero-pointer and invalid-history boundaries, and
on aliased original source registers. Empty result vectors share the mandatory extra word.
-/

namespace ComplexityTests.WordRAMRealizationBindScratch

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

private def word : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

private def pointerRead (a : ℕ) : Memory.Prog ℕ := do
  let b ← Memory.read a
  Memory.read b

private def supplied :=
  (Realizes.readWitness (B := .exact) word 0).bind
    (Realizes.readWitness (appendWords word word) 1)

private def certificates : Unit → Certificate .exact := fun _ => ⟨supplied⟩

-- The Backend consumes the supplied data, not a classically chosen proof witness.
example : Backend.registers certificates = 5 := by
  simp [Backend.registers, Backend.argWords, Backend.scratchWords, certificates,
    supplied, Realizes.Witness.bind, Realizes.readWitness]

example : Backend.factor certificates = 1 := by
  simp [Backend.factor, certificates, supplied, Realizes.Witness.bind, Realizes.readWitness]

-- The emitted Backend body is exactly the two dependent loads, with no result copies.
example : Backend.code certificates () =
    .seq (.op (.load (Backend.tmp certificates () ⟨2, by decide⟩)
        (Backend.src certificates () ⟨0, by decide⟩)))
      (.op (.load (Backend.tmp certificates () ⟨0, by decide⟩)
        (Backend.tmp certificates () ⟨2, by decide⟩))) := rfl

-- The old two zero-scratch read certificates needed two auxiliary words; packing needs one.
example : supplied.scratchSize = 1 ∧ 0 + 1 + 0 + 1 = 2 := by decide

private def fr : Fin 6 := 0
private def src : Fin 1 → Fin 6 := fun _ => 1
private def tmp : Fin 3 → Fin 6 := fun i => ⟨2 + i.val, by omega⟩

private def initial (frontier address marker : ℕ) (mem : ℕ → ℕ) : Data 6 :=
  ⟨fun i => if i = fr then frontier else if i = 1 then address
    else if i = 5 then marker else 0, mem⟩

-- Tightening a load never changes its endpoint: native execution is deterministic.
private theorem tighten_load {w r T : ℕ} {d a : Fin r} {x y : Data r}
    (h : ExecWithin (B := .exact) w (.op (.load d a)) x y T) :
    ExecWithin (B := .exact) w (.op (.load d a)) x y 1 := by
  obtain ⟨n, _, he⟩ := h
  obtain ⟨n', hn', he'⟩ := ExecWithin.load (B := .exact) (w := w) (d := d) (a := a) (x := x)
  obtain ⟨rfl, _⟩ := he.unique he'
  exact ⟨n', hn', he'⟩

-- Exact same-emitter additive bound: two loads, with the actual first reply kept live.
private theorem pointer_run (w frontier address marker : ℕ) (mem : ℕ → ℕ)
    (hb : (initial frontier address marker mem).Bounded w)
    (hv : (Memory.spec w).ValidHistory ⟨mem, frontier⟩
      ((Memory.spec w).clientHistory ⟨mem, frontier⟩ (pointerRead address))) :
    ∃ y, ExecWithin w (supplied.code fr src tmp) (initial frontier address marker mem) y 2 ∧
      memoryState fr y = ⟨mem, frontier⟩ ∧ y.regs 2 = mem (mem address) ∧
      y.regs 1 = address ∧ y.regs 5 = marker := by
  have hi : Function.Injective tmp := by
    intro a b h
    apply Fin.ext
    have h' := congrArg Fin.val h
    change 2 + a.val = 2 + b.val at h'
    omega
  have hd (i : Fin 1) (j : Fin 3) : src i ≠ tmp j := by
    intro h
    have h' := congrArg Fin.val h
    change 1 = 2 + j.val at h'
    omega
  have hf (j : Fin 3) : tmp j ≠ fr := by
    intro h
    have h' := congrArg Fin.val h
    change 2 + j.val = 0 at h'
    omega
  have hs (i : Fin 1) : src i ≠ fr := by
    change (1 : Fin 6) ≠ 0
    decide
  have h := (Realizes.Witness.bind_execWithin
    (Realizes.readWitness (B := .exact) word 0)
    (Realizes.readWitness (appendWords word word) 1) fr src tmp hi hd hf hs).2
  obtain ⟨y, he, hm, hout, hframe⟩ := h w address (initial frontier address marker mem)
    hb rfl ⟨trivial, trivial⟩ hv 1 1
    (fun _ _ _ _ _ _ he => tighten_load he)
    (fun _ _ _ _ _ _ _ _ _ _ _ he => tighten_load he)
  change ∀ i : Fin 6, i ≠ fr → (∀ j : Fin 3, tmp j ≠ i) →
    y.regs i = (initial frontier address marker mem).regs i at hframe
  refine ⟨y, he, hm, hout 0, ?_, ?_⟩
  · exact hframe 1 (by decide) (fun j h => by
      have h' := congrArg Fin.val h
      change 2 + j.val = 1 at h'
      omega)
  · exact hframe 5 (by decide) (fun j h => by
      have h' := congrArg Fin.val h
      change 2 + j.val = 5 at h'
      have := j.isLt
      omega)

private def maxMemory : ℕ → ℕ := fun a => if a = 0 then 1 else 3

-- Width two admits the largest word 3. The intermediate reply 1 is a valid next address.
example : ∃ y, ExecWithin 2 (supplied.code fr src tmp) (initial 2 0 3 maxMemory) y 2 ∧
    memoryState fr y = ⟨maxMemory, 2⟩ ∧ y.regs 2 = 3 ∧ y.regs 1 = 0 ∧ y.regs 5 = 3 := by
  apply pointer_run 2 2 0 3 maxMemory
  · constructor
    · intro i
      fin_cases i <;> decide
    · intro a
      change Fits 2 (if a = 0 then 1 else 3)
      split_ifs <;> decide
  · decide

private noncomputable def backendInitial : Data (Backend.registers certificates) :=
  ⟨fun i => if i.val = 0 then 2 else 0, maxMemory⟩

-- The generic backend runs the supplied five-register body with its unchanged Spec budget.
example : ∃ y n, Exec 2 (Backend.code certificates ()) backendInitial y n ∧ n ≤ 4 ∧
    y.mem = maxMemory ∧ y.regs (Backend.frontier certificates) = 2 ∧
    y.regs (Backend.tmp certificates () ⟨0, by decide⟩) = 3 ∧
    y.regs (Backend.src certificates () ⟨0, by decide⟩) = 0 := by
  have hx : backendInitial.Bounded 2 := by
    constructor
    · intro i
      change Fits 2 (if i.val = 0 then 2 else 0)
      split_ifs <;> decide
    · intro a
      change Fits 2 (if a = 0 then 1 else 3)
      split_ifs <;> decide
  obtain ⟨y, n, he, hn, hm, ho, _, hr⟩ := Backend.exists_exec_live certificates () (0 : ℕ) hx
    (by funext i; fin_cases i; rfl) ⟨trivial, trivial⟩ (by decide)
  have hanswer := ho ⟨0, by decide⟩
  change y.regs (Backend.tmp certificates () ⟨0, by decide⟩) =
    maxMemory (maxMemory 0) at hanswer
  exact ⟨y, n, he, hn, congrArg Memory.State.mem hm, congrArg Memory.State.frontier hm,
    hanswer,
    hr _ (Backend.src_ne_frontier certificates () _) (fun j =>
      (Backend.src_ne_tmp certificates () () _ j).symm)⟩

-- The identical emitted body follows a zero pointer and reads zero again.
example : ∃ y, ExecWithin 1 (supplied.code fr src tmp) (initial 1 0 1 (fun _ => 0)) y 2 ∧
    memoryState fr y = ⟨fun _ => 0, 1⟩ ∧ y.regs 2 = 0 ∧ y.regs 1 = 0 ∧ y.regs 5 = 1 := by
  apply pointer_run 1 1 0 1 (fun _ => 0)
  · constructor
    · intro i
      fin_cases i <;> decide
    · exact fun _ => fits_zero 1
  · decide

-- A fitting pointer equal to the frontier fails the *oracle history* domain. This is not a
-- claim that the RAM load itself faults or an extra premise invented for the composite.
example : ¬(Memory.spec 2).ValidHistory ⟨fun _ => 2, 2⟩
    ((Memory.spec 2).clientHistory ⟨fun _ => 2, 2⟩ (pointerRead 0)) := by decide

private def pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) := appendWords word word

private def aliased :=
  (Realizes.readWitness (B := .exact) pairWords 0).bind
    (Realizes.readWitness (appendWords pairWords word) 2)

-- The two original environment coordinates may physically alias when their encoded values
-- agree. No injectivity of the input wiring is needed by either retained bind or its Spec.
example : ∃ y, ExecWithin 1 (aliased.code fr (fun _ => 1) tmp)
    (initial 1 0 1 (fun _ => 0)) y 4 ∧ memoryState fr y = ⟨fun _ => 0, 1⟩ ∧
    y.regs 2 = 0 ∧ y.regs 1 = 0 := by
  have hi : Function.Injective tmp := by
    intro a b h
    apply Fin.ext
    have h' := congrArg Fin.val h
    change 2 + a.val = 2 + b.val at h'
    omega
  have hd (i : Fin 2) (j : Fin 3) : (1 : Fin 6) ≠ tmp j := by
    intro h
    have h' := congrArg Fin.val h
    change 1 = 2 + j.val at h'
    omega
  have hf (j : Fin 3) : tmp j ≠ fr := by
    intro h
    have h' := congrArg Fin.val h
    change 2 + j.val = 0 at h'
    omega
  obtain ⟨y, he, hm, ho, hr⟩ := (aliased.code_spec fr (fun _ => 1) tmp hi hd hf
    (fun _ => by decide)).2 1 (0, 0) (initial 1 0 1 (fun _ => 0))
      (by
        constructor
        · intro i
          fin_cases i <;> decide
        · exact fun _ => fits_zero 1)
      (by funext i; fin_cases i <;> rfl) ⟨trivial, trivial⟩ (by decide)
  change ∀ i : Fin 6, i ≠ fr → (∀ j : Fin 3, tmp j ≠ i) →
    y.regs i = (initial 1 0 1 (fun _ => 0)).regs i at hr
  exact ⟨y, he, hm, ho 0, hr 1 (by decide) (fun j h => by
    have h' := congrArg Fin.val h
    change 2 + j.val = 1 at h'
    omega)⟩

-- Both outputs may be empty: two writes share their one mandatory extra word.
private def emptyResults :=
  (Realizes.writeWitness (B := .exact) pairWords 0 1).bind
    (Realizes.writeWitness (appendWords pairWords
      (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding) 0 1)

private def writeInitial : Data 6 := ⟨![2, 1, 3, 1, 1, 1], fun _ => 1⟩

example : ∃ y, ExecWithin 2 (emptyResults.code 0 ![1, 2] (fun _ => 3))
    writeInitial y 4 ∧ y.mem = Function.update (fun _ => 1) 1 3 ∧
    y.regs 0 = 2 ∧ y.regs 1 = 1 ∧ y.regs 2 = 3 ∧ y.regs 5 = 1 := by
  obtain ⟨y, he, hm, _, hr⟩ := (emptyResults.code_spec 0 ![1, 2] (fun _ => 3)
    (by
      change Function.Injective (fun _ : Fin 1 => (3 : Fin 6))
      exact fun _ _ _ => Subsingleton.elim _ _)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide)
    (fun _ => by decide) (by intro i; fin_cases i <;> decide)).2 2 (1, 3) writeInitial
      (by
        constructor
        · intro i
          fin_cases i <;> decide
        · intro a
          change Fits 2 1
          decide)
      (by funext i; fin_cases i <;> rfl) ⟨trivial, trivial⟩ (by decide)
  have hmem := congrArg Memory.State.mem hm
  have hfront := congrArg Memory.State.frontier hm
  refine ⟨y, he, ?_, hfront, hr 1 (by decide) (fun _ => by decide),
    hr 2 (by decide) (fun _ => by decide), hr 5 (by decide) (fun _ => by decide)⟩
  change y.mem = Function.update (Function.update (fun _ => 1) 1 3) 1 3 at hmem
  simpa only [Function.update_idem] using hmem

end ComplexityTests.WordRAMRealizationBindScratch
