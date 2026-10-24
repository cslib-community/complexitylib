/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.Parameters
public import Complexity.Algorithms.WordRAM.FusionTree.ReadHeader

/-!
# Register banks for fusion-node queries

The query uses a fixed register file. Header, compression, rank, neighbor, boundary, and
multiword highest-bit workspaces occupy disjoint intervals. Explicit copies connect them.

## Main definitions

* `NodeProgram.registers`, `NodeProgram.query`, `NodeProgram.pointer`, `NodeProgram.out`,
  `NodeProgram.argument`, `NodeProgram.cut`, `NodeProgram.zero`, `NodeProgram.chosen`,
  `NodeProgram.divergence`, `NodeProgram.position`: physical register count and caller registers.
* `NodeProgram.bank`, `NodeProgram.headerBank`, `NodeProgram.compressBank`,
  `NodeProgram.rankBank`, `NodeProgram.neighborBank`, `NodeProgram.boundaryBank`,
  `NodeProgram.parameter`, `NodeProgram.count`: contiguous subroutine register banks and header
  register indices.
* `NodeProgram.Frame`: memory and registers below forty are unchanged by a subroutine.
* `NodeProgram.moves`, `NodeProgram.moved`: charged register copies, with a terminal self-copy,
  and their resulting state.
* `NodeProgram.Prepared`: the actual eighteen loaded header words supply node parameters.

## References

* [FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.NodeProgram

open Cslib.WordRAM

/-- Fixed physical register count, independent of width and node occupancy. -/
abbrev registers : ℕ := 1024
/-- Original bounded query. -/
abbrev query : Fin registers := 0
/-- Original record address. -/
abbrev pointer : Fin registers := 1
/-- Final full-key inclusive rank. -/
abbrev out : Fin registers := 2
/-- Full word to compress, and later the compressed result. -/
abbrev argument : Fin registers := 3
/-- Initial inclusive sketch rank. -/
abbrev cut : Fin registers := 4
/-- Constant zero for control flow. -/
abbrev zero : Fin registers := 5
/-- Selected full key. -/
abbrev chosen : Fin registers := 6
/-- Exclusive or of the selected full key and original query. -/
abbrev divergence : Fin registers := 7
/-- Highest differing position on a miss. -/
abbrev position : Fin registers := 8

/-- A contiguous register embedding. -/
def bank {k : ℕ} (offset : ℕ) (hk : offset + k ≤ registers) (i : Fin k) :
    Fin registers := ⟨offset + i.val, by omega⟩

/-- Contiguous register embeddings are injective. -/
theorem bank_injective {k offset : ℕ} (hk : offset + k ≤ registers) :
    Function.Injective (bank offset hk) := by
  intro i j he
  apply Fin.ext
  have := congrArg Fin.val he
  dsimp only [bank] at this
  omega

/-- A renamed subroutine cannot write a register outside its embedding. This proof treats
the subroutine structurally and does not expand its instruction graph. -/
private theorem preserves_rename {k : ℕ} {f : Fin k → Fin registers} (c : Code .standard k)
    (i : Fin registers) (hi : ∀ j, f j ≠ i) : (c.rename f).Preserves i := by
  induction c with
  | op o =>
    cases o <;> simp only [Code.rename, Code.Preserves, Op.rename, Op.dest,
      ne_eq, Option.some.injEq, reduceCtorEq, not_false_eq_true] <;> apply hi
  | seq a b iha ihb => exact ⟨iha, ihb⟩
  | branch cond pos neg ihp ihn => exact ⟨ihp, ihn⟩
  | loop cond body ih => exact ih

/-- In particular, a contiguous bank frames every physical register outside its interval. -/
theorem preserves_bank {k offset : ℕ} (hk : offset + k ≤ registers)
    (c : Code .standard k) (i : Fin registers)
    (hi : i.val < offset ∨ offset + k ≤ i.val) :
    (c.rename (bank offset hk)).Preserves i := by
  apply preserves_rename
  intro j he
  have := congrArg Fin.val he
  dsimp only [bank] at this
  omega

/-- Eighteen-word header reader, including its pointer and address scratch. -/
abbrev headerBank : Fin 21 → Fin registers := bank 10 (by decide)
/-- Compression workspace. -/
abbrev compressBank : Fin 21 → Fin registers := bank 40 (by decide)
/-- Inclusive or strict rank workspace. -/
abbrev rankBank : Fin 10 → Fin registers := bank 70 (by decide)
/-- Two-neighbor loader and selector. -/
abbrev neighborBank : Fin 17 → Fin registers := bank 90 (by decide)
/-- Correction boundaries. -/
abbrev boundaryBank : Fin 10 → Fin registers := bank 110 (by decide)

/-- Header register holding one of the fifteen stored preprocessing words. -/
def parameter (j : Fin 15) : Fin registers := headerBank ⟨j.val + 4, by omega⟩
/-- Header register holding occupancy. -/
abbrev count : Fin registers := headerBank 2

/-- Memory and caller registers below forty agree. The direction follows execution. -/
def Frame (x y : Data registers) : Prop :=
  y.mem = x.mem ∧ ∀ i : Fin registers, i.val < 40 → y.regs i = x.regs i

/-- `Frame` is reflexive. -/
theorem Frame.refl (x : Data registers) : Frame x x := ⟨rfl, fun _ _ => rfl⟩

/-- `Frame` is transitive. -/
theorem Frame.trans {x y z : Data registers} (hxy : Frame x y) (hyz : Frame y z) :
    Frame x z := ⟨hyz.1.trans hxy.1, fun i hi => (hyz.2 i hi).trans (hxy.2 i hi)⟩

/-- Updating a register at index at least `40` preserves `Frame`. -/
theorem frame_set (x : Data registers) (i : Fin registers) (v : ℕ) (hi : 40 ≤ i.val) :
    Frame x (x.set i v) := by
  refine ⟨rfl, ?_⟩
  intro j hj
  have hn : j ≠ i := by intro he; subst j; omega
  exact Function.update_of_ne hn _ _

/-- Extending a subroutine state into a register bank at offset at least `40` preserves `Frame`. -/
theorem frame_extend {k offset : ℕ} (hk : offset + k ≤ registers) (ho : 40 ≤ offset)
    (x : Data registers) (y : Data k) (hm : y.mem = x.mem) :
    Frame x (y.extend (bank offset hk) x) := by
  refine ⟨hm, ?_⟩
  intro i hi
  apply Function.extend_apply'
  rintro ⟨j, he⟩
  have := congrArg Fin.val he
  dsimp only [bank] at this
  omega

/-- Copy a finite sequence of registers, charging also a final self-copy of register 39.
The final self-copy supplies an executable empty sequence without a special RAM primitive. -/
def moves : List (Fin registers × Fin registers) → Code .standard registers
  | [] => .op (.copy 39 39)
  | (dst, src) :: rest => .seq (.op (.copy dst src)) (moves rest)

/-- Exact result of the charged copies. -/
def moved (xs : List (Fin registers × Fin registers)) (x : Data registers) : Data registers :=
  xs.foldl (fun y p => y.set p.1 (y.regs p.2)) x

/-- The instruction count of `moves xs` is `xs.length + 1`. -/
theorem size_moves (xs : List (Fin registers × Fin registers)) :
    (moves xs).size = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons p ps ih => simp only [moves, Code.size, List.length_cons, ih]; omega

/-- Executing `moves xs` reaches `moved xs x` in `xs.length + 1` steps. -/
theorem exec_moves (w : ℕ) (xs : List (Fin registers × Fin registers)) (x : Data registers) :
    Exec w (moves xs) x (moved xs x) (xs.length + 1) := by
  induction xs generalizing x with
  | nil =>
    have he : x.set 39 (x.regs 39) = x := by
      ext i
      · simp only [Data.set_regs, Function.update_eq_self]
      · rfl
    simpa only [moves, moved, List.foldl_nil, List.length_nil, Nat.zero_add, he] using
      (Exec.copy (B := .standard) (w := w) (d := 39) (s := 39) (x := x))
  | cons p xs ih =>
    simpa only [moves, moved, List.foldl_cons, List.length_cons, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using
      (Exec.copy (B := .standard) (w := w) (d := p.1) (s := p.2) (x := x)).seq
        (ih (x.set p.1 (x.regs p.2)))

/-- Register copies whose destinations are at index at least `40` preserve `Frame`. -/
theorem frame_moved (xs : List (Fin registers × Fin registers)) (x : Data registers)
    (hs : ∀ p ∈ xs, 40 ≤ p.1.val) : Frame x (moved xs x) := by
  induction xs generalizing x with
  | nil => exact Frame.refl x
  | cons p ps ih =>
    have hp := hs p (by simp)
    have hf : Frame x (x.set p.1 (x.regs p.2)) := by
      refine ⟨rfl, ?_⟩
      intro i hi
      have hn : i ≠ p.1 := by intro he; subst i; omega
      exact Function.update_of_ne hn _ _
    exact hf.trans (ih _ (fun q hq => hs q (by simp only [List.mem_cons]; exact Or.inr hq)))

/-- Literal values loaded from the actual header. This is a register contract, with no
correctness, execution, or rank oracle among its fields. -/
structure Prepared {w n : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (x : Data registers) : Prop where
  /-- Actual occupancy word. -/
  count_eq : x.regs count = n
  /-- Actual fifteen parameter words. -/
  words_eq : ∀ j : Fin 15, x.regs (parameter j) = p.words j

/-- The `Prepared` header invariant is preserved across `Frame` transitions. -/
theorem Prepared.frame {w n : ℕ} {keys : Fin n → ℕ} {p : NodeParameters w keys}
    {x y : Data registers} (hx : Prepared p x) (hf : Frame x y) : Prepared p y := by
  constructor
  · exact (hf.2 count (by decide)).trans hx.count_eq
  · intro j
    exact (hf.2 (parameter j) (by dsimp [parameter, headerBank, bank]; omega)).trans
      (hx.words_eq j)

/-- Caller scratch registers zero through nine are disjoint from the loaded header. -/
theorem Prepared.set_low {w n : ℕ} {keys : Fin n → ℕ} {p : NodeParameters w keys}
    {x : Data registers} (hx : Prepared p x) (i : Fin registers) (v : ℕ) (hi : i.val < 10) :
    Prepared p (x.set i v) := by
  constructor
  · have hn : count ≠ i := by
      intro he
      have := congrArg Fin.val he
      dsimp only [count, headerBank, bank] at this
      omega
    exact (Function.update_of_ne hn _ _).trans hx.count_eq
  · intro j
    have hn : parameter j ≠ i := by
      intro he
      have := congrArg Fin.val he
      dsimp only [parameter, headerBank, bank] at this
      omega
    exact (Function.update_of_ne hn _ _).trans (hx.words_eq j)

end Cslib.Algorithms.WordRAM.FusionTree.NodeProgram
