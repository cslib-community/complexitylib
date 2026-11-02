/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (canonical initialized flat-program clients)

public import Complexity.Algorithms.WordRAM.Dijkstra.ListEncode
public import Complexity.Computability.WordRAM.Realization.Bind
public import Complexity.Computability.WordRAM.Realization.Glue
public import Complexity.Computability.WordRAM.Realization.Primitive
public import Complexity.Computability.WordRAM.Realization.Program.Standard

/-!
# Canonical flat programs for an actual memory client

One fixed program writes a runtime word to an input-memory cell and reads it back. The complete
native post-memory, frontier and encoded result are checked without any register-bank proof in
the client. The empty-input case keeps the actual positive next-free-address premise.
-/

public section

namespace Cslib.WordRAM.Realization.Tests.StandardProgram

open Cslib.DataStructure

private abbrev word : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
private abbrev unitWords : Unit ↪ (Fin 0 → ℕ) := (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
private abbrev arguments : ℕ × ℕ ↪ (Fin 2 → ℕ) := appendWords word word

private def writeRead (d : ℕ × ℕ) : Memory.Prog ℕ := do
  Memory.write d.1 d.2
  Memory.read d.1

private theorem writeRead_realizes :
    Realizes .exact writeRead arguments word (fun _ _ _ => True) (fun _ _ => 1) := by
  have h := (Realizes.write (B := .exact) arguments 0 1).bind
    (Realizes.read (appendWords arguments unitWords) 0)
  exact h.consequence (fun _ _ _ _ _ _ => ⟨trivial, trivial⟩) (fun _ _ => le_rfl)

/-- A uniform flat program preserves the actual final data of a write followed by a read.
There are no caller-written register indices, disjointness conditions or intermediate states. -/
theorem writeRead_native : ∃ r C pc : ℕ, ∃ prog : Program .exact r,
    ∃ frontier result : Fin r, ∀ w v, Fits w 3 → Fits w v →
      ∃ y n, Runs w prog (State.init [1, v]) ⟨pc, y⟩ n ∧
        step w prog ⟨pc, y⟩ = .halt v ∧
        y.mem 1 = v ∧ y.mem 2 = v ∧ y.mem 100 = 0 ∧
        y.regs frontier = 3 ∧ y.regs result = v ∧ n + 1 ≤ C * 4 + 1 := by
  obtain ⟨r, C, pc, prog, frontier, out, he⟩ :=
    writeRead_realizes.exists_standard_init_program_state (fun d => [d.1, d.2])
      (by intro d i; fin_cases i <;> rfl) 0
  refine ⟨r, C, pc, prog, frontier, out 0, ?_⟩
  intro w v h3 hv
  have hin : InputFits w [1, v] := by
    refine ⟨h3.of_le (by change 2 ≤ 3; decide), ?_⟩
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact h3.of_le (by decide)
    · exact hv
  have hvalid : (Memory.spec w).ValidHistory (inputState [1, v])
      ((Memory.spec w).clientHistory (inputState [1, v]) (writeRead (1, v))) := by
    change (1 < 3 ∧ Fits w v) ∧ 1 < 3 ∧ True
    exact ⟨⟨by decide, hv⟩, by decide, trivial⟩
  obtain ⟨y, n, hr, hh, hm, hout, hn⟩ := he w (1, v)
    (by change 2 ≤ 2; exact le_rfl) h3 hin trivial hvalid
  exact ⟨y, n, hr, hh, congrArg (fun s : Memory.State => s.mem 1) hm,
    congrArg (fun s : Memory.State => s.mem 2) hm,
    congrArg (fun s : Memory.State => s.mem 100) hm,
    congrArg Memory.State.frontier hm, hout 0, hn⟩

-- A concrete maximum-width payload inhabits the uniform memory-client endpoint.
example : ∃ r : ℕ, ∃ prog : Program .exact r, ∃ y : Data r, ∃ pc n : ℕ,
    Runs 4 prog (State.init [1, 15]) ⟨pc, y⟩ n ∧
      step 4 prog ⟨pc, y⟩ = .halt 15 ∧ y.mem 1 = 15 ∧ y.mem 100 = 0 := by
  obtain ⟨r, _, pc, prog, _, _, he⟩ := writeRead_native
  obtain ⟨y, n, hr, hh, hm, _, ht, _⟩ := he 4 15 (by decide) (by decide)
  exact ⟨r, prog, y, pc, n, hr, hh, hm, ht⟩

private theorem zero_realizes :
    Realizes .exact (fun _ : Unit => (pure 0 : Memory.Prog ℕ)) unitWords word
      (fun _ _ _ => True) (fun _ _ => 1) := by
  have h := Realizes.glue unitWords (GlueComputes.const (B := .exact) (P := fun _ => True)
    (bound := fun _ => 0) 0 (fun _ _ => le_rfl))
  exact h.consequence (fun w _ _ _ _ _ => ⟨trivial, fits_zero w⟩) (fun _ _ => le_rfl)

/-- Empty input still installs frontier one, with its neutral copy and halt charged. -/
theorem emptyInput_native : ∃ r C : ℕ, ∃ prog : Program .exact r,
    ∀ w, Fits w 1 → ∃ t, Executes w prog (State.init []) 0 t ∧ t ≤ C * 2 + 1 := by
  obtain ⟨r, C, prog, he⟩ := zero_realizes.exists_standard_init_program (fun _ => [])
    (fun _ i => Fin.elim0 i) 0
  refine ⟨r, C, prog, ?_⟩
  intro w h1
  exact he w () (by decide) h1 ⟨fits_zero w, by simp⟩ trivial (by trivial)

private theorem readHeader_realizes :
    Realizes .exact (fun _ : Unit => Memory.read 1) unitWords word
      (fun w _ _ => Fits w 1) (fun _ _ => 2) := by
  have h := (Realizes.glue unitWords (GlueComputes.const (B := .exact)
    (P := fun _ => True) (bound := fun _ => 1) 1 (fun _ _ => le_rfl))).bind
      (Realizes.read (appendWords unitWords word) 0)
  exact h.consequence (fun _ _ _ _ _ hfit => ⟨⟨trivial, hfit⟩, trivial⟩)
    (fun _ _ => le_rfl)

/-- The graph is runtime memory, while the register argument is only Unit. One fixed program
reads its first header word for every adjacency-list instance, preserving all input memory. -/
theorem graphHeader_native : ∃ r C pc : ℕ, ∃ prog : Program .exact r,
    ∃ frontier result : Fin r,
    ∀ w (G : Cslib.Algorithms.WordRAM.Dijkstra.ListInstance),
      Fits w (G.encode.length + 1) → InputFits w G.encode →
      ∃ y n, Runs w prog (State.init G.encode) ⟨pc, y⟩ n ∧
        step w prog ⟨pc, y⟩ = .halt G.n ∧
        y.mem = (Data.init G.encode : Data 0).mem ∧
        y.regs frontier = G.encode.length + 1 ∧ y.regs result = G.n ∧
        n + 1 ≤ C * 4 + 1 := by
  obtain ⟨r, C, pc, prog, frontier, out, he⟩ :=
    readHeader_realizes.exists_standard_init_program_state_from_words 0
  refine ⟨r, C, pc, prog, frontier, out 0, ?_⟩
  intro w G hw hin
  have hvalid : (Memory.spec w).ValidHistory (inputState G.encode)
      ((Memory.spec w).clientHistory (inputState G.encode) (Memory.read 1)) := by
    change 1 < G.encode.length + 1 ∧ True
    rw [G.encode_length]
    exact ⟨by omega, trivial⟩
  obtain ⟨y, n, hr, hh, hm, hout, hn⟩ := he w () G.encode
    (fun j => Fin.elim0 j) (Nat.zero_le _) hw hin (hw.of_le (by omega)) hvalid
  exact ⟨y, n, hr, hh, congrArg Memory.State.mem hm,
    congrArg Memory.State.frontier hm, hout 0, hn⟩

private def isolatedVertex : Cslib.Algorithms.WordRAM.Dijkstra.ListInstance :=
  ⟨1, fun _ => [], 0⟩

private def maximumEdge : Cslib.Algorithms.WordRAM.Dijkstra.ListInstance :=
  ⟨2, fun u => if u.val = 0 then [(1, 15)] else [], 0⟩

-- Two different graph memories share one program; the maximum fitting edge weight survives.
example : ∃ r pc : ℕ, ∃ prog : Program .exact r, ∃ y₁ y₂ : Data r, ∃ n₁ n₂ : ℕ,
    Runs 4 prog (State.init isolatedVertex.encode) ⟨pc, y₁⟩ n₁ ∧
      Runs 4 prog (State.init maximumEdge.encode) ⟨pc, y₂⟩ n₂ ∧
      step 4 prog ⟨pc, y₁⟩ = .halt 1 ∧ step 4 prog ⟨pc, y₂⟩ = .halt 2 ∧
      y₂.mem 7 = 15 := by
  obtain ⟨r, _, pc, prog, _, _, he⟩ := graphHeader_native
  obtain ⟨y₁, n₁, hr₁, hh₁, _⟩ := he 4 isolatedVertex (by decide) (by decide)
  obtain ⟨y₂, n₂, hr₂, hh₂, hm₂, _⟩ := he 4 maximumEdge (by decide) (by decide)
  exact ⟨r, pc, prog, y₁, y₂, n₁, n₂, hr₁, hr₂, hh₁, hh₂,
    congrFun hm₂ 7⟩

-- No initialized width-zero instance is claimed, even on empty input.
example : ¬Fits 0 (([] : List ℕ).length + 1) := by decide

end Cslib.WordRAM.Realization.Tests.StandardProgram
