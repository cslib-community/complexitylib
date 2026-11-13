/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Dijkstra.Memory
public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Algorithms.WordRAM.Dijkstra.ListEncode
import CslibFrontier.Computability.WordRAM.Realization.Backend
import CslibFrontier.Tactic.Realize

/-!
# Flat programs from native Dijkstra memory clients

The binary-heap and Fibonacci-heap endpoints both realize a memory program that reads the
adjacency-list input words, and both export it through the standard initialized-program
exporter. `exists_program_state` is that export: a uniform realization, the program's
admissibility and distance outputs, and a bound `c G` on its memory cost give one flat program
whose halting run computes the distances in `O(c G + 1)` steps and ends in the program's final
memory. Each endpoint supplies only its cost bound.

## Main results

* `exists_program_state`: the flat export of a native Dijkstra memory client.
-/

public section

namespace Cslib.Algorithms.Lean.Dijkstra.Native

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Dijkstra (ListInstance)
open Cslib.Algorithms.WordRAM.Dijkstra (encodeDist)

/-- **The flat export of a native Dijkstra memory client.** Let `p` be uniformly realized on the
input words of every graph at every word size that holds `8 (n + m + 2) (W + 2)`, and on those
inputs be admissible, leave the encoded distances at the output cells and cost at most `c G`
memory units. Then one flat exact-basis program, chosen before every graph and word size, halts
within `C (c G + 1)` steps with the encoded distances at the output cells, its final memory and
frontier being those of `p`. The prefix installing the input, the body and the halt are charged. -/
theorem exists_program_state {p : Memory.Prog Unit} (c : ListInstance → ℕ)
    (hp : Realizes .exact (fun _ : Unit => p)
      (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := Unit))
      (fun w _ s => ∃ G : ListInstance, s = Memory.State.init G.encode ∧
        Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) (fun _ _ => 0))
    (hspec : ∀ (G : ListInstance) {w : ℕ},
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) →
      (Memory.spec w).ValidHistory (Memory.State.init G.encode)
          ((Memory.spec w).clientHistory (Memory.State.init G.encode) p) ∧
        (∀ v : Fin G.n, ((Memory.spec w).clientState (Memory.State.init G.encode) p).mem
          (G.outAddr v) = encodeDist (G.dist G.source v)) ∧
        (Memory.spec w).totalCost Memory.charge (Memory.State.init G.encode)
          ((Memory.spec w).clientHistory (Memory.State.init G.encode) p) ≤ c G) :
    ∃ r C pc : ℕ, ∃ prog : Program .exact r, ∃ frontier : Fin r,
      ∀ (G : ListInstance) (w : ℕ), Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) →
        ∃ (y : Data r) (steps : ℕ), Runs w prog (State.init G.encode) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt 0 ∧
          memoryState frontier y = (Memory.spec w).clientState (Memory.State.init G.encode) p ∧
          steps + 1 ≤ C * (c G + 1) ∧
          ∀ v : Fin G.n, y.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  -- Return the word `0`, so that the standard exporter has a result to halt with.
  have hReturn : Realizes .exact (fun _ : Unit × Unit => pure 0)
      (appendWords (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := Unit)))
      (WordEncoding.encode (α := ℕ)) (fun _ _ _ => True) (fun _ _ => 0) := by realize
  have hpReturn : Realizes .exact (fun _ : Unit => do p; pure 0)
      (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := ℕ))
      (fun w _ s => ∃ G : ListInstance, s = Memory.State.init G.encode ∧
        Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) (fun _ _ => 0) := by
    apply (hp.bind₀ hReturn).consequence
    · intro w d s _ _ h
      exact ⟨h, trivial⟩
    · intro _ _
      exact le_rfl
  obtain ⟨r, C, pc, prog, frontier, _, he⟩ :=
    hpReturn.exists_standard_init_program_state_from_words 0
  refine ⟨r, C + 1, pc, prog, frontier, ?_⟩
  intro G w hfit
  obtain ⟨hvalid, hdist, hcost⟩ := hspec G hfit
  have hfront : Fits w (G.encode.length + 1) := by
    rw [G.encode_length]
    exact hfit.of_le (by nlinarith)
  -- The trailing `pure 0` adds no memory operation.
  have hv : (Memory.spec w).ValidHistory (Memory.State.init G.encode)
      ((Memory.spec w).clientHistory (Memory.State.init G.encode) (do p; pure 0)) := by
    simpa only [client_simps, List.append_nil] using hvalid
  obtain ⟨y, steps, hrun, hhalt, hstate, _, htime⟩ :=
    he w () G.encode (fun i => Fin.elim0 i) (Nat.zero_le _) hfront
      (G.inputFits_encode hfit) ⟨G, rfl, hfit⟩ hv
  have hs : (Memory.spec w).clientState (Memory.State.init G.encode) (do p; pure 0) =
      (Memory.spec w).clientState (Memory.State.init G.encode) p := by
    simp only [client_simps]
  have hm : memoryCost (do p; pure 0) (Memory.State.init G.encode) =
      memoryCost p (Memory.State.init G.encode) := by
    simp only [client_simps, Nat.add_zero]
  change memoryState frontier y = (Memory.spec w).clientState (Memory.State.init G.encode)
    (do p; pure 0) at hstate
  rw [hs] at hstate
  change steps + 1 ≤ C * (memoryCost (do p; pure 0)
    (Memory.State.init G.encode) + 0 + 1) + 1 at htime
  rw [hm] at htime
  have hr : (Memory.spec w).clientResult (Memory.State.init G.encode) (do p; pure 0) = 0 := by
    simp only [client_simps]
  rw [hr] at hhalt
  rw [← memoryCost_eq_totalCost w] at hcost
  refine ⟨y, steps, hrun, hhalt, hstate, ?_, ?_⟩
  · nlinarith [Nat.mul_le_mul_left C hcost]
  · intro v
    have hm := congrArg (fun s : Memory.State => s.mem (G.outAddr v)) hstate
    exact hm.trans (hdist v)

end Cslib.Algorithms.Lean.Dijkstra.Native
