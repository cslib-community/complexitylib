/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Complexity.Problems.TMSAT
import CslibFrontier.Computability.Complexity.Problems.Hamiltonian.AnyEndpoints
import CslibFrontier.Logics.Propositional.CNF.TruthTable

/-! Arora–Barak draft, Chapter 2: TMSAT (Theorem 2.9) with a concrete accepted instance and the
rejection of every instance with step bound zero; the truth-table CNF (Claim 2.14) of a concrete
function and its size bound; and directed Hamiltonian paths without given endpoints
(Theorem 2.18), with concrete members, the empty-graph convention and the reduction. -/

namespace CslibFrontierTests.AroraBarakChapterTwo

open Cslib Cslib.Complexity Cslib.Logic.PL Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-! ### TMSAT -/

/-- Halt at once, emitting the symbol `1` (`eBit true`), whatever the input head reads. -/
def acceptAct : Act := ⟨0, [], some 1, none⟩

/-- A machine with no work tapes that accepts every input in one step. -/
def acceptDesc : Desc :=
  ⟨0, 0, [(⟨0, none, []⟩, acceptAct), (⟨0, some 0, []⟩, acceptAct), (⟨0, some 1, []⟩, acceptAct)]⟩

/-- The accepting machine accepts `⟨[true], u⟩` within one step for a two-bit witness. -/
example : (⟨acceptDesc, [true], 2, 1⟩ : TMSATInstance) ∈ TMSAT :=
  ⟨[false, true], rfl, by unfold TMSATInstance.Accepts; decide⟩

/-- With the step bound zero, no machine accepts: it has not halted. -/
example (d : Desc) (x : List Bool) (n : ℕ) : (⟨d, x, n, 0⟩ : TMSATInstance) ∉ TMSAT := by
  rintro ⟨u, -, h⟩
  exact Bool.false_ne_true (congrArg Prod.snd h)

/-- TMSAT is `NP`-complete, so `SAT` reduces to it. -/
example : PolyTimeReducible encCNF encTMSATInstance SAT TMSAT :=
  TMSAT.npHard encCNF SAT SAT.mem_NP

example : NPComplete encTMSATInstance TMSAT := TMSAT.npComplete

/-! ### The truth-table CNF -/

/-- The truth-table CNF of the two-variable exclusive or computes it. -/
example (σ : Fin 2 → Bool) :
    (CNF.ofTruthTable fun v : Fin 2 → Bool => v 0 ^^ v 1).eval σ = (σ 0 ^^ σ 1) :=
  CNF.eval_ofTruthTable _ σ

/-- Every function of three variables has a CNF with at most `3 * 2 ^ 3 = 24` AND/OR symbols. -/
example (f : (Fin 3 → Bool) → Bool) :
    ∃ φ : CNF (Fin 3), (∀ σ, φ.eval σ = f σ) ∧ φ.connectiveCount ≤ 24 :=
  CNF.exists_eval_eq_connectiveCount_le f

/-- The size measure: two clauses of two and three literals have `1 + 2` ORs and one AND. -/
example : CNF.connectiveCount ([[(0, true), (1, false)], [(0, false), (1, true), (2, true)]] :
    CNF ℕ) = 4 := rfl

/-! ### Hamiltonian paths without given endpoints -/

/-- The path `0 → 1 → 2` is a Hamiltonian path. -/
example : (⟨[0, 1, 2], [(0, 1), (1, 2)]⟩ : Graph) ∈ DirHamPathAny :=
  ⟨[0, 1, 2], by decide, by simp, by simp, by simp⟩

/-- Empty-graph convention: a graph without declared vertices has no Hamiltonian path. -/
example : (⟨[], []⟩ : Graph) ∉ DirHamPathAny :=
  DirHamPathAny.notMem_of_vertices_eq_nil rfl

/-- Two vertices without arcs have no Hamiltonian path. -/
example : (⟨[0, 1], []⟩ : Graph) ∉ DirHamPathAny := by
  rintro ⟨p, hnd, hcov, -, hch⟩
  match p, hnd, hcov, hch with
  | [], _, hcov, _ => simpa using (hcov 0).2 (by simp)
  | [a], _, hcov, _ =>
    have h0 := (hcov 0).2 (by simp)
    have h1 := (hcov 1).2 (by simp)
    simp only [List.mem_singleton] at h0 h1
    omega
  | _ :: _ :: _, _, _, hch => simp at hch

/-- The reduction from designated endpoints. -/
example : PolyTimeReducible encPathInstance encGraph DirHamPath DirHamPathAny :=
  polyTimeReducible_DirHamPath_DirHamPathAny

example : NPComplete encGraph DirHamPathAny := DirHamPathAny_npComplete

end CslibFrontierTests.AroraBarakChapterTwo
