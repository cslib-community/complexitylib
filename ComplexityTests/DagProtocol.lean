/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.DagProtocol
import Mathlib.Tactic.FinCases

/-!
# Tests: dag-like protocols and their circuits

Small dag-like protocols for Karchmer–Wigderson games on two bits, and the circuits that
`DagProtocol.Solves.exists_circuit` and `DagProtocol.Solves.exists_monotone_circuit` build from
them.

* `andProtocol` solves the monotone game of `x₀ ∧ x₁` with two inner nodes, where the second
  leads to the first: Bob says whether `y₀ = 0`; if so the answer is `0`, and otherwise the walk
  goes to node `0`, where Bob checks consistency again (`y₀ = 1`) before answering `1`. The walk
  answers `1` on `11` against `10`, and the extracted monotone circuit has at most `20` gates.
* The protocol of the one-gate circuit `x₀ ∧ x₁` (`gateProtocol`), as in the remark after
  Krajíček's Theorem 2.3, solves the same game with one inner node and one bit.
* Answering `0` at once (`zeroProtocol`) does not solve the game: it fails on `11` against `10`.
* The protocol with no inner nodes whose source is the answer `0` solves the game of `¬x₀`, and
  the extracted De Morgan circuit has at most two gates.
-/

namespace ComplexityTests.DagProtocol

open Cslib Cslib.Communication Cslib.Circuits

/-- The inputs where `x₀ ∧ x₁` holds. -/
private def U : Set (BitString 2) := {x | x 0 = true ∧ x 1 = true}

/-- The inputs where `x₀ ∧ x₁` fails. -/
private def V : Set (BitString 2) := {y | y 0 = false ∨ y 1 = false}

/-- The tree protocols of `andProtocol`. At node `1` Bob says whether `y₀ = 0`: if so the answer
is `0`, and otherwise the walk goes to node `0`. At node `0` Bob says whether `y₀ = 0` again: if
so the node is inconsistent, and otherwise the answer is `1`. -/
private def andStep : (j : Fin 2) → Protocol (BitString 2) (BitString 2) (Option (Fin j ⊕ Fin 2))
  | 0 => .bob (fun y => y 0) (.output none) (.output (some (.inr 1)))
  | 1 => .bob (fun y => y 0) (.output (some (.inr 0))) (.output (some (.inl ⟨0, Nat.zero_lt_one⟩)))

/-- A dag-like protocol for the monotone Karchmer–Wigderson game of `x₀ ∧ x₁`, with two inner
nodes and source node `1`. -/
private def andProtocol : DagProtocol (BitString 2) (BitString 2) (Fin 2) 2 :=
  ⟨andStep, .inl 1⟩

/-- Each tree protocol sends one bit. -/
example : andProtocol.depth = 1 := by
  decide

/-- `andProtocol` solves the monotone Karchmer–Wigderson game of `x₀ ∧ x₁`. -/
private theorem andProtocol_solves : andProtocol.Solves ExceedsAt U V := by
  refine ⟨fun x _ y _ => ?_, fun j x hx y hy s hs => ?_⟩
  · change (andStep 1).run x y ≠ none
    cases hy₀ : y 0 <;> simp [andStep, hy₀]
  · obtain ⟨hx₀, hx₁⟩ := hx
    fin_cases j <;> cases hy₀ : y 0 <;>
      simp only [andProtocol, andStep, Protocol.run_bob, Protocol.run_output, hy₀, Bool.cond_false,
        Bool.cond_true, reduceCtorEq, Option.some.injEq] at hs <;> subst hs
    · exact ⟨hx₁, hy.resolve_left (by simp [hy₀])⟩
    · exact ⟨hx₀, hy₀⟩
    · change (andStep 0).run x y ≠ none
      simp [andStep, hy₀]

/-- The walk of `andProtocol` on `11` against `10` goes from node `1` to node `0` and answers `1`,
the coordinate where `11` is one and `10` is zero. -/
example : andProtocol.run ![true, true] ![true, false] = some 1 := by
  obtain ⟨o, ho, hR⟩ := andProtocol_solves.exists_run_eq (x := ![true, true]) (y := ![true, false])
    ⟨rfl, rfl⟩ (Or.inr rfl)
  rw [ho]
  fin_cases o
  · simp at hR
  · rfl

/-- The monotone circuit extracted from `andProtocol` has at most `(2 · 2 + 1) · 4 = 20` gates and
separates the inputs of `x₀ ∧ x₁` from the others. -/
example : ∃ C : Circuit Monotone.signature 2 1, C.size ≤ 20 ∧
    (∀ u ∈ U, C.eval Monotone.interpretation u 0 = true) ∧
    ∀ v ∈ V, C.eval Monotone.interpretation v 0 = false := by
  have h : andProtocol.depth = 1 := by decide
  simpa [h] using andProtocol_solves.exists_monotone_circuit

/-- **The protocol of a circuit**, after the remark following [Krajíček, Theorem 2.3][Krajicek1997]
for the one-gate monotone circuit `x₀ ∧ x₁`: the inner node is the gate, consistent where its value
is one on Alice's input and zero on Bob's, which holds on all of `U × V`; there Bob names an
argument that is zero on his input, and so one on Alice's. -/
private def gateProtocol : DagProtocol (BitString 2) (BitString 2) (Fin 2) 1 :=
  ⟨fun _ => .bob (fun y => y 0) (.output (some (.inr 0))) (.output (some (.inr 1))), .inl 0⟩

/-- The protocol of the one-gate circuit `x₀ ∧ x₁` solves its monotone Karchmer–Wigderson game with
one bit of communication. -/
example : gateProtocol.Solves ExceedsAt U V ∧ gateProtocol.depth = 1 := by
  refine ⟨⟨fun x _ y _ => ?_, fun j x hx y hy s hs => ?_⟩, by decide⟩
  · change (Protocol.bob _ _ _).run x y ≠ none
    cases hy₀ : y 0 <;> simp [hy₀]
  · obtain ⟨hx₀, hx₁⟩ := hx
    change (Protocol.bob _ _ _).run x y = some s at hs
    cases hy₀ : y 0 <;>
      simp only [Protocol.run_bob, Protocol.run_output, hy₀, Bool.cond_false, Bool.cond_true,
        Option.some.injEq] at hs <;> subst hs
    · exact ⟨hx₀, hy₀⟩
    · exact ⟨hx₁, hy.resolve_left (by simp [hy₀])⟩

/-- A protocol answering `0` at once. -/
private def zeroProtocol : DagProtocol (BitString 2) (BitString 2) (Fin 2) 0 :=
  ⟨fun j => j.elim0, .inr 0⟩

/-- Answering `0` at once does not solve the monotone game of `x₀ ∧ x₁`: `11` and `10` agree at
`0`. -/
example : ¬ zeroProtocol.Solves ExceedsAt U V := by
  intro h
  have := h.1 ![true, true] ⟨rfl, rfl⟩ ![true, false] (Or.inr rfl)
  simp [zeroProtocol] at this

/-- The protocol with no inner nodes whose source is the answer `0` solves the Karchmer–Wigderson
game of `¬x₀`, and gives a De Morgan circuit with at most two gates separating `¬x₀` from `x₀`. -/
example : ∃ C : Circuit Boolean.signature 2 1, C.size ≤ 2 ∧
    (∀ u ∈ {x : BitString 2 | x 0 = false}, C.eval Boolean.interpretation u 0 = true) ∧
    ∀ v ∈ {y : BitString 2 | y 0 = true}, C.eval Boolean.interpretation v 0 = false := by
  have h : zeroProtocol.Solves DiffersAt {x | x 0 = false} {y | y 0 = true} :=
    ⟨fun x hx y hy => by simp_all [zeroProtocol], fun j => Fin.elim0 j⟩
  have hd : zeroProtocol.depth = 0 := by decide
  simpa [hd] using h.exists_circuit

end ComplexityTests.DagProtocol
