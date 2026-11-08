/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Distributed.Byzantine.OralMessages

/-! Byzantine agreement: a leader protocol that solves the fault-free case and fails against one
equivocating fault, the trivial one-process protocol, the covering lemma for the trivial cover,
concrete equivocation and rushing runs of `om1` on four processes, and instances of the node bound
and of the single-fault characterization. -/

namespace ComplexityTests.Distributed.Byzantine

open Cslib.Distributed.Byzantine

/-! ### A leader protocol -/

/-- Every process adopts the state of process `0` in each round. -/
def leader (n : ℕ) : Protocol (Fin (n + 1)) Bool Bool where
  init _ b := b
  send _ _ s _ := s
  update _ _ _ m := m 0
  output _ s := s

/-- Without faults, everyone decides the leader's input after one round. -/
theorem leader_decision_empty (n : ℕ) (adv : ℕ → Fin (n + 1) → Fin (n + 1) → Bool)
    (x : Fin (n + 1) → Bool) (i : Fin (n + 1)) : (leader n).decision ∅ adv x 1 i = x 0 := by
  simp [Protocol.decision, Protocol.state, leader]

/-- The definition is not vacuous: the leader protocol solves the fault-free problem. -/
theorem leader_solves (n : ℕ) : (leader n).SolvesByzantineAgreement 0 1 where
  agreement F hF adv x i _ j _ := by
    obtain rfl := Finset.card_eq_zero.1 (Nat.le_zero.1 hF)
    rw [leader_decision_empty, leader_decision_empty]
  validity F hF adv x v hv i _ := by
    obtain rfl := Finset.card_eq_zero.1 (Nat.le_zero.1 hF)
    rw [leader_decision_empty]
    exact hv 0 (Finset.notMem_empty 0)

/-- A faulty leader sending `false` to process `1` and `true` to process `2`. -/
def splitLeader : ℕ → Fin 3 → Fin 3 → Bool := fun _ _ i => decide (i = 2)

-- The correct processes `1` and `2` disagree.
example : (leader 2).decision {0} splitLeader (fun _ => false) 1 1 = false ∧
    (leader 2).decision {0} splitLeader (fun _ => false) 1 2 = true := by
  decide

example : ¬ (leader 2).SolvesByzantineAgreement 1 1 := fun h => by
  have := h.agreement {0} (by decide) splitLeader (fun _ => false) 1 (by decide) 2 (by decide)
  revert this
  decide

/-! ### Deciding the own input -/

example : (Protocol.ownInput (Fin 1)).SolvesByzantineAgreement 5 3 :=
  Protocol.solvesByzantineAgreement_ownInput 5 3

-- On two processes, even without faults, different inputs give different decisions.
example : (Protocol.ownInput (Fin 2)).decision ∅ (fun _ _ _ => ()) ![false, true] 3 0 ≠
    (Protocol.ownInput (Fin 2)).decision ∅ (fun _ _ _ => ()) ![false, true] 3 1 := by
  decide

/-! ### The covering lemma for the trivial cover -/

-- Without faults, a run is the run on the network in which every process is its own node.
example {S M : Type} (π : Protocol (Fin 3) S M) (adv : ℕ → Fin 3 → Fin 3 → M)
    (x : Fin 3 → Bool) (r : ℕ) (i : Fin 3) :
    π.state ∅ adv x r i = π.coverState id x (fun _ j => j) r i :=
  π.state_eq_coverState id x _ ∅ adv x id (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ j hj => absurd hj (Finset.notMem_empty j)) r i (Finset.notMem_empty i)

/-! ### `om1` against an equivocating process -/

/-- Process `3` claims input `true` to process `0` and `false` to the others in round 1, and
claims to have received `true` from everyone in round 2. -/
def equivocate : ℕ → Fin 4 → Fin 4 → Fin 4 → Bool :=
  fun r _ i _ => if r = 0 then decide (i = 0) else true

-- Mixed inputs: the estimates are `w = (true, false, true, false)`, a tie, so all correct
-- processes decide `false`.
example : ∀ i : Fin 3, (om1 (Fin 4)).decision {3} equivocate ![true, false, true, false] 2
    i.castSucc = false := by
  decide

-- All correct inputs `true`: the estimate for `3` is `false`, but `w` has three `true` entries.
example : ∀ i : Fin 3, (om1 (Fin 4)).decision {3} equivocate (fun _ => true) 2
    i.castSucc = true := by
  decide

example : (om1 (Fin 4)).SolvesByzantineAgreement 1 2 :=
  solvesByzantineAgreement_om1 (by simp) le_rfl

/-! ### `om1` against a rushing process -/

/-- Process `3` sees the global state before choosing its messages: in round 1 it claims the
negation of the recipient's input, and in round 2 the negation of what the recipient heard from
process `0`. -/
def rushing : ℕ → (Fin 4 → OM1State (Fin 4)) → Fin 4 → Fin 4 → Fin 4 → Bool :=
  fun r σ _ i _ => if r = 0 then !(σ i).input else !((σ i).heard 0)

-- With unanimous inputs `true`, process `3` claims input `false` to process `0` in round 1, yet
-- the correct processes still decide `true`.
example : ((om1 (Fin 4)).adaptiveState {3} rushing (fun _ => true) 1 0).heard 3 = false := by
  decide

example : ∀ i : Fin 3, (om1 (Fin 4)).output i.castSucc
    ((om1 (Fin 4)).adaptiveState {3} rushing (fun _ => true) 2 i.castSucc) = true := by
  decide

-- In general, agreement against `rushing` follows from agreement against fixed tables.
example (x : Fin 4 → Bool) (i j : Fin 4) (hi : i ∉ ({3} : Finset (Fin 4)))
    (hj : j ∉ ({3} : Finset (Fin 4))) :
    (om1 (Fin 4)).output i ((om1 (Fin 4)).adaptiveState {3} rushing x 2 i) =
      (om1 (Fin 4)).output j ((om1 (Fin 4)).adaptiveState {3} rushing x 2 j) :=
  ((solvesByzantineAgreement_om1 (by simp) le_rfl).adaptive (by decide) rushing x).1 i hi j hj

/-! ### The node bound -/

-- Two processes: the middle group of the covering argument is empty.
example {S M : Type} (π : Protocol (Fin 2) S M) (R : ℕ) : ¬ π.SolvesByzantineAgreement 1 R :=
  π.not_solvesByzantineAgreement (by simp) (by simp)

-- Six processes do not tolerate two faults; `om1` on three processes does not tolerate one.
example {S M : Type} (π : Protocol (Fin 6) S M) (R : ℕ) : ¬ π.SolvesByzantineAgreement 2 R :=
  π.not_solvesByzantineAgreement (by simp) (by simp)

example : ¬ (om1 (Fin 3)).SolvesByzantineAgreement 1 2 :=
  Protocol.not_solvesByzantineAgreement_three _ 2

/-! ### The single-fault characterization -/

example : ¬ ∃ (S M : Type) (π : Protocol (Fin 3) S M), π.SolvesByzantineAgreement 1 2 := by
  rw [exists_solvesByzantineAgreement_one_iff 3 le_rfl]
  omega

example : ∃ (S M : Type) (π : Protocol (Fin 7) S M), π.SolvesByzantineAgreement 1 5 :=
  (exists_solvesByzantineAgreement_one_iff 7 (by omega)).2 (Or.inr (by omega))

end ComplexityTests.Distributed.Byzantine
