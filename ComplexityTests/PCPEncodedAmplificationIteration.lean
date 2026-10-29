/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Encoded.Amplification.Iteration
import Complexity.Tactic.PolyTime

/-! Complete encoding bounds and certificate inference for normalized amplification loops. -/

namespace ComplexityTests.PCPEncodedAmplificationIteration

open Cslib Cslib.PCP Cslib.PCP.Encoded Cslib.PCP.HadamardTester Turing.MultiTapeTM

local notation "Alphabet" => (Bool × (Fin 6 → Bool))
local notation "Constraint" => (Alphabet → Alphabet → Bool)

variable {D Input : Type} [Fintype D] [DecidableEq D] {width : ℕ}
  {input : Input ↪ List Bool} {label : D ↪ List Bool} {graph : Input → Graph Constraint}
  (hgraph : ComputableInPolyTime graph input (Graph.encoding (encPi (encPi encBool))))
  (hwellFormed : ∀ x, (graph x).WellFormed)
  (family : (n : ℕ) → RotationMap (Fin n) D) (rotate : ℕ × (ℕ × D) → ℕ × D)
  (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
    (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
  (hcost : ComputableInPolyTime rotate
    (encPair encUnary (encPair encUnary label)) (encPair encUnary label))
  (fallback : Constraint) (T q : ℕ) [NeZero q] (walks : List (Graph.PowerLabel D T q))
  (number : Graph.SelectedComposeSlot (Graph.PowerAlphabet D Alphabet T) ≃ Fin width)
  (coins : List (Fin 5 × Rand (Graph.PowerAlphabet D Alphabet T))) (queries : List (Fin 6))

example : ComputableInPolyTime
    (fun x => Graph.amplifyIter fallback rotate T q walks number coins queries
      (Nat.clog 2 (graph x).edges.length) (graph x))
    input (Graph.encoding (encPi (encPi encBool))) := by
  fail_if_success (clear hcost; fun_prop)
  fail_if_success (clear hgraph; fun_prop)
  fun_prop

example : ComputableInPolyTime (fun x =>
    let g := graph x
    Graph.amplifyIter fallback rotate T q walks number coins queries (Nat.clog 2 g.edges.length) g)
    input (Graph.encoding (encPi (encPi encBool))) := by
  fail_if_success (clear hcost; polytime)
  fail_if_success (clear hgraph; polytime)
  polytime

example (g : Graph Constraint) :
    Graph.amplifyIter fallback rotate T q walks number coins queries 0 g = g := by
  unfold Graph.amplifyIter
  rfl

end ComplexityTests.PCPEncodedAmplificationIteration
