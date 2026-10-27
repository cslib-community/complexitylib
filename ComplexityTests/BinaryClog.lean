import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

-- Ceiling logarithms distinguish exact powers from their next integers and handle zero/one.
/-- info: [0, 0, 1, 2, 2, 3, 3, 3, 3, 4] -/
#guard_msgs in
#eval (List.range 10).map (Nat.clog 2)

example : Nat.clog 2 1024 = 10 ∧ Nat.clog 2 1025 = 11 ∧
    (encNat 1024).length = 11 ∧ (encUnary (Nat.clog 2 1024)).length = 10 := by decide

-- A caller can construct the next dyadic bound with a binary input and full binary output.
example : ComputableInPolyTime (fun B : ℕ => 2 ^ Nat.clog 2 B) encNat encNat :=
  binary_two_pow.comp binary_clog_two

example : 2 ^ Nat.clog 2 3 = 4 ∧ 2 ^ Nat.clog 2 4 = 4 ∧
    2 ^ Nat.clog 2 0 = 1 ∧ 2 ^ Nat.clog 2 1 = 1 := by decide

-- Replacing the ceiling by the floor misses the first sufficient power at a non-power input.
example : ¬ 3 ≤ 2 ^ Nat.log 2 3 ∧ 3 ≤ 2 ^ Nat.clog 2 3 := by decide
