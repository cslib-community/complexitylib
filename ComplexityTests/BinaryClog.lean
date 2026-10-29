import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

-- Ceiling logarithms distinguish exact powers from their next integers and handle zero/one.
/-- info: [0, 0, 1, 2, 2, 3, 3, 3, 3, 4] -/
#guard_msgs in
#eval (List.range 10).map (Nat.clog 2)

-- Ceiling logarithms distinguish exact powers from their next integers, handle zero/one, and
-- separate ceiling from floor at non-powers.
example :
    (Nat.clog 2 1024 = 10 ∧ Nat.clog 2 1025 = 11 ∧
      (encNat 1024).length = 11 ∧ (encUnary (Nat.clog 2 1024)).length = 10) ∧
    (2 ^ Nat.clog 2 3 = 4 ∧ 2 ^ Nat.clog 2 4 = 4 ∧
      2 ^ Nat.clog 2 0 = 1 ∧ 2 ^ Nat.clog 2 1 = 1) ∧
    (¬ 3 ≤ 2 ^ Nat.log 2 3 ∧ 3 ≤ 2 ^ Nat.clog 2 3) ∧
    ((encNat (Nat.clog 2 0)).length = 0 ∧ (encNat (Nat.clog 2 1)).length = 0 ∧
      (encNat (Nat.clog 2 1024)).length = 4 ∧ (encNat (Nat.clog 2 1025)).length = 4) := by
  decide

-- Binary-output frontends return `encNat` words and compose cleanly with `binary_two_pow`,
-- `fun_prop`, and `binary_add`.
example :
    ComputableInPolyTime (fun B : ℕ => 2 ^ Nat.clog 2 B) encNat encNat ∧
      ComputableInPolyTime (fun n : ℕ => Nat.clog 2 (Nat.clog 2 n)) encNat encNat ∧
      ComputableInPolyTime (fun p : ℕ × ℕ => Nat.clog 2 (p.1 + p.2))
        (encPair encNat encNat) encNat :=
  ⟨binary_two_pow.comp binary_clog_two, by fun_prop, binary_clog_two_nat' binary_add⟩
