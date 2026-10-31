/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives

/-! # Direct binary counters: boundary words and independent resource bounds -/

@[expose] public section
open Turing.MultiTapeTM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableTidilyInDegree] do
    if (← Lean.getEnv).contains name then
      throwError "unexpected higher tidy calculus: {name}"

namespace ComplexityTests.Internal.BinaryPrimitives

-- Unbounded carry chains are verified for the actual folds, then specialized to long words.
theorem carryChain (k : ℕ) :
    NatSucc.succFinish ((List.replicate k true).foldl NatSucc.succStep (true, [])) =
      List.replicate k false ++ [true] := by
  rw [NatSucc.succFinish_foldl, List.nil_append]
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [List.replicate_succ, NatSucc.incr, List.cons_append] using
      congrArg (List.cons false) ih

-- Uniform certificates on all natural numbers, carry boundary equations, and independent
-- workspace/output charges.
example (n : ℕ) {f : ℕ → ℕ} {t s T S : ℕ → ℕ}
    (h : ComputableInTimeAndSpace f encNat encNat t s)
    (ht : ∀ n, t n ≤ T n + 1) (hs : ∀ n, s n ≤ S n + 1)
    (hl : ∀ n, (encNat (f n)).length ≤ S n + 1) :
    ComputableInO (· + 1) encNat encNat
      (fun n => ((encNat n).length + 1) ^ 2) (fun n => (encNat n).length + 1) ∧
    ComputableInO (· - 1) encNat encNat
      (fun n => ((encNat n).length + 1) ^ 2) (fun n => (encNat n).length + 1) ∧
    ComputableInO (fun n => decide (n = 0)) encNat encBool
      (fun n => (encNat n).length) (fun n => (encNat n).length) ∧
    (∃ c, ComputableInTimeAndSpace (· - 1) encNat encNat
      (fun n => c * (((encNat n).length + 1) ^ 2 + 1))
      (fun n => c * ((encNat n).length + 1 + 1)) ∧
      ∀ n, (encNat (n - 1)).length ≤ c * ((encNat n).length + 1 + 1)) ∧
    NatSucc.succFinish ([].foldl NatSucc.succStep (true, [])) = [true] ∧
    NatSucc.succFinish ([true].foldl NatSucc.succStep (true, [])) = [false, true] ∧
    NatSucc.incr true [true, true, true] = [false, false, false, true] ∧
    NatSucc.succFinish ((List.replicate 128 true).foldl NatSucc.succStep (true, [])) =
      List.replicate 128 false ++ [true] ∧
    (encNat 0).isEmpty = true ∧
    (encNat 1).isEmpty = false ∧
    encNat (n + 1) = NatSucc.succFinish ((encNat n).foldl NatSucc.succStep (true, [])) ∧
    encNat 0 = [] ∧
    encNat 1 = [true] ∧
    (¬ ComputableInO (fun w : List Bool => w) encBits encBits
      (fun w => (w.length + 1) ^ 2) (fun _ => 0)) ∧
    ComputableInO f encNat encNat T S := by
  refine ⟨.natSucc, .natPred, .natIsZero, ComputableInO.natPred,
    rfl, rfl, rfl, carryChain 128, rfl, rfl,
    by simp only [encNat_apply, NatSucc.succFinish_foldl, List.nil_append, NatSucc.bits_succ],
    rfl, rfl, ?_, ?_⟩
  · rintro ⟨c, _, hl'⟩
    have hlen := hl' (List.replicate (c + 1) true)
    simp only [encBits_apply, List.length_replicate, Nat.zero_add, Nat.mul_one] at hlen
    omega
  · fail_if_success exact ComputableInO.of_bounds h 1 (by simpa using ht) (by simpa using hs)
    exact ComputableInO.of_bounds h 1 (by simpa using ht) (by simpa using hs) (by simpa using hl)

end ComplexityTests.Internal.BinaryPrimitives
