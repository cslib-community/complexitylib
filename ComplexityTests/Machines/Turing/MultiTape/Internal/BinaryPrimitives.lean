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

-- These are uniform certificates on all natural numbers, not fixed-width counter instances.
example : ComputableInO (· + 1) encNat encNat
    (fun n => ((encNat n).length + 1) ^ 2) (fun n => (encNat n).length + 1) :=
  .natSucc

example : ComputableInO (· - 1) encNat encNat
    (fun n => ((encNat n).length + 1) ^ 2) (fun n => (encNat n).length + 1) :=
  .natPred

example : ComputableInO (fun n => decide (n = 0)) encNat encBool
    (fun n => (encNat n).length) (fun n => (encNat n).length) :=
  .natIsZero

-- The same machine witnesses quadratic time and linear workspace, with a separate output charge.
example : ∃ c, ComputableInTimeAndSpace (· - 1) encNat encNat
    (fun n => c * (((encNat n).length + 1) ^ 2 + 1))
    (fun n => c * ((encNat n).length + 1 + 1)) ∧
    ∀ n, (encNat (n - 1)).length ≤ c * ((encNat n).length + 1 + 1) :=
  ComputableInO.natPred

-- Boundary, carry and borrow behavior of the unchanged word algorithms.
example : NatSucc.succFinish ([].foldl NatSucc.succStep (true, [])) = [true] := rfl
example : NatSucc.succFinish ([true].foldl NatSucc.succStep (true, [])) = [false, true] := rfl
example : NatPred.norm (NatPred.decr []) = [] := rfl
example : NatPred.norm (NatPred.decr [true]) = [] := rfl
example : NatPred.norm (NatPred.decr [false, false, true]) = [true, true] := rfl
example : NatSucc.incr true [true, true, true] = [false, false, false, true] := rfl

-- Unbounded carry/borrow chains are verified for the actual folds, then specialized to long words.
theorem carryChain (k : ℕ) :
    NatSucc.succFinish ((List.replicate k true).foldl NatSucc.succStep (true, [])) =
      List.replicate k false ++ [true] := by
  rw [NatSucc.succFinish_foldl, List.nil_append]
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [List.replicate_succ, NatSucc.incr, List.cons_append] using
      congrArg (List.cons false) ih

theorem borrowChain (k : ℕ) :
    NatPred.norm (NatPred.decr (List.replicate k false ++ [true])) =
      List.replicate k true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, NatPred.decr]
    rw [NatPred.norm_cons (NatPred.decr_ne_nil (by simp)), ih]

example : NatSucc.succFinish ((List.replicate 128 true).foldl NatSucc.succStep (true, [])) =
    List.replicate 128 false ++ [true] := carryChain 128
example : NatPred.norm (NatPred.decr (List.replicate 128 false ++ [true])) =
    List.replicate 128 true := borrowChain 128
example : (encNat 0).isEmpty = true := rfl
example : (encNat 1).isEmpty = false := rfl

-- The bit equations apply to arbitrary sizes and retain zero's empty encoding.
example (n : ℕ) : encNat (n + 1) =
    NatSucc.succFinish ((encNat n).foldl NatSucc.succStep (true, [])) := by
  simp only [encNat_apply, NatSucc.succFinish_foldl, List.nil_append, NatSucc.bits_succ]
example (n : ℕ) : encNat (n - 1) = NatPred.norm (NatPred.decr (encNat n)) :=
  NatPred.bits_pred n
example : encNat 0 = [] := rfl
example : encNat 1 = [true] := rfl

-- A word-copying machine's zero work tapes do not imply constant *charged* workspace.
example : ¬ ComputableInO (fun w : List Bool => w) encBits encBits
    (fun w => (w.length + 1) ^ 2) (fun _ => 0) := by
  rintro ⟨c, _, hl⟩
  have h := hl (List.replicate (c + 1) true)
  simp only [encBits_apply, List.length_replicate, Nat.zero_add, Nat.mul_one] at h
  omega

-- Exact resource packaging cannot fabricate an output charge from workspace alone.
example {f : ℕ → ℕ} {t s T S : ℕ → ℕ}
    (h : ComputableInTimeAndSpace f encNat encNat t s)
    (ht : ∀ n, t n ≤ T n + 1) (hs : ∀ n, s n ≤ S n + 1)
    (hl : ∀ n, (encNat (f n)).length ≤ S n + 1) : ComputableInO f encNat encNat T S := by
  fail_if_success exact ComputableInO.of_bounds h 1 (by simpa using ht) (by simpa using hs)
  exact ComputableInO.of_bounds h 1 (by simpa using ht) (by simpa using hs) (by simpa using hl)

/-- info: 'Turing.MultiTapeTM.ComputableInO.natSucc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableInO.natSucc

/-- info: 'Turing.MultiTapeTM.ComputableInO.natPred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableInO.natPred

/-- info: 'Turing.MultiTapeTM.ComputableInO.natIsZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableInO.natIsZero

end ComplexityTests.Internal.BinaryPrimitives
