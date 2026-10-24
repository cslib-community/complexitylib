/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Hierarchy
import Complexity.Computability.Complexity.Classes.PH.Kannan
import Complexity.Computability.MCSP.Basic

/-!
# Tests for Kannan's theorem

The parameters of Kannan's language on concrete lengths, truth tables read as functions, the `Σ₃`
verifier on concrete certificates, non-vacuity of the circuit classes the theorem escapes, and axiom
checks for the headline results.
-/

namespace Cslib.Complexity.Tests.Kannan

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Turing.MultiTapeTM

/-! ### Parameters -/

-- At length `3`, `k = 0` asks for hard functions of `3 (⌊log₂ 4⌋ + 1) = 9` inputs, with more than
-- `4` gates.
example : Kannan.arity 0 3 = 9 := by decide
example : Kannan.threshold 0 3 = 4 := rfl
example : Kannan.arity 1 7 = 16 := by decide
example : Kannan.threshold 1 2 = 9 := rfl
example : Kannan.tableBound 0 0 = 8 := rfl
example : Kannan.certBound 0 0 = 16 := rfl

/-! ### Truth tables -/

-- Truth tables are indexed by the input read least significant bit first.
example : MCSP.tableFunction 2 [false, true, true, false] ![true, false] = true := by decide
example : MCSP.tableFunction 2 [false, true, true, false] ![true, true] = false := by decide
example : Kannan.table 0 0 (List.replicate 10 true) = List.replicate 8 true := by decide

-- GapMCSP bundles `GapMCSP.yes`, `GapMCSP.no`, and `GapMCSP.disjoint_yes_no` as a `PromiseProblem`.
example (s : ℕ → ℕ) (n : ℕ) :
    GapMCSP s s n le_rfl = PromiseProblem.ofSet (GapMCSP.yes s n) := by simp

example : BitString.binaryValue [true, false, true] = 5 := by decide
example {u v : List Bool} (hlen : u.length = v.length)
    (h : BitString.binaryValue u = BitString.binaryValue v) : u = v :=
  BitString.binaryValue_injective_of_length_eq hlen h

/-! ### The `Σ₃` verifier -/

/-- The truth table on three inputs that is `true` only on the all-`false` input. -/
def T₀ : List Bool := true :: List.replicate 7 false

/-- The certificate of the constant-`false` circuit on three inputs: one constant gate, output
wire `3`. -/
def falseCertificate : List Bool := certificate 3 1 [(.const false, [])] 3

example : falseCertificate.length = Kannan.certBound 0 0 := rfl

-- On the empty input, `T₀` gives `true`. The second block holds the earlier constant-`false` table
-- and a certificate that is not a circuit for `T₀`, and the third block is a circuit for the
-- earlier table, so the verifier accepts.
example : Kannan.verifier 0 ([], T₀ ++ (List.replicate 8 false ++ List.replicate 16 false) ++
    falseCertificate) = true := by decide

-- Without a circuit for the earlier table, the verifier rejects.
example : Kannan.verifier 0 ([], T₀ ++ (List.replicate 8 false ++ List.replicate 16 false) ++
    List.replicate 16 false) = false := by decide

/-! ### Non-vacuity -/

/-- The classes that Kannan's theorem escapes are not empty: the empty language has circuits of
one gate. -/
theorem zero_mem_SIZE {c : ℕ} (hc : 1 ≤ c) (k : ℕ) :
    (0 : Language Bool) ∈ SIZE fun n => c * (n + 1) ^ k := by
  intro n
  have : (0 : Language Bool).slice n = fun _ => false := by
    funext x
    simp [Language.slice]
  rw [this, complexity_const]
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (Nat.succ_ne_zero n)))

-- First hard truth tables exist at all large lengths.
example (k : ℕ) : ∀ᶠ n in Filter.atTop, ∃ T, Kannan.IsFirstHard k n T :=
  (Kannan.eventually_exists_isHard k).mono fun _ => Kannan.exists_isFirstHard

example : (Kannan.language 2 : Set (List Bool)) ∈ PH encBits :=
  SigmaP_subset_PH 3 (Kannan.language_mem_SigmaP_three 2)

example (c : ℕ) : Kannan.language 2 ∉ SIZE fun n => c * (n + 1) ^ 2 :=
  Kannan.language_notMem_SIZE 2 c

-- No polynomial budget of a fixed degree holds all of `Σ₂`.
example (k c : ℕ) : ¬∀ L : Language Bool, (L : Set (List Bool)) ∈ SigmaP 2 encBits →
    L ∈ SIZE fun n => c * (n + 1) ^ k := fun h =>
  let ⟨L, hL, hS⟩ := exists_mem_SigmaP_two_notMem_SIZE k
  hS c (h L hL)

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.mem_NP_image' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.mem_NP_image

/--
info: 'Cslib.Complexity.image_SAT_mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.image_SAT_mem_NP

/--
info: 'Cslib.MCSP.mem_of_verifier_eq_true' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.MCSP.mem_of_verifier_eq_true

/--
info: 'Cslib.MCSP.exists_verifier_append' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.MCSP.exists_verifier_append

/--
info: 'Cslib.MCSP.computableInPolyTime_tableVerifier' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.computableInPolyTime_tableVerifier

/--
info: 'Cslib.MCSP.complexity_le_of_tableVerifier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.MCSP.complexity_le_of_tableVerifier

/--
info: 'Cslib.MCSP.exists_tableVerifier_append' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.MCSP.exists_tableVerifier_append

/--
info: 'Cslib.GapMCSP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.GapMCSP

/--
info: 'Cslib.Complexity.Kannan.language_notMem_SIZE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.Kannan.language_notMem_SIZE

/--
info: 'Cslib.Complexity.Kannan.language_mem_SigmaP_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.Kannan.language_mem_SigmaP_three

/--
info: 'Cslib.Complexity.exists_mem_SigmaP_two_notMem_SIZE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.exists_mem_SigmaP_two_notMem_SIZE

end Cslib.Complexity.Tests.Kannan
