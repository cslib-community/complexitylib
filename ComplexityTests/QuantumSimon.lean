/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.QueryComplexity.Quantum.Simon

/-! Simon's problem: promise instances and failures, nonvacuity of the hypotheses of the classical
lower bound, and Simon's algorithm on concrete inputs with `n = 1`. -/

namespace ComplexityTests.QuantumSimon

open Cslib Cslib.Quantum Cslib.QueryComplexity Finset

/-! ### The promise -/

-- With `n = 1` the constant function hides `s = 1`, and the identity hides `s = 0`.
example : SimonPromise (fun (_ : Fin 1 → Bool) => (0 : Fin 1 → Bool)) (fun _ => true) := by
  unfold SimonPromise
  decide

example : SimonPromise (id : (Fin 1 → Bool) → Fin 1 → Bool) 0 :=
  (simonPromise_zero_iff _).mpr Function.injective_id

-- A function with three equal values satisfies the promise for no hidden string.
/-- `f(a) = a₀ ∧ a₁`, which takes the value `0` three times. -/
def and2 (a : Fin 2 → Bool) : Fin 2 → Bool := fun _ => a 0 && a 1

example : ∀ s, ¬SimonPromise and2 s := by
  unfold SimonPromise and2
  decide

-- The hidden string is unique.
example {f : (Fin 3 → Bool) → Fin 3 → Bool} {s s' : Fin 3 → Bool} (h : SimonPromise f s)
    (h' : SimonPromise f s') : s = s' :=
  h.eq h'

-- Every hard input satisfies the promise.
example {N n : ℕ} (E : Fin N ≃ (Fin n → Bool) × Fin n) (π : Equiv.Perm (Fin n → Bool))
    (s : Fin n → Bool) : SimonPromise (simonFun E (simonHard E π s)) s :=
  simonPromise_simonHard E π s

/-! ### Nonvacuity of the classical lower bound

The total function "some nonzero hidden string exists" answers Simon's problem on the promise
inputs, and some randomized decision tree computes it with error `1/3`; so the hypotheses of the
lower bound are satisfiable for every `n`. -/

/-- The total function deciding whether `f` hides a nonzero string. -/
noncomputable def hidesNonzero {N n : ℕ} (E : Fin N ≃ (Fin n → Bool) × Fin n)
    (X : Fin N → Bool) : Bool := by
  classical
  exact decide (∃ s, s ≠ 0 ∧ SimonPromise (simonFun E X) s)

theorem hidesNonzero_spec {N n : ℕ} (E : Fin N ≃ (Fin n → Bool) × Fin n) (X : Fin N → Bool)
    (s : Fin n → Bool) (hX : SimonPromise (simonFun E X) s) :
    hidesNonzero E X = decide (s ≠ 0) := by
  classical
  unfold hidesNonzero
  by_cases hs : s = 0
  · simp only [hs, ne_eq, not_true_eq_false, decide_false, decide_eq_false_iff_not]
    rintro ⟨s', hs', h'⟩
    exact hs' ((hX.eq h').symm.trans hs)
  · simp only [hs, ne_eq, not_false_eq_true, decide_true, decide_eq_true_eq]
    exact ⟨s, hs, hX⟩

example {N n : ℕ} (E : Fin N ≃ (Fin n → Bool) × Fin n) :
    ∃ μ : RandomizedDecisionTree (Fin N) Bool,
      ∀ X s, SimonPromise (simonFun E X) s → μ.errorProb (hidesNonzero E) X ≤ 1 / 3 := by
  obtain ⟨μ, hμ, -⟩ :=
    exists_computes_depth_eq_randomizedComplexity (ε := 1 / 3) (by norm_num) (hidesNonzero E)
  exact ⟨μ, fun X _ _ => hμ X⟩

-- So every such tree has depth at least `2^{n/2}`, and `R_{1/3}` of this total function too.
example {N n : ℕ} (E : Fin N ≃ (Fin n → Bool) × Fin n) (hn : 1 ≤ n) :
    2 ^ n ≤ randomizedComplexity (1 / 3) (hidesNonzero E) ^ 2 :=
  simon_two_pow_le_randomizedComplexity_sq E _ (hidesNonzero_spec E) hn

/-! ### Simon's algorithm with `n = 1`

The `N = 2` output bits of `f : {0,1} → {0,1}` are indexed by `E`. -/

/-- The positions of the truth table with `n = 1`. -/
noncomputable def E1 : Fin 2 ≃ (Fin 1 → Bool) × Fin 1 :=
  Fintype.equivOfCardEq (by simp)

-- The constant function hides `s = 1`: Simon's algorithm accepts its truth table with certainty.
example (m : ℕ) :
    measureProb (run (simonAlg m E1 0) (simonInit 0)
      (simonInput E1 fun _ => (0 : Fin 1 → Bool)) (m * 1)) (simonAccept m 1) = 1 := by
  refine measureProb_simonAlg_of_ne_zero E1 0 (s := fun _ => true) ?_ ?_
  · rw [simonFun_simonInput]
    unfold SimonPromise
    decide
  · decide

-- The identity is injective: with `3` rounds, acceptance has probability at most `1/8`.
example :
    measureProb (run (simonAlg 3 E1 0) (simonInit 0) (simonInput E1 id) (3 * 1))
      (simonAccept 3 1) ≤ 1 / 8 := by
  refine (measureProb_simonAlg_le_of_injective E1 0 ?_).trans_eq (by norm_num)
  rw [simonFun_simonInput]
  exact Function.injective_id

-- The specification and both forms of the separation at `n = 1`.
example : ‖(simonInit 0 : State 2 (SimonWork 3 1))‖ = 1 := (simonAlg_spec E1 0).1

example : (1 + 2) * 1 ≤ 3 * Nat.log 2 2 ^ 2 := (simon_separation_inputLength E1 0 le_rfl).2.1

end ComplexityTests.QuantumSimon
