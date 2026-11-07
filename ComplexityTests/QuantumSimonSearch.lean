/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.QueryComplexity.Quantum.SimonSearch

/-! The search version of Simon's problem: the classical post-processing on concrete row matrices,
the fiber bound, Simon's algorithm on concrete inputs with `n = 1`, and nonvacuity of the
hypotheses of the classical search lower bound. -/

namespace ComplexityTests.QuantumSimonSearch

open Cslib Cslib.Quantum Cslib.QueryComplexity Finset

/-! ### The post-processing -/

/-- The row matrix with rows `10` and `01`, which span `{0,1}^2`. -/
def zsSpan : Fin 2 × Fin 2 → Bool := fun k => decide (k.1 = k.2)

/-- The row matrix with the single row `11`, orthogonal to `00` and `11`. -/
def zsOne : Fin 1 × Fin 2 → Bool := fun _ => true

-- Spanning rows determine `s = 0`, so the post-processing outputs `0`.
example : SimonDetermines zsSpan 0 := by
  unfold SimonDetermines zsSpan
  decide

example : simonSolve zsSpan = 0 :=
  simonSolve_eq (by unfold SimonDetermines zsSpan; decide)

-- The row `11` determines `s = 11`, and the post-processing outputs it.
example : SimonDetermines zsOne (fun _ => true) := by
  unfold SimonDetermines zsOne
  decide

example : simonSolve zsOne = fun _ => true :=
  simonSolve_eq (by unfold SimonDetermines zsOne; decide)

-- The row `11` does not determine `s = 0`, and no rows determine anything when `n = 2`.
example : ¬SimonDetermines zsOne 0 := by
  unfold SimonDetermines zsOne
  decide

example (s : Fin 2 → Bool) : ¬SimonDetermines (fun _ : Fin 0 × Fin 2 => false) s := by
  unfold SimonDetermines
  revert s
  decide

/-! ### The fiber bound -/

-- With `n = 1` the constant function hides `s = 1`: each row has two preimages, so each fiber of
-- the rowwise function has at most `2^m` elements.
example {N m : ℕ} (E : Fin N ≃ (Fin 1 → Bool) × Fin 1) (X : Fin N → Bool)
    (hX : SimonPromise (simonFun E X) fun _ => true) (ys : Fin m × Fin 1 → Bool) :
    #{a | simonG (m := m) E X a = ys} ≤ 2 ^ m :=
  card_simonG_fiber_le hX ys

/-! ### Simon's algorithm with `n = 1` -/

/-- The positions of the truth table with `n = 1`. -/
noncomputable def E1 : Fin 2 ≃ (Fin 1 → Bool) × Fin 1 :=
  Fintype.equivOfCardEq (by simp)

-- The constant function hides `s = 1`: with `3` rounds the algorithm finds it with probability
-- above `3/4`.
example :
    3 / 4 < measureProb (run (simonAlg 3 E1 0) (simonInit 0)
      (simonInput E1 fun _ => (0 : Fin 1 → Bool)) ((1 + 2) * 1)) (simonFound 3 fun _ => true) := by
  refine (simonAlg_search_spec E1 0).2 _ _ ?_
  rw [simonFun_simonInput]
  unfold SimonPromise
  decide

-- The identity hides `s = 0`: the algorithm finds `0` with probability above `3/4`, and with `m`
-- rounds with probability at least `1 - 1/2^m`.
example :
    3 / 4 < measureProb (run (simonAlg 3 E1 0) (simonInit 0) (simonInput E1 id) ((1 + 2) * 1))
      (simonFound 3 0) := by
  refine (simonAlg_search_spec E1 0).2 _ _ ?_
  rw [simonFun_simonInput]
  exact (simonPromise_zero_iff _).mpr Function.injective_id

example (m : ℕ) :
    1 - 1 / 2 ^ m ≤ measureProb (run (simonAlg m E1 0) (simonInit 0) (simonInput E1 id) (m * 1))
      (simonFound m 0) := by
  have h := measureProb_simonFound (m := m) E1 0 (s := 0) (by
    rw [simonFun_simonInput]
    exact (simonPromise_zero_iff _).mpr Function.injective_id)
  norm_num at h ⊢
  exact h

/-! ### Nonvacuity of the classical search lower bound

The total function returning the hidden string finds it on every promise input, and some
randomized decision tree computes it with error `1/3`; so the hypotheses of the lower bound are
satisfiable for every `n`. -/

/-- The total function returning the hidden string of `f`, or `0` if there is none. -/
noncomputable def hiddenString {N n : ℕ} (E : Fin N ≃ (Fin n → Bool) × Fin n)
    (X : Fin N → Bool) : Fin n → Bool := by
  classical
  exact if h : ∃ s, SimonPromise (simonFun E X) s then h.choose else 0

theorem hiddenString_spec {N n : ℕ} (E : Fin N ≃ (Fin n → Bool) × Fin n) (X : Fin N → Bool)
    (s : Fin n → Bool) (hX : SimonPromise (simonFun E X) s) : hiddenString E X = s := by
  have h : ∃ s, SimonPromise (simonFun E X) s := ⟨s, hX⟩
  simp only [hiddenString, h, dite_true]
  exact h.choose_spec.eq hX

example {N n : ℕ} (E : Fin N ≃ (Fin n → Bool) × Fin n) :
    ∃ μ : RandomizedDecisionTree (Fin N) (Fin n → Bool),
      ∀ X s, SimonPromise (simonFun E X) s → μ.errorProb (hiddenString E) X ≤ 1 / 3 := by
  obtain ⟨μ, hμ, -⟩ :=
    exists_computes_depth_eq_randomizedComplexity (ε := 1 / 3) (by norm_num) (hiddenString E)
  exact ⟨μ, fun X _ _ => hμ X⟩

-- So every such tree has depth at least `2^{n/2}`, and `R_{1/3}` of this total function too.
example {N n : ℕ} (E : Fin N ≃ (Fin n → Bool) × Fin n) (hn : 1 ≤ n) :
    2 ^ n ≤ randomizedComplexity (1 / 3) (hiddenString E) ^ 2 := by
  obtain ⟨μ, hμ, hd⟩ :=
    exists_computes_depth_eq_randomizedComplexity (ε := 1 / 3) (by norm_num) (hiddenString E)
  rw [← hd]
  exact simon_search_two_pow_le_depth_sq E μ _ (hiddenString_spec E) (fun X _ _ => hμ X) hn

/-! ### Post-processing randomized decision trees -/

-- Relabelling the leaves of a deterministic tree keeps its depth and error.
example {ι β γ : Type*} (g : β → γ) (t : DecisionTree ι β) :
    (RandomizedDecisionTree.mapOutput g (Convexity.StdSimplex.single t)).depth ≤ t.depth := by
  simpa using RandomizedDecisionTree.depth_mapOutput_le g (Convexity.StdSimplex.single t)

end ComplexityTests.QuantumSimonSearch
