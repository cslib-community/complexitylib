/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.ValiantVazirani
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Probability.Isolation

/-! Unique satisfiability, the Valiant–Vazirani reduction on concrete formulas, `RP` relative to
an oracle, asking lists of words, the isolation lemma on a concrete family, and axiom guards. -/

namespace ComplexityTests.Isolation

open Cslib Cslib.Complexity Cslib.Logic.PL Cslib.Probability Turing.MultiTapeTM

/-! ### Unique satisfiability -/

/-- The formula `x₀` is uniquely satisfiable. -/
example : ([[(0, true)]] : CNF ℕ) ∈ USAT := by
  refine ⟨fun _ => true, rfl, fun τ hτ v hv => ?_⟩
  simp only [CNF.vars, List.flatten_cons, List.flatten_nil, List.append_nil, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
  subst hv
  simpa using hτ

/-- The empty formula has no variables, so it is uniquely satisfiable. -/
example : ([] : CNF ℕ) ∈ USAT := ⟨fun _ => false, rfl, fun _ _ _ hv => by simp [CNF.vars] at hv⟩

/-- `x₀ ∨ x₁` has three satisfying assignments of its variables. -/
example : ([[(0, true), (1, true)]] : CNF ℕ) ∉ USAT := by
  rintro ⟨σ, -, h⟩
  have h₀ := h (fun v => v == 0) rfl 0 (by simp [CNF.vars])
  have h₁ := h (fun v => v == 1) rfl 0 (by simp [CNF.vars])
  exact absurd (h₀.trans h₁.symm) (by decide)

/-- `x₀ ∧ ¬x₀` is a no-instance of `PromiseUSAT`. -/
example : ([[(0, true)], [(0, false)]] : CNF ℕ) ∈ PromiseUSAT.no := by
  rintro ⟨σ, hσ⟩
  cases h : σ 0 <;> simp [h] at hσ

example : PromiseUSAT ∈ PromiseNP encCNF := PromiseUSAT_mem_PromiseNP

/-! ### The reduction on concrete formulas -/

open ValiantVazirani

/-- With no random bits, no equation is added. -/
example : reduce ([[(0, true)]], []) = [[(0, true)]] := by decide

/-- The selector bits `01` ask for one equation, read from the remaining bits `1b`: its coefficient
is `1` and its offset `b`. One unit clause fixes the offset, one forces the parity to vanish, and
four clauses relate the parity variables. -/
example : (reduce ([[(0, true)]], [false, true, true, true])).length = 7 := by decide

/-- The selector bits `01` and the equation `x₀ + 1 = 0`: auxiliary variables `1` and `3` carry
the parities. -/
example : reduce ([[(0, true)]], [false, true, true, true]) =
    [[(0, true)], [(1, true)], [(3, false)], [(3, false), (1, true), (0, true)],
      [(3, false), (1, false), (0, false)], [(3, true), (1, false), (0, true)],
      [(3, true), (1, true), (0, false)]] := by
  decide

/-- The equation `x₀ + 1 = 0` keeps the solution `x₀ = 1`. -/
example : CNF.Satisfiable (reduce ([[(0, true)]], [false, true, true, true])) :=
  ⟨fun v => decide (v ∈ [0, 1]), by decide⟩

/-- The equation `x₀ = 0` excludes the only solution. -/
example : ¬CNF.Satisfiable (reduce ([[(0, true)]], [false, true, true, false])) := by
  rw [show reduce ([[(0, true)]], [false, true, true, false]) =
    [[(0, true)], [(1, false)], [(3, false)], [(3, false), (1, true), (0, true)],
      [(3, false), (1, false), (0, false)], [(3, true), (1, false), (0, true)],
      [(3, true), (1, true), (0, false)]] by decide]
  rintro ⟨σ, hσ⟩
  cases h₀ : σ 0 <;> cases h₁ : σ 1 <;> cases h₃ : σ 3 <;>
    simp [h₀, h₁, h₃] at hσ

/-- The affine hash family of bit strings is pairwise independent, agrees with the general
`affineHash` over `Bool`, and words of three bits represent `5`. -/
example (p : (Fin 2 → BitString 3) × BitString 2) (x : BitString 3) :
    IsPairwiseIndependentHash (BitString.LinearHash.affineHash (k := 2) (n := 3)) ∧
    BitString.LinearHash.affineHash p x = affineHash (m := Fin 2) (n := Fin 3) (F := Bool) p x ∧
    (∃ u : Fin 3 → Bool, BitString.binaryValue (List.ofFn u) = 5) :=
  ⟨BitString.LinearHash.isPairwiseIndependentHash_affineHash 2 3,
   BitString.LinearHash.affineHash_eq_affineHash p x,
   BitString.exists_binaryValue_eq (by norm_num)⟩

open Classical in
/-- The success bound (both cardinality and density) for the satisfiable formula `x₀`: at least a
`3 / 128` fraction of the random words of any length `m ≥ randomBits [[x₀]]` give a uniquely
satisfiable formula. -/
example (m : ℕ) (hm : randomBits [[(0, true)]] ≤ m) :
    randomBits [[(0, true)]] = 8 ∧
    3 * 2 ^ m ≤ 32 * 4 * (Finset.univ.filter fun r : Fin m → Bool =>
      reduce ([[(0, true)]], List.ofFn r) ∈ USAT).card ∧
    3 / (32 * (1 + 3)) ≤ Finset.dens (Finset.univ.filter fun r : Fin m → Bool =>
      reduce ([[(0, true)]], List.ofFn r) ∈ USAT) :=
  ⟨by decide,
   three_mul_two_pow_le_card_reduce_mem_USAT (φ := [[(0, true)]]) ⟨fun _ => true, rfl⟩ hm,
   three_div_le_dens_reduce_mem_USAT (φ := [[(0, true)]]) ⟨fun _ => true, rfl⟩ hm⟩

/-- An unsatisfiable formula stays unsatisfiable. -/
example (r : List Bool) : reduce ([[(0, true)], [(0, false)]], r) ∈ UNSAT := by
  refine reduce_mem_UNSAT (fun ⟨σ, hσ⟩ => ?_) r
  cases h : σ 0 <;> simp [h] at hσ

/-! ### Oracle classes -/

/-- `queryAny` asks every word and accepts when one is in the oracle. -/
example : OracleComp.interpret (m := Id) (languageOracle {[true]}) (queryAny [[false], [true]]) =
    true := by
  classical
  rw [interpret_queryAny]
  simp

example : OracleComp.interpret (m := Id) (languageOracle {[true]}) (queryAny [[false]]) =
    false := by
  classical
  rw [interpret_queryAny]
  simp

/-- `SAT` is in `RP` relative to `USAT`, by Valiant–Vazirani. -/
example : SAT ∈ RPWithOracle (encCNF '' USAT) encCNF :=
  NP_subset_RPWithOracle_USAT encCNF SAT.mem_NP

/-- `SAT` is in `RP` relative to `PromiseUSAT`. -/
example : SAT ∈ RPWithPromiseOracle PromiseUSAT encCNF encCNF :=
  NP_subset_RPWithPromiseOracle_PromiseUSAT encCNF SAT.mem_NP

/-- `RP` relative to an oracle lies in `NP` relative to it. -/
example (A : Set (List Bool)) : RPWithOracle A encBits ⊆ NPWithOracle A encBits :=
  RPWithOracle_subset_NPWithOracle A encBits

/-! ### The isolation lemma -/

/-- The family `{{0}, {1}, {0, 1}}` of subsets of `Fin 2`. -/
def family : Finset (Finset (Fin 2)) := {{0}, {1}, {0, 1}}

/-- With weights `1` and `2`, the set `{0}` has minimum weight and `{1}` does not. -/
example : {0} ∈ minWeightSets (fun x : Fin 4 => x.val + 1) ![0, 1] family ∧
    {1} ∉ minWeightSets (fun x : Fin 4 => x.val + 1) ![0, 1] family := by
  simp [mem_minWeightSets, family, setWeight]

/-- With equal weights, `{0}` and `{1}` both have minimum weight. -/
example : {0} ∈ minWeightSets (fun x : Fin 4 => x.val + 1) ![0, 0] family ∧
    {1} ∈ minWeightSets (fun x : Fin 4 => x.val + 1) ![0, 0] family := by
  simp [mem_minWeightSets, family, setWeight]

/-- With weights from `1, …, 4`, the family has a unique set of minimum weight with probability at
least `1 / 2`. -/
example : 1 / 2 ≤ Finset.dens (Finset.univ.filter fun w : Fin 2 → Fin 4 =>
    (minWeightSets (fun x => x.val + 1) w family).card = 1) :=
  half_le_dens_minWeightSets_card_eq_one (by simp) ⟨{0}, by simp [family]⟩

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.ValiantVazirani.reduce_mem_UNSAT' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ValiantVazirani.reduce_mem_UNSAT

end ComplexityTests.Isolation
