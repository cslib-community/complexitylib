/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CountingTreeBound
public import ComplexityTests.Computability.Complexity.FineGrained.CountingSparsification
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# Independent counting-sparsification workspace controls

A concrete native polynomial-time leaf routine is given an exponential time allowance while its
workspace stays polynomial. The new transfer is instantiated with an unconditional tree bound.
The routine is only a diagnostic: it counts the particular leaves below, not arbitrary CNFs.
The branching trace checks the declared-variable correction and terminal stack separately from
the resource theorem, without adding a second search or counting algorithm.
-/

@[expose] public section

namespace Cslib.Complexity.Tests.CountingWorkspace

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification Turing.MultiTapeTM
open CountingSparsify

/-- Diagnostic leaf output: reject an empty clause, otherwise return one. -/
def leafProbe (ψ : CNF ℕ) : ℕ := if ψ.any List.isEmpty then 0 else 1

private theorem probe_certificate (q : CNF ℕ → ℕ) :
    ∃ d, ComputableInO leafProbe encCNF encNat
      (fun ψ => 2 ^ q ψ * ((encCNF ψ).length + 1) ^ d)
      (fun ψ => ((encCNF ψ).length + 1) ^ d) := by
  have hp : ComputableTidilyInPolyTime leafProbe encCNF encNat := by
    unfold leafProbe encCNF
    fun_prop
  obtain ⟨d, e, h⟩ := hp.exists_degree
  exact ⟨d, .of_tidy (h.inO.mono_le
    (fun ψ => Nat.le_mul_of_pos_left _ (Nat.two_pow_pos (q ψ))) (fun _ => le_rfl))⟩

/-- No tree or machine premise is assumed: the width-one tree bound and the concrete leaf
certificate provide a single native search certificate with polynomial workspace. The supplied
leaf time allowance is `2 ^ ψ.length * (|encCNF ψ| + 1) ^ d`. -/
example : ∃ T S : CNF ℕ → ℕ,
    ComputableInO (search 2 1 1 1 leafProbe) encCNF encNat T S ∧
      PolyBounded (fun ψ : CNF ℕ => (encCNF ψ).length) S := by
  obtain ⟨d, h⟩ := probe_certificate List.length
  have ht (ψ : CNF ℕ) :
      ((2 ^ ψ.length * ((encCNF ψ).length + 1) ^ d : ℕ) : ℝ) ≤
        1 * (2 ^ ((1 : ℝ) * ψ.length) * (((encCNF ψ).length : ℝ) + 1) ^ d) + 1 := by
    simp only [one_mul, Real.rpow_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_add, Nat.cast_one]
    linarith
  obtain ⟨T, S, _, _, hTS, hS, _⟩ := exists_computableInO_search_polySpace
    (by decide : 1 ≤ 2) (by decide : 1 ≤ 1) (by decide : 2 ≤ 2) (k := 1) le_rfl
    (countingTreeBound_one (by decide) 1 1) h
    (fun ψ _ _ => by unfold leafProbe; split_ifs <;> simp [Nat.one_le_two_pow])
    (by norm_num : (0 : ℝ) ≤ 1) (c := 1) (e := d)
    (fun ψ _ _ => by simpa only [Nat.cast_one] using ht ψ)
    (a := 1) (b := d) (fun _ _ _ => by simp)
  exact ⟨T, S, hTS, hS⟩

/-- The same native diagnostic passes through the existing dense compiler and width guard with
an exponential allowance in the number of variables and a separate polynomial workspace. -/
example : ∃ T S : CNF ℕ → ℕ,
    ComputableInO (guardOccurrenceCounter 2 leafProbe) encCNF encNat T S ∧
      PolyBounded (fun ψ : CNF ℕ => (encCNF ψ).length) S := by
  obtain ⟨d, h⟩ := probe_certificate CNF.numVars
  have ht (ψ : CNF ℕ) :
      ((2 ^ ψ.numVars * ((encCNF ψ).length + 1) ^ d : ℕ) : ℝ) ≤
        1 * (2 ^ ((1 : ℝ) * ψ.numVars) * (((encCNF ψ).length : ℝ) + 1) ^ d) + 1 := by
    simp only [one_mul, Real.rpow_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_add, Nat.cast_one]
    linarith
  obtain ⟨T, S, _, _, hTS, hS, _⟩ :=
    exists_computableInO_guardOccurrenceCounter_polySpace_of_promise (by decide : 2 ≤ 2)
      h (by norm_num : (0 : ℝ) ≤ 1) (c := 1) (e := d)
      (fun ψ _ _ _ => by simpa only [Nat.cast_one] using ht ψ)
      (a := 1) (b := d) (fun _ _ _ _ => by simp)
  exact ⟨T, S, hTS, hS⟩

/-- Width guards, declared-variable normalization, terminal stack stability, encoded label-size
distinction, and diagnostic vs. exact model-count comparison. -/
example :
    search 2 1 1 1 leafProbe [[(7, true)], [(99, true), (99, false)]] = 0 ∧
    search 2 2 2 1 leafProbe [[(7, true)], [(99, true), (99, false)]] = 2 ∧
    (step 2 2 leafProbe)^[3] (init 2 flowerWithTautology) = (3, ([], 5)) ∧
    (step 2 2 leafProbe)^[4] (init 2 flowerWithTautology) = (3, ([], 5)) ∧
    search 2 2 2 2 leafProbe flowerWithTautology = 5 ∧
    search 2 1 0 1 leafProbe ([] : CNF ℕ) = 1 ∧
    search 2 1 0 1 leafProbe ([[]] : CNF ℕ) = 0 ∧
    search 2 1 0 1 leafProbe [[(1000, true)]] = 0 ∧
    (CNF.numVars [[(0, true)]] = CNF.numVars [[(1000, true)]] ∧
      (encCNF [[(0, true)]]).length < (encCNF [[(1000, true)]]).length) ∧
    (leafProbe [[(0, true), (1, true)]] = 1 ∧
      CNF.modelCount [[(0, true), (1, true)]] = 3) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide⟩

end Cslib.Complexity.Tests.CountingWorkspace
