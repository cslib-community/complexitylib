/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.DegreePartition

/-!
# Vertex-polynomial volume of fixed degree-matrix constructions

Count the actual one-hot clauses, bounded neighbor sublists, matrix states and reverse terms.
These output-volume bounds are separate from the certified binary writing costs. Source:
[ChenJiangZhu2027], Theorem 7.3 / Appendix C.2, PDF pp.25,32.
-/

public section

namespace Cslib.Logic.PL.DegreePartition

/-- The existing one-hot writer contributes at most one wide clause and q squared exclusions. -/
theorem oneHot_volume (n q D : ℕ) : (oneHot n q D).length ≤ n * (1 + q ^ 2) := by
  have hu (u : Fin n) :
      (CNF.exactlyOne ((List.finRange q).map fun i => selection (D := D) i u)).length ≤
        1 + q ^ 2 := by
    simp only [CNF.exactlyOne, CNF.atLeastOne, CNF.atMostOne, List.length_append,
      List.length_cons, List.length_nil, List.length_flatMap, List.length_map,
      List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    calc
      _ ≤ 1 + ∑ _i : Fin q, q := by
        apply Nat.add_le_add_left
        apply Finset.sum_le_sum
        intro i _
        simpa only [List.length_ofFn] using List.length_filter_le
          (fun j => decide (j ≠ selection i u)) (List.ofFn fun j : Fin q => selection j u)
      _ = _ := by simp [pow_two]
  simp only [List.finRange, List.map_ofFn] at hu
  simp only [oneHot, List.length_flatMap, List.finRange, List.map_ofFn, List.sum_ofFn,
    Function.comp_def]
  calc
    _ ≤ ∑ _u : Fin n, (1 + q ^ 2) := Finset.sum_le_sum fun u _ => hu u
    _ = _ := by simp

/-- Every fixed matrix state contributes at most one implication clause per source vertex. -/
theorem rules_volume (n q D : ℕ) (hD : 1 ≤ D)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    (rules n q D hD M).length ≤ q ^ 2 * n * (D + 1) := by
  have hu (i j : Fin q) (u : Fin n) : (ruleAt hD M i j u).length ≤ D + 1 := by
    simp only [ruleAt, List.length_flatMap, List.finRange, List.map_ofFn,
      List.sum_ofFn, Function.comp_def]
    calc
      _ ≤ ∑ _s : Fin (D + 1), 1 := Finset.sum_le_sum fun s _ => by split_ifs <;> simp
      _ = _ := by simp
  simp only [rules, List.length_flatMap, List.finRange, List.map_ofFn,
    List.sum_ofFn, Function.comp_def]
  calc
    _ ≤ ∑ _i : Fin q, ∑ _j : Fin q, ∑ _u : Fin n, (D + 1) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun u _ => hu i j u
    _ = _ := by simp [pow_two, Nat.mul_assoc]

/-- Actual full no-test side clauses and reverse terms have explicit fixed-q,D polynomial volume. -/
theorem volumes {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hD : 1 ≤ D) (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    (side G q D hD M).length ≤ n * (1 + q ^ 2) + q * D * n * (n + 1) ^ D +
      q ^ 2 * n * (D + 1) ∧
    ((conditions G q D).map List.length).sum ≤ q * D * n * ((n + 1) ^ D + 1) := by
  have hv := DegreeThreshold.volumes G D 0
  constructor
  · have hf : ((List.finRange q).flatMap fun j =>
        (DegreeThreshold.finiteForward G D 0).relabel (Prod.mk j)).length ≤
        q * D * n * (n + 1) ^ D := by
      simp only [List.length_flatMap, CNF.relabel, List.length_map, List.finRange,
        List.map_ofFn, List.sum_ofFn, Function.comp_def]
      have h := Nat.mul_le_mul_left q hv.1
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        Nat.mul_assoc] using h
    have ho := oneHot_volume n q D
    have hr := rules_volume n q D hD M
    simp only [side, List.length_append]
    omega
  · simp only [conditions, List.flatMap, List.map_flatten, List.sum_flatten, List.map_map,
      CNF.relabel, List.length_map, List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    have h := Nat.mul_le_mul_left q hv.2
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Nat.mul_assoc] using h

end Cslib.Logic.PL.DegreePartition
