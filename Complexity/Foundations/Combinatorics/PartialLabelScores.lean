/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.UniformSchedules
public import Mathlib.Data.List.MinMax
import Mathlib.Tactic.SplitIfs

/-!
# Computable collision scores for partial label schedules

In the conditional-expectation construction in the proof of Lemma 4.5, printed p. 31 of
[OpenAI2026ETH], one whole variable or factor label is fixed at a time. A partial assignment
stores a whole label or `none` at each choice index. Unassigned choices are completed by one
uniformly enumerated function: repeated reads of one index never resample its value.

The closed-form incidence and group scores equal the actual finite completion averages. Their
normalized average is preserved when an unassigned whole label is fixed. Mathlib `List.argmin`
then gives a deterministic nonincreasing step when its explicit candidate list is exhaustive.
The scores enumerate incidence/variable pairs, not full completions.

This supplies score evaluation and one greedy step, not traversal of every choice index, an
initial potential estimate, or a new complete schedule-existence theorem. Polynomial rational
operation/bit-cost bounds and native machine certification remain separate obligations.
-/

public section

namespace Cslib.BalancedSchedules

open Finset
open scoped BigOperators

variable {I L : Type*} [DecidableEq I] [Fintype L] [DecidableEq L]

/-- Complete a partial assignment, using the same filler value on every read of an index. -/
@[expose] def completeLabels (assigned : I → Option L) (filler : I → L) (i : I) : L :=
  (assigned i).getD (filler i)

/-- Exact collision score for two choice indices under a partial assignment. A repeated index
scores one, not the reciprocal label count. -/
@[expose] def partialCollision (assigned : I → Option L) (i j : I) : ℚ :=
  if i = j then 1 else
    match assigned i, assigned j with
    | some x, some y => if x = y then 1 else 0
    | _, _ => 1 / (Fintype.card L : ℚ)

/-- The computable pair score is the true finite average over completions. -/
theorem partialCollision_eq_expect [Fintype I] [Nonempty L]
    (assigned : I → Option L) (i j : I) :
    partialCollision assigned i j =
      𝔼 filler : I → L,
        if completeLabels assigned filler i = completeLabels assigned filler j
        then (1 : ℚ) else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [partialCollision, ↓reduceIte, Fintype.expect_const]
  · cases hi : assigned i with
    | none =>
      cases hj : assigned j with
      | none =>
        simpa only [partialCollision, hij, ↓reduceIte, hi, hj, completeLabels,
          Option.getD_none] using (expect_schedule_collision (L := L) i j).symm
      | some y =>
        simp only [partialCollision, hij, ↓reduceIte, hi, hj, completeLabels,
          Option.getD_none, Option.getD_some]
        rw [expect_schedule_apply i (fun x : L => if x = y then (1 : ℚ) else 0)]
        simp [NNRat.smul_def]
    | some x =>
      cases hj : assigned j with
      | none =>
        simp only [partialCollision, hij, ↓reduceIte, hi, hj, completeLabels,
          Option.getD_none, Option.getD_some]
        rw [expect_schedule_apply j (fun y : L => if x = y then (1 : ℚ) else 0)]
        simp [NNRat.smul_def]
      | some y =>
        simp only [partialCollision, hij, ↓reduceIte, hi, hj, completeLabels,
          Option.getD_some, Fintype.expect_const]

/-- Averaging the candidate values of one unassigned whole label preserves the pair score. -/
theorem expect_partialCollision_update [Nonempty L] (assigned : I → Option L)
    (k i j : I) (hk : assigned k = none) :
    (𝔼 x : L, partialCollision (Function.update assigned k (some x)) i j) =
      partialCollision assigned i j := by
  by_cases hij : i = j
  · subst j
    simp only [partialCollision, ↓reduceIte, Fintype.expect_const]
  by_cases hki : k = i
  · subst k
    cases hj : assigned j with
    | none => simp [partialCollision, hij, hk, hj, Function.update, Ne.symm hij]
    | some y => simp [partialCollision, hij, hk, hj, Function.update, Ne.symm hij,
        NNRat.smul_def]
  by_cases hkj : k = j
  · subst k
    cases hi : assigned i with
    | none => simp [partialCollision, hij, hk, hi, Function.update]
    | some x => simp [partialCollision, hij, hk, hi, Function.update, NNRat.smul_def]
  simp only [partialCollision, hij, ↓reduceIte, Function.update_of_ne (Ne.symm hki),
    Function.update_of_ne (Ne.symm hkj), Fintype.expect_const]

/-- Observe one coordinate of a partial assignment of whole schedules. -/
@[expose] def partialCoordinateCollision {T G : Type*} [Fintype G] [DecidableEq G]
    (assigned : I → Option (T → G)) (t : T) (i j : I) : ℚ :=
  partialCollision (fun k => (assigned k).map (fun word => word t)) i j

omit [DecidableEq I] in
private theorem completeLabels_apply {T G : Type*} (assigned : I → Option (T → G))
    (filler : I → T → G) (i : I) (t : T) :
    completeLabels assigned filler i t =
      completeLabels (fun k => (assigned k).map (fun word => word t)) (fun k => filler k t) i := by
  cases h : assigned i <;> simp only [completeLabels, h, Option.getD_none,
    Option.getD_some, Option.map_none, Option.map_some]

/-- The coordinate score averages over whole schedule completions, not independent
incidence-level or point-specific replacements. -/
theorem partialCoordinateCollision_eq_expect {T G : Type*} [Fintype T] [DecidableEq T]
    [Fintype G] [DecidableEq G] [Nonempty G] [Fintype I]
    (assigned : I → Option (T → G)) (t : T) (i j : I) :
    partialCoordinateCollision assigned t i j =
      𝔼 filler : I → T → G,
        if completeLabels assigned filler i t = completeLabels assigned filler j t
        then (1 : ℚ) else 0 := by
  symm
  calc
    _ = 𝔼 filler : T → I → G,
        if completeLabels (fun k => (assigned k).map (fun word => word t)) (filler t) i =
          completeLabels (fun k => (assigned k).map (fun word => word t)) (filler t) j
        then (1 : ℚ) else 0 :=
      Fintype.expect_equiv (Equiv.piComm (fun _ : I => fun _ : T => G)) _ _
        (fun filler => by simp only [completeLabels_apply]; rfl)
    _ = _ := by
      rw [expect_schedule_apply t (fun filler : I → G =>
        if completeLabels (fun k => (assigned k).map (fun word => word t)) filler i =
          completeLabels (fun k => (assigned k).map (fun word => word t)) filler j
        then (1 : ℚ) else 0)]
      exact (partialCollision_eq_expect _ i j).symm

/-- Fixing one whole schedule preserves the average of every coordinate-collision score. -/
theorem expect_partialCoordinateCollision_update {T G : Type*} [Fintype T] [DecidableEq T]
    [Fintype G] [DecidableEq G] [Nonempty G]
    (assigned : I → Option (T → G)) (t : T) (k i j : I) (hk : assigned k = none) :
    (𝔼 word : T → G,
      partialCoordinateCollision (Function.update assigned k (some word)) t i j) =
      partialCoordinateCollision assigned t i j := by
  have hmap (word : T → G) :
      (fun l => (Function.update assigned k (some word) l).map (fun v => v t)) =
        Function.update (fun l => (assigned l).map (fun v => v t)) k (some (word t)) := by
    funext l
    by_cases h : l = k
    · subst l
      simp only [Function.update_self, Option.map_some]
    · simp only [Function.update_of_ne h]
  simp only [partialCoordinateCollision, hmap]
  rw [expect_schedule_apply t (fun value : G =>
    partialCollision (Function.update (fun l => (assigned l).map (fun v => v t)) k
      (some value)) i j)]
  exact expect_partialCollision_update _ k i j (by simp only [hk, Option.map_none])

/-- Incidence collisions factor only across the independent variable-label and factor-label
families. Repeated endpoints within either family are retained in `partialCollision`. -/
@[expose] def partialIncidenceCollision {V F : Type*} [DecidableEq V] [DecidableEq F]
    (varLabels : V → Option L) (factors : F → Option L) (v v' : V) (f f' : F) : ℚ :=
  partialCollision varLabels v v' * partialCollision factors f f'

/-- Exact joint completion average for one pair of incidences. -/
theorem partialIncidenceCollision_eq_expect {V F : Type*} [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] [Nonempty L]
    (varLabels : V → Option L) (factors : F → Option L) (v v' : V) (f f' : F) :
    partialIncidenceCollision varLabels factors v v' f f' =
      𝔼 a : V → L, 𝔼 d : F → L,
        if (completeLabels varLabels a v, completeLabels factors d f) =
          (completeLabels varLabels a v', completeLabels factors d f') then (1 : ℚ) else 0 := by
  rw [partialIncidenceCollision, partialCollision_eq_expect, partialCollision_eq_expect,
    Fintype.expect_mul_expect]
  apply Finset.expect_congr rfl
  intro a _
  apply Finset.expect_congr rfl
  intro d _
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

/-- Closed rational incidence potential of a partial assignment. The summation is over
incidences, not over exponentially many full completions. -/
@[expose] def partialIncidencePotential {E V F : Type*} [Fintype E]
    [DecidableEq V] [DecidableEq F] (edge : E → F × V)
    (varLabels : V → Option L) (factorLabels : F → Option L) : ℚ :=
  (∑ e, ∑ e', partialIncidenceCollision varLabels factorLabels
    (edge e).2 (edge e').2 (edge e).1 (edge e').1) -
      (Fintype.card E : ℚ) ^ 2 / (Fintype.card (L × L) : ℚ)

/-- The closed incidence formula equals the actual potential averaged over completions.
In particular, sharing a variable or factor does not create an independent new choice. -/
theorem partialIncidencePotential_eq_expect {E V F : Type*} [Fintype E]
    [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] [Nonempty L]
    (edge : E → F × V) (varLabels : V → Option L) (factorLabels : F → Option L) :
    partialIncidencePotential edge varLabels factorLabels =
      𝔼 a : V → L, 𝔼 d : F → L, potential (fun e =>
        (completeLabels varLabels a (edge e).2, completeLabels factorLabels d (edge e).1)) := by
  have hL : 0 < Fintype.card (L × L) := Fintype.card_pos
  simp_rw [potential_eq_collisions_sub _ hL, Finset.expect_sub_distrib,
    Finset.expect_sum_comm, Fintype.expect_const]
  simp only [partialIncidencePotential]
  simp_rw [partialIncidenceCollision_eq_expect]

/-- Closed rational total group potential, computed from the same partial whole schedules. -/
@[expose] def partialGroupPotential {T V G : Type*} [Fintype T] [Fintype V]
    [DecidableEq V] [Fintype G] [DecidableEq G] (assigned : V → Option (T → G)) : ℚ :=
  (∑ t, ∑ v, ∑ v', partialCoordinateCollision assigned t v v') -
    (Fintype.card T : ℚ) * Fintype.card V ^ 2 / (Fintype.card G : ℚ)

/-- The closed group formula equals the actual group potential averaged over completions
of whole schedules. No new independently sampled point labels are introduced. -/
theorem partialGroupPotential_eq_expect {T V G : Type*} [Fintype T] [DecidableEq T]
    [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Nonempty G]
    (assigned : V → Option (T → G)) :
    partialGroupPotential assigned =
      𝔼 filler : V → T → G, ∑ t, potential (fun v => completeLabels assigned filler v t) := by
  have hG : 0 < Fintype.card G := Fintype.card_pos
  simp_rw [sum_potential_eq_collisions_sub _ hG, Finset.expect_sub_distrib,
    Finset.expect_sum_comm, Fintype.expect_const]
  simp only [partialGroupPotential]
  simp_rw [partialCoordinateCollision_eq_expect]

/-- Averaging a variable-label update preserves every incidence pair score. -/
theorem expect_partialIncidenceCollision_update_variable {V F : Type*}
    [DecidableEq V] [DecidableEq F] [Nonempty L]
    (varLabels : V → Option L) (factorLabels : F → Option L)
    (k v v' : V) (f f' : F) (hk : varLabels k = none) :
    (𝔼 x : L, partialIncidenceCollision (Function.update varLabels k (some x)) factorLabels
      v v' f f') = partialIncidenceCollision varLabels factorLabels v v' f f' := by
  simp only [partialIncidenceCollision]
  rw [← Finset.expect_mul, expect_partialCollision_update _ k v v' hk]

/-- Averaging a factor-label update preserves every incidence pair score. -/
theorem expect_partialIncidenceCollision_update_factor {V F : Type*}
    [DecidableEq V] [DecidableEq F] [Nonempty L]
    (varLabels : V → Option L) (factorLabels : F → Option L)
    (v v' : V) (k f f' : F) (hk : factorLabels k = none) :
    (𝔼 x : L, partialIncidenceCollision varLabels (Function.update factorLabels k (some x))
      v v' f f') = partialIncidenceCollision varLabels factorLabels v v' f f' := by
  simp only [partialIncidenceCollision]
  rw [← Finset.mul_expect, expect_partialCollision_update _ k f f' hk]

/-- A whole variable-label update preserves the average closed incidence potential. -/
theorem expect_partialIncidencePotential_update_variable {E V F : Type*} [Fintype E]
    [DecidableEq V] [DecidableEq F] [Nonempty L] (edge : E → F × V)
    (varLabels : V → Option L) (factorLabels : F → Option L) (k : V)
    (hk : varLabels k = none) :
    (𝔼 x : L, partialIncidencePotential edge (Function.update varLabels k (some x)) factorLabels) =
      partialIncidencePotential edge varLabels factorLabels := by
  simp only [partialIncidencePotential]
  rw [Finset.expect_sub_distrib, Fintype.expect_const]
  simp_rw [Finset.expect_sum_comm,
    expect_partialIncidenceCollision_update_variable _ _ k _ _ _ _ hk]

/-- A whole factor-label update preserves the average closed incidence potential. -/
theorem expect_partialIncidencePotential_update_factor {E V F : Type*} [Fintype E]
    [DecidableEq V] [DecidableEq F] [Nonempty L] (edge : E → F × V)
    (varLabels : V → Option L) (factorLabels : F → Option L) (k : F)
    (hk : factorLabels k = none) :
    (𝔼 x : L, partialIncidencePotential edge varLabels (Function.update factorLabels k (some x))) =
      partialIncidencePotential edge varLabels factorLabels := by
  simp only [partialIncidencePotential]
  rw [Finset.expect_sub_distrib, Fintype.expect_const]
  simp_rw [Finset.expect_sum_comm, expect_partialIncidenceCollision_update_factor _ _ _ _ k _ _ hk]

/-- A whole variable-label update preserves the average closed group potential. -/
theorem expect_partialGroupPotential_update {T V G : Type*} [Fintype T] [DecidableEq T]
    [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Nonempty G]
    (assigned : V → Option (T → G)) (k : V) (hk : assigned k = none) :
    (𝔼 word : T → G, partialGroupPotential (Function.update assigned k (some word))) =
      partialGroupPotential assigned := by
  simp only [partialGroupPotential]
  rw [Finset.expect_sub_distrib, Fintype.expect_const]
  simp_rw [Finset.expect_sum_comm, expect_partialCoordinateCollision_update _ _ k _ _ hk]

/-- The paper's normalized partial score, with `C = b + w`. Both normalization denominators
remain explicit. This rational value carries no algorithmic cost certificate. -/
@[expose] def normalizedPartialScore {E V F T G : Type*} [Fintype E] [Fintype V]
    [DecidableEq V] [DecidableEq F] [Fintype T] [DecidableEq T] [Fintype G] [DecidableEq G]
    (edge : E → F × V) (varLabels : V → Option (T → G))
    (factorLabels : F → Option (T → G)) (C : ℕ) : ℚ :=
  partialIncidencePotential edge varLabels factorLabels / ((Fintype.card E : ℚ) * C) +
    partialGroupPotential varLabels / ((Fintype.card T : ℚ) * Fintype.card V)

/-- The computable normalized score is the conditional finite average of the actual
normalized objective on full completions. -/
theorem normalizedPartialScore_eq_expect {E V F T G : Type*} [Fintype E] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] [Fintype T] [DecidableEq T]
    [Fintype G] [DecidableEq G] [Nonempty G] (edge : E → F × V)
    (varLabels : V → Option (T → G)) (factorLabels : F → Option (T → G)) (C : ℕ) :
    normalizedPartialScore edge varLabels factorLabels C =
      𝔼 a : V → T → G, 𝔼 d : F → T → G,
        (potential (fun e => (completeLabels varLabels a (edge e).2,
          completeLabels factorLabels d (edge e).1)) / ((Fintype.card E : ℚ) * C) +
        (∑ t, potential (fun v => completeLabels varLabels a v t)) /
          ((Fintype.card T : ℚ) * Fintype.card V)) := by
  rw [normalizedPartialScore, partialIncidencePotential_eq_expect, partialGroupPotential_eq_expect]
  simp_rw [Finset.expect_add_distrib, ← Finset.expect_div, Fintype.expect_const]

/-- Fixing a whole variable schedule preserves the average normalized score. The update is
one whole word, shared by all its incidences and all schedule coordinates. -/
theorem expect_normalizedPartialScore_update_variable {E V F T G : Type*} [Fintype E]
    [Fintype V] [DecidableEq V] [DecidableEq F] [Fintype T] [DecidableEq T]
    [Fintype G] [DecidableEq G] [Nonempty G] (edge : E → F × V)
    (varLabels : V → Option (T → G)) (factorLabels : F → Option (T → G))
    (C : ℕ) (k : V) (hk : varLabels k = none) :
    (𝔼 word : T → G,
      normalizedPartialScore edge (Function.update varLabels k (some word)) factorLabels C) =
      normalizedPartialScore edge varLabels factorLabels C := by
  simp only [normalizedPartialScore]
  rw [Finset.expect_add_distrib, ← Finset.expect_div, ← Finset.expect_div,
    expect_partialIncidencePotential_update_variable _ _ _ k hk,
    expect_partialGroupPotential_update _ k hk]

/-- Fixing a whole factor schedule preserves the average normalized score; it changes no
variable-group assignment. -/
theorem expect_normalizedPartialScore_update_factor {E V F T G : Type*} [Fintype E]
    [Fintype V] [DecidableEq V] [DecidableEq F] [Fintype T] [DecidableEq T]
    [Fintype G] [DecidableEq G] [Nonempty G] (edge : E → F × V)
    (varLabels : V → Option (T → G)) (factorLabels : F → Option (T → G))
    (C : ℕ) (k : F) (hk : factorLabels k = none) :
    (𝔼 word : T → G,
      normalizedPartialScore edge varLabels (Function.update factorLabels k (some word)) C) =
      normalizedPartialScore edge varLabels factorLabels C := by
  simp only [normalizedPartialScore]
  rw [Finset.expect_add_distrib, ← Finset.expect_div,
    expect_partialIncidencePotential_update_factor _ _ _ k hk, Fintype.expect_const]

/-- Deterministic candidate selection for one variable: enumerate the supplied whole labels
and retain the first minimum. Empty candidate lists return `none`. -/
@[expose] def bestVariableLabel {E V F T G : Type*} [Fintype E] [Fintype V]
    [DecidableEq V] [DecidableEq F] [Fintype T] [DecidableEq T]
    [Fintype G] [DecidableEq G] (edge : E → F × V)
    (varLabels : V → Option (T → G)) (factorLabels : F → Option (T → G))
    (C : ℕ) (k : V) (values : List (T → G)) : Option (T → G) :=
  values.argmin fun word =>
    normalizedPartialScore edge (Function.update varLabels k (some word)) factorLabels C

/-- With an exhaustive candidate list, the actual deterministic update does not increase the
normalized score. Exhaustiveness is an enumeration condition, not a supplied good-label oracle. -/
theorem bestVariableLabel_spec {E V F T G : Type*} [Fintype E] [Fintype V]
    [DecidableEq V] [DecidableEq F] [Fintype T] [DecidableEq T]
    [Fintype G] [DecidableEq G] [Nonempty G] (edge : E → F × V)
    (varLabels : V → Option (T → G)) (factorLabels : F → Option (T → G))
    (C : ℕ) (k : V) (hk : varLabels k = none) (values : List (T → G))
    (hcover : ∀ word, word ∈ values) :
    ∃ chosen, bestVariableLabel edge varLabels factorLabels C k values = some chosen ∧
      normalizedPartialScore edge (Function.update varLabels k (some chosen)) factorLabels C ≤
        normalizedPartialScore edge varLabels factorLabels C := by
  let score := fun word =>
    normalizedPartialScore edge (Function.update varLabels k (some word)) factorLabels C
  change ∃ chosen, values.argmin score = some chosen ∧
    score chosen ≤ normalizedPartialScore edge varLabels factorLabels C
  cases harg : values.argmin score with
  | none =>
    have hnil : values = [] := List.argmin_eq_none.mp harg
    obtain ⟨word⟩ := (inferInstance : Nonempty (T → G))
    simpa only [hnil, List.not_mem_nil] using hcover word
  | some chosen =>
    refine ⟨chosen, rfl, ?_⟩
    calc
      score chosen ≤ 𝔼 word : T → G, score word := by
        apply Finset.le_expect Finset.univ_nonempty
        intro word _
        exact List.le_of_mem_argmin (hcover word) (by simp only [harg, Option.mem_some])
      _ = _ := expect_normalizedPartialScore_update_variable edge varLabels factorLabels C k hk

/-- Deterministic candidate selection for one factor, without changing variable groups. -/
@[expose] def bestFactorLabel {E V F T G : Type*} [Fintype E] [Fintype V]
    [DecidableEq V] [DecidableEq F] [Fintype T] [DecidableEq T]
    [Fintype G] [DecidableEq G] (edge : E → F × V)
    (varLabels : V → Option (T → G)) (factorLabels : F → Option (T → G))
    (C : ℕ) (k : F) (values : List (T → G)) : Option (T → G) :=
  values.argmin fun word =>
    normalizedPartialScore edge varLabels (Function.update factorLabels k (some word)) C

/-- The actual factor update selected from an exhaustive list does not increase the score. -/
theorem bestFactorLabel_spec {E V F T G : Type*} [Fintype E] [Fintype V]
    [DecidableEq V] [DecidableEq F] [Fintype T] [DecidableEq T]
    [Fintype G] [DecidableEq G] [Nonempty G] (edge : E → F × V)
    (varLabels : V → Option (T → G)) (factorLabels : F → Option (T → G))
    (C : ℕ) (k : F) (hk : factorLabels k = none) (values : List (T → G))
    (hcover : ∀ word, word ∈ values) :
    ∃ chosen, bestFactorLabel edge varLabels factorLabels C k values = some chosen ∧
      normalizedPartialScore edge varLabels (Function.update factorLabels k (some chosen)) C ≤
        normalizedPartialScore edge varLabels factorLabels C := by
  let score := fun word =>
    normalizedPartialScore edge varLabels (Function.update factorLabels k (some word)) C
  change ∃ chosen, values.argmin score = some chosen ∧
    score chosen ≤ normalizedPartialScore edge varLabels factorLabels C
  cases harg : values.argmin score with
  | none =>
    have hnil : values = [] := List.argmin_eq_none.mp harg
    obtain ⟨word⟩ := (inferInstance : Nonempty (T → G))
    simpa only [hnil, List.not_mem_nil] using hcover word
  | some chosen =>
    refine ⟨chosen, rfl, ?_⟩
    calc
      score chosen ≤ 𝔼 word : T → G, score word := by
        apply Finset.le_expect Finset.univ_nonempty
        intro word _
        exact List.le_of_mem_argmin (hcover word) (by simp only [harg, Option.mem_some])
      _ = _ := expect_normalizedPartialScore_update_factor edge varLabels factorLabels C k hk

end Cslib.BalancedSchedules
