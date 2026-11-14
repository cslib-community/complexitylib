/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticDomination.Adapted
public import Mathlib.Data.Fin.Tuple.Take

/-!
# Prefix marginals of sequential PMF processes

Restricting an actual finite execution to an earlier budget gives exactly the
process at that budget. Supported full executions therefore have supported prefixes.

## Main results

* `seqProcess_map_init`, `seqProcess_map_castLE`: exact prefix marginals.
* `mem_support_seqProcess_snoc`, `mem_support_seqProcess_castLE`,
  `mem_support_seqProcess_step`: supported extensions, restrictions and actual transitions.
-/

public section
namespace Cslib.Probability.PMF
variable {α : Type*}

/-- Forgetting the last response recovers the preceding sequential law. -/
theorem seqProcess_map_init (step : ∀ t : ℕ, (Fin t → α) → PMF α) (n : ℕ) :
    (seqProcess step (n + 1)).map Fin.init = seqProcess step n := by
  rw [seqProcess, PMF.map_bind]
  have hm (h : Fin n → α) :
      ((step n h).map (fun a => Fin.snoc (α := fun _ => α) h a)).map
        (Fin.init (α := fun _ => α)) = PMF.pure h := by
    simp only [PMF.map_comp, Function.comp_def, Fin.init_snoc]
    exact PMF.map_const (step n h) h
  simp_rw [hm]
  exact PMF.bind_pure _

/-- Every finite-prefix marginal is the actual law at the shorter budget. -/
theorem seqProcess_map_castLE (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    {n m : ℕ} (hnm : n ≤ m) :
    (seqProcess step m).map (fun h i => h (Fin.castLE hnm i)) = seqProcess step n := by
  induction m, hnm using Nat.le_induction with
  | base =>
    have hf : (fun (h : Fin n → α) i => h (Fin.castLE le_rfl i)) = id := rfl
    rw [hf, PMF.map_id]
  | succ m hnm ih =>
    have hf : (fun (h : Fin (m + 1) → α) (i : Fin n) => h (Fin.castLE (Nat.le_succ_of_le hnm) i)) =
        (fun (h : Fin m → α) i => h (Fin.castLE hnm i)) ∘ Fin.init := rfl
    rw [hf, ← PMF.map_comp, seqProcess_map_init, ih]

/-- A supported extension consists exactly of a supported prefix and a
supported response from its actual conditional law. -/
theorem mem_support_seqProcess_snoc (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    {n : ℕ} (h : Fin n → α) (a : α) :
    Fin.snoc h a ∈ (seqProcess step (n + 1)).support ↔
      h ∈ (seqProcess step n).support ∧ a ∈ (step n h).support := by
  rw [seqProcess, PMF.mem_support_bind_iff]
  constructor
  · rintro ⟨g, hg, hx⟩
    obtain ⟨x, ha, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    obtain ⟨rfl, rfl⟩ := Fin.snoc_inj.mp he
    exact ⟨hg, ha⟩
  · rintro ⟨hh, ha⟩
    exact ⟨h, hh, (PMF.mem_support_map_iff _ _ _).mpr ⟨a, ha, rfl⟩⟩

/-- Restricting a supported execution gives a supported earlier prefix. -/
theorem mem_support_seqProcess_castLE (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    {n m : ℕ} (hnm : n ≤ m) (h : Fin m → α) (hh : h ∈ (seqProcess step m).support) :
    (fun i => h (Fin.castLE hnm i)) ∈ (seqProcess step n).support := by
  rw [← seqProcess_map_castLE step hnm]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨h, hh, rfl⟩

/-- Every coordinate of a supported execution is supported by its actual
history-dependent transition law. -/
theorem mem_support_seqProcess_step (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    {n : ℕ} (h : Fin n → α) (hh : h ∈ (seqProcess step n).support) (t : Fin n) :
    h t ∈ (step t.1 (Fin.take t.1 t.2.le h)).support := by
  have hp := mem_support_seqProcess_castLE step (Nat.succ_le_of_lt t.2) h hh
  change Fin.take (t.1 + 1) (Nat.succ_le_of_lt t.2) h ∈ _ at hp
  rw [Fin.take_succ_eq_snoc _ t.2] at hp
  exact ((mem_support_seqProcess_snoc step _ _).mp hp).2

end Cslib.Probability.PMF
