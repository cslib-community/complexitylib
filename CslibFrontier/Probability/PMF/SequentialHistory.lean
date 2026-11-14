/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.OfFn

/-!
# Newest-first transcripts of finite sequential histories

`seqHistory` translates the chronological coordinates used by sequential PMF
processes into the newest-first lists used by history-dependent response laws.
-/

public section
namespace Cslib.Probability.PMF
variable {α : Type*}

/-- Read a chronological finite prefix as a newest-first response transcript. -/
@[expose] def seqHistory {n : ℕ} (h : Fin n → α) : List α := (List.ofFn h).reverse

@[simp] theorem seqHistory_zero (h : Fin 0 → α) : seqHistory h = [] := by
  simp [seqHistory]

@[simp] theorem seqHistory_one (h : Fin 1 → α) : seqHistory h = [h 0] := by
  simp [seqHistory]

@[simp] theorem length_seqHistory {n : ℕ} (h : Fin n → α) : (seqHistory h).length = n := by
  simp [seqHistory]

/-- Appending the next chronological coordinate prepends the newest response. -/
theorem seqHistory_snoc {n : ℕ} (h : Fin n → α) (a : α) :
    seqHistory (Fin.snoc h a) = a :: seqHistory h := by
  rw [seqHistory, List.ofFn_succ_last]
  simp [seqHistory]

end Cslib.Probability.PMF
