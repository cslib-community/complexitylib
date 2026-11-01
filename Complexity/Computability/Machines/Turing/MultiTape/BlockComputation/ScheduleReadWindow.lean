/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadSpace
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadCorrect

/-!
# Streamed schedule window membership

Window membership is computed from four streamed digit counts. The schedule, target interval,
port and candidate predecessor are binary runtime data. No interval list or runtime power is
allocated; tape number and digit offset are fixed machine parameters.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleRead

open MultiTapeTM MultiTapeTM.ComputableInSpace

/-- Schedule, target interval, target port and candidate preceding interval. -/
abbrev WindowArgs := ℕ × ℕ × ℕ × ℕ

/-- Binary encoding of all window-membership inputs. -/
@[expose] noncomputable def encWindowArgs : WindowArgs ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat encNat))

/-- Compare the positive/negative counts defining two windows, using streamed readers. -/
@[expose] def inWindow (k c : ℕ) : WindowArgs → Bool := fun (σ, i, δ, j) =>
  let pi := read k c 2 (σ, i)
  let ni := read k c 0 (σ, i)
  let pj := read k c 2 (σ, j)
  let nj := read k c 0 (σ, j)
  decide (pj + ni + 1 ≤ nj + pi + δ + 1 ∧ nj + pi + δ ≤ pj + ni + 2)

/-- The streamed comparison has exactly the existing numeric schedule semantics. -/
theorem inWindow_eq (k c σ i δ j : ℕ) :
    inWindow k c (σ, i, δ, j) = inWindowNum k σ c i δ j := by
  simp only [inWindow, read_eq_digitCount, inWindowNum]

/-- Native window membership uses space linear in actual binary input storage. -/
theorem inWindow_inSpace (k c : ℕ) :
    ComputableInSpace (inWindow k c) encWindowArgs encBool
      (fun a => (encWindowArgs a).length) := by
  have hs := fst encNat (encPair encNat (encPair encNat encNat))
  have ht := snd encNat (encPair encNat (encPair encNat encNat))
  have hi := budget_comp_linear (fst encNat (encPair encNat encNat)) ht
  have hdj := budget_comp_linear (snd encNat (encPair encNat encNat)) ht
  have hd := budget_comp_linear (fst encNat encNat) hdj
  have hj := budget_comp_linear (snd encNat encNat) hdj
  have hpi := budget_comp_linear (read_inSpace k c 2) (budget_prod hs hi)
  have hni := budget_comp_linear (read_inSpace k c 0) (budget_prod hs hi)
  have hpj := budget_comp_linear (read_inSpace k c 2) (budget_prod hs hj)
  have hnj := budget_comp_linear (read_inSpace k c 0) (budget_prod hs hj)
  have hone := budget_const (encB := encNat) 1 (show
    (fun a => (encWindowArgs a).length) ≼ fun a => (encWindowArgs a).length from .refl _)
  have htwo := budget_const (encB := encNat) 2 (show
    (fun a => (encWindowArgs a).length) ≼ fun a => (encWindowArgs a).length from .refl _)
  have ha := budget_natAdd hpj hni
  have hb := budget_natAdd (budget_natAdd hnj hpi) hd
  have hleft := budget_natLt (budget_natAdd hb hone) (budget_natAdd ha hone)
  have hright := budget_natLt (budget_natAdd ha htwo) hb
  have hfalse := budget_const (encB := encBool) false (show
    (fun a => (encWindowArgs a).length) ≼ fun a => (encWindowArgs a).length from .refl _)
  have htrue := budget_const (encB := encBool) true (show
    (fun a => (encWindowArgs a).length) ≼ fun a => (encWindowArgs a).length from .refl _)
  exact (budget_ite hleft hfalse (budget_ite hright hfalse htrue)).of_enc_eq
    fun ⟨σ, i, δ, j⟩ => by
      simp only [inWindow, decide_eq_true_eq]
      split_ifs <;> simp_all

end Turing.MultiTapePTM.BlockComputation.ScheduleRead
