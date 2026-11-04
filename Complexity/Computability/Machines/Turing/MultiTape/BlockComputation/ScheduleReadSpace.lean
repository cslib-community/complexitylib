/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadCorrect
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts

/-!
# Native space bounds for streamed schedule digit counts

The number of tapes, head offset and queried digit are fixed parameters. The schedule number
and interval count are binary runtime inputs. Reading rows repeatedly divides by the fixed row
radix; the state retains only the unread suffix and one count. In particular, it does not build
a list of intervals or a power with runtime exponent.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleRead

open MultiTapeTM MultiTapeTM.ComputableInSpace

/-- The unread suffix and binary count use their actual storage. -/
@[expose] noncomputable def encState : State ↪ List Bool := encPair encNat encNat

/-- One fixed-head digit-count step uses native space linear in its stored state. -/
theorem step_inSpace (k c δ : ℕ) :
    ComputableInSpace (step k c δ) encState encState (fun a => (encState a).length) := by
  have hs := fst encNat encNat
  have hn := snd encNat encNat
  have hnext := budget_natDiv hs (budget_const (encB := encNat) (3 ^ (k + 1)) (.refl _))
  have hdigit := budget_natMod
    (budget_natDiv hs (budget_const (encB := encNat) (3 ^ c) (.refl _)))
    (budget_const (encB := encNat) 3 (.refl _))
  have htest := budget_natEq hdigit (budget_const (encB := encNat) δ (.refl _))
  have hinc := budget_ite htest
    (budget_const (encB := encNat) 1 (.refl _))
    (budget_const (encB := encNat) 0 (.refl _))
  exact (budget_prod hnext (budget_natAdd hn hinc)).of_enc_eq fun a => by
    simp only [step, encState, decide_eq_true_eq]

/-- Counting a fixed schedule digit uses space linear in the binary schedule and interval
count, including when the schedule is zero and the interval count is very large. -/
theorem read_inSpace (k c δ : ℕ) :
    ComputableInSpace (read k c δ) encState encNat (fun a => (encState a).length) := by
  have hinit := budget_prod (fst encNat encNat)
    (budget_const (encB := encNat) 0 (.refl _))
  have hstates (a : ℕ × ℕ) (j : ℕ) (hj : j ≤ a.2) :
      (encState ((step k c δ)^[j] (a.1, 0))).length ≤ (encState a).length := by
    have hs := ComputableTidilyInO.length_encNat_mono (iterate_fst_le k c δ a.1 j)
    have hn := ComputableTidilyInO.length_encNat_mono
      ((iterate_snd_le k c δ a.1 j).trans hj)
    simp only [encState, length_encPair]
    omega
  have hrun := budget_iterate (snd encNat encNat) hinit (step_inSpace k c δ)
    hstates (.refl _)
  exact (snd' hrun).of_enc_eq fun _ => rfl

/-- Positive and negative movement counts give the signed block origin without storing
an integer whose magnitude is charged separately. -/
@[expose] def origin (k c : ℕ) (a : ℕ × ℕ) : ℕ × ℕ :=
  (read k c 2 a, read k c 0 a)

/-- Native signed-origin preparation keeps both binary counts within the input budget. -/
theorem origin_inSpace (k c : ℕ) :
    ComputableInSpace (origin k c) encState encState (fun a => (encState a).length) :=
  budget_prod (read_inSpace k c 2) (read_inSpace k c 0)

/-- The two prepared counters represent the functional schedule's exact block origin. -/
theorem origin_sub_eq_scheduleBlock {k q : ℕ} (σ i : ℕ) (hi : i ≤ q)
    (head : Option (Fin k)) :
    let (positive, negative) := origin k ((finSuccEquiv k).symm head) (σ, i)
    (positive : ℤ) - negative = scheduleBlock (scheduleOfNat k q σ) i head := by
  simpa only [origin, read_eq_digitCount] using
    (scheduleBlock_scheduleOfNat (k := k) σ hi head).symm

end Turing.MultiTapePTM.BlockComputation.ScheduleRead
