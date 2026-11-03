/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadSearch
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadWindow
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds

/-!
# Native space for streamed predecessor search

The search retains its binary schedule and target, one binary cursor and the latest matching
interval. Each membership test reuses the streamed digit-count reader. Thus even a very large
binary target does not allocate an interval list or a power with runtime exponent.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleRead

open MultiTapeTM MultiTapeTM.ComputableInSpace

/-- Binary schedule, target interval and target port. -/
@[expose] noncomputable def encSearchArgs : SearchArgs ↪ List Bool :=
  encPair encNat (encPair encNat encNat)

/-- Immutable search arguments, binary cursor and optional last matching interval. -/
@[expose] noncomputable def encSearchState : SearchState ↪ List Bool :=
  encPair encSearchArgs (encPair encNat (encOption encNat))

/-- A search step uses native space linear in its actual encoded state. -/
theorem searchStep_inSpace (k c : ℕ) :
    ComputableInSpace (searchStep k c) encSearchState encSearchState
      (fun a => (encSearchState a).length) := by
  have ha := fst encSearchArgs (encPair encNat (encOption encNat))
  have hr := snd encSearchArgs (encPair encNat (encOption encNat))
  have hj := hr.fst'
  have hlast := hr.snd'
  have hwargs := budget_prod ha.fst'
    (budget_prod ha.snd'.fst' (budget_prod ha.snd'.snd' hj))
  have htest := budget_comp_linear (inWindow_inSpace k c) hwargs
  have hfound := budget_ite htest (budget_optionSome hj) hlast
  exact (budget_prod ha (budget_prod (budget_natSucc hj) hfound)).of_enc_eq
    fun ⟨⟨σ, i, δ⟩, j, latest⟩ => by
      simp only [searchStep, encSearchState, encSearchArgs]

/-- A predecessor search stores only binary counters and the latest witness, with native
space linear in the actual schedule/target/port encoding. -/
theorem search_inSpace (k c : ℕ) :
    ComputableInSpace (search k c) encSearchArgs (encOption encNat)
      (fun a => (encSearchArgs a).length) := by
  have ha : ComputableInSpace (fun a : SearchArgs => a) encSearchArgs encSearchArgs
      (fun a => (encSearchArgs a).length) := of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)
  have hn := ha.snd'.fst'
  have hinit := budget_prod ha (budget_prod
    (budget_const (encB := encNat) 0 (.refl _))
    (budget_const (encB := encOption encNat) none (.refl _)))
  have hstates (a : SearchArgs) (j : ℕ) (hj : j ≤ a.2.1) :
      (encSearchState ((searchStep k c)^[j] (a, 0, none))).length ≤
        8 * (encSearchArgs a).length + 8 := by
    have hcursor := searchIterate_cursor k c a j
    have hcontext := searchIterate_context k c a j
    have hc := ComputableTidilyInO.length_encNat_mono hj
    have hlatest :
        (encOption encNat (((searchStep k c)^[j] (a, 0, none)).2.2)).length ≤
          (encNat a.2.1).length + 1 := by
      cases hl : ((searchStep k c)^[j] (a, 0, none)).2.2 with
      | none => simp
      | some v =>
        have hv := searchIterate_latest_bound k c a j v hl
        have hb := ComputableTidilyInO.length_encNat_mono (hv.le.trans hj)
        simpa only [encOption_some, List.length_cons] using Nat.add_le_add_right hb 1
    simp only [encSearchState, length_encPair, hcontext, hcursor]
    have harg : 2 * (encNat a.2.1).length ≤ (encSearchArgs a).length := by
      simp only [encSearchArgs, length_encPair]
      omega
    omega
  have hrun := budget_iterate hn hinit (searchStep_inSpace k c) hstates
    (.of_le_linear 8 8 fun _ => le_rfl)
  exact hrun.snd'.snd' |>.of_enc_eq fun _ => rfl

end Turing.MultiTapePTM.BlockComputation.ScheduleRead
