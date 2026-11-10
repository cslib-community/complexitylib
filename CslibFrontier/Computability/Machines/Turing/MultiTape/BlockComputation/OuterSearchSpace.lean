/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Mathlib.Data.Finset.Lattice.Fold
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.OuterSearch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearchSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts

/-!
# Physical space for bounded increasing time guesses

One outer caller is retained beside one schedule search. A finite supremum bounds candidate
storage without adding a factor for the number of guesses. The supremum is a mathematical
allowance; no list of guesses or candidate spaces is constructed by the machine.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.OuterSearch

open MultiTapeTM

/-- Actual binary input length and largest time guess, including the optional decision. -/
@[expose] noncomputable def callerSpace (N A : ℕ) : ℕ :=
  8 * ((encNat N).length + (encNat A).length + 1)

/-- Maximum storage of one candidate search through the largest permitted guess. -/
@[expose] noncomputable def candidateSpace (k s : ℕ) (Q : Type) (N A : ℕ) : ℕ :=
  (Finset.range (A + 1)).sup fun guess => ScheduleSearch.space k s Q N
    (BalancedParameters.blockWidth guess) (BalancedParameters.horizon guess)

/-- One suspended caller beside one candidate, with complete sum and product framing. -/
@[expose] noncomputable def space (k s : ℕ) (Q : Type) (N A : ℕ) : ℕ :=
  2 * callerSpace N A + candidateSpace k s Q N A + 2

/-- Any candidate through the bounded guess fits the same supremum allowance. -/
theorem candidate_space_le (k s : ℕ) (Q : Type) (N A guess : ℕ) (hguess : guess ≤ A) :
    ScheduleSearch.space k s Q N (BalancedParameters.blockWidth guess)
      (BalancedParameters.horizon guess) ≤ candidateSpace k s Q N A :=
  Finset.le_sup (f := fun guess => ScheduleSearch.space k s Q N
    (BalancedParameters.blockWidth guess) (BalancedParameters.horizon guess))
    (Finset.mem_range.mpr (by omega))

/-- Binary caller storage is uniform through the largest permitted time guess. -/
theorem caller_encoding_le (N A guess : ℕ) (result : Option Bool) (hguess : guess ≤ A) :
    (encCaller (N, guess, result)).length ≤ callerSpace N A := by
  have hg := length_encNat_mono hguess
  have hr : (encOption encBool result).length ≤ 2 := by
    cases result <;> simp only [encOption_none, encOption_some, List.length_nil,
      List.length_cons, encBool_apply] <;> omega
  simp only [encCaller, length_encPair, callerSpace]
  omega

/-- Every physical clock of a bounded candidate call charges its suspended caller and callee. -/
theorem runFrom_one_encoding_le {k s : ℕ} {Q : Type} [Finite Q]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (N guess A : ℕ) (result : Option Bool)
    (w : List Bool) (T : ℕ) (hpending : pending (N, guess, result) = true)
    (hguess : guess ≤ A)
    (hpre : ∀ u < T, (ScheduleSearch.machine M e).halted
      ((ScheduleSearch.machine M e).runFrom w (ScheduleSearch.initial
        (N, BalancedParameters.blockWidth guess, BalancedParameters.horizon guess)) u) = false)
    (hhalt : (ScheduleSearch.machine M e).halted ((ScheduleSearch.machine M e).runFrom w
      (ScheduleSearch.initial
        (N, BalancedParameters.blockWidth guess, BalancedParameters.horizon guess)) T) = true)
    (hsize : ∀ u ≤ T, (ScheduleSearch.encState ((ScheduleSearch.machine M e).runFrom w
      (ScheduleSearch.initial
        (N, BalancedParameters.blockWidth guess, BalancedParameters.horizon guess)) u)).length ≤
          candidateSpace k s Q N A)
    (hnext : (encCaller (resume (N, guess, result) ((ScheduleSearch.machine M e).runFrom w
      (ScheduleSearch.initial
        (N, BalancedParameters.blockWidth guess, BalancedParameters.horizon guess)) T))).length ≤
          callerSpace N A)
    (t : ℕ) (ht : t ≤ T + 2) :
    (encState ((machine M e).runFrom w (.inl (N, guess, result)) t)).length ≤
      space k s Q N A := by
  have hreq : request (k := k) (Q := Q) (N, guess, result) = some (ScheduleSearch.initial
      (N, BalancedParameters.blockWidth guess, BalancedParameters.horizon guess)) := by
    simp only [request, hpending, ↓reduceIte, parameters]
  have hlive : caller.halted (N, guess, result) = false := by
    simp only [caller, hpending, Bool.not_true]
  exact QueryMachine.withCalls_runFrom_call_encoding_le caller (ScheduleSearch.machine M e)
    request resume w encCaller ScheduleSearch.encState hlive hreq hpre hhalt
    (caller_encoding_le N A guess result hguess) hnext hsize t ht

end Turing.MultiTapePTM.BlockComputation.OuterSearch
