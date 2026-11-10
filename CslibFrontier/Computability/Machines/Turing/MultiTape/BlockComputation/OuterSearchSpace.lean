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
@[expose] noncomputable def callerSpace (N G : ℕ) : ℕ :=
  8 * ((encNat N).length + (encNat G).length + 1)

/-- Maximum storage of one candidate search through the largest permitted guess `G`, for
evaluator allowance `A` and parameters `P`. -/
@[expose] noncomputable def candidateSpace (k : ℕ) (A : ℕ → ℕ → ℕ → ℕ) (P : Parameters)
    (N G : ℕ) : ℕ :=
  (Finset.range (G + 1)).sup fun guess =>
    ScheduleSearch.space k A N (P.blockWidth guess) (P.horizon guess)

/-- One suspended caller beside one candidate, with complete sum and product framing. -/
@[expose] noncomputable def space (k : ℕ) (A : ℕ → ℕ → ℕ → ℕ) (P : Parameters) (N G : ℕ) : ℕ :=
  2 * callerSpace N G + candidateSpace k A P N G + 2

/-- Any candidate through the bounded guess fits the same supremum allowance. -/
theorem candidate_space_le (k : ℕ) (A : ℕ → ℕ → ℕ → ℕ) (P : Parameters) (N G guess : ℕ)
    (hguess : guess ≤ G) :
    ScheduleSearch.space k A N (P.blockWidth guess) (P.horizon guess) ≤
      candidateSpace k A P N G :=
  Finset.le_sup (f := fun guess =>
    ScheduleSearch.space k A N (P.blockWidth guess) (P.horizon guess))
    (Finset.mem_range.mpr (by omega))

/-- Binary caller storage is uniform through the largest permitted time guess. -/
theorem caller_encoding_le (N G guess : ℕ) (result : Option Bool) (hguess : guess ≤ G) :
    (encCaller (N, guess, result)).length ≤ callerSpace N G := by
  have hg := length_encNat_mono hguess
  have hr : (encOption encBool result).length ≤ 2 := by
    cases result <;> simp only [encOption_none, encOption_some, List.length_nil,
      List.length_cons, encBool_apply] <;> omega
  simp only [encCaller, length_encPair, callerSpace]
  omega

/-- Every physical clock of a bounded candidate call charges its suspended caller and callee. -/
theorem runFrom_one_encoding_le {k : ℕ} (E : ScheduleSearch.Evaluator) (A : ℕ → ℕ → ℕ → ℕ)
    (P : Parameters) (N guess G : ℕ) (result : Option Bool)
    (w : List Bool) (T : ℕ) (hpending : pending (N, guess, result) = true)
    (hguess : guess ≤ G)
    (hpre : ∀ u < T, (ScheduleSearch.machine E k).halted
      ((ScheduleSearch.machine E k).runFrom w (ScheduleSearch.initial E
        (N, P.blockWidth guess, P.horizon guess)) u) = false)
    (hhalt : (ScheduleSearch.machine E k).halted ((ScheduleSearch.machine E k).runFrom w
      (ScheduleSearch.initial E (N, P.blockWidth guess, P.horizon guess)) T) = true)
    (hsize : ∀ u ≤ T, (ScheduleSearch.encState E ((ScheduleSearch.machine E k).runFrom w
      (ScheduleSearch.initial E (N, P.blockWidth guess, P.horizon guess)) u)).length ≤
          candidateSpace k A P N G)
    (hnext : (encCaller (resume E (N, guess, result) ((ScheduleSearch.machine E k).runFrom w
      (ScheduleSearch.initial E (N, P.blockWidth guess, P.horizon guess)) T))).length ≤
          callerSpace N G)
    (t : ℕ) (ht : t ≤ T + 2) :
    (encState E ((machine E k P).runFrom w (.inl (N, guess, result)) t)).length ≤
      space k A P N G := by
  have hreq : request E P (N, guess, result) = some (ScheduleSearch.initial E
      (N, P.blockWidth guess, P.horizon guess)) := by
    simp only [request, hpending, ↓reduceIte, parameters]
  have hlive : caller.halted (N, guess, result) = false := by
    simp only [caller, hpending, Bool.not_true]
  exact QueryMachine.withCalls_runFrom_call_encoding_le caller (ScheduleSearch.machine E k)
    (request E P) (resume E) w encCaller (ScheduleSearch.encState E) hlive hreq hpre hhalt
    (caller_encoding_le N G guess result hguess) hnext hsize t ht

end Turing.MultiTapePTM.BlockComputation.OuterSearch
