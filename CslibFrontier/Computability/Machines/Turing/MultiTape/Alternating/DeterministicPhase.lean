/-
Copyright (c) 2026 Samuel Schlesinger and Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuessVerify

/-!
# Deterministic native phases with a live continuation

A deterministic machine can be embedded in an alternating controller whose copy of the halted
configuration is a live return state. The first-halt argument gives an exact handoff within the
original clock, without running the controller beyond that handoff. Both alternating moves
agree during the phase; no restriction on the controller's player labels is required.
-/

public section

namespace Turing.MultiTapeATM

variable {k : ℕ} {Symbol S T : Type} {input : List Symbol}
  (atm : MultiTapeATM k Symbol T) {M : MultiTapeTM k Symbol S}
  (lift : Cfg k Symbol S input → Cfg k Symbol T input)
  (hstep : ∀ b c, c.state ≠ none → atm.next b (lift c) = lift (M.step c))

include hstep

private theorem iterate_next_lift (c : Cfg k Symbol S input) :
    ∀ j, (∀ i < j, (M.runFrom c i).state ≠ none) →
      (atm.next false)^[j] (lift c) = lift (M.runFrom c j)
  | 0, _ => rfl
  | j + 1, h => by
    rw [Function.iterate_succ_apply',
      iterate_next_lift c j (fun i hi => h i (by omega)),
      hstep false _ (h j (by omega))]
    simp only [MultiTapeTM.runFrom, Function.iterate_succ_apply']

/-- A certified native run gives a deterministic prefix ending at a live return configuration.
The prefix charges at most the given clock and preserves every field specified by `lift`. -/
theorem exists_deterministic_phase (hlive : ∀ c, (lift c).state ≠ none)
    {c : Cfg k Symbol S input} {t : ℕ} (ht : (M.runFrom c t).state = none) :
    ∃ τ ≤ t,
      (∀ j < τ, ∀ b, atm.next b ((atm.next false)^[j] (lift c)) =
        (atm.next false)^[j + 1] (lift c)) ∧
      (∀ j ≤ τ, ((atm.next false)^[j] (lift c)).state ≠ none) ∧
      (atm.next false)^[τ] (lift c) = lift (M.runFrom c t) := by
  classical
  have hex : ∃ τ, (M.runFrom c τ).state = none := ⟨t, ht⟩
  refine ⟨Nat.find hex, Nat.find_min' hex ht, fun j hj b => ?_, fun j hj => ?_, ?_⟩
  · have hrun : ∀ i < j, (M.runFrom c i).state ≠ none := fun i hi => Nat.find_min hex (by omega)
    rw [Function.iterate_succ_apply', iterate_next_lift atm lift hstep c j hrun,
      hstep b _ (Nat.find_min hex hj), hstep false _ (Nat.find_min hex hj)]
  · rw [iterate_next_lift atm lift hstep c j fun i hi => Nat.find_min hex (by omega)]
    exact hlive _
  · rw [iterate_next_lift atm lift hstep c _ fun i hi => Nat.find_min hex hi,
      MultiTapeTM.runFrom_eq_of_halt M c (Nat.find_min' hex ht) (Nat.find_spec hex)]

end Turing.MultiTapeATM
