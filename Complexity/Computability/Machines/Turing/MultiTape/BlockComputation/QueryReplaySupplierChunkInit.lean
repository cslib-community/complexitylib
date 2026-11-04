/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySupplierChunk
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySupplierBounds
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.FirstHalt

/-!
# Native initialization and bounds for packed local answers

The requested chunk metadata accompanies the existing checked Boolean supplier. Initialization
is native, every clock charges both retained metadata and actual replay storage, and stopping
is inherited from the checked local call. The original input is never copied into this state.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.SupplierChunk

open MultiTapeTM MultiTapeTM.ComputableInSpace MultiTapeNTM.ChoiceTable

variable {k s : ℕ} {Q : Type}

/-- Requested chunk metadata and actual checked-supplier initialization arguments. -/
abbrev Args := Context × Supplier.Args

/-- Actual binary metadata and assignment-counter storage. -/
@[expose] noncomputable def encArgs : Args ↪ List Bool := encPair encContext Supplier.encArgs

/-- Prepare the checked replay while retaining the requested packed chunk. -/
@[expose] noncomputable def prepare (e : Q ≃ Fin s) : Args → State k Q :=
  fun (context, args) => (context, Supplier.prepare e args)

variable [Finite Q]

/-- Packed-answer preparation uses space linear in the actual binary argument storage. -/
theorem prepare_inSpace (e : Q ≃ Fin s) :
    ComputableInSpace (prepare (k := k) e) encArgs encState
      (fun a => (encArgs a).length) :=
  budget_prod (fst encContext Supplier.encArgs)
    (budget_comp_linear (Supplier.prepare_inSpace (k := k) e)
      (snd encContext Supplier.encArgs))

/-- Every clock includes the requested chunk metadata and the complete checked replay state. -/
theorem length_runFrom_prepare_le (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (b : ℕ) [NeZero b] (σ i limit counter stride m chunk t : ℕ) :
    let (positive, negative) := ScheduleRead.origin k 0 (σ, i)
    (encState ((machine M e).runFrom w
      (prepare e ((m, chunk), (w.length, b, σ, i, limit, counter, stride))) t)).length ≤
      2 * (encContext (m, chunk)).length + 1 + (Encoding.width k s b + 1) +
        (2 * (Gate.encContext
          (positive, negative, ScheduleRead.fullrow k (σ, i))).length + 2 +
          1024 * (k + 1) * (b + Nat.log2 w.length + Nat.card (Option Q) +
            Nat.card OutputTrack + 1)) := by
  rw [prepare, runFrom_eq]
  have h := Supplier.length_runFrom_prepare_le M e w b σ i limit counter stride t
  dsimp only at h ⊢
  simp only [encState, length_encPair]
  omega

omit [Finite Q] in
/-- Requested chunk metadata does not delay stopping of a checked local call. -/
theorem halted_runFrom_prepare (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (N b σ i limit counter stride m chunk : ℕ) :
    (machine M e).halted ((machine M e).runFrom w
      (prepare e ((m, chunk), (N, b, σ, i, limit, counter, stride))) b) = true := by
  rw [prepare, runFrom_eq]
  exact Supplier.halted_runFrom_prepare M e w N b σ i limit counter stride

omit [Finite Q] in
/-- A prepared numeric supplier has the exact first-return clock needed by the same-input
call rules, and returns the state used by the packed-answer correctness theorem. -/
theorem exists_first_return (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (N b σ i limit counter stride m chunk : ℕ) :
    let start := prepare e ((m, chunk), (N, b, σ, i, limit, counter, stride))
    ∃ T, T ≤ b ∧ (machine M e).halted ((machine M e).runFrom w start T) = true ∧
      (∀ t < T, (machine M e).halted ((machine M e).runFrom w start t) = false) ∧
      (machine M e).runFrom w start T = (machine M e).runFrom w start b := by
  exact QueryMachine.exists_first_halt_le _ w _ b
    (halted_runFrom_prepare M e w N b σ i limit counter stride m chunk)

end Turing.MultiTapePTM.BlockComputation.QueryReplay.SupplierChunk
