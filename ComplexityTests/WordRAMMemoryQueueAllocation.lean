/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Realization.Client.MemoryQueueAllocation
import Complexity.Computability.WordRAM.Realization.Witness

/-! The dirty-memory body ABI and the charged standard list-input ABI are checked separately.
One allocation emitter is reused at independent frontiers, retaining old item words seven. The
supported complete source client also compiles to a flat program. `Data.init` starts its future
cells at zero and is not used as evidence for dirty-item preservation. -/

namespace ComplexityTests.WordRAMMemoryQueueAllocation

open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open MemoryQueueAllocation

private def front {k t : ℕ} : Fin (1 + (k + t)) := ⟨0, by omega⟩
private def src {k t : ℕ} (i : Fin k) : Fin (1 + (k + t)) := Fin.natAdd 1 (Fin.castAdd t i)
private def tmp {k t : ℕ} (i : Fin t) : Fin (1 + (k + t)) := Fin.natAdd 1 (Fin.natAdd k i)

private theorem placement (k t : ℕ) :
    Function.Injective (src (k := k) (t := t)) ∧
    Function.Injective (tmp (k := k) (t := t)) ∧
    (∀ i j, src (t := t) i ≠ tmp (k := k) j) ∧
    (∀ j, tmp (k := k) (t := t) j ≠ front) ∧
    (∀ i, src (k := k) (t := t) i ≠ front) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    simpa only [src, Fin.val_natAdd, Fin.val_castAdd, Nat.add_left_cancel_iff] using this
  · intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    simp only [tmp, Fin.val_natAdd] at this
    omega
  · intro i j h
    have := congrArg Fin.val h
    simp only [src, tmp, Fin.val_natAdd, Fin.val_castAdd] at this
    have := i.isLt
    omega
  · intro i h
    have := congrArg Fin.val h
    simp only [tmp, front, Fin.val_natAdd] at this
    omega
  · intro i h
    have := congrArg Fin.val h
    simp only [src, front, Fin.val_natAdd, Fin.val_castAdd] at this
    omega

private def packed {k t : ℕ} (v : Fin k → ℕ) (s : Memory.State) : Data (1 + (k + t)) :=
  ⟨Fin.addCases (fun _ => s.frontier) (Fin.addCases v (fun _ => 0)), s.mem⟩

private theorem packed_bounded {k t w : ℕ} {v : Fin k → ℕ} {s : Memory.State}
    (hv : ∀ i, Fits w (v i)) (hs : Memory.WellFormed w s) :
    (packed (t := t) v s).Bounded w := by
  refine ⟨fun i => ?_, hs.mem_fits⟩
  refine Fin.addCases (fun _ => by simpa [packed] using hs.frontier_fits) (fun j => ?_) i
  exact Fin.addCases (fun i => by simpa [packed] using hv i) (fun _ => by simp [packed]) j

private theorem packed_input {k t : ℕ} (v : Fin k → ℕ) (s : Memory.State) :
    (packed (t := t) v s).regs ∘ src = v := by
  funext i
  simp [packed, src]

private theorem packed_state {k t : ℕ} (v : Fin k → ℕ) (s : Memory.State) :
    memoryState front (packed (t := t) v s) = s := by
  cases s
  rfl

private def dirty (f : ℕ) : Memory.State := ⟨fun _ => 7, f⟩
private theorem dirty_wf {f : ℕ} (hf : Fits 4 f) : Memory.WellFormed 4 (dirty f) :=
  ⟨hf, fun _ => by change Fits 4 7; decide⟩

private theorem allocation :
    Realizes .exact allocPair (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding MemoryQueue.layoutWords
      (fun w C s => Fits w (s.frontier + 2 * (C + 1))) (fun _ _ => 42) := realizes_allocPair
private noncomputable def allocationCode := allocation.code
  (front (k := 1) (t := 8 + allocation.scratchSize + 1)) src tmp
private noncomputable def allocationData (C : ℕ) (s : Memory.State) :=
  packed (t := 8 + allocation.scratchSize + 1) (fun _ : Fin 1 => C) s

private theorem allocation_execution (w C : ℕ) (s : Memory.State) (hw : Memory.WellFormed w s)
    (hf : Fits w (s.frontier + 2 * (C + 1))) :
    ∃ y, ExecWithin w allocationCode (allocationData C s) y (allocation.factor * 49) ∧
      memoryState front y = Queue.Memory.allocated s C ∧
      ∀ i : Fin 8, y.regs (tmp (Fin.castAdd (allocation.scratchSize + 1) i)) =
        MemoryQueue.layoutWords (Queue.Memory.frontLayout s C, Queue.Memory.rearLayout s C) i := by
  obtain ⟨_, hi, hd, hfr, hs⟩ := placement 1 (8 + allocation.scratchSize + 1)
  have hx : (allocationData C s).Bounded w := packed_bounded (fun _ => hf.of_le (by omega)) hw
  have hin := packed_input (t := 8 + allocation.scratchSize + 1) (fun _ : Fin 1 => C) s
  have hm : memoryState front (allocationData C s) = s :=
    packed_state (t := 8 + allocation.scratchSize + 1) (fun _ : Fin 1 => C) s
  obtain ⟨y, he, hmem, hout, _⟩ := (allocation.code_spec front src tmp hi hd hfr hs).2
    w C (allocationData C s) hx hin (hm ▸ hf) (hm ▸ valid_allocPair hf)
  rw [hm] at he hmem hout
  rw [allocPair_memoryCost] at he
  exact ⟨y, he, hmem, hout⟩

-- The SAME emitter is used at frontiers three and five. Items retain seven, so clearing the
-- whole allocated block would not realize this source initializer.
example (f : ℕ) (hf : f = 3 ∨ f = 5) :
    ∃ y, ExecWithin 4 allocationCode (allocationData 2 (dirty f)) y (allocation.factor * 49) ∧
      y.regs (tmp (Fin.castAdd (allocation.scratchSize + 1) 0)) = f ∧
      y.mem f = 0 ∧ y.mem (f + 3) = 0 ∧ y.mem (f + 1) = 7 ∧
      y.mem (f + 2) = 7 ∧ y.mem 100 = 7 ∧ y.regs front = f + 6 := by
  have hf' : Fits 4 f := by rcases hf with rfl | rfl <;> decide
  have hend : Fits 4 ((dirty f).frontier + 2 * (2 + 1)) := by
    rcases hf with rfl | rfl <;> decide
  obtain ⟨y, he, hm, hout⟩ := allocation_execution 4 2 (dirty f) (dirty_wf hf') hend
  refine ⟨y, he, hout 0, ?_, ?_, ?_, ?_, ?_, congrArg Memory.State.frontier hm⟩
  all_goals
    rcases hf with rfl | rfl
    all_goals first
      | exact congrArg (fun s : Memory.State => s.mem 3) hm
      | exact congrArg (fun s : Memory.State => s.mem 6) hm
      | exact congrArg (fun s : Memory.State => s.mem 4) hm
      | exact congrArg (fun s : Memory.State => s.mem 5) hm
      | exact congrArg (fun s : Memory.State => s.mem 8) hm
      | exact congrArg (fun s : Memory.State => s.mem 7) hm
      | exact congrArg (fun s : Memory.State => s.mem 100) hm

private theorem client :
    Realizes .exact (fun d : ℕ × ℕ => Queue.Memory.run 0 d.1 (roundTrip 0 d.1 d.2))
      roundTripWords optionWords
      (fun w d s => 1 ≤ d.1 ∧ Fits w (s.frontier + 2 * (d.1 + 1)))
      (fun _ _ => 163) := realizes_roundTrip 0
private noncomputable def clientCode := client.code
  (front (k := 2) (t := 2 + client.scratchSize + 1)) src tmp
private noncomputable def clientData (C v : ℕ) (s : Memory.State) :=
  packed (t := 2 + client.scratchSize + 1) (roundTripWords (C, v)) s

private theorem client_execution (w C v : ℕ) (s : Memory.State) (hw : Memory.WellFormed w s)
    (hC : 1 ≤ C) (hv : Fits w v) (hf : Fits w (s.frontier + 2 * (C + 1))) :
    ∃ y, ExecWithin w clientCode (clientData C v s) y
        (client.factor * (memoryCost (Queue.Memory.run 0 C (roundTrip 0 C v)) s + 164)) ∧
      memoryState front y = (Memory.spec w).clientState s
        (Queue.Memory.run 0 C (roundTrip 0 C v)) ∧
      y.regs (tmp (Fin.castAdd (client.scratchSize + 1) 0)) = 1 ∧
      y.regs (tmp (Fin.castAdd (client.scratchSize + 1) 1)) = v := by
  obtain ⟨_, hi, hd, hfr, hs⟩ := placement 2 (2 + client.scratchSize + 1)
  have hwords (i : Fin 2) : Fits w (roundTripWords (C, v) i) := by
    fin_cases i
    · change Fits w C; exact hf.of_le (by omega)
    · change Fits w v; exact hv
  have hx : (clientData C v s).Bounded w := packed_bounded hwords hw
  have hin := packed_input (t := 2 + client.scratchSize + 1) (roundTripWords (C, v)) s
  have hm : memoryState front (clientData C v s) = s :=
    packed_state (t := 2 + client.scratchSize + 1) (roundTripWords (C, v)) s
  have hc := roundTrip_correct_source 0 hC hv hf
  obtain ⟨y, he, hmem, hout, _⟩ := (client.code_spec front src tmp hi hd hfr hs).2
    w (C, v) (clientData C v s) hx hin (hm ▸ And.intro hC hf) (hm ▸ hc.1)
  rw [hm] at he hmem hout
  rw [hc.2] at hout
  exact ⟨y, he, hmem, hout 0, hout 1⟩

private theorem client_program_execution (w C v : ℕ) (s : Memory.State)
    (hw : Memory.WellFormed w s) (hC : 1 ≤ C) (hv : Fits w v)
    (hf : Fits w (s.frontier + 2 * (C + 1))) :
    ∃ y n, Runs w
        (clientCode.program (tmp (Fin.castAdd (client.scratchSize + 1) 1)))
        ⟨0, clientData C v s⟩ ⟨clientCode.size, y⟩ n ∧
      step w (clientCode.program (tmp (Fin.castAdd (client.scratchSize + 1) 1)))
        ⟨clientCode.size, y⟩ = .halt v ∧
      n + 1 ≤ client.factor *
        (memoryCost (Queue.Memory.run 0 C (roundTrip 0 C v)) s + 164) + 1 ∧
      memoryState front y = (Memory.spec w).clientState s
        (Queue.Memory.run 0 C (roundTrip 0 C v)) ∧
      y.regs (tmp (Fin.castAdd (client.scratchSize + 1) 0)) = 1 := by
  obtain ⟨y, ⟨n, hn, he⟩, hm, ht, hv⟩ := client_execution w C v s hw hC hv hf
  have hr := he.runs (pc := 0)
    (p := clientCode.program (tmp (Fin.castAdd (client.scratchSize + 1) 1)))
    (Program.Contains.self _).append_left
  refine ⟨y, n, ?_, ?_, Nat.add_le_add_right hn 1, hm, ht⟩
  · simpa only [Nat.zero_add] using hr
  · rw [← hv]
    exact step_halt (by simp [Code.program])

-- Exact concrete grades: initialization is memory6/work42; the supported whole client is
-- memory20/work163. Old inactive item cells and the inaccessible tail stay seven.
example : memoryCost (allocPair 2) (dirty 3) = 6 := rfl
example : memoryCost (Queue.Memory.run 0 2 (roundTrip 0 2 15)) (dirty 3) = 20 := by decide

example : ∃ y, ExecWithin 4 clientCode (clientData 2 15 (dirty 3)) y (client.factor * 184) ∧
    y.regs (tmp (Fin.castAdd (client.scratchSize + 1) 0)) = 1 ∧
    y.regs (tmp (Fin.castAdd (client.scratchSize + 1) 1)) = 15 ∧
    y.mem 3 = 0 ∧ y.mem 6 = 0 ∧ y.mem 5 = 7 ∧ y.mem 8 = 7 ∧ y.mem 100 = 7 ∧
    y.regs front = 9 := by
  obtain ⟨y, he, hm, ht, hv⟩ := client_execution 4 2 15 (dirty 3)
    (dirty_wf (by decide)) (by decide) (by decide) (by decide)
  refine ⟨y, he, ht, hv, ?_, ?_, ?_, ?_, ?_, congrArg Memory.State.frontier hm⟩
  · exact congrArg (fun s : Memory.State => s.mem 3) hm
  · exact congrArg (fun s : Memory.State => s.mem 6) hm
  · exact congrArg (fun s : Memory.State => s.mem 5) hm
  · exact congrArg (fun s : Memory.State => s.mem 8) hm
  · exact congrArg (fun s : Memory.State => s.mem 100) hm

-- Flat compilation retains that same final Data, then charges the trailing halt. Inputs here
-- are already installed; this is the arbitrary dirty-memory ABI, not the Data.init ABI.
example : ∃ y n, Runs 4
      (clientCode.program (tmp (Fin.castAdd (client.scratchSize + 1) 1)))
      ⟨0, clientData 2 15 (dirty 3)⟩ ⟨clientCode.size, y⟩ n ∧
    step 4 (clientCode.program (tmp (Fin.castAdd (client.scratchSize + 1) 1)))
      ⟨clientCode.size, y⟩ = .halt 15 ∧ n + 1 ≤ client.factor * 184 + 1 ∧
    y.regs (tmp (Fin.castAdd (client.scratchSize + 1) 0)) = 1 ∧
    y.mem 5 = 7 ∧ y.mem 100 = 7 ∧ y.regs front = 9 := by
  obtain ⟨y, n, hr, hh, hn, hm, ht⟩ := client_program_execution 4 2 15 (dirty 3)
    (dirty_wf (by decide)) (by decide) (by decide) (by decide)
  refine ⟨y, n, hr, hh, hn, ht, ?_, ?_, congrArg Memory.State.frontier hm⟩
  · exact congrArg (fun s : Memory.State => s.mem 5) hm
  · exact congrArg (fun s : Memory.State => s.mem 100) hm

-- The separate standard-input endpoint uses the existing charged prefix: one flat program
-- precedes physical width, capacity and value. Future Data.init cells are initially zero.
example : ∃ r K, ∃ p : Program .exact r, ∀ w C v, 1 ≤ C → Fits w v →
    Fits w (3 + 2 * (C + 1)) → ∃ t, Executes w p (State.init [C, v]) v t ∧
      t ≤ K * (memoryCost (Queue.Memory.run 0 C (roundTrip 0 C v))
        (inputState [C, v]) + 164) + 1 := by
  obtain ⟨n, K, emit, he⟩ := client.exists_init_program (fun d : ℕ × ℕ => [d.1, d.2])
    (by intro d i; fin_cases i <;> rfl)
  obtain ⟨hsrc, hi, hd, hfr, hs⟩ := placement 2 (2 + n + 1)
  refine ⟨_, K, (Code.seq
    (inputPrefix (front (k := 2) (t := 2 + n + 1)) (tmp (Fin.last (2 + n))) src)
    (emit front src tmp)).program (tmp (Fin.castAdd (n + 1) 1)), ?_⟩
  intro w C v hC hv hf
  have hin : InputFits w [C, v] := by
    refine ⟨?_, ?_⟩
    · change Fits w 2
      exact hf.of_le (by omega)
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hf.of_le (by omega)
    · exact hv
  have hc := roundTrip_correct_source 0 (s := inputState [C, v]) hC hv hf
  obtain ⟨t, ht, hbound⟩ := he front src tmp hsrc hi hd hfr hs 1 w (C, v)
    (by change 2 ≤ 2; omega) (by change Fits w 3; exact hf.of_le (by omega)) hin ⟨hC, hf⟩ hc.1
  rw [hc.2] at ht
  exact ⟨t, ht, hbound⟩

end ComplexityTests.WordRAMMemoryQueueAllocation
