/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PriorityQueue.FibonacciHeap

/-!
# Concrete interpreter and non-vacuity tests for `PriorityQueue.FibonacciHeap`

Exercises `FibonacciHeap` on the concrete `Cslib.WordRAM.Code.eval` interpreter over `Basis.exact`:

* equal-key lexicographic `(key, handle)` tie-breaking in `extractMin`;
* `9`-element degree-table consolidation into a degree-`3` tree with `cons[0..9]` restored to `0`;
* genuine multi-level cascading cuts during `decreaseKey` (`mark[5] : 0 → 1 → 0`, cutting both the
  child and its marked parent to the root list);
* `initClear` on dirty memory with adjacent boundary-sentinel preservation;
* non-vacuity instantiations of `run_ops_exact_fresh`, `run_ops_exact_reusable`, and `amortized`.
-/

@[expose] public section

open Cslib Cslib.WordRAM Cslib.Algorithms.Lean
open Cslib.Algorithms.WordRAM.PriorityQueue
open Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap

namespace WordRAMFibonacciHeapTests

/-- Rebuild a natural number from `0` and `Nat.succ` so that all `Function.update` closures in its
originating expression are eliminated during kernel reduction. -/
def forceNat : ℕ → Option ℕ
  | 0 => some 0
  | n + 1 => (forceNat n).map Nat.succ

/-- Eagerly force every element of a list of natural numbers via `forceNat`. -/
def forceList : List ℕ → Option (List ℕ)
  | [] => some []
  | x :: xs =>
    match forceNat x, forceList xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none

/-- Tabulate registers `0..rFib - 1` and memory `0..memCap - 1` into flat lists between
interpreter calls so `Function.update` closures do not compound exponentially across operations. -/
def compactData (memCap : ℕ) (d : Data rFib) : Option (Data rFib) := do
  let rs ← forceList ((List.finRange rFib).map d.regs)
  let ms ← forceList ((List.range memCap).map d.mem)
  let tail ← forceNat (d.mem memCap)
  pure
    { regs := fun i => rs.getD i.val 0
      mem := fun a => if a < memCap then ms.getD a 0 else tail }

/-- Run a single operation `o` via `dispatchCode.eval` at word size `w` and loop fuel `fuel`,
compacting the resulting state and accumulating total instruction steps. -/
def stepEval {n : ℕ} (w fuel : ℕ) (dt : Data rFib × ℕ) (o : IndexedMinPQ.Op n) :
    Option (Data rFib × ℕ) := do
  let (d', t) ← dispatchCode.eval w fuel ⟨prepareRegs o dt.1.regs, dt.1.mem⟩
  let dc ← compactData 105 d'
  pure (dc, dt.2 + t)

/-- Run a sequence of operations via `stepEval`. -/
def seqEval {n : ℕ} (w fuel : ℕ) :
    Option (Data rFib × ℕ) → List (IndexedMinPQ.Op n) → Option (Data rFib × ℕ)
  | none, _ => none
  | some dt, [] => some dt
  | some dt, o :: ops => seqEval w fuel (stepEval w fuel dt o) ops

/-- Repeatedly run `extractMin` `k` times and collect the decoded `Option (ℕ × ℕ)` outputs. -/
def extractAll {n : ℕ} (w fuel : ℕ) :
    ℕ → Data rFib → Option (List (Option (ℕ × ℕ)) × Data rFib)
  | 0, d => some ([], d)
  | k + 1, d => do
    let (d', _) ← dispatchCode.eval w fuel ⟨prepareRegs (n := n) .extractMin d.regs, d.mem⟩
    let dc ← compactData 105 d'
    let item := if dc.regs outFlag = 0 then none else some (dc.regs outV, dc.regs outK)
    let res ← extractAll (n := n) w fuel k dc
    pure (item :: res.1, res.2)

/-! ### 1. Equal-key lexicographic tie-breaking, `isEmpty`, and `getKey` -/

/-- Inserting handles `3`, `1`, `2` with equal key `7` extracts `(1, 7)`, `(2, 7)`, `(3, 7)` in
strict handle order, and then `none`. -/
example :
    (do
      let d0 ← code.toSubroutineCode.initFresh.eval 12 16 ⟨initRegs 4 10, fun _ => 0⟩
      let d1 ← stepEval (n := 4) 12 16 d0 .isEmpty
      let d2 ← seqEval (n := 4) 12 16 (some d1) [.insert 3 7, .insert 1 7, .insert 2 7]
      let d3 ← stepEval (n := 4) 12 16 d2 .isEmpty
      let d4 ← stepEval (n := 4) 12 16 d3 (.getKey 1)
      let d5 ← stepEval (n := 4) 12 16 d4 (.getKey 0)
      let (exts, _) ← extractAll (n := 4) 12 16 4 d5.1
      let summary : List ℕ :=
        [d1.1.regs outFlag, d3.1.regs outFlag, d4.1.regs outFlag, d4.1.regs outK,
         d5.1.regs outFlag]
      pure (summary, exts)) =
    some ([1, 0, 1, 7, 0], [some (1, 7), some (2, 7), some (3, 7), none]) := by
  decide +kernel

/-! ### 2. Degree-table consolidation and genuine cascading cuts (`n = 9`) -/

/-- Nine inserts followed by `extractMin` consolidate the remaining `8` nodes into a single
degree-`3` tree rooted at `1` while clearing `cons[0..9]` back to `0`; subsequent `decreaseKey`s on
both children `6` and `7` of non-root `5` first mark `5` (`mark[5] = 1`) and then trigger a
cascading cut (`par[5] = 0`, `mark[5] = 0`, `numMarked = 0`). -/
example :
    (do
      let d0 ← code.toSubroutineCode.initFresh.eval 12 32 ⟨initRegs 9 10, fun _ => 0⟩
      let d1 ← seqEval (n := 9) 12 32 (some d0)
        [.insert 0 10, .insert 1 20, .insert 2 30, .insert 3 40, .insert 4 50,
         .insert 5 60, .insert 6 70, .insert 7 80, .insert 8 90]
      let d2 ← stepEval (n := 9) 12 32 d1 .extractMin
      let consVals := (List.range 10).map fun deg => d2.1.mem (10 + 8 * 9 + deg)
      let d3 ← stepEval (n := 9) 12 32 d2 (.decreaseKey 6 5)
      let d4 ← stepEval (n := 9) 12 32 d3 (.decreaseKey 7 4)
      let (exts, _) ← extractAll (n := 9) 12 16 3 d4.1
      let stats : List ℕ :=
        [d2.1.regs outFlag, d2.1.regs outV, d2.1.regs outK,
         d2.1.regs numRootsReg, d2.1.mem (10 + 5 * 9 + 1),
         d2.1.mem (10 + 9 + 5), d2.1.mem (10 + 5 * 9 + 5), d2.1.mem (10 + 6 * 9 + 5),
         d3.1.mem (10 + 9 + 5), d3.1.mem (10 + 6 * 9 + 5), d3.1.regs numMarkedReg,
         d4.1.mem (10 + 9 + 5), d4.1.mem (10 + 6 * 9 + 5),
         d4.1.regs numMarkedReg, d4.1.regs numRootsReg] ++ consVals
      pure (stats, exts)) =
    some ([1, 0, 10, 1, 3, 2, 2, 0, 2, 1, 1, 0, 0, 0, 4] ++ List.replicate 10 0,
      [some (7, 4), some (6, 5), some (1, 20)]) := by
  decide +kernel

/-! ### 3. `initClear` on dirty memory and boundary-sentinel preservation -/

/-- Dirty initial memory on `n = 3, base = 10` (`[10, 38)`), with sentinels `77` at address `9`
and `88` at address `38`, and garbage `99` everywhere else. -/
def dirtyMem (a : ℕ) : ℕ :=
  if a = 9 then 77 else if a = 38 then 88 else 99

example :
    (do
      let (d0Raw, t0) ← code.toSubroutineCode.initClear.eval 12 64 ⟨initRegs 3 10, dirtyMem⟩
      let d0 ← compactData 105 d0Raw
      let d1 ← seqEval (n := 3) 12 32 (some (d0, t0)) [.insert 2 15, .insert 0 15, .decreaseKey 2 9]
      let (exts, df) ← extractAll (n := 3) 12 32 3 d1.1
      pure (exts, df.mem 9, df.mem 38)) =
    some ([some (2, 9), some (0, 15), none], 77, 88) := by
  decide +kernel

/-! ### 4. Non-vacuity of standalone theorems -/

/-- Concrete admissible sequence exercising all five operation constructors. -/
def sampleOps : List (IndexedMinPQ.Op 4) :=
  [.insert 2 30, .insert 1 30, .decreaseKey 2 10, .getKey 2, .extractMin, .isEmpty]

theorem sampleOps_valid :
    (IndexedMinPQ.spec 4 50).ValidHistory (IndexedMinPQ.empty 4) sampleOps := by
  refine ⟨⟨rfl, by decide⟩, ⟨⟨by decide, by decide⟩, ⟨⟨⟨30, rfl, by decide⟩, by decide⟩,
    ⟨trivial, ⟨trivial, ⟨trivial, trivial⟩⟩⟩⟩⟩⟩

/-- Non-vacuity of `run_ops_exact_fresh`: concrete non-empty execution on zeroed `[8, 45)` with
outside sentinel at address `0`. -/
example :
    ∃ pc₀ x₀ t_init z t_ops,
      Runs 10 initFreshProg ⟨0, ⟨initRegs 4 8, fun a => if a = 0 then 99 else 0⟩⟩ ⟨pc₀, x₀⟩
        t_init ∧
      (∃ out, step 10 initFreshProg ⟨pc₀, x₀⟩ = .halt out) ∧
      RunsOps (K_max := 50) 10 8 (IndexedMinPQ.empty 4) x₀ sampleOps z t_ops ∧
      x₀.mem 0 = 99 ∧
      t_init + 1 ≤ 421 ∧
      t_ops ≤ 421 * 8 := by
  have hS : Fits 10 (8 + space 4) := by unfold space Fits; decide
  have hK : Fits 10 50 := by decide
  have hmem : ∀ a, Fits 10 (if a = 0 then 99 else 0) := fun a => by split_ifs <;> decide
  have hzero : ∀ a ∈ (Block.mk 8 (space 4)).footprint, (if a = 0 then 99 else 0) = 0 := by
    intro a ha
    rw [Block.mem_footprint, Block.Owns] at ha
    dsimp only at ha
    have ha0 : a ≠ 0 := by omega
    simp [ha0]
  obtain ⟨pc₀, x₀, t_init, z, t_ops, hr₀, hh₀, hmod₀, hruns, ht_init, ht_ops⟩ :=
    run_ops_exact_fresh hS hK hmem hzero sampleOps sampleOps_valid
  have hlog : Nat.log 2 4 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  have hm0 : x₀.mem 0 = 99 := by
    have h := hmod₀ 0 (by rw [Block.mem_footprint, Block.Owns]; dsimp only [space]; omega)
    simpa using h
  refine ⟨pc₀, x₀, t_init, z, t_ops, hr₀, hh₀, hruns, hm0, ht_init, ?_⟩
  simp only [sampleOps, numQueries, numInserts, numDecreaseKeys, numExtractMins, hlog] at ht_ops
  omega

/-- Non-vacuity of `run_ops_exact_reusable` on dirty memory (`mem₀ a = 77`). -/
example :
    ∃ pc₀ x₀ t_init z t_ops,
      Runs 10 initClearProg ⟨0, ⟨initRegs 4 8, fun _ => 77⟩⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step 10 initClearProg ⟨pc₀, x₀⟩ = .halt out) ∧
      RunsOps (K_max := 50) 10 8 (IndexedMinPQ.empty 4) x₀ sampleOps z t_ops ∧
      x₀.mem 0 = 77 ∧
      t_init + 1 ≤ 421 * 5 ∧
      t_ops ≤ 421 * 8 := by
  have hS : Fits 10 (8 + space 4) := by unfold space Fits; decide
  have hK : Fits 10 50 := by decide
  have hmem : ∀ _ : ℕ, Fits 10 77 := fun _ => by decide
  obtain ⟨pc₀, x₀, t_init, z, t_ops, hr₀, hh₀, hmod₀, hruns, ht_init, ht_ops⟩ :=
    run_ops_exact_reusable hS hK hmem sampleOps sampleOps_valid
  have hlog : Nat.log 2 4 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  have hm0 : x₀.mem 0 = 77 :=
    hmod₀ 0 (by rw [Block.mem_footprint, Block.Owns]; dsimp only [space]; omega)
  refine ⟨pc₀, x₀, t_init, z, t_ops, hr₀, hh₀, hruns, hm0, ht_init, ?_⟩
  simp only [sampleOps, numQueries, numInserts, numDecreaseKeys, numExtractMins, hlog] at ht_ops
  omega

/-- Non-vacuity of the `Stateful.Amortized` certificate over `Basis.standard`. -/
example :
    let hS : Fits 10 (8 + space 4) := by unfold space Fits; decide
    let hK : Fits 10 50 := by decide
    Stateful.Amortized (certificate hS hK).realization
      DynamicProgram.OperationTrace.instructions
      (fun _ x => potential x)
      (fun s o => charge 4 s o + 1) :=
  amortized _ _

/-- Lift a single `IndexedMinPQ` operation into `Client` for `spec 4 50`. -/
abbrev callOp (o : IndexedMinPQ.Op 4) :
    (IndexedMinPQ.spec 4 50).Client ((IndexedMinPQ.spec 4 50).Result o) :=
  PFunctor.FreeM.lift (P := (IndexedMinPQ.spec 4 50).signature) o

/-- Concrete adaptive client inserting `(2, 8)` and `(1, 8)`, decreasing `2` to `0`, and extracting
the minimum. -/
def sampleClient : (IndexedMinPQ.spec 4 50).Client (Option (Fin 4 × ℕ)) := do
  callOp (.insert 2 8)
  callOp (.insert 1 8)
  callOp (.decreaseKey 2 0)
  callOp .extractMin

/-- Non-vacuity of `subroutineDS`, `FibInv`, and `run_client_amortized` over `Basis.standard`:
initializes `y₀` from zeroed memory with `potential y₀ = 0` and executes `sampleClient` returning
`some (2, 0)`. -/
example :
    let hS : Fits 10 (8 + space 4) := by unfold space Fits; decide
    let hK : Fits 10 50 := by decide
    ∃ y₀ y traces,
      FibInv 4 50 10 8 (IndexedMinPQ.empty 4) y₀ ∧
      potential y₀ = 0 ∧
      Stateful.Executes ((dynamicProgram hS hK).ExecOp 10) sampleClient y₀
        (some (2, 0)) y traces ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces + potential y ≤
        (IndexedMinPQ.spec 4 50).totalCost (fun s o => charge 4 s o + 1)
          (IndexedMinPQ.empty 4)
          ((IndexedMinPQ.spec 4 50).runClient (IndexedMinPQ.empty 4) sampleClient).2.2 := by
  intro hS hK
  let x₀ : Data rFib := ⟨initRegs 4 8, fun _ => 0⟩
  have hx₀ : x₀.Bounded 10 :=
    ⟨fun i => by fin_cases i <;> decide, fun _ => show Fits 10 0 by decide⟩
  have hfr : x₀.regs frontierReg = 8 := by decide
  have hpar : ∀ j : Fin 1, x₀.regs (![nReg] j) = ![4] j := fun j => by fin_cases j; rfl
  have hz : ∀ a ∈ (Block.mk 8 (space 4)).footprint, x₀.mem a = 0 := fun _ _ => rfl
  obtain ⟨y₀, _, _, hr₀, hpot₀, _⟩ :=
    (subroutineDS (K_max := 50) hS hK).initFresh_exec hx₀ hfr hpar hz
  have hp₀ : potential y₀ = 0 := Nat.eq_zero_of_le_zero hpot₀
  have hhist : ((IndexedMinPQ.spec 4 50).runClient (IndexedMinPQ.empty 4) sampleClient).2.2 =
      [.insert 2 8, .insert 1 8, .decreaseKey 2 0, .extractMin] := rfl
  have hv : (IndexedMinPQ.spec 4 50).ValidHistory (IndexedMinPQ.empty 4)
      ((IndexedMinPQ.spec 4 50).runClient (IndexedMinPQ.empty 4) sampleClient).2.2 := by
    rw [hhist]
    simp [Stateful.Spec.ValidHistory, IndexedMinPQ.spec, IndexedMinPQ.empty]
  have hres : ((IndexedMinPQ.spec 4 50).runClient (IndexedMinPQ.empty 4) sampleClient).1 =
      some (2, 0) := by
    decide
  obtain ⟨y, traces, hex, _, hcost⟩ := run_client_amortized hS hK sampleClient hr₀ hv
  rw [hres] at hex
  rw [hp₀, Nat.add_zero] at hcost
  exact ⟨y₀, y, traces, hr₀, hp₀, hex, hcost⟩

end WordRAMFibonacciHeapTests
