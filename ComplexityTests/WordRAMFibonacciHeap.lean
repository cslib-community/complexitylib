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

/-! ### 5. Key–value Fibonacci heap with handles (`FibonacciHeap.MinPQ`) -/

/-- Tabulate registers `0..rMinPQ - 1` (`48`) and memory `0..memCap - 1` into flat lists between
interpreter calls for `FibonacciHeap.MinPQ`. -/
def compactDataMinPQ (memCap : ℕ) (d : Data MinPQ.rMinPQ) : Option (Data MinPQ.rMinPQ) := do
  let rs ← forceList ((List.finRange MinPQ.rMinPQ).map d.regs)
  let ms ← forceList ((List.range memCap).map d.mem)
  let tail ← forceNat (d.mem memCap)
  pure
    { regs := fun i => rs.getD i.val 0
      mem := fun a => if a < memCap then ms.getD a 0 else tail }

/-- Run a single `Cslib.Algorithms.Lean.MinPQ.Op` via `MinPQ.dispatchCode.eval`. -/
def stepEvalMinPQ {n_max : ℕ} (w fuel : ℕ) (dt : Data MinPQ.rMinPQ × ℕ)
    (o : Cslib.Algorithms.Lean.MinPQ.Op n_max) :
    Option (Data MinPQ.rMinPQ × ℕ) := do
  let (d', t) ← MinPQ.dispatchCode.eval w fuel ⟨MinPQ.prepareRegs o dt.1.regs, dt.1.mem⟩
  let dc ← compactDataMinPQ 80 d'
  pure (dc, dt.2 + t)

/-- Concrete interpreter test for `FibonacciHeap.MinPQ`:
* `insert 30 300` allocates handle `0`, `insert 20 200` allocates handle `1`;
* `get 0` returns key `30` and satellite value `300`;
* `decreaseKey 0 5` lowers handle `0`'s key to `5`;
* `extractMin` returns `(u = 5, v = 300, h = 0)` and pushes handle `0` onto the free stack;
* `insert 15 150` reuses handle `0` from the free stack;
* two more `extractMin`s return `(15, 150, 0)` and `(20, 200, 1)`, followed by `none`. -/
example :
    (do
      let d0 ← MinPQ.subroutineCode.initFresh.eval 12 16 ⟨MinPQ.initRegs 4 10, fun _ => 0⟩
      let d1 ← stepEvalMinPQ (n_max := 4) 12 16 d0 (.insert 30 300)
      let d2 ← stepEvalMinPQ (n_max := 4) 12 16 d1 (.insert 20 200)
      let d3 ← stepEvalMinPQ (n_max := 4) 12 16 d2 (.get 0)
      let d4 ← stepEvalMinPQ (n_max := 4) 12 16 d3 (.decreaseKey 0 5)
      let d5 ← stepEvalMinPQ (n_max := 4) 12 16 d4 .extractMin
      let d6 ← stepEvalMinPQ (n_max := 4) 12 16 d5 (.insert 15 150)
      let d7 ← stepEvalMinPQ (n_max := 4) 12 16 d6 .extractMin
      let d8 ← stepEvalMinPQ (n_max := 4) 12 16 d7 .extractMin
      let d9 ← stepEvalMinPQ (n_max := 4) 12 16 d8 .extractMin
      pure
        [d1.1.regs MinPQ.outV, d2.1.regs MinPQ.outV,
         d3.1.regs MinPQ.outFlag, d3.1.regs MinPQ.outK, d3.1.regs MinPQ.outValReg,
         d5.1.regs MinPQ.outFlag, d5.1.regs MinPQ.outK, d5.1.regs MinPQ.outValReg,
         d5.1.regs MinPQ.outV,
         d6.1.regs MinPQ.outV,
         d7.1.regs MinPQ.outK, d7.1.regs MinPQ.outValReg, d7.1.regs MinPQ.outV,
         d8.1.regs MinPQ.outK, d8.1.regs MinPQ.outValReg, d8.1.regs MinPQ.outV,
         d9.1.regs MinPQ.outFlag]) =
    some [0, 1, 1, 30, 300, 1, 5, 300, 0, 0, 15, 150, 0, 20, 200, 1, 0] := by
  decide +kernel

/-- Non-vacuity of `FibonacciHeap.relAmortized` over `Basis.standard`. -/
example :
    let hS : Fits 10 (8 + MinPQ.space 4) := by unfold MinPQ.space Fits; decide
    let hU : Fits 10 50 := by decide
    let hV : Fits 10 500 := by decide
    Stateful.RelAmortized (relCertificate hS hU hV).realization
      DynamicProgram.OperationTrace.instructions
      (fun _ x => MinPQ.potential x)
      (fun s o => MinPQ.charge 4 s o + 1) :=
  relAmortized _ _ _

/-- Lift a single `Cslib.Algorithms.Lean.MinPQ.Op` into an adaptive `Client`. -/
abbrev callMinPQOp (o : Cslib.Algorithms.Lean.MinPQ.Op 4) :
    (Cslib.Algorithms.Lean.MinPQ.spec 4 50 500).Client
      ((Cslib.Algorithms.Lean.MinPQ.spec 4 50 500).Result o) :=
  PFunctor.FreeM.lift (P := (Cslib.Algorithms.Lean.MinPQ.spec 4 50 500).signature) o

/-- Concrete adaptive client that inserts `(30, 300)`, receives the allocated handle `h`, lowers
`h`'s key to `5`, and extracts the minimum entry. -/
def sampleMinPQClient :
    (Cslib.Algorithms.Lean.MinPQ.spec 4 50 500).Client (Option (ℕ × ℕ × Fin 4)) := do
  let hOpt ← callMinPQOp (.insert 30 300)
  match hOpt with
  | some h =>
    callMinPQOp (.decreaseKey h 5)
    callMinPQOp .extractMin
  | none =>
    callMinPQOp .extractMin

/-- Non-vacuity of `MinPQ.relSubroutineDS`, `MinPQ.Rep`, and `MinPQ.run_client_amortized` for an
adaptive handle-passing client over `Basis.standard`. -/
example :
    let hS : Fits 10 (8 + MinPQ.space 4) := by unfold MinPQ.space Fits; decide
    let hU : Fits 10 50 := by decide
    let hV : Fits 10 500 := by decide
    ∃ a y₀ y traces s' tr,
      MinPQ.Rep 4 50 500 10 8 (Cslib.Algorithms.Lean.MinPQ.empty 4) y₀ ∧
      MinPQ.potential y₀ = 0 ∧
      Stateful.Executes ((relDynamicProgram hS hU hV).ExecOp 10) sampleMinPQClient y₀
        a y traces ∧
      (Cslib.Algorithms.Lean.MinPQ.spec 4 50 500).ClientRun
        (Cslib.Algorithms.Lean.MinPQ.empty 4) sampleMinPQClient a s' tr ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces + MinPQ.potential y ≤
        (Cslib.Algorithms.Lean.MinPQ.spec 4 50 500).totalCost
          (fun st o => MinPQ.charge 4 st o + 1)
          (Cslib.Algorithms.Lean.MinPQ.empty 4) tr := by
  intro hS hU hV
  let x₀ : Data MinPQ.rMinPQ := ⟨MinPQ.initRegs 4 8, fun _ => 0⟩
  have hx₀ : x₀.Bounded 10 :=
    ⟨fun i => by fin_cases i <;> decide, fun _ => show Fits 10 0 by decide⟩
  have hfr : x₀.regs MinPQ.outerFrontierReg = 8 := by decide
  have hpar : ∀ j : Fin 1, x₀.regs (![MinPQ.nReg] j) = ![4] j := fun j => by fin_cases j; rfl
  have hz : ∀ a ∈ (Block.mk 8 (MinPQ.space 4)).footprint, x₀.mem a = 0 := fun _ _ => rfl
  obtain ⟨y₀, _, _, hr₀, hpot₀, _⟩ :=
    (relSubroutineDS hS hU hV).initFresh_exec hx₀ hfr hpar hz
  have hp₀ : MinPQ.potential y₀ = 0 := Nat.eq_zero_of_le_zero hpot₀
  have hv : (Cslib.Algorithms.Lean.MinPQ.spec 4 50 500).DemonicValid
      (Cslib.Algorithms.Lean.MinPQ.empty 4) sampleMinPQClient := by
    refine .liftBind _ _ ⟨by decide, by decide, by decide⟩ ?_
    rintro s₁ _ ⟨h, _, rfl, rfl⟩
    refine .liftBind _ _ ⟨30, 300, by simp [Function.update], by decide⟩ ?_
    rintro s₂ _ _
    exact .liftBind _ _ trivial fun s₃ a _ => .pure s₃ a
  obtain ⟨a, y, traces, s', tr, hex, hrun, _, _, hcost⟩ :=
    MinPQ.run_client_amortized hS hU hV sampleMinPQClient hr₀ hv
  rw [hp₀, Nat.add_zero] at hcost
  exact ⟨a, y₀, y, traces, s', tr, hr₀, hp₀, hex, hrun, hcost⟩

end WordRAMFibonacciHeapTests
