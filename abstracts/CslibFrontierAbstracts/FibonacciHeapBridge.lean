/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import CslibFrontierAbstracts.WordRAMBridge
import CslibFrontier.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

/-!
# Bridge for the Fibonacci-heap formal abstract

`FibonacciHeapAbstract.lean` defines a min-priority queue with handles storing key–value pairs from
scratch, together with an adaptive client tree `Client`, its exact word-RAM presentation, register
calling convention, memory-confinement predicate and adaptive execution relation `RunsClient`. This
file proves, for every word-RAM presentation `S` satisfying `WordRAMBridge.Laws S` and every
priority-queue presentation `P` satisfying `PQLaws S P`, that the compiled library programs
`initFreshProg`, `initClearProg` and `opProg` of
`Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.MinPQ` realize `RunsClient` within the
claimed `O(1)` / `O(n_max + 1)` initialization bounds and
`O(m_q + m_ins + m_dec + ∑ (log n_t + 1))` amortized operation bound in the current number of
stored elements `n_t`.

## Main results

* `PQPresentation.runsClient_map`: adaptive-client runs of `FibonacciHeap.MinPQ.opProg` over
  `Basis.exact` translate step-for-step to `P.RunsClient` via `WordRAMBridge.Machine.runs_map`.
* `amortized_fresh`: transfers `FibonacciHeap.MinPQ.run_client_exact_fresh` (`O(1)` fresh
  initialization on zeroed `[base, base + 11 * n_max + 1)`) to any `S` and `P`.
* `amortized_reusable`: transfers `FibonacciHeap.MinPQ.run_client_exact_reusable` (`O(n_max + 1)`
  initialization on arbitrary `w`-bit memory) to any `S` and `P`.

## Syntax in the imports

`FibonacciHeap` is authored in the scoped word-RAM program syntax of
`CslibFrontier/Computability/WordRAM/Notation.lean` and its exact-basis variant in
`CslibFrontier/Computability/WordRAM/ExactNotation.lean`. All syntax rules, `macro_rules` and
tactics in those files are scoped to `Cslib.WordRAM`. Only the syntax category `wramStmt` and the
syntax abbreviation `wramBlock` are global, since Lean cannot scope syntax categories, and outside
`Cslib.WordRAM` `wramStmt` has no rules. `FibonacciHeapAbstract.lean` does not open
`Cslib.WordRAM`, so none of this syntax is active there.
-/

namespace CslibFrontierAbstracts.FibonacciHeapBridge

open Cslib.WordRAM
open Cslib.DataStructure Cslib.DataStructure.PriorityQueue Cslib.DataStructure.PriorityQueue.WordRAM
open CslibFrontierTests.Abstracts
open WordRAMBridge

/-! ## Priority-queue presentation and agreement with `MinPQ` -/

/-- Polymorphic signature of the priority-queue definitions in `FibonacciHeapAbstract`, specialized
at register count `FibonacciHeap.MinPQ.rMinPQ` (`48`) where the concrete programs live. -/
structure PQPresentation (S : WordRAMBridge.Presentation) where
  Op : ℕ → Type
  OpResult {n_max : ℕ} : Op n_max → Type
  isEmpty {n_max : ℕ} : Op n_max
  get {n_max : ℕ} : Fin n_max → Op n_max
  insert {n_max : ℕ} : ℕ → ℕ → Op n_max
  decreaseKey {n_max : ℕ} : Fin n_max → ℕ → Op n_max
  extractMin {n_max : ℕ} : Op n_max
  op_rec {n_max : ℕ} {motive : Op n_max → Type} :
    motive isEmpty → (∀ h, motive (get h)) → (∀ u v, motive (insert u v)) →
      (∀ h u', motive (decreaseKey h u')) → motive extractMin → ∀ o, motive o
  op_induction {n_max : ℕ} {P : Op n_max → Prop} :
    P isEmpty → (∀ h, P (get h)) → (∀ u v, P (insert u v)) →
      (∀ h u', P (decreaseKey h u')) → P extractMin → ∀ o, P o
  resIsEmpty {n_max : ℕ} : Bool → OpResult (isEmpty (n_max := n_max))
  resGet {n_max : ℕ} (h : Fin n_max) : Option (ℕ × ℕ) → OpResult (get h)
  resInsert {n_max : ℕ} (u v : ℕ) : Option (Fin n_max) → OpResult (insert (n_max := n_max) u v)
  resDecreaseKey {n_max : ℕ} (h : Fin n_max) (u' : ℕ) : Unit → OpResult (decreaseKey h u')
  resExtractMin {n_max : ℕ} : Option (ℕ × ℕ × Fin n_max) → OpResult (extractMin (n_max := n_max))
  Client : ℕ → Type
  done {n_max : ℕ} : Client n_max
  clientStep {n_max : ℕ} (o : Op n_max) : (OpResult o → Client n_max) → Client n_max
  client_rec {n_max : ℕ} {motive : Client n_max → Type} :
    motive done →
      (∀ (o : Op n_max) (k : OpResult o → Client n_max),
        (∀ r, motive (k r)) → motive (clientStep o k)) →
      ∀ c, motive c
  client_induction {n_max : ℕ} {P : Client n_max → Prop} :
    P done →
      (∀ (o : Op n_max) (k : OpResult o → Client n_max),
        (∀ r, P (k r)) → P (clientStep o k)) →
      ∀ c, P c
  size {n_max : ℕ} : (Fin n_max → Option (ℕ × ℕ)) → ℕ
  extractStepLog {n_max : ℕ} : (Fin n_max → Option (ℕ × ℕ)) → Op n_max → ℕ
  StepState {n_max : ℕ} :
    (Fin n_max → Option (ℕ × ℕ)) → (o : Op n_max) →
      (Fin n_max → Option (ℕ × ℕ)) → OpResult o → Prop
  StepDecoded {n_max : ℕ} :
    (Fin n_max → Option (ℕ × ℕ)) → (o : Op n_max) →
      (Fin n_max → Option (ℕ × ℕ)) → OpResult o → (Fin 48 → ℕ) → Prop
  ValidOp {n_max : ℕ} : ℕ → ℕ → (Fin n_max → Option (ℕ × ℕ)) → Op n_max → Prop
  ValidClient {n_max : ℕ} : ℕ → ℕ → (Fin n_max → Option (ℕ × ℕ)) → Client n_max → Prop
  numQueries {n_max : ℕ} : List (Op n_max) → ℕ
  numInserts {n_max : ℕ} : List (Op n_max) → ℕ
  numDecreaseKeys {n_max : ℕ} : List (Op n_max) → ℕ
  numExtractMins {n_max : ℕ} : List (Op n_max) → ℕ
  initRegs {r : ℕ} : ℕ → ℕ → Fin r → ℕ
  prepareRegs {n_max : ℕ} : Op n_max → (Fin 48 → ℕ) → Fin 48 → ℕ
  stateReg {r : ℕ} : S.State r → Fin r → ℕ
  stateMem {r : ℕ} : S.State r → ℕ → ℕ
  RunsClient {r n_max : ℕ} :
    ℕ → List (S.Instr r) → ℕ → ℕ → (Fin n_max → Option (ℕ × ℕ)) → (Fin r → ℕ) → (ℕ → ℕ) →
      Client n_max → List (Op n_max) → (Fin n_max → Option (ℕ × ℕ)) → (Fin r → ℕ) → (ℕ → ℕ) →
      ℕ → ℕ → Prop

/-- Equational and relational laws connecting a `PQPresentation` to the definitions in
`FibonacciHeapAbstract`. -/
structure PQLaws (S : WordRAMBridge.Presentation) (P : PQPresentation S) : Prop where
  op_rec_isEmpty : ∀ {n_max} {motive : P.Op n_max → Type}
    (f_emp : motive P.isEmpty) (f_get : ∀ h, motive (P.get h))
    (f_ins : ∀ u v, motive (P.insert u v)) (f_dec : ∀ h u', motive (P.decreaseKey h u'))
    (f_ext : motive P.extractMin),
    P.op_rec f_emp f_get f_ins f_dec f_ext P.isEmpty = f_emp
  op_rec_get : ∀ {n_max} {motive : P.Op n_max → Type}
    (f_emp : motive P.isEmpty) (f_get : ∀ h, motive (P.get h))
    (f_ins : ∀ u v, motive (P.insert u v)) (f_dec : ∀ h u', motive (P.decreaseKey h u'))
    (f_ext : motive P.extractMin) (h : Fin n_max),
    P.op_rec f_emp f_get f_ins f_dec f_ext (P.get h) = f_get h
  op_rec_insert : ∀ {n_max} {motive : P.Op n_max → Type}
    (f_emp : motive P.isEmpty) (f_get : ∀ h, motive (P.get h))
    (f_ins : ∀ u v, motive (P.insert u v)) (f_dec : ∀ h u', motive (P.decreaseKey h u'))
    (f_ext : motive P.extractMin) (u v : ℕ),
    P.op_rec f_emp f_get f_ins f_dec f_ext (P.insert u v) = f_ins u v
  op_rec_decreaseKey : ∀ {n_max} {motive : P.Op n_max → Type}
    (f_emp : motive P.isEmpty) (f_get : ∀ h, motive (P.get h))
    (f_ins : ∀ u v, motive (P.insert u v)) (f_dec : ∀ h u', motive (P.decreaseKey h u'))
    (f_ext : motive P.extractMin) (h : Fin n_max) (u' : ℕ),
    P.op_rec f_emp f_get f_ins f_dec f_ext (P.decreaseKey h u') = f_dec h u'
  op_rec_extractMin : ∀ {n_max} {motive : P.Op n_max → Type}
    (f_emp : motive P.isEmpty) (f_get : ∀ h, motive (P.get h))
    (f_ins : ∀ u v, motive (P.insert u v)) (f_dec : ∀ h u', motive (P.decreaseKey h u'))
    (f_ext : motive P.extractMin),
    P.op_rec f_emp f_get f_ins f_dec f_ext P.extractMin = f_ext
  client_rec_done : ∀ {n_max} {motive : P.Client n_max → Type}
    (d : motive P.done)
    (s : ∀ (o : P.Op n_max) (k : P.OpResult o → P.Client n_max),
      (∀ r, motive (k r)) → motive (P.clientStep o k)),
    P.client_rec d s P.done = d
  client_rec_step : ∀ {n_max} {motive : P.Client n_max → Type}
    (d : motive P.done)
    (s : ∀ (o : P.Op n_max) (k : P.OpResult o → P.Client n_max),
      (∀ r, motive (k r)) → motive (P.clientStep o k))
    (o : P.Op n_max) (k : P.OpResult o → P.Client n_max),
    P.client_rec d s (P.clientStep o k) = s o k (fun r => P.client_rec d s (k r))
  size_eq : ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)),
    P.size q = (Finset.univ.filter fun h => (q h).isSome).card
  extractStepLog_isEmpty : ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)),
    P.extractStepLog q P.isEmpty = 0
  extractStepLog_get : ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)) (h : Fin n_max),
    P.extractStepLog q (P.get h) = 0
  extractStepLog_insert : ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)) (u v : ℕ),
    P.extractStepLog q (P.insert u v) = 0
  extractStepLog_decreaseKey : ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)) (h : Fin n_max) (u' : ℕ),
    P.extractStepLog q (P.decreaseKey h u') = 0
  extractStepLog_extractMin : ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)),
    P.extractStepLog q P.extractMin = Nat.log 2 (P.size q) + 1
  stepState_isEmpty : ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)),
    P.StepState q P.isEmpty q (P.resIsEmpty (decide (∀ h, q h = none)))
  stepState_get : ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)) (h : Fin n_max),
    P.StepState q (P.get h) q (P.resGet h (q h))
  stepState_insert : ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)) (u v : ℕ) (h : Fin n_max),
    q h = none →
      P.StepState q (P.insert u v) (Function.update q h (some (u, v))) (P.resInsert u v (some h))
  stepState_decreaseKey :
    ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)) (h : Fin n_max) (u' u₀ v : ℕ),
      q h = some (u₀, v) →
        P.StepState q (P.decreaseKey h u') (Function.update q h (some (u', v)))
          (P.resDecreaseKey h u' ())
  stepState_extractMin_empty : ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)),
    (∀ h, q h = none) → P.StepState q P.extractMin q (P.resExtractMin none)
  stepState_extractMin_some :
    ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)) (h : Fin n_max) (u v : ℕ),
      q h = some (u, v) → (∀ h' u' v', q h' = some (u', v') → u ≤ u') →
        P.StepState q P.extractMin (Function.update q h none) (P.resExtractMin (some (u, v, h)))
  decodes_isEmpty : ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)) (reg : Fin 48 → ℕ),
    (reg ⟨22, by decide⟩ ≠ 0 ↔ ∀ h, q h = none) →
      P.StepDecoded q P.isEmpty q (P.resIsEmpty (decide (∀ h, q h = none))) reg
  decodes_get : ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)) (h : Fin n_max) (reg : Fin 48 → ℕ),
    (if reg ⟨22, by decide⟩ = 0 then some none
     else some (some (reg ⟨24, by decide⟩, reg ⟨47, by decide⟩))) =
      some (q h) → P.StepDecoded q (P.get h) q (P.resGet h (q h)) reg
  decodes_insert :
    ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)) (u v : ℕ) (h : Fin n_max) (reg : Fin 48 → ℕ),
      q h = none → reg ⟨23, by decide⟩ = (h : ℕ) →
        P.StepDecoded q (P.insert u v) (Function.update q h (some (u, v)))
          (P.resInsert u v (some h)) reg
  decodes_decreaseKey :
    ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)) (h : Fin n_max) (u' u₀ v : ℕ) (reg : Fin 48 → ℕ),
      q h = some (u₀, v) →
        P.StepDecoded q (P.decreaseKey h u') (Function.update q h (some (u', v)))
          (P.resDecreaseKey h u' ()) reg
  decodes_extractMin_empty : ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)) (reg : Fin 48 → ℕ),
    (∀ h, q h = none) → reg ⟨22, by decide⟩ = 0 →
      P.StepDecoded q P.extractMin q (P.resExtractMin none) reg
  decodes_extractMin_some :
    ∀ {n_max} (q : Fin n_max → Option (ℕ × ℕ)) (h : Fin n_max) (u v : ℕ) (reg : Fin 48 → ℕ),
      q h = some (u, v) → (∀ h' u' v', q h' = some (u', v') → u ≤ u') →
        reg ⟨22, by decide⟩ ≠ 0 → reg ⟨23, by decide⟩ = (h : ℕ) →
        reg ⟨24, by decide⟩ = u → reg ⟨47, by decide⟩ = v →
        P.StepDecoded q P.extractMin (Function.update q h none)
          (P.resExtractMin (some (u, v, h))) reg
  valid_insert : ∀ {n_max U V} (q : Fin n_max → Option (ℕ × ℕ)) (u v : ℕ),
    P.ValidOp U V q (P.insert u v) → P.size q < n_max ∧ u < U ∧ v < V
  valid_decreaseKey : ∀ {n_max U V} (q : Fin n_max → Option (ℕ × ℕ)) (h : Fin n_max) (u' : ℕ),
    P.ValidOp U V q (P.decreaseKey h u') → ∃ u₀ v, q h = some (u₀, v) ∧ u' ≤ u₀
  validClient_step :
    ∀ {n_max U V} (q : Fin n_max → Option (ℕ × ℕ)) (o : P.Op n_max)
      (k : P.OpResult o → P.Client n_max),
      P.ValidClient U V q (P.clientStep o k) →
        P.ValidOp U V q o ∧ ∀ q' res, P.StepState q o q' res → P.ValidClient U V q' (k res)
  queries_isEmpty : ∀ {n_max} (ops : List (P.Op n_max)),
    P.numQueries (P.isEmpty :: ops) = 1 + P.numQueries ops
  queries_get : ∀ {n_max} (h : Fin n_max) (ops : List (P.Op n_max)),
    P.numQueries (P.get h :: ops) = 1 + P.numQueries ops
  queries_insert : ∀ {n_max} (u v : ℕ) (ops : List (P.Op n_max)),
    P.numQueries (P.insert u v :: ops) = P.numQueries ops
  queries_decreaseKey : ∀ {n_max} (h : Fin n_max) (u' : ℕ) (ops : List (P.Op n_max)),
    P.numQueries (P.decreaseKey h u' :: ops) = P.numQueries ops
  queries_extractMin : ∀ {n_max} (ops : List (P.Op n_max)),
    P.numQueries (P.extractMin :: ops) = P.numQueries ops
  queries_nil : ∀ {n_max}, P.numQueries (n_max := n_max) [] = 0
  inserts_isEmpty : ∀ {n_max} (ops : List (P.Op n_max)),
    P.numInserts (P.isEmpty :: ops) = P.numInserts ops
  inserts_get : ∀ {n_max} (h : Fin n_max) (ops : List (P.Op n_max)),
    P.numInserts (P.get h :: ops) = P.numInserts ops
  inserts_insert : ∀ {n_max} (u v : ℕ) (ops : List (P.Op n_max)),
    P.numInserts (P.insert u v :: ops) = 1 + P.numInserts ops
  inserts_decreaseKey : ∀ {n_max} (h : Fin n_max) (u' : ℕ) (ops : List (P.Op n_max)),
    P.numInserts (P.decreaseKey h u' :: ops) = P.numInserts ops
  inserts_extractMin : ∀ {n_max} (ops : List (P.Op n_max)),
    P.numInserts (P.extractMin :: ops) = P.numInserts ops
  inserts_nil : ∀ {n_max}, P.numInserts (n_max := n_max) [] = 0
  dec_isEmpty : ∀ {n_max} (ops : List (P.Op n_max)),
    P.numDecreaseKeys (P.isEmpty :: ops) = P.numDecreaseKeys ops
  dec_get : ∀ {n_max} (h : Fin n_max) (ops : List (P.Op n_max)),
    P.numDecreaseKeys (P.get h :: ops) = P.numDecreaseKeys ops
  dec_insert : ∀ {n_max} (u v : ℕ) (ops : List (P.Op n_max)),
    P.numDecreaseKeys (P.insert u v :: ops) = P.numDecreaseKeys ops
  dec_decreaseKey : ∀ {n_max} (h : Fin n_max) (u' : ℕ) (ops : List (P.Op n_max)),
    P.numDecreaseKeys (P.decreaseKey h u' :: ops) = 1 + P.numDecreaseKeys ops
  dec_extractMin : ∀ {n_max} (ops : List (P.Op n_max)),
    P.numDecreaseKeys (P.extractMin :: ops) = P.numDecreaseKeys ops
  dec_nil : ∀ {n_max}, P.numDecreaseKeys (n_max := n_max) [] = 0
  ext_isEmpty : ∀ {n_max} (ops : List (P.Op n_max)),
    P.numExtractMins (P.isEmpty :: ops) = P.numExtractMins ops
  ext_get : ∀ {n_max} (h : Fin n_max) (ops : List (P.Op n_max)),
    P.numExtractMins (P.get h :: ops) = P.numExtractMins ops
  ext_insert : ∀ {n_max} (u v : ℕ) (ops : List (P.Op n_max)),
    P.numExtractMins (P.insert u v :: ops) = P.numExtractMins ops
  ext_decreaseKey : ∀ {n_max} (h : Fin n_max) (u' : ℕ) (ops : List (P.Op n_max)),
    P.numExtractMins (P.decreaseKey h u' :: ops) = P.numExtractMins ops
  ext_extractMin : ∀ {n_max} (ops : List (P.Op n_max)),
    P.numExtractMins (P.extractMin :: ops) = 1 + P.numExtractMins ops
  ext_nil : ∀ {n_max}, P.numExtractMins (n_max := n_max) [] = 0
  initRegs_spec : ∀ n_max base (i : Fin 48),
    P.initRegs n_max base i = if (i : ℕ) = 0 then n_max else if (i : ℕ) = 1 then base else 0
  prep_isEmpty : ∀ {n_max} (reg : Fin 48 → ℕ) (i : Fin 48),
    P.prepareRegs (n_max := n_max) P.isEmpty reg i =
      if (i : ℕ) = 17 then 0 else if (i : ℕ) = 18 then 0 else if (i : ℕ) = 19 then 0
      else if (i : ℕ) = 20 then 0 else if (i : ℕ) = 21 then 0 else if (i : ℕ) = 46 then 0
      else reg i
  prep_get : ∀ {n_max} (h : Fin n_max) (reg : Fin 48 → ℕ) (i : Fin 48),
    P.prepareRegs (P.get h) reg i =
      if (i : ℕ) = 17 then 0 else if (i : ℕ) = 18 then 0 else if (i : ℕ) = 19 then 1
      else if (i : ℕ) = 20 then (h : ℕ) else if (i : ℕ) = 21 then 0 else if (i : ℕ) = 46 then 0
      else reg i
  prep_insert : ∀ {n_max} (u v : ℕ) (reg : Fin 48 → ℕ) (i : Fin 48),
    P.prepareRegs (n_max := n_max) (P.insert u v) reg i =
      if (i : ℕ) = 17 then 0 else if (i : ℕ) = 18 then 1 else if (i : ℕ) = 19 then 0
      else if (i : ℕ) = 20 then 0 else if (i : ℕ) = 21 then u else if (i : ℕ) = 46 then v
      else reg i
  prep_decreaseKey : ∀ {n_max} (h : Fin n_max) (u' : ℕ) (reg : Fin 48 → ℕ) (i : Fin 48),
    P.prepareRegs (P.decreaseKey h u') reg i =
      if (i : ℕ) = 17 then 0 else if (i : ℕ) = 18 then 1 else if (i : ℕ) = 19 then 1
      else if (i : ℕ) = 20 then (h : ℕ) else if (i : ℕ) = 21 then u' else if (i : ℕ) = 46 then 0
      else reg i
  prep_extractMin : ∀ {n_max} (reg : Fin 48 → ℕ) (i : Fin 48),
    P.prepareRegs (n_max := n_max) P.extractMin reg i =
      if (i : ℕ) = 17 then 1 else if (i : ℕ) = 18 then 0 else if (i : ℕ) = 19 then 0
      else if (i : ℕ) = 20 then 0 else if (i : ℕ) = 21 then 0 else if (i : ℕ) = 46 then 0
      else reg i
  stateReg_eq : ∀ (pc : ℕ) (reg : Fin 48 → ℕ) (m : ℕ → ℕ), P.stateReg (S.state pc reg m) = reg
  stateMem_eq : ∀ (pc : ℕ) (reg : Fin 48 → ℕ) (m : ℕ → ℕ), P.stateMem (S.state pc reg m) = m
  runsClient_done : ∀ {n_max w} {p : List (S.Instr 48)} {base len}
    {q : Fin n_max → Option (ℕ × ℕ)} {reg : Fin 48 → ℕ} {mem : ℕ → ℕ},
    P.RunsClient w p base len q reg mem P.done [] q reg mem 0 0
  runsClient_step : ∀ {n_max w} {p : List (S.Instr 48)} {base len}
    {q q₁ q' : Fin n_max → Option (ℕ × ℕ)} {reg : Fin 48 → ℕ} {mem : ℕ → ℕ}
    {o : P.Op n_max} {k : P.OpResult o → P.Client n_max} {res : P.OpResult o}
    {ops : List (P.Op n_max)} {t : S.State 48}
    {reg' : Fin 48 → ℕ} {mem' : ℕ → ℕ} {steps rest extRest : ℕ},
    Relation.RelatesInSteps (fun a b => S.step w p a = S.next b)
      (S.state 0 (P.prepareRegs o reg) mem) t steps →
    (∃ out, S.step w p t = S.halted out) →
    P.StepDecoded q o q₁ res (P.stateReg t) →
    (∀ a, a < base ∨ base + len ≤ a → P.stateMem t a = mem a) →
    P.RunsClient w p base len q₁ (P.stateReg t) (P.stateMem t) (k res) ops
      q' reg' mem' rest extRest →
    P.RunsClient w p base len q reg mem (P.clientStep o k) (o :: ops) q' reg' mem'
      ((steps + 1) + rest) (P.extractStepLog q o + extRest)

theorem forall_none_iff_dom_empty {n_max : ℕ} (q : Fin n_max → Option (ℕ × ℕ)) :
    (∀ h, q h = none) ↔ MinPQ.dom q = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  exact forall_congr' fun h => MinPQ.notMem_dom_iff.symm

theorem unchangedOutside_of_modifies {base n_max : ℕ} {m m' : ℕ → ℕ}
    (hm : Modifies (Block.mk base (FibonacciHeap.MinPQ.space n_max)).footprint m m') :
    ∀ a, a < base ∨ base + (11 * n_max + 1) ≤ a → m' a = m a := by
  intro a ha
  apply hm a
  rw [Block.mem_footprint, Block.Owns]
  dsimp only [FibonacciHeap.MinPQ.space]
  omega

namespace PQPresentation

variable {S : WordRAMBridge.Presentation} (P : PQPresentation S)

/-- Translate a library `MinPQ.Op n_max` into `P.Op n_max`. -/
def opOf {n_max : ℕ} : MinPQ.Op n_max → P.Op n_max
  | .isEmpty => P.isEmpty
  | .get h => P.get h
  | .insert u v => P.insert u v
  | .decreaseKey h u' => P.decreaseKey h u'
  | .extractMin => P.extractMin

/-- Translate a library operation result into `P.OpResult (P.opOf g)`. -/
def resOf {n_max U V : ℕ} :
    (g : MinPQ.Op n_max) → (minPQSpec n_max U V).Result g → P.OpResult (P.opOf g)
  | .isEmpty, b => P.resIsEmpty b
  | .get h, r => P.resGet h r
  | .insert u v, r => P.resInsert u v r
  | .decreaseKey h u', r => P.resDecreaseKey h u' r
  | .extractMin, r => P.resExtractMin r

/-- Translate a single abstract client step into a library `Client` step. -/
def stepToLib {n_max U V : ℕ} (o : P.Op n_max) :
    (P.OpResult o → (minPQSpec n_max U V).Client Unit) → (minPQSpec n_max U V).Client Unit :=
  P.op_rec (motive := fun o =>
      (P.OpResult o → (minPQSpec n_max U V).Client Unit) → (minPQSpec n_max U V).Client Unit)
    (fun ih => PFunctor.FreeM.liftBind (P := (minPQSpec n_max U V).signature) .isEmpty
      fun b => ih (P.resIsEmpty b))
    (fun h ih => PFunctor.FreeM.liftBind (P := (minPQSpec n_max U V).signature) (.get h)
      fun r => ih (P.resGet h r))
    (fun u v ih => PFunctor.FreeM.liftBind (P := (minPQSpec n_max U V).signature) (.insert u v)
      fun r => ih (P.resInsert u v r))
    (fun h u' ih => PFunctor.FreeM.liftBind (P := (minPQSpec n_max U V).signature)
      (.decreaseKey h u') fun r => ih (P.resDecreaseKey h u' r))
    (fun ih => PFunctor.FreeM.liftBind (P := (minPQSpec n_max U V).signature) .extractMin
      fun r => ih (P.resExtractMin r))
    o

/-- Translate an abstract `P.Client n_max` into a library `(minPQSpec n_max U V).Client Unit`. -/
def toLibClient {n_max U V : ℕ} (c : P.Client n_max) : (minPQSpec n_max U V).Client Unit :=
  P.client_rec (motive := fun _ => (minPQSpec n_max U V).Client Unit)
    (PFunctor.FreeM.pure ()) (fun o _ ih => P.stepToLib o ih) c

section WithLaws

variable {P} (hP : PQLaws S P)
include hP

theorem toLibClient_done {n_max U V : ℕ} :
    P.toLibClient (n_max := n_max) (U := U) (V := V) P.done = PFunctor.FreeM.pure () :=
  hP.client_rec_done _ _

theorem toLibClient_clientStep_opOf {n_max U V : ℕ} (g : MinPQ.Op n_max)
    (k : P.OpResult (P.opOf g) → P.Client n_max) :
    P.toLibClient (U := U) (V := V) (P.clientStep (P.opOf g) k) =
      PFunctor.FreeM.liftBind (P := (minPQSpec n_max U V).signature) g
        (fun a => P.toLibClient (k (P.resOf (U := U) (V := V) g a))) := by
  dsimp only [toLibClient]
  rw [hP.client_rec_step (motive := fun _ => (minPQSpec n_max U V).Client Unit)]
  cases g with
  | isEmpty =>
    exact congrFun (hP.op_rec_isEmpty (motive := fun o =>
      (P.OpResult o → (minPQSpec n_max U V).Client Unit) → (minPQSpec n_max U V).Client Unit)
      _ _ _ _ _) _
  | get h =>
    exact congrFun (hP.op_rec_get (motive := fun o =>
      (P.OpResult o → (minPQSpec n_max U V).Client Unit) → (minPQSpec n_max U V).Client Unit)
      _ _ _ _ _ h) _
  | insert u v =>
    exact congrFun (hP.op_rec_insert (motive := fun o =>
      (P.OpResult o → (minPQSpec n_max U V).Client Unit) → (minPQSpec n_max U V).Client Unit)
      _ _ _ _ _ u v) _
  | decreaseKey h u' =>
    exact congrFun (hP.op_rec_decreaseKey (motive := fun o =>
      (P.OpResult o → (minPQSpec n_max U V).Client Unit) → (minPQSpec n_max U V).Client Unit)
      _ _ _ _ _ h u') _
  | extractMin =>
    exact congrFun (hP.op_rec_extractMin (motive := fun o =>
      (P.OpResult o → (minPQSpec n_max U V).Client Unit) → (minPQSpec n_max U V).Client Unit)
      _ _ _ _ _) _

theorem size_eq_lib {n_max : ℕ} (q : Fin n_max → Option (ℕ × ℕ)) :
    P.size q = MinPQ.size q :=
  hP.size_eq q

theorem extractStepLog_eq {n_max : ℕ} (q : Fin n_max → Option (ℕ × ℕ)) (g : MinPQ.Op n_max) :
    P.extractStepLog q (P.opOf g) =
      match g with
      | .extractMin => Nat.log 2 (MinPQ.size q) + 1
      | _ => 0 := by
  cases g with
  | isEmpty => exact hP.extractStepLog_isEmpty q
  | get h => exact hP.extractStepLog_get q h
  | insert u v => exact hP.extractStepLog_insert q u v
  | decreaseKey h u' => exact hP.extractStepLog_decreaseKey q h u'
  | extractMin =>
    rw [opOf, hP.extractStepLog_extractMin, size_eq_lib hP]

theorem stepState_of_lib {n_max U V : ℕ} {q q' : Fin n_max → Option (ℕ × ℕ)}
    {g : MinPQ.Op n_max} {a : (minPQSpec n_max U V).Result g}
    (hs : (minPQSpec n_max U V).step q g q' a) :
    P.StepState q (P.opOf g) q' (P.resOf (U := U) (V := V) g a) := by
  cases g with
  | isEmpty =>
    dsimp only [minPQSpec, MinPQ.Op.Result] at a hs
    rcases hs with ⟨rfl, rfl⟩
    simpa only [opOf, resOf, forall_none_iff_dom_empty] using hP.stepState_isEmpty _
  | get h =>
    dsimp only [minPQSpec, MinPQ.Op.Result] at a hs
    rcases hs with ⟨rfl, rfl⟩
    exact hP.stepState_get _ h
  | insert u v =>
    dsimp only [minPQSpec, MinPQ.Op.Result] at a hs
    rcases hs with ⟨h, hnone, rfl, rfl⟩
    exact hP.stepState_insert _ u v h hnone
  | decreaseKey h u' =>
    dsimp only [minPQSpec, MinPQ.Op.Result] at a hs
    rcases hs with ⟨u₀, v, hq, rfl, rfl⟩
    exact hP.stepState_decreaseKey _ h u' u₀ v hq
  | extractMin =>
    dsimp only [minPQSpec, MinPQ.Op.Result] at a hs
    rcases hs with ⟨hemp, rfl, rfl⟩ | ⟨h, u, v, ⟨hq, hmin⟩, rfl, rfl⟩
    · exact hP.stepState_extractMin_empty _ ((forall_none_iff_dom_empty _).mpr hemp)
    · exact hP.stepState_extractMin_some _ h u v hq hmin

theorem stepDecoded_of_lib {n_max U V : ℕ} {q q' : Fin n_max → Option (ℕ × ℕ)}
    {g : MinPQ.Op n_max} {a : (minPQSpec n_max U V).Result g} {reg : Fin 48 → ℕ}
    (hs : (minPQSpec n_max U V).step q g q' a)
    (hd : FibonacciHeap.MinPQ.decode (n_max := n_max) (U := U) (V := V) g reg = some a) :
    P.StepDecoded q (P.opOf g) q' (P.resOf (U := U) (V := V) g a) reg := by
  cases g with
  | isEmpty =>
    dsimp only [minPQSpec, MinPQ.Op.Result] at a hs hd
    rcases hs with ⟨rfl, rfl⟩
    dsimp only [FibonacciHeap.MinPQ.decode, FibonacciHeap.MinPQ.outFlag] at hd
    have hd' := Option.some.inj hd
    have hiff : reg ⟨22, by decide⟩ ≠ 0 ↔ ∀ h, q' h = none :=
      (decide_eq_decide.mp hd').trans (forall_none_iff_dom_empty q').symm
    simpa only [opOf, resOf, forall_none_iff_dom_empty] using hP.decodes_isEmpty _ reg hiff
  | get h =>
    dsimp only [minPQSpec, MinPQ.Op.Result] at a hs hd
    rcases hs with ⟨rfl, rfl⟩
    exact hP.decodes_get _ h reg hd
  | insert u v =>
    dsimp only [minPQSpec, MinPQ.Op.Result] at a hs hd
    rcases hs with ⟨h, hnone, rfl, rfl⟩
    dsimp only [FibonacciHeap.MinPQ.decode, FibonacciHeap.MinPQ.outV] at hd
    by_cases hlt : reg ⟨23, by decide⟩ < n_max
    · simp only [hlt, ↓reduceDIte] at hd
      have hh : (⟨reg ⟨23, by decide⟩, hlt⟩ : Fin n_max) = h :=
        Option.some.inj (Option.some.inj hd)
      exact hP.decodes_insert _ u v h reg hnone (congrArg Fin.val hh)
    · simp only [hlt, ↓reduceDIte] at hd
      cases hd
  | decreaseKey h u' =>
    dsimp only [minPQSpec, MinPQ.Op.Result] at a hs
    rcases hs with ⟨u₀, v, hq, rfl, rfl⟩
    exact hP.decodes_decreaseKey _ h u' u₀ v reg hq
  | extractMin =>
    dsimp only [minPQSpec, MinPQ.Op.Result] at a hs hd
    dsimp only [FibonacciHeap.MinPQ.decode, FibonacciHeap.MinPQ.outFlag,
      FibonacciHeap.MinPQ.outV, FibonacciHeap.MinPQ.outK,
      FibonacciHeap.MinPQ.outValReg] at hd
    rcases hs with ⟨hemp, rfl, rfl⟩ | ⟨h, u, v, ⟨hq, hmin⟩, rfl, rfl⟩
    · by_cases hf : reg ⟨22, by decide⟩ = 0
      · exact hP.decodes_extractMin_empty _ reg ((forall_none_iff_dom_empty _).mpr hemp) hf
      · simp only [hf, ↓reduceIte] at hd
        by_cases hlt : reg ⟨23, by decide⟩ < n_max
        · simp only [hlt, ↓reduceDIte] at hd
          cases Option.some.inj hd
        · simp only [hlt, ↓reduceDIte] at hd
          cases hd
    · by_cases hf : reg ⟨22, by decide⟩ = 0
      · simp only [hf, ↓reduceIte] at hd
        cases Option.some.inj hd
      · simp only [hf, ↓reduceIte] at hd
        by_cases hlt : reg ⟨23, by decide⟩ < n_max
        · simp only [hlt, ↓reduceDIte] at hd
          have hprod := Option.some.inj (Option.some.inj hd)
          simp only [Prod.mk.injEq] at hprod
          rcases hprod with ⟨hk, hval, hh⟩
          exact hP.decodes_extractMin_some _ h u v reg hq hmin hf
            (congrArg Fin.val hh) hk hval
        · simp only [hlt, ↓reduceDIte] at hd
          cases hd

theorem initRegs_eq (n_max base : ℕ) :
    P.initRegs (r := 48) n_max base = FibonacciHeap.MinPQ.initRegs n_max base := by
  funext i
  rw [hP.initRegs_spec]
  simp only [FibonacciHeap.MinPQ.initRegs, FibonacciHeap.MinPQ.nReg,
    FibonacciHeap.MinPQ.outerFrontierReg, Fin.ext_iff]

theorem prepareRegs_eq {n_max : ℕ} (g : MinPQ.Op n_max) (reg : Fin 48 → ℕ) :
    P.prepareRegs (P.opOf g) reg = FibonacciHeap.MinPQ.prepareRegs g reg := by
  funext i
  cases g with
  | isEmpty =>
    rw [opOf, hP.prep_isEmpty]
    simp only [FibonacciHeap.MinPQ.prepareRegs, FibonacciHeap.MinPQ.rawEncode,
      FibonacciHeap.MinPQ.tag2, FibonacciHeap.MinPQ.tag1, FibonacciHeap.MinPQ.tag0,
      FibonacciHeap.MinPQ.argV, FibonacciHeap.MinPQ.argK, FibonacciHeap.MinPQ.inValReg,
      Fin.ext_iff]
    split_ifs <;> omega
  | get h =>
    rw [opOf, hP.prep_get]
    simp only [FibonacciHeap.MinPQ.prepareRegs, FibonacciHeap.MinPQ.rawEncode,
      FibonacciHeap.MinPQ.tag2, FibonacciHeap.MinPQ.tag1, FibonacciHeap.MinPQ.tag0,
      FibonacciHeap.MinPQ.argV, FibonacciHeap.MinPQ.argK, FibonacciHeap.MinPQ.inValReg,
      Fin.ext_iff]
    split_ifs <;> omega
  | insert u v =>
    rw [opOf, hP.prep_insert]
    simp only [FibonacciHeap.MinPQ.prepareRegs, FibonacciHeap.MinPQ.rawEncode,
      FibonacciHeap.MinPQ.tag2, FibonacciHeap.MinPQ.tag1, FibonacciHeap.MinPQ.tag0,
      FibonacciHeap.MinPQ.argV, FibonacciHeap.MinPQ.argK, FibonacciHeap.MinPQ.inValReg,
      Fin.ext_iff]
    split_ifs <;> omega
  | decreaseKey h u' =>
    rw [opOf, hP.prep_decreaseKey]
    simp only [FibonacciHeap.MinPQ.prepareRegs, FibonacciHeap.MinPQ.rawEncode,
      FibonacciHeap.MinPQ.tag2, FibonacciHeap.MinPQ.tag1, FibonacciHeap.MinPQ.tag0,
      FibonacciHeap.MinPQ.argV, FibonacciHeap.MinPQ.argK, FibonacciHeap.MinPQ.inValReg,
      Fin.ext_iff]
    split_ifs <;> omega
  | extractMin =>
    rw [opOf, hP.prep_extractMin]
    simp only [FibonacciHeap.MinPQ.prepareRegs, FibonacciHeap.MinPQ.rawEncode,
      FibonacciHeap.MinPQ.tag2, FibonacciHeap.MinPQ.tag1, FibonacciHeap.MinPQ.tag0,
      FibonacciHeap.MinPQ.argV, FibonacciHeap.MinPQ.argK, FibonacciHeap.MinPQ.inValReg,
      Fin.ext_iff]
    split_ifs <;> omega

private theorem validOp_to_lib {n_max U V : ℕ} (g : MinPQ.Op n_max)
    (q : Fin n_max → Option (ℕ × ℕ)) (hv : P.ValidOp U V q (P.opOf g)) :
    (minPQSpec n_max U V).valid q g := by
  cases g with
  | isEmpty | get _ | extractMin => trivial
  | insert u v =>
    have h := hP.valid_insert q u v hv
    rw [size_eq_lib hP] at h
    exact h
  | decreaseKey h u' => exact hP.valid_decreaseKey q h u' hv

private theorem validClient_step_opOf {n_max U V : ℕ} (g : MinPQ.Op n_max)
    (k : P.OpResult (P.opOf g) → P.Client n_max)
    (ih : ∀ r, ∀ (q : (minPQSpec n_max U V).State), P.ValidClient U V q (k r) →
      (minPQSpec n_max U V).DemonicValid q (P.toLibClient (U := U) (V := V) (k r)))
    (q : (minPQSpec n_max U V).State)
    (hv : P.ValidClient U V q (P.clientStep (P.opOf g) k)) :
    (minPQSpec n_max U V).DemonicValid q
      (P.toLibClient (U := U) (V := V) (P.clientStep (P.opOf g) k)) := by
  obtain ⟨hv_o, hv_k⟩ := hP.validClient_step q (P.opOf g) k hv
  rw [toLibClient_clientStep_opOf hP g k]
  exact StateTransitionSpec.DemonicValid.liftBind (D := minPQSpec n_max U V)
    g _ (validOp_to_lib hP g q hv_o)
    fun q' a hs => ih _ q' (hv_k q' _ (stepState_of_lib hP hs))

theorem validClient_to_lib {n_max U V : ℕ} (c : P.Client n_max) :
    ∀ (q : (minPQSpec n_max U V).State),
      P.ValidClient U V q c →
        (minPQSpec n_max U V).DemonicValid q (P.toLibClient (U := U) (V := V) c) :=
  P.client_induction
    (P := fun c => ∀ (q : (minPQSpec n_max U V).State), P.ValidClient U V q c →
      (minPQSpec n_max U V).DemonicValid q (P.toLibClient (U := U) (V := V) c))
    (fun q _ => by
      rw [toLibClient_done hP]
      exact StateTransitionSpec.DemonicValid.pure (D := minPQSpec n_max U V) q ())
    (fun o k ih =>
      P.op_induction
        (P := fun o => ∀ (k : P.OpResult o → P.Client n_max),
          (∀ r, ∀ (q : (minPQSpec n_max U V).State), P.ValidClient U V q (k r) →
            (minPQSpec n_max U V).DemonicValid q (P.toLibClient (U := U) (V := V) (k r))) →
          ∀ (q : (minPQSpec n_max U V).State), P.ValidClient U V q (P.clientStep o k) →
            (minPQSpec n_max U V).DemonicValid q
              (P.toLibClient (U := U) (V := V) (P.clientStep o k)))
        (fun k ih => validClient_step_opOf hP .isEmpty k ih)
        (fun h k ih => validClient_step_opOf hP (.get h) k ih)
        (fun u v k ih => validClient_step_opOf hP (.insert u v) k ih)
        (fun h u' k ih => validClient_step_opOf hP (.decreaseKey h u') k ih)
        (fun k ih => validClient_step_opOf hP .extractMin k ih)
        o k ih)
    c

theorem numQueries_eq {n_max : ℕ} :
    ∀ (gs : List (MinPQ.Op n_max)),
      FibonacciHeap.MinPQ.numQueries gs = P.numQueries (gs.map P.opOf)
  | [] => hP.queries_nil.symm
  | g :: gs => by
    have ih := numQueries_eq gs
    cases g <;>
      simp only [List.map_cons, opOf, FibonacciHeap.MinPQ.numQueries, ih,
        hP.queries_isEmpty, hP.queries_get, hP.queries_insert,
        hP.queries_decreaseKey, hP.queries_extractMin]

theorem numInserts_eq {n_max : ℕ} :
    ∀ (gs : List (MinPQ.Op n_max)),
      FibonacciHeap.MinPQ.numInserts gs = P.numInserts (gs.map P.opOf)
  | [] => hP.inserts_nil.symm
  | g :: gs => by
    have ih := numInserts_eq gs
    cases g <;>
      simp only [List.map_cons, opOf, FibonacciHeap.MinPQ.numInserts, ih,
        hP.inserts_isEmpty, hP.inserts_get, hP.inserts_insert,
        hP.inserts_decreaseKey, hP.inserts_extractMin]

theorem numDecreaseKeys_eq {n_max : ℕ} :
    ∀ (gs : List (MinPQ.Op n_max)),
      FibonacciHeap.MinPQ.numDecreaseKeys gs = P.numDecreaseKeys (gs.map P.opOf)
  | [] => hP.dec_nil.symm
  | g :: gs => by
    have ih := numDecreaseKeys_eq gs
    cases g <;>
      simp only [List.map_cons, opOf, FibonacciHeap.MinPQ.numDecreaseKeys, ih,
        hP.dec_isEmpty, hP.dec_get, hP.dec_insert,
        hP.dec_decreaseKey, hP.dec_extractMin]

theorem numExtractMins_eq {n_max : ℕ} :
    ∀ (gs : List (MinPQ.Op n_max)),
      FibonacciHeap.MinPQ.numExtractMins gs = P.numExtractMins (gs.map P.opOf)
  | [] => hP.ext_nil.symm
  | g :: gs => by
    have ih := numExtractMins_eq gs
    cases g <;>
      simp only [List.map_cons, opOf, FibonacciHeap.MinPQ.numExtractMins, ih,
        hP.ext_isEmpty, hP.ext_get, hP.ext_insert,
        hP.ext_decreaseKey, hP.ext_extractMin]

private theorem runsClient_step_opOf (hS : WordRAMBridge.Laws S) {n_max U V w base : ℕ}
    (g : MinPQ.Op n_max) (k : P.OpResult (P.opOf g) → P.Client n_max)
    (ih : ∀ r, ∀ {q q' : Fin n_max → Option (ℕ × ℕ)} {x z : Data 48} {v : Unit}
      {tr : (minPQSpec n_max U V).Transcript} {total : ℕ},
      FibonacciHeap.MinPQ.RunsClient (U := U) (V := V) w base q x
        (P.toLibClient (U := U) (V := V) (k r)) v tr q' z total →
      P.RunsClient w (S.programOf FibonacciHeap.MinPQ.opProg) base (11 * n_max + 1) q x.regs x.mem
        (k r) (tr.ops.map P.opOf) q' z.regs z.mem total (FibonacciHeap.MinPQ.extractLogSum q tr))
    {q q' : Fin n_max → Option (ℕ × ℕ)} {x z : Data 48} {v : Unit}
    {tr : (minPQSpec n_max U V).Transcript} {total : ℕ}
    (hruns : FibonacciHeap.MinPQ.RunsClient (U := U) (V := V) w base q x
      (P.toLibClient (U := U) (V := V) (P.clientStep (P.opOf g) k)) v tr q' z total) :
    P.RunsClient w (S.programOf FibonacciHeap.MinPQ.opProg) base (11 * n_max + 1) q x.regs x.mem
      (P.clientStep (P.opOf g) k) (tr.ops.map P.opOf) q' z.regs z.mem total
      (FibonacciHeap.MinPQ.extractLogSum q tr) := by
  rw [toLibClient_clientStep_opOf hP g k, FibonacciHeap.MinPQ.RunsClient.liftBind_iff] at hruns
  rcases hruns with ⟨q₁, a, tr_rest, pc, y, steps, rest, rfl, rfl, hr, ⟨out, hh⟩,
    hstep, hdec, hmod, hrest⟩
  have hr' : Relation.RelatesInSteps
      (fun a b => S.step w (S.programOf FibonacciHeap.MinPQ.opProg) a = S.next b)
      (S.state 0 (P.prepareRegs (P.opOf g) x.regs) x.mem)
      (S.state pc y.regs y.mem) steps := by
    rw [prepareRegs_eq hP]
    exact Machine.runs_map hS hr
  have hh' : S.step w (S.programOf FibonacciHeap.MinPQ.opProg) (S.state pc y.regs y.mem) =
      S.halted out :=
    Machine.step_halt hS hh
  have hdec' : P.StepDecoded q (P.opOf g) q₁ (P.resOf (U := U) (V := V) g a)
      (P.stateReg (S.state pc y.regs y.mem)) := by
    rw [hP.stateReg_eq]
    exact stepDecoded_of_lib hP hstep hdec
  have hmod' : ∀ a, a < base ∨ base + (11 * n_max + 1) ≤ a →
      P.stateMem (S.state pc y.regs y.mem) a = x.mem a := by
    rw [hP.stateMem_eq]
    exact unchangedOutside_of_modifies hmod
  have hrest' := ih (P.resOf (U := U) (V := V) g a) hrest
  have hstep_res := hP.runsClient_step hr' ⟨out, hh'⟩ hdec' hmod'
    (by rw [hP.stateReg_eq, hP.stateMem_eq]; exact hrest')
  have hext : FibonacciHeap.MinPQ.extractLogSum q
      ({ op := g, result := a, nextState := q₁ } :: tr_rest) =
    P.extractStepLog q (P.opOf g) + FibonacciHeap.MinPQ.extractLogSum q₁ tr_rest := by
    cases g <;>
      simp only [FibonacciHeap.MinPQ.extractLogSum, opOf,
        hP.extractStepLog_isEmpty, hP.extractStepLog_get, hP.extractStepLog_insert,
        hP.extractStepLog_decreaseKey, hP.extractStepLog_extractMin, size_eq_lib hP]
  dsimp only [StateTransitionSpec.Transcript.ops, List.map_cons]
  rw [hext]
  exact hstep_res

theorem runsClient_map (hS : WordRAMBridge.Laws S) {n_max U V w base : ℕ}
    (c : P.Client n_max) :
    ∀ {q q' : Fin n_max → Option (ℕ × ℕ)} {x z : Data 48} {v : Unit}
      {tr : (minPQSpec n_max U V).Transcript} {total : ℕ},
      FibonacciHeap.MinPQ.RunsClient (U := U) (V := V) w base q x
        (P.toLibClient (U := U) (V := V) c) v tr q' z total →
      P.RunsClient w (S.programOf FibonacciHeap.MinPQ.opProg) base (11 * n_max + 1) q x.regs x.mem
        c (tr.ops.map P.opOf) q' z.regs z.mem total (FibonacciHeap.MinPQ.extractLogSum q tr) :=
  P.client_induction
    (P := fun c => ∀ {q q' : Fin n_max → Option (ℕ × ℕ)} {x z : Data 48} {v : Unit}
      {tr : (minPQSpec n_max U V).Transcript} {total : ℕ},
      FibonacciHeap.MinPQ.RunsClient (U := U) (V := V) w base q x
        (P.toLibClient (U := U) (V := V) c) v tr q' z total →
      P.RunsClient w (S.programOf FibonacciHeap.MinPQ.opProg) base (11 * n_max + 1) q x.regs x.mem
        c (tr.ops.map P.opOf) q' z.regs z.mem total (FibonacciHeap.MinPQ.extractLogSum q tr))
    (fun hruns => by
      rw [toLibClient_done hP, FibonacciHeap.MinPQ.RunsClient.pure_iff] at hruns
      rcases hruns with ⟨_, rfl, rfl, rfl, rfl⟩
      exact hP.runsClient_done)
    (fun o k ih =>
      P.op_induction
        (P := fun o => ∀ (k : P.OpResult o → P.Client n_max),
          (∀ r, ∀ {q q' : Fin n_max → Option (ℕ × ℕ)} {x z : Data 48} {v : Unit}
            {tr : (minPQSpec n_max U V).Transcript} {total : ℕ},
            FibonacciHeap.MinPQ.RunsClient (U := U) (V := V) w base q x
              (P.toLibClient (U := U) (V := V) (k r)) v tr q' z total →
            P.RunsClient w (S.programOf FibonacciHeap.MinPQ.opProg) base (11 * n_max + 1)
              q x.regs x.mem (k r) (tr.ops.map P.opOf) q' z.regs z.mem total
              (FibonacciHeap.MinPQ.extractLogSum q tr)) →
          ∀ {q q' : Fin n_max → Option (ℕ × ℕ)} {x z : Data 48} {v : Unit}
            {tr : (minPQSpec n_max U V).Transcript} {total : ℕ},
            FibonacciHeap.MinPQ.RunsClient (U := U) (V := V) w base q x
              (P.toLibClient (U := U) (V := V) (P.clientStep o k)) v tr q' z total →
            P.RunsClient w (S.programOf FibonacciHeap.MinPQ.opProg) base (11 * n_max + 1)
              q x.regs x.mem (P.clientStep o k) (tr.ops.map P.opOf) q' z.regs z.mem total
              (FibonacciHeap.MinPQ.extractLogSum q tr))
        (fun k ih => runsClient_step_opOf hP hS .isEmpty k ih)
        (fun h k ih => runsClient_step_opOf hP hS (.get h) k ih)
        (fun u v k ih => runsClient_step_opOf hP hS (.insert u v) k ih)
        (fun h u' k ih => runsClient_step_opOf hP hS (.decreaseKey h u') k ih)
        (fun k ih => runsClient_step_opOf hP hS .extractMin k ih)
        o k ih)
    c

end WithLaws

end PQPresentation

/-! ## Transfer of the standalone Fibonacci-heap theorems -/

/-- Transfer of `FibonacciHeap.MinPQ.run_client_exact_fresh` (`O(1)` fresh initialization on zeroed
`[base, base + 11 * n_max + 1)`) to any exact word-RAM presentation `S` and priority-queue
presentation `P`. -/
theorem amortized_fresh (S : WordRAMBridge.Presentation) (hS : WordRAMBridge.Laws S)
    (P : PQPresentation S) (hP : PQLaws S P) :
    ∃ r, ∃ p_init p_op : List (S.Instr r), ∃ K,
      ∀ (n_max U V base w : ℕ) (mem₀ : ℕ → ℕ) (c : P.Client n_max),
        base + (11 * n_max + 1) < 2 ^ w →
        U < 2 ^ w →
        V < 2 ^ w →
        (∀ a, mem₀ a < 2 ^ w) →
        (∀ a, base ≤ a → a < base + (11 * n_max + 1) → mem₀ a = 0) →
        P.ValidClient U V (fun _ => none) c →
        ∃ t₀ t_init ops q_f reg_f mem_f t_ops extLog,
          Relation.RelatesInSteps (fun a b => S.step w p_init a = S.next b)
            (S.state 0 (P.initRegs n_max base) mem₀) t₀ t_init ∧
          (∃ out, S.step w p_init t₀ = S.halted out) ∧
          (∀ a, a < base ∨ base + (11 * n_max + 1) ≤ a → P.stateMem t₀ a = mem₀ a) ∧
          P.RunsClient w p_op base (11 * n_max + 1) (fun _ => none) (P.stateReg t₀) (P.stateMem t₀)
            c ops q_f reg_f mem_f t_ops extLog ∧
          t_init + 1 ≤ K ∧
          t_ops ≤
            K * (P.numQueries ops + P.numInserts ops + P.numDecreaseKeys ops + extLog) ∧
          extLog ≤ P.numExtractMins ops * (Nat.log 2 n_max + 1) := by
  refine ⟨48, S.programOf FibonacciHeap.MinPQ.initFreshProg,
    S.programOf FibonacciHeap.MinPQ.opProg, 421,
    fun n_max U V base w mem₀ c hsp hU hV hmem hzero hv => ?_⟩
  have hzero' : ∀ a ∈ (Block.mk base (FibonacciHeap.MinPQ.space n_max)).footprint, mem₀ a = 0 := by
    intro a ha
    rw [Block.mem_footprint, Block.Owns] at ha
    exact hzero a ha.1 ha.2
  obtain ⟨pc₀, x₀, t_init, _, tr, q_f, z, t_ops, hr₀, ⟨out, hh₀⟩, hmod₀, hruns, _,
      ht_init, ht_ops, _⟩ :=
    FibonacciHeap.MinPQ.run_client_exact_fresh (U := U) (V := V) hsp hU hV hmem hzero'
      (P.toLibClient (U := U) (V := V) c) (P.validClient_to_lib hP c _ hv)
  have hlog_le : FibonacciHeap.MinPQ.extractLogSum (MinPQ.empty n_max) tr ≤
      P.numExtractMins (tr.ops.map P.opOf) * (Nat.log 2 n_max + 1) := by
    rw [← P.numExtractMins_eq hP tr.ops]
    exact FibonacciHeap.MinPQ.extractLogSum_le_numExtractMins tr (MinPQ.empty n_max)
  refine ⟨S.state pc₀ x₀.regs x₀.mem, t_init, tr.ops.map P.opOf, q_f, z.regs, z.mem, t_ops,
    FibonacciHeap.MinPQ.extractLogSum (MinPQ.empty n_max) tr, ?_,
    ⟨out, Machine.step_halt hS hh₀⟩, ?_, ?_, ht_init, ?_, hlog_le⟩
  · rw [P.initRegs_eq hP]
    exact Machine.runs_map hS hr₀
  · rw [hP.stateMem_eq]
    exact unchangedOutside_of_modifies hmod₀
  · rw [hP.stateReg_eq, hP.stateMem_eq]
    exact P.runsClient_map hP hS c hruns
  · rw [← P.numQueries_eq hP tr.ops, ← P.numInserts_eq hP tr.ops, ← P.numDecreaseKeys_eq hP tr.ops]
    exact ht_ops

/-- Transfer of `FibonacciHeap.MinPQ.run_client_exact_reusable` (`O(n_max + 1)` clear initialization
on arbitrary `w`-bit memory) to any exact word-RAM presentation `S` and priority-queue presentation
`P`. -/
theorem amortized_reusable (S : WordRAMBridge.Presentation) (hS : WordRAMBridge.Laws S)
    (P : PQPresentation S) (hP : PQLaws S P) :
    ∃ r, ∃ p_init p_op : List (S.Instr r), ∃ K,
      ∀ (n_max U V base w : ℕ) (mem₀ : ℕ → ℕ) (c : P.Client n_max),
        base + (11 * n_max + 1) < 2 ^ w →
        U < 2 ^ w →
        V < 2 ^ w →
        (∀ a, mem₀ a < 2 ^ w) →
        P.ValidClient U V (fun _ => none) c →
        ∃ t₀ t_init ops q_f reg_f mem_f t_ops extLog,
          Relation.RelatesInSteps (fun a b => S.step w p_init a = S.next b)
            (S.state 0 (P.initRegs n_max base) mem₀) t₀ t_init ∧
          (∃ out, S.step w p_init t₀ = S.halted out) ∧
          (∀ a, a < base ∨ base + (11 * n_max + 1) ≤ a → P.stateMem t₀ a = mem₀ a) ∧
          P.RunsClient w p_op base (11 * n_max + 1) (fun _ => none) (P.stateReg t₀) (P.stateMem t₀)
            c ops q_f reg_f mem_f t_ops extLog ∧
          t_init + 1 ≤ K * (n_max + 1) ∧
          t_ops ≤
            K * (P.numQueries ops + P.numInserts ops + P.numDecreaseKeys ops + extLog) ∧
          extLog ≤ P.numExtractMins ops * (Nat.log 2 n_max + 1) := by
  refine ⟨48, S.programOf FibonacciHeap.MinPQ.initClearProg,
    S.programOf FibonacciHeap.MinPQ.opProg, 421,
    fun n_max U V base w mem₀ c hsp hU hV hmem hv => ?_⟩
  obtain ⟨pc₀, x₀, t_init, _, tr, q_f, z, t_ops, hr₀, ⟨out, hh₀⟩, hmod₀, hruns, _,
      ht_init, ht_ops, _⟩ :=
    FibonacciHeap.MinPQ.run_client_exact_reusable (U := U) (V := V) hsp hU hV hmem
      (P.toLibClient (U := U) (V := V) c) (P.validClient_to_lib hP c _ hv)
  have hlog_le : FibonacciHeap.MinPQ.extractLogSum (MinPQ.empty n_max) tr ≤
      P.numExtractMins (tr.ops.map P.opOf) * (Nat.log 2 n_max + 1) := by
    rw [← P.numExtractMins_eq hP tr.ops]
    exact FibonacciHeap.MinPQ.extractLogSum_le_numExtractMins tr (MinPQ.empty n_max)
  refine ⟨S.state pc₀ x₀.regs x₀.mem, t_init, tr.ops.map P.opOf, q_f, z.regs, z.mem, t_ops,
    FibonacciHeap.MinPQ.extractLogSum (MinPQ.empty n_max) tr, ?_,
    ⟨out, Machine.step_halt hS hh₀⟩, ?_, ?_, ht_init, ?_, hlog_le⟩
  · rw [P.initRegs_eq hP]
    exact Machine.runs_map hS hr₀
  · rw [hP.stateMem_eq]
    exact unchangedOutside_of_modifies hmod₀
  · rw [hP.stateReg_eq, hP.stateMem_eq]
    exact P.runsClient_map hP hS c hruns
  · rw [← P.numQueries_eq hP tr.ops, ← P.numInserts_eq hP tr.ops, ← P.numDecreaseKeys_eq hP tr.ops]
    exact ht_ops

end CslibFrontierAbstracts.FibonacciHeapBridge
