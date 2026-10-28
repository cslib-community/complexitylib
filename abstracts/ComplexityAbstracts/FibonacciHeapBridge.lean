/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.WordRAMBridge
import Complexity.Algorithms.WordRAM.PriorityQueue.FibonacciHeap

/-!
# Bridge for the Fibonacci-heap formal abstract

`FibonacciHeapAbstract.lean` defines an indexed min-priority queue from scratch, together with its
own exact word-RAM presentation, register calling convention, memory-confinement predicate and
multi-operation execution relation `RunsOps`. This file proves, for every word-RAM presentation `S`
satisfying `WordRAMBridge.Laws S` and every priority-queue presentation `P` satisfying `PQLaws S P`,
that the compiled library programs `initFreshProg`, `initClearProg` and `opProg` of
`Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap` realize `RunsOps` within the claimed
`O(1)` / `O(n)` initialization bounds and `O(m_q + m_ins + m_dec + m_ext (log n + 1))` amortized
operation bound (for `m_q` queries, `m_ins` insertions, `m_dec` key decreases, and `m_ext` minimum
extractions).

## Main results

* `PQPresentation.runsOps_map`: multi-operation runs of `FibonacciHeap.opProg` over `Basis.exact`
  translate step-for-step to `P.RunsOps` via `WordRAMBridge.Machine.runs_map`.
* `amortized_fresh`: transfers `FibonacciHeap.run_ops_exact_fresh` (`O(1)` fresh initialization on
  zeroed `[base, base + 9 n + 1)`) to any `S` and `P`.
* `amortized_reusable`: transfers `FibonacciHeap.run_ops_exact_reusable` (`O(n)` initialization on
  arbitrary `w`-bit memory) to any `S` and `P`.

## Syntax in the imports

`FibonacciHeap` is authored in the scoped word-RAM program syntax of
`Complexity/Computability/WordRAM/Notation.lean` and its exact-basis variant in
`Complexity/Computability/WordRAM/ExactNotation.lean`. All syntax rules, `macro_rules` and
tactics in those files are scoped to `Cslib.WordRAM`. Only the syntax category `wramStmt` and the
syntax abbreviation `wramBlock` are global, since Lean cannot scope syntax categories, and outside
`Cslib.WordRAM` `wramStmt` has no rules. `FibonacciHeapAbstract.lean` does not open
`Cslib.WordRAM`, so none of this syntax is active there.
-/

namespace ComplexityAbstracts.FibonacciHeapBridge

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open Cslib.Algorithms.WordRAM.PriorityQueue
open ComplexityTests.Abstracts
open WordRAMBridge

/-! ## Priority-queue presentation and agreement with `IndexedMinPQ` -/

/-- Polymorphic signature of the priority-queue definitions in `FibonacciHeapAbstract`, specialized
at register count `FibonacciHeap.rFib` (`42`) where the concrete programs live. -/
structure PQPresentation (S : WordRAMBridge.Presentation) where
  Op : ℕ → Type
  isEmpty {n : ℕ} : Op n
  getKey {n : ℕ} : Fin n → Op n
  insert {n : ℕ} : Fin n → ℕ → Op n
  decreaseKey {n : ℕ} : Fin n → ℕ → Op n
  extractMin {n : ℕ} : Op n
  op_induction {n : ℕ} {P : Op n → Prop} :
    P isEmpty → (∀ v, P (getKey v)) → (∀ v k, P (insert v k)) →
      (∀ v k, P (decreaseKey v k)) → P extractMin → ∀ o, P o
  chooseMin {n : ℕ} : Fin n × ℕ → Fin n × ℕ → Fin n × ℕ
  foldMin {n : ℕ} : List (Fin n × ℕ) → Option (Fin n × ℕ)
  findMin {n : ℕ} : (Fin n → Option ℕ) → Option (Fin n × ℕ)
  nextQueue {n : ℕ} : (Fin n → Option ℕ) → Op n → (Fin n → Option ℕ)
  DecodesStep {n : ℕ} : (Fin n → Option ℕ) → Op n → (Fin 42 → ℕ) → Prop
  ValidOp {n : ℕ} : ℕ → (Fin n → Option ℕ) → Op n → Prop
  ValidSeq {n : ℕ} : ℕ → (Fin n → Option ℕ) → List (Op n) → Prop
  numQueries {n : ℕ} : List (Op n) → ℕ
  numInserts {n : ℕ} : List (Op n) → ℕ
  numDecreaseKeys {n : ℕ} : List (Op n) → ℕ
  numExtractMins {n : ℕ} : List (Op n) → ℕ
  initRegs {r : ℕ} : ℕ → ℕ → Fin r → ℕ
  prepareRegs {n : ℕ} : Op n → (Fin 42 → ℕ) → Fin 42 → ℕ
  stateReg {r : ℕ} : S.State r → Fin r → ℕ
  stateMem {r : ℕ} : S.State r → ℕ → ℕ
  RunsOps {r n : ℕ} :
    ℕ → List (S.Instr r) → ℕ → ℕ → (Fin n → Option ℕ) → (Fin r → ℕ) → (ℕ → ℕ) →
      List (Op n) → (Fin r → ℕ) → (ℕ → ℕ) → ℕ → Prop

/-- Equational laws connecting a `PQPresentation` to the definitions in `FibonacciHeapAbstract`. -/
structure PQLaws (S : WordRAMBridge.Presentation) (P : PQPresentation S) : Prop where
  chooseMin_spec : ∀ {n} (a b : Fin n × ℕ),
    ((a.2 < b.2 ∨ (a.2 = b.2 ∧ (a.1 : ℕ) ≤ (b.1 : ℕ))) → P.chooseMin a b = a) ∧
    (¬(a.2 < b.2 ∨ (a.2 = b.2 ∧ (a.1 : ℕ) ≤ (b.1 : ℕ))) → P.chooseMin a b = b)
  foldMin_nil : ∀ {n}, P.foldMin (n := n) [] = none
  foldMin_cons : ∀ {n} (a : Fin n × ℕ) (l : List (Fin n × ℕ)),
    P.foldMin (a :: l) =
      match P.foldMin l with
      | none => some a
      | some b => some (P.chooseMin a b)
  findMin_eq : ∀ {n} (q : Fin n → Option ℕ),
    P.findMin q = P.foldMin ((List.finRange n).filterMap fun v => (q v).map (v, ·))
  next_isEmpty : ∀ {n} (q : Fin n → Option ℕ), P.nextQueue q P.isEmpty = q
  next_getKey : ∀ {n} (q : Fin n → Option ℕ) (v : Fin n), P.nextQueue q (P.getKey v) = q
  next_insert : ∀ {n} (q : Fin n → Option ℕ) (v : Fin n) (k : ℕ),
    P.nextQueue q (P.insert v k) = Function.update q v (some k)
  next_decreaseKey : ∀ {n} (q : Fin n → Option ℕ) (v : Fin n) (k : ℕ),
    P.nextQueue q (P.decreaseKey v k) = Function.update q v (some k)
  next_extractMin : ∀ {n} (q : Fin n → Option ℕ),
    P.nextQueue q P.extractMin =
      match P.findMin q with
      | none => q
      | some (u, _) => Function.update q u none
  decodes_isEmpty : ∀ {n} (q : Fin n → Option ℕ) (reg : Fin 42 → ℕ),
    (reg ⟨22, by decide⟩ ≠ 0 ↔ ∀ v, q v = none) → P.DecodesStep q P.isEmpty reg
  decodes_getKey : ∀ {n} (q : Fin n → Option ℕ) (v : Fin n) (reg : Fin 42 → ℕ),
    (if reg ⟨22, by decide⟩ = 0 then some none else some (some (reg ⟨24, by decide⟩))) =
      some (q v) → P.DecodesStep q (P.getKey v) reg
  decodes_insert : ∀ {n} (q : Fin n → Option ℕ) (v : Fin n) (k : ℕ) (reg : Fin 42 → ℕ),
    P.DecodesStep q (P.insert v k) reg
  decodes_decreaseKey : ∀ {n} (q : Fin n → Option ℕ) (v : Fin n) (k : ℕ) (reg : Fin 42 → ℕ),
    P.DecodesStep q (P.decreaseKey v k) reg
  decodes_extractMin : ∀ {n} (q : Fin n → Option ℕ) (reg : Fin 42 → ℕ),
    (if reg ⟨22, by decide⟩ = 0 then some none
     else if h : reg ⟨23, by decide⟩ < n then
       some (some (⟨reg ⟨23, by decide⟩, h⟩, reg ⟨24, by decide⟩))
     else none) =
      some (match P.findMin q with | none => none | some (u, k) => some (u, k)) →
    P.DecodesStep q P.extractMin reg
  valid_insert : ∀ {n K_max} (q : Fin n → Option ℕ) (v : Fin n) (k : ℕ),
    P.ValidOp K_max q (P.insert v k) → q v = none ∧ k ≤ K_max
  valid_decreaseKey : ∀ {n K_max} (q : Fin n → Option ℕ) (v : Fin n) (k : ℕ),
    P.ValidOp K_max q (P.decreaseKey v k) → (∃ k₀, q v = some k₀ ∧ k ≤ k₀) ∧ k ≤ K_max
  validSeq_cons : ∀ {n K_max} (q : Fin n → Option ℕ) (o : P.Op n) (ops : List (P.Op n)),
    P.ValidSeq K_max q (o :: ops) → P.ValidOp K_max q o ∧ P.ValidSeq K_max (P.nextQueue q o) ops
  queries_isEmpty : ∀ {n} (ops : List (P.Op n)),
    P.numQueries (P.isEmpty :: ops) = 1 + P.numQueries ops
  queries_getKey : ∀ {n} (v : Fin n) (ops : List (P.Op n)),
    P.numQueries (P.getKey v :: ops) = 1 + P.numQueries ops
  queries_insert : ∀ {n} (v : Fin n) (k : ℕ) (ops : List (P.Op n)),
    P.numQueries (P.insert v k :: ops) = P.numQueries ops
  queries_decreaseKey : ∀ {n} (v : Fin n) (k : ℕ) (ops : List (P.Op n)),
    P.numQueries (P.decreaseKey v k :: ops) = P.numQueries ops
  queries_extractMin : ∀ {n} (ops : List (P.Op n)),
    P.numQueries (P.extractMin :: ops) = P.numQueries ops
  queries_nil : ∀ {n}, P.numQueries (n := n) [] = 0
  inserts_isEmpty : ∀ {n} (ops : List (P.Op n)),
    P.numInserts (P.isEmpty :: ops) = P.numInserts ops
  inserts_getKey : ∀ {n} (v : Fin n) (ops : List (P.Op n)),
    P.numInserts (P.getKey v :: ops) = P.numInserts ops
  inserts_insert : ∀ {n} (v : Fin n) (k : ℕ) (ops : List (P.Op n)),
    P.numInserts (P.insert v k :: ops) = 1 + P.numInserts ops
  inserts_decreaseKey : ∀ {n} (v : Fin n) (k : ℕ) (ops : List (P.Op n)),
    P.numInserts (P.decreaseKey v k :: ops) = P.numInserts ops
  inserts_extractMin : ∀ {n} (ops : List (P.Op n)),
    P.numInserts (P.extractMin :: ops) = P.numInserts ops
  inserts_nil : ∀ {n}, P.numInserts (n := n) [] = 0
  dec_isEmpty : ∀ {n} (ops : List (P.Op n)),
    P.numDecreaseKeys (P.isEmpty :: ops) = P.numDecreaseKeys ops
  dec_getKey : ∀ {n} (v : Fin n) (ops : List (P.Op n)),
    P.numDecreaseKeys (P.getKey v :: ops) = P.numDecreaseKeys ops
  dec_insert : ∀ {n} (v : Fin n) (k : ℕ) (ops : List (P.Op n)),
    P.numDecreaseKeys (P.insert v k :: ops) = P.numDecreaseKeys ops
  dec_decreaseKey : ∀ {n} (v : Fin n) (k : ℕ) (ops : List (P.Op n)),
    P.numDecreaseKeys (P.decreaseKey v k :: ops) = 1 + P.numDecreaseKeys ops
  dec_extractMin : ∀ {n} (ops : List (P.Op n)),
    P.numDecreaseKeys (P.extractMin :: ops) = P.numDecreaseKeys ops
  dec_nil : ∀ {n}, P.numDecreaseKeys (n := n) [] = 0
  ext_isEmpty : ∀ {n} (ops : List (P.Op n)),
    P.numExtractMins (P.isEmpty :: ops) = P.numExtractMins ops
  ext_getKey : ∀ {n} (v : Fin n) (ops : List (P.Op n)),
    P.numExtractMins (P.getKey v :: ops) = P.numExtractMins ops
  ext_insert : ∀ {n} (v : Fin n) (k : ℕ) (ops : List (P.Op n)),
    P.numExtractMins (P.insert v k :: ops) = P.numExtractMins ops
  ext_decreaseKey : ∀ {n} (v : Fin n) (k : ℕ) (ops : List (P.Op n)),
    P.numExtractMins (P.decreaseKey v k :: ops) = P.numExtractMins ops
  ext_extractMin : ∀ {n} (ops : List (P.Op n)),
    P.numExtractMins (P.extractMin :: ops) = 1 + P.numExtractMins ops
  ext_nil : ∀ {n}, P.numExtractMins (n := n) [] = 0
  initRegs_spec : ∀ n base (i : Fin 42),
    P.initRegs n base i = if (i : ℕ) = 0 then n else if (i : ℕ) = 1 then base else 0
  prep_isEmpty : ∀ {n} (reg : Fin 42 → ℕ) (i : Fin 42),
    P.prepareRegs (n := n) P.isEmpty reg i =
      if (i : ℕ) = 17 then 0 else if (i : ℕ) = 18 then 0 else if (i : ℕ) = 19 then 0
      else if (i : ℕ) = 20 then 0 else if (i : ℕ) = 21 then 0 else reg i
  prep_getKey : ∀ {n} (v : Fin n) (reg : Fin 42 → ℕ) (i : Fin 42),
    P.prepareRegs (P.getKey v) reg i =
      if (i : ℕ) = 17 then 0 else if (i : ℕ) = 18 then 0 else if (i : ℕ) = 19 then 1
      else if (i : ℕ) = 20 then (v : ℕ) else if (i : ℕ) = 21 then 0 else reg i
  prep_insert : ∀ {n} (v : Fin n) (k : ℕ) (reg : Fin 42 → ℕ) (i : Fin 42),
    P.prepareRegs (P.insert v k) reg i =
      if (i : ℕ) = 17 then 0 else if (i : ℕ) = 18 then 1 else if (i : ℕ) = 19 then 0
      else if (i : ℕ) = 20 then (v : ℕ) else if (i : ℕ) = 21 then k else reg i
  prep_decreaseKey : ∀ {n} (v : Fin n) (k : ℕ) (reg : Fin 42 → ℕ) (i : Fin 42),
    P.prepareRegs (P.decreaseKey v k) reg i =
      if (i : ℕ) = 17 then 0 else if (i : ℕ) = 18 then 1 else if (i : ℕ) = 19 then 1
      else if (i : ℕ) = 20 then (v : ℕ) else if (i : ℕ) = 21 then k else reg i
  prep_extractMin : ∀ {n} (reg : Fin 42 → ℕ) (i : Fin 42),
    P.prepareRegs (n := n) P.extractMin reg i =
      if (i : ℕ) = 17 then 1 else if (i : ℕ) = 18 then 0 else if (i : ℕ) = 19 then 0
      else if (i : ℕ) = 20 then 0 else if (i : ℕ) = 21 then 0 else reg i
  stateReg_eq : ∀ (pc : ℕ) (reg : Fin 42 → ℕ) (m : ℕ → ℕ), P.stateReg (S.state pc reg m) = reg
  stateMem_eq : ∀ (pc : ℕ) (reg : Fin 42 → ℕ) (m : ℕ → ℕ), P.stateMem (S.state pc reg m) = m
  runsOps_nil : ∀ {n w} {p : List (S.Instr 42)} {base len} {q : Fin n → Option ℕ}
    {reg : Fin 42 → ℕ} {mem : ℕ → ℕ},
    P.RunsOps w p base len q reg mem [] reg mem 0
  runsOps_cons : ∀ {n w} {p : List (S.Instr 42)} {base len} {q : Fin n → Option ℕ}
    {reg : Fin 42 → ℕ} {mem : ℕ → ℕ} {o : P.Op n} {ops : List (P.Op n)} {t : S.State 42}
    {reg' : Fin 42 → ℕ} {mem' : ℕ → ℕ} {steps rest : ℕ},
    Relation.RelatesInSteps (fun a b => S.step w p a = S.next b)
      (S.state 0 (P.prepareRegs o reg) mem) t steps →
    (∃ out, S.step w p t = S.halted out) →
    P.DecodesStep q o (P.stateReg t) →
    (∀ a, a < base ∨ base + len ≤ a → P.stateMem t a = mem a) →
    P.RunsOps w p base len (P.nextQueue q o) (P.stateReg t) (P.stateMem t) ops reg' mem' rest →
    P.RunsOps w p base len q reg mem (o :: ops) reg' mem' ((steps + 1) + rest)

theorem forall_none_iff_dom_empty {n : ℕ} (q : Fin n → Option ℕ) :
    (∀ v, q v = none) ↔ IndexedMinPQ.dom q = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  exact forall_congr' fun v => IndexedMinPQ.notMem_dom_iff.symm

theorem unchangedOutside_of_modifies {base n : ℕ} {m m' : ℕ → ℕ}
    (hm : Modifies (Block.mk base (FibonacciHeap.space n)).footprint m m') :
    ∀ a, a < base ∨ base + (9 * n + 1) ≤ a → m' a = m a := by
  intro a ha
  apply hm a
  rw [Block.mem_footprint, Block.Owns]
  dsimp only [FibonacciHeap.space]
  omega

namespace PQPresentation

variable {S : WordRAMBridge.Presentation} (P : PQPresentation S)

/-- Translate a library `IndexedMinPQ.Op n` into `P.Op n`. -/
def opOf {n : ℕ} : IndexedMinPQ.Op n → P.Op n
  | .isEmpty => P.isEmpty
  | .getKey v => P.getKey v
  | .insert v k => P.insert v k
  | .decreaseKey v k => P.decreaseKey v k
  | .extractMin => P.extractMin

theorem opOf_surjective {n : ℕ} (o : P.Op n) : ∃ g : IndexedMinPQ.Op n, P.opOf g = o :=
  P.op_induction (P := fun o => ∃ g, P.opOf g = o) ⟨.isEmpty, rfl⟩ (fun v => ⟨.getKey v, rfl⟩)
    (fun v k => ⟨.insert v k, rfl⟩) (fun v k => ⟨.decreaseKey v k, rfl⟩) ⟨.extractMin, rfl⟩ o

theorem list_opOf_surjective {n : ℕ} (ops : List (P.Op n)) :
    ∃ gs : List (IndexedMinPQ.Op n), gs.map P.opOf = ops := by
  choose f hf using P.opOf_surjective (n := n)
  refine ⟨ops.map f, ?_⟩
  rw [List.map_map]
  conv_rhs => rw [← List.map_id ops]
  congr 1
  funext o
  exact hf o

section WithLaws

variable {P} (hP : PQLaws S P)
include hP

theorem chooseMin_eq {n : ℕ} (a b : Fin n × ℕ) :
    P.chooseMin a b = IndexedMinPQ.chooseMin a b := by
  by_cases h : IndexedMinPQ.PrioLE a b
  · simp only [IndexedMinPQ.chooseMin, h, ↓reduceIte]
    exact (hP.chooseMin_spec a b).1 h
  · simp only [IndexedMinPQ.chooseMin, h, ↓reduceIte]
    exact (hP.chooseMin_spec a b).2 h

theorem foldMin_eq {n : ℕ} (l : List (Fin n × ℕ)) :
    P.foldMin l = IndexedMinPQ.foldMin l := by
  induction l with
  | nil => exact hP.foldMin_nil
  | cons a l ih =>
    rw [hP.foldMin_cons, ih]
    simp only [IndexedMinPQ.foldMin]
    cases IndexedMinPQ.foldMin l with
    | none => rfl
    | some b =>
      dsimp only
      rw [chooseMin_eq hP]

theorem findMin_eq {n : ℕ} (q : Fin n → Option ℕ) :
    P.findMin q = IndexedMinPQ.findMin q := by
  rw [hP.findMin_eq, foldMin_eq hP, IndexedMinPQ.findMin]

theorem nextQueue_eq {n K_max : ℕ} (q : Fin n → Option ℕ) (g : IndexedMinPQ.Op n) :
    P.nextQueue q (P.opOf g) = ((IndexedMinPQ.spec n K_max).step q g).1 := by
  cases g with
  | isEmpty => exact hP.next_isEmpty q
  | getKey v => exact hP.next_getKey q v
  | insert v k => exact hP.next_insert q v k
  | decreaseKey v k => exact hP.next_decreaseKey q v k
  | extractMin =>
    rw [opOf, hP.next_extractMin, findMin_eq hP]
    simp only [IndexedMinPQ.spec]
    cases IndexedMinPQ.findMin q <;> rfl

theorem decodesStep_of_lib {n K_max : ℕ} (q : Fin n → Option ℕ) (g : IndexedMinPQ.Op n)
    (reg : Fin 42 → ℕ)
    (hd : FibonacciHeap.code.decode (n := n) (K_max := K_max) g reg =
      some ((IndexedMinPQ.spec n K_max).step q g).2) :
    P.DecodesStep q (P.opOf g) reg := by
  cases g with
  | isEmpty =>
    apply hP.decodes_isEmpty
    dsimp only [PQCode.decode, FibonacciHeap.code, FibonacciHeap.outFlag,
      IndexedMinPQ.spec] at hd
    have hd' : decide (reg ⟨22, _⟩ ≠ 0) = decide (IndexedMinPQ.dom q = ∅) :=
      Option.some.inj hd
    exact (decide_eq_decide.mp hd').trans (forall_none_iff_dom_empty q).symm
  | getKey v =>
    apply hP.decodes_getKey
    dsimp only [PQCode.decode, FibonacciHeap.code, FibonacciHeap.outFlag, FibonacciHeap.outK,
      IndexedMinPQ.spec] at hd
    exact hd
  | insert v k => exact hP.decodes_insert q v k reg
  | decreaseKey v k => exact hP.decodes_decreaseKey q v k reg
  | extractMin =>
    apply hP.decodes_extractMin
    rw [findMin_eq hP]
    dsimp only [PQCode.decode, FibonacciHeap.code, FibonacciHeap.outFlag, FibonacciHeap.outV,
      FibonacciHeap.outK, IndexedMinPQ.spec] at hd
    rcases hm : IndexedMinPQ.findMin q with _ | ⟨u, k⟩ <;> rw [hm] at hd <;> exact hd

theorem initRegs_eq (n base : ℕ) :
    P.initRegs (r := 42) n base = FibonacciHeap.initRegs n base := by
  funext i
  rw [hP.initRegs_spec]
  simp only [FibonacciHeap.initRegs, FibonacciHeap.nReg, FibonacciHeap.frontierReg, Fin.ext_iff]

theorem prepareRegs_eq {n : ℕ} (g : IndexedMinPQ.Op n) (reg : Fin 42 → ℕ) :
    P.prepareRegs (P.opOf g) reg = FibonacciHeap.prepareRegs g reg := by
  funext i
  cases g with
  | isEmpty =>
    rw [opOf, hP.prep_isEmpty]
    simp only [FibonacciHeap.prepareRegs, PQCode.encode,
      FibonacciHeap.tag2, FibonacciHeap.tag1, FibonacciHeap.tag0,
      FibonacciHeap.argV, FibonacciHeap.argK, Fin.ext_iff]
    split_ifs <;> omega
  | getKey v =>
    rw [opOf, hP.prep_getKey]
    simp only [FibonacciHeap.prepareRegs, PQCode.encode, FibonacciHeap.code,
      FibonacciHeap.tag2, FibonacciHeap.tag1, FibonacciHeap.tag0,
      FibonacciHeap.argV, FibonacciHeap.argK, Fin.ext_iff]
    split_ifs <;> omega
  | insert v k =>
    rw [opOf, hP.prep_insert]
    simp only [FibonacciHeap.prepareRegs, PQCode.encode, FibonacciHeap.code,
      FibonacciHeap.tag2, FibonacciHeap.tag1, FibonacciHeap.tag0,
      FibonacciHeap.argV, FibonacciHeap.argK, Fin.ext_iff]
    split_ifs <;> omega
  | decreaseKey v k =>
    rw [opOf, hP.prep_decreaseKey]
    simp only [FibonacciHeap.prepareRegs, PQCode.encode, FibonacciHeap.code,
      FibonacciHeap.tag2, FibonacciHeap.tag1, FibonacciHeap.tag0,
      FibonacciHeap.argV, FibonacciHeap.argK, Fin.ext_iff]
    split_ifs <;> omega
  | extractMin =>
    rw [opOf, hP.prep_extractMin]
    simp only [FibonacciHeap.prepareRegs, PQCode.encode, FibonacciHeap.code,
      FibonacciHeap.tag2, FibonacciHeap.tag1, FibonacciHeap.tag0,
      FibonacciHeap.argV, FibonacciHeap.argK, Fin.ext_iff]
    split_ifs <;> omega

theorem validSeq_to_lib {n K_max : ℕ} :
    ∀ (gs : List (IndexedMinPQ.Op n)) (q : Fin n → Option ℕ),
      P.ValidSeq K_max q (gs.map P.opOf) → (IndexedMinPQ.spec n K_max).ValidHistory q gs
  | [], _, _ => trivial
  | g :: gs, q, hv => by
    obtain ⟨hv_g, hv_gs⟩ := hP.validSeq_cons q (P.opOf g) (gs.map P.opOf) hv
    rw [nextQueue_eq hP (K_max := K_max)] at hv_gs
    refine ⟨?_, validSeq_to_lib gs _ hv_gs⟩
    cases g with
    | isEmpty | getKey _ | extractMin => trivial
    | insert v k => exact hP.valid_insert q v k hv_g
    | decreaseKey v k => exact hP.valid_decreaseKey q v k hv_g

theorem numQueries_eq {n : ℕ} :
    ∀ (gs : List (IndexedMinPQ.Op n)),
      FibonacciHeap.numQueries gs = P.numQueries (gs.map P.opOf)
  | [] => hP.queries_nil.symm
  | g :: gs => by
    have ih := numQueries_eq gs
    cases g <;>
      simp only [List.map_cons, opOf, FibonacciHeap.numQueries, ih,
        hP.queries_isEmpty, hP.queries_getKey, hP.queries_insert,
        hP.queries_decreaseKey, hP.queries_extractMin]

theorem numInserts_eq {n : ℕ} :
    ∀ (gs : List (IndexedMinPQ.Op n)),
      FibonacciHeap.numInserts gs = P.numInserts (gs.map P.opOf)
  | [] => hP.inserts_nil.symm
  | g :: gs => by
    have ih := numInserts_eq gs
    cases g <;>
      simp only [List.map_cons, opOf, FibonacciHeap.numInserts, ih,
        hP.inserts_isEmpty, hP.inserts_getKey, hP.inserts_insert,
        hP.inserts_decreaseKey, hP.inserts_extractMin]

theorem numDecreaseKeys_eq {n : ℕ} :
    ∀ (gs : List (IndexedMinPQ.Op n)),
      FibonacciHeap.numDecreaseKeys gs = P.numDecreaseKeys (gs.map P.opOf)
  | [] => hP.dec_nil.symm
  | g :: gs => by
    have ih := numDecreaseKeys_eq gs
    cases g <;>
      simp only [List.map_cons, opOf, FibonacciHeap.numDecreaseKeys, ih,
        hP.dec_isEmpty, hP.dec_getKey, hP.dec_insert,
        hP.dec_decreaseKey, hP.dec_extractMin]

theorem numExtractMins_eq {n : ℕ} :
    ∀ (gs : List (IndexedMinPQ.Op n)),
      FibonacciHeap.numExtractMins gs = P.numExtractMins (gs.map P.opOf)
  | [] => hP.ext_nil.symm
  | g :: gs => by
    have ih := numExtractMins_eq gs
    cases g <;>
      simp only [List.map_cons, opOf, FibonacciHeap.numExtractMins, ih,
        hP.ext_isEmpty, hP.ext_getKey, hP.ext_insert,
        hP.ext_decreaseKey, hP.ext_extractMin]

theorem runsOps_map (hS : WordRAMBridge.Laws S) {n K_max w base : ℕ} :
    ∀ {q : Fin n → Option ℕ} {x z : Data 42} {gs : List (IndexedMinPQ.Op n)} {total : ℕ},
      FibonacciHeap.RunsOps (K_max := K_max) w base q x gs z total →
      P.RunsOps w (S.programOf FibonacciHeap.opProg) base (9 * n + 1) q x.regs x.mem
        (gs.map P.opOf) z.regs z.mem total
  | _, _, _, _, _, .nil => hP.runsOps_nil
  | q, x, z, g :: gs, _,
      @FibonacciHeap.RunsOps.cons _ _ _ _ _ _ _ _ pc y _ steps rest hr ⟨out, hh⟩ hdec hmod hrest =>
    by
      have hr' : Relation.RelatesInSteps
          (fun a b => S.step w (S.programOf FibonacciHeap.opProg) a = S.next b)
          (S.state 0 (P.prepareRegs (P.opOf g) x.regs) x.mem)
          (S.state pc y.regs y.mem) steps := by
        rw [prepareRegs_eq hP]
        exact Machine.runs_map hS hr
      have hh' : S.step w (S.programOf FibonacciHeap.opProg) (S.state pc y.regs y.mem) =
          S.halted out :=
        Machine.step_halt hS hh
      have hdec' : P.DecodesStep q (P.opOf g) (P.stateReg (S.state pc y.regs y.mem)) := by
        rw [hP.stateReg_eq]
        exact decodesStep_of_lib hP q g y.regs hdec
      have hmod' : ∀ a, a < base ∨ base + (9 * n + 1) ≤ a →
          P.stateMem (S.state pc y.regs y.mem) a = x.mem a := by
        rw [hP.stateMem_eq]
        exact unchangedOutside_of_modifies hmod
      have ih := runsOps_map hS hrest
      rw [← nextQueue_eq hP (K_max := K_max)] at ih
      refine hP.runsOps_cons hr' ⟨out, hh'⟩ hdec' hmod' ?_
      rw [hP.stateReg_eq, hP.stateMem_eq]
      exact ih

end WithLaws

end PQPresentation

/-! ## Transfer of the standalone Fibonacci-heap theorems -/

/-- Transfer of `FibonacciHeap.run_ops_exact_fresh` (`O(1)` fresh initialization on zeroed
`[base, base + 9 n + 1)`) to any exact word-RAM presentation `S` and priority-queue presentation
`P`. -/
theorem amortized_fresh (S : WordRAMBridge.Presentation) (hS : WordRAMBridge.Laws S)
    (P : PQPresentation S) (hP : PQLaws S P) :
    ∃ r, ∃ p_init p_op : List (S.Instr r), ∃ K,
      ∀ (n K_max base w : ℕ) (mem₀ : ℕ → ℕ) (ops : List (P.Op n)),
        base + (9 * n + 1) < 2 ^ w →
        K_max < 2 ^ w →
        (∀ a, mem₀ a < 2 ^ w) →
        (∀ a, base ≤ a → a < base + (9 * n + 1) → mem₀ a = 0) →
        P.ValidSeq K_max (fun _ => none) ops →
        ∃ t₀ t_init reg_f mem_f t_ops,
          Relation.RelatesInSteps (fun a b => S.step w p_init a = S.next b)
            (S.state 0 (P.initRegs n base) mem₀) t₀ t_init ∧
          (∃ out, S.step w p_init t₀ = S.halted out) ∧
          (∀ a, a < base ∨ base + (9 * n + 1) ≤ a → P.stateMem t₀ a = mem₀ a) ∧
          P.RunsOps w p_op base (9 * n + 1) (fun _ => none) (P.stateReg t₀) (P.stateMem t₀) ops
            reg_f mem_f t_ops ∧
          t_init + 1 ≤ K ∧
          t_ops ≤
            K * (P.numQueries ops + P.numInserts ops + P.numDecreaseKeys ops +
              P.numExtractMins ops * (Nat.log 2 n + 1)) := by
  refine ⟨42, S.programOf FibonacciHeap.initFreshProg, S.programOf FibonacciHeap.opProg, 421,
    fun n K_max base w mem₀ ops hsp hK hmem hzero hv => ?_⟩
  obtain ⟨gs, rfl⟩ := P.list_opOf_surjective ops
  have hzero' : ∀ a ∈ (Block.mk base (FibonacciHeap.space n)).footprint, mem₀ a = 0 := by
    intro a ha
    rw [Block.mem_footprint, Block.Owns] at ha
    exact hzero a ha.1 ha.2
  obtain ⟨pc₀, x₀, t_init, z, t_ops, hr₀, ⟨out, hh₀⟩, hmod₀, hruns, ht_init, ht_ops⟩ :=
    FibonacciHeap.run_ops_exact_fresh (K_max := K_max) hsp hK hmem hzero' gs
      (P.validSeq_to_lib hP gs _ hv)
  refine ⟨S.state pc₀ x₀.regs x₀.mem, t_init, z.regs, z.mem, t_ops, ?_,
    ⟨out, Machine.step_halt hS hh₀⟩, ?_, ?_, ht_init, ?_⟩
  · rw [P.initRegs_eq hP]
    exact Machine.runs_map hS hr₀
  · rw [hP.stateMem_eq]
    exact unchangedOutside_of_modifies hmod₀
  · rw [hP.stateReg_eq, hP.stateMem_eq]
    exact P.runsOps_map hP hS hruns
  · rw [← P.numQueries_eq hP, ← P.numInserts_eq hP, ← P.numDecreaseKeys_eq hP,
      ← P.numExtractMins_eq hP]
    exact ht_ops

/-- Transfer of `FibonacciHeap.run_ops_exact_reusable` (`O(n)` clear initialization on arbitrary
`w`-bit memory) to any exact word-RAM presentation `S` and priority-queue presentation `P`. -/
theorem amortized_reusable (S : WordRAMBridge.Presentation) (hS : WordRAMBridge.Laws S)
    (P : PQPresentation S) (hP : PQLaws S P) :
    ∃ r, ∃ p_init p_op : List (S.Instr r), ∃ K,
      ∀ (n K_max base w : ℕ) (mem₀ : ℕ → ℕ) (ops : List (P.Op n)),
        base + (9 * n + 1) < 2 ^ w →
        K_max < 2 ^ w →
        (∀ a, mem₀ a < 2 ^ w) →
        P.ValidSeq K_max (fun _ => none) ops →
        ∃ t₀ t_init reg_f mem_f t_ops,
          Relation.RelatesInSteps (fun a b => S.step w p_init a = S.next b)
            (S.state 0 (P.initRegs n base) mem₀) t₀ t_init ∧
          (∃ out, S.step w p_init t₀ = S.halted out) ∧
          (∀ a, a < base ∨ base + (9 * n + 1) ≤ a → P.stateMem t₀ a = mem₀ a) ∧
          P.RunsOps w p_op base (9 * n + 1) (fun _ => none) (P.stateReg t₀) (P.stateMem t₀) ops
            reg_f mem_f t_ops ∧
          t_init + 1 ≤ K * (n + 1) ∧
          t_ops ≤
            K * (P.numQueries ops + P.numInserts ops + P.numDecreaseKeys ops +
              P.numExtractMins ops * (Nat.log 2 n + 1)) := by
  refine ⟨42, S.programOf FibonacciHeap.initClearProg, S.programOf FibonacciHeap.opProg, 421,
    fun n K_max base w mem₀ ops hsp hK hmem hv => ?_⟩
  obtain ⟨gs, rfl⟩ := P.list_opOf_surjective ops
  obtain ⟨pc₀, x₀, t_init, z, t_ops, hr₀, ⟨out, hh₀⟩, hmod₀, hruns, ht_init, ht_ops⟩ :=
    FibonacciHeap.run_ops_exact_reusable (K_max := K_max) hsp hK hmem gs
      (P.validSeq_to_lib hP gs _ hv)
  refine ⟨S.state pc₀ x₀.regs x₀.mem, t_init, z.regs, z.mem, t_ops, ?_,
    ⟨out, Machine.step_halt hS hh₀⟩, ?_, ?_, ht_init, ?_⟩
  · rw [P.initRegs_eq hP]
    exact Machine.runs_map hS hr₀
  · rw [hP.stateMem_eq]
    exact unchangedOutside_of_modifies hmod₀
  · rw [hP.stateReg_eq, hP.stateMem_eq]
    exact P.runsOps_map hP hS hruns
  · rw [← P.numQueries_eq hP, ← P.numInserts_eq hP, ← P.numDecreaseKeys_eq hP,
      ← P.numExtractMins_eq hP]
    exact ht_ops

end ComplexityAbstracts.FibonacciHeapBridge
