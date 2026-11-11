/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Dijkstra.Memory
public import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Source

/-!
# Dijkstra's memory program with natural-number arguments

The source takes ordinary priority-queue memory programs as parameters. Its registers can carry
natural handles and keys; its extraction branch performs the original checked finite-handle
observation. No new priority-queue specification, backend or decoder is introduced. In
particular, relaxation retains the original `du + c < old` test and the fallback for an invalid
edge target. Arithmetic passed to an opaque method is staged explicitly as source `pure` steps.

The equalities retain the entire free-monad program, not only its answer. The binary instance
uses the original two-query dirty allocator and recovers `Dijkstra.Memory.run` exactly. Native
method certificates, reached-state domains, word-fit obligations and instruction bounds remain
separate requirements; the source equalities assign no free native cost to the staged values.

## Main definitions

* `relaxWord`, `scanWord`, `loopWord`, `clientWord`: the natural-argument client.
* `runWord`: read the graph input and allocate before executing that client.

## Main results

* `relaxWord_eq`, `scanWord_eq`, `loopWord_eq`, `clientWord_eq`: exact linked-source transport.
* `runWord_eq_binary`: the canonical binary-heap instance is the original memory program.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Dijkstra.Native

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue

/-- Read a tentative distance and perform the original insertion or decrease-key relaxation. -/
def relaxTarget (ins dec : ℕ → ℕ → Memory.Prog Unit) (T : Block) (v du c : ℕ) :
    Memory.Prog Unit := do
  let x ← read (T.base + v)
  let d ← pure (du + c)
  if x = 0 then
    write (T.base + v) (d + 1)
    ins v d
  else
    let old ← pure (x - 1)
    if d < old then
      write (T.base + v) (d + 1)
      dec v d

/-- Read one edge, retaining the source fallback for an invalid target, and relax its target. -/
def relaxWord (ins dec : ℕ → ℕ → Memory.Prog Unit) (T : Block)
    (A : AdjacencyList.Memory.Layout) (n u du i : ℕ) : Memory.Prog Unit := do
  let a ← read (A.offsets.base + u)
  let t ← read (A.edges.base + 2 * (a + i))
  let c ← read (A.edges.base + (2 * (a + i) + 1))
  if t < n then relaxTarget ins dec T t du c
  else relaxTarget ins dec T u du 0

private theorem relaxTarget_eq {n : ℕ} (ins dec : ℕ → ℕ → Memory.Prog Unit) (T : Block)
    (v : Fin n) (du c : ℕ) : relaxTarget ins dec T v du c = (do
      match ← Dictionary.Memory.query T v with
      | none => Dictionary.Memory.insert T v (du + c); ins v (du + c)
      | some old => if du + c < old then
        Dictionary.Memory.insert T v (du + c)
        dec v (du + c)) := by
  unfold relaxTarget Dictionary.Memory.query Dictionary.Memory.insert Block.get Block.set
  simp only [bind_assoc, pure_bind]
  congr 1 with x : 1
  cases x <;> simp [Dictionary.Memory.decode]

private theorem link_relaxEdge {n K V w : ℕ}
    (pq : Methods (indexedMinPQSpec n K) (Memory.spec w)) (T : Block)
    (A : AdjacencyList.Memory.Layout) (u : Fin n) (du i : ℕ) :
    link (Methods.prod pq (Methods.prod (Dictionary.Memory.ops T)
      (AdjacencyList.Memory.ops A))) (relaxEdge (K := K) (V := V) u du i) = (do
      let (v, c) ← AdjacencyList.Memory.edge A u i
      match ← Dictionary.Memory.query T v with
      | none => Dictionary.Memory.insert T v (du + c); pq (.insert v (du + c))
      | some old => if du + c < old then
        Dictionary.Memory.insert T v (du + c)
        pq (.decreaseKey v (du + c))) := by
  let M : Methods (spec n K V) (Memory.spec w) :=
    Methods.prod pq (Methods.prod (Dictionary.Memory.ops T) (AdjacencyList.Memory.ops A))
  have he : (edge (K := K) (V := V) u i).liftM M = AdjacencyList.Memory.edge A u i :=
    PFunctor.FreeM.liftM_lift (P := (spec n K V).signature) M (.inr (.inr (.edge u i)))
  have hg (v : Fin n) : (getDist (K := K) (V := V) v).liftM M =
      Dictionary.Memory.query T v :=
    PFunctor.FreeM.liftM_lift (P := (spec n K V).signature) M (.inr (.inl (.query v)))
  have hs (v : Fin n) (d : ℕ) : (setDist (K := K) (V := V) v d).liftM M =
      Dictionary.Memory.insert T v d :=
    PFunctor.FreeM.liftM_lift (P := (spec n K V).signature) M (.inr (.inl (.insert v d)))
  have hp (o : IndexedMinPQ.Op n) : (queue (K := K) (V := V) o).liftM M = pq o :=
    PFunctor.FreeM.liftM_lift (P := (spec n K V).signature) M (.inl o)
  change (relaxEdge (K := K) (V := V) u du i).liftM M = _
  unfold relaxEdge
  refine (PFunctor.FreeM.liftM_bind M (edge u i) _).trans ?_
  rw [he]
  congr 1 with vc : 1
  rcases vc with ⟨v, c⟩
  refine (PFunctor.FreeM.liftM_bind M (getDist v) _).trans ?_
  rw [hg]
  congr 1 with old : 1
  cases old with
  | none =>
    exact (PFunctor.FreeM.liftM_bind M (setDist v (du + c)) _).trans
      (by rw [hs, hp])
  | some old =>
    by_cases h : du + c < old
    · simp only [ite_eq_left h]
      exact (PFunctor.FreeM.liftM_bind M (setDist v (du + c)) _).trans
        (by rw [hs, hp])
    · simp only [ite_eq_right h]
      rfl

/-- The natural-argument relaxation is the complete original linked program. -/
theorem relaxWord_eq {n K V w : ℕ}
    (pq : Methods (indexedMinPQSpec n K) (Memory.spec w))
    (ins dec : ℕ → ℕ → Memory.Prog Unit)
    (hins : ∀ (v : Fin n) d, ins v d = pq (.insert v d))
    (hdec : ∀ (v : Fin n) d, dec v d = pq (.decreaseKey v d))
    (T : Block) (A : AdjacencyList.Memory.Layout) (u : Fin n) (du i : ℕ) :
    relaxWord ins dec T A n u du i =
      link (Methods.prod pq (Methods.prod (Dictionary.Memory.ops T)
        (AdjacencyList.Memory.ops A))) (relaxEdge (K := K) (V := V) u du i) := by
  change ((o : IndexedMinPQ.Op n) → Memory.Prog o.Result) at pq
  rw [link_relaxEdge]
  simp_rw [← hins, ← hdec]
  unfold relaxWord AdjacencyList.Memory.edge Block.get
  simp only [bind_assoc, pure_bind]
  congr 1 with a : 1
  congr 1 with t : 1
  congr 1 with c : 1
  by_cases ht : t < n
  · simpa only [ite_eq_left ht, dite_eq_left ht] using
      relaxTarget_eq ins dec T ⟨t, ht⟩ du c
  · simpa only [ite_eq_right ht, dite_eq_right ht] using
      relaxTarget_eq ins dec T u du 0

/-- Scan the returned degree with a bounded increasing edge-index loop. -/
def scanWord (ins dec : ℕ → ℕ → Memory.Prog Unit) (T : Block)
    (A : AdjacencyList.Memory.Layout) (n u du : ℕ) : Memory.Prog Unit := do
  let a ← read (A.offsets.base + u)
  let b ← read (A.offsets.base + (u + 1))
  let degree ← pure (b - a)
  let _ ← WordRAM.Realization.boundedWhile (fun (b i : ℕ) => i < b)
    (fun x => do relaxWord ins dec T A n u du x.2; pure (x.2 + 1)) degree degree 0
  pure ()

/-- The natural-argument scan retains every original query in its original order. -/
theorem scanWord_eq {n K V w : ℕ}
    (pq : Methods (indexedMinPQSpec n K) (Memory.spec w))
    (ins dec : ℕ → ℕ → Memory.Prog Unit)
    (hins : ∀ (v : Fin n) d, ins v d = pq (.insert v d))
    (hdec : ∀ (v : Fin n) d, dec v d = pq (.decreaseKey v d))
    (T : Block) (A : AdjacencyList.Memory.Layout) (u : Fin n) (du : ℕ) :
    scanWord ins dec T A n u du =
      link (Methods.prod pq (Methods.prod (Dictionary.Memory.ops T)
        (AdjacencyList.Memory.ops A))) (scan (K := K) (V := V) u du) := by
  rw [← scanView_eq]
  unfold scanWord scanView
  change _ = (AdjacencyList.Memory.degree A u >>= fun d : ℕ => do
    let _ ← WordRAM.Realization.boundedWhile (fun (b i : ℕ) => i < b)
      (fun x => do
        link (Methods.prod pq (Methods.prod (Dictionary.Memory.ops T)
          (AdjacencyList.Memory.ops A))) (relaxEdge (K := K) (V := V) u du x.2)
        pure (x.2 + 1)) d d 0
    pure ())
  unfold AdjacencyList.Memory.degree Block.get
  simp only [bind_assoc, pure_bind]
  congr 1 with a : 1
  congr 1 with b : 1
  have hb : (fun x : ℕ × ℕ => do
      relaxWord ins dec T A n u du x.2; pure (x.2 + 1)) =
      (fun x : ℕ × ℕ => do
        link (Methods.prod pq (Methods.prod (Dictionary.Memory.ops T)
          (AdjacencyList.Memory.ops A))) (relaxEdge (K := K) (V := V) u du x.2)
        pure (x.2 + 1)) := by
    funext x
    exact congrArg (fun p => p >>= fun _ => pure (x.2 + 1))
      (relaxWord_eq pq ins dec hins hdec T A u du x.2)
  rw [hb]

/-- Extract once; an empty or invalid observed entry sets the remaining rounds to zero. -/
def loopStepWord (extract : Memory.Prog (Option (ℕ × ℕ)))
    (ins dec : ℕ → ℕ → Memory.Prog Unit) (T : Block)
    (A : AdjacencyList.Memory.Layout) (n : ℕ) (x : Unit × ℕ) : Memory.Prog ℕ := do
  match ← extract with
  | none => pure 0
  | some (u, du) =>
    if u < n then
      scanWord ins dec T A n u du
      pure (x.2 - 1)
    else pure 0

/-- Checked observation transports one complete word-level extraction and scan. -/
theorem loopStepWord_eq {n K V w : ℕ}
    (pq : Methods (indexedMinPQSpec n K) (Memory.spec w))
    (extract : Memory.Prog (Option (ℕ × ℕ)))
    (ins dec : ℕ → ℕ → Memory.Prog Unit)
    (hins : ∀ (v : Fin n) d, ins v d = pq (.insert v d))
    (hdec : ∀ (v : Fin n) d, dec v d = pq (.decreaseKey v d))
    (hex : extract.map (fun a => a.bind fun p => BinaryHeap.Memory.entry n p.1 p.2) =
      pq .extractMin)
    (T : Block) (A : AdjacencyList.Memory.Layout) (x : Unit × ℕ) :
    loopStepWord extract ins dec T A n x =
      loopStep (K := K) (V := V) (Methods.prod pq (Methods.prod (Dictionary.Memory.ops T)
        (AdjacencyList.Memory.ops A))) x := by
  let M : Methods (spec n K V) (Memory.spec w) :=
    Methods.prod pq (Methods.prod (Dictionary.Memory.ops T) (AdjacencyList.Memory.ops A))
  let cont : Option (Fin n × ℕ) → Memory.Prog ℕ := fun e =>
    match e with
    | none => pure 0
    | some (u, du) => do scanView M u du; pure (x.2 - 1)
  have hstep : loopStep M x =
      Bind.bind (α := Option (Fin n × ℕ)) (pq .extractMin) cont := by
    unfold loopStep
    congr 1 with e : 1
    change Option (Fin n × ℕ) at e
    cases e <;> rfl
  change _ = loopStep M x
  rw [hstep]
  unfold loopStepWord cont
  rw [← hex, ← PFunctor.FreeM.bind_pure_comp]
  simp only [PFunctor.FreeM.bind_eq_bind, bind_assoc, pure_bind, Function.comp_apply]
  congr 1 with e : 1
  cases e with
  | none => rfl
  | some e =>
    rcases e with ⟨u, du⟩
    dsimp only [Option.bind_some]
    unfold BinaryHeap.Memory.entry
    by_cases hu : u < n
    · simp only [ite_eq_left hu, dite_eq_left hu]
      rw [scanWord_eq pq ins dec hins hdec (K := K) (V := V) T A ⟨u, hu⟩ du,
        scanView_eq]
    · simp only [ite_eq_right hu, dite_eq_right hu]

/-- Exact erasure of the original typed extraction transports the complete word-level round.
The checked runtime handle branch succeeds on every typed source reply; no decoder is assumed. -/
theorem loopStepWord_eq_of_erasure {n K V w : ℕ}
    (pq : Methods (indexedMinPQSpec n K) (Memory.spec w))
    (extract : Memory.Prog (Option (ℕ × ℕ)))
    (ins dec : ℕ → ℕ → Memory.Prog Unit)
    (hins : ∀ (v : Fin n) d, ins v d = pq (.insert v d))
    (hdec : ∀ (v : Fin n) d, dec v d = pq (.decreaseKey v d))
    (hex : extract = (pq .extractMin).map (Option.map fun p => (p.1.val, p.2)))
    (T : Block) (A : AdjacencyList.Memory.Layout) (x : Unit × ℕ) :
    loopStepWord extract ins dec T A n x =
      loopStep (K := K) (V := V) (Methods.prod pq (Methods.prod (Dictionary.Memory.ops T)
        (AdjacencyList.Memory.ops A))) x := by
  rw [hex]
  unfold loopStepWord loopStep
  rw [← PFunctor.FreeM.bind_pure_comp]
  simp only [PFunctor.FreeM.bind_eq_bind, bind_assoc, pure_bind, Function.comp_apply]
  congr 1 with e : 1
  change Option (Fin n × ℕ) at e
  cases e with
  | none => rfl
  | some e =>
    rcases e with ⟨u, du⟩
    simp only [Option.map_some, ite_eq_left u.isLt]
    rw [scanWord_eq pq ins dec hins hdec (K := K) (V := V) T A u du, scanView_eq]

/-- The original round cutoff with a genuine empty-queue exit. -/
def loopWord (extract : Memory.Prog (Option (ℕ × ℕ)))
    (ins dec : ℕ → ℕ → Memory.Prog Unit) (T : Block)
    (A : AdjacencyList.Memory.Layout) (n k : ℕ) : Memory.Prog Unit := do
  let _ ← WordRAM.Realization.boundedWhile (fun (_ : Unit) (a : ℕ) => a ≠ 0)
    (loopStepWord extract ins dec T A n) () k k
  pure ()

/-- The word-level main loop is exactly the original linked main loop. -/
theorem loopWord_eq {n K V w : ℕ}
    (pq : Methods (indexedMinPQSpec n K) (Memory.spec w))
    (extract : Memory.Prog (Option (ℕ × ℕ)))
    (ins dec : ℕ → ℕ → Memory.Prog Unit)
    (hins : ∀ (v : Fin n) d, ins v d = pq (.insert v d))
    (hdec : ∀ (v : Fin n) d, dec v d = pq (.decreaseKey v d))
    (hex : extract.map (fun a => a.bind fun p => BinaryHeap.Memory.entry n p.1 p.2) =
      pq .extractMin)
    (T : Block) (A : AdjacencyList.Memory.Layout) (k : ℕ) :
    loopWord extract ins dec T A n k =
      link (Methods.prod pq (Methods.prod (Dictionary.Memory.ops T)
        (AdjacencyList.Memory.ops A))) (loop (K := K) (V := V) k) := by
  rw [← loopView_eq]
  unfold loopWord loopView
  have hb : loopStepWord extract ins dec T A n =
      loopStep (K := K) (V := V) (Methods.prod pq (Methods.prod (Dictionary.Memory.ops T)
        (AdjacencyList.Memory.ops A))) :=
    funext (loopStepWord_eq pq extract ins dec hins hdec hex T A)
  rw [hb]

/-- Exact typed-result erasure preserves the full early-exit loop and its query history. -/
theorem loopWord_eq_of_erasure {n K V w : ℕ}
    (pq : Methods (indexedMinPQSpec n K) (Memory.spec w))
    (extract : Memory.Prog (Option (ℕ × ℕ)))
    (ins dec : ℕ → ℕ → Memory.Prog Unit)
    (hins : ∀ (v : Fin n) d, ins v d = pq (.insert v d))
    (hdec : ∀ (v : Fin n) d, dec v d = pq (.decreaseKey v d))
    (hex : extract = (pq .extractMin).map (Option.map fun p => (p.1.val, p.2)))
    (T : Block) (A : AdjacencyList.Memory.Layout) (k : ℕ) :
    loopWord extract ins dec T A n k =
      link (Methods.prod pq (Methods.prod (Dictionary.Memory.ops T)
        (AdjacencyList.Memory.ops A))) (loop (K := K) (V := V) k) := by
  rw [← loopView_eq]
  unfold loopWord loopView
  have hb : loopStepWord extract ins dec T A n =
      loopStep (K := K) (V := V) (Methods.prod pq (Methods.prod (Dictionary.Memory.ops T)
        (AdjacencyList.Memory.ops A))) :=
    funext (loopStepWord_eq_of_erasure pq extract ins dec hins hdec hex T A)
  rw [hb]

/-- Install the source distance, stage the zero key, and execute the original main loop. -/
def clientWord (extract : Memory.Prog (Option (ℕ × ℕ)))
    (ins dec : ℕ → ℕ → Memory.Prog Unit) (T : Block)
    (A : AdjacencyList.Memory.Layout) (n src : ℕ) : Memory.Prog Unit := do
  let z ← pure 0
  write (T.base + src) (z + 1)
  ins src z
  loopWord extract ins dec T A n n

/-- The word-level client retains the complete linked source. -/
theorem clientWord_eq {n K V w : ℕ}
    (pq : Methods (indexedMinPQSpec n K) (Memory.spec w))
    (extract : Memory.Prog (Option (ℕ × ℕ)))
    (ins dec : ℕ → ℕ → Memory.Prog Unit)
    (hins : ∀ (v : Fin n) d, ins v d = pq (.insert v d))
    (hdec : ∀ (v : Fin n) d, dec v d = pq (.decreaseKey v d))
    (hex : extract.map (fun a => a.bind fun p => BinaryHeap.Memory.entry n p.1 p.2) =
      pq .extractMin)
    (T : Block) (A : AdjacencyList.Memory.Layout) (src : Fin n) :
    clientWord extract ins dec T A n src =
      link (Methods.prod pq (Methods.prod (Dictionary.Memory.ops T)
        (AdjacencyList.Memory.ops A))) (dijkstra (K := K) (V := V) src) := by
  rw [← clientView_eq]
  unfold clientWord clientView
  simp only [pure_bind]
  rw [hins src 0, loopWord_eq pq extract ins dec hins hdec hex T A n, ← loopView_eq]
  rfl

/-- The complete initialized source client is unchanged by erasing typed extraction results. -/
theorem clientWord_eq_of_erasure {n K V w : ℕ}
    (pq : Methods (indexedMinPQSpec n K) (Memory.spec w))
    (extract : Memory.Prog (Option (ℕ × ℕ)))
    (ins dec : ℕ → ℕ → Memory.Prog Unit)
    (hins : ∀ (v : Fin n) d, ins v d = pq (.insert v d))
    (hdec : ∀ (v : Fin n) d, dec v d = pq (.decreaseKey v d))
    (hex : extract = (pq .extractMin).map (Option.map fun p => (p.1.val, p.2)))
    (T : Block) (A : AdjacencyList.Memory.Layout) (src : Fin n) :
    clientWord extract ins dec T A n src =
      link (Methods.prod pq (Methods.prod (Dictionary.Memory.ops T)
        (AdjacencyList.Memory.ops A))) (dijkstra (K := K) (V := V) src) := by
  rw [← clientView_eq]
  unfold clientWord clientView
  simp only [pure_bind]
  rw [hins src 0, loopWord_eq_of_erasure pq extract ins dec hins hdec hex T A n,
    ← loopView_eq]
  rfl

/-- Read the graph header, allocate the original distance table and supplied queue,
then run Dijkstra. -/
def runWord {ε : Type} (alloc : ℕ → Memory.Prog ε)
    (extract : ε → Memory.Prog (Option (ℕ × ℕ)))
    (ins dec : ε → ℕ → ℕ → Memory.Prog Unit) : Memory.Prog Unit := do
  let n ← read 1
  let src ← read 2
  let m ← read (n + 3)
  let T ← allocBlockDirty n
  let e ← alloc n
  if src < n then
    clientWord (extract e) (ins e) (dec e) T (Memory.inputGraph n m) n src

/-- The canonical binary-heap allocator and observed source methods recover the exact
original run. -/
theorem runWord_eq_binary
    (extract : (Σ n, BinaryHeap.Memory.Layout n) → Memory.Prog (Option (ℕ × ℕ)))
    (ins dec : (Σ n, BinaryHeap.Memory.Layout n) → ℕ → ℕ → Memory.Prog Unit)
    (hins : ∀ n (H : BinaryHeap.Memory.Layout n) (v : Fin n) d,
      ins ⟨n, H⟩ v d = BinaryHeap.Memory.insert H v d)
    (hdec : ∀ n (H : BinaryHeap.Memory.Layout n) (v : Fin n) d,
      dec ⟨n, H⟩ v d = BinaryHeap.Memory.decreaseKey H v d)
    (hex : ∀ n (H : BinaryHeap.Memory.Layout n),
      (extract ⟨n, H⟩).map (fun a => a.bind fun p => BinaryHeap.Memory.entry n p.1 p.2) =
        BinaryHeap.Memory.extractMin H) :
    runWord (fun n => do
      let H ← BinaryHeap.Memory.allocLayout n
      pure (⟨n, H⟩ : Σ n, BinaryHeap.Memory.Layout n)) extract ins dec = Memory.run := by
  unfold runWord Memory.run
  simp only [bind_assoc, pure_bind]
  congr 1 with n : 1
  congr 1 with src : 1
  congr 1 with m : 1
  congr 1 with T : 1
  congr 1 with H : 1
  by_cases hs : src < n
  · simp only [ite_eq_left hs, dite_eq_left hs]
    exact clientWord_eq (BinaryHeap.Memory.ops H) (extract ⟨n, H⟩)
      (ins ⟨n, H⟩) (dec ⟨n, H⟩) (hins n H) (hdec n H) (hex n H)
      T (Memory.inputGraph n m) ⟨src, hs⟩
  · simp only [ite_eq_right hs, dite_eq_right hs]

end Cslib.Algorithms.Lean.Dijkstra.Native
