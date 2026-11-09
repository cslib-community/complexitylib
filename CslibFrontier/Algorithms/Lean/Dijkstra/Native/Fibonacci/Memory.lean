/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Domain
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Allocation
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.ExtractSource
import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Domain
import CslibFrontier.Algorithms.WordRAM.Dijkstra.ListEncode

/-!
# The existing Dijkstra client over the framed Fibonacci heap

The existing indexed queue, distance table and adjacency arrays share one memory through
`Memory.Framed.prod`. Initialization reserves the original heap's `9 n + 5` cells without
clearing them: the actual input convention supplies zero memory beyond its frontier. The heap's
nonzero potential is retained in the composite amortized certificate.

These are source and memory-cost results. The native caller separately charges register
arithmetic, argument delivery, loop control, its initialized prefix and final halt.

## Main definitions

* `pqMethods`, `methods`, `framed`: the existing methods and their framed product.
* `run`: read the original graph input, reserve the table and heap, and run the original client.

## Main results

* `amortized`: the original heap potential telescopes over the shared memory.
* `inv_input`: dirty reservations in the input's zero tail establish the original initial state.
* `runWord_eq`: result-type erasure preserves the complete memory program.
-/

public section

namespace Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue
open Cslib.Algorithms.WordRAM.Dijkstra (ListInstance encodeDist)

/-- Interpret the existing indexed Fibonacci methods through their existing record layout. -/
@[expose] def pqMethods (n K w base : ℕ) :
    Methods (indexedMinPQSpec n K) (Memory.spec w) :=
  fun o => link ((FibonacciHeap.layout n base).methods w) (FibonacciHeap.methods n w K o)

/-- The original three Dijkstra interfaces over one shared memory. -/
@[expose] def methods (n K V w base : ℕ) (T : Block) (A : AdjacencyList.Memory.Layout) :
    Methods (spec n K V) (Memory.spec w) :=
  Methods.prod (pqMethods n K w base)
    (Methods.prod (Dictionary.Memory.ops T) (AdjacencyList.Memory.ops A))

/-- The heap, distance table and immutable graph, composed through the existing framed product. -/
@[expose] def framed {n K V w : ℕ} (hn : Fits w n) (hK : Fits w K) (base : ℕ)
    {T : Block} (hT : Dictionary.Memory.Valid T w n V)
    {A : AdjacencyList.Memory.Layout} (hA : A.Valid n) (adj : AdjacencyList.State n) :
    Memory.Framed (spec n K V) w :=
  (FibonacciHeap.framed hn hK base).prod
    ((Dictionary.Memory.framed (n_max := n) hT).prod (AdjacencyList.Memory.framed adj hA))

/-- The product uses exactly the original linked method table. -/
theorem framed_methods {n K V w base : ℕ} (hn : Fits w n) (hK : Fits w K)
    {T : Block} (hT : Dictionary.Memory.Valid T w n V)
    {A : AdjacencyList.Memory.Layout} (hA : A.Valid n) (adj : AdjacencyList.State n) :
    (framed hn hK base hT hA adj).methods = methods n K V w base T A := rfl

/-- Bounds and handler width restrict validity, without changing any source method. -/
theorem methods_eq (n K V w K' V' w' base : ℕ) (T : Block)
    (A : AdjacencyList.Memory.Layout) :
    methods n K V w base T A = methods n K' V' w' base T A := by
  funext o
  cases o with
  | inl o =>
    change link ((FibonacciHeap.layout n base).methods w) (FibonacciHeap.methods n w K o) =
      link ((FibonacciHeap.layout n base).methods w') (FibonacciHeap.methods n w' K' o)
    cases o <;> simp only [FibonacciHeap.methods, FibonacciHeap.Native.link_width]
  | inr o => rcases o with (_ | _) | (_ | _) <;> rfl

/-- Composite charges: the original Fibonacci amortized charge, one unit per table query and
three units per graph query. -/
@[expose] def opCharge (n K V : ℕ) : (spec n K V).State → (spec n K V).Op → ℕ :=
  productCharge (FibonacciHeap.charge n) (productCharge (fun _ _ => 1) fun _ _ => 3)

/-- The heap's original nonzero potential telescopes across both other disjoint structures. -/
theorem amortized {n K V w base : ℕ} (hn : Fits w n) (hK : Fits w K)
    {T : Block} (hT : Dictionary.Memory.Valid T w n V)
    {A : AdjacencyList.Memory.Layout} (hA : A.Valid n) (adj : AdjacencyList.State n) :
    (framed hn hK base hT hA adj).Amortized Memory.charge (opCharge n K V)
      (fun s => (FibonacciHeap.potential n ((FibonacciHeap.layout n base).abs s) + 0) +
        (0 + 0)) :=
  Memory.Framed.amortized_prod (FibonacciHeap.framed_amortized hn hK base)
    (Memory.Framed.amortized_prod (Dictionary.Memory.amortized hT)
      (AdjacencyList.Memory.amortized hA) (Memory.Framed.Local.const _ 0)
      (Memory.Framed.Local.const _ 0))
    (FibonacciHeap.potential_local hn hK base) (Memory.Framed.Local.const _ 0)

/-- Read the unchanged graph header, reserve the distance table and original Fibonacci layout
in the input's zero tail, and run the existing early-exit Dijkstra client. -/
@[expose] def run : Memory.Prog Unit := do
  let n ← read 1
  let src ← read 2
  let m ← read (n + 3)
  let T ← allocBlockDirty n
  let base ← allocDirty (9 * n + 5)
  if h : src < n then
    link (methods n 0 0 0 base T (Memory.inputGraph n m))
      (dijkstra (K := 0) (V := 0) ⟨src, h⟩)
  else pure ()

/-- The raw-word caller is the same complete source program, not merely an equal-answer run. -/
theorem runWord_eq :
    runWord (fun n => do
      let base ← allocDirty (9 * n + 5)
      pure (n, base))
      (fun d => link ((FibonacciHeap.layout d.1 d.2).methods 0)
        (FibonacciHeap.Native.extractRaw d.1))
      (fun d v k => link ((FibonacciHeap.layout d.1 d.2).methods 0)
        (FibonacciHeap.insert v k))
      (fun d v k => link ((FibonacciHeap.layout d.1 d.2).methods 0)
        (FibonacciHeap.decreaseKey d.1 v k)) = run := by
  unfold runWord run
  simp only [bind_assoc, pure_bind]
  congr 1
  funext n
  congr 1
  funext src
  congr 1
  funext m
  congr 1
  funext T
  congr 1
  funext base
  by_cases hs : src < n
  · simp only [ite_eq_left hs, dite_eq_left hs]
    exact clientWord_eq_of_erasure (pqMethods n 0 0 base) _ _ _
      (fun _ _ => rfl) (fun _ _ => rfl)
      (FibonacciHeap.Native.link_extractRaw_eq _ _) T (Memory.inputGraph n m) ⟨src, hs⟩
  · simp only [ite_eq_right hs, dite_eq_right hs]

/-- Dirty reservations after the original input establish the exact empty-queue, empty-table
and graph state, without a clearing loop or an extra zero-memory premise. -/
theorem inv_input (G : ListInstance) {w K V : ℕ}
    (hn : Fits w G.n) (hK : Fits w K)
    (hT : Dictionary.Memory.Valid ⟨(Memory.State.init G.encode).frontier, G.n⟩ w G.n V)
    (hA : (Memory.inputGraph G.n G.m).Valid G.n)
    (hfit : Fits w ((Memory.State.init G.encode).frontier + G.n + (9 * G.n + 5))) :
    let s₀ := Memory.State.init G.encode
    let s' : Memory.State := ⟨s₀.mem, s₀.frontier + G.n + (9 * G.n + 5)⟩
    (framed hn hK (s₀.frontier + G.n) hT hA G.adj).inv s' ∧
      (framed hn hK (s₀.frontier + G.n) hT hA G.adj).abs s' = init G := by
  intro s₀ s'
  obtain ⟨hHinv, hHabs⟩ := FibonacciHeap.framed_allocDirty hn hK
    ((zeroAbove_init G.encode).allocDirty G.n)
  obtain ⟨hTAinv, hTAabs, hTAlt⟩ := Memory.inv_tableGraph G hT hA (by omega) hfit
  refine ⟨⟨hHinv, hTAinv, ?_, hfit⟩, Prod.ext hHabs hTAabs⟩
  -- The heap lies past the table and the graph.
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [s₀, FibonacciHeap.framed_footprint, FibonacciHeap.footprint, Finset.mem_Ico] at ha
  have := hTAlt _ a hb
  omega

end Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci
