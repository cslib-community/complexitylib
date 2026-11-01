/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Dijkstra.Cost
public import Complexity.DataStructure.AdjacencyList.Memory
public import Complexity.DataStructure.Dictionary.Memory
public import Complexity.DataStructure.PriorityQueue.BinaryHeap.Memory
import Complexity.Algorithms.WordRAM.Dijkstra.ListEncode

/-!
# Dijkstra's algorithm with a binary heap, over the memory oracle

The client `Cslib.Algorithms.Lean.Dijkstra.dijkstra` runs over three structures in one memory
(`framed`, a `Memory.Framed.prod`): the indexed binary heap
`Cslib.DataStructure.PriorityQueue.BinaryHeap.Memory.framed`, a direct-address table for the
tentative distances, and the adjacency arrays of the graph. `run` is one memory program for every
graph. It reads the word RAM's input convention (`ListInstance.encode`): it reads `n`, the source
and the number `m` of edges, allocates the distance table and the heap just past the input, where
memory is zero, and runs the linked client on the adjacency arrays of the input.

`run_spec` is the memory-level counterpart of `Cslib.Algorithms.WordRAM.Dijkstra.LogLinearSpec`:
at every word size that holds `8 (n + m + 2) (W + 2)`, every memory operation of `run` is
admissible, the cell `G.outAddr v` then holds the encoded distance from the source to `v`, and the
run costs at most `52 (m + 1) (⌊log₂ n⌋ + 1)` memory units. `exists_run_logLinear` exports the
bound as `O((m + 1) log n)`. Correctness is `dijkstra_correct` transported through the refinement
(`Refinement.simulates_client`); the cost is the client's operation count
(`totalCost_dijkstra_le`) at the structures' charges, transported by their amortized
certificates (`Refinement.Amortized.client`). The proofs here mention no register, instruction
or address beyond the layout of the input.

Executing memory programs on the word RAM is a separate, generic realization step, which this
file does not provide.

## Main definitions

* `memMethods`, `opCharge`: the methods of the three structures, and their charges.
* `inputGraph`: the adjacency arrays of the input convention.
* `framed`: the three structures as one framed refinement of `Dijkstra.spec`.
* `run`: read the input, allocate, and run Dijkstra's algorithm.

## Main results

* `dijkstra_eq`: the client does not depend on the key and value bounds of its interfaces.
* `holds_inputGraph`: the input holds the graph in the adjacency arrays.
* `run_spec`: admissibility, distances and memory cost of `run`.
* `exists_run_logLinear`: the same with an `O((m + 1) log n)` cost function.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Dijkstra.Memory

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.Algorithms.WordRAM.Dijkstra (ListInstance encodeDist)

/-! ## The client does not depend on its bounds -/

/-- The main loop does not depend on the key and value bounds `K` and `V`, which only restrict
admissibility. -/
theorem loop_eq (n K V K' V' k : ℕ) : @loop n K V k = @loop n K' V' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [loop, ih]
    rfl

/-- The client does not depend on the key and value bounds `K` and `V`. -/
theorem dijkstra_eq {n : ℕ} (K V K' V' : ℕ) (src : Fin n) :
    @dijkstra n K V src = @dijkstra n K' V' src := by
  simp only [dijkstra, loop_eq n K V K' V']

/-! ## The structures -/

/-- The methods of the heap `H`, the distance table `T` and the adjacency arrays `A`. -/
def memMethods (n K V w : ℕ) (H : BinaryHeap.Memory.Layout n) (T : Block)
    (A : AdjacencyList.Memory.Layout) : Methods (spec n K V) (Memory.spec w) :=
  Methods.prod (BinaryHeap.Memory.ops H)
    (Methods.prod (Dictionary.Memory.ops T) (AdjacencyList.Memory.ops A))

/-- The adjacency arrays of the input convention: the `n + 1` offsets at address `3`, and the `m`
edges from address `n + 4`. -/
def inputGraph (n m : ℕ) : AdjacencyList.Memory.Layout := ⟨⟨3, n + 1⟩, ⟨n + 4, 2 * m⟩⟩

variable {n K V w : ℕ} {H : BinaryHeap.Memory.Layout n} {T : Block}
  {A : AdjacencyList.Memory.Layout}

/-- The heap, the distance table and the adjacency arrays of the graph `adj`, as one framed
refinement of the interfaces of Dijkstra's algorithm. -/
def framed (hH : H.Valid w K) (hT : Dictionary.Memory.Valid T w n V) (hA : A.Valid n)
    (adj : AdjacencyList.State n) : Memory.Framed (spec n K V) w :=
  (BinaryHeap.Memory.framed hH).prod
    ((Dictionary.Memory.framed (n_max := n) hT).prod (AdjacencyList.Memory.framed adj hA))

/-- The composite's methods are `memMethods`. -/
theorem framed_methods (hH : H.Valid w K) (hT : Dictionary.Memory.Valid T w n V)
    (hA : A.Valid n) (adj : AdjacencyList.State n) :
    (framed hH hT hA adj).methods = memMethods n K V w H T A := rfl

/-- The methods do not depend on the bounds and the word size in their type. -/
theorem memMethods_eq (n K V w K' V' w' : ℕ) (H : BinaryHeap.Memory.Layout n) (T : Block)
    (A : AdjacencyList.Memory.Layout) : memMethods n K V w H T A = memMethods n K' V' w' H T A := by
  funext o
  rcases o with o | o | o <;> rfl

/-- The charge of the composite: a heap operation costs `opCost n`, a distance-table operation
one unit and a graph query three units. -/
abbrev opCharge (n K V : ℕ) : (spec n K V).State → (spec n K V).Op → ℕ :=
  productCharge (fun _ _ => BinaryHeap.Memory.opCost n) (productCharge (fun _ _ => 1)
    fun _ _ => 3)

/-- Every operation of the composite costs at most its `charge`, with no potential. -/
theorem amortized (hH : H.Valid w K) (hT : Dictionary.Memory.Valid T w n V) (hA : A.Valid n)
    (adj : AdjacencyList.State n) :
    (framed hH hT hA adj).Amortized Memory.charge (opCharge n K V) fun _ => 0 :=
  Memory.Framed.amortized_prod (BinaryHeap.Memory.amortized hH)
    (Memory.Framed.amortized_prod (Dictionary.Memory.amortized hT)
      (AdjacencyList.Memory.amortized hA) (Memory.Framed.Local.const _ 0)
      (Memory.Framed.Local.const _ 0))
    (Memory.Framed.Local.const _ 0)
    (Memory.Framed.Local.const _ 0)

/-! ## The program -/

/-- **Dijkstra's algorithm over memory** on the word RAM's input convention: read `n`, the source
and the number `m` of edges, allocate the distance table and the heap past the input, and run the
client through the three structures. The key bound, value bound and word size in the types of
`memMethods` and `dijkstra` are `0`: they only restrict admissibility, and the program does not
depend on them (`dijkstra_eq`). -/
def run : Prog Unit := do
  let n ← read 1
  let src ← read 2
  let m ← read (n + 3)
  let T ← allocBlockDirty n
  let H ← BinaryHeap.Memory.allocLayout n
  if h : src < n then
    link (memMethods n 0 0 0 H T (inputGraph n m)) (dijkstra (K := 0) (V := 0) ⟨src, h⟩)
  else pure ()

/-! ## The input -/

/-- The input convention holds the graph in the adjacency arrays `inputGraph`. -/
theorem holds_inputGraph (G : ListInstance) :
    AdjacencyList.Memory.Holds (inputGraph G.n G.m) G.adj (Memory.State.init G.encode).mem := by
  set m := (Memory.State.init G.encode).mem with hm
  have hoff : ∀ j ≤ G.n, m (3 + j) = G.offset j := fun j hj => by
    rw [Nat.add_comm]
    exact G.init_offset (r := 0) hj
  refine ⟨fun u => ?_, fun u => ?_, fun u i hi => ?_, fun u i hi => ?_⟩
  · change m (3 + (u + 1)) = m (3 + u) + _
    rw [hoff _ u.isLt, hoff _ u.isLt.le, G.offset_succ u.isLt]
  · change 2 * m (3 + (u + 1)) ≤ 2 * G.m
    rw [hoff _ u.isLt, ← G.offset_n]
    exact Nat.mul_le_mul_left 2 (G.offset_mono u.isLt)
  · change m (G.n + 4 + 2 * (m (3 + u) + i)) = _
    rw [hoff _ u.isLt.le, show G.n + 4 + 2 * (G.offset u + i) = 2 * (G.offset u + i) + G.n + 4 by
      omega]
    exact G.init_target (r := 0) u hi
  · change m (G.n + 4 + (2 * (m (3 + u) + i) + 1)) = _
    rw [hoff _ u.isLt.le, show G.n + 4 + (2 * (G.offset u + i) + 1) =
      2 * (G.offset u + i) + G.n + 5 by omega]
    exact G.init_weight (r := 0) u hi

/-- A cell whose decoded value is `some d` exactly when the distance `D` is `d` holds the encoded
distance. -/
private theorem eq_encodeDist {x : ℕ} {D : ℕ∞}
    (h : ∀ d : ℕ, Dictionary.Memory.decode x = some d ↔ D = d) : x = encodeDist D := by
  cases x with
  | zero =>
    have hD : D = ⊤ := by
      by_contra hD
      obtain ⟨d, rfl⟩ := ENat.ne_top_iff_exists.mp hD
      simpa using (h d).mpr rfl
    simp [hD, encodeDist]
  | succ x =>
    have hD := (h x).mp rfl
    simp [hD, encodeDist]


/-! ## Correctness and cost -/

/-- The cost of Dijkstra's algorithm over memory, at most: `52 (m + 1) (⌊log₂ n⌋ + 1)`. -/
def memCost (n m : ℕ) : ℕ := 52 * (m + 1) * (Nat.log 2 n + 1)

/-- The client's operations, at the charges of the three structures, cost at most
`3 (m + 1) opCost n + 8 m + 4`, which with the six units of reading and allocating is within
`memCost`. -/
private theorem budget_le (n m : ℕ) :
    6 + (3 * (m + 1) * BinaryHeap.Memory.opCost n + 8 * m + 4) ≤ memCost n m := by
  unfold memCost BinaryHeap.Memory.opCost
  generalize Nat.log 2 n = L
  nlinarith

/-- **Dijkstra's algorithm over memory.** On the input words of a graph `G`, at every word size
`w` that holds `8 (n + m + 2) (W + 2)`, every memory operation of `run` is admissible, it costs at
most `memCost n m` memory units, and the cell `G.outAddr v` then holds the encoded distance from
the source to `v`, for every vertex `v`. -/
theorem run_triple (G : ListInstance) {w : ℕ}
    (hfit : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    Triple w (Memory.State.init G.encode) run (memCost G.n G.m)
      fun _ s' => ∀ v : Fin G.n, s'.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  set s₀ := Memory.State.init G.encode with hs₀
  have hf₀ : s₀.frontier = G.n + 2 * G.m + 4 := by
    simp only [s₀, Memory.State.init, G.encode_length]
  have hz : ZeroAbove s₀ := zeroAbove_init _
  have hn1 : s₀.mem 1 = G.n := rfl
  have hsrc : s₀.mem 2 = G.source := rfl
  have hm : s₀.mem (G.n + 3) = G.m := by
    rw [← G.offset_n]
    exact G.init_offset (r := 0) le_rfl
  -- The bounds of the interfaces and the facts that fit a word.
  set K := G.n * G.maxWeight with hK
  have hW : 2 ≤ G.maxWeight + 2 := by omega
  have hbig : 2 * (G.n + G.m + 2) ≤ 8 * (G.n + G.m + 2) * (G.maxWeight + 2) := by nlinarith
  have hn : Fits w G.n := hfit.of_le (by nlinarith)
  have hKf : Fits w K := hfit.of_le (by nlinarith)
  have hVf : Fits w (K + 1) := hfit.of_le (by nlinarith)
  -- The rate of each kind of operation.
  let rate : OpKind → ℕ
    | .insert => BinaryHeap.Memory.opCost G.n
    | .extractMin => BinaryHeap.Memory.opCost G.n
    | .decreaseKey => BinaryHeap.Memory.opCost G.n
    | .inspect => 0
    | .distance => 1
    | .graph => 3
  have hrate : rateBound rate G.n G.m ≤
      3 * (G.m + 1) * BinaryHeap.Memory.opCost G.n + 8 * G.m + 4 :=
    (min_le_right _ _).trans (by simp only [rate]; nlinarith)
  refine Triple.mono (c := rateBound rate G.n G.m + 6) ?_
    (by have := budget_le G.n G.m; omega) fun _ _ h => h
  refine Triple.read_bind (by omega) <| Triple.read_bind (by omega) ?_
  rw [hn1, hsrc]
  refine Triple.read_bind (by omega) ?_
  rw [hm]
  refine Triple.allocBlockDirty_bind (hfit.of_le (by nlinarith)) ?_
  refine BinaryHeap.Memory.allocLayout_bind
    (hfit.of_le (by simp only [PriorityQueue.WordRAM.BinaryHeap.space]; nlinarith)) ?_
  rw [dite_eq_left G.source.isLt]
  dsimp only
  -- The three structures, at the bounds `K` and `K + 1`, on the memory after allocation.
  set f := s₀.frontier with hf
  have hH : (BinaryHeap.Memory.allocated G.n (f + G.n)).Valid w K :=
    BinaryHeap.Memory.valid_allocated hn hKf
  have hT : Dictionary.Memory.Valid ⟨f, G.n⟩ w G.n (K + 1) := ⟨rfl, hVf⟩
  have hA : (inputGraph G.n G.m).Valid G.n := ⟨rfl⟩
  set M := framed hH hT hA G.adj with hM
  obtain ⟨hHinv, hHabs⟩ := BinaryHeap.Memory.inv_allocated (s := ⟨s₀.mem, f + G.n⟩)
    (hz.allocDirty G.n)
  obtain ⟨hTinv, hTabs⟩ := Dictionary.Memory.inv_alloc (U := G.n) hz
  have hsp : PriorityQueue.WordRAM.BinaryHeap.space G.n = 3 * G.n + 1 := rfl
  have hinv : M.inv ⟨s₀.mem, f + G.n + 1 + PriorityQueue.WordRAM.BinaryHeap.space G.n⟩ := by
    refine ⟨hHinv, ⟨Block.Allocated.mono hTinv (by simp only; omega),
      ⟨by simp only [inputGraph, Block.Allocated]; omega,
        by simp only [inputGraph, Block.Allocated]; omega, holds_inputGraph G⟩, ?_⟩, ?_⟩
    · simp only [Dictionary.Memory.framed_footprint, AdjacencyList.Memory.framed_footprint]
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Block.mem_footprint, Block.Owns, AdjacencyList.Memory.Layout.footprint,
        inputGraph, Finset.mem_union] at ha hb
      omega
    · simp only [Memory.Framed.prod_footprint, BinaryHeap.Memory.framed_footprint,
        Dictionary.Memory.framed_footprint, AdjacencyList.Memory.framed_footprint]
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Block.mem_footprint, Block.Owns, AdjacencyList.Memory.Layout.footprint,
        BinaryHeap.Memory.Layout.footprint, inputGraph, Finset.mem_union, hsp] at ha hb
      omega
  have habs : M.abs ⟨s₀.mem, f + G.n + 1 + PriorityQueue.WordRAM.BinaryHeap.space G.n⟩ =
      init G := by
    exact Prod.ext hHabs (Prod.ext hTabs rfl)
  obtain ⟨hvalid, hdist⟩ := dijkstra_correct (K := K) (V := K + 1) G le_rfl (by omega)
  rw [← habs] at hvalid hdist
  obtain ⟨hvE, -, hstate, -⟩ := M.simulates_client (dijkstra G.source) hinv hvalid
  have hcost := (amortized hH hT hA G.adj).client (dijkstra G.source) hinv hvalid
  have hcost' := totalCost_dijkstra_le (K := K) (V := K + 1) G le_rfl (by omega)
    (opCharge G.n K (K + 1)) rate fun s o ho => by
      rcases o with (_ | _ | _ | _ | _) | (_ | _) | (_ | _) <;>
        first | exact absurd rfl ho | simp [rate, kind, opCharge, productCharge]
  rw [← habs] at hcost'
  have hprog : link (memMethods G.n 0 0 0 (BinaryHeap.Memory.allocated G.n (f + G.n)) ⟨f, G.n⟩
      (inputGraph G.n G.m)) (dijkstra (K := 0) (V := 0) ⟨G.source, G.source.isLt⟩) =
      link M.methods (dijkstra (K := K) (V := K + 1) G.source) := by
    rw [hM, framed_methods, dijkstra_eq K (K + 1) 0 0, memMethods_eq G.n K (K + 1) w 0 0 0]
    rfl
  rw [hprog]
  refine triple_iff.mpr ⟨hvE, ?_, fun v => ?_⟩
  · exact (Nat.le_add_right _ _).trans (hcost.trans (Nat.add_le_add_right hcost' 0))
  obtain ⟨dist, hds, hdv⟩ := hdist
  rw [← hstate] at hds
  have hcell := congrArg (fun x => x.2.1 v) hds
  simp only [M, framed, Memory.Framed.prod_abs] at hcell
  refine eq_encodeDist fun d => ?_
  rw [show G.outAddr v = f + v by simp only [ListInstance.outAddr]; omega, ← hdv v d, ← hcell]
  exact Iff.rfl

/-- **Dijkstra's algorithm over memory, unpacked.** On the input words of a graph `G`, at every
word size that holds `8 (n + m + 2) (W + 2)`, every memory operation of `run` is admissible, the
cell `G.outAddr v` then holds the encoded distance from the source to `v`, and the run costs at
most `52 (m + 1) (⌊log₂ n⌋ + 1)` memory units. -/
theorem run_spec (G : ListInstance) {w : ℕ}
    (hfit : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    (Memory.spec w).ValidHistory (Memory.State.init G.encode)
        ((Memory.spec w).clientHistory (Memory.State.init G.encode) run) ∧
      (∀ v : Fin G.n, ((Memory.spec w).clientState (Memory.State.init G.encode) run).mem
        (G.outAddr v) = encodeDist (G.dist G.source v)) ∧
      (Memory.spec w).totalCost Memory.charge (Memory.State.init G.encode)
        ((Memory.spec w).clientHistory (Memory.State.init G.encode) run) ≤ memCost G.n G.m := by
  obtain ⟨hv, hc, hd⟩ := triple_iff.mp (run_triple G hfit)
  exact ⟨hv, hd, hc⟩

/-- `memCost` grows with the graph. -/
theorem memCost_mono {n m n' m' : ℕ} (hn : n ≤ n') (hm : m ≤ m') : memCost n m ≤ memCost n' m' := by
  unfold memCost
  have := Nat.log_mono_right (b := 2) hn
  gcongr

/-- **The exported form: `O((m + 1) log n)` memory units.** One memory program computes the
distances from the source of every graph, at every word size that holds `8 (n + m + 2) (W + 2)`,
admissibly and within `f (n, m)` memory units, for a monotone `f = O((m + 1) log n)` as `n` grows,
uniformly in `m`. Since `m + 1 ≤ n + m`, this is also `O((n + m) log n)`. -/
theorem exists_run_logLinear :
    ∃ f : ℕ × ℕ → ℕ, Monotone f ∧
      (fun p => (f p : ℝ)) =O[Filter.comap Prod.fst Filter.atTop]
        (fun ((n, m) : ℕ × ℕ) => ((m + 1) * Nat.log 2 n : ℝ)) ∧
      ∀ (G : ListInstance) (w : ℕ), Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) →
        (Memory.spec w).ValidHistory (Memory.State.init G.encode)
            ((Memory.spec w).clientHistory (Memory.State.init G.encode) run) ∧
          (∀ v : Fin G.n, ((Memory.spec w).clientState (Memory.State.init G.encode) run).mem
            (G.outAddr v) = encodeDist (G.dist G.source v)) ∧
          (Memory.spec w).totalCost Memory.charge (Memory.State.init G.encode)
            ((Memory.spec w).clientHistory (Memory.State.init G.encode) run) ≤ f (G.n, G.m) := by
  refine ⟨fun (n, m) => memCost n m, fun ⟨_, _⟩ ⟨_, _⟩ ⟨hn, hm⟩ => memCost_mono hn hm, ?_,
    fun G _ hfit => run_spec G hfit⟩
  refine Asymptotics.IsBigO.of_bound 104 ?_
  rw [Filter.eventually_comap]
  filter_upwards [Filter.eventually_ge_atTop 2] with b hb p hp
  obtain ⟨n, m⟩ := p
  simp only at hp
  subst hp
  have hL : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by simpa using hb)
  have h : memCost n m ≤ 104 * ((m + 1) * Nat.log 2 n) := by
    unfold memCost
    nlinarith
  simp only [Real.norm_natCast, norm_mul]
  rw [Real.norm_of_nonneg (by positivity)]
  exact_mod_cast h

end Cslib.Algorithms.Lean.Dijkstra.Memory
