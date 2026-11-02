/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Dijkstra.Native.Word
public import Complexity.Computability.WordRAM.Realization.Absorb
public import Complexity.Computability.WordRAM.Realization.Program.Standard
import Complexity.Algorithms.WordRAM.Dijkstra.ListEncode
import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Backend
import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Initialize
import Complexity.Tactic.Realize

/-!
# Native binary-heap Dijkstra from the memory client

The existing memory program is realized through its exact word-level source view, the original
heap methods and allocator, and the existing bounded-while rules. The graph representation and
the original client's admissible remaining history establish every reached callee domain.
A separate key invariant retains the advertised key bound; the structural heap invariant alone
does not assert it. Both loops retain their actual early exit and nontruncating cutoff.

This theorem uses the existing exact-basis machine and standard initialized-program exporter.
All register layouts, emitted code and clock factors precede runtime graphs, widths and memory.
The original word envelope is unchanged. Arithmetic, copies, source initialization and control
are charged; the result is not derived from memory-query counts alone. The flat endpoint also
retains the entire final memory and frontier of `Dijkstra.Memory.run`.

## Main results

* `realizes_run`: a uniform native realization of the original allocated memory program.
* `exists_program_state`: one flat program with a charged log-linear clock and exact final state.

The instruction factor is existential. No claim preserves the old handwritten implementation's
literal coefficients, and no Fibonacci-heap native endpoint is asserted here.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.Dijkstra.Native.Binary

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.Algorithms.WordRAM.Dijkstra (ListInstance encodeDist)

private abbrev TargetArgs := ((BinaryHeap.Native.HeapLayout × Block) × ℕ) × (ℕ × ℕ)
private abbrev word := WordEncoding.encode (α := ℕ)
private def targetInput := appendWords
  (appendWords (appendWords BinaryHeap.Native.layoutWords blockWords) word)
  (appendWords word word)

private def targetSafe (w : ℕ) (d : TargetArgs) (s : Memory.State) : Prop :=
  ∃ (hv : d.1.2 < d.1.1.1.1) (K : ℕ),
    d.1.1.1.2.Valid w K ∧ BinaryHeap.Memory.Inv d.1.1.1.2 s ∧
      d.1.1.2.Allocated s ∧ d.1.1.2.length = d.1.1.1.1 ∧
      Disjoint d.1.1.1.2.footprint d.1.1.2.footprint ∧ Fits w (d.2.1 + d.2.2 + 1) ∧
      match Dictionary.Memory.decode (s.mem (d.1.1.2.base + d.1.2)) with
      | none => IndexedMinPQ.valid K (BinaryHeap.Memory.abs d.1.1.1.2 s)
          (.insert ⟨d.1.2, hv⟩ (d.2.1 + d.2.2))
      | some old => d.2.1 + d.2.2 < old →
          IndexedMinPQ.valid K (BinaryHeap.Memory.abs d.1.1.1.2 s)
            (.decreaseKey ⟨d.1.2, hv⟩ (d.2.1 + d.2.2))

private theorem table_write_heap {n w K v z : ℕ} {H : BinaryHeap.Memory.Layout n}
    {T : Block} {s : Memory.State} (hL : H.Valid w K) (hi : BinaryHeap.Memory.Inv H s)
    (hv : v < T.length) (hd : Disjoint H.footprint T.footprint) :
    BinaryHeap.Memory.Inv H ⟨Function.update s.mem (T.base + v) z, s.frontier⟩ ∧
      BinaryHeap.Memory.abs H ⟨Function.update s.mem (T.base + v) z, s.frontier⟩ =
        BinaryHeap.Memory.abs H s := by
  have ha : T.base + v ∈ T.footprint := Block.mem_footprint.mpr (Block.owns_add hv)
  have he : ∀ a ∈ H.footprint, Function.update s.mem (T.base + v) z a = s.mem a := by
    intro a h
    have hne : a ≠ T.base + v := by
      intro he
      exact (Finset.disjoint_left.mp hd) (he ▸ h) ha
    exact Function.update_of_ne hne z s.mem
  exact ⟨hi.congr hL he le_rfl, BinaryHeap.Memory.abs_congr (s := s) he⟩

private theorem target_realizes : Realizes .exact (fun d : TargetArgs =>
    relaxTarget (fun v k => BinaryHeap.Memory.insert d.1.1.1.2 v k)
      (fun v k => BinaryHeap.Memory.decreaseKey d.1.1.1.2 v k)
      d.1.1.2 d.1.2 d.2.1 d.2.2)
    targetInput (WordEncoding.encode (α := Unit)) targetSafe (fun _ _ => 0) := by
  have hInsert := BinaryHeap.Native.realizes_insert
  have hDecrease := BinaryHeap.Native.realizes_decreaseKey
  realize
  all_goals rcases h with ⟨hv, K, hL, hi, ht, hlen, hd, hsum, hop⟩
  all_goals have hvT : d.1.2 < d.1.1.2.length := by omega
  all_goals try first
    | exact hmem.fits_of_lt_frontier (ht.lt_frontier hvT)
    | exact hsum.of_le (by omega)
    | omega
  case hsafe.right.right.isTrue.right =>
    obtain ⟨hi', he⟩ := table_write_heap hL hi hvT hd
      (T := d.1.1.2) (v := d.1.2) (z := d.2.1 + d.2.2 + 1)
    refine ⟨hv, K, hL, hi', ?_⟩
    rw [he]
    simpa only [hc, Dictionary.Memory.decode_zero] using hop
  case hsafe.right.right.isFalse.right.isTrue.right =>
    obtain ⟨hi', he⟩ := table_write_heap hL hi hvT hd
      (T := d.1.1.2) (v := d.1.2) (z := d.2.1 + d.2.2 + 1)
    refine ⟨hv, K, hL, hi', ?_⟩
    rw [he]
    have hx0 : s.mem (d.1.1.2.base + d.1.2) ≠ 0 := by assumption
    have hdecode : Dictionary.Memory.decode (s.mem (d.1.1.2.base + d.1.2)) =
        some (s.mem (d.1.1.2.base + d.1.2) - 1) := by
      cases hx : s.mem (d.1.1.2.base + d.1.2) with
      | zero => exact False.elim (hx0 hx)
      | succ x => rfl
    rw [hdecode] at hop
    exact hop hc

private theorem relax_valid_queue {n K V : ℕ} (s : (spec n K V).State)
    (u v : Fin n) (du i c : ℕ)
    (hg : AdjacencyList.step s.2.2 (.edge u i) = (s.2.2, (v, c)))
    (hv : (spec n K V).ValidHistory s
      ((spec n K V).clientHistory s (relaxEdge u du i))) :
    match s.2.1 v with
    | none => IndexedMinPQ.valid K s.1 (.insert v (du + c))
    | some old => du + c < old → IndexedMinPQ.valid K s.1 (.decreaseKey v (du + c)) := by
  cases hd : s.2.1 v with
  | none =>
    have hp := hv
    unfold relaxEdge at hp
    dsimp only [edge, getDist, setDist, queue, StateTransitionSpec.clientHistory,
      StateTransitionSpec.runClient, PFunctor.FreeM.lift, PFunctor.FreeM.bind,
      Bind.bind, Pure.pure, PFunctor.FreeM.instBind, PFunctor.FreeM.instPure,
      StateTransitionSpec.stepFn, productStepFn] at hp
    rw [hg] at hp
    dsimp only [Dictionary.step, StateTransitionSpec.runClient, PFunctor.FreeM.bind,
      Bind.bind, Pure.pure, PFunctor.FreeM.instBind, PFunctor.FreeM.instPure] at hp
    rw [hd] at hp
    exact hp.2.2.2.1
  | some old =>
    intro hc
    have hp := hv
    unfold relaxEdge at hp
    dsimp only [edge, getDist, setDist, queue, StateTransitionSpec.clientHistory,
      StateTransitionSpec.runClient, PFunctor.FreeM.lift, PFunctor.FreeM.bind,
      Bind.bind, Pure.pure, PFunctor.FreeM.instBind, PFunctor.FreeM.instPure,
      StateTransitionSpec.stepFn, productStepFn] at hp
    rw [hg] at hp
    dsimp only [Dictionary.step, StateTransitionSpec.runClient, PFunctor.FreeM.bind,
      Bind.bind, Pure.pure, PFunctor.FreeM.instBind, PFunctor.FreeM.instPure] at hp
    rw [hd] at hp
    dsimp only at hp
    rw [ite_eq_left hc] at hp
    exact hp.2.2.2.1

private theorem targetSafe_of_relax_valid (G : Algorithms.WordRAM.Dijkstra.ListInstance)
    {w : ℕ} (H : BinaryHeap.Memory.Layout G.n) (T : Block)
    (hH : H.Valid w (G.n * G.maxWeight))
    (hT : Dictionary.Memory.Valid T w G.n (G.n * G.maxWeight + 1))
    (s : Memory.State)
    (hf : (Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s)
    (u v : Fin G.n) (du i c : ℕ)
    (hg : AdjacencyList.step G.adj (.edge u i) = (G.adj, (v, c)))
    (hv : (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
      ((Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
      ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
        ((Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        (relaxEdge u du i)))
    (hdu : du ≤ G.n * G.maxWeight) (hc : c ≤ G.maxWeight)
    (hfit : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    targetSafe w (((⟨G.n, H⟩, T), v.val), (du, c)) s := by
  have hd := hf.2.2.1
  change Disjoint H.footprint (T.footprint ∪ (Memory.inputGraph G.n G.m).footprint) at hd
  refine ⟨v.isLt, G.n * G.maxWeight, hH, hf.1, hf.2.1.1, hT.length_eq,
    hd.mono_right Finset.subset_union_left, hfit.of_le (by nlinarith), ?_⟩
  exact relax_valid_queue _ u v du i c hg hv

private abbrev RelaxArgs := ((BinaryHeap.Native.HeapLayout × Block) × (ℕ × ℕ)) × (ℕ × ℕ × ℕ)
private def relaxInput := appendWords
  (appendWords (appendWords BinaryHeap.Native.layoutWords blockWords) (appendWords word word))
  (appendWords word (appendWords word word))

private def relaxSafe (w : ℕ) (d : RelaxArgs) (s : Memory.State) : Prop :=
  ∃ (G : Algorithms.WordRAM.Dijkstra.ListInstance) (H : BinaryHeap.Memory.Layout G.n)
    (hH : H.Valid w (G.n * G.maxWeight))
    (hT : Dictionary.Memory.Valid d.1.1.2 w G.n (G.n * G.maxWeight + 1)) (u : Fin G.n),
    d.1.1.1 = ⟨G.n, H⟩ ∧ d.1.2.1 = G.n ∧ d.1.2.2 = G.m ∧ d.2.1 = u.val ∧
      (Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s ∧
      d.2.2.1 ≤ G.n * G.maxWeight ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) ∧
      (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
        ((Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
          ((Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
          (relaxEdge u d.2.2.1 d.2.2.2))

private theorem relax_realizes : Realizes .exact (fun d : RelaxArgs =>
    relaxWord (fun v k => BinaryHeap.Memory.insert d.1.1.1.2 v k)
      (fun v k => BinaryHeap.Memory.decreaseKey d.1.1.1.2 v k) d.1.1.2
      ⟨⟨3, d.1.2.1 + 1⟩, ⟨d.1.2.1 + 4, 2 * d.1.2.2⟩⟩
      d.1.2.1 d.2.1 d.2.2.1 d.2.2.2)
    relaxInput (WordEncoding.encode (α := Unit)) relaxSafe (fun _ _ => 0) := by
  have hInsert := BinaryHeap.Native.realizes_insert
  have hDecrease := BinaryHeap.Native.realizes_decreaseKey
  have hTarget := target_realizes
  realize
  all_goals
    rcases d with ⟨⟨⟨e, T⟩, n, m⟩, vcur, du, i⟩
    rcases h with ⟨G, H, hH, hT, u, he, hn, hm, hu, hf, hdu, hfit, hv⟩
    dsimp only at he hn hm hu hT hdu hv ⊢
    subst e
    subst n
    subst m
    subst vcur
    have hA : AdjacencyList.Memory.Inv (Memory.inputGraph G.n G.m) G.adj s :=
      hf.2.1.2.1
    have hi : i < (G.adj u).length := hv.1
    have htgt := hA.holds.target u i hi
    change s.mem (G.n + 4 + 2 * (s.mem (3 + u.val) + i)) =
      ((G.adj u)[i]).1.val at htgt
    have hwt := hA.holds.weight u i hi
    change s.mem (G.n + 4 + (2 * (s.mem (3 + u.val) + i) + 1)) =
      ((G.adj u)[i]).2 at hwt
    have hbound : s.mem (G.n + 4 + 2 * (s.mem (3 + u.val) + i)) < G.n := by
      rw [htgt]
      exact ((G.adj u)[i]).1.isLt
    first
    | have hbad : ¬s.mem (G.n + 4 + 2 * (s.mem (3 + u.val) + i)) < G.n := by
        assumption
      exact False.elim (hbad hbound)
    | have hoff : 3 + u.val < s.frontier := hA.offsets_allocated.lt_frontier (by
        change u.val < G.n + 1
        have hu := u.isLt
        omega)
      have hlast := hA.edges_allocated.lt_frontier (hA.holds.edge_lt u hi)
      change G.n + 4 + (2 * (s.mem (3 + u.val) + i) + 1) < s.frontier at hlast
      first
      | exact hmem.frontier_fits.of_le (by omega)
      | rw [htgt, hwt]
        refine targetSafe_of_relax_valid G H T hH hT s hf u ((G.adj u)[i]).1 du i
          ((G.adj u)[i]).2 (AdjacencyList.step_edge G.adj u hi) hv hdu ?_ hfit
        exact G.le_maxWeight (List.getElem_mem hi)

private def remainingEdges {n K V : ℕ} (u : Fin n) (du b i : ℕ) :
    (spec n K V).Client Unit := (List.range' i (b - i)).forM (relaxEdge u du)

private theorem remainingEdges_cons {n K V : ℕ} (u : Fin n) (du b i : ℕ) (hi : i < b) :
    remainingEdges (K := K) (V := V) u du b i = (do
      relaxEdge u du i
      remainingEdges u du b (i + 1)) := by
  unfold remainingEdges
  have he : b - i = (b - (i + 1)) + 1 := by omega
  rw [he, List.range'_succ]
  rfl

private theorem remainingEdges_step {n K V w : ℕ}
    (M : Refinement (spec n K V) (Memory.spec w)) (u : Fin n) (du b i : ℕ)
    (s : Memory.State) (hi : i < b) (hinv : M.inv s)
    (hv : (spec n K V).ValidHistory (M.abs s)
      ((spec n K V).clientHistory (M.abs s) (remainingEdges u du b i))) :
    (spec n K V).ValidHistory (M.abs s)
      ((spec n K V).clientHistory (M.abs s) (relaxEdge u du i)) ∧
    M.inv ((Memory.spec w).clientState s (link M.methods (relaxEdge u du i))) ∧
    (spec n K V).ValidHistory
      (M.abs ((Memory.spec w).clientState s (link M.methods (relaxEdge u du i))))
      ((spec n K V).clientHistory
        (M.abs ((Memory.spec w).clientState s (link M.methods (relaxEdge u du i))))
        (remainingEdges u du b (i + 1))) := by
  rw [remainingEdges_cons u du b i hi, StateTransitionSpec.clientHistory_bind,
    StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient] at hv
  obtain ⟨_, _, he, hinv'⟩ := M.simulates_client (relaxEdge u du i) hinv hv.1
  refine ⟨hv.1, hinv', ?_⟩
  rw [he]
  exact hv.2

private theorem scan_while_safe (G : Algorithms.WordRAM.Dijkstra.ListInstance)
    {w : ℕ} (H : BinaryHeap.Memory.Layout G.n) (T : Block)
    (hH : H.Valid w (G.n * G.maxWeight))
    (hT : Dictionary.Memory.Valid T w G.n (G.n * G.maxWeight + 1))
    (u : Fin G.n) (du : ℕ) (s : Memory.State)
    (hf : (Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s)
    (hdu : du ≤ G.n * G.maxWeight)
    (hfit : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)))
    (hbfit : Fits w (G.adj u).length)
    (hv : (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
      ((Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
      ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
        ((Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        (remainingEdges u du (G.adj u).length 0)))
    (hm : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (boundedWhile (fun b i : ℕ => i < b) (fun x => do
        relaxWord (fun v k => BinaryHeap.Memory.insert H v k)
          (fun v k => BinaryHeap.Memory.decreaseKey H v k) T (Memory.inputGraph G.n G.m)
          G.n u.val du x.2
        pure (x.2 + 1)) (G.adj u).length (G.adj u).length 0))) :
    whileSafe (fun b i : ℕ => i < b) (fun x => do
      relaxWord (fun v k => BinaryHeap.Memory.insert H v k)
        (fun v k => BinaryHeap.Memory.decreaseKey H v k) T (Memory.inputGraph G.n G.m)
        G.n u.val du x.2
      pure (x.2 + 1))
      (fun w x s => relaxSafe w (((⟨G.n, H⟩, T), G.n, G.m), u.val, du, x.2) s ∧
        Fits w (x.2 + 1)) w (G.adj u).length (G.adj u).length 0 s := by
  let M := Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj
  let b := (G.adj u).length
  let p (i : ℕ) := relaxWord (fun v k => BinaryHeap.Memory.insert H v k)
    (fun v k => BinaryHeap.Memory.decreaseKey H v k) T (Memory.inputGraph G.n G.m)
    G.n u.val du i
  have heq (i : ℕ) : p i = link M.methods (relaxEdge u du i) :=
    relaxWord_eq (BinaryHeap.Memory.ops H) _ _ (fun _ _ => rfl) (fun _ _ => rfl) _ _ u du i
  let I (i : ℕ) (s : Memory.State) := i ≤ b ∧ M.inv s ∧
    (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory (M.abs s)
      ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory (M.abs s)
        (remainingEdges u du b i))
  apply whileSafe_of_measure _ _ _ w b I (fun i _ => b - i) ?_ ?_ ⟨Nat.zero_le _, hf, hv⟩
    (by omega) hm
  · intro a s hi hr hg
    have := hi.1
    omega
  · intro a s hi ha _
    obtain ⟨hfirst, hinv, hrest⟩ := remainingEdges_step M.toRefinement u du b a s ha hi.2.1 hi.2.2
    have hres : (Memory.spec 0).clientResult s (do p a; pure (a + 1)) = a + 1 := by
      rw [StateTransitionSpec.clientResult_bind]
      rfl
    have hstate : (Memory.spec 0).clientState s (do p a; pure (a + 1)) =
        (Memory.spec w).clientState s (link M.methods (relaxEdge u du a)) := by
      rw [StateTransitionSpec.clientState_bind]
      change (Memory.spec 0).clientState s (p a) = _
      rw [← clientState_width w, heq]
    refine ⟨⟨?_, hbfit.of_le (by omega)⟩, ?_, ?_⟩
    · exact ⟨G, H, hH, hT, u, rfl, rfl, rfl, rfl, hi.2.1, hdu, hfit, hfirst⟩
    · change I ((Memory.spec 0).clientResult s (do p a; pure (a + 1)))
        ((Memory.spec 0).clientState s (do p a; pure (a + 1)))
      rw [hres, hstate]
      exact ⟨by omega, hinv, hrest⟩
    · change b - (Memory.spec 0).clientResult s (do p a; pure (a + 1)) < b - a
      rw [hres]
      omega

private abbrev ScanArgs := ((BinaryHeap.Native.HeapLayout × Block) × (ℕ × ℕ)) × (ℕ × ℕ)
private def scanInput := appendWords
  (appendWords (appendWords BinaryHeap.Native.layoutWords blockWords) (appendWords word word))
  (appendWords word word)

private def scanSafe (w : ℕ) (d : ScanArgs) (s : Memory.State) : Prop :=
  ∃ (G : Algorithms.WordRAM.Dijkstra.ListInstance) (H : BinaryHeap.Memory.Layout G.n)
    (hH : H.Valid w (G.n * G.maxWeight))
    (hT : Dictionary.Memory.Valid d.1.1.2 w G.n (G.n * G.maxWeight + 1)) (u : Fin G.n),
    d.1.1.1 = ⟨G.n, H⟩ ∧ d.1.2.1 = G.n ∧ d.1.2.2 = G.m ∧ d.2.1 = u.val ∧
      (Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s ∧
      d.2.2 ≤ G.n * G.maxWeight ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) ∧
      (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
        ((Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
          ((Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
          (scan u d.2.2))

private theorem scan_realizes : Realizes .exact (fun d : ScanArgs =>
    scanWord (fun v k => BinaryHeap.Memory.insert d.1.1.1.2 v k)
      (fun v k => BinaryHeap.Memory.decreaseKey d.1.1.1.2 v k) d.1.1.2
      ⟨⟨3, d.1.2.1 + 1⟩, ⟨d.1.2.1 + 4, 2 * d.1.2.2⟩⟩
      d.1.2.1 d.2.1 d.2.2)
    scanInput (WordEncoding.encode (α := Unit)) scanSafe (fun _ _ => 0) := by
  have hRelax := relax_realizes
  realize
  all_goals
    rcases d with ⟨⟨⟨e, T⟩, n, m⟩, vcur, du⟩
    rcases h with ⟨G, H, hH, hT, u, he, hn, hm, hu, hf, hdu, hfit, hv⟩
    dsimp only at he hn hm hu hT hdu hv ⊢
    subst e
    subst n
    subst m
    subst vcur
    have hA : AdjacencyList.Memory.Inv (Memory.inputGraph G.n G.m) G.adj s :=
      hf.2.1.2.1
    have hoff : 3 + u.val < s.frontier := hA.offsets_allocated.lt_frontier (by
      change u.val < G.n + 1
      have hu := u.isLt
      omega)
    have hnext : 3 + (u.val + 1) < s.frontier := hA.offsets_allocated.lt_frontier (by
      change u.val + 1 < G.n + 1
      have hu := u.isLt
      omega)
    have hsucc := hA.holds.offset_succ u
    change s.mem (3 + (u.val + 1)) = s.mem (3 + u.val) + (G.adj u).length at hsucc
    first
    | exact hmem.fits_of_lt_frontier hoff
    | exact hmem.fits_of_lt_frontier hnext
    | omega
    | intro hm
      rw [hsucc, Nat.add_sub_cancel_left] at hm ⊢
      have hbfit : Fits w (G.adj u).length := (hmem.mem_fits (3 + (u.val + 1))).of_le (by omega)
      apply scan_while_safe G H T hH hT u du s hf hdu hfit hbfit ?_ hm
      unfold scan at hv
      dsimp only [degree, StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
        PFunctor.FreeM.lift, PFunctor.FreeM.bind, Bind.bind, Pure.pure,
        PFunctor.FreeM.instBind, PFunctor.FreeM.instPure, StateTransitionSpec.stepFn,
        productStepFn, AdjacencyList.step] at hv
      change _ ∧ (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
        ((Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
          ((Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
          ((List.range (G.adj u).length).forM (relaxEdge u du))) at hv
      simpa only [remainingEdges, Nat.sub_zero, List.range_eq_range'] using hv.2

private theorem loopStepWord_result_le (extract : Memory.Prog (Option (ℕ × ℕ)))
    (ins dec : ℕ → ℕ → Memory.Prog Unit) (T : Block)
    (A : AdjacencyList.Memory.Layout) (n : ℕ) (x : Unit × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (loopStepWord extract ins dec T A n x) ≤ x.2 - 1 := by
  unfold loopStepWord
  rw [StateTransitionSpec.clientResult_bind]
  cases he : (Memory.spec 0).clientResult s extract with
  | none =>
    change 0 ≤ x.2 - 1
    omega
  | some e =>
    rcases e with ⟨u, du⟩
    by_cases hu : u < n
    · simp only [ite_eq_left hu, StateTransitionSpec.clientResult_bind]
      rfl
    · simp only [ite_eq_right hu]
      change 0 ≤ x.2 - 1
      omega

private def abstractLoopStep {n K V : ℕ} (a : ℕ) : (spec n K V).Client ℕ := do
  match ← queue .extractMin with
  | none => pure 0
  | some (u, du) => scan u du; pure (a - 1)

private theorem loop_eq_step {n K V : ℕ} (a : ℕ) (ha : a ≠ 0) :
    loop (n := n) (K := K) (V := V) a = (do
      let b ← abstractLoopStep (n := n) (K := K) (V := V) a
      loop b) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  rw [loop]
  unfold abstractLoopStep
  simp only [bind_assoc]
  congr 1
  funext e
  cases e with
  | none => rfl
  | some e =>
    rcases e with ⟨u, du⟩
    simp only [bind_assoc, pure_bind, Nat.succ_sub_one]

private theorem loopStep_eq_link {n K V w : ℕ}
    (M : Methods (spec n K V) (Memory.spec w)) (a : ℕ) :
    loopStep M ((), a) = link M (abstractLoopStep (K := K) (V := V) a) := by
  symm
  unfold abstractLoopStep link
  refine (PFunctor.FreeM.liftM_bind M (queue .extractMin) _).trans ?_
  have hq : (queue (n := n) (K := K) (V := V) .extractMin).liftM M = M (.inl .extractMin) :=
    PFunctor.FreeM.liftM_lift (P := (spec n K V).signature) M (.inl .extractMin)
  rw [hq]
  unfold loopStep
  congr 1
  funext e
  change Option (Fin n × ℕ) at e
  cases e with
  | none => rfl
  | some e =>
    rcases e with ⟨u, du⟩
    dsimp only
    rw [PFunctor.FreeM.liftM_bind, scanView_eq]
    rfl

private theorem indexed_step_keys {n K : ℕ} (s : IndexedMinPQ.State n) (o : IndexedMinPQ.Op n)
    (hv : IndexedMinPQ.valid K s o)
    (hb : ∀ v k, s v = some k → k ≤ K) :
    ∀ v k, (IndexedMinPQ.step s o).1 v = some k → k ≤ K := by
  cases o with
  | isEmpty => exact hb
  | getKey _ => exact hb
  | insert u d | decreaseKey u d =>
    intro v k hk
    by_cases h : v = u
    · subst v
      simp only [IndexedMinPQ.step, Function.update_self] at hk
      cases hk
      exact hv.2
    · apply hb v k
      simpa only [IndexedMinPQ.step, Function.update_of_ne h] using hk
  | extractMin =>
    cases hf : IndexedMinPQ.findMin s with
    | none => simpa only [IndexedMinPQ.step, hf] using hb
    | some e =>
      rcases e with ⟨u, d⟩
      intro v k hk
      by_cases h : v = u
      · subst v
        simp only [IndexedMinPQ.step, hf, Function.update_self] at hk
        contradiction
      · apply hb v k
        simpa only [IndexedMinPQ.step, hf, Function.update_of_ne h] using hk

private theorem composite_step_keys {n K V : ℕ} (s : (spec n K V).State)
    (o : (spec n K V).Op) (hv : (spec n K V).valid s o)
    (hb : ∀ v k, s.1 v = some k → k ≤ K) :
    ∀ v k, ((spec n K V).stepFn s o).1.1 v = some k → k ≤ K := by
  cases o with
  | inl o => exact indexed_step_keys s.1 o hv hb
  | inr _ => exact hb

private theorem history_keys {n K V : ℕ} (s : (spec n K V).State)
    (os : List (spec n K V).Op) (hv : (spec n K V).ValidHistory s os)
    (hb : ∀ v k, s.1 v = some k → k ≤ K) :
    ∀ v k, ((spec n K V).run s os).1.1 v = some k → k ≤ K := by
  induction os generalizing s with
  | nil => exact hb
  | cons o os ih => exact ih _ hv.2 (composite_step_keys s o hv.1 hb)

private theorem client_keys {n K V : ℕ} {α : Type} (s : (spec n K V).State)
    (p : (spec n K V).Client α)
    (hv : (spec n K V).ValidHistory s ((spec n K V).clientHistory s p))
    (hb : ∀ v k, s.1 v = some k → k ≤ K) :
    ∀ v k, ((spec n K V).clientState s p).1 v = some k → k ≤ K := by
  have h := history_keys s _ hv hb
  exact (congrArg (fun t : (spec n K V).State => ∀ v k, t.1 v = some k → k ≤ K)
    ((spec n K V).run_runClient p s)).mp h

private abbrev StepArgs := ((BinaryHeap.Native.HeapLayout × Block) × (ℕ × ℕ)) × ℕ
private def stepInput := appendWords
  (appendWords (appendWords BinaryHeap.Native.layoutWords blockWords) (appendWords word word)) word

private def stepSafe (w : ℕ) (d : StepArgs) (s : Memory.State) : Prop :=
  ∃ (G : Algorithms.WordRAM.Dijkstra.ListInstance) (H : BinaryHeap.Memory.Layout G.n)
    (hH : H.Valid w (G.n * G.maxWeight))
    (hT : Dictionary.Memory.Valid d.1.1.2 w G.n (G.n * G.maxWeight + 1)),
    d.1.1.1 = ⟨G.n, H⟩ ∧ d.1.2.1 = G.n ∧ d.1.2.2 = G.m ∧
      (Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s ∧
      (∀ v k, BinaryHeap.Memory.abs H s v = some k → k ≤ G.n * G.maxWeight) ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) ∧ 0 < d.2 ∧
      (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
        ((Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
          ((Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
          (abstractLoopStep d.2))

private theorem step_realizes : Realizes .exact (fun d : StepArgs =>
    loopStepWord ((BinaryHeap.Memory.extractMin d.1.1.1.2).map
      (Option.map fun a => (a.1.val, a.2)))
      (fun v k => BinaryHeap.Memory.insert d.1.1.1.2 v k)
      (fun v k => BinaryHeap.Memory.decreaseKey d.1.1.1.2 v k) d.1.1.2
      ⟨⟨3, d.1.2.1 + 1⟩, ⟨d.1.2.1 + 4, 2 * d.1.2.2⟩⟩ d.1.2.1 ((), d.2))
    stepInput word stepSafe (fun _ _ => 0) := by
  have hScan := scan_realizes
  have hExtract := BinaryHeap.Native.realizes_extractMin
  realize
  all_goals
    rcases d with ⟨⟨⟨e, T⟩, n, m⟩, a⟩
    rcases h with ⟨G, H, hH, hT, he, hn, hm, hf, hb, hfit, ha, hv⟩
    dsimp only at he hn hm hT hb ha hv ⊢
    subst e
    subst n
    subst m
    first
    | exact ⟨G.n * G.maxWeight, hH, hf.1⟩
    | omega
    | let M := Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj
      unfold abstractLoopStep at hv
      rw [StateTransitionSpec.clientHistory_bind, StateTransitionSpec.validHistory_append,
        StateTransitionSpec.run_runClient] at hv
      obtain ⟨_, hres, hstate, hinv⟩ := M.simulates_client (queue .extractMin) hf hv.1
      have hql : link M.methods (queue (n := G.n) (K := G.n * G.maxWeight)
          (V := G.n * G.maxWeight + 1) .extractMin) = BinaryHeap.Memory.extractMin H :=
        PFunctor.FreeM.liftM_lift (P := (spec G.n (G.n * G.maxWeight)
          (G.n * G.maxWeight + 1)).signature) M.methods (.inl .extractMin)
      rw [hql] at hres hstate hinv
      change (Memory.spec w).clientResult s (BinaryHeap.Memory.extractMin H) = _ at hres
      change M.abs ((Memory.spec w).clientState s (BinaryHeap.Memory.extractMin H)) = _ at hstate
      change M.inv ((Memory.spec w).clientState s (BinaryHeap.Memory.extractMin H)) at hinv
      rw [clientResult_width] at hres
      rw [clientState_width] at hstate hinv
      have hrmap : (Memory.spec 0).clientResult s
          ((BinaryHeap.Memory.extractMin H).map (Option.map fun x => (x.1.val, x.2))) =
          Option.map (fun x => (x.1.val, x.2))
            ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientResult (M.abs s)
              (queue .extractMin)) := by
        rw [← PFunctor.FreeM.bind_pure_comp, StateTransitionSpec.clientResult,
          StateTransitionSpec.runClient_bind]
        simp only [Function.comp_apply, StateTransitionSpec.runClient_pure']
        change Option.map _ ((Memory.spec 0).clientResult s (BinaryHeap.Memory.extractMin H)) = _
        rw [hres]
      have hsmap : (Memory.spec 0).clientState s
          ((BinaryHeap.Memory.extractMin H).map (Option.map fun x => (x.1.val, x.2))) =
          (Memory.spec 0).clientState s (BinaryHeap.Memory.extractMin H) := by
        rw [← PFunctor.FreeM.bind_pure_comp, StateTransitionSpec.clientState,
          StateTransitionSpec.runClient_bind]
        rfl
      rw [hsmap, hrmap]
      cases hq : (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientResult (M.abs s)
          (queue .extractMin) with
      | none =>
        simp only [hrmap, hq, Option.map_none, optionWordsWith_none] at *
        contradiction
      | some uk =>
        rcases uk with ⟨u, du⟩
        simp only [Option.map_some, optionWordsWith_some]
        have hfind : IndexedMinPQ.findMin (BinaryHeap.Memory.abs H s) = some (u, du) := by
          have hqeq : (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientResult
              (M.abs s) (queue .extractMin) = IndexedMinPQ.findMin (BinaryHeap.Memory.abs H s) := by
            change (IndexedMinPQ.step (BinaryHeap.Memory.abs H s) .extractMin).2 = _
            cases h : IndexedMinPQ.findMin (BinaryHeap.Memory.abs H s) <;>
              simp only [IndexedMinPQ.step, h]
          rw [hqeq] at hq
          exact hq
        refine ⟨G, H, hH, hT, u, rfl, rfl, rfl, rfl, hinv,
          hb u du (IndexedMinPQ.findMin_eq_some_state hfind), hfit, ?_⟩
        rw [hstate]
        have htail := hv.2
        rw [hq] at htail
        dsimp only at htail
        rw [StateTransitionSpec.clientHistory_bind, StateTransitionSpec.validHistory_append,
          StateTransitionSpec.run_runClient] at htail
        exact htail.1

private def loopSafe (w : ℕ) (d : StepArgs) (s : Memory.State) : Prop :=
  ∃ (G : Algorithms.WordRAM.Dijkstra.ListInstance) (H : BinaryHeap.Memory.Layout G.n)
    (hH : H.Valid w (G.n * G.maxWeight))
    (hT : Dictionary.Memory.Valid d.1.1.2 w G.n (G.n * G.maxWeight + 1)),
    d.1.1.1 = ⟨G.n, H⟩ ∧ d.1.2.1 = G.n ∧ d.1.2.2 = G.m ∧
      (Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s ∧
      (∀ v k, BinaryHeap.Memory.abs H s v = some k → k ≤ G.n * G.maxWeight) ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) ∧
      (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
        ((Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
          ((Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
          (loop d.2))

private def stepProgram (d : StepArgs) : Memory.Prog ℕ :=
  loopStepWord ((BinaryHeap.Memory.extractMin d.1.1.1.2).map
    (Option.map fun a => (a.1.val, a.2)))
    (fun v k => BinaryHeap.Memory.insert d.1.1.1.2 v k)
    (fun v k => BinaryHeap.Memory.decreaseKey d.1.1.1.2 v k) d.1.1.2
    ⟨⟨3, d.1.2.1 + 1⟩, ⟨d.1.2.1 + 4, 2 * d.1.2.2⟩⟩ d.1.2.1 ((), d.2)

private def extendedBody (x : (StepArgs × ℕ) × ℕ) : Memory.Prog ℕ :=
  stepProgram (x.1.1.1, x.2)

private theorem extendedBody_realizes :
    Realizes .exact extendedBody (appendWords (appendWords stepInput word) word) word
      (fun w x s => stepSafe w (x.1.1.1, x.2) s) (fun _ _ => 0) := by
  apply step_realizes.reindex (fun x => (x.1.1.1, x.2))
    (appendWords (appendWords stepInput word) word)
    ![0, 1, 2, 3, 4, 5, 6, 7, 10]
  intro e i
  fin_cases i <;> rfl

private theorem nativeWhile_realizes :
    Realizes .exact (fun x : (StepArgs × ℕ) × ℕ =>
      boundedWhile (fun e a => e.2 < a) extendedBody x.1 x.1.1.2 x.2)
      (appendWords (appendWords stepInput word) word) word
      (fun w x s => whileSafe (fun e a => e.2 < a) extendedBody
        (fun w x s => stepSafe w (x.1.1.1, x.2) s) w x.1 x.1.1.2 x.2 s)
      (fun _ _ => 0) := by
  apply Realizes.while₀ (appendWords stepInput word) word (.lt 9 10)
    (fun x => x.1.1.2) extendedBody_realizes
  intro x s
  exact one_le_memoryCost_liftBind _ _ _

private theorem nativeWhile_valid_realizes :
    Realizes .exact (fun x : (StepArgs × ℕ) × ℕ =>
      boundedWhile (fun e a => e.2 < a) extendedBody x.1 x.1.1.2 x.2)
      (appendWords (appendWords stepInput word) word) word
      (fun w x s => (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
        (boundedWhile (fun e a => e.2 < a) extendedBody x.1 x.1.1.2 x.2)) →
        whileSafe (fun e a => e.2 < a) extendedBody
          (fun w x s => stepSafe w (x.1.1.1, x.2) s) w x.1 x.1.1.2 x.2 s)
      (fun _ _ => 0) :=
  nativeWhile_realizes.consequence_valid (fun _ _ _ _ _ hv h => h hv)

private theorem staged_loop_realizes : Realizes .exact (fun d : StepArgs => do
    let z ← pure 0
    let a ← pure d.2
    let _ ← boundedWhile (fun e a => e.2 < a) extendedBody (d, z) d.2 a
    pure ())
    stepInput (WordEncoding.encode (α := Unit)) loopSafe (fun _ _ => 0) := by
  have hW := nativeWhile_valid_realizes
  realize
  rcases d with ⟨⟨⟨e, T⟩, n, m⟩, a0⟩
  rcases h with ⟨G, H, hH, hT, he, hn, hm, hf, hb, hfit, hv⟩
  dsimp only at he hn hm hT hb hv ⊢
  subst e
  subst n
  subst m
  let M := Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj
  let e0 : StepArgs := (((⟨G.n, H⟩, T), G.n, G.m), a0)
  let I (a : ℕ) (s : Memory.State) := M.inv s ∧
    (∀ v k, (M.abs s).1 v = some k → k ≤ G.n * G.maxWeight) ∧
    (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory (M.abs s)
      ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory (M.abs s) (loop a))
  have heq (a : ℕ) : extendedBody ((e0, 0), a) = link M.methods (abstractLoopStep a) := by
    exact (loopStepWord_eq (BinaryHeap.Memory.ops H) _ _ _ (fun _ _ => rfl)
      (fun _ _ => rfl) (BinaryHeap.Native.extractMin_observation ⟨G.n, H⟩) T
      (Memory.inputGraph G.n G.m) ((), a)).trans (loopStep_eq_link M.methods a)
  intro hm
  apply whileSafe_of_measure _ _ _ w (e0, 0) I (fun a _ => a) ?_ ?_ ⟨hf, hb, hv⟩ le_rfl hm
  · intro a s _ hr
    change ¬0 < a
    omega
  · intro a s hi ha _
    change 0 < a at ha
    have hp := hi.2.2
    rw [loop_eq_step a (by omega), StateTransitionSpec.clientHistory_bind,
      StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient] at hp
    have hs := M.simulates_client (abstractLoopStep a) hi.1 hp.1
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨G, H, hH, hT, rfl, rfl, rfl, hi.1, hi.2.1, hfit, ha, hp.1⟩
    · rw [heq, ← clientResult_width w, ← clientState_width w]
      refine ⟨hs.2.2.2, ?_, ?_⟩
      · rw [hs.2.2.1]
        exact client_keys (M.abs s) (abstractLoopStep a) hp.1 hi.2.1
      · rw [hs.2.2.1, hs.2.1]
        exact hp.2
    · have hl := loopStepWord_result_le
        ((BinaryHeap.Memory.extractMin H).map (Option.map fun x => (x.1.val, x.2)))
        (fun v k => BinaryHeap.Memory.insert H v k)
        (fun v k => BinaryHeap.Memory.decreaseKey H v k) T
        (Memory.inputGraph G.n G.m) G.n ((), a) s
      change (Memory.spec 0).clientResult s (extendedBody ((e0, 0), a)) ≤ a - 1 at hl
      omega

private theorem loop_realizes : Realizes .exact (fun d : StepArgs =>
    loopWord ((BinaryHeap.Memory.extractMin d.1.1.1.2).map
      (Option.map fun a => (a.1.val, a.2)))
      (fun v k => BinaryHeap.Memory.insert d.1.1.1.2 v k)
      (fun v k => BinaryHeap.Memory.decreaseKey d.1.1.1.2 v k) d.1.1.2
      ⟨⟨3, d.1.2.1 + 1⟩, ⟨d.1.2.1 + 4, 2 * d.1.2.2⟩⟩ d.1.2.1 d.2)
    stepInput (WordEncoding.encode (α := Unit)) loopSafe (fun _ _ => 0) := by
  apply staged_loop_realizes.congr
  intro d
  simp only [pure_bind]
  unfold loopWord
  refine congrArg (fun p : Memory.Prog ℕ => p >>= fun _ => (pure () : Memory.Prog Unit)) ?_
  exact boundedWhile_congr (fun e a => e.2 < a) (fun (_ : Unit) a => a ≠ 0)
    (body := extendedBody)
    (body' := loopStepWord ((BinaryHeap.Memory.extractMin d.1.1.1.2).map
      (Option.map fun a => (a.1.val, a.2)))
      (fun v k => BinaryHeap.Memory.insert d.1.1.1.2 v k)
      (fun v k => BinaryHeap.Memory.decreaseKey d.1.1.1.2 v k) d.1.1.2
      ⟨⟨3, d.1.2.1 + 1⟩, ⟨d.1.2.1 + 4, 2 * d.1.2.2⟩⟩ d.1.2.1)
    (d := (d, 0)) (d' := ()) (fun a => by omega)
    (fun a => rfl) d.2 d.2

private theorem initial_loop_safe (G : Algorithms.WordRAM.Dijkstra.ListInstance) {w : ℕ}
    (hfit : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    loopSafe w
      (((⟨G.n, BinaryHeap.Memory.allocated G.n ((Memory.State.init G.encode).frontier + G.n)⟩,
        ⟨(Memory.State.init G.encode).frontier, G.n⟩), G.n, G.m), G.n)
      ((Memory.spec 0).clientState
        ⟨Function.update (Memory.State.init G.encode).mem
          ((Memory.State.init G.encode).frontier + G.source.val) 1,
          (Memory.State.init G.encode).frontier + G.n + 1 + WordRAM.BinaryHeap.space G.n⟩
        (BinaryHeap.Memory.insert
          (BinaryHeap.Memory.allocated G.n ((Memory.State.init G.encode).frontier + G.n))
          G.source.val 0)) := by
  let f := (Memory.State.init G.encode).frontier
  let H := BinaryHeap.Memory.allocated G.n (f + G.n)
  let T : Block := ⟨f, G.n⟩
  have hH : H.Valid w (G.n * G.maxWeight) := BinaryHeap.Memory.valid_allocated
    (hfit.of_le (by nlinarith)) (hfit.of_le (by nlinarith))
  have hT : Dictionary.Memory.Valid T w G.n (G.n * G.maxWeight + 1) :=
    ⟨rfl, hfit.of_le (by nlinarith)⟩
  let M := Memory.framed hH hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj
  let s0 : Memory.State := ⟨(Memory.State.init G.encode).mem,
    f + G.n + 1 + WordRAM.BinaryHeap.space G.n⟩
  have hfront : f = G.n + 2 * G.m + 4 := by simp only [f, Memory.State.init, G.encode_length]
  obtain ⟨hi, habs⟩ := Memory.inv_input G hH hT ⟨rfl⟩
    (hfit.of_le (by
      change Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) at hfit
      change f + G.n + 1 + WordRAM.BinaryHeap.space G.n ≤ _
      rw [hfront]
      unfold WordRAM.BinaryHeap.space
      nlinarith))
  let p : (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).Client Unit := do
    setDist G.source 0
    queue (.insert G.source 0)
  have hprog : dijkstra (K := G.n * G.maxWeight) (V := G.n * G.maxWeight + 1) G.source =
      (do p; loop G.n) := by
    unfold dijkstra p
    rw [bind_assoc]
  obtain ⟨hv, _⟩ := dijkstra_correct (K := G.n * G.maxWeight)
    (V := G.n * G.maxWeight + 1) G le_rfl (by omega)
  rw [← habs, hprog, StateTransitionSpec.clientHistory_bind,
    StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient] at hv
  obtain ⟨_, _, hstate, hinv⟩ := M.simulates_client p hi hv.1
  have hk := client_keys (M.abs s0) p hv.1 (by
    intro v k hk
    rw [habs] at hk
    change (none : Option ℕ) = some k at hk
    contradiction)
  have hpeq : link M.methods p = (do
      Dictionary.Memory.insert T G.source 0
      BinaryHeap.Memory.insert H G.source.val 0) := by
    unfold p link
    rw [PFunctor.FreeM.liftM_bind]
    have hset : (setDist (K := G.n * G.maxWeight) (V := G.n * G.maxWeight + 1)
        G.source 0).liftM M.methods = Dictionary.Memory.insert T G.source 0 :=
      PFunctor.FreeM.liftM_lift (P := (spec G.n (G.n * G.maxWeight)
        (G.n * G.maxWeight + 1)).signature) M.methods (.inr (.inl (.insert G.source 0)))
    rw [hset]
    congr 1
    funext _
    exact PFunctor.FreeM.liftM_lift (P := (spec G.n (G.n * G.maxWeight)
      (G.n * G.maxWeight + 1)).signature) M.methods (.inl (.insert G.source 0))
  have hs : (Memory.spec w).clientState s0 (link M.methods p) =
      (Memory.spec 0).clientState
        ⟨Function.update (Memory.State.init G.encode).mem (f + G.source.val) 1,
          f + G.n + 1 + WordRAM.BinaryHeap.space G.n⟩
        (BinaryHeap.Memory.insert H G.source.val 0) := by
    rw [hpeq, StateTransitionSpec.clientState_bind]
    change (Memory.spec w).clientState
        ⟨Function.update (Memory.State.init G.encode).mem (f + G.source.val) 1,
          f + G.n + 1 + WordRAM.BinaryHeap.space G.n⟩
        (BinaryHeap.Memory.insert H G.source.val 0) = _
    exact clientState_width _ _ _
  rw [hs] at hinv hstate
  refine ⟨G, H, hH, hT, rfl, rfl, rfl, hinv, ?_, hfit, ?_⟩
  · change ∀ v k, (M.abs _).1 v = some k → _
    rw [hstate]
    exact hk
  · change (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
      (M.abs _) ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
        (M.abs _) (loop G.n))
    rw [hstate]
    exact hv.2

private theorem initial_insert_safe (G : ListInstance) {w : ℕ}
    (hfit : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    BinaryHeap.Native.insertSafe w
      ((⟨G.n, BinaryHeap.Memory.allocated G.n
        ((Memory.State.init G.encode).frontier + G.n)⟩, G.source.val), 0)
      ⟨Function.update (Memory.State.init G.encode).mem
        ((Memory.State.init G.encode).frontier + G.source.val) 1,
        (Memory.State.init G.encode).frontier + G.n + 1 + WordRAM.BinaryHeap.space G.n⟩ := by
  let H := BinaryHeap.Memory.allocated G.n ((Memory.State.init G.encode).frontier + G.n)
  have hL : H.Valid w (G.n * G.maxWeight) :=
    BinaryHeap.Memory.valid_allocated (hfit.of_le (by nlinarith))
      (hfit.of_le (by nlinarith))
  have hz := (zeroAbove_init G.encode).allocDirty G.n
  obtain ⟨hi, ha⟩ := BinaryHeap.Memory.inv_allocated (n := G.n) hz
  have hframe : ∀ a ∈ H.footprint,
      Function.update (Memory.State.init G.encode).mem
        ((Memory.State.init G.encode).frontier + G.source.val) 1 a =
          (Memory.State.init G.encode).mem a := by
    intro a ha
    apply Function.update_of_ne
    have hlow := BinaryHeap.Memory.le_of_mem_footprint_allocated ha
    have hs := G.source.isLt
    omega
  refine ⟨G.source.isLt, G.n * G.maxWeight, hL, hi.congr hL hframe le_rfl, ?_⟩
  change BinaryHeap.Memory.abs H _ G.source = none ∧ 0 ≤ G.n * G.maxWeight
  rw [BinaryHeap.Memory.abs_congr
    (s := ⟨(Memory.State.init G.encode).mem,
      (Memory.State.init G.encode).frontier + G.n + 1 + WordRAM.BinaryHeap.space G.n⟩) hframe]
  exact ⟨congrFun ha G.source, Nat.zero_le _⟩

private theorem word_run_realizes : Realizes .exact
    (fun _ : Unit => runWord
      (fun n => do
        let H ← BinaryHeap.Memory.allocLayout n
        pure (⟨n, H⟩ : BinaryHeap.Native.HeapLayout))
      (fun d => (BinaryHeap.Memory.extractMin d.2).map
        (Option.map fun a => (a.1.val, a.2)))
      (fun d v k => BinaryHeap.Memory.insert d.2 v k)
      (fun d v k => BinaryHeap.Memory.decreaseKey d.2 v k))
    (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := Unit))
    (fun w _ s => ∃ G : ListInstance, s = Memory.State.init G.encode ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) (fun _ _ => 0) := by
  have hAlloc := BinaryHeap.Native.Initialize.realizes_allocLayout
  have hInsert := BinaryHeap.Native.realizes_insert
  have hDecrease := BinaryHeap.Native.realizes_decreaseKey
  have hLoop := loop_realizes
  unfold runWord Memory.inputGraph
  realize
  case hsafe.left =>
    rcases h with ⟨G, rfl, hfit⟩
    exact hfit.of_le (by nlinarith)
  case hsafe.right.left =>
    rcases h with ⟨G, rfl, hfit⟩
    exact hfit.of_le (by nlinarith)
  case hsafe.right.right.left =>
    rcases h with ⟨G, rfl, hfit⟩
    change Fits w (G.n + 3)
    exact hfit.of_le (by nlinarith)
  case hsafe.right.right.right.left =>
    rcases h with ⟨G, rfl, hfit⟩
    change Fits w ((Memory.State.init G.encode).frontier + G.n + 1 +
      WordRAM.BinaryHeap.space G.n)
    have hf : (Memory.State.init G.encode).frontier = G.n + 2 * G.m + 4 := by
      simp only [Memory.State.init, G.encode_length]
    rw [hf]
    exact hfit.of_le (by unfold WordRAM.BinaryHeap.space; nlinarith)
  case hsafe.right.right.right.right.isTrue.left.left =>
    rcases h with ⟨G, rfl, hfit⟩
    change Fits w ((Memory.State.init G.encode).frontier + G.source.val)
    have hf : (Memory.State.init G.encode).frontier = G.n + 2 * G.m + 4 := by
      simp only [Memory.State.init, G.encode_length]
    rw [hf]
    exact hfit.of_le (by have hs := G.source.isLt; nlinarith)
  case hsafe.right.right.right.right.isTrue.left.right =>
    rcases h with ⟨G, rfl, hfit⟩
    exact hfit.of_le (by nlinarith)
  case hsafe.right.right.right.right.isTrue.right.left =>
    rcases h with ⟨G, rfl, hfit⟩
    exact initial_insert_safe G hfit
  case hsafe.right.right.right.right.isTrue.right.right =>
    rcases h with ⟨G, rfl, hfit⟩
    have hn : (Memory.State.init G.encode).mem 1 = G.n := rfl
    have hs : (Memory.State.init G.encode).mem 2 = G.source.val := rfl
    have hm : (Memory.State.init G.encode).mem (G.n + 3) = G.m := by
      rw [← G.offset_n]
      exact G.init_offset (r := 0) le_rfl
    have ht : (Memory.spec 0).runClient (Memory.State.init G.encode) (Memory.allocBlockDirty G.n) =
        (⟨(Memory.State.init G.encode).frontier, G.n⟩,
          ⟨(Memory.State.init G.encode).mem, (Memory.State.init G.encode).frontier + G.n⟩,
          [.allocDirty G.n]) := rfl
    simp only [StateTransitionSpec.clientResult, StateTransitionSpec.clientState,
      BinaryHeap.Native.Initialize.allocLayout_run, hn, hs, hm, ht]
    exact initial_loop_safe G hfit

/-- One fixed native emitter realizes the original allocated binary-heap Dijkstra memory
program. The domain retains the original graph input and word-size envelope; native arithmetic,
argument delivery, initialization and control are included in its constant instruction factor. -/
theorem realizes_run : Realizes .exact (fun _ : Unit => Memory.run)
    (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := Unit))
    (fun w _ s => ∃ G : ListInstance, s = Memory.State.init G.encode ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) (fun _ _ => 0) := by
  apply word_run_realizes.congr
  intro _
  exact runWord_eq_binary _ _ _ (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun n H => BinaryHeap.Native.extractMin_observation ⟨n, H⟩)

private theorem realizes_run_return : Realizes .exact (fun _ : Unit => do Memory.run; pure 0)
    (WordEncoding.encode (α := Unit)) word
    (fun w _ s => ∃ G : ListInstance, s = Memory.State.init G.encode ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) (fun _ _ => 0) := by
  have hReturn : Realizes .exact (fun _ : Unit × Unit => pure 0)
      (appendWords (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := Unit))) word
      (fun _ _ _ => True) (fun _ _ => 0) := by realize
  apply (realizes_run.bind₀ hReturn).consequence
  · intro w d s _ _ h
    exact ⟨h, trivial⟩
  · intro _ _
    exact le_rfl

/-- One flat exact-basis program, chosen before every graph and word size, computes the
shortest-path distances. Its charged prefix, body and halt take log-linear time, and the full
final memory/frontier is exactly the state of the original memory program. -/
theorem exists_program_state :
    ∃ r C pc : ℕ, ∃ prog : Program .exact r, ∃ frontier : Fin r,
      ∀ (G : ListInstance) (w : ℕ), Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) →
        ∃ (y : Data r) (steps : ℕ), Runs w prog (State.init G.encode) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt 0 ∧
          memoryState frontier y =
            (Memory.spec w).clientState (Memory.State.init G.encode) Memory.run ∧
          steps + 1 ≤ C * (G.m + 1) * (Nat.log 2 G.n + 1) ∧
          ∀ v : Fin G.n, y.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  obtain ⟨r, C, pc, prog, frontier, _, he⟩ :=
    realizes_run_return.exists_standard_init_program_state_from_words 0
  refine ⟨r, 54 * (C + 1), pc, prog, frontier, ?_⟩
  intro G w hfit
  obtain ⟨hvalid, hdist, hcost⟩ := Memory.run_spec G hfit
  have hfront : Fits w (G.encode.length + 1) := by
    rw [G.encode_length]
    exact hfit.of_le (by nlinarith)
  have hv : (Memory.spec w).ValidHistory (Memory.State.init G.encode)
      ((Memory.spec w).clientHistory (Memory.State.init G.encode) (do Memory.run; pure 0)) := by
    rw [(Memory.spec w).clientHistory_bind Memory.run (fun _ : Unit => (pure 0 : Memory.Prog ℕ))]
    simpa only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_pure',
      List.append_nil] using hvalid
  obtain ⟨y, steps, hrun, hhalt, hstate, _, htime⟩ :=
    he w () G.encode (fun i => Fin.elim0 i) (Nat.zero_le _) hfront
      (G.inputFits_encode hfit) ⟨G, rfl, hfit⟩ hv
  have hs : (Memory.spec w).clientState (Memory.State.init G.encode)
      (do Memory.run; pure 0) =
      (Memory.spec w).clientState (Memory.State.init G.encode) Memory.run := by
    rw [StateTransitionSpec.clientState_bind]
    rfl
  have hm : memoryCost (do Memory.run; pure 0) (Memory.State.init G.encode) =
      memoryCost Memory.run (Memory.State.init G.encode) := by
    simpa only [PFunctor.FreeM.bind_eq_bind, memoryCost_pure, Nat.add_zero] using
      (memoryCost_bind Memory.run (fun _ : Unit => (pure 0 : Memory.Prog ℕ))
        (Memory.State.init G.encode))
  change memoryState frontier y = (Memory.spec w).clientState (Memory.State.init G.encode)
    (do Memory.run; pure 0) at hstate
  rw [hs] at hstate
  change steps + 1 ≤ C * (memoryCost (do Memory.run; pure 0)
    (Memory.State.init G.encode) + 0 + 1) + 1 at htime
  rw [hm] at htime
  have hr : (Memory.spec w).clientResult (inputState G.encode)
      (do Memory.run; pure 0) = 0 := by
    rw [(Memory.spec w).clientResult_bind Memory.run (fun _ : Unit => (pure 0 : Memory.Prog ℕ))]
    rfl
  rw [hr] at hhalt
  rw [← memoryCost_eq_totalCost w] at hcost
  refine ⟨y, steps, hrun, hhalt, hstate, ?_, ?_⟩
  · unfold Memory.memCost at hcost
    have hpos : 1 ≤ (G.m + 1) * (Nat.log 2 G.n + 1) := Nat.mul_pos (by omega) (by omega)
    nlinarith [Nat.mul_le_mul_left C hcost, Nat.mul_le_mul_left C hpos]
  · intro v
    have hm := congrArg (fun s : Memory.State => s.mem (G.outAddr v)) hstate
    exact hm.trans (hdist v)

end Cslib.Algorithms.Lean.Dijkstra.Native.Binary
