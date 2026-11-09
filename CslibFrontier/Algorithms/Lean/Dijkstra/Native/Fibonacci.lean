/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Fibonacci.Cost
public import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
public import CslibFrontier.Computability.WordRAM.Realization.Absorb
import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Backend
import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Initialize
import CslibFrontier.Algorithms.WordRAM.Dijkstra.ListEncode
import CslibFrontier.Tactic.Realize

/-!
# Native Fibonacci-heap Dijkstra from the existing framed memory client

The existing uniform method certificates realize the original linked source. Reached domains
come from the shared framed refinement and valid remaining Dijkstra histories. The original
amortized potential pays for memory operations; the native code separately charges arithmetic,
argument copies, loop control and initialization. Flat exports retain the original graph input
and word envelope, include their real prefix and halt, and preserve the full final memory.

## Main results

* `realizes_run`: one uniform emitter for the original allocated Fibonacci memory client.
* `exists_program_state`: its sharper halt-inclusive flat clock and exact whole-state export.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [M. L. Fredman and R. E. Tarjan, *Fibonacci heaps and their uses in improved network
  optimization algorithms*][FredmanTarjan1987]
-/

public section

namespace Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.Algorithms.WordRAM.Dijkstra (ListInstance encodeDist)

private def insertWord (e : ℕ × ℕ) (v k : ℕ) : Memory.Prog Unit :=
  link ((FibonacciHeap.layout e.1 e.2).methods 0) (FibonacciHeap.insert v k)

private def decreaseWord (e : ℕ × ℕ) (v k : ℕ) : Memory.Prog Unit :=
  link ((FibonacciHeap.layout e.1 e.2).methods 0) (FibonacciHeap.decreaseKey e.1 v k)

private theorem insert_realizes : Realizes .exact
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => insertWord d.1.1 d.1.2 d.2)
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
    (fun w d _ => Fits w (d.1.1.2 + (9 * d.1.1.1 + 5)) ∧ d.1.2 < d.1.1.1)
    (fun _ _ => 0) :=
  FibonacciHeap.Native.realizes_insert.reindex
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => ![d.1.1.1, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) ![0, 1, 2, 3]
    (by intro d i; fin_cases i <;> rfl)

private theorem decrease_realizes : Realizes .exact
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => decreaseWord d.1.1 d.1.2 d.2)
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
    (fun w d s => FibonacciHeap.Native.decreaseValid w
      ![d.1.1.1, d.1.1.2, d.1.2, d.2] s) (fun _ _ => 0) :=
  FibonacciHeap.Native.realizes_decreaseKey.reindex
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => ![d.1.1.1, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) ![0, 1, 2, 3]
    (by intro d i; fin_cases i <;> rfl)

private abbrev TargetArgs := (((ℕ × ℕ) × Block) × ℕ) × (ℕ × ℕ)
private abbrev word := WordEncoding.encode (α := ℕ)
private def targetInput := appendWords
  (appendWords (appendWords (WordEncoding.encode (α := ℕ × ℕ)) blockWords) word)
  (WordEncoding.encode (α := ℕ × ℕ))

private def targetProgram (d : TargetArgs) : Memory.Prog Unit :=
  relaxTarget (insertWord d.1.1.1) (decreaseWord d.1.1.1) d.1.1.2 d.1.2 d.2.1 d.2.2

private def targetSafe (w : ℕ) (d : TargetArgs) (s : Memory.State) : Prop :=
  ∃ (hv : d.1.2 < d.1.1.1.1) (K : ℕ), Fits w K ∧ Fits w (d.1.1.1.2 + (9 * d.1.1.1.1 + 5)) ∧
    (FibonacciHeap.layout d.1.1.1.1 d.1.1.1.2).Inv s ∧
    FibonacciHeap.Inv d.1.1.1.1 K ((FibonacciHeap.layout d.1.1.1.1 d.1.1.1.2).abs s) ∧
    (Block.mk (d.1.1.2.base) (d.1.1.2.length)).Allocated s ∧ d.1.1.2.length = d.1.1.1.1 ∧
    Disjoint (FibonacciHeap.footprint d.1.1.1.1 d.1.1.1.2)
      (Block.mk (d.1.1.2.base) (d.1.1.2.length)).footprint ∧
    Fits w (d.2.1 + d.2.2 + 1) ∧
    match Dictionary.Memory.decode (s.mem (d.1.1.2.base + d.1.2)) with
    | none => IndexedMinPQ.valid K (FibonacciHeap.abs d.1.1.1.1
        ((FibonacciHeap.layout d.1.1.1.1 d.1.1.1.2).abs s)) (.insert ⟨d.1.2, hv⟩ (d.2.1 + d.2.2))
    | some old => d.2.1 + d.2.2 < old → IndexedMinPQ.valid K
        (FibonacciHeap.abs d.1.1.1.1 ((FibonacciHeap.layout d.1.1.1.1 d.1.1.1.2).abs s))
        (.decreaseKey ⟨d.1.2, hv⟩ (d.2.1 + d.2.2))

private theorem target_realizes : Realizes .exact targetProgram targetInput
      (WordEncoding.encode (α := Unit))
      targetSafe (fun _ _ => 0) := by
  unfold targetProgram
  have hInsert := insert_realizes
  have hDecrease := decrease_realizes
  realize
  all_goals rcases h with ⟨hv, K, hK, hwindow, halloc, hI, hT, hlen, hd, hsum, hop⟩
  all_goals
    have hvT : d.1.2 < (Block.mk (d.1.1.2.base) (d.1.1.2.length)).length := by
      dsimp only
      omega
  all_goals try first
    | exact hmem.fits_of_lt_frontier (hT.lt_frontier hvT)
    | exact hsum.of_le (by omega)
    | omega
  have ha : d.1.1.2.base + d.1.2 ∈ (Block.mk (d.1.1.2.base) (d.1.1.2.length)).footprint :=
    Block.mem_footprint.mpr (Block.owns_add hvT)
  have hframe : ∀ a ∈ FibonacciHeap.footprint d.1.1.1.1 d.1.1.1.2,
      Function.update s.mem (d.1.1.2.base + d.1.2) (d.2.1 + d.2.2 + 1) a = s.mem a := by
    intro a he
    apply Function.update_of_ne
    intro h
    exact (Finset.disjoint_left.mp hd) (h ▸ he) ha
  have he := FibonacciHeap.layout_abs_congr (n := d.1.1.1.1) (base := d.1.1.1.2) (s := s)
    (s' := ⟨Function.update s.mem (d.1.1.2.base + d.1.2) (d.2.1 + d.2.2 + 1), s.frontier⟩) hframe
  have hx0 : s.mem (d.1.1.2.base + d.1.2) ≠ 0 := by assumption
  have hdecode : Dictionary.Memory.decode (s.mem (d.1.1.2.base + d.1.2)) =
      some (s.mem (d.1.1.2.base + d.1.2) - 1) := by
    cases hx : s.mem (d.1.1.2.base + d.1.2) with
    | zero => exact False.elim (hx0 hx)
    | succ x => rfl
  rw [hdecode] at hop
  obtain ⟨⟨old, hOld, hle⟩, hkey⟩ := hop hc
  refine ⟨hwindow, halloc, ⟨d.1.2, hv⟩, K, old, rfl, hK, ?_, ?_, hle, hkey⟩
  · change FibonacciHeap.Inv d.1.1.1.1 K ((FibonacciHeap.layout d.1.1.1.1 d.1.1.1.2).abs
      ⟨Function.update s.mem (d.1.1.2.base + d.1.2) (d.2.1 + d.2.2 + 1), s.frontier⟩)
    rw [he]
    exact hI
  · change FibonacciHeap.abs d.1.1.1.1 ((FibonacciHeap.layout d.1.1.1.1 d.1.1.1.2).abs
      ⟨Function.update s.mem (d.1.1.2.base + d.1.2) (d.2.1 + d.2.2 + 1), s.frontier⟩)
      ⟨d.1.2, hv⟩ = some old
    rw [he]
    exact hOld

private theorem targetSafe_of_relax_valid (G : ListInstance) {w base : ℕ} (T : Block)
    (hn : Fits w G.n) (hK : Fits w (G.n * G.maxWeight))
    (hT : Dictionary.Memory.Valid T w G.n (G.n * G.maxWeight + 1))
    (s : Memory.State)
    (hf : (framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s)
    (u v : Fin G.n) (du i c : ℕ)
    (hg : AdjacencyList.step G.adj (.edge u i) = (G.adj, (v, c)))
    (hv : (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
      ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
      ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
        ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        (relaxEdge u du i)))
    (hdu : du ≤ G.n * G.maxWeight) (hc : c ≤ G.maxWeight)
    (hfit : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)))
    (hwindow : Fits w (base + (9 * G.n + 5))) :
    targetSafe w ((((G.n, base), T), v.val), (du, c)) s := by
  have hd := hf.2.2.1
  change Disjoint (FibonacciHeap.footprint G.n base)
    (T.footprint ∪ (Memory.inputGraph G.n G.m).footprint) at hd
  refine ⟨v.isLt, G.n * G.maxWeight, hK, hwindow, hf.1.1, hf.1.2,
    hf.2.1.1, hT.length_eq, hd.mono_right Finset.subset_union_left,
    hfit.of_le (by nlinarith), ?_⟩
  exact relax_valid_queue _ u v du i c hg hv

private abbrev Env := ((ℕ × ℕ) × Block) × (ℕ × ℕ)
private def envInput := appendWords
  (appendWords (WordEncoding.encode (α := ℕ × ℕ)) blockWords)
  (WordEncoding.encode (α := ℕ × ℕ))
private abbrev RelaxArgs := Env × (ℕ × ℕ × ℕ)
private def relaxInput := appendWords envInput (WordEncoding.encode (α := ℕ × ℕ × ℕ))

private def relaxSafe (w : ℕ) (d : RelaxArgs) (s : Memory.State) : Prop :=
  ∃ (G : ListInstance) (base : ℕ) (hn : Fits w G.n)
    (hK : Fits w (G.n * G.maxWeight))
    (hT : Dictionary.Memory.Valid d.1.1.2 w G.n (G.n * G.maxWeight + 1)) (u : Fin G.n),
    d.1.1.1 = (G.n, base) ∧ d.1.2.1 = G.n ∧ d.1.2.2 = G.m ∧ d.2.1 = u.val ∧
    (framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s ∧
    d.2.2.1 ≤ G.n * G.maxWeight ∧
    Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) ∧
    Fits w (base + (9 * G.n + 5)) ∧
    (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
      ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
      ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
        ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        (relaxEdge u d.2.2.1 d.2.2.2))

private def relaxProgram (d : RelaxArgs) : Memory.Prog Unit := do
  let a ← read (3 + d.2.1)
  let t ← read (d.1.2.1 + 4 + 2 * (a + d.2.2.2))
  let c ← read (d.1.2.1 + 4 + (2 * (a + d.2.2.2) + 1))
  if t < d.1.2.1 then
    targetProgram ((d.1.1, t), (d.2.2.1, c))
  else
    let z ← pure 0
    targetProgram ((d.1.1, d.2.1), (d.2.2.1, z))

private theorem relax_realizes : Realizes .exact (fun d : RelaxArgs =>
    relaxWord
      (insertWord d.1.1.1)
      (decreaseWord d.1.1.1) d.1.1.2
      (Memory.inputGraph d.1.2.1 d.1.2.2) d.1.2.1 d.2.1 d.2.2.1 d.2.2.2)
    relaxInput (WordEncoding.encode (α := Unit)) relaxSafe (fun _ _ => 0) := by
  suffices h : Realizes .exact relaxProgram relaxInput (WordEncoding.encode (α := Unit))
      relaxSafe (fun _ _ => 0) from h.congr (fun _ => rfl)
  have hTarget := target_realizes
  unfold relaxProgram
  realize
  all_goals
    rcases d with ⟨⟨⟨e, T⟩, n, m⟩, vcur, du, i⟩
    rcases h with ⟨G, base, hnFit, hK, hT, u, he, hn, hm, hu, hf, hdu, hfit, hwindow, hv⟩
    dsimp only at he hn hm hu hT hdu hv ⊢
    subst e
    subst n
    subst m
    subst vcur
    have hA : AdjacencyList.Memory.Inv (Memory.inputGraph G.n G.m) G.adj s := hf.2.1.2.1
    have hi : i < (G.adj u).length := hv.1
    have htgt := hA.holds.target u i hi
    change s.mem (G.n + 4 + 2 * (s.mem (3 + u.val) + i)) = ((G.adj u)[i]).1.val at htgt
    have hwt := hA.holds.weight u i hi
    change s.mem (G.n + 4 + (2 * (s.mem (3 + u.val) + i) + 1)) = ((G.adj u)[i]).2 at hwt
    have hbound : s.mem (G.n + 4 + 2 * (s.mem (3 + u.val) + i)) < G.n := by
      rw [htgt]
      exact ((G.adj u)[i]).1.isLt
    first
    | have hbad : ¬s.mem (G.n + 4 + 2 * (s.mem (3 + u.val) + i)) < G.n := by assumption
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
        refine targetSafe_of_relax_valid G T hnFit hK hT s hf u ((G.adj u)[i]).1 du i
          ((G.adj u)[i]).2 (AdjacencyList.step_edge G.adj u hi) hv hdu ?_ hfit hwindow
        exact G.le_maxWeight (List.getElem_mem hi)

private abbrev ScanArgs := Env × (ℕ × ℕ)
private def scanInput := appendWords envInput (WordEncoding.encode (α := ℕ × ℕ))

private def scanSafe (w : ℕ) (d : ScanArgs) (s : Memory.State) : Prop :=
  ∃ (G : ListInstance) (base : ℕ) (hn : Fits w G.n)
    (hK : Fits w (G.n * G.maxWeight))
    (hT : Dictionary.Memory.Valid d.1.1.2 w G.n (G.n * G.maxWeight + 1)) (u : Fin G.n),
    d.1.1.1 = (G.n, base) ∧ d.1.2.1 = G.n ∧ d.1.2.2 = G.m ∧ d.2.1 = u.val ∧
    (framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s ∧
    d.2.2 ≤ G.n * G.maxWeight ∧
    Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) ∧
    Fits w (base + (9 * G.n + 5)) ∧
    (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
      ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
      ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
        ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        (scan u d.2.2))

private def scanProgram (d : ScanArgs) : Memory.Prog Unit := do
  let a ← read (3 + d.2.1)
  let b ← read (3 + (d.2.1 + 1))
  let degree ← pure (b - a)
  let _ ← boundedWhile (fun b i : ℕ => i < b) (fun x => do
    relaxProgram (d.1, d.2.1, d.2.2, x.2)
    pure (x.2 + 1)) degree degree 0
  pure ()

private theorem scan_realizes : Realizes .exact scanProgram scanInput
    (WordEncoding.encode (α := Unit)) scanSafe (fun _ _ => 0) := by
  have hRelax : Realizes .exact relaxProgram relaxInput (WordEncoding.encode (α := Unit))
      relaxSafe (fun _ _ => 0) := relax_realizes.congr (fun _ => rfl)
  unfold scanProgram
  realize
  all_goals
    rcases d with ⟨⟨⟨e, T⟩, n, m⟩, vcur, du⟩
    rcases h with ⟨G, base, hnFit, hK, hT, u, he, hn, hm, hu, hf, hdu, hfit, hwindow, hv⟩
    dsimp only at he hn hm hu hT hdu hv ⊢
    subst e
    subst n
    subst m
    subst vcur
    have hA : AdjacencyList.Memory.Inv (Memory.inputGraph G.n G.m) G.adj s := hf.2.1.2.1
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
      let M := framed hnFit hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj
      let p (i : ℕ) := relaxProgram ((((G.n, base), T), G.n, G.m), u.val, du, i)
      apply Native.scan_while_safe M.toRefinement u du (G.adj u).length p
        (fun w i s => relaxSafe w ((((G.n, base), T), G.n, G.m), u.val, du, i) s)
        (fun i => relaxWord_eq (pqMethods G.n (G.n * G.maxWeight) w base)
          (insertWord (G.n, base)) (decreaseWord (G.n, base))
          (fun v k => (FibonacciHeap.Native.link_width base w (FibonacciHeap.insert v k)).symm)
          (fun v k => (FibonacciHeap.Native.link_width base w
            (FibonacciHeap.decreaseKey G.n v k)).symm)
          T (Memory.inputGraph G.n G.m) u du i) ?_ s hf hbfit ?_ hm
      · intro i s hi hinv hvalid
        exact ⟨G, base, hnFit, hK, hT, u, rfl, rfl, rfl, rfl, hinv,
          hdu, hfit, hwindow, hvalid⟩
      · unfold scan at hv
        dsimp only [degree, StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
          PFunctor.FreeM.lift, PFunctor.FreeM.bind, Bind.bind, Pure.pure,
          PFunctor.FreeM.instBind, PFunctor.FreeM.instPure, StateTransitionSpec.stepFn,
          productStepFn, AdjacencyList.step] at hv
        change _ ∧ (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
          (M.abs s) ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
            (M.abs s) ((List.range (G.adj u).length).forM (relaxEdge u du))) at hv
        simpa only [remainingEdges, Nat.sub_zero, List.range_eq_range'] using hv.2

private def extractWord (e : ℕ × ℕ) : Memory.Prog (Option (ℕ × ℕ)) :=
  link ((FibonacciHeap.layout e.1 e.2).methods 0) (FibonacciHeap.Native.extractRaw e.1)

private theorem extract_realizes : Realizes .exact extractWord
    (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Option (ℕ × ℕ)))
    (fun w d s => FibonacciHeap.Native.extractValid w ![d.1, d.2] s) (fun _ _ => 0) :=
  FibonacciHeap.Native.realizes_extractRaw.reindex (fun d : ℕ × ℕ => ![d.1, d.2])
    (WordEncoding.encode (α := ℕ × ℕ)) ![0, 1] (by intro d i; fin_cases i <;> rfl)

private theorem extractWord_eq (n K w base : ℕ) :
    extractWord (n, base) =
      (pqMethods n K w base .extractMin).map (Option.map fun p => (p.1.val, p.2)) := by
  simp only [extractWord, pqMethods, FibonacciHeap.methods,
    FibonacciHeap.Native.link_extractRaw_eq, FibonacciHeap.Native.link_width]
  rfl

private abbrev StepArgs := Env × ℕ
private def stepInput := appendWords envInput word

private def stepSafe (w : ℕ) (d : StepArgs) (s : Memory.State) : Prop :=
  ∃ (G : ListInstance) (base : ℕ) (hn : Fits w G.n)
    (hK : Fits w (G.n * G.maxWeight))
    (hT : Dictionary.Memory.Valid d.1.1.2 w G.n (G.n * G.maxWeight + 1)),
    d.1.1.1 = (G.n, base) ∧ d.1.2.1 = G.n ∧ d.1.2.2 = G.m ∧
    (framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s ∧
    (∀ v k, ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s).1 v =
      some k → k ≤ G.n * G.maxWeight) ∧
    Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) ∧
    Fits w (base + (9 * G.n + 5)) ∧ 0 < d.2 ∧
    (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
      ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
      ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
        ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        (abstractLoopStep d.2))

private def stepProgram (d : StepArgs) : Memory.Prog ℕ := do
  match ← extractWord d.1.1.1 with
  | none => pure 0
  | some (u, du) =>
    if u < d.1.2.1 then
      scanProgram (d.1, u, du)
      pure (d.2 - 1)
    else pure 0

private theorem step_realizes : Realizes .exact stepProgram stepInput word stepSafe
    (fun _ _ => 0) := by
  have hExtract := extract_realizes
  have hScan := scan_realizes
  unfold stepProgram
  realize
  all_goals
    rcases d with ⟨⟨⟨e, T⟩, n, m⟩, a⟩
    rcases h with ⟨G, base, hnFit, hK, hT, he, hn, hm, hf, hb, hfit, hwindow, ha, hv⟩
    dsimp only at he hn hm hT hb ha hv ⊢
    subst e
    subst n
    subst m
    first
    | exact ⟨hwindow, hf.1.1, G.n * G.maxWeight, hK, hf.1.2⟩
    | omega
    | let M := framed hnFit hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj
      unfold abstractLoopStep at hv
      rw [StateTransitionSpec.clientHistory_bind, StateTransitionSpec.validHistory_append,
        StateTransitionSpec.run_runClient] at hv
      obtain ⟨_, hres, hstate, hinv⟩ := M.simulates_client (queue .extractMin) hf hv.1
      have hql : link M.methods (queue (n := G.n) (K := G.n * G.maxWeight)
          (V := G.n * G.maxWeight + 1) .extractMin) =
          pqMethods G.n (G.n * G.maxWeight) w base .extractMin :=
        PFunctor.FreeM.liftM_lift (P :=
          (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).signature)
          M.methods (.inl .extractMin)
      rw [hql] at hres hstate hinv
      simp only [pqMethods, FibonacciHeap.methods,
        FibonacciHeap.Native.link_width] at hres hstate hinv
      rw [clientResult_width] at hres
      rw [clientState_width] at hstate hinv
      have hrmap : (Memory.spec 0).clientResult s (extractWord (G.n, base)) =
          Option.map (fun p => (p.1.val, p.2))
            ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientResult
              (M.abs s) (queue .extractMin)) := by
        rw [extractWord_eq G.n (G.n * G.maxWeight) 0 base,
          ← PFunctor.FreeM.bind_pure_comp, StateTransitionSpec.clientResult,
          StateTransitionSpec.runClient_bind]
        simp only [Function.comp_apply, StateTransitionSpec.runClient_pure']
        exact congrArg (Option.map fun p : Fin G.n × ℕ => (p.1.val, p.2)) hres
      have hsmap : (Memory.spec 0).clientState s (extractWord (G.n, base)) =
          (Memory.spec 0).clientState s
            (link ((FibonacciHeap.layout G.n base).methods 0) (FibonacciHeap.extractMin G.n)) := by
        rw [extractWord_eq G.n (G.n * G.maxWeight) 0 base,
          ← PFunctor.FreeM.bind_pure_comp, StateTransitionSpec.clientState,
          StateTransitionSpec.runClient_bind]
        rfl
      rw [hsmap, hrmap]
      cases hq : (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientResult
          (M.abs s) (queue .extractMin) with
      | none =>
        simp only [hrmap, hq, Option.map_none, optionWordsWith_none, Fin.cases_zero,
          not_true] at *
      | some uk =>
        rcases uk with ⟨u, du⟩
        simp only [Option.map_some, optionWordsWith_some]
        have hfind : IndexedMinPQ.findMin (M.abs s).1 = some (u, du) := by
          have he : (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientResult
              (M.abs s) (queue .extractMin) = IndexedMinPQ.findMin (M.abs s).1 := by
            change (IndexedMinPQ.step (M.abs s).1 .extractMin).2 = _
            cases h : IndexedMinPQ.findMin (M.abs s).1 <;> simp only [IndexedMinPQ.step, h]
          rw [he] at hq
          exact hq
        refine ⟨G, base, hnFit, hK, hT, u, rfl, rfl, rfl, rfl, hinv,
          hb u du (IndexedMinPQ.findMin_eq_some_state hfind), hfit, hwindow, ?_⟩
        change (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
          (M.abs ((Memory.spec 0).clientState s
            (link ((FibonacciHeap.layout G.n base).methods 0) (FibonacciHeap.extractMin G.n))))
          ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
            (M.abs ((Memory.spec 0).clientState s
              (link ((FibonacciHeap.layout G.n base).methods 0) (FibonacciHeap.extractMin G.n))))
            (scan u du))
        rw [hstate]
        have htail := hv.2
        rw [hq] at htail
        dsimp only at htail
        rw [StateTransitionSpec.clientHistory_bind, StateTransitionSpec.validHistory_append,
          StateTransitionSpec.run_runClient] at htail
        exact htail.1

private def loopSafe (w : ℕ) (d : StepArgs) (s : Memory.State) : Prop :=
  ∃ (G : ListInstance) (base : ℕ) (hn : Fits w G.n)
    (hK : Fits w (G.n * G.maxWeight))
    (hT : Dictionary.Memory.Valid d.1.1.2 w G.n (G.n * G.maxWeight + 1)),
    d.1.1.1 = (G.n, base) ∧ d.1.2.1 = G.n ∧ d.1.2.2 = G.m ∧
    (framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s ∧
    (∀ v k, ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s).1 v =
      some k → k ≤ G.n * G.maxWeight) ∧
    Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) ∧
    Fits w (base + (9 * G.n + 5)) ∧
    (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
      ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
      ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
        ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        (loop d.2))

private def extendedBody (x : (StepArgs × ℕ) × ℕ) : Memory.Prog ℕ :=
  stepProgram (x.1.1.1, x.2)

private theorem extendedBody_realizes : Realizes .exact extendedBody
    (appendWords (appendWords stepInput word) word) word
    (fun w x s => stepSafe w (x.1.1.1, x.2) s) (fun _ _ => 0) := by
  apply step_realizes.reindex (fun x => (x.1.1.1, x.2))
    (appendWords (appendWords stepInput word) word) ![0, 1, 2, 3, 4, 5, 8]
  intro e i
  fin_cases i <;> rfl

private theorem nativeWhile_realizes : Realizes .exact (fun x : (StepArgs × ℕ) × ℕ =>
    boundedWhile (fun e a => e.2 < a) extendedBody x.1 x.1.1.2 x.2)
    (appendWords (appendWords stepInput word) word) word
    (fun w x s => whileSafe (fun e a => e.2 < a) extendedBody
      (fun w x s => stepSafe w (x.1.1.1, x.2) s) w x.1 x.1.1.2 x.2 s)
    (fun _ _ => 0) := by
  apply Realizes.while₀ (appendWords stepInput word) word (.lt 7 8)
    (fun x => x.1.1.2) extendedBody_realizes
  intro x s
  exact one_le_memoryCost_liftBind _ _ _

private theorem nativeWhile_valid_realizes : Realizes .exact
    (fun x : (StepArgs × ℕ) × ℕ =>
      boundedWhile (fun e a => e.2 < a) extendedBody x.1 x.1.1.2 x.2)
    (appendWords (appendWords stepInput word) word) word
    (fun w x s => (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (boundedWhile (fun e a => e.2 < a) extendedBody x.1 x.1.1.2 x.2)) →
      whileSafe (fun e a => e.2 < a) extendedBody
        (fun w x s => stepSafe w (x.1.1.1, x.2) s) w x.1 x.1.1.2 x.2 s)
    (fun _ _ => 0) :=
  nativeWhile_realizes.consequence_valid (fun _ _ _ _ _ hv h => h hv)

private def loopProgram (d : StepArgs) : Memory.Prog Unit := do
  let z ← pure 0
  let a ← pure d.2
  let _ ← boundedWhile (fun e a => e.2 < a) extendedBody (d, z) d.2 a
  pure ()

private theorem loop_realizes : Realizes .exact loopProgram stepInput
    (WordEncoding.encode (α := Unit)) loopSafe (fun _ _ => 0) := by
  have hW := nativeWhile_valid_realizes
  unfold loopProgram
  realize
  rcases d with ⟨⟨⟨e, T⟩, n, m⟩, a₀⟩
  rcases h with ⟨G, base, hnFit, hK, hT, he, hn, hm, hf, hb, hfit, hwindow, hv⟩
  dsimp only at he hn hm hT hb hv ⊢
  subst e
  subst n
  subst m
  let M := framed hnFit hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj
  let e₀ : StepArgs := ((((G.n, base), T), G.n, G.m), a₀)
  have heq (a : ℕ) : extendedBody ((e₀, 0), a) = link M.methods (abstractLoopStep a) := by
    change loopStepWord (extractWord (G.n, base)) (insertWord (G.n, base))
      (decreaseWord (G.n, base)) T (Memory.inputGraph G.n G.m) G.n ((), a) = _
    exact (loopStepWord_eq_of_erasure (pqMethods G.n (G.n * G.maxWeight) w base)
      _ _ _
      (fun v k => (FibonacciHeap.Native.link_width base w (FibonacciHeap.insert v k)).symm)
      (fun v k => (FibonacciHeap.Native.link_width base w
        (FibonacciHeap.decreaseKey G.n v k)).symm)
      (extractWord_eq G.n (G.n * G.maxWeight) w base) T (Memory.inputGraph G.n G.m)
      ((), a)).trans (loopStep_eq_link M.methods a)
  intro hm
  apply loop_while_safe M.toRefinement (e₀, 0) (fun e a => e.2 < a) extendedBody
    (fun w x s => stepSafe w (x.1.1.1, x.2) s) (fun _ => Iff.rfl) heq ?_ ?_
    a₀ s hf hb hv hm
  · intro a s
    exact loopStepWord_result_le (extractWord (G.n, base)) (insertWord (G.n, base))
      (decreaseWord (G.n, base)) T (Memory.inputGraph G.n G.m) G.n ((), a) s
  · intro a s ha hinv hkeys hvalid
    exact ⟨G, base, hnFit, hK, hT, rfl, rfl, rfl, hinv, hkeys,
      hfit, hwindow, ha, hvalid⟩

private theorem loopProgram_eq (d : StepArgs) :
    loopProgram d = loopWord (extractWord d.1.1.1) (insertWord d.1.1.1)
      (decreaseWord d.1.1.1) d.1.1.2 (Memory.inputGraph d.1.2.1 d.1.2.2) d.1.2.1 d.2 := by
  simp only [loopProgram, pure_bind]
  unfold loopWord
  refine congrArg (fun p : Memory.Prog ℕ => p >>= fun _ => (pure () : Memory.Prog Unit)) ?_
  exact boundedWhile_congr (fun e a => e.2 < a) (fun (_ : Unit) a => a ≠ 0)
    (body := extendedBody)
    (body' := loopStepWord (extractWord d.1.1.1) (insertWord d.1.1.1)
      (decreaseWord d.1.1.1) d.1.1.2 (Memory.inputGraph d.1.2.1 d.1.2.2) d.1.2.1)
    (d := (d, 0)) (d' := ()) (fun a => by omega) (fun a => rfl) d.2 d.2

private theorem initial_loop_safe (G : ListInstance) {w : ℕ}
    (hfit : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    let f := (Memory.State.init G.encode).frontier
    loopSafe w (((((G.n, f + G.n), ⟨f, G.n⟩), G.n, G.m), G.n))
      ((Memory.spec 0).clientState
        ⟨Function.update (Memory.State.init G.encode).mem (f + G.source.val) 1,
          f + G.n + (9 * G.n + 5)⟩
        (insertWord (G.n, f + G.n) G.source.val 0)) := by
  let f := (Memory.State.init G.encode).frontier
  let T : Block := ⟨f, G.n⟩
  let base := f + G.n
  have hn : Fits w G.n := hfit.of_le (by nlinarith)
  have hK : Fits w (G.n * G.maxWeight) := hfit.of_le (by nlinarith)
  have hT : Dictionary.Memory.Valid T w G.n (G.n * G.maxWeight + 1) :=
    ⟨rfl, hfit.of_le (by nlinarith)⟩
  have hf : f = G.n + 2 * G.m + 4 := by
    simp only [f, Memory.State.init, G.encode_length]
  have hwindow : Fits w (base + (9 * G.n + 5)) := hfit.of_le (by
    dsimp only [base]
    rw [hf]
    nlinarith)
  let M := framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj
  let s₀ : Memory.State := ⟨(Memory.State.init G.encode).mem, base + (9 * G.n + 5)⟩
  obtain ⟨hi, habs⟩ := inv_input G hn hK hT ⟨rfl⟩ hwindow
  let p : (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).Client Unit := do
    setDist G.source 0
    queue (.insert G.source 0)
  have hloop := Native.initial_loop_safe G le_rfl (by omega) M.toRefinement s₀ hi habs
  have hpeq : link M.methods p = (do
      write (f + G.source.val) 1
      insertWord (G.n, base) G.source.val 0) := by
    unfold p link
    rw [PFunctor.FreeM.liftM_bind]
    have hset : (setDist (K := G.n * G.maxWeight) (V := G.n * G.maxWeight + 1)
        G.source 0).liftM M.methods = write (f + G.source.val) 1 :=
      PFunctor.FreeM.liftM_lift (P :=
        (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).signature)
        M.methods (.inr (.inl (.insert G.source 0)))
    rw [hset]
    congr 1
    funext _
    exact (PFunctor.FreeM.liftM_lift (P :=
      (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).signature)
      M.methods (.inl (.insert G.source 0))).trans
        (FibonacciHeap.Native.link_width base w (FibonacciHeap.insert G.source.val 0))
  have hs : (Memory.spec w).clientState s₀ (link M.methods p) =
      (Memory.spec 0).clientState
        ⟨Function.update (Memory.State.init G.encode).mem (f + G.source.val) 1,
          base + (9 * G.n + 5)⟩ (insertWord (G.n, base) G.source.val 0) := by
    rw [hpeq, StateTransitionSpec.clientState_bind]
    exact clientState_width _ _ _
  change M.inv ((Memory.spec w).clientState s₀ (link M.methods p)) ∧
    (∀ v k, (M.abs ((Memory.spec w).clientState s₀ (link M.methods p))).1 v = some k →
      k ≤ G.n * G.maxWeight) ∧
    (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
      (M.abs ((Memory.spec w).clientState s₀ (link M.methods p)))
      ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
        (M.abs ((Memory.spec w).clientState s₀ (link M.methods p))) (loop G.n)) at hloop
  rw [hs] at hloop
  exact ⟨G, base, hn, hK, hT, rfl, rfl, rfl, hloop.1, hloop.2.1,
    hfit, hwindow, hloop.2.2⟩

private def allocProgram (n : ℕ) : Memory.Prog (ℕ × ℕ) := do
  let base ← Memory.allocDirty (9 * n + 5)
  pure (n, base)

private theorem alloc_realizes : Realizes .exact allocProgram word
    (WordEncoding.encode (α := ℕ × ℕ))
    (fun w n s => Fits w (s.frontier + (9 * n + 5))) (fun _ _ => 0) := by
  have hAlloc := FibonacciHeap.Native.Initialize.realizes_reserve
  unfold allocProgram
  realize
  exact h

private theorem allocProgram_run (n : ℕ) (s : Memory.State) :
    (Memory.spec 0).runClient s (allocProgram n) =
      ((n, s.frontier), ⟨s.mem, s.frontier + (9 * n + 5)⟩,
        [.allocDirty (9 * n + 5)]) := rfl

private def runProgram : Memory.Prog Unit := do
  let n ← read 1
  let src ← read 2
  let m ← read (n + 3)
  let T ← allocBlockDirty n
  let e ← allocProgram n
  if src < n then
    let z ← pure 0
    write (T.base + src) (z + 1)
    insertWord e src z
    loopProgram (((e, T), n, m), n)
  else pure ()

private theorem runProgram_eq : runProgram = run := by
  rw [← runWord_eq]
  unfold runProgram runWord
  congr 1
  funext n
  congr 1
  funext src
  congr 1
  funext m
  congr 1
  funext T
  congr 1
  funext e
  by_cases hs : src < n
  · simp only [ite_eq_left hs, pure_bind]
    rw [loopProgram_eq]
    rfl
  · simp only [ite_eq_right hs]

/-- One native emitter realizes the original Fibonacci-heap Dijkstra memory client. Its
domain retains the unchanged graph encoding and word envelope. Arithmetic, argument delivery,
dirty allocation and early-exit loop control are included in the uniform instruction factor. -/
theorem realizes_run : Realizes .exact (fun _ : Unit => run)
    (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := Unit))
    (fun w _ s => ∃ G : ListInstance, s = Memory.State.init G.encode ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) (fun _ _ => 0) := by
  suffices h : Realizes .exact (fun _ : Unit => runProgram)
      (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := Unit))
      (fun w _ s => ∃ G : ListInstance, s = Memory.State.init G.encode ∧
        Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) (fun _ _ => 0) from
    h.congr (fun _ => runProgram_eq)
  have hAlloc := alloc_realizes
  have hInsert := insert_realizes
  have hLoop := loop_realizes
  unfold runProgram
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
    change Fits w ((Memory.State.init G.encode).frontier + G.n + (9 * G.n + 5))
    have hf : (Memory.State.init G.encode).frontier = G.n + 2 * G.m + 4 := by
      simp only [Memory.State.init, G.encode_length]
    rw [hf]
    exact hfit.of_le (by nlinarith)
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
  case hsafe.right.right.right.right.isTrue.right.left.left =>
    rcases h with ⟨G, rfl, hfit⟩
    simp only [StateTransitionSpec.clientResult, allocProgram_run]
    change Fits w ((Memory.State.init G.encode).frontier + G.n + (9 * G.n + 5))
    have hf : (Memory.State.init G.encode).frontier = G.n + 2 * G.m + 4 := by
      simp only [Memory.State.init, G.encode_length]
    rw [hf]
    exact hfit.of_le (by nlinarith)
  case hsafe.right.right.right.right.isTrue.right.left.right =>
    rcases h with ⟨G, rfl, hfit⟩
    simp only [StateTransitionSpec.clientResult, allocProgram_run]
    change G.source.val < G.n
    exact G.source.isLt
  case hsafe.right.right.right.right.isTrue.right.right =>
    rcases h with ⟨G, rfl, hfit⟩
    have hn : (Memory.State.init G.encode).mem 1 = G.n := rfl
    have hs : (Memory.State.init G.encode).mem 2 = G.source.val := rfl
    have hm : (Memory.State.init G.encode).mem (G.n + 3) = G.m := by
      rw [← G.offset_n]
      exact G.init_offset (r := 0) le_rfl
    have ht : (Memory.spec 0).runClient (Memory.State.init G.encode)
        (Memory.allocBlockDirty G.n) =
        (⟨(Memory.State.init G.encode).frontier, G.n⟩,
          ⟨(Memory.State.init G.encode).mem, (Memory.State.init G.encode).frontier + G.n⟩,
          [.allocDirty G.n]) := rfl
    simp only [StateTransitionSpec.clientResult, StateTransitionSpec.clientState,
      allocProgram_run, hn, hs, hm, ht]
    exact initial_loop_safe G hfit

private theorem realizes_run_return : Realizes .exact (fun _ : Unit => do run; pure 0)
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

/-- One flat exact-basis program, chosen before all graphs and widths, computes every distance
within the sharper reachable-vertex Fibonacci bound. Its actual prefix, memory client and halt
are charged, and its entire final memory/frontier is the original memory client's final state.
As in the statement specification, placing the raw graph words in `Data.init` is uncharged. -/
theorem exists_program_state :
    ∃ r C pc : ℕ, ∃ prog : Program .exact r, ∃ frontier : Fin r,
      ∀ (G : ListInstance) (w : ℕ), Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) →
        ∃ (y : Data r) (steps : ℕ), Runs w prog (State.init G.encode) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt 0 ∧
          memoryState frontier y =
            (Memory.spec w).clientState (Memory.State.init G.encode) run ∧
          steps + 1 ≤ C * (G.m + min G.n (G.m + 1) * (Nat.log 2 G.n + 1)) ∧
          ∀ v : Fin G.n, y.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  obtain ⟨r, C, pc, prog, frontier, _, he⟩ :=
    realizes_run_return.exists_standard_init_program_state_from_words 0
  refine ⟨r, 402 * (C + 1), pc, prog, frontier, ?_⟩
  intro G w hfit
  obtain ⟨hvalid, hdist, hcost⟩ := run_spec G hfit
  have hfront : Fits w (G.encode.length + 1) := by
    rw [G.encode_length]
    exact hfit.of_le (by nlinarith)
  have hv : (Memory.spec w).ValidHistory (Memory.State.init G.encode)
      ((Memory.spec w).clientHistory (Memory.State.init G.encode) (do run; pure 0)) := by
    rw [(Memory.spec w).clientHistory_bind run (fun _ : Unit => (pure 0 : Memory.Prog ℕ))]
    simpa only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_pure',
      List.append_nil] using hvalid
  obtain ⟨y, steps, hrun, hhalt, hstate, _, htime⟩ :=
    he w () G.encode (fun i => Fin.elim0 i) (Nat.zero_le _) hfront
      (G.inputFits_encode hfit) ⟨G, rfl, hfit⟩ hv
  have hs : (Memory.spec w).clientState (Memory.State.init G.encode) (do run; pure 0) =
      (Memory.spec w).clientState (Memory.State.init G.encode) run := by
    rw [StateTransitionSpec.clientState_bind]
    rfl
  have hm : memoryCost (do run; pure 0) (Memory.State.init G.encode) =
      memoryCost run (Memory.State.init G.encode) := by
    simpa only [PFunctor.FreeM.bind_eq_bind, memoryCost_pure, Nat.add_zero] using
      (memoryCost_bind run (fun _ : Unit => (pure 0 : Memory.Prog ℕ))
        (Memory.State.init G.encode))
  change memoryState frontier y = (Memory.spec w).clientState (Memory.State.init G.encode)
    (do run; pure 0) at hstate
  rw [hs] at hstate
  change steps + 1 ≤ C * (memoryCost (do run; pure 0)
    (Memory.State.init G.encode) + 0 + 1) + 1 at htime
  rw [hm] at htime
  have hr : (Memory.spec w).clientResult (inputState G.encode) (do run; pure 0) = 0 := by
    rw [(Memory.spec w).clientResult_bind run (fun _ : Unit => (pure 0 : Memory.Prog ℕ))]
    rfl
  rw [hr] at hhalt
  rw [← memoryCost_eq_totalCost w] at hcost
  refine ⟨y, steps, hrun, hhalt, hstate, ?_, ?_⟩
  · have hn : 1 ≤ G.n := by have := G.source.isLt; omega
    have hmin : 1 ≤ min G.n (G.m + 1) := le_min hn (by omega)
    have hpos : 1 ≤ G.m + min G.n (G.m + 1) * (Nat.log 2 G.n + 1) := by
      have := Nat.mul_le_mul hmin (show 1 ≤ Nat.log 2 G.n + 1 by omega)
      omega
    nlinarith [Nat.mul_le_mul_left C hcost, Nat.mul_le_mul_left C hpos]
  · intro v
    have hm := congrArg (fun s : Memory.State => s.mem (G.outAddr v)) hstate
    exact hm.trans (hdist v)

end Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci
