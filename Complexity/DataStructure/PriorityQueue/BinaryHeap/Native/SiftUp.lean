/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.While
public import Complexity.Computability.WordRAM.Realization.Reindex
public import Complexity.Computability.WordRAM.Realization.Witness
public import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Encoding
import Complexity.Tactic.Realize

/-!
# Native realization of the memory heap's sift-up

The source is the existing memory-oracle sift-up, including its four reads and four-write swap.
A finite while view uses an input logarithmic cutoff only to prove termination; the native loop
exits on its actual index guard. This primitive supports the binary-heap migration; it does not
by itself supply the complete heap interface or its initialization contract. Bounds count
unit-cost `.exact` word-RAM instructions, with fitting words and the explicit installed-argument
ABI. They are not bit-operation bounds.

## Main results

* `finish_loop_eq`: the finite while view is the original free-monad program, not only an
  equal-result implementation. Its complete operation history and memory charge are preserved.
* `realizes_siftUp`: shared compiler and while rules supply one uniform native realization.
* `exec_siftUp`: native instruction time is logarithmic, with the source's order repair,
  exact whole-memory state and caller-register frame.

The heap source and its invariant proofs are reused from `BinaryHeap.Memory`; no heap algorithm
or machine semantics is redefined here.
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.SiftUp

open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.PriorityQueue.BinaryHeap

open Cslib.DataStructure.PriorityQueue

/-- Four original reads, followed by the original swap or a stop index. The nested comparisons
are the existing key-first, handle-tie priority relation spelled as native scalar conditions. -/
def step (d : (HeapLayout × Unit) × ℕ) : Memory.Prog ℕ := do
  let L := d.1.1.2
  let k := d.2
  let vk ← L.heap.get k
  let kk ← L.key.get vk
  let vp ← L.heap.get (k / 2)
  let kp ← L.key.get vp
  if kk < kp then do
    PriorityQueue.BinaryHeap.Memory.swap L k (k / 2) vk vp
    pure (k / 2)
  else if kk = kp then
    if vk < vp then do
      PriorityQueue.BinaryHeap.Memory.swap L k (k / 2) vk vp
      pure (k / 2)
    else pure 1
  else pure 1

/-- The scalar branch spelling changes neither reads nor writes. -/
theorem step_eq (d : (HeapLayout × Unit) × ℕ) :
    step d = (do
      let L := d.1.1.2
      let k := d.2
      let vk ← L.heap.get k
      let kk ← L.key.get vk
      let vp ← L.heap.get (k / 2)
      let kp ← L.key.get vp
      if PriorityQueue.IndexedMinPQ.RawPrioLT (vk, kk) (vp, kp) then do
        PriorityQueue.BinaryHeap.Memory.swap L k (k / 2) vk vp
        pure (k / 2)
      else pure 1) := by
  unfold step
  dsimp only
  congr 1
  funext vk
  congr 1
  funext kk
  congr 1
  funext vp
  congr 1
  funext kp
  by_cases hkey : kk < kp
  · simp [PriorityQueue.IndexedMinPQ.RawPrioLT, hkey]
  · by_cases heq : kk = kp <;> by_cases hv : vk < vp <;>
      simp [PriorityQueue.IndexedMinPQ.RawPrioLT, hkey, heq, hv]

/-- The loop state is a one-based position; returning 1 terminates without another read. -/
def guard (_ : HeapLayout × Unit) (k : ℕ) : Prop := 2 ≤ k

instance (d : HeapLayout × Unit) (k : ℕ) : Decidable (guard d k) :=
  inferInstanceAs (Decidable (2 ≤ k))

/-- The while view preserves the entire existing `siftUp` free-monad program. -/
theorem finish_loop_eq (d : HeapLayout × Unit) (fuel k : ℕ) (hf : Nat.log 2 k ≤ fuel) :
    (do
      let _ ← boundedWhile guard step d fuel k
      pure ()) = PriorityQueue.BinaryHeap.Memory.siftUp d.1.2 k := by
  induction fuel generalizing k with
  | zero =>
    have hk : ¬2 ≤ k := by
      intro hk
      have := Nat.log_of_one_lt_of_le one_lt_two hk
      omega
    rw [PriorityQueue.BinaryHeap.Memory.siftUp, ite_eq_right hk]
    rfl
  | succ fuel ih =>
    rw [PriorityQueue.BinaryHeap.Memory.siftUp]
    by_cases hk : 2 ≤ k
    · have hlog := Nat.log_of_one_lt_of_le one_lt_two hk
      simp only [boundedWhile, guard, hk, ↓reduceIte, step_eq, bind_assoc]
      congr 1
      funext vk
      congr 1
      funext kk
      congr 1
      funext vp
      congr 1
      funext kp
      split
      · simp only [bind_assoc, pure_bind]
        congr 1
        funext _
        exact ih (k / 2) (by omega)
      · simp only [pure_bind, boundedWhile_of_not guard step d fuel 1 (by change ¬(2 ≤ 1); omega)]
    · simp [boundedWhile, guard, hk]

/-- A certified constant-one register. The preparation rule below emits this value; it is
not a preinstalled or free host argument to the native loop. -/
def oneWords : Unit ↪ (Fin 1 → ℕ) where
  toFun _ := fun _ => 1
  inj' := by intro a b _; cases a; cases b; rfl

/-- The existing heap-shape invariant is sufficient for each sift step. Order repair remains
in the source's `siftUp_triple`, rather than being reproved for a native implementation. -/
def Shape (w : ℕ) (d : HeapLayout × Unit) (k : ℕ) (s : Memory.State) : Prop :=
  Fits w d.1.1 ∧ d.1.2.arrays.Allocated s ∧
    ∃ S, 1 ≤ k ∧ k ≤ S ∧ HeapShape d.1.1 d.1.2.base S s.mem

/-- One real step preserves heap shape and drops the logarithmic rank. Its eight-unit bound
uses the original four-read/four-write source trace, including the no-swap early exit. -/
theorem step_triple {w : ℕ} {d : HeapLayout × Unit} {k : ℕ} {s : Memory.State}
    (hi : Shape w d k s) (hk : 2 ≤ k) :
    Triple w s (step (d, k)) 8
      (fun a s' => Shape w d a s' ∧ Nat.log 2 a < Nat.log 2 k) := by
  obtain ⟨hn, hA, S, hk1, hkS, hshape⟩ := hi
  have hSn := hshape.size_le
  have hvk := hshape.vertex_lt k hk1 hkS
  have hvp := hshape.vertex_lt (k / 2) (by omega) (by omega)
  have hlog := Nat.log_of_one_lt_of_le one_lt_two hk
  rw [step_eq]
  dsimp only
  refine Triple.read_bind (PriorityQueue.BinaryHeap.Memory.heap_lt hA (by omega)) <|
    Triple.read_bind (PriorityQueue.BinaryHeap.Memory.key_lt hA hvk) <|
    Triple.read_bind (PriorityQueue.BinaryHeap.Memory.heap_lt hA (by omega)) <|
    Triple.read_bind (PriorityQueue.BinaryHeap.Memory.key_lt hA hvp) ?_
  split
  · obtain ⟨hshape', -, -, -, -, -⟩ :=
      hshape.swap (a := k) (b := k / 2) hk1 hkS (by omega) (by omega) (by omega)
    refine PriorityQueue.BinaryHeap.Memory.swap_bind hn hA (by omega) (by omega) hvk hvp <|
      Triple.pure ?_
    exact ⟨⟨hn, hA, S, by omega, by omega, hshape'⟩, by omega⟩
  · exact Triple.pure ⟨⟨hn, hA, S, by omega, by omega, hshape⟩, by simp; omega⟩

/-- Eight source-memory units and one continuing-control unit per logarithmic rank level.
Unused cutoff steps are not charged as iterations; exit potential is retained. -/
theorem loop_currency_le {w : ℕ} {d : HeapLayout × Unit} {k fuel : ℕ} {s : Memory.State}
    (hi : Shape w d k s)
    (hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (boundedWhile guard step d fuel k))) :
    memoryCost (boundedWhile guard step d fuel k) s +
        whileWork guard step (fun _ _ => 0) d fuel k s +
        9 * Nat.log 2 ((Memory.spec 0).clientResult s
          (boundedWhile guard step d fuel k)) ≤ 9 * Nat.log 2 k := by
  refine while_charge_le_potential guard step (fun _ _ => 0) w d (Shape w d)
    (fun a _ => 9 * Nat.log 2 a) (fun a s hi hg _ => ?_) hi hv
  obtain ⟨_, _, hpost⟩ := triple_iff.mp (step_triple hi hg)
  rw [clientResult_width w, clientState_width w] at hpost
  have hc' : memoryCost (step (d, a)) s ≤ 8 := by
    rw [step_eq]
    simp only [memoryCost, StateTransitionSpec.clientHistory,
      StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.totalCost_cons,
      StateTransitionSpec.stepFn, Memory.step, Memory.charge]
    split_ifs with hlt <;>
      simp only [hlt, ↓reduceIte, PriorityQueue.BinaryHeap.Memory.swap,
        ← PFunctor.FreeM.bind_eq_bind, StateTransitionSpec.runClient_bind,
        StateTransitionSpec.runClient_lift, StateTransitionSpec.runClient_pure',
        StateTransitionSpec.totalCost, StateTransitionSpec.stepFn, Memory.step, Memory.charge,
        List.cons_append, List.nil_append, List.append_nil, Nat.add_zero] <;> omega
  exact ⟨hpost.1, by omega⟩

/-- One fixed compiler-generated step body before all runtime layouts, widths and indices.
Local straight-line computation is absorbed into the uniform realization factor. -/
theorem realizes_step :
    Realizes .exact step
      (appendWords (appendWords layoutWords oneWords)
        (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding)
      (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
      (fun w (d, k) s => 2 ≤ k ∧ Shape w d k s) (fun _ _ => 0) := by
  realize
  all_goals
    rcases h with ⟨hk, hn, hA, S, hk1, hkS, hshape⟩
    have hSn := hshape.size_le
    have hvk := hshape.vertex_lt d.2 hk1 hkS
    have hvp := hshape.vertex_lt (d.2 / 2) (by omega) (by omega)
    first
    | omega
    | exact hn.of_le (by omega)
    | exact hmem.fits_of_lt_frontier (PriorityQueue.BinaryHeap.Memory.heap_lt hA (by omega))
    | exact hmem.fits_of_lt_frontier (PriorityQueue.BinaryHeap.Memory.key_lt hA hvk)
    | exact hmem.fits_of_lt_frontier (PriorityQueue.BinaryHeap.Memory.key_lt hA hvp)
    | exact hmem.fits_of_lt_frontier (PriorityQueue.BinaryHeap.Memory.pos_lt hA hvk)
    | exact hmem.fits_of_lt_frontier (PriorityQueue.BinaryHeap.Memory.pos_lt hA hvp)

/-- The actual index guard selects a native early exit; the logarithmic cutoff is proof data.
No register contains a fuel counter or a computed logarithm. -/
theorem realizes_loop :
    Realizes .exact
      (fun (d, k) => boundedWhile guard step d (Nat.log 2 k) k)
      (appendWords (appendWords layoutWords oneWords)
        (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding)
      (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
      (fun w (d, k) s => Shape w d k s)
      (fun (d, k) s => whileWork guard step (fun _ _ => 0) d (Nat.log 2 k) k s) := by
  have h := Realizes.whileMeasure (appendWords layoutWords oneWords)
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding (.lt 4 5)
    (fun (_, k) => Nat.log 2 k) realizes_step (fun w d k s => Shape w d k s)
    (fun _ k _ => Nat.log 2 k)
    (fun _ _ k _ _ hz => by
      change ¬(1 < k)
      intro hk
      have := Nat.log_of_one_lt_of_le one_lt_two hk
      omega)
    (fun w d k s hi hg _ => by
      change 1 < k at hg
      obtain ⟨_, _, hp⟩ := triple_iff.mp (step_triple hi hg)
      rw [clientResult_width w, clientState_width w] at hp
      exact ⟨⟨hg, hi⟩, hp⟩)
  exact h.consequence (fun _ _ _ _ _ hi => ⟨hi, le_rfl⟩) (fun _ _ => le_rfl)

/-- Actual reached loop controls, plus two binds. Constant preparation and the Unit return are
certified native glue, absorbed into the same fixed exchange factor. -/
def localWork (d : HeapLayout × ℕ) (s : Memory.State) : ℕ :=
  whileWork guard step (fun _ _ => 0) (d.1, ()) (Nat.log 2 d.2) d.2 s + 2

/-- Realize the original sift-up, with one emitter before all runtime layouts, indices, memory
contents and widths. Constant-one preparation and loop/finish composition use shared rules. -/
private theorem realizes_siftUp_graded :
    Realizes .exact (fun d : HeapLayout × ℕ => PriorityQueue.BinaryHeap.Memory.siftUp d.1.2 d.2)
      indexWords (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
      (fun w d s => Shape w (d.1, ()) d.2 s) localWork := by
  have hprepare : Realizes .exact (fun _ : HeapLayout × ℕ => pure ())
      indexWords oneWords (fun w d s => Shape w (d.1, ()) d.2 s) (fun _ _ => 0) := by
    realize
    obtain ⟨hn, _, S, hk, hkS, hshape⟩ := h
    exact hn.of_le (hk.trans (hkS.trans hshape.size_le))
  have hloop := realizes_loop.reindex
    (fun e : (HeapLayout × ℕ) × Unit => ((e.1.1, e.2), e.1.2))
    (appendWords indexWords oneWords) ![0, 1, 2, 3, 5, 4]
    (by intro e i; fin_cases i <;> rfl)
  have hfinish : Realizes .exact (fun _ : (HeapLayout × ℕ) × ℕ => pure ())
      (appendWords indexWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding)
      (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding (fun _ _ _ => True) (fun _ _ => 0) := by
    realize
  have h := (hprepare.bind hloop).bind hfinish
  refine (h.congr (p' := fun d => PriorityQueue.BinaryHeap.Memory.siftUp d.1.2 d.2)
    ?_).consequence ?_ ?_
  · intro d
    simpa only [← PFunctor.FreeM.bind_eq_bind, PFunctor.FreeM.pure_bind] using
      finish_loop_eq (d.1, ()) (Nat.log 2 d.2) d.2 le_rfl
  · intro w d s _ _ hi
    exact ⟨⟨hi, hi⟩, trivial⟩
  · intro d s
    simp [localWork, StateTransitionSpec.clientResult, StateTransitionSpec.clientState,
      StateTransitionSpec.runClient_pure', Nat.add_assoc]

/-- The queryful source pays every executed loop control. Bounded preparation/finish work is
absorbed into one fixed factor, so call sites may use the standard zero-work certificate.
This does not discard a query-free or arbitrary grading. -/
theorem realizes_siftUp :
    Realizes .exact (fun d : HeapLayout × ℕ => PriorityQueue.BinaryHeap.Memory.siftUp d.1.2 d.2)
      indexWords (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
      (fun w d s => Shape w (d.1, ()) d.2 s) (fun _ _ => 0) := by
  refine realizes_siftUp_graded.mono_mul 2 (fun d s => ?_)
  have hquery : ∀ x t, 1 ≤ memoryCost (step x) t := by
    intro x t
    change 1 ≤ 1 + _
    omega
  have hc := whileWork_zero_le guard step hquery (d.1, ()) (Nat.log 2 d.2) d.2 s
  have he := finish_loop_eq (d.1, ()) (Nat.log 2 d.2) d.2 le_rfl
  have hm : memoryCost (PriorityQueue.BinaryHeap.Memory.siftUp d.1.2 d.2) s =
      memoryCost (boundedWhile guard step (d.1, ()) (Nat.log 2 d.2) d.2) s := by
    rw [← he]
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure, Nat.add_zero]
  rw [← hm] at hc
  dsimp only [localWork]
  omega

/-- The actual combined currency is logarithmic. The premise is admissibility of the original
program's complete history, not an assumed cost of a different implementation. -/
theorem combined_le {w : ℕ} {d : HeapLayout × ℕ} {s : Memory.State}
    (hi : Shape w (d.1, ()) d.2 s)
    (hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (PriorityQueue.BinaryHeap.Memory.siftUp d.1.2 d.2))) :
    memoryCost (PriorityQueue.BinaryHeap.Memory.siftUp d.1.2 d.2) s + localWork d s ≤
      9 * Nat.log 2 d.2 + 2 := by
  have he := finish_loop_eq (d.1, ()) (Nat.log 2 d.2) d.2 le_rfl
  have hvalid : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      ((boundedWhile guard step (d.1, ()) (Nat.log 2 d.2) d.2).bind fun _ => pure ())) :=
    by
      rw [← he] at hv
      simpa only [← PFunctor.FreeM.bind_eq_bind] using hv
  have hvloop := ((validHistory_bind w _ (fun _ => pure ()) s).mp hvalid).1
  have hp := loop_currency_le hi hvloop
  have hm : memoryCost (PriorityQueue.BinaryHeap.Memory.siftUp d.1.2 d.2) s =
      memoryCost (boundedWhile guard step (d.1, ()) (Nat.log 2 d.2) d.2) s := by
    rw [← he]
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure, Nat.add_zero]
  rw [hm]
  unfold localWork
  omega

/-- One fixed native emitter repairs a sift-up defect in logarithmic instruction time. The
complete whole-memory result and live-register frame come from `Realizes`; order repair and
history admissibility come from the original source theorem. Arguments are already installed
in the stated register ABI. This bound does not include loading an arbitrary external heap. -/
theorem exec_siftUp {r : ℕ} (frontier : Fin r) (src : Fin 5 → Fin r)
    (tmp : Fin (0 + realizes_siftUp.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier)
    {w n S k : ℕ} (L : PriorityQueue.BinaryHeap.Memory.Layout n) (x : Data r)
    (hx : x.Bounded w) (hin : x.regs ∘ src = indexWords (⟨n, L⟩, k))
    (hA : L.arrays.Allocated (memoryState frontier x)) (hk : 1 ≤ k) (hkS : k ≤ S)
    (hshape : HeapShape n L.base S x.mem) (hord : UpOrdered (heapEntry n L.base x.mem) S k) :
    ∃ y, ExecWithin w (realizes_siftUp.code frontier src tmp) x y
        (9 * realizes_siftUp.factor * (Nat.log 2 n + 1)) ∧
      memoryState frontier y =
        (Memory.spec w).clientState (memoryState frontier x)
          (PriorityQueue.BinaryHeap.Memory.siftUp L k) ∧
      HeapInv n L.base S y.mem ∧
      PriorityQueue.BinaryHeap.Memory.Rearranges L
        (memoryState frontier x) (memoryState frontier y) ∧
      ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i := by
  have hn : Fits w n := by
    have h : Fits w ((x.regs ∘ src) 0) := hx.1 (src 0)
    rw [hin] at h
    exact h
  obtain ⟨hv, _, hpost⟩ := triple_iff.mp
    (PriorityQueue.BinaryHeap.Memory.siftUp_triple hn hA hk hkS hshape hord)
  have hI : Shape w ((⟨n, L⟩ : HeapLayout), ()) k (memoryState frontier x) :=
    ⟨hn, hA, S, hk, hkS, hshape⟩
  obtain ⟨y, hy, hm, _, hframe⟩ :=
    (realizes_siftUp.code_spec frontier src tmp hi hd hf hs).2 w (⟨n, L⟩, k) x hx hin hI hv
  have hc := combined_le (d := (⟨n, L⟩, k)) hI hv
  change memoryCost (PriorityQueue.BinaryHeap.Memory.siftUp L k) (memoryState frontier x) +
    localWork (⟨n, L⟩, k) (memoryState frontier x) ≤ 9 * Nat.log 2 k + 2 at hc
  have hlog := Nat.log_mono_right (b := 2) (hkS.trans hshape.size_le)
  have hbound : realizes_siftUp.factor *
      (memoryCost (PriorityQueue.BinaryHeap.Memory.siftUp L k) (memoryState frontier x) +
        localWork (⟨n, L⟩, k) (memoryState frontier x) + 1) ≤
      9 * realizes_siftUp.factor * (Nat.log 2 n + 1) := by
    calc
      _ ≤ realizes_siftUp.factor * (9 * (Nat.log 2 n + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  rw [← hm] at hpost
  refine ⟨y, hy.mono (le_trans ?_ hbound), hm, hpost.1, hpost.2, hframe⟩
  apply Nat.mul_le_mul_left
  change memoryCost (PriorityQueue.BinaryHeap.Memory.siftUp L k) (memoryState frontier x) +
      0 + 1 ≤ _
  omega

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.SiftUp
