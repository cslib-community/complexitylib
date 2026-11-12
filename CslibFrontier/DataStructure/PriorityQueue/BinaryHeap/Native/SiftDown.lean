/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
public import CslibFrontier.Computability.WordRAM.Realization.Reindex
public import CslibFrontier.Computability.WordRAM.Realization.Witness
public import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Encoding
import CslibFrontier.Tactic.Realize
import CslibFrontier.Computability.WordRAM.Realization.Backend

/-!
# Source-faithful native sift-down

The existing memory program supplies the array reads, swap and order proof. A finite while view
preserves its complete free-monad program. Its logarithmic cutoff is proof data, while native
code tests the actual index against a charged prepared threshold. No runtime logarithm or fuel
register is supplied for free. The initially-zero index exits before threshold preparation.
The compiler handles the original named priority and non-strict right-child guards directly.

## Main results

* `finish_loop_eq`: the while view is the complete original memory program.
* `step_triple`: the existing heap shape survives each body and the logarithmic rank drops.
* `realizes_siftDown`: one uniform compiler-generated emitter with charged glue and control.
* `exec_siftDown`: the original order repair, whole-memory result and frame in logarithmic
  unit-cost exact-basis instruction time, on the explicit allocated/word-bounded input domain.

The source heap invariants and order proof are reused, not a new heap algorithm or model.
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.SiftDown

open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.PriorityQueue Cslib.DataStructure.PriorityQueue.BinaryHeap

/-- Layout, size and one control word: a threshold inside the loop, an index at entry. -/
abbrev Argument := (HeapLayout × ℕ) × ℕ

/-- The original four-write sink, returning the selected child or a stop sentinel. -/
def sink {n : ℕ} (L : BinaryHeap.Memory.Layout n) (S k c vk kk vc kc : ℕ) : Memory.Prog ℕ :=
  if IndexedMinPQ.RawPrioLT (vc, kc) (vk, kk) then do
    BinaryHeap.Memory.swap L k c vk vc
    pure c
  else pure (S + 1)

/-- Four reads, two additional right-child reads when present, and exactly the source swap. -/
def step (d : Argument × ℕ) : Memory.Prog ℕ := do
  let L := d.1.1.1.2
  let S := d.1.1.2
  let k := d.2
  let vk ← L.heap.get k
  let kk ← L.key.get vk
  let vl ← L.heap.get (2 * k)
  let kl ← L.key.get vl
  if 2 * k + 1 ≤ S then do
    let vr ← L.heap.get (2 * k + 1)
    let kr ← L.key.get vr
    if IndexedMinPQ.RawPrioLT (vr, kr) (vl, kl) then
      sink L S k (2 * k + 1) vk kk vr kr
    else sink L S k (2 * k) vk kk vl kl
  else sink L S k (2 * k) vk kk vl kl

/-- Actual scalar native guard; the threshold is computed by preceding certified glue. -/
def guard (d : Argument) (k : ℕ) : Prop := k < d.2

instance (d : Argument) (k : ℕ) : Decidable (guard d k) := inferInstanceAs (Decidable (k < d.2))

/-- Positive positions turn the source multiplication test into a native threshold test. -/
theorem guard_iff {d : Argument} {k : ℕ} (ht : d.2 = d.1.2 / 2 + 1) (hk : 1 ≤ k) :
    guard d k ↔ 1 ≤ k ∧ 2 * k ≤ d.1.2 := by
  unfold guard
  rw [ht]
  omega

/-- Every child edge increases the base-two logarithm by exactly one. -/
private theorem log_child {k c : ℕ} (hk : 1 ≤ k) (hc : c / 2 = k) :
    Nat.log 2 c = Nat.log 2 k + 1 := by
  rw [Nat.log_of_one_lt_of_le one_lt_two (by omega), hc]

/-- Forgetting the final index preserves the exact source, including every query and write.
The cutoff is an input-only logarithmic bound, and it never truncates on this domain. -/
theorem finish_loop_eq (d : Argument) (ht : d.2 = d.1.2 / 2 + 1) (fuel k : ℕ)
    (hk : 1 ≤ k) (hcut : Nat.log 2 d.1.2 - Nat.log 2 k ≤ fuel) :
    (do let _ ← boundedWhile guard step d fuel k; pure ()) =
      BinaryHeap.Memory.siftDown d.1.1.2 d.1.2 k := by
  induction fuel generalizing k with
  | zero =>
    have hstop : ¬(1 ≤ k ∧ 2 * k ≤ d.1.2) := by
      intro hg
      have hm := Nat.log_mono_right (b := 2) hg.2
      have hl := log_child hk (show (2 * k) / 2 = k by omega)
      omega
    rw [BinaryHeap.Memory.siftDown, ite_eq_right hstop]
    rfl
  | succ fuel ih =>
    have hstop : ¬guard d (d.1.2 + 1) := by simp only [guard, ht]; omega
    have hsink (c vk kk vc kc : ℕ) (hc : c / 2 = k) (hcS : c ≤ d.1.2) :
        (do
          let a ← sink d.1.1.2 d.1.2 k c vk kk vc kc
          let _ ← boundedWhile guard step d fuel a
          pure ()) =
          BinaryHeap.Memory.sink d.1.1.2 k c vk kk vc kc
            (BinaryHeap.Memory.siftDown d.1.1.2 d.1.2 c) := by
      unfold sink BinaryHeap.Memory.sink
      split
      · simp only [bind_assoc, pure_bind]
        congr 1 with _ : 1
        apply ih c (by omega)
        have hl := log_child hk hc
        have hm := Nat.log_mono_right (b := 2) hcS
        omega
      · simp only [pure_bind, boundedWhile_of_not guard step d fuel (d.1.2 + 1) hstop]
    rw [BinaryHeap.Memory.siftDown]
    by_cases hg : guard d k
    · have hsrc := (guard_iff ht hk).mp hg
      simp only [boundedWhile, hg, hsrc, ↓reduceIte, step, bind_assoc]
      congr 1 with vk : 1
      congr 1 with kk : 1
      congr 1 with vl : 1
      congr 1 with kl : 1
      split
      next hr =>
        simp only [bind_assoc]
        congr 1 with vr : 1
        congr 1 with kr : 1
        split
        · exact hsink (2 * k + 1) vk kk vr kr (by omega) hr
        · exact hsink (2 * k) vk kk vl kl (by omega) hsrc.2
      next hr =>
        exact hsink (2 * k) vk kk vl kl (by omega) hsrc.2
    · have hsrc : ¬(1 ≤ k ∧ 2 * k ≤ d.1.2) := mt (guard_iff ht hk).mpr hg
      simp only [boundedWhile, hg, hsrc, ↓reduceIte, pure_bind]

/-- Reached loop indices are occupied positions or the stop sentinel `S+1`. The original
whole-memory heap shape and allocated array block remain explicit. -/
def Shape (w : ℕ) (d : Argument) (k : ℕ) (s : Memory.State) : Prop :=
  d.2 = d.1.2 / 2 + 1 ∧ Fits w d.1.1.1 ∧ d.1.1.2.arrays.Allocated s ∧
    HeapShape d.1.1.1 d.1.1.2.base d.1.2 s.mem ∧ 1 ≤ k ∧ k ≤ d.1.2 + 1

/-- The logarithmic distance to the last occupied level. -/
def rank (d : Argument) (k : ℕ) : ℕ := Nat.log 2 d.1.2 - Nat.log 2 k

/-- Each continuing body keeps the existing shape and strictly decreases its ghost rank.
It uses at most four ordinary reads, two right reads and the original four-write swap. -/
theorem step_triple {w : ℕ} {d : Argument} {k : ℕ} {s : Memory.State}
    (hi : Shape w d k s) (hg : guard d k) :
    Triple w s (step (d, k)) 10 (fun a s' => Shape w d a s' ∧ rank d a < rank d k) := by
  obtain ⟨ht, hn, hA, hshape, hk, hkS⟩ := hi
  have hsrc := (guard_iff ht hk).mp hg
  have hSn := hshape.size_le
  have hvk := hshape.vertex_lt k hk (by omega)
  have hvl := hshape.vertex_lt (2 * k) (by omega) hsrc.2
  have hlog2 := log_child hk (show (2 * k) / 2 = k by omega)
  have hlogS := Nat.log_mono_right (b := 2) hsrc.2
  have hsink (c : ℕ) (hc : c / 2 = k) (hcS : c ≤ d.1.2) :
      Triple w s
        (sink d.1.1.2 d.1.2 k c
          (s.mem (d.1.1.2.base + d.1.1.1 + k))
          (s.mem (d.1.1.2.base + s.mem (d.1.1.2.base + d.1.1.1 + k)))
          (s.mem (d.1.1.2.base + d.1.1.1 + c))
          (s.mem (d.1.1.2.base + s.mem (d.1.1.2.base + d.1.1.1 + c)))) 4
        (fun a s' => Shape w d a s' ∧ rank d a < rank d k) := by
    have hc1 : 1 ≤ c := by omega
    have hvc := hshape.vertex_lt c hc1 hcS
    unfold sink
    split
    · obtain ⟨hshape', -, -, -, -, -⟩ :=
        hshape.swap (a := k) (b := c) hk (by omega) hc1 hcS (by omega)
      refine BinaryHeap.Memory.swap_bind hn hA (by omega) (by omega) hvk hvc <|
        Triple.pure ?_
      refine ⟨⟨ht, hn, hA, hshape', hc1, by omega⟩, ?_⟩
      have hl := log_child hk hc
      have hm := Nat.log_mono_right (b := 2) hcS
      unfold rank
      omega
    · refine Triple.pure ⟨⟨ht, hn, hA, hshape, by omega, le_rfl⟩, ?_⟩
      have hm : Nat.log 2 d.1.2 ≤ Nat.log 2 (d.1.2 + 1) :=
        Nat.log_mono_right (by omega)
      have hz : rank d (d.1.2 + 1) = 0 := Nat.sub_eq_zero_of_le hm
      rw [hz]
      change 0 < Nat.log 2 d.1.2 - Nat.log 2 k
      omega
  unfold step
  dsimp only
  refine Triple.read_bind (BinaryHeap.Memory.heap_lt hA (by omega)) <|
    Triple.read_bind (BinaryHeap.Memory.key_lt hA hvk) <|
    Triple.read_bind (BinaryHeap.Memory.heap_lt hA (by omega)) <|
    Triple.read_bind (BinaryHeap.Memory.key_lt hA hvl) ?_
  split
  next hr =>
    have hvr := hshape.vertex_lt (2 * k + 1) (by omega) hr
    refine Triple.read_bind (BinaryHeap.Memory.heap_lt hA (by omega)) <|
      Triple.read_bind (BinaryHeap.Memory.key_lt hA hvr) ?_
    split
    · exact hsink (2 * k + 1) (by omega) hr
    · exact hsink (2 * k) (by omega) hsrc.2
  next hr =>
    exact (hsink (2 * k) (by omega) hsrc.2).mono (by omega) fun _ _ h => h

/-- The layout/size, then the charged prepared threshold. -/
abbrev inputWords := appendWords indexWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

/-- The shared compiler certifies the exact physical body; all fit obligations follow from
allocated storage and the original heap shape, including the sentinel `S+1`. -/
theorem realizes_step : Realizes .exact step
    (appendWords inputWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding)
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
    (fun w (d, k) s => Shape w d k s ∧ guard d k) (fun _ _ => 0) := by
  realize
  all_goals
    rcases h with ⟨⟨ht, hn, hA, hshape, hk, hkS⟩, hg⟩
    have hsrc := (guard_iff ht hk).mp hg
    have hSn := hshape.size_le
    have hvk := hshape.vertex_lt d.2 hk (by omega)
    have hvl := hshape.vertex_lt (2 * d.2) (by omega) hsrc.2
    have halloc : d.1.1.1.2.base + (3 * d.1.1.1.1 + 1) ≤ s.frontier := hA
    first
    | omega
    | exact hn.of_le (by omega)
    | exact hmem.frontier_fits.of_le (by omega)
    | exact hmem.fits_of_lt_frontier (BinaryHeap.Memory.key_lt hA
        (hshape.vertex_lt (2 * d.2 + 1) (by omega) (by omega)))
    | exact hmem.fits_of_lt_frontier (BinaryHeap.Memory.pos_lt hA
        (hshape.vertex_lt (2 * d.2 + 1) (by omega) (by omega)))

/-- The source cutoff suffices: rank zero stops, and every real body strictly drops rank.
The actual returned index may be the fitted sentinel, never a hidden truncated continuation. -/
theorem loop_safe {w : ℕ} {d : Argument} {k : ℕ} {s : Memory.State}
    (hi : Shape w d k s)
    (hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (boundedWhile guard step d (rank d k) k))) :
    whileSafe guard step (fun w (d, k) s => Shape w d k s ∧ guard d k)
      w d (rank d k) k s := by
  refine whileSafe_of_measure guard step _ w d (Shape w d) (fun a _ => rank d a)
    (fun a s hi hz hg => ?_) (fun a s hi hg _ => ?_) hi le_rfl hv
  · have hsrc := (guard_iff hi.1 hi.2.2.2.2.1).mp hg
    have hm := Nat.log_mono_right (b := 2) hsrc.2
    have hl := log_child hsrc.1 (show (2 * a) / 2 = a by omega)
    unfold rank at hz
    omega
  · obtain ⟨_, _, hpost⟩ := triple_iff.mp (step_triple hi hg)
    rw [clientResult_width w, clientState_width w] at hpost
    exact ⟨⟨hi, hg⟩, hpost⟩

/-- The queryful body pays each real loop iteration's control, including all early exits. -/
theorem realizes_loop : Realizes .exact
    (fun (d, k) => boundedWhile guard step d (rank d k) k)
    (appendWords inputWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding)
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
    (fun w (d, k) s => Shape w d k s) (fun _ _ => 0) := by
  have hStep := realizes_step
  realize
  intro hv
  -- Compare body domains at the loop's fixed captured environment.
  refine whileSafe_imp _ _ (fun _ => Iff.rfl) (fun _ => rfl) ?_ (loop_safe h hv)
  intro a t hg hi
  exact hi

/-- The original source storage/shape domain, admitting index zero as an immediate exit. -/
def Safe (w : ℕ) (d : Argument) (s : Memory.State) : Prop :=
  Fits w d.1.1.1 ∧ d.1.1.2.arrays.Allocated s ∧
    HeapShape d.1.1.1 d.1.1.2.base d.1.2 s.mem ∧ d.2 ≤ d.1.2

/-- The existing source sift-down has one fixed native emitter before every runtime layout,
size, start index, width and memory. Zero exits before division; otherwise threshold preparation,
all guard/control operations, body glue and final Unit return are certified and charged.
The local loop certificate lets `realize` prepare the threshold and wire the call. -/
theorem realizes_siftDown : Realizes .exact
    (fun d : Argument => BinaryHeap.Memory.siftDown d.1.1.2 d.1.2 d.2)
    inputWords (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding Safe (fun _ _ => 0) := by
  let p (d : Argument) : Memory.Prog Unit :=
    if d.2 = 0 then pure () else do
      let _ ← boundedWhile guard step (d.1, d.1.2 / 2 + 1)
        (rank (d.1, d.1.2 / 2 + 1) d.2) d.2
      pure ()
  have hp : Realizes .exact p inputWords (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
      Safe (fun _ _ => 0) := by
    have hLoop := realizes_loop
    realize
    all_goals
      rcases h with ⟨hn, hA, hshape, hkS⟩
      have hSn := hshape.size_le
      have halloc : d.1.1.2.base + (3 * d.1.1.1 + 1) ≤ s.frontier := hA
      first
      | exact ⟨rfl, hn, hA, hshape, by omega, hkS.trans (Nat.le_succ _)⟩
      | omega
      | exact hmem.frontier_fits.of_le (by omega)
  refine hp.congr ?_
  intro d
  dsimp only [p]
  by_cases hk : d.2 = 0
  · simp [hk, BinaryHeap.Memory.siftDown]
  · rw [ite_eq_right hk]
    exact finish_loop_eq (d.1, d.1.2 / 2 + 1) rfl
      (rank (d.1, d.1.2 / 2 + 1) d.2) d.2 (by omega) le_rfl

/-- The exact source's logarithmic order repair and rearrangement lift to one uniform native
code witness. The caller supplies already installed arguments, word bounds and an allocated
heap; loading arbitrary external storage is outside this operation clock. -/
theorem exec_siftDown {r : ℕ} (frontier : Fin r) (src : Fin 6 → Fin r)
    (tmp : Fin (0 + realizes_siftDown.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier)
    {w n S k : ℕ} (L : BinaryHeap.Memory.Layout n) (x : Data r)
    (hx : x.Bounded w) (hin : x.regs ∘ src = inputWords ((⟨n, L⟩, S), k))
    (hA : L.arrays.Allocated (memoryState frontier x)) (hkS : k ≤ S)
    (hshape : HeapShape n L.base S x.mem) (hord : DownOrdered (heapEntry n L.base x.mem) S k) :
    ∃ y, ExecWithin w (realizes_siftDown.code frontier src tmp) x y
        (10 * realizes_siftDown.factor * (Nat.log 2 n + 1)) ∧
      memoryState frontier y =
        (Memory.spec w).clientState (memoryState frontier x) (BinaryHeap.Memory.siftDown L S k) ∧
      HeapInv n L.base S y.mem ∧
      BinaryHeap.Memory.Rearranges L (memoryState frontier x) (memoryState frontier y) ∧
      ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i := by
  have hn : Fits w n := by
    have h : Fits w ((x.regs ∘ src) 0) := hx.1 (src 0)
    rw [hin] at h
    exact h
  obtain ⟨hv, hc, hpost⟩ := triple_iff.mp
    (BinaryHeap.Memory.siftDown_triple hn hA hkS hshape hord)
  have hI : Safe w (((⟨n, L⟩ : HeapLayout), S), k) (memoryState frontier x) :=
    ⟨hn, hA, hshape, hkS⟩
  obtain ⟨y, hy, hm, _, hframe⟩ :=
    (realizes_siftDown.code_spec frontier src tmp hi hd hf hs).2 w ((⟨n, L⟩, S), k) x
      hx hin hI hv
  rw [← memoryCost_eq_totalCost] at hc
  have hlog := Nat.log_mono_right (b := 2) hshape.size_le
  have hbound : realizes_siftDown.factor *
      (memoryCost (BinaryHeap.Memory.siftDown L S k) (memoryState frontier x) + 0 + 1) ≤
      10 * realizes_siftDown.factor * (Nat.log 2 n + 1) := by
    calc
      _ ≤ realizes_siftDown.factor * (10 * (Nat.log 2 n + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  rw [← hm] at hpost
  exact ⟨y, hy.mono hbound, hm, hpost.1, hpost.2, hframe⟩

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.SiftDown
