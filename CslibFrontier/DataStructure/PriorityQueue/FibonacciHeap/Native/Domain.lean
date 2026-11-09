/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Update
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Source

/-!
# Source forest domains for native Fibonacci updates

The existing forest and record proofs supply the pointer and exact-subtraction conditions
needed by native source blocks. These are consequences of the existing `Cascading` invariant,
not a replacement heap model or a complete native decrease-key theorem.

## Main results

* `cutSafe_of_cascading`: the existing forest invariant and allocated layout supply the native
  cut's entry and actual intermediate-state domains.
* `cascadeStep_progress`: continuing source steps strictly decrease the original marked count.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

/-- Linking the Fibonacci record source has width-independent memory behavior. Width remains
in the separate admissibility predicate. -/
theorem link_width {n : ℕ} (base w : ℕ) {α : Type} (p : Prog α) :
    DataStructure.link (E := Memory.spec w) ((layout n base).methods w) p =
      DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) p := by
  have hm : ((layout n base).methods w :
      (o : Record.Op Cell) → Memory.Prog (Record.Op.Result o)) =
      ((layout n base).methods 0 : (o : Record.Op Cell) → Memory.Prog (Record.Op.Result o)) := by
    funext o
    cases o <;> rfl
  exact congrArg (fun methods => PFunctor.FreeM.liftM methods p) hm


private theorem mark_le_numMarked_of_par {n K : ℕ} {s : IndexedMinPQ.State n}
    {st : RawState n} {v m cur p : Fin n} {pending : Option (Fin n)} {ts : List (FHTree n)}
    (h : Cascading n K s st v m pending ts) (hcur : cur ∈ forestNodes ts)
    (hpar : st.par cur = p.val + 1) : st.mark cur ≤ st.numMarked := by
  obtain ⟨T, hT, hdesc⟩ := h.desc_of_par hcur (by omega)
  obtain ⟨_, _, _, hin, hmark, _, _⟩ := exists_parent_info (h.valid T hT).1 hdesc hpar
  rw [h.numMarked]
  by_cases hm : st.mark cur = 0
  · simp [hm]
  · have hpos : 0 < markedCount st := Finset.card_pos.mpr ⟨cur, by simp [markedSet, hin, hm]⟩
    omega

/-- The source forest conditions supply the intermediate root-list and mark/count conditions
needed to move an unlinked child to the roots. In particular, the subtraction premise follows
from the original marked-set interpretation of the count. -/
private theorem wp_unlink_rootFields {n K w : ℕ} {s : IndexedMinPQ.State n} {g : Cell → ℕ}
    {v m cur p : Fin n} {pending : Option (Fin n)} {ts : List (FHTree n)}
    (h : Cascading n K s (view n g) v m pending ts)
    (hcur : cur ∈ forestNodes ts) (hpar : (view n g).par cur = p.val + 1)
    (hfit : Fits w n) :
    Record.wp (Cell.ok n) w (unlink cur p) (fun _ g' _ =>
      (view n g').minRoot = m.val + 1 ∧
        (∃ r : Fin n, (view n g').right m = r.val) ∧
        (view n g').mark cur ≤ (view n g').numMarked) g := by
  have hmark_count := mark_le_numMarked_of_par h hcur hpar
  obtain ⟨rtail, hcirc, hperm⟩ := h.roots
  obtain ⟨hdeg, htwo, hdeg_le, hroots, _, _⟩ := h.cut_pre hperm hcur hpar
  refine wp_unlink hdeg htwo hdeg_le hfit fun g' _ _ left right child hunlink hview => ?_
  obtain ⟨r, hr⟩ := exists_right_min_of_unlink htwo hcirc hroots hunlink
  rw [hview]
  exact ⟨h.minRoot, ⟨r, hr⟩, hmark_count⟩

/-- A continuing original cascade step has a typed parent in the updated forest and strictly
fewer marked nodes. Stopping branches require no continuing forest witness. This is the
source progress fact used to justify native while nontruncation. -/
theorem cascadeStep_progress {n K w : ℕ} {s : IndexedMinPQ.State n} {g : Cell → ℕ}
    {v m z : Fin n} {ts : List (FHTree n)} (hfit : Fits w n)
    (h : Cascading n K s (view n g) v m (some z) ts)
    (hv : ∃ T ∈ ts, T.root = v)
    (hzv : ∀ T ∈ ts, z ∈ T.nodes → T.root ≠ v) (hz : z ∈ forestNodes ts) :
    Record.wp (Cell.ok n) w (cascadeStep z) (fun next g' _ =>
      next = none ∨ ∃ (p : Fin n) (ts' : List (FHTree n)), next = some p.val ∧
        Cascading n K s (view n g') v m (some p) ts' ∧
        (∃ T ∈ ts', T.root = v) ∧ (∀ T ∈ ts', p ∈ T.nodes → T.root ≠ v) ∧
        p ∈ forestNodes ts' ∧ (view n g').numMarked < (view n g).numMarked) g := by
  have hzn := z.isLt
  simp only [cascadeStep, Record.wp_read_bind, Cell.ok]
  refine ⟨hzn, ?_⟩
  by_cases hpz : (view n g).par z = 0
  · have hpz' : g (.par z) = 0 := hpz
    simp only [hpz', ite_true, Record.wp_pure]
    exact Or.inl trivial
  obtain ⟨T, hT, hdesc⟩ := h.desc_of_par hz hpz
  obtain ⟨p, _, hpar⟩ := (h.valid T hT).1.par_of_mem_children z hdesc
  have hpar' : g (.par z) = p.val + 1 := hpar
  simp only [hpar', Nat.add_one_ne_zero, ite_false, Record.wp_read_bind,
    Nat.add_sub_cancel, Cell.ok]
  refine ⟨hzn, ?_⟩
  by_cases hmz : (view n g).mark z = 0
  · have hmz' : g (.mark z) = 0 := hmz
    have hmarked := h.mark hz hpz hmz
    have hcount : (view n g).numMarked + 1 ≤ n :=
      calc (view n g).numMarked + 1 = markedCount _ := hmarked.numMarked
        _ ≤ n := markedCount_le_n _
    simp only [hmz', ite_true, Record.wp_write_bind, Record.wp_read_bind, Record.wp_pure,
      Function.update_apply, reduceCtorEq, ite_false, Cell.ok, true_and]
    exact ⟨⟨hzn, hfit.of_le (by omega)⟩, hfit.of_le hcount, Or.inl trivial⟩
  · have hmz' : g (.mark z) ≠ 0 := hmz
    simp only [hmz', ite_false]
    rw [Record.wp_bind]
    obtain ⟨rtail, hcirc, hperm⟩ := h.roots
    obtain ⟨hdp, hdp2, hdp_le, hroots, hnr, hnm⟩ := h.cut_pre hperm hz hpar
    refine wp_cut hdp hdp2 hdp_le h.minRoot hcirc hroots hpar hfit hnr hnm
      fun g' _ _ hcut => ?_
    simp only [Record.wp_pure]
    obtain ⟨ts', hc', hv', hpv', hp'⟩ :=
      hcut.cascading h hperm (Or.inr rfl) (Or.inr hv) hzv hz hpar
    refine Or.inr ⟨p, ts', rfl, hc', hv', hpv', hp', ?_⟩
    have hmark_count := mark_le_numMarked_of_par h hz hpar
    have hnew := hcut.numMarked
    omega

/-- The original `Cascading` forest supplies every cut domain, including the mark/count
subtraction after the actual unlink run. The lower refinement transports the source record
facts to literal memory addresses; the full heap invariant need not hold between the blocks. -/
theorem cutSafe_of_cascading {n K w base : ℕ} {s : IndexedMinPQ.State n}
    {mem : Memory.State} {v m cur p : Fin n} {pending : Option (Fin n)} {ts : List (FHTree n)}
    (hfit : Fits w (base + (9 * n + 5))) (halloc : (layout n base).Inv mem)
    (h : Cascading n K s (view n ((layout n base).abs mem)) v m pending ts)
    (hcur : cur ∈ forestNodes ts)
    (hpar : (view n ((layout n base).abs mem)).par cur = p.val + 1) :
    cutSafe w ![n, base, cur.val, p.val] mem := by
  have hn : Fits w n := hfit.of_le (by omega)
  have hw := wp_unlink_rootFields h hcur hpar hn
  obtain ⟨hv, hfields⟩ := (Record.wp_iff _ _ _).mp hw
  obtain ⟨_, _, habs, _⟩ :=
    (Record.refinement (layout n base) w).simulates_client (unlink cur p) halloc hv
  dsimp only [Record.refinement] at habs
  change (layout n base).abs ((Memory.spec w).clientState mem
      (DataStructure.link (E := Memory.spec w) ((layout n base).methods w) (unlink cur p))) =
    (Record.spec (Cell.ok n) w).clientState ((layout n base).abs mem) (unlink cur p) at habs
  rw [Realization.clientState_width w] at habs
  rw [link_width] at habs
  rw [← habs] at hfields
  let next := (Memory.spec 0).clientState mem
    (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) (unlink cur p))
  have hmin : next.mem (base + 9 * n + 1) = m.val + 1 := by
    simpa only [view, Record.Layout.abs, Cell.ok, ite_true, layout, next] using hfields.1
  obtain ⟨r, hr⟩ := hfields.2.1
  have hright : next.mem (base + 4 * n + m.val) = r.val := by
    simpa only [view, Record.Layout.abs, Cell.ok, m.isLt, ite_true, layout, next] using hr
  have hmark : next.mem (base + 6 * n + cur.val) ≤ next.mem (base + 9 * n + 3) := by
    simpa only [view, Record.Layout.abs, Cell.ok, cur.isLt, ite_true, layout, next]
      using hfields.2.2
  obtain ⟨_, _, hperm⟩ := h.roots
  have hpos := (h.cut_pre hperm hcur hpar).1
  have hdeg : 1 ≤ mem.mem (base + 5 * n + p.val) := by
    simpa only [view, Record.Layout.abs, Cell.ok, p.isLt, ite_true, layout] using hpos
  change Fits w (base + (9 * n + 5)) ∧ cur.val < n ∧ p.val < n ∧
    1 ≤ mem.mem (base + 5 * n + p.val) ∧ _
  refine ⟨hfit, cur.isLt, p.isLt, hdeg, ?_⟩
  change 1 ≤ next.mem (base + 9 * n + 1) ∧ next.mem (base + 9 * n + 1) ≤ n ∧
    next.mem (base + 4 * n + (next.mem (base + 9 * n + 1) - 1)) < n ∧
    next.mem (base + 6 * n + cur.val) ≤ next.mem (base + 9 * n + 3)
  rw [hmin, Nat.add_sub_cancel, hright]
  exact ⟨by omega, by have := m.isLt; omega, r.isLt, hmark⟩

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
