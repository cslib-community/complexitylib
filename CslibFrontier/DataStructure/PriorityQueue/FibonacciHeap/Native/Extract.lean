/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Consolidate
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.ExtractSource
import CslibFrontier.Tactic.Realize
import CslibFrontier.DataStructure.Memory.RecordLink
import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Domain

/-!
# Native extraction of the original indexed Fibonacci heap

The native source detaches the minimum, reuses the original two root-list phases and table
scan, and returns the unshifted optional handle/key words. Its exact program erases only the
original typed handle. Source admissibility, the allocated representation and the original
forest invariant remain distinct requirements.

## Main results

* `realizes_extractRaw`: native realization of the complete original extraction source.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

private def forestReturn (d : Fin 8 → ℕ) : Memory.Prog (Option (ℕ × ℕ)) := do
  DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
    (scatterForest (d 0) (d 2) (d 3) (d 4) (d 5))
  if d 6 < d 0 then pure (some (d 6, d 7)) else pure none

private def forestReturnSafe (w : ℕ) (d : Fin 8 → ℕ) (s : Memory.State) : Prop :=
  forestSafe w ![d 0, d 1, d 2, d 3, d 4, d 5] s ∧ Fits w 1

private theorem realizes_forestReturn : Realizes .exact forestReturn (.refl _)
    (WordEncoding.encode (α := Option (ℕ × ℕ))) forestReturnSafe (fun _ _ => 0) := by
  have hForest := realizes_scatterForest.reindex
    (fun d : Fin 8 → ℕ => ![d 0, d 1, d 2, d 3, d 4, d 5]) (.refl _) ![0, 1, 2, 3, 4, 5]
    (by intro d i; fin_cases i <;> rfl)
  have hRet : Realizes .exact
      (fun d : (Fin 8 → ℕ) × Unit =>
        if d.1 6 < d.1 0 then pure (some (d.1 6, d.1 7)) else pure none)
      (appendWords (.refl _) (WordEncoding.encode (α := Unit)))
      (WordEncoding.encode (α := Option (ℕ × ℕ)))
      (fun w _ _ => Fits w 1) (fun _ _ => 0) := by
    realize
    exact h
  exact (hForest.bind₀ hRet).congr (fun _ => rfl)

private def extractBody (d : Fin 2 → ℕ) : Memory.Prog (Option (ℕ × ℕ)) := do
  let m ← Memory.read (d 1 + 9 * d 0 + 1)
  if m = 0 then pure none
  else
    let u ← pure (m - 1)
    let key ← Memory.read (d 1 + u)
    Memory.write (d 1 + 7 * d 0 + u) 0
    let sz ← Memory.read (d 1 + 9 * d 0 + 4)
    Memory.write (d 1 + 9 * d 0 + 4) (sz - 1)
    let right ← Memory.read (d 1 + 4 * d 0 + u)
    let nr ← Memory.read (d 1 + 9 * d 0 + 2)
    let degree ← Memory.read (d 1 + 5 * d 0 + u)
    let child ← Memory.read (d 1 + 2 * d 0 + u)
    let args ← pure (((((((d 0, d 1), nr), right), degree), child), u), key)
    forestReturn ![args.1.1.1.1.1.1.1, args.1.1.1.1.1.1.2, args.1.1.1.1.1.2,
      args.1.1.1.1.2, args.1.1.1.2, args.1.1.2, args.1.2, args.2]

private def extractSafe (w : ℕ) (d : Fin 2 → ℕ) (s : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧
    (s.mem (d 1 + 9 * d 0 + 1) ≠ 0 →
      let u := s.mem (d 1 + 9 * d 0 + 1) - 1
      u < d 0 ∧ 1 ≤ s.mem (d 1 + 9 * d 0 + 4) ∧
        forestReturnSafe w ![d 0, d 1, s.mem (d 1 + 9 * d 0 + 2),
          s.mem (d 1 + 4 * d 0 + u), s.mem (d 1 + 5 * d 0 + u),
          s.mem (d 1 + 2 * d 0 + u), u, s.mem (d 1 + u)]
          ⟨Function.update (Function.update s.mem (d 1 + 7 * d 0 + u) 0)
            (d 1 + 9 * d 0 + 4) (s.mem (d 1 + 9 * d 0 + 4) - 1), s.frontier⟩)

private theorem realizes_extractBody : Realizes .exact extractBody (.refl _)
    (WordEncoding.encode (α := Option (ℕ × ℕ))) extractSafe (fun _ _ => 0) := by
  have hTail := realizes_forestReturn.reindex
    (fun d : ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
      ![d.1.1.1.1.1.1.1, d.1.1.1.1.1.1.2, d.1.1.1.1.1.2, d.1.1.1.1.2,
        d.1.1.1.2, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ))
    ![0, 1, 2, 3, 4, 5, 6, 7] (by intro d i; fin_cases i <;> rfl)
  have nine (n : ℕ) : n + n + n + n + n + n + n + n + n = 9 * n := by omega
  conv =>
    arg 2
    ext d
    simp only [extractBody, ← nine]
  realize
  all_goals try simp only [nine] at *
  all_goals try have hdom := h.2 (by assumption)
  all_goals try simp (disch := omega) only [Function.update_of_ne] at *
  all_goals first
    | exact h.1.of_le (by have := h.2 (by assumption); omega)
    | exact (h.2 (by assumption)).2.1
    | exact (h.2 (by assumption)).2.2
    | exact h.1.of_le (by omega)
    | omega

private theorem erase_fin_check (n u key : ℕ) :
    Option.map (fun a : Fin n × ℕ => (a.1.val, a.2))
        (if h : u < n then some (⟨u, h⟩, key) else none) =
      if u < n then some (u, key) else none := by
  by_cases hu : u < n <;> simp [hu]

private theorem forestReturn_eq (n base nr right degree child u key : ℕ) :
    forestReturn ![n, base, nr, right, degree, child, u, key] = (do
      DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0)
        (scatterForest n nr right degree child)
      if u < n then pure (some (u, key)) else pure none) := rfl

private theorem extractBody_eq (d : Fin 2 → ℕ) : extractBody d =
    DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
      (extractRaw (d 0)) := by
  rw [link_extractRaw_eq, ← bind_pure_comp]
  simp only [extractBody, extractMin, DataStructure.link, PFunctor.FreeM.liftM_bind,
    Record.lift_ite, PFunctor.FreeM.liftM_pure, bind_assoc, pure_bind]
  congr 1 with m : 1
  by_cases hm : m = 0
  · simp only [hm, ite_true, pure_bind, Option.map_none]
  · have pure_if (u key : ℕ) :
        (if u < d 0 then (pure (some (u, key)) : Memory.Prog (Option (ℕ × ℕ))) else pure none) =
          pure (if u < d 0 then some (u, key) else none) := by
      by_cases hu : u < d 0 <;> simp [hu]
    simp only [hm, ite_false, pure_bind, forestReturn_eq, scatterForest, finishRoots,
      DataStructure.link, PFunctor.FreeM.liftM_bind, bind_assoc, erase_fin_check, pure_if]
    rfl


/-- The original allocated indexed-heap invariant and its current word envelope. Capacity zero
is retained; this predicate introduces no stronger key, layout or abstract-space contract. -/
@[expose] def extractValid (w : ℕ) (d : Fin 2 → ℕ) (s : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ (layout (d 0) (d 1)).Inv s ∧
    ∃ K, Fits w K ∧ Inv (d 0) K ((layout (d 0) (d 1)).abs s)

private theorem extractSafe_of_valid {w : ℕ} {d : Fin 2 → ℕ} {mem : Memory.State}
    (h : extractValid w d mem) : extractSafe w d mem := by
  obtain ⟨hfit, halloc, K, _, hI⟩ := h
  refine ⟨hfit, ?_⟩
  intro hm
  rcases minRoot_cases hI with h0 | ⟨m, _, hmin, _⟩
  · exact (hm h0).elim
  have hmin' : mem.mem (d 1 + 9 * d 0 + 1) = m.val + 1 := hmin
  rw [hmin', Nat.add_sub_cancel]
  obtain ⟨cs, roots, hD⟩ := FibRawInv.detach hI hmin
  have hmem : m ∈ IndexedMinPQ.dom (abs (d 0) ((layout (d 0) (d 1)).abs mem)) :=
    IndexedMinPQ.mem_dom_iff.mpr ⟨_, (FibRawInv.findMin_eq_some hI hmin).2.1⟩
  have hsz : 1 ≤ (view (d 0) ((layout (d 0) (d 1)).abs mem)).sz := by
    rw [hD.sz]
    exact Finset.card_pos.mpr ⟨m, hmem⟩
  let next : Memory.State :=
    ⟨Function.update (Function.update mem.mem (d 1 + 7 * d 0 + m.val) 0)
      (d 1 + 9 * d 0 + 4) (mem.mem (d 1 + 9 * d 0 + 4) - 1), mem.frontier⟩
  have hi : (layout (d 0) (d 1)).Inv next := halloc
  have ha : view (d 0) ((layout (d 0) (d 1)).abs next) =
      detachState (view (d 0) ((layout (d 0) (d 1)).abs mem)) m := by
    change view (d 0) ((layout (d 0) (d 1)).abs
      ⟨Function.update (Function.update mem.mem ((layout (d 0) (d 1)).addr (.inHeap m)) 0)
        ((layout (d 0) (d 1)).addr .sz) (mem.mem (d 1 + 9 * d 0 + 4) - 1), mem.frontier⟩) = _
    rw [(layout (d 0) (d 1)).abs_write
      (m := ⟨Function.update mem.mem ((layout (d 0) (d 1)).addr (.inHeap m)) 0, mem.frontier⟩)
      (i := .sz) trivial _,
      (layout (d 0) (d 1)).abs_write (m := mem) (i := .inHeap m) m.isLt 0,
      view_update_sz, view_update_inHeap]
    rfl
  have hf := forestSafe_of_detached hfit hi hD ha
  have hnr : mem.mem (d 1 + 9 * d 0 + 2) = roots.length + 1 := hD.numRoots
  have hdeg : mem.mem (d 1 + 5 * d 0 + m.val) = cs.length := by
    simpa only [view, Record.Layout.abs, Cell.ok, m.isLt, ite_true, layout] using hD.deg
  refine ⟨m.isLt, hsz, ?_, hfit.of_le (by omega)⟩
  change forestSafe w ![d 0, d 1, mem.mem (d 1 + 9 * d 0 + 2),
    mem.mem (d 1 + 4 * d 0 + m.val), mem.mem (d 1 + 5 * d 0 + m.val),
    mem.mem (d 1 + 2 * d 0 + m.val)] next
  rw [hnr, hdeg]
  simpa only [view, Record.Layout.abs, Cell.ok, m.isLt, ite_true, layout] using hf

/-- One uniform native certificate for the complete original extraction source, with only
its typed result erased. The existing heap invariant supplies every reached phase domain;
its nonzero amortized potential is retained for operation-family and caller transport. -/
theorem realizes_extractRaw : Realizes .exact
    (fun d : Fin 2 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (extractRaw (d 0)))
    (.refl _) (WordEncoding.encode (α := Option (ℕ × ℕ))) extractValid (fun _ _ => 0) :=
  (realizes_extractBody.congr extractBody_eq).consequence
    (fun _ _ _ _ _ h => extractSafe_of_valid h) (fun _ _ => le_rfl)

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
