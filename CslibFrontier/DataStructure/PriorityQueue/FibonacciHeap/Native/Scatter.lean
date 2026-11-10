/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Link
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Source
public import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
import CslibFrontier.Tactic.Realize
import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Domain

/-!
# Native consolidation-table steps

A consolidation step either places the root and stops or clears its occupied slot, performs the
original certified root link, and continues. The maximum-degree accumulator uses a paid native
comparison, preserving the original `max` source expression. The body domain concerns the actual
cleared-table memory. The original placement forest supplies those domains and proves the
finite cutoff sufficient. Full extraction also needs the root-list and table traversals.

## Main definitions

* `scatterStepSafe`: handle, degree-table and actual cleared-state link domains.
* `scatterSafe`: the reached body domains and nontruncating finite while domain.

## Main results

* `realizes_scatterStep`: the original consolidation step with its pending root and maximum.
* `scatterSafe_of_placing`: the existing forest placement supplies all native loop domains.
* `realizes_scatter`: the complete consolidation recursion through the shared native while rule.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

private def scatterBody (d : Fin 4 → ℕ) : Memory.Prog (Option ℕ × ℕ) := do
  let deg ← Memory.read (d 1 + 5 * d 0 + d 2)
  let c ← Memory.read (d 1 + 8 * d 0 + deg)
  if c = 0 then
    Memory.write (d 1 + 8 * d 0 + deg) (d 2 + 1)
    if d 3 < deg then pure (none, deg) else pure (none, d 3)
  else
    Memory.write (d 1 + 8 * d 0 + deg) 0
    let p ← pure (c - 1)
    let u ← DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
      (FibonacciHeap.link (d 2) p)
    pure (some u, d 3)

private theorem scatterBody_eq (d : Fin 4 → ℕ) : scatterBody d =
    DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
      (scatterStep (d 2, d 3)) := by
  simp only [scatterBody, scatterStep, DataStructure.link, PFunctor.FreeM.liftM_bind]
  congr 1 with deg : 1
  congr 1 with c : 1
  by_cases hc : c = 0
  · simp only [hc, ite_true, PFunctor.FreeM.liftM_bind, PFunctor.FreeM.liftM_pure]
    congr 1 with _ : 1
    by_cases hmax : d 3 < deg
    · rw [ite_eq_left hmax, max_eq_right (Nat.le_of_lt hmax)]
    · rw [ite_eq_right hmax, max_eq_left (Nat.le_of_not_lt hmax)]
  · simp only [hc, ite_false, PFunctor.FreeM.liftM_bind, PFunctor.FreeM.liftM_pure, pure_bind]
    rfl

/-- Native compiler conditions for the reached consolidation step. The occupied-slot branch
uses the same root-link domain at the memory obtained by its actual zero write. -/
@[expose] def scatterStepSafe (w : ℕ) (d : Fin 4 → ℕ) (s : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧ s.mem (d 1 + 5 * d 0 + d 2) ≤ d 0 ∧
    (let deg := s.mem (d 1 + 5 * d 0 + d 2)
     let c := s.mem (d 1 + 8 * d 0 + deg)
     c ≠ 0 → linkSafe w ![d 0, d 1, d 2, c - 1]
       { s with mem := Function.update s.mem (d 1 + 8 * d 0 + deg) 0 })

private theorem realizes_scatterBody : Realizes .exact scatterBody (.refl _)
    (WordEncoding.encode (α := Option ℕ × ℕ)) scatterStepSafe (fun _ _ => 0) := by
  have hLink := realizes_link.reindex
    (fun d : Fin 5 → ℕ => ![d 0, d 1, d 2, d 3]) (.refl _) ![0, 1, 2, 3]
    (by intro d i; fin_cases i <;> rfl)
  have hRet : Realizes .exact
      (fun d : (Fin 5 → ℕ) × ℕ => pure (some d.2, d.1 4))
      (appendWords (.refl _) (WordEncoding.encode (α := ℕ)))
      (WordEncoding.encode (α := Option ℕ × ℕ)) (fun w _ _ => Fits w 1) (fun _ _ => 0) := by
    realize
    exact h
  have hNext := (hLink.bind₀ hRet).reindex
    (fun d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => ![d.1.1.1.1, d.1.1.1.2, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) ![0, 1, 2, 3, 4]
    (by intro d i; fin_cases i <;> rfl)
  change Realizes .exact
    (fun d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => do
      let u ← DataStructure.link (E := Memory.spec 0)
        ((layout d.1.1.1.1 d.1.1.1.2).methods 0) (FibonacciHeap.link d.1.1.2 d.1.2)
      pure (some u, d.2))
    (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ))
    (WordEncoding.encode (α := Option ℕ × ℕ))
    (fun w d s => linkSafe w ![d.1.1.1.1, d.1.1.1.2, d.1.1.2, d.1.2] s ∧ Fits w 1)
    (fun _ _ => 0) at hNext
  unfold scatterBody
  realize
  all_goals try first
    | exact h.1.of_le (by have := h.2.1; have := h.2.2.1; omega)
    | exact h.2.2.2 (by assumption)
    | omega

/-- The original consolidation-table step, with all runtime root and maximum-degree words
faithfully retained. The link's local work and argument staging are charged by the shared rules. -/
theorem realizes_scatterStep : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (scatterStep (d 2, d 3)))
    (.refl _) (WordEncoding.encode (α := Option ℕ × ℕ)) scatterStepSafe (fun _ _ => 0) :=
  realizes_scatterBody.congr scatterBody_eq

private theorem scatterStep_progress {n sz w md : ℕ} {z : Fin n} {g : Cell → ℕ}
    {T : FHTree n} {slots : List (FHTree n)} (hfit : Fits w n)
    (h : Placing sz z (view n g) T slots md) :
    Record.wp (Cell.ok n) w (scatterStep (T.root.val, md)) (fun next g' _ =>
      next.1 = none ∨ ∃ (T' : FHTree n) (slots' : List (FHTree n)),
        next = (some T'.root.val, md) ∧ Placing sz z (view n g') T' slots' md ∧
        slots'.length < slots.length) g := by
  have hdn := h.deg_bounds.2
  have hdeg : g (.deg T.root) = T.deg := ValidSubtree.deg_root h.valid.1
  simp only [scatterStep, Record.wp_read_bind, hdeg, Cell.ok]
  refine ⟨T.root.isLt, by omega, ?_⟩
  rcases h.table.lookup (d := T.deg) (by omega) with ⟨h0, _⟩ | ⟨i, hi, hdi, hci, _, hno⟩
  · have h0' : g (.cons T.deg) = 0 := h0
    simp only [h0', ite_true, Record.wp_write_bind, Record.wp_pure, Cell.ok]
    exact ⟨⟨by omega, hfit.of_le T.root.isLt⟩, Or.inl trivial⟩
  · have hci' : g (.cons T.deg) = slots[i].root.val + 1 := hci
    simp only [hci', Nat.add_one_ne_zero, ite_false, Record.wp_write_bind, Nat.add_sub_cancel,
      Cell.ok]
    refine ⟨⟨by omega, fits_zero w⟩, ?_⟩
    rw [Record.wp_bind]
    obtain ⟨hT, hS, hnd, hnext⟩ := h.collide hi hdi hno (view_update_cons g 0 T.deg)
    refine wp_link hT hS hnd hdi.symm (by omega) hfit fun g' _ T' _ hl => ?_
    simp only [Record.wp_pure]
    refine Or.inr ⟨T', slots.eraseIdx i, rfl, (hnext hl).1, ?_⟩
    rw [List.length_eraseIdx_of_lt hi]
    omega

/-- The actual source placement supplies the degree-table bound and both roots' native link
conditions after the slot is cleared. -/
theorem scatterStepSafe_of_placing {n sz w base md : ℕ} {z : Fin n}
    {mem : Memory.State} {T : FHTree n} {slots : List (FHTree n)}
    (hfit : Fits w (base + (9 * n + 5)))
    (h : Placing sz z (view n ((layout n base).abs mem)) T slots md) :
    scatterStepSafe w ![n, base, T.root.val, md] mem := by
  have hdn := h.deg_bounds.2
  have hdeg : mem.mem (base + 5 * n + T.root.val) = T.deg := by
    have hd := ValidSubtree.deg_root h.valid.1
    simpa only [view, Record.Layout.abs, Cell.ok, T.root.isLt, ite_true, layout,
      FHTree.deg] using hd
  change Fits w (base + (9 * n + 5)) ∧ T.root.val < n ∧
    mem.mem (base + 5 * n + T.root.val) ≤ n ∧ _
  refine ⟨hfit, T.root.isLt, by omega, ?_⟩
  change mem.mem (base + 8 * n + mem.mem (base + 5 * n + T.root.val)) ≠ 0 →
    linkSafe w ![n, base, T.root.val,
      mem.mem (base + 8 * n + mem.mem (base + 5 * n + T.root.val)) - 1]
      ⟨Function.update mem.mem (base + 8 * n + mem.mem (base + 5 * n + T.root.val)) 0,
        mem.frontier⟩
  rw [hdeg]
  intro hc
  rcases h.table.lookup (d := T.deg) (by omega) with ⟨h0, _⟩ | ⟨i, hi, hdi, hci, _, hno⟩
  · have h0' : mem.mem (base + 8 * n + T.deg) = 0 := by
      simpa only [view, Record.Layout.abs, Cell.ok, show T.deg ≤ n by omega,
        ite_true, layout] using h0
    exact (hc h0').elim
  · have hci' : mem.mem (base + 8 * n + T.deg) = slots[i].root.val + 1 := by
      simpa only [view, Record.Layout.abs, Cell.ok, show T.deg ≤ n by omega,
        ite_true, layout] using hci
    rw [hci', Nat.add_sub_cancel]
    let clear : Memory.State :=
      ⟨Function.update mem.mem (base + 8 * n + T.deg) 0, mem.frontier⟩
    have ha := (layout n base).abs_write (m := mem) (i := .cons T.deg)
      (by change T.deg ≤ n; omega) 0
    let old := view n ((layout n base).abs mem)
    have hv : view n ((layout n base).abs clear) =
        { old with cons := Function.update old.cons T.deg 0 } := by
      change view n ((layout n base).abs
        ⟨Function.update mem.mem ((layout n base).addr (.cons T.deg)) 0, mem.frontier⟩) = _
      rw [ha, view_update_cons]
    obtain ⟨hT, hS, _, _⟩ := h.collide hi hdi hno hv
    exact linkSafe_of_validRoots hfit hT hS

private theorem scatter_whileSafe {n sz w base : ℕ} {z : Fin n}
    (hfit : Fits w (base + (9 * n + 5))) :
    ∀ (fuel : ℕ) {mem : Memory.State} {T : FHTree n} {slots : List (FHTree n)} {md : ℕ},
      (layout n base).Inv mem → Placing sz z (view n ((layout n base).abs mem)) T slots md →
      slots.length < fuel →
      whileSafe (fun (_ : Unit) (a : Option ℕ × ℕ) => optionWords a.1 0 ≠ 0)
        (fun a : Unit × (Option ℕ × ℕ) => DataStructure.link (E := Memory.spec 0)
          ((layout n base).methods 0) (scatterStep (optionWords a.2.1 1, a.2.2)))
        (fun w a mem => scatterStepSafe w ![n, base, optionWords a.2.1 1, a.2.2] mem)
        w () fuel (some T.root.val, md) mem
  | 0, _, _, _, _, _, _, hfuel => absurd hfuel (Nat.not_lt_zero _)
  | fuel + 1, mem, T, slots, md, halloc, h, hfuel => by
    have hsafe := scatterStepSafe_of_placing hfit h
    have hprog := scatterStep_progress (hfit.of_le (by omega)) h
    obtain ⟨hrec, hpost⟩ := (Record.wp_iff _ _ _).mp hprog
    obtain ⟨_, hres, habs, hi'⟩ :=
      (Record.refinement (layout n base) w).simulates_client (scatterStep (T.root.val, md))
        halloc hrec
    dsimp only [Record.refinement] at hres habs hi'
    rw [clientResult_width w, link_width (w := w)] at hres
    rw [clientState_width w, link_width (w := w)] at habs hi'
    rw [← hres, ← habs] at hpost
    change scatterStepSafe w ![n, base, T.root.val, md] mem ∧ _
    refine ⟨hsafe, ?_⟩
    simp only [optionWords_some, Matrix.cons_val_one, Matrix.cons_val_zero]
    rcases hpost with hn | ⟨T', slots', hn, h', hlen⟩
    · cases fuel <;> simp [whileSafe, hn, optionWords_none]
    · rw [hn]
      exact scatter_whileSafe hfit fuel hi' h' (by omega)

/-- The native consolidation loop's domain: all reached body conditions hold and no active
root is discarded by the original finite cutoff. The degree accumulator remains a runtime word. -/
@[expose] def scatterSafe (w : ℕ) (d : Fin 4 → ℕ) (mem : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧
    whileSafe (fun (_ : Unit) (a : Option ℕ × ℕ) => optionWords a.1 0 ≠ 0)
      (fun a : Unit × (Option ℕ × ℕ) => DataStructure.link (E := Memory.spec 0)
        ((layout (d 0) (d 1)).methods 0) (scatterStep (optionWords a.2.1 1, a.2.2)))
      (fun w a mem => scatterStepSafe w ![d 0, d 1, optionWords a.2.1 1, a.2.2] mem)
      w () (d 0 + 1) (some (d 2), d 3) mem

/-- The original placement invariant supplies the native loop domain. Each collision removes
one table tree, so the original capacity cutoff suffices; no slot count is executed natively. -/
theorem scatterSafe_of_placing {n sz w base md : ℕ} {z : Fin n}
    {mem : Memory.State} {T : FHTree n} {slots : List (FHTree n)}
    (hfit : Fits w (base + (9 * n + 5))) (halloc : (layout n base).Inv mem)
    (h : Placing sz z (view n ((layout n base).abs mem)) T slots md) :
    scatterSafe w ![n, base, T.root.val, md] mem := by
  exact ⟨hfit, T.root.isLt, scatter_whileSafe hfit (n + 1) halloc h (by
    have := h.length_lt
    omega)⟩

/-- One uniform native emitter for the complete original consolidation recursion. It preserves
both the linked memory source and its returned maximum degree, using the shared while rule. -/
theorem realizes_scatter : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (scatter (d 0 + 1) (d 2) (d 3)))
    (.refl _) (WordEncoding.encode (α := ℕ)) scatterSafe (fun _ _ => 0) := by
  have hStep := realizes_scatterStep.reindex
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => ![d.1.1.1, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) ![0, 1, 2, 3]
    (by intro d i; fin_cases i <;> rfl)
  change Realizes .exact
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout d.1.1.1 d.1.1.2).methods 0) (scatterStep (d.1.2, d.2)))
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
    (WordEncoding.encode (α := Option ℕ × ℕ))
    (fun w d mem => scatterStepSafe w ![d.1.1.1, d.1.1.2, d.1.2, d.2] mem)
    (fun _ _ => 0) at hStep
  conv =>
    arg 2
    ext d
    rw [link_scatter_eq_boundedWhile]
  realize
  all_goals first
    | exact h.1.of_le (by omega)
    | exact fun _ => h.2.2

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
