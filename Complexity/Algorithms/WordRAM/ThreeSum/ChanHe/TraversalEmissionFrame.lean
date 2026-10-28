/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalInvariant
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalEmission

/-!
# Retained memory and pending children after a native emission

The actual pointer-table store is below the fresh heap and outside every live input block.
These frame lemmas retain old arrays and controller parameters, and identify the three actual
compact heavy buffers with the existing finite recursion's children.

## Main results

* `Emission.controls`, `Emission.loaded`: retained caller registers and current entry.
* `Emission.stored`: preservation of any live array around the reserved gap.
* `Emission.children_tasks`: the exact ordered mathematical worklist after child pushes.

These memory-frame and representation proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- An actual emission preserves each old-prefix cell except its one explicit table store. -/
theorem Emission.prefix_preserved {Q : Finset ℕ} {Λ : ℕ} {e : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y) (p : ℕ) (hp : p < x.regs heap)
    (hne : p ≠ x.regs outputs + x.regs outputCount) : y.mem p = x.mem p := by
  rw [h.memory, Function.update_of_ne hne]
  exact h.prefixMemory p hp

/-- All persistent caller parameters survive the actual complete visit. -/
theorem Emission.controls {Q : Finset ℕ} {Λ : ℕ} {e : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y) {a : Arena} (hc : a.Controls x) : a.Controls y := by
  apply hc.congr
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  apply h.registers i <;>
    first | omega | (intro he; have := congrArg Fin.val he; norm_num at this; omega)

/-- The current root record survives the visit until the actual child-preparation instructions. -/
theorem Emission.loaded {Q : Finset ℕ} {Λ : ℕ} {e : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y) (hl : e.Loaded x) : e.Loaded y := by
  have hs (i : Fin 7) : y.regs (slot i) = x.regs (slot i) := by
    apply h.registers <;>
      first | (dsimp [slot]; omega) |
        (intro he; have := congrArg Fin.val he; dsimp [slot] at this; omega)
  refine ⟨(hs 0).trans hl.1, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact (hs 1).trans (hl.2.1 0)
    · exact (hs 3).trans (hl.2.1 1)
    · exact (hs 5).trans (hl.2.1 2)
  · intro j
    fin_cases j
    · exact (hs 2).trans (hl.2.2 0)
    · exact (hs 4).trans (hl.2.2 1)
    · exact (hs 6).trans (hl.2.2 2)

/-- Old input columns below the stack or above the output table cannot be overwritten by the
single native pointer store, and both actual kernels preserve the old prefix. -/
theorem Emission.stored {Q : Finset ℕ} {Λ : ℕ} {e d : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y) {a : Arena} (ha : a.Separated) (hc : a.Controls x)
    (hs : d.Stored x.mem) (hg : d.Around a.stack (a.floor - a.stack))
    (hend : ∀ j, d.source j + (d.data j).length ≤ x.regs heap)
    (htable : x.regs outputs + x.regs outputCount < a.floor) : d.Stored y.mem := by
  apply hs.congr
  intro j i hi
  apply h.prefix_preserved _ (by have := hend j; omega)
  have ht : x.regs outputs = a.table := hc.2.2.2.2.2.2.1
  have hstack := ha.2.1
  have hfloor := ha.2.2.1
  rcases hg j with hj | hj <;> omega

/-- Top-first native child entries with the three actual compact heavy buffers. -/
def Emission.children {Q : Finset ℕ} {Λ : ℕ} {e : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y) : List Entry :=
  [e.child 0 ((recordLayout x h.M).heavy 0) (h.lists 0),
    e.child 1 ((recordLayout x h.M).heavy 1) (h.lists 1),
    e.child 2 ((recordLayout x h.M).heavy 2) (h.lists 2)]

/-- Actual heavy-buffer readback represents exactly the existing ordered three-child recursion. -/
theorem Emission.children_tasks {Q : Finset ℕ} {Λ : ℕ} {e : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y) :
    h.children.map Entry.task = e.task.children Q Λ (e.fuel - 1) := by
  simp only [Emission.children, List.map_cons, List.map_nil]
  apply e.task_children Q Λ (recordLayout x h.M).heavy h.lists
  intro j
  rw [h.sets j, h.exactModulus]

/-- Each of the actual three heavy-child arrays retains the existing admissibility promises. -/
theorem Emission.children_valid {Q : Finset ℕ} {Λ n U : ℕ} {e : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y) (hv : e.Valid n U) : ∀ d ∈ h.children, d.Valid n U := by
  intro d hd
  have hc (j : Fin 3) :
      (e.child j ((recordLayout x h.M).heavy j) (h.lists j)).Valid n U := by
    apply hv.child j _ _ (h.nodup j)
    rw [h.sets j]
    exact Cslib.Algorithms.ThreeSum.ChanHe.heavy_subset _ _
  simp only [Emission.children, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact hc 0
  · exact hc 1
  · exact hc 2

/-- Each child reuses the two surviving original columns and one actual compact heavy buffer. -/
theorem Emission.children_stored {Q : Finset ℕ} {Λ : ℕ} {e : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y) (hs : e.Stored y.mem) : ∀ d ∈ h.children, d.Stored y.mem := by
  intro d hd
  have hc (j : Fin 3) := hs.child j ((recordLayout x h.M).heavy j) (h.lists j) (h.heavy j)
  simp only [Emission.children, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact hc 0
  · exact hc 1
  · exact hc 2

/-- The actual heap pointer advances past the old frontier. -/
theorem Emission.heap_mono {Q : Finset ℕ} {Λ : ℕ} {e : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y) : x.regs heap ≤ y.regs heap := by
  rw [h.heap_eq, recordLayout_endpoint]
  omega

/-- Every actual child column lies below the advanced native allocation frontier. -/
theorem Emission.children_ends {Q : Finset ℕ} {Λ : ℕ} {e : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y) (hl : e.Loaded x)
    (hend : ∀ j, e.source j + (e.data j).length ≤ x.regs heap) :
    ∀ d ∈ h.children, ∀ k, d.source k + (d.data k).length ≤ y.regs heap := by
  have hpacked : (recordLayout x h.M).packed ≤ (recordLayout x h.M).endpoint := by
    dsimp only [NodePacking.Layout.endpoint, NodePacking.Layout.hist, NodePacking.Layout.scratch]
    omega
  have heavyEnd (j : Fin 3) :
      (recordLayout x h.M).heavy j + (h.lists j).length ≤ y.regs heap := by
    rw [h.heap_eq]
    calc (recordLayout x h.M).heavy j + (h.lists j).length
        ≤ (recordLayout x h.M).heavy j + (recordLayout x h.M).n j := by
          apply Nat.add_le_add_left
          simpa only [recordLayout, hl.2.2] using h.length_le j
      _ ≤ (recordLayout x h.M).packed := (recordLayout x h.M).heavy_end_le_packed j
      _ ≤ (recordLayout x h.M).endpoint := hpacked
  have hc (j k : Fin 3) :
      (e.child j ((recordLayout x h.M).heavy j) (h.lists j)).source k +
        ((e.child j ((recordLayout x h.M).heavy j) (h.lists j)).data k).length ≤
          y.regs heap := by
    by_cases he : k = j
    · subst k
      simpa only [Entry.child, Function.update_self] using heavyEnd j
    · simpa only [Entry.child, Function.update_of_ne he] using (hend k).trans h.heap_mono
  intro d hd k
  simp only [Emission.children, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact hc 0 k
  · exact hc 1 k
  · exact hc 2 k

/-- Every new heavy child begins above the reserved stack/table gap. -/
theorem Emission.children_around {Q : Finset ℕ} {Λ : ℕ} {e : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y) {base capacity : ℕ} (hg : e.Around base capacity)
    (hfloor : base + capacity ≤ x.regs heap) :
    ∀ d ∈ h.children, d.Around base capacity := by
  have hc (j : Fin 3) :
      (e.child j ((recordLayout x h.M).heavy j) (h.lists j)).Around base capacity := by
    apply hg.child
    have hb := (recordLayout x h.M).base_le_descriptor j
    change x.regs heap ≤ (recordLayout x h.M).descriptor j at hb
    dsimp only [NodePacking.Layout.heavy]
    omega
  intro d hd
  simp only [Emission.children, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact hc 0
  · exact hc 1
  · exact hc 2

/-- The exact native words prepared for the three pushes are the new semantic child records. -/
theorem Emission.children_words {Q : Finset ℕ} {Λ : ℕ} {e : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y) (hl : e.Loaded x) :
    childWords y 0 ++ childWords y 1 ++ childWords y 2 = h.children.flatMap Entry.words := by
  rw [Entry.child_words (h.loaded hl) _ _ h.bases h.lengths 0,
    Entry.child_words (h.loaded hl) _ _ h.bases h.lengths 1,
    Entry.child_words (h.loaded hl) _ _ h.bases h.lengths 2]
  simp only [Emission.children, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]

/-- The complete visit retains the actual pending stack, including its native pointer and
length registers; its sole external memory store lies above the stack reservation. -/
theorem Emission.stack {Q : Finset ℕ} {Λ w : ℕ} {e : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y) {a : Arena} (ha : a.Separated) (hc : a.Controls x)
    (hy : y.Bounded w) (vs : List ℕ)
    (hr : Stack.Rep w a.stack a.capacity vs (x.comap Traversal.registers))
    (htable : x.regs outputs + x.regs outputCount < x.regs heap) :
    Stack.Rep w a.stack a.capacity vs (y.comap Traversal.registers) := by
  have hregs (i : Fin 9) : y.regs (Traversal.registers i) = x.regs (Traversal.registers i) := by
    apply h.registers <;>
      first | (dsimp [Traversal.registers]; omega) |
        (intro he; have := congrArg Fin.val he; dsimp [Traversal.registers] at this; omega)
  have ht : x.regs outputs = a.table := hc.2.2.2.2.2.2.1
  refine ⟨⟨fun i => hy.1 (Traversal.registers i), hy.2⟩, (hregs Stack.ptr).trans hr.pointer,
    (hregs Stack.len).trans hr.length_eq, hr.capacity_le, ?_⟩
  intro i
  have hi : i.val < a.capacity := lt_of_lt_of_le i.isLt hr.capacity_le
  change y.mem (a.stack + i.val) = _
  rw [h.prefix_preserved _ (by have := ha.2.1; omega)
    (by have := ha.2.1; omega)]
  exact hr.contents i

/-- Append the actual newly emitted packed pointer and array to the retained output sequence. -/
theorem Emission.output {Q : Finset ℕ} {Λ : ℕ} {e : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y) {a : Arena} (hc : a.Controls x)
    (ns : List (ℕ × Cslib.Algorithms.ThreeSum.ChanHe.Node))
    (hs : StoredNodes a.U a.N a.table ns x.mem)
    (hcount : x.regs outputCount = ns.length)
    (hbounds : ∀ i : Fin ns.length,
      a.floor ≤ ns[i.val].1 ∧ ns[i.val].1 + 4 * a.N ≤ x.regs heap)
    (htable : a.table + ns.length < a.floor) (hfloor : a.floor ≤ x.regs heap) :
    StoredNodes a.U a.N a.table
      (ns ++ [((recordLayout x h.M).packed, e.task.node Q Λ)]) y.mem := by
  have hU : x.regs magnitude = a.U := hc.2.2.1
  have hN : x.regs groups = a.N := hc.2.2.2.1
  have ht : x.regs outputs = a.table := hc.2.2.2.2.2.2.1
  have hpacked : x.regs heap ≤ (recordLayout x h.M).packed := by
    dsimp only [recordLayout, NodePacking.Layout.packed]
    omega
  have hbefore : StoredNodes a.U a.N a.table ns h.before := by
    apply hs.congr
    · intro p _ hp
      exact h.prefixMemory p (by omega)
    · intro i u hu
      exact h.prefixMemory _ (by have := (hbounds i).2; omega)
  have hnew : (Block.mk (recordLayout x h.M).packed (4 * a.N)).Realizes h.before
      (fun i => Signed.encode ((e.task.node Q Λ).oneArray a.U i.val)) := by
    intro i
    have hi : i.val < 4 * x.regs groups := by simpa only [hN] using i.isLt
    have hp := h.packed ⟨i.val, hi⟩
    change y.mem ((recordLayout x h.M).packed + i.val) = _ at hp
    rw [h.memory, Function.update_of_ne (show
      (recordLayout x h.M).packed + i.val ≠ x.regs outputs + x.regs outputCount by
        rw [ht, hcount]; omega)] at hp
    simpa only [Block.read, hU] using hp
  rw [h.memory, ht, hcount]
  exact hbefore.append hnew (by intro i; have := (hbounds i).1; omega) (by omega)

/-- For a live entry, the actual heavy children and emitted node are the exact finite step. -/
theorem Emission.math_step {Q : Finset ℕ} {Λ : ℕ} {e : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y) (es : List Entry) (hf : e.fuel ≠ 0)
    (hn : ∀ j, (e.data j).length ≠ 0) :
    Math.step Q Λ e.task (es.map Entry.task) =
      ((h.children ++ es).map Entry.task, some (e.task.node Q Λ)) := by
  have hempty : ¬e.task.empty := by
    simp only [Math.Task.empty, Entry.task, List.toFinset_eq_empty_iff]
    intro he
    rcases he with he | he | he
    · exact hn 0 (by rw [he]; rfl)
    · exact hn 1 (by rw [he]; rfl)
    · exact hn 2 (by rw [he]; rfl)
  rw [List.map_append, h.children_tasks]
  cases he : e.fuel with
  | zero => exact (hf he).elim
  | succ f =>
    simp only [Math.step, show e.task.fuel = f + 1 from he, hempty, ↓reduceIte,
      Nat.add_sub_cancel]

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
