/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.WordRAM.Realization.Product
public import Complexity.Computability.WordRAM.Realization.Primitive
public import Complexity.Computability.WordRAM.Realization.Bind
public import Complexity.Computability.WordRAM.Realization.GlueVector
public import Complexity.Computability.WordRAM.Realization.Reindex
public import Complexity.Computability.WordRAM.Realization.Program
public import ComplexityTests.DataStructureMemoryAlloc

/-!
# Native dispatch for two cells that grow in shared memory

These clients reuse the public write-once cell and allocator fixtures from
`DataStructureMemoryAlloc`. They do not introduce a second memory or framing model.
The input vectors contain every constant used by the native methods. Allocation, sequential
control and the sum dispatcher retain their separate charges.
-/

public section

namespace ComplexityTests.WordRAMRealizationProductGrowth

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open ComplexityTests.DataStructureMemoryAlloc

private abbrev wordWords : ℕ ↪ (Fin 1 → ℕ) :=
  (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

private abbrev unitWords : Unit ↪ (Fin 0 → ℕ) :=
  (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding

/-- Header, value, allocation count and a zero comparison word. -/
private def cellWords : ℕ × ℕ ↪ (Fin 4 → ℕ) where
  toFun := fun (h, v) => ![h, v, 1, 0]
  inj' := by
    intro a b hab
    exact Prod.ext (congrFun hab 0) (congrFun hab 1)

private abbrev allocatedWords := appendWords cellWords wordWords
private abbrev writtenWords := appendWords allocatedWords unitWords

-- The allocated address is a runtime answer. Both later stores consume it through the
-- existing bind environment; no host-side argument installation is granted.
private theorem cellSet_realizes :
    Realizes .exact (fun (h, v) => cellSet h v) cellWords unitWords
      (fun _ _ _ => True) (fun _ _ => 2) := by
  have ha : Realizes .exact (fun _ : ℕ × ℕ => allocDirty 1) cellWords wordWords
      (fun _ _ _ => True) (fun _ _ => 0) := Realizes.allocDirty cellWords 2
  have hw : Realizes .exact (fun ((_, v), p) => write p v) allocatedWords unitWords
      (fun _ _ _ => True) (fun _ _ => 0) := Realizes.write allocatedWords 4 1
  have hh : Realizes .exact (fun (((h, _), p), _) => write h p) writtenWords unitWords
      (fun _ _ _ => True) (fun _ _ => 0) := Realizes.write writtenWords 0 4
  have h := Realizes.bind ha (Realizes.bind hw hh)
  exact h.consequence (fun _ _ _ _ _ _ => ⟨trivial, trivial, trivial⟩)
    (fun _ _ => le_rfl)

/-- The branch tag is separate from the full component input. -/
private def sumWords : (ℕ × ℕ) ⊕ (ℕ × ℕ) ↪ (Fin 5 → ℕ) where
  toFun
    | .inl (h, v) => ![0, h, v, 1, 0]
    | .inr (h, v) => ![1, h, v, 1, 0]
  inj' := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Prod.ext (congrFun hab 1) (congrFun hab 2))
      | inr b => have h := congrFun hab 0; simp at h
    | inr a =>
      cases b with
      | inl b => have h := congrFun hab 0; simp at h
      | inr b => exact congrArg Sum.inr (Prod.ext (congrFun hab 1) (congrFun hab 2))

private def sumSet : (ℕ × ℕ) ⊕ (ℕ × ℕ) → Prog Unit :=
  Sum.elim (fun (h, v) => cellSet h v) (fun (h, v) => cellSet h v)

-- `eq` compares two runtime words: side zero takes the left branch, side one the right.
-- The same emitter handles both summands, and its four work units include both binds and
-- the two dispatcher units. The three memory operations are charged separately.
private theorem sumSet_realizes :
    Realizes .exact sumSet sumWords unitWords
      (fun _ _ _ => True) (fun _ _ => 4) := by
  have h := Realizes.sum cellSet_realizes cellSet_realizes sumWords
    ![1, 2, 3, 4] ![1, 2, 3, 4]
    (fun _ i => by fin_cases i <;> rfl)
    (fun _ i => by fin_cases i <;> rfl)
    (.eq 0 4) (fun _ => rfl) (by rintro ⟨h, v⟩; change 1 ≠ 0; decide)
  exact h.consequence (fun _ d _ _ _ _ => by cases d <;> trivial)
    (fun d _ => by cases d <;> exact le_rfl)

private def pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) where
  toFun := fun (a, b) => ![a, b]
  inj' := by
    intro a b hab
    exact Prod.ext (congrFun hab 0) (congrFun hab 1)

private abbrev firstHeaderWords := appendWords cellWords wordWords
private abbrev bothHeaderWords := appendWords firstHeaderWords wordWords

-- Allocating both headers also pays for returning their two-word handle. Both allocations
-- consume the explicit count word; no count or handle is installed by an uncharged prepare.
private theorem allocate_realizes :
    Realizes .exact (fun _ : ℕ × ℕ => cells.alloc) cellWords pairWords
      (fun _ _ _ => True) (fun _ _ => 6) := by
  have hfirst : Realizes .exact (fun _ : ℕ × ℕ => allocDirty 1) cellWords wordWords
      (fun _ _ _ => True) (fun _ _ => 0) := Realizes.allocDirty cellWords 2
  have hsecond : Realizes .exact (fun _ : (ℕ × ℕ) × ℕ => allocDirty 1)
      firstHeaderWords wordWords (fun _ _ _ => True) (fun _ _ => 0) :=
    Realizes.allocDirty firstHeaderWords 2
  have hout : Realizes .exact (fun ((_, h₁), h₂) => pure (h₁, h₂)) bothHeaderWords pairWords
      (fun _ _ _ => True) (fun _ _ => 4) := by
    have h := Realizes.glueVector (B := .exact) bothHeaderWords pairWords
      (fun ((_, h₁), h₂) => (h₁, h₂))
      (fun i v => v (if i = 0 then 4 else 5))
      (fun i v => v (if i = 0 then 4 else 5)) (fun _ => 1)
      (P := fun _ => True)
      (fun _ i => by fin_cases i <;> rfl)
      (fun i => GlueComputes.proj (if i = 0 then 4 else 5) (fun _ _ => le_rfl))
    exact h.consequence (fun _ _ _ hw _ _ => ⟨trivial, fun i => hw _⟩)
      (fun _ _ => by decide)
  have h := Realizes.bind hfirst (Realizes.bind hsecond hout)
  exact h.consequence (fun _ _ _ _ _ _ => ⟨trivial, trivial, trivial⟩)
    (fun _ _ => le_rfl)

private abbrev productWords := appendWords cellWords pairWords
private abbrev afterLeftWords := appendWords productWords unitWords

private def allocatedSets : ℕ × ℕ → Prog Unit := fun (a, b) => cells.run (do
  let _ ← (product (Cell 8) (Cell 8)).call (.inl (.set a))
  (product (Cell 8) (Cell 8)).call (.inr (.set b)))

-- The two method calls use the actual allocated headers through static register routes.
-- Their tags come from the input's existing zero/one words, not host-side computation.
private theorem allocatedSets_realizes :
    Realizes .exact allocatedSets
      cellWords unitWords (fun _ _ _ => True) (fun _ _ => 16) := by
  have hl := sumSet_realizes.reindex
    (fun ((a, _), (h₁, _)) => Sum.inl (h₁, a)) productWords ![3, 4, 0, 2, 3]
    (fun _ i => by fin_cases i <;> rfl)
  have hr := sumSet_realizes.reindex
    (fun (((_, b), (_, h₂)), _) => Sum.inr (h₂, b)) afterLeftWords ![2, 5, 1, 2, 3]
    (fun _ i => by fin_cases i <;> rfl)
  have h := Realizes.bind allocate_realizes (Realizes.bind hl hr)
  exact h.consequence (fun _ _ _ _ _ _ => ⟨trivial, trivial, trivial⟩)
    (fun _ _ => le_rfl)

/-- A live memory sentinel lies below the allocation frontier, outside all future cell storage. -/
private def initial : State := ⟨fun a => if a = 0 then 9 else 0, 1⟩

private theorem initial_pre : cells.Pre initial := by
  apply pre
  intro a ha
  have hne : a ≠ 0 := by change 1 ≤ a at ha; omega
  simp only [initial, hne, ↓reduceIte]

private theorem initial_fits : Fits 8 (initial.frontier + cells.room) := by decide

private abbrev productFrame := cells.framed initial initial_pre initial_fits

private def afterSetup : State := (spec 8).clientState initial (cells.run (pure ()))
private def afterLeft : State := (spec 8).clientState initial (cells.run setLeft)
private def afterBoth : State := (spec 8).clientState initial (cells.run setBoth)

/-- The imported cell method's actual three-query history is charged, including its allocation. -/
theorem cellSet_memory_cost (h v : ℕ) (s : State) : memoryCost (cellSet h v) s = 3 := rfl

private def installed {r : ℕ} (s : State) (values : ℕ × ℕ) (marker : ℕ) : Data r :=
  ⟨fun j => if j.val = 0 then s.frontier else if j.val = 1 then values.1
    else if j.val = 2 then values.2 else if j.val = 3 then 1
    else if j.val = 5 then marker else 0, s.mem⟩

-- The native body, scratch size and exchange constant precede ALL runtime cases. Its semantic
-- postcondition is literal whole-memory equality, while the register frame retains the marker.
private theorem allocatedSets_native :
    ∃ n C, ∃ code : Code .exact (6 + (0 + n + 1)),
      ∀ (w : ℕ) (values : ℕ × ℕ) (s : State) (marker : ℕ),
        WellFormed w s → (∀ i, Fits w (cellWords values i)) → Fits w marker →
        (spec w).ValidHistory s ((spec w).clientHistory s (allocatedSets values)) →
        ∃ y, ExecWithin w code (installed s values marker) y
            (C * (memoryCost (allocatedSets values) s + 17)) ∧
          memoryState ⟨0, by omega⟩ y = (spec w).clientState s (allocatedSets values) ∧
          y.regs ⟨5, by omega⟩ = marker ∧
          ∀ i : Fin 4, y.regs ⟨1 + i.val, by omega⟩ = cellWords values i := by
  obtain ⟨n, C, emit, he⟩ := allocatedSets_realizes
  let f : Fin (6 + (0 + n + 1)) := ⟨0, by omega⟩
  let src : Fin 4 → Fin (6 + (0 + n + 1)) := fun i => ⟨1 + i.val, by omega⟩
  let tmp : Fin (0 + n + 1) → Fin (6 + (0 + n + 1)) := Fin.natAdd 6
  have hi : Function.Injective tmp := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    change 6 + a.val = 6 + b.val at h
    omega
  have hd (i : Fin 4) (j : Fin (0 + n + 1)) : src i ≠ tmp j := by
    intro h
    have hv := congrArg Fin.val h
    change 1 + i.val = 6 + j.val at hv
    omega
  have htf (j : Fin (0 + n + 1)) : tmp j ≠ f := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + j.val = 0 at hv
    omega
  have hsf (i : Fin 4) : src i ≠ f := by
    intro h
    have hv := congrArg Fin.val h
    change 1 + i.val = 0 at hv
    omega
  refine ⟨n, C, emit f src tmp, ?_⟩
  intro w values s marker hs hw hmark hv
  let x : Data (6 + (0 + n + 1)) := installed s values marker
  have hx : x.Bounded w := by
    refine ⟨fun j => ?_, hs.2⟩
    change Fits w (if j.val = 0 then s.frontier else if j.val = 1 then values.1
      else if j.val = 2 then values.2 else if j.val = 3 then 1
      else if j.val = 5 then marker else 0)
    split_ifs
    · exact hs.1
    · exact hw 0
    · exact hw 1
    · exact hw 2
    · exact hmark
    · exact fits_zero w
  have hin : x.regs ∘ src = cellWords values := by
    funext i
    fin_cases i <;> rfl
  have hxs : memoryState f x = s := rfl
  obtain ⟨y, hy, hm, _, hframe⟩ :=
    (he f src tmp hi hd htf hsf).2 w values x hx hin trivial (hxs.symm ▸ hv)
  have hmarker := hframe ⟨5, by omega⟩
    (by intro h; have hv := congrArg Fin.val h; change 5 = 0 at hv; omega)
    (fun j h => by have hv := congrArg Fin.val h; change 6 + j.val = 5 at hv; omega)
  rw [hxs] at hy hm
  refine ⟨y, hy, hm, hmarker, ?_⟩
  intro i
  exact (hframe (src i) (hsf i) (fun j => (hd i j).symm)).trans (congrFun hin i)

-- Both allocations, both dynamically allocating sets and their bounds are nonvacuous.
example : memoryCost (allocatedSets (5, 7)) initial = 8 := by decide

example : (spec 8).ValidHistory initial
    ((spec 8).clientHistory initial (allocatedSets (5, 7))) := by decide

example : (spec 8).ValidHistory initial
    ((spec 8).clientHistory initial (allocatedSets (0, 255))) := by decide

-- One actual body is reused for two sets of runtime values and two widths. Both executions
-- preserve the entire semantic memory, and the unrelated live register keeps its own value.
example : ∃ n C, ∃ code : Code .exact (6 + (0 + n + 1)), ∃ y₁ y₂,
    ExecWithin 8 code (installed initial (5, 7) 11) y₁ (C * 25) ∧
    ExecWithin 9 code (installed initial (0, 255) 12) y₂ (C * 25) ∧
    memoryState ⟨0, by omega⟩ y₁ = afterBoth ∧
    memoryState ⟨0, by omega⟩ y₂ = (spec 9).clientState initial (allocatedSets (0, 255)) ∧
    y₁.regs ⟨5, by omega⟩ = 11 ∧ y₂.regs ⟨5, by omega⟩ = 12 ∧
    y₁.mem 0 = 9 ∧ y₂.mem 0 = 9 := by
  obtain ⟨n, C, code, hrun⟩ := allocatedSets_native
  have hs (w : ℕ) (h9 : Fits w 9) (h1 : Fits w 1) : WellFormed w initial := by
    refine ⟨h1, fun a => ?_⟩
    change Fits w (if a = 0 then 9 else 0)
    split_ifs
    · exact h9
    · exact fits_zero w
  obtain ⟨y₁, hy₁, hm₁, hmarker₁, _⟩ := hrun 8 (5, 7) initial 11
    (hs 8 (by decide) (by decide)) (by decide) (by decide) (by decide)
  obtain ⟨y₂, hy₂, hm₂, hmarker₂, _⟩ := hrun 9 (0, 255) initial 12
    (hs 9 (by decide) (by decide)) (by decide) (by decide) (by decide)
  have hc₁ : memoryCost (allocatedSets (5, 7)) initial = 8 := by decide
  have hc₂ : memoryCost (allocatedSets (0, 255)) initial = 8 := by decide
  rw [hc₁] at hy₁
  rw [hc₂] at hy₂
  have hmem₁ := congrArg State.mem hm₁
  have hmem₂ := congrArg State.mem hm₂
  refine ⟨n, C, code, y₁, y₂, hy₁, hy₂, hm₁, hm₂, hmarker₁, hmarker₂, ?_, ?_⟩
  · exact (congrFun hmem₁ 0).trans (by decide)
  · exact (congrFun hmem₂ 0).trans (by decide)

private def raw : ℕ × ℕ → List ℕ := fun (a, b) => [a, b, 1, 0]

-- Standard raw-list inputs execute the existing paid prefix, not the preinstalled register
-- fixture above. The output-zero write and trailing halt are charged by the Unit projection.
private theorem allocatedSets_from_init : ∃ (r C : ℕ) (program : Program .exact r),
    ∀ (w : ℕ) (values : ℕ × ℕ), InputFits w (raw values) → Fits w 5 →
      (spec w).ValidHistory (inputState (raw values))
        ((spec w).clientHistory (inputState (raw values)) (allocatedSets values)) →
      ∃ t, Executes w program (Cslib.WordRAM.State.init (raw values)) 0 t ∧
        t ≤ C * (memoryCost (allocatedSets values) (inputState (raw values)) + 17) + 2 := by
  obtain ⟨n, C, emit, he⟩ := allocatedSets_realizes.exists_init_unit_program raw
    (fun _ i => by fin_cases i <;> rfl)
  let r := 6 + (0 + n + 1)
  let f : Fin r := ⟨0, by dsimp [r]; omega⟩
  let src : Fin 4 → Fin r := fun i => ⟨1 + i.val, by dsimp [r]; omega⟩
  let tmp : Fin (0 + n + 1) → Fin r := Fin.natAdd 6
  have hsrc : Function.Injective src := by
    intro a b h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change 1 + a.val = 1 + b.val at hv
    omega
  have hi : Function.Injective tmp := by
    intro a b h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change 6 + a.val = 6 + b.val at hv
    omega
  have hd (i : Fin 4) (j : Fin (0 + n + 1)) : src i ≠ tmp j := by
    intro h
    have hv := congrArg Fin.val h
    change 1 + i.val = 6 + j.val at hv
    omega
  have hf (j : Fin (0 + n + 1)) : tmp j ≠ f := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + j.val = 0 at hv
    omega
  have hs (i : Fin 4) : src i ≠ f := by
    intro h
    have hv := congrArg Fin.val h
    change 1 + i.val = 0 at hv
    omega
  refine ⟨r, C, (Code.seq (inputPrefix f (tmp (Fin.last (0 + n))) src)
    (.seq (emit f src tmp) (.op (.const (tmp 0) 0)))).program (tmp 0), ?_⟩
  intro w values hin hfit hv
  obtain ⟨t, ht, htime⟩ := he f src tmp hsrc hi hd hf hs w values
    (by rcases values with ⟨a, b⟩; change 4 ≤ 4; omega) (by simpa only [raw, List.length_cons,
      List.length_nil] using hfit) hin trivial hv
  exact ⟨t, ht, htime⟩

-- The paid raw-input program has a checked, admissible instance with four fresh cells of room.
example : ∃ (r C : ℕ) (program : Program .exact r) (t : ℕ),
    Executes 8 program (Cslib.WordRAM.State.init [5, 7, 1, 0]) 0 t ∧ t ≤ C * 25 + 2 := by
  obtain ⟨r, C, program, hrun⟩ := allocatedSets_from_init
  obtain ⟨t, ht, htime⟩ := hrun 8 (5, 7) (by decide) (by decide) (by decide)
  exact ⟨r, C, program, t, ht, htime⟩

private abbrev sharedFrame := (cellFramed 1 8).prod (cellFramed 2 8)
private def reserved : Block := ⟨1, 4⟩

private theorem shared_inv_setup : sharedFrame.inv afterSetup :=
  (cells.allocates initial initial_pre initial_fits).inv

private theorem shared_inv_left : sharedFrame.inv afterLeft := by
  obtain ⟨_, _, hinv, _⟩ := cells.run_correct setLeft initial_pre initial_fits
    ⟨⟨rfl, by decide⟩, trivial⟩
  exact hinv

private theorem setup_footprint : ∀ a ∈ sharedFrame.footprint afterSetup,
    a ∈ reserved.footprint := by
  intro a ha
  change a ∈ ({1} ∪ {2} : Finset ℕ) at ha
  simp only [Finset.mem_union, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl <;> decide

private theorem left_footprint : ∀ a ∈ sharedFrame.footprint afterLeft,
    a ∈ reserved.footprint := by
  intro a ha
  change a ∈ ({1, 3} ∪ {2} : Finset ℕ) at ha
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with (rfl | rfl) | rfl <;> decide

private theorem setup_room (a : ℕ) (hl : afterSetup.frontier ≤ a)
    (hu : a < afterSetup.frontier + sharedFrame.room afterSetup) :
    a ∈ reserved.footprint := by
  apply Block.mem_footprint.mpr
  change 1 ≤ a ∧ a < 1 + 4
  change 3 ≤ a at hl
  change a < 3 + 2 at hu
  omega

private theorem left_room (a : ℕ) (hl : afterLeft.frontier ≤ a)
    (hu : a < afterLeft.frontier + sharedFrame.room afterLeft) :
    a ∈ reserved.footprint := by
  apply Block.mem_footprint.mpr
  change 1 ≤ a ∧ a < 1 + 4
  change 4 ≤ a at hl
  change a < 4 + 1 at hu
  omega

-- These native/frame clients select the SAME certificate emitter. Each explicit source
-- equation identifies a real product method. The region includes the headers AND all future
-- allocation room; containing only the current footprint would not discharge the theorem.
example {r : ℕ} (f : Fin r) (src : Fin 5 → Fin r)
    (tmp : Fin (0 + sumSet_realizes.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ f) (hs : ∀ i, src i ≠ f)
    (x : Data r) (hx : x.Bounded 8) (hin : x.regs ∘ src = sumWords (.inl (1, 5)))
    (hstate : memoryState f x = afterSetup) :
    ∃ y, ExecWithin 8 (sumSet_realizes.code f src tmp) x y (sumSet_realizes.factor * 8) ∧
      memoryState f y = afterLeft ∧ Modifies reserved.footprint x.mem y.mem ∧
      sharedFrame.footprint (memoryState f y) ⊆ reserved.footprint ∧
      (memoryState f y).frontier + sharedFrame.room (memoryState f y) ≤ 5 ∧
      y.mem 0 = 9 := by
  have hsource : (sumSet (.inl (1, 5))).bind pure = sharedFrame.methods (.inl (.set 5)) := by
    change (cellSet 1 5).bind pure = cellSet 1 5
    exact bind_pure (m := Prog) (cellSet 1 5)
  obtain ⟨y, hy, hm, _, _, hmod, hfp, hroom, _, _⟩ :=
    sumSet_realizes.product_exec (cellFramed 1 8) (cellFramed 2 8) f src tmp hi hd hf hs
      (.inl (1, 5)) x (.inl (.set 5)) id hsource hx hin trivial
      (hstate.symm ▸ shared_inv_setup) (by rw [hstate]; decide) reserved
      (by simpa only [hstate] using setup_footprint)
      (by simpa only [hstate] using setup_room)
  rw [hstate] at hy hm hroom
  have hmem := congrArg State.mem hstate
  exact ⟨y, hy, hm, hmod, hfp, hroom,
    (hmod 0 (by decide)).trans ((congrFun hmem 0).trans (by decide))⟩

example {r : ℕ} (f : Fin r) (src : Fin 5 → Fin r)
    (tmp : Fin (0 + sumSet_realizes.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ f) (hs : ∀ i, src i ≠ f)
    (x : Data r) (hx : x.Bounded 8) (hin : x.regs ∘ src = sumWords (.inr (2, 7)))
    (hstate : memoryState f x = afterLeft) :
    ∃ y, ExecWithin 8 (sumSet_realizes.code f src tmp) x y (sumSet_realizes.factor * 8) ∧
      memoryState f y = afterBoth ∧ Modifies reserved.footprint x.mem y.mem ∧
      sharedFrame.footprint (memoryState f y) ⊆ reserved.footprint ∧
      (memoryState f y).frontier + sharedFrame.room (memoryState f y) ≤ 5 ∧
      y.mem 0 = 9 := by
  have hsource : (sumSet (.inr (2, 7))).bind pure = sharedFrame.methods (.inr (.set 7)) := by
    change (cellSet 2 7).bind pure = cellSet 2 7
    exact bind_pure (m := Prog) (cellSet 2 7)
  obtain ⟨y, hy, hm, _, _, hmod, hfp, hroom, _, _⟩ :=
    sumSet_realizes.product_exec (cellFramed 1 8) (cellFramed 2 8) f src tmp hi hd hf hs
      (.inr (2, 7)) x (.inr (.set 7)) id hsource hx hin trivial
      (hstate.symm ▸ shared_inv_left) (by rw [hstate]; decide) reserved
      (by simpa only [hstate] using left_footprint)
      (by simpa only [hstate] using left_room)
  rw [hstate] at hy hm hroom
  have hmem := congrArg State.mem hstate
  exact ⟨y, hy, hm, hmod, hfp, hroom,
    (hmod 0 (by decide)).trans ((congrFun hmem 0).trans (by decide))⟩

-- Shared room is consumed by actual allocation within each set; the unrelated sentinel remains.
example : productFrame.footprint afterSetup = {1, 2} ∧
    productFrame.abs afterSetup = (none, none) ∧ afterSetup.frontier = 3 ∧
    productFrame.room afterSetup = 2 ∧ afterSetup.mem 0 = 9 := by decide

example : productFrame.footprint afterLeft = {1, 3, 2} ∧
    productFrame.abs afterLeft = (some 5, none) ∧ afterLeft.frontier = 4 ∧
    productFrame.room afterLeft = 1 ∧ afterLeft.mem 0 = 9 := by decide

example : productFrame.footprint afterBoth = {1, 3, 2, 4} ∧
    productFrame.abs afterBoth = (some 5, some 7) ∧ afterBoth.frontier = 5 ∧
    productFrame.room afterBoth = 0 ∧ afterBoth.mem 0 = 9 := by decide

-- Reuse the allocator's complete shared-memory contract on this nonzero-sentinel input.
example : (spec 8).ValidHistory initial ((spec 8).clientHistory initial (cells.run client)) ∧
    (spec 8).clientResult initial (cells.run client) = (some 5, some 7) := by
  obtain ⟨hv, hr, _⟩ := cells.run_correct client initial_pre initial_fits client_valid
  exact ⟨hv, hr⟩

-- The existing eight-bit reservation boundary is retained, including failure of only the
-- second set one cell above the admitted frontier.
example : Fits 8 (high.frontier + cells.room) ∧ ¬Fits 8 (tooHigh.frontier + cells.room) := by
  decide

example : (spec 8).ValidHistory tooHigh ((spec 8).clientHistory tooHigh (cells.run setLeft)) ∧
    ¬(spec 8).ValidHistory tooHigh ((spec 8).clientHistory tooHigh (cells.run setBoth)) := by
  decide

-- A resident structure cannot be taken over twice: reuse the public stack-resident fixture.
example (s : State) : ¬((inputStack 0 (by decide) [7, 5]).prod
    (inputStack 0 (by decide) [7, 5])).Pre s := by
  intro hs
  have hd : Disjoint (layout 0).footprint (layout 0).footprint := Allocator.ProdPre.disjoint hs
  exact absurd hd (by decide)

private def residentState : State :=
  ⟨fun a => if a = 1 then 2 else if a = 2 then 5 else 0, 3⟩

private abbrev residentCell := Allocator.resident (cellFramed 1 8) (some 5) 0

-- The zero-allocation resident case has an actual satisfying precondition, not an assumed frame.
example : residentCell.Pre residentState := by
  refine ⟨⟨by decide, ?_, by decide⟩, by decide, by decide⟩
  intro _
  change 2 < 3
  decide

private theorem resident_pure_realizes :
    Realizes .exact (fun _ : Unit => residentCell.run (pure ())) unitWords unitWords
      (fun _ _ _ => True) (fun _ _ => 0) := by
  have h := Realizes.glueVector (B := .exact) unitWords unitWords (fun _ => ())
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (P := fun _ => True) (fun _ i => Fin.elim0 i) (fun i => Fin.elim0 i)
  exact h.consequence (fun _ _ _ _ _ _ => ⟨trivial, fun i => Fin.elim0 i⟩)
    (fun _ _ => le_rfl)

example : memoryCost (residentCell.run (pure ())) residentState = 0 := rfl

-- This is an already-resident ABI, not a claim to install a memory image for free.
-- Zero memory charge still leaves the generic native body allowance plus the real zero write
-- and halt. The preceding allocated client separately checks charged raw-list installation.
example : ∃ (r C : ℕ) (program : Program .exact r) (t : ℕ),
    Executes 8 program ⟨0, ⟨fun j => if j.val = 0 then 3 else 0, residentState.mem⟩⟩ 0 t ∧
      t ≤ C + 2 := by
  obtain ⟨n, C, emit, he⟩ := resident_pure_realizes.exists_unit_program
  let r := 1 + (0 + n + 1)
  let f : Fin r := ⟨0, by dsimp [r]; omega⟩
  let src : Fin 0 → Fin r := Fin.elim0
  let tmp : Fin (0 + n + 1) → Fin r := Fin.natAdd 1
  have hi : Function.Injective tmp := by
    intro a b h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change 1 + a.val = 1 + b.val at hv
    omega
  have hf (j : Fin (0 + n + 1)) : tmp j ≠ f := by
    intro h
    have hv := congrArg Fin.val h
    change 1 + j.val = 0 at hv
    omega
  let x : Data r := ⟨fun j => if j.val = 0 then 3 else 0, residentState.mem⟩
  have hx : x.Bounded 8 := by
    constructor
    · intro j
      change Fits 8 (if j.val = 0 then 3 else 0)
      split_ifs <;> decide
    · intro a
      change Fits 8 (if a = 1 then 2 else if a = 2 then 5 else 0)
      split_ifs <;> decide
  have hin : x.regs ∘ src = unitWords () := by
    funext i
    exact Fin.elim0 i
  obtain ⟨t, ht, htime⟩ := he f src tmp hi (fun i => Fin.elim0 i) hf
    (fun i => Fin.elim0 i) 8 () x hx hin trivial trivial
  change t ≤ C * 1 + 2 at htime
  exact ⟨r, C, (Code.seq (emit f src tmp) (.op (.const (tmp 0) 0))).program (tmp 0),
    t, ht, by simpa only [Nat.mul_one] using htime⟩

end ComplexityTests.WordRAMRealizationProductGrowth
