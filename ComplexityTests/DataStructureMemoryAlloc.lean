/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.Stack.Memory

/-!
# Allocation inside operations, and structures already in memory

Two checks of the allocator contract of `Memory.Allocator`, at word size `8`.

**Room consumed inside operations.** A write-once cell reserves one cell of room when it is
allocated, and allocates that cell inside its first `set`. Two such cells share one memory as
`cells`, the product of their allocators. A client sets them alternately, so each `set`
allocates above the other structure's newest cell. The tests check:

* the answers and the admissibility of the whole run, by the generic `Allocator.run_correct`;
* the allocations inside the operations, in the run's memory history;
* after each step, the footprints, the abstractions and the frontier plus the remaining room,
  which stays at the frontier the allocation reserved up to;
* the boundary: from frontier `251`, where `251 + 4` fits a byte, the run is admissible. From
  `252` it is not, and only the right `set` fails: its allocation, of the last of the four
  reserved cells, would leave the frontier at `256`.

**Structures already in memory.** A stack that the input holds is taken over by
`Allocator.resident`, in the shape of Dijkstra's algorithm: two stacks are allocated from
scratch above the input, and the input's stack is used in place. The generic theorems give the
run's answer and cost. Two stacks that the input holds in disjoint cells combine too. Taking
over the same cells twice is excluded by the product's precondition.
-/

@[expose] public section

namespace ComplexityTests.DataStructureMemoryAlloc

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory

/-! ## A write-once cell that allocates on its first `set` -/

/-- The operations of a write-once cell: set it once, and get its value. -/
inductive CellOp where
  /-- Set the cell to a value. -/
  | set (v : ℕ)
  /-- Get the value, if set. -/
  | get
  deriving DecidableEq

/-- Setting answers nothing; getting answers the value, if set. -/
abbrev CellOp.Result : CellOp → Type
  | .set _ => Unit
  | .get => Option ℕ

/-- Setting stores the value, and getting returns it. -/
def cellStep (c : Option ℕ) : (o : CellOp) → Option ℕ × o.Result
  | .set v => (some v, ())
  | .get => (c, c)

/-- A cell is set once, to a word. -/
def cellValid (w : ℕ) (c : Option ℕ) : CellOp → Prop
  | .set v => c = none ∧ Fits w v
  | .get => True

instance (w : ℕ) (c : Option ℕ) (o : CellOp) : Decidable (cellValid w c o) := by
  cases o <;> unfold cellValid <;> infer_instance

/-- The write-once cell at word size `w`. -/
abbrev Cell (w : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := Option ℕ) (Op := CellOp) (Result := CellOp.Result) cellStep
    (cellValid w)

/-- Admissibility of a concrete history of cell operations is decidable. -/
instance (w : ℕ) (c : Option ℕ) (os : List CellOp) : Decidable ((Cell w).ValidHistory c os) := by
  induction os generalizing c with
  | nil => exact isTrue trivial
  | cons o os ih =>
    exact decidable_of_iff (cellValid w c o ∧ (Cell w).ValidHistory (cellStep c o).1 os) Iff.rfl

variable (h w : ℕ)

/-- Set: allocate the value cell, write the value there, and point the header `h` at it. -/
def cellSet (v : ℕ) : Prog Unit := do
  let p ← allocDirty 1
  write p v
  write h p

/-- Get: a zero header means unset; otherwise read the cell that it points to. -/
def cellGet : Prog (Option ℕ) := do
  let p ← read h
  if p = 0 then pure none else do
    let v ← read p
    pure (some v)

/-- The cell's operations as memory programs, with header `h`. -/
def cellMethods : Methods (Cell w) (spec w)
  | .set v => cellSet h v
  | .get => cellGet h

/-- The value cell, if the header points to one. -/
def cellAbs (s : State) : Option ℕ := if s.mem h = 0 then none else some (s.mem (s.mem h))

/-- The header, and the value cell once set. -/
def cellFootprint (s : State) : Finset ℕ := if s.mem h = 0 then {h} else {h, s.mem h}

/-- One cell of room until the cell is set. -/
def cellRoom (s : State) : ℕ := if s.mem h = 0 then 1 else 0

/-- The header and the value cell are allocated, and the frontier plus the room fits a word, so
that the first `set` may allocate. -/
structure CellInv (s : State) : Prop where
  /-- The header is allocated. -/
  header_lt : h < s.frontier
  /-- The value cell is allocated. -/
  value_lt : s.mem h ≠ 0 → s.mem h < s.frontier
  /-- The reserved cell fits. -/
  fits_room : Fits w (s.frontier + cellRoom h s)

/-- A set allocates one cell at the frontier, writes the value there and points the header at
it. -/
theorem runClient_cellSet (s : State) (v : ℕ) :
    (spec w).runClient s (cellSet h v) =
      ((), ⟨Function.update (Function.update s.mem s.frontier v) h s.frontier, s.frontier + 1⟩,
        [.allocDirty 1, .write s.frontier v, .write h s.frontier]) := rfl

/-- A get of an unset cell reads the header. -/
theorem runClient_cellGet_of_eq_zero (s : State) (h0 : s.mem h = 0) :
    (spec w).runClient s (cellGet h) = (none, s, [.read h]) := by
  simp [cellGet, h0]

/-- A get of a set cell reads the header and the value cell. -/
theorem runClient_cellGet_of_ne_zero (s : State) (h0 : s.mem h ≠ 0) :
    (spec w).runClient s (cellGet h) = (some (s.mem (s.mem h)), s, [.read h, .read (s.mem h)]) := by
  unfold cellGet
  simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.stepFn, step_read, h0,
    ↓reduceIte]
  rfl

/-- Allocating a header clears one cell at the frontier. -/
theorem runClient_alloc_one (s : State) :
    (spec w).runClient s (alloc 1) =
      (s.frontier, ⟨clear s.mem s.frontier 1, s.frontier + 1⟩, [.alloc 1]) := rfl

variable {h w}

/-- A cell is unset exactly when its header is zero. -/
theorem cellAbs_eq_none {s : State} : cellAbs h s = none ↔ s.mem h = 0 := by
  unfold cellAbs
  split <;> simp_all

variable (h w)

/-- The write-once cell with header `h` implements its specification. -/
def cellRefinement : Refinement (Cell w) (spec w) :=
  Refinement.ofFn (cellMethods h w) (CellInv h w) (cellAbs h)
    (by
      intro s o hs hv
      have hh := CellInv.header_lt hs
      cases o with
      | set v =>
        obtain ⟨hnone, hfit⟩ := hv
        have h0 := cellAbs_eq_none.mp hnone
        have hr := CellInv.fits_room hs
        simp only [cellRoom, h0, ↓reduceIte] at hr
        simp only [cellMethods, StateTransitionSpec.clientHistory, runClient_cellSet,
          StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, step_allocDirty,
          step_write, valid_allocDirty, valid_write]
        exact ⟨hr, ⟨Nat.lt_add_one _, hfit⟩, ⟨by omega, hr.of_le (by omega)⟩, trivial⟩
      | get =>
        by_cases h0 : s.mem h = 0
        · simp only [cellMethods, StateTransitionSpec.clientHistory,
            runClient_cellGet_of_eq_zero h w s h0]
          exact ⟨hh, trivial⟩
        · simp only [cellMethods, StateTransitionSpec.clientHistory,
            runClient_cellGet_of_ne_zero h w s h0]
          exact ⟨hh, CellInv.value_lt hs h0, trivial⟩)
    (by
      intro s o hs hv
      have hh := CellInv.header_lt hs
      cases o with
      | set v =>
        obtain ⟨hnone, -⟩ := hv
        have h0 := cellAbs_eq_none.mp hnone
        have hr := CellInv.fits_room hs
        simp only [cellRoom, h0, ↓reduceIte] at hr
        have hne : s.frontier ≠ h := by omega
        have hf0 : s.frontier ≠ 0 := by omega
        simp only [cellMethods, StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
          runClient_cellSet]
        refine ⟨?_, ⟨by simp only; omega, fun _ => ?_, ?_⟩⟩
        · simp [cellAbs, cellStep, hne, hf0]
        · simp only [Function.update_self]
          omega
        · simpa [cellRoom, hf0] using hr
      | get =>
        by_cases h0 : s.mem h = 0
        · simp only [cellMethods, StateTransitionSpec.clientState,
            StateTransitionSpec.clientResult, runClient_cellGet_of_eq_zero h w s h0]
          exact ⟨by simp [cellAbs, h0, cellStep], hs⟩
        · simp only [cellMethods, StateTransitionSpec.clientState,
            StateTransitionSpec.clientResult, runClient_cellGet_of_ne_zero h w s h0]
          exact ⟨by simp [cellAbs, h0, cellStep], hs⟩)

/-- The refinement runs the cell's methods. -/
@[simp] theorem cellRefinement_methods : (cellRefinement h w).methods = cellMethods h w := rfl

/-- The refinement's abstraction. -/
@[simp] theorem cellRefinement_abs : (cellRefinement h w).abs = cellAbs h := rfl

/-- The refinement's invariant. -/
@[simp] theorem cellRefinement_inv : (cellRefinement h w).inv = CellInv h w := rfl

/-- The header belongs to the footprint. -/
theorem header_mem_cellFootprint (s : State) : h ∈ cellFootprint h s := by
  unfold cellFootprint
  split <;> simp

/-- **The write-once cell, framed with room.** Its footprint grows into the cell that its first
`set` allocates, and that `set` gives up the one cell of room it advances the frontier by. -/
def cellFramed : Framed (Cell w) w where
  toRefinement := cellRefinement h w
  footprint := cellFootprint h
  room := cellRoom h
  lt_frontier {s a} hs ha := by
    have hh := CellInv.header_lt hs
    unfold cellFootprint at ha
    split at ha
    · rw [Finset.mem_singleton] at ha
      omega
    · rcases Finset.mem_insert.mp ha with ha | ha
      · omega
      · rw [Finset.mem_singleton] at ha
        rw [ha]
        exact CellInv.value_lt hs (by assumption)
  congr {s s'} hs hmem hf hr := by
    have hh : s'.mem h = s.mem h := hmem h (header_mem_cellFootprint h s)
    have hroom : cellRoom h s' = cellRoom h s := by simp only [cellRoom, hh]
    have hfp : cellFootprint h s' = cellFootprint h s := by simp only [cellFootprint, hh]
    refine ⟨⟨(CellInv.header_lt hs).trans_le hf, fun h0 => ?_, hroom ▸ hr⟩, ?_, hfp, hroom⟩
    · rw [hh] at h0 ⊢
      exact (CellInv.value_lt hs h0).trans_le hf
    · change cellAbs h s' = cellAbs h s
      unfold cellAbs
      by_cases h0 : s.mem h = 0
      · simp [hh, h0]
      · have hv : s'.mem (s.mem h) = s.mem (s.mem h) := hmem _ (by simp [cellFootprint, h0])
        simp [hh, h0, hv]
  modifies {s} o {a s' tr} hs hv hrun := by
    obtain ⟨_, _, rfl, _⟩ := ((spec w).clientRun_iff_runClient _ _ _ _ _).mp hrun
    simp only [cellRefinement_inv, cellRefinement_abs] at hs hv
    have hh := CellInv.header_lt hs
    cases o with
    | set v =>
      obtain ⟨hnone, -⟩ := hv
      have h0 := cellAbs_eq_none.mp hnone
      have hne : s.frontier ≠ h := by omega
      simp only [cellRefinement_methods, cellMethods, StateTransitionSpec.clientState,
        runClient_cellSet]
      refine ⟨fun b hb hb' => ?_, fun b hb => ?_, ?_⟩
      · have hbh : b ≠ h := fun e => hb' (e ▸ header_mem_cellFootprint h s)
        change Function.update (Function.update s.mem s.frontier v) h s.frontier b = s.mem b
        rw [Function.update_of_ne hbh, Function.update_of_ne (by omega)]
      · have hf0 : s.frontier ≠ 0 := by omega
        simp only [cellFootprint, Function.update_self, hf0, ↓reduceIte, Finset.mem_insert,
          Finset.mem_singleton] at hb
        rcases hb with hb | hb
        · exact .inl (hb ▸ header_mem_cellFootprint h s)
        · exact .inr hb.ge
      · have hf0 : s.frontier ≠ 0 := by omega
        simp [cellRoom, h0, hf0]
    | get =>
      by_cases h0 : s.mem h = 0
      · simp only [cellRefinement_methods, cellMethods, StateTransitionSpec.clientState,
          runClient_cellGet_of_eq_zero h w s h0]
        exact ⟨fun _ _ _ => trivial, fun _ hb => .inl hb, le_rfl⟩
      · simp only [cellRefinement_methods, cellMethods, StateTransitionSpec.clientState,
          runClient_cellGet_of_ne_zero h w s h0]
        exact ⟨fun _ _ _ => trivial, fun _ hb => .inl hb, le_rfl⟩

/-- A set costs three memory units, a get at most two, with no potential. -/
theorem cellAmortized : (cellFramed h w).Amortized charge (fun _ _ => 3) fun _ => 0 := by
  apply Refinement.Amortized.ofFn
  intro s o _ _
  change (spec w).totalCost charge s ((spec w).clientHistory s (cellMethods h w o)) + 0 ≤ 3 + 0
  cases o with
  | set v => simp [cellMethods, StateTransitionSpec.clientHistory, runClient_cellSet]
  | get =>
    by_cases h0 : s.mem h = 0
    · simp [cellMethods, StateTransitionSpec.clientHistory, runClient_cellGet_of_eq_zero h w s h0]
    · simp [cellMethods, StateTransitionSpec.clientHistory, runClient_cellGet_of_ne_zero h w s h0]

/-- **The write-once cell as an allocator**: allocate a zeroed header, and reserve one more cell
for the first `set`. -/
def cellAllocator : Allocator (Cell w) w where
  Handle := ℕ
  alloc := alloc 1
  methods h := cellMethods h w
  init := none
  room := 2
  cost := 2
  framed s _ _ := cellFramed s.frontier w
  allocates s _ hroom := by
    have h0 : clear s.mem s.frontier 1 s.frontier = 0 :=
      clear_of_owns ⟨le_rfl, Nat.lt_add_one _⟩
    refine
      { validHistory := ?_, cost_le := ?_, mem_eq := ?_, methods_eq := rfl, inv := ?_,
        abs_eq := ?_, of_mem_footprint := ?_, room_le := ?_ } <;>
      simp only [StateTransitionSpec.clientHistory, StateTransitionSpec.clientState,
        runClient_alloc_one]
    · exact ⟨hroom.of_le (by omega), trivial⟩
    · simp
    · exact fun a ha => clear_of_not_owns (by simp only [Block.Owns]; omega)
    · refine ⟨Nat.lt_add_one _, fun h => absurd h0 h, ?_⟩
      change Fits w (s.frontier + 1 + cellRoom s.frontier ⟨clear s.mem s.frontier 1, _⟩)
      simp only [cellRoom, h0, ↓reduceIte]
      exact hroom.of_le (by omega)
    · change cellAbs s.frontier ⟨clear s.mem s.frontier 1, _⟩ = none
      simp [cellAbs, h0]
    · intro a ha
      change a ∈ cellFootprint s.frontier ⟨clear s.mem s.frontier 1, _⟩ at ha
      simp only [cellFootprint, h0, ↓reduceIte, Finset.mem_singleton] at ha
      exact .inr ha.ge
    · change s.frontier + 1 + cellRoom s.frontier ⟨clear s.mem s.frontier 1, _⟩ ≤ _
      simp only [cellRoom, h0, ↓reduceIte]
      omega

/-- Each cell costs three memory units per operation, and allocation leaves no potential. -/
theorem cellAllocator_amortized : (cellAllocator w).Amortized (fun _ _ => 3) 0 :=
  fun s _ _ => ⟨fun _ => 0, cellAmortized s.frontier w, Framed.Local.const _ 0, le_rfl⟩

/-! ## Two cells that allocate inside their operations -/

/-- Two write-once cells in one memory, each with one cell of room for its `set`. -/
abbrev cells : Allocator (product (Cell 8) (Cell 8)) 8 := (cellAllocator 8).prod (cellAllocator 8)

/-- The two cells reserve four cells: two headers and two value cells. -/
example : cells.room = 4 := rfl

/-- Set the left cell. -/
def setLeft : (product (Cell 8) (Cell 8)).Client Unit :=
  (product (Cell 8) (Cell 8)).call (.inl (.set 5))

/-- Set the left cell, then the right one. -/
def setBoth : (product (Cell 8) (Cell 8)).Client Unit := do
  let _ ← (product (Cell 8) (Cell 8)).call (.inl (.set 5))
  let _ ← (product (Cell 8) (Cell 8)).call (.inr (.set 7))
  pure ()

/-- Set both cells, then get both. -/
def client : (product (Cell 8) (Cell 8)).Client (Option ℕ × Option ℕ) := do
  setBoth
  let a ← (product (Cell 8) (Cell 8)).call (.inl .get)
  let b ← (product (Cell 8) (Cell 8)).call (.inr .get)
  pure (a, b)

/-- Memory with nothing allocated. -/
def nothing : State := ⟨fun _ => 0, 0⟩

/-- Nothing is needed of the memory besides room. -/
theorem pre (s : State) : cells.Pre s := ⟨trivial, trivial, Finset.disjoint_empty_left _⟩

/-- The four reserved cells fit a byte. -/
theorem fits : Fits 8 (nothing.frontier + cells.room) := by decide

/-- The two cells, as set up by the allocation from `nothing`. -/
abbrev framed : Framed (product (Cell 8) (Cell 8)) 8 := cells.framed nothing (pre _) fits

/-- The client is admissible: each cell is set once, to a byte. -/
theorem client_valid : (product (Cell 8) (Cell 8)).ValidHistory cells.init
    ((product (Cell 8) (Cell 8)).clientHistory cells.init client) :=
  ⟨⟨rfl, by decide⟩, ⟨rfl, by decide⟩, trivial, trivial, trivial⟩

/-- **The run is admissible and answers as the specification does**, by the generic theorem: no
proof about this client or this product. -/
theorem run_correct :
    (spec 8).ValidHistory nothing ((spec 8).clientHistory nothing (cells.run client)) ∧
      (spec 8).clientResult nothing (cells.run client) = (some 5, some 7) ∧
      framed.abs ((spec 8).clientState nothing (cells.run client)) = (some 5, some 7) := by
  obtain ⟨hv, hres, -, habs⟩ := cells.run_correct client (pre _) fits client_valid
  exact ⟨hv, hres, habs⟩

/-- The same answer, by evaluation. -/
example : (spec 8).clientResult nothing (cells.run client) = (some 5, some 7) := by decide

/-- **Each `set` allocates inside the operation**: the headers at `0` and `1`, then the left
value cell at `2` and the right one at `3`, above the other structure's newest cell. -/
example : (spec 8).clientHistory nothing (cells.run client) =
    [.alloc 1, .alloc 1, .allocDirty 1, .write 2 5, .write 0 2, .allocDirty 1, .write 3 7,
      .write 1 3, .read 0, .read 2, .read 1, .read 3] := by
  decide

/-- After allocation: both headers, both cells unset, and two cells of room up to frontier
`4`. -/
example : let s := (spec 8).clientState nothing (cells.run (pure ()))
    framed.footprint s = {0, 1} ∧ framed.abs s = (none, none) ∧ s.frontier = 2 ∧
      framed.room s = 2 := by
  decide

/-- After the left `set`: the left cell has taken its reserved cell `2`, and the right cell keeps
its value, its footprint and its reservation. The frontier plus the room is still `4`. -/
example : let s := (spec 8).clientState nothing (cells.run setLeft)
    framed.footprint s = {0, 2, 1} ∧ framed.abs s = (some 5, none) ∧ s.frontier = 3 ∧
      framed.room s = 1 := by
  decide

/-- After both `set`s: all four reserved cells are used and no room is left. -/
example : let s := (spec 8).clientState nothing (cells.run setBoth)
    framed.footprint s = {0, 2, 1, 3} ∧ framed.abs s = (some 5, some 7) ∧ s.frontier = 4 ∧
      framed.room s = 0 := by
  decide

/-- It costs two units per header and three per `set` and two per `get`. -/
example : (spec 8).totalCost charge nothing ((spec 8).clientHistory nothing (cells.run client)) =
    14 := by
  decide

/-- The generic cost theorem: four units to allocate, and three per operation. -/
example : (spec 8).totalCost charge nothing ((spec 8).clientHistory nothing (cells.run client)) ≤
    4 + 0 + 3 * 4 := by
  have h := Allocator.Amortized.prod (cellAllocator_amortized (w := 8))
    (cellAllocator_amortized (w := 8))
  simp only [productCharge_const] at h
  exact Allocator.run_cost_le h client (pre _) fits client_valid

/-! ### The boundary of the reservation -/

/-- The highest frontier with room for both cells at word size `8`: `251 + 4 = 255`. -/
def high : State := ⟨fun _ => 0, 251⟩

/-- One cell higher: `252 + 4 = 256` does not fit a byte. -/
def tooHigh : State := ⟨fun _ => 0, 252⟩

example : Fits 8 (high.frontier + cells.room) ∧ ¬Fits 8 (tooHigh.frontier + cells.room) := by
  decide

/-- From the highest frontier with room, the generic theorem gives an admissible run. -/
example : (spec 8).ValidHistory high ((spec 8).clientHistory high (cells.run client)) :=
  (cells.run_correct client (pre _) (by decide) client_valid).1

/-- One cell higher, the run is not admissible. -/
example : ¬(spec 8).ValidHistory tooHigh ((spec 8).clientHistory tooHigh (cells.run client)) := by
  decide

/-- Only the right `set` fails, when it allocates the last of the four reserved cells: the
allocations and the left `set` are admissible. -/
example : (spec 8).ValidHistory tooHigh ((spec 8).clientHistory tooHigh (cells.run setLeft)) ∧
    ¬(spec 8).ValidHistory tooHigh ((spec 8).clientHistory tooHigh (cells.run setBoth)) := by
  decide

/-! ## Stacks already in memory -/

/-- A bounded stack of capacity `2` at word size `8`. -/
abbrev S : StateTransitionSpec := Stack.WordRAM.spec 8 2

/-- The layout of stack `i`: its count cell at `3 i`, its items at `3 i + 1` and `3 i + 2`. -/
def layout (i : ℕ) : Stack.Memory.Layout := ⟨⟨3 * i, 1⟩, ⟨3 * i + 1, 2⟩⟩

/-- The layouts are well formed. -/
theorem valid (i : ℕ) (hi : i < 3) : (layout i).Valid 8 2 :=
  Stack.Memory.valid_allocLayout (f := 3 * i) (Fits.of_le (show Fits 8 9 by decide) (by omega))

/-- The stack at layout `i`, taken over as it is in memory, holding `xs`. -/
abbrev inputStack (i : ℕ) (hi : i < 3) (xs : List ℕ) : Allocator S 8 :=
  Allocator.resident (Stack.Memory.framed (valid i hi)) xs 0

/-- The input: stack `0` holds `7` on top of `5`, and stack `1` holds `4`. -/
def input : State :=
  ⟨fun a => if a = 0 then 2 else if a = 1 then 5 else if a = 2 then 7 else if a = 3 then 1
    else if a = 4 then 4 else 0, 6⟩

/-- Stack `i` holds in the input. -/
theorem inv_input (i : ℕ) (hi : i < 2) : Stack.Memory.Inv (layout i) input where
  count_allocated := by simp only [Block.Allocated, layout, input]; omega
  items_allocated := by simp only [Block.Allocated, layout, input]; omega
  count_le := by
    obtain _ | _ | i := i
    · decide
    · decide
    · omega

/-- **The Dijkstra shape**: two stacks allocated from scratch above the input, and the input's
stack `0` taken over in place, as Dijkstra's algorithm takes over its input graph. -/
abbrev dijkstraShape : Allocator (product S (product S S)) 8 :=
  (Stack.Memory.allocator 8 2).prod ((Stack.Memory.allocator 8 2).prod (inputStack 0 (by decide)
    [7, 5]))

/-- The input holds the stack that the third structure takes over. -/
theorem pre_dijkstraShape : dijkstraShape.Pre input :=
  ⟨trivial, ⟨trivial, ⟨inv_input 0 (by decide), by decide, le_rfl⟩, Finset.disjoint_empty_left _⟩,
    Finset.disjoint_empty_left _⟩

/-- Pop the input's stack, push `1` on the first fresh stack and `2` on the second, then pop
all three. -/
def dijkstraClient : (product S (product S S)).Client (List (Option ℕ)) := do
  let a ← (product S (product S S)).call (.inr (.inr .pop))
  let _ ← (product S (product S S)).call (.inl (.push 1))
  let _ ← (product S (product S S)).call (.inr (.inl (.push 2)))
  let b ← (product S (product S S)).call (.inl .pop)
  let c ← (product S (product S S)).call (.inr (.inl .pop))
  let d ← (product S (product S S)).call (.inr (.inr .pop))
  pure [a, b, c, d]

/-- The client is admissible from the allocated states. -/
theorem dijkstraClient_valid : (product S (product S S)).ValidHistory dijkstraShape.init
    ((product S (product S S)).clientHistory dijkstraShape.init dijkstraClient) :=
  ⟨trivial, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, trivial, trivial, trivial, trivial⟩

/-- **The generic correctness theorem**: the run answers as the specification does from the
input's stack and two empty ones. -/
example : (spec 8).clientResult input (dijkstraShape.run dijkstraClient) =
    [some 7, some 1, some 2, some 5] := by
  obtain ⟨-, hres, -⟩ :=
    dijkstraShape.run_correct dijkstraClient pre_dijkstraShape (by decide) dijkstraClient_valid
  rw [hres]
  decide

/-- The same answer, by evaluation. The fresh stacks take the six cells above the input, and
the input's stack is popped in place: its count cell, at address `0`, ends at `0`. -/
example : (spec 8).clientResult input (dijkstraShape.run dijkstraClient) =
      [some 7, some 1, some 2, some 5] ∧
    ((spec 8).clientState input (dijkstraShape.run dijkstraClient)).frontier = 12 ∧
    ((spec 8).clientState input (dijkstraShape.run dijkstraClient)).mem 0 = 0 := by
  decide

/-- The generic cost theorem: six units to allocate the fresh stacks, none for the input's, and
three per operation. -/
example : (spec 8).totalCost charge input ((spec 8).clientHistory input
    (dijkstraShape.run dijkstraClient)) ≤ 6 + 0 + 3 * 6 := by
  have hres : (inputStack 0 (by decide) [7, 5]).Amortized (fun _ _ => 3) 0 :=
    Allocator.Amortized.resident (Stack.Memory.amortized _) (Framed.Local.const _ 0)
      fun _ _ _ => le_rfl
  have h := Allocator.Amortized.prod (Stack.Memory.amortized_allocator (w := 8) (C := 2))
    (Allocator.Amortized.prod (Stack.Memory.amortized_allocator (w := 8) (C := 2)) hres)
  simp only [productCharge_const] at h
  exact Allocator.run_cost_le h dijkstraClient pre_dijkstraShape (by decide) dijkstraClient_valid

/-- Two stacks that the input holds in disjoint cells. -/
abbrev bothInputs : Allocator (product S S) 8 :=
  (inputStack 0 (by decide) [7, 5]).prod (inputStack 1 (by decide) [4])

/-- Pop both input stacks twice. -/
def popBoth : (product S S).Client (List (Option ℕ)) := do
  let a ← (product S S).call (.inl .pop)
  let b ← (product S S).call (.inr .pop)
  let c ← (product S S).call (.inl .pop)
  let d ← (product S S).call (.inr .pop)
  pure [a, b, c, d]

/-- Both stacks hold in the input, in disjoint cells. -/
theorem pre_bothInputs : bothInputs.Pre input :=
  ⟨⟨inv_input 0 (by decide), by decide, le_rfl⟩, ⟨inv_input 1 (by decide), by decide, le_rfl⟩,
    by decide⟩

/-- The generic correctness theorem for two structures taken over in place. -/
example : (spec 8).clientResult input (bothInputs.run popBoth) =
    [some 7, some 4, some 5, none] := by
  obtain ⟨-, hres, -⟩ := bothInputs.run_correct popBoth pre_bothInputs (by decide)
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  rw [hres]
  decide

/-- **The same cells cannot be taken over twice**: the product's precondition asks for disjoint
cells, so no memory satisfies it for one stack taken over twice. -/
example (s : State) : ¬((inputStack 0 (by decide) [7, 5]).prod
    (inputStack 0 (by decide) [7, 5])).Pre s := fun hs => by
  have hd : Disjoint (layout 0).footprint (layout 0).footprint := Allocator.ProdPre.disjoint hs
  exact absurd hd (by decide)

end ComplexityTests.DataStructureMemoryAlloc
