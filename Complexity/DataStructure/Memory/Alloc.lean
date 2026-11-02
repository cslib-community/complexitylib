/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Memory.Frame
public import Complexity.Foundations.Analysis.Asymptotics.CostBound

/-!
# Allocating data structures over the memory oracle

A program that uses data structures over `Memory.spec w` first allocates their storage, then runs
a client of their specification through their methods. A `Memory.Allocator D w` packages the
first half for a specification `D`:

* the allocation program, which returns a handle such as a layout of named fields;
* the methods, given the handle;
* the abstract state the allocation sets up, the room it needs, and a bound on its cost;
* for each memory with that room, the framed refinement it sets up (`Allocator.framed`), with the
  proof that the allocation sets it up (`Memory.Allocates`).

The structure's footprint lies in fresh cells, which the allocation and later operations take
from the frontier, and in the allocated cells `Allocator.owned` that it takes over. A structure
allocated from scratch takes over none. One that the input already holds, such as a graph given
as adjacency arrays, takes over the cells holding it, and its precondition `Allocator.Pre` says
that they do. `Allocator.resident` is the allocator of a framed structure already in memory,
whose allocation does nothing.

`Allocator.run` allocates and then runs a client. `Allocator.run_correct` and
`Allocator.run_cost` hold for every allocator and every client: a client admissible for the
specification issues only admissible memory operations, answers as the specification does, and
costs at most the allocation's cost, the potential once allocated, and the upper charges of its
operations. A certificate `Allocator.Amortized` carries the cost side. `Allocator.run_cost_isBigO`
exports a constant per-operation charge as `O(m)` in the number `m` of operations.

Allocators combine as their structures do.

* `Allocator.prod` allocates two structures one after the other, and sets up their product over
  one memory (`Memory.Framed.prod`). Its room is the sum of the rooms, so it reserves both
  structures' growth. Iterated, `A₁.prod (A₂.prod A₃)` allocates the three structures of a client
  such as Dijkstra's algorithm, which runs over `product PQ (product Dict Adj)`.
* `Allocator.comp` puts a refinement on top, such as a queue over the pair of its stacks, with
  `Memory.Framed.comp`.

Certificates combine along with them (`Allocator.Amortized.prod`, `Allocator.Amortized.comp`,
`Allocator.Amortized.resident`). An allocation changes no allocated cell, so it keeps the other
structures' preconditions and the cells they take over (`Allocator.pre_fresh`,
`Allocator.owned_fresh`). The product's precondition (`Allocator.ProdPre`) asks in addition that
the cells the two structures take over be disjoint. So `A₁.prod (A₂.prod A₃)` may combine
structures allocated from scratch with structures that the input holds.

## Main definitions

* `Memory.Allocates`: what an allocation program establishes for the structure it sets up.
* `Memory.Allocator`: an allocation program, the methods it sets up, and their framed refinement.
* `Memory.Allocator.run`: allocate, then run a client.
* `Memory.Allocator.prod`, `Memory.Allocator.comp`: products and refinements on top.
* `Memory.Allocator.ProdPre`: the precondition of a product.
* `Memory.Allocator.resident`: a structure already in memory.
* `Memory.Allocator.Amortized`: an amortized cost certificate of an allocator.

## Main results

* `Memory.Allocator.run_correct`: the run is admissible and answers as the specification.
* `Memory.Allocator.run_cost`, `Memory.Allocator.run_cost_le`: its memory cost.
* `Memory.Allocator.run_cost_isBigO`: the cost as `O(m)` for constant per-operation charges.
* `Memory.Allocator.Amortized.prod`, `Memory.Allocator.Amortized.comp`,
  `Memory.Allocator.Amortized.resident`: certificates combine, and carry over to structures
  already in memory.
-/

@[expose] public section

namespace Cslib.DataStructure.Memory

open Cslib.WordRAM

variable {w : ℕ}

/-- What running the allocation program `alloc` from the memory `s` establishes for the framed
refinement `M`: its operations are admissible and cost at most `cost`, it changes no allocated
cell, and it sets up `M` with the methods of the handle it returns, holding at the abstract state
`init`. The footprint lies in the allocated cells `owned` that the structure takes over and in
fresh cells, and the frontier plus `M`'s room is at most `room` beyond the old frontier. -/
structure Allocates {D : StateTransitionSpec.{0, 0, 0}} {H : Type} (alloc : Prog H)
    (methods : H → Methods D (spec w)) (init : D.State) (owned : Finset ℕ) (room cost : ℕ)
    (s : State) (M : Framed D w) : Prop where
  /-- The allocation's operations are admissible. -/
  validHistory : (spec w).ValidHistory s ((spec w).clientHistory s alloc)
  /-- The allocation costs at most `cost`. -/
  cost_le : (spec w).totalCost charge s ((spec w).clientHistory s alloc) ≤ cost
  /-- The allocation changes no allocated cell. -/
  mem_eq : ∀ a < s.frontier, ((spec w).clientState s alloc).mem a = s.mem a
  /-- The structure runs the methods of the returned handle. -/
  methods_eq : M.methods = methods ((spec w).clientResult s alloc)
  /-- The structure holds after the allocation. -/
  inv : M.inv ((spec w).clientState s alloc)
  /-- It represents `init`. -/
  abs_eq : M.abs ((spec w).clientState s alloc) = init
  /-- Its footprint lies in the cells it takes over and in fresh cells. -/
  of_mem_footprint : ∀ a ∈ M.footprint ((spec w).clientState s alloc), a ∈ owned ∨ s.frontier ≤ a
  /-- The allocation and the structure's reserved room take at most `room` cells. -/
  room_le : ((spec w).clientState s alloc).frontier + M.room ((spec w).clientState s alloc) ≤
    s.frontier + room

/-- **Allocators.** A memory program `alloc` that allocates a structure implementing `D`, and
the structure's methods, given the handle that `alloc` returns. From a memory satisfying `Pre` in
which `room` cells beyond the frontier fit a word, the allocation sets up the framed refinement
`framed s`, which represents `init`, at a memory cost of at most `cost`. Its footprint lies in
fresh cells and in the allocated cells `owned s` that it takes over, such as an input that holds
the structure already. -/
structure Allocator (D : StateTransitionSpec.{0, 0, 0}) (w : ℕ) where
  /-- What the allocation returns, such as a layout of named fields. -/
  Handle : Type
  /-- The allocation program. -/
  alloc : Prog Handle
  /-- The structure's methods, given the handle. -/
  methods : Handle → Methods D (spec w)
  /-- The abstract state the allocation sets up. -/
  init : D.State
  /-- The cells the allocation takes and the room it reserves for growth. -/
  room : ℕ
  /-- A bound on the memory cost of the allocation. -/
  cost : ℕ
  /-- What the allocation needs of the memory besides room, such as the structure it takes
  over. -/
  Pre : State → Prop := fun _ => True
  /-- The allocated cells that the structure takes over instead of allocating them. -/
  owned : State → Finset ℕ := fun _ => ∅
  /-- The cells taken over are allocated. -/
  owned_lt : ∀ {s a}, Pre s → a ∈ owned s → a < s.frontier := by intros; simp_all
  /-- Runs that keep every allocated cell and leave the room fitting, such as other allocations,
  keep the precondition. -/
  pre_fresh : ∀ {s s' : State}, Pre s → (∀ a < s.frontier, s'.mem a = s.mem a) →
    s.frontier ≤ s'.frontier → Fits w (s'.frontier + room) → Pre s' := by intros; trivial
  /-- Such runs keep the cells taken over. -/
  owned_fresh : ∀ {s s' : State}, Pre s → (∀ a < s.frontier, s'.mem a = s.mem a) →
    s.frontier ≤ s'.frontier → Fits w (s'.frontier + room) → owned s' = owned s := by
    intros; rfl
  /-- The framed refinement that allocating from `s` sets up. -/
  framed : (s : State) → Pre s → Fits w (s.frontier + room) → Framed D w
  /-- Allocating from `s` sets it up. -/
  allocates : ∀ s (hs : Pre s) (hroom : Fits w (s.frontier + room)),
    Allocates alloc methods init (owned s) room cost s (framed s hs hroom)

namespace Allocator

variable {D D₁ D₂ E : StateTransitionSpec.{0, 0, 0}}

/-! ## Runs -/

section Run

variable (A : Allocator D w)

/-- Allocate the structure, then run a client of its specification through its methods. -/
def run {β : Type} (p : D.Client β) : Prog β := A.alloc >>= fun h => link (A.methods h) p

/-- The history of a run: the allocation's, then the linked client's. -/
theorem clientHistory_run {β : Type} (p : D.Client β) (s : State) :
    (spec w).clientHistory s (A.run p) = (spec w).clientHistory s A.alloc ++
      (spec w).clientHistory ((spec w).clientState s A.alloc)
        (link (A.methods ((spec w).clientResult s A.alloc)) p) :=
  (spec w).clientHistory_bind _ _ s

/-- The answer of a run is the linked client's. -/
theorem clientResult_run {β : Type} (p : D.Client β) (s : State) :
    (spec w).clientResult s (A.run p) =
      (spec w).clientResult ((spec w).clientState s A.alloc)
        (link (A.methods ((spec w).clientResult s A.alloc)) p) :=
  (spec w).clientResult_bind _ _ s

/-- A run ends where the linked client ends. -/
theorem clientState_run {β : Type} (p : D.Client β) (s : State) :
    (spec w).clientState s (A.run p) =
      (spec w).clientState ((spec w).clientState s A.alloc)
        (link (A.methods ((spec w).clientResult s A.alloc)) p) :=
  (spec w).clientState_bind _ _ s

variable {fD : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn fD]

/-- **Correctness of a run.** From a memory with the allocator's precondition and room, a client
admissible for the specification issues only admissible memory operations and answers as the
specification does from `A.init`; the structure then holds at the specified final state. -/
theorem run_correct {β : Type} (p : D.Client β) {s : State} (hs : A.Pre s)
    (hroom : Fits w (s.frontier + A.room)) (hv : D.ValidHistory A.init (D.clientHistory A.init p)) :
    (spec w).ValidHistory s ((spec w).clientHistory s (A.run p)) ∧
      (spec w).clientResult s (A.run p) = D.clientResult A.init p ∧
      (A.framed s hs hroom).inv ((spec w).clientState s (A.run p)) ∧
      (A.framed s hs hroom).abs ((spec w).clientState s (A.run p)) = D.clientState A.init p := by
  have hA := A.allocates s hs hroom
  obtain ⟨hvE, hres, habs, hinv⟩ :=
    (A.framed s hs hroom).simulates_client p hA.inv (by rw [hA.abs_eq]; exact hv)
  rw [hA.methods_eq] at hvE hres habs hinv
  rw [hA.abs_eq] at hres habs
  rw [clientHistory_run, clientResult_run, clientState_run,
    StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient]
  exact ⟨⟨hA.validHistory, hvE⟩, hres, hinv, habs⟩

end Run

/-! ## Cost certificates -/

/-- **An amortized cost certificate of an allocator.** From every memory it can allocate from,
the structure it sets up is amortized against `upper` with a potential that reads only its
footprint and is at most `Φ₀` once allocated. -/
def Amortized (A : Allocator D w) (upper : D.State → D.Op → ℕ) (Φ₀ : ℕ) : Prop :=
  ∀ s (hs : A.Pre s) (hroom : Fits w (s.frontier + A.room)), ∃ Φ : State → ℕ,
    (A.framed s hs hroom).Amortized charge upper Φ ∧ (A.framed s hs hroom).Local Φ ∧
      Φ ((spec w).clientState s A.alloc) ≤ Φ₀

section Cost

variable {A : Allocator D w} {fD : (s : D.State) → (o : D.Op) → D.State × D.Result o}
  [D.HasStepFn fD]

/-- **The cost of a run.** A client admissible for the specification costs at most the
allocation's cost, the potential once allocated, and the upper charges of its operations. -/
theorem run_cost {upper : D.State → D.Op → ℕ} {Φ₀ : ℕ} (hA : A.Amortized upper Φ₀) {β : Type}
    (p : D.Client β) {s : State} (hs : A.Pre s) (hroom : Fits w (s.frontier + A.room))
    (hv : D.ValidHistory A.init (D.clientHistory A.init p)) :
    (spec w).totalCost charge s ((spec w).clientHistory s (A.run p)) ≤
      A.cost + Φ₀ + D.totalCost upper A.init (D.clientHistory A.init p) := by
  have hal := A.allocates s hs hroom
  obtain ⟨Φ, hc, -, hΦ⟩ := hA s hs hroom
  have h := hc.client p hal.inv (by rw [hal.abs_eq]; exact hv)
  rw [hal.methods_eq, hal.abs_eq] at h
  rw [clientHistory_run, StateTransitionSpec.totalCost_append, StateTransitionSpec.run_runClient]
  have := hal.cost_le
  omega

/-- The cost of a run for a constant charge `K` per operation: at most the allocation's cost,
the potential once allocated, and `K` per operation. -/
theorem run_cost_le {K Φ₀ : ℕ} (hA : A.Amortized (fun _ _ => K) Φ₀) {β : Type}
    (p : D.Client β) {s : State} (hs : A.Pre s) (hroom : Fits w (s.frontier + A.room))
    (hv : D.ValidHistory A.init (D.clientHistory A.init p)) :
    (spec w).totalCost charge s ((spec w).clientHistory s (A.run p)) ≤
      A.cost + Φ₀ + K * (D.clientHistory A.init p).length := by
  have h := run_cost hA p hs hroom hv
  rw [StateTransitionSpec.totalCost_const, Nat.mul_comm] at h
  exact h

/-- **The exported form.** For a constant charge per operation, the memory cost of a run is
`O(m)` in the number `m` of operations, over admissible clients. -/
theorem run_cost_isBigO {K Φ₀ : ℕ} (hA : A.Amortized (fun _ _ => K) Φ₀) {β : Type} {s : State}
    (hs : A.Pre s) (hroom : Fits w (s.frontier + A.room)) :
    CostIsBigO Filter.atTop (fun m : ℕ => (m : ℝ))
      (fun p : {p : D.Client β // D.ValidHistory A.init (D.clientHistory A.init p)} =>
        (D.clientHistory A.init p.1).length)
      (fun p => (spec w).totalCost charge s ((spec w).clientHistory s (A.run p.1))) :=
  CostIsBigO.of_le_add_mul (A.cost + Φ₀) K fun p => run_cost_le hA p.1 hs hroom p.2

end Cost

/-! ## Refinements on top -/

/-- **A refinement on top of an allocated structure.** The same allocation sets up the
composite `Memory.Framed.comp R M`, whose methods link `R`'s methods through the structure's,
provided `R`'s invariant holds of the allocated abstract state. -/
def comp (R : Refinement D E) (A : Allocator E w) (hinit : R.inv A.init) : Allocator D w where
  Handle := A.Handle
  alloc := A.alloc
  methods h o := link (A.methods h) (R.methods o)
  init := R.abs A.init
  room := A.room
  cost := A.cost
  Pre := A.Pre
  owned := A.owned
  owned_lt := A.owned_lt
  pre_fresh := A.pre_fresh
  owned_fresh := A.owned_fresh
  framed s hs hroom := Framed.comp R (A.framed s hs hroom)
  allocates s hs hroom :=
    have h := A.allocates s hs hroom
    { validHistory := h.validHistory
      cost_le := h.cost_le
      mem_eq := h.mem_eq
      methods_eq := by rw [Framed.comp_methods, h.methods_eq]
      inv := ⟨h.inv, by rw [h.abs_eq]; exact hinit⟩
      abs_eq := by rw [Framed.comp_abs, h.abs_eq]
      of_mem_footprint := h.of_mem_footprint
      room_le := h.room_le }

/-- **Potentials stack through a refinement on top.** A certificate of `R` against the middle
charges and one of the allocator against them give a certificate of the composite, with `R`'s
potential at the allocated state added. -/
theorem Amortized.comp {R : Refinement D E} {A : Allocator E w} {hinit : R.inv A.init}
    {middle : E.State → E.Op → ℕ} {upper : D.State → D.Op → ℕ} {Φ : E.State → ℕ} {Ψ₀ : ℕ}
    (hR : R.Amortized middle upper Φ) (hA : A.Amortized middle Ψ₀) :
    (A.comp R hinit).Amortized upper (Φ A.init + Ψ₀) := by
  intro s hs hroom
  obtain ⟨Ψ, hc, hl, hΨ⟩ := hA s hs hroom
  have hal := A.allocates s hs hroom
  refine ⟨fun s' => Φ ((A.framed s hs hroom).abs s') + Ψ s', Framed.amortized_comp hR hc,
    Framed.Local.add (Framed.Local.comp (Framed.Local.comp_abs _ Φ)) (Framed.Local.comp hl), ?_⟩
  change Φ ((A.framed s hs hroom).abs ((spec w).clientState s A.alloc)) +
    Ψ ((spec w).clientState s A.alloc) ≤ Φ A.init + Ψ₀
  rw [hal.abs_eq]
  omega

/-! ## Products -/

section Prod

variable (A₁ : Allocator D₁ w) (A₂ : Allocator D₂ w)

/-- Allocate both structures, one after the other. -/
def allocPair : Prog (A₁.Handle × A₂.Handle) := do
  let h₁ ← A₁.alloc
  let h₂ ← A₂.alloc
  pure (h₁, h₂)

/-- Both allocations' histories, one after the other. -/
theorem clientHistory_allocPair (s : State) :
    (spec w).clientHistory s (allocPair A₁ A₂) = (spec w).clientHistory s A₁.alloc ++
      (spec w).clientHistory ((spec w).clientState s A₁.alloc) A₂.alloc := by
  rw [allocPair, (spec w).clientHistory_bind, (spec w).clientHistory_bind]
  exact congrArg (_ ++ ·) (List.append_nil _)

/-- The memory after both allocations. -/
theorem clientState_allocPair (s : State) :
    (spec w).clientState s (allocPair A₁ A₂) =
      (spec w).clientState ((spec w).clientState s A₁.alloc) A₂.alloc := by
  rw [allocPair, (spec w).clientState_bind, (spec w).clientState_bind]
  rfl

/-- Both handles. -/
theorem clientResult_allocPair (s : State) :
    (spec w).clientResult s (allocPair A₁ A₂) =
      ((spec w).clientResult s A₁.alloc,
        (spec w).clientResult ((spec w).clientState s A₁.alloc) A₂.alloc) := by
  rw [allocPair, (spec w).clientResult_bind, (spec w).clientResult_bind]
  rfl

variable {A₁}

/-- After allocating the first structure, room for both leaves room for the second. -/
theorem room_after {s : State} (hs₁ : A₁.Pre s) {r : ℕ}
    (hroom : Fits w (s.frontier + (A₁.room + r))) :
    Fits w (((spec w).clientState s A₁.alloc).frontier + r) :=
  hroom.of_le (by
    have := (A₁.allocates s hs₁ (hroom.of_le (by omega))).room_le
    omega)

/-- After allocating the first structure, the second one's precondition still holds. -/
theorem pre_after {s : State} (hs₁ : A₁.Pre s)
    (hroom : Fits w (s.frontier + (A₁.room + A₂.room))) (hs₂ : A₂.Pre s) :
    A₂.Pre ((spec w).clientState s A₁.alloc) :=
  A₂.pre_fresh hs₂ (A₁.allocates s hs₁ (hroom.of_le (by omega))).mem_eq
    (frontier_le_clientState s _) (room_after hs₁ hroom)

/-- After allocating the first structure, the second one takes over the same cells. -/
theorem owned_after {s : State} (hs₁ : A₁.Pre s)
    (hroom : Fits w (s.frontier + (A₁.room + A₂.room))) (hs₂ : A₂.Pre s) :
    A₂.owned ((spec w).clientState s A₁.alloc) = A₂.owned s :=
  A₂.owned_fresh hs₂ (A₁.allocates s hs₁ (hroom.of_le (by omega))).mem_eq
    (frontier_le_clientState s _) (room_after hs₁ hroom)

variable (A₁)

/-- The precondition of a product of allocators: both preconditions, and the cells that the two
structures take over are disjoint. -/
structure ProdPre (s : State) : Prop where
  /-- The first allocator's precondition. -/
  left : A₁.Pre s
  /-- The second allocator's precondition. -/
  right : A₂.Pre s
  /-- The two structures take over disjoint cells. -/
  disjoint : Disjoint (A₁.owned s) (A₂.owned s)

/-- **Products of allocators.** Allocate the two structures one after the other, and set up
their product over one memory. The room and the cost add, and the product takes over the cells
that either structure takes over. -/
def prod : Allocator (product D₁ D₂) w where
  Handle := A₁.Handle × A₂.Handle
  alloc := allocPair A₁ A₂
  methods := fun (h₁, h₂) => Methods.prod (A₁.methods h₁) (A₂.methods h₂)
  init := (A₁.init, A₂.init)
  room := A₁.room + A₂.room
  cost := A₁.cost + A₂.cost
  Pre := ProdPre A₁ A₂
  owned s := A₁.owned s ∪ A₂.owned s
  owned_lt hs ha := (Finset.mem_union.mp ha).elim (A₁.owned_lt hs.left) (A₂.owned_lt hs.right)
  pre_fresh hs hmem hf hr :=
    have hr₁ := hr.of_le (Nat.add_le_add_left (Nat.le_add_right A₁.room A₂.room) _)
    have hr₂ := hr.of_le (Nat.add_le_add_left (Nat.le_add_left A₂.room A₁.room) _)
    { left := A₁.pre_fresh hs.left hmem hf hr₁
      right := A₂.pre_fresh hs.right hmem hf hr₂
      disjoint := by
        rw [A₁.owned_fresh hs.left hmem hf hr₁, A₂.owned_fresh hs.right hmem hf hr₂]
        exact hs.disjoint }
  owned_fresh hs hmem hf hr := by
    rw [A₁.owned_fresh hs.left hmem hf
        (hr.of_le (Nat.add_le_add_left (Nat.le_add_right A₁.room A₂.room) _)),
      A₂.owned_fresh hs.right hmem hf
        (hr.of_le (Nat.add_le_add_left (Nat.le_add_left A₂.room A₁.room) _))]
  framed s hs hroom :=
    (A₁.framed s hs.left (hroom.of_le (by omega))).prod
      (A₂.framed ((spec w).clientState s A₁.alloc) (pre_after A₂ hs.left hroom hs.right)
        (room_after hs.left hroom))
  allocates s hs hroom := by
    -- The two allocations, from `s` to `s₁` and from `s₁` to `s₂`.
    obtain ⟨hs₁, hs₂, hd⟩ := hs
    have hroom₁ : Fits w (s.frontier + A₁.room) := hroom.of_le (by omega)
    have h₁ := A₁.allocates s hs₁ hroom₁
    have h₂ := A₂.allocates _ (pre_after A₂ hs₁ hroom hs₂) (room_after hs₁ hroom)
    have ho₂ := owned_after A₂ hs₁ hroom hs₂
    have hf₁ := frontier_le_clientState (w := w) s A₁.alloc
    have hfit := h₁.room_le
    have hfit₂ := h₂.room_le
    -- The second footprint lies in cells taken over, which are allocated and apart from the
    -- first structure's, and in cells fresh after the first allocation.
    obtain ⟨hinv, habs, hfp, hr⟩ := Framed.prod_of_fresh h₁.inv h₂.mem_eq
      (frontier_le_clientState _ _) h₂.inv
      (Finset.disjoint_left.mpr fun a ha ha' => by
        have hlt := (A₁.framed s hs₁ hroom₁).lt_frontier h₁.inv ha
        rcases h₂.of_mem_footprint a ha' with ha' | ha'
        · rw [ho₂] at ha'
          have := A₂.owned_lt hs₂ ha'
          rcases h₁.of_mem_footprint a ha with ha | ha
          · exact Finset.disjoint_left.mp hd ha ha'
          · omega
        · omega)
      (hroom.of_le (by omega))
    refine
      { validHistory := ?_, cost_le := ?_, mem_eq := ?_, methods_eq := ?_, inv := ?_,
        abs_eq := ?_, of_mem_footprint := ?_, room_le := ?_ }
    · rw [clientHistory_allocPair, StateTransitionSpec.validHistory_append,
        StateTransitionSpec.run_runClient]
      exact ⟨h₁.validHistory, h₂.validHistory⟩
    · rw [clientHistory_allocPair, StateTransitionSpec.totalCost_append,
        StateTransitionSpec.run_runClient]
      have := h₁.cost_le
      have := h₂.cost_le
      omega
    · intro a ha
      rw [clientState_allocPair, h₂.mem_eq a (ha.trans_le hf₁), h₁.mem_eq a ha]
    · rw [clientResult_allocPair, Framed.prod_methods, h₁.methods_eq, h₂.methods_eq]
    · rw [clientState_allocPair]
      exact hinv
    · rw [clientState_allocPair, habs, h₁.abs_eq, h₂.abs_eq]
    · intro a ha
      rw [clientState_allocPair, hfp] at ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (h₁.of_mem_footprint a ha).imp_left (Finset.mem_union_left _)
      · rcases h₂.of_mem_footprint a ha with ha | ha
        · rw [ho₂] at ha
          exact .inl (Finset.mem_union_right _ ha)
        · exact .inr (hf₁.trans ha)
    · rw [clientState_allocPair, hr]
      omega

/-- The product's methods run each side's methods with its own handle. -/
@[simp] theorem prod_methods (h₁ : A₁.Handle) (h₂ : A₂.Handle) :
    (A₁.prod A₂).methods (h₁, h₂) = Methods.prod (A₁.methods h₁) (A₂.methods h₂) := rfl

/-- The product sets up both abstract states. -/
@[simp] theorem prod_init : (A₁.prod A₂).init = (A₁.init, A₂.init) := rfl

/-- The product's room is the sum of the rooms. -/
@[simp] theorem prod_room : (A₁.prod A₂).room = A₁.room + A₂.room := rfl

/-- The product's allocation costs at most the sum of the costs. -/
@[simp] theorem prod_cost : (A₁.prod A₂).cost = A₁.cost + A₂.cost := rfl

/-- The product takes over the cells that either structure takes over. -/
@[simp] theorem prod_owned (s : State) :
    (A₁.prod A₂).owned s = A₁.owned s ∪ A₂.owned s := rfl

/-- The product's precondition. -/
theorem prod_pre_iff (s : State) : (A₁.prod A₂).Pre s ↔ ProdPre A₁ A₂ s := Iff.rfl

variable {A₁ A₂}

/-- **Certificates add across a product of allocators**: the charges componentwise, the
potentials once allocated by sum. -/
theorem Amortized.prod {upper₁ : D₁.State → D₁.Op → ℕ} {upper₂ : D₂.State → D₂.Op → ℕ}
    {Φ₁ Φ₂ : ℕ} (hA₁ : A₁.Amortized upper₁ Φ₁) (hA₂ : A₂.Amortized upper₂ Φ₂) :
    (A₁.prod A₂).Amortized (productCharge upper₁ upper₂) (Φ₁ + Φ₂) := by
  intro s hs hroom
  obtain ⟨hs₁, hs₂, -⟩ := hs
  have hroom₁ : Fits w (s.frontier + A₁.room) := hroom.of_le (by simp only [prod_room]; omega)
  have hs₂' := pre_after A₂ hs₁ hroom hs₂
  have hroom₂ := room_after hs₁ hroom
  obtain ⟨Ψ₁, hc₁, hl₁, hΨ₁⟩ := hA₁ s hs₁ hroom₁
  obtain ⟨Ψ₂, hc₂, hl₂, hΨ₂⟩ := hA₂ _ hs₂' hroom₂
  refine ⟨fun s' => Ψ₁ s' + Ψ₂ s', Framed.amortized_prod hc₁ hc₂ hl₁ hl₂,
    Framed.Local.add hl₁.prod_left hl₂.prod_right, ?_⟩
  -- The first potential is unchanged by the second allocation.
  have h₁ := A₁.allocates s hs₁ hroom₁
  have h₂ := A₂.allocates _ hs₂' hroom₂
  have hfit := h₁.room_le
  have hfit₂ := h₂.room_le
  have hkeep := hl₁ h₁.inv
    (fun a ha => h₂.mem_eq a ((A₁.framed s hs₁ hroom₁).lt_frontier h₁.inv ha))
    (frontier_le_clientState _ _) (hroom.of_le (by simp only [prod_room]; omega))
  change Ψ₁ ((spec w).clientState s (allocPair A₁ A₂)) +
    Ψ₂ ((spec w).clientState s (allocPair A₁ A₂)) ≤ Φ₁ + Φ₂
  rw [clientState_allocPair, hkeep]
  omega

end Prod

/-! ## Structures already in memory -/

section Resident

variable (M : Framed D w) (init : D.State) (room : ℕ)

/-- **A structure already in memory**, such as a graph that the input holds as adjacency arrays.
Its allocation does nothing. It takes over the footprint of `M`, and needs `M` to hold, to
represent `init` and to have at most `room` cells of room. -/
def resident : Allocator D w where
  Handle := Unit
  alloc := pure ()
  methods _ := M.methods
  init := init
  room := room
  cost := 0
  Pre s := M.inv s ∧ M.abs s = init ∧ M.room s ≤ room
  owned := M.footprint
  owned_lt hs ha := M.lt_frontier hs.1 ha
  pre_fresh {s _} hs hmem hf hr := by
    obtain ⟨hinv, habs, hle⟩ := hs
    obtain ⟨hinv', habs', -, hroom'⟩ := M.of_fresh hinv hmem hf (hr.of_le (by omega))
    exact ⟨hinv', habs'.trans habs, hroom' ▸ hle⟩
  owned_fresh {s _} hs hmem hf hr := by
    obtain ⟨hinv, -, hle⟩ := hs
    obtain ⟨-, -, hfp, -⟩ := M.of_fresh hinv hmem hf (hr.of_le (by omega))
    exact hfp
  framed _ _ _ := M
  allocates s hs _ := by
    obtain ⟨hinv, habs, hle⟩ := hs
    exact
      { validHistory := trivial
        cost_le := le_rfl
        mem_eq := fun _ _ => rfl
        methods_eq := rfl
        inv := hinv
        abs_eq := habs
        of_mem_footprint := fun _ ha => .inl ha
        room_le := Nat.add_le_add_left hle s.frontier }

/-- A structure already in memory runs `M`'s methods. -/
@[simp] theorem resident_methods (h : Unit) : (resident M init room).methods h = M.methods := rfl

/-- It represents `init`. -/
@[simp] theorem resident_init : (resident M init room).init = init := rfl

/-- It takes over `M`'s footprint. -/
@[simp] theorem resident_owned (s : State) : (resident M init room).owned s = M.footprint s := rfl

/-- Its allocation costs nothing. -/
@[simp] theorem resident_cost : (resident M init room).cost = 0 := rfl

/-- Its precondition: `M` holds, represents `init` and has at most `room` cells of room. -/
theorem resident_pre_iff (s : State) :
    (resident M init room).Pre s ↔ M.inv s ∧ M.abs s = init ∧ M.room s ≤ room := Iff.rfl

variable {M init room}

/-- **The certificate of a structure already in memory** is the structure's own: a potential
that reads only its footprint and is at most `Φ₀` wherever the structure represents `init`. -/
theorem Amortized.resident {upper : D.State → D.Op → ℕ} {Φ : State → ℕ} {Φ₀ : ℕ}
    (hc : M.Amortized charge upper Φ) (hl : M.Local Φ)
    (hΦ : ∀ s, M.inv s → M.abs s = init → Φ s ≤ Φ₀) :
    (resident M init room).Amortized upper Φ₀ := fun s hs _ => by
  obtain ⟨hinv, habs, -⟩ := hs
  exact ⟨Φ, hc, hl, hΦ s hinv habs⟩

end Resident

end Allocator

end Cslib.DataStructure.Memory
