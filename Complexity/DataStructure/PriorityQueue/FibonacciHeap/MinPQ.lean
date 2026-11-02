/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Memory

/-!
# A Fibonacci heap with handles and values over memory

The min-priority queue `minPQSpec n U V` stores key–value pairs and hands out its own handles.
It is implemented in two refinement steps over the indexed Fibonacci heap of `Memory.lean`:

1. `toAlloc`: the deterministic allocator `PriorityQueue.MinPQ.stepAlloc` (a stack of freed
   handles, then a bump pointer) refines the relational specification, by the existing
   `stepAlloc_refines_spec`.
2. `impl`: the allocator over the indexed heap beside a record of `Slot`s, the handles' values,
   the stack of freed handles, the bump pointer and the stack's height. Each operation calls the
   heap at most once and reads or writes at most four slots.

Both the heap and the slot record are allocated in memory (`FibonacciHeap.allocator`,
`Record.allocator`), side by side (`Memory.Allocator.prod`), and the two steps go on top
(`Memory.Allocator.comp`): `allocator`. The potentials stack (`amortized_allocator`), so every
operation costs `O(1)` memory units, amortized, but `extractMin`, which costs `O(log m)` on a
queue of `m` entries.

The module adapts Renfei Zhou's native formalization of the same structure
(`WordRAM/FibonacciHeap`, its `MinPQ.lean`) to the memory level: his value array, handle stack and
bump pointer become the slot record, and his allocator model `AllocState`/`stepAlloc` is reused
unchanged.

## Main definitions

* `allocSpec`: the deterministic allocator as a specification.
* `toAlloc`: the allocator refines `minPQSpec`.
* `Slot`, `Lower`, `allocState`, `Inv`, `methods`, `impl`: the allocator over the heap and the
  slots.
* `charge`: the amortized charges `1`, `3`, `47`, `104` and `extractCharge m + 4`.
* `allocator`: the queue allocated in memory.

## Main results

* `amortized_impl`: each operation costs its charge in calls to the heap and the slots.
* `amortized_allocator`: each operation costs its charge in memory units, amortized.
* `run_correct`, `run_cost`: a client of the queue run over memory.
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.MinPQ

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue

/-! ## The allocator as a specification -/

/-- The deterministic handle allocator `PriorityQueue.MinPQ.stepAlloc` as a specification, with
the admissibility of `minPQSpec`. -/
abbrev allocSpec (n U V : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := PriorityQueue.MinPQ.AllocState n)
    (Op := PriorityQueue.MinPQ.Op n) (Result := fun o => o.Result) PriorityQueue.MinPQ.stepAlloc
    fun s o => (minPQSpec n U V).valid s.entries o

/-- **The allocator refines the relational queue**: each of its deterministic choices of a
handle and of a minimum entry is one the specification allows. -/
def toAlloc (n U V : ℕ) : Refinement (minPQSpec n U V) (allocSpec n U V) where
  methods o := (allocSpec n U V).call o
  inv s := s.WellFormed
  abs s := s.entries
  valid o _ hv := ((allocSpec n U V).demonicValid_iff_validHistory_runClient _ _).mpr ⟨hv, trivial⟩
  correct {s} o {a s' tr} hi hv hrun := by
    obtain ⟨_, rfl, rfl, _⟩ :=
      ((allocSpec n U V).clientRun_iff_runClient s _ a s' tr).mp hrun
    exact PriorityQueue.MinPQ.stepAlloc_refines_spec hi o hv

/-! ## Slots beside the heap -/

/-- The words kept beside the heap. -/
inductive Slot where
  /-- The value stored with a handle. -/
  | val (h : ℕ)
  /-- An entry of the stack of freed handles, from the bottom. -/
  | free (i : ℕ)
  /-- The bump pointer: handles from here on were never used. -/
  | fresh
  /-- The height of the stack of freed handles. -/
  | top
  deriving DecidableEq

/-- The slots for `n` handles: `n` values, `n` stack entries, and two scalars. -/
def Slot.ok (n : ℕ) : Slot → Prop
  | .val h | .free h => h < n
  | .fresh | .top => True

instance (n : ℕ) : DecidablePred (Slot.ok n) := fun c => by
  cases c <;> unfold Slot.ok <;> infer_instance

/-- The lower interface: the indexed heap with keys at most `K`, beside the slots. -/
abbrev Lower (n K w : ℕ) : StateTransitionSpec :=
  product (indexedMinPQSpec n K) (Record.spec (Slot.ok n) w)

/-- The handle a word names, if any. -/
def toHandle (n x : ℕ) : Option (Fin n) := if h : x < n then some ⟨x, h⟩ else none

/-- The allocator state that the heap and the slots represent: the heap's keys with the slots'
values, the stack read from its top down, and the bump pointer. -/
def allocState {n : ℕ} : IndexedMinPQ.State n × (Slot → ℕ) → PriorityQueue.MinPQ.AllocState n
  | (s, g) =>
    ⟨fun h => (s h).map fun u => (u, g (.val h)),
      (List.range (g .top)).reverse.filterMap fun i => toHandle n (g (.free i)), g .fresh⟩

/-- The representation invariant: the allocator state is well formed, the stack holds handles,
and keys are at most `K`. -/
structure Inv (n K : ℕ) (s : IndexedMinPQ.State n) (g : Slot → ℕ) : Prop where
  wf : (allocState (s, g)).WellFormed
  free_lt : ∀ i < g .top, g (.free i) < n
  keys : ∀ h u, s h = some u → u ≤ K

section Programs

variable {n K w : ℕ}

/-- A call to the heap. -/
def heapOp (o : IndexedMinPQ.Op n) : (Lower n K w).Client o.Result := .liftBind (.inl o) .pure

/-- Read a slot. -/
def rd (c : Slot) : (Lower n K w).Client ℕ := .liftBind (.inr (.read c)) .pure

/-- Write a slot. -/
def wr (c : Slot) (x : ℕ) : (Lower n K w).Client Unit := .liftBind (.inr (.write c x)) .pure

/-- A heap call steps the heap. -/
@[simp] theorem runClient_heapOp_bind {α : Type} (s : IndexedMinPQ.State n) (g : Slot → ℕ)
    (o : IndexedMinPQ.Op n) (k : o.Result → (Lower n K w).Client α) :
    (Lower n K w).runClient (s, g) (heapOp o >>= k) =
      let (v, e, os) := (Lower n K w).runClient ((IndexedMinPQ.step s o).1, g)
        (k (IndexedMinPQ.step s o).2)
      (v, e, .inl o :: os) := rfl

/-- A read answers the slot. -/
@[simp] theorem runClient_rd_bind {α : Type} (s : IndexedMinPQ.State n) (g : Slot → ℕ) (c : Slot)
    (k : ℕ → (Lower n K w).Client α) :
    (Lower n K w).runClient (s, g) (rd c >>= k) =
      let (v, e, os) := (Lower n K w).runClient (s, g) (k (g c))
      (v, e, .inr (.read c) :: os) := rfl

/-- A write updates the slot. -/
@[simp] theorem runClient_wr_bind {α : Type} (s : IndexedMinPQ.State n) (g : Slot → ℕ) (c : Slot)
    (x : ℕ) (k : Unit → (Lower n K w).Client α) :
    (Lower n K w).runClient (s, g) (wr c x >>= k) =
      let (v, e, os) := (Lower n K w).runClient (s, Function.update g c x) (k ())
      (v, e, .inr (.write c x) :: os) := rfl

/-- Admissibility of a heap call. -/
@[simp] theorem validHistory_heapOp_cons (s : IndexedMinPQ.State n) (g : Slot → ℕ)
    (o : IndexedMinPQ.Op n) (os : List (Lower n K w).Op) :
    (Lower n K w).ValidHistory (s, g) (.inl o :: os) ↔
      IndexedMinPQ.valid K s o ∧ (Lower n K w).ValidHistory ((IndexedMinPQ.step s o).1, g) os :=
  Iff.rfl

/-- Admissibility of a read. -/
@[simp] theorem validHistory_rd_cons (s : IndexedMinPQ.State n) (g : Slot → ℕ) (c : Slot)
    (os : List (Lower n K w).Op) :
    (Lower n K w).ValidHistory (s, g) (.inr (.read c) :: os) ↔
      Slot.ok n c ∧ (Lower n K w).ValidHistory (s, g) os :=
  Iff.rfl

/-- Admissibility of a write. -/
@[simp] theorem validHistory_wr_cons (s : IndexedMinPQ.State n) (g : Slot → ℕ) (c : Slot)
    (x : ℕ) (os : List (Lower n K w).Op) :
    (Lower n K w).ValidHistory (s, g) (.inr (.write c x) :: os) ↔
      (Slot.ok n c ∧ Fits w x) ∧ (Lower n K w).ValidHistory (s, Function.update g c x) os :=
  Iff.rfl

/-- The queue's operations over the heap and the slots. -/
def methods (n U V K w : ℕ) : Methods (allocSpec n U V) (Lower n K w)
  | .isEmpty => do
    let b ← heapOp (n := n) (K := K) (w := w) .isEmpty
    pure b
  | .get h => do
    let k ← heapOp (n := n) (K := K) (w := w) (.getKey h)
    match k with
    | none => pure none
    | some u => do
      let v ← rd (.val h)
      pure (some (u, v))
  | .insert u v => do
    let t ← rd (n := n) (K := K) (w := w) .top
    if t = 0 then do
      let f ← rd .fresh
      if hf : f < n then do
        wr .fresh (f + 1)
        wr (.val f) v
        heapOp (.insert ⟨f, hf⟩ u)
        pure (some ⟨f, hf⟩)
      else pure none
    else do
      wr .top (t - 1)
      let x ← rd (.free (t - 1))
      match toHandle n x with
      | none => pure none
      | some h => do
        wr (.val h) v
        heapOp (.insert h u)
        pure (some h)
  | .decreaseKey h u' => do
    heapOp (n := n) (K := K) (w := w) (.decreaseKey h u')
    pure ()
  | .extractMin => do
    let r ← heapOp (n := n) (K := K) (w := w) .extractMin
    match r with
    | none => pure none
    | some (h, u) => do
      let v ← rd (.val h)
      let t ← rd .top
      wr (.free t) h
      wr .top (t + 1)
      pure (some (u, v, h))

end Programs

/-! ## The allocator over the heap and the slots -/

section Impl

variable {n U V K w : ℕ} {s : IndexedMinPQ.State n} {g : Slot → ℕ}

/-- The allocator's entries forget the values into the heap's keys. -/
theorem toIndexed_allocState :
    PriorityQueue.MinPQ.toIndexed (allocState (s, g)).entries = s := by
  funext h
  cases hs : s h <;> simp [PriorityQueue.MinPQ.toIndexed_apply, allocState, hs]

/-- The allocator and the heap hold the same handles. -/
theorem dom_allocState :
    PriorityQueue.MinPQ.dom (allocState (s, g)).entries = IndexedMinPQ.dom s := by
  rw [← PriorityQueue.MinPQ.dom_toIndexed, toIndexed_allocState]

/-- `isEmpty` asks the heap. -/
theorem run_isEmpty : (Lower n K w).runClient (s, g) (methods n U V K w .isEmpty) =
    (decide (IndexedMinPQ.dom s = ∅), (s, g), [.inl .isEmpty]) := rfl

/-- `get h` asks the heap for the key, and reads the value if `h` is present. -/
theorem run_get (h : Fin n) :
    (Lower n K w).runClient (s, g) (methods n U V K w (.get h)) =
      match s h with
      | none => (none, (s, g), [.inl (.getKey h)])
      | some u => (some (u, g (.val h)), (s, g), [.inl (.getKey h), .inr (.read (.val h))]) := by
  rw [methods, runClient_heapOp_bind]
  simp only [IndexedMinPQ.step]
  cases s h with
  | none => rfl
  | some u =>
    simp only
    rw [runClient_rd_bind]
    rfl

/-- `decreaseKey h u'` lowers the key in the heap. -/
theorem run_decreaseKey (h : Fin n) (u' : ℕ) :
    (Lower n K w).runClient (s, g) (methods n U V K w (.decreaseKey h u')) =
      ((), (Function.update s h (some u'), g), [.inl (.decreaseKey h u')]) := rfl

/-- `insert u v` with no freed handle takes the bump pointer's. -/
theorem run_insert_fresh {u v : ℕ} (ht : g .top = 0) (hf : g .fresh < n) :
    (Lower n K w).runClient (s, g) (methods n U V K w (.insert u v)) =
      (some ⟨g .fresh, hf⟩, (Function.update s ⟨g .fresh, hf⟩ (some u),
        Function.update (Function.update g .fresh (g .fresh + 1)) (.val (g .fresh)) v),
        [.inr (.read .top), .inr (.read .fresh), .inr (.write .fresh (g .fresh + 1)),
          .inr (.write (.val (g .fresh)) v), .inl (.insert ⟨g .fresh, hf⟩ u)]) := by
  rw [methods, runClient_rd_bind]
  simp only [ht, ite_true]
  rw [runClient_rd_bind]
  simp only [hf, dite_true]
  rw [runClient_wr_bind, runClient_wr_bind, runClient_heapOp_bind]
  rfl

/-- `insert u v` pops the top freed handle `h`. -/
theorem run_insert_pop {u v : ℕ} {h : Fin n} (ht : g .top ≠ 0)
    (hh : toHandle n (g (.free (g .top - 1))) = some h) :
    (Lower n K w).runClient (s, g) (methods n U V K w (.insert u v)) =
      (some h, (Function.update s h (some u),
        Function.update (Function.update g .top (g .top - 1)) (.val h) v),
        [.inr (.read .top), .inr (.write .top (g .top - 1)), .inr (.read (.free (g .top - 1))),
          .inr (.write (.val h) v), .inl (.insert h u)]) := by
  rw [methods, runClient_rd_bind]
  simp only [ht, ite_false]
  rw [runClient_wr_bind, runClient_rd_bind]
  simp only [Function.update_apply, reduceCtorEq, ite_false, hh]
  rw [runClient_wr_bind, runClient_heapOp_bind]
  rfl

/-- `extractMin` takes the heap's minimum, reads its value, and pushes its handle. -/
theorem run_extractMin :
    (Lower n K w).runClient (s, g) (methods n U V K w .extractMin) =
      match IndexedMinPQ.findMin s with
      | none => (none, (s, g), [.inl .extractMin])
      | some (h, u) => (some (u, g (.val h), h), (Function.update s h none,
          Function.update (Function.update g (.free (g .top)) h) .top (g .top + 1)),
          [.inl .extractMin, .inr (.read (.val h)), .inr (.read .top),
            .inr (.write (.free (g .top)) h), .inr (.write .top (g .top + 1))]) := by
  rw [methods, runClient_heapOp_bind]
  simp only [IndexedMinPQ.step]
  cases IndexedMinPQ.findMin s with
  | none => rfl
  | some p =>
    obtain ⟨h, u⟩ := p
    simp only
    rw [runClient_rd_bind, runClient_rd_bind, runClient_wr_bind, runClient_wr_bind]
    rfl

/-- The stack lists the handles of its `top` cells. -/
theorem length_freeList (hfree : ∀ i < g .top, g (.free i) < n) :
    (allocState (s, g)).freeList.length = g .top := by
  change ((List.range (g .top)).reverse.filterMap fun i => toHandle n (g (.free i))).length = _
  rw [List.length_filterMap_eq_countP, List.countP_eq_length.mpr, List.length_reverse,
    List.length_range]
  intro i hi
  simp only [List.mem_reverse, List.mem_range] at hi
  simp [toHandle, hfree i hi]

/-- The stack's top cell holds the head of the free list. -/
theorem freeList_eq_cons {t : ℕ} (ht : g .top = t + 1) :
    (allocState (s, g)).freeList = (toHandle n (g (.free t))).toList ++
      (List.range t).reverse.filterMap fun i => toHandle n (g (.free i)) := by
  change (List.range (g .top)).reverse.filterMap _ = _
  rw [ht, List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.filterMap_cons]
  cases toHandle n (g (.free t)) <;> rfl

/-- The free list read from slots that agree on the stack. -/
theorem filterMap_congr {g' : Slot → ℕ} {t : ℕ} (h : ∀ i < t, g' (.free i) = g (.free i)) :
    ((List.range t).reverse.filterMap fun i => toHandle n (g' (.free i))) =
      (List.range t).reverse.filterMap fun i => toHandle n (g (.free i)) :=
  List.filterMap_congr fun i hi => by
    rw [h i (List.mem_range.mp (List.mem_reverse.mp hi))]

/-- The representation: `Inv` of the heap's state and the slots. -/
def Rep (n K : ℕ) : IndexedMinPQ.State n × (Slot → ℕ) → Prop
  | (s, g) => Inv n K s g

/-- **Each operation does what the allocator does**, admissibly, and keeps the invariant. -/
theorem methods_spec (hn : Fits w n) (hV : Fits w V) (hI : Inv n U s g)
    (o : PriorityQueue.MinPQ.Op n) (hv : (minPQSpec n U V).valid (allocState (s, g)).entries o) :
    (Lower n U w).ValidHistory (s, g) ((Lower n U w).clientHistory (s, g) (methods n U V U w o)) ∧
      PriorityQueue.MinPQ.stepAlloc (allocState (s, g)) o =
        (allocState ((Lower n U w).clientState (s, g) (methods n U V U w o)),
          (Lower n U w).clientResult (s, g) (methods n U V U w o)) ∧
      Rep n U ((Lower n U w).clientState (s, g) (methods n U V U w o)) := by
  have hwf' := (PriorityQueue.MinPQ.stepAlloc_refines_spec hI.wf o hv).2
  obtain ⟨⟨hfr_le, -, hfl_none, hbump, hsum⟩, hfree, hkeys⟩ := hI
  have hlen := length_freeList (s := s) hfree
  simp only [StateTransitionSpec.clientHistory, StateTransitionSpec.clientState,
    StateTransitionSpec.clientResult]
  cases o with
  | isEmpty =>
    rw [run_isEmpty]
    refine ⟨⟨trivial, trivial⟩, by simp [PriorityQueue.MinPQ.stepAlloc, dom_allocState],
      ⟨hwf', hfree, hkeys⟩⟩
  | get h =>
    rw [run_get]
    cases hs : s h with
    | none =>
      refine ⟨⟨trivial, trivial⟩, by simp [PriorityQueue.MinPQ.stepAlloc, allocState, hs],
        ⟨hwf', hfree, hkeys⟩⟩
    | some u =>
      refine ⟨⟨trivial, h.isLt, trivial⟩, by simp [PriorityQueue.MinPQ.stepAlloc, allocState, hs],
        ⟨hwf', hfree, hkeys⟩⟩
  | decreaseKey h u' =>
    obtain ⟨u, v, huv, hu'⟩ := hv
    have hs : s h = some u ∧ g (.val h) = v := by
      cases hsh : s h <;> simp_all [allocState]
    rw [run_decreaseKey]
    have heq : PriorityQueue.MinPQ.stepAlloc (allocState (s, g)) (.decreaseKey h u') =
        (allocState (Function.update s h (some u'), g), ()) := by
      simp only [PriorityQueue.MinPQ.stepAlloc, huv]
      congr 2
      funext h'
      by_cases hh : h' = h
      · subst hh
        simp [allocState, hs.2]
      · simp [allocState, hh]
    refine ⟨⟨⟨⟨u, hs.1, hu'⟩, hu'.trans (hkeys h u hs.1)⟩, trivial⟩, heq,
      ⟨by rw [heq] at hwf'; exact hwf', hfree, fun h' k hk => ?_⟩⟩
    by_cases hh : h' = h
    · subst hh
      simp only [Function.update_self, Option.some.injEq] at hk
      exact hk ▸ hu'.trans (hkeys _ u hs.1)
    · rw [Function.update_of_ne hh] at hk
      exact hkeys h' k hk
  | insert u v =>
    obtain ⟨hsz, hu, hvV⟩ := hv
    have hfresh : (allocState (s, g)).fresh = g .fresh := rfl
    have htop_le : g .top ≤ n := by omega
    by_cases ht : g .top = 0
    · have hf : g .fresh < n := by omega
      rw [run_insert_fresh ht hf]
      have hnone : s ⟨g .fresh, hf⟩ = none := by
        have := hbump ⟨g .fresh, hf⟩ le_rfl
        simpa [allocState] using this
      have hah : PriorityQueue.MinPQ.allocHandle (allocState (s, g)) =
          some (⟨g .fresh, hf⟩, [], g .fresh + 1) := by
        have hfl0 : (allocState (s, g)).freeList = [] := by simp [allocState, ht]
        unfold PriorityQueue.MinPQ.allocHandle
        rw [hfl0]
        simp only [hfresh, hf, ↓reduceDIte]
      have heq : PriorityQueue.MinPQ.stepAlloc (allocState (s, g)) (.insert u v) =
          (allocState (Function.update s ⟨g .fresh, hf⟩ (some u),
            Function.update (Function.update g .fresh (g .fresh + 1)) (.val (g .fresh)) v),
            some ⟨g .fresh, hf⟩) := by
        simp only [PriorityQueue.MinPQ.stepAlloc, hah]
        refine Prod.ext ?_ rfl
        change (⟨_, _, _⟩ : PriorityQueue.MinPQ.AllocState n) = ⟨_, _, _⟩
        congr 1
        · funext h'
          by_cases hh : h' = ⟨g .fresh, hf⟩
          · subst hh
            simp [allocState]
          · have hv' : (Slot.val h'.val) ≠ .val (g .fresh) := fun e =>
              hh (Fin.ext (Slot.val.inj e))
            simp [allocState, hh, Function.update_of_ne hv']
        · simp [ht]
      refine ⟨⟨trivial, trivial, ⟨trivial, hn.of_le hf⟩, ⟨hf, hV.of_le hvV.le⟩,
        ⟨hnone, hu.le⟩, trivial⟩, heq, ⟨by rw [heq] at hwf'; exact hwf', fun i hi => ?_,
        fun h' k hk => ?_⟩⟩
      · simp [ht] at hi
      · by_cases hh : h' = ⟨g .fresh, hf⟩
        · subst hh
          simp only [Function.update_self, Option.some.injEq] at hk
          omega
        · rw [Function.update_of_ne hh] at hk
          exact hkeys h' k hk
    · obtain ⟨t, ht'⟩ : ∃ t, g .top = t + 1 := ⟨g .top - 1, by omega⟩
      have hfl₀ := freeList_eq_cons (s := s) ht'
      have htn : g (.free t) < n := hfree t (by omega)
      set h : Fin n := ⟨g (.free t), htn⟩ with hh_def
      have hh : toHandle n (g (.free (g .top - 1))) = some h := by
        simp [toHandle, ht', htn, h]
      have hmem : h ∈ (allocState (s, g)).freeList := by
        rw [hfl₀]
        simp [toHandle, htn, h]
      have hnone : s h = none := by
        have := (hfl_none h hmem).2
        simpa [allocState] using this
      rw [run_insert_pop ht hh]
      have hah : PriorityQueue.MinPQ.allocHandle (allocState (s, g)) =
          some (h, (List.range t).reverse.filterMap fun i => toHandle n (g (.free i)),
            g .fresh) := by
        unfold PriorityQueue.MinPQ.allocHandle
        rw [hfl₀]
        simp [toHandle, htn, h, hfresh]
      have heq : PriorityQueue.MinPQ.stepAlloc (allocState (s, g)) (.insert u v) =
          (allocState (Function.update s h (some u),
            Function.update (Function.update g .top (g .top - 1)) (.val h) v), some h) := by
        simp only [PriorityQueue.MinPQ.stepAlloc, hah]
        refine Prod.ext ?_ rfl
        change (⟨_, _, _⟩ : PriorityQueue.MinPQ.AllocState n) = ⟨_, _, _⟩
        congr 1
        · funext h'
          by_cases hh' : h' = h
          · subst hh'
            simp [allocState]
          · have hv' : (Slot.val h'.val) ≠ .val h.val := fun e => hh' (Fin.ext (Slot.val.inj e))
            simp [allocState, hh', Function.update_of_ne hv']
        · change _ = (List.range (Function.update (Function.update g .top (g .top - 1))
            (.val h) v .top)).reverse.filterMap _
          simp only [Function.update_apply, reduceCtorEq, ite_false, ite_true, ht',
            Nat.add_sub_cancel]
      refine ⟨⟨trivial, ⟨trivial, hn.of_le (by omega)⟩, (by change g .top - 1 < n; omega),
        ⟨h.isLt, hV.of_le hvV.le⟩, ⟨hnone, hu.le⟩, trivial⟩, heq,
        ⟨by rw [heq] at hwf'; exact hwf', fun i hi => ?_, fun h' k hk => ?_⟩⟩
      · simp only [Function.update_apply, reduceCtorEq, ite_false, ite_true, ht',
          Nat.add_sub_cancel] at hi ⊢
        exact hfree i (by omega)
      · by_cases hh' : h' = h
        · subst hh'
          simp only [Function.update_self, Option.some.injEq] at hk
          omega
        · rw [Function.update_of_ne hh'] at hk
          exact hkeys h' k hk
  | extractMin =>
    rw [run_extractMin]
    rcases hfm : IndexedMinPQ.findMin s with _ | ⟨h, u⟩
    · have hemp : PriorityQueue.MinPQ.findMin (allocState (s, g)).entries = none := by
        rw [PriorityQueue.MinPQ.findMin_eq_none_iff, dom_allocState]
        exact IndexedMinPQ.findMin_eq_none_iff.mp hfm
      have heq : PriorityQueue.MinPQ.stepAlloc (allocState (s, g)) .extractMin =
          (allocState (s, g), none) := by
        simp only [PriorityQueue.MinPQ.stepAlloc, hemp]
      refine ⟨⟨trivial, trivial⟩, heq, ⟨by rw [heq] at hwf'; exact hwf', hfree, hkeys⟩⟩
    · obtain ⟨v', hAe, hmf, -⟩ := PriorityQueue.MinPQ.findMin_eq_some_of_indexed
        (s := (allocState (s, g)).entries) (by rw [toIndexed_allocState]; exact hfm)
      have hs : s h = some u ∧ g (.val h) = v' := by
        cases hsh : s h <;> simp_all [allocState]
      have hpos : 1 ≤ PriorityQueue.MinPQ.size (allocState (s, g)).entries :=
        Finset.card_pos.mpr ⟨h, PriorityQueue.MinPQ.mem_dom_iff.mpr ⟨u, v', hAe⟩⟩
      have htn : g .top + 1 ≤ n := by omega
      have heq : PriorityQueue.MinPQ.stepAlloc (allocState (s, g)) .extractMin =
          (allocState (Function.update s h none,
            Function.update (Function.update g (.free (g .top)) h) .top (g .top + 1)),
            some (u, g (.val h), h)) := by
        simp only [PriorityQueue.MinPQ.stepAlloc, hmf, hs.2]
        refine Prod.ext ?_ rfl
        change (⟨_, _, _⟩ : PriorityQueue.MinPQ.AllocState n) = ⟨_, _, _⟩
        congr 1
        · funext h'
          by_cases hh' : h' = h
          · subst hh'
            simp [allocState]
          · simp [allocState, hh']
        · change h :: (allocState (s, g)).freeList = (allocState (Function.update s h none,
            Function.update (Function.update g (.free (g .top)) h) .top (g .top + 1))).freeList
          rw [freeList_eq_cons (s := Function.update s h none)
            (g := Function.update (Function.update g (.free (g .top)) h) .top (g .top + 1))
            (t := g .top) (by simp)]
          rw [filterMap_congr (g := g) fun i hi => by simp [Nat.ne_of_lt hi]]
          simp [toHandle, allocState]
      refine ⟨⟨trivial, h.isLt, trivial, ⟨by simp only [Slot.ok]; omega, hn.of_le h.isLt.le⟩,
        ⟨trivial, hn.of_le htn⟩, trivial⟩, heq,
        ⟨by rw [heq] at hwf'; exact hwf', fun i hi => ?_, fun h' k hk => ?_⟩⟩
      · simp only [Function.update_apply, reduceCtorEq, ite_false, ite_true] at hi ⊢
        by_cases hit : i = g .top
        · simp [hit]
        · simp only [Slot.free.injEq, hit, ite_false]
          exact hfree i (by omega)
      · by_cases hh' : h' = h
        · subst hh'
          simp at hk
        · rw [Function.update_of_ne hh'] at hk
          exact hkeys h' k hk

/-- **The allocator over the heap and the slots.** -/
def impl (hn : Fits w n) (hV : Fits w V) : Refinement (allocSpec n U V) (Lower n U w) :=
  Refinement.ofFn (methods n U V U w) (Rep n U) allocState
    (fun {e} o hI hv => by
      obtain ⟨s, g⟩ := e
      exact (methods_spec hn hV hI o hv).1)
    (fun {e} o hI hv => by
      obtain ⟨s, g⟩ := e
      exact (methods_spec hn hV hI o hv).2)

end Impl

/-! ## Costs -/

/-- The amortized charge of each operation on a queue `s`, in memory units: one heap call and up
to four slot operations, with the heap's charges. -/
def charge (n : ℕ) (s : PriorityQueue.MinPQ.State n) : PriorityQueue.MinPQ.Op n → ℕ
  | .isEmpty => 1
  | .get _ => 3
  | .insert _ _ => 4 + 19 + credit
  | .decreaseKey _ _ => 104
  | .extractMin => extractCharge (PriorityQueue.MinPQ.size s) + 4

/-- The charges on the allocator's states. -/
def allocCharge (n : ℕ) (s : PriorityQueue.MinPQ.AllocState n) (o : PriorityQueue.MinPQ.Op n) :
    ℕ :=
  charge n s.entries o

/-- Each allocator call is one call. -/
theorem amortized_toAlloc (n U V : ℕ) :
    (toAlloc n U V).Amortized (allocCharge n) (charge n) fun _ => 0 :=
  Refinement.Amortized.ofFn fun _ _ _ => le_refl _

/-- **Each operation costs its charge** in heap charges and slot operations. -/
theorem amortized_impl {n U V w : ℕ} (hn : Fits w n) (hV : Fits w V) :
    (impl (U := U) hn hV).Amortized (productCharge (FibonacciHeap.charge n) fun _ _ => 1)
      (allocCharge n) fun _ => 0 := by
  refine Refinement.Amortized.ofFn fun {e} o hI hv => ?_
  obtain ⟨s, g⟩ := e
  obtain ⟨⟨hfr_le, -, -, -, hsum⟩, hfree, -⟩ := hI
  have hlen := length_freeList (s := s) hfree
  simp only [StateTransitionSpec.clientHistory, Nat.add_zero]
  change (Lower n U w).totalCost _ (s, g)
    ((Lower n U w).runClient (s, g) (methods n U V U w o)).2.2 ≤
      charge n (allocState (s, g)).entries o
  cases o with
  | isEmpty => rw [run_isEmpty]; rfl
  | get h =>
    rw [run_get]
    cases s h <;> simp [StateTransitionSpec.totalCost, productCharge, FibonacciHeap.charge, charge]
  | decreaseKey h u' => rw [run_decreaseKey]; rfl
  | insert u v =>
    have hsz : PriorityQueue.MinPQ.size (allocState (s, g)).entries < n := hv.1
    have hfresh : (allocState (s, g)).fresh = g .fresh := rfl
    by_cases ht : g .top = 0
    · have hf : g .fresh < n := by omega
      rw [run_insert_fresh ht hf]
      simp [StateTransitionSpec.totalCost, productCharge, FibonacciHeap.charge, charge, credit]
    · obtain ⟨t, ht'⟩ : ∃ t, g .top = t + 1 := ⟨g .top - 1, by omega⟩
      have htn : g (.free t) < n := hfree t (by omega)
      have hh : toHandle n (g (.free (g .top - 1))) = some ⟨g (.free t), htn⟩ := by
        simp [toHandle, ht', htn]
      rw [run_insert_pop ht hh]
      simp [StateTransitionSpec.totalCost, productCharge, FibonacciHeap.charge, charge, credit]
  | extractMin =>
    rw [run_extractMin]
    rcases hfm : IndexedMinPQ.findMin s with _ | ⟨h, u⟩ <;>
      simp [StateTransitionSpec.totalCost, productCharge, FibonacciHeap.charge, charge,
        ← dom_allocState (g := g), PriorityQueue.MinPQ.size]

/-! ## In memory -/

/-- The slots at `2 n + 2` consecutive cells from `base`: values, stack, bump pointer, height. -/
def slotLayout (n base : ℕ) : Record.Layout (Slot.ok n) where
  addr
    | .val h => base + h
    | .free i => base + n + i
    | .fresh => base + 2 * n
    | .top => base + 2 * n + 1
  addr_injOn i j hi hj h := by
    cases i <;> cases j <;> simp only [Slot.ok, Slot.val.injEq, Slot.free.injEq,
      reduceCtorEq] at h hi hj ⊢ <;> omega

/-- Allocating the slots: `2 n + 2` zeroed cells, the height last. -/
def slotAllocator (n w : ℕ) : Memory.Allocator (Record.spec (Slot.ok n) w) w :=
  Record.allocator (slotLayout n) (2 * n + 2) w
    (fun _ i hi => by cases i <;> simp only [slotLayout, Slot.ok] at hi ⊢ <;> omega)
    fun _ => ⟨.top, trivial, by simp only [slotLayout]; omega⟩

variable {n U V w : ℕ}

/-- Every slot operation costs one memory unit. -/
theorem amortized_slotAllocator : (slotAllocator n w).Amortized (fun _ _ => 1) 0 :=
  Record.amortized_allocator

/-- The zeroed heap and slots represent the empty allocator. -/
theorem rep_init (hn : Fits w n) (hU : Fits w U) :
    Rep n U ((FibonacciHeap.allocator hn hU).prod (slotAllocator n w)).init := by
  refine ⟨?_, fun _ hi => absurd hi (Nat.not_lt_zero _), fun h u hu => ?_⟩
  · have he : allocState ((FibonacciHeap.allocator hn hU).prod (slotAllocator n w)).init =
        PriorityQueue.MinPQ.AllocState.empty n := by
      rfl
    change (allocState ((FibonacciHeap.allocator hn hU).prod (slotAllocator n w)).init).WellFormed
    rw [he]
    exact PriorityQueue.MinPQ.AllocState.wellFormed_empty n
  · change FibonacciHeap.abs n (fun _ => 0) h = some u at hu
    simp [FibonacciHeap.absRaw, view] at hu

/-- **The allocator over memory**: the heap and the slots allocated side by side, with the
allocator on top. It answers deterministically. -/
def allocAllocator (hn : Fits w n) (hU : Fits w U) (hV : Fits w V) :
    Memory.Allocator (allocSpec n U V) w :=
  ((FibonacciHeap.allocator hn hU).prod (slotAllocator n w)).comp (impl hn hV) (rep_init hn hU)

/-- The allocated allocator is well formed. -/
theorem wellFormed_init (hn : Fits w n) (hU : Fits w U) (hV : Fits w V) :
    (toAlloc n U V).inv (allocAllocator hn hU hV).init :=
  (rep_init hn hU).wf

/-- **The min-priority queue over memory**, as a `Memory.Allocator` for `minPQSpec`, so that it
composes with other structures in one memory. -/
def allocator (hn : Fits w n) (hU : Fits w U) (hV : Fits w V) :
    Memory.Allocator (minPQSpec n U V) w :=
  (allocAllocator hn hU hV).comp (toAlloc n U V) (wellFormed_init hn hU hV)

/-- **Stacked potentials**, deterministic form: every operation costs its `allocCharge` in memory
units, amortized, with no potential once allocated. -/
theorem amortized_allocAllocator (hn : Fits w n) (hU : Fits w U) (hV : Fits w V) :
    (allocAllocator hn hU hV).Amortized (allocCharge n) 0 := by
  have h := Memory.Allocator.Amortized.comp (hinit := rep_init hn hU)
    (amortized_impl (U := U) hn hV)
    ((FibonacciHeap.amortized_allocator hn hU).prod amortized_slotAllocator)
  simp only [Nat.add_zero] at h
  exact h

/-- **Stacked potentials**: every operation costs its `charge` in memory units, amortized, with no
potential once allocated. -/
theorem amortized_allocator (hn : Fits w n) (hU : Fits w U) (hV : Fits w V) :
    (allocator hn hU hV).Amortized (charge n) 0 := by
  have h := Memory.Allocator.Amortized.comp (hinit := wellFormed_init hn hU hV)
    (amortized_toAlloc n U V) (amortized_allocAllocator hn hU hV)
  simp only [Nat.add_zero] at h
  exact h

/-- Nothing is needed of the memory but room. -/
theorem pre_allocAllocator (hn : Fits w n) (hU : Fits w U) (hV : Fits w V) (s : Memory.State) :
    (allocAllocator hn hU hV).Pre s :=
  ⟨trivial, trivial, Finset.disjoint_empty_left _⟩

/-- **Correctness of a run.** From a memory with room for the heap and the slots, an admissible
client of the allocator issues admissible memory operations and answers as the allocator does
from the empty queue. -/
theorem run_correct (hn : Fits w n) (hU : Fits w U) (hV : Fits w V) {β : Type}
    (p : (allocSpec n U V).Client β) {s : Memory.State}
    (hroom : Fits w (s.frontier + (allocAllocator hn hU hV).room))
    (hv : (allocSpec n U V).ValidHistory (allocAllocator hn hU hV).init
      ((allocSpec n U V).clientHistory (allocAllocator hn hU hV).init p)) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
        ((allocAllocator hn hU hV).run p)) ∧
      (Memory.spec w).clientResult s ((allocAllocator hn hU hV).run p) =
        (allocSpec n U V).clientResult (allocAllocator hn hU hV).init p :=
  have ⟨hvE, hres, _⟩ := (allocAllocator hn hU hV).run_correct p
    (pre_allocAllocator hn hU hV s) hroom hv
  ⟨hvE, hres⟩

/-- **Cost of a run**: the allocation's cost plus the charges of the client's operations. -/
theorem run_cost (hn : Fits w n) (hU : Fits w U) (hV : Fits w V) {β : Type}
    (p : (allocSpec n U V).Client β) {s : Memory.State}
    (hroom : Fits w (s.frontier + (allocAllocator hn hU hV).room))
    (hv : (allocSpec n U V).ValidHistory (allocAllocator hn hU hV).init
      ((allocSpec n U V).clientHistory (allocAllocator hn hU hV).init p)) :
    (Memory.spec w).totalCost Memory.charge s ((Memory.spec w).clientHistory s
        ((allocAllocator hn hU hV).run p)) ≤
      (allocAllocator hn hU hV).cost + (allocSpec n U V).totalCost (allocCharge n)
        (allocAllocator hn hU hV).init ((allocSpec n U V).clientHistory
          (allocAllocator hn hU hV).init p) := by
  simpa using Memory.Allocator.run_cost (amortized_allocAllocator hn hU hV) p
    (pre_allocAllocator hn hU hV s) hroom hv


end Cslib.DataStructure.PriorityQueue.FibonacciHeap.MinPQ
