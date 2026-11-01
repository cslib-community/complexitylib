/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: local-only (test driver)

public import Complexity.Tactic.Stateful

/-!
# Adaptive resource contracts through two interface implementations

An abstract counter is implemented with a mutable cell, which is implemented using the first
component of a pair. The second component is hidden storage. A client reads the counter and
increments it only when the answer is zero. Costs count the supplied primitive evidence:
reads cost two and writes cost three. No whole-machine runtime bound is asserted.
-/

@[expose] public section

namespace Cslib.Stateful.Tests

/-- A counter supporting reads and increments. -/
abbrev counter : Spec :=
  Spec.ofFn (State := Nat) (Op := Bool) (Result := fun _ => Nat) fun s inc =>
    if inc then (s + 1, s + 1) else (s, s)

/-- A mutable natural-number cell. -/
abbrev cell : Spec :=
  Spec.ofFn (State := Nat) (Op := Option Nat) (Result := fun _ => Nat) fun s o => match o with
    | none => (s, s)
    | some n => (n, n)

/-- Two independent mutable cells. -/
abbrev storage : Spec := product cell cell

/-- Budget for a counter operation realized with reads and writes. -/
def counterCharge (_ : Nat) (inc : Bool) : Nat := if inc then 5 else 2

/-- Primitive read and write costs. -/
def cellCharge (_ : Nat) : Option Nat → Nat
  | none => 2
  | some _ => 3

/-- Charge the selected component. -/
def storageCharge (s : Nat × Nat) : storage.Op → Nat
  | .inl o => cellCharge s.1 o
  | .inr o => cellCharge s.2 o

/-- Implement increments by reading and writing a cell. -/
def counterModule : Module counter cell :=
  Module.ofFn
    (fun inc => .liftBind none fun (n : Nat) =>
      if inc then .liftBind (some (n + 1)) fun m => .pure m else .pure n)
    Eq
    (fun inc hr _ => by subst hr; cases inc <;> trivial)
    (fun inc hr _ => by subst hr; cases inc <;> exact ⟨rfl, rfl⟩)

/-- Represent a cell using the first storage component. -/
def cellModule : Module cell storage :=
  Module.ofFn
    (fun o => .liftBind (.inl o) fun n => .pure n)
    (fun s e => s = e.1)
    (fun _ _ _ => ⟨trivial, trivial⟩)
    (fun o hr _ => by
      cases o with
      | none => exact ⟨hr.symm, hr⟩
      | some n => exact ⟨rfl, rfl⟩)

theorem counter_bound : counterModule.ChargeBound cellCharge counterCharge :=
  Module.ChargeBound.ofFn fun o hr _ => by
    subst hr
    cases o <;> exact Nat.le_refl _

theorem cell_bound : cellModule.ChargeBound storageCharge cellCharge :=
  Module.ChargeBound.ofFn fun o _ _ => by
    cases o <;> exact Nat.le_refl _

/-- Read the counter and increment it only when its value is zero. -/
def ensurePositive : counter.Client Nat :=
  (.liftBind false (fun n => .pure n) : counter.Client Nat).bind fun n =>
    if n = 0 then .liftBind true (fun m => .pure m) else .pure n

theorem read_contract : counter.CostHoare counterCharge (fun _ => True)
    (.liftBind false fun n => .pure n) (fun n s => n = s) (fun s => counterCharge s false) := by
  stateful

theorem continue_contract (n : Nat) : counter.CostHoare counterCharge
    (fun s => n = s)
    (if n = 0 then .liftBind true (fun m => .pure m) else .pure n : counter.Client Nat)
    (fun m s => m = s ∧ 0 < m) (fun _ => 5) := by
  split
  · apply Spec.CostHoare.call_ofFn
    intro s _
    exact ⟨trivial, rfl, Nat.zero_lt_succ s⟩
  · have hp : counter.CostHoare counterCharge (fun s => n = s) (.pure n)
        (fun m s => m = s ∧ 0 < m) (fun _ => 0) := by
      apply Spec.CostHoare.pure
      intro s hs
      exact ⟨hs, by omega⟩
    exact hp.consequence (fun _ hs => hs) (fun _ _ hs => hs) (fun _ _ => by omega)

/-- The adaptive abstract client satisfies a uniform seven-unit operation budget. -/
theorem ensurePositive_contract : counter.CostHoare counterCharge (fun _ => True)
    ensurePositive (fun n s => n = s ∧ 0 < n) (fun _ => 7) := by
  exact Spec.CostHoare.bind read_contract continue_contract
    (fun _ _ _ _ _ => Nat.le_refl 7)

/-- Two successive interface implementations. -/
def implementation := counterModule.comp cellModule

/-- Both refinement layers preserve the same client contract and quantitative bound. -/
theorem ensurePositive_linked : storage.CostHoare storageCharge
    (fun e => ∃ s, True ∧ implementation.rep s e)
    (link implementation.methods ensurePositive)
    (fun n e => ∃ s, (n = s ∧ 0 < n) ∧ implementation.rep s e) (fun _ => 7) :=
  ensurePositive_contract.link (counter_bound.comp cell_bound) (fun _ => 7)
    (fun _ _ _ _ => Nat.le_refl _)

/-- Primitive evidence records the specified transition and its charged cost. -/
def exec : Execution storage (Nat × Nat) Nat :=
  fun s o a s' t => (s', a) = storage.stepFn s o ∧ t = storageCharge s o

/-- The deterministic primitive semantics realizes the storage interface. -/
def realization : Realization storage exec :=
  Realization.ofFn Eq
    (fun o hr _ => by subst hr; exact ⟨_, _, _, rfl, rfl⟩)
    (fun hr _ he => by
      subst hr
      exact ⟨congrArg Prod.snd he.1, (congrArg Prod.fst he.1).symm⟩)

theorem native_bound : Bound realization id storageCharge :=
  fun hr _ he => by
    subst hr
    exact he.2.le

/-- Every initial counter has a native execution within seven units, with a positive answer. -/
theorem ensurePositive_native (s spare : Nat) :
    ∃ a c' traces, Executes exec (link implementation.methods ensurePositive)
      (s, spare) a c' traces ∧
      (∃ s', realization.rep s' c' ∧
        ∃ n, (a = n ∧ 0 < a) ∧ implementation.rep n s') ∧ total id traces ≤ 7 := by
  exact Spec.CostHoare.exists_executes (s := (s, spare)) native_bound ensurePositive_linked
    ⟨s, trivial, s, rfl, rfl⟩ rfl

-- The zero branch performs a read, another read and a write; the nonzero branch only reads.
example : storage.runClient (0, 99) (link implementation.methods ensurePositive) =
    (1, (1, 99), [.inl none, .inl none, .inl (some 1)]) := rfl

example : storage.runClient (8, 99) (link implementation.methods ensurePositive) =
    (8, (8, 99), [.inl none]) := rfl

example : storage.totalCost storageCharge (0, 99)
    (storage.runClient (0, 99) (link implementation.methods ensurePositive)).2.2 = 7 := rfl

example : storage.totalCost storageCharge (8, 99)
    (storage.runClient (8, 99) (link implementation.methods ensurePositive)).2.2 = 2 := rfl

-- A cost certificate cannot silently drop one of the calls in the zero branch.
example : ¬ counter.CostHoare counterCharge (fun _ => True)
    ensurePositive (fun n s => n = s ∧ 0 < n) (fun _ => 6) := by
  intro h
  have hb := ((counter.costHoare_iff_ofFn ..).mp h).2 0 trivial
  change 7 ≤ 6 at hb
  omega

-- Named client contracts can be reused by proof search without expanding the implementation.
attribute [local aesop safe apply (rule_sets := [Stateful])] ensurePositive_contract

example : counter.CostHoare counterCharge (fun _ => True)
    ensurePositive (fun n s => n = s ∧ 0 < n) (fun _ => 7) := by
  stateful

-- State-dependent charges must use the changed state for the second call.
example (n : Nat) : counter.CostHoare (fun s _ => s + 1) (fun s => s = n)
    ((.liftBind true (fun a => .pure a) : counter.Client Nat).bind fun _ =>
      .liftBind false fun a => .pure a)
    (fun a s => a = s ∧ s = n + 1) (fun s => 2 * s + 3) := by
  apply Spec.CostHoare.bind (mid := fun a s => a = s ∧ s = n + 1)
    (first := fun s => s + 1) (next := fun _ s => s + 1)
  · apply Spec.CostHoare.call_ofFn
    intro s hs
    exact ⟨trivial, rfl, congrArg (· + 1) hs⟩
  · intro a
    apply Spec.CostHoare.call_ofFn
    intro s hs
    exact ⟨trivial, rfl, hs.2⟩
  · intro s hs a s' ha
    rw [hs, ha.2]
    omega

/-- info: 'Cslib.Stateful.Spec.CostHoare.link' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spec.CostHoare.link

/-- info: 'Cslib.Stateful.Module.ChargeBound.comp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Module.ChargeBound.comp

/-- info: 'Cslib.Stateful.Tests.ensurePositive_native' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ensurePositive_native

/-! ## Nondeterministic relational specification (two-slot allocator) -/

/-- Operations of a two-slot index allocator: `alloc` nondeterministically returns any free
slot in `Fin 2`; `free i` releases slot `i`. -/
inductive TwoSlotOp : Type
  | alloc : TwoSlotOp
  | free : Fin 2 → TwoSlotOp
  deriving DecidableEq

/-- Relational specification of a two-slot allocator whose state `(b₀, b₁) : Bool × Bool`
records whether slots `0` and `1` are currently occupied. When both slots are free, `alloc`
nondeterministically returns either `0` or `1`. -/
abbrev TwoSlotAlloc : Spec where
  State := Bool × Bool
  Op := TwoSlotOp
  Result
    | .alloc => Fin 2
    | .free _ => Unit
  valid s
    | .alloc => s.1 = false ∨ s.2 = false
    | .free _ => True
  step s o s' a :=
    match o, a with
    | .alloc, i =>
      (i = 0 ∧ s.1 = false ∧ s' = (true, s.2)) ∨
      (i = 1 ∧ s.2 = false ∧ s' = (s.1, true))
    | .free i, () =>
      s' = if i = 0 then (false, s.2) else (s.1, false)

instance : TwoSlotAlloc.Total where
  step_total s o hv := by
    cases o with
    | alloc =>
      rcases hv with h0 | h1
      · exact ⟨(true, s.2), 0, Or.inl ⟨rfl, h0, rfl⟩⟩
      · exact ⟨(s.1, true), 1, Or.inr ⟨rfl, h1, rfl⟩⟩
    | free i =>
      exact ⟨if i = 0 then (false, s.2) else (s.1, false), (), rfl⟩

/-- Both slot `0` and slot `1` are valid outcomes of `alloc` from `(false, false)`. -/
theorem twoSlotAlloc_nondeterministic :
    ((true, false), (0 : Fin 2)) ∈ TwoSlotAlloc.outcomes (false, false) .alloc ∧
    ((false, true), (1 : Fin 2)) ∈ TwoSlotAlloc.outcomes (false, false) .alloc :=
  ⟨Or.inl ⟨rfl, rfl, rfl⟩, Or.inr ⟨rfl, rfl, rfl⟩⟩

/-- Sample LTS transition via `Spec.toLTS`. -/
theorem twoSlotAlloc_toLTS_tr :
    TwoSlotAlloc.toLTS.Tr (false, false) ⟨.alloc, (1 : Fin 2)⟩ (false, true) :=
  Or.inr ⟨rfl, rfl, rfl⟩

/-- Adaptive client that allocates two slots sequentially, frees the first slot returned, and
returns the pair `(i, j)` of allocated slots. -/
abbrev allocTwoAndFreeFirst : TwoSlotAlloc.Client (Fin 2 × Fin 2) :=
  .liftBind TwoSlotOp.alloc fun i =>
    .liftBind TwoSlotOp.alloc fun j =>
      .liftBind (TwoSlotOp.free i) fun _ =>
        .pure (i, j)

/-- From `(false, false)`, `allocTwoAndFreeFirst` is demonically admissible across all
nondeterministic choices of the first and second allocations. -/
theorem allocTwoAndFreeFirst_demonicValid :
    TwoSlotAlloc.DemonicValid (false, false) allocTwoAndFreeFirst := by
  refine Spec.DemonicValid.liftBind (D := TwoSlotAlloc) TwoSlotOp.alloc _ (Or.inl rfl)
    fun s₁ i h₁ => ?_
  have hv₂ : TwoSlotAlloc.valid s₁ TwoSlotOp.alloc := by
    rcases h₁ with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  refine Spec.DemonicValid.liftBind (D := TwoSlotAlloc) TwoSlotOp.alloc _ hv₂
    fun s₂ j _ => ?_
  refine Spec.DemonicValid.liftBind (D := TwoSlotAlloc) (TwoSlotOp.free i) _ trivial
    fun s₃ _ _ => .pure s₃ (i, j)

/-- Demonic `CostHoare` specification: under unit per-operation charge, every relational execution
of `allocTwoAndFreeFirst` from `(false, false)` returns distinct slots `i ≠ j`, leaves `i` free
and `j` occupied, and incurs abstract cost `3`. -/
theorem allocTwoAndFreeFirst_costHoare :
    TwoSlotAlloc.CostHoare (fun _ _ => 1)
      (fun s => s = (false, false))
      allocTwoAndFreeFirst
      (fun p s' => p.1 ≠ p.2 ∧ (if p.1 = 0 then s'.1 = false else s'.2 = false))
      (fun _ => 3) := by
  refine ⟨fun s hs => ?_, fun s hs v s' tr hrun => ?_⟩
  · subst hs
    refine ⟨allocTwoAndFreeFirst_demonicValid, fun v s' tr hrun => ?_⟩
    obtain ⟨_, i, s₁, tr₁, h₁, hrun₁, _⟩ := (Spec.clientRun_liftBind_iff ..).mp hrun
    obtain ⟨_, j, s₂, tr₂, h₂, hrun₂, _⟩ := (Spec.clientRun_liftBind_iff ..).mp hrun₁
    obtain ⟨_, _, s₃, tr₃, h₃, hrun₃, _⟩ := (Spec.clientRun_liftBind_iff ..).mp hrun₂
    obtain ⟨rfl, rfl, rfl⟩ := (Spec.clientRun_pure_iff ..).mp hrun₃
    rcases h₁ with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩
    · rcases h₂ with ⟨_, hfalse, _⟩ | ⟨rfl, _, rfl⟩
      · cases hfalse
      · subst h₃
        exact ⟨by decide, by decide⟩
    · rcases h₂ with ⟨rfl, _, rfl⟩ | ⟨_, hfalse, _⟩
      · subst h₃
        exact ⟨by decide, by decide⟩
      · cases hfalse
  · subst hs
    obtain ⟨_, i, s₁, tr₁, _, hrun₁, rfl⟩ := (Spec.clientRun_liftBind_iff ..).mp hrun
    obtain ⟨_, j, s₂, tr₂, _, hrun₂, rfl⟩ := (Spec.clientRun_liftBind_iff ..).mp hrun₁
    obtain ⟨_, _, s₃, tr₃, _, hrun₃, rfl⟩ := (Spec.clientRun_liftBind_iff ..).mp hrun₂
    obtain ⟨rfl, rfl, rfl⟩ := (Spec.clientRun_pure_iff ..).mp hrun₃
    simp

/-- Consequence to plain demonic `Hoare`. -/
theorem allocTwoAndFreeFirst_hoare :
    TwoSlotAlloc.Hoare
      (fun s => s = (false, false))
      allocTwoAndFreeFirst
      (fun p s' => p.1 ≠ p.2 ∧ (if p.1 = 0 then s'.1 = false else s'.2 = false)) :=
  allocTwoAndFreeFirst_costHoare.hoare

/-- Concrete first-fit implementation of `TwoSlotAlloc`: `alloc` chooses slot `0` when free and
slot `1` otherwise, recording `1` unit of execution trace cost per operation. -/
def firstFitExec : Execution TwoSlotAlloc (Bool × Bool) ℕ
  | c, .alloc, i, c', n =>
    n = 1 ∧
    if c.1 = false then i = 0 ∧ c' = (true, c.2)
    else i = 1 ∧ c' = (c.1, true)
  | c, .free i, (), c', n =>
    n = 1 ∧ c' = (if i = 0 then (false, c.2) else (c.1, false))

/-- Angelic realization of `TwoSlotAlloc` by `firstFitExec`. -/
def firstFitRealization : Realization TwoSlotAlloc firstFitExec where
  rep s c := s = c
  total {s c} o hr _ := by
    subst hr
    cases o with
    | alloc =>
      rcases Bool.dichotomy s.1 with h0 | h0
      · exact ⟨0, (true, s.2), 1, rfl, by simp [h0]⟩
      · exact ⟨1, (s.1, true), 1, rfl, by simp [h0]⟩
    | free i =>
      exact ⟨(), if i = 0 then (false, s.2) else (s.1, false), 1, rfl, rfl⟩
  correct {s c o a c' n} hr hv he := by
    subst hr
    cases o with
    | alloc =>
      obtain ⟨_, hbranch⟩ := he
      rcases Bool.dichotomy s.1 with h0 | h0
      · simp only [h0, ↓reduceIte] at hbranch
        obtain ⟨rfl, rfl⟩ := hbranch
        exact ⟨(true, s.2), Or.inl ⟨rfl, h0, rfl⟩, rfl⟩
      · simp only [h0, Bool.true_eq_false, ↓reduceIte] at hbranch
        obtain ⟨rfl, rfl⟩ := hbranch
        have h1 : s.2 = false := hv.resolve_left (by simp [h0])
        exact ⟨(s.1, true), Or.inr ⟨rfl, h1, rfl⟩, by simp [h0]⟩
    | free i =>
      obtain ⟨_, rfl⟩ := he
      cases a
      exact ⟨if i = 0 then (false, s.2) else (s.1, false), rfl, rfl⟩

/-- Per-operation worst-case bound for `firstFitRealization`. -/
theorem firstFitBound :
    Bound firstFitRealization id (fun _ _ => 1) := by
  intro s c o a c' n _ _ he
  cases o with
  | alloc => exact Nat.le_of_eq he.1
  | free _ => exact Nat.le_of_eq he.1

/-- Amortized certificate for `firstFitRealization` with zero potential. -/
theorem firstFitAmortized :
    Amortized firstFitRealization id (fun _ _ => 0) (fun _ _ => 1) :=
  Amortized.of_worstCase firstFitBound

/-- End-to-end execution of `allocTwoAndFreeFirst` on `firstFitRealization` via
`Amortized.exists_demonic` and `Spec.CostHoare.realize_amortized`. -/
theorem firstFit_allocTwoAndFreeFirst_executes :
    ∃ v c' traces s' tr,
      Executes firstFitExec allocTwoAndFreeFirst (false, false) v c' traces ∧
      TwoSlotAlloc.ClientRun (false, false) allocTwoAndFreeFirst v s' tr ∧
      firstFitRealization.rep s' c' ∧
      (v.1 ≠ v.2 ∧ (if v.1 = 0 then s'.1 = false else s'.2 = false)) ∧
      total id traces ≤ 3 := by
  obtain ⟨v, c', traces, _, _, he, _, _, _, _⟩ :=
    firstFitAmortized.exists_demonic allocTwoAndFreeFirst
      (s := (false, false)) (c := (false, false)) rfl allocTwoAndFreeFirst_demonicValid
  obtain ⟨s', tr, hrun, hr, hpost, hcost⟩ :=
    allocTwoAndFreeFirst_costHoare.realize_amortized firstFitAmortized rfl rfl he
  exact ⟨v, c', traces, s', tr, he, hrun, hr, hpost, by omega⟩

end Cslib.Stateful.Tests
