/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (test driver)

public import Complexity.Init
public import Complexity.Foundations.Semantics.Stateful.Relational

/-!
# Tests for Relational Stateful Specifications

Concrete non-vacuous tests for `Cslib.Stateful.RelSpec`, its totality class `RelSpec.Total`,
projection `RelSpec.toLTS`, zero-cost deterministic embedding `Spec.toRelSpec`, demonic adaptive
client semantics (`ClientRun`, `DemonicValid`, `RelSpec.Hoare`, `RelSpec.CostHoare`), and angelic
backend realization and amortized analysis (`RelRealization`, `RelBound`, `RelAmortized`).
-/

@[expose] public section

namespace ComplexityTests.StatefulRelational

open Cslib.Stateful

/-! ## 1. A genuinely nondeterministic relational specification (two-slot allocator) -/

/-- Operations of a two-slot index allocator: `alloc` nondeterministically returns any free
slot in `Fin 2`; `free i` releases slot `i`. -/
inductive TwoSlotOp : Type
  | alloc : TwoSlotOp
  | free : Fin 2 → TwoSlotOp
  deriving DecidableEq

/-- Relational specification of a two-slot allocator whose state `(b₀, b₁) : Bool × Bool`
records whether slots `0` and `1` are currently occupied. When both slots are free, `alloc`
nondeterministically returns either `0` or `1`. -/
abbrev TwoSlotAlloc : RelSpec where
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

/-- Sample LTS transition via `RelSpec.toLTS`. -/
theorem twoSlotAlloc_toLTS_tr :
    TwoSlotAlloc.toLTS.Tr (false, false) ⟨.alloc, (1 : Fin 2)⟩ (false, true) :=
  Or.inr ⟨rfl, rfl, rfl⟩

/-! ## 2. Adaptive client, demonic admissibility, and Hoare / CostHoare verification -/

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
  refine RelSpec.DemonicValid.liftBind (D := TwoSlotAlloc) TwoSlotOp.alloc _ (Or.inl rfl)
    fun s₁ i h₁ => ?_
  have hv₂ : TwoSlotAlloc.valid s₁ TwoSlotOp.alloc := by
    rcases h₁ with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  refine RelSpec.DemonicValid.liftBind (D := TwoSlotAlloc) TwoSlotOp.alloc _ hv₂
    fun s₂ j _ => ?_
  refine RelSpec.DemonicValid.liftBind (D := TwoSlotAlloc) (TwoSlotOp.free i) _ trivial
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
    obtain ⟨_, i, s₁, tr₁, h₁, hrun₁, _⟩ := (RelSpec.clientRun_liftBind_iff ..).mp hrun
    obtain ⟨_, j, s₂, tr₂, h₂, hrun₂, _⟩ := (RelSpec.clientRun_liftBind_iff ..).mp hrun₁
    obtain ⟨_, _, s₃, tr₃, h₃, hrun₃, _⟩ := (RelSpec.clientRun_liftBind_iff ..).mp hrun₂
    obtain ⟨rfl, rfl, rfl⟩ := (RelSpec.clientRun_pure_iff ..).mp hrun₃
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
    obtain ⟨_, i, s₁, tr₁, _, hrun₁, rfl⟩ := (RelSpec.clientRun_liftBind_iff ..).mp hrun
    obtain ⟨_, j, s₂, tr₂, _, hrun₂, rfl⟩ := (RelSpec.clientRun_liftBind_iff ..).mp hrun₁
    obtain ⟨_, _, s₃, tr₃, _, hrun₃, rfl⟩ := (RelSpec.clientRun_liftBind_iff ..).mp hrun₂
    obtain ⟨rfl, rfl, rfl⟩ := (RelSpec.clientRun_pure_iff ..).mp hrun₃
    simp

/-- Consequence to plain demonic `Hoare`. -/
theorem allocTwoAndFreeFirst_hoare :
    TwoSlotAlloc.Hoare
      (fun s => s = (false, false))
      allocTwoAndFreeFirst
      (fun p s' => p.1 ≠ p.2 ∧ (if p.1 = 0 then s'.1 = false else s'.2 = false)) :=
  allocTwoAndFreeFirst_costHoare.hoare

/-! ## 3. Concrete first-fit backend realization and amortized certificate -/

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
def firstFitRealization : RelRealization TwoSlotAlloc firstFitExec where
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
    RelBound firstFitRealization id (fun _ _ => 1) := by
  intro s c o a c' n _ _ he
  cases o with
  | alloc => exact Nat.le_of_eq he.1
  | free _ => exact Nat.le_of_eq he.1

/-- Amortized certificate for `firstFitRealization` with zero potential. -/
theorem firstFitAmortized :
    RelAmortized firstFitRealization id (fun _ _ => 0) (fun _ _ => 1) :=
  RelAmortized.of_relBound firstFitBound

/-- End-to-end execution of `allocTwoAndFreeFirst` on `firstFitRealization` via
`RelAmortized.run_client_amortized` and `RelSpec.CostHoare.realize_amortized`. -/
theorem firstFit_allocTwoAndFreeFirst_executes :
    ∃ v c' traces s' tr,
      Executes firstFitExec allocTwoAndFreeFirst (false, false) v c' traces ∧
      TwoSlotAlloc.ClientRun (false, false) allocTwoAndFreeFirst v s' tr ∧
      firstFitRealization.rep s' c' ∧
      (v.1 ≠ v.2 ∧ (if v.1 = 0 then s'.1 = false else s'.2 = false)) ∧
      total id traces ≤ 3 := by
  obtain ⟨v, c', traces, _, _, he, _, _, _, _⟩ :=
    firstFitAmortized.run_client_amortized allocTwoAndFreeFirst
      (s := (false, false)) (c := (false, false)) rfl allocTwoAndFreeFirst_demonicValid
  obtain ⟨s', tr, hrun, hr, hpost, hcost⟩ :=
    allocTwoAndFreeFirst_costHoare.realize_amortized firstFitAmortized rfl rfl he
  exact ⟨v, c', traces, s', tr, he, hrun, hr, hpost, by omega⟩

/-! ## 4. Layer 1 (`Spec.toRelSpec`) embedding and collapse equivalences -/

/-- Simple deterministic counter specification to exercise `Spec.toRelSpec`. -/
abbrev CounterSpec : Spec where
  State := ℕ
  Op := Unit
  Result _ := ℕ
  step n _ := (n + 1, n)

/-- Adaptive client on `CounterSpec` that increments twice and returns the sum of results. -/
def counterTwice : CounterSpec.Client ℕ :=
  .liftBind () fun a => .liftBind () fun b => .pure (a + b)

/-- `DemonicValid` on `CounterSpec.toRelSpec` collapses to `ValidHistory` on `CounterSpec`. -/
theorem counterTwice_demonicValid (n : ℕ) :
    CounterSpec.toRelSpec.DemonicValid n counterTwice := by
  rw [CounterSpec.toRelSpec_demonicValid_iff]
  exact ⟨trivial, trivial, trivial⟩

/-- `RelSpec.Hoare` on `CounterSpec.toRelSpec` is equivalent to `Spec.Hoare`. -/
theorem counterTwice_relHoare :
    CounterSpec.toRelSpec.Hoare (fun n => n = 5) counterTwice (fun v s' => v = 11 ∧ s' = 7) := by
  rw [CounterSpec.toRelSpec_hoare_iff]
  intro s hs
  subst hs
  exact ⟨⟨trivial, trivial, trivial⟩, rfl, rfl⟩

end ComplexityTests.StatefulRelational
