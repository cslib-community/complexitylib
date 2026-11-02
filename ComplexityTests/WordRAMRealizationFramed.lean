/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: candidate

import Complexity.Computability.WordRAM.Realization.BackendFrame
import Complexity.Tactic.Realize
import ComplexityTests.WordRAMRealizationBackend

/-! The array stack's backend from `WordRAMRealizationBackend`, framed. Its operations write only
their layout's cells (`modifies`, `frame`), as the hand-stepped `Stack.WordRAM.modifies` and
`frame` did. An allocation tag, added by `Backend.extend`, sets up an empty stack from arbitrary
bounded data in constant time, clearing only the count cell (`allocate`), and a client then runs
on it (`run_allocated`). Two stacks share one memory with two frames (`modifies_left`,
`instruction_bound_pair`). -/

open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
  Cslib.WordRAM.Realization.MemoryStack Cslib.DataStructure.Queue

namespace ComplexityTests.WordRAMRealizationFramed

open ComplexityTests.WordRAMRealizationBackend (Tag certificates backend implements)

/-- The stack's operations implement the framed stack. -/
theorem implements_framed {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C) :
    (backend w C L).Implements (Stack.Memory.framed hL).toRefinement :=
  implements hL

/-! ## The frame of the stack -/

/-- **Modifies.** A native stack operation writes only its layout's cells. -/
theorem modifies {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C) {vs : List ℕ}
    {x y : Data (Backend.registers certificates)} {o : StackOp ℕ}
    {a : (Stack.WordRAM.spec w C).Result o} {n : ℕ}
    (hr : (Backend.implementation (implements_framed hL)).rep vs x)
    (hv : (Stack.WordRAM.spec w C).valid vs o) (he : (backend w C L).exec w x o a y n) :
    Modifies L.footprint x.mem y.mem := by
  have h := Backend.modifies (implements_framed hL) hr hv he
  rwa [Memory.Framed.region_eq_footprint _ rfl, Stack.Memory.framed_footprint] at h

/-- **Frame.** A native stack operation keeps every assertion on cells outside its layout. -/
theorem frame {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C) {vs : List ℕ}
    {x y : Data (Backend.registers certificates)} {o : StackOp ℕ}
    {a : (Stack.WordRAM.spec w C).Result o} {n : ℕ}
    (hr : (Backend.implementation (implements_framed hL)).rep vs x)
    (hv : (Stack.WordRAM.spec w C).valid vs o) (he : (backend w C L).exec w x o a y n)
    {Q : HeapAssertion} (hQ : Q.holds x.mem) (hd : Disjoint Q.footprint L.footprint) :
    Q.holds y.mem :=
  HeapAssertion.frame hQ hd (modifies hL hr hv he)

/-! ## Allocation from dirty memory -/

/-- Allocating a stack of capacity `C` zeroes one count cell and leaves the item array as it
was. -/
theorem realizes_allocLayout : Realizes .exact Stack.Memory.allocLayout
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding layoutWords
    (fun w C s => Fits w (s.frontier + 1 + C)) (fun _ _ => 0) := by
  realize
  all_goals exact h.of_le (by omega)

/-- The allocation's body. -/
noncomputable def allocCertificate : Unit → Certificate .exact := fun _ => ⟨realizes_allocLayout⟩

/-- The stack's bodies and the allocation's. -/
noncomputable abbrev withAlloc : Tag ⊕ Unit → Certificate .exact :=
  Sum.elim certificates allocCertificate

/-- The stack on layout `L`, with the allocation tag. -/
noncomputable def allocated (w C : ℕ) (L : Stack.Memory.Layout) :
    Backend (Stack.WordRAM.spec w C) withAlloc :=
  (backend w C L).extend allocCertificate

/-- The allocation tag allocates a stack of capacity `C` and returns its layout. -/
noncomputable def allocation (w C : ℕ) :
    Backend.Allocation (Stack.Memory.allocator w C) withAlloc where
  tag := .inr ()
  arg := C
  handle := id
  run _ := rfl
  entry _ _ hroom := by
    change Fits w (_ + (C + 1)) at hroom
    exact ⟨fun _ => (hroom.of_le (by omega) : Fits w C), hroom.of_le (by omega)⟩

/-- The layout that allocation returns at frontier `f`. -/
def layoutAt (f C : ℕ) : Stack.Memory.Layout := ⟨⟨f, 1⟩, ⟨f + 1, C⟩⟩

/-- **Allocation in constant time.** One constant `K`, chosen before every width, capacity and
memory, bounds the allocation of an empty stack from any bounded data whose frontier leaves room
for it. It writes only the `C + 1` cells above the frontier, returns the layout, and leaves data
that represents the empty stack on it. -/
theorem allocate : ∃ K, ∀ {w C : ℕ} {x : Data (Backend.registers withAlloc)}, x.Bounded w →
    ∀ (hroom : Fits w (x.regs (Backend.frontier withAlloc) + 1 + C)),
    ∃ y n, Exec w (Backend.code withAlloc (.inr ())) (Backend.install withAlloc (.inr ()) C x)
        y n ∧ n ≤ K ∧
      (∀ j, y.regs (Backend.tmp withAlloc (.inr ())
        (Fin.castAdd ((withAlloc (.inr ())).realizes.scratchSize + 1) j)) =
          (withAlloc (.inr ())).output (layoutAt (x.regs (Backend.frontier withAlloc)) C) j) ∧
      Modifies (Finset.Ico (x.regs (Backend.frontier withAlloc))
        (x.regs (Backend.frontier withAlloc) + (C + 1))) x.mem y.mem ∧
      (Backend.implementation
        ((implements_framed (Stack.Memory.valid_allocLayout hroom)).extend allocCertificate)).rep
          [] y := by
  refine ⟨Backend.factor withAlloc * 4, fun {w C x} hx hroom => ?_⟩
  obtain ⟨y, n, b, he, hn, hout, hb, hmod, hrep⟩ := (allocation w C).exec (F := allocated w C)
    (fun s _ hr => (implements_framed (Stack.Memory.valid_allocLayout
      ((show Fits w (s.frontier + (C + 1)) from hr).of_le (by omega)))).extend allocCertificate)
    hx trivial (show Fits w (x.regs (Backend.frontier withAlloc) + (C + 1)) from
      hroom.of_le (by omega))
  cases hb
  exact ⟨y, n, he, hn, hout, hmod, hrep⟩

/-- Every operation of the stack with the allocation tag has one constant bound. -/
theorem instruction_bound : ∃ K, ∀ {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C),
    Bound (Backend.implementation ((implements_framed hL).extend allocCertificate)) id
      fun _ _ => K :=
  ⟨Backend.factor withAlloc * 23, fun hL =>
    Backend.bound ((implements_framed hL).extend allocCertificate) (Stack.Memory.amortized hL) 19
      fun o _ _ => by
      cases o <;> exact Nat.le_of_ble_eq_true rfl⟩

/-- **Allocate, then run any admissible client**, as the hand-stepped `run_initialized`: from
arbitrary bounded data with room, the allocation and `m` operations take at most `K₀ + m * K`
instructions. -/
theorem run_allocated : ∃ K₀ K, ∀ {w C : ℕ} {x : Data (Backend.registers withAlloc)},
    x.Bounded w → Fits w (x.regs (Backend.frontier withAlloc) + 1 + C) → ∀ {α : Type}
    (p : (Stack.WordRAM.spec w C).Client α),
    (Stack.WordRAM.spec w C).ValidHistory [] ((Stack.WordRAM.spec w C).clientHistory [] p) →
    ∃ ready y n traces,
      Exec w (Backend.code withAlloc (.inr ())) (Backend.install withAlloc (.inr ()) C x) ready n ∧
      Executes ((allocated w C (layoutAt (x.regs (Backend.frontier withAlloc)) C)).exec w) p ready
        ((Stack.WordRAM.spec w C).clientResult [] p) y traces ∧
      n + total id traces ≤ K₀ + ((Stack.WordRAM.spec w C).clientHistory [] p).length * K := by
  obtain ⟨K₀, h₀⟩ := allocate
  obtain ⟨K, hK⟩ := instruction_bound
  refine ⟨K₀, K, fun {w C x} hx hroom {α} p hv => ?_⟩
  obtain ⟨ready, n, he, hn, -, -, hrep⟩ := h₀ hx hroom
  obtain ⟨y, traces, hex, -, htot⟩ := Bound.exists_executes_const (hK _) p hrep hv
  exact ⟨ready, y, n, traces, he, hex, by omega⟩

/-! ## Two stacks in one memory -/

/-- Two stacks run as the product of two stacks over one memory, each operation selecting a body
of its own side. -/
theorem implements_pair {w C : ℕ} {L₁ L₂ : Stack.Memory.Layout} (h₁ : L₁.Valid w C)
    (h₂ : L₂.Valid w C) :
    ((backend w C L₁).sum (backend w C L₂)).Implements
      ((Stack.Memory.framed h₁).prod (Stack.Memory.framed h₂)).toRefinement :=
  (implements_framed h₁).prod_framed (implements_framed h₂)

/-- **Two frames.** An operation of the left stack writes only the left layout's cells. -/
theorem modifies_left {w C : ℕ} {L₁ L₂ : Stack.Memory.Layout} (h₁ : L₁.Valid w C)
    (h₂ : L₂.Valid w C) {vs₁ vs₂ : List ℕ}
    {x y : Data (Backend.registers (Sum.elim certificates certificates))} {o : StackOp ℕ}
    {a : (Stack.WordRAM.spec w C).Result o} {n : ℕ}
    (hr : (Backend.implementation (implements_pair h₁ h₂)).rep (vs₁, vs₂) x)
    (hv : (Stack.WordRAM.spec w C).valid vs₁ o)
    (he : ((backend w C L₁).sum (backend w C L₂)).exec w x (.inl o) a y n) :
    Modifies L₁.footprint x.mem y.mem := by
  have h := Backend.modifies_inl (implements_framed h₁) (implements_framed h₂) hr hv he
  rwa [Memory.Framed.region_eq_footprint _ rfl, Stack.Memory.framed_footprint] at h

/-- The whole pair writes only the two layouts' cells. -/
theorem modifies_pair {w C : ℕ} {L₁ L₂ : Stack.Memory.Layout} (h₁ : L₁.Valid w C)
    (h₂ : L₂.Valid w C) {vs : List ℕ × List ℕ}
    {x y : Data (Backend.registers (Sum.elim certificates certificates))}
    {o : (product (Stack.WordRAM.spec w C) (Stack.WordRAM.spec w C)).Op}
    {a : (product (Stack.WordRAM.spec w C) (Stack.WordRAM.spec w C)).Result o} {n : ℕ}
    (hr : (Backend.implementation (implements_pair h₁ h₂)).rep vs x)
    (hv : (product (Stack.WordRAM.spec w C) (Stack.WordRAM.spec w C)).valid vs o)
    (he : ((backend w C L₁).sum (backend w C L₂)).exec w x o a y n) :
    Modifies (L₁.footprint ∪ L₂.footprint) x.mem y.mem := by
  have h := Backend.modifies (implements_pair h₁ h₂) hr hv he
  rwa [Memory.Framed.region_eq_footprint _ rfl] at h

/-- One constant bounds every operation of the pair, before every width, capacity and pair of
layouts. The stacks' charges add across the product (`Memory.Framed.amortized_prod`). -/
theorem instruction_bound_pair : ∃ K, ∀ {w C : ℕ} {L₁ L₂ : Stack.Memory.Layout}
    (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C),
    Bound (Backend.implementation (implements_pair h₁ h₂)) id fun _ _ => K := by
  refine ⟨Backend.factor (Sum.elim certificates certificates) * (3 + 19 + 1),
    fun {w C L₁ L₂} h₁ h₂ => ?_⟩
  have A : ((Stack.Memory.framed h₁).prod (Stack.Memory.framed h₂)).Amortized Memory.charge
      (fun _ _ => 3) fun _ => 0 := by
    have A := Memory.Framed.amortized_prod (Stack.Memory.amortized h₁)
      (Stack.Memory.amortized h₂) (Memory.Framed.Local.const _ 0) (Memory.Framed.Local.const _ 0)
    rwa [productCharge_const] at A
  have hwork : ∀ {e} o, ((Stack.Memory.framed h₁).prod (Stack.Memory.framed h₂)).inv e →
      (product (Stack.WordRAM.spec _ _) (Stack.WordRAM.spec _ _)).valid
        (((Stack.Memory.framed h₁).prod (Stack.Memory.framed h₂)).abs e) o →
      (Sum.elim certificates certificates (((backend _ _ L₁).sum (backend _ _ L₂)).tag o)).work
        (((backend _ _ L₁).sum (backend _ _ L₂)).arg o) e ≤ 19 := by
    intro e o _ _
    rcases o with o | o <;> cases o <;> exact Nat.le_of_ble_eq_true rfl
  intro s x o a y n hr hv he
  exact Backend.bound (implements_pair h₁ h₂) A 19 hwork hr hv he

end ComplexityTests.WordRAMRealizationFramed
