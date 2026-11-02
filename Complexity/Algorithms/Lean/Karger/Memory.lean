/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Karger.Memory.Contract
public import Complexity.DataStructure.Memory.Frame

/-!
# The contraction structure over memory

The contraction structure `Karger.spec` is implemented over the memory oracle `Memory.spec w` by
the programs of `Karger.Memory.Layout` (`size`, `total`, `pairAt`) and `Karger.Memory.Contract`
(`contract`), on the layout of a `Layout`. This file assembles them into a refinement.

* `refinement`: a `Refinement Karger.spec (Memory.spec w)` with invariant `Inv` and abstraction
  `abs`.
* `amortized`: each operation on a graph of `k` supervertices costs at most `opCharge`, which is
  one memory unit for `size` and `total`, `2 k + 1` for `pairAt` and `7 k + 7` for `contract`.
  So `amortized_capacity` bounds every operation by `7 C + 7` at capacity `C`.
* `framed`: the same refinement as a `Memory.Framed`, whose footprint is the layout's region, so
  it joins products with other structures in one memory.

Each obligation comes from one weakest-precondition lemma per operation (`wp_methods`), through
`StateTransitionSpec.wp_iff`. Nothing here mentions a register or an instruction.

## Main definitions

* `methods`, `opCharge`: the operations as memory programs, and their charges.
* `refinement`, `framed`: the implementation as a refinement, and as a framed one.

## Main results

* `wp_methods`: each operation realizes the specified step, preserves the invariant, costs at
  most `opCharge`, and changes no cell outside the layout.
* `amortized`, `amortized_capacity`: the cost certificates.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Karger.Memory

open Cslib.WordRAM Cslib.WeightedCut Cslib.DataStructure Cslib.DataStructure.Memory
  Cslib.DataStructure.StateTransitionSpec

variable (L : Layout) (w : ℕ)

/-- The operations of the contraction structure as memory programs. -/
def methods : Methods spec (Memory.spec w)
  | .size => size L
  | .total => total L
  | .pairAt r => pairAt L r
  | .contract u v => contract L u v

/-- The memory charge of each operation on a graph of `k` supervertices: one unit for the size
and the total, `2 k + 1` for the sampling query, and `7 k + 7` for a contraction. -/
def opCharge (G : Graph) : Op → ℕ
  | .size => 1
  | .total => 1
  | .pairAt _ => 2 * G.size + 1
  | .contract _ _ => 7 * G.size + 7

variable {L w}

/-- **Every operation over memory.** From a state satisfying the invariant, each admissible
operation answers and steps as the specification, preserves the invariant, costs at most
`opCharge`, keeps the frontier and changes no cell outside the layout. -/
theorem wp_methods {s : Memory.State} (hs : Inv L w s) (o : Op) (hv : spec.valid (abs L s) o) :
    (Memory.spec w).wp charge (methods L w o)
      (fun a s' t => spec.stepFn (abs L s) o = (abs L s', a) ∧ Inv L w s' ∧
        t ≤ opCharge (abs L s) o ∧ s'.frontier = s.frontier ∧
        ∀ b ∉ L.footprint, s'.mem b = s.mem b) s := by
  have hlim := hs.allocated
  cases o with
  | size =>
    exact (wp_lift _ _ _).mpr
      ⟨hs.lt_frontier L.size_mem_footprint, rfl, hs, le_rfl, rfl, fun _ _ => rfl⟩
  | total =>
    refine (wp_lift _ _ _).mpr
      ⟨hs.lt_frontier L.total_mem_footprint, ?_, hs, le_rfl, rfl, fun _ _ => rfl⟩
    change (abs L s, totalDoubledWeight (abs L s).weight) = (abs L s, s.mem L.total.base)
    rw [hs.total_eq]
  | pairAt r =>
    refine wp_mono ?_ (wp_pairAt hs hv)
    rintro a s' t ⟨rfl, rfl, ht⟩
    exact ⟨rfl, hs, ht, rfl, fun _ _ => rfl⟩
  | contract u v =>
    refine wp_mono ?_ (wp_contract hs hv)
    rintro a s' t ⟨hf, hfr, habs, hs', ht⟩
    exact ⟨by rw [habs]; rfl, hs', ht, hf, hfr⟩

variable (L w)

/-- **The contraction structure over memory.** -/
noncomputable def refinement : Refinement spec (Memory.spec w) :=
  Refinement.ofFn (methods L w) (Inv L w) (abs L)
    (fun o hs hv => ((wp_iff _ _ _).mp (wp_methods hs o hv)).1)
    (fun o hs hv => by
      obtain ⟨-, hstep, hs', -⟩ := (wp_iff _ _ _).mp (wp_methods hs o hv)
      exact ⟨hstep, hs'⟩)

@[simp] theorem refinement_methods : (refinement L w).methods = methods L w := rfl

@[simp] theorem refinement_inv : (refinement L w).inv = Inv L w := rfl

@[simp] theorem refinement_abs : (refinement L w).abs = abs L := rfl

/-- **Cost.** Each operation costs at most `opCharge` memory units, with no potential. -/
theorem amortized : (refinement L w).Amortized charge opCharge fun _ => 0 :=
  Refinement.Amortized.ofFn fun o hs hv => by
    obtain ⟨-, -, -, ht, -⟩ := (wp_iff _ _ _).mp (wp_methods hs o hv)
    simpa using ht

/-- At most `capacity` supervertices, every operation costs at most `7 capacity + 7` memory
units. -/
theorem amortized_capacity :
    (refinement L w).Amortized charge (fun _ _ => 7 * L.capacity + 7) fun _ => 0 := by
  refine ⟨fun {e} o {a e' tr} hs hv hrun => ((amortized L w).step o hs hv hrun).trans ?_⟩
  have hk : ((refinement L w).abs e).size ≤ L.capacity := hs.size_le
  cases o <;> simp only [opCharge] <;> omega

/-- **The framed implementation.** The refinement, with the layout's region as its footprint. -/
noncomputable def framed : Memory.Framed spec w :=
  .ofStatic (refinement L w) L.footprint (fun hs ha => Inv.lt_frontier hs ha)
    (fun hs h hf => ⟨hs.congr h hf, abs_congr hs h⟩)
    (fun o hs hv b _ hb => by
      obtain ⟨-, -, -, -, -, hfr⟩ := (wp_iff _ _ _).mp (wp_methods hs o hv)
      exact hfr b hb)

@[simp] theorem framed_toRefinement : (framed L w).toRefinement = refinement L w := rfl

/-- The framed implementation has the same costs. -/
theorem framed_amortized : (framed L w).Amortized charge opCharge fun _ => 0 :=
  amortized L w

end Cslib.Algorithms.Lean.Karger.Memory
