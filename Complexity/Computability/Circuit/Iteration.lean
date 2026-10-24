/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Simulation
public import Complexity.Computability.Circuit.Synthesis
public import Cslib.Computability.Circuit.Composition
public import Cslib.Computability.Circuit.Synthesis
public import Mathlib.Logic.Function.Iterate

/-!
# Iterating circuits

A circuit `c` with as many outputs as inputs computes a map `c.eval I` on states. Composing `t`
copies gives `c.iterate t`, which computes the `t`-th power of that map
(`Circuit.eval_iterate`); its arbitrary weighted cost and its size are exactly `t` times those of
`c` (`Circuit.cost_program_iterate`, `Circuit.size_iterate`). Zero copies are the identity
wiring, with no gates.

When the intermediate states are needed as well, the orbit prefix can be retained within the same
budget: `Synthesis.orbit` makes every state `(c.eval I)^[j] (init x)` with `j ≤ t` available at
cost `t * c.size`, sharing each state with every later construction (`Synthesis.stages`,
`Synthesis.steps`). This uses one copy of `c` per transition, applied to wires that are already
available.

The signature and the carrier are arbitrary. Sizes bound circuits; they do not certify the running
time of any construction of them.

## Main definitions

* `Cslib.Circuits.Circuit.iterate`: `t` copies of a circuit composed in sequence.
* `Cslib.Circuits.Synthesis.stages`: the values retained through a stage.

## Main results

* `Cslib.Circuits.Circuit.eval_iterate`, `Cslib.Circuits.Circuit.cost_program_iterate`,
  `Cslib.Circuits.Circuit.size_iterate`: exact semantics, weighted cost and size.
* `Cslib.Circuits.Synthesis.steps`: a sequence of constructions adds its costs.
* `Cslib.Circuits.Synthesis.orbit`: retain an orbit prefix with one circuit per transition.

## References

* `Circuit.iterate` and its semantics and costs follow Algebraic/Iteration.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic],
  with Mathlib's `Nat.iterate` in place of its own function iteration.
* The retained orbits are adapted from lean/Proofs/{Iteration,Synthesis}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits

universe v u

variable {σ : Signature.{v}} {U : Type u}

namespace Circuit

variable {m : ℕ}

/-- `t` copies of `c` composed in sequence; zero copies are the identity wiring. -/
def iterate (c : Circuit σ m m) : ℕ → Circuit σ m m
  | 0 => Circuit.id σ m
  | t + 1 => c.comp (c.iterate t)

/-- Iterating a circuit computes the power of its map. -/
@[simp] theorem eval_iterate (c : Circuit σ m m) (I : Interpretation σ U) (t : ℕ) :
    (c.iterate t).eval I = (c.eval I)^[t] := by
  induction t with
  | zero => funext x; simp [iterate]
  | succ t ih =>
    funext x
    rw [iterate, eval_comp, ih, Function.iterate_succ_apply']

/-- Iterating a circuit multiplies its arbitrary weighted cost exactly. -/
theorem cost_program_iterate (c : Circuit σ m m) (t : ℕ) (cost : σ.Op → ℕ) :
    (c.iterate t).program.cost cost = t * c.program.cost cost := by
  induction t with
  | zero => rw [Nat.zero_mul]; exact cost_program_wiring _ cost
  | succ t ih =>
    change (c.comp (c.iterate t)).program.cost cost = _
    rw [cost_program_comp, ih, Nat.succ_mul, Nat.add_comm]

/-- Iterating a circuit multiplies its size exactly. -/
@[simp] theorem size_iterate (c : Circuit σ m m) (t : ℕ) : (c.iterate t).size = t * c.size := by
  simpa only [Program.cost_const, one_mul] using c.cost_program_iterate t (fun _ => 1)

/-- A circuit computing `f` iterates to a circuit computing the powers of `f`. -/
theorem Computes.iterate {c : Circuit σ m m} {I : Interpretation σ U}
    {f : (Fin m → U) → Fin m → U} (hc : c.Computes I f) (t : ℕ) :
    (c.iterate t).Computes I f^[t] := fun x => by
  rw [eval_iterate, show c.eval I = f from funext hc]

end Circuit

namespace Synthesis

variable {I : Interpretation σ U} {n : ℕ}

/-- The values retained through stage `t` of a straight-line construction. -/
def stages (q : ℕ → Set ((Fin n → U) → U)) (t : ℕ) : Set ((Fin n → U) → U) :=
  ⋃ j ∈ Finset.range (t + 1), q j

@[simp] theorem stages_zero (q : ℕ → Set ((Fin n → U) → U)) : stages q 0 = q 0 := by
  simp [stages]

private theorem stages_succ (q : ℕ → Set ((Fin n → U) → U)) (t : ℕ) :
    stages q (t + 1) = stages q t ∪ q (t + 1) := by
  simp [stages, Finset.range_add_one, Set.union_comm]

theorem subset_stages (q : ℕ → Set ((Fin n → U) → U)) {j t : ℕ} (hj : j ≤ t) :
    q j ⊆ stages q t := fun _ hf =>
  Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), hf⟩⟩

/-- A sequence of `t` constructions of cost `C` each costs `t * C`, and retains every stage. -/
theorem steps {s : Set ((Fin n → U) → U)} (q : ℕ → Set ((Fin n → U) → U)) (C t : ℕ)
    (hzero : q 0 ⊆ s) (hstep : ∀ j < t, Synthesis I (s ∪ stages q j) (q (j + 1)) C) :
    Synthesis I s (stages q t) (t * C) := by
  induction t with
  | zero => simpa using of_subset hzero
  | succ t ih =>
    have h := (ih fun j hj => hstep j (by omega)).comp (hstep t (by omega))
    simpa only [stages_succ, Nat.succ_mul] using h

/-- **Retained orbit prefixes.** If every coordinate of the initial state is available, then all
coordinates of the states `(c.eval I)^[j] (init x)` for `j ≤ t` become available with
`t * c.size` additional gates: one copy of `c` per transition. -/
theorem orbit {s : Set ((Fin n → U) → U)} {m : ℕ} (c : Circuit σ m m)
    (init : (Fin n → U) → Fin m → U) (hinit : ∀ i, (fun x => init x i) ∈ s) (t : ℕ) :
    Synthesis I s
      (stages (fun j => Set.range fun i x => (c.eval I)^[j] (init x) i) t) (t * c.size) := by
  refine steps _ c.size t ?_ fun j _ => ?_
  · rintro _ ⟨i, rfl⟩
    exact hinit i
  · have h := circuit (I := I) (s := s ∪ stages (fun j =>
      Set.range fun i x => (c.eval I)^[j] (init x) i) j) c
      (fun i x => (c.eval I)^[j] (init x) i)
      fun i => Or.inr (subset_stages _ le_rfl ⟨i, rfl⟩)
    simpa only [Function.iterate_succ_apply'] using h

end Synthesis

end Cslib.Circuits
