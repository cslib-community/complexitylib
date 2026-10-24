/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AffineDisperser.Step
public import Complexity.Computability.Circuit.Boolean.SemiCircuit.OfCircuit

/-!
# A `3.5 n - 7 d` lower bound for affine dispersers

**Theorem 4.1** of [Mishra and Santhanam][MishraSanthanam2026]: every circuit over the full
binary basis `B₂` computing an affine disperser for dimension `d` on `n` bits has at least
`3.5 n - 7 d` gates (`Cslib.Circuits.Boolean.AffineDisperser.seven_mul_le_two_mul_size_add`).
This improves the `3.1 n - o(n)` lower bound of [Li and Yang][LiYang2022], itself improving the
`(3 + 1/86) n - o(n)` bound of [Find, Golovnev, Hirsch and Kulikov][FindGolovnevHirschKulikov2016],
whose fair semi-circuits (`Cslib.Circuits.Boolean.SemiCircuit`) carry the gate elimination.

The proof starts gate elimination from the circuit itself (`initialState`): its inputs are the
parameters, its gates the acyclic part, the affine system is empty and the parameter map is the
identity, so `a = n` and `W ≤ 2 |C| + 7 n`. Every valid state satisfies `14 a ≤ W + 14 d`
(`State.Valid.fourteen_mul_a_le`), by induction on `m + s` along the steps of Lemma 4.2
(`State.Valid.exists_step`), so `14 n ≤ 2 |C| + 7 n + 14 d`.

The circuits are those of cslib over `fullSignature 2 Bool`, where a constant also costs a gate;
the source lets circuits read constants for free, so the bound holds here a fortiori.

The development is organised as follows.

* `AffineDisperser.State`: the states of gate elimination, their potential, Proposition 2.2 and
  Lemma 2.3 of the source.
* `AffineDisperser.Operations`, `AffineDisperser.Reparameterisation`, `AffineDisperser.Rewiring`:
  the operations on states (restrictions and deletions; exchanging a parameter with an auxiliary
  variable and the quadratic substitution; moving and rewiring gates), with validity.
* `AffineDisperser.Reduction`: reductions, which restrict parameters and delete constraints, and
  their accounting, done once for all reductions.
* `AffineDisperser.Deletion`, `AffineDisperser.Normal`: the preliminary reductions of
  Section 4.1.
* `AffineDisperser.MinimalAnd`: restructuring the minimal AND, Section 4.2.
* `AffineDisperser.Elimination`: eliminating the minimal AND, Section 4.3.
* `AffineDisperser.Step`: Lemma 4.2, one step of gate elimination.

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.initialState`: the initial state of gate elimination.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.fourteen_mul_a_le`: the potential bound.
* `Cslib.Circuits.Boolean.AffineDisperser.seven_mul_le_two_mul_size_add`: Theorem 4.1.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
* [J. Li and T. Yang, *3.1n − o(n) Circuit Lower Bounds for Explicit Functions*][LiYang2022]
* [M. G. Find, A. Golovnev, E. A. Hirsch and A. S. Kulikov, *A better-than-3n lower bound for the
  circuit complexity of an explicit function*][FindGolovnevHirschKulikov2016]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Cslib.Circuits Cslib.BitString SemiCircuit

variable {n : ℕ} {f : BooleanFunction n}

/-! ### The potential bound -/

/-- Every valid state for an affine disperser for dimension `d` satisfies `14 a ≤ W + 14 d`:
apply Lemma 4.2 until `a ≤ d`, adding up `ΔW ≤ 14 Δa`. -/
theorem State.Valid.fourteen_mul_a_le {d : ℕ} (hf : IsAffineDisperser f d) :
    ∀ S : State n, S.Valid f → 14 * S.a ≤ S.W + 14 * d := by
  intro S
  induction h : S.m + S.s using Nat.strong_induction_on generalizing S with
  | _ k ih =>
    intro hS
    by_cases ha : S.a ≤ d
    · omega
    · obtain ⟨S', hstep⟩ := hS.exists_step hf (lt_of_not_ge ha)
      have := ih _ (h ▸ hstep.lt) S' rfl hstep.valid
      have := hstep.potential
      omega

/-! ### The initial state of a circuit -/

/-- The initial state of gate elimination for a circuit: its semi-circuit
(`SemiCircuit.ofCircuit`), whose parameters are the inputs, with no pairs and the parameter map
reading the inputs. -/
def initialState (C : Circuit (fullSignature 2 Bool) n 1) : State n where
  toSemiCircuit := SemiCircuit.ofCircuit C
  pairs := ∅
  phi val := fun i => val i

/-- The initial state of a circuit computing `f` is valid. -/
theorem initialState_valid {C : Circuit (fullSignature 2 Bool) n 1}
    (hC : C.Computes fullInterpretation (single f)) : (initialState C).Valid f where
  wf := wellFormed_ofCircuit C
  pair_mem := fun pr hpr => by simp [initialState] at hpr
  pairs_disjoint := fun pr hpr => by simp [initialState] at hpr
  phi_congr := fun val val' h => funext fun i => h i (Finset.mem_range.2 i.2)
  phi_affine := fun k σ hσ _ u v w => funext fun i => congrFun (hσ u v w) i
  phi_injective := fun val val' h j hj => by
    have := congrFun h ⟨j, Finset.mem_range.1 hj⟩
    simpa [initialState] using this
  computes := fun val hval => by
    rw [show (initialState C).out.eval val = _ from out_eval_ofCircuit C hval, hC]
    rfl

theorem initialState_a (C : Circuit (fullSignature 2 Bool) n 1) : (initialState C).a = n := by
  simp [State.a, State.m, State.q, initialState]

private theorem initialState_W_le (C : Circuit (fullSignature 2 Bool) n 1) :
    (initialState C).W ≤ 2 * C.size + 7 * n := by
  have hs : (initialState C).s = C.size := by
    simp [State.s, SemiCircuit.size, initialState]
  have hq : (initialState C).q = 0 := by simp [State.q, initialState]
  unfold State.W
  rw [hs, hq]
  have : ∑ x ∈ (initialState C).unpaired, weight ((initialState C).deg x) ≤ 7 * n := by
    calc ∑ x ∈ (initialState C).unpaired, weight ((initialState C).deg x)
        ≤ ∑ _x ∈ (initialState C).unpaired, 7 := Finset.sum_le_sum fun _ _ => weight_le_seven _
      _ = 7 * (initialState C).unpaired.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 7 * n := by
        have : (initialState C).unpaired.card ≤ n :=
          (Finset.card_filter_le _ _).trans (by simp [initialState])
        omega
  omega

/-! ### Theorem 4.1 -/

/-- **Theorem 4.1** of [Mishra and Santhanam][MishraSanthanam2026]: every circuit over the full
binary basis computing an affine disperser for dimension `d` on `n` bits has at least
`3.5 n - 7 d` gates, stated without subtraction as `7 n ≤ 2 |C| + 14 d`. -/
theorem seven_mul_le_two_mul_size_add {d : ℕ} (hf : IsAffineDisperser f d)
    (C : Circuit (fullSignature 2 Bool) n 1) (hC : C.Computes fullInterpretation (single f)) :
    7 * n ≤ 2 * C.size + 14 * d := by
  have h := State.Valid.fourteen_mul_a_le hf _ (initialState_valid hC)
  rw [initialState_a] at h
  have := initialState_W_le C
  omega

end Cslib.Circuits.Boolean.AffineDisperser
