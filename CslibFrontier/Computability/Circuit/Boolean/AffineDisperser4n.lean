/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Step
public import CslibFrontier.Computability.Circuit.Boolean.SemiCircuit.OfCircuit

/-!
# The `4n - 10d` circuit size lower bound for affine dispersers

This module proves the `4n - 10d` size lower bound (`Theorem 4.1` per issue `#4322`, unverified
against [Mishra and Santhanam][MishraSanthanam2027] because the submission PDF returned HTTP 1042):
any general Boolean circuit (`fullSignature 2 Bool`) computing a `d`-affine disperser `f` on `n`
bits has size at least `4 * n - 10 * d`, i.e., `4 * n ≤ C.size + 10 * d`
(`Cslib.Circuits.Boolean.AffineDisperser4n.four_mul_le_size_add`).

Circuits are formalized over `fullSignature 2 Bool`, where a constant also costs a gate; the
source lets circuits read constants for free, so the bound holds here a fortiori (Lean's bound
is weaker than the source's by at most the two constant gates; `AffineDisperser.lean` uses the
same convention). This module proves only the size bound and the non-constructive existence of a
constant affine subspace / disagreeing input (`exists_affine_subspace_const_of_size_lt`,
`exists_disagreeing_input_of_size_lt`); the deterministic `poly(n, 2^d)`-time refuter clause
reported on `#4322` remains open (Milestone 4).

The potential of a state (`State.W`) is `s + 4 q + 6 · #{used unpaired parameters}`. Starting from
the initial state `initialState C` with `a = n`, `s = C.size`, `q = 0`, and
`W ≤ C.size + 6 * n`, iterating `Lemma 4.2` (`State.Valid.exists_step`, label per `#4322`)
establishes `10 * S.a ≤ S.W + 10 * d` for every valid state (`State.Valid.ten_mul_a_le`), yielding
`10 * n ≤ C.size + 6 * n + 10 * d`, hence `4 * n ≤ C.size + 10 * d`.

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser4n.initialState`: the initial zero-locus state of a
  circuit.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.ten_mul_a_le`: `10 * S.a ≤ S.W + 10 * d`
  for every valid state of a `d`-affine disperser.
* `Cslib.Circuits.Boolean.AffineDisperser4n.four_mul_le_size_add`: the `4n - 10d` lower bound
  `4 * n ≤ C.size + 10 * d` (size-bound clause of `Theorem 4.1` per `#4322`).
* `Cslib.Circuits.Boolean.AffineDisperser4n.exists_affine_subspace_const_of_size_lt`: any
  circuit with `C.size + 10 * d < 4 * n` is constant on some `d`-dimensional affine subspace.
* `Cslib.Circuits.Boolean.AffineDisperser4n.exists_disagreeing_input_of_size_lt`: non-constructive
  disagreement witness for any circuit with `C.size + 10 * d < 4 * n` against any `d`-affine
  disperser.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 4n - O(log n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2027] (submission PDF inaccessible with HTTP 1042; cited
  labels follow issue `#4322` and are unverified against the manuscript)
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Finset Cslib.Circuits Cslib.BitString SemiCircuit

namespace State

private theorem Valid.ten_mul_a_le_aux {n : ℕ} {f : BooleanFunction n} {d : ℕ}
    (hf : IsAffineDisperser f d) :
    ∀ k (S : State n), S.Valid f → S.m + S.s ≤ k → 10 * S.a ≤ S.W + 10 * d := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro S hS hk
    by_cases ha : d < S.a
    · obtain ⟨S', hstep⟩ := hS.exists_step hf ha
      have hih := ih (S'.m + S'.s) (Nat.lt_of_lt_of_le hstep.lt hk) S' hstep.valid le_rfl
      have hp := hstep.potential
      omega
    · omega

/-- Every valid state of a `d`-affine disperser satisfies `10 * S.a ≤ S.W + 10 * d`. -/
theorem Valid.ten_mul_a_le {n : ℕ} {f : BooleanFunction n} {d : ℕ} {S : State n}
    (hS : S.Valid f) (hf : IsAffineDisperser f d) : 10 * S.a ≤ S.W + 10 * d :=
  ten_mul_a_le_aux hf (S.m + S.s) S hS le_rfl

end State

/-- The initial gate-elimination state of a general Boolean circuit `C`. -/
@[expose] def initialState {n : ℕ} (C : Circuit (fullSignature 2 Bool) n 1) : State n where
  toSemiCircuit := ofCircuit C
  pairs := ∅
  phi val i := val i

/-- The initial state of a circuit computing `f` is valid. -/
theorem initialState_valid {n : ℕ} {f : BooleanFunction n}
    {C : Circuit (fullSignature 2 Bool) n 1}
    (hC : C.Computes fullInterpretation (single f)) : (initialState C).Valid f where
  wf := wellFormed_ofCircuit C
  pair_mem _ h := absurd h (Finset.notMem_empty _)
  pairs_disjoint _ h := absurd h (Finset.notMem_empty _)
  phi_congr val val' hv := by
    ext i
    exact hv i (by
      change ↑i ∈ (ofCircuit C).params
      rw [ofCircuit_params]
      exact Finset.mem_range.2 i.isLt)
  phi_affine _ _ _ := rfl
  phi_injective val val' hv j hj := by
    change j ∈ (ofCircuit C).params at hj
    rw [ofCircuit_params, Finset.mem_range] at hj
    exact congrFun hv ⟨j, hj⟩
  computes val hval _ := by
    change (ofCircuit C).out.eval val = f (fun i => val i)
    rw [out_eval_ofCircuit C hval]
    exact congrFun (hC fun i => val i) 0

/-- The initial state has effective affine dimension `n`. -/
theorem initialState_a {n : ℕ} (C : Circuit (fullSignature 2 Bool) n 1) :
    (initialState C).a = n := by
  change (ofCircuit C).params.card - (∅ : Finset ZeroPair).card = n
  rw [ofCircuit_params, Finset.card_range, Finset.card_empty, Nat.sub_zero]

/-- The initial state has potential at most `C.size + 6 * n`. -/
theorem initialState_W_le {n : ℕ} (C : Circuit (fullSignature 2 Bool) n 1) :
    (initialState C).W ≤ C.size + 6 * n := by
  have hs : (initialState C).s = C.size := by
    change (ofCircuit C).gates.card + (ofCircuit C).eqns.card = C.size
    rw [ofCircuit_gates, ofCircuit_eqns, Nat.card_Ico, Finset.card_empty,
      Nat.add_sub_cancel_left, add_zero]
  have hq : (initialState C).q = 0 := Finset.card_empty
  have hwt : ∑ x ∈ (initialState C).unpaired, weight ((initialState C).deg x) ≤ 6 * n := by
    calc
      ∑ x ∈ (initialState C).unpaired, weight ((initialState C).deg x)
        ≤ ∑ _ ∈ (initialState C).unpaired, 6 :=
          Finset.sum_le_sum fun _ _ => weight_le_six _
      _ = (initialState C).unpaired.card * 6 := Finset.sum_const_nat fun _ _ => rfl
      _ ≤ (initialState C).params.card * 6 :=
          Nat.mul_le_mul_right 6 (Finset.card_le_card (Finset.filter_subset _ _))
      _ = 6 * n := by
          change (ofCircuit C).params.card * 6 = 6 * n
          rw [ofCircuit_params, Finset.card_range, mul_comm]
  change (initialState C).s + 4 * (initialState C).q +
      ∑ x ∈ (initialState C).unpaired, weight ((initialState C).deg x) ≤ C.size + 6 * n
  omega

/-- Size lower bound `4 * n ≤ C.size + 10 * d` for any `fullSignature 2 Bool` circuit computing a
`d`-affine disperser on `n` bits (label `Theorem 4.1` per `#4322`, unverified against
[MishraSanthanam2027]; the `poly(n, 2^d)` refuter clause remains open, and constants count as gates
under `fullSignature 2 Bool`). -/
theorem four_mul_le_size_add {n : ℕ} {f : BooleanFunction n} {d : ℕ}
    (hf : IsAffineDisperser f d) (C : Circuit (fullSignature 2 Bool) n 1)
    (hC : C.Computes fullInterpretation (single f)) :
    4 * n ≤ C.size + 10 * d := by
  have hW := (initialState_valid hC).ten_mul_a_le hf
  have ha := initialState_a C
  have hWle := initialState_W_le C
  omega

/-- Any circuit of size strictly below `4 * n - 10 * d` is constant on some `d`-dimensional
injective affine subspace (hence cannot compute a `d`-affine disperser). -/
theorem exists_affine_subspace_const_of_size_lt {n d : ℕ}
    (C : Circuit (fullSignature 2 Bool) n 1) (hC : C.size + 10 * d < 4 * n) :
    ∃ g : BitString d → BitString n, IsAffine g ∧ Function.Injective g ∧
      ∃ b : Bool, ∀ u, C.eval fullInterpretation (g u) 0 = b := by
  by_contra hno
  push Not at hno
  let fC : BooleanFunction n := fun x => C.eval fullInterpretation x 0
  have hfC : IsAffineDisperser fC d := fun g hg hinj => by
    obtain ⟨u, hu⟩ := hno g hg hinj (fC (g 0))
    exact ⟨u, 0, hu⟩
  have hcomp : C.Computes fullInterpretation (single fC) := fun x => by
    ext i
    rw [Fin.eq_zero i]
    rfl
  have hlb := four_mul_le_size_add hfC C hcomp
  omega

/-- Every circuit of size strictly below `4 * n - 10 * d` disagrees with any `d`-affine
disperser on some input (coming from a `d`-dimensional affine subspace on which `C` is constant). -/
theorem exists_disagreeing_input_of_size_lt {n d : ℕ} {f : BooleanFunction n}
    (hf : IsAffineDisperser f d) (C : Circuit (fullSignature 2 Bool) n 1)
    (hC : C.size + 10 * d < 4 * n) :
    ∃ x : BitString n, C.eval fullInterpretation x 0 ≠ f x := by
  obtain ⟨g, hg, hinj, b, hb⟩ := exists_affine_subspace_const_of_size_lt C hC
  obtain ⟨u, v, huv⟩ := hf g hg hinj
  by_cases hu : C.eval fullInterpretation (g u) 0 = f (g u)
  · refine ⟨g v, ?_⟩
    rw [hb v, ← hb u, hu]
    exact huv
  · exact ⟨g u, hu⟩

end Cslib.Circuits.Boolean.AffineDisperser4n
