/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Discrepancy
public import CslibFrontier.Computability.Communication.NOF.Discrepancy
public import Mathlib.Data.Fin.Tuple.Basic
import CslibFrontier.Probability.PMF.Map

/-!
# Two-player number-on-forehead protocols

With two players, the player with `x 0` on their forehead sees exactly `x 1` and the other player
sees exactly `x 0`, so a two-party protocol (`Cslib.Communication.Protocol`) can be played by
players `Fin 2`, with player `1` as Alice, who holds `x 0`, and player `0` as Bob.
A two-party protocol runs as a two-player NOF protocol with the same depth
(`NOF.Protocol.ofTwoParty`), so two-party upper bounds are NOF upper bounds
(`NOF.Protocol.ecomplexityFun_le_twoParty`). Cylinder intersections for two players are rectangles,
and the NOF discrepancy is the two-party discrepancy of `Cslib.Communication.discrepancy`
(`NOF.discrepancy_fin_two`), so with two players the NOF discrepancy bound of
`Cslib.Communication.NOF.Protocol.two_mul_le_two_pow_mul_discrepancy` is the two-party one.

## Main definitions

* `Cslib.Communication.NOF.Protocol.ofTwoParty`: a two-party protocol as a two-player NOF protocol.

## Main results

* `Cslib.Communication.NOF.Protocol.ecomplexityFun_le_twoParty`: two-party protocols are NOF
  protocols.
* `Cslib.Communication.NOF.discrepancy_fin_two`: with two players the NOF discrepancy is the
  two-party discrepancy.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Communication.NOF

open Finset BitString Probability

universe v w

variable {X : Fin 2 → Type v} {Z : Type w}

theorem view_zero_apply_one (x : ∀ i, X i) : view 0 x ⟨1, Fin.zero_ne_one.symm⟩ = x 1 :=
  rfl

theorem view_one_apply_zero (x : ∀ i, X i) : view 1 x ⟨0, Fin.zero_ne_one⟩ = x 0 :=
  rfl

/-- With two players, player `0` sees `x 1` and nothing else. -/
theorem view_zero_eq_iff {x y : ∀ i, X i} : view 0 x = view 0 y ↔ x 1 = y 1 := by
  refine ⟨fun h => congrFun h ⟨1, Fin.zero_ne_one.symm⟩, fun h => funext fun ⟨j, hj⟩ => ?_⟩
  obtain rfl : j = 1 := by omega
  exact h

/-- With two players, player `1` sees `x 0` and nothing else. -/
theorem view_one_eq_iff {x y : ∀ i, X i} : view 1 x = view 1 y ↔ x 0 = y 0 := by
  refine ⟨fun h => congrFun h ⟨0, Fin.zero_ne_one⟩, fun h => funext fun ⟨j, hj⟩ => ?_⟩
  obtain rfl : j = 0 := by omega
  exact h

namespace Protocol

/-- A two-party protocol as a two-player number-on-forehead protocol: Alice, who holds `x 0`, is
player `1`, who sees `x 0`, and Bob, who holds `x 1`, is player `0`. -/
def ofTwoParty : Communication.Protocol (X 0) (X 1) Z → Protocol X Z
  | .output z => output z
  | .alice send p₀ p₁ =>
      speak 1 (fun v => send (v ⟨0, Fin.zero_ne_one⟩)) (ofTwoParty p₀) (ofTwoParty p₁)
  | .bob send p₀ p₁ =>
      speak 0 (fun v => send (v ⟨1, Fin.zero_ne_one.symm⟩)) (ofTwoParty p₀) (ofTwoParty p₁)

@[simp] theorem run_ofTwoParty (p : Communication.Protocol (X 0) (X 1) Z) (x : ∀ i, X i) :
    (ofTwoParty p).run x = p.run (x 0) (x 1) := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ => simp [ofTwoParty, ih₀, ih₁]
  | bob send p₀ p₁ ih₀ ih₁ => simp [ofTwoParty, ih₀, ih₁]

@[simp] theorem depth_ofTwoParty (p : Communication.Protocol (X 0) (X 1) Z) :
    (ofTwoParty p).depth = p.depth := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ => simp [ofTwoParty, ih₀, ih₁]
  | bob send p₀ p₁ ih₀ ih₁ => simp [ofTwoParty, ih₀, ih₁]

/-- **Two-party protocols are two-player NOF protocols**: computing `f` with two players costs at
most the two-party communication complexity of `f` read as a function of `x 0` and `x 1`. -/
theorem ecomplexityFun_le_twoParty (f : (∀ i, X i) → Z) :
    ecomplexityFun f ≤
      Communication.Protocol.ecomplexityFun fun (a : X 0) (b : X 1) =>
        f ((piFinTwoEquiv X).symm (a, b)) := by
  refine Communication.Protocol.le_ecomplexityFun_iff.mpr fun p hp => ?_
  refine (ecomplexityFun_le_depth (p := ofTwoParty p) (funext fun x => ?_)).trans_eq
    (by rw [depth_ofTwoParty])
  rw [run_ofTwoParty, hp]
  exact congrArg f ((piFinTwoEquiv X).symm_apply_apply x)

end Protocol

/-! ### Discrepancy -/

variable [∀ i, Fintype (X i)]

/-- The signed sum over the rectangle `A × B` under `ν` is the signed sum over the cylinder
intersection of the tests `φ`, when the tests of players `1` and `0` accept exactly `A` and
`B`. -/
private theorem sum_cylinderIntersection_eq_sum_rectangle (ν : PMF (∀ i, X i))
    (f : (∀ i, X i) → Bool) (φ : ∀ i, View X i → Bool) (A : Finset (X 0)) (B : Finset (X 1))
    (hφ : ∀ x, x ∈ cylinderIntersection φ ↔ x 0 ∈ A ∧ x 1 ∈ B) :
    ∑ x with x ∈ cylinderIntersection φ, (ν x).toReal * signVal (f x) =
      ∑ a ∈ A, ∑ b ∈ B, ((ν.map (piFinTwoEquiv X)) (a, b)).toReal *
        signVal (f ((piFinTwoEquiv X).symm (a, b))) := by
  rw [← sum_product']
  refine sum_nbij' (fun x => (x 0, x 1)) (fun q => (piFinTwoEquiv X).symm q) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simpa [mem_product] using (hφ x).mp (mem_filter.mp hx).2
  · intro q hq
    refine mem_filter.mpr ⟨mem_univ _, (hφ _).mpr ?_⟩
    simpa [mem_product, piFinTwoEquiv] using hq
  · intro x _
    exact (piFinTwoEquiv X).symm_apply_apply x
  · intro q _
    exact (piFinTwoEquiv X).apply_symm_apply q
  · intro x _
    have hx : (piFinTwoEquiv X).symm (x 0, x 1) = x := (piFinTwoEquiv X).symm_apply_apply x
    rw [PMF.map_equiv_apply, hx]

/-- **With two players the NOF discrepancy is the two-party discrepancy**: the cylinder
intersections of two players are the rectangles. -/
theorem discrepancy_fin_two (ν : PMF (∀ i, X i)) (f : (∀ i, X i) → Bool) :
    discrepancy ν f =
      Communication.discrepancy (ν.map (piFinTwoEquiv X))
        fun a b => f ((piFinTwoEquiv X).symm (a, b)) := by
  classical
  refine le_antisymm ?_ ?_
  · -- A cylinder intersection of two players is the rectangle of the inputs each player accepts.
    obtain ⟨φ, hφD⟩ := exists_abs_sum_eq_discrepancy ν f
    let A : Finset (X 0) := {a | ∃ x : ∀ i, X i, x 0 = a ∧ φ 1 (view 1 x) = true}
    let B : Finset (X 1) := {b | ∃ x : ∀ i, X i, x 1 = b ∧ φ 0 (view 0 x) = true}
    have hφ (x : ∀ i, X i) : x ∈ cylinderIntersection φ ↔ x 0 ∈ A ∧ x 1 ∈ B := by
      simp only [mem_cylinderIntersection, Fin.forall_fin_two, A, B, mem_filter, mem_univ,
        true_and]
      refine ⟨fun ⟨h0, h1⟩ => ⟨⟨x, rfl, h1⟩, ⟨x, rfl, h0⟩⟩, ?_⟩
      rintro ⟨⟨y, hy, h1⟩, ⟨z, hz, h0⟩⟩
      exact ⟨view_zero_eq_iff.mpr hz ▸ h0, view_one_eq_iff.mpr hy ▸ h1⟩
    rw [← hφD, sum_cylinderIntersection_eq_sum_rectangle ν f φ A B hφ]
    exact Communication.abs_sum_le_discrepancy _ _ A B
  · -- A rectangle is the cylinder intersection of the tests `x 1 ∈ S.2` and `x 0 ∈ S.1`.
    obtain ⟨A, B, hAB⟩ := Communication.exists_abs_sum_eq_discrepancy
      (ν.map (piFinTwoEquiv X)) fun a b => f ((piFinTwoEquiv X).symm (a, b))
    have hC : IsCylinderIntersection {x : ∀ i, X i | x 0 ∈ A ∧ x 1 ∈ B} :=
      ⟨fun i => {x | i = 0 → x 1 ∈ B} ∩ {x | i = 1 → x 0 ∈ A},
        fun i x a => by fin_cases i <;> simp, by ext x; simp [Fin.forall_fin_two, and_comm]⟩
    obtain ⟨φ, hφ⟩ := isCylinderIntersection_iff.mp hC
    rw [← hAB, ← sum_cylinderIntersection_eq_sum_rectangle ν f φ A B
      fun x => (Set.ext_iff.mp hφ x).symm]
    exact abs_sum_le_discrepancy ν f φ

end Cslib.Communication.NOF
