/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Frontier.TensorNetwork.ScheduledRecursion
import Complexity.Foundations.NumberTheory.Padics.AdjoinRootDigitLift
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases

/-!
# Tests for the contraction recursion

* **Renaming and lifting.** Renaming a two-edge network along a rotation of its vertices and a
  swap of its edges keeps its contraction, and the canonical lift of a network over `ℤ / 4` to `ℤ`
  (integer representatives in `{0, 1, 2, 3}`) reduces back to it.
* **Interpolation points in `O`.** For `f = U ^ 2 + U + 1`, the four binary-coordinate lifts in
  `O = ℤ_(2)[U] / (f)` have unit differences, and `ℤ_(2)` lies in `O`.
* **Correctness of the recursion over `O`**, with those four points and a constant schedule
  `a = u = 1`, `h = 3`. On a one-edge network these parameters are admissible (`3 M ≤ h u ≤ 3 M + u`
  and `M (2 L - 1) = 3 < 4`), so the root call is active (`contractRec_eq_callValue`); its children
  are not smaller and are evaluated directly. Without parameters the call is a leaf.
* **The scheduled recursion** (`ContractionSchedule.callParams`): small calls are leaves, the
  recursion is correct, and for large `s` the parameters of every active call are admissible.
-/

namespace ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.Recursion

open Polynomial Cslib.Circuits.Frontier TensorNetwork

/-! ### Renaming and lifting -/

/-- Edge `e` runs from row `e` to column `e + 2`; the tensor at `v` is `v + 1` when its edge
carries `true`, and `1` otherwise. -/
def net : TensorNetwork ℤ Bool (Fin 4) (Fin 2) where
  src e := ⟨e.val, by omega⟩
  tgt e := ⟨e.val + 2, by omega⟩
  tensor v x := if x ⟨v.val % 2, by omega⟩ then v.val + 1 else 1
  tensor_congr v x y h := by
    rw [h ⟨v.val % 2, by omega⟩ (by fin_cases v <;> decide)]

/-- Renaming the vertices by a rotation and the edges by a swap keeps the contraction. -/
example : (net.reindex (finRotate 4) (Equiv.swap 0 1)).contraction = net.contraction :=
  contraction_reindex _ _ _

/-- The same network over `ℤ / 4`. -/
def net₄ : TensorNetwork (ZMod 4) Bool (Fin 4) (Fin 2) :=
  net.map (Int.castRingHom (ZMod 4))

/-- The canonical lift of `net₄` to `ℤ`, by the integer representatives in `{0, …, 3}`, reduces
to `net₄`, so its contraction reduces to the contraction of `net₄`. -/
example : (net₄.mapFun fun x => (x.val : ℤ)).map (Int.castRingHom (ZMod 4)) = net₄ :=
  map_mapFun _ (fun x => by simp) _

/-! ### Interpolation points in `O = ℤ_(2)[U] / (U ^ 2 + U + 1)` -/

/-- `U ^ 2 + U + 1`, irreducible modulo 2. -/
noncomputable def f : ℤ[X] := X ^ 2 + X + 1

theorem f_monic : f.Monic := by unfold f; monicity!

theorem f_natDegree : f.natDegree = 2 := by unfold f; compute_degree!

theorem f_irreducible : Irreducible (f.map (Int.castRingHom (ZMod 2))) := by
  unfold f
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
    simp [this]
  · intro x hx
    rw [IsRoot.def, eval_add, eval_add, eval_pow, eval_X, eval_one] at hx
    fin_cases x <;> revert hx <;> decide

/-- The field `K = ℚ[U] / (U ^ 2 + U + 1)`. -/
abbrev K : Type := AdjoinRoot (f.map (Int.castRingHom ℚ))

/-- The ring `O = ℤ_(2)[U] / (U ^ 2 + U + 1)`, the valuation ring of `K`. -/
noncomputable abbrev O : Subring K := (AdjoinRoot.padicValuation 2 f_monic f_irreducible).integer

/-- `ℤ_(2)` lies in `O`: the valuation of `K` extends that of `ℚ`. -/
theorem hO : ∀ c ∈ Valuation.integer (Rat.padicValuation 2), algebraMap ℚ K c ∈ O := fun c hc => by
  rw [Valuation.mem_integer_iff, AdjoinRoot.padicValuation_algebraMap]
  exact hc

/-- There are `2 ^ 2 = 4` digit vectors. -/
theorem card_digits : Fintype.card (Fin f.natDegree → ZMod 2) = 4 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, f_natDegree]
  norm_num

/-- The four binary-coordinate lifts `0, 1, U, 1 + U`, in some order. -/
noncomputable def pts (k : Fin 4) : O :=
  AdjoinRoot.integerDigitLift f_monic f_irreducible
    ((Fintype.equivFin (Fin f.natDegree → ZMod 2)).symm (Fin.cast card_digits.symm k))

/-- **The binary-coordinate lifts are interpolation points**: their differences are units of `O`. -/
theorem pts_pairwise : Pairwise fun k l => IsUnit (pts k - pts l) := fun _ _ hkl =>
  AdjoinRoot.pairwise_isUnit_integerDigitLift_sub f_monic f_irreducible fun h =>
    hkl (Fin.cast_injective _ ((Fintype.equivFin _).symm.injective h))

/-! ### The recursion over `O` -/

/-- Direct contraction is a correct oracle. -/
example : ContractionOracle.Correct (B := O) fun _ _ N _ _ => N.contraction :=
  fun _ _ _ _ _ => ⟨0, by simp⟩

/-- The constant schedule `a = u = 1`, `h = 3`, with degree bound `1`. -/
def sched (_ _ : ℕ) : Option TensorNetwork.CallParams := some ⟨1, 1, 3, 1⟩

/-- On one edge with four points the schedule is admissible. -/
example : (TensorNetwork.CallParams.mk 1 1 3 1).Admissible 1 4 := by decide

/-- One edge from row `0` to column `1`, with tensor `(1, 2)` at the row and `(1, 1)` at the
column. -/
noncomputable def net₁ : TensorNetwork O Bool (Fin 2) (Fin 1) where
  src _ := 0
  tgt _ := 1
  tensor v x := if v = 0 ∧ x 0 then 2 else 1
  tensor_congr v x y h := by rw [h 0 (by fin_cases v <;> simp)]

/-- **The root call is active**: it is the active call of `callValue` with the packing of
Lemma D.3, the four lifts as interpolation points, and recursive calls at depth one for the
children with fewer edges. -/
example (p : ℕ) :
    contractRec O hO sched pts 0 2 1 net₁ (fun v => decide (v = 0)) p =
      callValue O hO
        (fun n' m' N' side' p' =>
          if m' < 1 then contractRec O hO sched pts 1 n' m' N' side' p' else N'.contraction)
        net₁ (fun v => decide (v = 0)) (fun _ => rfl) (fun _ => rfl)
        (Cslib.PacketPacking.packing net₁.src net₁.tgt 1 64) p 1 3 le_rfl pts :=
  contractRec_eq_callValue (θ := ⟨1, 1, 3, 1⟩) rfl
    ⟨⟨fun _ => rfl, fun _ => rfl, fun _ => (Finset.card_filter_le _ _).trans (by simp),
      fun _ => (Finset.card_filter_le _ _).trans (by simp)⟩, by decide⟩ p

/-- With no parameters, a call is a leaf and returns the contraction. -/
example (p : ℕ) :
    contractRec O hO (fun _ _ => none) pts 0 2 1 net₁ (fun v => decide (v = 0)) p =
      net₁.contraction :=
  contractRec_of_sched_eq_none rfl p

/-- **The recursion is correct**: at every precision, the root call returns the contraction of
`net₁` modulo `2 ^ p`. -/
example (p : ℕ) :
    Ideal.Quotient.mk (twoPowIdeal O p)
        (contractRec O hO sched pts 0 2 1 net₁ (fun v => decide (v = 0)) p) =
      Ideal.Quotient.mk (twoPowIdeal O p) net₁.contraction :=
  mk_contractRec O hO sched pts pts_pairwise 0 2 1 net₁ _ p

/-- The recursion is correct for every schedule and every network. -/
example (sched' : ℕ → ℕ → Option TensorNetwork.CallParams) (n m p : ℕ)
    (N : TensorNetwork O Bool (Fin n) (Fin m)) (side : Fin n → Bool) :
    ∃ c : O, contractRec O hO sched' pts 0 n m N side p = N.contraction + 2 ^ p * c :=
  exists_contractRec_eq_add O hO sched' pts pts_pairwise 0 n m N side p

/-! ### The scheduled recursion -/

open Cslib.Circuits.Frontier.ContractionSchedule in
/-- With the parameter schedule, a call with at most `leafSize s` edges is a leaf. -/
example (s n m p : ℕ) (hm : m ≤ leafSize s) (N : TensorNetwork O Bool (Fin n) (Fin m))
    (side : Fin n → Bool) :
    contractRec O hO (callParams s) pts 0 n m N side p = N.contraction :=
  contractRec_of_sched_eq_none (callParams_of_le hm) p

open Cslib.Circuits.Frontier.ContractionSchedule in
/-- With the parameter schedule, the recursion is correct. -/
example (s n m p : ℕ) (N : TensorNetwork O Bool (Fin n) (Fin m)) (side : Fin n → Bool) :
    ∃ c : O, contractRec O hO (callParams s) pts 0 n m N side p = N.contraction + 2 ^ p * c :=
  exists_contractRec_eq_add O hO (callParams s) pts pts_pairwise 0 n m N side p

open Cslib.Circuits.Frontier.ContractionSchedule in
/-- For large `s`, the parameters of every active call are admissible with `2 ^ (4 ⌊log₂ s⌋)`
points, so its guard reduces to the network running from rows to columns within the degree
bound. -/
example (C : ℕ) : ∃ s₀, ∀ s, s₀ ≤ s → ∀ d M p, Active C s d M p →
    (TensorNetwork.CallParams.mk (slotBits s d) (taper s d) (taperStep s d M)
      (degreeBound s)).Admissible M (2 ^ (4 * Nat.log 2 s)) := by
  obtain ⟨s₀, hs₀⟩ := exists_activeBounds C
  exact ⟨s₀, fun s hs d M p hA => ((hs₀ s hs).2 d M p hA).admissible le_rfl⟩

end ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.Recursion
