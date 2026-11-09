/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.DistinguishedPoints
import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.ForestDuality
import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.Spectrum

/-!
# Cycle-spectrum reduction, forest duality, and distinguished-point tests

Exercise cycle-spectrum reduction (`iterate_eq_card_add_mod`, `cycleSpectrum_test`,
`perm_symm_eq_iterate`), canonical hitting-time phase identities (`canonicalTime_apply`,
`iterate_eq_canonical_iff`), forest path packing / hitting-set duality (`forest_duality`), and
distinguished-point semantics (`distinguishedPower_correct`) on concrete finite functional graphs.
-/

namespace CslibFrontierTests.FunctionalGraphSpectrum

open Cslib.FunctionalGraph Cslib.FunctionalGraph.ForestDuality Function

/-! ### Cycle-spectrum reduction and phase identities -/

/-- The swap permutation on `Fin 2`. -/
private def swap2 : Equiv.Perm (Fin 2) := Equiv.swap 0 1

example (x : Fin 2) (T : ℕ) (hT : Fintype.card (Fin 2) ≤ T) :
    (swap2 : Fin 2 → Fin 2)^[T] x =
      (swap2 : Fin 2 → Fin 2)^[Fintype.card (Fin 2) +
        (T - Fintype.card (Fin 2)) % cycleLength (swap2 : Fin 2 → Fin 2) x] x :=
  iterate_eq_card_add_mod (swap2 : Fin 2 → Fin 2) x hT

example (x : Fin 2) :
    swap2.symm x = (swap2 : Fin 2 → Fin 2)^[cycleLength (swap2 : Fin 2 → Fin 2) x - 1] x :=
  perm_symm_eq_iterate swap2 x

example (f : Fin 4 → Fin 4) (x : Fin 4) :
    IsLeast {ℓ ∈ cycleSpectrum f | f^[Fintype.card (Fin 4) + ℓ] x = f^[Fintype.card (Fin 4)] x}
      (cycleLength f x) :=
  cycleSpectrum_test f x

example (f : Fin 4 → Fin 4) (x : Fin 4) (hx : x ∉ periodicPts f) :
    canonicalTime f (f x) + 1 = canonicalTime f x :=
  canonicalTime_apply f x hx

example (f : Fin 4 → Fin 4) (x : Fin 4) {T : ℕ} (hT : transientDepth f x ≤ T) (a : ℕ) :
    f^[T] x = f^[a] (canonicalCycle f x) ↔
      a + canonicalTime f x ≡ T [MOD cycleLength f x] :=
  iterate_eq_canonical_iff f x hT a

/-! ### Forest path packing / hitting-set duality -/

/-- Partial parent map on `Fin 4` sending `0` to `none` and `x > 0` to `some (x / 2)`. -/
private def halfParent (x : Fin 4) : Option (Fin 4) :=
  if x.val = 0 then none else some ⟨x.val / 2, by omega⟩

private theorem halfParent_acyclic : Acyclic halfParent := by
  intro x k hk hper
  have hlt : ∀ m : ℕ, 0 < m → ∀ y z : Fin 4, iter halfParent m y = some z → z.val < y.val := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      intro y z hyz
      rw [iter, Option.bind_eq_some_iff] at hyz
      obtain ⟨w, hwy, hwz⟩ := hyz
      unfold halfParent at hwz
      split_ifs at hwz with hw0
      simp only [Option.some.injEq] at hwz
      have hzw : z.val < w.val := by
        rw [← hwz]
        dsimp
        omega
      rcases Nat.eq_zero_or_pos m with rfl | hm'
      · simp only [iter, Option.some.injEq] at hwy
        subst hwy
        exact hzw
      · exact Nat.lt_trans hzw (ih hm' y w hwy)
  exact Nat.lt_irrefl x.val (hlt k hk x x hper)

example (r : Fin 4 → ℕ) (S : Finset (Fin 4)) :
    ∃ H : Finset (Fin 4), ∃ P : Finset (FPath (Fin 4)),
      Covers halfParent r S H ∧ Packing halfParent r S P ∧ P.card = H.card ∧
      (∀ H' : Finset (Fin 4), Covers halfParent r S H' → H.card ≤ H'.card) ∧
      (∀ P' : Finset (FPath (Fin 4)), Packing halfParent r S P' → P'.card ≤ P.card) :=
  forest_duality halfParent halfParent_acyclic r S

/-! ### Distinguished-point evaluation -/

example (x : Fin 2) :
    distinguishedPower (swap2 : Fin 2 → Fin 2) (fun y => y = 0) 2 5
      (fun h => (swap2 : Fin 2 → Fin 2)^[3] h) (fun l => 3 % l) x =
      (swap2 : Fin 2 → Fin 2)^[5] x :=
  distinguishedPower_correct (swap2 : Fin 2 → Fin 2) (fun y => y = 0) 2 5
    (fun h => (swap2 : Fin 2 → Fin 2)^[3] h) (fun l => 3 % l)
    (fun y _ => by revert y; decide)
    (fun _ _ => rfl) (fun _ _ _ => rfl) x

example (f : Fin 4 → Fin 4) (H : Fin 4 → Prop) [DecidablePred H] (K T : ℕ)
    (z : Fin 4 → Fin 4) (R : ℕ → ℕ)
    (hhit : ∀ y : Fin 4, (∀ i ≤ K, ∀ j ≤ K, f^[i] y = f^[j] y → i = j) →
      ∃ i ≤ K, H (f^[i] y))
    (hz : ∀ h, H h → z h = f^[T - K] h)
    (hR : ∀ l, 1 ≤ l → l ≤ K → R l = (T - K) % l)
    (x : Fin 4) :
    distinguishedPower f H K T z R x = f^[T] x :=
  distinguishedPower_correct f H K T z R hhit hz hR x

/-! ### Axioms -/

/--
info: 'Cslib.FunctionalGraph.shifted_payload' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms shifted_payload

/--
info: 'Cslib.FunctionalGraph.correction_run' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms correction_run

/--
info: 'Cslib.FunctionalGraph.periodWalk_spec' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms periodWalk_spec

/--
info: 'Cslib.FunctionalGraph.walk_run' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms walk_run

end CslibFrontierTests.FunctionalGraphSpectrum
