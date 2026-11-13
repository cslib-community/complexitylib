/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Forcing
public import CslibFrontier.Computability.Communication.OneOut
import Mathlib.Tactic

/-!
# Projected leaf rectangles for distinct-instance choice

The deterministic bridge in [ChukhinKulikovMihajlinSmal2026], proof of Lemma 5.2,
printed pp. 10–11 (PDF pp. 11–12). The original protocol takes injective tuples;
the constructed protocol takes single inputs. Projections use the coordinate actually
announced at each original leaf, and keep leaf occurrences distinct even when their
answers coincide. A fixed coordinate and a background partition determine forcing sets
on which the single-input protocol solves the original relation without extra bits.
The existence of a coordinate/background with the desired probability advantage is
not assumed by the construction and is not established by this module.

## Main results

* `projections_valid`: the source's equation (1), on the actual projected leaf rectangles.
* `rectangleProtocol_solves`: compatible forcing choices solve the original relation.
* `depth_rectangleProtocol`: the constructed protocol has exactly the original tree depth.
-/

public section
namespace Cslib.Communication.OneOut
open Protocol
variable {X Y Z : Type*} {k : ℕ}

/-- Alice's coordinate projection of an original leaf rectangle. -/
@[expose] def aliceProjection (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z))
    (w : Fin p.leafCount) : Set X :=
  {a | ∃ x ∈ p.leafAlice w, x (p.leafOutput w).index = a}

/-- Bob's coordinate projection of an original leaf rectangle. -/
@[expose] def bobProjection (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z))
    (w : Fin p.leafCount) : Set Y :=
  {b | ∃ y ∈ p.leafBob w, y (p.leafOutput w).index = b}

/-- The answer at a leaf is valid on the product of its coordinate projections. -/
theorem projections_valid {R : X → Y → Z → Prop}
    {p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z)}
    (hp : p.Solves (Relation R) Set.univ Set.univ) (w : Fin p.leafCount)
    {a : X} {b : Y} (ha : a ∈ aliceProjection p w) (hb : b ∈ bobProjection p w) :
    R a b (p.leafOutput w).value := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact hp.solves_leafOutput w x ⟨trivial, hx⟩ y ⟨trivial, hy⟩

/-- Every legal tuple lets Alice force membership of its announced entry in the
corresponding projection, by following her original messages. This is the final hybrid endpoint. -/
theorem canForce_aliceProjection
    (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z)) (x : Fin k ↪ X) :
    p.labelLeaves.CanForce true
      (fun w => x (p.leafOutput w).index ∈ aliceProjection p w) :=
  (p.labelLeaves.canForce_mono true (fun _ hw => ⟨x, hw, rfl⟩)) (p.canForce_leafAlice x)

/-- Every legal tuple lets Bob force his announced entry's projection. Determinacy then
excludes Alice forcing its complement, which is the initial hybrid endpoint. -/
theorem canForce_bobProjection
    (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z)) (y : Fin k ↪ Y) :
    p.labelLeaves.CanForce false
      (fun w => y (p.leafOutput w).index ∈ bobProjection p w) :=
  (p.labelLeaves.canForce_mono false (fun _ hw => ⟨y, hw, rfl⟩)) (p.canForce_leafBob y)

/-- At the pivotal coordinate, Alice forces membership in her projection.
At every other leaf, she forces membership in the background side. -/
@[expose] def aliceGoal (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z))
    (i : Fin k) (background : Set (Fin p.leafCount)) (a : X) (w : Fin p.leafCount) : Prop :=
  if (p.leafOutput w).index = i then a ∈ aliceProjection p w else w ∈ background

/-- Bob forces his projection at the pivotal coordinate and the complementary background
at all other leaves. -/
@[expose] def bobGoal (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z))
    (i : Fin k) (background : Set (Fin p.leafCount)) (b : Y) (w : Fin p.leafCount) : Prop :=
  if (p.leafOutput w).index = i then b ∈ bobProjection p w else w ∉ background

/-- Alice's single inputs on which her pivotal goal can be forced. -/
@[expose] def aliceSide (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z))
    (i : Fin k) (background : Set (Fin p.leafCount)) : Set X :=
  {a | p.labelLeaves.CanForce true (aliceGoal p i background a)}

/-- Bob's single inputs on which his pivotal goal can be forced. -/
@[expose] def bobSide (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z))
    (i : Fin k) (background : Set (Fin p.leafCount)) : Set Y :=
  {b | p.labelLeaves.CanForce false (bobGoal p i background b)}

/-- Steering the original occurrence-labelled tree and then returning its original answer. -/
@[expose] noncomputable def rectangleProtocol
    (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z))
    (i : Fin k) (background : Set (Fin p.leafCount)) : Protocol X Y Z :=
  (p.labelLeaves.steer (aliceGoal p i background) (bobGoal p i background)).map
    (fun w => (p.leafOutput w).value)

/-- Both forcing goals select the pivotal coordinate; backgrounds cannot win simultaneously. -/
theorem goals_compatible (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z))
    (i : Fin k) (background : Set (Fin p.leafCount)) {a : X} {b : Y}
    {w : Fin p.leafCount} (ha : aliceGoal p i background a w)
    (hb : bobGoal p i background b w) :
    (p.leafOutput w).index = i ∧ a ∈ aliceProjection p w ∧ b ∈ bobProjection p w := by
  by_cases hi : (p.leafOutput w).index = i
  · exact ⟨hi, by simpa [aliceGoal, hi] using ha, by simpa [bobGoal, hi] using hb⟩
  · have hl : w ∈ background := by simpa [aliceGoal, hi] using ha
    have hr : w ∉ background := by simpa [bobGoal, hi] using hb
    exact (hr hl).elim

/-- The constructed single-input protocol solves the original relation on its forcing rectangle. -/
theorem rectangleProtocol_solves {R : X → Y → Z → Prop}
    {p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z)}
    (hp : p.Solves (Relation R) Set.univ Set.univ) (i : Fin k)
    (background : Set (Fin p.leafCount)) :
    (rectangleProtocol p i background).Solves R (aliceSide p i background)
      (bobSide p i background) := by
  intro a ha b hb
  obtain ⟨hl, hr⟩ := run_steer p.labelLeaves (aliceGoal p i background)
    (bobGoal p i background) a b ha hb
  have h := goals_compatible p i background hl hr
  simpa [rectangleProtocol] using projections_valid hp _ h.2.1 h.2.2

/-- Neither occurrence labelling, steering nor returning the answer adds communication. -/
@[simp] theorem depth_rectangleProtocol
    (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z))
    (i : Fin k) (background : Set (Fin p.leafCount)) :
    (rectangleProtocol p i background).depth = p.depth := by
  simp [rectangleProtocol]

/-- Alice forcing the complement of Bob's goal is exactly nonmembership in Bob's side.
This supplies the pre-pivot event in the source's probability difference. -/
theorem canForce_before_iff (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z))
    (i : Fin k) (background : Set (Fin p.leafCount)) (b : Y) :
    p.labelLeaves.CanForce true (fun w => ¬ bobGoal p i background b w) ↔
      b ∉ bobSide p i background :=
  p.labelLeaves.canForce_not_iff false (bobGoal p i background b)

end Cslib.Communication.OneOut
