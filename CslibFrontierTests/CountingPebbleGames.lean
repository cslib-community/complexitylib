/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.FiniteVariable.CountingHintikka
public import CslibFrontierTests.FOPebbleGames
import CslibFrontier.Foundations.Data.Fintype.FiberEquiv

/-! # Counting logic and bijective pebble games: checked instances

* **Bijective games force equal cardinality.** With a round and a pebble left, Duplicator's
  bijection is a bijection `M ≃ N`. The counting logic sees the same thing: the rank-`1` sentence
  `hasCard m`, "exactly `m` elements", holds in a finite structure `M` exactly when
  `Nat.card M = m`, so the easy direction also forces `Nat.card M = Nat.card N`.
* **Counting adds power over a fixed number of variables.** In the empty language, Duplicator
  wins the infinite `1`-pebble game on `Fin 3` and `Fin 2`, so they agree on every one-variable
  first-order sentence, but the one-variable counting sentence `hasCard 3` separates them and
  Spoiler wins the one-round bijective `1`-pebble game. The hard direction turns this back into a
  separating counting Hintikka sentence.
* **`C₆` and two triangles agree on `C²`.** Duplicator wins the infinite bijective `2`-pebble game
  on the cycle `C₆` and two disjoint triangles `2C₃`: for any vertices `x` of `C₆` and `y` of
  `2C₃`, a bijection matches the vertices of `C₆` with those of `2C₃` so that equality with and
  adjacency to `x` correspond to equality with and adjacency to `y`, since both graphs are
  `2`-regular on six vertices. So the two graphs satisfy the same two-variable counting sentences,
  a positive instance of the bijective game that is not an isomorphism. By the Immerman–Lander
  theorem (`CslibFrontier.Logics.FirstOrder.FiniteVariable.ColorRefinement`), this matches the
  failure of color refinement to separate them. -/

@[expose] public section

namespace Cslib.Tests.CountingPebbleGames

open FirstOrder Language Structure
open Cslib.Logic.FO
open Cslib.Tests.FOPebbleGames

/-! ### Bijective games force equal cardinality -/

variable {L : Language} {M N : Type*} [L.Structure M] [L.Structure N]

/-- With a round and a pebble left, a won bijective game forces the structures to have the same
cardinality. -/
theorem card_eq_of_bijPebbleWins {k n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : BijPebbleWins L (n + 1) S a b) (i : Fin k) : Nat.card M = Nat.card N :=
  Nat.card_congr (h.nonempty_equiv i).some

/-- Exactly `m` elements: a one-variable counting sentence of quantifier rank `1`. -/
def hasCard (L : Language) (m : ℕ) : FiniteVariable.CountingFormula L 1 :=
  .exactly m 0 ⊤

theorem realize_hasCard [Finite M] (m : ℕ) (a : Fin 1 → M) :
    (hasCard L m).Realize a ↔ Nat.card M = m := by
  rw [hasCard, FiniteVariable.CountingFormula.realize_exactly_iff_ncard]
  simp only [FiniteVariable.CountingFormula.realize_top, Set.ofPred_true, Set.ncard_univ]

theorem quantifierRank_hasCard (m : ℕ) : (hasCard L m).quantifierRank = 1 := by
  rw [hasCard, FiniteVariable.CountingFormula.quantifierRank_exactly,
    FiniteVariable.CountingFormula.quantifierRank_top]

theorem freeVars_hasCard (m : ℕ) : (hasCard L m).freeVars = ∅ := by
  rw [hasCard, FiniteVariable.CountingFormula.freeVars_exactly,
    FiniteVariable.CountingFormula.freeVars_top, Finset.erase_empty]

/-- The same conclusion through the counting logic: a won one-round bijective `1`-pebble game
makes the two finite structures agree on `hasCard (Nat.card M)`. -/
theorem card_eq_of_bijPebbleWins_of_realize [Finite M] [Finite N] {S : Set (Fin 1)}
    {a : Fin 1 → M} {b : Fin 1 → N} (h : BijPebbleWins L 1 S a b) : Nat.card M = Nat.card N := by
  have := (h.realize_iff (quantifierRank_hasCard (Nat.card M)).le
    (by simp only [freeVars_hasCard, Finset.coe_empty, Set.empty_subset])).1
    ((realize_hasCard _ a).2 rfl)
  exact ((realize_hasCard _ b).1 this).symm

/-! ### Counting adds power over a fixed number of variables -/

instance (m : ℕ) : Language.empty.Structure (Fin m) := Language.emptyStructure

instance (l : ℕ) : IsEmpty (Language.empty.Relations l) :=
  inferInstanceAs (IsEmpty Empty)

instance : Finite (Σ l, Language.empty.Relations l) :=
  inferInstance

/-- With one pebble and no relation symbols, every position is a partial isomorphism. -/
theorem partialIsoOn_empty_one {V W : Type*} [Language.empty.Structure V]
    [Language.empty.Structure W] (S : Set (Fin 1)) (a : Fin 1 → V) (b : Fin 1 → W) :
    PartialIsoOn Language.empty S a b := by
  refine ⟨fun i _ j _ => ?_, fun R _ _ => isEmptyElim R⟩
  rw [Subsingleton.elim i j]
  exact iff_of_true rfl rfl

/-- **Duplicator wins the infinite `1`-pebble game on `Fin 3` and `Fin 2`.** -/
theorem pebbleWinsForever_fin_three_two (S : Set (Fin 1)) (a : Fin 1 → Fin 3) (b : Fin 1 → Fin 2) :
    PebbleWinsForever Language.empty S a b :=
  IsPebbleBackAndForth.pebbleWinsForever (I := fun _ _ _ => True)
    ⟨fun {S a b} _ => partialIsoOn_empty_one S a b, fun _ _ _ => ⟨0, trivial⟩,
      fun _ _ _ => ⟨0, trivial⟩⟩ trivial

/-- Hence `Fin 3` and `Fin 2` satisfy the same one-variable first-order sentences. -/
theorem realize_iff_fin_three_two {φ : FiniteVariable.Formula Language.empty 1}
    (hφ : φ.freeVars = ∅) (a : Fin 1 → Fin 3) (b : Fin 1 → Fin 2) :
    φ.Realize a ↔ φ.Realize b :=
  (pebbleWinsForever_fin_three_two ∅ a b).realize_iff (by
    simp only [hφ, Finset.coe_empty, subset_refl])

/-- The one-variable counting sentence `hasCard 3` separates them. -/
theorem realize_hasCard_fin_three_two (a : Fin 1 → Fin 3) (b : Fin 1 → Fin 2) :
    (hasCard Language.empty 3).Realize a ∧ ¬ (hasCard Language.empty 3).Realize b := by
  simp only [realize_hasCard, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

/-- **Spoiler wins the one-round bijective `1`-pebble game on `Fin 3` and `Fin 2`.** -/
theorem not_bijPebbleWins_fin_three_two (S : Set (Fin 1)) (a : Fin 1 → Fin 3)
    (b : Fin 1 → Fin 2) : ¬ BijPebbleWins Language.empty 1 S a b := fun h => by
  have := card_eq_of_bijPebbleWins h 0
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

/-- The hard direction in action: the counting Hintikka formula of the type of `a`, a one-variable
counting sentence of quantifier rank at most `1`, holds in `Fin 3` and fails in `Fin 2`. -/
example (a : Fin 1 → Fin 3) (b : Fin 1 → Fin 2) :
    ∃ φ : FiniteVariable.CountingFormula Language.empty 1, φ.quantifierRank ≤ 1 ∧
      ↑φ.freeVars ⊆ (∅ : Set (Fin 1)) ∧ φ.Realize a ∧ ¬ φ.Realize b := by
  refine ⟨countingHintikka ∅ (countingType (L := Language.empty) 1 ∅ a),
    quantifierRank_countingHintikka_le _ _, freeVars_countingHintikka_subset _ _, ?_, ?_⟩
  · rw [realize_countingHintikka]
  · rw [realize_countingHintikka, eq_comm, countingType_eq_iff]
    exact not_bijPebbleWins_fin_three_two ∅ a b

/-- The embedding of `FO^k` into `C^k` in action: the first-order sentence "some element exists"
becomes a counting sentence with the same truth value, rank and free variables. -/
example (a : Fin 1 → Fin 3) :
    ((FiniteVariable.Formula.ex 0 ⊤ : FiniteVariable.Formula Language.empty 1).toCounting).Realize
      a := by
  rw [FiniteVariable.Formula.realize_toCounting, FiniteVariable.Formula.realize_ex]
  exact ⟨0, (FiniteVariable.Formula.realize_top _).2 trivial⟩

/-! ### `C₆` and two triangles agree on `C²` -/

/-- For any vertices `x` of `C₆` and `y` of `2C₃`, a bijection carries equality with and adjacency
to `x` to equality with and adjacency to `y`: each graph has one vertex equal to the given one,
two adjacent to it and three others. -/
theorem exists_equiv_fin_twoTriangles : ∀ (x : Fin 6) (y : Bool × Fin 3),
    Finset.univ.val.map
        (fun c : Fin 6 => (decide (c = x), decide ((SimpleGraph.cycleGraph 6).Adj c x))) =
      Finset.univ.val.map
        (fun d : Bool × Fin 3 => (decide (d = y), decide (twoTriangles.Adj d y))) := by
  decide

/-- **Duplicator wins the infinite bijective `2`-pebble game on `C₆` and `2C₃`**, from any position
with no pebbles placed: being a partial isomorphism on the placed pebbles is a back-and-forth
invariant of the bijective game. -/
theorem bijPebbleWinsForever_fin_twoTriangles (a : Fin 2 → Fin 6) (b : Fin 2 → Bool × Fin 3) :
    BijPebbleWinsForever Language.graph ∅ a b := by
  refine IsBijPebbleBackAndForth.bijPebbleWinsForever
    (I := fun S a b => PartialIsoOn Language.graph S a b)
    ⟨id, fun {S a b} h i => ?_⟩ (partialIsoOn_empty a b)
  obtain ⟨f, hf⟩ := Equiv.exists_apply_eq_iff_map_univ_eq.2
    (exists_equiv_fin_twoTriangles (a (i + 1)) (b (i + 1)))
  refine ⟨f, fun c => partialIsoOn_update_graph irrefl_fin irrefl_twoTriangles symm_fin
    symm_twoTriangles h i c (f c) ?_ ?_⟩
  · simpa only [Prod.mk.injEq, decide_eq_decide] using (congrArg Prod.fst (hf c)).symm
  · have := (congrArg Prod.snd (hf c)).symm
    rw [decide_eq_decide] at this
    exact relMap_adj_fin.trans (this.trans relMap_adj_twoTriangles.symm)

/-- Hence `C₆` and `2C₃` satisfy the same two-variable counting sentences. -/
theorem realize_iff_fin_twoTriangles {φ : FiniteVariable.CountingFormula Language.graph 2}
    (hφ : φ.freeVars = ∅) (a : Fin 2 → Fin 6) (b : Fin 2 → Bool × Fin 3) :
    φ.Realize a ↔ φ.Realize b :=
  (bijPebbleWinsForever_fin_twoTriangles a b).realize_iff (by
    simp only [hφ, Finset.coe_empty, subset_refl])

end Cslib.Tests.CountingPebbleGames
