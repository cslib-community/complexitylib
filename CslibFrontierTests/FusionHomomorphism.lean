/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Fusion.Homomorphism
import CslibFrontier.Computability.Circuit.Fusion.Counting
import CslibFrontier.Computability.Circuit.SumOfTerms.Basic

/-!
# Homomorphism transport clients

Source complexity can strictly decrease under a noninjective homomorphism. Cover complexity
can strictly decrease even under an injective homomorphism, since image atoms need not lift.
Further clients retain nonuniform costs, repeated atoms, unused gates and multiple outputs.
-/

namespace ComplexityTests.FusionHomomorphism

open Cslib.Circuits SumOfTerms Fusion

private abbrev natAddition : Interpretation (signature Empty) ℕ := interpretation Empty.elim

private def scale (k : ℕ) : Homomorphism natAddition natAddition where
  map n := k * n
  homomorphic op args := by
    cases op with
    | add => exact Nat.mul_add k (args 0) (args 1)
    | term t => exact t.elim

private def missingTarget (b : Bool) : Fin 1 → ℕ := fun _ => if b then 1 else 0
private def zeroSources (_ : Bool) : Fin 1 → ℕ := fun _ => 0

private theorem missing_complexity :
    ecomplexityFrom natAddition addCost missingTarget zeroSources = ⊤ :=
  ecomplexityFrom_eq_top_of_fiber_collision (x := false) (y := true) rfl (by decide)

-- Mapping every value to zero changes an impossible problem to a zero-gate projection.
private theorem collapsed_complexity :
    ecomplexityFrom natAddition addCost (fun x => (scale 0).map ∘ missingTarget x)
      (fun x => (scale 0).map ∘ zeroSources x) = 0 := by
  simp only [scale, Function.comp_def, Nat.zero_mul]
  exact ecomplexityFrom_self (I := natAddition) (fun _ : Bool => fun _ : Fin 1 => 0)

example : ecomplexityFrom natAddition addCost (fun x => (scale 0).map ∘ missingTarget x)
    (fun x => (scale 0).map ∘ zeroSources x) <
      ecomplexityFrom natAddition addCost missingTarget zeroSources := by
  rw [collapsed_complexity, missing_complexity]
  exact ENat.natCast_lt_top 0

-- An injective map preserves the same infinite complexity without requiring surjectivity.
example : ecomplexityFrom natAddition addCost (fun x => (scale 2).map ∘ missingTarget x)
    (fun x => (scale 2).map ∘ zeroSources x) = ⊤ := by
  rw [ecomplexityFrom_map_eq (scale 2) (by intro a b h; change 2 * a = 2 * b at h; lia)]
  exact missing_complexity

private def isOne (_ : Unit) (n : ℕ) : Prop := n = 1

private def oneCover : Cover natAddition isOne where
  size := 1
  atoms _ := ⟨.add, ![1, 1]⟩
  isCover _ h := by
    exact (by decide : (2 : ℕ) ≠ 1) (h 0 (by
      change ∀ i : Fin 2, (![1, 1] : Fin 2 → ℕ) i = 1
      decide))

private theorem image_cover_complexity : coverComplexity natAddition isOne addCost ≤ 1 :=
  coverComplexity_le oneCover addCost

private theorem one_le_cover_complexity : (1 : ℕ∞) ≤ coverComplexity natAddition isOne addCost := by
  refine le_coverComplexity_iff.mpr fun c => ?_
  have h := c.card_le_mul_cost {()} addCost 1 (fun i => ?_)
  · exact_mod_cast (by simpa using h : 1 ≤ c.cost addCost)
  · rcases c.atoms i with ⟨op, args⟩
    cases op with
    | add => exact Finset.card_le_one.mpr fun _ _ _ _ => Subsingleton.elim _ _
    | term t => exact t.elim

example : coverComplexity natAddition isOne addCost = 1 :=
  le_antisymm image_cover_complexity one_le_cover_complexity

private def firstCoordinate : Homomorphism (interpretation (Empty.elim : Empty → ℕ × ℕ))
    natAddition where
  map := Prod.fst
  homomorphic op _ := by cases op with
    | add => rfl
    | term t => exact t.elim

-- A one-dimensional Fusion bound transfers to circuits computing pairs, through a noninjective map.
private theorem pair_lower_bound : (1 : ℕ∞) ≤
    ecomplexityFrom (interpretation (Empty.elim : Empty → ℕ × ℕ)) addCost
      (fun _ : Unit => ![(2, 20), (1, 10), (2, 20)]) (fun _ : Unit => ![(1, 10)]) :=
  one_le_cover_complexity.trans ((coverComplexity_le_comap firstCoordinate isOne addCost).trans
    (coverComplexity_le_ecomplexityFrom _ _ _ _ _ ()
      (by change ∀ _ : Unit, ∀ i : Fin 1, ((![(1, 10)] : Fin 1 → ℕ × ℕ) i).1 = 1; decide)
      (fun _ => ⟨0, by change ¬(2 : ℕ) = 1; decide⟩)))

private def pairDouble : Circuit (signature Empty) 1 3 :=
  ⟨(Program.empty : Program (signature Empty) 1 0).gate ⟨.add, ![.input 0, .input 0]⟩,
    ![.gate 0, .input 0, .gate 0]⟩

-- The bound is attained, retaining a supplied input and a duplicated designated output.
example : ecomplexityFrom (interpretation (Empty.elim : Empty → ℕ × ℕ)) addCost
    (fun _ : Unit => ![(2, 20), (1, 10), (2, 20)]) (fun _ : Unit => ![(1, 10)]) = 1 :=
  le_antisymm (ecomplexityFrom_le_of_computesFrom pairDouble (fun _ => by decide)) pair_lower_bound

-- No doubled value equals one, so the pullback invariant is false on every argument.
-- Every binary atom preserves it, while the target has the one-atom cover above.
private theorem pullback_cover_complexity :
    coverComplexity natAddition (fun t => isOne t ∘ (scale 2).map) addCost = ⊤ := by
  apply top_le_iff.mp
  refine le_coverComplexity_iff.mpr fun c => (c.isCover () fun i => ?_).elim
  rcases c.atoms i with ⟨op, args⟩
  cases op with
  | add =>
    intro hargs
    have h := hargs 0
    change 2 * args 0 = 1 at h
    lia
  | term t => exact t.elim

example : coverComplexity natAddition isOne addCost <
    coverComplexity natAddition (fun t => isOne t ∘ (scale 2).map) addCost := by
  rw [pullback_cover_complexity]
  exact image_cover_complexity.trans_lt (ENat.natCast_lt_top 1)

private def integerImage : Homomorphism (interpretation (id : ℕ → ℕ))
    (interpretation (fun n : ℕ => (n : ℤ))) where
  map n := n
  homomorphic op args := by
    cases op with
    | add => exact Int.natCast_add (args 0) (args 1)
    | term _ => rfl

private def shared : Circuit (signature ℕ) 0 3 :=
  ⟨(((Program.empty : Program (signature ℕ) 0 0).gate
    ⟨.term 2, Fin.elim0⟩ |>.gate ⟨.term 3, Fin.elim0⟩).gate
    ⟨.add, ![.gate 0, .gate 1]⟩).gate ⟨.term 2, Fin.elim0⟩,
    ![.gate 2, .gate 0, .gate 2]⟩

private def belowFive (_ : Unit) (z : ℤ) : Prop := z < 5

private def sharedCover : Cover (interpretation id) (fun t => belowFive t ∘ integerImage.map) :=
  Cover.ofProgram shared.program (interpretation id) _ Fin.elim0 (fun _ i => i.elim0)
    (fun _ => ⟨.gate (2 : Fin 4), by change ¬(5 : ℤ) < 5; decide⟩)

private def mixedWeight : Op ℕ → ℕ
  | .add => 7
  | .term n => n + 1

-- The repeated term remains charged despite being unused; two outputs share the addition.
example : (sharedCover.map integerImage).cost mixedWeight = 17 := by
  rw [Cover.cost_map, sharedCover, Cover.cost_ofProgram]
  decide

example : (sharedCover.map integerImage).cost termCost = 3 ∧
    (sharedCover.map integerImage).cost addCost = 1 := by
  rw [Cover.cost_map, Cover.cost_map, sharedCover, Cover.cost_ofProgram, Cover.cost_ofProgram]
  decide

example : (sharedCover.map integerImage).size = 4 ∧
    (sharedCover.map integerImage).atoms (0 : Fin 4) =
      (sharedCover.map integerImage).atoms (3 : Fin 4) := by
  constructor
  · rfl
  · apply congrArg (fun args => (⟨.term 2, args⟩ : Atom (signature ℕ) ℤ))
    exact Subsingleton.elim _ _

example (k : Fin 4) : (sharedCover.map integerImage).atoms k =
    programAtoms shared.program (interpretation (fun n : ℕ => (n : ℤ))) Fin.elim0 k := by
  change (programAtoms shared.program (interpretation id) Fin.elim0 k).map integerImage.map = _
  simpa only [show integerImage.map ∘ (Fin.elim0 : Fin 0 → ℕ) = Fin.elim0 from
    Subsingleton.elim _ _] using programAtoms_map shared.program integerImage Fin.elim0 k

/-- info: ([5, 2, 5], [[], [], [2, 3], []], 4, 17) -/
#guard_msgs in
#eval (List.ofFn (shared.eval (interpretation (fun n : ℕ => (n : ℤ))) Fin.elim0),
  List.ofFn (fun k => List.ofFn ((sharedCover.map integerImage).atoms k).arguments),
  (sharedCover.map integerImage).size, (sharedCover.map integerImage).cost mixedWeight)

-- The exported simplification rules handle ordinary functional spelling of repeated maps.
example (a : Atom (signature Empty) ℕ) : ((a.map (scale 2).map).map id).map (scale 3).map =
    a.map ((scale 3).comp (scale 2)).map := by simp

-- A downstream lower bound composes directly with pullback and source-complexity transport.
universe u v w z t
example {σ : Signature.{u}} {U : Type v} {V : Type w} {W : Type z} {X : Type t}
    {I : Interpretation σ U} {J : Interpretation σ V} (h : Homomorphism I J)
    (P : W → V → Prop) (weight : σ.Op → ℕ) (sources : X → Fin 2 → U)
    (target : X → Fin 3 → U) (x : X) (k : ℕ∞)
    (hbound : k ≤ coverComplexity J P weight)
    (hin : ∀ t i, P t (h.map (sources x i)))
    (hout : ∀ t, ∃ o, ¬ P t (h.map (target x o))) :
    k ≤ ecomplexityFrom I weight target sources :=
  hbound.trans ((coverComplexity_le_comap h P weight).trans
    (coverComplexity_le_ecomplexityFrom I (fun t => P t ∘ h.map) weight
      target sources x hin hout))

end ComplexityTests.FusionHomomorphism
