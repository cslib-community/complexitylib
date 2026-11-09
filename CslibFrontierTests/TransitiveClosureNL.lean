/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.TransitiveClosure

/-! # FO(TC) ⊆ NL clients -/

@[expose] public section

namespace Cslib.Tests.TransitiveClosureNL

open FirstOrder Language Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered Cslib.Complexity

/-- The headline applies to every query defined by an FO(TC) sentence. -/
example {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Ordered.Query L}
    (hK : TCDefinable K) : K.encodedLanguage v ∈ NL encStructure :=
  hK.encodedLanguage_mem_NL v

/-- In particular to every query defined by a sentence with positive closures. -/
example {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Ordered.Query L}
    (hK : PosTCDefinable K) : K.encodedLanguage v ∈ NL encStructure :=
  hK.encodedLanguage_mem_NL v

/-- First-order definable queries are covered too. -/
example {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Ordered.Query L}
    (hK : Definable K) : K.encodedLanguage v ∈ NL encStructure :=
  hK.posTCDefinable.encodedLanguage_mem_NL v

/-! ### Reachability from `0` to `max` in a directed graph -/

/-- One binary edge relation. -/
inductive Rel : ℕ → Type
  | edge : Rel 2

/-- The language of directed graphs. -/
abbrev G : Language where
  Functions _ := Empty
  Relations := Rel

instance : G.IsRelational := fun _ => inferInstance

/-- The vocabulary listing the edge relation. -/
def vocabulary : Vocabulary G where
  count := 1
  symbol :=
    { toFun := fun _ => ⟨2, Rel.edge⟩
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := by rintro ⟨_, r⟩; cases r; rfl }

/-- The edge body, with the two endpoints as the bound variables of the closure. -/
def edgeBody : Operator.Formula (language G) TC.shape [] (Empty ⊕ Fin (2 * 1)) :=
  .ofFO (Relations.formula₂ ((LHom.sumInl : G →ᴸ language G).onRelation Rel.edge)
    (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))

/-- `max` is reachable from `0` along edges. -/
def reach : Operator.Formula (language G) TC.shape [] Empty :=
  TC.tc edgeBody (TC.pair ![zero G] ![max G])

/-- The reachability query, stated semantically on vertices. -/
def Reach : Ordered.Query G :=
  {M | Relation.ReflTransGen (fun x y : Fin M.size => Structure.RelMap (L := G) Rel.edge ![x, y])
    ((zero G).realize (Empty.elim : Empty → Fin M.size))
    ((max G).realize (Empty.elim : Empty → Fin M.size))}

theorem positive_reach : TC.Positive reach true := ⟨rfl, trivial⟩

/-- The sentence `reach` defines the reachability query. -/
theorem realize_reach (M : Ordered.Structure G) :
    M ∈ Reach ↔ reach.Realize (M := M) TC.interpretation Operator.RelEnv.empty Empty.elim := by
  have hedge : ∀ us vs : Fin 1 → Fin M.size,
      edgeBody.Realize TC.interpretation Operator.RelEnv.empty
          (Sum.elim Empty.elim (TC.pair us vs)) ↔
        Structure.RelMap (L := G) Rel.edge ![us 0, vs 0] := by
    intro us vs
    simp only [edgeBody, Operator.Formula.realize_ofFO, Formula.realize_rel₂,
      LHom.map_onRelation]
    rfl
  rw [reach, TC.realize_tc_pair]
  simp only [Reach, Set.mem_ofPred_eq, Matrix.cons_val_fin_one]
  constructor
  · intro h
    exact Relation.ReflTransGen.lift (fun x : Fin M.size => fun _ : Fin 1 => x)
      (fun a b hab => (hedge _ _).mpr hab) _ _ h
  · intro h
    exact Relation.ReflTransGen.lift (fun us : Fin 1 → Fin M.size => us 0)
      (fun us vs huv => (hedge us vs).mp huv) _ _ h

/-- **Directed reachability is in native `NL`**, at the source-only encoding of graphs. -/
example : Reach.encodedLanguage vocabulary ∈ NL encStructure :=
  PosTCDefinable.encodedLanguage_mem_NL ⟨reach, positive_reach, realize_reach⟩ vocabulary

/-! ### Polarity -/

/-- A negated closure is not positive. -/
example : ¬ TC.Positive reach.neg true := fun h => Bool.false_ne_true h.1

/-- A doubly negated closure is positive. -/
example : TC.Positive reach.neg.neg true := positive_reach

/-- The closure has width one. -/
example : TC.width reach = 1 := rfl

/-! ### Non-reachability: a negated closure -/

/-- `max` is not reachable from `0`. -/
def nonReach : Operator.Formula (language G) TC.shape [] Empty := reach.neg

/-- The non-reachability query. -/
def NonReach : Ordered.Query G := Reachᶜ

/-- The sentence `nonReach` defines the non-reachability query. -/
theorem realize_nonReach (M : Ordered.Structure G) :
    M ∈ NonReach ↔
      nonReach.Realize (M := M) TC.interpretation Operator.RelEnv.empty Empty.elim := by
  rw [nonReach, Operator.Formula.realize_neg, ← realize_reach]
  rfl

/-- `nonReach` lies outside the positive fragment. -/
example : ¬ TC.Positive nonReach true := fun h => Bool.false_ne_true h.1

/-- **Directed non-reachability is in native `NL`**, through the inductive-counting block for
negated closures. -/
example : NonReach.encodedLanguage vocabulary ∈ NL encStructure :=
  TCDefinable.encodedLanguage_mem_NL ⟨nonReach, realize_nonReach⟩ vocabulary

end Cslib.Tests.TransitiveClosureNL
