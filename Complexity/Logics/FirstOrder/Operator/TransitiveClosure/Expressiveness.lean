/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Operator.TransitiveClosure
public import Mathlib.ModelTheory.Graph
import Complexity.Logics.FirstOrder.Locality.Reachability
import Complexity.Logics.FirstOrder.Operator.TransitiveClosure.Definability
import Complexity.Tactic.FOOperator
import Mathlib.CategoryTheory.ConcreteCategory.Bundled

/-!
# FO(TC) is strictly more expressive than first-order logic

One formula of FO(TC), the closure of the edge relation, defines the reflexive–transitive closure
of the edge relation in every structure of the language of graphs, read as directed graphs
(`exists_formula_reflTransGen`). It is the formula `[trcl_{x,y} E(x, y)](x₀, x₁)` of
[Libkin, Definition 10.20 (p. 199)][Libkin2004], except that the library's closure operator is
reflexive. No first-order formula defines this query on all finite structures
(`Cslib.Logic.FO.Locality.not_exists_formula_reflTransGen`, proved by Gaifman locality,
[Libkin, §4.1][Libkin2004]). So this FO(TC) formula is equivalent to no first-order formula on
finite structures (`exists_formula_not_fo_equivalent`). Every first-order formula is an FO(TC)
formula through `Operator.Formula.ofFO`, so FO(TC) is strictly more expressive than FO on finite
structures of the language of graphs.

This is a statement about expressive power over arbitrary, unordered finite structures. The
library's capture theorems for FO(TC) are over ordered structures.

## Main results

* `exists_formula_reflTransGen`: FO(TC) defines the reflexive–transitive closure of the edge
  relation.
* `exists_formula_not_fo_equivalent`: some FO(TC) formula is equivalent to no first-order
  formula on finite structures.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
-/

public section

universe u

open FirstOrder Language Structure Cslib.Logic.FO

namespace Cslib.Logic.FO.TC

/-- Closure of a relation on one-element tuples is closure of the relation on their entries. -/
private theorem reflTransGen_fin_one_iff {M : Type*} {R : M → M → Prop} {a b : M} :
    Relation.ReflTransGen (fun us vs : Fin 1 → M => R (us 0) (vs 0)) (fun _ => a) (fun _ => b) ↔
      Relation.ReflTransGen R a b :=
  ⟨fun h => h.lift (fun us : Fin 1 → M => us 0) fun _ _ h => h,
    fun h => h.lift (fun x : M => fun _ : Fin 1 => x) fun _ _ h => h⟩

/-- **FO(TC) defines transitive closure** ([Libkin, Definition 10.20][Libkin2004]): one
well-formed FO(TC) formula `φ(x₀, x₁)` of the language of graphs defines, in every structure, the
reflexive–transitive closure of the edge relation. -/
theorem exists_formula_reflTransGen :
    ∃ φ : Operator.Formula Language.graph shape [] (Fin 2), φ.wellFormed policy = true ∧
      ∀ (M : Type u) [Language.graph.Structure M] (a b : M),
        φ.Realize interpretation Operator.RelEnv.empty ![a, b] ↔
          Relation.ReflTransGen (fun x y : M => RelMap adj ![x, y]) a b := by
  have : Operator.Definable (L := Language.graph) policy
      (fun X : CategoryTheory.Bundled.{u} Language.graph.Structure => X)
      (fun _ => interpretation) (fun _ => Operator.RelEnv.empty)
      (fun X v => Relation.ReflTransGen
        (fun us vs : Fin 1 → X => RelMap adj ![us 0, vs 0])
        (fun j => ((fun _ => Term.var 0) j : Language.graph.Term (Fin 2)).realize v)
        (fun j => ((fun _ => Term.var 1) j : Language.graph.Term (Fin 2)).realize v)) := by
    fo_definable
  obtain ⟨φ, hwf, hφ⟩ := this
  refine ⟨φ, hwf, fun M _ a b => (hφ (CategoryTheory.Bundled.of M) ![a, b]).trans ?_⟩
  simp only [Term.realize_var]
  exact reflTransGen_fin_one_iff (R := fun x y : M => RelMap adj ![x, y])

/-- **FO(TC) is strictly more expressive than FO**: some well-formed FO(TC) formula `φ(x₀, x₁)`
of the language of graphs, the reflexive–transitive closure of the edge relation, is equivalent to
no first-order formula on finite structures. -/
theorem exists_formula_not_fo_equivalent :
    ∃ φ : Operator.Formula Language.graph shape [] (Fin 2), φ.wellFormed policy = true ∧
      ¬ ∃ ψ : Language.graph.Formula (Fin 2), ∀ (M : Type u) [Finite M]
        [Language.graph.Structure M] (v : Fin 2 → M),
        ψ.Realize v ↔ φ.Realize interpretation Operator.RelEnv.empty v := by
  obtain ⟨φ, hwf, hφ⟩ := exists_formula_reflTransGen.{u}
  refine ⟨φ, hwf, fun ⟨ψ, hψ⟩ => Locality.not_exists_formula_reflTransGen.{u}
    ⟨ψ, fun M _ _ a b => (hψ M ![a, b]).trans (hφ M a b)⟩⟩

end Cslib.Logic.FO.TC
