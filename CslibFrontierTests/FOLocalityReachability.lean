/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Locality.Reachability
public import CslibFrontier.Logics.FirstOrder.Operator.TransitiveClosure.Expressiveness
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.SuccPred.Nat
import Mathlib.Tactic.NormNum

/-! # Transitive closure and reachability by Gaifman locality: checked instances

* **Quantifier rank `1`.** No formula of quantifier rank at most `1` defines `≤` (the
  reflexive–transitive closure of `⋖`) on the successor relation on `19` points, and none defines
  reachability in two disjoint paths on `11` vertices.
* **Small chains are not ruled out.** On `Fin 2` the rank-`0` formula `x = y ∨ E(x, y)` does define
  `≤`, and it fails on `Fin 3`; the bound `N ≤ 2 · 3 ^ (q + 1)` allows this.
* **Distance formulas.** In the path on `5` vertices the ends are at distance `4`, so
  `distLE 2` holds of them and `distLE 1` does not.
* **The radius hypothesis is satisfiable.** Libkin's radius `(3 ^ (n + 1) - 1) / 2` satisfies the
  hypothesis of `two_pow_le_of_gaifman_radius`, by Gaifman locality, so the lower bound
  `2 ^ k ≤ (3 ^ (k + 2) - 1) / 2` follows and the hypothesis is not vacuous. The rank-`3` formula
  `distLE 3` separates two pairs with isomorphic radius-`3` neighborhoods.
* **FO(TC).** The FO(TC) formula of `exists_formula_reflTransGen` defines `≤` on every successor
  relation `(Fin N, ⋖)`, which no first-order formula does. -/

public section

namespace Cslib.Tests.FOLocalityReachability

open FirstOrder Language Structure SimpleGraph
open Cslib.Logic.FO Cslib.Logic.FO.Locality

/-! ### Quantifier rank `1` -/

/-- No formula of quantifier rank at most `1` defines `≤` on the successor relation on `19`
points. -/
example {φ : Language.graph.Formula (Fin 2)} (hφ : quantifierRank φ ≤ 1) :
    ¬ ∀ a b : Fin 19, (letI := relStructure (M := Fin 19) (· ⋖ ·); φ.Realize ![a, b]) ↔
      Relation.ReflTransGen (· ⋖ ·) a b := by
  intro h
  have := card_le_of_realize_iff_reflTransGen h
  have h3 : 3 ^ (quantifierRank φ + 1) ≤ 9 :=
    (Nat.pow_le_pow_right (by norm_num) (by omega) : _ ≤ 3 ^ 2).trans_eq (by norm_num)
  omega

/-- No formula of quantifier rank at most `1` defines `<` on the successor relation on `19`
points. -/
example {φ : Language.graph.Formula (Fin 2)} (hφ : quantifierRank φ ≤ 1) :
    ¬ ∀ a b : Fin 19, (letI := relStructure (M := Fin 19) (· ⋖ ·); φ.Realize ![a, b]) ↔
      Relation.TransGen (· ⋖ ·) a b := by
  intro h
  have := card_le_of_realize_iff_transGen h
  have h3 : 3 ^ (quantifierRank φ + 1) ≤ 9 :=
    (Nat.pow_le_pow_right (by norm_num) (by omega) : _ ≤ 3 ^ 2).trans_eq (by norm_num)
  omega

/-- No formula of quantifier rank at most `1` defines reachability in `P_11 ⊕ P_11`. -/
example {φ : Language.graph.Formula (Fin 2)} (hφ : quantifierRank φ ≤ 1) :
    ¬ ∀ x y : Fin 11 ⊕ Fin 11, (letI := (pathGraph 11 ⊕g pathGraph 11).structure;
      φ.Realize ![x, y]) ↔ (pathGraph 11 ⊕g pathGraph 11).Reachable x y := by
  intro h
  have := card_le_of_realize_iff_reachable_pathGraph h
  have h3 : 3 ^ (quantifierRank φ + 1) ≤ 9 :=
    (Nat.pow_le_pow_right (by norm_num) (by omega) : _ ≤ 3 ^ 2).trans_eq (by norm_num)
  omega

/-! ### Small chains -/

/-- On the successor relation, `distLE 0` says `x = y ∨ x ⋖ y`. -/
theorem realize_distLE_zero_covBy {N : ℕ} (a b : Fin N) :
    (letI := relStructure (M := Fin N) (· ⋖ ·); (distLE 0).Realize ![a, b]) ↔ a = b ∨ a ⋖ b := by
  let := relStructure (M := Fin N) (· ⋖ ·)
  rw [realize_distLE_zero, relMap_relStructure]

/-- On `Fin 2` the rank-`0` formula `x = y ∨ E(x, y)` defines `≤`. -/
example : ∀ a b : Fin 2, (letI := relStructure (M := Fin 2) (· ⋖ ·); (distLE 0).Realize ![a, b]) ↔
    Relation.ReflTransGen (· ⋖ ·) a b := by
  intro a b
  rw [realize_distLE_zero_covBy, ← le_iff_reflTransGen_covBy]
  fin_cases a <;> fin_cases b <;> simp [Fin.covBy_iff]

/-- On `Fin 3` it does not: `0 ≤ 2`, but `0 ≠ 2` and `0` is not covered by `2`. -/
example : ¬ ∀ a b : Fin 3, (letI := relStructure (M := Fin 3) (· ⋖ ·);
    (distLE 0).Realize ![a, b]) ↔ Relation.ReflTransGen (· ⋖ ·) a b := by
  intro h
  have := (h 0 2).2 (le_iff_reflTransGen_covBy.1 (by decide))
  rw [realize_distLE_zero_covBy] at this
  simp [Fin.covBy_iff] at this

/-! ### Distance formulas -/

/-- The ends of `P_5` satisfy `distLE 2`: their distance `4` is at most `2 ^ 2`. -/
example : letI := (pathGraph 5).structure; (distLE 2).Realize ![(0 : Fin 5), 4] := by
  rw [realize_distLE, edist_pathGraph]
  norm_num

/-- The ends of `P_5` do not satisfy `distLE 1`: their distance `4` exceeds `2 ^ 1`. -/
example : ¬ (letI := (pathGraph 5).structure; (distLE 1).Realize ![(0 : Fin 5), 4]) := by
  rw [realize_distLE, edist_pathGraph]
  norm_num

/-! ### The exponential radius -/

/-- The rank-`3` formula `distLE 3` separates two pairs with isomorphic radius-`3`
neighborhoods. -/
example : ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V) (a b : Fin 2 → V),
    (letI := G.structure; NbhdIso Language.graph 3 a b) ∧
    (letI := G.structure; (distLE 3).Realize a) ∧ ¬ (letI := G.structure; (distLE 3).Realize b) :=
  exists_nbhdIso_realize_distLE 2

/-- Libkin's Gaifman radius satisfies the hypothesis of `two_pow_le_of_gaifman_radius`, so the
hypothesis is not vacuous, and the lower bound follows. -/
example (k : ℕ) : 2 ^ k ≤ (3 ^ (k + 1 + 1) - 1) / 2 :=
  two_pow_le_of_gaifman_radius (ρ := fun n => (3 ^ (n + 1) - 1) / 2)
    (fun _ _ _ G _ _ _ hφ hab => by
      let := G.structure
      exact hab.formula_realize_iff hφ) k

/-! ### FO(TC) -/

/-- The FO(TC) closure formula defines `≤` on every successor relation `(Fin N, ⋖)`. -/
example : ∃ φ : Operator.Formula Language.graph TC.shape [] (Fin 2),
    φ.wellFormed TC.policy = true ∧ ∀ (N : ℕ) (a b : Fin N),
      (letI := relStructure (M := Fin N) (· ⋖ ·);
        φ.Realize TC.interpretation Operator.RelEnv.empty ![a, b]) ↔ a ≤ b := by
  obtain ⟨φ, hwf, hφ⟩ := TC.exists_formula_reflTransGen.{0}
  refine ⟨φ, hwf, fun N a b => ?_⟩
  let := relStructure (M := Fin N) (· ⋖ ·)
  have hR : (fun x y : Fin N => RelMap adj ![x, y]) = (· ⋖ ·) :=
    funext₂ fun x y => propext (relMap_relStructure _ x y)
  rw [hφ, hR, le_iff_reflTransGen_covBy]

end Cslib.Tests.FOLocalityReachability
