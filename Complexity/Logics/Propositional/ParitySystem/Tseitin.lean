/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ParitySystem
public import Complexity.Logics.Propositional.Tseitin

/-!
# Tseitin parity systems

The **Tseitin parity system** `ParitySystem.tseitin ends χ` of a multigraph `ends : E → Sym2 V`
with charges `χ` has a variable for each edge and, for each vertex `v`, the equation saying that
the parity of the edges at `v` other than self-loops is `χ v`. It is satisfied by the same
assignments as the Tseitin formula `CNF.tseitinFormula ends χ`
(`ParitySystem.holds_tseitin_iff_eval_tseitinFormula`), so it is unsatisfiable when the total
charge is odd (`ParitySystem.not_holds_tseitin`), and on a connected multigraph satisfiable
exactly when the total charge is even (`ParitySystem.exists_holds_tseitin_iff`).

## Main definitions

* `Cslib.Logic.PL.ParitySystem.tseitin`: the Tseitin parity system of a multigraph with charges.

## Main results

* `Cslib.Logic.PL.ParitySystem.holds_tseitin_iff`,
  `Cslib.Logic.PL.ParitySystem.holds_tseitin_iff_eval_tseitinFormula`: the semantics of Tseitin
  parity systems.
* `Cslib.Logic.PL.ParitySystem.not_holds_tseitin`,
  `Cslib.Logic.PL.ParitySystem.exists_holds_tseitin_iff`: satisfiability by total charge.

## References

* [G. S. Tseitin, *On the complexity of derivation in propositional calculus*][Tseitin1983]
* [A. Urquhart, *Hard examples for resolution*][Urquhart1987]
-/

public section

namespace Cslib.Logic.PL.ParitySystem

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

/-- The **Tseitin parity system** of the multigraph `ends` with charges `χ`: a variable for each
edge, and for each vertex `v` the equation saying that the parity of the edges at `v` other than
self-loops is `χ v`. -/
noncomputable def tseitin (ends : E → Sym2 V) (χ : V → Bool) : ParitySystem E :=
  univ.toList.map fun v => (Multigraph.incidence ends v, χ v)

variable {ends : E → Sym2 V} {χ : V → Bool}

/-- The equations of the Tseitin parity system are those of the vertices. -/
theorem mem_tseitin {e : Finset E × Bool} :
    e ∈ tseitin ends χ ↔ ∃ v, (Multigraph.incidence ends v, χ v) = e := by
  simp [tseitin]

/-- The Tseitin parity system has an equation for each vertex. -/
@[simp] theorem length_tseitin : (tseitin ends χ).length = Fintype.card V := by
  simp [tseitin]

/-- The equation of the vertex `v` belongs to the Tseitin parity system. -/
theorem incidence_mem_tseitin (v : V) : (Multigraph.incidence ends v, χ v) ∈ tseitin ends χ :=
  mem_tseitin.2 ⟨v, rfl⟩

/-- An assignment satisfies the Tseitin parity system when its parity at every vertex is the
charge. -/
theorem holds_tseitin_iff (a : E → Bool) :
    (tseitin ends χ).Holds a ↔ ∀ v, parityOn (Multigraph.incidence ends v) a = χ v := by
  simp [Holds, mem_tseitin]

/-- The Tseitin parity system and the Tseitin formula have the same satisfying assignments. -/
theorem holds_tseitin_iff_eval_tseitinFormula [DecidableEq E] (a : E → Bool) :
    (tseitin ends χ).Holds a ↔ (CNF.tseitinFormula ends χ).eval a = true := by
  rw [holds_tseitin_iff, CNF.eval_tseitinFormula_eq_true_iff]

/-- **Tseitin parity systems with odd total charge are unsatisfiable.** -/
theorem not_holds_tseitin (h : parityOn univ χ = true) (a : E → Bool) :
    ¬ (tseitin ends χ).Holds a := fun ha => by
  rw [Tseitin.parityOn_univ_eq_false_of_forall ((holds_tseitin_iff a).1 ha)] at h
  exact Bool.false_ne_true h

/-- On a connected multigraph, **the Tseitin parity system is satisfiable exactly when the total
charge is even**. -/
theorem exists_holds_tseitin_iff (hG : (Multigraph.toSimpleGraph ends).Connected) :
    (∃ a, (tseitin ends χ).Holds a) ↔ parityOn univ χ = false := by
  classical
  simp only [holds_tseitin_iff_eval_tseitinFormula]
  exact CNF.satisfiable_tseitinFormula_iff hG

end Cslib.Logic.PL.ParitySystem
