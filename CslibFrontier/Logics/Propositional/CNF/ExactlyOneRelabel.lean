/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ExactlyOne

/-!
# Injective transport of exactly-one constraints

Reusing the existing distinct-variable encoding under a wire embedding preserves its actual
clause list. Injectivity is necessary because identifying two variables changes the exclusions.
-/

public section

namespace Cslib.Logic.PL.CNF

/-- Exactly-one construction commutes with an injective variable relabeling. -/
theorem relabel_exactlyOne {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (vs : List V) :
    CNF.relabel f (CNF.exactlyOne vs) = CNF.exactlyOne (vs.map f) := by
  simp only [CNF.exactlyOne, CNF.atLeastOne, CNF.atMostOne, CNF.relabel, Clause.relabel,
    List.map_append, List.map_cons, List.map_nil, List.map_flatMap, List.map_map,
    List.flatMap_map, List.filter_map, Function.comp_def, Prod.map, id_eq, ne_eq, hf.eq_iff]

/-- Exactly-one has one wide positive clause and binary exclusions. -/
theorem width_exactlyOne {V : Type*} [DecidableEq V] (vs : List V) (c : Clause V)
    (hc : c ∈ CNF.exactlyOne vs) : c.length ≤ max vs.length 2 := by
  rcases List.mem_append.mp hc with hc | hc
  · have he := List.mem_singleton.mp hc
    subst c
    simpa only [List.length_map] using Nat.le_max_left vs.length 2
  · simp only [CNF.atMostOne, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨_, _, _, _, rfl⟩ := hc
    exact Nat.le_max_right _ _

end Cslib.Logic.PL.CNF
