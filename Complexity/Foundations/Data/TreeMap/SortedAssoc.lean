/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.List.SortedAssoc
public import Std.Data.TreeMap.Basic
import Std.Data.TreeMap.Lemmas

/-!
# Sorted association lists and `Std.TreeMap`

On a sorted association list `l` over a linear order, the entries of Lean core's
`Std.TreeMap.ofList l compare` are `l` itself. The proof uses only the public lemmas of
`Std.TreeMap`, nothing of its internals.

## Main results

* `Std.TreeMap.toList_ofList_of_isSortedAssoc`: the tree map built from a sorted association list
  lists exactly that list.

Ported from `cslib-community/EpsilonEridani` at commit `1966ab476`:
[EpsilonEridani/Foundations/Data/TreeMap/SortedAssoc.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Foundations/Data/TreeMap/SortedAssoc.lean).
-/

public section

variable {α β : Type} [LinearOrder α]

namespace Std.TreeMap

/-- The entries of the tree map built from a sorted association list are the list itself. -/
theorem toList_ofList_of_isSortedAssoc {l : List (α × β)} (h : l.IsSortedAssoc) :
    (ofList l compare).toList = l := by
  have hd : l.Pairwise fun a b => ¬compare a.1 b.1 = .eq :=
    h.pairwise.imp fun hab => by rw [compare_eq_iff_eq]; exact hab.ne
  have hof : ∀ {k : α} {v : β}, (k, v) ∈ l → (ofList l compare)[k]? = some v :=
    fun hm => getElem?_ofList_of_mem (compare_eq_iff_eq.2 rfl) hd hm
  refine List.IsSortedAssoc.eq_of_forall_mem_iff ?_ h fun ⟨k, v⟩ => ?_
  · rw [List.isSortedAssoc_iff_pairwise, List.pairwise_map]
    exact ordered_keys_toList.imp fun hab => compare_lt_iff_lt.1 hab
  · rw [mem_toList_iff_getElem?_eq_some]
    refine ⟨fun hk => ?_, hof⟩
    by_cases hc : (l.map Prod.fst).contains k
    · obtain ⟨⟨k', v'⟩, hm, rfl⟩ := List.mem_map.1 (List.contains_iff_mem.1 hc)
      rw [hof hm, Option.some_inj] at hk
      exact hk ▸ hm
    · simp [getElem?_ofList_of_contains_eq_false (Bool.eq_false_iff.2 hc)] at hk

end Std.TreeMap
