/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/List/ProdSigma.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Multiset.Bind

/-!
# Filtering and swapping list products

The list product `l₁ ×ˢ l₂` enumerates pairs with the left element outermost. Filtering it by a
predicate of one component is the product with that list filtered, as for `Finset`
(`Finset.filter_product_left`), and swapping its pairs permutes it into `l₂ ×ˢ l₁`, as for
`Multiset` (`Multiset.map_swap_product`). The list forms keep the order of the pairs, which matters
when lists represent bags of rows in a fixed order.

## Main results

* `List.filter_product_left`, `List.filter_product_right`: filtering a product by one component.
* `List.perm_map_swap_product`: swapping the pairs of a product permutes it into the other product.
-/

public section

namespace List

variable {α β : Type*}

/-- Filtering a product by a predicate of the left component filters the left list. -/
theorem filter_product_left (p : α → Bool) (l₁ : List α) (l₂ : List β) :
    (l₁ ×ˢ l₂).filter (fun (a, _) => p a) = l₁.filter p ×ˢ l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a l ih =>
    rw [product_cons, filter_append, ih, filter_map]
    by_cases ha : p a
    · simp [ha, Function.comp_def, product_cons]
    · simp [ha, Function.comp_def]

/-- Filtering a product by a predicate of the right component filters the right list. -/
theorem filter_product_right (p : β → Bool) (l₁ : List α) (l₂ : List β) :
    (l₁ ×ˢ l₂).filter (fun (_, b) => p b) = l₁ ×ˢ l₂.filter p := by
  induction l₁ with
  | nil => rfl
  | cons a l ih =>
    rw [product_cons, filter_append, ih, filter_map, product_cons]
    rfl

/-- Swapping the pairs of `l₁ ×ˢ l₂` gives a permutation of `l₂ ×ˢ l₁`. -/
theorem perm_map_swap_product (l₁ : List α) (l₂ : List β) :
    ((l₁ ×ˢ l₂).map Prod.swap).Perm (l₂ ×ˢ l₁) := by
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, ← Multiset.coe_product,
    Multiset.map_swap_product, Multiset.coe_product]

end List
