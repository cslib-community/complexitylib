/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Zigzag
public import Complexity.Foundations.Combinatorics.Expander.Power
public import Complexity.Foundations.Combinatorics.Expander.IteratedProd

/-!
# The zig-zag tower

A single expander `H` of constant size generates an infinite family of expanders of constant
degree, by alternating squaring with the zig-zag product
[Reingold, Vadhan and Wigderson, Section 1.2][ReingoldVadhanWigderson2002]
[Hoory, Linial and Wigderson, Section 9.2][HooryLinialWigderson2006]. Let `H` be a `D`-regular
multigraph on `B`, with an equivalence `e : B ≃ (Fin 2 → D × D)`, so that `H` has `|D| ^ 4`
vertices. Then

* `G₁ = H ^ 2`, with its labels `Fin 2 → D` renamed to `D × D`;
* `Gₙ₊₁ = Gₙ ^ 2 ⓩ H`: the square `Gₙ ^ 2` has the labels `Fin 2 → D × D`, which `e.symm` renames
  to the vertices `B` of `H`, so that it can be zig-zagged with `H`.

Squaring raises the degree `|D| ^ 2` of `Gₙ` to `|D| ^ 4`, and the zig-zag product with `H` brings
it back to `|D| ^ 2` while multiplying the number of vertices by `|B| = |D| ^ 4`. So `Gₙ` is a
`|D| ^ 2`-regular multigraph on `|D| ^ (4 n)` vertices. If `λ(H) ≤ 1 / 5`, then `λ(Gₙ) ≤ 2 / 5`
for every `n` [Reingold, Vadhan and Wigderson, Theorem 1.4][ReingoldVadhanWigderson2002]: at the
start `λ(G₁) ≤ λ(H) ^ 2 ≤ 1 / 25`, and by the zig-zag theorem
`Cslib.RotationMap.spectralExpansion_zigzag_le`,
`λ(Gₙ₊₁) ≤ λ(Gₙ) ^ 2 + λ(H) + λ(H) ^ 2 ≤ 4 / 25 + 1 / 5 + 1 / 25 = 2 / 5`. More generally, the
bound `λ(Gₙ) ≤ c` is kept whenever `c ^ 2 + λ(H) + λ(H) ^ 2 ≤ c`.

Here `Cslib.RotationMap.zigzagTower H e n` is the graph `Gₙ₊₁`, on the vertices
`Cslib.RotationMap.ZigzagTowerVertex B n`, the `(n + 1)`-fold product `(⋯ (B × B) × ⋯) × B`.
The tower is explicit given `H` and `e`: `zigzagTower` is a computable definition, which computes
the rotation maps of the tower from `H.rot`, `e` and `e.symm` by a recursion without choices; the
rotation map of `Gₙ₊₁` evaluates that of `Gₙ` twice and `H.rot` twice. So `H` is the only ingredient
of the family that may be non-explicit. Evaluating the rotation map of `Gₙ` takes `2 ^ (n + 1) - 2`
evaluations of `H.rot`, polynomially many in the number of vertices of `Gₙ` but not in the length
of their names: the tower is only mildly explicit
[Hoory, Linial and Wigderson, Section 9.2][HooryLinialWigderson2006], and Reingold, Vadhan and
Wigderson interleave tensor products to make it fully explicit
[Reingold, Vadhan and Wigderson, Section 3.2][ReingoldVadhanWigderson2002].

## Main definitions

* `Cslib.RotationMap.ZigzagTowerVertex`: the vertices of the graphs of the tower.
* `Cslib.RotationMap.zigzagTower`: the zig-zag tower `G₁, G₂, …` over a base graph `H`.

## Main results

* `Cslib.RotationMap.card_zigzagTowerVertex`,
  `Cslib.RotationMap.card_zigzagTowerVertex_of_equiv`: `Gₙ₊₁` has `|B| ^ (n + 1)` vertices, that
  is `|D| ^ (4 (n + 1))`.
* `Cslib.RotationMap.lt_card_zigzagTowerVertex`: the graphs of the tower grow without bound.
* `Cslib.RotationMap.spectralExpansion_zigzagTower_le`: if `c ^ 2 + λ(H) + λ(H) ^ 2 ≤ c`, then
  every graph of the tower has spectral expansion at most `c`.
* `Cslib.RotationMap.spectralExpansion_zigzagTower_le_two_div_five`: if `λ(H) ≤ 1 / 5`, then
  every graph of the tower has spectral expansion at most `2 / 5`
  [Reingold, Vadhan and Wigderson, Theorem 1.4][ReingoldVadhanWigderson2002].

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

@[expose] public section

namespace Cslib.RotationMap

universe u

/-- The vertices of the `(n + 1)`-st graph of the zig-zag tower over a base graph on `B`: the
`(n + 1)`-fold product `(⋯ (B × B) × ⋯) × B`, nested to the left, as each zig-zag product pairs
a vertex of the previous graph with a vertex of the base graph. They are the iterated products
`Cslib.IteratedProd B B n`, whose instances and cardinality apply. -/
abbrev ZigzagTowerVertex (B : Type u) : ℕ → Type u :=
  IteratedProd B B

/-- The `(n + 1)`-st graph of the tower has `|B| ^ (n + 1)` vertices. -/
theorem card_zigzagTowerVertex (B : Type u) [Fintype B] (n : ℕ) :
    Fintype.card (ZigzagTowerVertex B n) = Fintype.card B ^ (n + 1) := by
  rw [IteratedProd.card, pow_succ, mul_comm]

/-- The graphs of the tower grow without bound: if the base graph has at least two vertices, then
the `(n + 1)`-st graph of the tower has more than `n` vertices. -/
theorem lt_card_zigzagTowerVertex {B : Type u} [Fintype B] (hB : 1 < Fintype.card B) (n : ℕ) :
    n < Fintype.card (ZigzagTowerVertex B n) := by
  rw [card_zigzagTowerVertex]
  exact n.lt_succ_self.trans (Nat.lt_pow_self hB)

variable {B : Type u} {D : Type*}

/-- When the vertices of the base graph name the pairs of pairs of its labels, the `(n + 1)`-st
graph of the tower has `|D| ^ (4 (n + 1))` vertices
[Reingold, Vadhan and Wigderson, Theorem 1.4][ReingoldVadhanWigderson2002]. -/
theorem card_zigzagTowerVertex_of_equiv [Fintype B] [Fintype D] (e : B ≃ (Fin 2 → D × D))
    (n : ℕ) : Fintype.card (ZigzagTowerVertex B n) = Fintype.card D ^ (4 * (n + 1)) := by
  rw [card_zigzagTowerVertex, Fintype.card_congr e, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_fin]
  ring

variable (H : RotationMap B D) (e : B ≃ (Fin 2 → D × D))

/-- The **zig-zag tower** [Reingold, Vadhan and Wigderson, Section 1.2][ReingoldVadhanWigderson2002]
[Hoory, Linial and Wigderson, Section 9.2][HooryLinialWigderson2006] over a `D`-regular base graph
`H` whose vertices name the pairs of pairs of its labels by `e`. `zigzagTower H e n` is the graph
`Gₙ₊₁` of the tower `G₁ = H ^ 2`, `Gₙ₊₁ = Gₙ ^ 2 ⓩ H`: the base graph squared, with its labels
`Fin 2 → D` renamed to `D × D`, and then, at each step, the square of the previous graph, with its
labels `Fin 2 → D × D` renamed by `e.symm` to the vertices of `H`, zig-zagged with `H`. -/
def zigzagTower : (n : ℕ) → RotationMap (ZigzagTowerVertex B n) (D × D)
  | 0 => (H.pow 2).relabel (finTwoArrowEquiv D)
  | n + 1 => (((zigzagTower n).pow 2).relabel e.symm).zigzag H

/-- The first graph of the tower is the base graph squared. -/
theorem zigzagTower_zero : zigzagTower H e 0 = (H.pow 2).relabel (finTwoArrowEquiv D) :=
  rfl

/-- Each graph of the tower is the square of the previous one zig-zagged with the base graph. -/
theorem zigzagTower_succ (n : ℕ) :
    zigzagTower H e (n + 1) = (((zigzagTower H e n).pow 2).relabel e.symm).zigzag H :=
  rfl

/-- The rotation map of each graph of the tower is that of the square of the previous one
zig-zagged with the base graph. -/
theorem rot_zigzagTower_succ (n : ℕ) (v : ZigzagTowerVertex B n) (k : B) (i j : D) :
    (zigzagTower H e (n + 1)).rot ((v, k), (i, j)) =
      ((((zigzagTower H e n).pow 2).relabel e.symm).zigzag H).rot ((v, k), (i, j)) :=
  rfl

variable [Fintype B] [Fintype D]

/-- **The zig-zag tower is a family of expanders**: if `c ^ 2 + λ(H) + λ(H) ^ 2 ≤ c`, then every
graph of the tower has spectral expansion at most `c`. -/
theorem spectralExpansion_zigzagTower_le {c : ℝ}
    (hc : c ^ 2 + H.spectralExpansion + H.spectralExpansion ^ 2 ≤ c) (n : ℕ) :
    (zigzagTower H e n).spectralExpansion ≤ c := by
  have hH := H.spectralExpansion_nonneg
  induction n with
  | zero =>
    calc (zigzagTower H e 0).spectralExpansion = (H.pow 2).spectralExpansion :=
          spectralExpansion_relabel _ _
      _ ≤ H.spectralExpansion ^ 2 := H.spectralExpansion_pow_le 2
      _ ≤ c := by linarith [sq_nonneg c]
  | succ n ih =>
    have hG := (zigzagTower H e n).spectralExpansion_nonneg
    refine ((((zigzagTower H e n).pow 2).relabel e.symm).spectralExpansion_zigzag_le H).trans ?_
    rw [spectralExpansion_relabel]
    have := (zigzagTower H e n).spectralExpansion_pow_le 2
    have : (zigzagTower H e n).spectralExpansion ^ 2 ≤ c ^ 2 := by gcongr
    linarith

/-- **The zig-zag tower is a family of expanders**
[Reingold, Vadhan and Wigderson, Theorem 1.4][ReingoldVadhanWigderson2002]: if the base graph has
spectral expansion at most `1 / 5`, then every graph of the tower has spectral expansion at most
`2 / 5`. -/
theorem spectralExpansion_zigzagTower_le_two_div_five (hH : H.spectralExpansion ≤ 1 / 5)
    (n : ℕ) : (zigzagTower H e n).spectralExpansion ≤ 2 / 5 := by
  refine spectralExpansion_zigzagTower_le H e ?_ n
  have := H.spectralExpansion_nonneg
  nlinarith

end Cslib.RotationMap
