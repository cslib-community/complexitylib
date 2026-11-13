/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.CubicEdgeColoring
public import CslibFrontier.Foundations.Combinatorics.Expander.AffineFamily
public import CslibFrontier.Foundations.Combinatorics.Expander.Cheeger
public import CslibFrontier.Foundations.Combinatorics.Expander.Loops

/-!
# Cubic edge-coloured expanders

A `K`-regular multigraph `G` on `V`, given by a rotation map with labels `Fin K`, becomes a simple
cubic graph with a proper `3`-edge-colouring (`Cslib.RotationMap.cubicReplacement`) on
`(Bool × V) × (Fin K × Bool)`, so on `4 K |V|` vertices. Take two copies `(false, v)` and
`(true, v)` of every vertex, its *sides*, and replace each copy by a *cloud*: a cycle of length
`2 K` through the points `(j, false)`, `(j, true)`, `(j + 1, false)`, …, `j ∈ Fin K`. The cycle is
even, so its edges alternate between two perfect matchings, colours `0` (`(j, false)`–`(j, true)`)
and `1` (`(j, true)`–`(j + 1, false)`). Colour `2` joins clouds on opposite sides:

* the *base* point `((b, v), (j, false))` is joined to `((!b, w), (i, false))` when
  `G.rot (v, j) = (w, i)`, which is the replacement product with a cycle
  [Hoory, Linial and Wigderson, Section 9.4][HooryLinialWigderson2006] of the bipartite double
  cover of `G`;
* the *vertical* point `((b, v), (j, true))` is joined to `((!b, v), (j, true))`.

Colour `2` always changes the side, so it creates neither self-loops nor parallel edges, even when
`G` has them. The vertical edges stop the bipartite double cover from falling apart when `G` is
(nearly) bipartite.

The construction keeps balanced-cut edge expansion with explicit constants
(`Cslib.RotationMap.isBalancedCutExpander_cubicReplacement`): if `G` has edge expansion at least
`h ≥ 0`, every cut of the cubic graph into parts of at least a third of its vertices is crossed by
at least `h |V| / (3 (h + K + 1))` edges. The proof is combinatorial. A cloud lying partly on
each side of the cut contributes a crossing edge of colour `0` or `1`. The vertices `v` with both
clouds on the same side of the cut form two sets `U` and `W`, which are both large when few clouds
are split; colour-`2` edges cross the cut along the vertical edges of the remaining vertices and
along the edges of `G` from `U` to `W`.

Applied to the explicit arithmetic expanders `Cslib.RotationMap.arithmeticExpander`, this gives
simple cubic graphs with proper `3`-edge-colourings on `8 ⋅ 257 ^ 12 ⋅ m` vertices for every
`m ≥ 2`, all balanced-cut `γ`-edge expanders for one `γ > 0`
(`Cslib.RotationMap.isBalancedCutExpander_cubicArithmeticExpander`). This is the part of
[ArenasBroadrickLiewVanDenBroeck2026, Proposition 5.2] used by their Theorem 1.1; the proposition
also asks for every even number of vertices `n ≥ 6` and a polynomial-time algorithm, which are not
proved here.

## Main definitions

* `Cslib.RotationMap.cubicMate`: the three perfect matchings.
* `Cslib.RotationMap.cubicReplacement`: the cubic graph with its proper `3`-edge-colouring.
* `Cslib.RotationMap.cubicArithmeticExpander`: the construction applied to the arithmetic
  expanders, on `Fin (8 * 257 ^ 12 * m)`.

## Main results

* `Cslib.RotationMap.isBalancedCutExpander_cubicReplacement`: edge expansion of `G` gives
  balanced-cut edge expansion of the cubic graph.
* `Cslib.RotationMap.isBalancedCutExpander_cubicArithmeticExpander`: a family of cubic
  edge-coloured balanced-cut expanders.
* `Cslib.RotationMap.exists_cubicEdgeColoring_isBalancedCutExpander`: such graphs exist on
  unboundedly many vertex counts.

## References

* [M. Arenas, O. Broadrick, V. Liew, G. Van den Broeck, *d-DNNF is not polynomially closed under
  negation*][ArenasBroadrickLiewVanDenBroeck2026]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

public section

namespace Cslib.RotationMap

open Finset

variable {V : Type*} {K : ℕ} [NeZero K] (G : RotationMap V (Fin K))

/-- The three perfect matchings of the cubic replacement of `G`: colour `0` joins `(j, false)` to
`(j, true)` and colour `1` joins `(j, true)` to `(j + 1, false)` inside a cloud; colour `2` joins a
base point `((b, v), (j, false))` to `((!b, w), (i, false))` when `G.rot (v, j) = (w, i)`, and a
vertical point `((b, v), (j, true))` to `((!b, v), (j, true))`. -/
@[expose] def cubicMate (c : Fin 3) : (Bool × V) × (Fin K × Bool) → (Bool × V) × (Fin K × Bool) :=
  ![fun ⟨q, j, s⟩ => (q, j, !s),
    fun ⟨q, j, s⟩ => (q, bif s then (j + 1, false) else (j - 1, true)),
    fun ⟨⟨b, v⟩, j, s⟩ =>
      bif s then ((!b, v), j, s) else Prod.map (Prod.mk !b) (·, false) (G.rot (v, j))] c

@[simp]
theorem cubicMate_zero (q : Bool × V) (j : Fin K) (s : Bool) :
    G.cubicMate 0 (q, j, s) = (q, j, !s) :=
  rfl

@[simp]
theorem cubicMate_one_true (q : Bool × V) (j : Fin K) :
    G.cubicMate 1 (q, j, true) = (q, j + 1, false) :=
  rfl

@[simp]
theorem cubicMate_one_false (q : Bool × V) (j : Fin K) :
    G.cubicMate 1 (q, j, false) = (q, j - 1, true) :=
  rfl

@[simp]
theorem cubicMate_two_true (b : Bool) (v : V) (j : Fin K) :
    G.cubicMate 2 ((b, v), j, true) = ((!b, v), j, true) :=
  rfl

@[simp]
theorem cubicMate_two_false (b : Bool) (v : V) (j : Fin K) :
    G.cubicMate 2 ((b, v), j, false) = ((!b, G.neighbor v j), (G.rot (v, j)).2, false) :=
  rfl

theorem cubicMate_cubicMate (c : Fin 3) (x : (Bool × V) × (Fin K × Bool)) :
    G.cubicMate c (G.cubicMate c x) = x := by
  obtain ⟨⟨b, v⟩, j, s⟩ := x
  fin_cases c <;> cases s <;> simp [neighbor]

theorem cubicMate_ne (c : Fin 3) (x : (Bool × V) × (Fin K × Bool)) : G.cubicMate c x ≠ x := by
  obtain ⟨⟨b, v⟩, j, s⟩ := x
  fin_cases c <;> cases s <;> simp

theorem cubicMate_injective (hK : 1 < K) (x : (Bool × V) × (Fin K × Bool)) :
    Function.Injective fun c => G.cubicMate c x := by
  have h1 : (1 : Fin K) ≠ 0 := fun h => by
    have := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt hK] at this
  obtain ⟨⟨b, v⟩, j, s⟩ := x
  intro c c' h
  fin_cases c <;> fin_cases c' <;> cases s <;> simp_all [eq_comm (a := j)]

/-- **The cubic replacement** of a `K`-regular multigraph `G`, for `K ≥ 2`: the simple cubic graph
on `(Bool × V) × (Fin K × Bool)` whose colour classes are the three matchings `G.cubicMate`. -/
@[expose] def cubicReplacement (hK : 1 < K) : CubicEdgeColoring ((Bool × V) × (Fin K × Bool)) where
  mate := G.cubicMate
  mate_mate := G.cubicMate_cubicMate
  mate_ne := G.cubicMate_ne
  mate_injective := G.cubicMate_injective hK

@[simp]
theorem cubicReplacement_mate (hK : 1 < K) : (G.cubicReplacement hK).mate = G.cubicMate :=
  rfl

/-! ### Balanced-cut expansion -/

variable [Fintype V] [DecidableEq V]

/-- The cloud of `q` lies inside `T`. -/
private def CloudIn (T : Finset ((Bool × V) × (Fin K × Bool))) (q : Bool × V) : Prop :=
  ∀ ℓ, (q, ℓ) ∈ T

private instance (T : Finset ((Bool × V) × (Fin K × Bool))) : DecidablePred (CloudIn T) :=
  fun q => inferInstanceAs (Decidable (∀ ℓ, (q, ℓ) ∈ T))

/-- No cloud lies both inside `T` and inside its complement. -/
private theorem not_cloudIn_compl {T : Finset ((Bool × V) × (Fin K × Bool))} {q : Bool × V}
    (h : CloudIn T q) : ¬CloudIn Tᶜ q := fun h' => mem_compl.1 (h' (0, false)) (h (0, false))

open Fin.NatCast in
/-- **A split cloud has a crossing cycle edge.** A cloud meeting both `T` and its complement has a
point of `T` whose colour-`0` or colour-`1` partner is outside `T`. -/
private theorem exists_cubicMate_notMem (T : Finset ((Bool × V) × (Fin K × Bool)))
    {q : Bool × V} (h₀ : ¬CloudIn Tᶜ q) (h₁ : ¬CloudIn T q) :
    ∃ ℓ, (q, ℓ) ∈ T ∧ (G.cubicMate 0 (q, ℓ) ∉ T ∨ G.cubicMate 1 (q, ℓ) ∉ T) := by
  simp only [CloudIn, mem_compl, not_forall, not_not] at h₀ h₁
  obtain ⟨⟨j₀, s₀⟩, h₀⟩ := h₀
  obtain ⟨⟨j₁, s₁⟩, h₁⟩ := h₁
  by_contra! h
  have hfalse : ∀ {j s}, (q, j, s) ∈ T → (q, j, false) ∈ T := by
    intro j s hj
    cases s
    · exact hj
    · simpa using (h _ hj).1
  have hstep : ∀ j : Fin K, (q, j, false) ∈ T → (q, j + 1, false) ∈ T := fun j hj => by
    have h0 : (q, j, true) ∈ T := by simpa using (h _ hj).1
    simpa using (h _ h0).2
  have hall : ∀ k : ℕ, (q, j₀ + (Nat.cast k : Fin K), false) ∈ T := by
    intro k
    induction k with
    | zero => simpa using hfalse h₀
    | succ k ih => simpa [Nat.cast_succ, add_assoc] using hstep _ ih
  have hj₁ : (q, j₁, false) ∈ T := by simpa [Fin.cast_val_eq_self] using hall (j₁ - j₀).val
  apply h₁
  cases s₁
  · exact hj₁
  · simpa using (h _ hj₁).1

omit [NeZero K] [DecidableEq V] in
theorem card_cubicVertex :
    Fintype.card ((Bool × V) × (Fin K × Bool)) = 4 * K * Fintype.card V := by
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  ring

omit [NeZero K] in
/-- Points of `T` lie in clouds not inside `Tᶜ`; those are the clouds of vertices with both clouds
inside `T`, of vertices with one cloud inside `T` and the other inside `Tᶜ`, and the split clouds
and their partners. -/
private theorem card_le_cloudIn (T : Finset ((Bool × V) × (Fin K × Bool))) :
    #T ≤ 2 * K * (2 * #{v | CloudIn T (false, v) ∧ CloudIn T (true, v)} +
      #{v | CloudIn T (false, v) ∧ CloudIn Tᶜ (true, v)} +
      #{v | CloudIn Tᶜ (false, v) ∧ CloudIn T (true, v)} +
      2 * #{q | ¬CloudIn T q ∧ ¬CloudIn Tᶜ q}) := by
  set U : Finset V := {v | CloudIn T (false, v) ∧ CloudIn T (true, v)}
  set Q₁ : Finset V := {v | CloudIn T (false, v) ∧ CloudIn Tᶜ (true, v)}
  set Q₂ : Finset V := {v | CloudIn Tᶜ (false, v) ∧ CloudIn T (true, v)}
  set P : Finset (Bool × V) := {q | ¬CloudIn T q ∧ ¬CloudIn Tᶜ q}
  set N : Finset (Bool × V) := {q | ¬CloudIn Tᶜ q}
  have hsub : T ⊆ N ×ˢ (univ : Finset (Fin K × Bool)) := fun x hx => by
    simp only [N, mem_product, mem_filter, mem_univ, true_and, and_true]
    exact fun h => mem_compl.1 (h x.2) hx
  have hclouds : N ⊆
      ((univ ×ˢ U ∪ {false} ×ˢ Q₁) ∪ {true} ×ˢ Q₂) ∪ (P ∪ P.image fun q => (!q.1, q.2)) := by
    rintro ⟨b, v⟩ hq
    simp only [N, mem_filter, mem_univ, true_and] at hq
    simp only [U, Q₁, Q₂, P, mem_union, mem_product, mem_univ, mem_singleton, mem_filter,
      true_and, mem_image, Prod.exists, Prod.mk.injEq]
    by_cases hT : CloudIn T (b, v)
    · by_cases h' : CloudIn T (!b, v)
      · cases b <;> simp_all
      by_cases h'' : CloudIn Tᶜ (!b, v)
      · cases b <;> simp_all
      · right; right
        exact ⟨!b, v, ⟨h', h''⟩, by simp, rfl⟩
    · right; left
      exact ⟨hT, hq⟩
  calc #T ≤ #(N ×ˢ (univ : Finset (Fin K × Bool))) := card_le_card hsub
    _ = 2 * K * #N := by
      rw [card_product, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      ring
    _ ≤ 2 * K * (2 * #U + #Q₁ + #Q₂ + 2 * #P) := by
      gcongr
      refine (card_le_card hclouds).trans ?_
      refine (card_union_le _ _).trans ?_
      have h1 := card_union_le (univ ×ˢ U ∪ {false} ×ˢ Q₁) ({true} ×ˢ Q₂)
      have h2 := card_union_le (univ ×ˢ U) ({false} ×ˢ Q₁)
      have h3 := card_union_le P (P.image fun q => (!q.1, q.2))
      have h4 := card_image_le (s := P) (f := fun q => (!q.1, q.2))
      simp only [card_product, card_univ, Fintype.card_bool, card_singleton, one_mul] at h1 h2
      omega

/-- The vertices whose two clouds are neither both inside `T` nor both inside `Tᶜ` have one cloud
in each, or a split cloud. -/
private theorem card_mixed_le (T : Finset ((Bool × V) × (Fin K × Bool))) :
    #{v | ¬(CloudIn T (false, v) ∧ CloudIn T (true, v)) ∧
        ¬(CloudIn Tᶜ (false, v) ∧ CloudIn Tᶜ (true, v))} ≤
      #{v | CloudIn T (false, v) ∧ CloudIn Tᶜ (true, v)} +
      #{v | CloudIn Tᶜ (false, v) ∧ CloudIn T (true, v)} +
      #{q | ¬CloudIn T q ∧ ¬CloudIn Tᶜ q} := by
  set P : Finset (Bool × V) := {q | ¬CloudIn T q ∧ ¬CloudIn Tᶜ q}
  set Q₁ : Finset V := {v | CloudIn T (false, v) ∧ CloudIn Tᶜ (true, v)}
  set Q₂ : Finset V := {v | CloudIn Tᶜ (false, v) ∧ CloudIn T (true, v)}
  have hsub : ({v | ¬(CloudIn T (false, v) ∧ CloudIn T (true, v)) ∧
        ¬(CloudIn Tᶜ (false, v) ∧ CloudIn Tᶜ (true, v))} : Finset V) ⊆
      (Q₁ ∪ Q₂) ∪ P.image Prod.snd := by
    intro v hv
    simp only [P, Q₁, Q₂, mem_filter, mem_univ, true_and, mem_union, mem_image, Prod.exists,
      exists_eq_right] at hv ⊢
    by_cases hf : CloudIn T (false, v) <;> by_cases hf' : CloudIn Tᶜ (false, v) <;>
      by_cases ht : CloudIn T (true, v) <;> by_cases ht' : CloudIn Tᶜ (true, v) <;>
      first
        | exact absurd hf' (not_cloudIn_compl hf)
        | exact absurd ht' (not_cloudIn_compl ht)
        | (right; exact ⟨false, hf, hf'⟩)
        | (right; exact ⟨true, ht, ht'⟩)
        | simp_all
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  gcongr
  · exact card_union_le _ _
  · exact card_image_le

/-- **Balanced-cut expansion of the cubic replacement.** If the `K`-regular multigraph `G`, with
`K ≥ 2`, has edge expansion at least `h ≥ 0`, then its cubic replacement, on `4 K |V|` vertices,
is a balanced-cut `h / (12 K (h + K + 1))`-edge expander: every cut into two parts of at least a
third of the vertices is crossed by at least `h |V| / (3 (h + K + 1))` edges. -/
theorem isBalancedCutExpander_cubicReplacement (hK : 1 < K) {h : ℝ} (h₀ : 0 ≤ h)
    (hG : h ≤ G.edgeExpansion) :
    IsBalancedCutExpander (G.cubicReplacement hK).toSimpleGraph (h / (12 * K * (h + K + 1))) := by
  intro T hT hTc
  rw [CubicEdgeColoring.card_interedges, Fin.sum_univ_three, cubicReplacement_mate]
  rw [card_cubicVertex] at hT hTc ⊢
  set m := Fintype.card V
  set U : Finset V := {v | CloudIn T (false, v) ∧ CloudIn T (true, v)}
  set W : Finset V := {v | CloudIn Tᶜ (false, v) ∧ CloudIn Tᶜ (true, v)}
  set Q₁ : Finset V := {v | CloudIn T (false, v) ∧ CloudIn Tᶜ (true, v)}
  set Q₂ : Finset V := {v | CloudIn Tᶜ (false, v) ∧ CloudIn T (true, v)}
  set P : Finset (Bool × V) := {q | ¬CloudIn T q ∧ ¬CloudIn Tᶜ q}
  set Y : Finset V := {v | ¬(CloudIn T (false, v) ∧ CloudIn T (true, v)) ∧
    ¬(CloudIn Tᶜ (false, v) ∧ CloudIn Tᶜ (true, v))}
  -- Split clouds cross the cut along cycle edges.
  have hA : #P ≤ #{x ∈ T | G.cubicMate 0 x ∉ T} + #{x ∈ T | G.cubicMate 1 x ∉ T} := by
    have hsub : P ⊆ ({x ∈ T | G.cubicMate 0 x ∉ T} ∪ {x ∈ T | G.cubicMate 1 x ∉ T}).image
        Prod.fst := by
      intro q hq
      simp only [P, mem_filter, mem_univ, true_and] at hq
      obtain ⟨ℓ, hℓ, hc⟩ := G.exists_cubicMate_notMem T hq.2 hq.1
      exact mem_image.2 ⟨(q, ℓ), by simp only [mem_union, mem_filter]; tauto, rfl⟩
    exact (card_le_card hsub).trans (card_image_le.trans (card_union_le _ _))
  -- Colour `2` crosses the cut along vertical edges and along the edges of `G` from `U` to `W`.
  have hB : #(G.interedges U W) + K * #Q₁ + K * #Q₂ ≤ #{x ∈ T | G.cubicMate 2 x ∉ T} := by
    let f₁ : V × Fin K → (Bool × V) × (Fin K × Bool) := fun p => ((false, p.1), p.2, false)
    let f₂ : V × Fin K → (Bool × V) × (Fin K × Bool) := fun p => ((false, p.1), p.2, true)
    let f₃ : V × Fin K → (Bool × V) × (Fin K × Bool) := fun p => ((true, p.1), p.2, true)
    have hinj : ∀ b s : Bool, Function.Injective fun p : V × Fin K => ((b, p.1), p.2, s) :=
      fun b s p p' hp => by
        simp only [Prod.mk.injEq, true_and, and_true] at hp
        exact Prod.ext hp.1 hp.2
    have hsub : ((G.interedges U W).image f₁ ∪ (Q₁ ×ˢ univ).image f₂) ∪
        (Q₂ ×ˢ univ).image f₃ ⊆ {x ∈ T | G.cubicMate 2 x ∉ T} := by
      intro x hx
      simp only [mem_union, mem_image, mem_interedges, mem_product, mem_univ, and_true,
        Prod.exists, f₁, f₂, f₃, U, W, Q₁, Q₂, mem_filter, true_and] at hx
      simp only [mem_filter]
      rcases hx with (⟨v, j, ⟨hv, hw⟩, rfl⟩ | ⟨v, j, hv, rfl⟩) | ⟨v, j, hv, rfl⟩
      · exact ⟨hv.1 _, by simpa using hw.2 _⟩
      · exact ⟨hv.1 _, by simpa using hv.2 _⟩
      · exact ⟨hv.2 _, by simpa using hv.1 _⟩
    have hd₁ : Disjoint ((G.interedges U W).image f₁) ((Q₁ ×ˢ univ).image f₂) := by
      simp only [disjoint_left, mem_image, f₁, f₂]
      rintro _ ⟨p, -, rfl⟩ ⟨p', -, h⟩
      simp at h
    have hd₂ : Disjoint ((G.interedges U W).image f₁ ∪ (Q₁ ×ˢ univ).image f₂)
        ((Q₂ ×ˢ univ).image f₃) := by
      simp only [disjoint_left, mem_union, mem_image, f₁, f₂, f₃]
      rintro _ (⟨p, -, rfl⟩ | ⟨p, -, rfl⟩) ⟨p', -, h⟩ <;> simp at h
    have := card_le_card hsub
    rw [card_union_of_disjoint hd₂, card_union_of_disjoint hd₁,
      card_image_of_injective _ (hinj _ _), card_image_of_injective _ (hinj _ _),
      card_image_of_injective _ (hinj _ _), card_product, card_product, card_univ,
      Fintype.card_fin] at this
    linarith [mul_comm (#Q₁) K, mul_comm (#Q₂) K]
  -- Counting points by clouds: both `U` and `W` are large unless many clouds are split.
  have hTU := card_le_cloudIn T
  have hTW := card_le_cloudIn Tᶜ
  simp only [compl_compl] at hTW
  have hP : #({q | ¬CloudIn Tᶜ q ∧ ¬CloudIn T q} : Finset (Bool × V)) = #P := by
    congr 1
    ext q
    simp only [P, mem_filter, mem_univ, true_and, and_comm]
  rw [hP] at hTW
  have hY := card_mixed_le T
  -- The edges of `G` leaving `U` either reach `W` or a vertex of `Y`.
  have hI : #(G.interedges U Uᶜ) ≤ #(G.interedges U W) + K * #Y := by
    have hsub : G.interedges U Uᶜ ⊆ G.interedges U W ∪ G.interedges univ Y := by
      intro p hp
      simp only [mem_interedges, mem_compl, mem_union, mem_univ, true_and] at hp ⊢
      by_cases hw : G.neighbor p.1 p.2 ∈ W
      · exact Or.inl ⟨hp.1, hw⟩
      · right
        simp only [U, W, Y, mem_filter, mem_univ, true_and] at hp hw ⊢
        exact ⟨hp.2, hw⟩
    have hY' : #(G.interedges univ Y) = K * #Y := by
      rw [card_interedges_comm, interedges, filter_true_of_mem (fun _ _ => mem_univ _),
        card_product, card_univ, Fintype.card_fin, mul_comm]
    exact (card_le_card hsub).trans ((card_union_le _ _).trans_eq (by rw [hY']))
  -- Edge expansion of `G` across the smaller of `U` and `Uᶜ ⊇ W`.
  have hWU : #W ≤ #Uᶜ := card_le_card fun v hv => by
    simp only [W, U, mem_filter, mem_univ, true_and, mem_compl] at hv ⊢
    exact fun hU => not_cloudIn_compl hU.1 hv.1
  have hE : h * #U ≤ #(G.interedges U Uᶜ) ∨ h * #W ≤ #(G.interedges U Uᶜ) := by
    rcases le_total (2 * #U) m with hU | hU
    · exact Or.inl ((mul_le_mul_of_nonneg_right hG (Nat.cast_nonneg _)).trans
        (G.edgeExpansion_mul_card_le hU))
    · right
      have hUc : 2 * #Uᶜ ≤ m := by rw [card_compl]; omega
      have := (mul_le_mul_of_nonneg_right hG (Nat.cast_nonneg _)).trans
        (G.edgeExpansion_mul_card_le hUc)
      rw [compl_compl, card_interedges_comm] at this
      exact (mul_le_mul_of_nonneg_left (Nat.cast_le.2 hWU) h₀).trans this
  -- The arithmetic.
  generalize #{x ∈ T | G.cubicMate 0 x ∉ T} = C₀ at *
  generalize #{x ∈ T | G.cubicMate 1 x ∉ T} = C₁ at *
  generalize #{x ∈ T | G.cubicMate 2 x ∉ T} = C₂ at *
  have hK₀ : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  have hK₁ : (1 : ℝ) ≤ K := by exact_mod_cast hK.le
  have hcT : (4 * K * m : ℝ) ≤ 3 * #T := by exact_mod_cast hT
  have hcTc : (4 * K * m : ℝ) ≤ 3 * #Tᶜ := by exact_mod_cast hTc
  have rTU : (#T : ℝ) ≤ 2 * K * (2 * #U + #Q₁ + #Q₂ + 2 * #P) := by exact_mod_cast hTU
  have rTW : (#Tᶜ : ℝ) ≤ 2 * K * (2 * #W + #Q₂ + #Q₁ + 2 * #P) := by exact_mod_cast hTW
  have rA : (#P : ℝ) ≤ C₀ + C₁ := by exact_mod_cast hA
  have rB : (#(G.interedges U W) + K * #Q₁ + K * #Q₂ : ℝ) ≤ C₂ := by exact_mod_cast hB
  have rY : (#Y : ℝ) ≤ #Q₁ + #Q₂ + #P := by exact_mod_cast hY
  have rI : (#(G.interedges U Uᶜ) : ℝ) ≤ #(G.interedges U W) + K * #Y := by exact_mod_cast hI
  have rE : h * #U ≤ #(G.interedges U Uᶜ) ∨ h * #W ≤ #(G.interedges U Uᶜ) := hE
  clear hT hTc hTU hTW hA hB hY hI hE hWU hP
  generalize (#(G.interedges U Uᶜ) : ℝ) = I at *
  have hJ : (0 : ℝ) ≤ #(G.interedges U W) := Nat.cast_nonneg _
  generalize (#(G.interedges U W) : ℝ) = J at *
  generalize (#U : ℝ) = u at *
  generalize (#W : ℝ) = w at *
  generalize (#Y : ℝ) = y at *
  generalize (#T : ℝ) = τ at *
  generalize (#Tᶜ : ℝ) = τ' at *
  have hq₁ : (0 : ℝ) ≤ #Q₁ := Nat.cast_nonneg _
  have hq₂ : (0 : ℝ) ≤ #Q₂ := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ #P := Nat.cast_nonneg _
  generalize (#Q₁ : ℝ) = q₁ at *
  generalize (#Q₂ : ℝ) = q₂ at *
  generalize (#P : ℝ) = p at *
  -- Every cut edge count is at least `t = q₁ + q₂ + p`.
  have hXt : q₁ + q₂ + p ≤ C₀ + C₁ + C₂ := by
    nlinarith [mul_le_mul_of_nonneg_right hK₁ hq₁, mul_le_mul_of_nonneg_right hK₁ hq₂]
  -- Both `U` and `W` have at least `m / 3 - t` vertices.
  have hKq : 0 ≤ K * (q₁ + q₂) := by positivity
  have hU : (m : ℝ) / 3 - (q₁ + q₂ + p) ≤ u := by
    have : 4 * K * (m : ℝ) ≤ 4 * K * (3 * u + 3 * (q₁ + q₂ + p)) := by nlinarith
    have := le_of_mul_le_mul_left this (by positivity)
    linarith
  have hW : (m : ℝ) / 3 - (q₁ + q₂ + p) ≤ w := by
    have : 4 * K * (m : ℝ) ≤ 4 * K * (3 * w + 3 * (q₁ + q₂ + p)) := by nlinarith
    have := le_of_mul_le_mul_left this (by positivity)
    linarith
  have hcross : h * (m / 3 - (q₁ + q₂ + p)) ≤ I := by
    rcases rE with hE | hE
    · exact (mul_le_mul_of_nonneg_left hU h₀).trans hE
    · exact (mul_le_mul_of_nonneg_left hW h₀).trans hE
  have hKY : K * y ≤ K * (q₁ + q₂ + p) := mul_le_mul_of_nonneg_left rY hK₀.le
  have h1 : h * (m / 3 - (q₁ + q₂ + p)) - K * (q₁ + q₂ + p) + (q₁ + q₂ + p) ≤
      C₀ + C₁ + C₂ := by
    nlinarith [mul_le_mul_of_nonneg_right hK₁ hq₁, mul_le_mul_of_nonneg_right hK₁ hq₂]
  have h2 : (h + K - 1) * (q₁ + q₂ + p) ≤ (h + K - 1) * (C₀ + C₁ + C₂) :=
    mul_le_mul_of_nonneg_left hXt (by linarith)
  have h3 : (0 : ℝ) ≤ C₀ + C₁ + C₂ := by linarith
  have hmain : h * m ≤ 3 * (h + K + 1) * (C₀ + C₁ + C₂) := by nlinarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  push_cast
  calc h * (4 * K * m) = 4 * K * (h * m) := by ring
    _ ≤ 4 * K * (3 * (h + K + 1) * (C₀ + C₁ + C₂)) := by gcongr
    _ = _ := by ring

/-! ### Explicit cubic expanders -/

omit [Fintype V] [DecidableEq V] in
/-- The arithmetic expanders have degree `2 ⋅ 257 ^ 12`. -/
theorem card_arithmeticExpanderLabel :
    Fintype.card (AffinePlaneFamilyLabel (ZMod 257) 257) = 2 * 257 ^ 12 :=
  card_affinePlaneFamilyLabel (ZMod.finEquiv 257).toEquiv.symm

/-- The cubic replacement (`cubicReplacement`) of the explicit arithmetic expander
`arithmeticExpander m`, with its labels numbered, on `Fin (8 ⋅ 257 ^ 12 ⋅ m)`. -/
noncomputable def cubicArithmeticExpander (m : ℕ) : CubicEdgeColoring (Fin (8 * 257 ^ 12 * m)) :=
  (((arithmeticExpander m).relabel (Fintype.equivFinOfCardEq card_arithmeticExpanderLabel)
    ).cubicReplacement (by norm_num)).map (Fintype.equivFinOfCardEq (by
      rw [card_cubicVertex, Fintype.card_fin]; ring))

/-- **Explicit cubic edge-coloured expanders.** There is `γ > 0` such that for every `m ≥ 2` the
simple cubic graph `cubicArithmeticExpander m` on `8 ⋅ 257 ^ 12 ⋅ m` vertices, which comes with a
proper `3`-edge-colouring, is a balanced-cut `γ`-edge expander. One can take
`γ = h / (12 K (h + K + 1))` with `K = 2 ⋅ 257 ^ 12` and `h = 9 / (800 ⋅ 257 ^ 16)`. -/
theorem isBalancedCutExpander_cubicArithmeticExpander :
    ∃ γ : ℝ, 0 < γ ∧ ∀ m, 2 ≤ m →
      IsBalancedCutExpander (cubicArithmeticExpander m).toSimpleGraph γ := by
  set K : ℕ := 2 * 257 ^ 12
  set h : ℝ := 9 / (800 * 257 ^ 16)
  refine ⟨h / (12 * K * (h + K + 1)), by positivity, fun m hm => ?_⟩
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  set G := (arithmeticExpander m).relabel (Fintype.equivFinOfCardEq card_arithmeticExpanderLabel)
  have hG : h ≤ G.edgeExpansion := by
    refine le_trans ?_ (le_edgeExpansion_of_spectralExpansion_le
      ((spectralExpansion_relabel _ _).trans_le (spectralExpansion_arithmeticExpander_le m)))
    simp only [h, Fintype.card_fin]
    have : (1 : ℝ) ≤ K := by norm_num [K]
    push_cast at this ⊢
    nlinarith
  exact (G.isBalancedCutExpander_cubicReplacement (by norm_num) (by positivity) hG).map _

/-- **Cubic edge-coloured expanders on unboundedly many vertex counts**: the part of
[ArenasBroadrickLiewVanDenBroeck2026, Proposition 5.2] used by their Theorem 1.1. There is
`γ > 0` such that for every `m` there are `n ≥ m` and a simple cubic graph on `Fin n` with a
proper `3`-edge-colouring that is a balanced-cut `γ`-edge expander. The graphs are
`cubicArithmeticExpander`; the proposition's polynomial-time construction for every even
`n ≥ 6` is not proved here. -/
theorem exists_cubicEdgeColoring_isBalancedCutExpander :
    ∃ γ : ℝ, 0 < γ ∧ ∀ m, ∃ n ≥ m, ∃ M : CubicEdgeColoring (Fin n),
      IsBalancedCutExpander M.toSimpleGraph γ := by
  obtain ⟨γ, hγ, h⟩ := isBalancedCutExpander_cubicArithmeticExpander
  refine ⟨γ, hγ, fun m => ⟨8 * 257 ^ 12 * (m + 2), by nlinarith, _, h _ (by omega)⟩⟩

end Cslib.RotationMap
