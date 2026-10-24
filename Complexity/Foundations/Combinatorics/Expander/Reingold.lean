/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Connected
public import Complexity.Foundations.Combinatorics.Expander.IteratedProd

/-!
# Reingold's transformation

Reingold's algorithm for undirected connectivity [Reingold][Reingold2008]
[Arora and Barak, Section 21.4][AroraBarak09] turns a regular graph into one in which every
connected component is an expander of constant degree, without merging components, by alternating
the zig-zag product with a fixed small expander `H` and squaring.

Let `H` be a regular multigraph on `B` with labels `E`, together with an equivalence
`e : B ≃ (Fin 2 → E × E)`, so that `H` has `|E| ^ 4` vertices and degree `|E|`. For a
`B`-regular graph `G` on `V`, the zig-zag product `G ⓩ H` is `E × E`-regular on `V × B`, and its
square is `Fin 2 → E × E`-regular, so `e.symm` renames its labels back to `B`:

`reingoldStep H e G = ((G ⓩ H) ^ 2).relabel e.symm`,

a `B`-regular graph on `V × B`. Starting from `G₀ = G`, `reingold H e G ℓ` is the graph
`G_ℓ = reingoldStep H e G_{ℓ - 1}`, on the vertices `IteratedProd V B ℓ = (⋯ (V × B) × ⋯) × B`.
Each vertex of `G_ℓ` lies over a vertex of `G`, its `root`.

**Spectral gap.** By the zig-zag theorem `λ(G ⓩ H) ≤ 1 - (1 - λ(G)) (1 - λ(H)) ^ 2`, so with
`λ(H) ≤ 1 / 5` a gap `γ = 1 - λ(G)` becomes at least `1 - (1 - 16 γ / 25) ^ 2`
(`spectralExpansion_reingoldStep_le`), which is at least `min (6 γ / 5) (1 / 5)`
(`min_le_one_sub_spectralExpansion_reingoldStep`). After `ℓ` steps the gap is at least
`min ((6 / 5) ^ ℓ γ) (1 / 5)` (`min_pow_le_one_sub_spectralExpansion_reingold`). Reingold takes
the eighth power of `G ⓩ H`, for a `D`-regular base graph on `D ^ 16` vertices with
`λ(H) ≤ 1 / 2`, and obtains `λ ↦ max (λ ^ 2) (1 / 2)` in the proof of
[Reingold, Lemma 3.2][Reingold2008]; taking
the square, with the base graph of the zig-zag tower, the gap grows by the factor `6 / 5` instead,
which changes only the constant in the number of steps.

**Components.** The transformation is natural for homomorphisms (`Cslib.RotationMap.Hom.reingold`),
so it acts separately on each connected component [Reingold, Lemma 3.3][Reingold2008]: the
transform of the connected component of `s` maps into the transform of `G`, onto the vertices over
that component. A walk in `G_ℓ` stays over one component of `G`
(`reachable_root_neighbor_pow_reingold`). If at least half of the edges at every vertex of `G` are
self-loops, a connected component on `N ≤ |V|` vertices has spectral gap at least
`1 / (2 N² |B|²)`, so once `2 |V|² |B|² 5 ^ ℓ ≤ 5 · 6 ^ ℓ` the transform of every component is an
expander with `λ ≤ 4 / 5`, on at most `|V| |B| ^ ℓ` vertices. Walks of length `T` then reach
every vertex over the component as soon as `|V| |B| ^ ℓ 4 ^ T ≤ 5 ^ T`
(`exists_neighbor_pow_reingold_eq`). Hence (`reachable_iff_exists_root_neighbor_pow_reingold`):
`t` is reachable from `s` in `G` exactly when some walk of length `T` in `G_ℓ` from a vertex over
`s` ends over `t`. Both `ℓ` and `T` are `O(log |V|)` when `|B|` is a constant.

## Main definitions

* `Cslib.RotationMap.reingoldStep`: one step `((G ⓩ H) ^ 2).relabel e.symm` of the
  transformation.
* `Cslib.RotationMap.reingold`: the graphs `G_ℓ`, on the iterated products
  `Cslib.IteratedProd V B ℓ`.

## Main results

* `Cslib.RotationMap.min_le_one_sub_spectralExpansion_reingoldStep`,
  `Cslib.RotationMap.min_pow_le_one_sub_spectralExpansion_reingold`: the spectral gap grows
  geometrically until it reaches `1 / 5`.
* `Cslib.RotationMap.reachable_root_neighbor_pow_reingold`: walks in `G_ℓ` stay over a connected
  component of `G`.
* `Cslib.RotationMap.exists_neighbor_pow_reingold_eq`: short walks in `G_ℓ` reach every vertex
  over the connected component of the start.
* `Cslib.RotationMap.reachable_iff_exists_root_neighbor_pow_reingold`: connectivity in `G` is
  decided by the walks of length `T` in `G_ℓ` from one vertex.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

universe u


variable {B : Type u} {E : Type*} (H : RotationMap B E) (e : B ≃ (Fin 2 → E × E))

/-- **One step of Reingold's transformation**, a variant of [Reingold, Definition 3.1][Reingold2008]
[Arora and Barak, Section 21.4][AroraBarak09] with the square instead of the eighth power: the
square of the zig-zag product of a `B`-regular graph `G` with the graph `H` on `B`, whose labels
`Fin 2 → E × E` are renamed back to `B` by `e.symm`. -/
def reingoldStep {V : Type*} (G : RotationMap V B) : RotationMap (V × B) B :=
  ((G.zigzag H).pow 2).relabel e.symm

/-- **Reingold's transformation**, a variant of [Reingold, Definition 3.1][Reingold2008] with the
square instead of the eighth power: `reingold H e G ℓ` is the graph `G_ℓ` obtained from `G₀ = G`
by `ℓ` steps `G_{i + 1} = ((G_i ⓩ H) ^ 2).relabel e.symm`. -/
def reingold {V : Type u} (G : RotationMap V B) : (ℓ : ℕ) → RotationMap (IteratedProd V B ℓ) B
  | 0 => G
  | ℓ + 1 => reingoldStep H e (reingold G ℓ)

/-- The graph `G₀` is the original graph. -/
@[simp]
theorem reingold_zero {V : Type u} (G : RotationMap V B) : reingold H e G 0 = G :=
  rfl

/-- Each graph of the transformation is a step of the transformation from the previous one. -/
theorem reingold_succ {V : Type u} (G : RotationMap V B) (ℓ : ℕ) :
    reingold H e G (ℓ + 1) = reingoldStep H e (reingold H e G ℓ) :=
  rfl

/-- **Reingold's transformation is natural**: a homomorphism of graphs induces homomorphisms of
their transforms, acting on the roots. -/
def Hom.reingold {V W : Type u} {G : RotationMap V B} {G' : RotationMap W B} (φ : Hom G G') :
    (ℓ : ℕ) → Hom (RotationMap.reingold H e G ℓ) (RotationMap.reingold H e G' ℓ)
  | 0 => φ
  | ℓ + 1 => (((φ.reingold ℓ).zigzag H).pow 2).relabel e.symm

/-- The homomorphism of the transforms applies the homomorphism to the root. -/
theorem Hom.reingold_apply {V W : Type u} {G : RotationMap V B} {G' : RotationMap W B}
    (φ : Hom G G') (ℓ : ℕ) (x : IteratedProd V B ℓ) :
    φ.reingold H e ℓ x = IteratedProd.map φ ℓ x := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => exact Prod.ext (ih x.1) rfl

section Projection

/-- Every edge of `G_ℓ` joins two vertices over vertices of `G` reachable from each other. -/
private theorem reachable_root_neighbor_reingold {V : Type u} (G : RotationMap V B) :
    ∀ (ℓ : ℕ) (x : IteratedProd V B ℓ) (i : B),
      G.toSimpleGraph.Reachable x.root ((reingold H e G ℓ).neighbor x i).root
  | 0, x, i => G.reachable_neighbor x i
  | ℓ + 1, x, i =>
    reachable_neighbor_pow_of_forall G ((reingold H e G ℓ).zigzag H)
      (fun p ↦ IteratedProd.root p.1)
      (fun p _ ↦ reachable_root_neighbor_reingold G ℓ p.1 _) 2 x (e i)

/-- **Walks in `G_ℓ` stay over a connected component of `G`**: the walk of length `T` from any
vertex of `G_ℓ` ends over a vertex reachable in `G` from the root of the start. -/
theorem reachable_root_neighbor_pow_reingold {V : Type u} (G : RotationMap V B) (ℓ T : ℕ)
    (x : IteratedProd V B ℓ) (k : Fin T → B) :
    G.toSimpleGraph.Reachable x.root (((reingold H e G ℓ).pow T).neighbor x k).root :=
  reachable_neighbor_pow_of_forall G (reingold H e G ℓ) IteratedProd.root
    (reachable_root_neighbor_reingold H e G ℓ) T x k

end Projection

section Spectral

variable [Fintype B] [Fintype E]

/-- One step of the transformation turns the spectral gap `1 - λ(G)` into at least
`1 - (1 - (1 - λ(G)) (1 - λ(H)) ^ 2) ^ 2`, by the zig-zag theorem. -/
theorem spectralExpansion_reingoldStep_le {V : Type*} [Fintype V] (G : RotationMap V B) :
    (reingoldStep H e G).spectralExpansion ≤
      (1 - (1 - G.spectralExpansion) * (1 - H.spectralExpansion) ^ 2) ^ 2 := by
  rw [reingoldStep, spectralExpansion_relabel]
  exact ((G.zigzag H).spectralExpansion_pow_le 2).trans
    (pow_le_pow_left₀ (spectralExpansion_nonneg _) (G.spectralExpansion_zigzag_le_one_sub H) 2)

/-- **The spectral gap grows**, as in the proof of [Reingold, Lemma 3.2][Reingold2008]: if
`λ(H) ≤ 1 / 5` and the
spectral gap of `G` is at least `γ ≥ 0`, one step of the transformation has spectral gap at least
`min (6 γ / 5) (1 / 5)`. -/
theorem min_le_one_sub_spectralExpansion_reingoldStep {V : Type*} [Fintype V]
    (hH : H.spectralExpansion ≤ 1 / 5) (G : RotationMap V B) {γ : ℝ} (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤ 1 - G.spectralExpansion) :
    min (6 / 5 * γ) (1 / 5) ≤ 1 - (reingoldStep H e G).spectralExpansion := by
  have hμ₀ := G.spectralExpansion_nonneg
  have hμ₁ := G.spectralExpansion_le_one
  have hν₀ := H.spectralExpansion_nonneg
  set x := (1 - G.spectralExpansion) * (1 - H.spectralExpansion) ^ 2 with hx
  have hν : (16 / 25 : ℝ) ≤ (1 - H.spectralExpansion) ^ 2 := by nlinarith
  have hx₁ : x ≤ 1 :=
    (mul_le_mul (by linarith) (pow_le_one₀ (by linarith) (by linarith)) (sq_nonneg _)
      zero_le_one).trans_eq (one_mul 1)
  have hxγ : 16 / 25 * γ ≤ x := by
    rw [hx]
    calc 16 / 25 * γ ≤ (1 - H.spectralExpansion) ^ 2 * γ :=
          mul_le_mul_of_nonneg_right hν hγ₀
      _ ≤ (1 - H.spectralExpansion) ^ 2 * (1 - G.spectralExpansion) :=
          mul_le_mul_of_nonneg_left hγ (sq_nonneg _)
      _ = _ := mul_comm _ _
  have hstep : (reingoldStep H e G).spectralExpansion ≤ (1 - 16 / 25 * γ) ^ 2 :=
    (spectralExpansion_reingoldStep_le H e G).trans
      (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  have hγ₁ : γ ≤ 1 := by linarith
  rcases le_total γ (1 / 6) with h | h
  · refine (min_le_left _ _).trans ?_
    nlinarith
  · refine (min_le_right _ _).trans ?_
    nlinarith

/-- **The spectral gap grows geometrically** [Reingold, Lemma 3.2][Reingold2008]: if `λ(H) ≤ 1 / 5`
and the spectral gap of `G` is at least `γ ≥ 0`, the `ℓ`-th graph of the transformation has spectral
gap at least `min ((6 / 5) ^ ℓ γ) (1 / 5)`. -/
theorem min_pow_le_one_sub_spectralExpansion_reingold {V : Type u} [Fintype V]
    (hH : H.spectralExpansion ≤ 1 / 5) (G : RotationMap V B) {γ : ℝ} (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤ 1 - G.spectralExpansion) (ℓ : ℕ) :
    min ((6 / 5) ^ ℓ * γ) (1 / 5) ≤ 1 - (reingold H e G ℓ).spectralExpansion := by
  induction ℓ with
  | zero =>
    rw [pow_zero, one_mul]
    exact (min_le_left _ _).trans hγ
  | succ ℓ ih =>
    have h₀ : 0 ≤ min ((6 / 5) ^ ℓ * γ) (1 / 5) := le_min (by positivity) (by norm_num)
    refine le_trans ?_ (min_le_one_sub_spectralExpansion_reingoldStep H e hH _ h₀ ih)
    refine le_min ?_ (min_le_right _ _)
    rcases le_total ((6 / 5) ^ ℓ * γ) (1 / 5) with h | h
    · rw [min_eq_left h, pow_succ]
      exact (min_le_left _ _).trans_eq (by ring)
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (by norm_num)

end Spectral

section Main

variable [Fintype B] [Fintype E] [Nonempty B]

/-- **Short walks in `G_ℓ` reach the whole component** [Reingold, Lemmas 3.2 and 3.3 and
Proposition 2.2][Reingold2008]: if
`λ(H) ≤ 1 / 5`, at least half of the edges at every vertex of `G` are self-loops,
`2 |V|² |B|² 5 ^ ℓ ≤ 5 · 6 ^ ℓ` and `|V| |B| ^ ℓ 4 ^ T ≤ 5 ^ T`, then for any two vertices `x` and
`y` of `G_ℓ` over vertices reachable from each other in `G`, some walk of length exactly `T` leads
from `x` to `y`. The transform of the connected component of the root of `x` is an expander with
`λ ≤ 4 / 5` on at most `|V| |B| ^ ℓ` vertices, and it maps into `G_ℓ`. -/
theorem exists_neighbor_pow_reingold_eq {V : Type u} [Fintype V] [DecidableEq V]
    (hH : H.spectralExpansion ≤ 1 / 5) (G : RotationMap V B)
    (hG : ∀ v, Fintype.card B ≤ 2 * G.edgeCount v v) {ℓ T : ℕ}
    (hℓ : 2 * Fintype.card V ^ 2 * Fintype.card B ^ 2 * 5 ^ ℓ ≤ 5 * 6 ^ ℓ)
    (hT : Fintype.card V * Fintype.card B ^ ℓ * 4 ^ T ≤ 5 ^ T)
    {x y : IteratedProd V B ℓ} (hxy : G.toSimpleGraph.Reachable x.root y.root) :
    ∃ k : Fin T → B, ((reingold H e G ℓ).pow T).neighbor x k = y := by
  classical
  have : Nonempty V := ⟨x.root⟩
  set C := {v | G.toSimpleGraph.Reachable x.root v}
  have hxC : x.root ∈ C := SimpleGraph.Reachable.refl _
  -- the spectral gap of the component
  have hR : ∀ v, Fintype.card B ≤ 2 * (G.componentGraph x.root).edgeCount v v := fun v ↦ by
    simpa using hG v
  have hCV : Fintype.card C ≤ Fintype.card V := Fintype.card_subtype_le _
  have hC : 0 < Fintype.card C := Fintype.card_pos_iff.2 ⟨⟨x.root, hxC⟩⟩
  have hB : 0 < Fintype.card B := Fintype.card_pos
  set γ : ℝ := 1 / (2 * Fintype.card V ^ 2 * Fintype.card B ^ 2) with hγdef
  have hγ₀ : 0 ≤ γ := by positivity
  have hγ : γ ≤ 1 - (G.componentGraph x.root).spectralExpansion := by
    refine le_trans ?_ (sub_le_sub_left
      ((G.componentGraph x.root).spectralExpansion_le_of_preconnected hR
        (G.preconnected_componentGraph x.root)) 1)
    rw [sub_sub_cancel, hγdef]
    have : (Fintype.card C : ℝ) ≤ Fintype.card V := by exact_mod_cast hCV
    gcongr
  -- after `ℓ` steps it is at least `1 / 5`
  have hgap := min_pow_le_one_sub_spectralExpansion_reingold H e hH _ hγ₀ hγ ℓ
  have hℓ' : (1 / 5 : ℝ) ≤ (6 / 5) ^ ℓ * γ := by
    have hcast : (2 * Fintype.card V ^ 2 * Fintype.card B ^ 2 * 5 ^ ℓ : ℝ) ≤ 5 * 6 ^ ℓ := by
      exact_mod_cast hℓ
    have e₁ : (6 / 5 : ℝ) ^ ℓ * γ =
        6 ^ ℓ / (5 ^ ℓ * (2 * Fintype.card V ^ 2 * Fintype.card B ^ 2)) := by
      rw [hγdef, div_pow]
      field_simp
    rw [e₁, le_div_iff₀ (by positivity)]
    linarith
  rw [min_eq_right hℓ'] at hgap
  have hlam : (reingold H e (G.componentGraph x.root) ℓ).spectralExpansion ≤ 4 / 5 := by linarith
  -- so walks of length `T` reach every vertex of the transform of the component
  have hwalk : (reingold H e (G.componentGraph x.root) ℓ).spectralExpansion ^ T *
      (Fintype.card (IteratedProd C B ℓ) - 1) < 1 := by
    rw [IteratedProd.card]
    have hM : (1 : ℝ) ≤ Fintype.card C * Fintype.card B ^ ℓ := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hC.ne' (pow_pos hB ℓ).ne')
    have hMV : (Fintype.card C * Fintype.card B ^ ℓ : ℝ) * 4 ^ T ≤ 5 ^ T := by
      have : (Fintype.card C * Fintype.card B ^ ℓ * 4 ^ T : ℝ) ≤
          Fintype.card V * Fintype.card B ^ ℓ * 4 ^ T := by gcongr
      exact this.trans (by exact_mod_cast hT)
    have hlam₀ := (reingold H e (G.componentGraph x.root) ℓ).spectralExpansion_nonneg
    push_cast
    calc (reingold H e (G.componentGraph x.root) ℓ).spectralExpansion ^ T *
          ((Fintype.card C : ℝ) * Fintype.card B ^ ℓ - 1) ≤
          (4 / 5) ^ T * ((Fintype.card C : ℝ) * Fintype.card B ^ ℓ - 1) := by
          gcongr
      _ < (4 / 5) ^ T * ((Fintype.card C : ℝ) * Fintype.card B ^ ℓ) := by
          gcongr
          linarith
      _ ≤ 1 := by
          rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)]
          linarith
  obtain ⟨k, hk⟩ := (reingold H e (G.componentGraph x.root) ℓ).exists_neighbor_pow_eq hwalk
    (x.setRoot (⟨x.root, hxC⟩ : C)) (y.setRoot (⟨y.root, hxy⟩ : C))
  refine ⟨k, ?_⟩
  have h := (((G.componentHom x.root).reingold H e ℓ).pow T).neighbor_map
    (x.setRoot (⟨x.root, hxC⟩ : C)) k
  simp only [Hom.pow_apply, Hom.reingold_apply, hk, IteratedProd.map_setRoot, componentHom_apply,
    IteratedProd.setRoot_root] at h
  exact h

/-- **Undirected connectivity by short walks in Reingold's transform** [Reingold][Reingold2008]
[Arora and Barak, Section 21.4][AroraBarak09]: if `λ(H) ≤ 1 / 5`, at least half of the edges at
every vertex of `G` are self-loops, `2 |V|² |B|² 5 ^ ℓ ≤ 5 · 6 ^ ℓ` and
`|V| |B| ^ ℓ 4 ^ T ≤ 5 ^ T`, then `t` is reachable from `s` in `G` exactly when some walk of length
`T` in `G_ℓ` from the vertex `(⋯ (s, b) ⋯, b)` ends over `t`. -/
theorem reachable_iff_exists_root_neighbor_pow_reingold {V : Type u} [Fintype V] [DecidableEq V]
    (hH : H.spectralExpansion ≤ 1 / 5) (G : RotationMap V B)
    (hG : ∀ v, Fintype.card B ≤ 2 * G.edgeCount v v) {ℓ T : ℕ}
    (hℓ : 2 * Fintype.card V ^ 2 * Fintype.card B ^ 2 * 5 ^ ℓ ≤ 5 * 6 ^ ℓ)
    (hT : Fintype.card V * Fintype.card B ^ ℓ * 4 ^ T ≤ 5 ^ T) (s t : V) (b : B) :
    G.toSimpleGraph.Reachable s t ↔
      ∃ k : Fin T → B,
        (((reingold H e G ℓ).pow T).neighbor (IteratedProd.mk s b ℓ) k).root = t := by
  refine ⟨fun h ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · obtain ⟨k, hk⟩ := exists_neighbor_pow_reingold_eq H e hH G hG hℓ hT
      (x := IteratedProd.mk s b ℓ) (y := IteratedProd.mk t b ℓ) (by simpa using h)
    exact ⟨k, by rw [hk, IteratedProd.root_mk]⟩
  · simpa [hk] using reachable_root_neighbor_pow_reingold H e G ℓ T (IteratedProd.mk s b ℓ) k

end Main

end Cslib.RotationMap
