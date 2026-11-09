/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Loops
public import CslibFrontier.Foundations.Combinatorics.Expander.Power
public import CslibFrontier.Foundations.Combinatorics.Expander.Zigzag
public import CslibFrontier.Foundations.Combinatorics.Expander.SimpleGraph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Homomorphisms and restrictions of rotation maps

A homomorphism `φ : G.Hom G'` between two rotation maps with the same labels is a map of the
vertices under which the rotation map of `G'` follows that of `G`, label by label: the `i`-th
edge at `φ v` in `G'` is the image of the `i`-th edge at `v` in `G`, and it arrives with the same
label. So `φ` maps the walk of `G` from `v` along any labels to the walk of `G'` from `φ v` along
the same labels (`Cslib.RotationMap.Hom.neighbor_pow_map`): the walks of `G'` from `φ v` are
exactly the images of the walks of `G` from `v`, and every vertex reachable from `φ v` is the image
of a vertex reachable from `v` (`Cslib.RotationMap.Hom.exists_reachable_apply_eq`). Homomorphisms
are compatible with powers, relabelling and zig-zag products, so a graph product of an image is the
image of the product.

The basic example is the restriction `G.restrict S hS` of `G` to a set `S` of vertices closed under
taking neighbors, such as the set of the vertices reachable from a given vertex
(`Cslib.RotationMap.componentGraph`), with the inclusion `G.restrictHom S hS` into `G`. Reingold's
algorithm for undirected connectivity [Reingold][Reingold2008] transforms a graph by powers and
zig-zag products, and its analysis runs on the connected component of the start vertex: the
transform of the component maps into the transform of the graph, so walks in one are walks in the
other.

## Main definitions

* `Cslib.RotationMap.Hom`: homomorphisms of rotation maps with the same labels.
* `Cslib.RotationMap.Hom.id`, `Cslib.RotationMap.Hom.comp`: the identity homomorphism and the
  composition of homomorphisms.
* `Cslib.RotationMap.Hom.pow`, `Cslib.RotationMap.Hom.relabel`, `Cslib.RotationMap.Hom.zigzag`:
  the induced homomorphisms of powers, relabellings and zig-zag products.
* `Cslib.RotationMap.restrict`, `Cslib.RotationMap.restrictHom`: the restriction to a set of
  vertices closed under taking neighbors, and its inclusion.
* `Cslib.RotationMap.componentGraph`: the restriction to the vertices reachable from a vertex.
* `Cslib.RotationMap.componentHom`: the inclusion of that restriction into the graph.

## Main results

* `Cslib.RotationMap.Hom.neighbor_map`, `Cslib.RotationMap.Hom.neighbor_pow_map`: homomorphisms
  map neighbors to neighbors and walks to walks along the same labels.
* `Cslib.RotationMap.reachable_neighbor`: every neighbor of a vertex is reachable from it.
* `Cslib.RotationMap.Hom.reachable_map`, `Cslib.RotationMap.Hom.exists_reachable_apply_eq`,
  `Cslib.RotationMap.Hom.reachable_apply_iff`: homomorphisms map reachable vertices to reachable
  vertices, and lift the walks from the image of a vertex.
* `Cslib.RotationMap.mem_of_reachable`: a set closed under taking neighbors contains every vertex
  reachable from it.
* `Cslib.RotationMap.preconnected_componentGraph`, `Cslib.RotationMap.edgeCount_componentGraph`:
  the restriction to the vertices reachable from a vertex is connected and preserves edge
  multiplicities.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
-/

@[expose] public section

namespace Cslib.RotationMap

variable {V W X D E : Type*}

/-- A **homomorphism** from `G` to `G'`, rotation maps with the same labels: a map of the vertices
under which the rotation map of `G'` follows that of `G`. The `i`-th edge at `φ v` in `G'` is the
image of the `i`-th edge at `v` in `G`, and it arrives with the same label. -/
structure Hom (G : RotationMap V D) (G' : RotationMap W D) where
  /-- The map of the vertices. -/
  toFun : V → W
  /-- The rotation map of `G'` at the image of a dart is the image of the rotation map of `G`. -/
  rot_map' (v : V) (i : D) : G'.rot (toFun v, i) = Prod.map toFun id (G.rot (v, i))

namespace Hom

variable {G : RotationMap V D} {G' : RotationMap W D} {G'' : RotationMap X D}

/-- A homomorphism of rotation maps coerces to its map of the vertices. -/
instance : FunLike (Hom G G') V W where
  coe := toFun
  coe_injective φ ψ h := by
    cases φ
    cases ψ
    congr

/-- The underlying map of a homomorphism is its coercion to a function. -/
@[simp]
theorem toFun_eq_coe (φ : Hom G G') : φ.toFun = φ :=
  rfl

/-- The rotation map of `G'` at the image of a dart is the image of the rotation map of `G`. -/
theorem rot_map (φ : Hom G G') (v : V) (i : D) :
    G'.rot (φ v, i) = Prod.map φ id (G.rot (v, i)) :=
  φ.rot_map' v i

/-- A homomorphism maps the `i`-th neighbor of `v` to the `i`-th neighbor of the image of `v`. -/
theorem neighbor_map (φ : Hom G G') (v : V) (i : D) : G'.neighbor (φ v) i = φ (G.neighbor v i) :=
  congrArg Prod.fst (φ.rot_map v i)

/-- Homomorphisms with the same map of the vertices are equal. -/
@[ext]
theorem ext {φ ψ : Hom G G'} (h : ∀ v, φ v = ψ v) : φ = ψ :=
  DFunLike.ext _ _ h

/-- The identity homomorphism. -/
protected def id (G : RotationMap V D) : Hom G G where
  toFun := id
  rot_map' _ _ := rfl

/-- The identity homomorphism is the identity map. -/
@[simp]
theorem coe_id (G : RotationMap V D) : ⇑(Hom.id G) = id :=
  rfl

/-- The identity homomorphism fixes every vertex. -/
theorem id_apply (G : RotationMap V D) (v : V) : Hom.id G v = v :=
  rfl

/-- The composition of homomorphisms. -/
def comp (ψ : Hom G' G'') (φ : Hom G G') : Hom G G'' where
  toFun := ψ ∘ φ
  rot_map' v i := by
    change G''.rot (ψ (φ v), i) = _
    rw [ψ.rot_map, φ.rot_map, Prod.map_map]
    rfl

/-- The composition of homomorphisms applies them in turn. -/
@[simp]
theorem comp_apply (ψ : Hom G' G'') (φ : Hom G G') (v : V) : ψ.comp φ v = ψ (φ v) :=
  rfl

/-- A homomorphism maps walks to walks: the rotation map of the walks of length `t` follows it. -/
theorem powRot_map (φ : Hom G G') :
    ∀ (t : ℕ) (v : V) (k : Fin t → D),
      powRot G'.rot t (φ v, k) = Prod.map φ id (powRot G.rot t (v, k))
  | 0, _, _ => rfl
  | t + 1, v, k => by
    rw [powRot_succ, powRot_succ, φ.rot_map, Prod.map_fst, Prod.map_snd, id_eq, powRot_map φ t]
    rfl

/-- A homomorphism of rotation maps is a homomorphism of their `t`-th powers. -/
def pow (φ : Hom G G') (t : ℕ) : Hom (G.pow t) (G'.pow t) where
  toFun := φ
  rot_map' := φ.powRot_map t

/-- The homomorphism of the powers is the same map of the vertices. -/
@[simp]
theorem pow_apply (φ : Hom G G') (t : ℕ) (v : V) : φ.pow t v = φ v :=
  rfl

/-- A homomorphism maps the walk from `v` along `k` to the walk from `φ v` along `k`. -/
theorem neighbor_pow_map (φ : Hom G G') (t : ℕ) (v : V) (k : Fin t → D) :
    (G'.pow t).neighbor (φ v) k = φ ((G.pow t).neighbor v k) :=
  (φ.pow t).neighbor_map v k

/-- A homomorphism of rotation maps is a homomorphism of their relabellings. -/
def relabel (φ : Hom G G') (e : D ≃ E) : Hom (G.relabel e) (G'.relabel e) where
  toFun := φ
  rot_map' v i := by
    rw [rot_relabel, rot_relabel, φ.rot_map]
    rfl

/-- The homomorphism of the relabellings is the same map of the vertices. -/
@[simp]
theorem relabel_apply (φ : Hom G G') (e : D ≃ E) (v : V) : φ.relabel e v = φ v :=
  rfl

/-- A homomorphism of rotation maps with labels `D` induces a homomorphism of their zig-zag
products with a graph `H` on `D`, acting on the first coordinate. -/
def zigzag (φ : Hom G G') (H : RotationMap D E) : Hom (G.zigzag H) (G'.zigzag H) where
  toFun := Prod.map φ id
  rot_map' p i := by
    obtain ⟨v, k⟩ := p
    obtain ⟨i, j⟩ := i
    change (G'.zigzag H).rot ((φ v, k), (i, j)) = _
    rw [rot_zigzag, rot_zigzag, φ.rot_map]
    rfl

/-- The homomorphism of the zig-zag products maps the vertex `(v, k)` to `(φ v, k)`. -/
@[simp]
theorem zigzag_apply (φ : Hom G G') (H : RotationMap D E) (p : V × D) :
    φ.zigzag H p = (φ p.1, p.2) :=
  rfl

end Hom

section Restrict

variable (G : RotationMap V D)

/-- The **restriction** of `G` to a set `S` of vertices closed under taking neighbors: the
rotation map of `G` on the darts at the vertices of `S`. -/
def restrict (S : Set V) (hS : ∀ v ∈ S, ∀ i, G.neighbor v i ∈ S) : RotationMap S D where
  rot p := (⟨G.neighbor p.1 p.2, hS _ p.1.2 _⟩, (G.rot (p.1, p.2)).2)
  rot_involutive p := by
    refine Prod.ext (Subtype.ext ?_) ?_
    · exact G.neighbor_neighbor_rot p.1 p.2
    · change (G.rot ((G.rot (p.1.1, p.2)).1, (G.rot (p.1.1, p.2)).2)).2 = p.2
      rw [Prod.mk.eta, rot_rot]

/-- The rotation map of a restriction of `G` is the rotation map of `G`. -/
@[simp]
theorem rot_restrict (S : Set V) (hS : ∀ v ∈ S, ∀ i, G.neighbor v i ∈ S) (p : S × D) :
    (G.restrict S hS).rot p = (⟨G.neighbor p.1 p.2, hS p.1 p.1.2 p.2⟩, (G.rot (p.1, p.2)).2) :=
  rfl

/-- The inclusion of a restriction of `G` into `G` is a homomorphism. -/
def restrictHom (S : Set V) (hS : ∀ v ∈ S, ∀ i, G.neighbor v i ∈ S) : Hom (G.restrict S hS) G where
  toFun := Subtype.val
  rot_map' _ _ := rfl

/-- The inclusion of a restriction maps a vertex to itself. -/
@[simp]
theorem restrictHom_apply (S : Set V) (hS : ∀ v ∈ S, ∀ i, G.neighbor v i ∈ S) (v : S) :
    G.restrictHom S hS v = v :=
  rfl

/-- The neighbors in a restriction are the neighbors in `G`. -/
@[simp]
theorem coe_neighbor_restrict (S : Set V) (hS : ∀ v ∈ S, ∀ i, G.neighbor v i ∈ S) (v : S) (i : D) :
    ((G.restrict S hS).neighbor v i : V) = G.neighbor v i :=
  rfl

/-- A restriction of `G` has the same edge multiplicities as `G`. -/
@[simp]
theorem edgeCount_restrict [DecidableEq V] [Fintype D] (S : Set V)
    (hS : ∀ v ∈ S, ∀ i, G.neighbor v i ∈ S) (v u : S) :
    (G.restrict S hS).edgeCount v u = G.edgeCount v u := by
  simp only [edgeCount, Subtype.ext_iff, coe_neighbor_restrict]

end Restrict

section Reachable

variable (G : RotationMap V D)

/-- Every neighbor of a vertex is reachable from it in the simple graph of `G`. -/
theorem reachable_neighbor (v : V) (i : D) : G.toSimpleGraph.Reachable v (G.neighbor v i) := by
  by_cases h : v = G.neighbor v i
  · rw [← h]
  · exact SimpleGraph.Adj.reachable ⟨h, i, rfl⟩

variable {G} {G' : RotationMap W D}

/-- A homomorphism maps reachable vertices to reachable vertices. -/
theorem Hom.reachable_map (φ : Hom G G') {u v : V} (h : G.toSimpleGraph.Reachable u v) :
    G'.toSimpleGraph.Reachable (φ u) (φ v) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hxy ih =>
    obtain ⟨-, i, rfl⟩ := hxy
    exact ih.trans (φ.neighbor_map _ i ▸ G'.reachable_neighbor _ i)

/-- **Lifting walks along a homomorphism**: every vertex reachable from the image of `u` is the
image of a vertex reachable from `u`. -/
theorem Hom.exists_reachable_apply_eq (φ : Hom G G') {u : V} {w : W}
    (h : G'.toSimpleGraph.Reachable (φ u) w) : ∃ v, G.toSimpleGraph.Reachable u v ∧ φ v = w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ⟨u, .refl u, rfl⟩
  | tail _ hxy ih =>
    obtain ⟨v, huv, rfl⟩ := ih
    obtain ⟨-, i, rfl⟩ := hxy
    exact ⟨G.neighbor v i, huv.trans (G.reachable_neighbor v i), (φ.neighbor_map v i).symm⟩

/-- Along an injective homomorphism, the images of two vertices are reachable from each other
exactly when the vertices are. -/
theorem Hom.reachable_apply_iff (φ : Hom G G') (hφ : Function.Injective φ) {u v : V} :
    G'.toSimpleGraph.Reachable (φ u) (φ v) ↔ G.toSimpleGraph.Reachable u v := by
  refine ⟨fun h ↦ ?_, φ.reachable_map⟩
  obtain ⟨v', huv', hv'⟩ := φ.exists_reachable_apply_eq h
  exact hφ hv' ▸ huv'

/-- If every edge of `G'` joins vertices whose images under `π` are reachable from each other in
`G`, so does every walk. -/
theorem reachable_neighbor_pow_of_forall {D' : Type*} (G : RotationMap V D)
    (G' : RotationMap W D') (π : W → V)
    (hπ : ∀ x i, G.toSimpleGraph.Reachable (π x) (π (G'.neighbor x i))) :
    ∀ (t : ℕ) (x : W) (k : Fin t → D'),
      G.toSimpleGraph.Reachable (π x) (π ((G'.pow t).neighbor x k))
  | 0, _, _ => .refl _
  | t + 1, x, k => (hπ x (k 0)).trans (reachable_neighbor_pow_of_forall G G' π hπ t _ _)

variable (G)

/-- A set of vertices closed under taking neighbors contains every vertex reachable from it. -/
theorem mem_of_reachable {S : Set V} (hS : ∀ v ∈ S, ∀ i, G.neighbor v i ∈ S) {u v : V}
    (hu : u ∈ S) (h : G.toSimpleGraph.Reachable u v) : v ∈ S := by
  obtain ⟨w, -, rfl⟩ := (G.restrictHom S hS).exists_reachable_apply_eq (u := ⟨u, hu⟩) h
  exact w.2

/-- The vertices reachable from `s` are closed under taking neighbors. -/
theorem neighbor_mem_setOf_reachable (s : V) :
    ∀ v ∈ {v | G.toSimpleGraph.Reachable s v}, ∀ i,
      G.neighbor v i ∈ {v | G.toSimpleGraph.Reachable s v} :=
  fun v hv i ↦ (hv : G.toSimpleGraph.Reachable s v).trans (G.reachable_neighbor v i)

/-- The **connected component** of `s` in `G`, as a rotation map: the restriction of `G` to the
vertices reachable from `s`. -/
def componentGraph (s : V) : RotationMap {v | G.toSimpleGraph.Reachable s v} D :=
  G.restrict _ (G.neighbor_mem_setOf_reachable s)

/-- The inclusion of the connected component of `s` into `G`. -/
def componentHom (s : V) : Hom (G.componentGraph s) G :=
  G.restrictHom _ (G.neighbor_mem_setOf_reachable s)

/-- The inclusion of the connected component of `s` maps a vertex to itself. -/
@[simp]
theorem componentHom_apply (s : V) (v : {v | G.toSimpleGraph.Reachable s v}) :
    G.componentHom s v = v :=
  rfl

/-- The connected component of a vertex is connected. -/
theorem preconnected_componentGraph (s : V) : (G.componentGraph s).toSimpleGraph.Preconnected :=
  fun u v ↦ ((G.componentHom s).reachable_apply_iff Subtype.val_injective).1 (u.2.symm.trans v.2)

/-- The connected component of `s` has the same edge multiplicities as `G`. -/
@[simp]
theorem edgeCount_componentGraph [DecidableEq V] [Fintype D] (s : V)
    (v u : {v | G.toSimpleGraph.Reachable s v}) :
    (G.componentGraph s).edgeCount v u = G.edgeCount v u :=
  G.edgeCount_restrict _ _ v u

end Reachable

end Cslib.RotationMap
