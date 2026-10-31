/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Deformation

/-!
# Renaming and lifting tensor networks

Two operations that keep the contraction of a tensor network under control while its types or its
coefficient ring change.

* **Renaming** (`TensorNetwork.reindex`). Transport a network along bijections of its vertices
  and of its edges. The contraction is unchanged (`TensorNetwork.contraction_reindex`). The
  contraction recursion of [OpenAI2026ETH] (§D.4.6–§D.4.7, pp. 63–64) uses it to number the
  vertices and edges of a child network by `Fin`.
* **Lifting the entries** (`TensorNetwork.mapFun`). Apply an arbitrary function to every tensor
  entry. When the function is a section of a ring homomorphism `f`, reducing the lifted network
  along `f` recovers the original (`TensorNetwork.map_mapFun`), so its contraction reduces to the
  original contraction (`TensorNetwork.contraction_map_mapFun`). This is the manuscript's
  canonical lift of entries specified modulo `2 ^ p` (§D.4.1, p. 58); any section works.

## Main definitions

* `Cslib.Circuits.Frontier.TensorNetwork.reindex`: renaming the vertices and edges.
* `Cslib.Circuits.Frontier.TensorNetwork.mapFun`: mapping every entry by a function.

## Main results

* `Cslib.Circuits.Frontier.TensorNetwork.contraction_reindex`: renaming preserves the contraction,
  and `card_reindex_src`, `card_reindex_tgt` the degrees.
* `Cslib.Circuits.Frontier.TensorNetwork.map_mapFun`: reducing a lift along `f` recovers the
  network.
* `Cslib.Circuits.Frontier.TensorNetwork.contraction_map_mapFun`: the contraction of a lift
  reduces to the contraction.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.1 (p. 58) and
  §D.4.6 (p. 63).
-/

public section

namespace Cslib.Circuits.Frontier.TensorNetwork

open Finset

variable {R S U V E V' E' : Type*}

/-! ### Renaming the vertices and edges -/

section Reindex

variable (eV : V ≃ V') (eE : E ≃ E') (N : TensorNetwork R U V E)

/-- The network transported along bijections `eV` of the vertices and `eE` of the edges: edge
`eE e` runs from `eV (N.src e)` to `eV (N.tgt e)`, and vertex `eV v` carries the tensor of `v`. -/
@[expose] def reindex : TensorNetwork R U V' E' where
  src e := eV (N.src (eE.symm e))
  tgt e := eV (N.tgt (eE.symm e))
  tensor v x := N.tensor (eV.symm v) (x ∘ eE)
  tensor_congr v x y h := N.tensor_congr _ _ _ fun e he => h (eE e) (by
    simp only [Equiv.symm_apply_apply]
    rcases he with he | he
    · exact Or.inl (by rw [he, Equiv.apply_symm_apply])
    · exact Or.inr (by rw [he, Equiv.apply_symm_apply]))

@[simp] theorem reindex_src (e : E') : (N.reindex eV eE).src e = eV (N.src (eE.symm e)) :=
  rfl

@[simp] theorem reindex_tgt (e : E') : (N.reindex eV eE).tgt e = eV (N.tgt (eE.symm e)) :=
  rfl

@[simp] theorem reindex_tensor (v : V') (x : E' → U) :
    (N.reindex eV eE).tensor v x = N.tensor (eV.symm v) (x ∘ eE) :=
  rfl

/-- Renaming keeps the number of edges leaving each vertex. -/
theorem card_reindex_src [Fintype E] [Fintype E'] [DecidableEq V] [DecidableEq V'] (v : V') :
    #{e | (N.reindex eV eE).src e = v} = #{e | N.src e = eV.symm v} := by
  refine Finset.card_equiv eE.symm fun e => ?_
  rw [Finset.mem_filter, Finset.mem_filter]
  simp [Equiv.eq_symm_apply]

/-- Renaming keeps the number of edges entering each vertex. -/
theorem card_reindex_tgt [Fintype E] [Fintype E'] [DecidableEq V] [DecidableEq V'] (v : V') :
    #{e | (N.reindex eV eE).tgt e = v} = #{e | N.tgt e = eV.symm v} := by
  refine Finset.card_equiv eE.symm fun e => ?_
  rw [Finset.mem_filter, Finset.mem_filter]
  simp [Equiv.eq_symm_apply]

/-- **Renaming preserves the contraction.** -/
theorem contraction_reindex [CommSemiring R] [Fintype U] [Fintype V] [Fintype E] [DecidableEq E]
    [Fintype V'] [Fintype E'] [DecidableEq E'] :
    (N.reindex eV eE).contraction = N.contraction :=
  Fintype.sum_equiv (eE.symm.arrowCongr (Equiv.refl U)) _ _ fun _ =>
    Fintype.prod_equiv eV.symm _ _ fun _ => rfl

end Reindex

/-! ### Lifting the entries -/

section MapFun

/-- The tensor network with every tensor entry mapped by the function `f`. Unlike
`TensorNetwork.map`, `f` need not be a ring homomorphism; a section of a reduction map lifts the
entries. -/
@[expose] def mapFun (f : R → S) (N : TensorNetwork R U V E) : TensorNetwork S U V E where
  toMultigraph := N.toMultigraph
  tensor v x := f (N.tensor v x)
  tensor_congr v x y h := by rw [N.tensor_congr v x y h]

@[simp] theorem mapFun_tensor (f : R → S) (N : TensorNetwork R U V E) (v : V) (x : E → U) :
    (N.mapFun f).tensor v x = f (N.tensor v x) :=
  rfl

@[simp] theorem toMultigraph_mapFun (f : R → S) (N : TensorNetwork R U V E) :
    (N.mapFun f).toMultigraph = N.toMultigraph :=
  rfl

variable [CommSemiring R] [CommSemiring S] (f : R →+* S) {σ : S → R}

/-- **Reducing a lift recovers the network**: for a section `σ` of `f`, mapping the entries by
`σ` and then by `f` changes nothing. -/
theorem map_mapFun (hσ : ∀ x, f (σ x) = x) (N : TensorNetwork S U V E) :
    (N.mapFun σ).map f = N := by
  obtain ⟨G, T, hT⟩ := N
  simp only [map, mapFun, hσ]

/-- **The contraction of a lift reduces to the contraction**: for a section `σ` of `f`, `f` maps
the contraction of the lifted network to the contraction of the network. -/
theorem contraction_map_mapFun [Fintype U] [Fintype V] [Fintype E] [DecidableEq E]
    (hσ : ∀ x, f (σ x) = x) (N : TensorNetwork S U V E) :
    f (N.mapFun σ).contraction = N.contraction := by
  rw [← contraction_map, map_mapFun f hσ]

end MapFun

end Cslib.Circuits.Frontier.TensorNetwork
