/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Product
import CslibFrontier.Probability.PMF.Map

/-!
# Relabelling the coordinates of a finite product

Relabelling the coordinates of an independent product along an equivalence of the index types
gives the independent product of the relabelled factors. In particular an independent product
indexed by a product type `ι × κ` is a product of independent blocks indexed by `ι`, each an
independent product indexed by `κ`, and a sample of `q * m` independent points splits into `q`
independent blocks of `m` points along `finProdFinEquiv`.

## Main results

* `Cslib.Probability.PMF.pi_map_piCongrLeft_symm`: relabelling the coordinates of a product.
* `Cslib.Probability.PMF.pi_map_curry`: a product indexed by `ι × κ` is a product of independent
  blocks.
* `Cslib.Probability.PMF.pi_map_finProdFinEquiv`: a sample of `q * m` points is a sample of `q`
  independent blocks of `m` points.
-/

public section

namespace Cslib.Probability.PMF

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Relabelling the coordinates of an independent product along an equivalence `e` of the index
types gives the product of the relabelled factors. -/
theorem pi_map_piCongrLeft_symm {α : ι → Type*} [∀ i, Finite (α i)] (p : ∀ i, PMF (α i))
    (e : κ ≃ ι) :
    (pi p).map (Equiv.piCongrLeft α e).symm = pi fun k => p (e k) := by
  ext b
  rw [map_equiv_apply, Equiv.symm_symm, pi_apply, pi_apply]
  exact (Fintype.prod_equiv e _ _ fun k => by rw [Equiv.piCongrLeft_apply_apply]).symm

/-- Relabelling the coordinates of an independent sample along an equivalence `e` of the index
types gives an independent sample. -/
theorem pi_map_comp_equiv {γ : Type*} [Finite γ] (p : PMF γ) (e : κ ≃ ι) :
    (pi fun _ : ι => p).map (fun b k => b (e k)) = pi fun _ : κ => p :=
  pi_map_piCongrLeft_symm (fun _ : ι => p) e

/-- An independent product indexed by `ι × κ` is a product of independent blocks indexed by `ι`,
each an independent product indexed by `κ`. -/
theorem pi_map_curry {γ : Type*} [Finite γ] (p : ι × κ → PMF γ) :
    (pi p).map Function.curry = pi fun i => pi fun k => p (i, k) := by
  ext b
  rw [show (Function.curry : (ι × κ → γ) → ι → κ → γ) = Equiv.curry ι κ γ from rfl,
    map_equiv_apply, pi_apply, pi_apply, Fintype.prod_prod_type]
  rfl

/-- An independent sample of `q * m` points is a sample of `q` independent blocks of `m` points,
the block `j` consisting of the points `finProdFinEquiv (j, k)`. -/
theorem pi_map_finProdFinEquiv {γ : Type*} [Finite γ] (p : PMF γ) (q m : ℕ) :
    (pi fun _ : Fin (q * m) => p).map (fun b j k => b (finProdFinEquiv (j, k))) =
      pi fun _ : Fin q => pi fun _ : Fin m => p := by
  rw [← pi_map_curry fun _ => p, ← pi_map_comp_equiv p finProdFinEquiv, PMF.map_comp]
  rfl

end Cslib.Probability.PMF
