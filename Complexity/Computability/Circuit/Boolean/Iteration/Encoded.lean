/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration

/-!
# Encoded state spaces and burn-in

The fixed-power bound applies to a map `f` on any finite invariant set `S` of a type in any
universe, given an injective bit encoding `e` of `S` and a Boolean circuit realizing `f` on the
encodings (`fixed_power_encoded`). All computation is charged on the encoding; no gate evaluates
`f` itself. Its storage term counts `|S|`.

After a burn-in of `d` steps, computed by a separate circuit, every orbit lies in the image of
`f^[d]`, so the storage term of the remaining steps counts only that image
(`fixed_power_image`).

## Main results

* `Cslib.Circuits.Boolean.Iteration.fixed_power_encoded`: fixed powers through an encoding.
* `Cslib.Circuits.Boolean.Iteration.fixed_power_image`: fixed powers after a burn-in.

## References

* Adapted from lean/Proofs/Extensions.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

universe u

variable {α : Type u} {n : ℕ}

/-- A circuit realizing `f` on the encodings of an invariant set realizes its powers. -/
private theorem iterate_encoded (f : α → α) (S : Finset α) (e : α → BitString n)
    (c : Circuit signature n n) (hS : ∀ x ∈ S, f x ∈ S)
    (hstep : ∀ x ∈ S, c.eval interpretation (e x) = e (f x)) {x : α} (hx : x ∈ S) (T : ℕ) :
    (c.eval interpretation)^[T] (e x) = e (f^[T] x) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact hstep _ (Set.MapsTo.iterate (f := f) (s := ↑S) hS T hx)

/-- **Encoded fixed powers.** If an injective encoding `e` of a finite invariant set `S` of an
arbitrary type is realized by a circuit `c`, then for every exponent `T` and `0 < L ≤ 2 ^ n` some
circuit of size at most `40000 * powerBudget n c.size S.card L` realizes `f^[T]` on `S`. -/
theorem fixed_power_encoded (f : α → α) (S : Finset α) (e : α → BitString n)
    (he : Set.InjOn e S) (c : Circuit signature n n) (hS : ∀ x ∈ S, f x ∈ S)
    (hstep : ∀ x ∈ S, c.eval interpretation (e x) = e (f x))
    (T L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n n,
      (∀ x ∈ S, out.eval interpretation (e x) = e (f^[T] x)) ∧
      out.size ≤ 40000 * powerBudget n c.size S.card L := by
  classical
  have himage : ∀ y ∈ S.image e, c.eval interpretation y ∈ S.image e := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [hstep x hx]
    exact Finset.mem_image.mpr ⟨f x, hS x hx, rfl⟩
  obtain ⟨out, hout, hsize⟩ := fixed_power_on n c (S.image e) T L himage hL hLN
  refine ⟨out, fun x hx => ?_, by simpa only [Finset.card_image_of_injOn he] using hsize⟩
  rw [hout (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hx, rfl⟩))]
  exact iterate_encoded f S e c hS hstep hx T

/-- **Fixed powers after a burn-in.** Given a circuit for `d ≤ T` steps, the remaining `T - d`
steps cost the fixed-power bound with storage term the size of the image of `f^[d]`. -/
theorem fixed_power_image (c burn : Circuit signature n n) (d T L : ℕ)
    (hburn : burn.Computes interpretation (c.eval interpretation)^[d])
    (hdT : d ≤ T) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n n,
      out.Computes interpretation (c.eval interpretation)^[T] ∧
      out.size ≤ burn.size + 40000 * powerBudget n c.size
        (Finset.univ.image (c.eval interpretation)^[d]).card L := by
  classical
  let f := c.eval interpretation
  let S := Finset.univ.image f^[d]
  have hS : ∀ y ∈ S, f y ∈ S := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨f x, Finset.mem_univ _, by
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']⟩
  obtain ⟨tail, htail, hsize⟩ := fixed_power_on n c S (T - d) L hS hL hLN
  refine ⟨tail.comp burn, fun x => ?_, ?_⟩
  · rw [Circuit.eval_comp, hburn x,
      htail (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)),
      ← Function.iterate_add_apply, Nat.sub_add_cancel hdT]
  · rw [Circuit.size_comp]
    exact Nat.add_le_add_left hsize burn.size

end Cslib.Circuits.Boolean.Iteration
