/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Parameterized.Kernelization
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts

/-!
# Polynomial compressions

A *compression* of a parameterized problem `(A, κ)` into a problem `B`
[BodlaenderJansenKratsch2014, Definition 2] (`Cslib.Complexity.IsCompression`) maps each instance
`a`, in time polynomial in `|enc a| + κ a`, to an instance of `B` that is a yes-instance exactly
when `a ∈ A`, of length at most `h (κ a)`. It is *polynomial* when `h` is polynomially bounded
(`Cslib.Complexity.HasPolyCompression`). Unlike a kernelization, a compression may change the
problem, and it need not bound any parameter of its output.

Two differences with kernelizations (`Cslib.Complexity.IsKernelization`) are deliberate, and
follow [BodlaenderJansenKratsch2014, Definitions 1 and 2]:

* The time bound is a polynomial in `|enc a| + κ a`, not in `|enc a|`: the parameter may be much
  larger than the encoded instance, for instance when it is written in binary. Every
  kernelization is computable in time polynomial in `|enc a|`, so a polynomial kernel is a
  polynomial compression (`Cslib.Complexity.HasPolyKernel.hasPolyCompression`).
* The target of a polynomial compression is any problem on bit strings
  (`Set (List Bool)`); a compression into a problem with another encoding gives one into the
  encoded problem (`Cslib.Complexity.IsCompression.hasPolyCompression`).

As for `Cslib.Complexity.HasPolyKernel`, the size bound `h` is arbitrary, where the cited
definition requires it to be computable; the definitions here are therefore weaker, and the lower
bounds proved with them stronger.

A compression of `(Q, κ)` composes with a polynomial-time map into `Q` whose parameter is
polynomially bounded in the length of its input (`Cslib.Complexity.IsCompression.comp`); this is
how [BodlaenderJansenKratsch2014, Theorem 5] combines a compression with a cross-composition.

## Main definitions

* `Cslib.Complexity.IsCompression`, `Cslib.Complexity.HasPolyCompression`.

## Main results

* `Cslib.Complexity.IsCompression.comp`: a compression composed with a polynomial-time map of
  polynomially bounded parameter is computable in polynomial time.
* `Cslib.Complexity.HasPolyKernel.hasPolyCompression`: a polynomial kernel is a polynomial
  compression.

## References

* [H. L. Bodlaender, B. M. P. Jansen, S. Kratsch, *Kernelization lower bounds by
  cross-composition*][BodlaenderJansenKratsch2014]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

section Defs

variable {α β : Type}

/-- `K` is a *compression* of the parameterized problem `(A, κ)` into `B` with size bound `h`
[BodlaenderJansenKratsch2014, Definition 2]: it is computable within time and space
`T (|enc a| + κ a)` for a polynomially bounded `T` (a time bound alone gives such a space bound),
`K a ∈ B` exactly when `a ∈ A`, and `K a` has encoded length at most `h (κ a)`. Unlike the cited
definition, `h` need not be computable. -/
structure IsCompression (enc : α ↪ List Bool) (κ : α → ℕ) (A : Set α) (encB : β ↪ List Bool)
    (B : Set β) (K : α → β) (h : ℕ → ℕ) : Prop where
  /-- The compression is computable in time and space polynomial in `|enc a| + κ a`. -/
  polyTime : ∃ T : ℕ → ℕ, PolynomiallyBounded T ∧
    ComputableInTimeAndSpace K enc encB (fun a => T ((enc a).length + κ a))
      fun a => T ((enc a).length + κ a)
  /-- The compression preserves membership. -/
  mem_iff : ∀ a, K a ∈ B ↔ a ∈ A
  /-- The output has encoded length bounded by a function of the parameter. -/
  length_le : ∀ a, (encB (K a)).length ≤ h (κ a)

/-- The parameterized problem `(A, κ)` has a *polynomial compression*
[BodlaenderJansenKratsch2014, Definition 2]: a compression into some problem on bit strings, with a
polynomially bounded size bound. -/
@[expose] def HasPolyCompression (enc : α ↪ List Bool) (κ : α → ℕ) (A : Set α) : Prop :=
  ∃ (B : Set (List Bool)) (K : α → List Bool) (h : ℕ → ℕ), PolynomiallyBounded h ∧
    IsCompression enc κ A encBits B K h

end Defs

variable {α β γ : Type} {enc : α ↪ List Bool} {κ : α → ℕ} {A : Set α} {encB : β ↪ List Bool}
  {B : Set β} {K : α → β} {h : ℕ → ℕ}

/-- A compression into a problem `B` with any encoding is a compression into the encoded problem
`encB '' B` on bit strings. -/
theorem IsCompression.encode (hK : IsCompression enc κ A encB B K h) :
    IsCompression enc κ A encBits (encB '' B) (fun a => encB (K a)) h := by
  obtain ⟨T, hT, hK'⟩ := hK.polyTime
  refine ⟨⟨T, hT, ?_⟩, fun a => ?_, hK.length_le⟩
  · obtain ⟨k, State, hfin, tm, htm⟩ := hK'
    exact ⟨k, State, hfin, tm, htm⟩
  · rw [encB.injective.mem_set_image]
    exact hK.mem_iff a

/-- A compression with a polynomially bounded size bound gives a polynomial compression. -/
theorem IsCompression.hasPolyCompression (hK : IsCompression enc κ A encB B K h)
    (hh : PolynomiallyBounded h) : HasPolyCompression enc κ A :=
  ⟨_, _, h, hh, hK.encode⟩

/-- **Composing a compression with a polynomial-time map.** Let `K` be a compression of `(B, κ)`,
and let `g` be computable in polynomial time, with `κ (g c)` bounded by a polynomially bounded
function of `|encC c|`. Then `K ∘ g` is computable in polynomial time. -/
theorem IsCompression.comp {encC : γ ↪ List Bool} {κ : β → ℕ}
    {B : Set β} {Z : Set γ} {K : β → γ} {h : ℕ → ℕ} {g : α → β}
    (hK : IsCompression encB κ B encC Z K h) (hg : ComputableInPolyTime g enc encB)
    (hκ : PolyBounded (fun a => (enc a).length) fun a => κ (g a)) :
    ComputableInPolyTime (fun a => K (g a)) enc encC := by
  obtain ⟨T, hT, hK'⟩ := hK.polyTime
  -- `T` bounds the output of `K`, hence also its space up to a constant factor
  have hKO : ComputableInO K encB encC (fun b => T ((encB b).length + κ b))
      (fun b => T ((encB b).length + κ b)) := by
    obtain ⟨c, hc⟩ := hK'.exists_space_linear
    exact .of_bounds hc (c + 1) (fun b => by nlinarith) (fun b => by nlinarith)
      fun b => (hK'.length_le b).trans (by nlinarith)
  obtain ⟨d, e, hgd⟩ := hg.exists_degree
  have hlen : PolyBounded (fun a => (enc a).length) fun a => (encB (g a)).length :=
    hgd.2.polyBounded
  have hTg : PolyBounded (fun a => (enc a).length)
      fun a => T ((encB (g a)).length + κ (g a)) :=
    (PolyBounded.of_polynomiallyBounded id hT).comp (hlen.add hκ)
  have hgO := hgd.inO
  refine (hKO.comp hgO).computableInPolyTime ?_ ?_ <;>
    exact (PolyBounded.of_forall_le 1 d fun a => by simp).add hTg

/-- **A polynomial kernel is a polynomial compression**: a kernelization is computable in time
polynomial in `|enc a|`, hence in `|enc a| + κ a`. -/
theorem IsKernelization.isCompression {K : α → α} {g : ℕ → ℕ}
    (hK : IsKernelization enc κ A K g) : IsCompression enc κ A enc A K g := by
  obtain ⟨t, s, ht, hs, hK'⟩ := hK.polyTime
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp (ht.add hs)
  have hle (a : α) : t (enc a).length + s (enc a).length ≤ c * ((enc a).length + κ a + 1) ^ d :=
    (hcd (enc a).length).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d))
  refine ⟨⟨fun n => c * (n + 1) ^ d, by fun_prop, hK'.mono (fun a => ?_) fun a => ?_⟩,
    hK.mem_iff, hK.length_le⟩ <;>
  · have := hle a
    dsimp only
    omega

/-- **A polynomial kernel is a polynomial compression** [BodlaenderJansenKratsch2014, p. 5]. -/
theorem HasPolyKernel.hasPolyCompression (h : HasPolyKernel enc κ A) :
    HasPolyCompression enc κ A :=
  let ⟨_, _, hg, hK⟩ := h
  hK.isCompression.hasPolyCompression hg

end Cslib.Complexity
