/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.DiscreteLog
public import Complexity.Probability.PMF
import Complexity.Probability.PMF.Bind
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring

/-!
# Universal and $\text{universal}_2$ projective hash functions over prime-order groups

This module formalizes the universal and $\text{universal}_2$ projective hash families over a
`PrimeOrderGroupFamily` from
[Boneh and Shoup, Sections 12.5.1–12.5.2, printed pp. 484–488][BonehShoup2023], which form the
algebraic core of the Cramer–Shoup public-key encryption scheme (Section 12.5.3 and Exercise 12.27).

Groups are written additively as `ZMod (F.order d)`-modules (matching `DiscreteLog`,
`DiffieHellman`, and `ElGamal`), so the book's $v^\sigma w^\tau$ is
$\sigma \bullet v + \tau \bullet w$.

## Source Statements ([BonehShoup2023], Sections 12.5.1–12.5.2, printed pp. 485–488)

Verbatim from [BonehShoup2023], Section 12.5.1 (printed p. 485):

> The function $f := f_{\sigma, \tau}$ is indexed by randomly chosen
> $\sigma, \tau \in \mathbb{Z}_q$, and is defined as follows:
> $$f_{\sigma, \tau} : \mathbb{G}^2 \to \mathbb{G}, \quad
> (v, w) \mapsto v^\sigma w^\tau. \quad (12.13)$$
> The auxiliary information $h$ that defines $f$ on $L_u$ is
> $$h := f(g, u) = g^\sigma u^\tau. \quad (12.14)$$
> …
> **Lemma 12.5.** Suppose $\sigma$ and $\tau$ are uniformly and independently distributed over
> $\mathbb{Z}_q$. Then for all $u, v, w, h, z \in \mathbb{G}$, if $(u, v, w)$ is not a DH-triple,
> then
> $$\Pr[g^\sigma u^\tau = h \land v^\sigma w^\tau = z] = \frac{1}{q^2}.$$

Verbatim from [BonehShoup2023], Section 12.5.2 (printed pp. 487–488):

> We define a new function $f' := f'_{\sigma_1, \tau_1, \sigma_2, \tau_2}$, indexed by randomly
> chosen $\sigma_1, \tau_1, \sigma_2, \tau_2 \in \mathbb{Z}_q$, as follows
> $$f'_{\sigma_1, \tau_1, \sigma_2, \tau_2} : \mathbb{G}^2 \times \mathbb{Z}_q \to \mathbb{G}, \quad
> (v, w, \rho) \mapsto f_{\sigma_1, \tau_1}(v, w) \cdot f_{\sigma_2, \tau_2}(v, w)^\rho =
> v^{\sigma_1 + \rho \sigma_2} w^{\tau_1 + \rho \tau_2}. \quad (12.16)$$
> The auxiliary information that defines $f'$ on $L_u \times \mathbb{Z}_q$ is $h' := (h_1, h_2)$,
> where $h_i$ is the auxiliary information that defines $f_{\sigma_i, \tau_i}$ on $L_u$; that is
> $$h_i := f_{\sigma_i, \tau_i}(g, u) = g^{\sigma_i} u^{\tau_i}
> \quad \text{for } i = 1, 2. \quad (12.17)$$
> …
> **Lemma 12.7.** Suppose $\sigma_1, \tau_1, \sigma_2, \tau_2$ are uniformly and independently
> distributed over $\mathbb{Z}_q$. Then for all
> $u, v, w, \hat{v}, \hat{w}, h_1, h_2, z, \hat{z} \in \mathbb{G}$ and all
> $\rho, \hat{\rho} \in \mathbb{Z}_q$, if $(u, v, w)$ and $(u, \hat{v}, \hat{w})$
> are not DH-triples, and $\rho \ne \hat{\rho}$, then
> $$\Pr[g^{\sigma_1} u^{\tau_1} = h_1 \land g^{\sigma_2} u^{\tau_2} = h_2 \land
> v^{\sigma_1 + \rho_1 \sigma_2} w^{\tau_1 + \rho_1 \tau_2} = z \land
> \hat{v}^{\sigma_1 + \rho_2 \sigma_2} \hat{w}^{\tau_1 + \rho_2 \tau_2} = \hat{z}] =
> \frac{1}{q^4}.$$
> …
> **Lemma 12.8.** In Attack Game 12.5, for any adversary $\mathcal{A}$ that outputs at most $Q$
> tuples, the probability that it wins is at most $Q/q$.

Attack Game 12.5 itself is not formalized as a standalone game here; instead, this module proves
the explicit change-of-variables equivalences (`projHashFiberChangeEquiv`,
`projHash2FiberChangeEquiv`), the single-tuple `1 / q` hit law (`uniform_projHash2_fiber_apply`),
and the finite-list `Q / q` union bound (`uniform_projHash2_fiber_any_le`) on the `τ₂`-fiber given
`δ₁ = σ₁ + α * τ₁`, `δ₂ = σ₂ + α * τ₂`, and `ξ = τ₁ + ρ * τ₂` (where `(h₁, h₂, z)` and all DH
queries depend only on `(δ₁, δ₂, ξ)`). The adaptive decryption-oracle reduction for Cramer–Shoup
using these ingredients is carried by `Complexity/Crypto/Computational/CramerShoup.lean` (PR 2).

## Main definitions

* `Cslib.Crypto.ProjectiveHash.projHash`, `Cslib.Crypto.ProjectiveHash.projHashAux`: universal
  projective hash evaluation `(12.13)` and public projection `(12.14)`.
* `Cslib.Crypto.ProjectiveHash.projHashFiberChangeEquiv`,
  `Cslib.Crypto.ProjectiveHash.projHashEquiv`: fiber change-of-variables `(δ, τ) ↦ (δ - α * τ, τ)`
  and 2×2 linear equivalence on `ZMod q × ZMod q` underlying Lemma 12.5 when `γ ≠ α * β`.
* `Cslib.Crypto.ProjectiveHash.projHash2`, `Cslib.Crypto.ProjectiveHash.projHash2Aux`:
  $\text{universal}_2$ projective hash evaluation `(12.16)` and public projection pair `(12.17)`.
* `Cslib.Crypto.ProjectiveHash.projHash2FiberChangeEquiv`,
  `Cslib.Crypto.ProjectiveHash.projHash2Equiv`: 4-tuple fiber change-of-variables
  `((δ₁, δ₂), (ξ, τ₂)) ↦ ((δ₁ - α * (ξ - ρ * τ₂), ξ - ρ * τ₂), (δ₂ - α * τ₂, τ₂))` and 4×4 linear
  equivalence on `(ZMod q × ZMod q) × (ZMod q × ZMod q)` underlying Lemma 12.7 when `γ ≠ α * β`,
  `γ' ≠ α * β'`, and `ρ' ≠ ρ`.

## Main results

* `Cslib.Crypto.ProjectiveHash.projHash_smul_generator`,
  `Cslib.Crypto.ProjectiveHash.projHash2_smul_generator`: projective evaluation on Diffie–Hellman
  triples `(β • g, β • u) ∈ L_u` via the public projections `h` and `(h₁, h₂)`.
* `Cslib.Crypto.ProjectiveHash.projHash_bijective_of_ne`,
  `Cslib.Crypto.ProjectiveHash.uniform_projHash_apply_of_ne`,
  `Cslib.Crypto.ProjectiveHash.uniform_projHash_fiber`,
  `Cslib.Crypto.ProjectiveHash.uniform_projHash_fiber_add`: Lemma 12.5 bijection and `1 / q ^ 2`
  joint point mass, together with conditional uniform masking on non-DH triples as a consequence of
  Lemma 12.5 under `projHashFiberChangeEquiv`.
* `Cslib.Crypto.ProjectiveHash.projHash2_fiber_eq`,
  `Cslib.Crypto.ProjectiveHash.projHash2_bijective_of_ne`,
  `Cslib.Crypto.ProjectiveHash.uniform_projHash2_apply_of_ne`,
  `Cslib.Crypto.ProjectiveHash.projHash2_fiber_bijective_of_ne`,
  `Cslib.Crypto.ProjectiveHash.uniform_projHash2_fiber_apply`,
  `Cslib.Crypto.ProjectiveHash.uniform_projHash2_fiber_any_le`: Lemma 12.7 4-tuple bijection and
  `1 / q ^ 4` joint point mass, and the single-tuple `1 / q` and `Q`-tuple `Q / q` union-bound
  ingredients of Lemma 12.8 (via Lemma 12.7) on the `τ₂`-fiber of `projHash2FiberChangeEquiv` for
  non-DH triples with `ρ' ≠ ρ`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 12.5.1–12.5.2 (printed pp. 484–488).
-/

@[expose] public section

namespace Cslib.Crypto.ProjectiveHash

open Probability
open scoped ENNReal

variable (F : PrimeOrderGroupFamily)

/-! ### Universal projective hash functions ([BonehShoup2023], Section 12.5.1, printed p. 485) -/

/-- Universal projective hash evaluation `f_{σ,τ}(v, w) = σ • v + τ • w`
([BonehShoup2023], Section 12.5.1, equation (12.13), printed p. 485). -/
def projHash (d : F.Desc) (σ τ : ZMod (F.order d)) (v w : F.Carrier d) : F.Carrier d :=
  σ • v + τ • w

/-- Auxiliary public projection `h = f_{σ,τ}(g, u) = σ • g + τ • u`
([BonehShoup2023], Section 12.5.1, equation (12.14), printed p. 485). -/
def projHashAux (d : F.Desc) (σ τ : ZMod (F.order d)) (u : F.Carrier d) : F.Carrier d :=
  projHash F d σ τ (F.generator d) u

/-- **Projective property of `projHash` on $L_u$** ([BonehShoup2023], Section 12.5.1, printed
p. 485): on any Diffie–Hellman pair `(v, w) = (β • g, β • u)`, `f_{σ,τ}(v, w) = β • h`. -/
@[simp]
theorem projHash_smul_generator (d : F.Desc) (σ τ β : ZMod (F.order d)) (u : F.Carrier d) :
    projHash F d σ τ (β • F.generator d) (β • u) = β • projHashAux F d σ τ u := by
  simp only [projHash, projHashAux, smul_add, smul_smul, mul_comm]

/-- Explicit generator-exponent form of `projHashAux` on `u = α • g`. -/
@[simp]
theorem projHashAux_generator_smul (d : F.Desc) (σ τ α : ZMod (F.order d)) :
    projHashAux F d σ τ (α • F.generator d) = (σ + α * τ) • F.generator d := by
  simp only [projHashAux, projHash, smul_smul, ← add_smul, mul_comm τ α]

/-- Explicit generator-exponent form of `projHash` on `(v, w) = (β • g, γ • g)`. -/
@[simp]
theorem projHash_generator_smul (d : F.Desc) (σ τ β γ : ZMod (F.order d)) :
    projHash F d σ τ (β • F.generator d) (γ • F.generator d) =
      (β * σ + γ * τ) • F.generator d := by
  simp only [projHash, smul_smul, ← add_smul, mul_comm σ β, mul_comm τ γ]

/-- On the fiber `σ = δ - α * τ` where `projHashAux F d σ τ (α • g) = δ • g`, evaluating `projHash`
on `(β • g, γ • g)` gives `(β * δ + (γ - α * β) * τ) • g`. -/
theorem projHash_fiber_eq (d : F.Desc) (α β γ δ τ : ZMod (F.order d)) :
    projHash F d (δ - α * τ) τ (β • F.generator d) (γ • F.generator d) =
      (β * δ + (γ - α * β) * τ) • F.generator d := by
  rw [projHash_generator_smul]
  congr 1
  ring

/-- On the fiber `σ = δ - α * τ`, the auxiliary projection `projHashAux` is independent of `τ` and
equals `δ • g`. -/
theorem projHashAux_fiber_eq (d : F.Desc) (α δ τ : ZMod (F.order d)) :
    projHashAux F d (δ - α * τ) τ (α • F.generator d) = δ • F.generator d := by
  rw [projHashAux_generator_smul]
  congr 1
  ring

/-- The fiber change-of-variables `(δ, τ) ↦ (δ - α * τ, τ)` on `ZMod (F.order d) × ZMod (F.order d)`
under which `projHashAux F d σ τ (α • g) = δ • g` depends only on `δ`. -/
def projHashFiberChangeEquiv (d : F.Desc) (α : ZMod (F.order d)) :
    ZMod (F.order d) × ZMod (F.order d) ≃ ZMod (F.order d) × ZMod (F.order d) where
  toFun p := (p.1 - α * p.2, p.2)
  invFun q := (q.1 + α * q.2, q.2)
  left_inv p := by
    ext
    · dsimp only; ring
    · rfl
  right_inv q := by
    ext
    · dsimp only; ring
    · rfl

@[simp]
theorem projHashFiberChangeEquiv_apply (d : F.Desc) (α δ τ : ZMod (F.order d)) :
    projHashFiberChangeEquiv F d α (δ, τ) = (δ - α * τ, τ) :=
  rfl

/-- The affine bijection `τ ↦ β * δ + (γ - α * β) * τ` on `ZMod (F.order d)` when `γ ≠ α * β`. -/
def projHashFiberEquiv (d : F.Desc) {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β)
    (δ : ZMod (F.order d)) : ZMod (F.order d) ≃ ZMod (F.order d) :=
  (Equiv.mulLeft₀ (γ - α * β) (sub_ne_zero.mpr hγ)).trans (Equiv.addLeft (β * δ))

@[simp]
theorem projHashFiberEquiv_apply (d : F.Desc) {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β)
    (δ τ : ZMod (F.order d)) :
    projHashFiberEquiv F d hγ δ τ = β * δ + (γ - α * β) * τ := by
  simp [projHashFiberEquiv]

/-- Explicit 2×2 linear equivalence `(σ, τ) ↦ (σ + α * τ, β * p.1 + γ * p.2)` on
`ZMod (F.order d) × ZMod (F.order d)` when `γ ≠ α * β` ([BonehShoup2023], proof of Lemma 12.5,
printed pp. 485–486). -/
def projHashEquiv (d : F.Desc) {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β) :
    ZMod (F.order d) × ZMod (F.order d) ≃ ZMod (F.order d) × ZMod (F.order d) where
  toFun p := (p.1 + α * p.2, β * p.1 + γ * p.2)
  invFun q :=
    let τ := (γ - α * β)⁻¹ * (q.2 - β * q.1)
    (q.1 - α * τ, τ)
  left_inv p := by
    have hne : γ - α * β ≠ 0 := sub_ne_zero.mpr hγ
    ext
    · dsimp only
      have hsub : β * p.1 + γ * p.2 - β * (p.1 + α * p.2) = (γ - α * β) * p.2 := by ring
      rw [hsub, inv_mul_cancel_left₀ hne]
      ring
    · dsimp only
      have hsub : β * p.1 + γ * p.2 - β * (p.1 + α * p.2) = (γ - α * β) * p.2 := by ring
      rw [hsub, inv_mul_cancel_left₀ hne]
  right_inv q := by
    have hne : γ - α * β ≠ 0 := sub_ne_zero.mpr hγ
    ext
    · dsimp only
      ring
    · dsimp only
      have hlin :
          β * (q.1 - α * ((γ - α * β)⁻¹ * (q.2 - β * q.1))) +
            γ * ((γ - α * β)⁻¹ * (q.2 - β * q.1)) =
          β * q.1 + (γ - α * β) * ((γ - α * β)⁻¹ * (q.2 - β * q.1)) := by ring
      rw [hlin, mul_inv_cancel_left₀ hne]
      ring

/-- **Lemma 12.5 bijection** ([BonehShoup2023], Section 12.5.1, printed p. 485): when `γ ≠ α * β`,
the map `(σ, τ) ↦ (projHashAux F d σ τ (α • g), projHash F d σ τ (β • g) (γ • g))` is a bijection
from `ZMod (F.order d) × ZMod (F.order d)` to `F.Carrier d × F.Carrier d`. -/
theorem projHash_bijective_of_ne (d : F.Desc) {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β) :
    Function.Bijective (fun p : ZMod (F.order d) × ZMod (F.order d) =>
      (projHashAux F d p.1 p.2 (α • F.generator d),
        projHash F d p.1 p.2 (β • F.generator d) (γ • F.generator d))) := by
  have hcomp :
      (fun p : ZMod (F.order d) × ZMod (F.order d) =>
        (projHashAux F d p.1 p.2 (α • F.generator d),
          projHash F d p.1 p.2 (β • F.generator d) (γ • F.generator d))) =
      (Prod.map (fun x : ZMod (F.order d) => x • F.generator d)
        (fun y : ZMod (F.order d) => y • F.generator d)) ∘ projHashEquiv F d hγ := by
    funext p
    simp [projHashEquiv]
  rw [hcomp]
  exact ((F.smul_generator_bijective d).prodMap (F.smul_generator_bijective d)).comp
    (projHashEquiv F d hγ).bijective

/-- **Lemma 12.5 (`1 / q ^ 2` joint point mass)** ([BonehShoup2023], Section 12.5.1,
printed p. 485): under uniform `(σ, τ) : ZMod (F.order d) × ZMod (F.order d)`, for any non-DH
triple `γ ≠ α * β` and any `h, z : F.Carrier d`, the joint pair
`(projHashAux F d σ τ (α • g), projHash F d σ τ (β • g) (γ • g))` equals `(h, z)` with
probability `((F.order d : ℝ≥0∞) ^ 2)⁻¹`. -/
theorem uniform_projHash_apply_of_ne (d : F.Desc) {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β)
    (h z : F.Carrier d) :
    ((PMF.uniformOfFintype (ZMod (F.order d) × ZMod (F.order d))).map (fun p =>
      (projHashAux F d p.1 p.2 (α • F.generator d),
        projHash F d p.1 p.2 (β • F.generator d) (γ • F.generator d)))) (h, z) =
      ((F.order d : ℝ≥0∞) ^ 2)⁻¹ := by
  obtain ⟨δ, rfl⟩ := F.smul_generator_surjective d h
  obtain ⟨ζ, rfl⟩ := F.smul_generator_surjective d z
  let encodePair : ZMod (F.order d) × ZMod (F.order d) → F.Carrier d × F.Carrier d :=
    Prod.map (fun x => x • F.generator d) (fun y => y • F.generator d)
  have hinj : Function.Injective encodePair :=
    ((F.smul_generator_bijective d).prodMap (F.smul_generator_bijective d)).1
  have hmap :
      (PMF.uniformOfFintype (ZMod (F.order d) × ZMod (F.order d))).map (fun p =>
        (projHashAux F d p.1 p.2 (α • F.generator d),
          projHash F d p.1 p.2 (β • F.generator d) (γ • F.generator d))) =
      (PMF.uniformOfFintype (ZMod (F.order d) × ZMod (F.order d))).map encodePair := by
    have hcomp :
        (fun p : ZMod (F.order d) × ZMod (F.order d) =>
          (projHashAux F d p.1 p.2 (α • F.generator d),
            projHash F d p.1 p.2 (β • F.generator d) (γ • F.generator d))) =
        encodePair ∘ projHashEquiv F d hγ := by
      funext p
      simp [encodePair, projHashEquiv]
    rw [hcomp, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv]
  classical
  change ((PMF.uniformOfFintype (ZMod (F.order d) × ZMod (F.order d))).map (fun p =>
    (projHashAux F d p.1 p.2 (α • F.generator d),
      projHash F d p.1 p.2 (β • F.generator d) (γ • F.generator d)))) (encodePair (δ, ζ)) = _
  rw [hmap, PMF.map_apply]
  simp [hinj.eq_iff, PMF.uniformOfFintype_apply, sq]

/-- **Consequence of Lemma 12.5 (conditional uniformity on the `τ`-fiber)**
([BonehShoup2023], Section 12.5.1, printed p. 485): under the change of variables
`projHashFiberChangeEquiv` (`σ = δ - α * τ`, so `h = δ • g`), for any fixed `δ` and uniform
`τ : ZMod (F.order d)`, `projHash F d (δ - α * τ) τ (β • g) (γ • g)` has the same distribution as
`ζ • g` for a uniform `ζ : ZMod (F.order d)` whenever `γ ≠ α * β`. -/
theorem uniform_projHash_fiber {α_out : Type*} (d : F.Desc) {α β γ : ZMod (F.order d)}
    (hγ : γ ≠ α * β) (δ : ZMod (F.order d)) (f : F.Carrier d → PMF α_out) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ =>
      f (projHash F d (δ - α * τ) τ (β • F.generator d) (γ • F.generator d))) =
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun ζ => f (ζ • F.generator d) := by
  simp only [projHash_fiber_eq]
  change (PMF.uniformOfFintype (ZMod (F.order d))).bind
      ((fun ζ => f (ζ • F.generator d)) ∘ projHashFiberEquiv F d hγ δ) =
    (PMF.uniformOfFintype (ZMod (F.order d))).bind (fun ζ => f (ζ • F.generator d))
  rw [← PMF.bind_map, PMF.uniformOfFintype_map_equiv]

/-- **One-time group mask via `projHash` on a non-DH triple**: fixing `δ = σ + α * τ`, for any
message `m : F.Carrier d` and any non-DH triple `γ ≠ α * β`, masking `m` by
`projHash F d (δ - α * τ) τ (β • g) (γ • g) + m` under uniform `τ` has the same distribution as
`ζ • g` for uniform `ζ : ZMod (F.order d)` (and is therefore independent of `m`). -/
theorem uniform_projHash_fiber_add {α_out : Type*} (d : F.Desc) {α β γ : ZMod (F.order d)}
    (hγ : γ ≠ α * β) (δ : ZMod (F.order d)) (m : F.Carrier d) (f : F.Carrier d → PMF α_out) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ =>
      f (projHash F d (δ - α * τ) τ (β • F.generator d) (γ • F.generator d) + m)) =
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun ζ => f (ζ • F.generator d) := by
  rw [uniform_projHash_fiber F d hγ δ (fun z => f (z + m)), F.uniform_smul_generator_add d m f]

/-! ### $\text{Universal}_2$ projective hash functions ([BonehShoup2023], Section 12.5.2) -/

/-- $\text{Universal}_2$ projective hash evaluation
`f'_{σ₁,τ₁,σ₂,τ₂}(v, w, ρ) = (σ₁ + ρ * σ₂) • v + (τ₁ + ρ * τ₂) • w`
([BonehShoup2023], Section 12.5.2, equation (12.16), printed p. 487). -/
def projHash2 (d : F.Desc) (σ₁ τ₁ σ₂ τ₂ ρ : ZMod (F.order d))
    (v w : F.Carrier d) : F.Carrier d :=
  (σ₁ + ρ * σ₂) • v + (τ₁ + ρ * τ₂) • w

/-- Auxiliary public projection pair `(h₁, h₂) = (σ₁ • g + τ₁ • u, σ₂ • g + τ₂ • u)`
([BonehShoup2023], Section 12.5.2, equation (12.17), printed p. 487). -/
def projHash2Aux (d : F.Desc) (σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d)) (u : F.Carrier d) :
    F.Carrier d × F.Carrier d :=
  (projHashAux F d σ₁ τ₁ u, projHashAux F d σ₂ τ₂ u)

/-- `projHash2` decomposes as `f_{σ₁,τ₁}(v, w) + ρ • f_{σ₂,τ₂}(v, w)` ([BonehShoup2023],
equation (12.16), printed p. 487). -/
theorem projHash2_eq_projHash_add (d : F.Desc) (σ₁ τ₁ σ₂ τ₂ ρ : ZMod (F.order d))
    (v w : F.Carrier d) :
    projHash2 F d σ₁ τ₁ σ₂ τ₂ ρ v w =
      projHash F d σ₁ τ₁ v w + ρ • projHash F d σ₂ τ₂ v w := by
  simp only [projHash2, projHash, add_smul, smul_add, smul_smul]
  abel

/-- **Projective property of `projHash2` on $L_u$** ([BonehShoup2023], Section 12.5.2, printed
p. 487): on any Diffie–Hellman pair `(v, w) = (β • g, β • u)`,
`f'(v, w, ρ) = β • (h₁ + ρ • h₂)`. -/
@[simp]
theorem projHash2_smul_generator (d : F.Desc) (σ₁ τ₁ σ₂ τ₂ β ρ : ZMod (F.order d))
    (u : F.Carrier d) :
    projHash2 F d σ₁ τ₁ σ₂ τ₂ ρ (β • F.generator d) (β • u) =
      β • ((projHash2Aux F d σ₁ τ₁ σ₂ τ₂ u).1 + ρ • (projHash2Aux F d σ₁ τ₁ σ₂ τ₂ u).2) := by
  rw [projHash2_eq_projHash_add, projHash_smul_generator, projHash_smul_generator,
    smul_add, smul_comm ρ β]
  rfl

/-- Explicit generator-exponent form of `projHash2` on `(v, w) = (β • g, γ • g)`. -/
@[simp]
theorem projHash2_generator_smul (d : F.Desc) (σ₁ τ₁ σ₂ τ₂ ρ β γ : ZMod (F.order d)) :
    projHash2 F d σ₁ τ₁ σ₂ τ₂ ρ (β • F.generator d) (γ • F.generator d) =
      (β * (σ₁ + ρ * σ₂) + γ * (τ₁ + ρ * τ₂)) • F.generator d := by
  simp only [projHash2, smul_smul, ← add_smul, mul_comm _ β, mul_comm _ γ]

/-- On the fiber `σ₁ = δ₁ - α * τ₁` and `σ₂ = δ₂ - α * τ₂` (where `(h₁, h₂) = (δ₁ • g, δ₂ • g)`),
evaluating `projHash2` on `(β • g, γ • g, ρ)` gives
`(β * (δ₁ + ρ * δ₂) + (γ - α * β) * (τ₁ + ρ * τ₂)) • g`. -/
theorem projHash2_fiber_eq (d : F.Desc) (α β γ δ₁ δ₂ τ₁ τ₂ ρ : ZMod (F.order d)) :
    projHash2 F d (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂ ρ
      (β • F.generator d) (γ • F.generator d) =
      (β * (δ₁ + ρ * δ₂) + (γ - α * β) * (τ₁ + ρ * τ₂)) • F.generator d := by
  rw [projHash2_generator_smul]
  congr 1
  ring

/-- On a Diffie–Hellman triple `γ = α * β`, `projHash2` on the fiber `σ₁ = δ₁ - α * τ₁`,
`σ₂ = δ₂ - α * τ₂` equals `(β * (δ₁ + ρ * δ₂)) • g`, independent of `(τ₁, τ₂)`. -/
theorem projHash2_fiber_dh (d : F.Desc) (α β δ₁ δ₂ τ₁ τ₂ ρ : ZMod (F.order d)) :
    projHash2 F d (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂ ρ
      (β • F.generator d) ((α * β) • F.generator d) =
      (β * (δ₁ + ρ * δ₂)) • F.generator d := by
  rw [projHash2_fiber_eq, sub_self, zero_mul, add_zero]

/-- On the fiber `σ₁ = δ₁ - α * τ₁` and `σ₂ = δ₂ - α * τ₂`, `projHash2Aux` is `(δ₁ • g, δ₂ • g)`. -/
@[simp]
theorem projHash2Aux_fiber_eq (d : F.Desc) (α δ₁ δ₂ τ₁ τ₂ : ZMod (F.order d)) :
    projHash2Aux F d (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂ (α • F.generator d) =
      (δ₁ • F.generator d, δ₂ • F.generator d) := by
  simp only [projHash2Aux, projHashAux_fiber_eq]

/-- The 4-tuple fiber change-of-variables
`((δ₁, δ₂), (ξ, τ₂)) ↦ ((δ₁ - α * (ξ - ρ * τ₂), ξ - ρ * τ₂), (δ₂ - α * τ₂, τ₂))`
on `(ZMod (F.order d) × ZMod (F.order d)) × (ZMod (F.order d) × ZMod (F.order d))`, under which
`(h₁, h₂)`, the challenge tag on `(β • g, γ • g, ρ)`, and all Diffie–Hellman queries depend only
on `(δ₁, δ₂, ξ)` and are independent of `τ₂`. -/
def projHash2FiberChangeEquiv (d : F.Desc) (α ρ : ZMod (F.order d)) :
    (ZMod (F.order d) × ZMod (F.order d)) × (ZMod (F.order d) × ZMod (F.order d)) ≃
      (ZMod (F.order d) × ZMod (F.order d)) × (ZMod (F.order d) × ZMod (F.order d)) where
  toFun p :=
    ((p.1.1 - α * (p.2.1 - ρ * p.2.2), p.2.1 - ρ * p.2.2),
      (p.1.2 - α * p.2.2, p.2.2))
  invFun q :=
    ((q.1.1 + α * q.1.2, q.2.1 + α * q.2.2),
      (q.1.2 + ρ * q.2.2, q.2.2))
  left_inv p := by
    ext
    · dsimp only; ring
    · dsimp only; ring
    · dsimp only; ring
    · rfl
  right_inv q := by
    ext
    · dsimp only; ring
    · dsimp only; ring
    · dsimp only; ring
    · rfl

@[simp]
theorem projHash2FiberChangeEquiv_apply (d : F.Desc) (α ρ δ₁ δ₂ ξ τ₂ : ZMod (F.order d)) :
    projHash2FiberChangeEquiv F d α ρ ((δ₁, δ₂), (ξ, τ₂)) =
      ((δ₁ - α * (ξ - ρ * τ₂), ξ - ρ * τ₂), (δ₂ - α * τ₂, τ₂)) :=
  rfl

/-- Further conditioning on `ξ = τ₁ + ρ * τ₂` (so `τ₁ = ξ - ρ * τ₂`) makes the challenge tag on
`(β • g, γ • g, ρ)` equal to `(β * (δ₁ + ρ * δ₂) + (γ - α * β) * ξ) • g`, independent of `τ₂`. -/
theorem projHash2_fiber_challenge_eq (d : F.Desc) (α β γ δ₁ δ₂ ξ τ₂ ρ : ZMod (F.order d)) :
    projHash2 F d (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂) (δ₂ - α * τ₂) τ₂ ρ
      (β • F.generator d) (γ • F.generator d) =
      (β * (δ₁ + ρ * δ₂) + (γ - α * β) * ξ) • F.generator d := by
  rw [projHash2_fiber_eq]
  congr 1
  ring

/-- Further conditioning on `ξ = τ₁ + ρ * τ₂` (so `τ₁ = ξ - ρ * τ₂`), a query on
`(β' • g, γ' • g, ρ')` evaluates to
`(β' * (δ₁ + ρ' * δ₂) + (γ' - α * β') * ξ + (γ' - α * β') * (ρ' - ρ) * τ₂) • g`. -/
theorem projHash2_fiber_query_eq (d : F.Desc) (α β' γ' δ₁ δ₂ ξ τ₂ ρ ρ' : ZMod (F.order d)) :
    projHash2 F d (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂) (δ₂ - α * τ₂) τ₂ ρ'
      (β' • F.generator d) (γ' • F.generator d) =
      ((β' * (δ₁ + ρ' * δ₂) + (γ' - α * β') * ξ) +
        ((γ' - α * β') * (ρ' - ρ)) * τ₂) • F.generator d := by
  rw [projHash2_fiber_eq]
  congr 1
  ring

/-- The affine bijection
`τ₂ ↦ (β' * (δ₁ + ρ' * δ₂) + (γ' - α * β') * ξ) + ((γ' - α * β') * (ρ' - ρ)) * τ₂`
on `ZMod (F.order d)` when `γ' ≠ α * β'` and `ρ' ≠ ρ`. -/
def projHash2QueryFiberEquiv (d : F.Desc) {α β' γ' ρ ρ' : ZMod (F.order d)}
    (hγ' : γ' ≠ α * β') (hρ : ρ' ≠ ρ) (δ₁ δ₂ ξ : ZMod (F.order d)) :
    ZMod (F.order d) ≃ ZMod (F.order d) :=
  (Equiv.mulLeft₀ ((γ' - α * β') * (ρ' - ρ))
    (mul_ne_zero (sub_ne_zero.mpr hγ') (sub_ne_zero.mpr hρ))).trans
    (Equiv.addLeft (β' * (δ₁ + ρ' * δ₂) + (γ' - α * β') * ξ))

@[simp]
theorem projHash2QueryFiberEquiv_apply (d : F.Desc) {α β' γ' ρ ρ' : ZMod (F.order d)}
    (hγ' : γ' ≠ α * β') (hρ : ρ' ≠ ρ) (δ₁ δ₂ ξ τ₂ : ZMod (F.order d)) :
    projHash2QueryFiberEquiv F d hγ' hρ δ₁ δ₂ ξ τ₂ =
      (β' * (δ₁ + ρ' * δ₂) + (γ' - α * β') * ξ) + ((γ' - α * β') * (ρ' - ρ)) * τ₂ := by
  simp only [projHash2QueryFiberEquiv, Equiv.trans_apply, Equiv.mulLeft₀_apply,
    Equiv.coe_addLeft]

/-- **Single-tuple ingredient of Lemma 12.8 via Lemma 12.7 (bijection on the `τ₂`-fiber)**
([BonehShoup2023], Section 12.5.2, printed pp. 487–488): under the change of variables
`projHash2FiberChangeEquiv`, for any `γ' ≠ α * β'` and `ρ' ≠ ρ`, the map
`τ₂ ↦ projHash2 F d (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂) (δ₂ - α * τ₂) τ₂ ρ' (β' • g) (γ' • g)`
is a bijection from `ZMod (F.order d)` to `F.Carrier d`. -/
theorem projHash2_fiber_bijective_of_ne (d : F.Desc) {α β' γ' ρ ρ' : ZMod (F.order d)}
    (hγ' : γ' ≠ α * β') (hρ : ρ' ≠ ρ) (δ₁ δ₂ ξ : ZMod (F.order d)) :
    Function.Bijective (fun τ₂ : ZMod (F.order d) =>
      projHash2 F d (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂) (δ₂ - α * τ₂) τ₂ ρ'
        (β' • F.generator d) (γ' • F.generator d)) := by
  have hcomp :
      (fun τ₂ : ZMod (F.order d) =>
        projHash2 F d (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂) (δ₂ - α * τ₂) τ₂ ρ'
          (β' • F.generator d) (γ' • F.generator d)) =
      (fun x : ZMod (F.order d) => x • F.generator d) ∘
        projHash2QueryFiberEquiv F d hγ' hρ δ₁ δ₂ ξ := by
    funext τ₂
    rw [Function.comp_apply, projHash2QueryFiberEquiv_apply, projHash2_fiber_query_eq]
  rw [hcomp]
  exact (F.smul_generator_bijective d).comp (projHash2QueryFiberEquiv F d hγ' hρ δ₁ δ₂ ξ).bijective

/-- **Single-tuple ingredient of Lemma 12.8 via Lemma 12.7 (`1 / q` hit law on the `τ₂`-fiber)**
([BonehShoup2023], Section 12.5.2, printed pp. 487–488): under `projHash2FiberChangeEquiv`, fixing
`δ₁ = σ₁ + α * τ₁`, `δ₂ = σ₂ + α * τ₂`, and `ξ = τ₁ + ρ * τ₂` (which completely determine
`(h₁, h₂)`, the challenge tag `z`, and all DH queries), as `τ₂` varies uniformly over
`ZMod (F.order d)`, the tag on any non-DH query `(β' • g, γ' • g, ρ')` hits any target
`z' : F.Carrier d` with probability `(F.order d : ℝ≥0∞)⁻¹` whenever `γ' ≠ α * β'` and `ρ' ≠ ρ`. -/
theorem uniform_projHash2_fiber_apply (d : F.Desc) {α β' γ' ρ ρ' : ZMod (F.order d)}
    (hγ' : γ' ≠ α * β') (hρ : ρ' ≠ ρ) (δ₁ δ₂ ξ : ZMod (F.order d)) (z' : F.Carrier d) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).map (fun τ₂ =>
      projHash2 F d (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂) (δ₂ - α * τ₂) τ₂ ρ'
        (β' • F.generator d) (γ' • F.generator d))) z' = (F.order d : ℝ≥0∞)⁻¹ := by
  obtain ⟨ζ, rfl⟩ := F.smul_generator_surjective d z'
  have hmap :
      (PMF.uniformOfFintype (ZMod (F.order d))).map (fun τ₂ =>
        projHash2 F d (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂) (δ₂ - α * τ₂) τ₂ ρ'
          (β' • F.generator d) (γ' • F.generator d)) =
      (PMF.uniformOfFintype (ZMod (F.order d))).map (fun x => x • F.generator d) := by
    have hcomp :
        (fun τ₂ : ZMod (F.order d) =>
          projHash2 F d (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂) (δ₂ - α * τ₂) τ₂ ρ'
            (β' • F.generator d) (γ' • F.generator d)) =
        (fun x : ZMod (F.order d) => x • F.generator d) ∘
          projHash2QueryFiberEquiv F d hγ' hρ δ₁ δ₂ ξ := by
      funext τ₂
      rw [Function.comp_apply, projHash2QueryFiberEquiv_apply, projHash2_fiber_query_eq]
    rw [hcomp, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv]
  classical
  rw [hmap, PMF.map_apply]
  have hsingle :
      (∑' x : ZMod (F.order d),
        if ζ • F.generator d = x • F.generator d then
          (PMF.uniformOfFintype (ZMod (F.order d))) x
        else 0) =
      (PMF.uniformOfFintype (ZMod (F.order d))) ζ := by
    rw [← tsum_ite_eq ζ (fun x => (PMF.uniformOfFintype (ZMod (F.order d))) x)]
    refine tsum_congr fun x => ?_
    by_cases hx : x = ζ
    · subst hx; simp
    · have hne : ζ • F.generator d ≠ x • F.generator d :=
        fun h => hx ((F.smul_generator_injective d h).symm)
      simp [hx, hne]
  rw [hsingle, PMF.uniformOfFintype_apply, ZMod.card]

/-- **Finite-list `Q / q` union-bound ingredient of Lemma 12.8 on the `τ₂`-fiber**
([BonehShoup2023], Section 12.5.2, printed p. 488): for any list `queries` of candidate tuples
`(β', γ', ρ', z')` all satisfying `γ' ≠ α * β'` and `ρ' ≠ ρ`, and any fixed `δ₁, δ₂, ξ : ZMod q`,
the probability over uniform `τ₂ : ZMod (F.order d)` that at least one tuple in `queries` has tag
`z'` is at most `(queries.length : ℝ≥0∞) / (F.order d : ℝ≥0∞)`. -/
theorem uniform_projHash2_fiber_any_le (d : F.Desc) [DecidableEq (F.Carrier d)]
    (α ρ δ₁ δ₂ ξ : ZMod (F.order d))
    (queries : List (ZMod (F.order d) × ZMod (F.order d) × ZMod (F.order d) × F.Carrier d))
    (hq : ∀ q ∈ queries, q.2.1 ≠ α * q.1 ∧ q.2.2.1 ≠ ρ) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).map (fun τ₂ =>
      queries.any (fun q =>
        decide (projHash2 F d (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂) (δ₂ - α * τ₂) τ₂ q.2.2.1
          (q.1 • F.generator d) (q.2.1 • F.generator d) = q.2.2.2)))) true ≤
      (queries.length : ℝ≥0∞) / (F.order d : ℝ≥0∞) := by
  let μ := PMF.uniformOfFintype (ZMod (F.order d))
  let hit (q : ZMod (F.order d) × ZMod (F.order d) × ZMod (F.order d) × F.Carrier d)
      (τ₂ : ZMod (F.order d)) : Bool :=
    decide (projHash2 F d (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂) (δ₂ - α * τ₂) τ₂ q.2.2.1
      (q.1 • F.generator d) (q.2.1 • F.generator d) = q.2.2.2)
  induction queries with
  | nil =>
    simp
  | cons q qs ih =>
    have hq_head : q.2.1 ≠ α * q.1 ∧ q.2.2.1 ≠ ρ := hq q List.mem_cons_self
    have hq_tail : ∀ q' ∈ qs, q'.2.1 ≠ α * q'.1 ∧ q'.2.2.1 ≠ ρ :=
      fun q' hmem => hq q' (List.mem_cons_of_mem q hmem)
    have hor :
        (μ.map (fun τ₂ => (q :: qs).any (fun q' => hit q' τ₂))) true ≤
          (μ.map (hit q)) true + (μ.map (fun τ₂ => qs.any (fun q' => hit q' τ₂))) true := by
      simp only [List.any_cons, PMF.map_apply, ← tsum_add]
      refine tsum_le_tsum fun τ₂ => ?_
      cases hit q τ₂ <;> cases qs.any (fun q' => hit q' τ₂) <;> simp
    have hsingle : (μ.map (hit q)) true = (F.order d : ℝ≥0∞)⁻¹ := by
      have heq :
          (μ.map (hit q)) true =
            (μ.map (fun τ₂ =>
              projHash2 F d (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂) (δ₂ - α * τ₂) τ₂ q.2.2.1
                (q.1 • F.generator d) (q.2.1 • F.generator d))) q.2.2.2 := by
        rw [PMF.map_apply, PMF.map_apply]
        refine tsum_congr fun τ₂ => ?_
        dsimp only [hit]
        split_ifs with h₁ h₂ h₂
        · rfl
        · exfalso; exact h₂ (decide_eq_true_iff.mp h₁.symm).symm
        · exfalso; exact h₁ (decide_eq_true h₂.symm).symm
        · rfl
      rw [heq]
      exact uniform_projHash2_fiber_apply F d hq_head.1 hq_head.2 δ₁ δ₂ ξ q.2.2.2
    refine hor.trans ?_
    rw [hsingle, List.length_cons, Nat.cast_add, Nat.cast_one, ENNReal.add_div, one_div, add_comm]
    exact add_le_add_left (ih hq_tail) _

/-- Explicit 4-tuple linear equivalence
`(σ₁, τ₁, σ₂, τ₂) ↦ ((σ₁ + α * τ₁, σ₂ + α * τ₂), (z, z'))`
on `(ZMod (F.order d) × ZMod (F.order d)) × (ZMod (F.order d) × ZMod (F.order d))` when
`γ ≠ α * β`, `γ' ≠ α * β'`, and `ρ' ≠ ρ` ([BonehShoup2023], proof of Lemma 12.7, printed p. 487). -/
def projHash2Equiv (d : F.Desc) {α β γ β' γ' ρ ρ' : ZMod (F.order d)}
    (hγ : γ ≠ α * β) (hγ' : γ' ≠ α * β') (hρ : ρ' ≠ ρ) :
    (ZMod (F.order d) × ZMod (F.order d)) × (ZMod (F.order d) × ZMod (F.order d)) ≃
      (ZMod (F.order d) × ZMod (F.order d)) × (ZMod (F.order d) × ZMod (F.order d)) where
  toFun p :=
    ((p.1.1 + α * p.1.2, p.2.1 + α * p.2.2),
      (β * (p.1.1 + ρ * p.2.1) + γ * (p.1.2 + ρ * p.2.2),
        β' * (p.1.1 + ρ' * p.2.1) + γ' * (p.1.2 + ρ' * p.2.2)))
  invFun q :=
    let δ₁ := q.1.1
    let δ₂ := q.1.2
    let ξ := (γ - α * β)⁻¹ * (q.2.1 - β * (δ₁ + ρ * δ₂))
    let ξ' := (γ' - α * β')⁻¹ * (q.2.2 - β' * (δ₁ + ρ' * δ₂))
    let τ₂ := (ρ' - ρ)⁻¹ * (ξ' - ξ)
    let τ₁ := ξ - ρ * τ₂
    ((δ₁ - α * τ₁, τ₁), (δ₂ - α * τ₂, τ₂))
  left_inv p := by
    have hne : γ - α * β ≠ 0 := sub_ne_zero.mpr hγ
    have hne' : γ' - α * β' ≠ 0 := sub_ne_zero.mpr hγ'
    have hneρ : ρ' - ρ ≠ 0 := sub_ne_zero.mpr hρ
    have hξ :
        (γ - α * β)⁻¹ *
          (β * (p.1.1 + ρ * p.2.1) + γ * (p.1.2 + ρ * p.2.2) -
            β * (p.1.1 + α * p.1.2 + ρ * (p.2.1 + α * p.2.2))) =
        p.1.2 + ρ * p.2.2 := by
      have hsub :
          β * (p.1.1 + ρ * p.2.1) + γ * (p.1.2 + ρ * p.2.2) -
            β * (p.1.1 + α * p.1.2 + ρ * (p.2.1 + α * p.2.2)) =
          (γ - α * β) * (p.1.2 + ρ * p.2.2) := by ring
      rw [hsub, inv_mul_cancel_left₀ hne]
    have hξ' :
        (γ' - α * β')⁻¹ *
          (β' * (p.1.1 + ρ' * p.2.1) + γ' * (p.1.2 + ρ' * p.2.2) -
            β' * (p.1.1 + α * p.1.2 + ρ' * (p.2.1 + α * p.2.2))) =
        p.1.2 + ρ' * p.2.2 := by
      have hsub :
          β' * (p.1.1 + ρ' * p.2.1) + γ' * (p.1.2 + ρ' * p.2.2) -
            β' * (p.1.1 + α * p.1.2 + ρ' * (p.2.1 + α * p.2.2)) =
          (γ' - α * β') * (p.1.2 + ρ' * p.2.2) := by ring
      rw [hsub, inv_mul_cancel_left₀ hne']
    have hτ₂ : (ρ' - ρ)⁻¹ * ((p.1.2 + ρ' * p.2.2) - (p.1.2 + ρ * p.2.2)) = p.2.2 := by
      have hsub : (p.1.2 + ρ' * p.2.2) - (p.1.2 + ρ * p.2.2) = (ρ' - ρ) * p.2.2 := by ring
      rw [hsub, inv_mul_cancel_left₀ hneρ]
    ext <;> dsimp only <;> rw [hξ, hξ', hτ₂] <;> ring
  right_inv q := by
    have hne : γ - α * β ≠ 0 := sub_ne_zero.mpr hγ
    have hne' : γ' - α * β' ≠ 0 := sub_ne_zero.mpr hγ'
    have hneρ : ρ' - ρ ≠ 0 := sub_ne_zero.mpr hρ
    ext
    · dsimp only; ring
    · dsimp only; ring
    · dsimp only
      set ξ := (γ - α * β)⁻¹ * (q.2.1 - β * (q.1.1 + ρ * q.1.2))
      set ξ' := (γ' - α * β')⁻¹ * (q.2.2 - β' * (q.1.1 + ρ' * q.1.2))
      set τ₂ := (ρ' - ρ)⁻¹ * (ξ' - ξ)
      have hlin :
          β * (q.1.1 - α * (ξ - ρ * τ₂) + ρ * (q.1.2 - α * τ₂)) +
            γ * (ξ - ρ * τ₂ + ρ * τ₂) =
          β * (q.1.1 + ρ * q.1.2) + (γ - α * β) * ξ := by ring
      rw [hlin]
      dsimp only [ξ]
      rw [mul_inv_cancel_left₀ hne]
      ring
    · dsimp only
      set ξ := (γ - α * β)⁻¹ * (q.2.1 - β * (q.1.1 + ρ * q.1.2))
      set ξ' := (γ' - α * β')⁻¹ * (q.2.2 - β' * (q.1.1 + ρ' * q.1.2))
      have hτ :
          ξ - ρ * ((ρ' - ρ)⁻¹ * (ξ' - ξ)) + ρ' * ((ρ' - ρ)⁻¹ * (ξ' - ξ)) = ξ' := by
        have hlin :
            ξ - ρ * ((ρ' - ρ)⁻¹ * (ξ' - ξ)) + ρ' * ((ρ' - ρ)⁻¹ * (ξ' - ξ)) =
            ξ + (ρ' - ρ) * ((ρ' - ρ)⁻¹ * (ξ' - ξ)) := by ring
        rw [hlin, mul_inv_cancel_left₀ hneρ]
        ring
      have hlin :
          β' * (q.1.1 - α * (ξ - ρ * ((ρ' - ρ)⁻¹ * (ξ' - ξ))) +
              ρ' * (q.1.2 - α * ((ρ' - ρ)⁻¹ * (ξ' - ξ)))) +
            γ' * (ξ - ρ * ((ρ' - ρ)⁻¹ * (ξ' - ξ)) + ρ' * ((ρ' - ρ)⁻¹ * (ξ' - ξ))) =
          β' * (q.1.1 + ρ' * q.1.2) +
            (γ' - α * β') * (ξ - ρ * ((ρ' - ρ)⁻¹ * (ξ' - ξ)) + ρ' * ((ρ' - ρ)⁻¹ * (ξ' - ξ))) := by
        ring
      rw [hlin, hτ]
      dsimp only [ξ']
      rw [mul_inv_cancel_left₀ hne']
      ring

/-- **Lemma 12.7 (`universal₂` projective hash 4-tuple bijection)**
([BonehShoup2023], Section 12.5.2, printed pp. 487–488): for any non-DH triples `γ ≠ α * β` and
`γ' ≠ α * β'` and any distinct tags `ρ' ≠ ρ`, the evaluation map
`((σ₁, τ₁), (σ₂, τ₂)) ↦ ((h₁, h₂), (f'(v, w, ρ), f'(v', w', ρ')))` is a bijection from
`(ZMod (F.order d) × ZMod (F.order d)) × (ZMod (F.order d) × ZMod (F.order d))` to
`(F.Carrier d × F.Carrier d) × (F.Carrier d × F.Carrier d)`. -/
theorem projHash2_bijective_of_ne (d : F.Desc) {α β γ β' γ' ρ ρ' : ZMod (F.order d)}
    (hγ : γ ≠ α * β) (hγ' : γ' ≠ α * β') (hρ : ρ' ≠ ρ) :
    Function.Bijective
      (fun p : (ZMod (F.order d) × ZMod (F.order d)) × (ZMod (F.order d) × ZMod (F.order d)) =>
        (projHash2Aux F d p.1.1 p.1.2 p.2.1 p.2.2 (α • F.generator d),
          (projHash2 F d p.1.1 p.1.2 p.2.1 p.2.2 ρ (β • F.generator d) (γ • F.generator d),
            projHash2 F d p.1.1 p.1.2 p.2.1 p.2.2 ρ'
              (β' • F.generator d) (γ' • F.generator d)))) := by
  have hcomp :
      (fun p : (ZMod (F.order d) × ZMod (F.order d)) × (ZMod (F.order d) × ZMod (F.order d)) =>
        (projHash2Aux F d p.1.1 p.1.2 p.2.1 p.2.2 (α • F.generator d),
          (projHash2 F d p.1.1 p.1.2 p.2.1 p.2.2 ρ (β • F.generator d) (γ • F.generator d),
            projHash2 F d p.1.1 p.1.2 p.2.1 p.2.2 ρ'
              (β' • F.generator d) (γ' • F.generator d)))) =
      (Prod.map
        (Prod.map (fun x : ZMod (F.order d) => x • F.generator d)
          (fun y : ZMod (F.order d) => y • F.generator d))
        (Prod.map (fun x : ZMod (F.order d) => x • F.generator d)
          (fun y : ZMod (F.order d) => y • F.generator d))) ∘
        projHash2Equiv F d hγ hγ' hρ := by
    funext p
    simp [projHash2Equiv, projHash2Aux]
  rw [hcomp]
  exact (((F.smul_generator_bijective d).prodMap (F.smul_generator_bijective d)).prodMap
    ((F.smul_generator_bijective d).prodMap (F.smul_generator_bijective d))).comp
    (projHash2Equiv F d hγ hγ' hρ).bijective

/-- **Lemma 12.7 (`1 / q ^ 4` joint 4-tuple point mass)** ([BonehShoup2023], Section 12.5.2,
printed pp. 487–488): under uniform `((σ₁, τ₁), (σ₂, τ₂))`, for any non-DH triples `γ ≠ α * β` and
`γ' ≠ α * β'`, any distinct tags `ρ' ≠ ρ`, and any `h₁, h₂, z, z' : F.Carrier d`, the 4-tuple
`((h₁, h₂), (z, z'))` has probability `((F.order d : ℝ≥0∞) ^ 4)⁻¹`. -/
theorem uniform_projHash2_apply_of_ne (d : F.Desc) {α β γ β' γ' ρ ρ' : ZMod (F.order d)}
    (hγ : γ ≠ α * β) (hγ' : γ' ≠ α * β') (hρ : ρ' ≠ ρ) (h₁ h₂ z z' : F.Carrier d) :
    ((PMF.uniformOfFintype
      ((ZMod (F.order d) × ZMod (F.order d)) × (ZMod (F.order d) × ZMod (F.order d)))).map
      (fun p =>
        (projHash2Aux F d p.1.1 p.1.2 p.2.1 p.2.2 (α • F.generator d),
          (projHash2 F d p.1.1 p.1.2 p.2.1 p.2.2 ρ (β • F.generator d) (γ • F.generator d),
            projHash2 F d p.1.1 p.1.2 p.2.1 p.2.2 ρ'
              (β' • F.generator d) (γ' • F.generator d))))) ((h₁, h₂), (z, z')) =
      ((F.order d : ℝ≥0∞) ^ 4)⁻¹ := by
  obtain ⟨δ₁, rfl⟩ := F.smul_generator_surjective d h₁
  obtain ⟨δ₂, rfl⟩ := F.smul_generator_surjective d h₂
  obtain ⟨ζ₁, rfl⟩ := F.smul_generator_surjective d z
  obtain ⟨ζ₂, rfl⟩ := F.smul_generator_surjective d z'
  let Dom := (ZMod (F.order d) × ZMod (F.order d)) × (ZMod (F.order d) × ZMod (F.order d))
  let encodeQuad : Dom → (F.Carrier d × F.Carrier d) × (F.Carrier d × F.Carrier d) :=
    Prod.map
      (Prod.map (fun x => x • F.generator d) (fun y => y • F.generator d))
      (Prod.map (fun x => x • F.generator d) (fun y => y • F.generator d))
  have hinj : Function.Injective encodeQuad :=
    (((F.smul_generator_bijective d).prodMap (F.smul_generator_bijective d)).prodMap
      ((F.smul_generator_bijective d).prodMap (F.smul_generator_bijective d))).1
  have hmap :
      (PMF.uniformOfFintype Dom).map
        (fun p =>
          (projHash2Aux F d p.1.1 p.1.2 p.2.1 p.2.2 (α • F.generator d),
            (projHash2 F d p.1.1 p.1.2 p.2.1 p.2.2 ρ (β • F.generator d) (γ • F.generator d),
              projHash2 F d p.1.1 p.1.2 p.2.1 p.2.2 ρ'
                (β' • F.generator d) (γ' • F.generator d)))) =
      (PMF.uniformOfFintype Dom).map encodeQuad := by
    have hcomp :
        (fun p : Dom =>
          (projHash2Aux F d p.1.1 p.1.2 p.2.1 p.2.2 (α • F.generator d),
            (projHash2 F d p.1.1 p.1.2 p.2.1 p.2.2 ρ (β • F.generator d) (γ • F.generator d),
              projHash2 F d p.1.1 p.1.2 p.2.1 p.2.2 ρ'
                (β' • F.generator d) (γ' • F.generator d)))) =
        encodeQuad ∘ projHash2Equiv F d hγ hγ' hρ := by
      funext p
      simp [encodeQuad, projHash2Equiv, projHash2Aux]
    rw [hcomp, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv]
  classical
  change ((PMF.uniformOfFintype Dom).map
    (fun p =>
      (projHash2Aux F d p.1.1 p.1.2 p.2.1 p.2.2 (α • F.generator d),
        (projHash2 F d p.1.1 p.1.2 p.2.1 p.2.2 ρ (β • F.generator d) (γ • F.generator d),
          projHash2 F d p.1.1 p.1.2 p.2.1 p.2.2 ρ'
            (β' • F.generator d) (γ' • F.generator d)))))
    (encodeQuad ((δ₁, δ₂), (ζ₁, ζ₂))) = _
  rw [hmap, PMF.map_apply]
  have hcard : (Fintype.card Dom : ℝ≥0∞) = (F.order d : ℝ≥0∞) ^ 4 := by
    dsimp only [Dom]
    simp only [Fintype.card_prod, ZMod.card, Nat.cast_mul]
    ring
  simp [hinj.eq_iff, PMF.uniformOfFintype_apply, hcard]

end Cslib.Crypto.ProjectiveHash
