/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/RingTheory/AdjoinRoot.lean`)

public import Complexity.Init
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Reducing the coefficients of `R[X] / (g)`

For a ring homomorphism `φ : R →+* S` and `q ∣ g.map φ`, Mathlib's `AdjoinRoot.map φ g q` sends
`R[X] / (g)` to `S[X] / (q)`. This file computes it on classes of polynomials, shows that it is
surjective when `φ` is, and characterizes its kernel when `g` is monic and `q = g.map φ`: an element
vanishes exactly when the coefficients of its reduced representative do.

These facts are used both for Galois rings (`GaloisRing.residue`, reduction modulo `p`) and for the
`p`-adic valuation of `ℚ[X] / (f)` (`AdjoinRoot.padicValuation`).

## Main results

* `AdjoinRoot.map_mk`: the class of `P` maps to the class of `P.map φ`.
* `AdjoinRoot.map_surjective_of_surjective`: reducing the coefficients is surjective when `φ` is.
* `AdjoinRoot.map_eq_zero_iff`: an element of `R[X] / (g)` vanishes in `S[X] / (g.map φ)` exactly
  when the coefficients of its reduced representative do.
-/

public section

open Polynomial

namespace AdjoinRoot

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {g : R[X]}

/-- Reducing the coefficients maps the class of `P` to the class of `P.map φ`. -/
theorem map_mk (q : S[X]) (h : q ∣ g.map φ) (P : R[X]) :
    map φ g q h (mk g P) = mk q (P.map φ) := by
  have : (map φ g q h).comp (mk g) = (mk q).comp (mapRingHom φ) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [RingHom.comp_apply, mk_C, map_of, coe_mapRingHom, Polynomial.map_C]
    · simp only [RingHom.comp_apply, mk_X, map_root, coe_mapRingHom, Polynomial.map_X]
  exact congrArg (fun F : R[X] →+* AdjoinRoot q => F P) this

/-- Reducing the coefficients is surjective when `φ` is. -/
theorem map_surjective_of_surjective (q : S[X]) (h : q ∣ g.map φ)
    (hφ : Function.Surjective φ) : Function.Surjective (map φ g q h) := by
  intro y
  obtain ⟨Q, rfl⟩ := mk_surjective y
  obtain ⟨P, rfl⟩ := Polynomial.map_surjective φ hφ Q
  exact ⟨mk g P, map_mk φ q h P⟩

/-- **An element vanishes after reducing the coefficients** of a monic `g` exactly when the
coefficients of its representative of degree below `deg g` do: that representative reduces to a
polynomial of degree below `deg (g.map φ)`, which `g.map φ` divides only when it is zero. -/
theorem map_eq_zero_iff [Nontrivial S] (hg : g.Monic) {q : S[X]} (h : q ∣ g.map φ)
    (hq : q = g.map φ) (x : AdjoinRoot g) :
    map φ g q h x = 0 ↔ ∀ i, φ ((modByMonicHom hg x).coeff i) = 0 := by
  subst hq
  have := φ.domain_nontrivial
  obtain ⟨Q, rfl⟩ := mk_surjective x
  rw [modByMonicHom_mk]
  set P := Q %ₘ g
  have hx : mk g P = mk g Q := by
    have := mk_leftInverse hg (mk g Q)
    rwa [modByMonicHom_mk] at this
  have hdeg : (P.map φ).degree < (g.map φ).degree := by
    rw [hg.degree_map]
    exact degree_map_le.trans_lt (degree_modByMonic_lt _ hg)
  rw [← hx, map_mk, mk_eq_zero]
  constructor
  · intro hdvd i
    by_contra hne
    have h0 : P.map φ ≠ 0 := fun h0 => hne (by rw [← coeff_map, h0, coeff_zero])
    exact (hg.map φ).not_dvd_of_degree_lt h0 hdeg hdvd
  · intro h
    have : P.map φ = 0 := Polynomial.ext fun i => by rw [coeff_map, h, coeff_zero]
    rw [this]
    exact dvd_zero _

end AdjoinRoot
