/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
public import CslibFrontier.Foundations.FieldTheory.TensorBasis
public import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.AdjoinRoot

/-!
# Explicit binary fields of composite degree

For distinct primes `mᵢ` with product `n`, each least-code irreducible binary polynomial
`Cslib.leastIrreducible mᵢ` has a root `αᵢ` in `𝔽_{2 ^ n} = GaloisField 2 n`
(`Cslib.AffineDisperser.binaryRoot`), and the monomials `∏ᵢ αᵢ ^ Jᵢ`, `Jᵢ < mᵢ`, form a basis of
`𝔽_{2 ^ n}` over `𝔽₂` (`Cslib.AffineDisperser.compositeBasis`). Arithmetic in this basis is
arithmetic in `𝔽₂[X₁, …, Xₖ] / (g₁(X₁), …, gₖ(Xₖ))`, which needs only the polynomials of small
degree `mᵢ`.

## Main definitions

* `Cslib.AffineDisperser.binaryRoot`: a root of `leastIrreducible p` in `GaloisField 2 n`, `p ∣ n`.
* `Cslib.AffineDisperser.compositeBasis`: the monomial basis of `GaloisField 2 (∏ᵢ mᵢ)` for distinct
  primes `mᵢ`.

## Main results

* `Cslib.AffineDisperser.exists_aeval_leastIrreducible_eq_zero`: `leastIrreducible p` has a root in
  `GaloisField 2 n` when `p ∣ n`.
* `Cslib.AffineDisperser.minpoly_binaryRoot`: when `p ∣ n` and `p, n ≠ 0`, the minimal polynomial of
  `binaryRoot p n` over `𝔽₂` is `leastIrreducible p`.

## References

* [R. Lidl, H. Niederreiter, *Finite Fields*, Chapters 1 and 3][LidlNiederreiter1997]
-/

@[expose] public section

namespace Cslib.AffineDisperser

open Module Polynomial

/-- `leastIrreducible p` has a root in `𝔽_{2 ^ n}` when `p ∣ n`. -/
theorem exists_aeval_leastIrreducible_eq_zero {p n : ℕ} (hp : p ≠ 0) (hn : n ≠ 0) (hpn : p ∣ n) :
    ∃ α : GaloisField 2 n, aeval α (leastIrreducible p) = 0 := by
  have hdeg : finrank (ZMod 2) (AdjoinRoot (leastIrreducible p)) = p := by
    rw [(AdjoinRoot.powerBasis (irreducible_leastIrreducible p).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, natDegree_leastIrreducible hp]
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod 2) (K := AdjoinRoot (leastIrreducible p)) (L := GaloisField 2 n)
    (by rw [hdeg, GaloisField.finrank 2 hn]; exact hpn)
  exact ⟨φ (AdjoinRoot.root _), by rw [aeval_algHom_apply, AdjoinRoot.aeval_eq,
    AdjoinRoot.mk_self, map_zero]⟩

open Classical in
/-- A root of `leastIrreducible p` in `𝔽_{2 ^ n}`, which exists when `p ∣ n` and `p, n ≠ 0`
(`0` when there is none). The root is chosen arbitrarily; the explicit disperser does not depend
on the choice (`Cslib.AffineDisperser.traceSymBits_rootBasis_eq_explicitDisperser`). -/
noncomputable def binaryRoot (p n : ℕ) : GaloisField 2 n :=
  if h : ∃ α : GaloisField 2 n, aeval α (leastIrreducible p) = 0 then h.choose else 0

/-- When `p ∣ n` and `p, n ≠ 0`, the minimal polynomial of `binaryRoot p n` over `𝔽₂` is
`leastIrreducible p`. -/
theorem minpoly_binaryRoot {p n : ℕ} (hp : p ≠ 0) (hn : n ≠ 0) (hpn : p ∣ n) :
    minpoly (ZMod 2) (binaryRoot p n) = leastIrreducible p := by
  have h := exists_aeval_leastIrreducible_eq_zero hp hn hpn
  rw [binaryRoot, dite_eq_left h]
  exact (minpoly.eq_of_irreducible_of_monic (irreducible_leastIrreducible p) h.choose_spec
    (monic_leastIrreducible p)).symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The monomial basis of `𝔽_{2 ^ n}`**, `n = ∏ᵢ mᵢ` for distinct primes `mᵢ`: the monomials
`∏ᵢ αᵢ ^ Jᵢ`, `Jᵢ < mᵢ`, in roots `αᵢ = binaryRoot mᵢ n` of the irreducible polynomials
`leastIrreducible mᵢ`. -/
noncomputable def compositeBasis (m : ι → ℕ) (hm : ∀ i, (m i).Prime)
    (hinj : Function.Injective m) :
    Basis ((i : ι) → Fin (m i)) (ZMod 2) (GaloisField 2 (∏ i, m i)) :=
  have hn : ∏ i, m i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hm i).ne_zero
  prodPowBasis (α := fun i => binaryRoot (m i) (∏ i, m i))
    (fun i j hij => (Nat.coprime_primes (hm i) (hm j)).2 (hinj.ne hij))
    (GaloisField.finrank 2 hn) fun i => by
      rw [minpoly_binaryRoot (hm i).ne_zero hn (Finset.dvd_prod_of_mem m (Finset.mem_univ i)),
        natDegree_leastIrreducible (hm i).ne_zero]

/-- The basis vector of `compositeBasis` at exponents `J` is the monomial `∏ᵢ αᵢ ^ Jᵢ` in the roots
`αᵢ = binaryRoot mᵢ (∏ᵢ mᵢ)`. -/
theorem compositeBasis_apply (m : ι → ℕ) (hm : ∀ i, (m i).Prime) (hinj : Function.Injective m)
    (J : (i : ι) → Fin (m i)) :
    compositeBasis m hm hinj J = ∏ i, binaryRoot (m i) (∏ i, m i) ^ (J i : ℕ) := by
  unfold compositeBasis
  exact prodPowBasis_apply _ _ _ J

end Cslib.AffineDisperser
