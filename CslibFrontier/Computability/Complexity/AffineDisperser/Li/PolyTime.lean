/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser
public import CslibFrontier.Computability.Complexity.AffineDisperser.PolyTime
public import CslibFrontier.Computability.Complexity.AffineDisperser.Li.ShoupIrreducible
public import CslibFrontier.Computability.Complexity.AffineDisperser.Li.ShoupPolyTime
public import CslibFrontier.Computability.Complexity.Classes.P.Slices
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Cslib.Computability.Languages.Slice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Polynomial-Time Explicit Affine Disperser via Shoup's Irreducible Polynomials

This module certifies polynomial-time computability (`Turing.MultiTapeTM.ComputableInPolyTime`
and membership in `Cslib.Complexity.P`) for `primeMulTable`, `primeDisperserBits`, and
`primeDisperser` from `CslibFrontier.Computability.Complexity.AffineDisperser.Li.ShoupIrreducible`.
Together with `Cslib.Circuits.Boolean.AffineDisperser.seven_mul_le_two_mul_size_add`, this yields
an unconditional explicit polynomial-time affine disperser in `P` for dimension `O(N ^ (4 / 5))`
and a `3.5 * N - O(N ^ (4 / 5))` Boolean circuit size lower bound over `B₂` (Milestone 1 toward
Issue #4323; the full `O(log N)` dimension construction of [X. Li][Li2023] remains open).

## Main definitions

* `Cslib.AffineDisperser.Li.primeDisperserLanguage`: the language whose slice at length `N` is
  `primeDisperser N`.

## Main results

* `Cslib.AffineDisperser.Li.computableInPolyTime_primeSymDeg`: `primeSymDeg` is computable in
  polynomial time in unary.
* `Cslib.AffineDisperser.Li.computableInPolyTime_primeMulTable`: `primeMulTable` is computable in
  polynomial time.
* `Cslib.AffineDisperser.Li.computableInPolyTime_primeDisperserBits`: `primeDisperserBits` is
  computable in polynomial time.
* `Cslib.AffineDisperser.Li.computableInPolyTime_primeDisperser`: `fun x => primeDisperser
  x.length (BitString.ofList x.length x)` is computable in polynomial time.
* `Cslib.AffineDisperser.Li.primeDisperserLanguage_mem_P`: `(primeDisperserLanguage : Set
  (List Bool)) ∈ Cslib.Complexity.P Turing.MultiTapeTM.encBits`.
* `Cslib.AffineDisperser.Li.exists_mem_P_eventually_le_size_primeDisperser`: unconditional
  explicit `P` language with a `3.5 * N - 15036 * N ^ (4 / 5)` Boolean circuit size lower bound.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
* [V. Shoup, *New algorithms for finding irreducible polynomials over finite fields*][Shoup1990]
* [X. Li, *Two source extractors for asymptotically optimal entropy, and (many) more*][Li2023]
-/

public section

namespace Cslib.AffineDisperser.Li

open Cslib.Circuits Filter Turing.MultiTapeTM ComputableInPolyTime

attribute [local irreducible] ComputableInPolyTime ComputableTidilyInPolyTime

/-- `primeSymDeg` is computable in polynomial time in unary. -/
@[fun_prop]
theorem computableInPolyTime_primeSymDeg :
    ComputableInPolyTime primeSymDeg encUnary encUnary := by
  unfold primeSymDeg
  fun_prop

/-- `primeMulTable` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_primeMulTable :
    ComputableInPolyTime primeMulTable encBits encTable := by
  have hcell : ComputableTidilyInPolyTime
      (fun q : ((ℕ × List (List Bool)) × ℕ) × ℕ => q.1.1.2.getD (q.1.2 + q.2) [])
      (encPair (encPair (encPair encUnary (encList encBits)) encUnary) encUnary) encBits := by
    simpa only [Function.comp_def] using
      (ComputableTidilyInPolyTime.listGetD (encA := encBits) (encL := encList encBits) []).comp
        (by fun_prop : ComputableTidilyInPolyTime
          (fun q : ((ℕ × List (List Bool)) × ℕ) × ℕ => (q.1.1.2, q.1.2 + q.2))
          (encPair (encPair (encPair encUnary (encList encBits)) encUnary) encUnary)
          (encPair (encList encBits) encUnary))
  have hrow : ComputableTidilyInPolyTime
      (fun p : (ℕ × List (List Bool)) × ℕ =>
        (List.range p.1.1).map fun v => p.1.2.getD (p.2 + v) [])
      (encPair (encPair encUnary (encList encBits)) encUnary) (encList encBits) :=
    ComputableTidilyInPolyTime.mapWithInput (by fun_prop) hcell
  have houter : ComputableTidilyInPolyTime
      (fun p : ℕ × List (List Bool) =>
        (List.range p.1).map fun u => (List.range p.1).map fun v => p.2.getD (u + v) [])
      (encPair encUnary (encList encBits)) encTable :=
    ComputableTidilyInPolyTime.mapWithInput (by fun_prop) hrow
  have hpair : ComputableInPolyTime (fun g : List Bool => (g.length - 1, powerTable g))
      encBits (encPair encUnary (encList encBits)) := by fun_prop
  have heq : primeMulTable = fun g : List Bool =>
      (List.range (g.length - 1)).map fun u =>
        (List.range (g.length - 1)).map fun v => (powerTable g).getD (u + v) [] := rfl
  rw [heq]
  simpa only [Function.comp_def] using houter.computableInPolyTime.comp hpair

/-- `primeDisperserBits` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_primeDisperserBits :
    ComputableInPolyTime (fun p : ℕ × List Bool => primeDisperserBits p.1 p.2)
      (encPair encUnary encBits) encBool := by
  simpa only [Function.comp_def, primeDisperserBits] using
    computableInPolyTime_traceSymCoords.comp
      ((((computableInPolyTime_primeMulTable.comp
            (computableInPolyTime_shoupIrreducibleBits.comp
              (computableInPolyTime_primeDeg.comp (fst encUnary encBits)))).prod
          (by fun_prop)).prod
        (computableInPolyTime_primeSymDeg.comp (fst encUnary encBits))).prod
      (snd encUnary encBits))

/-- The raw bit-list evaluator for `primeDisperser` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_primeDisperser :
    ComputableInPolyTime
      (fun x : List Bool => primeDisperser x.length (BitString.ofList x.length x))
      encBits encBool := by
  have heq :
      (fun x : List Bool => primeDisperser x.length (BitString.ofList x.length x)) =
        fun x : List Bool => primeDisperserBits x.length x := by
    funext x
    simp only [primeDisperser, BitString.ofFn_ofList rfl]
  rw [heq]
  simpa only [Function.comp_def, id_eq] using
    computableInPolyTime_primeDisperserBits.comp (length_bits.prod id')

/-- The language of the unconditional prime-degree Shoup affine disperser: its slice at length
`N` is `primeDisperser N`. -/
@[expose] noncomputable def primeDisperserLanguage : Language Bool :=
  Language.ofSlices primeDisperser

/-- The slice of `primeDisperserLanguage` at length `N` is `primeDisperser N`. -/
@[simp]
theorem slice_primeDisperserLanguage (N : ℕ) :
    primeDisperserLanguage.slice N = primeDisperser N :=
  Language.slice_ofSlices _ N

/-- `(primeDisperserLanguage : Set (List Bool))` belongs to `Cslib.Complexity.P encBits`. -/
theorem primeDisperserLanguage_mem_P :
    (primeDisperserLanguage : Set (List Bool)) ∈ Cslib.Complexity.P encBits :=
  Complexity.ofSlices_mem_P (f := primeDisperser) computableInPolyTime_primeDisperser

/-- Concrete `B₂` circuit size lower bound for `primeDisperser N` via
`Cslib.Circuits.Boolean.AffineDisperser.seven_mul_le_two_mul_size_add`. -/
theorem seven_mul_le_two_mul_size_add_primeThreshold {N : ℕ}
    (C : Circuit (fullSignature 2 Bool) N 1)
    (hC : C.Computes fullInterpretation (single (primeDisperser N))) :
    7 * N ≤ 2 * C.size + 14 * (primeThreshold N + 1) :=
  Boolean.AffineDisperser.seven_mul_le_two_mul_size_add (isAffineDisperser_primeDisperser N) C hC

/-- Every `B₂` circuit computing `primeDisperser N` has size at least
`3.5 * N - 15036 * N ^ (4 / 5)` for all sufficiently large `N`. -/
theorem eventually_le_size_of_computes_primeDisperser :
    ∀ᶠ N in atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
      C.Computes fullInterpretation (single (primeDisperser N)) →
        (7 : ℝ) / 2 * (N : ℝ) - 15036 * (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (C.size : ℝ) := by
  filter_upwards [eventually_primeThreshold_real_le] with N hleR C hC
  have hnatR : (7 : ℝ) * (N : ℝ) ≤ 2 * (C.size : ℝ) + 14 * ((primeThreshold N + 1 : ℕ) : ℝ) := by
    exact_mod_cast seven_mul_le_two_mul_size_add_primeThreshold C hC
  linarith

/-- Unconditional explicit language in `P` achieving the `3.5 * N - O(N ^ (4 / 5))` Boolean
circuit size lower bound over `B₂` via `primeDisperser`. This establishes Milestone 1 toward
Issue #4323; reducing the threshold dimension from `O(N ^ (4 / 5))` to `O(log N)` remains open. -/
theorem exists_mem_P_eventually_le_size_primeDisperser :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ Cslib.Complexity.P encBits ∧
      ∀ᶠ N in atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
        C.Computes fullInterpretation (single (L.slice N)) →
          (7 : ℝ) / 2 * (N : ℝ) - 15036 * (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (C.size : ℝ) :=
  ⟨primeDisperserLanguage, primeDisperserLanguage_mem_P, by
    simpa only [slice_primeDisperserLanguage] using
      eventually_le_size_of_computes_primeDisperser⟩

end Cslib.AffineDisperser.Li
