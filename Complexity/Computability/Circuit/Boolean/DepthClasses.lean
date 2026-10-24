/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.ModGates
public import Complexity.Computability.Circuit.Boolean.PPoly
public import Complexity.Computability.Circuit.Boolean.TC0

/-!
# The NC, AC and TC hierarchies

`PolylogDepth I i` is the class of languages decided, at every input length `n`, by circuits over
the Boolean basis `I` of polynomially bounded size and depth `O((log n) ^ i)`, with the explicit
envelope `c (⌊log₂ n⌋ + 1) ^ i`. Over the De Morgan basis of fan-in two this is **NCⁱ**, over the
unbounded fan-in basis **ACⁱ**, with majority gates **TCⁱ**, and with `MOD_q` gates **ACⁱ[q]**
[Arora and Barak, Section 6.7][AroraBarak09], [Vollmer, Chapter 4][Vollmer1999]. For `i = 0` these
are the constant-depth classes (`polylogDepth_zero`). Every hierarchy is monotone in `i`
(`PolylogDepth.mono_exponent`), and a meaning-preserving map of bases embeds the classes
(`PolylogDepth.mono`), so `NCⁱ ⊆ ACⁱ ⊆ TCⁱ` and `ACⁱ ⊆ ACⁱ[q]`. These classes are nonuniform.

## Main definitions

* `Cslib.Circuits.Boolean.PolylogDepth`: polynomial size and depth `O((log n) ^ i)`.
* `Cslib.Circuits.Boolean.NC`, `AC`, `TC`, `ACMod`: the hierarchies.

## Main results

* `Cslib.Circuits.Boolean.NC_subset_AC`, `AC_subset_TC`, `AC_subset_ACMod`: the inclusions.
* `Cslib.Circuits.Boolean.AC_zero`, `TC_zero`, `ACMod_zero`: the constant-depth classes.
* `Cslib.Circuits.Boolean.NC_subset_PPoly`: **NCⁱ ⊆ P/poly**.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {σ τ : Signature}

/-- The languages over `Bool` decided, at every input length `n`, by circuits over `I` of
polynomially bounded size and depth at most `c (⌊log₂ n⌋ + 1) ^ i` for a constant `c`. -/
def PolylogDepth (I : Interpretation σ Bool) (i : ℕ) : Set (Language Bool) :=
  DepthClass I fun n => (Nat.log 2 n + 1) ^ i

namespace PolylogDepth

variable {I : Interpretation σ Bool} {i j : ℕ}

/-- The hierarchy is monotone in the exponent. -/
theorem mono_exponent (hij : i ≤ j) : PolylogDepth I i ⊆ PolylogDepth I j :=
  DepthClass.mono_depth fun _ => Nat.pow_le_pow_right (by omega) hij

/-- A meaning-preserving map of bases embeds the classes. -/
theorem mono (φ : σ.Hom τ) {J : Interpretation τ Bool} [φ.Preserves I J] :
    PolylogDepth I i ⊆ PolylogDepth J i :=
  DepthClass.mono φ

end PolylogDepth

/-- For exponent zero, polynomial size and constant depth. -/
theorem polylogDepth_zero (I : Interpretation σ Bool) : PolylogDepth I 0 = ConstDepth I := by
  simp only [PolylogDepth, pow_zero, ConstDepth]

/-- **NCⁱ**: polynomial size and depth `O((log n) ^ i)` over the De Morgan basis of fan-in two. -/
def NC (i : ℕ) : Set (Language Bool) :=
  PolylogDepth interpretation i

/-- **ACⁱ**: polynomial size and depth `O((log n) ^ i)` with unbounded fan-in. -/
def AC (i : ℕ) : Set (Language Bool) :=
  PolylogDepth Unbounded.interpretation i

/-- **TCⁱ**: polynomial size and depth `O((log n) ^ i)` with majority gates. -/
def TC (i : ℕ) : Set (Language Bool) :=
  PolylogDepth (Unbounded.extInterpretation majority) i

/-- **ACⁱ[q]**: polynomial size and depth `O((log n) ^ i)` with `MOD_q` gates. -/
def ACMod (q i : ℕ) : Set (Language Bool) :=
  PolylogDepth (Unbounded.extInterpretation (modGate q)) i

/-- `AC 0` is `AC⁰`. -/
theorem AC_zero : AC 0 = AC0 :=
  polylogDepth_zero _

/-- `TC 0` is `TC⁰`. -/
theorem TC_zero : TC 0 = TC0 :=
  polylogDepth_zero _

/-- `ACMod q 0` is `AC⁰[q]`. -/
theorem ACMod_zero (q : ℕ) : ACMod q 0 = AC0Mod q :=
  polylogDepth_zero _

/-- **NCⁱ ⊆ ACⁱ.** -/
theorem NC_subset_AC (i : ℕ) : NC i ⊆ AC i :=
  PolylogDepth.mono Unbounded.deMorganToUnbounded

/-- **ACⁱ ⊆ TCⁱ.** -/
theorem AC_subset_TC (i : ℕ) : AC i ⊆ TC i :=
  PolylogDepth.mono Unbounded.toExt

/-- **ACⁱ ⊆ ACⁱ[q].** -/
theorem AC_subset_ACMod (q i : ℕ) : AC i ⊆ ACMod q i :=
  PolylogDepth.mono Unbounded.toExt

/-- `NC` is monotone in the depth exponent. -/
theorem NC_mono {i j : ℕ} (hij : i ≤ j) : NC i ⊆ NC j :=
  PolylogDepth.mono_exponent hij

/-- `AC` is monotone in the depth exponent. -/
theorem AC_mono {i j : ℕ} (hij : i ≤ j) : AC i ⊆ AC j :=
  PolylogDepth.mono_exponent hij

/-- `TC` is monotone in the depth exponent. -/
theorem TC_mono {i j : ℕ} (hij : i ≤ j) : TC i ⊆ TC j :=
  PolylogDepth.mono_exponent hij

/-- `ACMod q` is monotone in the depth exponent. -/
theorem ACMod_mono (q : ℕ) {i j : ℕ} (hij : i ≤ j) : ACMod q i ⊆ ACMod q j :=
  PolylogDepth.mono_exponent hij

/-- **`NCⁱ ⊆ P/poly`** for every `i`: a language decided by polynomial-size De Morgan circuits of
polylogarithmic depth has polynomially bounded circuit complexity. -/
theorem NC_subset_PPoly (i : ℕ) : NC i ⊆ PPoly := by
  rintro L ⟨c, s, hs, hC⟩
  refine hs.mono_of_le fun n => ?_
  obtain ⟨C, hCc, -, hCs⟩ := hC n
  exact (complexity_le_of_computes C hCc).trans hCs

end Cslib.Circuits.Boolean
