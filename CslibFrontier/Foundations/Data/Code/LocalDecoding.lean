/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.LineCode.Basic
public import CslibFrontier.Foundations.Data.Code.ReedMuller
import CslibFrontier.Foundations.FieldTheory.Finite.UnitSum
import CslibFrontier.Foundations.Combinatorics.LineCode.Line
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Local decoding of Reed–Muller codes along lines

Let `F` be a finite field with `q` elements and let `f` be a codeword of the Reed–Muller code of
degree `d` in `m` variables over `F`, the evaluation table of a polynomial of total degree at most
`d`. Along every affine line `c ↦ x + c • v` the codeword is a polynomial in `c` of degree at most
`d`, and the values of a polynomial of degree below `q - 1` sum to zero over `F`. So for
`d + 1 < q` the sum of `f` over every line vanishes
(`Cslib.Code.sum_add_smul_eq_zero_of_mem_reedMuller`), and the value of `f` at `x` is minus the
sum of its values on the punctured line `Cslib.LineCode.puncturedLine x v` of the `q - 1` points
`x + c • v` with `c ≠ 0`.

The *line decoder* `Cslib.Code.lineDecode w x v` reads a received word `w` at the `q - 1` points of
that punctured line only (`Cslib.Code.lineDecode_congr`) and returns minus their sum. This is the
basic local decoder of Reed–Muller codes, which interpolates the restriction of the received word to
a random line through `x` [Arora and Barak, Chapter 19][AroraBarak09], [GuruswamiRudraSudan2019];
interpolating a polynomial of degree below `q - 1` from all `q - 1` points other than `x` gives
minus their sum at `x`. On a codeword it returns the value at `x` for every direction
(`Cslib.Code.lineDecode_eq_of_mem_reedMuller`), and on a corrupted codeword it still does whenever
the punctured line avoids the corrupted points (`Cslib.Code.lineDecode_eq_of_disjoint`). By the
blocking bound `Cslib.LineCode.card_filter_not_disjoint_puncturedLine_le`, every corrupted point
other than `x` lies on the punctured lines of only `q - 1` of the `q ^ m - 1` nonzero directions, so
at most `(q - 1) * Δ(w, f)` nonzero directions make the decoder err
(`Cslib.Code.card_filter_lineDecode_ne_le`): for a uniformly random nonzero direction the decoder
reads `f x` from `w` with `q - 1` queries except with probability at most
`(q - 1) * Δ(w, f) / (q ^ m - 1)`. In particular, if `2 * (q - 1) * Δ(w, f) < q ^ m - 1`, more than
half of the nonzero directions recover `f x` at every point `x`
(`Cslib.Code.lt_two_mul_card_filter_lineDecode_eq`).

## Main definitions

* `Cslib.Code.lineDecode`: the line decoder.

## Main results

* `Cslib.Code.exists_natDegree_le_eval_eq_of_mem_reedMuller`: Reed–Muller codewords of degree `d`
  restrict to polynomials of degree at most `d` on lines.
* `Cslib.Code.sum_add_smul_eq_zero_of_mem_reedMuller`: Reed–Muller codewords of degree below
  `q - 1` sum to zero on every line.
* `Cslib.Code.lineDecode_congr`: the decoder queries only the punctured line.
* `Cslib.Code.lineDecode_eq_of_mem_reedMuller`: the decoder is exact on codewords.
* `Cslib.Code.lineDecode_eq_of_disjoint`: the decoder is exact on lines avoiding the errors.
* `Cslib.Code.card_filter_lineDecode_ne_le`: local decoding, few directions err.
* `Cslib.Code.lt_two_mul_card_filter_lineDecode_eq`: most directions recover the value.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*]
  [GuruswamiRudraSudan2019]
-/

@[expose] public section

namespace Cslib.Code

open Finset LineCode

variable {F : Type*} [Field F] [Fintype F] {m d : ℕ}

omit [Fintype F] in
/-- **Restriction to a line.** The restriction `t ↦ f (x + t • v)` of a codeword `f` of the
Reed–Muller code of degree `d` is a polynomial of degree at most `d`. -/
theorem exists_natDegree_le_eval_eq_of_mem_reedMuller {f : (Fin m → F) → F}
    (hf : f ∈ reedMuller F m d) (x v : Fin m → F) :
    ∃ g : Polynomial F, g.natDegree ≤ d ∧ ∀ t, g.eval t = f (x + t • v) := by
  obtain ⟨P, hP, rfl⟩ := mem_reedMuller.1 hf
  refine ⟨P.eval₂ Polynomial.C fun i => Polynomial.C (v i) * Polynomial.X + Polynomial.C (x i),
    (FiniteField.natDegree_eval₂_line_le P v x).trans hP, fun t => ?_⟩
  rw [FiniteField.eval_eval₂_line]
  congr 2
  funext i
  exact add_comm _ _

/-- **Line sums of Reed–Muller codewords.** For `d + 1 < q`, the values of a codeword of the
Reed–Muller code of degree `d` over a field with `q` elements sum to zero on every affine line
`c ↦ x + c • v`, including the degenerate line `v = 0`. -/
theorem sum_add_smul_eq_zero_of_mem_reedMuller (hd : d + 1 < Fintype.card F)
    {f : (Fin m → F) → F} (hf : f ∈ reedMuller F m d) (x v : Fin m → F) :
    ∑ c : F, f (x + c • v) = 0 := by
  obtain ⟨g, hg, hgeval⟩ := exists_natDegree_le_eval_eq_of_mem_reedMuller hf x v
  simp only [← hgeval]
  exact FiniteField.sum_eval_eq_zero_of_natDegree_lt (g := g) (by omega)

variable [DecidableEq F]

/-- The *line decoder*: the value at `x` read off a received word `w` along the direction `v`,
minus the sum of the values of `w` at the `q - 1` points `x + c • v` with `c ≠ 0`. -/
def lineDecode (w : (Fin m → F) → F) (x v : Fin m → F) : F :=
  -∑ c ∈ (univ : Finset F).erase 0, w (x + c • v)

/-- **Locality.** The line decoder queries the received word only at the points of the punctured
line `puncturedLine x v`, of which there are at most `q - 1`. -/
theorem lineDecode_congr {w w' : (Fin m → F) → F} {x v : Fin m → F}
    (h : ∀ y ∈ puncturedLine x v, w y = w' y) : lineDecode w x v = lineDecode w' x v := by
  rw [lineDecode, lineDecode, sum_congr rfl fun c hc =>
    h _ (mem_puncturedLine.2 ⟨c, ne_of_mem_erase hc, rfl⟩)]

/-- **The line decoder is exact on codewords.** For `d + 1 < q`, on a codeword `f` of the
Reed–Muller code of degree `d` the line decoder returns `f x` for every direction `v`. -/
theorem lineDecode_eq_of_mem_reedMuller (hd : d + 1 < Fintype.card F) {f : (Fin m → F) → F}
    (hf : f ∈ reedMuller F m d) (x v : Fin m → F) : lineDecode f x v = f x := by
  have h := sum_add_smul_eq_zero_of_mem_reedMuller hd hf x v
  rw [← add_sum_erase _ _ (mem_univ 0), zero_smul, add_zero] at h
  rw [lineDecode, neg_eq_iff_add_eq_zero, add_comm, h]

/-- For `d + 1 < q`, if the punctured line through `x` in the direction `v` avoids the points where
the received word `w` differs from a codeword `f` of the Reed–Muller code of degree `d`, the line
decoder reads `f x` from `w`. An error at `x` itself is corrected. -/
theorem lineDecode_eq_of_disjoint (hd : d + 1 < Fintype.card F) {f w : (Fin m → F) → F}
    (hf : f ∈ reedMuller F m d) {x v : Fin m → F}
    (h : Disjoint (puncturedLine x v) ({y | w y ≠ f y} : Finset (Fin m → F))) :
    lineDecode w x v = f x := by
  rw [← lineDecode_eq_of_mem_reedMuller hd hf x v]
  refine lineDecode_congr fun y hy => ?_
  by_contra hne
  exact disjoint_left.1 h hy (mem_filter.2 ⟨mem_univ y, hne⟩)

/-- **Local decoding of Reed–Muller codes.** For `d + 1 < q`, let `w` be a received word and `f` a
codeword of the Reed–Muller code of degree `d` over a field with `q` elements. At every point `x`,
at most `(q - 1) * Δ(w, f)` of the `q ^ m - 1` nonzero directions `v` make the line decoder err. -/
theorem card_filter_lineDecode_ne_le (hd : d + 1 < Fintype.card F) {f : (Fin m → F) → F}
    (hf : f ∈ reedMuller F m d) (w : (Fin m → F) → F) (x : Fin m → F) :
    #{v ∈ univ.erase 0 | lineDecode w x v ≠ f x} ≤ hammingDist w f * (Fintype.card F - 1) := by
  let B : Finset (Fin m → F) := {y | w y ≠ f y}
  calc #{v ∈ univ.erase 0 | lineDecode w x v ≠ f x}
      ≤ #{v ∈ univ.erase 0 | ¬Disjoint (puncturedLine x v) B} :=
        card_le_card fun v hv => by
          rw [mem_filter] at hv ⊢
          exact ⟨hv.1, fun hdisj => hv.2 (lineDecode_eq_of_disjoint hd hf hdisj)⟩
    _ ≤ #(B.erase x) * (Fintype.card F - 1) := card_filter_not_disjoint_puncturedLine_le x B
    _ ≤ hammingDist w f * (Fintype.card F - 1) := Nat.mul_le_mul_right _ (card_erase_le)

/-- **Self-correction of Reed–Muller codes.** For `d + 1 < q`, if a received word `w` and a
codeword `f` of the Reed–Muller code of degree `d` over a field with `q` elements satisfy
`2 * (q - 1) * Δ(w, f) < q ^ m - 1`, then at every point `x` more than half of the `q ^ m - 1`
nonzero directions make the line decoder return `f x`. -/
theorem lt_two_mul_card_filter_lineDecode_eq (hd : d + 1 < Fintype.card F)
    {f w : (Fin m → F) → F} (hf : f ∈ reedMuller F m d)
    (h : 2 * (hammingDist w f * (Fintype.card F - 1)) < Fintype.card F ^ m - 1) (x : Fin m → F) :
    Fintype.card F ^ m - 1 < 2 * #{v ∈ univ.erase 0 | lineDecode w x v = f x} := by
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin m → F)).erase 0)
    (fun v => lineDecode w x v = f x)
  rw [card_erase_of_mem (mem_univ 0), card_univ, Fintype.card_fun, Fintype.card_fin] at hsplit
  have hne := card_filter_lineDecode_ne_le hd hf w x
  simp only [ne_eq] at hne
  omega

end Cslib.Code
