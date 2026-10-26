/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Encoding.Certificate
public import Complexity.Computability.Circuit.Boolean.PolynomialTime
public import Complexity.Computability.Circuit.Boolean.Substitution
import Complexity.Computability.Circuit.Complexity
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial advice

A machine *takes advice* when, on an input `x` of length `n`, it also reads a string `α n` that
depends only on `n` [Arora and Barak, Section 6.3][AroraBarak09]. With the advice placed in
front of the input as the pair `(α |x|, x)`, encoded as `frame (α |x|) ++ x`, a language is in
`PAdvice` when it consists of the inputs whose pair lies in a problem decidable in polynomial time,
for advice of polynomial length. This is the class `⋃ DTIME(n ^ c) / n ^ d` of
[Arora and Barak, Theorem 6.18][AroraBarak09], the original definition of `P/poly`
[Karp and Lipton][KarpLipton1980].

Hardwiring the advice into circuits for the pairs gives circuits for the language: at each length
`n` the first `2 |α n| + 1` inputs are fixed to the bits of `frame (α n)`, which costs two gates for
the constants (`PPoly.of_advice`). With `P ⊆ P/poly` (`P_subset_PPolyOn`), every language in
`PAdvice` is in `PPoly` (`PAdvice_subset_PPoly`). The machine enters only through the hypothesis
that the problem of pairs is in `Complexity.P`. Conversely, evaluating circuits from an advice
string listing their certificates (`familyAdvice`, `evalAdvice`) in polynomial time
(`computableInPolyTime_evalAdvice`) shows `PPoly ⊆ PAdvice` (`PPoly_subset_PAdvice`), establishing
`PPoly = PAdvice` (`PPoly_eq_PAdvice`).

## Main definitions

* `Cslib.Circuits.Boolean.familyAdvice`: the advice string listing circuits up to a given length.
* `Cslib.Circuits.Boolean.evalAdvice`: circuit evaluation from an advice string.
* `Cslib.Circuits.Boolean.PAdvice`: polynomial time with polynomial advice.

## Main results

* `Cslib.Circuits.Boolean.PPoly.of_advice`: hardwiring advice of polynomial length into circuits
  of polynomial size.
* `Cslib.Circuits.Boolean.PPoly.exists_evalAdvice`: advice strings of polynomial length deciding a
  language in `P/poly` up to any polynomial input-length bound.
* `Cslib.Circuits.Boolean.computableInPolyTime_evalAdvice`,
  `Cslib.Circuits.Boolean.computableInPolyTime_evalAdvice_eval`: circuit evaluation from advice is
  polynomial-time, also with the polynomial bounds of `PPoly.exists_evalAdvice`.
* `Cslib.Circuits.Boolean.PAdvice_subset_PPoly`: `P/advice ⊆ P/poly`.
* `Cslib.Circuits.Boolean.PPoly_subset_PAdvice`: `P/poly ⊆ P/advice`.
* `Cslib.Circuits.Boolean.PPoly_eq_PAdvice`: `P/poly = P/advice`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.3][AroraBarak09]
* [R. M. Karp, R. J. Lipton, *Some connections between nonuniform and uniform complexity
  classes*][KarpLipton1980]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM ComputableInPolyTime

/-- **Hardwiring advice.** If `x ∈ L` exactly when `frame (α |x|) ++ x ∈ M`, with `M` in `P/poly`
and advice `α` of polynomial length, then `L` is in `P/poly`: fixing the first inputs of the
circuits for `M` to the bits of `frame (α n)` costs two gates. -/
theorem PPoly.of_advice {L M : Language Bool} (hM : M ∈ PPoly) (α : ℕ → List Bool)
    (hα : PolynomiallyBounded fun n => (α n).length)
    (h : ∀ x, x ∈ L ↔ frame (α x.length) ++ x ∈ M) : L ∈ PPoly := by
  set q := fun N => complexity interpretation (single (M.slice N))
  have hq : PolynomiallyBounded q := hM
  refine PolynomiallyBounded.mono_of_le (g := fun n => q (2 * (α n).length + 1 + n) + 2)
    (by fun_prop) fun n => ?_
  let a : Fin (frame (α n)).length → Bool := fun j => (frame (α n))[j]
  have ha : List.ofFn a = frame (α n) := List.ofFn_getElem
  have hslice : L.slice n = fun x => M.slice ((frame (α n)).length + n)
      (substitute (prependInputs a) x) := by
    funext x
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, Language.slice_eq_true_iff,
      substitute_prependInputs, List.ofFn_fin_append, h, List.length_ofFn, ha]
  have hc := complexity_substitute_le (prependInputs a) (M.slice ((frame (α n)).length + n))
  rwa [← hslice, length_frame] at hc

/-! ### Advice strings for circuit families -/

/-- The advice string listing the circuits `C 0, …, C N`, each with at most `s` gates: block `m`
holds the certificate of `C m` (`certificate`), padded with `false` to `certLength N s` bits. -/
def familyAdvice (N s : ℕ) (C : ∀ m, Circuit signature m 1) : List Bool :=
  (List.range (N + 1)).flatMap fun m =>
    certificate m s (C m).code.1 ((C m).outputs 0).toNat ++
      List.replicate (certLength N s - certLength m s) false

/-- The value on `x` of the circuit for inputs of length `x.length`, read with at most `s` gates
from the block at position `x.length` of an advice string `w` whose blocks have `width` bits.
Every advice string gives a value. -/
def evalAdvice (s width : ℕ) (w x : List Bool) : Bool :=
  evalOutput x (readCertificate x.length s (w.drop (x.length * width))).1
    (readCertificate x.length s (w.drop (x.length * width))).2

section Family

variable {N s : ℕ} {C : ∀ m, Circuit signature m 1}

private theorem length_familyAdvice_block (hs : ∀ m ≤ N, (C m).size ≤ s) {m : ℕ} (hm : m ≤ N) :
    (certificate m s (C m).code.1 ((C m).outputs 0).toNat ++
      List.replicate (certLength N s - certLength m s) false).length = certLength N s := by
  rw [List.length_append, length_certificate_code _ (hs m hm), List.length_replicate,
    Nat.add_sub_cancel' (certLength_mono_left hm s)]

/-- The advice string of circuits with at most `s` gates has `N + 1` blocks of `certLength N s`
bits. -/
theorem length_familyAdvice (hs : ∀ m ≤ N, (C m).size ≤ s) :
    (familyAdvice N s C).length = (N + 1) * certLength N s := by
  rw [familyAdvice, List.length_flatMap, List.map_congr_left fun m hm =>
    length_familyAdvice_block hs (Nat.lt_succ_iff.1 (List.mem_range.1 hm)), List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul]

/-- Block `m` of the advice string of a family starts with the certificate of `C m`. -/
private theorem drop_familyAdvice (hs : ∀ m ≤ N, (C m).size ≤ s) {m : ℕ} (hm : m ≤ N) :
    ∃ rest, (familyAdvice N s C).drop (m * certLength N s) =
      certificate m s (C m).code.1 ((C m).outputs 0).toNat ++ rest := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hprefix : ((List.range m).flatMap fun j =>
      certificate j s (C j).code.1 ((C j).outputs 0).toNat ++
        List.replicate (certLength (m + k) s - certLength j s) false).length =
      m * certLength (m + k) s := by
    rw [List.length_flatMap, List.map_congr_left fun j hj =>
      length_familyAdvice_block hs (by have := List.mem_range.1 hj; omega), List.map_const',
      List.length_range, List.sum_replicate, smul_eq_mul]
  rw [familyAdvice, show m + k + 1 = m + (k + 1) by omega, List.range_add, List.flatMap_append,
    List.drop_left' hprefix, List.range_succ_eq_map, List.map_cons, List.flatMap_cons,
    Nat.add_zero, List.append_assoc]
  exact ⟨_, rfl⟩

/-- **Evaluation from the advice string of a family** is evaluation of its circuits, on inputs of
length at most `N`. -/
theorem evalAdvice_familyAdvice (hs : ∀ m ≤ N, (C m).size ≤ s) {x : List Bool}
    (hx : x.length ≤ N) :
    evalAdvice s (certLength N s) (familyAdvice N s C) x =
      (C x.length).eval interpretation (fun i => x[i]) 0 := by
  obtain ⟨rest, hrest⟩ := drop_familyAdvice hs hx
  rw [evalAdvice, hrest, readCertificate_certificate_code_append _ (hs _ hx),
    Circuit.eval_eq_evalOutput]
  simp only [Fin.getElem_fin, List.ofFn_getElem]

end Family

/-- **Evaluation from advice strings is polynomial-time**, for the number of gates and the block
width in unary. -/
@[fun_prop]
theorem computableInPolyTime_evalAdvice {γ : Type} {encIn : γ ↪ List Bool}
    {s width : γ → ℕ} {w x : γ → List Bool} (hs : ComputableInPolyTime s encIn encUnary)
    (hwidth : ComputableInPolyTime width encIn encUnary)
    (hw : ComputableInPolyTime w encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime (fun a => evalAdvice (s a) (width a) (w a) (x a)) encIn
      encBool := by
  have hm : ComputableInPolyTime (fun a => (x a).length) encIn encUnary :=
    length_bits.comp hx
  have hc := computableInPolyTime_readCertificate hm hs
    (hw.bitsDropWithInput (unary_mul.comp (hm.prod hwidth)))
  exact computableInPolyTime_evalOutput hx hc.fst' hc.snd'

/-- Evaluation from advice is polynomial-time with `S.eval n` gates in blocks of `W.eval n` bits,
for polynomials `S` and `W` of a length `n` in unary, the bounds of `PPoly.exists_evalAdvice`. -/
theorem computableInPolyTime_evalAdvice_eval {γ : Type} {encIn : γ ↪ List Bool}
    (S W : Polynomial ℕ) {n : γ → ℕ} {w x : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary) (hw : ComputableInPolyTime w encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime (fun a => evalAdvice (S.eval (n a)) (W.eval (n a)) (w a) (x a)) encIn
      encBool :=
  computableInPolyTime_evalAdvice ((unary_eval S).comp hn) ((unary_eval W).comp hn) hw hx

/-- **Polynomial time with polynomial advice** [Arora and Barak, Section 6.3][AroraBarak09]:
the languages `L` with advice `α` of polynomial length and a problem `A` of pairs, decidable in
polynomial time for the encoding `frame u ++ x` of `(u, x)`, such that `x ∈ L` exactly when
`(α |x|, x) ∈ A`. -/
def PAdvice : Set (Language Bool) :=
  {L | ∃ α : ℕ → List Bool, PolynomiallyBounded (fun n => (α n).length) ∧
    ∃ A ∈ Complexity.P (encPair encBits encBits), ∀ x, x ∈ L ↔ (α x.length, x) ∈ A}

/-- **P/advice ⊆ P/poly** [Arora and Barak, Theorem 6.18][AroraBarak09]: a language decided in
polynomial time with polynomial advice has circuits of polynomial size. -/
theorem PAdvice_subset_PPoly : PAdvice ⊆ PPoly := by
  rintro L ⟨α, hα, A, hA, hL⟩
  obtain ⟨M, hM, hAM⟩ := P_subset_PPolyOn hA
  exact PPoly.of_advice hM α hα fun x => (hL x).trans (hAM _)

/-- **Advice strings for `P/poly` up to a polynomial length bound.** For any language `L ∈ P/poly`
and polynomial `N : Polynomial ℕ`, there exist polynomials `S W P : Polynomial ℕ` (for the circuit
size bound, block width, and total advice length) and an advice family `α : ℕ → List Bool` of
polynomial length `(α n).length = P.eval n` such that `evalAdvice (S.eval n) (W.eval n) (α n) x`
decides `x ∈ L` for every `n` and every word `x` of length at most `N.eval n`. -/
theorem PPoly.exists_evalAdvice {L : Language Bool} (hL : L ∈ PPoly) (N : Polynomial ℕ) :
    ∃ (S W P : Polynomial ℕ) (α : ℕ → List Bool),
      (∀ n, (α n).length = P.eval n) ∧
      PolynomiallyBounded (fun n => (α n).length) ∧
      ∀ n (x : List Bool), x.length ≤ N.eval n →
        (evalAdvice (S.eval n) (W.eval n) (α n) x = true ↔ x ∈ L) := by
  obtain ⟨C, s, hs, hC⟩ := mem_PPoly_iff_exists_circuits.1 hL
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.1 hs
  let S : Polynomial ℕ := Polynomial.C c * (N + 1) ^ d
  let W : Polynomial ℕ := S + (N + S) + S * (3 + 2 * (N + S))
  let P : Polynomial ℕ := (N + 1) * W
  have hS (n : ℕ) : S.eval n = c * (N.eval n + 1) ^ d := by
    simp only [S, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_one]
  have hW (n : ℕ) : W.eval n = certLength (N.eval n) (S.eval n) := by
    simp only [W, certLength, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  have hP (n : ℕ) : P.eval n = (N.eval n + 1) * certLength (N.eval n) (S.eval n) := by
    simp only [P, hW, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one]
  have hsize (n : ℕ) : ∀ m ≤ N.eval n, (C m).size ≤ S.eval n := fun m hm =>
    ((hC m).1.trans (hcd m)).trans (by
      rw [hS]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) d))
  let α : ℕ → List Bool := fun n => familyAdvice (N.eval n) (S.eval n) C
  have hlen (n : ℕ) : (α n).length = P.eval n :=
    (length_familyAdvice (hsize n)).trans (hP n).symm
  have hα : PolynomiallyBounded fun n => (α n).length := by
    have hfun : (fun n => (α n).length) = fun n => P.eval n := funext hlen
    rw [hfun]
    fun_prop
  refine ⟨S, W, P, α, hlen, hα, fun n x hx => ?_⟩
  rw [hW, evalAdvice_familyAdvice (hsize n) hx, (hC _).2, single_apply,
    Language.slice_eq_true_iff]
  simp only [Fin.getElem_fin, List.ofFn_getElem]

/-- **P/poly ⊆ P/advice** [Arora and Barak, Theorem 6.18][AroraBarak09]: a language decided in
polynomial size has polynomial advice. -/
theorem PPoly_subset_PAdvice : PPoly ⊆ PAdvice := by
  intro L hL
  obtain ⟨S, W, _, α, -, hα, h_eval⟩ := PPoly.exists_evalAdvice hL Polynomial.X
  refine ⟨α, hα, {p : List Bool × List Bool |
    evalAdvice (S.eval p.2.length) (W.eval p.2.length) p.1 p.2 = true}, ?_, fun x => ?_⟩
  · refine ⟨fun p => evalAdvice (S.eval p.2.length) (W.eval p.2.length) p.1 p.2,
      ?_, fun _ => Iff.rfl⟩
    have hx : ComputableInPolyTime Prod.snd (encPair encBits encBits) encBits :=
      ComputableInPolyTime.snd _ _
    exact computableInPolyTime_evalAdvice_eval S W (length_bits.comp hx)
      (ComputableInPolyTime.fst _ _) hx
  · exact (h_eval x.length x (by simp)).symm

/-- **P/poly = P/advice** [Arora and Barak, Theorem 6.18][AroraBarak09]: the circuit class P/poly
equals the advice class P/advice. -/
theorem PPoly_eq_PAdvice : PPoly = (PAdvice : Set (Language Bool)) :=
  Set.Subset.antisymm PPoly_subset_PAdvice PAdvice_subset_PPoly

end Cslib.Circuits.Boolean
