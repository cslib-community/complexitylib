/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.PPoly
public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.MCSP.AntiChecker.Oracle
import CslibFrontier.Computability.Circuit.Boolean.PolynomialTime
import CslibFrontier.Computability.Complexity.Classes.PH.KarpLipton
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.AffineHash
import CslibFrontier.Foundations.Data.BitString.List

/-!
# The anti-checker oracle has polynomial-size circuits on its queries if NP does

Under `NP ⊆ P/poly`, the yes-queries of the anti-checker oracle
(`Cslib.MCSP.AntiChecker.smallSet`) lie in `P/poly` for their encoding
(`Cslib.MCSP.AntiChecker.smallSet_mem_PPolyOn`), so some language in `P/poly` agrees with the
anti-checker oracle on every query
(`Cslib.MCSP.AntiChecker.exists_mem_PPoly_agrees_antiCheckerOracle`).

A query is a no-query when the power of the consistent descriptions is large: there are `u + 1`
affine hash seeds, packed into one word `σ`, such that every target `z` of `u` bits has a tuple
`x` of `ℓ` certificates, each valid and agreeing with the samples, that one of the seeds sends to
`z`. This is an `∃ σ ∀ z ∃ x` statement over words of lengths polynomial in the unary parameters,
about a polynomial-time test built from the sample verifier `Cslib.MCSP.checkCertificateOn` and
the word affine hash `Cslib.BitString.LinearHash.wordAffineHash`. Nonuniform quantifier
elimination under `NP ⊆ P/poly`
(`Cslib.Complexity.PPolyOn.exists_of_computableInPolyTime_length`,
`Cslib.Complexity.PPolyOn.forall_of_computableInPolyTime_length`), from the proof of the
Karp–Lipton theorem [Karp and Lipton, Section 3][KarpLipton1980], removes the three quantifiers,
and closure under complement gives the yes-queries.

## Main results

* `Cslib.MCSP.AntiChecker.smallSet_mem_PPolyOn`: the yes-queries have polynomial-size circuits.
* `Cslib.MCSP.AntiChecker.exists_mem_PPoly_agrees_antiCheckerOracle`: a language in `P/poly`
  agrees with the anti-checker oracle on every query.

## References

* [R. M. Karp, R. J. Lipton, *Some connections between nonuniform and uniform complexity
  classes*][KarpLipton1980]
-/

public section

namespace Cslib.MCSP.AntiChecker

open Finset Circuits Circuits.Boolean Complexity Turing.MultiTapeTM ComputableInPolyTime

/-! ### The covering test -/

/-- Every row of `x`, read as `ℓ` certificates of length `certLength n s`, is a valid certificate
agreeing with the samples `P`. -/
private def rowsConsistent (n s ℓ : ℕ) (P : List (List Bool × Bool)) (x : List Bool) : Bool :=
  (BitString.listRows ℓ (certLength n s) x).all fun w =>
    checkCertificateOn P (·.1) (fun p out => out == p.2) n s w

/-- Some seed among rows `0, …, u` of `σ`, each a packed affine hash to `u` bits, sends `x` to
`z`. -/
private def hashesTo (u N : ℕ) (σ z x : List Bool) : Bool :=
  (List.range (u + 1)).any fun i =>
    decide (BitString.LinearHash.wordAffineHash u (BitString.listRow (u * N + u) i σ) x = z)

/-- The test of the covering certificate of a query `q`, with packed seeds `σ`, target `z` and
tuple `x`. -/
private def coverTest (r : ((Query × List Bool) × List Bool) × List Bool) : Bool :=
  rowsConsistent r.1.1.1.arity r.1.1.1.size r.1.1.1.power r.1.1.1.samples r.2 &&
    hashesTo r.1.1.1.threshold (r.1.1.1.power * certLength r.1.1.1.arity r.1.1.1.size)
      r.1.1.2 r.1.2 r.2

/-! ### The covering certificate -/

section Certificate

variable {n s ℓ u : ℕ} {P : List (List Bool × Bool)}

private theorem rowsConsistent_ofFn (x : BitString (ℓ * certLength n s)) :
    rowsConsistent n s ℓ P (List.ofFn x) = true ↔
      x ∈ BitString.blockPower (consistent (validCertificates n s)
        (fun w y => evalCertificate n s (List.ofFn w) y) P) ℓ := by
  rw [rowsConsistent, BitString.listRows_ofFn, List.all_eq_true, BitString.mem_blockPower]
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, mem_consistent,
    mem_validCertificates, checkCertificateOn, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]

private theorem hashesTo_ofFn {N : ℕ} (σ : List Bool) (y : BitString u) (x : BitString N) :
    hashesTo u N σ (List.ofFn y) (List.ofFn x) = true ↔
      ∃ i < u + 1, BitString.LinearHash.affineHash
        (BitString.LinearHash.unpackAffineSeed u N (BitString.listRow (u * N + u) i σ)) x = y := by
  simp only [hashesTo, List.any_eq_true, List.mem_range, decide_eq_true_eq,
    BitString.LinearHash.wordAffineHash_eq_ofFn, List.ofFn_inj]

/-- **The covering certificate**: the power of the consistent descriptions is large exactly when
some packed seeds `σ` cover every target `z` by a consistent tuple `x`. -/
private theorem isLarge_iff_exists :
    IsLarge u (BitString.blockPower (consistent (validCertificates n s)
        (fun w y => evalCertificate n s (List.ofFn w) y) P) ℓ) ↔
      ∃ σ : List Bool, σ.length = (u + 1) * (u * (ℓ * certLength n s) + u) ∧
        ∀ z : List Bool, z.length = u → ∃ x : List Bool, x.length = ℓ * certLength n s ∧
          (rowsConsistent n s ℓ P x && hashesTo u (ℓ * certLength n s) σ z x) = true := by
  constructor
  · rintro ⟨seeds, hc⟩
    have hlen : ∀ w ∈ List.ofFn fun i => BitString.LinearHash.packAffineSeed (seeds i),
        w.length = u * (ℓ * certLength n s) + u := by
      simp [List.mem_ofFn]
    refine ⟨(List.ofFn fun i => BitString.LinearHash.packAffineSeed (seeds i)).flatten, ?_,
      fun z hz => ?_⟩
    · simp [List.length_flatten, List.sum_replicate, Function.comp_def]
      ring
    obtain ⟨i, hi⟩ := hc (BitString.ofList u z)
    obtain ⟨x, hx, hxz⟩ := mem_image.1 hi
    refine ⟨List.ofFn x, List.length_ofFn, ?_⟩
    rw [← BitString.ofFn_ofList hz, Bool.and_eq_true, rowsConsistent_ofFn, hashesTo_ofFn]
    refine ⟨hx, i, i.isLt, ?_⟩
    rw [BitString.listRow_flatten hlen (by rw [List.length_ofFn]; exact i.isLt),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact i.isLt),
      Option.getD_some, List.getElem_ofFn]
    simpa using hxz
  · rintro ⟨σ, -, hσ⟩
    refine ⟨fun i => BitString.LinearHash.unpackAffineSeed u (ℓ * certLength n s)
      (BitString.listRow (u * (ℓ * certLength n s) + u) i σ), fun y => ?_⟩
    obtain ⟨x, hxlen, hx⟩ := hσ (List.ofFn y) List.length_ofFn
    rw [← BitString.ofFn_ofList hxlen, Bool.and_eq_true, rowsConsistent_ofFn, hashesTo_ofFn] at hx
    obtain ⟨hmem, i, hi, hhash⟩ := hx
    exact ⟨⟨i, hi⟩, mem_image.2 ⟨_, hmem, hhash⟩⟩

end Certificate

/-! ### Polynomial time -/

/-- The covering test is polynomial-time. -/
private theorem computableInPolyTime_coverTest :
    ComputableInPolyTime coverTest
      (encPair (encPair (encPair encQuery encBits) encBits) encBits) encBool := by
  let e1 := encPair encQuery encBits
  let e2 := encPair e1 encBits
  let e3 := encPair e2 encBits
  have hq : ComputableInPolyTime (fun r : ((Query × List Bool) × List Bool) × List Bool =>
      r.1.1.1) e3 encQuery :=
    (fst encQuery encBits).comp ((fst e1 encBits).comp (fst e2 encBits))
  have hσ : ComputableInPolyTime (fun r : ((Query × List Bool) × List Bool) × List Bool =>
      r.1.1.2) e3 encBits :=
    (snd encQuery encBits).comp ((fst e1 encBits).comp (fst e2 encBits))
  have hz : ComputableInPolyTime (fun r : ((Query × List Bool) × List Bool) × List Bool =>
      r.1.2) e3 encBits :=
    (snd e1 encBits).comp (fst e2 encBits)
  have hx : ComputableInPolyTime (fun r : ((Query × List Bool) × List Bool) × List Bool =>
      r.2) e3 encBits :=
    snd e2 encBits
  have hn := encQuery_arity_deg.computableInPolyTime.comp hq
  have hs := encQuery_size_deg.computableInPolyTime.comp hq
  have hℓ := encQuery_power_deg.computableInPolyTime.comp hq
  have hu := encQuery_threshold_deg.computableInPolyTime.comp hq
  have hP := encQuery_samples_deg.computableInPolyTime.comp hq
  have hL : ComputableInPolyTime (fun r : ((Query × List Bool) × List Bool) × List Bool =>
      certLength r.1.1.1.arity r.1.1.1.size) e3 encUnary := by
    unfold certLength
    fun_prop
  have hN : ComputableInPolyTime (fun r : ((Query × List Bool) × List Bool) × List Bool =>
      r.1.1.1.power * certLength r.1.1.1.arity r.1.1.1.size) e3 encUnary := by
    fun_prop
  have hrows : ComputableInPolyTime (fun r : ((Query × List Bool) × List Bool) × List Bool =>
      rowsConsistent r.1.1.1.arity r.1.1.1.size r.1.1.1.power r.1.1.1.samples r.2)
      e3 encBool := by
    have hcheck : ComputableInPolyTime
        (fun p : (((Query × List Bool) × List Bool) × List Bool) × List Bool =>
          checkCertificateOn p.1.1.1.1.samples (·.1) (fun q out => out == q.2)
            p.1.1.1.1.arity p.1.1.1.1.size p.2) (encPair e3 encBits) encBool := by
      have h1 := fst e3 encBits
      exact computableInPolyTime_checkCertificateOn (hn.comp h1) (hs.comp h1) (snd e3 encBits)
        (hP.comp h1) (fst encBits encBool)
        ((snd (encPair (encPair e3 encBits) (encPair encBits encBool)) encBool).beq
          ((snd encBits encBool).comp ((snd (encPair e3 encBits) (encPair encBits encBool)).comp
            (fst (encPair (encPair e3 encBits) (encPair encBits encBool)) encBool))))
    unfold rowsConsistent
    simp only [List.all_eq_not_any_not]
    exact bool_not.comp (anyWithInput (bitsRowsWithInput hℓ hL hx) (bool_not.comp hcheck))
  have hhash : ComputableInPolyTime (fun r : ((Query × List Bool) × List Bool) × List Bool =>
      hashesTo r.1.1.1.threshold (r.1.1.1.power * certLength r.1.1.1.arity r.1.1.1.size)
        r.1.1.2 r.1.2 r.2) e3 encBool := by
    have hrange : ComputableInPolyTime (fun r : ((Query × List Bool) × List Bool) × List Bool =>
        List.range (r.1.1.1.threshold + 1)) e3 (encList encUnary) := by
      fun_prop
    have h1 := fst e3 encUnary
    have hrow : ComputableInPolyTime
        (fun p : (((Query × List Bool) × List Bool) × List Bool) × ℕ =>
          BitString.listRow (p.1.1.1.1.threshold * (p.1.1.1.1.power *
            certLength p.1.1.1.1.arity p.1.1.1.1.size) + p.1.1.1.1.threshold) p.2 p.1.1.1.2)
        (encPair e3 encUnary) encBits :=
      bitsRowWithInput (unary_add' (unary_mul' (hu.comp h1) (hN.comp h1)) (hu.comp h1))
        (snd e3 encUnary) (hσ.comp h1)
    have htest : ComputableInPolyTime
        (fun p : (((Query × List Bool) × List Bool) × List Bool) × ℕ =>
          decide (BitString.LinearHash.wordAffineHash p.1.1.1.1.threshold
            (BitString.listRow (p.1.1.1.1.threshold * (p.1.1.1.1.power *
              certLength p.1.1.1.1.arity p.1.1.1.1.size) + p.1.1.1.1.threshold) p.2 p.1.1.1.2)
            p.1.2 = p.1.1.2)) (encPair e3 encUnary) encBool :=
      decide_eq' (BitString.LinearHash.computableInPolyTime_wordAffineHash (hu.comp h1) hrow
        (hx.comp h1)) (hz.comp h1)
    unfold hashesTo
    exact anyWithInput hrange htest
  unfold coverTest
  exact bool_and' hrows hhash

/-! ### Quantifier elimination -/

/-- **Under `NP ⊆ P/poly`, the yes-queries of the anti-checker oracle have polynomial-size
circuits.** -/
theorem smallSet_mem_PPolyOn (hNP : NP encBits ⊆ PPolyOn encBits) :
    smallSet ∈ PPolyOn encQuery := by
  let e1 := encPair encQuery encBits
  let e2 := encPair e1 encBits
  have hq2 : ComputableInPolyTime (fun r : (Query × List Bool) × List Bool => r.1.1) e2
      encQuery :=
    (fst encQuery encBits).comp (fst e1 encBits)
  have hq1 : ComputableInPolyTime (fun r : Query × List Bool => r.1) e1 encQuery :=
    fst encQuery encBits
  have hN : ComputableInPolyTime (fun r : (Query × List Bool) × List Bool =>
      r.1.1.power * certLength r.1.1.arity r.1.1.size) e2 encUnary := by
    have hn := encQuery_arity_deg.computableInPolyTime.comp hq2
    have hs := encQuery_size_deg.computableInPolyTime.comp hq2
    have hℓ := encQuery_power_deg.computableInPolyTime.comp hq2
    unfold certLength
    fun_prop
  have hu : ComputableInPolyTime (fun r : Query × List Bool => r.1.threshold) e1 encUnary :=
    encQuery_threshold_deg.computableInPolyTime.comp hq1
  have hW : ComputableInPolyTime (fun q : Query => (q.threshold + 1) *
      (q.threshold * (q.power * certLength q.arity q.size) + q.threshold)) encQuery encUnary := by
    have hn := encQuery_arity_deg.computableInPolyTime
    have hs := encQuery_size_deg.computableInPolyTime
    have hℓ := encQuery_power_deg.computableInPolyTime
    have hu := encQuery_threshold_deg.computableInPolyTime
    unfold certLength
    fun_prop
  have h3 : {r : ((Query × List Bool) × List Bool) × List Bool | coverTest r = true} ∈
      PPolyOn (encPair e2 encBits) :=
    P_subset_PPolyOn ⟨coverTest, computableInPolyTime_coverTest, fun _ => Iff.rfl⟩
  have h2 := PPolyOn.exists_of_computableInPolyTime_length hNP hN
    (P := fun r x => coverTest (r, x) = true) h3
  have h1 := PPolyOn.forall_of_computableInPolyTime_length hNP hu
    (P := fun r z => ∃ x : List Bool, x.length = r.1.power * certLength r.1.arity r.1.size ∧
      coverTest ((r, z), x) = true) h2
  have h0 := PPolyOn.exists_of_computableInPolyTime_length hNP hW
    (P := fun q σ => ∀ z : List Bool, z.length = q.threshold →
      ∃ x : List Bool, x.length = q.power * certLength q.arity q.size ∧
        coverTest (((q, σ), z), x) = true) h1
  have heq : smallSet = {q : Query | ∃ σ : List Bool, σ.length = (q.threshold + 1) *
      (q.threshold * (q.power * certLength q.arity q.size) + q.threshold) ∧
      ∀ z : List Bool, z.length = q.threshold →
        ∃ x : List Bool, x.length = q.power * certLength q.arity q.size ∧
          coverTest (((q, σ), z), x) = true}ᶜ := by
    ext q
    rw [mem_smallSet, hashOracle_eq_true, isLarge_iff_exists]
    rfl
  rw [heq]
  exact PPolyOn.compl h0

/-- **Under `NP ⊆ P/poly`, a language in `P/poly` agrees with the anti-checker oracle on every
query.** -/
theorem exists_mem_PPoly_agrees_antiCheckerOracle (hNP : NP encBits ⊆ PPolyOn encBits) :
    ∃ O ∈ PPoly, ∀ q : Query, encQuery q ∈ O ↔ encQuery q ∈ antiCheckerOracle := by
  obtain ⟨O, hO, h⟩ := smallSet_mem_PPolyOn hNP
  exact ⟨O, hO, fun q => by rw [encQuery_mem_antiCheckerOracle, h]⟩

end Cslib.MCSP.AntiChecker
