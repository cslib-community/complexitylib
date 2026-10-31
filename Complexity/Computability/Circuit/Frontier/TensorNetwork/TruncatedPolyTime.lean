/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Truncated
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.DescribedContraction
public import Complexity.Computability.GenericRAM.Native.IndexFold
import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionPolyTime
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionSchedule
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# The reduction of truncation order `ℓ` as a native machine

The reduction of `Complexity/Computability/Circuit/Frontier/TensorNetwork/Truncated.lean`
(`Cslib.Circuits.Frontier.DescribedNetwork.interpContract`) contracts specialized networks over
`A_P = (ℤ / 2 ^ P)[U] / (f)` and interpolates. This file runs it as one native machine around any
native certificate of the contraction over `A_P` (`engineCertificate`), with the precision `P` and
the truncation order `ℓ` in unary.

**Polynomial-time steps.** Specializing a network at a point (`DescribedNetwork.specNet_polyTime`),
the binary-digit points (`DescribedNetwork.digitPoints_polyTime`), the inputs of the contractions
(`coreInput_polyTime`) and reading the truncated contraction off the interpolant
(`interpRecover_polyTime`, `engineRecover_polyTime`) are polynomial-time.

**The loop.** The machine visits the digit points with the binary-index fold
`Cslib.GenericRAM.IndexFold`, keeping the index, the input and the values so far; each round
calls the given certificate once (`engineStep`, `engineStepCertificate`, `run_engineStep`). Then it
interpolates.

**Direct summation.** A native certificate of the entries gives one of the specialized entries
(`specEntryCertificate`: the entry, then Horner's rule), hence direct summation over `A_P` of a
specialized network (`directCoreCertificate`). Through the reduction at the modulus
`FastContraction.modulus n` for `n = (ℓ - 1) k + 1` points, which has enough residues
(`le_two_pow_length_modulus`), this computes the truncated contraction on every input
(`truncDirectCertificate`). Its cost is that of direct summation.

No time or space bound of the loop is proved here. With the contraction of Theorem D.1 at `ℓ = 1`
over `A_P` in place of direct summation, a bound of the loop gives Theorem D.1 at truncation order
`ℓ` (#1538).

## Main definitions

* `Cslib.Circuits.Frontier.encSpecDesc`, `Cslib.Circuits.Frontier.encTrunc`,
  `Cslib.Circuits.Frontier.encCore`, `Cslib.Circuits.Frontier.encEngine`: encodings.
* `Cslib.Circuits.Frontier.specEntryCertificate`: the native evaluator of specialized entries.
* `Cslib.Circuits.Frontier.engineCertificate`: the reduction around a contraction over `A_P`.
* `Cslib.Circuits.Frontier.directCoreCertificate`: direct summation over `A_P`.
* `Cslib.Circuits.Frontier.truncDirectCertificate`: the truncated contraction by direct summation.

## Main results

* `Cslib.Circuits.Frontier.DescribedNetwork.specNet_polyTime`,
  `Cslib.Circuits.Frontier.interpRecover_polyTime`: polynomial-time steps.
* `Cslib.Circuits.Frontier.run_engineStep`, `Cslib.Circuits.Frontier.interpContract_eq_run`: the
  loop computes the reduction.
* `Cslib.Circuits.Frontier.interpContract_direct_eq`: direct summation through the reduction is
  the truncated contraction.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53).
-/

public section

namespace Cslib.Circuits.Frontier

open Turing.MultiTapeTM Cslib.GenericRAM GaloisRingArith

variable {T : Type} (encT : T ↪ List Bool)

/-- The encoding of the data `(P, ℓ, fl, ζ)` of a specialization: `P` and `ℓ` in unary, the
coefficients of the modulus and the point in binary. -/
abbrev encSpecData : ℕ × ℕ × List ℕ × List ℕ ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair (encList encNat) (encList encNat)))

/-- The encoding of a specialized descriptor: the original descriptor, then the data of the
specialization. -/
abbrev encSpecDesc : SpecDesc T ↪ List Bool := encPair encT encSpecData

variable {encT}

/-- The first `ℓ` coefficients as constant coefficient lists, from `ℓ` in unary. -/
theorem constCoeffs_polyTime :
    ComputableInPolyTime (fun q : ℕ × List ℕ => constCoeffs q.1 q.2)
      (encPair encUnary (encList encNat)) (encList (encList encNat)) := by
  have hc : ComputableInPolyTime (fun q : (ℕ × List ℕ) × ℕ => q.1.2)
      (encPair (encPair encUnary (encList encNat)) encUnary) (encList encNat) :=
    (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)
  have hget := computableInPolyTime_getD hc (ComputableInPolyTime.snd _ _)
  exact ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.range.comp (ComputableInPolyTime.fst _ _))
    (ComputableInPolyTime.cons' hget (ComputableInPolyTime.const []))

/-- **Horner's rule on the first `ℓ` coefficients**, from the data of a specialization and a
coefficient list, with `P` and `ℓ` in unary. -/
theorem horner_polyTime :
    ComputableInPolyTime
      (fun q : (ℕ × ℕ × List ℕ × List ℕ) × List ℕ =>
        peval q.1.1 q.1.2.2.1 (constCoeffs q.1.2.1 q.2) q.1.2.2.2)
      (encPair encSpecData (encList encNat)) (encList encNat) := by
  have hd := ComputableInPolyTime.fst encSpecData (encList encNat)
  have hc := ComputableInPolyTime.snd encSpecData (encList encNat)
  have hP := (ComputableInPolyTime.fst _ _).comp hd
  have hrest := (ComputableInPolyTime.snd _ _).comp hd
  have hℓ := (ComputableInPolyTime.fst _ _).comp hrest
  have hfz := (ComputableInPolyTime.snd _ _).comp hrest
  have hfl := (ComputableInPolyTime.fst _ _).comp hfz
  have hz := (ComputableInPolyTime.snd _ _).comp hfz
  exact computableInPolyTime_peval hP hfl (constCoeffs_polyTime.comp (hℓ.prod hc)) hz

variable (entry : T → List Bool → List ℕ)

/-- **The native evaluator of specialized entries**, from a native certificate of the entries:
evaluate the original entry, then apply Horner's rule in `A_P`. -/
noncomputable def specEntryCertificate
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    NativeCertificate (fun q : SpecDesc T × List Bool => specEntry entry q.1 q.2)
      (encPair (encSpecDesc encT) encBits) (encList encNat) :=
  ((NativeCertificate.ofPolyTime horner_polyTime).comp
    ((NativeCertificate.ofPolyTime
        ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))).prod
      (ce.comp (NativeCertificate.ofPolyTime
        ((((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _))).prod
          (ComputableInPolyTime.snd _ _)))))).congr fun _ => rfl

namespace DescribedNetwork

/-- **Specializing is polynomial-time**: from the data `(P, ℓ, fl, ζ)` and the network to the
specialized network. -/
theorem specNet_polyTime :
    ComputableInPolyTime
      (fun q : (ℕ × ℕ × List ℕ × List ℕ) × DescribedNetwork T =>
        specNet q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
      (encPair encSpecData (encDescribed encT)) (encDescribed (encSpecDesc encT)) := by
  have hG := ComputableInPolyTime.snd encSpecData (encDescribed encT)
  have hd := ComputableInPolyTime.fst encSpecData (encDescribed encT)
  have hv : ComputableInPolyTime
      (fun q : ((ℕ × ℕ × List ℕ × List ℕ) × DescribedNetwork T) × (List ℕ × T) =>
        (q.2.1, (q.2.2, q.1.1)))
      (encPair (encPair encSpecData (encDescribed encT)) (encPair (encList encNat) encT))
      (encPair (encList encNat) (encSpecDesc encT)) :=
    ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)).prod
      (((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)).prod
        ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)))
  have hpair : ComputableInPolyTime
      (fun q : (ℕ × ℕ × List ℕ × List ℕ) × DescribedNetwork T =>
        (q.2.numEdges, q.2.vertices.map fun v => (v.1, (v.2, q.1))))
      (encPair encSpecData (encDescribed encT))
      (encPair encUnary (encList (encPair (encList encNat) (encSpecDesc encT)))) :=
    (numEdges_polyTime.comp hG).prod
      (ComputableInPolyTime.mapWithInput (vertices_polyTime.comp hG) hv)
  exact (ComputableInPolyTime.of_eq (encIn := encPair encUnary
    (encList (encPair (encList encNat) (encSpecDesc encT))))
    (f := fun p : ℕ × List (List ℕ × SpecDesc T) => (⟨p.1, p.2⟩ : DescribedNetwork (SpecDesc T)))
    fun _ => rfl).comp hpair

/-- **The binary-digit points are polynomial-time**, from the number of coordinates and the
number of points in unary. -/
theorem digitPoints_polyTime :
    ComputableInPolyTime
      (fun q : ℕ × ℕ => (List.range q.2).map (FastContraction.digits q.1))
      (encPair encUnary encUnary) (encList (encList encNat)) :=
  ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.range.comp (ComputableInPolyTime.snd _ _))
    (FastContraction.digits_polyTime.comp
      (((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _)))

end DescribedNetwork

/-- **Reading off the interpolant is polynomial-time**, with `P` and `ℓ` in unary. -/
theorem interpRecover_polyTime :
    ComputableInPolyTime
      (fun q : ℕ × ℕ × List ℕ × List (List ℕ) × List (List ℕ) =>
        interpRecover q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
      (encPair encUnary (encPair encUnary (encPair (encList encNat)
        (encPair (encList (encList encNat)) (encList (encList encNat))))))
      (encList encNat) := by
  let encQ := encPair encUnary (encPair encUnary (encPair (encList encNat)
    (encPair (encList (encList encNat)) (encList (encList encNat)))))
  have hP := ComputableInPolyTime.fst encUnary (encPair encUnary (encPair (encList encNat)
    (encPair (encList (encList encNat)) (encList (encList encNat)))))
  have hr := ComputableInPolyTime.snd encUnary (encPair encUnary (encPair (encList encNat)
    (encPair (encList (encList encNat)) (encList (encList encNat)))))
  have hℓ := (ComputableInPolyTime.fst _ _).comp hr
  have hr' := (ComputableInPolyTime.snd _ _).comp hr
  have hfl := (ComputableInPolyTime.fst _ _).comp hr'
  have hr'' := (ComputableInPolyTime.snd _ _).comp hr'
  have hpts := (ComputableInPolyTime.fst _ _).comp hr''
  have hys := (ComputableInPolyTime.snd _ _).comp hr''
  have hI := computableInPolyTime_interp hP hfl hpts hys
  have hq : ComputableInPolyTime
      (fun q : (ℕ × ℕ × List ℕ × List (List ℕ) × List (List ℕ)) × ℕ =>
        ((interp q.1.1 q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2).getD q.2 []).getD 0 0 % 2 ^ q.1.1)
      (encPair encQ encUnary) encNat := by
    have h1 := ComputableInPolyTime.fst encQ encUnary
    have hrow := (ComputableInPolyTime.listGetD (encA := encList encNat) []).comp
      ((hI.comp h1).prod (ComputableInPolyTime.snd encQ encUnary))
    exact computableInPolyTime_mod_two_pow
      (computableInPolyTime_getD hrow (ComputableInPolyTime.const 0)) (hP.comp h1)
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hℓ) hq

/-! ### The reduction as a streaming loop -/

/-- The encoding of an input `(P, ℓ, r, G)` of the truncated contraction: `P` and `ℓ` in unary,
`r` in binary, then the network. -/
abbrev encTrunc (encT : T ↪ List Bool) : ℕ × ℕ × ℕ × DescribedNetwork T ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encNat (DescribedNetwork.encDescribed encT)))

/-- The encoding of an input `(P, fl, r, G')` of a contraction over `A_P` of specialized
networks: `P` in unary, the modulus, `r` in binary, then the specialized network. -/
abbrev encCore (encT : T ↪ List Bool) :
    ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T) ↪ List Bool :=
  encPair encUnary (encPair (encList encNat)
    (encPair encNat (DescribedNetwork.encDescribed (encSpecDesc encT))))

/-- The input of the reduction: the modulus and the input `(P, ℓ, r, G)`. -/
abbrev encEngine (encT : T ↪ List Bool) : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T ↪ List Bool :=
  encPair (encList encNat) (encTrunc encT)

/-- The input of the contraction at the `k`-th digit point, for a modulus `y.1` and an input
`y.2 = (P, ℓ, r, G)`. -/
@[expose] def coreInput (y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) (k : ℕ) :
    ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T) :=
  (y.2.1, y.1, y.2.2.2.1,
    DescribedNetwork.specNet y.2.1 y.2.2.1 y.1 (FastContraction.digits y.1.length k) y.2.2.2.2)

variable (core : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T) → List ℕ)

/-- **One round of the reduction** at the index `p.1`: append the contraction at the `p.1`-th digit
point to the values so far. -/
@[expose] def engineStep
    (p : ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ))) :
    (List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ) :=
  (p.2.1, p.2.2 ++ [core (coreInput p.2.1 p.1)])

/-- After `j` rounds, the values are the contractions at the first `j` digit points. -/
theorem run_engineStep (y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) (j : ℕ) :
    IndexFold.run (engineStep core) j (y, []) =
      (j, (y, (List.range j).map fun k => core (coreInput y k))) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [IndexFold.run_succ, ih]
    simp only [IndexFold.step, engineStep, List.range_succ, List.map_append, List.map_cons,
      List.map_nil]

/-- **The reduction is the streaming loop followed by recovery.** -/
theorem interpContract_eq_run (y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) :
    DescribedNetwork.interpContract core y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2 =
      interpRecover y.2.1 y.2.2.1 y.1
        ((List.range (DescribedNetwork.pointCount y.2.2.1 y.2.2.2.2)).map
          (FastContraction.digits y.1.length))
        (IndexFold.run (engineStep core) (DescribedNetwork.pointCount y.2.2.1 y.2.2.2.2)
          (y, [])).2.2 := by
  rw [run_engineStep, DescribedNetwork.interpContract, List.map_map]
  rfl

/-- The binary digits are polynomial-time from the number in binary. -/
theorem digits_polyTime_binary :
    ComputableInPolyTime (fun q : ℕ × ℕ => FastContraction.digits q.1 q.2)
      (encPair encUnary encNat) (encList encNat) :=
  ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.range.comp (ComputableInPolyTime.fst _ _))
    (ComputableInPolyTime.ite (encMid := encNat)
      (ComputableInPolyTime.binary_testBit
        ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))
        (ComputableInPolyTime.snd _ _))
      (ComputableInPolyTime.const 1) (ComputableInPolyTime.const 0))

/-- The number of points is polynomial-time, in unary. -/
theorem pointCount_polyTime :
    ComputableInPolyTime (fun y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T =>
      DescribedNetwork.pointCount y.2.2.1 y.2.2.2.2) (encEngine encT) encUnary := by
  have hx := ComputableInPolyTime.snd (encList encNat) (encTrunc encT)
  have hℓ := (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd _ _).comp hx)
  have hG := (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp
    ((ComputableInPolyTime.snd _ _).comp hx))
  have hk := (ComputableInPolyTime.length_list _).comp
    (DescribedNetwork.vertices_polyTime.comp hG)
  exact ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.unary_sub' hℓ
      (ComputableInPolyTime.const 1)) hk) (ComputableInPolyTime.const 1)

/-- The input of the contraction at a binary index is polynomial-time. -/
theorem coreInput_polyTime :
    ComputableInPolyTime
      (fun p : ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)) =>
        coreInput p.2.1 p.1)
      (encPair encNat (encPair (encEngine encT) (encList (encList encNat)))) (encCore encT) := by
  have hy := (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd encNat
    (encPair (encEngine encT) (encList (encList encNat))))
  have hk := ComputableInPolyTime.fst encNat (encPair (encEngine encT) (encList (encList encNat)))
  have hfl := (ComputableInPolyTime.fst _ _).comp hy
  have hx := (ComputableInPolyTime.snd _ _).comp hy
  have hP := (ComputableInPolyTime.fst _ _).comp hx
  have hx' := (ComputableInPolyTime.snd _ _).comp hx
  have hℓ := (ComputableInPolyTime.fst _ _).comp hx'
  have hx'' := (ComputableInPolyTime.snd _ _).comp hx'
  have hr := (ComputableInPolyTime.fst _ _).comp hx''
  have hG := (ComputableInPolyTime.snd _ _).comp hx''
  have hζ := digits_polyTime_binary.comp
    (((ComputableInPolyTime.length_list _).comp hfl).prod hk)
  exact hP.prod (hfl.prod (hr.prod (DescribedNetwork.specNet_polyTime.comp
    ((hP.prod (hℓ.prod (hfl.prod hζ))).prod hG))))

/-- The certificate of one round, from a certificate of the contraction over `A_P`. -/
noncomputable def engineStepCertificate
    (cc : NativeCertificate core (encCore encT) (encList encNat)) :
    NativeCertificate (engineStep core)
      (encPair encNat (encPair (encEngine encT) (encList (encList encNat))))
      (encPair (encEngine encT) (encList (encList encNat))) :=
  (NativeCertificate.ofPolyTime
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))).prod
    ((NativeCertificate.ofPolyTime (ComputableInPolyTime.snoc (encList encNat))).comp
      ((NativeCertificate.ofPolyTime
          ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _))).prod
        (cc.comp (NativeCertificate.ofPolyTime coreInput_polyTime))))

/-- Recovery from the final state of the loop is polynomial-time. -/
theorem engineRecover_polyTime :
    ComputableInPolyTime
      (fun p : ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)) =>
        interpRecover p.2.1.2.1 p.2.1.2.2.1 p.2.1.1
          ((List.range (DescribedNetwork.pointCount p.2.1.2.2.1 p.2.1.2.2.2.2)).map
            (FastContraction.digits p.2.1.1.length)) p.2.2)
      (encPair encNat (encPair (encEngine encT) (encList (encList encNat)))) (encList encNat) := by
  let encS := encPair encNat (encPair (encEngine encT) (encList (encList encNat)))
  have hy : ComputableInPolyTime
      (fun p : ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)) => p.2.1)
      encS (encEngine encT) :=
    (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)
  have hys : ComputableInPolyTime
      (fun p : ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)) => p.2.2)
      encS (encList (encList encNat)) :=
    (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)
  have hfl : ComputableInPolyTime
      (fun p : ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)) => p.2.1.1)
      encS (encList encNat) := (ComputableInPolyTime.fst _ _).comp hy
  have hP : ComputableInPolyTime
      (fun p : ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)) => p.2.1.2.1)
      encS encUnary :=
    (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd _ _).comp hy)
  have hℓ : ComputableInPolyTime
      (fun p : ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)) => p.2.1.2.2.1)
      encS encUnary :=
    (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.snd _ _).comp hy))
  have hpts : ComputableInPolyTime
      (fun p : ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)) =>
        (List.range (DescribedNetwork.pointCount p.2.1.2.2.1 p.2.1.2.2.2.2)).map
          (FastContraction.digits p.2.1.1.length))
      encS (encList (encList encNat)) :=
    DescribedNetwork.digitPoints_polyTime.comp
      (((ComputableInPolyTime.length_list _).comp hfl).prod (pointCount_polyTime.comp hy))
  have h := interpRecover_polyTime.comp (hP.prod (hℓ.prod (hfl.prod (hpts.prod hys))))
  exact h

/-- **The reduction as one native machine**, from a native certificate of the contraction over
`A_P` of specialized networks: the streaming loop over the digit points, keeping only the binary
index, the input and the values so far, then recovery. On input `(fl, (P, ℓ, r, G))` it computes
`interpContract core fl P ℓ r G`. -/
noncomputable def engineCertificate
    (cc : NativeCertificate core (encCore encT) (encList encNat)) :
    NativeCertificate (fun y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T =>
        DescribedNetwork.interpContract core y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2)
      (encEngine encT) (encList encNat) :=
  ((NativeCertificate.ofPolyTime engineRecover_polyTime).comp
    (IndexFold.certificate
      (NativeCertificate.ofPolyTime (ComputableInPolyTime.unary_to_binary.comp pointCount_polyTime))
      (NativeCertificate.ofPolyTime
        (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const [])))
      (engineStepCertificate core cc))).congr fun y => by
    simp only [Function.comp_apply]
    rw [interpContract_eq_run, run_engineStep]

/-! ### Direct summation as the contraction over `A_P` -/

/-- **Direct summation over a specialized network**, as a contraction over `A_P` with the input
`(P, fl, r, G')`, from a native certificate of the entries. -/
noncomputable def directCoreCertificate
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    NativeCertificate
      (fun x : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T) =>
        DescribedNetwork.sumValue SumOps.galois (specEntry entry) (x.1, x.2.1) x.2.2.2)
      (encCore encT) (encList encNat) :=
  ((DescribedNetwork.contractionCertificate (specEntry entry) SumOps.galois_polyTime
      (specEntryCertificate entry ce)).comp
    (NativeCertificate.ofPolyTime
      ((((ComputableInPolyTime.fst _ _).prod
        ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))).prod
        ((ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp
          (ComputableInPolyTime.snd _ _)))) :
        ComputableInPolyTime
          (fun x : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T) => ((x.1, x.2.1), x.2.2.2))
          (encCore encT)
          (DescribedNetwork.encInput (encPair encUnary (encList encNat))
            (encSpecDesc encT))))).congr fun _ => rfl

/-- `n ≤ 2 ^ deg f` for the modulus `FastContraction.modulus n`: it has enough residues for `n`
points. -/
theorem le_two_pow_length_modulus (n : ℕ) : n ≤ 2 ^ (FastContraction.modulus n).length := by
  have h4 := FastContraction.four_mul_log_le_length_modulus n
  have hlt := Nat.lt_pow_succ_log_self (b := 2) one_lt_two n
  rcases Nat.eq_zero_or_pos (Nat.log 2 n) with h0 | hpos
  · have h2 : n < 2 := by simpa [h0] using hlt
    exact (show n ≤ 1 by omega).trans Nat.one_le_two_pow
  · exact hlt.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- Choosing the modulus `FastContraction.modulus n` for `n = (ℓ - 1) k + 1` points is
polynomial-time. -/
theorem modulusChoice_polyTime :
    ComputableInPolyTime
      (fun x : ℕ × ℕ × ℕ × DescribedNetwork T =>
        (FastContraction.modulus (DescribedNetwork.pointCount x.2.1 x.2.2.2), x))
      (encTrunc encT) (encEngine encT) := by
  have hpc : ComputableInPolyTime
      (fun x : ℕ × ℕ × ℕ × DescribedNetwork T => DescribedNetwork.pointCount x.2.1 x.2.2.2)
      (encTrunc encT) encUnary := by
    have h := pointCount_polyTime (encT := encT).comp
      ((ComputableInPolyTime.const ([] : List ℕ)).prod ComputableInPolyTime.id')
    exact h
  have h := (FastContraction.modulus_polyTime.comp hpc).prod ComputableInPolyTime.id'
  exact h

/-- **Direct summation through the reduction computes the truncated contraction**, at the modulus
`FastContraction.modulus n` for `n = (ℓ - 1) k + 1` points. -/
theorem interpContract_direct_eq (P ℓ r : ℕ) (G : DescribedNetwork T) :
    DescribedNetwork.interpContract
        (fun x : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T) =>
          DescribedNetwork.sumValue SumOps.galois (specEntry entry) (x.1, x.2.1) x.2.2.2)
        (FastContraction.modulus (DescribedNetwork.pointCount ℓ G)) P ℓ r G =
      G.truncContraction entry P ℓ := by
  refine DescribedNetwork.interpContract_eq (entry := entry)
    (FastContraction.irreducible_modulus (DescribedNetwork.pointCount ℓ G)) G
    (le_two_pow_length_modulus _) fun k _ => ?_
  exact DescribedNetwork.val_sumValue_galois (specEntry entry)
    (P, FastContraction.modulus (DescribedNetwork.pointCount ℓ G)) _

/-- **The truncated contraction by direct summation**, as one native machine on every input
`(P, ℓ, r, G)`: the reduction with direct summation over `A_P` at the modulus
`FastContraction.modulus n`, for `n = (ℓ - 1) k + 1` points. It is correct everywhere; its cost is
that of direct summation, exponential in the number of edges. -/
noncomputable def truncDirectCertificate
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    NativeCertificate
      (fun x : ℕ × ℕ × ℕ × DescribedNetwork T => x.2.2.2.truncContraction entry x.1 x.2.1)
      (encTrunc encT) (encList encNat) :=
  ((engineCertificate _ (directCoreCertificate entry ce)).comp
    (NativeCertificate.ofPolyTime modulusChoice_polyTime)).congr fun x =>
      interpContract_direct_eq entry x.1 x.2.1 x.2.2.1 x.2.2.2

end Cslib.Circuits.Frontier
