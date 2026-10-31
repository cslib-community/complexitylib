/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContraction
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.DirectContraction
import Complexity.Computability.PolyTime.GaloisRingSeries
import Complexity.Foundations.FieldTheory.Finite.Trinomial
import Mathlib.Data.List.GetD
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.SqrtLog
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPower
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends

/-!
# The native machine of the fast contraction algorithm

The stack recursion of `Cslib.Circuits.Frontier.FastContraction.scheme` as one native machine for
the contraction modulo `2 ^ P` of an explicit network `(r, G)`, with the precision `P` in binary:
the root descriptors are tables (`T = List ℕ`), read by the entry procedure `tableEntry`. The
encodings, the root network (`FastContraction.rootNet`) and its polynomial-time construction are
stated for every type of root descriptors.

**The root.** The precision is first capped at the encoded length of the network
(`ExplicitTensorNetwork.capPrecision`), which does not change the residue. The root call
(`FastContraction.root`) has the scale `s = m`, the number of edges of `G`, depth `0`, edge bound
`m + 1`, the capped precision `p`, the tables of `G` as descriptors (`FastContraction.rootNet`) and
the modulus `f = X ^ (2 ⬝ 3 ^ t) + X ^ (3 ^ t) + 1` (`FastContraction.modulus`), irreducible modulo
`2` (`Cslib.irreducible_trinomial`), whose `2 ⬝ 3 ^ t > 4 ⌊log₂ m⌋ + 2` binary digits give the
interpolation points of every call of the schedule.

**The fuel and the fallback.** The number of calls of the recursion depends, through the schedule's
constant, on the ratio of the precision to the number of edges, which the machine does not know in
advance. So the machine runs the recursion for a fixed clock `2 ^ (K₀ (m + p) / √⌊log₂ (m + p)⌋)`
(`FastContraction.fuel`), and returns the constant coordinate of the root's value when the run has
returned a value tagged with depth `0`, and direct summation otherwise
(`FastContraction.fastValue`).
A value tagged `0` is the root's value for every fuel (`FastContraction.eq_value_of_run`), so the
result is correct on every well-formed input, whatever the fuel
(`FastContraction.fastValue_eq`); the clock matters only for the running time.

## Main definitions

* `Cslib.Circuits.Frontier.FastContraction.encCall`, `encFrame`, `encValue`: the encodings.
* `Cslib.Circuits.Frontier.FastContraction.leafCertificate`: direct summation at the leaves.
* `Cslib.Circuits.Frontier.FastContraction.modulus`, `rootNet`, `root`, `fuel`: the root call and
  the clock.
* `Cslib.Circuits.Frontier.FastContraction.fastValue`: the result of the machine.
* `Cslib.Circuits.Frontier.FastContraction.fastCertificate`: the machine, given polynomial-time
  components of the scheme.

## Main results

* `Cslib.Circuits.Frontier.FastContraction.irreducible_modulus`: the modulus is irreducible modulo
  `2`.
* `Cslib.Circuits.Frontier.FastContraction.val_rootNet`: the root computes the contraction of `G`.
* `Cslib.Circuits.Frontier.FastContraction.getD_mod_of_val_eq`: reading off the constant
  coordinate.
* `Cslib.Circuits.Frontier.FastContraction.fastValue_eq`: the machine is correct on well-formed
  inputs, for every fuel.
* `Cslib.Circuits.Frontier.FastContraction.root_polyTime`,
  `Cslib.Circuits.Frontier.FastContraction.fuel_polyTime`: the root and the clock in polynomial
  time.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.7 (p. 64).
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction

open GaloisRingArith ChildCursor Cslib.GenericRAM Cslib.GenericRAM.StackRecursion
  Turing.MultiTapeTM

variable {T : Type}

/-! ### Encodings -/

/-- The encoding of the parameters of a call: the scale, the depth, the edge bound and the
precision in unary, the coefficients of the modulus in binary and the number of rows in
binary. -/
abbrev encParams : Params ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary
    (encPair (encList encNat) encNat))))

/-- The encoding of a call: its parameters and its network, with the root descriptors encoded by
`encT`. -/
abbrev encCall (encT : T ↪ List Bool) : Call T ↪ List Bool :=
  encPair encParams (DescribedNetwork.encDescribed (VertexDesc.enc encT))

/-- The encoding of a frame: the cursor state and the accumulator, in binary. -/
abbrev encFrame : Frame ↪ List Bool :=
  encPair (encOption ChildCursor.encState)
    (encPair (encList encNat) (encPair (encList encNat) (encList (encList encNat))))

/-- The encoding of a tagged value: the depth in unary and the coefficient list in binary. -/
abbrev encValue : ℕ × List ℕ ↪ List Bool := encPair encUnary (encList encNat)

/-! ### The leaves -/

variable (encT : T ↪ List Bool)

/-- The depth of a call is polynomial-time. -/
theorem depth_polyTime : ComputableInPolyTime (Call.depth (T := T)) (encCall encT) encUnary := by
  unfold Call.depth; fun_prop

/-- The input of direct summation at a call, `((p, fl), D)`, is polynomial-time. -/
theorem leafInput_polyTime :
    ComputableInPolyTime (fun x : Call T => ((x.prec, x.fl), x.net)) (encCall encT)
      (DescribedNetwork.encInput (encPair encUnary (encList encNat)) (VertexDesc.enc encT)) := by
  unfold Call.prec Call.fl Call.net; fun_prop

variable (mk : Call (List ℕ) → State → ℕ × DescribedNetwork (VertexDesc (List ℕ)))

/-- **The leaf certificate** over tables: direct summation over the coefficient lists of `A_p`,
with the native evaluator of the vertex descriptors, tagged with the depth. -/
@[expose] noncomputable def leafCertificate :
    NativeCertificate (scheme tableEntry mk).leaf (encCall (encList encNat)) encValue :=
  ((NativeCertificate.ofPolyTime (depth_polyTime (encList encNat))).prod
    ((DescribedNetwork.contractionCertificate (VertexDesc.entry tableEntry)
      SumOps.galois_polyTime VertexDesc.entryCertificate).comp
      (NativeCertificate.ofPolyTime (leafInput_polyTime (encList encNat))))).congr
    fun _ => rfl

/-- The time of a leaf: the depth, the input of direct summation, and direct summation. -/
theorem leafCertificate_time (x : Call (List ℕ)) :
    (leafCertificate mk).time x =
      (NativeCertificate.ofPolyTime (depth_polyTime (encList encNat))).time x +
        ((NativeCertificate.ofPolyTime (leafInput_polyTime (encList encNat))).time x +
          (DescribedNetwork.contractionCertificate (VertexDesc.entry tableEntry)
            SumOps.galois_polyTime VertexDesc.entryCertificate).time ((x.prec, x.fl), x.net)) :=
  rfl

/-- The space of a leaf. -/
theorem leafCertificate_space (x : Call (List ℕ)) :
    (leafCertificate mk).space x =
      (NativeCertificate.ofPolyTime (depth_polyTime (encList encNat))).space x +
        ((NativeCertificate.ofPolyTime (leafInput_polyTime (encList encNat))).space x +
          (DescribedNetwork.contractionCertificate (VertexDesc.entry tableEntry)
            SumOps.galois_polyTime VertexDesc.entryCertificate).space ((x.prec, x.fl), x.net)) :=
  rfl

/-! ### The root -/

/-- The exponent `t` of the modulus, with `2 ^ (t + 1) > 4 ⌊log₂ m⌋ + 2`. -/
@[expose] def modulusExp (m : ℕ) : ℕ := Nat.log 2 (4 * Nat.log 2 m + 2)

/-- **The modulus** `X ^ (2 ⬝ 3 ^ t) + X ^ (3 ^ t) + 1`, by its coefficients below the leading
one. -/
@[expose] def modulus (m : ℕ) : List ℕ :=
  (List.range (2 * 3 ^ modulusExp m)).map fun i =>
    if i = 0 ∨ i = 3 ^ modulusExp m then 1 else 0

/-- The modulus has `2 ⬝ 3 ^ t` coefficients. -/
theorem length_modulus (m : ℕ) : (modulus m).length = 2 * 3 ^ modulusExp m := by
  simp [modulus]

/-- The modulus has a coefficient. -/
theorem modulus_ne_nil (m : ℕ) : modulus m ≠ [] := by
  rw [← List.length_pos_iff, length_modulus]
  positivity

/-- **The modulus is the trinomial** `X ^ (2 ⬝ 3 ^ t) + X ^ (3 ^ t) + 1` over `ℤ`. -/
theorem monicOf_modulus (m : ℕ) :
    monicOf (modulus m) = Polynomial.X ^ (2 * 3 ^ modulusExp m) +
      Polynomial.X ^ (3 ^ modulusExp m) + 1 := by
  set t := modulusExp m
  have h3 : 0 < 3 ^ t := by positivity
  have hsum : ∑ i ∈ Finset.range (2 * 3 ^ t),
      Polynomial.C (((modulus m).getD i 0 : ℕ) : ℤ) * Polynomial.X ^ i =
      Polynomial.X ^ (3 ^ t) + 1 := by
    have hget (i : ℕ) (hi : i < 2 * 3 ^ t) :
        (modulus m).getD i 0 = if i = 0 ∨ i = 3 ^ t then 1 else 0 := by
      rw [List.getD_eq_getElem _ _ (by rw [length_modulus]; exact hi)]
      simp [modulus, t]
    rw [Finset.sum_congr rfl fun i hi => by rw [hget i (Finset.mem_range.mp hi)]]
    rw [Finset.sum_eq_add (0 : ℕ) (3 ^ t) (by omega) (fun i _ hi => by
      simp only [hi.1, hi.2, or_self, ↓reduceIte, Nat.cast_zero, map_zero, zero_mul])
      (fun h => absurd (Finset.mem_range.mpr (by omega)) h)
      (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
    simp [add_comm]
  rw [monicOf, length_modulus, hsum, add_assoc]

/-- **The modulus is irreducible modulo `2`**: its reduction is `Cslib.trinomial t`. -/
theorem irreducible_modulus (m : ℕ) :
    Irreducible ((monicOf (modulus m)).map (Int.castRingHom (ZMod 2))) := by
  rw [monicOf_modulus]
  simpa [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    Cslib.trinomial] using Cslib.irreducible_trinomial (modulusExp m)

/-- **The root descriptors of a network as vertex descriptors**; for an explicit network, its
tables. -/
@[expose] def rootNet (G : DescribedNetwork T) : DescribedNetwork (VertexDesc T) :=
  ⟨G.numEdges, G.vertices.map fun v => (v.1, .inl v.2)⟩

/-- **The root call** of a capped input `(p, r, G)`: scale `m`, depth `0`, edge bound `m + 1`,
precision `p`, the modulus and the tables of `G`. -/
@[expose] def root (q : ℕ × ℕ × ExplicitTensorNetwork ℕ) : Call (List ℕ) :=
  ((q.2.2.numEdges, 0, q.2.2.numEdges + 1, q.1, modulus q.2.2.numEdges, q.2.1), rootNet q.2.2)

/-- The constant of the clock. -/
@[expose] def fuelConst : ℕ := 2 ^ 22

/-- **The clock** of a capped input `(p, r, G)`: `2 ^ (K₀ (m + p) / √⌊log₂ (m + p)⌋)`. -/
@[expose] def fuel (q : ℕ × ℕ × ExplicitTensorNetwork ℕ) : ℕ :=
  2 ^ (fuelConst * (q.2.2.numEdges + q.1) / Nat.sqrt (Nat.log 2 (q.2.2.numEdges + q.1)))

/-- **The root computes the contraction of `G`**: in `A_p`, the contraction of the tables read as
constants is the image of the contraction of `G`. -/
theorem val_rootNet (p : ℕ) (fl : List ℕ) (G : ExplicitTensorNetwork ℕ) :
    (rootNet G).contraction (fun t bs => val p fl (VertexDesc.entry tableEntry t bs)) =
      (G.contraction : Ring p fl) := by
  rw [← DescribedNetwork.contraction_entry]
  have h := DescribedNetwork.map_contraction (Nat.castRingHom (Ring p fl))
    ExplicitTensorNetwork.entry G
  simp only [Nat.coe_castRingHom] at h
  rw [h]
  simp only [DescribedNetwork.contraction, rootNet, List.map_map]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  refine List.map_congr_left fun v _ => ?_
  simp only [Function.comp_apply, VertexDesc.val_entry_inl]

/-- **Reading off the constant coordinate.** If a coefficient list has the value of a natural
number `k` in `A_p`, with `f` of positive degree, its constant coordinate is `k` modulo `2 ^ p`. -/
theorem getD_mod_of_val_eq {p : ℕ} {fl y : List ℕ} {k : ℕ} (hfl : fl ≠ [])
    (h : val p fl y = (k : Ring p fl)) : y.getD 0 0 % 2 ^ p = k % 2 ^ p := by
  rw [← GaloisRingArith.val_singleton] at h
  simpa using GaloisRingArith.mod_eq_of_val_eq h (List.length_pos_iff.mpr hfl)

/-! ### The root and the clock in polynomial time -/

/-- The exponent of the modulus is polynomial-time, in unary from unary. -/
theorem modulusExp_polyTime : ComputableInPolyTime modulusExp encUnary encUnary := by
  have hb := ComputableInPolyTime.unary_to_binary
  have hlog := ComputableInPolyTime.binary_log_two.comp hb
  have harg := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 4) hlog)
    (ComputableInPolyTime.const 2)
  exact ComputableInPolyTime.binary_log_two.comp (hb.comp harg)

/-- `3 ^ t ≤ (4 ⌊log₂ m⌋ + 2) ^ 2` for the exponent `t` of the modulus. -/
theorem three_pow_modulusExp_le (m : ℕ) : 3 ^ modulusExp m ≤ (4 * Nat.log 2 m + 2) ^ 2 := by
  have h := Nat.pow_log_le_self 2 (show 4 * Nat.log 2 m + 2 ≠ 0 by omega)
  calc 3 ^ modulusExp m ≤ 4 ^ modulusExp m := Nat.pow_le_pow_left (by norm_num) _
    _ = (2 ^ modulusExp m) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    _ ≤ (4 * Nat.log 2 m + 2) ^ 2 := Nat.pow_le_pow_left h _

/-- **The modulus is polynomial-time**, from the number of edges in unary. -/
theorem modulus_polyTime : ComputableInPolyTime modulus encUnary (encList encNat) := by
  have hb := ComputableInPolyTime.unary_to_binary
  have hlog := ComputableInPolyTime.binary_log_two.comp hb
  have hE : ComputableInPolyTime (fun m => 3 ^ modulusExp m) encUnary encUnary := by
    refine ComputableInPolyTime.binary_to_unary_bounded
      (ComputableInPolyTime.binary_pow.comp ((ComputableInPolyTime.const 3).prod
        modulusExp_polyTime))
      ((ComputableInPolyTime.unary_pow 2).comp (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 4) hlog)
        (ComputableInPolyTime.const 2))) three_pow_modulusExp_le
  have hrange := ComputableInPolyTime.range.comp
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hE)
  have hi := ComputableInPolyTime.snd encUnary encUnary
  have htest : ComputableInPolyTime (fun q : ℕ × ℕ => decide (q.2 = 0 ∨ q.2 = 3 ^ modulusExp q.1))
      (encPair encUnary encUnary) encBool :=
    ComputableInPolyTime.decide_or
      (ComputableInPolyTime.decide_eq' hi (ComputableInPolyTime.const 0))
      (ComputableInPolyTime.decide_eq' hi (hE.comp (ComputableInPolyTime.fst _ _)))
  have hbody : ComputableInPolyTime (fun q : ℕ × ℕ =>
      if q.2 = 0 ∨ q.2 = 3 ^ modulusExp q.1 then 1 else 0) (encPair encUnary encUnary) encNat :=
    (ComputableInPolyTime.ite htest
      (ComputableInPolyTime.const 1 : ComputableInPolyTime (fun _ : ℕ × ℕ => (1 : ℕ))
        (encPair encUnary encUnary) encNat)
      (ComputableInPolyTime.const 0)).of_enc_eq fun q => by simp only [decide_eq_true_eq]
  unfold modulus
  exact ComputableInPolyTime.mapWithInput
    (f := fun m i => if i = 0 ∨ i = 3 ^ modulusExp m then 1 else 0) hrange hbody

/-- The number of edges of a capped input, in unary. -/
private theorem edges_polyTime :
    ComputableInPolyTime (fun q : ℕ × ℕ × ExplicitTensorNetwork ℕ => q.2.2.numEdges)
      ExplicitTensorNetwork.encContractionInput encUnary :=
  ExplicitTensorNetwork.numEdges_polyTime

/-- The network of a capped input. -/
private theorem network_polyTime :
    ComputableInPolyTime (fun q : ℕ × ℕ × ExplicitTensorNetwork ℕ => q.2.2)
      ExplicitTensorNetwork.encContractionInput ExplicitTensorNetwork.encExplicitNetwork :=
  (ComputableInPolyTime.snd encNat ExplicitTensorNetwork.encExplicitNetwork).comp
    (ComputableInPolyTime.snd encUnary (encPair encNat ExplicitTensorNetwork.encExplicitNetwork))

/-- **The root descriptors as vertex descriptors are polynomial-time.** -/
theorem rootNet_polyTime :
    ComputableInPolyTime rootNet (DescribedNetwork.encDescribed encT)
      (DescribedNetwork.encDescribed (VertexDesc.enc encT)) := by
  have hpair : ComputableInPolyTime (DescribedNetwork.equivProd (T := T))
      (DescribedNetwork.encDescribed encT)
      (encPair encUnary (encList (encPair (encList encNat) encT))) :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have hm := (ComputableInPolyTime.fst _ _).comp hpair
  have hvs := (ComputableInPolyTime.snd _ _).comp hpair
  have hv : ComputableInPolyTime (fun q : DescribedNetwork T × (List ℕ × T) =>
      (q.2.1, (Sum.inl q.2.2 : VertexDesc T)))
      (encPair (DescribedNetwork.encDescribed encT) (encPair (encList encNat) encT))
      (encPair (encList encNat) (VertexDesc.enc encT)) :=
    ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)).prod
      ((ComputableInPolyTime.sumInl _ _).comp
        ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)))
  have hmap := ComputableInPolyTime.mapWithInput
    (f := fun _ v => (v.1, (Sum.inl v.2 : VertexDesc T))) hvs hv
  have hout : ComputableInPolyTime (DescribedNetwork.equivProd (T := VertexDesc T)).symm
      (encPair encUnary (encList (encPair (encList encNat) (VertexDesc.enc encT))))
      (DescribedNetwork.encDescribed (VertexDesc.enc encT)) :=
    ComputableInPolyTime.of_eq fun _ => rfl
  exact (hout.comp (hm.prod hmap)).of_enc_eq fun _ => rfl

/-- **The root call is polynomial-time**, from a capped input. -/
theorem root_polyTime : ComputableInPolyTime root ExplicitTensorNetwork.encContractionInput
    (encCall (encList encNat)) := by
  have hp := ComputableInPolyTime.fst encUnary (encPair encNat
    ExplicitTensorNetwork.encExplicitNetwork)
  have hr := (ComputableInPolyTime.fst encNat ExplicitTensorNetwork.encExplicitNetwork).comp
    (ComputableInPolyTime.snd encUnary (encPair encNat ExplicitTensorNetwork.encExplicitNetwork))
  exact (edges_polyTime.prod ((ComputableInPolyTime.const 0).prod
    ((ComputableInPolyTime.unary_add' edges_polyTime (ComputableInPolyTime.const 1)).prod
      (hp.prod ((modulus_polyTime.comp edges_polyTime).prod hr))))).prod
    ((rootNet_polyTime (encList encNat)).comp network_polyTime)

/-- **The clock is polynomial-time**, from a capped input. -/
theorem fuel_polyTime : ComputableInPolyTime fuel ExplicitTensorNetwork.encContractionInput
    encNat :=
  (ComputableInPolyTime.unary_two_pow_div_sqrt_log_two fuelConst).comp
    (ComputableInPolyTime.unary_add' edges_polyTime
      (ComputableInPolyTime.fst encUnary (encPair encNat
        ExplicitTensorNetwork.encExplicitNetwork)))

/-! ### The result -/

/-- **The result of the machine** on an input `(P, r, G)`: with the capped precision `p`, the
constant coordinate of a returned root value modulo `2 ^ p` if the run returns a value tagged
`0`, and direct summation otherwise. -/
@[expose] noncomputable def fastValue (q : ℕ × ℕ × ExplicitTensorNetwork ℕ) : ℕ :=
  ((scheme tableEntry mk).run fuel root (ExplicitTensorNetwork.capPrecision q)).elim
    (q.2.2.contraction % 2 ^ q.1)
    fun v => if v.1 = 0 then v.2.getD 0 0 % 2 ^ (ExplicitTensorNetwork.capPrecision q).1
      else q.2.2.contraction % 2 ^ q.1

/-- **The machine is correct on well-formed inputs**, for every fuel. If the step of an active
call is correct and well-formedness passes to the children, then on every input whose root is
well-formed the result is the contraction modulo `2 ^ P`. -/
theorem fastValue_eq {WF : Call (List ℕ) → Prop} (hstep : StepCorrect tableEntry mk WF)
    (hwf : WFChildren mk WF)
    (q : ℕ × ℕ × ExplicitTensorNetwork ℕ)
    (hroot : WF (root (ExplicitTensorNetwork.capPrecision q))) :
    fastValue mk q = q.2.2.contraction % 2 ^ q.1 := by
  unfold fastValue
  rcases hrun : (scheme tableEntry mk).run fuel root (ExplicitTensorNetwork.capPrecision q) with
    _ | ⟨t, y⟩
  · rfl
  · simp only [Option.elim_some]
    split_ifs with ht
    · subst ht
      have hy := eq_value_of_run tableEntry mk (fuel := fuel) (root := root) rfl hrun
      have hval : val (ExplicitTensorNetwork.capPrecision q).1
          (modulus (ExplicitTensorNetwork.capPrecision q).2.2.numEdges) y =
          (rootNet (ExplicitTensorNetwork.capPrecision q).2.2).contraction fun t bs =>
            val (ExplicitTensorNetwork.capPrecision q).1
              (modulus (ExplicitTensorNetwork.capPrecision q).2.2.numEdges)
              (VertexDesc.entry tableEntry t bs) :=
        hy ▸ val_value tableEntry mk hstep hwf _ hroot
      rw [val_rootNet] at hval
      rw [getD_mod_of_val_eq (modulus_ne_nil _) hval]
      exact ExplicitTensorNetwork.contraction_mod_two_pow_min q.1 q.2.2
    · rfl

/-! ### The machine -/

/-- The encoding of an input `(P, r, G)`: the precision and the number of rows in binary, and the
network. -/
abbrev encInput : ℕ × ℕ × ExplicitTensorNetwork ℕ ↪ List Bool :=
  encPair encNat (encPair encNat ExplicitTensorNetwork.encExplicitNetwork)

variable {mk}

/-- **The clocked run** from a capped input, as one native machine, given polynomial-time
components of the scheme. -/
@[expose] noncomputable def runCertificate
    (hpoly : (scheme tableEntry mk).PolyTime (encCall (encList encNat)) encFrame encValue) :
    NativeCertificate ((scheme tableEntry mk).run fuel root)
      ExplicitTensorNetwork.encContractionInput
      (encOption encValue) :=
  Scheme.certificate hpoly (leafCertificate mk) (NativeCertificate.ofPolyTime fuel_polyTime)
    (NativeCertificate.ofPolyTime root_polyTime)

/-- The constant coordinate of a value modulo `2 ^ p`, for the capped precision `p`. -/
theorem decode_polyTime :
    ComputableInPolyTime (fun q : (ℕ × ℕ × ExplicitTensorNetwork ℕ) × (ℕ × List ℕ) =>
      q.2.2.getD 0 0 % 2 ^ (ExplicitTensorNetwork.capPrecision q.1).1)
      (encPair encInput encValue) encNat := by
  have hcap := (ComputableInPolyTime.fst _ _).comp
    (ExplicitTensorNetwork.capPrecision_polyTime.comp (ComputableInPolyTime.fst encInput encValue))
  have hy := (ComputableInPolyTime.snd encUnary (encList encNat)).comp
    (ComputableInPolyTime.snd encInput encValue)
  exact GaloisRingArith.computableInPolyTime_mod_two_pow
    ((ComputableInPolyTime.listGetD (encA := encNat) 0).comp
      (hy.prod (ComputableInPolyTime.const 0)))
    hcap

/-- Whether a value is tagged `0`. -/
theorem tag_polyTime :
    ComputableInPolyTime (fun q : (ℕ × ℕ × ExplicitTensorNetwork ℕ) × (ℕ × List ℕ) =>
      decide (q.2.1 = 0)) (encPair encInput encValue) encBool :=
  ComputableInPolyTime.decide_eq' ((ComputableInPolyTime.fst encUnary (encList encNat)).comp
    (ComputableInPolyTime.snd encInput encValue)) (ComputableInPolyTime.const 0)

/-- **The fast machine**: cap the precision and run the recursion; on a value tagged `0`, read
off its constant coordinate, and otherwise sum directly. It computes `fastValue`. -/
@[expose] noncomputable def fastCertificate
    (hpoly : (scheme tableEntry mk).PolyTime (encCall (encList encNat)) encFrame encValue) :
    NativeCertificate (fastValue mk) encInput encNat :=
  (NativeCertificate.option
    ((runCertificate hpoly).comp
      (NativeCertificate.ofPolyTime ExplicitTensorNetwork.capPrecision_polyTime))
    ExplicitTensorNetwork.directContractionBinaryCertificate
    (NativeCertificate.branch (NativeCertificate.ofPolyTime tag_polyTime)
      (NativeCertificate.ofPolyTime decode_polyTime)
      (ExplicitTensorNetwork.directContractionBinaryCertificate.comp
        (NativeCertificate.ofPolyTime (ComputableInPolyTime.fst encInput encValue))))).congr
    fun q => by
      simp only [fastValue, Function.comp_apply]
      cases (scheme tableEntry mk).run fuel root (ExplicitTensorNetwork.capPrecision q) with
      | none => rfl
      | some v => simp only [Option.elim_some, decide_eq_true_eq]

/-- The time of the fast machine, unfolded: the capped run twice, the input, and the decoding or
direct summation. -/
theorem fastCertificate_time
    (hpoly : (scheme tableEntry mk).PolyTime (encCall (encList encNat)) encFrame encValue)
    (q : ℕ × ℕ × ExplicitTensorNetwork ℕ) :
    (fastCertificate hpoly).time q =
      2 * ((NativeCertificate.ofPolyTime ExplicitTensorNetwork.capPrecision_polyTime).time q +
        (runCertificate hpoly).time (ExplicitTensorNetwork.capPrecision q)) +
      (encInput q).length +
      ((scheme tableEntry mk).run fuel root (ExplicitTensorNetwork.capPrecision q)).elim
        (ExplicitTensorNetwork.directContractionBinaryCertificate.time q) fun v =>
          (NativeCertificate.ofPolyTime tag_polyTime).time (q, v) +
            if decide (v.1 = 0) = true then
              (NativeCertificate.ofPolyTime decode_polyTime).time (q, v)
            else (NativeCertificate.ofPolyTime
                (ComputableInPolyTime.fst encInput encValue)).time (q, v) +
              ExplicitTensorNetwork.directContractionBinaryCertificate.time q := rfl

/-- The space of the fast machine, unfolded. -/
theorem fastCertificate_space
    (hpoly : (scheme tableEntry mk).PolyTime (encCall (encList encNat)) encFrame encValue)
    (q : ℕ × ℕ × ExplicitTensorNetwork ℕ) :
    (fastCertificate hpoly).space q =
      2 * ((NativeCertificate.ofPolyTime ExplicitTensorNetwork.capPrecision_polyTime).space q +
        (runCertificate hpoly).space (ExplicitTensorNetwork.capPrecision q)) +
      (encInput q).length +
      ((scheme tableEntry mk).run fuel root (ExplicitTensorNetwork.capPrecision q)).elim
        (ExplicitTensorNetwork.directContractionBinaryCertificate.space q) fun v =>
          (NativeCertificate.ofPolyTime tag_polyTime).space (q, v) +
            if decide (v.1 = 0) = true then
              (NativeCertificate.ofPolyTime decode_polyTime).space (q, v)
            else (NativeCertificate.ofPolyTime
                (ComputableInPolyTime.fst encInput encValue)).space (q, v) +
              ExplicitTensorNetwork.directContractionBinaryCertificate.space q := rfl

end Cslib.Circuits.Frontier.FastContraction
