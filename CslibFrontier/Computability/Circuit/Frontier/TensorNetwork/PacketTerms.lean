/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.CoeffScheme
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import CslibFrontier.Tactic.OptionMatch
import Mathlib.Data.List.GetD
import CslibFrontier.Tactic.EncLen

/-!
# The native packet evaluator

The native packet evaluator (`Cslib.Circuits.Frontier.NativePacket`) computes the entries of the
packet vertices of the child networks of the contraction algorithm of [OpenAI2026ETH] on
coefficient lists (§D.4.6, p. 63). This file makes it one native machine with the source's
bounds: time `exp(O(L log s))` and polynomial space.

* **Row terms in polynomial time.** Kernel values, cross ratios, local forms, mode coefficients
  and values, and the row terms are polynomial-time
  (`NativePacket.kernelValueList_polyTime`, …, `NativePacket.rowTermList_polyTime`), with the
  precision `p`, the bit counts `a` and `i`, the number of slots `L` and the number of exponents
  `nb` in unary, and the integers in binary sign-magnitude form (`Turing.MultiTapeTM.encIntBin`).
  The `2`-adic valuation needs at most `size |n|` halvings (`NativePacket.twoVal_polyTime`).
* **A packet context** (`NativePacket.PacketCtx`) holds what the row terms and the modes need,
  with the number of tiles `2 ^ (i + 1)` in unary. Coefficient extraction for a packet
  (`NativePacket.packetTerms`) is an instance of `CoeffScheme.Terms` with polynomial-time data
  (`NativePacket.packetTerms_polyTime`).
* **The native packet entry** (`NativePacket.packetEntryNative`) multiplies the value of the stack
  recursion by the powers of the source mode values. Its value in `A_p` is `packetEntry`
  (`NativePacket.val_packetEntryNative_eq`), and one native machine computes it
  (`NativePacket.entryCertificate`) in time `K (m + 2) ^ L Z ^ K` and space `K Z ^ K`, for `m`
  target modes, `L` row ports and `Z` polynomial in the input and the reduced coefficient lists
  (`NativePacket.entryCertificate_le`). The exponents are read in unary, since the source's are
  below the precision.
* **Descriptors** (`NativePacket.PacketDesc`): a packet context, the ports `(isRow, slot)` of the
  vertex in its port order and the dense exponents, "its packet data, the tuple `β`, the
  interpolation value, and the creation precision" (p. 63). `NativePacket.vertexCertificate`
  computes the entry at the bits on the ports, the evaluator of
  `Cslib.Circuits.Frontier.DescribedNetwork` direct summation at coefficient lists, with the same
  bounds (`NativePacket.vertexCertificate_le`).

## Main definitions

* `Cslib.Circuits.Frontier.NativePacket.PacketCtx`: the context of a packet entry.
* `Cslib.Circuits.Frontier.NativePacket.packetTerms`: coefficient extraction for a packet.
* `Cslib.Circuits.Frontier.NativePacket.packetEntryNative`: the native packet entry.
* `Cslib.Circuits.Frontier.NativePacket.entryCertificate`: its native machine.
* `Cslib.Circuits.Frontier.NativePacket.PacketDesc`,
  `Cslib.Circuits.Frontier.NativePacket.packetVertexEntry`,
  `Cslib.Circuits.Frontier.NativePacket.vertexCertificate`: descriptors of packet vertices, their
  entries at the bits on their ports, and the native machine for them.

## Main results

* `Cslib.Circuits.Frontier.NativePacket.twoVal_polyTime`: the `2`-adic valuation.
* `Cslib.Circuits.Frontier.NativePacket.PacketCtx.mk_polyTime`: construction from certified fields
  with the existing unary/binary packet encoding.
* `Cslib.Circuits.Frontier.NativePacket.kernelValueList_polyTime`,
  `Cslib.Circuits.Frontier.NativePacket.crossRatioList_polyTime`: kernel values and cross ratios.
* `Cslib.Circuits.Frontier.NativePacket.rowTermList_polyTime`: the row terms.
* `Cslib.Circuits.Frontier.NativePacket.val_packetEntryNative_eq`,
  `Cslib.Circuits.Frontier.NativePacket.map_val_packetEntryNative`: the native entry is the
  packet entry, in `A_p` and in every ring receiving it.
* `Cslib.Circuits.Frontier.NativePacket.entryCertificate_le`,
  `Cslib.Circuits.Frontier.NativePacket.vertexCertificate_le`: their time and space.
* `Cslib.Circuits.Frontier.NativePacket.val_packetVertexEntry`: the entry of a packet vertex is
  the packet entry at the ports read from its bits.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.6 (p. 63).
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local macro "ℤ₍₂₎" : term => `(Valuation.integer (Rat.padicValuation 2))

namespace NativePacket

open GaloisRingArith TensorNetwork Turing.MultiTapeTM Cslib.GenericRAM

attribute [local irreducible] ComputableInPolyTime

/-! ### The `2`-adic valuation by halving -/

/-- The valuation by halving is `padicValNat 2` whenever the fuel exceeds the valuation. -/
theorem twoValAux_eq_of_lt : ∀ (k m : ℕ), (m = 0 ∨ padicValNat 2 m < k) →
    twoValAux k m = padicValNat 2 m
  | 0, m, h => by
    rcases h with rfl | h
    · rw [twoValAux]; simp
    · omega
  | k + 1, m, h => by
    rw [twoValAux]
    split_ifs with hm
    · obtain ⟨hm0, hm2⟩ := hm
      have hm' : m = 2 * (m / 2) := by omega
      have hv : padicValNat 2 m = padicValNat 2 (m / 2) + 1 := by
        conv_lhs => rw [hm', padicValNat.mul two_ne_zero (by omega), padicValNat_self, add_comm]
      rw [hv, twoValAux_eq_of_lt k (m / 2) (by omega)]
    · by_cases hm0 : m = 0
      · rw [hm0]; simp
      · exact (padicValNat.eq_zero_of_not_dvd fun h2 => hm ⟨hm0, by omega⟩).symm

/-- The valuation of a nonzero natural is below its bit length. -/
theorem padicValNat_two_lt_size {m : ℕ} (hm : m ≠ 0) : padicValNat 2 m < m.size := by
  have h1 : 2 ^ padicValNat 2 m ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) pow_padicValNat_dvd
  have h2 := Nat.lt_size_self m
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (h1.trans_lt h2)

/-- **The valuation needs only `size |n|` halvings.** -/
theorem twoVal_eq_twoValAux_size (n : ℤ) : twoVal n = twoValAux n.natAbs.size n.natAbs := by
  rw [twoVal_eq, twoValAux_eq_of_lt]
  · rfl
  · by_cases h : n.natAbs = 0
    · exact .inl h
    · exact .inr (padicValNat_two_lt_size h)

/-- One step of the valuation by halving, on the value, the count and whether it has stopped. -/
def twoValStep (s : ℕ × ℕ × Bool) : ℕ × ℕ × Bool :=
  if s.2.2 = false ∧ s.1 ≠ 0 ∧ s.1 % 2 = 0 then (s.1 / 2, s.2.1 + 1, false) else (s.1, s.2.1, true)

private theorem twoValStep_iterate : ∀ (k m v : ℕ),
    (twoValStep^[k] (m, v, false)).2.1 = v + twoValAux k m ∧
      ∀ m' v', twoValStep^[k] (m', v', true) = (m', v', true)
  | 0, m, v => ⟨by simp [twoValAux], fun _ _ => rfl⟩
  | k + 1, m, v => by
    refine ⟨?_, fun m' v' => ?_⟩
    · rw [Function.iterate_succ_apply]
      by_cases hm : m ≠ 0 ∧ m % 2 = 0
      · have h1 : twoValStep (m, v, false) = (m / 2, v + 1, false) := by
          simp [twoValStep, hm.1, hm.2]
        have h2 : twoValAux (k + 1) m = twoValAux k (m / 2) + 1 := by
          simp [twoValAux, hm.1, hm.2]
        rw [h1, h2, (twoValStep_iterate k (m / 2) (v + 1)).1]
        ring
      · have h1 : twoValStep (m, v, false) = (m, v, true) := by
          simp only [twoValStep]
          split_ifs with h
          · exact absurd ⟨h.2.1, h.2.2⟩ hm
          · rfl
        have h2 : twoValAux (k + 1) m = 0 := by
          simp only [twoValAux, hm, ↓reduceIte]
        rw [h1, h2, (twoValStep_iterate k m v).2]
        simp
    · have h1 : twoValStep (m', v', true) = (m', v', true) := by simp [twoValStep]
      rw [Function.iterate_succ_apply, h1, (twoValStep_iterate k m' v').2]

private theorem foldl_range_eq_iterate {β : Type} (f : β → β) : ∀ (k : ℕ) (s : β),
    (List.range k).foldl (fun s _ => f s) s = f^[k] s
  | 0, s => rfl
  | k + 1, s => by
    rw [List.range_succ, List.foldl_append, foldl_range_eq_iterate f k s, List.foldl_cons,
      List.foldl_nil, Function.iterate_succ_apply']

/-- The valuation by halving as a fold over `size |n|` steps. -/
theorem twoVal_eq_foldl (n : ℤ) :
    twoVal n = ((List.range n.natAbs.size).foldl (fun s _ => twoValStep s)
      (n.natAbs, 0, false)).2.1 := by
  rw [foldl_range_eq_iterate, (twoValStep_iterate _ _ 0).1, zero_add, twoVal_eq_twoValAux_size]

section PolyTime

variable {α : Type} {encIn : α ↪ List Bool}

/-- **The `2`-adic valuation is polynomial-time**, on binary integers, in unary. -/
theorem twoVal_polyTime : ComputableInPolyTime twoVal encIntBin encUnary := by
  let encS := encPair encNat (encPair encUnary encBool)
  have hstep : ComputableInPolyTime (fun q : (ℤ × (ℕ × ℕ × Bool)) × ℕ => twoValStep q.1.2)
      (encPair (encPair encIntBin encS) encUnary) encS := by
    have hs := (ComputableInPolyTime.snd encIntBin encS).comp
      (ComputableInPolyTime.fst (encPair encIntBin encS) encUnary)
    have hm := (ComputableInPolyTime.fst encNat (encPair encUnary encBool)).comp hs
    have hv := (ComputableInPolyTime.fst encUnary encBool).comp
      ((ComputableInPolyTime.snd encNat (encPair encUnary encBool)).comp hs)
    have hb := (ComputableInPolyTime.snd encUnary encBool).comp
      ((ComputableInPolyTime.snd encNat (encPair encUnary encBool)).comp hs)
    have hgo := (ComputableInPolyTime.binary_div.comp
      (hm.prod (ComputableInPolyTime.const 2))).prod
      ((ComputableInPolyTime.unary_succ.comp hv).prod
        (ComputableInPolyTime.const (encOut := encBool) false))
    have hstay := hm.prod (hv.prod (ComputableInPolyTime.const (encOut := encBool) true))
    refine (ComputableInPolyTime.ite hb hstay (ComputableInPolyTime.ite
      (ComputableInPolyTime.beq hm (ComputableInPolyTime.const 0)) hstay
      (ComputableInPolyTime.ite (ComputableInPolyTime.beq
        (ComputableInPolyTime.binary_mod.comp (hm.prod (ComputableInPolyTime.const 2)))
        (ComputableInPolyTime.const 0)) hgo hstay))).of_enc_eq fun q => congrArg encS ?_
    obtain ⟨⟨z, m, v, b⟩, j⟩ := q
    simp only [twoValStep]
    cases b <;> by_cases h0 : m = 0 <;> by_cases h2 : m % 2 = 0 <;> simp [h0, h2]
  have hfold := ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary)
    (step := fun _ s _ => twoValStep s)
    (ComputableInPolyTime.intBin_natAbs.prod
      ((ComputableInPolyTime.const 0).prod (ComputableInPolyTime.const false)))
    ⟨ComputableInPolyTime.range.comp
      (ComputableInPolyTime.binary_size.comp ComputableInPolyTime.intBin_natAbs),
      hstep, inferInstance, inferInstance⟩
    (growth := fun _ => 2) ⟨PolyBounded.const 2, fun z s _ _ => ?_⟩
  · refine ((ComputableInPolyTime.fst encUnary encBool).comp
      ((ComputableInPolyTime.snd encNat (encPair encUnary encBool)).comp hfold)).of_enc_eq
      fun z => ?_
    simp only [Function.comp_apply, twoVal_eq_foldl]
  · obtain ⟨m, v, b⟩ := s
    have hdiv : (encNat (m / 2)).length ≤ (encNat m).length := by
      change (m / 2).bits.length ≤ m.bits.length
      rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
      exact Nat.size_le_size (Nat.div_le_self _ _)
    simp only [twoValStep]
    split_ifs <;> cases b <;>
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBool_apply,
        List.length_cons, List.length_nil] <;> omega

end PolyTime


/-! ### Residues of integers -/

/-- The odd part of an integer in sign-magnitude form. -/
theorem ediv_two_pow_twoVal (n : ℤ) :
    n / 2 ^ twoVal n = if n < 0 then -((n.natAbs / 2 ^ twoVal n : ℕ) : ℤ)
      else ((n.natAbs / 2 ^ twoVal n : ℕ) : ℤ) := by
  have hdvd : 2 ^ twoVal n ∣ n.natAbs := by
    rw [twoVal_eq]; exact pow_padicValNat_dvd
  have hdvd' : (2 : ℤ) ^ twoVal n ∣ (n.natAbs : ℤ) := by exact_mod_cast hdvd
  generalize twoVal n = v at *
  split_ifs with h
  · have hn : n = -(n.natAbs : ℤ) := by rw [Int.ofNat_natAbs_of_nonpos h.le, neg_neg]
    conv_lhs => rw [hn]
    rw [Int.neg_ediv_of_dvd hdvd']
    push_cast
    rfl
  · have hn : n = (n.natAbs : ℤ) := (Int.natAbs_of_nonneg (not_lt.mp h)).symm
    conv_lhs => rw [hn]
    push_cast
    rfl

/-- The residue of an integer power of two. -/
theorem toNat_two_pow_emod (k p : ℕ) : ((2 : ℤ) ^ k % 2 ^ p).toNat = 2 ^ k % 2 ^ p := by
  rw [show (2 : ℤ) ^ k % 2 ^ p = ((2 ^ k % 2 ^ p : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast]

/-- The residue of a natural number. -/
theorem toNat_natCast_emod (m p : ℕ) : ((m : ℤ) % 2 ^ p).toNat = m % 2 ^ p := by
  rw [show (m : ℤ) % 2 ^ p = ((m % 2 ^ p : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast]

section PolyTime

variable {α : Type} {encIn : α ↪ List Bool}

/-- The odd part of a binary integer. -/
theorem oddPart_polyTime {z : α → ℤ} (hz : ComputableInPolyTime z encIn encIntBin) :
    ComputableInPolyTime (fun x => z x / 2 ^ twoVal (z x)) encIn encIntBin := by
  have habs := ComputableInPolyTime.intBin_natAbs.comp hz
  have hv := twoVal_polyTime.comp hz
  refine (ComputableInPolyTime.intBin_signMagnitude.comp
    ((ComputableInPolyTime.intBin_isNeg.comp hz).prod
      (ComputableInPolyTime.binary_div.comp
        (habs.prod (ComputableInPolyTime.binary_two_pow.comp hv))))).of_enc_eq fun x => ?_
  simp only [Function.comp_apply, decide_eq_true_eq, ediv_two_pow_twoVal (z x)]

/-- The residue modulo `2 ^ p` of a binary integer, with `p` in unary. -/
theorem residue_polyTime {n : α → ℤ} {p : α → ℕ}
    (hn : ComputableInPolyTime n encIn encIntBin) (hp : ComputableInPolyTime p encIn encUnary) :
    ComputableInPolyTime (fun x => (n x % 2 ^ p x).toNat) encIn encNat :=
  (ComputableInPolyTime.intBin_emodNat' hn
    (ComputableInPolyTime.binary_two_pow.comp hp)).of_enc_eq fun x => by
    simp only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat]

/-- An integer as a constant coefficient list, from its residue. -/
theorem intConst_polyTime {p : α → ℕ} {fl : α → List ℕ} {n : α → ℤ}
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hres : ComputableInPolyTime (fun x => (n x % 2 ^ p x).toNat) encIn encNat) :
    ComputableInPolyTime (fun x => intConst (p x) (fl x) (n x)) encIn (encList encNat) := by
  have h2 := ComputableInPolyTime.snd encIn encUnary
  refine computableInPolyTime_tabulate ((ComputableInPolyTime.length_list encNat).comp hfl)
    ((ComputableInPolyTime.ite (ComputableInPolyTime.beq h2 (ComputableInPolyTime.const 0))
      (hres.comp (ComputableInPolyTime.fst encIn encUnary))
      (ComputableInPolyTime.const 0)).of_enc_eq fun q => ?_)
  by_cases h : q.2 = 0 <;> simp [h]

/-- The constant list of a power of two `2 ^ k`, with `k` in unary. -/
theorem intConst_two_pow_polyTime {p : α → ℕ} {fl : α → List ℕ} {k : α → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => intConst (p x) (fl x) ((2 : ℤ) ^ k x)) encIn
      (encList encNat) :=
  intConst_polyTime hfl ((ComputableInPolyTime.binary_mod.comp
    ((ComputableInPolyTime.binary_two_pow.comp hk).prod
      (ComputableInPolyTime.binary_two_pow.comp hp))).of_enc_eq fun x => by
      simp only [Function.comp_apply, toNat_two_pow_emod])

/-- The constant list of a binary natural number. -/
theorem intConst_natCast_polyTime {p : α → ℕ} {fl : α → List ℕ} {m : α → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hm : ComputableInPolyTime m encIn encNat) :
    ComputableInPolyTime (fun x => intConst (p x) (fl x) (m x : ℤ)) encIn (encList encNat) :=
  intConst_polyTime hfl ((ComputableInPolyTime.binary_mod.comp
    (hm.prod (ComputableInPolyTime.binary_two_pow.comp hp))).of_enc_eq fun x => by
      simp only [Function.comp_apply, toNat_natCast_emod])

/-- The constant list of the odd part of a binary integer. -/
theorem intConst_oddPart_polyTime {p : α → ℕ} {fl : α → List ℕ} {z : α → ℤ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hz : ComputableInPolyTime z encIn encIntBin) :
    ComputableInPolyTime (fun x => intConst (p x) (fl x) (z x / 2 ^ twoVal (z x))) encIn
      (encList encNat) :=
  intConst_polyTime hfl (residue_polyTime (oddPart_polyTime hz) hp)

/-! ### Sums and products of lists -/

/-- **Products of computed lists of coefficient lists are polynomial-time.** -/
theorem prodList_polyTime {p : α → ℕ} {fl : α → List ℕ} {cs : α → List (List ℕ)}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hcs : ComputableInPolyTime cs encIn (encList (encList encNat))) :
    ComputableInPolyTime (fun x => prodList (p x) (fl x) (cs x)) encIn (encList encNat) := by
  have hstep : ComputableInPolyTime (fun q : (α × List ℕ) × List ℕ => mul (p q.1.1) (fl q.1.1)
      q.1.2 q.2) (encPair (encPair encIn (encList encNat)) (encList encNat)) (encList encNat) := by
    have hx := (ComputableInPolyTime.fst encIn (encList encNat)).comp
      (ComputableInPolyTime.fst (encPair encIn (encList encNat)) (encList encNat))
    exact computableInPolyTime_mul (hp.comp hx) (hfl.comp hx)
      ((ComputableInPolyTime.snd encIn (encList encNat)).comp (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.snd _ _)
  exact ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encList encNat) (encL := encList (encList encNat))
    (step := fun x acc c => mul (p x) (fl x) acc c) (computableInPolyTime_one hfl)
    ⟨hcs, hstep, inferInstance, inferInstance⟩
    ⟨polyBounded_reducedLength hp hfl, fun x acc c _ => by
      have := length_encList_le (length_mul (p x) (fl x) acc c) fun _ h => lt_of_mem_mul h
      omega⟩

/-- **Sums of computed lists of coefficient lists are polynomial-time.** -/
theorem sumList_polyTime {p : α → ℕ} {fl : α → List ℕ} {cs : α → List (List ℕ)}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hcs : ComputableInPolyTime cs encIn (encList (encList encNat))) :
    ComputableInPolyTime (fun x => sumList (p x) (fl x) (cs x)) encIn (encList encNat) := by
  have hstep : ComputableInPolyTime (fun q : (α × List ℕ) × List ℕ => add (p q.1.1) (fl q.1.1)
      q.1.2 q.2) (encPair (encPair encIn (encList encNat)) (encList encNat)) (encList encNat) := by
    have hx := (ComputableInPolyTime.fst encIn (encList encNat)).comp
      (ComputableInPolyTime.fst (encPair encIn (encList encNat)) (encList encNat))
    exact computableInPolyTime_add (hp.comp hx) (hfl.comp hx)
      ((ComputableInPolyTime.snd encIn (encList encNat)).comp (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.snd _ _)
  exact ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encList encNat) (encL := encList (encList encNat))
    (step := fun x acc c => add (p x) (fl x) acc c)
    (computableInPolyTime_tabulate (g := fun _ _ => 0)
      ((ComputableInPolyTime.length_list encNat).comp hfl) (ComputableInPolyTime.const 0))
    ⟨hcs, hstep, inferInstance, inferInstance⟩
    ⟨polyBounded_reducedLength hp hfl, fun x acc c _ => by
      have := length_encList_le (length_add (p x) (fl x) acc c) fun _ h => lt_of_mem_add h
      omega⟩

/-! ### Kernel values and cross ratios -/

/-- The linear factor `u + 2 ^ k ζ` for the odd part `u` of a binary integer. -/
theorem linFactor_polyTime {p : α → ℕ} {fl : α → List ℕ} {z : α → ℤ} {k : α → ℕ}
    {ζ : α → List ℕ} (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hz : ComputableInPolyTime z encIn encIntBin) (hk : ComputableInPolyTime k encIn encUnary)
    (hζ : ComputableInPolyTime ζ encIn (encList encNat)) :
    ComputableInPolyTime (fun x => linFactor (p x) (fl x) (z x / 2 ^ twoVal (z x)) (k x) (ζ x))
      encIn (encList encNat) :=
  computableInPolyTime_add hp hfl (intConst_oddPart_polyTime hp hfl hz)
    (computableInPolyTime_mul hp hfl (intConst_two_pow_polyTime hp hfl hk) hζ)

/-- The grid of `L` slots, with `L` in unary, as binary integers. -/
theorem gridList_polyTime : ComputableInPolyTime gridList encUnary (encList encIntBin) := by
  have hj := ComputableInPolyTime.intBin_natCast.comp (ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.snd encUnary encUnary))
  have hL := ComputableInPolyTime.intBin_natCast.comp (ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.fst encUnary encUnary))
  exact ComputableInPolyTime.mapWithInput (f := fun (L j : ℕ) => (j : ℤ) - (L : ℤ))
    (ComputableInPolyTime.range.comp (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.const 2) ComputableInPolyTime.id'))
    (ComputableInPolyTime.intBin_sub.comp (hj.prod hL))

end PolyTime


section PolyTime

variable {α : Type} {encIn : α ↪ List Bool}

/-- **The odd part of `C'(0)` is polynomial-time**, with `L` in unary. -/
theorem kernelUnitDen_polyTime {p : α → ℕ} {fl : α → List ℕ} {L : α → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hL : ComputableInPolyTime L encIn encUnary) :
    ComputableInPolyTime (fun x => kernelUnitDen (p x) (fl x) (L x)) encIn (encList encNat) := by
  have h1 := ComputableInPolyTime.fst encIn encIntBin
  have h2 := ComputableInPolyTime.snd encIn encIntBin
  have hfilt := ComputableInPolyTime.filterWithInput (test := fun _ q => decide (q ≠ 0))
    (gridList_polyTime.comp hL) (h2.decide_ne (ComputableInPolyTime.const 0))
  exact prodList_polyTime hp hfl (ComputableInPolyTime.mapWithInput
    (f := fun x q => intConst (p x) (fl x) ((0 - q) / 2 ^ twoVal (0 - q))) hfilt
    (intConst_oddPart_polyTime (hp.comp h1) (hfl.comp h1)
      (ComputableInPolyTime.intBin_sub.comp ((ComputableInPolyTime.const 0).prod h2))))

/-- **The kernel unit is polynomial-time.** -/
theorem kernelUnitList_polyTime {p : α → ℕ} {fl : α → List ℕ} {L : α → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hL : ComputableInPolyTime L encIn encUnary) :
    ComputableInPolyTime (fun x => kernelUnitList (p x) (fl x) (L x)) encIn (encList encNat) :=
  computableInPolyTime_inv hp hfl (kernelUnitDen_polyTime hp hfl hL)

/-- **Kernel values are polynomial-time**, with `a` and `L` in unary and `t`, `d` binary. -/
theorem kernelValueList_polyTime {p : α → ℕ} {fl : α → List ℕ} {a L : α → ℕ} {t d : α → ℤ}
    {ζ : α → List ℕ} (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary) (hL : ComputableInPolyTime L encIn encUnary)
    (ht : ComputableInPolyTime t encIn encIntBin) (hd : ComputableInPolyTime d encIn encIntBin)
    (hζ : ComputableInPolyTime ζ encIn (encList encNat)) :
    ComputableInPolyTime (fun x => kernelValueList (p x) (fl x) (a x) (L x) (t x) (d x) (ζ x))
      encIn (encList encNat) := by
  have hexp {z : α → ℤ} (hz : ComputableInPolyTime z encIn encIntBin) :
      ComputableInPolyTime (fun x => a x + 1 - twoVal (z x)) encIn encUnary :=
    ComputableInPolyTime.unary_sub' (ComputableInPolyTime.unary_add' ha
      (ComputableInPolyTime.const 1)) (twoVal_polyTime.comp hz)
  have htd := ComputableInPolyTime.intBin_sub.comp (ht.prod hd)
  have hmid : ComputableInPolyTime (fun x => if d x = t x then one (fl x) else
      mul (p x) (fl x) (intConst (p x) (fl x) (2 ^ (a x + 1 - twoVal (t x - d x)))) (ζ x))
      encIn (encList encNat) :=
    (ComputableInPolyTime.ite (ComputableInPolyTime.beq hd ht) (computableInPolyTime_one hfl)
      (computableInPolyTime_mul hp hfl (intConst_two_pow_polyTime hp hfl (hexp htd)) hζ)).of_enc_eq
      fun x => by by_cases h : d x = t x <;> simp [h]
  have h1 := ComputableInPolyTime.fst encIn encIntBin
  have h2 := ComputableInPolyTime.snd encIn encIntBin
  have htest : ComputableInPolyTime (fun z : α × ℤ => decide (z.2 ≠ d z.1 ∧ z.2 ≠ t z.1))
      (encPair encIn encIntBin) encBool :=
    (ComputableInPolyTime.ite (ComputableInPolyTime.beq h2 (hd.comp h1))
      (ComputableInPolyTime.const (encOut := encBool) false) (ComputableInPolyTime.ite
        (ComputableInPolyTime.beq h2 (ht.comp h1))
        (ComputableInPolyTime.const (encOut := encBool) false)
        (ComputableInPolyTime.const (encOut := encBool) true))).of_enc_eq fun z => by
      by_cases h : z.2 = d z.1 <;> by_cases h' : z.2 = t z.1 <;> simp [h, h']
  have hfilt := ComputableInPolyTime.filterWithInput
    (test := fun x q => decide (q ≠ d x ∧ q ≠ t x)) (gridList_polyTime.comp hL) htest
  have htq := ComputableInPolyTime.intBin_sub.comp ((ht.comp h1).prod h2)
  have hfac := ComputableInPolyTime.mapWithInput
    (f := fun x q => linFactor (p x) (fl x) ((t x - q) / 2 ^ twoVal (t x - q))
      (a x + 1 - twoVal (t x - q)) (ζ x)) hfilt
    (linFactor_polyTime (hp.comp h1) (hfl.comp h1) htq
      (ComputableInPolyTime.unary_sub' (ComputableInPolyTime.unary_add' (ha.comp h1)
        (ComputableInPolyTime.const 1)) (twoVal_polyTime.comp htq)) (hζ.comp h1))
  exact computableInPolyTime_mul hp hfl
    (computableInPolyTime_mul hp hfl (kernelUnitList_polyTime hp hfl hL) hmid)
    (prodList_polyTime hp hfl hfac)

/-- **Cross ratios are polynomial-time.** -/
theorem crossRatioList_polyTime {p : α → ℕ} {fl : α → List ℕ} {a i : α → ℕ} {t d : α → ℤ}
    {ζ : α → List ℕ} (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary) (hi : ComputableInPolyTime i encIn encUnary)
    (ht : ComputableInPolyTime t encIn encIntBin) (hd : ComputableInPolyTime d encIn encIntBin)
    (hζ : ComputableInPolyTime ζ encIn (encList encNat)) :
    ComputableInPolyTime (fun x => crossRatioList (p x) (fl x) (a x) (i x) (t x) (d x) (ζ x))
      encIn (encList encNat) := by
  have htd := ComputableInPolyTime.intBin_sub.comp (ht.prod hd)
  have hv := twoVal_polyTime.comp htd
  exact computableInPolyTime_mul hp hfl
    (intConst_two_pow_polyTime hp hfl (ComputableInPolyTime.unary_sub'
      (ComputableInPolyTime.unary_add' hi (ComputableInPolyTime.const 1)) hv))
    (computableInPolyTime_inv hp hfl (linFactor_polyTime hp hfl htd
      (ComputableInPolyTime.unary_sub' (ComputableInPolyTime.unary_add' ha
        (ComputableInPolyTime.const 1)) hv) hζ))

end PolyTime


section PolyTime

variable {α : Type} {encIn : α ↪ List Bool}

/-- **Local forms are polynomial-time**, with the column ports in binary. -/
theorem localFormList_polyTime {p : α → ℕ} {fl : α → List ℕ} {a L : α → ℕ} {t : α → ℤ}
    {cols : α → List (ℕ × Bool)} {x : α → ℕ} {ζ : α → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary) (hL : ComputableInPolyTime L encIn encUnary)
    (ht : ComputableInPolyTime t encIn encIntBin)
    (hcols : ComputableInPolyTime cols encIn (encList (encPair encNat encBool)))
    (hx : ComputableInPolyTime x encIn encNat)
    (hζ : ComputableInPolyTime ζ encIn (encList encNat)) :
    ComputableInPolyTime (fun z => localFormList (p z) (fl z) (a z) (L z) (t z) (cols z) (x z)
      (ζ z)) encIn (encList encNat) := by
  have h1 := ComputableInPolyTime.fst encIn (encPair encNat encBool)
  have h2 := ComputableInPolyTime.snd encIn (encPair encNat encBool)
  have hd := ComputableInPolyTime.intBin_sub.comp
    ((ComputableInPolyTime.intBin_natCast.comp ((ComputableInPolyTime.fst _ _).comp h2)).prod
      (ComputableInPolyTime.intBin_natCast.comp (hx.comp h1)))
  have hf : ComputableInPolyTime (fun q : α × (ℕ × Bool) =>
      if q.2.2 then kernelValueList (p q.1) (fl q.1) (a q.1) (L q.1) (t q.1) ((q.2.1 : ℤ) - x q.1)
        (ζ q.1) else zero (fl q.1)) (encPair encIn (encPair encNat encBool)) (encList encNat) :=
    ComputableInPolyTime.ite ((ComputableInPolyTime.snd _ _).comp h2)
      (kernelValueList_polyTime (hp.comp h1) (hfl.comp h1) (ha.comp h1) (hL.comp h1) (ht.comp h1)
        hd (hζ.comp h1))
      (computableInPolyTime_tabulate (g := fun _ _ => 0)
        ((ComputableInPolyTime.length_list encNat).comp (hfl.comp h1))
        (ComputableInPolyTime.const 0))
  exact sumList_polyTime hp hfl (ComputableInPolyTime.mapWithInput
    (f := fun z c => if c.2 then kernelValueList (p z) (fl z) (a z) (L z) (t z) ((c.1 : ℤ) - x z)
      (ζ z) else zero (fl z)) hcols hf)

/-- **Mode coefficients are polynomial-time**, with the slots in binary and the exponent `b` in
unary. -/
theorem modeCoeffList_polyTime {p : α → ℕ} {fl : α → List ℕ} {a L i : α → ℕ} {t : α → ℤ}
    {differ : α → Bool} {x y₀ b : α → ℕ} {ζ : α → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary) (hL : ComputableInPolyTime L encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary) (ht : ComputableInPolyTime t encIn encIntBin)
    (hdiffer : ComputableInPolyTime differ encIn encBool)
    (hx : ComputableInPolyTime x encIn encNat) (hy₀ : ComputableInPolyTime y₀ encIn encNat)
    (hb : ComputableInPolyTime b encIn encUnary)
    (hζ : ComputableInPolyTime ζ encIn (encList encNat)) :
    ComputableInPolyTime (fun z => modeCoeffList (p z) (fl z) (a z) (L z) (i z) (t z) (differ z)
      (x z) (y₀ z) (b z) (ζ z)) encIn (encList encNat) := by
  have hd := ComputableInPolyTime.intBin_sub.comp
    ((ComputableInPolyTime.intBin_natCast.comp hy₀).prod
      (ComputableInPolyTime.intBin_natCast.comp hx))
  have hzero := computableInPolyTime_tabulate (g := fun _ _ => 0)
    ((ComputableInPolyTime.length_list encNat).comp hfl) (ComputableInPolyTime.const 0)
  refine (ComputableInPolyTime.ite hdiffer (ComputableInPolyTime.ite (ComputableInPolyTime.beq
      (ComputableInPolyTime.binary_testBit hx hi) (ComputableInPolyTime.binary_testBit hy₀ hi))
      (computableInPolyTime_mul hp hfl (kernelValueList_polyTime hp hfl ha hL ht hd hζ)
        (computableInPolyTime_pow hp hfl (crossRatioList_polyTime hp hfl ha hi ht hd hζ) hb))
      hzero) hzero).of_enc_eq fun z => ?_
  simp only [modeCoeffList]
  cases hdz : differ z <;> by_cases hbit : (x z).testBit (i z) = (y₀ z).testBit (i z) <;>
    simp [hbit, GaloisRingArith.zero]

/-- **Mode values are polynomial-time**, with the exponent `b` in unary. -/
theorem modeValueList_polyTime {p : α → ℕ} {fl : α → List ℕ} {i : α → ℕ} {differ : α → Bool}
    {cols : α → List (ℕ × Bool)} {y₀ b : α → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hi : ComputableInPolyTime i encIn encUnary)
    (hdiffer : ComputableInPolyTime differ encIn encBool)
    (hcols : ComputableInPolyTime cols encIn (encList (encPair encNat encBool)))
    (hy₀ : ComputableInPolyTime y₀ encIn encNat) (hb : ComputableInPolyTime b encIn encUnary) :
    ComputableInPolyTime (fun z => modeValueList (p z) (fl z) (i z) (differ z) (cols z) (y₀ z)
      (b z)) encIn (encList encNat) := by
  have h1 := ComputableInPolyTime.fst encIn (encPair encNat encBool)
  have h2 := ComputableInPolyTime.snd encIn (encPair encNat encBool)
  have hc := (ComputableInPolyTime.fst encNat encBool).comp h2
  have hbit := (ComputableInPolyTime.snd encNat encBool).comp h2
  have hT := ComputableInPolyTime.binary_two_pow.comp
    (ComputableInPolyTime.unary_add' (hi.comp h1) (ComputableInPolyTime.const 1))
  have hzero := computableInPolyTime_tabulate (g := fun _ _ => 0)
    ((ComputableInPolyTime.length_list encNat).comp (hfl.comp h1)) (ComputableInPolyTime.const 0)
  have hpow := computableInPolyTime_pow (hp.comp h1) (hfl.comp h1)
    (intConst_natCast_polyTime (hp.comp h1) (hfl.comp h1)
      (ComputableInPolyTime.binary_div.comp (hc.prod hT))) (hb.comp h1)
  have hf : ComputableInPolyTime (fun q : α × (ℕ × Bool) =>
      if q.2.2 = true ∧ differ q.1 = true ∧ q.2.1 % 2 ^ (i q.1 + 1) = y₀ q.1 then
        pow (p q.1) (fl q.1) (intConst (p q.1) (fl q.1) ((q.2.1 / 2 ^ (i q.1 + 1) : ℕ) : ℤ)) (b q.1)
      else zero (fl q.1)) (encPair encIn (encPair encNat encBool)) (encList encNat) := by
    refine (ComputableInPolyTime.ite hbit (ComputableInPolyTime.ite (hdiffer.comp h1)
      (ComputableInPolyTime.ite (ComputableInPolyTime.beq
        (ComputableInPolyTime.binary_mod.comp (hc.prod hT)) (hy₀.comp h1)) hpow hzero) hzero)
      hzero).of_enc_eq fun q => ?_
    cases hq : q.2.2 <;> cases hd : differ q.1 <;>
      by_cases hm : q.2.1 % 2 ^ (i q.1 + 1) = y₀ q.1 <;> simp [hq, hd, hm, GaloisRingArith.zero]
  exact sumList_polyTime hp hfl (ComputableInPolyTime.mapWithInput
    (f := fun z c => if c.2 = true ∧ differ z = true ∧ c.1 % 2 ^ (i z + 1) = y₀ z then
      pow (p z) (fl z) (intConst (p z) (fl z) ((c.1 / 2 ^ (i z + 1) : ℕ) : ℤ)) (b z)
    else zero (fl z)) hcols hf)

/-- **Row terms are polynomial-time**, with `nb` in unary and the mode index in binary. -/
theorem rowTermList_polyTime {p : α → ℕ} {fl : α → List ℕ} {a L i nb : α → ℕ} {t : α → ℤ}
    {differ : α → Bool} {cols : α → List (ℕ × Bool)} {ζ : α → List ℕ} {r : α → ℕ × Bool}
    {o : α → Option ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary) (hL : ComputableInPolyTime L encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary) (ht : ComputableInPolyTime t encIn encIntBin)
    (hnb : ComputableInPolyTime nb encIn encUnary)
    (hdiffer : ComputableInPolyTime differ encIn encBool)
    (hcols : ComputableInPolyTime cols encIn (encList (encPair encNat encBool)))
    (hζ : ComputableInPolyTime ζ encIn (encList encNat))
    (hr : ComputableInPolyTime r encIn (encPair encNat encBool))
    (ho : ComputableInPolyTime o encIn (encOption encNat)) :
    ComputableInPolyTime (fun z => rowTermList (p z) (fl z) (a z) (L z) (i z) (t z) (nb z)
      (differ z) (cols z) (ζ z) (r z) (o z)) encIn (encList encNat) := by
  have hx := (ComputableInPolyTime.fst encNat encBool).comp hr
  have hbit := (ComputableInPolyTime.snd encNat encBool).comp hr
  have hloc := localFormList_polyTime hp hfl ha hL ht hcols hx hζ
  have h1 := ComputableInPolyTime.fst encIn encNat
  have hk := ComputableInPolyTime.snd encIn encNat
  have hnb' := ComputableInPolyTime.unary_to_binary.comp (hnb.comp h1)
  have hy := ComputableInPolyTime.binary_div.comp (hk.prod hnb')
  have hexp := ComputableInPolyTime.binary_min_unary' (hnb.comp h1)
    (ComputableInPolyTime.binary_mod.comp (hk.prod hnb'))
  have hcoef := modeCoeffList_polyTime (hp.comp h1) (hfl.comp h1) (ha.comp h1) (hL.comp h1)
    (hi.comp h1) (ht.comp h1) (hdiffer.comp h1) (hx.comp h1) hy hexp (hζ.comp h1)
  have hzero := computableInPolyTime_tabulate (g := fun _ _ => 0)
    ((ComputableInPolyTime.length_list encNat).comp (hfl.comp h1)) (ComputableInPolyTime.const 0)
  unfold rowTermList
  option_match_to_elim
  refine ComputableInPolyTime.optionElimWithInput ho (ComputableInPolyTime.ite hbit hloc
    (computableInPolyTime_sub hp hfl (computableInPolyTime_one hfl) hloc))
    ((ComputableInPolyTime.ite (ComputableInPolyTime.beq (hnb.comp h1)
      (ComputableInPolyTime.const 0)) hzero (ComputableInPolyTime.ite (hbit.comp h1) hcoef
        (computableInPolyTime_neg (hp.comp h1) (hfl.comp h1) hcoef))).of_enc_eq fun q => ?_)
  by_cases h0 : nb q.1 = 0
  · simp [h0, GaloisRingArith.zero]
  · have hmin : min (nb q.1) (q.2 % nb q.1) = q.2 % nb q.1 :=
      min_eq_right (Nat.mod_lt _ (Nat.pos_of_ne_zero h0)).le
    simp only [h0, beq_iff_eq, ↓reduceIte, Function.comp_apply, hmin]

end PolyTime


/-! ### Coefficient extraction for a packet -/

/-- **The context of a packet entry**: the precision `p` and the coefficients `fl` of `f`, the
bit counts `a` and `i`, the number of slots `L = 2 ^ a` and of tiles `tiles = 2 ^ (i + 1)`, the
grid point `t`, the number `nb` of exponents per tile, whether the two symbols of the packet are
the group (`e₁`, `e₂`) and whether they differ, the column ports, and `ζ`. -/
structure PacketCtx where
  /-- The precision. -/
  p : ℕ
  /-- The coefficients of `f` below the leading one. -/
  fl : List ℕ
  /-- The number of slot bits. -/
  a : ℕ
  /-- The number of slots, `2 ^ a`. -/
  L : ℕ
  /-- The digit of the tiles. -/
  i : ℕ
  /-- The number of tiles, `2 ^ (i + 1)`. -/
  tiles : ℕ
  /-- The grid point. -/
  t : ℤ
  /-- The number of exponents per tile. -/
  nb : ℕ
  /-- Whether the first symbol is the group. -/
  e₁ : Bool
  /-- Whether the second symbol is the group. -/
  e₂ : Bool
  /-- Whether the two symbols differ. -/
  differ : Bool
  /-- The column ports: slots and bits. -/
  cols : List (ℕ × Bool)
  /-- The interpolation value. -/
  ζ : List ℕ
  deriving Inhabited

namespace PacketCtx

/-- A packet context as nested pairs. -/
def equivProd : PacketCtx ≃ (ℕ × List ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℤ × (ℕ ×
    ((Bool × Bool × Bool) × (List (ℕ × Bool) × List ℕ)))))) where
  toFun c := ((c.p, c.fl), ((c.a, c.L), ((c.i, c.tiles), (c.t, (c.nb,
    ((c.e₁, c.e₂, c.differ), (c.cols, c.ζ)))))))
  invFun q := ⟨q.1.1, q.1.2, q.2.1.1, q.2.1.2, q.2.2.1.1, q.2.2.1.2, q.2.2.2.1, q.2.2.2.2.1,
    q.2.2.2.2.2.1.1, q.2.2.2.2.2.1.2.1, q.2.2.2.2.2.1.2.2, q.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The encoding of the nested pairs of a packet context. -/
abbrev encProd : (ℕ × List ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℤ × (ℕ ×
    ((Bool × Bool × Bool) × (List (ℕ × Bool) × List ℕ)))))) ↪ List Bool :=
  encPair (encPair encUnary (encList encNat))
    (encPair (encPair encUnary encUnary) (encPair (encPair encUnary encUnary)
      (encPair encIntBin (encPair encUnary (encPair (encPair encBool (encPair encBool encBool))
        (encPair (encList (encPair encNat encBool)) (encList encNat)))))))

/-- **The encoding of a packet context**: the counts in unary, `t` in binary sign-magnitude
form, and the lists in binary. -/
def enc : PacketCtx ↪ List Bool := encOfEquiv equivProd encProd

/-- Construct a packet context from polynomial-time fields, using its existing encoding:
counts are unary, the grid point is in binary sign-magnitude form, and list entries are binary. -/
@[fun_prop]
theorem mk_polyTime {δ : Type} {encIn : δ ↪ List Bool}
    {p a L i tiles nb : δ → ℕ} {fl ζ : δ → List ℕ} {t : δ → ℤ}
    {e₁ e₂ differ : δ → Bool} {cols : δ → List (ℕ × Bool)}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary)
    (hL : ComputableInPolyTime L encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (htiles : ComputableInPolyTime tiles encIn encUnary)
    (ht : ComputableInPolyTime t encIn encIntBin)
    (hnb : ComputableInPolyTime nb encIn encUnary)
    (he₁ : ComputableInPolyTime e₁ encIn encBool)
    (he₂ : ComputableInPolyTime e₂ encIn encBool)
    (hdiffer : ComputableInPolyTime differ encIn encBool)
    (hcols : ComputableInPolyTime cols encIn (encList (encPair encNat encBool)))
    (hζ : ComputableInPolyTime ζ encIn (encList encNat)) :
    ComputableInPolyTime (fun x => PacketCtx.mk (p x) (fl x) (a x) (L x) (i x) (tiles x)
      (t x) (nb x) (e₁ x) (e₂ x) (differ x) (cols x) (ζ x)) encIn enc :=
  ((hp.prod hfl).prod ((ha.prod hL).prod ((hi.prod htiles).prod (ht.prod
    (hnb.prod ((he₁.prod (he₂.prod hdiffer)).prod (hcols.prod hζ))))))).of_enc_eq fun _ => rfl

private theorem toProd_polyTime : ComputableInPolyTime equivProd enc encProd :=
  ComputableInPolyTime.of_eq fun _ => rfl

private theorem rest_polyTime :
    ComputableInPolyTime (fun c : PacketCtx => (equivProd c).2.2.2.2.2) enc
      (encPair (encPair encBool (encPair encBool encBool))
        (encPair (encList (encPair encNat encBool)) (encList encNat))) :=
  (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp
    ((ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.snd _ _).comp toProd_polyTime))))

/-- The precision, in polynomial time. -/
theorem p_polyTime : ComputableInPolyTime PacketCtx.p enc encUnary :=
  (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.fst _ _).comp toProd_polyTime)
/-- The coefficients of `f`, in polynomial time. -/
theorem fl_polyTime : ComputableInPolyTime PacketCtx.fl enc (encList encNat) :=
  (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.fst _ _).comp toProd_polyTime)
/-- The number of slot bits, in polynomial time. -/
theorem a_polyTime : ComputableInPolyTime PacketCtx.a enc encUnary :=
  (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.fst _ _).comp
    ((ComputableInPolyTime.snd _ _).comp toProd_polyTime))
/-- The number of slots, in polynomial time. -/
theorem L_polyTime : ComputableInPolyTime PacketCtx.L enc encUnary :=
  (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.fst _ _).comp
    ((ComputableInPolyTime.snd _ _).comp toProd_polyTime))
/-- The digit of the tiles, in polynomial time. -/
theorem i_polyTime : ComputableInPolyTime PacketCtx.i enc encUnary :=
  (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.fst _ _).comp
    ((ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp toProd_polyTime)))
/-- The number of tiles, in polynomial time. -/
theorem tiles_polyTime : ComputableInPolyTime PacketCtx.tiles enc encUnary :=
  (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.fst _ _).comp
    ((ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp toProd_polyTime)))
/-- The grid point, in polynomial time. -/
theorem t_polyTime : ComputableInPolyTime PacketCtx.t enc encIntBin :=
  (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd _ _).comp
    ((ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp toProd_polyTime)))
/-- The number of exponents per tile, in polynomial time. -/
theorem nb_polyTime : ComputableInPolyTime PacketCtx.nb enc encUnary :=
  (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd _ _).comp
    ((ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.snd _ _).comp toProd_polyTime))))
/-- Whether the first symbol is the group, in polynomial time. -/
theorem e₁_polyTime : ComputableInPolyTime PacketCtx.e₁ enc encBool :=
  (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.fst _ _).comp rest_polyTime)
/-- Whether the second symbol is the group, in polynomial time. -/
theorem e₂_polyTime : ComputableInPolyTime PacketCtx.e₂ enc encBool :=
  (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd _ _).comp
    ((ComputableInPolyTime.fst _ _).comp rest_polyTime))
/-- Whether the symbols differ, in polynomial time. -/
theorem differ_polyTime : ComputableInPolyTime PacketCtx.differ enc encBool :=
  (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp
    ((ComputableInPolyTime.fst _ _).comp rest_polyTime))
/-- The column ports, in polynomial time. -/
theorem cols_polyTime : ComputableInPolyTime PacketCtx.cols enc
    (encList (encPair encNat encBool)) :=
  (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd _ _).comp rest_polyTime)
/-- The interpolation value, in polynomial time. -/
theorem ζ_polyTime : ComputableInPolyTime PacketCtx.ζ enc (encList encNat) :=
  (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp rest_polyTime)

end PacketCtx

/-- The dense indices of the modes of a packet whose tiles target the group. -/
def targetModes (c : PacketCtx) : List ℕ :=
  (List.range (c.tiles * c.nb)).filter fun k => modeTargets c.i c.e₁ c.e₂ (k / c.nb)

/-- **Coefficient extraction for a packet**: the precision, the target modes and the row
terms. -/
def packetTerms : CoeffScheme.Terms PacketCtx (ℕ × Bool) where
  prec c := (c.p, c.fl)
  modes := targetModes
  term c r o := rowTermList c.p c.fl c.a c.L c.i c.t c.nb c.differ c.cols c.ζ r o

/-- **The data of coefficient extraction for a packet are polynomial-time.** -/
theorem packetTerms_polyTime : packetTerms.PolyTime PacketCtx.enc (encPair encNat encBool) where
  prec := PacketCtx.p_polyTime.prod PacketCtx.fl_polyTime
  modes := by
    have hrange : ComputableInPolyTime (fun c : PacketCtx => List.range (c.tiles * c.nb))
        PacketCtx.enc (encList encNat) :=
      (ComputableInPolyTime.mapWithInput (f := fun _ (k : ℕ) => k)
        (ComputableInPolyTime.range.comp (ComputableInPolyTime.unary_mul'
          PacketCtx.tiles_polyTime PacketCtx.nb_polyTime))
        (ComputableInPolyTime.unary_to_binary.comp
          (ComputableInPolyTime.snd PacketCtx.enc encUnary))).of_enc_eq fun c => by
        simp
    have h1 := ComputableInPolyTime.fst PacketCtx.enc encNat
    have h2 := ComputableInPolyTime.snd PacketCtx.enc encNat
    have hy := ComputableInPolyTime.binary_div.comp
      (h2.prod (ComputableInPolyTime.unary_to_binary.comp (PacketCtx.nb_polyTime.comp h1)))
    have htest : ComputableInPolyTime (fun q : PacketCtx × ℕ =>
        modeTargets q.1.i q.1.e₁ q.1.e₂ (q.2 / q.1.nb)) (encPair PacketCtx.enc encNat)
        encBool :=
      ComputableInPolyTime.ite (ComputableInPolyTime.binary_testBit hy
        (PacketCtx.i_polyTime.comp h1)) (PacketCtx.e₂_polyTime.comp h1)
        (PacketCtx.e₁_polyTime.comp h1)
    exact ComputableInPolyTime.filterWithInput hrange htest
  term := by
    let E := encPair PacketCtx.enc (encPair (encPair encNat encBool) (encOption encNat))
    have hc := ComputableInPolyTime.fst PacketCtx.enc
      (encPair (encPair encNat encBool) (encOption encNat))
    have hr := (ComputableInPolyTime.fst (encPair encNat encBool) (encOption encNat)).comp
      (ComputableInPolyTime.snd PacketCtx.enc (encPair (encPair encNat encBool)
        (encOption encNat)))
    have ho := (ComputableInPolyTime.snd (encPair encNat encBool) (encOption encNat)).comp
      (ComputableInPolyTime.snd PacketCtx.enc (encPair (encPair encNat encBool)
        (encOption encNat)))
    exact rowTermList_polyTime (PacketCtx.p_polyTime.comp hc) (PacketCtx.fl_polyTime.comp hc)
      (PacketCtx.a_polyTime.comp hc) (PacketCtx.L_polyTime.comp hc)
      (PacketCtx.i_polyTime.comp hc) (PacketCtx.t_polyTime.comp hc)
      (PacketCtx.nb_polyTime.comp hc) (PacketCtx.differ_polyTime.comp hc)
      (PacketCtx.cols_polyTime.comp hc) (PacketCtx.ζ_polyTime.comp hc) hr ho

/-- **Coefficient extraction for a packet is correct**: with `tiles = 2 ^ (i + 1)`, the value of
the recursion in `A_p` is that of the coefficient extraction of `packetEntryList`. -/
theorem val_packetTerms_value (c : PacketCtx) (htiles : c.tiles = 2 ^ (c.i + 1))
    (rows : List (ℕ × Bool)) (γ : List ℕ) :
    val c.p c.fl (packetTerms.value c rows γ) =
      val c.p c.fl (listCoeffList c.p c.fl ((List.range (2 ^ (c.i + 1) * c.nb)).filter fun k =>
          modeTargets c.i c.e₁ c.e₂ (k / c.nb))
        (rows.map (rowTermList c.p c.fl c.a c.L c.i c.t c.nb c.differ c.cols c.ζ))
        (fun k => γ.getD k 0)) := by
  rw [val_listCoeffList (List.nodup_range.filter _), List.map_map]
  have h := packetTerms.val_value c ((List.nodup_range).filter _) rows γ
  simp only [packetTerms, targetModes, htiles] at h
  exact h


/-! ### Packet entries natively -/

/-- The dense indices of the modes of a packet whose tiles have the group as source. -/
def sourceModes (c : PacketCtx) : List ℕ :=
  (List.range (c.tiles * c.nb)).filter fun k => modeSources c.i c.e₁ c.e₂ (k / c.nb)

/-- The product of the powers of the values of the source modes, at the exponents of a dense
list. -/
def sourceProduct (c : PacketCtx) (β : List ℕ) : List ℕ :=
  prodList c.p c.fl ((sourceModes c).map fun k =>
    pow c.p c.fl (modeValueList c.p c.fl c.i c.differ c.cols (k / c.nb) (k % c.nb)) (β.getD k 0))

/-- **A packet entry, natively**: coefficient extraction by the stack recursion, at the
exponents of the dense list `β`, times the product of the powers of the source mode values. -/
def packetEntryNative (c : PacketCtx) (rows : List (ℕ × Bool)) (β : List ℕ) : List ℕ :=
  mul c.p c.fl (packetTerms.value c rows β) (sourceProduct c β)

/-- **The native packet entry is `packetEntryList`** in `A_p`, when `tiles = 2 ^ (i + 1)`. -/
theorem val_packetEntryNative (c : PacketCtx) (htiles : c.tiles = 2 ^ (c.i + 1))
    (rows : List (ℕ × Bool)) (β : List ℕ) :
    val c.p c.fl (packetEntryNative c rows β) =
      val c.p c.fl (packetEntryList c.p c.fl c.a c.L c.i c.t c.nb c.e₁ c.e₂ c.differ
        (fun k => β.getD k 0) rows c.cols c.ζ) := by
  rw [packetEntryNative, packetEntryList, val_mul, val_mul, val_packetTerms_value c htiles,
    sourceProduct, sourceModes, htiles]

/-- **The native packet entry is the packet entry** (§D.4.6, p. 63): for a grid point `t` of
valuation `i < a`, `L = 2 ^ a`, `tiles = 2 ^ (i + 1)` and ports in slots below `L`, its value in
`A_p` is `packetEntry` at the reduction of `ℤ_(2)`, the value of `ζ`, and the exponents of `β`
at the dense indices of the modes. -/
theorem val_packetEntryNative_eq (c : PacketCtx) (hL : c.L = 2 ^ c.a) (hia : c.i < c.a)
    (htiles : c.tiles = 2 ^ (c.i + 1)) (ht : c.t ∈ cauchyGrid (2 ^ c.a))
    (hti : (2 : ℤ) ^ c.i ∣ c.t) (hti' : ¬ (2 : ℤ) ^ (c.i + 1) ∣ c.t)
    {rows : List (ℕ × Bool)} (hrows : ∀ r ∈ rows, r.1 < 2 ^ c.a)
    (hcols : ∀ r ∈ c.cols, r.1 < 2 ^ c.a) (β : List ℕ) :
    val c.p c.fl (packetEntryNative c rows β) =
      packetEntry (p := c.nb) (scalarHom c.p c.fl) (val c.p c.fl c.ζ) c.a c.i c.t c.e₁ c.e₂
        c.differ (fun Z => β.getD (finProdFinEquiv Z) 0) rows c.cols := by
  rw [val_packetEntryNative c htiles, val_packetEntryList hL hia ht hti hti' c.nb c.e₁ c.e₂
    c.differ _ hrows hcols]

/-- **The native packet entry in every ring receiving `A_p`.** Along a ring map `ψ : A_p → S`
with `2` nilpotent in `S`, the value of the native entry is `packetEntry` over `S` at any ring
map `κ : ℤ_(2) → S` and at the image of `ζ`; with `child_tensor_inr_cauchyModeSplitting`, it is
the entry of a packet vertex of a child network over `S`. -/
theorem map_val_packetEntryNative {S : Type*} [CommRing S] (c : PacketCtx)
    (ψ : Ring c.p c.fl →+* S) {n : ℕ} (hn : (2 : S) ^ n = 0) (κ : ℤ₍₂₎ →+* S)
    (hL : c.L = 2 ^ c.a) (hia : c.i < c.a) (htiles : c.tiles = 2 ^ (c.i + 1))
    (ht : c.t ∈ cauchyGrid (2 ^ c.a)) (hti : (2 : ℤ) ^ c.i ∣ c.t)
    (hti' : ¬ (2 : ℤ) ^ (c.i + 1) ∣ c.t) {rows : List (ℕ × Bool)}
    (hrows : ∀ r ∈ rows, r.1 < 2 ^ c.a) (hcols : ∀ r ∈ c.cols, r.1 < 2 ^ c.a) (β : List ℕ) :
    ψ (val c.p c.fl (packetEntryNative c rows β)) =
      packetEntry (p := c.nb) κ (ψ (val c.p c.fl c.ζ)) c.a c.i c.t c.e₁ c.e₂ c.differ
        (fun Z => β.getD (finProdFinEquiv Z) 0) rows c.cols := by
  rw [val_packetEntryNative c htiles, map_val_packetEntryList ψ hn κ hL hia ht hti hti' c.nb
    c.e₁ c.e₂ c.differ _ hrows hcols]

section Certificate

/-- The input of the native packet evaluator: a context, the row ports and the dense exponents,
the exponents in unary. -/
abbrev encEntryInput : PacketCtx × (List (ℕ × Bool) × List ℕ) ↪ List Bool :=
  encPair PacketCtx.enc (encPair (encList (encPair encNat encBool)) (encList encUnary))

/-- The root of coefficient extraction, with the exponents re-encoded in binary. -/
theorem node_polyTime :
    ComputableInPolyTime (fun q : PacketCtx × (List (ℕ × Bool) × List ℕ) => q)
      encEntryInput (CoeffScheme.Terms.encNode PacketCtx.enc (encPair encNat encBool)) := by
  have hβ := (ComputableInPolyTime.snd (encList (encPair encNat encBool)) (encList encUnary)).comp
    (ComputableInPolyTime.snd PacketCtx.enc
      (encPair (encList (encPair encNat encBool)) (encList encUnary)))
  have hβ' : ComputableInPolyTime (fun q : PacketCtx × (List (ℕ × Bool) × List ℕ) => q.2.2)
      encEntryInput (encList encNat) :=
    (ComputableInPolyTime.mapWithInput (f := fun _ (k : ℕ) => k) hβ
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _))).of_enc_eq
      fun q => by simp
  exact (ComputableInPolyTime.fst _ _).prod
    (((ComputableInPolyTime.fst (encList (encPair encNat encBool)) (encList encUnary)).comp
      (ComputableInPolyTime.snd _ _)).prod hβ')

/-- The source product is polynomial-time, with the exponents in unary. -/
theorem sourceProduct_polyTime :
    ComputableInPolyTime (fun q : PacketCtx × (List (ℕ × Bool) × List ℕ) =>
      sourceProduct q.1 q.2.2) encEntryInput (encList encNat) := by
  have hc := ComputableInPolyTime.fst PacketCtx.enc
    (encPair (encList (encPair encNat encBool)) (encList encUnary))
  have hβ := (ComputableInPolyTime.snd (encList (encPair encNat encBool)) (encList encUnary)).comp
    (ComputableInPolyTime.snd PacketCtx.enc
      (encPair (encList (encPair encNat encBool)) (encList encUnary)))
  have hp := PacketCtx.p_polyTime.comp hc
  have hfl := PacketCtx.fl_polyTime.comp hc
  have hrange : ComputableInPolyTime (fun q : PacketCtx × (List (ℕ × Bool) × List ℕ) =>
      List.range (q.1.tiles * q.1.nb)) encEntryInput (encList encNat) :=
    (ComputableInPolyTime.mapWithInput (f := fun _ (k : ℕ) => k)
      (ComputableInPolyTime.range.comp (ComputableInPolyTime.unary_mul'
        (PacketCtx.tiles_polyTime.comp hc) (PacketCtx.nb_polyTime.comp hc)))
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _))).of_enc_eq
      fun q => by simp
  have h1 := ComputableInPolyTime.fst encEntryInput encNat
  have h2 := ComputableInPolyTime.snd encEntryInput encNat
  have hnb := ComputableInPolyTime.unary_to_binary.comp (PacketCtx.nb_polyTime.comp (hc.comp h1))
  have hy := ComputableInPolyTime.binary_div.comp (h2.prod hnb)
  have htest : ComputableInPolyTime (fun z : (PacketCtx × (List (ℕ × Bool) × List ℕ)) × ℕ =>
      modeSources z.1.1.i z.1.1.e₁ z.1.1.e₂ (z.2 / z.1.1.nb)) (encPair encEntryInput encNat)
      encBool :=
    ComputableInPolyTime.ite (ComputableInPolyTime.binary_testBit hy
      (PacketCtx.i_polyTime.comp (hc.comp h1))) (PacketCtx.e₁_polyTime.comp (hc.comp h1))
      (PacketCtx.e₂_polyTime.comp (hc.comp h1))
  have hmodes := ComputableInPolyTime.filterWithInput
    (test := fun q k => modeSources q.1.i q.1.e₁ q.1.e₂ (k / q.1.nb)) hrange htest
  have hexp := ComputableInPolyTime.binary_min_unary'
    (ComputableInPolyTime.unary_add' (PacketCtx.nb_polyTime.comp (hc.comp h1))
      (ComputableInPolyTime.const 1))
    (ComputableInPolyTime.binary_mod.comp (h2.prod hnb))
  have hval := modeValueList_polyTime (hp.comp h1) (hfl.comp h1)
    (PacketCtx.i_polyTime.comp (hc.comp h1)) (PacketCtx.differ_polyTime.comp (hc.comp h1))
    (PacketCtx.cols_polyTime.comp (hc.comp h1)) hy hexp
  have hβk : ComputableInPolyTime (fun z : (PacketCtx × (List (ℕ × Bool) × List ℕ)) × ℕ =>
      z.1.2.2.getD z.2 0) (encPair encEntryInput encNat) encUnary :=
    ComputableInPolyTime.listGetD_binary (encA := encUnary) 0 (hβ.comp h1) h2
  have hlist := ComputableInPolyTime.mapWithInput
    (f := fun q k => pow q.1.p q.1.fl (modeValueList q.1.p q.1.fl q.1.i q.1.differ q.1.cols
      (k / q.1.nb) (min (q.1.nb + 1) (k % q.1.nb))) (q.2.2.getD k 0)) hmodes
    (computableInPolyTime_pow (hp.comp h1) (hfl.comp h1) hval hβk)
  refine (prodList_polyTime hp hfl hlist).of_enc_eq fun q => ?_
  simp only [sourceProduct, sourceModes]
  congr 2
  refine List.map_congr_left fun k hk => ?_
  have hk' := List.mem_range.mp (List.mem_filter.mp hk).1
  have hnb0 : 0 < q.1.nb := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hk'
  rw [min_eq_right ((Nat.mod_lt _ hnb0).le.trans (Nat.le_succ _))]

/-- The final product of the native packet evaluator is polynomial-time. -/
theorem mulFinal_polyTime :
    ComputableInPolyTime (fun z : (PacketCtx × (List (ℕ × Bool) × List ℕ)) × (List ℕ × List ℕ) =>
      mul z.1.1.p z.1.1.fl z.2.1 z.2.2)
      (encPair encEntryInput (encPair (encList encNat) (encList encNat))) (encList encNat) := by
  have hc := (ComputableInPolyTime.fst PacketCtx.enc
    (encPair (encList (encPair encNat encBool)) (encList encUnary))).comp
    (ComputableInPolyTime.fst encEntryInput (encPair (encList encNat) (encList encNat)))
  have hy := ComputableInPolyTime.snd encEntryInput (encPair (encList encNat) (encList encNat))
  exact computableInPolyTime_mul (PacketCtx.p_polyTime.comp hc) (PacketCtx.fl_polyTime.comp hc)
    ((ComputableInPolyTime.fst _ _).comp hy) ((ComputableInPolyTime.snd _ _).comp hy)

/-- **The native packet evaluator**: one native machine for `packetEntryNative` on every
context, row ports and dense exponents (in unary). Its time is that of the stack recursion of
coefficient extraction (`CoeffScheme.Terms.valueCertificate_le`, `exp(O(L log m))` times a
polynomial), plus polynomial time. -/
noncomputable def entryCertificate :
    NativeCertificate (fun q : PacketCtx × (List (ℕ × Bool) × List ℕ) =>
      packetEntryNative q.1 q.2.1 q.2.2) encEntryInput (encList encNat) :=
  ((NativeCertificate.ofPolyTime mulFinal_polyTime).comp
    ((NativeCertificate.ofPolyTime ComputableInPolyTime.id').prod
      (((CoeffScheme.Terms.valueCertificate packetTerms_polyTime).comp
        (NativeCertificate.ofPolyTime node_polyTime)).prod
        (NativeCertificate.ofPolyTime sourceProduct_polyTime)))).congr fun _ => rfl


/-- The value of coefficient extraction is reduced. -/
theorem reduced_value {C Rw : Type} (S : CoeffScheme.Terms C Rw) (x : C) (rows : List Rw)
    (γ : List ℕ) : SumOps.galois.Reduced (S.prec x) (S.value x rows γ) := by
  cases rows with
  | nil => exact S.reduced_leafValue x γ
  | cons r rs =>
    exact SumOps.galois.reduced_foldl (S.prec x) _ (SumOps.galois.reduced_add (S.prec x)) _ _
      (SumOps.galois.reduced_zero (S.prec x))

/-- The source product is reduced. -/
theorem reduced_sourceProduct (c : PacketCtx) (β : List ℕ) :
    SumOps.galois.Reduced (c.p, c.fl) (sourceProduct c β) :=
  SumOps.galois.reduced_foldl (c.p, c.fl) _ (SumOps.galois.reduced_mul (c.p, c.fl)) id _
    (SumOps.galois.reduced_one (c.p, c.fl))

/-- **The resources of the native packet evaluator.** There is `K` such that on an input of
length `n` with `m` target modes and `L` row ports, if the reduced coefficient lists of its
precision are at most `Rv` bits long, then with `Z = n + m + Rv + 2` the time is at most
`K (m + 2) ^ L Z ^ K` and the space at most `K Z ^ K`: the `exp(O(L log s))` time and polynomial
space of §D.4.6 (p. 63). -/
theorem entryCertificate_le :
    ∃ K : ℕ, ∀ (q : PacketCtx × (List (ℕ × Bool) × List ℕ)) (Rv : ℕ),
      (∀ y, SumOps.galois.Reduced (q.1.p, q.1.fl) y → (encList encNat y).length ≤ Rv) →
      entryCertificate.time q ≤ K * ((targetModes q.1).length + 2) ^ q.2.1.length *
          ((encEntryInput q).length + (targetModes q.1).length + Rv + 2) ^ K ∧
        entryCertificate.space q ≤
          K * ((encEntryInput q).length + (targetModes q.1).length + Rv + 2) ^ K := by
  let cI := NativeCertificate.ofPolyTime (ComputableInPolyTime.id' (encIn := encEntryInput))
  let cN := NativeCertificate.ofPolyTime node_polyTime
  let cP := NativeCertificate.ofPolyTime sourceProduct_polyTime
  let cM := NativeCertificate.ofPolyTime mulFinal_polyTime
  let encMul := encPair encEntryInput (encPair (encList encNat) (encList encNat))
  let overhead (z : (PacketCtx × (List (ℕ × Bool) × List ℕ)) × (List ℕ × List ℕ)) :=
    cI.time z.1 + cI.space z.1 + (cN.time z.1 + cN.space z.1) +
      (cP.time z.1 + cP.space z.1) + (cM.time z + cM.space z)
  have hq := (ComputableInPolyTime.fst encEntryInput
    (encPair (encList encNat) (encList encNat))).polyBounded_length
  have hI := NativeCertificate.ofPolyTime_isPolynomial
    (ComputableInPolyTime.id' (encIn := encEntryInput))
  have hN := NativeCertificate.ofPolyTime_isPolynomial node_polyTime
  have hP := NativeCertificate.ofPolyTime_isPolynomial sourceProduct_polyTime
  have hM := NativeCertificate.ofPolyTime_isPolynomial mulFinal_polyTime
  have hover : PolyBounded (fun z => (encMul z).length) overhead :=
    ((((hI.1.add hI.2).comp hq).add ((hN.1.add hN.2).comp hq)).add
      ((hP.1.add hP.2).comp hq)).add (hM.1.add hM.2)
  obtain ⟨c, d, hover⟩ := hover.exists_le
  obtain ⟨K₁, hK₁⟩ := CoeffScheme.Terms.valueCertificate_le packetTerms_polyTime
  have hpoly : PolyBounded id (fun Z : ℕ => c * (8 * Z) ^ d + K₁ * Z ^ K₁) :=
    ((PolyBounded.const c).mul (((PolyBounded.const 8).mul .self).pow d)).add
      ((PolyBounded.const K₁).mul (PolyBounded.self.pow K₁))
  obtain ⟨K, hK⟩ := hpoly.exists_le_self_pow
  refine ⟨K, fun q Rv hRv => ?_⟩
  let Z := (encEntryInput q).length + (targetModes q.1).length + Rv + 2
  let E := ((targetModes q.1).length + 2) ^ q.2.1.length
  let z := (q, (packetTerms.value q.1 q.2.1 q.2.2, sourceProduct q.1 q.2.2))
  have hE : 1 ≤ E := Nat.one_le_pow _ _ (by omega)
  have hnode : (CoeffScheme.Terms.encNode PacketCtx.enc (encPair encNat encBool) q).length ≤
      (encEntryInput q).length := by
    obtain ⟨ctx, rows, β⟩ := q
    have hβ : (encList encNat β).length ≤ (encList encUnary β).length := by
      simp only [length_encList]
      refine List.sum_le_sum fun k _ => ?_
      have : (encNat k).length ≤ k := by
        change k.bits.length ≤ k
        rw [Nat.size_eq_bits_len]
        exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans le_rfl
      enc_len
    enc_len
  have hred1 := hRv _ (reduced_value packetTerms q.1 q.2.1 q.2.2)
  have hred2 := hRv _ (reduced_sourceProduct q.1 q.2.2)
  have hmul : (encMul z).length + 1 ≤ 8 * Z := by
    have e1 := length_encPair (enc₁ := encEntryInput)
      (enc₂ := encPair (encList encNat) (encList encNat)) z
    have e2 := length_encPair (enc₁ := encList encNat) (enc₂ := encList encNat) z.2
    simp only [encMul, z, packetTerms] at hred1 e1 e2 ⊢
    dsimp only [Z]
    omega
  have ho : overhead z ≤ c * (8 * Z) ^ d :=
    (hover z).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmul _))
  have hv := hK₁ q Rv (by simpa only [packetTerms] using hRv)
  have hz : (CoeffScheme.Terms.encNode PacketCtx.enc (encPair encNat encBool) q).length +
      (targetModes q.1).length + Rv + 2 ≤ Z := by dsimp only [Z]; omega
  have hvt : (CoeffScheme.Terms.valueCertificate packetTerms_polyTime).time q ≤
      E * (K₁ * Z ^ K₁) := by
    calc
      _ ≤ K₁ * E * Z ^ K₁ :=
        hv.1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hz K₁))
      _ = _ := by ring
  have hvs : (CoeffScheme.Terms.valueCertificate packetTerms_polyTime).space q ≤
      K₁ * Z ^ K₁ :=
    hv.2.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hz K₁))
  have htotal := hK Z (by dsimp only [id, Z]; omega)
  change c * (8 * Z) ^ d + K₁ * Z ^ K₁ ≤ K * Z ^ K at htotal
  have ht : entryCertificate.time q ≤ E * (overhead z + K₁ * Z ^ K₁) := by
    have hrest : cI.time q + cN.time q + cP.time q + cM.time z ≤ overhead z := by
      dsimp only [overhead, z]
      omega
    have hscaled := hrest.trans (Nat.le_mul_of_pos_left _ hE)
    change cI.time q + (cN.time q +
      (CoeffScheme.Terms.valueCertificate packetTerms_polyTime).time q + cP.time q) +
      cM.time z ≤ _
    nlinarith
  have hs : entryCertificate.space q ≤ overhead z + K₁ * Z ^ K₁ := by
    have hrest : cI.space q + cN.space q + cP.space q + cM.space z ≤ overhead z := by
      dsimp only [overhead, z]
      omega
    change cI.space q + (cN.space q +
      (CoeffScheme.Terms.valueCertificate packetTerms_polyTime).space q + cP.space q) +
      cM.space z ≤ _
    omega
  constructor
  · exact (ht.trans (Nat.mul_le_mul_left E
      (show overhead z + K₁ * Z ^ K₁ ≤ K * Z ^ K by omega))).trans_eq (by
      dsimp only [E, Z]; ring)
  · change entryCertificate.space q ≤ K * Z ^ K
    exact hs.trans (by omega)

end Certificate

/-! ### Descriptors of packet vertices -/

/-- **The descriptor of a packet vertex**: a packet context, whose column ports are read from
the bits instead, the ports of the vertex in its port order, each `(isRow, slot)`, and the dense
exponents of the modes of the packet. -/
abbrev PacketDesc := PacketCtx × (List (Bool × ℕ) × List ℕ)

/-- The ports of one side, with the bits on them: the slots of the ports with `isRow = side`,
paired with their bits, in port order. -/
def sidePorts (ports : List (Bool × ℕ)) (bs : List Bool) (side : Bool) : List (ℕ × Bool) :=
  ((List.range ports.length).filter fun j => (ports.getD j (false, 0)).1 == side).map fun j =>
    ((ports.getD j (false, 0)).2, bs.getD j false)

/-- **The entry of a packet vertex at the bits on its ports**: the native packet entry, with the
row ports and the column ports read from the bits. -/
def packetVertexEntry (d : PacketDesc) (bs : List Bool) : List ℕ :=
  packetEntryNative { d.1 with cols := sidePorts d.2.1 bs false } (sidePorts d.2.1 bs true) d.2.2

/-- The encoding of a packet descriptor: the context, the ports in binary, and the exponents in
unary. -/
abbrev encPacketDesc : PacketDesc ↪ List Bool :=
  encPair PacketCtx.enc (encPair (encList (encPair encBool encNat)) (encList encUnary))

/-- The ports of one side are polynomial-time. -/
theorem sidePorts_polyTime {α : Type} {encIn : α ↪ List Bool} {ports : α → List (Bool × ℕ)}
    {bs : α → List Bool} {side : α → Bool}
    (hports : ComputableInPolyTime ports encIn (encList (encPair encBool encNat)))
    (hbs : ComputableInPolyTime bs encIn encBits)
    (hside : ComputableInPolyTime side encIn encBool) :
    ComputableInPolyTime (fun x => sidePorts (ports x) (bs x) (side x)) encIn
      (encList (encPair encNat encBool)) := by
  have h1 := ComputableInPolyTime.fst encIn encUnary
  have h2 := ComputableInPolyTime.snd encIn encUnary
  have hport := (ComputableInPolyTime.listGetD (encA := encPair encBool encNat)
    (encL := encList (encPair encBool encNat)) (false, 0)).comp ((hports.comp h1).prod h2)
  have htest := ComputableInPolyTime.beq ((ComputableInPolyTime.fst _ _).comp hport)
    (hside.comp h1)
  have hfilt := ComputableInPolyTime.filterWithInput
    (test := fun x j => ((ports x).getD j (false, 0)).1 == side x)
    (ComputableInPolyTime.range.comp ((ComputableInPolyTime.length_list _).comp hports)) htest
  have hbit := (ComputableInPolyTime.listGetD (encA := encBool) (encL := encBits) false).comp
    ((hbs.comp h1).prod h2)
  exact ComputableInPolyTime.mapWithInput
    (f := fun x j => (((ports x).getD j (false, 0)).2, (bs x).getD j false)) hfilt
    (((ComputableInPolyTime.snd _ _).comp hport).prod hbit)

/-- The input of the native packet evaluator from a descriptor and the bits on its ports. -/
theorem entryInput_polyTime :
    ComputableInPolyTime (fun q : PacketDesc × List Bool =>
      (({ q.1.1 with cols := sidePorts q.1.2.1 q.2 false } : PacketCtx),
        (sidePorts q.1.2.1 q.2 true, q.1.2.2)))
      (encPair encPacketDesc encBits) encEntryInput := by
  have hd := ComputableInPolyTime.fst encPacketDesc encBits
  have hbs := ComputableInPolyTime.snd encPacketDesc encBits
  have hc := (ComputableInPolyTime.fst _ _).comp hd
  have hports := (ComputableInPolyTime.fst (encList (encPair encBool encNat))
    (encList encUnary)).comp ((ComputableInPolyTime.snd _ _).comp hd)
  have hβ := (ComputableInPolyTime.snd (encList (encPair encBool encNat))
    (encList encUnary)).comp ((ComputableInPolyTime.snd _ _).comp hd)
  have hcols := sidePorts_polyTime hports hbs (ComputableInPolyTime.const false)
  have hrows := sidePorts_polyTime hports hbs (ComputableInPolyTime.const true)
  have h01 := (PacketCtx.p_polyTime.comp hc).prod (PacketCtx.fl_polyTime.comp hc)
  have h23 := (PacketCtx.a_polyTime.comp hc).prod (PacketCtx.L_polyTime.comp hc)
  have h45 := (PacketCtx.i_polyTime.comp hc).prod (PacketCtx.tiles_polyTime.comp hc)
  have hsyms := (PacketCtx.e₁_polyTime.comp hc).prod ((PacketCtx.e₂_polyTime.comp hc).prod
    (PacketCtx.differ_polyTime.comp hc))
  have hlast := hcols.prod (PacketCtx.ζ_polyTime.comp hc)
  have htuple := h01.prod (h23.prod (h45.prod ((PacketCtx.t_polyTime.comp hc).prod
    ((PacketCtx.nb_polyTime.comp hc).prod (hsyms.prod hlast)))))
  have hctx : ComputableInPolyTime (fun q : PacketDesc × List Bool =>
      ({ q.1.1 with cols := sidePorts q.1.2.1 q.2 false } : PacketCtx))
      (encPair encPacketDesc encBits) PacketCtx.enc :=
    htuple.of_enc_eq fun _ => rfl
  exact hctx.prod (hrows.prod hβ)

/-- **The native packet evaluator on descriptors**: one native machine for the entry of a packet
vertex at the bits on its ports, the `ev` of the direct summation of
`Cslib.Circuits.Frontier.DescribedNetwork` at coefficient lists (`SumOps.galois`). -/
noncomputable def vertexCertificate :
    NativeCertificate (fun q : PacketDesc × List Bool => packetVertexEntry q.1 q.2)
      (encPair encPacketDesc encBits) (encList encNat) :=
  (entryCertificate.comp (NativeCertificate.ofPolyTime entryInput_polyTime)).congr fun _ => rfl

/-- **The resources of the native packet evaluator on descriptors.** There is `K` such that on a
descriptor and bits of total length `n`, with `m` target modes and `L` row ports, if the reduced
coefficient lists of its precision are at most `Rv` bits long, then with `Z = n + m + Rv + 2` the
time is at most `K (m + 2) ^ L Z ^ K` and the space at most `K Z ^ K`. -/
theorem vertexCertificate_le :
    ∃ K : ℕ, ∀ (q : PacketDesc × List Bool) (Rv : ℕ),
      (∀ y, SumOps.galois.Reduced (q.1.1.p, q.1.1.fl) y → (encList encNat y).length ≤ Rv) →
      vertexCertificate.time q ≤ K * ((targetModes q.1.1).length + 2) ^
          (sidePorts q.1.2.1 q.2 true).length *
          ((encPair encPacketDesc encBits q).length + (targetModes q.1.1).length + Rv + 2) ^ K ∧
        vertexCertificate.space q ≤ K * ((encPair encPacketDesc encBits q).length +
          (targetModes q.1.1).length + Rv + 2) ^ K := by
  obtain ⟨K₀, hK₀⟩ := entryCertificate_le
  let cI := NativeCertificate.ofPolyTime entryInput_polyTime
  let prepare (q : PacketDesc × List Bool) :=
    (({ q.1.1 with cols := sidePorts q.1.2.1 q.2 false } : PacketCtx),
      (sidePorts q.1.2.1 q.2 true, q.1.2.2))
  let size (x : (PacketDesc × List Bool) × (ℕ × ℕ)) :=
    (encPair encPacketDesc encBits x.1).length + x.2.1 + x.2.2 + 2
  let bound (x : (PacketDesc × List Bool) × (ℕ × ℕ)) :=
    cI.time x.1 + cI.space x.1 +
      K₀ * ((encEntryInput (prepare x.1)).length + x.2.1 + x.2.2 + 2) ^ K₀
  have hbase : PolyBounded size (fun x => (encPair encPacketDesc encBits x.1).length) :=
    PolyBounded.self.mono fun x => by dsimp only [size]; omega
  have hm : PolyBounded size (fun x => x.2.1) :=
    PolyBounded.self.mono fun x => by dsimp only [size]; omega
  have hr : PolyBounded size (fun x => x.2.2) :=
    PolyBounded.self.mono fun x => by dsimp only [size]; omega
  have hi := NativeCertificate.ofPolyTime_isPolynomial entryInput_polyTime
  have hlen := entryInput_polyTime.polyBounded_length.comp hbase
  have hb : PolyBounded size bound :=
    ((hi.1.add hi.2).comp hbase).add
      ((PolyBounded.const K₀).mul ((((hlen.add hm).add hr).add (.const 2)).pow K₀))
  obtain ⟨K, hK⟩ := hb.exists_le_self_pow
  refine ⟨K, fun q Rv hRv => ?_⟩
  let x := (q, ((targetModes q.1.1).length, Rv))
  let E := ((targetModes q.1.1).length + 2) ^ (sidePorts q.1.2.1 q.2 true).length
  have hE : 1 ≤ E := Nat.one_le_pow _ _ (by omega)
  have hbound := hK x (by dsimp only [size, x]; omega)
  have hv := hK₀ (prepare q) Rv hRv
  have ht : vertexCertificate.time q ≤ E * bound x := by
    have hscaled : cI.time q ≤ E * (cI.time q + cI.space q) :=
      (Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_left _ hE)
    have hvt : entryCertificate.time (prepare q) ≤
        E * (K₀ * ((encEntryInput (prepare q)).length + (targetModes q.1.1).length + Rv + 2) ^
          K₀) := by
      calc
        _ ≤ K₀ * E * ((encEntryInput (prepare q)).length + (targetModes q.1.1).length + Rv + 2) ^
            K₀ := hv.1
        _ = _ := by ring
    change cI.time q + entryCertificate.time (prepare q) ≤ _
    dsimp only [bound, x]
    nlinarith
  have hs : vertexCertificate.space q ≤ bound x := by
    have hvs : entryCertificate.space (prepare q) ≤
        K₀ * ((encEntryInput (prepare q)).length + (targetModes q.1.1).length + Rv + 2) ^ K₀ :=
      hv.2
    change cI.space q + entryCertificate.space (prepare q) ≤ _
    dsimp only [bound, x]
    omega
  constructor
  · exact (ht.trans (Nat.mul_le_mul_left E hbound)).trans_eq (by
      dsimp only [size, x, E]; ring)
  · exact hs.trans hbound

/-- **The entry of a packet vertex is the packet entry** at the row and column ports read from
its bits. -/
theorem val_packetVertexEntry (d : PacketDesc) (bs : List Bool) (hL : d.1.L = 2 ^ d.1.a)
    (hia : d.1.i < d.1.a) (htiles : d.1.tiles = 2 ^ (d.1.i + 1))
    (ht : d.1.t ∈ cauchyGrid (2 ^ d.1.a)) (hti : (2 : ℤ) ^ d.1.i ∣ d.1.t)
    (hti' : ¬ (2 : ℤ) ^ (d.1.i + 1) ∣ d.1.t) (hports : ∀ x ∈ d.2.1, x.2 < 2 ^ d.1.a) :
    val d.1.p d.1.fl (packetVertexEntry d bs) =
      packetEntry (p := d.1.nb) (scalarHom d.1.p d.1.fl) (val d.1.p d.1.fl d.1.ζ) d.1.a d.1.i
        d.1.t d.1.e₁ d.1.e₂ d.1.differ (fun Z => d.2.2.getD (finProdFinEquiv Z) 0)
        (sidePorts d.2.1 bs true) (sidePorts d.2.1 bs false) := by
  have hside (side : Bool) : ∀ r ∈ sidePorts d.2.1 bs side, r.1 < 2 ^ d.1.a := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    have hj' := List.mem_range.mp (List.mem_filter.mp hj).1
    exact hports _ (by rw [List.getD_eq_getElem _ _ hj']; exact List.getElem_mem _)
  exact val_packetEntryNative_eq { d.1 with cols := sidePorts d.2.1 bs false } hL hia htiles ht
    hti hti' (hside true) (hside false) d.2.2


end NativePacket

end Cslib.Circuits.Frontier
