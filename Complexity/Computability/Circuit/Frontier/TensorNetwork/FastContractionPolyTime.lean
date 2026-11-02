/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionMachine
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.NativeChildPolyTime
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionStep
import Complexity.Computability.PolyTime.BudgetTuples
import Complexity.Computability.PolyTime.GaloisRingArithmetic
import Complexity.Computability.PolyTime.GaloisRingSeries
import Mathlib.Data.List.GetD
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.SqrtLog
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPower
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeRadix

/-!
# The components of the native contraction recursion in polynomial time

The scheme `Cslib.Circuits.Frontier.FastContraction.scheme ev mk` of the contraction recursion of
[OpenAI2026ETH] has polynomial-time components (`Cslib.GenericRAM.StackRecursion.Scheme.PolyTime`)
for the encodings `FastContraction.encCall encT`, `encFrame` and `encValue` whenever the child
builder `mk` is polynomial-time (`FastContraction.scheme_polyTime`), for every type `T` of root
descriptors with an encoding `encT` and every entry procedure `ev`: the leaf test does not
evaluate an entry, and the descriptors are only copied. The native child builder is
(`FastContraction.nativeMk_polyTime`), so the scheme of `FastContraction.nativeMk` has
polynomial-time components (`FastContraction.scheme_nativeMk_polyTime`).

**Every call.** The components compute the data of a call on every call and every frame, not only
on the active calls and the cursor's states. The scale `s`, the depth, the edge bound, the
precision and the number `M` of edges are in unary, so the schedule's quantities are polynomial in
the input:
* `a = slotBits s d ≤ ⌊log₂ s⌋ / 32768`, so `2 ^ a ≤ s + 1`
  (`ContractionSchedule.two_pow_slotBits_le`);
* the multiplicity step `h = ⌈3 M / u⌉` is at most `3 M + u`;
* every level is at most `a + 1` (`FastContraction.level_le`), so a node has at most `4 (s + 1)`
  tiles;
* the native packing has at most `M (2 ^ a) ^ 12` packets
  (`NativeChild.numPackets_nativeParentPacking_le`), which bounds the mode weights and the
  cursor's exponent tuples.

The number of rows and the cursor's exponents are stored in binary, so the packing and the child
builder cap them, at the number of vertices (`FastContraction.rowCap`) and at the node's precision.
The caps change nothing on well-formed active calls (`FastContraction.nativeMk_eq`).

## Main results

* `Cslib.Circuits.Frontier.ContractionSchedule.taper_polyTime`,
  `Cslib.Circuits.Frontier.ContractionSchedule.slotBits_polyTime`,
  `Cslib.Circuits.Frontier.ContractionSchedule.taperStep_polyTime`,
  `Cslib.Circuits.Frontier.ContractionSchedule.leafSize_polyTime`,
  `Cslib.Circuits.Frontier.ContractionSchedule.degreeBound_polyTime`: the schedule.
* `Cslib.Circuits.Frontier.FastContraction.active_polyTime`, `nodePrec_polyTime`,
  `packets_polyTime`, `weights_polyTime`, `points_polyTime`, `table_polyTime`: the data of a call.
* `Cslib.Circuits.Frontier.FastContraction.scheme_polyTime`: the components of the scheme, for a
  polynomial-time child builder.
* `Cslib.Circuits.Frontier.FastContraction.nativeMk_polyTime`,
  `Cslib.Circuits.Frontier.FastContraction.scheme_nativeMk_polyTime`: the native child builder and
  the components of its scheme.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH].
-/

public section

open Turing.MultiTapeTM

namespace Cslib.Circuits.Frontier.ContractionSchedule

/-! ### The schedule -/

/-- `⌊log₂ s⌋` in unary from `s` in unary. -/
private theorem log_polyTime : ComputableInPolyTime (Nat.log 2) encUnary encUnary :=
  ComputableInPolyTime.binary_log_two.comp ComputableInPolyTime.unary_to_binary

/-- **The taper is polynomial-time**, in unary from the scale and the depth in unary. -/
theorem taper_polyTime : ComputableInPolyTime (fun q : ℕ × ℕ => taper q.1 q.2)
    (encPair encUnary encUnary) encUnary := by
  have hlog := log_polyTime.comp (ComputableInPolyTime.fst encUnary encUnary)
  exact ComputableInPolyTime.binary_to_unary_bounded
    (ComputableInPolyTime.binary_div.comp ((ComputableInPolyTime.unary_to_binary.comp hlog).prod
      (ComputableInPolyTime.binary_two_pow.comp (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.const 17) (ComputableInPolyTime.snd encUnary encUnary)))))
    hlog fun q => Nat.div_le_self _ _

/-- A sum over `Finset.range` as the sum of a list. -/
private theorem sum_range_eq_list (f : ℕ → ℕ) (n : ℕ) :
    ∑ j ∈ Finset.range n, f j = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]
    simp

/-- **The number of label coordinates is polynomial-time**, in unary from the scale and the depth
in unary. -/
theorem slotBits_polyTime : ComputableInPolyTime (fun q : ℕ × ℕ => slotBits q.1 q.2)
    (encPair encUnary encUnary) encUnary := by
  have hd := ComputableInPolyTime.snd encUnary encUnary
  have hlog := log_polyTime.comp (ComputableInPolyTime.fst encUnary encUnary)
  have hterm : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => taper p.1.1 p.2)
      (encPair (encPair encUnary encUnary) encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (taper_polyTime.comp
      (((ComputableInPolyTime.fst encUnary encUnary).comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _)))
  have hterms : ComputableInPolyTime (fun q : ℕ × ℕ => (List.range (q.2 + 1)).map (taper q.1))
      (encPair encUnary encUnary) (encList encNat) :=
    ComputableInPolyTime.mapWithInput (f := fun q j => taper q.1 j)
      (ComputableInPolyTime.range.comp
        (ComputableInPolyTime.unary_add' hd (ComputableInPolyTime.const 1))) hterm
  have hsum := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.binary_sum).comp hterms
  have hval (q : ℕ × ℕ) : slotBits q.1 q.2 = 2 * ((List.range (q.2 + 1)).map (taper q.1)).sum := by
    simp only [slotBits, prefixBits, sum_range_eq_list]
  refine (ComputableInPolyTime.binary_to_unary_bounded
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2) hsum) hlog
    fun q => ?_).of_enc_eq fun q => ?_
  · simp only [Function.comp_apply, ← hval]
    exact (slotBits_le q.1 q.2).trans (Nat.div_le_self _ _)
  · simp only [Function.comp_apply, hval]

/-- `2 ^ a ≤ s + 1` for the number `a = slotBits s d` of label coordinates. -/
theorem two_pow_slotBits_le (s d : ℕ) : 2 ^ slotBits s d ≤ s + 1 := by
  have ha := slotBits_le s d
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp only [Nat.log_zero_right, Nat.zero_div, Nat.le_zero] at ha
    simp [ha]
  · calc 2 ^ slotBits s d ≤ 2 ^ Nat.log 2 s :=
          Nat.pow_le_pow_right (by norm_num) (ha.trans (Nat.div_le_self _ _))
      _ ≤ s := Nat.pow_log_le_self 2 hs.ne'
      _ ≤ s + 1 := Nat.le_succ s

/-- **The multiplicity step is polynomial-time**, in unary from the scale, the depth and the number
of edges in unary. -/
theorem taperStep_polyTime :
    ComputableInPolyTime (fun q : ℕ × ℕ × ℕ => taperStep q.1 q.2.1 q.2.2)
      (encPair encUnary (encPair encUnary encUnary)) encUnary := by
  have hs := ComputableInPolyTime.fst encUnary (encPair encUnary encUnary)
  have hr := ComputableInPolyTime.snd encUnary (encPair encUnary encUnary)
  have hd := (ComputableInPolyTime.fst encUnary encUnary).comp hr
  have hM := (ComputableInPolyTime.snd encUnary encUnary).comp hr
  have hu := taper_polyTime.comp (hs.prod hd)
  exact ComputableInPolyTime.unary_div.comp ((ComputableInPolyTime.unary_sub'
    (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.const 3) hM) hu) (ComputableInPolyTime.const 1)).prod hu)

/-- **The leaf size is polynomial-time**, in unary from the scale in unary. -/
theorem leafSize_polyTime : ComputableInPolyTime leafSize encUnary encUnary :=
  ComputableInPolyTime.binary_to_unary_bounded
    (ComputableInPolyTime.binary_div.comp (ComputableInPolyTime.unary_to_binary.prod
      (ComputableInPolyTime.binary_sqrt' (ComputableInPolyTime.unary_to_binary.comp log_polyTime))))
    (ComputableInPolyTime.id' (encIn := encUnary)) fun _ => Nat.div_le_self _ _

/-- **The degree bound is polynomial-time**: `2 ^ (9 ⌊log₂ s⌋ / 10 + 2)` in binary from `s` in
unary. -/
theorem degreeBound_polyTime : ComputableInPolyTime degreeBound encUnary encNat := by
  have hb := ComputableInPolyTime.unary_to_binary
  have hlog := ComputableInPolyTime.binary_log_two.comp hb
  have he : ComputableInPolyTime (fun m => 9 * Nat.log 2 m / 10 + 2) encUnary encUnary :=
    ComputableInPolyTime.binary_to_unary_bounded
      (ComputableInPolyTime.binary_add.comp ((ComputableInPolyTime.binary_div.comp
        ((ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 9) (hb.comp hlog)).prod
          (ComputableInPolyTime.const 10))).prod (ComputableInPolyTime.const 2)))
      (ComputableInPolyTime.unary_add' hlog (ComputableInPolyTime.const 2)) fun m => by
        simp only [Function.comp_apply]; omega
  exact ComputableInPolyTime.binary_two_pow.comp he

end Cslib.Circuits.Frontier.ContractionSchedule

namespace Cslib.Circuits.Frontier.FastContraction

open GaloisRingArith ChildCursor NativeRecovery ContractionSchedule NativeChild
  Cslib.GenericRAM Cslib.GenericRAM.StackRecursion

variable {T : Type} {encT : T ↪ List Bool}

/-! ### The parameters of a call -/

/-- The scale is polynomial-time. -/
theorem scale_polyTime : ComputableInPolyTime Call.scale (encCall encT) encUnary := by
  unfold Call.scale; fun_prop

/-- The edge bound is polynomial-time. -/
theorem bound_polyTime : ComputableInPolyTime Call.bound (encCall encT) encUnary := by
  unfold Call.bound; fun_prop

/-- The precision is polynomial-time. -/
theorem prec_polyTime : ComputableInPolyTime Call.prec (encCall encT) encUnary := by
  unfold Call.prec; fun_prop

/-- The coefficients of the modulus are polynomial-time. -/
theorem fl_polyTime : ComputableInPolyTime Call.fl (encCall encT) (encList encNat) := by
  unfold Call.fl; fun_prop

/-- The number of rows is polynomial-time. -/
theorem rows_polyTime : ComputableInPolyTime Call.rows (encCall encT) encNat := by
  unfold Call.rows; fun_prop

/-- The network is polynomial-time. -/
theorem net_polyTime :
    ComputableInPolyTime Call.net (encCall encT)
      (DescribedNetwork.encDescribed (VertexDesc.enc encT)) := by
  unfold Call.net; fun_prop

/-- The number of edges is polynomial-time, in unary. -/
theorem edges_polyTime : ComputableInPolyTime Call.edges (encCall encT) encUnary :=
  DescribedNetwork.numEdges_polyTime.comp net_polyTime

/-- The vertices are polynomial-time. -/
theorem vertices_polyTime : ComputableInPolyTime (fun x : Call T => x.net.vertices) (encCall encT)
    (encList (encPair (encList encNat) (VertexDesc.enc encT))) :=
  DescribedNetwork.vertices_polyTime.comp net_polyTime

/-! ### The schedule of a call -/

/-- The number of label coordinates is polynomial-time. -/
theorem slots_polyTime : ComputableInPolyTime slots (encCall encT) encUnary :=
  slotBits_polyTime.comp (scale_polyTime.prod (depth_polyTime encT))

/-- `2 ^ a ≤ s + 1` at every call. -/
theorem two_pow_slots_le (x : Call T) : 2 ^ slots x ≤ x.scale + 1 := two_pow_slotBits_le _ _

/-- The number `2 ^ a` of slots is polynomial-time, in unary. -/
theorem twoPowSlots_polyTime : ComputableInPolyTime (fun x => 2 ^ slots x)
    (encCall encT) encUnary :=
  ComputableInPolyTime.binary_to_unary_bounded
    (ComputableInPolyTime.binary_two_pow.comp slots_polyTime)
    (ComputableInPolyTime.unary_add' scale_polyTime (ComputableInPolyTime.const 1))
    two_pow_slots_le

/-- The number `2 ^ (a + 1)` of grid indices is polynomial-time, in unary. -/
theorem twoPowSlotsSucc_polyTime :
    ComputableInPolyTime (fun x => 2 ^ (slots x + 1)) (encCall encT) encUnary :=
  (ComputableInPolyTime.unary_add' twoPowSlots_polyTime twoPowSlots_polyTime).of_enc_eq fun x => by
    rw [pow_succ, mul_two]

/-- The number of levels is polynomial-time. -/
theorem levels_polyTime : ComputableInPolyTime levels (encCall encT) encUnary :=
  taper_polyTime.comp (scale_polyTime.prod (depth_polyTime encT))

/-- The multiplicity step is polynomial-time. -/
theorem step_polyTime : ComputableInPolyTime step (encCall encT) encUnary :=
  taperStep_polyTime.comp (scale_polyTime.prod ((depth_polyTime encT).prod edges_polyTime))

/-- The number of interpolation points is polynomial-time, in unary. -/
theorem numPoints_polyTime : ComputableInPolyTime numPoints (encCall encT) encUnary :=
  ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' edges_polyTime
    (ComputableInPolyTime.unary_sub' (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.const 2) twoPowSlots_polyTime) (ComputableInPolyTime.const 1)))
    (ComputableInPolyTime.const 1)

/-- The shift `Δ'` is polynomial-time, in unary. -/
theorem shift_polyTime : ComputableInPolyTime shift (encCall encT) encUnary :=
  ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.unary_mul'
        (ComputableInPolyTime.unary_add' slots_polyTime (ComputableInPolyTime.const 1))
        twoPowSlotsSucc_polyTime) step_polyTime) levels_polyTime)
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.const 8) step_polyTime) twoPowSlots_polyTime))
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.const 8) edges_polyTime)
      (ComputableInPolyTime.unary_add' slots_polyTime (ComputableInPolyTime.const 1)))

/-- The common precision `N = p + Δ'` is polynomial-time, in unary. -/
theorem wide_polyTime : ComputableInPolyTime wide (encCall encT) encUnary :=
  ComputableInPolyTime.unary_add' prec_polyTime shift_polyTime

/-! ### Nodes, levels and precisions -/

/-- The capped valuation `twoVal b d` is at most `b`. -/
private theorem twoVal_le (b d : ℕ) : twoVal b d ≤ b := by
  unfold twoVal
  split_ifs
  · exact Nat.zero_le _
  · exact (List.length_filter_le _ _).trans (List.length_range (n := b)).le

/-- Every level is at most `a + 1`. -/
theorem level_le (x : Call T) (k : ℕ) : level x k ≤ slots x + 1 := twoVal_le _ _

/-- The level of a grid index is polynomial-time, in unary. -/
theorem level_polyTime :
    ComputableInPolyTime (fun q : Call T × ℕ => level q.1 q.2) (encPair (encCall encT) encUnary)
      encUnary := by
  have hx := ComputableInPolyTime.fst (encCall encT) encUnary
  have hk := ComputableInPolyTime.snd (encCall encT) encUnary
  have hL := twoPowSlots_polyTime.comp hx
  have h := computableInPolyTime_twoVal
    (ComputableInPolyTime.unary_add' (slots_polyTime.comp hx) (ComputableInPolyTime.const 1))
    (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_sub' hk hL)
      (ComputableInPolyTime.unary_sub' hL hk))
  exact h

/-- The nodes of positive multiplicity are polynomial-time, as unary grid indices. -/
theorem nodes_polyTime : ComputableInPolyTime nodes (encCall encT) (encList encUnary) := by
  have hx := ComputableInPolyTime.fst (encCall encT) encUnary
  have hk := ComputableInPolyTime.snd (encCall encT) encUnary
  have hL := twoPowSlots_polyTime.comp hx
  have hmult := computableInPolyTime_mult (slots_polyTime.comp hx) hL (levels_polyTime.comp hx)
    (step_polyTime.comp hx) hk
  have htest : ComputableInPolyTime (fun q : Call T × ℕ =>
      decide (q.2 ≠ 2 ^ slots q.1 ∧ 0 < mult (slots q.1) (levels q.1) (step q.1) q.2))
      (encPair (encCall encT) encUnary) encBool :=
    (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_not.comp
      (ComputableInPolyTime.decide_eq' hk hL))
      (ComputableInPolyTime.unary_lt' (ComputableInPolyTime.const 0) hmult)).of_enc_eq fun q => by
      simp only [Function.comp_apply, Bool.decide_and, decide_not]
  have h := ComputableInPolyTime.filterWithInput
    (test := fun (x : Call T) k =>
      decide (k ≠ 2 ^ slots x ∧ 0 < mult (slots x) (levels x) (step x) k))
    (ComputableInPolyTime.range.comp twoPowSlotsSucc_polyTime) htest
  exact h

/-- The grid index of the `i`-th node is polynomial-time, in unary. -/
theorem node_polyTime :
    ComputableInPolyTime (fun q : Call T × ℕ => (nodes q.1).getD q.2 0)
      (encPair (encCall encT) encUnary)
      encUnary := by
  have h := ComputableInPolyTime.listGetDWithInput
    (nodes_polyTime.comp (ComputableInPolyTime.fst (encCall encT) encUnary))
    (ComputableInPolyTime.snd (encCall encT) encUnary) 0
  exact h

/-- The level of the `i`-th node is polynomial-time, in unary. -/
theorem nodeLevel_polyTime :
    ComputableInPolyTime (fun q : Call T × ℕ => level q.1 ((nodes q.1).getD q.2 0))
      (encPair (encCall encT) encUnary) encUnary := by
  have h := level_polyTime.comp
      ((ComputableInPolyTime.fst (encCall encT) encUnary).prod node_polyTime)
  exact h

/-- The number `2 ^ (v₂ t + 1)` of tiles of the `i`-th node is polynomial-time, in unary. -/
theorem tiles_polyTime :
    ComputableInPolyTime (fun q : Call T × ℕ => 2 ^ (level q.1 ((nodes q.1).getD q.2 0) + 1))
      (encPair (encCall encT) encUnary) encUnary := by
  have hv := ComputableInPolyTime.binary_two_pow.comp
    (ComputableInPolyTime.unary_add' (nodeLevel_polyTime (encT := encT))
      (ComputableInPolyTime.const 1))
  have hb := ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 4)
    (twoPowSlots_polyTime.comp (ComputableInPolyTime.fst (encCall encT) encUnary))
  have h := ComputableInPolyTime.binary_to_unary_bounded hv hb fun q => by
    simp only [Function.comp_apply]
    calc 2 ^ (level q.1 ((nodes q.1).getD q.2 0) + 1) ≤ 2 ^ (slots q.1 + 2) :=
          Nat.pow_le_pow_right (by norm_num)
            (by have := level_le q.1 ((nodes q.1).getD q.2 0); omega)
      _ = 4 * 2 ^ slots q.1 := by rw [pow_add]; ring
  exact h

/-- **The precision of the `i`-th node is polynomial-time**, in unary. -/
theorem nodePrec_polyTime :
    ComputableInPolyTime (fun q : Call T × ℕ => nodePrec q.1 q.2) (encPair (encCall encT) encUnary)
      encUnary := by
  have hx := ComputableInPolyTime.fst (encCall encT) encUnary
  have hpow : ComputableInPolyTime
      (fun q : Call T × ℕ => 2 ^ (slots q.1 - level q.1 ((nodes q.1).getD q.2 0)))
      (encPair (encCall encT) encUnary) encUnary := by
    have h := ComputableInPolyTime.binary_to_unary_bounded (ComputableInPolyTime.binary_two_pow.comp
      (ComputableInPolyTime.unary_sub' (slots_polyTime.comp hx) nodeLevel_polyTime))
      (twoPowSlots_polyTime.comp hx)
      fun q => Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    exact h
  have h := ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add' (prec_polyTime.comp hx)
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.const 8) (step_polyTime.comp hx)) hpow))
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.const 8) (edges_polyTime.comp hx))
      (ComputableInPolyTime.unary_add' (slots_polyTime.comp hx) (ComputableInPolyTime.const 1)))
  exact h

/-! ### The packing and the weights -/

/-- The capped number of rows is polynomial-time, in unary. -/
theorem rowCap_polyTime : ComputableInPolyTime rowCap (encCall encT) encUnary :=
  (ComputableInPolyTime.binary_min_unary.comp
    (((ComputableInPolyTime.length_list _).comp vertices_polyTime).prod rows_polyTime)).of_enc_eq
    fun x => by simp only [Function.comp_apply, rowCap, min_comm]

/-- **The packing is polynomial-time** on every call. -/
theorem packing_polyTime : ComputableInPolyTime packing
    (encCall encT) PacketPacking.encNativePacking :=
  computableInPolyTime_nativeParentPacking rowCap_polyTime slots_polyTime net_polyTime

/-- **The number of packets is polynomial-time**, in unary, on every call: there are at most
`M (2 ^ a) ^ 12 ≤ M (s + 1) ^ 12` of them (`NativeChild.numPackets_nativeParentPacking_le`). -/
theorem packets_polyTime :
    ComputableInPolyTime (fun x : Call T => (packing x).2.1) (encCall encT) encUnary :=
  computableInPolyTime_numPackets_nativeParentPacking rowCap_polyTime slots_polyTime
    twoPowSlots_polyTime net_polyTime

/-- **The weights of the modes of the `i`-th node are polynomial-time.** -/
theorem weights_polyTime :
    ComputableInPolyTime (fun q : Call T × ℕ => weights q.1 q.2) (encPair (encCall encT) encUnary)
      (encList encNat) := by
  have hx := ComputableInPolyTime.fst (encCall encT) encUnary
  have hp := nodePrec_polyTime (encT := encT)
  have hlen := ComputableInPolyTime.unary_mul' (packets_polyTime.comp hx)
    (ComputableInPolyTime.unary_mul' tiles_polyTime hp)
  have hj := ComputableInPolyTime.snd (encPair (encCall encT) encUnary) encUnary
  have hpj := hp.comp (ComputableInPolyTime.fst (encPair (encCall encT) encUnary) encUnary)
  have hf : ComputableInPolyTime (fun r : (Call T × ℕ) × ℕ => r.2 % nodePrec r.1.1 r.1.2 + 1)
      (encPair (encPair (encCall encT) encUnary) encUnary) encNat := by
    have h := ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mod.comp (hj.prod hpj)) (ComputableInPolyTime.const 1))
    exact h
  have h := ComputableInPolyTime.mapWithInput
    (f := fun (q : Call T × ℕ) j => j % nodePrec q.1 q.2 + 1)
    (ComputableInPolyTime.range.comp hlen) hf
  exact h

/-- The number of modes of the `i`-th node is polynomial-time, in unary. -/
theorem weightsLength_polyTime :
    ComputableInPolyTime (fun q : Call T × ℕ => (weights q.1 q.2).length)
      (encPair (encCall encT) encUnary)
      encUnary := by
  have h := (ComputableInPolyTime.length_list _).comp (weights_polyTime (encT := encT))
  exact h

/-! ### Points and the table -/

/-- The binary digits are polynomial-time, from the length and the number in unary. -/
theorem digits_polyTime :
    ComputableInPolyTime (fun q : ℕ × ℕ => digits q.1 q.2) (encPair encUnary encUnary)
      (encList encNat) := by
  have hk := (ComputableInPolyTime.snd encUnary encUnary).comp
    (ComputableInPolyTime.fst (encPair encUnary encUnary) encUnary)
  have hf : ComputableInPolyTime (fun r : (ℕ × ℕ) × ℕ => if r.1.2.testBit r.2 then 1 else 0)
      (encPair (encPair encUnary encUnary) encUnary) encNat := by
    have h := ComputableInPolyTime.ite (encMid := encNat) (ComputableInPolyTime.binary_testBit
      (ComputableInPolyTime.unary_to_binary.comp hk) (ComputableInPolyTime.snd _ _))
      (ComputableInPolyTime.const 1) (ComputableInPolyTime.const 0)
    exact h
  have h := ComputableInPolyTime.mapWithInput
    (f := fun (q : ℕ × ℕ) i => if q.2.testBit i then 1 else 0)
    (ComputableInPolyTime.range.comp (ComputableInPolyTime.fst encUnary encUnary)) hf
  exact h

/-- **The interpolation points are polynomial-time.** -/
theorem points_polyTime : ComputableInPolyTime points (encCall encT)
    (encList (encList encNat)) := by
  have hf : ComputableInPolyTime (fun r : Call T × ℕ => digits r.1.fl.length r.2)
      (encPair (encCall encT) encUnary) (encList encNat) := by
    have h := digits_polyTime.comp ((((ComputableInPolyTime.length_list _).comp fl_polyTime).comp
      (ComputableInPolyTime.fst (encCall encT) encUnary)).prod (ComputableInPolyTime.snd _ _))
    exact h
  have h := ComputableInPolyTime.mapWithInput (f := fun (x : Call T) k => digits x.fl.length k)
    (ComputableInPolyTime.range.comp numPoints_polyTime) hf
  exact h

/-- **The table of native recovery is polynomial-time**, from a call and the stored values. -/
theorem table_polyTime :
    ComputableInPolyTime (fun q : Call T × List (List ℕ) => table q.1 q.2)
      (encPair (encCall encT) (encList (encList encNat))) (encList (encList (encList encNat))) := by
  let e := encPair (encCall encT) (encList (encList encNat))
  have hx := ComputableInPolyTime.fst (encCall encT) (encList (encList encNat))
  have hx' := hx.comp (ComputableInPolyTime.fst e encUnary)
  have hV' := (ComputableInPolyTime.snd (encCall encT) (encList (encList encNat))).comp
    (ComputableInPolyTime.fst e encUnary)
  have hk := ComputableInPolyTime.snd e encUnary
  have hn := numPoints_polyTime.comp hx'
  have hmem := ComputableInPolyTime.decide_mem (nodes_polyTime.comp hx') hk
  have hidx := ComputableInPolyTime.idxOfWithInput (nodes_polyTime.comp hx') hk
  have hdrop : ComputableInPolyTime (fun r : (Call T × List (List ℕ)) × ℕ =>
      r.1.2.drop ((nodes r.1.1).idxOf r.2 * numPoints r.1.1)) (encPair e encUnary)
      (encList (encList encNat)) :=
    .of_tidy (ComputableTidilyInPolyTime.listDropWithInput hV'.tidy
      (ComputableInPolyTime.unary_mul' hidx hn).tidy)
  have htake : ComputableInPolyTime (fun r : (Call T × List (List ℕ)) × ℕ =>
      (r.1.2.drop ((nodes r.1.1).idxOf r.2 * numPoints r.1.1)).take (numPoints r.1.1))
      (encPair e encUnary) (encList (encList encNat)) :=
    .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hdrop.tidy hn.tidy)
  have hf : ComputableInPolyTime (fun r : (Call T × List (List ℕ)) × ℕ =>
      if r.2 ∈ nodes r.1.1 then
        (r.1.2.drop ((nodes r.1.1).idxOf r.2 * numPoints r.1.1)).take (numPoints r.1.1)
      else []) (encPair e encUnary) (encList (encList encNat)) := by
    have h := ComputableInPolyTime.ite hmem htake (ComputableInPolyTime.const [])
    refine h.of_enc_eq fun r => ?_
    simp only [Function.comp_apply, decide_eq_true_eq]
  have h := ComputableInPolyTime.mapWithInput (f := fun (q : Call T × List (List ℕ)) k =>
      if k ∈ nodes q.1 then
        (q.2.drop ((nodes q.1).idxOf k * numPoints q.1)).take (numPoints q.1) else [])
    (ComputableInPolyTime.range.comp (twoPowSlotsSucc_polyTime.comp hx)) hf
  exact h

/-! ### Active calls -/

/-- Whether a call is active, as a conjunction of tests. -/
theorem active_eq (x : Call T) : active x =
    (decide (leafSize x.scale < x.edges) && decide (1 ≤ levels x) && decide (levels x ≤ x.edges) &&
      decide (levels x ≤ slots x) &&
      x.net.vertices.all (fun v => decide (v.1.length ≤ degreeBound x.scale)) &&
      decide (numPoints x ≤ 2 ^ x.fl.length) && decide (x.edges < x.bound)) := by
  simp only [active, Bool.decide_and, List.all_eq, decide_eq_true_eq, Bool.and_assoc]

/-- **Whether a call is active is polynomial-time.** -/
theorem active_polyTime : ComputableInPolyTime active (encCall encT) encBool := by
  have hdeg : ComputableInPolyTime (fun x : Call T =>
      x.net.vertices.all (fun v => decide (v.1.length ≤ degreeBound x.scale)))
        (encCall encT) encBool :=
    ComputableInPolyTime.allWithInput vertices_polyTime
      (ComputableInPolyTime.binary_le' (ComputableInPolyTime.unary_to_binary.comp
        ((ComputableInPolyTime.length_list _).comp ((ComputableInPolyTime.fst _ _).comp
          (ComputableInPolyTime.snd _ _))))
        (degreeBound_polyTime.comp (scale_polyTime.comp (ComputableInPolyTime.fst _ _))))
  have h := ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and'
    (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and'
        (ComputableInPolyTime.unary_lt' (leafSize_polyTime.comp scale_polyTime) edges_polyTime)
        (ComputableInPolyTime.unary_le' (ComputableInPolyTime.const 1) levels_polyTime))
        (ComputableInPolyTime.unary_le' levels_polyTime edges_polyTime))
        (ComputableInPolyTime.unary_le' levels_polyTime slots_polyTime)) hdeg)
      (ComputableInPolyTime.binary_le'
        (ComputableInPolyTime.unary_to_binary.comp numPoints_polyTime)
        (ComputableInPolyTime.binary_two_pow.comp
          ((ComputableInPolyTime.length_list _).comp fl_polyTime))))
    (ComputableInPolyTime.unary_lt' edges_polyTime bound_polyTime)
  refine h.of_enc_eq fun x => ?_
  rw [active_eq]
  rfl

/-! ### The components of the scheme -/

section Scheme

variable (ev : T → List Bool → List ℕ) (mk : Call T → State → ℕ × DescribedNetwork (VertexDesc T))

/-- **The leaf test is polynomial-time.** -/
theorem isLeaf_polyTime : ComputableInPolyTime (scheme ev mk).isLeaf (encCall encT) encBool := by
  have h := ComputableInPolyTime.bool_not.comp (active_polyTime (encT := encT))
  exact h

/-- **The initial accumulator is polynomial-time.** -/
theorem start_polyTime : ComputableInPolyTime (scheme ev mk).start (encCall encT) encFrame := by
  have hlen : ComputableInPolyTime (fun x : Call T => (weights x 0).length)
      (encCall encT) encUnary := by
    have h := weightsLength_polyTime.comp
      ((ComputableInPolyTime.id' (encIn := (encCall encT))).prod (ComputableInPolyTime.const 0))
    exact h
  have hst : ComputableInPolyTime (fun x : Call T => cursorStart (weights x)) (encCall encT)
      (encPair encUnary (encPair encUnary (encPair (encList encNat) encUnary))) :=
    (ComputableInPolyTime.const 0).prod ((ComputableInPolyTime.const 0).prod
      ((ComputableInPolyTime.replicate hlen (ComputableInPolyTime.const 0)).prod
        (ComputableInPolyTime.const 0)))
  have hst' : ComputableInPolyTime (fun x : Call T => cursorStart (weights x)) (encCall encT)
      ChildCursor.encState := hst
  have h : ComputableInPolyTime (scheme ev mk).start (encCall encT)
      (encPair (encOption ChildCursor.encState)
        (encPair (encList encNat) (encPair (encList encNat) (encList (encList encNat))))) :=
    ((ComputableInPolyTime.optionSome _).comp hst').prod
      ((computableInPolyTime_one fl_polyTime).prod ((computableInPolyTime_zero fl_polyTime).prod
        (ComputableInPolyTime.const [])))
  exact h

/-- The node index of a cursor state is polynomial-time. -/
private theorem stateNode_polyTime :
    ComputableInPolyTime (fun c : State => c.1) ChildCursor.encState encUnary := by
  unfold ChildCursor.encState; fun_prop

/-- The point index of a cursor state is polynomial-time. -/
private theorem statePoint_polyTime :
    ComputableInPolyTime (fun c : State => c.2.1) ChildCursor.encState encUnary := by
  unfold ChildCursor.encState; fun_prop

/-- The exponents of a cursor state are polynomial-time, in binary. -/
private theorem stateExps_polyTime :
    ComputableInPolyTime (fun c : State => c.2.2.1) ChildCursor.encState (encList encNat) := by
  unfold ChildCursor.encState; fun_prop

/-- The group of a cursor state is polynomial-time. -/
private theorem stateGroup_polyTime :
    ComputableInPolyTime (fun c : State => c.2.2.2) ChildCursor.encState encUnary := by
  unfold ChildCursor.encState; fun_prop

variable {ev mk}

/-- **The child call at a cursor state is polynomial-time**, given a polynomial-time builder. -/
theorem child_polyTime
    (hmk : ComputableInPolyTime (fun q : Call T × State => mk q.1 q.2)
      (encPair (encCall encT) ChildCursor.encState)
      (encPair encNat (DescribedNetwork.encDescribed (VertexDesc.enc encT)))) :
    ComputableInPolyTime (fun q : Call T × State => child q.1 mk q.2)
      (encPair (encCall encT) ChildCursor.encState) (encCall encT) := by
  have hx := ComputableInPolyTime.fst (encCall encT) ChildCursor.encState
  have ht := stateNode_polyTime.comp (ComputableInPolyTime.snd (encCall encT) ChildCursor.encState)
  have hprec : ComputableInPolyTime (fun q : Call T × State => nodePrec q.1 q.2.1)
      (encPair (encCall encT) ChildCursor.encState) encUnary := by
    have h := nodePrec_polyTime.comp (hx.prod ht)
    exact h
  have h : ComputableInPolyTime (fun q : Call T × State => child q.1 mk q.2)
      (encPair (encCall encT) ChildCursor.encState)
      (encPair (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary
        (encPair (encList encNat) encNat)))))
          (DescribedNetwork.encDescribed (VertexDesc.enc encT))) :=
    ((scale_polyTime.comp hx).prod ((ComputableInPolyTime.unary_add' ((depth_polyTime encT).comp hx)
      (ComputableInPolyTime.const 1)).prod ((edges_polyTime.comp hx).prod (hprec.prod
        ((fl_polyTime.comp hx).prod ((ComputableInPolyTime.fst _ _).comp hmk)))))).prod
      ((ComputableInPolyTime.snd _ _).comp hmk)
  exact h

/-- **Child generation is polynomial-time**, given a polynomial-time builder. -/
theorem next_polyTime
    (hmk : ComputableInPolyTime (fun q : Call T × State => mk q.1 q.2)
      (encPair (encCall encT) ChildCursor.encState)
      (encPair encNat (DescribedNetwork.encDescribed (VertexDesc.enc encT)))) :
    ComputableInPolyTime (fun p : Call T × Frame => (scheme ev mk).next p.1 p.2)
      (encPair (encCall encT) encFrame) (encOption (encCall encT)) := by
  have hc : ComputableInPolyTime (fun p : Call T × Frame => p.2.1) (encPair (encCall encT) encFrame)
      (encOption ChildCursor.encState) :=
    (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd (encCall encT) encFrame)
  have hbody : ComputableInPolyTime (fun r : (Call T × Frame) × State => some (child r.1.1 mk r.2))
      (encPair (encPair (encCall encT) encFrame) ChildCursor.encState)
        (encOption (encCall encT)) := by
    have h := (ComputableInPolyTime.optionSome (encCall encT)).comp ((child_polyTime hmk).comp
      (((ComputableInPolyTime.fst (encCall encT) encFrame).comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _)))
    exact h
  have h := ComputableInPolyTime.optionElimWithInput
    (body := fun (p : Call T × Frame) (c : State) => some (child p.1 mk c)) hc
    (ComputableInPolyTime.const (encOut := encOption (encCall encT)) none) hbody
  refine h.of_enc_eq fun p => ?_
  rcases p with ⟨x, _ | c, acc⟩ <;> rfl

variable (ev mk)

/-- The inputs of `absorb` at a cursor state: the call, its frame, the child's value and the
state. -/
private abbrev AbsorbIn (T : Type) : Type := ((Call T × Frame) × (ℕ × List ℕ)) × State

/-- The encoding of `AbsorbIn`. -/
private abbrev encAbsorbIn (encT : T ↪ List Bool) : AbsorbIn T ↪ List Bool :=
  encPair (encPair (encPair (encCall encT) encFrame) encValue) ChildCursor.encState

/-- The call of an input of `absorb`. -/
private theorem absorbCall_polyTime :
    ComputableInPolyTime (fun r : AbsorbIn T => r.1.1.1) (encAbsorbIn encT) (encCall encT) :=
  (ComputableInPolyTime.fst (encCall encT) encFrame).comp
    ((ComputableInPolyTime.fst _ encValue).comp
    (ComputableInPolyTime.fst _ ChildCursor.encState))

/-- The state of an input of `absorb`. -/
private theorem absorbState_polyTime :
    ComputableInPolyTime (fun r : AbsorbIn T => r.2) (encAbsorbIn encT) ChildCursor.encState :=
  ComputableInPolyTime.snd _ _

/-- **The cursor step of `absorb` is polynomial-time.** -/
private theorem absorbCursor_polyTime :
    ComputableInPolyTime (fun r : AbsorbIn T => cursorNext (weights r.1.1.1) (nodePrec r.1.1.1)
      (nodes r.1.1.1).length (numPoints r.1.1.1) 64 r.2) (encAbsorbIn encT)
        (encOption encState) := by
  have hx := absorbCall_polyTime (encT := encT)
  have hc := absorbState_polyTime (encT := encT)
  have ht := stateNode_polyTime.comp hc
  have hT := (ComputableInPolyTime.length_list _).comp (nodes_polyTime.comp hx)
  have hn := numPoints_polyTime.comp hx
  have hwt : ComputableInPolyTime (fun r : AbsorbIn T => weights r.1.1.1 r.2.1) (encAbsorbIn encT)
      (encList encNat) := by
    have h := weights_polyTime.comp (hx.prod ht)
    exact h
  have hpt : ComputableInPolyTime (fun r : AbsorbIn T => nodePrec r.1.1.1 r.2.1) (encAbsorbIn encT)
      encNat := by
    have h := ComputableInPolyTime.unary_to_binary.comp (nodePrec_polyTime.comp (hx.prod ht))
    exact h
  have hnext : ComputableInPolyTime (fun r : AbsorbIn T => (weights r.1.1.1 (r.2.1 + 1)).length)
      (encAbsorbIn encT) encUnary := by
    have h := weightsLength_polyTime.comp
      (hx.prod (ComputableInPolyTime.unary_add' ht (ComputableInPolyTime.const 1)))
    exact h
  have hin : ComputableInPolyTime (fun r : AbsorbIn T =>
      (((((nodes r.1.1.1).length, numPoints r.1.1.1, (64 : ℕ)), (weights r.1.1.1 r.2.1,
        nodePrec r.1.1.1 r.2.1, (weights r.1.1.1 (r.2.1 + 1)).length)), r.2) : StepInput))
      (encAbsorbIn encT) (encPair (encPair (encPair encUnary (encPair encUnary encUnary))
        (encPair (encList encNat) (encPair encNat encUnary))) ChildCursor.encState) :=
    ((hT.prod (hn.prod (ComputableInPolyTime.const 64))).prod (hwt.prod (hpt.prod hnext))).prod hc
  have hin' : ComputableInPolyTime (fun r : AbsorbIn T =>
      (((((nodes r.1.1.1).length, numPoints r.1.1.1, (64 : ℕ)), (weights r.1.1.1 r.2.1,
        nodePrec r.1.1.1 r.2.1, (weights r.1.1.1 (r.2.1 + 1)).length)), r.2) : StepInput))
      (encAbsorbIn encT) encStepInput := hin
  refine (computableInPolyTime_cursorStep.comp hin').of_enc_eq fun r => ?_
  rw [cursorNext_eq_cursorStep]
  rfl

/-- **The accumulator step of `absorb` is polynomial-time.** -/
private theorem absorbAcc_polyTime :
    ComputableInPolyTime (fun r : AbsorbIn T => absorbAt (weights r.1.1.1) (nodePrec r.1.1.1) 64
      (mul (wide r.1.1.1) r.1.1.1.fl) (add (wide r.1.1.1) r.1.1.1.fl) (one r.1.1.1.fl)
      (zero r.1.1.1.fl) r.2 r.1.1.2.2 r.1.2.2) (encAbsorbIn encT)
      (encPair (encList encNat) (encPair (encList encNat) (encList (encList encNat)))) := by
  have hx := absorbCall_polyTime (encT := encT)
  have hc := absorbState_polyTime (encT := encT)
  have ht := stateNode_polyTime.comp hc
  have hN := wide_polyTime.comp hx
  have hfl := fl_polyTime.comp hx
  have hacc : ComputableInPolyTime (fun r : AbsorbIn T => r.1.1.2.2) (encAbsorbIn encT)
      (encPair (encList encNat) (encPair (encList encNat) (encList (encList encNat)))) :=
    (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd (encCall encT) encFrame).comp
      ((ComputableInPolyTime.fst _ encValue).comp
        (ComputableInPolyTime.fst _ ChildCursor.encState)))
  have hprod := (ComputableInPolyTime.fst _ _).comp hacc
  have hsum := (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd _ _).comp hacc)
  have hstored := (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp hacc)
  have hy : ComputableInPolyTime (fun r : AbsorbIn T => r.1.2.2) (encAbsorbIn encT)
      (encList encNat) :=
    (ComputableInPolyTime.snd encUnary (encList encNat)).comp ((ComputableInPolyTime.snd _ _).comp
      (ComputableInPolyTime.fst _ ChildCursor.encState))
  have hpy := computableInPolyTime_mul hN hfl hprod hy
  have hnew := computableInPolyTime_add hN hfl hsum hpy
  have hone := computableInPolyTime_one hfl
  have hzero := computableInPolyTime_zero hfl
  have hlast : ComputableInPolyTime (fun r : AbsorbIn T =>
      (BudgetTuples.budgetNext (weights r.1.1.1 r.2.1) (nodePrec r.1.1.1 r.2.1) r.2.2.2.1).isNone)
      (encAbsorbIn encT) encBool := by
    have hwt : ComputableInPolyTime (fun r : AbsorbIn T => weights r.1.1.1 r.2.1) (encAbsorbIn encT)
        (encList encNat) := by
      have h := weights_polyTime.comp (hx.prod ht)
      exact h
    have hpt : ComputableInPolyTime (fun r : AbsorbIn T => nodePrec r.1.1.1 r.2.1)
        (encAbsorbIn encT)
        encNat := by
      have h := ComputableInPolyTime.unary_to_binary.comp (nodePrec_polyTime.comp (hx.prod ht))
      exact h
    have hin : ComputableInPolyTime (fun r : AbsorbIn T =>
        (weights r.1.1.1 r.2.1, nodePrec r.1.1.1 r.2.1, r.2.2.2.1)) (encAbsorbIn encT)
        (encPair (encList encNat) (encPair encNat (encList encNat))) :=
      hwt.prod (hpt.prod (stateExps_polyTime.comp hc))
    have hin' : ComputableInPolyTime (fun r : AbsorbIn T =>
        (weights r.1.1.1 r.2.1, nodePrec r.1.1.1 r.2.1, r.2.2.2.1)) (encAbsorbIn encT)
        BudgetTuples.encBudgetInput := hin
    have h := ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.optionIsSome
      (BudgetTuples.computableInPolyTime_budgetNext.comp hin'))
    refine h.of_enc_eq fun r => ?_
    simp only [Function.comp_apply]
    cases BudgetTuples.budgetNext (weights r.1.1.1 r.2.1) (nodePrec r.1.1.1 r.2.1) r.2.2.2.1 <;> rfl
  have hg : ComputableInPolyTime (fun r : AbsorbIn T => decide (r.2.2.2.2 + 1 < 64))
      (encAbsorbIn encT)
      encBool :=
    ComputableInPolyTime.unary_lt' (ComputableInPolyTime.unary_add' (stateGroup_polyTime.comp hc)
      (ComputableInPolyTime.const 1)) (ComputableInPolyTime.const 64)
  have h := ComputableInPolyTime.ite hg (hpy.prod (hsum.prod hstored))
    (ComputableInPolyTime.ite hlast (hone.prod (hzero.prod (ComputableInPolyTime.listAppend' hstored
      (ComputableInPolyTime.cons' hnew (ComputableInPolyTime.const [])))))
      (hone.prod (hnew.prod hstored)))
  refine h.of_enc_eq fun r => ?_
  simp only [absorbAt, decide_eq_true_eq, Function.comp_apply]

/-- **Absorbing a child's value is polynomial-time.** -/
theorem absorb_polyTime :
    ComputableInPolyTime
      (fun p : (Call T × Frame) × (ℕ × List ℕ) => (scheme ev mk).absorb p.1.1 p.1.2 p.2)
      (encPair (encPair (encCall encT) encFrame) encValue) encFrame := by
  have hc : ComputableInPolyTime (fun p : (Call T × Frame) × (ℕ × List ℕ) => p.1.2.1)
      (encPair (encPair (encCall encT) encFrame) encValue) (encOption ChildCursor.encState) :=
    (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd (encCall encT) encFrame).comp
      (ComputableInPolyTime.fst _ encValue))
  have hfallback : ComputableInPolyTime (fun p : (Call T × Frame) × (ℕ × List ℕ) => p.1.2)
      (encPair (encPair (encCall encT) encFrame) encValue) encFrame :=
    (ComputableInPolyTime.snd (encCall encT) encFrame).comp (ComputableInPolyTime.fst _ encValue)
  have hbody : ComputableInPolyTime (fun r : AbsorbIn T =>
      ((cursorNext (weights r.1.1.1) (nodePrec r.1.1.1) (nodes r.1.1.1).length (numPoints r.1.1.1)
        64 r.2, absorbAt (weights r.1.1.1) (nodePrec r.1.1.1) 64
        (mul (wide r.1.1.1) r.1.1.1.fl) (add (wide r.1.1.1) r.1.1.1.fl) (one r.1.1.1.fl)
        (zero r.1.1.1.fl) r.2 r.1.1.2.2 r.1.2.2) : Frame)) (encAbsorbIn encT) encFrame :=
    absorbCursor_polyTime.prod (absorbAcc_polyTime)
  have h := ComputableInPolyTime.optionElimWithInput
    (body := fun (p : (Call T × Frame) × (ℕ × List ℕ)) (c : State) =>
      ((cursorNext (weights p.1.1) (nodePrec p.1.1) (nodes p.1.1).length (numPoints p.1.1) 64 c,
        absorbAt (weights p.1.1) (nodePrec p.1.1) 64 (mul (wide p.1.1) p.1.1.fl)
          (add (wide p.1.1) p.1.1.fl) (one p.1.1.fl) (zero p.1.1.fl) c p.1.2.2 p.2.2) : Frame))
    hc hfallback hbody
  refine h.of_enc_eq fun p => ?_
  rcases p with ⟨⟨x, _ | c, acc⟩, y⟩ <;> rfl

/-- **The value of a call is polynomial-time.** -/
theorem finish_polyTime :
    ComputableInPolyTime (fun p : Call T × Frame => (scheme ev mk).finish p.1 p.2)
      (encPair (encCall encT) encFrame) encValue := by
  have hx := ComputableInPolyTime.fst (encCall encT) encFrame
  have hV : ComputableInPolyTime (fun p : Call T × Frame => p.2.2.2.2)
      (encPair (encCall encT) encFrame)
      (encList (encList encNat)) :=
    (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd (encCall encT) encFrame)))
  have htab : ComputableInPolyTime (fun p : Call T × Frame => table p.1 p.2.2.2.2)
      (encPair (encCall encT) encFrame) (encList (encList (encList encNat))) := by
    have h := table_polyTime.comp (hx.prod hV)
    exact h
  have hrec := computableInPolyTime_recover (prec_polyTime.comp hx) (shift_polyTime.comp hx)
    (fl_polyTime.comp hx) (slots_polyTime.comp hx) (twoPowSlots_polyTime.comp hx)
    (levels_polyTime.comp hx) (step_polyTime.comp hx) (points_polyTime.comp hx) htab
  have h := ((depth_polyTime encT).comp hx).prod hrec
  exact h

variable {ev mk}

/-- **The components of the scheme are polynomial-time**, for a polynomial-time child builder. -/
theorem scheme_polyTime
    (hmk : ComputableInPolyTime (fun q : Call T × State => mk q.1 q.2)
      (encPair (encCall encT) ChildCursor.encState)
      (encPair encNat (DescribedNetwork.encDescribed (VertexDesc.enc encT)))) :
    (scheme ev mk).PolyTime (encCall encT) encFrame encValue :=
  ⟨isLeaf_polyTime ev mk, start_polyTime ev mk, next_polyTime hmk, absorb_polyTime ev mk,
    finish_polyTime ev mk⟩

end Scheme

/-! ### The native child builder -/

/-- **The native child builder is polynomial-time** on every call and cursor state
(`NativeChild.computableInPolyTime_nativeChild_nativeParentPacking`). The rows are capped at the
number of vertices and the exponents at the node's precision, so both are polynomial in unary; the
number `2 ^ a` of slots is at most `s + 1` and the number `2 ^ (v₂ t + 1)` of tiles at most
`4 (s + 1)`. -/
theorem nativeMk_polyTime :
    ComputableInPolyTime (fun q : Call T × State => nativeMk q.1 q.2)
      (encPair (encCall encT) ChildCursor.encState)
      (encPair encNat (DescribedNetwork.encDescribed (VertexDesc.enc encT))) := by
  have hx := ComputableInPolyTime.fst (encCall encT) ChildCursor.encState
  have hc := ComputableInPolyTime.snd (encCall encT) ChildCursor.encState
  have ht := stateNode_polyTime.comp hc
  have hj := statePoint_polyTime.comp hc
  have hβ := stateExps_polyTime.comp hc
  have hg := ComputableInPolyTime.unary_to_binary.comp (stateGroup_polyTime.comp hc)
  have hr := rowCap_polyTime.comp hx
  have ha := slots_polyTime.comp hx
  have hL := twoPowSlots_polyTime.comp hx
  have hfl := fl_polyTime.comp hx
  have hD := net_polyTime.comp hx
  have hi : ComputableInPolyTime (fun q : Call T × State => level q.1 ((nodes q.1).getD q.2.1 0))
      (encPair (encCall encT) ChildCursor.encState) encUnary := by
    have h := nodeLevel_polyTime.comp (hx.prod ht)
    exact h
  have hT : ComputableInPolyTime
      (fun q : Call T × State => 2 ^ (level q.1 ((nodes q.1).getD q.2.1 0) + 1))
      (encPair (encCall encT) ChildCursor.encState) encUnary := by
    have h := tiles_polyTime.comp (hx.prod ht)
    exact h
  have hpt : ComputableInPolyTime (fun q : Call T × State => nodePrec q.1 q.2.1)
      (encPair (encCall encT) ChildCursor.encState) encUnary := by
    have h := nodePrec_polyTime.comp (hx.prod ht)
    exact h
  have hnode : ComputableInPolyTime
      (fun q : Call T × State => node (slots q.1) ((nodes q.1).getD q.2.1 0))
      (encPair (encCall encT) ChildCursor.encState) encIntBin := by
    have h := ComputableInPolyTime.intBin_subNatNat.comp
      ((ComputableInPolyTime.unary_to_binary.comp (node_polyTime.comp (hx.prod ht))).prod
        (ComputableInPolyTime.unary_to_binary.comp hL))
    refine h.of_enc_eq fun q => ?_
    simp only [Function.comp_apply, node, Int.subNatNat_eq_coe, Nat.cast_pow, Nat.cast_ofNat]
  have hζ : ComputableInPolyTime (fun q : Call T × State => (points q.1).getD q.2.2.1 [])
      (encPair (encCall encT) ChildCursor.encState) (encList encNat) := by
    have h := ComputableInPolyTime.listGetDWithInput (points_polyTime.comp hx) hj []
    exact h
  have hcap : ComputableInPolyTime
      (fun q : Call T × State => q.2.2.2.1.map (min · (nodePrec q.1 q.2.1)))
      (encPair (encCall encT) ChildCursor.encState) (encList encUnary) := by
    have hf : ComputableInPolyTime
        (fun r : (Call T × State) × ℕ => min r.2 (nodePrec r.1.1 r.1.2.1))
        (encPair (encPair (encCall encT) ChildCursor.encState) encNat) encUnary := by
      have h := ComputableInPolyTime.binary_min_unary.comp
        ((hpt.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _))
      refine h.of_enc_eq fun r => ?_
      simp only [Function.comp_apply, min_comm]
    have h := ComputableInPolyTime.mapWithInput
      (f := fun (q : Call T × State) (b : ℕ) => min b (nodePrec q.1 q.2.1)) hβ hf
    exact h
  have hrows := computableInPolyTime_childRows_nativeParentPacking hr ha hi hD hg
  have hchild := computableInPolyTime_nativeChild_nativeParentPacking hfl ha hL hi hT hpt hnode hζ
    hr hD hcap hg
  have h := hrows.prod hchild
  exact h

/-- **The components of the native contraction recursion are polynomial-time**: the hypothesis
`hpoly` of `CountingSimulation.contractionAlgorithmOfNative`. -/
theorem scheme_nativeMk_polyTime (ev : T → List Bool → List ℕ) :
    (scheme ev (nativeMk (T := T))).PolyTime (encCall encT) encFrame encValue :=
  scheme_polyTime nativeMk_polyTime

end Cslib.Circuits.Frontier.FastContraction
