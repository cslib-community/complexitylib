/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionShape
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.Data.List.GetD

/-!
# The encoded sizes of the calls of the native contraction recursion

Bounds on the encoded lengths of the calls (`FastContraction.encCall`) of the native recursion
from bounds on their numbers: the length of an encoded call is at most `64 (B + 1) ^ 3 + 2 B R` when
its numbers, lists and ports are at most `B` and its descriptors at most `R` long
(`FastContraction.length_encCall_le`), and a bounded packet descriptor is at most
`200 (B + 1) ^ 2` long (`FastContraction.length_enc_inr_le`). The values are reduced at their
precision (`FastContraction.reducedAt_value`), and the frames of an active call with at most `m`
edges at scale `m` and precision `p` are at most `64 (B + 1) ^ 3` long for
`B = 256 (m + 1) ^ 5 (p + 1) + e` (`FastContraction.length_encFrame_frameAt_le`): the accumulator
stays reduced at the common precision and stores at most one value per node and point.

## Main results

* `Cslib.Circuits.Frontier.FastContraction.length_encList_le`: lists of bounded elements.
* `Cslib.Circuits.Frontier.FastContraction.length_enc_packetCtx_le`: packet contexts.
* `Cslib.Circuits.Frontier.FastContraction.length_enc_inr_le`: bounded packet descriptors.
* `Cslib.Circuits.Frontier.FastContraction.length_encCall_le`: calls.
* `Cslib.Circuits.Frontier.FastContraction.reducedAt_value`,
  `Cslib.Circuits.Frontier.FastContraction.length_encValue_le`: values.
* `Cslib.Circuits.Frontier.FastContraction.length_encFrame_frameAt_le`: the frames of an active
  call.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction

open Turing.MultiTapeTM NativePacket

variable {T : Type} {encT : T ↪ List Bool}

/-- A number at most `b` has at most `b` binary digits. -/
theorem length_encNat_le {a b : ℕ} (h : a ≤ b) : (encNat a).length ≤ b := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (h.trans_lt Nat.lt_two_pow_self)

/-- **A list of elements of encoded length at most `B`** has encoded length at most
`k (2 B + 1)` for `k` elements. -/
theorem length_encList_le {α : Type*} (enc : α ↪ List Bool) {l : List α} {B : ℕ}
    (h : ∀ a ∈ l, (enc a).length ≤ B) : (encList enc l).length ≤ l.length * (2 * B + 1) := by
  rw [length_encList]
  calc (l.map fun a => 2 * (enc a).length + 1).sum ≤ (l.map fun _ => 2 * B + 1).sum :=
        List.sum_le_sum fun a ha => by have := h a ha; omega
    _ = l.length * (2 * B + 1) := by simp

/-- A list of numbers at most `1` has encoded length at most `3 k` for `k` numbers. -/
theorem length_encList_le_of_le_one {l : List ℕ} (h : ∀ z ∈ l, z ≤ 1) :
    (encList encNat l).length ≤ 3 * l.length := by
  have := length_encList_le encNat (B := 1) fun z hz => length_encNat_le (h z hz)
  omega

/-- **A packet context with fields at most `B`** and no column list has encoded length at most
`64 (B + 1)`. -/
theorem length_enc_packetCtx_le (c : PacketCtx) {B : ℕ} (hp : c.p ≤ B) (hfl : c.fl.length ≤ B)
    (hfl1 : ∀ z ∈ c.fl, z ≤ 1) (ha : c.a ≤ B) (hL : c.L ≤ B) (hi : c.i ≤ B) (htl : c.tiles ≤ B)
    (ht : c.t.natAbs ≤ B) (hnb : c.nb ≤ B) (hcols : c.cols = []) (hζ : c.ζ.length ≤ B)
    (hζ1 : ∀ z ∈ c.ζ, z ≤ 1) : (PacketCtx.enc c).length ≤ 64 * (B + 1) := by
  have h1 := length_encList_le_of_le_one hfl1
  have h2 := length_encList_le_of_le_one hζ1
  have h3 : c.t.natAbs.size ≤ B := (Nat.size_le.mpr (Nat.lt_two_pow_self)).trans ht
  simp only [PacketCtx.enc, encOfEquiv, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
    PacketCtx.equivProd, Equiv.coe_fn_mk, length_encPair, encUnary_apply, List.length_replicate,
    length_encIntBin, encBool_apply, List.length_singleton, hcols, length_encList, List.map_nil,
    List.sum_nil] at h1 h2 ⊢
  omega

/-- `2 ^ a ≤ m` for `a ≤ ⌊log₂ m⌋` and `m ≠ 0`. -/
theorem two_pow_le_of_le_log {a m : ℕ} (ha : a ≤ Nat.log 2 m) (hm : m ≠ 0) : 2 ^ a ≤ m :=
  (Nat.pow_le_pow_right (by norm_num) ha).trans (Nat.pow_log_le_self 2 hm)

/-- **A bounded packet descriptor has encoded length at most `200 (B + 1) ^ 2`**, when
`2 (m + 1) (P + 1)`, the modulus's length and the number of ports are at most `B` and the
modulus has 0/1 coefficients. -/
theorem length_enc_inr_le {fl : List ℕ} {m P k : ℕ} {d : PacketDesc} (h : PacketBound fl m P k d)
    {B : ℕ} (hB : 2 * (m + 1) * (P + 1) ≤ B) (hfl : fl.length ≤ B) (hfl1 : ∀ z ∈ fl, z ≤ 1)
    (hk : k ≤ B) : (VertexDesc.enc encT (.inr d)).length ≤ 200 * (B + 1) ^ 2 := by
  obtain ⟨hp, hnb, hfl', ha, hL, hi, htl, ht, hcols, hζ, hζ1, htags, hslots, hβ, hβ'⟩ := h
  have h2m : 2 * (m + 1) ≤ B := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hB
  have hP1 : P + 1 ≤ B := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hB
  have hLm : 2 ^ d.1.a ≤ m + 1 := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, Nat.log_zero_right, Nat.le_zero] at ha; rw [ha, h0]; simp
    · exact (two_pow_le_of_le_log ha (by omega)).trans (Nat.le_succ _)
  have htiles : d.1.tiles ≤ 2 * (m + 1) := by
    rw [htl, pow_succ]
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) hi
    omega
  have haL := Nat.lt_two_pow_self (n := d.1.a)
  have hiL := Nat.lt_two_pow_self (n := d.1.i)
  have hiL' : 2 ^ d.1.i ≤ 2 ^ d.1.a := Nat.pow_le_pow_right (by norm_num) hi
  have hflB : d.1.fl.length ≤ B := by rw [hfl']; exact hfl
  have hfl1' : ∀ z ∈ d.1.fl, z ≤ 1 := by rw [hfl']; exact hfl1
  have hctx := length_enc_packetCtx_le d.1 (B := B) (by omega) hflB hfl1' (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hcols (hζ.trans hfl) hζ1
  have htg : (encList (encPair encBool encNat) d.2.1).length ≤ B * (2 * (B + 3) + 1) := by
    refine (length_encList_le _ (B := B + 3) fun b hb => ?_).trans
      (Nat.mul_le_mul_right _ (htags ▸ hk))
    rw [length_encPair, encBool_apply, List.length_singleton]
    have := length_encNat_le_of_lt_two_pow (hslots b hb)
    have := Nat.lt_two_pow_self (n := d.1.a)
    omega
  have hbeta : (encList encUnary d.2.2).length ≤ B * (2 * B + 1) := by
    refine (length_encList_le _ (B := B) fun b hb => ?_).trans (Nat.mul_le_mul_right _ ?_)
    · rw [encUnary_apply, List.length_replicate]
      exact (hβ' b hb).trans (hp.trans (by omega))
    · calc d.2.2.length ≤ d.1.tiles * d.1.p := hβ
        _ ≤ 2 * (m + 1) * (P + 1) := Nat.mul_le_mul htiles (hp.trans (Nat.le_succ _))
        _ ≤ B := hB
  rw [length_encSum]
  simp only [Sum.elim_inr, encPacketDesc, length_encPair]
  nlinarith

/-- **The encoded length of a call** is at most `64 (B + 1) ^ 3 + 2 B R` when its scale, depth,
bound, precision, number of edges, number of vertices, modulus length, the binary length of its
rows and its ports are at most `B`, the modulus has 0/1 coefficients, and its descriptors are at
most `R` long. -/
theorem length_encCall_le {x : Call T} {B R : ℕ} (hs : x.scale ≤ B) (hd : x.depth ≤ B)
    (hb : x.bound ≤ B) (hp : x.prec ≤ B) (hfl : x.fl.length ≤ B) (hfl1 : ∀ z ∈ x.fl, z ≤ 1)
    (hr : (encNat x.rows).length ≤ B) (hE : x.edges ≤ B) (hV : x.net.vertices.length ≤ B)
    (hports : ∀ v ∈ x.net.vertices, v.1.length ≤ B ∧ ∀ i ∈ v.1, i ≤ B)
    (hdesc : ∀ v ∈ x.net.vertices, (VertexDesc.enc encT v.2).length ≤ R) :
    (encCall encT x).length ≤ 64 * (B + 1) ^ 3 + 2 * B * R := by
  have h1 := length_encList_le_of_le_one hfl1
  have hv : ∀ v ∈ x.net.vertices, (encPair (encList encNat) (VertexDesc.enc encT) v).length ≤
      2 * (B * (2 * B + 1)) + 1 + R := fun v hv => by
    rw [length_encPair]
    have := (length_encList_le encNat (B := B) fun i hi => length_encNat_le
      ((hports v hv).2 i hi)).trans (Nat.mul_le_mul_right _ (hports v hv).1)
    have := hdesc v hv
    omega
  have hvs := (length_encList_le _ hv).trans (Nat.mul_le_mul_right _ hV)
  simp only [encCall, encParams, length_encPair, encUnary_apply, List.length_replicate,
    DescribedNetwork.encDescribed, encOfEquiv, Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding, DescribedNetwork.equivProd, Equiv.coe_fn_mk] at hvs ⊢
  have h2 : B * (2 * (2 * (B * (2 * B + 1)) + 1 + R) + 1) =
      8 * B ^ 3 + 4 * B ^ 2 + 3 * B + 2 * B * R := by ring
  rw [h2] at hvs
  nlinarith

/-! ### Values -/

/-- A reduced coefficient list: `e` coordinates, each at most `2 ^ p`. -/
@[expose] def ReducedAt (p : ℕ) (fl c : List ℕ) : Prop := c.length = fl.length ∧ ∀ z ∈ c, z ≤ 2 ^ p

theorem reducedAt_add (p : ℕ) (fl c d : List ℕ) : ReducedAt p fl (GaloisRingArith.add p fl c d) :=
  ⟨GaloisRingArith.length_add _ _ _ _, fun _ hz => (GaloisRingArith.lt_of_mem_add hz).le⟩

theorem reducedAt_mul (p : ℕ) (fl c d : List ℕ) : ReducedAt p fl (GaloisRingArith.mul p fl c d) :=
  ⟨GaloisRingArith.length_mul _ _ _ _, fun _ hz => (GaloisRingArith.lt_of_mem_mul hz).le⟩

theorem reducedAt_zero (p : ℕ) (fl : List ℕ) : ReducedAt p fl (GaloisRingArith.zero fl) :=
  (SumOps.galois.reduced_zero (p, fl))

theorem reducedAt_one (p : ℕ) (fl : List ℕ) : ReducedAt p fl (GaloisRingArith.one fl) :=
  (SumOps.galois.reduced_one (p, fl))

/-- A reduced list at precision `p` has encoded length at most `e (2 (p + 1) + 1)`. -/
theorem length_encList_le_of_reducedAt {p : ℕ} {fl c : List ℕ} (h : ReducedAt p fl c) :
    (encList encNat c).length ≤ fl.length * (2 * (p + 1) + 1) := by
  rw [← h.1]
  exact length_encList_le _ fun z hz => length_encNat_le_of_lt_two_pow
    ((h.2 z hz).trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self p)))

/-- **The values of the calls are reduced** at their precision, for every child builder. -/
theorem reducedAt_value (ev : T → List Bool → List ℕ)
    (mk : Call T → ChildCursor.State → ℕ × DescribedNetwork (VertexDesc T))
    (x : Call T) :
    ReducedAt x.prec x.fl (value ev mk x) := by
  cases ha : active x
  · rw [value_of_not_active ev mk ha]
    exact DescribedNetwork.reduced_sumValue (ops := SumOps.galois) (eval := VertexDesc.entry ev)
      (x.prec, x.fl) x.net
  · rw [value_of_active ev mk ha, finishValue, NativeRecovery.recover]
    set W := table x (runLoop x fun c => value ev mk (child x mk c)).2.2
    have hfold : ∀ (l : List ℕ) (S : List ℕ), ReducedAt (x.prec + shift x) x.fl S →
        ReducedAt (x.prec + shift x) x.fl (l.foldl (fun S k => if k = 2 ^ slots x then S else
          GaloisRingArith.add (x.prec + shift x) x.fl S
            (NativeRecovery.nodeTerm (x.prec + shift x) x.fl
            (slots x) (levels x) (step x) (shift x) (points x) k (W.getD k []))) S) := by
      intro l
      induction l with
      | nil => exact fun S hS => hS
      | cons k l ih =>
        intro S hS
        rw [List.foldl_cons]
        refine ih _ ?_
        split_ifs
        · exact hS
        · exact reducedAt_add _ _ _ _
    obtain ⟨hl, hz⟩ := hfold (List.range (2 ^ (slots x + 1))) _ (reducedAt_zero _ _)
    refine ⟨by rw [GaloisRingArith.shiftDown, List.length_map, hl], fun z hzm => ?_⟩
    simp only [GaloisRingArith.shiftDown, List.mem_map] at hzm
    obtain ⟨w, hw, rfl⟩ := hzm
    have := hz w hw
    rw [pow_add] at this
    exact Nat.le_of_lt_succ (Nat.lt_succ_of_le (Nat.div_le_of_le_mul (by linarith)))

/-- **The encoded length of a tagged value** of a call. -/
theorem length_encValue_le (ev : T → List Bool → List ℕ)
    (mk : Call T → ChildCursor.State → ℕ × DescribedNetwork (VertexDesc T))
    (x : Call T) :
    (encValue (x.depth, value ev mk x)).length ≤
      2 * x.depth + 1 + x.fl.length * (2 * (x.prec + 1) + 1) := by
  rw [length_encPair, encUnary_apply, List.length_replicate]
  have := length_encList_le_of_reducedAt (reducedAt_value ev mk x)
  simp only at this ⊢
  omega

/-! ### Frames -/

section Frames

variable {ws : ℕ → List ℕ} {ps : ℕ → ℕ} {N : ℕ} {fl : List ℕ}

/-- An accumulator whose product, sum and stored values are reduced at precision `N`. -/
@[expose] def AccReduced (N : ℕ) (fl : List ℕ) (acc : ChildCursor.Acc (List ℕ)) : Prop :=
  ReducedAt N fl acc.1 ∧ ReducedAt N fl acc.2.1 ∧ ∀ y ∈ acc.2.2, ReducedAt N fl y

/-- **The accumulator stays reduced** along the children, and its stored values only grow. -/
theorem accReduced_runAcc (vals : ChildCursor.State → List ℕ) (l : List ChildCursor.State)
    {acc : ChildCursor.Acc (List ℕ)} (h : AccReduced N fl acc) :
    AccReduced N fl (ChildCursor.runAcc ws ps 64 (GaloisRingArith.mul N fl)
        (GaloisRingArith.add N fl) (GaloisRingArith.one fl) (GaloisRingArith.zero fl) vals l acc) ∧
      acc.2.2.length ≤ (ChildCursor.runAcc ws ps 64 (GaloisRingArith.mul N fl)
        (GaloisRingArith.add N fl) (GaloisRingArith.one fl) (GaloisRingArith.zero fl) vals l
          acc).2.2.length := by
  induction l generalizing acc with
  | nil => exact ⟨h, le_rfl⟩
  | cons s l ih =>
    simp only [ChildCursor.runAcc, List.foldl_cons] at ih ⊢
    have hstep : AccReduced N fl (ChildCursor.absorbAt ws ps 64 (GaloisRingArith.mul N fl)
        (GaloisRingArith.add N fl) (GaloisRingArith.one fl) (GaloisRingArith.zero fl) s acc
          (vals s)) ∧ acc.2.2.length ≤ (ChildCursor.absorbAt ws ps 64 (GaloisRingArith.mul N fl)
        (GaloisRingArith.add N fl) (GaloisRingArith.one fl) (GaloisRingArith.zero fl) s acc
          (vals s)).2.2.length := by
      unfold ChildCursor.absorbAt
      split_ifs
      · exact ⟨⟨reducedAt_mul _ _ _ _, h.2.1, h.2.2⟩, le_rfl⟩
      · refine ⟨⟨reducedAt_one _ _, reducedAt_zero _ _, fun y hy => ?_⟩, by simp⟩
        rcases List.mem_append.mp hy with hy | hy
        · exact h.2.2 y hy
        · rw [List.mem_singleton.mp hy]; exact reducedAt_add _ _ _ _
      · exact ⟨⟨reducedAt_one _ _, reducedAt_add _ _ _ _, h.2.2⟩, le_rfl⟩
    obtain ⟨h1, h2⟩ := ih hstep.1
    exact ⟨h1, hstep.2.trans h2⟩

/-- **The encoded length of a frame** is at most `64 (B + 1) ^ 3` when its cursor state's numbers
and exponents, the number of stored values, `N + 1` and `e` are at most `B`, and its accumulator is
reduced at precision `N`. -/
theorem length_encFrame_le {o : Option ChildCursor.State} {acc : ChildCursor.Acc (List ℕ)}
    {B : ℕ} (hst : ∀ s, o = some s → s.1 ≤ B ∧ s.2.1 ≤ B ∧ s.2.2.1.length ≤ B ∧
      (∀ b ∈ s.2.2.1, b ≤ B) ∧ s.2.2.2 ≤ B)
    (hacc : AccReduced N fl acc) (hst' : acc.2.2.length ≤ B) (hN : N + 1 ≤ B)
    (he : fl.length ≤ B) : (encFrame (o, acc)).length ≤ 64 * (B + 1) ^ 3 := by
  have hred : ∀ c, ReducedAt N fl c → (encList encNat c).length ≤ B * (2 * B + 1) := fun c hc =>
    (length_encList_le_of_reducedAt hc).trans (Nat.mul_le_mul he (by omega))
  have hopt : (encOption ChildCursor.encState o).length ≤ 4 * B ^ 2 + 7 * B + 4 := by
    rcases o with _ | s
    · simp [encOption]
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hst s rfl
      have hβ := (length_encList_le encNat (B := B) fun b hb => length_encNat_le (h4 b hb)).trans
        (Nat.mul_le_mul_right _ h3)
      simp only [encOption, Function.Embedding.coeFn_mk, Option.elim_some, List.length_cons,
        ChildCursor.encState, length_encPair, encUnary_apply, List.length_replicate]
      nlinarith
  have hstored := (length_encList_le (encList encNat) (B := B * (2 * B + 1)) fun y hy =>
    hred y (hacc.2.2 y hy)).trans (Nat.mul_le_mul_right _ hst')
  have h1 := hred _ hacc.1
  have h2 := hred _ hacc.2.1
  simp only [encFrame, length_encPair]
  nlinarith

end Frames

/-! ### The frames of an active call -/

section ActiveFrames

variable {x : Call T}

/-- The bound `256 (m + 1) ^ 5 (p + 1) + e` on the numbers of the frames of an active call at scale
`m` with precision `p`. -/
@[expose] def frameBound (x : Call T) : ℕ := 256 * (x.scale + 1) ^ 5 * (x.prec + 1) + x.fl.length

/-- The numbers of an active call with at most `m` edges at scale `m`. -/
theorem active_numbers (ha : active x = true) (hM : x.edges ≤ x.scale) :
    (nodes x).length ≤ 2 * x.scale ∧ numPoints x ≤ 2 * x.scale ^ 2 + 1 ∧
      (packing x).2.1 ≤ x.scale ^ 2 ∧ shift x ≤ 48 * (x.scale + 1) ^ 4 ∧
      ∀ j, nodePrec x j ≤ x.prec + 40 * x.scale ^ 2 ∧
        2 ^ (level x ((nodes x).getD j 0) + 1) ≤ 4 * x.scale := by
  obtain ⟨haL, h12, hL, huL, hLs, hh⟩ := slots_facts ha
  have ha1 : slots x + 1 ≤ x.scale := by omega
  have hu : levels x ≤ x.scale := by omega
  have hstep : step x ≤ 4 * x.scale := by omega
  have h2a : 2 ^ (slots x + 1) ≤ 2 * x.scale := by rw [pow_succ]; omega
  refine ⟨(length_nodes_le x).trans h2a, ?_, ?_, ?_, fun j => ⟨nodePrec_le_add ha hM j, ?_⟩⟩
  · unfold numPoints
    have : x.edges * (2 * 2 ^ slots x - 1) ≤ x.scale * (2 * x.scale) :=
      Nat.mul_le_mul hM (by omega)
    nlinarith
  · calc (packing x).2.1 ≤ x.edges * (2 ^ slots x) ^ 12 :=
          NativeChild.numPackets_nativeParentPacking_le _ _ _
      _ ≤ x.scale * x.scale := Nat.mul_le_mul hM h12
      _ = x.scale ^ 2 := by ring
  · unfold shift
    have e1 : (slots x + 1) * 2 ^ (slots x + 1) * step x * levels x ≤
        x.scale * (2 * x.scale) * (4 * x.scale) * x.scale :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul ha1 h2a) hstep) hu
    have e2 : 8 * step x * 2 ^ slots x ≤ 8 * (4 * x.scale) * x.scale :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hstep) hL
    have e3 : 8 * x.edges * (slots x + 1) ≤ 8 * x.scale * x.scale :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) ha1
    have h4 : x.scale ^ 4 ≤ (x.scale + 1) ^ 4 := Nat.pow_le_pow_left (Nat.le_succ _) 4
    have h2 : x.scale ^ 2 ≤ (x.scale + 1) ^ 4 :=
      (Nat.pow_le_pow_left (Nat.le_succ _) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have e4 : x.scale * (2 * x.scale) * (4 * x.scale) * x.scale + 8 * (4 * x.scale) * x.scale +
        8 * x.scale * x.scale = 8 * x.scale ^ 4 + 40 * x.scale ^ 2 := by ring
    omega
  · have : level x ((nodes x).getD j 0) ≤ slots x + 1 := by
      unfold level NativeRecovery.twoVal
      split_ifs
      · omega
      · exact (List.length_filter_le _ _).trans List.length_range.le
    calc 2 ^ (level x ((nodes x).getD j 0) + 1) ≤ 2 ^ (slots x + 1 + 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 4 * x.scale := by rw [pow_succ]; omega

/-- The exponent tuple of a child of an active call is a tuple of weight below its node's
precision. -/
theorem mem_budgetTuples_of_mem_children {c : ChildCursor.State} (hc : c ∈ children x) :
    c.2.2.1 ∈ BudgetTuples.budgetTuples (weights x c.1) (nodePrec x c.1) := by
  simp only [children, ChildCursor.cursorList, ChildCursor.nodeBlock, ChildCursor.pointBlock,
    ChildCursor.groupBlock, List.mem_flatMap, List.mem_range, List.mem_map] at hc
  obtain ⟨j, -, i, -, β, hβ, g, -, rfl⟩ := hc
  exact hβ

/-- **The frames of an active call** with at most `m` edges at scale `m` have encoded length at
most `64 (B + 1) ^ 3` for `B = frameBound x`. -/
theorem length_encFrame_frameAt_le (ha : active x = true) (hM : x.edges ≤ x.scale)
    (vals : ChildCursor.State → List ℕ) (c : ℕ) :
    (encFrame (frameAt x vals c)).length ≤ 64 * (frameBound x + 1) ^ 3 := by
  obtain ⟨hT, hn, hP, hsh, hj⟩ := active_numbers ha hM
  have hM1 := one_le_edges_of_active ha
  set m := x.scale with hm
  set p := x.prec with hp
  have hBf : 256 * ((m + 1) ^ 5 * (p + 1)) ≤ frameBound x := by
    rw [← Nat.mul_assoc]; exact Nat.le_add_right _ _
  have hm5 : 1 ≤ (m + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hm1 : m + 1 ≤ (m + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
  have hm2 : (m + 1) ^ 2 ≤ (m + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hm3 : (m + 1) ^ 3 ≤ (m + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hm4 : (m + 1) ^ 4 ≤ (m + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hsq : m ^ 2 ≤ (m + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ _) 2
  have hcu : m ^ 3 ≤ (m + 1) ^ 3 := Nat.pow_le_pow_left (Nat.le_succ _) 3
  have hP5 : (m + 1) ^ 5 ≤ (m + 1) ^ 5 * (p + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hpq : p + 1 ≤ (m + 1) ^ 5 * (p + 1) := Nat.le_mul_of_pos_left _ (by omega)
  -- The stored values.
  obtain ⟨qs, hqs, hrun⟩ := ChildCursor.runAcc_cursorList (ws := weights x) (ps := nodePrec x)
    (T := (nodes x).length) (n := numPoints x) (r := 64) (GaloisRingArith.mul (wide x) x.fl)
    (GaloisRingArith.add (wide x) x.fl) (GaloisRingArith.one x.fl) (GaloisRingArith.zero x.fl)
    (GaloisRingArith.val (wide x) x.fl) (fun a b => GaloisRingArith.val_mul a b)
    (fun a b => GaloisRingArith.val_add a b) GaloisRingArith.val_one GaloisRingArith.val_zero
    (by norm_num) (nodePrec_pos hM1) weights_pos vals
  have hqlen : qs.length = (nodes x).length * numPoints x := by
    have := congrArg List.length hqs
    simpa [List.length_flatMap, List.sum_replicate] using this
  have hinit : AccReduced (wide x) x.fl (GaloisRingArith.one x.fl, GaloisRingArith.zero x.fl, []) :=
    ⟨reducedAt_one _ _, reducedAt_zero _ _, by simp⟩
  have hpre := accReduced_runAcc (ws := weights x) (ps := nodePrec x) vals
    ((children x).take c) hinit
  have hsuf := accReduced_runAcc (ws := weights x) (ps := nodePrec x) vals
    ((children x).drop c) hpre.1
  have hfull : ChildCursor.runAcc (weights x) (nodePrec x) 64
      (GaloisRingArith.mul (wide x) x.fl) (GaloisRingArith.add (wide x) x.fl)
      (GaloisRingArith.one x.fl) (GaloisRingArith.zero x.fl) vals (children x)
      (GaloisRingArith.one x.fl, GaloisRingArith.zero x.fl, []) =
      (GaloisRingArith.one x.fl, GaloisRingArith.zero x.fl, qs) := by
    rw [children]; exact hrun
  rw [← ChildCursor.runAcc_append, List.take_append_drop, hfull] at hsuf
  have hstored : (ChildCursor.runAcc (weights x) (nodePrec x) 64
      (GaloisRingArith.mul (wide x) x.fl) (GaloisRingArith.add (wide x) x.fl)
      (GaloisRingArith.one x.fl) (GaloisRingArith.zero x.fl) vals ((children x).take c)
      (GaloisRingArith.one x.fl, GaloisRingArith.zero x.fl, [])).2.2.length ≤ frameBound x := by
    refine hsuf.2.trans ?_
    rw [hqlen]
    have : (nodes x).length * numPoints x ≤ 2 * m * (2 * m ^ 2 + 1) := Nat.mul_le_mul hT hn
    have : 2 * m * (2 * m ^ 2 + 1) = 4 * m ^ 3 + 2 * m := by ring
    omega
  refine length_encFrame_le (N := wide x) (fl := x.fl) (fun s hs => ?_) hpre.1 hstored ?_
    (Nat.le_add_left _ _)
  · have hsm : s ∈ children x := List.mem_of_getElem? hs
    obtain ⟨hj1, hi1, hg1⟩ := lt_of_mem_children hsm
    have hβ := mem_budgetTuples_of_mem_children hsm
    have hlen := ((BudgetTuples.mem_budgetTuples (weights_pos _)).mp hβ).1
    obtain ⟨hpj, hlj⟩ := hj s.1
    refine ⟨by omega, by omega, ?_, fun b hb => ?_, by omega⟩
    · rw [hlen, weights, NativeChild.modeWeights, List.length_map, List.length_range]
      have h1 : (packing x).2.1 * (2 ^ (level x ((nodes x).getD s.1 0) + 1) * nodePrec x s.1) ≤
          m ^ 2 * (4 * m * (p + 40 * m ^ 2)) :=
        Nat.mul_le_mul hP (Nat.mul_le_mul hlj hpj)
      have h2 : m ^ 2 * (4 * m * (p + 40 * m ^ 2)) = 4 * (m ^ 3 * p) + 160 * m ^ 5 := by ring
      have h3 : m ^ 5 ≤ (m + 1) ^ 5 := Nat.pow_le_pow_left (Nat.le_succ _) 5
      have h4 : m ^ 3 * p ≤ (m + 1) ^ 5 * (p + 1) :=
        Nat.mul_le_mul (hcu.trans hm3) (Nat.le_succ _)
      omega
    · have := BudgetTuples.lt_of_mem_budgetTuples (weights_pos _) hβ hb
      have : m ^ 2 ≤ (m + 1) ^ 5 := hsq.trans hm2
      omega
  · unfold wide
    omega

end ActiveFrames

/-! ### The sizes along the recursion -/

section Sizes

variable {x₀ x : Call T}

/-- **The sizes of a call of a given shape**: from a root `x₀` at depth `0`, at scale its number
`m` of edges, with bound `m + 1`, a 0/1 modulus and descriptors at most `200 (Z + 1) ^ 2` long, a
call of its shape, its tagged value and, if it is active, its frames are at most
`1000 (Z + 1) ^ 3` long, once `Z` dominates `256 (m + 1) ^ 5 (P + 1) + e` for the precision bound
`P = p₀ + 40 m² (m + 1)` and the vertices, rows and their growth. -/
theorem Shape.length_le (ev : T → List Bool → List ℕ) (h₀s : x₀.scale = x₀.edges)
    (h₀b : x₀.bound = x₀.edges + 1)
    (h₀d : x₀.depth = 0) (h : Shape x₀ x) {Z : ℕ}
    (hZ1 : 256 * (x₀.edges + 1) ^ 5 * (x₀.prec + (x₀.edges + 1) * (40 * x₀.edges ^ 2) + 1) +
      x₀.fl.length ≤ Z)
    (hZ2 : x₀.net.vertices.length + (x₀.edges + 1) * x₀.edges ^ 2 + (encNat x₀.rows).length ≤ Z)
    (hfl1 : ∀ z ∈ x₀.fl, z ≤ 1)
    (hR₀ : ∀ w ∈ x₀.net.vertices, (VertexDesc.enc encT w.2).length ≤ 200 * (Z + 1) ^ 2) :
    (encCall encT x).length ≤ 1000 * (Z + 1) ^ 3 ∧
      (encValue (x.depth, value ev nativeMk x)).length ≤ 1000 * (Z + 1) ^ 3 ∧
      (active x = true → ∀ vals c,
        (encPair (encCall encT) encFrame (x, frameAt x vals c)).length ≤ 1000 * (Z + 1) ^ 3) := by
  set m := x₀.edges with hm
  set P := x₀.prec + (m + 1) * (40 * m ^ 2) with hP
  -- The numbers of `x`.
  have hbd := h.bound_add_depth_le
  rw [h₀b, h₀d] at hbd
  have hd : x.depth ≤ m + 1 := by omega
  have hprec : x.prec ≤ P := h.prec_le.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ hd) _)
  have hV : x.net.vertices.length ≤ x₀.net.vertices.length + (m + 1) * m ^ 2 :=
    h.vertices_le.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _)
  have hm5 : m + 1 ≤ (m + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
  have hP1 : P + 1 ≤ (m + 1) ^ 5 * (P + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  have hmP : 2 * (m + 1) * (P + 1) ≤ 256 * (m + 1) ^ 5 * (P + 1) := by
    have : (m + 1) * (P + 1) ≤ (m + 1) ^ 5 * (P + 1) := Nat.mul_le_mul_right _ hm5
    nlinarith
  have hmZ : 2 * (m + 1) ≤ Z := by
    have : 2 * (m + 1) ≤ 2 * (m + 1) * (P + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hPZ : P + 1 ≤ Z := by
    have : P + 1 ≤ 2 * (m + 1) * (P + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hflZ : x₀.fl.length ≤ Z := by omega
  have hsc : x.scale = m := h.scale_eq.trans h₀s
  have hE : x.edges ≤ 2 * m := h.edges_le
  have hports : ∀ v ∈ x.net.vertices, v.1.length ≤ Z ∧ ∀ i ∈ v.1, i ≤ Z := fun v hv =>
    ⟨(length_le_edges_of_wf h.wf hv).trans (hE.trans (by omega)),
      fun i hi => (h.wf.2.1 v hv i hi).le.trans (hE.trans (by omega))⟩
  have hR : ∀ v ∈ x.net.vertices, (VertexDesc.enc encT v.2).length ≤ 200 * (Z + 1) ^ 2 := by
    intro v hv
    rcases h.desc v hv with ⟨w, hw, hvw⟩ | ⟨d, hvd, hb⟩
    · rw [hvw]; exact hR₀ w hw
    · rw [hvd]
      refine length_enc_inr_le (hb.mono (Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _))
        (show 2 * (m + 1) * (P + 1) ≤ Z by omega) hflZ hfl1 (hports v hv).1
  have hrows : (encNat x.rows).length ≤ Z := by
    rcases h.rows_le with rfl | hr
    · omega
    · exact (length_encNat_le (hr.trans (Nat.add_le_add_left
        (Nat.mul_le_mul_right _ hd) _))).trans
        (show x₀.net.vertices.length + (m + 1) * m ^ 2 ≤ Z by omega)
  have hcall := length_encCall_le (B := Z) (R := 200 * (Z + 1) ^ 2) (x := x)
    (by rw [hsc]; omega) (hd.trans (by omega)) (by omega) (hprec.trans (by omega))
    (h.fl_eq ▸ hflZ) (h.fl_eq ▸ hfl1) hrows (hE.trans (by omega)) (hV.trans (by omega)) hports hR
  have hcall' : (encCall encT x).length ≤ 464 * (Z + 1) ^ 3 := by
    have : 2 * Z * (200 * (Z + 1) ^ 2) ≤ 400 * (Z + 1) ^ 3 := by
      have : Z ≤ Z + 1 := Nat.le_succ _
      calc 2 * Z * (200 * (Z + 1) ^ 2) = 400 * (Z * (Z + 1) ^ 2) := by ring
        _ ≤ 400 * ((Z + 1) * (Z + 1) ^ 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ this)
        _ = 400 * (Z + 1) ^ 3 := by ring
    omega
  have hZ3 : (Z + 1) ^ 2 ≤ (Z + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hZ1' : Z + 1 ≤ (Z + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  refine ⟨hcall'.trans (by omega), ?_, fun ha vals c => ?_⟩
  · have hv := length_encValue_le ev nativeMk x
    rw [h.fl_eq] at hv
    have : x₀.fl.length * (2 * (x.prec + 1) + 1) ≤ Z * (2 * Z + 1) :=
      Nat.mul_le_mul hflZ (by omega)
    have : Z * (2 * Z + 1) ≤ 3 * (Z + 1) ^ 2 := by nlinarith
    omega
  · have hM : x.edges ≤ x.scale := by
      have := edges_lt_bound_of_active ha
      omega
    have hf := length_encFrame_frameAt_le ha hM vals c
    have hfb : frameBound x ≤ Z := by
      unfold frameBound
      rw [hsc, h.fl_eq]
      have : 256 * (m + 1) ^ 5 * (x.prec + 1) ≤ 256 * (m + 1) ^ 5 * (P + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have hfZ : (frameBound x + 1) ^ 3 ≤ (Z + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hl := length_encPair (enc₁ := encCall encT) (enc₂ := encFrame) (x, frameAt x vals c)
    simp only at hl
    rw [hl]
    omega

end Sizes

end Cslib.Circuits.Frontier.FastContraction
