/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionShape
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.GetD

/-!
# The encoded sizes of the calls of the native contraction recursion

Bounds on the encoded lengths of the calls (`FastContraction.encCall`) of the native recursion
from bounds on their numbers: the length of an encoded call is at most `64 (B + 1) ^ 3 + 2 B R` when
its numbers, lists and ports are at most `B` and its descriptors at most `R` long
(`FastContraction.length_encCall_le`), and a bounded packet descriptor is at most
`200 (B + 1) ^ 2` long (`FastContraction.length_enc_inr_le`).

## Main results

* `Cslib.Circuits.Frontier.FastContraction.length_encList_le`: lists of bounded elements.
* `Cslib.Circuits.Frontier.FastContraction.length_enc_packetCtx_le`: packet contexts.
* `Cslib.Circuits.Frontier.FastContraction.length_enc_inr_le`: bounded packet descriptors.
* `Cslib.Circuits.Frontier.FastContraction.length_encCall_le`: calls.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction

open Turing.MultiTapeTM NativePacket

/-- A number at most `b` has at most `b` binary digits. -/
theorem length_encNat_le {a b : ℕ} (h : a ≤ b) : (encNat a).length ≤ b := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (h.trans_lt Nat.lt_two_pow_self)

/-- A number below `2 ^ p` has at most `p` binary digits. -/
theorem length_encNat_le_of_lt_two_pow {a p : ℕ} (h : a < 2 ^ p) : (encNat a).length ≤ p := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le.mpr h

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
    (hk : k ≤ B) : (VertexDesc.enc (.inr d)).length ≤ 200 * (B + 1) ^ 2 := by
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
theorem length_encCall_le {x : Call} {B R : ℕ} (hs : x.scale ≤ B) (hd : x.depth ≤ B)
    (hb : x.bound ≤ B) (hp : x.prec ≤ B) (hfl : x.fl.length ≤ B) (hfl1 : ∀ z ∈ x.fl, z ≤ 1)
    (hr : (encNat x.rows).length ≤ B) (hE : x.edges ≤ B) (hV : x.net.vertices.length ≤ B)
    (hports : ∀ v ∈ x.net.vertices, v.1.length ≤ B ∧ ∀ i ∈ v.1, i ≤ B)
    (hdesc : ∀ v ∈ x.net.vertices, (VertexDesc.enc v.2).length ≤ R) :
    (encCall x).length ≤ 64 * (B + 1) ^ 3 + 2 * B * R := by
  have h1 := length_encList_le_of_le_one hfl1
  have hv : ∀ v ∈ x.net.vertices, (encPair (encList encNat) VertexDesc.enc v).length ≤
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
theorem reducedAt_value (mk : Call → ChildCursor.State → ℕ × DescribedNetwork VertexDesc) (x : Call) :
    ReducedAt x.prec x.fl (value mk x) := by
  cases ha : active x
  · rw [value_of_not_active mk ha]
    exact DescribedNetwork.reduced_sumValue (ops := SumOps.galois) (eval := VertexDesc.entry)
      (x.prec, x.fl) x.net
  · rw [value_of_active mk ha, finishValue, NativeRecovery.recover]
    set W := table x (runLoop x fun c => value mk (child x mk c)).2.2
    have hfold : ∀ (l : List ℕ) (S : List ℕ), ReducedAt (x.prec + shift x) x.fl S →
        ReducedAt (x.prec + shift x) x.fl (l.foldl (fun S k => if k = 2 ^ slots x then S else
          GaloisRingArith.add (x.prec + shift x) x.fl S (NativeRecovery.nodeTerm (x.prec + shift x) x.fl
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
theorem length_encValue_le (mk : Call → ChildCursor.State → ℕ × DescribedNetwork VertexDesc) (x : Call) :
    (encValue (x.depth, value mk x)).length ≤
      2 * x.depth + 1 + x.fl.length * (2 * (x.prec + 1) + 1) := by
  rw [length_encPair, encUnary_apply, List.length_replicate]
  have := length_encList_le_of_reducedAt (reducedAt_value mk x)
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

end Cslib.Circuits.Frontier.FastContraction
