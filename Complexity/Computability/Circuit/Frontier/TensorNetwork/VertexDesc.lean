/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.PacketTerms
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Foundations.Data.BitString.Binary
import Mathlib.Data.List.GetD

/-!
# Descriptors of the vertices of the recursion's networks

The networks of the contraction recursion of [OpenAI2026ETH] (§D.4.6–§D.4.7, pp. 63–64) have two
kinds of vertices. The vertices of the input network keep their tables, and they survive into
every child of their group with the same ports. The packet vertices created at a call are
described by "its packet data, the tuple `β`, the interpolation value, and the creation
precision" (p. 63), and from then on they also survive into the children of their group. A
vertex descriptor (`VertexDesc`) is therefore a table or a packet descriptor
(`NativePacket.PacketDesc`), and a retained vertex keeps its descriptor.

`VertexDesc.entry` evaluates a descriptor at the bits on its ports: the table entry, as a constant
coefficient list, or the native packet entry at the packet's creation precision. A network of the
recursion reads the entries at its own precision `(p, fl)` (`GaloisRingArith.val p fl`), so a
retained packet vertex created at a lower precision is read at the higher one: its coefficients
are those of the same element of `O = ℤ_(2)[U] / (f)`. One native machine evaluates every
descriptor (`VertexDesc.entryCertificate`), with the packet evaluator's bounds: time
`K (m + 2) ^ L Z ^ K` and space `K Z ^ K`, for `m` target modes and `L` row ports of a packet (none
for a table) and `Z` polynomial in the input and the reduced coefficient lists
(`VertexDesc.entryCertificate_le`). It is the evaluator of direct summation over networks of
descriptors at coefficient lists (`DescribedNetwork.contractionCertificate` at `SumOps.galois`).

## Main definitions

* `Cslib.Circuits.Frontier.VertexDesc`: a table or a packet descriptor.
* `Cslib.Circuits.Frontier.VertexDesc.entry`: its entry at the bits on its ports.
* `Cslib.Circuits.Frontier.VertexDesc.enc`: its encoding.
* `Cslib.Circuits.Frontier.VertexDesc.entryCertificate`: the native evaluator.

## Main results

* `Cslib.Circuits.Frontier.VertexDesc.val_entry_inl`: a table entry is read as a constant.
* `Cslib.Circuits.Frontier.VertexDesc.map_val_entry_inr`: a packet entry is the packet entry in
  every ring receiving `A_p` with `2` nilpotent.
* `Cslib.Circuits.Frontier.VertexDesc.entryCertificate_le`: the time and space of the evaluator.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.6–§D.4.7, pp. 63–64.
-/

public section

namespace Cslib.Circuits.Frontier

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

open GaloisRingArith NativePacket TensorNetwork Turing.MultiTapeTM Cslib.GenericRAM

/-- **The descriptor of a vertex** of a network of the contraction recursion: the table of a
vertex of the input network (`inl`), or the descriptor of a packet vertex (`inr`). -/
abbrev VertexDesc : Type := List ℕ ⊕ PacketDesc

namespace VertexDesc

/-- **The entry of a vertex at the bits on its ports**: the table entry, as a constant coefficient
list, or the native packet entry at the packet's creation precision. -/
@[expose] def entry : VertexDesc → List Bool → List ℕ
  | .inl table, bs => [ExplicitTensorNetwork.entry table bs]
  | .inr d, bs => packetVertexEntry d bs

/-- The encoding of a descriptor: a tag, then the table in binary or the packet descriptor. -/
abbrev enc : VertexDesc ↪ List Bool := encSum (encList encNat) encPacketDesc

/-- The number of target modes of a descriptor: those of its packet, and none for a table. -/
@[expose] def modes : VertexDesc → ℕ
  | .inl _ => 0
  | .inr d => (targetModes d.1).length

/-- The number of row ports of a descriptor at the bits on its ports: those of its packet, and
none for a table. -/
@[expose] def rowPorts : VertexDesc → List Bool → ℕ
  | .inl _, _ => 0
  | .inr d, bs => (sidePorts d.2.1 bs true).length

/-- The reduced coefficient lists of the creation precision of a descriptor are at most `Rv` bits
long; no condition for a table. -/
@[expose] def ReducedLE (Rv : ℕ) : VertexDesc → Prop
  | .inl _ => True
  | .inr d => ∀ y, SumOps.galois.Reduced (d.1.p, d.1.fl) y → (encList encNat y).length ≤ Rv

/-! ### Values -/

@[simp] theorem entry_inl (table : List ℕ) (bs : List Bool) :
    entry (.inl table) bs = [ExplicitTensorNetwork.entry table bs] := rfl

@[simp] theorem entry_inr (d : PacketDesc) (bs : List Bool) :
    entry (.inr d) bs = packetVertexEntry d bs := rfl

/-- **A table entry is read as a constant** at every precision. -/
theorem val_entry_inl (p : ℕ) (fl table : List ℕ) (bs : List Bool) :
    val p fl (entry (.inl table) bs) =
      ((ExplicitTensorNetwork.entry table bs : ℕ) : Ring p fl) := by
  obtain h | ⟨e, he⟩ : fl.length = 0 ∨ ∃ e, fl.length = e + 1 :=
    (Nat.eq_zero_or_pos _).imp id fun h => ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
  · have := subsingleton_of_length_eq_zero (p := p) h
    exact Subsingleton.elim _ _
  · rw [entry_inl, val, he, Finset.sum_range_succ',
      Finset.sum_eq_zero fun i _ => by rw [List.getD_cons_succ, List.getD_nil]; simp]
    simp

/-- **A packet entry in every ring receiving `A_p`.** Along a ring map `ψ` from `A_p`, at the
precision `p` of the packet, to a ring in which `2` is nilpotent, the entry of a packet descriptor
at the bits on its ports is `packetEntry` at any ring map `κ : ℤ_(2) → S`, the image of the
interpolation value, the dense exponents, and the row and column ports read from the bits. -/
theorem map_val_entry_inr {S : Type*} [CommRing S] (d : PacketDesc) (bs : List Bool)
    (ψ : Ring d.1.p d.1.fl →+* S) {n : ℕ} (hn : (2 : S) ^ n = 0) (κ : ℤ₍₂₎ →+* S)
    (hL : d.1.L = 2 ^ d.1.a) (hia : d.1.i < d.1.a) (htiles : d.1.tiles = 2 ^ (d.1.i + 1))
    (ht : d.1.t ∈ cauchyGrid (2 ^ d.1.a)) (hti : (2 : ℤ) ^ d.1.i ∣ d.1.t)
    (hti' : ¬ (2 : ℤ) ^ (d.1.i + 1) ∣ d.1.t) (hports : ∀ x ∈ d.2.1, x.2 < 2 ^ d.1.a) :
    ψ (val d.1.p d.1.fl (entry (.inr d) bs)) =
      packetEntry (p := d.1.nb) κ (ψ (val d.1.p d.1.fl d.1.ζ)) d.1.a d.1.i d.1.t d.1.e₁ d.1.e₂
        d.1.differ (fun Z => d.2.2.getD (finProdFinEquiv Z) 0) (sidePorts d.2.1 bs true)
        (sidePorts d.2.1 bs false) := by
  have hside (side : Bool) : ∀ r ∈ sidePorts d.2.1 bs side, r.1 < 2 ^ d.1.a := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    have hj' := List.mem_range.mp (List.mem_filter.mp hj).1
    exact hports _ (by rw [List.getD_eq_getElem _ _ hj']; exact List.getElem_mem _)
  exact map_val_packetEntryNative { d.1 with cols := sidePorts d.2.1 bs false } ψ hn κ hL hia
    htiles ht hti hti' (hside true) (hside false) d.2.2

/-- A packet entry is a reduced coefficient list at the packet's precision. -/
theorem reduced_entry_inr (d : PacketDesc) (bs : List Bool) :
    SumOps.galois.Reduced (d.1.p, d.1.fl) (entry (.inr d) bs) :=
  SumOps.galois.reduced_mul (d.1.p, d.1.fl) _ _

/-! ### The native evaluator -/

/-- The right summand of a descriptor and its bits. -/
theorem getRight_polyTime :
    ComputableInPolyTime (fun q : VertexDesc × List Bool => q.1.getRight?) (encPair enc encBits)
      (encOption encPacketDesc) :=
  (ComputableInO.getRight?_deg _ _).computableInPolyTime.comp (ComputableInPolyTime.fst _ _)

/-- The table entry of a descriptor at its bits, the empty table standing for a packet, as a
singleton list. -/
theorem tableEntry_polyTime :
    ComputableInPolyTime (fun q : VertexDesc × List Bool =>
      [ExplicitTensorNetwork.entry (q.1.getLeft?.getD []) q.2]) (encPair enc encBits)
      (encList encNat) := by
  have hleft : ComputableInPolyTime (fun q : VertexDesc × List Bool => q.1.getLeft?)
      (encPair enc encBits) (encOption (encList encNat)) :=
    (ComputableInO.getLeft?_deg _ _).computableInPolyTime.comp (ComputableInPolyTime.fst _ _)
  have htable : ComputableInPolyTime (fun q : VertexDesc × List Bool => q.1.getLeft?.getD [])
      (encPair enc encBits) (encList encNat) :=
    (ComputableInDegree.getD (enc₁ := encList encNat) (enc := encOption (encList encNat))
      []).computableInPolyTime.comp hleft
  have hindex := ComputableInPolyTime.bitsBinaryValue.comp
    (ComputableInPolyTime.bitsReverse.comp (ComputableInPolyTime.snd enc encBits))
  have hentry := ComputableInPolyTime.listGetD_binary (encA := encNat) (encL := encList encNat) 0
    htable hindex
  exact (ComputableInPolyTime.cons' hentry (ComputableInPolyTime.const [])).of_enc_eq fun q => by
    simp only [ExplicitTensorNetwork.entry, BitString.lsbValue_eq_binaryValue_reverse,
      Function.comp_apply]

/-- The input of the packet evaluator from a descriptor's bits and its packet. -/
theorem packetInput_polyTime :
    ComputableInPolyTime (fun p : (VertexDesc × List Bool) × PacketDesc => (p.2, p.1.2))
      (encPair (encPair enc encBits) encPacketDesc) (encPair encPacketDesc encBits) :=
  (ComputableInPolyTime.snd _ _).prod
    ((ComputableInPolyTime.snd enc encBits).comp (ComputableInPolyTime.fst _ _))

/-- **One native machine for the entries of all descriptors**: the table lookup for a table, and
the native packet evaluator (`NativePacket.vertexCertificate`) for a packet. -/
noncomputable def entryCertificate :
    NativeCertificate (fun q : VertexDesc × List Bool => entry q.1 q.2) (encPair enc encBits)
      (encList encNat) :=
  (NativeCertificate.option (value := fun q : VertexDesc × List Bool => q.1.getRight?)
    (fallback := fun q => [ExplicitTensorNetwork.entry (q.1.getLeft?.getD []) q.2])
    (body := fun p => packetVertexEntry p.2 p.1.2)
    (NativeCertificate.ofPolyTime getRight_polyTime)
    (NativeCertificate.ofPolyTime tableEntry_polyTime)
    ((vertexCertificate.comp (NativeCertificate.ofPolyTime packetInput_polyTime)).congr
      fun _ => rfl)).congr fun q => by
    rcases q with ⟨d | d, bs⟩ <;> rfl

/-- `c (y + 1) ^ d ≤ c Z ^ D` when `y + 1 ≤ Z` and `d ≤ D`. -/
private theorem mul_pow_le_mul_pow {c y d Z D : ℕ} (hy : y + 1 ≤ Z) (hd : d ≤ D) :
    c * (y + 1) ^ d ≤ c * Z ^ D :=
  Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hy _).trans
    (Nat.pow_le_pow_right (by omega) hd))

/-- **The resources of the native evaluator of descriptors.** There is `K` such that on a
descriptor and bits of total length `n`, with `m` target modes and `L` row ports (`0` and `0` for a
table), if the reduced coefficient lists of a packet's precision are at most `Rv` bits long, then
with `Z = n + m + Rv + 2` the time is at most `K (m + 2) ^ L Z ^ K` and the space at most
`K Z ^ K`. -/
theorem entryCertificate_le :
    ∃ K : ℕ, ∀ (q : VertexDesc × List Bool) (Rv : ℕ), q.1.ReducedLE Rv →
      entryCertificate.time q ≤ K * (q.1.modes + 2) ^ q.1.rowPorts q.2 *
          ((encPair enc encBits q).length + q.1.modes + Rv + 2) ^ K ∧
        entryCertificate.space q ≤
          K * ((encPair enc encBits q).length + q.1.modes + Rv + 2) ^ K := by
  obtain ⟨K₀, hK₀⟩ := vertexCertificate_le
  have hR := NativeCertificate.ofPolyTime_isPolynomial getRight_polyTime
  have hT := NativeCertificate.ofPolyTime_isPolynomial tableEntry_polyTime
  have hI := NativeCertificate.ofPolyTime_isPolynomial packetInput_polyTime
  obtain ⟨cr, dr, hrt⟩ := hR.1.exists_le
  obtain ⟨cr', dr', hrs⟩ := hR.2.exists_le
  obtain ⟨ct, dt, htt⟩ := hT.1.exists_le
  obtain ⟨ct', dt', hts⟩ := hT.2.exists_le
  obtain ⟨ci, di, hit⟩ := hI.1.exists_le
  obtain ⟨ci', di', his⟩ := hI.2.exists_le
  obtain ⟨D, hD⟩ : ∃ D, D = K₀ + dr + dr' + dt + dt' + di + di' + 1 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = K₀ + 2 * cr + 2 * cr' + ct + ct' + ci * 3 ^ di + ci' * 3 ^ di' + 1 :=
    ⟨_, rfl⟩
  refine ⟨G + D, fun q Rv hRv => ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, n = (encPair enc encBits q).length := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = n + q.1.modes + Rv + 2 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = (q.1.modes + 2) ^ q.1.rowPorts q.2 := ⟨_, rfl⟩
  rw [← hn, ← hZ, ← hP]
  have hP1 : 1 ≤ P := hP ▸ Nat.one_le_pow _ _ (by omega)
  have hnZ : n + 1 ≤ Z := by omega
  have hZD : Z ^ D ≤ Z ^ (G + D) := Nat.pow_le_pow_right (by omega) (by omega)
  have hnD : n ≤ Z ^ D := by
    calc n ≤ Z := by omega
      _ = Z ^ 1 := (pow_one Z).symm
      _ ≤ Z ^ D := Nat.pow_le_pow_right (by omega) (by omega)
  have hrt' : (NativeCertificate.ofPolyTime getRight_polyTime).time q ≤ cr * Z ^ D :=
    (hrt q).trans (hn ▸ mul_pow_le_mul_pow hnZ (by omega))
  have hrs' : (NativeCertificate.ofPolyTime getRight_polyTime).space q ≤ cr' * Z ^ D :=
    (hrs q).trans (hn ▸ mul_pow_le_mul_pow hnZ (by omega))
  rcases q with ⟨d | d, bs⟩
  · -- A table: the lookup alone.
    have htt' : (NativeCertificate.ofPolyTime tableEntry_polyTime).time (.inl d, bs) ≤
        ct * Z ^ D := (htt _).trans (hn ▸ mul_pow_le_mul_pow hnZ (by omega))
    have hts' : (NativeCertificate.ofPolyTime tableEntry_polyTime).space (.inl d, bs) ≤
        ct' * Z ^ D := (hts _).trans (hn ▸ mul_pow_le_mul_pow hnZ (by omega))
    have htime : entryCertificate.time (.inl d, bs) =
        2 * (NativeCertificate.ofPolyTime getRight_polyTime).time (.inl d, bs) + n +
          (NativeCertificate.ofPolyTime tableEntry_polyTime).time (.inl d, bs) := by
      rw [hn]; rfl
    have hspace : entryCertificate.space (.inl d, bs) =
        2 * (NativeCertificate.ofPolyTime getRight_polyTime).space (.inl d, bs) + n +
          (NativeCertificate.ofPolyTime tableEntry_polyTime).space (.inl d, bs) := by
      rw [hn]; rfl
    constructor
    · rw [htime]
      calc _ ≤ G * Z ^ D := by
            have : (2 * cr + 1 + ct) * Z ^ D ≤ G * Z ^ D := Nat.mul_le_mul_right _ (by omega)
            have e : (2 * cr + 1 + ct) * Z ^ D = 2 * (cr * Z ^ D) + Z ^ D + ct * Z ^ D := by ring
            omega
        _ ≤ (G + D) * P * Z ^ (G + D) :=
            Nat.mul_le_mul ((Nat.le_add_right G D).trans (Nat.le_mul_of_pos_right _ hP1)) hZD
    · rw [hspace]
      calc _ ≤ G * Z ^ D := by
            have : (2 * cr' + 1 + ct') * Z ^ D ≤ G * Z ^ D := Nat.mul_le_mul_right _ (by omega)
            have e : (2 * cr' + 1 + ct') * Z ^ D = 2 * (cr' * Z ^ D) + Z ^ D + ct' * Z ^ D := by
              ring
            omega
        _ ≤ (G + D) * Z ^ (G + D) := Nat.mul_le_mul (by omega) hZD
  · -- A packet: the input of the packet evaluator, then the evaluator.
    have hn' : n = 2 * ((encPacketDesc d).length + 1) + 1 + (encBits bs).length := by
      rw [hn]; exact length_encPair _
    have hlen : (encPair encPacketDesc encBits (d, bs)).length ≤ n := by
      have h3 : (encPair encPacketDesc encBits (d, bs)).length =
          2 * (encPacketDesc d).length + 1 + (encBits bs).length := length_encPair _
      omega
    have hlenI : (encPair (encPair enc encBits) encPacketDesc ((.inr d, bs), d)).length + 1 ≤
        3 * Z := by
      have h1 : (encPair (encPair enc encBits) encPacketDesc ((.inr d, bs), d)).length =
          2 * (encPair enc encBits (.inr d, bs)).length + 1 + (encPacketDesc d).length :=
        length_encPair _
      omega
    have hpow3 {c e : ℕ} (he : e ≤ D) : c * (3 * Z) ^ e ≤ c * 3 ^ e * Z ^ D := by
      rw [Nat.mul_pow, ← Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) he)
    have hit' : (NativeCertificate.ofPolyTime packetInput_polyTime).time ((.inr d, bs), d) ≤
        ci * 3 ^ di * Z ^ D :=
      (hit _).trans ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlenI _)).trans
        (hpow3 (by omega)))
    have his' : (NativeCertificate.ofPolyTime packetInput_polyTime).space ((.inr d, bs), d) ≤
        ci' * 3 ^ di' * Z ^ D :=
      (his _).trans ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlenI _)).trans
        (hpow3 (by omega)))
    obtain ⟨hvt, hvs⟩ := hK₀ (d, bs) Rv hRv
    have hZ' : (encPair encPacketDesc encBits (d, bs)).length + (targetModes d.1).length + Rv + 2
        ≤ Z := by rw [hZ]; simp only [modes]; omega
    have hpowK : ((encPair encPacketDesc encBits (d, bs)).length + (targetModes d.1).length + Rv +
        2) ^ K₀ ≤ Z ^ D :=
      (Nat.pow_le_pow_left hZ' _).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have hvt' : vertexCertificate.time (d, bs) ≤ K₀ * P * Z ^ D := by
      refine hvt.trans ?_
      rw [hP]
      exact Nat.mul_le_mul_left _ hpowK
    have hvs' : vertexCertificate.space (d, bs) ≤ K₀ * Z ^ D :=
      hvs.trans (Nat.mul_le_mul_left _ hpowK)
    have htime : entryCertificate.time (.inr d, bs) =
        2 * (NativeCertificate.ofPolyTime getRight_polyTime).time (.inr d, bs) + n +
          ((NativeCertificate.ofPolyTime packetInput_polyTime).time ((.inr d, bs), d) +
            vertexCertificate.time (d, bs)) := by
      rw [hn]; rfl
    have hspace : entryCertificate.space (.inr d, bs) =
        2 * (NativeCertificate.ofPolyTime getRight_polyTime).space (.inr d, bs) + n +
          ((NativeCertificate.ofPolyTime packetInput_polyTime).space ((.inr d, bs), d) +
            vertexCertificate.space (d, bs)) := by
      rw [hn]; rfl
    constructor
    · rw [htime]
      have h1 : 2 * (cr * Z ^ D) + Z ^ D + ci * 3 ^ di * Z ^ D ≤
          P * ((2 * cr + 1 + ci * 3 ^ di) * Z ^ D) := by
        calc _ = (2 * cr + 1 + ci * 3 ^ di) * Z ^ D := by ring
          _ ≤ _ := Nat.le_mul_of_pos_left _ hP1
      have h2 : P * ((2 * cr + 1 + ci * 3 ^ di) * Z ^ D) + K₀ * P * Z ^ D ≤ P * (G * Z ^ D) := by
        rw [show K₀ * P * Z ^ D = P * (K₀ * Z ^ D) by ring, ← Nat.mul_add, ← Nat.add_mul]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      calc _ ≤ P * (G * Z ^ D) := by omega
        _ ≤ (G + D) * P * Z ^ (G + D) := by
            rw [show (G + D) * P * Z ^ (G + D) = P * ((G + D) * Z ^ (G + D)) by ring]
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) hZD)
    · rw [hspace]
      calc _ ≤ G * Z ^ D := by
            have : (2 * cr' + 1 + ci' * 3 ^ di' + K₀) * Z ^ D ≤ G * Z ^ D :=
              Nat.mul_le_mul_right _ (by omega)
            have e : (2 * cr' + 1 + ci' * 3 ^ di' + K₀) * Z ^ D =
                2 * (cr' * Z ^ D) + Z ^ D + ci' * 3 ^ di' * Z ^ D + K₀ * Z ^ D := by ring
            omega
        _ ≤ (G + D) * Z ^ (G + D) := Nat.mul_le_mul (by omega) hZD

end VertexDesc

end Cslib.Circuits.Frontier
