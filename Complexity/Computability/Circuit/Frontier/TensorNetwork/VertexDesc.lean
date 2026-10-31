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
kinds of vertices. The vertices of the input network keep their original descriptions, and they
survive into every child of their group with the same ports. The packet vertices created at a call
are described by "its packet data, the tuple `β`, the interpolation value, and the creation
precision" (p. 63), and from then on they also survive into the children of their group. A vertex
descriptor (`VertexDesc T`) is therefore a root descriptor of type `T` or a packet descriptor
(`NativePacket.PacketDesc`), and a retained vertex keeps its descriptor.

`VertexDesc.entry ev` evaluates a descriptor at the bits on its ports: the root's entry procedure
`ev`, which returns a coefficient list, or the native packet entry at the packet's creation
precision. A network of the recursion reads the entries at its own precision `(p, fl)`
(`GaloisRingArith.val p fl`), so a vertex is read at every precision through the canonical lift of
its coefficient list: a retained packet vertex created at a lower precision is read at the higher
one as the same element of `O = ℤ_(2)[U] / (f)`. Explicit tables are the root descriptors
`T = List ℕ` with the entry procedure `tableEntry`, which returns the table entry as a constant.
From a native certificate `ce` of the entry procedure, one native machine evaluates every
descriptor (`VertexDesc.entryCertificate ce`): time `K (m + 2) ^ L Z ^ K + E` and space
`K Z ^ K + ES`, for `m` target modes and `L` row ports of a packet (none for a root), `Z` polynomial
in the input and the reduced coefficient lists, and `E` and `ES` the time and space of `ce` on a
root (`VertexDesc.entryCertificate_le`). It is the evaluator of direct summation over networks of
descriptors at coefficient lists (`DescribedNetwork.contractionCertificate` at `SumOps.galois`).
The entry procedure of tables has a polynomial native certificate (`tableEntryCertificate`).

## Main definitions

* `Cslib.Circuits.Frontier.tableEntry`: the entry procedure of tables.
* `Cslib.Circuits.Frontier.VertexDesc`: a root descriptor or a packet descriptor.
* `Cslib.Circuits.Frontier.VertexDesc.entry`: its entry at the bits on its ports.
* `Cslib.Circuits.Frontier.VertexDesc.enc`: its encoding.
* `Cslib.Circuits.Frontier.VertexDesc.entryCertificate`: the native evaluator.
* `Cslib.Circuits.Frontier.tableEntryCertificate`: the native certificate of the entry procedure
  of tables.

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

/-- **The entry procedure of tables**: the table entry at the bits on the ports, as a constant
coefficient list. -/
@[expose] def tableEntry (table : List ℕ) (bs : List Bool) : List ℕ :=
  [ExplicitTensorNetwork.entry table bs]

/-- **The descriptor of a vertex** of a network of the contraction recursion: the descriptor of a
vertex of the input network (`inl`), or the descriptor of a packet vertex (`inr`). -/
abbrev VertexDesc (T : Type) : Type := T ⊕ PacketDesc

namespace VertexDesc

variable {T : Type}

/-- **The entry of a vertex at the bits on its ports**: the entry procedure `ev` of the input
network, or the native packet entry at the packet's creation precision. -/
@[expose] def entry (ev : T → List Bool → List ℕ) : VertexDesc T → List Bool → List ℕ
  | .inl t, bs => ev t bs
  | .inr d, bs => packetVertexEntry d bs

/-- The encoding of a descriptor: a tag, then the root descriptor or the packet descriptor. -/
abbrev enc (encT : T ↪ List Bool) : VertexDesc T ↪ List Bool := encSum encT encPacketDesc

/-- The number of target modes of a descriptor: those of its packet, and none for a root. -/
@[expose] def modes : VertexDesc T → ℕ
  | .inl _ => 0
  | .inr d => (targetModes d.1).length

/-- The number of row ports of a descriptor at the bits on its ports: those of its packet, and
none for a root. -/
@[expose] def rowPorts : VertexDesc T → List Bool → ℕ
  | .inl _, _ => 0
  | .inr d, bs => (sidePorts d.2.1 bs true).length

/-- The reduced coefficient lists of the creation precision of a descriptor are at most `Rv` bits
long; no condition for a root. -/
@[expose] def ReducedLE (Rv : ℕ) : VertexDesc T → Prop
  | .inl _ => True
  | .inr d => ∀ y, SumOps.galois.Reduced (d.1.p, d.1.fl) y → (encList encNat y).length ≤ Rv

/-! ### Values -/

@[simp] theorem entry_inl (ev : T → List Bool → List ℕ) (t : T) (bs : List Bool) :
    entry ev (.inl t) bs = ev t bs := rfl

@[simp] theorem entry_inr (ev : T → List Bool → List ℕ) (d : PacketDesc) (bs : List Bool) :
    entry ev (.inr d) bs = packetVertexEntry d bs := rfl

/-- **A table entry is read as a constant** at every precision. -/
theorem val_entry_inl (p : ℕ) (fl table : List ℕ) (bs : List Bool) :
    val p fl (entry tableEntry (.inl table) bs) =
      ((ExplicitTensorNetwork.entry table bs : ℕ) : Ring p fl) := by
  obtain h | ⟨e, he⟩ : fl.length = 0 ∨ ∃ e, fl.length = e + 1 :=
    (Nat.eq_zero_or_pos _).imp id fun h => ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
  · have := subsingleton_of_length_eq_zero (p := p) h
    exact Subsingleton.elim _ _
  · rw [entry_inl, tableEntry, val, he, Finset.sum_range_succ',
      Finset.sum_eq_zero fun i _ => by rw [List.getD_cons_succ, List.getD_nil]; simp]
    simp

/-- **A packet entry in every ring receiving `A_p`.** Along a ring map `ψ` from `A_p`, at the
precision `p` of the packet, to a ring in which `2` is nilpotent, the entry of a packet descriptor
at the bits on its ports is `packetEntry` at any ring map `κ : ℤ_(2) → S`, the image of the
interpolation value, the dense exponents, and the row and column ports read from the bits. -/
theorem map_val_entry_inr {S : Type*} [CommRing S] (ev : T → List Bool → List ℕ)
    (d : PacketDesc) (bs : List Bool) (ψ : Ring d.1.p d.1.fl →+* S) {n : ℕ}
    (hn : (2 : S) ^ n = 0) (κ : ℤ₍₂₎ →+* S)
    (hL : d.1.L = 2 ^ d.1.a) (hia : d.1.i < d.1.a) (htiles : d.1.tiles = 2 ^ (d.1.i + 1))
    (ht : d.1.t ∈ cauchyGrid (2 ^ d.1.a)) (hti : (2 : ℤ) ^ d.1.i ∣ d.1.t)
    (hti' : ¬ (2 : ℤ) ^ (d.1.i + 1) ∣ d.1.t) (hports : ∀ x ∈ d.2.1, x.2 < 2 ^ d.1.a) :
    ψ (val d.1.p d.1.fl (entry ev (.inr d) bs)) =
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
theorem reduced_entry_inr (ev : T → List Bool → List ℕ) (d : PacketDesc) (bs : List Bool) :
    SumOps.galois.Reduced (d.1.p, d.1.fl) (entry ev (.inr d) bs) :=
  SumOps.galois.reduced_mul (d.1.p, d.1.fl) _ _

/-! ### The native evaluator -/

section Evaluator

variable {encT : T ↪ List Bool}

/-- The left summand of a descriptor and its bits. -/
theorem getLeft_polyTime :
    ComputableInPolyTime (fun q : VertexDesc T × List Bool => q.1.getLeft?)
      (encPair (enc encT) encBits) (encOption encT) :=
  (ComputableInO.getLeft?_deg _ _).computableInPolyTime.comp (ComputableInPolyTime.fst _ _)

/-- The input of the packet evaluator at a descriptor and its bits, the default packet standing for
a root. -/
theorem packetInput_polyTime :
    ComputableInPolyTime (fun q : VertexDesc T × List Bool => (q.1.getRight?.getD default, q.2))
      (encPair (enc encT) encBits) (encPair encPacketDesc encBits) := by
  have hright : ComputableInPolyTime (fun q : VertexDesc T × List Bool => q.1.getRight?)
      (encPair (enc encT) encBits) (encOption encPacketDesc) :=
    (ComputableInO.getRight?_deg _ _).computableInPolyTime.comp (ComputableInPolyTime.fst _ _)
  exact ((ComputableInDegree.getD (enc₁ := encPacketDesc) (enc := encOption encPacketDesc)
    default).computableInPolyTime.comp hright).prod (ComputableInPolyTime.snd _ _)

/-- The input of the root's entry procedure from a descriptor's bits and its root descriptor. -/
theorem rootInput_polyTime :
    ComputableInPolyTime (fun (((_, bs), t) : (VertexDesc T × List Bool) × T) => (t, bs))
      (encPair (encPair (enc encT) encBits) encT) (encPair encT encBits) :=
  (ComputableInPolyTime.snd _ _).prod
    ((ComputableInPolyTime.snd (enc encT) encBits).comp (ComputableInPolyTime.fst _ _))

variable {ev : T → List Bool → List ℕ}

/-- **One native machine for the entries of all descriptors**, from a native certificate `ce` of
the entry procedure `ev` of the root descriptors: `ce` for a root, and the native packet evaluator
(`NativePacket.vertexCertificate`) for a packet. -/
noncomputable def entryCertificate
    (ce : NativeCertificate (fun q : T × List Bool => ev q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    NativeCertificate (fun q : VertexDesc T × List Bool => entry ev q.1 q.2)
      (encPair (enc encT) encBits) (encList encNat) :=
  (NativeCertificate.option (value := fun q : VertexDesc T × List Bool => q.1.getLeft?)
    (fallback := fun q => packetVertexEntry (q.1.getRight?.getD default) q.2)
    (body := fun ((_, bs), t) => ev t bs)
    (NativeCertificate.ofPolyTime getLeft_polyTime)
    ((vertexCertificate.comp (NativeCertificate.ofPolyTime packetInput_polyTime)).congr
      fun _ => rfl)
    ((ce.comp (NativeCertificate.ofPolyTime rootInput_polyTime)).congr fun _ => rfl)).congr
    fun q => by
      rcases q with ⟨d | d, bs⟩ <;> rfl

/-- `c (y + 1) ^ d ≤ c Z ^ D` when `y + 1 ≤ Z` and `d ≤ D`. -/
private theorem mul_pow_le_mul_pow {c y d Z D : ℕ} (hy : y + 1 ≤ Z) (hd : d ≤ D) :
    c * (y + 1) ^ d ≤ c * Z ^ D :=
  Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hy _).trans
    (Nat.pow_le_pow_right (by omega) hd))

/-- **The resources of the native evaluator of descriptors.** For a native certificate `ce` of
the entry procedure of the roots, there is `K` such that on a descriptor and bits of total length
`n`, with `m` target modes and `L` row ports (`0` and `0` for a root), if the reduced coefficient
lists of a packet's precision are at most `Rv` bits long and `ce` takes time at most `E` and space
at most `ES` on a root and the bits, then with `Z = n + m + Rv + 2` the time is at most
`K (m + 2) ^ L Z ^ K + E` and the space at most `K Z ^ K + ES`. -/
theorem entryCertificate_le
    (ce : NativeCertificate (fun q : T × List Bool => ev q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    ∃ K : ℕ, ∀ (q : VertexDesc T × List Bool) (Rv E ES : ℕ), q.1.ReducedLE Rv →
      (∀ t, q.1 = .inl t → ce.time (t, q.2) ≤ E ∧ ce.space (t, q.2) ≤ ES) →
      (entryCertificate ce).time q ≤ K * (q.1.modes + 2) ^ q.1.rowPorts q.2 *
          ((encPair (enc encT) encBits q).length + q.1.modes + Rv + 2) ^ K + E ∧
        (entryCertificate ce).space q ≤
          K * ((encPair (enc encT) encBits q).length + q.1.modes + Rv + 2) ^ K + ES := by
  obtain ⟨K₀, hK₀⟩ := vertexCertificate_le
  have hL := NativeCertificate.ofPolyTime_isPolynomial (getLeft_polyTime (encT := encT))
  have hP := NativeCertificate.ofPolyTime_isPolynomial (packetInput_polyTime (encT := encT))
  have hI := NativeCertificate.ofPolyTime_isPolynomial (rootInput_polyTime (encT := encT))
  obtain ⟨cr, dr, hrt⟩ := hL.1.exists_le
  obtain ⟨cr', dr', hrs⟩ := hL.2.exists_le
  obtain ⟨cp, dp, hpt⟩ := hP.1.exists_le
  obtain ⟨cp', dp', hps⟩ := hP.2.exists_le
  obtain ⟨ci, di, hit⟩ := hI.1.exists_le
  obtain ⟨ci', di', his⟩ := hI.2.exists_le
  obtain ⟨D, hD⟩ : ∃ D, D = K₀ + dr + dr' + dp + dp' + di + di' + 1 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = K₀ + 2 * cr + 2 * cr' + cp + cp' + ci * 3 ^ di + ci' * 3 ^ di' + 1 :=
    ⟨_, rfl⟩
  refine ⟨G + D, fun q Rv E ES hRv hE => ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, n = (encPair (enc encT) encBits q).length := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = n + q.1.modes + Rv + 2 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = (q.1.modes + 2) ^ q.1.rowPorts q.2 := ⟨_, rfl⟩
  rw [← hn, ← hZ, ← hP]
  have hP1 : 1 ≤ P := hP ▸ Nat.one_le_pow _ _ (by omega)
  have hnZ : n + 1 ≤ Z := by omega
  have hZD : Z ^ D ≤ Z ^ (G + D) := Nat.pow_le_pow_right (by omega) (by omega)
  have hrt' : (NativeCertificate.ofPolyTime (getLeft_polyTime (encT := encT))).time q ≤
      cr * Z ^ D := (hrt q).trans (hn ▸ mul_pow_le_mul_pow hnZ (by omega))
  have hrs' : (NativeCertificate.ofPolyTime (getLeft_polyTime (encT := encT))).space q ≤
      cr' * Z ^ D := (hrs q).trans (hn ▸ mul_pow_le_mul_pow hnZ (by omega))
  rcases q with ⟨t | d, bs⟩
  · -- A root: the input of the entry procedure, then the entry procedure.
    obtain ⟨hEt, hEs⟩ : ce.time (t, bs) ≤ E ∧ ce.space (t, bs) ≤ ES := hE t rfl
    have hlenI : (encPair (encPair (enc encT) encBits) encT ((.inl t, bs), t)).length + 1 ≤
        3 * Z := by
      have h1 : (encPair (encPair (enc encT) encBits) encT ((.inl t, bs), t)).length =
          2 * (encPair (enc encT) encBits (.inl t, bs)).length + 1 + (encT t).length :=
        length_encPair _
      have h2 : (encPair (enc encT) encBits (Sum.inl t, bs)).length =
          2 * ((enc encT) (.inl t)).length + 1 + (encBits bs).length := length_encPair _
      have h3 : ((enc encT) (Sum.inl t : VertexDesc T)).length = (encT t).length + 1 := by
        rw [length_encSum]; rfl
      omega
    have hpow3 {c e : ℕ} (he : e ≤ D) : c * (3 * Z) ^ e ≤ c * 3 ^ e * Z ^ D := by
      rw [Nat.mul_pow, ← Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) he)
    have hit' : (NativeCertificate.ofPolyTime (rootInput_polyTime (encT := encT))).time
        ((.inl t, bs), t) ≤ ci * 3 ^ di * Z ^ D :=
      (hit _).trans ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlenI _)).trans
        (hpow3 (by omega)))
    have his' : (NativeCertificate.ofPolyTime (rootInput_polyTime (encT := encT))).space
        ((.inl t, bs), t) ≤ ci' * 3 ^ di' * Z ^ D :=
      (his _).trans ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlenI _)).trans
        (hpow3 (by omega)))
    have htime : (entryCertificate ce).time (.inl t, bs) =
        2 * (NativeCertificate.ofPolyTime (getLeft_polyTime (encT := encT))).time (.inl t, bs) +
          n + ((NativeCertificate.ofPolyTime (rootInput_polyTime (encT := encT))).time
            ((.inl t, bs), t) + ce.time (t, bs)) := by
      rw [hn]; rfl
    have hspace : (entryCertificate ce).space (.inl t, bs) =
        2 * (NativeCertificate.ofPolyTime (getLeft_polyTime (encT := encT))).space (.inl t, bs) +
          n + ((NativeCertificate.ofPolyTime (rootInput_polyTime (encT := encT))).space
            ((.inl t, bs), t) + ce.space (t, bs)) := by
      rw [hn]; rfl
    have hnD : n ≤ Z ^ D := by
      calc n ≤ Z := by omega
        _ = Z ^ 1 := (pow_one Z).symm
        _ ≤ Z ^ D := Nat.pow_le_pow_right (by omega) (by omega)
    constructor
    · rw [htime]
      have h1 : 2 * (cr * Z ^ D) + Z ^ D + ci * 3 ^ di * Z ^ D ≤ G * Z ^ D := by
        have : (2 * cr + 1 + ci * 3 ^ di) * Z ^ D ≤ G * Z ^ D := Nat.mul_le_mul_right _ (by omega)
        have e : (2 * cr + 1 + ci * 3 ^ di) * Z ^ D =
            2 * (cr * Z ^ D) + Z ^ D + ci * 3 ^ di * Z ^ D := by ring
        omega
      have h2 : G * Z ^ D ≤ (G + D) * P * Z ^ (G + D) :=
        Nat.mul_le_mul ((Nat.le_add_right G D).trans (Nat.le_mul_of_pos_right _ hP1)) hZD
      omega
    · rw [hspace]
      have h1 : 2 * (cr' * Z ^ D) + Z ^ D + ci' * 3 ^ di' * Z ^ D ≤ G * Z ^ D := by
        have : (2 * cr' + 1 + ci' * 3 ^ di') * Z ^ D ≤ G * Z ^ D :=
          Nat.mul_le_mul_right _ (by omega)
        have e : (2 * cr' + 1 + ci' * 3 ^ di') * Z ^ D =
            2 * (cr' * Z ^ D) + Z ^ D + ci' * 3 ^ di' * Z ^ D := by ring
        omega
      have h2 : G * Z ^ D ≤ (G + D) * Z ^ (G + D) := Nat.mul_le_mul (by omega) hZD
      omega
  · -- A packet: the input of the packet evaluator, then the evaluator.
    have hpt' : (NativeCertificate.ofPolyTime (packetInput_polyTime (encT := encT))).time
        (.inr d, bs) ≤ cp * Z ^ D :=
      (hpt _).trans (hn ▸ mul_pow_le_mul_pow hnZ (by omega))
    have hps' : (NativeCertificate.ofPolyTime (packetInput_polyTime (encT := encT))).space
        (.inr d, bs) ≤ cp' * Z ^ D :=
      (hps _).trans (hn ▸ mul_pow_le_mul_pow hnZ (by omega))
    have hlen : (encPair encPacketDesc encBits (d, bs)).length ≤ n := by
      have h1 : n = 2 * ((encPacketDesc d).length + 1) + 1 + (encBits bs).length := by
        rw [hn]; exact length_encPair _
      have h3 : (encPair encPacketDesc encBits (d, bs)).length =
          2 * (encPacketDesc d).length + 1 + (encBits bs).length := length_encPair _
      omega
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
    have htime : (entryCertificate ce).time (.inr d, bs) =
        2 * (NativeCertificate.ofPolyTime (getLeft_polyTime (encT := encT))).time (.inr d, bs) +
          n + ((NativeCertificate.ofPolyTime (packetInput_polyTime (encT := encT))).time
            (.inr d, bs) + vertexCertificate.time (d, bs)) := by
      rw [hn]; rfl
    have hspace : (entryCertificate ce).space (.inr d, bs) =
        2 * (NativeCertificate.ofPolyTime (getLeft_polyTime (encT := encT))).space (.inr d, bs) +
          n + ((NativeCertificate.ofPolyTime (packetInput_polyTime (encT := encT))).space
            (.inr d, bs) + vertexCertificate.space (d, bs)) := by
      rw [hn]; rfl
    have hnD : n ≤ Z ^ D := by
      calc n ≤ Z := by omega
        _ = Z ^ 1 := (pow_one Z).symm
        _ ≤ Z ^ D := Nat.pow_le_pow_right (by omega) (by omega)
    constructor
    · rw [htime]
      have h1 : 2 * (cr * Z ^ D) + Z ^ D + cp * Z ^ D ≤ P * ((2 * cr + 1 + cp) * Z ^ D) := by
        calc _ = (2 * cr + 1 + cp) * Z ^ D := by ring
          _ ≤ _ := Nat.le_mul_of_pos_left _ hP1
      have h2 : P * ((2 * cr + 1 + cp) * Z ^ D) + K₀ * P * Z ^ D ≤ P * (G * Z ^ D) := by
        rw [show K₀ * P * Z ^ D = P * (K₀ * Z ^ D) by ring, ← Nat.mul_add, ← Nat.add_mul]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      have h3 : P * (G * Z ^ D) ≤ (G + D) * P * Z ^ (G + D) := by
        rw [show (G + D) * P * Z ^ (G + D) = P * ((G + D) * Z ^ (G + D)) by ring]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) hZD)
      omega
    · rw [hspace]
      have h1 : 2 * (cr' * Z ^ D) + Z ^ D + cp' * Z ^ D + K₀ * Z ^ D ≤ G * Z ^ D := by
        have : (2 * cr' + 1 + cp' + K₀) * Z ^ D ≤ G * Z ^ D := Nat.mul_le_mul_right _ (by omega)
        have e : (2 * cr' + 1 + cp' + K₀) * Z ^ D =
            2 * (cr' * Z ^ D) + Z ^ D + cp' * Z ^ D + K₀ * Z ^ D := by ring
        omega
      have h2 : G * Z ^ D ≤ (G + D) * Z ^ (G + D) := Nat.mul_le_mul (by omega) hZD
      omega

end Evaluator

end VertexDesc

/-! ### Tables -/

/-- The entry procedure of tables is polynomial-time. -/
theorem tableEntry_polyTime :
    ComputableInPolyTime (fun q : List ℕ × List Bool => tableEntry q.1 q.2)
      (encPair (encList encNat) encBits) (encList encNat) := by
  have hindex := ComputableInPolyTime.bitsBinaryValue.comp
    (ComputableInPolyTime.bitsReverse.comp (ComputableInPolyTime.snd (encList encNat) encBits))
  have hentry := ComputableInPolyTime.listGetD_binary (encA := encNat) (encL := encList encNat) 0
    (ComputableInPolyTime.fst _ _) hindex
  exact (ComputableInPolyTime.cons' hentry (ComputableInPolyTime.const [])).of_enc_eq fun q => by
    simp only [tableEntry, ExplicitTensorNetwork.entry,
      BitString.lsbValue_eq_binaryValue_reverse, Function.comp_apply]

/-- **The native certificate of the entry procedure of tables.** -/
noncomputable def tableEntryCertificate :
    NativeCertificate (fun q : List ℕ × List Bool => tableEntry q.1 q.2)
      (encPair (encList encNat) encBits) (encList encNat) :=
  NativeCertificate.ofPolyTime tableEntry_polyTime

/-- The certificate of the entry procedure of tables is polynomial. -/
theorem tableEntryCertificate_isPolynomial : tableEntryCertificate.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial tableEntry_polyTime

end Cslib.Circuits.Frontier
