/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionMachine
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionStep
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Mathlib.Data.List.GetD
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# The leaves of the fast contraction algorithm

The cost of the leaves of the native recursion of Theorem D.1 of [OpenAI2026ETH]
(`Cslib.Circuits.Frontier.FastContraction.leafCertificate`), the leaf clause of the resource
analysis `Cslib.Complexity.CountingSimulation.FastAnalysis`. A leaf sums directly over the `2 ^ M`
edge assignments of a call with `M` edges (§D.4.7, p. 64), and the entry of a packet vertex costs
`(m + 2) ^ L` for `m` target modes and `L` row ports, the source's `exp(O(L log s))` (§D.4.6,
p. 63).

**The cost of a leaf** (`FastContraction.leafCertificate_le`): with at most `R` target modes and
`Λ` row ports per vertex, time `K (n + R + 1) ^ K 2 ^ M (R + 2) ^ Λ` and space `K (n + R + 1) ^ K`
on a call of encoded length `n`, from the bounds of direct summation
(`DescribedNetwork.contractionCertificate_le`) and of the evaluator of descriptors
(`VertexDesc.entryCertificate_le`).

**The packet shape** (`FastContraction.PacketShape`). Every packet vertex of a call of the
recursion has `i < a ≤ ⌊log₂ s⌋ / 32768`, `2 ^ (i + 1)` tiles, at most `p` exponents per tile, and
row ports in distinct slots below `2 ^ a`. So, with `A = 2 ^ (⌊log₂ s⌋ / 32768)`, it has at most
`A p` target modes and `A` row ports. The root has no packets, and the shape passes to the native
children of a well-formed active call (`FastContraction.packetShape_child`): a retained vertex
keeps its descriptor, and the row ports of a new packet are edges of one packet of the packing,
in distinct slots (`NativeChild.desc_of_mem_nativeChild`).

**The leaf bound** (`FastContraction.exists_leafCertificate_le`). For `s ≤ m ≤ C s`, a leaf with
the packet shape and at most `2 m` edges takes time `K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` and space
`K (n + 1) ^ K`, provided that from some `s₀` on it has at most `leafSize m` edges and precision at
most `m ^ c`: then `2 ^ M ≤ 2 ^ (C s / √⌊log₂ s⌋)`, and `(A p + 2) ^ A` is
`2 ^ O(s ^ (1 / 32768) log s)` (`FastContraction.exists_packetFactor_le`). Below `s₀` everything
but a polynomial in `n` is a constant.

## Main definitions

* `Cslib.Circuits.Frontier.FastContraction.PacketShape`: the shape of the packets of a call.

## Main results

* `Cslib.Circuits.Frontier.FastContraction.leafCertificate_le`: the cost of a leaf.
* `Cslib.Circuits.Frontier.NativeChild.desc_of_mem_nativeChild`: the descriptors of a native
  child.
* `Cslib.Circuits.Frontier.FastContraction.packetShape_root`,
  `Cslib.Circuits.Frontier.FastContraction.packetShape_child`: the packet shape on the reached
  calls.
* `Cslib.Circuits.Frontier.FastContraction.leafCertificate_le_of_packetShape`: the cost of a leaf
  with the packet shape.
* `Cslib.Circuits.Frontier.FastContraction.exists_leafCertificate_le`: the leaf bound of the
  resource analysis.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.6–§D.4.7,
  pp. 63–64.
-/

public section

namespace Cslib.Circuits.Frontier

/-! ### The descriptors of the native children -/

namespace NativeChild

open ChildNumbering

variable {D : DescribedNetwork VertexDesc} {r : ℕ}

/-- **The descriptors of the native child.** A vertex of the native child of a rows-first parent
with at least `64 ^ a` edges keeps the descriptor of a parent vertex, or is the packet `q`, with
the packet context of `q`, the slice of `β` at `q`, and tags whose slots are below `2 ^ a` and
distinct among its row ports. -/
theorem desc_of_mem_nativeChild (hD : D.IsRowsFirstBipartite r) {fl : List ℕ} {a i : ℕ}
    (hK : 64 ^ a ≤ D.numEdges) (hia : i < a) (pt : ℕ) (t : ℤ) (ζ β : List ℕ) (g : Fin 64)
    {v : List ℕ × VertexDesc}
    (hv : v ∈ (nativeChild fl a i pt t ζ r D (nativeParentPacking r a D) β g).vertices) :
    (∃ w ∈ D.vertices, v.2 = w.2) ∨
      ∃ q tags, v.2 = .inr (packetCtx fl a i pt t ζ g q, tags, betaSlice i pt β q) ∧
        (∀ y ∈ tags, y.2 < 2 ^ a) ∧ ((tags.filter (·.1)).map (·.2)).Nodup := by
  have hgroups := groupsOf_eq hD hK hia
  have hpk1 : (nativeParentPacking r a D).2.1 = (parentPacking hD a).numPackets := by
    rw [nativeParentPacking_eq hD hK]
  have hpk2 : (nativeParentPacking r a D).2.2 = List.ofFn fun e =>
      (((parentPacking hD a).packet e : ℕ), ((parentPacking hD a).slot e : ℕ)) := by
    rw [nativeParentPacking_eq hD hK]
  rw [nativeChild_eq hD _ (parentPacking hD a).packet (fun e => ((parentPacking hD a).slot e : ℕ))
    g fl a i pt t ζ β _ hgroups hpk1 hpk2] at hv
  simp only [List.mem_ofFn] at hv
  obtain ⟨c, rfl⟩ := hv
  rcases hc : (childVertexEquiv (P := (parentPacking hD a).numPackets)
      (packingGroup (parentSide r) (parentPacking hD a) ⟨i, hia⟩) g).symm c with w | q
  · left
    refine ⟨D.vertices[(w.1 : ℕ)], List.getElem_mem _, ?_⟩
    simp only [numberedDesc, Sum.elim_inl]
  · right
    simp only [numberedDesc, Sum.elim_inr]
    refine ⟨q, _, rfl, ?_, ?_⟩
    · intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨e, -, rfl⟩ := hy
      exact Fin.isLt _
    · rw [List.filter_map, List.map_map]
      refine List.Nodup.map_on ?_ ((nodup_packetPorts hD _ _ g q).filter _)
      intro c₁ hc₁ c₂ hc₂ heq
      simp only [List.mem_filter, Function.comp_apply] at hc₁ hc₂
      obtain ⟨hm₁, hl₁⟩ := hc₁
      obtain ⟨hm₂, hl₂⟩ := hc₂
      rw [mem_packetPorts] at hm₁ hm₂
      rcases c₁ with e₁ | e₁
      · rcases c₂ with e₂ | e₂
        · simp only [Function.comp_apply, Sum.elim_inl] at heq hm₁ hm₂
          have hinj := (parentPacking hD a).injective (a₁ := e₁.1) (a₂ := e₂.1)
            (Prod.ext (hm₁.trans hm₂.symm) (Fin.ext heq))
          rw [Subtype.ext hinj]
        · simp at hl₂
      · simp at hl₁

end NativeChild

namespace FastContraction

open GaloisRingArith NativePacket ChildCursor NativeRecovery ContractionSchedule NativeChild
  Cslib.GenericRAM Cslib.GenericRAM.StackRecursion Turing.MultiTapeTM

/-! ### Encoded lengths -/

/-- The scale, the precision and the coefficients of the modulus are at most the encoded length
of a call. -/
theorem scale_add_prec_add_length_fl_le (x : Call) :
    x.scale + x.prec + x.fl.length ≤ (encCall x).length := by
  have h := length_le_length_encList encNat x.fl
  obtain ⟨⟨s, d, b, p, fl, r⟩, D⟩ := x
  simp only [Call.scale, Call.prec, Call.fl, encCall, encParams, length_encPair, encUnary_apply,
    List.length_replicate] at h ⊢
  omega

/-- The network of a call is at most its encoded length. -/
theorem length_net_le (x : Call) :
    (DescribedNetwork.encDescribed VertexDesc.enc x.net).length ≤ (encCall x).length := by
  obtain ⟨p, D⟩ := x
  simp only [Call.net, encCall, length_encPair]
  omega

/-- A vertex of a call is at most its encoded length. -/
theorem length_vertex_le {x : Call} {v : List ℕ × VertexDesc} (hv : v ∈ x.net.vertices) :
    (encPair (encList encNat) VertexDesc.enc v).length ≤ (encCall x).length := by
  have h := length_le_encList_of_mem (encPair (encList encNat) VertexDesc.enc) hv
  have h2 : (encList (encPair (encList encNat) VertexDesc.enc) x.net.vertices).length ≤
      (DescribedNetwork.encDescribed VertexDesc.enc x.net).length := by
    change _ ≤ (encPair encUnary (encList (encPair (encList encNat) VertexDesc.enc))
      (x.net.numEdges, x.net.vertices)).length
    rw [length_encPair]
    dsimp only
    omega
  have h3 := length_net_le x
  omega

/-- The number of vertices of a call is at most its encoded length. -/
theorem length_vertices_le (x : Call) : x.net.vertices.length ≤ (encCall x).length := by
  have h := DescribedNetwork.length_numEdges_vertices_le (encT := VertexDesc.enc) x.net
  have h3 := length_net_le x
  omega

/-! ### The cost of a leaf -/

/-- `c (y + 1) ^ d ≤ c W ^ d` when `y + 1 ≤ W`. -/
private theorem mul_pow_le_of_le {c y d W : ℕ} (hy : y + 1 ≤ W) : c * (y + 1) ^ d ≤ c * W ^ d :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hy _)

/-- Raising the exponent of `W ≥ 1`. -/
private theorem mul_pow_le_mul_pow {c W d E : ℕ} (hW : 1 ≤ W) (hd : d ≤ E) :
    c * W ^ d ≤ c * W ^ E :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW hd)

/-- The reduced coefficient lists against `W`. -/
private theorem rv_le {n W cf df cp dp ct dt : ℕ} (hnW : n + 1 ≤ W) :
    n * (2 * n + 3) + cf * (n + 1) ^ df * (2 * (cp * (n + 1) ^ dp) + 3) +
        ct * (3 * n + 2) ^ dt ≤
      (5 + cf * (2 * cp + 3) + ct * 3 ^ dt) * W ^ (2 + df + dp + dt) := by
  have hW1 : 1 ≤ W := by omega
  have h1 : n * (2 * n + 3) ≤ 5 * W ^ 2 :=
    calc n * (2 * n + 3) ≤ W * (5 * W) := Nat.mul_le_mul (by omega) (by omega)
      _ = 5 * W ^ 2 := by ring
  have h2 : cf * (n + 1) ^ df * (2 * (cp * (n + 1) ^ dp) + 3) ≤
      cf * (2 * cp + 3) * W ^ (df + dp) := by
    have hb1 : (n + 1) ^ df ≤ W ^ df := Nat.pow_le_pow_left hnW _
    have hb2 : cp * (n + 1) ^ dp ≤ cp * W ^ dp := mul_pow_le_of_le hnW
    have hW1' : 1 ≤ W ^ dp := Nat.one_le_pow _ _ (by omega)
    have : 2 * (cp * (n + 1) ^ dp) + 3 ≤ (2 * cp + 3) * W ^ dp := by
      rw [add_mul, Nat.mul_assoc]; omega
    calc cf * (n + 1) ^ df * (2 * (cp * (n + 1) ^ dp) + 3)
        ≤ cf * W ^ df * ((2 * cp + 3) * W ^ dp) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hb1) this
      _ = cf * (2 * cp + 3) * W ^ (df + dp) := by rw [pow_add]; ring
  have h3 : ct * (3 * n + 2) ^ dt ≤ ct * 3 ^ dt * W ^ dt :=
    calc ct * (3 * n + 2) ^ dt ≤ ct * (3 * W) ^ dt :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = ct * 3 ^ dt * W ^ dt := by rw [mul_pow]; ring
  have l1 : 5 * W ^ 2 ≤ 5 * W ^ (2 + df + dp + dt) := mul_pow_le_mul_pow hW1 (by omega)
  have l2 : cf * (2 * cp + 3) * W ^ (df + dp) ≤ cf * (2 * cp + 3) * W ^ (2 + df + dp + dt) :=
    mul_pow_le_mul_pow hW1 (by omega)
  have l3 : ct * 3 ^ dt * W ^ dt ≤ ct * 3 ^ dt * W ^ (2 + df + dp + dt) :=
    mul_pow_le_mul_pow hW1 (by omega)
  rw [add_mul, add_mul]
  omega

/-- The input of direct summation against `W`. -/
private theorem sum_le_of_le {W a b c₀ d₀ cR E₀ : ℕ} (hW : 1 ≤ W) (ha : a ≤ c₀ * W ^ d₀)
    (hd : d₀ ≤ E₀) (hb : b ≤ cR * W ^ E₀) : a + b + b + 1 ≤ (c₀ + 2 * cR + 1) * W ^ E₀ := by
  have h1 : c₀ * W ^ d₀ ≤ c₀ * W ^ E₀ := mul_pow_le_mul_pow hW hd
  have h2 : 1 ≤ W ^ E₀ := Nat.one_le_pow _ _ (by omega)
  rw [add_mul, add_mul, Nat.mul_assoc 2]
  omega

/-- The bound on the entries' arguments against `W`. -/
private theorem zb_le {W n R Rv cR E₀ : ℕ} (hW : 1 ≤ W) (hE : 1 ≤ E₀) (hRv : Rv ≤ cR * W ^ E₀)
    (hnR : 3 * n + R + 3 ≤ 3 * W) : 3 * n + R + Rv + 3 ≤ (3 + cR) * W ^ E₀ := by
  have h1 : W ≤ W ^ E₀ :=
    calc W = W ^ 1 := (pow_one W).symm
      _ ≤ W ^ E₀ := Nat.pow_le_pow_right hW hE
  rw [add_mul]
  omega

/-- The arithmetic of the time of a leaf. -/
private theorem time_assemble {Td Ti Ts cd dd ci di P X k W A Zb c₁ c₂ E₀ K₁ K₂ : ℕ}
    (hW : 1 ≤ W) (hP : 1 ≤ P) (hX : 1 ≤ X) (hd : Td ≤ cd * W ^ dd) (hi : Ti ≤ ci * W ^ di)
    (hs : Ts ≤ (P * (k + 1) + 1) * (K₁ * (A + 1) ^ K₁ + 2 * (K₂ * X * Zb ^ K₂)))
    (hk : k + 1 ≤ W) (hA : A + 1 ≤ c₁ * W ^ E₀) (hZ : Zb ≤ c₂ * W ^ E₀) :
    Td + (Ti + Ts) ≤ (2 * (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂)) + cd + ci) *
      W ^ (1 + E₀ * (K₁ + K₂) + dd + di) * P * X := by
  have hWF1 : W ^ (E₀ * K₁) ≤ W ^ (E₀ * (K₁ + K₂)) :=
    Nat.pow_le_pow_right hW (by rw [Nat.mul_add]; omega)
  have hWF2 : W ^ (E₀ * K₂) ≤ W ^ (E₀ * (K₁ + K₂)) :=
    Nat.pow_le_pow_right hW (by rw [Nat.mul_add]; omega)
  set F := E₀ * (K₁ + K₂)
  set S := W ^ (1 + F + dd + di)
  have hA' : K₁ * (A + 1) ^ K₁ ≤ K₁ * c₁ ^ K₁ * W ^ F :=
    calc K₁ * (A + 1) ^ K₁ ≤ K₁ * (c₁ * W ^ E₀) ^ K₁ :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA _)
      _ = K₁ * c₁ ^ K₁ * W ^ (E₀ * K₁) := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]
      _ ≤ K₁ * c₁ ^ K₁ * W ^ F := Nat.mul_le_mul_left _ hWF1
  have hZ' : K₂ * X * Zb ^ K₂ ≤ K₂ * c₂ ^ K₂ * X * W ^ F :=
    calc K₂ * X * Zb ^ K₂ ≤ K₂ * X * (c₂ * W ^ E₀) ^ K₂ :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hZ _)
      _ = K₂ * c₂ ^ K₂ * X * W ^ (E₀ * K₂) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ K₂ * c₂ ^ K₂ * X * W ^ F := Nat.mul_le_mul_left _ hWF2
  have hin : K₁ * (A + 1) ^ K₁ + 2 * (K₂ * X * Zb ^ K₂) ≤
      (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂)) * X * W ^ F := by
    have : K₁ * c₁ ^ K₁ * W ^ F ≤ K₁ * c₁ ^ K₁ * W ^ F * X := Nat.le_mul_of_pos_right _ hX
    have e : (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂)) * X * W ^ F =
        K₁ * c₁ ^ K₁ * W ^ F * X + 2 * (K₂ * c₂ ^ K₂ * X * W ^ F) := by ring
    omega
  have hPk : P * (k + 1) + 1 ≤ 2 * P * W := by
    have : P * (k + 1) ≤ P * W := Nat.mul_le_mul_left _ hk
    have : 1 ≤ P * W := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [Nat.mul_assoc]; omega
  have hs' : Ts ≤ 2 * (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂)) * S * P * X :=
    calc Ts ≤ (2 * P * W) * ((K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂)) * X * W ^ F) :=
          hs.trans (Nat.mul_le_mul hPk hin)
      _ = 2 * (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂)) * W ^ (1 + F) * P * X := by
          rw [pow_add, pow_one]; ring
      _ ≤ 2 * (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂)) * S * P * X :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW (by omega))))
  have hPX : 1 ≤ P * X := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hd' : Td ≤ cd * S * P * X :=
    calc Td ≤ cd * S := hd.trans (mul_pow_le_mul_pow hW (by omega))
      _ ≤ cd * S * (P * X) := Nat.le_mul_of_pos_right _ hPX
      _ = cd * S * P * X := by ring
  have hi' : Ti ≤ ci * S * P * X :=
    calc Ti ≤ ci * S := hi.trans (mul_pow_le_mul_pow hW (by omega))
      _ ≤ ci * S * (P * X) := Nat.le_mul_of_pos_right _ hPX
      _ = ci * S * P * X := by ring
  have e : (2 * (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂)) + cd + ci) * S * P * X =
      2 * (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂)) * S * P * X + cd * S * P * X + ci * S * P * X := by
    ring
  omega

/-- The arithmetic of the space of a leaf. -/
private theorem space_assemble {Sd Si Ss cd dd ci di W A Zb c₁ c₂ E₀ K₁ K₂ ES : ℕ}
    (hW : 1 ≤ W) (hd : Sd ≤ cd * W ^ dd) (hi : Si ≤ ci * W ^ di)
    (hs : Ss ≤ K₁ * (A + 1) ^ K₁ + ES) (hA : A + 1 ≤ c₁ * W ^ E₀) (hES : ES = K₂ * Zb ^ K₂)
    (hZ : Zb ≤ c₂ * W ^ E₀) :
    Sd + (Si + Ss) ≤ (K₁ * c₁ ^ K₁ + K₂ * c₂ ^ K₂ + cd + ci) *
      W ^ (E₀ * (K₁ + K₂) + dd + di) := by
  have hWF1 : W ^ (E₀ * K₁) ≤ W ^ (E₀ * (K₁ + K₂) + dd + di) :=
    Nat.pow_le_pow_right hW (by rw [Nat.mul_add]; omega)
  have hWF2 : W ^ (E₀ * K₂) ≤ W ^ (E₀ * (K₁ + K₂) + dd + di) :=
    Nat.pow_le_pow_right hW (by rw [Nat.mul_add]; omega)
  set F := E₀ * (K₁ + K₂)
  set S := W ^ (F + dd + di)
  have hA' : K₁ * (A + 1) ^ K₁ ≤ K₁ * c₁ ^ K₁ * S :=
    calc K₁ * (A + 1) ^ K₁ ≤ K₁ * (c₁ * W ^ E₀) ^ K₁ :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA _)
      _ = K₁ * c₁ ^ K₁ * W ^ (E₀ * K₁) := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]
      _ ≤ K₁ * c₁ ^ K₁ * S := Nat.mul_le_mul_left _ hWF1
  have hZ' : ES ≤ K₂ * c₂ ^ K₂ * S :=
    calc ES = K₂ * Zb ^ K₂ := hES
      _ ≤ K₂ * (c₂ * W ^ E₀) ^ K₂ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hZ _)
      _ = K₂ * c₂ ^ K₂ * W ^ (E₀ * K₂) := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]
      _ ≤ K₂ * c₂ ^ K₂ * S := Nat.mul_le_mul_left _ hWF2
  have hd' : Sd ≤ cd * S := hd.trans (mul_pow_le_mul_pow hW (by omega))
  have hi' : Si ≤ ci * S := hi.trans (mul_pow_le_mul_pow hW (by omega))
  have e : (K₁ * c₁ ^ K₁ + K₂ * c₂ ^ K₂ + cd + ci) * S =
      K₁ * c₁ ^ K₁ * S + K₂ * c₂ ^ K₂ * S + cd * S + ci * S := by ring
  omega

/-- **The cost of a leaf.** There is `K` such that, on a call of encoded length `n` with `M` edges
whose vertices have at most `R` target modes and at most `Λ` row ports on every bit list on their
ports, direct summation takes time at most `K (n + R + 1) ^ K 2 ^ M (R + 2) ^ Λ` and space at most
`K (n + R + 1) ^ K`, whatever the child builder. -/
theorem leafCertificate_le : ∃ K : ℕ, ∀ (mk : Call → State → ℕ × DescribedNetwork VertexDesc)
    (x : Call) (R Λ : ℕ),
    (∀ v ∈ x.net.vertices, v.2.modes ≤ R ∧
      ∀ bs : List Bool, bs.length = v.1.length → v.2.rowPorts bs ≤ Λ) →
    (leafCertificate mk).time x ≤
        K * ((encCall x).length + R + 1) ^ K * 2 ^ x.edges * (R + 2) ^ Λ ∧
      (leafCertificate mk).space x ≤ K * ((encCall x).length + R + 1) ^ K := by
  obtain ⟨K₁, hK₁⟩ := DescribedNetwork.contractionCertificate_le (ops := SumOps.galois)
    (eval := VertexDesc.entry) (encQ := encPair encUnary (encList encNat))
    (encY := encList encNat) (encT := VertexDesc.enc) SumOps.galois_polyTime
    VertexDesc.entryCertificate
  obtain ⟨K₂, hK₂⟩ := VertexDesc.entryCertificate_le
  have hD := NativeCertificate.ofPolyTime_isPolynomial depth_polyTime
  have hI := NativeCertificate.ofPolyTime_isPolynomial leafInput_polyTime
  obtain ⟨cd, dd, hdt⟩ := hD.1.exists_le
  obtain ⟨cd', dd', hds⟩ := hD.2.exists_le
  obtain ⟨ci, di, hit⟩ := hI.1.exists_le
  obtain ⟨ci', di', his⟩ := hI.2.exists_le
  obtain ⟨cl, dl, hl⟩ := leafInput_polyTime.polyBounded_length.exists_le
  obtain ⟨cp, dp, hp⟩ := PacketCtx.p_polyTime.polyBounded_length.exists_le
  obtain ⟨cf, df, hf⟩ := PacketCtx.fl_polyTime.polyBounded_length.exists_le
  obtain ⟨ct, dt, ht⟩ := VertexDesc.tableEntry_polyTime.polyBounded_length.exists_le
  -- The constants.
  obtain ⟨e, he⟩ : ∃ e, e = 2 + df + dp + dt := ⟨_, rfl⟩
  obtain ⟨cR, hcR⟩ : ∃ cR, cR = 5 + cf * (2 * cp + 3) + ct * 3 ^ dt := ⟨_, rfl⟩
  obtain ⟨E₀, hE₀⟩ : ∃ E₀, E₀ = dl + e := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = cl + 2 * cR + 1 := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, c₂ = 3 + cR := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = 2 * (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂)) + cd + ci +
      (K₁ * c₁ ^ K₁ + K₂ * c₂ ^ K₂) + cd' + ci' := ⟨_, rfl⟩
  obtain ⟨Dg, hDg⟩ : ∃ Dg, Dg = 1 + E₀ * (K₁ + K₂) + dd + di + dd' + di' := ⟨_, rfl⟩
  refine ⟨G + Dg, fun mk x R Λ hRΛ => ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, n = (encCall x).length := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = n + R + 1 := ⟨_, rfl⟩
  rw [← hn, show n + R + 1 = W from hW.symm]
  have hW1 : 1 ≤ W := by omega
  have hnW : n + 1 ≤ W := by omega
  -- The precision and the modulus of the call.
  have hpfl := scale_add_prec_add_length_fl_le x
  rw [← hn] at hpfl
  -- Every vertex and bit list on its ports is at most `3 n + 1` long.
  have hq (v : List ℕ × VertexDesc) (hv : v ∈ x.net.vertices) (bs : List Bool)
      (hbs : bs.length = v.1.length) :
      (encPair VertexDesc.enc encBits (v.2, bs)).length ≤ 3 * n + 1 := by
    have h1 := length_vertex_le hv
    have h2 := length_le_length_encList encNat v.1
    rw [length_encPair] at h1 ⊢
    change 2 * (VertexDesc.enc v.2).length + 1 + bs.length ≤ 3 * n + 1
    omega
  -- The reduced coefficient lists.
  obtain ⟨Rv, hRv⟩ : ∃ Rv, Rv = n * (2 * n + 3) +
      cf * (n + 1) ^ df * (2 * (cp * (n + 1) ^ dp) + 3) + ct * (3 * n + 2) ^ dt := ⟨_, rfl⟩
  have hred : ∀ y, SumOps.galois.Reduced (x.prec, x.fl) y → (encList encNat y).length ≤ Rv := by
    intro y hy
    have h := SumOps.length_encList_le_of_galois_reduced hy
    simp only at h
    have : x.fl.length * (2 * x.prec + 3) ≤ n * (2 * n + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hpacket (v : List ℕ × VertexDesc) (hv : v ∈ x.net.vertices) (d : PacketDesc)
      (hd : v.2 = .inr d) :
      ∀ y, SumOps.galois.Reduced (d.1.p, d.1.fl) y → (encList encNat y).length ≤ Rv := by
    intro y hy
    have h := SumOps.length_encList_le_of_galois_reduced hy
    simp only at h
    have h1 := length_vertex_le hv
    rw [length_encPair, hd, length_encSum] at h1
    simp only [Sum.elim_inr] at h1
    have h2 : (PacketCtx.enc d.1).length ≤ n := by
      have := length_encPair (enc₁ := PacketCtx.enc)
        (enc₂ := encPair (encList (encPair encBool encNat)) (encList encUnary)) d
      change (encPacketDesc d).length = _ at this
      omega
    have hpd : d.1.p ≤ cp * (n + 1) ^ dp := by
      have := hp d.1
      rw [encUnary_apply, List.length_replicate] at this
      exact this.trans (mul_pow_le_of_le (by omega))
    have hfd : d.1.fl.length ≤ cf * (n + 1) ^ df :=
      (length_le_length_encList encNat d.1.fl).trans ((hf d.1).trans (mul_pow_le_of_le (by omega)))
    have : d.1.fl.length * (2 * d.1.p + 3) ≤ cf * (n + 1) ^ df * (2 * (cp * (n + 1) ^ dp) + 3) :=
      Nat.mul_le_mul hfd (by omega)
    omega
  -- The entries.
  obtain ⟨Zb, hZb⟩ : ∃ Zb, Zb = 3 * n + R + Rv + 3 := ⟨_, rfl⟩
  have hentry : ∀ v ∈ ((x.prec, x.fl), x.net).2.vertices, ∀ bs : List Bool,
      bs.length = v.1.length →
      VertexDesc.entryCertificate.time (v.2, bs) ≤ K₂ * (R + 2) ^ Λ * Zb ^ K₂ ∧
        VertexDesc.entryCertificate.space (v.2, bs) ≤ K₂ * Zb ^ K₂ ∧
        (encList encNat (VertexDesc.entry v.2 bs)).length ≤ Rv := by
    intro v hv bs hbs
    have hlen := hq v hv bs hbs
    obtain ⟨hmodes, hrows⟩ := hRΛ v hv
    have hrows := hrows bs hbs
    have hRLE : v.2.ReducedLE Rv := by
      rcases hd : v.2 with t | d
      · trivial
      · exact hpacket v hv d hd
    obtain ⟨hT, hS⟩ := hK₂ (v.2, bs) Rv hRLE
    dsimp only at hT hS
    have hZ : (encPair VertexDesc.enc encBits (v.2, bs)).length + v.2.modes + Rv + 2 ≤ Zb := by
      omega
    refine ⟨hT.trans ?_, hS.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hZ _)), ?_⟩
    · refine Nat.mul_le_mul (Nat.mul_le_mul_left _ ?_) (Nat.pow_le_pow_left hZ _)
      exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hrows)
    · rcases hd : v.2 with t | d
      · have := ht (v.2, bs)
        rw [hd] at this
        refine this.trans ?_
        have h3 : (encPair VertexDesc.enc encBits (Sum.inl t, bs)).length + 1 ≤ 3 * n + 2 := by
          rw [← hd]; omega
        calc ct * ((encPair VertexDesc.enc encBits (Sum.inl t, bs)).length + 1) ^ dt
            ≤ ct * (3 * n + 2) ^ dt := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 _)
          _ ≤ Rv := by omega
      · exact hpacket v hv d hd _ (VertexDesc.reduced_entry_inr d bs)
  obtain ⟨hsT, hsS⟩ := hK₁ ((x.prec, x.fl), x.net) (K₂ * (R + 2) ^ Λ * Zb ^ K₂) (K₂ * Zb ^ K₂) Rv
    Rv hentry hred
  -- Polynomial pieces against `W`.
  have hk : x.net.vertices.length + 1 ≤ W := by have := length_vertices_le x; omega
  have hRvW : Rv ≤ cR * W ^ e := by
    rw [hRv, hcR, he]; exact rv_le hnW
  have hWE : W ^ e ≤ W ^ E₀ := Nat.pow_le_pow_right hW1 (by omega)
  have hA1 : (DescribedNetwork.encInput (encPair encUnary (encList encNat)) VertexDesc.enc
      ((x.prec, x.fl), x.net)).length + Rv + Rv + 1 ≤ c₁ * W ^ E₀ := by
    have h1 : (DescribedNetwork.encInput (encPair encUnary (encList encNat)) VertexDesc.enc
        ((x.prec, x.fl), x.net)).length ≤ cl * W ^ dl :=
      (hl x).trans (by rw [← hn]; exact mul_pow_le_of_le hnW)
    rw [hc₁]
    exact sum_le_of_le hW1 h1 (by omega) (hRvW.trans (Nat.mul_le_mul_left _ hWE))
  have hZW : Zb ≤ c₂ * W ^ E₀ := by
    rw [hc₂, hZb]
    exact zb_le hW1 (by omega) (hRvW.trans (Nat.mul_le_mul_left _ hWE)) (by omega)
  have hnW' : (encCall x).length + 1 ≤ W := by omega
  have hdt' := (hdt x).trans (mul_pow_le_of_le (c := cd) (d := dd) hnW')
  have hit' := (hit x).trans (mul_pow_le_of_le (c := ci) (d := di) hnW')
  have hds' := (hds x).trans (mul_pow_le_of_le (c := cd') (d := dd') hnW')
  have his' := (his x).trans (mul_pow_le_of_le (c := ci') (d := di') hnW')
  have hP : 1 ≤ 2 ^ x.edges := Nat.one_le_two_pow
  have hX : 1 ≤ (R + 2) ^ Λ := Nat.one_le_pow _ _ (by omega)
  refine ⟨?_, ?_⟩
  · rw [leafCertificate_time]
    refine (time_assemble hW1 hP hX hdt' hit' hsT hk hA1 hZW).trans ?_
    refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right hW1 (by omega))))
  · rw [leafCertificate_space]
    refine (space_assemble hW1 hds' his' hsS hA1 rfl hZW).trans ?_
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hW1 (by omega))

/-! ### The shape of the packets -/

/-- **The shape of the packets of a call**: every packet vertex has `i < a ≤ ⌊log₂ s⌋ / 32768`,
`2 ^ (i + 1)` tiles and at most `p` exponents per tile, and the slots of its ports are below
`2 ^ a` and distinct among its row ports. So it has at most `2 ^ (⌊log₂ s⌋ / 32768) p` target modes
and at most `2 ^ (⌊log₂ s⌋ / 32768)` row ports (`modes_le_of_packetShape`,
`rowPorts_le_of_packetShape`). -/
def PacketShape (x : Call) : Prop :=
  ∀ v ∈ x.net.vertices, ∀ d : PacketDesc, v.2 = .inr d →
    d.1.i < d.1.a ∧ d.1.a ≤ Nat.log 2 x.scale / 32768 ∧ d.1.tiles = 2 ^ (d.1.i + 1) ∧
      d.1.nb ≤ x.prec ∧ (∀ y ∈ d.2.1, y.2 < 2 ^ d.1.a) ∧ ((d.2.1.filter (·.1)).map (·.2)).Nodup

/-- **The root has no packets.** -/
theorem packetShape_root (q : ℕ × ℕ × ExplicitTensorNetwork ℕ) : PacketShape (root q) := by
  intro v hv d hd
  simp only [root, rootNet, Call.net, List.mem_map] at hv
  obtain ⟨w, -, rfl⟩ := hv
  cases hd

/-- **The packet shape passes to the native children** of a well-formed active call: a retained
vertex keeps its descriptor, at a precision that only grows, and a new packet has `a` slot bits
(`slotBits_le`), `i < a` (the valuation of its node), `2 ^ (i + 1)` tiles, the child's precision
as its number of exponents per tile, and the slots of the packing, distinct within a packet. -/
theorem packetShape_child {x : Call} (hx : WF x) (ha : active x = true) (hs : PacketShape x)
    {c : State} (hc : c ∈ children x) : PacketShape (child x nativeMk c) := by
  -- The builder at a cursor state of a well-formed active call: the uncapped native child.
  have hmk : (nativeMk x c).2 = nativeChild x.fl (slots x) (level x ((nodes x).getD c.1 0))
      (nodePrec x c.1) (node (slots x) ((nodes x).getD c.1 0)) ((points x).getD c.2.1 []) x.rows
      x.net (nativeParentPacking x.rows (slots x) x.net) c.2.2.1 c.2.2.2 := by
    rw [nativeMk_eq hx ha hc]
  obtain ⟨-, hD⟩ := hx
  obtain ⟨hj, -, hg⟩ := lt_of_mem_children hc
  have ha' := ha
  simp only [active, decide_eq_true_eq] at ha'
  obtain ⟨-, -, -, hua, -, -, -⟩ := ha'
  have hkmem : (nodes x).getD c.1 0 ∈ nodes x := by
    rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  obtain ⟨hk, -, hq⟩ := mem_nodes.mp hkmem
  have hia : level x ((nodes x).getD c.1 0) < slots x := by
    rw [level_eq hk]
    exact padicValInt_lt_of_taperMult_pos (by rwa [← mult_eq _ _ hk]) hua
  have hp : x.prec ≤ nodePrec x c.1 := by unfold nodePrec nodePrecision; omega
  intro v hv d hd
  have hv' : v ∈ (nativeChild x.fl (slots x) (level x ((nodes x).getD c.1 0)) (nodePrec x c.1)
      (node (slots x) ((nodes x).getD c.1 0)) ((points x).getD c.2.1 []) x.rows x.net
      (nativeParentPacking x.rows (slots x) x.net) c.2.2.1 (⟨c.2.2.2, hg⟩ : Fin 64)).vertices := by
    change v ∈ (nativeMk x c).2.vertices at hv
    rwa [hmk] at hv
  rcases NativeChild.desc_of_mem_nativeChild hD (pow_slots_le_edges_of_active ha) hia _ _ _ _ _
      hv' with ⟨w, hw, hvw⟩ | ⟨q, tags, hvq, hslot, hnodup⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs w hw d (hvw ▸ hd)
    exact ⟨h1, h2, h3, h4.trans hp, h5, h6⟩
  · rw [hvq] at hd
    cases hd
    exact ⟨hia, slotBits_le _ _, rfl, le_rfl, hslot, hnodup⟩

/-- The positions of a list satisfying a test are as many as its elements satisfying it. -/
private theorem length_filter_range_getD {α : Type} (l : List α) (d : α) (p : α → Bool) :
    ((List.range l.length).filter fun j => p (l.getD j d)).length = (l.filter p).length := by
  have hl : (List.range l.length).map (fun j => l.getD j d) = l := by
    refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h₂]
  conv_rhs => rw [← hl]
  rw [List.filter_map, List.length_map]
  rfl

/-- `2 ^ (⌊log₂ s⌋ / 32768)` is at most `s + 1`. -/
theorem two_pow_log_div_le (s : ℕ) : 2 ^ (Nat.log 2 s / 32768) ≤ s + 1 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · calc 2 ^ (Nat.log 2 s / 32768) ≤ 2 ^ Nat.log 2 s :=
          Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)
      _ ≤ s := Nat.pow_log_le_self 2 hs.ne'
      _ ≤ s + 1 := Nat.le_succ s

/-- **The target modes of a call with the packet shape**: at most `2 ^ (⌊log₂ s⌋ / 32768) p`. -/
theorem modes_le_of_packetShape {x : Call} (hs : PacketShape x) {v : List ℕ × VertexDesc}
    (hv : v ∈ x.net.vertices) : v.2.modes ≤ 2 ^ (Nat.log 2 x.scale / 32768) * x.prec := by
  rcases hd : v.2 with t | d
  · simp [VertexDesc.modes]
  · obtain ⟨h1, h2, h3, h4, -, -⟩ := hs v hv d hd
    simp only [VertexDesc.modes, targetModes]
    calc ((List.range (d.1.tiles * d.1.nb)).filter _).length
        ≤ (List.range (d.1.tiles * d.1.nb)).length := List.length_filter_le _ _
      _ = d.1.tiles * d.1.nb := List.length_range
      _ ≤ 2 ^ (Nat.log 2 x.scale / 32768) * x.prec := by
          rw [h3]
          exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) h4

/-- **The row ports of a call with the packet shape**: at most `2 ^ (⌊log₂ s⌋ / 32768)`, since
the slots of the row ports of a packet are distinct and below `2 ^ a`. -/
theorem rowPorts_le_of_packetShape {x : Call} (hs : PacketShape x) {v : List ℕ × VertexDesc}
    (hv : v ∈ x.net.vertices) (bs : List Bool) :
    v.2.rowPorts bs ≤ 2 ^ (Nat.log 2 x.scale / 32768) := by
  rcases hd : v.2 with t | d
  · simp [VertexDesc.rowPorts]
  · obtain ⟨-, h2, -, -, h5, h6⟩ := hs v hv d hd
    simp only [VertexDesc.rowPorts, sidePorts, List.length_map]
    have hlen := length_filter_range_getD d.2.1 (false, 0) (fun y => y.1 == true)
    rw [hlen]
    have hsub : ((d.2.1.filter (·.1)).map (·.2)).toFinset ⊆ Finset.range (2 ^ d.1.a) := by
      intro y hy
      simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hy
      obtain ⟨z, ⟨hz, -⟩, rfl⟩ := hy
      exact Finset.mem_range.mpr (h5 z hz)
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup h6, Finset.card_range, List.length_map] at hcard
    have hbeq : (d.2.1.filter fun y => y.1 == true) = d.2.1.filter (·.1) := by
      congr 1
    rw [hbeq]
    exact hcard.trans (Nat.pow_le_pow_right (by norm_num) h2)

/-- **The cost of a leaf with the packet shape.** There is `K` such that, on a call of encoded
length `n` with `M` edges, scale `s` and precision `p` with the packet shape, writing
`A = 2 ^ (⌊log₂ s⌋ / 32768)`, direct summation takes time at most
`K (n + 1) ^ K 2 ^ M (A p + 2) ^ A` and space at most `K (n + 1) ^ K`. -/
theorem leafCertificate_le_of_packetShape : ∃ K : ℕ,
    ∀ (mk : Call → State → ℕ × DescribedNetwork VertexDesc) (x : Call), PacketShape x →
      (leafCertificate mk).time x ≤ K * ((encCall x).length + 1) ^ K * 2 ^ x.edges *
          (2 ^ (Nat.log 2 x.scale / 32768) * x.prec + 2) ^ 2 ^ (Nat.log 2 x.scale / 32768) ∧
        (leafCertificate mk).space x ≤ K * ((encCall x).length + 1) ^ K := by
  obtain ⟨K, hK⟩ := leafCertificate_le
  refine ⟨2 * K, fun mk x hs => ?_⟩
  obtain ⟨hT, hS⟩ := hK mk x (2 ^ (Nat.log 2 x.scale / 32768) * x.prec)
    (2 ^ (Nat.log 2 x.scale / 32768)) fun v hv =>
      ⟨modes_le_of_packetShape hs hv, fun bs _ => rowPorts_le_of_packetShape hs hv bs⟩
  have hn := scale_add_prec_add_length_fl_le x
  have hA := two_pow_log_div_le x.scale
  have hR : (encCall x).length + 2 ^ (Nat.log 2 x.scale / 32768) * x.prec + 1 ≤
      ((encCall x).length + 1) ^ 2 := by
    have : 2 ^ (Nat.log 2 x.scale / 32768) * x.prec ≤
        ((encCall x).length + 1) * (encCall x).length := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hpow : K * ((encCall x).length + 2 ^ (Nat.log 2 x.scale / 32768) * x.prec + 1) ^ K ≤
      2 * K * ((encCall x).length + 1) ^ (2 * K) :=
    calc _ ≤ K * (((encCall x).length + 1) ^ 2) ^ K :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hR _)
      _ = K * ((encCall x).length + 1) ^ (2 * K) := by rw [← pow_mul]
      _ ≤ 2 * K * ((encCall x).length + 1) ^ (2 * K) :=
          Nat.mul_le_mul_right _ (by omega)
  exact ⟨hT.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpow)), hS.trans hpow⟩

/-! ### The leaf bound of the analysis -/

/-- `(μ + 1) ^ 2 ≤ 16 · 2 ^ (μ / 2)`. -/
private theorem succ_sq_le_two_pow (μ : ℕ) : (μ + 1) ^ 2 ≤ 16 * 2 ^ (μ / 2) := by
  have hk : μ / 4 + 1 ≤ 2 ^ (μ / 4) := Nat.lt_two_pow_self
  have h1 : μ + 1 ≤ 4 * 2 ^ (μ / 4) := by omega
  calc (μ + 1) ^ 2 ≤ (4 * 2 ^ (μ / 4)) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = 16 * 2 ^ (2 * (μ / 4)) := by rw [mul_pow, ← pow_mul, mul_comm (μ / 4)]; norm_num
    _ ≤ 16 * 2 ^ (μ / 2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **The packet factor is subexponential.** For `s ≤ m ≤ C s` and `p ≤ m ^ c`, with
`A = 2 ^ (⌊log₂ m⌋ / 32768)`, `(A p + 2) ^ A ≤ 2 ^ (K s / √⌊log₂ s⌋)` for a constant `K` depending
only on `C` and `c`: `A ≤ 2 ^ O(1) s ^ (1 / 32768)`, against `s / √⌊log₂ s⌋`. -/
theorem exists_packetFactor_le (C c : ℕ) : ∃ K : ℕ, ∀ s m p : ℕ, 2 ≤ s → s ≤ m → m ≤ C * s →
    p ≤ m ^ c → (2 ^ (Nat.log 2 m / 32768) * p + 2) ^ 2 ^ (Nat.log 2 m / 32768) ≤
      2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = Nat.log 2 C + 1 := ⟨_, rfl⟩
  refine ⟨16 * ((c₀ + 2) * (c + 1)) * 2 ^ c₀, fun s m p hs hsm hmC hp => ?_⟩
  set μ := Nat.log 2 s with hμ
  set lam := Nat.log 2 m with hlam
  set A := 2 ^ (lam / 32768) with hA
  have hm2 : 2 ≤ m := hs.trans hsm
  have hS1 : 1 ≤ Nat.sqrt μ := Nat.one_le_sqrt_log_two hs
  -- `A ≤ m` and `m < 2 ^ (λ + 1)`.
  have hAm : A ≤ m := (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)).trans
    (Nat.pow_log_le_self 2 (by omega))
  have hmlam : m < 2 ^ (lam + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  -- `λ ≤ c₀ + μ`.
  have hlamμ : lam ≤ c₀ + μ := by
    have hC : C < 2 ^ c₀ := hc₀ ▸ Nat.lt_pow_succ_log_self (by norm_num) C
    have hs' : s < 2 ^ (μ + 1) := Nat.lt_pow_succ_log_self (by norm_num) s
    have : m < 2 ^ (c₀ + μ + 1) := by
      calc m ≤ C * s := hmC
        _ < 2 ^ c₀ * 2 ^ (μ + 1) := Nat.mul_lt_mul'' hC hs'
        _ = 2 ^ (c₀ + μ + 1) := by rw [← pow_add]; ring_nf
    have := Nat.log_lt_of_lt_pow (by omega) this
    omega
  -- The base: `A p + 2 ≤ 2 ^ ((λ + 1) (c + 1) + 1)`.
  have hbase : A * p + 2 ≤ 2 ^ ((lam + 1) * (c + 1) + 1) := by
    have h1 : A * p ≤ m * m ^ c := Nat.mul_le_mul hAm hp
    have h2 : 2 ≤ m * m ^ c := by
      have : 1 ≤ m ^ c := Nat.one_le_pow _ _ (by omega)
      nlinarith
    have h3 : m * m ^ c = m ^ (c + 1) := by ring
    have h4 : m ^ (c + 1) ≤ (2 ^ (lam + 1)) ^ (c + 1) := Nat.pow_le_pow_left hmlam.le _
    calc A * p + 2 ≤ 2 * m ^ (c + 1) := by omega
      _ ≤ 2 * (2 ^ (lam + 1)) ^ (c + 1) := Nat.mul_le_mul_left _ h4
      _ = 2 ^ ((lam + 1) * (c + 1) + 1) := by rw [← pow_mul]; ring
  -- The exponent.
  have hA' : A ≤ 2 ^ c₀ * 2 ^ (μ / 32768) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hE : ((lam + 1) * (c + 1) + 1) * A * Nat.sqrt μ ≤
      16 * ((c₀ + 2) * (c + 1)) * 2 ^ c₀ * s := by
    have h1 : (lam + 1) * (c + 1) + 1 ≤ (c₀ + 2) * (c + 1) * (μ + 1) := by
      have : lam + 1 ≤ (c₀ + 1) * (μ + 1) := by nlinarith
      nlinarith
    have h2 : Nat.sqrt μ ≤ μ + 1 := (Nat.sqrt_le_self μ).trans (Nat.le_succ μ)
    have h3 := succ_sq_le_two_pow μ
    have h4 : 2 ^ (μ / 2) * 2 ^ (μ / 32768) ≤ 2 ^ μ := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : 2 ^ μ ≤ s := Nat.pow_log_le_self 2 (by omega)
    calc ((lam + 1) * (c + 1) + 1) * A * Nat.sqrt μ
        ≤ ((c₀ + 2) * (c + 1) * (μ + 1)) * (2 ^ c₀ * 2 ^ (μ / 32768)) * (μ + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 hA') h2
      _ = (c₀ + 2) * (c + 1) * 2 ^ c₀ * ((μ + 1) ^ 2 * 2 ^ (μ / 32768)) := by ring
      _ ≤ (c₀ + 2) * (c + 1) * 2 ^ c₀ * (16 * 2 ^ (μ / 2) * 2 ^ (μ / 32768)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h3)
      _ = 16 * ((c₀ + 2) * (c + 1)) * 2 ^ c₀ * (2 ^ (μ / 2) * 2 ^ (μ / 32768)) := by ring
      _ ≤ 16 * ((c₀ + 2) * (c + 1)) * 2 ^ c₀ * s := Nat.mul_le_mul_left _ (h4.trans h5)
  have hE' : ((lam + 1) * (c + 1) + 1) * A ≤ 16 * ((c₀ + 2) * (c + 1)) * 2 ^ c₀ * s / Nat.sqrt μ :=
    (Nat.le_div_iff_mul_le (by omega)).mpr hE
  calc (A * p + 2) ^ A ≤ (2 ^ ((lam + 1) * (c + 1) + 1)) ^ A := Nat.pow_le_pow_left hbase _
    _ = 2 ^ (((lam + 1) * (c + 1) + 1) * A) := by rw [← pow_mul]
    _ ≤ 2 ^ (16 * ((c₀ + 2) * (c + 1)) * 2 ^ c₀ * s / Nat.sqrt μ) :=
        Nat.pow_le_pow_right (by norm_num) hE'

/-- **The leaf bound of the resource analysis.** For all constants `C`, `c` and `s₀` there is `K`
such that a call with the packet shape, scale `m` with `s ≤ m ≤ C s` and at most `2 m` edges takes
time at most `K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` and space at most `K (n + 1) ^ K` at a leaf,
provided that from `s₀` on it has at most `leafSize m` edges and precision at most `m ^ c`. Below
`s₀`, the scale is bounded, so the packet factor is polynomial and `2 ^ M` is a constant; from
`s₀` on, `2 ^ M ≤ 2 ^ (C s / √⌊log₂ s⌋)` and the packet factor is subexponential
(`exists_packetFactor_le`). -/
theorem exists_leafCertificate_le (C c s₀ : ℕ) : ∃ K : ℕ,
    ∀ (mk : Call → State → ℕ × DescribedNetwork VertexDesc) (s : ℕ) (x : Call), 2 ≤ s →
      s ≤ x.scale → x.scale ≤ C * s → PacketShape x → x.edges ≤ 2 * x.scale →
      (s₀ ≤ s → x.edges ≤ leafSize x.scale ∧ x.prec ≤ x.scale ^ c) →
      (leafCertificate mk).time x ≤
          K * ((encCall x).length + 1) ^ K * 2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) ∧
        (leafCertificate mk).space x ≤ K * ((encCall x).length + 1) ^ K := by
  obtain ⟨K₀, hK₀⟩ := leafCertificate_le_of_packetShape
  obtain ⟨K₁, hK₁⟩ := exists_packetFactor_le C c
  obtain ⟨Ks, hKs⟩ : ∃ Ks, Ks = K₀ * 2 ^ (2 * (C * s₀)) * (C * s₀ + 2) ^ (C * s₀) := ⟨_, rfl⟩
  refine ⟨Ks + K₀ + C * s₀ + C + K₁, fun mk s x hs hsm hmC hshape hM hbig => ?_⟩
  obtain ⟨hT, hS⟩ := hK₀ mk x hshape
  set n := (encCall x).length with hn
  set K := Ks + K₀ + C * s₀ + C + K₁ with hK
  set S := Nat.sqrt (Nat.log 2 s) with hSdef
  have hS1 : 1 ≤ S := Nat.one_le_sqrt_log_two hs
  have hB1 : 1 ≤ n + 1 := by omega
  have hX1 : 1 ≤ 2 ^ (K * s / S) := Nat.one_le_two_pow
  have hnK : (n + 1) ^ K₀ ≤ (n + 1) ^ K := Nat.pow_le_pow_right hB1 (by omega)
  refine ⟨?_, hS.trans (Nat.mul_le_mul (by omega) hnK)⟩
  set A := 2 ^ (Nat.log 2 x.scale / 32768) with hA
  have hAm : A ≤ x.scale := (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)).trans
    (Nat.pow_log_le_self 2 (by omega))
  rcases lt_or_ge s s₀ with hsmall | hlarge
  · -- Below `s₀`: constants and a polynomial.
    have hmC' : x.scale ≤ C * s₀ := hmC.trans (Nat.mul_le_mul_left _ hsmall.le)
    have hp : x.prec ≤ n := by have := scale_add_prec_add_length_fl_le x; omega
    have h2M : 2 ^ x.edges ≤ 2 ^ (2 * (C * s₀)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hbase : A * x.prec + 2 ≤ (C * s₀ + 2) * (n + 1) := by
      have : A * x.prec ≤ C * s₀ * n := Nat.mul_le_mul (hAm.trans hmC') hp
      nlinarith
    have hfac : (A * x.prec + 2) ^ A ≤ (C * s₀ + 2) ^ (C * s₀) * (n + 1) ^ (C * s₀) := by
      calc (A * x.prec + 2) ^ A ≤ ((C * s₀ + 2) * (n + 1)) ^ A := Nat.pow_le_pow_left hbase _
        _ ≤ ((C * s₀ + 2) * (n + 1)) ^ (C * s₀) :=
            Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr (by positivity)) (hAm.trans hmC')
        _ = (C * s₀ + 2) ^ (C * s₀) * (n + 1) ^ (C * s₀) := mul_pow _ _ _
    calc (leafCertificate mk).time x ≤ K₀ * (n + 1) ^ K₀ * 2 ^ x.edges * (A * x.prec + 2) ^ A := hT
      _ ≤ K₀ * (n + 1) ^ K₀ * 2 ^ (2 * (C * s₀)) *
            ((C * s₀ + 2) ^ (C * s₀) * (n + 1) ^ (C * s₀)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h2M) hfac
      _ = Ks * (n + 1) ^ (K₀ + C * s₀) := by rw [hKs, pow_add]; ring
      _ ≤ K * (n + 1) ^ K := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hB1 (by omega))
      _ ≤ K * (n + 1) ^ K * 2 ^ (K * s / S) := Nat.le_mul_of_pos_right _ hX1
  · -- From `s₀` on: the leaf size and the packet factor.
    obtain ⟨hleaf, hp⟩ := hbig hlarge
    have hlog : S ≤ Nat.sqrt (Nat.log 2 x.scale) := Nat.sqrt_log_two_mono hsm
    have hMs : x.edges ≤ C * s / S :=
      calc x.edges ≤ x.scale / Nat.sqrt (Nat.log 2 x.scale) := hleaf
        _ ≤ x.scale / S := Nat.div_le_div_left hlog hS1
        _ ≤ C * s / S := Nat.div_le_div_right hmC
    have hfac := hK₁ s x.scale x.prec hs hsm hmC hp
    have hCK : (C + K₁) * s ≤ K * s := Nat.mul_le_mul_right _ (by omega)
    have hexp : C * s / S + K₁ * s / S ≤ K * s / S :=
      Nat.div_add_div_le_add_div.trans (Nat.div_le_div_right (by rw [← add_mul]; exact hCK))
    calc (leafCertificate mk).time x ≤ K₀ * (n + 1) ^ K₀ * 2 ^ x.edges * (A * x.prec + 2) ^ A := hT
      _ ≤ K₀ * (n + 1) ^ K₀ * 2 ^ (C * s / S) * 2 ^ (K₁ * s / S) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hMs)) hfac
      _ = K₀ * (n + 1) ^ K₀ * 2 ^ (C * s / S + K₁ * s / S) := by rw [pow_add]; ring
      _ ≤ K * (n + 1) ^ K * 2 ^ (K * s / S) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) hnK) (Nat.pow_le_pow_right (by norm_num) hexp)

end FastContraction

end Cslib.Circuits.Frontier
