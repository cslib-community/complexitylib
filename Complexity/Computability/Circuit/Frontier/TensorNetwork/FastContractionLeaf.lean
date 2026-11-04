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
(`Cslib.Circuits.Frontier.FastContraction.leafCertificate ce`, for a native certificate `ce` of the
entry procedure of the roots), the leaf clause of the resource analysis
`Cslib.Complexity.CountingSimulation.FastAnalysis`. A leaf sums directly over the `2 ^ M` edge
assignments of a call with `M` edges, with polynomially many entry evaluations each (§D.4.7,
p. 64). The entry of a packet vertex costs `(m + 2) ^ L` for `m` target modes and `L` row ports,
the source's `exp(O(L log s))` (§D.4.6, p. 63), and the entry of a root costs what `ce` costs.

**The cost of a leaf** (`FastContraction.leafCertificate_le`): with at most `R` target modes and
`Λ` row ports per vertex, and roots costing time at most `E` and space at most `ES` in `ce`, time
`K (n + R + ES + 1) ^ K 2 ^ M ((R + 2) ^ Λ + E)` and space `K (n + R + ES + 1) ^ K` on a call of
encoded length `n`, from the bounds of direct summation
(`DescribedNetwork.contractionCertificate_le`) and of the evaluator of descriptors
(`VertexDesc.entryCertificate_le`). A root's output is at most a constant times `ES + 1` long,
since a native certificate charges its output to its space bound. For tables the root costs are
polynomial, which gives time `K (n + 1) ^ K 2 ^ M (A p + 2) ^ A` with the packet shape
(`FastContraction.leafCertificate_tableEntry_le_of_packetShape`).

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
but a polynomial in `n` is a constant (`FastContraction.exists_leafFactor_le`). With an entry
procedure whose roots cost time `E` and space `ES`, the leaf takes time
`K (n + ES + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋) (E + 1)` and space `K (n + ES + 1) ^ K`
(`FastContraction.exists_leafCertificate_le_of_entry`).

## Main definitions

* `Cslib.Circuits.Frontier.FastContraction.PacketShape`: the shape of the packets of a call.

## Main results

* `Cslib.Circuits.Frontier.FastContraction.leafCertificate_le`: the cost of a leaf.
* `Cslib.Circuits.Frontier.FastContraction.packetShape_root`,
  `Cslib.Circuits.Frontier.FastContraction.packetShape_child`: the packet shape on the reached
  calls.
* `Cslib.Circuits.Frontier.FastContraction.leafCertificate_le_of_packetShape`,
  `Cslib.Circuits.Frontier.FastContraction.leafCertificate_tableEntry_le_of_packetShape`: the cost
  of a leaf with the packet shape, and over tables.
* `Cslib.Circuits.Frontier.FastContraction.exists_leafFactor_le`: the factor `2 ^ M (A p + 2) ^ A`
  is subexponential.
* `Cslib.Circuits.Frontier.FastContraction.exists_leafCertificate_le`,
  `Cslib.Circuits.Frontier.FastContraction.exists_leafCertificate_le_of_entry`: the leaf bound of
  the resource analysis, over tables and with the costs of the root entries.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.6–§D.4.7,
  pp. 63–64.
-/

public section

namespace Cslib.Circuits.Frontier

namespace FastContraction

open GaloisRingArith NativePacket ChildCursor NativeRecovery ContractionSchedule NativeChild
  Cslib.GenericRAM Cslib.GenericRAM.StackRecursion Turing.MultiTapeTM

variable {T : Type}

/-! ### Encoded lengths -/

section Lengths

variable (encT : T ↪ List Bool)

/-- The scale, the precision and the coefficients of the modulus are at most the encoded length
of a call. -/
theorem scale_add_prec_add_length_fl_le (x : Call T) :
    x.scale + x.prec + x.fl.length ≤ (encCall encT x).length := by
  have h := length_le_length_encList encNat x.fl
  obtain ⟨⟨s, d, b, p, fl, r⟩, D⟩ := x
  simp only [Call.scale, Call.prec, Call.fl, encCall, encParams, length_encPair, encUnary_apply,
    List.length_replicate] at h ⊢
  omega

/-- The network of a call is at most its encoded length. -/
theorem length_net_le (x : Call T) :
    (DescribedNetwork.encDescribed (VertexDesc.enc encT) x.net).length ≤
      (encCall encT x).length := by
  obtain ⟨p, D⟩ := x
  simp only [Call.net, encCall, length_encPair]
  omega

/-- A vertex of a call is at most its encoded length. -/
theorem length_vertex_le {x : Call T} {v : List ℕ × VertexDesc T}
    (hv : v ∈ x.net.vertices) :
    (encPair (encList encNat) (VertexDesc.enc encT) v).length ≤ (encCall encT x).length := by
  have h := length_le_encList_of_mem (encPair (encList encNat) (VertexDesc.enc encT)) hv
  have h2 : (encList (encPair (encList encNat) (VertexDesc.enc encT)) x.net.vertices).length ≤
      (DescribedNetwork.encDescribed (VertexDesc.enc encT) x.net).length := by
    change _ ≤ (encPair encUnary (encList (encPair (encList encNat) (VertexDesc.enc encT)))
      (x.net.numEdges, x.net.vertices)).length
    rw [length_encPair]
    dsimp only
    omega
  have h3 := length_net_le encT x
  omega

/-- The number of vertices of a call is at most its encoded length. -/
theorem length_vertices_le (x : Call T) :
    x.net.vertices.length ≤ (encCall encT x).length := by
  have h := DescribedNetwork.length_numEdges_vertices_le (encT := VertexDesc.enc encT) x.net
  have h3 := length_net_le encT x
  omega

end Lengths

/-! ### The cost of a leaf -/

/-- `c (y + 1) ^ d ≤ c W ^ d` when `y + 1 ≤ W`. -/
private theorem mul_pow_le_of_le {c y d W : ℕ} (hy : y + 1 ≤ W) : c * (y + 1) ^ d ≤ c * W ^ d :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hy _)

/-- Raising the exponent of `W ≥ 1`. -/
private theorem mul_pow_le_mul_pow {c W d E : ℕ} (hW : 1 ≤ W) (hd : d ≤ E) :
    c * W ^ d ≤ c * W ^ E :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW hd)

/-- The reduced coefficient lists against `W`. -/
private theorem rv_le {n W cf df cp dp : ℕ} (hnW : n + 1 ≤ W) :
    n * (2 * n + 3) + cf * (n + 1) ^ df * (2 * (cp * (n + 1) ^ dp) + 3) ≤
      (5 + cf * (2 * cp + 3)) * W ^ (2 + df + dp) := by
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
  have l1 : 5 * W ^ 2 ≤ 5 * W ^ (2 + df + dp) := mul_pow_le_mul_pow hW1 (by omega)
  have l2 : cf * (2 * cp + 3) * W ^ (df + dp) ≤ cf * (2 * cp + 3) * W ^ (2 + df + dp) :=
    mul_pow_le_mul_pow hW1 (by omega)
  rw [add_mul]
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
private theorem time_assemble {Td Ti Ts cd dd ci di P X E k W A Zb c₁ c₂ E₀ K₁ K₂ : ℕ}
    (hW : 1 ≤ W) (hP : 1 ≤ P) (hX : 1 ≤ X) (hd : Td ≤ cd * W ^ dd) (hi : Ti ≤ ci * W ^ di)
    (hs : Ts ≤ (P * (k + 1) + 1) * (K₁ * (A + 1) ^ K₁ + 2 * (K₂ * X * Zb ^ K₂ + E)))
    (hk : k + 1 ≤ W) (hA : A + 1 ≤ c₁ * W ^ E₀) (hZ : Zb ≤ c₂ * W ^ E₀) :
    Td + (Ti + Ts) ≤ (2 * (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂) + 2) + cd + ci) *
      W ^ (1 + E₀ * (K₁ + K₂) + dd + di) * P * (X + E) := by
  have hWF1 : W ^ (E₀ * K₁) ≤ W ^ (E₀ * (K₁ + K₂)) :=
    Nat.pow_le_pow_right hW (by rw [Nat.mul_add]; omega)
  have hWF2 : W ^ (E₀ * K₂) ≤ W ^ (E₀ * (K₁ + K₂)) :=
    Nat.pow_le_pow_right hW (by rw [Nat.mul_add]; omega)
  set F := E₀ * (K₁ + K₂)
  set S := W ^ (1 + F + dd + di)
  set Y := X + E with hY
  have hY1 : 1 ≤ Y := by omega
  have hF1 : 1 ≤ W ^ F := Nat.one_le_pow _ _ (by omega)
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
  have hin : K₁ * (A + 1) ^ K₁ + 2 * (K₂ * X * Zb ^ K₂ + E) ≤
      (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂) + 2) * Y * W ^ F := by
    have h1 : K₁ * c₁ ^ K₁ * W ^ F ≤ K₁ * c₁ ^ K₁ * W ^ F * Y := Nat.le_mul_of_pos_right _ hY1
    have h2 : K₂ * c₂ ^ K₂ * X * W ^ F ≤ K₂ * c₂ ^ K₂ * Y * W ^ F :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    have h3 : E ≤ Y * W ^ F := (show E ≤ Y by omega).trans (Nat.le_mul_of_pos_right _ hF1)
    have e : (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂) + 2) * Y * W ^ F =
        K₁ * c₁ ^ K₁ * W ^ F * Y + 2 * (K₂ * c₂ ^ K₂ * Y * W ^ F) + 2 * (Y * W ^ F) := by ring
    omega
  have hPk : P * (k + 1) + 1 ≤ 2 * P * W := by
    have : P * (k + 1) ≤ P * W := Nat.mul_le_mul_left _ hk
    have : 1 ≤ P * W := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [Nat.mul_assoc]; omega
  have hs' : Ts ≤ 2 * (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂) + 2) * S * P * Y :=
    calc Ts ≤ (2 * P * W) * ((K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂) + 2) * Y * W ^ F) :=
          hs.trans (Nat.mul_le_mul hPk hin)
      _ = 2 * (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂) + 2) * W ^ (1 + F) * P * Y := by
          rw [pow_add, pow_one]; ring
      _ ≤ 2 * (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂) + 2) * S * P * Y :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW (by omega))))
  have hPY : 1 ≤ P * Y := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hd' : Td ≤ cd * S * P * Y :=
    calc Td ≤ cd * S := hd.trans (mul_pow_le_mul_pow hW (by omega))
      _ ≤ cd * S * (P * Y) := Nat.le_mul_of_pos_right _ hPY
      _ = cd * S * P * Y := by ring
  have hi' : Ti ≤ ci * S * P * Y :=
    calc Ti ≤ ci * S := hi.trans (mul_pow_le_mul_pow hW (by omega))
      _ ≤ ci * S * (P * Y) := Nat.le_mul_of_pos_right _ hPY
      _ = ci * S * P * Y := by ring
  have e : (2 * (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂) + 2) + cd + ci) * S * P * Y =
      2 * (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂) + 2) * S * P * Y + cd * S * P * Y +
        ci * S * P * Y := by
    ring
  omega

/-- The arithmetic of the space of a leaf. -/
private theorem space_assemble {Sd Si Ss cd dd ci di W A Zb c₁ c₂ E₀ K₁ K₂ ES ES' : ℕ}
    (hW : 1 ≤ W) (hd : Sd ≤ cd * W ^ dd) (hi : Si ≤ ci * W ^ di)
    (hs : Ss ≤ K₁ * (A + 1) ^ K₁ + ES') (hA : A + 1 ≤ c₁ * W ^ E₀)
    (hES : ES' = K₂ * Zb ^ K₂ + ES) (hESW : ES ≤ W) (hZ : Zb ≤ c₂ * W ^ E₀) :
    Sd + (Si + Ss) ≤ (K₁ * c₁ ^ K₁ + K₂ * c₂ ^ K₂ + cd + ci + 1) *
      W ^ (1 + E₀ * (K₁ + K₂) + dd + di) := by
  have hWF1 : W ^ (E₀ * K₁) ≤ W ^ (1 + E₀ * (K₁ + K₂) + dd + di) :=
    Nat.pow_le_pow_right hW (by rw [Nat.mul_add]; omega)
  have hWF2 : W ^ (E₀ * K₂) ≤ W ^ (1 + E₀ * (K₁ + K₂) + dd + di) :=
    Nat.pow_le_pow_right hW (by rw [Nat.mul_add]; omega)
  set F := E₀ * (K₁ + K₂)
  set S := W ^ (1 + F + dd + di)
  have hA' : K₁ * (A + 1) ^ K₁ ≤ K₁ * c₁ ^ K₁ * S :=
    calc K₁ * (A + 1) ^ K₁ ≤ K₁ * (c₁ * W ^ E₀) ^ K₁ :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA _)
      _ = K₁ * c₁ ^ K₁ * W ^ (E₀ * K₁) := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]
      _ ≤ K₁ * c₁ ^ K₁ * S := Nat.mul_le_mul_left _ hWF1
  have hZ' : K₂ * Zb ^ K₂ ≤ K₂ * c₂ ^ K₂ * S :=
    calc K₂ * Zb ^ K₂ ≤ K₂ * (c₂ * W ^ E₀) ^ K₂ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hZ _)
      _ = K₂ * c₂ ^ K₂ * W ^ (E₀ * K₂) := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]
      _ ≤ K₂ * c₂ ^ K₂ * S := Nat.mul_le_mul_left _ hWF2
  have hWS : ES ≤ S :=
    hESW.trans ((pow_one W).symm.le.trans (Nat.pow_le_pow_right hW (by omega)))
  have hd' : Sd ≤ cd * S := hd.trans (mul_pow_le_mul_pow hW (by omega))
  have hi' : Si ≤ ci * S := hi.trans (mul_pow_le_mul_pow hW (by omega))
  have e : (K₁ * c₁ ^ K₁ + K₂ * c₂ ^ K₂ + cd + ci + 1) * S =
      K₁ * c₁ ^ K₁ * S + K₂ * c₂ ^ K₂ * S + cd * S + ci * S + S := by ring
  omega

variable {encT : T ↪ List Bool} {ev : T → List Bool → List ℕ}

/-- **The cost of a leaf.** For a native certificate `ce` of the entry procedure of the roots, there
is `K` such that, on a call of encoded length `n` with `M` edges whose vertices have at most `R`
target modes and at most `Λ` row ports on every bit list on their ports, and whose roots take time
at most `E` and space at most `ES` in `ce` on every bit list on their ports, direct summation takes
time at most `K (n + R + ES + 1) ^ K 2 ^ M ((R + 2) ^ Λ + E)` and space at most
`K (n + R + ES + 1) ^ K`, whatever the child builder. -/
theorem leafCertificate_le
    (ce : NativeCertificate (fun q : T × List Bool => ev q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    ∃ K : ℕ, ∀ (mk : Call T → State → ℕ × DescribedNetwork (VertexDesc T)) (x : Call T)
      (R Λ E ES : ℕ),
      (∀ v ∈ x.net.vertices, v.2.modes ≤ R ∧
        ∀ bs : List Bool, bs.length = v.1.length → v.2.rowPorts bs ≤ Λ) →
      (∀ v ∈ x.net.vertices, ∀ t, v.2 = .inl t → ∀ bs : List Bool, bs.length = v.1.length →
        ce.time (t, bs) ≤ E ∧ ce.space (t, bs) ≤ ES) →
      (leafCertificate ce mk).time x ≤
          K * ((encCall encT x).length + R + ES + 1) ^ K * 2 ^ x.edges * ((R + 2) ^ Λ + E) ∧
        (leafCertificate ce mk).space x ≤ K * ((encCall encT x).length + R + ES + 1) ^ K := by
  obtain ⟨K₁, hK₁⟩ := DescribedNetwork.contractionCertificate_le (ops := SumOps.galois)
    (eval := VertexDesc.entry ev) (encQ := encPair encUnary (encList encNat))
    (encY := encList encNat) (encT := VertexDesc.enc encT) SumOps.galois_polyTime
    (VertexDesc.entryCertificate ce)
  obtain ⟨K₂, hK₂⟩ := VertexDesc.entryCertificate_le ce
  obtain ⟨cE, -, hcE⟩ := ce.computes
  have hD := NativeCertificate.ofPolyTime_isPolynomial (depth_polyTime encT)
  have hI := NativeCertificate.ofPolyTime_isPolynomial (leafInput_polyTime encT)
  obtain ⟨cd, dd, hdt⟩ := hD.1.exists_le
  obtain ⟨cd', dd', hds⟩ := hD.2.exists_le
  obtain ⟨ci, di, hit⟩ := hI.1.exists_le
  obtain ⟨ci', di', his⟩ := hI.2.exists_le
  obtain ⟨cl, dl, hl⟩ := (leafInput_polyTime encT).polyBounded_length.exists_le
  obtain ⟨cp, dp, hp⟩ := PacketCtx.p_polyTime.polyBounded_length.exists_le
  obtain ⟨cf, df, hf⟩ := PacketCtx.fl_polyTime.polyBounded_length.exists_le
  -- The constants.
  obtain ⟨e, he⟩ : ∃ e, e = 2 + df + dp := ⟨_, rfl⟩
  obtain ⟨cR, hcR⟩ : ∃ cR, cR = 5 + cf * (2 * cp + 3) + cE := ⟨_, rfl⟩
  obtain ⟨E₀, hE₀⟩ : ∃ E₀, E₀ = dl + e := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = cl + 2 * cR + 1 := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, c₂ = 3 + cR := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = 2 * (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂) + 2) + cd + ci +
      (K₁ * c₁ ^ K₁ + K₂ * c₂ ^ K₂ + cd' + ci' + 1) := ⟨_, rfl⟩
  obtain ⟨Dg, hDg⟩ : ∃ Dg, Dg = 1 + E₀ * (K₁ + K₂) + dd + di + dd' + di' := ⟨_, rfl⟩
  refine ⟨G + Dg, fun mk x R Λ E ES hRΛ hroot => ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, n = (encCall encT x).length := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = n + R + ES + 1 := ⟨_, rfl⟩
  rw [← hn, show n + R + ES + 1 = W from hW.symm]
  have hW1 : 1 ≤ W := by omega
  have hnW : n + 1 ≤ W := by omega
  -- The precision and the modulus of the call.
  have hpfl := scale_add_prec_add_length_fl_le encT x
  rw [← hn] at hpfl
  -- Every vertex and bit list on its ports is at most `3 n + 1` long.
  have hq (v : List ℕ × VertexDesc T) (hv : v ∈ x.net.vertices) (bs : List Bool)
      (hbs : bs.length = v.1.length) :
      (encPair (VertexDesc.enc encT) encBits (v.2, bs)).length ≤ 3 * n + 1 := by
    have h1 := length_vertex_le encT hv
    have h2 := length_le_length_encList encNat v.1
    rw [length_encPair] at h1 ⊢
    change 2 * (VertexDesc.enc encT v.2).length + 1 + bs.length ≤ 3 * n + 1
    omega
  -- The reduced coefficient lists, and the outputs of the roots.
  obtain ⟨Rv, hRv⟩ : ∃ Rv, Rv = n * (2 * n + 3) +
      cf * (n + 1) ^ df * (2 * (cp * (n + 1) ^ dp) + 3) := ⟨_, rfl⟩
  obtain ⟨Ev, hEv⟩ : ∃ Ev, Ev = Rv + cE * (ES + 1) := ⟨_, rfl⟩
  have hred : ∀ y, SumOps.galois.Reduced (x.prec, x.fl) y → (encList encNat y).length ≤ Rv := by
    intro y hy
    have h := SumOps.length_encList_le_of_galois_reduced hy
    simp only at h
    have : x.fl.length * (2 * x.prec + 3) ≤ n * (2 * n + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hpacket (v : List ℕ × VertexDesc T) (hv : v ∈ x.net.vertices) (d : PacketDesc)
      (hd : v.2 = .inr d) :
      ∀ y, SumOps.galois.Reduced (d.1.p, d.1.fl) y → (encList encNat y).length ≤ Rv := by
    intro y hy
    have h := SumOps.length_encList_le_of_galois_reduced hy
    simp only at h
    have h1 := length_vertex_le encT hv
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
      (VertexDesc.entryCertificate ce).time (v.2, bs) ≤ K₂ * (R + 2) ^ Λ * Zb ^ K₂ + E ∧
        (VertexDesc.entryCertificate ce).space (v.2, bs) ≤ K₂ * Zb ^ K₂ + ES ∧
        (encList encNat (VertexDesc.entry ev v.2 bs)).length ≤ Ev := by
    intro v hv bs hbs
    have hlen := hq v hv bs hbs
    obtain ⟨hmodes, hrows⟩ := hRΛ v hv
    have hrows := hrows bs hbs
    have hRLE : v.2.ReducedLE Rv := by
      rcases hd : v.2 with t | d
      · trivial
      · exact hpacket v hv d hd
    obtain ⟨hT, hS⟩ := hK₂ (v.2, bs) Rv E ES hRLE fun t ht => hroot v hv t ht bs hbs
    dsimp only at hT hS
    have hZ : (encPair (VertexDesc.enc encT) encBits (v.2, bs)).length + v.2.modes + Rv + 2 ≤
        Zb := by
      omega
    refine ⟨hT.trans (Nat.add_le_add_right ?_ _),
      hS.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hZ _)) _), ?_⟩
    · refine Nat.mul_le_mul (Nat.mul_le_mul_left _ ?_) (Nat.pow_le_pow_left hZ _)
      exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hrows)
    · rcases hd : v.2 with t | d
      · have h1 : (encList encNat (ev t bs)).length ≤ cE * (ce.space (t, bs) + 1) := hcE (t, bs)
        have h2 : cE * (ce.space (t, bs) + 1) ≤ cE * (ES + 1) :=
          Nat.mul_le_mul_left _ (by have := (hroot v hv t hd bs hbs).2; omega)
        simp only [VertexDesc.entry_inl]
        omega
      · have := hpacket v hv d hd _ (VertexDesc.reduced_entry_inr ev d bs)
        omega
  obtain ⟨hsT, hsS⟩ := hK₁ ((x.prec, x.fl), x.net) (K₂ * (R + 2) ^ Λ * Zb ^ K₂ + E)
    (K₂ * Zb ^ K₂ + ES) Ev Rv hentry hred
  -- Polynomial pieces against `W`.
  have hk : x.net.vertices.length + 1 ≤ W := by have := length_vertices_le encT x; omega
  have hRvW : Rv ≤ (cR - cE) * W ^ e := by
    have h := rv_le (cf := cf) (df := df) (cp := cp) (dp := dp) hnW
    rw [hRv, he]
    refine h.trans (Nat.mul_le_mul_right _ ?_)
    omega
  have hWE : W ^ e ≤ W ^ E₀ := Nat.pow_le_pow_right hW1 (by omega)
  have hW1E : W ≤ W ^ E₀ :=
    (pow_one W).symm.le.trans (Nat.pow_le_pow_right hW1 (by omega))
  have hEvW : Ev ≤ cR * W ^ E₀ := by
    have h1 : Rv ≤ (cR - cE) * W ^ E₀ := hRvW.trans (Nat.mul_le_mul_left _ hWE)
    have h2 : cE * (ES + 1) ≤ cE * W ^ E₀ := Nat.mul_le_mul_left _ (by omega)
    have e : cR * W ^ E₀ = (cR - cE) * W ^ E₀ + cE * W ^ E₀ := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
    omega
  have hA1 : (DescribedNetwork.encInput (encPair encUnary (encList encNat))
      (VertexDesc.enc encT) ((x.prec, x.fl), x.net)).length + Ev + Rv + 1 ≤ c₁ * W ^ E₀ := by
    have h1 : (DescribedNetwork.encInput (encPair encUnary (encList encNat))
        (VertexDesc.enc encT) ((x.prec, x.fl), x.net)).length ≤ cl * W ^ dl :=
      (hl x).trans (by rw [← hn]; exact mul_pow_le_of_le hnW)
    have h2 : Rv ≤ Ev := by omega
    have h3 := sum_le_of_le hW1 h1 (by omega) hEvW
    rw [hc₁]
    omega
  have hZW : Zb ≤ c₂ * W ^ E₀ := by
    rw [hc₂, hZb]
    have h1 : Rv ≤ cR * W ^ E₀ := by
      have := hRvW.trans (Nat.mul_le_mul_left _ hWE)
      exact this.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    exact zb_le hW1 (by omega) h1 (by omega)
  have hnW' : (encCall encT x).length + 1 ≤ W := by omega
  have hdt' := (hdt x).trans (mul_pow_le_of_le (c := cd) (d := dd) hnW')
  have hit' := (hit x).trans (mul_pow_le_of_le (c := ci) (d := di) hnW')
  have hds' := (hds x).trans (mul_pow_le_of_le (c := cd') (d := dd') hnW')
  have his' := (his x).trans (mul_pow_le_of_le (c := ci') (d := di') hnW')
  have hP : 1 ≤ 2 ^ x.edges := Nat.one_le_two_pow
  have hX : 1 ≤ (R + 2) ^ Λ := Nat.one_le_pow _ _ (by omega)
  refine ⟨?_, ?_⟩
  · rw [leafCertificate_time]
    refine (time_assemble hW1 hP hX hdt' hit' hsT hk (by omega) hZW).trans ?_
    have hpow : W ^ (1 + E₀ * (K₁ + K₂) + dd + di) ≤ W ^ (G + Dg) :=
      Nat.pow_le_pow_right hW1 (by omega)
    calc _ = (2 * (K₁ * c₁ ^ K₁ + 2 * (K₂ * c₂ ^ K₂) + 2) + cd + ci) *
          W ^ (1 + E₀ * (K₁ + K₂) + dd + di) * (2 ^ x.edges * ((R + 2) ^ Λ + E)) := by ring
      _ ≤ (G + Dg) * W ^ (G + Dg) * (2 ^ x.edges * ((R + 2) ^ Λ + E)) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) hpow)
      _ = _ := by ring
  · rw [leafCertificate_space]
    refine (space_assemble hW1 hds' his' hsS (by omega) rfl (by omega) hZW).trans ?_
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hW1 (by omega))

/-! ### The shape of the packets -/

/-- **The shape of the packets of a call**: every packet vertex has `i < a ≤ ⌊log₂ s⌋ / 32768`,
`2 ^ (i + 1)` tiles and at most `p` exponents per tile, and the slots of its ports are below
`2 ^ a` and distinct among its row ports. So it has at most `2 ^ (⌊log₂ s⌋ / 32768) p` target modes
and at most `2 ^ (⌊log₂ s⌋ / 32768)` row ports (`modes_le_of_packetShape`,
`rowPorts_le_of_packetShape`). -/
def PacketShape (x : Call T) : Prop :=
  ∀ v ∈ x.net.vertices, ∀ d : PacketDesc, v.2 = .inr d →
    d.1.i < d.1.a ∧ d.1.a ≤ Nat.log 2 x.scale / 32768 ∧ d.1.tiles = 2 ^ (d.1.i + 1) ∧
      d.1.nb ≤ x.prec ∧ (∀ y ∈ d.2.1, y.2 < 2 ^ d.1.a) ∧ ((d.2.1.filter (·.1)).map (·.2)).Nodup

/-- **A call on a root network has no packets**: its descriptors are those of a network
`G`, by `rootNet G`. -/
theorem packetShape_of_net_eq_rootNet {x : Call T} {G : DescribedNetwork T}
    (h : x.net = rootNet G) : PacketShape x := by
  intro v hv d hd
  rw [h] at hv
  simp only [rootNet, List.mem_map] at hv
  obtain ⟨w, -, rfl⟩ := hv
  cases hd

/-- **The root has no packets.** -/
theorem packetShape_root (q : ℕ × ℕ × ExplicitTensorNetwork ℕ) : PacketShape (root q) :=
  packetShape_of_net_eq_rootNet rfl

/-- **The packet shape passes to the native children** of a well-formed active call: a retained
vertex keeps its descriptor, at a precision that only grows, and a new packet has `a` slot bits
(`slotBits_le`), `i < a` (the valuation of its node), `2 ^ (i + 1)` tiles, the child's precision
as its number of exponents per tile, and the slots of the packing, distinct within a packet. -/
theorem packetShape_child {x : Call T} (hx : WF x) (ha : active x = true) (hs : PacketShape x)
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
theorem modes_le_of_packetShape {x : Call T} (hs : PacketShape x) {v : List ℕ × VertexDesc T}
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
theorem rowPorts_le_of_packetShape {x : Call T} (hs : PacketShape x) {v : List ℕ × VertexDesc T}
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

/-- **The cost of a leaf with the packet shape.** For a native certificate `ce` of the entry
procedure of the roots, there is `K` such that, on a call of encoded length `n` with `M` edges,
scale `s` and precision `p` with the packet shape, whose roots take time at most `E` and space at
most `ES` in `ce` on every bit list on their ports, writing `A = 2 ^ (⌊log₂ s⌋ / 32768)`, direct
summation takes time at most `K (n + ES + 1) ^ K 2 ^ M ((A p + 2) ^ A + E)` and space at most
`K (n + ES + 1) ^ K`. -/
theorem leafCertificate_le_of_packetShape
    (ce : NativeCertificate (fun q : T × List Bool => ev q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    ∃ K : ℕ, ∀ (mk : Call T → State → ℕ × DescribedNetwork (VertexDesc T)) (x : Call T)
      (E ES : ℕ), PacketShape x →
      (∀ v ∈ x.net.vertices, ∀ t, v.2 = .inl t → ∀ bs : List Bool, bs.length = v.1.length →
        ce.time (t, bs) ≤ E ∧ ce.space (t, bs) ≤ ES) →
      (leafCertificate ce mk).time x ≤ K * ((encCall encT x).length + ES + 1) ^ K * 2 ^ x.edges *
          ((2 ^ (Nat.log 2 x.scale / 32768) * x.prec + 2) ^ 2 ^ (Nat.log 2 x.scale / 32768) + E) ∧
        (leafCertificate ce mk).space x ≤ K * ((encCall encT x).length + ES + 1) ^ K := by
  obtain ⟨K, hK⟩ := leafCertificate_le ce
  refine ⟨2 * K, fun mk x E ES hs hroot => ?_⟩
  obtain ⟨hT, hS⟩ := hK mk x (2 ^ (Nat.log 2 x.scale / 32768) * x.prec)
    (2 ^ (Nat.log 2 x.scale / 32768)) E ES (fun v hv =>
      ⟨modes_le_of_packetShape hs hv, fun bs _ => rowPorts_le_of_packetShape hs hv bs⟩) hroot
  have hn := scale_add_prec_add_length_fl_le encT x
  have hA := two_pow_log_div_le x.scale
  set N := (encCall encT x).length + ES with hN
  have hR : (encCall encT x).length + 2 ^ (Nat.log 2 x.scale / 32768) * x.prec + ES + 1 ≤
      (N + 1) ^ 2 := by
    have : 2 ^ (Nat.log 2 x.scale / 32768) * x.prec ≤ (N + 1) * N :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hpow : K * ((encCall encT x).length + 2 ^ (Nat.log 2 x.scale / 32768) * x.prec + ES +
      1) ^ K ≤ 2 * K * (N + 1) ^ (2 * K) :=
    calc _ ≤ K * ((N + 1) ^ 2) ^ K := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hR _)
      _ = K * (N + 1) ^ (2 * K) := by rw [← pow_mul]
      _ ≤ 2 * K * (N + 1) ^ (2 * K) := Nat.mul_le_mul_right _ (by omega)
  exact ⟨hT.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpow)), hS.trans hpow⟩

/-- **The cost of a leaf over tables with the packet shape.** The entry procedure of tables is
polynomial, so there is `K` such that, on a call over tables of encoded length `n` with `M` edges,
scale `s` and precision `p` with the packet shape, writing `A = 2 ^ (⌊log₂ s⌋ / 32768)`, direct
summation takes time at most `K (n + 1) ^ K 2 ^ M (A p + 2) ^ A` and space at most
`K (n + 1) ^ K`. -/
theorem leafCertificate_tableEntry_le_of_packetShape : ∃ K : ℕ,
    ∀ (mk : Call (List ℕ) → State → ℕ × DescribedNetwork (VertexDesc (List ℕ)))
      (x : Call (List ℕ)), PacketShape x →
      (leafCertificate tableEntryCertificate mk).time x ≤
          K * ((encCall (encList encNat) x).length + 1) ^ K * 2 ^ x.edges *
            (2 ^ (Nat.log 2 x.scale / 32768) * x.prec + 2) ^ 2 ^ (Nat.log 2 x.scale / 32768) ∧
        (leafCertificate tableEntryCertificate mk).space x ≤
          K * ((encCall (encList encNat) x).length + 1) ^ K := by
  obtain ⟨K, hK⟩ := leafCertificate_le_of_packetShape tableEntryCertificate
  obtain ⟨ct, dt, ht⟩ := tableEntryCertificate_isPolynomial.1.exists_le
  obtain ⟨cs, ds, hs⟩ := tableEntryCertificate_isPolynomial.2.exists_le
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = 1 + cs * 3 ^ ds := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, c₂ = 1 + ct * 3 ^ dt := ⟨_, rfl⟩
  refine ⟨K * c₁ ^ K * c₂ + (ds + 1) * K + dt, fun mk x hshape => ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, n = (encCall (encList encNat) x).length := ⟨_, rfl⟩
  rw [← hn]
  -- A root and the bits on its ports are at most `3 n` long.
  have hlen : ∀ v ∈ x.net.vertices, ∀ t, v.2 = .inl t → ∀ bs : List Bool,
      bs.length = v.1.length →
        (encPair (encList encNat) encBits (t, bs)).length + 1 ≤ 3 * (n + 1) := by
    intro v hv t hvt bs hbs
    have h1 := length_vertex_le (encList encNat) hv
    have h2 := length_le_length_encList encNat v.1
    rw [← hn, length_encPair, hvt, length_encSum] at h1
    rw [length_encPair]
    change 2 * (encList encNat t).length + 1 + bs.length + 1 ≤ 3 * (n + 1)
    simp only [Sum.elim_inl] at h1
    omega
  have hpow3 {c d : ℕ} : c * (3 * (n + 1)) ^ d = c * 3 ^ d * (n + 1) ^ d := by
    rw [mul_pow]; ring
  obtain ⟨hT, hS⟩ := hK mk x (ct * 3 ^ dt * (n + 1) ^ dt) (cs * 3 ^ ds * (n + 1) ^ ds) hshape
    fun v hv t hvt bs hbs => ⟨(ht (t, bs)).trans (by
      rw [← hpow3]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hlen v hv t hvt bs hbs) _)),
      (hs (t, bs)).trans (by
      rw [← hpow3]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hlen v hv t hvt bs hbs) _))⟩
  rw [← hn] at hT hS
  set A := 2 ^ (Nat.log 2 x.scale / 32768)
  set X := (A * x.prec + 2) ^ A
  set B := n + 1 with hB
  have hB1 : 1 ≤ B := by omega
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  -- `n + ES + 1 ≤ c₁ B ^ (ds + 1)` and `X + E ≤ c₂ B ^ dt X`.
  have hW : n + cs * 3 ^ ds * B ^ ds + 1 ≤ c₁ * B ^ (ds + 1) := by
    have h1 : B ≤ B ^ (ds + 1) := (pow_one B).symm.le.trans (Nat.pow_le_pow_right hB1 (by omega))
    have h2 : cs * 3 ^ ds * B ^ ds ≤ cs * 3 ^ ds * B ^ (ds + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB1 (by omega))
    rw [hc₁, add_mul, one_mul]
    omega
  have hXE : X + ct * 3 ^ dt * B ^ dt ≤ c₂ * B ^ dt * X := by
    have h1 : 1 ≤ B ^ dt := Nat.one_le_pow _ _ (by omega)
    have h2 : ct * 3 ^ dt * B ^ dt ≤ ct * 3 ^ dt * B ^ dt * X := Nat.le_mul_of_pos_right _ hX1
    have h3 : X ≤ B ^ dt * X := Nat.le_mul_of_pos_left _ h1
    have e : c₂ * B ^ dt * X = B ^ dt * X + ct * 3 ^ dt * B ^ dt * X := by rw [hc₂]; ring
    omega
  have hWK : K * (n + cs * 3 ^ ds * B ^ ds + 1) ^ K ≤ K * c₁ ^ K * B ^ ((ds + 1) * K) := by
    calc _ ≤ K * (c₁ * B ^ (ds + 1)) ^ K := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW _)
      _ = K * c₁ ^ K * B ^ ((ds + 1) * K) := by rw [mul_pow, ← pow_mul]; ring
  set K' := K * c₁ ^ K * c₂ + (ds + 1) * K + dt
  have hc₂1 : 1 ≤ c₂ := by omega
  refine ⟨hT.trans ?_, hS.trans ?_⟩
  · calc _ ≤ K * c₁ ^ K * B ^ ((ds + 1) * K) * 2 ^ x.edges * (c₂ * B ^ dt * X) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ hWK) hXE
      _ = K * c₁ ^ K * c₂ * B ^ ((ds + 1) * K + dt) * 2 ^ x.edges * X := by rw [pow_add]; ring
      _ ≤ K' * B ^ K' * 2 ^ x.edges * X :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
            (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hB1 (by omega))))
  · calc _ ≤ K * c₁ ^ K * B ^ ((ds + 1) * K) := hWK
      _ ≤ K' * B ^ K' := Nat.mul_le_mul
          ((Nat.le_mul_of_pos_right _ hc₂1).trans (by omega))
          (Nat.pow_le_pow_right hB1 (by omega))

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

/-- **The leaf factor is subexponential.** For all constants `C`, `c` and `s₀` there is `K` such
that, for `s ≤ m ≤ C s`, `M ≤ 2 m` and `p ≤ n`, writing `A = 2 ^ (⌊log₂ m⌋ / 32768)`,
`2 ^ M (A p + 2) ^ A ≤ K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)`, provided that from `s₀` on
`M ≤ leafSize m` and `p ≤ m ^ c`. Below `s₀`, `m` is bounded, so the packet factor is polynomial
in `n` and `2 ^ M` is a constant; from `s₀` on, `2 ^ M ≤ 2 ^ (C s / √⌊log₂ s⌋)` and the packet
factor is subexponential (`exists_packetFactor_le`). This is the factor of the cost of a leaf with
the packet shape (`leafCertificate_le_of_packetShape`) that is not polynomial. -/
theorem exists_leafFactor_le (C c s₀ : ℕ) : ∃ K : ℕ, ∀ s m M p n : ℕ, 2 ≤ s → s ≤ m →
    m ≤ C * s → M ≤ 2 * m → p ≤ n → (s₀ ≤ s → M ≤ leafSize m ∧ p ≤ m ^ c) →
    2 ^ M * (2 ^ (Nat.log 2 m / 32768) * p + 2) ^ 2 ^ (Nat.log 2 m / 32768) ≤
      K * (n + 1) ^ K * 2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) := by
  obtain ⟨K₁, hK₁⟩ := exists_packetFactor_le C c
  obtain ⟨Ks, hKs⟩ : ∃ Ks, Ks = 2 ^ (2 * (C * s₀)) * (C * s₀ + 2) ^ (C * s₀) := ⟨_, rfl⟩
  have hKs1 : 1 ≤ Ks := by rw [hKs]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨Ks + C * s₀ + C + K₁, fun s m M p n hs hsm hmC hM hp hbig => ?_⟩
  set K := Ks + C * s₀ + C + K₁ with hK
  set S := Nat.sqrt (Nat.log 2 s) with hSdef
  set A := 2 ^ (Nat.log 2 m / 32768) with hA
  have hS1 : 1 ≤ S := Nat.one_le_sqrt_log_two hs
  have hB1 : 1 ≤ n + 1 := by omega
  have hX1 : 1 ≤ 2 ^ (K * s / S) := Nat.one_le_two_pow
  have hAm : A ≤ m := (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)).trans
    (Nat.pow_log_le_self 2 (by omega))
  rcases lt_or_ge s s₀ with hsmall | hlarge
  · -- Below `s₀`: constants and a polynomial.
    have hmC' : m ≤ C * s₀ := hmC.trans (Nat.mul_le_mul_left _ hsmall.le)
    have h2M : 2 ^ M ≤ 2 ^ (2 * (C * s₀)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hbase : A * p + 2 ≤ (C * s₀ + 2) * (n + 1) := by
      have : A * p ≤ C * s₀ * n := Nat.mul_le_mul (hAm.trans hmC') hp
      nlinarith
    have hfac : (A * p + 2) ^ A ≤ (C * s₀ + 2) ^ (C * s₀) * (n + 1) ^ (C * s₀) := by
      calc (A * p + 2) ^ A ≤ ((C * s₀ + 2) * (n + 1)) ^ A := Nat.pow_le_pow_left hbase _
        _ ≤ ((C * s₀ + 2) * (n + 1)) ^ (C * s₀) :=
            Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr (by positivity)) (hAm.trans hmC')
        _ = (C * s₀ + 2) ^ (C * s₀) * (n + 1) ^ (C * s₀) := mul_pow _ _ _
    calc 2 ^ M * (A * p + 2) ^ A
        ≤ 2 ^ (2 * (C * s₀)) * ((C * s₀ + 2) ^ (C * s₀) * (n + 1) ^ (C * s₀)) :=
          Nat.mul_le_mul h2M hfac
      _ = Ks * (n + 1) ^ (C * s₀) := by rw [hKs]; ring
      _ ≤ K * (n + 1) ^ K := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hB1 (by omega))
      _ ≤ K * (n + 1) ^ K * 2 ^ (K * s / S) := Nat.le_mul_of_pos_right _ hX1
  · -- From `s₀` on: the leaf size and the packet factor.
    obtain ⟨hleaf, hpm⟩ := hbig hlarge
    have hlog : S ≤ Nat.sqrt (Nat.log 2 m) := Nat.sqrt_log_two_mono hsm
    have hMs : M ≤ C * s / S :=
      calc M ≤ m / Nat.sqrt (Nat.log 2 m) := hleaf
        _ ≤ m / S := Nat.div_le_div_left hlog hS1
        _ ≤ C * s / S := Nat.div_le_div_right hmC
    have hfac : (A * p + 2) ^ A ≤ 2 ^ (K₁ * s / S) := hK₁ s m p hs hsm hmC hpm
    have hCK : (C + K₁) * s ≤ K * s := Nat.mul_le_mul_right _ (by omega)
    have hexp : C * s / S + K₁ * s / S ≤ K * s / S :=
      Nat.div_add_div_le_add_div.trans (Nat.div_le_div_right (by rw [← add_mul]; exact hCK))
    have hKn : 1 ≤ K * (n + 1) ^ K := Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (by positivity))
    calc 2 ^ M * (A * p + 2) ^ A ≤ 2 ^ (C * s / S) * 2 ^ (K₁ * s / S) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hMs) hfac
      _ = 2 ^ (C * s / S + K₁ * s / S) := by rw [pow_add]
      _ ≤ 2 ^ (K * s / S) := Nat.pow_le_pow_right (by norm_num) hexp
      _ ≤ K * (n + 1) ^ K * 2 ^ (K * s / S) := Nat.le_mul_of_pos_left _ hKn

/-- A polynomial factor `K₀ B ^ K₀` absorbed into a leaf bound `K₁ B ^ K₁ 2 ^ (K₁ s / S)`. -/
private theorem mul_leafBound_le {K₀ K₁ B s S : ℕ} (hB : 1 ≤ B) :
    K₀ * B ^ K₀ * (K₁ * B ^ K₁ * 2 ^ (K₁ * s / S)) ≤
      (K₀ * K₁ + K₀ + K₁) * B ^ (K₀ * K₁ + K₀ + K₁) * 2 ^ ((K₀ * K₁ + K₀ + K₁) * s / S) :=
  calc K₀ * B ^ K₀ * (K₁ * B ^ K₁ * 2 ^ (K₁ * s / S))
      = K₀ * K₁ * B ^ (K₀ + K₁) * 2 ^ (K₁ * s / S) := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _))
        (Nat.pow_le_pow_right hB (by omega)))
        (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right
          (Nat.mul_le_mul_right _ (by omega))))

/-- **The leaf bound of the resource analysis.** For all constants `C`, `c` and `s₀` there is `K`
such that a call with the packet shape, scale `m` with `s ≤ m ≤ C s` and at most `2 m` edges takes
time at most `K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` and space at most `K (n + 1) ^ K` at a leaf,
provided that from `s₀` on it has at most `leafSize m` edges and precision at most `m ^ c`: the
cost of a leaf over tables with the packet shape
(`leafCertificate_tableEntry_le_of_packetShape`), with its factor `2 ^ M (A p + 2) ^ A` bounded by
`exists_leafFactor_le`. -/
theorem exists_leafCertificate_le (C c s₀ : ℕ) : ∃ K : ℕ,
    ∀ (mk : Call (List ℕ) → State → ℕ × DescribedNetwork (VertexDesc (List ℕ))) (s : ℕ)
      (x : Call (List ℕ)), 2 ≤ s →
      s ≤ x.scale → x.scale ≤ C * s → PacketShape x → x.edges ≤ 2 * x.scale →
      (s₀ ≤ s → x.edges ≤ leafSize x.scale ∧ x.prec ≤ x.scale ^ c) →
      (leafCertificate tableEntryCertificate mk).time x ≤
          K * ((encCall (encList encNat) x).length + 1) ^ K * 2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) ∧
        (leafCertificate tableEntryCertificate mk).space x ≤
          K * ((encCall (encList encNat) x).length + 1) ^ K := by
  obtain ⟨K₀, hK₀⟩ := leafCertificate_tableEntry_le_of_packetShape
  obtain ⟨K₁, hK₁⟩ := exists_leafFactor_le C c s₀
  refine ⟨K₀ * K₁ + K₀ + K₁, fun mk s x hs hsm hmC hshape hM hbig => ?_⟩
  obtain ⟨hT, hS⟩ := hK₀ mk x hshape
  set n := (encCall (encList encNat) x).length with hn
  have hB1 : 1 ≤ n + 1 := by omega
  have hp : x.prec ≤ n := by have := scale_add_prec_add_length_fl_le (encList encNat) x; omega
  have hF := hK₁ s x.scale x.edges x.prec n hs hsm hmC hM hp hbig
  refine ⟨hT.trans ?_, hS.trans (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hB1 (by omega)))⟩
  rw [Nat.mul_assoc]
  exact (Nat.mul_le_mul_left _ hF).trans (mul_leafBound_le hB1)

/-- **The leaf bound with the costs of the root entries.** For a native certificate `ce` of the
entry procedure and all constants `C`, `c` and `s₀` there is `K` such that a call with the packet
shape, scale `m` with `s ≤ m ≤ C s` and at most `2 m` edges, whose root entries take time at most
`E` and space at most `ES`, takes time at most `K (n + ES + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋) (E + 1)`
and space at most `K (n + ES + 1) ^ K` at a leaf, provided that from `s₀` on it has at most
`leafSize m` edges and precision at most `m ^ c`: the cost of a leaf with the packet shape
(`leafCertificate_le_of_packetShape`), with its factor `2 ^ M (A p + 2) ^ A` bounded as for tables
by `exists_leafFactor_le`. -/
theorem exists_leafCertificate_le_of_entry
    (ce : NativeCertificate (fun q : T × List Bool => ev q.1 q.2) (encPair encT encBits)
      (encList encNat)) (C c s₀ : ℕ) : ∃ K : ℕ,
    ∀ (mk : Call T → State → ℕ × DescribedNetwork (VertexDesc T)) (s : ℕ) (x : Call T)
      (E ES : ℕ), 2 ≤ s → s ≤ x.scale → x.scale ≤ C * s → PacketShape x →
      x.edges ≤ 2 * x.scale → (s₀ ≤ s → x.edges ≤ leafSize x.scale ∧ x.prec ≤ x.scale ^ c) →
      (∀ v ∈ x.net.vertices, ∀ t, v.2 = .inl t → ∀ bs : List Bool, bs.length = v.1.length →
        ce.time (t, bs) ≤ E ∧ ce.space (t, bs) ≤ ES) →
      (leafCertificate ce mk).time x ≤ K * ((encCall encT x).length + ES + 1) ^ K *
          2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) * (E + 1) ∧
        (leafCertificate ce mk).space x ≤ K * ((encCall encT x).length + ES + 1) ^ K := by
  obtain ⟨K₀, hK₀⟩ := leafCertificate_le_of_packetShape ce
  obtain ⟨K₁, hK₁⟩ := exists_leafFactor_le C c s₀
  refine ⟨K₀ * K₁ + K₀ + K₁, fun mk s x E ES hs hsm hmC hshape hM hbig hroot => ?_⟩
  obtain ⟨hT, hS⟩ := hK₀ mk x E ES hshape hroot
  set W := (encCall encT x).length + ES + 1 with hW
  have hB1 : 1 ≤ W := by omega
  have hp : x.prec ≤ (encCall encT x).length + ES := by
    have := scale_add_prec_add_length_fl_le encT x; omega
  have hF := hK₁ s x.scale x.edges x.prec _ hs hsm hmC hM hp hbig
  rw [← hW] at hF
  set Pk := (2 ^ (Nat.log 2 x.scale / 32768) * x.prec + 2) ^ 2 ^ (Nat.log 2 x.scale / 32768)
  refine ⟨?_, hS.trans (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hB1 (by omega)))⟩
  have hPE : Pk + E ≤ Pk * (E + 1) := by
    have : 1 ≤ Pk := Nat.one_le_pow _ _ (by omega)
    nlinarith
  calc _ ≤ K₀ * W ^ K₀ * 2 ^ x.edges * (Pk + E) := hT
    _ ≤ K₀ * W ^ K₀ * (2 ^ x.edges * Pk) * (E + 1) := by
        rw [Nat.mul_assoc (K₀ * W ^ K₀), Nat.mul_assoc (K₀ * W ^ K₀), Nat.mul_assoc (2 ^ x.edges)]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hPE)
    _ ≤ _ := Nat.mul_le_mul_right _ ((Nat.mul_le_mul_left _ hF).trans (mul_leafBound_le hB1))

end FastContraction

end Cslib.Circuits.Frontier
