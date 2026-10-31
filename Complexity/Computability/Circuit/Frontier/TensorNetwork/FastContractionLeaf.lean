/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionMachine
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# The leaves of the fast contraction algorithm

The cost of the leaves of the native recursion of Theorem D.1 of [OpenAI2026ETH]
(`Cslib.Circuits.Frontier.FastContraction.leafCertificate`): direct summation over the `2 ^ M`
edge assignments of a call with `M` edges, whose packet entries cost `(m + 2) ^ L` for `m` target
modes and `L` row ports (§D.4.6–§D.4.7, pp. 63–64).

## Main results

* `Cslib.Circuits.Frontier.FastContraction.leafCertificate_le`: if every vertex of a call has at
  most `R` target modes and at most `Λ` row ports, the leaf takes time at most
  `K (n + R + 1) ^ K 2 ^ M (R + 2) ^ Λ` and space at most `K (n + R + 1) ^ K` on a call of encoded
  length `n` with `M` edges.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.6–§D.4.7.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction

open GaloisRingArith NativePacket ChildCursor Cslib.GenericRAM Cslib.GenericRAM.StackRecursion
  Turing.MultiTapeTM

/-! ### Encoded lengths -/

/-- The precision and the coefficients of the modulus are at most the encoded length of a call. -/
theorem prec_add_length_fl_le (x : Call) : x.prec + x.fl.length ≤ (encCall x).length := by
  have h := length_le_length_encList encNat x.fl
  obtain ⟨⟨s, d, b, p, fl, r⟩, D⟩ := x
  simp only [Call.prec, Call.fl, encCall, encParams, length_encPair, encUnary_apply,
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
  have hpfl := prec_add_length_fl_le x
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
  obtain ⟨Rv, hRv⟩ : ∃ Rv, Rv = n * (2 * n + 3) + cf * (n + 1) ^ df * (2 * (cp * (n + 1) ^ dp) + 3) +
      ct * (3 * n + 2) ^ dt := ⟨_, rfl⟩
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

end Cslib.Circuits.Frontier.FastContraction
