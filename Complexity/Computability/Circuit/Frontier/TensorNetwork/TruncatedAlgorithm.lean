/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.TruncatedResources
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ModulusGrowth
import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionPolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Polynomial truncation order from a contraction over `A_P`

Theorem D.1 of [OpenAI2026ETH] (p. 53) contracts networks whose entries lie in
`B_{P,ℓ} = (ℤ / 2 ^ P)[V] / (V ^ ℓ)`. This file states its interface for described networks
(`Cslib.Circuits.Frontier.TruncatedContractionAlgorithm`) and assembles it
(`Cslib.Circuits.Frontier.TruncatedContractionAlgorithm.ofCore`) from a native contraction over
`A_P = (ℤ / 2 ^ P)[U] / (f)` of the specialized networks, at the modulus
`f = FastContraction.modulus m` of a network with `m` edges.

**The interface.** One native certificate computes the truncated contraction
(`DescribedNetwork.truncContraction`) from `(P, ℓ, r, G)`, with `P` and `ℓ` in unary. For all
constants `C`, `D` and `d` there is `K` such that, on every network admissible at a size `s ≥ 2`
with constant `C`, precision `1 ≤ P ≤ D s (⌊log₂ s⌋ + 1)` and truncation order
`1 ≤ ℓ ≤ D (s + 1) ^ d`, it takes time at most
`K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` and space at most `K (n + 1) ^ K`, for the encoded length `n`
of the input. This is the shape of `Cslib.Complexity.CountingSimulation.ContractionAlgorithm`.

**The assembly** branches on whether the modulus has enough residues for the
`N = (ℓ - 1) k + 1` interpolation points (`Cslib.Circuits.Frontier.truncGuard`):
* if `N ≤ 2 ^ deg f`, it runs the reduction of truncation order `ℓ` to `A_P`
  (`engineCertificate`) around the given contraction over `A_P`
  (`Cslib.Circuits.Frontier.fastTruncCertificate`);
* otherwise it sums directly (`truncDirectCertificate`).

On admissible inputs with at most `C s` vertices, at least `s` edges and polynomial `ℓ`, the first
branch is eventually taken. The modulus already has degree
`2 * 3 ^ ⌊log₂ (4 ⌊log₂ m⌋ + 2)⌋`, which eventually exceeds every fixed multiple of `log₂ m`.
The explicit sufficient threshold is `max (C D) (2 ^ (2 ^ (d + 2)))`
(`Cslib.Circuits.Frontier.truncGuard_of_polynomial_le`). Below it, direct summation costs a
constant factor. The older and smaller linear-order threshold is also retained.

The logarithmic factor in precision and the polynomial truncation range strengthen the stated
range of Theorem D.1. These extensions are proved here; they are not attributed to its statement.

**The hypotheses on the contraction over `A_P`** are those of the interface planned in #1538 for
milestone E1: it is correct on every network at the modulus of its number of edges, and meets the
bound of the interface on the networks admissible for it. The assembly also asks that the
specialized networks of admissible networks be admissible for it, and that the entries be computed
within time `poly(L) 2 ^ O(s)` and polynomial space for the encoded length `L` of the network (for
the small sizes). The reduction itself is ours, not the manuscript's; see
`Complexity/Computability/Circuit/Frontier/TensorNetwork/Truncated.lean`.

## Main definitions

* `Cslib.Circuits.Frontier.TruncatedContractionAlgorithm`: the interface.
* `Cslib.Circuits.Frontier.truncGuard`: whether the modulus has enough residues.
* `Cslib.Circuits.Frontier.fastTruncCertificate`: the reduction at the modulus of the network.
* `Cslib.Circuits.Frontier.TruncatedContractionAlgorithm.ofCore`: the assembly.

## Main results

* `Cslib.Circuits.Frontier.truncGuard_polyTime`: the guard is polynomial-time.
* `Cslib.Circuits.Frontier.truncGuard_of_le`: admissible inputs pass the guard from some size on.
* `Cslib.Circuits.Frontier.fastTruncCertificate_correct`: the reduction is correct on guarded
  inputs.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53).
-/

public section

namespace Cslib.Circuits.Frontier

open Turing.MultiTapeTM Cslib.GenericRAM GaloisRingArith

variable {T : Type} {encT : T ↪ List Bool}

/-- **The interface of Theorem D.1 at truncation order `ℓ`** for described networks. One native
certificate computes the truncated contraction from `(P, ℓ, r, G)`, with `P` and `ℓ` in unary. For
all constants `C`, `D`, `d` there is `K` such that, on every network admissible at a size `s ≥ 2`
with constant `C`, precision `1 ≤ P ≤ D s (⌊log₂ s⌋ + 1)` and order `1 ≤ ℓ ≤ D (s + 1) ^ d`, its
time is at most
`K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` and its space at most `K (n + 1) ^ K`, where `n` is the
encoded length of the input. Outside admissible inputs the certificate need only be correct. -/
structure TruncatedContractionAlgorithm (encT : T ↪ List Bool) (entry : T → List Bool → List ℕ)
    (Admissible : ℕ → ℕ → ℕ × DescribedNetwork T → Prop) where
  /-- The native truncated contraction. -/
  certificate : NativeCertificate
    (fun ((P, ℓ, _, G) : ℕ × ℕ × ℕ × DescribedNetwork T) => G.truncContraction entry P ℓ)
    (encTrunc encT) (encList encNat)
  /-- Its time and space for logarithmically larger precision and any fixed polynomial
  truncation order. All constants are chosen before the instance. -/
  bound_polynomial : ∀ C D d : ℕ, ∃ K : ℕ, ∀ (s P ℓ r : ℕ) (G : DescribedNetwork T),
    2 ≤ s → 1 ≤ P → P ≤ D * s * (Nat.log 2 s + 1) →
    1 ≤ ℓ → ℓ ≤ D * (s + 1) ^ d → Admissible C s (r, G) →
      certificate.time (P, ℓ, r, G) ≤ K * ((encTrunc encT (P, ℓ, r, G)).length + 1) ^ K *
          2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) ∧
        certificate.space (P, ℓ, r, G) ≤ K * ((encTrunc encT (P, ℓ, r, G)).length + 1) ^ K

/-- The linear precision and truncation range of Theorem D.1 is a special case of the enlarged
range. -/
theorem TruncatedContractionAlgorithm.bound {entry : T → List Bool → List ℕ}
    {Admissible : ℕ → ℕ → ℕ × DescribedNetwork T → Prop}
    (A : TruncatedContractionAlgorithm encT entry Admissible) (C D : ℕ) :
    ∃ K : ℕ, ∀ (s P ℓ r : ℕ) (G : DescribedNetwork T), 2 ≤ s → 1 ≤ P → P ≤ D * s →
      1 ≤ ℓ → ℓ ≤ D * s → Admissible C s (r, G) →
        A.certificate.time (P, ℓ, r, G) ≤ K * ((encTrunc encT (P, ℓ, r, G)).length + 1) ^ K *
          2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) ∧
        A.certificate.space (P, ℓ, r, G) ≤ K * ((encTrunc encT (P, ℓ, r, G)).length + 1) ^ K := by
  obtain ⟨K, hK⟩ := A.bound_polynomial C D 1
  refine ⟨K, fun s P ℓ r G hs hP hPD hℓ hℓD hA => hK s P ℓ r G hs hP ?_ hℓ ?_ hA⟩
  · exact hPD.trans (Nat.le_mul_of_pos_right _ (by omega))
  · simpa only [pow_one] using hℓD.trans (Nat.mul_le_mul_left D (Nat.le_succ s))

/-! ### The guard -/

/-- **The guard** at an input `(P, ℓ, r, G)`: the modulus `FastContraction.modulus m` of the network
`G` with `m` edges has at least as many residues as the `(ℓ - 1) k + 1` interpolation points. -/
@[expose] def truncGuard : ℕ × ℕ × ℕ × DescribedNetwork T → Bool
  | (_, ℓ, _, G) =>
    decide (DescribedNetwork.pointCount ℓ G ≤ 2 ^ (FastContraction.modulus G.numEdges).length)

/-- The network of an input. -/
private theorem network_polyTime :
    ComputableInPolyTime (fun ((_, _, _, G) : ℕ × ℕ × ℕ × DescribedNetwork T) => G)
      (encTrunc encT) (DescribedNetwork.encDescribed encT) :=
  (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp
    (ComputableInPolyTime.snd _ _))

/-- **The guard is polynomial-time.** -/
theorem truncGuard_polyTime :
    ComputableInPolyTime (truncGuard (T := T)) (encTrunc encT) encBool := by
  have hpc : ComputableInPolyTime
      (fun x : ℕ × ℕ × ℕ × DescribedNetwork T => DescribedNetwork.pointCount x.2.1 x.2.2.2)
      (encTrunc encT) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (pointCount_polyTime (encT := encT).comp
      ((ComputableInPolyTime.const ([] : List ℕ)).prod ComputableInPolyTime.id'))
  have h2 : ComputableInPolyTime
      (fun x : ℕ × ℕ × ℕ × DescribedNetwork T =>
        2 ^ (FastContraction.modulus x.2.2.2.numEdges).length) (encTrunc encT) encNat :=
    ComputableInPolyTime.binary_two_pow.comp ((ComputableInPolyTime.length_list _).comp
      (FastContraction.modulus_polyTime.comp
        (DescribedNetwork.numEdges_polyTime.comp network_polyTime)))
  refine (ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.binary_lt' h2 hpc)).of_enc_eq
    fun x => congrArg encBool ?_
  obtain ⟨P, ℓ, r, G⟩ := x
  simp only [truncGuard, Function.comp_apply]
  by_cases h : DescribedNetwork.pointCount ℓ G ≤ 2 ^ (FastContraction.modulus G.numEdges).length
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_le h]

/-- **Admissible inputs pass the guard from some size on.** With at most `C s` vertices, at least
`s` edges and `ℓ ≤ D s`, the guard holds once `s ≥ 4 (C D + 1)`: the modulus has degree at least
`4 ⌊log₂ m⌋`, so more than `m ^ 4 / 16 ≥ C D s ^ 2 + 1` residues. -/
theorem truncGuard_of_le {C D s P ℓ r : ℕ} {G : DescribedNetwork T} (hs : 4 * (C * D + 1) ≤ s)
    (hℓ : ℓ ≤ D * s) (hk : G.vertices.length ≤ C * s) (hm : s ≤ G.numEdges) :
    truncGuard (P, ℓ, r, G) = true := by
  simp only [truncGuard, decide_eq_true_eq]
  set m := G.numEdges
  have hlog : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self one_lt_two m
  have h4 : m ^ 4 < 2 ^ (4 * Nat.log 2 m) * 16 := by
    calc m ^ 4 < (2 ^ (Nat.log 2 m + 1)) ^ 4 := Nat.pow_lt_pow_left hlog (by norm_num)
      _ = 2 ^ (4 * Nat.log 2 m) * 16 := by rw [← pow_mul]; ring
  have h5 : 2 ^ (4 * Nat.log 2 m) ≤ 2 ^ (FastContraction.modulus m).length :=
    Nat.pow_le_pow_right (by norm_num) (FastContraction.four_mul_log_le_length_modulus m)
  have hsm : s ^ 4 ≤ m ^ 4 := Nat.pow_le_pow_left hm 4
  have hpc : DescribedNetwork.pointCount ℓ G ≤ D * s * (C * s) + 1 := by
    have : (ℓ - 1) * G.vertices.length ≤ D * s * (C * s) :=
      Nat.mul_le_mul (by omega) hk
    simp only [DescribedNetwork.pointCount]
    omega
  have hss : 16 * (C * D + 1) ≤ s * s := by nlinarith
  have hkey : 16 * (D * s * (C * s) + 1) ≤ s ^ 4 := by
    have e : s ^ 4 = s * s * (s * s) := by ring
    have e2 : D * s * (C * s) = C * D * (s * s) := by ring
    rw [e, e2]
    have h1 : 1 ≤ s * s := by nlinarith
    nlinarith
  omega

/-- Every fixed polynomial truncation order eventually passes the same interpolation guard.
The threshold is independent of the network, its precision and its encoding length. -/
theorem truncGuard_of_polynomial_le {C D d s P ℓ r : ℕ} {G : DescribedNetwork T}
    (hs : max (C * D) (2 ^ (2 ^ (d + 2))) ≤ s)
    (hℓ : ℓ ≤ D * (s + 1) ^ d) (hk : G.vertices.length ≤ C * s) (hm : s ≤ G.numEdges) :
    truncGuard (P, ℓ, r, G) = true := by
  simp only [truncGuard, decide_eq_true_eq]
  have hCD : C * D ≤ s := (le_max_left _ _).trans hs
  have hpow : 1 ≤ (s + 1) ^ (d + 1) := Nat.one_le_pow _ _ (by omega)
  have hprod : (ℓ - 1) * G.vertices.length ≤ C * D * (s + 1) ^ (d + 1) := by
    calc (ℓ - 1) * G.vertices.length ≤ (D * (s + 1) ^ d) * (C * (s + 1)) :=
          Nat.mul_le_mul (by omega) (hk.trans (Nat.mul_le_mul_left C (Nat.le_succ s)))
      _ = C * D * (s + 1) ^ (d + 1) := by rw [pow_succ]; ring
  calc DescribedNetwork.pointCount ℓ G
      ≤ (C * D + 1) * (s + 1) ^ (d + 1) := by
        simp only [DescribedNetwork.pointCount]
        nlinarith
    _ ≤ (s + 1) * (s + 1) ^ (d + 1) := Nat.mul_le_mul_right _ (by omega)
    _ = (s + 1) ^ (d + 2) := by rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]; ring
    _ ≤ (G.numEdges + 1) ^ (d + 2) := Nat.pow_le_pow_left (by omega) _
    _ ≤ 2 ^ (FastContraction.modulus G.numEdges).length :=
      FastContraction.pow_le_card_modulus (((le_max_right _ _).trans hs).trans hm)

/-! ### The fast branch -/

/-- The input of the reduction at the modulus of the network. -/
theorem modulusEdges_polyTime :
    ComputableInPolyTime
      (fun ((P, ℓ, r, G) : ℕ × ℕ × ℕ × DescribedNetwork T) =>
        (FastContraction.modulus G.numEdges, (P, ℓ, r, G)))
      (encTrunc encT) (encEngine encT) :=
  (FastContraction.modulus_polyTime.comp
    (DescribedNetwork.numEdges_polyTime.comp network_polyTime)).prod ComputableInPolyTime.id'

variable {core : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T) → List ℕ}

/-- **The reduction at the modulus of the network**: the native reduction of truncation order `ℓ`
to contractions over `A_P`, with the modulus `FastContraction.modulus m` for `m` edges. -/
@[expose] noncomputable def fastTruncCertificate
    (cc : NativeCertificate core (encCore encT) (encList encNat)) :
    NativeCertificate
      (fun ((P, ℓ, r, G) : ℕ × ℕ × ℕ × DescribedNetwork T) =>
        DescribedNetwork.interpContract core (FastContraction.modulus G.numEdges) P ℓ r G)
      (encTrunc encT) (encList encNat) :=
  ((engineCertificate core cc).comp (NativeCertificate.ofPolyTime modulusEdges_polyTime)).congr
    fun _ => rfl

/-- **The reduction is correct on guarded inputs**, for a contraction over `A_P` that is correct
at the modulus of the number of edges. -/
theorem fastTruncCertificate_correct {entry : T → List Bool → List ℕ}
    (hval : ∀ (P r : ℕ) (G' : DescribedNetwork (SpecDesc T)),
      val P (FastContraction.modulus G'.numEdges) (core (P, FastContraction.modulus G'.numEdges,
        r, G')) =
        G'.contraction fun d bs =>
          val P (FastContraction.modulus G'.numEdges) (specEntry entry d bs))
    (P ℓ r : ℕ) (G : DescribedNetwork T) (hg : truncGuard (P, ℓ, r, G) = true) :
    DescribedNetwork.interpContract core (FastContraction.modulus G.numEdges) P ℓ r G =
      G.truncContraction entry P ℓ := by
  simp only [truncGuard, decide_eq_true_eq] at hg
  refine DescribedNetwork.interpContract_eq (FastContraction.irreducible_modulus _) _ hg
    fun k _ => ?_
  have h := hval P r (DescribedNetwork.specNet P ℓ (FastContraction.modulus G.numEdges)
    (FastContraction.digits (FastContraction.modulus G.numEdges).length k) G)
  rw [DescribedNetwork.numEdges_specNet] at h
  exact h

/-! ### The assembly -/

/-- **Theorem D.1 at truncation order `ℓ`, from a contraction over `A_P`.** Let `cc` be a native
contraction over `A_P` of specialized networks that is correct on every network at the modulus
`FastContraction.modulus m` of its number `m` of edges (`hval`) and meets the interface's bound on
the networks admissible for it (`hcore`, for an admissibility `CoreAdm`). Suppose that the networks
specialized at the digit points of admissible networks are admissible for it (`htransfer`), that
admissible networks have between `s` and `C s` edges and at most `C s` vertices (`hshape`), and
that the entries take time `K (L + 1) ^ K 2 ^ (K s)` and space `K (L + 1) ^ K` on admissible
networks of encoded length `L` (`hentry`). Then branching on `truncGuard` to the reduction around
`cc` or to direct summation is a truncated contraction algorithm. -/
noncomputable def TruncatedContractionAlgorithm.ofCore {entry : T → List Bool → List ℕ}
    {Adm : ℕ → ℕ → ℕ × DescribedNetwork T → Prop}
    {CoreAdm : ℕ → ℕ → ℕ × DescribedNetwork (SpecDesc T) → Prop}
    (cc : NativeCertificate core (encCore encT) (encList encNat))
    (hval : ∀ (P r : ℕ) (G' : DescribedNetwork (SpecDesc T)),
      val P (FastContraction.modulus G'.numEdges) (core (P, FastContraction.modulus G'.numEdges,
        r, G')) =
        G'.contraction fun d bs =>
          val P (FastContraction.modulus G'.numEdges) (specEntry entry d bs))
    (hcore : ∀ C D : ℕ, ∃ K : ℕ, ∀ (s P r : ℕ) (G' : DescribedNetwork (SpecDesc T)), 2 ≤ s →
      1 ≤ P → P ≤ D * s * (Nat.log 2 s + 1) → CoreAdm C s (r, G') →
        cc.time (P, FastContraction.modulus G'.numEdges, r, G') ≤
            K * ((encCore encT (P, FastContraction.modulus G'.numEdges, r, G')).length + 1) ^ K *
              2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) ∧
          cc.space (P, FastContraction.modulus G'.numEdges, r, G') ≤
            K * ((encCore encT (P, FastContraction.modulus G'.numEdges, r, G')).length + 1) ^ K)
    (htransfer : ∀ C D d : ℕ, ∃ C' : ℕ, ∀ (s P ℓ r k : ℕ) (G : DescribedNetwork T), 2 ≤ s →
      1 ≤ P → P ≤ D * s * (Nat.log 2 s + 1) →
      1 ≤ ℓ → ℓ ≤ D * (s + 1) ^ d → Adm C s (r, G) →
        CoreAdm C' s (r, DescribedNetwork.specNet P ℓ (FastContraction.modulus G.numEdges)
          (FastContraction.digits (FastContraction.modulus G.numEdges).length k) G))
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat))
    (hentry : ∀ C : ℕ, ∃ K : ℕ, ∀ (s r : ℕ) (G : DescribedNetwork T), Adm C s (r, G) →
      ∀ v ∈ G.vertices, ∀ bs : List Bool, bs.length = v.1.length →
        ce.time (v.2, bs) ≤
            K * ((DescribedNetwork.encDescribed encT G).length + 1) ^ K * 2 ^ (K * s) ∧
          ce.space (v.2, bs) ≤ K * ((DescribedNetwork.encDescribed encT G).length + 1) ^ K)
    (hshape : ∀ C s r G, Adm C s (r, G) →
      s ≤ G.numEdges ∧ G.numEdges ≤ C * s ∧ G.vertices.length ≤ C * s) :
    TruncatedContractionAlgorithm encT entry Adm where
  certificate :=
    (NativeCertificate.branch (NativeCertificate.ofPolyTime truncGuard_polyTime)
      (fastTruncCertificate cc) (truncDirectCertificate entry ce)).congr fun ⟨P, ℓ, r, G⟩ => by
        split
        · next h => exact fastTruncCertificate_correct hval P ℓ r G h
        · rfl
  bound_polynomial C D dℓ := by
    obtain ⟨C', hC'⟩ := htransfer C D dℓ
    obtain ⟨K₀, hK₀⟩ := hcore C' D
    obtain ⟨Ke, hKe⟩ := hentry C
    obtain ⟨Kd, hKd⟩ := truncDirectCertificate_le entry ce
    obtain ⟨KE, hKE⟩ := engineCertificate_le (encT := encT) core cc
    obtain ⟨cO, -, hcO⟩ := cc.computes
    obtain ⟨pg, hpg, mg, bg⟩ := exists_mono_poly_cert (truncGuard_polyTime (encT := encT))
    obtain ⟨pM, hpM, mM, bM⟩ := exists_mono_poly_cert (modulusEdges_polyTime (encT := encT))
    obtain ⟨cY, dY, hY⟩ := (modulusEdges_polyTime (encT := encT)).polyBounded_length.exists_le
    set s₀ := max (C * D) (2 ^ (2 ^ (dℓ + 2))) with hs₀
    -- The overheads, as polynomials in the length `n` of the input.
    let Yf : ℕ → ℕ := fun n => cY * (n + 1) ^ dY
    let Qf : ℕ → ℕ := fun n => K₀ * (9 * (Yf n + 1) ^ 2 + 1) ^ K₀
    let F1 : ℕ → ℕ := fun n => pM n + (Yf n * Yf n + 2) *
      (KE * (Yf n + cO * (Qf n + 1) + 1) ^ KE + Qf n)
    let Ef : ℕ → ℕ := fun n => Ke * (n + 1) ^ Ke
    let F2 : ℕ → ℕ := fun n =>
      Kd * (n + Ef n + 1) ^ Kd * 2 ^ (C * s₀) * (Ef n * 2 ^ (Ke * s₀) + 1)
    let F : ℕ → ℕ := fun n => pg n + F1 n + F2 n
    have hYp : PolyBounded id Yf :=
      (PolyBounded.const cY).mul ((PolyBounded.self.add (PolyBounded.const 1)).pow dY)
    have hQp : PolyBounded id Qf :=
      (PolyBounded.const K₀).mul (((PolyBounded.const 9).mul ((hYp.add
        (PolyBounded.const 1)).pow 2)).add (PolyBounded.const 1) |>.pow K₀)
    have hEp : PolyBounded id Ef :=
      (PolyBounded.const Ke).mul ((PolyBounded.self.add (PolyBounded.const 1)).pow Ke)
    have qg := PolyBounded.of_polynomiallyBounded id hpg
    have qM := PolyBounded.of_polynomiallyBounded id hpM
    have hFp : PolyBounded id F :=
      ((qg.comp PolyBounded.self).add
        ((qM.comp PolyBounded.self).add (((hYp.mul hYp).add
          (PolyBounded.const 2)).mul (((PolyBounded.const KE).mul (((hYp.add
            ((PolyBounded.const cO).mul (hQp.add (PolyBounded.const 1)))).add
              (PolyBounded.const 1)).pow KE)).add hQp)))).add
        ((((PolyBounded.const Kd).mul (((PolyBounded.self.add hEp).add
          (PolyBounded.const 1)).pow Kd)).mul (PolyBounded.const (2 ^ (C * s₀)))).mul
          ((hEp.mul (PolyBounded.const (2 ^ (Ke * s₀)))).add (PolyBounded.const 1)))
    obtain ⟨a, d, had⟩ := hFp.exists_le
    refine ⟨a + d + K₀, fun s P ℓ r G hs hP hPD hℓ hℓD hA => ?_⟩
    obtain ⟨hsm, hmC, hkC⟩ := hshape C s r G hA
    set n := (encTrunc encT (P, ℓ, r, G)).length with hn
    set Xs := 2 ^ (K₀ * s / Nat.sqrt (Nat.log 2 s)) with hXs
    have hXs1 : 1 ≤ Xs := Nat.one_le_two_pow
    have hFn := had n
    simp only [id] at hFn
    have hK : a * (n + 1) ^ d * Xs ≤ (a + d + K₀) * (n + 1) ^ (a + d + K₀) *
        2 ^ ((a + d + K₀) * s / Nat.sqrt (Nat.log 2 s)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega)))
        (Nat.pow_le_pow_right (by norm_num)
          (Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))))
    have hKs : a * (n + 1) ^ d ≤ (a + d + K₀) * (n + 1) ^ (a + d + K₀) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    have hgt : (NativeCertificate.ofPolyTime truncGuard_polyTime).time (P, ℓ, r, G) ≤ pg n :=
      (bg (P, ℓ, r, G)).1
    have hgs : (NativeCertificate.ofPolyTime truncGuard_polyTime).space (P, ℓ, r, G) ≤ pg n :=
      (bg (P, ℓ, r, G)).2
    -- The two branches.
    have hfast : truncGuard (P, ℓ, r, G) = true →
        (fastTruncCertificate cc).time (P, ℓ, r, G) ≤ Xs * F1 n ∧
          (fastTruncCertificate cc).space (P, ℓ, r, G) ≤ F1 n := by
      intro _
      set fl := FastContraction.modulus G.numEdges with hfl
      have hLy : (encEngine encT (fl, P, ℓ, r, G)).length ≤ Yf n := hY (P, ℓ, r, G)
      have hNy : DescribedNetwork.pointCount ℓ G + 1 ≤ Yf n * Yf n + 2 := by
        have h1 := pointCount_le (encT := encT) fl P ℓ r G
        have h2 := Nat.mul_le_mul hLy hLy
        omega
      have hcall (k : ℕ) :
          cc.time (coreInput (fl, P, ℓ, r, G) k) ≤ Qf n * Xs ∧
            cc.space (coreInput (fl, P, ℓ, r, G) k) ≤ Qf n ∧
              (encList encNat (core (coreInput (fl, P, ℓ, r, G) k))).length ≤
                cO * (Qf n + 1) := by
        have hc := length_encCore_coreInput_le (encT := encT) (fl, P, ℓ, r, G) k
        have hci : coreInput (fl, P, ℓ, r, G) k = (P, FastContraction.modulus
            (DescribedNetwork.specNet P ℓ fl (FastContraction.digits fl.length k) G).numEdges,
            r, DescribedNetwork.specNet P ℓ fl (FastContraction.digits fl.length k) G) := rfl
        rw [hci] at hc ⊢
        obtain ⟨hT, hS⟩ := hK₀ s P r _ hs hP hPD (hC' s P ℓ r k G hs hP hPD hℓ hℓD hA)
        have hQ : K₀ * ((encCore encT (P, FastContraction.modulus
            (DescribedNetwork.specNet P ℓ fl (FastContraction.digits fl.length k) G).numEdges,
            r, DescribedNetwork.specNet P ℓ fl (FastContraction.digits fl.length k) G)).length +
              1) ^ K₀ ≤ Qf n := by
          refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
          have : 9 * ((encEngine encT (fl, P, ℓ, r, G)).length + 1) ^ 2 ≤ 9 * (Yf n + 1) ^ 2 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
          omega
        have hS' := hS.trans hQ
        refine ⟨hT.trans (Nat.mul_le_mul_right _ hQ), hS', ?_⟩
        have hout := hcO (P, FastContraction.modulus
          (DescribedNetwork.specNet P ℓ fl (FastContraction.digits fl.length k) G).numEdges,
          r, DescribedNetwork.specNet P ℓ fl (FastContraction.digits fl.length k) G)
        exact hout.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hS' 1))
      obtain ⟨hTe, hSe⟩ := hKE fl P ℓ r G _ _ _ fun k _ => hcall k
      have hEng : KE * ((encEngine encT (fl, P, ℓ, r, G)).length + cO * (Qf n + 1) + 1) ^ KE ≤
          KE * (Yf n + cO * (Qf n + 1) + 1) ^ KE :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      have hMt : (NativeCertificate.ofPolyTime modulusEdges_polyTime).time (P, ℓ, r, G) ≤ pM n :=
        (bM (P, ℓ, r, G)).1
      have hMs : (NativeCertificate.ofPolyTime modulusEdges_polyTime).space (P, ℓ, r, G) ≤
          pM n := (bM (P, ℓ, r, G)).2
      refine ⟨?_, ?_⟩
      · simp only [fastTruncCertificate, NativeCertificate.congr, NativeCertificate.comp_time]
        change (NativeCertificate.ofPolyTime modulusEdges_polyTime).time (P, ℓ, r, G) +
          (engineCertificate core cc).time (fl, P, ℓ, r, G) ≤ _
        have hTe' := hTe.trans (Nat.mul_le_mul hNy (Nat.add_le_add_right hEng _))
        have e1 : (Yf n * Yf n + 2) * (KE * (Yf n + cO * (Qf n + 1) + 1) ^ KE + Qf n * Xs) ≤
            Xs * ((Yf n * Yf n + 2) * (KE * (Yf n + cO * (Qf n + 1) + 1) ^ KE + Qf n)) := by
          have h1 : KE * (Yf n + cO * (Qf n + 1) + 1) ^ KE ≤
              Xs * (KE * (Yf n + cO * (Qf n + 1) + 1) ^ KE) := Nat.le_mul_of_pos_left _ hXs1
          calc (Yf n * Yf n + 2) * (KE * (Yf n + cO * (Qf n + 1) + 1) ^ KE + Qf n * Xs)
              ≤ (Yf n * Yf n + 2) * (Xs * (KE * (Yf n + cO * (Qf n + 1) + 1) ^ KE) +
                  Qf n * Xs) := Nat.mul_le_mul_left _ (by omega)
            _ = Xs * ((Yf n * Yf n + 2) * (KE * (Yf n + cO * (Qf n + 1) + 1) ^ KE + Qf n)) := by
                ring
        have e2 : pM n ≤ Xs * pM n := Nat.le_mul_of_pos_left _ hXs1
        have e3 : Xs * F1 n = Xs * pM n +
            Xs * ((Yf n * Yf n + 2) * (KE * (Yf n + cO * (Qf n + 1) + 1) ^ KE + Qf n)) := by
          simp only [F1]; ring
        omega
      · simp only [fastTruncCertificate, NativeCertificate.congr, NativeCertificate.comp_space]
        change (NativeCertificate.ofPolyTime modulusEdges_polyTime).space (P, ℓ, r, G) +
          (engineCertificate core cc).space (fl, P, ℓ, r, G) ≤ _
        have h1 : KE * (Yf n + cO * (Qf n + 1) + 1) ^ KE + Qf n ≤
            (Yf n * Yf n + 2) * (KE * (Yf n + cO * (Qf n + 1) + 1) ^ KE + Qf n) :=
          Nat.le_mul_of_pos_left _ (by omega)
        simp only [F1]
        omega
    have hdirect : truncGuard (P, ℓ, r, G) = false →
        (truncDirectCertificate entry ce).time (P, ℓ, r, G) ≤ F2 n ∧
          (truncDirectCertificate entry ce).space (P, ℓ, r, G) ≤ F2 n := by
      intro hg
      have hss : s < s₀ := by
        by_contra h
        have := truncGuard_of_polynomial_le (P := P) (r := r)
          (show max (C * D) (2 ^ (2 ^ (dℓ + 2))) ≤ s by omega) hℓD hkC hsm
        rw [this] at hg
        exact Bool.noConfusion hg
      have hL : (DescribedNetwork.encDescribed encT G).length ≤ n := by
        simp only [hn, encTrunc, length_encPair]
        omega
      have hEf : Ke * ((DescribedNetwork.encDescribed encT G).length + 1) ^ Ke ≤ Ef n :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      have h2s : 2 ^ (Ke * s) ≤ 2 ^ (Ke * s₀) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hss.le)
      obtain ⟨hT, hS⟩ := hKd P ℓ r G (Ef n * 2 ^ (Ke * s₀)) (Ef n) fun v hv bs hbs => by
        obtain ⟨h1, h2⟩ := hKe s r G hA v hv bs hbs
        exact ⟨h1.trans (Nat.mul_le_mul hEf h2s), h2.trans hEf⟩
      have h2m : 2 ^ G.numEdges ≤ 2 ^ (C * s₀) :=
        Nat.pow_le_pow_right (by norm_num) (hmC.trans (Nat.mul_le_mul_left _ hss.le))
      refine ⟨hT.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2m)), hS.trans ?_⟩
      simp only [F2]
      have h1 : 1 ≤ 2 ^ (C * s₀) * (Ef n * 2 ^ (Ke * s₀) + 1) :=
        Nat.one_le_iff_ne_zero.mpr (by positivity)
      calc Kd * (n + Ef n + 1) ^ Kd ≤ Kd * (n + Ef n + 1) ^ Kd *
            (2 ^ (C * s₀) * (Ef n * 2 ^ (Ke * s₀) + 1)) := Nat.le_mul_of_pos_right _ h1
        _ = _ := by ring
    refine ⟨?_, ?_⟩
    · simp only [NativeCertificate.congr, NativeCertificate.branch_time]
      have hF : pg n + Xs * F1 n + F2 n ≤ Xs * F n := by
        have h1 : pg n ≤ Xs * pg n := Nat.le_mul_of_pos_left _ hXs1
        have h2 : F2 n ≤ Xs * F2 n := Nat.le_mul_of_pos_left _ hXs1
        have e : Xs * F n = Xs * pg n + Xs * F1 n + Xs * F2 n := by simp only [F]; ring
        omega
      have hFX : Xs * F n ≤ a * (n + 1) ^ d * Xs := by
        calc Xs * F n ≤ Xs * (a * (n + 1) ^ d) := Nat.mul_le_mul_left _ hFn
          _ = a * (n + 1) ^ d * Xs := by ring
      split
      · next hg =>
        have := (hfast hg).1
        omega
      · next hg =>
        have := (hdirect (by simpa using hg)).1
        omega
    · simp only [NativeCertificate.congr, NativeCertificate.branch_space]
      have hF : pg n + F1 n + F2 n ≤ F n := le_rfl
      split
      · next hg =>
        have := (hfast hg).2
        omega
      · next hg =>
        have := (hdirect (by simpa using hg)).2
        omega

end Cslib.Circuits.Frontier
