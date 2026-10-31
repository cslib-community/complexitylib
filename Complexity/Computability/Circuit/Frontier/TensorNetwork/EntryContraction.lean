/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionMachine
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Schedule
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import Complexity.Foundations.Data.BitString.Binary
import Complexity.Foundations.Data.Nat.Asymptotics

/-!
# Contraction with entry procedures: the interface

Theorem D.1 of [OpenAI2026ETH] (p. 53) contracts Boolean tensor networks whose entries are not
given as tables but computed: it assumes, uniformly over the vertices and the Boolean choices of
their ports, that each entry is computable from the description in time
`(s + L) ^ b 2 ^ (A s ^ (9/10))` and space `(s + L) ^ b` (a paraphrase), with maximum degree at
most `⌈s ^ (9/10)⌉`. At that degree a table has
`2 ^ ⌈s ^ (9/10)⌉` entries, so Lemma D.2 (p. 56), which applies the theorem with entries computed
by procedures, needs this form for its polynomial-space bound. This file states the interface
that the contraction algorithm provides for such networks, milestone E1 of #1538.

**Entry procedures.** A network is a described network `DescribedNetwork T` (the record shared
with explicit networks), with descriptors in a type `T` encoded by `encT`. An *entry procedure*
is a function `entry : T → List Bool → List ℕ`, the coefficient list over
`A_P = (ℤ / 2 ^ P)[U] / (f)` of the entry of a descriptor at the bits on its ports, with a native
certificate `ce` on `encPair encT encBits`. This is the evaluator of direct summation
(`DescribedNetwork.contractionCertificate`). Explicit networks are the case of tables, and the
specialized networks of the truncation-order reduction (#1538, E2) are another instance.

**Admissible networks** (`EntryAdmissible`). Theorem D.1's hypotheses with one constant `C` for
the theorem's `C`, `A` and `b`: rows-first bipartite, between `s` and `C s` edges, maximum degree
at most `⌈s ^ (9/10)⌉` (`ceilNineTenths`), and every entry within time
`C (s + L + 1) ^ C 2 ^ (C ⌈s ^ (9/10)⌉)` and space `C (s + L + 1) ^ C`, where `L` is the encoded
length of the network. Entry outputs need no separate size condition, because a native
certificate's space bound charges its encoded output. As for explicit networks
(`Cslib.Complexity.CountingSimulation.ExplicitAdmissible`), admissibility asks for at least `s`
edges; a caller can pad with disjoint edges whose row tensor is `[x = 0]` and column tensor `1`,
which leave the contraction unchanged. The number of vertices is not bounded separately: the
encoded length bounds it.

**The interface** (`EntryContractionAlgorithm`). One native certificate maps an input
`(P, fl, r, G)`, with the precision `P` in unary and the coefficients `fl` of a modulus, to a
coefficient list whose value in `A_P` at the modulus `FastContraction.modulus m`, for `m` the
number of edges, is the contraction of the entries' values, on every input. On admissible inputs
at that modulus it runs in time `K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` and space `K (n + 1) ^ K`,
the bound shape of `Cslib.Complexity.CountingSimulation.ContractionAlgorithm`. The input format is
that of the truncation-order reduction's contractions of specialized networks.

**Direct summation** (`EntryContraction.directCore`). Summing over all edge assignments with the
entry procedure computes the contraction on every input (`EntryContraction.val_directCore`), in
time `(2 ^ m (k + 1) + 1) (K (n + ES + 1) ^ K + 2 E)` and space `K (n + ES + 1) ^ K + ES` when the
procedure takes time `E` and space `ES` on the vertices (`EntryContraction.directCore_le`). On
admissible inputs that is `K (n + 1) ^ K 2 ^ (K s)` and polynomial space
(`EntryContraction.exists_directCore_le`): the fallback of the contraction algorithm for small `s`.

**Instances.** A polynomial-time entry procedure meets the entry bounds from some constant on
(`EntryContraction.exists_entryAdmissible_of_isPolynomial`), so admissibility reduces to the
shape of the network. Tables are the entry procedure `tableEntry` (`VertexDesc.lean`), and direct
summation with it is the contraction of the explicit network
(`EntryContraction.val_directCore_tableEntry`).

## Main definitions

* `Cslib.Circuits.Frontier.ceilNineTenths`: `⌈s ^ (9/10)⌉`.
* `Cslib.Circuits.Frontier.EntryContraction.encInput`: the encoding of an input.
* `Cslib.Circuits.Frontier.EntryAdmissible`: Theorem D.1's hypotheses.
* `Cslib.Circuits.Frontier.EntryContractionAlgorithm`: the interface.
* `Cslib.Circuits.Frontier.EntryContraction.directCore`: direct summation with an entry procedure.

## Main results

* `Cslib.Circuits.Frontier.le_ceilNineTenths_iff`: `x ≤ ⌈s ^ (9/10)⌉` iff `(x - 1) ^ 10 < s ^ 9`.
* `Cslib.Circuits.Frontier.ceilNineTenths_le_degreeBound`: the degree bound of the schedule is at
  least `⌈s ^ (9/10)⌉`.
* `Cslib.Circuits.Frontier.exists_mul_ceilNineTenths_le`: `A ⌈s ^ (9/10)⌉ ≤ s / √⌊log₂ s⌋` from
  some size on, so entry costs fit the time budget.
* `Cslib.Circuits.Frontier.EntryContraction.val_directCore`: direct summation is correct.
* `Cslib.Circuits.Frontier.EntryContraction.directCore_le`,
  `Cslib.Circuits.Frontier.EntryContraction.exists_directCore_le`: its resources.
* `Cslib.Circuits.Frontier.EntryContraction.exists_entryAdmissible_of_isPolynomial`:
  polynomial-time entry procedures meet the entry bounds.
* `Cslib.Circuits.Frontier.EntryContraction.val_directCore_tableEntry`: direct summation of an
  explicit network.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53),
  Lemma D.2 (pp. 54–56) and Appendix D.4.6–D.4.7 (pp. 63–64).
-/

public section

namespace Cslib.Circuits.Frontier

open GaloisRingArith Cslib.GenericRAM Turing.MultiTapeTM

/-! ### The nine-tenths power -/

/-- `s ^ 9 ≤ s ^ 10`. -/
theorem pow_nine_le_pow_ten_self (s : ℕ) : s ^ 9 ≤ s ^ 10 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · exact Nat.pow_le_pow_right hs (by norm_num)

/-- Some `x` has `s ^ 9 ≤ x ^ 10`. -/
theorem exists_pow_nine_le_pow_ten (s : ℕ) : ∃ x, s ^ 9 ≤ x ^ 10 :=
  ⟨s, pow_nine_le_pow_ten_self s⟩

/-- **`⌈s ^ (9/10)⌉`**, the least `x` with `s ^ 9 ≤ x ^ 10`. -/
@[expose] def ceilNineTenths (s : ℕ) : ℕ := Nat.find (exists_pow_nine_le_pow_ten s)

/-- `s ^ 9 ≤ ⌈s ^ (9/10)⌉ ^ 10`. -/
theorem pow_nine_le_ceilNineTenths_pow_ten (s : ℕ) : s ^ 9 ≤ ceilNineTenths s ^ 10 :=
  Nat.find_spec (exists_pow_nine_le_pow_ten s)

/-- `⌈s ^ (9/10)⌉ ≤ x` whenever `s ^ 9 ≤ x ^ 10`. -/
theorem ceilNineTenths_le {s x : ℕ} (h : s ^ 9 ≤ x ^ 10) : ceilNineTenths s ≤ x :=
  Nat.find_min' _ h

/-- **`x ≤ ⌈s ^ (9/10)⌉` iff `(x - 1) ^ 10 < s ^ 9`**: the condition of a degree at most
`⌈s ^ (9/10)⌉`, for `s ≥ 1`. -/
theorem le_ceilNineTenths_iff {s x : ℕ} (hs : 1 ≤ s) :
    x ≤ ceilNineTenths s ↔ (x - 1) ^ 10 < s ^ 9 := by
  constructor
  · intro hx
    by_contra h
    rw [not_lt] at h
    have h1 := ceilNineTenths_le h
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · have : 1 ≤ s ^ 9 := Nat.one_le_pow _ _ hs
      rw [Nat.zero_sub, zero_pow (by norm_num)] at h
      omega
    · omega
  · intro h
    by_contra hx
    rw [not_le] at hx
    have h1 : ceilNineTenths s ≤ x - 1 := by omega
    have h2 := (pow_nine_le_ceilNineTenths_pow_ten s).trans (Nat.pow_le_pow_left h1 10)
    omega

/-- `⌈s ^ (9/10)⌉ ≤ s`. -/
theorem ceilNineTenths_le_self (s : ℕ) : ceilNineTenths s ≤ s :=
  ceilNineTenths_le (pow_nine_le_pow_ten_self s)

/-- **The degree bound of the schedule is at least `⌈s ^ (9/10)⌉`**
(`ContractionSchedule.pow_nine_le_degreeBound_pow_ten`). -/
theorem ceilNineTenths_le_degreeBound (s : ℕ) :
    ceilNineTenths s ≤ ContractionSchedule.degreeBound s :=
  ceilNineTenths_le (ContractionSchedule.pow_nine_le_degreeBound_pow_ten s)

/-- **Entry costs fit the budget**: for every `A`, from some size on,
`A ⌈s ^ (9/10)⌉ ≤ s / √⌊log₂ s⌋`. So the entry time `2 ^ (A s ^ (9/10))` allowed by Theorem D.1
is within the `2 ^ O(s / √log s)` budget of a leaf (§D.4.7, p. 64). -/
theorem exists_mul_ceilNineTenths_le (A : ℕ) :
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → A * ceilNineTenths s ≤ s / Nat.sqrt (Nat.log 2 s) := by
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp
    (Nat.eventually_mul_add_one_pow_le_pow_div (4 * A) 1 10 one_lt_two (by norm_num))
  refine ⟨2 ^ (L₀ + 1), fun s hs => ?_⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = Nat.log 2 s := ⟨_, rfl⟩
  have hs0 : s ≠ 0 := by have := Nat.one_le_two_pow (n := L₀ + 1); omega
  have hL : L₀ + 1 ≤ L := hLdef ▸ Nat.le_log_of_pow_le one_lt_two hs
  have h1 := hL₀ L (by omega)
  rw [pow_one] at h1
  have hsq : Nat.sqrt L ≤ L + 1 := (Nat.sqrt_le_self L).trans (Nat.le_succ L)
  have hsq0 : 0 < Nat.sqrt L := Nat.sqrt_pos.2 (by omega)
  have hD : ceilNineTenths s ≤ 2 ^ (9 * L / 10 + 2) := by
    have := ceilNineTenths_le_degreeBound s
    rwa [ContractionSchedule.degreeBound, ← hLdef] at this
  have hpow : 2 ^ L ≤ s := hLdef ▸ Nat.pow_log_le_self 2 hs0
  rw [← hLdef, Nat.le_div_iff_mul_le hsq0]
  calc A * ceilNineTenths s * Nat.sqrt L ≤ A * 2 ^ (9 * L / 10 + 2) * (L + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hD) hsq
    _ = 2 ^ (9 * L / 10) * (4 * A * (L + 1)) := by rw [pow_add]; ring
    _ ≤ 2 ^ (9 * L / 10) * 2 ^ (L / 10) := Nat.mul_le_mul_left _ h1
    _ = 2 ^ (9 * L / 10 + L / 10) := (pow_add _ _ _).symm
    _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ s := hpow

/-! ### The interface -/

namespace EntryContraction

/-- **The encoding of an input `(P, fl, r, G)`**: the precision `P` in unary, the coefficients of
the modulus and the number of rows in binary, then the network. -/
abbrev encInput {T : Type} (encT : T ↪ List Bool) :
    ℕ × List ℕ × ℕ × DescribedNetwork T ↪ List Bool :=
  encPair encUnary (encPair (encList encNat) (encPair encNat (DescribedNetwork.encDescribed encT)))

end EntryContraction

variable {T : Type} {encT : T ↪ List Bool} {entry : T → List Bool → List ℕ}

/-- **Admissible networks with an entry procedure** at size `s` with constant `C` (Theorem D.1's
hypotheses, with `C` for its constants `C`, `A` and `b`): the network `G` with `r` row vertices is
rows-first bipartite, has between `s` and `C s` edges, every vertex has at most
`⌈s ^ (9/10)⌉` ports, and on every vertex and bits on its ports the entry procedure's certificate
takes time at most `C (s + L + 1) ^ C 2 ^ (C ⌈s ^ (9/10)⌉)` and space at most `C (s + L + 1) ^ C`,
for `L` the encoded length of `G`. -/
@[expose] def EntryAdmissible
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) (C s : ℕ) (G : ℕ × DescribedNetwork T) : Prop :=
  G.2.IsRowsFirstBipartite G.1 ∧ s ≤ G.2.numEdges ∧ G.2.numEdges ≤ C * s ∧
    (∀ v ∈ G.2.vertices, v.1.length ≤ ceilNineTenths s) ∧
    ∀ v ∈ G.2.vertices, ∀ bs : List Bool, bs.length = v.1.length →
      ce.time (v.2, bs) ≤
          C * (s + (DescribedNetwork.encDescribed encT G.2).length + 1) ^ C *
            2 ^ (C * ceilNineTenths s) ∧
        ce.space (v.2, bs) ≤ C * (s + (DescribedNetwork.encDescribed encT G.2).length + 1) ^ C

variable (encT entry) in
/-- **The contraction interface for entry procedures** (Theorem D.1 with `ℓ = 1`, entries in
`A_P`). A native certificate maps `(P, fl, r, G)` to a coefficient list `core (P, fl, r, G)`. At
the modulus `fl = FastContraction.modulus m`, for `m` the number of edges of `G`, its value in
`A_P` is the contraction of the values of the entries, on every input. For all constants `C` and
`D` there is `K` such that on every network admissible at a size `s ≥ 2` with constant `C`, and
every precision `1 ≤ P ≤ D s`, at that modulus the certificate takes time at most
`K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` and space at most `K (n + 1) ^ K`, for `n` the encoded length
of the input. -/
structure EntryContractionAlgorithm (Admissible : ℕ → ℕ → ℕ × DescribedNetwork T → Prop) where
  /-- The output on an input `(P, fl, r, G)`. -/
  core : ℕ × List ℕ × ℕ × DescribedNetwork T → List ℕ
  /-- Its native certificate. -/
  certificate : NativeCertificate core (EntryContraction.encInput encT) (encList encNat)
  /-- **Correctness**: at the modulus of the number of edges, the value is the contraction. -/
  val_core : ∀ (P r : ℕ) (G : DescribedNetwork T),
    val P (FastContraction.modulus G.numEdges)
        (core (P, FastContraction.modulus G.numEdges, r, G)) =
      G.contraction fun t bs => val P (FastContraction.modulus G.numEdges) (entry t bs)
  /-- Its time and space on admissible inputs at the modulus of the number of edges. -/
  bound : ∀ C D : ℕ, ∃ K : ℕ, ∀ (s P r : ℕ) (G : DescribedNetwork T), 2 ≤ s → 1 ≤ P →
    P ≤ D * s → Admissible C s (r, G) →
      certificate.time (P, FastContraction.modulus G.numEdges, r, G) ≤
          K * ((EntryContraction.encInput encT
              (P, FastContraction.modulus G.numEdges, r, G)).length + 1) ^ K *
            2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) ∧
        certificate.space (P, FastContraction.modulus G.numEdges, r, G) ≤
          K * ((EntryContraction.encInput encT
              (P, FastContraction.modulus G.numEdges, r, G)).length + 1) ^ K

/-! ### Direct summation -/

namespace EntryContraction

/-- The input of direct summation, `((P, fl), G)`, from `(P, fl, r, G)`. -/
theorem sumInput_polyTime :
    ComputableInPolyTime
      (fun ((P, fl, _, G) : ℕ × List ℕ × ℕ × DescribedNetwork T) => ((P, fl), G)) (encInput encT)
      (DescribedNetwork.encInput (encPair encUnary (encList encNat)) encT) :=
  ((ComputableInPolyTime.fst _ _).prod
    ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))).prod
    ((ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp
      (ComputableInPolyTime.snd _ _)))

variable (entry) in
/-- **Direct summation with an entry procedure**: on `(P, fl, r, G)`, the sum over all edge
assignments of the products of the entries, with the operations of `A_P` at the modulus `fl`. -/
@[expose] noncomputable def directCore
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    NativeCertificate
      (fun ((P, fl, _, G) : ℕ × List ℕ × ℕ × DescribedNetwork T) =>
        DescribedNetwork.sumValue SumOps.galois entry (P, fl) G)
      (encInput encT) (encList encNat) :=
  ((DescribedNetwork.contractionCertificate entry SumOps.galois_polyTime ce).comp
    (NativeCertificate.ofPolyTime sumInput_polyTime)).congr fun _ => rfl

/-- **Direct summation is correct**: at every modulus, the value is the contraction. -/
theorem val_directCore (P : ℕ) (fl : List ℕ) (G : DescribedNetwork T) :
    val P fl (DescribedNetwork.sumValue SumOps.galois entry (P, fl) G) =
      G.contraction fun t bs => val P fl (entry t bs) :=
  DescribedNetwork.val_sumValue_galois entry (P, fl) G

/-- The time of direct summation: the input of the sum, then the sum. -/
theorem directCore_time
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) (P : ℕ) (fl : List ℕ) (r : ℕ) (G : DescribedNetwork T) :
    (directCore entry ce).time (P, fl, r, G) =
      (NativeCertificate.ofPolyTime (sumInput_polyTime (encT := encT))).time (P, fl, r, G) +
        (DescribedNetwork.contractionCertificate entry SumOps.galois_polyTime ce).time
          ((P, fl), G) := rfl

/-- The space of direct summation. -/
theorem directCore_space
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) (P : ℕ) (fl : List ℕ) (r : ℕ) (G : DescribedNetwork T) :
    (directCore entry ce).space (P, fl, r, G) =
      (NativeCertificate.ofPolyTime (sumInput_polyTime (encT := encT))).space (P, fl, r, G) +
        (DescribedNetwork.contractionCertificate entry SumOps.galois_polyTime ce).space
          ((P, fl), G) := rfl

/-- The precision, the modulus and the input of the sum against the encoded input. -/
private theorem lengths_le (P : ℕ) (fl : List ℕ) (r : ℕ) (G : DescribedNetwork T) :
    P + fl.length ≤ (encInput encT (P, fl, r, G)).length ∧
      (DescribedNetwork.encInput (encPair encUnary (encList encNat)) encT
        ((P, fl), G)).length ≤ 2 * (encInput encT (P, fl, r, G)).length := by
  have h := length_le_length_encList encNat fl
  simp only [encInput, DescribedNetwork.encInput, length_encPair, encUnary_apply,
    List.length_replicate] at h ⊢
  omega

private theorem mul_pow_le {c W d E : ℕ} (hW : 1 ≤ W) (hd : d ≤ E) : c * W ^ d ≤ c * W ^ E :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW hd)

/-- **The resources of direct summation with an entry procedure.** There is `K` such that on an
input `(P, fl, r, G)` of encoded length `n`, with `m` edges and `k` vertices in `G`, if the entry
procedure takes time at most `E` and space at most `ES` on every vertex and bits on its ports,
then direct summation takes time at most `(2 ^ m (k + 1) + 1) (K (n + ES + 1) ^ K + 2 E)` and
space at most `K (n + ES + 1) ^ K + ES`. -/
theorem directCore_le
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    ∃ K : ℕ, ∀ (P : ℕ) (fl : List ℕ) (r : ℕ) (G : DescribedNetwork T) (E ES : ℕ),
      (∀ v ∈ G.vertices, ∀ bs : List Bool, bs.length = v.1.length →
        ce.time (v.2, bs) ≤ E ∧ ce.space (v.2, bs) ≤ ES) →
      (directCore entry ce).time (P, fl, r, G) ≤
          (2 ^ G.numEdges * (G.vertices.length + 1) + 1) *
            (K * ((encInput encT (P, fl, r, G)).length + ES + 1) ^ K + 2 * E) ∧
        (directCore entry ce).space (P, fl, r, G) ≤
          K * ((encInput encT (P, fl, r, G)).length + ES + 1) ^ K + ES := by
  obtain ⟨K₁, hK₁⟩ := DescribedNetwork.contractionCertificate_le (ops := SumOps.galois)
    (eval := entry) (encQ := encPair encUnary (encList encNat)) (encY := encList encNat)
    (encT := encT) SumOps.galois_polyTime ce
  obtain ⟨c, -, hout⟩ := ce.computes
  have hI := NativeCertificate.ofPolyTime_isPolynomial (sumInput_polyTime (encT := encT))
  obtain ⟨ct, dt, hit⟩ := hI.1.exists_le
  obtain ⟨cs, ds, his⟩ := hI.2.exists_le
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = K₁ * (c + 6) ^ K₁ := ⟨_, rfl⟩
  refine ⟨ct + cs + c₁ + dt + ds + 2 * K₁, fun P fl r G E ES hE => ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, n = (encInput encT (P, fl, r, G)).length := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = n + ES + 1 := ⟨_, rfl⟩
  rw [← hn, show n + ES + 1 = W from hW.symm]
  have hW1 : 1 ≤ W := by omega
  obtain ⟨hPfl, hproj⟩ := lengths_le P fl r G
  rw [← hn] at hPfl hproj
  have hRv : ∀ y, SumOps.galois.Reduced (P, fl) y →
      (encList encNat y).length ≤ n * (2 * n + 3) := fun y hy =>
    (SumOps.length_encList_le_of_galois_reduced hy).trans (Nat.mul_le_mul (by simp only; omega)
      (by simp only; omega))
  have hEv : ∀ v ∈ G.vertices, ∀ bs : List Bool,
      bs.length = v.1.length → ce.time (v.2, bs) ≤ E ∧ ce.space (v.2, bs) ≤ ES ∧
        (encList encNat (entry v.2 bs)).length ≤ c * (ES + 1) := fun v hv bs hbs =>
    ⟨(hE v hv bs hbs).1, (hE v hv bs hbs).2,
      (hout (v.2, bs)).trans (Nat.mul_le_mul_left _ (by have := (hE v hv bs hbs).2; omega))⟩
  obtain ⟨hT, hS⟩ := hK₁ ((P, fl), G) E ES (c * (ES + 1)) (n * (2 * n + 3)) hEv hRv
  -- The argument of direct summation's polynomial against `W ^ 2`.
  have hA : (DescribedNetwork.encInput (encPair encUnary (encList encNat)) encT
      ((P, fl), G)).length + c * (ES + 1) + n * (2 * n + 3) + 1 ≤ (c + 6) * W ^ 2 := by
    have h1 : c * (ES + 1) ≤ c * W := Nat.mul_le_mul_left _ (by omega)
    have h2 : c * W ≤ c * W ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
    have h3 : n * (2 * n + 3) + 2 * n + 1 ≤ 6 * W ^ 2 := by nlinarith
    nlinarith
  have hpoly : K₁ * ((DescribedNetwork.encInput (encPair encUnary (encList encNat)) encT
      ((P, fl), G)).length + c * (ES + 1) + n * (2 * n + 3) + 1) ^ K₁ ≤
      c₁ * W ^ (2 * K₁) := by
    rw [hc₁, pow_mul, Nat.mul_assoc, ← Nat.mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA _)
  have hnW : n + 1 ≤ W := by omega
  have hit' : (NativeCertificate.ofPolyTime (sumInput_polyTime (encT := encT))).time
      (P, fl, r, G) ≤ ct * W ^ dt := by
    have h := hit (P, fl, r, G)
    rw [← hn] at h
    exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnW _))
  have his' : (NativeCertificate.ofPolyTime (sumInput_polyTime (encT := encT))).space
      (P, fl, r, G) ≤ cs * W ^ ds := by
    have h := his (P, fl, r, G)
    rw [← hn] at h
    exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnW _))
  obtain ⟨K, hK⟩ : ∃ K, K = ct + cs + c₁ + dt + ds + 2 * K₁ := ⟨_, rfl⟩
  rw [← hK]
  have hct : ct * W ^ dt ≤ ct * W ^ K := mul_pow_le hW1 (by omega)
  have hcs : cs * W ^ ds ≤ cs * W ^ K := mul_pow_le hW1 (by omega)
  have hc1 : c₁ * W ^ (2 * K₁) ≤ c₁ * W ^ K := mul_pow_le hW1 (by omega)
  have hsum : ct * W ^ K + cs * W ^ K + c₁ * W ^ K ≤ K * W ^ K := by
    rw [← Nat.add_mul, ← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have hP1 : 1 ≤ 2 ^ G.numEdges * (G.vertices.length + 1) + 1 := by omega
  constructor
  · rw [directCore_time]
    calc _ ≤ ct * W ^ dt + (2 ^ G.numEdges * (G.vertices.length + 1) + 1) *
          (c₁ * W ^ (2 * K₁) + 2 * E) :=
          Nat.add_le_add hit' (hT.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hpoly _)))
      _ ≤ (2 ^ G.numEdges * (G.vertices.length + 1) + 1) *
          (ct * W ^ K + (c₁ * W ^ K + 2 * E)) := by
          rw [Nat.mul_add _ (ct * W ^ K)]
          refine Nat.add_le_add ((hct.trans (Nat.le_mul_of_pos_left _ hP1))) ?_
          exact Nat.mul_le_mul_left _ (by omega)
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  · rw [directCore_space]
    calc _ ≤ cs * W ^ ds + (c₁ * W ^ (2 * K₁) + ES) :=
          Nat.add_le_add his' (hS.trans (Nat.add_le_add_right hpoly _))
      _ ≤ _ := by omega

/-- **Direct summation on admissible inputs** takes time `K (n + 1) ^ K 2 ^ (K s)` and space
`K (n + 1) ^ K`, at the modulus of the number of edges, for `K` depending only on the constants:
the fallback of the contraction algorithm for small sizes. -/
theorem exists_directCore_le
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) (C : ℕ) :
    ∃ K : ℕ, ∀ (s P r : ℕ) (G : DescribedNetwork T), EntryAdmissible ce C s (r, G) →
      (directCore entry ce).time (P, FastContraction.modulus G.numEdges, r, G) ≤
          K * ((encInput encT (P, FastContraction.modulus G.numEdges, r, G)).length + 1) ^ K *
            2 ^ (K * s) ∧
        (directCore entry ce).space (P, FastContraction.modulus G.numEdges, r, G) ≤
          K * ((encInput encT (P, FastContraction.modulus G.numEdges, r, G)).length + 1) ^ K := by
  obtain ⟨K₀, hK₀⟩ := directCore_le (entry := entry) ce
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = C * 3 ^ C + 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = 4 * (K₀ * (c₀ + 1) ^ K₀ + c₀ + 1) * 2 + K₀ * (C + 1) + C + 3 :=
    ⟨_, rfl⟩
  refine ⟨K, fun s P r G hA => ?_⟩
  obtain ⟨-, hsm, hmC, -, hent⟩ := hA
  simp only at hsm hmC hent
  obtain ⟨n, hn⟩ : ∃ n, n = (encInput encT (P, FastContraction.modulus G.numEdges, r, G)).length :=
    ⟨_, rfl⟩
  rw [← hn]
  -- The size, the network and the vertices against `n`.
  have hG : (DescribedNetwork.encDescribed encT G).length ≤ n := by
    rw [hn]; simp only [encInput, length_encPair]; omega
  have hmk := DescribedNetwork.length_numEdges_vertices_le (encT := encT) G
  have hsn : s ≤ n := by omega
  have hB : s + (DescribedNetwork.encDescribed encT G).length + 1 ≤ 3 * (n + 1) := by omega
  -- The entry bounds.
  obtain ⟨E, hE⟩ : ∃ E, E = c₀ * (n + 1) ^ C * 2 ^ (C * s) := ⟨_, rfl⟩
  obtain ⟨ES, hES⟩ : ∃ ES, ES = c₀ * (n + 1) ^ C := ⟨_, rfl⟩
  have hpowB : C * (s + (DescribedNetwork.encDescribed encT G).length + 1) ^ C ≤ ES := by
    rw [hES]
    calc C * (s + (DescribedNetwork.encDescribed encT G).length + 1) ^ C
        ≤ C * (3 * (n + 1)) ^ C := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB _)
      _ = C * 3 ^ C * (n + 1) ^ C := by rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ c₀ * (n + 1) ^ C := Nat.mul_le_mul_right _ (by omega)
  have hbnd : ∀ v ∈ G.vertices, ∀ bs : List Bool, bs.length = v.1.length →
      ce.time (v.2, bs) ≤ E ∧ ce.space (v.2, bs) ≤ ES := by
    intro v hv bs hbs
    obtain ⟨ht, hs⟩ := hent v hv bs hbs
    refine ⟨ht.trans ?_, hs.trans hpowB⟩
    rw [hE, show c₀ * (n + 1) ^ C * 2 ^ (C * s) = (c₀ * (n + 1) ^ C) * 2 ^ (C * s) from rfl]
    exact Nat.mul_le_mul (hES ▸ hpowB) (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left _ (ceilNineTenths_le_self s)))
  obtain ⟨hT, hS⟩ := hK₀ P (FastContraction.modulus G.numEdges) r G E ES hbnd
  rw [← hn] at hT hS
  -- Arithmetic.
  have hn1 : 1 ≤ n + 1 := by omega
  have hWES : n + ES + 1 ≤ (c₀ + 1) * (n + 1) ^ (C + 1) := by
    have h1 : n + 1 ≤ (n + 1) ^ (C + 1) := by
      calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (n + 1) ^ (C + 1) := Nat.pow_le_pow_right hn1 (by omega)
    have h2 : ES ≤ c₀ * (n + 1) ^ (C + 1) := by
      rw [hES]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn1 (by omega))
    rw [Nat.add_mul, one_mul]; omega
  obtain ⟨A₀, hA₀⟩ : ∃ A₀, A₀ = K₀ * (c₀ + 1) ^ K₀ := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = n + 1 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 2 ^ (C * s) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = (C + 1) * K₀ + C := ⟨_, rfl⟩
  rw [← hX] at hn1 hWES hE hES ⊢
  rw [← hY] at hE
  have hX1 : 1 ≤ X := hn1
  have hY1 : 1 ≤ Y := hY ▸ Nat.one_le_two_pow
  have hpoly : K₀ * (n + ES + 1) ^ K₀ ≤ A₀ * X ^ ((C + 1) * K₀) := by
    rw [hA₀, pow_mul, Nat.mul_assoc, ← Nat.mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hWES _)
  have hXe1 : X ^ ((C + 1) * K₀) ≤ X ^ e := Nat.pow_le_pow_right hX1 (by omega)
  have hXe2 : X ^ C ≤ X ^ e := Nat.pow_le_pow_right hX1 (by omega)
  -- The number of assignments and vertices.
  have hk : G.vertices.length + 1 ≤ X := by omega
  have hm : 2 ^ G.numEdges ≤ Y := hY ▸ Nat.pow_le_pow_right (by norm_num) hmC
  have hcount : 2 ^ G.numEdges * (G.vertices.length + 1) + 1 ≤ 2 * (Y * X) := by
    have := Nat.mul_le_mul hm hk
    have : 1 ≤ Y * X := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hinner : K₀ * (n + ES + 1) ^ K₀ + 2 * E ≤ (A₀ + 2 * c₀) * X ^ e * Y := by
    have h1 : A₀ * X ^ ((C + 1) * K₀) ≤ A₀ * X ^ e * Y :=
      (Nat.mul_le_mul_left _ hXe1).trans (Nat.le_mul_of_pos_right _ hY1)
    have h2 : 2 * E ≤ 2 * c₀ * X ^ e * Y := by
      rw [hE, Nat.mul_assoc 2 c₀, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hXe2))
    have e3 : (A₀ + 2 * c₀) * X ^ e * Y = A₀ * X ^ e * Y + 2 * c₀ * X ^ e * Y := by ring
    omega
  have hCc : C ≤ c₀ := by
    have : C ≤ C * 3 ^ C := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hKc : 2 * (A₀ + 2 * c₀) ≤ K := by rw [hK, ← hA₀]; omega
  have hKe : e + 1 ≤ K := by
    have : (C + 1) * K₀ = K₀ * (C + 1) := Nat.mul_comm _ _
    rw [hK, he]; omega
  have hKY : Y * Y ≤ 2 ^ (K * s) := by
    have h2C : 2 * C ≤ K := by rw [hK]; omega
    rw [hY, ← pow_add]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    calc C * s + C * s = 2 * C * s := by ring
      _ ≤ K * s := Nat.mul_le_mul_right _ h2C
  constructor
  · calc _ ≤ 2 * (Y * X) * ((A₀ + 2 * c₀) * X ^ e * Y) := hT.trans (Nat.mul_le_mul hcount hinner)
      _ = 2 * (A₀ + 2 * c₀) * X ^ (e + 1) * (Y * Y) := by rw [pow_succ]; ring
      _ ≤ K * X ^ K * 2 ^ (K * s) :=
          Nat.mul_le_mul (Nat.mul_le_mul hKc (Nat.pow_le_pow_right hX1 hKe)) hKY
  · have h1 : ES ≤ c₀ * X ^ e := hES ▸ Nat.mul_le_mul_left _ hXe2
    calc _ ≤ A₀ * X ^ e + c₀ * X ^ e :=
          hS.trans (Nat.add_le_add (hpoly.trans (Nat.mul_le_mul_left _ hXe1)) h1)
      _ = (A₀ + c₀) * X ^ e := by ring
      _ ≤ K * X ^ K := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hX1 (by omega))

/-! ### Polynomial-time entry procedures and tables -/

/-- **Polynomial-time entry procedures meet the entry bounds.** For a polynomial certificate of the
entry procedure there is `C₀` such that, for every `C ≥ C₀`, a rows-first network with between
`s` and `C s` edges and degree at most `⌈s ^ (9/10)⌉` is admissible at size `s` with constant
`C`. -/
theorem exists_entryAdmissible_of_isPolynomial
    {ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)} (hce : ce.IsPolynomial) :
    ∃ C₀ : ℕ, ∀ (C s r : ℕ) (G : DescribedNetwork T), C₀ ≤ C → G.IsRowsFirstBipartite r →
      s ≤ G.numEdges → G.numEdges ≤ C * s → (∀ v ∈ G.vertices, v.1.length ≤ ceilNineTenths s) →
        EntryAdmissible ce C s (r, G) := by
  obtain ⟨ct, dt, ht⟩ := hce.1.exists_le
  obtain ⟨cs, ds, hs⟩ := hce.2.exists_le
  refine ⟨ct * 3 ^ dt + cs * 3 ^ ds + dt + ds + 1, fun C s r G hC hrows hsm hmC hdeg =>
    ⟨hrows, hsm, hmC, hdeg, fun v hv bs hbs => ?_⟩⟩
  change v ∈ G.vertices at hv
  obtain ⟨B, hB⟩ : ∃ B, B = s + (DescribedNetwork.encDescribed encT G).length + 1 := ⟨_, rfl⟩
  rw [← hB]
  have hB1 : 1 ≤ B := by omega
  -- The argument of the procedure is at most `3 B`.
  have hq : (encPair encT encBits (v.2, bs)).length + 1 ≤ 3 * B := by
    have h1 := length_le_encList_of_mem (encPair (encList encNat) encT) hv
    have h2 : (encList (encPair (encList encNat) encT) G.vertices).length ≤
        (DescribedNetwork.encDescribed encT G).length := by
      change _ ≤ (encPair encUnary (encList (encPair (encList encNat) encT))
        (G.numEdges, G.vertices)).length
      rw [length_encPair]
      dsimp only
      omega
    have h3 := length_le_length_encList encNat v.1
    rw [length_encPair] at h1 ⊢
    change 2 * (encT v.2).length + 1 + bs.length + 1 ≤ 3 * B
    omega
  have hpow {c d : ℕ} : c * ((encPair encT encBits (v.2, bs)).length + 1) ^ d ≤
      c * 3 ^ d * B ^ d := by
    rw [Nat.mul_assoc, ← Nat.mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq _)
  have hBC {c d : ℕ} (hc : c ≤ C) (hd : d ≤ C) : c * B ^ d ≤ C * B ^ C :=
    Nat.mul_le_mul hc (Nat.pow_le_pow_right hB1 hd)
  refine ⟨(ht _).trans (hpow.trans ((hBC (by omega) (by omega)).trans
    (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow))), (hs _).trans (hpow.trans
      (hBC (by omega) (by omega)))⟩

/-- **Direct summation of a table network is its contraction**, in `A_P` at every modulus. -/
theorem val_directCore_tableEntry (P : ℕ) (fl : List ℕ) (G : ExplicitTensorNetwork ℕ) :
    val P fl (DescribedNetwork.sumValue SumOps.galois tableEntry (P, fl) G) =
      (G.contraction : GaloisRingArith.Ring P fl) := by
  rw [val_directCore, ← DescribedNetwork.contraction_entry]
  have h := DescribedNetwork.map_contraction (Nat.castRingHom (GaloisRingArith.Ring P fl))
    ExplicitTensorNetwork.entry G
  simp only [Nat.coe_castRingHom] at h
  rw [h]
  congr 1
  funext t bs
  exact VertexDesc.val_entry_inl P fl t bs

end EntryContraction

end Cslib.Circuits.Frontier
