/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.TruncatedAlgorithm
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.EntryContraction
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Theorem D.1 at truncation order `ℓ` for entry procedures

Theorem D.1 of [OpenAI2026ETH] (p. 53) contracts networks whose entries lie in
`B_{P,ℓ} = (ℤ / 2 ^ P)[V] / (V ^ ℓ)` and are computed by procedures. This file reduces it to the
case `ℓ = 1` with entries in `A_P = (ℤ / 2 ^ P)[U] / (f)`: from a contraction algorithm for entry
procedures (`Cslib.Circuits.Frontier.EntryContractionAlgorithm`) for the specialized entries,
`Cslib.Circuits.Frontier.TruncatedContractionAlgorithm.ofEntry` builds a truncated contraction
algorithm for the original entries. It instantiates the assembly
`Cslib.Circuits.Frontier.TruncatedContractionAlgorithm.ofCore` and discharges its hypotheses.

**Admissible networks** (`Cslib.Circuits.Frontier.TruncEntryAdmissible`). The hypotheses of
Theorem D.1 as in `Cslib.Circuits.Frontier.EntryAdmissible`, plus **at most `C s` vertices**. The
precision is bounded by `D s (⌊log₂ s⌋ + 1)` and the truncation order by `D (s + 1) ^ d`, for
fixed `D` and `d`, in the interface itself.

*Narrowing against Theorem D.1.* The theorem asks only that the number of vertices be bounded by
a fixed polynomial in `s`. The bound `k ≤ C s` is what the assembly needs: the reduction of
truncation order `ℓ` to `A_P` interpolates at `(ℓ - 1) k + 1` points, which must fit in the
residues of the modulus `FastContraction.modulus m`. These eventually outnumber every fixed
polynomial in `m` (`FastContraction.pow_le_card_modulus`), so polynomial truncation passes the
guard beyond a constant size. Below that size direct summation costs a constant factor.
The applications satisfy the linear vertex bound: the network of Lemma D.2 (p. 56) has
`2 J = 2 ⌈n ^ (1/4)⌉` vertices at size `s = n ν`, and that of the fixed-density bound (§D.2,
p. 54) has `O_k(n + m)` vertices at size `s = n + m`.

**The hypotheses of the assembly.**
* *Specialization keeps networks admissible* (`EntryContraction.exists_entryAdmissible_specNet`):
  the specialized network has the same ports, and evaluating a specialized entry costs the original
  entry plus a polynomial in the lengths of its input and of the original entry
  (`Cslib.Circuits.Frontier.specEntryCertificate_le`). The original entry is at most linear in its
  space, and specialization does not shorten the encoded network
  (`DescribedNetwork.length_encDescribed_le_specNet`).
* *Entries within `poly(L) 2 ^ O(s)`* (`EntryContraction.exists_entry_le_of_entryAdmissible`): the
  number of edges is in unary in the encoding, so `s ≤ L`, and `⌈s ^ (9/10)⌉ ≤ s`.
* *The shape*: between `s` and `C s` edges by `EntryAdmissible`, and at most `C s` vertices.

## Main definitions

* `Cslib.Circuits.Frontier.TruncEntryAdmissible`: the admissible networks.
* `Cslib.Circuits.Frontier.TruncatedContractionAlgorithm.ofEntry`: the truncated contraction
  algorithm from a contraction algorithm for the specialized entries.

## Main results

* `Cslib.Circuits.Frontier.DescribedNetwork.isRowsFirstBipartite_specNet_iff`: specialization
  keeps a network rows-first.
* `Cslib.Circuits.Frontier.DescribedNetwork.length_encDescribed_le_specNet`: specialization does
  not shorten the encoded network.
* `Cslib.Circuits.Frontier.EntryContraction.exists_entryAdmissible_specNet`: specialization keeps
  networks admissible.
* `Cslib.Circuits.Frontier.EntryContraction.exists_entry_le_of_entryAdmissible`: entries within
  `poly(L) 2 ^ O(s)` on admissible networks.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53), the
  fixed-density bound (§D.2, p. 54) and Lemma D.2 (pp. 54–56).
-/

public section

namespace Cslib.Circuits.Frontier

open Turing.MultiTapeTM Cslib.GenericRAM

variable {T : Type} {encT : T ↪ List Bool} {entry : T → List Bool → List ℕ}

namespace DescribedNetwork

/-- **Specialization keeps a network rows-first**: it keeps the ports. -/
theorem isRowsFirstBipartite_specNet_iff (P ℓ : ℕ) (fl ζ : List ℕ) (G : DescribedNetwork T)
    (r : ℕ) : (specNet P ℓ fl ζ G).IsRowsFirstBipartite r ↔ G.IsRowsFirstBipartite r := by
  simp only [IsRowsFirstBipartite, numEdges_specNet, vertices_specNet, List.forall_mem_map,
    ← List.map_take, ← List.map_drop, List.map_map, Function.comp_def]

/-- **Specialization does not shorten the encoded network**: each descriptor `t` becomes
`(t, P, ℓ, fl, ζ)`. -/
theorem length_encDescribed_le_specNet (P ℓ : ℕ) (fl ζ : List ℕ) (G : DescribedNetwork T) :
    (encDescribed encT G).length ≤
      (encDescribed (encSpecDesc encT) (specNet P ℓ fl ζ G)).length := by
  change (encPair encUnary (encList (encPair (encList encNat) encT))
      (G.numEdges, G.vertices)).length ≤
    (encPair encUnary (encList (encPair (encList encNat) (encSpecDesc encT)))
      (G.numEdges, G.vertices.map fun v => (v.1, (v.2, P, ℓ, fl, ζ)))).length
  simp only [length_encPair, length_encList, List.map_map]
  refine Nat.add_le_add_left (List.sum_le_sum fun v _ => ?_) _
  simp only [Function.comp_apply]
  omega

end DescribedNetwork

/-- **Admissible networks for Theorem D.1 at truncation order `ℓ`**, with an entry procedure, at
size `s` with constant `C`: the network `G` with `r` row vertices is admissible for `ce`
(`EntryAdmissible`: rows-first bipartite, between `s` and `C s` edges, degree at most
`⌈s ^ (9/10)⌉`, entries within `C (s + L + 1) ^ C 2 ^ (C ⌈s ^ (9/10)⌉)` time and
`C (s + L + 1) ^ C` space) and has **at most `C s` vertices**.

The vertex bound narrows Theorem D.1 of [OpenAI2026ETH] (p. 53), which asks only for a polynomial
bound in `s`. The networks of Lemma D.2 (p. 56) and of the fixed-density bound (§D.2, p. 54)
satisfy it. -/
@[expose] def TruncEntryAdmissible
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) (C s : ℕ) (G : ℕ × DescribedNetwork T) : Prop :=
  EntryAdmissible ce C s G ∧ G.2.vertices.length ≤ C * s

namespace EntryContraction

variable (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
  (encList encNat))

/-- **Specialization keeps networks admissible.** For every entry certificate `ce` and constant
`C` there is `C'` such that, for every network `G` admissible for `ce` at size `s` with constant
`C`, every network specialized from it, at any precision `P`, truncation order `ℓ`, modulus `fl`
and point `ζ`, is admissible for the specialized entries (`specEntryCertificate entry ce`) at
size `s` with constant `C'`. -/
theorem exists_entryAdmissible_specNet (C : ℕ) :
    ∃ C' : ℕ, ∀ (s P ℓ r : ℕ) (fl ζ : List ℕ) (G : DescribedNetwork T),
      EntryAdmissible ce C s (r, G) →
        EntryAdmissible (specEntryCertificate entry ce) C' s
          (r, DescribedNetwork.specNet P ℓ fl ζ G) := by
  obtain ⟨K₁, hK₁⟩ := specEntryCertificate_le (encT := encT)
  obtain ⟨cO, -, hcO⟩ := ce.computes
  -- The overhead of specialization, as a polynomial in `s + L'`.
  let f : ℕ → ℕ := fun n => K₁ * (3 * n + 3 + cO * (C * (n + 1) ^ C + 1) + 1) ^ K₁
  have hf : PolyBounded id f :=
    (PolyBounded.const K₁).mul (((((PolyBounded.const 3).mul PolyBounded.self).add
      (PolyBounded.const 3)).add ((PolyBounded.const cO).mul (((PolyBounded.const C).mul
        ((PolyBounded.self.add (PolyBounded.const 1)).pow C)).add (PolyBounded.const 1)))).add
      (PolyBounded.const 1) |>.pow K₁)
  obtain ⟨a, d, had⟩ := hf.exists_le
  refine ⟨C + a + d, fun s P ℓ r fl ζ G hA => ?_⟩
  obtain ⟨hrows, hsm, hmC, hdeg, hent⟩ := hA
  refine ⟨(DescribedNetwork.isRowsFirstBipartite_specNet_iff P ℓ fl ζ G r).2 hrows, hsm,
    hmC.trans (Nat.mul_le_mul_right _ (by omega)), ?_, ?_⟩
  · intro v hv
    change v ∈ G.vertices.map _ at hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact hdeg u hu
  · intro v hv bs hbs
    have hv' := hv
    change v ∈ G.vertices.map _ at hv'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv'
    change bs.length = u.1.length at hbs
    set L' := (DescribedNetwork.encDescribed (encSpecDesc encT)
      (DescribedNetwork.specNet P ℓ fl ζ G)).length with hL'
    have hLL : (DescribedNetwork.encDescribed encT G).length ≤ L' :=
      DescribedNetwork.length_encDescribed_le_specNet P ℓ fl ζ G
    set n := s + L' with hn
    have hn1 : 1 ≤ n + 1 := by omega
    obtain ⟨hT, hS⟩ := hent u hu bs hbs
    have hbase : C * (s + (DescribedNetwork.encDescribed encT G).length + 1) ^ C ≤
        C * (n + 1) ^ C :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    -- The input of the specialized entry is at most `3 n + 3` bits.
    have hq : (encPair (encSpecDesc encT) encBits ((u.2, P, ℓ, fl, ζ), bs)).length ≤ 3 * n + 3 := by
      have h1 := length_le_encList_of_mem (encPair (encList encNat) (encSpecDesc encT)) hv
      have h2 : (encList (encPair (encList encNat) (encSpecDesc encT))
          (DescribedNetwork.specNet P ℓ fl ζ G).vertices).length ≤ L' := by
        rw [hL']
        change _ ≤ (encPair encUnary (encList (encPair (encList encNat) (encSpecDesc encT)))
          ((DescribedNetwork.specNet P ℓ fl ζ G).numEdges,
            (DescribedNetwork.specNet P ℓ fl ζ G).vertices)).length
        rw [length_encPair]
        dsimp only
        omega
      have h3 := length_le_length_encList encNat u.1
      rw [length_encPair] at h1 ⊢
      change 2 * (encSpecDesc encT (u.2, P, ℓ, fl, ζ)).length + 1 + bs.length ≤ 3 * n + 3
      dsimp only at h1
      omega
    -- The original entry is at most `cO (C (n + 1) ^ C + 1)` bits.
    have hout : (encList encNat (entry u.2 bs)).length ≤ cO * (C * (n + 1) ^ C + 1) :=
      (hcO (u.2, bs)).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (hS.trans hbase) 1))
    obtain ⟨hT', hS'⟩ := hK₁ entry ce u.2 P ℓ fl ζ bs
    have hover : K₁ * ((encPair (encSpecDesc encT) encBits ((u.2, P, ℓ, fl, ζ), bs)).length +
        (encList encNat (entry u.2 bs)).length + 1) ^ K₁ ≤ a * (n + 1) ^ d := by
      refine le_trans ?_ (had n)
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    have hpow {c e : ℕ} (hc : c ≤ C + a + d) (he : e ≤ C + a + d) :
        c * (n + 1) ^ e ≤ (C + a + d) * (n + 1) ^ (C + a + d) :=
      Nat.mul_le_mul hc (Nat.pow_le_pow_right hn1 he)
    have h2 : 2 ^ (C * ceilNineTenths s) ≤ 2 ^ ((C + a + d) * ceilNineTenths s) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
    have hX1 : 1 ≤ 2 ^ ((C + a + d) * ceilNineTenths s) := Nat.one_le_two_pow
    have hsplit : C * (n + 1) ^ C + a * (n + 1) ^ d ≤
        (C + a + d) * (n + 1) ^ (C + a + d) := by
      have e1 := hpow (c := C) (e := C) (by omega) (by omega)
      have e2 := hpow (c := a) (e := d) (by omega) (by omega)
      have e3 : C * (n + 1) ^ (C + a + d) + a * (n + 1) ^ (C + a + d) ≤
          (C + a + d) * (n + 1) ^ (C + a + d) := by
        rw [← Nat.add_mul]
        exact Nat.mul_le_mul_right _ (by omega)
      have e1' : C * (n + 1) ^ C ≤ C * (n + 1) ^ (C + a + d) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn1 (by omega))
      have e2' : a * (n + 1) ^ d ≤ a * (n + 1) ^ (C + a + d) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn1 (by omega))
      omega
    refine ⟨?_, ?_⟩
    · change (specEntryCertificate entry ce).time ((u.2, P, ℓ, fl, ζ), bs) ≤
        (C + a + d) * (n + 1) ^ (C + a + d) * 2 ^ ((C + a + d) * ceilNineTenths s)
      have hT2 : ce.time (u.2, bs) ≤ C * (n + 1) ^ C * 2 ^ ((C + a + d) * ceilNineTenths s) :=
        hT.trans (Nat.mul_le_mul (hbase) h2)
      have hA2 : a * (n + 1) ^ d ≤ a * (n + 1) ^ d * 2 ^ ((C + a + d) * ceilNineTenths s) :=
        Nat.le_mul_of_pos_right _ hX1
      calc (specEntryCertificate entry ce).time ((u.2, P, ℓ, fl, ζ), bs)
          ≤ C * (n + 1) ^ C * 2 ^ ((C + a + d) * ceilNineTenths s) +
              a * (n + 1) ^ d * 2 ^ ((C + a + d) * ceilNineTenths s) := by
            omega
        _ = (C * (n + 1) ^ C + a * (n + 1) ^ d) * 2 ^ ((C + a + d) * ceilNineTenths s) := by
            ring
        _ ≤ (C + a + d) * (n + 1) ^ (C + a + d) * 2 ^ ((C + a + d) * ceilNineTenths s) :=
            Nat.mul_le_mul_right _ hsplit
    · change (specEntryCertificate entry ce).space ((u.2, P, ℓ, fl, ζ), bs) ≤
        (C + a + d) * (n + 1) ^ (C + a + d)
      have := hS.trans hbase
      omega

/-- **Entries within `poly(L) 2 ^ O(s)` on admissible networks.** For every constant `C` there is
`K` such that on every network admissible for `ce` at size `s` with constant `C`, of encoded length
`L`, every entry takes time at most `K (L + 1) ^ K 2 ^ (K s)` and space at most `K (L + 1) ^ K`:
the number of edges is in unary in the encoding, so `s ≤ L`, and `⌈s ^ (9/10)⌉ ≤ s`. -/
theorem exists_entry_le_of_entryAdmissible (C : ℕ) :
    ∃ K : ℕ, ∀ (s r : ℕ) (G : DescribedNetwork T), EntryAdmissible ce C s (r, G) →
      ∀ v ∈ G.vertices, ∀ bs : List Bool, bs.length = v.1.length →
        ce.time (v.2, bs) ≤
            K * ((DescribedNetwork.encDescribed encT G).length + 1) ^ K * 2 ^ (K * s) ∧
          ce.space (v.2, bs) ≤ K * ((DescribedNetwork.encDescribed encT G).length + 1) ^ K := by
  refine ⟨C * 2 ^ C + C, fun s r G hA v hv bs hbs => ?_⟩
  obtain ⟨-, hsm, -, -, hent⟩ := hA
  change s ≤ G.numEdges at hsm
  obtain ⟨hT, hS⟩ := hent v hv bs hbs
  set L := (DescribedNetwork.encDescribed encT G).length with hL
  have hmL := DescribedNetwork.length_numEdges_vertices_le (encT := encT) G
  have hL1 : 1 ≤ L + 1 := by omega
  -- `C (s + L + 1) ^ C ≤ C 2 ^ C (L + 1) ^ C ≤ K (L + 1) ^ K`.
  have hbase : C * (s + L + 1) ^ C ≤ (C * 2 ^ C + C) * (L + 1) ^ (C * 2 ^ C + C) := by
    calc C * (s + L + 1) ^ C ≤ C * (2 * (L + 1)) ^ C :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = C * 2 ^ C * (L + 1) ^ C := by rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ (C * 2 ^ C + C) * (L + 1) ^ (C * 2 ^ C + C) :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hL1 (by omega))
  have h2 : 2 ^ (C * ceilNineTenths s) ≤ 2 ^ ((C * 2 ^ C + C) * s) :=
    Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul (by omega) (ceilNineTenths_le_self s))
  exact ⟨hT.trans (Nat.mul_le_mul hbase h2), hS.trans hbase⟩

end EntryContraction

/-- **Theorem D.1 at truncation order `ℓ` for entry procedures, from the case `ℓ = 1`.** Let `ce`
be a native certificate of an entry procedure, and `A` a contraction algorithm for the specialized
entries (`specEntry entry`, with the certificate `specEntryCertificate entry ce`) on the networks
admissible for them. Then the assembly `TruncatedContractionAlgorithm.ofCore` around `A` is a
truncated contraction algorithm for the networks admissible for `ce` with at most `C s` vertices
(`TruncEntryAdmissible ce`): it computes the contraction in `B_{P,ℓ}` in time
`poly(n) 2 ^ O(s / √⌊log₂ s⌋)` and polynomial space, for
`1 ≤ P ≤ D s (⌊log₂ s⌋ + 1)` and `1 ≤ ℓ ≤ D (s + 1) ^ d`, for fixed `D`, `d`. -/
noncomputable def TruncatedContractionAlgorithm.ofEntry
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat))
    (A : EntryContractionAlgorithm (encSpecDesc encT) (specEntry entry)
      (EntryAdmissible (specEntryCertificate entry ce))) :
    TruncatedContractionAlgorithm encT entry (TruncEntryAdmissible ce) :=
  ofCore (core := A.core) A.certificate A.val_core A.bound_logPrecision
    (fun C _ _ => by
      obtain ⟨C', hC'⟩ := EntryContraction.exists_entryAdmissible_specNet ce C
      exact ⟨C', fun s P ℓ r _ G _ _ _ _ _ hA => hC' s P ℓ r _ _ G hA.1⟩)
    ce
    (fun C => by
      obtain ⟨K, hK⟩ := EntryContraction.exists_entry_le_of_entryAdmissible ce C
      exact ⟨K, fun s r G hA => hK s r G hA.1⟩)
    (fun _ _ _ _ hA => ⟨hA.1.2.1, hA.1.2.2.1, hA.2⟩)

end Cslib.Circuits.Frontier
