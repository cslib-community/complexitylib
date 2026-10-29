/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Encoding.Certificate
public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.MCSP.NP
public import Complexity.Computability.MCSP.Succinct
public import Complexity.Foundations.Data.BitString.Enumeration
import Complexity.Computability.Circuit.Boolean.Hierarchy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Succinct MCSP is in NP

We define standard string encodings for instances of the Succinct Minimum Circuit Size Problem
(`Cslib.SuccinctMCSP.Instance`) and prove that `SuccinctMCSP` belongs to `NP` under both encodings:
* `Cslib.SuccinctMCSP.enc`: encodes the arity in unary (`encUnary`), the canonical list of
  input-output samples using `encList (encPair encBits encBool)`, and the threshold in unary
  (`encUnary`). This is equivalent up to field order and list framing (`t` is implicit in `encList`)
  to the encoding `⟨1^n, 1^s, 1^t, (x_1, b_1), …, (x_t, b_t)⟩` of
  [OliveiraPichSanthanam2019, Section 4.1, proof of Theorem 1.4], and the two are computable from
  each other in polynomial time.
* `Cslib.SuccinctMCSP.encBinary`: encodes the arity in unary, the canonical list of samples, and
  the threshold in binary (`encNat`).

Any consistent sample set `samples` on `n` variables is satisfied by the sparse DNF indicator
function `sampleFunction samples` of circuit complexity at most `samples.card * (2 * n + 3) + 1`
(`complexity_sampleFunction_le`). A certificate for `SuccinctMCSP` can therefore be capped at
`MCSP.sampleBudget n samples.card s = min s (samples.card * (2 * n + 3) + 1)` gates, which is
polynomial in the encoded instance length even when `samples.card ≪ 2 ^ n` and the threshold `s` is
given in binary. The verifier instantiates `MCSP.checkCertificateOn` with the listed samples.

## Main definitions

* `Cslib.SuccinctMCSP.sampleFunction`: indicator function of the positive samples.
* `Cslib.SuccinctMCSP.enumSamples`, `Cslib.SuccinctMCSP.rawSamples`: canonical duplicate-free
  enumeration of an instance's samples.
* `Cslib.SuccinctMCSP.toRaw`: embedding of `SuccinctMCSP.Instance` into raw data.
* `Cslib.SuccinctMCSP.enc`, `Cslib.SuccinctMCSP.encBinary`: unary- and binary-threshold encodings.
* `Cslib.SuccinctMCSP.ofFunctionEncLength`: the exact bit length of
  `SuccinctMCSP.enc (SuccinctMCSP.Instance.ofFunction f S s)`.
* `Cslib.SuccinctMCSP.rawVerifier`, `Cslib.SuccinctMCSP.verifier`: the `NP` verifiers.

## Main results

* `Cslib.SuccinctMCSP.complexity_sampleFunction_le`: sparse synthesis bound in the number of
  samples.
* `Cslib.SuccinctMCSP.mem_iff_exists_circuit_le_sampleBudget`: `SuccinctMCSP` membership with gate
  count capped at `MCSP.sampleBudget`.
* `Cslib.SuccinctMCSP.rawSamples_ofFunction`, `Cslib.SuccinctMCSP.length_enc_ofFunction`: canonical
  sample enumeration and encoded length of `Instance.ofFunction`.
* `Cslib.SuccinctMCSP.mem_of_verifier_eq_true`, `Cslib.SuccinctMCSP.exists_verifier_append`:
  soundness and padded completeness of `SuccinctMCSP.verifier`.
* `Cslib.SuccinctMCSP.isVerifier`, `Cslib.SuccinctMCSP.isVerifier_encBinary`: verifier correctness.
* `Cslib.SuccinctMCSP.computableInPolyTime_rawVerifier`,
  `Cslib.SuccinctMCSP.computableInPolyTime_id_enc_encBinary`,
  `Cslib.SuccinctMCSP.computableInPolyTime_verifier`,
  `Cslib.SuccinctMCSP.computableInPolyTime_verifier_encBinary`: polynomial-time certificates for
  the verifiers and unary-to-binary threshold re-encoding.
* `Cslib.SuccinctMCSP.mem_NP`, `Cslib.SuccinctMCSP.mem_NP_encBinary`: `SuccinctMCSP ∈ NP`.

## References

* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness magnification near state-of-the-art lower
  bounds*][OliveiraPichSanthanam2019]
-/

@[expose] public section

namespace Cslib.SuccinctMCSP

open Circuits Circuits.Boolean Turing.MultiTapeTM Complexity

/-! ### Sample-set complexity bound and gate budget -/

/-- The Boolean function on `n` inputs that returns `true` on the positive samples in `samples` and
`false` elsewhere. -/
def sampleFunction {n : ℕ} (samples : Finset (BitString n × Bool)) : BooleanFunction n :=
  fun y => decide ((y, true) ∈ samples)

/-- Restricting the constant `true` function to the positive inputs in `samples` shows that
`sampleFunction samples` has circuit complexity at most `samples.card * (2 * n + 3) + 1`. -/
theorem complexity_sampleFunction_le {n : ℕ} (samples : Finset (BitString n × Bool)) :
    complexity interpretation (single (sampleFunction samples)) ≤
      samples.card * (2 * n + 3) + 1 := by
  classical
  let S : Finset (BitString n) := (samples.filter fun p => p.2 = true).image Prod.fst
  have heq : sampleFunction samples = fun y => decide (y ∈ S) && true := by
    funext y
    simp [S, sampleFunction]
  have hcard : S.card ≤ samples.card :=
    Finset.card_image_le.trans (Finset.card_filter_le _ _)
  rw [heq]
  exact (complexity_mask_le (fun _ => true) S).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hcard) 1)

/-- When `x` has no contradictory samples, `sampleFunction x.samples` agrees with every sample in
`x.samples`. -/
theorem sampleFunction_agrees {x : Instance}
    (hcons : ∀ y : BitString x.arity, ¬((y, true) ∈ x.samples ∧ (y, false) ∈ x.samples))
    {p : BitString x.arity × Bool} (hp : p ∈ x.samples) :
    sampleFunction x.samples p.1 = p.2 := by
  rcases p with ⟨y, _ | _⟩
  · simp only [sampleFunction, decide_eq_false_iff_not]
    exact fun htrue => hcons y ⟨htrue, hp⟩
  · simp [sampleFunction, hp]

/-- An instance is in `SuccinctMCSP` if and only if it is satisfied by a circuit of size at most
`MCSP.sampleBudget x.arity x.samples.card x.threshold`. -/
theorem mem_iff_exists_circuit_le_sampleBudget {x : Instance} :
    x ∈ SuccinctMCSP ↔
      ∃ c : Circuit signature x.arity 1,
        c.size ≤ MCSP.sampleBudget x.arity x.samples.card x.threshold ∧
        ∀ p ∈ x.samples, c.eval interpretation p.1 0 = p.2 := by
  constructor
  · intro hx
    rcases le_total x.threshold (x.samples.card * (2 * x.arity + 3) + 1) with hle | hle
    · obtain ⟨c, hc, hp⟩ := hx
      exact ⟨c, by rw [MCSP.sampleBudget, Nat.min_eq_left hle]; exact hc, hp⟩
    · have hcons : ∀ y : BitString x.arity, ¬((y, true) ∈ x.samples ∧ (y, false) ∈ x.samples) :=
        fun y ⟨ht, hf⟩ => notMem_of_mem_samples ht hf hx
      obtain ⟨c, hc, hsize⟩ := complexity_le_iff.mp (complexity_sampleFunction_le x.samples)
      refine ⟨c, by rw [MCSP.sampleBudget, Nat.min_eq_right hle]; exact hsize, fun p hp => ?_⟩
      rw [Circuit.computes_single_iff.mp hc p.1]
      exact sampleFunction_agrees hcons hp
  · rintro ⟨c, hc, hp⟩
    exact ⟨c, hc.trans (Nat.min_le_left _ _), hp⟩

/-! ### Canonical sample enumeration and instance encodings -/

/-- All possible input-output pairs on `n` variables, enumerated in the order of `BitString.enum n`
with output `false` before `true`. -/
def enumSamples (n : ℕ) : List (BitString n × Bool) :=
  (BitString.enum n).flatMap fun y => [(y, false), (y, true)]

@[simp] theorem mem_enumSamples (n : ℕ) (p : BitString n × Bool) : p ∈ enumSamples n := by
  rcases p with ⟨y, _ | _⟩ <;>
    exact List.mem_flatMap.mpr ⟨y, BitString.mem_enum n y, by simp⟩

@[simp] theorem length_enumSamples (n : ℕ) : (enumSamples n).length = 2 ^ n * 2 := by
  simp [enumSamples, List.length_flatMap]

theorem nodup_enumSamples (n : ℕ) : (enumSamples n).Nodup := by
  rw [List.nodup_iff_length_dedup_eq, ← List.card_toFinset]
  have hall : (enumSamples n).toFinset = Finset.univ := by
    ext p
    simp
  rw [hall]
  simp [BitString]

/-- The samples of an instance `x` listed canonically in the order of `enumSamples x.arity`, with
each input bitstring converted to `List Bool` via `List.ofFn`. -/
def rawSamples (x : Instance) : List (List Bool × Bool) :=
  ((enumSamples x.arity).filter (· ∈ x.samples)).map fun p => (List.ofFn p.1, p.2)

theorem mem_rawSamples_iff {x : Instance} {p : List Bool × Bool} :
    p ∈ rawSamples x ↔ ∃ y : BitString x.arity, (y, p.2) ∈ x.samples ∧ List.ofFn y = p.1 := by
  rcases p with ⟨w, b⟩
  simp only [rawSamples, List.mem_map, List.mem_filter, mem_enumSamples, true_and,
    decide_eq_true_eq, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨y, b', hmem, rfl, rfl⟩
    exact ⟨y, hmem, rfl⟩
  · rintro ⟨y, hmem, rfl⟩
    exact ⟨y, b, hmem, rfl, rfl⟩

@[simp] theorem ofFn_mem_rawSamples_iff (x : Instance) (y : BitString x.arity) (b : Bool) :
    (List.ofFn y, b) ∈ rawSamples x ↔ (y, b) ∈ x.samples := by
  rw [mem_rawSamples_iff]
  exact ⟨fun ⟨y', hmem, heq⟩ => by obtain rfl := List.ofFn_injective heq; exact hmem,
    fun hmem => ⟨y, hmem, rfl⟩⟩

@[simp] theorem length_rawSamples (x : Instance) : (rawSamples x).length = x.samples.card := by
  have hall : (enumSamples x.arity).toFinset.filter (· ∈ x.samples) = x.samples := by
    ext p
    simp
  have hcard := (nodup_enumSamples x.arity).card_eq_countP (P := (· ∈ x.samples))
  rw [hall] at hcard
  simpa [rawSamples, List.countP_eq_length_filter] using hcard.symm

/-- Embedding a `SuccinctMCSP.Instance` into raw data `((arity, rawSamples), threshold)`. -/
def toRaw : Instance ↪ (ℕ × List (List Bool × Bool)) × ℕ :=
  ⟨fun x => ((x.arity, rawSamples x), x.threshold), by
    rintro ⟨n, S, s⟩ ⟨n', S', s'⟩ h
    obtain ⟨h1, rfl⟩ := Prod.ext_iff.mp h
    obtain ⟨rfl, hraw⟩ := Prod.ext_iff.mp h1
    congr 1
    ext ⟨y, b⟩
    rw [← ofFn_mem_rawSamples_iff ⟨n, S, s⟩ y b, ← ofFn_mem_rawSamples_iff ⟨n, S', s⟩ y b]
    dsimp only at hraw ⊢
    rw [hraw]⟩

theorem toRaw_apply (x : Instance) : toRaw x = ((x.arity, rawSamples x), x.threshold) := rfl

/-- Instances of `SuccinctMCSP` encoded by the arity in unary, the framed list of samples, and the
threshold in unary. This is equivalent up to field order and list framing (`t` is implicit in
`encList`) to `⟨1^n, 1^s, 1^t, (x_1, b_1), …, (x_t, b_t)⟩` in
[OliveiraPichSanthanam2019, Section 4.1, proof of Theorem 1.4], and both encodings are computable
from each other in polynomial time. -/
def enc : Instance ↪ List Bool :=
  toRaw.trans (encPair (encPair encUnary (encList (encPair encBits encBool))) encUnary)

theorem enc_apply (x : Instance) :
    enc x =
      encPair (encPair encUnary (encList (encPair encBits encBool))) encUnary (toRaw x) :=
  rfl

/-- Instances of `SuccinctMCSP` encoded by the arity in unary, the framed list of samples, and the
threshold in binary. -/
def encBinary : Instance ↪ List Bool :=
  toRaw.trans (encPair (encPair encUnary (encList (encPair encBits encBool))) encNat)

theorem encBinary_apply (x : Instance) :
    encBinary x =
      encPair (encPair encUnary (encList (encPair encBits encBool))) encNat (toRaw x) :=
  rfl

private theorem filter_flatMap_ofFunction {n : ℕ} (f : BooleanFunction n)
    (S : Finset (BitString n)) (l : List (BitString n)) :
    (l.flatMap fun y => [(y, false), (y, true)]).filter
        (· ∈ S.image fun x => (x, f x)) =
      (l.filter (· ∈ S)).map fun y => (y, f y) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    rw [List.flatMap_cons, List.cons_append, List.cons_append, List.nil_append,
      List.filter_cons, List.filter_cons, List.filter_cons, ih]
    by_cases hy : y ∈ S <;> cases hfy : f y <;> simp [hy, hfy]

/-- For `Instance.ofFunction f S s`, the canonical sample enumeration `rawSamples` visits the
inputs of `S` in the order of `BitString.enum n`, paired with their values under `f`. -/
theorem rawSamples_ofFunction {n : ℕ} (f : BooleanFunction n)
    (S : Finset (BitString n)) (s : ℕ) :
    rawSamples (Instance.ofFunction f S s) =
      ((BitString.enum n).filter (· ∈ S)).map fun y => (List.ofFn y, f y) := by
  unfold rawSamples Instance.ofFunction enumSamples
  dsimp only
  rw [filter_flatMap_ofFunction, List.map_map]
  rfl

/-- The exact bit length of `SuccinctMCSP.enc (SuccinctMCSP.Instance.ofFunction f S s)` when
`S.card = q`: the framed unary arity `n`, the twice-framed list of `q` samples of length `n` + `1`,
and the unary threshold `s`. -/
def ofFunctionEncLength (n q s : ℕ) : ℕ :=
  4 * n + 3 + q * (8 * n + 10) + s

/-- `SuccinctMCSP.ofFunctionEncLength` is monotone in the number of samples `q`. -/
theorem ofFunctionEncLength_mono (n s : ℕ) :
    Monotone (fun q => ofFunctionEncLength n q s) := by
  intro q₁ q₂ hq
  simp only [ofFunctionEncLength]
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hq) _) _

private theorem length_encList_rawSamples_ofFunction {n : ℕ} (f : BooleanFunction n)
    (S : Finset (BitString n)) (s : ℕ) :
    (encList (encPair encBits encBool)
      (rawSamples (Instance.ofFunction f S s))).length = S.card * (4 * n + 5) := by
  have hlen : ((BitString.enum n).filter (· ∈ S)).length = S.card := by
    have h := length_rawSamples (Instance.ofFunction f S s)
    rwa [rawSamples_ofFunction, List.length_map, card_samples_ofFunction] at h
  rw [rawSamples_ofFunction, length_encList, List.map_map]
  have hconst : ((fun a => 2 * (encPair encBits encBool a).length + 1) ∘
      fun y : BitString n => (List.ofFn y, f y)) = fun _ => 4 * n + 5 := by
    funext y
    simp only [Function.comp_apply, length_encPair, encBits_apply, List.length_ofFn,
      encBool_apply, List.length_singleton]
    omega
  rw [hconst, List.map_const', List.sum_replicate, smul_eq_mul, hlen]

/-- The encoded length of `Instance.ofFunction f S s` under `SuccinctMCSP.enc` depends only on the
arity `n`, the sample count `S.card`, and the threshold `s`. -/
@[simp] theorem length_enc_ofFunction {n : ℕ} (f : BooleanFunction n)
    (S : Finset (BitString n)) (s : ℕ) :
    (enc (Instance.ofFunction f S s)).length = ofFunctionEncLength n S.card s := by
  rw [enc_apply, toRaw_apply, length_encPair, length_encPair,
    length_encList_rawSamples_ofFunction]
  simp only [Instance.ofFunction, encUnary_apply, List.length_replicate, ofFunctionEncLength]
  ring

private theorem card_samples_le_length_encList (x : Instance) :
    x.samples.card ≤ (encList (encPair encBits encBool) (rawSamples x)).length := by
  have h := SizedListEncoding.length_le (encA := encPair encBits encBool)
    (encL := encList (encPair encBits encBool)) (rawSamples x)
  simpa using h

private theorem arity_and_card_le_length_enc_of_encT (encT : ℕ ↪ List Bool) (x : Instance) :
    x.arity ≤
        (encPair (encPair encUnary (encList (encPair encBits encBool))) encT (toRaw x)).length ∧
      x.samples.card ≤
        (encPair (encPair encUnary (encList (encPair encBits encBool))) encT (toRaw x)).length := by
  have hcard := card_samples_le_length_encList x
  rw [toRaw_apply, length_encPair, length_encPair, encUnary_apply, List.length_replicate]
  dsimp only
  omega

/-! ### Verifier and correctness -/

/-- The verifier on raw data `(((n, samples), s), w)`: instantiates `MCSP.checkCertificateOn` on
the sample list `samples` at gate budget `MCSP.sampleBudget n samples.length s`. -/
def rawVerifier (r : ((ℕ × List (List Bool × Bool)) × ℕ) × List Bool) : Bool :=
  MCSP.checkCertificateOn r.1.1.2 Prod.fst (fun p out => out == p.2)
    r.1.1.1 (MCSP.sampleBudget r.1.1.1 r.1.1.2.length r.1.2) r.2

/-- The `NP` verifier for `SuccinctMCSP`. -/
def verifier (p : Instance × List Bool) : Bool :=
  rawVerifier (toRaw p.1, p.2)

theorem verifier_eq (x : Instance) (w : List Bool) :
    verifier (x, w) =
      MCSP.checkCertificateOn (rawSamples x) Prod.fst (fun p out => out == p.2)
        x.arity (MCSP.sampleBudget x.arity x.samples.card x.threshold) w := by
  change rawVerifier (((x.arity, rawSamples x), x.threshold), w) = _
  unfold rawVerifier
  dsimp only
  rw [length_rawSamples]

private theorem certLength_le_enc_of_encT (encT : ℕ ↪ List Bool) (x : Instance) :
    certLength x.arity (MCSP.sampleBudget x.arity x.samples.card x.threshold) ≤
      MCSP.certPolynomial.eval
        (encPair (encPair encUnary (encList (encPair encBits encBool))) encT (toRaw x)).length := by
  obtain ⟨hn, hcard⟩ := arity_and_card_le_length_enc_of_encT encT x
  exact MCSP.certLength_sampleBudget_le hn hcard

/-- **Soundness of the verifier.** An instance with an accepted certificate, of any length, is in
`SuccinctMCSP`. -/
theorem mem_of_verifier_eq_true {x : Instance} {w : List Bool} (hw : verifier (x, w) = true) :
    x ∈ SuccinctMCSP := by
  rw [verifier_eq] at hw
  obtain ⟨c, hcS, hall⟩ := MCSP.exists_circuit_of_checkCertificateOn hw
  refine ⟨c, hcS.trans (Nat.min_le_left _ _), fun p hp => ?_⟩
  simpa using hall (List.ofFn p.1, p.2)
    ((ofFn_mem_rawSamples_iff x p.1 p.2).mpr hp) p.1 rfl

/-- **Completeness of the verifier.** Every instance in `SuccinctMCSP` has a certificate of length
`certLength x.arity (MCSP.sampleBudget x.arity x.samples.card x.threshold)` that is accepted
whatever bits follow it. -/
theorem exists_verifier_append {x : Instance} (hx : x ∈ SuccinctMCSP) :
    ∃ u : List Bool,
      u.length = certLength x.arity (MCSP.sampleBudget x.arity x.samples.card x.threshold) ∧
      ∀ extra, verifier (x, u ++ extra) = true := by
  obtain ⟨C, hcS, hagree⟩ := mem_iff_exists_circuit_le_sampleBudget.mp hx
  simp only [verifier_eq]
  refine MCSP.exists_checkCertificateOn_append hcS fun p hp => ?_
  obtain ⟨y, hy, heq⟩ := mem_rawSamples_iff.mp hp
  exact ⟨y, heq.symm, by simp [hagree (y, p.2) hy]⟩

/-- `SuccinctMCSP.verifier` verifies `SuccinctMCSP` under `enc` (unary threshold). -/
theorem isVerifier : IsVerifier enc MCSP.certPolynomial verifier SuccinctMCSP := by
  refine IsVerifier.of_padding (fun x w _ hw => mem_of_verifier_eq_true hw) fun x hx => ?_
  obtain ⟨u, hu, hV⟩ := exists_verifier_append hx
  exact ⟨u, hu ▸ certLength_le_enc_of_encT encUnary x, fun k => hV _⟩

/-- `SuccinctMCSP.verifier` verifies `SuccinctMCSP` under `encBinary` (binary threshold). -/
theorem isVerifier_encBinary : IsVerifier encBinary MCSP.certPolynomial verifier SuccinctMCSP := by
  refine IsVerifier.of_padding (fun x w _ hw => mem_of_verifier_eq_true hw) fun x hx => ?_
  obtain ⟨u, hu, hV⟩ := exists_verifier_append hx
  exact ⟨u, hu ▸ certLength_le_enc_of_encT encNat x, fun k => hV _⟩

/-! ### Polynomial time -/

/-- The raw verifier for `SuccinctMCSP` is computable in polynomial time. -/
theorem computableInPolyTime_rawVerifier :
    ComputableInPolyTime rawVerifier
      (encPair
        (encPair (encPair encUnary (encList (encPair encBits encBool))) encNat)
        encBits)
      encBool := by
  let encSample := encPair encBits encBool
  let encSamples := encList encSample
  let encIn := encPair (encPair (encPair encUnary encSamples) encNat) encBits
  have hn : ComputableInPolyTime
      (fun r : ((ℕ × List (List Bool × Bool)) × ℕ) × List Bool => r.1.1.1)
      encIn encUnary :=
    (ComputableInPolyTime.fst _ _).fst'.fst'
  have hsamples : ComputableInPolyTime
      (fun r : ((ℕ × List (List Bool × Bool)) × ℕ) × List Bool => r.1.1.2)
      encIn encSamples :=
    (ComputableInPolyTime.fst _ _).fst'.snd'
  have hlen : ComputableInPolyTime
      (fun r : ((ℕ × List (List Bool × Bool)) × ℕ) × List Bool => r.1.1.2.length)
      encIn encUnary :=
    (ComputableInPolyTime.length_list encSample).comp hsamples
  have hs : ComputableInPolyTime
      (fun r : ((ℕ × List (List Bool × Bool)) × ℕ) × List Bool => r.1.2)
      encIn encNat :=
    (ComputableInPolyTime.fst _ _).snd'
  have hS : ComputableInPolyTime
      (fun r : ((ℕ × List (List Bool × Bool)) × ℕ) × List Bool =>
        MCSP.sampleBudget r.1.1.1 r.1.1.2.length r.1.2)
      encIn encUnary :=
    MCSP.computableInPolyTime_sampleBudget hn hlen hs
  have hw : ComputableInPolyTime
      (fun r : ((ℕ × List (List Bool × Bool)) × ℕ) × List Bool => r.2)
      encIn encBits :=
    ComputableInPolyTime.snd _ _
  have haccept : ComputableInPolyTime
      (fun q : ((((ℕ × List (List Bool × Bool)) × ℕ) × List Bool) × (List Bool × Bool)) × Bool =>
        q.2 == q.1.2.2)
      (encPair (encPair encIn encSample) encBool) encBool :=
    ComputableInPolyTime.beq (ComputableInPolyTime.snd _ _)
      (ComputableInPolyTime.fst _ _).snd'.snd'
  exact MCSP.computableInPolyTime_checkCertificateOn hn hS hw hsamples
    (ComputableInPolyTime.fst encBits encBool) haccept

/-- The `SuccinctMCSP` verifier is computable in polynomial time under `encBinary`. -/
theorem computableInPolyTime_verifier_encBinary :
    ComputableInPolyTime verifier (encPair encBinary encBits) encBool := by
  have hraw : ComputableInPolyTime
      (fun p : Instance × List Bool => (toRaw p.1, p.2))
      (encPair encBinary encBits)
      (encPair
        (encPair (encPair encUnary (encList (encPair encBits encBool))) encNat)
        encBits) :=
    .of_eq fun _ => rfl
  exact computableInPolyTime_rawVerifier.comp hraw

/-- Re-encoding a `SuccinctMCSP.Instance` from unary threshold encoding (`enc`) to binary threshold
encoding (`encBinary`) is computable in polynomial time. -/
theorem computableInPolyTime_id_enc_encBinary :
    ComputableInPolyTime id enc encBinary := by
  let encPairIn := encPair encUnary (encList (encPair encBits encBool))
  have hraw : ComputableInPolyTime toRaw enc (encPair encPairIn encUnary) :=
    .of_eq fun _ => rfl
  have hconv : ComputableInPolyTime
      (fun r : (ℕ × List (List Bool × Bool)) × ℕ => (r.1, r.2))
      (encPair encPairIn encUnary) (encPair encPairIn encNat) :=
    (ComputableInPolyTime.fst _ _).prod
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _))
  exact (hconv.comp hraw).of_enc_eq fun _ => rfl

/-- The `SuccinctMCSP` verifier is computable in polynomial time under `enc` (unary threshold). -/
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair enc encBits) encBool :=
  computableInPolyTime_verifier_encBinary.comp
    ((computableInPolyTime_id_enc_encBinary.comp (ComputableInPolyTime.fst enc encBits)).prod
      (ComputableInPolyTime.snd enc encBits))

/-- **`SuccinctMCSP` is in `NP`** under `SuccinctMCSP.enc` (unary arity, framed sample list, and
unary threshold) [OliveiraPichSanthanam2019, Section 4.1, proof of Theorem 1.4]. -/
theorem mem_NP : SuccinctMCSP ∈ NP enc :=
  ⟨MCSP.certPolynomial, verifier, computableInPolyTime_verifier, isVerifier⟩

/-- **`SuccinctMCSP` is in `NP`** under `SuccinctMCSP.encBinary` (unary arity, framed sample list,
and binary threshold). -/
theorem mem_NP_encBinary : SuccinctMCSP ∈ NP encBinary :=
  ⟨MCSP.certPolynomial, verifier, computableInPolyTime_verifier_encBinary, isVerifier_encBinary⟩

end Cslib.SuccinctMCSP
