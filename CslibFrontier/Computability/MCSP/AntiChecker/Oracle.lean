/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.AntiChecker.Threshold
public import CslibFrontier.Computability.MCSP.Succinct
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# The anti-checker oracle language

The greedy anti-checker (`Cslib.MCSP.AntiChecker.greedy`) asks the hash threshold oracle
(`Cslib.MCSP.AntiChecker.hashOracle`) about the circuits on `n` inputs with at most `s` gates,
described by their valid certificates (`Cslib.MCSP.validCertificates`). This module fixes one
language that answers all of these questions, for every `n`, `s`, power `ℓ` and threshold `u`.

A query (`Cslib.MCSP.AntiChecker.Query`) lists `n`, `s`, `ℓ` and `u`, followed by labelled
samples `(x, b)`, and is encoded with the four parameters in unary and each sample as its framed
input bits and its label (`Cslib.MCSP.AntiChecker.encQuery`). The yes-queries
(`Cslib.MCSP.AntiChecker.smallSet`) are those the hash oracle answers yes to: the `ℓ`-th Cartesian
power of the valid certificates consistent with the samples is not covered by `u + 1` affine hash
functions to `u` bits. The language `Cslib.MCSP.AntiChecker.antiCheckerOracle` consists of the
encodings of the yes-queries. On the queries of the greedy it is the hash oracle
(`Cslib.MCSP.AntiChecker.encQuery_ofSamples_mem_antiCheckerOracle_iff`), so an oracle agreeing with
it on those queries can drive the greedy
(`Cslib.MCSP.AntiChecker.isThresholdOracle_of_eq_true_iff`).

At power `1` and threshold `0` a query is a no-query exactly when some function computable with at
most `s` gates agrees with every sample
(`Cslib.MCSP.AntiChecker.encQuery_ofSamples_one_zero_notMem_antiCheckerOracle_iff`). So the same
fixed language also decides the complement of the list form of Succinct MCSP
(`Cslib.MCSP.AntiChecker.encQuery_ofSamples_one_zero_notMem_iff_mem_succinctMCSP`)
that [Oliveira, Pich and Santhanam, proof of Theorem 1.4][OliveiraPichSanthanam2019] query after
building an anti-checker. One fixed oracle for the generator and the final query is what an oracle
circuit in [Chen, Hirahara, Oliveira, Pich, Rajgopal and Santhanam, Definition 11]
[ChenHiraharaOliveiraPichRajgopalSanthanam2020] allows.

The parameters of a query are only `n`, `s`, `ℓ` and `u`, in unary, and its length is linear in
them and in the total length of the samples (`Cslib.MCSP.AntiChecker.length_encQuery`). For the
`t` samples of a greedy run on `n` inputs, it is `2 (n + s + ℓ + u) + 4 + t (4 n + 5)`
(`Cslib.MCSP.AntiChecker.length_encQuery_ofSamples`). Membership of the language in `P/poly` under
`NP ⊆ P/poly` is in `CslibFrontier.Computability.MCSP.AntiChecker.Oracle.PolyTime`.

This is the oracle of the library's deterministic greedy, not the approximate-counting oracle of
[Oliveira, Pich and Santhanam, Lemma 4.1][OliveiraPichSanthanam2019].

## Main definitions

* `Cslib.MCSP.AntiChecker.Query`, `Cslib.MCSP.AntiChecker.Query.ofSamples`: queries, and the
  query of labelled samples of a function on `n` inputs.
* `Cslib.MCSP.AntiChecker.encQuery`: unary parameters, then the framed samples.
* `Cslib.MCSP.AntiChecker.smallSet`: the queries the hash oracle answers yes to.
* `Cslib.MCSP.AntiChecker.antiCheckerOracle`: the encodings of the yes-queries.

## Main results

* `Cslib.MCSP.AntiChecker.length_encQuery`, `Cslib.MCSP.AntiChecker.length_encQuery_ofSamples`:
  the exact query length.
* `Cslib.MCSP.AntiChecker.encQuery_mem_antiCheckerOracle`: the language decides the yes-queries.
* `Cslib.MCSP.AntiChecker.encQuery_ofSamples_mem_antiCheckerOracle_iff`,
  `Cslib.MCSP.AntiChecker.isThresholdOracle_of_eq_true_iff`: on the greedy's queries it is the hash
  oracle, so any oracle agreeing with it there is a threshold oracle.
* `Cslib.MCSP.AntiChecker.encQuery_ofSamples_one_zero_notMem_antiCheckerOracle_iff`,
  `Cslib.MCSP.AntiChecker.encQuery_ofSamples_one_zero_notMem_iff_mem_succinctMCSP`:
  at power `1` and threshold `0`, a no-query is a yes-instance of Succinct MCSP.

## References

* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness magnification near state-of-the-art lower
  bounds*][OliveiraPichSanthanam2019]
* [L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal, R. Santhanam, *Beyond natural
  proofs: hardness magnification and locality*][ChenHiraharaOliveiraPichRajgopalSanthanam2020]
-/

public section

namespace Cslib.MCSP.AntiChecker

open Finset Circuits Circuits.Boolean Turing.MultiTapeTM

/-- A query to the anti-checker oracle: is the `power`-th Cartesian power of the descriptions of
circuits on `arity` inputs with at most `size` gates that agree with `samples` small at
`threshold`? -/
structure Query where
  /-- The number `n` of inputs of the circuits. -/
  arity : ℕ
  /-- The number `s` of gates allowed. -/
  size : ℕ
  /-- The power `ℓ` of the set of consistent descriptions. -/
  power : ℕ
  /-- The threshold `u` of the hash oracle. -/
  threshold : ℕ
  /-- The labelled samples: the bits of an input and the value required there. -/
  samples : List (List Bool × Bool)

/-- **Unary parameters**, then the samples: a query is encoded as its arity, gate bound, power and
threshold in unary, followed by the framed list of its samples, each the framed bits of its input
followed by its label. -/
enc_structure encQuery : Query where
  arity : encUnary, size : encUnary, power : encUnary, threshold : encUnary,
  samples : (encList (encPair encBits encBool))

/-- The query with unary parameters `n`, `s`, `ℓ`, `u` and the labelled samples `P` of a function
on `n` inputs. -/
@[expose] def Query.ofSamples (n s ℓ u : ℕ) (P : List (BitString n × Bool)) : Query :=
  ⟨n, s, ℓ, u, P.map fun p => (List.ofFn p.1, p.2)⟩

/-- **The length of a query**: twice its unary parameters, plus four bits of framing, plus
`4 |x| + 5` bits for each sample `(x, b)`. -/
theorem length_encQuery (q : Query) :
    (encQuery q).length = 2 * (q.arity + q.size + q.power + q.threshold) + 4 +
      (q.samples.map fun p => 4 * p.1.length + 5).sum := by
  have h (p : List Bool × Bool) :
      2 * (2 * (encBits p.1).length + 1 + (encBool p.2).length) + 1 = 4 * p.1.length + 5 := by
    simp only [encBits_apply, encBool_apply, List.length_singleton]
    ring
  simp only [encQuery_apply, encQueryFields, length_encPair, encUnary_apply,
    List.length_replicate, length_encList, h]
  ring

/-- **The length of a greedy query**: `2 (n + s + ℓ + u) + 4 + t (4 n + 5)` for `t` samples of a
function on `n` inputs. With `s` in unary this is polynomial in `s`, `ℓ`, `u` and `t`. -/
theorem length_encQuery_ofSamples (n s ℓ u : ℕ) (P : List (BitString n × Bool)) :
    (encQuery (Query.ofSamples n s ℓ u P)).length =
      2 * (n + s + ℓ + u) + 4 + P.length * (4 * n + 5) := by
  rw [length_encQuery]
  simp [Query.ofSamples, Function.comp_def, List.sum_replicate]

/-- The queries the hash oracle answers yes to: the `power`-th Cartesian power of the valid
certificates for `arity` inputs and `size` gates that agree with the samples is not large at
`threshold`. -/
def smallSet : Set Query :=
  {q | hashOracle (validCertificates q.arity q.size)
    (fun w x => evalCertificate q.arity q.size (List.ofFn w) x) q.power q.samples
      q.threshold = true}

theorem mem_smallSet {q : Query} :
    q ∈ smallSet ↔ hashOracle (validCertificates q.arity q.size)
      (fun w x => evalCertificate q.arity q.size (List.ofFn w) x) q.power q.samples
        q.threshold = true :=
  Iff.rfl

/-- **The anti-checker oracle**: the encodings of the queries the hash oracle answers yes to. -/
def antiCheckerOracle : Language Bool :=
  {w | ∃ q ∈ smallSet, encQuery q = w}

/-- The anti-checker oracle decides the yes-queries. -/
theorem encQuery_mem_antiCheckerOracle {q : Query} :
    encQuery q ∈ antiCheckerOracle ↔ q ∈ smallSet :=
  ⟨fun ⟨_, hq', h⟩ => encQuery.injective h ▸ hq', fun hq => ⟨q, hq, rfl⟩⟩

/-- Evaluating a certificate on the bits of a sample input agrees with `certificateFunction`. -/
private theorem consistent_map_ofFn {n s : ℕ} (P : List (BitString n × Bool)) :
    consistent (validCertificates n s)
        (fun w x => evalCertificate n s (List.ofFn w) x) (P.map fun p => (List.ofFn p.1, p.2)) =
      consistent (validCertificates n s) (certificateFunction n s) P := by
  ext w
  rw [mem_consistent, mem_consistent, List.forall_mem_map]
  exact Iff.rfl

/-- **On the greedy's queries the anti-checker oracle is the hash oracle** for the valid
certificates. -/
theorem encQuery_ofSamples_mem_antiCheckerOracle_iff {n s ℓ u : ℕ}
    {P : List (BitString n × Bool)} :
    encQuery (Query.ofSamples n s ℓ u P) ∈ antiCheckerOracle ↔
      hashOracle (validCertificates n s) (certificateFunction n s) ℓ P u = true := by
  rw [encQuery_mem_antiCheckerOracle, mem_smallSet, hashOracle_eq_true, hashOracle_eq_true]
  simp only [Query.ofSamples]
  rw [consistent_map_ofFn]

/-- **An oracle agreeing with the anti-checker oracle on the greedy's queries is a threshold
oracle** for the valid certificates, at every power `ℓ > 0`. -/
theorem isThresholdOracle_of_eq_true_iff {n s ℓ : ℕ} (hℓ : 0 < ℓ)
    {O : List (BitString n × Bool) → ℕ → Bool}
    (hO : ∀ P u, O P u = true ↔ encQuery (Query.ofSamples n s ℓ u P) ∈ antiCheckerOracle) :
    IsThresholdOracle (validCertificates n s) (certificateFunction n s) ℓ O := by
  have h : O = hashOracle (validCertificates n s) (certificateFunction n s) ℓ := by
    funext P u
    exact Bool.eq_iff_iff.2 ((hO P u).trans encQuery_ofSamples_mem_antiCheckerOracle_iff)
  exact h ▸ isThresholdOracle_hashOracle _ _ hℓ

/-- **At power `1` and threshold `0`, a no-query is a yes-instance of Succinct MCSP**: the query
of samples `P` is not in the anti-checker oracle exactly when some function computable with at
most `s` gates agrees with every sample. -/
theorem encQuery_ofSamples_one_zero_notMem_antiCheckerOracle_iff {n s : ℕ}
    {P : List (BitString n × Bool)} :
    encQuery (Query.ofSamples n s 1 0 P) ∉ antiCheckerOracle ↔
      ∃ g ∈ computableFunctions n s, ∀ p ∈ P, g p.1 = p.2 := by
  rw [encQuery_ofSamples_mem_antiCheckerOracle_iff, hashOracle_eq_true, not_not,
    isLarge_zero_iff, nonempty_iff_ne_empty, Ne,
    BitString.blockPower_eq_empty_iff one_ne_zero, ← Ne, ← nonempty_iff_ne_empty]
  constructor
  · rintro ⟨w, hw⟩
    rw [mem_consistent] at hw
    exact ⟨_, certificateFunction_mem_computableFunctions hw.1, hw.2⟩
  · rintro ⟨g, hg, hP⟩
    rw [← mem_coe, ← image_validCertificates] at hg
    obtain ⟨w, hw, rfl⟩ := hg
    exact ⟨w, mem_consistent.2 ⟨mem_coe.1 hw, hP⟩⟩

/-- At power `1` and threshold `0`, the anti-checker oracle decides the complement of Succinct MCSP
on the samples `P`, read as a set. -/
theorem encQuery_ofSamples_one_zero_notMem_iff_mem_succinctMCSP {n s : ℕ}
    {P : List (BitString n × Bool)} :
    encQuery (Query.ofSamples n s 1 0 P) ∉ antiCheckerOracle ↔
      (⟨n, P.toFinset, s⟩ : SuccinctMCSP.Instance) ∈ SuccinctMCSP := by
  rw [encQuery_ofSamples_one_zero_notMem_antiCheckerOracle_iff,
    SuccinctMCSP.mem_iff_exists_mem_computableFunctions]
  simp only [List.mem_toFinset]

end Cslib.MCSP.AntiChecker
