/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Fagin.Layout
public import Complexity.Computability.Complexity.Fagin.StrictVerifier
public import Complexity.Computability.Complexity.Fagin.Tableau
public import Complexity.Computability.Complexity.Fagin.Verifier
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# NP classes are existential second-order definable (Fagin's theorem)

The converse direction of Fagin's theorem [Fagin, Theorem 6][Fagin1974],
[Immerman, Theorem 7.8][Immerman1999], [Papadimitriou, Theorem 8.3][Papadimitriou94]: for an
isomorphism-closed class `K` of finite relational structures over a language `L` with a finite
vocabulary `v : Vocabulary L`, if `v.queryLanguage K ∈ NP encStructure`, then `K` is existential
second-order definable (`Cslib.Logic.ESO.Definable.of_queryLanguage_mem_NP`). Combined with
`Cslib.Logic.ESO.Definable.queryLanguage_mem_NP` from
`Complexity/Computability/Complexity/Fagin/Verifier.lean`, this gives Fagin's
characterization `Cslib.Logic.ESO.definable_iff_queryLanguage_mem_NP`
(`Cslib.Logic.ESO.Definable K ↔ v.queryLanguage K ∈ NP encStructure`).

Given an `NP` verifier `V` with certificate-length polynomial `p`, we wrap `V` in
`Cslib.Complexity.strictVerifier encStructure p V` so that any accepting run has a certificate of
length `p |encStructure a|`. Let `tm` be a deterministic multi-tape Turing machine computing
`strictVerifier encStructure p V` within time `c * (|input| + 1) ^ d`.

We choose an exponent `k ≥ 1` bounding all relation arities of `v` such that on every well-formed
input `a` of cardinality `n = a.1 ≥ 2`, the power-domain size `B = n ^ k` exceeds both the framed
input plus certificate length and `tm`'s time bound (`Cslib.Logic.Vocabulary.exists_pow_bound`).
On `Fin B` equipped with `v.powerStructure a B`, we conjoin `v.layoutESOSentence` and
`v.tableauESOSentence tm` and existentially project the intermediate input-tape relations
(`uLenSym`, `uBitSym`) via `Cslib.Logic.ESO.Sentence.project` to obtain
`v.npPowerSentence tm : ESO.Sentence v.powerLanguage`. Pulling this sentence back to `(M, <)` along
the first-order interpretation `v.powerInterpretation k har` and existentially quantifying the
linear order `<` via `Cslib.Logic.ESO.Definable.of_powerLanguage` (which handles cardinalities
`0` and `1` by finite truth-table disjunction in
`Complexity/Computability/Complexity/Fagin/Small.lean`) yields the defining ESO
sentence over `L`.

## Main definitions

* `Cslib.Logic.Vocabulary.maxArity`: one more than the largest relation arity of `v`, a positive
  strict upper bound on all relation arities.
* `Cslib.Logic.Vocabulary.npPowerSentence`: the existential second-order sentence over
  `v.powerLanguage` combining input-tape layout synthesis and the accepting tableau of `tm`.

## Main results

* `Cslib.Logic.Vocabulary.length_encStructure_le_pow`: the encoded length of a well-formed input of
  cardinality `n ≥ 1` is at most `(v.count + 1) * (2 * n ^ v.maxArity + 1)`.
* `Cslib.Logic.Vocabulary.exists_pow_bound`: existence of a tuple width `k ≥ 1` such that `n ^ k`
  bounds both the verifier's input-plus-certificate length and its running time for all well-formed
  inputs of cardinality `n ≥ 2`.
* `Cslib.Logic.Vocabulary.exists_powerSentence_of_mem_NP`: an NP language has an ESO
  definition on sufficiently large canonical power structures, without assuming invariance
  under renumbering.
* `Cslib.Logic.Vocabulary.realize_npPowerSentence`: on `Fin B`, `v.npPowerSentence tm` holds
  iff `CookLevin.tableau tm (frame (encStructure a)) L (B - 1)` is satisfiable for some certificate
  length `L` with `|frame (encStructure a)| + L + 1 < B`.
* `Cslib.Logic.ESO.Definable.of_queryLanguage_mem_NP`: every isomorphism-closed class `K` whose
  query language is in `NP` is existential second-order definable.
* `Cslib.Logic.ESO.definable_iff_queryLanguage_mem_NP`,
  `Cslib.Logic.ESO.definable_iff_isoClosed_and_queryLanguage_mem_NP`: **Fagin's theorem**
  (`Definable K ↔ v.queryLanguage K ∈ NP encStructure` for isomorphism-closed `K`, and
  `Definable K ↔ IsoClosed K ∧ v.queryLanguage K ∈ NP encStructure` in general).

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94], Theorem 8.3
-/

@[expose] public section

universe u v

namespace Cslib.Logic

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure CategoryTheory
open Turing Turing.MultiTapeTM
open Cslib.Complexity

namespace Vocabulary

variable {L : Language.{u, v}} (v : Vocabulary L)

/-! ### Polynomial bounds on encoded structure length and tableau size -/

/-- One more than the largest relation arity of `v`: a positive strict upper bound on all relation
arities of `v`. -/
def maxArity : ℕ :=
  Finset.univ.sup v.arity + 1

private theorem one_le_maxArity : 1 ≤ v.maxArity :=
  Nat.le_add_left 1 _

private theorem arity_le_maxArity (i : Fin v.count) : v.arity i ≤ v.maxArity :=
  (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_add_right _ 1)

/-- For a well-formed input `a` with `1 ≤ a.1`, the `m`-th prefix of `encStructure a` has length at
most `(m + 1) * (2 * a.1 ^ v.maxArity + 1)`. -/
private theorem length_encStructurePrefix_le_pow {a : EncodedStructure} (ha : v.WellFormed a)
    (ha1 : 1 ≤ a.1) (m : ℕ) (hm : m ≤ v.count) :
    (v.encStructurePrefix a m).length ≤ (m + 1) * (2 * a.1 ^ v.maxArity + 1) := by
  induction m with
  | zero =>
    rw [v.encStructurePrefix_zero, Nat.zero_add, Nat.one_mul, length_frame, encUnary_apply,
      List.length_replicate]
    have hpow : a.1 ≤ a.1 ^ v.maxArity := by
      simpa using Nat.pow_le_pow_right ha1 v.one_le_maxArity
    omega
  | succ m ih =>
    have hi : m < v.count := by omega
    let idx : Fin v.count := ⟨m, hi⟩
    have h1 := ih (by omega)
    have h2 : (v.table a (v.symbol idx)).length = a.1 ^ v.arity idx :=
      Vocabulary.WellFormed.length_table v ha (v.symbol idx)
    have h3 : a.1 ^ v.arity idx ≤ a.1 ^ v.maxArity :=
      Nat.pow_le_pow_right ha1 (v.arity_le_maxArity idx)
    have hsucc := congrArg List.length (v.encStructurePrefix_succ a idx)
    rw [List.length_append, length_frame, h2] at hsucc
    change (v.encStructurePrefix a (m + 1)).length =
      (v.encStructurePrefix a m).length + (2 * a.1 ^ v.arity idx + 1) at hsucc
    rw [hsucc, Nat.add_mul, Nat.one_mul]
    omega

/-- For a well-formed input `a` with `1 ≤ a.1`, `(encStructure a).length` is bounded by
`(v.count + 1) * (2 * a.1 ^ v.maxArity + 1)`. -/
theorem length_encStructure_le_pow {a : EncodedStructure} (ha : v.WellFormed a) (ha1 : 1 ≤ a.1) :
    (encStructure a).length ≤ (v.count + 1) * (2 * a.1 ^ v.maxArity + 1) := by
  rw [← v.encStructurePrefix_count ha]
  exact v.length_encStructurePrefix_le_pow ha ha1 v.count (le_refl _)

/-- Given a certificate-length polynomial `p` and time-bound parameters `c, d`, there exists an
exponent `k ≥ 1` bounding all relation arities of `v` such that on every well-formed input `a` of
cardinality `a.1 ≥ 2`, the power-domain size `a.1 ^ k` bounds both the total verifier input length
plus `2` and the verifier time bound plus `1`. -/
theorem exists_pow_bound (p : Polynomial ℕ) (c d : ℕ) :
    ∃ k : ℕ, 1 ≤ k ∧ (∀ i : Fin v.count, v.arity i ≤ k) ∧
      ∀ a : EncodedStructure, v.WellFormed a → 2 ≤ a.1 →
        (frame (encStructure a)).length + p.eval (encStructure a).length + 2 ≤ a.1 ^ k ∧
        c * ((frame (encStructure a)).length + p.eval (encStructure a).length + 1) ^ d + 1 ≤
          a.1 ^ k := by
  obtain ⟨cp, dp, hp⟩ := Cslib.polynomiallyBounded_iff_le.mp
    (ComputableTidilyInPolyTime.polynomiallyBounded (ComputableTidilyInPolyTime.unary_eval p))
  let g : ℕ → ℕ := fun n => (v.count + 1) * (2 * n ^ v.maxArity + 1)
  let F : ℕ → ℕ := fun n =>
    (c + 1) * (2 * g n + 1 + cp * (g n + 1) ^ dp + 1) ^ (d + 1) + 1
  have hF_poly : Cslib.PolynomiallyBounded F := by
    dsimp [F, g]
    fun_prop
  obtain ⟨C, D, hF⟩ := Cslib.polynomiallyBounded_iff_le.mp hF_poly
  let k := max v.maxArity (C + 2 * D)
  refine ⟨k, v.one_le_maxArity.trans (le_max_left _ _),
    fun i => (v.arity_le_maxArity i).trans (le_max_left _ _), fun a ha h2 => ?_⟩
  have h_n1 : a.1 + 1 ≤ a.1 ^ 2 := by nlinarith
  have h_powD : (a.1 + 1) ^ D ≤ a.1 ^ (2 * D) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left h_n1 D
  have h_C : C ≤ a.1 ^ C :=
    C.lt_two_pow_self.le.trans (Nat.pow_le_pow_left h2 C)
  have hF_le : F a.1 ≤ a.1 ^ k := calc
    F a.1 ≤ C * (a.1 + 1) ^ D := hF a.1
    _ ≤ a.1 ^ C * a.1 ^ (2 * D) := Nat.mul_le_mul h_C h_powD
    _ = a.1 ^ (C + 2 * D) := (pow_add a.1 C (2 * D)).symm
    _ ≤ a.1 ^ k := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have hlen : (encStructure a).length ≤ g a.1 :=
    v.length_encStructure_le_pow ha (by omega)
  have hp_le : p.eval (encStructure a).length ≤ cp * (g a.1 + 1) ^ dp :=
    (hp _).trans (Nat.mul_le_mul_left cp (Nat.pow_le_pow_left (by omega) dp))
  let N := (frame (encStructure a)).length + p.eval (encStructure a).length + 1
  let M := 2 * g a.1 + 1 + cp * (g a.1 + 1) ^ dp + 1
  have hNM : N ≤ M := by
    change (frame (encStructure a)).length + p.eval (encStructure a).length + 1 ≤
      2 * g a.1 + 1 + cp * (g a.1 + 1) ^ dp + 1
    rw [length_frame]
    omega
  have hN1 : N ≤ N ^ (d + 1) := Nat.le_self_pow (by omega) N
  have hNd : N ^ d ≤ N ^ (d + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ d)
  have hMd : N ^ (d + 1) ≤ M ^ (d + 1) := Nat.pow_le_pow_left hNM (d + 1)
  constructor
  · calc (frame (encStructure a)).length + p.eval (encStructure a).length + 2
        = 1 * N + 1 := by
          change _ = 1 * ((frame (encStructure a)).length + p.eval (encStructure a).length + 1) + 1
          omega
      _ ≤ (c + 1) * M ^ (d + 1) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul (by omega) (hN1.trans hMd)) 1
      _ ≤ a.1 ^ k := hF_le
  · calc c * ((frame (encStructure a)).length + p.eval (encStructure a).length + 1) ^ d + 1
        = c * N ^ d + 1 := rfl
      _ ≤ (c + 1) * M ^ (d + 1) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul (by omega) (hNd.trans hMd)) 1
      _ ≤ a.1 ^ k := hF_le

/-! ### Combined ESO sentence on the power structure -/

variable {m : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM m Bool State)

/-- The existential second-order sentence over `v.powerLanguage` that existentially guesses the
framed input-tape relations (`uLenSym` and `uBitSym`), checks that they represent
`frame (encStructure a)` via `v.layoutESOSentence`, and asserts via `v.tableauESOSentence tm` that
`tm` accepts `frame (encStructure a) ++ w` for some certificate `w`. -/
noncomputable def npPowerSentence : ESO.Sentence v.powerLanguage :=
  (v.layoutESOSentence ⊓ v.tableauESOSentence tm).project

/-- **Correctness of `v.npPowerSentence` on `Fin B`.** On `(Fin B, v.powerStructure a B)` for a
well-formed input `a` with `(frame (encStructure a)).length + 1 < B`, `(v.npPowerSentence tm)`
holds if and only if `CookLevin.tableau tm (frame (encStructure a)) L (B - 1)` is satisfiable for
some certificate length `L` with `(frame (encStructure a)).length + L + 1 < B`. -/
theorem realize_npPowerSentence {a : EncodedStructure} (ha : v.WellFormed a) {B : ℕ}
    (hB : (frame (encStructure a)).length + 1 < B) :
    (letI := v.powerStructure a B;
      (v.npPowerSentence tm).Realize (Fin B)) ↔
      ∃ L : ℕ, (frame (encStructure a)).length + L + 1 < B ∧
        (CookLevin.tableau tm (frame (encStructure a)) L (B - 1)).Satisfiable := by
  let _ := v.powerStructure a B
  rw [npPowerSentence, ESO.Sentence.realize_project]
  constructor
  · rintro ⟨I_in, h⟩
    let _ := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in
    obtain ⟨hlay, htab⟩ := (ESO.Sentence.realize_inf (M := Fin B)).1 h
    obtain ⟨huLen, huBit⟩ := (v.realize_layoutESOSentence ha (by omega) I_in).1 hlay
    exact (v.realize_tableauESOSentence tm a B I_in hB huLen huBit).1 htab
  · intro hsat
    let I_in : ∀ b : Bool, Set (Fin ((fun _ : Bool => 1) b) → Fin B) := fun b =>
      if b then {x | (x 0 : ℕ) = (frame (encStructure a)).length}
      else {x | (frame (encStructure a))[(x 0 : ℕ)]? = some true}
    let _ := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in
    have huLen : ∀ z : Fin B, ![z] ∈ I_in true ↔ (z : ℕ) = (frame (encStructure a)).length :=
      fun _ => Iff.rfl
    have huBit : ∀ p : Fin B, (p : ℕ) < (frame (encStructure a)).length →
        (![p] ∈ I_in false ↔ (frame (encStructure a))[(p : ℕ)]? = some true) :=
      fun _ _ => Iff.rfl
    have hlay := (v.realize_layoutESOSentence ha (by omega) I_in).2 ⟨huLen, huBit⟩
    have htab := (v.realize_tableauESOSentence tm a B I_in hB huLen huBit).2 hsat
    exact ⟨I_in, (ESO.Sentence.realize_inf (M := Fin B)).2 ⟨hlay, htab⟩⟩

/-- An NP language of encoded structures has a single ESO definition on canonical power
structures of sufficiently large fixed dimension. Only well-formed inputs of size at least two
are considered; no invariance under renumbering is assumed. -/
theorem exists_powerSentence_of_mem_NP {K : Set EncodedStructure} (hNP : K ∈ NP encStructure) :
    ∃ k : ℕ, 1 ≤ k ∧ (∀ i : Fin v.count, v.arity i ≤ k) ∧
      ∃ Ψ : ESO.Sentence v.powerLanguage, ∀ a : EncodedStructure,
        v.WellFormed a → 2 ≤ a.1 →
        (a ∈ K ↔ letI := v.powerStructure a (a.1 ^ k); Ψ.Realize (Fin (a.1 ^ k))) := by
  rcases hNP with ⟨p, V, hVpoly, hV⟩
  obtain ⟨t, s, ht, -, m, State, hfin, tm, htm⟩ :=
    (computableInPolyTime_strictVerifier encStructure p hVpoly).tidy
  obtain ⟨c, d, ht⟩ := ht.exists_le
  let _ := Fintype.ofFinite State
  classical
  obtain ⟨k, hk, har, hpow⟩ := v.exists_pow_bound p c d
  refine ⟨k, hk, har, v.npPowerSentence tm, fun a ha h2 => ?_⟩
  obtain ⟨hB1, hB2⟩ := hpow a ha h2
  rw [v.realize_npPowerSentence tm ha (by omega)]
  have hsat := CookLevin.exists_tableau_satisfiable_iff_of_strictVerifier hV htm
    (a := a) (M := a.1 ^ k - 2 - (frame (encStructure a)).length) (T := a.1 ^ k - 1)
    (by omega) fun w hw => ?_
  · rw [← hsat]
    refine exists_congr fun L => and_congr_left fun _ => ?_
    omega
  · have htw := ht (a, w)
    have hlen_pair : (encPair encStructure encBits (a, w)).length =
        (frame (encStructure a)).length + p.eval (encStructure a).length := by
      rw [encPair_apply, List.length_append, encBits_apply, hw]
    rw [hlen_pair] at htw
    omega

end Vocabulary

namespace ESO

/-- **NP classes of finite structures are existential second-order definable** (the converse
direction of Fagin's theorem): for an isomorphism-closed class `K` of finite relational structures
over a language `L` with a finite vocabulary `v`, if `v.queryLanguage K ∈ NP encStructure`, then
`K` is existential second-order definable [Fagin, Theorem 6][Fagin1974],
[Immerman, Theorem 7.8][Immerman1999], [Papadimitriou, Theorem 8.3][Papadimitriou94]. -/
theorem Definable.of_queryLanguage_mem_NP {L : Language.{u, v}} [L.IsRelational]
    (v : Vocabulary L) {K : Set (Bundled.{0} L.Structure)} (hK : IsoClosed K)
    (hNP : v.queryLanguage K ∈ NP encStructure) :
    Definable K := by
  obtain ⟨k, hk, har, Ψ, hΨ⟩ := v.exists_powerSentence_of_mem_NP hNP
  exact Definable.of_powerLanguage v hK k hk har Ψ hΨ

/-- **Fagin's theorem**: an isomorphism-closed class `K` of finite relational structures over a
language `L` with a finite vocabulary `v` is existential second-order definable if and only if its
query language `v.queryLanguage K` belongs to `NP encStructure` [Fagin, Theorem 6][Fagin1974],
[Immerman, Theorem 7.8][Immerman1999], [Papadimitriou, Theorem 8.3][Papadimitriou94]. -/
theorem definable_iff_queryLanguage_mem_NP {L : Language.{u, v}} [L.IsRelational]
    (v : Vocabulary L) {K : Set (Bundled.{0} L.Structure)} (hK : IsoClosed K) :
    Definable K ↔ v.queryLanguage K ∈ NP encStructure :=
  ⟨Definable.queryLanguage_mem_NP v, Definable.of_queryLanguage_mem_NP v hK⟩

/-- **Fagin's theorem** (hypothesis-free form): a class `K` of finite relational structures over a
language `L` with a finite vocabulary `v` is existential second-order definable if and only if `K`
is closed under isomorphism and its query language `v.queryLanguage K` belongs to
`NP encStructure` [Fagin, Theorem 6][Fagin1974], [Immerman, Theorem 7.8][Immerman1999]. -/
theorem definable_iff_isoClosed_and_queryLanguage_mem_NP {L : Language.{u, v}} [L.IsRelational]
    (v : Vocabulary L) {K : Set (Bundled.{0} L.Structure)} :
    Definable K ↔ IsoClosed K ∧ v.queryLanguage K ∈ NP encStructure :=
  ⟨fun h => ⟨h.isoClosed, h.queryLanguage_mem_NP v⟩,
    fun ⟨hK, hNP⟩ => Definable.of_queryLanguage_mem_NP v hK hNP⟩

end ESO

/-- **Fagin's theorem** (`Vocabulary` dot-notation alias of
`Cslib.Logic.ESO.definable_iff_queryLanguage_mem_NP`). -/
alias Vocabulary.definable_iff_queryLanguage_mem_NP := ESO.definable_iff_queryLanguage_mem_NP

end Cslib.Logic
