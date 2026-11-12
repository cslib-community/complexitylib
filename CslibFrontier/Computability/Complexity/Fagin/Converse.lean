/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Fagin.Layout
public import CslibFrontier.Computability.Complexity.Classes.NP.StrictVerifier
public import CslibFrontier.Computability.Complexity.Fagin.Tableau
public import CslibFrontier.Computability.Complexity.Fagin.Verifier
public import CslibFrontier.Computability.Complexity.Fagin.Power
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Basic
import CslibFrontier.Logics.FirstOrder.Encoding.PowerBound

/-!
# NP classes are existential second-order definable (Fagin's theorem)

The converse direction of Fagin's theorem [Fagin, Theorem 6][Fagin1974],
[Immerman, Theorem 7.8][Immerman1999], [Papadimitriou, Theorem 8.3][Papadimitriou94]: for an
isomorphism-closed class `K` of finite relational structures over a language `L` with a finite
vocabulary `v : Vocabulary L`, if `v.queryLanguage K ∈ NP encStructure`, then `K` is existential
second-order definable (`Cslib.Logic.ESO.Definable.of_queryLanguage_mem_NP`). Combined with
`Cslib.Logic.ESO.Definable.queryLanguage_mem_NP` from
`CslibFrontier/Computability/Complexity/Fagin/Verifier.lean`, this gives Fagin's
characterization `Cslib.Logic.ESO.definable_iff_queryLanguage_mem_NP`
(`Cslib.Logic.ESO.Definable K ↔ v.queryLanguage K ∈ NP encStructure`).

Given an `NP` verifier `V` with certificate-length polynomial `p`, we wrap `V` in
`Cslib.Complexity.strictVerifier encStructure p V` so that any accepting run has a certificate of
length `p |encStructure a|`. Let `tm` be a deterministic multi-tape Turing machine computing
`strictVerifier encStructure p V` within a polynomial time bound `t₀`.

We choose an exponent `k ≥ 1` bounding all relation arities of `v` such that on every well-formed
input `a` of cardinality `n = a.1 ≥ 2`, the power-domain size `B = n ^ k` exceeds both the framed
input plus certificate length and `tm`'s time bound (`Cslib.Logic.Vocabulary.exists_pow_bound`
from `CslibFrontier/Logics/FirstOrder/Encoding/PowerBound.lean`).
On `Fin B` equipped with `v.powerStructure a B`, we conjoin `v.layoutESOSentence` and
`v.tableauESOSentence tm` and existentially project the intermediate input-tape relations
(`uLenSym`, `uBitSym`) via `Cslib.Logic.ESO.Sentence.project` to obtain
`v.npPowerSentence tm : ESO.Sentence v.powerLanguage`. Pulling this sentence back to `(M, <)` along
the first-order interpretation `v.powerInterpretation k har` and existentially quantifying the
linear order `<` via `Cslib.Logic.ESO.Definable.of_powerLanguage` (which handles cardinalities
`0` and `1` by finite truth-table disjunction in
`CslibFrontier/Computability/Complexity/Fagin/Small.lean`) yields the defining ESO
sentence over `L`.

## Main definitions

* `Cslib.Logic.Vocabulary.npPowerSentence`: the existential second-order sentence over
  `v.powerLanguage` combining input-tape layout synthesis and the accepting tableau of `tm`.

## Main results

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
  obtain ⟨t₀, _, ht₀, -, m, State, hfin, tm, htm⟩ :=
    computableInPolyTime_strictVerifier encStructure p hVpoly
  let _ := Fintype.ofFinite State
  classical
  obtain ⟨k, hk, har, hpow⟩ := v.exists_pow_bound
    (fun n => 2 * n + 1 + p.eval n + 1 + t₀ (2 * n + 1 + p.eval n)) (by fun_prop)
  refine ⟨k, hk, har, v.npPowerSentence tm, fun a ha h2 => ?_⟩
  have hB := hpow a ha h2
  rw [v.realize_npPowerSentence tm ha (by rw [length_frame]; omega),
    hV.exists_strictVerifier_eq_true_iff]
  constructor
  · rintro ⟨w, hw⟩
    have hlen_pair : (encPair encStructure encBits (a, w)).length =
        2 * (encStructure a).length + 1 + p.eval (encStructure a).length := by
      rw [encPair_apply, List.length_append, encBits_apply, length_frame,
        length_eq_of_strictVerifier_eq_true hw]
    obtain ⟨hhalt, hout⟩ := (htm (a, w)).runFrom_of_le
      (show t₀ (encPair encStructure encBits (a, w)).length ≤ a.1 ^ k - 1 by rw [hlen_pair]; omega)
    simp only [encPair_apply, encBits_apply, hw, encBool_apply] at hhalt hout
    exact ⟨w.length, by rw [length_frame, length_eq_of_strictVerifier_eq_true hw]; omega,
      CookLevin.tableau_satisfiable_iff.2 ⟨w, rfl, hhalt, hout⟩⟩
  · rintro ⟨L, -, hsat⟩
    obtain ⟨w, -, hhalt, hout⟩ := CookLevin.tableau_satisfiable_iff.1 hsat
    have hcomp := (htm (a, w)).1
    rw [encPair_apply, encBits_apply] at hcomp
    rw [hcomp.output_eq_of_halted hhalt, encBool_apply, List.singleton_inj] at hout
    exact ⟨w, hout⟩

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
