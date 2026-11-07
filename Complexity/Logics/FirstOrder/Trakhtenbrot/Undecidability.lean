/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Trakhtenbrot.Evaln
public import Complexity.Logics.FirstOrder.Raw.FinSat
public import Mathlib.Computability.Halting
import Complexity.Foundations.Computability.ComputablePred

/-!
# Trakhtenbrot's theorem

**Trakhtenbrot's theorem** ([Trakhtenbrot1950]; compare [Libkin2004], Theorem 9.2 and
Corollary 9.3): finite satisfiability of first-order sentences is undecidable. It is proved here
for raw relational sentences over the union of all finite vocabularies (unboundedly many relation
symbols, each of arity at most three); Libkin's fixed-vocabulary form is not yet formalized (see
**Scope** below). Since finite satisfiability is r.e.
(`Cslib.Logic.FO.RawFormula.rePred_finSat`), finite validity is co-r.e. but not r.e., so no
effective proof system is sound and complete for truth in all finite structures.

The reduction is from the halting problem for Mathlib's partial recursive codes
(`ComputablePred.halting_problem`). For a code `c`, `Trakhtenbrot.haltSentence c` is the
conjunction of the arithmetic axioms (`Complexity/Logics/FirstOrder/Trakhtenbrot/Arithmetic.lean`),
the axioms for the graphs of `evaln · d` for all codes `d` with `encode d ≤ encode c`
(`Complexity/Logics/FirstOrder/Trakhtenbrot/Evaln.lean`), and the goal "the graph of `c` contains a
tuple `(k, 0, x)`". Then `c` halts on input `0` iff `haltSentence c` has a finite model
(`Trakhtenbrot.eval_dom_iff_finSat`):

* if `evaln K c 0 = some x`, the true arithmetic and the true graphs of `evaln k d` for `k ≤ K`
  on a large enough initial segment `Fin N` form a model;
* in a finite model the arithmetic is standard (`arithModel_faithful`), so a tuple `(k, 0, x)` in
  the graph of `c` is a true fact `evaln k c 0 = some x` (`evaln_of_model`).

The map `c ↦ haltSentence c` is primitive recursive.

**Scope.** The textbook proofs encode Turing machine runs directly; here the encoded computation
is Mathlib's step-bounded evaluator `Nat.Partrec.Code.evaln`, which plays the same role. The
sentences are library-local `Cslib.Logic.FO.RawFormula`s, not Mathlib `L.Sentence`s (see the
module documentation of `Complexity/Logics/FirstOrder/Raw/Basic.lean`). The reduction uses
relation symbols of arity at most three, but unboundedly many of them; Libkin's Theorem 9.2 is
stated for every vocabulary with at least one binary relation symbol, a sharpening that needs a
further interpretation of the vocabulary in one binary relation and is not formalized here.

## Main definitions

* `Cslib.Logic.FO.Trakhtenbrot.haltSentence`: the sentence of a code.

## Main results

* `Cslib.Logic.FO.Trakhtenbrot.eval_dom_iff_finSat`: the reduction from halting.
* `Cslib.Logic.FO.Trakhtenbrot.primrec_haltSentence`: the reduction is primitive recursive.
* `Cslib.Logic.FO.RawFormula.not_computablePred_finSat`: **Trakhtenbrot's theorem**, for raw
  sentences over the union of all finite vocabularies.
* `Cslib.Logic.FO.RawFormula.not_rePred_finValid`: finite validity of such sentences is not r.e.
* `Cslib.Logic.FO.RawFormula.not_rePred_not_finSat`: finite unsatisfiability is not r.e.
* `Cslib.Logic.FO.RawFormula.exists_finValid_not_of_rePred`: every r.e. set of finitely valid
  sentences misses a finitely valid sentence.
* `Cslib.Logic.FO.RawFormula.exists_finValid_unprovable`: every sound proof system with a
  decidable proof relation leaves some finitely valid sentence unprovable.

## References

* [B. A. Trakhtenbrot, *Impossibility of an algorithm for the decision problem in finite
  classes*][Trakhtenbrot1950]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
-/

public section

namespace Cslib.Logic.FO

open RawFormula
open Nat.Partrec (Code)
open Encodable (encode)

namespace Trakhtenbrot

variable {M : Type*}

/-! ### The reduction -/

/-- "The graph of code number `m` contains a tuple `(k, 0, x)`." -/
def goalF (m : ℕ) : RawFormula :=
  ex 0 (ex 1 (ex 2 (conj (rel 1 [1]) (rel (m + 4) [0, 1, 2]))))

/-- The sentence of a code `c`: the arithmetic axioms, the goal "`c` halts on input `0`", and the
`evaln` axioms for all codes up to `c`. -/
def haltSentence (c : Code) : RawFormula :=
  bigConj (arithAxioms ++ goalF (encode c) ::
    (List.range (encode c + 1)).map fun m => evAx (Denumerable.ofNat Code m))

theorem realize_goalF {I : ℕ → List M → Prop} {v : ℕ → M} (m : ℕ) :
    (goalF m).Realize I v ↔ ∃ k z x, I 1 [z] ∧ I (m + 4) [k, z, x] := by
  simp [goalF]

theorem realize_haltSentence {I : ℕ → List M → Prop} {v : ℕ → M} (c : Code) :
    (haltSentence c).Realize I v ↔ ArithModel I ∧
      (∃ k z x, I 1 [z] ∧ I (encode c + 4) [k, z, x]) ∧
        ∀ d : Code, encode d ≤ encode c → (evAx d).Realize I v := by
  simp only [haltSentence, realize_bigConj, List.mem_append, List.mem_cons, List.mem_map,
    List.mem_range]
  constructor
  · intro h
    refine ⟨realize_arithAxioms.1 fun φ hφ => h φ (Or.inl hφ),
      (realize_goalF _).1 (h _ (Or.inr (Or.inl rfl))), fun d hd => ?_⟩
    exact h _ (Or.inr (Or.inr ⟨encode d, by omega, by rw [Denumerable.ofNat_encode]⟩))
  · rintro ⟨h1, h2, h3⟩ φ (hφ | rfl | ⟨m, hm, rfl⟩)
    · exact realize_arithAxioms.2 h1 φ hφ
    · exact (realize_goalF _).2 h2
    · exact h3 _ (by rw [Denumerable.encode_ofNat]; omega)

/-- **The reduction.** A code halts on input `0` iff its sentence has a finite model. -/
theorem eval_dom_iff_finSat (c : Code) : (Code.eval c 0).Dom ↔ FinSat (haltSentence c) := by
  constructor
  · intro h
    obtain ⟨K, hK⟩ := Code.evaln_complete.1 (Part.get_mem h)
    have hK' : Code.evaln K c 0 = some ((Code.eval c 0).get h) := hK
    let N := K + outBound K (encode c) + 1
    have hKN : K < N := by omega
    refine ⟨Fin N, inferInstance, ⟨⟨0, by omega⟩⟩, stdInterp N K, fun _ => ⟨0, by omega⟩, ?_⟩
    rw [realize_haltSentence]
    refine ⟨arithModel_stdInterp, ?_, fun d hd => ?_⟩
    · have hx : (Code.eval c 0).get h < N := by
        have := le_outBound le_rfl le_rfl hK'
        omega
      refine ⟨⟨K, hKN⟩, ⟨0, by omega⟩, ⟨_, hx⟩, (stdInterp_zero _).2 rfl, ?_⟩
      rw [stdInterp_ev]
      exact ⟨le_rfl, hK'⟩
    · rw [realize_evAx]
      exact stdInterp_caseSem (by omega) d hd
  · rintro ⟨M, _, _, I, v, h⟩
    rw [realize_haltSentence] at h
    obtain ⟨hA, ⟨k, z, x, hz, hI⟩, hE⟩ := h
    obtain ⟨N, e, hlt, hz', hs, hp⟩ := arithModel_faithful hA
    have hax : ∀ d : Code, encode d ≤ encode c → ∀ k n x, I (encode d + 4) [k, n, x] →
        I 0 [n, k] ∧ CaseSem I d k n x := fun d hd => (realize_evAx d).1 (hE d hd)
    have H : Code.evaln (e k) c (e z) = some (e x) :=
      evaln_of_model (fun a => (e a : ℕ)) hlt hz' hs hp hax c le_rfl k z x hI
    rw [(hz' z).1 hz] at H
    exact Part.dom_iff_mem.2 ⟨_, Code.evaln_sound H⟩

/-! ### Computability of the reduction -/

section Primrec

open Primrec

theorem primrec_goalF : Primrec goalF :=
  primrec_ex (const 0) (primrec_ex (const 1) (primrec_ex (const 2)
    (primrec_conj (const (rel 1 [1]))
      (primrec_rel (nat_add.comp Primrec.id (const 4)) (const [0, 1, 2])))))

/-- The reduction `c ↦ haltSentence c` is primitive recursive. -/
theorem primrec_haltSentence : Primrec haltSentence :=
  primrec_bigConj.comp (list_append.comp (const arithAxioms)
    (list_cons.comp (primrec_goalF.comp Primrec.encode)
      (list_map (list_range.comp (succ.comp Primrec.encode))
        (primrec_evAx.comp ((Primrec.ofNat Code).comp snd)).to₂)))

end Primrec

end Trakhtenbrot

namespace RawFormula

open Trakhtenbrot

/-! ### Trakhtenbrot's theorem and its corollaries -/

/-- **Trakhtenbrot's theorem** ([Trakhtenbrot1950]): finite satisfiability of first-order
sentences is undecidable. This is the form for raw relational sentences over the union of all
finite vocabularies (unboundedly many relation symbols, each of arity at most three). The
fixed-vocabulary form of [Libkin2004], Theorem 9.2 (every vocabulary with a binary relation
symbol) is not yet formalized. -/
theorem not_computablePred_finSat : ¬ComputablePred FinSat := fun h =>
  ComputablePred.halting_problem 0 <|
    (h.comp primrec_haltSentence.to_comp).of_eq fun c => (eval_dom_iff_finSat c).symm

/-- **Finite validity is not r.e.**, for raw relational sentences over the union of all finite
vocabularies. [Libkin2004], Corollary 9.3, is the corresponding statement for a fixed vocabulary
with a binary relation symbol, which is not yet formalized. -/
theorem not_rePred_finValid : ¬REPred FinValid := fun h =>
  ComputablePred.halting_problem_not_re 0 <|
    (h.comp (primrec_neg primrec_haltSentence).to_comp).of_eq fun c => by
      rw [finValid_neg_iff, ← eval_dom_iff_finSat]

/-- Finite unsatisfiability is not r.e. -/
theorem not_rePred_not_finSat : ¬REPred fun φ => ¬FinSat φ := fun h =>
  not_rePred_finValid <| (h.comp (primrec_neg Primrec.id).to_comp).of_eq fun φ =>
    (finValid_iff_not_finSat_neg φ).symm

/-- Finite validity is undecidable. -/
theorem not_computablePred_finValid : ¬ComputablePred FinValid := fun h =>
  not_rePred_finValid h.to_re

/-- **Incompleteness for finite validity.** Every r.e. set of finitely valid sentences misses some
finitely valid sentence. -/
theorem exists_finValid_not_of_rePred {S : RawFormula → Prop} (hS : REPred S)
    (hsound : ∀ φ, S φ → FinValid φ) : ∃ φ, FinValid φ ∧ ¬S φ := by
  by_contra hne
  exact not_rePred_finValid (hS.of_eq fun φ =>
    ⟨hsound φ, fun h => by_contra fun hs => hne ⟨φ, h, hs⟩⟩)

/-- **No sound and complete proof system for finite validity.** If `P φ π` ("`π` is a proof of
`φ`") is a decidable relation and only finitely valid sentences have proofs, then some finitely
valid sentence has no proof. -/
theorem exists_finValid_unprovable {β : Type*} [Primcodable β] {P : RawFormula → β → Prop}
    (hP : ComputablePred (Function.uncurry P)) (hsound : ∀ φ π, P φ π → FinValid φ) :
    ∃ φ, FinValid φ ∧ ∀ π, ¬P φ π := by
  obtain ⟨φ, hφ, hS⟩ := exists_finValid_not_of_rePred (ComputablePred.rePred_exists hP)
    fun φ ⟨π, h⟩ => hsound φ π h
  exact ⟨φ, hφ, fun π h => hS ⟨π, h⟩⟩

end RawFormula

end Cslib.Logic.FO
