/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple
public import CslibFrontier.Logics.FirstOrder.Ordered.Tuple.Flatten

/-!
# Composition of canonical full-tuple interpretations

Composition pulls back each output input-relation formula and flattens the outer coordinate
before the inner coordinate. Canonical numeric formulas are reconstructed on the full product
dimension. The flattening rank theorem proves that these have exactly the semantics of the
successive canonical expansions, including order, BIT and the numeric constants.

The source universe has at least two elements and both dimensions are positive. No automatic
numeric preservation is claimed for arbitrary restricted domains, and no machine bound is implied.

## Main definitions

* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.comp`: native full-tuple composition.

## Main results

* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.compEquiv`: canonical composition isomorphism.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.realize_comp_onFormula`:
  semantic agreement with successive native pullbacks.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Proposition 1.28, Exercise 1.30,
  Remark 1.32 and Exercise 1.33, with the full tuple universe.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered.FullTupleInterpretation

open FirstOrder Language Structure

variable {L L' L'' : Language} {k l : ℕ} [L'.IsRelational]

/-- Pull back output input-relation formulas and flatten `(j, i)` to `j * k + i`.
All numeric symbols are supplied by the canonical full-tuple construction at dimension `l * k`. -/
noncomputable def comp (J : FullTupleInterpretation L' L'' l)
    (I : FullTupleInterpretation L L' k) : FullTupleInterpretation L L'' (l * k) where
  rel R := (I.onFormula (J.rel R)).relabel
    fun p => (p.1.1, finProdFinEquiv (p.1.2, p.2))

variable (J : FullTupleInterpretation L' L'' l) (I : FullTupleInterpretation L L' k)
  {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]

/-- The composite relation definition agrees with the second interpretation on the inner ranks. -/
theorem realize_comp_rel (hk : 0 < k) {r : ℕ} (R : L''.Relations r)
    (v : Fin r → Fin l → Fin k → Fin n) :
    ((J.comp I).rel R).Realize (fun p => flattenTuple (v p.1) p.2) ↔
      letI := I.inputStructure (n := n)
      letI : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
      (J.rel R).Realize (fun p => lexEquiv (v p.1 p.2)) := by
  simp only [comp, Formula.realize_relabel, Function.comp_def, flattenTuple_apply]
  exact I.realize_onFormula hk (J.rel R) (fun p => v p.1 p.2)

variable [L''.IsRelational]

/-- Successive canonical interpretations and the flattened composite are isomorphic as full
ordered structures. The map preserves the natural index of every element. -/
def compEquiv (hk : 0 < k) (hl : 0 < l) :
    letI := I.inputStructure (n := n)
    letI : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
    letI := J.inputStructure (n := n ^ k)
    letI : Fact (2 ≤ (n ^ k) ^ l) := ⟨two_le_pow (n := n ^ k) hl⟩
    letI := (J.comp I).inputStructure (n := n)
    letI : Fact (2 ≤ n ^ (l * k)) := ⟨two_le_pow (n := n) (Nat.mul_pos hl hk)⟩
    Fin ((n ^ k) ^ l) ≃[language L''] Fin (n ^ (l * k)) := by
  letI := I.inputStructure (n := n)
  letI : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
  letI := J.inputStructure (n := n ^ k)
  letI : Fact (2 ≤ (n ^ k) ^ l) := ⟨two_le_pow (n := n ^ k) hl⟩
  letI := (J.comp I).inputStructure (n := n)
  letI : Fact (2 ≤ n ^ (l * k)) := ⟨two_le_pow (n := n) (Nat.mul_pos hl hk)⟩
  have hcard : (n ^ k) ^ l = n ^ (l * k) := by rw [← pow_mul, Nat.mul_comm k l]
  let e := finCongr hcard
  refine { e with map_fun' := ?_, map_rel' := ?_ }
  · intro r f x
    cases f with
    | inl f => exact isEmptyElim f
    | inr f =>
      cases f <;> apply Fin.ext
      · rfl
      · rfl
      · exact congrArg (· - 1) hcard
  · intro r R x
    cases R with
    | inl R =>
      let v : Fin r → Fin l → Fin k → Fin n :=
        fun a j => lexEquiv.symm (lexEquiv.symm (x a) j)
      have hx (a : Fin r) : lexEquiv.symm (e (x a)) = flattenTuple (v a) := by
        apply lexEquiv.injective
        apply Fin.ext
        rw [Equiv.apply_symm_apply]
        change (e (x a)).val = lexRank (flattenTuple (v a))
        rw [lexRank_flattenTuple]
        change (x a).val = lexRank (fun j => lexEquiv (lexEquiv.symm (lexEquiv.symm (x a) j)))
        simp only [Equiv.apply_symm_apply, lexRank]
      change ((J.comp I).rel R).Realize (fun p => lexEquiv.symm (e (x p.1)) p.2) ↔ _
      simp only [hx]
      rw [J.realize_comp_rel I hk R v]
      change (J.rel R).Realize (fun p => lexEquiv (lexEquiv.symm (lexEquiv.symm (x p.1) p.2))) ↔
        (J.rel R).Realize (fun p => lexEquiv.symm (x p.1) p.2)
      simp only [Equiv.apply_symm_apply]
    | inr R =>
      cases R <;> rfl

/-- The composition isomorphism changes only the type-level expression for the same size. -/
@[simp] theorem compEquiv_apply_val (hk : 0 < k) (hl : 0 < l) (x : Fin ((n ^ k) ^ l)) :
    ((J.compEquiv I hk hl) x).val = x.val := rfl

/-- Every ordered formula has the same truth value under the composite pullback and the two
successive pullbacks. Constants and quantifiers are included. -/
theorem realize_comp_onFormula (hk : 0 < k) (hl : 0 < l) {α : Type*}
    (φ : (language L'').Formula α) (v : α → Fin l → Fin k → Fin n) :
    ((J.comp I).onFormula φ).Realize (fun p => flattenTuple (v p.1) p.2) ↔
      (I.onFormula (J.onFormula φ)).Realize (fun p => v p.1.1 p.1.2 p.2) := by
  let := I.inputStructure (n := n)
  let : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
  let := J.inputStructure (n := n ^ k)
  let : Fact (2 ≤ (n ^ k) ^ l) := ⟨two_le_pow (n := n ^ k) hl⟩
  let := (J.comp I).inputStructure (n := n)
  let : Fact (2 ≤ n ^ (l * k)) := ⟨two_le_pow (n := n) (Nat.mul_pos hl hk)⟩
  rw [(J.comp I).realize_onFormula (Nat.mul_pos hl hk) φ (fun a => flattenTuple (v a)),
    I.realize_onFormula hk (J.onFormula φ) (fun p => v p.1 p.2),
    J.realize_onFormula hl φ (fun a j => lexEquiv (v a j))]
  have hv : (fun a => lexEquiv (flattenTuple (v a))) =
      fun a => J.compEquiv I hk hl (lexEquiv (fun j => lexEquiv (v a j))) := by
    funext a
    apply Fin.ext
    rw [compEquiv_apply_val]
    exact lexRank_flattenTuple (v a)
  rw [hv]
  exact StrongHomClass.realize_formula (J.compEquiv I hk hl) φ

/-- Composition preserves sentence pullback, including the canonical numeric vocabulary. -/
theorem realize_comp_onSentence (hk : 0 < k) (hl : 0 < l) (φ : (language L'').Sentence) :
    Fin n ⊨ (J.comp I).onSentence φ ↔ Fin n ⊨ I.onSentence (J.onSentence φ) := by
  let := I.inputStructure (n := n)
  let : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
  let := J.inputStructure (n := n ^ k)
  let : Fact (2 ≤ (n ^ k) ^ l) := ⟨two_le_pow (n := n ^ k) hl⟩
  let := (J.comp I).inputStructure (n := n)
  let : Fact (2 ≤ n ^ (l * k)) := ⟨two_le_pow (n := n) (Nat.mul_pos hl hk)⟩
  rw [(J.comp I).realize_onSentence (Nat.mul_pos hl hk), I.realize_onSentence hk,
    J.realize_onSentence hl]
  exact (StrongHomClass.realize_sentence (J.compEquiv I hk hl) φ).symm

end Cslib.Logic.FO.Ordered.FullTupleInterpretation
