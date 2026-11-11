/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple
public import CslibFrontier.Logics.SecondOrder.Horn
import CslibFrontier.Logics.FirstOrder.Operator.Tuple

/-!
# Ordered full-tuple interpretations pull back SO∃-Horn sentences

A full-tuple ordered interpretation `I : FullTupleInterpretation L L' k` pulls back any SO∃-Horn
sentence `Φ` over `language L'` to an SO∃-Horn sentence `I.onHornSentence Φ` over `language L`.
Each relation variable of arity `r` becomes a relation variable of arity `r * k`, and each clause
of width `w` becomes a clause of width `w * k` whose guard is pulled back via `I.onFormula`.

Because `lexEquiv : (Fin k → Fin n) ≃ Fin (n ^ k)` is a bijection on the full tuple domain,
`Operator.Tuple.blockEquiv lexEquiv` identifies `r * k`-tuples over `Fin n` bijectively with
`r`-tuples over `Fin (n ^ k)`, so `I.onHornSentence Φ` has the exact truth value of `Φ` on the
canonical rank universe `Fin (n ^ k)`.

## Main definitions

* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.onHornClause`: pull back a Horn clause, scaling
  its variable width and relation arities by `k`.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.onHornSentence`: pull back an SO∃-Horn sentence
  along a full-tuple ordered interpretation.

## Main results

* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.realize_onHornSentence`: the sentence pullback
  preserves truth on the canonical lexicographically ranked universe `Fin (n ^ k)`.

## References

* [E. Grädel, *Capturing complexity classes by fragments of second-order logic*][Gradel1992],
  for SO∃-Horn encodings over tuple universes. Section and theorem locators are unverified.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Proposition 3.5 and Remark 1.32, for
  first-order tuple interpretations on canonical ordered structures.
-/

public section

open FirstOrder Language

namespace Cslib.Logic.FO.Ordered.FullTupleInterpretation

variable {L L' : Language} [L'.IsRelational] {k : ℕ}
  (I : FullTupleInterpretation L L' k)

private def scaleArgs {r w : ℕ} (f : Fin r → Fin w) : Fin (r * k) → Fin (w * k) :=
  finProdFinEquiv ∘ Prod.map f id ∘ finProdFinEquiv.symm

private theorem blockEquiv_comp_scaleArgs {M N : Type*} (e : (Fin k → M) ≃ N) {r w : ℕ}
    (f : Fin r → Fin w) (xs : Fin (w * k) → M) :
    Operator.Tuple.blockEquiv e r (xs ∘ scaleArgs (k := k) f) =
      Operator.Tuple.blockEquiv e w xs ∘ f := by
  funext i
  simp only [Operator.Tuple.blockEquiv_apply, Function.comp_apply, scaleArgs,
    Equiv.symm_apply_apply, Prod.map_apply, id_eq]

private def scaleAtom {V : Type} {arity : V → ℕ} {w : ℕ}
    (a : ESO.Horn.Atom arity (Fin w)) :
    ESO.Horn.Atom (fun i => arity i * k) (Fin (w * k)) where
  rel := a.rel
  args := scaleArgs a.args

/-- Pull back a Horn clause over `language L'` along `I`, multiplying its variable width and every
relation arity by `k`. -/
noncomputable def onHornClause {V : Type} {arity : V → ℕ}
    (C : ESO.Horn.Clause (language L') arity) :
    ESO.Horn.Clause (language L) (fun i => arity i * k) where
  width := C.width * k
  guard := (I.onFormula C.guard).relabel finProdFinEquiv
  body := C.body.map (scaleAtom (k := k))
  head := C.head.map (scaleAtom (k := k))

/-- Pull back an SO∃-Horn sentence along a full-tuple ordered interpretation, scaling every
relation arity and clause width by the tuple dimension `k`. -/
noncomputable def onHornSentence (Φ : ESO.Horn.Sentence (language L')) :
    ESO.Horn.Sentence (language L) where
  Var := Φ.Var
  arity i := Φ.arity i * k
  clauses := Φ.clauses.map I.onHornClause

private theorem holds_scaleAtom {n : ℕ} {V : Type} {arity : V → ℕ} {w : ℕ}
    (a : ESO.Horn.Atom arity (Fin w))
    {Rs : ∀ i, Set (Fin (arity i * k) → Fin n)}
    {Rt : ∀ i, Set (Fin (arity i) → Fin (n ^ k))}
    (hrel : ∀ i xs, xs ∈ Rs i ↔ Operator.Tuple.blockEquiv lexEquiv (arity i) xs ∈ Rt i)
    (xs : Fin (w * k) → Fin n) :
    (scaleAtom (k := k) a).Holds Rs xs ↔
      a.Holds Rt (Operator.Tuple.blockEquiv lexEquiv w xs) := by
  change xs ∘ scaleArgs a.args ∈ Rs a.rel ↔
    Operator.Tuple.blockEquiv lexEquiv w xs ∘ a.args ∈ Rt a.rel
  rw [hrel, blockEquiv_comp_scaleArgs]

variable {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]

private theorem holds_onHornClause (hk : 0 < k) {V : Type} {arity : V → ℕ}
    (C : ESO.Horn.Clause (language L') arity)
    {Rs : ∀ i, Set (Fin (arity i * k) → Fin n)}
    {Rt : ∀ i, Set (Fin (arity i) → Fin (n ^ k))}
    (hrel : ∀ i xs, xs ∈ Rs i ↔ Operator.Tuple.blockEquiv lexEquiv (arity i) xs ∈ Rt i) :
    letI := I.inputStructure (n := n)
    letI : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
    (I.onHornClause C).Holds Rs ↔ C.Holds Rt := by
  let := I.inputStructure (n := n)
  let : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
  let eW := Operator.Tuple.blockEquiv (lexEquiv (n := n) (k := k)) C.width
  refine eW.forall_congr ?_
  intro xs
  refine imp_congr ?_ (imp_congr ?_ ?_)
  · change ((I.onFormula C.guard).relabel finProdFinEquiv).Realize xs ↔ C.guard.Realize (eW xs)
    rw [Formula.realize_relabel]
    have hcomp : xs ∘ finProdFinEquiv = fun p : Fin C.width × Fin k =>
        xs (finProdFinEquiv (p.1, p.2)) :=
      funext fun p => congrArg (xs ∘ finProdFinEquiv) p.eta.symm
    rw [hcomp]
    exact I.realize_onFormula hk C.guard fun i j => xs (finProdFinEquiv (i, j))
  · change (∀ a' ∈ C.body.map (scaleAtom (k := k)), a'.Holds Rs xs) ↔
      ∀ a ∈ C.body, a.Holds Rt (eW xs)
    rw [List.forall_mem_map]
    exact forall₂_congr fun a _ => holds_scaleAtom a hrel xs
  · change ((C.head.map (scaleAtom (k := k))).elim False fun a' => a'.Holds Rs xs) ↔
      C.head.elim False fun a => a.Holds Rt (eW xs)
    cases C.head with
    | none => rfl
    | some a => exact holds_scaleAtom a hrel xs

/-- **Full-tuple pullback preserves SO∃-Horn truth** on the canonical lexicographically ranked
universe `Fin (n ^ k)`. -/
theorem realize_onHornSentence (hk : 0 < k) (Φ : ESO.Horn.Sentence (language L')) :
    (I.onHornSentence Φ).Realize (Fin n) ↔
      letI := I.inputStructure (n := n)
      letI : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
      Φ.Realize (Fin (n ^ k)) := by
  let := I.inputStructure (n := n)
  let : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
  constructor
  · rintro ⟨Rs, hRs⟩
    let Rs₀ : ∀ i : Φ.Var, Set (Fin (Φ.arity i * k) → Fin n) := Rs
    let Rt : ∀ i : Φ.Var, Set (Fin (Φ.arity i) → Fin (n ^ k)) :=
      fun i => {ys | (Operator.Tuple.blockEquiv lexEquiv (Φ.arity i)).symm ys ∈ Rs₀ i}
    have hrel : ∀ i xs, xs ∈ Rs₀ i ↔
        Operator.Tuple.blockEquiv lexEquiv (Φ.arity i) xs ∈ Rt i := fun i xs =>
      iff_of_eq <| congrArg (· ∈ Rs₀ i)
        ((Operator.Tuple.blockEquiv lexEquiv (Φ.arity i)).symm_apply_apply xs).symm
    refine ⟨Rt, fun C hC => ?_⟩
    exact (I.holds_onHornClause hk C hrel).mp (hRs _ (List.mem_map_of_mem hC))
  · rintro ⟨Rt, hRt⟩
    let Rs : ∀ i, Set (Fin (Φ.arity i * k) → Fin n) :=
      fun i => {xs | Operator.Tuple.blockEquiv lexEquiv (Φ.arity i) xs ∈ Rt i}
    refine ⟨Rs, fun C' hC' => ?_⟩
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC'
    exact (I.holds_onHornClause hk C fun _ _ => Iff.rfl).mpr (hRt C hC)

end Cslib.Logic.FO.Ordered.FullTupleInterpretation
