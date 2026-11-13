/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Encoding
public import CslibFrontier.Logics.SecondOrder.Projection
public import CslibFrontier.Logics.SecondOrder.Reduction

/-!
# The power interpretation on `k`-tuples

Given a finite relational vocabulary `v : Vocabulary L` and a tuple width `k ≥ 1` bounding all
arities of `v`, a `k`-tuple `x : Fin k → M` over a finite structure `M` numbered by `e : M ≃ Fin n`
represents the natural number `tupleIndex (e ∘ x) < n ^ k` in base `n` (little-endian).

The relational language `v.powerLanguage` describes the numbers below `n ^ k` together with the
input tables:
* a binary relation `powerLt` for the strict linear order `<` on `Fin (n ^ k)`,
* a unary relation `powerIsElem` for numbers `< n` (those whose high `k - 1` digits vanish),
* for each symbol `i : Fin v.count` of arity `a = v.arity i`, a unary relation `powerInTable i`
  for numbers `< n ^ a` (those whose high `k - a` digits vanish), and
* for each symbol `i : Fin v.count` of arity `a = v.arity i`, a unary relation `powerTableBit i`
  holding of `m < n ^ a` when the `m`-th bit of the `i`-th relation table is `true`.

We construct a first-order interpretation `v.powerInterpretation k har` of dimension `Fin k` from
`L.sum ESO.orderLanguage` to `v.powerLanguage` and prove (`v.powerEquiv`) that on `(M, e)` the
interpreted structure is isomorphic to `(Fin (n ^ k), v.powerStructure (v.encode M e) (n ^ k))`.
Pulling back along this interpretation via `FO.Interpretation.onESOSentence` therefore turns an
existential second-order sentence about the numeric structure `Fin (n ^ k)` into one about `M`
(`v.realize_onESOSentence_powerInterpretation`). Machine simulations in descriptive complexity
(Fagin, Immerman–Vardi, Grädel, NL ⊆ FO(TC)) run on this numeric structure.

## Main definitions

* `Cslib.Logic.Vocabulary.powerLanguage`, `Cslib.Logic.Vocabulary.powerIsElem`,
  `Cslib.Logic.Vocabulary.powerInTable`, `Cslib.Logic.Vocabulary.powerTableBit`,
  `Cslib.Logic.Vocabulary.powerLt`: the relational language of the `k`-th power structure and its
  symbols.
* `Cslib.Logic.Vocabulary.powerStructure`: the canonical `v.powerLanguage`-structure on `Fin B`
  induced by an `EncodedStructure`.
* `Cslib.Logic.Vocabulary.powerInterpretation`: the first-order interpretation of dimension `Fin k`
  from `L.sum ESO.orderLanguage` to `v.powerLanguage`.

## Main results

* `Cslib.Logic.Vocabulary.powerEquiv`: the structure interpreted by `v.powerInterpretation` in
  `(M, orderRelOfEquiv e)` is isomorphic to `Fin (n ^ k)` with `v.powerStructure (v.encode M e)`.
* `Cslib.Logic.Vocabulary.realize_onESOSentence_powerInterpretation`: pulling an existential
  second-order sentence back along `v.powerInterpretation` preserves its truth value.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v

open FirstOrder Language Structure CategoryTheory BoundedFormula

namespace Cslib.Logic

/-! ### The power language and canonical numeric structure -/

namespace Vocabulary

variable {L : Language.{u, v}} (v : Vocabulary L)

/-- The relational language of a power structure over a vocabulary `v`:
* unary relation `.inl ()` (`powerIsElem`) testing `< n`,
* unary relation `.inr (.inl i)` (`powerInTable i`) testing `< n ^ v.arity i`,
* unary relation `.inr (.inr i)` (`powerTableBit i`) testing the `i`-th relation table of `v`, and
* binary relation `()` (`powerLt`) for the strict linear order `<`. -/
def powerLanguage : Language.{0, 0} where
  Functions _ := Empty
  Relations
    | 1 => Unit ⊕ Fin v.count ⊕ Fin v.count
    | 2 => Unit
    | _ => Empty

instance : v.powerLanguage.IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

/-- The binary relation symbol `<` of `v.powerLanguage`. -/
def powerLt : v.powerLanguage.Relations 2 := ()

/-- The unary relation symbol `< n` of `v.powerLanguage`. -/
def powerIsElem : v.powerLanguage.Relations 1 := .inl ()

/-- The unary relation symbol `< n ^ v.arity i` of `v.powerLanguage`. -/
def powerInTable (i : Fin v.count) : v.powerLanguage.Relations 1 := .inr (.inl i)

/-- The unary relation symbol for the `i`-th relation table of `v` in `v.powerLanguage`. -/
def powerTableBit (i : Fin v.count) : v.powerLanguage.Relations 1 := .inr (.inr i)

/-- The canonical `v.powerLanguage`-structure on `Fin B` induced by an `EncodedStructure` `a`:
`powerLt` is `<` on `Fin B`, `powerIsElem` is `< a.1`, `powerInTable i` is `< a.1 ^ v.arity i`,
and `powerTableBit i` holds of `m` when `m < a.1 ^ v.arity i` and bit `m` of the `i`-th table of
`a` is `true`. -/
@[instance_reducible]
def powerStructure (a : EncodedStructure) (B : ℕ) : v.powerLanguage.Structure (Fin B) where
  funMap f := isEmptyElim f
  RelMap {m} r x := match m, r with
    | 1, .inl () => (x 0 : ℕ) < a.1
    | 1, .inr (.inl i) => (x 0 : ℕ) < a.1 ^ v.arity i
    | 1, .inr (.inr i) =>
      (x 0 : ℕ) < a.1 ^ v.arity i ∧ (v.table a (v.symbol i)).getD (x 0 : ℕ) false = true
    | 2, () => x 0 < x 1

private theorem relMap_powerLt (a : EncodedStructure) (B : ℕ) (x : Fin 2 → Fin B) :
    (v.powerStructure a B).RelMap v.powerLt x ↔ x 0 < x 1 :=
  Iff.rfl

private theorem relMap_powerIsElem (a : EncodedStructure) (B : ℕ) (x : Fin 1 → Fin B) :
    (v.powerStructure a B).RelMap v.powerIsElem x ↔ (x 0 : ℕ) < a.1 :=
  Iff.rfl

theorem relMap_powerInTable (a : EncodedStructure) (B : ℕ) (i : Fin v.count)
    (x : Fin 1 → Fin B) :
    (v.powerStructure a B).RelMap (v.powerInTable i) x ↔ (x 0 : ℕ) < a.1 ^ v.arity i :=
  Iff.rfl

private theorem relMap_powerTableBit (a : EncodedStructure) (B : ℕ) (i : Fin v.count)
    (x : Fin 1 → Fin B) :
    (v.powerStructure a B).RelMap (v.powerTableBit i) x ↔
      (x 0 : ℕ) < a.1 ^ v.arity i ∧ (v.table a (v.symbol i)).getD (x 0 : ℕ) false = true :=
  Iff.rfl

/-! ### The first-order interpretation of `v.powerLanguage` on `k`-tuples -/

section Interpretation

/-- The binary relation symbol `<` of `ESO.orderLanguage`, inside `L.sum ESO.orderLanguage`. -/
abbrev ltRel : (L.sum ESO.orderLanguage).Relations 2 :=
  Sum.inr ESO.ltSym

/-- The formula `x < y` in `L.sum ESO.orderLanguage` for free variables `p, q : α`. -/
def ltVarFormula {α : Type*} (p q : α) : (L.sum ESO.orderLanguage).Formula α :=
  ltRel.boundedFormula₂ (.var (.inl p)) (.var (.inl q))

/-- The formula `∀ z, ¬ (z < x_p)` in `L.sum ESO.orderLanguage`, saying that `x_p` is the minimum
element of the linear order. -/
def isMinVarFormula {α : Type*} (p : α) : (L.sum ESO.orderLanguage).Formula α :=
  ∀' ∼(ltRel.boundedFormula₂ &0 (.var (.inl p)))

private theorem relMap_ltRel {M : Type} [L.Structure M] {n : ℕ} (e : M ≃ Fin n)
    (x : Fin 2 → M) :
    @RelMap (L.sum ESO.orderLanguage) M
      (@sumStructure _ _ M _
        (ESO.varLanguage.structure (arity := fun _ : Unit => 2) (ESO.orderRelOfEquiv e))) 2
      ltRel x ↔ e (x 0) < e (x 1) :=
  Iff.rfl

private theorem realize_ltVarFormula {α : Type*} {M : Type} [L.Structure M] {n : ℕ} (e : M ≃ Fin n)
    (val : α → M) (p q : α) :
    (letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2) (ESO.orderRelOfEquiv e);
      (ltVarFormula (L := L) p q).Realize val) ↔ e (val p) < e (val q) := by
  let _ := ESO.varLanguage.structure (arity := fun _ : Unit => 2) (ESO.orderRelOfEquiv e)
  simp [ltVarFormula, Formula.Realize, relMap_ltRel]

private theorem realize_isMinVarFormula {α : Type*} {M : Type} [L.Structure M] {n : ℕ}
    (e : M ≃ Fin n)
    (val : α → M) (p : α) :
    (letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2) (ESO.orderRelOfEquiv e);
      (isMinVarFormula (L := L) p).Realize val) ↔ (e (val p) : ℕ) = 0 := by
  let _ := ESO.varLanguage.structure (arity := fun _ : Unit => 2) (ESO.orderRelOfEquiv e)
  have h1 : (isMinVarFormula (L := L) p).Realize val ↔ ∀ z : M, ¬ (e z < e (val p)) := by
    simp [isMinVarFormula, Formula.Realize, relMap_ltRel, Fin.snoc]
  rw [h1]
  constructor
  · intro h
    by_contra hne
    have h0 : 0 < (e (val p) : ℕ) := by omega
    have hn : 0 < n := h0.trans (e (val p)).2
    have := h (e.symm ⟨0, hn⟩)
    simp [Fin.lt_def, h0] at this
  · intro h z
    simp [Fin.lt_def, h]

variable (k : ℕ) (hk : 1 ≤ k) (har : ∀ i : Fin v.count, v.arity i ≤ k)

/-- The colexicographic `<` formula on two `k`-tuples in `L.sum ESO.orderLanguage`. -/
noncomputable def powerLtFormula : (L.sum ESO.orderLanguage).Formula (Fin 2 × Fin k) :=
  Formula.iSup fun i : Fin k =>
    ltVarFormula (0, i) (1, i) ⊓
      Formula.iInf fun j : {j : Fin k // i < j} =>
        Term.equal (.var (0, j.1)) (.var (1, j.1))

/-- The formula testing that all coordinates at indices `≥ a` are the minimum element. -/
noncomputable def highZeroFormula (a : ℕ) : (L.sum ESO.orderLanguage).Formula (Fin 1 × Fin k) :=
  Formula.iInf fun i : {i : Fin k // a ≤ (i : ℕ)} => isMinVarFormula (0, i.1)

/-- The formula defining `powerTableBit idx` on a `k`-tuple. -/
noncomputable def powerTableBitFormula (idx : Fin v.count) :
    (L.sum ESO.orderLanguage).Formula (Fin 1 × Fin k) :=
  highZeroFormula k (v.arity idx) ⊓
    Relations.formula (Sum.inl (v.symbol idx).2)
      (fun j : Fin (v.arity idx) => .var (0, Fin.castLE (har idx) j))

/-- The first-order interpretation of `v.powerLanguage` in `L.sum ESO.orderLanguage` of dimension
`Fin k`. -/
noncomputable def powerInterpretation :
    FO.Interpretation (L.sum ESO.orderLanguage) v.powerLanguage (Fin k) where
  domain := ⊤
  rel {m} r := match m, r with
    | 1, .inl () => highZeroFormula k 1
    | 1, .inr (.inl idx) => highZeroFormula k (v.arity idx)
    | 1, .inr (.inr idx) => v.powerTableBitFormula k har idx
    | 2, () => powerLtFormula k

/-- `highZeroFormula k a` reads only row `0` of its valuation, and holds there iff that `k`-tuple
has index `< n ^ a`. -/
private theorem realize_highZeroFormula {M : Type} [L.Structure M] {n : ℕ} (e : M ≃ Fin n)
    (a : ℕ) (ha : a ≤ k) (val : Fin 1 × Fin k → M) :
    (letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2) (ESO.orderRelOfEquiv e);
      (highZeroFormula (L := L) k a).Realize val) ↔
      tupleIndex (e ∘ fun i => val (0, i)) < n ^ a := by
  let _ := ESO.varLanguage.structure (arity := fun _ : Unit => 2) (ESO.orderRelOfEquiv e)
  simp only [highZeroFormula, Formula.realize_iInf, realize_isMinVarFormula e, Subtype.forall]
  exact (tupleIndex_lt_pow_iff ha _).symm

/-- `powerLtFormula k` compares rows `0` and `1` of its valuation as `k`-tuples. -/
private theorem realize_powerLtFormula {M : Type} [L.Structure M] {n : ℕ} (e : M ≃ Fin n)
    (val : Fin 2 × Fin k → M) :
    (letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2) (ESO.orderRelOfEquiv e);
      (powerLtFormula (L := L) k).Realize val) ↔
      tupleIndex (e ∘ fun i => val (0, i)) < tupleIndex (e ∘ fun i => val (1, i)) := by
  let _ := ESO.varLanguage.structure (arity := fun _ : Unit => 2) (ESO.orderRelOfEquiv e)
  simp only [powerLtFormula, Formula.realize_iSup, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_equal, Term.realize_var, realize_ltVarFormula e,
    Subtype.forall]
  rw [tupleIndex_lt_iff]
  simp only [Function.comp_apply, e.injective.eq_iff]

include hk in
/-- **The power isomorphism**: when `M` is expanded by the strict linear order of `e : M ≃ Fin n`,
 the structure interpreted by `v.powerInterpretation k har` is isomorphic to `Fin (n ^ k)` with
`v.powerStructure (v.encode M e) (n ^ k)`. -/
def powerEquiv (M : Type) [L.Structure M] {n : ℕ} (e : M ≃ Fin n) :
    letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2) (ESO.orderRelOfEquiv e)
    letI := v.powerStructure (v.encode M e) (n ^ k)
    (v.powerInterpretation k har).Model M ≃[v.powerLanguage] Fin (n ^ k) :=
  letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2) (ESO.orderRelOfEquiv e)
  letI := v.powerStructure (v.encode M e) (n ^ k)
  { toFun := fun x => finFunctionFinEquiv (e ∘ x.1)
    invFun := fun m => ⟨e.symm ∘ finFunctionFinEquiv.symm m, Formula.realize_top.2 trivial⟩
    left_inv := fun x => FO.Interpretation.Model.ext <| funext fun i => by
      simp [Function.comp_def]
    right_inv := fun m => by
      change finFunctionFinEquiv (e ∘ e.symm ∘ finFunctionFinEquiv.symm m) = m
      have h : (e ∘ e.symm ∘ finFunctionFinEquiv.symm m) = finFunctionFinEquiv.symm m := by
        funext i; simp
      rw [h, finFunctionFinEquiv.apply_symm_apply]
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {m} r x => match m, r with
      | 1, .inl () => by
        change (v.powerStructure (v.encode M e) (n ^ k)).RelMap v.powerIsElem _ ↔
          (highZeroFormula (L := L) k 1).Realize (fun p : Fin 1 × Fin k => (x p.1).1 p.2)
        rw [realize_highZeroFormula k e 1 hk, relMap_powerIsElem]
        simp [Vocabulary.encode, tupleIndex]
      | 1, .inr (.inl idx) => by
        change (v.powerStructure (v.encode M e) (n ^ k)).RelMap (v.powerInTable idx) _ ↔
          (highZeroFormula (L := L) k (v.arity idx)).Realize
            (fun p : Fin 1 × Fin k => (x p.1).1 p.2)
        rw [realize_highZeroFormula k e (v.arity idx) (har idx), relMap_powerInTable]
        simp [Vocabulary.encode, tupleIndex]
      | 1, .inr (.inr idx) => by
        change (v.powerStructure (v.encode M e) (n ^ k)).RelMap (v.powerTableBit idx) _ ↔
          (v.powerTableBitFormula k har idx).Realize (fun p : Fin 1 × Fin k => (x p.1).1 p.2)
        rw [powerTableBitFormula, Formula.realize_inf,
          realize_highZeroFormula k e (v.arity idx) (har idx), relMap_powerTableBit]
        change (tupleIndex (e ∘ (x 0).1) < n ^ v.arity idx ∧
            (v.table (v.encode M e) (v.symbol idx)).getD (tupleIndex (e ∘ (x 0).1)) false = true) ↔
          tupleIndex (e ∘ (x 0).1) < n ^ v.arity idx ∧
            RelMap (v.symbol idx).2 (fun j => (x 0).1 (Fin.castLE (har idx) j))
        refine and_congr_right fun hlt => ?_
        have hhigh := (tupleIndex_lt_pow_iff (har idx) (e ∘ (x 0).1)).1 hlt
        have heq := tupleIndex_eq_of_high_zero (har idx) hhigh
        rw [v.table_encode M e (v.symbol idx), heq]
        have hget := getD_relTable_eq_true_iff M e (v.symbol idx).2
          (fun j => e ((x 0).1 (Fin.castLE (har idx) j)))
        simpa [Vocabulary.arity, Function.comp_def] using hget
      | 2, () => by
        change (v.powerStructure (v.encode M e) (n ^ k)).RelMap v.powerLt _ ↔
          (powerLtFormula (L := L) k).Realize (fun p : Fin 2 × Fin k => (x p.1).1 p.2)
        rw [realize_powerLtFormula k e, relMap_powerLt]
        rfl }

include hk in
/-- Pulling back an existential second-order sentence `Ψ` over `v.powerLanguage` along
`v.powerInterpretation k har` holds in `(M, orderRelOfEquiv e)` iff `Ψ` holds in `Fin (n ^ k)`
with `v.powerStructure (v.encode M e) (n ^ k)`. -/
theorem realize_onESOSentence_powerInterpretation
    (M : Type) [L.Structure M] {n : ℕ} (e : M ≃ Fin n) (Ψ : ESO.Sentence v.powerLanguage) :
    (letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2) (ESO.orderRelOfEquiv e);
      ((v.powerInterpretation k har).onESOSentence Ψ).Realize M) ↔
      (letI := v.powerStructure (v.encode M e) (n ^ k);
        Ψ.Realize (Fin (n ^ k))) := by
  let _ := ESO.varLanguage.structure (arity := fun _ : Unit => 2) (ESO.orderRelOfEquiv e)
  let _ := v.powerStructure (v.encode M e) (n ^ k)
  rw [(v.powerInterpretation k har).realize_onESOSentence Ψ]
  exact Ψ.realize_iff_of_equiv (v.powerEquiv k hk har M e)

end Interpretation

end Vocabulary

end Cslib.Logic
