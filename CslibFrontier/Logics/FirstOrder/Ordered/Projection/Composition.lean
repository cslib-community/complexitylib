/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Projection

/-!
# Identity and composition of ordered projections

Immerman and Landau's first-order projections contain the identity map and are closed under
composition [Immerman and Landau, Proposition 3.7][ImmermanLandau1995]. The semantic composite
`J.comp I` of two full-tuple interpretations pulls back `J.rel R` through `I.onFormula`, which is
not syntactically `ProjectionFormula.toOrdered` of a decision tree. Instead, `compProjection`
substitutes into the outer projection formula directly via `ProjectionFormula.subst`: each numeric
guard over `Fin (n ^ k)` is pulled back to `k`-tuples by the empty-vocabulary full-tuple
interpretation (`ProjectionFormula.pullGuard`) and flattened along `finProdFinEquiv`, while each
input literal of `J` is replaced by the relabeled inner projection formula, negated when the outer
literal is negative (`ProjectionFormula.substLiteral`).

The resulting projection interpretation agrees with `J.comp I` on every canonical ordered
structure, so `FullTupleInterpretation.map_congr` and `FullTupleInterpretation.map_comp` identify
its image map with the composition of the two image maps.

Transitivity of quantifier-free projections (`IsQFProjection.comp`), where guards must remain
quantifier-free and `BIT`-free over `qfNumericLanguage`, is treated separately.

## Main definitions

* `Cslib.Logic.FO.ProjectionFormula.pullGuard`: pullback of pure canonical numeric guards to
  `k`-tuples.
* `Cslib.Logic.FO.ProjectionFormula.substLiteral`: substitution of relabeled inner projection
  formulas for outer input literals.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.compProjection`: syntactic composite projection
  formula.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.id`: the one-dimensional identity projection.

## Main results

* `Cslib.Logic.FO.ProjectionFormula.realize_pullGuard`: `pullGuard` evaluates a numeric guard on
  lexicographic tuple ranks.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.realize_compProjection`,
  `Cslib.Logic.FO.Ordered.FullTupleInterpretation.IsProjection.comp`: syntactic projection
  witnesses for full-tuple composition.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.isQFProjection_id`,
  `Cslib.Logic.FO.Ordered.FullTupleInterpretation.map_id`,
  `Cslib.Logic.FO.Ordered.IsQFProjectionMap.id`,
  `Cslib.Logic.FO.Ordered.IsProjectionMap.id`: identity projection maps.
* `Cslib.Logic.FO.Ordered.IsProjectionMap.comp`: composition of first-order projection maps.

## References

* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995],
  Definitions 3.3 and 3.6 and Proposition 3.7.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Proposition 1.28, Remark 1.32 and
  Exercise 1.33.
-/

public section

namespace Cslib.Logic.FO

open FirstOrder Language Structure Ordered

namespace ProjectionFormula

/-- Empty-vocabulary full-tuple interpretation used to pull pure numeric guards back to
`k`-tuples. -/
private def emptyFullTuple (k : ℕ) : FullTupleInterpretation Language.empty Language.empty k where
  rel R := isEmptyElim R

/-- Pull a pure canonical numeric guard formula back from elements to `k`-tuples, using the
canonical full-tuple numeric interpretation over the empty input vocabulary. -/
noncomputable def pullGuard {β : Type*} (k : ℕ) (g : numericLanguage.Formula β) :
    numericLanguage.Formula (β × Fin k) :=
  (LHom.sumElim (LHom.ofIsEmpty Language.empty numericLanguage) (LHom.id numericLanguage)).onFormula
    ((emptyFullTuple k).onFormula
      ((LHom.sumInr : numericLanguage →ᴸ language Language.empty).onFormula g))

/-- On `Fin n` with `2 ≤ n` and `0 < k`, `pullGuard k g` holds of `k`-tuples `v` exactly when `g`
holds of their lexicographic ranks in `Fin (n ^ k)`. -/
theorem realize_pullGuard {β : Type*} {k n : ℕ} [Fact (2 ≤ n)] (hk : 0 < k)
    (g : numericLanguage.Formula β) (v : β → Fin k → Fin n) :
    (pullGuard k g).Realize (fun p => v p.1 p.2) ↔
      letI : Fact (2 ≤ n ^ k) := ⟨FullTupleInterpretation.two_le_pow (n := n) hk⟩
      g.Realize (fun b => lexEquiv (v b)) := by
  let : Language.empty.Structure (Fin n) := Language.emptyStructure
  let : Language.empty.Structure (Fin (n ^ k)) := (emptyFullTuple k).inputStructure (n := n)
  let : Fact (2 ≤ n ^ k) := ⟨FullTupleInterpretation.two_le_pow (n := n) hk⟩
  rw [pullGuard, LHom.realize_onFormula, (emptyFullTuple k).realize_onFormula hk _ v]
  exact LHom.realize_onFormula _ g

/-- Substitute each input literal of an outer `l`-tuple projection by the relabeled inner
`k`-tuple projection formula, negating when the outer literal is negative. -/
def substLiteral {N L L' : Language} {r k l : ℕ}
    (pI : ∀ {s : ℕ}, L'.Relations s → ProjectionFormula N L (Fin s × Fin k)) :
    InputLiteral L' (Fin r × Fin l) → ProjectionFormula N L (Fin r × Fin (l * k))
  | .const b => .leaf (.const b)
  | .rel S args neg =>
    let q := (pI S).relabel fun ⟨b, i⟩ =>
      let (a, j) := args b
      (a, finProdFinEquiv (j, i))
    if neg then q.not else q

end ProjectionFormula

namespace Ordered

namespace FullTupleInterpretation

/-- Syntactic projection witness for the composite of an `l`-dimensional projection formula `pJ`
with `k`-dimensional projection formulas `pI`: guards are pulled back through
`ProjectionFormula.pullGuard k` and flattened along `finProdFinEquiv`, while leaves substitute `pI`
negated according to polarity. -/
noncomputable def compProjection {L L' : Language} {r k l : ℕ}
    (pJ : ProjectionFormula numericLanguage L' (Fin r × Fin l))
    (pI : ∀ {s : ℕ}, L'.Relations s → ProjectionFormula numericLanguage L (Fin s × Fin k)) :
    ProjectionFormula numericLanguage L (Fin r × Fin (l * k)) :=
  pJ.subst
    (fun g => (ProjectionFormula.pullGuard k g).relabel
      fun ⟨⟨a, j⟩, i⟩ => (a, finProdFinEquiv (j, i)))
    (ProjectionFormula.substLiteral pI)

private theorem realize_substLiteral {L L' : Language} [L'.IsRelational] {r k l n : ℕ}
    [Fact (2 ≤ n)] [L.Structure (Fin n)] {I : FullTupleInterpretation L L' k} (hk : 0 < k)
    (pI : ∀ {s : ℕ}, L'.Relations s → ProjectionFormula numericLanguage L (Fin s × Fin k))
    (hI : ∀ {s : ℕ} (S : L'.Relations s), I.rel S = (pI S).toOrdered)
    (v : Fin r → Fin l → Fin k → Fin n) (lit : InputLiteral L' (Fin r × Fin l)) :
    ((ProjectionFormula.substLiteral pI lit).toFormula).Realize
        (fun p => flattenTuple (v p.1) p.2) ↔
      letI := I.inputStructure (n := n)
      letI : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
      lit.Realize (fun q => lexEquiv (v q.1 q.2)) := by
  let := I.inputStructure (n := n)
  let : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
  cases lit with
  | const b =>
    simp only [ProjectionFormula.substLiteral, ProjectionFormula.realize_toFormula_leaf,
      InputLiteral.realize_const]
  | rel S args neg =>
    have hpos :
        (((pI S).relabel fun ⟨b, i⟩ =>
            let (a, j) := args b
            (a, finProdFinEquiv (j, i))).toFormula).Realize
            (fun p => flattenTuple (v p.1) p.2) ↔
          RelMap S (fun b => lexEquiv (v (args b).1 (args b).2)) := by
      rw [ProjectionFormula.realize_relabel, ProjectionFormula.realize_toFormula,
        ← ProjectionFormula.realize_toOrdered, ← hI S]
      change (I.rel S).Realize _ ↔
        (I.rel S).Realize (fun p => lexEquiv.symm (lexEquiv (v (args p.1).1 (args p.1).2)) p.2)
      refine iff_of_eq (congrArg (I.rel S).Realize (funext fun ⟨b, i⟩ => ?_))
      simp only [Function.comp_apply, Equiv.symm_apply_apply, flattenTuple_apply]
    cases neg
    · simpa only [ProjectionFormula.substLiteral, Bool.false_eq_true, ↓reduceIte,
        InputLiteral.realize_rel_false] using hpos
    · simp only [ProjectionFormula.substLiteral, ↓reduceIte, ProjectionFormula.realize_not, hpos,
        InputLiteral.realize_rel_true]

/-- On `Fin n` with `2 ≤ n` and `0 < k`, `compProjection pJ pI` evaluates on flattened blocks just
as `pJ` evaluates on the lexicographic ranks of the inner `k`-tuples in `I.inputStructure`. -/
theorem realize_compProjection {L L' : Language} [L'.IsRelational] {r k l n : ℕ}
    [Fact (2 ≤ n)] [L.Structure (Fin n)] {I : FullTupleInterpretation L L' k} (hk : 0 < k)
    (pJ : ProjectionFormula numericLanguage L' (Fin r × Fin l))
    (pI : ∀ {s : ℕ}, L'.Relations s → ProjectionFormula numericLanguage L (Fin s × Fin k))
    (hI : ∀ {s : ℕ} (S : L'.Relations s), I.rel S = (pI S).toOrdered)
    (v : Fin r → Fin l → Fin k → Fin n) :
    ((compProjection pJ pI).toOrdered).Realize (fun p => flattenTuple (v p.1) p.2) ↔
      letI := I.inputStructure (n := n)
      letI : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
      pJ.toOrdered.Realize (fun p => lexEquiv (v p.1 p.2)) := by
  let := I.inputStructure (n := n)
  let : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
  rw [ProjectionFormula.realize_toOrdered, ← ProjectionFormula.realize_toFormula,
    pJ.realize_toOrdered, ← pJ.realize_toFormula]
  unfold compProjection
  refine ProjectionFormula.realize_subst _ _
    (fun p : Fin r × Fin l => lexEquiv (v p.1 p.2))
    (fun p : Fin r × Fin (l * k) => flattenTuple (v p.1) p.2) ?_
    (realize_substLiteral hk pI hI v) pJ
  intro g
  rw [Formula.realize_relabel]
  have hcomp :
      ((fun p : Fin r × Fin (l * k) => flattenTuple (v p.1) p.2) ∘
        fun ⟨⟨a, j⟩, i⟩ => (a, finProdFinEquiv (j, i))) =
        fun p : (Fin r × Fin l) × Fin k => (fun q : Fin r × Fin l => v q.1 q.2) p.1 p.2 := by
    funext ⟨⟨a, j⟩, i⟩
    simp only [Function.comp_apply, flattenTuple_apply]
  rw [hcomp]
  exact ProjectionFormula.realize_pullGuard hk g (fun q => v q.1 q.2)

/-- **First-order projections compose** [Immerman and Landau, Proposition 3.7][ImmermanLandau1995]:
for an `l`-dimensional projection `J` and a positive-dimensional `k`-dimensional projection `I`,
there is an `(l * k)`-dimensional projection `K` whose relation formulas agree with `J.comp I` on
every canonical ordered structure. -/
theorem IsProjection.comp {L L' L'' : Language} [L'.IsRelational] {k l : ℕ}
    {J : FullTupleInterpretation L' L'' l} {I : FullTupleInterpretation L L' k}
    (hJ : J.IsProjection) (hk : 0 < k) (hI : I.IsProjection) :
    ∃ K : FullTupleInterpretation L L'' (l * k), K.IsProjection ∧
      ∀ {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {r : ℕ} (R : L''.Relations r)
        (x : Fin r × Fin (l * k) → Fin n),
        (K.rel R).Realize x ↔ ((J.comp I).rel R).Realize x := by
  classical
  let pJ : ∀ {r : ℕ}, L''.Relations r → ProjectionFormula numericLanguage L' (Fin r × Fin l) :=
    fun R => (hJ R).choose
  let pI : ∀ {s : ℕ}, L'.Relations s → ProjectionFormula numericLanguage L (Fin s × Fin k) :=
    fun S => (hI S).choose
  have hpJ : ∀ {r : ℕ} (R : L''.Relations r), J.rel R = (pJ R).toOrdered :=
    fun R => (hJ R).choose_spec
  have hpI : ∀ {s : ℕ} (S : L'.Relations s), I.rel S = (pI S).toOrdered :=
    fun S => (hI S).choose_spec
  refine ⟨ofProjection (fun R => compProjection (pJ R) pI), isProjection_ofProjection _, ?_⟩
  intro n _ _ r R x
  let v : Fin r → Fin l → Fin k → Fin n := fun a j i => x (a, finProdFinEquiv (j, i))
  have hx : x = fun p => flattenTuple (v p.1) p.2 := by
    funext ⟨a, m⟩
    exact (congrFun (flattenTuple_finProdFinEquiv fun m' => x (a, m')) m).symm
  rw [hx, rel_ofProjection, realize_compProjection hk (pJ R) pI hpI v, ← hpJ R,
    J.realize_comp_rel I hk R v]

/-- The one-dimensional identity full-tuple interpretation: each relation is its own positive input
literal on the single coordinate. -/
noncomputable def id (L : Language) : FullTupleInterpretation L L 1 :=
  ofQFProjection fun R => .leaf (.rel R (fun i => (i, 0)) false)

/-- `FullTupleInterpretation.id L` is a quantifier-free projection. -/
theorem isQFProjection_id (L : Language) : (FullTupleInterpretation.id L).IsQFProjection :=
  isQFProjection_ofQFProjection _ fun _ => ProjectionFormula.isQF_leaf _

/-- `FullTupleInterpretation.id L` is a first-order projection. -/
theorem isProjection_id (L : Language) : (FullTupleInterpretation.id L).IsProjection :=
  IsQFProjection.isProjection (isQFProjection_id L)

/-- The image of `FullTupleInterpretation.id L` is the identity on ordered structures. -/
theorem map_id (L : Language) [L.IsRelational] (M : Ordered.Structure L) :
    (FullTupleInterpretation.id L).toDomainInterpretation.map
        ((FullTupleInterpretation.id L).admissible_toDomainInterpretation one_pos) M = M := by
  let hc :
      ((FullTupleInterpretation.id L).toDomainInterpretation.map
        ((FullTupleInterpretation.id L).admissible_toDomainInterpretation one_pos) M).size =
        M.size ^ 1 :=
    card_toDomainInterpretation M
  have hsize :
      ((FullTupleInterpretation.id L).toDomainInterpretation.map
        ((FullTupleInterpretation.id L).admissible_toDomainInterpretation one_pos) M).size =
        M.size :=
    hc.trans (pow_one M.size)
  refine Ordered.Structure.ext hsize fun R x => ?_
  refine ((FullTupleInterpretation.id L).relMap_map_toDomainInterpretation one_pos R x).trans ?_
  change ((FullTupleInterpretation.id L).rel R).Realize
      (fun p => lexEquiv.symm (Fin.cast hc (x p.1)) p.2) ↔ _
  rw [FullTupleInterpretation.id, realize_rel_ofQFProjection]
  change RelMap R _ ↔ _
  refine iff_of_eq (congrArg (RelMap R) (funext fun i => ?_))
  apply Fin.ext
  change (lexEquiv.symm (Fin.cast hc (x i)) 0).val = (Fin.cast hsize (x i)).val
  rw [lexEquiv_symm_apply_val]
  simp only [Fin.rev, Fin.val_zero, zero_add, tsub_self, pow_zero, Nat.div_one, Fin.val_cast]
  exact Nat.mod_eq_of_lt ((x i).isLt.trans_eq hsize)

end FullTupleInterpretation

/-- **The identity on ordered structures is a quantifier-free projection map.** -/
theorem IsQFProjectionMap.id {L : Language} [L.IsRelational] :
    IsQFProjectionMap (_root_.id : Ordered.Structure L → Ordered.Structure L) :=
  ⟨1, .id L, one_pos, FullTupleInterpretation.isQFProjection_id L,
    funext fun M => (FullTupleInterpretation.map_id L M).symm⟩

/-- **The identity on ordered structures is a first-order projection map.** -/
theorem IsProjectionMap.id {L : Language} [L.IsRelational] :
    IsProjectionMap (_root_.id : Ordered.Structure L → Ordered.Structure L) :=
  IsQFProjectionMap.id.isProjectionMap

/-- **First-order projection maps are closed under composition**
[Immerman and Landau, Proposition 3.7][ImmermanLandau1995]. -/
theorem IsProjectionMap.comp {L L' L'' : Language} [L'.IsRelational] [L''.IsRelational]
    {f : Ordered.Structure L → Ordered.Structure L'}
    {g : Ordered.Structure L' → Ordered.Structure L''}
    (hf : IsProjectionMap f) (hg : IsProjectionMap g) : IsProjectionMap (g ∘ f) := by
  obtain ⟨k, I, hk, hI, rfl⟩ := hf
  obtain ⟨l, J, hl, hJ, rfl⟩ := hg
  obtain ⟨K, hK, hKrel⟩ := hJ.comp hk hI
  refine ⟨l * k, K, Nat.mul_pos hl hk, hK, ?_⟩
  rw [FullTupleInterpretation.map_congr (Nat.mul_pos hl hk) hKrel]
  exact funext fun M => (J.map_comp I hk hl M).symm

end Ordered

end Cslib.Logic.FO
