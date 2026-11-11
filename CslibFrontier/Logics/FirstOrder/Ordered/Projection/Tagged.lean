/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Projection
import CslibFrontier.Tactic.FirstOrder.Simp

/-!
# Tuple models and binary-tagged quantifier-free projections

Every positive-dimensional full-tuple interpretation `I : FullTupleInterpretation L L' k` on an
ordered structure `M` induces a structure `I.tupleStructure M` directly on the tuple type
`Fin k → Fin M.size`, isomorphic as an `L'`-structure to the canonical rank image
`I.toDomainInterpretation.map _ M` via `I.tupleEquiv`. For isomorphism-closed queries, correctness
of a quantifier-free projection `FullTupleInterpretation.ofQFProjection q` therefore reduces to a
combinatorial proof on genuine tuples `Fin k → Fin M.size`, without lexicographic rank arithmetic.

To build gadget projections without `BIT`, this module also provides binary `{0, max}` tag prefixes
on `Fin (d + m) → Fin n`. Since `0 ≠ max` whenever `2 ≤ n`, injective Boolean codes
`T → Fin d → Bool` carve out pairwise disjoint families of `m`-tuple blocks using only
quantifier-free endpoint equalities in `qfNumericLanguage`. Disjoint unary dispatch
(`dispatchBinaryTag`) and symmetric loopless pair dispatch (`symmPairBinaryTag`) assemble
multi-gadget projections whose `IsQF` obligations and simple-graph axioms discharge uniformly.

## Main definitions

* `Cslib.Logic.FO.Ordered.QFNumeric.varEq`, `Cslib.Logic.FO.Ordered.QFNumeric.isZero`,
  `Cslib.Logic.FO.Ordered.QFNumeric.isMax`, `Cslib.Logic.FO.Ordered.QFNumeric.varSucc`:
  quantifier-free variable equality, endpoint tests, and successor atoms in `qfNumericLanguage`.
* `Cslib.Logic.FO.ProjectionFormula.const`, `Cslib.Logic.FO.ProjectionFormula.posLit`,
  `Cslib.Logic.FO.ProjectionFormula.negLit`, `Cslib.Logic.FO.ProjectionFormula.guardAnd`:
  leaf constructors and guarded conjunction on `ProjectionFormula`.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.tupleStructure`,
  `Cslib.Logic.FO.Ordered.FullTupleInterpretation.tupleEquiv`: the `L'`-structure on
  `Fin k → Fin M.size` and its isomorphism with `DomainInterpretation.map`.
* `Cslib.Logic.FO.Ordered.mkTagged`, `Cslib.Logic.FO.Ordered.MatchBinaryTag`,
  `Cslib.Logic.FO.Ordered.hasBinaryTag`: binary `{0, max}` tag prefixes on `Fin (d + m) → Fin n`.
* `Cslib.Logic.FO.Ordered.dispatchBinaryTag`, `Cslib.Logic.FO.Ordered.symmPairBinaryTag`:
  disjoint unary and symmetric binary tag dispatch for quantifier-free projections.

## Main results

* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.relMap_tupleStructure_ofQFProjection`:
  tuple-level relation semantics of `ofQFProjection`.
* `Cslib.Logic.FO.Ordered.isQF_dispatchBinaryTag`,
  `Cslib.Logic.FO.Ordered.realize_dispatchBinaryTag`: quantifier-freeness and exact semantics of
  unary binary-tag dispatch.
* `Cslib.Logic.FO.Ordered.isQF_symmPairBinaryTag`,
  `Cslib.Logic.FO.Ordered.realize_symmPairBinaryTag`,
  `Cslib.Logic.FO.Ordered.irrefl_symmPairBinaryTag`,
  `Cslib.Logic.FO.Ordered.symm_symmPairBinaryTag`: quantifier-freeness, directed-edge semantics,
  irreflexivity, and symmetry of `symmPairBinaryTag`.
-/

public section

namespace Cslib.Logic.FO

open FirstOrder Language Structure

/-! ### ProjectionFormula combinators -/

namespace ProjectionFormula

variable {N L : Language} {α : Type*}

/-- Constant leaf projection formula. -/
@[expose] def const (b : Bool) : ProjectionFormula N L α :=
  .leaf (.const b)

/-- Positive relation-literal leaf projection formula. -/
@[expose] def posLit {r : ℕ} (R : L.Relations r) (args : Fin r → α) : ProjectionFormula N L α :=
  .leaf (.rel R args false)

/-- Negative relation-literal leaf projection formula. -/
@[expose] def negLit {r : ℕ} (R : L.Relations r) (args : Fin r → α) : ProjectionFormula N L α :=
  .leaf (.rel R args true)

/-- Conjoin a numeric guard with a projection formula (`false` when the guard fails). -/
@[expose] def guardAnd (g : N.Formula α) (p : ProjectionFormula N L α) : ProjectionFormula N L α :=
  .branch g p (.leaf (.const false))

theorem isQF_const (b : Bool) : (const b : ProjectionFormula N L α).IsQF :=
  trivial

theorem isQF_posLit {r : ℕ} (R : L.Relations r) (args : Fin r → α) :
    (posLit R args : ProjectionFormula N L α).IsQF :=
  trivial

theorem isQF_negLit {r : ℕ} (R : L.Relations r) (args : Fin r → α) :
    (negLit R args : ProjectionFormula N L α).IsQF :=
  trivial

theorem IsQF.guardAnd {g : N.Formula α} {p : ProjectionFormula N L α}
    (hg : g.IsQF) (hp : p.IsQF) : (guardAnd g p).IsQF :=
  ⟨hg, hp, trivial⟩

section Realize

variable {M : Type*} [N.Structure M] [L.Structure M]

@[simp]
theorem realize_const_true (x : α → M) :
    (const true : ProjectionFormula N L α).toFormula.Realize x := by
  simp [const, realize_toFormula_leaf, InputLiteral.realize_const]

@[simp]
theorem realize_const_false (x : α → M) :
    ¬ (const false : ProjectionFormula N L α).toFormula.Realize x := by
  simp [const, realize_toFormula_leaf, InputLiteral.realize_const]

@[simp]
theorem realize_posLit {r : ℕ} (R : L.Relations r) (args : Fin r → α) (x : α → M) :
    (posLit R args : ProjectionFormula N L α).toFormula.Realize x ↔
      RelMap R (fun i => x (args i)) := by
  rw [posLit, realize_toFormula_leaf, InputLiteral.realize_rel_false]

@[simp]
theorem realize_negLit {r : ℕ} (R : L.Relations r) (args : Fin r → α) (x : α → M) :
    (negLit R args : ProjectionFormula N L α).toFormula.Realize x ↔
      ¬ RelMap R (fun i => x (args i)) := by
  rw [negLit, realize_toFormula_leaf, InputLiteral.realize_rel_true]

@[simp]
theorem realize_guardAnd (g : N.Formula α) (p : ProjectionFormula N L α) (x : α → M) :
    (guardAnd g p).toFormula.Realize x ↔ g.Realize x ∧ p.toFormula.Realize x := by
  rw [guardAnd, realize_toFormula_branch, realize_toFormula_leaf, InputLiteral.realize_const]
  simp

end Realize

end ProjectionFormula

namespace Ordered

/-! ### Quantifier-free numeric atoms -/

namespace QFNumeric

variable {α : Type*}

/-- Variable equality `a = b` in `qfNumericLanguage`. -/
@[expose] def varEq (a b : α) : qfNumericLanguage.Formula α :=
  Term.equal (.var a) (.var b)

/-- Endpoint test `a = 0` in `qfNumericLanguage`. -/
@[expose] def isZero (a : α) : qfNumericLanguage.Formula α :=
  Term.equal (.var a) zero

/-- Endpoint test `a = max` in `qfNumericLanguage`. -/
@[expose] def isMax (a : α) : qfNumericLanguage.Formula α :=
  Term.equal (.var a) max

/-- Non-wrapping successor atom `a + 1 = b` on variables in `qfNumericLanguage`. -/
@[expose] def varSucc (a b : α) : qfNumericLanguage.Formula α :=
  succ (.var a) (.var b)

theorem isQF_varEq (a b : α) : (varEq a b).IsQF :=
  (BoundedFormula.IsAtomic.equal _ _).isQF

theorem isQF_isZero (a : α) : (isZero a).IsQF :=
  (BoundedFormula.IsAtomic.equal _ _).isQF

theorem isQF_isMax (a : α) : (isMax a).IsQF :=
  (BoundedFormula.IsAtomic.equal _ _).isQF

theorem isQF_varSucc (a b : α) : (varSucc a b).IsQF :=
  (isAtomic_succ _ _).isQF

section Realize

variable {n : ℕ} [Fact (2 ≤ n)]

instance instNeZeroOfFactTwoLe : NeZero n :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt (Fact.out : 2 ≤ n))⟩

/-- The greatest element `n - 1` of `Fin n` when `2 ≤ n`. -/
abbrev maxFin (n : ℕ) [Fact (2 ≤ n)] : Fin n :=
  ⟨n - 1, NumericFunction.index_lt Fact.out .max⟩

theorem zero_ne_maxFin : (0 : Fin n) ≠ maxFin n := by
  have h2 : 2 ≤ n := Fact.out
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_zero] at hv
  change 0 = n - 1 at hv
  omega

@[simp]
theorem realize_varEq (a b : α) (v : α → Fin n) :
    (varEq a b).Realize v ↔ v a = v b := by
  simp [varEq]

@[simp]
theorem realize_isZero (a : α) (v : α → Fin n) :
    (isZero a).Realize v ↔ v a = 0 := by
  rw [isZero, Formula.realize_equal, Term.realize_var]
  exact ⟨fun h => Fin.ext ((congrArg Fin.val h).trans (realize_zero_val v)),
    fun h => h ▸ Fin.ext (realize_zero_val v).symm⟩

@[simp]
theorem realize_isMax (a : α) (v : α → Fin n) :
    (isMax a).Realize v ↔ v a = maxFin n := by
  rw [isMax, Formula.realize_equal, Term.realize_var]
  exact ⟨fun h => Fin.ext ((congrArg Fin.val h).trans (realize_max_val v)),
    fun h => h ▸ Fin.ext (realize_max_val v).symm⟩

@[simp]
theorem realize_varSucc (a b : α) (v : α → Fin n) :
    (varSucc a b).Realize v ↔ (v a).val + 1 = (v b).val := by
  simp [varSucc]

end Realize

end QFNumeric

/-! ### Tuple models of full-tuple interpretations -/

namespace FullTupleInterpretation

variable {L L' : Language} [L'.IsRelational] {k : ℕ}

/-- The `L'`-structure induced directly on `Fin k → Fin M.size` by a full-tuple interpretation. -/
@[instance_reducible]
def tupleStructure (I : FullTupleInterpretation L L' k) (M : Ordered.Structure L) :
    L'.Structure (Fin k → Fin M.size) where
  funMap f := isEmptyElim f
  RelMap R u := (I.rel R).Realize (fun p => u p.1 p.2)

/-- Isomorphism of `L'`-structures between `Fin k → Fin M.size` (with `I.tupleStructure M`) and
the canonical ordered image `I.toDomainInterpretation.map _ M`. -/
noncomputable def tupleEquiv (I : FullTupleInterpretation L L' k) (hk : 0 < k)
    {hI : I.toDomainInterpretation.Admissible} (M : Ordered.Structure L) :
    letI := I.tupleStructure M
    (Fin k → Fin M.size) ≃[L'] I.toDomainInterpretation.map hI M := by
  letI := I.tupleStructure M
  have hI_eq : hI = I.admissible_toDomainInterpretation hk := Subsingleton.elim _ _
  subst hI_eq
  let hc : (I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk) M).size =
      M.size ^ k :=
    I.card_toDomainInterpretation M
  let e : (Fin k → Fin M.size) ≃
      Fin (I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk) M).size :=
    lexEquiv.trans (finCongr hc.symm)
  refine { e with map_fun' := fun f _ => isEmptyElim f, map_rel' := ?_ }
  intro r R u
  rw [I.relMap_map_toDomainInterpretation hk R (e.toFun ∘ u)]
  change (I.rel R).Realize (fun p => lexEquiv.symm ((Fin.cast hc ∘ (e.toFun ∘ u)) p.1) p.2) ↔
    (I.rel R).Realize (fun p => u p.1 p.2)
  refine iff_of_eq (congrArg (I.rel R).Realize (funext fun ⟨a, j⟩ => ?_))
  change lexEquiv.symm (lexEquiv (u a)) j = u a j
  exact congrFun (lexEquiv.symm_apply_apply (u a)) j

/-- On `tupleStructure`, `ofQFProjection q` realizes each relation symbol `R` via `(q R).toFormula`.
-/
theorem relMap_tupleStructure_ofQFProjection
    (q : ∀ {r : ℕ}, L'.Relations r → ProjectionFormula qfNumericLanguage L (Fin r × Fin k))
    (M : Ordered.Structure L) {r : ℕ} (R : L'.Relations r) (u : Fin r → Fin k → Fin M.size) :
    ((ofQFProjection q).tupleStructure M).RelMap R u ↔
      (q R).toFormula.Realize (fun p => u p.1 p.2) := by
  change ((ofQFProjection q).rel R).Realize (fun p => u p.1 p.2) ↔ _
  rw [realize_rel_ofQFProjection, ProjectionFormula.realize_toFormula]

/-- Membership of `I.toDomainInterpretation.map hI M` in the ordered query of an isomorphism-closed
class `S` is equivalent to membership of `(Fin k → Fin M.size)` with `I.tupleStructure M`. -/
theorem mem_of_isoClosed {S : Set (CategoryTheory.Bundled L'.Structure)} (hS : IsoClosed S)
    (I : FullTupleInterpretation L L' k) (hk : 0 < k)
    {hI : I.toDomainInterpretation.Admissible} (M : Ordered.Structure L) :
    (letI := I.tupleStructure M;
      CategoryTheory.Bundled.of (c := L'.Structure) (Fin k → Fin M.size) ∈ S) ↔
      I.toDomainInterpretation.map hI M ∈
        ({N : Ordered.Structure L' |
          CategoryTheory.Bundled.of (c := L'.Structure) N ∈ S} : Query L') := by
  let _ := I.tupleStructure M
  have hfin : Finite (CategoryTheory.Bundled.of (c := L'.Structure) (Fin k → Fin M.size)) :=
    inferInstanceAs (Finite (Fin k → Fin M.size))
  exact @hS _ _ hfin (I.tupleEquiv hk M)

end FullTupleInterpretation

/-! ### Binary `{0, max}` tagged tuples and disjoint projection dispatch -/

section BinaryTag

/-- Build a `(d + m)`-tuple on `Fin n` from a `d`-bit `{0, max}` tag prefix and an `m`-tuple
payload. -/
def mkTagged {n d m : ℕ} [Fact (2 ≤ n)] (bs : Fin d → Bool) (payload : Fin m → Fin n) :
    Fin (d + m) → Fin n :=
  Fin.append (fun i => if bs i then QFNumeric.maxFin n else 0) payload

@[simp]
theorem mkTagged_tag {n d m : ℕ} [Fact (2 ≤ n)] (bs : Fin d → Bool) (payload : Fin m → Fin n)
    (i : Fin d) :
    mkTagged bs payload (Fin.castAdd m i) = (if bs i then QFNumeric.maxFin n else 0) :=
  Fin.append_left _ _ i

@[simp]
theorem mkTagged_payload {n d m : ℕ} [Fact (2 ≤ n)] (bs : Fin d → Bool) (payload : Fin m → Fin n)
    (j : Fin m) :
    mkTagged bs payload (Fin.natAdd d j) = payload j :=
  Fin.append_right _ _ j

/-- A tuple `u : Fin (d + m) → Fin n` carries the binary `{0, max}` tag `bs` on its first `d`
coordinates. -/
def MatchBinaryTag {n d m : ℕ} [Fact (2 ≤ n)] (bs : Fin d → Bool)
    (u : Fin (d + m) → Fin n) : Prop :=
  ∀ i : Fin d, u (Fin.castAdd m i) = (if bs i then QFNumeric.maxFin n else 0)

theorem matchBinaryTag_unique {n d m : ℕ} [Fact (2 ≤ n)] {bs₁ bs₂ : Fin d → Bool}
    {u : Fin (d + m) → Fin n} (h₁ : MatchBinaryTag bs₁ u) (h₂ : MatchBinaryTag bs₂ u) :
    bs₁ = bs₂ := by
  funext i
  have hi := (h₁ i).symm.trans (h₂ i)
  cases hb₁ : bs₁ i <;> cases hb₂ : bs₂ i
  · rfl
  · rw [hb₁, hb₂] at hi
    exact False.elim (QFNumeric.zero_ne_maxFin hi)
  · rw [hb₁, hb₂] at hi
    exact False.elim (QFNumeric.zero_ne_maxFin hi.symm)
  · rfl

@[simp]
theorem matchBinaryTag_mkTagged {n d m : ℕ} [Fact (2 ≤ n)] (bs₁ bs₂ : Fin d → Bool)
    (payload : Fin m → Fin n) :
    MatchBinaryTag bs₁ (mkTagged bs₂ payload) ↔ bs₁ = bs₂ := by
  constructor
  · intro h
    exact matchBinaryTag_unique h (fun i => mkTagged_tag bs₂ payload i)
  · rintro rfl i
    exact mkTagged_tag bs₁ payload i

theorem eq_mkTagged_of_matchBinaryTag {n d m : ℕ} [Fact (2 ≤ n)] {bs : Fin d → Bool}
    {u : Fin (d + m) → Fin n} (h : MatchBinaryTag bs u) :
    u = mkTagged bs (fun j => u (Fin.natAdd d j)) := by
  funext idx
  refine Fin.addCases (fun i => ?_) (fun j => ?_) idx
  · rw [mkTagged_tag, h i]
  · rw [mkTagged_payload]

theorem mkTagged_inj {n d m : ℕ} [Fact (2 ≤ n)] {bs₁ bs₂ : Fin d → Bool}
    {p₁ p₂ : Fin m → Fin n} :
    mkTagged bs₁ p₁ = mkTagged bs₂ p₂ ↔ bs₁ = bs₂ ∧ p₁ = p₂ := by
  constructor
  · intro h
    have hbs : bs₁ = bs₂ := (matchBinaryTag_mkTagged bs₁ bs₂ p₂).mp (h ▸ fun i =>
      mkTagged_tag bs₁ p₁ i)
    refine ⟨hbs, funext fun j => ?_⟩
    have hj := congrFun h (Fin.natAdd d j)
    rwa [mkTagged_payload, mkTagged_payload] at hj
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Quantifier-free guard in `qfNumericLanguage` testing whether tuple argument `a` has binary
`{0, max}` tag `bs` on its first `d` coordinates. -/
noncomputable def hasBinaryTag {r d : ℕ} (m : ℕ) (bs : Fin d → Bool) (a : Fin r) :
    qfNumericLanguage.Formula (Fin r × Fin (d + m)) :=
  Formula.iInf fun i : Fin d =>
    if bs i then QFNumeric.isMax (a, Fin.castAdd m i)
    else QFNumeric.isZero (a, Fin.castAdd m i)

theorem isQF_hasBinaryTag {r d : ℕ} (m : ℕ) (bs : Fin d → Bool) (a : Fin r) :
    (hasBinaryTag m bs a).IsQF := by
  refine Formula.isQF_iInf _ fun i => ?_
  split_ifs
  · exact QFNumeric.isQF_isMax _
  · exact QFNumeric.isQF_isZero _

@[simp]
theorem realize_hasBinaryTag {n r d : ℕ} [Fact (2 ≤ n)] (m : ℕ) (bs : Fin d → Bool) (a : Fin r)
    (x : Fin r × Fin (d + m) → Fin n) :
    (hasBinaryTag m bs a).Realize x ↔ MatchBinaryTag bs (fun j => x (a, j)) := by
  rw [hasBinaryTag, Formula.realize_iInf]
  refine forall_congr' fun i => ?_
  cases hbi : bs i
  · simp
  · simp

/-- Disjoint unary dispatch on the binary `{0, max}` tag of tuple argument `a : Fin r`. -/
noncomputable def dispatchBinaryTag {L : Language} {T : Type*} {r d m : ℕ}
    (a : Fin r) (code : T → Fin d → Bool) (tags : List T)
    (body : T → ProjectionFormula qfNumericLanguage L (Fin r × Fin (d + m)))
    (fallback : ProjectionFormula qfNumericLanguage L (Fin r × Fin (d + m))) :
    ProjectionFormula qfNumericLanguage L (Fin r × Fin (d + m)) :=
  tags.foldr (fun t acc => .branch (hasBinaryTag m (code t) a) (body t) acc) fallback

theorem isQF_dispatchBinaryTag {L : Language} {T : Type*} {r d m : ℕ}
    (a : Fin r) (code : T → Fin d → Bool) (tags : List T)
    {body : T → ProjectionFormula qfNumericLanguage L (Fin r × Fin (d + m))}
    {fallback : ProjectionFormula qfNumericLanguage L (Fin r × Fin (d + m))}
    (hbody : ∀ t ∈ tags, (body t).IsQF) (hfb : fallback.IsQF) :
    (dispatchBinaryTag a code tags body fallback).IsQF := by
  induction tags with
  | nil => exact hfb
  | cons t ts ih =>
    exact ⟨isQF_hasBinaryTag m (code t) a, hbody t List.mem_cons_self,
      ih (fun t' ht' => hbody t' (List.mem_cons_of_mem t ht'))⟩

theorem realize_dispatchBinaryTag {L : Language} {T : Type*} {n r d m : ℕ}
    [Fact (2 ≤ n)] [L.Structure (Fin n)]
    (a : Fin r) {code : T → Fin d → Bool} (hcode : Function.Injective code) (tags : List T)
    (body : T → ProjectionFormula qfNumericLanguage L (Fin r × Fin (d + m)))
    (fallback : ProjectionFormula qfNumericLanguage L (Fin r × Fin (d + m)))
    (x : Fin r × Fin (d + m) → Fin n) :
    (dispatchBinaryTag a code tags body fallback).toFormula.Realize x ↔
      (∃ t ∈ tags, MatchBinaryTag (code t) (fun j => x (a, j)) ∧
        (body t).toFormula.Realize x) ∨
      ((∀ t ∈ tags, ¬ MatchBinaryTag (code t) (fun j => x (a, j))) ∧
        fallback.toFormula.Realize x) := by
  induction tags with
  | nil => simp [dispatchBinaryTag]
  | cons t ts ih =>
    simp only [dispatchBinaryTag, List.foldr_cons, ProjectionFormula.realize_toFormula_branch,
      realize_hasBinaryTag]
    change (MatchBinaryTag (code t) (fun j => x (a, j)) ∧ (body t).toFormula.Realize x ∨
        ¬ MatchBinaryTag (code t) (fun j => x (a, j)) ∧
          (dispatchBinaryTag a code ts body fallback).toFormula.Realize x) ↔ _
    rw [ih]
    constructor
    · rintro (⟨hm, hb⟩ | ⟨hnm, ⟨t', ht', hm', hb'⟩ | ⟨hall, hfb⟩⟩)
      · exact Or.inl ⟨t, List.mem_cons_self, hm, hb⟩
      · exact Or.inl ⟨t', List.mem_cons_of_mem t ht', hm', hb'⟩
      · refine Or.inr ⟨fun t' ht' => ?_, hfb⟩
        rcases List.mem_cons.mp ht' with rfl | ht'
        · exact hnm
        · exact hall t' ht'
    · rintro (⟨t', ht', hm', hb'⟩ | ⟨hall, hfb⟩)
      · rcases List.mem_cons.mp ht' with rfl | ht'
        · exact Or.inl ⟨hm', hb'⟩
        · by_cases hm : MatchBinaryTag (code t) (fun j => x (a, j))
          · have heq : t = t' := hcode (matchBinaryTag_unique hm hm')
            subst heq
            exact Or.inl ⟨hm, hb'⟩
          · exact Or.inr ⟨hm, Or.inl ⟨t', ht', hm', hb'⟩⟩
      · exact Or.inr ⟨hall t List.mem_cons_self,
          Or.inr ⟨fun t' ht' => hall t' (List.mem_cons_of_mem t ht'), hfb⟩⟩

/-- Swap the two tuple indices in `Fin 2 × Fin k`. -/
def swapPairArg {k : ℕ} : Fin 2 × Fin k → Fin 2 × Fin k
  | ⟨0, j⟩ => ⟨1, j⟩
  | ⟨1, j⟩ => ⟨0, j⟩

private theorem pair_comp_swapPairArg {α : Type*} {k : ℕ} (u v : Fin k → α) :
    ((fun p : Fin 2 × Fin k => (![u, v] p.1) p.2) ∘ swapPairArg) =
      fun p : Fin 2 × Fin k => (![v, u] p.1) p.2 := by
  funext ⟨a, j⟩
  cases a using Fin.cases with
  | zero => rfl
  | succ a' =>
    have ha : a' = 0 := Subsingleton.elim _ _
    subst ha
    rfl

/-- Symmetric loopless binary-relation dispatch over pairs of tags from `tags`, symmetrizing an
asymmetric upper-triangular edge specification `upper`. -/
noncomputable def symmPairBinaryTag {L : Language} {T : Type*} {d m : ℕ}
    (code : T → Fin d → Bool) (tags : List T)
    (upper : T → T → Option (ProjectionFormula qfNumericLanguage L (Fin 2 × Fin (d + m)))) :
    ProjectionFormula qfNumericLanguage L (Fin 2 × Fin (d + m)) :=
  dispatchBinaryTag 0 code tags
    (fun t₁ => dispatchBinaryTag 1 code tags
      (fun t₂ =>
        match upper t₁ t₂ with
        | some p => p
        | none =>
          match upper t₂ t₁ with
          | some p => p.relabel swapPairArg
          | none => .const false)
      (.const false))
    (.const false)

theorem isQF_symmPairBinaryTag {L : Language} {T : Type*} {d m : ℕ}
    (code : T → Fin d → Bool) (tags : List T)
    {upper : T → T → Option (ProjectionFormula qfNumericLanguage L (Fin 2 × Fin (d + m)))}
    (hupper : ∀ t₁ t₂ p, upper t₁ t₂ = some p → p.IsQF) :
    (symmPairBinaryTag code tags upper).IsQF := by
  refine isQF_dispatchBinaryTag 0 code tags (fun t₁ _ => ?_) (ProjectionFormula.isQF_const false)
  refine isQF_dispatchBinaryTag 1 code tags (fun t₂ _ => ?_) (ProjectionFormula.isQF_const false)
  cases h12 : upper t₁ t₂ with
  | some p => exact hupper t₁ t₂ p h12
  | none =>
    cases h21 : upper t₂ t₁ with
    | some p => exact (hupper t₂ t₁ p h21).relabel swapPairArg
    | none => exact ProjectionFormula.isQF_const false

/-- Directed edge specified by `upper` on binary-tagged tuples `(u, v)`. -/
@[expose] def UpperTagEdge {L : Language} {T : Type*} {n d m : ℕ} [Fact (2 ≤ n)]
    [L.Structure (Fin n)]
    (code : T → Fin d → Bool) (tags : List T)
    (upper : T → T → Option (ProjectionFormula qfNumericLanguage L (Fin 2 × Fin (d + m))))
    (u v : Fin (d + m) → Fin n) : Prop :=
  ∃ t₁ ∈ tags, ∃ t₂ ∈ tags,
    MatchBinaryTag (code t₁) u ∧ MatchBinaryTag (code t₂) v ∧
      ∃ p, upper t₁ t₂ = some p ∧
        p.toFormula.Realize (fun q : Fin 2 × Fin (d + m) => (![u, v] q.1) q.2)

theorem realize_symmPairBinaryTag {L : Language} {T : Type*} {n d m : ℕ}
    [Fact (2 ≤ n)] [L.Structure (Fin n)]
    {code : T → Fin d → Bool} (hcode : Function.Injective code) (tags : List T)
    {upper : T → T → Option (ProjectionFormula qfNumericLanguage L (Fin 2 × Fin (d + m)))}
    (hasym : ∀ t₁ t₂ p, upper t₁ t₂ = some p → upper t₂ t₁ = none)
    (u v : Fin (d + m) → Fin n) :
    (symmPairBinaryTag code tags upper).toFormula.Realize
        (fun q : Fin 2 × Fin (d + m) => (![u, v] q.1) q.2) ↔
      UpperTagEdge code tags upper u v ∨ UpperTagEdge code tags upper v u := by
  let x : Fin 2 × Fin (d + m) → Fin n := fun q => (![u, v] q.1) q.2
  have hx0 : (fun j => x (0, j)) = u := rfl
  have hx1 : (fun j => x (1, j)) = v := rfl
  rw [symmPairBinaryTag, realize_dispatchBinaryTag 0 hcode tags _ _ x]
  simp only [hx0, ProjectionFormula.realize_const_false, and_false, or_false]
  constructor
  · rintro ⟨t₁, ht₁, hm₁, hinner⟩
    rw [realize_dispatchBinaryTag 1 hcode tags _ _ x] at hinner
    simp only [hx1, ProjectionFormula.realize_const_false, and_false, or_false] at hinner
    obtain ⟨t₂, ht₂, hm₂, hleaf⟩ := hinner
    cases h12 : upper t₁ t₂ with
    | some p =>
      rw [h12] at hleaf
      exact Or.inl ⟨t₁, ht₁, t₂, ht₂, hm₁, hm₂, p, h12, hleaf⟩
    | none =>
      rw [h12] at hleaf
      cases h21 : upper t₂ t₁ with
      | some p =>
        rw [h21, ProjectionFormula.realize_relabel, pair_comp_swapPairArg] at hleaf
        exact Or.inr ⟨t₂, ht₂, t₁, ht₁, hm₂, hm₁, p, h21, hleaf⟩
      | none =>
        rw [h21] at hleaf
        exact False.elim (ProjectionFormula.realize_const_false _ hleaf)
  · rintro (⟨t₁, ht₁, t₂, ht₂, hm₁, hm₂, p, h12, hp⟩ | ⟨t₂, ht₂, t₁, ht₁, hm₂, hm₁, p, h21, hp⟩)
    · refine ⟨t₁, ht₁, hm₁, ?_⟩
      rw [realize_dispatchBinaryTag 1 hcode tags _ _ x]
      refine Or.inl ⟨t₂, ht₂, hm₂, ?_⟩
      rw [h12]
      exact hp
    · refine ⟨t₁, ht₁, hm₁, ?_⟩
      rw [realize_dispatchBinaryTag 1 hcode tags _ _ x]
      refine Or.inl ⟨t₂, ht₂, hm₂, ?_⟩
      rw [hasym t₂ t₁ p h21, h21, ProjectionFormula.realize_relabel, pair_comp_swapPairArg]
      exact hp

theorem irrefl_symmPairBinaryTag {L : Language} {T : Type*} {n d m : ℕ}
    [Fact (2 ≤ n)] [L.Structure (Fin n)]
    {code : T → Fin d → Bool} (hcode : Function.Injective code) (tags : List T)
    {upper : T → T → Option (ProjectionFormula qfNumericLanguage L (Fin 2 × Fin (d + m)))}
    (hasym : ∀ t₁ t₂ p, upper t₁ t₂ = some p → upper t₂ t₁ = none)
    (u : Fin (d + m) → Fin n) :
    ¬ (symmPairBinaryTag code tags upper).toFormula.Realize
        (fun q : Fin 2 × Fin (d + m) => (![u, u] q.1) q.2) := by
  rw [realize_symmPairBinaryTag hcode tags hasym u u]
  rintro (⟨t₁, _, t₂, _, hm₁, hm₂, p, h12, -⟩ | ⟨t₁, _, t₂, _, hm₁, hm₂, p, h12, -⟩) <;>
  · have heq : t₁ = t₂ := hcode (matchBinaryTag_unique hm₁ hm₂)
    subst heq
    have hnone := hasym t₁ t₁ p h12
    rw [h12] at hnone
    cases hnone

theorem symm_symmPairBinaryTag {L : Language} {T : Type*} {n d m : ℕ}
    [Fact (2 ≤ n)] [L.Structure (Fin n)]
    {code : T → Fin d → Bool} (hcode : Function.Injective code) (tags : List T)
    {upper : T → T → Option (ProjectionFormula qfNumericLanguage L (Fin 2 × Fin (d + m)))}
    (hasym : ∀ t₁ t₂ p, upper t₁ t₂ = some p → upper t₂ t₁ = none)
    {u v : Fin (d + m) → Fin n}
    (h : (symmPairBinaryTag code tags upper).toFormula.Realize
      (fun q : Fin 2 × Fin (d + m) => (![u, v] q.1) q.2)) :
    (symmPairBinaryTag code tags upper).toFormula.Realize
      (fun q : Fin 2 × Fin (d + m) => (![v, u] q.1) q.2) := by
  rw [realize_symmPairBinaryTag hcode tags hasym] at h ⊢
  exact h.symm

end BinaryTag

end Ordered

end Cslib.Logic.FO
