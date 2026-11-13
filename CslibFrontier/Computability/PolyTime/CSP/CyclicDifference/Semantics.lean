/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.CyclicDifference.FaceParity
public import CslibFrontier.Computability.PolyTime.CSP.CyclicDifference.WhiteChains
import Mathlib.Data.List.GetD

/-!
# Semantic correctness of the actual difference compiler

The source predicate keeps well-formedness, the supplied checked ordered numerical rotation,
and original CSP satisfiability. Vertex spins are obtained from the reviewed numerical lifting
theorem on the actual polygon graph. Nullaries are handled internally without changing source
indices, and no translation, geometric realization, solver or inverse-table oracle is supplied.
-/

public section

namespace Cslib.Complexity.CSP.CyclicCompiler

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Table Cslib.BitString
open Graph.RotationCertificate Graph.RotationSystem

variable {Rel : Type} {F : CSP Rel ℕ}

/-- Evaluation of the actual indexed black-constraint list. -/
theorem eval_blackConstraints_iff (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (σ : ℕ → Bool) :
    (blackConstraints arity sem F).eval Table.sem σ = true ↔
      ∀ i : Fin F.length, 0 < F[i.val].scope.length →
        (differenceTable arity sem F[i.val].rel).sem
          ((blackScope F i F[i.val].scope).map σ) = true := by
  simp only [CSP.eval, List.all_eq_true]
  constructor
  · intro h i hipos
    apply h ⟨differenceTable arity sem F[i.val].rel, blackScope F i F[i.val].scope⟩
    apply List.mem_map.mpr
    refine ⟨(F[i.val], i.val), List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · apply List.mem_zipIdx_iff_getElem?.mpr
      exact List.getElem?_eq_getElem i.isLt
    · simpa only [Bool.not_eq_true', List.isEmpty_eq_false_iff] using
        (List.ne_nil_of_length_pos hipos)
  · intro h constraint hc
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hc
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp
      (List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hentry).1)
    have hpos : 0 < F[entry.2].scope.length := by
      rw [he]
      exact List.length_pos_iff.mpr (by
        simpa only [Bool.not_eq_true', List.isEmpty_eq_false_iff] using
          (List.mem_filter.mp hentry).2)
    have hh := h ⟨entry.2, hi⟩ hpos
    simpa only [he, Constraint.eval] using hh

/-- Original variable spins read in the actual scope order. -/
@[expose] def spinTuple (F : CSP Rel ℕ) (spin : ℕ → Bool) (i : Fin F.length) :
    Fin F[i.val].scope.length → Bool :=
  fun j => spin (F.distinctVars.idxOf (Occurrence.var (F := F) ⟨i, j⟩))

/-- Local gradient tuples are exactly ordered cyclic differences, even with repeated names. -/
theorem gradient_blackScope (spin σ : ℕ → Bool)
    (he : ∀ o : F.Occurrence, σ (incidenceEdgeIndex o) =
      (polygonGraph F).edgeGradient spin (polygonDart o false).1) (i : Fin F.length) :
    (blackScope F i F[i.val].scope).map σ = List.ofFn (cyclicDifference (spinTuple F spin i)) := by
  rw [blackScope_eq_ofFn, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  rw [Function.comp_apply, he]
  change (spin (polygonDart (F := F) ⟨i, j⟩ false).vertex ^^
    spin (polygonDart (F := F) ⟨i, j⟩ true).vertex) = _
  simp only [vertex_polygonDart, Bool.false_eq_true, ↓reduceIte, spinTuple, cyclicDifference]
  rfl

/-- A true canonical nullary relation accepts the empty row. Nonemptiness suffices because
there is only one tuple of arity zero. -/
theorem sem_nullary_of_nonempty (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (r : Rel) (hwidth : arity r = 0) (hne : (booleanRelation arity sem r).Nonempty) :
    sem r [] = true := by
  obtain ⟨x, hx⟩ := hne
  change sem r (List.ofFn x) = true at hx
  have hnil : List.ofFn x = [] := List.length_eq_zero_iff.mp (by simp [hwidth])
  rwa [hnil] at hx

/-- A black-and-expanded-white satisfying assignment is face-even on the actual polygon. -/
theorem faceEven_of_body (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (cert : Graph.RotationCertificate) (h : verifyRotation (incidenceGraph F) cert = true)
    (σ : ℕ → Bool) (hsat : (body arity sem F cert).eval Table.sem σ = true) :
    (polygonRotation (decode _ cert h)).FaceEven (fun i => σ i.val) := by
  have hh : (blackConstraints arity sem F).eval Table.sem σ = true ∧
      (whiteConstraints F.occurrences.length (whiteScopes F cert)).eval Table.sem σ = true := by
    simpa only [body, CSP.eval, List.all_append, Bool.and_eq_true] using hsat
  obtain ⟨hb, hw⟩ := hh
  apply (faceEven_iff_dart _ _).mpr
  intro d
  obtain ⟨o, ho⟩ := exists_polygonDart d
  cases hd : d.2
  · rw [hd] at ho
    rw [← ho, faceParity_black]
    exact parity_differenceTable arity sem _ _
      ((eval_blackConstraints_iff arity sem σ).mp hb o.1 (Nat.zero_lt_of_lt o.2.isLt))
  · rw [hd] at ho
    rw [← ho, faceParity_white cert h]
    obtain ⟨p, hp, hr⟩ := exists_whiteRep cert h o
    rw [whiteScope_eq_of_sameCycle cert h o p hp]
    apply whiteConstraints_sound _ _ σ hw
    apply List.mem_map.mpr
    refine ⟨incidenceEdgeIndex p, List.mem_filter.mpr ⟨?_, hr⟩, rfl⟩
    exact List.mem_range.mpr (by
      simpa only [incidenceGraph_edges, List.length_map] using incidenceEdgeIndex_lt p)

/-- Scope tuples agree with the original CSP evaluator after dense spin reconstruction. -/
theorem ofFn_spinTuple (spin : ℕ → Bool) (i : Fin F.length) :
    List.ofFn (spinTuple F spin i) =
      F[i.val].scope.map (fun v => spin (F.distinctVars.idxOf v)) := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp only [List.getElem_ofFn, List.getElem_map, spinTuple, Occurrence.var]

/-- Accepted expanded output lifts back to the original source under its checked rotation.
Empty occurring relations are excluded by the actual compiler guard, including false nullaries. -/
theorem satisfiable_source_of_body (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (hself : ∀ r, IsSelfComplementary (booleanRelation arity sem r))
    (cert : Graph.RotationCertificate) (hwell : WellFormed arity F)
    (hcert : verifyRotationCertificate F cert = true)
    (hnonempty : ∀ c ∈ F, nonemptySymbol arity sem c.rel = true)
    (hsat : (body arity sem F cert).Satisfiable Table.sem) : F.Satisfiable sem := by
  obtain ⟨h, hgenus, horder⟩ := (verifyRotationCertificate_eq_true_iff F cert).mp hcert
  obtain ⟨σ, hσ⟩ := hsat
  have hface := faceEven_of_body arity sem cert h σ hσ
  obtain ⟨spin, hspin⟩ := (faceEven_iff_exists_vertexSpins
    (polygonRotation (decode _ cert h)) polygon_endpoints_declared
      (numericalGenusZero_polygon_with_nullaries _ horder hgenus) _).mp hface
  have he (o : F.Occurrence) : σ (incidenceEdgeIndex o) =
      (polygonGraph F).edgeGradient spin (polygonDart o false).1 :=
    (congrFun hspin (polygonDart o false).1).symm
  have hb : (blackConstraints arity sem F).eval Table.sem σ = true := by
    have hh : (blackConstraints arity sem F).eval Table.sem σ = true ∧
        (whiteConstraints F.occurrences.length (whiteScopes F cert)).eval Table.sem σ = true := by
      simpa only [body, CSP.eval, List.all_append, Bool.and_eq_true] using hσ
    exact hh.1
  refine ⟨fun v => spin (F.distinctVars.idxOf v), List.all_eq_true.mpr ?_⟩
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  have hwidth := hwell F[i] (List.getElem_mem hi)
  change sem F[i].rel (F[i].scope.map (fun v => spin (F.distinctVars.idxOf v))) = true
  by_cases hpos : 0 < F[i].scope.length
  · have ht := (eval_blackConstraints_iff arity sem σ).mp hb ⟨i, hi⟩ hpos
    rw [gradient_blackScope spin σ he] at ht
    have hs := (sem_differenceTable_cyclicDifference arity sem F[i].rel
      (hself _) hwidth (spinTuple F spin ⟨i, hi⟩)).mp ht
    rwa [ofFn_spinTuple] at hs
  · have hnil : F[i].scope = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hnil, List.map_nil]
    exact sem_nullary_of_nonempty arity sem F[i].rel
      (by rw [hnil] at hwidth; simpa using hwidth.symm)
      ((nonemptySymbol_eq_true_iff arity sem _).mp (hnonempty F[i] (List.getElem_mem hi)))

/-- Every source solution gives a solution of the actual expanded body. Difference tables are
static; white parity follows from telescoping on the actual polygon rotation. -/
theorem satisfiable_body_of_source (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (hself : ∀ r, IsSelfComplementary (booleanRelation arity sem r))
    (cert : Graph.RotationCertificate) (hwell : WellFormed arity F)
    (hcert : verifyRotationCertificate F cert = true) (hsat : F.Satisfiable sem) :
    (body arity sem F cert).Satisfiable Table.sem := by
  obtain ⟨h, _, _⟩ := (verifyRotationCertificate_eq_true_iff F cert).mp hcert
  obtain ⟨source, hsource⟩ := hsat
  let spin (v : ℕ) := source (F.distinctVars.getD v 0)
  let σ (n : ℕ) := (List.ofFn ((polygonGraph F).edgeGradient spin)).getD n false
  have hspin (o : F.Occurrence) : spin (F.distinctVars.idxOf o.var) = source o.var := by
    unfold spin
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr o.var_mem)),
      List.getElem_idxOf (List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr o.var_mem))]
  have hσ (i : Fin (polygonGraph F).2.length) : σ i.val = (polygonGraph F).edgeGradient spin i := by
    unfold σ
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
    simp only [List.getElem_ofFn]
  have he (o : F.Occurrence) : σ (incidenceEdgeIndex o) =
      (polygonGraph F).edgeGradient spin (polygonDart o false).1 := hσ (polygonDart o false).1
  have hb : (blackConstraints arity sem F).eval Table.sem σ = true := by
    apply (eval_blackConstraints_iff arity sem σ).mpr
    intro i _
    rw [gradient_blackScope spin σ he]
    apply (sem_differenceTable_cyclicDifference arity sem F[i.val].rel (hself _)
      (hwell F[i.val] (List.getElem_mem i.isLt)) _).mpr
    have hrow : List.ofFn (spinTuple F spin i) = F[i.val].scope.map source := by
      apply List.ext_getElem
      · simp
      · intro j hj hk
        simp only [List.getElem_ofFn, List.getElem_map, spinTuple]
        exact hspin ⟨i, ⟨j, by simpa only [List.length_map] using hk⟩⟩
    rw [hrow]
    exact List.all_eq_true.mp hsource F[i.val] (List.getElem_mem i.isLt)
  have hparity : ∀ scope ∈ whiteScopes F cert, wordParity (scope.map σ) = false := by
    intro scope hs
    obtain ⟨edge, he, rfl⟩ := List.mem_map.mp hs
    have hlt := List.mem_range.mp (List.mem_filter.mp he).1
    obtain ⟨o, ho⟩ := exists_incidenceEdgeIndex (F := F) edge (by
      simpa only [incidenceGraph_edges, List.length_map] using hlt)
    have hface := (polygonRotation (decode _ cert h)).faceEven_edgeGradient spin
      (Quotient.mk _ (polygonDart o true))
    have heq : (fun i : Fin (polygonGraph F).2.length => σ i.val) =
        (polygonGraph F).edgeGradient spin := funext hσ
    rw [← heq, faceParity_white cert h] at hface
    simpa only [ho] using hface
  have hbound : ∀ scope ∈ whiteScopes F cert, ∀ v ∈ scope, v < F.occurrences.length := by
    intro scope hs
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hs
    exact (whiteScope_bounds F cert edge).2.2
  obtain ⟨τ, hτ, hw⟩ := whiteConstraints_complete F.occurrences.length (whiteScopes F cert)
    σ hbound hparity
  have hbτ : (blackConstraints arity sem F).eval Table.sem τ = true := by
    apply (eval_blackConstraints_iff arity sem τ).mpr
    intro i hpos
    have hrow : (blackScope F i F[i.val].scope).map τ = (blackScope F i F[i.val].scope).map σ :=
      List.map_congr_left (fun v hv => hτ v ((blackScope_bounds i).2 v hv))
    rw [hrow]
    exact (eval_blackConstraints_iff arity sem σ).mp hb i hpos
  refine ⟨τ, ?_⟩
  simpa only [body, CSP.eval, List.all_append, Bool.and_eq_true] using And.intro hbτ hw

/-- Satisfying well-formed source instances pass the occurring-relation nonemptiness guard.
This includes true nullaries, and does not require every language symbol to be nonempty. -/
theorem nonemptySymbol_of_satisfiable (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (hwell : WellFormed arity F) (hsat : F.Satisfiable sem) :
    ∀ c ∈ F, nonemptySymbol arity sem c.rel = true := by
  obtain ⟨σ, hσ⟩ := hsat
  intro c hc
  have hm : c.scope.map σ ∈ sourceRows arity sem c.rel := by
    apply List.mem_filter.mpr
    exact ⟨mem_enumList.mpr (by simpa only [List.length_map] using hwell c hc),
      List.all_eq_true.mp hσ c hc⟩
  have hn : sourceRows arity sem c.rel ≠ [] := by
    intro he
    rw [he] at hm
    contradiction
  simpa only [nonemptySymbol, Bool.not_eq_true', List.isEmpty_eq_false_iff] using hn

/-- Full guarded semantic correctness on the original CSP and supplied certificate.
The only language assumption is simultaneous self-complementarity. All graph translation,
nullary, face-lifting and parity-chain obligations are discharged internally. -/
theorem satisfiable_compile_iff (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (hself : ∀ r, IsSelfComplementary (booleanRelation arity sem r))
    (input : CSP Rel ℕ × Graph.RotationCertificate) :
    (compile arity sem input).Satisfiable Table.sem ↔
      WellFormed arity input.1 ∧ verifyRotationCertificate input.1 input.2 = true ∧
        input.1.Satisfiable sem := by
  by_cases hg : (validArity arity input.1 && verifyRotationCertificate input.1 input.2 &&
      input.1.all (fun c => nonemptySymbol arity sem c.rel)) = true
  · have hp : (WellFormed arity input.1 ∧ verifyRotationCertificate input.1 input.2 = true) ∧
        (∀ c ∈ input.1, nonemptySymbol arity sem c.rel = true) := by
      simpa only [Bool.and_eq_true, validArity_eq_true_iff, List.all_eq_true] using hg
    rw [compile, ite_eq_left hg]
    constructor
    · intro hs
      exact ⟨hp.1.1, hp.1.2,
        satisfiable_source_of_body arity sem hself input.2 hp.1.1 hp.1.2 hp.2 hs⟩
    · rintro ⟨hw, hc, hs⟩
      exact satisfiable_body_of_source arity sem hself input.2 hw hc hs
  · rw [compile, ite_eq_right hg]
    constructor
    · exact fun hs => (not_satisfiable_rejectEdge hs).elim
    · rintro ⟨hw, hc, hs⟩
      apply (hg ?_).elim
      simp only [Bool.and_eq_true, validArity_eq_true_iff, List.all_eq_true]
      exact ⟨⟨hw, hc⟩, nonemptySymbol_of_satisfiable arity sem hw hs⟩

end Cslib.Complexity.CSP.CyclicCompiler
