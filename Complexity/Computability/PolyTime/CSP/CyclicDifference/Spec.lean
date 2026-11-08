/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.CyclicDifference.Native
public import Complexity.Computability.PolyTime.CSP.CyclicDifference.Semantics
public import Complexity.Computability.PolyTime.CSP.CyclicDifference.BlackCounts
public import Complexity.Logics.Propositional.CSP.Edge.Defects

/-!
# Checked native cyclic-difference compiler specification

For each fixed finite Boolean language, the actual total compiler takes the original CSP and
a supplied checked ordered numerical genus-zero rotation. In the self-complementary language
branch with nonempty difference relations even delta-matroids, it outputs an explicit-table
EDGE CSP over the existing infinite `CSP.Table` alphabet. Every output is well formed and every
constraint is a nonempty even delta-matroid, including rejected raw inputs. Source indices stay
binary; all construction loops traverse actual lists. Static language preprocessing may depend
exponentially on fixed arity, as in Schaefer's fixed-language convention.

This numerical supplied-certificate stage implements the forward difference construction of
[DvorakKupec2015], Section 3, Lemma 5/Corollary 4/Theorem 2, printed pp. 439–440, with the edge
convention of [KazdaKolmogorovRolinek2018], v6, Definition 3 (printed p. 0:3). The parity-chain
implementation is original. There is no geometric realization claim, bare rotation recognizer,
edge solver assumption or full planar dichotomy claim.

## Main results

* `Cslib.Complexity.CSP.CyclicCompiler.compile_correct`: full guarded semantic/edge/evenness result.
* `Cslib.Complexity.CSP.CyclicCompiler.compile_spec`: combined ordinary native endpoint.
-/

public section

namespace Cslib.Complexity.CSP.CyclicCompiler

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Table Cslib.BitString
open Graph.RotationCertificate Graph.RotationSystem Turing.MultiTapeTM

variable {Rel : Type} {F : CSP Rel ℕ}

/-- Dense edge and auxiliary names have exactly two output occurrences. The auxiliary block
starts at the original occurrence count and has its actual prefix-sum length. -/
theorem count_vars_body (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (cert : Graph.RotationCertificate) (h : verifyRotation (incidenceGraph F) cert = true)
    (v : ℕ) :
    (body arity sem F cert).vars.count v =
      if v < F.occurrences.length +
        auxiliaryPrefix (whiteScopes F cert) (whiteScopes F cert).length then 2 else 0 := by
  have hcount : (body arity sem F cert).vars.count v =
      (if v < F.occurrences.length then 1 else 0) +
      ((if v < F.occurrences.length then 1 else 0) +
        if F.occurrences.length ≤ v ∧ v < F.occurrences.length +
          auxiliaryPrefix (whiteScopes F cert) (whiteScopes F cert).length then 2 else 0) := by
    unfold body
    simp only [CSP.vars, List.flatMap_append, List.count_append]
    change (blackConstraints arity sem F).vars.count v +
      (whiteConstraints F.occurrences.length (whiteScopes F cert)).vars.count v = _
    rw [count_vars_blackConstraints, count_vars_whiteConstraints, count_flatten_whiteScopes cert h]
  split_ifs at hcount ⊢ <;> omega

/-- Actual black and expanded-white scopes meet the positional edge convention. This uses
only the checked original rotation, with no positivity or semantic assumption. -/
theorem edgeInstance_body (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (cert : Graph.RotationCertificate) (h : verifyRotation (incidenceGraph F) cert = true) :
    EdgeInstance (body arity sem F cert) := by
  have hbound : ∀ scope ∈ whiteScopes F cert, ∀ v ∈ scope, v < F.occurrences.length := by
    intro scope hs
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hs
    exact (whiteScope_bounds F cert edge).2.2
  have hnd : ∀ scope ∈ whiteScopes F cert, scope.Nodup := by
    intro scope hs
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hs
    exact (whiteScope_bounds F cert edge).1
  apply edgeInstance_of_count_eq_two
  · intro constraint hc
    rcases List.mem_append.mp hc with hc | hc
    · exact blackConstraints_scopes_nodup arity sem F constraint hc
    · exact whiteConstraints_scopes_nodup _ _ hnd hbound constraint hc
  · intro v hv
    have hcount := count_vars_body arity sem cert h v
    have hpos := List.count_pos_iff.mpr hv
    split_ifs at hcount <;> omega

/-- All-raw edge guarantee of the total compiler, including rejection. -/
theorem edgeInstance_compile (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (input : CSP Rel ℕ × Graph.RotationCertificate) : EdgeInstance (compile arity sem input) := by
  unfold compile
  split_ifs with hg
  · have hp : (validArity arity input.1 = true ∧
        verifyRotationCertificate input.1 input.2 = true) ∧
        input.1.all (fun c => nonemptySymbol arity sem c.1) = true := by
      simpa only [Bool.and_eq_true] using hg
    obtain ⟨h, _, _⟩ := (verifyRotationCertificate_eq_true_iff input.1 input.2).mp hp.1.2
    exact edgeInstance_body arity sem input.2 h
  · exact edgeInstance_rejectEdge

/-- Widths and actual explicit-table relations of the guarded body. Empty symbols need not
satisfy the static delta-matroid condition; their occurring constraints are rejected first. -/
theorem body_tables (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (hdelta : ∀ r, (booleanRelation arity sem r).Nonempty →
      IsEvenDeltaMatroid (cyclicDifferenceRelation (booleanRelation arity sem r)))
    (cert : Graph.RotationCertificate) (hwell : WellFormed arity F)
    (hne : ∀ c ∈ F, nonemptySymbol arity sem c.1 = true)
    (constraint : Constraint Table ℕ) (hc : constraint ∈ body arity sem F cert) :
    constraint.1.arity = constraint.2.length ∧
      IsEvenDeltaMatroid (booleanRelation Table.arity Table.sem constraint.1) := by
  rcases List.mem_append.mp hc with hb | hw
  · obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hb
    have hsrc : entry.1 ∈ F := List.fst_mem_of_mem_zipIdx (List.mem_filter.mp he).1
    refine ⟨?_, isEvenDeltaMatroid_differenceTable arity sem entry.1.1
      (hdelta _ ((nonemptySymbol_eq_true_iff arity sem _).mp (hne entry.1 hsrc)))⟩
    simp only [arity_differenceTable, blackScope, List.length_map, List.length_range]
    exact (hwell entry.1 hsrc).symm
  · obtain ⟨entry, _, hentry⟩ := List.mem_flatMap.mp hw
    exact ⟨(parityChain_tables _ _ constraint hentry).1,
      (parityChain_tables _ _ constraint hentry).2.2⟩

/-- Actual even delta-matroid constraints and matching table/scope widths on every raw input. -/
theorem compile_tables (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (hdelta : ∀ r, (booleanRelation arity sem r).Nonempty →
      IsEvenDeltaMatroid (cyclicDifferenceRelation (booleanRelation arity sem r)))
    (input : CSP Rel ℕ × Graph.RotationCertificate) :
    ∀ constraint ∈ compile arity sem input,
      constraint.1.arity = constraint.2.length ∧
        IsEvenDeltaMatroid (booleanRelation Table.arity Table.sem constraint.1) := by
  unfold compile
  split_ifs with hg
  · have hp : (WellFormed arity input.1 ∧ verifyRotationCertificate input.1 input.2 = true) ∧
        (∀ c ∈ input.1, nonemptySymbol arity sem c.1 = true) := by
      simpa only [Bool.and_eq_true, validArity_eq_true_iff, List.all_eq_true] using hg
    exact body_tables arity sem hdelta input.2 hp.1.1 hp.2
  · intro constraint hc
    exact ⟨(wellFormed_rejectEdge constraint hc).symm, rejectEdge_tables constraint hc⟩

/-- Every emitted explicit row has the declared width. Together with `compile_tables`, this
also gives exact actual scope widths; no malformed table is used as a rejection shortcut. -/
theorem tableWellFormed_compile (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (hdelta : ∀ r, (booleanRelation arity sem r).Nonempty →
      IsEvenDeltaMatroid (cyclicDifferenceRelation (booleanRelation arity sem r)))
    (input : CSP Rel ℕ × Graph.RotationCertificate)
    (constraint : Constraint Table ℕ) (hc : constraint ∈ compile arity sem input) :
    constraint.1.wellFormed = true := by
  obtain ⟨x, hx⟩ := (compile_tables arity sem hdelta input constraint hc).2.isDeltaMatroid.nonempty
  exact (Table.sem_eq_true.mp hx).1

/-- Full guarded correctness of the actual total compiler on the original CSP/certificate.
All translation, graph, lifting, nullary and expansion ingredients are proved internally. -/
theorem compile_correct (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (hself : ∀ r, IsSelfComplementary (booleanRelation arity sem r))
    (hdelta : ∀ r, (booleanRelation arity sem r).Nonempty →
      IsEvenDeltaMatroid (cyclicDifferenceRelation (booleanRelation arity sem r)))
    (input : CSP Rel ℕ × Graph.RotationCertificate) :
    EdgeInstance (compile arity sem input) ∧ WellFormed Table.arity (compile arity sem input) ∧
      EdgeInstance.EvenConstraints Table.sem (compile arity sem input) ∧
      ((WellFormed arity input.1 ∧ verifyRotationCertificate input.1 input.2 = true ∧
        input.1.Satisfiable sem) ↔ (compile arity sem input).Satisfiable Table.sem) := by
  have ht := compile_tables arity sem hdelta input
  refine ⟨edgeInstance_compile arity sem input, fun c hc => (ht c hc).1.symm, ?_,
    (satisfiable_compile_iff arity sem hself input).symm⟩
  intro i
  have hw := (ht _ (List.getElem_mem i.isLt)).1
  have hm := (ht _ (List.getElem_mem i.isLt)).2
  change IsEvenDeltaMatroid {t : Fin (compile arity sem input)[i.val].1.arity → Bool |
    Table.sem (compile arity sem input)[i.val].1 (List.ofFn t) = true} at hm
  have htransport (n : ℕ) (hn : (compile arity sem input)[i.val].1.arity = n) :
      IsEvenDeltaMatroid {t : Fin n → Bool |
        Table.sem (compile arity sem input)[i.val].1 (List.ofFn t) = true} := by
    subst n
    exact hm
  exact htransport _ hw

/-- Combined ordinary native fixed-language endpoint: no correct-translation certificate,
solver/recognizer, geometric realization, or input-validity premise is a runtime assumption. -/
theorem compile_spec [Finite Rel] (encRel : Rel ↪ List Bool)
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (hself : ∀ r, IsSelfComplementary (booleanRelation arity sem r))
    (hdelta : ∀ r, (booleanRelation arity sem r).Nonempty →
      IsEvenDeltaMatroid (cyclicDifferenceRelation (booleanRelation arity sem r))) :
    ComputableInPolyTime (compile arity sem) (encCSPRotationCertificate encRel encNat)
      (encCSP encTable encNat) ∧
    ∀ input : CSP Rel ℕ × Graph.RotationCertificate,
      EdgeInstance (compile arity sem input) ∧ WellFormed Table.arity (compile arity sem input) ∧
      EdgeInstance.EvenConstraints Table.sem (compile arity sem input) ∧
      ((WellFormed arity input.1 ∧ verifyRotationCertificate input.1 input.2 = true ∧
        input.1.Satisfiable sem) ↔ (compile arity sem input).Satisfiable Table.sem) :=
  ⟨computableInPolyTime_compile encRel arity sem, compile_correct arity sem hself hdelta⟩

end Cslib.Complexity.CSP.CyclicCompiler
