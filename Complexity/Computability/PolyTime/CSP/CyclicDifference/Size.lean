/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.CyclicDifference.Spec

/-!
# Combinatorial and encoded compiler bounds

`M` is the actual original occurrence count and `C` the actual constraint count. White boundaries
partition exactly `M` edge positions; auxiliary blocks have at most `M` names. The bounds refer
to actual emitted constraints and dense binary names, independently of original label magnitude.
Full framed encoded output polynomiality is `polyBounded_length_compile`, derived from the
ordinary native program certificate, not from a unit-cost combinatorial-size proxy.
-/

public section

namespace Cslib.Complexity.CSP.CyclicCompiler

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Table
open Graph.RotationCertificate Turing.MultiTapeTM

variable {Rel : Type} {F : CSP Rel ℕ}

/-- Full static black-table encoding bound, including binary arity, Boolean row framing and
row-list framing. Its exponential arity factor is a constant only for a fixed language. -/
theorem length_encTable_differenceTable_le (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) (r : Rel) :
    (encTable (differenceTable arity sem r)).length ≤
      2 * (encNat (arity r)).length + 1 + 2 ^ arity r * (6 * arity r + 1) := by
  rw [length_encTable (wellFormed_differenceTable arity sem r)]
  have hrows := length_rows_differenceTable_le arity sem r
  simpa only [arity_differenceTable] using
    Nat.add_le_add_left (Nat.mul_le_mul_right (6 * arity r + 1) hrows)
      (2 * (encNat (arity r)).length + 1)

/-- Each emitted white table has at most 81 fully framed bits, independent of face length. -/
theorem length_encTable_evenTable_le {n : ℕ} (hn : n ≤ 3) :
    (encTable (evenTable n)).length ≤ 81 := by
  interval_cases n <;> decide

/-- Nonempty raw boundary scans include their starting edge whenever it is in range. -/
theorem whiteScope_nonempty (cert : Graph.RotationCertificate) (edge : ℕ)
    (hedge : edge < F.occurrences.length) : 0 < (whiteScope F cert edge).length := by
  apply List.length_pos_iff.mpr
  apply List.ne_nil_of_mem (a := edge)
  apply List.mem_filter.mpr
  refine ⟨List.mem_range.mpr hedge, List.any_eq_true.mpr ?_⟩
  exact ⟨0, List.mem_range.mpr (by omega), by
    simp only [walk, Function.iterate_zero, id_eq, decide_true]⟩

/-- Every emitted white face has a genuine nonempty boundary, including raw certificates. -/
theorem whiteScopes_nonempty (cert : Graph.RotationCertificate) :
    ∀ scope ∈ whiteScopes F cert, 0 < scope.length := by
  intro scope hs
  obtain ⟨edge, he, rfl⟩ := List.mem_map.mp hs
  exact whiteScope_nonempty cert edge (List.mem_range.mp (List.mem_filter.mp he).1)

/-- The complete white boundary length is exactly the original occurrence count. -/
theorem length_flatten_whiteScopes (cert : Graph.RotationCertificate)
    (h : verifyRotation (incidenceGraph F) cert = true) :
    (whiteScopes F cert).flatten.length = F.occurrences.length := by
  have he : (whiteScopes F cert).flatten.toFinset = Finset.range F.occurrences.length := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_range, mem_flatten_whiteScopes cert h]
  have hn := List.toFinset_card_of_nodup (nodup_flatten_whiteScopes cert h)
  rw [he, Finset.card_range] at hn
  exact hn.symm

/-- Fresh auxiliary allocation is bounded by the actual total white boundary length. -/
theorem auxiliaryPrefix_all_le (scopes : List (List ℕ)) :
    auxiliaryPrefix scopes scopes.length ≤ scopes.flatten.length := by
  induction scopes with
  | nil => simp [auxiliaryPrefix]
  | cons scope scopes ih =>
    simp only [List.length_cons, auxiliaryPrefix_cons, List.flatten_cons, List.length_append]
    omega

/-- At most one chain constraint per original boundary edge for nonempty faces. -/
theorem length_whiteConstraints_le (edges : ℕ) (scopes : List (List ℕ))
    (hpos : ∀ scope ∈ scopes, 0 < scope.length) :
    (whiteConstraints edges scopes).length ≤ scopes.flatten.length := by
  induction scopes generalizing edges with
  | nil => simp [whiteConstraints]
  | cons scope scopes ih =>
    rw [whiteConstraints_cons, List.length_append, length_parityChain]
    have hs := hpos scope (by simp)
    have ht := ih (edges + (scope.length - 3)) (fun s hm => hpos s (by simp [hm]))
    simp only [List.flatten_cons, List.length_append]
    omega

/-- The body contains at most `C + M` constraints, including retained original positions. -/
theorem length_body_le (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (cert : Graph.RotationCertificate) (h : verifyRotation (incidenceGraph F) cert = true) :
    (body arity sem F cert).length ≤ F.length + F.occurrences.length := by
  have hb : (blackConstraints arity sem F).length ≤ F.length := by
    simpa only [blackConstraints, List.length_map, List.length_zipIdx] using
      List.length_filter_le (fun entry : Constraint Rel ℕ × ℕ => !entry.1.2.isEmpty) F.zipIdx
  have hw := length_whiteConstraints_le F.occurrences.length (whiteScopes F cert)
    (whiteScopes_nonempty cert)
  rw [length_flatten_whiteScopes cert h] at hw
  unfold body
  rw [List.length_append]
  omega

/-- Every body variable lies in the consecutive old-edge-plus-auxiliary interval. -/
theorem body_names_lt (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (cert : Graph.RotationCertificate) (h : verifyRotation (incidenceGraph F) cert = true)
    (v : ℕ) (hv : v ∈ (body arity sem F cert).vars) : v < 2 * F.occurrences.length := by
  have hc := count_vars_body arity sem cert h v
  have hp := List.count_pos_iff.mpr hv
  have ha := auxiliaryPrefix_all_le (whiteScopes F cert)
  rw [length_flatten_whiteScopes cert h] at ha
  split_ifs at hc <;> omega

/-- The body's variable set is exactly one dense interval; unused auxiliary names are not
allocated. Source names and nullary constraint positions introduce no holes. -/
theorem vars_toFinset_body (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (cert : Graph.RotationCertificate) (h : verifyRotation (incidenceGraph F) cert = true) :
    (body arity sem F cert).vars.toFinset = Finset.range (F.occurrences.length +
      auxiliaryPrefix (whiteScopes F cert) (whiteScopes F cert).length) := by
  ext v
  rw [List.mem_toFinset, ← List.count_pos_iff, count_vars_body arity sem cert h,
    Finset.mem_range]
  split_ifs <;> omega

/-- Exact dense variable count, before the fixed rejection branch. -/
theorem numVars_body (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (cert : Graph.RotationCertificate) (h : verifyRotation (incidenceGraph F) cert = true) :
    (body arity sem F cert).numVars = F.occurrences.length +
      auxiliaryPrefix (whiteScopes F cert) (whiteScopes F cert).length := by
  rw [CSP.numVars, vars_toFinset_body arity sem cert h, Finset.card_range]

/-- Exactly two actual ports per dense target variable, and at most `4M` emitted ports. -/
theorem length_vars_body_le (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (cert : Graph.RotationCertificate) (h : verifyRotation (incidenceGraph F) cert = true) :
    (body arity sem F cert).vars.length ≤ 4 * F.occurrences.length := by
  have hl := List.sum_toFinset_count_eq_length (body arity sem F cert).vars
  rw [vars_toFinset_body arity sem cert h] at hl
  have hc : (∑ v ∈ Finset.range (F.occurrences.length +
      auxiliaryPrefix (whiteScopes F cert) (whiteScopes F cert).length),
      (body arity sem F cert).vars.count v) =
      2 * (F.occurrences.length +
        auxiliaryPrefix (whiteScopes F cert) (whiteScopes F cert).length) := by
    calc
      _ = ∑ _v ∈ Finset.range (F.occurrences.length +
          auxiliaryPrefix (whiteScopes F cert) (whiteScopes F cert).length), 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [count_vars_body arity sem cert h, ite_eq_left (Finset.mem_range.mp hv)]
      _ = _ := by simp [Nat.mul_comm]
  have ha := auxiliaryPrefix_all_le (whiteScopes F cert)
  rw [length_flatten_whiteScopes cert h] at ha
  omega

/-- Every raw compiler output has at most `C + M + 2` constraints. Rejection uses two pins. -/
theorem length_compile_le (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (input : CSP Rel ℕ × Graph.RotationCertificate) :
    (compile arity sem input).length ≤ input.1.length + input.1.occurrences.length + 2 := by
  unfold compile
  split_ifs with hg
  · have hp : (validArity arity input.1 = true ∧
        verifyRotationCertificate input.1 input.2 = true) ∧
        input.1.all (fun c => nonemptySymbol arity sem c.1) = true := by
      simpa only [Bool.and_eq_true] using hg
    obtain ⟨h, _, _⟩ := (verifyRotationCertificate_eq_true_iff input.1 input.2).mp hp.1.2
    exact (length_body_le arity sem input.2 h).trans (by omega)
  · change 2 ≤ _
    omega

/-- Binary output names are bounded by `2M`, with the fixed rejecting name included. -/
theorem compile_names_lt (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (input : CSP Rel ℕ × Graph.RotationCertificate)
    (v : ℕ) (hv : v ∈ (compile arity sem input).vars) : v < 2 * input.1.occurrences.length + 1 := by
  unfold compile at hv
  split_ifs at hv with hg
  · have hp : (validArity arity input.1 = true ∧
        verifyRotationCertificate input.1 input.2 = true) ∧
        input.1.all (fun c => nonemptySymbol arity sem c.1) = true := by
      simpa only [Bool.and_eq_true] using hg
    obtain ⟨h, _, _⟩ := (verifyRotationCertificate_eq_true_iff input.1 input.2).mp hp.1.2
    exact (body_names_lt arity sem input.2 h v hv).trans (Nat.lt_succ_self _)
  · have he : v = 0 := by simpa [rejectEdge, CSP.vars] using hv
    omega

/-- Every raw compiler output has at most `4M + 2` actual ports, including rejection. -/
theorem length_vars_compile_le (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (input : CSP Rel ℕ × Graph.RotationCertificate) :
    (compile arity sem input).vars.length ≤ 4 * input.1.occurrences.length + 2 := by
  unfold compile
  split_ifs with hg
  · have hp : (validArity arity input.1 = true ∧
        verifyRotationCertificate input.1 input.2 = true) ∧
        input.1.all (fun c => nonemptySymbol arity sem c.1) = true := by
      simpa only [Bool.and_eq_true] using hg
    obtain ⟨h, _, _⟩ := (verifyRotationCertificate_eq_true_iff input.1 input.2).mp hp.1.2
    exact (length_vars_body_le arity sem input.2 h).trans (by omega)
  · change 2 ≤ _
    omega

end Cslib.Complexity.CSP.CyclicCompiler
