/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP.SelfReduction
public import Complexity.Computability.Complexity.Classes.Oracle
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
import Complexity.Computability.Complexity.Classes.Oracle.Closure
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation

/-!
# The self-reduction of `SAT` relative to an oracle

The self-reduction of `Complexity.Computability.Complexity.Classes.NP.SelfReduction` fixes the
literal occurrences of a formula one at a time, asking a decision procedure whether the formula
stays satisfiable [Arora and Barak][AroraBarak09]. Here the decision procedure is an
oracle language `A`, asked about the encodings of the formulas: the self-reduction is polynomial
time relative to `A` (`Cslib.Complexity.SAT.computableInPolyTimeWithOracle_selfReduce`,
`Cslib.Complexity.SAT.computableInPolyTimeWithOracle_search`). With `A` the encodings of the
satisfiable formulas, which is in `NP`, it finds a satisfying assignment of every satisfiable
formula (`Cslib.Complexity.SAT.verifier_search_image`): search for `SAT` is polynomial time with
an `NP` oracle.

The oracle program (`Cslib.Complexity.SAT.searchProgram`) is a bounded adaptive loop, one step per
literal occurrence. Each step asks one request (`Cslib.Complexity.SAT.searchStepProgram`), and its
state is the list of literals fixed so far, as in `Cslib.Complexity.SAT.selfReduce`; the loop is
certified by `Cslib.Probability.IsOraclePPTOn.iterateWith_spec'`, with every reachable state
bounded through `Cslib.Complexity.SAT.length_encNat_le_of_mem_vars`.

## Main definitions

* `Cslib.Complexity.SAT.searchQuery`: the formula asked about by one step.
* `Cslib.Complexity.SAT.searchStep`: one step of the self-reduction on the literals fixed so far.
* `Cslib.Complexity.SAT.searchStepProgram`, `Cslib.Complexity.SAT.searchProgram`: the oracle
  programs.

## Main results

* `Cslib.Complexity.SAT.iterate_searchStep`: iterating the step is the self-reduction.
* `Cslib.Complexity.SAT.computableInPolyTimeWithOracle_selfReduce`,
  `Cslib.Complexity.SAT.computableInPolyTimeWithOracle_search`: the self-reduction is polynomial
  time relative to any oracle language that answers its requests.
* `Cslib.Complexity.SAT.verifier_search_image`, `Cslib.Complexity.SAT.exists_search_withOracle`:
  with the oracle `encCNF '' SAT`, the search finds a satisfying assignment of every satisfiable
  formula.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.SAT

open Cslib.Logic.PL Turing.MultiTapeTM Probability

/-! ### The step -/

/-- The formula asked about after fixing the literals `answers`: `φ` with them as unit clauses, and
the next literal occurrence set to true. -/
def searchQuery (φ : CNF ℕ) (answers : List (Literal ℕ)) : CNF ℕ :=
  φ ++ units answers ++ [[(φ.vars.getD answers.length 0, true)]]

/-- One step of the self-reduction of `φ` with the decision procedure `D`, on the literals fixed
so far: fix the next literal occurrence, if any remains. -/
def searchStep (D : CNF ℕ → Bool) (φ : CNF ℕ) (answers : List (Literal ℕ)) :
    List (Literal ℕ) :=
  if answers.length < φ.vars.length then
    answers ++ [(φ.vars.getD answers.length 0, D (searchQuery φ answers))]
  else answers

/-- Each step of the self-reduction fixes one more literal. -/
private theorem length_foldl_selfReduceStep (D : CNF ℕ → Bool) (φ : CNF ℕ) (l : List ℕ)
    (answers : List (Literal ℕ)) :
    (l.foldl (selfReduceStep D φ) answers).length = answers.length + l.length := by
  induction l generalizing answers with
  | nil => rfl
  | cons v l ih =>
    simp only [List.foldl_cons, ih, selfReduceStep, List.length_append, List.length_cons,
      List.length_nil]
    omega

/-- **Iterating the step is the self-reduction**, on every prefix of the literal occurrences. -/
theorem iterate_searchStep (D : CNF ℕ → Bool) (φ : CNF ℕ) {i : ℕ} (hi : i ≤ φ.vars.length) :
    (searchStep D φ)^[i] [] = (φ.vars.take i).foldl (selfReduceStep D φ) [] := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hlt : i < φ.vars.length := by omega
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hlen : ((φ.vars.take i).foldl (selfReduceStep D φ) []).length = i := by
      rw [length_foldl_selfReduceStep, List.length_nil, List.length_take]
      omega
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.foldl_append,
      List.foldl_cons, List.foldl_nil, searchStep, ite_eq_left (by omega : _ < _), selfReduceStep,
      searchQuery,
      hlen, List.getD_eq_getElem _ _ hlt]

/-- The self-reduction is the step iterated once for each literal occurrence. -/
theorem selfReduce_eq_iterate (D : CNF ℕ → Bool) (φ : CNF ℕ) :
    selfReduce D φ = (searchStep D φ)^[φ.vars.length] [] := by
  rw [iterate_searchStep D φ le_rfl, List.take_length, selfReduce]

/-! ### The oracle program -/

/-- One step against an oracle: `prog` answers the request for the encoded query. -/
def searchStepProgram (prog : List Bool → WordQueryComp Unit Bool) (φ : CNF ℕ)
    (answers : List (Literal ℕ)) : WordQueryComp Unit (List (Literal ℕ)) :=
  if answers.length < φ.vars.length then
    (fun b => answers ++ [(φ.vars.getD answers.length 0, b)]) <$>
      prog (encCNF (searchQuery φ answers))
  else pure answers

/-- The self-reduction against an oracle: one step for each literal occurrence. -/
def searchProgram (prog : List Bool → WordQueryComp Unit Bool) (φ : CNF ℕ) :
    WordQueryComp Unit (List (Literal ℕ)) :=
  OracleComp.iterate φ.vars.length (searchStepProgram prog φ) []

open Classical in
/-- Against an oracle language, a step is the step of the self-reduction with the decision
procedure the oracle answers. -/
theorem interpret_searchStepProgram {A : Set (List Bool)}
    {prog : List Bool → WordQueryComp Unit Bool}
    (hprog : ∀ w, OracleComp.interpret (m := Id) (languageOracle A) (prog w) = decide (w ∈ A))
    (φ : CNF ℕ) (answers : List (Literal ℕ)) :
    OracleComp.interpret (m := Id) (languageOracle A) (searchStepProgram prog φ answers) =
      searchStep (fun ψ => decide (encCNF ψ ∈ A)) φ answers := by
  unfold searchStepProgram searchStep
  split_ifs
  · rw [OracleComp.interpret_map, hprog]
    rfl
  · rfl

open Classical in
/-- Against an oracle language, the program is the self-reduction with the decision procedure the
oracle answers. -/
theorem interpret_searchProgram {A : Set (List Bool)}
    {prog : List Bool → WordQueryComp Unit Bool}
    (hprog : ∀ w, OracleComp.interpret (m := Id) (languageOracle A) (prog w) = decide (w ∈ A))
    (φ : CNF ℕ) :
    OracleComp.interpret (m := Id) (languageOracle A) (searchProgram prog φ) =
      selfReduce (fun ψ => decide (encCNF ψ ∈ A)) φ := by
  rw [searchProgram, OracleComp.interpret_id_iterate, selfReduce_eq_iterate]
  congr 1
  funext answers
  exact interpret_searchStepProgram hprog φ answers

/-! ### Polynomial time -/

/-- The literals fixed so far have short encodings: each is an occurrence of `φ`. -/
private theorem length_encList_le {φ : CNF ℕ} {answers : List (Literal ℕ)}
    (h : ∀ l ∈ answers, l.1 ∈ φ.vars) :
    (encList (encPair encNat encBool) answers).length ≤
      answers.length * (4 * (encCNF φ).length + 5) := by
  induction answers with
  | nil => simp [encList_nil]
  | cons l answers ih =>
    have hl := length_encNat_le_of_mem_vars (h l List.mem_cons_self)
    have ih := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    simp only [encList_cons, List.length_append, length_frame, length_encPair, encBool_apply,
      List.length_cons, List.length_nil]
    rw [Nat.add_mul, Nat.one_mul]
    generalize answers.length * (4 * (encCNF φ).length + 5) = X at ih ⊢
    omega

/-- The step is strict oracle PPT, for a polynomial-time single-request decision `prog`. -/
private theorem isOraclePPTOn_searchStepProgram {prog : List Bool → WordQueryComp Unit Bool}
    (hprog : IsOraclePPTOn encBits encBool
      (fun w => OracleComp.interpret ProbOracleComp.query (prog w))) :
    IsOraclePPTOn (encPair encCNF (encList (encPair encNat encBool)))
      (encList (encPair encNat encBool))
      (fun pair => OracleComp.interpret ProbOracleComp.query
        (searchStepProgram prog pair.1 pair.2)) := by
  have hlen : ComputableInPolyTime (fun pair : CNF ℕ × List (Literal ℕ) => pair.2.length)
      (encPair encCNF (encList (encPair encNat encBool))) encUnary :=
    (ComputableInPolyTime.length_list _).comp (ComputableInPolyTime.snd _ _)
  have hvars : ComputableInPolyTime (fun pair : CNF ℕ × List (Literal ℕ) => pair.1.vars)
      (encPair encCNF (encList (encPair encNat encBool))) (encList encNat) :=
    computableInPolyTime_vars.comp (ComputableInPolyTime.fst _ _)
  have hnext : ComputableInPolyTime
      (fun pair : CNF ℕ × List (Literal ℕ) => pair.1.vars.getD pair.2.length 0)
      (encPair encCNF (encList (encPair encNat encBool))) encNat :=
    ComputableInPolyTime.listGetDWithInput hvars hlen 0
  have hquery : ComputableInPolyTime
      (fun p : (CNF ℕ × List (Literal ℕ)) × ℕ => p.1.1 ++ units p.1.2 ++ [[(p.2, true)]])
      (encPair (encPair encCNF (encList (encPair encNat encBool))) encNat) encCNF := by
    unfold units encCNF
    fun_prop
  have hrequest : ComputableInPolyTime
      (fun pair : CNF ℕ × List (Literal ℕ) => encCNF (searchQuery pair.1 pair.2))
      (encPair encCNF (encList (encPair encNat encBool))) encBits :=
    (hquery.comp (ComputableInPolyTime.id'.prod hnext)).of_enc_eq fun _ => rfl
  have hcond : ComputableInPolyTime
      (fun pair : CNF ℕ × List (Literal ℕ) => decide (pair.2.length < pair.1.vars.length))
      (encPair encCNF (encList (encPair encNat encBool))) encBool := by
    have hvarsLen : ComputableInPolyTime
        (fun pair : CNF ℕ × List (Literal ℕ) => pair.1.vars.length)
        (encPair encCNF (encList (encPair encNat encBool))) encUnary :=
      (ComputableInPolyTime.length_list _).comp hvars
    exact ComputableInPolyTime.unary_lt.comp (hlen.prod hvarsLen)
  have hpost : ComputableInPolyTime
      (fun p : (CNF ℕ × List (Literal ℕ)) × Bool =>
        p.1.2 ++ [(p.1.1.vars.getD p.1.2.length 0, p.2)])
      (encPair (encPair encCNF (encList (encPair encNat encBool))) encBool)
      (encList (encPair encNat encBool)) :=
    ComputableInPolyTime.listAppend' (ComputableInPolyTime.fst _ _).snd'
      (ComputableInPolyTime.cons' ((hnext.comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _)) (ComputableInPolyTime.const []))
  have hyes := (hprog.preprocess' hrequest).map_with'
    (f := fun pair b => pair.2 ++ [(pair.1.vars.getD pair.2.length 0, b)]) hpost
  have hno : IsOraclePPTOn (Operation := Unit)
      (encPair encCNF (encList (encPair encNat encBool))) (encList (encPair encNat encBool))
      (fun pair : CNF ℕ × List (Literal ℕ) => pure pair.2) :=
    (ComputableInPolyTime.snd _ _).isOraclePPTOn
  refine (IsOraclePPTOn.ite' (condition := fun pair : CNF ℕ × List (Literal ℕ) =>
    pair.2.length < pair.1.vars.length) hcond hyes hno).congr fun pair State oracle s => ?_
  unfold searchStepProgram
  split_ifs <;> simp only [OracleComp.interpret_map, OracleComp.interpret_pure]

open Classical in
/-- **The self-reduction is polynomial time relative to an oracle language** `A`, when `A` answers
its requests: the decision procedure asks whether the encoding of the query is in `A`. -/
theorem computableInPolyTimeWithOracle_selfReduce (A : Set (List Bool)) :
    ComputableInPolyTimeWithOracle A (selfReduce fun ψ => decide (encCNF ψ ∈ A)) encCNF
      (encList (encPair encNat encBool)) := by
  obtain ⟨prog, hprogCert, hprog⟩ := computableInPolyTimeWithOracle_mem A
  have hcount : ComputableInPolyTime (fun φ : CNF ℕ => φ.vars.length) encCNF encUnary :=
    (ComputableInPolyTime.length_list _).comp computableInPolyTime_vars
  have hsize : PolyBounded (fun φ => (encCNF φ).length)
      (fun φ => (encUnary φ.vars.length).length * (4 * (encCNF φ).length + 5)) :=
    hcount.polyBounded_length.mul (((PolyBounded.const 4).mul
      (PolyBounded.of_forall_le 1 1 fun φ => by simp)).add (.const 5))
  have hit := IsOraclePPTOn.iterateWith_spec' (input := encCNF)
    (stateEncoding := encList (encPair encNat encBool))
    (count := fun φ => φ.vars.length) (initial := fun _ => [])
    (step := fun φ answers => OracleComp.interpret ProbOracleComp.query
      (searchStepProgram prog φ answers))
    hcount (ComputableInPolyTime.const []) (isOraclePPTOn_searchStepProgram hprogCert)
    (fun φ i answers => answers.map Prod.fst = φ.vars.take i) (fun _ => rfl)
    (fun φ i answers hi hinv next hnext => by
      have hlen : answers.length = i := by
        rw [← List.length_map (f := Prod.fst), hinv, List.length_take]
        omega
      unfold searchStepProgram at hnext
      rw [ite_eq_left (by omega), OracleComp.interpret_map] at hnext
      obtain ⟨b, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      have hlt : i < φ.vars.length := hi
      rw [List.map_append, hinv, hlen, List.take_add_one, List.getElem?_eq_getElem hlt,
        Option.toList_some, List.getD_eq_getElem _ _ hlt]
      rfl)
    hsize
    (fun φ i answers hi hinv => by
      have hmem : ∀ l ∈ answers, l.1 ∈ φ.vars := fun l hl =>
        List.mem_of_mem_take (hinv ▸ List.mem_map_of_mem hl)
      have hlen : answers.length ≤ φ.vars.length := by
        rw [← List.length_map (f := Prod.fst), hinv, List.length_take]
        omega
      simp only [encUnary_apply, List.length_replicate]
      exact (length_encList_le hmem).trans (Nat.mul_le_mul_right _ hlen))
  refine ⟨searchProgram prog, ?_, fun φ => interpret_searchProgram hprog φ⟩
  simpa only [searchProgram, OracleComp.interpret_iterate] using hit.1

open Classical in
/-- **The certificate found by the self-reduction is polynomial time relative to `A`.** -/
theorem computableInPolyTimeWithOracle_search (A : Set (List Bool)) :
    ComputableInPolyTimeWithOracle A (search fun ψ => decide (encCNF ψ ∈ A)) encCNF encBits :=
  (computableInPolyTimeWithOracle_selfReduce A).map
    (ComputableInPolyTime.listToBits.comp
      (ComputableInPolyTime.map (ComputableInPolyTime.snd encNat encBool)))

open Classical in
/-- **Search for `SAT` with an `NP` oracle.** With the oracle `encCNF '' SAT`, which is in `NP`,
the self-reduction finds a satisfying assignment of every satisfiable formula. -/
theorem verifier_search_image (φ : CNF ℕ) :
    verifier (φ, search (fun ψ => decide (encCNF ψ ∈ encCNF '' SAT)) φ) = true ↔ φ ∈ SAT :=
  verifier_search_iff fun ψ _ => by
    rw [decide_eq_true_iff]
    exact ⟨fun ⟨ψ', hψ', heq⟩ => encCNF.injective heq ▸ hψ', fun h => ⟨ψ, h, rfl⟩⟩

/-- **Satisfying assignments in polynomial time with an oracle for `SAT`**, the oracle analogue of
`Cslib.Complexity.SAT.exists_search`. -/
theorem exists_search_withOracle :
    ∃ g : CNF ℕ → List Bool, ComputableInPolyTimeWithOracle (encCNF '' SAT) g encCNF encBits ∧
      ∀ φ, verifier (φ, g φ) = true ↔ φ ∈ SAT := by
  classical
  exact ⟨_, computableInPolyTimeWithOracle_search _, verifier_search_image⟩

end Cslib.Complexity.SAT
