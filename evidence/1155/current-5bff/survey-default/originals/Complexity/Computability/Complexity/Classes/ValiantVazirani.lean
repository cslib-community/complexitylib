/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle
public import Complexity.Computability.Complexity.Classes.RP
public import Complexity.Computability.Complexity.Classes.ValiantVazirani.Reduction
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Logics.Propositional.CNF.PolyTime

/-!
# The Valiant–Vazirani theorem

Valiant and Vazirani showed that deciding satisfiability reduces in randomized polynomial time to
deciding it on formulas with at most one satisfying assignment [Valiant and Vazirani]
[ValiantVazirani1986], [Arora and Barak, Section 17.4][AroraBarak09].

The randomized isolation reduction `ValiantVazirani.reduce` and its amplification bound
`ValiantVazirani.two_pow_le_two_mul_card_exists_row` are developed in
`Complexity.Computability.Complexity.Classes.ValiantVazirani.Reduction` and re-exported here.

## The class form

`RPWithOracle A enc` is `RP` relative to the oracle language `A`: `Cslib.Complexity.RP` with
`ComputableInPolyTime` replaced by `Cslib.Complexity.ComputableInPolyTimeWithOracle A`, as
`PWithOracle` relativizes `P`. For an oracle that is a promise problem, `RPWithPromiseOracle Q encQ
enc` asks for one algorithm that is correct against every language solving `Q`, whose answers
outside the promise are arbitrary. Every problem in `NP` lies in `RP` relative to `PromiseUSAT`
(`NP_subset_RPWithPromiseOracle_PromiseUSAT`): after the Cook–Levin reduction, the algorithm runs
the Valiant–Vazirani reduction on `11 (N + 3)` independent blocks of random bits, where `N`
bounds the number of variable occurrences, asks the oracle about each reduced formula
(`queryAny`), and accepts when it answers yes once. On a no-instance every reduced formula is
unsatisfiable, so the oracle answers no; on a yes-instance some reduced formula is uniquely
satisfiable except with probability at most `(1 - 3 / (32 (N + 3))) ^ (11 (N + 3)) ≤ 1 / 2`
(`ValiantVazirani.two_pow_le_two_mul_card_exists_row`, from the repeated-trials bound
`Fintype.half_le_dens_filter_exists_apply_mem`). In particular `NP ⊆ RP^USAT`
(`NP_subset_RPWithOracle_USAT`); this form is weak, since `USAT` as a language is `coNP`-hard,
and the promise version carries the Valiant–Vazirani content.

## Main definitions

* `Cslib.Complexity.RPWithOracle`, `Cslib.Complexity.RPWithPromiseOracle`: `RP` relative to an
  oracle language and to a promise problem.
* `Cslib.Complexity.queryAny`: ask every word of a list.

## Main results

* `Cslib.Complexity.computableInPolyTimeWithOracle_any_mem`: asking a list of words.
* `Cslib.Complexity.NP_subset_RPWithPromiseOracle_PromiseUSAT`: `NP ⊆ RP^PromiseUSAT`.
* `Cslib.Complexity.NP_subset_RPWithOracle_USAT`: `NP ⊆ RP^USAT`.

## References

* [L. G. Valiant, V. V. Vazirani, *NP is as easy as detecting unique
  solutions*][ValiantVazirani1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α β : Type}

/-! ### Randomized polynomial time relative to an oracle -/

/-- The problems decided with one-sided error by polynomial-time machines with oracle `A` reading
polynomially long random strings: `Cslib.Complexity.RP` with `ComputableInPolyTime` replaced by
`ComputableInPolyTimeWithOracle A`, as `PWithOracle` relativizes `P`. -/
def RPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTimeWithOracle A V (encPair enc encBits) encBool ∧
      DecidesWithOneSidedError enc p V L}

theorem mem_RPWithOracle {A : Set (List Bool)} {enc : α ↪ List Bool} {L : Set α} :
    L ∈ RPWithOracle A enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTimeWithOracle A V (encPair enc encBits) encBool ∧
        DecidesWithOneSidedError enc p V L :=
  Iff.rfl

/-- Every problem in `RP` is in `RP` relative to every oracle. -/
theorem RP_subset_RPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    RP enc ⊆ RPWithOracle A enc := fun _ ⟨p, V, hV, h⟩ =>
  ⟨p, V, hV.computableInPolyTimeWithOracle A, h⟩

/-- `RP` relative to an oracle lies inside `NP` relative to the same oracle: an accepted random
string is a certificate. -/
theorem RPWithOracle_subset_NPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    RPWithOracle A enc ⊆ NPWithOracle A enc := fun _ ⟨p, V, hV, h⟩ =>
  ⟨p, V, hV, h.isVerifier⟩

open Classical in
/-- The problems decided with one-sided error by a single polynomial-time oracle algorithm
against every oracle language that solves the promise problem `Q` under the encoding `encQ`:
`RP` relative to a promise problem. The algorithm is fixed before the oracle, and the oracle's
answers outside the promise are arbitrary. -/
def RPWithPromiseOracle (Q : PromiseProblem β) (encQ : β ↪ List Bool) (enc : α ↪ List Bool) :
    Set (Set α) :=
  {L | ∃ p : Polynomial ℕ,
    PolyTimeOracleProgram (encPair enc encBits) encBool
      (fun A => Q.SolvedBy (fun b => decide (encQ b ∈ A)))
      (fun V => DecidesWithOneSidedError enc p V L)}

/-- Every problem in `RP` is in `RP` relative to every promise problem: its algorithm makes no
request. -/
theorem RP_subset_RPWithPromiseOracle (Q : PromiseProblem β) (encQ : β ↪ List Bool)
    (enc : α ↪ List Bool) : RP enc ⊆ RPWithPromiseOracle Q encQ enc := fun _ ⟨p, _, hV, h⟩ =>
  ⟨p, .of_polyTime hV fun _ _ => h⟩

open Classical in
/-- `RP` relative to a promise problem lies inside `RP` relative to every oracle language solving
the promise problem. -/
theorem RPWithPromiseOracle_subset_RPWithOracle {Q : PromiseProblem β} {encQ : β ↪ List Bool}
    {A : Set (List Bool)} (hA : Q.SolvedBy fun b => decide (encQ b ∈ A))
    (enc : α ↪ List Bool) :
    RPWithPromiseOracle Q encQ enc ⊆ RPWithOracle A enc := fun _ ⟨p, hL⟩ =>
  let ⟨V, hV, hdec⟩ := hL.exists_computableInPolyTimeWithOracle hA
  ⟨p, V, hV, hdec⟩

/-! ### Asking every word of a list -/

/-- One step of `queryAny`: ask the first remaining word, and record whether its reply begins with
`true`. -/
def queryAnyStep (s : List (List Bool) × Bool) : WordQueryComp Unit (List (List Bool) × Bool) :=
  if s.1.isEmpty then pure s else
    (fun reply => (s.1.tail, s.2 || reply == [true])) <$>
      (List.take 1 <$> OracleComp.query ((), s.1.headD []))

/-- Ask the oracle every word of the list, in order, and accept when some reply begins with
`true`. -/
def queryAny (words : List (List Bool)) : WordQueryComp Unit Bool :=
  Prod.snd <$> OracleComp.iterate words.length queryAnyStep (words, false)

private theorem interpret_queryAnyStep (s : List (List Bool) × Bool) :
    OracleComp.interpret ProbOracleComp.query (queryAnyStep s) =
      if s.1.isEmpty then pure s else
        (fun reply => (s.1.tail, s.2 || reply == [true])) <$>
          (List.take 1 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), s.1.headD [])) := by
  unfold queryAnyStep
  split <;> simp [OracleComp.interpret_map, OracleComp.interpret_query]

/-- **Asking every word is strict oracle PPT**: each step copies one word onto the query buffer
and reads one reply bit, and the list shrinks. -/
private theorem isOraclePPTOn_queryAny :
    IsOraclePPTOn (encList encBits) encBool
      (fun words => OracleComp.interpret ProbOracleComp.query (queryAny words)) := by
  simp only [queryAny, OracleComp.interpret_map, OracleComp.interpret_iterate]
  refine IsOraclePPTOn.map (IsOraclePPTOn.iterate_of_bounded_growth
    (stateEncoding := encPair (encList encBits) encBool) (by fun_prop) (by fun_prop) ?_
    (growth := 0) ?_) (by fun_prop)
  · simp only [interpret_queryAnyStep]
    refine IsOraclePPTOn.cond (by fun_prop) (ComputableTidilyInPolyTime.id'.isOraclePPTOn) ?_
    exact IsOraclePPTOn.map_with (IsOraclePPTOn.query_take () (by fun_prop) (by fun_prop))
      (by fun_prop)
  · intro state next hnext
    rw [interpret_queryAnyStep] at hnext
    obtain ⟨words, acc⟩ := state
    cases words with
    | nil => rw [OracleComp.eq_of_mem_supportWith_pure hnext]; simp
    | cons word words =>
      obtain ⟨reply, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      simp only [length_encPair, encBool_apply, List.length_singleton, List.tail_cons,
        length_encList, List.map_cons, List.sum_cons]
      omega

open Classical in
private theorem interpret_id_queryAnyStep (A : Set (List Bool)) (word : List Bool)
    (words : List (List Bool)) (acc : Bool) :
    OracleComp.interpret (m := Id) (languageOracle A) (queryAnyStep (word :: words, acc)) =
      (words, acc || decide (word ∈ A)) := by
  simp only [queryAnyStep, List.isEmpty_cons, Bool.false_eq_true, ite_false]
  change (fun reply : List Bool => (words, acc || reply == [true]))
    (List.take 1 (languageOracle A ((), word))) = _
  rw [languageOracle_apply]
  cases decide (word ∈ A) <;> rfl

open Classical in
/-- Against a language oracle, `queryAny` accepts exactly when some word is in the language. -/
theorem interpret_queryAny (A : Set (List Bool)) (words : List (List Bool)) :
    OracleComp.interpret (m := Id) (languageOracle A) (queryAny words) =
      words.any fun word => decide (word ∈ A) := by
  have key : ∀ (words : List (List Bool)) (acc : Bool),
      OracleComp.interpret (m := Id) (languageOracle A)
        (OracleComp.iterate words.length queryAnyStep (words, acc)) =
        ([], acc || words.any fun word => decide (word ∈ A)) := by
    intro words
    induction words with
    | nil => intro acc; simp only [List.length_nil, List.any_nil, Bool.or_false]; rfl
    | cons word words ih =>
      intro acc
      rw [List.length_cons, OracleComp.iterate_succ_bind, OracleComp.interpret_bind]
      change OracleComp.interpret (m := Id) (languageOracle A)
        (OracleComp.iterate words.length queryAnyStep
          (OracleComp.interpret (m := Id) (languageOracle A)
            (queryAnyStep (word :: words, acc)))) = _
      rw [interpret_id_queryAnyStep, ih]
      simp [Bool.or_assoc]
  unfold queryAny
  rw [OracleComp.interpret_map, key]
  simp only [Bool.false_or]
  rfl

open Classical in
/-- Whether some word of a list is in `A` is computable in polynomial time relative to `A`. -/
theorem computableInPolyTimeWithOracle_any_mem (A : Set (List Bool)) :
    ComputableInPolyTimeWithOracle A (fun words : List (List Bool) =>
      words.any fun word => decide (word ∈ A)) (encList encBits) encBool :=
  ⟨queryAny, isOraclePPTOn_queryAny, interpret_queryAny A⟩

/-! ### NP is in RP relative to PromiseUSAT -/

open ValiantVazirani in
/-- **Valiant–Vazirani: `NP ⊆ RP^PromiseUSAT`.** Every problem in `NP` is decided with one-sided
error by one polynomial-time oracle algorithm against every language solving `PromiseUSAT`. The
algorithm reduces the instance to `SAT` by the Cook–Levin theorem, runs the Valiant–Vazirani
reduction on `11 (N + 3)` independent blocks of `(N + 2) ^ 2` random bits, where `N` bounds the
number of variable occurrences, asks the oracle about each reduced formula, and accepts when it
answers yes once. On a no-instance every reduced formula is unsatisfiable, so the oracle always
answers no. -/
theorem NP_subset_RPWithPromiseOracle_PromiseUSAT (enc : α ↪ List Bool) :
    NP enc ⊆ RPWithPromiseOracle PromiseUSAT encCNF enc := by
  classical
  intro L hL
  obtain ⟨g, hg, hgL⟩ := (CookLevin.SAT_npHard enc L hL)
  obtain ⟨c, d, hlen⟩ := hg.polyBounded_length.exists_le
  let queries : α × List Bool → List (List Bool) := fun x =>
    (BitString.listRows (11 * (c * ((enc x.1).length + 1) ^ d + 3))
      ((c * ((enc x.1).length + 1) ^ d + 2) ^ 2) x.2).map
        fun b => encCNF (reduce (g x.1, b))
  have hqueries : ComputableTidilyInPolyTime queries (encPair enc encBits) (encList encBits) := by
    have hreduce := computableInPolyTime_reduce.tidy
    have hg := hg.tidy
    fun_prop
  refine ⟨Polynomial.C 11 * (Polynomial.C c * (Polynomial.X + 1) ^ d + 3) *
      (Polynomial.C c * (Polynomial.X + 1) ^ d + 2) ^ 2,
    fun x => queryAny (queries x), isOraclePPTOn_queryAny.preprocess hqueries,
    fun A hA a => ⟨fun ha => ?_, fun ha r => ?_⟩⟩
  · set N := c * ((enc a).length + 1) ^ d with hN
    have heval : (Polynomial.C 11 * (Polynomial.C c * (Polynomial.X + 1) ^ d + 3) *
        (Polynomial.C c * (Polynomial.X + 1) ^ d + 2) ^ 2).eval (enc a).length =
        11 * (N + 3) * (N + 2) ^ 2 := by
      simp [hN]
    rw [heval]
    have hsat : g a ∈ SAT := (hgL a).1 ha
    have hvars : (g a).vars.length ≤ N := (SAT.length_vars_le _).trans (hlen a)
    have hW : randomBits (g a) ≤ (N + 2) ^ 2 :=
      (randomBits_le _).trans (Nat.pow_le_pow_left (by omega) 2)
    refine (two_pow_le_two_mul_card_exists_row (M := N + 3) (by omega)
      (fun b => reduce (g a, b) ∈ USAT)
      ((three_mul_two_pow_le_card_reduce_mem_USAT hsat hW).trans ?_)).trans ?_
    · exact Nat.mul_le_mul_right _ (by omega)
    · refine Nat.mul_le_mul_left _ (Finset.card_le_card fun r hr => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      obtain ⟨b, hb, hgood⟩ := hr
      rw [interpret_queryAny, List.any_eq_true]
      exact ⟨_, List.mem_map.2 ⟨b, hb, rfl⟩, hA.1 _ hgood⟩
  · dsimp only
    rw [interpret_queryAny, List.any_eq_false]
    intro w hw
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hw
    have := hA.2 _ (reduce_mem_UNSAT (fun h => ha ((hgL a).2 h)) b)
    simpa using this

open Classical in
/-- **`NP ⊆ RP^A` for every language `A` solving `PromiseUSAT`.** -/
theorem NP_subset_RPWithOracle_of_solvedBy {A : Set (List Bool)}
    (hA : PromiseUSAT.SolvedBy fun φ => decide (encCNF φ ∈ A)) (enc : α ↪ List Bool) :
    NP enc ⊆ RPWithOracle A enc :=
  (NP_subset_RPWithPromiseOracle_PromiseUSAT enc).trans
    (RPWithPromiseOracle_subset_RPWithOracle hA enc)

/-- **`NP ⊆ RP^USAT`**, with the encodings of the uniquely satisfiable formulas as oracle. This
form is weak: `USAT` as a language is `coNP`-hard, so even `P` relative to it contains `NP`. The
Valiant–Vazirani content is the promise version `NP_subset_RPWithPromiseOracle_PromiseUSAT`,
whose algorithm only relies on the oracle's answers on uniquely satisfiable and unsatisfiable
formulas. -/
theorem NP_subset_RPWithOracle_USAT (enc : α ↪ List Bool) :
    NP enc ⊆ RPWithOracle (encCNF '' USAT) enc := by
  classical
  refine NP_subset_RPWithOracle_of_solvedBy ?_ enc
  simpa only [encCNF.injective.mem_set_image] using solvedBy_USAT

end Cslib.Complexity
