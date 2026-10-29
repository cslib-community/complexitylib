/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Classes.Oracle.Closure
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Complexity.Reduction.Autoreducibility
public import Complexity.Computability.Complexity.Reduction.Turing
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Polynomial-time Turing autoreducibility

A set `A` is **polynomial-time Turing autoreducible** if it can be decided in polynomial time
by an oracle machine that never queries its own input ([Ambos-Spies 1984][AmbosSpies1984];
[Buhrman, Fortnow, van Melkebeek and Torenvliet 2000][BuhrmanFortnowVanMelkebeekTorenvliet2000]).

## Main definitions

* `Cslib.Complexity.PolyTimeTuringAutoreducible`: polynomial-time Turing autoreducibility of an
  encoded language `A`.

## Main results

* `Cslib.Complexity.PolyTimeTuringAutoreducible.polyTimeTuringReducible`: an autoreduction is in
  particular a Turing reduction of `A` to `A`.
* `Cslib.Complexity.polyTimeTuringAutoreducible_bits_iff`: simplified characterization for bitstring
  languages with `encBits`.
* `Cslib.Complexity.polyTimeTuringAutoreducible_of_polyTimeReducible_fixedPointFree`,
  `Cslib.Complexity.PolyTimeManyOneAutoreducible.polyTimeTuringAutoreducible`,
  `Cslib.Complexity.LogSpaceManyOneAutoreducible.polyTimeTuringAutoreducible`: every
  fixed-point-free polynomial-time or logspace many-one autoreduction of `A` induces a
  polynomial-time Turing autoreduction.
* `Cslib.Complexity.PolyTimeTruthTableAutoreducible.polyTimeTuringAutoreducible`,
  `Cslib.Complexity.PolyTimeKTruthTableAutoreducible.polyTimeTuringAutoreducible`,
  `Cslib.Complexity.PolyTimeBTTAutoreducible.polyTimeTuringAutoreducible`,
  `Cslib.Complexity.PolyTimeDTTAutoreducible.polyTimeTuringAutoreducible`,
  `Cslib.Complexity.PolyTimeCTTAutoreducible.polyTimeTuringAutoreducible`: truth-table
  autoreducibility and its bounded, disjunctive, and conjunctive specializations imply
  polynomial-time Turing autoreducibility.
* `Cslib.Complexity.PolyTimeTruthTableMitotic.polyTimeTuringAutoreducible`,
  `Cslib.Complexity.PolyTimeBTTMitotic.polyTimeTuringAutoreducible`,
  `Cslib.Complexity.PolyTimeKTruthTableMitotic.polyTimeTuringAutoreducible`,
  `Cslib.Complexity.PolyTimeDTTMitotic.polyTimeTuringAutoreducible`,
  `Cslib.Complexity.PolyTimeManyOneMitotic.polyTimeTuringAutoreducible`: every truth-table,
  bounded truth-table, `k`-truth-table, disjunctive truth-table, or many-one mitotic set is
  polynomial-time Turing autoreducible.
* `Cslib.Complexity.polyTimeTuringAutoreducible_of_mem_P`: every language `A ∈ P` is unconditionally
  polynomial-time Turing autoreducible (via a 0-query program). This sharply contrasts with
  many-one autoreducibility, where singleton and co-singleton languages in `P` are
  not many-one autoreducible.

## References

* [K. Ambos-Spies, *P-mitotic sets*][AmbosSpies1984]
* [H. Buhrman, L. Fortnow, D. van Melkebeek, L. Torenvliet, *Separating Complexity Classes
  Using Autoreducibility*][BuhrmanFortnowVanMelkebeekTorenvliet2000]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability
open Turing.MultiTapeTM

variable {α : Type} {encA : α ↪ List Bool} {A : Set α}

/-- `A` is polynomial-time Turing autoreducible: some deterministic polynomial-time oracle program
decides `A` relative to the oracle for `A` without ever querying its own input. -/
def PolyTimeTuringAutoreducible (encA : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ program : α → WordQueryComp Unit Bool,
    IsOraclePPTOn encA encBool (fun a => OracleComp.interpret ProbOracleComp.query (program a)) ∧
    (∀ a, ∀ q ∈ OracleComp.queriesWith (languageOracle (encA '' A)) (program a), q.2 ≠ encA a) ∧
    ∀ a, a ∈ A ↔ OracleComp.interpret (m := Id) (languageOracle (encA '' A)) (program a) = true

/-- A polynomial-time Turing autoreduction is in particular a polynomial-time Turing reduction of
`A` to `A`. -/
theorem PolyTimeTuringAutoreducible.polyTimeTuringReducible
    (h : PolyTimeTuringAutoreducible encA A) : PolyTimeTuringReducible encA encA A A := by
  obtain ⟨program, hPPT, _, hdec⟩ := h
  exact ⟨fun a => OracleComp.interpret (m := Id) (languageOracle (encA '' A)) (program a),
    ⟨program, hPPT, fun _ => rfl⟩, hdec⟩

/-- On bitstring languages with the default encoding `encBits`, the no-self-query condition
simply requires `q.2 ≠ a`. -/
theorem polyTimeTuringAutoreducible_bits_iff {B : Set (List Bool)} :
    PolyTimeTuringAutoreducible encBits B ↔
      ∃ program : List Bool → WordQueryComp Unit Bool,
        IsOraclePPTOn encBits encBool
          (fun a => OracleComp.interpret ProbOracleComp.query (program a)) ∧
        (∀ a, ∀ q ∈ OracleComp.queriesWith (languageOracle B) (program a), q.2 ≠ a) ∧
        ∀ a, a ∈ B ↔ OracleComp.interpret (m := Id) (languageOracle B) (program a) = true := by
  have : encBits '' B = B := Set.image_id B
  simp only [PolyTimeTuringAutoreducible, this, encBits_apply]

open Classical in
/-- Every fixed-point-free polynomial-time many-one reduction of `A` to `A` induces a
polynomial-time Turing autoreduction. -/
theorem polyTimeTuringAutoreducible_of_polyTimeReducible_fixedPointFree
    {f : α → α} (hf : ComputableInPolyTime f encA encA) (hne : ∀ a, f a ≠ a)
    (hA : ∀ a, a ∈ A ↔ f a ∈ A) : PolyTimeTuringAutoreducible encA A := by
  refine ⟨fun a => (fun reply => decide (reply = [true])) <$>
    (List.take 1 <$> OracleComp.query ((), encA (f a))), ?_, fun a q hq => ?_, fun a => ?_⟩
  · simp only [OracleComp.interpret_map, OracleComp.interpret_query]
    exact (IsOraclePPTOn.query_take' () hf (limit := fun _ => 1) (by fun_prop)).map'
      (by fun_prop)
  · simp only [OracleComp.queriesWith_map, OracleComp.queriesWith_query,
      List.mem_singleton] at hq
    subst hq
    exact fun h_eq => hne a (encA.injective h_eq)
  · change a ∈ A ↔
      decide (List.take 1 (languageOracle (encA '' A) ((), encA (f a))) = [true]) = true
    rw [languageOracle_apply]
    have hmem : a ∈ A ↔ encA (f a) ∈ encA '' A := by
      rw [hA a, encA.injective.mem_set_image]
    rw [hmem]
    cases hc : decide (encA (f a) ∈ encA '' A)
    · have : encA (f a) ∉ encA '' A := decide_eq_false_iff_not.mp hc
      simp [this]
    · have : encA (f a) ∈ encA '' A := decide_eq_true_iff.mp hc
      simp [this]

/-- **Every problem in `P` is polynomial-time Turing autoreducible.** The decider makes zero
oracle queries, so the no-self-query condition is vacuously satisfied. -/
theorem polyTimeTuringAutoreducible_of_mem_P
    (hA : A ∈ P encA) : PolyTimeTuringAutoreducible encA A := by
  obtain ⟨f, hf, h_dec⟩ := hA
  refine ⟨fun a => pure (f a), ?_, fun a q hq => ?_, fun a => ?_⟩
  · exact hf.isOraclePPTOn (Operation := Unit)
  · simp only [OracleComp.queriesWith_pure, List.not_mem_nil] at hq
  · simp only [OracleComp.interpret_pure]
    exact h_dec a

/-- Every polynomial-time many-one autoreduction is a polynomial-time Turing autoreduction. -/
theorem PolyTimeManyOneAutoreducible.polyTimeTuringAutoreducible
    (h : PolyTimeManyOneAutoreducible encA A) : PolyTimeTuringAutoreducible encA A :=
  let ⟨_, ⟨hf, hne⟩, hA⟩ := h
  polyTimeTuringAutoreducible_of_polyTimeReducible_fixedPointFree hf hne hA

/-- Every logspace many-one autoreduction is a polynomial-time Turing autoreduction. -/
theorem LogSpaceManyOneAutoreducible.polyTimeTuringAutoreducible
    (h : LogSpaceManyOneAutoreducible encA A) : PolyTimeTuringAutoreducible encA A :=
  h.polyTimeManyOneAutoreducible.polyTimeTuringAutoreducible

/-! ### Truth-table to Turing autoreducibility -/

private def queryWordsStep (s : List (List Bool) × List Bool) :
    WordQueryComp Unit (List (List Bool) × List Bool) :=
  if s.1.isEmpty then pure s else
    (fun reply => (s.1.tail, s.2 ++ [reply == [true]])) <$>
      (List.take 1 <$> OracleComp.query ((), s.1.headD []))

private def queryWords (words : List (List Bool)) : WordQueryComp Unit (List Bool) :=
  Prod.snd <$> OracleComp.iterate words.length queryWordsStep (words, [])

private theorem interpret_queryWordsStep (s : List (List Bool) × List Bool) :
    OracleComp.interpret ProbOracleComp.query (queryWordsStep s) =
      if s.1.isEmpty then pure s else
        (fun reply => (s.1.tail, s.2 ++ [reply == [true]])) <$>
          (List.take 1 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), s.1.headD [])) := by
  unfold queryWordsStep
  split <;> simp [OracleComp.interpret_map, OracleComp.interpret_query]

private theorem isOraclePPTOn_queryWords :
    IsOraclePPTOn (encList encBits) encBits
      (fun words => OracleComp.interpret ProbOracleComp.query (queryWords words)) := by
  simp only [queryWords, OracleComp.interpret_map, OracleComp.interpret_iterate]
  refine IsOraclePPTOn.map' (IsOraclePPTOn.iterate_of_bounded_growth'
    (stateEncoding := encPair (encList encBits) encBits) (by fun_prop) (by fun_prop) ?_
    (growth := 0) ?_) (by fun_prop)
  · simp only [interpret_queryWordsStep]
    refine IsOraclePPTOn.cond' (by fun_prop)
      (ComputableInPolyTime.id'.isOraclePPTOn) ?_
    exact IsOraclePPTOn.map_with'
      (IsOraclePPTOn.query_take' () (by fun_prop) (by fun_prop))
      (by fun_prop)
  · intro state next hnext
    rw [interpret_queryWordsStep] at hnext
    obtain ⟨words, acc⟩ := state
    cases words with
    | nil => rw [OracleComp.eq_of_mem_supportWith_pure hnext]; simp
    | cons word words =>
      obtain ⟨reply, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      simp only [length_encPair, encBits_apply, List.length_append, List.length_singleton,
        List.tail_cons, length_encList, List.map_cons, List.sum_cons]
      omega

open Classical in
private theorem interpret_id_queryWordsStep (O : Set (List Bool)) (word : List Bool)
    (words : List (List Bool)) (acc : List Bool) :
    OracleComp.interpret (m := Id) (languageOracle O) (queryWordsStep (word :: words, acc)) =
      (words, acc ++ [decide (word ∈ O)]) := by
  simp only [queryWordsStep, List.isEmpty_cons, Bool.false_eq_true, ite_false]
  change (fun reply : List Bool => (words, acc ++ [reply == [true]]))
    (List.take 1 (languageOracle O ((), word))) = _
  rw [languageOracle_apply]
  cases decide (word ∈ O) <;> rfl

open Classical in
private theorem interpret_queryWords (O : Set (List Bool)) (words : List (List Bool)) :
    OracleComp.interpret (m := Id) (languageOracle O) (queryWords words) =
      words.map fun word => decide (word ∈ O) := by
  have key : ∀ (words : List (List Bool)) (acc : List Bool),
      OracleComp.interpret (m := Id) (languageOracle O)
        (OracleComp.iterate words.length queryWordsStep (words, acc)) =
        ([], acc ++ words.map fun word => decide (word ∈ O)) := by
    intro words
    induction words with
    | nil => intro acc; simp only [List.length_nil, List.map_nil, List.append_nil]; rfl
    | cons word words ih =>
      intro acc
      rw [List.length_cons, OracleComp.iterate_succ_bind, OracleComp.interpret_bind]
      change OracleComp.interpret (m := Id) (languageOracle O)
        (OracleComp.iterate words.length queryWordsStep
          (OracleComp.interpret (m := Id) (languageOracle O)
            (queryWordsStep (word :: words, acc)))) = _
      rw [interpret_id_queryWordsStep, ih]
      simp [List.append_assoc]
  unfold queryWords
  rw [OracleComp.interpret_map, key]
  simp only [List.nil_append]
  rfl

private theorem mem_queriesWith_queryWords
    (answer : (q : Unit × List Bool) → List Bool) (words : List (List Bool))
    {q : Unit × List Bool} (hq : q ∈ OracleComp.queriesWith answer (queryWords words)) :
    q.2 ∈ words := by
  have key : ∀ (ws : List (List Bool)) (acc : List Bool) {q : Unit × List Bool},
      q ∈ OracleComp.queriesWith answer (OracleComp.iterate ws.length queryWordsStep (ws, acc)) →
        q.2 ∈ ws := by
    intro ws
    induction ws with
    | nil =>
      intro acc q hq
      simp only [List.length_nil, OracleComp.iterate, OracleComp.queriesWith_pure,
        List.not_mem_nil] at hq
    | cons w rest ih =>
      intro acc q hq
      rw [List.length_cons, OracleComp.iterate_succ_bind, OracleComp.queriesWith_bind] at hq
      rcases List.mem_append.mp hq with hq₁ | hq₂
      · simp only [queryWordsStep, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
          List.headD_cons, OracleComp.queriesWith_map, OracleComp.queriesWith_query,
          List.mem_singleton] at hq₁
        subst hq₁
        exact List.mem_cons_self
      · obtain ⟨b, hb⟩ : ∃ b, OracleComp.interpret (m := Id) answer
            (queryWordsStep (w :: rest, acc)) = (rest, acc ++ [b]) :=
          ⟨List.take 1 (answer ((), w)) == [true], rfl⟩
        rw [hb] at hq₂
        exact List.mem_cons_of_mem w (ih (acc ++ [b]) hq₂)
  unfold queryWords at hq
  rw [OracleComp.queriesWith_map] at hq
  exact key words [] hq

/-- **Every polynomial-time truth-table autoreduction is a polynomial-time Turing autoreduction.**
The query list `(List.range (r a)).map (fun i => encA (q (a, i)))` is evaluated sequentially
against `languageOracle (encA '' A)`, and every queried word has the form `encA (q (a, i))` with
`i < r a`, which is distinct from `encA a` by injectivity of `encA`. -/
theorem PolyTimeTruthTableAutoreducible.polyTimeTuringAutoreducible
    (h : PolyTimeTruthTableAutoreducible encA A) :
    PolyTimeTuringAutoreducible encA A := by
  classical
  obtain ⟨r, q, d, hr, hq, hd, hne, hA⟩ := h
  let words : α → List (List Bool) :=
    fun a => (List.range (r a)).map fun i => encA (q (a, i))
  have hwords : ComputableInPolyTime words encA (encList encBits) :=
    ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.range.comp hr) hq.encoding_comp
  let program : α → WordQueryComp Unit Bool := fun a =>
    (fun ans => d (a, ans)) <$> queryWords (words a)
  refine ⟨program, ?_, fun a qr hqr => ?_, fun a => ?_⟩
  · have hcomp := IsOraclePPTOn.map_with' (f := fun a ans => d (a, ans))
      (isOraclePPTOn_queryWords.preprocess' hwords) hd
    refine hcomp.congr fun a => ?_
    simp [program]
  · simp only [program, OracleComp.queriesWith_map] at hqr
    have hmem := mem_queriesWith_queryWords (languageOracle (encA '' A)) (words a) hqr
    simp only [words, List.mem_map, List.mem_range] at hmem
    obtain ⟨i, hi, hqi⟩ := hmem
    intro heq
    exact hne a i hi (encA.injective (hqi.trans heq))
  · simp only [program, OracleComp.interpret_map, interpret_queryWords]
    rw [hA a]
    suffices h_eq : (words a).map (fun w => decide (w ∈ encA '' A)) =
        truthTableAnswers (q ⁻¹' A) r a by
      rw [h_eq]
      exact Iff.rfl
    simp [words, truthTableAnswers_eq_map_range, List.map_map, Function.comp_def]

/-- Every polynomial-time `k`-truth-table autoreduction is a polynomial-time Turing
autoreduction. -/
theorem PolyTimeKTruthTableAutoreducible.polyTimeTuringAutoreducible {k : ℕ}
    (h : PolyTimeKTruthTableAutoreducible k encA A) :
    PolyTimeTuringAutoreducible encA A :=
  h.polyTimeBTTAutoreducible.polyTimeTruthTableAutoreducible.polyTimeTuringAutoreducible

/-- Every polynomial-time bounded truth-table autoreduction is a polynomial-time Turing
autoreduction. -/
theorem PolyTimeBTTAutoreducible.polyTimeTuringAutoreducible
    (h : PolyTimeBTTAutoreducible encA A) :
    PolyTimeTuringAutoreducible encA A :=
  h.polyTimeTruthTableAutoreducible.polyTimeTuringAutoreducible

/-- Every polynomial-time disjunctive truth-table autoreduction is a polynomial-time Turing
autoreduction. -/
theorem PolyTimeDTTAutoreducible.polyTimeTuringAutoreducible
    (h : PolyTimeDTTAutoreducible encA A) :
    PolyTimeTuringAutoreducible encA A :=
  h.polyTimeTruthTableAutoreducible.polyTimeTuringAutoreducible

/-- Every polynomial-time conjunctive truth-table autoreduction is a polynomial-time Turing
autoreduction. -/
theorem PolyTimeCTTAutoreducible.polyTimeTuringAutoreducible
    (h : PolyTimeCTTAutoreducible encA A) :
    PolyTimeTuringAutoreducible encA A :=
  h.polyTimeTruthTableAutoreducible.polyTimeTuringAutoreducible

/-- Every polynomial-time truth-table mitotic set is polynomial-time Turing autoreducible. -/
theorem PolyTimeTruthTableMitotic.polyTimeTuringAutoreducible
    (h : PolyTimeTruthTableMitotic encA A) :
    PolyTimeTuringAutoreducible encA A :=
  h.polyTimeTruthTableAutoreducible.polyTimeTuringAutoreducible

/-- Every polynomial-time bounded truth-table mitotic set is polynomial-time Turing
autoreducible. -/
theorem PolyTimeBTTMitotic.polyTimeTuringAutoreducible
    (h : PolyTimeBTTMitotic encA A) :
    PolyTimeTuringAutoreducible encA A :=
  h.polyTimeBTTAutoreducible.polyTimeTuringAutoreducible

/-- Every polynomial-time `k`-truth-table mitotic set is polynomial-time Turing autoreducible. -/
theorem PolyTimeKTruthTableMitotic.polyTimeTuringAutoreducible {k : ℕ}
    (h : PolyTimeKTruthTableMitotic k encA A) :
    PolyTimeTuringAutoreducible encA A :=
  h.polyTimeKTruthTableAutoreducible.polyTimeTuringAutoreducible

/-- Every polynomial-time disjunctive truth-table mitotic set is polynomial-time Turing
autoreducible. -/
theorem PolyTimeDTTMitotic.polyTimeTuringAutoreducible
    (h : PolyTimeDTTMitotic encA A) :
    PolyTimeTuringAutoreducible encA A :=
  h.polyTimeDTTAutoreducible.polyTimeTuringAutoreducible

/-- Every polynomial-time many-one mitotic set is polynomial-time Turing autoreducible. -/
theorem PolyTimeManyOneMitotic.polyTimeTuringAutoreducible
    (h : PolyTimeManyOneMitotic encA A) :
    PolyTimeTuringAutoreducible encA A :=
  h.polyTimeTruthTableMitotic.polyTimeTuringAutoreducible

end Cslib.Complexity
