/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle.QueryBit
public import Complexity.Computability.Complexity.Problems.SAT
import Complexity.Computability.Complexity.Classes.NP.Image
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Probabilistic.Oracle.Composition

/-!
# Bounded-query oracle classes and `P^{NP[O(log n)]}`

`f` is computable in polynomial time relative to `A` with `r` requests
(`Cslib.Complexity.ComputableInPolyTimeWithOracleQueries`) when it has the certificate of
`Cslib.Complexity.ComputableInPolyTimeWithOracle` and the program, run against the oracle
language `A`, makes at most `r n` requests on instances of encoded length `n`
(`Cslib.OracleComp.queriesWith`). The requests are counted against `A` itself, as in the usual
definition of a machine with oracle `A` making a bounded number of queries; the certificate's
clock bounds the requests against every oracle in any case
(`Cslib.Probability.IsOraclePPTOn.query_bounds`).

`P^{NP[O(log n)]}` (`Cslib.Complexity.PNPLog`) is the class of problems decided in polynomial time
with at most `c log₂ n + c` requests to some oracle language in `NP`, for a constant `c`
[Hemaspaandra and Ogihara, p. 1][HemaspaandraOgihara2002] [Kadin][Kadin1989]. It contains
`NP` and `coNP` with one request to the encodings of the satisfiable formulas
(`Cslib.Complexity.NP_subset_PWithOracleQueries_image_SAT`), through the Cook–Levin reduction, and
is closed under complement.

## Main definitions

* `Cslib.Complexity.ComputableInPolyTimeWithOracleQueries`: polynomial time relative to an oracle
  with a bounded number of requests.
* `Cslib.Complexity.PWithOracleQueries`: the problems so decided.
* `Cslib.Complexity.PNPLog`: `P^{NP[O(log n)]}`.

## Main results

* `Cslib.Complexity.ComputableInPolyTimeWithOracleQueries.computableInPolyTimeWithOracle`,
  `.mono`, `.map`: forgetting and weakening the bound, and postprocessing.
* `Turing.MultiTapeTM.ComputableInPolyTime.computableInPolyTimeWithOracleQueries`: polynomial time
  makes no request.
* `Cslib.Complexity.computableInPolyTimeWithOracleQueries_query`: one request
  (`Cslib.Complexity.queryBit`) decides membership of a polynomial-time request word.
* `Cslib.Complexity.compl_mem_PWithOracleQueries`, `Cslib.Complexity.compl_mem_PNPLog`: closure
  under complement.
* `Cslib.Complexity.NP_subset_PWithOracleQueries_image_SAT`: one request to `SAT` decides a
  problem in `NP`.
* `Cslib.Complexity.P_subset_PNPLog`, `Cslib.Complexity.NP_subset_PNPLog`,
  `Cslib.Complexity.coNP_subset_PNPLog`, `Cslib.Complexity.PNPLog_subset_PWithOracle`.

## References

* [L. A. Hemaspaandra, M. Ogihara, *The Complexity Theory Companion*][HemaspaandraOgihara2002]
* [J. Kadin, *P^{NP[O(log n)]} and sparse Turing-complete sets for NP*][Kadin1989]
-/

@[expose] public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM Cslib.Logic.PL

variable {α β γ : Type}

/-- `f` is computable in polynomial time relative to the oracle language `A` with at most `r n`
requests on instances of encoded length `n`: one deterministic word-query program has the
certificate of `ComputableInPolyTimeWithOracle`, computes `f` against `A`, and makes at most
`r (input a).length` requests on `a` against `A`. -/
def ComputableInPolyTimeWithOracleQueries (A : Set (List Bool)) (r : ℕ → ℕ) (f : α → β)
    (input : α ↪ List Bool) (output : β ↪ List Bool) : Prop :=
  ∃ program : α → WordQueryComp Unit β,
    IsOraclePPTOn input output (fun a => OracleComp.interpret ProbOracleComp.query (program a)) ∧
      ∀ a, OracleComp.interpret (m := Id) (languageOracle A) (program a) = f a ∧
        (OracleComp.queriesWith (languageOracle A) (program a)).length ≤ r (input a).length

namespace ComputableInPolyTimeWithOracleQueries

variable {A : Set (List Bool)} {r r' : ℕ → ℕ} {input : α ↪ List Bool} {middle : β ↪ List Bool}
  {output : γ ↪ List Bool}

/-- A bounded number of requests is in particular polynomial time relative to the oracle. -/
theorem computableInPolyTimeWithOracle {f : α → β}
    (h : ComputableInPolyTimeWithOracleQueries A r f input middle) :
    ComputableInPolyTimeWithOracle A f input middle :=
  let ⟨program, hprogram, heq⟩ := h
  ⟨program, hprogram, fun a => (heq a).1⟩

/-- Weakening the bound on the requests. -/
theorem mono {f : α → β} (h : ComputableInPolyTimeWithOracleQueries A r f input middle)
    (hr : ∀ n, r n ≤ r' n) : ComputableInPolyTimeWithOracleQueries A r' f input middle :=
  let ⟨program, hprogram, heq⟩ := h
  ⟨program, hprogram, fun a => ⟨(heq a).1, (heq a).2.trans (hr _)⟩⟩

/-- Polynomial-time postprocessing of the result makes no further request. -/
theorem map {f : α → β} {g : β → γ} (h : ComputableInPolyTimeWithOracleQueries A r f input middle)
    (hg : ComputableInPolyTime g middle output) :
    ComputableInPolyTimeWithOracleQueries A r (fun a => g (f a)) input output := by
  obtain ⟨program, hprogram, heq⟩ := h
  refine ⟨fun a => g <$> program a, ?_, fun a => ⟨?_, ?_⟩⟩
  · simpa only [OracleComp.interpret_map] using hprogram.map' hg
  · rw [OracleComp.interpret_map, (heq a).1]
    rfl
  · rw [OracleComp.queriesWith_map]
    exact (heq a).2

end ComputableInPolyTimeWithOracleQueries

/-- A polynomial-time computation makes no request. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.computableInPolyTimeWithOracleQueries
    {f : α → β} {input : α ↪ List Bool} {output : β ↪ List Bool}
    (h : ComputableInPolyTime f input output) (A : Set (List Bool)) (r : ℕ → ℕ) :
    ComputableInPolyTimeWithOracleQueries A r f input output :=
  ⟨fun a => pure (f a), h.isOraclePPTOn, fun _ => ⟨rfl, by simp⟩⟩

open Classical in
/-- **One request** to `A` for the polynomial-time word `req a` decides whether `req a ∈ A`. -/
theorem computableInPolyTimeWithOracleQueries_query {req : α → List Bool}
    {input : α ↪ List Bool} (hreq : ComputableInPolyTime req input encBits)
    (A : Set (List Bool)) :
    ComputableInPolyTimeWithOracleQueries A (fun _ => 1) (fun a => decide (req a ∈ A)) input
      encBool :=
  ⟨fun a => queryBit (req a), isOraclePPTOn_queryBit hreq,
    fun a => ⟨interpret_queryBit A (req a), by simp⟩⟩

/-- The problems decided in polynomial time relative to the oracle language `A` with at most
`r n` requests on instances of encoded length `n`. -/
def PWithOracleQueries (A : Set (List Bool)) (r : ℕ → ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ f : α → Bool, ComputableInPolyTimeWithOracleQueries A r f enc encBool ∧
    ∀ a, a ∈ L ↔ f a = true}

theorem mem_PWithOracleQueries {A : Set (List Bool)} {r : ℕ → ℕ} {enc : α ↪ List Bool}
    {L : Set α} :
    L ∈ PWithOracleQueries A r enc ↔ ∃ f : α → Bool,
      ComputableInPolyTimeWithOracleQueries A r f enc encBool ∧ ∀ a, a ∈ L ↔ f a = true :=
  Iff.rfl

/-- **`P^{NP[O(log n)]}`**: the problems decided in polynomial time with at most `c log₂ n + c`
requests, on instances of encoded length `n`, to some oracle language in `NP`
[Hemaspaandra and Ogihara, p. 1][HemaspaandraOgihara2002] [Kadin][Kadin1989]. -/
def PNPLog (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ A ∈ NP encBits, ⋃ c : ℕ, PWithOracleQueries A (fun n => c * Nat.log 2 n + c) enc

theorem mem_PNPLog {enc : α ↪ List Bool} {L : Set α} :
    L ∈ PNPLog enc ↔ ∃ A ∈ NP encBits, ∃ c : ℕ,
      L ∈ PWithOracleQueries A (fun n => c * Nat.log 2 n + c) enc := by
  simp only [PNPLog, Set.mem_iUnion, exists_prop]

section

variable {A : Set (List Bool)} {r r' : ℕ → ℕ} {enc : α ↪ List Bool} {L : Set α}

theorem PWithOracleQueries_subset_PWithOracle :
    PWithOracleQueries A r enc ⊆ PWithOracle A enc := fun _ ⟨f, hf, hL⟩ =>
  ⟨f, hf.computableInPolyTimeWithOracle, hL⟩

theorem PWithOracleQueries_mono (hr : ∀ n, r n ≤ r' n) :
    PWithOracleQueries A r enc ⊆ PWithOracleQueries A r' enc := fun _ ⟨f, hf, hL⟩ =>
  ⟨f, hf.mono hr, hL⟩

/-- A problem in `P` is decided with no request. -/
theorem P_subset_PWithOracleQueries (A : Set (List Bool)) (r : ℕ → ℕ) (enc : α ↪ List Bool) :
    P enc ⊆ PWithOracleQueries A r enc := fun _ ⟨f, hf, hL⟩ =>
  ⟨f, hf.computableInPolyTimeWithOracleQueries A r, hL⟩

/-- **Closure under complement**: negate the decider, with the same requests. -/
theorem compl_mem_PWithOracleQueries (hL : L ∈ PWithOracleQueries A r enc) :
    Lᶜ ∈ PWithOracleQueries A r enc := by
  obtain ⟨f, hf, hL⟩ := hL
  refine ⟨fun a => !f a, hf.map (by fun_prop), fun a => ?_⟩
  rw [Set.mem_compl_iff, hL a]
  simp

open Classical in
/-- A problem that reduces in polynomial time to the oracle language is decided with one
request. -/
theorem mem_PWithOracleQueries_of_reduction {req : α → List Bool}
    (hreq : ComputableInPolyTime req enc encBits) (h : ∀ a, a ∈ L ↔ req a ∈ A) :
    L ∈ PWithOracleQueries A (fun _ => 1) enc :=
  ⟨_, computableInPolyTimeWithOracleQueries_query hreq A, fun a => by
    rw [h a, decide_eq_true_iff]⟩

/-- **One request to `SAT` decides a problem in `NP`**: the request is the encoding of the
Cook–Levin reduction of the instance. -/
theorem NP_subset_PWithOracleQueries_image_SAT (enc : α ↪ List Bool) :
    NP enc ⊆ PWithOracleQueries (encCNF '' SAT) (fun _ => 1) enc := by
  intro L hL
  obtain ⟨f, hf, hfL⟩ := CookLevin.SAT_npHard enc L hL
  have henc : ComputableInPolyTime (fun φ : CNF ℕ => encCNF φ) encCNF encBits :=
    .of_eq fun _ => rfl
  refine mem_PWithOracleQueries_of_reduction (req := fun a => encCNF (f a)) (henc.comp hf)
    fun a => ?_
  rw [hfL a]
  exact ⟨fun h => ⟨f a, h, rfl⟩, fun ⟨_, h, he⟩ => encCNF.injective he ▸ h⟩

/-- A problem decided with `c log₂ n + c` requests to an oracle language in `NP` is in
`P^{NP[O(log n)]}`. -/
theorem mem_PNPLog_of_mem_PWithOracleQueries (hA : A ∈ NP encBits) {c : ℕ}
    (hL : L ∈ PWithOracleQueries A (fun n => c * Nat.log 2 n + c) enc) : L ∈ PNPLog enc :=
  mem_PNPLog.mpr ⟨A, hA, c, hL⟩

/-- **`P^{NP[O(log n)]}` is closed under complement.** -/
theorem compl_mem_PNPLog (hL : L ∈ PNPLog enc) : Lᶜ ∈ PNPLog enc := by
  obtain ⟨A, hA, c, hL⟩ := mem_PNPLog.mp hL
  exact mem_PNPLog_of_mem_PWithOracleQueries hA (compl_mem_PWithOracleQueries hL)

/-- `P ⊆ P^{NP[O(log n)]}`. -/
theorem P_subset_PNPLog (enc : α ↪ List Bool) : P enc ⊆ PNPLog enc := fun _ hL =>
  mem_PNPLog_of_mem_PWithOracleQueries image_SAT_mem_NP
    (P_subset_PWithOracleQueries _ (fun n => 0 * Nat.log 2 n + 0) enc hL)

/-- **`NP ⊆ P^{NP[O(log n)]}`**, with one request to `SAT`. -/
theorem NP_subset_PNPLog (enc : α ↪ List Bool) : NP enc ⊆ PNPLog enc := fun _ hL =>
  mem_PNPLog_of_mem_PWithOracleQueries (c := 1) image_SAT_mem_NP
    (PWithOracleQueries_mono (fun n => by omega) (NP_subset_PWithOracleQueries_image_SAT enc hL))

/-- **`coNP ⊆ P^{NP[O(log n)]}`**. -/
theorem coNP_subset_PNPLog (enc : α ↪ List Bool) : coNP enc ⊆ PNPLog enc := fun _ hL => by
  simpa only [compl_compl] using compl_mem_PNPLog (NP_subset_PNPLog enc hL)

/-- `P^{NP[O(log n)]} ⊆ P^{NP}`. -/
theorem PNPLog_subset_PWithOracle (enc : α ↪ List Bool) :
    PNPLog enc ⊆ ⋃ A ∈ NP encBits, PWithOracle A enc := by
  intro L hL
  obtain ⟨A, hA, c, hL⟩ := mem_PNPLog.mp hL
  exact Set.mem_biUnion hA (PWithOracleQueries_subset_PWithOracle hL)

end

end Cslib.Complexity
