/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Approximation.LabelCover.Incidence
public import Complexity.Computability.PCP.Approximation.LabelCover.Repetition
public import Complexity.Computability.PCP.Encoded.Deloop
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap

/-!
# Label Cover with arbitrarily small soundness

Label Cover is NP-hard with perfect completeness and arbitrarily small soundness, at the price of
alphabets that grow as the soundness shrinks: Raz's parallel repetition lemma reduces the
soundness of the two-query projection PCP to an arbitrarily small constant
[Arora and Barak, Theorem 19.3 and the first paragraph of Section 19.4][AroraBarak07].
The reduction composes three polynomial-time steps.

1. Loop removal (`Cslib.PCP.Encoded.Graph.deloop`) makes the hard binary constraint graphs of
   `Cslib.Complexity.GapTwoCSP_npHard` loopless without changing their value.
2. The incidence construction (`Cslib.PCP.Encoded.LabelCoverIncidence.reduce`) turns a loopless
   binary constraint graph into a Label Cover instance without parallel edges, losing a factor of
   at most two in the unsatisfied fraction.
3. The `k`-fold parallel repetition (`Cslib.PCP.Encoded.LabelCoverRepetition.pow`) keeps
   satisfiability, and parallel repetition for instances without parallel edges
   (`Cslib.PCP.Encoded.LabelCoverRepetition.one_sub_unsatVal_pow_le`) bounds the value of the
   repetition of a no-instance.

For each fixed `k` the repetition is polynomial-time (`isPolyTime_pow`): the output has `m ^ k`
edges for `m` input edges, each with a complete table on `(Fin k → β)` and unary endpoints below
`(n + 1) ^ (2 ^ k)` for `n` input vertices. The degree of the polynomial is exponential in `k`.

**Scope.** This is Raz's parallel repetition theorem [Raz1998] applied to the library's own PCP
instance, through Holenstein's explicit bound [Holenstein2009]. The constants are explicit but
astronomically large: with `128²` left and `128` right labels per coordinate, the soundness after
`k` rounds is `(1 - 2⁻¹⁸⁶ / 6000)^{k / 21}`. The loop removal and the two-left-vertex
contradiction instance are library adaptations to the executable graph API.

## Main results

* `Cslib.PCP.Encoded.LabelCoverRepetition.isPolyTime_pow`: for each fixed `k`, the `k`-fold
  repetition is polynomial-time under the framed graph and table encodings.
* `Cslib.Complexity.polyTimeReducible_GapTwoCSP_GapLabelCover_pow`: the composed reduction
  from binary CSP to `k`-fold repeated Label Cover, for any finite alphabet.
* `Cslib.Complexity.GapLabelCover_npHard_pow`: Label Cover over `k`-tuples of the PCP alphabet is
  NP-hard at soundness `(1 - 2⁻¹⁸⁶ / 6000)^{k / 21}`.
* `Cslib.Complexity.exists_GapLabelCover_npHard`: **for every `δ ∈ (0, 1)` some number of
  rounds `k` makes Label Cover NP-hard at completeness `1` and soundness `δ`.**

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft,
  Sections 19.1 and 19.4][AroraBarak07]
* [R. Raz, *A parallel repetition theorem*][Raz1998]
* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.LabelCoverRepetition

open Turing.MultiTapeTM

variable {β γ : Type}

/-- The vertex count of the repetition is polynomial-time for each fixed `k`. -/
private theorem isPolyTime_tupleCode_const (k : ℕ) :
    ComputableInPolyTime (fun n : ℕ => tupleCode k fun _ => n) encUnary encUnary := by
  induction k with
  | zero => exact .const 0
  | succ k ih =>
    exact (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_pair).comp
      (ComputableInPolyTime.id'.prod ih)

variable [Fintype β] [Finite γ]

/-- Prepending a computed edge to a computed repeated edge is polynomial-time; the combined
table is a function of the two finite tables. -/
private theorem isPolyTime_consEdge {k : ℕ} {Input : Type} {input : Input ↪ List Bool}
    {encG : γ ↪ List Bool} {d : Input → Edge (β → γ)}
    {e : Input → Edge ((Fin k → β) → Fin k → γ)}
    (hd : ComputableInPolyTime d input (Edge.encoding (encPi encG)))
    (he : ComputableInPolyTime e input (Edge.encoding (encPi (encPi encG)))) :
    ComputableInPolyTime (fun x => consEdge (d x) (e x)) input
      (Edge.encoding (encPi (encPi encG))) := by
  have hpair := ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_pair
  have hc : ComputableInPolyTime
      (fun p : (β → γ) × ((Fin k → β) → Fin k → γ) =>
        fun a : Fin (k + 1) → β => (Fin.cons (p.1 (a 0)) (p.2 (Fin.tail a)) : Fin (k + 1) → γ))
      (encPair (encPi encG) (encPi (encPi encG))) (encPi (encPi encG)) := .of_finite _
  exact Edge.isPolyTime_mk
    (hpair.comp ((Edge.isPolyTime_src hd).prod (Edge.isPolyTime_src he)))
    (hpair.comp ((Edge.isPolyTime_dst hd).prod (Edge.isPolyTime_dst he)))
    (hc.comp ((Edge.isPolyTime_constraint hd).prod (Edge.isPolyTime_constraint he)))

private theorem isPolyTime_edges_pow (encG : γ ↪ List Bool) (k : ℕ) :
    ComputableInPolyTime (fun g : Graph (β → γ) => (pow k g).edges)
      (Graph.encoding (encPi encG)) (encList (Edge.encoding (encPi (encPi encG)))) := by
  induction k with
  | zero => exact .const _
  | succ k ih =>
    have hg : ComputableInPolyTime (fun g : Graph (β → γ) => g)
        (Graph.encoding (encPi encG)) (Graph.encoding (encPi encG)) := .id'
    have hinner : ComputableInPolyTime
        (fun p : Graph (β → γ) × Edge (β → γ) => (pow k p.1).edges.map (consEdge p.2))
        (encPair (Graph.encoding (encPi encG)) (Edge.encoding (encPi encG)))
        (encList (Edge.encoding (encPi (encPi encG)))) :=
      ComputableInPolyTime.mapWithInput (f := fun p e => consEdge p.2 e)
        (ih.comp (.fst _ _))
        (isPolyTime_consEdge ((ComputableInPolyTime.snd _ _).comp (.fst _ _)) (.snd _ _))
    have h := ComputableInPolyTime.flatMapWithInput
      (f := fun g d => (pow k g).edges.map (consEdge d)) (Graph.isPolyTime_edges hg) hinner
    simpa only [edges_pow_succ] using h

/-- **For each fixed `k` the `k`-fold repetition is polynomial-time.** The output lists the
`m ^ k` tuples of the `m` input edges, each with unary endpoints and a complete table on
`(Fin k → β)`; for fixed `k` and fixed alphabets this is polynomial in the input length.

The polynomial degree grows exponentially in `k`. Iterated `Nat.pair` numbers the `k`-tuples of
the `n` input vertices below `(n + 1) ^ (2 ^ k)` (`vertices_pow_le`), and the endpoints and the
vertex count are written in unary, so for fixed alphabets the output of a well-formed input has
size about `m ^ k * (n + 1) ^ (2 ^ k)`. The statement is therefore polynomial time for each fixed
`k` only, which is all the NP-hardness reductions below use. A mixed-radix numbering would give
degree linear in `k`. -/
@[fun_prop]
theorem isPolyTime_pow (encG : γ ↪ List Bool) (k : ℕ) :
    ComputableInPolyTime (pow (β := β) (γ := γ) k)
      (Graph.encoding (encPi encG)) (Graph.encoding (encPi (encPi encG))) := by
  have hg : ComputableInPolyTime (fun g : Graph (β → γ) => g)
      (Graph.encoding (encPi encG)) (Graph.encoding (encPi encG)) := .id'
  exact Graph.isPolyTime_mk
    (ComputableInPolyTime.unary_add'
      ((isPolyTime_tupleCode_const k).comp (Graph.isPolyTime_vertices hg)) (.const 1))
    (isPolyTime_edges_pow encG k)

end Cslib.PCP.Encoded.LabelCoverRepetition

namespace Cslib.Complexity

open Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

/-- **Binary CSP reduces to repeated Label Cover.** For a finite alphabet `α` with two distinct
symbols, loop removal, the incidence construction and `k` rounds of parallel repetition reduce
`GapTwoCSP α (1 - ε)` to Label Cover over `k`-tuples of pairs of symbols and `k`-tuples of
symbols, with perfect completeness and soundness
`(1 - (ε / 2)³ / 6000)^{k / log₂ |α|³}`. -/
theorem polyTimeReducible_GapTwoCSP_GapLabelCover_pow {α : Type} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) (encA : α ↪ List Bool) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {k : ℕ} (hk : 0 < k) :
    PromiseProblem.PolyTimeReducible (Graph.encoding encConstraintTable)
      (Graph.encoding (encPi (encPi encA))) (GapTwoCSP α (1 - ε))
      (GapLabelCover (Fin k → α × α) (Fin k → α) 1
        ((1 - (ε / 2) ^ 3 / 6000) ^
          ((k : ℝ) / Real.logb 2 (Fintype.card (α × α) * Fintype.card α)))) := by
  let : Nonempty α := ⟨a⟩
  let pairs : List (α × α) := Finset.univ.toList
  have hpairs : ∀ p, p ∈ pairs := fun p => Finset.mem_toList.mpr (Finset.mem_univ p)
  have hcard : 2 ≤ Fintype.card (α × α) * Fintype.card α := by
    have h2 : 2 ≤ Fintype.card α := Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
    rw [Fintype.card_prod]
    nlinarith
  set s := (1 - (ε / 2) ^ 3 / 6000) ^
    ((k : ℝ) / Real.logb 2 (Fintype.card (α × α) * Fintype.card α)) with hs
  have hs1 : s < 1 := by
    have hlog : 0 < Real.logb 2 (Fintype.card (α × α) * Fintype.card α) :=
      Real.logb_pos one_lt_two (by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hcard)
    have he0 : 0 < (ε / 2) ^ 3 := by positivity
    have he1 : (ε / 2) ^ 3 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    rw [hs]
    exact Real.rpow_lt_one (by linarith) (by linarith) (div_pos (by exact_mod_cast hk) hlog)
  refine ⟨fun g => LabelCoverRepetition.pow k
      (LabelCoverIncidence.reduce pairs a b (Graph.deloop g)),
    (LabelCoverRepetition.isPolyTime_pow encA k).comp
      ((LabelCoverIncidence.isPolyTime_reduce pairs a b encA).comp Graph.isPolyTime_deloop),
    fun g hg => ?_, fun g hg => ?_⟩
  · have hsat := LabelCoverRepetition.satisfiable_pow k
      (LabelCoverIncidence.satisfiable_reduce pairs hpairs a b
        ((Graph.satisfiable_deloop_iff g).mpr (mem_yes_GapTwoCSP.mp hg)))
    rw [GapLabelCover, PromiseProblem.mem_yes_gapMax,
      (ConstraintGraph.unsatVal_eq_zero_iff _).mpr hsat]
    norm_num
  · have hno := (mem_no_GapTwoCSP (by linarith)).mp hg
    have hgap := LabelCoverIncidence.half_unsatVal_le_reduce pairs a b hab (Graph.deloop g)
    rw [Graph.unsatVal_deloop] at hgap
    have hpow := LabelCoverRepetition.one_sub_unsatVal_pow_le
      (LabelCoverIncidence.noParallelEdges_reduce pairs a b (Graph.isLoopless_deloop g)) hcard
      (ε := ε / 2) (by linarith) k
    rw [GapLabelCover, PromiseProblem.mem_no_gapMax]
    exact ⟨hpow, by simpa using hs1⟩

/-- **Label Cover is NP-hard at soundness `(1 - 2⁻¹⁸⁶ / 6000)^{k / 21}`** for every `k ≥ 1`, with
perfect completeness, `128^{2k}` left labels (`k`-tuples of pairs of symbols of the PCP alphabet
`Bool × (Fin 6 → Bool)`) and `128^k` right labels. This is Raz's parallel repetition theorem
[Raz1998] applied to the library's PCP instance `GapTwoCSP_npHard`, with Holenstein's explicit,
astronomically large constants [Holenstein2009]. -/
theorem GapLabelCover_npHard_pow {k : ℕ} (hk : 0 < k) :
    PromiseProblem.NPHard
      (Graph.encoding (encPi (encPi (encPair encBool (encPi encBool)))))
      (GapLabelCover (Fin k → (Bool × (Fin 6 → Bool)) × (Bool × (Fin 6 → Bool)))
        (Fin k → Bool × (Fin 6 → Bool)) 1
        ((1 - 1 / (6000 * 2 ^ 186)) ^ ((k : ℝ) / 21))) := by
  have hred := polyTimeReducible_GapTwoCSP_GapLabelCover_pow
    (false, fun _ : Fin 6 => false) (true, fun _ : Fin 6 => false) (by decide)
    (encPair encBool (encPi encBool)) (ε := 1 / 2 ^ 61) (by positivity) (by norm_num) hk
  have hcard : Real.logb 2 (Fintype.card ((Bool × (Fin 6 → Bool)) × (Bool × (Fin 6 → Bool))) *
      Fintype.card (Bool × (Fin 6 → Bool))) = 21 := by
    rw [show (Fintype.card ((Bool × (Fin 6 → Bool)) × (Bool × (Fin 6 → Bool))) *
      Fintype.card (Bool × (Fin 6 → Bool)) : ℝ) = 2 ^ (21 : ℝ) by
        simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fun, Fintype.card_fin]
        norm_num]
    exact Real.logb_rpow (by norm_num) (by norm_num)
  rw [hcard, show (1 - (1 / 2 ^ 61 / 2 : ℝ) ^ 3 / 6000) = 1 - 1 / (6000 * 2 ^ 186) by norm_num]
    at hred
  exact GapTwoCSP_npHard.trans hred

/-- **Label Cover with arbitrarily small soundness is NP-hard**: for every `δ ∈ (0, 1)` there is a
number of rounds `k` such that Label Cover with `128^{2k}` left labels and `128^k` right labels is
NP-hard at completeness `1` and soundness `δ`. The number `k` depends on `δ`: any `k = 21 n`
with `n ≥ 1` and `(1 - 2⁻¹⁸⁶ / 6000)^n ≤ δ` works, so `k` is astronomically large. -/
theorem exists_GapLabelCover_npHard {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ k : ℕ, 0 < k ∧ PromiseProblem.NPHard
      (Graph.encoding (encPi (encPi (encPair encBool (encPi encBool)))))
      (GapLabelCover (Fin k → (Bool × (Fin 6 → Bool)) × (Bool × (Fin 6 → Bool)))
        (Fin k → Bool × (Fin 6 → Bool)) 1 δ) := by
  set c : ℝ := 1 - 1 / (6000 * 2 ^ 186) with hc
  have hc0 : 0 ≤ c := by rw [hc]; norm_num
  have hc1 : c < 1 := by rw [hc]; norm_num
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hc1
  refine ⟨21 * (n + 1), by positivity, (GapLabelCover_npHard_pow (by positivity)).mono
    (fun g hg => hg) fun g hg => ?_⟩
  have hpow : c ^ (((21 * (n + 1) : ℕ) : ℝ) / 21) = c ^ (n + 1) := by
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  rw [GapLabelCover, PromiseProblem.mem_no_gapMax] at hg ⊢
  rw [hpow] at hg
  exact ⟨hg.1.trans ((pow_le_pow_of_le_one hc0 hc1.le (Nat.le_succ n)).trans hn.le), hδ1⟩

end Cslib.Complexity
