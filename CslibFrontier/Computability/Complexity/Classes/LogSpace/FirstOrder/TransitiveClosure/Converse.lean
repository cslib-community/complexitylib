/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.ConfigurationGraph
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.TransitiveClosure
public import CslibFrontier.Computability.Complexity.ImmermanVardi.Input
public import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple.Power
public import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple.TransitiveClosure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic
import CslibFrontier.Foundations.Relation.Transport
import CslibFrontier.Logics.FirstOrder.Encoding.PowerBound

/-!
# Nondeterministic logarithmic space in FO(TC)

On the library's canonically ordered finite structures, every query whose source-only encoded
language belongs to native `NL` is defined by one FO(TC) sentence whose closures all occur
positively. With the forward inclusion `TCDefinable.encodedLanguage_mem_NL`, this gives
FO(TC) = FO(positive TC) = NL.

A configuration of the logarithmic-space machine is a tuple of registers
(`ConfigurationGraph.stepFormula`), one universe element per register. On the power universe
`Fin (n ^ K)` with `K` chosen from the machine's space bound, every reachable configuration fits,
so the acceptance sentence `∃ X Y, start X ∧ accept Y ∧ TC[step](X, Y)` holds exactly when the
machine accepts. Pullback along the canonical full-tuple interpretation gives one sentence over
the original input universe.

## Main definitions

* `Cslib.Complexity.ConfigurationGraph.acceptanceSentence`: some start register tuple reaches an
  accepting one by a single positive closure of `stepFormula`.

## Main results

* `Cslib.Complexity.ConfigurationGraph.realize_acceptanceSentence`: the acceptance sentence holds
  exactly when the machine accepts, on every universe containing all reachable registers.
  `realize_acceptanceSentence_closureBy` states this for every transported closure semantics
  whose transform fixes the register step relation.
* `Cslib.Logic.Vocabulary.exists_pow_fits`: a power universe `n ^ K` holds every reachable
  configuration of a logarithmic-space machine.
* `Cslib.Logic.FO.Ordered.exists_sentence_of_decidesInSpace`: the sentence for a
  logarithmic-space decider, under every such closure semantics.
* `Cslib.Logic.FO.Ordered.PosTCDefinable.of_encodedLanguage_mem_NL`: NL ⊆ FO(positive TC).
* `Cslib.Logic.FO.Ordered.posTCDefinable_iff_encodedLanguage_mem_NL`,
  `Cslib.Logic.FO.Ordered.tcDefinable_iff_encodedLanguage_mem_NL`: FO(positive TC) and FO(TC)
  capture native `NL`.
* `Cslib.Logic.FO.Ordered.tcDefinable_iff_posTCDefinable`: negated closures add nothing.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*, Theorem 3.1][Immerman1987]:
  NL is the class of queries definable in FO(positive TC) on ordered structures. Its proof codes
  an instantaneous description by a fixed tuple of variables and takes one closure of the
  first-order successor relation. Here a description is a tuple of registers on a power universe,
  and the numeric vocabulary is order, BIT, zero, one and maximum rather than successor, zero and
  maximum.
* [N. Immerman, *Nondeterministic Space is Closed Under Complementation*][Immerman1988],
  Corollary 3: FO(positive TC) = FO(TC).
-/

public section

open FirstOrder Language Turing Cslib.Turing Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered
open Turing.MultiTapeNTM.ConfigurationGraph

namespace Cslib.Complexity.ConfigurationGraph

variable {L : Language} {k : ℕ} {State : Type} [Fintype State]

variable (L) in
/-- **Acceptance by reachability**: some start register tuple reaches a halted register tuple
with output tag `1` along `stepFormula`. The sentence has one closure, of width the number of
registers, at positive polarity. -/
noncomputable def acceptanceSentence (inputFormula : Option Bool → (language L).Formula (Fin 1))
    (lengthFormula : (language L).Formula (Fin 1)) (ntm : MultiTapeNTM k Bool State) :
    Operator.Formula (language L) TC.shape [] Empty :=
  Operator.Formula.exs (2 * Fintype.card (Register k))
    (.conj (.ofFO (startFormula L ntm fun r =>
        .var (.inr (TC.left id (Fintype.equivFin (Register k) r)))))
      (.conj (.ofFO (acceptFormula L State fun r =>
          .var (.inr (TC.right id (Fintype.equivFin (Register k) r)))))
        (TC.tc (.ofFO (stepFormula L inputFormula lengthFormula ntm
            (fun r => .var (.inr (TC.left id (Fintype.equivFin (Register k) r))))
            (fun r => .var (.inr (TC.right id (Fintype.equivFin (Register k) r))))))
          (TC.pair (fun i => .var (.inr (TC.left id i)))
            (fun i => .var (.inr (TC.right id i)))))))

/-- The acceptance sentence uses its closure positively. -/
@[simp] theorem positive_acceptanceSentence
    (inputFormula : Option Bool → (language L).Formula (Fin 1))
    (lengthFormula : (language L).Formula (Fin 1)) (ntm : MultiTapeNTM k Bool State) :
    TC.Positive (acceptanceSentence L inputFormula lengthFormula ntm) true := by
  rw [acceptanceSentence, TC.positive_exs]
  exact ⟨trivial, trivial, rfl, trivial⟩

private theorem pair_left_id {A : Type*} {m : ℕ} (xs ys : Fin m → A) (i : Fin m) :
    TC.pair xs ys (TC.left id i) = xs i :=
  congrFun (TC.left_pair xs ys) i

private theorem pair_right_id {A : Type*} {m : ℕ} (xs ys : Fin m → A) (i : Fin m) :
    TC.pair xs ys (TC.right id i) = ys i :=
  congrFun (TC.right_pair xs ys) i

variable {N : ℕ} [Fact (2 ≤ N)] [L.Structure (Fin N)]

/-- **The acceptance sentence decides acceptance** under every transported closure semantics
`TC.Tuple.closureBy T` whose transform fixes the register step relation on `Fin N`: on a universe
`Fin N` that contains the input length and every register of every reachable configuration, the
sentence holds exactly when the machine accepts. Ordinary closure is `T = id`
(`realize_acceptanceSentence`); deterministic closure is the deterministic reduct, which fixes the
step relation of a deterministic machine. -/
theorem realize_acceptanceSentence_closureBy
    {T : ∀ {β : Type}, (β → β → Prop) → β → β → Prop} (hT : TC.Tuple.Transports T)
    {inputFormula : Option Bool → (language L).Formula (Fin 1)}
    {lengthFormula : (language L).Formula (Fin 1)} {w : List Bool}
    (hinput : ∀ s (a : Fin N), (inputFormula s).Realize ![a] ↔ inputAt w a.val = s)
    (hlen : ∀ a : Fin N, lengthFormula.Realize ![a] ↔ w.length = a.val) (hn : w.length < N)
    (ntm : MultiTapeNTM k Bool State)
    (hstep : T (fun x y : Register k → Fin N =>
        RegisterStep ntm w (fun i => (x i).val) (fun i => (y i).val)) =
      fun x y => RegisterStep ntm w (fun i => (x i).val) (fun i => (y i).val))
    (hfit : ∀ v, Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v →
      Fits N (registers v)) :
    (acceptanceSentence L inputFormula lengthFormula ntm).Realize (M := Fin N)
        (TC.Tuple.closureBy T) Operator.RelEnv.empty Empty.elim ↔ ntm.Accepts w := by
  let E : (Fin (Fintype.card (Register k)) → Fin N) ≃ (Register k → Fin N) :=
    { toFun := fun x i => x (Fintype.equivFin (Register k) i)
      invFun := fun x i => x ((Fintype.equivFin (Register k)).symm i)
      left_inv := fun x => funext fun i => by simp only [Equiv.apply_symm_apply]
      right_inv := fun x => funext fun i => by simp only [Equiv.symm_apply_apply] }
  let S := fun x y : Register k → Fin N =>
    RegisterStep ntm w (fun i => (x i).val) (fun i => (y i).val)
  -- closure tuples are register tuples, read through the enumeration of the registers
  have hpath : ∀ a b, Relation.ReflTransGen (T fun x y => S (E x) (E y)) a b ↔
      Relation.ReflTransGen S (E a) (E b) :=
    Relation.reflTransGen_equiv_iff E fun a b =>
      (hT E (s := S) (fun _ _ => Iff.rfl) a b).trans (iff_of_eq (congrFun (congrFun hstep _) _))
  rw [accepts_iff_registerStep_fin hfit]
  simp only [acceptanceSentence, Operator.Formula.realize_exs, Operator.Formula.realize_conj,
    Operator.Formula.realize_ofFO, TC.Tuple.realize_tc_closureBy, TC.left_pair, TC.right_pair,
    realize_startFormula, realize_acceptFormula, realize_stepFormula hinput hlen hn,
    Term.realize_var, Sum.elim_inr, pair_left_id, pair_right_id]
  constructor
  · rintro ⟨xs, hs, ⟨hc, ho⟩, hr⟩
    exact ⟨E (TC.left xs), E (TC.right xs), hs, (hpath _ _).mp hr, hc, ho⟩
  · rintro ⟨x, y, hs, hr, hc, ho⟩
    refine ⟨TC.pair (E.symm x) (E.symm y), ?_, ⟨?_, ?_⟩, ?_⟩
    · simpa only [pair_left_id, E, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply] using hs
    · simpa only [pair_right_id, E, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply] using hc
    · simpa only [pair_right_id, E, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply] using ho
    · simp only [pair_left_id, pair_right_id]
      exact (hpath _ _).mpr (by simpa only [Equiv.apply_symm_apply] using hr)

/-- **The acceptance sentence decides acceptance**: on a universe `Fin N` that contains the
input length and every register of every reachable configuration, the acceptance sentence holds
exactly when the machine accepts. -/
theorem realize_acceptanceSentence {inputFormula : Option Bool → (language L).Formula (Fin 1)}
    {lengthFormula : (language L).Formula (Fin 1)} {w : List Bool}
    (hinput : ∀ s (a : Fin N), (inputFormula s).Realize ![a] ↔ inputAt w a.val = s)
    (hlen : ∀ a : Fin N, lengthFormula.Realize ![a] ↔ w.length = a.val) (hn : w.length < N)
    (ntm : MultiTapeNTM k Bool State)
    (hfit : ∀ v, Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v →
      Fits N (registers v)) :
    (acceptanceSentence L inputFormula lengthFormula ntm).Realize (M := Fin N)
        TC.interpretation Operator.RelEnv.empty Empty.elim ↔ ntm.Accepts w :=
  realize_acceptanceSentence_closureBy TC.Tuple.transports_id hinput hlen hn ntm rfl hfit

end Cslib.Complexity.ConfigurationGraph

namespace Cslib.Logic.Vocabulary

open Cslib.Complexity

/-- **Logarithmic-space configurations fit a power universe**: for a vocabulary and a space
constant there is a power `K ≥ 1` bounding all relation arities such that on every well-formed
input of cardinality at least two, the power universe `a.1 ^ K` is longer than the encoding and
contains every register of every view reachable by a machine with states `State` that runs within
space `c * (log₂ n + 1)`. -/
theorem exists_pow_fits {L : Language} (v : Vocabulary L) (State : Type) [Fintype State]
    (c : ℕ) :
    ∃ K : ℕ, 1 ≤ K ∧ (∀ i : Fin v.count, v.arity i ≤ K) ∧
      ∀ a : EncodedStructure, v.WellFormed a → 2 ≤ a.1 →
        ∀ {k : ℕ} {ntm : MultiTapeNTM k Bool State},
          ntm.RunsInSpace (encStructure a) (c * (Nat.log2 (encStructure a).length + 1)) →
          (encStructure a).length < a.1 ^ K ∧
            ∀ u, Relation.ReflTransGen ntm.ViewStep (ntm.initView (encStructure a)) u →
              Fits (a.1 ^ K) (registers u) := by
  obtain ⟨K, hK, har, hpow⟩ := v.exists_pow_bound
    (fun n => n + radix (radixExponent State c) n) (by unfold radix; fun_prop)
  refine ⟨K, hK, har, fun a ha h2 k ntm hs => ?_⟩
  have hb : (encStructure a).length + radix (radixExponent State c) (encStructure a).length <
      a.1 ^ K := hpow a ha h2
  exact ⟨by omega, fun _ hv i => (fits_of_runsInSpace c hs hv i).trans_le (by omega)⟩

end Cslib.Logic.Vocabulary

namespace Cslib.Logic.FO.Ordered

open Cslib.Complexity Cslib.Complexity.ConfigurationGraph Turing.MultiTapeTM

/-- **A machine sentence for every logarithmic-space decider**: a query whose source-only encoded
language is decided by a native machine within logarithmic space is defined by one sentence with a
single positive closure, read under every transported closure semantics `TC.Tuple.closureBy T`
whose transform fixes the machine's register step relation on every `Fin N`. Ordinary closure
gives NL ⊆ FO(positive TC); deterministic closure and a deterministic machine give
L ⊆ FO(DTC). -/
theorem exists_sentence_of_decidesInSpace {L : Language} [L.IsRelational] (v : Vocabulary L)
    {K : Query L} {T : ∀ {β : Type}, (β → β → Prop) → β → β → Prop}
    (hT : TC.Tuple.Transports T) {k : ℕ} {State : Type} [Fintype State]
    {ntm : MultiTapeNTM k Bool State} {c : ℕ}
    (hdec : ntm.DecidesInSpace encStructure (K.encodedLanguage v)
      fun a => c * (Nat.log2 (encStructure a).length + 1))
    (hstep : ∀ (w : List Bool) (N : ℕ), T (fun x y : Register k → Fin N =>
        RegisterStep ntm w (fun i => (x i).val) (fun i => (y i).val)) =
      fun x y => RegisterStep ntm w (fun i => (x i).val) (fun i => (y i).val)) :
    ∃ φ : Operator.Formula (language L) TC.shape [] Empty, TC.Positive φ true ∧
      ∀ M : Structure L,
        M ∈ K ↔ φ.Realize (M := M) (TC.Tuple.closureBy T) Operator.RelEnv.empty Empty.elim := by
  obtain ⟨K', hK', har, hpow⟩ := v.exists_pow_fits State c
  let I := v.orderedPowerInterpretation K' har
  let ψ := acceptanceSentence v.powerLanguage v.inputSymbol v.inputLength ntm
  refine ⟨I.onTCSentence ψ, (I.positive_onTCSentence ψ true).mpr
    (positive_acceptanceSentence _ _ ntm), fun M => ?_⟩
  let a := encode v M
  have ha : v.WellFormed a := v.wellFormed_encode M (Equiv.refl M)
  obtain ⟨hn, hfit⟩ := hpow a ha M.size_ge_two ((hdec.1 a).1)
  change _ < M.size ^ K' at hn
  change ∀ u, _ → Fits (M.size ^ K') _ at hfit
  let _ : Fact (2 ≤ M.size ^ K') := ⟨FullTupleInterpretation.two_le_pow (n := M.size) hK'⟩
  let _ := v.powerStructure a (M.size ^ K')
  have haccept : ψ.Realize (M := Fin (M.size ^ K')) (TC.Tuple.closureBy T)
      Operator.RelEnv.empty Empty.elim ↔ ntm.Accepts (encStructure a) :=
    realize_acceptanceSentence_closureBy hT (v.realize_inputSymbol ha hn)
      (v.realize_inputLength ha hn) hn ntm (hstep _ _) hfit
  rw [I.realize_onTCSentence_closureBy hT hK' ψ]
  have he := v.inputStructure_orderedPowerInterpretation K' har hK' M
  change I.inputStructure (n := M.size) = v.powerStructure a (M.size ^ K') at he
  rw [he]
  exact (mem_encodedLanguage_encode v K M).symm.trans ((hdec.1 a).2.trans haccept.symm)

/-- **NL ⊆ FO(positive TC)** on canonically ordered structures: a query whose source-only
encoded language is decided by a native nondeterministic logarithmic-space machine is defined by
one FO(TC) sentence with a single, positive closure. -/
theorem PosTCDefinable.of_encodedLanguage_mem_NL {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} (hK : K.encodedLanguage v ∈ NL encStructure) :
    PosTCDefinable K := by
  obtain ⟨tapes, State, _, ntm, c, hdec⟩ := hK
  let _ := Fintype.ofFinite State
  exact exists_sentence_of_decidesInSpace v TC.Tuple.transports_id hdec fun _ _ => rfl

/-- **FO(positive TC) captures NL**: a single FO(TC) sentence with positive closures defines an
ordered query exactly when its source-only language is in native nondeterministic logarithmic
space. -/
theorem posTCDefinable_iff_encodedLanguage_mem_NL {L : Language} [L.IsRelational]
    (v : Vocabulary L) (K : Query L) :
    PosTCDefinable K ↔ K.encodedLanguage v ∈ NL encStructure :=
  ⟨fun h => h.encodedLanguage_mem_NL v, PosTCDefinable.of_encodedLanguage_mem_NL v⟩

/-- **FO(TC) captures NL** ([Immerman1988], Corollary 3): a single FO(TC) sentence defines an
ordered query exactly when its source-only language is in native nondeterministic logarithmic
space. -/
theorem tcDefinable_iff_encodedLanguage_mem_NL {L : Language} [L.IsRelational]
    (v : Vocabulary L) (K : Query L) :
    TCDefinable K ↔ K.encodedLanguage v ∈ NL encStructure :=
  ⟨fun h => h.encodedLanguage_mem_NL v,
    fun h => (PosTCDefinable.of_encodedLanguage_mem_NL v h).tcDefinable⟩

/-- **Negated closures add nothing** on canonically ordered structures: every FO(TC) query has a
sentence whose closures all occur positively. -/
theorem tcDefinable_iff_posTCDefinable {L : Language} [L.IsRelational] (v : Vocabulary L)
    (K : Query L) : TCDefinable K ↔ PosTCDefinable K :=
  (tcDefinable_iff_encodedLanguage_mem_NL v K).trans
    (posTCDefinable_iff_encodedLanguage_mem_NL v K).symm

end Cslib.Logic.FO.Ordered
