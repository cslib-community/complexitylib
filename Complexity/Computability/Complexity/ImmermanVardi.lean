/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P.FirstOrder
public import Complexity.Computability.Complexity.ImmermanVardi.Tableau.Acceptance
public import Complexity.Computability.Complexity.ImmermanVardi.Input
public import Complexity.Logics.FirstOrder.Ordered.FullTuple.LeastFixedPoint
public import Complexity.Logics.FirstOrder.Ordered.FullTuple.Power
import Complexity.Computability.Complexity.Fagin.Converse

/-!
# The Immerman–Vardi characterization of polynomial time

On the library's canonically ordered finite structures, a query is definable by one checked
FO(LFP) sentence exactly when its source-only encoded language belongs to native `P`.
The vocabulary is finite and relational; its fixed enumeration determines truth-table order.
Universes are `Fin n` with `n ≥ 2`. Order, BIT, zero, one, and maximum are canonical numeric
symbols, computed from the universe size rather than supplied as input tables.

The forward direction compiles a fixed formula to a native polynomial-time model checker.
For the converse, a native deterministic machine has a positive local tableau. Its input
symbols are defined directly from the actual binary encoding. A fixed tuple width bounds the
machine's time, input length, and finite feature tags for all input sizes. Pullback along the
canonical full-tuple interpretation gives one sentence over the original input universe.

## Main results

* `FO.Ordered.LFPDefinable.of_encodedLanguage_mem_P`: every native polynomial-time ordered
  query has a uniform checked FO(LFP) sentence.
* `FO.Ordered.lfpDefinable_iff_encodedLanguage_mem_P`: FO(LFP) captures native polynomial time.

## References

* [N. Immerman, *Relational Queries Computable in Polynomial Time*][Immerman1986], Theorem 1
  and Section 3. The theorem is instantiated here at the existing canonical ordered vocabulary
  and unary-cardinality/full-truth-table encoding. Malformed table shapes and universes below
  two are rejected.
-/

public section

open FirstOrder Language Turing Turing.MultiTapeTM

namespace Cslib.Logic

namespace Vocabulary

variable {L : Language} (v : Vocabulary L)

/-- A single tuple dimension contains the input, runtime, and fixed finite feature tags of a
polynomial-time native machine, uniformly over well-formed ordered structures. -/
theorem exists_lfp_power_bound (t : ℕ → ℕ) (ht : Cslib.PolynomiallyBounded t) (tags : ℕ) :
    ∃ k : ℕ, 1 ≤ k ∧ (∀ i : Fin v.count, v.arity i ≤ k) ∧
      ∀ a : EncodedStructure, v.WellFormed a → 2 ≤ a.1 →
        (encStructure a).length + 1 < a.1 ^ k ∧
        t (encStructure a).length < a.1 ^ k ∧ tags ≤ a.1 ^ k := by
  obtain ⟨c, d, htime⟩ := Cslib.polynomiallyBounded_iff_le.mp ht
  obtain ⟨k, hk, har, hpow⟩ := v.exists_pow_bound 0 (c + tags) d
  refine ⟨k, hk, har, fun a ha hn => ?_⟩
  obtain ⟨hinput, hclock⟩ := hpow a ha hn
  simp only [Polynomial.eval_zero, Nat.add_zero] at hinput hclock
  have hlen : (encStructure a).length + 1 ≤ (frame (encStructure a)).length + 1 := by
    rw [length_frame]
    omega
  have ht' : t (encStructure a).length ≤
      (c + tags) * ((frame (encStructure a)).length + 1) ^ d :=
    (htime _).trans (Nat.mul_le_mul (Nat.le_add_right c tags)
      (Nat.pow_le_pow_left hlen d))
  have hp : 1 ≤ ((frame (encStructure a)).length + 1) ^ d :=
    Nat.one_le_pow _ _ (by omega)
  have htags : tags ≤ (c + tags) * ((frame (encStructure a)).length + 1) ^ d :=
    calc tags ≤ c + tags := Nat.le_add_left _ _
         _ = (c + tags) * 1 := (Nat.mul_one _).symm
         _ ≤ _ := Nat.mul_le_mul_left _ hp
  exact ⟨by omega, by omega, by omega⟩

end Vocabulary

namespace FO.Ordered

open Cslib.Complexity

/-- Every ordered query decided by an actual native polynomial-time machine is defined by one
checked FO(LFP) sentence over the original ordered input structures. -/
theorem LFPDefinable.of_encodedLanguage_mem_P {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} (hK : K.encodedLanguage v ∈ P encStructure) :
    LFPDefinable K := by
  classical
  obtain ⟨f, ⟨t, _, ht, _, m, State, hfinite, tm, htm⟩, hdec⟩ := hK
  let _ := hfinite
  let _ := Fintype.ofFinite State
  obtain ⟨k, hk, har, hpow⟩ :=
    v.exists_lfp_power_bound t ht (Fintype.card (ImmermanVardi.Tableau.Tag m State))
  let A := {a : EncodedStructure // v.WellFormed a ∧ 2 ≤ a.1}
  let size (a : A) := a.val.1 ^ k
  let input (a : A) := encStructure a.val
  let inst (a : A) : v.powerLanguage.Structure (Fin (size a)) :=
    v.powerStructure a.val (size a)
  let instSize (a : A) : Fact (2 ≤ size a) := by
    let _ : Fact (2 ≤ a.val.1) := ⟨a.property.2⟩
    exact ⟨FullTupleInterpretation.two_le_pow (n := a.val.1) hk⟩
  have hb (a : A) :
      (input a).length + 1 < size a ∧ t (input a).length < size a ∧
        Fintype.card (ImmermanVardi.Tableau.Tag m State) ≤ size a :=
    hpow a.val a.property.1 a.property.2
  obtain ⟨ψ, hψ⟩ := ImmermanVardi.Tableau.exists_acceptance_sentence
    (L := v.powerLanguage) (size := size) tm input v.inputSymbol
    (fun a s p => v.realize_inputSymbol a.property.1
      ((Nat.lt_succ_self _).trans (hb a).1) s p)
    (fun a => (hb a).1) (fun a => (hb a).2.2)
  let I := v.orderedPowerInterpretation k har
  refine ⟨I.onLFPSentence ψ, fun M => ?_⟩
  let a : A := ⟨encode v M, v.wellFormed_encode M (Equiv.refl M), M.size_ge_two⟩
  have hm := (htm (encode v M)).runFrom_of_le
    (show t (input a).length ≤ size a - 1 by have := (hb a).2.1; omega)
  have haccept : ψ.Realize (M := Fin (size a)) Operator.RelEnv.empty Empty.elim ↔
      f (encode v M) = true := by
    have hψ' := hψ a
    have hv (v : Empty → Fin (size a)) : v = Empty.elim := Subsingleton.elim _ _
    simp only [hv] at hψ'
    rw [hψ']
    change ((tm.runFrom (tm.initCfg (encStructure (encode v M))) (size a - 1)).Halted ∧
      (tm.runFrom (tm.initCfg (encStructure (encode v M))) (size a - 1)).output = [true]) ↔ _
    simp only [hm.2, encBool_apply, List.singleton_inj]
    exact ⟨And.right, fun h => ⟨hm.1, h⟩⟩
  have hquery : M ∈ K ↔ f (encode v M) = true :=
    (mem_encodedLanguage_encode v K M).symm.trans (hdec (encode v M))
  rw [I.realize_onLFPSentence hk ψ]
  have he := v.inputStructure_orderedPowerInterpretation k har hk M
  change I.inputStructure (n := M.size) = inst a at he
  rw [he]
  exact hquery.trans haccept.symm

/-- **Immerman–Vardi:** a single checked FO(LFP) sentence defines an ordered query exactly
when its source-only language is decidable in native polynomial time. -/
theorem lfpDefinable_iff_encodedLanguage_mem_P {L : Language} [L.IsRelational]
    (v : Vocabulary L) (K : Query L) :
    LFPDefinable K ↔ K.encodedLanguage v ∈ P encStructure :=
  ⟨fun h => h.encodedLanguage_mem_P v, LFPDefinable.of_encodedLanguage_mem_P v⟩

end FO.Ordered
end Cslib.Logic
