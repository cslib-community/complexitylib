/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Reduction.Isomorphism.Conjecture
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Tests for the Berman–Hartmanis isomorphism theory

* A concrete use of the polynomial-time Cantor–Schröder–Bernstein theorem: words of even length
  and words of odd length are polynomial-time isomorphic, through `true :: w` and `List.tail`.
* A positive and a negative instance of paddability: the words of even length are paddable, a
  nonempty finite language is not.
* Concrete runs of the SAT padding: the padding clause, read-back, and the preservation of
  satisfiability on a satisfiable and an unsatisfiable formula.
* Client use of the SAT-variant isomorphisms through transitivity.
-/

open Turing.MultiTapeTM Cslib.Complexity Cslib.Logic.PL

namespace ComplexityTests.BermanHartmanis

/-! ### Cantor–Schröder–Bernstein on a concrete pair of languages -/

theorem computableInPolyTime_cons_true :
    ComputableInPolyTime (fun w : List Bool => true :: w) encBits encBits :=
  (ComputableTidilyInPolyTime.bitsCons (ComputableTidilyInPolyTime.const true)
    ComputableTidilyInPolyTime.id').computableInPolyTime

theorem computableInPolyTime_tail : ComputableInPolyTime List.tail encBits encBits :=
  ComputableTidilyInPolyTime.bitsTail.computableInPolyTime

/-- Words of even length. -/
def EvenWords : Set (List Bool) := {w | Even w.length}

/-- Words of odd length. -/
def OddWords : Set (List Bool) := {w | Odd w.length}

/-- Prepending `true` is a length-increasing invertible one-one reduction between even-length
and odd-length words, in either direction. -/
theorem consTrue_reduces (A B : Set (List Bool))
    (h : ∀ w : List Bool, w ∈ A ↔ (true :: w) ∈ B) :
    PolyTimeInvertibleLengthIncreasingOneOneReducible encBits encBits A B :=
  ⟨fun w => true :: w, ⟨List.tail, computableInPolyTime_cons_true, computableInPolyTime_tail,
    fun _ => rfl, fun w => by simp only [encBits_apply, List.length_cons, Nat.lt_add_one]⟩, h⟩

/-- Even-length and odd-length words are polynomial-time isomorphic, by the polynomial-time
Cantor–Schröder–Bernstein theorem: neither `true :: ·` is onto, but the chain construction still
produces a bijection. -/
theorem polyTimeIsomorphic_even_odd : PolyTimeIsomorphic encBits encBits EvenWords OddWords :=
  (consTrue_reduces _ _ fun w => by
      simp only [EvenWords, OddWords, Set.mem_ofPred_eq, List.length_cons, Nat.odd_add_one,
        Nat.not_odd_iff_even]).polyTimeIsomorphic
    (consTrue_reduces _ _ fun w => by
      simp only [EvenWords, OddWords, Set.mem_ofPred_eq, List.length_cons, Nat.even_add_one,
        Nat.not_even_iff_odd])

/-- The isomorphism produced by `polyTime_schroeder_bernstein` is either `true :: ·` or the
inverse of `true :: ·` at every word, so on the empty word, which has no preimage, it is
`[true]`. -/
example : ∃ e : List Bool ≃ List Bool, e [] = [true] := by
  obtain ⟨e, -, he⟩ := polyTime_schroeder_bernstein computableInPolyTime_cons_true
    computableInPolyTime_tail computableInPolyTime_cons_true computableInPolyTime_tail
    (fun _ => rfl) (fun _ => rfl) (fun w => by simp only [encBits_apply, List.length_cons,
      Nat.lt_add_one]) (fun w => by simp only [encBits_apply, List.length_cons, Nat.lt_add_one])
  refine ⟨e, ?_⟩
  rcases he [] with h | h
  · exact h
  · exact absurd h (List.cons_ne_nil _ _)

/-! ### Paddability: a positive and a negative instance -/

/-- The words of even length are paddable: append the doubled framed padding, `frame y ++ frame y`,
whose length is even. -/
theorem evenWords_paddable : Paddable encBits EvenWords := by
  refine ⟨fun w y => frame y ++ frame y ++ w, fun w => unframe w, ?_,
    ComputableInPolyTime.unframe, fun w y => by simp only [List.append_assoc,
      unframe_frame_append], fun w y => ?_⟩
  · have hy : ComputableInPolyTime (fun p : List Bool × List Bool => frame p.2)
        (encPair encBits encBits) encBits :=
      ComputableInPolyTime.frame.comp (ComputableInPolyTime.snd encBits encBits)
    exact ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsAppend hy hy)
      (ComputableInPolyTime.fst encBits encBits)
  · simp only [EvenWords, Set.mem_ofPred_eq, List.length_append, length_frame]
    constructor
    · intro h
      rcases h with ⟨k, hk⟩
      exact ⟨k - (2 * y.length + 1), by omega⟩
    · intro h
      rcases h with ⟨k, hk⟩
      exact ⟨k + (2 * y.length + 1), by omega⟩

/-- A nonempty finite language is not paddable: padding a member is injective in the padding. -/
example : ¬Paddable encBits ({[]} : Set (List Bool)) := fun h =>
  (h.infinite ⟨[], rfl⟩) (Set.finite_singleton [])

/-- Padding the empty language is possible; together with the previous example, paddability
distinguishes `∅` from `{[]}`. -/
example : Paddable encBits (∅ : Set (List Bool)) :=
  ⟨fun _ y => y, id, ComputableInPolyTime.snd encBits encBits, ComputableInPolyTime.id',
    fun _ _ => rfl, fun _ _ => Iff.rfl⟩

/-! ### Concrete runs of the SAT padding -/

/-- Padding with `[true, false]` prepends the tautological clause on variable `5 = 0b101`. -/
example :
    SAT.pad [[(0, true)]] [true, false] = [[(5, true), (5, false), (5, true)], [(0, true)]] := by
  decide

/-- The padding is read back from the first clause. -/
example : SAT.unpad (SAT.pad [[(0, true)], [(1, false)]] [false, false, true, true, false]) =
    [false, false, true, true, false] := by
  decide

/-- A satisfiable formula stays satisfiable after padding. -/
example : SAT.pad [[(0, true)]] [true] ∈ SAT :=
  (SAT.satisfiable_pad _ _).2 ⟨fun _ => true, rfl⟩

/-- The empty clause stays unsatisfiable after padding. -/
example : SAT.pad [[]] [false, true] ∉ SAT := fun h =>
  absurd ((SAT.satisfiable_pad _ _).1 h) fun ⟨σ, hσ⟩ => by simp at hσ

/-- A width-four clause is not in `ThreeSAT`, and padding cannot change that. -/
example : SAT.pad [[(0, true), (1, true), (2, true), (3, true)]] [] ∉ ThreeSAT := fun h =>
  absurd (h.1 _ (List.mem_cons_of_mem _ List.mem_cons_self)) (by decide)

/-! ### Clients of the SAT-variant isomorphisms -/

/-- `ThreeSAT` and `NAEThreeSAT` are polynomial-time isomorphic, through `SAT`. -/
example : PolyTimeIsomorphic encCNF encCNF ThreeSAT NAEThreeSAT :=
  polyTimeIsomorphic_SAT_ThreeSAT.symm.trans polyTimeIsomorphic_SAT_NAEThreeSAT

/-- `ThreeSAT ∈ P ↔ ExactThreeSAT ∈ P`, from the isomorphisms. -/
example : ThreeSAT ∈ P encCNF ↔ ExactThreeSAT ∈ P encCNF :=
  (polyTimeIsomorphic_SAT_ThreeSAT.symm.trans polyTimeIsomorphic_SAT_ExactThreeSAT).mem_P_iff

/-- `UNSAT` is paddable, and so is its word language read through the formula decoder. -/
example : Paddable encBits (cnfDecoder.decode ⁻¹' UNSAT) :=
  UNSAT_paddable.preimage_decode cnfDecoder

/-- The typed and word models of `SAT` are polynomial-time isomorphic. -/
example : PolyTimeIsomorphic encCNF encBits SAT (cnfDecoder.decode ⁻¹' SAT) :=
  SAT_paddable.polyTimeIsomorphic_preimage_decode cnfDecoder

/-- Under the Berman–Hartmanis conjecture, `NAEThreeSAT` is not in `P`. -/
example (h : BermanHartmanisConjecture) : NAEThreeSAT ∉ P encCNF := fun hN =>
  h.SAT_notMem_P (polyTimeIsomorphic_SAT_NAEThreeSAT.mem_P_iff.2 hN)

end ComplexityTests.BermanHartmanis
