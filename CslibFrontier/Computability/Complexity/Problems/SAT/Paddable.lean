/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Problems.ExactThreeSAT
public import CslibFrontier.Computability.Complexity.Problems.NAEThreeSAT
public import CslibFrontier.Computability.Complexity.Reduction.Isomorphism.Paddable
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Paddability of SAT and its variants

`SAT`, `ThreeSAT`, `ExactThreeSAT` and `NAEThreeSAT` are paddable: prepend the clause
`[(N, true), (N, false), (N, true)]`, where `N` is the natural number whose little-endian binary
digits are `y ++ [true]`. The clause contains both literals of `N`, so it is true, and has both a
true and a false literal, under every assignment, and it has exactly three literals. Padding thus
preserves satisfiability, not-all-equal satisfiability, and every clause-width condition met by a
width-three clause. The padding `y` is read back from the binary digits of the first variable.

By the Berman–Hartmanis theorem for paddable languages
(`Cslib.Complexity.NPComplete.polyTimeIsomorphic_of_paddable`), these four `NP`-complete languages
are pairwise polynomial-time isomorphic, under the common encoding `Cslib.Complexity.encCNF`.

## Source and adaptations

The source version is the 1975 Cornell technical report
[Berman and Hartmanis][BermanHartmanis1975]. Locators in this file refer to that report; the
numbering of the 1977 journal version [Berman and Hartmanis][BermanHartmanis1977] has not been
checked. The corresponding source is the report's Theorem 7 and its CNF padding construction
(printed pp. 13–14); the isomorphisms also use §III, Theorem 1 and Lemmas 3 and 5 (printed
pp. 7–12), through `Cslib.Complexity.NPComplete.polyTimeIsomorphic_of_paddable`.

The padding gadget here is not the report's. The report's CNF construction pads with clauses over
fresh variables. The gadget here adds a single clause over one variable `N`, and the padding is
the binary representation of `N`. The variable need not be fresh, because the clause is true under
every assignment whether or not `N` occurs elsewhere in the formula. Keeping the gadget one
width-three clause with a true and a false literal also lets it serve `ThreeSAT`, `ExactThreeSAT`
and `NAEThreeSAT`, not only `SAT`. The decoder needed by the isomorphism theorems is
`Cslib.Complexity.cnfDecoder`.

## Main definitions

* `Cslib.Complexity.SAT.pad`, `Cslib.Complexity.SAT.unpad`: padding a formula with a tautological
  width-three clause, and reading the padding back.

## Main results

* `Cslib.Complexity.SAT.paddable_of_pad_mem_iff`: any formula language invariant under `SAT.pad`
  is paddable.
* `Cslib.Complexity.SAT_paddable`, `Cslib.Complexity.ThreeSAT_paddable`,
  `Cslib.Complexity.ExactThreeSAT_paddable`, `Cslib.Complexity.NAEThreeSAT_paddable`,
  `Cslib.Complexity.UNSAT_paddable`.
* `Cslib.Complexity.NPComplete.polyTimeIsomorphic_SAT_iff_paddable`: an `NP`-complete language
  with a total polynomial-time decoder is polynomial-time isomorphic to `SAT` exactly when it is
  paddable.
* `Cslib.Complexity.polyTimeIsomorphic_SAT_ThreeSAT`,
  `Cslib.Complexity.polyTimeIsomorphic_SAT_ExactThreeSAT`,
  `Cslib.Complexity.polyTimeIsomorphic_SAT_NAEThreeSAT`: `SAT` is polynomial-time isomorphic to
  each of the other three.

## References

* [L. Berman, J. Hartmanis, *On isomorphisms and density of NP and other complete
  sets*][BermanHartmanis1975], Cornell TR75-260 (1975), Theorem 7, §III, Theorem 1 and Lemmas 3
  and 5
* [L. Berman, J. Hartmanis, *On isomorphisms and density of NP and other complete
  sets*][BermanHartmanis1977], journal version (numbering not checked)
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

namespace SAT

/-- The tautological width-three clause recording the bit string `y` in its variable. -/
@[expose] def padClause (y : List Bool) : Clause ℕ :=
  [(ofBits (y ++ [true]), true), (ofBits (y ++ [true]), false), (ofBits (y ++ [true]), true)]

/-- Pad a formula with the bit string `y`, by prepending a tautological width-three clause. -/
@[expose] def pad (φ : CNF ℕ) (y : List Bool) : CNF ℕ := padClause y :: φ

/-- Read back the padding: the binary digits of the first variable, without the final `true`. -/
@[expose] def unpad (φ : CNF ℕ) : List Bool :=
  ((φ.headD []).headD (0, false)).1.bits.dropLast

/-- `unpad` inverts `pad` in the padding argument. -/
theorem unpad_pad (φ : CNF ℕ) (y : List Bool) : unpad (pad φ y) = y := by
  simp only [unpad, pad, padClause, List.headD_cons, bits_ofBits]
  rw [List.rdropWhile_concat_neg _ _ _ (by decide), List.dropLast_concat]

/-- The padding clause is true under every assignment. -/
theorem padClause_eval (σ : ℕ → Bool) (y : List Bool) : Clause.eval σ (padClause y) = true := by
  cases h : σ (ofBits (y ++ [true])) <;> simp [padClause, h]

/-- Padding preserves the value of a formula under every assignment. -/
theorem eval_pad (σ : ℕ → Bool) (φ : CNF ℕ) (y : List Bool) :
    (pad φ y).eval σ = φ.eval σ := by
  rw [pad, CNF.eval_cons, padClause_eval, Bool.true_and]

/-- Padding preserves not-all-equal evaluation under every assignment. -/
theorem evalNAE_pad (σ : ℕ → Bool) (φ : CNF ℕ) (y : List Bool) :
    (pad φ y).evalNAE σ = φ.evalNAE σ := by
  rw [CNF.evalNAE, CNF.evalNAE, eval_pad, eval_pad]

/-- Padding preserves satisfiability. -/
theorem satisfiable_pad (φ : CNF ℕ) (y : List Bool) :
    (pad φ y).Satisfiable ↔ φ.Satisfiable := by
  simp only [CNF.Satisfiable, eval_pad]

/-- Padding preserves not-all-equal satisfiability. -/
theorem naeSatisfiable_pad (φ : CNF ℕ) (y : List Bool) :
    (pad φ y).NAESatisfiable ↔ φ.NAESatisfiable := by
  simp only [CNF.NAESatisfiable, evalNAE_pad]

/-- A clause condition met by width-three clauses holds for every clause of a padded formula
exactly when it holds for every clause of the formula. -/
theorem forall_clause_pad {p : Clause ℕ → Prop} (hp : ∀ c : Clause ℕ, c.length = 3 → p c)
    (φ : CNF ℕ) (y : List Bool) : (∀ c ∈ pad φ y, p c) ↔ ∀ c ∈ φ, p c := by
  rw [pad, List.forall_mem_cons]
  exact ⟨fun h => h.2, fun h => ⟨hp _ rfl, h⟩⟩

/-- Padding is polynomial-time. -/
theorem computableInPolyTime_pad :
    ComputableInPolyTime (fun p : CNF ℕ × List Bool => pad p.1 p.2) (encPair encCNF encBits)
      encCNF := by
  have hN : ComputableInPolyTime (fun p : CNF ℕ × List Bool => ofBits (p.2 ++ [true]))
      (encPair encCNF encBits) encNat :=
    ComputableInPolyTime.bitsToNat.comp
      (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.snd encCNF encBits)
        (ComputableInPolyTime.const [true]))
  unfold pad padClause encCNF
  fun_prop

/-- Reading back the padding is polynomial-time. -/
theorem computableInPolyTime_unpad : ComputableInPolyTime unpad encCNF encBits := by
  have hv : ComputableInPolyTime (fun φ : CNF ℕ => ((φ.headD []).headD (0, false)).1) encCNF
      encNat := by
    unfold encCNF
    fun_prop
  have hbits : ComputableInPolyTime (fun φ : CNF ℕ => ((φ.headD []).headD (0, false)).1.bits)
      encCNF encBits := hv.of_enc_eq fun _ => rfl
  refine (ComputableInPolyTime.bitsTakeWithInput hbits
    (ComputableInPolyTime.unary_sub' (ComputableInPolyTime.length_bits.comp hbits)
      (ComputableInPolyTime.const 1))).of_enc_eq fun φ => ?_
  simp only [unpad, encBits_apply, List.dropLast_eq_take, Function.comp_apply]

/-- A formula language invariant under padding is paddable. -/
theorem paddable_of_pad_mem_iff {L : Set (CNF ℕ)} (h : ∀ φ y, pad φ y ∈ L ↔ φ ∈ L) :
    Paddable encCNF L :=
  ⟨pad, unpad, computableInPolyTime_pad, computableInPolyTime_unpad, unpad_pad, h⟩

end SAT

/-- `SAT` is paddable. Compare [Berman and Hartmanis][BermanHartmanis1975], Theorem 7 and its CNF
construction; `SAT.pad` replaces the report's fresh-variable gadget by a single clause. -/
theorem SAT_paddable : Paddable encCNF SAT :=
  SAT.paddable_of_pad_mem_iff fun φ y => SAT.satisfiable_pad φ y

/-- `UNSAT` is paddable. -/
theorem UNSAT_paddable : Paddable encCNF UNSAT :=
  SAT_paddable.compl

/-- `ThreeSAT` is paddable. -/
theorem ThreeSAT_paddable : Paddable encCNF ThreeSAT :=
  SAT.paddable_of_pad_mem_iff fun φ y => and_congr
    (SAT.forall_clause_pad (fun _ h => h.le) φ y) (SAT.satisfiable_pad φ y)

/-- `ExactThreeSAT` is paddable. -/
theorem ExactThreeSAT_paddable : Paddable encCNF ExactThreeSAT :=
  SAT.paddable_of_pad_mem_iff fun φ y => and_congr
    (SAT.forall_clause_pad (fun _ h => h) φ y) (SAT.satisfiable_pad φ y)

/-- `NAEThreeSAT` is paddable. -/
theorem NAEThreeSAT_paddable : Paddable encCNF NAEThreeSAT :=
  SAT.paddable_of_pad_mem_iff fun φ y => and_congr
    (SAT.forall_clause_pad (fun _ h => h.le) φ y) (SAT.naeSatisfiable_pad φ y)

/-- An `NP`-complete language, over an instance type with a total polynomial-time decoder, is
polynomial-time isomorphic to `SAT` exactly when it is paddable: the reverse direction is
[Berman and Hartmanis][BermanHartmanis1975], §III, Theorem 1 combined with Lemmas 3 and 5, applied
to `SAT_paddable`, and the forward direction is derived here (see
`Cslib.Complexity.NPComplete.polyTimeIsomorphic_iff_paddable`). The Berman–Hartmanis conjecture
therefore says, over such instance types, that every `NP`-complete language is paddable. -/
theorem NPComplete.polyTimeIsomorphic_SAT_iff_paddable {α : Type} {encA : α ↪ List Bool}
    {A : Set α} (hA : NPComplete encA A) (DA : Decoder encA) :
    PolyTimeIsomorphic encA encCNF A SAT ↔ Paddable encA A :=
  hA.polyTimeIsomorphic_iff_paddable CookLevin.SAT_npComplete SAT_paddable DA cnfDecoder

/-- `SAT` and `ThreeSAT` are polynomial-time isomorphic
([Berman and Hartmanis][BermanHartmanis1975], §III, Theorem 1 and Lemmas 3 and 5, with the
paddability of both languages from `SAT.pad`). -/
theorem polyTimeIsomorphic_SAT_ThreeSAT : PolyTimeIsomorphic encCNF encCNF SAT ThreeSAT :=
  CookLevin.SAT_npComplete.polyTimeIsomorphic_of_paddable ThreeSAT_npComplete SAT_paddable
    ThreeSAT_paddable cnfDecoder cnfDecoder

/-- `SAT` and `ExactThreeSAT` are polynomial-time isomorphic
([Berman and Hartmanis][BermanHartmanis1975], §III, Theorem 1 and Lemmas 3 and 5, with the
paddability of both languages from `SAT.pad`). -/
theorem polyTimeIsomorphic_SAT_ExactThreeSAT :
    PolyTimeIsomorphic encCNF encCNF SAT ExactThreeSAT :=
  CookLevin.SAT_npComplete.polyTimeIsomorphic_of_paddable ExactThreeSAT_npComplete SAT_paddable
    ExactThreeSAT_paddable cnfDecoder cnfDecoder

/-- `SAT` and `NAEThreeSAT` are polynomial-time isomorphic
([Berman and Hartmanis][BermanHartmanis1975], §III, Theorem 1 and Lemmas 3 and 5, with the
paddability of both languages from `SAT.pad`). -/
theorem polyTimeIsomorphic_SAT_NAEThreeSAT : PolyTimeIsomorphic encCNF encCNF SAT NAEThreeSAT :=
  CookLevin.SAT_npComplete.polyTimeIsomorphic_of_paddable NAEThreeSAT_npComplete SAT_paddable
    NAEThreeSAT_paddable cnfDecoder cnfDecoder

end Cslib.Complexity
