/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.MINKTStar.Generator
import CslibFrontier.Computability.Kolmogorov.TimeBounded.PolyTime
import CslibFrontier.Computability.MCSP.PartialHardness.EvaluatorPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# The `MINKT*` generator runs in polynomial time

The generator witness of `Cslib.Kolmogorov.MINKTStar.Generator` prints a table consistent with the
partial truth table of the CMMSA construction. This module shows that printing it is
polynomial-time in the encoded witness (`GenWitness.computableInPolyTime_generate`), for fixed `Δ`
and `k`. A machine for `generate`, followed by the encoded witness, is then a program for the table
(`exists_timeBounded_of_computableInPolyTime`). With a step budget that is a fixed polynomial of the
size bound, this makes the `MINKT*` instance of the CMMSA table a yes-instance
(`exists_toMINKTStar_mem`).

* **The witness.** The instance, `λ` in unary and the tables are fields of the witness. The input
  numbered `x` is read in binary, and its term choice is entry `x mod 2 ^ indexWidth` of the unary
  list of choices. The parity is then the evaluator of the CMMSA construction, whose polynomial time
  is `PartialMCSP.FromCMMSA.computableInPolyTime_termParityN`.
* **The table.** The `2 ^ L` inputs are enumerated in unary; `2 ^ L` is polynomial in `|I|` and `λ`
  for every instance (`PartialMCSP.FromCMMSA.two_pow_inputLength_le`), and `λ` is unary in the
  witness, so the table is polynomial in the encoded witness.
* **The program.** `exists_timeBounded_of_computableInPolyTime` gives a monotone polynomial `pG` and
  a constant `c` with `K^t (generate w) ≤ |enc w| + c` whenever `t ≥ pG (|enc w|)`. For the honest
  witness, `|enc w| ≤ sizeBound Δ I λ`, so the step budget `pG (sizeBound Δ I λ + c)` and the size
  threshold `sizeBound Δ I λ + c` suffice. The universal machine simulates at the same step count
  (`DescriptionMethod.exists_etimeBoundedComplexity_universalTM_le_ofMultiTapeTM`), so no overhead
  factor enters the budget.

## Main definitions

* `Cslib.Kolmogorov.MINKTStar.toMINKTStar`: the `MINKT*` instance of the CMMSA table for the
  functions `f`, with a step budget and a size threshold.

## Main results

* `Cslib.Kolmogorov.MINKTStar.GenWitness.computableInPolyTime_generate`: the printed table is
  polynomial-time in the encoded witness.
* `Cslib.Kolmogorov.MINKTStar.GenWitness.computableInPolyTime_sizeBound`: the size bound is
  polynomial-time, in unary.
* `Cslib.Kolmogorov.MINKTStar.computableInPolyTime_toMINKTStar`: the `MINKT*` instance is
  polynomial-time from explicit tables of the functions.
* `Cslib.Kolmogorov.MINKTStar.exists_toMINKTStar_mem`: **Yes completeness**. For a Yes instance of
  `GapCMMSA`, every `λ ≥ 1` and every choice of the functions, the `MINKT*` instance with step
  budget `pG (sizeBound Δ I λ + c)` and size threshold `sizeBound Δ I λ + c` is a yes-instance.

## References

The generator and its analysis are the library's own. They give the yes case of the library's
proof of the `MINKT*` clause of [Hirahara2022, Theorem I.2], `MINKTStar.rpHard` in `Hardness.lean`.

* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
-/

public section

namespace Cslib.Kolmogorov.MINKTStar

open Cslib.Complexity Cslib.PartialMCSP.FromCMMSA Turing.MultiTapeTM

variable {α : Type} {input : α ↪ List Bool}

namespace GenWitness

/-- **The printed table is polynomial-time** in the witness, for fixed `Δ` and `k`: the instance
(in `CMMSAInstance.encoding`), `λ` and the term choices in unary, and the tables. -/
@[fun_prop]
theorem computableInPolyTime_generate (Δ k : ℕ) {w : α → GenWitness}
    (hw : ComputableInPolyTime w input enc) :
    ComputableInPolyTime (fun a => generate Δ k (w a)) input encBits := by
  have hI := enc_inst_polyTime hw
  have hlam := enc_lam_polyTime hw
  have h₁ := ComputableInPolyTime.fst input encUnary
  have hx := ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd input encUnary)
  have hj := computableInPolyTime_mod_two_pow_indexWidth (hI.comp h₁) hx
  have ht := ComputableInPolyTime.listGetD_binary (encA := encUnary) (encL := encList encUnary) 0
    (enc_choice_polyTime (hw.comp h₁)) hj
  unfold generate genEntry
  exact ComputableInPolyTime.mapToBitsWithInput
    (ComputableInPolyTime.unary_range' (computableInPolyTime_two_pow_inputLength Δ k hI hlam))
    (computableInPolyTime_termParityN Δ k (hI.comp h₁) (hlam.comp h₁)
      (enc_tables_polyTime (hw.comp h₁)) hx ht)

end GenWitness

/-- **The size bound is polynomial-time**, in unary, from the instance and `λ` in unary. -/
@[fun_prop]
theorem GenWitness.computableInPolyTime_sizeBound (Δ : ℕ) {I : α → CMMSAInstance} {lam : α → ℕ}
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam input encUnary) :
    ComputableInPolyTime (fun a => GenWitness.sizeBound Δ (I a) (lam a)) input encUnary := by
  unfold GenWitness.sizeBound
  exact ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const _)
      ((ComputableInPolyTime.encoding_length _).comp hI)) (ComputableInPolyTime.const 3))
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 4)
        (CMMSAInstance.isPolyTime_threshold hI)) (ComputableInPolyTime.const 2)) hlam)

/-- **The `MINKT*` instance of the CMMSA table** for the functions `f`: the partial truth table of
the CMMSA construction, in the order of `BitString.equivFin`, with step budget `t` and size
threshold `s`. -/
@[expose] def toMINKTStar (I : CMMSAInstance) (Δ k lam : ℕ) (f : VarFunctions I lam) (t s : ℕ) :
    Instance :=
  ⟨List.ofFn fun i => entry (Δ := Δ) (k := k) f ((BitString.equivFin _).symm i), t, s⟩

/-- **The `MINKT*` instance is polynomial-time from explicit tables**, for fixed `Δ` and `k`. If
`T a` has the table of every variable of `I a` under the functions `f a`, and the budget and the
threshold are polynomial-time in unary, then `toMINKTStar (I a) Δ k (lam a) (f a) (t a) (s a)` is
computed in polynomial time from the instance, `λ` in unary and the tables. -/
theorem computableInPolyTime_toMINKTStar {I : α → CMMSAInstance} {lam t s : α → ℕ}
    {T : α → List (List Bool)} {f : (a : α) → VarFunctions (I a) (lam a)} (Δ k : ℕ)
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam input encUnary)
    (hT : ComputableInPolyTime T input (encList encBits))
    (hf : ∀ a v, IsVarTable (I a) (lam a) (f a) (T a) v)
    (ht : ComputableInPolyTime t input encUnary) (hs : ComputableInPolyTime s input encUnary) :
    ComputableInPolyTime (fun a => toMINKTStar (I a) Δ k (lam a) (f a) (t a) (s a)) input enc :=
  ((computableInPolyTime_tableN Δ k hI hlam hT).prod (ht.prod hs)).of_enc_eq fun a => by
    rw [enc_apply, tableN_eq_ofFn (hf a) 0]
    rfl

/-- **Yes completeness of the `MINKT*` table.** There are a monotone polynomial `pG` and a constant
`c` such that, for every Yes instance `I` of `GapCMMSA Δ g σ`, every `λ ≥ 1` and every choice of
the functions `f`, the `MINKT*` instance of the CMMSA table with step budget
`pG (sizeBound Δ I λ + c)` and size threshold `sizeBound Δ I λ + c` is a yes-instance. The
polynomial and the constant depend only on `Δ` and `k`. -/
theorem exists_toMINKTStar_mem (Δ k : ℕ) :
    ∃ (pG : Polynomial ℕ) (c : ℕ), Monotone pG.eval ∧
      ∀ (g σ : ℝ) (I : CMMSAInstance), I ∈ (GapCMMSA Δ g σ).yes → ∀ lam, 1 ≤ lam →
        ∀ f : VarFunctions I lam,
          toMINKTStar I Δ k lam f (pG.eval (GenWitness.sizeBound Δ I lam + c))
            (GenWitness.sizeBound Δ I lam + c) ∈ MINKTStar := by
  obtain ⟨pG, c, -, hmono, hK⟩ := exists_timeBounded_of_computableInPolyTime
    (GenWitness.computableInPolyTime_generate Δ k ComputableInPolyTime.id')
  refine ⟨pG, c, hmono, fun g σ I hI lam hlam f => ?_⟩
  obtain ⟨w, rfl, rfl, hcons, hsize⟩ := GenWitness.exists_consistent_generate Δ k hI hlam f
  have hlen : (GenWitness.enc w).length + c ≤ GenWitness.sizeBound Δ w.inst w.lam + c :=
    Nat.add_le_add_right hsize c
  refine ⟨_, hcons, ?_⟩
  calc timeBoundedAt (pG.eval (GenWitness.sizeBound Δ w.inst w.lam + c)) (w.generate Δ k)
      = timeBounded (fun _ => pG.eval (GenWitness.sizeBound Δ w.inst w.lam + c))
          (w.generate Δ k) := rfl
    _ ≤ ((GenWitness.enc w).length + c : ℕ) :=
        hK (t := fun _ => _) w (hmono (hsize.trans (Nat.le_add_right _ _)))
    _ ≤ ((GenWitness.sizeBound Δ w.inst w.lam + c : ℕ) : ℕ∞) := Nat.cast_le.mpr hlen

end Cslib.Kolmogorov.MINKTStar
