/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.Runtime.Parameters
public import Complexity.Computability.Circuit.Rational.Runtime.Point
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Foundations.Data.List.Append

/-!
# Polynomial-time rational hitting-list generator

This module assembles the polynomial-time rational hitting-list generator from the certified
parameter schedule (`Complexity/Computability/Circuit/Rational/Runtime/Parameters.lean`), the staged
division-free integer determinant
(`Complexity/Computability/Circuit/Rational/Runtime/Determinant.lean`), the integer lift tables
(`Complexity/Computability/Circuit/Rational/Runtime/Lift.lean`), the reduced-rational
binary encoding (`Complexity/Computability/Circuit/Rational/Runtime/Encode.lean`), and the per-point
Cramer normalization
(`Complexity/Computability/Circuit/Rational/Runtime/Point.lean`).

Given parameters `(n, s)`, `gridPointWords` enumerates the three-dimensional grid
`{1, …, H}³` in lexicographic order and collects the encoded normalized tuples emitted at all
nonsingular points. `outputWord` prepends the self-delimiting binary encodings of the common
matrix dimension `M * Dg` and the emitted tuple count `words.length`, and `hittingListWord n s`
instantiates `outputWord` at `Parameters.truncation n s`, `Parameters.ambientDimension n s`,
`CyclotomicRing.degree (Parameters.exponent n s)`, and `Parameters.gridSize n s`, agreeing with
`encodeOutput (hittingList n s)` for all `n, s : ℕ` (`hittingListWord_eq`).

For a standalone `List Bool → List Bool` generator, `inputWord n s` encodes `(n, s)` as the unary
word `true ^ n ++ [false] ++ true ^ s`, `parseInput` recovers `some (n, s)` when `1 ≤ n`, `1 ≤ s`,
and `w = inputWord n s` (and `none` otherwise), and `hittingGenerator` emits
`encodeOutput (hittingList n s)` on valid inputs and `[]` on malformed inputs.

## Main definitions

* `Cslib.Circuits.Rational.gridPointWords`: list of encoded tuples emitted across the `{1, …, H}³`
  grid.
* `Cslib.Circuits.Rational.outputWord`, `Cslib.Circuits.Rational.hittingListWord`: complete binary
  encoding of the generator output for fixed parameters and for the selected parameter schedule.
* `Cslib.Circuits.Rational.inputWord`, `Cslib.Circuits.Rational.parseInput`: unary input format
  `true ^ n ++ [false] ++ true ^ s` and its parser.
* `Cslib.Circuits.Rational.hittingGenerator`: the standalone `List Bool → List Bool` hitting-list
  generator.

## Main results

* `Cslib.Circuits.Rational.gridPointWords_eq`, `Cslib.Circuits.Rational.outputWord_eq`,
  `Cslib.Circuits.Rational.hittingListWord_eq`: agreement with `ExecutableGenerator.output` and
  `encodeOutput (hittingList n s)`.
* `Cslib.Circuits.Rational.hittingList_polytime`: `(n, s) ↦ encodeOutput (hittingList n s)` is
  computable in polynomial time from unary `(n, s)`.
* `Cslib.Circuits.Rational.parseInput_eq_some_iff`, `Cslib.Circuits.Rational.parseInput_inputWord`,
  `Cslib.Circuits.Rational.parseInput_eq_none_iff`: exact characterization of `parseInput`.
* `Cslib.Circuits.Rational.hittingGenerator_inputWord`,
  `Cslib.Circuits.Rational.hittingGenerator_eq_nil`,
  `Cslib.Circuits.Rational.hittingGenerator_eq_nil_of_parseInput_eq_none`: behavior of
  `hittingGenerator` on valid and malformed inputs.
* `Cslib.Circuits.Rational.hittingGenerator_polytime`: `hittingGenerator` is computable in
  polynomial time over `encBits`.
* `Cslib.Circuits.Rational.hittingGenerator_spec`: packaged end-to-end polynomial-time,
  dimension-bound, encoding-length, and hitting specification for `hittingGenerator`.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf787 (files
  lean/OAI/Computability/RationalHitting/GridEnumeration.lean and PolynomialTime.lean), via the
  complexitylib port [Schlesinger2026RationalHitting] at revision
  add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits.Rational

/-! ### Grid enumeration and complete output encoding -/

/-- List of encoded normalized tuples emitted across the `{1, …, H}³` grid in lexicographic
order. -/
def gridPointWords (n N M Dg H : ℕ) : List (List Bool) :=
  (List.range H).flatMap fun t =>
    (List.range H).flatMap fun p =>
      (List.range H).flatMap fun r =>
        pointWords n N M Dg (t + 1) (p + 1) (r + 1)

/-- Complete binary encoding of the generator output for parameters `(n, N, M, Dg, H)`: the
encoded matrix dimension `M * Dg`, the encoded emitted tuple count, and the concatenation of all
emitted tuple encodings. -/
def outputWord (n N M Dg H : ℕ) : List Bool :=
  let words := gridPointWords n N M Dg H
  encodeNat (M * Dg) ++ encodeNat words.length ++ words.flatten

/-- Complete binary encoding of the hitting list at the selected parameters for `(n, s)`. -/
def hittingListWord (n s : ℕ) : List Bool :=
  outputWord n (Parameters.truncation n s) (Parameters.ambientDimension n s)
    (CyclotomicRing.degree (Parameters.exponent n s)) (Parameters.gridSize n s)

private lemma filterMap_map_eq_flatMap_toList {α β γ : Type*} (l : List α)
    (g : α → Option β) (f : β → γ) :
    (l.filterMap g).map f = l.flatMap fun x => ((g x).map f).toList := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases h : g a <;> simp [h, ih]

/-- `gridPointWords` produces the list of encoded tuples of `ExecutableGenerator.output`. -/
theorem gridPointWords_eq (n N e H : ℕ) :
    gridPointWords n N (CyclotomicRing.dimension e) (CyclotomicRing.degree e) H =
      (ExecutableGenerator.output n N e H).tuples.map encodeTuple := by
  rw [ExecutableGenerator.output, filterMap_map_eq_flatMap_toList, Generator.grid,
    gridPointWords, ← List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map, List.flatMap_assoc]
  congr 1; funext t; congr 1; funext p; congr 1; funext r
  exact pointWords_eq n N e (fun i => (![t, p, r] i).val + 1)

/-- `outputWord` agrees with `encodeOutput (ExecutableGenerator.output n N e H)`. -/
theorem outputWord_eq (n N e H : ℕ) :
    outputWord n N (CyclotomicRing.dimension e) (CyclotomicRing.degree e) H =
      encodeOutput (ExecutableGenerator.output n N e H) := by
  simp only [outputWord, gridPointWords_eq, encodeOutput, ExecutableGenerator.output,
    Generator.matrixDimension, List.length_map, List.flatten_eq_flatMap, List.flatMap_map, id_eq]

/-- `hittingListWord n s` agrees with `encodeOutput (hittingList n s)` for all `n, s : ℕ`. -/
theorem hittingListWord_eq (n s : ℕ) :
    hittingListWord n s = encodeOutput (hittingList n s) :=
  outputWord_eq n (Parameters.truncation n s) (Parameters.exponent n s) (Parameters.gridSize n s)

/-! ### Unary input format and standalone generator -/

/-- Unary input word `true ^ n ++ [false] ++ true ^ s` representing the parameter pair `(n, s)`. -/
def inputWord (n s : ℕ) : List Bool :=
  List.replicate n true ++ false :: List.replicate s true

/-- The length of `inputWord n s` is `n + s + 1`. -/
@[simp] theorem length_inputWord (n s : ℕ) : (inputWord n s).length = n + s + 1 := by
  simp only [inputWord, List.length_append, List.length_replicate, List.length_cons]
  omega

/-- The first `false` bit of `inputWord n s` occurs at index `n`. -/
@[simp] theorem idxOf_false_inputWord (n s : ℕ) : (inputWord n s).idxOf false = n :=
  List.idxOf_false_replicate_append n _

/-- Parse a valid unary input word `inputWord n s` with `1 ≤ n` and `1 ≤ s`, returning `none`
on malformed inputs. -/
def parseInput (w : List Bool) : Option (ℕ × ℕ) :=
  let n := w.idxOf false
  let s := w.length - n - 1
  if 1 ≤ n ∧ 1 ≤ s ∧ w = inputWord n s then some (n, s) else none

/-- `parseInput w = some (n, s)` holds if and only if `1 ≤ n`, `1 ≤ s`, and `w = inputWord n s`. -/
theorem parseInput_eq_some_iff (w : List Bool) (n s : ℕ) :
    parseInput w = some (n, s) ↔ 1 ≤ n ∧ 1 ≤ s ∧ w = inputWord n s := by
  unfold parseInput
  dsimp only
  constructor
  · intro h
    split_ifs at h with hcond
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    exact hcond
  · rintro ⟨hn, hs, rfl⟩
    have hs_eq : (inputWord n s).length - n - 1 = s := by
      rw [length_inputWord]
      omega
    rw [idxOf_false_inputWord, hs_eq, ite_eq_left ⟨hn, hs, rfl⟩]

/-- `parseInput` recovers `(n, s)` on `inputWord n s` whenever `1 ≤ n` and `1 ≤ s`. -/
@[simp] theorem parseInput_inputWord {n s : ℕ} (hn : 1 ≤ n) (hs : 1 ≤ s) :
    parseInput (inputWord n s) = some (n, s) :=
  (parseInput_eq_some_iff _ n s).mpr ⟨hn, hs, rfl⟩

/-- `parseInput w = none` holds if and only if `w` is not of the form `inputWord n s` with
`1 ≤ n` and `1 ≤ s`. -/
theorem parseInput_eq_none_iff (w : List Bool) :
    parseInput w = none ↔ ¬ ∃ n s, 1 ≤ n ∧ 1 ≤ s ∧ w = inputWord n s := by
  rw [Option.eq_none_iff_forall_ne_some]
  simp only [Prod.forall, ne_eq, parseInput_eq_some_iff, not_exists]

/-- The standalone rational hitting-list generator on bit words: parses a unary input word
`inputWord n s` with `1 ≤ n` and `1 ≤ s` and emits `encodeOutput (hittingList n s)`, or `[]` on
malformed inputs. -/
def hittingGenerator (w : List Bool) : List Bool :=
  (parseInput w).elim [] fun p => encodeOutput (hittingList p.1 p.2)

/-- On a valid unary input `inputWord n s` with `1 ≤ n` and `1 ≤ s`, `hittingGenerator` emits
`encodeOutput (hittingList n s)`. -/
@[simp] theorem hittingGenerator_inputWord {n s : ℕ} (hn : 1 ≤ n) (hs : 1 ≤ s) :
    hittingGenerator (inputWord n s) = encodeOutput (hittingList n s) := by
  simp [hittingGenerator, parseInput_inputWord hn hs]

/-- On any word where `parseInput w = none`, `hittingGenerator w = []`. -/
theorem hittingGenerator_eq_nil_of_parseInput_eq_none {w : List Bool} (h : parseInput w = none) :
    hittingGenerator w = [] := by
  simp [hittingGenerator, h]

/-- On any malformed input word not of the form `inputWord n s` with `1 ≤ n` and `1 ≤ s`,
`hittingGenerator w = []`. -/
theorem hittingGenerator_eq_nil {w : List Bool}
    (h : ¬ ∃ n s, 1 ≤ n ∧ 1 ≤ s ∧ w = inputWord n s) :
    hittingGenerator w = [] :=
  hittingGenerator_eq_nil_of_parseInput_eq_none ((parseInput_eq_none_iff w).mpr h)

/-! ### Polynomial-time certificates -/

open Turing MultiTapeTM MultiTapeTM.ComputableInPolyTime

variable {α : Type} {encIn : α ↪ List Bool}

@[local fun_prop]
private theorem encodeNat_of_unary {f : α → ℕ}
    (hf : ComputableInPolyTime f encIn encUnary) :
    ComputableInPolyTime (fun x => encodeNat (f x)) encIn encBits :=
  encodeNat_polytime.comp (unary_to_binary.comp hf)

@[local fun_prop]
private theorem bitsReplicate' {n : α → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (bit : Bool) :
    ComputableInPolyTime (fun x => List.replicate (n x) bit) encIn encBits :=
  (bitsReplicate bit).comp hn

@[local fun_prop]
private theorem bitsIdxOfWithInput {w : α → List Bool} {b : α → Bool}
    (hw : ComputableInPolyTime w encIn encBits)
    (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun x => (w x).idxOf (b x)) encIn encUnary :=
  idxOfWithInput (bitsToList.comp hw) hb

@[local fun_prop]
private theorem bits_decide_eq {a b : α → List Bool}
    (ha : ComputableInPolyTime a encIn encBits)
    (hb : ComputableInPolyTime b encIn encBits) :
    ComputableInPolyTime (fun x => decide (a x = b x)) encIn encBool :=
  ha.decide_eq' hb

@[local fun_prop]
private theorem optionSome' {β : Type} {encB : β ↪ List Bool} {f : α → β}
    (hf : ComputableInPolyTime f encIn encB) :
    ComputableInPolyTime (fun x => some (f x)) encIn (encOption encB) :=
  (optionSome encB).comp hf

@[local fun_prop]
private theorem length_list_comp {β : Type} {encB : β ↪ List Bool} {l : α → List β}
    (hl : ComputableInPolyTime l encIn (encList encB)) :
    ComputableInPolyTime (fun x => (l x).length) encIn encUnary :=
  (length_list encB).comp hl

/-- Enumerating the encoded tuples across the `{1, …, H}³` grid is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_gridPointWords {n N M Dg H : α → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hN : ComputableInPolyTime N encIn encUnary)
    (hM : ComputableInPolyTime M encIn encUnary)
    (hDg : ComputableInPolyTime Dg encIn encUnary)
    (hH : ComputableInPolyTime H encIn encUnary) :
    ComputableInPolyTime
      (fun x => gridPointWords (n x) (N x) (M x) (Dg x) (H x))
      encIn (encList encBits) := by
  unfold gridPointWords
  apply flatMapWithInput (range.comp hH)
  apply flatMapWithInput (range.comp (by fun_prop))
  apply flatMapWithInput (range.comp (by fun_prop))
  apply computableInPolyTime_pointWords <;> fun_prop

/-- Computing the complete output encoding `outputWord` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_outputWord {n N M Dg H : α → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hN : ComputableInPolyTime N encIn encUnary)
    (hM : ComputableInPolyTime M encIn encUnary)
    (hDg : ComputableInPolyTime Dg encIn encUnary)
    (hH : ComputableInPolyTime H encIn encUnary) :
    ComputableInPolyTime
      (fun x => outputWord (n x) (N x) (M x) (Dg x) (H x))
      encIn encBits := by
  have hwords := computableInPolyTime_gridPointWords hn hN hM hDg hH
  have hdim := encodeNat_of_unary (unary_mul.comp (hM.prod hDg))
  have hlen := encodeNat_of_unary ((length_list encBits).comp hwords)
  exact (hdim.bitsAppend hlen).bitsAppend (bitsFlatten hwords)

/-- Computing `hittingListWord` from unary `(n, s)` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_hittingListWord {n s : α → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary) :
    ComputableInPolyTime (fun x => hittingListWord (n x) (s x)) encIn encBits :=
  computableInPolyTime_outputWord hn
    (computableInPolyTime_truncation hn hs)
    (computableInPolyTime_ambientDimension hn hs)
    (computableInPolyTime_degree hn hs)
    (computableInPolyTime_gridSize hn hs)

attribute [local irreducible] encodeOutput hittingList hittingListWord

/-- The encoded rational hitting list `(n, s) ↦ encodeOutput (hittingList p.1 p.2)` is computable
in polynomial time from unary `(n, s)`. -/
theorem hittingList_polytime :
    ComputableInPolyTime (fun p : ℕ × ℕ => encodeOutput (hittingList p.1 p.2))
      (encPair encUnary encUnary) encBits := by
  have h : ComputableInPolyTime (fun p : ℕ × ℕ => hittingListWord p.1 p.2)
      (encPair encUnary encUnary) encBits :=
    computableInPolyTime_hittingListWord (fst encUnary encUnary) (snd encUnary encUnary)
  exact h.of_enc_eq fun p => congrArg encBits (hittingListWord_eq p.1 p.2).symm

/-- Compositional polynomial-time certificate for `encodeOutput (hittingList (n x) (s x))`. -/
theorem computableInPolyTime_hittingList {n s : α → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary) :
    ComputableInPolyTime
      (fun x => encodeOutput (hittingList (n x) (s x)))
      encIn encBits :=
  hittingList_polytime.comp (hn.prod hs)

/-- Constructing the unary input word `inputWord` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_inputWord {n s : α → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary) :
    ComputableInPolyTime (fun x => inputWord (n x) (s x)) encIn encBits := by
  unfold inputWord
  fun_prop

/-- Parsing a unary input word with `parseInput` is polynomial-time. -/
@[fun_prop]
theorem parseInput_polytime :
    ComputableInPolyTime parseInput encBits (encOption (encPair encUnary encUnary)) := by
  unfold parseInput inputWord
  fun_prop

/-- Compositional polynomial-time certificate for `parseInput`. -/
@[fun_prop]
theorem computableInPolyTime_parseInput {w : α → List Bool}
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun x => parseInput (w x))
      encIn (encOption (encPair encUnary encUnary)) :=
  parseInput_polytime.comp hw

/-- The standalone rational hitting-list generator `hittingGenerator` is computable in
polynomial time on a multi-tape Turing machine. -/
@[fun_prop]
theorem hittingGenerator_polytime :
    ComputableInPolyTime hittingGenerator encBits encBits :=
  optionElimWithInput parseInput_polytime (const [])
    (hittingList_polytime.comp (snd encBits (encPair encUnary encUnary)))

/-- End-to-end specification of the polynomial-time rational hitting-list generator:
`hittingGenerator` is computable in polynomial time on a multi-tape Turing machine, and on
every unary input `inputWord n s` with `1 ≤ n` and `1 ≤ s` it emits the canonical binary encoding
of `hittingList n s`, which has dimension at most `256 * (n + s + 1) ^ 10`, encoding length at
most `outputConstant * (n + s + 1) ^ 104`, and hits every admissible nonzero formula in `n`
variables with at most `s` nodes. -/
theorem hittingGenerator_spec :
    ComputableInPolyTime hittingGenerator encBits encBits ∧
      ∀ n s : ℕ, 1 ≤ n → 1 ≤ s →
        hittingGenerator (inputWord n s) = encodeOutput (hittingList n s) ∧
          (hittingList n s).dimension ≤ 256 * (n + s + 1) ^ 10 ∧
          (encodeOutput (hittingList n s)).length ≤
            PolynomialBounds.outputConstant * (n + s + 1) ^ 104 ∧
          Hits s (hittingList n s) :=
  ⟨hittingGenerator_polytime, fun n s hn hs =>
    ⟨hittingGenerator_inputWord hn hs, hittingList_dimension_le n s,
      hittingList_encoding_length_le n s, hittingList_hits n s⟩⟩

end Cslib.Circuits.Rational
