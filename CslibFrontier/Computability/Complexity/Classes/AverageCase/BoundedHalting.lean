/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.AverageCase.Collapse
public import CslibFrontier.Computability.Complexity.Classes.AverageCase.Distributional
public import CslibFrontier.Computability.Kolmogorov.TimeBounded
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Tactic.PolyTime

/-!
# The distributional bounded halting problem

The bounded halting problem `BH` of [Bogdanov and Trevisan, §3.2][BogdanovTrevisan2006] asks, on an
instance `(M, x, 1^t)`, whether the nondeterministic machine `M` accepts `x` within `t` steps. Its
"uniform" ensemble `U^BH_N` flips uniform bits until either `N` bits have been flipped or a
prefix-free representation of `(M, x)` has been read, and in the latter case pads it with ones to
length `N`. This module defines both, proves `(BH, U^BH) ∈ DistNP`, and supplies the facts used by
the completeness theorem (`Cslib.Complexity.BoundedHalting.distComplete_problem`).

## Modelling

* **Machines are verifiers.** The library has a universal *deterministic* multi-tape machine,
  `Cslib.Kolmogorov.DescriptionMethod.universalTMRunFor`, so a nondeterministic machine is modelled
  as a deterministic program `c` together with a guessed witness: `c` *accepts* `z` within `t`
  steps (`Cslib.Complexity.BoundedHalting.Accepts`) when, for some witness `v` of length at most
  `t`, the universal machine run for `t` steps on the program `c` and the input `(z, v)` returns
  `[true]`. A nondeterministic machine running for `t` steps makes at most `t` guesses, so this is
  the usual guess-and-verify form of nondeterministic acceptance. The clock counts steps of the
  simulated machine.
* **Headers.** The instance `(c, z, 1^t)` is the word
  `frame c ++ frame (lenWord |z|) ++ z ++ 1^t` (`Cslib.Complexity.BoundedHalting.encode`), with
  `lenWord |z|` the binary representation of `|z|`. Its *header*
  `frame c ++ frame (lenWord |z|) ++ z` has length `2|c| + 2 log |z| + |z| + O(1)`, matching the
  source's `2 log ℓ + 2 log n + ℓ + n + Θ(1)` up to the constant factor on the fixed program length.
  Headers form a prefix code recognized in polynomial time
  (`Cslib.Complexity.BoundedHalting.parser`), so `U^BH` is the collapse of the uniform ensemble at
  that code (`Cslib.Complexity.HeaderParser.ensemble`). Words that are not padded headers are not
  in `BH`, as in the source.

## Main definitions

* `Cslib.Complexity.BoundedHalting.BH`: the bounded halting problem.
* `Cslib.Complexity.BoundedHalting.uniformBH`: the ensemble `U^BH`.
* `Cslib.Complexity.BoundedHalting.problem`: the distributional problem `(BH, U^BH)`.

## Main results

* `Cslib.Complexity.BoundedHalting.uniformBH_dist_encode`: an instance `(c, z, 1^t)` has
  probability `2^{-|header c z|}`.
* `Cslib.Complexity.BoundedHalting.uniformBH_pComp`: `U^BH` is polynomial-time computable.
* `Cslib.Complexity.BoundedHalting.BH_mem_NP`: `BH ∈ NP`.
* `Cslib.Complexity.BoundedHalting.problem_mem_DistNP`: `(BH, U^BH) ∈ DistNP`.

## References

* [A. Bogdanov, L. Trevisan, *Average-Case Complexity*][BogdanovTrevisan2006]
* [L. A. Levin, *Average Case Complete Problems*][Levin1986]
-/

public section

namespace Cslib.Complexity

open scoped ENNReal
open Turing.MultiTapeTM Kolmogorov.DescriptionMethod

namespace BoundedHalting

/-! ### Instances -/

/-- The binary representation of `n`, most significant bit first, without leading zeros. -/
def lenWord (n : ℕ) : List Bool := n.bits.reverse

/-- `lenWord n` represents `n`. -/
@[simp]
theorem binaryValue_lenWord (n : ℕ) : BitString.binaryValue (lenWord n) = n :=
  BitString.binaryValue_reverse_bits n

/-- `lenWord n` has `Nat.size n` bits. -/
@[simp]
theorem length_lenWord (n : ℕ) : (lenWord n).length = n.size := by
  rw [lenWord, List.length_reverse, Nat.size_eq_bits_len]

/-- The header of the instance asking whether program `c` accepts input `z`: the program and the
length of `z` in binary, each framed, followed by `z`. -/
def header (c z : List Bool) : List Bool := frame c ++ frame (lenWord z.length) ++ z

/-- The length of a header. -/
@[simp]
theorem length_header (c z : List Bool) :
    (header c z).length = 2 * c.length + 1 + (2 * z.length.size + 1) + z.length := by
  simp only [header, List.length_append, length_frame, length_lenWord]

/-- The instance `(c, z, 1^t)` of the bounded halting problem: the header of `(c, z)` followed by
`t` ones. -/
def encode (c z : List Bool) (t : ℕ) : List Bool := header c z ++ List.replicate t true

/-- The length of an instance. -/
@[simp]
theorem length_encode (c z : List Bool) (t : ℕ) :
    (encode c z t).length = (header c z).length + t := by
  simp [encode]

/-- Program `c` **accepts** input `z` within `t` steps: on some witness `v` of length at most `t`,
the universal machine run on the program `c` and the input `(z, v)` halts within `t` steps with
output `[true]`. -/
def Accepts (c z : List Bool) (t : ℕ) : Prop :=
  ∃ v : List Bool, v.length ≤ t ∧
    universalTMRunFor (frame c ++ (frame z ++ v)) t = some [true]

/-- Unfolding `Cslib.Complexity.BoundedHalting.Accepts`. -/
theorem accepts_iff {c z : List Bool} {t : ℕ} : Accepts c z t ↔ ∃ v : List Bool, v.length ≤ t ∧
    universalTMRunFor (frame c ++ (frame z ++ v)) t = some [true] := Iff.rfl

/-- The **bounded halting problem** `BH`: the instances `(c, z, 1^t)` such that `c` accepts `z`
within `t` steps. -/
def BH : Set (List Bool) := {y | ∃ c z t, y = encode c z t ∧ Accepts c z t}

/-- Unfolding `Cslib.Complexity.BoundedHalting.BH`. -/
theorem mem_BH_iff {y : List Bool} : y ∈ BH ↔ ∃ c z t, y = encode c z t ∧ Accepts c z t :=
  Iff.rfl

/-! ### Parsing headers -/

/-- The length of the input declared by a word: the framed binary number after the first frame. -/
def declLen (r : List Bool) : ℕ := BitString.binaryValue (unframe (dropFrame r))

/-- What follows the first two frames. -/
def rest (r : List Bool) : List Bool := dropFrame (dropFrame r)

/-- The input of a word: as many bits after the first two frames as declared. -/
def input (r : List Bool) : List Bool :=
  (rest r).take (min (rest r).length (declLen r))

/-- The header parsed from the start of a word. -/
def parseHeader (r : List Bool) : List Bool := header (unframe r) (input r)

/-- A word **begins with a header** if the parsed header is a prefix of it. -/
def valid (r : List Bool) : Bool := decide (r.take (parseHeader r).length = parseHeader r)

/-- The program of a word beginning with a header. -/
theorem unframe_header_append (c z s : List Bool) : unframe (header c z ++ s) = c := by
  rw [header, List.append_assoc, List.append_assoc, unframe_frame_append]

/-- The input of a word beginning with a header. -/
theorem input_header_append (c z s : List Bool) : input (header c z ++ s) = z := by
  have hd : declLen (header c z ++ s) = z.length := by
    rw [declLen, header, List.append_assoc, List.append_assoc, dropFrame_frame_append,
      unframe_frame_append, binaryValue_lenWord]
  have hr : rest (header c z ++ s) = z ++ s := by
    rw [rest, header, List.append_assoc, List.append_assoc, dropFrame_frame_append,
      dropFrame_frame_append]
  rw [input, hd, hr, List.length_append, Nat.min_eq_right (Nat.le_add_right _ _),
    List.take_left' rfl]

/-- A header is parsed from every word extending it. -/
theorem parseHeader_header_append (c z s : List Bool) :
    parseHeader (header c z ++ s) = header c z := by
  rw [parseHeader, unframe_header_append, input_header_append]

/-- A word is valid exactly when its parsed header is a prefix of it. -/
theorem valid_iff (r : List Bool) : valid r = true ↔ parseHeader r <+: r := by
  rw [valid, decide_eq_true_eq, List.prefix_iff_eq_take, eq_comm]

/-- Every word extending a header is valid. -/
theorem valid_header_append (c z s : List Bool) : valid (header c z ++ s) = true := by
  rw [valid_iff, parseHeader_header_append]
  exact List.prefix_append _ _

/-- The prefix code of headers. -/
@[expose] def parser : HeaderParser where
  valid := valid
  header := parseHeader
  header_isPrefix r hr := (valid_iff r).mp hr
  valid_of_isPrefix r r' hr hp := by
    obtain ⟨s, rfl⟩ := hp
    have h := parseHeader_header_append (unframe r) (input r) s
    exact ⟨valid_header_append _ _ _, h⟩

/-- The validity test of `Cslib.Complexity.BoundedHalting.parser`. -/
theorem parser_valid : parser.valid = valid := rfl

/-- The header map of `Cslib.Complexity.BoundedHalting.parser`. -/
theorem parser_header : parser.header = parseHeader := rfl

/-- The program of an instance. -/
theorem unframe_encode (c z : List Bool) (t : ℕ) : unframe (encode c z t) = c :=
  unframe_header_append c z _

/-- The input of an instance. -/
theorem input_encode (c z : List Bool) (t : ℕ) : input (encode c z t) = z :=
  input_header_append c z _

/-- The header of an instance. -/
theorem parseHeader_encode (c z : List Bool) (t : ℕ) : parseHeader (encode c z t) = header c z :=
  parseHeader_header_append c z _

/-- Instances are fixed by collapsing. -/
theorem collapse_encode (c z : List Bool) (t : ℕ) :
    parser.collapse (encode c z t) = encode c z t := by
  rw [HeaderParser.collapse_of_valid _ (valid_header_append c z _), parser_header, encode,
    parseHeader_header_append, List.length_append, List.length_replicate, Nat.add_sub_cancel_left]

/-! ### The uniform ensemble and the distributional problem -/

/-- The ensemble `U^BH` of [Bogdanov and Trevisan, §3.2][BogdanovTrevisan2006]: flip uniform bits
until a header has been read, then pad it with ones. -/
noncomputable def uniformBH : Ensemble := parser.ensemble

/-- The **distributional bounded halting problem** `(BH, U^BH)`. -/
@[expose] noncomputable def problem : DistProblem := ⟨BH, uniformBH⟩

/-- The language of `(BH, U^BH)`. -/
theorem problem_lang : problem.lang = BH := rfl

/-- The ensemble of `(BH, U^BH)`. -/
theorem problem_ens : problem.ens = uniformBH := rfl

/-- An instance `(c, z, 1^t)` has probability `2^{-|header c z|}` under `U^BH`. -/
theorem uniformBH_dist_encode (c z : List Bool) (t : ℕ) :
    uniformBH.dist (encode c z t).length (encode c z t) = (2 ^ (header c z).length : ℝ≥0∞)⁻¹ := by
  have h := parser.ensemble_dist_collapse (valid_header_append c z (List.replicate t true))
  rw [← encode, collapse_encode, parser_header, encode, parseHeader_header_append] at h
  exact h

/-- Instances determine their program, input and clock. -/
theorem encode_injective {c z c' z' : List Bool} {t t' : ℕ}
    (h : encode c z t = encode c' z' t') : c = c' ∧ z = z' ∧ t = t' := by
  have hc := congrArg unframe h
  have hz := congrArg input h
  rw [encode, encode, unframe_header_append, unframe_header_append] at hc
  rw [encode, encode, input_header_append, input_header_append] at hz
  subst hc hz
  refine ⟨rfl, rfl, ?_⟩
  simpa using congrArg List.length h

/-- An instance is in `BH` exactly when its program accepts its input within its clock. -/
theorem encode_mem_BH_iff {c z : List Bool} {t : ℕ} : encode c z t ∈ BH ↔ Accepts c z t := by
  constructor
  · rintro ⟨c', z', t', h, hacc⟩
    obtain ⟨rfl, rfl, rfl⟩ := encode_injective h
    exact hacc
  · exact fun h => ⟨c, z, t, rfl, h⟩

/-! ### Polynomial-time parsing -/

/-- `lenWord` is computable in polynomial time from a unary argument. -/
theorem lenWord_polyTime : ComputableInPolyTime lenWord encUnary encBits := by
  have hbits : ComputableInPolyTime Nat.bits encNat encBits :=
    ComputableInPolyTime.of_eq fun _ => rfl
  unfold lenWord
  exact ComputableInPolyTime.bitsReverse.comp (hbits.comp ComputableInPolyTime.unary_to_binary)

/-- Parsing the input is computable in polynomial time. -/
theorem input_polyTime : ComputableInPolyTime input encBits encBits := by
  have hd : ComputableInPolyTime declLen encBits encNat := by
    unfold declLen
    exact ComputableInPolyTime.bitsBinaryValue.comp
      (ComputableInPolyTime.unframe.comp ComputableInPolyTime.dropFrame)
  have hr : ComputableInPolyTime rest encBits encBits := by
    unfold rest
    exact ComputableInPolyTime.dropFrame.comp ComputableInPolyTime.dropFrame
  unfold input
  exact ComputableInPolyTime.bitsTakeWithInput hr
    (ComputableInPolyTime.binary_min_unary' (ComputableInPolyTime.length_bits.comp hr) hd)

/-- Forming headers is computable in polynomial time. -/
theorem header_polyTime : ComputableInPolyTime (fun p : List Bool × List Bool => header p.1 p.2)
    (encPair encBits encBits) encBits := by
  have hl := lenWord_polyTime.comp
    (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.snd encBits encBits))
  unfold header
  polytime

/-- Instances `(c, z, 1^t)` with polynomial-time computable components are computable in polynomial
time. -/
theorem encode_polyTime {α : Type} {enc : α ↪ List Bool} {c z : α → List Bool} {t : α → ℕ}
    (hc : ComputableInPolyTime c enc encBits) (hz : ComputableInPolyTime z enc encBits)
    (ht : ComputableInPolyTime t enc encUnary) :
    ComputableInPolyTime (fun a => encode (c a) (z a) (t a)) enc encBits :=
  ComputableInPolyTime.bitsAppend (header_polyTime.comp (hc.prod hz))
    ((ComputableInPolyTime.bitsReplicate true).comp ht)

/-- Parsing headers is computable in polynomial time. -/
theorem parseHeader_polyTime : ComputableInPolyTime parseHeader encBits encBits := by
  exact header_polyTime.comp (ComputableInPolyTime.unframe.prod input_polyTime)

/-- Recognizing words that begin with a header is computable in polynomial time. -/
theorem valid_polyTime : ComputableInPolyTime valid encBits encBool := by
  have hp := parseHeader_polyTime
  unfold valid
  polytime

/-- **`U^BH` is polynomial-time computable.** -/
theorem uniformBH_pComp : uniformBH.PComp :=
  parser.pComp_ensemble valid_polyTime parseHeader_polyTime

/-! ### Membership in `NP` -/

/-- The number of ones after the header of a word. -/
def steps (y : List Bool) : ℕ := y.length - (parseHeader y).length

/-- The verifier for `BH`: the instance is a header padded with `t` ones and the framed certificate
is a witness of length at most `t` on which the universal machine accepts within `t` steps. -/
def verifier (yw : List Bool × List Bool) : Bool :=
  decide (yw.1 = parseHeader yw.1 ++ List.replicate (steps yw.1) true) &&
    decide ((unframe yw.2).length ≤ steps yw.1) &&
    decide (universalTMRunFor (frame (unframe yw.1) ++ (frame (input yw.1) ++ unframe yw.2))
      (steps yw.1) = some [true])

/-- The verifier for `BH` is computable in polynomial time. -/
theorem verifier_polyTime : ComputableInPolyTime verifier (encPair encBits encBits) encBool := by
  have hp := parseHeader_polyTime
  have hi := input_polyTime
  have hs : ComputableInPolyTime steps encBits encUnary := by
    unfold steps
    polytime
  have hu := computableInPolyTime_universalTMRunFor
  unfold verifier
  polytime

/-- The clock of an instance. -/
theorem steps_encode (c z : List Bool) (t : ℕ) : steps (encode c z t) = t := by
  rw [steps, encode, parseHeader_header_append, List.length_append, List.length_replicate,
    Nat.add_sub_cancel_left]

/-- **`BH ∈ NP`**, with certificates of length `2|y| + 1` (framed witnesses). -/
theorem BH_mem_NP : BH ∈ NP encBits := by
  refine ⟨2 * Polynomial.X + 1, verifier, verifier_polyTime, IsVerifier.of_padding ?_ ?_⟩
  · intro y w _ hV
    simp only [verifier, Bool.and_eq_true, decide_eq_true_eq] at hV
    obtain ⟨⟨hy, hlen⟩, hrun⟩ := hV
    refine ⟨unframe y, input y, steps y, ?_, unframe w, hlen, hrun⟩
    rw [encode, header]
    exact hy
  · rintro y ⟨c, z, t, rfl, v, hv, hrun⟩
    refine ⟨frame v, ?_, fun k => ?_⟩
    · simp only [length_frame, encBits, Function.Embedding.coe_refl, id_eq, length_encode,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
        Polynomial.eval_one]
      omega
    · simp only [verifier, Bool.and_eq_true, decide_eq_true_eq, steps_encode,
        unframe_frame_append, unframe_encode, input_encode, parseHeader_encode]
      exact ⟨⟨rfl, hv⟩, hrun⟩

/-- **`(BH, U^BH) ∈ DistNP`.** -/
theorem problem_mem_DistNP : problem ∈ DistNP :=
  mem_DistNP.mpr ⟨BH_mem_NP, uniformBH_pComp⟩

end BoundedHalting

end Cslib.Complexity
