/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Classes.Sparse.Turing
public import Complexity.Computability.Complexity.Classes.Tally
public import Complexity.Computability.Complexity.Reduction.Turing
import Complexity.Computability.Circuit.Boolean.Advice
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Pair

/-!
# `P/poly = P^SPARSE = P^TALLY`

A problem has circuits of polynomial size exactly when it is decided in polynomial time relative to
some sparse oracle language, and then a tally oracle language suffices
(`Cslib.Complexity.PPolyOn_eq_iUnion_PWithOracle_SPARSE`,
`Cslib.Complexity.PPolyOn_eq_iUnion_PWithOracle_TALLY`).
[Hemaspaandra and Ogihara, p. 22][HemaspaandraOgihara2002] cite `P/poly = P^SPARSE` as well known,
and their bibliographic notes (p. 27) attribute it, through
[Berman and Hartmanis][BermanHartmanis1977], to Meyer.

The inclusion `P^S ⊆ P/poly` for sparse `S` is `Cslib.Complexity.PWithOracle_subset_PPolyOn`
(`Complexity/Computability/Complexity/Classes/Sparse/Turing.lean`). This module proves the
converse. A problem in `P/poly` is decided in polynomial time from advice strings `α n` of
polynomial length that list its circuits (`Cslib.Circuits.Boolean.PPoly.exists_evalAdvice`). The
tally language `adviceTally α` holds the unary word of `Nat.pair n i` exactly when bit `i` of
`α n` is `true` (`Cslib.Complexity.encUnary_pair_mem_adviceTally`). On an input of length `n` the
reduction asks the `|α n|` words for `(n, i)`, `i < |α n|`, reads `α n` off the answers, and
evaluates the circuits it lists. The requests are computed without the answers, so this is a
polynomial-time truth-table reduction to a tally language
(`Cslib.Complexity.exists_polyTimeTruthTableReducible_adviceTally`), and truth-table reductions are
Turing reductions (`Cslib.Complexity.PolyTimeTruthTableReducible.polyTimeTuringReducible`). Hence
`P/poly` is also the class of problems with polynomial-time truth-table reductions to tally
languages (`Cslib.Complexity.mem_PPolyOn_iff_exists_mem_TALLY_polyTimeTruthTableReducible`).

## Main definitions

* `Cslib.Complexity.adviceTally`: the tally language encoding the bits of an advice function.

## Main results

* `Cslib.Complexity.encUnary_pair_mem_adviceTally`, `Cslib.Complexity.adviceTally_mem_TALLY`:
  membership in `adviceTally α` reads the bits of `α`, and `adviceTally α` is tally.
* `Cslib.Complexity.exists_polyTimeTruthTableReducible_adviceTally`: a problem in `P/poly` has a
  polynomial-time truth-table reduction to `adviceTally α` for advice `α` of polynomial length.
* `Cslib.Complexity.mem_PPolyOn_iff_exists_mem_TALLY_polyTimeTruthTableReducible`: `P/poly` is the
  class of problems truth-table reducible in polynomial time to tally languages.
* `Cslib.Complexity.exists_mem_TALLY_mem_PWithOracle_of_mem_PPolyOn`: `P/poly ⊆ P^TALLY`.
* `Cslib.Complexity.mem_PPolyOn_iff_exists_mem_SPARSE_mem_PWithOracle`,
  `Cslib.Complexity.mem_PPolyOn_iff_exists_mem_TALLY_mem_PWithOracle`: membership in `P/poly` is
  membership in `P^S` for a sparse, or tally, `S`.
* `Cslib.Complexity.PPolyOn_eq_iUnion_PWithOracle_SPARSE`,
  `Cslib.Complexity.PPolyOn_eq_iUnion_PWithOracle_TALLY`: `P/poly = P^SPARSE = P^TALLY`.

## References

* [L. A. Hemaspaandra, M. Ogihara, *The Complexity Theory Companion*][HemaspaandraOgihara2002]
* [L. Berman, J. Hartmanis, *On isomorphisms and density of NP and other complete
  sets*][BermanHartmanis1977]
-/

public section

namespace Cslib.Complexity

open Circuits Circuits.Boolean Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- The tally language encoding the bits of the advice function `adv`: the unary word of
`Nat.pair n i` is a member exactly when bit `i` of `adv n` is `true`. Bits past the end of
`adv n` count as `false`. -/
def adviceTally (adv : ℕ → List Bool) : Set (List Bool) :=
  encUnary '' {k | (adv k.unpair.1).getD k.unpair.2 false = true}

/-- The unary word of `Nat.pair n i` lies in `adviceTally adv` exactly when bit `i` of `adv n` is
`true`. -/
theorem encUnary_pair_mem_adviceTally {adv : ℕ → List Bool} {n i : ℕ} :
    encUnary (Nat.pair n i) ∈ adviceTally adv ↔ (adv n).getD i false = true := by
  rw [adviceTally, encUnary.injective.mem_set_image, Set.mem_ofPred_eq, Nat.unpair_pair]

/-- `adviceTally adv` is a tally language. -/
theorem adviceTally_mem_TALLY (adv : ℕ → List Bool) : adviceTally adv ∈ TALLY :=
  image_encUnary_mem_TALLY _

/-- **Advice as a tally oracle.** A problem in `P/poly` has a polynomial-time truth-table
reduction to the tally language `adviceTally adv`, for some advice `adv` of polynomial length. On
an instance `a` with `n = |enc a|` the reduction asks the unary words of `Nat.pair n i` for
`i < |adv n|`, whose answers are the bits of `adv n`, and evaluates the circuits that `adv n`
lists on `enc a`. -/
theorem exists_polyTimeTruthTableReducible_adviceTally (hA : A ∈ PPolyOn enc) :
    ∃ adv : ℕ → List Bool, PolynomiallyBounded (fun n => (adv n).length) ∧
      PolyTimeTruthTableReducible enc encBits A (adviceTally adv) := by
  obtain ⟨L, hL, hAL⟩ := hA
  obtain ⟨S, W, P, adv, hlen, hadv, heval⟩ := PPoly.exists_evalAdvice hL Polynomial.X
  have hn : ComputableInPolyTime (fun p : α × List Bool => (enc p.1).length)
      (encPair enc encBits) encUnary := (encoding_length enc).comp (fst _ _)
  refine ⟨adv, hadv, fun a => P.eval (enc a).length,
    fun p => encUnary (Nat.pair (enc p.1).length p.2),
    fun p => evalAdvice (S.eval (enc p.1).length) (W.eval (enc p.1).length) p.2 (enc p.1),
    (unary_eval P).comp (encoding_length enc),
    encoding_comp (unary_pair.comp (((encoding_length enc).comp (fst _ _)).prod (snd _ _))),
    computableInPolyTime_evalAdvice_eval S W hn (snd _ _)
      ((of_eq (encIn := enc) (encOut := encBits) fun _ => rfl).comp (fst _ _)), fun a => ?_⟩
  have hans : truthTableAnswers
      ((fun p : α × ℕ => encUnary (Nat.pair (enc p.1).length p.2)) ⁻¹' adviceTally adv)
      (fun a => P.eval (enc a).length) a = adv (enc a).length := by
    refine List.ext_getElem (by rw [length_truthTableAnswers, hlen]) fun i _ hi => ?_
    simp only [truthTableAnswers, List.getElem_ofFn, Set.mem_preimage,
      encUnary_pair_mem_adviceTally, List.getD_eq_getElem _ _ hi, Bool.decide_eq_true]
  rw [hans, heval _ _ (by simp), hAL a]

/-- **`P/poly ⊆ R_tt(TALLY)`**: a problem in `P/poly` has a polynomial-time truth-table reduction
to a tally language. -/
theorem exists_mem_TALLY_polyTimeTruthTableReducible_of_mem_PPolyOn (hA : A ∈ PPolyOn enc) :
    ∃ T ∈ TALLY, PolyTimeTruthTableReducible enc encBits A T := by
  obtain ⟨adv, -, h⟩ := exists_polyTimeTruthTableReducible_adviceTally hA
  exact ⟨adviceTally adv, adviceTally_mem_TALLY adv, h⟩

/-- **`P/poly ⊆ P^TALLY`** (Meyer): a problem in `P/poly` is decided in polynomial time relative
to some tally oracle language [Hemaspaandra and Ogihara, p. 22][HemaspaandraOgihara2002]. -/
theorem exists_mem_TALLY_mem_PWithOracle_of_mem_PPolyOn (hA : A ∈ PPolyOn enc) :
    ∃ T ∈ TALLY, A ∈ PWithOracle T enc := by
  obtain ⟨T, hT, h⟩ := exists_mem_TALLY_polyTimeTruthTableReducible_of_mem_PPolyOn hA
  exact ⟨T, hT, polyTimeTuringReducible_bits_iff_mem_PWithOracle.mp h.polyTimeTuringReducible⟩

/-- **`P/poly = R_tt(TALLY)`**: a problem is in `P/poly` exactly when it has a polynomial-time
truth-table reduction to a tally language. -/
theorem mem_PPolyOn_iff_exists_mem_TALLY_polyTimeTruthTableReducible :
    A ∈ PPolyOn enc ↔ ∃ T ∈ TALLY, PolyTimeTruthTableReducible enc encBits A T :=
  ⟨exists_mem_TALLY_polyTimeTruthTableReducible_of_mem_PPolyOn, fun ⟨_, hT, h⟩ =>
    PWithOracle_subset_PPolyOn (TALLY_subset_SPARSE hT) enc
      (polyTimeTuringReducible_bits_iff_mem_PWithOracle.mp h.polyTimeTuringReducible)⟩

/-- **Meyer's theorem, with tally oracles**: a problem is in `P/poly` exactly when it is decided
in polynomial time relative to some tally oracle language. -/
theorem mem_PPolyOn_iff_exists_mem_TALLY_mem_PWithOracle :
    A ∈ PPolyOn enc ↔ ∃ T ∈ TALLY, A ∈ PWithOracle T enc :=
  ⟨exists_mem_TALLY_mem_PWithOracle_of_mem_PPolyOn, fun ⟨_, hT, h⟩ =>
    PWithOracle_subset_PPolyOn (TALLY_subset_SPARSE hT) enc h⟩

/-- **Meyer's theorem**: a problem is in `P/poly` exactly when it is decided in polynomial time
relative to some sparse oracle language [Hemaspaandra and Ogihara, p. 22][HemaspaandraOgihara2002].
-/
theorem mem_PPolyOn_iff_exists_mem_SPARSE_mem_PWithOracle :
    A ∈ PPolyOn enc ↔ ∃ S ∈ SPARSE encBits, A ∈ PWithOracle S enc :=
  ⟨fun hA => (exists_mem_TALLY_mem_PWithOracle_of_mem_PPolyOn hA).imp fun _ ⟨hT, h⟩ =>
    ⟨TALLY_subset_SPARSE hT, h⟩, fun ⟨_, hS, h⟩ => PWithOracle_subset_PPolyOn hS enc h⟩

/-- **`P/poly = P^SPARSE`** (Meyer) [Hemaspaandra and Ogihara, p. 22][HemaspaandraOgihara2002]:
the problems with circuits of polynomial size are those decided in polynomial time relative to a
sparse oracle language. -/
theorem PPolyOn_eq_iUnion_PWithOracle_SPARSE (enc : α ↪ List Bool) :
    PPolyOn enc = ⋃ S ∈ SPARSE encBits, PWithOracle S enc := by
  ext A
  rw [Set.mem_iUnion₂, mem_PPolyOn_iff_exists_mem_SPARSE_mem_PWithOracle]
  exact exists_congr fun _ => exists_prop.symm

/-- **`P/poly = P^TALLY`**: the problems with circuits of polynomial size are those decided in
polynomial time relative to a tally oracle language. -/
theorem PPolyOn_eq_iUnion_PWithOracle_TALLY (enc : α ↪ List Bool) :
    PPolyOn enc = ⋃ T ∈ TALLY, PWithOracle T enc := by
  ext A
  rw [Set.mem_iUnion₂, mem_PPolyOn_iff_exists_mem_TALLY_mem_PWithOracle]
  exact exists_congr fun _ => exists_prop.symm

end Cslib.Complexity
