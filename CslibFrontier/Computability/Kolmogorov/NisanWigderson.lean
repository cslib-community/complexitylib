/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.Basic
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Reconstruction

/-!
# Short descriptions from distinguishers of the Nisan–Wigderson generator

Let `C` be a list code whose codewords are Boolean functions on `n` bits, and let a deterministic
test distinguish the Nisan–Wigderson generator built from a design `D` and the codeword
`C.encode x` of a message `x`. The reconstruction turns the test into a predictor of the codeword
with advantage `ε / m` (`Cslib.Crypto.PRG.NisanWigderson.exists_half_add_div_le_trialAgreement`),
determined by a reconstruction of at most `m 2 ^ a` bits
(`Cslib.Crypto.PRG.NisanWigderson.Reconstruction`,
`Cslib.Crypto.PRG.NisanWigderson.reconstructionBits_le`), and list decoding the predictor lists
`x` among `L` candidates. So `x` is determined by the reconstruction and an index of `⌈log₂ L⌉`
bits, given `D`, `C` and the test. This is the step from distinguishers to short time-bounded
descriptions in Hirahara's analysis of the time-bounded Kolmogorov complexity problem
[Hirahara2018].

To turn this into a bound on the time-bounded complexity `C_M^t(x)` of a description method `M`,
`M` must be able to run the decoder: from a description of the reconstruction and the index,
output the candidate within `t` steps. No machine for the decoder is constructed in this library
yet, so this is a hypothesis, `Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder`, in the
style of `Cslib.Kolmogorov.DescriptionMethod.Simulation`: a compiler from reconstructions and
indices to `M`-programs, with an explicit program overhead `c` over the length of a direct binary
description and an explicit time bound `t`. Under it, `C_M^t(x) ≤ m 2 ^ a + ⌈log₂ m⌉ + ⌈log₂ L⌉ + c`
(`Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder.etimeBoundedComplexity_le`). A test that
accepts a `δ` fraction of all strings and no output of the generator has advantage `δ`, which gives
the same bound for strings with a dense distinguisher
(`Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder.etimeBoundedComplexity_le_of_dens`), in
particular for a dense test that accepts only strings of high time-bounded complexity when all
outputs of the generator have low time-bounded complexity
(`Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder.etimeBoundedComplexity_le_of_random`).

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder`: a description method that runs the
  decoder of the reconstruction, with explicit program and time overheads.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder.etimeBoundedComplexity_le`: a
  distinguisher of the generator built from the codeword of `x` gives a short time-bounded
  description of `x`.
* `Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder.etimeBoundedComplexity_le_of_dens`,
  `Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder.etimeBoundedComplexity_le_of_random`:
  the same from a dense test that avoids the outputs of the generator.

## References

* [S. Hirahara, *Non-black-box worst-case to average-case reductions within NP*][Hirahara2018]
* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
-/

@[expose] public section

namespace Cslib.Kolmogorov.DescriptionMethod

open Cslib.Crypto.PRG Cslib.Crypto.PRG.NisanWigderson Finset

variable {α : Type*} {ℓ n a m L : ℕ}

/-- A *reconstruction decoder* in the description method `M`, for the design `D`, the list code
`C` and the deterministic test `test`, with program overhead `c` and time bound `t`: every
reconstruction `R` for `D` and every index `k` of the list decoder are compiled into an
`M`-program that outputs, within `t` steps, the `k`-th candidate that `C` decodes from the guess
of `R`, and whose length exceeds by at most `c` the
`⌈log₂ m⌉ + reconstructionBits D R.pos + ⌈log₂ L⌉` bits of a direct binary description of `R`
and `k`: the position in `⌈log₂ m⌉` bits, then the table entries, the padding and candidate bits,
whose number `reconstructionBits D R.pos` is fixed by `D` and the position, and finally the index
in `⌈log₂ L⌉` bits. Such descriptions are uniquely decodable once `D` and `L` are known.

This is all that is assumed of `M` to bound time-bounded complexities through the reconstruction:
that it runs the decoder, with `D`, `C` and `test` built in, on direct descriptions of the
decoder's input. The overhead `c` and the time bound `t` may depend on `D`, `C` and `test`, so the
resulting bounds are relative to them; nothing is assumed about how the decoder evaluates the test
or the list decoder, whose cost is part of `t`. -/
structure ReconstructionDecoder (M : DescriptionMethod α) (D : Design ℓ n a m)
    (C : ListCode α (Fin n → Bool) Bool L) (test : (Fin m → Bool) → Bool) (c t : ℕ) where
  /-- The program describing the `k`-th candidate decoded from the reconstruction `R`. -/
  program : Reconstruction D → Fin L → List Bool
  /-- A program exceeds a direct description of its reconstruction and index by at most `c`
  bits. -/
  length_program_le (R : Reconstruction D) (k : Fin L) :
    (program R k).length ≤ Nat.clog 2 m + reconstructionBits D R.pos + Nat.clog 2 L + c
  /-- A program outputs its candidate within `t` steps. -/
  mem_runFor_program (R : Reconstruction D) (k : Fin L) :
    C.decode (R.guess test) k ∈ (M.run (program R k)).runFor t

namespace ReconstructionDecoder

variable {M : DescriptionMethod α} {D : Design ℓ n a m} {C : ListCode α (Fin n → Bool) Bool L}
  {test : (Fin m → Bool) → Bool} {c t : ℕ}

/-- **Short descriptions from distinguishers** [Hirahara2018]. Let `0 < m`, let the list code `C`
list decode up to radius `1 / 2 - ε / m`, and let `M` run the decoder of the reconstruction for
the deterministic test `test` with program overhead `c` within `t` steps. If `test` accepts the
outputs of the Nisan–Wigderson generator built from the codeword of `x` with probability at least
`ε` more than uniform strings, then `C_M^t(x) ≤ m 2 ^ a + ⌈log₂ m⌉ + ⌈log₂ L⌉ + c`. -/
theorem etimeBoundedComplexity_le (I : ReconstructionDecoder M D C test c t) (hm : 0 < m)
    {ε : ℝ} (hC : C.ListDecodes (1 / 2 - ε / m)) {x : α}
    (hε : ε ≤ ((generator D (C.encode x)).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal) :
    M.etimeBoundedComplexity t x ≤ (m * 2 ^ a + Nat.clog 2 m + Nat.clog 2 L + c : ℕ) := by
  obtain ⟨tr, htr⟩ := exists_half_add_div_le_trialAgreement D (C.encode x) test hm hε
  obtain ⟨k, hk⟩ : ∃ k, C.decode ((Reconstruction.ofTrial D (C.encode x) tr).guess test) k = x := by
    refine hC.exists_decode_eq_of_half_add_le ?_
    rw [Reconstruction.guess_ofTrial]
    simpa only [trialAgreement, eq_comm] using htr
  refine etimeBoundedComplexity_le_natCast_iff.mpr
    ⟨I.program _ k, ?_, hk ▸ I.mem_runFor_program _ k⟩
  have hlen := I.length_program_le (Reconstruction.ofTrial D (C.encode x) tr) k
  change _ ≤ Nat.clog 2 m + reconstructionBits D tr.pos + Nat.clog 2 L + c at hlen
  have := reconstructionBits_le D tr.pos
  omega

/-- **Short descriptions from dense distinguishers** [Hirahara2018]. Let `0 < m`, let the list code
`C` list decode up to radius `1 / 2 - δ / m`, and let `M` run the decoder of the reconstruction for
the negation of the deterministic test `test` with program overhead `c` within `t` steps. If `test`
accepts at least a `δ` fraction of all strings but no output of the Nisan–Wigderson generator built
from the codeword of `x`, then `C_M^t(x) ≤ m 2 ^ a + ⌈log₂ m⌉ + ⌈log₂ L⌉ + c`. -/
theorem etimeBoundedComplexity_le_of_dens (I : ReconstructionDecoder M D C (fun y => !test y) c t)
    (hm : 0 < m) {δ : ℝ} (hC : C.ListDecodes (1 / 2 - δ / m)) {x : α}
    (hδ : δ ≤ dens {y | test y = true})
    (havoid : ∀ z, test (generator D (C.encode x) z) = false) :
    M.etimeBoundedComplexity t x ≤ (m * 2 ^ a + Nat.clog 2 m + Nat.clog 2 L + c : ℕ) :=
  I.etimeBoundedComplexity_le hm hC <| hδ.trans_eq
    (Generator.toReal_realExperiment_sub_toReal_idealExperiment_not _ havoid).symm

/-- **Short descriptions from tests for random strings** [Hirahara2018]. Let `N` be a description
method for `m`-bit strings, and let the deterministic test `test` accept at least a `δ` fraction
of all strings, all of them of complexity `C_N^{t'} ≥ s`. Let `0 < m`, let the list code `C` list
decode up to radius `1 / 2 - δ / m`, and let `M` run the decoder of the reconstruction for the
negation of `test` with program overhead `c` within `t` steps. If every output of the
Nisan–Wigderson generator built from the codeword of `x` has complexity `C_N^{t'} < s`, then
`C_M^t(x) ≤ m 2 ^ a + ⌈log₂ m⌉ + ⌈log₂ L⌉ + c`. -/
theorem etimeBoundedComplexity_le_of_random (I : ReconstructionDecoder M D C (fun y => !test y) c t)
    (hm : 0 < m) {δ : ℝ} (hC : C.ListDecodes (1 / 2 - δ / m)) {N : DescriptionMethod (Fin m → Bool)}
    {t' s : ℕ} (hδ : δ ≤ dens {y | test y = true})
    (hrandom : ∀ y, test y = true → s ≤ N.etimeBoundedComplexity t' y) {x : α}
    (hlow : ∀ z, N.etimeBoundedComplexity t' (generator D (C.encode x) z) < s) :
    M.etimeBoundedComplexity t x ≤ (m * 2 ^ a + Nat.clog 2 m + Nat.clog 2 L + c : ℕ) :=
  I.etimeBoundedComplexity_le_of_dens hm hC hδ fun z =>
    Bool.eq_false_iff.mpr fun h => (hlow z).not_ge (hrandom _ h)

end ReconstructionDecoder

end Cslib.Kolmogorov.DescriptionMethod
