/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Sampling
public import CslibFrontier.Foundations.Data.Code.ListDecoding
import CslibFrontier.Foundations.Data.Finset.Sampling

/-!
# Reconstructions of the Nisan–Wigderson generator and list decoding

With its random choices fixed, the predictor that the Nisan–Wigderson reconstruction builds from a
deterministic test needs the hard function `f` only through the earlier output bits, and by
`Cslib.Crypto.PRG.NisanWigderson.dependsOn_generator_extend` each of them is a function of the
at most `a` input bits that its block shares with the block of the predicted bit. A
*reconstruction* stores these functions as tables, together with the position of the predicted
bit, the candidate bit and the padding bits after that position; its guess is computed from this
data and the test alone (`Cslib.Crypto.PRG.NisanWigderson.Reconstruction.guess`). Every trial
gives a reconstruction with the same guess
(`Cslib.Crypto.PRG.NisanWigderson.Reconstruction.guess_ofTrial`), and a reconstruction at
position `i` consists of `reconstructionBits D i ≤ m 2 ^ a` bits
(`Cslib.Crypto.PRG.NisanWigderson.reconstructionBits_le`).

If `f` is the codeword `C.encode x` of a message `x` in a list code `C`, a guess that agrees with
`f` on a `1 / 2 + δ` fraction of the inputs lists `x` among its candidates when `C` list decodes
up to radius `1 / 2 - δ`. With the sampling layer
(`Cslib.Crypto.PRG.NisanWigderson.div_two_mul_le_dens_goodTrials`), a uniformly random trial lists
`x` with probability at least `ε / (2 m)`
(`Cslib.Crypto.PRG.NisanWigderson.div_two_mul_le_dens_mem_candidates`), and `k` independent
trials give at most `k L` candidates (`Cslib.Crypto.PRG.NisanWigderson.card_trialCandidates_le`)
that include `x` with probability at least `1 - (1 - ε / (2 m)) ^ k`
(`Cslib.Crypto.PRG.NisanWigderson.one_sub_pow_le_dens_mem_trialCandidates`): this is the
randomized list-decoding reconstruction of [Hirahara2018].

## Main definitions

* `Cslib.Crypto.PRG.NisanWigderson.Reconstruction`: the data of a predictor, with the earlier
  output bits stored as tables.
* `Cslib.Crypto.PRG.NisanWigderson.Reconstruction.guess`: its guess.
* `Cslib.Crypto.PRG.NisanWigderson.Reconstruction.ofTrial`: the reconstruction of a trial.
* `Cslib.Crypto.PRG.NisanWigderson.reconstructionBits`: the number of bits of a reconstruction.
* `Cslib.Crypto.PRG.NisanWigderson.trialCandidates`: the candidates listed by several trials.

## Main results

* `Cslib.Crypto.PRG.NisanWigderson.Reconstruction.guess_ofTrial`: a reconstruction guesses as its
  trial does.
* `Cslib.Crypto.PRG.NisanWigderson.reconstructionBits_le`: a reconstruction has at most `m 2 ^ a`
  bits.
* `Cslib.Crypto.PRG.NisanWigderson.div_two_mul_le_dens_mem_candidates`,
  `Cslib.Crypto.PRG.NisanWigderson.one_sub_pow_le_dens_mem_trialCandidates`: randomized list
  decoding.

## References

* [S. Hirahara, *Non-black-box worst-case to average-case reductions within NP*][Hirahara2018]
* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapters 19
  and 20
-/

@[expose] public section

namespace Cslib.Crypto.PRG.NisanWigderson

open Finset

variable {ℓ n a m : ℕ}

/-- A *reconstruction* for the design `D`: the data of the predictor that the reconstruction
builds from a deterministic test, with its random choices fixed and the earlier output bits stored
as tables. -/
structure Reconstruction (D : Design ℓ n a m) where
  /-- The position of the predicted bit. -/
  pos : Fin m
  /-- For each earlier position `j`, output bit `j` as a function of the input bits in
  `D.overlap pos j`. -/
  table : (j : Fin pos) → (D.overlap pos (Fin.castLE pos.isLt.le j) → Bool) → Bool
  /-- The candidate value of the predicted bit. -/
  bit : Bool
  /-- The padding bits after position `pos`. -/
  tail : {j : Fin m // pos < j} → Bool

namespace Reconstruction

variable {D : Design ℓ n a m}

/-- The padding of a reconstruction as a string of `m` bits, `false` up to position `pos`. -/
def pad (R : Reconstruction D) (j : Fin m) : Bool :=
  if h : R.pos < j then R.tail ⟨j, h⟩ else false

/-- The guess of a reconstruction at the input `x`: the test is run on the table values at `x` for
the positions before `pos`, the candidate bit at `pos`, and the padding after `pos`; the guess is
the candidate bit if the test accepts and its negation otherwise (`nextBitGuess`). -/
def guess (R : Reconstruction D) (test : (Fin m → Bool) → Bool) (x : Fin n → Bool) : Bool :=
  nextBitGuess test R.pos R.bit R.pad fun j => R.table j fun k => x k

variable (D) in
/-- The reconstruction of the trial `t` for the hard function `f`: the table of output bit `j` is
read off the generator on the seed that agrees with `t.seed` outside the `t.pos`-th block. -/
def ofTrial (f : (Fin n → Bool) → Bool) (t : Trial ℓ m) : Reconstruction D where
  pos := t.pos
  table j y := generator D f (D.extend t.pos
    (fun k => if h : k ∈ D.overlap t.pos (Fin.castLE t.pos.isLt.le j) then y ⟨k, h⟩ else false)
    t.seed) (Fin.castLE t.pos.isLt.le j)
  bit := t.bit
  tail j := t.pad j

/-- The reconstruction of a trial guesses as the trial does. -/
theorem guess_ofTrial (f : (Fin n → Bool) → Bool) (test : (Fin m → Bool) → Bool)
    (t : Trial ℓ m) : (ofTrial D f t).guess test = trialGuess D f test t := by
  funext x
  have hinput : (fun j : Fin m => if h : (j : ℕ) < t.pos then (ofTrial D f t).table ⟨j, h⟩
        (fun k => x k) else if j = t.pos then t.bit else (ofTrial D f t).pad j) =
      fun j : Fin m => if h : (j : ℕ) < t.pos then
        Fin.take t.pos t.pos.isLt.le (generator D f (D.extend t.pos x t.seed)) ⟨j, h⟩
        else if j = t.pos then t.bit else t.pad j := by
    funext j
    by_cases h : (j : ℕ) < t.pos
    · simp only [h, ↓reduceDIte, ofTrial, Fin.take_apply]
      exact dependsOn_generator_extend D f t.pos _ t.seed fun k hk => dite_eq_left hk
    · have hlt (hji : j ≠ t.pos) : t.pos < j :=
        lt_of_le_of_ne (not_lt.mp h) (Ne.symm hji)
      simp only [h, ↓reduceDIte]
      split_ifs with hji
      · rfl
      · simp [pad, ofTrial, hlt hji]
  exact congrArg (fun y => if test y then t.bit else !t.bit) hinput

end Reconstruction

/-- The number of bits of a reconstruction at position `i`: `2 ^ #(D.overlap i j)` table entries
for each earlier position `j`, then `m - i - 1` padding bits and the candidate bit. -/
def reconstructionBits (D : Design ℓ n a m) (i : Fin m) : ℕ :=
  ∑ j : Fin i, 2 ^ #(D.overlap i (Fin.castLE i.isLt.le j)) + (m - (i : ℕ))

/-- A reconstruction has at most `m 2 ^ a` bits. -/
theorem reconstructionBits_le (D : Design ℓ n a m) (i : Fin m) :
    reconstructionBits D i ≤ m * 2 ^ a := by
  have htable : ∑ j : Fin i, (2 : ℕ) ^ #(D.overlap i (Fin.castLE i.isLt.le j)) ≤
      (i : ℕ) * 2 ^ a := by
    calc _ ≤ ∑ _j : Fin i, (2 : ℕ) ^ a := sum_le_sum fun j _ =>
          Nat.pow_le_pow_right two_pos (D.card_overlap_le (Fin.ne_of_gt j.isLt))
      _ = i * 2 ^ a := by simp
  have hpad : m - (i : ℕ) ≤ (m - i) * 2 ^ a := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a)
  have hm : (i : ℕ) * 2 ^ a + (m - i) * 2 ^ a = m * 2 ^ a := by
    rw [← add_mul, Nat.add_sub_cancel' i.isLt.le]
  unfold reconstructionBits
  omega

/-! ### Randomized list decoding -/

section ListDecoding

variable {α : Type*} {L : ℕ} [DecidableEq α]

/-- The candidates listed by the trials `ts`: the union of the candidates that the list code `C`
decodes from their guesses. -/
def trialCandidates (C : ListCode α (Fin n → Bool) Bool L) (D : Design ℓ n a m)
    (f : (Fin n → Bool) → Bool) (test : (Fin m → Bool) → Bool) {k : ℕ}
    (ts : Fin k → Trial ℓ m) : Finset α :=
  univ.biUnion fun j => C.candidates (trialGuess D f test (ts j))

variable (C : ListCode α (Fin n → Bool) Bool L) (D : Design ℓ n a m) (test : (Fin m → Bool) → Bool)

/-- **List size.** `k` trials list at most `k L` candidates. -/
theorem card_trialCandidates_le (f : (Fin n → Bool) → Bool) {k : ℕ} (ts : Fin k → Trial ℓ m) :
    #(trialCandidates C D f test ts) ≤ k * L :=
  (card_biUnion_le_card_mul _ _ L fun j _ => C.card_candidates_le _).trans_eq <| by simp

/-- **Sampling and list decoding** [Hirahara2018]. Let `0 < m`, `0 ≤ ε`, let the list code `C`
list decode up to radius `1 / 2 - ε / (2 m)`, and let a deterministic test accept outputs of the
generator built from the codeword of `x` with probability at least `ε` more than uniform strings.
Then `C` lists `x` among the candidates for the guess of a uniformly random trial with probability
at least `ε / (2 m)`. -/
theorem div_two_mul_le_dens_mem_candidates (hm : 0 < m) {ε : ℝ} (hε₀ : 0 ≤ ε)
    (hC : C.ListDecodes (1 / 2 - ε / (2 * m))) {x : α}
    (hε : ε ≤ ((generator D (C.encode x)).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal) :
    ε / (2 * m) ≤
      (dens {t : Trial ℓ m | x ∈ C.candidates (trialGuess D (C.encode x) test t)} : ℝ) := by
  refine (div_two_mul_le_dens_goodTrials D (C.encode x) test hm hε₀ hε).trans ?_
  refine NNRat.cast_le.mpr (dens_le_dens fun t ht => ?_)
  rw [mem_goodTrials, trialAgreement] at ht
  simp only [mem_filter, mem_univ, true_and]
  refine hC.mem_candidates_of_half_add_le ?_
  simpa only [eq_comm] using ht

/-- **Repeated sampling and list decoding** [Hirahara2018]. Under the hypotheses of
`div_two_mul_le_dens_mem_candidates`, the at most `k L` candidates listed by `k` independent
uniformly random trials include `x` with probability at least `1 - (1 - ε / (2 m)) ^ k`. -/
theorem one_sub_pow_le_dens_mem_trialCandidates (hm : 0 < m) {ε : ℝ} (hε₀ : 0 ≤ ε)
    (hC : C.ListDecodes (1 / 2 - ε / (2 * m))) {x : α}
    (hε : ε ≤ ((generator D (C.encode x)).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal) (k : ℕ) :
    1 - (1 - ε / (2 * m)) ^ k ≤
      (dens {ts : Fin k → Trial ℓ m | x ∈ trialCandidates C D (C.encode x) test ts} : ℝ) := by
  have : NeZero m := ⟨hm.ne'⟩
  have h := Fintype.one_sub_pow_le_dens_filter_exists_apply_mem (ι := Fin k)
    (div_two_mul_le_dens_mem_candidates C D test hm hε₀ hC hε)
  rw [Fintype.card_fin] at h
  refine h.trans_eq ?_
  congr 3
  ext ts
  simp [trialCandidates]

end ListDecoding

end Cslib.Crypto.PRG.NisanWigderson
