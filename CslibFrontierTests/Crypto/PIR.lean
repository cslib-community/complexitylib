/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.LocallyDecodable.Hadamard
import CslibFrontier.Crypto.Protocols.PIR.Cube
import CslibFrontier.Crypto.Protocols.PIR.SingleServer
import CslibFrontier.Crypto.Protocols.PIR.SmoothCode
import Mathlib.Tactic.NormNum

/-!
# Tests: private information retrieval

* The two-server scheme reads a bit of a three-bit database: the identity behind its
  reconstruction holds for every database, set and index (checked by `decide`), the scheme is
  correct and private with `8` bits, and the two servers together learn the index.
* The rows transformation reads a nine-bit database with two servers and `12` bits, and the
  subcube scheme reads an eight-bit database with eight servers and `56` bits.
* One server needs exactly `n` bits: a three-bit database has a one-server scheme with three
  bits and none with two.
* Both hypotheses of the lower bound are needed. The scheme that sends the index to the server is
  correct and communicates `3` bits for a four-bit database, so it is not private; the scheme that
  always outputs `false` is private and communicates nothing, but it is not correct.
* The library's Hadamard decoder (`BitString.hadamardDecoder`) has uniform reads
  (`BitString.map_hadamardDecoder_query`) and decodes codewords exactly, so its reads and output
  give a two-server scheme with `2 (3 + 1)` bits for a three-bit database, as the two-server scheme
  does.
-/

namespace ComplexityTests.Crypto.PIR

open Cslib Cslib.Crypto.Protocols.PIR Cslib.BitString Cslib.Code Probability

/-! ### Two servers -/

/-- The reconstruction identity of the two-server scheme on three bits: the parities of `x` on
`t` and on `t + eᵢ` add up to `x i`. -/
example : ∀ x t : Fin 3 → Bool, ∀ i : Fin 3, x ⬝ᵥ t + x ⬝ᵥ (t + Pi.single i true) = x i := by
  decide

example : (twoServer (Fin 3)).IsCorrect ∧ (twoServer (Fin 3)).IsPrivate :=
  ⟨isCorrect_twoServer, isPrivate_twoServer⟩

example : communication Bool (Fin 3 → Bool) Bool = 8 := by
  rw [communication_twoServer, Fintype.card_fin]

example : HasScheme (Fin 3) 2 8 := by
  have h := isCorrect_twoServer.hasScheme (isPrivate_twoServer (ι := Fin 3))
  rwa [Fintype.card_bool, communication_twoServer, Fintype.card_fin] at h

/-- The two servers together learn the index: their queries add up to `eᵢ`. -/
example (i : Fin 3) (r : Unit) (q : Bool → Fin 3 → Bool)
    (hrq : (r, q) ∈ (ProbComp.eval ((twoServer (Fin 3)).query i)).support) :
    q false + q true = Pi.single i true :=
  query_add_query_twoServer hrq

/-! ### Rows and subcubes -/

example : communication Bool (Fin 3 → Bool) (Fin 3 → Bool) = 12 := by
  rw [communication_twoServer_rows, Fintype.card_fin]

example : HasScheme (Fin 9) 2 12 :=
  hasScheme_two_of_le_mul_self (n := 9) (m := 3) le_rfl

example : HasScheme (Fin 10) 2 16 := by
  have h : Nat.sqrt 10 = 3 := Nat.sqrt_add_eq (a := 1) 3 (by norm_num)
  have h2 := hasScheme_two_sqrt 10
  rwa [h] at h2

example : (cube (Fin 2) (Fin 2)).IsCorrect ∧ (cube (Fin 2) (Fin 2)).IsPrivate :=
  ⟨isCorrect_cube, isPrivate_cube⟩

example : HasScheme (Fin 8) 8 56 :=
  hasScheme_two_pow_of_le_pow (n := 8) (d := 3) (ℓ := 2) le_rfl

/-! ### One server -/

example : HasScheme (Fin 3) 1 3 :=
  (hasScheme_one_iff (Fin 3) 3).mpr le_rfl

example : ¬ HasScheme (Fin 3) 1 2 := fun h => by
  have := h.card_le
  rw [Fintype.card_fin] at this
  omega

/-- The scheme that sends the index itself to a single server. -/
noncomputable def direct (ι : Type) : Scheme ι Unit Unit ι Bool where
  query i := pure ((), fun _ => i)
  answer _ x j := x j
  reconstruct _ _ a := a ()

theorem isCorrect_direct (ι : Type) : (direct ι).IsCorrect := by
  rw [Scheme.isCorrect_iff]
  intro x i r q hrq
  simp only [direct, ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hrq
  obtain ⟨-, rfl⟩ := hrq
  rfl

/-- The scheme that sends the index is correct and communicates fewer than `4` bits for a
four-bit database, so the single-server lower bound shows that it is not private. -/
example : ¬ (direct (Fin 4)).IsPrivate := fun hprivate => by
  have h := (direct (Fin 4)).card_le_communication (isCorrect_direct (Fin 4)) hprivate
  rw [communication_eq, Fintype.card_unit, Fintype.card_fin, Fintype.card_bool,
    show (4 : ℕ) = 2 ^ 2 from rfl, Nat.clog_pow 2 _ (by norm_num), Nat.clog_eq_one le_rfl le_rfl]
    at h
  omega

/-- The same, directly: the server sees the index. -/
example : ¬ (direct (Fin 2)).IsPrivate := fun hprivate => by
  have h := hprivate.eval_serverQuery_eq () 0 1
  simp only [Scheme.eval_serverQuery, direct, ProbComp.eval_pure, PMF.pure_map] at h
  have hs := congrArg PMF.support h
  rw [PMF.support_pure, PMF.support_pure, Set.singleton_eq_singleton_iff] at hs
  exact absurd hs (by decide)

/-- The scheme that always outputs `false`. -/
noncomputable def constFalse (ι : Type) : Scheme ι Unit Unit Unit Unit where
  query _ := pure ((), fun _ => ())
  answer _ _ _ := ()
  reconstruct _ _ _ := false

theorem isPrivate_constFalse (ι : Type) : (constFalse ι).IsPrivate :=
  (constFalse ι).isPrivate_iff.mpr fun _ _ _ => by
    simp only [Scheme.eval_serverQuery, constFalse, ProbComp.eval_pure, PMF.pure_map]

example : communication Unit Unit Unit = 0 := by
  rw [communication_eq, Fintype.card_unit, Nat.clog_one_right]

example : ¬ (constFalse (Fin 1)).IsCorrect := fun hcorrect => by
  have h := hcorrect.reconstruct_eq (fun _ => true) 0 (r := ()) (q := fun _ => ())
    (by simp only [constFalse, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff])
  exact absurd h (by decide)

/-! ### From the Hadamard code -/

section Hadamard

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The positions that the library's Hadamard decoder reads for the bit `i`: `r` and `eᵢ + r`. -/
private def hadamardReads (i : ι) (r : ι → Bool) : Fin 2 → ι → Bool :=
  ![r, Pi.single i true + r]

/-- The output function of the library's Hadamard decoder. -/
private def hadamardOutput (_ : ι) (_ : ι → Bool) (a : Fin 2 → Bool) : Bool :=
  a 0 ^^ a 1

/-- These are the reads and the output of `BitString.hadamardDecoder`. -/
private theorem hadamardDecoder_eq (i : ι) :
    hadamardDecoder i =
      nonadaptive (ProbComp.uniform (ι → Bool)) (hadamardReads i) (hadamardOutput i) := by
  rw [hadamardDecoder]
  rfl

/-- The Hadamard decoder decodes every codeword with probability one. -/
private theorem decodeLaw_hadamard (x : ι → Bool) (i : ι) :
    decodeLaw (nonadaptive (ProbComp.uniform (ι → Bool)) (hadamardReads i) (hadamardOutput i))
      (hadamardCode x) = PMF.pure (x i) := by
  rw [← hadamardDecoder_eq, decodeLaw_hadamardDecoder]
  have h : selfCorrect (hadamardCode x) (Pi.single i true) = Function.const _ (x i) := by
    funext r
    rw [selfCorrect_hadamardCode, hadamardCode_single, Function.const_apply]
  rw [h, PMF.map_const]

omit [DecidableEq ι] in
/-- The Hadamard decoder gives a two-server scheme with `2 (n + 1)` bits. -/
private theorem hasScheme_hadamard : HasScheme ι 2 (2 * (Fintype.card ι + 1)) := by
  classical
  have h := hasScheme_ofDecoder hadamardCode (fun _ => ProbComp.uniform (ι → Bool))
    hadamardReads hadamardOutput (fun i k => map_hadamardDecoder_query i k) decodeLaw_hadamard
  rwa [Fintype.card_fun, Fintype.card_bool, Nat.clog_pow 2 _ (by norm_num),
    Nat.clog_eq_one le_rfl le_rfl] at h

end Hadamard

example : HasScheme (Fin 3) 2 8 := by
  have h := hasScheme_hadamard (ι := Fin 3)
  rwa [Fintype.card_fin] at h

end ComplexityTests.Crypto.PIR
