/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

import CslibFrontier.Crypto.Protocols.PIR.Block
import Mathlib.Tactic.NormNum

/-!
# Tests: private block retrieval (CGKS Section 4)

* Tight one-server and full-coalition block lower bounds (`hasBlockScheme_one_iff`,
  `BlockScheme.card_mul_le_communication_of_card_le`): `4` blocks of `4` bits need `16` bits with
  one server (or when all `2` of `2` servers collude), so `15` bits is impossible.
* Proposition 4 (`Scheme.toBlock` and `communication_toBlock_of_card_answer`):
  - lifting `twoServer (Fin 5)` to `6`-bit blocks uses `22` bits (vs. `30` for one server);
  - lifting `2`-private Shamir PIR (`shamir (Fin 4)` over `ZMod 5`) to `8`-bit blocks preserves
    both perfect correctness and `2`-privacy.
* Abelian-group homomorphism reduction (`Scheme.mapAnswerHom`) + Proposition 5 (`Scheme.sumChunks`):
  - a two-server scheme returning masked pairs in the non-Boolean group `Bool × Bool` reduces via
    `xorPairHom : Bool × Bool →+ Bool` to a one-bit-answer `HasXorReconstruct` scheme, which then
    composes with `sumChunks` across `m = 3` chunks so each server still replies with `1` bit.
* Corollaries 6, 7 and 8:
  - Corollary 6 (`hasBlockScheme_of_xorReconstruct` and `hasTPrivateBlockScheme_of_xorReconstruct`)
    retrieves a `10`-bit block from `12` blocks with `2` servers and `50` bits (vs. `120` bits);
  - Corollary 7 (`hasBlockScheme_two_of_le`) retrieves an `8`-bit block from `8` blocks with `2`
    servers and `32` bits (vs. `64` bits);
  - Corollary 8 (`hasBlockScheme_four_of_le_sq`, `hasBlockScheme_four_of_le_half_sq`) retrieves an
    `8`-bit block from `16` blocks with `4` servers and `64` bits (vs. `128` bits), and retrieves
    a `9`-bit block from `16` blocks (`4 ^ 2`, `2 * 4 ≤ 9`) in `72` bits.
-/

namespace CslibFrontierTests.Crypto.PIRBlock

open Cslib Cslib.Crypto.Protocols.PIR Cslib.Crypto.Protocols.SecretSharing Probability

/-! ### One-server and full-coalition block lower bounds -/

example : HasBlockScheme (Fin 4) (Fin 4 → Bool) 1 16 :=
  (hasBlockScheme_one_iff (Fin 4) (Fin 4) 16).mpr (by decide)

example : ¬ HasBlockScheme (Fin 4) (Fin 4 → Bool) 1 15 := by
  rw [hasBlockScheme_one_iff]
  decide

example : ¬ HasTPrivateBlockScheme (Fin 4) (Fin 4 → Bool) 2 2 15 := by
  rw [hasTPrivateBlockScheme_iff]
  rintro ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩
  have hlb := P.card_mul_le_communication_of_card_le hcorrect hprivate (by omega)
  rw [Fintype.card_fin] at hlb
  omega

/-! ### Proposition 4: single-bit PIR to `ℓ`-bit block PIR -/

example :
    ((twoServer (Fin 5)).toBlock (Fin 6)).IsCorrect ∧
      ((twoServer (Fin 5)).toBlock (Fin 6)).IsPrivate ∧
      communication Bool (Fin 5 → Bool) (Fin 6 → Bool) = 22 := by
  refine ⟨isCorrect_twoServer.toBlock (Fin 6), isPrivate_twoServer.toBlock (Fin 6), ?_⟩
  rw [communication_toBlock_of_card_answer Bool (Fin 5 → Bool) Bool (Fin 6) (b := 1) (by decide),
    Fintype.card_bool, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin,
    Nat.clog_pow 2 _ (by norm_num)]

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Proposition 4 preserves `2`-privacy when lifting linear Shamir PIR to `8`-bit blocks. -/
example :
    let params := zmodShamirParams (t := 2) (k := 3) (p := 5) (by decide) (by decide)
    ((shamir (Fin 4) params).toBlock (Fin 8)).IsCorrect ∧
      ((shamir (Fin 4) params).toBlock (Fin 8)).IsTPrivate 2 := by
  intro params
  exact ⟨(isCorrect_shamir params).toBlock (Fin 8), (isTPrivate_shamir params).toBlock (Fin 8)⟩

/-! ### Group-homomorphism reduction (`mapAnswerHom`) + Proposition 5 (`sumChunks`) -/

/-- Additive homomorphism `(b₁, b₂) ↦ b₁ + b₂` from `Bool × Bool` to `Bool` (`BooleanRing` XOR). -/
private def xorPairHom : Bool × Bool →+ Bool where
  toFun p := p.1 + p.2
  map_zero' := rfl
  map_add' p q := by
    rcases p with ⟨p₁, p₂⟩
    rcases q with ⟨q₁, q₂⟩
    cases p₁ <;> cases p₂ <;> cases q₁ <;> cases q₂ <;> rfl

/-- A two-server scheme on `Option (Fin 3)` whose server answers are `2`-bit pairs in `Bool × Bool`
(`(parity + q 0, q 0)`), reconstructing via `xorPairHom (a false + a true)`. -/
private noncomputable def pairedTwoServer :
    Scheme (Option (Fin 3)) Bool Unit (Option (Fin 3) → Bool) (Bool × Bool) where
  query := (twoServer (Option (Fin 3))).query
  answer σ x q := ((twoServer (Option (Fin 3))).answer σ x q + q none, q none)
  reconstruct _ _ a := xorPairHom (∑ σ : Bool, a σ)

private theorem isCorrect_pairedTwoServer : pairedTwoServer.IsCorrect := by
  rw [Scheme.isCorrect_iff]
  intro x o r q hrq
  have hbase := (isCorrect_twoServer (ι := Option (Fin 3))).reconstruct_eq x o hrq
  rw [reconstruct_twoServer] at hbase
  dsimp only [pairedTwoServer, xorPairHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Fintype.sum_bool]
  change (((twoServer (Option (Fin 3))).answer true x (q true) + q true none) +
      ((twoServer (Option (Fin 3))).answer false x (q false) + q false none)) +
    (q true none + q false none) = x o
  rw [← hbase]
  generalize (twoServer (Option (Fin 3))).answer false x (q false) = a₀
  generalize (twoServer (Option (Fin 3))).answer true x (q true) = a₁
  generalize q false none = m₀
  generalize q true none = m₁
  cases a₀ <;> cases a₁ <;> cases m₀ <;> cases m₁ <;> rfl

private theorem isPrivate_pairedTwoServer : pairedTwoServer.IsPrivate := by
  rw [Scheme.isPrivate_iff]
  intro σ i i'
  rw [Scheme.eval_serverQuery, Scheme.eval_serverQuery]
  dsimp only [pairedTwoServer]
  rw [← Scheme.eval_serverQuery, ← Scheme.eval_serverQuery]
  exact isPrivate_twoServer.eval_serverQuery_eq σ i i'

/-- End-to-end check of the CGKS §4.1 homomorphism note + Proposition 5: `mapAnswerHom` compresses
`Bool × Bool` answers to `1` bit with `HasXorReconstruct`, and `sumChunks 3` then expands `3`
chunks while keeping `1`-bit server answers (`26` total bits across `2` servers). -/
example :
    let P₁ := pairedTwoServer.mapAnswerHom (fun _ p => p) xorPairHom
    (P₁.sumChunks 3).IsCorrect ∧
      (P₁.sumChunks 3).IsPrivate ∧
      (P₁.sumChunks 3).HasXorReconstruct ∧
      communication Bool (Fin 3 → Option (Fin 3) → Bool) Bool ≤ 26 := by
  intro P₁
  have hC₁ : P₁.IsCorrect :=
    isCorrect_pairedTwoServer.mapAnswerHom (fun _ p => p) xorPairHom (fun _ _ _ => rfl)
  have hP₁ : P₁.IsPrivate :=
    isPrivate_pairedTwoServer.mapAnswerHom (fun _ p => p) xorPairHom
  have hX₁ : P₁.HasXorReconstruct :=
    Scheme.hasXorReconstruct_mapAnswerHom pairedTwoServer (fun _ p => p) xorPairHom
  refine ⟨hC₁.sumChunks 3 hX₁, hP₁.sumChunks 3, Scheme.hasXorReconstruct_sumChunks 3 P₁, ?_⟩
  have hcomm := communication_sumChunks_le Bool (Option (Fin 3) → Bool) 3
  have hcard : Fintype.card (Option (Fin 3) → Bool) = 16 := by decide
  have hclog : Nat.clog 2 16 = 4 := by decide
  rw [Fintype.card_bool, hcard, hclog] at hcomm
  omega

/-! ### Corollaries 6, 7 and 8 -/

/-- Corollary 6: `N = 12 ≤ 3 * 4` blocks of `ℓ = 10` bits with `twoServer (Option (Fin 4))`
(`|Q| = 32`, `⌈log₂ |Q|⌉ = 5`) uses `2 * (3 * 5 + 10) = 50` bits (vs. `120` bits for `1` server). -/
example : HasBlockScheme (Fin 12) (Fin 10 → Bool) 2 50 := by
  have h := hasBlockScheme_of_xorReconstruct (N := 12) (m := 3) (n := 4) (ℓ := 10)
    (isCorrect_twoServer (ι := Option (Fin 4)))
    (isPrivate_twoServer (ι := Option (Fin 4)))
    (Scheme.hasXorReconstruct_twoServer (Option (Fin 4)))
    (by decide)
  have hcard : Fintype.card (Option (Fin 4) → Bool) = 32 := by decide
  have hclog : Nat.clog 2 32 = 5 := by decide
  rw [Fintype.card_bool, hcard, hclog] at h
  exact h

/-- `t`-private Corollary 6 (`t = 1` on `twoServer (Option (Fin 2))`, `2` servers, `34` bits). -/
example : HasTPrivateBlockScheme (Fin 6) (Fin 8 → Bool) 1 2 34 := by
  have h := hasTPrivateBlockScheme_of_xorReconstruct (N := 6) (m := 3) (n := 2) (ℓ := 8) (t := 1)
    (isCorrect_twoServer (ι := Option (Fin 2)))
    (Scheme.isTPrivate_one_iff.mpr (isPrivate_twoServer (ι := Option (Fin 2))))
    (Scheme.hasXorReconstruct_twoServer (Option (Fin 2)))
    (by decide)
  have hcardQ : Fintype.card (Option (Fin 2) → Bool) = 8 := by decide
  have hclog : Nat.clog 2 8 = 3 := by decide
  rw [Fintype.card_bool, hcardQ, hclog] at h
  exact h

/-- Corollary 7: `n = 8 ≤ ℓ = 8` uses `4 * 8 = 32` bits with `2` servers (vs. `64` for `1`). -/
example : HasBlockScheme (Fin 8) (Fin 8 → Bool) 2 32 :=
  hasBlockScheme_two_of_le (n := 8) (ℓ := 8) le_rfl

/-- Corollary 8 (`n ≤ (ℓ / 2) ^ 2`): `n = 16`, `ℓ = 8` uses `8 * 8 = 64` bits with `4` servers
(vs. `128` for `1` server). -/
example : HasBlockScheme (Fin 16) (Fin 8 → Bool) 4 64 :=
  hasBlockScheme_four_of_le_half_sq (n := 16) (ℓ := 8) (by decide)

/-- Corollary 8 (`n ≤ m ^ 2`, `2 * m ≤ ℓ`): for odd `ℓ = 9`, `n = 16 ≤ 4 * 4` and `2 * 4 ≤ 9` gives
`8 * 9 = 72` bits with `4` servers (vs. `144` for `1` server). -/
example : HasBlockScheme (Fin 16) (Fin 9 → Bool) 4 72 :=
  hasBlockScheme_four_of_le_sq (n := 16) (m := 4) (ℓ := 9) (by decide) (by decide)

end CslibFrontierTests.Crypto.PIRBlock
