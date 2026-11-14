/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

module

import CslibFrontier.Crypto.Protocols.PIR.GeneralCover
import CslibFrontier.Crypto.Protocols.PIR.MultiInteractive
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Uniform

/-! # Checked examples for heterogeneous covering PIR, radius-`r` covers, and interactive bounds -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.PIRGeneralCover

open Cslib Cslib.Crypto.Protocols Cslib.Crypto.Protocols.PIR Probability

/-! ### 1. Heterogeneous per-server widths (`PIR.IndexedScheme`) -/

/-- Server `false` returns `1` bit (`Bool`) and server `true` returns `2` bits (`Bool × Bool`). -/
def AsymmetricAns : Bool → Type
  | false => Bool
  | true => Bool × Bool

instance (b : Bool) : Fintype (AsymmetricAns b) := by
  cases b <;> dsimp only [AsymmetricAns] <;> infer_instance

/-- Asymmetric `2`-server `IndexedScheme` where server `false` returns `1` bit (`Bool`) and server
`true` returns `2` bits (`Bool × Bool`), demonstrating unequal per-server wire widths (`9 < 10`). -/
noncomputable def asymmetricTwoServer (ι : Type) [Fintype ι] [DecidableEq ι] :
    IndexedScheme ι Bool Unit (fun _ => ι → Bool) AsymmetricAns where
  query := (twoServer ι).query
  answer
    | false, x, q => BitString.hadamardCode x q
    | true, x, q => (BitString.hadamardCode x q, false)
  reconstruct _ _ a :=
    let a₀ : Bool := a false
    let a₁ : Bool × Bool := a true
    a₀ + a₁.1

example : indexedCommunication Bool (fun _ => Fin 3 → Bool) AsymmetricAns = 9 := by
  rw [indexedCommunication_eq, Fintype.sum_bool]
  decide

example : (asymmetricTwoServer (Fin 3)).IsPrivate := by
  rw [IndexedScheme.isPrivate_iff]
  intro s i i'
  have hq (idx : Fin 3) : ProbComp.eval ((asymmetricTwoServer (Fin 3)).serverQuery s idx) =
      ProbComp.eval ((twoServer (Fin 3)).serverQuery s idx) := by
    rw [IndexedScheme.eval_serverQuery, Scheme.eval_serverQuery]
    rfl
  rw [hq i, hq i', isPrivate_twoServer.eval_serverQuery_eq s i i']

example : (asymmetricTwoServer (Fin 3)).IsCorrect := by
  rw [IndexedScheme.isCorrect_iff]
  intro x i r q hrq
  have h := isCorrect_twoServer.reconstruct_eq x i hrq
  rw [reconstruct_twoServer, answer_twoServer, answer_twoServer] at h
  exact h

/-- Tight `1`-server `IndexedScheme` bound on `4` bits (`4` achievable, `3` impossible). -/
example : HasIndexedScheme (Fin 4) 1 4 :=
  (hasIndexedScheme_one_iff (Fin 4) 4).mpr (by simp)

example : ¬ HasIndexedScheme (Fin 4) 1 3 := by
  rw [hasIndexedScheme_one_iff]
  simp

/-- Full-coalition impossibility for heterogeneous `2`-server `2`-private schemes on `5` bits. -/
example : ¬ HasTPrivateIndexedScheme (Fin 5) 2 2 4 := by
  intro h
  have hle := h.card_le_of_le le_rfl
  simp at hle

/-! ### 2. Unbalanced CGKS §3.3 Theorem 1 (`d = 5, k = 7`, CGKS Figure 1) -/

/-- Because `7 ∤ 32`, no balanced `RadiusOneCover (Fin 7) (Fin 5) M` can exist for any finite `M`.
-/
example : ¬ ∃ (M : Type) (_ : Fintype M), 7 * (Fintype.card M + 1) = 2 ^ 5 := by
  rintro ⟨M, _, hbal⟩
  omega

/-- With per-server answer widths, `sevenWordCode` gives `7` servers and `60 · ℓ + 7` bits: at
`n = 2 ^ 20` (`ℓ = 16`), `967` bits vs. `1127` bits in the uniform `ofHammingDist` cover and `2592`
bits in `cube (Fin 5)`. -/
example : HasIndexedScheme (Fin (2 ^ 20)) 7 967 :=
  hasIndexedScheme_seven_of_le_pow_five (ℓ := 16) (by decide)

/-- Nonvacuous small database (`n = 243 = 3 ^ 5`, `187 < 243` bits) and empty database (`n = 0`). -/
example : HasIndexedScheme (Fin 243) 7 187 :=
  hasIndexedScheme_seven_of_le_pow_five (ℓ := 3) (by decide)

example : HasIndexedScheme (Fin 0) 7 7 :=
  hasIndexedScheme_seven_of_le_pow_five (ℓ := 0) (by decide)

/-- `ExactRadiusOneCover.ofHammingDist` preserves the underlying codeword assignment. -/
example : (ExactRadiusOneCover.ofHammingDist sevenWordCode sevenWordCode_injective
    sevenWordCode_covers).code = sevenWordCode := by
  simp

/-- `emulateCubeQuery` flips the selected coordinate inside `T` and leaves coordinates outside `T`
unchanged. -/
example (a : Fin 2 → Fin 3 → Bool) :
    emulateCubeQuery a {0} (fun _ => (1 : Fin 3)) 0 = a 0 + Pi.single 1 true ∧
      emulateCubeQuery a {0} (fun _ => (1 : Fin 3)) 1 = a 1 := by
  simp

/-! ### 3. General radius-`r` and radius-`2` covering-code PIR (`CGKS §3.3, pp. 9–10`) -/

/-- Radius-`2` ball query count on `Fin 5` with side length `3`: `1 + 5·3 + 10·9 = 106`. -/
example : Fintype.card (RadiusBallQuery (Fin 5) 2 (Fin 3)) = 106 := by
  rw [card_radiusBallQuery]
  decide

/-- `{00000, 11111}` covers `Fin 5 → Bool` at radius `2` (achieving `21 122 < 2 ^ 25` bits at
`n = 2 ^ 25, ℓ = 32`, i.e., CGKS p. 10's displayed `20 800` leading term plus `322` radius-`0`/`1`
answer bits, and satisfying the coarser `k d ℓ + k d² ℓ² = 51 520` bound), whereas a single
codeword `{00000}` does not cover `Fin 5 → Bool` at radius `2`. -/
example : HasScheme (Fin (2 ^ 25)) 2 21122 :=
  hasScheme_two_radius_two_of_le_pow_five (ℓ := 32) (by decide)

example : HasScheme (Fin (2 ^ 25)) 2 (2 * 5 * 32 + 2 * 5 ^ 2 * 32 ^ 2) :=
  hasScheme_of_hammingDist_two_sq repetitionFive_covers_two (by decide) (ℓ := 32) (by decide)
    (by decide)

example : ¬ ∀ w : Fin 5 → Bool, hammingDist (fun _ : Fin 5 => false) w ≤ 2 := by
  decide

/-! ### 4. Interactive block bounds and multi-server full-coalition interactive bounds -/

/-- Single-server interactive block retrieval on `3` blocks of `4` bits needs `12` bits (`11` is
impossible, `12` is achieved by `InteractiveScheme.blockDownload 3 4`). -/
example : (InteractiveScheme.blockDownload 3 4).protocol.depth = 12 :=
  InteractiveScheme.depth_blockDownload 3 4

example : ¬ ∃ (C D : Type) (P : InteractiveScheme (Fin 3) C D (BitString 4)),
    P.IsCorrect ∧ P.IsPrivate ∧ P.protocol.depth ≤ 11 := by
  rw [InteractiveScheme.exists_block_iff]
  decide

/-- Flip bit `idx` of a `2`-bit mask `c : Fin 2 → Bool` (computable involution). -/
def flipTwoBit (idx : Fin 2) : (Fin 2 → Bool) ≃ (Fin 2 → Bool) where
  toFun c j := c j != decide (j = idx)
  invFun c j := c j != decide (j = idx)
  left_inv c := by
    funext j
    revert c idx j
    decide
  right_inv c := by
    funext j
    revert c idx j
    decide

/-- Concrete `2`-server `1`-private multi-round scheme on `Fin 2` (`depth = 6`): the user sends the
`2`-bit mask `c` to server `false`, receives its parity bit `b₀`, then sends `c + eᵢ` to server
`true`, receives its parity bit `b₁`, and outputs `b₀ != b₁` (`b₀ + b₁`). -/
noncomputable def twoServerMultiRound :
    MultiInteractiveScheme (Fin 2) Bool (Fin 2 → Bool) (fun _ => Unit) where
  userCoins _ := ProbComp.uniform (Fin 2 → Bool)
  serverCoins := pure fun _ => ()
  serverBit _ x _ hist :=
    (x 0 && (hist.getD 0 (.fromUser false)).bit) != (x 1 && (hist.getD 1 (.fromUser false)).bit)
  tree :=
    let recvTrue (b₀ : Bool) :
        MultiRoundTree Bool (Fin 2 × (Fin 2 → Bool)) (Fin 2 × (Fin 2 → Bool) → Bool) :=
      .sendTo true (fun ⟨i, c⟩ => c 0 != decide (i = 0))
        (.sendTo true (fun ⟨i, c⟩ => c 1 != decide (i = 1))
          (.recvFrom true (.output fun _ => b₀) (.output fun _ => !b₀))
          (.recvFrom true (.output fun _ => b₀) (.output fun _ => !b₀)))
        (.sendTo true (fun ⟨i, c⟩ => c 1 != decide (i = 1))
          (.recvFrom true (.output fun _ => b₀) (.output fun _ => !b₀))
          (.recvFrom true (.output fun _ => b₀) (.output fun _ => !b₀)))
    .sendTo false (fun ⟨_, c⟩ => c 0)
      (.sendTo false (fun ⟨_, c⟩ => c 1)
        (.recvFrom false (recvTrue false) (recvTrue true))
        (.recvFrom false (recvTrue false) (recvTrue true)))
      (.sendTo false (fun ⟨_, c⟩ => c 1)
        (.recvFrom false (recvTrue false) (recvTrue true))
        (.recvFrom false (recvTrue false) (recvTrue true)))

example : twoServerMultiRound.tree.depth = 6 := rfl

theorem run_twoServerMultiRound :
    ∀ (x : Fin 2 → Bool) (i : Fin 2) (c : Fin 2 → Bool) (d : Bool → Unit),
      (twoServerMultiRound.tree.compile twoServerMultiRound.serverBit (fun _ => [])).run
        (x, d) (i, c) (i, c) = x i := by
  decide

example : twoServerMultiRound.IsCorrect := by
  rw [MultiInteractiveScheme.isCorrect_iff]
  intro x i c _ d _
  change (twoServerMultiRound.tree.compile twoServerMultiRound.serverBit (fun _ => [])).leafOutput _
      _ = x i
  rw [← Communication.Protocol.run_eq_leafOutput_leaf]
  exact run_twoServerMultiRound x i c d

example : twoServerMultiRound.IsPrivate := by
  rw [MultiInteractiveScheme.isPrivate_iff]
  intro s x i i'
  have hcoins (idx : Fin 2) :
      ProbComp.eval (twoServerMultiRound.toInteractiveScheme.coins idx) =
        (PMF.uniformOfFintype (Fin 2 → Bool)).map fun c => (c, fun _ : Bool => ()) := by
    rw [InteractiveScheme.eval_coins, MultiInteractiveScheme.toInteractiveScheme_userCoins,
      MultiInteractiveScheme.toInteractiveScheme_serverCoins]
    simp only [twoServerMultiRound, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.pure_map]
    rfl
  cases s
  · -- Server `false` sees `[c 0, c 1, reply(x, c)]` for uniform `c`, independent of `i`.
    rw [MultiInteractiveScheme.eval_serverTranscript, MultiInteractiveScheme.eval_serverTranscript,
      hcoins i, hcoins i', PMF.map_comp, PMF.map_comp]
    congr 1
    funext c
    revert x i i' c
    decide
  · -- Server `true` sees `[q 0, q 1, reply(x, q)]` for `q = flipTwoBit i c`, which has the same
    -- uniform law as `c`.
    rw [MultiInteractiveScheme.eval_serverTranscript, MultiInteractiveScheme.eval_serverTranscript,
      hcoins i, hcoins i', PMF.map_comp, PMF.map_comp]
    let traceTrue (q : Fin 2 → Bool) : List ChannelMsg :=
      let b₁ := (x 0 && q 0) != (x 1 && q 1)
      [.fromUser (q 0), .fromUser (q 1), .fromServer b₁]
    have hfactor (idx : Fin 2) :
        (PMF.uniformOfFintype (Fin 2 → Bool)).map
          ((fun cd : (Fin 2 → Bool) × (Bool → Unit) =>
              ((twoServerMultiRound.tree.execTrace twoServerMultiRound.serverBit
                  (fun _ => []) x cd.2 (idx, cd.1)).filter fun sb => decide (sb.1 = true)).map
                Prod.snd) ∘
            fun c => (c, fun _ : Bool => ())) =
        ((PMF.uniformOfFintype (Fin 2 → Bool)).map (flipTwoBit idx)).map traceTrue := by
      rw [PMF.map_comp]
      congr 1
      funext c
      revert x idx c
      decide
    rw [hfactor i, hfactor i',
      PMF.uniformOfFintype_map_equiv (flipTwoBit i),
      PMF.uniformOfFintype_map_equiv (flipTwoBit i')]

/-- Concrete `1`-server multi-bit download protocol on `Fin 3` (`depth = 3` with zero user-to-server
messages): the server sends `x 0`, `x 1`, and `x 2` in three consecutive `recvFrom ()` steps using
its directional `ChannelMsg` history length, attaining `card_le_depth_of_card_le` tightly at
`|S| = 1, n = 3`. -/
noncomputable def oneServerMultiDownload :
    MultiInteractiveScheme (Fin 3) Unit Unit (fun _ => Unit) where
  userCoins _ := pure ()
  serverCoins := pure fun _ => ()
  serverBit _ x _ hist :=
    match hist.length with
    | 0 => x 0
    | 1 => x 1
    | _ => x 2
  tree :=
    let step2 (b₀ b₁ : Bool) : MultiRoundTree Unit (Fin 3 × Unit) (Fin 3 × Unit → Bool) :=
      .recvFrom ()
        (.output fun ⟨i, _⟩ => match i with | 0 => b₀ | 1 => b₁ | 2 => false)
        (.output fun ⟨i, _⟩ => match i with | 0 => b₀ | 1 => b₁ | 2 => true)
    .recvFrom ()
      (.recvFrom () (step2 false false) (step2 false true))
      (.recvFrom () (step2 true false) (step2 true true))

example : oneServerMultiDownload.tree.depth = 3 := rfl

theorem run_oneServerMultiDownload :
    ∀ (x : Fin 3 → Bool) (i : Fin 3) (d : Unit → Unit),
      (oneServerMultiDownload.tree.compile oneServerMultiDownload.serverBit (fun _ => [])).run
        (x, d) (i, ()) (i, ()) = x i := by
  decide

example : oneServerMultiDownload.IsCorrect := by
  rw [MultiInteractiveScheme.isCorrect_iff]
  intro x i c _ d _
  cases c
  change (oneServerMultiDownload.tree.compile oneServerMultiDownload.serverBit
      (fun _ => [])).leafOutput _ _ = x i
  rw [← Communication.Protocol.run_eq_leafOutput_leaf]
  exact run_oneServerMultiDownload x i d

example : oneServerMultiDownload.IsTPrivate 1 := by
  rw [MultiInteractiveScheme.isTPrivate_one_iff, MultiInteractiveScheme.isPrivate_iff]
  intro s x i i'
  have hcoins (idx : Fin 3) :
      ProbComp.eval (oneServerMultiDownload.toInteractiveScheme.coins idx) =
        PMF.pure ((), fun _ : Unit => ()) := by
    rw [InteractiveScheme.eval_coins, MultiInteractiveScheme.toInteractiveScheme_userCoins,
      MultiInteractiveScheme.toInteractiveScheme_serverCoins]
    simp [oneServerMultiDownload]
  rw [MultiInteractiveScheme.eval_serverTranscript, MultiInteractiveScheme.eval_serverTranscript,
    hcoins i, hcoins i', PMF.pure_map, PMF.pure_map]
  congr 1

/-- By contrast, when both servers collude (`|S| = 2 ≤ 2`), no `2`-private multi-round scheme on
`Fin 4` can have depth `≤ 3`, and no `2`-private multi-round `2`-bit block scheme on `Fin 3` can
have depth `≤ 5`. -/
example : ¬ ∃ (C : Type) (D : Bool → Type) (P : MultiInteractiveScheme (Fin 4) Bool C D),
    P.IsCorrect ∧ P.IsTPrivate 2 ∧ P.tree.depth ≤ 3 := by
  rintro ⟨C, D, P, hcorr, hpriv, hdepth⟩
  have hle := P.card_le_depth_of_card_le hcorr hpriv (by simp)
  simp only [Fintype.card_fin] at hle
  omega

example : ¬ ∃ (C : Type) (D : Bool → Type)
    (P : MultiInteractiveScheme (Fin 3) Bool C D (BitString 2)),
    P.IsCorrect ∧ P.IsTPrivate 2 ∧ P.tree.depth ≤ 5 := by
  rintro ⟨C, D, P, hcorr, hpriv, hdepth⟩
  have hle := P.card_mul_le_depth_of_card_le hcorr hpriv (by simp)
  simp only [Fintype.card_fin] at hle
  omega

end CslibFrontierTests.Crypto.PIRGeneralCover
