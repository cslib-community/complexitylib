/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

import CslibFrontier.Crypto.Protocols.PIR.Block
import CslibFrontier.Crypto.Protocols.PIR.Shamir
import CslibFrontier.Probability.Uniform
import Mathlib.Tactic.NormNum

/-!
# Tests: private block retrieval (CGKS Section 4)

* Tight one-server and full-coalition block lower bounds (`hasBlockScheme_one_iff`,
  `HasTPrivateScheme.card_mul_le_of_le`): `4` blocks of `4` bits need `16` bits with one
  server (or when all `2` of `2` servers collude), so `15` bits is impossible.
* Proposition 4 (`Scheme.toBlock`, `communication_toBlock_of_card_answer`, and
  `communication_toBlock_le`):
  - lifting `twoServer (Fin 5)` to `6`-bit blocks uses `22` bits (vs. `30` for one server);
  - lifting `2`-private Shamir PIR (`shamir (Fin 4)` over `ZMod 5`) to `8`-bit blocks preserves
    both perfect correctness and `2`-privacy and communicates at most `108` bits via
    `communication_toBlock_le`.
* Abelian-group homomorphism reduction (`Scheme.mapAnswerHom`) + Proposition 5 (`Scheme.sumChunks`):
  - a two-server scheme returning masked pairs in the non-Boolean group `Bool × Bool` reduces via
    `xorPairHom : Bool × Bool →+ Bool` to a one-bit-answer `HasXorReconstruct` scheme, which then
    composes with `sumChunks` across `m = 3` chunks so each server still replies with `1` bit.
* Corollaries 6, 7 and 8 (including genuine `t = 2` multi-server collusion):
  - Corollary 6 (`hasBlockScheme_of_xorReconstruct`) retrieves a `10`-bit block from `12` blocks
    with `2` servers and `50` bits (vs. `120` bits);
  - `t = 2` Corollary 6 (`hasTPrivateBlockScheme_of_xorReconstruct`) on a `3`-server additive-mask
    XOR scheme (`threeServerXor`) retrieves a `10`-bit block from `12` blocks with `3` servers,
    `2`-collusion privacy, and `75` bits (vs. `120` bits);
  - Corollary 7 (`hasBlockScheme_two_of_le`) retrieves an `8`-bit block from `8` blocks with `2`
    servers and `32` bits (vs. `64` bits);
  - Corollary 8 (`hasBlockScheme_four_of_le_sq`, `hasBlockScheme_four_of_le_half_sq`) retrieves an
    `8`-bit block from `16` blocks with `4` servers and `64` bits (vs. `128` bits), and retrieves
    a `9`-bit block from `16` blocks (`4 ^ 2`, `2 * 4 ≤ 9`) in `72` bits.
-/

namespace CslibFrontierTests.Crypto.PIRBlock

open Cslib Cslib.Crypto.Protocols.PIR Cslib.Crypto.Protocols.SecretSharing Probability BitString

/-! ### One-server and full-coalition block lower bounds -/

example : HasScheme (Fin 4) 1 16 (Fin 4 → Bool) :=
  (hasBlockScheme_one_iff (Fin 4) (Fin 4) 16).mpr (by decide)

example : ¬ HasScheme (Fin 4) 1 15 (Fin 4 → Bool) := by
  rw [hasBlockScheme_one_iff]
  decide

example : ¬ HasTPrivateScheme (Fin 4) 2 2 15 (Fin 4 → Bool) := fun h => by
  have hlb := h.card_mul_le_of_le le_rfl
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

/-- Proposition 4 preserves `2`-privacy when lifting linear Shamir PIR over `ZMod 5` (`|A| = 5`,
non-power-of-two) to `8`-bit blocks, with `communication_toBlock_le` giving `≤ 108` bits. -/
example :
    let params := zmodShamirParams (t := 2) (k := 3) (p := 5) (by decide) (by decide)
    ((shamir (Fin 4) params).toBlock (Fin 8)).IsCorrect ∧
      ((shamir (Fin 4) params).toBlock (Fin 8)).IsTPrivate 2 ∧
      HasTPrivateScheme (Fin 4) 2 3 108 (Fin 8 → Bool) := by
  intro params
  have hC := (isCorrect_shamir (ι := Fin 4) params).toBlock (Fin 8)
  have hP := (isTPrivate_shamir (ι := Fin 4) params).toBlock (Fin 8)
  have hle := communication_toBlock_le (Fin 3) (Fin 4 → ZMod 5) (ZMod 5) (Fin 8)
  have hcardQ : Fintype.card (Fin 4 → ZMod 5) = 625 := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rfl
  have hclogQ : Nat.clog 2 625 = 10 := by decide
  have hclogA : Nat.clog 2 5 = 3 := by decide
  rw [threshold_zmodShamirParams] at hP
  refine ⟨hC, hP, ?_⟩
  have hB := hC.hasTPrivateScheme hP
  rw [Fintype.card_fin] at hB
  apply hB.mono
  rw [Fintype.card_fin, Fintype.card_fin, hcardQ, ZMod.card, hclogQ, hclogA] at hle
  omega

/-! ### Group-homomorphism reduction (`mapAnswerHom`) + Proposition 5 (`sumChunks`) -/

/-- Additive homomorphism `(b₁, b₂) ↦ b₁ + b₂` from `Bool × Bool` to `Bool` (`BooleanRing` XOR). -/
private def xorPairHom : Bool × Bool →+ Bool where
  toFun p := p.1 + p.2
  map_zero' := add_zero false
  map_add' p q := add_add_add_comm p.1 q.1 p.2 q.2

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
  rw [add_add_add_comm]
  simp only [add_assoc, BooleanRing.add_self, add_zero]
  rw [add_comm, hbase]

private theorem isPrivate_pairedTwoServer : pairedTwoServer.IsPrivate :=
  isPrivate_twoServer.of_query_eq id fun _ => rfl

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

/-! ### `2`-private `3`-server additive-mask XOR scheme for `t = 2` Corollary 6 -/

/-- Three-server `2`-private XOR scheme: servers `0, 1` receive independent uniform masks `u.1, u.2`
and server `2` receives `u.1 + u.2 + eᵢ`, so any `≤ 2` servers see uniform masks while all `3`
one-bit Hadamard answers XOR to `x i`. -/
private def threeServerQuery {ι : Type} [DecidableEq ι] (u : (ι → Bool) × (ι → Bool))
    (e : ι → Bool) : Fin 3 → ι → Bool
  | ⟨0, _⟩ => u.1
  | ⟨1, _⟩ => u.2
  | ⟨_ + 2, _⟩ => u.1 + u.2 + e

private noncomputable def threeServerXor (ι : Type) [Fintype ι] [DecidableEq ι] :
    Scheme ι (Fin 3) Unit (ι → Bool) Bool where
  query i := do
    let u ← ProbComp.uniform ((ι → Bool) × (ι → Bool))
    pure ((), threeServerQuery u (Pi.single i true))
  answer _ x a := hadamardCode x a
  reconstruct _ _ a := ∑ s : Fin 3, a s

private theorem hasXorReconstruct_threeServerXor (ι : Type) [Fintype ι] [DecidableEq ι] :
    (threeServerXor ι).HasXorReconstruct :=
  fun _ _ _ => rfl

private theorem isCorrect_threeServerXor (ι : Type) [Fintype ι] [DecidableEq ι] :
    (threeServerXor ι).IsCorrect := by
  rw [Scheme.isCorrect_iff]
  intro x i _ q hrq
  simp only [threeServerXor, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hrq
  obtain ⟨u, -, -, rfl⟩ := hrq
  change ∑ s : Fin 3, hadamardCode x (threeServerQuery u (Pi.single i true) s) = x i
  rw [Fin.sum_univ_three]
  dsimp only [threeServerQuery]
  rw [hadamardCode_apply, hadamardCode_apply, hadamardCode_apply, ← dotProduct_add,
    ← dotProduct_add]
  have hcancel : u.1 + u.2 + (u.1 + u.2 + Pi.single i true) = (Pi.single i true : ι → Bool) := by
    funext j
    simp only [Pi.add_apply, ← add_assoc, BooleanRing.add_self, zero_add]
  rw [hcancel]
  exact dotProduct_single_one x i

private theorem eval_coalitionQuery_threeServerXor {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : Finset (Fin 3)) (hT : T.card ≤ 2) (i : ι) :
    ProbComp.eval ((threeServerXor ι).coalitionQuery T i) =
      PMF.uniformOfFintype (T → ι → Bool) := by
  rw [Scheme.eval_coalitionQuery, threeServerXor, ProbComp.eval_bind]
  simp only [ProbComp.eval_pure, ProbComp.eval_uniform, PMF.map_bind, PMF.pure_map]
  change (PMF.uniformOfFintype ((ι → Bool) × (ι → Bool))).map
    (fun u (s : T) => threeServerQuery u (Pi.single i true) s.1) = _
  let linHom : ((ι → Bool) × (ι → Bool)) →+ (T → ι → Bool) :=
    { toFun := fun u s => threeServerQuery u 0 s.1
      map_zero' := by
        ext ⟨s, _⟩ j
        fin_cases s <;> rfl
      map_add' := fun u v => by
        ext ⟨s, _⟩ j
        fin_cases s
        · rfl
        · rfl
        · simp only [threeServerQuery, Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply,
            add_zero, add_add_add_comm] }
  have hnotAll : ¬ (∀ s : Fin 3, s ∈ T) := by
    intro hall
    have huniv : T = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [huniv] at hT
    exact absurd hT (by decide)
  push Not at hnotAll
  obtain ⟨s_miss, hmiss⟩ := hnotAll
  have hsurj : Function.Surjective linHom := by
    intro σ
    let g : Fin 3 → ι → Bool := fun s => if hs : s ∈ T then σ ⟨s, hs⟩ else 0
    have hu : ∃ u : (ι → Bool) × (ι → Bool),
        ∀ s : Fin 3, s ≠ s_miss → threeServerQuery u 0 s = g s := by
      fin_cases s_miss
      · refine ⟨(g 1 + g 2, g 1), fun s hs => ?_⟩
        fin_cases s
        · exact (hs rfl).elim
        · rfl
        · ext j
          simp only [threeServerQuery, Pi.add_apply, Pi.zero_apply, add_zero,
            add_right_comm (g 1 j) (g 2 j) (g 1 j), BooleanRing.add_self, zero_add]
          rfl
      · refine ⟨(g 0, g 0 + g 2), fun s hs => ?_⟩
        fin_cases s
        · rfl
        · exact (hs rfl).elim
        · ext j
          simp only [threeServerQuery, Pi.add_apply, Pi.zero_apply, add_zero, ← add_assoc,
            BooleanRing.add_self, zero_add]
          rfl
      · refine ⟨(g 0, g 1), fun s hs => ?_⟩
        fin_cases s
        · rfl
        · rfl
        · exact (hs rfl).elim
    obtain ⟨u, hu⟩ := hu
    refine ⟨u, funext fun ⟨s, hs⟩ => ?_⟩
    exact (hu s fun h => hmiss (h ▸ hs)).trans (dite_eq_left hs)
  have hshift :
      (fun (u : (ι → Bool) × (ι → Bool)) (s : T) => threeServerQuery u (Pi.single i true) s.1) =
        (Equiv.addRight (fun (s : T) => threeServerQuery 0 (Pi.single i true) s.1)) ∘ linHom := by
    ext u ⟨s, _⟩ j
    fin_cases s <;> simp [linHom, threeServerQuery]
  rw [hshift, ← PMF.map_comp,
    Cslib.Probability.PMF.uniformOfFintype_map_addHom linHom hsurj,
    PMF.uniformOfFintype_map_equiv]

private theorem isTPrivate_threeServerXor (ι : Type) [Fintype ι] [DecidableEq ι] :
    (threeServerXor ι).IsTPrivate 2 := by
  rw [Scheme.isTPrivate_iff]
  intro T hT i i'
  rw [eval_coalitionQuery_threeServerXor T hT i, eval_coalitionQuery_threeServerXor T hT i']

/-! ### Corollaries 6, 7 and 8 -/

/-- Corollary 6: `N = 12 ≤ 3 * 4` blocks of `ℓ = 10` bits with `twoServer (Option (Fin 4))`
(`|Q| = 32`, `⌈log₂ |Q|⌉ = 5`) uses `2 * (3 * 5 + 10) = 50` bits (vs. `120` bits for `1` server). -/
example : HasScheme (Fin 12) 2 50 (Fin 10 → Bool) := by
  have h := hasBlockScheme_of_xorReconstruct (N := 12) (m := 3) (n := 4) (ℓ := 10)
    (isCorrect_twoServer (ι := Option (Fin 4)))
    (isPrivate_twoServer (ι := Option (Fin 4)))
    (Scheme.hasXorReconstruct_twoServer (Option (Fin 4)))
    (by decide)
  have hcard : Fintype.card (Option (Fin 4) → Bool) = 32 := by decide
  have hclog : Nat.clog 2 32 = 5 := by decide
  rw [Fintype.card_bool, hcard, hclog] at h
  exact h

/-- Genuine `t = 2` Corollary 6 (`hasTPrivateBlockScheme_of_xorReconstruct` on `threeServerXor`):
`N = 12 ≤ 3 * 4` blocks of `ℓ = 10` bits with `3` servers and `2`-collusion privacy uses
`3 * (3 * 5 + 10) = 75 < 120` bits (and downgrades cleanly to `HasScheme` via
`HasTPrivateScheme.hasScheme`). -/
example :
    HasTPrivateScheme (Fin 12) 2 3 75 (Fin 10 → Bool) ∧
      HasScheme (Fin 12) 3 75 (Fin 10 → Bool) := by
  have h2 : HasTPrivateScheme (Fin 12) 2 3 75 (Fin 10 → Bool) := by
    have h :=
      hasTPrivateBlockScheme_of_xorReconstruct (N := 12) (m := 3) (n := 4) (ℓ := 10) (t := 2)
        (isCorrect_threeServerXor (Option (Fin 4)))
        (isTPrivate_threeServerXor (Option (Fin 4)))
        (hasXorReconstruct_threeServerXor (Option (Fin 4)))
        (by decide)
    have hcardQ : Fintype.card (Option (Fin 4) → Bool) = 32 := by decide
    have hclog : Nat.clog 2 32 = 5 := by decide
    rw [Fintype.card_fin, hcardQ, hclog] at h
    exact h
  exact ⟨h2, h2.hasScheme (by decide)⟩

/-- Corollary 7: `n = 8 ≤ ℓ = 8` uses `4 * 8 = 32` bits with `2` servers (vs. `64` for `1`). -/
example : HasScheme (Fin 8) 2 32 (Fin 8 → Bool) :=
  hasBlockScheme_two_of_le (n := 8) (ℓ := 8) le_rfl

/-- Corollary 8 (`n ≤ (ℓ / 2) ^ 2`): `n = 16`, `ℓ = 8` uses `8 * 8 = 64` bits with `4` servers
(vs. `128` for `1` server). -/
example : HasScheme (Fin 16) 4 64 (Fin 8 → Bool) :=
  hasBlockScheme_four_of_le_half_sq (n := 16) (ℓ := 8) (by decide)

/-- Corollary 8 (`n ≤ m ^ 2`, `2 * m ≤ ℓ`): for odd `ℓ = 9`, `n = 16 ≤ 4 * 4` and `2 * 4 ≤ 9` gives
`8 * 9 = 72` bits with `4` servers (vs. `144` for `1` server). -/
example : HasScheme (Fin 16) 4 72 (Fin 9 → Bool) :=
  hasBlockScheme_four_of_le_sq (n := 16) (m := 4) (ℓ := 9) (by decide) (by decide)

end CslibFrontierTests.Crypto.PIRBlock
