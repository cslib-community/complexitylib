/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.Encryption.Hybrid
import CslibFrontier.Crypto.Computational.Encryption.CCA
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT

/-!
# Tests for KEM–DEM hybrid public-key encryption

Exercises the KEM, DEM, and KEM–DEM hybrid encryption API in
`CslibFrontier.Crypto.Computational.Encryption.Hybrid`:
* native runtime certificates for `kemRealGame`, `kemIdealGame`, `demGame`, `hybridEncrypt`,
  `hybridDecrypt`, `otpEncrypt`, and `otpDecrypt`;
* non-vacuous rejection of two insecure KEMs by an explicit uniform distinguisher: `leakingEncaps`
  (`not_kemINDCPA_leaking`), whose leaked key is one bit too long and is caught by the length
  mismatch alone, and `sameLengthLeakingEncaps` (`not_kemINDCPA_sameLengthLeaking`), whose leaked
  key has the ideal key's length `n`, so the distinguisher has advantage exactly `1 - 2⁻ⁿ`
  (`advantage_kem_sameLengthLeaking`);
* exact decryption correctness of `hybridEncrypt` / `hybridDecrypt` instantiated with a concrete
  KEM and the one-time pad DEM (`otpEncrypt` / `otpDecrypt`);
* quantitative advantage bounds (`advantage_hybridGame_le`, `advantage_hybridGame_le_two_mul`) and
  an instantiation of the security predicate / reduction `KEMINDCPA.hybrid_otpEncrypt_indcpa` on an
  undecryptable security-game test fixture `idealEncaps` (`kemINDCPA_idealEncaps`,
  `indcpa_hybridEncrypt_idealEncaps_otpEncrypt`);
* the word one-time pad and its `WordINDCPA` corollary
  (`indcpa_hybridEncrypt_idealEncaps_otpWordEncrypt`), and a length-only scheme that satisfies
  `WordINDCPA` (`wordINDCPA_lengthOnly`) but not the unrestricted `INDCPAOf encBits`
  (`not_indcpaOf_lengthOnly`);
* doubled key-length security, native sampling, exact key lengths and decryption correctness,
  plus the zero-length boundary.
-/

@[expose] public section

namespace CslibFrontierTests.Crypto.HybridEncryption

open Cslib Cslib.Crypto Cslib.Crypto.Encryption Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- A simple key generator sampling a uniform `n`-bit key as both public and secret key. -/
noncomputable def toyKeyGen (n : ℕ) : ProbComp (List Bool × List Bool) := do
  let k ← BitString.sampleList n
  return (k, k)

/-- Deliberately insecure encapsulation that copies the public key as both encapsulated key and
ciphertext, and prefixes `true` so the encapsulated key is non-empty even at `n = 0`. This is the
length-boundary fixture: the leaked key has length `n + 1`, so it never equals an ideal `n`-bit
key. `sameLengthLeakingEncaps` below removes the length difference. -/
def leakingEncaps (_ : ℕ) (pk : List Bool) : ProbComp (List Bool × List Bool) :=
  pure (true :: pk, true :: pk)

/-- Deterministic decapsulation returning the encapsulation ciphertext directly. -/
def leakingDecaps (_ : ℕ) (_ ctKem : List Bool) : Option (List Bool) := some ctKem

theorem toyKeyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) toyKeyGen := by
  unfold toyKeyGen
  ppt

theorem leakingEncaps_ppt :
    IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => leakingEncaps p.1 p.2) := by
  unfold leakingEncaps
  ppt

theorem leakingDecaps_polyTime :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => leakingDecaps p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) (encOption encBits) := by
  unfold leakingDecaps
  fun_prop

/-- A uniform KEM distinguisher testing whether the encapsulated key equals the encapsulation
ciphertext `ctKem`. -/
def eqKemDistinguisher : Distinguisher := fun _ challenge =>
  let rest := dropFrame challenge
  let k := unframe rest
  let ctKem := dropFrame rest
  pure (decide (k = ctKem))

theorem eqKemDistinguisher_ppt : IsPPT encBool eqKemDistinguisher := by
  have hk : ComputableInPolyTime
      (fun challenge : List Bool => unframe (dropFrame challenge)) encBits encBits :=
    ComputableInPolyTime.unframe.comp ComputableInPolyTime.dropFrame
  have hct : ComputableInPolyTime
      (fun challenge : List Bool => dropFrame (dropFrame challenge)) encBits encBits :=
    ComputableInPolyTime.dropFrame.comp ComputableInPolyTime.dropFrame
  unfold eqKemDistinguisher
  exact (hk.decide_eq' hct).isPPTOn.preprocess (ComputableInPolyTime.snd encUnary encBits)

-- Native runtime checks for `kemRealGame`, `kemIdealGame`, `demGame`, `hybridEncrypt`,
-- and `hybridDecrypt`.

-- Canonical pair equality is exactly component equality; reuse the embedding's injectivity.
example (k₀ k₁ c₀ c₁ : List Bool) :
    encPair encBits encBits (k₀, c₀) = encPair encBits encBits (k₁, c₁) ↔
      k₀ = k₁ ∧ c₀ = c₁ := by
  simp only [(encPair encBits encBits).injective.eq_iff, Prod.mk.injEq]

-- Total frame projections alone admit noncanonical aliases, including a nonempty first component.
example : unframe [true, true] = unframe [true, true, false] ∧
    dropFrame [true, true] = dropFrame [true, true, false] ∧
    ([true, true] : List Bool) ≠ [true, true, false] := by decide

example : hybridDecrypt (fun _ _ _ => some []) (fun _ _ _ => some [])
    0 [] [true, true] = (none : Option (List Bool)) := rfl

example : hybridDecrypt (fun _ _ _ => some []) (fun _ _ _ => some [])
    0 [] [true, true, false] = some ([] : List Bool) := rfl

example : hybridDecrypt (fun _ _ _ => some []) (fun _ _ _ => some [])
    0 [] [] = (none : Option (List Bool)) := rfl

example : hybridDecrypt (fun _ _ _ => some []) (fun _ _ _ => some [])
    0 [] [true] = (none : Option (List Bool)) := rfl

-- The canonical empty pair is accepted, so an empty key/message is not a rejection.
example : hybridDecrypt (fun _ _ _ => some []) (fun _ _ _ => some [])
    0 [] [false] = some ([] : List Bool) := rfl

example : hybridDecrypt (fun _ _ _ => none) (fun _ _ _ => some [])
    0 [] [false] = (none : Option (List Bool)) := rfl

example : hybridDecrypt (fun _ _ _ => some []) (fun _ _ _ => none)
    0 [] [false] = (none : Option (List Bool)) := rfl

-- Actual CCA replies distinguish accepted empty plaintext from a malformed alias and the challenge.
example : cca2Phase2Oracle encBits
    (hybridDecrypt (fun _ _ _ => some []) (fun _ _ _ => some []))
    0 [] [false] ((), [true, true, false]) () = pure ([true], ()) := rfl

example : cca2Phase2Oracle encBits
    (hybridDecrypt (fun _ _ _ => some []) (fun _ _ _ => some []))
    0 [] [false] ((), []) () = pure ([], ()) := rfl

example : cca2Phase2Oracle encBits
    (hybridDecrypt (fun _ _ _ => some []) (fun _ _ _ => some []))
    0 [] [false] ((), [false]) () = pure ([], ()) := rfl

example : IsPPTOn encUnary encBool
    (kemRealGame toyKeyGen leakingEncaps eqKemDistinguisher) :=
  isPPTOn_kemRealGame toyKeyGen_ppt leakingEncaps_ppt
    eqKemDistinguisher_ppt (by fun_prop)

example : IsPPTOn encUnary encBool
    (kemIdealGame (fun n => n) toyKeyGen leakingEncaps eqKemDistinguisher) :=
  isPPTOn_kemIdealGame (by fun_prop) toyKeyGen_ppt leakingEncaps_ppt
    eqKemDistinguisher_ppt (by fun_prop)

example (adversary : Adversary) (hadversary : adversary.IsPPT) (bit : Bool) :
    IsPPTOn encUnary encBool (demGame otpEncrypt adversary bit) :=
  isPPTOn_demGame isPPTOn_otpEncrypt hadversary (by fun_prop) (by fun_prop)

example : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => hybridEncrypt leakingEncaps otpEncrypt p.1 p.2.1 p.2.2) :=
  isPPTOn_hybridEncrypt leakingEncaps_ppt isPPTOn_otpEncrypt

example : ComputableInPolyTime
    (fun p : ℕ × List Bool × List Bool =>
      hybridDecrypt leakingDecaps (fun n k ct => some (otpDecrypt n k ct)) p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encBits encBits)) (encOption encBool) :=
  computableInPolyTime_hybridDecrypt leakingDecaps_polyTime
    ((ComputableInPolyTime.optionSome encBool).comp computableInPolyTime_otpDecrypt)

/-- Every ciphertext produced by `hybridEncrypt leakingEncaps otpEncrypt` decrypts to the original
plaintext bit under `hybridDecrypt leakingDecaps (fun n k ct => some (otpDecrypt n k ct))`. -/
example (n : ℕ) (pk sk ct : List Bool) (bit : Bool)
    (hct : ct ∈ (ProbComp.eval (hybridEncrypt leakingEncaps otpEncrypt n pk bit)).support) :
    hybridDecrypt leakingDecaps (fun n k ct => some (otpDecrypt n k ct)) n sk ct = some bit := by
  refine hybridDecrypt_hybridEncrypt ?_ ?_ hct
  · intro k ctKem hsupp
    simp only [leakingEncaps, ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hsupp
    rcases hsupp with ⟨rfl, rfl⟩
    rfl
  · intro k ctDem _ hdemSupp
    simp only [otpEncrypt, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hdemSupp
    subst hdemSupp
    exact congrArg some (otpDecrypt_otpEncrypt n k bit)

/-- Concrete round-trip evaluation of `hybridDecrypt` on an encoded `(ctKem, ctDem)` pair. -/
example (bit : Bool) :
    hybridDecrypt leakingDecaps (fun n k ct => some (otpDecrypt n k ct)) 4 []
      (encPair encBits encBits ([true, false], [true ^^ bit])) = some bit := by
  rw [hybridDecrypt_encPair]
  simp [leakingDecaps, otpDecrypt]

/-- In `kemRealGame`, `eqKemDistinguisher` always outputs `true` on `leakingEncaps`. -/
theorem eval_kemRealGame_leaking (n : ℕ) :
    ProbComp.eval (kemRealGame toyKeyGen leakingEncaps eqKemDistinguisher n) =
      PMF.pure true := by
  simp only [kemRealGame, kemRealGameWith,
    toyKeyGen, leakingEncaps, eqKemDistinguisher, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind,
    ProbComp.eval_pure, BitString.eval_sampleList, PMF.pure_bind,
    decide_true, PMF.bind_const]

/-- In `kemIdealGame`, `eqKemDistinguisher` always outputs `false` on `leakingEncaps` because the
ideal key `kIdeal` has length `n` while `ctKem = true :: pk` has length `n + 1`. -/
theorem eval_kemIdealGame_leaking (n : ℕ) :
    ProbComp.eval (kemIdealGame (fun n => n) toyKeyGen leakingEncaps eqKemDistinguisher n) =
      PMF.pure false := by
  simp only [kemIdealGame, kemIdealGameWith, kemRealGameWith,
    toyKeyGen, leakingEncaps, eqKemDistinguisher, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind,
    ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind]
  trans (BitString.uniformList n).bind (fun _ => PMF.pure false)
  · refine PMF.bind_congr_on_support _ _ _ fun pk hpk => ?_
    trans (BitString.uniformList n).bind (fun _ => PMF.pure false)
    · refine PMF.bind_congr_on_support _ _ _ fun kIdeal hkIdeal => ?_
      have hlenPk := BitString.length_of_mem_support_uniformList hpk
      have hlenIdeal := BitString.length_of_mem_support_uniformList hkIdeal
      have hne : kIdeal ≠ true :: pk := by
        intro heq
        have := congrArg List.length heq
        simp [hlenPk, hlenIdeal] at this
      simp [hne]
    · exact PMF.bind_const _ _
  · exact PMF.bind_const _ _

/-- The leaking KEM is not IND-CPA secure: `eqKemDistinguisher` achieves advantage `1` at every
security parameter. -/
theorem not_kemINDCPA_leaking : ¬ KEMINDCPA (fun n => n) toyKeyGen leakingEncaps := by
  intro hsecure
  have hneg := hsecure eqKemDistinguisher eqKemDistinguisher_ppt
  simp only [eval_kemRealGame_leaking, eval_kemIdealGame_leaking] at hneg
  have hone : Game.advantage (PMF.pure true) (PMF.pure false) = 1 := by
    simp [Game.advantage, Game.succProbability]
  rw [hone] at hneg
  exact not_negligible_const one_ne_zero hneg

/-! ### A leaking KEM of the right length -/

/-- Deliberately insecure encapsulation that copies the public key as both encapsulated key and
ciphertext. Under `toyKeyGen` the leaked key is a uniform `n`-bit word, the same length as the
ideal key, so a length test cannot detect it. -/
def sameLengthLeakingEncaps (_ : ℕ) (pk : List Bool) : ProbComp (List Bool × List Bool) :=
  pure (pk, pk)

theorem sameLengthLeakingEncaps_ppt :
    IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => sameLengthLeakingEncaps p.1 p.2) := by
  unfold sameLengthLeakingEncaps
  ppt

/-- A uniform `n`-bit word equals a fixed `n`-bit word with probability `2⁻ⁿ`. -/
theorem uniformList_bind_decide_eq_apply_true {n : ℕ} {w : List Bool} (hw : w.length = n) :
    ((BitString.uniformList n).bind fun k => PMF.pure (decide (k = w))) true = (2 ^ n)⁻¹ := by
  rw [show (fun k => PMF.pure (decide (k = w))) = PMF.pure ∘ fun k => decide (k = w) from rfl,
    PMF.bind_pure_comp, BitString.uniformList_map_apply]
  subst hw
  have hcard : (Finset.univ.filter fun r : Fin w.length → Bool =>
      decide (List.ofFn r = w) = true).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨w.get, ?_⟩
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
      Finset.mem_singleton]
    constructor
    · intro h
      exact List.ofFn_injective (h.trans (List.ofFn_get w).symm)
    · rintro rfl
      exact List.ofFn_get w
  rw [hcard, Nat.cast_one, one_div]

/-- In `kemRealGame`, `eqKemDistinguisher` always outputs `true` on `sameLengthLeakingEncaps`. -/
theorem eval_kemRealGame_sameLengthLeaking (n : ℕ) :
    ProbComp.eval (kemRealGame toyKeyGen sameLengthLeakingEncaps
          eqKemDistinguisher n) =
      PMF.pure true := by
  simp only [kemRealGame, kemRealGameWith,
    toyKeyGen, sameLengthLeakingEncaps, eqKemDistinguisher, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind,
    ProbComp.eval_pure, BitString.eval_sampleList, PMF.pure_bind,
    decide_true, PMF.bind_const]

/-- In `kemIdealGame`, `eqKemDistinguisher` outputs `true` on `sameLengthLeakingEncaps` exactly
when the independent ideal key equals the public key, which has probability `2⁻ⁿ`. -/
theorem eval_kemIdealGame_sameLengthLeaking_true (n : ℕ) :
    ProbComp.eval (kemIdealGame (fun n => n) toyKeyGen sameLengthLeakingEncaps
          eqKemDistinguisher n) true =
      (2 ^ n)⁻¹ := by
  simp only [kemIdealGame, kemIdealGameWith, kemRealGameWith,
    toyKeyGen, sameLengthLeakingEncaps, eqKemDistinguisher, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind,
    ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_apply]
  calc
    _ = ∑' pk, BitString.uniformList n pk * (2 ^ n)⁻¹ := by
      refine tsum_congr fun pk => ?_
      by_cases hpk : pk ∈ (BitString.uniformList n).support
      · rw [uniformList_bind_decide_eq_apply_true
          (BitString.length_of_mem_support_uniformList hpk)]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hpk, zero_mul, zero_mul]
    _ = (2 ^ n)⁻¹ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- `eqKemDistinguisher` distinguishes `sameLengthLeakingEncaps` with advantage exactly
`1 - 2⁻ⁿ`: it accepts with probability `1` in the real game and `2⁻ⁿ` in the ideal game. -/
theorem advantage_kem_sameLengthLeaking (n : ℕ) :
    Game.advantage
        (ProbComp.eval (kemRealGame toyKeyGen sameLengthLeakingEncaps
          eqKemDistinguisher n))
        (ProbComp.eval (kemIdealGame (fun n => n) toyKeyGen sameLengthLeakingEncaps
          eqKemDistinguisher n)) =
      1 - (2 ^ n)⁻¹ := by
  have hle : ((2 : ℝ≥0) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
  rw [Game.advantage, Game.succProbability, Game.succProbability,
    eval_kemRealGame_sameLengthLeaking, eval_kemIdealGame_sameLengthLeaking_true,
    PMF.pure_apply_self, ENNReal.toNNReal_one, ENNReal.toNNReal_inv, ENNReal.toNNReal_pow,
    ENNReal.toNNReal_ofNat, NNReal.nndist_eq, tsub_eq_zero_of_le hle, max_eq_left zero_le]

/-- At `n = 1` the advantage is `1 / 2`. -/
example :
    Game.advantage
        (ProbComp.eval (kemRealGame toyKeyGen sameLengthLeakingEncaps
          eqKemDistinguisher 1))
        (ProbComp.eval (kemIdealGame (fun n => n) toyKeyGen sameLengthLeakingEncaps
          eqKemDistinguisher 1)) =
      1 / 2 := by
  rw [advantage_kem_sameLengthLeaking,
    tsub_eq_iff_eq_add_of_le (inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two))]
  norm_num

/-- At `n = 2` the advantage is `3 / 4`. -/
example :
    Game.advantage
        (ProbComp.eval (kemRealGame toyKeyGen sameLengthLeakingEncaps
          eqKemDistinguisher 2))
        (ProbComp.eval (kemIdealGame (fun n => n) toyKeyGen sameLengthLeakingEncaps
          eqKemDistinguisher 2)) =
      3 / 4 := by
  rw [advantage_kem_sameLengthLeaking,
    tsub_eq_iff_eq_add_of_le (inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two))]
  norm_num

/-- The same-length leaking KEM is not IND-CPA secure: the advantage `1 - 2⁻ⁿ` of
`eqKemDistinguisher` plus the negligible `2⁻ⁿ` is the constant `1`. -/
theorem not_kemINDCPA_sameLengthLeaking :
    ¬ KEMINDCPA (fun n => n) toyKeyGen sameLengthLeakingEncaps := by
  intro hsecure
  have hneg := hsecure eqKemDistinguisher eqKemDistinguisher_ppt
  simp only [advantage_kem_sameLengthLeaking] at hneg
  have hsum := hneg.add_fun (negligible_geometric (ratio := 2⁻¹) (by norm_num))
  refine not_negligible_const one_ne_zero (?_ : Negligible fun _ => (1 : ℝ≥0))
  convert hsum using 2 with n
  rw [inv_pow, tsub_add_cancel_of_le (inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two))]

/-- For `1 ≤ n`, specializing `advantage_hybridGame_le_two_mul` to `otpEncrypt` eliminates the
DEM advantage term via `advantage_demGame_otpEncrypt_eq_zero`. -/
example (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (adversary : Adversary) {n : ℕ} (hn : 1 ≤ n) :
    Game.advantage
      (ProbComp.eval (game keyGen (hybridEncrypt encaps otpEncrypt) adversary false n))
      (ProbComp.eval (game keyGen (hybridEncrypt encaps otpEncrypt) adversary true n)) ≤
      2 * Game.advantage
        (ProbComp.eval
          (kemRealGame keyGen encaps (hybridToKEMHiddenBitDistinguisher otpEncrypt adversary) n))
        (ProbComp.eval
          (kemIdealGame (fun n => n) keyGen encaps
            (hybridToKEMHiddenBitDistinguisher otpEncrypt adversary) n)) := by
  have h := advantage_hybridGame_le_two_mul (fun n => n) keyGen encaps otpEncrypt adversary n
  rwa [advantage_demGame_otpEncrypt_eq_zero hn, add_zero] at h

/-- For `1 ≤ n`, specializing `advantage_hybridGame_le` to `otpEncrypt` eliminates the DEM
advantage term via `advantage_demGame_otpEncrypt_eq_zero`. -/
example (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (adversary : Adversary) {n : ℕ} (hn : 1 ≤ n) :
    Game.advantage
      (ProbComp.eval (game keyGen (hybridEncrypt encaps otpEncrypt) adversary false n))
      (ProbComp.eval (game keyGen (hybridEncrypt encaps otpEncrypt) adversary true n)) ≤
      Game.advantage
        (ProbComp.eval
          (kemRealGame keyGen encaps (hybridToKEMDistinguisher otpEncrypt adversary false) n))
        (ProbComp.eval
          (kemIdealGame (fun n => n) keyGen encaps
            (hybridToKEMDistinguisher otpEncrypt adversary false) n)) +
      Game.advantage
        (ProbComp.eval
          (kemRealGame keyGen encaps (hybridToKEMDistinguisher otpEncrypt adversary true) n))
        (ProbComp.eval
          (kemIdealGame (fun n => n) keyGen encaps
            (hybridToKEMDistinguisher otpEncrypt adversary true) n)) := by
  have h := advantage_hybridGame_le (fun n => n) keyGen encaps otpEncrypt adversary n
  rwa [advantage_demGame_otpEncrypt_eq_zero hn, add_zero] at h

/-- Undecryptable security-game test fixture that draws a uniform `keyLen n`-bit key, discards any
recovery information, and emits `[]`, making `kemRealGame` and `kemIdealGame` distributionally
identical. No `decaps` can recover the encapsulated key on every supported output when
`1 ≤ keyLen n`; this
fixture exercises the `KEMINDCPA` security predicate and reduction only. -/
noncomputable def idealEncaps (keyLen : ℕ → ℕ) (n : ℕ) (_ : List Bool) :
    ProbComp (List Bool × List Bool) := do
  let k ← BitString.sampleList (keyLen n)
  return (k, [])

theorem idealEncaps_ppt {keyLen : ℕ → ℕ}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => idealEncaps keyLen p.1 p.2) := by
  have hk : IsPPTOn (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool => BitString.sampleList (keyLen p.1)) :=
    (hkeyLen.comp' (ComputableInPolyTime.fst _ _)).sampleList
  have hret : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => (p.2, ([] : List Bool)))
      (encPair (encPair encUnary encBits) encBits) (encPair encBits encBits) :=
    (ComputableInPolyTime.snd _ _).prod (ComputableInPolyTime.const [])
  unfold idealEncaps
  exact hk.bind_with hret.isPPTOn

theorem eval_kemRealGame_idealEncaps_eq_ideal (keyLen : ℕ → ℕ) (D : Distinguisher) (n : ℕ) :
    ProbComp.eval (kemRealGame toyKeyGen (idealEncaps keyLen) D n) =
      ProbComp.eval (kemIdealGame keyLen toyKeyGen (idealEncaps keyLen) D n) := by
  simp only [kemRealGame, kemRealGameWith,
    kemIdealGame, kemIdealGameWith, idealEncaps, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind, PMF.bind_const]

theorem kemINDCPA_idealEncaps (keyLen : ℕ → ℕ) :
    KEMINDCPA keyLen toyKeyGen (idealEncaps keyLen) := by
  intro D _
  simpa only [eval_kemRealGame_idealEncaps_eq_ideal, Game.advantage_self] using negligible_zero

/-- Instantiation of the security reduction `KEMINDCPA.hybrid_otpEncrypt_indcpa` on the
undecryptable security-game fixture `idealEncaps` and `otpEncrypt` (security predicate only). -/
theorem indcpa_hybridEncrypt_idealEncaps_otpEncrypt :
    INDCPA toyKeyGen (hybridEncrypt (idealEncaps (fun n => n)) otpEncrypt) :=
  (kemINDCPA_idealEncaps (fun n => n)).hybrid_otpEncrypt_indcpa
    toyKeyGen_ppt (idealEncaps_ppt (by fun_prop))

/-- Concrete 3-bit word one-time pad encryption and decryption round-trip on
`k = [true, false, true]` and `m = [true, true, false]`. -/
example :
    otpWordDecrypt 3 [true, false, true]
      (BitString.listXor 3 [[true, false, true], [true, true, false]]) =
      [true, true, false] := by decide

example :
    ProbComp.eval (otpWordEncrypt 3 [true, false, true] [true, true, false]) [false, true, true] =
      1 := by
  have h : [false, true, true] =
      BitString.listXor 3 [[true, false, true], [true, true, false]] := by decide
  rw [otpWordEncrypt, otpKeyWordEncrypt, ProbComp.eval_pure, h, PMF.pure_apply_self]

/-- Instantiation of the word-message security reduction `KEMINDCPA.hybrid_otpWordEncrypt_indcpa`
on `idealEncaps` and `otpWordEncrypt`. -/
theorem indcpa_hybridEncrypt_idealEncaps_otpWordEncrypt :
    WordINDCPA toyKeyGen (hybridEncrypt (idealEncaps (fun n => n)) otpWordEncrypt) :=
  (kemINDCPA_idealEncaps (fun n => n)).hybrid_otpWordEncrypt_indcpa
    toyKeyGen_ppt (idealEncaps_ppt (by fun_prop))

/-! ### Key length is independent of the security parameter -/

/-- The existing security-only fixture also works with twice the security parameter in key bits.
This checks the generalized composition, not decapsulation of the fixture's discarded key. -/
theorem indcpaOf_hybridEncrypt_doubleKey_otp :
    INDCPAOf encBits toyKeyGen
      (hybridEncrypt (idealEncaps (fun n => 2 * n)) (otpKeyWordEncrypt (fun n => 2 * n))) :=
  (kemINDCPA_idealEncaps (fun n => 2 * n)).hybrid_indcpa
    (demOneTimeKeyINDCPA_otpKeyWordEncrypt _) toyKeyGen_ppt
    (idealEncaps_ppt (by fun_prop)) (isPPTOn_otpKeyWordEncrypt (by fun_prop))

/-- The arbitrary-length ideal KEM experiment is natively strict PPT for `keyLen n = 2 * n`. -/
example : IsPPTOn encUnary encBool
    (kemIdealGame (fun n => 2 * n) toyKeyGen (idealEncaps (fun n => 2 * n))
      eqKemDistinguisher) :=
  isPPTOn_kemIdealGame (by fun_prop) toyKeyGen_ppt (idealEncaps_ppt (by fun_prop))
    eqKemDistinguisher_ppt (by fun_prop)

/-- Honest hybrid encryption remains native strict PPT at the doubled key length. -/
example : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
    (fun p => hybridEncrypt (idealEncaps (fun n => 2 * n)) (otpKeyWordEncrypt (fun n => 2 * n))
      p.1 p.2.1 p.2.2) :=
  isPPTOn_hybridEncrypt (idealEncaps_ppt (by fun_prop))
    (isPPTOn_otpKeyWordEncrypt (by fun_prop))

/-- Supported keys have exactly the chosen length, including the zero-length case. -/
example (keyLen : ℕ → ℕ) (n : ℕ) (pk k ct : List Bool)
    (h : (k, ct) ∈ (ProbComp.eval (idealEncaps keyLen n pk)).support) :
    k.length = keyLen n ∧ ct = [] := by
  simp only [idealEncaps, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨k', hk, heq⟩ := h
  cases heq
  exact ⟨BitString.length_of_mem_support_uniformList hk, rfl⟩

/-- The generic correctness theorem is independent of the key schedule. Here it recovers every
`2 * n`-bit message using the deliberately insecure, but correctly decryptable, leaking KEM. -/
example (n : ℕ) (pk sk ct m : List Bool) (hm : m.length = 2 * n)
    (hct : ct ∈ (ProbComp.eval
      (hybridEncrypt sameLengthLeakingEncaps (otpKeyWordEncrypt (fun n => 2 * n))
        n pk m)).support) :
    hybridDecrypt leakingDecaps
      (fun n k ct => some (otpKeyWordDecrypt (fun n => 2 * n) n k ct)) n sk ct = some m := by
  refine hybridDecrypt_hybridEncrypt ?_ ?_ hct
  · intro k ctKem hsupp
    simp only [sameLengthLeakingEncaps, ProbComp.eval_pure, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hsupp
    rcases hsupp with ⟨rfl, rfl⟩
    rfl
  · intro k ctDem _ hdemSupp
    simp only [otpKeyWordEncrypt, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hdemSupp
    subst ctDem
    exact congrArg some (otpKeyWordDecrypt_otpKeyWordEncrypt (fun n => 2 * n) n k hm)

/-- Zero key length is permitted by the security predicate; correctness of this zero-width pad
is restricted to the empty message. -/
example : KEMINDCPA (fun _ => 0) toyKeyGen (idealEncaps (fun _ => 0)) :=
  kemINDCPA_idealEncaps _

example (n : ℕ) (pk : List Bool) :
    ProbComp.eval (idealEncaps (fun _ => 0) n pk) = PMF.pure ([], []) := by
  simp [idealEncaps, BitString.sampleList]

example (n : ℕ) (k : List Bool) :
    otpKeyWordDecrypt (fun _ => 0) n k (BitString.listXor 0 [k, []]) = [] :=
  otpKeyWordDecrypt_otpKeyWordEncrypt (fun _ => 0) n k rfl

/-! ### The equal-length rule has force -/

/-- A toy length-only word encryption: the ciphertext of `m` is `List.replicate m.length false`,
so it reveals the length of `m` and nothing else. -/
def lengthOnlyEncrypt (_ : ℕ) (_ m : List Bool) : ProbComp (List Bool) :=
  pure (List.replicate m.length false)

/-- The length-only scheme satisfies `WordINDCPA`: an equal-length pair gives the same ciphertext
in both experiments, and an unequal-length pair is inadmissible. -/
theorem wordINDCPA_lengthOnly : WordINDCPA toyKeyGen lengthOnlyEncrypt := by
  intro adversary _ c
  refine tendsto_const_nhds.congr' ?_
  filter_upwards with n
  have heq :
      ProbComp.eval (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) toyKeyGen
        lengthOnlyEncrypt adversary false n) =
      ProbComp.eval (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) toyKeyGen
        lengthOnlyEncrypt adversary true n) := by
    simp only [gameOn, toyKeyGen, lengthOnlyEncrypt, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.pure_bind, apply_ite ProbComp.eval]
    congr 1 with keys : 1
    congr 1 with choice : 1
    by_cases hlen : choice.1.1.length = choice.1.2.length <;> simp [hlen]
  simp [heq]

/-- A word adversary that submits the pair `([], [false])` of unequal lengths and guesses whether
the ciphertext is `[false]`. -/
def lengthAdversary : WordAdversary where
  choose _ _ := pure (([], [false]), [])
  guess _ _ ct := pure (decide (ct = [false]))

/-- `lengthAdversary` is uniform strict PPT. -/
theorem lengthAdversary_isPPT : lengthAdversary.IsPPT where
  choose := (ComputableInPolyTime.const _).isPPTOn
  guess := by
    have hct : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.2)
        (encPair encUnary (encPair encBits encBits)) encBits := by fun_prop
    exact (ComputableInPolyTime.decide_eq' (encB := encBits) hct
      (ComputableInPolyTime.const [false])).isPPTOn

/-- Without the equal-length rule the length-only scheme is insecure: `lengthAdversary` wins the
unrestricted game with advantage `1`, so `lengthOnlyEncrypt` does not satisfy
`INDCPAOf encBits`. Together with `wordINDCPA_lengthOnly`, this shows that `WordINDCPA` is strictly
weaker than the unrestricted notion. -/
theorem not_indcpaOf_lengthOnly : ¬ INDCPAOf encBits toyKeyGen lengthOnlyEncrypt := by
  intro hsecure
  have hneg := hsecure lengthAdversary lengthAdversary_isPPT
  have hfalse (n : ℕ) :
      ProbComp.eval (game toyKeyGen lengthOnlyEncrypt lengthAdversary false n) =
        PMF.pure false := by
    simp only [gameOn, toyKeyGen, lengthOnlyEncrypt, lengthAdversary, ↓reduceIte,
      ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, PMF.pure_bind,
      PMF.bind_const]
    rfl
  have htrue (n : ℕ) :
      ProbComp.eval (game toyKeyGen lengthOnlyEncrypt lengthAdversary true n) =
        PMF.pure true := by
    simp only [gameOn, toyKeyGen, lengthOnlyEncrypt, lengthAdversary, ↓reduceIte,
      ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, PMF.pure_bind,
      PMF.bind_const]
    rfl
  simp only [hfalse, htrue] at hneg
  have hone : Game.advantage (PMF.pure false) (PMF.pure true) = 1 := by
    simp [Game.advantage, Game.succProbability]
  rw [hone] at hneg
  exact not_negligible_const one_ne_zero hneg

end CslibFrontierTests.Crypto.HybridEncryption
