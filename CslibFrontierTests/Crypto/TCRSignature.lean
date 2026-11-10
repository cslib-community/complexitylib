/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.TCRSignature

/-!
# Tests for `IndexedSignatureScheme.double` and `TCRSignature`

Provides concrete execution checks for `IndexedSignatureScheme.double`, `TCRSignature.otsMsg`,
`TCRSignature.otsMsg_inj`, and `TCRSignature.scheme`, proves that `TCRSignature.scheme S constHash`
is never `IndexedEUFCMA` for a constant hash family `constHash` via an explicit 1-query strict
oracle-PPT indexed forger winning with probability `1` at every security parameter `n` (confirming
that `H.TargetCollisionResistant` is essential even when `S` is `OneTimeEUFCMA`), and checks the
public security endpoints through `OneWayPermutation.exists_eufCMA`.
-/

namespace CslibFrontierTests.Crypto.TCRSignature

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### Concrete checks for `IndexedSignatureScheme.double` -/

/-- Toy deterministic capacity-`1` indexed scheme whose valid signatures at index `0` have length
`pk.length + msg.length`. -/
noncomputable def lengthIdxOne : IndexedSignatureScheme where
  capacity _ := 1
  keyGen n := pure (List.replicate n false, List.replicate n false)
  sign sk u msg := pure (if u == 0 then sk ++ msg else [])
  verify pk u msg sig := (u == 0) && (sig.length == pk.length + msg.length)
  capacity_polyTime := .const 1
  keyGen_ppt :=
    (((ComputableInPolyTime.bitsReplicate false).prod
      (ComputableInPolyTime.bitsReplicate false)).of_enc_eq fun _ => rfl).isPPTOn
  sign_ppt := by
    let encIn := encPair encBits (encPair encUnary encBits)
    have hsk := ComputableInPolyTime.fst encBits (encPair encUnary encBits)
    have hrest := ComputableInPolyTime.snd encBits (encPair encUnary encBits)
    have hu := hrest.fst'
    have hmsg := hrest.snd'
    have hcond := ComputableInPolyTime.unary_beq' hu (.const 0)
    have happ := ComputableInPolyTime.bitsAppend hsk hmsg
    exact ((hcond.ite happ (.const (encIn := encIn) (encOut := encBits) [])).of_enc_eq
      fun _ => rfl).isPPTOn
  verify_polyTime := by
    let encRest := encPair encUnary (encPair encBits encBits)
    have hpkLen :=
      (ComputableInPolyTime.fst encBits encRest).trans ComputableInPolyTime.length_bits
    have hrest := ComputableInPolyTime.snd encBits encRest
    have hu := hrest.fst'
    have hmsgLen := hrest.snd'.fst'.trans ComputableInPolyTime.length_bits
    have hsigLen := hrest.snd'.snd'.trans ComputableInPolyTime.length_bits
    exact ((ComputableInPolyTime.unary_beq' hu (.const 0)).bool_and'
      (hsigLen.unary_beq' (hpkLen.unary_add' hmsgLen))).of_enc_eq fun _ => rfl
  verify_sign n keys hkeys u hu msg sig hsig := by
    have hu0 : u = 0 := by omega
    subst hu0
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hkeys
    subst hkeys
    simp only [beq_self_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hsig
    subst hsig
    simp

/-- Capacity-`2` doubled scheme built from `lengthIdxOne`. -/
noncomputable abbrev lengthIdxTwo : IndexedSignatureScheme :=
  lengthIdxOne.double (fun _ => le_rfl)

example (n : ℕ) : lengthIdxTwo.capacity n = 2 := rfl

/-- Bundled public key pairing a 1-bit slot-`0` key with a 2-bit slot-`1` key. -/
def sampleDoublePk : List Bool :=
  encPair encBits encBits ([false], [false, false])

-- Slot 0 accepts length `1 + 1 = 2` and rejects slot 1's length `2 + 1 = 3`:
example : lengthIdxTwo.verify sampleDoublePk 0 [true] [false, true] = true := by
  decide +kernel

example : lengthIdxTwo.verify sampleDoublePk 0 [true] [false, false, true] = false := by
  decide +kernel

-- Slot 1 accepts length `2 + 1 = 3` and rejects slot 0's length `1 + 1 = 2`:
example : lengthIdxTwo.verify sampleDoublePk 1 [true] [false, false, true] = true := by
  decide +kernel

example : lengthIdxTwo.verify sampleDoublePk 1 [true] [false, true] = false := by
  decide +kernel

-- Every index `u ≥ 2` is rejected:
example : lengthIdxTwo.verify sampleDoublePk 2 [true] [false, true] = false := by
  decide +kernel

/-! ### Concrete checks for `TCRSignature` -/

/-- Constant `KeyedHashFamily` with `keyLen n = n` and `digestLen n = n + 1` mapping every input to
`0^{n+1}`. -/
def constHash : KeyedHashFamily where
  keyLen n := n
  digestLen n := n + 1
  eval n _ _ := List.replicate (n + 1) false
  keyLen_polyTime := .id'
  digestLen_polyTime := ComputableInPolyTime.id'.unary_add' (.const 1)
  le_digestLen _ := Nat.le_succ _
  polyTime :=
    (((ComputableInPolyTime.fst encUnary (encPair encBits encBits)).unary_add' (.const 1)).trans
      (ComputableInPolyTime.bitsReplicate false)).of_enc_eq fun _ => rfl
  length_eq _ _ _ _ := List.length_replicate

@[simp] theorem constHash_keyLen (n : ℕ) : constHash.keyLen n = n := rfl

@[simp] theorem constHash_eval (n : ℕ) (k msg : List Bool) :
    constHash.eval n k msg = List.replicate (n + 1) false := rfl

/-- Toy deterministic one-time signature scheme checking `pk.length == msg.length` and
`sig.length == msg.length`. -/
noncomputable def lengthOneTime : SignatureScheme where
  keyGen n := pure (List.replicate n false, List.replicate n false)
  sign _ msg := pure msg
  verify pk msg sig := (pk.length == msg.length) && (sig.length == msg.length)
  keyGen_ppt :=
    (((ComputableInPolyTime.bitsReplicate false).prod
      (ComputableInPolyTime.bitsReplicate false)).of_enc_eq fun _ => rfl).isPPTOn
  sign_ppt := (ComputableInPolyTime.snd encBits encBits).isPPTOn
  verify_polyTime := by
    let encRest := encPair encBits encBits
    have hpkLen :=
      (ComputableInPolyTime.fst encBits encRest).trans ComputableInPolyTime.length_bits
    have hrest := ComputableInPolyTime.snd encBits encRest
    have hmsgLen := hrest.fst'.trans ComputableInPolyTime.length_bits
    have hsigLen := hrest.snd'.trans ComputableInPolyTime.length_bits
    exact ((hpkLen.unary_beq' hmsgLen).bool_and'
      (hsigLen.unary_beq' hmsgLen)).of_enc_eq fun _ => rfl
  verify_sign n keys hkeys msg hmsg sig hsig := by
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hkeys hsig
    subst hkeys
    subst hsig
    simp [hmsg]

example :
    ([true, false] : List Bool) = [true, false] ∧
      ([false, true, true] : List Bool) = [false, true, true] :=
  TCRSignature.otsMsg_inj constHash (n := 2)
    (k₁ := [true, false]) (k₂ := [true, false])
    (d₁ := [false, true, true]) (d₂ := [false, true, true])
    rfl rfl rfl rfl rfl

/-- Sample public key at `n = 2` for `TCRSignature.scheme lengthOneTime constHash`. -/
def sampleTcrPk : List Bool :=
  encPair encUnary encBits (2, List.replicate (TCRSignature.otsParam constHash 2) false)

/-- Sample signature at `n = 2` with hash key `[true, false]` under `lengthOneTime` and
`constHash`. -/
def sampleTcrSig : List Bool :=
  let m := TCRSignature.otsMsg constHash 2 [true, false] [false, false, false]
  encPair encBits encBits ([true, false], m)

-- Messages `[]`, `[true]`, and `[true, false, true, true, false]` verify at `u = 0`:
example :
    (TCRSignature.scheme lengthOneTime constHash).verify sampleTcrPk 0 [] sampleTcrSig = true := by
  decide +kernel

example :
    (TCRSignature.scheme lengthOneTime constHash).verify sampleTcrPk 0 [true] sampleTcrSig =
      true := by
  decide +kernel

example :
    (TCRSignature.scheme lengthOneTime constHash).verify sampleTcrPk 0
      [true, false, true, true, false] sampleTcrSig = true := by
  decide +kernel

-- Rejected at index `u = 1`:
example :
    (TCRSignature.scheme lengthOneTime constHash).verify sampleTcrPk 1 [true] sampleTcrSig =
      false := by
  decide +kernel

-- Rejected when the hash key length differs from `constHash.keyLen 2 = 2`:
example :
    (TCRSignature.scheme lengthOneTime constHash).verify sampleTcrPk 0 [true]
      (encPair encBits encBits
        ([true], TCRSignature.otsMsg constHash 2 [true, false] [false, false, false])) = false := by
  decide +kernel

-- Rejected when the inner one-time signature is empty:
example :
    (TCRSignature.scheme lengthOneTime constHash).verify sampleTcrPk 0 [true]
      (encPair encBits encBits ([true, false], [])) = false := by
  decide +kernel

/-! ### Necessity of `H.TargetCollisionResistant` -/

/-- Explicit 1-query indexed forger against `TCRSignature.scheme S constHash`: asks the signing
oracle to sign `[false]` at index `0` (truncating the reply to `replyBound n`) and reuses that
signature to forge `(0, [true], sig)`. -/
def constHashForger (replyBound : ℕ → ℕ) : IndexedForger :=
  fun n _ => do
    let sig ← List.take (replyBound n) <$>
      ProbOracleComp.query ((), encPair encUnary encBits (0, [false]))
    return (0, [true], sig)

theorem isOraclePPT_constHashForger {replyBound : ℕ → ℕ}
    (hbound : ComputableInPolyTime replyBound encUnary encUnary) :
    IsOraclePPT (encPair encUnary (encPair encBits encBits)) (constHashForger replyBound) := by
  apply IsOraclePPTOn.isOraclePPT
  let In := ℕ × List Bool
  let encIn : In ↪ List Bool := encPair encUnary encBits
  have hn : ComputableInPolyTime (fun p : In => p.1) encIn encUnary :=
    ComputableInPolyTime.fst _ _
  have hquery : IsOraclePPTOn (Operation := Unit) encIn encBits
      (fun p : In => List.take (replyBound p.1) <$>
        ProbOracleComp.query ((), encPair encUnary encBits (0, [false]))) :=
    IsOraclePPTOn.query_take' () (.const (encPair encUnary encBits (0, [false]))) (hn.trans hbound)
  have hpost : ComputableInPolyTime (fun q : In × List Bool => (0, [true], q.2))
      (encPair encIn encBits) (encPair encUnary (encPair encBits encBits)) :=
    ((ComputableInPolyTime.const 0).prod
      ((ComputableInPolyTime.const [true]).prod
        (ComputableInPolyTime.snd encIn encBits))).of_enc_eq fun _ => rfl
  exact (hquery.bind_with (second := fun _ sig => pure (0, [true], sig))
    (hpost.isOraclePPTOn (Operation := Unit))).congr fun _ _ _ _ => rfl

/-- Target collision resistance of `H` is essential in
`SignatureScheme.OneTimeEUFCMA.indexedEUFCMA_tcrSignature`: for **every** signature scheme `S`
(even a `OneTimeEUFCMA` one), instantiating `TCRSignature.scheme S constHash` with the constant hash
family allows `constHashForger` to win `indexedEufCmaGame` with probability `1` at every `n`. -/
theorem not_indexedEUFCMA_tcrSignature_constHash (S : SignatureScheme) :
    ¬ (TCRSignature.scheme S constHash).IndexedEUFCMA := by
  intro hsec
  obtain ⟨ckg, dkg, hkgLen⟩ := S.keyGen_ppt.length_le
  obtain ⟨csg, dsg, hsgLen⟩ := S.sign_ppt.length_le
  let sigBound (n : ℕ) : ℕ :=
    let M := TCRSignature.otsParam constHash n
    csg * (2 * (ckg * (M + 1) ^ dkg) + M + 2) ^ dsg
  let replyBound (n : ℕ) : ℕ := 2 * n + 1 + sigBound n
  have hsigBoundPoly : ComputableInPolyTime sigBound encUnary encUnary := by
    have hM := TCRSignature.computableInPolyTime_otsParam constHash
    have hkgPow := (ComputableInPolyTime.unary_pow dkg).comp (hM.unary_add' (.const 1))
    have hkgTerm := (ComputableInPolyTime.const 2).unary_mul'
      ((ComputableInPolyTime.const ckg).unary_mul' hkgPow)
    have hinner := (hkgTerm.unary_add' hM).unary_add' (.const 2)
    exact (ComputableInPolyTime.const csg).unary_mul'
      ((ComputableInPolyTime.unary_pow dsg).comp hinner)
  have hreplyBoundPoly : ComputableInPolyTime replyBound encUnary encUnary :=
    (((ComputableInPolyTime.const 2).unary_mul' .id').unary_add' (.const 1)).unary_add'
      hsigBoundPoly
  have hforger := isOraclePPT_constHashForger hreplyBoundPoly
  have hneg := hsec.negligible (constHashForger replyBound) hforger
  have hone : ∀ n,
      Game.succProbability
        (ProbComp.eval
          ((TCRSignature.scheme S constHash).indexedEufCmaGame (constHashForger replyBound) n)) =
        1 := by
    intro n
    have heval :
        ProbComp.eval
          ((TCRSignature.scheme S constHash).indexedEufCmaGame (constHashForger replyBound) n) =
          PMF.pure true := by
      simp only [IndexedSignatureScheme.indexedEufCmaGame, TCRSignature.scheme_keyGen,
        TCRSignature.scheme_verify, TCRSignature.keyGen, constHashForger, bind_map_left,
        ProbComp.eval_bind, ProbComp.eval_pure, OracleComp.interpret_bind,
        OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure,
        ProbOracleComp.interpret_query, PMF.bind_bind, PMF.pure_bind]
      have horacle : ∀ otsk : List Bool,
          ProbComp.eval
            (((TCRSignature.scheme S constHash).indexedSigningOracle n
              (encPair encUnary encBits (n, otsk))
              ((), encPair encUnary encBits (0, [false]))).run []) =
          (BitString.uniformList n).bind fun k =>
            (ProbComp.eval
              (S.sign otsk
                (TCRSignature.otsMsg constHash n k (List.replicate (n + 1) false)))).bind
              fun ots => PMF.pure (encPair encBits encBits (k, ots), [(0, [false])]) := by
        intro otsk
        simp only [StateT.run, IndexedSignatureScheme.indexedSigningOracle,
          IndexedSignatureScheme.requestDecoder.decode_enc, TCRSignature.scheme_capacity,
          TCRSignature.scheme_sign, Nat.zero_lt_one, List.map_nil, List.not_mem_nil,
          not_false_eq_true, and_self, ↓reduceIte, TCRSignature.sign,
          TCRSignature.keyDecoder.decode_enc, ProbComp.eval_bind, ProbComp.eval_pure,
          BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind, constHash_keyLen,
          constHash_eval]
      calc
        _ = (ProbComp.eval (S.keyGen (TCRSignature.otsParam constHash n))).bind
              (fun _ => PMF.pure true) := by
              refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
              rw [horacle keys.2]
              simp only [PMF.bind_bind, PMF.pure_bind]
              calc
                _ = (BitString.uniformList n).bind (fun _ => PMF.pure true) := by
                      refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
                      have hkLen : k.length = n := BitString.length_of_mem_support_uniformList hk
                      calc
                        _ = (ProbComp.eval
                              (S.sign keys.2
                                (TCRSignature.otsMsg constHash n k
                                  (List.replicate (n + 1) false)))).bind
                              (fun _ => PMF.pure true) := by
                              refine PMF.bind_congr_on_support _ _ _ fun ots hots => ?_
                              have hkPair := hkgLen (TCRSignature.otsParam constHash n) keys hkeys
                              simp only [length_encPair, encBits_apply, encUnary_apply,
                                List.length_replicate] at hkPair
                              have hskLen :
                                  keys.2.length ≤
                                    ckg * (TCRSignature.otsParam constHash n + 1) ^ dkg := by
                                omega
                              have hmsgLen :
                                  (TCRSignature.otsMsg constHash n k
                                    (List.replicate (n + 1) false)).length =
                                    TCRSignature.otsParam constHash n :=
                                TCRSignature.length_otsMsg constHash n k _
                              have hsPair :=
                                hsgLen
                                  (keys.2,
                                    TCRSignature.otsMsg constHash n k
                                      (List.replicate (n + 1) false)) ots hots
                              simp only [length_encPair, encBits_apply, hmsgLen] at hsPair
                              have hbaseLe :
                                  2 * keys.2.length + 1 + TCRSignature.otsParam constHash n + 1 ≤
                                    2 * (ckg * (TCRSignature.otsParam constHash n + 1) ^ dkg) +
                                      TCRSignature.otsParam constHash n + 2 := by
                                omega
                              have hotsLen : ots.length ≤ sigBound n :=
                                hsPair.trans
                                  (Nat.mul_le_mul_left csg (Nat.pow_le_pow_left hbaseLe dsg))
                              have hsigLen :
                                  (encPair encBits encBits (k, ots)).length ≤ replyBound n := by
                                simp only [length_encPair, encBits_apply, hkLen, replyBound]
                                omega
                              have htake :
                                  (encPair encBits encBits (k, ots)).take (replyBound n) =
                                    encPair encBits encBits (k, ots) :=
                                List.take_of_length_le hsigLen
                              have hv :
                                  S.verify keys.1
                                    (TCRSignature.otsMsg constHash n k
                                      (List.replicate (n + 1) false)) ots = true :=
                                S.verify_sign (TCRSignature.otsParam constHash n) keys hkeys _
                                  hmsgLen ots hots
                              have hnotContains :
                                  ([(0, [false])] : List (ℕ × List Bool)).contains (0, [true]) =
                                    false := by
                                decide
                              simp only [htake, hnotContains, Bool.not_false, TCRSignature.verify,
                                TCRSignature.keyDecoder.decode_enc,
                                TCRSignature.sigDecoder.decode_enc, beq_self_eq_true,
                                constHash_keyLen, constHash_eval, hkLen, hv, Bool.and_self]
                        _ = PMF.pure true := PMF.bind_const _ _
                _ = PMF.pure true := PMF.bind_const _ _
        _ = PMF.pure true := PMF.bind_const _ _
    simp [Game.succProbability, heval]
  exact not_negligible_const (one_ne_zero : (1 : ℝ≥0) ≠ 0) (by simpa only [hone] using hneg)

/-! ### Public security endpoints -/

example {S : IndexedSignatureScheme} (hcap : ∀ n, 1 ≤ S.capacity n) (hS : S.IndexedEUFCMA) :
    (S.double hcap).IndexedEUFCMA :=
  hS.double hcap

example {S : SignatureScheme} (hS : S.OneTimeEUFCMA)
    {H : KeyedHashFamily} (hH : H.TargetCollisionResistant) :
    (TCRSignature.scheme S H).IndexedEUFCMA :=
  hS.indexedEUFCMA_tcrSignature hH

example {f : List Bool → List Bool} (hf : OneWay f)
    {H : KeyedHashFamily} (hH : H.TargetCollisionResistant) :
    ∃ S : IndexedSignatureScheme, (∀ n, S.capacity n = 2) ∧ S.IndexedEUFCMA :=
  hf.exists_indexedEUFCMA_of_targetCollisionResistant hH

example {f : List Bool → List Bool} (hf : OneWay f)
    {H : KeyedHashFamily} (hH : H.TargetCollisionResistant) :
    ∃ M : SignatureScheme, M.EUFCMA :=
  hf.exists_eufCMA_of_targetCollisionResistant hH

example {f : List Bool → List Bool} (hf : OneWayPermutation f) :
    ∃ M : SignatureScheme, M.EUFCMA :=
  hf.exists_eufCMA

end CslibFrontierTests.Crypto.TCRSignature
