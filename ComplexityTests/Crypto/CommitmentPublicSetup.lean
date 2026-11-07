/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Commitment.Basic
import Complexity.Crypto.Negligible.Basic

/-!
# Public setup for commitment schemes

Regressions for the concealed setup bit reported in issue #1716. The public encoding must
determine every honest operation. Exposing the setup bit in the XOR construction lets a
chosen-message adversary recover the challenge bit exactly.
-/

namespace ComplexityTests.Crypto.CommitmentPublicSetup

open Cslib Cslib.Probability Cslib.Crypto

/-- Two distinct Boolean setup keys cannot both be advertised by the empty string. -/
example (S : CommitmentScheme Bool) : ¬ (∀ k, S.encodeKey k = []) := by
  intro h
  have hkey : false = true := S.encodeKey.injective ((h false).trans (h true).symm)
  cases hkey

/-- Equal exposed public parameters determine all three honest operations. -/
example {Key : Type} (S : CommitmentScheme Key) {k₁ k₂ : Key}
    (h : S.encodeKey k₁ = S.encodeKey k₂) :
    S.ValidMessage k₁ = S.ValidMessage k₂ ∧
      S.commitDist k₁ = S.commitDist k₂ ∧ S.verify k₁ = S.verify k₂ := by
  cases S.encodeKey.injective h
  exact ⟨rfl, rfl, rfl⟩

/-- The XOR verifier from the reported example, with an empty opening. -/
def xorVerify (k : Bool) (m c o : List Bool) : Bool :=
  decide (m.length = 1 ∧ o = [] ∧ c = [m.headD false ^^ k])

/-- Erasing the setup bit prevents the XOR verifier from factoring through the public string. -/
example : ¬ ∃ V : List Bool → List Bool → List Bool → List Bool → Bool,
    ∀ k m c o, xorVerify k m c o = V [] m c o := by
  rintro ⟨V, h⟩
  have hfalse := h false [false] [false] []
  have htrue := h true [false] [false] []
  have hbad : true = false := hfalse.trans htrue.symm
  cases hbad

/-- The XOR construction with its setup bit actually public. -/
noncomputable def xorScheme : CommitmentScheme Bool where
  encodeKey := ⟨fun k => [k], by intro a b h; simpa using h⟩
  ValidMessage _ m := m.length = 1
  commitDist k m := PMF.pure ([m.headD false ^^ k], [])
  verify := xorVerify
  validMessage_of_verify _ _ _ _ h := (of_decide_eq_true h).1
  verify_of_mem_support _ _ co hm hco := by
    rw [PMF.support_pure, Set.mem_singleton_iff] at hco
    subst co
    simp [xorVerify, hm]

theorem xorScheme_encodeKey (k : Bool) : xorScheme.encodeKey k = [k] := rfl

/-- Retain the public bit, then XOR it with the commitment to recover the chosen message. -/
def xorAdversary : Encryption.WordAdversary where
  choose _ pk := pure (([false], [true]), pk)
  guess _ pk c := pure (c.headD false ^^ pk.headD false)

/-- Recovery is exact at each setup key, so it does not depend on the setup distribution. -/
theorem xor_hidingForKey (k bit : Bool) (n : ℕ) :
    xorScheme.hidingForKey k xorAdversary bit n = PMF.pure bit := by
  simp only [CommitmentScheme.hidingForKey, xorScheme_encodeKey, xorAdversary]
  cases k <;> cases bit <;> simp [xorScheme]

/-- Public setup rules out statistical hiding for the XOR construction under every setup law. -/
example (keyDist : ℕ → PMF Bool) : ¬ xorScheme.StatisticalHiding keyDist := by
  intro h
  have hgame (bit : Bool) (n : ℕ) :
      xorScheme.hidingGame keyDist xorAdversary bit n = PMF.pure bit := by
    simp [CommitmentScheme.hidingGame, xor_hidingForKey]
  exact not_negligible_const (c := 1) one_ne_zero (by
    simpa [hgame, Game.advantage, Game.succProbability] using h xorAdversary trivial)

end ComplexityTests.Crypto.CommitmentPublicSetup
