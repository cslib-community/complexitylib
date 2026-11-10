/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Tactic.PPT
import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC

/-! `ppt` on oracle goals, and the goal preparation shared by `ppt` and `polytime`: unfolding
hints, local encoding `let`s and certificates stored in structure fields. -/

namespace CslibFrontierTests.OraclePPTTactic

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM

/-- On a nonzero unary input `n`, ask the empty request and keep `n` reply bits. -/
private noncomputable def askUnlessZero (n : ℕ) : WordOracleComp Unit (List Bool) :=
  if n = 0 then pure [] else List.take n <$> ProbOracleComp.query ((), [])

-- An oracle goal: the hint unfolds the program, then the bounded-prefix query and the
-- conditional compose.
example : IsOraclePPTOn encUnary encBits askUnlessZero := by
  fail_if_success ppt
  ppt [askUnlessZero]

-- A reply prefix exponential in the input is not oracle PPT (`CslibFrontierTests.OracleComposition`
-- proves the negation), and oracle mode does not certify it.
example : True := by
  fail_if_success have : IsOraclePPTOn encUnary encBits (fun n => List.take (2 ^ n) <$>
      ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), [])) := by ppt
  trivial

/-- Ask about a sampled word, keeping as many reply bits as the input has. -/
private noncomputable def askAboutSample (word : List Bool) : WordOracleComp Bool (List Bool) := do
  let sample ← ProbOracleComp.sample (BitString.sampleList word.length)
  List.take word.length <$> ProbOracleComp.query (true, sample ++ word)

-- A sampled closed program feeds a later query that also captures the input.
example : IsOraclePPTOn encBits encBits askAboutSample := by
  ppt [askAboutSample]

-- Parameterized oracle goals unfold to the encoded unary-parameter/word input.
example : IsOraclePPT encBits (fun n word =>
    List.take n <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
      ((), word)) := by
  ppt

-- Local encoding `let`s are unfolded in the goal and in the hypotheses that mention them.
example {f : ℕ × List Bool → List Bool}
    (hf : let E := encPair encUnary encBits; ComputableInPolyTime f E encBits) :
    let E := encPair encUnary encBits
    IsOraclePPTOn E encBits (fun input => List.take input.1 <$>
      ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), f input)) := by
  intro E
  ppt

/-- The certificates of a real handler: the encrypt-then-MAC reduction to MAC security encrypts
an accepted request with the scheme's `encrypt` and asks the external signing oracle for a tag.
The encryption certificate is the field `E.encrypt_ppt` of the scheme. -/
example (E : SymmetricCipher) {tagBound : ℕ → ℕ}
    (htagBound : ComputableInPolyTime tagBound encUnary encUnary) :
    IsOraclePPTOn
      (encPair (encPair (encPair encUnary encBits) encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun pair : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        etmToMACHandler E pair.1.1.1 (tagBound pair.1.1.1) pair.1.2 pair.2.1
          pair.2.2) := by
  ppt [etmToMACHandler]

/-- A scheme whose sampler certificate is a structure field. -/
private structure Sampler where
  /-- Sample a word from an input word. -/
  run : List Bool → ProbComp (List Bool)
  /-- The sampler is strict PPT. -/
  run_ppt : IsPPTOn encBits encBits run

-- `fun_prop` does not look inside `S`; `ppt` adds `S.run_ppt` as a local fact.
example (S : Sampler) :
    IsOraclePPTOn (Operation := Unit) encBits encBits
      (fun word => ProbOracleComp.sample (S.run word)) := by
  fail_if_success fun_prop
  ppt

-- `polytime` takes the same hints and exposes deterministic fields.
example (E : SymmetricCipher) :
    ComputableInPolyTime (fun input : ℕ × List Bool × List Bool =>
      (E.decrypt input.1 input.2.1 input.2.2).isSome)
      (encPair encUnary (encPair encBits encBits)) encBool := by
  polytime

/-- Whether a word has even length. -/
private def evenLength (word : List Bool) : Bool := word.length % 2 == 0

example : ComputableInPolyTime evenLength encBits encBool := by
  polytime [evenLength]

-- A hint that does not occur in the goal is reported.
example : ComputableInPolyTime (fun word : List Bool => word.length) encBits encUnary := by
  fail_if_success polytime [evenLength]
  polytime

end CslibFrontierTests.OraclePPTTactic
