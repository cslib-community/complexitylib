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

/-- A structure bundling a parameterized oracle-PPT routine, exercising post-`prepareGoal`
unfolding of `IsOraclePPT` fields. -/
private structure OracleSubroutine where
  /-- Parameterized oracle routine returning a bit. -/
  run : ℕ → List Bool → WordOracleComp Unit Bool
  /-- Uniform strict oracle-PPT certificate for `run`. -/
  run_ppt : IsOraclePPT encBool run

-- Structure-field `IsOraclePPT` certificates are exposed by `prepareGoal` and unfolded so
-- `oraclePptKnownCall` prepares tuple arguments across monadic sequencing and mapped queries.
example (A : OracleSubroutine) (S : Sampler) :
    IsOraclePPT encBool (fun n word => do
      let b ← A.run (n + 1) word.reverse
      if b then
        let masked ← ProbOracleComp.sample (S.run (b :: word))
        (fun reply => reply == masked) <$>
          (List.take n <$>
            ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
              ((), masked ++ word))
      else
        (fun reply => !reply.isEmpty) <$>
          (List.take 1 <$>
            ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), word))) := by
  fail_if_success fun_prop
  ppt

-- Local `IsOraclePPT` certificates over an abstract operation type expose `Finite Op` from the
-- certificate itself and prepare curried arguments.
example {Op : Type} [DecidableEq Op]
    (routine : ℕ → List Bool → WordOracleComp Op Bool)
    (hroutine : IsOraclePPT encBool routine) :
    IsOraclePPT encBool (fun n word => do
      let flag ← routine (n + word.length) (word ++ word)
      if word.length < n then
        routine n (flag :: word)
      else
        pure (!flag)) := by
  ppt

-- Multi-component tuple arguments and competing local intermediate encodings resolve jointly
-- across oracle binds.
example (shared firstOnly secondOnly : ℕ ↪ List Bool)
    (first : (List Bool × ℕ) × List Bool → WordOracleComp Unit ℕ)
    (second : List Bool → ℕ → WordOracleComp Unit Bool)
    (hfShared : IsOraclePPTOn (encPair (encPair encBits encUnary) encBits) shared first)
    (_hfOther : IsOraclePPTOn (encPair (encPair encBits encUnary) encBits) firstOnly first)
    (hsShared : IsOraclePPTOn (encPair encBits shared) encBool (fun p => second p.1 p.2))
    (_hsOther : IsOraclePPTOn (encPair encBits secondOnly) encBool (fun p => second p.1 p.2)) :
    IsOraclePPTOn encBits encBool (fun word => do
      let k ← first ((word.reverse, word.length), word ++ word)
      second word k) := by
  ppt

-- Boolean conditional guards on oracle goals use full `PolyTime` (here a list fold) while keeping
-- `List.take` reply prefixes intact inside branches, and combine with curried closed `IsPPTOn`
-- sampling.
example (test : ℕ → List Bool → ProbComp Bool)
    (htest : IsPPTOn (encPair encUnary encBits) encBool (fun p => test p.1 p.2)) :
    IsOraclePPT encBool (fun n word =>
      if word.foldl (fun parity _ => !parity) true then do
        let reply ← List.take n <$>
          ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), word)
        ProbOracleComp.sample (test n (reply ++ word))
      else
        pure false) := by
  fail_if_success (clear htest; ppt)
  ppt

/-- A reducible wrapper around `OracleComp.iterate` keeps oracle loop dispatch active. -/
private abbrev wrappedOracleIterate {Op State : Type}
    (count : ℕ) (step : State → WordOracleComp Op State) (initial : State) :
    WordOracleComp Op State :=
  OracleComp.iterate count step initial

-- Bounded-growth oracle iteration supports nonincreasing state, constant additive growth, and
-- captured input-dependent polynomial growth.
example (step : List Bool → WordOracleComp Unit (List Bool))
    (hstep : IsOraclePPTOn encBits encBits step)
    (hshrink : ∀ state, ∀ next ∈ OracleComp.support (step state),
      next.length ≤ state.length)
    (growth : ℕ)
    (hgrowth : ∀ state, ∀ next ∈ OracleComp.support (step state),
      next.length ≤ state.length + growth)
    (step2 : List Bool → List Bool → WordOracleComp Unit (List Bool))
    (hstep2 : IsOraclePPTOn (encPair encBits encBits) encBits (fun pair => step2 pair.1 pair.2))
    (growth2 : List Bool → ℕ) (hpoly2 : PolyBounded List.length growth2)
    (hgrowth2 : ∀ word state, ∀ next ∈ OracleComp.support (step2 word state),
      next.length ≤ state.length + growth2 word) :
    IsOraclePPTOn encBits encBits (fun word => OracleComp.iterate word.length step word) ∧
    IsOraclePPTOn encBits encBits (fun word => wrappedOracleIterate word.length step word) ∧
    IsOraclePPTOn encBits encBits
      (fun word => wrappedOracleIterate word.length (step2 word) word) := by
  refine ⟨?_, ?_, ?_⟩
  · clear growth hgrowth step2 hstep2 growth2 hpoly2 hgrowth2
    fail_if_success (clear hstep; ppt)
    fail_if_success (clear hshrink; ppt)
    ppt
  · clear hshrink step2 hstep2 growth2 hpoly2 hgrowth2
    fail_if_success (clear hgrowth; ppt)
    ppt
  · clear step hstep hshrink growth hgrowth
    fail_if_success (clear hstep2; ppt)
    fail_if_success (clear hpoly2; ppt)
    fail_if_success (clear hgrowth2; ppt)
    ppt

/-- A raw-only Boolean guard with no plain `ComputableInPolyTime` certificate. -/
@[irreducible] private def rawOnlyGuard (word : List Bool) : Bool := word.isEmpty

@[fun_prop] private theorem rawOnlyGuard_tidy :
    ComputableTidilyInPolyTime rawOnlyGuard encBits encBool := by
  unfold rawOnlyGuard
  fun_prop

-- Uncharged raw `ProbOracleComp.query` calls without `List.take` (directly or under a post-map)
-- and raw-only conditional guards are rejected by `ppt`.
example : True := by
  fail_if_success have : IsOraclePPTOn encBits encBits (fun word =>
      ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), word)) := by ppt
  fail_if_success have : IsOraclePPTOn encBits encBool (fun word =>
      (fun reply => reply.headD false) <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), word)) := by ppt
  fail_if_success have : IsOraclePPTOn (Operation := Unit) encBits encBool (fun word =>
      if rawOnlyGuard word then pure true else pure false) := by ppt
  trivial

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
