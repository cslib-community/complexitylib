/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SchnorrSignature.EncodedROM
public import CslibFrontier.Computability.Interactive.Security.Oracle
public import CslibFrontier.Crypto.Computational.Signature.WordRandomOracle

/-!
# Actual Schnorr sampling in the adaptive random-oracle game

`schnorrEncodedROMScheme` takes its key law and scalar-nonce law as parameters. The native
algorithms sample with `schnorrSigKeyGen` and `sampleExp`, each within statistical distance `2⁻ⁿ`
of the ideal uniform law, and the typed Fiat–Shamir bound
(`succProbability_eufCmaGame_schnorrWordROMScheme_le`) is proved for the ideal laws. This module
moves a forger from the actual laws to the ideal ones in the existing EUF-CMA game:

* each signing call pays one nonce error, with the forger's output, the shared hash cache and the
  signing log all retained; hash calls pay nothing, because their transitions are identical;
* key generation pays one more error, before the exact ideal representation bridge
  `eufCmaGame_schnorrEncodedROMScheme_eq` applies.

For a forger making at most `Qs` signing calls the total is `(Qs + 1) / 2 ^ n`. For a native
oracle-PPT forger and a polynomial-time deterministic group description, the saved-coin adapter
of `WordRandomOracle` supplies the call budget, so the bound needs no assumed query cap. These are
statistical transport laws for the existing games; they do not certify the forking reduction.

## Main results

* `closeTo_runWith_schnorrEncodedROMScheme`: adaptive joint-state nonce replacement.
* `closeTo_eufCmaGame_schnorrEncodedROMScheme`: actual key and nonce sampling versus the ideal game.
* `exists_closeTo_worldGame_schnorrEncodedROMScheme`: native forgers with a derived polynomial
  query budget, for explicitly polynomial-time deterministic descriptions.

## References

Original compositions of the existing sampler, stateful replacement and representation laws.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Interactive Protocols Protocols.ROMSignature OracleComp Turing.MultiTapeTM
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily) (d : F.Desc) (n m : ℕ)

/-- Adaptive signing pays one sampler error per signing request, retaining all output and state.
The secret key is an arbitrary word, and the cache and log may already contain entries. -/
theorem closeTo_runWith_schnorrEncodedROMScheme
    (keyLaw : PMF (List Bool × List Bool)) (sk : List Bool) {α : Type}
    (program : OracleComp (ForgerSpec (List Bool) (List Bool) (List Bool) (BitString m)) α)
    {Qs : ℕ} (h : IsCostBounded signingCost program Qs)
    (state : List (List Bool × BitString m) × List (List Bool)) :
    CloseTo
      (runWith (handler (F.schnorrEncodedROMScheme d m keyLaw
        ((ProbComp.eval (F.sampleExp n d)).map Nat.cast)) sk) program state)
      (runWith (handler (F.schnorrEncodedROMScheme d m keyLaw
        (PMF.uniformOfFintype (ZMod (F.order d)))) sk) program state)
      (Qs * (1 / 2 ^ n : ℝ≥0)) := by
  apply h.closeTo_runWith
  intro q state
  cases q with
  | inl msg =>
    simpa only [signingCost, Nat.cast_one, one_mul, handler, schnorrEncodedROMScheme,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, runWith] using
      (F.closeTo_uniform_sampleExp n d).symm.bind_left (fun r => do
        let signed ← runWith (oracle (BitString m))
          ((F.schnorrEncodedROMScheme d m keyLaw
            (PMF.uniformOfFintype (ZMod (F.order d)))).sign sk msg r) state.1
        return (signed.1, (signed.2, msg :: state.2)))
  | inr word =>
    simpa only [signingCost, Nat.cast_zero, zero_mul, handler] using
      CloseTo.refl (handler (F.schnorrEncodedROMScheme d m keyLaw
        (PMF.uniformOfFintype (ZMod (F.order d)))) sk (Sum.inr word) state)

/-- The actual key and nonce distributions cost at most one key error plus one error per signing
call. The final verification uses the same cache; repeated signing requests remain allowed.
The right side is the existing canonical word game, with total outer signature decoding. -/
theorem closeTo_eufCmaGame_schnorrEncodedROMScheme (hm : 2 ^ m ≤ F.order d)
    (A : Forger (List Bool) (List Bool) (List Bool) (List Bool) (BitString m))
    {Qs Qro : ℕ} (hA : A.CallBounded Qs Qro) :
    CloseTo
      (eufCmaGame (F.schnorrEncodedROMScheme d m
        (ProbComp.eval (F.schnorrSigKeyGen n d))
        ((ProbComp.eval (F.sampleExp n d)).map Nat.cast)) A)
      (eufCmaGame (F.schnorrWordROMScheme d hm) (F.schnorrDecodedForger d A))
      ((Qs + 1 : ℕ) * (1 / 2 ^ n : ℝ≥0)) := by
  rw [← F.eufCmaGame_schnorrEncodedROMScheme_eq d hm A]
  have hhandler (sk : List Bool) :
      handler (F.schnorrEncodedROMScheme d m (ProbComp.eval (F.schnorrSigKeyGen n d))
        ((ProbComp.eval (F.sampleExp n d)).map Nat.cast)) sk =
      handler (F.schnorrEncodedROMScheme d m (F.schnorrIdealKeyGen d)
        ((ProbComp.eval (F.sampleExp n d)).map Nat.cast)) sk := by
    funext q state
    cases q <;> rfl
  have hcontains (log : List (List Bool)) (msg : List Bool) :
      @List.contains (List Bool) instBEqOfDecidableEq log msg = log.contains msg := by
    apply Bool.eq_iff_iff.mpr
    simp
  unfold eufCmaGame
  simp only [PMF.monad_bind_eq_bind, hhandler, hcontains]
  have hkey := (F.closeTo_schnorrSigKeyGen n d).symm
  have hgame := hkey.bind (δ := Qs * (1 / 2 ^ n : ℝ≥0)) (fun keys _ =>
    CloseTo.bind_right A.coins (fun coins _ =>
      (F.closeTo_runWith_schnorrEncodedROMScheme d n m (F.schnorrIdealKeyGen d) keys.2
        (A.forge keys.1 coins) (hA keys.1 coins).1 ([], [])).bind_left (fun forged => do
          let verified ← runWith (oracle (BitString m))
            ((F.schnorrEncodedROMScheme d m (F.schnorrIdealKeyGen d)
              (PMF.uniformOfFintype (ZMod (F.order d)))).verify
                keys.1 forged.1.1 forged.1.2) forged.2.1
          return verified.1 && !(forged.2.2.contains forged.1.1))))
  simpa only [schnorrEncodedROMScheme, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm, runWith] using hgame

/-- An actual native forger gets one efficient replay and one parameter-only polynomial query
budget from actual key-generation support. Descriptions here are supplied by the stated
polynomial-time deterministic function; this does not assert a random-setup routing theorem.
The raw-word world game retains the actual key and nonce laws before statistical transport. -/
theorem exists_closeTo_worldGame_schnorrEncodedROMScheme
    (description : ℕ → F.Desc)
    (hdescription : ComputableInPolyTime description encUnary F.encDesc)
    (width : ℕ → ℕ) (hwidth : ∀ n, 2 ^ width n ≤ F.order (description n))
    {program : ℕ → List Bool → WordOracleComp Bool (List Bool × List Bool)}
    (hprogram : IsOraclePPT (encPair encBits encBits) program) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : _root_.Turing.MultiTapePTM k Bool Control Bool) (c e keyC keyD : ℕ),
      IsOraclePPTOn (encPair encUnary (encPair encBits encBits)) (encPair encBits encBits)
        (savedWordReplay machine (fun op word => ProbOracleComp.query (op, word))
          c e keyC keyD) ∧
      ∀ n,
        let digestEncoding : BitString (width n) ↪ List Bool := ⟨List.ofFn, List.ofFn_injective⟩
        let A := savedCoinForger machine digestEncoding c e keyC keyD n
        let budget := savedCoinBudget c e keyC keyD n
        A.CallBounded budget budget ∧
        CloseTo
          (worldGame (F.schnorrEncodedROMScheme (description n) (width n)
            (ProbComp.eval (F.schnorrSigKeyGen n (description n)))
            ((ProbComp.eval (F.sampleExp n (description n))).map Nat.cast))
            (fun pk => routeWordProgram digestEncoding (program n pk))
            (fun verified ⟨msg, _⟩ pairs => verified && !(pairs.map Prod.fst).contains msg))
          (eufCmaGame (F.schnorrWordROMScheme (description n) (hwidth n))
            (F.schnorrDecodedForger (description n) A))
          ((budget + 1 : ℕ) * (1 / 2 ^ n : ℝ≥0)) := by
  have hprepare : ComputableInPolyTime (fun n : ℕ => (n, description n))
      encUnary (encPair encUnary F.encDesc) :=
    (show ComputableInPolyTime (fun n : ℕ => n) encUnary encUnary by fun_prop).prod hdescription
  have hgen : IsPPTOn encUnary (encPair encBits encBits)
      (fun n => F.schnorrSigKeyGen n (description n)) :=
    IsPPTOn.preprocess
      (program := fun input : ℕ × F.Desc => F.schnorrSigKeyGen input.1 input.2)
      (prepare := fun n : ℕ => (n, description n))
      F.isPPTOn_schnorrSigKeyGen hprepare
  obtain ⟨k, Control, hfinite, machine, c, e, keyC, keyD, hefficient, hgame⟩ :=
    exists_eufCmaGame_savedCoinForger
      (gen := fun n => F.schnorrSigKeyGen n (description n)) (program := program) hgen hprogram
  refine ⟨k, Control, hfinite, machine, c, e, keyC, keyD, hefficient, ?_⟩
  intro n
  dsimp only
  obtain ⟨hbudget, heq⟩ := hgame n (BitString (width n)) ⟨List.ofFn, List.ofFn_injective⟩
    (F.schnorrEncodedROMScheme (description n) (width n)
      (ProbComp.eval (F.schnorrSigKeyGen n (description n)))
      ((ProbComp.eval (F.sampleExp n (description n))).map Nat.cast)) rfl
  refine ⟨hbudget, ?_⟩
  rw [heq]
  exact F.closeTo_eufCmaGame_schnorrEncodedROMScheme (description n) n (width n)
    (hwidth n) _ hbudget

end Cslib.Crypto.PrimeOrderGroupFamily
