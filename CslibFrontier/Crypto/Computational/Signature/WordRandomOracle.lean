/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.Signature.RandomOracle.Simulation
public import CslibFrontier.Computability.Probabilistic.Oracle.ReplayParameter
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape.QueryBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape.Substitution
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native word forgers in the typed random-oracle signature world

Channel `false` signs a word; channel `true` hashes a word. Every hash payload is retained as a
distinct query, and digest replies use the supplied injective encoding. Signing randomness remains
in the shared world, separate from the forger's saved coins. The existing total pair decoder
handles arbitrary native output, including words that are not canonical pair encodings.

The saved-coin adapter returns the empty pair without calls on oversized public keys, and truncates
every supplied tape at the original input-dependent machine clock. Its sampling budget depends only
on the security parameter.
These are bridges between existing models, not a Schnorr security reduction.
The scheme's signer and shared oracle remain the existing typed world; this module does not
certify their native realization or the complete forking reduction.

## Main definitions

* `Cslib.Crypto.Protocols.ROMSignature.wordQuery`: exact Boolean channel routing.
* `Cslib.Crypto.Protocols.ROMSignature.routeWordProgram`: retain private sampling while routing.
* `Cslib.Crypto.Protocols.ROMSignature.savedCoinForger`: the existing explicit-coin forger model.
* `Cslib.Crypto.Protocols.ROMSignature.encReplayInput`: the encoding of a saved-coin replay's
  input.

## Main results

* `Cslib.Crypto.Protocols.ROMSignature.isOraclePPTOn_savedWordReplay`: native efficiency of the
  full guarded, truncated and decoded replay input.
* `Cslib.Crypto.Protocols.ROMSignature.callBounded_savedCoinForger`: every key and tape obey the
  parameter-only signing and hash budgets.
* `Cslib.Crypto.Protocols.ROMSignature.exists_savedCoinForger`: actual PPT key generation and
  an actual oracle-PPT forger give a joint-state-preserving adapter.
* `Cslib.Crypto.Protocols.ROMSignature.exists_eufCmaGame_savedCoinForger`: equality of the existing
  shared-world native-forger game and explicit-coin EUF-CMA game.

## References

Original adapters for the existing native oracle-PPT and typed ROM signature models.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.ROMSignature

open Probability OracleComp
open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM

variable {Digest α : Type}

/-- Route the signing channel and hash channel without decoding or identifying hash payloads. -/
def wordQuery (digestEncoding : Digest ↪ List Bool) :
    Bool → List Bool → OracleComp (ForgerSpec (List Bool) (List Bool) (List Bool) Digest)
      (List Bool)
  | false, word =>
    OracleComp.query (spec := ForgerSpec (List Bool) (List Bool) (List Bool) Digest) (.inl word)
  | true, word => digestEncoding <$>
    OracleComp.query (spec := ForgerSpec (List Bool) (List Bool) (List Bool) Digest) (.inr word)

/-- Route a native word program into the existing typed signature world, retaining its private
random sampling. Digest encodings affect replies only; all request words remain distinct. -/
def routeWordProgram (digestEncoding : Digest ↪ List Bool)
    (program : WordOracleComp Bool α) :
    ProbOracleComp (ForgerSpec (List Bool) (List Bool) (List Bool) Digest) α :=
  interpret (sumHandler (fun n => ProbOracleComp.sample (ProbComp.unifFin n))
    (fun request => liftOracleForger (wordQuery digestEncoding request.1 request.2))) program

/-- Routing retains the joint output and state of any typed handler. -/
theorem run_interpret_routeWordProgram (digestEncoding : Digest ↪ List Bool)
    (program : WordOracleComp Bool α) {Store : Type}
    (handler : (q : List Bool ⊕ List Bool) →
      StateT Store PMF (ForgerSpec (List Bool) (List Bool) (List Bool) Digest q)) (s : Store) :
    ProbOracleComp.runWith handler (routeWordProgram digestEncoding program) s =
      ProbOracleComp.runWith
        (fun request => interpret handler (wordQuery digestEncoding request.1 request.2))
        program s := by
  unfold routeWordProgram ProbOracleComp.runWith OracleComp.runWith
  rw [interpret_interpret]
  congr 2 with q : 1
  cases q with
  | inl n => simp [sumHandler, ProbOracleComp.interpret_sample, ProbComp.unifFin]
  | inr request =>
    simp only [sumHandler, liftOracleForger, interpret_interpret]
    congr 1 with q : 1
    simp [ProbOracleComp.query, sumHandler]

/-- Native replay and typed routing commute as programs, before choosing any oracle world. -/
theorem routeWordProgram_runCoins {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Bool) (digestEncoding : Digest ↪ List Bool)
    (coins input : List Bool) :
    routeWordProgram digestEncoding
      (machine.runCoins (fun op word => ProbOracleComp.query (op, word)) coins input) =
    liftOracleForger (machine.runCoins (wordQuery digestEncoding) coins input) := by
  simp only [routeWordProgram, liftOracleForger, interpret_runCoins,
    ProbOracleComp.query, interpret_query, sumHandler]

/-- One polynomial budget for the source clock on every admitted public key. -/
def savedCoinBudget (c d keyC keyD n : ℕ) : ℕ :=
  c * (2 * n + 2 + keyC * (n + 1) ^ keyD) ^ d

/-- The saved-coin budget is polynomial in the security parameter. -/
theorem polynomiallyBounded_savedCoinBudget (c d keyC keyD : ℕ) :
    PolynomiallyBounded (savedCoinBudget c d keyC keyD) := by
  unfold savedCoinBudget
  fun_prop

/-- Input `(1ⁿ, pk, tape)` of a saved-coin replay (`savedWordReplay`): the security parameter `n`
in unary, then the public key and the saved coin tape as bit words. The parameter and the public
key are framed. -/
abbrev encReplayInput : ℕ × List Bool × List Bool ↪ List Bool :=
  encPair encUnary (encPair encBits encBits)

/-- Guard the public input, truncate the saved tape, and decode the output, with the original
external channels supplied explicitly. Malformed output uses the existing total pair decoder. -/
def savedWordReplay {k : ℕ} {Control Query : Type} {spec : OracleSpec Query}
    (machine : MultiTapePTM k Bool Control Bool)
    (query : Bool → List Bool → OracleComp spec (List Bool)) (c d keyC keyD : ℕ)
    (p : ℕ × List Bool × List Bool) : OracleComp spec (List Bool × List Bool) :=
  if p.2.1.length ≤ keyC * (p.1 + 1) ^ keyD then
    (Decoder.bits.pair Decoder.bits).decode <$>
      machine.runCoins query
        (p.2.2.take (c * ((encPair encUnary encBits (p.1, p.2.1)).length + 1) ^ d))
        (encPair encUnary encBits (p.1, p.2.1))
  else pure ([], [])

/-- The complete guarded, truncated, decoded replay is strict oracle-PPT in its full input,
including the security parameter, public key, and arbitrary saved tape. -/
@[fun_prop] theorem isOraclePPTOn_savedWordReplay {k : ℕ} {Control : Type} [Finite Control]
    (machine : MultiTapePTM k Bool Control Bool) (c d keyC keyD : ℕ) :
    IsOraclePPTOn encReplayInput (encPair encBits encBits)
      (savedWordReplay machine (fun op word => ProbOracleComp.query (op, word)) c d keyC keyD) := by
  unfold savedWordReplay
  apply IsOraclePPTOn.ite'
  · fun_prop
  · apply IsOraclePPTOn.map' _ (Decoder.bits.pair Decoder.bits).computableInPolyTime
    apply machine.isOraclePPTOn_runCoins.preprocess'
      (prepare := fun p : ℕ × List Bool × List Bool =>
      (p.2.2.take (c * ((encPair encUnary encBits (p.1, p.2.1)).length + 1) ^ d),
        encPair encUnary encBits (p.1, p.2.1)))
    have hin : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => encPair encUnary encBits (p.1, p.2.1))
        (encPair encUnary (encPair encBits encBits)) encBits := by
      apply ComputableInPolyTime.encoding_comp
      fun_prop
    have hcut : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool =>
          c * ((encPair encUnary encBits (p.1, p.2.1)).length + 1) ^ d)
        (encPair encUnary (encPair encBits encBits)) encUnary := by fun_prop
    exact (ComputableInPolyTime.bitsTakeWithInput (by fun_prop) hcut).prod hin
  · fun_prop

/-- Use the existing total pair decoder after native replay. Oversized keys make no calls; all
coin tapes, including overlong ones outside the sampling support, are truncated before replay. -/
noncomputable def savedCoinForger {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Bool) (digestEncoding : Digest ↪ List Bool)
    (c d keyC keyD n : ℕ) :
    Forger (List Bool) (List Bool) (List Bool) (List Bool) Digest where
  Coins := List Bool
  coins := BitString.uniformList (savedCoinBudget c d keyC keyD n)
  forge pk coins := savedWordReplay machine (wordQuery digestEncoding) c d keyC keyD (n, pk, coins)

/-- The efficient native guarded replay is exactly the typed fixed-coin forger after channel
routing, including the oversized-key branch and total decoding of arbitrary output words. -/
theorem routeWordProgram_savedWordReplay {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Bool) (digestEncoding : Digest ↪ List Bool)
    (c d keyC keyD n : ℕ) (pk coins : List Bool) :
    routeWordProgram digestEncoding
      (savedWordReplay machine (fun op word => ProbOracleComp.query (op, word))
        c d keyC keyD (n, pk, coins)) =
    liftOracleForger ((savedCoinForger machine digestEncoding c d keyC keyD n).forge pk coins) := by
  unfold savedCoinForger savedWordReplay
  split
  · rename_i hpk
    change interpret _ ((Decoder.bits.pair Decoder.bits).decode <$> _) = _
    rw [interpret_map]
    change (Decoder.bits.pair Decoder.bits).decode <$>
      routeWordProgram digestEncoding (machine.runCoins _ _ _) = _
    rw [routeWordProgram_runCoins]
    simp only [liftOracleForger, ite_eq_left hpk, interpret_map]
  · rename_i hpk
    simp only [routeWordProgram, liftOracleForger, ite_eq_right hpk, interpret_pure]

/-- Signing and hashing each cost at most one external call in the word routing. -/
theorem isQueryBounded_wordQuery (digestEncoding : Digest ↪ List Bool) (op : Bool)
    (word : List Bool) : IsQueryBounded (wordQuery digestEncoding op word) 1 := by
  cases op with
  | false => exact IsCostBounded.query _
  | true => exact (isCostBounded_map_iff _ _ _).mpr (IsCostBounded.query _)

/-- The fixed-coin forger has uniform signing and hash budgets for every key and every tape. -/
theorem callBounded_savedCoinForger {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Bool) (digestEncoding : Digest ↪ List Bool)
    (c d keyC keyD n : ℕ) :
    (savedCoinForger machine digestEncoding c d keyC keyD n).CallBounded
      (savedCoinBudget c d keyC keyD n) (savedCoinBudget c d keyC keyD n) := by
  intro pk coins
  change List Bool at coins
  have htotal : IsQueryBounded
      ((savedCoinForger machine digestEncoding c d keyC keyD n).forge pk coins)
      (savedCoinBudget c d keyC keyD n) := by
    dsimp only [savedCoinForger, savedWordReplay]
    split
    · rename_i hpk
      apply (isCostBounded_map_iff _ _ _).mpr
      have h := machine.isCostBounded_runCoins (wordQuery digestEncoding) 1
        (isQueryBounded_wordQuery digestEncoding)
        (coins.take (c * ((encPair encUnary encBits (n, pk)).length + 1) ^ d))
        (encPair encUnary encBits (n, pk))
      apply h.mono
      simp only [List.length_take, Nat.mul_one]
      apply (Nat.min_le_left _ _).trans
      apply Nat.mul_le_mul_left c
      apply Nat.pow_le_pow_left
      simp only [length_encPair, encUnary_apply,
        List.length_replicate, encBits_apply] at *
      omega
    · exact .pure _ _
  exact ⟨htotal.of_le (fun q => by cases q <;> simp [signingCost]),
    htotal.of_le (fun q => by cases q <;> simp [hashCost])⟩

private theorem run_interpret_decode_mixture (digestEncoding : Digest ↪ List Bool)
    (program : WordOracleComp Bool (List Bool × List Bool)) (coins : PMF (List Bool))
    (replay : List Bool → WordOracleComp Bool (List Bool))
    (h : ∀ (Store : Type)
      (handler : Bool × List Bool → StateT Store PMF (List Bool)) s,
      ProbOracleComp.runWith handler (encPair encBits encBits <$> program) s =
        coins.bind (fun r => ProbOracleComp.runWith handler (replay r) s))
    (Store : Type) (handler : (q : List Bool ⊕ List Bool) →
      StateT Store PMF (ForgerSpec (List Bool) (List Bool) (List Bool) Digest q)) (s : Store) :
    ProbOracleComp.runWith handler (routeWordProgram digestEncoding program) s =
      coins.bind (fun r => ProbOracleComp.runWith handler
        ((Decoder.bits.pair Decoder.bits).decode <$>
          routeWordProgram digestEncoding (replay r)) s) := by
  have heq := congrArg (PMF.map (Prod.map (Decoder.bits.pair Decoder.bits).decode id))
    (h Store (fun request => interpret handler (wordQuery digestEncoding request.1 request.2)) s)
  simp only [PMF.map_bind, ← ProbOracleComp.runWith_map, Functor.map_map, Decoder.decode_enc,
    id_map'] at heq
  have hmap (p : WordOracleComp Bool (List Bool)) :
      (Decoder.bits.pair Decoder.bits).decode <$> routeWordProgram digestEncoding p =
        routeWordProgram digestEncoding ((Decoder.bits.pair Decoder.bits).decode <$> p) :=
    (interpret_map _ _ _).symm
  simpa only [hmap, run_interpret_routeWordProgram] using heq

/-- An actual uniform native forger has a key-independent saved-coin adapter. The key-size guard
is derived from actual strict-PPT key generation. Equality retains the complete state of every
typed signing/hash handler; in particular the handler's own randomness is not pre-sampled here. -/
theorem exists_savedCoinForger
    {gen : ℕ → ProbComp (List Bool × List Bool)}
    (hgen : IsPPTOn encUnary (encPair encBits encBits) gen)
    {program : ℕ → List Bool → WordOracleComp Bool (List Bool × List Bool)}
    (hprogram : IsOraclePPT (encPair encBits encBits) program) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM k Bool Control Bool) (c d keyC keyD : ℕ),
      IsOraclePPTOn encReplayInput (encPair encBits encBits)
        (savedWordReplay machine (fun op word => ProbOracleComp.query (op, word)) c d keyC keyD) ∧
      ∀ n keys, keys ∈ (ProbComp.eval (gen n)).support →
        ∀ (Digest : Type) (digestEncoding : Digest ↪ List Bool) (Store : Type)
          (handler : (q : List Bool ⊕ List Bool) →
          StateT Store PMF (ForgerSpec (List Bool) (List Bool) (List Bool) Digest q)) s,
        ProbOracleComp.runWith handler (routeWordProgram digestEncoding (program n keys.1)) s =
        (savedCoinForger machine digestEncoding c d keyC keyD n).coins.bind (fun coins =>
          ProbOracleComp.runWith handler
            (liftOracleForger
              ((savedCoinForger machine digestEncoding c d keyC keyD n).forge
                keys.1 coins)) s) := by
  obtain ⟨k, Control, hfinite, machine, c, d, keyC, keyD, hkeys, _, _, hrun⟩ :=
    hprogram.exists_savedCoins_of_keyGen hgen
  let := hfinite
  refine ⟨k, Control, hfinite, machine, c, d, keyC, keyD,
    isOraclePPTOn_savedWordReplay machine c d keyC keyD, ?_⟩
  intro n keys hkeys' Digest digestEncoding Store handler s
  have hpk := hkeys n keys hkeys'
  have h := run_interpret_decode_mixture digestEncoding (program n keys.1) _ _
    (hrun n keys.1 hpk) Store handler s
  simpa only [savedCoinForger, savedWordReplay, savedCoinBudget, ite_eq_left hpk,
    routeWordProgram_runCoins,
    liftOracleForger, interpret_map] using h

/-- The native private-random word forger and its explicit-coin adapter give exactly the same
existing EUF-CMA game. Signing, hash queries, and final verification share one memoized world;
freshness excludes only signing the final message, so repeated signing queries are allowed.
One native replay machine and clock work for every digest type and encoding, which may therefore
vary with the security parameter.
This bridge does not assert unforgeability or a discrete-log reduction. -/
theorem exists_eufCmaGame_savedCoinForger {gen : ℕ → ProbComp (List Bool × List Bool)}
    (hgen : IsPPTOn encUnary (encPair encBits encBits) gen)
    {program : ℕ → List Bool → WordOracleComp Bool (List Bool × List Bool)}
    (hprogram : IsOraclePPT (encPair encBits encBits) program) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM k Bool Control Bool) (c d keyC keyD : ℕ),
      IsOraclePPTOn encReplayInput (encPair encBits encBits)
        (savedWordReplay machine (fun op word => ProbOracleComp.query (op, word)) c d keyC keyD) ∧
      ∀ n (Digest : Type) [Fintype Digest] [Nonempty Digest]
        (digestEncoding : Digest ↪ List Bool)
        (scheme : Scheme (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) Digest),
        scheme.keyGen = ProbComp.eval (gen n) →
        (savedCoinForger machine digestEncoding c d keyC keyD n).CallBounded
          (savedCoinBudget c d keyC keyD n) (savedCoinBudget c d keyC keyD n) ∧
        worldGame scheme (fun pk => routeWordProgram digestEncoding (program n pk))
          (fun verified ⟨msg, _⟩ pairs => verified && !(pairs.map Prod.fst).contains msg) =
        eufCmaGame scheme (savedCoinForger machine digestEncoding c d keyC keyD n) := by
  obtain ⟨k, Control, hfinite, machine, c, d, keyC, keyD, hefficient, hrun⟩ :=
    exists_savedCoinForger hgen hprogram
  refine ⟨k, Control, hfinite, machine, c, d, keyC, keyD, hefficient, ?_⟩
  intro n Digest _ _ digestEncoding scheme hgen'
  refine ⟨callBounded_savedCoinForger machine digestEncoding c d keyC keyD n, ?_⟩
  rw [eufCmaGame_eq_worldGame]
  unfold worldGame
  apply PMF.bind_congr_on_support
  intro keys hkeys
  rw [hgen'] at hkeys
  have hcontains (pairs : List (List Bool × List Bool)) (msg : List Bool) :
      @List.contains (List Bool) instBEqOfDecidableEq (pairs.map Prod.fst) msg =
        (pairs.map Prod.fst).contains msg := by
    apply Bool.eq_iff_iff.mpr
    simp
  simpa only [PMF.monad_bind_eq_bind, hcontains] using
    eval_worldRealize_eq_bind scheme keys.1 keys.2 _ _ _
      (hrun n keys hkeys Digest digestEncoding)
      (fun verified ⟨msg, _⟩ pairs => verified && !(pairs.map Prod.fst).contains msg)

end Cslib.Crypto.Protocols.ROMSignature
