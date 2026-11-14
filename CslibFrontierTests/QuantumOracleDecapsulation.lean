/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontierTests.Crypto.MLKEMFixture
public import CslibFrontier.Crypto.Computational.Encryption.CCA
public import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! A one-bit-key instantiation of the actual ML-KEM transform over the shared toy K-PKE.
Two-bit selectors name three distinct ciphertexts; they are not FIPS byte encodings. The
classical caller makes one charged ideal service query and returns a padded two-bit option.
The native certificate covers the caller, not an implementation of the decapsulation service.
Both accepted and implicit-rejection keys read the same finite table supplied by the caller. -/

public section

namespace CslibFrontierTests.QuantumOracleDecapsulation

open Cslib Cslib.Crypto Cslib.Crypto.MLKEM Cslib.Crypto.Protocols Cslib.Crypto.Encryption
open Cslib.Probability Turing.MultiTapeTM CslibFrontierTests.Crypto.MLKEM

abbrev Hash := (Fin 1 → Bool) → Fin 1 → Bool

/-- The three valid toy ciphertext selectors. -/
inductive Request
  | honest
  | tampered
  | challenge
  deriving DecidableEq

instance : Fintype Request :=
  ⟨{.honest, .tampered, .challenge}, by intro q; cases q <;> simp⟩

/-- Canonical two-bit request words. The fourth two-bit word is invalid. -/
@[expose] def requestWord : Request → List Bool
  | .honest => [false, false]
  | .tampered => [false, true]
  | .challenge => [true, false]

/-- Honest and challenge ciphertexts encrypt different messages using the existing toy coins. -/
@[expose] def requestCiphertext : Request → Ciphertext toy
  | .honest => encrypt toy toyPK toyM (toyR, toyE₁, toyE₂)
  | .tampered => toyTampered
  | .challenge => encrypt toy toyPK (fun _ => false) (toyR, toyE₁, toyE₂)

theorem requestCiphertext_injective : Function.Injective requestCiphertext := by decide

@[simp] theorem length_requestWord (q : Request) : (requestWord q).length = 2 := by cases q <;> rfl

/-- Reject all noncanonical words, including extensions of a valid selector. -/
@[expose] def decodeRequest : List Bool → Option Request
  | [false, false] => some .honest
  | [false, true] => some .tampered
  | [true, false] => some .challenge
  | _ => none

@[simp] theorem decodeRequest_requestWord (q : Request) :
    decodeRequest (requestWord q) = some q := by cases q <;> rfl

theorem decodeRequest_eq_some_iff (w : List Bool) (q : Request) :
    decodeRequest w = some q ↔ w = requestWord q := by
  cases w with
  | nil => cases q <;> simp [decodeRequest, requestWord]
  | cons a w =>
    cases w with
    | nil => cases a <;> cases q <;> simp [decodeRequest, requestWord]
    | cons b w =>
      cases w with
      | nil => cases a <;> cases b <;> cases q <;> simp [decodeRequest, requestWord]
      | cons c w => cases a <;> cases b <;> cases q <;> simp [decodeRequest, requestWord]

/-- No accepted alias can denote the excluded challenge ciphertext. -/
theorem decode_challenge_iff (w : List Bool) :
    (decodeRequest w).map requestCiphertext = some (requestCiphertext .challenge) ↔
      w = requestWord .challenge := by
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨q, hq, heq⟩
    exact (decodeRequest_eq_some_iff w q).mp hq |>.trans
      (congrArg requestWord (requestCiphertext_injective heq))
  · rintro rfl
    exact ⟨.challenge, decodeRequest_requestWord _, rfl⟩

/-- Accepted keys read table address zero; the encryption coins remain the shared toy coins. -/
def hashG (H : Hash) : (Fin toy.n → Bool) × (Fin 256 → Bool) → Bool × Coins toy :=
  fun _ => (H (fun _ => false) 0, (toyR, toyE₁, toyE₂))

/-- Implicit-rejection keys read address one of the very same table. -/
def hashJ (H : Hash) : (Fin 256 → Bool) × Ciphertext toy → Bool :=
  fun _ => H (fun _ => true) 0

/-- The existing ML-KEM re-encryption/implicit-rejection transform with a toy one-bit key. -/
noncomputable def decaps (H : Hash) (c : Ciphertext toy) : Bool :=
  MLKEMTransform.decapsWith (toExplicitCoinPKE toy) (hashG H) (hashJ H) toyDK c

theorem decaps_honest (H : Hash) :
    decaps H (requestCiphertext .honest) = H (fun _ => false) 0 := by
  apply MLKEMTransform.decapsWith_encT (toExplicitCoinPKE toy) (hashG H) (hashJ H) toyDK toyM
  change some (decrypt toy toyS (encrypt toy toyPK toyM (toyR, toyE₁, toyE₂))) = some toyM
  rw [toyPK, decrypt_encrypt_eq_of_noise_le toy (B := 3) (by decide)
    toyA toyS toyE toyR toyE₁ toyE₂ toyM (toy_noise_le toyM)]

theorem decaps_tampered (H : Hash) :
    decaps H (requestCiphertext .tampered) = H (fun _ => true) 0 := by
  apply MLKEMTransform.decapsWith_of_reencrypt_ne (toExplicitCoinPKE toy)
    (hashG H) (hashJ H) toyDK (requestCiphertext .tampered)
  intro m' _
  exact toy_encrypt_ne_tampered m'

/-- Decode a canonical toy ciphertext selector before calling the transform. -/
noncomputable def decrypt (H : Hash) (_ : ℕ) (_ : List Bool) (w : List Bool) : Option Bool :=
  (decodeRequest w).map (decaps H ∘ requestCiphertext)

/-- Existing CCA phase-two challenge exclusion, interpreted as an ideal classical service. -/
noncomputable def handler (H : Hash) (request : Unit × List Bool) : StateT Unit PMF (List Bool) :=
  fun s => ProbComp.eval (cca2Phase2Oracle encBool (decrypt H) 0 []
    (requestWord .challenge) request s)

/-- Pad or truncate to exactly two bits, preserving the Option tag. -/
@[expose] def padReply (reply : List Bool) : List Bool := (reply ++ [false, false]).take 2

@[simp] theorem length_padReply (reply : List Bool) : (padReply reply).length = 2 := by
  simp [padReply]

/-- Make one classical query, read at most two reply bits, and pad the returned word. -/
@[expose] def caller (request : List Bool) : WordOracleComp Unit (List Bool) :=
  padReply <$> (List.take 2 <$> ProbOracleComp.query ((), request))

theorem caller_isOraclePPTOn : IsOraclePPTOn encBits encBits caller := by
  have hpad : ComputableInPolyTime padReply encBits encBits := by
    unfold padReply
    fun_prop
  exact (IsOraclePPTOn.query_take' () ComputableInPolyTime.id'
    (ComputableInPolyTime.const 2)).map' hpad

theorem caller_isQueryBounded (request : List Bool) : (caller request).IsQueryBounded 1 := by
  simpa only [caller, ProbOracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff] using
    (ProbOracleComp.IsQueryBounded.query
      (spec := fun _ : Unit × List Bool => List Bool) ((), request))

theorem caller_queriesSatisfy (request : List Bool) :
    (caller request).QueriesSatisfy (fun q => q = ((), request)) := by
  simpa only [caller, ProbOracleComp.QueriesSatisfy, OracleComp.queriesSatisfy_map_iff] using
    (ProbOracleComp.QueriesSatisfy.query (spec := fun _ : Unit × List Bool => List Bool)
      (p := fun q => q = ((), request)) (q := ((), request)) rfl)

/-- Each canonical request charges exactly two request bits. -/
theorem caller_queryLength (q : Request) :
    (caller (requestWord q)).QueriesSatisfy (fun request => request.2.length = 2) :=
  (caller_queriesSatisfy _).mono fun _ h => h ▸ length_requestWord q

/-- The reply-only law for a quantum/classical boundary; the sampled table remains an argument. -/
noncomputable def service (H : Hash) (request : List Bool) : PMF (List Bool) :=
  (ProbOracleComp.runWith (handler H) (caller request) ()).map Prod.fst

/-- The native one-query caller agrees with the padded existing CCA challenge filter. -/
theorem runWith_caller (H : Hash) (w : List Bool) :
    ProbOracleComp.runWith (handler H) (caller w) () = PMF.pure
      ((if w = requestWord .challenge then [false, false]
        else padReply (encOption encBool (decrypt H 0 [] w))), ()) := by
  simp only [caller, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, handler,
    cca2Phase2Oracle]
  by_cases hw : w = requestWord .challenge
  · simp [hw, padReply]
  · cases decrypt H 0 [] w <;> simp [hw, padReply, encOption, encBool_apply]

theorem service_eq (H : Hash) (w : List Bool) : service H w = PMF.pure
    (if w = requestWord .challenge then [false, false]
      else padReply (encOption encBool (decrypt H 0 [] w))) := by
  simp [service, runWith_caller]

/-- Accepted decapsulation and coherent access can inspect the same table cell. -/
theorem service_honest (H : Hash) :
    service H (requestWord .honest) = PMF.pure [true, H (fun _ => false) 0] := by
  rw [service_eq]
  simp [requestWord, decrypt, decodeRequest, decaps_honest, padReply, encOption, encBool_apply]

/-- An allowed tampered ciphertext returns the implicit-rejection key, tagged as a key. -/
theorem service_tampered (H : Hash) :
    service H (requestWord .tampered) = PMF.pure [true, H (fun _ => true) 0] := by
  rw [service_eq]
  simp [requestWord, decrypt, decodeRequest, decaps_tampered, padReply, encOption, encBool_apply]

/-- Forbidden challenges are rejected before the transform is called. -/
theorem service_challenge (H : Hash) :
    service H (requestWord .challenge) = PMF.pure [false, false] := by
  simp [service_eq]

theorem length_of_mem_support_service (H : Hash) (w reply : List Bool)
    (h : reply ∈ (service H w).support) : reply.length = 2 := by
  rw [service_eq, PMF.mem_support_pure_iff] at h
  subst reply
  split <;> simp

-- A legitimate false key keeps its `some` tag and differs from forbidden-challenge rejection.
example : service (fun _ _ => false) (requestWord .honest) = PMF.pure [true, false] ∧
    service (fun _ _ => false) (requestWord .challenge) = PMF.pure [false, false] := by
  exact ⟨service_honest _, service_challenge _⟩

example : service (fun _ _ => false) (requestWord .honest) ≠
    service (fun _ _ => false) (requestWord .challenge) := by
  rw [service_honest, service_challenge]
  intro h
  have hmass := congrArg (fun p : PMF (List Bool) => p [true, false]) h
  simp [PMF.pure_apply] at hmass

-- The fourth selector and noncanonical extensions are invalid, not aliases of the challenge.
example (H : Hash) : service H [true, true] = PMF.pure [false, false] ∧
    service H [true, false, false] = PMF.pure [false, false] := by
  simp [service_eq, requestWord, decrypt, decodeRequest, padReply]

end CslibFrontierTests.QuantumOracleDecapsulation
