/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Signature
import Complexity.Crypto.Computational.MAC
import ComplexityTests.PolyTimePlainDriver

/-! Actual imported verification projections must be indexed by their programs. Unsupported
predicates must not silently register an inert certificate under their last argument. -/

open Turing.MultiTapeTM Cslib.Crypto

run_meta do
  for (certificate, program) in
      [(`Cslib.Crypto.SignatureScheme.verify_polyTime, `Cslib.Crypto.SignatureScheme.verify),
       (`Cslib.Crypto.MACScheme.verify_polyTime, `Cslib.Crypto.MACScheme.verify)] do
    let type := (← Lean.getConstInfo certificate).type
    let key ← Lean.Meta.forallTelescope type fun _ conclusion =>
      Cslib.Tactic.efficiencyKey conclusion
    unless key == (`Turing.MultiTapeTM.ComputableInPolyTime, program, false) do
      throwError "incorrect imported verification key: {key}"
    let entries := (Cslib.Tactic.certificateExt.getState (← Lean.getEnv)).getD key #[]
    unless entries.any (fun entry => entry.1 == certificate) do
      throwError "actual verification certificate absent from its program key: {certificate}"

example (S : SignatureScheme) : ComputableInPolyTime
    (fun p : List Bool × List Bool × List Bool => S.verify p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) encBool := by polytime

example (M : MACScheme) : ComputableInPolyTime
    (fun p : List Bool × List Bool × List Bool => M.verify p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) encBool := by polytime

-- This existing irreducible routine and certificate come from another ordinary module import.
-- The eager contract prevents fun_prop alone from hiding an inert named-certificate path.
example (B : Cslib.WordRAM.Basis) (c : ℕ) : ComputableInPolyTime
    (PlainDriverTests.checkedNamedConstant B c c) encUnary (encOption encNat) := by
  fail_if_success fun_prop
  polytime

namespace ProgramCertificateDiagnostics

def NotEfficiency (_ : List Bool → List Bool) : Prop := True

theorem wrongPredicate : NotEfficiency List.reverse := True.intro

/--
error: unsupported efficiency predicate `ProgramCertificateDiagnostics.NotEfficiency` for
`program_certificate`; expected TM polynomial time, PPT, or a documented word-RAM certificate
-/
#guard_msgs (whitespace := lax) in
attribute [program_certificate] wrongPredicate

theorem noProgram : True := True.intro

/--
error: unsupported efficiency predicate `True` for `program_certificate`; expected
TM polynomial time, PPT, or a documented word-RAM certificate
-/
#guard_msgs (whitespace := lax) in
attribute [program_certificate] noProgram

end ProgramCertificateDiagnostics
