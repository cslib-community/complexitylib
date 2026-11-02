/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.NativeDecode
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.NativeEncode
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputationTree
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives

/-!
# Native canonical-code validation

The semantic decoder assigns defaults to unused field words. The functional tree gate instead
requires an exact codeword. Re-serialization and comparison reject unused ranks, noncanonical
residues, track words and blank-cell words before local replay can start.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Encoding.NativeChecked

open Cslib Cslib.BitString MultiTapeTM ComputableInSpace QueryReplay

variable {k s : ℕ} {Q : Type} [Finite Q]

/-- Parse a successful label only if re-encoding its decoded data reproduces every input bit.
Rejected and FAIL labels return `none`; no default view is silently fed to the tree gate. -/
@[expose] noncomputable def parse (e : Q ≃ Fin s) (p : ℕ × List Bool) :
    Option (RawResult k Q) :=
  let decoded := NativeDecode.parse e p
  let raw := decoded.getD (none, fun _ => 0, .empty, fun _ => [])
  if NativeEncode.serialize e (p.1, true, raw) = p.2 then decoded else none

/-- Exact validation uses native linear space in the actual input word and binary width.
Equality uses its existing independent linear workspace bound, not its quadratic time bound. -/
theorem parse_inSpace (e : Q ≃ Fin s) :
    ComputableInSpace (parse (k := k) e) NativeDecode.encArgs (encOption encRawResult)
      (fun p => (NativeDecode.encArgs p).length) := by
  let empty : RawResult k Q := (none, fun _ => 0, .empty, fun _ => [])
  have hp := NativeDecode.parse_inSpace (k := k) e
  have hget : ComputableInSpace (fun x : Option (RawResult k Q) => x.getD empty)
      (encOption encRawResult) encRawResult
      (fun x => (encOption encRawResult x).length) :=
    of_inO (ComputableInDegree.getD (enc₁ := encRawResult) empty).inO_one
  have hr := budget_comp_linear hget hp
  have hinput := budget_prod (fst encNat encBits)
    (budget_prod (budget_const (encB := encBool) true (.refl _)) hr)
  have hout := budget_comp_linear (NativeEncode.serialize_bits_inSpace e) hinput
  have heq := budget_comp_linear (of_inO (ComputableInO.eq encBits))
    (budget_prod hout (snd encNat encBits))
  refine (budget_ite heq hp (budget_const none (.refl _))).of_enc_eq ?_
  intro p
  simp only [parse, Bool.decide_iff, empty]

omit [Finite Q] in
private theorem valid_of_parse_some (e : Q ≃ Fin s) (b : ℕ) [NeZero b]
    (bits : BitString (width k s b)) (raw : RawResult k Q)
    (h : NativeDecode.parse e (b, List.ofFn bits) = some raw) :
    NativeEncode.valid (b, true, raw) = true := by
  simp only [NativeDecode.parse, NeZero.ne b, List.length_ofFn, ne_eq,
    not_true_eq_false, or_self, ↓reduceIte] at h
  split at h
  · have hr := Option.some.inj h
    subst raw
    apply List.all_eq_true.mpr
    intro flag hflag
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hflag
    exact decide_eq_true (NativeDecode.length_payload_cells e b bits i)
  · contradiction

omit [Finite Q] in
/-- The native canonical-code guard is exactly the one used by the functional tree gate.
Unused field words become FAIL even though the underlying semantic decoder supplies defaults. -/
theorem parse_ofFn (e : Q ≃ Fin s) (b : ℕ) [NeZero b]
    (bits : BitString (width k s b)) :
    (parse e (b, List.ofFn bits)).map (RawResult.toView b) =
      decodeChecked (encode e) (decode e) bits := by
  have hdecoded := NativeDecode.parse_ofFn e b bits
  cases hp : NativeDecode.parse (k := k) e (b, List.ofFn bits) with
  | none =>
    have hd : decode e bits = none := by
      simpa only [hp, Option.map_none] using hdecoded.symm
    simp [parse, hp, decodeChecked, hd]
  | some raw =>
    have hd : decode e bits = some (raw.toView b) := by
      simpa only [hp, Option.map_some] using hdecoded.symm
    have hv := valid_of_parse_some e b bits raw hp
    have hs := NativeEncode.serialize_some e raw hv
    have heq : (NativeEncode.serialize e (b, true, raw) = List.ofFn bits) ↔
        ∀ i, encode e (some (raw.toView b)) i = bits i := by
      rw [hs, List.ofFn_inj]
      exact funext_iff
    simp only [parse, hp, Option.getD_some, decodeChecked, hd]
    by_cases hc : NativeEncode.serialize e (b, true, raw) = List.ofFn bits
    · simp [hc, heq.mp hc]
    · have hx : ¬ ∀ i, encode e (some (raw.toView b)) i = bits i :=
        fun h => hc (heq.mpr h)
      simp [hc, hx]

end Turing.MultiTapePTM.BlockComputation.Encoding.NativeChecked
