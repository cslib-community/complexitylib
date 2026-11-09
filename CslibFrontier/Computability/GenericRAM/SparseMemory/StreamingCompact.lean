/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.SparseMemory.CompactTuring
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamingFilter
import all CslibFrontier.Computability.GenericRAM.SparseMemory.CompactTuring
import all CslibFrontier.Computability.GenericRAM.SparseMemory.Turing
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Streaming default deletion

An alternative real machine computes exactly `compact`, retaining the explicit
default and one binding while emitting surviving frames. Its time is linear in
the number of stored bindings times a polynomial in the maximum binding/default
wire, rather than cubic in the whole store. Peak workspace charges the complete
input/output plus a polynomial per-binding budget. No bound on live support is
silently used to bound the input or the filter's internal workspace.

The older cubic machine and its consumers remain unchanged. This component alone
does not make association-list accesses or the uniform interpreter efficient.
-/

public section
namespace Cslib.GenericRAM.SparseMemory
open Turing.MultiTapeTM

variable {Address Value : Type} [DecidableEq Value]

/-- The width of the actual default and largest stored binding, including an empty-input unit. -/
def compactRecordWidth (encA : Address ↪ List Bool) (encV : Value ↪ List Bool)
    (input : Value × SparseMemory Address Value) : ℕ :=
  let (default, memory) := input
  streamFilterWidth encV (encPair encA encV) (default, entries memory)

/-- A real streaming implementation of precisely the existing compaction operation. Both its
per-binding polynomial and multitape machine are uniform over all runtime default/store inputs. -/
theorem compact_streaming (encA : Address ↪ List Bool) (encV : Value ↪ List Bool) :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ComputableInO (fun input : Value × SparseMemory Address Value =>
        compact input.1 input.2) (compactEncoding encA encV) (encoding encA encV)
        (fun input => 2 * (compactEncoding encA encV input).length +
          ((entries input.2).length + 1) * P (compactRecordWidth encA encV input))
        (fun input => 2 * (compactEncoding encA encV input).length +
          P (compactRecordWidth encA encV input)) := by
  have value := (ComputableTidilyInPolyTime.snd encA encV).comp
    (ComputableTidilyInPolyTime.snd encV (encPair encA encV))
  have default := ComputableTidilyInPolyTime.fst encV (encPair encA encV)
  obtain ⟨P, hP, hmP, h⟩ := ComputableInO.filter_stream
    (ComputableInPolyTime.of_tidy (value.decide_ne default))
  have unpack : ComputableInO (fun input : Value × SparseMemory Address Value =>
      (input.1, entries input.2)) (compactEncoding encA encV)
      (encPair encV (encList (encPair encA encV)))
      (fun input => (compactEncoding encA encV input).length)
      (fun input => (compactEncoding encA encV input).length) := .of_eq (fun _ => rfl)
  refine ⟨P, hP, hmP, ?_⟩
  have hc := (h.comp unpack).of_enc_eq
    (g := fun input : Value × SparseMemory Address Value => compact input.1 input.2)
    (encC := encoding encA encV) (fun input => by
      simp only [Function.comp_def, encoding_apply, entries_compact])
  convert hc using 1 <;>
    (funext input; simp only [compactRecordWidth, compactEncoding, length_encPair,
      encoding_apply]; omega)

end Cslib.GenericRAM.SparseMemory
