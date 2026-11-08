/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Tactic.Realize

set_option linter.privateModule false

/-!
# Method certificates with aliased word-vector encodings

The caller uses literal vector encodings, while the local method certificate retains its
input and output abbreviations. Method selection must normalize those codomains before
composing the opaque call with a real memory query and result projection.
-/

namespace ComplexityTests.WordRAMRealizeAliases

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

private abbrev Input := Fin 9 → ℕ
private abbrev Metadata := Fin 6 → ℕ

-- The same method certificate with literal vector types already works.
example (method : Input → Memory.Prog Metadata)
    (cert : Realizes .exact method (.refl (Fin 9 → ℕ)) (.refl (Fin 6 → ℕ))
      (fun _ _ _ => True) (fun _ _ => 0)) :
    Realizes .exact (fun d : (Fin 9 → ℕ) × ℕ => do
      let metadata ← method d.1
      let word ← Memory.read d.2
      pure (metadata 5, word))
      (appendWords (.refl (Fin 9 → ℕ)) (WordEncoding.encode (α := ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ)) (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

example (method : Input → Memory.Prog Metadata)
    (cert : Realizes .exact method (.refl Input) (.refl Metadata)
      (fun _ _ _ => True) (fun _ _ => 0)) :
    Realizes .exact (fun d : (Fin 9 → ℕ) × ℕ => do
      let metadata ← method d.1
      let word ← Memory.read d.2
      pure (metadata 5, word))
      (appendWords (.refl (Fin 9 → ℕ)) (WordEncoding.encode (α := ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ)) (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

private abbrev Empty := Fin 0 → ℕ

-- Empty method inputs and outputs still compose; no dummy live word is required.
example (method : Empty → Memory.Prog Empty)
    (cert : Realizes .exact method (.refl Empty) (.refl Empty)
      (fun _ _ _ => True) (fun _ _ => 0)) :
    Realizes .exact (fun d : Fin 0 → ℕ => do
      let _ ← method d
      pure ()) (.refl (Fin 0 → ℕ))
      (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

end ComplexityTests.WordRAMRealizeAliases
