/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
public import CslibFrontier.Logics.FirstOrder.Ordered.Query
import CslibFrontier.Logics.FirstOrder.Encoding.PowerBound

/-!
# Polynomial-time ordered queries run within one power of the universe size

The converse directions of the Immerman–Vardi and Grädel theorems simulate a native machine
deciding an ordered query on the power universe `Fin (n ^ k)`. This file supplies the machine and
the tuple width `k` once: one finite-state machine decides the query by step `n ^ k - 1` on every
structure of size `n`, and `n ^ k` exceeds the encoding length and any fixed number of finite
feature tags.

## Main results

* `Cslib.Logic.FO.Ordered.exists_tm_of_encodedLanguage_mem_P`: a query whose encoded language is
  in `P` is decided by one machine within `n ^ k - 1` steps, where `n ^ k` bounds the encoding
  length and a given number of tags.
-/

public section

open FirstOrder Language Turing Turing.MultiTapeTM Cslib.Complexity

namespace Cslib.Logic.FO.Ordered

/-- **The machine of a polynomial-time ordered query.** If the encoded language of `K` is in `P`,
one finite-state machine `tm` decides `K`: for every number `tags` there is a tuple width `k ≥ 1`
bounding all arities of `v` such that `n ^ k` exceeds the encoding length plus one and is at least
`tags` on every well-formed input of size `n ≥ 2`, and `tm` has halted with output `[true]` by step
`M.size ^ k - 1` exactly on the structures `M ∈ K`. -/
theorem exists_tm_of_encodedLanguage_mem_P {L : Language} [L.IsRelational] (v : Vocabulary L)
    {K : Query L} (hK : K.encodedLanguage v ∈ P encStructure) :
    ∃ (m : ℕ) (State : Type) (_ : Fintype State) (tm : MultiTapeTM m Bool State),
      ∀ tags : ℕ, ∃ k : ℕ, 1 ≤ k ∧ (∀ i : Fin v.count, v.arity i ≤ k) ∧
        (∀ a : EncodedStructure, v.WellFormed a → 2 ≤ a.1 →
          (encStructure a).length + 1 < a.1 ^ k ∧ tags ≤ a.1 ^ k) ∧
        ∀ M : Structure L, M ∈ K ↔
          (tm.runFrom (tm.initCfg (encStructure (encode v M))) (M.size ^ k - 1)).Halted ∧
          (tm.runFrom (tm.initCfg (encStructure (encode v M))) (M.size ^ k - 1)).output =
            [true] := by
  obtain ⟨f, ⟨t, _, ht, _, m, State, _, tm, htm⟩, hdec⟩ := hK
  refine ⟨m, State, Fintype.ofFinite State, tm, fun tags => ?_⟩
  obtain ⟨k, hk, har, hpow⟩ := v.exists_pow_bound (fun n => n + 1 + t n + tags) (by fun_prop)
  refine ⟨k, hk, har, fun a ha h2 => ?_, fun M => ?_⟩
  · have := hpow a ha h2
    omega
  · have hb : (encStructure (encode v M)).length + 1 + t (encStructure (encode v M)).length +
        tags < M.size ^ k :=
      hpow _ (v.wellFormed_encode M (Equiv.refl M)) M.size_ge_two
    obtain ⟨hhalt, hout⟩ := (htm (encode v M)).runFrom_of_le
      (show t (encStructure (encode v M)).length ≤ M.size ^ k - 1 by omega)
    rw [← mem_encodedLanguage_encode v K M, hdec, hout, encBool_apply, List.singleton_inj]
    exact ⟨fun hf => ⟨hhalt, hf⟩, And.right⟩

end Cslib.Logic.FO.Ordered
