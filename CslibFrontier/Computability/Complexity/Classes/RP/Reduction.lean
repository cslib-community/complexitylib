/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ZPP
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Complexity.Classes.TruncatedVerifier
import CslibFrontier.Foundations.Data.BitString.List

/-!
# RP, coRP and ZPP are closed under polynomial-time reductions

If `A` reduces to `B` in polynomial time and `B` is in `RP`, then so is `A`
(`Cslib.Complexity.PolyTimeReducible.mem_RP`). The verifier of `A` runs the verifier of `B` on the
reduced instance and on the prefix of a polynomially long random string that it expects
(`Cslib.Complexity.exists_truncated_verifier`). Every prefix is extended by the same number of
strings, so on members at least half of the random strings are still accepted, and on non-members
none is. Closure of `coRP` follows by complementing the reduction, and closure of `ZPP` from
`ZPP = RP ∩ coRP` (`Cslib.Complexity.ZPP_eq_RP_inter_coRP`).

## Main results

* `Cslib.Complexity.PolyTimeReducible.mem_RP`, `Cslib.Complexity.PolyTimeReducible.mem_coRP`,
  `Cslib.Complexity.PolyTimeReducible.mem_ZPP`: `RP`, `coRP` and `ZPP` are closed under
  polynomial-time reductions.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}

/-- **`RP` is closed under polynomial-time reductions.** The verifier of `A` runs the verifier of
`B` on the reduced instance and on the prefix of the random string that this verifier expects. -/
theorem PolyTimeReducible.mem_RP (h : PolyTimeReducible enc encB A B) (hB : B ∈ RP encB) :
    A ∈ RP enc := by
  obtain ⟨f, hf, hAB⟩ := h
  obtain ⟨q, W, hW, hWB⟩ := hB
  obtain ⟨P, V, hV, hle, hVW⟩ := exists_truncated_verifier hf q hW
  refine ⟨P, V, hV, fun a => ⟨fun ha => ?_, fun ha r => ?_⟩⟩
  · have hyes : 2 ^ q.eval (encB (f a)).length ≤
        2 * acceptCount W (f a) (q.eval (encB (f a)).length) := (hWB (f a)).1 ((hAB a).1 ha)
    have hacc : 2 ^ P.eval (enc a).length ≤ 2 * acceptCount V a (P.eval (enc a).length) := by
      rw [acceptCount_eq_two_pow_mul_of_take (hle a) (hVW a), ← pow_sub_mul_pow 2 (hle a),
        mul_left_comm]
      exact Nat.mul_le_mul_left _ hyes
    exact hacc
  · rw [hVW]
    exact (BitString.forall_take_ofFn_iff (hle a) (g := fun w => W (f a, w) = false)).2
      ((hWB (f a)).2 fun hb => ha ((hAB a).2 hb)) r

/-- **`coRP` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_coRP (h : PolyTimeReducible enc encB A B) (hB : B ∈ coRP encB) :
    A ∈ coRP enc :=
  h.mem_compl PolyTimeReducible.mem_RP hB

/-- **`ZPP` is closed under polynomial-time reductions**, since `ZPP = RP ∩ coRP`. -/
theorem PolyTimeReducible.mem_ZPP (h : PolyTimeReducible enc encB A B) (hB : B ∈ ZPP encB) :
    A ∈ ZPP enc := by
  rw [ZPP_eq_RP_inter_coRP] at hB ⊢
  exact ⟨h.mem_RP hB.1, h.mem_coRP hB.2⟩

end Cslib.Complexity
