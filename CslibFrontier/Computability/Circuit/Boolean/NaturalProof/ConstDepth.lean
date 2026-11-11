/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ConstDepth
public import CslibFrontier.Computability.Circuit.Boolean.NaturalProof

/-!
# Usefulness against constant-depth classes

A property `C` is useful against the constant-depth class `ConstDepth I` once, for every depth
bound `d` and polynomial size bound `s`, eventually no circuit over `I` of depth at most `d` and
size at most `s n` computes a member of `C n` (`NaturalProof.IsUseful.of_eventually_constDepth`).
This is how lower bounds such as Razborov's against AC⁰[2] give usefulness.

Only this direction is provided. The converse needs a hypothesis: over a basis that cannot produce
an output on zero inputs, `ConstDepth I` is empty, so every property is useful against it, while
projections still compute members of `C n`. The converse is deferred to milestone M6.8b of
[#4451](https://github.com/cslib-community/cslib-frontier/issues/4451), its first consumer.

## Main results

* `Cslib.Circuits.Boolean.NaturalProof.IsUseful.of_eventually_constDepth`: usefulness against
  `ConstDepth I` from eventual size–depth lower bounds.

## References

* [A. A. Razborov, S. Rudich, *Natural proofs*][RazborovRudich1997]
-/

public section

namespace Cslib.Circuits.Boolean.NaturalProof

open Filter

variable {σ : Signature} {I : Interpretation σ Bool} {C : ∀ n, Set (BooleanFunction n)}

/-- **Usefulness against a constant-depth class** [RazborovRudich1997]: if for every depth `d`
and polynomially bounded size `s`, eventually no circuit of depth at most `d` and at most `s n`
gates computes a member of `C n`, then `C` is useful against `ConstDepth I`. -/
theorem IsUseful.of_eventually_constDepth
    (h : ∀ (d : ℕ) (s : ℕ → ℕ), PolynomiallyBounded s → ∀ᶠ n in atTop,
      ∀ (Cn : Circuit σ n 1), Cn.depth ≤ d → Cn.size ≤ s n →
        ∀ f ∈ C n, ¬ Cn.Computes I (single f)) :
    IsUseful (ConstDepth I) C := by
  intro L hL
  obtain ⟨d, s, hs, hC⟩ := ConstDepth.mem_iff.1 hL
  filter_upwards [h d s hs] with n hn hmem
  obtain ⟨Cn, hCc, hCd, hCs⟩ := hC n
  exact hn Cn hCd hCs _ hmem hCc

end Cslib.Circuits.Boolean.NaturalProof
