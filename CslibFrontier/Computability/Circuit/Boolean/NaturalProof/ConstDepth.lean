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

The converse holds when `ConstDepth I` is nonempty (`NaturalProof.IsUseful.eventually_constDepth`):
the circuits of any language in the class supply a function at every input length, so the
patching argument of `NaturalProof.IsUseful.eventually_forall_not` applies. The hypothesis is
needed: over a basis that cannot produce an output on zero inputs, `ConstDepth I` is empty, so
every property is useful against it, while projections still compute members of `C n`. This
converse is the form in which the abstract
[Carmosino et al., Theorem 5.1][CarmosinoImpagliazzoKabanetsKolokolova2016] uses usefulness
against a constant-depth class; that theorem stays open under
[#798](https://github.com/cslib-community/cslib-frontier/issues/798).

## Main results

* `Cslib.Circuits.Boolean.NaturalProof.IsUseful.of_eventually_constDepth`: usefulness against
  `ConstDepth I` from eventual size–depth lower bounds.
* `Cslib.Circuits.Boolean.NaturalProof.IsUseful.eventually_constDepth`: the converse, when
  `ConstDepth I` is nonempty.

## References

* [A. A. Razborov, S. Rudich, *Natural proofs*][RazborovRudich1997]
* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
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

/-- **Usefulness against a nonempty constant-depth class gives lower bounds**: if `C` is useful
against `ConstDepth I` and the class contains a language, then for every depth `d` and polynomially
bounded size `s`, eventually no circuit of depth at most `d` and at most `s n` gates computes a
member of `C n`. A language of the class, of depth `d₀` and size `s₀`, supplies at every length a
function computed within depth `max d d₀` and size `s n + s₀ n`, so
`IsUseful.eventually_forall_not` applies to those functions. -/
theorem IsUseful.eventually_constDepth (hC : IsUseful (ConstDepth I) C)
    (hne : (ConstDepth I).Nonempty) (d : ℕ) (s : ℕ → ℕ) (hs : PolynomiallyBounded s) :
    ∀ᶠ n in atTop, ∀ (Cn : Circuit σ n 1), Cn.depth ≤ d → Cn.size ≤ s n →
      ∀ f ∈ C n, ¬ Cn.Computes I (single f) := by
  obtain ⟨L₀, hL₀⟩ := hne
  obtain ⟨d₀, s₀, hs₀, hC₀⟩ := ConstDepth.mem_iff.1 hL₀
  filter_upwards [hC.eventually_forall_not
    (P := fun n f => ∃ Cn : Circuit σ n 1, Cn.Computes I (single f) ∧ Cn.depth ≤ max d d₀ ∧
      Cn.size ≤ s n + s₀ n)
    (fun g hg => ConstDepth.mem_iff.2 ⟨max d d₀, fun n => s n + s₀ n, hs.add hs₀, fun n => by
      rw [Language.slice_ofSlices]; exact hg n⟩)
    fun n => by
      obtain ⟨C₀, hc, hd, hsz⟩ := hC₀ n
      exact ⟨L₀.slice n, C₀, hc, hd.trans (le_max_right _ _), hsz.trans (Nat.le_add_left _ _)⟩]
    with n hn Cn hd hsz f hf hc
  exact hn f hf ⟨Cn, hc, hd.trans (le_max_left _ _), hsz.trans (Nat.le_add_right _ _)⟩

end Cslib.Circuits.Boolean.NaturalProof
