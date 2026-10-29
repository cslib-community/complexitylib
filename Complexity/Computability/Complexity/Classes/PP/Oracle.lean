/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PP
public import Complexity.Computability.Complexity.Classes.SharpP.Oracle
import Complexity.Computability.Complexity.Classes.Oracle.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Majority relative to a language oracle

`PPWithOracle A enc` uses the existing fixed-length strict-majority condition with a deterministic
oracle verifier certified by `ComputableInPolyTimeWithOracle`. Its resource bound applies to
arbitrary stateful replies; the accepted witnesses are counted against `languageOracle A`.
Exact ties reject, including the selector construction in the positive-GapP characterization.

To compare two relativized counts, pad both verifiers with false tails to the sum of their
certificate lengths. One additional bit selects the first verifier or the complement of the
second; more than half accept exactly when the first count is larger. This proof uses the
existing counting identities, and assumes no relativized counting-closure theorem.

These are verifier classes. Equivalence with probabilistic oracle machines is separate.
AWPP lowness for this oracle-verifier model is proved in
`Complexity/Computability/Complexity/Classes/AWPP/Lowness.lean`.

## Main definitions

* `Cslib.Complexity.PPWithOracle`: strict majority of fixed-length oracle-verifier witnesses.

## Main results

* `Cslib.Complexity.mem_PPWithOracle_iff_exists_GapPWithOracle`: positive-gap characterization.
* `Cslib.Complexity.PP_subset_PPWithOracle`: ordinary PP ignores the oracle.
* `Cslib.Complexity.PPWithOracle_eq_PP`: a polynomial-time oracle adds no PP languages.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994].
* [L. Fortnow, *Counting Complexity*][Fortnow1997], Classification 4.3.
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 3.4.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set (List Bool)}

/-- Strict majority on exactly polynomially many witness bits, with a deterministic verifier
relative to the fixed language oracle. Its program has a strict certificate
for arbitrary replies. -/
def PPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTimeWithOracle A V (encPair enc encBits) encBool ∧
      DecidesByMajority enc p V L}

/-- An ordinary PP verifier can ignore every oracle. -/
theorem PP_subset_PPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    PP enc ⊆ PPWithOracle A enc := fun _ ⟨p, V, hV, hL⟩ =>
  ⟨p, V, hV.computableInPolyTimeWithOracle A, hL⟩

/-- A polynomial-time oracle adds no PP languages. -/
theorem PPWithOracle_eq_PP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    PPWithOracle A enc = PP enc :=
  Set.Subset.antisymm (fun _ ⟨p, V, hV, hL⟩ =>
    ⟨p, V, hV.computableInPolyTime hA, hL⟩) (PP_subset_PPWithOracle A enc)

/-- Relativized PP is exactly positivity of a relativized gap function. For the reverse direction,
two counts are padded to a common certificate length and selected with one extra bit. -/
theorem mem_PPWithOracle_iff_exists_GapPWithOracle {L : Set α} :
    L ∈ PPWithOracle A enc ↔ ∃ g ∈ GapPWithOracle A enc, ∀ a, a ∈ L ↔ 0 < g a := by
  constructor
  · rintro ⟨p, V, hV, hL⟩
    let f₁ a := acceptCount V a (p.eval (enc a).length)
    let f₂ a := acceptCount (fun x => !V x) a (p.eval (enc a).length)
    refine ⟨fun a => (f₁ a : ℤ) - f₂ a,
      ⟨f₁, ⟨p, V, hV, fun _ => rfl⟩,
        f₂, ⟨p, _, hV.map (ComputableInPolyTime.bool_not), fun _ => rfl⟩,
        fun _ => rfl⟩, fun a => ?_⟩
    have htotal := acceptCount_add_acceptCount_not V a (p.eval (enc a).length)
    rw [hL a]
    dsimp only [f₁, f₂]
    lia
  · rintro ⟨g, ⟨f₁, ⟨p, V₁, h₁, hf₁⟩, f₂, ⟨q, V₂, h₂, hf₂⟩, hg⟩, hL⟩
    let W₁ := andVerifier (fun a => p.eval (enc a).length) V₁ allFalseVerifier
    let W₂ := andVerifier (fun a => q.eval (enc a).length) V₂ allFalseVerifier
    have hfalse : ComputableInPolyTimeWithOracle A (allFalseVerifier (α := α))
        (encPair enc encBits) encBool :=
      computableInPolyTime_allFalseVerifier.computableInPolyTimeWithOracle A
    have hW₁ : ComputableInPolyTimeWithOracle A W₁ (encPair enc encBits) encBool :=
      computableInPolyTimeWithOracle_andVerifier (by fun_prop) h₁ hfalse
    have hW₂ : ComputableInPolyTimeWithOracle A W₂ (encPair enc encBits) encBool :=
      computableInPolyTimeWithOracle_andVerifier (by fun_prop) h₂ hfalse
    refine ⟨p + q + 1, selectVerifier W₁ (fun x => !W₂ x),
      computableInPolyTimeWithOracle_selectVerifier hW₁
        (hW₂.map (ComputableInPolyTime.bool_not)), fun a => ?_⟩
    have hc₁ : acceptCount W₁ a ((p + q).eval (enc a).length) = f₁ a := by
      simpa only [W₁, Polynomial.eval_add, hf₁ a] using
        acceptCount_andVerifier_allFalseVerifier (fun a => p.eval (enc a).length)
          V₁ a (q.eval (enc a).length)
    have hc₂ : acceptCount W₂ a ((p + q).eval (enc a).length) = f₂ a := by
      simpa only [W₂, Polynomial.eval_add, Nat.add_comm, hf₂ a] using
        acceptCount_andVerifier_allFalseVerifier (fun a => q.eval (enc a).length)
          V₂ a (p.eval (enc a).length)
    have htotal := acceptCount_add_acceptCount_not W₂ a ((p + q).eval (enc a).length)
    rw [hc₂] at htotal
    rw [hL a, hg a, Polynomial.eval_add, Polynomial.eval_one,
      acceptCount_selectVerifier, hc₁, pow_succ]
    lia

end Cslib.Complexity
