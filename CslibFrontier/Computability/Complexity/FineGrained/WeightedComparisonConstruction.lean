/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.WeightedComparison.WithBase
public import CslibFrontier.Computability.PolyTime.CNF.WeightedComparison.Signed
public import CslibFrontier.Computability.GenericRAM.Native.Certificate

/-!
# Whole-generator polynomial time and peak workspace

The certificates concern the complete actual original-input programs, including signed
normalization, correlated-family generation, gate-list/CNF writes, output framing and existing
DNF-instance augmentation. They are extracted from the proved binary machine implementations,
not from the independent gate-count or output-volume bounds. Source: [ChenJiangZhu2027],
Lemma A.1 / Corollary A.2 (PDF pp.28–29).

## Main results

* `exists_signed_generator_resources`: whole signed writer time and peak workspace.
* `exists_family_generator_resources`: whole fixed-family writer resources.
* `exists_augmented_generator_resources`: whole original-instance augmentation resources.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedSum

open Turing.MultiTapeTM Cslib.GenericRAM

/-- Complete signed original-input normalization and comparison writing have polynomial time and
peak workspace, uniformly over all raw binary frames and target magnitudes. -/
theorem exists_signed_generator_resources (op : Comparison) (c : ℕ) :
    ∃ cs : NativeCertificate (SignedFrontend.build op c) SignedFrontend.encInput
      Logic.PL.VCOne.encSignedCNF, ∃ C e : ℕ,
        ∀ x, cs.time x ≤ C * ((SignedFrontend.encInput x).length + 1) ^ e ∧
          cs.space x ≤ C * ((SignedFrontend.encInput x).length + 1) ^ e := by
  obtain ⟨cs, ht, hs⟩ := NativeCertificate.exists_polynomial (SignedFrontend.build_polytime op c)
  obtain ⟨C, e, h⟩ := (ht.add hs).exists_le
  exact ⟨cs, C, e, fun x => ⟨(Nat.le_add_right _ _).trans (h x),
    (Nat.le_add_left _ _).trans (h x)⟩⟩

/-- Every fixed correlated comparison family has a complete original-input generator certificate.
Only family size/modes and c are compiled parameters; coefficients and targets vary at runtime. -/
theorem exists_family_generator_resources {r : ℕ} (op : Fin r → Comparison) (c : ℕ) :
    ∃ cs : NativeCertificate (Family.build op c) Family.encInput Logic.PL.VCOne.encSignedCNF,
      ∃ C e : ℕ, ∀ x, cs.time x ≤ C * ((Family.encInput x).length + 1) ^ e ∧
        cs.space x ≤ C * ((Family.encInput x).length + 1) ^ e := by
  obtain ⟨cs, ht, hs⟩ := NativeCertificate.exists_polynomial (Family.build_polytime op c)
  obtain ⟨C, e, h⟩ := (ht.add hs).exists_le
  exact ⟨cs, C, e, fun x => ⟨(Nat.le_add_right _ _).trans (h x),
    (Nat.le_add_left _ _).trans (h x)⟩⟩

/-- Actual whole original-instance augmentation is polynomial in input bit length, including
computed auxiliary counts, copied original predicates, all gates/clauses and output writing. -/
theorem exists_augmented_generator_resources {r : ℕ} (op : Fin r → Comparison) (c : ℕ) :
    ∃ cs : NativeCertificate (WithBase.build op c) WithBase.encInput
      Logic.PL.TwoBoundary.BinaryFrontend.encInput,
      ∃ C e : ℕ, ∀ x, cs.time x ≤ C * ((WithBase.encInput x).length + 1) ^ e ∧
        cs.space x ≤ C * ((WithBase.encInput x).length + 1) ^ e := by
  obtain ⟨cs, ht, hs⟩ := NativeCertificate.exists_polynomial (WithBase.build_polytime op c)
  obtain ⟨C, e, h⟩ := (ht.add hs).exists_le
  exact ⟨cs, C, e, fun x => ⟨(Nat.le_add_right _ _).trans (h x),
    (Nat.le_add_left _ _).trans (h x)⟩⟩

end Cslib.Circuits.Boolean.WeightedSum
