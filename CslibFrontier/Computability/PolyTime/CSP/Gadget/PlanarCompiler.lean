/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Gadget.CertifiedRotation
public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.Genus

/-!
# Total certified planar gadget compilation

Actual checked gadget witnesses determine every free and auxiliary block internally.
On accepted source inputs the compiler emits exactly `replaceGadgets` and the computed
replacement certificate, which passes the full original ordered numerical checker.
On malformed source data it emits the empty body and invalid certificate `[0]`.

The all-raw semantic equivalence includes well-formedness and actual checker acceptance.
Only the fixed source alphabet must be finite for native polynomial time. Static gadget
witnesses and their boundary preprocessing may be noncomputable; the executed function is
the existing finite-lookup compiler, with binary names and certificate entries as data.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Turing.MultiTapeTM

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- Run the existing total compiler with blocks derived from actual checked gadgets.
The bound is fixed independently of the input; its correctness is used only in proofs. -/
@[expose] noncomputable def compileGadgets
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) :
    CSP Src ℕ × Graph.RotationCertificate → CSP Rel ℕ × Graph.RotationCertificate :=
  compile srcArity B (fun r => (gadgets r).template)
    (fun r => freeBoundaryBlocks (gadgets r) (witnesses r))
    (fun r => auxiliaryBoundaryBlocks (gadgets r) (witnesses r))

/-- Both branches have the original target arities, including the empty reject branch. -/
theorem wellFormed_compileGadgets
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (p : CSP Src ℕ × Graph.RotationCertificate) :
    WellFormed arity (compileGadgets gadgets witnesses B p).1 :=
  wellFormed_compile arity srcArity B _ (fun r => (gadgets r).wellFormed_template) _ _ p

/-- Actual target checker acceptance is exactly the executed source guard, on every raw
input. In particular a malformed source never receives a positive target certificate. -/
theorem verifyRotationCertificate_compileGadgets_iff
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B)
    (p : CSP Src ℕ × Graph.RotationCertificate) :
    verifyRotationCertificate (compileGadgets gadgets witnesses B p).1
      (compileGadgets gadgets witnesses B p).2 = true ↔ sourceGuard srcArity p = true := by
  cases hg : sourceGuard srcArity p
  · have h := verifyRotationCertificate_compile_of_sourceGuard_false srcArity B
      (fun r => (gadgets r).template)
      (fun r => freeBoundaryBlocks (gadgets r) (witnesses r))
      (fun r => auxiliaryBoundaryBlocks (gadgets r) (witnesses r)) p hg
    simp only [compileGadgets, h, Bool.false_eq_true]
  · obtain ⟨hF, hc⟩ := (sourceGuard_eq_true_iff srcArity p).mp hg
    have ht := verifyRotationCertificate_replacementCertificate
      gadgets witnesses B hB p.1 hF p.2 hc
    simp only [compileGadgets, compile, hg, ite_true, ht]

/-- Complete guarded satisfiability equivalence on all raw inputs, including malformed
scopes, malformed certificates, empty alphabets and nullary or closed components. -/
theorem wellFormed_certifiedSatisfiable_compileGadgets_iff
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B)
    (p : CSP Src ℕ × Graph.RotationCertificate) :
    (WellFormed arity (compileGadgets gadgets witnesses B p).1 ∧
      verifyRotationCertificate (compileGadgets gadgets witnesses B p).1
        (compileGadgets gadgets witnesses B p).2 = true ∧
      (compileGadgets gadgets witnesses B p).1.Satisfiable sem) ↔
      WellFormed srcArity p.1 ∧ verifyRotationCertificate p.1 p.2 = true ∧
        p.1.Satisfiable srcSem := by
  rw [verifyRotationCertificate_compileGadgets_iff gadgets witnesses B hB p]
  have hw := wellFormed_compileGadgets gadgets witnesses B p
  simp only [hw, true_and]
  cases hg : sourceGuard srcArity p
  · have hn : ¬ (WellFormed srcArity p.1 ∧ verifyRotationCertificate p.1 p.2 = true) := by
      rw [← sourceGuard_eq_true_iff, hg]
      exact Bool.false_ne_true
    simp only [Bool.false_eq_true, false_and, false_iff, ← and_assoc]
    exact fun h => hn h.1
  · obtain ⟨hF, hc⟩ := (sourceGuard_eq_true_iff srcArity p).mp hg
    simp only [true_and, hF, hc, compileGadgets, compile, hg, ite_true]
    exact satisfiable_replaceGadgets_iff gadgets B hB p.1 hF

/-- Ordinary native polynomial time for the actual checked family on every binary/framed
input. The source alphabet alone is finite; no input-validity premise funds a clock. -/
theorem computableInPolyTime_compileGadgets [Finite Src]
    (encSrc : Src ↪ List Bool) (encRel : Rel ↪ List Bool)
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) :
    ComputableInPolyTime (compileGadgets gadgets witnesses B)
      (encCSPRotationCertificate encSrc encNat) (encCSPRotationCertificate encRel encNat) :=
  computableInPolyTime_compile encSrc encRel srcArity B _ _ _

/-- Complete framed output length, including binary target names, symbols, list framing and
certificate entries, is polynomially bounded on every raw input. -/
theorem exists_framed_bound_compileGadgets [Finite Src]
    (encSrc : Src ↪ List Bool) (encRel : Rel ↪ List Bool)
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) :
    ∃ c d : ℕ, ∀ p : CSP Src ℕ × Graph.RotationCertificate,
      (encCSPRotationCertificate encRel encNat (compileGadgets gadgets witnesses B p)).length ≤
        c * ((encCSPRotationCertificate encSrc encNat p).length + 1) ^ d :=
  (computableInPolyTime_compileGadgets encSrc encRel gadgets witnesses B)
    |>.polyBounded_length.exists_le

end Cslib.Complexity.CSP.GadgetRotation
