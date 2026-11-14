/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Gadget.Rotation
import CslibFrontier.Computability.PolyTime.CSP.Gadget

/-!
# Total guarded instance-and-rotation compilation

The valid branch executes the existing PP replacement and positional table construction.
The invalid branch emits the empty target body and the invalid one-entry certificate `[0]`.
Thus rejection remains possible even for an empty target alphabet: the certificate guard,
rather than a target relation or unguarded satisfiability, rejects malformed source data.

The complete framed input and output use binary variable names and successor entries.
Native polynomial time holds on all raw inputs for a fixed finite source alphabet, with
no finiteness requirement on the target alphabet. The static templates and local words
are fixed lookup data; their construction is not part of this uniform runtime claim.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM

variable {Src Rel : Type}

/-- Exact source scopes and the supplied original ordered rotation must both pass. -/
@[expose] def sourceGuard (srcArity : Src → ℕ)
    (p : CSP Src ℕ × Graph.RotationCertificate) : Bool :=
  validArity srcArity p.1 && verifyRotationCertificate p.1 p.2

/-- Compile the literal replacement body and deterministic successor table on accepted
source inputs; otherwise return an empty body with an invalid certificate. -/
@[expose] def compile (srcArity : Src → ℕ) (B : ℕ)
    (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks auxiliaryBlocks : Src → List (List ℕ))
    (p : CSP Src ℕ × Graph.RotationCertificate) : CSP Rel ℕ × Graph.RotationCertificate :=
  if sourceGuard srcArity p then
    (replaceGadgets B templates p.1,
      replacementCertificate B templates freeBlocks auxiliaryBlocks p.1 p.2)
  else ([], ⟨[0]⟩)

/-- The executed source guard is exactly source well-formedness and checker acceptance. -/
theorem sourceGuard_eq_true_iff (srcArity : Src → ℕ)
    (p : CSP Src ℕ × Graph.RotationCertificate) :
    sourceGuard srcArity p = true ↔
      WellFormed srcArity p.1 ∧ verifyRotationCertificate p.1 p.2 = true := by
  simp only [sourceGuard, Bool.and_eq_true, validArity_eq_true_iff]

/-- The rejecting certificate has the wrong length for an empty body, for every alphabet. -/
theorem verifyRotationCertificate_empty_invalid :
    verifyRotationCertificate ([] : CSP Rel ℕ) ⟨[0]⟩ = false := rfl

/-- Malformed source bodies or certificates take the same explicit rejection branch. -/
theorem compile_of_sourceGuard_false (srcArity : Src → ℕ) (B : ℕ)
    (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks auxiliaryBlocks : Src → List (List ℕ))
    (p : CSP Src ℕ × Graph.RotationCertificate) (hg : sourceGuard srcArity p = false) :
    compile srcArity B templates freeBlocks auxiliaryBlocks p = ([], ⟨[0]⟩) := by
  simp [compile, hg]

/-- The full target checker rejects every malformed-source branch, including an empty
target alphabet, although its empty output body is satisfiable. -/
theorem verifyRotationCertificate_compile_of_sourceGuard_false (srcArity : Src → ℕ) (B : ℕ)
    (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks auxiliaryBlocks : Src → List (List ℕ))
    (p : CSP Src ℕ × Graph.RotationCertificate) (hg : sourceGuard srcArity p = false) :
    verifyRotationCertificate (compile srcArity B templates freeBlocks auxiliaryBlocks p).1
      (compile srcArity B templates freeBlocks auxiliaryBlocks p).2 = false := by
  rw [compile_of_sourceGuard_false srcArity B templates freeBlocks auxiliaryBlocks p hg]
  exact verifyRotationCertificate_empty_invalid

/-- Certified gadgets give exact target arities on both branches; the reject body is empty. -/
theorem wellFormed_compile (arity : Rel → ℕ) (srcArity : Src → ℕ) (B : ℕ)
    (templates : Src → CSP Rel (Bool × ℕ)) (ht : ∀ r, WellFormed arity (templates r))
    (freeBlocks auxiliaryBlocks : Src → List (List ℕ))
    (p : CSP Src ℕ × Graph.RotationCertificate) :
    WellFormed arity (compile srcArity B templates freeBlocks auxiliaryBlocks p).1 := by
  unfold compile
  split
  · exact wellFormed_replaceGadgets B templates ht p.1
  · simp [WellFormed]

/-- Native polynomial time on every raw binary/framed input, with only the fixed source
alphabet finite. All encoded target symbols remain data produced by fixed lookup. -/
theorem computableInPolyTime_compile [Finite Src]
    (encSrc : Src ↪ List Bool) (encRel : Rel ↪ List Bool) (srcArity : Src → ℕ) (B : ℕ)
    (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks auxiliaryBlocks : Src → List (List ℕ)) :
    ComputableInPolyTime (compile srcArity B templates freeBlocks auxiliaryBlocks)
      (encCSPRotationCertificate encSrc encNat) (encCSPRotationCertificate encRel encNat) := by
  have hguard : ComputableInPolyTime (sourceGuard srcArity)
      (encCSPRotationCertificate encSrc encNat) encBool := by
    have hv := (computableInPolyTime_validArity encSrc srcArity).comp
      (ComputableInPolyTime.fst (encCSP encSrc encNat) Graph.encRotationCertificate)
    have hc := computableInPolyTime_verifyRotationCertificate encSrc encNat
    unfold sourceGuard
    fun_prop
  have hb := (computableInPolyTime_replaceGadgets encSrc encRel B templates).comp
    (ComputableInPolyTime.fst (encCSP encSrc encNat) Graph.encRotationCertificate)
  have hc := computableInPolyTime_replacementCertificate encSrc encRel B templates
    freeBlocks auxiliaryBlocks
  exact hguard.ite (hb.prod hc)
    (ComputableInPolyTime.const ([], (⟨[0]⟩ : Graph.RotationCertificate)))

/-- The complete output, including list framing and binary certificate entries, is
polynomially bounded on all raw inputs. -/
theorem exists_framed_bound_compile [Finite Src]
    (encSrc : Src ↪ List Bool) (encRel : Rel ↪ List Bool) (srcArity : Src → ℕ) (B : ℕ)
    (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks auxiliaryBlocks : Src → List (List ℕ)) :
    ∃ c d : ℕ, ∀ p : CSP Src ℕ × Graph.RotationCertificate,
      (encCSPRotationCertificate encRel encNat
        (compile srcArity B templates freeBlocks auxiliaryBlocks p)).length ≤
      c * ((encCSPRotationCertificate encSrc encNat p).length + 1) ^ d :=
  (computableInPolyTime_compile encSrc encRel srcArity B templates freeBlocks auxiliaryBlocks)
    |>.polyBounded_length.exists_le

end Cslib.Complexity.CSP.GadgetRotation
