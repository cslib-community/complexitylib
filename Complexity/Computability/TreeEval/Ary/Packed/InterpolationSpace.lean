/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.Interpolation
public import Complexity.Computability.TreeEval.Reader.Cert.Residue

/-!
# Modular Lagrange basis evaluation within binary argument space

The counter in `basisWeight p s a x` is stored in binary. Every modular accumulator is bounded
by `p+1`, including malformed zero-modulus inputs. Thus the alphabet cardinality `s` contributes
its binary encoding length, rather than `s` cells of work space. The native arithmetic
certificates and bounded-counter iteration implement every multiplication, inverse and factor.

## Main definitions

* `Cslib.TreeEval.Ary.Packed.encBasisArgs`: encode `(p,s,a,x)` in binary.

## Main results

* `Cslib.TreeEval.Ary.Packed.basisWeight_inSpace`: the full scalar basis weight is computable
  in native work space linear in the encoded arguments.

This certifies one interpolation weight, not the full grid sum or a Tree Evaluation machine.
-/

public section

namespace Cslib.TreeEval.Ary.Packed

open Reader Turing MultiTapeTM ComputableInSpace

/-- Binary encoding of four natural parameters, in the order `(p,s,a,x)` for `basisWeight`. -/
abbrev encBasisArgs : ℕ × ℕ × ℕ × ℕ ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat encNat))

/-- A single factor uses only linear space in its four binary arguments `(p,a,j,x)`. -/
theorem basisFactor_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ × ℕ × ℕ => basisFactor q.1 q.2.1 q.2.2.1 q.2.2.2)
      encBasisArgs encNat fun q => (encBasisArgs q).length := by
  have hp := fst encNat (encPair encNat (encPair encNat encNat))
  have htail := snd encNat (encPair encNat (encPair encNat encNat))
  have ha := fst' htail
  have hjx := snd' htail
  have hj := fst' hjx
  have hx := snd' hjx
  have hneg := budget_comp_linear negMod_inSpace (budget_prod hp hj)
  have hnum := budget_comp_linear addMod_inSpace (budget_prod hp (budget_prod hx hneg))
  have hden := budget_comp_linear addMod_inSpace (budget_prod hp (budget_prod ha hneg))
  have hinv := budget_comp_linear unitInv_inSpace (budget_prod hp (budget_natPred hden))
  have hprod := budget_comp_linear mulMod_inSpace (budget_prod hp (budget_prod hnum hinv))
  have hone := budget_natMod (budget_const (encB := encNat) 1 (.refl _)) hp
  exact (budget_ite (budget_natEq hj ha) hone hprod).of_enc_eq fun q => by
    by_cases h : q.2.2.1 = q.2.1 <;> simp [basisFactor, h]

private abbrev encBasisState : (ℕ × ℕ × ℕ) × ℕ × ℕ ↪ List Bool :=
  encPair encNat3 (encPair encNat encNat)

private theorem basisStep_inSpace :
    ComputableInSpace basisStep encBasisState encBasisState fun q => (encBasisState q).length := by
  have hpar := fst encNat3 (encPair encNat encNat)
  have hp := fst' hpar
  have hax := snd' hpar
  have ha := fst' hax
  have hx := snd' hax
  have hja := snd encNat3 (encPair encNat encNat)
  have hj := fst' hja
  have hacc := snd' hja
  have hfac := budget_comp_linear basisFactor_inSpace
    (budget_prod hp (budget_prod ha (budget_prod hj hx)))
  have hmul := budget_comp_linear mulMod_inSpace (budget_prod hp (budget_prod hacc hfac))
  have hnext := budget_ite (budget_natIsZero hp)
    (budget_const (encB := encNat) 0 (.refl _)) hmul
  exact (budget_prod hpar (budget_prod (budget_natSucc hj) hnext)).of_enc_eq fun q => by
    by_cases h : q.1.1 = 0 <;> simp [basisStep, h]

/-- The complete basis weight, including its binary counter, is computed in native work space
linear in the binary encodings of `(p,s,a,x)`. The statement is total: no prime or positivity
hypothesis is needed for the resource certificate. -/
theorem basisWeight_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ × ℕ × ℕ => basisWeight q.1 q.2.1 q.2.2.1 q.2.2.2)
      encBasisArgs encNat fun q => (encBasisArgs q).length := by
  have hp := fst encNat (encPair encNat (encPair encNat encNat))
  have htail := snd encNat (encPair encNat (encPair encNat encNat))
  have hs := fst' htail
  have hax := snd' htail
  have hpar := budget_prod hp hax
  have hone := budget_natMod (budget_const (encB := encNat) 1 (.refl _)) hp
  have hinit := budget_prod hpar
    (budget_prod (budget_const (encB := encNat) 0 (.refl _)) hone)
  have hstates (q : ℕ × ℕ × ℕ × ℕ) (j : ℕ) (hj : j ≤ q.2.1) :
      (encBasisState (basisStep^[j] ((q.1, q.2.2.1, q.2.2.2), 0, 1 % q.1))).length ≤
        16 * ((encBasisArgs q).length + 1) := by
    have hpar := (iterate_basisStep_counter q.1 q.2.2.1 q.2.2.2 j).1
    have hcounter := (iterate_basisStep_counter q.1 q.2.2.1 q.2.2.2 j).2
    have hacc := length_encNat_mono (basisWeight_le q.1 j q.2.2.1 q.2.2.2)
    have hs := length_encNat_mono hj
    have hsucc := length_encNat_add_le_add q.1 1
    have h1 : (encNat 1).length = 1 := rfl
    change (encBasisState
      ((basisStep^[j] ((q.1, q.2.2.1, q.2.2.2), 0, 1 % q.1)).1,
        (basisStep^[j] ((q.1, q.2.2.1, q.2.2.2), 0, 1 % q.1)).2.1,
        (basisStep^[j] ((q.1, q.2.2.1, q.2.2.2), 0, 1 % q.1)).2.2)).length ≤ _
    rw [hpar, hcounter]
    change (encBasisState ((q.1, q.2.2.1, q.2.2.2), j,
      basisWeight q.1 j q.2.2.1 q.2.2.2)).length ≤ _
    simp only [encBasisState, encBasisArgs, encNat3, length_encPair] at hacc hs hsucc ⊢
    omega
  have hrun := budget_iterate hs hinit basisStep_inSpace hstates
    (.of_le_linear 16 16 fun _ => le_rfl)
  exact (snd' (snd' hrun)).of_enc_eq fun _ => rfl

end Cslib.TreeEval.Ary.Packed
