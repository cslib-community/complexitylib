/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.GateInterpolation
public import Complexity.Computability.TreeEval.Ary.Packed.InterpolationSpace

/-!
# Packed grid weights in native work space

A grid assignment is consumed by repeated division by the alphabet cardinality. The coordinate
counter, remaining assignment and modular accumulator are all stored in binary. Their sizes are
bounded by the encoded inputs even if the requested coordinate count exceeds the supplied point's
length, or the modulus or alphabet cardinality is zero.

## Main definitions

* `Cslib.TreeEval.Ary.Packed.encGridWeightArgs`: encode `((p,s,n,k),x)`.

## Main results

* `Cslib.TreeEval.Ary.Packed.gridWeight_inSpace`: the complete product of coordinate weights is
  computed in native work space linear in the encoded arguments, without a unary charge for
  the coordinate count or alphabet cardinality.

The table-query sum and the full Tree Evaluation machine remain separate obligations.
-/

public section

namespace Cslib.TreeEval.Ary.Packed

open Reader Turing MultiTapeTM ComputableInSpace

/-- Encode the modulus, alphabet size, coordinate count, assignment index and point in binary. -/
abbrev encGridWeightArgs : (ℕ × ℕ × ℕ × ℕ) × List ℕ ↪ List Bool :=
  encPair encBasisArgs (encList encNat)

/-- All intermediate products fit within the modulus plus one, including malformed zero
moduli and the empty product. -/
theorem gridWeight_le (p s n k : ℕ) (x : List ℕ) : gridWeight p s n k x ≤ p + 1 := by
  cases n with
  | zero => exact (Nat.mod_le _ _).trans (by omega)
  | succ n =>
    rw [gridWeight, Function.iterate_succ_apply']
    simp only [gridWeightStep]
    split_ifs with hz
    · omega
    · exact (Nat.mod_lt _ (Nat.pos_of_ne_zero hz)).le.trans (by omega)

private abbrev GridWeightPar := (ℕ × ℕ) × List ℕ
private abbrev GridWeightState := GridWeightPar × ℕ × ℕ × ℕ

private abbrev encGridWeightPar : GridWeightPar ↪ List Bool :=
  encPair (encPair encNat encNat) (encList encNat)

private abbrev encGridWeightState : GridWeightState ↪ List Bool :=
  encPair encGridWeightPar encNat3

private def gridWeightStateStep (q : GridWeightState) : GridWeightState :=
  (q.1, gridWeightStep q.1.1.1 q.1.1.2 q.1.2 q.2)

private theorem gridWeightStateStep_inSpace :
    ComputableInSpace gridWeightStateStep encGridWeightState encGridWeightState
      fun q => (encGridWeightState q).length := by
  have hpar := fst encGridWeightPar encNat3
  have hps := fst' hpar
  have hp := fst' hps
  have hs := snd' hps
  have hx := snd' hpar
  have hst := snd encGridWeightPar encNat3
  have hj := fst' hst
  have hqa := snd' hst
  have hq := fst' hqa
  have ha := snd' hqa
  have hcell := budget_comp_lin getD (linear_mul 8) (budget_prod hx hj)
  have hdigit := budget_natMod hq hs
  have hfactor := budget_comp_linear basisWeight_inSpace
    (budget_prod hp (budget_prod hs (budget_prod hdigit hcell)))
  have hmul := budget_comp_linear mulMod_inSpace (budget_prod hp (budget_prod ha hfactor))
  have hacc := budget_ite (budget_natIsZero hp)
    (budget_const (encB := encNat) 0 (.refl _)) hmul
  have hnext := budget_prod hpar (budget_prod (budget_natSucc hj)
    (budget_prod (budget_natDiv hq hs) hacc))
  exact hnext.of_enc_eq fun q => by
    by_cases h : q.1.1.1 = 0 <;> simp [gridWeightStateStep, gridWeightStep, h]

private theorem iterate_gridWeightStateStep (p s k : ℕ) (x : List ℕ) (n : ℕ) :
    gridWeightStateStep^[n] (((p, s), x), 0, k, 1 % p) =
      (((p, s), x), (gridWeightStep p s x)^[n] (0, k, 1 % p)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl

/-- All coordinates of one interpolation weight are evaluated in native work space linear in
`encGridWeightArgs ((p,s,n,k),x)`. No correctness or primality assumptions are needed for this
total resource bound. -/
theorem gridWeight_inSpace :
    ComputableInSpace (fun q : (ℕ × ℕ × ℕ × ℕ) × List ℕ =>
      gridWeight q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
      encGridWeightArgs encNat fun q => (encGridWeightArgs q).length := by
  have hargs := fst encBasisArgs (encList encNat)
  have hp := fst' hargs
  have hrest := snd' hargs
  have hs := fst' hrest
  have hnk := snd' hrest
  have hn := fst' hnk
  have hk := snd' hnk
  have hx := snd encBasisArgs (encList encNat)
  have hpar := budget_prod (budget_prod hp hs) hx
  have hone := budget_natMod (budget_const (encB := encNat) 1 (.refl _)) hp
  have hinit := budget_prod hpar
    (budget_prod (budget_const (encB := encNat) 0 (.refl _)) (budget_prod hk hone))
  have hstates (q : (ℕ × ℕ × ℕ × ℕ) × List ℕ) (j : ℕ) (hj : j ≤ q.1.2.2.1) :
      (encGridWeightState (gridWeightStateStep^[j]
        (((q.1.1, q.1.2.1), q.2), 0, q.1.2.2.2, 1 % q.1.1))).length ≤
        32 * ((encGridWeightArgs q).length + 1) := by
    rw [iterate_gridWeightStateStep]
    have hc := gridWeightStep_counters q.1.1 q.1.2.1 q.1.2.2.2 q.2 j
    have hquot := length_encNat_mono (Nat.div_le_self q.1.2.2.2 (q.1.2.1 ^ j))
    have hcounter := length_encNat_mono hj
    have hacc := length_encNat_mono (gridWeight_le q.1.1 q.1.2.1 j q.1.2.2.2 q.2)
    have hsucc := length_encNat_add_le_add q.1.1 1
    have h1 : (encNat 1).length = 1 := rfl
    change (encGridWeightState
      (((q.1.1, q.1.2.1), q.2),
        ((gridWeightStep q.1.1 q.1.2.1 q.2)^[j] (0, q.1.2.2.2, 1 % q.1.1)).1,
        ((gridWeightStep q.1.1 q.1.2.1 q.2)^[j] (0, q.1.2.2.2, 1 % q.1.1)).2.1,
        ((gridWeightStep q.1.1 q.1.2.1 q.2)^[j] (0, q.1.2.2.2, 1 % q.1.1)).2.2)).length ≤ _
    rw [hc.1, hc.2]
    change (encGridWeightState (((q.1.1, q.1.2.1), q.2), j,
      q.1.2.2.2 / q.1.2.1 ^ j, gridWeight q.1.1 q.1.2.1 j q.1.2.2.2 q.2)).length ≤ _
    simp only [encGridWeightState, encGridWeightPar, encGridWeightArgs, encBasisArgs,
      encNat3, length_encPair] at hquot hcounter hacc hsucc ⊢
    omega
  have hrun := budget_iterate hn hinit gridWeightStateStep_inSpace hstates
    (.of_le_linear 32 32 fun _ => le_rfl)
  refine (snd' (snd' (snd' hrun))).of_enc_eq fun q => ?_
  rw [iterate_gridWeightStateStep]
  rfl

end Cslib.TreeEval.Ary.Packed
