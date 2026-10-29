/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Reader.Defs
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib

/-!
# Residues within linear work space

The residue operations of `Cslib.TreeEval.Reader` are computable within work space linear
in the lengths of their encoded arguments.

## Main results

* `Cslib.TreeEval.Reader.addMod_inSpace`, `.mulMod_inSpace`, `.negMod_inSpace`,
  `.chi_inSpace`, `.unitInv_inSpace`: the residue operations; `unitInv p j` computes
  `(j + 1) ^ (p - 2)` modulo `p` by repeated multiplication.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Reader

open Turing MultiTapeTM ComputableInSpace

/-- The projections of a triple. -/
private theorem proj3 :
    ComputableInSpace (fun q : ℕ × ℕ × ℕ => q.1) encNat3 encNat
      (fun q => (encNat3 q).length) ∧
    ComputableInSpace (fun q : ℕ × ℕ × ℕ => q.2.1) encNat3 encNat
      (fun q => (encNat3 q).length) ∧
    ComputableInSpace (fun q : ℕ × ℕ × ℕ => q.2.2) encNat3 encNat
      (fun q => (encNat3 q).length) :=
  ⟨fst _ _, fst' (snd _ _), snd' (snd _ _)⟩

/-- The sum modulo `p`, from `(p, a, b)`. -/
theorem addMod_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ × ℕ => addMod q.1 q.2.1 q.2.2) encNat3 encNat
      fun q => (encNat3 q).length := by
  obtain ⟨hp, ha, hb⟩ := proj3
  exact budget_comp_lin natMod (linear_mul _)
    (budget_prod (budget_comp_lin natAdd linear_succ (budget_prod ha hb)) hp)

/-- The product modulo `p`, from `(p, a, b)`. -/
theorem mulMod_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ × ℕ => mulMod q.1 q.2.1 q.2.2) encNat3 encNat
      fun q => (encNat3 q).length := by
  obtain ⟨hp, ha, hb⟩ := proj3
  exact budget_comp_lin natMod (linear_mul _)
    (budget_prod (budget_comp_lin natMul (linear_mul _) (budget_prod ha hb)) hp)

/-- The negation modulo `p`, from `(p, a)`. -/
theorem negMod_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ => negMod q.1 q.2) (encPair encNat encNat) encNat
      fun q => (encPair encNat encNat q).length := by
  have hp := fst encNat encNat
  have hm := budget_comp_lin natMod (linear_mul _) (budget_prod (snd encNat encNat) hp)
  exact budget_comp_lin natMod (linear_mul _)
    (budget_prod (budget_comp_lin natSub linear_succ (budget_prod hm hp)) hp)

/-- The residue of `x` or of `1 - x` modulo `p`, from `((p, x), b)`. -/
theorem chi_inSpace :
    ComputableInSpace (fun q : (ℕ × ℕ) × Bool => chi q.1.1 q.2 q.1.2)
      (encPair (encPair encNat encNat) encBool) encNat
      fun q => (encPair (encPair encNat encNat) encBool q).length := by
  have hpx := fst (encPair encNat encNat) encBool
  have hp := fst' hpx
  have hmod := budget_comp_lin natMod (linear_mul _) (budget_prod (snd' hpx) hp)
  have hneg := budget_comp_linear negMod_inSpace hpx
  have hadd := budget_comp_linear addMod_inSpace
    (budget_prod hp (budget_prod (budget_const 1 (.refl _)) hneg))
  exact (budget_ite (snd _ _) hmod hadd).of_enc_eq fun q => by simp only [chi]

/-- One factor of a power modulo `p`, on `(p, a, acc)`. -/
private def powStep (q : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (q.1, q.2.1, mulMod q.1 q.2.2 q.2.1)

private theorem iterate_powStep (p a n : ℕ) : powStep^[n] (p, a, 1 % p) = (p, a, powMod p a n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem powMod_le {p a : ℕ} {k : ℕ} (hk : k ≤ p - 2) : powMod p a k ≤ p + 1 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · obtain rfl : k = 0 := by omega
    simp [powMod]
  · cases k with
    | zero => exact (Nat.mod_le _ _).trans (by omega)
    | succ k => exact (Nat.mod_lt _ hp).le.trans (by omega)

/-- **The inverse of the unit of round `j`**, `unitInv p j` from `(p, j)`. -/
theorem unitInv_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ => unitInv q.1 q.2) (encPair encNat encNat) encNat
      fun q => (encPair encNat encNat q).length := by
  have hp := fst encNat encNat
  have hstep : ComputableInSpace powStep encNat3 encNat3 fun q => (encNat3 q).length := by
    obtain ⟨hp, ha, hacc⟩ := proj3
    exact budget_prod hp (budget_prod ha
      (budget_comp_linear mulMod_inSpace (budget_prod hp (budget_prod hacc ha))))
  have hinit := budget_prod hp (budget_prod (budget_comp_lin natSucc linear_succ (snd _ _))
    (budget_comp_lin natMod (linear_mul _) (budget_prod (budget_const 1 (.refl _)) hp)))
  have hn := budget_comp_lin natPred linear_succ (budget_comp_lin natPred linear_succ hp)
  refine (snd' (snd' (budget_iterate hn hinit hstep (fun q k hk => ?_)
    (.of_le_linear 4 8 fun q => le_rfl)))).of_enc_eq fun q => by rw [iterate_powStep]; rfl
  rw [iterate_powStep]
  have h₁ := length_encNat_mono (powMod_le (p := q.1) (a := q.2 + 1)
    (k := k) (by omega))
  have h₂ := length_encNat_add_le_add q.1 1
  have h₃ := length_encNat_add_le_add q.2 1
  have h₄ : (encNat 1).length = 1 := rfl
  simp only [length_encPair] at h₁ h₂ h₃ ⊢
  omega

end Reader

end Cslib.TreeEval
