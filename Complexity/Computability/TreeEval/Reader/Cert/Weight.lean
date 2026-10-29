/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Reader.Cert.Residue
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.GetD

/-!
# The weights of table entries within linear work space

The weight `Cslib.TreeEval.Reader.weight p ℓ k x y`, the product of `x j` or `1 - x j` over the low
bits of `k` and the same over its high bits for `y`, is computable within work space
linear in the lengths of its encoded arguments and in `ℓ`. Its products are taken over a counter
rather than a list of indices, and they stay short: below `p`, or, for `p = 0`, no longer than the
registers together.

## Main results

* `Cslib.TreeEval.Reader.weight_inSpace`: the weight.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Reader

open Turing MultiTapeTM ComputableInSpace

/-! ### Half of a weight, over a counter -/

/-- A factor of half of a weight, on `((p, k, o), x)` and the counter and product `(j, a)`. -/
private def halfStep (s : ((ℕ × ℕ × ℕ) × List ℕ) × ℕ × ℕ) : ((ℕ × ℕ × ℕ) × List ℕ) × ℕ × ℕ :=
  (s.1, s.2.1 + 1, mulMod s.1.1.1 s.2.2
    (chi s.1.1.1 (s.1.1.2.1.testBit (s.1.1.2.2 + s.2.1)) (s.1.2.getD s.2.1 0)))

private theorem iterate_halfStep (p k o : ℕ) (x : List ℕ) (a : ℕ) (n : ℕ) :
    halfStep^[n] (((p, k, o), x), 0, a) = (((p, k, o), x), n, (List.range n).foldl
      (fun a j => mulMod p a (chi p (k.testBit (o + j)) (x.getD j 0))) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, List.range_succ, List.foldl_append]
    rfl

private theorem weight_eq (p ℓ k : ℕ) (x y : List ℕ) :
    weight p ℓ k x y = mulMod p (halfStep^[ℓ] (((p, k, 0), x), 0, 1 % p)).2.2
      (halfStep^[ℓ] (((p, k, ℓ), y), 0, 1 % p)).2.2 := by
  simp only [weight, iterate_halfStep, zero_add]

private theorem length_chi_le (p : ℕ) (b : Bool) (x : ℕ) :
    (encNat (chi p b x)).length ≤ (encNat p).length + (encNat x).length + 1 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · cases b
    · have : chi 0 false x = 1 := by simp [chi, addMod, negMod]
      rw [this]; simp
    · simp [chi]
  · have := length_encNat_mono
      (show chi p b x ≤ p by cases b <;> exact (Nat.mod_lt _ hp).le)
    omega

private theorem sum_length_getD_le (x : List ℕ) (j : ℕ) :
    ∑ i ∈ Finset.range j, (encNat (x.getD i 0)).length ≤ (encList encNat x).length := by
  induction x generalizing j with
  | nil => simp
  | cons a x ih =>
    rcases j with _ | j
    · simp
    · rw [Finset.sum_range_succ', length_encList]
      simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
      have := ih j
      rw [length_encList] at this
      omega

/-- For `p = 0`, the products of half of a weight are no longer than their factors together. -/
private theorem length_halfStep_zero_le (k o : ℕ) (x : List ℕ) (j : ℕ) :
    (encNat (halfStep^[j] (((0, k, o), x), 0, 1 % 0)).2.2).length ≤
      ∑ i ∈ Finset.range j, ((encNat (x.getD i 0)).length + 1) + 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Finset.sum_range_succ]
    have h₁ := length_encNat_mul_le (halfStep^[j] (((0, k, o), x), 0, 1 % 0)).2.2
      (chi 0 (k.testBit (o + j)) (x.getD j 0))
    have h₂ := length_chi_le 0 (k.testBit (o + j)) (x.getD j 0)
    rw [iterate_halfStep] at ih h₁ ⊢
    simp only [halfStep, mulMod, Nat.mod_zero] at ih h₁ ⊢
    have h₀ : (encNat 0).length = 0 := rfl
    omega

/-- **The products of half of a weight** are no longer than the prime, the register and the
counter together. -/
private theorem length_halfStep_le (p k o : ℕ) (x : List ℕ) (j : ℕ) :
    (encNat (halfStep^[j] (((p, k, o), x), 0, 1 % p)).2.2).length ≤
      (encNat p).length + (encList encNat x).length + j + 1 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have h₁ := length_halfStep_zero_le k o x j
    have h₂ := sum_length_getD_le x j
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at h₁
    omega
  · rcases j with _ | j
    · have := length_encNat_mono (Nat.mod_le 1 p)
      simp only [Function.iterate_zero, id_eq]
      have h₁ : (encNat 1).length = 1 := rfl
      omega
    · have := length_encNat_mono
        (show (halfStep^[j + 1] (((p, k, o), x), 0, 1 % p)).2.2 ≤ p by
          rw [Function.iterate_succ_apply', iterate_halfStep]
          simp only [halfStep, mulMod]
          exact (Nat.mod_lt _ hp).le)
      omega

/-- The encoding of the states of `halfStep`. -/
private abbrev encHalf : ((ℕ × ℕ × ℕ) × List ℕ) × ℕ × ℕ ↪ List Bool :=
  encPair (encPair encNat3 (encList encNat)) (encPair encNat encNat)

private theorem halfStep_inSpace :
    ComputableInSpace halfStep encHalf encHalf fun s => (encHalf s).length + 1 := by
  have hl : (fun s => (encHalf s).length) ≼ fun s => (encHalf s).length + 1 :=
    .of_le fun _ => by omega
  have hpar := (fst (encPair encNat3 (encList encNat)) (encPair encNat encNat)).weaken hl
  have hja := (snd (encPair encNat3 (encList encNat)) (encPair encNat encNat)).weaken hl
  have hpko := fst' hpar
  have hx := snd' hpar
  have hp := fst' hpko
  have hk := fst' (snd' hpko)
  have ho := snd' (snd' hpko)
  have hj := fst' hja
  have ha := snd' hja
  have hsucc := budget_comp_lin natSucc linear_succ hj
  have hoj := budget_comp_lin natAdd linear_succ (budget_prod ho hj)
  have hbit := budget_comp natTestBit (budget_prod hk hoj) (.of_le_linear 64 64 fun s => by
    have := length_encNat_add_le_add s.1.1.2.2 s.2.1
    simp only [length_encPair] at this ⊢; omega)
  have hxj := budget_comp_lin getD (linear_mul _) (budget_prod hx hj)
  have hc := budget_comp_linear chi_inSpace (budget_prod (budget_prod hp hxj) hbit)
  have hm := budget_comp_linear mulMod_inSpace (budget_prod hp (budget_prod ha hc))
  exact budget_prod hpar (budget_prod hsucc hm)

/-- The encoding of the arguments of half of a weight. -/
private abbrev encHalfIn : ((ℕ × ℕ × ℕ) × List ℕ) × ℕ ↪ List Bool :=
  encPair (encPair encNat3 (encList encNat)) encNat

/-- **Half of a weight**, from `(((p, k, o), x), n)`. -/
private theorem half_inSpace :
    ComputableInSpace
      (fun h : ((ℕ × ℕ × ℕ) × List ℕ) × ℕ => (halfStep^[h.2] (h.1, 0, 1 % h.1.1.1)).2.2)
      encHalfIn encNat fun h => 256 * ((encHalfIn h).length + h.2 + 1) := by
  have hl : (fun h => (encHalfIn h).length) ≼ fun h => 64 * ((encHalfIn h).length + h.2 + 1) :=
    .of_le fun _ => by omega
  have hpar := (fst (encPair encNat3 (encList encNat)) encNat).weaken hl
  have hn := (snd (encPair encNat3 (encList encNat)) encNat).weaken hl
  have hp := fst' (fst' hpar)
  have hone := budget_comp_lin natMod (linear_mul _)
    (budget_prod (budget_const (encB := encNat) 1 hl) hp)
  have hinit := budget_prod hpar (budget_prod (budget_const (encB := encNat) 0 hl) hone)
  have hlen (h : ((ℕ × ℕ × ℕ) × List ℕ) × ℕ) (j : ℕ) (hj : j ≤ h.2) :
      (encHalf (halfStep^[j] (h.1, 0, 1 % h.1.1.1))).length ≤
        4 * ((encHalfIn h).length + h.2 + 1) := by
    obtain ⟨⟨⟨p, k, o⟩, x⟩, n⟩ := h
    have h₁ := length_halfStep_le p k o x j
    have h₂ : (encNat j).length ≤ n := (length_encNat_le_self j).trans hj
    rw [iterate_halfStep] at h₁ ⊢
    simp only [length_encPair] at h₁ h₂ ⊢
    omega
  have h := iterate (n := fun h : ((ℕ × ℕ × ℕ) × List ℕ) × ℕ => h.2) hn hinit halfStep_inSpace
    (Q := fun h => 4 * ((encHalfIn h).length + h.2 + 1) + 1)
    (B := fun h => 4 * ((encHalfIn h).length + h.2 + 1))
    (fun h j hj => by have := hlen h j hj; dsimp only; omega) (fun h j hj => hlen h j hj)
  refine (snd' (snd' h)).mono_le fun h => ?_
  simp only [length_encPair] at *
  omega

/-- The encoding of the arguments of a weight. -/
abbrev encWeightIn : (ℕ × ℕ × ℕ) × List ℕ × List ℕ ↪ List Bool :=
  encPair encNat3 (encPair (encList encNat) (encList encNat))

/-- **The weight**, `weight p ℓ k x y` from `((p, ℓ, k), x, y)`. -/
theorem weight_inSpace :
    ComputableInSpace (fun w : (ℕ × ℕ × ℕ) × List ℕ × List ℕ =>
        weight w.1.1 w.1.2.1 w.1.2.2 w.2.1 w.2.2)
      encWeightIn encNat fun w => 64 * ((encWeightIn w).length + w.1.2.1 + 1) := by
  have hl : (fun w => (encWeightIn w).length) ≼ fun w => 64 *
      ((encWeightIn w).length + w.1.2.1 + 1) :=
    .of_le fun _ => by omega
  have hℓle : (fun w : (ℕ × ℕ × ℕ) × List ℕ × List ℕ => w.1.2.1) ≼
      fun w => 64 * ((encWeightIn w).length + w.1.2.1 + 1) := .of_le fun _ => by omega
  have hpkl := (fst encNat3 (encPair (encList encNat) (encList encNat))).weaken hl
  have hxy := (snd encNat3 (encPair (encList encNat) (encList encNat))).weaken hl
  have hp := fst' hpkl
  have hℓ := fst' (snd' hpkl)
  have hk := snd' (snd' hpkl)
  have hlo₀ := budget_prod (budget_prod (budget_prod hp
    (budget_prod hk (budget_const (encB := encNat) 0 hl))) (fst' hxy)) hℓ
  have hhi₀ := budget_prod (budget_prod (budget_prod hp (budget_prod hk hℓ)) (snd' hxy)) hℓ
  have hlo := budget_comp half_inSpace hlo₀
    (.const_mul 256 (((length_le hlo₀).add hℓle).add (.const 1 _)))
  have hhi := budget_comp half_inSpace hhi₀
    (.const_mul 256 (((length_le hhi₀).add hℓle).add (.const 1 _)))
  exact (budget_comp_linear mulMod_inSpace (budget_prod hp (budget_prod hlo hhi))).of_enc_eq
    fun w => by rw [weight_eq]

end Reader

end Cslib.TreeEval
