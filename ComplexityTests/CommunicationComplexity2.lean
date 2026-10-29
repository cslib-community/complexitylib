/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.PMF.Event
import Complexity.Computability.Communication.Amplification
import Complexity.Computability.Communication.Discrepancy
import Complexity.Computability.Communication.Functions
import Complexity.Computability.Communication.Newman
import Complexity.Probability.PMF

/-!
Regression clients for randomized communication complexity: public- and private-coin protocols,
amplification by majority, the averaging argument, Newman's theorem, the weighted area bound, the
discrepancy bound, and the `Ω(n)` lower bound for the inner product.
-/

open Cslib Cslib.Communication Finset

namespace CommunicationComplexity2Tests

/-! ### Protocols on transformed inputs and the function form -/

example : (Protocol.comap (fun n : ℕ => decide (n = 0)) id
    (.alice id (.output 0) (.output 1) : Protocol Bool Bool ℕ)).run 0 true = 1 := rfl

example : Protocol.ecomplexityFun (fun (x : Bool) (_ : Unit) => x) ≤ 1 :=
  Protocol.ecomplexityFun_le_iff.mpr ⟨.alice id (.output false) (.output true),
    funext₂ fun x _ => by cases x <;> rfl, le_rfl⟩

/-! ### A public-coin protocol for equality with two bits -/

/-- With shared random bits `r`, Alice sends `x ⬝ᵥ r` and Bob announces whether `y ⬝ᵥ r` agrees. -/
private def eqProtocol {n : ℕ} (r : BitString n) : Protocol (BitString n) (BitString n) Bool :=
  .alice (fun x => x ⬝ᵥ r) (.bob (fun y => y ⬝ᵥ r) (.output true) (.output false))
    (.bob (fun y => y ⬝ᵥ r) (.output false) (.output true))

private theorem run_eqProtocol {n : ℕ} (r x y : BitString n) :
    (eqProtocol r).run x y = decide (x ⬝ᵥ r = y ⬝ᵥ r) := by
  simp only [eqProtocol, Protocol.run_alice, Protocol.run_bob, Protocol.run_output]
  cases x ⬝ᵥ r <;> cases y ⬝ᵥ r <;> rfl

/-- The random-parity protocol for equality. -/
private noncomputable def eqPublicCoin (n : ℕ) : PublicCoin (BitString n) (BitString n) Bool :=
  (Probability.PMF.uniformOfFintype (BitString n)).map eqProtocol

private theorem depth_eqPublicCoin (n : ℕ) : PublicCoin.depth (eqPublicCoin n) ≤ 2 := by
  refine PublicCoin.depth_le_iff.mpr fun p hp => ?_
  obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  simp [eqProtocol]

/-- Two distinct bit strings have the same parity on exactly half of all subsets. -/
private theorem card_agree_mul_two {n : ℕ} {x y : BitString n} (hxy : x ≠ y) :
    #{r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} * 2 = 2 ^ n := by
  have hv : x + y ≠ 0 := fun h => hxy (by
    have := congrArg (· + y) h
    simpa [add_assoc] using this)
  have hcount := BitString.two_mul_card_dotProduct_eq_true_add (x + y)
  simp only [hv, ↓reduceIte, add_zero, Fintype.card_fin] at hcount
  have hagree : #{r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} =
      #{r : BitString n | ¬(x + y) ⬝ᵥ r = true} := by
    congr 1
    ext r
    simp only [mem_filter, mem_univ, true_and, add_dotProduct]
    cases x ⬝ᵥ r <;> cases y ⬝ᵥ r <;> decide
  have := card_filter_add_card_filter_not (s := univ) fun r : BitString n => (x + y) ⬝ᵥ r = true
  rw [card_univ, BitString.card] at this
  set a := #{r : BitString n | (x + y) ⬝ᵥ r = true}
  set b := #{r : BitString n | ¬(x + y) ⬝ᵥ r = true}
  omega

/-- The random-parity protocol errs only on unequal inputs, with probability one half. -/
private theorem solves_eqPublicCoin (n : ℕ) :
    PublicCoin.Solves (eqPublicCoin n) (1 / 2) (fun x y b => equality x y = b) Set.univ
      Set.univ := by
  classical
  intro x _ y _
  rw [PublicCoin.errorProb, eqPublicCoin, PMF.toOuterMeasure_map_apply,
    Probability.PMF.toOuterMeasure_apply_toReal, ← sum_filter]
  simp only [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    BitString.card, Set.mem_preimage, Set.mem_ofPred_eq, run_eqProtocol, equality]
  rw [sum_const, nsmul_eq_mul]
  by_cases hxy : x = y
  · simp [hxy]
  · have hset : #{r : BitString n | ¬decide (x = y) = decide (x ⬝ᵥ r = y ⬝ᵥ r)} =
        #{r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} := by
      congr 1
      ext r
      simp [hxy]
    rw [hset, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have : (#{r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} : ℝ) * 2 = 2 ^ n := by
      exact_mod_cast card_agree_mul_two hxy
    push_cast
    linarith

-- Equality has public-coin complexity at most two with error one half. A coin flip with no
-- communication also has error one half, so this only checks the protocol.
example (n : ℕ) : PublicCoin.ecomplexityFun (1 / 2) (equality : BitString n → BitString n → Bool)
    ≤ 2 :=
  (PublicCoin.ecomplexity_le_depth (solves_eqPublicCoin n)).trans (depth_eqPublicCoin n)

/-! ### Equality with error one quarter -/

/-- Bob announces whether his parities agree with the parities `a` and `b` that Alice sent. -/
private def eqCheck {n : ℕ} (r : BitString n × BitString n) (a b : Bool) :
    Protocol (BitString n) (BitString n) Bool :=
  .bob (fun y => decide (y ⬝ᵥ r.1 = a ∧ y ⬝ᵥ r.2 = b)) (.output false) (.output true)

/-- With shared random bits `r`, Alice sends `x ⬝ᵥ r.1` and `x ⬝ᵥ r.2`, and Bob announces whether
`y ⬝ᵥ r.1` and `y ⬝ᵥ r.2` agree with them. -/
private def eqProtocol₂ {n : ℕ} (r : BitString n × BitString n) :
    Protocol (BitString n) (BitString n) Bool :=
  .alice (fun x => x ⬝ᵥ r.1)
    (.alice (fun x => x ⬝ᵥ r.2) (eqCheck r false false) (eqCheck r false true))
    (.alice (fun x => x ⬝ᵥ r.2) (eqCheck r true false) (eqCheck r true true))

private theorem run_eqProtocol₂ {n : ℕ} (r : BitString n × BitString n) (x y : BitString n) :
    (eqProtocol₂ r).run x y = decide (x ⬝ᵥ r.1 = y ⬝ᵥ r.1 ∧ x ⬝ᵥ r.2 = y ⬝ᵥ r.2) := by
  simp only [eqProtocol₂, eqCheck, Protocol.run_alice, Protocol.run_bob, Protocol.run_output]
  cases x ⬝ᵥ r.1 <;> cases x ⬝ᵥ r.2 <;> cases y ⬝ᵥ r.1 <;> cases y ⬝ᵥ r.2 <;> rfl

/-- Two independent random parities for equality. -/
private noncomputable def eqPublicCoin₂ (n : ℕ) : PublicCoin (BitString n) (BitString n) Bool :=
  (Probability.PMF.uniformOfFintype (BitString n × BitString n)).map eqProtocol₂

private theorem depth_eqPublicCoin₂ (n : ℕ) : PublicCoin.depth (eqPublicCoin₂ n) ≤ 3 := by
  refine PublicCoin.depth_le_iff.mpr fun p hp => ?_
  obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  simp [eqProtocol₂, eqCheck]

/-- Two independent random parities err only on unequal inputs, with probability one quarter. -/
private theorem solves_eqPublicCoin₂ (n : ℕ) :
    PublicCoin.Solves (eqPublicCoin₂ n) (1 / 4) (fun x y b => equality x y = b) Set.univ
      Set.univ := by
  classical
  intro x _ y _
  rw [PublicCoin.errorProb, eqPublicCoin₂, PMF.toOuterMeasure_map_apply,
    Probability.PMF.toOuterMeasure_apply_toReal, ← sum_filter]
  simp only [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.card_prod, BitString.card, Set.mem_preimage, Set.mem_ofPred_eq, run_eqProtocol₂,
    equality]
  rw [sum_const, nsmul_eq_mul]
  by_cases hxy : x = y
  · simp [hxy]
  · have hset : #{r : BitString n × BitString n |
          ¬decide (x = y) = decide (x ⬝ᵥ r.1 = y ⬝ᵥ r.1 ∧ x ⬝ᵥ r.2 = y ⬝ᵥ r.2)} =
        #(({r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} : Finset _) ×ˢ
          ({r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} : Finset _)) := by
      congr 1
      ext r
      simp [hxy]
    rw [hset, card_product, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have : (#{r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} : ℝ) * 2 = 2 ^ n := by
      exact_mod_cast card_agree_mul_two hxy
    push_cast
    nlinarith

/-- Equality has public-coin complexity at most three with error one quarter, against `n + 1`
deterministically. -/
private theorem ecomplexityFun_quarter_equality_le (n : ℕ) :
    PublicCoin.ecomplexityFun (1 / 4) (equality : BitString n → BitString n → Bool) ≤ 3 :=
  (PublicCoin.ecomplexity_le_depth (solves_eqPublicCoin₂ n)).trans (depth_eqPublicCoin₂ n)

/-! ### Amplification by majority -/

/-- The strict majority of `2 r` independent runs of the two-parity protocol errs with probability
at most `(4 * (1 / 4) * (3 / 4)) ^ r = (3 / 4) ^ r`. -/
private theorem solves_amplify_eqPublicCoin₂ (n r : ℕ) :
    ((eqPublicCoin₂ n).amplify r).Solves ((3 / 4) ^ r) (fun x y b => equality x y = b)
      Set.univ Set.univ := by
  have h := (solves_eqPublicCoin₂ n).amplify (by norm_num) r
  rwa [show (4 * (1 / 4) * (1 - 1 / 4) : ℝ) = 3 / 4 by norm_num] at h

-- Equality with error `(3 / 4) ^ r` costs at most `6 r` bits.
example (n r : ℕ) :
    PublicCoin.ecomplexityFun ((3 / 4) ^ r) (equality : BitString n → BitString n → Bool) ≤
      2 * r * 3 :=
  (PublicCoin.ecomplexity_le_depth (solves_amplify_eqPublicCoin₂ n r)).trans
    (PublicCoin.depth_amplify_le (c := 3) (depth_eqPublicCoin₂ n) r)

-- Eight runs, `r = 4`, bring the error `(3 / 4) ^ 4 = 81 / 256` below `1 / 3`, with `24` bits for
-- every input length.
example (n : ℕ) :
    PublicCoin.ecomplexityFun (1 / 3) (equality : BitString n → BitString n → Bool) ≤ 24 :=
  (PublicCoin.ecomplexity_le_depth ((solves_amplify_eqPublicCoin₂ n 4).mono (by norm_num)
    subset_rfl subset_rfl)).trans
    ((PublicCoin.depth_amplify_le (c := 3) (depth_eqPublicCoin₂ n) 4).trans (by norm_num))

-- On 3-bit strings, public-coin equality with error `1 / 4` is strictly cheaper than
-- deterministic equality (`≤ 3` vs `4`).
example :
    PublicCoin.ecomplexityFun (1 / 4) (equality : BitString 3 → BitString 3 → Bool) <
      Protocol.ecomplexityFun (equality : BitString 3 → BitString 3 → Bool) := by
  refine (ecomplexityFun_quarter_equality_le 3).trans_lt ?_
  rw [Protocol.ecomplexityFun, ecomplexity_equality (by decide)]
  decide

-- The averaging argument picks, for inputs drawn from any distribution, a deterministic protocol
-- of depth at most two that errs with probability at most one half.
example (n : ℕ) (ν : PMF (BitString n × BitString n)) :
    ∃ p : Protocol (BitString n) (BitString n) Bool,
      p.distributionalError ν (fun x y b => equality x y = b) ≤ 1 / 2 ∧ p.depth ≤ 2 := by
  obtain ⟨p, hp, herr⟩ :=
    (solves_eqPublicCoin n).exists_distributionalError_le ν fun _ _ => ⟨trivial, trivial⟩
  exact ⟨p, herr, by exact_mod_cast (PublicCoin.depth_le_depth hp).trans (depth_eqPublicCoin n)⟩

/-! ### Deterministic and private-coin protocols -/

-- Deterministic equality on 3 bits gives a private-coin protocol of cost at most 4.
example : PrivateCoin.ecomplexityFun (1 / 3) (equality : BitString 3 → BitString 3 → Bool) ≤ 4 :=
  (PrivateCoin.ecomplexity_le_protocol (by norm_num)).trans_eq (ecomplexity_equality (by decide))

-- A deterministic protocol, run while ignoring the random bits, errs with probability zero.
example (x : BitString 2) (y : BitString 2) :
    PrivateCoin.errorProb ((eqProtocol 1).comap Prod.fst Prod.fst : PrivateCoin 3 1 _ _ _)
      (fun x y b => (eqProtocol 1).run x y = b) x y = 0 := by
  simp [PrivateCoin.errorProb]

/-! ### Newman's theorem -/

-- Applied to `eqPublicCoin₂`: a private-coin protocol for equality with `O(log n)` bits.
example (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    PrivateCoin.ecomplexityFun (1 / 4 + δ) (equality : BitString n → BitString n → Bool) ≤
      3 + Nat.clog 2 ⌈(n : ℝ) / δ ^ 2⌉₊ := by
  exact (PrivateCoin.ecomplexity_le_add_clog (n := n)
    (R := fun (x y : BitString n) b => equality x y = b) (A := Set.univ) (B := Set.univ)
    (by simp) (by simp) hδ).trans (add_le_add_left (ecomplexityFun_quarter_equality_le n) _)

-- On 16-bit strings, Newman's theorem with `eqPublicCoin₂ 16` gives a private-coin equality
-- protocol with error `3 / 8` sending at most `3 + ⌈log₂ (16 · 64)⌉ = 13` bits (whereas
-- deterministic equality needs `17` bits).
example :
    PrivateCoin.ecomplexityFun (3 / 8) (equality : BitString 16 → BitString 16 → Bool) ≤ 13 := by
  have h := (PrivateCoin.ecomplexity_le_add_clog (n := 16)
    (R := fun (x y : BitString 16) b => equality x y = b) (A := Set.univ) (B := Set.univ)
    (ε := 1 / 4) (δ := 1 / 8) (by simp) (by simp) (by norm_num)).trans
    (add_le_add_left (ecomplexityFun_quarter_equality_le 16) _)
  rw [show (1 / 4 + 1 / 8 : ℝ) = 3 / 8 by norm_num,
    show ⌈((16 : ℕ) : ℝ) / (1 / 8 : ℝ) ^ 2⌉₊ = 1024 by norm_num,
    show Nat.clog 2 1024 = 10 by decide] at h
  simpa [PrivateCoin.ecomplexityFun, show (3 + 10 : ℕ∞) = 13 by rfl] using h

/-! ### The weighted area bound -/

-- Unit weights give back the area bound.
example {X Y : Type*} [Fintype X] [Fintype Y] (p : Protocol X Y Bool) :
    (#{q : X × Y | p.run q.1 q.2 = true} : ℝ) ≤
      #{i | p.leafOutput i = true} * (Fintype.card X * Fintype.card Y) := by
  have h := Protocol.sum_filter_le_mul (p := p) rfl true (fun _ _ => (1 : ℝ))
    (K := Fintype.card X * Fintype.card Y) fun A B _ => by
      simp only [sum_const, nsmul_eq_mul, mul_one]
      exact mul_le_mul (by exact_mod_cast card_le_univ A) (by exact_mod_cast card_le_univ B)
        (by positivity) (by positivity)
  simpa using h

/-! ### Discrepancy and the inner product -/

-- On 4-bit strings, the uniform discrepancy of the inner product is at most `1 / 4`.
example :
    discrepancy (Probability.PMF.uniformOfFintype (BitString 4 × BitString 4))
      (fun x y => x ⬝ᵥ y) ≤ 1 / 4 := by
  have h := discrepancy_dotProduct_sq_mul_two_pow_le 4
  nlinarith [discrepancy_nonneg (ν := Probability.PMF.uniformOfFintype (BitString 4 × BitString 4))
    (f := fun x y => x ⬝ᵥ y)]

-- With error `1 / 3`, the inner product of ten bits needs at least four bits with public coins,
-- and hence also with private coins.
private theorem four_le_publicCoin_dotProduct_ten :
    4 ≤ PublicCoin.ecomplexityFun (1 / 3) (fun x y : BitString 10 => x ⬝ᵥ y) := by
  have h := PublicCoin.le_two_mul_ecomplexityFun_dotProduct_add_three 10
  cases hc : PublicCoin.ecomplexityFun (1 / 3) (fun x y : BitString 10 => x ⬝ᵥ y)
    using ENat.recTopCoe with
  | top => simp
  | coe c =>
    rw [hc] at h
    have : 10 ≤ 2 * c + 3 := by exact_mod_cast h
    exact_mod_cast (by omega : 4 ≤ c)

example : 4 ≤ PrivateCoin.ecomplexityFun (1 / 3) (fun x y : BitString 10 => x ⬝ᵥ y) :=
  four_le_publicCoin_dotProduct_ten.trans PublicCoin.ecomplexityFun_le_privateCoin

-- The general error trade-off: error `1 / 2 - γ` with `c` bits forces `(2 γ)² 2 ^ n ≤ 4 ^ c`.
example (n c : ℕ) {γ : ℝ} (hγ : 0 ≤ γ)
    (h : PublicCoin.ecomplexityFun (1 / 2 - γ) (fun x y : BitString n => x ⬝ᵥ y) ≤ c) :
    (2 * γ) ^ 2 * 2 ^ n ≤ 4 ^ c := by
  obtain ⟨μ, hμ, hc⟩ := PublicCoin.ecomplexity_le_iff.mp h
  exact hμ.sq_mul_two_pow_le_four_pow_of_dotProduct hc hγ

end CommunicationComplexity2Tests
