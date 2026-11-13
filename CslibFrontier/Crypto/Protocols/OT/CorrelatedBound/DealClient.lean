/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.OT.CorrelatedBound.Protocol
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Probability.Entropy
import CslibFrontier.Probability.MutualInformation.DataProcessing
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product
import CslibFrontier.Probability.Uniform

/-!
# The `(2, 1; 1)` Deal Source Client

This module instantiates the correlated-source oblivious-transfer upper bounds of
`Cslib.Crypto.Protocols.OT.CorrelatedBound.Protocol` on a concrete finite `(2, 1; 1)` card-deal
source (`deal211`) in which a deck of 4 distinct cards (`Fin 4`) is dealt uniformly at random:
Alice receives 2 cards (`a₀ ≠ a₁`) and Bob receives 1 card (`b ∉ {a₀, a₁}`), while 1 card
remains hidden.

## Main definitions

* `Cslib.Crypto.Protocols.OT.deal211`: uniform ordered `(2, 1; 1)` card deal over `Fin 4`.
* `Cslib.Crypto.Protocols.OT.deal211Unordered`: uniform unordered `(2, 1; 1)` card deal where
  Alice receives a 2-element subset of `Fin 4`.
* `Cslib.Crypto.Protocols.OT.deal211Batch`: `m` independent copies of `deal211`.

## Main results

* `Cslib.Crypto.Protocols.OT.mutualInfo_deal211`: `mutualInfo deal211 = 1` bit.
* `Cslib.Crypto.Protocols.OT.mutualInfo_deal211Unordered`: `mutualInfo deal211Unordered = 1` bit.
* `Cslib.Crypto.Protocols.OT.mutualInfo_deal211Batch`: `mutualInfo (deal211Batch m) = m` bits.
* `Cslib.Crypto.Protocols.OT.rot_le_one_of_deal211`,
  `Cslib.Crypto.Protocols.OT.chosenOT_le_one_of_deal211`,
  `Cslib.Crypto.Protocols.OT.commProtocol_rot_le_one_of_deal211`,
  `Cslib.Crypto.Protocols.OT.privateCoin_rot_le_one_of_deal211`,
  `Cslib.Crypto.Protocols.OT.rot_le_one_of_deal211Unordered`,
  `Cslib.Crypto.Protocols.OT.chosenOT_le_one_of_deal211Unordered`: at most `1` perfectly
  semi-honest private OT (random or chosen-input) is possible from a single `(2, 1; 1)` deal.
* `Cslib.Crypto.Protocols.OT.rot_le_of_deal211Batch`,
  `Cslib.Crypto.Protocols.OT.chosenOT_le_of_deal211Batch`: at most `m` OTs from `m` independent
  `(2, 1; 1)` deals.
* `Cslib.Crypto.Protocols.OT.rot_le_entropy_fst`,
  `Cslib.Crypto.Protocols.OT.rot_le_entropy_snd`,
  `Cslib.Crypto.Protocols.OT.rot_le_logb_card_fst`,
  `Cslib.Crypto.Protocols.OT.rot_le_logb_card_snd`: general source entropy and alphabet-size
  upper bounds on `k` random OTs.

## References

* [R. Ahlswede and I. Csiszár, *Common Randomness in Information Theory and Cryptography.
  Part I: Secret Sharing*][AhlswedeCsiszar1993] (bibliographic metadata verified; primary full text
  uninspected; locators unverified).
* [A. C. A. Nascimento and A. Winter, *On the Oblivious-Transfer Capacity of Noisy
  Resources*][NascimentoWinter2008] (bibliographic metadata verified; primary full text uninspected;
  locators unverified).
-/

open Cslib
open Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.MPC
open Cslib.Probability
open Cslib.Probability.PMF
open scoped ENNReal

namespace Cslib.Crypto.Protocols.OT

public section

private theorem uniformPermFin4_map_eval2_eq_uniform :
    ((PMF.uniformOfFintype (Equiv.Perm (Fin 4))).map fun ρ => ρ 2) =
      PMF.uniformOfFintype (Fin 4) := by
  let μ := (PMF.uniformOfFintype (Equiv.Perm (Fin 4))).map fun ρ => ρ 2
  have hconst : ∀ b : Fin 4, μ b = μ 0 := by
    intro b
    let σ := Equiv.swap (0 : Fin 4) b
    have hinv : μ.map σ = μ := by
      dsimp only [μ]
      rw [PMF.map_comp]
      have hcomp : ((σ : Fin 4 → Fin 4) ∘ fun ρ : Equiv.Perm (Fin 4) => ρ 2) =
          (fun ρ : Equiv.Perm (Fin 4) => ρ 2) ∘ Equiv.mulLeft σ := rfl
      rw [hcomp, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv]
    calc μ b = (μ.map σ) b := (congrArg (fun q : PMF (Fin 4) => q b) hinv).symm
      _ = μ (σ.symm b) := map_equiv_apply μ σ b
      _ = μ 0 := by simp only [σ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hsum : ∑ b : Fin 4, μ b = 1 := by
    simpa only [tsum_fintype] using μ.tsum_coe
  have h4 : (4 : ℝ≥0∞) * μ 0 = 1 := by
    have hsum' : ∑ _ : Fin 4, μ 0 = 1 := by
      rw [← hsum]
      exact Finset.sum_congr rfl fun b _ => (hconst b).symm
    simpa only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using hsum'
  have h0 : μ 0 = (4 : ℝ≥0∞)⁻¹ := by
    rw [mul_comm] at h4
    exact ENNReal.eq_inv_of_mul_eq_one_left h4
  ext b
  rw [hconst b, h0, PMF.uniformOfFintype_apply, Fintype.card_fin]
  rfl

/-- Uniform ordered `(2, 1; 1)` card deal over `Fin 4`: Alice gets `(ρ 0, ρ 1)` and Bob gets
`ρ 2` for a uniform random permutation `ρ : Equiv.Perm (Fin 4)`. -/
@[expose] noncomputable def deal211 : PMF ((Fin 4 × Fin 4) × Fin 4) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin 4))).map fun ρ => ((ρ 0, ρ 1), ρ 2)

/-- Support characterization for `deal211`: `(a, b)` occurs iff `a.1`, `a.2`, and `b` are
pairwise distinct cards in `Fin 4`. -/
theorem mem_support_deal211 {a : Fin 4 × Fin 4} {b : Fin 4} :
    (a, b) ∈ deal211.support ↔ a.1 ≠ a.2 ∧ b ≠ a.1 ∧ b ≠ a.2 := by
  rw [deal211, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨ρ, _, hρ⟩
    have ha1 : ρ 0 = a.1 := congrArg (fun p => p.1.1) hρ
    have ha2 : ρ 1 = a.2 := congrArg (fun p => p.1.2) hρ
    have hb : ρ 2 = b := congrArg Prod.snd hρ
    refine ⟨?_, ?_, ?_⟩
    · rw [← ha1, ← ha2]
      exact ρ.injective.ne (by decide)
    · rw [← hb, ← ha1]
      exact ρ.injective.ne (by decide)
    · rw [← hb, ← ha2]
      exact ρ.injective.ne (by decide)
  · rintro ⟨h01, hb0, hb1⟩
    have hrem : ∃ c : Fin 4, c ≠ a.1 ∧ c ≠ a.2 ∧ c ≠ b := by
      have hcard : (({a.1, a.2, b} : Finset (Fin 4)).card) ≤ 3 := by
        calc ({a.1, a.2, b} : Finset (Fin 4)).card
            ≤ ({a.2, b} : Finset (Fin 4)).card + 1 := Finset.card_insert_le _ _
          _ ≤ ({b} : Finset (Fin 4)).card + 1 + 1 :=
              Nat.add_le_add_right (Finset.card_insert_le _ _) 1
          _ = 3 := by simp only [Finset.card_singleton]
      have hne : (Finset.univ \ ({a.1, a.2, b} : Finset (Fin 4))).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
          Fintype.card_fin]
        omega
      obtain ⟨c, hc⟩ := hne
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hc
      exact ⟨c, fun h => hc.2 (Or.inl h), fun h => hc.2 (Or.inr (Or.inl h)),
        fun h => hc.2 (Or.inr (Or.inr h))⟩
    obtain ⟨c, hc0, hc1, hcb⟩ := hrem
    let f : Fin 4 → Fin 4 := ![a.1, a.2, b, c]
    have hinj : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> dsimp only [f] at hij <;>
        first | rfl | exact False.elim (h01 hij) | exact False.elim (hb0 hij.symm) |
          exact False.elim (hb1 hij.symm) | exact False.elim (hc0 hij.symm) |
          exact False.elim (hc1 hij.symm) | exact False.elim (hcb hij.symm) |
          exact False.elim (h01 hij.symm) | exact False.elim (hb0 hij) |
          exact False.elim (hb1 hij) | exact False.elim (hc0 hij) |
          exact False.elim (hc1 hij) | exact False.elim (hcb hij)
    let ρ : Equiv.Perm (Fin 4) :=
      Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, rfl⟩)
    have hρsupp : ρ ∈ (PMF.uniformOfFintype (Equiv.Perm (Fin 4))).support := by
      rw [PMF.mem_support_iff, PMF.uniformOfFintype_apply]
      simp only [ne_eq, ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, not_false_eq_true]
    exact ⟨ρ, hρsupp, rfl⟩

/-- Bob's marginal in `deal211` is uniform over `Fin 4`. -/
theorem deal211_map_snd : deal211.map Prod.snd = PMF.uniformOfFintype (Fin 4) := by
  dsimp only [deal211]
  rw [PMF.map_comp]
  exact uniformPermFin4_map_eval2_eq_uniform

private noncomputable def unseenOrdered (a : Fin 4 × Fin 4) : Finset (Fin 4) :=
  (Finset.univ.erase a.1).erase a.2

private theorem unseenOrdered_card {a : Fin 4 × Fin 4} (h : a.1 ≠ a.2) :
    (unseenOrdered a).card = 2 := by
  dsimp only [unseenOrdered]
  have ha1 : a.1 ∈ (Finset.univ : Finset (Fin 4)) := Finset.mem_univ _
  have ha2 : a.2 ∈ (Finset.univ : Finset (Fin 4)).erase a.1 :=
    Finset.mem_erase.mpr ⟨h.symm, Finset.mem_univ _⟩
  rw [Finset.card_erase_of_mem ha2, Finset.card_erase_of_mem ha1, Finset.card_univ,
    Fintype.card_fin]

private theorem deal211_fst_ne {a : Fin 4 × Fin 4} (ha : a ∈ (deal211.map Prod.fst).support) :
    a.1 ≠ a.2 := by
  rw [PMF.mem_support_map_iff] at ha
  obtain ⟨⟨a', b⟩, hab, rfl⟩ := ha
  exact (mem_support_deal211.mp hab).1

private theorem deal211_const_on_unseen (a : Fin 4 × Fin 4)
    {b₀ b₁ : Fin 4} (hb₀ : b₀ ∈ unseenOrdered a) (hb₁ : b₁ ∈ unseenOrdered a) :
    deal211 (a, b₁) = deal211 (a, b₀) := by
  dsimp only [unseenOrdered] at hb₀ hb₁
  rw [Finset.mem_erase, Finset.mem_erase] at hb₀ hb₁
  let σ := Equiv.swap b₀ b₁
  let g : ((Fin 4 × Fin 4) × Fin 4) ≃ ((Fin 4 × Fin 4) × Fin 4) :=
    Equiv.prodCongr (Equiv.prodCongr σ σ) σ
  have hinv : deal211.map g = deal211 := by
    dsimp only [deal211]
    rw [PMF.map_comp]
    have hcomp : ((g : (Fin 4 × Fin 4) × Fin 4 → (Fin 4 × Fin 4) × Fin 4) ∘
        fun ρ : Equiv.Perm (Fin 4) => ((ρ 0, ρ 1), ρ 2)) =
        (fun ρ : Equiv.Perm (Fin 4) => ((ρ 0, ρ 1), ρ 2)) ∘ Equiv.mulLeft σ := rfl
    rw [hcomp, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv]
  have hsymm : g.symm (a, b₁) = (a, b₀) := by
    have hσ1 : σ.symm a.1 = a.1 := by
      rw [Equiv.symm_swap]
      exact Equiv.swap_apply_of_ne_of_ne hb₀.2.1.symm hb₁.2.1.symm
    have hσ2 : σ.symm a.2 = a.2 := by
      rw [Equiv.symm_swap]
      exact Equiv.swap_apply_of_ne_of_ne hb₀.1.symm hb₁.1.symm
    have hσb : σ.symm b₁ = b₀ := by simp only [σ, Equiv.symm_swap, Equiv.swap_apply_right]
    exact Prod.ext (Prod.ext hσ1 hσ2) hσb
  calc deal211 (a, b₁) = (deal211.map g) (a, b₁) :=
        (congrArg (fun q : PMF ((Fin 4 × Fin 4) × Fin 4) => q (a, b₁)) hinv).symm
    _ = deal211 (g.symm (a, b₁)) := map_equiv_apply deal211 g (a, b₁)
    _ = deal211 (a, b₀) := by rw [hsymm]

/-- The mutual information of the ordered `(2, 1; 1)` deal source `deal211` is exactly `1` bit. -/
theorem mutualInfo_deal211 : mutualInfo deal211 = 1 := by
  have hsnd : entropy (deal211.map Prod.snd) = 2 := by
    rw [deal211_map_snd, entropy_uniform, Fintype.card_fin]
    have h4 : ((4 : ℕ) : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h4, Real.logb_two_pow]
    norm_num
  have hres := mutualInfo_eq_entropy_map_snd_sub_logb_of_const_fiber deal211 unseenOrdered 2
    (by norm_num) (fun a ha => unseenOrdered_card (deal211_fst_ne ha))
    (fun a _ b hb => by
      by_contra hne0
      have hsupp : (a, b) ∈ deal211.support := hne0
      obtain ⟨_, hb1, hb2⟩ := mem_support_deal211.mp hsupp
      exact hb (Finset.mem_erase.mpr ⟨hb2, Finset.mem_erase.mpr ⟨hb1, Finset.mem_univ _⟩⟩))
    (fun a _ b₀ hb₀ b₁ hb₁ => deal211_const_on_unseen a hb₀ hb₁)
  rw [hres, hsnd, Nat.cast_ofNat, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  norm_num

/-- Any protocol realizing `k` independent random OTs with perfect semi-honest privacy over
`deal211` satisfies `k ≤ 1`. -/
theorem rot_le_one_of_deal211 {sc : Schedule 2 noOracleSpec} {Coins : Fin 2 → Type}
    [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)] {k : ℕ}
    (proto : MPC.Protocol 2 noOracleSpec sc (Fin.cases (Fin 4 × Fin 4) (fun _ => Fin 4)) Coins
      (fun _ => Fin k → Bool × Bool))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc (fun _ => Unit) (Fin.cases (Fin 4 × Fin 4) (fun _ => Fin 4)) Coins
        (fun _ => Fin k → Bool × Bool) I)
    (hPriv : PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (fun _ => dealSource deal211) (rotFunctionality k) S) :
    k ≤ 1 := by
  have hk := rot_le_mutualInfo proto deal211 S hPriv
  rw [mutualInfo_deal211] at hk
  exact_mod_cast hk

/-- Any protocol realizing `k` chosen-input OTs (`batchOTFunctionality k Bool`) with perfect
semi-honest privacy over `deal211` satisfies `k ≤ 1`. -/
theorem chosenOT_le_one_of_deal211 {sc : Schedule 2 noOracleSpec} {Coins : Fin 2 → Type}
    [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)] {k : ℕ}
    (proto : MPC.Protocol 2 noOracleSpec sc
      (fun i => (batchOTSpec k Bool).Query () i × Fin.cases (Fin 4 × Fin 4) (fun _ => Fin 4) i)
      Coins ((batchOTSpec k Bool).Answer ()))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc ((batchOTSpec k Bool).Query ())
        (fun i => (batchOTSpec k Bool).Query () i × Fin.cases (Fin 4 × Fin 4) (fun _ => Fin 4) i)
        Coins ((batchOTSpec k Bool).Answer ()) I)
    (hPriv : PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (dealSourceWithInput deal211) (batchOTFunctionality k Bool) S) :
    k ≤ 1 := by
  have hk := chosenOT_le_mutualInfo proto deal211 S hPriv
  rw [mutualInfo_deal211] at hk
  exact_mod_cast hk

/-- Any deterministic communication tree `P` computing `k` perfectly private random OTs over
`deal211` satisfies `k ≤ 1`. -/
theorem commProtocol_rot_le_one_of_deal211 {k : ℕ} {τ : Type}
    (P : Communication.Protocol (Fin 4 × Fin 4) (Fin 4) τ)
    (outA : (Fin 4 × Fin 4) × Fin P.leafCount → Fin k → Bool × Bool)
    (outB : Fin 4 × Fin P.leafCount → Fin k → Bool × Bool)
    (hCorrect : ∀ a b j, (a, b) ∈ deal211.support →
      (outB (b, P.leaf a b) j).2 = otSelect (outA (a, P.leaf a b) j) (outB (b, P.leaf a b) j).1)
    (hAlicePriv : IndepUniform (P.transcriptLaw deal211) (fun (x, _, t) => (outA (x, t), t))
      (fun (_, y, t) => rotChoices (outB (y, t))))
    (hBobPriv : IndepUniform (P.transcriptLaw deal211) (fun (_, y, t) => (t, outB (y, t)))
      (fun (x, y, t) => rotUnselected (outA (x, t)) (outB (y, t)))) :
    k ≤ 1 := by
  have hk := commProtocol_rot_le_mutualInfo P deal211 outA outB hCorrect hAlicePriv hBobPriv
  rw [mutualInfo_deal211] at hk
  exact_mod_cast hk

/-- Any private-coin communication protocol computing `k` perfectly private random OTs over
`deal211` satisfies `k ≤ 1`. -/
theorem privateCoin_rot_le_one_of_deal211 {a b k : ℕ} {τ : Type}
    (P : Communication.PrivateCoin a b (Fin 4 × Fin 4) (Fin 4) τ)
    (outA : ((Fin 4 × Fin 4) × BitString a) × Fin (Communication.Protocol.leafCount P) →
      Fin k → Bool × Bool)
    (outB : (Fin 4 × BitString b) × Fin (Communication.Protocol.leafCount P) →
      Fin k → Bool × Bool)
    (hCorrect : ∀ (u : (Fin 4 × Fin 4) × BitString a) (v : Fin 4 × BitString b) (j : Fin k),
      (u.1, v.1) ∈ deal211.support →
        (outB (v, Communication.Protocol.leaf P u v) j).2 =
          otSelect (outA (u, Communication.Protocol.leaf P u v) j)
            (outB (v, Communication.Protocol.leaf P u v) j).1)
    (hAlicePriv : IndepUniform
      (Communication.Protocol.transcriptLaw P (Communication.PrivateCoin.inputLaw a b deal211))
      (fun (x, _, t) => (outA (x, t), t)) (fun (_, y, t) => rotChoices (outB (y, t))))
    (hBobPriv : IndepUniform
      (Communication.Protocol.transcriptLaw P (Communication.PrivateCoin.inputLaw a b deal211))
      (fun (_, y, t) => (t, outB (y, t)))
      (fun (x, y, t) => rotUnselected (outA (x, t)) (outB (y, t)))) :
    k ≤ 1 := by
  have hk := privateCoin_rot_le_mutualInfo P deal211 outA outB hCorrect hAlicePriv hBobPriv
  rw [mutualInfo_deal211] at hk
  exact_mod_cast hk

/-- Uniform unordered `(2, 1; 1)` card deal over `Fin 4`: Alice receives the unordered 2-element
subset `{ρ 0, ρ 1}` and Bob receives `ρ 2`. -/
@[expose] noncomputable def deal211Unordered : PMF ({s : Finset (Fin 4) // s.card = 2} × Fin 4) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin 4))).map fun ρ =>
    (⟨{ρ 0, ρ 1}, Finset.card_pair (ρ.injective.ne (by decide : (0 : Fin 4) ≠ 1))⟩, ρ 2)

/-- Support characterization for `deal211Unordered`: `(s, b)` occurs iff `b ∉ s.1`. -/
theorem mem_support_deal211Unordered {s : {s : Finset (Fin 4) // s.card = 2}} {b : Fin 4} :
    (s, b) ∈ deal211Unordered.support ↔ b ∉ s.1 := by
  rw [deal211Unordered, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨ρ, _, hρ⟩
    have hs : ({ρ 0, ρ 1} : Finset (Fin 4)) = s.1 := congrArg (fun p => p.1.1) hρ
    have hb : ρ 2 = b := congrArg Prod.snd hρ
    rw [← hs, ← hb, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact (ρ.injective.ne (by decide : (2 : Fin 4) ≠ 0)) h
    · exact (ρ.injective.ne (by decide : (2 : Fin 4) ≠ 1)) h
  · intro hb
    obtain ⟨a₀, a₁, ha_ne, hs_eq⟩ := Finset.card_eq_two.mp s.2
    have hba0 : b ≠ a₀ := by
      intro h
      rw [hs_eq, h] at hb
      exact hb (Finset.mem_insert_self _ _)
    have hba1 : b ≠ a₁ := by
      intro h
      rw [hs_eq, h] at hb
      exact hb (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hsupp : ((a₀, a₁), b) ∈ deal211.support := mem_support_deal211.mpr ⟨ha_ne, hba0, hba1⟩
    rw [deal211, PMF.mem_support_map_iff] at hsupp
    obtain ⟨ρ, hρsupp, hρ⟩ := hsupp
    have ha0 : ρ 0 = a₀ := congrArg (fun p => p.1.1) hρ
    have ha1 : ρ 1 = a₁ := congrArg (fun p => p.1.2) hρ
    have hb_eq : ρ 2 = b := congrArg Prod.snd hρ
    refine ⟨ρ, hρsupp, Prod.ext (Subtype.ext ?_) hb_eq⟩
    dsimp only
    rw [ha0, ha1, hs_eq]

/-- Bob's marginal in `deal211Unordered` is uniform over `Fin 4`. -/
theorem deal211Unordered_map_snd :
    deal211Unordered.map Prod.snd = PMF.uniformOfFintype (Fin 4) := by
  dsimp only [deal211Unordered]
  rw [PMF.map_comp]
  exact uniformPermFin4_map_eval2_eq_uniform

private noncomputable def unseenUnordered (s : {s : Finset (Fin 4) // s.card = 2}) :
    Finset (Fin 4) :=
  Finset.univ \ s.1

private theorem unseenUnordered_card (s : {s : Finset (Fin 4) // s.card = 2}) :
    (unseenUnordered s).card = 2 := by
  dsimp only [unseenUnordered]
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, s.2]

private theorem deal211Unordered_const_on_unseen (s : {s : Finset (Fin 4) // s.card = 2})
    {b₀ b₁ : Fin 4} (hb₀ : b₀ ∈ unseenUnordered s) (hb₁ : b₁ ∈ unseenUnordered s) :
    deal211Unordered (s, b₁) = deal211Unordered (s, b₀) := by
  dsimp only [unseenUnordered] at hb₀ hb₁
  rw [Finset.mem_sdiff] at hb₀ hb₁
  let σ := Equiv.swap b₀ b₁
  have hσσ : ∀ z : Fin 4, σ (σ z) = z := fun z => by
    have h : σ.symm = σ := Equiv.symm_swap b₀ b₁
    conv_lhs => arg 1; rw [← h]
    exact σ.symm_apply_apply z
  let mapSet : {t : Finset (Fin 4) // t.card = 2} → {t : Finset (Fin 4) // t.card = 2} :=
    fun t => ⟨t.1.map σ.toEmbedding, by rw [Finset.card_map, t.2]⟩
  have hinv_set : Function.LeftInverse mapSet mapSet := by
    intro t
    apply Subtype.ext
    ext x
    simp only [mapSet, Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨y, ⟨z, hz, hy⟩, hx⟩
      rw [← hy, hσσ] at hx
      exact hx ▸ hz
    · intro hx
      exact ⟨σ x, ⟨x, hx, rfl⟩, hσσ x⟩
  let g : ({t : Finset (Fin 4) // t.card = 2} × Fin 4) ≃
      ({t : Finset (Fin 4) // t.card = 2} × Fin 4) :=
    { toFun := fun p => (mapSet p.1, σ p.2)
      invFun := fun p => (mapSet p.1, σ p.2)
      left_inv := fun p => Prod.ext (hinv_set p.1) (hσσ p.2)
      right_inv := fun p => Prod.ext (hinv_set p.1) (hσσ p.2) }
  have hinv : deal211Unordered.map g = deal211Unordered := by
    dsimp only [deal211Unordered]
    rw [PMF.map_comp]
    have hcomp : ((g : _ → _) ∘ fun ρ : Equiv.Perm (Fin 4) =>
        (⟨{ρ 0, ρ 1}, Finset.card_pair (ρ.injective.ne (by decide : (0 : Fin 4) ≠ 1))⟩, ρ 2)) =
        (fun ρ : Equiv.Perm (Fin 4) =>
          (⟨{ρ 0, ρ 1}, Finset.card_pair (ρ.injective.ne (by decide : (0 : Fin 4) ≠ 1))⟩, ρ 2)) ∘
        Equiv.mulLeft σ := by
      funext ρ
      refine Prod.ext (Subtype.ext ?_) rfl
      ext x
      simp only [g, mapSet, Equiv.coe_fn_mk, Function.comp_def, Equiv.coe_mulLeft,
        Equiv.Perm.mul_apply, Finset.mem_map, Finset.mem_insert, Finset.mem_singleton,
        Equiv.coe_toEmbedding]
      constructor
      · rintro ⟨y, rfl | rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨ρ 0, Or.inl rfl, rfl⟩
        · exact ⟨ρ 1, Or.inr rfl, rfl⟩
    rw [hcomp, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv]
  have hsymm : g.symm (s, b₁) = (s, b₀) := by
    refine Prod.ext (Subtype.ext ?_) ?_
    · ext x
      simp only [g, mapSet, Equiv.coe_fn_symm_mk, Finset.mem_map, Equiv.coe_toEmbedding]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy0 : y ≠ b₀ := fun h => hb₀.2 (h ▸ hy)
        have hy1 : y ≠ b₁ := fun h => hb₁.2 (h ▸ hy)
        rwa [Equiv.swap_apply_of_ne_of_ne hy0 hy1]
      · intro hx
        have hx0 : x ≠ b₀ := fun h => hb₀.2 (h ▸ hx)
        have hx1 : x ≠ b₁ := fun h => hb₁.2 (h ▸ hx)
        exact ⟨x, hx, Equiv.swap_apply_of_ne_of_ne hx0 hx1⟩
    · simp only [g, σ, Equiv.coe_fn_symm_mk, Equiv.swap_apply_right]
  calc deal211Unordered (s, b₁) = (deal211Unordered.map g) (s, b₁) :=
        (congrArg (fun q : PMF _ => q (s, b₁)) hinv).symm
    _ = deal211Unordered (g.symm (s, b₁)) := map_equiv_apply deal211Unordered g (s, b₁)
    _ = deal211Unordered (s, b₀) := by rw [hsymm]

/-- The mutual information of the unordered `(2, 1; 1)` deal source `deal211Unordered` is
`1` bit. -/
theorem mutualInfo_deal211Unordered : mutualInfo deal211Unordered = 1 := by
  have hsnd : entropy (deal211Unordered.map Prod.snd) = 2 := by
    rw [deal211Unordered_map_snd, entropy_uniform, Fintype.card_fin]
    have h4 : ((4 : ℕ) : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h4, Real.logb_two_pow]
    norm_num
  have hres := mutualInfo_eq_entropy_map_snd_sub_logb_of_const_fiber
    deal211Unordered unseenUnordered 2 (by norm_num) (fun s _ => unseenUnordered_card s)
    (fun s _ b hb => by
      by_contra hne0
      have hsupp : (s, b) ∈ deal211Unordered.support := hne0
      exact hb (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, mem_support_deal211Unordered.mp hsupp⟩))
    (fun s _ b₀ hb₀ b₁ hb₁ => deal211Unordered_const_on_unseen s hb₀ hb₁)
  rw [hres, hsnd, Nat.cast_ofNat, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  norm_num

/-- Any protocol realizing `k` independent random OTs with perfect semi-honest privacy over
`deal211Unordered` satisfies `k ≤ 1`. -/
theorem rot_le_one_of_deal211Unordered {sc : Schedule 2 noOracleSpec} {Coins : Fin 2 → Type}
    [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)] {k : ℕ}
    (proto : MPC.Protocol 2 noOracleSpec sc
      (Fin.cases {s : Finset (Fin 4) // s.card = 2} (fun _ => Fin 4)) Coins
      (fun _ => Fin k → Bool × Bool))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc (fun _ => Unit)
        (Fin.cases {s : Finset (Fin 4) // s.card = 2} (fun _ => Fin 4)) Coins
        (fun _ => Fin k → Bool × Bool) I)
    (hPriv : PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (fun _ => dealSource deal211Unordered) (rotFunctionality k) S) :
    k ≤ 1 := by
  have hk := rot_le_mutualInfo proto deal211Unordered S hPriv
  rw [mutualInfo_deal211Unordered] at hk
  exact_mod_cast hk

/-- Any protocol realizing `k` chosen-input OTs with perfect semi-honest privacy over
`deal211Unordered` satisfies `k ≤ 1`. -/
theorem chosenOT_le_one_of_deal211Unordered {sc : Schedule 2 noOracleSpec} {Coins : Fin 2 → Type}
    [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)] {k : ℕ}
    (proto : MPC.Protocol 2 noOracleSpec sc
      (fun i => (batchOTSpec k Bool).Query () i ×
        Fin.cases {s : Finset (Fin 4) // s.card = 2} (fun _ => Fin 4) i)
      Coins ((batchOTSpec k Bool).Answer ()))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc ((batchOTSpec k Bool).Query ())
        (fun i => (batchOTSpec k Bool).Query () i ×
          Fin.cases {s : Finset (Fin 4) // s.card = 2} (fun _ => Fin 4) i)
        Coins ((batchOTSpec k Bool).Answer ()) I)
    (hPriv : PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (dealSourceWithInput deal211Unordered) (batchOTFunctionality k Bool) S) :
    k ≤ 1 := by
  have hk := chosenOT_le_mutualInfo proto deal211Unordered S hPriv
  rw [mutualInfo_deal211Unordered] at hk
  exact_mod_cast hk

/-- `m` independent copies of the ordered `(2, 1; 1)` card deal `deal211`. -/
@[expose] noncomputable def deal211Batch (m : ℕ) :
    PMF ((Fin m → Fin 4 × Fin 4) × (Fin m → Fin 4)) :=
  (PMF.pi fun _ : Fin m => deal211).map fun f => (fun i => (f i).1, fun i => (f i).2)

private theorem deal211Batch_apply (m : ℕ) (as : Fin m → Fin 4 × Fin 4) (bs : Fin m → Fin 4) :
    deal211Batch m (as, bs) = ∏ i : Fin m, deal211 (as i, bs i) := by
  change ((PMF.pi fun _ : Fin m => deal211).map
    (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Fin 4 × Fin 4) (fun _ => Fin 4))) (as, bs) =
    _
  rw [map_equiv_apply, PMF.pi_apply]
  rfl

/-- `m` independent `(2, 1; 1)` card deals have mutual information exactly `(m : ℝ)` bits. -/
theorem mutualInfo_deal211Batch (m : ℕ) : mutualInfo (deal211Batch m) = m := by
  have hsnd_eq : (deal211Batch m).map Prod.snd = PMF.uniformOfFintype (Fin m → Fin 4) := by
    dsimp only [deal211Batch]
    rw [PMF.map_comp]
    have hcomp : (Prod.snd ∘ fun f : Fin m → (Fin 4 × Fin 4) × Fin 4 =>
        (fun i => (f i).1, fun i => (f i).2)) = fun outcome i => (outcome i).2 := rfl
    rw [hcomp, ← PMF.pi_map]
    simp only [deal211_map_snd, PMF.pi_uniformOfFintype]
  have hsnd : entropy ((deal211Batch m).map Prod.snd) = 2 * (m : ℝ) := by
    rw [hsnd_eq, entropy_uniform, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      Nat.cast_pow]
    have h4 : ((4 : ℕ) : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h4, ← pow_mul, Real.logb_two_pow]
    push_cast
    ring
  have hfst_eq : (deal211Batch m).map Prod.fst = PMF.pi fun _ : Fin m => deal211.map Prod.fst := by
    dsimp only [deal211Batch]
    rw [PMF.map_comp]
    have hcomp : (Prod.fst ∘ fun f : Fin m → (Fin 4 × Fin 4) × Fin 4 =>
        (fun i => (f i).1, fun i => (f i).2)) = fun outcome i => (outcome i).1 := rfl
    rw [hcomp, ← PMF.pi_map]
  let unseenB : (Fin m → Fin 4 × Fin 4) → Finset (Fin m → Fin 4) :=
    fun as => Fintype.piFinset fun i => unseenOrdered (as i)
  have hfst_supp : ∀ {as : Fin m → Fin 4 × Fin 4},
      as ∈ ((deal211Batch m).map Prod.fst).support →
        ∀ i : Fin m, as i ∈ (deal211.map Prod.fst).support := by
    intro as has i
    rw [hfst_eq, PMF.mem_support_iff, PMF.pi_apply] at has
    exact fun hi => has (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have hcard : ∀ as ∈ ((deal211Batch m).map Prod.fst).support, (unseenB as).card = 2 ^ m := by
    intro as has
    dsimp only [unseenB]
    rw [Fintype.card_piFinset]
    have hc : ∀ i : Fin m, (unseenOrdered (as i)).card = 2 :=
      fun i => unseenOrdered_card (deal211_fst_ne (hfst_supp has i))
    simp only [hc, Finset.prod_const, Finset.card_fin]
  have hzero : ∀ as ∈ ((deal211Batch m).map Prod.fst).support,
      ∀ bs ∉ unseenB as, deal211Batch m (as, bs) = 0 := by
    intro as _ bs hbs
    dsimp only [unseenB] at hbs
    rw [Fintype.mem_piFinset, not_forall] at hbs
    obtain ⟨i, hi⟩ := hbs
    have hdi : deal211 (as i, bs i) = 0 := by
      by_contra hne0
      obtain ⟨_, hb1, hb2⟩ := mem_support_deal211.mp hne0
      exact hi (Finset.mem_erase.mpr ⟨hb2, Finset.mem_erase.mpr ⟨hb1, Finset.mem_univ _⟩⟩)
    rw [deal211Batch_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hdi
  have hconst : ∀ as ∈ ((deal211Batch m).map Prod.fst).support,
      ∀ bs₀ ∈ unseenB as, ∀ bs₁ ∈ unseenB as,
        deal211Batch m (as, bs₁) = deal211Batch m (as, bs₀) := by
    intro as _ bs₀ hbs₀ bs₁ hbs₁
    dsimp only [unseenB] at hbs₀ hbs₁
    rw [Fintype.mem_piFinset] at hbs₀ hbs₁
    rw [deal211Batch_apply, deal211Batch_apply]
    exact Finset.prod_congr rfl fun i _ =>
      deal211_const_on_unseen (as i) (hbs₀ i) (hbs₁ i)
  have hres := mutualInfo_eq_entropy_map_snd_sub_logb_of_const_fiber (deal211Batch m) unseenB
    (2 ^ m) (pow_pos (by norm_num) m) hcard hzero hconst
  rw [hres, hsnd, Nat.cast_pow, Nat.cast_ofNat, Real.logb_two_pow]
  ring

/-- Any protocol realizing `k` independent random OTs with perfect semi-honest privacy over
`m` independent `(2, 1; 1)` card deals (`deal211Batch m`) satisfies `k ≤ m`. -/
theorem rot_le_of_deal211Batch {m k : ℕ} {sc : Schedule 2 noOracleSpec} {Coins : Fin 2 → Type}
    [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    (proto : MPC.Protocol 2 noOracleSpec sc
      (Fin.cases (Fin m → Fin 4 × Fin 4) (fun _ => Fin m → Fin 4)) Coins
      (fun _ => Fin k → Bool × Bool))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc (fun _ => Unit)
        (Fin.cases (Fin m → Fin 4 × Fin 4) (fun _ => Fin m → Fin 4)) Coins
        (fun _ => Fin k → Bool × Bool) I)
    (hPriv : PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (fun _ => dealSource (deal211Batch m)) (rotFunctionality k) S) :
    k ≤ m := by
  have hk := rot_le_mutualInfo proto (deal211Batch m) S hPriv
  rw [mutualInfo_deal211Batch] at hk
  exact Nat.cast_le.mp hk

/-- Any protocol realizing `k` chosen-input OTs with perfect semi-honest privacy over
`m` independent `(2, 1; 1)` card deals (`deal211Batch m`) satisfies `k ≤ m`. -/
theorem chosenOT_le_of_deal211Batch {m k : ℕ} {sc : Schedule 2 noOracleSpec} {Coins : Fin 2 → Type}
    [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    (proto : MPC.Protocol 2 noOracleSpec sc
      (fun i => (batchOTSpec k Bool).Query () i ×
        Fin.cases (Fin m → Fin 4 × Fin 4) (fun _ => Fin m → Fin 4) i)
      Coins ((batchOTSpec k Bool).Answer ()))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc ((batchOTSpec k Bool).Query ())
        (fun i => (batchOTSpec k Bool).Query () i ×
          Fin.cases (Fin m → Fin 4 × Fin 4) (fun _ => Fin m → Fin 4) i)
        Coins ((batchOTSpec k Bool).Answer ()) I)
    (hPriv : PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (dealSourceWithInput (deal211Batch m)) (batchOTFunctionality k Bool) S) :
    k ≤ m := by
  have hk := chosenOT_le_mutualInfo proto (deal211Batch m) S hPriv
  rw [mutualInfo_deal211Batch] at hk
  exact Nat.cast_le.mp hk

/-- Alice's marginal source entropy bounds the number of perfectly private random OTs over any
finite correlated source `source : PMF (A × B)`. -/
theorem rot_le_entropy_fst {sc : Schedule 2 noOracleSpec} {A B : Type} {Coins : Fin 2 → Type}
    [Finite A] [Finite B] [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    {k : ℕ}
    (proto : MPC.Protocol 2 noOracleSpec sc (Fin.cases A (fun _ => B)) Coins
      (fun _ => Fin k → Bool × Bool))
    (source : PMF (A × B))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc (fun _ => Unit) (Fin.cases A (fun _ => B)) Coins
        (fun _ => Fin k → Bool × Bool) I)
    (hPriv : PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (fun _ => dealSource source) (rotFunctionality k) S) :
    (k : ℝ) ≤ entropy (source.map Prod.fst) :=
  (rot_le_mutualInfo proto source S hPriv).trans (mutualInfo_le_entropy_map_fst source)

/-- Bob's marginal source entropy bounds the number of perfectly private random OTs over any
finite correlated source `source : PMF (A × B)`. -/
theorem rot_le_entropy_snd {sc : Schedule 2 noOracleSpec} {A B : Type} {Coins : Fin 2 → Type}
    [Finite A] [Finite B] [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    {k : ℕ}
    (proto : MPC.Protocol 2 noOracleSpec sc (Fin.cases A (fun _ => B)) Coins
      (fun _ => Fin k → Bool × Bool))
    (source : PMF (A × B))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc (fun _ => Unit) (Fin.cases A (fun _ => B)) Coins
        (fun _ => Fin k → Bool × Bool) I)
    (hPriv : PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (fun _ => dealSource source) (rotFunctionality k) S) :
    (k : ℝ) ≤ entropy (source.map Prod.snd) :=
  (rot_le_mutualInfo proto source S hPriv).trans (mutualInfo_le_entropy_map_snd source)

/-- Alice's alphabet bit-length `Real.logb 2 (Fintype.card A)` bounds `k` random OTs over
`source : PMF (A × B)`. -/
theorem rot_le_logb_card_fst {sc : Schedule 2 noOracleSpec} {A B : Type} {Coins : Fin 2 → Type}
    [Fintype A] [Finite B] [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    {k : ℕ}
    (proto : MPC.Protocol 2 noOracleSpec sc (Fin.cases A (fun _ => B)) Coins
      (fun _ => Fin k → Bool × Bool))
    (source : PMF (A × B))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc (fun _ => Unit) (Fin.cases A (fun _ => B)) Coins
        (fun _ => Fin k → Bool × Bool) I)
    (hPriv : PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (fun _ => dealSource source) (rotFunctionality k) S) :
    (k : ℝ) ≤ Real.logb 2 (Fintype.card A) :=
  (rot_le_entropy_fst proto source S hPriv).trans (entropy_le_log_card _)

/-- Bob's alphabet bit-length `Real.logb 2 (Fintype.card B)` bounds `k` random OTs over
`source : PMF (A × B)`. -/
theorem rot_le_logb_card_snd {sc : Schedule 2 noOracleSpec} {A B : Type} {Coins : Fin 2 → Type}
    [Finite A] [Fintype B] [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    {k : ℕ}
    (proto : MPC.Protocol 2 noOracleSpec sc (Fin.cases A (fun _ => B)) Coins
      (fun _ => Fin k → Bool × Bool))
    (source : PMF (A × B))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc (fun _ => Unit) (Fin.cases A (fun _ => B)) Coins
        (fun _ => Fin k → Bool × Bool) I)
    (hPriv : PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (fun _ => dealSource source) (rotFunctionality k) S) :
    (k : ℝ) ≤ Real.logb 2 (Fintype.card B) :=
  (rot_le_entropy_snd proto source S hPriv).trans (entropy_le_log_card _)

end

end Cslib.Crypto.Protocols.OT
