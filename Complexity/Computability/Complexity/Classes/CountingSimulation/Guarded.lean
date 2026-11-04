/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.Interfaces
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.DirectContraction
public import Complexity.Computability.GenericRAM.Native.Combinators

/-!
# A contraction algorithm from a guarded fast algorithm

The contraction interface (`Cslib.Complexity.CountingSimulation.ContractionAlgorithm`) quantifies
its admissibility constants `C` and `D` after the machine, so a machine cannot test them. For
explicit networks, a contraction algorithm is assembled from a fast machine that is correct and
within the interface's bounds on the inputs passing a polynomial-time guard that does not mention
`C` and `D`, and from direct summation (`ExplicitTensorNetwork.directContractionBinaryCertificate`)
elsewhere (`ContractionAlgorithm.ofGuarded`). This needs only that admissible networks have at most
`C s` edges and that, for each `C`, the admissible networks failing the guard have bounded size `s`:
there direct summation costs `2 ^ (C s₀)` times a polynomial, a constant factor.

In the contraction theorem of [OpenAI2026ETH] (Theorem D.1, with the proof of Appendix D.4), the
guard is the degree bound `⌈m ^ (9/10)⌉` in the number `m` of edges, and a network of degree at
most `C ⌊log₂ s⌋` fails it only for `s` below a threshold depending on `C`. The recursion of
Appendix D.4 then needs to be fast only on networks passing the guard.

## Main definitions

* `Cslib.Complexity.CountingSimulation.ContractionAlgorithm.ofGuarded`: the assembled algorithm.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53).
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.ExplicitTensorNetwork Cslib.GenericRAM
  Turing.MultiTapeTM

/-- The encoding of an explicit network with its number of rows. -/
local notation "encG" => encPair encNat encExplicitNetwork

/-- Absorb a constant factor and a smaller exponent: `c₁ (n + 1) ^ e₁ + c₂ (n + 1) ^ e₂ 2 ^ x ≤
K (n + 1) ^ K 2 ^ x` for `c₁ + c₂ ≤ K` and `e₁, e₂ ≤ K`. -/
private theorem absorb_le {n c₁ c₂ e₁ e₂ K x : ℕ} (hc : c₁ + c₂ ≤ K) (he₁ : e₁ ≤ K)
    (he₂ : e₂ ≤ K) :
    c₁ * (n + 1) ^ e₁ + c₂ * (n + 1) ^ e₂ * 2 ^ x ≤ K * (n + 1) ^ K * 2 ^ x := by
  have h1 : (n + 1) ^ e₁ ≤ (n + 1) ^ K := Nat.pow_le_pow_right (Nat.succ_pos _) he₁
  have h2 : (n + 1) ^ e₂ ≤ (n + 1) ^ K := Nat.pow_le_pow_right (Nat.succ_pos _) he₂
  have h3 : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  calc c₁ * (n + 1) ^ e₁ + c₂ * (n + 1) ^ e₂ * 2 ^ x
      ≤ c₁ * ((n + 1) ^ K * 2 ^ x) + c₂ * ((n + 1) ^ K * 2 ^ x) := by
        refine Nat.add_le_add (Nat.mul_le_mul_left _ (h1.trans (Nat.le_mul_of_pos_right _ h3)))
          ?_
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)
    _ = (c₁ + c₂) * ((n + 1) ^ K * 2 ^ x) := by ring
    _ ≤ K * ((n + 1) ^ K * 2 ^ x) := Nat.mul_le_mul_right _ hc
    _ = K * (n + 1) ^ K * 2 ^ x := by ring

/-- **A contraction algorithm from a guarded fast algorithm.** Let `fast` compute the contraction
modulo `2 ^ P` on the networks passing a polynomial-time `guard`, within the interface's bounds on
the admissible ones. If admissible networks have at most `C s` edges, and for each `C` the
admissible networks failing the guard have bounded size `s`, then branching on the guard to `fast`
or to direct summation is a contraction algorithm. -/
noncomputable def ContractionAlgorithm.ofGuarded
    {Adm : ℕ → ℕ → ℕ × ExplicitTensorNetwork ℕ → Prop}
    {guard : ℕ × ExplicitTensorNetwork ℕ → Bool}
    (hguard : ComputableInPolyTime guard encG encBool)
    {f : ℕ × (ℕ × ExplicitTensorNetwork ℕ) → ℕ}
    (fast : NativeCertificate f (encPair encNat encG) encNat)
    (hcorrect : ∀ P G, guard G = true → f (P, G) = G.2.contraction % 2 ^ P)
    (hbound : ∀ C D : ℕ, ∃ K : ℕ, ∀ (s P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ), 2 ≤ s →
      1 ≤ P → P ≤ D * s → Adm C s G → guard G = true →
      fast.time (P, G) ≤ K * ((encPair encNat encG (P, G)).length + 1) ^ K *
          2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) ∧
        fast.space (P, G) ≤ K * ((encPair encNat encG (P, G)).length + 1) ^ K)
    (hedges : ∀ C s G, Adm C s G → G.2.numEdges ≤ C * s)
    (hsmall : ∀ C, ∃ s₀, ∀ s G, Adm C s G → guard G = false → s ≤ s₀) :
    ContractionAlgorithm encG (fun G => G.2.contraction) Adm where
  certificate :=
    (NativeCertificate.branch
      (NativeCertificate.ofPolyTime (hguard.comp (ComputableInPolyTime.snd encNat encG)))
      fast directContractionBinaryCertificate).congr fun p => by
        split
        · next h => exact hcorrect p.1 p.2 h
        · rfl
  bound C D := by
    have ht := NativeCertificate.ofPolyTime_isPolynomial
      (hguard.comp (ComputableInPolyTime.snd encNat encG))
    obtain ⟨ct, dt, hct⟩ := ht.1.exists_le
    obtain ⟨cs, ds, hcs⟩ := ht.2.exists_le
    obtain ⟨K₁, hK₁⟩ := hbound C D
    obtain ⟨K₂, hK₂⟩ := exists_directContractionBinaryCertificate_le
    obtain ⟨s₀, hs₀⟩ := hsmall C
    refine ⟨ct + cs + dt + ds + K₁ + K₂ * 2 ^ (C * s₀) + K₂, fun s P G hs hP hPD hA => ?_⟩
    set K := ct + cs + dt + ds + K₁ + K₂ * 2 ^ (C * s₀) + K₂
    have hct' := hct (P, G)
    have hcs' := hcs (P, G)
    obtain ⟨hdt, hds⟩ := hK₂ (P, G)
    have hfast : guard G = true →
        fast.time (P, G) ≤ K₁ * ((encPair encNat encG (P, G)).length + 1) ^ K₁ *
            2 ^ (K₁ * s / Nat.sqrt (Nat.log 2 s)) ∧
          fast.space (P, G) ≤ K₁ * ((encPair encNat encG (P, G)).length + 1) ^ K₁ :=
      hK₁ s P G hs hP hPD hA
    set n := (encPair encNat encG (P, G)).length
    change (NativeCertificate.ofPolyTime (hguard.comp (ComputableInPolyTime.snd encNat encG))).time
        (P, G) + (if guard G = true then fast.time (P, G)
          else directContractionBinaryCertificate.time (P, G)) ≤ _ ∧
      (NativeCertificate.ofPolyTime (hguard.comp (ComputableInPolyTime.snd encNat encG))).space
        (P, G) + (if guard G = true then fast.space (P, G)
          else directContractionBinaryCertificate.space (P, G)) ≤ _
    have hpowK {e : ℕ} (he : e ≤ K) : (n + 1) ^ e ≤ (n + 1) ^ K :=
      Nat.pow_le_pow_right (Nat.succ_pos _) he
    cases hg : guard G
    · -- The guard fails: `s ≤ s₀`, so direct summation costs a constant factor.
      have hsm := hs₀ s G hA hg
      have hm : G.2.numEdges ≤ C * s₀ :=
        (hedges C s G hA).trans (Nat.mul_le_mul_left _ hsm)
      simp only [Bool.false_eq_true, ite_false]
      have h2m : 2 ^ G.2.numEdges ≤ 2 ^ (C * s₀) := Nat.pow_le_pow_right (by norm_num) hm
      have hdt' : directContractionBinaryCertificate.time (P, G) ≤
          K₂ * 2 ^ (C * s₀) * (n + 1) ^ K₂ * 2 ^ 0 := by
        refine hdt.trans ?_
        rw [pow_zero, Nat.mul_one]
        calc K₂ * (n + 1) ^ K₂ * 2 ^ G.2.numEdges
            ≤ K₂ * (n + 1) ^ K₂ * 2 ^ (C * s₀) := Nat.mul_le_mul_left _ h2m
          _ = K₂ * 2 ^ (C * s₀) * (n + 1) ^ K₂ := by ring
      constructor
      · have habs := absorb_le (n := n) (c₁ := ct) (c₂ := K₂ * 2 ^ (C * s₀)) (e₁ := dt)
          (e₂ := K₂) (K := K) (x := 0) (by omega) (by omega) (by omega)
        have hexp : K * (n + 1) ^ K * 2 ^ 0 ≤
            K * (n + 1) ^ K * 2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.zero_le _))
        have := hdt'
        omega
      · have h1 := Nat.mul_le_mul_left cs (hpowK (show ds ≤ K by omega))
        have h2 := Nat.mul_le_mul_left K₂ (hpowK (show K₂ ≤ K by omega))
        have h3 : (cs + K₂) * (n + 1) ^ K ≤ K * (n + 1) ^ K :=
          Nat.mul_le_mul_right _ (by omega)
        have e : (cs + K₂) * (n + 1) ^ K = cs * (n + 1) ^ K + K₂ * (n + 1) ^ K := by ring
        omega
    · -- The guard holds: the fast bound.
      obtain ⟨hft, hfs⟩ := hfast hg
      simp only [ite_true]
      constructor
      · have hx : K₁ * s / Nat.sqrt (Nat.log 2 s) ≤ K * s / Nat.sqrt (Nat.log 2 s) :=
          Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))
        have hft' : fast.time (P, G) ≤ K₁ * (n + 1) ^ K₁ * 2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) :=
          hft.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hx))
        have habs := absorb_le (n := n) (c₁ := ct) (c₂ := K₁) (e₁ := dt) (e₂ := K₁) (K := K)
          (x := K * s / Nat.sqrt (Nat.log 2 s)) (by omega) (by omega) (by omega)
        omega
      · have h1 := Nat.mul_le_mul_left cs (hpowK (show ds ≤ K by omega))
        have h2 := Nat.mul_le_mul_left K₁ (hpowK (show K₁ ≤ K by omega))
        have h3 : (cs + K₁) * (n + 1) ^ K ≤ K * (n + 1) ^ K :=
          Nat.mul_le_mul_right _ (by omega)
        have e : (cs + K₁) * (n + 1) ^ K = cs * (n + 1) ^ K + K₁ * (n + 1) ^ K := by ring
        omega

end Cslib.Complexity.CountingSimulation
