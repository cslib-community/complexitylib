/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Communication.Information
public import CslibFrontier.Probability.MutualInformation.DataProcessing
public import CslibFrontier.Probability.PMF.Independence
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product

/-!
# Information-theoretic upper bound on oblivious transfer from correlated randomness

For a joint law of a correlated source `(A, B)`, Alice's and Bob's final views `(V_A, V_B)`, a
public transcript `T`, and `k` random oblivious transfer (ROT) outputs `(S, R)`:

1. Conditional mutual information satisfies deterministic data processing
   (`condMutualInfo_map_le_of_comp`) and transcript monotonicity
   (`condMutualInfo_map_pair_fst_le_of_eq_zero`, `condMutualInfo_map_pair_snd_le_of_eq_zero`),
   provided in `Cslib.Probability.MutualInformation.DataProcessing`.
2. For `k` independent, correct, and perfectly private random OTs with public transcript `T`, the
   conditional mutual information `I(S; R | T)` equals `k` bits (`condMutualInfo_rot_eq`).
3. Combining data processing and transcript non-increase yields the Ahlswede–Csiszár-style bound
   `k ≤ I(A; B)` (`natCast_le_mutualInfo_of_rot`)
   [AhlswedeCsiszar1993; NascimentoWinter2008; CoverThomas2006].

## Main definitions

* `Cslib.Crypto.Protocols.OT.otSelect`: 1-out-of-2 bit selection from a pair.
* `Cslib.Crypto.Protocols.OT.rotChoices`: receiver choice vector extracted from `k` ROT outputs.
* `Cslib.Crypto.Protocols.OT.rotReceived`: receiver selected bits extracted from `k` ROT outputs.
* `Cslib.Crypto.Protocols.OT.rotUnselected`: sender unselected bits with respect to `rotChoices`.

## Main results

* `Cslib.Crypto.Protocols.OT.condMutualInfo_le_mutualInfo_of_internal_le_external`: bridge from
  `Cslib.Communication.internalInfoCost ≤ Cslib.Communication.externalInfoCost` to
  `I(X; Y | T) ≤ I(X; Y)`.
* `Cslib.Crypto.Protocols.OT.condMutualInfo_rot_eq`: `I(S; R | T) = k` for `k` correct and
  perfectly private random OTs.
* `Cslib.Crypto.Protocols.OT.natCast_le_mutualInfo_of_rot`: the upper bound `(k : ℝ) ≤ I(A; B)`.

## References

* [R. Ahlswede and I. Csiszár, *Common Randomness in Information Theory and Cryptography.
  Part I: Secret Sharing*][AhlswedeCsiszar1993] (bibliographic metadata verified; primary full text
  uninspected; locators unverified).
* [A. C. A. Nascimento and A. Winter, *On the Oblivious-Transfer Capacity of Noisy
  Resources*][NascimentoWinter2008] (bibliographic metadata verified; primary full text uninspected;
  locators unverified).
* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][CoverThomas2006]
  (information-theoretic background; locators unverified).
-/

public section

namespace Cslib.Crypto.Protocols.OT

open Cslib.Probability Cslib.Probability.PMF Cslib.Communication
open scoped ENNReal

variable {Ω α β γ δ τ : Type*}

/-! ### Communication cost bridge and OT observables -/

/-- Bridge from `Cslib.Communication`: whenever `internalInfoCost ≤ externalInfoCost`, the
conditional mutual information between the inputs given the transcript is at most the input
mutual information: `I(X; Y | T) ≤ I(X; Y)`. -/
theorem condMutualInfo_le_mutualInfo_of_internal_le_external [Finite α] [Finite β] [Finite τ]
    (law : PMF (α × β × τ)) (hle : internalInfoCost law ≤ externalInfoCost law) :
    condMutualInfo (law.map fun (x, y, t) => (t, x, y)) ≤
      mutualInfo (law.map fun (x, y, _) => (x, y)) := by
  have hid := externalInfoCost_sub_internalInfoCost law
  linarith

/-! ### Oblivious transfer observables and the `k ≤ I(A; B)` lower bound -/

/-- 1-out-of-2 selection from a pair `pair = (m₀, m₁)` by choice bit `c`. -/
@[expose] def otSelect (pair : Bool × Bool) (c : Bool) : Bool :=
  if c then pair.2 else pair.1

/-- Selecting bit `0` from `pair = (m₀, m₁)` returns `m₀`. -/
@[simp] theorem otSelect_false (pair : Bool × Bool) : otSelect pair false = pair.1 := rfl

/-- Selecting bit `1` from `pair = (m₀, m₁)` returns `m₁`. -/
@[simp] theorem otSelect_true (pair : Bool × Bool) : otSelect pair true = pair.2 := rfl

/-- The receiver choice vector `(c₀, ..., c_{k-1})` extracted from `k` ROT receiver outputs. -/
@[expose] def rotChoices {k : ℕ} (R : Fin k → Bool × Bool) : Fin k → Bool :=
  fun j => (R j).1

/-- The receiver output vector `(y₀, ..., y_{k-1})` extracted from `k` ROT receiver outputs. -/
@[expose] def rotReceived {k : ℕ} (R : Fin k → Bool × Bool) : Fin k → Bool :=
  fun j => (R j).2

/-- The sender's unselected bits `(m_{j, !c_j})_{j < k}` relative to receiver outputs `R`. -/
@[expose] def rotUnselected {k : ℕ} (S R : Fin k → Bool × Bool) : Fin k → Bool :=
  fun j => otSelect (S j) (!(R j).1)

private def bitFlip {k : ℕ} : (Fin k → Bool) ≃ (Fin k → Bool) where
  toFun c j := !(c j)
  invFun c j := !(c j)
  left_inv c := funext fun j => Bool.not_not (c j)
  right_inv c := funext fun j => Bool.not_not (c j)

@[simp] private theorem bitFlip_bitFlip {k : ℕ} (c : Fin k → Bool) :
    bitFlip (bitFlip c) = c :=
  bitFlip.left_inv c

/-- For `k` independent correct and perfectly private random OTs over a public transcript `T`,
the conditional mutual information `I(S; R | T)` equals `k` bits.

Here `hAlicePriv` states that the receiver's choice vector `rotChoices (R ω)` is uniform and
independent of `(S ω, T ω)` (implied by Alice's semi-honest simulation), and `hBobPriv` states
that the sender's unselected bits `rotUnselected (S ω) (R ω)` are uniform and independent of
`(T ω, R ω)` (implied by Bob's semi-honest simulation). -/
theorem condMutualInfo_rot_eq [Finite τ] {k : ℕ} (ν : PMF Ω)
    (T : Ω → τ) (S R : Ω → Fin k → Bool × Bool)
    (hCorrect : ∀ ω ∈ ν.support, ∀ j : Fin k, (R ω j).2 = otSelect (S ω j) (R ω j).1)
    (hAlicePriv : IndepUniform ν (fun ω => (S ω, T ω)) (fun ω => rotChoices (R ω)))
    (hBobPriv : IndepUniform ν (fun ω => (T ω, R ω)) (fun ω => rotUnselected (S ω) (R ω))) :
    condMutualInfo (ν.map fun ω => (T ω, S ω, R ω)) = k := by
  let C : Ω → Fin k → Bool := fun ω => rotChoices (R ω)
  let Y : Ω → Fin k → Bool := fun ω => rotReceived (R ω)
  let U : Ω → Fin k → Bool := fun ω => rotUnselected (S ω) (R ω)
  have hCR : condMutualInfo (ν.map fun ω => (T ω, S ω, R ω)) =
      condMutualInfo (ν.map fun ω => (T ω, S ω, (C ω, Y ω))) := by
    refine (condMutualInfo_map_congr ν T S (T := R) (T' := fun ω => (C ω, Y ω))
      (e := fun r => (rotChoices r, rotReceived r)) ?_ (fun _ _ => rfl)).symm
    intro r r' h
    funext j
    have h1 := congrFun (congrArg Prod.fst h) j
    have h2 := congrFun (congrArg Prod.snd h) j
    exact Prod.ext h1 h2
  rw [hCR, condMutualInfo_map_prodMk_right_eq_add]
  -- Step 1: `I(S; C | T) = 0` from Alice's privacy.
  have hSC : condMutualInfo (ν.map fun ω => (T ω, S ω, C ω)) = 0 := by
    refine condMutualInfo_eq_zero_of_apply_eq_mul _
      (fun t s => (ν.map fun ω => (S ω, T ω)) (s, t))
      (fun _ c => (PMF.uniformOfFintype (Fin k → Bool)) c) fun t s c => ?_
    have hmap : ν.map (fun ω => (T ω, S ω, C ω)) =
        (ν.map fun ω => ((S ω, T ω), C ω)).map fun ((s', t'), c') => (t', s', c') := by
      rw [PMF.map_comp]
      rfl
    rw [hmap, hAlicePriv.map_pair_eq]
    let e : ((Fin k → Bool × Bool) × τ) × (Fin k → Bool) ≃
        τ × (Fin k → Bool × Bool) × (Fin k → Bool) :=
      { toFun := fun ((s', t'), c') => (t', s', c')
        invFun := fun (t', s', c') => ((s', t'), c')
        left_inv := fun ((_, _), _) => rfl
        right_inv := fun (_, _, _) => rfl }
    change ((ν.map fun ω => (S ω, T ω)).bind fun st =>
        (PMF.uniformOfFintype (Fin k → Bool)).map (st, ·)).map e (t, s, c) = _
    rw [map_equiv_apply]
    exact bind_map_prodMk_apply _ _ ((s, t), c)
  -- Step 2: `I(S; Y | (T, C)) = H((T, C), Y) - H(T, C)` because `Y` is determined by `(S, C)`.
  have hSY : condMutualInfo (ν.map fun ω => ((T ω, C ω), S ω, Y ω)) =
      entropy (ν.map fun ω => ((T ω, C ω), Y ω)) - entropy (ν.map fun ω => (T ω, C ω)) := by
    rw [condMutualInfo_map]
    have hdet : entropy (ν.map fun ω => ((T ω, C ω), S ω, Y ω)) =
        entropy (ν.map fun ω => ((T ω, C ω), S ω)) := by
      refine entropy_map_eq_of_comp ν
        (e := fun tcs : (τ × (Fin k → Bool)) × (Fin k → Bool × Bool) =>
          (tcs.1, tcs.2, fun j => otSelect (tcs.2 j) (tcs.1.2 j)))
        (fun s t h => by
          obtain ⟨tc, s⟩ := s
          obtain ⟨tc', s'⟩ := t
          simp only [Prod.mk.injEq] at h
          exact Prod.ext h.1 h.2.1)
        fun ω hω => by
          ext : 1
          · rfl
          · ext : 1
            · rfl
            · funext j
              exact hCorrect ω hω j
    rw [hdet]
    ring
  -- Step 3: Show `((T, C), Y)` is `(T, C) × Unif` by flipping `C` to relate `Y` to `U`.
  have hFlipST : (ν.map fun ω => ((S ω, T ω), C ω)).map (Prod.map id (bitFlip (k := k))) =
      ν.map fun ω => ((S ω, T ω), C ω) := by
    rw [hAlicePriv.map_pair_eq, PMF.map_bind]
    congr 1 with st : 1
    rw [PMF.map_comp]
    have hcomp : Prod.map id (⇑(bitFlip (k := k))) ∘ (fun c => (st, c)) =
        (fun c => (st, c)) ∘ bitFlip := rfl
    rw [hcomp, ← PMF.map_comp, uniformOfFintype_map_equiv bitFlip]
  have hTC_flip : (ν.map fun ω => (T ω, C ω)).map (Prod.map id (bitFlip (k := k))) =
      ν.map fun ω => (T ω, C ω) := by
    have h1 : ν.map (fun ω => (T ω, C ω)) =
        (ν.map fun ω => ((S ω, T ω), C ω)).map fun p => (p.1.2, p.2) := by
      rw [PMF.map_comp]
      rfl
    rw [h1, PMF.map_comp]
    have hcomp :
        (Prod.map id (⇑(bitFlip (k := k))) ∘
          fun p : ((Fin k → Bool × Bool) × τ) × (Fin k → Bool) => (p.1.2, p.2)) =
          (fun p : ((Fin k → Bool × Bool) × τ) × (Fin k → Bool) => (p.1.2, p.2)) ∘
            Prod.map id (⇑(bitFlip (k := k))) := rfl
    rw [hcomp, ← PMF.map_comp, hFlipST]
  have hFlipEq : ν.map (fun ω => ((T ω, bitFlip (C ω)), Y ω)) =
      ν.map (fun ω => ((T ω, C ω), U ω)) := by
    let evalAt : (Fin k → Bool) → (Fin k → Bool × Bool) → (Fin k → Bool) :=
      fun c s j => otSelect (s j) (c j)
    have hLHS : ν.map (fun ω => ((T ω, bitFlip (C ω)), Y ω)) =
        (ν.map fun ω => ((S ω, T ω), C ω)).map fun p =>
          ((p.1.2, bitFlip p.2), evalAt p.2 p.1.1) := by
      rw [PMF.map_comp]
      refine map_congr_on_support ν _ _ fun ω hω => ?_
      exact Prod.ext rfl (funext fun j => hCorrect ω hω j)
    have hRHS : ν.map (fun ω => ((T ω, C ω), U ω)) =
        (ν.map fun ω => ((S ω, T ω), C ω)).map fun p =>
          ((p.1.2, p.2), evalAt (bitFlip p.2) p.1.1) := by
      rw [PMF.map_comp]
      rfl
    rw [hLHS, hRHS]
    conv_rhs => rw [← hFlipST, PMF.map_comp]
    congr 1 with p : 1
    dsimp only [Function.comp_def, Prod.map, id_eq]
    rw [bitFlip_bitFlip]
  have hTCU : IndepUniform ν (fun ω => (T ω, C ω)) U := by
    refine ⟨?_⟩
    have h1 : ν.map (fun ω => ((T ω, C ω), U ω)) =
        (ν.map fun ω => ((T ω, R ω), U ω)).map fun ((t, r), u) => ((t, rotChoices r), u) := by
      rw [PMF.map_comp]
      rfl
    have h2 : ν.map (fun ω => (T ω, C ω)) =
        (ν.map fun ω => (T ω, R ω)).map fun (t, r) => (t, rotChoices r) := by
      rw [PMF.map_comp]
      rfl
    rw [h1, hBobPriv.map_pair_eq, PMF.map_bind]
    conv_rhs => rw [h2, PMF.bind_map]
    congr 1 with ⟨t, r⟩ : 1
    rw [PMF.map_comp]
    rfl
  have hTCY : IndepUniform ν (fun ω => (T ω, C ω)) Y := by
    refine ⟨?_⟩
    have h1 : ν.map (fun ω => ((T ω, C ω), Y ω)) =
        (ν.map fun ω => ((T ω, bitFlip (C ω)), Y ω)).map
          (Prod.map (Prod.map id bitFlip) id) := by
      rw [PMF.map_comp]
      refine congrArg (ν.map ·) (funext fun ω => ?_)
      dsimp only [Function.comp_def, Prod.map, id_eq]
      rw [bitFlip_bitFlip]
    rw [h1, hFlipEq, hTCU.map_pair_eq, PMF.map_bind]
    conv_rhs => rw [← hTC_flip, PMF.bind_map]
    congr 1 with tc : 1
    rw [PMF.map_comp]
    rfl
  rw [hSC, zero_add, hSY, hTCY.map_pair_eq, entropy_prod, entropy_uniform, BitString.logb_card]
  ring

/-- **Ahlswede–Csiszár-style upper bound on oblivious transfer from correlated randomness**:
any two-party public-transcript execution over correlated source `(A, B)` whose views satisfy
`I(V_A; V_B | T) ≤ I(A; B)` and that produces `k` independent, correct, perfectly semi-honest
private random OTs satisfies `(k : ℝ) ≤ I(A; B)`. -/
theorem natCast_le_mutualInfo_of_rot
    [Finite α] [Finite β] [Finite γ] [Finite δ] [Finite τ] {k : ℕ} (ν : PMF Ω)
    (A : Ω → α) (B : Ω → β) (VA : Ω → γ) (VB : Ω → δ) (T : Ω → τ)
    (S R : Ω → Fin k → Bool × Bool)
    (hTranscript : condMutualInfo (ν.map fun ω => (T ω, VA ω, VB ω)) ≤
      mutualInfo (ν.map fun ω => (A ω, B ω)))
    (outA : γ → Fin k → Bool × Bool) (hOutA : ∀ ω ∈ ν.support, S ω = outA (VA ω))
    (outB : δ → Fin k → Bool × Bool) (hOutB : ∀ ω ∈ ν.support, R ω = outB (VB ω))
    (hCorrect : ∀ ω ∈ ν.support, ∀ j : Fin k, (R ω j).2 = otSelect (S ω j) (R ω j).1)
    (hAlicePriv : IndepUniform ν (fun ω => (S ω, T ω)) (fun ω => rotChoices (R ω)))
    (hBobPriv : IndepUniform ν (fun ω => (T ω, R ω)) (fun ω => rotUnselected (S ω) (R ω))) :
    (k : ℝ) ≤ mutualInfo (ν.map fun ω => (A ω, B ω)) := by
  calc (k : ℝ)
      = condMutualInfo (ν.map fun ω => (T ω, S ω, R ω)) :=
        (condMutualInfo_rot_eq ν T S R hCorrect hAlicePriv hBobPriv).symm
    _ ≤ condMutualInfo (ν.map fun ω => (T ω, VA ω, VB ω)) :=
        condMutualInfo_map_le_of_comp ν T VA S VB R outA hOutA outB hOutB
    _ ≤ mutualInfo (ν.map fun ω => (A ω, B ω)) := hTranscript

end Cslib.Crypto.Protocols.OT
