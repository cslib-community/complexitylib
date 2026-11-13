/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.OT.CorrelatedBound.DealClient
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.NormNum

/-!
# Tests: information-theoretic OT upper bounds from correlated randomness

* Tight impossibility on `(2, 1; 1)` deals: no semi-honest private `MPC.Protocol` over `deal211`
  or `deal211Unordered` realizes `2` random OTs (`rotFunctionality 2`) or `2` chosen-input OTs
  (`batchOTFunctionality 2 Bool`), and `m + 1` OTs are impossible over `deal211Batch m`, with
  matching `Communication.Protocol` and `Communication.PrivateCoin` `deal211` bounds.
* Nonvacuous `1`-OT achievability: Beaver's 1-round tetrahedral `MPC.Protocol` realizes
  `rotFunctionality 1` with `PerfectSemiHonestPrivateProperWithSetup` over `dealSource deal211`,
  and a depth-`3`
  `Communication.PrivateCoin 1 0` protocol witnesses the `1`-ROT privacy and correctness hypotheses
  of `privateCoin_rot_le_one_of_deal211` and `commProtocol_rot_le_mutualInfo`.
* Negative non-private counterexample: over the trivial source `PMF.pure ((), ())` of mutual
  information `0`, a deterministic non-private protocol can produce `2` correlated ROT-shaped pairs.
-/

namespace CslibFrontierTests.CorrelatedOTBound

open Cslib
open Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.MPC
open Cslib.Crypto.Protocols.OT
open Cslib.Probability
open Cslib.Probability.PMF

/-! ### Impossibility on `(2, 1; 1)` deal sources -/

/-- No perfectly semi-honest private protocol over `deal211` can realize `2` random OTs. -/
example {sc : Schedule 2 noOracleSpec} {Coins : Fin 2 → Type}
    [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    (proto : MPC.Protocol 2 noOracleSpec sc (Fin.cases (Fin 4 × Fin 4) (fun _ => Fin 4)) Coins
      (fun _ => Fin 2 → Bool × Bool))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc (fun _ => Unit) (Fin.cases (Fin 4 × Fin 4) (fun _ => Fin 4)) Coins
        (fun _ => Fin 2 → Bool × Bool) I) :
    ¬ PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (fun _ => dealSource deal211) (rotFunctionality 2) S := by
  intro hPriv
  have hle := rot_le_one_of_deal211 proto S hPriv
  omega

/-- No perfectly semi-honest private protocol over `deal211` can realize `2` chosen-input OTs. -/
example {sc : Schedule 2 noOracleSpec} {Coins : Fin 2 → Type}
    [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    (proto : MPC.Protocol 2 noOracleSpec sc
      (fun i => (batchOTSpec 2 Bool).Query () i × Fin.cases (Fin 4 × Fin 4) (fun _ => Fin 4) i)
      Coins ((batchOTSpec 2 Bool).Answer ()))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc ((batchOTSpec 2 Bool).Query ())
        (fun i => (batchOTSpec 2 Bool).Query () i × Fin.cases (Fin 4 × Fin 4) (fun _ => Fin 4) i)
        Coins ((batchOTSpec 2 Bool).Answer ()) I) :
    ¬ PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (dealSourceWithInput deal211) (batchOTFunctionality 2 Bool) S := by
  intro hPriv
  have hle := chosenOT_le_one_of_deal211 proto S hPriv
  omega

/-- No perfectly semi-honest private protocol over `deal211Unordered` realizes `2` random OTs. -/
example {sc : Schedule 2 noOracleSpec} {Coins : Fin 2 → Type}
    [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    (proto : MPC.Protocol 2 noOracleSpec sc
      (Fin.cases {s : Finset (Fin 4) // s.card = 2} (fun _ => Fin 4)) Coins
      (fun _ => Fin 2 → Bool × Bool))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc (fun _ => Unit)
        (Fin.cases {s : Finset (Fin 4) // s.card = 2} (fun _ => Fin 4)) Coins
        (fun _ => Fin 2 → Bool × Bool) I) :
    ¬ PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (fun _ => dealSource deal211Unordered) (rotFunctionality 2) S := by
  intro hPriv
  have hle := rot_le_one_of_deal211Unordered proto S hPriv
  omega

/-- No perfectly semi-honest private protocol over `m` independent `(2, 1; 1)` deals can
realize `m + 1` random OTs. -/
example {m : ℕ} {sc : Schedule 2 noOracleSpec} {Coins : Fin 2 → Type}
    [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    (proto : MPC.Protocol 2 noOracleSpec sc
      (Fin.cases (Fin m → Fin 4 × Fin 4) (fun _ => Fin m → Fin 4)) Coins
      (fun _ => Fin (m + 1) → Bool × Bool))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc (fun _ => Unit)
        (Fin.cases (Fin m → Fin 4 × Fin 4) (fun _ => Fin m → Fin 4)) Coins
        (fun _ => Fin (m + 1) → Bool × Bool) I) :
    ¬ PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (fun _ => dealSource (deal211Batch m)) (rotFunctionality (m + 1)) S := by
  intro hPriv
  have hle := rot_le_of_deal211Batch proto S hPriv
  omega

/-- `deal211` has strictly positive mutual information `1` bit (`k = 0` and `k = 1` are not
ruled out by the bound). -/
example : (1 : ℝ) ≤ mutualInfo deal211 ∧ mutualInfo deal211 < 2 := by
  rw [mutualInfo_deal211]
  norm_num

/-! ### Nonvacuous `1`-OT achievability: Beaver's tetrahedral protocol on `deal211` -/

private def otherList (a₀ a₁ : Fin 4) : List (Fin 4) :=
  ([0, 1, 2, 3] : List (Fin 4)).filter fun x => x != a₀ && x != a₁

private def otherTwo (a₀ a₁ : Fin 4) : Fin 4 × Fin 4 :=
  match otherList a₀ a₁ with
  | [u, v] => (u, v)
  | _ => (0, 0)

private def sortedPair (x y : Fin 4) : Fin 4 × Fin 4 :=
  if x ≤ y then (x, y) else (y, x)

private theorem sortedPair_comm {x y : Fin 4} : sortedPair x y = sortedPair y x := by
  revert x y
  decide

private theorem otherTwo_spec :
    ∀ a₀ a₁ b d : Fin 4, a₀ ≠ a₁ → b ≠ a₀ → b ≠ a₁ → d ≠ a₀ → d ≠ a₁ → b ≠ d →
      otherTwo a₀ a₁ = (b, d) ∨ otherTwo a₀ a₁ = (d, b) := by
  decide

private theorem sortedPair_fst_eq {a b : Fin 4} (h : a ≠ b) :
    decide (b = (sortedPair a b).1) = decide (b < a) := by
  revert a b h
  decide

private theorem decide_lt_swap {x y : Fin 4} (h : x ≠ y) :
    decide (x < y) = !decide (y < x) := by
  revert x y h
  decide

private theorem beaver_mem_sortedPair_iff :
    ∀ a₀ a₁ b d : Fin 4, a₀ ≠ a₁ → b ≠ a₀ → b ≠ a₁ → d ≠ a₀ → d ≠ a₁ → b ≠ d →
      decide (b = (sortedPair a₁ d).1 ∨ b = (sortedPair a₁ d).2) = false ∧
        decide (b = (sortedPair a₁ b).1 ∨ b = (sortedPair a₁ b).2) = true := by
  decide

private abbrev beaverMsg : Type := (Fin 4 × Fin 4) × (Fin 4 × Fin 4) × Bool × Bool
private abbrev beaverSchedule : Schedule 2 noOracleSpec := [Round.message 0 1 beaverMsg]
private abbrev beaverCoins : Fin 2 → Type := fun _ => Bool × Bool × Bool
private abbrev defaultCoins : Bool × Bool × Bool := (false, false, false)
private abbrev beaverOut : Fin 2 → Type := fun _ => Fin 1 → Bool × Bool
private abbrev beaverIn : Fin 2 → Type := Fin.cases (Fin 4 × Fin 4) (fun _ => Fin 4)

private def beaverSend :
    (Fin 4 × Fin 4) × (Bool × Bool × Bool) → beaverMsg
  | (a, (r, m₀, m₁)) =>
    let (u, v) := otherTwo a.1 a.2
    let w := if r then (v, u) else (u, v)
    (sortedPair a.1 w.1, sortedPair a.2 w.2, m₀, m₁)

private def beaverSendStep : beaverIn 0 × beaverCoins 0 → beaverMsg :=
  fun st => beaverSend (st.1, st.2)

private def beaverOut0 : (Fin 4 × Fin 4) × (Bool × Bool × Bool) → Fin 1 → Bool × Bool
  | (a, coins), _ =>
    let (u, v) := otherTwo a.1 a.2
    let w := if coins.1 then (v, u) else (u, v)
    (xor coins.2.1 (decide (w.1 < a.1)), xor coins.2.2 (decide (w.2 < a.2)))

private def beaverOut1 : Fin 4 × beaverMsg → Fin 1 → Bool × Bool
  | (b, (p₀, p₁, m₀, m₁)), _ =>
    let c := decide (b = p₁.1 ∨ b = p₁.2)
    let p := if c then p₁ else p₀
    let m := if c then m₁ else m₀
    (c, xor m (decide (b = p.1)))

private def beaverOutputFn :
    (i : Fin 2) →
      (beaverIn i × beaverCoins i) ×
        (Round.message (m := 2) (spec := noOracleSpec) 0 1 beaverMsg).Received i →
      beaverOut i
  | ⟨0, _⟩, ((a, coins), _) => beaverOut0 (a, coins)
  | ⟨1, _⟩, ((b, _), recv) => beaverOut1 (b, recv rfl)

private noncomputable def beaverOTProtocol :
    MPC.Protocol 2 noOracleSpec beaverSchedule beaverIn beaverCoins beaverOut where
  sampleCoins := fun i =>
    if i = 0 then ProbComp.uniform (Bool × Bool × Bool) else pure defaultCoins
  steps := Steps.message (sender := 0) (receiver := 1) (Msg := beaverMsg) beaverSendStep
    (Steps.done beaverOutputFn)

private def beaverView0 (a : Fin 4 × Fin 4) (coins : Bool × Bool × Bool) :
    PartyView beaverIn beaverCoins beaverSchedule 0 :=
  { input := a
    coins := coins
    received := (fun h => False.elim (zero_ne_one h), ()) }

private def beaverView1 (b : Fin 4) (msg : beaverMsg) :
    PartyView beaverIn beaverCoins beaverSchedule 1 :=
  { input := b
    coins := defaultCoins
    received := (fun _ => msg, ()) }

private noncomputable def beaverSim :
    (I : Finset (Fin 2)) →
      SetupSimulator beaverSchedule (fun _ => Unit) beaverIn beaverCoins beaverOut I
  | I => fun _ out =>
    if h0 : (0 : Fin 2) ∈ I then
      if h1 : (1 : Fin 2) ∈ I then
        pure fun ⟨i, _⟩ => match i with
          | ⟨0, _⟩ => beaverView0 (0, 1) (false, false, false)
          | ⟨1, _⟩ => beaverView1 2 ((0, 2), (1, 3), false, false)
      else do
        let ρ ← ProbComp.uniform (Equiv.Perm (Fin 4))
        let a := (ρ 0, ρ 1)
        let (u, v) := otherTwo a.1 a.2
        let s := out ⟨0, h0⟩ 0
        (fun r : Bool =>
          let w := if r then (v, u) else (u, v)
          let m₀ := xor s.1 (decide (w.1 < a.1))
          let m₁ := xor s.2 (decide (w.2 < a.2))
          fun ⟨i, hi⟩ =>
            if hi0 : i = 0 then hi0 ▸ beaverView0 a (r, m₀, m₁)
            else False.elim (by
              fin_cases i
              · exact hi0 rfl
              · exact h1 hi)) <$> ProbComp.uniform Bool
    else if h1 : (1 : Fin 2) ∈ I then do
      let ρ ← ProbComp.uniform (Equiv.Perm (Fin 4))
      let oy := out ⟨1, h1⟩ 0
      let c := oy.1
      let y := oy.2
      let b := ρ 2
      let p₀ := if c then sortedPair (ρ 0) (ρ 3) else sortedPair (ρ 0) (ρ 2)
      let p₁ := if c then sortedPair (ρ 1) (ρ 2) else sortedPair (ρ 1) (ρ 3)
      (fun mOther : Bool =>
        let m₀ := if c then mOther else xor y (decide (ρ 2 < ρ 0))
        let m₁ := if c then xor y (decide (ρ 2 < ρ 1)) else mOther
        fun ⟨i, hi⟩ =>
          if hi1 : i = 1 then hi1 ▸ beaverView1 b (p₀, p₁, m₀, m₁)
          else False.elim (by
            fin_cases i
            · exact h0 hi
            · exact hi1 rfl)) <$> ProbComp.uniform Bool
    else
      pure fun ⟨i, hi⟩ => False.elim (by
        fin_cases i
        · exact h0 hi
        · exact h1 hi)

private def rFlip (ρ : Equiv.Perm (Fin 4)) : Bool :=
  decide ((otherTwo (ρ 0) (ρ 1)).1 ≠ ρ 2)

private theorem rFlip_eq_false_of {ρ : Equiv.Perm (Fin 4)} (h : otherTwo (ρ 0) (ρ 1) = (ρ 2, ρ 3)) :
    rFlip ρ = false := by
  rw [rFlip, h]
  exact decide_eq_false (not_not.mpr rfl)

private theorem rFlip_eq_true_of {ρ : Equiv.Perm (Fin 4)} (h : otherTwo (ρ 0) (ρ 1) = (ρ 3, ρ 2)) :
    rFlip ρ = true := by
  rw [rFlip, h]
  exact decide_eq_true (ρ.injective.ne (by decide : (3 : Fin 4) ≠ 2))

private theorem w1_of_rFlip (ρ : Equiv.Perm (Fin 4)) (b : Bool) :
    (if xor b (rFlip ρ) then (otherTwo (ρ 0) (ρ 1)).2 else (otherTwo (ρ 0) (ρ 1)).1) =
      if b then ρ 3 else ρ 2 := by
  have hne : ∀ i j : Fin 4, i ≠ j → ρ i ≠ ρ j := fun i j hij => ρ.injective.ne hij
  rcases otherTwo_spec (ρ 0) (ρ 1) (ρ 2) (ρ 3) (hne 0 1 (by decide)) (hne 2 0 (by decide))
    (hne 2 1 (by decide)) (hne 3 0 (by decide)) (hne 3 1 (by decide)) (hne 2 3 (by decide)) with
    huv | huv
  · rw [rFlip_eq_false_of huv, huv]
    cases b <;> rfl
  · rw [rFlip_eq_true_of huv, huv]
    cases b <;> rfl

private theorem w2_of_rFlip (ρ : Equiv.Perm (Fin 4)) (b : Bool) :
    (if xor b (rFlip ρ) then (otherTwo (ρ 0) (ρ 1)).1 else (otherTwo (ρ 0) (ρ 1)).2) =
      if b then ρ 2 else ρ 3 := by
  have hne : ∀ i j : Fin 4, i ≠ j → ρ i ≠ ρ j := fun i j hij => ρ.injective.ne hij
  rcases otherTwo_spec (ρ 0) (ρ 1) (ρ 2) (ρ 3) (hne 0 1 (by decide)) (hne 2 0 (by decide))
    (hne 2 1 (by decide)) (hne 3 0 (by decide)) (hne 3 1 (by decide)) (hne 2 3 (by decide)) with
    huv | huv
  · rw [rFlip_eq_false_of huv, huv]
    cases b <;> rfl
  · rw [rFlip_eq_true_of huv, huv]
    cases b <;> rfl

private def swapPerm23 (ρ : Equiv.Perm (Fin 4)) (flip : Bool) : Equiv.Perm (Fin 4) :=
  if flip then ρ * Equiv.swap 2 3 else ρ

private theorem swapPerm23_0 (ρ : Equiv.Perm (Fin 4)) (flip : Bool) :
    swapPerm23 ρ flip 0 = ρ 0 := by
  cases flip
  · rfl
  · simp only [swapPerm23, ↓reduceIte, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 3)]

private theorem swapPerm23_1 (ρ : Equiv.Perm (Fin 4)) (flip : Bool) :
    swapPerm23 ρ flip 1 = ρ 1 := by
  cases flip
  · rfl
  · simp only [swapPerm23, ↓reduceIte, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 3)]

private theorem swapPerm23_2 (ρ : Equiv.Perm (Fin 4)) (flip : Bool) :
    swapPerm23 ρ flip 2 = if flip then ρ 3 else ρ 2 := by
  cases flip
  · rfl
  · simp only [swapPerm23, ↓reduceIte, Equiv.Perm.mul_apply, Equiv.swap_apply_left]

private theorem swapPerm23_invol (ρ : Equiv.Perm (Fin 4)) (flip : Bool) :
    swapPerm23 (swapPerm23 ρ flip) flip = ρ := by
  cases flip
  · rfl
  · have hsq : Equiv.swap (2 : Fin 4) 3 * Equiv.swap 2 3 = 1 := by decide
    simp only [swapPerm23, ↓reduceIte, mul_assoc, hsq, mul_one]

private def swapPerm03 (ρ : Equiv.Perm (Fin 4)) (flip : Bool) : Equiv.Perm (Fin 4) :=
  if flip then ρ * Equiv.swap 0 3 else ρ

private def swapPerm13 (ρ : Equiv.Perm (Fin 4)) (flip : Bool) : Equiv.Perm (Fin 4) :=
  if flip then ρ * Equiv.swap 1 3 else ρ

private theorem swapPerm03_invol (ρ : Equiv.Perm (Fin 4)) (flip : Bool) :
    swapPerm03 (swapPerm03 ρ flip) flip = ρ := by
  cases flip
  · rfl
  · have hsq : Equiv.swap (0 : Fin 4) 3 * Equiv.swap 0 3 = 1 := by decide
    simp only [swapPerm03, ↓reduceIte, mul_assoc, hsq, mul_one]

private theorem swapPerm13_invol (ρ : Equiv.Perm (Fin 4)) (flip : Bool) :
    swapPerm13 (swapPerm13 ρ flip) flip = ρ := by
  cases flip
  · rfl
  · have hsq : Equiv.swap (1 : Fin 4) 3 * Equiv.swap 1 3 = 1 := by decide
    simp only [swapPerm13, ↓reduceIte, mul_assoc, hsq, mul_one]

private theorem realCorrelated_beaverOTProtocol :
    realCorrelated beaverOTProtocol deal211 =
      (PMF.uniformOfFintype (Equiv.Perm (Fin 4))).bind fun ρ =>
        (PMF.uniformOfFintype (Bool × Bool × Bool)).map fun rmm =>
          let v0 := beaverView0 (ρ 0, ρ 1) rmm
          let v1 := beaverView1 (ρ 2) (beaverSend ((ρ 0, ρ 1), rmm))
          let views : (i : Fin 2) → PartyView beaverIn beaverCoins beaverSchedule i :=
            fun i => match i with | ⟨0, _⟩ => v0 | ⟨1, _⟩ => v1
          let out : (i : Fin 2) → beaverOut i :=
            fun i => match i with
              | ⟨0, _⟩ => beaverOutputFn 0 ((v0.input, v0.coins), v0.received.1)
              | ⟨1, _⟩ => beaverOutputFn 1 ((v1.input, v1.coins), v1.received.1)
          (views, out) := by
  rw [realCorrelated, deal211, PMF.bind_map]
  dsimp only [Function.comp_def]
  congr 1 with ρ : 1
  rw [Protocol.evalWith_eq, ProbComp.eval_pi]
  have hpi : (PMF.pi fun i : Fin 2 => (beaverOTProtocol.sampleCoins i).eval) =
      (PMF.uniformOfFintype (Bool × Bool × Bool)).map
        (fun rmm i => if i = 0 then rmm else defaultCoins) := by
    ext coins
    rw [PMF.pi_apply, Fin.prod_univ_two]
    have ha : (beaverOTProtocol.sampleCoins 0).eval =
        PMF.uniformOfFintype (Bool × Bool × Bool) := ProbComp.eval_uniform _
    have hc : (beaverOTProtocol.sampleCoins 1).eval = PMF.pure defaultCoins := ProbComp.eval_pure _
    rw [ha, hc, PMF.pure_apply]
    classical
    by_cases hc1 : coins 1 = defaultCoins
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc1), mul_one, PMF.map_apply,
        tsum_eq_single (coins 0)]
      · have hfun : coins = fun i : Fin 2 => if i = 0 then coins 0 else defaultCoins := by
          funext i
          fin_cases i
          · rfl
          · exact hc1
        rw [ite_eq_left_of_eq_true _ _ (eq_true hfun)]
      · intro x hx
        rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hx (congrFun h 0).symm)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc1), mul_zero, PMF.map_apply]
      rw [tsum_eq_sum (s := (∅ : Finset (Bool × Bool × Bool)))]
      · exact Finset.sum_empty.symm
      · intro x _
        rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hc1 (congrFun h 1))]
  rw [hpi, PMF.bind_map]
  simp only [beaverOTProtocol, Function.comp_def]
  simp only [Steps.evalWith_message, Steps.evalWith_done, PMF.pure_map]
  refine congrArg (PMF.bind (PMF.uniformOfFintype (Bool × Bool × Bool))) (funext fun rmm => ?_)
  dsimp only [PMF.map, Function.comp_def, beaverSendStep]
  refine congrArg PMF.pure (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
  · fin_cases i
    · refine PartyView.ext rfl rfl ?_
      exact Prod.ext (funext fun h => False.elim (zero_ne_one h)) rfl
    · refine PartyView.ext rfl rfl ?_
      exact Prod.ext rfl rfl
  · fin_cases i <;> rfl

private theorem beaverOut_eval (ρ : Equiv.Perm (Fin 4)) (b m₀ m₁ : Bool) :
    let s₀ := xor m₀ (decide ((if b then ρ 3 else ρ 2) < ρ 0))
    let s₁ := xor m₁ (decide ((if b then ρ 2 else ρ 3) < ρ 1))
    beaverOutputFn 0
        (((beaverView0 (ρ 0, ρ 1) (xor b (rFlip ρ), m₀, m₁)).input,
          (beaverView0 (ρ 0, ρ 1) (xor b (rFlip ρ), m₀, m₁)).coins),
          (beaverView0 (ρ 0, ρ 1) (xor b (rFlip ρ), m₀, m₁)).received.1) =
        (fun _ => (s₀, s₁)) ∧
      beaverOutputFn 1
        (((beaverView1 (ρ 2) (beaverSend ((ρ 0, ρ 1), (xor b (rFlip ρ), m₀, m₁)))).input,
          (beaverView1 (ρ 2) (beaverSend ((ρ 0, ρ 1), (xor b (rFlip ρ), m₀, m₁)))).coins),
          (beaverView1 (ρ 2)
            (beaverSend ((ρ 0, ρ 1), (xor b (rFlip ρ), m₀, m₁)))).received.1) =
        (fun _ => (b, otSelect (s₀, s₁) b)) := by
  have hw1 := w1_of_rFlip ρ b
  have hw2 := w2_of_rFlip ρ b
  have hne : ∀ i j : Fin 4, i ≠ j → ρ i ≠ ρ j := fun i j hij => ρ.injective.ne hij
  have hc_eval := beaver_mem_sortedPair_iff (ρ 0) (ρ 1) (ρ 2) (ρ 3) (hne 0 1 (by decide))
    (hne 2 0 (by decide)) (hne 2 1 (by decide)) (hne 3 0 (by decide)) (hne 3 1 (by decide))
    (hne 2 3 (by decide))
  refine ⟨funext fun _ => ?_, funext fun _ => ?_⟩
  · dsimp only [beaverOutputFn, beaverOut0, beaverView0]
    simp only [apply_ite Prod.fst, apply_ite Prod.snd, hw1, hw2]
  · dsimp only [beaverOutputFn, beaverOut1, beaverView1, beaverSend]
    simp only [apply_ite Prod.fst, apply_ite Prod.snd, hw1, hw2]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, hc_eval.1, otSelect_false]
      rw [sortedPair_fst_eq (hne 0 2 (by decide))]
    · simp only [↓reduceIte, hc_eval.2, otSelect_true]
      rw [sortedPair_fst_eq (hne 1 2 (by decide))]

private def beaverPhi0 : ((Equiv.Perm (Fin 4) × Bool) × (Bool × Bool × Bool)) ≃
    (((Fin 1 → Bool × Bool) × (Fin 1 → Bool)) × (Equiv.Perm (Fin 4) × Bool)) where
  toFun := fun ⟨⟨ρ, flip⟩, (r, m₀, m₁)⟩ =>
    let a := (ρ 0, ρ 1)
    let (u, v) := otherTwo a.1 a.2
    let w := if r then (v, u) else (u, v)
    let s₀ := xor m₀ (decide (w.1 < a.1))
    let s₁ := xor m₁ (decide (w.2 < a.2))
    let c := decide (ρ 2 = w.2)
    (((fun _ => (s₀, s₁)), fun _ => c), (swapPerm23 ρ flip, r))
  invFun := fun ⟨⟨s, c⟩, (ρ', r)⟩ =>
    let a := (ρ' 0, ρ' 1)
    let (u, v) := otherTwo a.1 a.2
    let w := if r then (v, u) else (u, v)
    let target2 := if c 0 then w.2 else w.1
    let flip := decide (ρ' 2 ≠ target2)
    let ρ := swapPerm23 ρ' flip
    let m₀ := xor (s 0).1 (decide (w.1 < a.1))
    let m₁ := xor (s 0).2 (decide (w.2 < a.2))
    ((ρ, flip), (r, m₀, m₁))
  left_inv := fun ⟨⟨ρ, flip⟩, (r, m₀, m₁)⟩ => by
    dsimp only
    simp only [swapPerm23_0, swapPerm23_1]
    have hne : ∀ i j : Fin 4, i ≠ j → ρ i ≠ ρ j := fun i j hij => ρ.injective.ne hij
    have h2 : ∀ (w : Fin 4 × Fin 4), (w = (ρ 2, ρ 3) ∨ w = (ρ 3, ρ 2)) →
        (decide (swapPerm23 ρ flip 2 ≠ if decide (ρ 2 = w.2) then w.2 else w.1) = flip) := by
      intro w hw
      rw [swapPerm23_2]
      rcases hw with rfl | rfl <;> cases flip <;>
        simp only [hne 2 3 (by decide), hne 3 2 (by decide), decide_eq_true_eq,
          decide_eq_false_iff_not, ne_eq, not_true_eq_false, not_false_eq_true,
          Bool.false_eq_true, ↓reduceIte]
    have hw_cases : (let (u, v) := otherTwo (ρ 0) (ρ 1);
        let w := if r then (v, u) else (u, v); w = (ρ 2, ρ 3) ∨ w = (ρ 3, ρ 2)) := by
      rcases otherTwo_spec (ρ 0) (ρ 1) (ρ 2) (ρ 3) (hne 0 1 (by decide))
        (hne 2 0 (by decide)) (hne 2 1 (by decide)) (hne 3 0 (by decide))
        (hne 3 1 (by decide)) (hne 2 3 (by decide)) with huv | huv <;>
        cases r <;> simp only [huv, Bool.false_eq_true, ↓reduceIte, or_true, true_or]
    dsimp only at hw_cases
    rw [h2 _ hw_cases, swapPerm23_invol]
    simp only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  right_inv := fun ⟨⟨s, c⟩, (ρ', r)⟩ => by
    dsimp only
    have hne' : ∀ i j : Fin 4, i ≠ j → ρ' i ≠ ρ' j := fun i j hij => ρ'.injective.ne hij
    set a := (ρ' 0, ρ' 1)
    set uv := otherTwo a.1 a.2
    set w := if r then (uv.2, uv.1) else (uv.1, uv.2)
    set target2 := if c 0 then w.2 else w.1
    set flip := decide (ρ' 2 ≠ target2)
    have hpair : w = (ρ' 2, ρ' 3) ∨ w = (ρ' 3, ρ' 2) := by
      rcases otherTwo_spec (ρ' 0) (ρ' 1) (ρ' 2) (ρ' 3) (hne' 0 1 (by decide))
        (hne' 2 0 (by decide)) (hne' 2 1 (by decide)) (hne' 3 0 (by decide))
        (hne' 3 1 (by decide)) (hne' 2 3 (by decide)) with huv | huv <;>
        cases hr : r <;> simp only [w, uv, a, huv, hr, Bool.false_eq_true, ↓reduceIte,
          true_or, or_true]
    have h2 : swapPerm23 ρ' flip 2 = target2 := by
      rw [swapPerm23_2]
      rcases hpair with hp | hp <;> cases hc : c 0 <;>
        simp only [flip, target2, hp, hc, Bool.false_eq_true, ↓reduceIte,
          decide_eq_true_eq, ne_eq, not_true_eq_false, hne' 2 3 (by decide), not_false_eq_true]
    have hc_eq : decide (swapPerm23 ρ' flip 2 = w.2) = c 0 := by
      rw [h2]
      rcases hpair with hp | hp <;> cases hc : c 0 <;>
        simp only [target2, hp, hc, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
          decide_eq_false_iff_not, hne' 2 3 (by decide), hne' 3 2 (by decide), not_false_eq_true]
    dsimp only [w, uv, a] at hc_eq
    simp only [swapPerm23_0, swapPerm23_1, hc_eq, swapPerm23_invol]
    dsimp only [w, uv, a]
    simp only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    refine Prod.ext (Prod.ext (funext fun j => ?_) (funext fun j => ?_)) (Prod.ext rfl rfl)
    · have hj : j = 0 := Fin.eq_zero j; subst hj; rfl
    · have hj : j = 0 := Fin.eq_zero j; subst hj; rfl

private theorem beaver_priv0 :
    ProbComp.eval (idealJoint (rotFunctionality 1) {0} (beaverSim {0}) fun _ => ()) =
      (realCorrelated beaverOTProtocol deal211).map
        (Prod.map ({0} : Finset (Fin 2)).restrict id) := by
  have hLHS :
      ProbComp.eval (idealJoint (rotFunctionality 1) {0} (beaverSim {0}) fun _ => ()) =
        (PMF.uniformOfFintype (((Fin 1 → Bool × Bool) × (Fin 1 → Bool)) ×
            (Equiv.Perm (Fin 4) × Bool))).map fun ⟨⟨s, c⟩, (ρ', r)⟩ =>
          let a := (ρ' 0, ρ' 1)
          let (u, v) := otherTwo a.1 a.2
          let w := if r then (v, u) else (u, v)
          let m₀ := xor (s 0).1 (decide (w.1 < a.1))
          let m₁ := xor (s 0).2 (decide (w.2 < a.2))
          let v0 : (i : ↑({0} : Finset (Fin 2))) →
              PartyView beaverIn beaverCoins beaverSchedule ↑i := fun ⟨i, hi⟩ =>
            if hi0 : i = 0 then hi0 ▸ beaverView0 a (r, m₀, m₁)
            else False.elim (hi0 (Finset.mem_singleton.mp hi))
          let out : (i : Fin 2) → beaverOut i :=
            Fin.cases s (fun _ j => (c j, otSelect (s j) (c j)))
          (v0, out) := by
    rw [eval_idealJoint, eval_rotFunctionality]
    dsimp only [idealROT, beaverSim]
    simp only [Finset.mem_singleton, one_ne_zero, ↓reduceDIte,
      ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_map,
      PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def, Finset.restrict, Fin.cases_zero]
    simp_rw [uniformOfFintype_bind_map]
    congr 1 with ⟨⟨s, c⟩, ρ', r⟩ : 1
    refine Prod.ext (funext fun ⟨i, hi⟩ => ?_) rfl
    have hi0 : i = 0 := Finset.mem_singleton.mp hi
    subst hi0
    rfl
  have hRHS :
      (realCorrelated beaverOTProtocol deal211).map
          (Prod.map ({0} : Finset (Fin 2)).restrict id) =
        (PMF.uniformOfFintype ((Equiv.Perm (Fin 4) × Bool) × (Bool × Bool × Bool))).map
          fun ⟨⟨ρ, _⟩, rmm⟩ =>
            let v0 : (i : ↑({0} : Finset (Fin 2))) →
                PartyView beaverIn beaverCoins beaverSchedule ↑i := fun ⟨i, hi⟩ =>
              if hi0 : i = 0 then hi0 ▸ beaverView0 (ρ 0, ρ 1) rmm
              else False.elim (hi0 (Finset.mem_singleton.mp hi))
            let v0' := beaverView0 (ρ 0, ρ 1) rmm
            let v1' := beaverView1 (ρ 2) (beaverSend ((ρ 0, ρ 1), rmm))
            let out : (i : Fin 2) → beaverOut i := fun i => match i with
              | ⟨0, _⟩ => beaverOutputFn 0 ((v0'.input, v0'.coins), v0'.received.1)
              | ⟨1, _⟩ => beaverOutputFn 1 ((v1'.input, v1'.coins), v1'.received.1)
            (v0, out) := by
    rw [realCorrelated_beaverOTProtocol]
    conv_lhs =>
      arg 2; arg 1
      rw [← uniformOfFintype_prod_map_fst (α := Equiv.Perm (Fin 4)) (β := Bool)]
    rw [PMF.bind_map, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
    rw [uniformOfFintype_bind_map]
    congr 1 with ⟨⟨ρ, _⟩, rmm⟩ : 1
    refine Prod.ext (funext fun ⟨i, hi⟩ => ?_) rfl
    have hi0 : i = 0 := Finset.mem_singleton.mp hi
    subst hi0
    rfl
  rw [hLHS, ← PMF.uniformOfFintype_map_equiv beaverPhi0, PMF.map_comp, hRHS]
  congr 1 with ⟨⟨ρ, flip⟩, r, m₀, m₁⟩ : 1
  simp only [Function.comp_def, beaverPhi0, Equiv.coe_fn_mk]
  simp only [swapPerm23_0, swapPerm23_1, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  refine Prod.ext (funext fun ⟨i, hi⟩ => ?_) (funext fun i => ?_)
  · have hi0 : i = 0 := Finset.mem_singleton.mp hi
    subst hi0
    rfl
  · fin_cases i
    · funext j
      fin_cases j
      rfl
    · funext j
      fin_cases j
      dsimp only [beaverOutputFn, beaverOut1, beaverView1, beaverSend]
      have hne : ∀ a b : Fin 4, a ≠ b → ρ a ≠ ρ b := fun a b hab => ρ.injective.ne hab
      rcases otherTwo_spec (ρ 0) (ρ 1) (ρ 2) (ρ 3) (hne 0 1 (by decide))
        (hne 2 0 (by decide)) (hne 2 1 (by decide)) (hne 3 0 (by decide))
        (hne 3 1 (by decide)) (hne 2 3 (by decide)) with huv | huv <;>
        cases r <;>
        simp only [huv, Bool.false_eq_true, ↓reduceIte,
          decide_eq_false (hne 2 3 (by decide)), decide_true,
          (beaver_mem_sortedPair_iff (ρ 0) (ρ 1) (ρ 2) (ρ 3) (hne 0 1 (by decide))
            (hne 2 0 (by decide)) (hne 2 1 (by decide)) (hne 3 0 (by decide))
            (hne 3 1 (by decide)) (hne 2 3 (by decide))).1,
          (beaver_mem_sortedPair_iff (ρ 0) (ρ 1) (ρ 2) (ρ 3) (hne 0 1 (by decide))
            (hne 2 0 (by decide)) (hne 2 1 (by decide)) (hne 3 0 (by decide))
            (hne 3 1 (by decide)) (hne 2 3 (by decide))).2,
          otSelect_false, otSelect_true] <;>
        first
        | (rw [sortedPair_fst_eq (hne 0 2 (by decide))]; rfl)
        | (rw [sortedPair_fst_eq (hne 1 2 (by decide))]; rfl)
private def beaverPhi1 : ((Equiv.Perm (Fin 4) × Bool) × (Bool × Bool × Bool)) ≃
    (((Fin 1 → Bool × Bool) × (Fin 1 → Bool)) × (Equiv.Perm (Fin 4) × Bool)) where
  toFun := fun ⟨⟨ρ, flip⟩, (r, m₀, m₁)⟩ =>
    let a := (ρ 0, ρ 1)
    let (u, v) := otherTwo a.1 a.2
    let w := if r then (v, u) else (u, v)
    let s₀ := xor m₀ (decide (w.1 < a.1))
    let s₁ := xor m₁ (decide (w.2 < a.2))
    let c := decide (ρ 2 = w.2)
    let mOther := if c then m₀ else m₁
    let ρ' := if c then swapPerm03 ρ flip else swapPerm13 ρ flip
    (((fun _ => (s₀, s₁)), fun _ => c), (ρ', mOther))
  invFun := fun ⟨⟨s, c⟩, (ρ', mOther)⟩ =>
    let flip := if c 0
      then decide (decide (ρ' 3 < ρ' 0) ≠ xor (s 0).1 mOther)
      else decide (decide (ρ' 3 < ρ' 1) ≠ xor (s 0).2 mOther)
    let ρ := if c 0 then swapPerm03 ρ' flip else swapPerm13 ρ' flip
    let r := xor (c 0) (rFlip ρ)
    let m₀ := if c 0 then mOther else xor (s 0).1 (decide (ρ 2 < ρ 0))
    let m₁ := if c 0 then xor (s 0).2 (decide (ρ 2 < ρ 1)) else mOther
    ((ρ, flip), (r, m₀, m₁))
  left_inv := fun ⟨⟨ρ, flip⟩, (r, m₀, m₁)⟩ => by
    dsimp only
    have hne : ∀ i j : Fin 4, i ≠ j → ρ i ≠ ρ j := fun i j hij => ρ.injective.ne hij
    have h03 : Equiv.swap (0 : Fin 4) 3 * Equiv.swap 0 3 = 1 := by decide
    have h13 : Equiv.swap (1 : Fin 4) 3 * Equiv.swap 1 3 = 1 := by decide
    have hxor : ∀ a b : Bool, xor a (xor b a) = b := fun a b => by
      cases a <;> cases b <;> rfl
    rcases otherTwo_spec (ρ 0) (ρ 1) (ρ 2) (ρ 3) (hne 0 1 (by decide))
      (hne 2 0 (by decide)) (hne 2 1 (by decide)) (hne 3 0 (by decide))
      (hne 3 1 (by decide)) (hne 2 3 (by decide)) with huv | huv
    · cases r <;> cases flip <;>
        simp only [huv, Bool.false_eq_true, ↓reduceIte,
          hne 2 3 (by decide), not_false_eq_true,
          swapPerm03, swapPerm13, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_right, decide_lt_swap (hne 0 3 (by decide)),
          decide_lt_swap (hne 1 3 (by decide)), Bool.xor_assoc, Bool.xor_self,
          Bool.xor_false, hxor, Bool.not_ne_self, ne_eq, not_true_eq_false, decide_true,
          decide_false, mul_assoc, h03, h13, mul_one] <;>
        simp only [rFlip_eq_false_of huv, Bool.xor_self, Bool.xor_false]
    · cases r <;> cases flip <;>
        simp only [huv, Bool.false_eq_true, ↓reduceIte,
          hne 2 3 (by decide), not_false_eq_true,
          swapPerm03, swapPerm13, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_right, decide_lt_swap (hne 0 3 (by decide)),
          decide_lt_swap (hne 1 3 (by decide)), Bool.xor_assoc, Bool.xor_self,
          Bool.xor_false, hxor, Bool.not_ne_self, ne_eq, not_true_eq_false, decide_true,
          decide_false, mul_assoc, h03, h13, mul_one] <;>
        simp only [rFlip_eq_true_of huv, Bool.false_xor, Bool.xor_self]
  right_inv := fun ⟨⟨s, c⟩, (ρ', mOther)⟩ => by
    have hne' : ∀ i j : Fin 4, i ≠ j → ρ' i ≠ ρ' j := fun i j hij => ρ'.injective.ne hij
    rcases Bool.eq_false_or_eq_true (c 0) with hc | hc
    · set flip := decide (decide (ρ' 3 < ρ' 0) ≠ xor (s 0).1 mOther)
      set ρ := swapPerm03 ρ' flip
      have hw1 : (if xor true (rFlip ρ) then (otherTwo (ρ 0) (ρ 1)).2
          else (otherTwo (ρ 0) (ρ 1)).1) = ρ 3 := by
        simpa only [↓reduceIte] using w1_of_rFlip ρ true
      have hw2 : (if xor true (rFlip ρ) then (otherTwo (ρ 0) (ρ 1)).1
          else (otherTwo (ρ 0) (ρ 1)).2) = ρ 2 := by
        simpa only [↓reduceIte] using w2_of_rFlip ρ true
      have h3lt0 : decide (ρ 3 < ρ 0) = xor (s 0).1 mOther := by
        by_cases hd : decide (ρ' 3 < ρ' 0) = xor (s 0).1 mOther
        · have hf : flip = false := decide_eq_false (not_not.mpr hd)
          simp only [ρ, hf, swapPerm03, Bool.false_eq_true, ↓reduceIte, hd]
        · have hf : flip = true := decide_eq_true hd
          have hl : decide ((ρ' * Equiv.swap (0 : Fin 4) 3) 3 <
              (ρ' * Equiv.swap (0 : Fin 4) 3) 0) = !decide (ρ' 3 < ρ' 0) := by
            simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
            exact decide_lt_swap (hne' 0 3 (by decide))
          simp only [ρ, hf, swapPerm03, ↓reduceIte, hl]
          cases hxor : xor (s 0).1 mOther <;> cases hd' : decide (ρ' 3 < ρ' 0) <;>
            simp_all only [Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true,
              not_true_eq_false, Bool.not_true, Bool.not_false]
      have hswap : swapPerm03 ρ flip = ρ' := swapPerm03_invol ρ' flip
      have hflip : decide (decide (ρ' 3 < ρ' 0) ≠ xor (s 0).1 mOther) = flip := rfl
      have hρ : swapPerm03 ρ' flip = ρ := rfl
      dsimp only
      simp only [hc, ↓reduceIte, hflip, hρ, apply_ite Prod.fst, apply_ite Prod.snd]
      simp only [hw1, hw2, h3lt0, Bool.xor_assoc, Bool.xor_self,
        Bool.xor_false, Bool.xor_comm mOther, hswap]
      refine Prod.ext (Prod.ext (funext fun j => ?_) (funext fun j => ?_)) (Prod.ext rfl rfl)
      · have hj : j = 0 := Fin.eq_zero j; subst hj; rfl
      · have hj : j = 0 := Fin.eq_zero j; subst hj; exact hc.symm
    · set flip := decide (decide (ρ' 3 < ρ' 1) ≠ xor (s 0).2 mOther)
      set ρ := swapPerm13 ρ' flip
      have hw1 : (if xor false (rFlip ρ) then (otherTwo (ρ 0) (ρ 1)).2
          else (otherTwo (ρ 0) (ρ 1)).1) = ρ 2 := by
        simpa only [Bool.false_eq_true, ↓reduceIte] using w1_of_rFlip ρ false
      have hw2 : (if xor false (rFlip ρ) then (otherTwo (ρ 0) (ρ 1)).1
          else (otherTwo (ρ 0) (ρ 1)).2) = ρ 3 := by
        simpa only [Bool.false_eq_true, ↓reduceIte] using w2_of_rFlip ρ false
      have hne : ∀ i j : Fin 4, i ≠ j → ρ i ≠ ρ j := fun i j hij => ρ.injective.ne hij
      have h3lt1 : decide (ρ 3 < ρ 1) = xor (s 0).2 mOther := by
        by_cases hd : decide (ρ' 3 < ρ' 1) = xor (s 0).2 mOther
        · have hf : flip = false := decide_eq_false (not_not.mpr hd)
          simp only [ρ, hf, swapPerm13, Bool.false_eq_true, ↓reduceIte, hd]
        · have hf : flip = true := decide_eq_true hd
          have hl : decide ((ρ' * Equiv.swap (1 : Fin 4) 3) 3 <
              (ρ' * Equiv.swap (1 : Fin 4) 3) 1) = !decide (ρ' 3 < ρ' 1) := by
            simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
            exact decide_lt_swap (hne' 1 3 (by decide))
          simp only [ρ, hf, swapPerm13, ↓reduceIte, hl]
          cases hxor : xor (s 0).2 mOther <;> cases hd' : decide (ρ' 3 < ρ' 1) <;>
            simp_all only [Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true,
              not_true_eq_false, Bool.not_true, Bool.not_false]
      have hswap : swapPerm13 ρ flip = ρ' := swapPerm13_invol ρ' flip
      have hflip : decide (decide (ρ' 3 < ρ' 1) ≠ xor (s 0).2 mOther) = flip := rfl
      have hρ : swapPerm13 ρ' flip = ρ := rfl
      dsimp only
      simp only [hc, Bool.false_eq_true, ↓reduceIte, hflip, hρ, apply_ite Prod.fst,
        apply_ite Prod.snd]
      simp only [hw1, hw2, decide_eq_false (hne 2 3 (by decide)), h3lt1, Bool.xor_assoc,
        Bool.xor_self, Bool.xor_false, Bool.xor_comm mOther, hswap]
      refine Prod.ext (Prod.ext (funext fun j => ?_) (funext fun j => ?_)) (Prod.ext rfl rfl)
      · have hj : j = 0 := Fin.eq_zero j; subst hj; rfl
      · have hj : j = 0 := Fin.eq_zero j; subst hj; exact hc.symm

private theorem beaver_priv1 :
    ProbComp.eval (idealJoint (rotFunctionality 1) {1} (beaverSim {1}) fun _ => ()) =
      (realCorrelated beaverOTProtocol deal211).map
        (Prod.map ({1} : Finset (Fin 2)).restrict id) := by
  have hLHS :
      ProbComp.eval (idealJoint (rotFunctionality 1) {1} (beaverSim {1}) fun _ => ()) =
        (PMF.uniformOfFintype (((Fin 1 → Bool × Bool) × (Fin 1 → Bool)) ×
            (Equiv.Perm (Fin 4) × Bool))).map fun ⟨⟨s, c⟩, (ρ', mOther)⟩ =>
          let b := ρ' 2
          let p₀ := if c 0 then sortedPair (ρ' 0) (ρ' 3) else sortedPair (ρ' 0) (ρ' 2)
          let p₁ := if c 0 then sortedPair (ρ' 1) (ρ' 2) else sortedPair (ρ' 1) (ρ' 3)
          let m₀ := if c 0 then mOther else xor (otSelect (s 0) (c 0)) (decide (ρ' 2 < ρ' 0))
          let m₁ := if c 0 then xor (otSelect (s 0) (c 0)) (decide (ρ' 2 < ρ' 1)) else mOther
          let v1 : (i : ↑({1} : Finset (Fin 2))) →
              PartyView beaverIn beaverCoins beaverSchedule ↑i := fun ⟨i, hi⟩ =>
            if hi1 : i = 1 then hi1 ▸ beaverView1 b (p₀, p₁, m₀, m₁)
            else False.elim (hi1 (Finset.mem_singleton.mp hi))
          let out : (i : Fin 2) → beaverOut i :=
            Fin.cases s (fun _ j => (c j, otSelect (s j) (c j)))
          (v1, out) := by
    rw [eval_idealJoint, eval_rotFunctionality]
    dsimp only [idealROT, beaverSim, Finset.restrict]
    simp only [Finset.mem_singleton, zero_ne_one, ↓reduceDIte,
      ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_map,
      PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
    simp_rw [uniformOfFintype_bind_map]
    congr 1 with ⟨⟨s, c⟩, ρ', mOther⟩ : 1
    refine Prod.ext (funext fun ⟨i, hi⟩ => ?_) rfl
    have hi1 : i = 1 := Finset.mem_singleton.mp hi
    subst hi1
    rfl
  have hRHS :
      (realCorrelated beaverOTProtocol deal211).map
          (Prod.map ({1} : Finset (Fin 2)).restrict id) =
        (PMF.uniformOfFintype ((Equiv.Perm (Fin 4) × Bool) × (Bool × Bool × Bool))).map
          fun ⟨⟨ρ, _⟩, rmm⟩ =>
            let v1 : (i : ↑({1} : Finset (Fin 2))) →
                PartyView beaverIn beaverCoins beaverSchedule ↑i := fun ⟨i, hi⟩ =>
              if hi1 : i = 1 then hi1 ▸ beaverView1 (ρ 2) (beaverSend ((ρ 0, ρ 1), rmm))
              else False.elim (hi1 (Finset.mem_singleton.mp hi))
            let v0' := beaverView0 (ρ 0, ρ 1) rmm
            let v1' := beaverView1 (ρ 2) (beaverSend ((ρ 0, ρ 1), rmm))
            let out : (i : Fin 2) → beaverOut i := fun i => match i with
              | ⟨0, _⟩ => beaverOutputFn 0 ((v0'.input, v0'.coins), v0'.received.1)
              | ⟨1, _⟩ => beaverOutputFn 1 ((v1'.input, v1'.coins), v1'.received.1)
            (v1, out) := by
    rw [realCorrelated_beaverOTProtocol]
    conv_lhs =>
      arg 2; arg 1
      rw [← uniformOfFintype_prod_map_fst (α := Equiv.Perm (Fin 4)) (β := Bool)]
    rw [PMF.bind_map, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
    rw [uniformOfFintype_bind_map]
    congr 1 with ⟨⟨ρ, _⟩, rmm⟩ : 1
    refine Prod.ext (funext fun ⟨i, hi⟩ => ?_) rfl
    have hi1 : i = 1 := Finset.mem_singleton.mp hi
    subst hi1
    rfl
  rw [hLHS, ← PMF.uniformOfFintype_map_equiv beaverPhi1, PMF.map_comp, hRHS]
  congr 1 with ⟨⟨ρ, flip⟩, r, m₀, m₁⟩ : 1
  simp only [Function.comp_def, beaverPhi1, Equiv.coe_fn_mk]
  have hne : ∀ i j : Fin 4, i ≠ j → ρ i ≠ ρ j := fun i j hij => ρ.injective.ne hij
  rcases otherTwo_spec (ρ 0) (ρ 1) (ρ 2) (ρ 3) (hne 0 1 (by decide))
    (hne 2 0 (by decide)) (hne 2 1 (by decide)) (hne 3 0 (by decide))
    (hne 3 1 (by decide)) (hne 2 3 (by decide)) with huv | huv <;>
    cases r <;> cases flip <;>
    simp only [huv, Bool.false_eq_true, ↓reduceIte, decide_true, decide_false,
      hne 2 3 (by decide), swapPerm03, swapPerm13, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 4) ≠ 1) (by decide : (0 : Fin 4) ≠ 3),
      Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 4) ≠ 0) (by decide : (1 : Fin 4) ≠ 3),
      Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 4) ≠ 0) (by decide : (2 : Fin 4) ≠ 3),
      Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 4) ≠ 1) (by decide : (2 : Fin 4) ≠ 3),
      Equiv.swap_apply_left, Equiv.swap_apply_right, otSelect_false, otSelect_true,
      Bool.xor_assoc, Bool.xor_self, Bool.xor_false] <;>
    (refine Prod.ext (funext fun ⟨i, hi⟩ => ?_) (funext fun i => ?_) <;>
      [ (have hi1 : i = 1 := Finset.mem_singleton.mp hi
         subst hi1
         dsimp only [beaverView1, beaverSend]
         simp only [huv, Bool.false_eq_true, ↓reduceIte]
         (try rw [sortedPair_comm (x := ρ 3) (y := ρ 1)])
         (try rw [sortedPair_comm (x := ρ 3) (y := ρ 0)])
         (try rfl));
        (fin_cases i <;>
         [ (funext j; fin_cases j
            dsimp only [beaverOutputFn, beaverOut0, beaverView0]
            simp only [huv, Bool.false_eq_true, ↓reduceIte]
            rfl);
           (funext j; fin_cases j
            dsimp only [beaverOutputFn, beaverOut1, beaverView1, beaverSend]
            simp only [huv, Bool.false_eq_true, ↓reduceIte]
            have hmem := beaver_mem_sortedPair_iff (ρ 0) (ρ 1) (ρ 2) (ρ 3) (hne 0 1 (by decide))
              (hne 2 0 (by decide)) (hne 2 1 (by decide)) (hne 3 0 (by decide))
              (hne 3 1 (by decide)) (hne 2 3 (by decide))
            (try rw [hmem.1])
            (try rw [hmem.2])
            (try simp only [Bool.false_eq_true, ↓reduceIte])
            first
            | (rw [sortedPair_fst_eq (hne 0 2 (by decide))]; rfl)
            | (rw [sortedPair_fst_eq (hne 1 2 (by decide))]; rfl)) ]) ])

/-- `beaverOTProtocol` realizes `rotFunctionality 1` with perfect semi-honest privacy over
`deal211`. -/
theorem beaverOTProtocol_private :
    PerfectSemiHonestPrivateProperWithSetup beaverOTProtocol noOracleWorld
      (fun _ => dealSource deal211) (rotFunctionality 1) beaverSim := by
  have hOutEq : (realCorrelated beaverOTProtocol deal211).map Prod.snd = idealROT 1 := by
    have h := congrArg (PMF.map Prod.snd) beaver_priv0
    rw [eval_idealJoint, eval_rotFunctionality] at h
    rw [PMF.map_bind, PMF.map_comp] at h
    have hconst : ∀ {α β : Type} (p : PMF α) (b : β),
        PMF.map (fun _ => b) p = PMF.pure b := fun p b => PMF.map_const p b
    simp only [PMF.map_comp, Function.comp_def, hconst, PMF.bind_pure] at h
    exact h.symm
  intro I hI x
  obtain rfl : x = fun _ => () := Subsingleton.elim _ _
  have hI_cases : I = ∅ ∨ I = {0} ∨ I = {1} := by
    revert I hI
    decide
  rcases hI_cases with rfl | rfl | rfl
  · refine Eq.trans ?_ (dealSource_bind_realJoint beaverOTProtocol deal211 ∅).symm
    rw [eval_idealJoint, eval_rotFunctionality]
    dsimp only [beaverSim]
    rw [← hOutEq, PMF.bind_map]
    simp only [Finset.notMem_empty, ↓reduceDIte, ProbComp.eval_pure,
      PMF.pure_map, Function.comp_def]
    change (realCorrelated beaverOTProtocol deal211).map _ =
      (realCorrelated beaverOTProtocol deal211).map _
    congr 1 with x : 1
    refine Prod.ext (funext fun ⟨i, hi⟩ => False.elim (Finset.notMem_empty i hi)) rfl
  · exact beaver_priv0.trans (dealSource_bind_realJoint beaverOTProtocol deal211 {0}).symm
  · exact beaver_priv1.trans (dealSource_bind_realJoint beaverOTProtocol deal211 {1}).symm

/-- Confirming our `k ≤ 1` bound is consistent with `beaverOTProtocol`: applying
`rot_le_one_of_deal211` yields `1 ≤ 1`. -/
example : 1 ≤ 1 :=
  rot_le_one_of_deal211 beaverOTProtocol beaverSim beaverOTProtocol_private

/-! ### Non-private counterexample over `PMF.pure ((), ())` -/

/-- Without privacy, a deterministic 1-round protocol over the trivial source `PMF.pure ((), ())`
(mutual information `0`) can sample two random `(s₀, s₁, c)` triples and send them in clear,
matching `idealROT 2`'s output distribution while leaking everything to the transcript. -/
example :
    ∃ (sc : Schedule 2 noOracleSpec) (Coins : Fin 2 → Type)
      (_ : Finite (Coins 0)) (_ : Finite (Coins 1)) (_ : Finite (PublicTranscript sc))
      (proto : MPC.Protocol 2 noOracleSpec sc (Fin.cases Unit (fun _ => Unit)) Coins
        (fun _ => Fin 2 → Bool × Bool)),
      (realCorrelated proto (PMF.pure ((), ()))).map Prod.snd = idealROT 2 := by
  let Msg : Type := (Fin 2 → Bool × Bool) × (Fin 2 → Bool)
  let Coins : Fin 2 → Type := fun _ => Msg
  let defaultMsg : Msg := (fun _ => (false, false), fun _ => false)
  let sc : Schedule 2 noOracleSpec := [Round.message 0 1 Msg]
  let proto : MPC.Protocol 2 noOracleSpec sc (Fin.cases Unit (fun _ => Unit)) Coins
      (fun _ => Fin 2 → Bool × Bool) :=
    { sampleCoins := fun i => match i with
        | ⟨0, _⟩ => ProbComp.uniform Msg
        | ⟨1, _⟩ => pure defaultMsg
      steps := Steps.message (sender := 0) (receiver := 1) (Msg := Msg)
        (fun (_, coins) => coins)
        (Steps.done (Fin.cases
          (fun ((_, coins), _) => coins.1)
          (fun x ((_, _), recv) j =>
            let msg := recv (congrArg Fin.succ (Fin.eq_zero x))
            (msg.2 j, otSelect (msg.1 j) (msg.2 j))))) }
  refine ⟨sc, Coins, inferInstance, inferInstance, inferInstance, proto, ?_⟩
  rw [realCorrelated, PMF.pure_bind, Protocol.evalWith_eq, ProbComp.eval_pi]
  have hpi : (PMF.pi fun i : Fin 2 => (proto.sampleCoins i).eval) =
      (PMF.uniformOfFintype Msg).map (fun m i => if i = 0 then m else defaultMsg) := by
    ext coins
    rw [PMF.pi_apply, Fin.prod_univ_two]
    have ha : (proto.sampleCoins 0).eval = PMF.uniformOfFintype Msg := ProbComp.eval_uniform _
    have hc : (proto.sampleCoins 1).eval = PMF.pure defaultMsg := ProbComp.eval_pure _
    rw [ha, hc, PMF.pure_apply]
    classical
    by_cases hc1 : coins 1 = defaultMsg
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc1), mul_one, PMF.map_apply,
        tsum_eq_single (coins 0)]
      · have hfun : coins = fun i : Fin 2 => if i = 0 then coins 0 else defaultMsg := by
          funext i
          fin_cases i
          · rfl
          · exact hc1
        rw [ite_eq_left_of_eq_true _ _ (eq_true hfun)]
      · intro x hx
        rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hx (congrFun h 0).symm)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc1), mul_zero, PMF.map_apply]
      rw [tsum_eq_sum (s := (∅ : Finset Msg))]
      · exact Finset.sum_empty.symm
      · intro x _
        rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hc1 (congrFun h 1))]
  rw [hpi, PMF.map_bind, PMF.bind_map]
  simp only [proto, Steps.evalWith_message, Steps.evalWith_done, PMF.pure_map, Function.comp_def]
  change (PMF.uniformOfFintype Msg).map _ = _
  dsimp only [idealROT]
  congr 1 with x : 1
  funext i
  fin_cases i <;> rfl

/-! ### Chosen-input unordered/batch, entropy/cardinality, and communication-tree bounds -/

/-- No perfectly semi-honest private protocol over `deal211Unordered` realizes `2` chosen OTs. -/
example {sc : Schedule 2 noOracleSpec} {Coins : Fin 2 → Type}
    [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    (proto : MPC.Protocol 2 noOracleSpec sc
      (fun i => (batchOTSpec 2 Bool).Query () i ×
        Fin.cases {s : Finset (Fin 4) // s.card = 2} (fun _ => Fin 4) i)
      Coins ((batchOTSpec 2 Bool).Answer ()))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc ((batchOTSpec 2 Bool).Query ())
        (fun i => (batchOTSpec 2 Bool).Query () i ×
          Fin.cases {s : Finset (Fin 4) // s.card = 2} (fun _ => Fin 4) i)
        Coins ((batchOTSpec 2 Bool).Answer ()) I) :
    ¬ PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (dealSourceWithInput deal211Unordered) (batchOTFunctionality 2 Bool) S := by
  intro hPriv
  have hle := chosenOT_le_one_of_deal211Unordered proto S hPriv
  omega

/-- No perfectly semi-honest private protocol over `deal211Batch m` realizes `m + 1` chosen OTs. -/
example {m : ℕ} {sc : Schedule 2 noOracleSpec} {Coins : Fin 2 → Type}
    [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    (proto : MPC.Protocol 2 noOracleSpec sc
      (fun i => (batchOTSpec (m + 1) Bool).Query () i ×
        Fin.cases (Fin m → Fin 4 × Fin 4) (fun _ => Fin m → Fin 4) i)
      Coins ((batchOTSpec (m + 1) Bool).Answer ()))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc ((batchOTSpec (m + 1) Bool).Query ())
        (fun i => (batchOTSpec (m + 1) Bool).Query () i ×
          Fin.cases (Fin m → Fin 4 × Fin 4) (fun _ => Fin m → Fin 4) i)
        Coins ((batchOTSpec (m + 1) Bool).Answer ()) I) :
    ¬ PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (dealSourceWithInput (deal211Batch m)) (batchOTFunctionality (m + 1) Bool) S := by
  intro hPriv
  have hle := chosenOT_le_of_deal211Batch proto S hPriv
  omega

/-- Single-party marginal entropy and cardinality upper bounds on `deal211`. -/
example {sc : Schedule 2 noOracleSpec} {Coins : Fin 2 → Type}
    [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)] {k : ℕ}
    (proto : MPC.Protocol 2 noOracleSpec sc (Fin.cases (Fin 4 × Fin 4) (fun _ => Fin 4)) Coins
      (fun _ => Fin k → Bool × Bool))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc (fun _ => Unit) (Fin.cases (Fin 4 × Fin 4) (fun _ => Fin 4)) Coins
        (fun _ => Fin k → Bool × Bool) I)
    (hPriv : PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (fun _ => dealSource deal211) (rotFunctionality k) S) :
    (k : ℝ) ≤ PMF.entropy (PMF.map Prod.fst deal211) ∧
      (k : ℝ) ≤ PMF.entropy (PMF.map Prod.snd deal211) ∧
      (k : ℝ) ≤ Real.logb 2 (Fintype.card (Fin 4 × Fin 4)) ∧
      (k : ℝ) ≤ Real.logb 2 (Fintype.card (Fin 4)) :=
  ⟨rot_le_entropy_fst proto deal211 S hPriv,
    rot_le_entropy_snd proto deal211 S hPriv,
    rot_le_logb_card_fst proto deal211 S hPriv,
    rot_le_logb_card_snd proto deal211 S hPriv⟩

/-- No deterministic `Communication.Protocol` over `deal211` realizes `2` perfectly private ROTs. -/
example {τ : Type} (p : Communication.Protocol (Fin 4 × Fin 4) (Fin 4) τ)
    (outA : (Fin 4 × Fin 4) × Fin p.leafCount → Fin 2 → Bool × Bool)
    (outB : Fin 4 × Fin p.leafCount → Fin 2 → Bool × Bool)
    (hCorr : ∀ a b j, (a, b) ∈ deal211.support →
      (outB (b, p.leaf a b) j).2 = otSelect (outA (a, p.leaf a b) j) (outB (b, p.leaf a b) j).1)
    (hPrivA : IndepUniform (p.transcriptLaw deal211) (fun (x, _, t) => (outA (x, t), t))
      (fun (_, y, t) => rotChoices (outB (y, t))))
    (hPrivB : IndepUniform (p.transcriptLaw deal211) (fun (_, y, t) => (t, outB (y, t)))
      (fun (x, y, t) => rotUnselected (outA (x, t)) (outB (y, t)))) :
    False := by
  have hle := commProtocol_rot_le_one_of_deal211 p outA outB hCorr hPrivA hPrivB
  omega

/-- No `Communication.PrivateCoin a b` protocol over `deal211` realizes `2` private ROTs. -/
example {a b : ℕ} {τ : Type}
    (p : Communication.PrivateCoin a b (Fin 4 × Fin 4) (Fin 4) τ)
    (outA : ((Fin 4 × Fin 4) × Cslib.BitString a) × Fin (Communication.Protocol.leafCount p) →
      Fin 2 → Bool × Bool)
    (outB : (Fin 4 × Cslib.BitString b) × Fin (Communication.Protocol.leafCount p) →
      Fin 2 → Bool × Bool)
    (hCorr : ∀ u v j, (u.1, v.1) ∈ deal211.support →
      (outB (v, Communication.Protocol.leaf p u v) j).2 =
        otSelect (outA (u, Communication.Protocol.leaf p u v) j)
          (outB (v, Communication.Protocol.leaf p u v) j).1)
    (hPrivA : IndepUniform
      (Communication.Protocol.transcriptLaw p (Communication.PrivateCoin.inputLaw a b deal211))
      (fun (x, _, t) => (outA (x, t), t)) (fun (_, y, t) => rotChoices (outB (y, t))))
    (hPrivB : IndepUniform
      (Communication.Protocol.transcriptLaw p (Communication.PrivateCoin.inputLaw a b deal211))
      (fun (_, y, t) => (t, outB (y, t)))
      (fun (x, y, t) => rotUnselected (outA (x, t)) (outB (y, t)))) :
    False := by
  have hle := privateCoin_rot_le_one_of_deal211 p outA outB hCorr hPrivA hPrivB
  omega

/-! ### Nonvacuous `1`-ROT witness for `PrivateCoin` and `Communication.Protocol` -/

private theorem uniform_map_pair_eq_bind_fin1
    {Ω Γ : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → Γ) (g : Ω → Bool)
    (σ : Ω → Ω) (hσ_invol : ∀ ω, σ (σ ω) = ω)
    (hσ_f : ∀ ω, f (σ ω) = f ω)
    (hσ_g : ∀ ω, g (σ ω) = !(g ω)) :
    PMF.map (fun ω => (f ω, fun _ : Fin 1 => g ω)) (PMF.uniformOfFintype Ω) =
      (PMF.map f (PMF.uniformOfFintype Ω)).bind fun y =>
        PMF.map (fun b => (y, b)) (PMF.uniformOfFintype (Fin 1 → Bool)) := by
  let e : Ω × Bool ≃ Ω × (Fin 1 → Bool) :=
    { toFun := fun (ω, d) => (if d then ω else σ ω, fun _ => g ω)
      invFun := fun (ω', b') => (if g ω' = b' 0 then ω' else σ ω', decide (g ω' = b' 0))
      left_inv := fun ⟨ω, d⟩ => by
        cases d
        · have hne : (!g ω) ≠ g ω := by cases g ω <;> decide
          simp only [Bool.false_eq_true, ↓reduceIte, hσ_g, hσ_invol, hne, decide_false]
        · simp only [↓reduceIte, decide_true]
      right_inv := fun ⟨ω', b'⟩ => by
        by_cases h : g ω' = b' 0
        · simp only [h, decide_true, ↓reduceIte]
          exact Prod.ext rfl (funext fun i => by rw [Fin.eq_zero i])
        · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, hσ_invol, hσ_g]
          refine Prod.ext rfl (funext fun i => by
            rw [Fin.eq_zero i]
            cases hg : g ω' <;> cases hb : b' 0 <;> simp_all) }
  have hLHS :
      PMF.map (fun ω => (f ω, fun _ : Fin 1 => g ω)) (PMF.uniformOfFintype Ω) =
        PMF.map (fun q : Ω × Bool => (f q.1, fun _ : Fin 1 => g q.1))
          (PMF.uniformOfFintype (Ω × Bool)) := by
    have hconst :
        (fun a : Ω => PMF.map (fun _ : Bool => (f a, fun _ : Fin 1 => g a))
            (PMF.uniformOfFintype Bool)) =
          fun a : Ω => PMF.pure (f a, fun _ : Fin 1 => g a) :=
      funext fun a => PMF.map_const _ _
    rw [← PMF.uniformOfFintype_prod, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
    rw [hconst]
    exact (PMF.bind_pure_comp _ _).symm
  have hRHS :
      (PMF.map f (PMF.uniformOfFintype Ω)).bind (fun y =>
          PMF.map (fun b => (y, b)) (PMF.uniformOfFintype (Fin 1 → Bool))) =
        PMF.map (fun q : Ω × (Fin 1 → Bool) => (f q.1, q.2))
          (PMF.uniformOfFintype (Ω × (Fin 1 → Bool))) := by
    rw [← PMF.uniformOfFintype_prod, PMF.map_bind, PMF.bind_map]
    simp only [PMF.map_comp, Function.comp_def]
  rw [hLHS, hRHS, ← PMF.uniformOfFintype_map_equiv e, PMF.map_comp]
  congr 1 with ⟨ω, d⟩ : 1
  cases d <;> simp only [e, Equiv.coe_fn_mk, Function.comp_def, ↓reduceIte, Bool.false_eq_true,
    hσ_f]

private def w1Of (a : Fin 4 × Fin 4) (r : Bool) : Fin 4 :=
  let (u, v) := otherTwo a.1 a.2
  if r then v else u

private def w2Of (a : Fin 4 × Fin 4) (r : Bool) : Fin 4 :=
  let (u, v) := otherTwo a.1 a.2
  if r then u else v

private theorem w1Of_rFlip (ρ : Equiv.Perm (Fin 4)) (b : Bool) :
    w1Of (ρ 0, ρ 1) (xor b (rFlip ρ)) = if b then ρ 3 else ρ 2 := by
  have hne : ∀ i j : Fin 4, i ≠ j → ρ i ≠ ρ j := fun i j hij => ρ.injective.ne hij
  rcases otherTwo_spec (ρ 0) (ρ 1) (ρ 2) (ρ 3) (hne 0 1 (by decide)) (hne 2 0 (by decide))
    (hne 2 1 (by decide)) (hne 3 0 (by decide)) (hne 3 1 (by decide)) (hne 2 3 (by decide)) with
    huv | huv <;> simp only [w1Of]
  · rw [rFlip_eq_false_of huv, huv]; cases b <;> rfl
  · rw [rFlip_eq_true_of huv, huv]; cases b <;> rfl

private theorem w2Of_rFlip (ρ : Equiv.Perm (Fin 4)) (b : Bool) :
    w2Of (ρ 0, ρ 1) (xor b (rFlip ρ)) = if b then ρ 2 else ρ 3 := by
  have hne : ∀ i j : Fin 4, i ≠ j → ρ i ≠ ρ j := fun i j hij => ρ.injective.ne hij
  rcases otherTwo_spec (ρ 0) (ρ 1) (ρ 2) (ρ 3) (hne 0 1 (by decide)) (hne 2 0 (by decide))
    (hne 2 1 (by decide)) (hne 3 0 (by decide)) (hne 3 1 (by decide)) (hne 2 3 (by decide)) with
    huv | huv <;> simp only [w2Of]
  · rw [rFlip_eq_false_of huv, huv]; cases b <;> rfl
  · rw [rFlip_eq_true_of huv, huv]; cases b <;> rfl

private def pairTreeBit (k : Fin 4) : (Fin 4 × Fin 4) × BitString 1 → Bool :=
  fun u =>
    let p := sortedPair u.1.1 (w1Of u.1 (u.2 0))
    decide (k = p.1 ∨ k = p.2)

private def pairTree : Communication.PrivateCoin 1 0 (Fin 4 × Fin 4) (Fin 4) Unit :=
  Communication.Protocol.alice (pairTreeBit 0)
    (Communication.Protocol.alice (pairTreeBit 1)
      (Communication.Protocol.alice (pairTreeBit 2)
        (Communication.Protocol.output ()) (Communication.Protocol.output ()))
      (Communication.Protocol.alice (pairTreeBit 2)
        (Communication.Protocol.output ()) (Communication.Protocol.output ())))
    (Communication.Protocol.alice (pairTreeBit 1)
      (Communication.Protocol.alice (pairTreeBit 2)
        (Communication.Protocol.output ()) (Communication.Protocol.output ()))
      (Communication.Protocol.alice (pairTreeBit 2)
        (Communication.Protocol.output ()) (Communication.Protocol.output ())))

private def leafToPair (l : Fin pairTree.leafCount) : Fin 4 × Fin 4 :=
  match l.val with
  | 1 => (2, 3)
  | 2 => (1, 3)
  | 3 => (1, 2)
  | 4 => (0, 3)
  | 5 => (0, 2)
  | 6 => (0, 1)
  | _ => (0, 0)

private def pairOutA :
    ((Fin 4 × Fin 4) × BitString 1) × Fin pairTree.leafCount → Fin 1 → Bool × Bool
  | ((a, rA), _), _ =>
    (decide (w1Of a (rA 0) < a.1), decide (w2Of a (rA 0) < a.2))

private def pairOutB : (Fin 4 × BitString 0) × Fin pairTree.leafCount → Fin 1 → Bool × Bool
  | ((b, _), l), _ =>
    let p₀ := leafToPair l
    let c := decide (b ≠ p₀.1 ∧ b ≠ p₀.2)
    let p := if c then otherTwo p₀.1 p₀.2 else p₀
    let other := if b = p.1 then p.2 else p.1
    (c, decide (b < other))

private def leafOfPair (p : Fin 4 × Fin 4) : Fin pairTree.leafCount :=
  ⟨4 * Bool.toNat (decide (0 = p.1 ∨ 0 = p.2)) +
    2 * Bool.toNat (decide (1 = p.1 ∨ 1 = p.2)) +
    Bool.toNat (decide (2 = p.1 ∨ 2 = p.2)), by
    cases h0 : decide (0 = p.1 ∨ 0 = p.2) <;>
    cases h1 : decide (1 = p.1 ∨ 1 = p.2) <;>
    cases h2 : decide (2 = p.1 ∨ 2 = p.2) <;> decide⟩

private theorem pairTree_leaf_eq (u : (Fin 4 × Fin 4) × BitString 1)
    (v : Fin 4 × BitString 0) :
    Communication.Protocol.leaf pairTree u v =
      leafOfPair (sortedPair u.1.1 (w1Of u.1 (u.2 0))) := by
  rcases u with ⟨⟨a₀, a₁⟩, rA⟩
  rcases v with ⟨b, rB⟩
  have hrA : rA = fun _ => rA 0 := funext fun i => by rw [Fin.eq_zero i]
  have hrB : rB = Fin.elim0 := funext fun i => Fin.elim0 i
  rw [hrA, hrB]
  generalize rA 0 = r
  revert a₀ a₁ b r
  decide

private theorem leafToPair_leafOfPair :
    ∀ x y : Fin 4, x ≠ y → leafToPair (leafOfPair (sortedPair x y)) = sortedPair x y := by
  decide

private theorem w1Of_ne_fst :
    ∀ a₀ a₁ : Fin 4, ∀ r : Bool, a₀ ≠ a₁ → a₀ ≠ w1Of (a₀, a₁) r := by
  decide

private theorem pairTree_correct_pointwise :
    ∀ a₀ a₁ b : Fin 4, a₀ ≠ a₁ → b ≠ a₀ → b ≠ a₁ → ∀ r : Bool,
      let p₀ := sortedPair a₀ (w1Of (a₀, a₁) r)
      let c := decide (b ≠ p₀.1 ∧ b ≠ p₀.2)
      let p := if c then otherTwo p₀.1 p₀.2 else p₀
      let other := if b = p.1 then p.2 else p.1
      decide (b < other) =
        otSelect (decide (w1Of (a₀, a₁) r < a₀), decide (w2Of (a₀, a₁) r < a₁)) c := by
  decide

private theorem pairTree_correct (u : (Fin 4 × Fin 4) × BitString 1) (v : Fin 4 × BitString 0)
    (j : Fin 1) (hsup : (u.1, v.1) ∈ deal211.support) :
    (pairOutB (v, Communication.Protocol.leaf pairTree u v) j).2 =
      otSelect (pairOutA (u, Communication.Protocol.leaf pairTree u v) j)
        (pairOutB (v, Communication.Protocol.leaf pairTree u v) j).1 := by
  have hj : j = 0 := Fin.eq_zero j
  subst hj
  rcases u with ⟨⟨a₀, a₁⟩, rA⟩
  rcases v with ⟨b, rB⟩
  rw [PMF.mem_support_iff] at hsup
  simp only [deal211, PMF.map_apply] at hsup
  have hex : ∃ ρ : Equiv.Perm (Fin 4), ((ρ 0, ρ 1), ρ 2) = ((a₀, a₁), b) := by
    by_contra hno
    apply hsup
    refine tsum_eq_zero_iff.mpr fun ρ => ?_
    classical
    split_ifs with h
    · exact absurd ⟨ρ, h.symm⟩ hno
    · rfl
  rcases hex with ⟨ρ, hρ⟩
  have ha0 : ρ 0 = a₀ := (Prod.ext_iff.mp (Prod.ext_iff.mp hρ).1).1
  have ha1 : ρ 1 = a₁ := (Prod.ext_iff.mp (Prod.ext_iff.mp hρ).1).2
  have hb : ρ 2 = b := (Prod.ext_iff.mp hρ).2
  subst ha0 ha1 hb
  have hne01 : ρ 0 ≠ ρ 1 := ρ.injective.ne (by decide)
  have hb0 : ρ 2 ≠ ρ 0 := ρ.injective.ne (by decide)
  have hb1 : ρ 2 ≠ ρ 1 := ρ.injective.ne (by decide)
  rw [pairTree_leaf_eq]
  dsimp only [pairOutB, pairOutA]
  rw [leafToPair_leafOfPair (ρ 0) (w1Of (ρ 0, ρ 1) (rA 0)) (w1Of_ne_fst _ _ _ hne01)]
  exact pairTree_correct_pointwise (ρ 0) (ρ 1) (ρ 2) hne01 hb0 hb1 (rA 0)

private theorem privateCoin_inputLaw_deal211 :
    Communication.PrivateCoin.inputLaw 1 0 deal211 =
      (PMF.uniformOfFintype (Equiv.Perm (Fin 4) × Bool)).map fun (ρ, r) =>
        (((ρ 0, ρ 1), fun _ : Fin 1 => r), (ρ 2, (Fin.elim0 : BitString 0))) := by
  let e : BitString 1 × BitString 0 ≃ Bool :=
    { toFun := fun p => p.1 0
      invFun := fun b => (fun _ => b, Fin.elim0)
      left_inv := fun ⟨rA, rB⟩ =>
        Prod.ext (funext fun i => by rw [Fin.eq_zero i]) (funext fun i => Fin.elim0 i)
      right_inv := fun _ => rfl }
  have hu :
      PMF.uniformOfFintype (BitString 1 × BitString 0) =
        (PMF.uniformOfFintype Bool).map e.symm :=
    (PMF.uniformOfFintype_map_equiv e.symm).symm
  rw [Communication.PrivateCoin.inputLaw, deal211, hu, PMF.map_bind, PMF.bind_map,
    ← PMF.uniformOfFintype_prod]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Equiv.prodProdProdComm_apply]
  congr 1 with ⟨ρ, r⟩ : 1

private theorem pairTree_correct_inputLaw (u : (Fin 4 × Fin 4) × BitString 1)
    (v : Fin 4 × BitString 0) (j : Fin 1)
    (hsup : (u, v) ∈ (Communication.PrivateCoin.inputLaw 1 0 deal211).support) :
    (pairOutB (v, Communication.Protocol.leaf pairTree u v) j).2 =
      otSelect (pairOutA (u, Communication.Protocol.leaf pairTree u v) j)
        (pairOutB (v, Communication.Protocol.leaf pairTree u v) j).1 := by
  refine pairTree_correct u v j ?_
  rw [privateCoin_inputLaw_deal211, PMF.mem_support_iff, PMF.map_apply] at hsup
  rw [PMF.mem_support_iff, deal211, PMF.map_apply]
  intro hzero
  apply hsup
  refine tsum_eq_zero_iff.mpr fun ⟨ρ, r⟩ => ?_
  have hrho : ((ρ 0, ρ 1), ρ 2) ≠ (u.1, v.1) := by
    intro heq
    have hz := tsum_eq_zero_iff.mp hzero ρ
    simp only [heq, ↓reduceIte] at hz
    have hcard : (PMF.uniformOfFintype (Equiv.Perm (Fin 4))) ρ ≠ 0 := by
      simp only [PMF.uniformOfFintype_apply, ne_eq, ENNReal.inv_eq_zero,
        ENNReal.natCast_ne_top, not_false_eq_true]
    exact hcard hz
  have hne : (u, v) ≠ (((ρ 0, ρ 1), fun _ : Fin 1 => r), (ρ 2, Fin.elim0)) := fun h =>
    hrho (Prod.ext (congrArg (Prod.fst ∘ Prod.fst) h.symm)
      (congrArg (Prod.fst ∘ Prod.snd) h.symm))
  simp only [hne, ↓reduceIte]

private theorem pairTree_transcriptLaw :
    Communication.Protocol.transcriptLaw pairTree
        (Communication.PrivateCoin.inputLaw 1 0 deal211) =
      (PMF.uniformOfFintype (Equiv.Perm (Fin 4) × Bool)).map fun (ρ, r) =>
        (((ρ 0, ρ 1), fun _ : Fin 1 => r),
          (ρ 2, (Fin.elim0 : BitString 0)),
          leafOfPair (sortedPair (ρ 0) (w1Of (ρ 0, ρ 1) r))) := by
  rw [Communication.Protocol.transcriptLaw, privateCoin_inputLaw_deal211, PMF.map_comp]
  congr 1 with ⟨ρ, r⟩ : 1
  dsimp only [Function.comp_def]
  rw [pairTree_leaf_eq]

private theorem mem_pair_flip (b x y : Fin 4) :
    decide (b ≠ (sortedPair x y).1 ∧ b ≠ (sortedPair x y).2) =
      !decide (b = (sortedPair x y).1 ∨ b = (sortedPair x y).2) := by
  cases h1 : decide (b = (sortedPair x y).1) <;>
  cases h2 : decide (b = (sortedPair x y).2) <;>
  simp_all

private theorem pairTree_alice_private :
    IndepUniform (Communication.Protocol.transcriptLaw pairTree
        (Communication.PrivateCoin.inputLaw 1 0 deal211))
      (fun (x, _, t) => (pairOutA (x, t), t))
      (fun (_, y, t) => rotChoices (pairOutB (y, t))) := by
  refine ⟨?_⟩
  let f : Equiv.Perm (Fin 4) × Bool → (Fin 1 → Bool × Bool) × Fin pairTree.leafCount :=
    fun (ρ, r) =>
      let l := leafOfPair (sortedPair (ρ 0) (w1Of (ρ 0, ρ 1) r))
      (pairOutA (((ρ 0, ρ 1), fun _ => r), l), l)
  let g : Equiv.Perm (Fin 4) × Bool → Bool := fun (ρ, r) =>
    let l := leafOfPair (sortedPair (ρ 0) (w1Of (ρ 0, ρ 1) r))
    (pairOutB ((ρ 2, Fin.elim0), l) 0).1
  let σ : Equiv.Perm (Fin 4) × Bool → Equiv.Perm (Fin 4) × Bool :=
    fun (ρ, r) => (ρ * Equiv.swap (2 : Fin 4) 3, r)
  have hσ_invol : ∀ ω, σ (σ ω) = ω := fun ⟨ρ, r⟩ => by
    have hsq : Equiv.swap (2 : Fin 4) 3 * Equiv.swap (2 : Fin 4) 3 = 1 := by decide
    simp only [σ, mul_assoc, hsq, mul_one]
  have h0 : ∀ ρ : Equiv.Perm (Fin 4), (ρ * Equiv.swap (2 : Fin 4) 3) 0 = ρ 0 := fun ρ => by
    simp only [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 3)]
  have h1 : ∀ ρ : Equiv.Perm (Fin 4), (ρ * Equiv.swap (2 : Fin 4) 3) 1 = ρ 1 := fun ρ => by
    simp only [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 3)]
  have hσ_f : ∀ ω, f (σ ω) = f ω := fun ⟨ρ, r⟩ => by
    simp only [f, σ, h0, h1]
  have hσ_g : ∀ ω, g (σ ω) = !(g ω) := fun ⟨ρ, r⟩ => by
    have hne : ∀ i j : Fin 4, i ≠ j → ρ i ≠ ρ j := fun i j hij => ρ.injective.ne hij
    have hne01 : ρ 0 ≠ ρ 1 := hne 0 1 (by decide)
    have h2' : (ρ * Equiv.swap (2 : Fin 4) 3) 2 = ρ 3 := by
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    dsimp only [g, σ]
    rw [h0, h1, h2']
    have hl : leafToPair (leafOfPair (sortedPair (ρ 0) (w1Of (ρ 0, ρ 1) r))) =
        sortedPair (ρ 0) (w1Of (ρ 0, ρ 1) r) :=
      leafToPair_leafOfPair _ _ (w1Of_ne_fst _ _ _ hne01)
    dsimp only [pairOutB]
    rw [hl, mem_pair_flip, mem_pair_flip]
    rcases otherTwo_spec (ρ 0) (ρ 1) (ρ 2) (ρ 3) hne01 (hne 2 0 (by decide))
      (hne 2 1 (by decide)) (hne 3 0 (by decide)) (hne 3 1 (by decide))
      (hne 2 3 (by decide)) with huv | huv <;> cases r <;>
      simp only [w1Of, huv, ↓reduceIte, Bool.false_eq_true]
    · have ha := (beaver_mem_sortedPair_iff (ρ 1) (ρ 0) (ρ 2) (ρ 3) (hne 1 0 (by decide))
        (hne 2 1 (by decide)) (hne 2 0 (by decide)) (hne 3 1 (by decide))
        (hne 3 0 (by decide)) (hne 2 3 (by decide))).2
      have hb := (beaver_mem_sortedPair_iff (ρ 1) (ρ 0) (ρ 3) (ρ 2) (hne 1 0 (by decide))
        (hne 3 1 (by decide)) (hne 3 0 (by decide)) (hne 2 1 (by decide))
        (hne 2 0 (by decide)) (hne 3 2 (by decide))).1
      rw [ha, hb]; rfl
    · have ha := (beaver_mem_sortedPair_iff (ρ 1) (ρ 0) (ρ 2) (ρ 3) (hne 1 0 (by decide))
        (hne 2 1 (by decide)) (hne 2 0 (by decide)) (hne 3 1 (by decide))
        (hne 3 0 (by decide)) (hne 2 3 (by decide))).1
      have hb := (beaver_mem_sortedPair_iff (ρ 1) (ρ 0) (ρ 3) (ρ 2) (hne 1 0 (by decide))
        (hne 3 1 (by decide)) (hne 3 0 (by decide)) (hne 2 1 (by decide))
        (hne 2 0 (by decide)) (hne 3 2 (by decide))).2
      rw [ha, hb]; rfl
    · have ha := (beaver_mem_sortedPair_iff (ρ 1) (ρ 0) (ρ 2) (ρ 3) (hne 1 0 (by decide))
        (hne 2 1 (by decide)) (hne 2 0 (by decide)) (hne 3 1 (by decide))
        (hne 3 0 (by decide)) (hne 2 3 (by decide))).1
      have hb := (beaver_mem_sortedPair_iff (ρ 1) (ρ 0) (ρ 3) (ρ 2) (hne 1 0 (by decide))
        (hne 3 1 (by decide)) (hne 3 0 (by decide)) (hne 2 1 (by decide))
        (hne 2 0 (by decide)) (hne 3 2 (by decide))).2
      rw [ha, hb]; rfl
    · have ha := (beaver_mem_sortedPair_iff (ρ 1) (ρ 0) (ρ 2) (ρ 3) (hne 1 0 (by decide))
        (hne 2 1 (by decide)) (hne 2 0 (by decide)) (hne 3 1 (by decide))
        (hne 3 0 (by decide)) (hne 2 3 (by decide))).2
      have hb := (beaver_mem_sortedPair_iff (ρ 1) (ρ 0) (ρ 3) (ρ 2) (hne 1 0 (by decide))
        (hne 3 1 (by decide)) (hne 3 0 (by decide)) (hne 2 1 (by decide))
        (hne 2 0 (by decide)) (hne 3 2 (by decide))).1
      rw [ha, hb]; rfl
  rw [pairTree_transcriptLaw, PMF.map_comp, PMF.map_comp]
  have hLHS :
      (PMF.uniformOfFintype (Equiv.Perm (Fin 4) × Bool)).map
          ((fun q => ((pairOutA (q.1, q.2.2), q.2.2), rotChoices (pairOutB (q.2.1, q.2.2)))) ∘
            (fun (ρ, r) => (((ρ 0, ρ 1), fun _ : Fin 1 => r), (ρ 2, Fin.elim0),
              leafOfPair (sortedPair (ρ 0) (w1Of (ρ 0, ρ 1) r))))) =
        (PMF.uniformOfFintype (Equiv.Perm (Fin 4) × Bool)).map
          fun ω => (f ω, fun _ : Fin 1 => g ω) := by
    congr 1 with ⟨ρ, r⟩ : 1
  exact hLHS.trans (uniform_map_pair_eq_bind_fin1 f g σ hσ_invol hσ_f hσ_g)

private theorem xor_eq_false_left {a b : Bool} (h : xor a b = false) : a = b := by
  cases a <;> cases b <;> trivial

private theorem xor_eq_true_left {a b : Bool} (h : xor a b = true) : a = !b := by
  cases a <;> cases b <;> trivial

private theorem pairTree_bob_private :
    IndepUniform (Communication.Protocol.transcriptLaw pairTree
        (Communication.PrivateCoin.inputLaw 1 0 deal211))
      (fun (_, y, t) => (t, pairOutB (y, t)))
      (fun (x, y, t) => rotUnselected (pairOutA (x, t)) (pairOutB (y, t))) := by
  refine ⟨?_⟩
  let f : Equiv.Perm (Fin 4) × Bool → Fin pairTree.leafCount × (Fin 1 → Bool × Bool) :=
    fun (ρ, r) =>
      let l := leafOfPair (sortedPair (ρ 0) (w1Of (ρ 0, ρ 1) r))
      (l, pairOutB ((ρ 2, Fin.elim0), l))
  let g : Equiv.Perm (Fin 4) × Bool → Bool := fun (ρ, r) =>
    let l := leafOfPair (sortedPair (ρ 0) (w1Of (ρ 0, ρ 1) r))
    rotUnselected (pairOutA (((ρ 0, ρ 1), fun _ => r), l)) (pairOutB ((ρ 2, Fin.elim0), l)) 0
  let σ : Equiv.Perm (Fin 4) × Bool → Equiv.Perm (Fin 4) × Bool :=
    fun (ρ, r) =>
      if xor r (rFlip ρ)
      then (ρ * Equiv.swap (0 : Fin 4) 3, !(rFlip (ρ * Equiv.swap (0 : Fin 4) 3)))
      else (ρ * Equiv.swap (1 : Fin 4) 3, rFlip (ρ * Equiv.swap (1 : Fin 4) 3))
  have hσ_invol : ∀ ω, σ (σ ω) = ω := fun ⟨ρ, r⟩ => by
    dsimp only [σ]
    cases hb : xor r (rFlip ρ)
    · have hr : r = rFlip ρ := xor_eq_false_left hb
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_self, mul_assoc]
      have hsq : Equiv.swap (1 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 3 = 1 := by decide
      rw [hsq, mul_one, hr]
    · have hr : r = !(rFlip ρ) := xor_eq_true_left hb
      simp only [↓reduceIte, Bool.not_xor_self, mul_assoc]
      have hsq : Equiv.swap (0 : Fin 4) 3 * Equiv.swap (0 : Fin 4) 3 = 1 := by decide
      rw [hsq, mul_one, hr]
  have hs0 : ∀ ρ : Equiv.Perm (Fin 4),
      ((ρ * Equiv.swap (0 : Fin 4) 3) 0 = ρ 3) ∧
      ((ρ * Equiv.swap (0 : Fin 4) 3) 1 = ρ 1) ∧
      ((ρ * Equiv.swap (0 : Fin 4) 3) 2 = ρ 2) ∧
      ((ρ * Equiv.swap (0 : Fin 4) 3) 3 = ρ 0) := fun ρ => by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 4) ≠ 0) (by decide : (1 : Fin 4) ≠ 3),
      Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 4) ≠ 0) (by decide : (2 : Fin 4) ≠ 3),
      and_self]
  have hs1 : ∀ ρ : Equiv.Perm (Fin 4),
      ((ρ * Equiv.swap (1 : Fin 4) 3) 0 = ρ 0) ∧
      ((ρ * Equiv.swap (1 : Fin 4) 3) 1 = ρ 3) ∧
      ((ρ * Equiv.swap (1 : Fin 4) 3) 2 = ρ 2) ∧
      ((ρ * Equiv.swap (1 : Fin 4) 3) 3 = ρ 1) := fun ρ => by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 4) ≠ 1) (by decide : (0 : Fin 4) ≠ 3),
      Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 4) ≠ 1) (by decide : (2 : Fin 4) ≠ 3),
      and_self]
  have hσ_f : ∀ ω, f (σ ω) = f ω := fun ⟨ρ, r⟩ => by
    dsimp only [f, σ]
    cases hb : xor r (rFlip ρ)
    · have hr : r = xor false (rFlip ρ) := (xor_eq_false_left hb).trans (Bool.false_xor _).symm
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hrf' : rFlip (ρ * Equiv.swap (1 : Fin 4) 3) =
          xor false (rFlip (ρ * Equiv.swap (1 : Fin 4) 3)) := (Bool.false_xor _).symm
      rw [hr]
      conv_lhs => rw [hrf']
      rw [w1Of_rFlip, w1Of_rFlip, (hs1 ρ).1, (hs1 ρ).2.2.1]
      rfl
    · have hr : r = xor true (rFlip ρ) := (xor_eq_true_left hb).trans (Bool.true_xor _).symm
      simp only [↓reduceIte]
      have hrf' : (!rFlip (ρ * Equiv.swap (0 : Fin 4) 3)) =
          xor true (rFlip (ρ * Equiv.swap (0 : Fin 4) 3)) := (Bool.true_xor _).symm
      rw [hr]
      conv_lhs => rw [hrf']
      rw [w1Of_rFlip, w1Of_rFlip, (hs0 ρ).1, (hs0 ρ).2.2.2, (hs0 ρ).2.2.1, sortedPair_comm]
      rfl
  have hσ_g : ∀ ω, g (σ ω) = !(g ω) := fun ⟨ρ, r⟩ => by
    have hne : ∀ i j : Fin 4, i ≠ j → ρ i ≠ ρ j := fun i j hij => ρ.injective.ne hij
    dsimp only [g, σ]
    cases hb : xor r (rFlip ρ)
    · have hr : r = xor false (rFlip ρ) := (xor_eq_false_left hb).trans (Bool.false_xor _).symm
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hrf' : rFlip (ρ * Equiv.swap (1 : Fin 4) 3) =
          xor false (rFlip (ρ * Equiv.swap (1 : Fin 4) 3)) := (Bool.false_xor _).symm
      have hleaf : sortedPair ((ρ * Equiv.swap (1 : Fin 4) 3) 0)
            (w1Of ((ρ * Equiv.swap (1 : Fin 4) 3) 0, (ρ * Equiv.swap (1 : Fin 4) 3) 1)
              (rFlip (ρ * Equiv.swap (1 : Fin 4) 3))) =
          sortedPair (ρ 0) (ρ 2) := by
        rw [hrf', w1Of_rFlip, (hs1 ρ).1, (hs1 ρ).2.2.1]; rfl
      have hleaf2 : sortedPair (ρ 0) (w1Of (ρ 0, ρ 1) r) = sortedPair (ρ 0) (ρ 2) := by
        rw [hr, w1Of_rFlip]; rfl
      rw [hleaf, hleaf2, (hs1 ρ).2.2.1]
      have hl : leafToPair (leafOfPair (sortedPair (ρ 0) (ρ 2))) = sortedPair (ρ 0) (ρ 2) :=
        leafToPair_leafOfPair _ _ (hne 0 2 (by decide))
      have hc : (pairOutB ((ρ 2, Fin.elim0), leafOfPair (sortedPair (ρ 0) (ρ 2))) 0).1 = false := by
        dsimp only [pairOutB]
        rw [hl, mem_pair_flip]
        have hm := (beaver_mem_sortedPair_iff (ρ 1) (ρ 0) (ρ 2) (ρ 3) (hne 1 0 (by decide))
          (hne 2 1 (by decide)) (hne 2 0 (by decide)) (hne 3 1 (by decide))
          (hne 3 0 (by decide)) (hne 2 3 (by decide))).2
        rw [hm]; rfl
      dsimp only [rotUnselected]
      rw [hc]
      dsimp only [pairOutA]
      rw [hrf', hr, w2Of_rFlip, w2Of_rFlip]
      simp only [Bool.false_eq_true, ↓reduceIte, (hs1 ρ).2.1, (hs1 ρ).2.2.2]
      exact decide_lt_swap (hne 1 3 (by decide))
    · have hr : r = xor true (rFlip ρ) := (xor_eq_true_left hb).trans (Bool.true_xor _).symm
      simp only [↓reduceIte]
      have hrf' : (!rFlip (ρ * Equiv.swap (0 : Fin 4) 3)) =
          xor true (rFlip (ρ * Equiv.swap (0 : Fin 4) 3)) := (Bool.true_xor _).symm
      have hleaf : sortedPair ((ρ * Equiv.swap (0 : Fin 4) 3) 0)
            (w1Of ((ρ * Equiv.swap (0 : Fin 4) 3) 0, (ρ * Equiv.swap (0 : Fin 4) 3) 1)
              (!rFlip (ρ * Equiv.swap (0 : Fin 4) 3))) =
          sortedPair (ρ 0) (ρ 3) := by
        rw [hrf', w1Of_rFlip, (hs0 ρ).1, (hs0 ρ).2.2.2, sortedPair_comm]; rfl
      have hleaf2 : sortedPair (ρ 0) (w1Of (ρ 0, ρ 1) r) = sortedPair (ρ 0) (ρ 3) := by
        rw [hr, w1Of_rFlip]; rfl
      rw [hleaf, hleaf2, (hs0 ρ).2.2.1]
      have hl : leafToPair (leafOfPair (sortedPair (ρ 0) (ρ 3))) = sortedPair (ρ 0) (ρ 3) :=
        leafToPair_leafOfPair _ _ (hne 0 3 (by decide))
      have hc : (pairOutB ((ρ 2, Fin.elim0), leafOfPair (sortedPair (ρ 0) (ρ 3))) 0).1 = true := by
        dsimp only [pairOutB]
        rw [hl, mem_pair_flip]
        have hm := (beaver_mem_sortedPair_iff (ρ 1) (ρ 0) (ρ 2) (ρ 3) (hne 1 0 (by decide))
          (hne 2 1 (by decide)) (hne 2 0 (by decide)) (hne 3 1 (by decide))
          (hne 3 0 (by decide)) (hne 2 3 (by decide))).1
        rw [hm]; rfl
      dsimp only [rotUnselected]
      rw [hc]
      dsimp only [pairOutA]
      rw [hrf', hr, w1Of_rFlip, w1Of_rFlip]
      simp only [↓reduceIte, (hs0 ρ).1, (hs0 ρ).2.2.2]
      exact decide_lt_swap (hne 0 3 (by decide))
  rw [pairTree_transcriptLaw, PMF.map_comp, PMF.map_comp]
  have hLHS :
      (PMF.uniformOfFintype (Equiv.Perm (Fin 4) × Bool)).map
          ((fun q => ((q.2.2, pairOutB (q.2.1, q.2.2)),
              rotUnselected (pairOutA (q.1, q.2.2)) (pairOutB (q.2.1, q.2.2)))) ∘
            (fun (ρ, r) => (((ρ 0, ρ 1), fun _ : Fin 1 => r), (ρ 2, Fin.elim0),
              leafOfPair (sortedPair (ρ 0) (w1Of (ρ 0, ρ 1) r))))) =
        (PMF.uniformOfFintype (Equiv.Perm (Fin 4) × Bool)).map
          fun ω => (f ω, fun _ : Fin 1 => g ω) := by
    congr 1 with ⟨ρ, r⟩ : 1
  exact hLHS.trans (uniform_map_pair_eq_bind_fin1 f g σ hσ_invol hσ_f hσ_g)

/-- `pairTree` nonvacuously satisfies all correctness and privacy hypotheses of
`privateCoin_rot_le_one_of_deal211` for `1` OT. -/
example : (1 : ℕ) ≤ 1 :=
  privateCoin_rot_le_one_of_deal211 pairTree pairOutA pairOutB
    pairTree_correct pairTree_alice_private pairTree_bob_private

/-- `pairTree` nonvacuously witnesses `commProtocol_rot_le_mutualInfo` over
`Communication.PrivateCoin.inputLaw 1 0 deal211` at `k = 1`. -/
example : (1 : ℝ) ≤ mutualInfo (Communication.PrivateCoin.inputLaw 1 0 deal211) := by
  simpa using commProtocol_rot_le_mutualInfo pairTree
    (Communication.PrivateCoin.inputLaw 1 0 deal211)
    pairOutA pairOutB pairTree_correct_inputLaw pairTree_alice_private pairTree_bob_private

end CslibFrontierTests.CorrelatedOTBound
