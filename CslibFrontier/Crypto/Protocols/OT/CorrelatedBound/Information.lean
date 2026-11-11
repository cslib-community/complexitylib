/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.MutualInformation
public import CslibFrontier.Computability.Communication.Information
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product

/-!
# Information-theoretic upper bound on oblivious transfer from correlated randomness

For a joint law of a correlated source `(A, B)`, Alice's and Bob's final views `(V_A, V_B)`, a
public transcript `T`, and `k` random oblivious transfer (ROT) outputs `(S, R)`:

1. Conditional mutual information satisfies deterministic data processing
   (`condMutualInfo_map_le_of_comp`) and is non-increasing when conditioning on a public message
   determined by one party's view and the prior transcript
   (`condMutualInfo_map_pair_fst_le_of_eq_zero`, `condMutualInfo_map_pair_snd_le_of_eq_zero`).
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

* `Cslib.Crypto.Protocols.OT.condMutualInfo_map_le_of_comp`: conditional data processing for
  deterministic maps on the support.
* `Cslib.Crypto.Protocols.OT.condMutualInfo_map_pair_fst_le_of_eq_zero`,
  `Cslib.Crypto.Protocols.OT.condMutualInfo_map_pair_snd_le_of_eq_zero`: public messages
  conditionally independent of the other party given the speaker's state cannot increase
  conditional mutual information.
* `Cslib.Crypto.Protocols.OT.condMutualInfo_le_mutualInfo_of_internal_le_external`: bridge from
  `Cslib.Communication.internalInfoCost ≤ Cslib.Communication.externalInfoCost` to
  `I(X; Y | T) ≤ I(X; Y)`.
* `Cslib.Crypto.Protocols.OT.condMutualInfo_rot_eq`: `I(S; R | T) = k` for `k` correct and
  perfectly private random OTs.
* `Cslib.Crypto.Protocols.OT.natCast_le_mutualInfo_of_rot`: the upper bound `(k : ℝ) ≤ I(A; B)`.

## References

* [R. Ahlswede and I. Csiszár, *Common Randomness in Information Theory and Cryptography.
  Part I: Secret Sharing*][AhlswedeCsiszar1993] (bibliographic metadata verified; primary full text
  not audited in this session).
* [A. C. A. Nascimento and A. Winter, *On the Oblivious-Transfer Capacity of Noisy
  Resources*][NascimentoWinter2008] (bibliographic metadata verified; primary full text not audited
  in this session).
* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][CoverThomas2006] (information-
  theoretic background; printed book not audited in this session).
-/

public section

namespace Cslib.Crypto.Protocols.OT

open Cslib.Probability Cslib.Probability.PMF Cslib.Communication
open scoped ENNReal

variable {Ω α β γ δ τ : Type*}

/-! ### Conditional mutual information chain rules and data processing -/

/-- Symmetry of conditional mutual information in its two foreground variables:
`I(A; B | C) = I(B; A | C)`. -/
theorem condMutualInfo_map_swap [Finite γ] [Finite α] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (B : Ω → β) :
    condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) =
      condMutualInfo (ν.map fun ω => (C ω, B ω, A ω)) := by
  rw [condMutualInfo_map, condMutualInfo_map,
    entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω, B ω))
      (G := fun ω => (C ω, B ω, A ω)) (e := fun t => (t.1, t.2.2, t.2.1))
      (fun s t h => by
        obtain ⟨c, a, b⟩ := s
        obtain ⟨c', a', b'⟩ := t
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1))
      (fun _ _ => rfl)]
  ring

/-- Chain rule for conditional mutual information in the first foreground variable:
`I((D, A); B | C) = I(D; B | C) + I(A; B | (C, D))`. -/
theorem condMutualInfo_map_prodMk_left_eq_add [Finite γ] [Finite δ] [Finite α] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (D : Ω → δ) (A : Ω → α) (B : Ω → β) :
    condMutualInfo (ν.map fun ω => (C ω, (D ω, A ω), B ω)) =
      condMutualInfo (ν.map fun ω => (C ω, D ω, B ω)) +
        condMutualInfo (ν.map fun ω => ((C ω, D ω), A ω, B ω)) := by
  rw [condMutualInfo_map, condMutualInfo_map, condMutualInfo_map,
    entropy_map_eq_of_comp ν (F := fun ω => ((C ω, D ω), A ω))
      (G := fun ω => (C ω, (D ω, A ω))) (e := fun t => (t.1.1, (t.1.2, t.2)))
      (fun s t h => by
        obtain ⟨⟨c, d⟩, a⟩ := s
        obtain ⟨⟨c', d'⟩, a'⟩ := t
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1 h.2.1) h.2.2)
      (fun _ _ => rfl),
    entropy_map_eq_of_comp ν (F := fun ω => ((C ω, D ω), B ω))
      (G := fun ω => (C ω, D ω, B ω)) (e := fun t => (t.1.1, t.1.2, t.2))
      (fun s t h => by
        obtain ⟨⟨c, d⟩, b⟩ := s
        obtain ⟨⟨c', d'⟩, b'⟩ := t
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1 h.2.1) h.2.2)
      (fun _ _ => rfl),
    entropy_map_eq_of_comp ν (F := fun ω => ((C ω, D ω), A ω, B ω))
      (G := fun ω => (C ω, (D ω, A ω), B ω)) (e := fun t => (t.1.1, (t.1.2, t.2.1), t.2.2))
      (fun s t h => by
        obtain ⟨⟨c, d⟩, a, b⟩ := s
        obtain ⟨⟨c', d'⟩, a', b'⟩ := t
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1 h.2.1.1) (Prod.ext h.2.1.2 h.2.2))
      (fun _ _ => rfl)]
  ring

/-- Chain rule for conditional mutual information in the second foreground variable:
`I(A; (D, B) | C) = I(A; D | C) + I(A; B | (C, D))`. -/
theorem condMutualInfo_map_prodMk_right_eq_add [Finite γ] [Finite α] [Finite δ] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (D : Ω → δ) (B : Ω → β) :
    condMutualInfo (ν.map fun ω => (C ω, A ω, (D ω, B ω))) =
      condMutualInfo (ν.map fun ω => (C ω, A ω, D ω)) +
        condMutualInfo (ν.map fun ω => ((C ω, D ω), A ω, B ω)) := by
  rw [condMutualInfo_map_swap ν C A (fun ω => (D ω, B ω)),
    condMutualInfo_map_prodMk_left_eq_add ν C D B A,
    condMutualInfo_map_swap ν C D A,
    condMutualInfo_map_swap ν (fun ω => (C ω, D ω)) B A]

/-- Conditional mutual information decreases when replacing the first foreground variable by a
function determined on the support: `I(S; B | C) ≤ I(A; B | C)`. -/
theorem condMutualInfo_map_le_of_comp_left {α' : Type*}
    [Finite γ] [Finite α] [Finite α'] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (S : Ω → α') (B : Ω → β)
    (f : α → α') (hf : ∀ ω ∈ ν.support, S ω = f (A ω)) :
    condMutualInfo (ν.map fun ω => (C ω, S ω, B ω)) ≤
      condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) := by
  have h1 : condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) =
      condMutualInfo (ν.map fun ω => (C ω, (S ω, A ω), B ω)) := by
    rw [condMutualInfo_map, condMutualInfo_map,
      entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω)) (G := fun ω => (C ω, (S ω, A ω)))
        (e := fun t => (t.1, (f t.2, t.2)))
        (fun s t h => by
          obtain ⟨c, a⟩ := s
          obtain ⟨c', a'⟩ := t
          simp only [Prod.mk.injEq] at h
          exact Prod.ext h.1 h.2.2)
        (fun ω hω => by simp [hf ω hω]),
      entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω, B ω))
        (G := fun ω => (C ω, (S ω, A ω), B ω)) (e := fun t => (t.1, (f t.2.1, t.2.1), t.2.2))
        (fun s t h => by
          obtain ⟨c, a, b⟩ := s
          obtain ⟨c', a', b'⟩ := t
          simp only [Prod.mk.injEq] at h
          exact Prod.ext h.1 (Prod.ext h.2.1.2 h.2.2))
        (fun ω hω => by simp [hf ω hω])]
  rw [h1, condMutualInfo_map_prodMk_left_eq_add]
  have := condMutualInfo_nonneg (ν.map fun ω => ((C ω, S ω), A ω, B ω))
  linarith

/-- Conditional data processing for deterministic maps on both foreground variables:
if `S` is determined by `A` and `R` is determined by `B` on the support of `ν`, then
`I(S; R | C) ≤ I(A; B | C)`. -/
theorem condMutualInfo_map_le_of_comp {α' β' : Type*}
    [Finite γ] [Finite α] [Finite α'] [Finite β] [Finite β']
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (S : Ω → α') (B : Ω → β) (R : Ω → β')
    (f : α → α') (hf : ∀ ω ∈ ν.support, S ω = f (A ω))
    (g : β → β') (hg : ∀ ω ∈ ν.support, R ω = g (B ω)) :
    condMutualInfo (ν.map fun ω => (C ω, S ω, R ω)) ≤
      condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) := by
  calc condMutualInfo (ν.map fun ω => (C ω, S ω, R ω))
      ≤ condMutualInfo (ν.map fun ω => (C ω, A ω, R ω)) :=
        condMutualInfo_map_le_of_comp_left ν C A S R f hf
    _ = condMutualInfo (ν.map fun ω => (C ω, R ω, A ω)) :=
        condMutualInfo_map_swap ν C A R
    _ ≤ condMutualInfo (ν.map fun ω => (C ω, B ω, A ω)) :=
        condMutualInfo_map_le_of_comp_left ν C B R A g hg
    _ = condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) :=
        condMutualInfo_map_swap ν C B A

/-- Conditioning on a message `M` that carries no conditional mutual information with `B` given
`(C, A)` cannot increase `I(A; B | C)`. -/
theorem condMutualInfo_map_pair_fst_le_of_eq_zero [Finite γ] [Finite δ] [Finite α] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (M : Ω → δ) (A : Ω → α) (B : Ω → β)
    (h : condMutualInfo (ν.map fun ω => ((C ω, A ω), M ω, B ω)) = 0) :
    condMutualInfo (ν.map fun ω => ((C ω, M ω), A ω, B ω)) ≤
      condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) := by
  have h1 := condMutualInfo_map_prodMk_left_eq_add ν C M A B
  have h2 := condMutualInfo_map_prodMk_left_eq_add ν C A M B
  have hswap : condMutualInfo (ν.map fun ω => (C ω, (M ω, A ω), B ω)) =
      condMutualInfo (ν.map fun ω => (C ω, (A ω, M ω), B ω)) := by
    rw [condMutualInfo_map, condMutualInfo_map,
      entropy_map_eq_of_comp ν (F := fun ω => (C ω, (A ω, M ω)))
        (G := fun ω => (C ω, (M ω, A ω))) (e := Prod.map id Prod.swap)
        (Function.injective_id.prodMap Prod.swap_injective) (fun _ _ => rfl),
      entropy_map_eq_of_comp ν (F := fun ω => (C ω, (A ω, M ω), B ω))
        (G := fun ω => (C ω, (M ω, A ω), B ω))
        (e := Prod.map id (Prod.map Prod.swap id))
        (Function.injective_id.prodMap (Prod.swap_injective.prodMap Function.injective_id))
        (fun _ _ => rfl)]
  have hnonneg := condMutualInfo_nonneg (ν.map fun ω => (C ω, M ω, B ω))
  linarith

/-- Symmetric form: conditioning on a message `M` that carries no conditional mutual information
with `A` given `(C, B)` cannot increase `I(A; B | C)`. -/
theorem condMutualInfo_map_pair_snd_le_of_eq_zero [Finite γ] [Finite δ] [Finite α] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (M : Ω → δ) (A : Ω → α) (B : Ω → β)
    (h : condMutualInfo (ν.map fun ω => ((C ω, B ω), M ω, A ω)) = 0) :
    condMutualInfo (ν.map fun ω => ((C ω, M ω), A ω, B ω)) ≤
      condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) := by
  rw [condMutualInfo_map_swap ν (fun ω => (C ω, M ω)) A B,
    condMutualInfo_map_swap ν C A B]
  exact condMutualInfo_map_pair_fst_le_of_eq_zero ν C M B A h

/-- Independent private randomness does not change mutual information:
`I((A, R₀); (B, R₁)) = I(A; B)`. -/
theorem mutualInfo_bind_pair_indep [Finite α] [Finite β] [Finite γ] [Finite δ]
    (source : PMF (α × β)) (c₀ : PMF γ) (c₁ : PMF δ) :
    mutualInfo (source.bind fun ab => c₀.bind fun r₀ => c₁.map fun r₁ =>
      ((ab.1, r₀), (ab.2, r₁))) = mutualInfo source := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  let joint := source.bind fun ab => c₀.bind fun r₀ => c₁.map fun r₁ => ((ab.1, r₀), (ab.2, r₁))
  have hfst : joint.map Prod.fst =
      (source.map Prod.fst).bind fun a => c₀.map (a, ·) := by
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
    calc source.bind (fun ab => c₀.bind fun r₀ => c₁.map (Function.const δ (ab.1, r₀)))
        = source.bind (fun ab => c₀.map (ab.1, ·)) := by
          congr 1 with ab : 1
          simp only [PMF.map_const]
          rfl
      _ = (source.map Prod.fst).bind fun a => c₀.map (a, ·) := by
          rw [PMF.bind_map]
          rfl
  have hsnd : joint.map Prod.snd =
      (source.map Prod.snd).bind fun b => c₁.map (b, ·) := by
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
    calc source.bind (fun ab => c₀.bind (fun _ => c₁.map (ab.2, ·)))
        = source.bind (fun ab => c₁.map (ab.2, ·)) := by
          congr 1 with ab : 1
          exact PMF.bind_const c₀ _
      _ = (source.map Prod.snd).bind fun b => c₁.map (b, ·) := by
          rw [PMF.bind_map]
          rfl
  have hjoint : entropy joint = entropy source + entropy c₀ + entropy c₁ := by
    let e : (α × β) × (γ × δ) ≃ (α × γ) × (β × δ) :=
      Equiv.prodProdProdComm α β γ δ
    have heq : joint = (source.bind fun ab => (c₀.bind fun r₀ => c₁.map (r₀, ·)).map (ab, ·)).map
        e := by
      simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def, e]
      rfl
    rw [heq, entropy_map_of_injective _ e.injective, entropy_bind_pair]
    simp only [← Finset.sum_mul, sum_toReal, one_mul, entropy_prod]
    ring
  have hMI_joint : mutualInfo joint =
      entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) - entropy joint := by
    have hid : joint.map (fun p => (p.1, p.2)) = joint := PMF.map_id joint
    simpa only [hid] using mutualInfo_map joint Prod.fst Prod.snd
  have hMI_source : mutualInfo source =
      entropy (source.map Prod.fst) + entropy (source.map Prod.snd) - entropy source := by
    have hid : source.map (fun p => (p.1, p.2)) = source := PMF.map_id source
    simpa only [hid] using mutualInfo_map source Prod.fst Prod.snd
  rw [hMI_joint, hMI_source, hfst, hsnd, entropy_prod, entropy_prod, hjoint]
  ring

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

@[simp] theorem otSelect_false (pair : Bool × Bool) : otSelect pair false = pair.1 := rfl
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
    (hAlicePriv : ν.map (fun ω => ((S ω, T ω), rotChoices (R ω))) =
      (ν.map fun ω => (S ω, T ω)).bind fun st =>
        (PMF.uniformOfFintype (Fin k → Bool)).map (st, ·))
    (hBobPriv : ν.map (fun ω => ((T ω, R ω), rotUnselected (S ω) (R ω))) =
      (ν.map fun ω => (T ω, R ω)).bind fun tr =>
        (PMF.uniformOfFintype (Fin k → Bool)).map (tr, ·)) :
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
    rw [hmap, hAlicePriv]
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
    rw [hAlicePriv, PMF.map_bind]
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
  have hTCU : ν.map (fun ω => ((T ω, C ω), U ω)) =
      (ν.map fun ω => (T ω, C ω)).bind fun tc =>
        (PMF.uniformOfFintype (Fin k → Bool)).map (tc, ·) := by
    have h1 : ν.map (fun ω => ((T ω, C ω), U ω)) =
        (ν.map fun ω => ((T ω, R ω), U ω)).map fun ((t, r), u) => ((t, rotChoices r), u) := by
      rw [PMF.map_comp]
      rfl
    have h2 : ν.map (fun ω => (T ω, C ω)) =
        (ν.map fun ω => (T ω, R ω)).map fun (t, r) => (t, rotChoices r) := by
      rw [PMF.map_comp]
      rfl
    rw [h1, hBobPriv, PMF.map_bind]
    conv_rhs => rw [h2, PMF.bind_map]
    congr 1 with ⟨t, r⟩ : 1
    rw [PMF.map_comp]
    rfl
  have hTCY : ν.map (fun ω => ((T ω, C ω), Y ω)) =
      (ν.map fun ω => (T ω, C ω)).bind fun tc =>
        (PMF.uniformOfFintype (Fin k → Bool)).map (tc, ·) := by
    have h1 : ν.map (fun ω => ((T ω, C ω), Y ω)) =
        (ν.map fun ω => ((T ω, bitFlip (C ω)), Y ω)).map
          (Prod.map (Prod.map id bitFlip) id) := by
      rw [PMF.map_comp]
      refine congrArg (ν.map ·) (funext fun ω => ?_)
      dsimp only [Function.comp_def, Prod.map, id_eq]
      rw [bitFlip_bitFlip]
    rw [h1, hFlipEq, hTCU, PMF.map_bind]
    conv_rhs => rw [← hTC_flip, PMF.bind_map]
    congr 1 with tc : 1
    rw [PMF.map_comp]
    rfl
  rw [hSC, zero_add, hSY, hTCY, entropy_prod, entropy_uniform, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one one_lt_two]
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
    (hAlicePriv : ν.map (fun ω => ((S ω, T ω), rotChoices (R ω))) =
      (ν.map fun ω => (S ω, T ω)).bind fun st =>
        (PMF.uniformOfFintype (Fin k → Bool)).map (st, ·))
    (hBobPriv : ν.map (fun ω => ((T ω, R ω), rotUnselected (S ω) (R ω))) =
      (ν.map fun ω => (T ω, R ω)).bind fun tr =>
        (PMF.uniformOfFintype (Fin k → Bool)).map (tr, ·)) :
    (k : ℝ) ≤ mutualInfo (ν.map fun ω => (A ω, B ω)) := by
  calc (k : ℝ)
      = condMutualInfo (ν.map fun ω => (T ω, S ω, R ω)) :=
        (condMutualInfo_rot_eq ν T S R hCorrect hAlicePriv hBobPriv).symm
    _ ≤ condMutualInfo (ν.map fun ω => (T ω, VA ω, VB ω)) :=
        condMutualInfo_map_le_of_comp ν T VA S VB R outA hOutA outB hOutB
    _ ≤ mutualInfo (ν.map fun ω => (A ω, B ω)) := hTranscript

end Cslib.Crypto.Protocols.OT
