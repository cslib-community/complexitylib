/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Crypto.Computational.CramerShoup.Scheme
public import Complexity.Languages.Probabilistic.UniformNat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Crypto.Game.Statistical
import Complexity.Probability.PMF
import Complexity.Probability.StatisticalDistance
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Certified PPT Reductions and Probabilistic Operations for Cramer–Shoup

This module constructs the uniform strict-PPT (`IsPPTOn`) operations and security reductions for the
**Multiplicative Cramer–Shoup public-key encryption scheme** ($\mathcal{E}_{\mathrm{MCS}}$,
[Boneh and Shoup, Exercise 12.27, printed pp. 521–522][BonehShoup2023], specialized to associated
data $\mathcal{D} = \mathrm{Unit}$) over a `PrimeOrderGroupFamily`, following the Games 0–4
reduction structure of [Boneh and Shoup, Section 12.5.3, Theorem 12.9, printed
pp. 488–493][BonehShoup2023]:

1. **Approximate exponent sampling via `sampleModNat`**: `sampleExp`,
   `sampleCramerShoupPair`, `sampleCramerShoupTripleExponents`, and `sampleCramerShoupSK`, together
   with their `IsPPTOn` certificates and `Game.advantage` bounds (`1 / 2 ^ n` per exponent draw)
   relative to exact uniform sampling on `ZMod (F.order d)`.
2. **Phase 1/2 and collision-tracking decryption oracle handlers**: `cramerShoupPhase1Oracle`,
   `cramerShoupPhase2Reply`, `cramerShoupPhase2Oracle`, and `cramerShoupCollisionPhase2Oracle`.
3. **Certified strict-PPT DDH distinguishers (`Game 1 → Game 2`, eq. (12.22), printed p. 492)**:
   `cramerShoupMsgToDDHDistinguisher` and `cramerShoupToDDHDistinguisher`, with `IsPPTOn`
   certificates `isPPTOn_cramerShoupMsgToDDHDistinguisher` and
   `isPPTOn_cramerShoupToDDHDistinguisher`.
4. **Certified strict-PPT CRHF collision finders (`Game 3 → Game 4`, eqs. (12.24)–(12.25), printed
   p. 492)**: `cramerShoupMsgToCollisionFinder` and `cramerShoupToCollisionFinder`, with `IsPPTOn`
   certificates `isPPTOn_cramerShoupMsgToCollisionFinder` and
   `isPPTOn_cramerShoupToCollisionFinder`.
5. **Certified strict-PPT `Encryption.cca2GameOn` operations**: `cramerShoupValid`,
   `cramerShoupKeyGenProb`, `cramerShoupEncryptProb`, and `cramerShoupDecryptOpt`, together with
   their `ComputableInPolyTime` and `IsPPTOn` certificates.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM ProjectiveHash Encryption Game
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

@[local fun_prop]
private theorem computableTidilyInPolyTime_decodeBits4 :
    ComputableTidilyInPolyTime decodeBits4 encBits
      (encPair encBits (encPair encBits (encPair encBits encBits))) :=
  computableInPolyTime_decodeBits4.tidy

@[local fun_prop]
private theorem computableTidilyInPolyTime_extractCramerShoupTriple :
    ComputableTidilyInPolyTime extractCramerShoupTriple encBits encBits :=
  computableInPolyTime_extractCramerShoupTriple.tidy

@[local fun_prop]
private theorem computableTidilyInPolyTime_encodeCramerShoupPublicKey
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc} {u : γ → List Bool}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hu : ComputableTidilyInPolyTime u encIn encBits)
    (hsk : ComputableTidilyInPolyTime sk encIn encCramerShoupSK) :
    ComputableTidilyInPolyTime
      (fun a => F.encodeCramerShoupPublicKey (d a) (u a) (sk a)) encIn encBits :=
  F.computableInPolyTime_encodeCramerShoupPublicKey.tidy.comp (hd.prod (hu.prod hsk))

@[local fun_prop]
private theorem computableTidilyInPolyTime_encodeCramerShoupChallenge
    {H : F.Desc × List Bool → List Bool}
    (hH : ComputableTidilyInPolyTime H (encPair F.encDesc encBits) encBits)
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {v w m : γ → List Bool}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hsk : ComputableTidilyInPolyTime sk encIn encCramerShoupSK)
    (hv : ComputableTidilyInPolyTime v encIn encBits)
    (hw : ComputableTidilyInPolyTime w encIn encBits)
    (hm : ComputableTidilyInPolyTime m encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => F.encodeCramerShoupChallenge H (d a) (sk a) (v a) (w a) (m a))
      encIn encBits :=
  (F.computableInPolyTime_encodeCramerShoupChallenge (.of_tidy hH)).tidy.comp
    (hd.prod (hsk.prod (hv.prod (hw.prod hm))))

@[local fun_prop]
private theorem computableTidilyInPolyTime_encodeCramerShoupEncrypt
    {H : F.Desc × List Bool → List Bool}
    (hH : ComputableTidilyInPolyTime H (encPair F.encDesc encBits) encBits)
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc}
    {pk : γ → List Bool × List Bool × List Bool × List Bool} {m : γ → List Bool} {b : γ → ℕ}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hpk : ComputableTidilyInPolyTime pk encIn
      (encPair encBits (encPair encBits (encPair encBits encBits))))
    (hm : ComputableTidilyInPolyTime m encIn encBits)
    (hb : ComputableTidilyInPolyTime b encIn encNat) :
    ComputableTidilyInPolyTime
      (fun a => F.encodeCramerShoupEncrypt H (d a) (pk a) (m a) (b a)) encIn encBits :=
  (F.computableInPolyTime_encodeCramerShoupEncrypt (.of_tidy hH)).tidy.comp
    (hd.prod (hpk.prod (hm.prod hb)))

private theorem computableTidilyInPolyTime_comp {α β γ : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {g : β → γ} {f : α → β}
    (hg : ComputableTidilyInPolyTime g encB encC)
    (hf : ComputableTidilyInPolyTime f encA encB) :
    ComputableTidilyInPolyTime (fun a => g (f a)) encA encC :=
  hg.comp hf

private theorem computableTidilyInPolyTime_decodeCramerShoup
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableTidilyInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableTidilyInPolyTime isElem (encPair F.encDesc encBits) encBool)
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {ct : γ → List Bool}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hsk : ComputableTidilyInPolyTime sk encIn encCramerShoupSK)
    (hct : ComputableTidilyInPolyTime ct encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => F.decodeCramerShoup H isElem (d a) (sk a) (ct a))
      encIn (encOption encBits) :=
  computableTidilyInPolyTime_comp
    (g := fun p : F.Desc × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) × List Bool =>
      F.decodeCramerShoup H isElem p.1 p.2.1 p.2.2)
    (f := fun a => (d a, sk a, ct a))
    (F.computableInPolyTime_decodeCramerShoup (.of_tidy hH) (.of_tidy hisElem)).tidy
    (hd.prod (hsk.prod hct))

/-! ### Approximate exponent sampling via `sampleModNat` -/

/-- Sample a pair of approximate exponents modulo `F.order d`. -/
noncomputable def sampleCramerShoupPair (n : ℕ) (d : F.Desc) : ProbComp (ℕ × ℕ) :=
  F.sampleExp n d >>= fun s =>
    F.sampleExp n d >>= fun t =>
      pure (s, t)

/-- Sample a 3-tuple of approximate exponents `(a, b, c)` modulo `F.order d`. -/
noncomputable def sampleCramerShoupTripleExponents (n : ℕ) (d : F.Desc) :
    ProbComp (ℕ × ℕ × ℕ) :=
  F.sampleExp n d >>= fun a =>
    F.sampleCramerShoupPair n d >>= fun bc =>
      pure (a, bc)

/-- Sample a 6-tuple secret key `((s, t), ((s₁, t₁), (s₂, t₂)))` of approximate exponents modulo
`F.order d`. -/
noncomputable def sampleCramerShoupSK (n : ℕ) (d : F.Desc) :
    ProbComp ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :=
  F.sampleCramerShoupPair n d >>= fun p =>
    F.sampleCramerShoupPair n d >>= fun p₁ =>
      F.sampleCramerShoupPair n d >>= fun p₂ =>
        pure (p, (p₁, p₂))

private theorem isPPTOn_sampleCramerShoupPair {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc) :
    IsPPTOn encIn (encPair encNat encNat) (fun a => F.sampleCramerShoupPair (n a) (d a)) := by
  unfold sampleCramerShoupPair
  refine (F.isPPTOn_sampleExp (.of_tidy hn) (.of_tidy hd)).bind_with ?_
  exact (F.isPPTOn_sampleExp (.of_tidy (hn.comp (by fun_prop)))
    (.of_tidy (hd.comp (by fun_prop)))).bind_with
    (ComputableTidilyInPolyTime.isPPTOn (by fun_prop))

private theorem isPPTOn_sampleCramerShoupTripleExponents {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc) :
    IsPPTOn encIn (encPair encNat (encPair encNat encNat))
      (fun a => F.sampleCramerShoupTripleExponents (n a) (d a)) := by
  unfold sampleCramerShoupTripleExponents
  refine (F.isPPTOn_sampleExp (.of_tidy hn) (.of_tidy hd)).bind_with ?_
  exact (F.isPPTOn_sampleCramerShoupPair (hn.comp (by fun_prop)) (hd.comp (by fun_prop))).bind_with
    (ComputableTidilyInPolyTime.isPPTOn (by fun_prop))

private theorem isPPTOn_sampleCramerShoupSK {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc) :
    IsPPTOn encIn encCramerShoupSK (fun a => F.sampleCramerShoupSK (n a) (d a)) := by
  unfold sampleCramerShoupSK
  refine (F.isPPTOn_sampleCramerShoupPair hn hd).bind_with ?_
  refine (F.isPPTOn_sampleCramerShoupPair
    (hn.comp (by fun_prop)) (hd.comp (by fun_prop))).bind_with ?_
  exact (F.isPPTOn_sampleCramerShoupPair
    (hn.comp (by fun_prop)) (hd.comp (by fun_prop))).bind_with
    (ComputableTidilyInPolyTime.isPPTOn (by fun_prop))

/-- Replacing `sampleCramerShoupPair n d` by two independent uniform draws on `ZMod (F.order d)`
changes `Game.advantage` by at most `2 / 2 ^ n`. -/
theorem advantage_bind_sampleCramerShoupPair_le (n : ℕ) (d : F.Desc)
    (k : ZMod (F.order d) → ZMod (F.order d) → Game) :
    Game.advantage
      ((ProbComp.eval (F.sampleCramerShoupPair n d)).bind fun p =>
        k (p.1 : ZMod (F.order d)) (p.2 : ZMod (F.order d)))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ => k σ τ) ≤
      2 / 2 ^ n := by
  simp only [sampleCramerShoupPair, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.bind_bind, PMF.pure_bind]
  refine (Game.advantage_triangle _
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ =>
      (ProbComp.eval (F.sampleExp n d)).bind fun t =>
        k σ (t : ZMod (F.order d))) _).trans ?_
  have h1 := F.advantage_bind_sampleExp_le n d (fun σ =>
    (ProbComp.eval (F.sampleExp n d)).bind fun t => k σ (t : ZMod (F.order d)))
  have h2 := advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _
    (fun σ => F.advantage_bind_sampleExp_le n d (k σ))
  calc _ ≤ (1 : ℝ≥0) / 2 ^ n + 1 / 2 ^ n := add_le_add h1 h2
    _ = 2 / 2 ^ n := by ring

/-- Replacing `sampleCramerShoupTripleExponents n d` by three independent uniform draws on
`ZMod (F.order d)` changes `Game.advantage` by at most `3 / 2 ^ n`. -/
theorem advantage_bind_sampleCramerShoupTripleExponents_le (n : ℕ) (d : F.Desc)
    (k : ZMod (F.order d) → ZMod (F.order d) → ZMod (F.order d) → Game) :
    Game.advantage
      ((ProbComp.eval (F.sampleCramerShoupTripleExponents n d)).bind fun p =>
        k (p.1 : ZMod (F.order d)) (p.2.1 : ZMod (F.order d)) (p.2.2 : ZMod (F.order d)))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ => k α β γ) ≤
      3 / 2 ^ n := by
  have hbind :
      ((ProbComp.eval (F.sampleCramerShoupTripleExponents n d)).bind fun p =>
        k (p.1 : ZMod (F.order d)) (p.2.1 : ZMod (F.order d)) (p.2.2 : ZMod (F.order d))) =
      (ProbComp.eval (F.sampleExp n d)).bind fun a =>
        (ProbComp.eval (F.sampleCramerShoupPair n d)).bind fun bc =>
          k (a : ZMod (F.order d)) (bc.1 : ZMod (F.order d)) (bc.2 : ZMod (F.order d)) := by
    simp only [sampleCramerShoupTripleExponents, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_bind, PMF.pure_bind]
  rw [hbind]
  refine (Game.advantage_triangle _
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
      (ProbComp.eval (F.sampleCramerShoupPair n d)).bind fun bc =>
        k α (bc.1 : ZMod (F.order d)) (bc.2 : ZMod (F.order d))) _).trans ?_
  have h1 := F.advantage_bind_sampleExp_le n d (fun α =>
    (ProbComp.eval (F.sampleCramerShoupPair n d)).bind fun bc =>
      k α (bc.1 : ZMod (F.order d)) (bc.2 : ZMod (F.order d)))
  have h2 := advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _
    (fun α => F.advantage_bind_sampleCramerShoupPair_le n d (k α))
  calc _ ≤ (1 : ℝ≥0) / 2 ^ n + 2 / 2 ^ n := add_le_add h1 h2
    _ = 3 / 2 ^ n := by ring

/-- Replacing `sampleCramerShoupSK n d` by six independent uniform draws on `ZMod (F.order d)`
changes `Game.advantage` by at most `6 / 2 ^ n`. -/
theorem advantage_bind_sampleCramerShoupSK_le (n : ℕ) (d : F.Desc)
    (k : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Game)
    (kZMod : ZMod (F.order d) → ZMod (F.order d) → ZMod (F.order d) →
      ZMod (F.order d) → ZMod (F.order d) → ZMod (F.order d) → Game)
    (hcast : ∀ s t s₁ t₁ s₂ t₂ : ℕ,
      k ((s, t), ((s₁, t₁), (s₂, t₂))) =
        kZMod (s : ZMod (F.order d)) (t : ZMod (F.order d))
          (s₁ : ZMod (F.order d)) (t₁ : ZMod (F.order d))
          (s₂ : ZMod (F.order d)) (t₂ : ZMod (F.order d))) :
    Game.advantage
      ((ProbComp.eval (F.sampleCramerShoupSK n d)).bind k)
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ₁ =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ₁ =>
              (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ₂ =>
                (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ₂ =>
                  kZMod σ τ σ₁ τ₁ σ₂ τ₂) ≤
      6 / 2 ^ n := by
  have hbind :
      (ProbComp.eval (F.sampleCramerShoupSK n d)).bind k =
      (ProbComp.eval (F.sampleCramerShoupPair n d)).bind fun p =>
        (ProbComp.eval (F.sampleCramerShoupPair n d)).bind fun p₁ =>
          (ProbComp.eval (F.sampleCramerShoupPair n d)).bind fun p₂ =>
            kZMod (p.1 : ZMod (F.order d)) (p.2 : ZMod (F.order d))
              (p₁.1 : ZMod (F.order d)) (p₁.2 : ZMod (F.order d))
              (p₂.1 : ZMod (F.order d)) (p₂.2 : ZMod (F.order d)) := by
    simp only [sampleCramerShoupSK, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_bind, PMF.pure_bind]
    refine congrArg _ (funext fun p =>
      congrArg _ (funext fun p₁ => congrArg _ (funext fun p₂ => ?_)))
    exact hcast p.1 p.2 p₁.1 p₁.2 p₂.1 p₂.2
  rw [hbind]
  let G1 :=
    (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ =>
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ =>
        (ProbComp.eval (F.sampleCramerShoupPair n d)).bind fun p₁ =>
          (ProbComp.eval (F.sampleCramerShoupPair n d)).bind fun p₂ =>
            kZMod σ τ (p₁.1 : ZMod (F.order d)) (p₁.2 : ZMod (F.order d))
              (p₂.1 : ZMod (F.order d)) (p₂.2 : ZMod (F.order d))
  let G2 :=
    (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ =>
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ₁ =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ₁ =>
            (ProbComp.eval (F.sampleCramerShoupPair n d)).bind fun p₂ =>
              kZMod σ τ σ₁ τ₁ (p₂.1 : ZMod (F.order d)) (p₂.2 : ZMod (F.order d))
  have hstep1 := F.advantage_bind_sampleCramerShoupPair_le n d (fun σ τ =>
    (ProbComp.eval (F.sampleCramerShoupPair n d)).bind fun p₁ =>
      (ProbComp.eval (F.sampleCramerShoupPair n d)).bind fun p₂ =>
        kZMod σ τ (p₁.1 : ZMod (F.order d)) (p₁.2 : ZMod (F.order d))
          (p₂.1 : ZMod (F.order d)) (p₂.2 : ZMod (F.order d)))
  have hstep2 := advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _
    (fun σ => advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _
      (fun τ => F.advantage_bind_sampleCramerShoupPair_le n d (fun σ₁ τ₁ =>
        (ProbComp.eval (F.sampleCramerShoupPair n d)).bind fun p₂ =>
          kZMod σ τ σ₁ τ₁ (p₂.1 : ZMod (F.order d)) (p₂.2 : ZMod (F.order d)))))
  have hstep3 := advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _
    (fun σ => advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _
      (fun τ => advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _
        (fun σ₁ => advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _
          (fun τ₁ => F.advantage_bind_sampleCramerShoupPair_le n d (kZMod σ τ σ₁ τ₁)))))
  refine (Game.advantage_triangle _ G1 _).trans ?_
  refine (add_le_add le_rfl (Game.advantage_triangle G1 G2 _)).trans ?_
  calc _ ≤ (2 : ℝ≥0) / 2 ^ n + (2 / 2 ^ n + 2 / 2 ^ n) :=
      add_le_add hstep1 (add_le_add hstep2 hstep3)
    _ = 6 / 2 ^ n := by ring


private theorem computableTidilyInPolyTime_add_unary {γ : Type} {encIn : γ ↪ List Bool}
    {f g : γ → ℕ} (hf : ComputableTidilyInPolyTime f encIn encUnary)
    (hg : ComputableTidilyInPolyTime g encIn encUnary) :
    ComputableTidilyInPolyTime (fun a => f a + g a) encIn encUnary :=
  (by fun_prop : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
    (encPair encUnary encUnary) encUnary).comp (hf.prod hg)

private theorem computableTidilyInPolyTime_isCramerShoupCollision
    {H : F.Desc × List Bool → List Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc} {req ct : γ → List Bool}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hreq : ComputableTidilyInPolyTime req encIn encBits)
    (hct : ComputableTidilyInPolyTime ct encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => F.isCramerShoupCollision H (d a) (req a) (ct a)) encIn encBool := by
  have hx :=
    computableTidilyInPolyTime_comp computableTidilyInPolyTime_extractCramerShoupTriple hreq
  have hy :=
    computableTidilyInPolyTime_comp computableTidilyInPolyTime_extractCramerShoupTriple hct
  have hbeqBits : ComputableTidilyInPolyTime (fun q : List Bool × List Bool => q.1 == q.2)
      (encPair encBits encBits) encBool := by polytime
  have hnot : ComputableTidilyInPolyTime (fun b : Bool => !b) encBool encBool := by polytime
  have hand : ComputableTidilyInPolyTime (fun q : Bool × Bool => q.1 && q.2)
      (encPair encBool encBool) encBool := by polytime
  have hne : ComputableTidilyInPolyTime
      (fun a => extractCramerShoupTriple (req a) != extractCramerShoupTriple (ct a))
      encIn encBool :=
    computableTidilyInPolyTime_comp hnot (computableTidilyInPolyTime_comp hbeqBits (hx.prod hy))
  have hord := computableTidilyInPolyTime_comp F.computableInPolyTime_order.tidy hd
  have hmodx := ComputableTidilyInPolyTime.binary_mod'
    (computableTidilyInPolyTime_comp ComputableTidilyInPolyTime.bitsToNat
      (computableTidilyInPolyTime_comp hH.tidy (hd.prod hx))) hord
  have hmody := ComputableTidilyInPolyTime.binary_mod'
    (computableTidilyInPolyTime_comp ComputableTidilyInPolyTime.bitsToNat
      (computableTidilyInPolyTime_comp hH.tidy (hd.prod hy))) hord
  have heqMod : ComputableTidilyInPolyTime
      (fun a => (ofBits (H (d a, extractCramerShoupTriple (req a))) % F.order (d a)) ==
        (ofBits (H (d a, extractCramerShoupTriple (ct a))) % F.order (d a))) encIn encBool := by
    have hcongr :
        (fun a => (ofBits (H (d a, extractCramerShoupTriple (req a))) % F.order (d a)) ==
          (ofBits (H (d a, extractCramerShoupTriple (ct a))) % F.order (d a))) =
        (fun a => encNat (ofBits (H (d a, extractCramerShoupTriple (req a))) % F.order (d a)) ==
          encNat (ofBits (H (d a, extractCramerShoupTriple (ct a))) % F.order (d a))) := by
      funext a; rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, encNat.injective.eq_iff]
    rw [hcongr]
    exact computableTidilyInPolyTime_comp hbeqBits
      ((computableTidilyInPolyTime_comp (ComputableTidilyInPolyTime.encode encNat) hmodx).prod
        (computableTidilyInPolyTime_comp (ComputableTidilyInPolyTime.encode encNat) hmody))
  exact computableTidilyInPolyTime_comp hand (hne.prod heqMod)

/-- Phase 1 decryption oracle handler for Cramer–Shoup. -/
def cramerShoupPhase1Oracle (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (d : F.Desc)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (request : Unit × List Bool) :
    StateT Unit ProbComp (List Bool) :=
  fun s => pure (F.cramerShoupPhase1Reply H isElem d sk request.2, s)

/-- Stateless Phase 2 decryption reply for Cramer–Shoup, rejecting the challenge ciphertext `ct`
with `[]`. -/
def cramerShoupPhase2Reply (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (d : F.Desc)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct req : List Bool) : List Bool :=
  if req == ct then [] else encOption encBits (F.decodeCramerShoup H isElem d sk req)

/-- Phase 2 decryption oracle handler for Cramer–Shoup, rejecting the challenge ciphertext `ct`. -/
def cramerShoupPhase2Oracle (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (d : F.Desc)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct : List Bool) (request : Unit × List Bool) :
    StateT Unit ProbComp (List Bool) :=
  fun s => pure (F.cramerShoupPhase2Reply H isElem d sk ct request.2, s)

/-- Phase 2 collision-tracking oracle handler for `cramerShoupToCollisionFinder`: replies with
`cramerShoupCollisionPhase2Reply` and records `some (extractCramerShoupTriple request.2)` whenever
`isCramerShoupCollision H d request.2 ct` holds. -/
def cramerShoupCollisionPhase2Oracle (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (d : F.Desc)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct : List Bool) (request : Unit × List Bool) :
    StateT (Option (List Bool)) ProbComp (List Bool) :=
  finderPhase2Oracle (F.cramerShoupCollisionPhase2Reply H isElem d sk ct)
    (fun req => F.isCramerShoupCollision H d req ct) extractCramerShoupTriple request

private theorem computableTidilyInPolyTime_cramerShoupPhase1Reply
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {req : γ → List Bool}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hsk : ComputableTidilyInPolyTime sk encIn encCramerShoupSK)
    (hreq : ComputableTidilyInPolyTime req encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => F.cramerShoupPhase1Reply H isElem (d a) (sk a) (req a)) encIn encBits :=
  computableTidilyInPolyTime_comp (ComputableTidilyInPolyTime.encode (encOption encBits))
    (F.computableTidilyInPolyTime_decodeCramerShoup hH.tidy hisElem.tidy hd hsk hreq)

private theorem computableTidilyInPolyTime_cramerShoupPhase2Reply
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {ct req : γ → List Bool}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hsk : ComputableTidilyInPolyTime sk encIn encCramerShoupSK)
    (hct : ComputableTidilyInPolyTime ct encIn encBits)
    (hreq : ComputableTidilyInPolyTime req encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => F.cramerShoupPhase2Reply H isElem (d a) (sk a) (ct a) (req a)) encIn encBits := by
  have hbeq : ComputableTidilyInPolyTime (fun q : List Bool × List Bool => q.1 == q.2)
      (encPair encBits encBits) encBool := by polytime
  exact ComputableTidilyInPolyTime.cond
    (computableTidilyInPolyTime_comp hbeq (hreq.prod hct)) (.const [])
    (F.computableTidilyInPolyTime_cramerShoupPhase1Reply hH hisElem hd hsk hreq)

private theorem computableTidilyInPolyTime_cramerShoupCollisionPhase2Reply
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {ct req : γ → List Bool}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hsk : ComputableTidilyInPolyTime sk encIn encCramerShoupSK)
    (hct : ComputableTidilyInPolyTime ct encIn encBits)
    (hreq : ComputableTidilyInPolyTime req encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => F.cramerShoupCollisionPhase2Reply H isElem (d a) (sk a) (ct a) (req a))
      encIn encBits := by
  have hbeq : ComputableTidilyInPolyTime (fun q : List Bool × List Bool => q.1 == q.2)
      (encPair encBits encBits) encBool := by polytime
  have hor : ComputableTidilyInPolyTime (fun q : Bool × Bool => q.1 || q.2)
      (encPair encBool encBool) encBool := by polytime
  exact ComputableTidilyInPolyTime.cond
    (computableTidilyInPolyTime_comp hor
      ((computableTidilyInPolyTime_comp hbeq (hreq.prod hct)).prod
        (F.computableTidilyInPolyTime_isCramerShoupCollision hH hd hreq hct)))
    (.const [])
    (F.computableTidilyInPolyTime_cramerShoupPhase1Reply hH hisElem hd hsk hreq)

private theorem isPPTOn_run_cramerShoupPhase1Oracle
    {Msg : Type} {encMsg : Msg ↪ List Bool}
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {adversary : CCA2AdversaryOf Msg}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hA : adversary.IsPPT encMsg)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {pk : γ → List Bool}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hsk : ComputableTidilyInPolyTime sk encIn encCramerShoupSK)
    (hpk : ComputableTidilyInPolyTime pk encIn encBits) :
    IsPPTOn encIn (encPair (encPair (encPair encMsg encMsg) encBits) (encFinEnum Unit))
      (fun a => (OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
          (F.cramerShoupPhase1Oracle H isElem (d a) (sk a)))
        (adversary.choose (n a) (pk a))).run ()) := by
  have hp1 := ComputableTidilyInPolyTime.fst encIn encBits
  have hp2 := ComputableTidilyInPolyTime.snd encIn encBits
  have hreply := F.computableTidilyInPolyTime_cramerShoupPhase1Reply hH hisElem
    (computableTidilyInPolyTime_comp hd hp1) (computableTidilyInPolyTime_comp hsk hp1) hp2
  have hE1 := ComputableTidilyInPolyTime.fst encIn
    (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hE2 := ComputableTidilyInPolyTime.snd encIn
    (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hreplyIn := F.computableTidilyInPolyTime_cramerShoupPhase1Reply hH hisElem
    (computableTidilyInPolyTime_comp hd hE1) (computableTidilyInPolyTime_comp hsk hE1)
    hE2.fst'.snd'
  exact hA.choose.on.run_interpret_preprocess
    (prepare := fun a : γ => (n a, pk a)) (initial := fun _ => ())
    (resources := fun a req => (F.cramerShoupPhase1Reply H isElem (d a) (sk a) req).length)
    (hn.prod hpk) (hreplyIn.prod hE2.snd').isPPTOn (.const ()) (fun _ _ => True)
    (fun _ => trivial) (computableTidilyInPolyTime_comp .length_bits hreply)
    (fun a request state _ result hresult => by
      have hresEq : result =
          (F.cramerShoupPhase1Reply H isElem (d a) (sk a) request.2, state) := by
        simpa [cramerShoupPhase1Oracle] using hresult
      subst hresEq
      exact ⟨trivial, le_rfl, Nat.le_add_right _ _⟩)

private theorem isPPTOn_run_cramerShoupPhase2Oracle
    {Msg : Type} {encMsg : Msg ↪ List Bool}
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {adversary : CCA2AdversaryOf Msg}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hA : adversary.IsPPT encMsg)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {state ct : γ → List Bool}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hsk : ComputableTidilyInPolyTime sk encIn encCramerShoupSK)
    (hstate : ComputableTidilyInPolyTime state encIn encBits)
    (hct : ComputableTidilyInPolyTime ct encIn encBits) :
    IsPPTOn encIn (encPair encBool (encFinEnum Unit))
      (fun a => (OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
          (F.cramerShoupPhase2Oracle H isElem (d a) (sk a) (ct a)))
        (adversary.guess (n a) (state a) (ct a))).run ()) := by
  have hp1 := ComputableTidilyInPolyTime.fst encIn encBits
  have hp2 := ComputableTidilyInPolyTime.snd encIn encBits
  have hreply := F.computableTidilyInPolyTime_cramerShoupPhase2Reply hH hisElem
    (computableTidilyInPolyTime_comp hd hp1) (computableTidilyInPolyTime_comp hsk hp1)
    (computableTidilyInPolyTime_comp hct hp1) hp2
  have hE1 := ComputableTidilyInPolyTime.fst encIn
    (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hE2 := ComputableTidilyInPolyTime.snd encIn
    (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hreplyIn := F.computableTidilyInPolyTime_cramerShoupPhase2Reply hH hisElem
    (computableTidilyInPolyTime_comp hd hE1) (computableTidilyInPolyTime_comp hsk hE1)
    (computableTidilyInPolyTime_comp hct hE1) hE2.fst'.snd'
  exact hA.guess.run_interpret_preprocess
    (prepare := fun a : γ => (n a, state a, ct a)) (initial := fun _ => ())
    (resources := fun a req => (F.cramerShoupPhase2Reply H isElem (d a) (sk a) (ct a) req).length)
    (hn.prod (hstate.prod hct)) (hreplyIn.prod hE2.snd').isPPTOn (.const ()) (fun _ _ => True)
    (fun _ => trivial) (computableTidilyInPolyTime_comp .length_bits hreply)
    (fun a request st _ result hresult => by
      have hresEq : result =
          (F.cramerShoupPhase2Reply H isElem (d a) (sk a) (ct a) request.2, st) := by
        simpa [cramerShoupPhase2Oracle] using hresult
      subst hresEq
      exact ⟨trivial, le_rfl, Nat.le_add_right _ _⟩)

private theorem isPPTOn_run_cramerShoupCollisionPhase2Oracle
    {Msg : Type} {encMsg : Msg ↪ List Bool}
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {adversary : CCA2AdversaryOf Msg}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hA : adversary.IsPPT encMsg)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {state ct : γ → List Bool}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hsk : ComputableTidilyInPolyTime sk encIn encCramerShoupSK)
    (hstate : ComputableTidilyInPolyTime state encIn encBits)
    (hct : ComputableTidilyInPolyTime ct encIn encBits) :
    IsPPTOn encIn (encPair encBool (encOption encBits))
      (fun a => (OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
          (F.cramerShoupCollisionPhase2Oracle H isElem (d a) (sk a) (ct a)))
        (adversary.guess (n a) (state a) (ct a))).run none) := by
  have hp1 := ComputableTidilyInPolyTime.fst encIn encBits
  have hp2 := ComputableTidilyInPolyTime.snd encIn encBits
  have hreply := F.computableTidilyInPolyTime_cramerShoupCollisionPhase2Reply hH hisElem
    (computableTidilyInPolyTime_comp hd hp1) (computableTidilyInPolyTime_comp hsk hp1)
    (computableTidilyInPolyTime_comp hct hp1) hp2
  have hE1 := ComputableTidilyInPolyTime.fst encIn
    (encPair (encPair (encFinEnum Unit) encBits) (encOption encBits))
  have hE2 := ComputableTidilyInPolyTime.snd encIn
    (encPair (encPair (encFinEnum Unit) encBits) (encOption encBits))
  have hreplyIn := F.computableTidilyInPolyTime_cramerShoupCollisionPhase2Reply hH hisElem
    (computableTidilyInPolyTime_comp hd hE1) (computableTidilyInPolyTime_comp hsk hE1)
    (computableTidilyInPolyTime_comp hct hE1) hE2.fst'.snd'
  have hcollIn := F.computableTidilyInPolyTime_isCramerShoupCollision hH
    (computableTidilyInPolyTime_comp hd hE1) hE2.fst'.snd' (computableTidilyInPolyTime_comp hct hE1)
  have hsome : ComputableTidilyInPolyTime
      (fun x : List Bool => (some x : Option (List Bool))) encBits (encOption encBits) := by
    polytime
  have hnextState := ComputableTidilyInPolyTime.cond hcollIn
    (computableTidilyInPolyTime_comp hsome
      (computableTidilyInPolyTime_comp computableTidilyInPolyTime_extractCramerShoupTriple
        hE2.fst'.snd'))
    hE2.snd'
  have hsomeLen := computableTidilyInPolyTime_comp ComputableTidilyInPolyTime.length_bits
    (computableTidilyInPolyTime_comp (ComputableTidilyInPolyTime.encode (encOption encBits))
      (computableTidilyInPolyTime_comp hsome
        (computableTidilyInPolyTime_comp computableTidilyInPolyTime_extractCramerShoupTriple hp2)))
  have hres := computableTidilyInPolyTime_add_unary
    (computableTidilyInPolyTime_comp ComputableTidilyInPolyTime.length_bits hreply) hsomeLen
  exact hA.guess.run_interpret_preprocess
    (prepare := fun a : γ => (n a, state a, ct a)) (initial := fun _ => none)
    (resources := fun a req =>
      (F.cramerShoupCollisionPhase2Reply H isElem (d a) (sk a) (ct a) req).length +
      (encOption encBits (some (extractCramerShoupTriple req))).length)
    (hn.prod (hstate.prod hct)) (hreplyIn.prod hnextState).isPPTOn
    (.const (none : Option (List Bool))) (fun _ _ => True) (fun _ => trivial) hres
    (fun a request st _ result hresult => by
      have hresEq : result =
          (F.cramerShoupCollisionPhase2Reply H isElem (d a) (sk a) (ct a) request.2,
           if F.isCramerShoupCollision H (d a) request.2 (ct a) then
             some (extractCramerShoupTriple request.2)
           else st) := by
        simpa [cramerShoupCollisionPhase2Oracle, finderPhase2Oracle] using hresult
      subst hresEq; dsimp only
      refine ⟨trivial, Nat.le_add_right _ _, ?_⟩
      split_ifs <;> omega)

/-- The DDH distinguisher constructed from a `CCA2AdversaryOf Msg` with message-to-group-word
encoding `encodeMsg : F.Desc × Msg → List Bool` ([BonehShoup2023], proof of Theorem 12.9,
Game 1 $\to$ Game 2, equation (12.22), printed pp. 490, 492, adapted to
$\mathcal{E}_{\mathrm{MCS}}$). -/
noncomputable def cramerShoupMsgToDDHDistinguisher
    {Msg : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : CCA2AdversaryOf Msg) (bit : Bool)
    (n : ℕ) (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool :=
  F.sampleCramerShoupSK n input.1 >>= fun sk =>
    let pk := F.encodeCramerShoupPublicKey input.1 input.2.1 sk
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
        (F.cramerShoupPhase1Oracle H isElem input.1 sk))
      (adversary.choose n pk)).run ()) >>= fun choiceOut =>
      let choice := choiceOut.1
      let m₀ := encodeMsg (input.1, choice.1.1)
      let m₁ := encodeMsg (input.1, choice.1.2)
      if isElem (input.1, m₀) && isElem (input.1, m₁) then
        let m := if bit then m₁ else m₀
        let ct := F.encodeCramerShoupChallenge H input.1 sk input.2.2.1 input.2.2.2 m
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (F.cramerShoupPhase2Oracle H isElem input.1 sk ct))
          (adversary.guess n choice.2 ct)).run ()) >>= fun guessOut =>
          pure guessOut.1
      else
        pure false

/-- The DDH distinguisher constructed from a group-message 1CCA adversary (`Msg = List Bool`,
`encodeMsg = Prod.snd`). -/
noncomputable abbrev cramerShoupToDDHDistinguisher
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : CCA2AdversaryOf (List Bool)) (bit : Bool)
    (n : ℕ) (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool :=
  F.cramerShoupMsgToDDHDistinguisher Prod.snd H isElem adversary bit n input

/-- `cramerShoupMsgToDDHDistinguisher` is uniform strict PPT whenever `encodeMsg`, `H`, and
`isElem` are computable in polynomial time and `adversary` is a strict oracle PPT 1CCA adversary. -/
theorem isPPTOn_cramerShoupMsgToDDHDistinguisher
    {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encodeMsg : F.Desc × Msg → List Bool}
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {adversary : CCA2AdversaryOf Msg}
    (hencMsg : ComputableInPolyTime encodeMsg (encPair F.encDesc encMsg) encBits)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hA : adversary.IsPPT encMsg) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun p =>
        F.cramerShoupMsgToDDHDistinguisher encodeMsg H isElem adversary bit p.1 p.2) := by
  let E0 := encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))
  let E1 := encPair E0 encCramerShoupSK
  let EChoice := encPair (encPair (encPair encMsg encMsg) encBits) (encFinEnum Unit)
  have hn0 := ComputableTidilyInPolyTime.fst encUnary
    (encPair F.encDesc (encPair encBits (encPair encBits encBits)))
  have hd0 := (ComputableTidilyInPolyTime.snd encUnary
    (encPair F.encDesc (encPair encBits (encPair encBits encBits)))).fst'
  have hsk := F.isPPTOn_sampleCramerShoupSK hn0 hd0
  have hp1_0 := ComputableTidilyInPolyTime.fst E0 encCramerShoupSK
  have hsk1 := ComputableTidilyInPolyTime.snd E0 encCramerShoupSK
  have hpk := F.computableTidilyInPolyTime_encodeCramerShoupPublicKey
    hp1_0.snd'.fst' hp1_0.snd'.snd'.fst' hsk1
  have hphase1 := F.isPPTOn_run_cramerShoupPhase1Oracle hH hisElem hA
    hp1_0.fst' hp1_0.snd'.fst' hsk1 hpk
  have hand : ComputableTidilyInPolyTime (fun q : Bool × Bool => q.1 && q.2)
      (encPair encBool encBool) encBool := by polytime
  have hp2_1 := ComputableTidilyInPolyTime.fst E1 EChoice
  have hp2_2 := ComputableTidilyInPolyTime.snd E1 EChoice
  have hd2 := hp2_1.fst'.snd'.fst'
  have hm₀ := computableTidilyInPolyTime_comp hencMsg.tidy (hd2.prod hp2_2.fst'.fst'.fst')
  have hm₁ := computableTidilyInPolyTime_comp hencMsg.tidy (hd2.prod hp2_2.fst'.fst'.snd')
  have hvalid := computableTidilyInPolyTime_comp hand
    ((computableTidilyInPolyTime_comp hisElem.tidy (hd2.prod hm₀)).prod
      (computableTidilyInPolyTime_comp hisElem.tidy (hd2.prod hm₁)))
  have hm : ComputableTidilyInPolyTime
      (fun p => if bit then encodeMsg (p.1.1.2.1, p.2.1.1.2)
        else encodeMsg (p.1.1.2.1, p.2.1.1.1)) (encPair E1 EChoice) encBits := by
    cases bit
    · exact hm₀
    · exact hm₁
  have hct := F.computableTidilyInPolyTime_encodeCramerShoupChallenge hH.tidy
    hd2 hp2_1.snd' hp2_1.fst'.snd'.snd'.snd'.fst' hp2_1.fst'.snd'.snd'.snd'.snd' hm
  have hphase2 := F.isPPTOn_run_cramerShoupPhase2Oracle hH hisElem hA
    hp2_1.fst'.fst' hd2 hp2_1.snd' hp2_2.fst'.snd' hct
  unfold cramerShoupMsgToDDHDistinguisher
  refine hsk.bind_with (hphase1.bind_with ?_)
  exact IsPPTOn.cond hvalid
    (hphase2.bind_with (ComputableTidilyInPolyTime.isPPTOn (by fun_prop)))
    (ComputableTidilyInPolyTime.isPPTOn (.const false))

/-- `cramerShoupToDDHDistinguisher` is uniform strict PPT whenever `H` and `isElem` are computable
in polynomial time and `adversary` is a strict oracle PPT 1CCA adversary. -/
theorem isPPTOn_cramerShoupToDDHDistinguisher
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {adversary : CCA2AdversaryOf (List Bool)}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hA : adversary.IsPPT encBits) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun p => F.cramerShoupToDDHDistinguisher H isElem adversary bit p.1 p.2) :=
  F.isPPTOn_cramerShoupMsgToDDHDistinguisher (by fun_prop) hH hisElem hA bit

/-- The setup-parameterized collision finder constructed from a `CCA2AdversaryOf Msg` with
message-to-group-word encoding `encodeMsg : F.Desc × Msg → List Bool` ([BonehShoup2023], proof of
Theorem 12.9, Game 4, equations (12.24)–(12.25), printed p. 492, adapted to
$\mathcal{E}_{\mathrm{MCS}}$). -/
noncomputable def cramerShoupMsgToCollisionFinder
    {Msg : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : CCA2AdversaryOf Msg) (bit : Bool) :
    CollisionFinderFor F.Desc :=
  fun n d =>
    F.sampleCramerShoupTripleExponents n d >>= fun abc =>
      F.sampleCramerShoupSK n d >>= fun sk =>
        let gen := F.encode d (F.generator d)
        let u := F.smul (d, abc.1, gen)
        let v := F.smul (d, abc.2.1, gen)
        let w := F.smul (d, abc.2.2, gen)
        let pk := F.encodeCramerShoupPublicKey d u sk
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (F.cramerShoupPhase1Oracle H isElem d sk))
          (adversary.choose n pk)).run ()) >>= fun choiceOut =>
          let choice := choiceOut.1
          let m₀ := encodeMsg (d, choice.1.1)
          let m₁ := encodeMsg (d, choice.1.2)
          if isElem (d, m₀) && isElem (d, m₁) then
            let m := if bit then m₁ else m₀
            let ct := F.encodeCramerShoupChallenge H d sk v w m
            ((OracleComp.interpret
              (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
                (F.cramerShoupCollisionPhase2Oracle H isElem d sk ct))
              (adversary.guess n choice.2 ct)).run none) >>= fun out =>
              let target := extractCramerShoupTriple ct
              pure (out.2.getD target, target)
          else
            pure ([], [])

/-- The setup-parameterized collision finder constructed from a group-message 1CCA adversary
(`Msg = List Bool`, `encodeMsg = Prod.snd`). -/
noncomputable abbrev cramerShoupToCollisionFinder
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : CCA2AdversaryOf (List Bool)) (bit : Bool) :
    CollisionFinderFor F.Desc :=
  F.cramerShoupMsgToCollisionFinder Prod.snd H isElem adversary bit

/-- `cramerShoupMsgToCollisionFinder` is uniform strict PPT whenever `encodeMsg`, `H`, and
`isElem` are computable in polynomial time and `adversary` is a strict oracle PPT 1CCA adversary. -/
theorem isPPTOn_cramerShoupMsgToCollisionFinder
    {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encodeMsg : F.Desc × Msg → List Bool}
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {adversary : CCA2AdversaryOf Msg}
    (hencMsg : ComputableInPolyTime encodeMsg (encPair F.encDesc encMsg) encBits)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hA : adversary.IsPPT encMsg) (bit : Bool) :
    IsPPTOn (encPair encUnary F.encDesc) (encPair encBits encBits)
      (fun p =>
        F.cramerShoupMsgToCollisionFinder encodeMsg H isElem adversary bit p.1 p.2) := by
  let E0 := encPair encUnary F.encDesc
  let EExp := encPair encNat (encPair encNat encNat)
  let E1 := encPair E0 EExp
  let E2 := encPair E1 encCramerShoupSK
  let EChoice := encPair (encPair (encPair encMsg encMsg) encBits) (encFinEnum Unit)
  let E3 := encPair E2 EChoice
  have habc := F.isPPTOn_sampleCramerShoupTripleExponents
    (ComputableTidilyInPolyTime.fst encUnary F.encDesc)
    (ComputableTidilyInPolyTime.snd encUnary F.encDesc)
  have hp1_0 := ComputableTidilyInPolyTime.fst E0 EExp
  have hsk := F.isPPTOn_sampleCramerShoupSK hp1_0.fst' hp1_0.snd'
  have hsmul := F.computableInPolyTime_smul.tidy
  have hp2_1 := ComputableTidilyInPolyTime.fst E1 encCramerShoupSK
  have hsk2 := ComputableTidilyInPolyTime.snd E1 encCramerShoupSK
  have hd2 := hp2_1.fst'.snd'
  have hgen2 := computableTidilyInPolyTime_comp F.computableInPolyTime_generator.tidy hd2
  have hu := computableTidilyInPolyTime_comp hsmul (hd2.prod (hp2_1.snd'.fst'.prod hgen2))
  have hpk := F.computableTidilyInPolyTime_encodeCramerShoupPublicKey hd2 hu hsk2
  have hphase1 := F.isPPTOn_run_cramerShoupPhase1Oracle hH hisElem hA
    hp2_1.fst'.fst' hd2 hsk2 hpk
  have hand : ComputableTidilyInPolyTime (fun q : Bool × Bool => q.1 && q.2)
      (encPair encBool encBool) encBool := by polytime
  have hp3_1 := ComputableTidilyInPolyTime.fst E2 EChoice
  have hp3_2 := ComputableTidilyInPolyTime.snd E2 EChoice
  have hd3 := hp3_1.fst'.fst'.snd'
  have hm₀ := computableTidilyInPolyTime_comp hencMsg.tidy (hd3.prod hp3_2.fst'.fst'.fst')
  have hm₁ := computableTidilyInPolyTime_comp hencMsg.tidy (hd3.prod hp3_2.fst'.fst'.snd')
  have hvalid := computableTidilyInPolyTime_comp hand
    ((computableTidilyInPolyTime_comp hisElem.tidy (hd3.prod hm₀)).prod
      (computableTidilyInPolyTime_comp hisElem.tidy (hd3.prod hm₁)))
  have hgen3 := computableTidilyInPolyTime_comp F.computableInPolyTime_generator.tidy hd3
  have hv := computableTidilyInPolyTime_comp hsmul
    (hd3.prod (hp3_1.fst'.snd'.snd'.fst'.prod hgen3))
  have hw := computableTidilyInPolyTime_comp hsmul
    (hd3.prod (hp3_1.fst'.snd'.snd'.snd'.prod hgen3))
  have hm : ComputableTidilyInPolyTime
      (fun p => if bit then encodeMsg (p.1.1.1.2, p.2.1.1.2)
        else encodeMsg (p.1.1.1.2, p.2.1.1.1)) E3 encBits := by
    cases bit
    · exact hm₀
    · exact hm₁
  have hct := F.computableTidilyInPolyTime_encodeCramerShoupChallenge hH.tidy
    hd3 hp3_1.snd' hv hw hm
  have hphase2c := F.isPPTOn_run_cramerShoupCollisionPhase2Oracle hH hisElem hA
    hp3_1.fst'.fst'.fst' hd3 hp3_1.snd' hp3_2.fst'.snd' hct
  have hp4_1 := ComputableTidilyInPolyTime.fst E3 (encPair encBool (encOption encBits))
  have hp4_2 := ComputableTidilyInPolyTime.snd E3 (encPair encBool (encOption encBits))
  have htarget :=
    computableTidilyInPolyTime_comp computableTidilyInPolyTime_extractCramerShoupTriple
      (computableTidilyInPolyTime_comp hct hp4_1)
  have houtPair := (ComputableTidilyInPolyTime.optionGetDWithInput hp4_2.snd' htarget).prod htarget
  unfold cramerShoupMsgToCollisionFinder
  refine habc.bind_with (hsk.bind_with (hphase1.bind_with ?_))
  exact IsPPTOn.cond hvalid
    (hphase2c.bind_with houtPair.isPPTOn)
    (ComputableTidilyInPolyTime.isPPTOn (.const (([] : List Bool), [])))

/-- `cramerShoupToCollisionFinder` is uniform strict PPT whenever `H` and `isElem` are computable
in polynomial time and `adversary` is a strict oracle PPT 1CCA adversary. -/
theorem isPPTOn_cramerShoupToCollisionFinder
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {adversary : CCA2AdversaryOf (List Bool)}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hA : adversary.IsPPT encBits) (bit : Bool) :
    IsPPTOn (encPair encUnary F.encDesc) (encPair encBits encBits)
      (fun p => F.cramerShoupToCollisionFinder H isElem adversary bit p.1 p.2) :=
  F.isPPTOn_cramerShoupMsgToCollisionFinder (by fun_prop) hH hisElem hA bit

/-- `encodeCramerShoupPublicKey` depends on `sk` only through its residues modulo `F.order d`. -/
theorem encodeCramerShoupPublicKey_eq_skNatOfZMod (d : F.Desc)
    (α : ZMod (F.order d)) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d)) sk =
      F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d))
        (F.skNatOfZMod d (sk.1.1 : ZMod (F.order d)) (sk.1.2 : ZMod (F.order d))
          (sk.2.1.1 : ZMod (F.order d)) (sk.2.1.2 : ZMod (F.order d))
          (sk.2.2.1 : ZMod (F.order d)) (sk.2.2.2 : ZMod (F.order d))) := by
  simp only [encodeCramerShoupPublicKey_encode, skNatOfZMod, ZMod.natCast_zmod_val]

/-- `encodeCramerShoupChallenge` depends on `sk` only through its residues modulo `F.order d`. -/
theorem encodeCramerShoupChallenge_eq_skNatOfZMod
    (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (v w : F.Carrier d) (m : List Bool) :
    F.encodeCramerShoupChallenge H d sk (F.encode d v) (F.encode d w) m =
      F.encodeCramerShoupChallenge H d
        (F.skNatOfZMod d (sk.1.1 : ZMod (F.order d)) (sk.1.2 : ZMod (F.order d))
          (sk.2.1.1 : ZMod (F.order d)) (sk.2.1.2 : ZMod (F.order d))
          (sk.2.2.1 : ZMod (F.order d)) (sk.2.2.2 : ZMod (F.order d)))
        (F.encode d v) (F.encode d w) m := by
  simp only [encodeCramerShoupChallenge, skNatOfZMod, encodeProjHash_encode,
    encodeProjHash2_encode, ZMod.natCast_zmod_val]

/-- `decodeCramerShoup` depends on `sk` only through its residues modulo `F.order d`. -/
theorem decodeCramerShoup_eq_skNatOfZMod
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct : List Bool) :
    F.decodeCramerShoup H isElem d sk ct =
      F.decodeCramerShoup H isElem d
        (F.skNatOfZMod d (sk.1.1 : ZMod (F.order d)) (sk.1.2 : ZMod (F.order d))
          (sk.2.1.1 : ZMod (F.order d)) (sk.2.1.2 : ZMod (F.order d))
          (sk.2.2.1 : ZMod (F.order d)) (sk.2.2.2 : ZMod (F.order d))) ct := by
  unfold decodeCramerShoup
  by_cases hvw :
      isElem (d, (decodeBits4 ct).1) = true ∧ isElem (d, (decodeBits4 ct).2.1) = true
  · obtain ⟨v, hv⟩ := (hmem d _).mp hvw.1
    obtain ⟨w, hw⟩ := (hmem d _).mp hvw.2
    simp only [← hv, ← hw, skNatOfZMod, encodeProjHash2_encode, encodeProjHash_encode,
      ZMod.natCast_zmod_val]
  · have hfalse : ((encBits4 (decodeBits4 ct) == ct) && isElem (d, (decodeBits4 ct).1) &&
        isElem (d, (decodeBits4 ct).2.1) && isElem (d, (decodeBits4 ct).2.2.1)) = false := by
      revert hvw
      cases isElem (d, (decodeBits4 ct).1) <;> cases isElem (d, (decodeBits4 ct).2.1) <;> simp
    simp [hfalse]

/-- `cramerShoupPhase1Oracle` depends on `sk` only through its residues modulo `F.order d`. -/
theorem cramerShoupPhase1Oracle_eq_skNatOfZMod
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    F.cramerShoupPhase1Oracle H isElem d sk =
      F.cramerShoupPhase1Oracle H isElem d
        (F.skNatOfZMod d (sk.1.1 : ZMod (F.order d)) (sk.1.2 : ZMod (F.order d))
          (sk.2.1.1 : ZMod (F.order d)) (sk.2.1.2 : ZMod (F.order d))
          (sk.2.2.1 : ZMod (F.order d)) (sk.2.2.2 : ZMod (F.order d))) := by
  funext req s
  simp only [cramerShoupPhase1Oracle, cramerShoupPhase1Reply,
    F.decodeCramerShoup_eq_skNatOfZMod H isElem hmem d sk req.2]

/-- `cramerShoupPhase2Oracle` depends on `sk` only through its residues modulo `F.order d`. -/
theorem cramerShoupPhase2Oracle_eq_skNatOfZMod
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct : List Bool) :
    F.cramerShoupPhase2Oracle H isElem d sk ct =
      F.cramerShoupPhase2Oracle H isElem d
        (F.skNatOfZMod d (sk.1.1 : ZMod (F.order d)) (sk.1.2 : ZMod (F.order d))
          (sk.2.1.1 : ZMod (F.order d)) (sk.2.1.2 : ZMod (F.order d))
          (sk.2.2.1 : ZMod (F.order d)) (sk.2.2.2 : ZMod (F.order d))) ct := by
  funext req s
  simp only [cramerShoupPhase2Oracle, cramerShoupPhase2Reply,
    F.decodeCramerShoup_eq_skNatOfZMod H isElem hmem d sk req.2]

/-- `cramerShoupCollisionPhase2Oracle` depends on `sk` only through its residues modulo
`F.order d`. -/
theorem cramerShoupCollisionPhase2Oracle_eq_skNatOfZMod
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct : List Bool) :
    F.cramerShoupCollisionPhase2Oracle H isElem d sk ct =
      F.cramerShoupCollisionPhase2Oracle H isElem d
        (F.skNatOfZMod d (sk.1.1 : ZMod (F.order d)) (sk.1.2 : ZMod (F.order d))
          (sk.2.1.1 : ZMod (F.order d)) (sk.2.1.2 : ZMod (F.order d))
          (sk.2.2.1 : ZMod (F.order d)) (sk.2.2.2 : ZMod (F.order d))) ct := by
  funext req s
  simp only [cramerShoupCollisionPhase2Oracle, finderPhase2Oracle, cramerShoupCollisionPhase2Reply,
    F.decodeCramerShoup_eq_skNatOfZMod H isElem hmem d sk req.2]

/-- Word-level public-key encryption under `cramerShoupPublicKey d α σ τ σ₁ τ₁ σ₂ τ₂` coincides with
`encodeCramerShoupChallenge` on `(v, w) = (β • g, (α * β) • g)` ([BonehShoup2023], Section 12.5.3,
Game 0 $\to$ Game 1, equation (12.21), printed p. 490). -/
@[simp]
theorem encodeCramerShoupEncrypt_publicKey_eq_challenge
    (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (α β σ τ σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d)) (m : List Bool) :
    let pkVal := F.cramerShoupPublicKey d α σ τ σ₁ τ₁ σ₂ τ₂
    F.encodeCramerShoupEncrypt H d
      (F.encode d pkVal.1, F.encode d pkVal.2.1, F.encode d pkVal.2.2.1, F.encode d pkVal.2.2.2)
      m β.val =
      F.encodeCramerShoupChallenge H d (F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂)
        (F.encode d (β • F.generator d)) (F.encode d ((α * β) • F.generator d)) m := by
  have hαβ : (α * β) • F.generator d = β • (α • F.generator d) := by rw [smul_smul, mul_comm]
  rw [hαβ]
  simp only [encodeCramerShoupEncrypt, encodeCramerShoupChallenge, cramerShoupPublicKey,
    projHash2Aux, skNatOfZMod, F.smul_encode, F.add_encode, ZMod.natCast_zmod_val,
    encodeProjHash_encode, encodeProjHash2_encode, projHash_smul_generator,
    projHash2_smul_generator]

/-! ### `Encryption.cca2GameOn` and `Encryption.INDCCA2On` instantiation -/

/-- Unpack a canonically framed 6-tuple secret key `((s, t), ((s₁, t₁), (s₂, t₂)))` of natural
numbers. -/
def decodeCramerShoupSK (w : List Bool) : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) :=
  let p1 := unframe w
  let p2 := dropFrame w
  let p21 := unframe p2
  let p22 := dropFrame p2
  ((ofBits (unframe p1), ofBits (dropFrame p1)),
    ((ofBits (unframe p21), ofBits (dropFrame p21)),
      (ofBits (unframe p22), ofBits (dropFrame p22))))

/-- `decodeCramerShoupSK` left-inverts `encCramerShoupSK`. -/
theorem decodeCramerShoupSK_encCramerShoupSK (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    decodeCramerShoupSK (encCramerShoupSK sk) = sk := by
  rcases sk with ⟨⟨s, t⟩, ⟨⟨s₁, t₁⟩, ⟨s₂, t₂⟩⟩⟩
  have hbits (n : ℕ) : ofBits n.bits = n := Nat.foldr_bit_bits n
  simp [encCramerShoupSK, decodeCramerShoupSK, encPair_apply, encNat_apply, hbits,
    unframe_frame_append, dropFrame_frame_append]

private theorem computableTidilyInPolyTime_decodeCramerShoupSK :
    ComputableTidilyInPolyTime decodeCramerShoupSK encBits encCramerShoupSK := by
  have hpair : ComputableTidilyInPolyTime
      (fun w : List Bool => (ofBits (unframe w), ofBits (dropFrame w)))
      encBits (encPair encNat encNat) := by fun_prop
  have hp1 : ComputableTidilyInPolyTime (fun w : List Bool => unframe w) encBits encBits := by
    fun_prop
  have hp2 : ComputableTidilyInPolyTime (fun w : List Bool => dropFrame w) encBits encBits := by
    fun_prop
  exact (hpair.comp hp1).prod
    ((hpair.comp (hp1.comp hp2)).prod (hpair.comp (hp2.comp hp2)))

/-- Challenge-pair group-membership admissibility predicate for `Encryption.cca2GameOn`
([BonehShoup2023], Section 12.5.3 & Exercise 12.27): both challenge words `m₀` and `m₁` must
belong to the group `F.Carrier (d n)`. -/
def cramerShoupValid (isElem : F.Desc × List Bool → Bool) (d : ℕ → F.Desc)
    (n : ℕ) (_pk m₀ m₁ : List Bool) : Bool :=
  isElem (d n, m₀) && isElem (d n, m₁)

/-- Probabilistic polynomial-time Cramer–Shoup key generation for a group family `d : ℕ → F.Desc`,
sampling approximate uniform exponents via `sampleModNat`. -/
noncomputable def cramerShoupKeyGenProb (d : ℕ → F.Desc) (n : ℕ) :
    ProbComp (List Bool × List Bool) :=
  F.sampleExp n (d n) >>= fun a =>
    F.sampleCramerShoupSK n (d n) >>= fun sk =>
      let u := F.smul (d n, a, F.encode (d n) (F.generator (d n)))
      pure (F.encodeCramerShoupPublicKey (d n) u sk, encCramerShoupSK sk)

/-- Probabilistic polynomial-time Cramer–Shoup encryption for a group family `d : ℕ → F.Desc`,
sampling the encryption exponent via `sampleModNat`. -/
noncomputable def cramerShoupEncryptProb
    (H : F.Desc × List Bool → List Bool) (d : ℕ → F.Desc)
    (n : ℕ) (pk m : List Bool) : ProbComp (List Bool) :=
  F.sampleExp n (d n) >>= fun b =>
    pure (F.encodeCramerShoupEncrypt H (d n) (decodeBits4 (dropFrame pk)) m b)

/-- Deterministic polynomial-time Cramer–Shoup decryption for `Encryption.cca2GameOn`. -/
def cramerShoupDecryptOpt
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (d : ℕ → F.Desc) (n : ℕ) (skBits ct : List Bool) : Option (List Bool) :=
  F.decodeCramerShoup H isElem (d n) (decodeCramerShoupSK skBits) ct

/-- `cramerShoupValid` is computable in polynomial time whenever `isElem` and `d` are. -/
theorem computableInPolyTime_cramerShoupValid
    {isElem : F.Desc × List Bool → Bool} {d : ℕ → F.Desc}
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool =>
        F.cramerShoupValid isElem d p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encBits encBits))) encBool := by
  let EIn := encPair encUnary (encPair encBits (encPair encBits encBits))
  have hd_in : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool => d p.1) EIn F.encDesc :=
    hd.tidy.comp (by fun_prop)
  have hand : ComputableTidilyInPolyTime
      (fun q : Bool × Bool => q.1 && q.2) (encPair encBool encBool) encBool := by polytime
  exact .of_tidy (hand.comp
    ((hisElem.tidy.comp (hd_in.prod (by fun_prop))).prod
      (hisElem.tidy.comp (hd_in.prod (by fun_prop)))))

/-- `cramerShoupKeyGenProb` is uniformly strict PPT whenever `d` is computable in polynomial
time. -/
theorem isPPTOn_cramerShoupKeyGenProb {d : ℕ → F.Desc}
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    IsPPTOn encUnary (encPair encBits encBits) (F.cramerShoupKeyGenProb d) := by
  let E1 := encPair encUnary encNat
  let E2 := encPair E1 encCramerShoupSK
  have hd2 : ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) => d p.1.1) E2 F.encDesc :=
    hd.tidy.comp (by fun_prop)
  have ha2 : ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) => p.1.2) E2 encNat := by fun_prop
  have hu : ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) =>
        F.smul (d p.1.1, p.1.2, F.encode (d p.1.1) (F.generator (d p.1.1)))) E2 encBits :=
    F.computableInPolyTime_smul.tidy.comp
      (hd2.prod (ha2.prod (F.computableInPolyTime_generator.tidy.comp hd2)))
  have hpk : ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) =>
        F.encodeCramerShoupPublicKey (d p.1.1)
          (F.smul (d p.1.1, p.1.2, F.encode (d p.1.1) (F.generator (d p.1.1)))) p.2)
      E2 encBits :=
    F.computableTidilyInPolyTime_encodeCramerShoupPublicKey hd2 hu (by fun_prop)
  have hskBits : ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) => encCramerShoupSK p.2) E2 encBits :=
    (ComputableTidilyInPolyTime.encode encCramerShoupSK).comp (by fun_prop)
  unfold cramerShoupKeyGenProb
  exact (F.isPPTOn_sampleExp (by fun_prop) hd).bind_with
    ((F.isPPTOn_sampleCramerShoupSK (by fun_prop) (hd.tidy.comp (by fun_prop))).bind_with
      (hpk.prod hskBits).isPPTOn)

/-- `cramerShoupEncryptProb` is uniformly strict PPT whenever `H` and `d` are computable in
polynomial time. -/
theorem isPPTOn_cramerShoupEncryptProb
    {H : F.Desc × List Bool → List Bool} {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun p => F.cramerShoupEncryptProb H d p.1 p.2.1 p.2.2) := by
  let E0 := encPair encUnary (encPair encBits encBits)
  let E1 := encPair E0 encNat
  have hct : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × ℕ =>
        F.encodeCramerShoupEncrypt H (d p.1.1) (decodeBits4 (dropFrame p.1.2.1)) p.1.2.2 p.2)
      E1 encBits :=
    F.computableTidilyInPolyTime_encodeCramerShoupEncrypt hH.tidy (hd.tidy.comp (by fun_prop))
      (computableTidilyInPolyTime_decodeBits4.comp (by fun_prop)) (by fun_prop) (by fun_prop)
  unfold cramerShoupEncryptProb
  exact (F.isPPTOn_sampleExp (by fun_prop)
    (hd.comp (by fun_prop))).bind_with hct.isPPTOn

/-- `cramerShoupDecryptOpt` is computable in polynomial time whenever `H`, `isElem`, and `d`
are. -/
theorem computableInPolyTime_cramerShoupDecryptOpt
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => F.cramerShoupDecryptOpt H isElem d p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) (encOption encBits) := by
  exact .of_tidy (F.computableTidilyInPolyTime_decodeCramerShoup hH.tidy hisElem.tidy
    (hd.tidy.comp (by fun_prop))
    (computableTidilyInPolyTime_decodeCramerShoupSK.comp (by fun_prop)) (by fun_prop))

/-- `cca2Phase1Oracle` for `cramerShoupDecryptOpt` agrees with `cramerShoupPhase1Oracle`. -/
theorem cca2Phase1Oracle_cramerShoupDecryptOpt
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (d : ℕ → F.Desc) (n : ℕ) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    cca2Phase1Oracle encBits (F.cramerShoupDecryptOpt H isElem d) n (encCramerShoupSK sk) =
      F.cramerShoupPhase1Oracle H isElem (d n) sk := by
  funext req s
  simp only [cca2Phase1Oracle, cramerShoupDecryptOpt, decodeCramerShoupSK_encCramerShoupSK,
    cramerShoupPhase1Oracle, cramerShoupPhase1Reply]

/-- `cca2Phase2Oracle` for `cramerShoupDecryptOpt` agrees with `cramerShoupPhase2Oracle`. -/
theorem cca2Phase2Oracle_cramerShoupDecryptOpt
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (d : ℕ → F.Desc) (n : ℕ) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct : List Bool) :
    cca2Phase2Oracle encBits (F.cramerShoupDecryptOpt H isElem d) n (encCramerShoupSK sk) ct =
      F.cramerShoupPhase2Oracle H isElem (d n) sk ct := by
  funext req s
  simp only [cca2Phase2Oracle, cramerShoupDecryptOpt, decodeCramerShoupSK_encCramerShoupSK,
    cramerShoupPhase2Oracle, cramerShoupPhase2Reply]
  split_ifs <;> rfl

/-- Extracting the 4-tuple of public-key group words from `encodeCramerShoupPublicKey`. -/
@[simp]
theorem decodeBits4_dropFrame_encodeCramerShoupPublicKey
    (d : F.Desc) (u : List Bool) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    decodeBits4 (dropFrame (F.encodeCramerShoupPublicKey d u sk)) =
      (u, F.encodeProjHashAux d sk.1.1 sk.1.2 u,
        F.encodeProjHashAux d sk.2.1.1 sk.2.1.2 u,
        F.encodeProjHashAux d sk.2.2.1 sk.2.2.2 u) := by
  simp [encodeCramerShoupPublicKey, encPair_apply, dropFrame_frame_append]

/-- `encodeCramerShoupEncrypt` on the public-key words generated by `skNatOfZMod` agrees with
`cramerShoupPublicKey`. -/
theorem encodeCramerShoupEncrypt_skNatOfZMod
    (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (α σ τ σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d)) (m : List Bool) (b : ℕ) :
    let u := F.encode d (α • F.generator d)
    let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
    let pkVal := F.cramerShoupPublicKey d α σ τ σ₁ τ₁ σ₂ τ₂
    F.encodeCramerShoupEncrypt H d
      (u, F.encodeProjHashAux d sk.1.1 sk.1.2 u,
        F.encodeProjHashAux d sk.2.1.1 sk.2.1.2 u,
        F.encodeProjHashAux d sk.2.2.1 sk.2.2.2 u) m b =
      F.encodeCramerShoupEncrypt H d
        (F.encode d pkVal.1, F.encode d pkVal.2.1,
          F.encode d pkVal.2.2.1, F.encode d pkVal.2.2.2)
        m (b : ZMod (F.order d)).val := by
  simp only [skNatOfZMod, encodeProjHashAux_encode, ZMod.natCast_zmod_val,
    cramerShoupPublicKey, projHash2Aux, encodeCramerShoupEncrypt, F.smul_encode, F.add_encode]


end Cslib.Crypto.PrimeOrderGroupFamily
