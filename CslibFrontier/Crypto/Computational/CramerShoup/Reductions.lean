/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CramerShoup.Scheme
public import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Crypto.Game.Statistical
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# Certified PPT Reductions and Probabilistic Operations for Cramer–Shoup

This module constructs the uniform strict-PPT (`IsPPTOn`) operations and security reductions for the
**Multiplicative Cramer–Shoup public-key encryption scheme** ($\mathcal{E}_{\mathrm{MCS}}$,
[Boneh and Shoup, Exercise 12.27, printed pp. 521–522][BonehShoup2023], with associated data
$\mathcal{D}$ as in Section 12.7, Definition 12.7, printed pp. 501–502) over a
`PrimeOrderGroupFamily`, following the Games 0–4 reduction structure of [Boneh and Shoup,
Section 12.5.3, Theorem 12.9, printed pp. 488–493][BonehShoup2023]:

1. **Approximate exponent sampling via `sampleModNat`**: `sampleExp`,
   `sampleCramerShoupPair`, `sampleCramerShoupTripleExponents`, and `sampleCramerShoupSK`, together
   with their `IsPPTOn` certificates and `Game.advantage` bounds (`1 / 2 ^ n` per exponent draw)
   relative to exact uniform sampling on `ZMod (F.order d)`.
2. **Phase 1/2 and collision-tracking decryption oracle handlers**: `cramerShoupPhase1Oracle`,
   `cramerShoupPhase2Reply`, `cramerShoupPhase2Oracle`, and `cramerShoupCollisionPhase2Oracle`.
3. **Certified strict-PPT DDH distinguishers (`Game 1 → Game 2`, eq. (12.22), printed p. 492)**:
   `cramerShoupMsgToDDHDistinguisher`, `cramerShoupADToDDHDistinguisher`, and
   `cramerShoupToDDHDistinguisher`, with `DDHDistinguisher.IsPPT` certificates
   `isPPT_cramerShoupMsgToDDHDistinguisher`, `isPPT_cramerShoupADToDDHDistinguisher`, and
   `isPPT_cramerShoupToDDHDistinguisher`.
4. **Certified strict-PPT CRHF collision finders (`Game 3 → Game 4`, eqs. (12.24)–(12.25), printed
   p. 492)**: `cramerShoupMsgToCollisionFinder`, `cramerShoupADToCollisionFinder`, and
   `cramerShoupToCollisionFinder`, with `IsPPTOn` certificates
   `isPPTOn_cramerShoupMsgToCollisionFinder`, `isPPTOn_cramerShoupADToCollisionFinder`, and
   `isPPTOn_cramerShoupToCollisionFinder`.
5. **Certified strict-PPT `Encryption.cca2ADGameOn` and `Encryption.cca2GameOn` operations**:
   `cramerShoupValid`, `cramerShoupKeyGenProb`, `cramerShoupADEncryptProb`,
   `cramerShoupEncryptProb`, `cramerShoupADDecryptOpt`, and `cramerShoupDecryptOpt`, together with
   their `ComputableInPolyTime` and `IsPPTOn` certificates.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM ProjectiveHash Encryption Game
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

private theorem computableInPolyTime_decodeCramerShoup_comp
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {ct ad : γ → List Bool}
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hsk : ComputableInPolyTime sk encIn encCramerShoupSK)
    (hct : ComputableInPolyTime ct encIn encBits)
    (had : ComputableInPolyTime ad encIn encBits) :
    ComputableInPolyTime
      (fun a => F.decodeCramerShoup H isElem (d a) (sk a) (ct a) (ad a))
      encIn (encOption encBits) := by
  change ComputableInPolyTime
    ((fun p : F.Desc × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) × List Bool × List Bool =>
      F.decodeCramerShoup H isElem p.1 p.2.1 p.2.2.1 p.2.2.2) ∘
      fun a => (d a, sk a, ct a, ad a)) encIn (encOption encBits)
  exact (F.computableInPolyTime_decodeCramerShoup hH hisElem).comp
    (hd.prod (hsk.prod (hct.prod had)))

/-! ### Approximate exponent sampling via `sampleModNat` -/

/-- Sample a pair of approximate exponents modulo `F.order d`. -/
noncomputable def sampleCramerShoupPair (n : ℕ) (d : F.Desc) : ProbComp (ℕ × ℕ) := do
  let s ← F.sampleExp n d
  let t ← F.sampleExp n d
  return (s, t)

/-- Sample a 3-tuple of approximate exponents `(a, b, c)` modulo `F.order d`. -/
noncomputable def sampleCramerShoupTripleExponents (n : ℕ) (d : F.Desc) :
    ProbComp (ℕ × ℕ × ℕ) := do
  let a ← F.sampleExp n d
  let bc ← F.sampleCramerShoupPair n d
  return (a, bc)

/-- Sample a 6-tuple secret key `((s, t), ((s₁, t₁), (s₂, t₂)))` of approximate exponents modulo
`F.order d`. -/
noncomputable def sampleCramerShoupSK (n : ℕ) (d : F.Desc) :
    ProbComp ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) := do
  let p ← F.sampleCramerShoupPair n d
  let p₁ ← F.sampleCramerShoupPair n d
  let p₂ ← F.sampleCramerShoupPair n d
  return (p, (p₁, p₂))

private theorem isPPTOn_sampleCramerShoupPair {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hd : ComputableInPolyTime d encIn F.encDesc) :
    IsPPTOn encIn (encPair encNat encNat) (fun a => F.sampleCramerShoupPair (n a) (d a)) := by
  have hfst := ComputableInPolyTime.fst encIn encNat
  have hp := ComputableInPolyTime.id' (encIn := encPair (encPair encIn encNat) encNat)
  exact (F.isPPTOn_sampleExp hn hd).bind_with
    ((F.isPPTOn_sampleExp (hn.comp hfst) (hd.comp hfst)).bind_with
      (hp.fst'.snd'.prod hp.snd').isPPTOn)

private theorem isPPTOn_sampleCramerShoupTripleExponents {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hd : ComputableInPolyTime d encIn F.encDesc) :
    IsPPTOn encIn (encPair encNat (encPair encNat encNat))
      (fun a => F.sampleCramerShoupTripleExponents (n a) (d a)) := by
  have hfst := ComputableInPolyTime.fst encIn encNat
  have hp := ComputableInPolyTime.id'
    (encIn := encPair (encPair encIn encNat) (encPair encNat encNat))
  exact (F.isPPTOn_sampleExp hn hd).bind_with
    ((F.isPPTOn_sampleCramerShoupPair (hn.comp hfst) (hd.comp hfst)).bind_with
      (hp.fst'.snd'.prod hp.snd').isPPTOn)

private theorem isPPTOn_sampleCramerShoupSK {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hd : ComputableInPolyTime d encIn F.encDesc) :
    IsPPTOn encIn encCramerShoupSK (fun a => F.sampleCramerShoupSK (n a) (d a)) := by
  let EP := encPair encNat encNat
  have hfst1 := ComputableInPolyTime.fst encIn EP
  have hfst2 := hfst1.comp (ComputableInPolyTime.fst (encPair encIn EP) EP)
  have hp := ComputableInPolyTime.id' (encIn := encPair (encPair (encPair encIn EP) EP) EP)
  exact (F.isPPTOn_sampleCramerShoupPair hn hd).bind_with
    ((F.isPPTOn_sampleCramerShoupPair (hn.comp hfst1) (hd.comp hfst1)).bind_with
      ((F.isPPTOn_sampleCramerShoupPair (hn.comp hfst2) (hd.comp hfst2)).bind_with
        (hp.fst'.fst'.snd'.prod (hp.fst'.snd'.prod hp.snd')).isPPTOn))

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
  exact F.advantage_bind_sampleExp_pair_le n d k

/-- Replacing `sampleCramerShoupTripleExponents n d` by three independent uniform draws on
`ZMod (F.order d)` changes `Game.advantage` by at most `3 / 2 ^ n`. -/
theorem advantage_bind_sampleCramerShoupTripleExponents_le (n : ℕ) (d : F.Desc)
    (k : ZMod (F.order d) → ZMod (F.order d) → ZMod (F.order d) → Game) :
    Game.advantage
      ((ProbComp.eval (F.sampleCramerShoupTripleExponents n d)).bind fun p =>
        let bc := p.2
        k (p.1 : ZMod (F.order d)) (bc.1 : ZMod (F.order d)) (bc.2 : ZMod (F.order d)))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ => k α β γ) ≤
      3 / 2 ^ n := by
  have hbind :
      ((ProbComp.eval (F.sampleCramerShoupTripleExponents n d)).bind fun p =>
        k (csExpA p : ZMod (F.order d)) (csExpB p : ZMod (F.order d))
          (csExpC p : ZMod (F.order d))) =
      (ProbComp.eval (F.sampleExp n d)).bind fun a =>
        (ProbComp.eval (F.sampleCramerShoupPair n d)).bind fun bc =>
          k (a : ZMod (F.order d)) (bc.1 : ZMod (F.order d)) (bc.2 : ZMod (F.order d)) := by
    simp only [sampleCramerShoupTripleExponents, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_bind, PMF.pure_bind, csExpA, csExpBC, csExpB, csExpC]
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
  exact ((Game.advantage_triangle _ _ _).trans
    (add_le_add hstep1 ((Game.advantage_triangle _ _ _).trans (add_le_add hstep2 hstep3)))).trans_eq
    (by ring)


private theorem computableInPolyTime_isCramerShoupCollision
    {H : F.Desc × List Bool → List Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc} {ct_q ad_q ct ad : γ → List Bool}
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hct_q : ComputableInPolyTime ct_q encIn encBits)
    (had_q : ComputableInPolyTime ad_q encIn encBits)
    (hct : ComputableInPolyTime ct encIn encBits)
    (had : ComputableInPolyTime ad encIn encBits) :
    ComputableInPolyTime
      (fun a => F.isCramerShoupCollision H (d a) (ct_q a) (ad_q a) (ct a) (ad a))
      encIn encBool := by
  have hx := computableInPolyTime_extractCramerShoupTuple.comp (hct_q.prod had_q)
  have hy := computableInPolyTime_extractCramerShoupTuple.comp (hct.prod had)
  have hne : ComputableInPolyTime
      (fun a =>
        extractCramerShoupTuple (ct_q a) (ad_q a) != extractCramerShoupTuple (ct a) (ad a))
      encIn encBool :=
    ComputableInPolyTime.bool_not.comp (hx.beq hy)
  have hord := F.computableInPolyTime_order.comp hd
  have hmodx := ComputableInPolyTime.binary_mod'
    (ComputableInPolyTime.bitsToNat.comp (hH.comp (hd.prod hx))) hord
  have hmody := ComputableInPolyTime.binary_mod'
    (ComputableInPolyTime.bitsToNat.comp (hH.comp (hd.prod hy))) hord
  exact ComputableInPolyTime.bool_and.comp (hne.prod (hmodx.beq hmody))

/-- Phase 1 decryption oracle handler for Cramer–Shoup (`hasAD = true` for `cca2ADPhase1Oracle`,
`hasAD = false` for `cca2Phase1Oracle`). -/
def cramerShoupPhase1Oracle (hasAD : Bool) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (d : F.Desc)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (request : Unit × List Bool) :
    StateT Unit ProbComp (List Bool) :=
  fun s => pure (F.cramerShoupPhase1Reply hasAD H isElem d sk request.2, s)

/-- Stateless Phase 2 decryption reply for Cramer–Shoup, rejecting the challenge `(ct, ad)`
with `[]`. -/
def cramerShoupPhase2Reply (hasAD : Bool) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (d : F.Desc)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct ad req : List Bool) : List Bool :=
  let q := splitCramerShoupQuery hasAD req
  if (q.1 == ct) && (q.2 == ad) then
    []
  else
    encOption encBits (F.decodeCramerShoup H isElem d sk q.1 q.2)

/-- Phase 2 decryption oracle handler for Cramer–Shoup, rejecting the challenge `(ct, ad)`. -/
def cramerShoupPhase2Oracle (hasAD : Bool) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (d : F.Desc)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct ad : List Bool) (request : Unit × List Bool) :
    StateT Unit ProbComp (List Bool) :=
  fun s => pure (F.cramerShoupPhase2Reply hasAD H isElem d sk ct ad request.2, s)

/-- Phase 2 collision-tracking oracle handler for `cramerShoupMsgToCollisionFinder`: replies with
`cramerShoupCollisionPhase2Reply` and records `some (extractCramerShoupTuple q.1 q.2)` whenever
`isCramerShoupCollision H d q.1 q.2 ct ad` holds (where `q = splitCramerShoupQuery hasAD req`). -/
def cramerShoupCollisionPhase2Oracle (hasAD : Bool) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (d : F.Desc)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct ad : List Bool) (request : Unit × List Bool) :
    StateT (Option (List Bool)) ProbComp (List Bool) :=
  finderPhase2Oracle (F.cramerShoupCollisionPhase2Reply hasAD H isElem d sk ct ad)
    (fun req =>
      let q := splitCramerShoupQuery hasAD req
      F.isCramerShoupCollision H d q.1 q.2 ct ad)
    (fun req =>
      let q := splitCramerShoupQuery hasAD req
      extractCramerShoupTuple q.1 q.2) request

private theorem computableInPolyTime_cramerShoupPhase1Reply
    (hasAD : Bool) {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {req : γ → List Bool}
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hsk : ComputableInPolyTime sk encIn encCramerShoupSK)
    (hreq : ComputableInPolyTime req encIn encBits) :
    ComputableInPolyTime
      (fun a => F.cramerShoupPhase1Reply hasAD H isElem (d a) (sk a) (req a)) encIn encBits := by
  have hsplit := (computableInPolyTime_splitCramerShoupQuery hasAD).comp hreq
  exact (F.computableInPolyTime_decodeCramerShoup_comp hH hisElem hd hsk
    hsplit.fst' hsplit.snd').encoding_comp

private theorem computableInPolyTime_cramerShoupPhase2Reply
    (hasAD : Bool) {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {ct ad req : γ → List Bool}
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hsk : ComputableInPolyTime sk encIn encCramerShoupSK)
    (hct : ComputableInPolyTime ct encIn encBits)
    (had : ComputableInPolyTime ad encIn encBits)
    (hreq : ComputableInPolyTime req encIn encBits) :
    ComputableInPolyTime
      (fun a => F.cramerShoupPhase2Reply hasAD H isElem (d a) (sk a) (ct a) (ad a) (req a))
      encIn encBits := by
  have hsplit := (computableInPolyTime_splitCramerShoupQuery hasAD).comp hreq
  have heq := ComputableInPolyTime.bool_and.comp
    ((hsplit.fst'.beq hct).prod (hsplit.snd'.beq had))
  exact heq.ite (.const [])
    (F.computableInPolyTime_cramerShoupPhase1Reply hasAD hH hisElem hd hsk hreq)

private theorem computableInPolyTime_cramerShoupCollisionPhase2Reply
    (hasAD : Bool) {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {ct ad req : γ → List Bool}
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hsk : ComputableInPolyTime sk encIn encCramerShoupSK)
    (hct : ComputableInPolyTime ct encIn encBits)
    (had : ComputableInPolyTime ad encIn encBits)
    (hreq : ComputableInPolyTime req encIn encBits) :
    ComputableInPolyTime
      (fun a => F.cramerShoupCollisionPhase2Reply hasAD H isElem (d a) (sk a) (ct a) (ad a) (req a))
      encIn encBits := by
  have hsplit := (computableInPolyTime_splitCramerShoupQuery hasAD).comp hreq
  have heq := ComputableInPolyTime.bool_and.comp
    ((hsplit.fst'.beq hct).prod (hsplit.snd'.beq had))
  exact (ComputableInPolyTime.bool_or.comp
      (heq.prod
        (F.computableInPolyTime_isCramerShoupCollision hH hd
          hsplit.fst' hsplit.snd' hct had))).ite
    (.const [])
    (F.computableInPolyTime_cramerShoupPhase1Reply hasAD hH hisElem hd hsk hreq)

private theorem isPPTOn_run_cramerShoupPhase1Oracle
    (hasAD : Bool) {Msg AD : Type} {encMsg : Msg ↪ List Bool} {encAD : AD ↪ List Bool}
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {adversary : ADCCA2AdversaryOf Msg AD}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hA : adversary.IsPPT encMsg encAD)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {pk : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hsk : ComputableInPolyTime sk encIn encCramerShoupSK)
    (hpk : ComputableInPolyTime pk encIn encBits) :
    IsPPTOn encIn
      (encPair (encPair (encPair (encPair encMsg encMsg) encAD) encBits) (encFinEnum Unit))
      (fun a => (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (F.cramerShoupPhase1Oracle hasAD H isElem (d a) (sk a)))
        (adversary.choose (n a) (pk a))).run ()) := by
  have hp1 := ComputableInPolyTime.fst encIn encBits
  have hp2 := ComputableInPolyTime.snd encIn encBits
  have hreply := F.computableInPolyTime_cramerShoupPhase1Reply hasAD hH hisElem
    (hd.comp hp1) (hsk.comp hp1) hp2
  have hE1 := ComputableInPolyTime.fst encIn
    (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hE2 := ComputableInPolyTime.snd encIn
    (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hreplyIn := F.computableInPolyTime_cramerShoupPhase1Reply hasAD hH hisElem
    (hd.comp hE1) (hsk.comp hE1) hE2.fst'.snd'
  exact hA.choose.run_interpret_preprocess'
    (prepare := fun a : γ => (n a, pk a)) (initial := fun _ => ())
    (resources := fun a req => (F.cramerShoupPhase1Reply hasAD H isElem (d a) (sk a) req).length)
    (hn.prod hpk) (hreplyIn.prod hE2.snd').isPPTOn (.const ()) (fun _ _ => True)
    (fun _ => trivial) (ComputableInPolyTime.length_bits.comp hreply)
    (fun a request state _ result hresult => by
      have hresEq : result =
          (F.cramerShoupPhase1Reply hasAD H isElem (d a) (sk a) request.2, state) := by
        simpa [cramerShoupPhase1Oracle] using hresult
      subst hresEq
      exact ⟨trivial, le_rfl, Nat.le_add_right _ _⟩)

private theorem isPPTOn_run_cramerShoupPhase2Oracle
    (hasAD : Bool) {Msg AD : Type} {encMsg : Msg ↪ List Bool} {encAD : AD ↪ List Bool}
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {adversary : ADCCA2AdversaryOf Msg AD}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hA : adversary.IsPPT encMsg encAD)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {state ct ad : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hsk : ComputableInPolyTime sk encIn encCramerShoupSK)
    (hstate : ComputableInPolyTime state encIn encBits)
    (hct : ComputableInPolyTime ct encIn encBits)
    (had : ComputableInPolyTime ad encIn encBits) :
    IsPPTOn encIn (encPair encBool (encFinEnum Unit))
      (fun a => (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (F.cramerShoupPhase2Oracle hasAD H isElem (d a) (sk a) (ct a) (ad a)))
        (adversary.guess (n a) (state a) (ct a))).run ()) := by
  have hp1 := ComputableInPolyTime.fst encIn encBits
  have hp2 := ComputableInPolyTime.snd encIn encBits
  have hreply := F.computableInPolyTime_cramerShoupPhase2Reply hasAD hH hisElem
    (hd.comp hp1) (hsk.comp hp1) (hct.comp hp1) (had.comp hp1) hp2
  have hE1 := ComputableInPolyTime.fst encIn
    (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hE2 := ComputableInPolyTime.snd encIn
    (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hreplyIn := F.computableInPolyTime_cramerShoupPhase2Reply hasAD hH hisElem
    (hd.comp hE1) (hsk.comp hE1) (hct.comp hE1) (had.comp hE1) hE2.fst'.snd'
  exact hA.guess.run_interpret_preprocess
    (prepare := fun a : γ => (n a, state a, ct a)) (initial := fun _ => ())
    (resources := fun a req =>
      (F.cramerShoupPhase2Reply hasAD H isElem (d a) (sk a) (ct a) (ad a) req).length)
    (hn.prod (hstate.prod hct)).tidy (hreplyIn.prod hE2.snd').isPPTOn
    (ComputableInPolyTime.const ()).tidy (fun _ _ => True)
    (fun _ => trivial) (ComputableInPolyTime.length_bits.comp hreply).tidy
    (fun a request st _ result hresult => by
      have hresEq : result =
          (F.cramerShoupPhase2Reply hasAD H isElem (d a) (sk a) (ct a) (ad a) request.2, st) := by
        simpa [cramerShoupPhase2Oracle] using hresult
      subst hresEq
      exact ⟨trivial, le_rfl, Nat.le_add_right _ _⟩)

private theorem isPPTOn_run_cramerShoupCollisionPhase2Oracle
    (hasAD : Bool) {Msg AD : Type} {encMsg : Msg ↪ List Bool} {encAD : AD ↪ List Bool}
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {adversary : ADCCA2AdversaryOf Msg AD}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hA : adversary.IsPPT encMsg encAD)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {state ct ad : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hsk : ComputableInPolyTime sk encIn encCramerShoupSK)
    (hstate : ComputableInPolyTime state encIn encBits)
    (hct : ComputableInPolyTime ct encIn encBits)
    (had : ComputableInPolyTime ad encIn encBits) :
    IsPPTOn encIn (encPair encBool (encOption encBits))
      (fun a => (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (F.cramerShoupCollisionPhase2Oracle hasAD H isElem (d a) (sk a) (ct a) (ad a)))
        (adversary.guess (n a) (state a) (ct a))).run none) := by
  have hp1 := ComputableInPolyTime.fst encIn encBits
  have hp2 := ComputableInPolyTime.snd encIn encBits
  have hreply := F.computableInPolyTime_cramerShoupCollisionPhase2Reply hasAD hH hisElem
    (hd.comp hp1) (hsk.comp hp1) (hct.comp hp1) (had.comp hp1) hp2
  have hE1 := ComputableInPolyTime.fst encIn
    (encPair (encPair (encFinEnum Unit) encBits) (encOption encBits))
  have hE2 := ComputableInPolyTime.snd encIn
    (encPair (encPair (encFinEnum Unit) encBits) (encOption encBits))
  have hreplyIn := F.computableInPolyTime_cramerShoupCollisionPhase2Reply hasAD hH hisElem
    (hd.comp hE1) (hsk.comp hE1) (hct.comp hE1) (had.comp hE1) hE2.fst'.snd'
  have hsplitIn := (computableInPolyTime_splitCramerShoupQuery hasAD).comp hE2.fst'.snd'
  have hcollIn := F.computableInPolyTime_isCramerShoupCollision hH
    (hd.comp hE1) hsplitIn.fst' hsplitIn.snd' (hct.comp hE1) (had.comp hE1)
  have hsome := ComputableInPolyTime.optionSome encBits
  have hnextState := hcollIn.ite
    (hsome.comp (computableInPolyTime_extractCramerShoupTuple.comp hsplitIn))
    hE2.snd'
  have hsplitP2 := (computableInPolyTime_splitCramerShoupQuery hasAD).comp hp2
  have hsomeLen := ComputableInPolyTime.length_bits.comp
    (hsome.comp (computableInPolyTime_extractCramerShoupTuple.comp hsplitP2)).encoding_comp
  have hres := ComputableInPolyTime.unary_add.comp
    ((ComputableInPolyTime.length_bits.comp hreply).prod hsomeLen)
  exact hA.guess.run_interpret_preprocess
    (prepare := fun a : γ => (n a, state a, ct a)) (initial := fun _ => none)
    (resources := fun a req =>
      let q := splitCramerShoupQuery hasAD req
      (F.cramerShoupCollisionPhase2Reply hasAD H isElem (d a) (sk a) (ct a) (ad a) req).length +
      (encOption encBits (some (extractCramerShoupTuple q.1 q.2))).length)
    (hn.prod (hstate.prod hct)).tidy (hreplyIn.prod hnextState).isPPTOn
    (ComputableInPolyTime.const (none : Option (List Bool))).tidy (fun _ _ => True)
    (fun _ => trivial) hres.tidy
    (fun a request st _ result hresult => by
      let q := splitCramerShoupQuery hasAD request.2
      have hresEq : result =
          (F.cramerShoupCollisionPhase2Reply hasAD H isElem (d a) (sk a) (ct a) (ad a) request.2,
           if F.isCramerShoupCollision H (d a) q.1 q.2 (ct a) (ad a) then
             some (extractCramerShoupTuple q.1 q.2)
           else st) := by
        simpa [cramerShoupCollisionPhase2Oracle, finderPhase2Oracle, q] using hresult
      subst hresEq; dsimp only [q]
      refine ⟨trivial, Nat.le_add_right _ _, ?_⟩
      split_ifs <;> omega)

/-- The DDH distinguisher constructed from an `ADCCA2AdversaryOf Msg AD` with message-to-group-word
encoding `encodeMsg : F.Desc × Msg → List Bool` and associated-data encoding
`encodeAD : F.Desc × AD → List Bool` ([BonehShoup2023], proof of Theorem 12.9, Game 1 $\to$ Game 2,
equation (12.22), printed pp. 490, 492, adapted to $\mathcal{E}_{\mathrm{MCS}}$ with associated
data). It encodes the DDH elements `(u, v, w)` of group `d` and runs the word-level game on
them. -/
noncomputable def cramerShoupMsgToDDHDistinguisher
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) : F.DDHDistinguisher :=
  fun n d u v w => do
    let sk ← F.sampleCramerShoupSK n d
    let pk := F.encodeCramerShoupPublicKey d (F.encode d u) sk
    let choiceOut ← (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
      (adversary.choose n pk)).run ()
    let choice := choiceOut.1
    let m₀ := encodeMsg (d, csChoiceMsg₀ choice)
    let m₁ := encodeMsg (d, csChoiceMsg₁ choice)
    let ad := encodeAD (d, csChoiceAD choice)
    if isElem (d, m₀) && isElem (d, m₁) then
      let m := if bit then m₁ else m₀
      let ct := F.encodeCramerShoupChallenge H d sk (F.encode d v) (F.encode d w) m ad
      let guessOut ← (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (F.cramerShoupPhase2Oracle hasAD H isElem d sk ct ad))
        (adversary.guess n choice.2 ct)).run ()
      return guessOut.1
    else
      return false

/-- The DDH distinguisher constructed from a group-message 1CCA adversary with associated data
(`Msg = List Bool`, `encodeMsg = Prod.snd`, `encodeAD = fun p => encAD p.2`). -/
noncomputable abbrev cramerShoupADToDDHDistinguisher
    {AD : Type} (encAD : AD ↪ List Bool)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf (List Bool) AD) (bit : Bool) : F.DDHDistinguisher :=
  F.cramerShoupMsgToDDHDistinguisher true Prod.snd (fun p => encAD p.2) H isElem adversary bit

/-- The DDH distinguisher constructed from an associated-data-free group-message 1CCA adversary
(`Msg = List Bool`, `encodeMsg = Prod.snd`, `ad = []`). -/
noncomputable abbrev cramerShoupToDDHDistinguisher
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : CCA2AdversaryOf (List Bool)) (bit : Bool) : F.DDHDistinguisher :=
  F.cramerShoupMsgToDDHDistinguisher false Prod.snd (fun _ => []) H isElem adversary.toADUnit bit

/-- `cramerShoupMsgToDDHDistinguisher` is uniform strict PPT whenever `encodeMsg`, `encodeAD`, `H`,
and `isElem` are computable in polynomial time and `adversary` is a strict oracle PPT 1CCA
adversary with associated data. -/
theorem isPPT_cramerShoupMsgToDDHDistinguisher
    (hasAD : Bool) {Msg AD : Type} {encMsg : Msg ↪ List Bool} {encAD : AD ↪ List Bool}
    {encodeMsg : F.Desc × Msg → List Bool} {encodeAD : F.Desc × AD → List Bool}
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {adversary : ADCCA2AdversaryOf Msg AD}
    (hencMsg : ComputableInPolyTime encodeMsg (encPair F.encDesc encMsg) encBits)
    (hencAD : ComputableInPolyTime encodeAD (encPair F.encDesc encAD) encBits)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hA : adversary.IsPPT encMsg encAD) (bit : Bool) :
    (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary bit).IsPPT := by
  unfold DDHDistinguisher.IsPPT
  let E0 := F.encDDHInput
  let E1 := encPair E0 encCramerShoupSK
  let EChoice := encPair (encPair (encPair (encPair encMsg encMsg) encAD) encBits) (encFinEnum Unit)
  have hp1 := ComputableInPolyTime.id' (encIn := E1)
  have hp2 := ComputableInPolyTime.id' (encIn := encPair E1 EChoice)
  have hn0 : ComputableInPolyTime (fun x : F.DDHInput => x.secParam) E0 encUnary := by fun_prop
  have hd0 : ComputableInPolyTime (fun x : F.DDHInput => x.groupParameters) E0 F.encDesc := by
    fun_prop
  have hu0 : ComputableInPolyTime (fun x : F.DDHInput => F.encode x.groupParameters x.leftPublic)
      E0 encBits := by fun_prop
  have hv0 : ComputableInPolyTime (fun x : F.DDHInput => F.encode x.groupParameters x.rightPublic)
      E0 encBits := by fun_prop
  have hw0 : ComputableInPolyTime
      (fun x : F.DDHInput => F.encode x.groupParameters x.candidateShared) E0 encBits := by
    fun_prop
  have hd1 := hd0.comp hp1.fst'
  have hsk := F.isPPTOn_sampleCramerShoupSK hn0 hd0
  have hpk := F.computableInPolyTime_encodeCramerShoupPublicKey.comp
    (hd1.prod ((hu0.comp hp1.fst').prod hp1.snd'))
  have hphase1 := F.isPPTOn_run_cramerShoupPhase1Oracle hasAD hH hisElem hA
    (hn0.comp hp1.fst') hd1 hp1.snd' hpk
  have hd2 := hd0.comp hp2.fst'.fst'
  have hm₀ := hencMsg.comp (hd2.prod hp2.snd'.fst'.fst'.fst'.fst')
  have hm₁ := hencMsg.comp (hd2.prod hp2.snd'.fst'.fst'.fst'.snd')
  have had := hencAD.comp (hd2.prod hp2.snd'.fst'.fst'.snd')
  have hvalid := ComputableInPolyTime.bool_and.comp
    ((hisElem.comp (hd2.prod hm₀)).prod (hisElem.comp (hd2.prod hm₁)))
  have hm : ComputableInPolyTime
      (fun p => if bit then encodeMsg (p.1.1.groupParameters, p.2.1.1.1.2)
        else encodeMsg (p.1.1.groupParameters, p.2.1.1.1.1)) (encPair E1 EChoice) encBits := by
    cases bit <;> assumption
  have hct := (F.computableInPolyTime_encodeCramerShoupChallenge hH).comp
    (hd2.prod (hp2.fst'.snd'.prod ((hv0.comp hp2.fst'.fst').prod
      ((hw0.comp hp2.fst'.fst').prod (hm.prod had)))))
  have hphase2 := F.isPPTOn_run_cramerShoupPhase2Oracle hasAD hH hisElem hA
    (hn0.comp hp2.fst'.fst') hd2 hp2.fst'.snd' hp2.snd'.fst'.snd' hct had
  exact hsk.bind_with (hphase1.bind_with (IsPPTOn.cond' hvalid
    (hphase2.bind_with ((ComputableInPolyTime.snd
      (encPair E1 EChoice) (encPair encBool (encFinEnum Unit))).fst').isPPTOn)
    (ComputableInPolyTime.isPPTOn (.const false))))

/-- `cramerShoupADToDDHDistinguisher` is uniform strict PPT whenever `H` and `isElem` are
computable in polynomial time and `adversary` is a strict oracle PPT 1CCA adversary with associated
data. -/
theorem isPPT_cramerShoupADToDDHDistinguisher
    {AD : Type} {encAD : AD ↪ List Bool}
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {adversary : ADCCA2AdversaryOf (List Bool) AD}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hA : adversary.IsPPT encBits encAD) (bit : Bool) :
    (F.cramerShoupADToDDHDistinguisher encAD H isElem adversary bit).IsPPT :=
  F.isPPT_cramerShoupMsgToDDHDistinguisher true
    (ComputableInPolyTime.snd F.encDesc encBits)
    (ComputableInPolyTime.snd F.encDesc encAD).encoding_comp hH hisElem hA bit

/-- `cramerShoupToDDHDistinguisher` is uniform strict PPT whenever `H` and `isElem` are computable
in polynomial time and `adversary` is a strict oracle PPT 1CCA adversary. -/
theorem isPPT_cramerShoupToDDHDistinguisher
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {adversary : CCA2AdversaryOf (List Bool)}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hA : adversary.IsPPT encBits) (bit : Bool) :
    (F.cramerShoupToDDHDistinguisher H isElem adversary bit).IsPPT :=
  F.isPPT_cramerShoupMsgToDDHDistinguisher false
    (ComputableInPolyTime.snd F.encDesc encBits) (.const [])
    hH hisElem hA.toADUnit bit

/-- The setup-parameterized collision finder constructed from an `ADCCA2AdversaryOf Msg AD` with
message-to-group-word encoding `encodeMsg : F.Desc × Msg → List Bool` and associated-data encoding
`encodeAD : F.Desc × AD → List Bool` ([BonehShoup2023], proof of Theorem 12.9, Game 4, equations
(12.24)–(12.25), printed p. 492, adapted to $\mathcal{E}_{\mathrm{MCS}}$ with associated data). -/
noncomputable def cramerShoupMsgToCollisionFinder
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) :
    CollisionFinderFor F.Desc :=
  fun n d => do
    let abc ← F.sampleCramerShoupTripleExponents n d
    let sk ← F.sampleCramerShoupSK n d
    let gen := F.encode d (F.generator d)
    let u := F.smul (d, csExpA abc, gen)
    let v := F.smul (d, csExpB abc, gen)
    let w := F.smul (d, csExpC abc, gen)
    let pk := F.encodeCramerShoupPublicKey d u sk
    let choiceOut ← (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
      (adversary.choose n pk)).run ()
    let choice := choiceOut.1
    let m₀ := encodeMsg (d, csChoiceMsg₀ choice)
    let m₁ := encodeMsg (d, csChoiceMsg₁ choice)
    let ad := encodeAD (d, csChoiceAD choice)
    if isElem (d, m₀) && isElem (d, m₁) then
      let m := if bit then m₁ else m₀
      let ct := F.encodeCramerShoupChallenge H d sk v w m ad
      let out ← (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (F.cramerShoupCollisionPhase2Oracle hasAD H isElem d sk ct ad))
        (adversary.guess n choice.2 ct)).run none
      let target := extractCramerShoupTuple ct ad
      return (out.2.getD target, target)
    else
      return ([], [])

/-- The setup-parameterized collision finder constructed from a group-message 1CCA adversary with
associated data (`Msg = List Bool`, `encodeMsg = Prod.snd`, `encodeAD = fun p => encAD p.2`). -/
noncomputable abbrev cramerShoupADToCollisionFinder
    {AD : Type} (encAD : AD ↪ List Bool)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf (List Bool) AD) (bit : Bool) :
    CollisionFinderFor F.Desc :=
  F.cramerShoupMsgToCollisionFinder true Prod.snd (fun p => encAD p.2) H isElem adversary bit

/-- The setup-parameterized collision finder constructed from an associated-data-free group-message
1CCA adversary (`Msg = List Bool`, `encodeMsg = Prod.snd`, `ad = []`). -/
noncomputable abbrev cramerShoupToCollisionFinder
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : CCA2AdversaryOf (List Bool)) (bit : Bool) :
    CollisionFinderFor F.Desc :=
  F.cramerShoupMsgToCollisionFinder false Prod.snd (fun _ => []) H isElem adversary.toADUnit bit

/-- `cramerShoupMsgToCollisionFinder` is uniform strict PPT whenever `encodeMsg`, `encodeAD`, `H`,
and `isElem` are computable in polynomial time and `adversary` is a strict oracle PPT 1CCA
adversary with associated data. -/
theorem isPPTOn_cramerShoupMsgToCollisionFinder
    (hasAD : Bool) {Msg AD : Type} {encMsg : Msg ↪ List Bool} {encAD : AD ↪ List Bool}
    {encodeMsg : F.Desc × Msg → List Bool} {encodeAD : F.Desc × AD → List Bool}
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {adversary : ADCCA2AdversaryOf Msg AD}
    (hencMsg : ComputableInPolyTime encodeMsg (encPair F.encDesc encMsg) encBits)
    (hencAD : ComputableInPolyTime encodeAD (encPair F.encDesc encAD) encBits)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hA : adversary.IsPPT encMsg encAD) (bit : Bool) :
    IsPPTOn (encPair encUnary F.encDesc) (encPair encBits encBits)
      (fun p =>
        F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary bit
          p.1 p.2) := by
  let E0 := encPair encUnary F.encDesc
  let EExp := encPair encNat (encPair encNat encNat)
  let E1 := encPair E0 EExp
  let E2 := encPair E1 encCramerShoupSK
  let EChoice := encPair (encPair (encPair (encPair encMsg encMsg) encAD) encBits) (encFinEnum Unit)
  let E3 := encPair E2 EChoice
  have hp0 := ComputableInPolyTime.id' (encIn := E0)
  have hp1 := ComputableInPolyTime.id' (encIn := E1)
  have hp2 := ComputableInPolyTime.id' (encIn := E2)
  have hp3 := ComputableInPolyTime.id' (encIn := E3)
  have hp4 :=
    ComputableInPolyTime.id' (encIn := encPair E3 (encPair encBool (encOption encBits)))
  have habc := F.isPPTOn_sampleCramerShoupTripleExponents hp0.fst' hp0.snd'
  have hsk := F.isPPTOn_sampleCramerShoupSK hp1.fst'.fst' hp1.fst'.snd'
  have hsmul := F.computableInPolyTime_smul
  have hd2 := hp2.fst'.fst'.snd'
  have hu := hsmul.comp
    (hd2.prod (hp2.fst'.snd'.fst'.prod (F.computableInPolyTime_generator.comp hd2)))
  have hpk := F.computableInPolyTime_encodeCramerShoupPublicKey.comp
    (hd2.prod (hu.prod hp2.snd'))
  have hphase1 := F.isPPTOn_run_cramerShoupPhase1Oracle hasAD hH hisElem hA
    hp2.fst'.fst'.fst' hd2 hp2.snd' hpk
  have hd3 := hp3.fst'.fst'.fst'.snd'
  have hm₀ := hencMsg.comp (hd3.prod hp3.snd'.fst'.fst'.fst'.fst')
  have hm₁ := hencMsg.comp (hd3.prod hp3.snd'.fst'.fst'.fst'.snd')
  have had := hencAD.comp (hd3.prod hp3.snd'.fst'.fst'.snd')
  have hvalid := ComputableInPolyTime.bool_and.comp
    ((hisElem.comp (hd3.prod hm₀)).prod (hisElem.comp (hd3.prod hm₁)))
  have hgen3 := F.computableInPolyTime_generator.comp hd3
  have hv := hsmul.comp (hd3.prod (hp3.fst'.fst'.snd'.snd'.fst'.prod hgen3))
  have hw := hsmul.comp (hd3.prod (hp3.fst'.fst'.snd'.snd'.snd'.prod hgen3))
  have hm : ComputableInPolyTime
      (fun p => if bit then encodeMsg (p.1.1.1.2, p.2.1.1.1.2)
        else encodeMsg (p.1.1.1.2, p.2.1.1.1.1)) E3 encBits := by
    cases bit <;> assumption
  have hct := (F.computableInPolyTime_encodeCramerShoupChallenge hH).comp
    (hd3.prod (hp3.fst'.snd'.prod (hv.prod (hw.prod (hm.prod had)))))
  have hphase2c := F.isPPTOn_run_cramerShoupCollisionPhase2Oracle hasAD hH hisElem hA
    hp3.fst'.fst'.fst'.fst' hd3 hp3.fst'.snd' hp3.snd'.fst'.snd' hct had
  have htarget := computableInPolyTime_extractCramerShoupTuple.comp
    ((hct.comp hp4.fst').prod (had.comp hp4.fst'))
  have houtPair :=
    (ComputableInPolyTime.optionGetDWithInput hp4.snd'.snd' htarget).prod htarget
  exact habc.bind_with (hsk.bind_with (hphase1.bind_with (IsPPTOn.cond' hvalid
    (hphase2c.bind_with houtPair.isPPTOn)
    (ComputableInPolyTime.isPPTOn (.const (([] : List Bool), []))))))

/-- `cramerShoupADToCollisionFinder` is uniform strict PPT whenever `H` and `isElem` are computable
in polynomial time and `adversary` is a strict oracle PPT 1CCA adversary with associated data. -/
theorem isPPTOn_cramerShoupADToCollisionFinder
    {AD : Type} {encAD : AD ↪ List Bool}
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {adversary : ADCCA2AdversaryOf (List Bool) AD}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hA : adversary.IsPPT encBits encAD) (bit : Bool) :
    IsPPTOn (encPair encUnary F.encDesc) (encPair encBits encBits)
      (fun p => F.cramerShoupADToCollisionFinder encAD H isElem adversary bit p.1 p.2) :=
  F.isPPTOn_cramerShoupMsgToCollisionFinder true
    (ComputableInPolyTime.snd F.encDesc encBits)
    (ComputableInPolyTime.snd F.encDesc encAD).encoding_comp hH hisElem hA bit

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
  F.isPPTOn_cramerShoupMsgToCollisionFinder false
    (ComputableInPolyTime.snd F.encDesc encBits) (.const [])
    hH hisElem hA.toADUnit bit

/-- `encodeCramerShoupPublicKey` depends on `sk` only through its residues modulo `F.order d`. -/
theorem encodeCramerShoupPublicKey_eq_skNatOfZMod (d : F.Desc)
    (α : ZMod (F.order d)) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d)) sk =
      F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d))
        (F.skNatOfZMod d ((csSkS sk : ℕ) : ZMod (F.order d)) ((csSkT sk : ℕ) : ZMod (F.order d))
          ((csSkS₁ sk : ℕ) : ZMod (F.order d)) ((csSkT₁ sk : ℕ) : ZMod (F.order d))
          ((csSkS₂ sk : ℕ) : ZMod (F.order d)) ((csSkT₂ sk : ℕ) : ZMod (F.order d))) := by
  simp only [encodeCramerShoupPublicKey_encode, skNatOfZMod,
    csSkS, csSkT, csSkS₁, csSkT₁, csSkS₂, csSkT₂, ZMod.natCast_zmod_val]

/-- `encodeCramerShoupChallenge` depends on `sk` only through its residues modulo `F.order d`. -/
theorem encodeCramerShoupChallenge_eq_skNatOfZMod
    (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (v w : F.Carrier d) (m ad : List Bool) :
    F.encodeCramerShoupChallenge H d sk (F.encode d v) (F.encode d w) m ad =
      F.encodeCramerShoupChallenge H d
        (F.skNatOfZMod d ((csSkS sk : ℕ) : ZMod (F.order d)) ((csSkT sk : ℕ) : ZMod (F.order d))
          ((csSkS₁ sk : ℕ) : ZMod (F.order d)) ((csSkT₁ sk : ℕ) : ZMod (F.order d))
          ((csSkS₂ sk : ℕ) : ZMod (F.order d)) ((csSkT₂ sk : ℕ) : ZMod (F.order d)))
        (F.encode d v) (F.encode d w) m ad := by
  simp only [encodeCramerShoupChallenge, skNatOfZMod, encodeProjHash_encode,
    encodeProjHash2_encode, csSkS, csSkT, csSkS₁, csSkT₁, csSkS₂, csSkT₂, ZMod.natCast_zmod_val]

/-- `decodeCramerShoup` depends on `sk` only through its residues modulo `F.order d`. -/
theorem decodeCramerShoup_eq_skNatOfZMod
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct ad : List Bool) :
    F.decodeCramerShoup H isElem d sk ct ad =
      F.decodeCramerShoup H isElem d
        (F.skNatOfZMod d ((csSkS sk : ℕ) : ZMod (F.order d)) ((csSkT sk : ℕ) : ZMod (F.order d))
          ((csSkS₁ sk : ℕ) : ZMod (F.order d)) ((csSkT₁ sk : ℕ) : ZMod (F.order d))
          ((csSkS₂ sk : ℕ) : ZMod (F.order d)) ((csSkT₂ sk : ℕ) : ZMod (F.order d))) ct ad := by
  unfold decodeCramerShoup
  by_cases hvw :
      isElem (d, csCtV (decodeBits4 ct)) = true ∧ isElem (d, csCtW (decodeBits4 ct)) = true
  · obtain ⟨v, hv⟩ := (hmem d _).mp hvw.1
    obtain ⟨w, hw⟩ := (hmem d _).mp hvw.2
    simp only [← hv, ← hw, skNatOfZMod, encodeProjHash2_encode, encodeProjHash_encode,
      csSkS, csSkT, csSkS₁, csSkT₁, csSkS₂, csSkT₂, ZMod.natCast_zmod_val]
  · have hfalse : ((encBits4 (decodeBits4 ct) == ct) && isElem (d, csCtV (decodeBits4 ct)) &&
        isElem (d, csCtW (decodeBits4 ct)) && isElem (d, csCtE (decodeBits4 ct))) = false := by
      revert hvw
      cases isElem (d, csCtV (decodeBits4 ct)) <;> cases isElem (d, csCtW (decodeBits4 ct)) <;> simp
    simp [hfalse]

/-- `cramerShoupPhase1Oracle` depends on `sk` only through its residues modulo `F.order d`. -/
theorem cramerShoupPhase1Oracle_eq_skNatOfZMod
    (hasAD : Bool) (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    F.cramerShoupPhase1Oracle hasAD H isElem d sk =
      F.cramerShoupPhase1Oracle hasAD H isElem d
        (F.skNatOfZMod d ((csSkS sk : ℕ) : ZMod (F.order d)) ((csSkT sk : ℕ) : ZMod (F.order d))
          ((csSkS₁ sk : ℕ) : ZMod (F.order d)) ((csSkT₁ sk : ℕ) : ZMod (F.order d))
          ((csSkS₂ sk : ℕ) : ZMod (F.order d)) ((csSkT₂ sk : ℕ) : ZMod (F.order d))) := by
  funext req s
  simp only [cramerShoupPhase1Oracle, cramerShoupPhase1Reply,
    F.decodeCramerShoup_eq_skNatOfZMod H isElem hmem d sk]

/-- `cramerShoupPhase2Oracle` depends on `sk` only through its residues modulo `F.order d`. -/
theorem cramerShoupPhase2Oracle_eq_skNatOfZMod
    (hasAD : Bool) (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct ad : List Bool) :
    F.cramerShoupPhase2Oracle hasAD H isElem d sk ct ad =
      F.cramerShoupPhase2Oracle hasAD H isElem d
        (F.skNatOfZMod d ((csSkS sk : ℕ) : ZMod (F.order d)) ((csSkT sk : ℕ) : ZMod (F.order d))
          ((csSkS₁ sk : ℕ) : ZMod (F.order d)) ((csSkT₁ sk : ℕ) : ZMod (F.order d))
          ((csSkS₂ sk : ℕ) : ZMod (F.order d)) ((csSkT₂ sk : ℕ) : ZMod (F.order d))) ct ad := by
  funext req s
  simp only [cramerShoupPhase2Oracle, cramerShoupPhase2Reply,
    F.decodeCramerShoup_eq_skNatOfZMod H isElem hmem d sk]

/-- `cramerShoupCollisionPhase2Oracle` depends on `sk` only through its residues modulo
`F.order d`. -/
theorem cramerShoupCollisionPhase2Oracle_eq_skNatOfZMod
    (hasAD : Bool) (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct ad : List Bool) :
    F.cramerShoupCollisionPhase2Oracle hasAD H isElem d sk ct ad =
      F.cramerShoupCollisionPhase2Oracle hasAD H isElem d
        (F.skNatOfZMod d ((csSkS sk : ℕ) : ZMod (F.order d)) ((csSkT sk : ℕ) : ZMod (F.order d))
          ((csSkS₁ sk : ℕ) : ZMod (F.order d)) ((csSkT₁ sk : ℕ) : ZMod (F.order d))
          ((csSkS₂ sk : ℕ) : ZMod (F.order d)) ((csSkT₂ sk : ℕ) : ZMod (F.order d))) ct ad := by
  funext req s
  simp only [cramerShoupCollisionPhase2Oracle, finderPhase2Oracle, cramerShoupCollisionPhase2Reply,
    F.decodeCramerShoup_eq_skNatOfZMod H isElem hmem d sk]

/-- Word-level public-key encryption under `cramerShoupPublicKey d α σ τ σ₁ τ₁ σ₂ τ₂` coincides with
`encodeCramerShoupChallenge` on `(v, w) = (β • g, (α * β) • g)` ([BonehShoup2023], Section 12.5.3,
Game 0 $\to$ Game 1, equation (12.21), printed p. 490). -/
@[simp]
theorem encodeCramerShoupEncrypt_publicKey_eq_challenge
    (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (α β σ τ σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d)) (m ad : List Bool) :
    let pkVal := F.cramerShoupPublicKey d α σ τ σ₁ τ₁ σ₂ τ₂
    F.encodeCramerShoupEncrypt H d
      (F.encode d (csPkU pkVal), F.encode d (csPkH pkVal),
        F.encode d (csPkH₁ pkVal), F.encode d (csPkH₂ pkVal))
      m ad β.val =
      F.encodeCramerShoupChallenge H d (F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂)
        (F.encode d (β • F.generator d)) (F.encode d ((α * β) • F.generator d)) m ad := by
  dsimp only
  have hαβ : (α * β) • F.generator d = β • (α • F.generator d) := by rw [smul_smul, mul_comm]
  rw [hαβ]
  simp only [encodeCramerShoupEncrypt, encodeCramerShoupChallenge, cramerShoupPublicKey,
    csPkU, csPkH, csPkH₁, csPkH₂, csSkS, csSkT, csSkS₁, csSkT₁, csSkS₂, csSkT₂,
    projHash2Aux, skNatOfZMod, F.smul_encode, F.add_encode, ZMod.natCast_zmod_val,
    encodeProjHash_encode, encodeProjHash2_encode, projHash_smul_generator,
    projHash2_smul_generator]

/-! ### `Encryption.cca2ADGameOn` and `Encryption.cca2GameOn` instantiation -/

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
  simp [encCramerShoupSK, decodeCramerShoupSK, encPair_apply, encNat_apply,
    unframe_frame_append, dropFrame_frame_append]

private theorem computableInPolyTime_decodeCramerShoupSK :
    ComputableInPolyTime decodeCramerShoupSK encBits encCramerShoupSK := by
  have hp1 := ComputableInPolyTime.unframe
  have hp2 := ComputableInPolyTime.dropFrame
  have hpair := (ComputableInPolyTime.bitsToNat.comp hp1).prod
    (ComputableInPolyTime.bitsToNat.comp hp2)
  exact (hpair.comp hp1).prod ((hpair.comp (hp1.comp hp2)).prod (hpair.comp (hp2.comp hp2)))

/-- Challenge-pair group-membership admissibility predicate for `Encryption.cca2ADGameOn` and
`Encryption.cca2GameOn` ([BonehShoup2023], Section 12.5.3 & Exercise 12.27): both challenge words
`m₀` and `m₁` must belong to the group `F.Carrier (d n)`. -/
def cramerShoupValid (isElem : F.Desc × List Bool → Bool) (d : ℕ → F.Desc)
    (n : ℕ) (_pk m₀ m₁ : List Bool) : Bool :=
  isElem (d n, m₀) && isElem (d n, m₁)

/-- Probabilistic polynomial-time Cramer–Shoup key generation for a group family `d : ℕ → F.Desc`,
sampling approximate uniform exponents via `sampleModNat`. -/
noncomputable def cramerShoupKeyGenProb (d : ℕ → F.Desc) (n : ℕ) :
    ProbComp (List Bool × List Bool) := do
  let a ← F.sampleExp n (d n)
  let sk ← F.sampleCramerShoupSK n (d n)
  let u := F.smul (d n, a, F.encode (d n) (F.generator (d n)))
  return (F.encodeCramerShoupPublicKey (d n) u sk, encCramerShoupSK sk)

/-- Probabilistic polynomial-time Cramer–Shoup encryption with associated data for a group family
`d : ℕ → F.Desc`, sampling the encryption exponent via `sampleModNat`. -/
noncomputable def cramerShoupADEncryptProb
    {AD : Type} (encAD : AD ↪ List Bool)
    (H : F.Desc × List Bool → List Bool) (d : ℕ → F.Desc)
    (n : ℕ) (pk m : List Bool) (ad : AD) : ProbComp (List Bool) := do
  let b ← F.sampleExp n (d n)
  return F.encodeCramerShoupEncrypt H (d n) (decodeBits4 (dropFrame pk)) m (encAD ad) b

/-- Probabilistic polynomial-time Cramer–Shoup encryption for a group family `d : ℕ → F.Desc`
(associated-data-free specialization `ad = []`), sampling the encryption exponent via
`sampleModNat`. -/
noncomputable def cramerShoupEncryptProb
    (H : F.Desc × List Bool → List Bool) (d : ℕ → F.Desc)
    (n : ℕ) (pk m : List Bool) : ProbComp (List Bool) := do
  let b ← F.sampleExp n (d n)
  return F.encodeCramerShoupEncrypt H (d n) (decodeBits4 (dropFrame pk)) m [] b

/-- Deterministic polynomial-time Cramer–Shoup decryption with associated data for
`Encryption.cca2ADGameOn`. -/
def cramerShoupADDecryptOpt
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (d : ℕ → F.Desc) (n : ℕ) (skBits ct ad : List Bool) : Option (List Bool) :=
  F.decodeCramerShoup H isElem (d n) (decodeCramerShoupSK skBits) ct ad

/-- Deterministic polynomial-time Cramer–Shoup decryption for `Encryption.cca2GameOn`
(associated-data-free specialization `ad = []`). -/
def cramerShoupDecryptOpt
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (d : ℕ → F.Desc) (n : ℕ) (skBits ct : List Bool) : Option (List Bool) :=
  F.cramerShoupADDecryptOpt H isElem d n skBits ct []

/-- `cramerShoupValid` is computable in polynomial time whenever `isElem` and `d` are. -/
theorem computableInPolyTime_cramerShoupValid
    {isElem : F.Desc × List Bool → Bool} {d : ℕ → F.Desc}
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => F.cramerShoupValid isElem d n pk m₀ m₁)
      (encPair encUnary (encPair encBits (encPair encBits encBits))) encBool := by
  have hp := ComputableInPolyTime.id'
    (encIn := encPair encUnary (encPair encBits (encPair encBits encBits)))
  have hd_in := hd.comp hp.fst'
  exact ComputableInPolyTime.bool_and.comp
    ((hisElem.comp (hd_in.prod hp.snd'.snd'.fst')).prod
      (hisElem.comp (hd_in.prod hp.snd'.snd'.snd')))

/-- `cramerShoupKeyGenProb` is uniformly strict PPT whenever `d` is computable in polynomial
time. -/
theorem isPPTOn_cramerShoupKeyGenProb {d : ℕ → F.Desc}
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    IsPPTOn encUnary (encPair encBits encBits) (F.cramerShoupKeyGenProb d) := by
  let E1 := encPair encUnary encNat
  have hp1 := ComputableInPolyTime.id' (encIn := E1)
  have hp2 := ComputableInPolyTime.id' (encIn := encPair E1 encCramerShoupSK)
  have hd2 := hd.comp hp2.fst'.fst'
  have hu := F.computableInPolyTime_smul.comp
    (hd2.prod (hp2.fst'.snd'.prod (F.computableInPolyTime_generator.comp hd2)))
  have hpk := F.computableInPolyTime_encodeCramerShoupPublicKey.comp
    (hd2.prod (hu.prod hp2.snd'))
  have hskBits := hp2.snd'.encoding_comp
  exact (F.isPPTOn_sampleExp (.id' (encIn := encUnary)) hd).bind_with
    ((F.isPPTOn_sampleCramerShoupSK hp1.fst' (hd.comp hp1.fst')).bind_with
      (hpk.prod hskBits).isPPTOn)

/-- `cramerShoupADEncryptProb` is uniformly strict PPT whenever `H` and `d` are computable in
polynomial time. -/
theorem isPPTOn_cramerShoupADEncryptProb
    {AD : Type} (encAD : AD ↪ List Bool)
    {H : F.Desc × List Bool → List Bool} {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    IsPPTOn (encPair encUnary (encPair encBits (encPair encBits encAD))) encBits
      (fun ⟨n, pk, m, ad⟩ => F.cramerShoupADEncryptProb encAD H d n pk m ad) := by
  let E0 := encPair encUnary (encPair encBits (encPair encBits encAD))
  have hp0 := ComputableInPolyTime.id' (encIn := E0)
  have hp1 := ComputableInPolyTime.id' (encIn := encPair E0 encNat)
  have hct := (F.computableInPolyTime_encodeCramerShoupEncrypt hH).comp
    ((hd.comp hp1.fst'.fst').prod
      ((computableInPolyTime_decodeBits4.comp
        (ComputableInPolyTime.dropFrame.comp hp1.fst'.snd'.fst')).prod
        (hp1.fst'.snd'.snd'.fst'.prod
          (hp1.fst'.snd'.snd'.snd'.encoding_comp.prod hp1.snd'))))
  exact (F.isPPTOn_sampleExp hp0.fst' (hd.comp hp0.fst')).bind_with hct.isPPTOn

/-- `cramerShoupEncryptProb` is uniformly strict PPT whenever `H` and `d` are computable in
polynomial time. -/
theorem isPPTOn_cramerShoupEncryptProb
    {H : F.Desc × List Bool → List Bool} {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun ⟨n, pk, m⟩ => F.cramerShoupEncryptProb H d n pk m) := by
  let E0 := encPair encUnary (encPair encBits encBits)
  have hp0 := ComputableInPolyTime.id' (encIn := E0)
  have hp1 := ComputableInPolyTime.id' (encIn := encPair E0 encNat)
  have hct := (F.computableInPolyTime_encodeCramerShoupEncrypt hH).comp
    ((hd.comp hp1.fst'.fst').prod
      ((computableInPolyTime_decodeBits4.comp
        (ComputableInPolyTime.dropFrame.comp hp1.fst'.snd'.fst')).prod
        (hp1.fst'.snd'.snd'.prod
          ((ComputableInPolyTime.const []).prod hp1.snd'))))
  exact (F.isPPTOn_sampleExp hp0.fst' (hd.comp hp0.fst')).bind_with hct.isPPTOn

/-- `cramerShoupADDecryptOpt` is computable in polynomial time whenever `H`, `isElem`, and `d`
are. -/
theorem computableInPolyTime_cramerShoupADDecryptOpt
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    ComputableInPolyTime
      (fun ⟨n, skBits, ct, ad⟩ => F.cramerShoupADDecryptOpt H isElem d n skBits ct ad)
      (encPair encUnary (encPair encBits (encPair encBits encBits))) (encOption encBits) := by
  have hp := ComputableInPolyTime.id'
    (encIn := encPair encUnary (encPair encBits (encPair encBits encBits)))
  exact F.computableInPolyTime_decodeCramerShoup_comp hH hisElem
    (hd.comp hp.fst') (computableInPolyTime_decodeCramerShoupSK.comp hp.snd'.fst')
    hp.snd'.snd'.fst' hp.snd'.snd'.snd'

/-- `cramerShoupDecryptOpt` is computable in polynomial time whenever `H`, `isElem`, and `d`
are. -/
theorem computableInPolyTime_cramerShoupDecryptOpt
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    ComputableInPolyTime
      (fun ⟨n, skBits, ct⟩ => F.cramerShoupDecryptOpt H isElem d n skBits ct)
      (encPair encUnary (encPair encBits encBits)) (encOption encBits) := by
  have hp := ComputableInPolyTime.id' (encIn := encPair encUnary (encPair encBits encBits))
  exact F.computableInPolyTime_decodeCramerShoup_comp hH hisElem
    (hd.comp hp.fst') (computableInPolyTime_decodeCramerShoupSK.comp hp.snd'.fst')
    hp.snd'.snd' (.const [])

/-- `cca2ADPhase1Oracle` for `cramerShoupADDecryptOpt` agrees with
`cramerShoupPhase1Oracle true`. -/
theorem cca2ADPhase1Oracle_cramerShoupADDecryptOpt
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (d : ℕ → F.Desc) (n : ℕ) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    cca2ADPhase1Oracle encBits (F.cramerShoupADDecryptOpt H isElem d) n (encCramerShoupSK sk) =
      F.cramerShoupPhase1Oracle true H isElem (d n) sk := by
  funext req s
  simp only [cca2ADPhase1Oracle, cramerShoupADDecryptOpt, decodeCramerShoupSK_encCramerShoupSK,
    cramerShoupPhase1Oracle, cramerShoupPhase1Reply, splitCramerShoupQuery, ↓reduceIte]

/-- `cca2ADPhase2Oracle` for `cramerShoupADDecryptOpt` agrees with
`cramerShoupPhase2Oracle true`. -/
theorem cca2ADPhase2Oracle_cramerShoupADDecryptOpt
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (d : ℕ → F.Desc) (n : ℕ) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct ad : List Bool) :
    cca2ADPhase2Oracle encBits (F.cramerShoupADDecryptOpt H isElem d) n (encCramerShoupSK sk)
      ct ad =
      F.cramerShoupPhase2Oracle true H isElem (d n) sk ct ad := by
  funext req s
  simp only [cca2ADPhase2Oracle, cramerShoupADDecryptOpt, decodeCramerShoupSK_encCramerShoupSK,
    cramerShoupPhase2Oracle, cramerShoupPhase2Reply, splitCramerShoupQuery, ↓reduceIte]
  split_ifs <;> rfl

/-- `cca2Phase1Oracle` for `cramerShoupDecryptOpt` agrees with `cramerShoupPhase1Oracle false`. -/
theorem cca2Phase1Oracle_cramerShoupDecryptOpt
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (d : ℕ → F.Desc) (n : ℕ) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    cca2Phase1Oracle encBits (F.cramerShoupDecryptOpt H isElem d) n (encCramerShoupSK sk) =
      F.cramerShoupPhase1Oracle false H isElem (d n) sk := by
  funext req s
  simp only [cca2Phase1Oracle, cramerShoupDecryptOpt, cramerShoupADDecryptOpt,
    decodeCramerShoupSK_encCramerShoupSK, cramerShoupPhase1Oracle, cramerShoupPhase1Reply,
    splitCramerShoupQuery, Bool.false_eq_true, ↓reduceIte]

/-- `cca2Phase2Oracle` for `cramerShoupDecryptOpt` agrees with `cramerShoupPhase2Oracle false`. -/
theorem cca2Phase2Oracle_cramerShoupDecryptOpt
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (d : ℕ → F.Desc) (n : ℕ) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct : List Bool) :
    cca2Phase2Oracle encBits (F.cramerShoupDecryptOpt H isElem d) n (encCramerShoupSK sk) ct =
      F.cramerShoupPhase2Oracle false H isElem (d n) sk ct [] := by
  funext req s
  simp only [cca2Phase2Oracle, cramerShoupDecryptOpt, cramerShoupADDecryptOpt,
    decodeCramerShoupSK_encCramerShoupSK, cramerShoupPhase2Oracle, cramerShoupPhase2Reply,
    splitCramerShoupQuery, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Bool.and_true]
  split_ifs <;> rfl

/-- Extracting the 4-tuple of public-key group words from `encodeCramerShoupPublicKey`. -/
@[simp]
theorem decodeBits4_dropFrame_encodeCramerShoupPublicKey
    (d : F.Desc) (u : List Bool) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    decodeBits4 (dropFrame (F.encodeCramerShoupPublicKey d u sk)) =
      (u, F.encodeProjHashAux d (csSkS sk) (csSkT sk) u,
        F.encodeProjHashAux d (csSkS₁ sk) (csSkT₁ sk) u,
        F.encodeProjHashAux d (csSkS₂ sk) (csSkT₂ sk) u) := by
  simp [encodeCramerShoupPublicKey, encPair_apply, dropFrame_frame_append]

/-- `encodeCramerShoupEncrypt` on the public-key words generated by `skNatOfZMod` agrees with
`cramerShoupPublicKey`. -/
theorem encodeCramerShoupEncrypt_skNatOfZMod
    (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (α σ τ σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d)) (m ad : List Bool) (b : ℕ) :
    let u := F.encode d (α • F.generator d)
    let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
    let pkVal := F.cramerShoupPublicKey d α σ τ σ₁ τ₁ σ₂ τ₂
    F.encodeCramerShoupEncrypt H d
      (u, F.encodeProjHashAux d (csSkS sk) (csSkT sk) u,
        F.encodeProjHashAux d (csSkS₁ sk) (csSkT₁ sk) u,
        F.encodeProjHashAux d (csSkS₂ sk) (csSkT₂ sk) u) m ad b =
      F.encodeCramerShoupEncrypt H d
        (F.encode d (csPkU pkVal), F.encode d (csPkH pkVal),
          F.encode d (csPkH₁ pkVal), F.encode d (csPkH₂ pkVal))
        m ad (b : ZMod (F.order d)).val := by
  simp only [skNatOfZMod, encodeProjHashAux_encode, ZMod.natCast_zmod_val,
    csPkU, csPkH, csPkH₁, csPkH₂, csSkS, csSkT, csSkS₁, csSkT₁, csSkS₂, csSkT₂,
    cramerShoupPublicKey, projHash2Aux, encodeCramerShoupEncrypt, F.smul_encode, F.add_encode]


end Cslib.Crypto.PrimeOrderGroupFamily
