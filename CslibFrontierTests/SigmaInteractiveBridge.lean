/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SchnorrProtocol
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Interactive
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.PPT

/-!
# Tests for the `SigmaProtocol` → `Interactive.Reduction` bridge

Exercises `CslibFrontier.Crypto.Protocols.SigmaProtocol.Interactive` on:

* `SigmaProtocol.schnorr`: completeness, round-by-round soundness, plain-model soundness,
  straight-line knowledge soundness, and perfect HVZK.
* `PrimeOrderGroupFamily.schnorrFamily`: `Interactive.Reduction.EfficientHVZK` with simulation
  error `0` and realization error `1 / 2 ^ n + 1 / 2 ^ n`.
* `SigmaProtocol.andProof`: completeness, round-by-round soundness, soundness, knowledge soundness,
  and perfect HVZK for the AND composition of two Sigma protocols.
* `SigmaProtocol.orProof`: completeness, round-by-round soundness, soundness, knowledge soundness,
  and perfect HVZK for the OR composition of two Sigma protocols.
-/

@[expose] public section

namespace CslibFrontierTests.SigmaInteractiveBridge

open Cslib Cslib.Probability Cslib.Interactive Cslib.Interactive.Spec
open Cslib.Crypto Cslib.Crypto.Protocols Cslib.Crypto.Protocols.SigmaProtocol
open Turing.MultiTapeTM
open scoped ENNReal NNReal

/-! ### Schnorr Sigma protocol as an interactive reduction -/

section Schnorr

variable {q : ℕ} [NeZero q] {G C : Type} [AddCommGroup G] [Module (ZMod q) G] [DecidableEq G]
  [Fintype C] [Nonempty C] (ι : C ↪ ZMod q) (g : G)

/-- Schnorr's interactive reduction is perfectly complete in the plain model. -/
theorem schnorr_interactive_complete :
    ((schnorr ι g).toInteractiveReduction (schnorrCommit g)).Complete
      World.plain (fun u α => α • g = u) Accept 0 :=
  schnorr_complete.toInteractiveReduction (commitRealizedBy_schnorr ι g)

/-- Schnorr's interactive verifier is round-by-round sound with challenge error `1 / |C|`. -/
theorem schnorr_interactive_rbrSound [Fact q.Prime] :
    (schnorr ι g).toInteractiveVerifier.RbrSound
      (language fun u (α : ZMod q) => α • g = u) Set.univ
      (1 / (Fintype.card C : ℝ≥0∞), ()) :=
  SpecialSoundness.rbrSound (schnorr_specialSoundness (ι := ι) (g := g))

/-- Schnorr's interactive verifier is sound in the plain model with error `1 / |C|`. -/
theorem schnorr_interactive_sound [Fact q.Prime] :
    (schnorr ι g).toInteractiveVerifier.Sound World.plain
      (language fun u (α : ZMod q) => α • g = u) Set.univ
      (1 / (Fintype.card C : ℝ≥0∞)) :=
  SpecialSoundness.sound (schnorr_specialSoundness (ι := ι) (g := g))

/-- Schnorr's interactive verifier is knowledge sound with error `1 / |C|`. -/
theorem schnorr_interactive_knowledgeSound [Fact q.Prime] :
    (schnorr ι g).toInteractiveVerifier.KnowledgeSound
      (fun u (α : ZMod q) => α • g = u) Accept
      ((schnorr ι g).witnessChooser fun α u => α • g = u)
      (1 / (Fintype.card C : ℝ≥0∞)) :=
  SpecialSoundness.knowledgeSound (schnorr_specialSoundness (ι := ι) (g := g))

/-- Schnorr's interactive reduction is perfectly HVZK in the plain model. -/
theorem schnorr_interactive_hvzk :
    ((schnorr ι g).toInteractiveReduction (schnorrCommit g)).HVZK
      (fun u α => α • g = u)
      ((schnorr ι g).interactiveSim (schnorrSimComp ι g)) 0 :=
  (schnorr_specialHVZK (ι := ι) (g := g)).hvzk_zero
    (commitRealizedBy_schnorr ι g) (eval_schnorrSimComp ι g)

end Schnorr

/-! ### Schnorr family: `EfficientSpecialHVZK` → `Interactive.Reduction.EfficientHVZK` -/

section SchnorrFamily

variable (F : PrimeOrderGroupFamily)

/-- Typed challenge sampler for `F.schnorrFamily`: sample `s ← F.sampleExp n d` and reduce modulo
`F.order d`. -/
noncomputable def schnorrSampleChallenge (i : ℕ × F.Desc) : ProbComp (ZMod (F.order i.2)) :=
  (Nat.cast : ℕ → ZMod (F.order i.2)) <$> F.sampleExp i.1 i.2

/-- One machine samples the encoded challenges of `schnorrSampleChallenge` from the encoded index:
it samples `s ← F.sampleExp n d` and writes the binary encoding of `s mod q`. -/
theorem isPPTOn_schnorrSampleChallenge :
    IsPPTOn (encPair encUnary F.encDesc) encBits
      fun i => F.schnorrEncoding.challenge i <$> schnorrSampleChallenge F i := by
  let encIdx := encPair encUnary F.encDesc
  have hn : ComputableInPolyTime (fun i : ℕ × F.Desc => i.1) encIdx encUnary := by fun_prop
  have hd : ComputableInPolyTime (fun i : ℕ × F.Desc => i.2) encIdx F.encDesc := by fun_prop
  have hword : IsPPTOn encIdx encBits fun i => F.sampleExp i.1 i.2 >>= fun s =>
      pure (s % F.order i.2).bits := by
    refine (F.isPPTOn_sampleExp hn hd).bind_with ?_
    let encMid := encPair encIdx encNat
    have hd' : ComputableInPolyTime (fun p : (ℕ × F.Desc) × ℕ => p.1.2) encMid F.encDesc := by
      fun_prop
    have hs : ComputableInPolyTime (fun p : (ℕ × F.Desc) × ℕ => p.2) encMid encNat := by
      fun_prop
    have hq := F.computableInPolyTime_order.comp hd'
    have hz : ComputableInPolyTime (fun p : (ℕ × F.Desc) × ℕ => (p.2 % F.order p.1.2).bits)
        encMid encBits :=
      .of_tidy (ComputableTidilyInPolyTime.natBits.comp (.binary_mod' hs.tidy hq.tidy))
    exact hz.isPPTOn
  refine hword.congr fun i => ?_
  rw [schnorrSampleChallenge, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_map,
    PMF.map_comp]
  simp only [ProbComp.eval_pure]
  rw [← PMF.bind_pure_comp]
  congr 1 with s : 1
  simp only [Function.comp_apply, PrimeOrderGroupFamily.schnorrEncoding,
    PrimeOrderGroupFamily.encScalar, Function.Embedding.coeFn_mk, encNat_apply,
    ZMod.val_natCast]

theorem closeTo_schnorrSampleChallenge (i : ℕ × F.Desc) :
    CloseTo (PMF.uniformOfFintype (ZMod (F.order i.2)))
      (ProbComp.eval (schnorrSampleChallenge F i)) (1 / 2 ^ i.1) := by
  have hδ : (((1 / 2 ^ i.1 : ℝ≥0)) : ℝ≥0∞) = 1 / 2 ^ i.1 := by
    rw [ENNReal.coe_div (pow_ne_zero _ two_ne_zero), ENNReal.coe_one, ENNReal.coe_pow,
      ENNReal.coe_ofNat]
  rw [schnorrSampleChallenge, ProbComp.eval_map, ← hδ]
  exact F.closeTo_uniform_sampleExp i.1 i.2

/-- **Schnorr's interactive reduction family is `EfficientHVZK`** with simulation error `0` and
realization error `1 / 2 ^ n + 1 / 2 ^ n`. -/
theorem schnorrFamily_interactive_efficientHVZK :
    Interactive.Reduction.EfficientHVZK
      (fun i => (F.schnorrFamily i).toInteractiveReduction
        (schnorrCommit (F.generator i.2)))
      (fun i u α => α • F.generator i.2 = u)
      (F.schnorrEncoding.toInteractiveEncoding F.schnorrFamily)
      (fun i => (F.schnorrFamily i).interactiveSim
        (schnorrSimComp (Function.Embedding.refl _) (F.generator i.2)))
      (fun _ => 0) (fun i => 1 / 2 ^ i.1 + 1 / 2 ^ i.1) :=
  F.efficientSpecialHVZK_schnorr.efficientHVZK F.schnorrFamily
    (fun i => commitRealizedBy_schnorr (Function.Embedding.refl _) (F.generator i.2))
    (fun i => eval_schnorrSimComp (Function.Embedding.refl _) (F.generator i.2))
    (isPPTOn_schnorrSampleChallenge F)
    (closeTo_schnorrSampleChallenge F)

end SchnorrFamily

/-! ### AND composition through the interactive bridge -/

section And

variable {X₀ Y₀ T₀ Z₀ X₁ Y₁ T₁ Z₁ C : Type} [Fintype C] [Nonempty C]
  {P₀ : SigmaProtocol X₀ Y₀ T₀ C Z₀} {P₁ : SigmaProtocol X₁ Y₁ T₁ C Z₁}
  {R₀ : X₀ → Y₀ → Prop} {R₁ : X₁ → Y₁ → Prop}

theorem andProof_interactive_complete
    {sample₀ : X₀ → Y₀ → ProbComp (T₀ × P₀.State)}
    {sample₁ : X₁ → Y₁ → ProbComp (T₁ × P₁.State)}
    (h₀ : P₀.Complete R₀) (h₁ : P₁.Complete R₁)
    (hc₀ : P₀.CommitRealizedBy sample₀) (hc₁ : P₁.CommitRealizedBy sample₁) :
    ((P₀.andProof P₁).toInteractiveReduction (andCommit sample₀ sample₁)).Complete
      World.plain (fun y x => R₀ x.1 y.1 ∧ R₁ x.2 y.2) Accept 0 :=
  (andProof_complete h₀ h₁).toInteractiveReduction (commitRealizedBy_andProof hc₀ hc₁)

theorem andProof_interactive_rbrSound
    {extract₀ : Y₀ → T₀ → C → Z₀ → C → Z₀ → X₀}
    {extract₁ : Y₁ → T₁ → C → Z₁ → C → Z₁ → X₁}
    (h₀ : P₀.SpecialSoundness R₀ extract₀) (h₁ : P₁.SpecialSoundness R₁ extract₁) :
    (P₀.andProof P₁).toInteractiveVerifier.RbrSound
      (language fun (y : Y₀ × Y₁) (x : X₀ × X₁) => R₀ x.1 y.1 ∧ R₁ x.2 y.2) Set.univ
      (1 / (Fintype.card C : ℝ≥0∞), ()) :=
  SpecialSoundness.rbrSound (andProof_specialSoundness h₀ h₁)

theorem andProof_interactive_sound
    {extract₀ : Y₀ → T₀ → C → Z₀ → C → Z₀ → X₀}
    {extract₁ : Y₁ → T₁ → C → Z₁ → C → Z₁ → X₁}
    (h₀ : P₀.SpecialSoundness R₀ extract₀) (h₁ : P₁.SpecialSoundness R₁ extract₁) :
    (P₀.andProof P₁).toInteractiveVerifier.Sound World.plain
      (language fun (y : Y₀ × Y₁) (x : X₀ × X₁) => R₀ x.1 y.1 ∧ R₁ x.2 y.2) Set.univ
      (1 / (Fintype.card C : ℝ≥0∞)) :=
  SpecialSoundness.sound (andProof_specialSoundness h₀ h₁)

theorem andProof_interactive_knowledgeSound [Nonempty X₀] [Nonempty X₁]
    {extract₀ : Y₀ → T₀ → C → Z₀ → C → Z₀ → X₀}
    {extract₁ : Y₁ → T₁ → C → Z₁ → C → Z₁ → X₁}
    (h₀ : P₀.SpecialSoundness R₀ extract₀) (h₁ : P₁.SpecialSoundness R₁ extract₁) :
    (P₀.andProof P₁).toInteractiveVerifier.KnowledgeSound
      (fun (y : Y₀ × Y₁) (x : X₀ × X₁) => R₀ x.1 y.1 ∧ R₁ x.2 y.2) Accept
      ((P₀.andProof P₁).witnessChooser fun (x : X₀ × X₁) (y : Y₀ × Y₁) => R₀ x.1 y.1 ∧ R₁ x.2 y.2)
      (1 / (Fintype.card C : ℝ≥0∞)) :=
  SpecialSoundness.knowledgeSound (andProof_specialSoundness h₀ h₁)

theorem andProof_interactive_hvzk
    {simulate₀ : Y₀ → C → PMF (T₀ × Z₀)} {simulate₁ : Y₁ → C → PMF (T₁ × Z₁)}
    {sample₀ : X₀ → Y₀ → ProbComp (T₀ × P₀.State)}
    {sample₁ : X₁ → Y₁ → ProbComp (T₁ × P₁.State)}
    {sim₀ : Y₀ → C → ProbComp (T₀ × Z₀)} {sim₁ : Y₁ → C → ProbComp (T₁ × Z₁)}
    (h₀ : P₀.SpecialHVZK R₀ simulate₀) (h₁ : P₁.SpecialHVZK R₁ simulate₁)
    (hc₀ : P₀.CommitRealizedBy sample₀) (hc₁ : P₁.CommitRealizedBy sample₁)
    (hs₀ : ∀ y c, ProbComp.eval (sim₀ y c) = simulate₀ y c)
    (hs₁ : ∀ y c, ProbComp.eval (sim₁ y c) = simulate₁ y c) :
    ((P₀.andProof P₁).toInteractiveReduction (andCommit sample₀ sample₁)).HVZK
      (fun y x => R₀ x.1 y.1 ∧ R₁ x.2 y.2)
      ((P₀.andProof P₁).interactiveSim (andSimComp sim₀ sim₁)) 0 :=
  (andProof_specialHVZK h₀ h₁).hvzk_zero
    (commitRealizedBy_andProof hc₀ hc₁) (eval_andSimComp hs₀ hs₁)

end And

/-! ### OR composition through the interactive bridge -/

section Or

variable {X₀ Y₀ T₀ Z₀ X₁ Y₁ T₁ Z₁ C : Type} [AddCommGroup C] [Fintype C] [Nonempty C]
  {P₀ : SigmaProtocol X₀ Y₀ T₀ C Z₀} {P₁ : SigmaProtocol X₁ Y₁ T₁ C Z₁}
  {R₀ : X₀ → Y₀ → Prop} {R₁ : X₁ → Y₁ → Prop}
  {simulate₀ : Y₀ → C → PMF (T₀ × Z₀)} {simulate₁ : Y₁ → C → PMF (T₁ × Z₁)}

theorem orProof_interactive_complete
    {sample₀ : X₀ → Y₀ → ProbComp (T₀ × P₀.State)}
    {sample₁ : X₁ → Y₁ → ProbComp (T₁ × P₁.State)}
    {sim₀ : Y₀ → C → ProbComp (T₀ × Z₀)} {sim₁ : Y₁ → C → ProbComp (T₁ × Z₁)}
    (h₀ : P₀.Complete R₀) (h₁ : P₁.Complete R₁)
    (hzk₀ : P₀.SpecialHVZK R₀ simulate₀) (hzk₁ : P₁.SpecialHVZK R₁ simulate₁)
    (hc₀ : P₀.CommitRealizedBy sample₀) (hc₁ : P₁.CommitRealizedBy sample₁)
    (hs₀ : ∀ y c, ProbComp.eval (sim₀ y c) = simulate₀ y c)
    (hs₁ : ∀ y c, ProbComp.eval (sim₁ y c) = simulate₁ y c) :
    ((orProof P₀ P₁ simulate₀ simulate₁).toInteractiveReduction
      (orCommit sample₀ sample₁ sim₀ sim₁)).Complete
      World.plain (Function.swap (orRelation R₀ R₁)) Accept 0 :=
  (orProof_complete h₀ h₁ hzk₀ hzk₁).toInteractiveReduction
    (commitRealizedBy_orProof hc₀ hc₁ hs₀ hs₁)

theorem orProof_interactive_rbrSound
    {extract₀ : Y₀ → T₀ → C → Z₀ → C → Z₀ → X₀}
    {extract₁ : Y₁ → T₁ → C → Z₁ → C → Z₁ → X₁}
    (h₀ : P₀.SpecialSoundness R₀ extract₀) (h₁ : P₁.SpecialSoundness R₁ extract₁) :
    (orProof P₀ P₁ simulate₀ simulate₁).toInteractiveVerifier.RbrSound
      (language (Function.swap (orRelation R₀ R₁))) Set.univ
      (1 / (Fintype.card C : ℝ≥0∞), ()) := by
  classical
  exact SpecialSoundness.rbrSound
    (orProof_specialSoundness (simulate₀ := simulate₀) (simulate₁ := simulate₁) h₀ h₁)

theorem orProof_interactive_sound
    {extract₀ : Y₀ → T₀ → C → Z₀ → C → Z₀ → X₀}
    {extract₁ : Y₁ → T₁ → C → Z₁ → C → Z₁ → X₁}
    (h₀ : P₀.SpecialSoundness R₀ extract₀) (h₁ : P₁.SpecialSoundness R₁ extract₁) :
    (orProof P₀ P₁ simulate₀ simulate₁).toInteractiveVerifier.Sound World.plain
      (language (Function.swap (orRelation R₀ R₁))) Set.univ
      (1 / (Fintype.card C : ℝ≥0∞)) := by
  classical
  exact SpecialSoundness.sound
    (orProof_specialSoundness (simulate₀ := simulate₀) (simulate₁ := simulate₁) h₀ h₁)

theorem orProof_interactive_knowledgeSound [Nonempty (X₀ ⊕ X₁)]
    {extract₀ : Y₀ → T₀ → C → Z₀ → C → Z₀ → X₀}
    {extract₁ : Y₁ → T₁ → C → Z₁ → C → Z₁ → X₁}
    (h₀ : P₀.SpecialSoundness R₀ extract₀) (h₁ : P₁.SpecialSoundness R₁ extract₁) :
    (orProof P₀ P₁ simulate₀ simulate₁).toInteractiveVerifier.KnowledgeSound
      (Function.swap (orRelation R₀ R₁)) Accept
      ((orProof P₀ P₁ simulate₀ simulate₁).witnessChooser (orRelation R₀ R₁))
      (1 / (Fintype.card C : ℝ≥0∞)) := by
  classical
  exact SpecialSoundness.knowledgeSound
    (orProof_specialSoundness (simulate₀ := simulate₀) (simulate₁ := simulate₁) h₀ h₁)

theorem orProof_interactive_hvzk
    {sample₀ : X₀ → Y₀ → ProbComp (T₀ × P₀.State)}
    {sample₁ : X₁ → Y₁ → ProbComp (T₁ × P₁.State)}
    {sim₀ : Y₀ → C → ProbComp (T₀ × Z₀)} {sim₁ : Y₁ → C → ProbComp (T₁ × Z₁)}
    (hzk₀ : P₀.SpecialHVZK R₀ simulate₀) (hzk₁ : P₁.SpecialHVZK R₁ simulate₁)
    (hc₀ : P₀.CommitRealizedBy sample₀) (hc₁ : P₁.CommitRealizedBy sample₁)
    (hs₀ : ∀ y c, ProbComp.eval (sim₀ y c) = simulate₀ y c)
    (hs₁ : ∀ y c, ProbComp.eval (sim₁ y c) = simulate₁ y c) :
    ((orProof P₀ P₁ simulate₀ simulate₁).toInteractiveReduction
      (orCommit sample₀ sample₁ sim₀ sim₁)).HVZK
      (Function.swap (orRelation R₀ R₁))
      ((orProof P₀ P₁ simulate₀ simulate₁).interactiveSim (orSimComp sim₀ sim₁)) 0 :=
  (orProof_specialHVZK hzk₀ hzk₁).hvzk_zero
    (commitRealizedBy_orProof hc₀ hc₁ hs₀ hs₁) (eval_orSimComp hs₀ hs₁)

end Or

end CslibFrontierTests.SigmaInteractiveBridge
