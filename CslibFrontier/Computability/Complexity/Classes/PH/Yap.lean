/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP.Advice
public import CslibFrontier.Computability.Complexity.Classes.PH.Closure
public import CslibFrontier.Computability.Complexity.Classes.PH.Reduction
public import CslibFrontier.Computability.Complexity.Problems.SAT
import CslibFrontier.Computability.Complexity.Classes.PH.Projection
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Yap's theorem (`coNP ⊆ NP/poly ⇒ PH = Σ₃`)

If `coNP ⊆ NP/poly` (equivalently `NP ⊆ coNP/poly`, or `UNSAT ∈ NP/poly`), the polynomial hierarchy
collapses to its third level: `PH = Σ₃`, and in fact `PH = Σ₃ ∩ Π₃` [Yap][Yap1983],
[Bodlaender, Jansen and Kratsch, Theorem 2][BodlaenderJansenKratsch2014].

## Proof overview

First, `coNP ⊆ NP/poly` already places `Σ₂` in `NP/poly`
(`Cslib.Complexity.SigmaP_two_subset_NPPoly_of_coNP_subset_NPPoly`) and `Π₂` in `coNP/poly`: a
problem in `Σ₂` projects a `Π₁ = coNP` predicate along words `u` of a fixed polynomial length
`p |enc a|`, so all pairs `(a, u)` share the same encoded length `2 |enc a| + 1 + p |enc a|` and
can share one advice string, while the quantifier over `u` merges with the `NP` certificate.

To collapse the hierarchy at level `3`, it suffices to show `Π₃ ⊆ Σ₃`
(`Cslib.Complexity.PiP_three_subset_SigmaP_three_of_coNP_subset_NPPoly`). Let `A ∈ Π₃` have blocks
of lengths `p₁`, `p₂`, `p₃`. Negating the innermost universal block gives `E ∈ NP` on pairs such
that `a ∈ A ↔ ∀ u₁ (|u₁| = p₁ n), ∃ u₂ (|u₂| = p₂ n), (a, u₁ ++ u₂) ∉ E`, where every queried word
`s = u₁ ++ u₂` has fixed length `m n = p₁ n + p₂ n` and every pair `(a, s)` has fixed encoded
length `M n = 2 n + 1 + m n`. Since `Eᶜ ∈ coNP ⊆ NP/poly`, there are polynomially bounded advice
`adv` and a problem `B ∈ NP` with `(a, s) ∉ E ↔ (adv (M n), (a, s)) ∈ B` whenever `|s| = m n`.

A `Σ₃` verifier for `A` guesses a framed advice string `w` in its first existential block and
checks two conditions on `(a, w)`:

* **Soundness** (`Π₁ ⊆ Π₂`): no word `s` of length `m n` satisfies both `(unframe w, (a, s)) ∈ B`
  and `(a, s) ∈ E`. Because both `B` and `E` lie in `NP`, the existence of a counterexample `s` is
  in `NP`, so soundness is in `coNP = Π₁`.
* **Completeness on `a`** (`Π₂`): for every `u₁` of length `p₁ n`, there is `u₂` of length `p₂ n`
  with `(unframe w, (a, u₁ ++ u₂)) ∈ B`. Because `B ∈ NP`, the inner check `∃ u₂, … ∈ B` stays in
  `NP = Σ₁ ⊆ Π₂`, and universal quantification over `u₁` keeps it in `Π₂`.

Intersecting the two `Π₂` conditions (`Cslib.Complexity.inter_mem_PiP`) and existentially
quantifying `w` (`Cslib.Complexity.mem_SigmaP_of_exists`) places `A` in `Σ₃`. Any sound advice
string accepted by the main check forces `(a, u₁ ++ u₂) ∉ E` for every `u₁`, while the true framed
advice `frame (adv (M n))` is both sound and complete.

Through `Cslib.Complexity.CookLevin.UNSAT_coNPComplete` and `Cslib.Complexity.cnfDecoder`, the
hypotheses `UNSAT ∈ NPPoly encCNF`, `SAT ∈ coNPPoly encCNF`, `coNP encBits ⊆ NPPoly encBits`,
`NP encBits ⊆ coNPPoly encBits`, and `∀ encB, coNP encB ⊆ NPPoly encB` are all equivalent.

## Main results

* `Cslib.Complexity.SigmaP_two_subset_NPPoly_of_coNP_subset_NPPoly`,
  `Cslib.Complexity.PiP_two_subset_coNPPoly_of_coNP_subset_NPPoly`: `coNP ⊆ NP/poly` gives
  `Σ₂ ⊆ NP/poly` and `Π₂ ⊆ coNP/poly`.
* `Cslib.Complexity.PiP_three_subset_SigmaP_three_of_coNP_subset_NPPoly`,
  `Cslib.Complexity.PiP_three_eq_SigmaP_three_of_coNP_subset_NPPoly`: `coNP ⊆ NP/poly` gives
  `Π₃ ⊆ Σ₃` and `Π₃ = Σ₃`.
* `Cslib.Complexity.UNSAT_mem_NPPoly_iff_forall_coNP_subset_NPPoly`,
  `Cslib.Complexity.coNP_encBits_subset_NPPoly_iff_UNSAT`,
  `Cslib.Complexity.coNP_encBits_subset_NPPoly_iff`,
  `Cslib.Complexity.NP_encBits_subset_coNPPoly_iff`: equivalence of the nonuniform hypotheses.
* `Cslib.Complexity.PH_eq_SigmaP_three_of_coNP_subset_NPPoly`,
  `Cslib.Complexity.PH_eq_SigmaP_three_of_NP_subset_coNPPoly`,
  `Cslib.Complexity.PH_eq_SigmaP_three_of_coNP_encBits_subset_NPPoly`,
  `Cslib.Complexity.PH_eq_SigmaP_three_of_NP_encBits_subset_coNPPoly`,
  `Cslib.Complexity.PH_eq_SigmaP_three_of_UNSAT_mem_NPPoly`,
  `Cslib.Complexity.PH_eq_SigmaP_three_of_SAT_mem_coNPPoly`,
  `Cslib.Complexity.PH_eq_SigmaP_three_inter_PiP_three_of_coNP_subset_NPPoly`: **Yap's theorem**.

## References

* [C.-K. Yap, *Some consequences of non-uniform conditions on uniform classes*][Yap1983]
* [H. L. Bodlaender, B. M. P. Jansen, S. Kratsch, *Kernelization lower bounds by
  cross-composition*][BodlaenderJansenKratsch2014]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool}

/-! ### `Σ₂ ⊆ NP/poly` -/

/-- **`coNP ⊆ NP/poly` gives `Σ₂ ⊆ NP/poly`** [Yap][Yap1983]: a problem in `Σ₂` is the projection
of a `Π₁ = coNP` problem along words `u` of fixed polynomial length `p |enc a|`, so all pairs
`(a, u)` share one advice length `2 |enc a| + 1 + p |enc a|` and `∃ u` merges with the `NP`
certificate. -/
theorem SigmaP_two_subset_NPPoly_of_coNP_subset_NPPoly
    (h : coNP (encPair enc encBits) ⊆ NPPoly (encPair enc encBits)) :
    SigmaP 2 enc ⊆ NPPoly enc := by
  intro A hA
  obtain ⟨p, C, hC, hAC⟩ := exists_mem_PiP_of_mem_SigmaP_succ hA
  rw [PiP_one_eq_coNP] at hC
  obtain ⟨adv, hadv, B, hB, hCB⟩ := h hC
  let M : Polynomial ℕ := 2 * Polynomial.X + 1 + p
  have hlen (a : α) (u : List Bool) (hu : u.length = p.eval (enc a).length) :
      (encPair enc encBits (a, u)).length = M.eval (enc a).length := by
    simp only [length_encPair, encBits_apply, hu, M, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  let B' : Set ((List Bool × α) × List Bool) := {x | (x.1.1, (x.1.2, x.2)) ∈ B}
  have hred : PolyTimeReducible (encPair (encPair encBits enc) encBits)
      (encPair encBits (encPair enc encBits)) B' B :=
    ⟨fun x => (x.1.1, (x.1.2, x.2)),
      (fst _ _).fst'.prod ((fst _ _).snd'.prod (snd _ _)), fun _ => Iff.rfl⟩
  have hN : ComputableInPolyTime (fun y : List Bool × α => p.eval (enc y.2).length)
      (encPair encBits enc) encUnary :=
    (unary_eval p).comp ((encoding_length enc).comp (snd encBits enc))
  have hNP : {y : List Bool × α | ∃ u : List Bool,
      u.length = p.eval (enc y.2).length ∧ (y, u) ∈ B'} ∈ NP (encPair encBits enc) := by
    rw [← SigmaP_one]
    exact mem_SigmaP_of_exists_length le_rfl hN (SigmaP_one ▸ hred.mem_NP hB)
  refine ⟨fun n => adv (M.eval n), hadv.comp (PolynomiallyBounded.polynomial_eval M),
    _, hNP, fun a => ?_⟩
  rw [hAC a]
  refine exists_congr fun u => and_congr_right fun hu => ?_
  rw [hCB (a, u), hlen a u hu]
  rfl

/-- **`coNP ⊆ NP/poly` gives `Π₂ ⊆ coNP/poly`** [Yap][Yap1983], by complementation from
`Cslib.Complexity.SigmaP_two_subset_NPPoly_of_coNP_subset_NPPoly`. -/
theorem PiP_two_subset_coNPPoly_of_coNP_subset_NPPoly
    (h : coNP (encPair enc encBits) ⊆ NPPoly (encPair enc encBits)) :
    PiP 2 enc ⊆ coNPPoly enc :=
  fun _ hA => SigmaP_two_subset_NPPoly_of_coNP_subset_NPPoly h (compl_mem_SigmaP_of_mem_PiP hA)

/-! ### `Π₃ ⊆ Σ₃` -/

/-- **Yap's theorem at level `3`** [Yap][Yap1983]: if `coNP ⊆ NP/poly` holds for the pair encoding
`encPair enc encBits`, then `PiP 3 enc ⊆ SigmaP 3 enc`. -/
theorem PiP_three_subset_SigmaP_three_of_coNP_subset_NPPoly
    (h : coNP (encPair enc encBits) ⊆ NPPoly (encPair enc encBits)) :
    PiP 3 enc ⊆ SigmaP 3 enc := by
  rintro A ⟨ps, V, hps, hV, hAV⟩
  rcases ps with _ | ⟨p₁, _ | ⟨p₂, _ | ⟨p₃, _ | _⟩⟩⟩ <;> try cases hps
  let E : Set (α × List Bool) :=
    {y | ∃ u₃ : List Bool, u₃.length = p₃.eval (enc y.1).length ∧ (!V (y.1, y.2 ++ u₃)) = true}
  have hE : E ∈ NP (encPair enc encBits) :=
    mem_NP_setOf_exists_append (V := fun x => !V x) (bool_not.comp hV) p₃
  obtain ⟨adv, hadv, B, hB, hEB⟩ :=
    h (show Eᶜ ∈ coNP (encPair enc encBits) by rwa [mem_coNP, compl_compl])
  let m : Polynomial ℕ := p₁ + p₂
  let M : Polynomial ℕ := 2 * Polynomial.X + 1 + m
  have hlen (a : α) (s : List Bool) (hs : s.length = m.eval (enc a).length) :
      (encPair enc encBits (a, s)).length = M.eval (enc a).length := by
    simp only [length_encPair, encBits_apply, hs, M, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  obtain ⟨K, hK⟩ := (PolyBounded.of_polynomiallyBounded id
    (hadv.comp (PolynomiallyBounded.polynomial_eval M))).exists_polynomial
  let W : Polynomial ℕ := 2 * K + 1
  -- Soundness: `unframe w` never accepts a word of length `m` belonging to `E`
  let BadPair : Set ((α × List Bool) × List Bool) :=
    {z | (unframe z.1.2, (z.1.1, z.2)) ∈ B ∧ (z.1.1, z.2) ∈ E}
  have hBadB : PolyTimeReducible (encPair (encPair enc encBits) encBits)
      (encPair encBits (encPair enc encBits))
      {z : (α × List Bool) × List Bool | (unframe z.1.2, (z.1.1, z.2)) ∈ B} B :=
    ⟨fun z => (unframe z.1.2, (z.1.1, z.2)),
      (unframe.comp (fst _ _).snd').prod ((fst _ _).fst'.prod (snd _ _)), fun _ => Iff.rfl⟩
  have hBadE : PolyTimeReducible (encPair (encPair enc encBits) encBits) (encPair enc encBits)
      {z : (α × List Bool) × List Bool | (z.1.1, z.2) ∈ E} E :=
    ⟨fun z => (z.1.1, z.2), (fst _ _).fst'.prod (snd _ _), fun _ => Iff.rfl⟩
  have hBadPair : BadPair ∈ SigmaP 1 (encPair (encPair enc encBits) encBits) :=
    inter_mem_SigmaP (SigmaP_one ▸ hBadB.mem_NP hB) (SigmaP_one ▸ hBadE.mem_NP hE)
  have hNm : ComputableInPolyTime (fun x : α × List Bool => m.eval (enc x.1).length)
      (encPair enc encBits) encUnary :=
    (unary_eval m).comp ((encoding_length enc).comp (fst enc encBits))
  let SoundSet : Set (α × List Bool) :=
    {x | ∀ s : List Bool, s.length = m.eval (enc x.1).length → (x, s) ∈ BadPairᶜ}
  have hSoundSet : SoundSet ∈ PiP 2 (encPair enc encBits) :=
    PiP_subset_PiP_succ 1
      (mem_PiP_of_forall_length le_rfl hNm (compl_mem_PiP_of_mem_SigmaP hBadPair))
  -- Main check: for every `u₁`, some `u₂` has `(unframe w, (a, u₁ ++ u₂)) ∈ B`
  have hNp₂ : ComputableInPolyTime
      (fun y : (α × List Bool) × List Bool => p₂.eval (enc y.1.1).length)
      (encPair (encPair enc encBits) encBits) encUnary :=
    (unary_eval p₂).comp ((encoding_length enc).comp (fst _ _).fst')
  have hNp₁ : ComputableInPolyTime (fun x : α × List Bool => p₁.eval (enc x.1).length)
      (encPair enc encBits) encUnary :=
    (unary_eval p₁).comp ((encoding_length enc).comp (fst enc encBits))
  let InnerSet : Set ((α × List Bool) × List Bool) :=
    {y | ∃ u₂ : List Bool, u₂.length = p₂.eval (enc y.1.1).length ∧
      (y.1, y.2 ++ u₂) ∈ {z : (α × List Bool) × List Bool | (unframe z.1.2, (z.1.1, z.2)) ∈ B}}
  have hInner : InnerSet ∈ PiP 2 (encPair (encPair enc encBits) encBits) :=
    SigmaP_subset_PiP_succ 1
      (mem_SigmaP_of_exists_append le_rfl hNp₂ (SigmaP_one ▸ hBadB.mem_NP hB))
  let MainSet : Set (α × List Bool) :=
    {x | ∀ u₁ : List Bool, u₁.length = p₁.eval (enc x.1).length → (x, u₁) ∈ InnerSet}
  have hMainSet : MainSet ∈ PiP 2 (encPair enc encBits) :=
    mem_PiP_of_forall_length (by decide) hNp₁ hInner
  -- Combine soundness and main check, then quantify existentially over `w`
  have hTarget : {a | ∃ w : List Bool, w.length = W.eval (enc a).length ∧
      (a, w) ∈ SoundSet ∩ MainSet} ∈ SigmaP 3 enc :=
    mem_SigmaP_of_exists (by decide)
      (PiP_subset_SigmaP_succ 2 (inter_mem_PiP hSoundSet hMainSet)) W
  convert hTarget using 1
  ext a
  have hA_iff : a ∈ A ↔ ∀ u₁ : List Bool, u₁.length = p₁.eval (enc a).length →
      ∃ u₂ : List Bool, u₂.length = p₂.eval (enc a).length ∧ (a, u₁ ++ u₂) ∉ E := by
    rw [hAV a]
    simp only [List.map_cons, List.map_nil,
      alternation_false_cons, alternation_true_cons, alternation_nil]
    refine forall_congr' fun u₁ => imp_congr_right fun _ => ?_
    refine exists_congr fun u₂ => and_congr_right fun _ => ?_
    simp [E, List.append_assoc]
  rw [hA_iff]
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · intro ha
    have hK' : (adv (M.eval (enc a).length)).length ≤ K.eval (enc a).length := hK (enc a).length
    have hframe_le : (frame (adv (M.eval (enc a).length))).length ≤ W.eval (enc a).length := by
      simp only [length_frame, W, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_ofNat, Polynomial.eval_one]
      omega
    let w := frame (adv (M.eval (enc a).length)) ++
      List.replicate (W.eval (enc a).length - (frame (adv (M.eval (enc a).length))).length) false
    have hw : w.length = W.eval (enc a).length := by
      rw [List.length_append, List.length_replicate, Nat.add_sub_cancel' hframe_le]
    have hunf : unframe w = adv (M.eval (enc a).length) := unframe_frame_append _ _
    refine ⟨w, hw, fun s hs ⟨hBs, hEs⟩ => ?_, fun u₁ hu₁ => ?_⟩
    · dsimp only at hs hBs hEs
      rw [hunf, ← hlen a s hs] at hBs
      exact (hEB (a, s)).2 hBs hEs
    · dsimp only at hu₁
      obtain ⟨u₂, hu₂, hnotE⟩ := ha u₁ hu₁
      have hs : (u₁ ++ u₂).length = m.eval (enc a).length := by simp [m, hu₁, hu₂]
      refine ⟨u₂, hu₂, ?_⟩
      dsimp only [Set.mem_ofPred_eq]
      rw [hunf, ← hlen a (u₁ ++ u₂) hs]
      exact (hEB (a, u₁ ++ u₂)).1 hnotE
  · rintro ⟨w, -, hSound, hMain⟩ u₁ hu₁
    obtain ⟨u₂, hu₂, hBu⟩ := hMain u₁ hu₁
    have hs : (u₁ ++ u₂).length = m.eval (enc a).length := by simp [m, hu₁, hu₂]
    exact ⟨u₂, hu₂, fun hEu => hSound (u₁ ++ u₂) hs ⟨hBu, hEu⟩⟩

/-- **Yap's theorem at level `3`** [Yap][Yap1983]: if `coNP ⊆ NP/poly` holds for the pair encoding
`encPair enc encBits`, then `PiP 3 enc = SigmaP 3 enc`. -/
theorem PiP_three_eq_SigmaP_three_of_coNP_subset_NPPoly
    (h : coNP (encPair enc encBits) ⊆ NPPoly (encPair enc encBits)) :
    PiP 3 enc = SigmaP 3 enc :=
  PiP_eq_SigmaP_of_PiP_subset_SigmaP (PiP_three_subset_SigmaP_three_of_coNP_subset_NPPoly h)

/-! ### Equivalence of nonuniform hypotheses -/

/-- **`UNSAT ∈ NP/poly` is equivalent to `coNP ⊆ NP/poly` across all encodings**, through
`Cslib.Complexity.CookLevin.UNSAT_coNPComplete`. -/
theorem UNSAT_mem_NPPoly_iff_forall_coNP_subset_NPPoly :
    UNSAT ∈ NPPoly encCNF ↔ ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ NPPoly encB :=
  ⟨fun h _ encB => coNP_subset_NPPoly_of_coNPComplete CookLevin.UNSAT_coNPComplete h encB,
    fun h => h encCNF CookLevin.UNSAT_coNPComplete.1⟩

/-- `SAT ∈ coNP/poly` is equivalent to `UNSAT ∈ NP/poly`. -/
theorem SAT_mem_coNPPoly_iff_UNSAT :
    SAT ∈ coNPPoly encCNF ↔ UNSAT ∈ NPPoly encCNF := by
  rw [mem_coNPPoly, compl_SAT]

/-- **`coNP ⊆ NP/poly` over bit strings is equivalent to `UNSAT ∈ NP/poly`**, via
`Cslib.Complexity.cnfDecoder` and `Cslib.Complexity.CookLevin.UNSAT_coNPComplete`. -/
theorem coNP_encBits_subset_NPPoly_iff_UNSAT :
    coNP encBits ⊆ NPPoly encBits ↔ UNSAT ∈ NPPoly encCNF := by
  refine ⟨fun h => ?_,
    fun h => coNP_subset_NPPoly_of_coNPComplete CookLevin.UNSAT_coNPComplete h encBits⟩
  let U : Set (List Bool) := {w | cnfDecoder.decode w ∈ UNSAT}
  have hred₁ : PolyTimeReducible encBits encCNF U UNSAT :=
    ⟨cnfDecoder.decode, cnfDecoder.computableInPolyTime, fun _ => Iff.rfl⟩
  have hU : U ∈ NPPoly encBits := h (hred₁.mem_coNP CookLevin.UNSAT_coNPComplete.1)
  have hred₂ : PolyTimeReducible encCNF encBits UNSAT U :=
    ⟨encCNF, (id' (encIn := encCNF)).encoding_comp, fun φ => by simp [U, cnfDecoder.decode_enc]⟩
  exact hred₂.mem_NPPoly hU

/-- **`coNP ⊆ NP/poly` on bit strings transfers to every instance encoding.** -/
theorem coNP_encBits_subset_NPPoly_iff :
    coNP encBits ⊆ NPPoly encBits ↔
      ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ NPPoly encB :=
  coNP_encBits_subset_NPPoly_iff_UNSAT.trans UNSAT_mem_NPPoly_iff_forall_coNP_subset_NPPoly

/-- **`NP ⊆ coNP/poly` on bit strings transfers to every instance encoding.** -/
theorem NP_encBits_subset_coNPPoly_iff :
    NP encBits ⊆ coNPPoly encBits ↔
      ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ coNPPoly encB := by
  rw [← coNP_subset_NPPoly_iff, coNP_encBits_subset_NPPoly_iff]
  exact ⟨fun h _ encB => coNP_subset_NPPoly_iff.1 (h encB),
    fun h _ encB => coNP_subset_NPPoly_iff.2 (h encB)⟩

/-! ### Collapse of the polynomial hierarchy -/

/-- **Yap's theorem** [Yap][Yap1983], [Bodlaender, Jansen and Kratsch, Theorem 2]
[BodlaenderJansenKratsch2014]: if `coNP ⊆ NP/poly` for problems with any encoding of their
instances, then the polynomial hierarchy collapses to its third level, `PH = Σ₃`. -/
theorem PH_eq_SigmaP_three_of_coNP_subset_NPPoly
    (h : ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ NPPoly encB) :
    PH enc = SigmaP 3 enc :=
  PH_eq_SigmaP_of_PiP_subset_SigmaP (by decide) fun encB =>
    PiP_three_subset_SigmaP_three_of_coNP_subset_NPPoly (h (encPair encB encBits))

/-- **Yap's theorem, `NP ⊆ coNP/poly ⇒ PH = Σ₃`** [Yap][Yap1983],
[Bodlaender, Jansen and Kratsch, Theorem 2][BodlaenderJansenKratsch2014]. -/
theorem PH_eq_SigmaP_three_of_NP_subset_coNPPoly
    (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ coNPPoly encB) :
    PH enc = SigmaP 3 enc :=
  PH_eq_SigmaP_three_of_coNP_subset_NPPoly fun encB => coNP_subset_NPPoly_iff.2 (h encB)

/-- **Yap's theorem from `UNSAT ∈ NP/poly`** [Yap][Yap1983]. -/
theorem PH_eq_SigmaP_three_of_UNSAT_mem_NPPoly (h : UNSAT ∈ NPPoly encCNF) :
    PH enc = SigmaP 3 enc :=
  PH_eq_SigmaP_three_of_coNP_subset_NPPoly (UNSAT_mem_NPPoly_iff_forall_coNP_subset_NPPoly.1 h)

/-- **Yap's theorem from `SAT ∈ coNP/poly`** [Yap][Yap1983]. -/
theorem PH_eq_SigmaP_three_of_SAT_mem_coNPPoly (h : SAT ∈ coNPPoly encCNF) :
    PH enc = SigmaP 3 enc :=
  PH_eq_SigmaP_three_of_UNSAT_mem_NPPoly (SAT_mem_coNPPoly_iff_UNSAT.1 h)

/-- **Yap's theorem from `coNP ⊆ NP/poly` on bit strings** [Yap][Yap1983]. -/
theorem PH_eq_SigmaP_three_of_coNP_encBits_subset_NPPoly (h : coNP encBits ⊆ NPPoly encBits) :
    PH enc = SigmaP 3 enc :=
  PH_eq_SigmaP_three_of_UNSAT_mem_NPPoly (coNP_encBits_subset_NPPoly_iff_UNSAT.1 h)

/-- **Yap's theorem from `NP ⊆ coNP/poly` on bit strings** [Yap][Yap1983]. -/
theorem PH_eq_SigmaP_three_of_NP_encBits_subset_coNPPoly (h : NP encBits ⊆ coNPPoly encBits) :
    PH enc = SigmaP 3 enc :=
  PH_eq_SigmaP_three_of_coNP_encBits_subset_NPPoly (coNP_subset_NPPoly_iff.2 h)

/-- **Yap's theorem (`PH = Σ₃ ∩ Π₃`)** [Yap][Yap1983]: if `coNP ⊆ NP/poly` for problems with any
encoding of their instances, then `PH = Σ₃ ∩ Π₃`. -/
theorem PH_eq_SigmaP_three_inter_PiP_three_of_coNP_subset_NPPoly
    (h : ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ NPPoly encB) :
    PH enc = SigmaP 3 enc ∩ PiP 3 enc := by
  rw [PH_eq_SigmaP_three_of_coNP_subset_NPPoly h,
    PiP_three_eq_SigmaP_three_of_coNP_subset_NPPoly (h (encPair enc encBits)), Set.inter_self]

end Cslib.Complexity
