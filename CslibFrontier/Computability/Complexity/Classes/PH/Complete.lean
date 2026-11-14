/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH.Collapse
public import CslibFrontier.Computability.Complexity.Classes.PH.Reduction
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Complexity.Problems.TMSAT
import CslibFrontier.Computability.Complexity.Classes.Alternation.Game
import CslibFrontier.Computability.Complexity.Classes.PH.Projection
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime

/-!
# Complete problems in the polynomial hierarchy and collapse criteria

A polynomial-time many-one reduction from an NP-complete language to its complement forces
`coNP ⊆ NP` for every explicit encoding, and hence collapses `PH` to `NP`.
This is the general reduction argument behind Exercise 3 of Chapter 5 of the 2007 draft of
[Arora and Barak][AroraBarak07]. The completeness hypothesis quantifies over all source encodings;
only one reduction on the fixed complete language is required.

Dually, `NP = coNP` at every encoding exactly when a fixed NP-complete language and a fixed
coNP-complete language reduce to each other
(`Cslib.Complexity.NPComplete.NP_eq_coNP_iff_reducible`).
This is the argument of Exercise 7, Chapter 2 of the 2007 draft, for 3SAT and TAUTOLOGY.

At higher levels, `SigmaPHard k`, `SigmaPComplete k`, `PiPHard k`, `PiPComplete k`, `PHHard` and
`PHComplete` specialize `Cslib.Complexity.PolyTimeHard` and `Cslib.Complexity.PolyTimeComplete` to
`Σₖ`, `Πₖ` and `PH` [Arora and Barak, Claim 5.7 and Chapter 5, Exercise 4][AroraBarak07]:

* Any `PH`-complete language lies in some level `Σₖ`, and reducing every `PH` problem to it pulls
  `PH` into `Σₖ` (`Cslib.Complexity.PHComplete.exists_forall_PH_eq_SigmaP`). In particular, a
  `PH`-hard language in `P` forces `PH = P` (`Cslib.Complexity.PHHard.PH_eq_P_of_mem_P`).
* Conversely, if `PH = Σₖ`, any `Σₖ`-complete language is `PH`-complete
  (`Cslib.Complexity.SigmaPComplete.phComplete_of_forall_PH_eq_SigmaP`). The level-`k` universal
  machine language `Cslib.Complexity.TMSigmaSAT` (`k` alternating blocks of unary witness length on
  `Cslib.Complexity.TMSATInstance`) is unconditionally `Σₖ`-complete for every `k`
  (`Cslib.Complexity.TMSigmaSAT.sigmaPComplete`), yielding the unconditional equivalence
  `(∃ β encB B, PHComplete encB B) ↔ ∃ k, ∀ {α} (enc : α ↪ List Bool), PH enc = SigmaP k enc`
  (`Cslib.Complexity.exists_phComplete_iff_exists_forall_PH_eq_SigmaP`).

## Main definitions

* `Cslib.Complexity.SigmaPHard`, `Cslib.Complexity.SigmaPComplete`: polynomial-time hardness and
  completeness for `Σₖ`.
* `Cslib.Complexity.PiPHard`, `Cslib.Complexity.PiPComplete`: polynomial-time hardness and
  completeness for `Πₖ`.
* `Cslib.Complexity.PHHard`, `Cslib.Complexity.PHComplete`: polynomial-time hardness and
  completeness for `PH`.
* `Cslib.Complexity.TMSigmaSAT`: the raw-verifier `Σₖ`-complete language on `TMSATInstance`.

## Main results

* `Cslib.Complexity.NPComplete.coNP_subset_NP_of_reducible_compl`,
  `Cslib.Complexity.NPComplete.NP_eq_coNP_of_reducible_compl`,
  `Cslib.Complexity.NPComplete.PH_eq_NP_of_reducible_compl`: a reduction from an NP-complete
  language to its complement collapses `PH` to `NP`.
* `Cslib.Complexity.NPComplete.NP_eq_coNP_iff_reducible`: `NP = coNP` through NP-complete and
  coNP-complete languages.
* `Cslib.Complexity.exists_replicate_of_mem_SigmaP`: every `Σₖ` problem has a verifier with a
  single polynomial bound for all `k` certificate blocks.
* `Cslib.Complexity.TMSigmaSAT.sigmaPComplete`: `TMSigmaSAT k` is `Σₖ`-complete.
* `Cslib.Complexity.PHHard.PH_eq_SigmaP_of_mem_SigmaP`,
  `Cslib.Complexity.PHHard.PH_eq_P_of_mem_P`,
  `Cslib.Complexity.PHComplete.exists_forall_PH_eq_SigmaP`: Claim 5.7 (`PH`-completeness collapses
  `PH`).
* `Cslib.Complexity.SigmaPComplete.phComplete_of_forall_PH_eq_SigmaP`,
  `Cslib.Complexity.exists_phComplete_iff_exists_forall_PH_eq_SigmaP`,
  `Cslib.Complexity.exists_phComplete_iff_exists_PH_encBits_eq_SigmaP`: Chapter 5, Exercise 4 (`PH`
  has a complete language iff `PH = Σₖ` for some `k`).

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft 2007][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {B : Set β}

/-! ### NP-complete languages and their complements -/

/-- An NP-complete language reducing to its complement puts every coNP language in NP. -/
theorem NPComplete.coNP_subset_NP_of_reducible_compl (hB : NPComplete encB B)
    (h : PolyTimeReducible encB encB B Bᶜ) : coNP enc ⊆ NP enc := by
  intro A hA
  have hAB : PolyTimeReducible enc encB A Bᶜ := by
    simpa only [compl_compl] using (hB.2 enc Aᶜ hA).compl
  have hBB : PolyTimeReducible encB encB Bᶜ B := by
    simpa only [compl_compl] using h.compl
  exact (hAB.trans hBB).mem_NP hB.1

/-- An NP-complete language reducing to its complement implies NP = coNP at every encoding. -/
theorem NPComplete.NP_eq_coNP_of_reducible_compl (hB : NPComplete encB B)
    (h : PolyTimeReducible encB encB B Bᶜ) : NP enc = coNP enc :=
  NP_eq_coNP_iff_coNP_subset_NP.mpr (fun _ => hB.coNP_subset_NP_of_reducible_compl h) enc

/-- An NP-complete language reducing to its complement collapses PH at every encoding. -/
theorem NPComplete.PH_eq_NP_of_reducible_compl (hB : NPComplete encB B)
    (h : PolyTimeReducible encB encB B Bᶜ) : PH enc = NP enc :=
  PH_eq_NP_of_coNP_subset_NP fun _ => hB.coNP_subset_NP_of_reducible_compl h

/-- **`NP = coNP` through complete languages.** For an NP-complete `B` and a coNP-complete `C`,
`NP = coNP` at every encoding exactly when `B` and `C` reduce to each other in polynomial time.
Only `C ≤ₚ B` is needed for `NP = coNP`. -/
theorem NPComplete.NP_eq_coNP_iff_reducible {γ : Type} {encC : γ ↪ List Bool} {C : Set γ}
    (hB : NPComplete encB B) (hC : coNPComplete encC C) :
    (∀ {δ : Type} (encD : δ ↪ List Bool), NP encD = coNP encD) ↔
      PolyTimeReducible encB encC B C ∧ PolyTimeReducible encC encB C B := by
  refine ⟨fun h => ⟨hC.2 encB B ((h encB).subset hB.1), hB.2 encC C ((h encC).superset hC.1)⟩,
    fun ⟨_, hCB⟩ => ?_⟩
  exact NP_eq_coNP_iff_coNP_subset_NP.mpr fun encD A hA =>
      ((hC.2 encD A hA).trans hCB).mem_NP hB.1

/-! ### Hardness and completeness for `Σₖ`, `Πₖ` and `PH` -/

/-- Every problem in `Σₖ`, with any encoding of its instances, reduces to `B` in polynomial
time. -/
abbrev SigmaPHard {β : Type*} (k : ℕ) (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeHard (fun {α} => SigmaP (α := α) k) encB B

/-- `B` is in `Σₖ` and every problem in `Σₖ` reduces to it in polynomial time. -/
abbrev SigmaPComplete {β : Type} (k : ℕ) (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeComplete (fun {α} => SigmaP (α := α) k) encB B

/-- Every problem in `Πₖ`, with any encoding of its instances, reduces to `B` in polynomial
time. -/
abbrev PiPHard {β : Type*} (k : ℕ) (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeHard (fun {α} => PiP (α := α) k) encB B

/-- `B` is in `Πₖ` and every problem in `Πₖ` reduces to it in polynomial time. -/
abbrev PiPComplete {β : Type} (k : ℕ) (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeComplete (fun {α} => PiP (α := α) k) encB B

/-- Every problem in `PH`, with any encoding of its instances, reduces to `B` in polynomial time
[Arora and Barak, Claim 5.7][AroraBarak07]. -/
abbrev PHHard {β : Type*} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeHard @PH encB B

/-- `B` is in `PH` and every problem in `PH` reduces to it in polynomial time
[Arora and Barak, Claim 5.7][AroraBarak07]. -/
abbrev PHComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeComplete @PH encB B

theorem phComplete_iff {β : Type} {encB : β ↪ List Bool} {B : Set β} :
    PHComplete encB B ↔
      B ∈ PH encB ∧
        ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α),
          A ∈ PH enc → PolyTimeReducible enc encB A B :=
  Iff.rfl

/-- The complement of a `Σₖ`-complete problem is `Πₖ`-complete. -/
theorem SigmaPComplete.compl {k : ℕ} (h : SigmaPComplete k encB B) : PiPComplete k encB Bᶜ :=
  PolyTimeComplete.compl (fun _ _ => compl_mem_SigmaP_iff.symm) h

/-- The complement of a `Πₖ`-complete problem is `Σₖ`-complete. -/
theorem PiPComplete.compl {k : ℕ} (h : PiPComplete k encB B) : SigmaPComplete k encB Bᶜ :=
  PolyTimeComplete.compl (fun _ _ => compl_mem_PiP_iff.symm) h

/-- `Σ₁`-hardness coincides with `NP`-hardness. -/
@[simp]
theorem sigmaPHard_one_iff : SigmaPHard 1 encB B ↔ NPHard encB B := by
  simp only [SigmaPHard, NPHard, PolyTimeHard, HardUnder, SigmaP_one]

/-- `Σ₁`-completeness coincides with `NP`-completeness. -/
@[simp]
theorem sigmaPComplete_one_iff : SigmaPComplete 1 encB B ↔ NPComplete encB B := by
  simp only [SigmaPComplete, NPComplete, PolyTimeComplete, PolyTimeHard, HardUnder, SigmaP_one]

/-- `Π₁`-hardness coincides with `coNP`-hardness. -/
@[simp]
theorem piPHard_one_iff : PiPHard 1 encB B ↔ coNPHard encB B := by
  simp only [PiPHard, coNPHard, PolyTimeHard, HardUnder, PiP_one_eq_coNP]

/-- `Π₁`-completeness coincides with `coNP`-completeness. -/
@[simp]
theorem piPComplete_one_iff : PiPComplete 1 encB B ↔ coNPComplete encB B := by
  simp only [PiPComplete, coNPComplete, PolyTimeComplete, PolyTimeHard, HardUnder, PiP_one_eq_coNP]

/-! ### Uniform block lengths and raw-verifier `Σₖ`-completeness -/

private theorem eval_le_eval_sum {ps : List (Polynomial ℕ)} {r : Polynomial ℕ} (hr : r ∈ ps)
    (n : ℕ) : r.eval n ≤ ps.sum.eval n := by
  induction ps with
  | nil => cases hr
  | cons q qs ih =>
    rw [List.sum_cons, Polynomial.eval_add]
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Nat.le_add_right _ _
    · exact (ih hr).trans (Nat.le_add_left _ _)

/-- **Uniform block-length normal form for `Σₖ`:** every `A ∈ SigmaP k enc` can be verified using a
single polynomial `p` for all `k` certificate blocks (`List.replicate k p`), matching
[Arora and Barak, Definition 5.3][AroraBarak09]. -/
theorem exists_replicate_of_mem_SigmaP {k : ℕ} {A : Set α} (hA : A ∈ SigmaP k enc) :
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        IsAlternatingVerifier enc true (List.replicate k p) V A := by
  obtain ⟨ps, V, hps, hV, hAV⟩ := hA
  refine ⟨ps.sum, fun x => V (x.1,
    takeBlocks (ps.map fun r => (r.eval (enc x.1).length, ps.sum.eval (enc x.1).length)) x.2),
    ?_, fun a => ?_⟩
  · have hlen : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
        (encPair enc encBits) encUnary :=
      (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
    have htake : ComputableInPolyTime
        (fun x : α × List Bool =>
          takeBlocks (ps.map fun r => (r.eval (enc x.1).length, ps.sum.eval (enc x.1).length)) x.2)
        (encPair enc encBits) encBits := by
      simpa only [List.map_map, Function.comp_def] using
        computableInPolyTime_takeBlocks
          (ps.map fun r => (fun x : α × List Bool => r.eval (enc x.1).length,
            fun x => ps.sum.eval (enc x.1).length))
          (fun l hl => by
            obtain ⟨r, -, rfl⟩ := List.mem_map.mp hl
            exact ⟨(ComputableInPolyTime.unary_eval r).comp hlen,
              (ComputableInPolyTime.unary_eval ps.sum).comp hlen⟩)
          (.snd _ _)
    exact hV.comp ((ComputableInPolyTime.fst _ _).prod htake)
  · rw [hAV a]
    have htake := alternation_takeBlocks
      (ls := ps.map fun r => (r.eval (enc a).length, ps.sum.eval (enc a).length))
      (q := true) (P := fun w => V (a, w) = true)
      (fun l hl => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
        exact eval_le_eval_sum hr (enc a).length)
    have hsnd : (ps.map fun r => (r.eval (enc a).length, ps.sum.eval (enc a).length)).map Prod.snd =
        (List.replicate k ps.sum).map (fun p => p.eval (enc a).length) := by
      rw [List.map_map, List.map_replicate, ← hps]
      exact List.map_const'
    have hfst : (ps.map fun r => (r.eval (enc a).length, ps.sum.eval (enc a).length)).map Prod.fst =
        ps.map (fun p => p.eval (enc a).length) := by
      simp [Function.comp_def]
    rw [← hfst, ← htake, hsnd]

/-- **Level-`k` machine satisfiability (`TMSigmaSAT k`)**: the instances `⟨α, x, 1ⁿ, 1ᵗ⟩`
(`Cslib.Complexity.TMSATInstance`) for which `k` alternating quantifier blocks of length `n`
(starting with `∃`) make the machine described by `α` accept `⟨x, u₁ ++ ⋯ ++ uₖ⟩` within `t` steps.
For `k = 1` this is `TMSAT`. -/
def TMSigmaSAT (k : ℕ) : Set TMSATInstance :=
  {a | Alternation true (List.replicate k a.witnessLength) a.Accepts}

namespace TMSigmaSAT

theorem mem_iff {k : ℕ} {a : TMSATInstance} :
    a ∈ TMSigmaSAT k ↔ Alternation true (List.replicate k a.witnessLength) a.Accepts :=
  Iff.rfl

@[simp]
theorem one_eq_TMSAT : TMSigmaSAT 1 = TMSAT := by
  ext a
  simp [TMSigmaSAT, TMSAT.mem_iff, alternation_singleton_true]

/-- The verifier of `TMSigmaSAT k`: cut `k` blocks of length `|enc a|` to `a.witnessLength` bits
each and run the described machine for `a.steps` steps. -/
noncomputable def verifier (k : ℕ) (q : TMSATInstance × List Bool) : Bool :=
  decide (universal (q.1.machine,
    (encPair encBits encBits (q.1.input,
      takeBlocks (List.replicate k (q.1.witnessLength, (encTMSATInstance q.1).length))
        q.2)).map eBit,
    q.1.steps) = ([eBit true], true))

theorem computableInPolyTime_verifier (k : ℕ) :
    ComputableInPolyTime (verifier k) (encPair encTMSATInstance encBits) encBool := by
  have hpair : ComputableInPolyTime (fun p : List Bool × List Bool => encPair encBits encBits p)
      (encPair encBits encBits) encBits :=
    .of_eq fun _ => rfl
  have htake : ComputableInPolyTime
      (fun q : TMSATInstance × List Bool =>
        takeBlocks (List.replicate k (q.1.witnessLength, (encTMSATInstance q.1).length)) q.2)
      (encPair encTMSATInstance encBits) encBits := by
    simpa only [List.map_replicate] using
      computableInPolyTime_takeBlocks
        (List.replicate k (fun q : TMSATInstance × List Bool => q.1.witnessLength,
          fun q => (encTMSATInstance q.1).length))
        (fun l hl => by
          obtain rfl := List.eq_of_mem_replicate hl
          exact ⟨by fun_prop,
            (ComputableInPolyTime.encoding_length encTMSATInstance).comp (.fst _ _)⟩)
        (.snd _ _)
  have hin : ComputableInPolyTime
      (fun q : TMSATInstance × List Bool =>
        (q.1.machine,
          (encPair encBits encBits (q.1.input,
            takeBlocks (List.replicate k (q.1.witnessLength, (encTMSATInstance q.1).length))
              q.2)).map eBit,
          q.1.steps))
      (encPair encTMSATInstance encBits) eInUnary := by
    have hx : ComputableInPolyTime (fun q : TMSATInstance × List Bool =>
        encPair encBits encBits (q.1.input,
          takeBlocks (List.replicate k (q.1.witnessLength, (encTMSATInstance q.1).length))
            q.2))
        (encPair encTMSATInstance encBits) encBits :=
      hpair.comp ((encTMSATInstance_input_polyTime (.fst _ _)).prod htake)
    have := computableInPolyTime_map_eBit.comp hx
    fun_prop
  exact (computableInPolyTime_universal.comp hin).decide_eq' (.const _)

theorem isAlternatingVerifier (k : ℕ) :
    IsAlternatingVerifier encTMSATInstance true (List.replicate k Polynomial.X)
      (verifier k) (TMSigmaSAT k) := fun a => by
  rw [mem_iff]
  have htake := alternation_takeBlocks
    (ls := List.replicate k (a.witnessLength, (encTMSATInstance a).length))
    (q := true) (P := a.Accepts)
    (fun l hl => by
      obtain rfl := List.eq_of_mem_replicate hl
      exact TMSAT.witnessLength_le a)
  simpa only [List.map_replicate, Polynomial.eval_X, verifier, decide_eq_true_iff,
    TMSATInstance.accepts_iff] using htake.symm

/-- **`TMSigmaSAT k` is in `Σₖ`.** -/
theorem mem_SigmaP (k : ℕ) : TMSigmaSAT k ∈ SigmaP k encTMSATInstance :=
  ⟨List.replicate k Polynomial.X, verifier k, List.length_replicate,
    computableInPolyTime_verifier k, isAlternatingVerifier k⟩

/-- **`TMSigmaSAT k` is `Σₖ`-hard**: every problem in `Σₖ` reduces to it in polynomial time via
the uniform-block verifier of `Cslib.Complexity.exists_replicate_of_mem_SigmaP`. -/
theorem sigmaPHard (k : ℕ) : SigmaPHard k encTMSATInstance (TMSigmaSAT k) := by
  intro α enc A hA
  obtain ⟨p, V, ⟨t, _, ht, -, m, State, hfin, tm, htm⟩, hV⟩ := exists_replicate_of_mem_SigmaP hA
  obtain ⟨c, d, ht⟩ := polynomiallyBounded_iff_le.mp ht
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  refine ⟨fun a => ⟨desc eS eBit tm, enc a, p.eval (enc a).length,
    (TMSAT.stepPoly (Polynomial.C k * p) c d).eval (enc a).length⟩, ?_, fun a => ?_⟩
  · have henc : ComputableInPolyTime (fun a => enc a) enc encBits := .of_eq fun _ => rfl
    have hlen : ComputableInPolyTime (fun a => (enc a).length) enc encUnary := by fun_prop
    have hp := (ComputableInPolyTime.unary_eval p).comp hlen
    have hq := (ComputableInPolyTime.unary_eval (TMSAT.stepPoly (Polynomial.C k * p) c d)).comp hlen
    fun_prop
  · rw [hV a, mem_iff]
    simp only [List.map_replicate]
    refine alternation_congr_of_length fun w hw => ?_
    rw [List.sum_replicate, smul_eq_mul] at hw
    have hle : t (encPair enc encBits (a, w)).length ≤
        (TMSAT.stepPoly (Polynomial.C k * p) c d).eval (enc a).length := by
      refine (ht _).trans_eq ?_
      rw [TMSAT.eval_stepPoly, length_encPair]
      simp only [encBits, Function.Embedding.refl_apply, hw, Polynomial.eval_mul, Polynomial.eval_C]
      ring_nf
    obtain ⟨hhalt, hout⟩ := (htm (a, w)).runFrom_of_le hle
    rw [TMSATInstance.accepts_desc_iff]
    change (tm.runFrom (tm.initCfg (encPair enc encBits (a, w))) _).output = [V (a, w)] at hout
    have hx : encPair encBits encBits (enc a, w) = encPair enc encBits (a, w) := rfl
    rw [hx, hout, List.cons.injEq]
    exact ⟨fun h => ⟨hhalt, h, rfl⟩, fun h => h.2.1⟩

/-- **`TMSigmaSAT k` is `Σₖ`-complete.** -/
theorem sigmaPComplete (k : ℕ) : SigmaPComplete k encTMSATInstance (TMSigmaSAT k) :=
  ⟨mem_SigmaP k, sigmaPHard k⟩

end TMSigmaSAT

/-! ### PH-completeness and hierarchy collapse (Arora–Barak Claim 5.7 and Chapter 5, Exercise 4) -/

/-- **Arora–Barak Claim 5.7:** if a `PH`-hard problem lies in `Σₖ`, then `PH = Σₖ` for every
instance encoding. -/
theorem PHHard.PH_eq_SigmaP_of_mem_SigmaP {k : ℕ} (hB : PHHard encB B) (hk : B ∈ SigmaP k encB)
    (enc : α ↪ List Bool) : PH enc = SigmaP k enc :=
  Set.Subset.antisymm (fun A hA => (hB enc A hA).mem_SigmaP hk) (SigmaP_subset_PH k)

/-- **Arora–Barak Claim 5.7 (`P` special case):** if a `PH`-hard problem lies in `P`, then
`PH = P` for every instance encoding. -/
theorem PHHard.PH_eq_P_of_mem_P (hB : PHHard encB B) (hP : B ∈ P encB) (enc : α ↪ List Bool) :
    PH enc = P enc := by
  rw [← SigmaP_zero] at hP ⊢
  exact PHHard.PH_eq_SigmaP_of_mem_SigmaP hB hP enc

/-- **Arora–Barak Claim 5.7 (forward direction):** if `B` is `PH`-complete, then the polynomial
hierarchy collapses to some level `Σₖ` at every instance encoding. -/
theorem PHComplete.exists_forall_PH_eq_SigmaP (hB : PHComplete encB B) :
    ∃ k, ∀ {α : Type} (enc : α ↪ List Bool), PH enc = SigmaP k enc := by
  obtain ⟨k, hk⟩ := mem_PH.mp hB.1
  exact ⟨k, fun enc => PHHard.PH_eq_SigmaP_of_mem_SigmaP hB.2 hk enc⟩

/-- **Converse of Claim 5.7 for any `Σₖ`-complete problem:** if `PH = Σₖ` at every encoding, then
every `Σₖ`-complete problem is `PH`-complete. -/
theorem SigmaPComplete.phComplete_of_forall_PH_eq_SigmaP {k : ℕ} (hB : SigmaPComplete k encB B)
    (h : ∀ {α : Type} (enc : α ↪ List Bool), PH enc = SigmaP k enc) : PHComplete encB B :=
  ⟨SigmaP_subset_PH k hB.1, fun _ enc A hA => hB.2 enc A ((h enc).subset hA)⟩

/-- **Converse of Claim 5.7 from fixed-domain `encBits` collapse:** if
`PH encBits = SigmaP k encBits`, then every `Σₖ`-complete problem is `PH`-complete. -/
theorem SigmaPComplete.phComplete_of_PH_encBits_eq_SigmaP {k : ℕ} (hB : SigmaPComplete k encB B)
    (h : PH encBits = SigmaP k encBits) : PHComplete encB B :=
  hB.phComplete_of_forall_PH_eq_SigmaP (PH_encBits_eq_SigmaP_iff.mp h)

/-- **Arora–Barak Claim 5.7 / Chapter 5, Exercise 4:** `PH` has a complete language under
polynomial-time many-one reductions if and only if `PH = Σₖ` for some `k` (at every instance
encoding). The reverse direction uses `TMSigmaSAT k` (`Cslib.Complexity.TMSigmaSAT.sigmaPComplete`).
-/
theorem exists_phComplete_iff_exists_forall_PH_eq_SigmaP :
    (∃ (β : Type) (encB : β ↪ List Bool) (B : Set β), PHComplete encB B) ↔
      ∃ k, ∀ {α : Type} (enc : α ↪ List Bool), PH enc = SigmaP k enc :=
  ⟨fun ⟨_, _, _, hB⟩ => hB.exists_forall_PH_eq_SigmaP,
    fun ⟨k, hk⟩ => ⟨TMSATInstance, encTMSATInstance, TMSigmaSAT k,
      (TMSigmaSAT.sigmaPComplete k).phComplete_of_forall_PH_eq_SigmaP hk⟩⟩

/-- **Arora–Barak Claim 5.7 / Chapter 5, Exercise 4 (fixed-domain `encBits` form):** `PH` has a
complete language under polynomial-time many-one reductions if and only if
`PH encBits = SigmaP k encBits` for some `k`. -/
theorem exists_phComplete_iff_exists_PH_encBits_eq_SigmaP :
    (∃ (β : Type) (encB : β ↪ List Bool) (B : Set β), PHComplete encB B) ↔
      ∃ k, PH encBits = SigmaP k encBits :=
  exists_phComplete_iff_exists_forall_PH_eq_SigmaP.trans
    (exists_congr fun _ => PH_encBits_eq_SigmaP_iff.symm)

end Cslib.Complexity
