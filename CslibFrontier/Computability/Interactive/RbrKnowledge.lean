/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Interactive.AuxZK
public import CslibFrontier.Computability.Interactive.Bundle
public import CslibFrontier.Computability.Interactive.Efficient
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.EventBind

/-!
# Round-by-round knowledge soundness of interactive reductions

Round-by-round knowledge soundness (`Interactive.Verifier.RbrKnowledgeSound`) strengthens
round-by-round soundness (`Interactive.Verifier.RbrSound`) with a straight-line witness extractor
`E : StmtIn → Transcript s → WitOut → WitIn` [Canetti et al.][CanettiCHLRRW2019],
[Chiesa and Yogev][ChiesaYogev2024].

For every input statement `x` (without assuming `x ∉ language relIn`), a state function
`S x : Prefix s → Prop` on transcript prefixes tracks whether the prover has gotten lucky on a
verifier challenge:
* Initially, the empty prefix is doomed (`¬ S x (Prefix.empty s)`).
* No prover message can leave a doomed prefix.
* Each random verifier challenge leaves a doomed prefix with probability at most that round's
  error in `ε : PerChallenge (fun _ => ℝ≥0∞) s`.
* On any complete transcript `τ` that remains doomed (`¬ S x τ`), if the verifier outputs `some x'`
  and `w` is a valid output witness (`relOut x' w`), then the extracted input witness is valid
  (`relIn x (E x τ w)`).

Because the initial prefix is doomed for every statement `x`, round-by-round knowledge soundness
both implies round-by-round soundness for the languages of the relations
(`Verifier.RbrKnowledgeSound.toRbrSound`) and implies straight-line knowledge soundness with error
`PerChallenge.sum s ε` (`Verifier.RbrKnowledgeSound.toKnowledgeSound`). When `E` is computable in
polynomial time on encoded words, it yields `Verifier.EfficientKnowledgeSound`
(`Verifier.RbrKnowledgeSound.efficientKnowledgeSound`). Moreover, unlike standard knowledge
soundness, its round-by-round state function composes directly across sequential reductions
(`Verifier.RbrKnowledgeSound.append`), sequential products (`Verifier.RbrKnowledgeSound.seqProd`),
iterated stages (`Verifier.RbrKnowledgeSound.iterate`), and statement-parameterized bundles
(`Verifier.RbrKnowledgeSound.bundle`).

## Main definitions

* `Interactive.Verifier.RbrKnowledgeSound`: round-by-round knowledge soundness in the plain model.
* `Interactive.Verifier.extractIterate`: composed straight-line extractor for `Reduction.iterate`.

## Main results

* `Interactive.rbrFrom_true`, `Interactive.RbrFrom.mono_wins`: monotonicity and trivial-state
  helpers for `RbrFrom`.
* `Interactive.Verifier.RbrKnowledgeSound.toRbrSound`,
  `Interactive.Verifier.RbrKnowledgeSound.rbrSound`: round-by-round knowledge soundness implies
  round-by-round soundness for `language relIn` and `language relOut`.
* `Interactive.Verifier.RbrKnowledgeSound.toKnowledgeSound`,
  `Interactive.Verifier.RbrKnowledgeSound.knowledgeSound`: round-by-round knowledge soundness
  implies straight-line knowledge soundness with error `PerChallenge.sum s ε`.
* `Interactive.Verifier.RbrKnowledgeSound.toSound`,
  `Interactive.Verifier.RbrKnowledgeSound.sound`: round-by-round knowledge soundness implies
  standard soundness with error `PerChallenge.sum s ε`.
* `Interactive.Verifier.RbrKnowledgeSound.efficientKnowledgeSound`: round-by-round knowledge
  soundness with a polynomial-time extractor gives `Verifier.EfficientKnowledgeSound`.
* `Interactive.Verifier.RbrSound.rbrKnowledgeSound`: round-by-round soundness gives round-by-round
  knowledge soundness for any extractor that is valid on `language relIn` (in particular for
  witness-free reductions).
* `Interactive.Verifier.RbrKnowledgeSound.append`,
  `Interactive.Verifier.RbrKnowledgeSound.seq`: sequential composition of round-by-round knowledge
  soundness with `Verifier.extractAppend`.
* `Interactive.Verifier.RbrKnowledgeSound.seqProd`,
  `Interactive.Verifier.RbrSound.seqProd`: sequential product composition on `s₁ ++ s₂` over
  `Verifier.seqProd` and `relProd`.
* `Interactive.Reduction.id_rbrKnowledgeSound`,
  `Interactive.Verifier.RbrKnowledgeSound.iterate`,
  `Interactive.Verifier.RbrKnowledgeSound.bundle`: identity, iteration, and bundle preservation.

## References

* [R. Canetti, Y. Chen, J. Holmgren, A. Lombardi, G. N. Rothblum, R. D. Rothblum, D. Wichs,
  *Fiat–Shamir: from practice to theory*][CanettiCHLRRW2019]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024]
-/

public section

namespace Cslib.Interactive

open scoped ENNReal
open Spec Probability Turing.MultiTapeTM

variable {s s₁ s₂ : Spec} {StmtIn WitIn StmtOut WitOut : Type}

/-! ### Round-by-round helpers -/

/-- The round-by-round condition holds trivially when every prefix is already in the lucky state. -/
theorem rbrFrom_true : ∀ (s : Spec) (smp : PerChallenge ProbComp s)
    (ε : PerChallenge (fun _ => ℝ≥0∞) s) (wins : Transcript s → Prop),
    RbrFrom s smp ε (fun _ => True) wins
  | [], _, _, _ => fun h => False.elim (h trivial)
  | .prover _ _ :: s, smp, ε, wins =>
    ⟨fun h => False.elim (h trivial), fun m => rbrFrom_true s smp ε fun τ => wins (m, τ)⟩
  | .verifier _ :: s, smp, ε, wins =>
    ⟨fun h => False.elim (h trivial), fun c => rbrFrom_true s smp.2 ε.2 fun τ => wins (c, τ)⟩

/-- Strengthening the winning event preserves the round-by-round condition. -/
theorem RbrFrom.mono_wins : ∀ {s : Spec} {smp : PerChallenge ProbComp s}
    {ε : PerChallenge (fun _ => ℝ≥0∞) s} {S : Prefix s → Prop}
    {wins wins' : Transcript s → Prop},
    (∀ τ, wins' τ → wins τ) → RbrFrom s smp ε S wins → RbrFrom s smp ε S wins'
  | [], _, _, _, _, _, hw, h => fun hS hw' => h hS (hw () hw')
  | .prover _ _ :: _, _, _, _, _, _, hw, h =>
    ⟨h.1, fun m => RbrFrom.mono_wins (fun τ => hw (m, τ)) (h.2 m)⟩
  | .verifier _ :: _, _, _, _, _, _, hw, h =>
    ⟨h.1, fun c => RbrFrom.mono_wins (fun τ => hw (c, τ)) (h.2 c)⟩

/-! ### Round-by-round knowledge soundness and its fundamental implications -/

/-- Round-by-round knowledge soundness in the plain model with straight-line extractor `E` and
per-round errors `ε`: some state function on transcript prefixes is false on the empty prefix of
every statement and satisfies the round-by-round condition for the event that the verifier outputs
a statement with a valid output witness for which `E` fails to recover a valid input witness. -/
def Verifier.RbrKnowledgeSound (V : Verifier OracleSpec.empty s StmtIn StmtOut)
    (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)
    (E : StmtIn → Transcript s → WitOut → WitIn)
    (ε : PerChallenge (fun _ => ℝ≥0∞) s) : Prop :=
  ∃ S : StmtIn → Prefix s → Prop, (∀ x, ¬ S x (Prefix.empty s)) ∧
    ∀ x, RbrFrom s V.samplers ε (S x)
      fun τ => ∃ x' w, V.outputOn x τ = some x' ∧ relOut x' w ∧ ¬ relIn x (E x τ w)

/-- **Round-by-round knowledge soundness implies round-by-round soundness** for the languages of
the input and output relations, with the same per-round errors. On a statement
`x ∉ language relIn`, no extracted witness can satisfy `relIn x`, so any transcript producing an
output in `language relOut` must have entered the lucky state. -/
theorem Verifier.RbrKnowledgeSound.toRbrSound
    {V : Verifier OracleSpec.empty s StmtIn StmtOut}
    {relIn : StmtIn → WitIn → Prop} {relOut : StmtOut → WitOut → Prop}
    {E : StmtIn → Transcript s → WitOut → WitIn}
    {ε : PerChallenge (fun _ => ℝ≥0∞) s}
    (h : V.RbrKnowledgeSound relIn relOut E ε) :
    V.RbrSound (language relIn) (language relOut) ε := by
  obtain ⟨S, hinit, hround⟩ := h
  refine ⟨fun x p => x ∈ language relIn ∨ S x p,
    fun x hx hS => hS.elim hx (hinit x), fun x => ?_⟩
  by_cases hx : x ∈ language relIn
  · refine RbrFrom.congr (fun _ => ⟨fun _ => Or.inl hx, fun _ => trivial⟩)
      (fun _ => Iff.rfl) (rbrFrom_true s V.samplers ε _)
  · refine RbrFrom.congr (fun p => ⟨Or.inr, fun hS => hS.resolve_left hx⟩)
      (fun _ => Iff.rfl) (RbrFrom.mono_wins ?_ (hround x))
    rintro τ ⟨x', ⟨w, hw⟩, hout⟩
    exact ⟨x', w, hout, hw, fun hrel => hx ⟨_, hrel⟩⟩

/-- Alias for `Verifier.RbrKnowledgeSound.toRbrSound`. -/
alias Verifier.RbrKnowledgeSound.rbrSound := Verifier.RbrKnowledgeSound.toRbrSound

/-- **Round-by-round knowledge soundness implies straight-line knowledge soundness**, with the sum
of the per-round errors and the same extractor `E`. -/
theorem Verifier.RbrKnowledgeSound.toKnowledgeSound
    {V : Verifier OracleSpec.empty s StmtIn StmtOut}
    {relIn : StmtIn → WitIn → Prop} {relOut : StmtOut → WitOut → Prop}
    {E : StmtIn → Transcript s → WitOut → WitIn}
    {ε : PerChallenge (fun _ => ℝ≥0∞) s}
    (h : V.RbrKnowledgeSound relIn relOut E ε) :
    V.KnowledgeSound relIn relOut E (PerChallenge.sum s ε) := by
  obtain ⟨S, hinit, hround⟩ := h
  intro x P
  rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply, plainLaw_bind]
  refine Probability.PMF.toOuterMeasure_bind_le _ _ _ fun st => ?_
  refine le_trans (MeasureTheory.measure_mono ?_)
    (rbrFrom_le s V.samplers ε (S x) _ (hround x) (hinit x) st)
  rintro ⟨τ, w⟩ ⟨⟨x', hout, hrel⟩, hnot⟩
  exact ⟨x', w, hout, hrel, hnot⟩

/-- Alias for `Verifier.RbrKnowledgeSound.toKnowledgeSound`. -/
alias Verifier.RbrKnowledgeSound.knowledgeSound := Verifier.RbrKnowledgeSound.toKnowledgeSound

/-- Round-by-round knowledge soundness implies soundness for the languages of the relations, with
the sum of the per-round errors. -/
theorem Verifier.RbrKnowledgeSound.toSound
    {V : Verifier OracleSpec.empty s StmtIn StmtOut}
    {relIn : StmtIn → WitIn → Prop} {relOut : StmtOut → WitOut → Prop}
    {E : StmtIn → Transcript s → WitOut → WitIn}
    {ε : PerChallenge (fun _ => ℝ≥0∞) s}
    (h : V.RbrKnowledgeSound relIn relOut E ε) :
    V.Sound (oP := OracleSpec.empty) World.plain (language relIn) (language relOut)
      (PerChallenge.sum s ε) :=
  h.toRbrSound.sound

/-- Alias for `Verifier.RbrKnowledgeSound.toSound`. -/
alias Verifier.RbrKnowledgeSound.sound := Verifier.RbrKnowledgeSound.toSound

/-- **Round-by-round knowledge soundness with a polynomial-time extractor gives efficient
straight-line knowledge soundness**, with knowledge error `PerChallenge.sum (s i) (ε i)` at
index `i`. -/
theorem Verifier.RbrKnowledgeSound.efficientKnowledgeSound
    {I : Type} {s : I → Spec} {StmtIn WitIn StmtOut WitOut : I → Type}
    {V : ∀ i, Verifier OracleSpec.empty (s i) (StmtIn i) (StmtOut i)}
    {relIn : ∀ i, StmtIn i → WitIn i → Prop} {relOut : ∀ i, StmtOut i → WitOut i → Prop}
    {enc : Encoding I s StmtIn} {encOut : ∀ i, WitOut i ↪ List Bool}
    {encIn : ∀ i, WitIn i ↪ List Bool}
    {E : ∀ i, StmtIn i → Transcript (s i) → WitOut i → WitIn i}
    {ε : ∀ i, PerChallenge (fun _ => ℝ≥0∞) (s i)}
    {f : I × List Bool × List Bool × List Bool → List Bool}
    (hrbr : ∀ i, (V i).RbrKnowledgeSound (relIn i) (relOut i) (E i) (ε i))
    (hf : ComputableInPolyTime f
      (encPair enc.index (encPair encBits (encPair encBits encBits))) encBits)
    (hreal : ExtractorRealizedBy enc encOut encIn E f) :
    Verifier.EfficientKnowledgeSound V relIn relOut enc encOut encIn E
      (fun i => PerChallenge.sum (s i) (ε i)) :=
  ⟨fun i => (hrbr i).toKnowledgeSound, ⟨f, hf, hreal⟩⟩

/-- Round-by-round soundness gives round-by-round knowledge soundness for any extractor that
outputs a valid witness on every statement of `language relIn` (for example, in reductions with
`Unit` witnesses). -/
theorem Verifier.RbrSound.rbrKnowledgeSound
    {V : Verifier OracleSpec.empty s StmtIn StmtOut}
    {relIn : StmtIn → WitIn → Prop} {relOut : StmtOut → WitOut → Prop}
    {ε : PerChallenge (fun _ => ℝ≥0∞) s}
    (E : StmtIn → Transcript s → WitOut → WitIn)
    (hE : ∀ x ∈ language relIn, ∀ τ w, relIn x (E x τ w))
    (h : V.RbrSound (language relIn) (language relOut) ε) :
    V.RbrKnowledgeSound relIn relOut E ε := by
  obtain ⟨S, hinit, hround⟩ := h
  refine ⟨fun x p => x ∉ language relIn ∧ S x p,
    fun x hS => hinit x hS.1 hS.2, fun x => ?_⟩
  by_cases hx : x ∈ language relIn
  · refine RbrFrom.congr (fun _ => ?_) (fun τ => ?_) (rbrFrom_false s V.samplers ε)
    · simp [hx]
    · constructor
      · exact False.elim
      · rintro ⟨x', w, -, -, hnot⟩
        exact hnot (hE x hx τ w)
  · refine RbrFrom.congr (fun p => ⟨fun hS => ⟨hx, hS⟩, And.right⟩)
      (fun _ => Iff.rfl) (RbrFrom.mono_wins ?_ (hround x))
    rintro τ ⟨x', w, hout, hrel, -⟩
    exact ⟨x', ⟨w, hrel⟩, hout⟩

/-! ### Sequential composition -/

section Sequential

variable {S₁ W₁ S₂ W₂ S₃ W₃ : Type}

/-- **Round-by-round knowledge soundness composes sequentially**, with the composed straight-line
extractor `Verifier.extractAppend` and the concatenated per-round errors. The combined state
function is `T₁` during the first phase and the disjunction of the first phase's failure event with
`T₂` during the second phase. -/
theorem Verifier.RbrKnowledgeSound.append
    {V₁ : Verifier OracleSpec.empty s₁ S₁ S₂}
    {V₂ : Verifier OracleSpec.empty s₂ S₂ S₃}
    {rel₁ : S₁ → W₁ → Prop} {rel₂ : S₂ → W₂ → Prop} {rel₃ : S₃ → W₃ → Prop}
    {E₁ : S₁ → Transcript s₁ → W₂ → W₁} {E₂ : S₂ → Transcript s₂ → W₃ → W₂}
    {ε₁ : PerChallenge (fun _ => ℝ≥0∞) s₁} {ε₂ : PerChallenge (fun _ => ℝ≥0∞) s₂}
    (h₁ : V₁.RbrKnowledgeSound rel₁ rel₂ E₁ ε₁)
    (h₂ : V₂.RbrKnowledgeSound rel₂ rel₃ E₂ ε₂) (y₀ : S₂) :
    (V₁.append V₂).RbrKnowledgeSound rel₁ rel₃ (V₁.extractAppend E₁ E₂ y₀)
      (PerChallenge.append s₁ s₂ ε₁ ε₂) := by
  obtain ⟨T₁, hinit₁, hr₁⟩ := h₁
  obtain ⟨T₂, hinit₂, hr₂⟩ := h₂
  let wins₁ : S₁ → Transcript s₁ → Prop :=
    fun x τ₁ => ∃ y w₂, V₁.outputOn x τ₁ = some y ∧ rel₂ y w₂ ∧ ¬ rel₁ x (E₁ x τ₁ w₂)
  let next : S₁ → Transcript s₁ → Prefix s₂ → Prop :=
    fun x τ₁ p => wins₁ x τ₁ ∨ ∃ y, V₁.outputOn x τ₁ = some y ∧ T₂ y p
  have hjunc : ∀ x τ₁, ¬ wins₁ x τ₁ → ¬ next x τ₁ (Prefix.empty s₂) := by
    rintro x τ₁ hw (hw' | ⟨y, _, hT⟩)
    · exact hw hw'
    · exact hinit₂ y hT
  have hsecond : ∀ x τ₁, RbrFrom s₂ V₂.samplers ε₂ (next x τ₁)
      (fun τ₂ => ∃ z w₃,
        (V₁.outputOn x τ₁).bind (fun y => V₂.outputOn y τ₂) = some z ∧
          rel₃ z w₃ ∧
          ¬ rel₁ x (E₁ x τ₁ (E₂ ((V₁.outputOn x τ₁).getD y₀) τ₂ w₃))) := by
    intro x τ₁
    by_cases hw₁ : wins₁ x τ₁
    · refine RbrFrom.congr (fun _ => ⟨fun _ => Or.inl hw₁, fun _ => trivial⟩)
        (fun _ => Iff.rfl) (rbrFrom_true s₂ V₂.samplers ε₂ _)
    · cases hout : V₁.outputOn x τ₁ with
      | none =>
        refine RbrFrom.congr (fun p => ?_) (fun τ₂ => ?_) (rbrFrom_false s₂ V₂.samplers ε₂)
        · simp [next, hw₁, hout]
        · simp
      | some y =>
        refine RbrFrom.congr (fun p => ?_) (fun _ => Iff.rfl)
          (RbrFrom.mono_wins ?_ (hr₂ y))
        · simp [next, hw₁, hout]
        · rintro τ₂ ⟨z, w₃, hz, hrel₃, hnot₁⟩
          simp only [Option.bind_some, Option.getD_some] at hz hnot₁
          refine ⟨z, w₃, hz, hrel₃, fun hrel₂ => hnot₁ ?_⟩
          by_contra hnot
          exact hw₁ ⟨y, E₂ y τ₂ w₃, hout, hrel₂, hnot⟩
  refine ⟨fun x => compState s₁ s₂ (T₁ x) (next x),
    fun x => not_compState_empty (hr₁ x) (hjunc x) (hinit₁ x), fun x => ?_⟩
  refine RbrFrom.congr (fun _ => Iff.rfl) (fun τ => ?_)
    (rbrFrom_append s₁ s₂ V₁.samplers V₂.samplers ε₁ ε₂ (T₁ x) (wins₁ x) (next x) _
      (hr₁ x) (hjunc x) (hsecond x))
  rw [outputOn_append]
  rfl

/-- Alias for `Verifier.RbrKnowledgeSound.append`. -/
alias Verifier.RbrKnowledgeSound.seq := Verifier.RbrKnowledgeSound.append

end Sequential

/-! ### Sequential product composition -/

section SeqProd

variable {S₁ W₁ S₂ W₂ T₁ U₁ T₂ U₂ : Type}

/-- **Round-by-round knowledge soundness composes across sequential products**, with combined state
`State₁` on the first phase and `State₁ ∨ State₂` on the second phase, and with product extractor
`Verifier.extractSeqProd E₁ E₂`. -/
theorem Verifier.RbrKnowledgeSound.seqProd
    {V₁ : Verifier OracleSpec.empty s₁ S₁ S₂}
    {V₂ : Verifier OracleSpec.empty s₂ T₁ T₂}
    {rel₁ : S₁ → W₁ → Prop} {rel₁' : S₂ → W₂ → Prop}
    {rel₂ : T₁ → U₁ → Prop} {rel₂' : T₂ → U₂ → Prop}
    {E₁ : S₁ → Transcript s₁ → W₂ → W₁} {E₂ : T₁ → Transcript s₂ → U₂ → U₁}
    {ε₁ : PerChallenge (fun _ => ℝ≥0∞) s₁} {ε₂ : PerChallenge (fun _ => ℝ≥0∞) s₂}
    (h₁ : V₁.RbrKnowledgeSound rel₁ rel₁' E₁ ε₁)
    (h₂ : V₂.RbrKnowledgeSound rel₂ rel₂' E₂ ε₂) :
    (V₁.seqProd V₂).RbrKnowledgeSound (relProd rel₁ rel₂) (relProd rel₁' rel₂')
      (Verifier.extractSeqProd E₁ E₂) (PerChallenge.append s₁ s₂ ε₁ ε₂) := by
  obtain ⟨St₁, hinit₁, hr₁⟩ := h₁
  obtain ⟨St₂, hinit₂, hr₂⟩ := h₂
  let wins₁ : S₁ → Transcript s₁ → Prop :=
    fun x₁ τ₁ => ∃ y₁ w₂, V₁.outputOn x₁ τ₁ = some y₁ ∧ rel₁' y₁ w₂ ∧ ¬ rel₁ x₁ (E₁ x₁ τ₁ w₂)
  let next : S₁ × T₁ → Transcript s₁ → Prefix s₂ → Prop :=
    fun x τ₁ p₂ => wins₁ x.1 τ₁ ∨ St₂ x.2 p₂
  have hjunc : ∀ x τ₁, ¬ wins₁ x.1 τ₁ → ¬ next x τ₁ (Prefix.empty s₂) := by
    rintro x τ₁ hw (hw' | hSt₂)
    · exact hw hw'
    · exact hinit₂ x.2 hSt₂
  have hsecond : ∀ x τ₁, RbrFrom s₂ V₂.samplers ε₂ (next x τ₁)
      (fun τ₂ => ∃ y w,
        ((V₁.outputOn x.1 τ₁).bind fun y₁ =>
            (V₂.outputOn x.2 τ₂).map fun y₂ => (y₁, y₂)) = some y ∧
          relProd rel₁' rel₂' y w ∧
          ¬ relProd rel₁ rel₂ x (E₁ x.1 τ₁ w.1, E₂ x.2 τ₂ w.2)) := by
    intro x τ₁
    by_cases hw₁ : wins₁ x.1 τ₁
    · refine RbrFrom.congr (fun _ => ⟨fun _ => Or.inl hw₁, fun _ => trivial⟩)
        (fun _ => Iff.rfl) (rbrFrom_true s₂ V₂.samplers ε₂ _)
    · refine RbrFrom.congr (fun p₂ => ⟨Or.inr, fun h => h.resolve_left hw₁⟩)
        (fun _ => Iff.rfl) (RbrFrom.mono_wins ?_ (hr₂ x.2))
      rintro τ₂ ⟨⟨y₁, y₂⟩, ⟨w₂, u₂⟩, hout, ⟨hrel₁', hrel₂'⟩, hnot⟩
      cases hout₁ : V₁.outputOn x.1 τ₁ with
      | none => simp [hout₁] at hout
      | some y₁' =>
        cases hout₂ : V₂.outputOn x.2 τ₂ with
        | none => simp [hout₁, hout₂] at hout
        | some y₂' =>
          simp only [hout₁, hout₂, Option.bind_some, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at hout
          obtain ⟨rfl, rfl⟩ := hout
          refine ⟨y₂', u₂, rfl, hrel₂', fun hrel₂ => hnot ⟨?_, hrel₂⟩⟩
          by_contra hnot₁
          exact hw₁ ⟨y₁', w₂, hout₁, hrel₁', hnot₁⟩
  refine ⟨fun x => compState s₁ s₂ (St₁ x.1) (next x),
    fun x => not_compState_empty (hr₁ x.1) (hjunc x) (hinit₁ x.1), fun x => ?_⟩
  refine RbrFrom.congr (fun _ => Iff.rfl) (fun τ => ?_)
    (rbrFrom_append s₁ s₂ V₁.samplers V₂.samplers ε₁ ε₂ (St₁ x.1) (wins₁ x.1) (next x) _
      (hr₁ x.1) (hjunc x) (hsecond x))
  rw [Verifier.outputOn_seqProd]
  rfl

/-- Round-by-round soundness composes across `Verifier.seqProd` when either input statement is
outside its language (`x ∉ L₁ ×ˢ L₂`, with `x.1 ∉ L₁` or `x.2 ∉ L₂`). -/
theorem Verifier.RbrSound.seqProd
    {V₁ : Verifier OracleSpec.empty s₁ S₁ S₂}
    {V₂ : Verifier OracleSpec.empty s₂ T₁ T₂}
    {L₁ : Set S₁} {L₁' : Set S₂} {L₂ : Set T₁} {L₂' : Set T₂}
    {ε₁ : PerChallenge (fun _ => ℝ≥0∞) s₁} {ε₂ : PerChallenge (fun _ => ℝ≥0∞) s₂}
    (h₁ : V₁.RbrSound L₁ L₁' ε₁) (h₂ : V₂.RbrSound L₂ L₂' ε₂) :
    (V₁.seqProd V₂).RbrSound (L₁ ×ˢ L₂) (L₁' ×ˢ L₂') (PerChallenge.append s₁ s₂ ε₁ ε₂) := by
  obtain ⟨St₁, hinit₁, hr₁⟩ := h₁
  obtain ⟨St₂, hinit₂, hr₂⟩ := h₂
  let wins₁ : S₁ → Transcript s₁ → Prop :=
    fun x₁ τ₁ => ∃ y₁ ∈ L₁', V₁.outputOn x₁ τ₁ = some y₁
  let S₁' : S₁ × T₁ → Prefix s₁ → Prop :=
    fun x p₁ => x.1 ∉ L₁ ∧ St₁ x.1 p₁
  let wins₁' : S₁ × T₁ → Transcript s₁ → Prop :=
    fun x τ₁ => x.1 ∉ L₁ ∧ wins₁ x.1 τ₁
  let next : S₁ × T₁ → Transcript s₁ → Prefix s₂ → Prop :=
    fun x τ₁ p₂ => wins₁' x τ₁ ∨ (x.1 ∈ L₁ ∧ St₂ x.2 p₂)
  have hr₁' : ∀ x : S₁ × T₁, RbrFrom s₁ V₁.samplers ε₁ (S₁' x) (wins₁' x) := by
    intro x
    by_cases hx₁ : x.1 ∈ L₁
    · refine RbrFrom.congr (fun _ => ?_) (fun _ => ?_) (rbrFrom_false s₁ V₁.samplers ε₁)
      · simp [S₁', hx₁]
      · simp [wins₁', hx₁]
    · exact RbrFrom.congr (fun _ => ⟨fun h => ⟨hx₁, h⟩, And.right⟩)
        (fun _ => ⟨fun h => ⟨hx₁, h⟩, And.right⟩) (hr₁ x.1)
  have hjunc : ∀ x : S₁ × T₁, x ∉ L₁ ×ˢ L₂ → ∀ τ₁, ¬ wins₁' x τ₁ →
      ¬ next x τ₁ (Prefix.empty s₂) := by
    rintro x hx τ₁ hw (hw' | ⟨hx₁, hSt₂⟩)
    · exact hw hw'
    · have hx₂ : x.2 ∉ L₂ := fun hx₂ => hx ⟨hx₁, hx₂⟩
      exact hinit₂ x.2 hx₂ hSt₂
  have hsecond : ∀ x : S₁ × T₁, x ∉ L₁ ×ˢ L₂ → ∀ τ₁,
      RbrFrom s₂ V₂.samplers ε₂ (next x τ₁)
        (fun τ₂ => ∃ y ∈ L₁' ×ˢ L₂',
          ((V₁.outputOn x.1 τ₁).bind fun y₁ =>
              (V₂.outputOn x.2 τ₂).map fun y₂ => (y₁, y₂)) = some y) := by
    intro x hx τ₁
    by_cases hw₁ : wins₁' x τ₁
    · refine RbrFrom.congr (fun _ => ⟨fun _ => Or.inl hw₁, fun _ => trivial⟩)
        (fun _ => Iff.rfl) (rbrFrom_true s₂ V₂.samplers ε₂ _)
    · by_cases hx₁ : x.1 ∈ L₁
      · refine RbrFrom.congr (fun p₂ => ?_) (fun _ => Iff.rfl)
          (RbrFrom.mono_wins ?_ (hr₂ x.2))
        · simp [next, hw₁, hx₁]
        · rintro τ₂ ⟨⟨y₁, y₂⟩, ⟨_, hy₂⟩, hout⟩
          cases hout₁ : V₁.outputOn x.1 τ₁ with
          | none => simp [hout₁] at hout
          | some y₁' =>
            cases hout₂ : V₂.outputOn x.2 τ₂ with
            | none => simp [hout₁, hout₂] at hout
            | some y₂' =>
              simp only [hout₁, hout₂, Option.bind_some, Option.map_some, Option.some.injEq,
                Prod.mk.injEq] at hout
              obtain ⟨rfl, rfl⟩ := hout
              exact ⟨y₂', hy₂, rfl⟩
      · refine RbrFrom.congr (fun _ => ?_) (fun τ₂ => ?_) (rbrFrom_false s₂ V₂.samplers ε₂)
        · simp [next, hw₁, hx₁]
        · constructor
          · exact False.elim
          · rintro ⟨⟨y₁, y₂⟩, ⟨hy₁, _⟩, hout⟩
            cases hout₁ : V₁.outputOn x.1 τ₁ with
            | none => simp [hout₁] at hout
            | some y₁' =>
              cases hout₂ : V₂.outputOn x.2 τ₂ with
              | none => simp [hout₁, hout₂] at hout
              | some y₂' =>
                simp only [hout₁, hout₂, Option.bind_some, Option.map_some, Option.some.injEq,
                  Prod.mk.injEq] at hout
                obtain ⟨rfl, rfl⟩ := hout
                exact hw₁ ⟨hx₁, y₁', hy₁, hout₁⟩
  refine ⟨fun x p => x ∈ L₁ ×ˢ L₂ ∨ compState s₁ s₂ (S₁' x) (next x) p,
    fun x hx hS => hS.elim hx
      (not_compState_empty (hr₁' x) (hjunc x hx) fun h => hinit₁ x.1 h.1 h.2),
    fun x => ?_⟩
  by_cases hx : x ∈ L₁ ×ˢ L₂
  · refine RbrFrom.congr (fun _ => ⟨fun _ => Or.inl hx, fun _ => trivial⟩)
      (fun _ => Iff.rfl) (rbrFrom_true (s₁ ++ s₂) (V₁.seqProd V₂).samplers _ _)
  · refine RbrFrom.congr (fun _ => ⟨Or.inr, fun h => h.resolve_left hx⟩) (fun τ => ?_)
      (rbrFrom_append s₁ s₂ V₁.samplers V₂.samplers ε₁ ε₂ (S₁' x) (wins₁' x) (next x) _
        (hr₁' x) (hjunc x hx) (hsecond x hx))
    rw [Verifier.outputOn_seqProd]

end SeqProd

/-! ### Identity, iteration, and bundles -/

/-- The identity reduction without rounds is round-by-round knowledge sound without error, with
the identity extractor. -/
theorem Reduction.id_rbrKnowledgeSound {S W : Type} (rel : S → W → Prop) :
    (Reduction.id (oP := OracleSpec.empty) (oV := OracleSpec.empty)
      (S := S) (W := W)).verifier.RbrKnowledgeSound rel rel (fun _ _ w => w) () := by
  refine ⟨fun _ _ => False, fun _ => not_false, fun x _ ⟨x', w, hout, hrel, hnot⟩ => ?_⟩
  obtain rfl : x = x' := Option.some.inj hout
  exact hnot hrel

/-- Composed straight-line extractor for the first `k` stages of `Reduction.iterate`. -/
@[expose] noncomputable def Verifier.extractIterate {s : ℕ → Spec} {S W : ℕ → Type}
    (R : (i : ℕ) →
      Reduction OracleSpec.empty OracleSpec.empty (s i) (S i) (W i) (S (i + 1)) (W (i + 1)))
    (E : (i : ℕ) → S i → Transcript (s i) → W (i + 1) → W i)
    (y₀ : (i : ℕ) → S i) :
    (k : ℕ) → S 0 → Transcript (iterSpec s k) → W k → W 0
  | 0 => fun _ _ w => w
  | k + 1 => (Reduction.iterate R k).verifier.extractAppend
      (Verifier.extractIterate R E y₀ k) (E k) (y₀ k)

/-- **Iterated round-by-round knowledge soundness**, with the composed stage extractors and the
per-round errors of the stages in order. -/
theorem Verifier.RbrKnowledgeSound.iterate {s : ℕ → Spec} {S W : ℕ → Type}
    {R : (i : ℕ) →
      Reduction OracleSpec.empty OracleSpec.empty (s i) (S i) (W i) (S (i + 1)) (W (i + 1))}
    {rel : (i : ℕ) → S i → W i → Prop}
    {E : (i : ℕ) → S i → Transcript (s i) → W (i + 1) → W i}
    {ε : (i : ℕ) → PerChallenge (fun _ => ℝ≥0∞) (s i)}
    (y₀ : (i : ℕ) → S i) (k : ℕ)
    (h : ∀ i < k, (R i).verifier.RbrKnowledgeSound (rel i) (rel (i + 1)) (E i) (ε i)) :
    (Reduction.iterate R k).verifier.RbrKnowledgeSound (rel 0) (rel k)
      (Verifier.extractIterate R E y₀ k) (PerChallenge.iterate ε k) := by
  induction k with
  | zero => exact Reduction.id_rbrKnowledgeSound (rel 0)
  | succ k ih =>
    exact (ih fun i hi => h i (by omega)).append (h k (by omega)) (y₀ k)

/-- **Round-by-round knowledge soundness of a bundle**, with the family of extractors
`fun x => E x.1 x.2` and the common per-round errors. -/
theorem Verifier.RbrKnowledgeSound.bundle {Θ : Type} {S₁ S₂ : Θ → Type} {W₁ W₂ : Type}
    {smp : PerChallenge ProbComp s}
    {V : (θ : Θ) → Verifier OracleSpec.empty s (S₁ θ) (S₂ θ)}
    (hsmp : ∀ θ, (V θ).samplers = smp)
    {rel₁ : (θ : Θ) → S₁ θ → W₁ → Prop} {rel₂ : (θ : Θ) → S₂ θ → W₂ → Prop}
    {E : (θ : Θ) → S₁ θ → Transcript s → W₂ → W₁}
    {ε : PerChallenge (fun _ => ℝ≥0∞) s}
    (h : ∀ θ, (V θ).RbrKnowledgeSound (rel₁ θ) (rel₂ θ) (E θ) ε) :
    (Verifier.bundle smp V).RbrKnowledgeSound
      (fun x w => rel₁ x.1 x.2 w) (fun y w => rel₂ y.1 y.2 w)
      (fun x τ w => E x.1 x.2 τ w) ε := by
  choose T hT hR using h
  refine ⟨fun x => T x.1 x.2, fun x => hT x.1 x.2, fun x => ?_⟩
  have hθ := hR x.1 x.2
  rw [hsmp] at hθ
  refine RbrFrom.congr (fun _ => Iff.rfl) (fun τ => ?_) hθ
  rw [Verifier.outputOn_bundle]
  constructor
  · rintro ⟨y, w, hout, hrel, hnot⟩
    exact ⟨⟨x.1, y⟩, w, by rw [hout]; rfl, hrel, hnot⟩
  · rintro ⟨⟨θ, y⟩, w, hout, hrel, hnot⟩
    cases hτ : (V x.1).outputOn x.2 τ with
    | none => rw [hτ] at hout; cases hout
    | some y' =>
      rw [hτ] at hout
      cases hout
      exact ⟨y', w, rfl, hrel, hnot⟩

end Cslib.Interactive
