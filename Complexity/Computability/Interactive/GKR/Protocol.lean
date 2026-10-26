/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Interactive.Bundle
public import Complexity.Computability.Interactive.Sumcheck
public import Complexity.Computability.Interactive.GKR.Summand
import Complexity.Foundations.FieldTheory.Finite.UnitSum
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Uniform
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# The GKR protocol

The GKR protocol [Goldwasser, Kalai, Rothblum][GoldwasserKalaiRothblum2015] lets a verifier check
the claim `D` about the outputs of a layered arithmetic circuit on an input `x` over a finite field
`F`, following [Thaler, §4.6][Thaler2022]. Claims about a layer are claims `W̃_j(z) = v` about the
multilinear extension of its gate values (`Cslib.Interactive.GKR.LayerClaim`).

* The **output step** (`LayeredCircuit.outputStep`) draws a uniform point `r` of the output layer
  and reduces the claim `D` to `W̃_depth(r) = D̃(r)`; a wrong `D` survives with probability at most
  `width depth / |F|` (Schwartz–Zippel).
* Each **layer** (`LayeredCircuit.layer`) reduces a claim about layer `i + 1` at `z` to a claim
  about layer `i`. It runs sumcheck on the GKR summand `f_z` (`sumcheckStage`, the library's
  `Sumcheck.round`s bundled over `z` by `Reduction.bundle`), and then the **line step**
  (`lineStep`): the prover sends the restriction `q` of `W̃_i` to the line through the two halves
  `y`, `w` of the last sumcheck point, the verifier checks the last sumcheck claim against
  `q 0 = W̃_i(y)` and `q 1 = W̃_i(w)`, draws `t` and keeps the claim `W̃_i(ℓ(t)) = q(t)`.
* The **input step** (`inputStep`) evaluates `x̃` at the last point.

The protocol (`LayeredCircuit.protocol`) is perfectly complete (`protocol_complete`) and sound with
error `(width depth + ∑_{i < depth} 5 · width i) / |F|` (`protocol_sound`): `2 / |F|` for each of
the `2 · width i` sumcheck rounds of layer `i`, `width i / |F|` for its line step, and
`width depth / |F|` for the output step. Both follow from the component theorems by the composition
theorems for completeness and round-by-round soundness. Verifier efficiency, which needs uniformity
of the circuit, is not addressed: the verifier evaluates the wiring extensions directly.

## Main definitions

* `Cslib.Interactive.GKR.LayeredCircuit.outputStep`, `Cslib.Interactive.GKR.LayeredCircuit.layer`,
  `Cslib.Interactive.GKR.LayeredCircuit.lineStep`,
  `Cslib.Interactive.GKR.LayeredCircuit.inputStep`: the stages.
* `Cslib.Interactive.GKR.LayeredCircuit.protocol`: the GKR protocol.

## Main results

* `Cslib.Interactive.GKR.LayeredCircuit.protocol_complete`: perfect completeness.
* `Cslib.Interactive.GKR.LayeredCircuit.protocol_sound`: soundness.
* `Cslib.Interactive.GKR.LayeredCircuit.toOuterMeasure_eval_eq_zero_le`: Schwartz–Zippel at a
  uniform point.

## References

* [S. Goldwasser, Y. T. Kalai, G. N. Rothblum, *Delegating computation: interactive proofs for
  muggles*][GoldwasserKalaiRothblum2015]
* [J. Thaler, *Proofs, Arguments, and Zero-Knowledge*][Thaler2022], Section 4.6
-/

@[expose] public section

namespace Cslib.Interactive.GKR

open MvPolynomial Cslib.BitString Spec
open scoped ENNReal

variable {F : Type} [Field F]

/-- The line through `y` (at `0`) and `w` (at `1`). -/
def line {k : ℕ} (y w : Fin k → F) (t : F) : Fin k → F := fun j => y j + t * (w j - y j)

theorem line_zero {k : ℕ} (y w : Fin k → F) : line y w 0 = y := by
  funext j
  simp [line]

theorem line_one {k : ℕ} (y w : Fin k → F) : line y w 1 = w := by
  funext j
  simp [line]

/-- The multilinear extension of `W`, restricted to the line through `y` and `w`: a polynomial of
degree at most `k` in the line parameter. -/
noncomputable def restrictLine {k : ℕ} (y w : Fin k → F) (W : (Fin k → Bool) → F) :
    Polynomial F :=
  (multilinearExtension W).eval₂ Polynomial.C
    fun j => Polynomial.C (w j - y j) * Polynomial.X + Polynomial.C (y j)

theorem eval_restrictLine {k : ℕ} (y w : Fin k → F) (W : (Fin k → Bool) → F) (t : F) :
    (restrictLine y w W).eval t = eval (line y w t) (multilinearExtension W) := by
  rw [restrictLine, FiniteField.eval_eval₂_line]
  congr 2
  funext j
  exact add_comm _ _

theorem natDegree_restrictLine_le {k : ℕ} (y w : Fin k → F) (W : (Fin k → Bool) → F) :
    (restrictLine y w W).natDegree ≤ k :=
  (FiniteField.natDegree_eval₂_line_le (multilinearExtension W) (w - y) y).trans
    ((totalDegree_multilinearExtension_le W).trans_eq (Fintype.card_fin k))

/-! ### The line step -/

/-- A claim about layer `j`: a point `z` and the claimed value of the multilinear extension of the
layer at `z`, stored as a sumcheck claim of round `0`. -/
abbrev LayerClaim (C : LayeredCircuit) (F : Type) (j : ℕ) : Type :=
  Σ _ : Fin (C.width j) → F, Sumcheck.Claim F 0

/-- A sumcheck claim of the last round of layer `i`, at the point `z` of layer `i + 1`. -/
abbrev SumcheckEnd (C : LayeredCircuit) (F : Type) (i : ℕ) : Type :=
  Σ _ : Fin (C.width (i + 1)) → F, Sumcheck.Claim F (C.width i + C.width i)

namespace LayeredCircuit

variable [Fintype F] [DecidableEq F] (C : LayeredCircuit) (i : ℕ)

/-- The combination the verifier checks against the last sumcheck claim:
`ãdd_i(z, y, w) (u + v) + m̃ult_i(z, y, w) u v`. -/
noncomputable def combine (z : Fin (C.width (i + 1)) → F) (y w : Fin (C.width i) → F) (u v : F) :
    F :=
  eval (Sum.elim z (Sum.elim y w)) (multilinearExtension (C.addPred (R := F) i)) * (u + v) +
    eval (Sum.elim z (Sum.elim y w)) (multilinearExtension (C.multPred (R := F) i)) * (u * v)

/-- The verifier's test of the line polynomial `q` against the last sumcheck claim `(z, r, c)`. -/
abbrev lineAccepts (x : SumcheckEnd C F i) (q : Polynomial F) : Prop :=
  q.natDegree ≤ C.width i ∧
    x.2.2 = C.combine i x.1 (x.2.1 ∘ Fin.castAdd _) (x.2.1 ∘ Fin.natAdd _) (q.eval 0) (q.eval 1)

/-- The claim about layer `i` at the point `t` of the line. -/
def lineClaim (x : SumcheckEnd C F i) (q : Polynomial F) (t : F) : LayerClaim C F i :=
  ⟨line (x.2.1 ∘ Fin.castAdd _) (x.2.1 ∘ Fin.natAdd _) t, (Fin.elim0, q.eval t)⟩

/-- **The line step** of layer `i`, for the values `W` of layer `i`. The prover sends the
restriction `q` of `W̃` to the line through the two halves `y`, `w` of the last sumcheck point; the
verifier checks the last sumcheck claim against `q 0 = W̃(y)` and `q 1 = W̃(w)`, draws `t` and
outputs the claim `W̃(ℓ(t)) = q(t)`. -/
noncomputable def lineStep (W : (Fin (C.width i) → Bool) → F) :
    Reduction OracleSpec.empty OracleSpec.empty (Sumcheck.roundSpec F) (SumcheckEnd C F i) Unit
      (LayerClaim C F i) Unit where
  prover x _ :=
    let q := restrictLine (x.2.1 ∘ Fin.castAdd _) (x.2.1 ∘ Fin.natAdd _) W
    pure (show ProbOracleComp OracleSpec.empty
        (Polynomial F × (F → ProbOracleComp OracleSpec.empty _)) from
      pure (q, fun t => pure (C.lineClaim i x q t, ())))
  verifier :=
    { samplers := (ProbComp.uniform F, ())
      decide := fun x c => do
        let q ← OracleComp.query (spec := OracleSpec.empty ⊕ₒ msgSpec (Sumcheck.roundSpec F))
          (.inr (.inl ()))
        return if C.lineAccepts i x q then some (C.lineClaim i x q c.1) else none }

theorem lineStep_outputOn (W : (Fin (C.width i) → Bool) → F) (x : SumcheckEnd C F i)
    (τ : Transcript (Sumcheck.roundSpec F)) :
    (C.lineStep i W).verifier.outputOn x τ =
      if C.lineAccepts i x τ.1 then some (C.lineClaim i x τ.1 τ.2.1) else none :=
  rfl

/-- The claims about layer `i` that are true. -/
def layerLang (W : (Fin (C.width i) → Bool) → F) : Set (LayerClaim C F i) :=
  {y | eval y.1 (multilinearExtension W) = y.2.2}

/-- The true last sumcheck claims of layer `i`. -/
def endLang (W : (Fin (C.width i) → Bool) → F) : Set (SumcheckEnd C F i) :=
  {x | x.2 ∈ language (Sumcheck.rel (C.summand i W x.1) (C.width i + C.width i))}

omit [Fintype F] [DecidableEq F] in
theorem mem_endLang (W : (Fin (C.width i) → Bool) → F) (x : SumcheckEnd C F i) :
    x ∈ C.endLang i W ↔ eval x.2.1 (C.summand i W x.1) = x.2.2 := by
  simp [endLang, language, Sumcheck.rel, Sumcheck.partialSum_self]

omit [Fintype F] [DecidableEq F] in
/-- The honest line polynomial passes the check exactly when the last sumcheck claim is true. -/
theorem combine_restrictLine (W : (Fin (C.width i) → Bool) → F) (x : SumcheckEnd C F i) :
    C.combine i x.1 (x.2.1 ∘ Fin.castAdd _) (x.2.1 ∘ Fin.natAdd _)
        ((restrictLine (x.2.1 ∘ Fin.castAdd _) (x.2.1 ∘ Fin.natAdd _) W).eval 0)
        ((restrictLine (x.2.1 ∘ Fin.castAdd _) (x.2.1 ∘ Fin.natAdd _) W).eval 1) =
      eval x.2.1 (C.summand i W x.1) := by
  rw [eval_restrictLine, eval_restrictLine, line_zero, line_one, combine]
  conv_rhs => rw [← Fin.append_castAdd_natAdd (f := x.2.1)]
  exact (C.eval_summand i W x.1 _ _).symm

/-- **The line step is perfectly complete.** -/
theorem lineStep_complete (W : (Fin (C.width i) → Bool) → F) :
    (C.lineStep i W).Complete World.plain (fun x _ => x ∈ C.endLang i W)
      (fun y _ => y ∈ C.layerLang i W) 0 := by
  intro x w hxw
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  simp only [lineStep, runStrategy, plainLaw_bind, plainLaw_pure, plainLaw_sample, PMF.pure_bind,
    PMF.bind_bind]
  have hacc : C.lineAccepts i x
      (restrictLine (x.2.1 ∘ Fin.castAdd _) (x.2.1 ∘ Fin.natAdd _) W) :=
    ⟨natDegree_restrictLine_le _ _ W,
      ((C.mem_endLang i W x).mp hxw).symm.trans (C.combine_restrictLine i W x).symm⟩
  rw [PMF.toOuterMeasure_bind_apply]
  refine Probability.PMF.tsum_mul_le_of_forall_le _ fun t => le_of_eq ?_
  refine (PMF.toOuterMeasure_pure_apply _ _).trans (ite_eq_right fun h => h ⟨?_, ?_⟩)
  · exact (C.lineStep_outputOn i W x _).trans (ite_eq_left hacc)
  · exact (eval_restrictLine _ _ W t).symm

/-- **The line step is round-by-round sound** with error `width i / |F|`: a false last sumcheck
claim forces a line polynomial other than the true restriction, which agrees with it at a random
point with probability at most `width i / |F|`. -/
theorem lineStep_rbrSound (W : (Fin (C.width i) → Bool) → F) :
    (C.lineStep i W).verifier.RbrSound (C.endLang i W) (C.layerLang i W)
      ((C.width i : ℝ≥0∞) / Fintype.card F, ()) := by
  refine ⟨fun x p => match p with
    | none => x ∈ C.endLang i W
    | some (_, none) => x ∈ C.endLang i W
    | some (q, some (t, _)) => x ∈ C.endLang i W ∨ (C.lineAccepts i x q ∧
        q.eval t = (restrictLine (x.2.1 ∘ Fin.castAdd _) (x.2.1 ∘ Fin.natAdd _) W).eval t),
    fun x hx h => hx h, fun x => ⟨fun hS _ h => hS h, fun q => ⟨?_, fun t => ?_⟩⟩⟩
  · intro hS
    change x ∉ C.endLang i W at hS
    change (ProbComp.eval (ProbComp.uniform F)).toOuterMeasure {t | x ∈ C.endLang i W ∨
      (C.lineAccepts i x q ∧ q.eval t =
        (restrictLine (x.2.1 ∘ Fin.castAdd _) (x.2.1 ∘ Fin.natAdd _) W).eval t)} ≤
          (C.width i : ℝ≥0∞) / Fintype.card F
    by_cases hacc : C.lineAccepts i x q
    · set q' := restrictLine (x.2.1 ∘ Fin.castAdd _) (x.2.1 ∘ Fin.natAdd _) W
      have hne : q - q' ≠ 0 := by
        refine sub_ne_zero.mpr fun h => hS ?_
        rw [C.mem_endLang, ← C.combine_restrictLine i W x]
        exact (h ▸ hacc.2).symm
      classical
      rw [ProbComp.eval_uniform, Probability.PMF.toOuterMeasure_uniformOfFintype, div_eq_mul_inv]
      gcongr
      have hsub : Finset.univ.filter (· ∈ {t | x ∈ C.endLang i W ∨
          (C.lineAccepts i x q ∧ q.eval t = q'.eval t)}) ⊆ (q - q').roots.toFinset := by
        intro t ht
        simp only [Finset.mem_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at ht
        rcases ht with ht | ht
        · exact absurd ht hS
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot,
          Polynomial.eval_sub, ht.2, sub_self]
      exact_mod_cast (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' _).trans ((Polynomial.natDegree_sub_le _ _).trans
          (max_le hacc.1 (natDegree_restrictLine_le _ _ W)))))
    · simp [hacc, hS]
  · rintro hS ⟨y, hy, hout⟩
    rw [lineStep_outputOn] at hout
    split_ifs at hout with hacc
    obtain rfl := Option.some.inj hout
    exact hS (Or.inr ⟨hacc, hy.symm.trans (eval_restrictLine _ _ W t).symm⟩)

/-! ### The sumcheck stage and one layer -/

/-- The number of sumcheck variables of layer `i`. -/
abbrev sumcheckVars (i : ℕ) : ℕ := C.width i + C.width i

private theorem samplers_round {n : ℕ} (d : ℕ) (P Q : MvPolynomial (Fin n) F) (k : ℕ) :
    (Sumcheck.round d P k).verifier.samplers = (Sumcheck.round d Q k).verifier.samplers :=
  rfl

private theorem samplers_iterate_succ {n : ℕ} (d : ℕ) (P : MvPolynomial (Fin n) F) (k : ℕ) :
    (Reduction.iterate (s := fun _ => Sumcheck.roundSpec F) (S := Sumcheck.Claim F)
      (W := fun _ => Unit) (Sumcheck.round d P) (k + 1)).verifier.samplers =
    PerChallenge.append _ _
      (Reduction.iterate (s := fun _ => Sumcheck.roundSpec F) (S := Sumcheck.Claim F)
        (W := fun _ => Unit) (Sumcheck.round d P) k).verifier.samplers
      (Sumcheck.round d P k).verifier.samplers :=
  rfl

/-- The challenge samplers of `k` sumcheck rounds: one uniform field element per round. -/
noncomputable def sumcheckSamplers :
    (k : ℕ) → PerChallenge ProbComp (iterSpec (fun _ => Sumcheck.roundSpec F) k)
  | 0 => ()
  | k + 1 => PerChallenge.append _ _ (sumcheckSamplers k) (ProbComp.uniform F, ())

/-- The challenge samplers of the iterated sumcheck rounds do not depend on the polynomial. -/
theorem samplers_iterate_round {n : ℕ} (d : ℕ) (P : MvPolynomial (Fin n) F) (k : ℕ) :
    (Reduction.iterate (s := fun _ => Sumcheck.roundSpec F) (S := Sumcheck.Claim F)
      (W := fun _ => Unit) (Sumcheck.round d P) k).verifier.samplers = sumcheckSamplers k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [samplers_iterate_succ, ih]
    rfl

/-- The sumcheck stage of layer `i`, for the values `W` of layer `i`: on a claim `(z, v)` about
layer `i + 1`, sumcheck on the summand `f_z`, bundled over `z`. -/
noncomputable def sumcheckStage (W : (Fin (C.width i) → Bool) → F) :
    Reduction OracleSpec.empty OracleSpec.empty
      (iterSpec (fun _ => Sumcheck.roundSpec F) (C.sumcheckVars i)) (LayerClaim C F (i + 1)) Unit
      (SumcheckEnd C F i) Unit :=
  Reduction.bundle
    (sumcheckSamplers (F := F) (C.sumcheckVars i))
    fun z => Reduction.iterate (s := fun _ => Sumcheck.roundSpec F) (S := Sumcheck.Claim F)
      (W := fun _ => Unit) (Sumcheck.round 2 (C.summand i W z)) (C.sumcheckVars i)

omit [Fintype F] [DecidableEq F] in
/-- A round-`0` sumcheck claim on the summand is a claim about the multilinear extension of the
layer above. -/
theorem mem_language_rel_zero (W : (Fin (C.width i) → Bool) → F) (x : LayerClaim C F (i + 1)) :
    x.2 ∈ language (Sumcheck.rel (C.summand i W x.1) 0) ↔
      x ∈ C.layerLang (i + 1) (C.step i W) := by
  have hpoint : ∀ b : Fin (C.sumcheckVars i - 0) → Bool,
      Sumcheck.point x.2.1 b = bitPoint (R := F) b := by
    intro b
    funext j
    simp only [Sumcheck.point, Nat.not_lt_zero, dite_false, bitPoint, bitVal]
    rfl
  simp only [language, Sumcheck.rel, Sumcheck.partialSum, hpoint, layerLang, Set.mem_ofPred_eq,
    exists_const]
  rw [← C.sum_eval_summand i W x.1]
  rfl

/-- The sumcheck stage is perfectly complete. -/
theorem sumcheckStage_complete (W : (Fin (C.width i) → Bool) → F) :
    (C.sumcheckStage i W).Complete World.plain (fun x _ => x ∈ C.layerLang (i + 1) (C.step i W))
      (fun y _ => y ∈ C.endLang i W) 0 := by
  have h := Reduction.Complete.bundle
    (smp := sumcheckSamplers (F := F) (C.sumcheckVars i))
    (R := fun z => Reduction.iterate (s := fun _ => Sumcheck.roundSpec F) (S := Sumcheck.Claim F)
      (W := fun _ => Unit) (Sumcheck.round 2 (C.summand i W z)) (C.sumcheckVars i))
    (fun z => samplers_iterate_round 2 _ _)
    (rel₁ := fun z => Sumcheck.rel (C.summand i W z) 0)
    (rel₂ := fun z => Sumcheck.rel (C.summand i W z) (C.sumcheckVars i)) (ε := 0)
    fun z => by
      have := Reduction.Complete.iterate (rel := Sumcheck.rel (C.summand i W z))
        (ε := fun _ => 0) (C.sumcheckVars i)
        fun j hj => Sumcheck.round_complete 2 _ (C.degreeOf_summand_le i W z) hj
      simpa using this
  intro x w hxw
  refine le_trans (le_of_eq (congrArg _ (Set.ext fun r => ?_))) (h x w ?_)
  · simp only [Set.mem_ofPred_eq, endLang, language]
    exact not_congr (and_congr_right fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨_, h⟩⟩)
  · exact ((C.mem_language_rel_zero i W x).mpr hxw).choose_spec

/-- The sumcheck stage is round-by-round sound with error `2 / |F|` per round. -/
theorem sumcheckStage_rbrSound (W : (Fin (C.width i) → Bool) → F) :
    (C.sumcheckStage i W).verifier.RbrSound (C.layerLang (i + 1) (C.step i W)) (C.endLang i W)
      (PerChallenge.iterate (fun _ => ((2 : ℝ≥0∞) / Fintype.card F, ())) (C.sumcheckVars i)) := by
  have h := Verifier.RbrSound.bundle
    (smp := sumcheckSamplers (F := F) (C.sumcheckVars i))
    (V := fun z => (Reduction.iterate (s := fun _ => Sumcheck.roundSpec F)
      (S := Sumcheck.Claim F) (W := fun _ => Unit) (Sumcheck.round 2 (C.summand i W z))
      (C.sumcheckVars i)).verifier)
    (fun z => samplers_iterate_round 2 _ _)
    (L₁ := fun z => language (Sumcheck.rel (C.summand i W z) 0))
    (L₂ := fun z => language (Sumcheck.rel (C.summand i W z) (C.sumcheckVars i)))
    fun z => Verifier.RbrSound.iterate (L := fun j => language (Sumcheck.rel (C.summand i W z) j))
      (C.sumcheckVars i) fun j hj =>
        Sumcheck.round_rbrSound 2 _ (C.degreeOf_summand_le i W z) hj
  have hL : {x : LayerClaim C F (i + 1) | x.2 ∈ language (Sumcheck.rel (C.summand i W x.1) 0)} =
      C.layerLang (i + 1) (C.step i W) := Set.ext fun x => C.mem_language_rel_zero i W x
  rw [hL] at h
  exact h

/-! ### The output and input steps -/

/-- The single round of the output step: the verifier draws a point of the output layer. -/
abbrev outputSpec : Spec := [.verifier (Fin (C.width C.depth) → F)]

/-- **The output step**: on claimed outputs `D`, the verifier draws a point `r` of the output layer
and turns the claim into `W̃_depth(r) = D̃(r)`. -/
noncomputable def outputStep :
    Reduction OracleSpec.empty OracleSpec.empty (C.outputSpec (F := F))
      ((Fin (C.width C.depth) → Bool) → F) Unit (LayerClaim C F C.depth) Unit where
  prover D _ :=
    pure (show (Fin (C.width C.depth) → F) →
        ProbOracleComp OracleSpec.empty (LayerClaim C F C.depth × Unit) from
      fun r => pure (⟨r, (Fin.elim0, eval r (multilinearExtension D))⟩, ()))
  verifier :=
    { samplers := (ProbComp.uniform _, ())
      decide := fun D c => pure (some ⟨c.1, (Fin.elim0, eval c.1 (multilinearExtension D))⟩) }

omit [DecidableEq F] in
theorem outputStep_outputOn (D : (Fin (C.width C.depth) → Bool) → F)
    (τ : Transcript (C.outputSpec (F := F))) :
    (C.outputStep (F := F)).verifier.outputOn D τ =
      some ⟨τ.1, (Fin.elim0, eval τ.1 (multilinearExtension D))⟩ :=
  rfl

/-- **The input step**: the verifier checks the claim about the input layer by evaluating the
multilinear extension of the input. -/
noncomputable def inputStep (x : (Fin (C.width 0) → Bool) → F) :
    Reduction OracleSpec.empty OracleSpec.empty [] (LayerClaim C F 0) Unit Unit Unit where
  prover _ _ := pure ((), ())
  verifier :=
    { samplers := ()
      decide := fun y _ =>
        pure (if eval y.1 (multilinearExtension x) = y.2.2 then some () else none) }

omit [DecidableEq F] in
/-- **Schwartz–Zippel** at a uniform point: a nonzero polynomial of total degree at most `d`
vanishes with probability at most `d / |F|`. -/
theorem toOuterMeasure_eval_eq_zero_le {k d : ℕ} {p : MvPolynomial (Fin k) F} (hp : p ≠ 0)
    (hdeg : p.totalDegree ≤ d) :
    (ProbComp.eval (ProbComp.uniform (Fin k → F))).toOuterMeasure {r | eval r p = 0} ≤
      (d : ℝ≥0∞) / Fintype.card F := by
  classical
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hsz := schwartz_zippel_totalDegree hp (Finset.univ : Finset F)
  rw [Fintype.piFinset_univ, Finset.card_univ, div_le_div_iff₀ (by positivity) (by positivity)]
    at hsz
  have hN : (Finset.univ.filter fun r : Fin k → F => eval r p = 0).card * Fintype.card F ≤
      d * Fintype.card F ^ k := by
    have : ((Finset.univ.filter fun r : Fin k → F => eval r p = 0).card * Fintype.card F : ℚ≥0) ≤
        d * Fintype.card F ^ k := hsz.trans (by gcongr)
    exact_mod_cast this
  rw [ProbComp.eval_uniform, Probability.PMF.toOuterMeasure_uniformOfFintype, Fintype.card_fun,
    Fintype.card_fin]
  set N := (Finset.univ.filter (· ∈ {r : Fin k → F | eval r p = 0})).card
  have hN' : ((N : ℝ≥0∞) * Fintype.card F) ≤ d * (Fintype.card F : ℝ≥0∞) ^ k := by
    have : N = (Finset.univ.filter fun r : Fin k → F => eval r p = 0).card := rfl
    rw [this]
    exact_mod_cast hN
  have hq0 : (Fintype.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast hq.ne'
  have hqt : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hk0 : (Fintype.card F : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ hq0
  have hkt : (Fintype.card F : ℝ≥0∞) ^ k ≠ ⊤ := ENNReal.pow_ne_top hqt
  push_cast
  calc (N : ℝ≥0∞) * ((Fintype.card F : ℝ≥0∞) ^ k)⁻¹
      = N * ((Fintype.card F : ℝ≥0∞) ^ k)⁻¹ *
          ((Fintype.card F : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)⁻¹) := by
        rw [ENNReal.mul_inv_cancel hq0 hqt, mul_one]
    _ = (N * Fintype.card F) * ((Fintype.card F : ℝ≥0∞) ^ k)⁻¹ *
          (Fintype.card F : ℝ≥0∞)⁻¹ := by ring
    _ ≤ (d * (Fintype.card F : ℝ≥0∞) ^ k) * ((Fintype.card F : ℝ≥0∞) ^ k)⁻¹ *
          (Fintype.card F : ℝ≥0∞)⁻¹ := by gcongr
    _ = d / Fintype.card F := by
        rw [mul_assoc (d : ℝ≥0∞), ENNReal.mul_inv_cancel hk0 hkt, mul_one, div_eq_mul_inv]

omit [DecidableEq F] in
omit [Fintype F] [DecidableEq F] in
theorem totalDegree_multilinearExtension_sub_le {k : ℕ} (D E : (Fin k → Bool) → F) :
    (multilinearExtension D - multilinearExtension E).totalDegree ≤ k := by
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · simpa using totalDegree_multilinearExtension_le (R := F) D
  · simpa using totalDegree_multilinearExtension_le (R := F) E

omit [Fintype F] [DecidableEq F] in
/-- Distinct functions on the cube have distinct multilinear extensions. -/
theorem multilinearExtension_sub_ne_zero {k : ℕ} {D E : (Fin k → Bool) → F} (h : D ≠ E) :
    multilinearExtension D - multilinearExtension E ≠ 0 := by
  refine fun h0 => h (funext fun b => ?_)
  have := congrArg (eval (bitPoint (R := F) b)) (sub_eq_zero.mp h0)
  simpa [eval_multilinearExtension] using this

omit [DecidableEq F] in
/-- **The output step is perfectly complete.** -/
theorem outputStep_complete (x : (Fin (C.width 0) → Bool) → F) :
    (C.outputStep (F := F)).Complete World.plain (fun D _ => D = C.output x)
      (fun y _ => y ∈ C.layerLang C.depth (C.value x C.depth)) 0 := by
  rintro D w rfl
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  simp only [outputStep, runStrategy, plainLaw_bind, plainLaw_pure, plainLaw_sample, PMF.pure_bind]
  rw [PMF.toOuterMeasure_bind_apply]
  refine Probability.PMF.tsum_mul_le_of_forall_le _ fun r => le_of_eq ?_
  exact (PMF.toOuterMeasure_pure_apply _ _).trans (ite_eq_right fun h => h ⟨rfl, rfl⟩)

omit [DecidableEq F] in
/-- **The output step is round-by-round sound** with error `width depth / |F|`, by
Schwartz–Zippel for the multilinear extensions of the claimed and the true outputs. -/
theorem outputStep_rbrSound (x : (Fin (C.width 0) → Bool) → F) :
    (C.outputStep (F := F)).verifier.RbrSound {C.output x}
      (C.layerLang C.depth (C.value x C.depth)) ((C.width C.depth : ℝ≥0∞) / Fintype.card F, ())
      := by
  refine ⟨fun D p => match p with
    | none => D = C.output x
    | some (r, _) => eval r (multilinearExtension D) = eval r (multilinearExtension (C.output x)),
    fun D hD h => hD h, fun D => ⟨?_, fun r => ?_⟩⟩
  · intro hD
    change D ≠ C.output x at hD
    change (ProbComp.eval (ProbComp.uniform _)).toOuterMeasure
      {r | eval r (multilinearExtension D) = eval r (multilinearExtension (C.output x))} ≤ _
    have hset : {r : Fin (C.width C.depth) → F | eval r (multilinearExtension D) =
        eval r (multilinearExtension (C.output x))} =
        {r | eval r (multilinearExtension D - multilinearExtension (C.output x)) = 0} := by
      ext r
      simp [sub_eq_zero]
    rw [hset]
    exact toOuterMeasure_eval_eq_zero_le (multilinearExtension_sub_ne_zero hD)
      (totalDegree_multilinearExtension_sub_le _ _)
  · rintro hS ⟨y, hy, hout⟩
    rw [outputStep_outputOn] at hout
    obtain rfl := Option.some.inj hout
    exact hS hy.symm

omit [Fintype F] in
/-- **The input step is perfectly complete.** -/
theorem inputStep_complete (x : (Fin (C.width 0) → Bool) → F) :
    (C.inputStep x).Complete World.plain (fun y _ => y ∈ C.layerLang 0 x) Accept 0 := by
  intro y w hyw
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  simp only [inputStep, runStrategy, plainLaw_bind, plainLaw_pure, PMF.pure_bind]
  refine le_of_eq ((PMF.toOuterMeasure_pure_apply _ _).trans
    (ite_eq_right fun h => h ⟨?_, trivial⟩))
  exact ite_eq_left hyw

omit [Fintype F] in
/-- **The input step is round-by-round sound** without error. -/
theorem inputStep_rbrSound (x : (Fin (C.width 0) → Bool) → F) :
    (C.inputStep x).verifier.RbrSound (C.layerLang 0 x) Set.univ () := by
  refine ⟨fun y _ => y ∈ C.layerLang 0 x, fun y hy h => hy h, fun y hS ⟨y', _, hout⟩ => hS ?_⟩
  by_contra h
  simp only [layerLang, Set.mem_ofPred_eq] at h
  simp [Verifier.outputOn, inputStep, h] at hout

/-! ### The protocol -/

/-- The rounds of layer `i`: sumcheck on `2 · width i` variables, then the line step. -/
abbrev layerSpec (i : ℕ) : Spec :=
  iterSpec (fun _ => Sumcheck.roundSpec F) (C.sumcheckVars i) ++ Sumcheck.roundSpec F

/-- **One layer of GKR**: a claim about layer `i + 1` becomes a claim about layer `i`. -/
noncomputable def layer (x : (Fin (C.width 0) → Bool) → F) (i : ℕ) :
    Reduction OracleSpec.empty OracleSpec.empty (C.layerSpec (F := F) i)
      (LayerClaim C F (i + 1)) Unit (LayerClaim C F i) Unit :=
  (C.sumcheckStage i (C.value x i)).append (C.lineStep i (C.value x i))

/-- The per-round errors of layer `i`: `2 / |F|` per sumcheck round and `width i / |F|` for the
line step. -/
noncomputable def layerError (i : ℕ) : PerChallenge (fun _ => ℝ≥0∞) (C.layerSpec (F := F) i) :=
  PerChallenge.append _ _
    (PerChallenge.iterate (fun _ => ((2 : ℝ≥0∞) / Fintype.card F, ())) (C.sumcheckVars i))
    ((C.width i : ℝ≥0∞) / Fintype.card F, ())

theorem layer_complete (x : (Fin (C.width 0) → Bool) → F) (i : ℕ) :
    (C.layer x i).Complete World.plain
      (fun y _ => y ∈ C.layerLang (i + 1) (C.value x (i + 1)))
      (fun y _ => y ∈ C.layerLang i (C.value x i)) 0 := by
  have h := (C.sumcheckStage_complete i (C.value x i)).append
    (C.lineStep_complete i (C.value x i))
  rw [add_zero] at h
  exact h

theorem layer_rbrSound (x : (Fin (C.width 0) → Bool) → F) (i : ℕ) :
    (C.layer x i).verifier.RbrSound (C.layerLang (i + 1) (C.value x (i + 1)))
      (C.layerLang i (C.value x i)) (C.layerError i) :=
  (C.sumcheckStage_rbrSound i (C.value x i)).append (C.lineStep_rbrSound i (C.value x i))

omit [DecidableEq F] in
theorem sum_layerError (i : ℕ) :
    PerChallenge.sum (C.layerSpec (F := F) i) (C.layerError i) =
      (C.sumcheckVars i : ℝ≥0∞) * (2 / Fintype.card F) + C.width i / Fintype.card F := by
  rw [layerError, PerChallenge.sum_append, PerChallenge.sum_iterate]
  simp [PerChallenge.sum]

/-- The rounds from layer `m` down to the input. -/
def descendSpec : ℕ → Spec
  | 0 => []
  | m + 1 => C.layerSpec (F := F) m ++ descendSpec m

/-- The layers from `m` down to the input, followed by the input step. -/
noncomputable def descend (x : (Fin (C.width 0) → Bool) → F) :
    (m : ℕ) → Reduction OracleSpec.empty OracleSpec.empty (C.descendSpec (F := F) m)
      (LayerClaim C F m) Unit Unit Unit
  | 0 => C.inputStep x
  | m + 1 => (C.layer x m).append (descend x m)

/-- The per-round errors of `descend`. -/
noncomputable def descendError : (m : ℕ) → PerChallenge (fun _ => ℝ≥0∞) (C.descendSpec (F := F) m)
  | 0 => ()
  | m + 1 => PerChallenge.append _ _ (C.layerError m) (descendError m)

theorem descend_complete (x : (Fin (C.width 0) → Bool) → F) :
    ∀ m, (C.descend x m).Complete World.plain
      (fun y _ => y ∈ C.layerLang m (C.value x m)) Accept 0
  | 0 => C.inputStep_complete x
  | m + 1 => by
    have h := (C.layer_complete x m).append (descend_complete x m)
    rw [add_zero] at h
    exact h

theorem descend_rbrSound (x : (Fin (C.width 0) → Bool) → F) :
    ∀ m, (C.descend x m).verifier.RbrSound (C.layerLang m (C.value x m)) Set.univ
      (C.descendError m)
  | 0 => C.inputStep_rbrSound x
  | m + 1 => (C.layer_rbrSound x m).append (descend_rbrSound x m)

omit [DecidableEq F] in
theorem sum_descendError :
    ∀ m, PerChallenge.sum (C.descendSpec (F := F) m) (C.descendError m) =
      ∑ i ∈ Finset.range m,
        ((C.sumcheckVars i : ℝ≥0∞) * (2 / Fintype.card F) + C.width i / Fintype.card F)
  | 0 => rfl
  | m + 1 => by
    change PerChallenge.sum (C.layerSpec m ++ C.descendSpec m)
      (PerChallenge.append _ _ (C.layerError m) (C.descendError m)) = _
    rw [PerChallenge.sum_append, sum_layerError, sum_descendError m, Finset.sum_range_succ,
      add_comm]

/-- **The GKR protocol** for the claim that the circuit outputs `D` on the input `x`: the output
step, then the layers from the output down to the input, then the input step. -/
noncomputable def protocol (x : (Fin (C.width 0) → Bool) → F) :
    Reduction OracleSpec.empty OracleSpec.empty
      (C.outputSpec (F := F) ++ C.descendSpec (F := F) C.depth)
      ((Fin (C.width C.depth) → Bool) → F) Unit Unit Unit :=
  (C.outputStep (F := F)).append (C.descend x C.depth)

/-- **Completeness of GKR**: the honest prover convinces the verifier of the true output with
probability one. -/
theorem protocol_complete (x : (Fin (C.width 0) → Bool) → F) :
    (C.protocol x).Complete World.plain (fun D _ => D = C.output x) Accept 0 := by
  have h := (C.outputStep_complete x).append (C.descend_complete x C.depth)
  rw [add_zero] at h
  exact h

/-- **Soundness of GKR** [Goldwasser, Kalai, Rothblum][GoldwasserKalaiRothblum2015],
[Thaler, §4.6][Thaler2022]: any prover convinces the verifier of a wrong output with probability
at most `(width depth + ∑_{i < depth} 5 · width i) / |F|`. -/
theorem protocol_sound (x : (Fin (C.width 0) → Bool) → F) :
    (C.protocol x).verifier.Sound (oP := OracleSpec.empty) World.plain {C.output x} Set.univ
      ((C.width C.depth + ∑ i ∈ Finset.range C.depth, 5 * C.width i : ℕ) / Fintype.card F) := by
  have h := ((C.outputStep_rbrSound x).append (C.descend_rbrSound x C.depth)).sound
  rw [PerChallenge.sum_append, sum_descendError] at h
  convert h using 1
  · rfl
  · simp only [PerChallenge.sum, add_zero, sumcheckVars, Nat.cast_add, Nat.cast_sum, Nat.cast_mul,
      Nat.cast_ofNat]
    rw [ENNReal.add_div]
    simp only [div_eq_mul_inv, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

end LayeredCircuit

end Cslib.Interactive.GKR
