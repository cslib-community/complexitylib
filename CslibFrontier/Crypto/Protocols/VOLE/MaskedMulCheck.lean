/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.VOLE.World
public import CslibFrontier.Crypto.Protocols.VOLE.BatchMulCheck
public import CslibFrontier.Computability.Interactive.Security
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Interactive
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PMFSwap

/-!
# Full honest receiver views of masked VOLE multiplication checks

One fresh ideal VOLE coordinate blinds both affine reply coefficients. All wire corrections are
sent before the verifier's uniform public vector of weights. The mask coordinate receives no
correction and is used once. The prover accesses only the sender setup oracle; the receiver's
key and tags remain private. The full receiver view includes that private share and every public
message, not just the affine reply.

This is the masking step in [BaumEtAl2023FAEST], §2.3.2, printed pp.12–13, adapted to full-field
wires and independent vector weights. The source uses subfield wires and scalar-power batching.
The result concerns one honest execution in an ideal correlation world; it does not establish
malicious-verifier ZK, VOLE-in-the-head security, or a certified efficient implementation.

## Main definitions

* `maskedMulCheckSpec`, `maskedMulCheck`: the correction/challenge/reply interaction.
* `maskedMulCheckView`: the complete view in the cached ideal VOLE world.
* `maskedMulCheckSimulate`: a witness-free simulator for that view.

## Main results

* `maskedMulCheck_complete`: completeness of the actual reduction in the ideal world.
* `maskedMulCheckView_eq_simulate`: exact simulation of the entire honest receiver view.
* `maskedMulCheckView_closeTo_simulate`: the corresponding zero-error closeness statement.
* `maskedMulCheckSimulate_accepts`: every simulated view satisfies verification.

The honest-view law needs only a finite commutative ring. Soundness bounds from the preceding
modules still require a field and are not strengthened here.

## References

* [C. Baum et al., *FAEST: Algorithm Specifications*, version 1.0][BaumEtAl2023FAEST]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.VOLE

open Probability Interactive Interactive.Spec
open scoped BigOperators

variable {F ι : Type} {n : ℕ}

/-- Wire corrections, public weights, then the blinded affine coefficients. This specializes
the existing three-round message shape; it does not assert Sigma-protocol security properties. -/
abbrev maskedMulCheckSpec (F ι : Type) (n : ℕ) : Spec :=
  SigmaProtocol.sigmaSpec (Fin n → F) (ι → F) (F × F)

variable [CommRing F] [Fintype ι]

/-- Honest reply, using the final setup coordinate only as a fresh affine mask.
The public index maps identify the two inputs and output of each multiplication gate. -/
def maskedMulCheckReply (left right output : ι → Fin n) (w : Fin n → F)
    (u v : Fin (n + 1) → F) (r : ι → F) : F × F :=
  ((∑ i, r i * voleMulCrossTerm (w (left i)) (v (left i).castSucc)
      (w (right i)) (v (right i).castSucc) (v (output i).castSucc)) + u (Fin.last n),
    (∑ i, r i * voleMulConstTerm (v (left i).castSucc) (v (right i).castSucc)) +
      v (Fin.last n))

/-- The receiver's weighted check, including the tag of the fresh mask coordinate. -/
def maskedMulCheckValue (left right output : ι → Fin n) (delta : F)
    (q : Fin (n + 1) → F) (d : Fin n → F) (r : ι → F) : F :=
  let adjusted := voleAdjustReceiver (Fin.init q) d delta
  (∑ i, r i * (adjusted (left i) * adjusted (right i) - adjusted (output i) * delta)) +
    q (Fin.last n)

/-- Adding the fresh VOLE mask preserves honest completeness at every receiver key. -/
theorem maskedMulCheckReply_correct (left right output : ι → Fin n) (w : Fin n → F)
    (c : VOLECorrelation F (n + 1)) (hc : c.Valid) (r : ι → F)
    (h : ∀ i, w (left i) * w (right i) = w (output i)) :
    maskedMulCheckValue left right output c.delta c.w (voleCommitWitness w (Fin.init c.u)) r =
      (maskedMulCheckReply left right output w c.u c.v r).1 * c.delta +
        (maskedMulCheckReply left right output w c.u c.v r).2 := by
  have hadjust : voleAdjustReceiver (Fin.init c.w)
      (voleCommitWitness w (Fin.init c.u)) c.delta =
      fun j => w j * c.delta + c.v j.castSucc := by
    funext j
    simp only [voleAdjustReceiver, voleCommitWitness, Pi.sub_apply, Fin.init, hc j.castSucc]
    ring
  simp only [maskedMulCheckValue, hadjust]
  rw [voleMulCheck_sum r (fun i => w (left i)) (fun i => w (right i)) (fun i => w (output i))
    (fun i => c.v (left i).castSucc) (fun i => c.v (right i).castSucc)
    (fun i => c.v (output i).castSucc) c.delta h, hc (Fin.last n)]
  simp only [maskedMulCheckReply]
  ring

private def maskedSetupEquiv (left right output : ι → Fin n) (w : Fin n → F)
    (delta : F) (r : ι → F) :
    ((Fin (n + 1) → F) × (Fin (n + 1) → F)) ≃
      ((Fin (n + 1) → F) × (Fin n → F) × F) where
  toFun uv := ((voleSample uv.1 uv.2 delta).w, voleCommitWitness w (Fin.init uv.1),
    (maskedMulCheckReply left right output w uv.1 uv.2 r).1)
  invFun qda :=
    let uw := w - qda.2.1
    let vw := fun j : Fin n => qda.1 j.castSucc - uw j * delta
    let um := qda.2.2 - ∑ i, r i * voleMulCrossTerm (w (left i)) (vw (left i))
      (w (right i)) (vw (right i)) (vw (output i))
    let u := Fin.snoc uw um
    (u, fun j => qda.1 j - u j * delta)
  left_inv uv := by
    rcases uv with ⟨u, v⟩
    dsimp
    simp only [voleCommitWitness, sub_sub_cancel, maskedMulCheckReply,
      Fin.init, Pi.sub_apply]
    simp only [add_sub_cancel_left]
    rw [Fin.snoc_init_self]
    congr 1 with j : 1
    ring
  right_inv qda := by
    rcases qda with ⟨q, d, a⟩
    apply Prod.ext
    · funext j
      dsimp [voleSample]
      ring
    · apply Prod.ext
      · funext j
        simp [voleCommitWitness]
      · simp only [maskedMulCheckReply, Fin.snoc_castSucc, Fin.snoc_last]
        simp

variable [Fintype F] [DecidableEq F] [DecidableEq ι]

/-- The actual public-coin reduction. Setup is available only through the role-local oracles.
The prover fixes every correction before seeing the random weights and sends one masked reply. -/
noncomputable def maskedMulCheck (left right output : ι → Fin n) :
    Reduction (voleSenderSpec F (n + 1)) (voleReceiverSpec F (n + 1))
      (maskedMulCheckSpec F ι n) Unit (Fin n → F) Unit Unit where
  prover _ w := do
    let (u, v) ← ProbOracleComp.query ()
    return (show ProbOracleComp (voleSenderSpec F (n + 1))
      ((Fin n → F) × ((ι → F) → ProbOracleComp (voleSenderSpec F (n + 1))
        (ProbOracleComp (voleSenderSpec F (n + 1)) ((F × F) × (Unit × Unit))))) from
      pure (voleCommitWitness w (Fin.init u), fun r => pure
        (pure (maskedMulCheckReply left right output w u v r, ((), ())))))
  verifier := {
    samplers := (ProbComp.uniform (ι → F), ())
    decide := fun _ challenges => do
      let (delta, q) ← OracleComp.query
        (spec := voleReceiverSpec F (n + 1) ⊕ₒ msgSpec (maskedMulCheckSpec F ι n)) (.inl ())
      let d : Fin n → F ← OracleComp.query
        (spec := voleReceiverSpec F (n + 1) ⊕ₒ msgSpec (maskedMulCheckSpec F ι n))
        (.inr (.inl ()))
      let ab : F × F ← OracleComp.query
        (spec := voleReceiverSpec F (n + 1) ⊕ₒ msgSpec (maskedMulCheckSpec F ι n))
        (.inr (.inr (.inl ())))
      return if maskedMulCheckValue left right output delta q d
          challenges.1 = ab.1 * delta + ab.2 then some () else none }

/-- The reduction's actual verifier reads its private setup share and applies the masked check
to the two prover messages and the public challenge. -/
theorem maskedMulCheck_output (left right output : ι → Fin n)
    (t : Transcript (maskedMulCheckSpec F ι n)) :
    (maskedMulCheck left right output).verifier.output
      (oP := voleSenderSpec F (n + 1)) () t = (do
      let (delta, q) ← ProbOracleComp.query
        (spec := voleSenderSpec F (n + 1) ⊕ₒ voleReceiverSpec F (n + 1)) (.inr ())
      return if maskedMulCheckValue left right output delta q t.1 t.2.1 =
          t.2.2.1.1 * delta + t.2.2.1.2 then some () else none) := by
  unfold Verifier.output maskedMulCheck
  rw [OracleComp.interpret_bind, OracleComp.interpret_query]
  simp only [OracleComp.sumHandler]
  congr 1

/-- Full honest receiver view. Its private setup share is read before the interaction; the
prover and verifier subsequently read their respective shares from the same cached correlation.
The final mask coordinate is consumed by just this one execution. -/
noncomputable def maskedMulCheckView (left right output : ι → Fin n) (w : Fin n → F) :
    PMF ((F × (Fin (n + 1) → F)) × Transcript (maskedMulCheckSpec F ι n)) :=
  (voleWorld F (n + 1)).eval do
    let receiver ← ProbOracleComp.query (.inr ())
    let result ← (maskedMulCheck left right output).run () w
    return (receiver, result.1)

/-- Witness-free simulation of the receiver's complete private share and public transcript.
The final constant coefficient is determined by the receiver's verification equation. -/
noncomputable def maskedMulCheckSimulate (left right output : ι → Fin n) :
    ProbComp ((F × (Fin (n + 1) → F)) × Transcript (maskedMulCheckSpec F ι n)) := do
  let delta ← ProbComp.uniform F
  let q ← ProbComp.uniform (Fin (n + 1) → F)
  let d ← ProbComp.uniform (Fin n → F)
  let r ← ProbComp.uniform (ι → F)
  let a ← ProbComp.uniform F
  return ((delta, q), (d, (r,
    ((a, maskedMulCheckValue left right output delta q d r - a * delta), ()))))

omit [DecidableEq F] in
/-- Every simulated view satisfies the receiver's masked verification equation. -/
theorem maskedMulCheckSimulate_accepts (left right output : ι → Fin n)
    {view : (F × (Fin (n + 1) → F)) × Transcript (maskedMulCheckSpec F ι n)}
    (hv : view ∈ (ProbComp.eval (maskedMulCheckSimulate left right output)).support) :
    maskedMulCheckValue left right output view.1.1 view.1.2 view.2.1 view.2.2.1 =
      view.2.2.2.1.1 * view.1.1 + view.2.2.2.1.2 := by
  simp only [maskedMulCheckSimulate, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_uniformOfFintype,
    true_and, PMF.mem_support_pure_iff] at hv
  obtain ⟨delta, q, d, r, a, rfl⟩ := hv
  change maskedMulCheckValue left right output delta q d r =
    a * delta + (maskedMulCheckValue left right output delta q d r - a * delta)
  ring

/-- The actual honest execution accepts every satisfying wire assignment, in the same ideal
world used for the full-view simulation. -/
theorem maskedMulCheck_complete (left right output : ι → Fin n) :
    (maskedMulCheck left right output).Complete (voleWorld F (n + 1))
      (fun _ w => ∀ i, w (left i) * w (right i) = w (output i)) Interactive.Accept 0 := by
  intro statement w h
  cases statement
  have hrun : (voleWorld F (n + 1)).eval ((maskedMulCheck left right output).run () w) =
      (do
        let c ← voleIdealDist F (n + 1)
        let r ← PMF.uniformOfFintype (ι → F)
        return ((voleCommitWitness w (Fin.init c.u),
          (r, (maskedMulCheckReply left right output w c.u c.v r, ()))),
            some (), ((), ()))) := by
    simp only [World.eval, Reduction.run, Verifier.execute, maskedMulCheck_output]
    simp only [pmf_norm, maskedMulCheck, liftProver, runStrategy, maskedMulCheckSpec,
      SigmaProtocol.sigmaSpec, ProbOracleComp.interpret_sample, ProbOracleComp.interpret_query,
      OracleComp.interpret_bind, OracleComp.interpret_pure, voleWorld, ProbOracleComp.runWith_bind,
      ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, pure_bind,
      VOLECorrelation.senderView]
    apply PMF.bind_congr_on_support
    intro c hc
    rw [← ProbOracleComp.sample]
    simp only [pmf_norm, ProbOracleComp.runWith_sample, ProbComp.eval_uniform]
    congr 1 with r : 1
    simp only [VOLECorrelation.receiverView,
      maskedMulCheckReply_correct left right output w c
        (valid_of_mem_support_voleIdealDist hc) r h, ite_true]
  rw [hrun]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  simp only [PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq, Interactive.Accept]
  simp

/-- Expanding the actual role-separated execution exposes exactly one ideal setup sample and
one subsequent public challenge. No sender-private data is included in the output view. -/
theorem maskedMulCheckView_eq (left right output : ι → Fin n) (w : Fin n → F) :
    maskedMulCheckView left right output w = (do
      let c ← voleIdealDist F (n + 1)
      let r ← PMF.uniformOfFintype (ι → F)
      return (c.receiverView, (voleCommitWitness w (Fin.init c.u),
        (r, (maskedMulCheckReply left right output w c.u c.v r, ()))))) := by
  simp only [pmf_norm, maskedMulCheckView, maskedMulCheck, maskedMulCheckSpec,
    SigmaProtocol.sigmaSpec, World.eval, Reduction.run, Verifier.execute, Verifier.output,
    liftProver, runStrategy, Transcript.challenges, OracleInterface.full, voleWorld,
    ProbOracleComp.interpret_sample, ProbOracleComp.interpret_query, OracleComp.interpret_bind,
    OracleComp.interpret_pure, VOLECorrelation.senderView, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, pure_bind]
  congr 1 with c : 1
  rw [← ProbOracleComp.sample]
  simp [ProbOracleComp.runWith_sample, PMF.bind_map, PMF.bind_const, ProbComp.eval_uniform,
    Function.comp_def]

omit [DecidableEq F] [DecidableEq ι] in
private theorem maskedView_fixed (left right output : ι → Fin n) (w : Fin n → F)
    (delta : F) (r : ι → F) (h : ∀ i, w (left i) * w (right i) = w (output i)) :
    (do
      let u ← PMF.uniformOfFintype (Fin (n + 1) → F)
      let v ← PMF.uniformOfFintype (Fin (n + 1) → F)
      return ((voleSample u v delta).receiverView, (voleCommitWitness w (Fin.init u),
        (r, (maskedMulCheckReply left right output w u v r, ()))))) = (do
      let q ← PMF.uniformOfFintype (Fin (n + 1) → F)
      let d ← PMF.uniformOfFintype (Fin n → F)
      let a ← PMF.uniformOfFintype F
      return ((delta, q), (d, (r,
        ((a, maskedMulCheckValue left right output delta q d r - a * delta), ()))))) := by
  let finish := fun qda : (Fin (n + 1) → F) × (Fin n → F) × F =>
    ((delta, qda.1), (qda.2.1, (r, ((qda.2.2,
      maskedMulCheckValue left right output delta qda.1 qda.2.1 r - qda.2.2 * delta), ()))))
  have hfinish (uv : (Fin (n + 1) → F) × (Fin (n + 1) → F)) :
      finish (maskedSetupEquiv left right output w delta r uv) =
        ((voleSample uv.1 uv.2 delta).receiverView,
          (voleCommitWitness w (Fin.init uv.1),
            (r, (maskedMulCheckReply left right output w uv.1 uv.2 r, ())))) := by
    have hc := maskedMulCheckReply_correct left right output w
      (voleSample uv.1 uv.2 delta) (valid_voleSample _ _ _) r h
    change ((voleSample uv.1 uv.2 delta).receiverView,
      (voleCommitWitness w (Fin.init uv.1), (r,
        (((maskedMulCheckReply left right output w uv.1 uv.2 r).1,
          maskedMulCheckValue left right output (voleSample uv.1 uv.2 delta).delta
            (voleSample uv.1 uv.2 delta).w (voleCommitWitness w (Fin.init uv.1)) r -
              (maskedMulCheckReply left right output w uv.1 uv.2 r).1 * delta), ())))) = _
    change maskedMulCheckValue left right output (voleSample uv.1 uv.2 delta).delta
      (voleSample uv.1 uv.2 delta).w (voleCommitWitness w (Fin.init uv.1)) r =
        (maskedMulCheckReply left right output w uv.1 uv.2 r).1 * delta +
          (maskedMulCheckReply left right output w uv.1 uv.2 r).2 at hc
    rw [hc]
    simp
  have he := congrArg (fun p => p.map finish)
    (PMF.uniformOfFintype_map_equiv (maskedSetupEquiv left right output w delta r))
  simp only [PMF.map_comp, Function.comp_def, hfinish] at he
  simpa only [pmf_norm, ← PMF.uniformOfFintype_prod, PMF.map, finish] using he

/-- Perfect simulation of the full honest receiver view in the cached ideal VOLE world.
Every selected multiplication constraint must hold. Public parameters are the wire count, gate
index type and three index maps; the simulator receives no witness. The equality includes the
receiver's private key and raw tags, all public corrections, the public weights and both reply
coefficients. This is an exact semantic view law, not a plain-model or malicious-verifier ZK
claim. -/
theorem maskedMulCheckView_eq_simulate (left right output : ι → Fin n) (w : Fin n → F)
    (h : ∀ i, w (left i) * w (right i) = w (output i)) :
    maskedMulCheckView left right output w =
      ProbComp.eval (maskedMulCheckSimulate left right output) := by
  rw [maskedMulCheckView_eq]
  simp only [pmf_norm, voleIdealDist, maskedMulCheckSimulate, ProbComp.eval_uniform]
  pmf_swap with r delta
  exact maskedView_fixed left right output w delta r h

/-- No event on the complete receiver view distinguishes the honest execution from simulation. -/
theorem maskedMulCheckView_closeTo_simulate (left right output : ι → Fin n) (w : Fin n → F)
    (h : ∀ i, w (left i) * w (right i) = w (output i)) :
    CloseTo (maskedMulCheckView left right output w)
      (ProbComp.eval (maskedMulCheckSimulate left right output)) 0 := by
  rw [maskedMulCheckView_eq_simulate left right output w h]
  exact CloseTo.refl _

end Cslib.Crypto.Protocols.VOLE
