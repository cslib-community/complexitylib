/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.VOLE.MaskedMulCheck
public import CslibFrontier.Computability.Interactive.StrategyEffect
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Tactic.PMFSwap

/-!
# Masked VOLE views against adaptive receivers

One fixed correction/challenge/reply execution uses a fresh ideal correlation. The receiver may
choose weights using its private setup share, the corrections and private coins, and may retain
state and query its cached share after the reply. The simulator runs those same continuations.
This is an exact view experiment in the existing ideal world, without a new ZK predicate or an
efficiency, reset, concurrent-session or VOLE-in-the-head claim.

## Main definitions

* `maskedMulCheckReceiverView`: actual cached-world execution with an arbitrary receiver strategy.
* `maskedMulCheckReceiverSimulate`: witness-free simulation with the same receiver program.

## Main results

* `maskedMulCheckReceiverView_eq_simulate`: exact equality of full adaptive receiver views.
* `maskedMulCheckReceiverSimulate_accepts`: simulated transcripts satisfy the masked equation.

This is an original semantic extension of the fresh-mask argument in the preceding module.
The source uses scalar-power weights and subfield wires; this full-ring version permits arbitrary
receiver-selected vector weights. The honest masking construction is described in
[BaumEtAl2023FAEST], Section 2.3.2, printed pages 12–13.
Its compiled security theorem is not claimed.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.VOLE

open Probability Interactive Interactive.Spec
open scoped BigOperators

variable {F ι Aux View : Type} {n : ℕ}
variable [CommRing F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

/-- The change of setup coordinates precedes the receiver's adaptive challenge. In particular,
its fresh sender coordinate is still uniform conditional on the whole receiver-visible prefix. -/
private def maskedPrefixEquiv (w : Fin n → F) (delta : F) :
    ((Fin (n + 1) → F) × (Fin (n + 1) → F)) ≃
      ((Fin (n + 1) → F) × (Fin n → F) × F) where
  toFun uv := ((voleSample uv.1 uv.2 delta).w,
    voleCommitWitness w (Fin.init uv.1), uv.1 (Fin.last n))
  invFun qdb :=
    let u := Fin.snoc (w - qdb.2.1) qdb.2.2
    (u, fun j => qdb.1 j - u j * delta)
  left_inv uv := by
    rcases uv with ⟨u, v⟩
    dsimp
    simp only [voleCommitWitness, sub_sub_cancel, Fin.snoc_init_self]
    congr 1 with j : 1
    ring
  right_inv qdb := by
    rcases qdb with ⟨q, d, b⟩
    apply Prod.ext
    · funext j
      dsimp [voleSample]
      ring
    · apply Prod.ext
      · funext j
        simp [voleCommitWitness]
      · simp

omit [DecidableEq F] in
private theorem uniform_maskedPrefix {α : Type} (w : Fin n → F) (delta : F)
    (f : (Fin (n + 1) → F) → (Fin (n + 1) → F) → PMF α) :
    (do
      let u ← PMF.uniformOfFintype (Fin (n + 1) → F)
      let v ← PMF.uniformOfFintype (Fin (n + 1) → F)
      f u v) = (do
      let q ← PMF.uniformOfFintype (Fin (n + 1) → F)
      let d ← PMF.uniformOfFintype (Fin n → F)
      let b ← PMF.uniformOfFintype F
      let uv := (maskedPrefixEquiv w delta).symm (q, d, b)
      f uv.1 uv.2) := by
  have h := congrArg (fun p => p.bind (fun uv => f uv.1 uv.2))
    (PMF.uniformOfFintype_map_equiv (maskedPrefixEquiv w delta).symm)
  simpa only [pmf_norm, ← PMF.uniformOfFintype_prod] using h.symm

omit [DecidableEq F] [DecidableEq ι] in
private theorem uniform_maskedReply {α : Type} (left right output : ι → Fin n)
    (w : Fin n → F) (delta : F) (q : Fin (n + 1) → F) (d : Fin n → F) (r : ι → F)
    (h : ∀ i, w (left i) * w (right i) = w (output i)) (f : F × F → PMF α) :
    (do
      let b ← PMF.uniformOfFintype F
      let uv := (maskedPrefixEquiv w delta).symm (q, d, b)
      f (maskedMulCheckReply left right output w uv.1 uv.2 r)) = (do
      let a ← PMF.uniformOfFintype F
      f (a, maskedMulCheckValue left right output delta q d r - a * delta)) := by
  let zero := (maskedPrefixEquiv w delta).symm (q, d, 0)
  let cross := (maskedMulCheckReply left right output w zero.1 zero.2 r).1
  have hslope (b : F) :
      let uv := (maskedPrefixEquiv w delta).symm (q, d, b)
      (maskedMulCheckReply left right output w uv.1 uv.2 r).1 = cross + b := by
    simp [maskedPrefixEquiv, maskedMulCheckReply, cross, zero]
  have hreply (b : F) :
      let uv := (maskedPrefixEquiv w delta).symm (q, d, b)
      maskedMulCheckReply left right output w uv.1 uv.2 r =
        (cross + b, maskedMulCheckValue left right output delta q d r - (cross + b) * delta) := by
    let uv := (maskedPrefixEquiv w delta).symm (q, d, b)
    have hp := (maskedPrefixEquiv w delta).apply_symm_apply (q, d, b)
    change ((voleSample uv.1 uv.2 delta).w,
      voleCommitWitness w (Fin.init uv.1), uv.1 (Fin.last n)) = (q, d, b) at hp
    have hc := maskedMulCheckReply_correct left right output w (voleSample uv.1 uv.2 delta)
      (valid_voleSample _ _ _) r h
    have hq := congrArg Prod.fst hp
    have hd := congrArg (fun x => x.2.1) hp
    dsimp only at hq hd
    change maskedMulCheckValue left right output delta (voleSample uv.1 uv.2 delta).w
      (voleCommitWitness w (Fin.init uv.1)) r =
        (maskedMulCheckReply left right output w uv.1 uv.2 r).1 * delta +
          (maskedMulCheckReply left right output w uv.1 uv.2 r).2 at hc
    rw [hq, hd, hslope b] at hc
    apply Prod.ext
    · exact hslope b
    · rw [hc]
      ring
  have he := congrArg
    (fun p => p.bind fun a => f (a, maskedMulCheckValue left right output delta q d r - a * delta))
    (PMF.uniformOfFintype_map_equiv (Equiv.addLeft cross))
  simpa only [pmf_norm, Equiv.coe_addLeft, hreply] using he

/-- The full receiver view in one actual interaction. Receiver initialization runs after its
setup share has been cached and before prover initialization; later effects run in protocol order.
Only the role-local sender interface is supplied to the honest prover. Auxiliary input is fixed
before this fresh setup is sampled. -/
noncomputable def maskedMulCheckReceiverView (left right output : ι → Fin n)
    (V : Aux → ProbOracleComp (voleReceiverSpec F (n + 1))
      (VerifierStrategy (ProbOracleComp (voleReceiverSpec F (n + 1)))
        (maskedMulCheckSpec F ι n) View))
    (w : Fin n → F) (z : Aux) :
    PMF ((F × (Fin (n + 1) → F)) × Transcript (maskedMulCheckSpec F ι n) × View) :=
  (voleWorld F (n + 1)).eval do
    let share ← ProbOracleComp.query (.inr ())
    let v ← liftVerifier (V z)
    let p ← liftProver ((maskedMulCheck left right output).prover () w)
    let result ← runAgainst (maskedMulCheckSpec F ι n)
      (ProverStrategy.hoist liftProver _ p) (VerifierStrategy.hoist liftVerifier _ v)
    return (share, result.1, result.2.2)

/-- Simulate the private share and full public transcript, retaining all receiver effects and
captured continuations. The constant share handler answers every later query identically; its
private sampling calls remain fresh. Corrections are delivered before the receiver chooses weights,
and the affine slope is sampled only after those weights and their continuation are fixed. -/
noncomputable def maskedMulCheckReceiverSimulate (left right output : ι → Fin n)
    (V : Aux → ProbOracleComp (voleReceiverSpec F (n + 1))
      (VerifierStrategy (ProbOracleComp (voleReceiverSpec F (n + 1)))
        (maskedMulCheckSpec F ι n) View))
    (z : Aux) :
    ProbComp ((F × (Fin (n + 1) → F)) × Transcript (maskedMulCheckSpec F ι n) × View) := do
  let delta ← ProbComp.uniform F
  let q ← ProbComp.uniform (Fin (n + 1) → F)
  let run := fun {α : Type} (program : ProbOracleComp (voleReceiverSpec F (n + 1)) α) =>
    OracleComp.interpret (OracleComp.sumHandler OracleComp.query (fun _ => pure (delta, q))) program
  let v ← run (V z)
  let d ← ProbComp.uniform (Fin n → F)
  let challenge ← run (v d)
  let (r, continuation) ← run challenge
  let a ← ProbComp.uniform F
  let reply := (a, maskedMulCheckValue left right output delta q d r - a * delta)
  let terminal ← run (continuation reply)
  let view ← run terminal
  return ((delta, q), (d, r, reply, ()), view)

private noncomputable def receiverLaw (share : F × (Fin (n + 1) → F)) {α : Type}
    (program : ProbOracleComp (voleReceiverSpec F (n + 1)) α) : PMF α :=
  OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
    (fun _ => PMF.pure share)) program

omit [CommRing F] [Fintype F] [DecidableEq F] in
private theorem interpret_liftVerifier {α : Type} (c : VOLECorrelation F (n + 1))
    (program : ProbOracleComp (voleReceiverSpec F (n + 1)) α) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
      (OracleComp.sumHandler (fun _ => PMF.pure (c.u, c.v))
        (fun _ => PMF.pure c.receiverView)))
      (liftVerifier (oP := voleSenderSpec F (n + 1)) program) =
        receiverLaw c.receiverView program := by
  rw [liftVerifier, OracleComp.interpret_interpret]
  unfold receiverLaw
  congr 1 with query : 1
  cases query <;> simp [OracleComp.sumHandler, ProbOracleComp.query]

private theorem maskedMulCheckReceiverView_eq (left right output : ι → Fin n)
    (V : Aux → ProbOracleComp (voleReceiverSpec F (n + 1))
      (VerifierStrategy (ProbOracleComp (voleReceiverSpec F (n + 1)))
        (maskedMulCheckSpec F ι n) View)) (w : Fin n → F) (z : Aux) :
    maskedMulCheckReceiverView left right output V w z = (do
      let c ← voleIdealDist F (n + 1)
      let v ← receiverLaw c.receiverView (V z)
      let d := voleCommitWitness w (Fin.init c.u)
      let challenge ← receiverLaw c.receiverView (v d)
      let (r, continuation) ← receiverLaw c.receiverView challenge
      let reply := maskedMulCheckReply left right output w c.u c.v r
      let terminal ← receiverLaw c.receiverView (continuation reply)
      let view ← receiverLaw c.receiverView terminal
      return (c.receiverView, (d, r, reply, ()), view)) := by
  have hinit : (voleWorld F (n + 1)).impl (.inr ()) none =
      (voleIdealDist F (n + 1)).map (fun c => (c.receiverView, some c)) := by
    simp [voleWorld, PMF.map, Function.comp_def]
  unfold maskedMulCheckReceiverView World.eval
  change (ProbOracleComp.runWith (State := Option (VOLECorrelation F (n + 1)))
    (voleWorld F (n + 1)).impl _ none).map Prod.fst = _
  erw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, hinit,
    PMF.bind_map, PMF.map_bind]
  conv_lhs =>
    arg 2
    ext c
    dsimp only [Function.comp_def]
    erw [voleWorld_cached_run (F := F) (n := n + 1) c]
  dsimp only [voleWorld]
  simp only [pmf_norm]
  congr 1 with c : 1
  simp [OracleComp.interpret_bind, OracleComp.interpret_pure, interpret_liftVerifier,
    maskedMulCheck, liftProver, ProbOracleComp.query, OracleComp.sumHandler,
    runAgainst, ProverStrategy.hoist, VerifierStrategy.hoist, maskedMulCheckSpec,
    SigmaProtocol.sigmaSpec, VOLECorrelation.senderView, PMF.map, Function.comp_def]

omit [DecidableEq F] [DecidableEq ι] in
private theorem maskedMulCheckReceiverSimulate_eq (left right output : ι → Fin n)
    (V : Aux → ProbOracleComp (voleReceiverSpec F (n + 1))
      (VerifierStrategy (ProbOracleComp (voleReceiverSpec F (n + 1)))
        (maskedMulCheckSpec F ι n) View)) (z : Aux) :
    ProbComp.eval (maskedMulCheckReceiverSimulate left right output V z) = (do
      let delta ← PMF.uniformOfFintype F
      let q ← PMF.uniformOfFintype (Fin (n + 1) → F)
      let v ← receiverLaw (delta, q) (V z)
      let d ← PMF.uniformOfFintype (Fin n → F)
      let challenge ← receiverLaw (delta, q) (v d)
      let (r, continuation) ← receiverLaw (delta, q) challenge
      let a ← PMF.uniformOfFintype F
      let reply := (a, maskedMulCheckValue left right output delta q d r - a * delta)
      let terminal ← receiverLaw (delta, q) (continuation reply)
      let view ← receiverLaw (delta, q) terminal
      return ((delta, q), (d, r, reply, ()), view)) := by
  have heval {α : Type} (share : F × (Fin (n + 1) → F))
      (program : ProbOracleComp (voleReceiverSpec F (n + 1)) α) :
      ProbComp.eval (OracleComp.interpret
        (OracleComp.sumHandler OracleComp.query (fun _ => pure share)) program) =
          receiverLaw share program := by
    change ProbComp.eval (OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifFin (fun _ => pure share)) program) = _
    rw [ProbOracleComp.eval_interpret]
    simp [receiverLaw]
  simp [maskedMulCheckReceiverSimulate, ProbComp.eval_bind, ProbComp.eval_uniform,
    heval, PMF.map, Function.comp_def]

/-- Exact simulation against every receiver strategy in the fixed three-message schedule.
The equality retains its private setup share, full transcript and arbitrary terminal view, including
state captured before the challenge and effects after the reply. The witness must satisfy every
selected gate. The setup is trusted and uniform, and the affine mask is fresh for this execution;
no reset, concurrent-session, runtime or plain-model ZK conclusion is asserted. -/
theorem maskedMulCheckReceiverView_eq_simulate (left right output : ι → Fin n)
    (V : Aux → ProbOracleComp (voleReceiverSpec F (n + 1))
      (VerifierStrategy (ProbOracleComp (voleReceiverSpec F (n + 1)))
        (maskedMulCheckSpec F ι n) View)) (w : Fin n → F) (z : Aux)
    (h : ∀ i, w (left i) * w (right i) = w (output i)) :
    maskedMulCheckReceiverView left right output V w z =
      ProbComp.eval (maskedMulCheckReceiverSimulate left right output V z) := by
  rw [maskedMulCheckReceiverView_eq, maskedMulCheckReceiverSimulate_eq]
  simp only [pmf_norm, voleIdealDist]
  pmf_swap with delta
  have hprefix := uniform_maskedPrefix w delta (fun u v => do
    let c := voleSample u v delta
    let verifier ← receiverLaw c.receiverView (V z)
    let d := voleCommitWitness w (Fin.init c.u)
    let challenge ← receiverLaw c.receiverView (verifier d)
    let (r, continuation) ← receiverLaw c.receiverView challenge
    let reply := maskedMulCheckReply left right output w c.u c.v r
    let terminal ← receiverLaw c.receiverView (continuation reply)
    let view ← receiverLaw c.receiverView terminal
    return (c.receiverView, (d, r, reply, ()), view))
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure] at hprefix
  rw [hprefix]
  have hshare (q : Fin (n + 1) → F) (d : Fin n → F) (b : F) :
      let uv := (maskedPrefixEquiv w delta).symm (q, d, b)
      (voleSample uv.1 uv.2 delta).receiverView = (delta, q) := by
    have hp := congrArg Prod.fst ((maskedPrefixEquiv w delta).apply_symm_apply (q, d, b))
    exact congrArg (delta, ·) hp
  have hcorr (q : Fin (n + 1) → F) (d : Fin n → F) (b : F) :
      let uv := (maskedPrefixEquiv w delta).symm (q, d, b)
      voleCommitWitness w (Fin.init uv.1) = d :=
    congrArg (fun x => x.2.1) ((maskedPrefixEquiv w delta).apply_symm_apply (q, d, b))
  simp_rw [hshare]
  dsimp only [voleSample]
  simp_rw [hcorr]
  pmf_swap with q v d challenge pair
  rcases pair with ⟨r, continuation⟩
  simpa only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure] using
    uniform_maskedReply left right output w delta q d r h (fun reply => do
      let terminal ← receiverLaw (delta, q) (continuation reply)
      let view ← receiverLaw (delta, q) terminal
      return ((delta, q), (d, r, reply, ()), view))

omit [DecidableEq F] [DecidableEq ι] in
/-- Every simulated transcript satisfies the masked equation, even when its weights were chosen
adaptively. This concerns the equation, not an arbitrary receiver's terminal decision. -/
theorem maskedMulCheckReceiverSimulate_accepts (left right output : ι → Fin n)
    (V : Aux → ProbOracleComp (voleReceiverSpec F (n + 1))
      (VerifierStrategy (ProbOracleComp (voleReceiverSpec F (n + 1)))
        (maskedMulCheckSpec F ι n) View)) (z : Aux)
    {result : (F × (Fin (n + 1) → F)) × Transcript (maskedMulCheckSpec F ι n) × View}
    (hv : result ∈ (ProbComp.eval (maskedMulCheckReceiverSimulate left right output V z)).support) :
    maskedMulCheckValue left right output result.1.1 result.1.2
        result.2.1.1 result.2.1.2.1 =
      result.2.1.2.2.1.1 * result.1.1 + result.2.1.2.2.1.2 := by
  rw [maskedMulCheckReceiverSimulate_eq] at hv
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hv
  rcases hv with ⟨delta, _, q, _, v, _, d, _, challenge, _, ⟨r, continuation⟩, _,
    a, _, terminal, _, view, _, rfl⟩
  dsimp
  ring

end Cslib.Crypto.Protocols.VOLE
