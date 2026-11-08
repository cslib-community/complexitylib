/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game
public import Complexity.Crypto.Protocols.MPC.Broadcast
public import Complexity.Crypto.Protocols.MPC.SharedMul
public import Mathlib.Data.ZMod.Basic
import Complexity.Languages.Probabilistic.Norm
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Uniform

/-!
# Arithmetic Beaver Multiplication Triples, Online Privacy, and Tampered-Opening Attack

This module formalizes Beaver's circuit-randomization multiplication step over `ZMod p` together
with its semi-honest coalition privacy in the ideal triple-preprocessing hybrid model and an
explicit illustration of additive-error output-opening tampering against unauthenticated 2-party
Beaver multiplication:

1. **Beaver Triple Share Structure (`TripleShare`):** per-party additive shares `(a_i, b_i, c_i)`
   of a multiplication triple over `R`. Input share pairs `(x_i, y_i)` and broadcast masked
   openings `(d_i, e_i) = (x_i - a_i, y_i - b_i)` are represented directly as `R × R` using
   Mathlib's coordinatewise `AddCommGroup` structure.
2. **Ideal $m$-Party Triple Preprocessing (`beaverTripleFunctionality`, `beaverTripleSpec`,
   `beaverTripleWorld`):** an $m$-party generalization of the 2-party dealer ("2.5-party")
   functionality in [BonehShoup2023], Section 23.2.2 (building on circuit randomization via
   multiplication triples from [Beaver1991] and the $m$-party additive-share online model of
   [DamgardPastroSmartZakarias2012]). It samples uniform additive shares
   `(a_i, b_i, c_i)` over `ZMod p` conditioned on $\sum_i c_i = (\sum_i a_i) \cdot (\sum_i b_i)$,
   reusing
   `ProbComp.sampleAdditiveShares` from `Complexity.Languages.Probabilistic.Sharing`. For every
   proper coalition `I ≠ Finset.univ`, the marginal distribution of `I`'s triple shares is uniform
   (`eval_restrict_beaverTripleFunctionality`).
3. **Beaver Online Share Multiplication (`beaverMulShare`, `beaverMulProtocol`, `beaverMulSim`,
   `perfectSemiHonestPrivateProper_beaverMul`):** synchronous $m$-party protocol over
   `Complexity.Crypto.Protocols.MPC.Basic` and `Complexity.Crypto.Protocols.MPC.Broadcast` in
   which the parties query `beaverTripleSpec p m`, broadcast their masked openings
   `localMaskedOpening`, and output additive shares summing to
   $(\sum_i x_i) \cdot (\sum_i y_i)$ (`sum_output_beaverMulProtocol`). We prove
   `PerfectSemiHonestPrivateProper` against every proper static coalition `I ≠ Finset.univ` with
   respect to `sharedMulFunctionality m` (exact equality of joint view-and-output distributions,
   with no polynomial-time simulator certificate).
4. **Additive-Error Tampered-Opening Attack Illustration (`tamperedOpening`,
   `tamperedOpeningExtract`, `tamperedOpeningReal`, `eval_tamperedOpeningReal`,
   `le_advantage_tamperedOpeningBitGame`):** motivated by the discussion of maliciously tampered
   openings in [BonehShoup2023], Section 23.2.4, we give an original concrete 2-party illustration
   showing what goes wrong if unauthenticated Beaver multiplication of `[z] = [x] * [0]` is
   followed by an unauthenticated output-share opening. Notice that `beaverMulProtocol` itself
   only produces output shares and has no output-broadcast round; if honest party `0` subsequently
   reveals its output share `z'₀ = beaverMulShare 0 (op₀ + tamperedOpening t₁) t₀` after party `1`
   substitutes `e'₁ = -b₁ + 1` in the masked-opening broadcast, the tampered transcript
   `(t₁, op₀, z'₀)` determines `x` identically (`tamperedOpeningExtract_eq`). The standalone
   `ProbComp (ZMod p)` experiment `tamperedOpeningReal` and the toy distinguishing games
   `tamperedOpeningTestOne`, `tamperedOpeningRealBitGame`, and `tamperedOpeningIdealBitGame`
   package this exact recovery against any input-independent guessing distribution
   `blindGuess : ProbComp (ZMod p)`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Beaver.TripleShare`: named structure for one party's additive shares
  `(a, b, c)` of a Beaver multiplication triple.
* `Cslib.Crypto.Protocols.MPC.Beaver.beaverTripleFunctionality`,
  `Cslib.Crypto.Protocols.MPC.Beaver.beaverTripleSpec`,
  `Cslib.Crypto.Protocols.MPC.Beaver.beaverTripleWorld`: $m$-party Beaver triple preprocessing
  functionality, oracle specification, and memoryless world.
* `Cslib.Crypto.Protocols.MPC.Beaver.localMaskedOpening`,
  `Cslib.Crypto.Protocols.MPC.Beaver.beaverMulShare`: local masked opening `(x_i - a_i, y_i - b_i)`
  and Beaver share multiplication step.
* `Cslib.Crypto.Protocols.MPC.Beaver.beaverMulSchedule`,
  `Cslib.Crypto.Protocols.MPC.Beaver.beaverMulProtocol`,
  `Cslib.Crypto.Protocols.MPC.Beaver.beaverMulSim`: synchronous $m$-party Beaver online
  multiplication protocol and proper-coalition simulator.
* `Cslib.Crypto.Protocols.MPC.Beaver.tamperedOpening`,
  `Cslib.Crypto.Protocols.MPC.Beaver.tamperedOpeningExtract`,
  `Cslib.Crypto.Protocols.MPC.Beaver.tamperedOpeningReal`,
  `Cslib.Crypto.Protocols.MPC.Beaver.tamperedOpeningTestOne`,
  `Cslib.Crypto.Protocols.MPC.Beaver.tamperedOpeningRealBitGame`,
  `Cslib.Crypto.Protocols.MPC.Beaver.tamperedOpeningIdealBitGame`: 2-party additive-error
  tampered-opening formula, standalone extraction experiment, and toy distinguishing games.

## Main results

* `Cslib.Crypto.Protocols.MPC.Beaver.mem_support_beaverTripleFunctionality_iff`,
  `Cslib.Crypto.Protocols.MPC.Beaver.eval_restrict_beaverTripleFunctionality`: support
  characterization and proper-coalition marginal uniformity of `beaverTripleFunctionality`.
* `Cslib.Crypto.Protocols.MPC.Beaver.sum_beaverMulShare`,
  `Cslib.Crypto.Protocols.MPC.Beaver.sum_beaverMulShare_eq_mul`: algebraic reconstruction of the
  product from Beaver output shares.
* `Cslib.Crypto.Protocols.MPC.Beaver.sum_output_beaverMulProtocol`,
  `Cslib.Crypto.Protocols.MPC.Beaver.perfectSemiHonestPrivateProper_beaverMul`: output correctness
  and proper-coalition perfect semi-honest privacy of `beaverMulProtocol` in `beaverTripleWorld`
  for `sharedMulFunctionality m`.
* `Cslib.Crypto.Protocols.MPC.Beaver.tamperedOpeningExtract_eq`,
  `Cslib.Crypto.Protocols.MPC.Beaver.eval_tamperedOpeningReal`,
  `Cslib.Crypto.Protocols.MPC.Beaver.one_le_add_advantage_tamperedOpening`,
  `Cslib.Crypto.Protocols.MPC.Beaver.le_advantage_tamperedOpeningBitGame`: deterministic recovery
  of `x` when the output share is opened after an additive-error tampered opening, and `≥ 1 / 2`
  distinguishing advantage in the standalone hidden-bit game against any input-independent guess.

## References

* [D. Beaver, *Efficient Multiparty Protocols Using Circuit Randomization*][Beaver1991].
* [I. Damgård, V. Pastro, N. P. Smart, S. Zakarias, *Multiparty Computation from Somewhat
  Homomorphic Encryption*][DamgardPastroSmartZakarias2012].
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Sections
  23.2.2 and 23.2.4.
-/

public section

namespace Cslib.Crypto.Protocols.MPC.Beaver

open Cslib.Probability Cslib.ProbComp Cslib.Crypto Cslib.Crypto.Protocols.MPC
open scoped ENNReal NNReal

/-! ### Beaver triple share structure -/

/-- One party's additive share `(a, b, c)` of a Beaver multiplication triple over `R`. -/
@[ext] structure TripleShare (R : Type) where
  /-- Additive share of the first random mask `a`. -/
  a : R
  /-- Additive share of the second random mask `b`. -/
  b : R
  /-- Additive share of the mask product `c = a * b`. -/
  c : R
  deriving DecidableEq, Fintype, Inhabited, Repr

/-! ### Ideal $m$-party Beaver triple preprocessing -/

/-- Randomized `m`-party Beaver triple preprocessing functionality over `ZMod p` (an `m`-party
generalization of the 2-party dealer in [BonehShoup2023], Section 23.2.2; cf. [Beaver1991];
[DamgardPastroSmartZakarias2012]): samples independent uniform additive share vectors
`a, b : Fin m → ZMod p` and uniform additive shares `c` summing to `(∑ i, a i) * (∑ i, b i)`. -/
noncomputable def beaverTripleFunctionality (p m : ℕ) [NeZero p] :
    Functionality m (fun _ => Unit) (fun _ => TripleShare (ZMod p)) := fun _ => do
  let a ← ProbComp.uniform (Fin m → ZMod p)
  let b ← ProbComp.uniform (Fin m → ZMod p)
  let c ← ProbComp.sampleAdditiveShares m ((∑ i : Fin m, a i) * (∑ i : Fin m, b i))
  return fun i => ⟨a i, b i, c i⟩

/-- `m`-ary oracle specification for Beaver triple preprocessing over `ZMod p`. -/
@[expose, reducible] def beaverTripleSpec (p m : ℕ) : MultiOracleSpec where
  Op := Unit
  arity _ := m
  Query _ _ := Unit
  Answer _ _ := TripleShare (ZMod p)

/-- Ideal memoryless world for `beaverTripleSpec p m` backed by `beaverTripleFunctionality p m`. -/
noncomputable def beaverTripleWorld (p m : ℕ) [NeZero p] :
    MultiOracleWorld (beaverTripleSpec p m) :=
  fun _ q => beaverTripleFunctionality p m q

/-- Support characterization for `beaverTripleFunctionality`: an `m`-tuple of triple shares lies in
the support if and only if `∑ i, (t i).c = (∑ i, (t i).a) * (∑ i, (t i).b)`. -/
theorem mem_support_beaverTripleFunctionality_iff {p m : ℕ} [NeZero p] [NeZero m]
    (u : Fin m → Unit) (t : Fin m → TripleShare (ZMod p)) :
    t ∈ (ProbComp.eval (beaverTripleFunctionality p m u)).support ↔
      (∑ i : Fin m, (t i).c) = (∑ i : Fin m, (t i).a) * (∑ i : Fin m, (t i).b) := by
  simp only [beaverTripleFunctionality, bind_pure_comp, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_uniform, PMF.mem_support_bind_iff, PMF.mem_support_map_iff,
    ProbComp.mem_support_sampleAdditiveShares_iff]
  constructor
  · rintro ⟨a, _, b, _, c, hc, rfl⟩
    exact hc
  · intro hc
    refine ⟨fun i => (t i).a, by simp [PMF.mem_support_iff],
      fun i => (t i).b, by simp [PMF.mem_support_iff],
      fun i => (t i).c, hc, ?_⟩
    ext i <;> rfl

/-- Every triple in the support of `beaverTripleFunctionality` satisfies the Beaver product
relation `∑ i, (t i).c = (∑ i, (t i).a) * (∑ i, (t i).b)`. -/
theorem sum_c_of_mem_support_beaverTripleFunctionality {p m : ℕ} [NeZero p] [NeZero m]
    {u : Fin m → Unit} {t : Fin m → TripleShare (ZMod p)}
    (ht : t ∈ (ProbComp.eval (beaverTripleFunctionality p m u)).support) :
    (∑ i : Fin m, (t i).c) = (∑ i : Fin m, (t i).a) * (∑ i : Fin m, (t i).b) :=
  (mem_support_beaverTripleFunctionality_iff u t).mp ht

/-- For every proper coalition `I ≠ Finset.univ`, the marginal distribution of `I`'s triple shares
in `beaverTripleFunctionality` is uniform on `(i : I) → TripleShare (ZMod p)`. -/
theorem eval_restrict_beaverTripleFunctionality {p m : ℕ} [NeZero p]
    (I : Finset (Fin m)) (hI : I ≠ Finset.univ) (u : Fin m → Unit) :
    (ProbComp.eval (beaverTripleFunctionality p m u)).map I.restrict =
      PMF.uniformOfFintype ((i : I) → TripleShare (ZMod p)) := by
  obtain ⟨j₀, _⟩ := not_forall.mp (mt Finset.eq_univ_iff_forall.mpr hI)
  have : NeZero m := ⟨Nat.ne_of_gt j₀.pos⟩
  simp only [beaverTripleFunctionality, bind_pure_comp, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_uniform, PMF.map_bind, PMF.map_comp]
  have hc : ∀ (a b : Fin m → ZMod p),
      (ProbComp.eval
        (ProbComp.sampleAdditiveShares m ((∑ i : Fin m, a i) * (∑ i : Fin m, b i)))).map
        (I.restrict ∘ fun (c : Fin m → ZMod p) (i : Fin m) =>
          (⟨a i, b i, c i⟩ : TripleShare (ZMod p))) =
      (PMF.uniformOfFintype ((i : I) → ZMod p)).map
        (fun cI (i : I) => (⟨I.restrict a i, I.restrict b i, cI i⟩ : TripleShare (ZMod p))) := by
    intro a b
    rw [← ProbComp.eval_restrict_sampleAdditiveShares I hI
      ((∑ i : Fin m, a i) * (∑ i : Fin m, b i)), PMF.map_comp]
    rfl
  simp_rw [hc]
  rw [PMF.uniformOfFintype_pi_bind_restrict (π := fun _ => ZMod p) I (fun aI =>
    (PMF.uniformOfFintype (Fin m → ZMod p)).bind fun b =>
      (PMF.uniformOfFintype ((i : I) → ZMod p)).map fun cI (i : I) =>
        (⟨aI i, I.restrict b i, cI i⟩ : TripleShare (ZMod p)))]
  have hb : ∀ aI : (i : I) → ZMod p,
      ((PMF.uniformOfFintype (Fin m → ZMod p)).bind fun b =>
        (PMF.uniformOfFintype ((i : I) → ZMod p)).map fun cI (i : I) =>
          (⟨aI i, I.restrict b i, cI i⟩ : TripleShare (ZMod p))) =
      ((PMF.uniformOfFintype ((i : I) → ZMod p)).bind fun bI =>
        (PMF.uniformOfFintype ((i : I) → ZMod p)).map fun cI (i : I) =>
          (⟨aI i, bI i, cI i⟩ : TripleShare (ZMod p))) := fun aI =>
    PMF.uniformOfFintype_pi_bind_restrict (π := fun _ => ZMod p) I (fun bI =>
      (PMF.uniformOfFintype ((i : I) → ZMod p)).map fun cI (i : I) =>
        (⟨aI i, bI i, cI i⟩ : TripleShare (ZMod p)))
  simp_rw [hb, PMF.uniformOfFintype_bind_map]
  let e : (((i : I) → ZMod p) × ((i : I) → ZMod p) × ((i : I) → ZMod p)) ≃
      ((i : I) → TripleShare (ZMod p)) :=
    { toFun := fun ⟨aI, bI, cI⟩ i => ⟨aI i, bI i, cI i⟩
      invFun := fun t => (fun i => (t i).a, fun i => (t i).b, fun i => (t i).c)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun t => by ext i <;> rfl }
  exact PMF.uniformOfFintype_map_equiv e

/-! ### Beaver share multiplication step and algebraic reconstruction -/

/-- Party `i`'s local masked opening share `(x_i - a_i, y_i - b_i)`. -/
@[expose] def localMaskedOpening {R : Type} [Sub R] (xy : R × R) (t : TripleShare R) : R × R :=
  let (x, y) := xy
  (x - t.a, y - t.b)

/-- Party `i`'s local Beaver output share given public reconstructed masked opening `op = (d, e)`
and party `i`'s triple share `t = (a_i, b_i, c_i)` ([BonehShoup2023], Section 23.2.2, generalized
to `m` parties; [DamgardPastroSmartZakarias2012]; cf. [Beaver1991]): party `0` adds the
public product term `d * e` to `d * b_i + e * a_i + c_i`. -/
@[expose] def beaverMulShare {R : Type} [CommRing R] {m : ℕ}
    (i : Fin m) (op : R × R) (t : TripleShare R) : R :=
  let (d, e) := op
  (if i.val = 0 then d * e else 0) + d * t.b + e * t.a + t.c

/-- Sum of `beaverMulShare` across all `m` parties (`m > 0`). -/
theorem sum_beaverMulShare {R : Type} [CommRing R] {m : ℕ} [NeZero m]
    (op : R × R) (t : Fin m → TripleShare R) :
    (∑ i : Fin m, beaverMulShare i op (t i)) =
      op.1 * op.2 + op.1 * (∑ i : Fin m, (t i).b) + op.2 * (∑ i : Fin m, (t i).a) +
        ∑ i : Fin m, (t i).c := by
  simp only [beaverMulShare, Fin.val_eq_zero_iff, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Algebraic correctness of Beaver multiplication ([BonehShoup2023], Section 23.2.2, generalized
to `m` parties; [DamgardPastroSmartZakarias2012]; cf. [Beaver1991]): when
`op = ∑ i, localMaskedOpening (xy i) (t i)` and `∑ i, (t i).c = (∑ i, (t i).a) * (∑ i, (t i).b)`,
the output shares sum to `(∑ i, (xy i).1) * (∑ i, (xy i).2)`. -/
theorem sum_beaverMulShare_eq_mul {R : Type} [CommRing R] {m : ℕ} [NeZero m]
    (xy : Fin m → R × R) (t : Fin m → TripleShare R)
    (hc : (∑ i : Fin m, (t i).c) = (∑ i : Fin m, (t i).a) * (∑ i : Fin m, (t i).b)) :
    (∑ i : Fin m, beaverMulShare i (∑ j : Fin m, localMaskedOpening (xy j) (t j)) (t i)) =
      (∑ i : Fin m, (xy i).1) * (∑ i : Fin m, (xy i).2) := by
  rw [sum_beaverMulShare, hc]
  simp only [Prod.fst_sum, Prod.snd_sum, localMaskedOpening, Finset.sum_sub_distrib]
  ring

/-! ### Synchronous $m$-party Beaver online multiplication protocol and privacy -/

/-- Schedule for `beaverMulProtocol p m`: one joint `beaverTripleSpec p m` preprocessing call
followed by an all-to-all broadcast of `ZMod p × ZMod p`. -/
@[expose, reducible] def beaverMulSchedule (p m : ℕ) : Schedule m (beaverTripleSpec p m) :=
  .oracle () (Function.Embedding.refl (Fin m)) ::
    broadcastSchedule m (beaverTripleSpec p m) (ZMod p × ZMod p)

/-- Synchronous `m`-party Beaver online multiplication protocol in the `beaverTripleSpec p m`-hybrid
model (generalizing [BonehShoup2023], Section 23.2.2 to `m` parties;
[DamgardPastroSmartZakarias2012]; cf. [Beaver1991]):
1. All `m` parties invoke `beaverTripleSpec p m` to receive triple shares `t_i = (a_i, b_i, c_i)`.
2. Each party `i` broadcasts `localMaskedOpening xy_i t_i = (x_i - a_i, y_i - b_i)`.
3. Each party `i` sums the received openings `op = ∑ j, msgs j` and outputs
   `beaverMulShare i op t_i`. -/
def beaverMulProtocol (p m : ℕ) :
    Protocol m (beaverTripleSpec p m) (beaverMulSchedule p m)
      (fun _ => ZMod p × ZMod p) (fun _ => Unit) (fun _ => ZMod p) where
  sampleCoins _ := pure ()
  steps :=
    Steps.oracle (m := m) (spec := beaverTripleSpec p m)
      (State := fun _ => (ZMod p × ZMod p) × Unit)
      (Out := fun _ => ZMod p)
      (op := ()) (parties := Function.Embedding.refl (Fin m))
      (sc := broadcastSchedule m (beaverTripleSpec p m) (ZMod p × ZMod p))
      (fun _ _ => ())
      (broadcastSteps m (spec := beaverTripleSpec p m)
        (Msg := ZMod p × ZMod p)
        (State := fun i => ((ZMod p × ZMod p) × Unit) ×
          (Round.oracle (spec := beaverTripleSpec p m) ()
            (Function.Embedding.refl (Fin m))).Received i)
        (Out := fun _ => ZMod p)
        (fun i ((xy_i, _), recv) => localMaskedOpening xy_i (recv i rfl))
        (fun i (_, recv) msgs => beaverMulShare i (∑ j : Fin m, msgs j) (recv i rfl)))

/-- Party `i`'s oracle-round received record in `beaverMulProtocol` determined by its own triple
share `ti : TripleShare (ZMod p)`. -/
private def receivedTriple {p m : ℕ} (i : Fin m) (ti : TripleShare (ZMod p)) :
    (Round.oracle (spec := beaverTripleSpec p m) ()
      (Function.Embedding.refl (Fin m))).Received i :=
  fun _ _ => ti

private theorem deliverOracle_refl_eq_receivedTriple {p m : ℕ}
    (t : Fin m → TripleShare (ZMod p)) (i : Fin m) :
    Round.deliverOracle (spec := beaverTripleSpec p m) (op := ())
      (Function.Embedding.refl (Fin m)) t i = receivedTriple i (t i) :=
  Round.received_oracle_ext fun _ hs => congrArg t hs

/-- Construct party `i`'s complete `PartyView` in `beaverMulProtocol` from its input `xy_i`,
its triple share `t_i`, and the vector `msgs` of broadcast masked openings. -/
private def beaverViewOf {p m : ℕ} (i : Fin m) (xy_i : ZMod p × ZMod p)
    (t_i : TripleShare (ZMod p)) (msgs : Fin m → ZMod p × ZMod p) :
    PartyView (fun _ => ZMod p × ZMod p) (fun _ => Unit) (beaverMulSchedule p m) i where
  input := xy_i
  coins := ()
  received := (receivedTriple i t_i, deliverBroadcast (spec := beaverTripleSpec p m) msgs i)

private theorem evalWith_beaverMulProtocol {p m : ℕ} [NeZero p]
    (xy : Fin m → ZMod p × ZMod p) :
    (beaverMulProtocol p m).evalWith (beaverTripleWorld p m) xy =
      (ProbComp.eval (beaverTripleFunctionality p m (fun _ => ()))).map fun t =>
        let msgs : Fin m → ZMod p × ZMod p := fun j => localMaskedOpening (xy j) (t j)
        let op : ZMod p × ZMod p := ∑ j : Fin m, msgs j
        (fun i => beaverViewOf i (xy i) (t i) msgs,
         fun i => beaverMulShare i op (t i)) := by
  rw [Protocol.evalWith_eq]
  change (ProbComp.eval (OracleComp.pi (fun _ : Fin m => (pure () : ProbComp Unit)))).bind _ = _
  rw [ProbComp.eval_pi_pure, PMF.pure_bind]
  simp only [beaverMulProtocol, beaverTripleWorld, Steps.evalWith_oracle,
    evalWith_broadcastSteps, PMF.map_bind, PMF.pure_map]
  rw [PMF.map]
  refine congrArg (PMF.bind (ProbComp.eval (beaverTripleFunctionality p m (fun _ => ()))))
    (funext fun t => congrArg PMF.pure ?_)
  have hdeliv : ∀ i : Fin m,
      Round.deliverOracle (spec := beaverTripleSpec p m) (op := ())
        (Function.Embedding.refl (Fin m)) t i = receivedTriple i (t i) :=
    deliverOracle_refl_eq_receivedTriple t
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · refine PartyView.ext rfl rfl (Prod.ext (hdeliv i) rfl)
  · simp only [Protocol.outputOfView, Steps.outputAt, outputAt_broadcastSteps]
    rfl

/-- Output correctness of `beaverMulProtocol` (`m > 0`): on every execution in the support of
`beaverTripleWorld p m`, the parties' outputs sum to `(∑ i, (xy i).1) * (∑ i, (xy i).2)`. -/
theorem sum_output_beaverMulProtocol {p m : ℕ} [NeZero p] [NeZero m]
    (xy : Fin m → ZMod p × ZMod p)
    {res : ((i : Fin m) → PartyView (fun _ => ZMod p × ZMod p) (fun _ => Unit)
        (beaverMulSchedule p m) i) × ((i : Fin m) → ZMod p)}
    (hres : res ∈ ((beaverMulProtocol p m).evalWith (beaverTripleWorld p m) xy).support) :
    (∑ i : Fin m, res.2 i) = (∑ i : Fin m, (xy i).1) * (∑ i : Fin m, (xy i).2) := by
  rw [evalWith_beaverMulProtocol, PMF.mem_support_map_iff] at hres
  obtain ⟨t, ht, rfl⟩ := hres
  exact sum_beaverMulShare_eq_mul xy t (sum_c_of_mem_support_beaverTripleFunctionality ht)

/-- Proper-coalition simulator for `beaverMulProtocol p m` (generalizing [BonehShoup2023],
Section 23.2.2 to `m` parties; cf. [Beaver1991]): samples independent uniform masks
`aI, bI` for corrupted parties `i ∈ I` and independent uniform masked openings `msgsCompl` for
honest parties `j ∈ Iᶜ`, computes the public sum `op = ∑ j, msgs j`, and sets each corrupted
party's `c_i` share so that `beaverMulShare i op t_i = zI i`. -/
noncomputable def beaverMulSim (p m : ℕ) [NeZero p] (I : Finset (Fin m)) :
    CoalitionSimulator (beaverMulSchedule p m)
      (fun _ => ZMod p × ZMod p) (fun _ => Unit) (fun _ => ZMod p) I :=
  fun xyI zI => do
    let aI ← ProbComp.uniform ((i : I) → ZMod p)
    let bI ← ProbComp.uniform ((i : I) → ZMod p)
    let msgsCompl ← ProbComp.uniform ((j : (Iᶜ : Finset (Fin m))) → ZMod p × ZMod p)
    let msgs : Fin m → ZMod p × ZMod p := fun j =>
      if hj : j ∈ I then
        ((xyI ⟨j, hj⟩).1 - aI ⟨j, hj⟩, (xyI ⟨j, hj⟩).2 - bI ⟨j, hj⟩)
      else
        msgsCompl ⟨j, Finset.mem_compl.mpr hj⟩
    let op : ZMod p × ZMod p := ∑ j : Fin m, msgs j
    return fun i =>
      beaverViewOf i.1 (xyI i)
        { a := aI i
          b := bI i
          c := zI i - ((if i.1.val = 0 then op.1 * op.2 else 0) +
            op.1 * bI i + op.2 * aI i) }
        msgs

/-- Perfect semi-honest privacy of `beaverMulProtocol p m` in `beaverTripleWorld p m` against every
proper static coalition `I ≠ Finset.univ` (`I.card < m`), realizing `sharedMulFunctionality m`
over `ZMod p` (generalizing [BonehShoup2023], Section 23.2.2 to `m` parties; cf. [Beaver1991]). -/
theorem perfectSemiHonestPrivateProper_beaverMul (p m : ℕ) [NeZero p] :
    PerfectSemiHonestPrivateProper (beaverMulProtocol p m) (beaverTripleWorld p m)
      (sharedMulFunctionality m) (beaverMulSim p m) := by
  classical
  intro I hI xy
  obtain ⟨j₀, hj₀⟩ := not_forall.mp (mt Finset.eq_univ_iff_forall.mpr hI)
  have : NeZero m := ⟨Nat.ne_of_gt j₀.pos⟩
  let E : Finset (Fin m) := Finset.univ.erase j₀
  let target : ZMod p := (∑ i : Fin m, (xy i).1) * (∑ i : Fin m, (xy i).2)
  let baseTerm (i : Fin m) (op : ZMod p × ZMod p) (ai bi : ZMod p) : ZMod p :=
    (if i.val = 0 then op.1 * op.2 else 0) + op.1 * bi + op.2 * ai
  -- Bijection between real preprocessing coins `(a, b, cE)` and ideal coins `(zE, aI, bI, msgsC)`.
  let equiv :
      ((Fin m → ZMod p) × (Fin m → ZMod p) × ((k : E) → ZMod p)) ≃
      (((k : E) → ZMod p) × ((i : I) → ZMod p) × ((i : I) → ZMod p) ×
        ((j : (Iᶜ : Finset (Fin m))) → ZMod p × ZMod p)) :=
    { toFun := fun ⟨a, b, cE⟩ =>
        let msgs : Fin m → ZMod p × ZMod p := fun j => ((xy j).1 - a j, (xy j).2 - b j)
        let op : ZMod p × ZMod p := ∑ j : Fin m, msgs j
        (fun k => baseTerm k.1 op (a k.1) (b k.1) + cE k,
         I.restrict a,
         I.restrict b,
         Iᶜ.restrict msgs)
      invFun := fun ⟨zE, aI, bI, msgsC⟩ =>
        let a : Fin m → ZMod p := fun j =>
          if hj : j ∈ I then aI ⟨j, hj⟩ else (xy j).1 - (msgsC ⟨j, Finset.mem_compl.mpr hj⟩).1
        let b : Fin m → ZMod p := fun j =>
          if hj : j ∈ I then bI ⟨j, hj⟩ else (xy j).2 - (msgsC ⟨j, Finset.mem_compl.mpr hj⟩).2
        let msgs : Fin m → ZMod p × ZMod p := fun j => ((xy j).1 - a j, (xy j).2 - b j)
        let op : ZMod p × ZMod p := ∑ j : Fin m, msgs j
        (a, b, fun k => zE k - baseTerm k.1 op (a k.1) (b k.1))
      left_inv := fun ⟨a, b, cE⟩ => by
        have ha : (fun j => if hj : j ∈ I then a j else (xy j).1 - ((xy j).1 - a j)) = a := by
          ext j; by_cases hj : j ∈ I <;> simp [hj]
        have hb : (fun j => if hj : j ∈ I then b j else (xy j).2 - ((xy j).2 - b j)) = b := by
          ext j; by_cases hj : j ∈ I <;> simp [hj]
        refine Prod.ext ha (Prod.ext hb ?_)
        ext k
        let fa : Fin m → ZMod p :=
          fun j => if hj : j ∈ I then a j else (xy j).1 - ((xy j).1 - a j)
        let fb : Fin m → ZMod p :=
          fun j => if hj : j ∈ I then b j else (xy j).2 - ((xy j).2 - b j)
        change baseTerm k.1 (∑ j : Fin m, ((xy j).1 - a j, (xy j).2 - b j)) (a k.1) (b k.1) +
            cE k -
          baseTerm k.1 (∑ j : Fin m, ((xy j).1 - fa j, (xy j).2 - fb j)) (fa k.1) (fb k.1) = cE k
        have hfa : fa = a := ha
        have hfb : fb = b := hb
        rw [hfa, hfb]
        exact add_sub_cancel_left _ _
      right_inv := fun ⟨zE, aI, bI, msgsC⟩ => by
        dsimp only
        refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
        · ext k
          exact add_sub_cancel _ _
        · ext ⟨i, hi⟩
          simp [Finset.restrict, hi]
        · ext ⟨i, hi⟩
          simp [Finset.restrict, hi]
        · ext ⟨j, hj⟩ <;> simp [Finset.restrict, Finset.mem_compl.mp hj] }
  -- Express `realJoint` as a single map over `uniformOfFintype` of `(a, b, cE)`.
  have hreal :
      (beaverMulProtocol p m).realJoint (beaverTripleWorld p m) I xy =
        (PMF.uniformOfFintype
          ((Fin m → ZMod p) × (Fin m → ZMod p) × ((k : E) → ZMod p))).map fun ⟨a, b, cE⟩ =>
            let c := ProbComp.completeSharesErase j₀ ((∑ i : Fin m, a i) * (∑ i : Fin m, b i)) cE
            let t : Fin m → TripleShare (ZMod p) := fun i => ⟨a i, b i, c i⟩
            let msgs : Fin m → ZMod p × ZMod p := fun j => localMaskedOpening (xy j) (t j)
            let op : ZMod p × ZMod p := ∑ j : Fin m, msgs j
            (fun i : I => beaverViewOf i.1 (xy i.1) (t i.1) msgs,
             fun i : Fin m => beaverMulShare i op (t i)) := by
    simp only [pmf_norm, Protocol.realJoint, evalWith_beaverMulProtocol, beaverTripleFunctionality,
      bind_pure_comp, ProbComp.eval_uniform,
      ProbComp.eval_sampleAdditiveShares_eq_map_completeSharesErase j₀,
      PMF.uniformOfFintype_bind_map]
    refine congrArg (PMF.map · _) (funext fun ⟨a, b, cE⟩ => rfl)
  -- Express `idealJoint` as a single map over `uniformOfFintype` of `(zE, aI, bI, msgsC)`.
  have hideal :
      ProbComp.eval (idealJoint (sharedMulFunctionality m) I (beaverMulSim p m I) xy) =
        (PMF.uniformOfFintype
          (((k : E) → ZMod p) × ((i : I) → ZMod p) × ((i : I) → ZMod p) ×
            ((j : (Iᶜ : Finset (Fin m))) → ZMod p × ZMod p))).map
          fun ⟨zE, aI, bI, msgsC⟩ =>
            let z := ProbComp.completeSharesErase j₀ target zE
            let msgs : Fin m → ZMod p × ZMod p := fun j =>
              if hj : j ∈ I then ((xy j).1 - aI ⟨j, hj⟩, (xy j).2 - bI ⟨j, hj⟩)
              else msgsC ⟨j, Finset.mem_compl.mpr hj⟩
            let op : ZMod p × ZMod p := ∑ j : Fin m, msgs j
            (fun i : I =>
              beaverViewOf i.1 (xy i.1)
                { a := aI i
                  b := bI i
                  c := z i.1 - baseTerm i.1 op (aI i) (bI i) }
                msgs,
             z) := by
    simp only [pmf_norm, idealJoint, sharedMulFunctionality, beaverMulSim, bind_pure_comp,
      ProbComp.eval_uniform, ProbComp.eval_sampleAdditiveShares_eq_map_completeSharesErase j₀,
      PMF.uniformOfFintype_bind_map]
    refine congrArg (PMF.map · _) (funext fun ⟨zE, aI, bI, msgsC⟩ => rfl)
  rw [hideal, hreal, ← PMF.uniformOfFintype_map_equiv equiv, PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun ⟨a, b, cE⟩ => ?_)
  dsimp only [Function.comp_def, equiv]
  simp only [Equiv.coe_fn_mk]
  dsimp only [Finset.restrict]
  simp only [dite_eq_ite, ite_self]
  let c := ProbComp.completeSharesErase j₀ ((∑ i : Fin m, a i) * (∑ i : Fin m, b i)) cE
  let t : Fin m → TripleShare (ZMod p) := fun i => ⟨a i, b i, c i⟩
  let msgs : Fin m → ZMod p × ZMod p := fun j => localMaskedOpening (xy j) (t j)
  let op : ZMod p × ZMod p := ∑ j : Fin m, msgs j
  let z : Fin m → ZMod p := fun i => beaverMulShare i op (t i)
  have hc_sum : (∑ i : Fin m, (t i).c) = (∑ i : Fin m, (t i).a) * (∑ i : Fin m, (t i).b) :=
    ProbComp.sum_completeSharesErase j₀ _ cE
  have hz_sum : ∑ i : Fin m, z i = target :=
    sum_beaverMulShare_eq_mul xy t hc_sum
  have hzE : (fun k : E => baseTerm k.1 op (a k.1) (b k.1) + cE k) = E.restrict z := by
    ext ⟨k, hk⟩
    have hne : k ≠ j₀ := (Finset.mem_erase.mp hk).1
    have hck : c k = cE ⟨k, hk⟩ := by simp [c, ProbComp.completeSharesErase, hne]
    simp [Finset.restrict, z, beaverMulShare, baseTerm, t, hck, add_assoc]
  have hz_eq :
      ProbComp.completeSharesErase j₀ target
        (fun k : E => baseTerm k.1 op (a k.1) (b k.1) + cE k) = z := by
    rw [hzE]
    exact ProbComp.completeSharesErase_restrict_erase j₀ hz_sum
  change (fun i : I =>
      beaverViewOf i.1 (xy i.1)
        { a := a i.1
          b := b i.1
          c := ProbComp.completeSharesErase j₀ target
              (fun k : E => baseTerm k.1 op (a k.1) (b k.1) + cE k) i.1 -
            baseTerm i.1 op (a i.1) (b i.1) }
        msgs,
      ProbComp.completeSharesErase j₀ target
        (fun k : E => baseTerm k.1 op (a k.1) (b k.1) + cE k)) =
    (fun i : I => beaverViewOf i.1 (xy i.1) (t i.1) msgs, z)
  rw [hz_eq]
  refine Prod.ext (funext fun ⟨i, _⟩ => ?_) rfl
  have hzi : z i - baseTerm i op (a i) (b i) = c i := by
    simp [z, beaverMulShare, baseTerm, t, add_assoc]
  dsimp only [t]
  rw [hzi]

/-! ### Additive-error tampered-opening attack illustration on unauthenticated 2-party Beaver
multiplication -/

/-- Malicious party `1`'s tampered masked opening in 2-party Beaver multiplication of `[x] * [0]`
(motivated by [BonehShoup2023], Section 23.2.4): holding input `(0, 0)` and triple share `t₁`,
party `1` adds an additive error `1` to its second opening coordinate `-t₁.b`. -/
@[expose] def tamperedOpening {R : Type} [AddGroup R] [One R]
    (t₁ : TripleShare R) : R × R :=
  (-t₁.a, -t₁.b + 1)

/-- Malicious party `1`'s deterministic extraction formula recovering party `0`'s secret input `x`
from party `0`'s masked opening `op₀` and opened Beaver output share `z'₀` (assuming the output
share `z'₀` is subsequently revealed). -/
@[expose] def tamperedOpeningExtract {R : Type} [CommRing R]
    (t₁ : TripleShare R) (op₀ : R × R) (z'₀ : R) : R :=
  let op := op₀ + tamperedOpening t₁
  z'₀ + (op.1 * t₁.b + op.2 * t₁.a + t₁.c)

/-- Algebraic identity behind the additive-error tampered-opening attack (original 2-party
illustration of output-opening tampering, motivated by [BonehShoup2023], Section 23.2.4): for every
valid 2-party Beaver triple `t` (`c₀ + c₁ = (a₀ + a₁) * (b₀ + b₁)`), if honest party `0`'s output
share `z'₀` is opened after party `1` broadcasts `tamperedOpening (t 1)`, then
`tamperedOpeningExtract` recovers honest party `0`'s private input `x` identically. -/
theorem tamperedOpeningExtract_eq {R : Type} [CommRing R]
    (x : R) (t : Fin 2 → TripleShare R)
    (hc : (t 0).c + (t 1).c = ((t 0).a + (t 1).a) * ((t 0).b + (t 1).b)) :
    let op₀ := localMaskedOpening (x, 0) (t 0)
    let z'₀ := beaverMulShare (m := 2) 0 (op₀ + tamperedOpening (t 1)) (t 0)
    tamperedOpeningExtract (t 1) op₀ z'₀ = x := by
  dsimp only [tamperedOpeningExtract, beaverMulShare, localMaskedOpening, tamperedOpening]
  simp only [Fin.val_zero, ↓reduceIte, Prod.fst_add, Prod.snd_add, zero_sub]
  linear_combination hc

/-- Standalone 2-party tampered-opening experiment on `[z] = [x] * [0]` over `ZMod p` (assuming
an unauthenticated output-share opening `z'₀`): samples a fresh triple from
`beaverTripleFunctionality p 2`, computes honest party `0`'s masked opening `op₀` and opened
output share `z'₀` on `(x, 0)` against `tamperedOpening (t 1)`, and outputs party `1`'s extracted
value. -/
noncomputable def tamperedOpeningReal (p : ℕ) [NeZero p] (x : ZMod p) : ProbComp (ZMod p) := do
  let t ← beaverTripleFunctionality p 2 (fun _ => ())
  let op₀ := localMaskedOpening (x, 0) (t 0)
  let z'₀ := beaverMulShare (m := 2) 0 (op₀ + tamperedOpening (t 1)) (t 0)
  return tamperedOpeningExtract (t 1) op₀ z'₀

/-- Exact secret recovery: `tamperedOpeningReal p x` outputs `x` with probability `1`. -/
@[simp] theorem eval_tamperedOpeningReal (p : ℕ) [NeZero p] (x : ZMod p) :
    ProbComp.eval (tamperedOpeningReal p x) = PMF.pure x := by
  simp only [tamperedOpeningReal, bind_pure_comp, ProbComp.eval_map]
  calc (ProbComp.eval (beaverTripleFunctionality p 2 (fun _ => ()))).map _
      = (ProbComp.eval (beaverTripleFunctionality p 2 (fun _ => ()))).map (fun _ => x) := by
          refine PMF.map_congr_on_support _ _ _ fun t ht => ?_
          have hc := sum_c_of_mem_support_beaverTripleFunctionality ht
          simp only [Fin.sum_univ_two] at hc
          exact tamperedOpeningExtract_eq x t hc
    _ = PMF.pure x := PMF.map_const _ x

/-- Toy distinguishing test checking whether a candidate value equals `1 : ZMod p`. -/
noncomputable def tamperedOpeningTestOne (p : ℕ) (prog : ProbComp (ZMod p)) : Game :=
  ProbComp.eval do
    let g ← prog
    return decide (g = (1 : ZMod p))

/-- Original standalone `Game` illustration: for `2 ≤ p` and any `x`-independent guessing
program `blindGuess : ProbComp (ZMod p)`, the sum of distinguishing advantages of
`tamperedOpeningTestOne` between `tamperedOpeningReal p 0` / `tamperedOpeningReal p 1` and
`blindGuess` is at least `1`. -/
theorem one_le_add_advantage_tamperedOpening {p : ℕ} [NeZero p] (hp : 2 ≤ p)
    (blindGuess : ProbComp (ZMod p)) :
    (1 : ℝ≥0) ≤
      Game.advantage (tamperedOpeningTestOne p (tamperedOpeningReal p 0))
        (tamperedOpeningTestOne p blindGuess) +
      Game.advantage (tamperedOpeningTestOne p (tamperedOpeningReal p 1))
        (tamperedOpeningTestOne p blindGuess) := by
  have : Fact (1 < p) := ⟨hp⟩
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  have hreal0 : tamperedOpeningTestOne p (tamperedOpeningReal p 0) = PMF.pure false := by
    simp [tamperedOpeningTestOne, bind_pure_comp, h01]
  have hreal1 : tamperedOpeningTestOne p (tamperedOpeningReal p 1) = PMF.pure true := by
    simp [tamperedOpeningTestOne, bind_pure_comp]
  have h1 : Game.advantage (PMF.pure false) (PMF.pure true) = 1 := by
    rw [Game.advantage_pure_false_left]
    simp [Game.succProbability]
  calc (1 : ℝ≥0)
      = Game.advantage (tamperedOpeningTestOne p (tamperedOpeningReal p 0))
          (tamperedOpeningTestOne p (tamperedOpeningReal p 1)) := by
          rw [hreal0, hreal1, h1]
    _ ≤ Game.advantage (tamperedOpeningTestOne p (tamperedOpeningReal p 0))
          (tamperedOpeningTestOne p blindGuess) +
        Game.advantage (tamperedOpeningTestOne p blindGuess)
          (tamperedOpeningTestOne p (tamperedOpeningReal p 1)) :=
          Game.advantage_triangle _ _ _
    _ = Game.advantage (tamperedOpeningTestOne p (tamperedOpeningReal p 0))
          (tamperedOpeningTestOne p blindGuess) +
        Game.advantage (tamperedOpeningTestOne p (tamperedOpeningReal p 1))
          (tamperedOpeningTestOne p blindGuess) := by
          rw [Game.advantage_comm (tamperedOpeningTestOne p blindGuess)]

/-- Standalone hidden-bit game for `tamperedOpeningReal`: samples a uniform secret bit `b` for
party `0`'s input `x ∈ {0, 1}`, runs `tamperedOpeningReal p x`, and tests whether the extracted
value equals `x`. -/
noncomputable def tamperedOpeningRealBitGame (p : ℕ) [NeZero p] : Game :=
  ProbComp.eval do
    let b ← ProbComp.uniform Bool
    let x : ZMod p := if b then 1 else 0
    let guess ← tamperedOpeningReal p x
    return decide (guess = x)

/-- Standalone reference hidden-bit game for an input-independent guessing program
`blindGuess : ProbComp (ZMod p)` that does not depend on the secret bit `b`. -/
noncomputable def tamperedOpeningIdealBitGame (p : ℕ) (blindGuess : ProbComp (ZMod p)) : Game :=
  ProbComp.eval do
    let b ← ProbComp.uniform Bool
    let x : ZMod p := if b then 1 else 0
    let guess ← blindGuess
    return decide (guess = x)

/-- Original standalone `Game` illustration: for every modulus `p ≥ 2` and every
input-independent guessing program `blindGuess : ProbComp (ZMod p)`, `tamperedOpeningRealBitGame p`
achieves distinguishing advantage at least `1 / 2` over `tamperedOpeningIdealBitGame p blindGuess`.
-/
theorem le_advantage_tamperedOpeningBitGame {p : ℕ} [NeZero p] (hp : 2 ≤ p)
    (blindGuess : ProbComp (ZMod p)) :
    (1 / 2 : ℝ≥0) ≤
      Game.advantage (tamperedOpeningRealBitGame p) (tamperedOpeningIdealBitGame p blindGuess) := by
  have : Fact (1 < p) := ⟨hp⟩
  have hreal : tamperedOpeningRealBitGame p = PMF.pure true := by
    simp only [pmf_norm, tamperedOpeningRealBitGame, bind_pure_comp, eval_tamperedOpeningReal,
      decide_true]
    exact PMF.bind_const _ (PMF.pure true)
  have hideal_le : (tamperedOpeningIdealBitGame p blindGuess) true ≤ (2 : ℝ≥0∞)⁻¹ := by
    simp only [tamperedOpeningIdealBitGame, bind_pure_comp, ProbComp.eval_bind,
      ProbComp.eval_map, ProbComp.eval_uniform, PMF.map]
    rw [PMF.bind_comm]
    apply Cslib.Probability.PMF.bind_apply_le_on_support
    intro g _
    rw [PMF.bind_apply, tsum_bool]
    by_cases hg0 : g = 0
    · simp [PMF.uniformOfFintype_apply, hg0]
    · by_cases hg1 : g = 1
      · simp [PMF.uniformOfFintype_apply, hg1]
      · simp [PMF.uniformOfFintype_apply, hg0, hg1]
  rw [← NNReal.coe_le_coe, Game.coe_advantage, hreal]
  have hsucc_real : (Game.succProbability (PMF.pure true) : ℝ) = 1 := by
    simp [Game.succProbability]
  have hsucc_ideal :
      (Game.succProbability (tamperedOpeningIdealBitGame p blindGuess) : ℝ) ≤ 1 / 2 := by
    rw [Game.coe_succProbability]
    have htr := ENNReal.toReal_mono (by simp) hideal_le
    simpa [ENNReal.toReal_inv, ENNReal.toReal_ofNat, one_div] using htr
  rw [hsucc_real]
  have hcast : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  rw [hcast]
  linarith [le_abs_self (1 - (Game.succProbability (tamperedOpeningIdealBitGame p blindGuess) : ℝ))]

end Cslib.Crypto.Protocols.MPC.Beaver
