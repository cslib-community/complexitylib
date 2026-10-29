/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.MPC.Basic
public import Complexity.Probability.PMF.Bind
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Ideal $\text{OT}_1^4$, 2-Party Shared Multiplication, and Pairwise $m$-Party Reduction

This module formalizes the shared-multiplication functionalities and oracle-aided privacy
reductions from Goldreich's *Foundations of Cryptography, Volume 2: Basic Applications*:

1. **1-out-of-4 Oblivious Transfer (`ot14Spec`, `ot14World`):** the asymmetric 2-party ideal
   oracle specification and world (Section 7.3.2, Eq. 7.20, print p. 640, for $k = 4$) in which
   slot `0` (sender) submits a 4-tuple of bits `Fin 4 → Bool` and receives `Unit`, while slot `1`
   (receiver) submits an index `Fin 4` and receives the selected bit.
2. **$m$-Party Shared Multiplication (`sharedMulFunctionality`, `sharedMulSpec`,
   `sharedMulWorld`):** the randomized $m$-party functionality mapping
   $((a_1, b_1), \dots, (a_m, b_m))$ to uniform additive shares $(c_1, \dots, c_m) \in \{0, 1\}^m$
   summing to $(\sum_i a_i) \cdot (\sum_i b_i)$ over $\mathrm{GF}(2)$ (`BooleanRing Bool`)
   (Section 7.3, Eqs. 7.17–7.18, print p. 635 for $m = 2$; Section 7.5.2, Eqs. 7.44–7.45,
   print p. 701 for general $m$).
3. **2-Party Shared Multiplication in the $\text{OT}_1^4$-Hybrid Model (`twoPartyMulProtocol`,
   `twoPartyMulSim`, `perfectSemiHonestPrivate_twoPartyMul`):** Construction 7.3.7 and
   Proposition 7.3.8 (Section 7.3.3, Eq. 7.21, print pp. 643–644), proved perfectly semi-honest
   private against every static coalition `I : Finset (Fin 2)`.
4. **Pairwise $m$-Party Shared Multiplication Reduction (`multiPartyMulProtocol`,
   `multiPartyMulSim`, `perfectSemiHonestPrivate_multiPartyMul`):** Construction 7.5.8 and
   Proposition 7.5.9 (Section 7.5.2.2, Eqs. 7.46–7.47, print pp. 703–705), reducing $m$-party
   shared multiplication to pairwise invocations of the 2-party shared-multiplication oracle
   `sharedMulSpec 2` over all ordered pairs $i < j$, proved perfectly semi-honest private against
   every static coalition `I : Finset (Fin m)`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.ot14Spec`, `Cslib.Crypto.Protocols.MPC.ot14World`: 2-party
  $\text{OT}_1^4$ oracle specification and ideal world.
* `Cslib.Crypto.Protocols.MPC.sharedMulFunctionality`,
  `Cslib.Crypto.Protocols.MPC.sharedMulSpec`, `Cslib.Crypto.Protocols.MPC.sharedMulWorld`:
  $m$-party shared-multiplication functionality, oracle specification, and ideal world.
* `Cslib.Crypto.Protocols.MPC.twoPartyMulSchedule`,
  `Cslib.Crypto.Protocols.MPC.twoPartyMulProtocol`, `Cslib.Crypto.Protocols.MPC.twoPartyMulSim`:
  Construction 7.3.7 and its coalition simulator.
* `Cslib.Crypto.Protocols.MPC.multiPartyMulSchedule`,
  `Cslib.Crypto.Protocols.MPC.multiPartyMulProtocol`,
  `Cslib.Crypto.Protocols.MPC.multiPartyMulSim`: Construction 7.5.8 and its coalition simulator.

## Main results

* `Cslib.Crypto.Protocols.MPC.perfectSemiHonestPrivate_twoPartyMul`: Proposition 7.3.8 (print
  p. 644), perfect semi-honest privacy of `twoPartyMulProtocol` in `ot14World` against every static
  coalition `I : Finset (Fin 2)`.
* `Cslib.Crypto.Protocols.MPC.perfectSemiHonestPrivate_multiPartyMul`: Proposition 7.5.9 (print
  pp. 704–705), perfect semi-honest privacy of `multiPartyMulProtocol m` in `sharedMulWorld 2`
  against every static coalition `I : Finset (Fin m)`.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.3 (Eqs. 7.17–7.18, p. 635), Section 7.3.2 (Eq. 7.20, p. 640), Section 7.3.3
  (Construction 7.3.7, Eq. 7.21, Proposition 7.3.8, pp. 643–644), Section 7.5.2 (Eqs. 7.44–7.45,
  p. 701), and Section 7.5.2.2 (Eqs. 7.46–7.47, Construction 7.5.8, Proposition 7.5.9,
  pp. 703–705).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp

/-! ### Ideal $\text{OT}_1^4$ and $m$-party shared multiplication -/

/-- 2-party 1-out-of-4 Oblivious Transfer oracle specification (Goldreich Section 7.3.2, Eq. 7.20,
p. 640, for $k = 4$): slot `0` (sender) submits a 4-tuple of bits `Fin 4 → Bool` and receives
`Unit`; slot `1` (receiver) submits an index `Fin 4` and receives the selected bit `Bool`. -/
@[reducible] def ot14Spec : MultiOracleSpec where
  Op := Unit
  arity _ := 2
  Query _ := Fin.cases (Fin 4 → Bool) (fun _ => Fin 4)
  Answer _ := Fin.cases Unit (fun _ => Bool)

/-- Answer tuple for `ot14Spec` on query `q`: returns `()` to slot `0` and `(q 0) (q 1)` to
slot `1`. -/
def ot14Answer (q : (s : Fin 2) → ot14Spec.Query () s) (s : Fin 2) : ot14Spec.Answer () s :=
  Fin.cases () (fun _ => q 0 (q 1)) s

/-- Ideal memoryless world for `ot14Spec` (Goldreich Section 7.3.2, Eq. 7.20, p. 640): returns
`()` to the sender (slot `0`) and `(q 0) (q 1)` to the receiver (slot `1`). -/
def ot14World : MultiOracleWorld ot14Spec :=
  fun _ q => pure (ot14Answer q)

/-- Randomized `m`-party shared-multiplication functionality over $\mathrm{GF}(2)$
(Goldreich Section 7.3, Eqs. 7.17–7.18, p. 635 for $m = 2$; Section 7.5.2, Eqs. 7.44–7.45, p. 701
for general $m$): samples uniform additive shares summing to
$(\sum_{i=1}^m a_i) \cdot (\sum_{i=1}^m b_i)$. -/
noncomputable def sharedMulFunctionality (m : ℕ) :
    Functionality m (fun _ => Bool × Bool) (fun _ => Bool) :=
  fun x => ProbComp.sampleAdditiveShares m ((∑ i : Fin m, (x i).1) * (∑ i : Fin m, (x i).2))

/-- `m`-ary oracle specification for shared multiplication (`sharedMulFunctionality m`). -/
@[reducible] def sharedMulSpec (m : ℕ) : MultiOracleSpec where
  Op := Unit
  arity _ := m
  Query _ _ := Bool × Bool
  Answer _ _ := Bool

/-- Ideal memoryless world for `sharedMulSpec m` backed by `sharedMulFunctionality m`. -/
noncomputable def sharedMulWorld (m : ℕ) :
    MultiOracleWorld (sharedMulSpec m) :=
  fun _ q => sharedMulFunctionality m q

/-! ### Construction 7.3.7 and Proposition 7.3.8: 2-party shared multiplication -/

/-- Encode a pair of bits `(a, b) : Bool × Bool` as `2 * a + b` in `Fin 4` (0-indexed version of
Goldreich Construction 7.3.7's `1 + 2a₂ + b₂ ∈ {1, 2, 3, 4}`, p. 643). -/
def boolPairToFin4 (p : Bool × Bool) : Fin 4 :=
  ⟨2 * p.1.toNat + p.2.toNat, by cases p.1 <;> cases p.2 <;> decide⟩

/-- Decode an index in `Fin 4` to its pair of bits `Bool × Bool`. -/
def fin4ToBoolPair (idx : Fin 4) : Bool × Bool :=
  (decide (2 ≤ idx.1), decide (idx.1 % 2 = 1))

@[simp] theorem fin4ToBoolPair_boolPairToFin4 (p : Bool × Bool) :
    fin4ToBoolPair (boolPairToFin4 p) = p := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- Residual function $f_{a,b}(x, y, z) = z + (x + a) \cdot (y + b)$ over $\mathrm{GF}(2)$ from
Goldreich Construction 7.3.7, Step 2 (p. 643). -/
def twoPartyMulResidual (ab xy : Bool × Bool) (z : Bool) : Bool :=
  z + (xy.1 + ab.1) * (xy.2 + ab.2)

/-- Schedule for `twoPartyMulProtocol`: a single joint 2-party invocation of `ot14Spec` with
party `0` as sender and party `1` as receiver. -/
@[reducible] def twoPartyMulSchedule : Schedule 2 ot14Spec :=
  [.oracle () (Function.Embedding.refl (Fin 2))]

/-- Coin sampler for `twoPartyMulProtocol`: party `0` samples a uniform bit; party `1` uses `()`. -/
noncomputable def twoPartyMulSampleCoins (i : Fin 2) :
    ProbComp (Fin.cases Bool (fun _ => Unit) i) :=
  Fin.cases (ProbComp.uniform Bool) (fun _ => pure ()) i

/-- Package party `0`'s coin `c₀ : Bool` and party `1`'s coin `() : Unit` into the 2-party coin
tuple. -/
def twoPartyMulCoins (c₀ : Bool) (i : Fin 2) : Fin.cases Bool (fun _ => Unit) i :=
  Fin.cases c₀ (fun _ => ()) i

/-- Oracle query function for `twoPartyMulProtocol` (Eq. 7.21, p. 643). -/
def twoPartyMulQuery (s : Fin (ot14Spec.arity ()))
    (st : (Bool × Bool) × Fin.cases Bool (fun _ => Unit) (Function.Embedding.refl (Fin 2) s)) :
    ot14Spec.Query () s :=
  Fin.cases
    (fun (st : (Bool × Bool) × Bool) idx => twoPartyMulResidual (fin4ToBoolPair idx) st.1 st.2)
    (fun _ st => boolPairToFin4 st.1) s st

/-- Output extraction function for `twoPartyMulProtocol`. -/
def twoPartyMulOutput (i : Fin 2)
    (st : ((Bool × Bool) × Fin.cases Bool (fun _ => Unit) i) ×
      (Round.oracle (spec := ot14Spec) () (Function.Embedding.refl (Fin 2))).Received i) : Bool :=
  Fin.cases
    (fun (st : ((Bool × Bool) × Bool) × _) => st.1.2)
    (fun j st => st.2 j.succ rfl) i st

/-- Construction 7.3.7 (p. 643): 2-party shared multiplication in the `ot14Spec`-hybrid model.
Party `0` samples a uniform bit `c₀`, submits the 4-tuple of residual values
`fun idx => twoPartyMulResidual (fin4ToBoolPair idx) (a₀, b₀) c₀` (Eq. 7.21, p. 643) as sender in
`ot14Spec`, and outputs `c₀`. Party `1` submits `boolPairToFin4 (a₁, b₁)` as receiver in
`ot14Spec` and outputs the received bit `c₀ + (a₀ + a₁) * (b₀ + b₁)`. -/
noncomputable def twoPartyMulProtocol :
    Protocol 2 ot14Spec twoPartyMulSchedule
      (fun _ => Bool × Bool) (Fin.cases Bool (fun _ => Unit)) (fun _ => Bool) where
  sampleCoins := twoPartyMulSampleCoins
  steps := .oracle twoPartyMulQuery (.done twoPartyMulOutput)

/-- Received oracle record for party `i` in `twoPartyMulProtocol` when its output is `yi`. -/
def twoPartyMulReceived (i : Fin 2) (yi : Bool) :
    (Round.oracle (spec := ot14Spec) () (Function.Embedding.refl (Fin 2))).Received i :=
  fun s _ => Fin.cases () (fun _ => yi) s

/-- Reconstruct party `i`'s complete `PartyView` in `twoPartyMulProtocol` deterministically from
its input `xi : Bool × Bool` and its output `yi : Bool` (Goldreich Proposition 7.3.8 Proof Sketch,
p. 644): for party `0`, its coin is `yi` and its oracle answer is `()`; for party `1`, its coin is
`()` and its oracle answer is `yi`. -/
def twoPartyMulViewOfInOut (i : Fin 2) (xi : Bool × Bool) (yi : Bool) :
    PartyView (fun _ => Bool × Bool) (Fin.cases Bool (fun _ => Unit)) twoPartyMulSchedule i where
  input := xi
  coins := twoPartyMulCoins yi i
  received := (twoPartyMulReceived i yi, ())

/-- Coalition simulator for `twoPartyMulProtocol` (Goldreich Proposition 7.3.8, p. 644): each
corrupted party `i ∈ I` deterministically forms its view from its own input `xI i` and output
`yI i`. -/
def twoPartyMulSim (I : Finset (Fin 2)) :
    CoalitionSimulator twoPartyMulSchedule
      (fun _ => Bool × Bool) (Fin.cases Bool (fun _ => Unit)) (fun _ => Bool) I :=
  fun xI yI => pure (fun i => twoPartyMulViewOfInOut i.1 (xI i) (yI i))

private theorem uniformOfFintype_fin1_bool :
    PMF.uniformOfFintype (Fin 1 → Bool) =
      (PMF.uniformOfFintype Bool).map (fun (b : Bool) (_ : Fin 1) => b) :=
  (PMF.uniformOfFintype_map_equiv (Equiv.funUnique (Fin 1) Bool).symm).symm

private theorem twoPartyMul_target_eq (x : Fin 2 → Bool × Bool) :
    ((∑ i : Fin 2, (x i).1) * (∑ i : Fin 2, (x i).2)) =
      ((x 0).1 + (x 1).1) * ((x 0).2 + (x 1).2) := by
  simp [Fin.sum_univ_two]

instance instFintypeFinCasesBoolUnit (i : Fin 2) : Fintype (Fin.cases Bool (fun _ => Unit) i) :=
  Fin.cases (inferInstanceAs (Fintype Bool)) (fun _ => inferInstanceAs (Fintype Unit)) i

private theorem eval_pi_twoPartyMulCoins :
    ProbComp.eval (OracleComp.pi twoPartyMulProtocol.sampleCoins) =
      (PMF.uniformOfFintype Bool).map twoPartyMulCoins := by
  ext r
  rw [ProbComp.eval_pi, PMF.pi_apply, Fin.prod_univ_two, PMF.map_apply]
  have hr : r = twoPartyMulCoins (r 0) := by
    ext i
    fin_cases i <;> rfl
  have h0 : ProbComp.eval (twoPartyMulProtocol.sampleCoins 0) (r 0) =
      PMF.uniformOfFintype Bool (r 0) :=
    congrFun (congrArg DFunLike.coe (ProbComp.eval_uniform (α := Bool))) (r 0)
  have h1 : ProbComp.eval (twoPartyMulProtocol.sampleCoins 1) (r 1) = 1 :=
    PMF.pure_apply_self ()
  rw [h0, h1, mul_one, tsum_bool]
  have hne : twoPartyMulCoins false ≠ twoPartyMulCoins true :=
    fun h => Bool.false_ne_true (congrFun h 0)
  cases hr0 : r 0
  · have heq : r = twoPartyMulCoins false := hr0 ▸ hr
    simp [heq, hne]
  · have heq : r = twoPartyMulCoins true := hr0 ▸ hr
    simp [heq, hne.symm]

private theorem evalWith_twoPartyMulProtocol (x : Fin 2 → Bool × Bool) :
    twoPartyMulProtocol.evalWith ot14World x =
      (ProbComp.eval (sharedMulFunctionality 2 x)).map fun y =>
        (fun i => twoPartyMulViewOfInOut i (x i) (y i), y) := by
  rw [Protocol.evalWith_eq, eval_pi_twoPartyMulCoins]
  simp only [Protocol.outputOfView, twoPartyMulProtocol, ot14World,
    Steps.evalWith_oracle, Steps.evalWith_done, Steps.outputAt, ProbComp.eval_pure,
    PMF.bind_map, PMF.pure_bind, PMF.pure_map, Function.comp_def]
  rw [sharedMulFunctionality, sampleAdditiveShares, ProbComp.eval_map, ProbComp.eval_uniform,
    PMF.map_comp, uniformOfFintype_fin1_bool, PMF.map_comp]
  refine congrArg (PMF.map · (PMF.uniformOfFintype Bool)) (funext fun c₀ => ?_)
  have htarget :
      twoPartyMulResidual (fin4ToBoolPair (boolPairToFin4 (x 1))) (x 0) c₀ =
        completeShares 2 ((∑ i : Fin 2, (x i).1) * (∑ i : Fin 2, (x i).2))
          (fun _ => c₀) 1 := by
    rw [fin4ToBoolPair_boolPairToFin4, twoPartyMul_target_eq]
    change c₀ + ((x 0).1 + (x 1).1) * ((x 0).2 + (x 1).2) =
      completeShares 2 (((x 0).1 + (x 1).1) * ((x 0).2 + (x 1).2)) (fun _ => c₀) (⊤ : Fin 2)
    rw [completeShares_top]
    simp [BooleanRing.sub_eq_add, add_comm]
  have hc₀ :
      c₀ =
        completeShares 2 ((∑ i : Fin 2, (x i).1) * (∑ i : Fin 2, (x i).2))
          (fun _ => c₀) 0 := by
    exact (completeShares_castLE 2 _ (fun _ => c₀) 0).symm
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · fin_cases i
    · refine PartyView.ext rfl ?_ (Prod.ext ?_ rfl)
      · exact hc₀
      · refine Round.received_oracle_ext fun s hs => ?_
        fin_cases s
        · rfl
        · contradiction
    · refine PartyView.ext rfl rfl (Prod.ext ?_ rfl)
      refine Round.received_oracle_ext fun s hs => ?_
      fin_cases s
      · contradiction
      · exact htarget
  · fin_cases i
    · exact hc₀
    · exact htarget

/-- Proposition 7.3.8 (p. 644): Construction 7.3.7 is perfectly semi-honest private in `ot14World`
against every static coalition `I : Finset (Fin 2)`. -/
theorem perfectSemiHonestPrivate_twoPartyMul :
    PerfectSemiHonestPrivate twoPartyMulProtocol ot14World
      (sharedMulFunctionality 2) twoPartyMulSim := by
  intro I x
  simp only [idealJoint, twoPartyMulSim, map_pure, bind_pure_comp, ProbComp.eval_map,
    Protocol.realJoint, evalWith_twoPartyMulProtocol, PMF.map_comp]
  rfl

/-! ### Construction 7.5.8 and Proposition 7.5.9: pairwise $m$-party reduction -/

/-- An ordered pair `(i, j)` of parties in `Fin m` with `i < j`. -/
abbrev OrderedPair (m : ℕ) : Type :=
  { p : Fin m × Fin m // p.1 < p.2 }

/-- Embedding of `Fin 2` into `Fin m` sending `0 ↦ p.1.1` and `1 ↦ p.1.2` for an ordered pair
`p : OrderedPair m`. -/
def pairEmbedding {m : ℕ} (p : OrderedPair m) : Fin 2 ↪ Fin m where
  toFun := Fin.cases p.1.1 (fun _ => p.1.2)
  inj' a b h := by
    fin_cases a <;> fin_cases b
    · rfl
    · exact (ne_of_lt p.2 h).elim
    · exact (ne_of_gt p.2 h).elim
    · rfl

@[simp] theorem pairEmbedding_zero {m : ℕ} (p : OrderedPair m) :
    pairEmbedding p 0 = p.1.1 := rfl

@[simp] theorem pairEmbedding_one {m : ℕ} (p : OrderedPair m) :
    pairEmbedding p 1 = p.1.2 := rfl

/-- Joint 2-party shared-multiplication oracle round for `p : OrderedPair m`. -/
@[reducible] def pairRound {m : ℕ} (p : OrderedPair m) : Round m (sharedMulSpec 2) :=
  .oracle () (pairEmbedding p)

/-- A party `i` that is neither `p.1.1` nor `p.1.2` receives a subsingleton record in
`pairRound p`. -/
theorem subsingleton_received_pairRound {m : ℕ} (p : OrderedPair m) {i : Fin m}
    (h1 : i ≠ p.1.1) (h2 : i ≠ p.1.2) : Subsingleton ((pairRound p).Received i) := by
  refine ⟨fun r₁ r₂ => Round.received_oracle_ext fun s hs => ?_⟩
  fin_cases s
  · exact (h1 hs.symm).elim
  · exact (h2 hs.symm).elim

/-- Schedule of 2-party shared-multiplication oracle rounds for a list of ordered pairs `L`. -/
@[reducible] def pairsSchedule {m : ℕ} (L : List (OrderedPair m)) :
    Schedule m (sharedMulSpec 2) :=
  L.map pairRound

/-- Canonical list of all ordered pairs `i < j` in `Fin m` in lexicographic order. -/
def orderedPairs (m : ℕ) : List (OrderedPair m) :=
  (List.finRange m).flatMap fun u =>
    (List.finRange m).filterMap fun v =>
      if h : u < v then some ⟨(u, v), h⟩ else none

/-- Schedule for `multiPartyMulProtocol m`: invokes `sharedMulSpec 2` once for each ordered pair
`i < j` in `orderedPairs m` (Goldreich Construction 7.5.8, Step 1, p. 704). -/
@[reducible] def multiPartyMulSchedule (m : ℕ) : Schedule m (sharedMulSpec 2) :=
  pairsSchedule (orderedPairs m)

/-- Extract party `i`'s oracle answer share from `pairRound p` (`0` if `i` is not one of the
two participating parties `p.1.1` or `p.1.2`). -/
def extractPairShare {m : ℕ} (p : OrderedPair m) (i : Fin m)
    (r : (pairRound p).Received i) : Bool :=
  if h0 : p.1.1 = i then
    r 0 h0
  else if h1 : p.1.2 = i then
    r 1 h1
  else
    0

/-- Step-by-step execution over a list of ordered pairs `L`, where each party's local state is
`((a_i, b_i), acc_i) : (Bool × Bool) × Bool`. In each round `p ∈ L`, `p.1.1` and `p.1.2` submit
their input pairs `(a_i, b_i)` to `sharedMulSpec 2` and each party adds its received share
(`extractPairShare p i`) to `acc_i`. -/
def pairsSteps {m : ℕ} :
    (L : List (OrderedPair m)) →
      Steps (fun _ : Fin m => (Bool × Bool) × Bool) (fun _ => Bool) (pairsSchedule L)
  | [] => .done (fun _ st => st.2)
  | p :: L =>
    .oracle (op := ()) (parties := pairEmbedding p)
      (fun _ st => st.1)
      ((pairsSteps L).mapState fun i st =>
        (st.1.1, st.1.2 + extractPairShare p i st.2))

/-- Construction 7.5.8 (p. 704): `m`-party shared multiplication in the 2-ary
`sharedMulSpec 2`-hybrid model, invoking `sharedMulSpec 2` once for each pair `i < j`.
Party `i` initializes its accumulator to $m \cdot a_i b_i$ (`m • ((x i).1 * (x i).2)`), adds its
received share from every pair `{i, j}`, and outputs the resulting sum
$c_i = m a_i b_i + \sum_{j \neq i} c_i^{\{i, j\}}$. -/
def multiPartyMulProtocol (m : ℕ) :
    Protocol m (sharedMulSpec 2) (multiPartyMulSchedule m)
      (fun _ => Bool × Bool) (fun _ => Unit) (fun _ => Bool) where
  sampleCoins _ := pure ()
  steps :=
    (pairsSteps (orderedPairs m)).mapState fun _ st =>
      (st.1, m • (st.1.1 * st.1.2))

namespace MultiPartyMul

/-- Sum of party `i`'s received oracle shares across `L : List (OrderedPair m)`. -/
def sumReceivedShares {m : ℕ} :
    (L : List (OrderedPair m)) → (i : Fin m) → (pairsSchedule L).Received i → Bool
  | [], _, _ => 0
  | p :: L, i, r => extractPairShare p i r.1 + sumReceivedShares L i r.2

@[simp] theorem outputAt_pairsSteps {m : ℕ} (L : List (OrderedPair m))
    (i : Fin m) (st_i : (Bool × Bool) × Bool) (recv_i : (pairsSchedule L).Received i) :
    (pairsSteps L).outputAt i st_i recv_i = st_i.2 + sumReceivedShares L i recv_i := by
  induction L generalizing st_i with
  | nil =>
    cases recv_i
    simp [pairsSteps, Steps.outputAt, sumReceivedShares]
  | cons p L ih =>
    rcases recv_i with ⟨r_head, r_tail⟩
    simp [pairsSteps, Steps.outputAt, ih, sumReceivedShares, add_assoc]

theorem outputOfView_multiPartyMulProtocol {m : ℕ} (i : Fin m)
    (v : PartyView (fun _ => Bool × Bool) (fun _ => Unit) (multiPartyMulSchedule m) i) :
    (multiPartyMulProtocol m).outputOfView i v =
      m • (v.input.1 * v.input.2) + sumReceivedShares (orderedPairs m) i v.received := by
  simp [Protocol.outputOfView, multiPartyMulProtocol]

/-- Construct party `i`'s received oracle record in `pairRound p` from party `i`'s row of
pairwise shares `row_i : Fin m → Bool`. -/
def receivedPairOfRow {m : ℕ} (p : OrderedPair m) (i : Fin m) (row_i : Fin m → Bool) :
    (pairRound p).Received i :=
  fun s _ => Fin.cases (row_i p.1.2) (fun _ => row_i p.1.1) s

/-- Construct party `i`'s received transcript along `pairsSchedule L` from party `i`'s row of
pairwise shares `row_i : Fin m → Bool`. -/
def receivedScheduleOfRow {m : ℕ} (i : Fin m) (row_i : Fin m → Bool) :
    (L : List (OrderedPair m)) → (pairsSchedule L).Received i
  | [] => ()
  | p :: L => (receivedPairOfRow p i row_i, receivedScheduleOfRow i row_i L)

theorem extractPairShare_receivedPairOfRow {m : ℕ} (p : OrderedPair m) (i : Fin m)
    (row_i : Fin m → Bool) :
    extractPairShare p i (receivedPairOfRow p i row_i) =
      (if p.1.1 = i then row_i p.1.2 else 0) +
        (if p.1.2 = i then row_i p.1.1 else 0) := by
  dsimp [extractPairShare, receivedPairOfRow]
  by_cases h0 : p.1.1 = i
  · have h1 : p.1.2 ≠ i := fun h => ne_of_lt p.2 (h0.trans h.symm)
    simp [h0, h1]
  · by_cases h1 : p.1.2 = i
    · simp only [h0, h1, ↓reduceIte, zero_add]
      rfl
    · simp [h0, h1]

private theorem sum_map_flatMap {α β M : Type} [AddCommMonoid M] (l : List α)
    (f : α → List β) (g : β → M) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

private theorem sum_map_filterMap {α β M : Type} [AddCommMonoid M] (l : List α)
    (f : α → Option β) (g : β → M) :
    ((l.filterMap f).map g).sum =
      (l.map fun a => match f a with | some b => g b | none => 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hf : f a <;> simp [List.filterMap, hf, ih]

private theorem sum_map_orderedPairs {m : ℕ} {M : Type} [AddCommMonoid M]
    (g : OrderedPair m → M) :
    ((orderedPairs m).map g).sum =
      ∑ u : Fin m, ∑ v : Fin m, if h : u < v then g ⟨(u, v), h⟩ else 0 := by
  rw [orderedPairs, sum_map_flatMap, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun u _ => ?_
  rw [sum_map_filterMap, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun v _ => ?_
  split_ifs <;> rfl

theorem sumReceivedShares_receivedScheduleOfRow {m : ℕ} (i : Fin m)
    (row_i : Fin m → Bool) (hdiag : row_i i = 0) :
    sumReceivedShares (orderedPairs m) i (receivedScheduleOfRow i row_i (orderedPairs m)) =
      ∑ j : Fin m, row_i j := by
  have hL : ∀ L : List (OrderedPair m),
      sumReceivedShares L i (receivedScheduleOfRow i row_i L) =
        (L.map fun p => extractPairShare p i (receivedPairOfRow p i row_i)).sum := by
    intro L
    induction L with
    | nil => rfl
    | cons p L ih => simp [sumReceivedShares, receivedScheduleOfRow, ih]
  rw [hL, sum_map_orderedPairs]
  simp only [extractPairShare_receivedPairOfRow, dite_eq_ite]
  have hsplit : ∀ u v : Fin m,
      (if u < v then
        (if u = i then row_i v else 0) + (if v = i then row_i u else 0)
      else 0) =
        (if u = i then (if i < v then row_i v else 0) else 0) +
          (if v = i then (if u < i then row_i u else 0) else 0) := by
    intro u v
    by_cases hu : u = i
    · subst hu
      by_cases hv : u = v
      · subst hv; simp
      · have hvu : v ≠ u := Ne.symm hv
        by_cases huv : u < v <;> simp [hvu, huv]
    · by_cases hv : v = i
      · subst hv
        by_cases huv : u < v <;> simp [hu, huv]
      · by_cases huv : u < v <;> simp [hu, hv, huv]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun u v => if u = i then (if i < v then row_i v else 0) else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hnot : ¬ j < i := not_lt_of_gt hij
    simp [hij, hnot]
  · simp only [lt_irrefl, ↓reduceIte, add_zero]
    exact hdiag.symm
  · have hnot : ¬ i < j := not_lt_of_gt hji
    simp [hji, hnot]

/-- Target sum $(a_i + a_j) \cdot (b_i + b_j)$ for the pair of parties `(i, j)`. -/
def pairTarget {m : ℕ} (x : Fin m → Bool × Bool) (i j : Fin m) : Bool :=
  ((x i).1 + (x j).1) * ((x i).2 + (x j).2)

theorem pairTarget_comm {m : ℕ} (x : Fin m → Bool × Bool) (i j : Fin m) :
    pairTarget x i j = pairTarget x j i := by
  simp [pairTarget, add_comm]

@[simp] theorem pairTarget_self {m : ℕ} (x : Fin m → Bool × Bool) (i : Fin m) :
    pairTarget x i i = 0 := by
  simp [pairTarget, BooleanRing.add_self]

/-- Matrix of pairwise shares $C(r, x)_{i, j}$ generated by coin vector
`r : OrderedPair m → Bool` on input `x`:
- for `i < j`, party `i` receives `r ⟨(i, j), h⟩`;
- for `j < i`, party `i` receives `r ⟨(j, i), h⟩ + pairTarget x i j`;
- for `i = j`, `0`. -/
def matrixOfCoins {m : ℕ} (x : Fin m → Bool × Bool) (r : OrderedPair m → Bool)
    (i j : Fin m) : Bool :=
  if hlt : i < j then
    r ⟨(i, j), hlt⟩
  else if hgt : j < i then
    r ⟨(j, i), hgt⟩ + pairTarget x i j
  else
    0

@[simp] theorem matrixOfCoins_self {m : ℕ} (x : Fin m → Bool × Bool)
    (r : OrderedPair m → Bool) (i : Fin m) :
    matrixOfCoins x r i i = 0 := by
  simp [matrixOfCoins]

/-- Symmetric zero-diagonal matrix associated with `d : OrderedPair m → Bool`. -/
def symMatrix {m : ℕ} (d : OrderedPair m → Bool) (i j : Fin m) : Bool :=
  if hlt : i < j then
    d ⟨(i, j), hlt⟩
  else if hgt : j < i then
    d ⟨(j, i), hgt⟩
  else
    0

theorem matrixOfCoins_add {m : ℕ} (x : Fin m → Bool × Bool)
    (r d : OrderedPair m → Bool) (i j : Fin m) :
    matrixOfCoins x (r + d) i j = matrixOfCoins x r i j + symMatrix d i j := by
  dsimp [matrixOfCoins, symMatrix]
  split_ifs with hlt hgt
  · rfl
  · exact add_right_comm (r ⟨(j, i), hgt⟩) (d ⟨(j, i), hgt⟩) (pairTarget x i j)
  · simp

/-- Output of party `i` in `multiPartyMulProtocol m` when the pairwise coin vector is `r`. -/
def realOut {m : ℕ} (x : Fin m → Bool × Bool) (r : OrderedPair m → Bool) (i : Fin m) : Bool :=
  m • ((x i).1 * (x i).2) + ∑ j : Fin m, matrixOfCoins x r i j

theorem realOut_add {m : ℕ} (x : Fin m → Bool × Bool)
    (r d : OrderedPair m → Bool) (i : Fin m) :
    realOut x (r + d) i = realOut x r i + ∑ j : Fin m, symMatrix d i j := by
  simp [realOut, matrixOfCoins_add, Finset.sum_add_distrib, add_assoc]

private def upperMatrix {m : ℕ} (d : OrderedPair m → Bool) (i j : Fin m) : Bool :=
  if hlt : i < j then d ⟨(i, j), hlt⟩ else 0

private theorem symMatrix_eq_upper_add_upper {m : ℕ} (d : OrderedPair m → Bool) (i j : Fin m) :
    symMatrix d i j = upperMatrix d i j + upperMatrix d j i := by
  dsimp [symMatrix, upperMatrix]
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hnot : ¬ j < i := not_lt_of_gt hij
    simp [hij, hnot]
  · simp
  · have hnot : ¬ i < j := not_lt_of_gt hji
    simp [hji, hnot]

theorem sum_symMatrix {m : ℕ} (d : OrderedPair m → Bool) :
    (∑ i : Fin m, ∑ j : Fin m, symMatrix d i j) = 0 := by
  simp_rw [symMatrix_eq_upper_add_upper, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun i j => upperMatrix d j i)]
  exact BooleanRing.add_self _

/-- Asymmetric bilinear decomposition of `pairTarget`:
$D(x)_{i, j} = a_i b_i + a_i b_j$ satisfies $D(x)_{i, j} + D(x)_{j, i} = (a_i + a_j)(b_i + b_j)$. -/
private def asymTerm {m : ℕ} (x : Fin m → Bool × Bool) (i j : Fin m) : Bool :=
  (x i).1 * (x i).2 + (x i).1 * (x j).2

private theorem asymTerm_add_comm {m : ℕ} (x : Fin m → Bool × Bool) (i j : Fin m) :
    asymTerm x i j + asymTerm x j i = pairTarget x i j := by
  dsimp [asymTerm, pairTarget]
  ring

private theorem matrixOfCoins_eq_symMatrix_add_asymTerm {m : ℕ}
    (x : Fin m → Bool × Bool) (r : OrderedPair m → Bool) (i j : Fin m) :
    matrixOfCoins x r i j =
      symMatrix (r + fun p => asymTerm x p.1.1 p.1.2) i j + asymTerm x i j := by
  dsimp [matrixOfCoins, symMatrix]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [hij, add_assoc, BooleanRing.add_self]
  · simp [asymTerm, BooleanRing.add_self]
  · have hnot : ¬ i < j := not_lt_of_gt hji
    simp only [hnot, ↓reduceDIte, hji]
    change r ⟨(j, i), hji⟩ + pairTarget x i j =
      (r ⟨(j, i), hji⟩ + asymTerm x j i) + asymTerm x i j
    rw [add_assoc, ← asymTerm_add_comm x i j, add_comm (asymTerm x i j)]

/-- Equations (7.46)–(7.47) (Goldreich Section 7.5.2.2, p. 703): for every coin vector `r`, the
sum of all `m` parties' outputs in Construction 7.5.8 equals $(\sum_i a_i) \cdot (\sum_i b_i)$. -/
theorem sum_realOut {m : ℕ} (x : Fin m → Bool × Bool) (r : OrderedPair m → Bool) :
    (∑ i : Fin m, realOut x r i) = (∑ i : Fin m, (x i).1) * (∑ i : Fin m, (x i).2) := by
  have hrow : ∀ i : Fin m,
      realOut x r i =
        (x i).1 * (∑ j : Fin m, (x j).2) +
          ∑ j : Fin m, symMatrix (r + fun p => asymTerm x p.1.1 p.1.2) i j := by
    intro i
    simp only [realOut, matrixOfCoins_eq_symMatrix_add_asymTerm, Finset.sum_add_distrib]
    have hasym :
        (∑ j : Fin m, asymTerm x i j) =
          m • ((x i).1 * (x i).2) + (x i).1 * (∑ j : Fin m, (x j).2) := by
      simp [asymTerm, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hasym]
    have hcancel : ∀ a b c : Bool, a + (b + (a + c)) = c + b := by
      intro a b c
      rw [← add_assoc b a c, add_comm b a, add_assoc a b c, ← add_assoc a a (b + c),
        BooleanRing.add_self, zero_add, add_comm]
    exact hcancel _ _ _
  simp_rw [hrow, Finset.sum_add_distrib, sum_symMatrix, add_zero, ← Finset.sum_mul]

/-- Complete `PartyView` of party `i` in `multiPartyMulProtocol m` constructed from its input
`xi : Bool × Bool` and its row of pairwise shares `row_i : Fin m → Bool`. -/
def viewOfRow {m : ℕ} (i : Fin m) (xi : Bool × Bool) (row_i : Fin m → Bool) :
    PartyView (fun _ => Bool × Bool) (fun _ => Unit) (multiPartyMulSchedule m) i where
  input := xi
  coins := ()
  received := receivedScheduleOfRow i row_i (orderedPairs m)

/-- 2-party oracle answer tuple for pair `p` on input `x` and coin `b : Bool`. -/
def pairAnswer {m : ℕ} (x : Fin m → Bool × Bool) (p : OrderedPair m) (b : Bool) :
    Fin 2 → Bool :=
  completeShares 2 (pairTarget x p.1.1 p.1.2) (fun _ => b)

theorem deliverOracle_pairAnswer_eq_receivedPairOfRow {m : ℕ}
    (x : Fin m → Bool × Bool) (r : OrderedPair m → Bool) (p : OrderedPair m) (i : Fin m) :
    Round.deliverOracle (spec := sharedMulSpec 2) (op := ())
        (pairEmbedding p) (pairAnswer x p (r p)) i =
      receivedPairOfRow p i (matrixOfCoins x r i) := by
  refine Round.received_oracle_ext fun s hs => ?_
  fin_cases s
  · change completeShares 2 (pairTarget x p.1.1 p.1.2) (fun _ => r p)
        (Fin.castLE (Nat.sub_le 2 1) 0) = matrixOfCoins x r i p.1.2
    rw [completeShares_castLE]
    have hi : p.1.1 = i := hs
    subst hi
    simp [matrixOfCoins, p.2]
  · change completeShares 2 (pairTarget x p.1.1 p.1.2) (fun _ => r p) (⊤ : Fin 2) =
        matrixOfCoins x r i p.1.1
    rw [completeShares_top]
    have hi : p.1.2 = i := hs
    subst hi
    have hnot : ¬ p.1.2 < p.1.1 := not_lt_of_gt p.2
    simp [matrixOfCoins, hnot, p.2, BooleanRing.sub_eq_add, pairTarget_comm, add_comm]

theorem nodup_orderedPairs (m : ℕ) : (orderedPairs m).Nodup := by
  rw [orderedPairs, List.nodup_flatMap]
  refine ⟨fun u _ => ?_, ?_⟩
  · refine (List.nodup_finRange m).filterMap ?_
    intro v₁ v₂ b h₁ h₂
    simp only [Option.mem_def] at h₁ h₂
    split_ifs at h₁ h₂
    cases h₁
    cases h₂
    rfl
  · refine (List.nodup_finRange m).pairwise_of_forall_ne fun u₁ _ u₂ _ hne => ?_
    dsimp [Function.onFun]
    rw [List.disjoint_left]
    intro p hp₁ hp₂
    simp only [List.mem_filterMap, List.mem_finRange, true_and] at hp₁ hp₂
    obtain ⟨v₁, h₁⟩ := hp₁
    obtain ⟨v₂, h₂⟩ := hp₂
    split_ifs at h₁ h₂
    cases h₁
    cases h₂
    exact hne rfl

/-- Received transcript along `pairsSchedule L` generated by `r : OrderedPair m → Bool`. -/
def deliverCoins {m : ℕ} (x : Fin m → Bool × Bool) (r : OrderedPair m → Bool) :
    (L : List (OrderedPair m)) → (i : Fin m) → (pairsSchedule L).Received i
  | [], _ => ()
  | p :: L, i =>
    (Round.deliverOracle (spec := sharedMulSpec 2) (op := ())
      (pairEmbedding p) (pairAnswer x p (r p)) i,
     deliverCoins x r L i)

theorem deliverCoins_eq_receivedScheduleOfRow {m : ℕ} (x : Fin m → Bool × Bool)
    (r : OrderedPair m → Bool) (L : List (OrderedPair m)) (i : Fin m) :
    deliverCoins x r L i = receivedScheduleOfRow i (matrixOfCoins x r i) L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp [deliverCoins, receivedScheduleOfRow,
      deliverOracle_pairAnswer_eq_receivedPairOfRow, ih]

theorem deliverCoins_update_of_not_mem {m : ℕ} (x : Fin m → Bool × Bool)
    (r : OrderedPair m → Bool) {p₀ : OrderedPair m} {L : List (OrderedPair m)}
    (hp₀ : p₀ ∉ L) (b : Bool) :
    deliverCoins x (Function.update r p₀ b) L = deliverCoins x r L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [List.mem_cons, not_or] at hp₀
    ext i
    simp [deliverCoins, Function.update_of_ne (Ne.symm hp₀.1),
      congrFun (ih hp₀.2) i]

private theorem eval_sharedMulWorld2_pair {m : ℕ} (x : Fin m → Bool × Bool) (p : OrderedPair m) :
    ProbComp.eval (sharedMulWorld 2 () (fun s => x (pairEmbedding p s))) =
      (PMF.uniformOfFintype Bool).map (pairAnswer x p) := by
  simp only [sharedMulWorld, sharedMulFunctionality, sampleAdditiveShares,
    ProbComp.eval_map, ProbComp.eval_uniform]
  rw [uniformOfFintype_fin1_bool, PMF.map_comp]
  have htarget :
      ((∑ i : Fin 2, (x (pairEmbedding p i)).1) * (∑ i : Fin 2, (x (pairEmbedding p i)).2)) =
        pairTarget x p.1.1 p.1.2 := by
    simp [Fin.sum_univ_two, pairTarget]
  rw [htarget]
  rfl

theorem evalWith_pairsSteps {m : ℕ} {L : List (OrderedPair m)} (hL : L.Nodup)
    (st : Fin m → (Bool × Bool) × Bool) :
    (pairsSteps L).evalWith (sharedMulWorld 2) st =
      (PMF.uniformOfFintype (OrderedPair m → Bool)).map fun r =>
        deliverCoins (fun j => (st j).1) r L := by
  induction L generalizing st with
  | nil =>
    simp only [pairsSteps, Steps.evalWith_done, deliverCoins]
    exact (PMF.map_const (PMF.uniformOfFintype (OrderedPair m → Bool)) (fun _ => ())).symm
  | cons p L ih =>
    rw [List.nodup_cons] at hL
    simp only [pairsSteps, Steps.evalWith_oracle, Steps.evalWith_mapState,
      eval_sharedMulWorld2_pair (fun j => (st j).1) p, ih hL.2, PMF.bind_map, PMF.map_comp]
    have hcongr :
        ((PMF.uniformOfFintype Bool).bind fun b =>
          (PMF.uniformOfFintype (OrderedPair m → Bool)).map fun r =>
            (fun r' : OrderedPair m → Bool => deliverCoins (fun j => (st j).1) r' (p :: L))
              (Function.update r p b)) =
        ((PMF.uniformOfFintype Bool).bind fun b =>
          ((PMF.uniformOfFintype (OrderedPair m → Bool)).map fun r =>
            Function.update r p b)).map fun r' =>
            deliverCoins (fun j => (st j).1) r' (p :: L) := by
      simp [PMF.map_bind, PMF.map_comp, Function.comp_def]
    calc
      ((PMF.uniformOfFintype Bool).bind fun b =>
          (PMF.uniformOfFintype (OrderedPair m → Bool)).map fun r i =>
            (Round.deliverOracle (spec := sharedMulSpec 2) (op := ())
              (pairEmbedding p) (pairAnswer (fun j => (st j).1) p b) i,
             deliverCoins (fun j => (st j).1) r L i))
        = ((PMF.uniformOfFintype Bool).bind fun b =>
            (PMF.uniformOfFintype (OrderedPair m → Bool)).map fun r =>
              (fun r' : OrderedPair m → Bool => deliverCoins (fun j => (st j).1) r' (p :: L))
                (Function.update r p b)) := by
          refine congrArg (PMF.bind (PMF.uniformOfFintype Bool)) (funext fun b => ?_)
          refine congrArg (PMF.map · (PMF.uniformOfFintype (OrderedPair m → Bool)))
            (funext fun r => ?_)
          funext i
          refine Prod.ext ?_ ?_
          · dsimp [deliverCoins]
            rw [Function.update_self]
          · exact congrFun (deliverCoins_update_of_not_mem _ r hL.1 b).symm i
      _ = _ := by
          rw [hcongr, PMF.uniformOfFintype_update p]

theorem evalWith_multiPartyMulProtocol (m : ℕ) (x : Fin m → Bool × Bool) :
    (multiPartyMulProtocol m).evalWith (sharedMulWorld 2) x =
      (PMF.uniformOfFintype (OrderedPair m → Bool)).map fun r =>
        (fun i => viewOfRow i (x i) (matrixOfCoins x r i), realOut x r) := by
  rw [Protocol.evalWith_eq]
  change (ProbComp.eval (OracleComp.pi (fun _ : Fin m => (pure () : ProbComp Unit)))).bind _ = _
  rw [ProbComp.eval_pi_pure, PMF.pure_bind]
  simp only [multiPartyMulProtocol, Steps.evalWith_mapState,
    evalWith_pairsSteps (nodup_orderedPairs m), PMF.map_comp]
  refine congrArg (PMF.map · (PMF.uniformOfFintype (OrderedPair m → Bool))) (funext fun r => ?_)
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · refine PartyView.ext rfl rfl ?_
    exact deliverCoins_eq_receivedScheduleOfRow x r (orderedPairs m) i
  · change (multiPartyMulProtocol m).outputOfView i
        ⟨x i, (), deliverCoins x r (orderedPairs m) i⟩ = realOut x r i
    rw [outputOfView_multiPartyMulProtocol, deliverCoins_eq_receivedScheduleOfRow,
      sumReceivedShares_receivedScheduleOfRow i (matrixOfCoins x r i) (matrixOfCoins_self x r i)]
    rfl

/-- Coin adjustment supported on pairs incident to the pivot party `ℓ : Fin m`. -/
def delta {m : ℕ} (ℓ : Fin m) (w : Fin m → Bool) (p : OrderedPair m) : Bool :=
  if p.1.1 = ℓ then w p.1.2
  else if p.1.2 = ℓ then w p.1.1
  else 0

/-- Restriction-based presentation of `delta ℓ` depending only on `Finset.univ.erase ℓ`. -/
def deltaErase {m : ℕ} (ℓ : Fin m) (u : (i : Finset.univ.erase ℓ) → Bool)
    (p : OrderedPair m) : Bool :=
  if h1 : p.1.1 = ℓ then
    u ⟨p.1.2, Finset.mem_erase.mpr ⟨ne_of_gt (h1 ▸ p.2), Finset.mem_univ _⟩⟩
  else if h2 : p.1.2 = ℓ then
    u ⟨p.1.1, Finset.mem_erase.mpr ⟨ne_of_lt (h2 ▸ p.2), Finset.mem_univ _⟩⟩
  else 0

theorem delta_eq_deltaErase_restrict {m : ℕ} (ℓ : Fin m) (w : Fin m → Bool) :
    delta ℓ w = deltaErase ℓ ((Finset.univ.erase ℓ).restrict w) := by
  ext p
  dsimp [delta, deltaErase]

theorem symMatrix_delta_of_ne {m : ℕ} (ℓ : Fin m) (w : Fin m → Bool)
    {i : Fin m} (hi : i ≠ ℓ) (j : Fin m) :
    symMatrix (delta ℓ w) i j = if j = ℓ then w i else 0 := by
  dsimp [symMatrix, delta]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [hij, hi]
  · simp [hi]
  · have hnot : ¬ i < j := not_lt_of_gt hji
    simp only [hnot, ↓reduceDIte, hji]
    by_cases hj : j = ℓ <;> simp [hi, hj]

theorem realOut_add_delta_of_ne {m : ℕ} (ℓ : Fin m) (x : Fin m → Bool × Bool)
    (r : OrderedPair m → Bool) (w : Fin m → Bool) {i : Fin m} (hi : i ≠ ℓ) :
    realOut x (r + delta ℓ w) i = realOut x r i + w i := by
  rw [realOut_add]
  simp [symMatrix_delta_of_ne ℓ w hi]

/-- Adjust coin vector `r` at pairs incident to `ℓ` so the protocol outputs equal `y`. -/
def tildeR {m : ℕ} (ℓ : Fin m) (x : Fin m → Bool × Bool) (y : Fin m → Bool)
    (r : OrderedPair m → Bool) : OrderedPair m → Bool :=
  r + delta ℓ (y + realOut x r)

theorem realOut_tildeR_of_ne {m : ℕ} (ℓ : Fin m) (x : Fin m → Bool × Bool)
    (y : Fin m → Bool) (r : OrderedPair m → Bool) {i : Fin m} (hi : i ≠ ℓ) :
    realOut x (tildeR ℓ x y r) i = y i := by
  dsimp [tildeR]
  rw [realOut_add_delta_of_ne ℓ x r (y + realOut x r) hi, Pi.add_apply,
    add_comm (y i), ← add_assoc, BooleanRing.add_self, zero_add]

theorem realOut_tildeR {m : ℕ} (ℓ : Fin m) (x : Fin m → Bool × Bool)
    (y : Fin m → Bool) (r : OrderedPair m → Bool)
    (hy : ∑ i : Fin m, y i = (∑ i : Fin m, (x i).1) * (∑ i : Fin m, (x i).2)) :
    realOut x (tildeR ℓ x y r) = y := by
  ext i
  by_cases hi : i = ℓ
  · subst hi
    have hsum : ∑ j : Fin m, realOut x (tildeR i x y r) j = ∑ j : Fin m, y j := by
      rw [sum_realOut, hy]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ y (Finset.mem_univ i)] at hsum
    have herase :
        ∑ j ∈ Finset.univ.erase i, realOut x (tildeR i x y r) j =
          ∑ j ∈ Finset.univ.erase i, y j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      exact realOut_tildeR_of_ne i x y r (Finset.mem_erase.mp hj).1
    rw [herase] at hsum
    exact add_right_cancel hsum
  · exact realOut_tildeR_of_ne ℓ x y r hi

/-- Choose a pivot party outside `I` when `I ≠ Finset.univ`, or `⊤` when `I = Finset.univ`. -/
def pivotParty {m : ℕ} [NeZero m] (I : Finset (Fin m)) : Fin m :=
  if h : (Finset.univ \ I).Nonempty then
    (Finset.univ \ I).max' h
  else
    (⊤ : Fin m)

theorem pivotParty_not_mem {m : ℕ} [NeZero m] {I : Finset (Fin m)} (hI : I ≠ Finset.univ) :
    pivotParty I ∉ I := by
  have hne : (Finset.univ \ I).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.sdiff_eq_empty_iff_subset]
    intro hsub
    exact hI (Finset.Subset.antisymm (Finset.subset_univ I) hsub)
  dsimp [pivotParty]
  simp only [hne, ↓reduceDIte]
  exact (Finset.mem_sdiff.mp ((Finset.univ \ I).max'_mem hne)).2

/-- Extend coalition inputs `xI : I → Bool × Bool` by `(0, 0)` outside `I`. -/
def extendIn {m : ℕ} (I : Finset (Fin m)) (xI : (i : I) → Bool × Bool) (j : Fin m) :
    Bool × Bool :=
  if hj : j ∈ I then xI ⟨j, hj⟩ else (0, 0)

/-- Extend coalition outputs `yI : I → Bool` by `0` outside `I`. -/
def extendOut {m : ℕ} (I : Finset (Fin m)) (yI : (i : I) → Bool) (j : Fin m) : Bool :=
  if hj : j ∈ I then yI ⟨j, hj⟩ else 0

@[simp] theorem extendIn_of_mem {m : ℕ} (I : Finset (Fin m)) (xI : (i : I) → Bool × Bool)
    {j : Fin m} (hj : j ∈ I) :
    extendIn I xI j = xI ⟨j, hj⟩ := by
  simp [extendIn, hj]

@[simp] theorem extendOut_of_mem {m : ℕ} (I : Finset (Fin m)) (yI : (i : I) → Bool)
    {j : Fin m} (hj : j ∈ I) :
    extendOut I yI j = yI ⟨j, hj⟩ := by
  simp [extendOut, hj]

@[simp] theorem extendIn_univ {m : ℕ} (x : Fin m → Bool × Bool) :
    extendIn Finset.univ (Finset.univ.restrict x) = x := by
  ext j <;> simp [extendIn]

@[simp] theorem extendOut_univ {m : ℕ} (y : Fin m → Bool) :
    extendOut Finset.univ (Finset.univ.restrict y) = y := by
  ext j; simp [extendOut]

/-- Coin shift aligning `matrixOfCoins x (r + sigmaShift I x) i` with
`matrixOfCoins (extendIn I (I.restrict x)) r i` for all `i ∈ I`. -/
def sigmaShift {m : ℕ} (I : Finset (Fin m)) (x : Fin m → Bool × Bool)
    (p : OrderedPair m) : Bool :=
  if p.1.2 ∈ I then
    pairTarget x p.1.2 p.1.1 + pairTarget (extendIn I (I.restrict x)) p.1.2 p.1.1
  else
    0

@[simp] theorem sigmaShift_univ {m : ℕ} (x : Fin m → Bool × Bool) :
    sigmaShift Finset.univ x = 0 := by
  ext p
  simp [sigmaShift, BooleanRing.add_self]

theorem matrixOfCoins_add_sigmaShift {m : ℕ} (I : Finset (Fin m))
    (x : Fin m → Bool × Bool) (r : OrderedPair m → Bool)
    {i : Fin m} (hi : i ∈ I) (j : Fin m) :
    matrixOfCoins x (r + sigmaShift I x) i j =
      matrixOfCoins (extendIn I (I.restrict x)) r i j := by
  dsimp [matrixOfCoins, sigmaShift]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp only [hij, ↓reduceDIte]
    by_cases hj : j ∈ I
    · simp [hj, pairTarget, hi, BooleanRing.add_self]
    · simp [hj]
  · simp
  · have hnot : ¬ i < j := not_lt_of_gt hji
    simp only [hnot, ↓reduceDIte, hji, hi, ↓reduceIte]
    have hcancel : ∀ a b c : Bool, a + (b + c) + b = a + c := by
      intro a b c
      rw [add_assoc a (b + c) b, add_comm (b + c) b, ← add_assoc b b c,
        BooleanRing.add_self, zero_add]
    exact hcancel _ _ _

theorem realOut_add_sigmaShift {m : ℕ} (I : Finset (Fin m))
    (x : Fin m → Bool × Bool) (r : OrderedPair m → Bool)
    {i : Fin m} (hi : i ∈ I) :
    realOut x (r + sigmaShift I x) i =
      realOut (extendIn I (I.restrict x)) r i := by
  simp [realOut, hi, matrixOfCoins_add_sigmaShift I x r hi]

theorem matrixOfCoins_tildeR_add_sigmaShift {m : ℕ} [NeZero m]
    (I : Finset (Fin m)) (x : Fin m → Bool × Bool) (y : Fin m → Bool)
    (r : OrderedPair m → Bool) {i : Fin m} (hi : i ∈ I) :
    matrixOfCoins x (tildeR (pivotParty I) x y (r + sigmaShift I x)) i =
      matrixOfCoins (extendIn I (I.restrict x))
        (tildeR (pivotParty I) (extendIn I (I.restrict x)) (extendOut I (I.restrict y)) r) i := by
  by_cases hI : I = Finset.univ
  · subst hI
    simp
  · have hne : i ≠ pivotParty I := fun h => pivotParty_not_mem hI (h ▸ hi)
    ext j
    dsimp [tildeR]
    rw [matrixOfCoins_add x (r + sigmaShift I x),
      matrixOfCoins_add (extendIn I (I.restrict x)) r,
      symMatrix_delta_of_ne _ _ hne, symMatrix_delta_of_ne _ _ hne,
      matrixOfCoins_add_sigmaShift I x r hi j,
      Pi.add_apply, Pi.add_apply,
      realOut_add_sigmaShift I x r hi,
      extendOut_of_mem I (I.restrict y) hi]
    rfl

private theorem uniform_bind_tildeR {m : ℕ} [NeZero m] {α : Type} (ℓ : Fin m)
    (x : Fin m → Bool × Bool) (F : (OrderedPair m → Bool) → α) :
    ((ProbComp.eval (sharedMulFunctionality m x)).bind fun y =>
      (PMF.uniformOfFintype (OrderedPair m → Bool)).map fun r₁ =>
        F (tildeR ℓ x y r₁)) =
      (PMF.uniformOfFintype (OrderedPair m → Bool)).map F := by
  dsimp [sharedMulFunctionality]
  rw [ProbComp.eval_sampleAdditiveShares_eq_map_completeSharesErase ℓ, PMF.bind_map]
  dsimp only [Function.comp_def]
  have htilde : ∀ (sub : (i : Finset.univ.erase ℓ) → Bool) (r₁ : OrderedPair m → Bool),
      tildeR ℓ x (ProbComp.completeSharesErase ℓ
          ((∑ i : Fin m, (x i).1) * (∑ i : Fin m, (x i).2)) sub) r₁ =
        r₁ + deltaErase ℓ (sub + (Finset.univ.erase ℓ).restrict (realOut x r₁)) := by
    intro sub r₁
    dsimp [tildeR]
    rw [delta_eq_deltaErase_restrict]
    have hrest :
        (Finset.univ.erase ℓ).restrict
          (ProbComp.completeSharesErase ℓ
            ((∑ i : Fin m, (x i).1) * (∑ i : Fin m, (x i).2)) sub + realOut x r₁) =
          sub + (Finset.univ.erase ℓ).restrict (realOut x r₁) := by
      ext ⟨i, hi⟩
      change ProbComp.completeSharesErase ℓ _ sub i + realOut x r₁ i =
        sub ⟨i, hi⟩ + realOut x r₁ i
      have h1 := congrFun (ProbComp.restrict_erase_completeSharesErase ℓ
        ((∑ i : Fin m, (x i).1) * (∑ i : Fin m, (x i).2)) sub) ⟨i, hi⟩
      exact congrArg (· + realOut x r₁ i) h1
    rw [hrest]
  simp_rw [htilde]
  have hswap1 :
      ((PMF.uniformOfFintype ((i : Finset.univ.erase ℓ) → Bool)).bind fun sub =>
        (PMF.uniformOfFintype (OrderedPair m → Bool)).map fun r₁ =>
          F (r₁ + deltaErase ℓ (sub + (Finset.univ.erase ℓ).restrict (realOut x r₁)))) =
      (PMF.uniformOfFintype (OrderedPair m → Bool)).bind fun r₁ =>
        (PMF.uniformOfFintype ((i : Finset.univ.erase ℓ) → Bool)).map fun sub =>
          F (r₁ + deltaErase ℓ (sub + (Finset.univ.erase ℓ).restrict (realOut x r₁))) := by
    simp only [PMF.map]
    exact PMF.bind_comm _ _ _
  rw [hswap1]
  have hshift1 : ∀ r₁ : OrderedPair m → Bool,
      (PMF.uniformOfFintype ((i : Finset.univ.erase ℓ) → Bool)).map (fun sub =>
        F (r₁ + deltaErase ℓ (sub + (Finset.univ.erase ℓ).restrict (realOut x r₁)))) =
      (PMF.uniformOfFintype ((i : Finset.univ.erase ℓ) → Bool)).map (fun u =>
        F (r₁ + deltaErase ℓ u)) := by
    intro r₁
    conv_rhs =>
      rw [← PMF.uniformOfFintype_map_equiv
        (Equiv.addRight ((Finset.univ.erase ℓ).restrict (realOut x r₁))), PMF.map_comp]
    rfl
  simp_rw [hshift1]
  have hswap2 :
      ((PMF.uniformOfFintype (OrderedPair m → Bool)).bind fun r₁ =>
        (PMF.uniformOfFintype ((i : Finset.univ.erase ℓ) → Bool)).map fun u =>
          F (r₁ + deltaErase ℓ u)) =
      (PMF.uniformOfFintype ((i : Finset.univ.erase ℓ) → Bool)).bind fun u =>
        (PMF.uniformOfFintype (OrderedPair m → Bool)).map fun r₁ =>
          F (r₁ + deltaErase ℓ u) := by
    simp only [PMF.map]
    exact PMF.bind_comm _ _ _
  rw [hswap2]
  have hshift2 : ∀ u : (i : Finset.univ.erase ℓ) → Bool,
      (PMF.uniformOfFintype (OrderedPair m → Bool)).map (fun r₁ =>
        F (r₁ + deltaErase ℓ u)) =
      (PMF.uniformOfFintype (OrderedPair m → Bool)).map F := by
    intro u
    conv_rhs =>
      rw [← PMF.uniformOfFintype_map_equiv (Equiv.addRight (deltaErase ℓ u)), PMF.map_comp]
    rfl
  simp_rw [hshift2, PMF.bind_const]

end MultiPartyMul

open MultiPartyMul

/-- Coalition simulator for `multiPartyMulProtocol m` (Goldreich Proposition 7.5.9, pp. 704–705). -/
noncomputable def multiPartyMulSim (m : ℕ) [NeZero m] (I : Finset (Fin m)) :
    CoalitionSimulator (multiPartyMulSchedule m)
      (fun _ => Bool × Bool) (fun _ => Unit) (fun _ => Bool) I :=
  fun xI yI =>
    (ProbComp.uniform (OrderedPair m → Bool)).map fun r =>
      let x₀ := extendIn I xI
      let y₀ := extendOut I yI
      let rSim := tildeR (pivotParty I) x₀ y₀ r
      fun i => viewOfRow i.1 (xI i) (matrixOfCoins x₀ rSim i.1)

/-- Proposition 7.5.9 (Goldreich Section 7.5.2.2, p. 704): `multiPartyMulProtocol m` privately
reduces `m`-party shared multiplication `sharedMulFunctionality m` to 2-party shared multiplication
`sharedMulWorld 2` with perfect semi-honest security against all static coalitions
`I : Finset (Fin m)`. -/
theorem perfectSemiHonestPrivate_multiPartyMul (m : ℕ) [NeZero m] :
    PerfectSemiHonestPrivate (multiPartyMulProtocol m) (sharedMulWorld 2)
      (sharedMulFunctionality m) (multiPartyMulSim m) := by
  intro I x
  rw [Protocol.realJoint, evalWith_multiPartyMulProtocol, PMF.map_comp]
  dsimp [idealJoint, multiPartyMulSim]
  simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.bind_map]
  let F : (OrderedPair m → Bool) →
      ((i : I) → PartyView (fun _ => Bool × Bool) (fun _ => Unit) (multiPartyMulSchedule m) i.1) ×
        (Fin m → Bool) :=
    fun r' => (fun i : I => viewOfRow i.1 (x i.1) (matrixOfCoins x r' i.1), realOut x r')
  change _ = (PMF.uniformOfFintype (OrderedPair m → Bool)).map F
  rw [← uniform_bind_tildeR (pivotParty I) x F]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun y hy => ?_
  have hsum : ∑ i : Fin m, y i = (∑ i : Fin m, (x i).1) * (∑ i : Fin m, (x i).2) :=
    ProbComp.sum_sampleAdditiveShares _ hy
  conv_rhs =>
    rw [← PMF.uniformOfFintype_map_equiv (Equiv.addRight (sigmaShift I x)), PMF.map_comp]
  refine congrArg (PMF.map · (PMF.uniformOfFintype (OrderedPair m → Bool))) (funext fun r => ?_)
  dsimp [F, Function.comp]
  refine Prod.ext (funext fun i => ?_) ?_
  · dsimp only
    rw [matrixOfCoins_tildeR_add_sigmaShift I x y r i.2]
  · exact (realOut_tildeR (pivotParty I) x y (r + sigmaShift I x) hsum).symm

end Cslib.Crypto.Protocols.MPC
