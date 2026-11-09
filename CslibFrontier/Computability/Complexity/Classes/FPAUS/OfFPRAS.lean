/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.FPAUS.Sampler
public import CslibFrontier.Computability.Probabilistic.PPT
import CslibFrontier.Computability.Complexity.Classes.FPAUS.FPRAS
import CslibFrontier.Computability.Probabilistic.Adaptive
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Retry
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Approximate counting gives almost uniform sampling for self-reducible families

For a one-bit self-reducible witness family (`Cslib.Complexity.SelfReducible`), the
counting-to-sampling sampler `Cslib.Complexity.SelfReducible.sampler` is a strict probabilistic
polynomial-time program whenever its approximate counter is. Together with its output law
(`Cslib.Complexity.SelfReducible.closeTo_sampler_of_isFPRAS`), a fully polynomial randomized
approximation scheme for the witness counts therefore yields a fully polynomial almost uniform
sampler [Jerrum, Valiant and Vazirani][JerrumValiantVazirani1986],
[Sinclair, Lecture 4, Section 4.2.3][Sinclair2025].

## The certificate

The recursive walk down the self-reduction tree
(`Cslib.Complexity.SelfReducible.walk`) is run as a bounded loop of `len x` steps
(`Cslib.Probability.IsPPTOn.iterateWith_spec'`) whose state is the current node, its estimate in
binary, the bits chosen so far, and a running flag. A rejected walk stops and keeps its state.
The loop invariant: the current node is no longer than `x`, at most `i` bits are recorded after
`i` steps, and the estimate is the root estimate or one returned at a node no longer than `x`.
The counter's output length is polynomial in its encoded input, and the counter is only called on
nodes no longer than `x` with parameters `4 ℓ + 3` and `q + ℓ + 4`, where `ℓ = len x`, so every
reachable state has encoded length polynomial in that of the input. The branching coin draws
`coinWidth` fair bits, polynomially many since the estimates are polynomially long, and compares
the draw with thresholds computed by binary arithmetic. The trials form a bounded retry loop
(`Cslib.Probability.IsPPTOn.retry`) with `trials q = 6 (q + 2)` rounds.

## Main results

* `Cslib.Complexity.SelfReducible.isPPTOn_sampler`: the sampler is strict PPT on `(x, q)`, with
  `q` in unary.
* `Cslib.Complexity.SelfReducible.isFPAUS_of_isFPRAS`: **an FPRAS gives an FPAUS**.
* `Cslib.Complexity.SelfReducible.mem_FPAUS_of_mem_FPRAS`: the class form.
* `Cslib.Complexity.SelfReducible.mem_FPAUS_iff_mem_FPRAS`: with
  `Cslib.Complexity.SelfReducible.mem_FPRAS_of_mem_FPAUS`, **sampling and counting are
  equivalent** for one-bit self-reducible families.

## Scope

The self-reduction fixes one bit per step, and the counter is called with relative error
`1 / (4 ℓ + 3)` on every intermediate instance, as in Sinclair's sketch. An FPRAS supplies any
requested accuracy in time polynomial in `1 / ε`, so this costs only a polynomial factor. Sinclair
and Jerrum's reduction from polynomial-error counting [Sinclair and Jerrum][SinclairJerrum1989] is
not formalized.

## References

* [M. R. Jerrum, L. G. Valiant, V. V. Vazirani, *Random generation of combinatorial structures from
  a uniform distribution*][JerrumValiantVazirani1986]
* [A. Sinclair, *CS294 Partition Functions*, Lecture 4, Section 4.2.3][Sinclair2025]
* [A. Sinclair, M. Jerrum, *Approximate counting, uniform generation and rapidly mixing Markov
  chains*][SinclairJerrum1989]
-/

public section

namespace Cslib.Complexity.SelfReducible

open Cslib.Probability Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {W : α → Finset (List Bool)}
  (R : SelfReducible enc W) (A : α → ℕ → ℕ → ProbComp (ℕ × ℕ))

/-! ### The walk as a bounded loop -/

/-- The state of a walk run as a loop: the current node, its estimate, the bits chosen so far in
reverse order, and whether the walk is still running. -/
private abbrev WalkState (α : Type) := α × (ℕ × ℕ) × List Bool × Bool

/-- Advance after the branching coin: on `some c` move to child `c` with estimate `e_c` and record
`c`; on `none` stop. -/
private def advance (s : WalkState α) (e₀ e₁ : ℕ × ℕ) (o : Option Bool) : WalkState α :=
  if o.isSome then (R.child s.1 (o.getD false), cond (o.getD false) e₁ e₀,
    o.getD false :: s.2.2.1, true) else (s.1, s.2.1, s.2.2.1, false)

/-- One level of a walk as a loop step: if running, estimate both children, flip the branching
coin and advance; otherwise stay. -/
private noncomputable def walkStep (p t m extra : ℕ) (s : WalkState α) :
    ProbComp (WalkState α) :=
  if s.2.2.2 then do
    let e₀ ← R.nodeEstimate A p t (R.child s.1 false)
    let e₁ ← R.nodeEstimate A p t (R.child s.1 true)
    R.advance s e₀ e₁ <$> choose m extra s.2.1 e₀ e₁
  else pure s

/-- The result of a finished loop: the recorded bits when the walk ran to a witness. -/
private def walkFinish (W : α → Finset (List Bool)) (s : WalkState α) : Option (List Bool) :=
  if s.2.2.2 && decide ([] ∈ W s.1) then some s.2.2.1.reverse else none

private theorem walkStep_stopped (p t m extra : ℕ) (y : α) (e : ℕ × ℕ) (acc : List Bool) :
    R.walkStep A p t m extra (y, e, acc, false) = pure (y, e, acc, false) := rfl

private theorem iterate_walkStep_stopped (p t m extra n : ℕ) (y : α) (e : ℕ × ℕ)
    (acc : List Bool) :
    OracleComp.iterate n (R.walkStep A p t m extra) (y, e, acc, false) =
      pure (y, e, acc, false) :=
  OracleComp.iterate_eq_pure n _ _ (R.walkStep_stopped A p t m extra y e acc)

/-- **The walk as a loop**: `n` loop steps from a running state at `y` with recorded bits `acc`
give the walk's result, prefixed by the recorded bits. -/
private theorem map_walkFinish_iterate (p t m extra n : ℕ) (y : α) (e : ℕ × ℕ)
    (acc : List Bool) :
    walkFinish W <$> OracleComp.iterate n (R.walkStep A p t m extra) (y, e, acc, true) =
      Option.map (acc.reverse ++ ·) <$> R.walk A p t m extra n y e := by
  induction n generalizing y e acc with
  | zero =>
    by_cases h : [] ∈ W y
    · simp [walk, walkFinish, h, OracleComp.iterate]
    · simp [walk, walkFinish, h, OracleComp.iterate]
  | succ n ih =>
    rw [OracleComp.iterate_succ_bind]
    simp only [walk, walkStep, ↓reduceIte, bind_assoc, map_bind, bind_map_left]
    refine congrArg (_ >>= ·) (funext fun e₀ => congrArg (_ >>= ·) (funext fun e₁ =>
      congrArg (_ >>= ·) (funext fun o => ?_)))
    cases o with
    | none =>
      simp [advance, descend, iterate_walkStep_stopped, walkFinish]
    | some c =>
      simp only [advance, Option.isSome_some, ↓reduceIte, Option.getD_some, descend, ih,
        Functor.map_map]
      refine congrArg (· <$> _) (funext fun r => ?_)
      cases r <;> simp

/-- A trial is the walk loop from the root, followed by `walkFinish`. -/
private theorem trial_eq (x : α) (q : ℕ) (e : ℕ × ℕ) :
    R.trial A x q e = walkFinish W <$> OracleComp.iterate (R.len x)
      (R.walkStep A (counterAccuracy (R.len x)) (precision (R.len x) q) (damping (R.len x))
        (precision (R.len x) q)) (x, e, [], true) := by
  rw [map_walkFinish_iterate, trial]
  simp only [List.reverse_nil, List.nil_append, Option.map_id_fun', id_map]

/-! ### Polynomial-time pieces -/

variable {β : Type} {input : β ↪ List Bool}

open ComputableInPolyTime in
/-- `weight` in binary, from `m` in unary and the estimates in binary. -/
private theorem computableInPolyTime_weight {m : β → ℕ} {e e₀ e₁ : β → ℕ × ℕ}
    (hm : ComputableInPolyTime m input encUnary)
    (he : ComputableInPolyTime e input (encPair encNat encNat))
    (he₀ : ComputableInPolyTime e₀ input (encPair encNat encNat))
    (he₁ : ComputableInPolyTime e₁ input (encPair encNat encNat)) (c : Bool) :
    ComputableInPolyTime (fun b => weight (m b) (e b) (e₀ b) (e₁ b) c) input encNat := by
  have hm₁ : ComputableInPolyTime (fun b => m b - 1) input encNat :=
    binary_sub' (unary_to_binary.comp hm) (const 1)
  cases c
  · exact binary_mul' (binary_mul' (binary_mul' hm₁ he₀.fst') he₁.snd') he.snd'
  · exact binary_mul' (binary_mul' (binary_mul' hm₁ he₁.fst') he₀.snd') he.snd'

open ComputableInPolyTime in
/-- `total` in binary, from `m` in unary and the estimates in binary. -/
private theorem computableInPolyTime_total {m : β → ℕ} {e e₀ e₁ : β → ℕ × ℕ}
    (hm : ComputableInPolyTime m input encUnary)
    (he : ComputableInPolyTime e input (encPair encNat encNat))
    (he₀ : ComputableInPolyTime e₀ input (encPair encNat encNat))
    (he₁ : ComputableInPolyTime e₁ input (encPair encNat encNat)) :
    ComputableInPolyTime (fun b => total (m b) (e b) (e₀ b) (e₁ b)) input encNat :=
  binary_mul' (binary_mul' (binary_mul' (unary_to_binary.comp hm) he.fst') he₀.snd') he₁.snd'

open ComputableInPolyTime in
/-- The threshold `u * 2 ^ k / D` in binary, from `u`, `D` in binary and `k` in unary. -/
private theorem computableInPolyTime_threshold {u D k : β → ℕ}
    (hu : ComputableInPolyTime u input encNat) (hD : ComputableInPolyTime D input encNat)
    (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun b => u b * 2 ^ k b / D b) input encNat :=
  binary_div.comp ((binary_mul' hu (binary_two_pow.comp hk)).prod hD)

open ComputableInPolyTime in
/-- The coin outcome, from the thresholds and the draw in binary. -/
private theorem computableInPolyTime_coinOutcome {g₀ g₁ r : β → ℕ}
    (hg₀ : ComputableInPolyTime g₀ input encNat) (hg₁ : ComputableInPolyTime g₁ input encNat)
    (hr : ComputableInPolyTime r input encNat) :
    ComputableInPolyTime (fun b => coinOutcome (g₀ b) (g₁ b) (r b)) input (encOption encBool) := by
  unfold coinOutcome
  have h₁ := binary_lt' hr hg₁
  have h₂ := binary_lt' hr (binary_add.comp (hg₁.prod hg₀))
  fun_prop

/-- The branching coin is strict PPT when `m` and `extra` are computed in unary and the three
estimates in binary. -/
private theorem isPPTOn_choose {m extra : β → ℕ} {e e₀ e₁ : β → ℕ × ℕ}
    (hm : ComputableInPolyTime m input encUnary)
    (hextra : ComputableInPolyTime extra input encUnary)
    (he : ComputableInPolyTime e input (encPair encNat encNat))
    (he₀ : ComputableInPolyTime e₀ input (encPair encNat encNat))
    (he₁ : ComputableInPolyTime e₁ input (encPair encNat encNat)) :
    IsPPTOn input (encOption encBool) (fun b => choose (m b) (extra b) (e b) (e₀ b) (e₁ b)) := by
  have htotal := computableInPolyTime_total hm he he₀ he₁
  have hwidth : ComputableInPolyTime (fun b => coinWidth (m b) (extra b) (e b) (e₀ b) (e₁ b))
      input encUnary :=
    ComputableInPolyTime.unary_add' (ComputableInPolyTime.binary_size.comp htotal) hextra
  have hg (c : Bool) := computableInPolyTime_threshold
    (computableInPolyTime_weight hm he he₀ he₁ c) htotal hwidth
  have hsample : IsPPTOn input encNat
      (fun b => ProbComp.sampleBinaryNat (coinWidth (m b) (extra b) (e b) (e₀ b) (e₁ b))) :=
    isPPTOn_sampleBinaryNat.preprocess hwidth
  have hcoin := computableInPolyTime_coinOutcome
    ((hg false).comp (ComputableInPolyTime.fst input encNat))
    ((hg true).comp (ComputableInPolyTime.fst input encNat))
    (ComputableInPolyTime.snd input encNat)
  exact hsample.map_with hcoin

/-- The node estimate is strict PPT when the node and the counter parameters are computed in
polynomial time, the parameters in unary. -/
private theorem isPPTOn_nodeEstimate
    (hA : IsPPTOn (encPair enc (encPair encUnary encUnary)) (encPair encNat encNat)
      (Function.uncurry fun x => Function.uncurry (A x)))
    {node : β → α} {p t : β → ℕ} (hnode : ComputableInPolyTime node input enc)
    (hp : ComputableInPolyTime p input encUnary) (ht : ComputableInPolyTime t input encUnary) :
    IsPPTOn input (encPair encNat encNat) (fun b => R.nodeEstimate A (p b) (t b) (node b)) := by
  have hzero : ComputableInPolyTime (fun b => decide (R.len (node b) = 0)) input encBool :=
    ComputableInPolyTime.unary_eq' (R.len_polytime.comp hnode) (ComputableInPolyTime.const 0)
  have hnil : ComputableInPolyTime (fun b => decide ([] ∈ W (node b))) input encBool :=
    R.nil_mem_polytime.comp hnode
  have hbase : IsPPTOn input (encPair encNat encNat)
      (fun b => (pure (if decide ([] ∈ W (node b)) = true then 1 else 0, 1) :
        ProbComp (ℕ × ℕ))) :=
    ComputableInPolyTime.isPPTOn (by fun_prop)
  have hcall : IsPPTOn input (encPair encNat encNat) (fun b => A (node b) (p b) (t b)) :=
    hA.preprocess (prepare := fun b => (node b, p b, t b)) (hnode.prod (hp.prod ht))
  refine (IsPPTOn.cond' hzero hbase hcall).congr fun b => ?_
  simp only [nodeEstimate, decide_eq_true_eq]

/-- The walk state encoding: node, estimate in binary, recorded bits, running flag. -/
private abbrev encState (enc : α ↪ List Bool) : WalkState α ↪ List Bool :=
  encPair enc (encPair (encPair encNat encNat) (encPair encBits encBool))

open ComputableInPolyTime in
/-- `advance` is polynomial-time. -/
private theorem computableInPolyTime_advance {s : β → WalkState α} {e₀ e₁ : β → ℕ × ℕ}
    {o : β → Option Bool} (hs : ComputableInPolyTime s input (encState enc))
    (he₀ : ComputableInPolyTime e₀ input (encPair encNat encNat))
    (he₁ : ComputableInPolyTime e₁ input (encPair encNat encNat))
    (ho : ComputableInPolyTime o input (encOption encBool)) :
    ComputableInPolyTime (fun b => R.advance (s b) (e₀ b) (e₁ b) (o b)) input (encState enc) := by
  have hc : ComputableInPolyTime (fun b => (o b).getD false) input encBool :=
    optionGetDWithInput ho (const false)
  have hchild : ComputableInPolyTime (fun b => R.child (s b).1 ((o b).getD false)) input enc :=
    R.child_polytime.comp (hs.fst'.prod hc)
  have hest : ComputableInPolyTime (fun b => cond ((o b).getD false) (e₁ b) (e₀ b)) input
      (encPair encNat encNat) := by
    simp only [Bool.cond_eq_ite]
    exact ite hc he₁ he₀
  have hacc : ComputableInPolyTime (fun b => (o b).getD false :: (s b).2.2.1) input encBits :=
    bitsCons hc hs.snd'.snd'.fst'
  have hyes := hchild.prod (hest.prod (hacc.prod (const (encOut := encBool) true)))
  have hno := hs.fst'.prod (hs.snd'.fst'.prod (hs.snd'.snd'.fst'.prod
    (const (encOut := encBool) false)))
  exact ite (optionIsSome ho) hyes hno

/-- One loop step is strict PPT on a captured input and the walk state, when the counter
parameters, the damping and the coin precision are computed from the captured input in unary. -/
private theorem isPPTOn_walkStep
    (hA : IsPPTOn (encPair enc (encPair encUnary encUnary)) (encPair encNat encNat)
      (Function.uncurry fun x => Function.uncurry (A x)))
    {p t m extra : β → ℕ} (hp : ComputableInPolyTime p input encUnary)
    (ht : ComputableInPolyTime t input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hextra : ComputableInPolyTime extra input encUnary) :
    IsPPTOn (encPair input (encState enc)) (encState enc)
      (fun r : β × WalkState α => R.walkStep A (p r.1) (t r.1) (m r.1) (extra r.1) r.2) := by
  have hfst := ComputableInPolyTime.fst input (encState enc)
  have hsnd := ComputableInPolyTime.snd input (encState enc)
  have hchild (c : Bool) : ComputableInPolyTime (fun r : β × WalkState α => R.child r.2.1 c)
      (encPair input (encState enc)) enc :=
    R.child_polytime.comp (hsnd.fst'.prod (ComputableInPolyTime.const c))
  have h₀ : IsPPTOn (encPair input (encState enc)) (encPair encNat encNat)
      (fun r : β × WalkState α => R.nodeEstimate A (p r.1) (t r.1) (R.child r.2.1 false)) :=
    R.isPPTOn_nodeEstimate A hA (hchild false) (hp.comp hfst) (ht.comp hfst)
  -- the second estimate, with the first captured
  have hfst₁ := ComputableInPolyTime.fst (encPair input (encState enc)) (encPair encNat encNat)
  have hsnd₁ := ComputableInPolyTime.snd (encPair input (encState enc)) (encPair encNat encNat)
  have h₁ : IsPPTOn (encPair (encPair input (encState enc)) (encPair encNat encNat))
      (encPair encNat encNat) (fun v : (β × WalkState α) × (ℕ × ℕ) =>
        R.nodeEstimate A (p v.1.1) (t v.1.1) (R.child v.1.2.1 true)) :=
    R.isPPTOn_nodeEstimate A hA ((hchild true).comp hfst₁) ((hp.comp hfst).comp hfst₁)
      ((ht.comp hfst).comp hfst₁)
  -- the coin, with both estimates captured
  have hfst₂ := ComputableInPolyTime.fst
    (encPair (encPair input (encState enc)) (encPair encNat encNat)) (encPair encNat encNat)
  have hsnd₂ := ComputableInPolyTime.snd
    (encPair (encPair input (encState enc)) (encPair encNat encNat)) (encPair encNat encNat)
  have hcoin : IsPPTOn
      (encPair (encPair (encPair input (encState enc)) (encPair encNat encNat))
        (encPair encNat encNat)) (encOption encBool)
      (fun u : ((β × WalkState α) × (ℕ × ℕ)) × (ℕ × ℕ) =>
        choose (m u.1.1.1) (extra u.1.1.1) u.1.1.2.2.1 u.1.2 u.2) :=
    isPPTOn_choose ((hm.comp hfst).comp (hfst₁.comp hfst₂))
      ((hextra.comp hfst).comp (hfst₁.comp hfst₂)) (hsnd.snd'.fst'.comp (hfst₁.comp hfst₂))
      (hsnd₁.comp hfst₂) hsnd₂
  have hfst₃ := ComputableInPolyTime.fst
    (encPair (encPair (encPair input (encState enc)) (encPair encNat encNat))
      (encPair encNat encNat)) (encOption encBool)
  have hsnd₃ := ComputableInPolyTime.snd
    (encPair (encPair (encPair input (encState enc)) (encPair encNat encNat))
      (encPair encNat encNat)) (encOption encBool)
  have hadv : ComputableInPolyTime
      (fun w : (((β × WalkState α) × (ℕ × ℕ)) × (ℕ × ℕ)) × Option Bool =>
        R.advance w.1.1.1.2 w.1.1.2 w.1.2 w.2)
      (encPair (encPair (encPair (encPair input (encState enc)) (encPair encNat encNat))
        (encPair encNat encNat)) (encOption encBool)) (encState enc) :=
    R.computableInPolyTime_advance (hsnd.comp (hfst₁.comp (hfst₂.comp hfst₃)))
      (hsnd₁.comp (hfst₂.comp hfst₃)) (hsnd₂.comp hfst₃) hsnd₃
  have h₂ : IsPPTOn
      (encPair (encPair (encPair input (encState enc)) (encPair encNat encNat))
        (encPair encNat encNat)) (encState enc)
      (fun u : ((β × WalkState α) × (ℕ × ℕ)) × (ℕ × ℕ) =>
        R.advance u.1.1.2 u.1.2 u.2 <$> choose (m u.1.1.1) (extra u.1.1.1) u.1.1.2.2.1 u.1.2 u.2) :=
    hcoin.map_with hadv
  have h₁₂ : IsPPTOn (encPair (encPair input (encState enc)) (encPair encNat encNat))
      (encState enc) (fun v : (β × WalkState α) × (ℕ × ℕ) => do
        let e₁ ← R.nodeEstimate A (p v.1.1) (t v.1.1) (R.child v.1.2.1 true)
        R.advance v.1.2 v.2 e₁ <$> choose (m v.1.1) (extra v.1.1) v.1.2.2.1 v.2 e₁) :=
    IsPPTOn.bind_with h₁ h₂
  have hyes : IsPPTOn (encPair input (encState enc)) (encState enc)
      (fun r : β × WalkState α => do
        let e₀ ← R.nodeEstimate A (p r.1) (t r.1) (R.child r.2.1 false)
        let e₁ ← R.nodeEstimate A (p r.1) (t r.1) (R.child r.2.1 true)
        R.advance r.2 e₀ e₁ <$> choose (m r.1) (extra r.1) r.2.2.1 e₀ e₁) :=
    IsPPTOn.bind_with h₀ h₁₂
  have hno : IsPPTOn (encPair input (encState enc)) (encState enc)
      (fun r : β × WalkState α => pure r.2) := hsnd.isPPTOn
  exact (IsPPTOn.cond' hsnd.snd'.snd'.snd' hyes hno).congr fun r => rfl

/-! ### The loop -/

private theorem computableInPolyTime_counterAccuracy {ℓ : β → ℕ}
    (hℓ : ComputableInPolyTime ℓ input encUnary) :
    ComputableInPolyTime (fun b => counterAccuracy (ℓ b)) input encUnary := by
  unfold counterAccuracy
  fun_prop

private theorem computableInPolyTime_precision {ℓ q : β → ℕ}
    (hℓ : ComputableInPolyTime ℓ input encUnary) (hq : ComputableInPolyTime q input encUnary) :
    ComputableInPolyTime (fun b => precision (ℓ b) (q b)) input encUnary := by
  unfold precision
  fun_prop

private theorem computableInPolyTime_damping {ℓ : β → ℕ}
    (hℓ : ComputableInPolyTime ℓ input encUnary) :
    ComputableInPolyTime (fun b => damping (ℓ b)) input encUnary := by
  unfold damping
  fun_prop

private theorem computableInPolyTime_trials {q : β → ℕ}
    (hq : ComputableInPolyTime q input encUnary) :
    ComputableInPolyTime (fun b => trials (q b)) input encUnary := by
  unfold trials
  fun_prop

/-- The possible results of one loop step: a stopped state stays, and a running state advances
after estimating both children. -/
private theorem mem_support_walkStep {p t m extra : ℕ} {s s' : WalkState α}
    (h : s' ∈ (ProbComp.eval (R.walkStep A p t m extra s)).support) :
    (s.2.2.2 = false ∧ s' = s) ∨
      (s.2.2.2 = true ∧ ∃ e₀ ∈ (ProbComp.eval (R.nodeEstimate A p t (R.child s.1 false))).support,
        ∃ e₁ ∈ (ProbComp.eval (R.nodeEstimate A p t (R.child s.1 true))).support,
        ∃ o, s' = R.advance s e₀ e₁ o) := by
  cases hrun : s.2.2.2
  · refine Or.inl ⟨rfl, ?_⟩
    simpa only [walkStep, hrun, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
      PMF.support_pure, Set.mem_singleton_iff] using h
  · refine Or.inr ⟨rfl, ?_⟩
    simp only [walkStep, hrun, ↓reduceIte, ProbComp.eval_bind, PMF.mem_support_bind_iff,
      ProbComp.eval_map, PMF.mem_support_map_iff] at h
    obtain ⟨e₀, he₀, e₁, he₁, o, -, rfl⟩ := h
    exact ⟨e₀, he₀, e₁, he₁, o, rfl⟩

/-- A bound on the encoded estimates returned at nodes no longer than `x`, from a length bound
`c (n + 1) ^ d` for the counter. -/
private def estBound (enc : α ↪ List Bool) (c d : ℕ) (x : α) (p t : ℕ) : ℕ :=
  c * ((encPair enc (encPair encUnary encUnary) (x, p, t)).length + 1) ^ d +
    (encPair encNat encNat (1, 1)).length

private theorem length_estimate_le {c d : ℕ}
    (hcd : ∀ a result,
      result ∈ (ProbComp.eval ((Function.uncurry fun x => Function.uncurry (A x)) a)).support →
        (encPair encNat encNat result).length ≤
          c * ((encPair enc (encPair encUnary encUnary) a).length + 1) ^ d)
    {x y : α} {p t : ℕ} (hy : (enc y).length ≤ (enc x).length) {e : ℕ × ℕ}
    (he : e ∈ (ProbComp.eval (R.nodeEstimate A p t y)).support) :
    (encPair encNat encNat e).length ≤ estBound enc c d x p t := by
  unfold estBound
  unfold nodeEstimate at he
  by_cases h0 : R.len y = 0
  · simp only [h0, ↓reduceIte, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at he
    subst he
    have h1 := length_encNat_mono (show (if [] ∈ W y then 1 else 0) ≤ 1 by split_ifs <;> omega)
    simp only [length_encPair] at h1 ⊢
    omega
  · simp only [h0, ↓reduceIte] at he
    have h := hcd (y, p, t) e he
    have hle : (encPair enc (encPair encUnary encUnary) (y, p, t)).length ≤
        (encPair enc (encPair encUnary encUnary) (x, p, t)).length := by
      simp only [length_encPair]
      omega
    have := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hle 1) d)
    omega

/-- The sampler input `(x, q)` with the root estimate. -/
private abbrev encLoop (enc : α ↪ List Bool) : (α × ℕ) × (ℕ × ℕ) ↪ List Bool :=
  encPair (encPair enc encUnary) (encPair encNat encNat)

/-- **One trial is strict PPT** on the instance, the accuracy and the root estimate. The loop
invariant: the current node is no longer than `x`, at most `i` bits are recorded, a running walk
has `len x - i` levels left, and the estimate is the root estimate or one returned at a node no
longer than `x`. -/
private theorem isPPTOn_trial
    (hA : IsPPTOn (encPair enc (encPair encUnary encUnary)) (encPair encNat encNat)
      (Function.uncurry fun x => Function.uncurry (A x))) :
    IsPPTOn (encLoop enc) (encOption encBits)
      (fun a : (α × ℕ) × (ℕ × ℕ) => R.trial A a.1.1 a.1.2 a.2) := by
  obtain ⟨c, d, hcd⟩ := hA.length_le
  have hx : ComputableInPolyTime (fun a : (α × ℕ) × (ℕ × ℕ) => a.1.1) (encLoop enc) enc :=
    (ComputableInPolyTime.fst (encPair enc encUnary) (encPair encNat encNat)).fst'
  have hq : ComputableInPolyTime (fun a : (α × ℕ) × (ℕ × ℕ) => a.1.2) (encLoop enc) encUnary :=
    (ComputableInPolyTime.fst (encPair enc encUnary) (encPair encNat encNat)).snd'
  have hlen : ComputableInPolyTime (fun a : (α × ℕ) × (ℕ × ℕ) => R.len a.1.1) (encLoop enc)
      encUnary := R.len_polytime.comp hx
  have hP := computableInPolyTime_counterAccuracy hlen
  have hT := computableInPolyTime_precision hlen hq
  have hM := computableInPolyTime_damping hlen
  have hinitial : ComputableInPolyTime
      (fun a : (α × ℕ) × (ℕ × ℕ) => ((a.1.1, a.2, [], true) : WalkState α)) (encLoop enc)
      (encState enc) :=
    hx.prod ((ComputableInPolyTime.snd _ _).prod
      ((ComputableInPolyTime.const (encOut := encBits) []).prod
        (ComputableInPolyTime.const (encOut := encBool) true)))
  have hsize : PolyBounded (fun a => (encLoop enc a).length)
      (fun a : (α × ℕ) × (ℕ × ℕ) => 2 * (enc a.1.1).length + 1 +
        (2 * ((encPair encNat encNat a.2).length + (c * ((encPair enc (encPair encUnary encUnary)
          (a.1.1, counterAccuracy (R.len a.1.1), precision (R.len a.1.1) a.1.2)).length + 1) ^ d +
            (encPair encNat encNat (1, 1)).length)) + 1 +
          (2 * (encUnary (R.len a.1.1)).length + 2))) := by
    have h1 := hx.polyBounded_length
    have h2 := (ComputableInPolyTime.snd (encPair enc encUnary)
      (encPair encNat encNat)).polyBounded_length
    have h3 := (hx.prod (hP.prod hT)).polyBounded_length
    have h4 := hlen.polyBounded_length
    have hK := ((PolyBounded.const c).mul ((h3.add (PolyBounded.const 1)).pow d)).add
      (PolyBounded.const (encPair encNat encNat (1, 1)).length)
    exact (((PolyBounded.const 2).mul h1).add (PolyBounded.const 1)).add
      ((((PolyBounded.const 2).mul (h2.add hK)).add (PolyBounded.const 1)).add
        (((PolyBounded.const 2).mul h4).add (PolyBounded.const 2)))
  have hstep := R.isPPTOn_walkStep A hA hP hT hM hT
  have hloop := IsPPTOn.iterateWith_spec' (input := encLoop enc) (stateEncoding := encState enc)
    (step := fun a => R.walkStep A (counterAccuracy (R.len a.1.1)) (precision (R.len a.1.1) a.1.2)
      (damping (R.len a.1.1)) (precision (R.len a.1.1) a.1.2))
    hlen hinitial hstep
    (fun a i s => (enc s.1).length ≤ (enc a.1.1).length ∧ s.2.2.1.length ≤ i ∧
      (s.2.2.2 = true → R.len s.1 + i = R.len a.1.1) ∧
      (s.2.1 = a.2 ∨ (encPair encNat encNat s.2.1).length ≤
        estBound enc c d a.1.1 (counterAccuracy (R.len a.1.1)) (precision (R.len a.1.1) a.1.2)))
    (fun a => ⟨le_rfl, by simp, fun _ => by simp, Or.inl rfl⟩)
    (fun a i s hi ⟨henc, hacc, hrun, hest⟩ s' hs' => by
      rcases R.mem_support_walkStep A hs' with ⟨hdead, rfl⟩ | ⟨halive, e₀, he₀, e₁, he₁, o, rfl⟩
      · refine ⟨henc, hacc.trans (Nat.le_succ i), fun h => ?_, hest⟩
        rw [hdead] at h
        exact absurd h Bool.false_ne_true
      · have hrun' := hrun halive
        have hpos : 0 < R.len s.1 := by omega
        cases o with
        | none =>
          exact ⟨henc, hacc.trans (Nat.le_succ i), fun h => absurd h Bool.false_ne_true, hest⟩
        | some b =>
          refine ⟨(R.length_child_le s.1 hpos b).trans henc, ?_, fun _ => ?_, Or.inr ?_⟩
          · change (b :: s.2.2.1).length ≤ i + 1
            rw [List.length_cons]
            omega
          · change R.len (R.child s.1 b) + (i + 1) = R.len a.1.1
            rw [R.len_child s.1 hpos b]
            omega
          · change (encPair encNat encNat (cond b e₁ e₀)).length ≤ _
            cases b
            · exact R.length_estimate_le A hcd ((R.length_child_le s.1 hpos false).trans henc) he₀
            · exact R.length_estimate_le A hcd ((R.length_child_le s.1 hpos true).trans henc) he₁)
    hsize
    (fun a i s hi ⟨henc, hacc, _, hest⟩ => by
      have hE : (encPair encNat encNat s.2.1).length ≤ (encPair encNat encNat a.2).length +
          estBound enc c d a.1.1 (counterAccuracy (R.len a.1.1))
            (precision (R.len a.1.1) a.1.2) := by
        rcases hest with h | h
        · rw [h]
          omega
        · omega
      unfold estBound at hE
      simp only [encState, length_encPair, encBits_apply, encBool_apply, List.length_singleton,
        encUnary_apply, List.length_replicate] at hE ⊢
      omega)
  have hfinish : ComputableInPolyTime (walkFinish W) (encState enc) (encOption encBits) := by
    unfold walkFinish
    have hnil : ComputableInPolyTime (fun s : WalkState α => decide ([] ∈ W s.1)) (encState enc)
        encBool := R.nil_mem_polytime.comp (ComputableInPolyTime.fst _ _)
    have hrev : ComputableInPolyTime (fun s : WalkState α => s.2.2.1.reverse) (encState enc)
        encBits := ComputableInPolyTime.bitsReverse.comp (ComputableInPolyTime.snd _ _).snd'.fst'
    exact ComputableInPolyTime.ite
      (ComputableInPolyTime.bool_and' (ComputableInPolyTime.snd _ _).snd'.snd' hnil)
      ((ComputableInPolyTime.optionSome encBits).comp hrev) (ComputableInPolyTime.const none)
  refine (hloop.1.map hfinish).congr fun a => ?_
  rw [R.trial_eq]

/-- **The counting-to-sampling sampler is strict PPT** on the instance and the unary accuracy
`q`, when the counter is strict PPT on the instance and its unary parameters. It makes at most
`1 + 2 ℓ · trials q` counter calls, with `ℓ = len x`, on instances no longer than `x`. -/
theorem isPPTOn_sampler
    (hA : IsPPTOn (encPair enc (encPair encUnary encUnary)) (encPair encNat encNat)
      (Function.uncurry fun x => Function.uncurry (A x))) :
    IsPPTOn (encPair enc encUnary) (encOption encBits) (Function.uncurry (R.sampler A)) := by
  have hx := ComputableInPolyTime.fst enc encUnary
  have hq := ComputableInPolyTime.snd enc encUnary
  have hlen : ComputableInPolyTime (fun a : α × ℕ => R.len a.1) (encPair enc encUnary) encUnary :=
    R.len_polytime.comp hx
  have hroot : IsPPTOn (encPair enc encUnary) (encPair encNat encNat)
      (fun a : α × ℕ => R.nodeEstimate A (counterAccuracy (R.len a.1)) (precision (R.len a.1) a.2)
        a.1) :=
    R.isPPTOn_nodeEstimate A hA hx (computableInPolyTime_counterAccuracy hlen)
      (computableInPolyTime_precision hlen hq)
  have hfuel : ComputableInPolyTime (fun a : (α × ℕ) × (ℕ × ℕ) => trials a.1.2) (encLoop enc)
      encUnary :=
    computableInPolyTime_trials
      (ComputableInPolyTime.fst (encPair enc encUnary) (encPair encNat encNat)).snd'
  have hgood : ComputableInPolyTime (fun o : Option (List Bool) => o.isSome) (encOption encBits)
      encBool :=
    ComputableInPolyTime.optionIsSome (ComputableInPolyTime.id' (encIn := encOption encBits))
  have hretry := (R.isPPTOn_trial A hA).retry hgood hfuel
  have hjoin : ComputableInPolyTime (fun o : Option (Option (List Bool)) => o.join)
      (encOption (encOption encBits)) (encOption encBits) := by
    have h : (fun o : Option (Option (List Bool)) => o.join) = fun o => o.getD none := by
      funext o
      cases o <;> rfl
    rw [h]
    exact ComputableInPolyTime.optionGetDWithInput
      (ComputableInPolyTime.id' (encIn := encOption (encOption encBits)))
      (ComputableInPolyTime.const none)
  have hsecond : IsPPTOn (encLoop enc) (encOption encBits)
      (fun a : (α × ℕ) × (ℕ × ℕ) => Option.join <$> OracleComp.retry
        (fun o : Option (List Bool) => o.isSome) (R.trial A a.1.1 a.1.2 a.2) (trials a.1.2)) :=
    hretry.map hjoin
  have h : IsPPTOn (encPair enc encUnary) (encOption encBits) (fun a : α × ℕ => do
      let e ← R.nodeEstimate A (counterAccuracy (R.len a.1)) (precision (R.len a.1) a.2) a.1
      Option.join <$> OracleComp.retry (fun o : Option (List Bool) => o.isSome)
        (R.trial A a.1 a.2 e) (trials a.2)) :=
    IsPPTOn.bind_with hroot hsecond
  exact h.congr fun a => rfl

/-- **Approximate counting gives almost uniform sampling** [Jerrum, Valiant and
Vazirani][JerrumValiantVazirani1986]: for a one-bit self-reducible witness family, a fully
polynomial randomized approximation scheme `A` for the number of witnesses yields a fully
polynomial almost uniform sampler `R.sampler A`. -/
theorem isFPAUS_of_isFPRAS (hA : IsFPRAS enc (fun x => (W x).card) A) :
    IsFPAUS enc W (R.sampler A) :=
  ⟨R.isPPTOn_sampler A hA.1, R.closeTo_sampler_of_isFPRAS hA⟩

include R in
/-- **The class form**: a one-bit self-reducible witness family whose witness counts have a fully
polynomial randomized approximation scheme has a fully polynomial almost uniform sampler. -/
theorem mem_FPAUS_of_mem_FPRAS (hW : (fun x => (W x).card) ∈ FPRAS enc) : W ∈ FPAUS enc :=
  let ⟨A, hA⟩ := hW
  ⟨R.sampler A, R.isFPAUS_of_isFPRAS A hA⟩

include R in
/-- **Sampling and counting are equivalent** for one-bit self-reducible witness families [Jerrum,
Valiant and Vazirani][JerrumValiantVazirani1986]: the family has a fully polynomial almost uniform
sampler exactly when its witness counts have a fully polynomial randomized approximation scheme. -/
theorem mem_FPAUS_iff_mem_FPRAS : W ∈ FPAUS enc ↔ (fun x => (W x).card) ∈ FPRAS enc :=
  ⟨R.mem_FPRAS_of_mem_FPAUS, R.mem_FPAUS_of_mem_FPRAS⟩

end Cslib.Complexity.SelfReducible
