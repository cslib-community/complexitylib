/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Bound
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryNormalization
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OPrimitives

/-!
# Running the simulation from a configuration, with an input oracle

`Turing.MultiTapeTM.Universal.lookStep d look p` is a step of the simulation of the machine
described by `d` that asks the *oracle* `look p` for the symbol under the input head instead of
reading an input list, and collects the emitted symbol. When the oracle answers as
`Turing.MultiTapeTM.Universal.inputSymbol x` does on the positions the input head can reach, its
runs are the runs of the simulation on `x`
(`Turing.MultiTapeTM.Universal.lookStep_iterate_eq_stepOut`). The oracle need not hold `x`: it can
compute the symbols of an input that is never written down, such as a padded input.

`Turing.MultiTapeTM.Universal.lookRun d look (p, (c, w))` runs `lookStep` from the configuration
`c` for the number of steps written in binary by `w`. It is computable from any configuration
within the time of the counter and of every step along the run
(`Turing.MultiTapeTM.Universal.lookRun_inO`), and a step costs the description lookup and the
configuration passes of `Turing.MultiTapeTM.Universal.stepWith_inO` plus one query to the oracle
(`Turing.MultiTapeTM.Universal.lookStep_inO`). Unlike `Turing.MultiTapeTM.Universal.simulate`,
neither starts from the initial configuration, so a run can be cut into blocks.

## Main definitions

* `Turing.MultiTapeTM.Universal.lookStep`: a step with an input oracle.
* `Turing.MultiTapeTM.Universal.lookStepTime`: its time bound.
* `Turing.MultiTapeTM.Universal.lookRun`: a binary number of steps from a configuration.

## Main results

* `Turing.MultiTapeTM.Universal.lookStep_iterate_eq_stepOut`: with a faithful oracle, the run of
  the simulation.
* `Turing.MultiTapeTM.Universal.lookStep_inO`, `Turing.MultiTapeTM.Universal.lookRun_inO`: the
  costs.
-/

public section

namespace Turing.MultiTapeTM.Universal

variable {π : Type} (d : Desc) (look : π × ℕ → Option ℕ)

/-! ### Steps with an input oracle -/

/-- A step of the machine described by `d`, asking the oracle `look p` for the symbol under the
input head at position `c.1.inputPos`, and appending the emitted symbol to the output `c.2`. -/
def lookStep (p : π) (c : SCfg × List ℕ) : SCfg × List ℕ :=
  ((stepWith d c.1 (look (p, c.1.inputPos))).1,
    c.2 ++ (stepWith d c.1 (look (p, c.1.inputPos))).2.toList)

/-- With the right answer, a step with an oracle is a step of the simulation. -/
theorem lookStep_eq_stepOut {p : π} {x : List ℕ} {c : SCfg × List ℕ}
    (h : look (p, c.1.inputPos) = inputSymbol x c.1.inputPos) :
    lookStep d look p c = stepOut d x c := by
  simp only [lookStep, stepOut, step_eq_stepWith, h]

/-- **Runs with a faithful oracle.** If the oracle answers as `inputSymbol x` on the positions up
to `x.length + 1`, which are all the positions the input head reaches, the runs with the oracle
from the initial configuration are those of the simulation on `x`. -/
theorem lookStep_iterate_eq_stepOut {p : π} {x : List ℕ}
    (h : ∀ q ≤ x.length + 1, look (p, q) = inputSymbol x q) (j : ℕ) :
    (lookStep d look p)^[j] (init d, []) = (stepOut d x)^[j] (init d, []) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact lookStep_eq_stepOut d look (h _ (inv_iterate d x j).1.inputPos)

/-! ### The cost of a step -/

/-- The time bound of a step with the oracle, for an oracle within the time `TL` and the space
`SL`: the oracle query, the step without the input
(`Turing.MultiTapeTM.Universal.wTime`) and the length of the arguments. -/
@[expose] def lookStepTime (TL SL : π × ℕ → ℕ) (q : π × (SCfg × List ℕ)) : ℕ :=
  TL (q.1, q.2.1.inputPos) + SL (q.1, q.2.1.inputPos) +
    wTime ((d, q.2.1), look (q.1, q.2.1.inputPos)) + q.2.2.length + 1

private lemma length_eWCtx_le_wTime (c : WCtx) : (eWCtx c).length ≤ wTime c := by
  unfold wTime
  have h : 1 ≤ (c.cfg.workTapes.length + c.desc.table.length + 1) * ((eDesc c.desc).length + 1) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  nlinarith

variable {encP : π ↪ List Bool}

/-- **The cost of a step with an oracle**: if the oracle is computable within the time `TL` and
the space `SL`, a step is computable within the time `lookStepTime`, up to a constant, in the
length of the arguments as well. -/
theorem lookStep_inO {TL SL : π × ℕ → ℕ}
    (hlook : ComputableInO look (encPair encP encNat) eSym TL SL) :
    ComputableInO (fun q : π × (SCfg × List ℕ) => lookStep d look q.1 q.2)
      (encPair encP (encPair eCfg (encList encUnary))) (encPair eCfg (encList encUnary))
      (fun q => (encPair encP (encPair eCfg (encList encUnary)) q).length +
        lookStepTime d look TL SL q)
      (fun q => (encPair encP (encPair eCfg (encList encUnary)) q).length +
        lookStepTime d look TL SL q) := by
  have hp := ComputableInO.fst encP (encPair eCfg (encList encUnary))
  have hcfg := (ComputableInO.snd encP (encPair eCfg (encList encUnary))).fst'
  have hout := (ComputableInO.snd encP (encPair eCfg (encList encUnary))).snd'
  have hpos := (hcfg.of_enc_eq (encC := eCfgFields)
    (g := fun q : π × (SCfg × List ℕ) => (q.2.1.state, q.2.1.inputPos, q.2.1.workTapes))
    fun _ => rfl).snd'.fst'
  have hsym := hlook.comp' (hp.prod hpos)
  have hctx := ((ComputableInO.const (encIn := encPair encP (encPair eCfg (encList encUnary)))
    (encMid := eDesc) d).prod hcfg).prod hsym
  have hsw := stepWith_inO.comp' hctx
  have hem := hsw.snd'
  have hsnoc := (ComputableInDegree.snoc encUnary).inO_one.comp_linear
    (hout.prod (ComputableInO.optionGetD 0 hem))
  have hnew := (ComputableInO.optionIsSome hem).ite hsnoc hout
  refine ((hsw.fst'.prod hnew).mono 16 (fun q => ?_) fun q => ?_).of_enc_eq fun q => ?_
  all_goals
    have hw := length_eWCtx_le_wTime ((d, q.2.1), look (q.1, q.2.1.inputPos))
    dsimp only [lookStepTime, Function.comp_apply, WCtx.desc, WCtx.cfg, WCtx.sym] at hw ⊢
  · split_ifs <;> omega
  · split_ifs <;> omega
  · rcases h : (stepWith d q.2.1 (look (q.1, q.2.1.inputPos))).2 with _ | e <;>
      simp [lookStep, h]

/-! ### Runs from a configuration -/

/-- The run with the oracle from the configuration `c`, for the number of steps written in binary
by `w` (`Turing.MultiTapeTM.ofBits`). -/
@[expose] def lookRun (q : π × (SCfg × List ℕ) × List Bool) : SCfg × List ℕ :=
  (lookStep d look q.1)^[ofBits q.2.2] q.2.1

private lemma iterate_step_eq (p : π) (c : SCfg × List ℕ) (k : ℕ) :
    (fun s : π × (SCfg × List ℕ) => (s.1, lookStep d look s.1 s.2))^[k] (p, c) =
      (p, (lookStep d look p)^[k] c) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']

/-- **The cost of a run from a configuration.** If the oracle is computable within the time `TL`
and the space `SL`, and along the run from `c` for `ofBits w` steps every step is within the time
`R` (`Turing.MultiTapeTM.Universal.lookStepTime`) and every configuration with its output is encoded
within `B` bits, the run is computable within the arguments and, for every step, `R`, `B` and the
square of the length of the counter. -/
theorem lookRun_inO [Inhabited π] {R B : π × (SCfg × List ℕ) × List Bool → ℕ}
    {TL' SL' : π × ℕ → ℕ}
    (hlook : ComputableInO look (encPair encP encNat) eSym TL' SL')
    (hR : ∀ q k, k ≤ ofBits q.2.2 →
      lookStepTime d look TL' SL' (q.1, (lookStep d look q.1)^[k] q.2.1) ≤ R q)
    (hB : ∀ q k, k ≤ ofBits q.2.2 →
      (encPair encP (encPair eCfg (encList encUnary))
        (q.1, (lookStep d look q.1)^[k] q.2.1)).length ≤ B q) :
    ComputableInO (lookRun d look)
      (encPair encP (encPair (encPair eCfg (encList encUnary)) encBits))
      (encPair eCfg (encList encUnary))
      (fun q => (encPair encP (encPair (encPair eCfg (encList encUnary)) encBits) q).length +
        (ofBits q.2.2 + 1) * (R q + B q + (q.2.2.length + 1) ^ 2))
      (fun q => (encPair encP (encPair (encPair eCfg (encList encUnary)) encBits) q).length +
        R q + B q) := by
  have hw := (ComputableInO.snd encP (encPair (encPair eCfg (encList encUnary)) encBits)).snd'
  have hn := ComputableInO.bitsToNat.comp' hw
  have hinit := (ComputableInO.fst encP (encPair (encPair eCfg (encList encUnary)) encBits)).prod
    (ComputableInO.snd encP (encPair (encPair eCfg (encList encUnary)) encBits)).fst'
  have hstep := (ComputableInO.fst encP (encPair eCfg (encList encUnary))).prod
    (lookStep_inO d look hlook)
  have hit := ComputableInO.iterate (n := fun q : π × (SCfg × List ℕ) × List Bool => ofBits q.2.2)
    (init := fun q => (q.1, q.2.1)) (step := fun s => (s.1, lookStep d look s.1 s.2))
    (R := fun q => 2 * B q + R q) (Q := fun q => 2 * B q + R q) (B := B) hn hinit hstep
    (fun q k hk => ?_) (fun q k hk => ?_) (fun q k hk => ?_)
  rotate_left
  · rw [iterate_step_eq]
    have := hR q k hk
    have := hB q k hk
    omega
  · rw [iterate_step_eq]
    have := hR q k hk
    have := hB q k hk
    omega
  · rw [iterate_step_eq]
    exact hB q k hk
  refine (hit.snd'.of_enc_eq fun q => ?_).mono 8 (fun q => ?_) fun q => ?_
  · rw [iterate_step_eq]
    rfl
  all_goals
    have hwL : q.2.2.length ≤
        (encPair encP (encPair (encPair eCfg (encList encUnary)) encBits) q).length := by
      simp only [length_encPair, encBits_apply]
      omega
    have hn := length_encNat_ofBits_le q.2.2
  · have hX : ((encNat (ofBits q.2.2)).length + 1) ^ 2 ≤ (q.2.2.length + 1) ^ 2 := by gcongr
    have h₁ : 2 * B q + R q + B q + ((encNat (ofBits q.2.2)).length + 1) ^ 2 ≤
        3 * (R q + B q + (q.2.2.length + 1) ^ 2) := by
      omega
    have h₂ := Nat.mul_le_mul_left (ofBits q.2.2 + 1) h₁
    have h₃ : (ofBits q.2.2 + 1) * (3 * (R q + B q + (q.2.2.length + 1) ^ 2)) =
        3 * ((ofBits q.2.2 + 1) * (R q + B q + (q.2.2.length + 1) ^ 2)) := by
      ring
    omega
  · omega

end Turing.MultiTapeTM.Universal
