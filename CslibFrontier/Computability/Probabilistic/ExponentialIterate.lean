/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Languages.Probabilistic.Iteration
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Loop.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.IterateWhile
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Tidy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Composition.Space
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import CslibFrontier.Tactic.EncLen

/-!
# Binary-counter exponential iteration on fair-coin multitape machines

`Cslib.Probability.IsPPTOn.iterate_spec` clocks bounded adaptive loops in polynomial time when the
iteration count is computed in unary (`encUnary`). Exponential-time randomized algorithms such as
Schöning's `k`-SAT walk instead repeat a polynomial-time step an exponential number of times while
reusing polynomial workspace across restarts.

When the iteration count `count : α → ℕ` is computable in polynomial time in **binary** (`encNat`),
`(encNat (count a)).length` is polynomial in `(input a).length` even when `count a` itself is
exponential. Pairing a binary countdown counter with a polynomially bounded state and running clean
phases inside `Turing.MultiTapePTM.repeatUntilBlank` produces one finite-control `MultiTapePTM`
whose runs:

* halt on every branch within `C * ((count a + 1) * ((input a).length + 1) ^ E)` steps,
* realize `(ProbComp.eval (OracleComp.iterate (count a) (step a) (initial a))).map stateEncoding`,
* visit at most `C * ((input a).length + 1) ^ E` work-tape cells (`toNTM.RunsInSpace`), independent
  of `count a`.

## Main definitions

* `Cslib.Probability.repeatAnyStep`: one OR-accumulating trial step (`if acc then pure true else
  trial`).

## Main results

* `Cslib.Probability.eval_iterate_repeatAnyStep_false_toReal`: `r` independent trials fail with
  probability `(1 - p) ^ r`.
* `Cslib.Probability.IsPPTOn.exists_multiTapePTM_iterate_binary`: closed binary-counter iteration
  with `(count a + 1) * poly(|input a|)` halting time and polynomial workspace.
* `Cslib.Probability.IsPPTOn.exists_multiTapePTM_iterateWith_binary`: captured-input variant.
* `Cslib.Probability.IsPPTOn.exists_multiTapePTM_repeatAnyBool_binary`: repeating a strict PPT
  Boolean trial an exponential binary-computable number of times in polynomial workspace.
-/

public section

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
  _root_.Turing.MultiTapePTM


namespace ExpIterateInternal



/-! ### Closed bridges and opaque two-phase composition -/

private noncomputable def emptyOracle : Empty × List Bool → StateT Unit PMF (List Bool) :=
  fun q => q.1.elim

private theorem runOracle_empty {k : ℕ} {State : Type} (M : MultiTapePTM k Bool State)
    (fuel : ℕ) (x : List Bool) :
    M.runOracle fuel x = ProbOracleComp.sample (M.runClosed fuel x) := by
  rw [runOracle_eq_map, MultiTapePTM.runOracleConfigFrom_empty, ← ProbOracleComp.sample_map,
    ← runClosed_eq_map]

private theorem halted_of_computesTidily {k : ℕ} {State : Type} {x : List Bool} {t : ℕ}
    {prog : ProbOracleComp (fun _ : Empty × List Bool => List Bool) (List Bool)}
    {M : MultiTapePTM k Bool State} (h : M.ComputesTidily x t prog) :
    ∀ final ∈ (ProbComp.eval (M.runClosedConfigFrom t (M.initialConfig x))).support,
      final.tapes.state = none := by
  intro final hfinal
  have hh := (h []).halted emptyOracle () (M.initialConfig x) (Cfg.init_eq_wordsCfg M.initial x)
    (fun op => op.elim) (final, ())
  rw [MultiTapePTM.runOracleConfigFrom_empty, ProbOracleComp.runWith_sample,
    PMF.mem_support_map_iff] at hh
  exact hh ⟨final, hfinal, rfl⟩

private theorem eval_runClosed_of_computesTidily {k : ℕ} {State : Type} {x : List Bool} {t : ℕ}
    {prog : ProbComp (List Bool)} {M : MultiTapePTM k Bool State}
    (h : M.ComputesTidily x t (ProbOracleComp.sample prog)) :
    ProbComp.eval (M.runClosed t x) = ProbComp.eval prog := by
  have hlaw := congrArg (PMF.map Prod.fst) (h.runOracle emptyOracle ())
  rw [runOracle_empty, ProbOracleComp.runWith_sample, ProbOracleComp.runWith_sample,
    PMF.map_comp, PMF.map_comp] at hlaw
  have hid : (Prod.fst ∘ fun a : List Bool => (a, ())) = id := rfl
  rwa [hid, PMF.map_id, PMF.map_id] at hlaw

private theorem runsInSpace_toNTM_of_computesTidily {k : ℕ} {State : Type} {x : List Bool}
    {t : ℕ} {prog : ProbOracleComp (fun _ : Empty × List Bool => List Bool) (List Bool)}
    {M : MultiTapePTM k Bool State} (h : M.ComputesTidily x t prog) :
    M.toNTM.RunsInSpace x (k * (2 * t + 1)) := by
  intro path
  apply MultiTapeNTM.RunPath.InWindow.space_le
  rintro _ ⟨idx, rfl⟩ j
  obtain ⟨coins, _, hcoins⟩ := M.exists_runPath_toNTM_iff.mp
    ⟨path.toRunPath.take idx, RelSeries.head_take _ _, rfl, RelSeries.last_take _ _⟩
  rw [← hcoins, path.head_eq, initCfg_toNTM, ← tapes_runClosedConfigFromCoins]
  exact workTapePos_runsWords_mem_window M (h []) (M.initialConfig x)
    (Cfg.init_eq_wordsCfg M.initial x) coins j

/-- Existential closed composition keeping machine terms opaque to the kernel. -/
private theorem exists_comp_closed {α : Type} {k₀ k₁ : ℕ} {S₀ S₁ : Type} [Finite S₀] [Finite S₁]
    (M₀ : MultiTapePTM k₀ Bool S₀) (M₁ : MultiTapePTM k₁ Bool S₁)
    (inp : α → List Bool) (t₀ t₁ s₀ s₁ bnd : α → ℕ)
    (μ₀ : α → PMF (List Bool)) (μ₁ : α → List Bool → PMF (List Bool))
    (hhalt₀ : ∀ a, ∀ final ∈ (ProbComp.eval
      (M₀.runClosedConfigFrom (t₀ a) (M₀.initialConfig (inp a)))).support,
      final.tapes.state = none)
    (heval₀ : ∀ a, ProbComp.eval (M₀.runClosed (t₀ a) (inp a)) = μ₀ a)
    (hspace₀ : ∀ a, M₀.toNTM.RunsInSpace (inp a) (s₀ a))
    (hbnd : ∀ a w, w ∈ (μ₀ a).support → w.length ≤ bnd a)
    (hhalt₁ : ∀ a w, w ∈ (μ₀ a).support → ∀ final ∈ (ProbComp.eval
      (M₁.runClosedConfigFrom (t₁ a) (M₁.initialConfig w))).support,
      final.tapes.state = none)
    (heval₁ : ∀ a w, w ∈ (μ₀ a).support → ProbComp.eval (M₁.runClosed (t₁ a) w) = μ₁ a w)
    (hspace₁ : ∀ a w, w ∈ (μ₀ a).support → M₁.toNTM.RunsInSpace w (s₁ a)) :
    ∃ (K : ℕ) (Control : Type) (_ : Finite Control) (M : MultiTapePTM K Bool Control),
      ∀ a,
        let T := t₀ a + (t₀ a + 4 + t₁ a)
        let S := (k₁ + k₀ + 2) * (2 * max (max (s₀ a) (s₁ a)) (bnd a + 2) + 1)
        (∀ final ∈ (ProbComp.eval (M.runClosedConfigFrom T (M.initialConfig (inp a)))).support,
          final.tapes.state = none) ∧
        ProbComp.eval (M.runClosed T (inp a)) = (μ₀ a).bind (μ₁ a) ∧
        M.toNTM.RunsInSpace (inp a) S := by
  refine ⟨k₁ + k₀ + 2, _, inferInstance, M₁.comp M₀ true, fun a => ?_⟩
  have hsupp (w : List Bool) :
      w ∈ (ProbComp.eval (M₀.runClosed (t₀ a) (inp a))).support ↔ w ∈ (μ₀ a).support := by
    rw [heval₀ a]
  refine ⟨?_, ?_, ?_⟩
  · exact comp_halted M₀ M₁ true (inp a) (t₀ a) (t₁ a) (hhalt₀ a)
      (fun w hw => hhalt₁ a w ((hsupp w).mp hw))
  · rw [eval_comp M₀ M₁ true (inp a) (t₀ a) (t₁ a) (hhalt₀ a)
      (fun w hw => hhalt₁ a w ((hsupp w).mp hw)), Probability.PMF.monad_bind_eq_bind, heval₀ a]
    apply Probability.PMF.bind_congr_on_support
    exact fun w hw => heval₁ a w hw
  · exact runsInSpace_toNTM_comp M₀ M₁ true (hhalt₀ a) (hspace₀ a)
      (fun w hw => hbnd a w ((hsupp w).mp hw))
      (fun w hw => hspace₁ a w ((hsupp w).mp hw))

/-- Package a closed machine `fullM` running within `(count a + 1) * polyFactor a` steps and
`fullSpace a` cells into uniform `(C, E)` polynomial envelopes. -/
private theorem exists_envelope_closed {α : Type} {kFull : ℕ} {FullControl : Type}
    [Finite FullControl] (fullM : MultiTapePTM kFull Bool FullControl)
    (inp : α → List Bool) (count fullTime fullSpace polyFactor : α → ℕ)
    (target : α → PMF (List Bool))
    (hpolyFactor : PolyBounded (fun a => (inp a).length) polyFactor)
    (hfullSpacePoly : PolyBounded (fun a => (inp a).length) fullSpace)
    (hraw_le : ∀ a, fullTime a ≤ (count a + 1) * polyFactor a)
    (hfullM : ∀ a,
      (∀ final ∈ (ProbComp.eval
          (fullM.runClosedConfigFrom (fullTime a) (fullM.initialConfig (inp a)))).support,
          final.tapes.state = none) ∧
      ProbComp.eval (fullM.runClosed (fullTime a) (inp a)) = target a ∧
      fullM.toNTM.RunsInSpace (inp a) (fullSpace a)) :
    ∃ (K : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM K Bool Control) (C E : ℕ),
      ∀ a,
        let T := C * ((count a + 1) * ((inp a).length + 1) ^ E)
        let S := C * ((inp a).length + 1) ^ E
        (∀ final ∈ (ProbComp.eval
            (machine.runClosedConfigFrom T (machine.initialConfig (inp a)))).support,
            final.tapes.state = none) ∧
          ProbComp.eval (machine.runClosed T (inp a)) = target a ∧
          machine.toNTM.RunsInSpace (inp a) S := by
  obtain ⟨ct, dt, hct⟩ := hpolyFactor.exists_le
  obtain ⟨cs, ds, hcs⟩ := hfullSpacePoly.exists_le
  let C : ℕ := max ct cs + 1
  let E : ℕ := max dt ds
  refine ⟨kFull, FullControl, inferInstance, fullM, C, E, fun a => ?_⟩
  let T := C * ((count a + 1) * ((inp a).length + 1) ^ E)
  let S := C * ((inp a).length + 1) ^ E
  obtain ⟨hhalt_raw, heval_raw, hspace_raw⟩ := hfullM a
  have hfull_le_T : fullTime a ≤ T := by
    have h2 : polyFactor a ≤ C * ((inp a).length + 1) ^ E :=
      (hct a).trans <| Nat.mul_le_mul ((le_max_left ct cs).trans (Nat.le_succ _))
        (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left dt ds))
    calc fullTime a ≤ (count a + 1) * (C * ((inp a).length + 1) ^ E) :=
          (hraw_le a).trans (Nat.mul_le_mul_left _ h2)
      _ = T := by dsimp only [T]; ring
  have hfull_le_S : fullSpace a ≤ S :=
    (hcs a).trans <| Nat.mul_le_mul ((le_max_right ct cs).trans (Nat.le_succ _))
      (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right dt ds))
  refine ⟨?_, ?_, fun p => (hspace_raw p).trans hfull_le_S⟩
  · rw [fullM.eval_runClosedConfigFrom_eq_of_halted _ hfull_le_T hhalt_raw]
    exact hhalt_raw
  · rw [fullM.eval_runClosed_eq_of_halted _ hfull_le_T hhalt_raw, heval_raw]

private theorem iterate_countdown {σ β : Type} (encode : ℕ × σ → β)
    (step : σ → WordOracleComp Empty σ) (wordStep : β → WordOracleComp Empty β)
    (hstep : ∀ c state, wordStep (encode (c + 1, state)) =
      (fun next => encode (c, next)) <$> step state) (c count : ℕ) (state : σ) :
    OracleComp.iterate count wordStep (encode (c + count, state)) =
      (fun final => encode (c, final)) <$> OracleComp.iterate count step state := by
  induction count generalizing state with
  | zero => simp only [Nat.add_zero, OracleComp.iterate_zero, map_pure]
  | succ count ih =>
    rw [OracleComp.iterate_succ_bind, OracleComp.iterate_succ_bind, ← Nat.add_assoc, hstep,
      bind_map_left, map_bind]
    simp only [ih]

end ExpIterateInternal

/-! ### Binary-counter exponential iteration -/

section BinaryIterate

variable {α σ : Type} {input : α ↪ List Bool} {stateEncoding : σ ↪ List Bool}

/-- **Closed binary-counter iteration in polynomial workspace.** If `count : α → ℕ` is computable in
polynomial time in **binary** (`encNat`), `initial` is computable in polynomial time, `step` is
strict PPT, and an invariant bounds the encoded size of every reachable state by a polynomial in
`|input a|`, then one finite-control fair-coin `MultiTapePTM` halts on every branch within
`C * ((count a + 1) * ((input a).length + 1) ^ E)` steps, realizes `OracleComp.iterate (count a)
step (initial a)` under `stateEncoding`, and runs in polynomial workspace
`C * ((input a).length + 1) ^ E` independent of `count a`. -/
theorem IsPPTOn.exists_multiTapePTM_iterate_binary {initial : α → σ} {count : α → ℕ}
    {step : σ → ProbComp σ}
    (hcount : ComputableInPolyTime count input encNat)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : IsPPTOn stateEncoding stateEncoding step)
    (invariant : α → ℕ → σ → Prop) (hbase : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a i state, i < count a → invariant a i state →
      ∀ next ∈ (ProbComp.eval (step state)).support, invariant a (i + 1) next)
    {size : α → ℕ} (hsize : PolyBounded (fun a => (input a).length) size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state →
      (stateEncoding state).length ≤ size a) :
    (∃ (K : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM K Bool Control) (C E : ℕ),
      ∀ a,
        let T := C * ((count a + 1) * ((input a).length + 1) ^ E)
        let S := C * ((input a).length + 1) ^ E
        (∀ final ∈ (ProbComp.eval
            (machine.runClosedConfigFrom T (machine.initialConfig (input a)))).support,
            final.tapes.state = none) ∧
          ProbComp.eval (machine.runClosed T (input a)) =
            (ProbComp.eval (OracleComp.iterate (count a) step (initial a))).map stateEncoding ∧
          machine.toNTM.RunsInSpace (input a) S) ∧
      ∀ a state, state ∈ (ProbComp.eval (OracleComp.iterate (count a) step (initial a))).support →
        invariant a (count a) state := by
  classical
  have hinv_final : ∀ a state,
      state ∈ (ProbComp.eval (OracleComp.iterate (count a) step (initial a))).support →
      invariant a (count a) state :=
    fun a => ProbComp.iterate_invariant (count a) step (initial a) (invariant a) (hbase a)
      (fun i hi state hs => hpreserve a i state hi hs)
  refine ⟨?_, hinv_final⟩
  let ostep : σ → WordOracleComp Empty σ := fun s => ProbOracleComp.sample (step s)
  have hostep : IsTidyOraclePPTOn stateEncoding stateEncoding ostep :=
    (hstep.isOraclePPTOn (Operation := Empty)).isTidyOraclePPTOn
  let encode : ℕ × σ ↪ List Bool := encPair encNat stateEncoding
  let body (pair : ℕ × σ) : WordOracleComp Empty (List Bool) :=
    if pair.1 = 0 then pure [] else (fun next => encode (pair.1 - 1, next)) <$> ostep pair.2
  have hbody : IsTidyOraclePPTOn encode encBits body := by
    apply IsTidyOraclePPTOn.ite (ComputableInPolyTime.decide_eq'
      (ComputableInPolyTime.fst encNat stateEncoding) (.const 0))
    · exact IsTidyOraclePPTOn.of_computableInPolyTime (.const [])
    · apply (hostep.preprocess (ComputableInPolyTime.snd encNat stateEncoding)).map_with
      exact (ComputableInPolyTime.of_eq (encIn := encode) (encOut := encBits) (f := encode)
        fun _ => rfl).comp
        ((ComputableInPolyTime.binary_sub'
          ((ComputableInPolyTime.fst encNat stateEncoding).comp
            (ComputableInPolyTime.fst encode stateEncoding)) (.const 1)).prod
          (ComputableInPolyTime.snd encode stateEncoding))
  obtain ⟨_, kB, Body, hfiniteB, bodyM, cB, dB, hbodyM⟩ := hbody
  let wordStep : List Bool → WordOracleComp Empty (List Bool) :=
    Function.extend encode body (fun _ => pure [])
  have hwordStep (pair : ℕ × σ) : wordStep (encode pair) = body pair :=
    encode.injective.extend_apply _ _ pair
  have hencode_le (c m : ℕ) (s : σ) (hcm : c ≤ m) :
      (encode (c, s)).length ≤ 2 * (encNat m).length + 1 + (stateEncoding s).length := by
    have hbits : (encNat c).length ≤ (encNat m).length := by
      simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size hcm
    enc_len [encode]
  have hloop_eq (c r : ℕ) (s : σ) :
      OracleComp.iterate r wordStep (encode (c + r, s)) =
        (fun final => encode (c, final)) <$> OracleComp.iterate r ostep s :=
    ExpIterateInternal.iterate_countdown encode ostep wordStep (fun c state => by
      rw [hwordStep]
      simp only [body, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]) c r s
  obtain ⟨_, kp, Prepare, hfiniteP, prepM, cp, dp, hprepM⟩ :=
    IsTidyOraclePPTOn.of_computableInPolyTime (Operation := Empty)
      ((ComputableInPolyTime.of_eq (encIn := encode) (encOut := encBits) (f := encode)
        fun _ => rfl).comp (hcount.prod hinitial))
  obtain ⟨_, ke, Extract, hfiniteE, extM, ce, de, hextM⟩ :=
    IsTidyOraclePPTOn.of_computableInPolyTime (Operation := Empty)
      ((ComputableInPolyTime.of_eq (encIn := stateEncoding) (encOut := encBits)
        (f := stateEncoding) fun _ => rfl).comp (ComputableInPolyTime.snd encNat stateEncoding))
  let tp (a : α) : ℕ := cp * ((input a).length + 1) ^ dp
  let bound (a : α) : ℕ := 2 * (encNat (count a)).length + 1 + size a
  let roundTime (a : α) : ℕ := cB * (bound a + 1) ^ dB
  let loopTime (a : α) : ℕ := (count a + 1) * (roundTime a + 10 * bound a + 23) + 8 * bound a + 17
  let te (a : α) : ℕ := ce * (bound a + 1) ^ de
  let prepSpace (a : α) : ℕ := kp * (2 * tp a + 1)
  let loopSpace (a : α) : ℕ := (kB + 1 + 2) * (2 * (roundTime a + 10 * bound a + 22) + 1)
  let extSpace (a : α) : ℕ := ke * (2 * te a + 1)
  let start (a : α) : List Bool := encode (count a, initial a)
  let μLoop (a : α) : PMF (List Bool) :=
    (ProbComp.eval (OracleComp.iterate (count a) step (initial a))).map
      (fun final => encode (0, final))
  have hprep_tidy (a : α) :
      prepM.ComputesTidily (input a) (tp a) (ProbOracleComp.sample (pure (start a))) := by
    simpa only [encBits, Function.Embedding.coe_refl, id_eq, map_pure, Function.comp_apply,
      ProbOracleComp.sample_pure] using hprepM a
  have hstart_len (a : α) : (start a).length ≤ bound a :=
    (hencode_le (count a) (count a) (initial a) le_rfl).trans
      (Nat.add_le_add_left (hbound a 0 (initial a) (Nat.zero_le _) (hbase a)) _)
  have hloop_spec (a : α) :
      (Turing.MultiTapePTM.iterateWhile bodyM true).ComputesTidily (start a) (loopTime a)
        (ProbOracleComp.sample
          ((fun final => encode (0, final)) <$> OracleComp.iterate (count a) step (initial a))) ∧
      (Turing.MultiTapePTM.iterateWhile bodyM true).toNTM.RunsInSpace (start a) (loopSpace a) := by
    let inv := fun n word => ∃ state, word = encode (count a - n, state) ∧ invariant a n state
    have hbase' : inv 0 (start a) := ⟨initial a, by simp only [start, Nat.sub_zero], hbase a⟩
    have hround : ∀ n < count a, ∀ w, inv n w →
        bodyM.ComputesTidily w (roundTime a) (wordStep w) := by
      rintro n hn word ⟨state, rfl, hstate⟩
      rw [hwordStep]
      have hlen := hencode_le (count a - n) (count a) state (Nat.sub_le _ _)
      have hs := hbound a n state hn.le hstate
      refine ((hbodyM (count a - n, state)).mono ?_).congr fun State oracle s => ?_
      · exact Nat.mul_le_mul_left cB (Nat.pow_le_pow_left (by dsimp only [bound]; omega) dB)
      · simp only [encBits, Function.Embedding.coe_refl, id_map]
    have hpreserve' : ∀ n < count a, ∀ w, inv n w → ∀ (OracleState : Type) (oracle : _)
        (s s' : OracleState) (w' : List Bool),
        (w', s') ∈ (ProbOracleComp.runWith oracle (wordStep w) s).support →
        inv (n + 1) w' ∧ w' ≠ [] := by
      rintro n hn word ⟨state, rfl, hstate⟩ State oracle s s' next hnext
      rw [hwordStep] at hnext
      have hpos : count a - n ≠ 0 := by omega
      simp only [body, hpos, ↓reduceIte] at hnext
      have hnext' := ProbOracleComp.mem_support_of_mem oracle hnext
      obtain ⟨final, hfinal, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext'
      have hsupp : final ∈ (ProbComp.eval (step state)).support :=
        (ProbOracleComp.support_sample (step state)).subset hfinal
      refine ⟨⟨final, by rw [Nat.sub_sub], hpreserve a n state hn hstate final hsupp⟩, ?_⟩
      simp only [encode, encPair_apply, frame, ne_eq]
      cases encNat (count a - (n + 1)) <;> simp
    have hlast : ∀ w, inv (count a) w → bodyM.ComputesTidily w (roundTime a) (pure []) := by
      rintro word ⟨state, rfl, hstate⟩
      have hlen := hencode_le (count a - count a) (count a) state (Nat.sub_le _ _)
      have hs := hbound a (count a) state le_rfl hstate
      refine ((hbodyM (count a - count a, state)).mono ?_).congr fun State oracle s => ?_
      · exact Nat.mul_le_mul_left cB (Nat.pow_le_pow_left (by dsimp only [bound]; omega) dB)
      · simp only [body, Nat.sub_self, ↓reduceIte, encBits, Function.Embedding.coe_refl, id_map]
    have hlength : ∀ n ≤ count a, ∀ w, inv n w → w.length ≤ bound a := by
      rintro n hn word ⟨state, rfl, hstate⟩
      have hlen := hencode_le (count a - n) (count a) state (Nat.sub_le _ _)
      have hs := hbound a n state hn hstate
      dsimp only [bound]
      omega
    have h1 := Turing.MultiTapePTM.ComputesTidily.iterateWhile true inv hbase'
      hround hpreserve' hlast hlength
    have h2 := Turing.MultiTapePTM.RunsInSpace.iterateWhile true inv hbase'
      hround hpreserve' hlast hlength
    have hboth : _ ∧ _ := ⟨h1, h2⟩
    have hword_sample : OracleComp.iterate (count a) wordStep (start a) =
        ProbOracleComp.sample
          ((fun final => encode (0, final)) <$> OracleComp.iterate (count a) step (initial a)) := by
      have hstart0 : start a = encode (0 + count a, initial a) := by simp only [start, Nat.zero_add]
      rw [hstart0, hloop_eq, ProbOracleComp.sample_map, ProbOracleComp.sample,
        OracleComp.interpret_iterate]
      rfl
    rw [hword_sample] at hboth
    exact hboth
  obtain ⟨kMid, MidControl, hfinMid, midM, hmidM⟩ :=
    ExpIterateInternal.exists_comp_closed prepM (Turing.MultiTapePTM.iterateWhile bodyM true)
      input tp loopTime prepSpace loopSpace bound
      (fun a => PMF.pure (start a)) (fun a _ => μLoop a)
      (fun a => ExpIterateInternal.halted_of_computesTidily (hprep_tidy a))
      (fun a => by
        rw [ExpIterateInternal.eval_runClosed_of_computesTidily (hprep_tidy a), ProbComp.eval_pure])
      (fun a => ExpIterateInternal.runsInSpace_toNTM_of_computesTidily (hprep_tidy a))
      (fun a w hw => by
        rw [PMF.support_pure, Set.mem_singleton_iff] at hw; subst hw; exact hstart_len a)
      (fun a w hw => by
        rw [PMF.support_pure, Set.mem_singleton_iff] at hw; subst hw
        exact ExpIterateInternal.halted_of_computesTidily (hloop_spec a).1)
      (fun a w hw => by
        rw [PMF.support_pure, Set.mem_singleton_iff] at hw; subst hw
        rw [ExpIterateInternal.eval_runClosed_of_computesTidily (hloop_spec a).1,
          ProbComp.eval_map])
      (fun a w hw => by
        rw [PMF.support_pure, Set.mem_singleton_iff] at hw; subst hw; exact (hloop_spec a).2)
  let midTime (a : α) : ℕ := tp a + (tp a + 4 + loopTime a)
  let midSpace (a : α) : ℕ :=
    ((kB + 1 + 2) + kp + 2) * (2 * max (max (prepSpace a) (loopSpace a)) (bound a + 2) + 1)
  have hμLoop_mem (a : α) (w : List Bool) (hw : w ∈ (μLoop a).support) :
      ∃ final ∈ (ProbComp.eval (OracleComp.iterate (count a) step (initial a))).support,
        w = encode (0, final) ∧ w.length ≤ bound a := by
    rw [PMF.mem_support_map_iff] at hw
    obtain ⟨final, hfinal, rfl⟩ := hw
    refine ⟨final, hfinal, rfl, ?_⟩
    have h1 := hencode_le 0 (count a) final (Nat.zero_le _)
    have h2 := hbound a (count a) final le_rfl (hinv_final a final hfinal)
    dsimp only [bound]
    omega
  have hext_on (a : α) (final : σ) (hlen : (encode (0, final)).length ≤ bound a) :
      extM.ComputesTidily (encode (0, final)) (te a)
        (ProbOracleComp.sample (pure (stateEncoding final))) := by
    have h0 : extM.ComputesTidily (encode (0, final))
        (ce * ((encode (0, final)).length + 1) ^ de)
        (ProbOracleComp.sample (pure (stateEncoding final))) := by
      simpa only [encBits, Function.Embedding.coe_refl, id_eq, map_pure, Function.comp_apply,
        ProbOracleComp.sample_pure] using hextM (0, final)
    exact h0.mono (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) de))
  let decodeOut : List Bool → List Bool :=
    Function.extend encode (fun p => stateEncoding p.2) (fun _ => [])
  have hdecodeOut (final : σ) : decodeOut (encode (0, final)) = stateEncoding final :=
    encode.injective.extend_apply (fun p => stateEncoding p.2) (fun _ => []) (0, final)
  obtain ⟨kFull, FullControl, hfinFull, fullM, hfullM⟩ :=
    ExpIterateInternal.exists_comp_closed midM extM
      input midTime te midSpace extSpace bound
      μLoop (fun _ w => PMF.pure (decodeOut w))
      (fun a => (hmidM a).1)
      (fun a => by rw [(hmidM a).2.1, PMF.pure_bind])
      (fun a => (hmidM a).2.2)
      (fun a w hw => (hμLoop_mem a w hw).choose_spec.2.2)
      (fun a w hw => by
        obtain ⟨final, _, rfl, hlen⟩ := hμLoop_mem a w hw
        exact ExpIterateInternal.halted_of_computesTidily (hext_on a final hlen))
      (fun a w hw => by
        obtain ⟨final, _, rfl, hlen⟩ := hμLoop_mem a w hw
        rw [ExpIterateInternal.eval_runClosed_of_computesTidily (hext_on a final hlen),
          ProbComp.eval_pure, hdecodeOut])
      (fun a w hw => by
        obtain ⟨final, _, rfl, hlen⟩ := hμLoop_mem a w hw
        exact ExpIterateInternal.runsInSpace_toNTM_of_computesTidily (hext_on a final hlen))
  let fullTime (a : α) : ℕ := midTime a + (midTime a + 4 + te a)
  let fullSpace (a : α) : ℕ :=
    (ke + kMid + 2) * (2 * max (max (midSpace a) (extSpace a)) (bound a + 2) + 1)
  have htpPoly : PolyBounded (fun a => (input a).length) tp :=
    .of_forall_le cp dp fun _ => le_rfl
  have hcountLenPoly : PolyBounded (fun a => (input a).length)
      (fun a => (encNat (count a)).length) := hcount.polyBounded_length
  have hboundPoly : PolyBounded (fun a => (input a).length) bound :=
    (((PolyBounded.const 2).mul hcountLenPoly).add (.const 1)).add hsize
  have hroundPoly : PolyBounded (fun a => (input a).length) roundTime :=
    PolyBounded.comp (size' := id) (v := fun n => cB * (n + 1) ^ dB)
      (.of_forall_le cB dB fun _ => le_rfl) hboundPoly
  have htePoly : PolyBounded (fun a => (input a).length) te :=
    PolyBounded.comp (size' := id) (v := fun n => ce * (n + 1) ^ de)
      (.of_forall_le ce de fun _ => le_rfl) hboundPoly
  have hprepSpacePoly : PolyBounded (fun a => (input a).length) prepSpace :=
    (PolyBounded.const kp).mul (((PolyBounded.const 2).mul htpPoly).add (.const 1))
  have hloopSpacePoly : PolyBounded (fun a => (input a).length) loopSpace :=
    (PolyBounded.const (kB + 1 + 2)).mul
      (((PolyBounded.const 2).mul
        ((hroundPoly.add ((PolyBounded.const 10).mul hboundPoly)).add (.const 22))).add (.const 1))
  have hmidSpacePoly : PolyBounded (fun a => (input a).length) midSpace :=
    (PolyBounded.const ((kB + 1 + 2) + kp + 2)).mul
      (((PolyBounded.const 2).mul
        (PolyBounded.max (PolyBounded.max hprepSpacePoly hloopSpacePoly)
          (hboundPoly.add (.const 2)))).add (.const 1))
  have hextSpacePoly : PolyBounded (fun a => (input a).length) extSpace :=
    (PolyBounded.const ke).mul (((PolyBounded.const 2).mul htePoly).add (.const 1))
  have hfullSpacePoly : PolyBounded (fun a => (input a).length) fullSpace :=
    (PolyBounded.const (ke + kMid + 2)).mul
      (((PolyBounded.const 2).mul
        (PolyBounded.max (PolyBounded.max hmidSpacePoly hextSpacePoly)
          (hboundPoly.add (.const 2)))).add (.const 1))
  let polyFactor (a : α) : ℕ :=
    4 * tp a + 4 * (roundTime a + 10 * bound a + 23) + 16 * bound a + te a + 46
  have hpolyFactor : PolyBounded (fun a => (input a).length) polyFactor :=
    (((((PolyBounded.const 4).mul htpPoly).add
      ((PolyBounded.const 4).mul
        ((hroundPoly.add ((PolyBounded.const 10).mul hboundPoly)).add (.const 23)))).add
      ((PolyBounded.const 16).mul hboundPoly)).add htePoly).add (.const 46)
  exact ExpIterateInternal.exists_envelope_closed fullM input count fullTime fullSpace polyFactor
    (fun a => (ProbComp.eval (OracleComp.iterate (count a) step (initial a))).map stateEncoding)
    hpolyFactor hfullSpacePoly
    (fun a => by
      dsimp only [fullTime, midTime, loopTime, polyFactor]
      have : 1 ≤ count a + 1 := Nat.succ_pos _
      nlinarith)
    (fun a => by
      obtain ⟨hhalt_raw, heval_raw, hspace_raw⟩ := hfullM a
      refine ⟨hhalt_raw, ?_, hspace_raw⟩
      rw [heval_raw]
      dsimp only [μLoop]
      rw [PMF.bind_map]
      congr 1 with final : 1
      dsimp only [Function.comp_def]
      rw [hdecodeOut])

/-- **Captured-input binary-counter iteration in polynomial workspace.** The loop step may capture
the original input `a : α`. -/
theorem IsPPTOn.exists_multiTapePTM_iterateWith_binary {initial : α → σ} {count : α → ℕ}
    {step : α → σ → ProbComp σ}
    (hcount : ComputableInPolyTime count input encNat)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : IsPPTOn (encPair input stateEncoding) stateEncoding (fun pair => step pair.1 pair.2))
    (invariant : α → ℕ → σ → Prop) (hbase : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a i state, i < count a → invariant a i state →
      ∀ next ∈ (ProbComp.eval (step a state)).support, invariant a (i + 1) next)
    {size : α → ℕ} (hsize : PolyBounded (fun a => (input a).length) size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state →
      (stateEncoding state).length ≤ size a) :
    (∃ (K : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM K Bool Control) (C E : ℕ),
      ∀ a,
        let T := C * ((count a + 1) * ((input a).length + 1) ^ E)
        let S := C * ((input a).length + 1) ^ E
        (∀ final ∈ (ProbComp.eval
            (machine.runClosedConfigFrom T (machine.initialConfig (input a)))).support,
            final.tapes.state = none) ∧
          ProbComp.eval (machine.runClosed T (input a)) =
            (ProbComp.eval (OracleComp.iterate (count a) (step a) (initial a))).map stateEncoding ∧
          machine.toNTM.RunsInSpace (input a) S) ∧
      ∀ a state,
        state ∈ (ProbComp.eval (OracleComp.iterate (count a) (step a) (initial a))).support →
        invariant a (count a) state := by
  classical
  have hinv_final : ∀ a state,
      state ∈ (ProbComp.eval (OracleComp.iterate (count a) (step a) (initial a))).support →
      invariant a (count a) state :=
    fun a => ProbComp.iterate_invariant (count a) (step a) (initial a) (invariant a) (hbase a)
      (fun i hi state hs => hpreserve a i state hi hs)
  refine ⟨?_, hinv_final⟩
  let packedEnc : α × σ ↪ List Bool := encPair input stateEncoding
  let packedStep (pair : α × σ) : ProbComp (α × σ) :=
    (fun next => (pair.1, next)) <$> step pair.1 pair.2
  have hpackedStep : IsPPTOn packedEnc packedEnc packedStep :=
    hstep.pair (ComputableInPolyTime.fst input stateEncoding).tidy
  obtain ⟨⟨kM, Mid, hfinM, midM, cM, eM, hmidM⟩, -⟩ :=
    IsPPTOn.exists_multiTapePTM_iterate_binary hcount
      (ComputableInPolyTime.id'.prod hinitial) hpackedStep
      (fun a i pair => pair.1 = a ∧ invariant a i pair.2) (fun a => ⟨rfl, hbase a⟩)
      (by
        rintro a i ⟨captured, state⟩ hi ⟨rfl, hstate⟩ next hnext
        rw [ProbComp.eval_map, PMF.mem_support_map_iff] at hnext
        obtain ⟨val, hval, rfl⟩ := hnext
        exact ⟨rfl, hpreserve captured i state hi hstate val hval⟩)
      (size := fun a => 2 * (input a).length + 1 + size a)
      ((((PolyBounded.const 2).mul .self).add (.const 1)).add hsize)
      (by
        rintro a i ⟨captured, state⟩ hi ⟨rfl, hstate⟩
        have := hbound captured i state hi hstate
        enc_len)
  obtain ⟨_, ke, Extract, hfinE, extM, ce, de, hextM⟩ :=
    IsTidyOraclePPTOn.of_computableInPolyTime (Operation := Empty)
      ((ComputableInPolyTime.of_eq (encIn := stateEncoding) (encOut := encBits)
        (f := stateEncoding) fun _ => rfl).comp (ComputableInPolyTime.snd input stateEncoding))
  let outBound (a : α) : ℕ := 2 * (input a).length + 1 + size a
  let te (a : α) : ℕ := ce * (outBound a + 1) ^ de
  let midTime (a : α) : ℕ := cM * ((count a + 1) * ((input a).length + 1) ^ eM)
  let midSpace (a : α) : ℕ := cM * ((input a).length + 1) ^ eM
  let extSpace (a : α) : ℕ := ke * (2 * te a + 1)
  let μMid (a : α) : PMF (List Bool) :=
    (ProbComp.eval (OracleComp.iterate (count a) (step a) (initial a))).map
      (fun s => packedEnc (a, s))
  have hmid_eval_eq (a : α) : ProbComp.eval (midM.runClosed (midTime a) (input a)) = μMid a := by
    have hiter_map : OracleComp.iterate (count a) packedStep (a, initial a) =
        (fun s => (a, s)) <$> OracleComp.iterate (count a) (step a) (initial a) :=
      OracleComp.iterate_map (count a) (step a) packedStep (fun s => (a, s))
        (fun _ => rfl) (initial a)
    rw [(hmidM a).2.1, hiter_map, ProbComp.eval_map, PMF.map_comp]
    rfl
  have hμMid_mem (a : α) (w : List Bool) (hw : w ∈ (μMid a).support) :
      ∃ final ∈ (ProbComp.eval (OracleComp.iterate (count a) (step a) (initial a))).support,
        w = packedEnc (a, final) ∧ w.length ≤ outBound a := by
    rw [PMF.mem_support_map_iff] at hw
    obtain ⟨final, hfinal, rfl⟩ := hw
    refine ⟨final, hfinal, rfl, ?_⟩
    have hs := hbound a (count a) final le_rfl (hinv_final a final hfinal)
    enc_len [packedEnc, outBound]
  have hext_on (a : α) (final : σ) (hlen : (packedEnc (a, final)).length ≤ outBound a) :
      extM.ComputesTidily (packedEnc (a, final)) (te a)
        (ProbOracleComp.sample (pure (stateEncoding final))) := by
    have h0 : extM.ComputesTidily (packedEnc (a, final))
        (ce * ((packedEnc (a, final)).length + 1) ^ de)
        (ProbOracleComp.sample (pure (stateEncoding final))) := by
      simpa only [encBits, Function.Embedding.coe_refl, id_eq, map_pure, Function.comp_apply,
        ProbOracleComp.sample_pure] using hextM (a, final)
    exact h0.mono (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) de))
  let decodePacked : List Bool → List Bool :=
    Function.extend packedEnc (fun p => stateEncoding p.2) (fun _ => [])
  have hdecodePacked (a : α) (final : σ) :
      decodePacked (packedEnc (a, final)) = stateEncoding final :=
    packedEnc.injective.extend_apply (fun p => stateEncoding p.2) (fun _ => []) (a, final)
  obtain ⟨kFull, FullControl, hfinFull, fullM, hfullM⟩ :=
    ExpIterateInternal.exists_comp_closed midM extM
      input midTime te midSpace extSpace outBound
      μMid (fun _ w => PMF.pure (decodePacked w))
      (fun a => (hmidM a).1)
      hmid_eval_eq
      (fun a => (hmidM a).2.2)
      (fun a w hw => (hμMid_mem a w hw).choose_spec.2.2)
      (fun a w hw => by
        obtain ⟨final, _, rfl, hlen⟩ := hμMid_mem a w hw
        exact ExpIterateInternal.halted_of_computesTidily (hext_on a final hlen))
      (fun a w hw => by
        obtain ⟨final, _, rfl, hlen⟩ := hμMid_mem a w hw
        rw [ExpIterateInternal.eval_runClosed_of_computesTidily (hext_on a final hlen),
          ProbComp.eval_pure, hdecodePacked])
      (fun a w hw => by
        obtain ⟨final, _, rfl, hlen⟩ := hμMid_mem a w hw
        exact ExpIterateInternal.runsInSpace_toNTM_of_computesTidily (hext_on a final hlen))
  let fullTime (a : α) : ℕ := midTime a + (midTime a + 4 + te a)
  let fullSpace (a : α) : ℕ :=
    (ke + kM + 2) * (2 * max (max (midSpace a) (extSpace a)) (outBound a + 2) + 1)
  have houtPoly : PolyBounded (fun a => (input a).length) outBound :=
    (((PolyBounded.const 2).mul .self).add (.const 1)).add hsize
  have htePoly : PolyBounded (fun a => (input a).length) te :=
    PolyBounded.comp (size' := id) (v := fun n => ce * (n + 1) ^ de)
      (.of_forall_le ce de fun _ => le_rfl) houtPoly
  have hmidSpacePoly : PolyBounded (fun a => (input a).length) midSpace :=
    .of_forall_le cM eM fun _ => le_rfl
  have hextSpacePoly : PolyBounded (fun a => (input a).length) extSpace :=
    (PolyBounded.const ke).mul (((PolyBounded.const 2).mul htePoly).add (.const 1))
  have hfullSpacePoly : PolyBounded (fun a => (input a).length) fullSpace :=
    (PolyBounded.const (ke + kM + 2)).mul
      (((PolyBounded.const 2).mul
        (PolyBounded.max (PolyBounded.max hmidSpacePoly hextSpacePoly)
          (houtPoly.add (.const 2)))).add (.const 1))
  let polyFactor (a : α) : ℕ := 2 * midSpace a + te a + 4
  have hpolyFactor : PolyBounded (fun a => (input a).length) polyFactor :=
    (((PolyBounded.const 2).mul hmidSpacePoly).add htePoly).add (.const 4)
  exact ExpIterateInternal.exists_envelope_closed fullM input count fullTime fullSpace polyFactor
    (fun a => (ProbComp.eval (OracleComp.iterate (count a) (step a) (initial a))).map stateEncoding)
    hpolyFactor hfullSpacePoly
    (fun a => by
      dsimp only [fullTime, midTime, midSpace, polyFactor]
      have : 1 ≤ count a + 1 := Nat.succ_pos _
      nlinarith)
    (fun a => by
      obtain ⟨hhalt_raw, heval_raw, hspace_raw⟩ := hfullM a
      refine ⟨hhalt_raw, ?_, hspace_raw⟩
      rw [heval_raw]
      dsimp only [μMid]
      rw [PMF.bind_map]
      congr 1 with final : 1
      dsimp only [Function.comp_def]
      rw [hdecodePacked])

end BinaryIterate

/-! ### Exponential independent Boolean trial repetition -/

/-- One OR-accumulating trial step: keep `true` once reached, otherwise run `trial`. -/
def repeatAnyStep (trial : ProbComp Bool) (acc : Bool) : ProbComp Bool :=
  if acc then pure true else trial

/-- `r` independent trials fail (`false`) with probability `(1 - p) ^ r`, where
`p = (ProbComp.eval trial true).toReal`. -/
theorem eval_iterate_repeatAnyStep_false_toReal (trial : ProbComp Bool) (r : ℕ) :
    (ProbComp.eval (OracleComp.iterate r (repeatAnyStep trial) false) false).toReal =
      (1 - (ProbComp.eval trial true).toReal) ^ r := by
  induction r with
  | zero =>
    simp only [OracleComp.iterate_zero, ProbComp.eval_pure, PMF.pure_apply_self, ENNReal.toReal_one,
      pow_zero]
  | succ r ih =>
    rw [OracleComp.iterate_succ, ProbComp.eval_bind]
    have hfalse_step : ProbComp.eval (repeatAnyStep trial false) = ProbComp.eval trial := rfl
    have htrue_step : ProbComp.eval (repeatAnyStep trial true) = PMF.pure true := rfl
    have hbind : (ProbComp.eval (OracleComp.iterate r (repeatAnyStep trial) false)).bind
        (fun b => ProbComp.eval (repeatAnyStep trial b)) false =
        ProbComp.eval (OracleComp.iterate r (repeatAnyStep trial) false) false *
          ProbComp.eval trial false := by
      rw [PMF.bind_apply, tsum_fintype]
      simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
        Finset.sum_insert, Finset.sum_singleton, htrue_step, hfalse_step, PMF.pure_apply,
        Bool.false_eq_true, ↓reduceIte, mul_zero, zero_add]
    rw [hbind, ENNReal.toReal_mul, ih, PMF.toReal_false_eq_one_sub (ProbComp.eval trial), pow_succ]

/-- When `trial` has zero probability of returning `true`, `r` repetitions return `false` with
probability `1` (exact distribution `PMF.pure false`). -/
theorem eval_iterate_repeatAnyStep_eq_pure_false (trial : ProbComp Bool) (r : ℕ)
    (hzero : ProbComp.eval trial true = 0) :
    ProbComp.eval (OracleComp.iterate r (repeatAnyStep trial) false) = PMF.pure false := by
  have hpure : ProbComp.eval trial = PMF.pure false := by
    ext b
    cases b with
    | false =>
      have hsum := PMF.tsum_coe (ProbComp.eval trial)
      rw [tsum_fintype] at hsum
      simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
        Finset.sum_insert, Finset.sum_singleton, hzero, zero_add] at hsum
      simp only [PMF.pure_apply_self, hsum]
    | true => simp only [hzero, PMF.pure_apply, Bool.true_eq_false, ↓reduceIte]
  induction r with
  | zero => simp only [OracleComp.iterate_zero, ProbComp.eval_pure]
  | succ r ih =>
    rw [OracleComp.iterate_succ, ProbComp.eval_bind, ih, PMF.pure_bind]
    exact hpure

/-- **Repeating a strict PPT Boolean trial an exponential binary-computable number of times.** Given
`htrial : IsPPTOn input encBool trialProg` and `hcount : ComputableInPolyTime trials input encNat`,
one finite-control fair-coin `MultiTapePTM` halts on every branch within
`C * ((trials a + 1) * ((input a).length + 1) ^ E)` steps, runs in polynomial workspace
`C * ((input a).length + 1) ^ E`, never outputs `[true]` when `trialProg a` has zero probability of
`true`, and outputs `[true]` with probability `1 - (1 - p) ^ (trials a)` where
`p = (ProbComp.eval (trialProg a) true).toReal`. -/
theorem IsPPTOn.exists_multiTapePTM_repeatAnyBool_binary {α : Type} {input : α ↪ List Bool}
    {trialProg : α → ProbComp Bool} {trials : α → ℕ}
    (htrial : IsPPTOn input encBool trialProg)
    (hcount : ComputableInPolyTime trials input encNat) :
    ∃ (K : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM K Bool Control) (C E : ℕ),
      ∀ a,
        let T := C * ((trials a + 1) * ((input a).length + 1) ^ E)
        let S := C * ((input a).length + 1) ^ E
        let μ := ProbComp.eval (OracleComp.iterate (trials a) (repeatAnyStep (trialProg a)) false)
        (∀ final ∈ (ProbComp.eval
            (machine.runClosedConfigFrom T (machine.initialConfig (input a)))).support,
            final.tapes.state = none) ∧
          ProbComp.eval (machine.runClosed T (input a)) = μ.map encBool ∧
          machine.toNTM.RunsInSpace (input a) S := by
  have hstep : IsPPTOn (encPair input encBool) encBool
      (fun pair : α × Bool => repeatAnyStep (trialProg pair.1) pair.2) := by
    refine IsPPTOn.cond' (ComputableInPolyTime.snd input encBool)
      (ComputableInPolyTime.const true).isPPTOn ?_
    exact htrial.preprocess (ComputableInPolyTime.fst input encBool)
  obtain ⟨⟨K, Control, hfin, machine, C, E, hM⟩, -⟩ :=
    IsPPTOn.exists_multiTapePTM_iterateWith_binary
      (initial := fun _ : α => false)
      (count := trials)
      (step := fun a b => repeatAnyStep (trialProg a) b)
      hcount (.const false) hstep
      (fun _ _ _ => True) (fun _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
      (size := fun _ => 1) (.const 1)
      (fun _ _ b _ _ => by cases b <;> exact le_rfl)
  exact ⟨K, Control, hfin, machine, C, E, hM⟩

end Cslib.Probability
