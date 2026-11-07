/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.BlockNetwork
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Deterministic

/-!
# Functional computation on HPV time blocks

A guessed movement schedule determines a bounded-fan-in computation: each interval reads its
predecessor's control record and the last providers of its three-block windows. Its gate replays
one interval and checks the movement of every head, including the input head. Failure propagates
through the mandatory predecessor edge, so a successful final value validates every earlier
movement label.

The definitions use the existing tape windows and configuration embedding. They describe pure
semantics with the original input shared by the local replays; they do not certify native input
access, graph construction or a space bound.

## Main definitions

* `Turing.MultiTapePTM.BlockComputation.gate`: the local interval function, with failure.
* `Turing.MultiTapePTM.BlockComputation.value`: evaluation through earlier providers.

## Main results

* `Turing.MultiTapePTM.BlockComputation.value_final_eq_some_iff`: success validates the complete
  movement schedule and returns the true leaving view.
* `Turing.MultiTapePTM.BlockComputation.value_final_eq_none_iff`: a wrong schedule fails.
* `Turing.MultiTapePTM.BlockComputation.boundary_ofDeterministic`: the native deterministic
  boundary is recovered exactly.

The window reconstruction proof follows the block-network proof by Samuel Schlesinger.

## References

* [R. Williams, *Simulating Time With Square-Root Space*][Williams2025], arXiv v1, §3.2,
  “Functions” and “Finishing”: local replay checks movement labels and propagates FAIL.
  This library construction uses the existing aligned three-block windows and a mandatory
  preceding-control edge; finite bit coding and unfolding into Tree Evaluation are not yet
  supplied here.
-/

public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {State : Type} {input : List Bool}

/-- Replaying fixed coins in the deterministic embedding is the original native run. -/
theorem stepCoins_ofDeterministic (M : MultiTapeTM k Bool State) (coins : List Bool)
    (c : Cfg k Bool State input) :
    (MultiTapePTM.ofDeterministic M).stepCoins coins c = M.runFrom c coins.length := by
  induction coins generalizing c with
  | nil => rfl
  | cons bit coins ih =>
    rw [MultiTapePTM.stepCoins_cons, ih]
    have hstep : ((MultiTapePTM.ofDeterministic M).withCoin bit).toTM.step c = M.step c := by
      cases hs : c.state with
      | none =>
        rw [MultiTapeTM.step_of_halt hs, MultiTapeTM.step_of_halt hs]
      | some state =>
        rw [MultiTapeTM.step_of_state hs, MultiTapeTM.step_of_state hs,
          MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
        rfl
    rw [hstep]
    change M.runFrom (M.step c) coins.length = M.runFrom c (coins.length + 1)
    rw [show coins.length + 1 = 1 + coins.length by omega, M.runFrom_add]
    rfl

end Turing.MultiTapeTM

namespace Turing.MultiTapePTM.BlockComputation

open MultiTapeNTM.ChoiceTable

variable {k q b : ℕ} {State : Type}

/-- One interval's leaving control record and window contents. Failure is represented by an
outer `Option`, rather than identifying it with any valid tape contents. -/
abbrev View (k : ℕ) (State : Type) (b : ℕ) :=
  BlockControl k State b × (Fin k → Fin 3 → ZMod b → Option Bool)

variable (machine : MultiTapePTM k Bool State) (input : List Bool) (b : ℕ) [NeZero b]
  (σ : Schedule k q)

/-- The source value contains the initial control and blank work tapes. -/
@[expose] def initialView : View k State b :=
  ((some machine.initial, 0, .empty), fun _ _ _ => none)

/-- A window block is obtained from its last provider; a block never seen before is blank. -/
@[expose] def enteringWindow (i : Fin q) (providers : Fin k → Fin 3 → Option (View k State b)) :
    Fin k → Fin 3 → ZMod b → Option Bool := fun h d =>
  match lastBefore (InWindow σ h (portBlock σ i h d)) i with
  | none => fun _ => none
  | some j => ((providers h d).getD (initialView machine b)).2 h
      (portOf σ j h (portBlock σ i h d))

open scoped Classical in
/-- The local gate has one control dependency and `3*k` window dependencies. All failed
inputs propagate. The replay checks the movement labels of all work heads and the input head. -/
@[expose] noncomputable def gate (i : Fin q) (previous : Option (View k State b))
    (providers : Fin k → Fin 3 → Option (View k State b)) : Option (View k State b) :=
  previous.bind fun prev =>
    if ∀ h d, (providers h d).isSome then
      let c := machine.stepCoins (List.replicate b false)
        (embedCfg (input := input) b (scheduleBlock σ i) prev.1
          (enteringWindow machine b σ i providers))
      if ∀ head, c.blockIndex b head = scheduleBlock σ i head + σ i head then
        some (c.blockControl b, c.windowContents b (scheduleBlock σ i))
      else none
    else none

/-- The value after `n` intervals. Each recursion follows either the preceding interval or an
older provider. No configuration outside the dependency values is consulted by a local gate. -/
@[expose] noncomputable def value : ℕ → Option (View k State b)
  | 0 => some (initialView machine b)
  | n + 1 =>
    if hi : n < q then
      gate machine input b σ ⟨n, hi⟩ (value n) fun h d =>
        match hp : lastBefore (InWindow σ h (portBlock σ ⟨n, hi⟩ h d)) ⟨n, hi⟩ with
        | none => some (initialView machine b)
        | some j => value (j + 1)
    else none
termination_by n => n
decreasing_by
  · omega
  · have hj := (lastBefore_eq_some_iff.mp hp).1
    change (j : ℕ) < n at hj
    omega

omit [NeZero b] in
/-- The dependency supplying the control record is present even if no work block is needed. -/
theorem gate_none (i : Fin q) (providers : Fin k → Fin 3 → Option (View k State b)) :
    gate machine input b σ i none providers = none := by
  simp [gate]

omit [NeZero b] in
/-- Once an interval fails, the mandatory control dependency propagates failure. -/
theorem value_succ_eq_none {n : ℕ} (h : value machine input b σ n = none) :
    value machine input b σ (n + 1) = none := by
  rw [value]
  split_ifs with hi
  · rw [h, gate_none]
  · rfl

/-- The true run at an interval boundary, with one fixed false coin per step. -/
@[expose] noncomputable def boundary (n : ℕ) : Cfg k Bool State input :=
  machine.intervalStart b (List.replicate (q * b) false) (Cfg.init machine.initial input) n

/-- The true movement schedule for the fixed-coin replay. -/
@[expose] noncomputable def actualSchedule : Schedule k q :=
  machine.schedule b q (List.replicate (q * b) false) (Cfg.init machine.initial input)

/-- Every guessed label before this boundary agrees with the true replay. -/
@[expose] def Prefix (n : ℕ) : Prop :=
  ∀ j : Fin q, j.val < n → actualSchedule machine input b (q := q) j = σ j

/-- The true value left by an interval, retaining its own window rather than the next window. -/
@[expose] noncomputable def trueView : ℕ → View k State b
  | 0 => initialView machine b
  | n + 1 => ((boundary machine input b (q := q) (n + 1)).blockControl b,
      (boundary machine input b (q := q) (n + 1)).windowContents b (scheduleBlock σ n))

omit [NeZero b] in
private theorem boundary_succ {n : ℕ} (hn : n < q) :
    boundary machine input b (q := q) (n + 1) =
      machine.stepCoins (List.replicate b false) (boundary machine input b (q := q) n) := by
  have hmul := Nat.mul_le_mul_right b (Nat.succ_le_of_lt hn)
  simp only [Nat.succ_mul] at hmul
  have hlen : min b (q * b - n * b) = b := by omega
  simp only [boundary, intervalStart_succ, List.drop_replicate, List.take_replicate, hlen]

omit [NeZero b] in
private theorem control_trueView (n : ℕ) :
    (trueView machine input b σ n).1 = (boundary machine input b (q := q) n).blockControl b := by
  cases n with
  | zero =>
    have h : ∀ head : Option (Fin k),
        ((Cfg.init machine.initial input).headPos head : ZMod b) = 0 :=
      fun head => by rw [Cfg.headPos_init, Int.cast_zero]
    simp only [trueView, initialView, boundary, intervalStart_zero, Cfg.blockControl,
      funext h]
    rfl
  | succ n => rfl

private theorem boundary_index {n : ℕ} (hn : n ≤ q) (hσ : Prefix machine input b σ n) :
    (boundary machine input b (q := q) n).blockIndex b = scheduleBlock σ n :=
  machine.blockIndex_intervalStart_eq_scheduleBlock b _ σ hn hσ

omit [NeZero b] in
/-- The initial boundary contains blank work tapes. -/
private theorem boundary_zero_cell (h : Fin k) (z : ℤ) :
    (boundary machine input b (q := q) 0).workTapes h z = none := by
  simp [boundary]

/-- A block outside the three aligned windows contains no cell of that window. -/
private theorem outside_window {c : Cfg k Bool State input} {h : Fin k} {j : ℤ}
    (hj : ¬ |c.blockIndex b (some h) - j| ≤ 1) (r : ZMod b) :
    b * j + (r.val : ℤ) ∉ c.blockWindow b h := by
  have hb : (0 : ℤ) < b := by exact_mod_cast Nat.pos_of_neZero b
  have hr : (r.val : ℤ) < b := by exact_mod_cast ZMod.val_lt r
  have hr0 : (0 : ℤ) ≤ r.val := by positivity
  simp only [Cfg.blockIndex, Cfg.headPos_some, abs_le, not_and_or, not_le] at hj
  simp only [Cfg.blockWindow, Set.mem_Ico, not_and_or, not_le, not_lt]
  rcases hj with hj | hj
  · right
    nlinarith
  · left
    nlinarith

/-- Last providers reconstruct the actual entering window whenever all prior labels agree. -/
private theorem enteringWindow_true (i : Fin q) (hσ : Prefix machine input b σ i)
    (providers : Fin k → Fin 3 → Option (View k State b))
    (hp : ∀ h d j, lastBefore (InWindow σ h (portBlock σ i h d)) i = some j →
      providers h d = some (trueView machine input b σ (j + 1))) :
    enteringWindow machine b σ i providers =
      (boundary machine input b (q := q) i).windowContents b (scheduleBlock σ i) := by
  have hindex (j : ℕ) (hj : j ≤ i) :
      (boundary machine input b (q := q) j).blockIndex b = scheduleBlock σ j :=
    boundary_index machine input b σ (by omega) (fun j' hj' => hσ j' (by omega))
  funext h d r
  set z := portBlock σ i h d
  have huntouched (j : ℕ) (hj : j ≤ i)
      (hnot : ∀ j' : Fin q, j ≤ j' → j' < i → ¬ InWindow σ h z j') :
      (boundary machine input b (q := q) i).workTapes h (b * z + r.val) =
        (boundary machine input b (q := q) j).workTapes h (b * z + r.val) := by
    refine machine.workTapes_intervalStart_eq_of_notMem_blockWindow (Nat.pos_of_neZero b)
      _ _ hj fun j' hj' hj'i => outside_window (input := input) (b := b) ?_ r
    change ¬ |(boundary machine input b (q := q) j').blockIndex b (some h) - z| ≤ 1
    rw [hindex j' hj'i.le]
    exact hnot ⟨j', by omega⟩ hj' hj'i
  change enteringWindow machine b σ i providers h d r =
    (boundary machine input b (q := q) i).workTapes h (b * z + r.val)
  unfold enteringWindow
  cases hlast : lastBefore (InWindow σ h (portBlock σ i h d)) i with
  | none =>
    simp only
    rw [huntouched 0 (Nat.zero_le _) (fun j _ hj => lastBefore_eq_none_iff.mp hlast j hj),
      boundary_zero_cell]
  | some j =>
    obtain ⟨hji, hin, hbetween⟩ := lastBefore_eq_some_iff.mp hlast
    rw [hp h d j hlast]
    simp only [Option.getD_some, trueView]
    rw [huntouched (j + 1) (by omega) (fun j' hj' hj'i => hbetween j' (by omega) hj'i)]
    change (boundary machine input b (q := q) (j + 1)).workTapes h
      (b * portBlock σ j h (portOf σ j h z) + r.val) = _
    rw [portBlock_portOf hin]

omit [NeZero b] in
private theorem gate_eq_some_iff (i : Fin q) (prev v : View k State b)
    (providers : Fin k → Fin 3 → Option (View k State b)) :
    gate machine input b σ i (some prev) providers = some v ↔
      (∀ h d, (providers h d).isSome) ∧
        machine.IntervalStep b input (scheduleBlock σ i) (σ i) prev.1
          (enteringWindow machine b σ i providers) (List.replicate b false) v.1 v.2 := by
  classical
  simp only [gate, Option.bind_some]
  split_ifs with hproviders hmove <;>
    simp_all [IntervalStep, Prod.ext_iff]

omit [NeZero b] in
private theorem sign_cast_injective : Function.Injective (fun s : SignType => (s : ℤ)) := by
  intro s t h
  cases s <;> cases t <;> first | rfl | (simp at h)

private theorem move_iff (i : Fin q) :
    (∀ head, (boundary machine input b (q := q) (i + 1)).blockIndex b head =
      (boundary machine input b (q := q) i).blockIndex b head + σ i head) ↔
      actualSchedule machine input b (q := q) i = σ i := by
  rw [funext_iff]
  refine forall_congr' fun head => ?_
  have h := machine.coe_schedule (Nat.pos_of_neZero b) q (List.replicate (q * b) false)
    (Cfg.init machine.initial input) i head
  change ((actualSchedule machine input b (q := q) i head : SignType) : ℤ) =
    (boundary machine input b (q := q) (i + 1)).blockIndex b head -
      (boundary machine input b (q := q) i).blockIndex b head at h
  constructor
  · intro hm
    have heq : (actualSchedule machine input b (q := q) i head : ℤ) = σ i head := by omega
    exact sign_cast_injective heq
  · intro hs
    rw [hs] at h
    omega

private theorem gate_true (i : Fin q) (hσ : Prefix machine input b σ i)
    (providers : Fin k → Fin 3 → Option (View k State b))
    (hproviders : ∀ h d, (providers h d).isSome)
    (hp : ∀ h d j, lastBefore (InWindow σ h (portBlock σ i h d)) i = some j →
      providers h d = some (trueView machine input b σ (j + 1)))
    (v : View k State b) :
    gate machine input b σ i (some (trueView machine input b σ i)) providers = some v ↔
      actualSchedule machine input b (q := q) i = σ i ∧
        v = trueView machine input b σ (i + 1) := by
  rw [gate_eq_some_iff, and_iff_right hproviders, control_trueView,
    enteringWindow_true machine input b σ i hσ providers hp]
  have hindex := boundary_index machine input b σ i.isLt.le hσ
  rw [← hindex, machine.intervalStep_view_iff b _ (by simp),
    ← boundary_succ machine input b i.isLt, move_iff]
  rw [hindex]
  change (_ = v.1 ∧ _ = v.2 ∧ _) ↔ _ ∧ v = (_, _)
  constructor
  · rintro ⟨hc, hw, hm⟩
    exact ⟨hm, Prod.ext hc.symm hw.symm⟩
  · rintro ⟨hm, rfl⟩
    exact ⟨rfl, rfl, hm⟩

/-- A successful interval value is exactly the true leaving view, and validates every movement
label in its prefix. In particular, success at the root validates all earlier labels. -/
theorem value_eq_some_iff {n : ℕ} (hn : n ≤ q) (v : View k State b) :
    value machine input b σ n = some v ↔
      Prefix machine input b σ n ∧ v = trueView machine input b σ n := by
  induction n using Nat.strong_induction_on generalizing v with
  | ind n ih =>
    cases n with
    | zero => simp [value, Prefix, trueView, eq_comm]
    | succ n =>
      have hnq : n < q := by omega
      let i : Fin q := ⟨n, hnq⟩
      let providers : Fin k → Fin 3 → Option (View k State b) := fun h d =>
        match hp : lastBefore (InWindow σ h (portBlock σ i h d)) i with
        | none => some (initialView machine b)
        | some j => value machine input b σ (j + 1)
      rw [value, dite_eq_left hnq]
      change gate machine input b σ i (value machine input b σ n) providers = some v ↔ _
      have hprev := ih n (by omega) (by omega)
      by_cases hσ : Prefix machine input b σ n
      · have hvn : value machine input b σ n = some (trueView machine input b σ n) :=
          (hprev _).mpr ⟨hσ, rfl⟩
        have hp h d j (hj : lastBefore (InWindow σ h (portBlock σ i h d)) i = some j) :
            providers h d = some (trueView machine input b σ (j + 1)) := by
          have hji := (lastBefore_eq_some_iff.mp hj).1
          change (j : ℕ) < n at hji
          have hvj := ih (j + 1) (by omega) (by omega)
            (trueView machine input b σ (j + 1))
          dsimp only [providers]
          split
          next he =>
            have hc := he.symm.trans hj
            cases hc
          next j' he =>
            have heq : j' = j := Option.some.inj (he.symm.trans hj)
            subst j'
            exact hvj.mpr ⟨fun j' hj' => hσ j' (by omega), rfl⟩
        have hproviders h d : (providers h d).isSome := by
          cases hj : lastBefore (InWindow σ h (portBlock σ i h d)) i with
          | none =>
            dsimp only [providers]
            split
            next => rfl
            next j he =>
              have hc := hj.symm.trans he
              cases hc
          | some j => rw [hp h d j hj]; rfl
        rw [hvn, gate_true machine input b σ i hσ providers hproviders hp]
        have hprefix : Prefix machine input b σ (n + 1) ↔
            actualSchedule machine input b (q := q) i = σ i := by
          constructor
          · exact fun h => h i (by simp [i])
          · intro h j hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
            · exact hσ j hj
            · have heq : j = i := Fin.ext hj
              simpa only [heq] using h
        rw [hprefix]
      · have hvn : value machine input b σ n = none := by
          cases hv : value machine input b σ n with
          | none => rfl
          | some w => exact False.elim (hσ ((hprev w).mp hv).1)
        rw [hvn, gate_none]
        constructor
        · intro h
          cases h
        · rintro ⟨hp, -⟩
          exact False.elim (hσ (fun j hj => hp j (by omega)))

/-- At the final boundary, every guessed label has been validated. -/
theorem value_final_eq_some_iff (v : View k State b) :
    value machine input b σ q = some v ↔
      actualSchedule machine input b (q := q) = σ ∧ v = trueView machine input b σ q := by
  rw [value_eq_some_iff machine input b σ le_rfl]
  have hprefix : Prefix machine input b σ q ↔ actualSchedule machine input b (q := q) = σ := by
    constructor
    · intro h
      funext j
      exact h j j.isLt
    · intro h j _
      exact congrFun h j
  rw [hprefix]

/-- A wrong complete movement guess fails at the final boundary. -/
theorem value_final_eq_none_iff :
    value machine input b σ q = none ↔ actualSchedule machine input b (q := q) ≠ σ := by
  constructor
  · intro hfail heq
    have hgood := (value_final_eq_some_iff machine input b σ
      (trueView machine input b σ q)).mpr ⟨heq, rfl⟩
    rw [hfail] at hgood
    cases hgood
  · intro hwrong
    cases hv : value machine input b σ q with
    | none => rfl
    | some v =>
      exact False.elim (hwrong ((value_final_eq_some_iff machine input b σ v).mp hv).1)

omit [NeZero b] in
/-- The fixed-coin boundaries of a deterministic embedding are the native machine boundaries. -/
theorem boundary_ofDeterministic (M : MultiTapeTM k Bool State) {n : ℕ} (hn : n ≤ q) :
    boundary (ofDeterministic M) input b (q := q) n =
      M.runFrom (Cfg.init M.q₀ input) (n * b) := by
  rw [boundary, intervalStart, MultiTapeTM.stepCoins_ofDeterministic]
  simp only [List.length_take, List.length_replicate,
    Nat.min_eq_left (Nat.mul_le_mul_right b hn)]
  rfl

end Turing.MultiTapePTM.BlockComputation
