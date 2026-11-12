/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.StateSimulation
public import Mathlib.Tactic.FinCases

/-!
# Native finite-control evaluation of a seven-input Boolean table

Seven existential transitions guess the inputs of a fixed Boolean operation. The operation is
checked in finite control. Three universal transitions choose an input whose claim is passed
to a native continuation machine; the eighth branch accepts without a query. No tape, cursor,
or input head is touched before continuation. The operation has fixed arity seven, so its truth
table is part of the finite machine, independent of any streamed query address or word width.
-/

public section

namespace Turing.MultiTapeATM.TruthTable

/-- Finite control for seven guesses, three universal choices, and a native continuation. -/
inductive State (S : Type) where
  | guess₀
  | guess₁ (a : Bool)
  | guess₂ (a b : Bool)
  | guess₃ (a b c : Bool)
  | guess₄ (a b c d : Bool)
  | guess₅ (a b c d e : Bool)
  | guess₆ (a b c d e f : Bool)
  | choose₀ (v : Fin 7 → Bool)
  | choose₁ (v : Fin 7 → Bool) (a : Bool)
  | choose₂ (v : Fin 7 → Bool) (a b : Bool)
  | child (port : Fin 7) (claim : Bool) (state : S)
  deriving Fintype

variable {k : ℕ} {S : Type}

/-- The three universal bits enumerate eight choices in binary order. -/
@[expose] def portCode (a b c : Bool) : Fin 8 :=
  ⟨4 * a.toNat + 2 * b.toNat + c.toNat, by cases a <;> cases b <;> cases c <;> decide⟩

/-- A control-only transition, optionally emitting one result bit. -/
@[expose] def jump (q : Option (State S)) (out : Option Bool := none) : Action k Bool (State S) :=
  ⟨0, fun _ => (none, 0), out, q⟩

/-- Native transition table for the fixed-arity guessing and port-selection phases. -/
@[expose] def tr (g : (Fin 7 → Bool) → Bool) (claim : Bool)
    (child : Fin 7 → Bool → MultiTapeATM k Bool S) (move : Bool) :
    State S → Option Bool → (Fin k → Option Bool) → Action k Bool (State S)
  | .guess₀, _, _ => jump (some (.guess₁ move))
  | .guess₁ a, _, _ => jump (some (.guess₂ a move))
  | .guess₂ a b, _, _ => jump (some (.guess₃ a b move))
  | .guess₃ a b c, _, _ => jump (some (.guess₄ a b c move))
  | .guess₄ a b c d, _, _ => jump (some (.guess₅ a b c d move))
  | .guess₅ a b c d e, _, _ => jump (some (.guess₆ a b c d e move))
  | .guess₆ a b c d e f, _, _ =>
    let v := ![a, b, c, d, e, f, move]
    jump (if g v = claim then some (.choose₀ v) else none)
  | .choose₀ v, _, _ => jump (some (.choose₁ v move))
  | .choose₁ v a, _, _ => jump (some (.choose₂ v a move))
  | .choose₂ v a b, _, _ =>
    let j := portCode a b move
    if h : j.val < 7 then
      let p : Fin 7 := ⟨j.val, h⟩
      jump (some (.child p (v p) (child p (v p)).toPTM.toNTM.q₀))
    else jump none (some true)
  | .child p bit q, input, work =>
    let a := (child p bit).action q input work move
    { a with state := a.state.map (.child p bit) }

/-- Alternating player of each control state and its continuation. -/
@[expose] def universal (child : Fin 7 → Bool → MultiTapeATM k Bool S) : State S → Bool
  | .choose₀ _ | .choose₁ _ _ | .choose₂ _ _ _ => true
  | .child p b q => (child p b).universal q
  | _ => false

/-- One fixed seven-input truth table followed by a native continuation for the selected input.
The two transitions of every guessing/choice state preserve all work storage and head positions. -/
@[expose] noncomputable def machine (g : (Fin 7 → Bool) → Bool) (claim : Bool)
    (child : Fin 7 → Bool → MultiTapeATM k Bool S) : MultiTapeATM k Bool (State S) :=
  ofTMs (fun b => MultiTapeTM.ofTr .guess₀ (tr g claim child b)) (universal child)

variable (g : (Fin 7 → Bool) → Bool) (claim : Bool)
  (child : Fin 7 → Bool → MultiTapeATM k Bool S)

private theorem next_child {input : List Bool} (p : Fin 7) (bit move : Bool)
    (cfg : Cfg k Bool S input) :
    (machine g claim child).next move (cfg.mapState (Option.map (.child p bit))) =
      ((child p bit).next move cfg).mapState (Option.map (.child p bit)) := by
  cases hs : cfg.state with
  | none =>
    rw [next_of_halted _ (by simp [hs]), next_of_halted _ hs]
  | some q =>
    rw [machine, next_ofTMs, MultiTapeTM.step_of_state (q := State.child p bit q) (by simp [hs]),
      MultiTapeTM.tr_ofTr, next_of_state _ hs]
    rfl

private def childSimulation (p : Fin 7) (bit : Bool) :
    StateSimulation (child p bit) (machine g claim child) where
  stateMap := .child p bit
  universal_eq _ := rfl
  next_eq cfg move := next_child g claim child p bit move cfg

/-- Once selected, the continuation has exactly its original alternating semantics. -/
theorem acceptsWithin_child {input : List Bool} (p : Fin 7) (bit : Bool)
    (n : ℕ) (cfg : Cfg k Bool S input) :
    (machine g claim child).AcceptsWithin n (cfg.mapState (Option.map (.child p bit))) ↔
      (child p bit).AcceptsWithin n cfg :=
  (childSimulation g claim child p bit).acceptsWithin_iff n cfg

private theorem acceptsWithin_child_start {input : List Bool} (p : Fin 7) (bit : Bool)
    (n : ℕ) (cfg : Cfg k Bool S input) :
    (machine g claim child).AcceptsWithin n
      (cfg.withState (some (.child p bit (child p bit).toPTM.toNTM.q₀))) ↔
      (child p bit).AcceptsWithin n (cfg.withState (some (child p bit).toPTM.toNTM.q₀)) := by
  exact acceptsWithin_child g claim child p bit n
    (cfg.withState (some (child p bit).toPTM.toNTM.q₀))

private theorem next_control {input : List Bool} (cfg : Cfg k Bool S input)
    (q q' : State S) (b : Bool)
    (h : ∀ inp work, tr g claim child b q inp work = jump (some q')) :
    (machine g claim child).next b (cfg.withState (some q)) = cfg.withState (some q') := by
  rw [machine, next_ofTMs, MultiTapeTM.step_of_state rfl, MultiTapeTM.tr_ofTr, h]
  simp [jump, Action.apply, Cfg.withState]

private theorem acceptsWithin_choose {input : List Bool} (n : ℕ)
    (cfg : Cfg k Bool S input) (hout : cfg.output = []) (v : Fin 7 → Bool) :
    (machine g claim child).AcceptsWithin (n + 3) (cfg.withState (some (.choose₀ v))) ↔
      ∀ p, (child p (v p)).AcceptsWithin n
        (cfg.withState (some (child p (v p)).toPTM.toNTM.q₀)) := by
  rw [acceptsWithin_succ_of_universal _ rfl rfl]
  have h₀ (b : Bool) := next_control g claim child cfg (.choose₀ v) (.choose₁ v b) b
    (by intros; rfl)
  simp only [h₀]
  have hu₁ (a : Bool) :
      (machine g claim child).AcceptsWithin (n + 2) (cfg.withState (some (.choose₁ v a))) ↔
        ∀ b, (machine g claim child).AcceptsWithin (n + 1)
          ((machine g claim child).next b (cfg.withState (some (.choose₁ v a)))) :=
    acceptsWithin_succ_of_universal _ rfl rfl
  simp only [hu₁]
  have h₁ (a b : Bool) := next_control g claim child cfg (.choose₁ v a) (.choose₂ v a b) b
    (by intros; rfl)
  have hu₂ (a b : Bool) :
      (machine g claim child).AcceptsWithin (n + 1) (cfg.withState (some (.choose₂ v a b))) ↔
        ∀ c, (machine g claim child).AcceptsWithin n
          ((machine g claim child).next c (cfg.withState (some (.choose₂ v a b)))) :=
    acceptsWithin_succ_of_universal _ rfl rfl
  simp only [h₁, hu₂]
  have hend (a b c : Bool) :
      (machine g claim child).AcceptsWithin n
        ((machine g claim child).next c (cfg.withState (some (.choose₂ v a b)))) ↔
        if h : (portCode a b c).val < 7 then
          (child ⟨(portCode a b c).val, h⟩ (v ⟨(portCode a b c).val, h⟩)).AcceptsWithin n
            (cfg.withState (some
              (child ⟨(portCode a b c).val, h⟩ (v ⟨(portCode a b c).val, h⟩)).toPTM.toNTM.q₀))
        else True := by
    by_cases hp : (portCode a b c).val < 7
    · rw [next_control g claim child cfg (.choose₂ v a b)
        (.child ⟨(portCode a b c).val, hp⟩ (v ⟨(portCode a b c).val, hp⟩)
          (child ⟨(portCode a b c).val, hp⟩ (v ⟨(portCode a b c).val, hp⟩)).toPTM.toNTM.q₀)
        c (by intros; simp [tr, hp])]
      simpa only [hp, ↓reduceDIte] using
        acceptsWithin_child_start g claim child ⟨(portCode a b c).val, hp⟩
          (v ⟨(portCode a b c).val, hp⟩) n cfg
    · have hn : (machine g claim child).next c (cfg.withState (some (.choose₂ v a b))) =
          { cfg.withState none with output := [true] } := by
        rw [machine, next_ofTMs, MultiTapeTM.step_of_state rfl, MultiTapeTM.tr_ofTr]
        simp [tr, hp, jump, Action.apply, Cfg.withState, hout]
      rw [hn, acceptsWithin_of_halted _ rfl]
      simp [hp]
  simp only [hend]
  constructor
  · intro h p
    fin_cases p
    · simpa [portCode] using h false false false
    · simpa [portCode] using h false false true
    · simpa [portCode] using h false true false
    · simpa [portCode] using h false true true
    · simpa [portCode] using h true false false
    · simpa [portCode] using h true false true
    · simpa [portCode] using h true true false
  · intro h a b c
    split
    · exact h _
    · trivial

private theorem acceptsWithin_control {input : List Bool} (cfg : Cfg k Bool S input)
    (q : State S) (qs : Bool → State S) (n : ℕ)
    (hq : (machine g claim child).universal q = false)
    (h : ∀ b inp work, tr g claim child b q inp work = jump (some (qs b))) :
    (machine g claim child).AcceptsWithin (n + 1) (cfg.withState (some q)) ↔
      ∃ b, (machine g claim child).AcceptsWithin n (cfg.withState (some (qs b))) := by
  rw [acceptsWithin_succ_of_existential _ rfl hq]
  simp only [next_control g claim child cfg q (qs _) _ (h _)]

private theorem acceptsWithin_guess₆ {input : List Bool} (cfg : Cfg k Bool S input)
    (hout : cfg.output = []) (n : ℕ) (a b c d e f : Bool) :
    (machine g claim child).AcceptsWithin (n + 4)
      (cfg.withState (some (.guess₆ a b c d e f))) ↔
      ∃ bit, g ![a, b, c, d, e, f, bit] = claim ∧
        ∀ p, (child p (![a, b, c, d, e, f, bit] p)).AcceptsWithin n
          (cfg.withState (some (child p (![a, b, c, d, e, f, bit] p)).toPTM.toNTM.q₀)) := by
  rw [acceptsWithin_succ_of_existential _ rfl rfl]
  apply exists_congr
  intro bit
  by_cases hg : g ![a, b, c, d, e, f, bit] = claim
  · rw [next_control g claim child cfg (.guess₆ a b c d e f)
      (.choose₀ ![a, b, c, d, e, f, bit]) bit (by intros; simp [tr, hg])]
    rw [acceptsWithin_choose g claim child n cfg hout]
    simp only [hg, true_and]
  · have hn : (machine g claim child).next bit
        (cfg.withState (some (.guess₆ a b c d e f))) = cfg.withState none := by
      rw [machine, next_ofTMs, MultiTapeTM.step_of_state rfl, MultiTapeTM.tr_ofTr]
      simp [tr, hg, jump, Action.apply, Cfg.withState]
    rw [hn, acceptsWithin_of_halted _ rfl]
    simp [hout, hg]

/-- The native macro realizes the existential truth-table check followed by universal child
verification, with ten charged transitions before the selected continuation. -/
theorem acceptsWithin_iff {input : List Bool} (n : ℕ) (cfg : Cfg k Bool S input)
    (hout : cfg.output = []) :
    (machine g claim child).AcceptsWithin (n + 10) (cfg.withState (some .guess₀)) ↔
      ∃ v : Fin 7 → Bool, g v = claim ∧
        ∀ p, (child p (v p)).AcceptsWithin n
          (cfg.withState (some (child p (v p)).toPTM.toNTM.q₀)) := by
  have hprefix :
      (machine g claim child).AcceptsWithin (n + 10) (cfg.withState (some .guess₀)) ↔
      ∃ a b c d e f bit, g ![a, b, c, d, e, f, bit] = claim ∧
        ∀ p, (child p (![a, b, c, d, e, f, bit] p)).AcceptsWithin n
          (cfg.withState (some (child p (![a, b, c, d, e, f, bit] p)).toPTM.toNTM.q₀)) := by
    rw [acceptsWithin_control g claim child cfg .guess₀ .guess₁ (n + 9) rfl
      (by intros; rfl)]
    apply exists_congr; intro a
    rw [acceptsWithin_control g claim child cfg (.guess₁ a) (.guess₂ a) (n + 8) rfl
      (by intros; rfl)]
    apply exists_congr; intro b
    rw [acceptsWithin_control g claim child cfg (.guess₂ a b) (.guess₃ a b) (n + 7) rfl
      (by intros; rfl)]
    apply exists_congr; intro c
    rw [acceptsWithin_control g claim child cfg (.guess₃ a b c) (.guess₄ a b c) (n + 6) rfl
      (by intros; rfl)]
    apply exists_congr; intro d
    rw [acceptsWithin_control g claim child cfg (.guess₄ a b c d) (.guess₅ a b c d) (n + 5) rfl
      (by intros; rfl)]
    apply exists_congr; intro e
    rw [acceptsWithin_control g claim child cfg (.guess₅ a b c d e) (.guess₆ a b c d e)
      (n + 4) rfl (by intros; rfl)]
    apply exists_congr; intro f
    exact acceptsWithin_guess₆ g claim child cfg hout n a b c d e f
  rw [hprefix]
  constructor
  · rintro ⟨a, b, c, d, e, f, bit, h⟩
    exact ⟨![a, b, c, d, e, f, bit], h⟩
  · rintro ⟨v, h⟩
    refine ⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, ?_⟩
    have hv : ![v 0, v 1, v 2, v 3, v 4, v 5, v 6] = v := by
      funext i
      fin_cases i <;> rfl
    simpa only [hv] using h

/-- Correct child bit-claim continuations give the value of the fixed Boolean operation. -/
theorem acceptsWithin_eval {input : List Bool} (n : ℕ) (cfg : Cfg k Bool S input)
    (hout : cfg.output = []) (value : Fin 7 → Bool)
    (hchild : ∀ p b, (child p b).AcceptsWithin n
      (cfg.withState (some (child p b).toPTM.toNTM.q₀)) ↔ value p = b) :
    (machine g claim child).AcceptsWithin (n + 10) (cfg.withState (some .guess₀)) ↔
      g value = claim := by
  rw [acceptsWithin_iff g claim child n cfg hout]
  simp only [hchild]
  constructor
  · rintro ⟨v, hg, hv⟩
    have he : value = v := funext hv
    rwa [he]
  · intro hg
    exact ⟨value, hg, fun _ => rfl⟩

/-- Continuation simulation preserves time on every branch, including rejecting branches. -/
theorem haltsWithin_child {input : List Bool} (p : Fin 7) (bit : Bool)
    (n : ℕ) (cfg : Cfg k Bool S input) :
    (machine g claim child).HaltsWithin n (cfg.mapState (Option.map (.child p bit))) ↔
      (child p bit).HaltsWithin n cfg :=
  (childSimulation g claim child p bit).haltsWithin_iff n cfg

private theorem haltsWithin_control {input : List Bool} (cfg : Cfg k Bool S input)
    (q : State S) (qs : Bool → State S) (n : ℕ)
    (h : ∀ b inp work, tr g claim child b q inp work = jump (some (qs b)))
    (hnext : ∀ b, (machine g claim child).HaltsWithin n (cfg.withState (some (qs b)))) :
    (machine g claim child).HaltsWithin (n + 1) (cfg.withState (some q)) := by
  apply haltsWithin_succ.mpr
  intro b
  rw [next_control g claim child cfg q (qs b) b (h b)]
  exact hnext b

/-- Every branch finishes within the continuation budget plus ten transitions. No correctness
assumption on guesses is needed, and the bound also includes the dummy universal branch. -/
theorem haltsWithin {input : List Bool} (n : ℕ) (cfg : Cfg k Bool S input)
    (hchild : ∀ p b, (child p b).HaltsWithin n
      (cfg.withState (some (child p b).toPTM.toNTM.q₀))) :
    (machine g claim child).HaltsWithin (n + 10) (cfg.withState (some .guess₀)) := by
  apply haltsWithin_control g claim child cfg .guess₀ .guess₁ (n + 9) (by intros; rfl)
  intro a
  apply haltsWithin_control g claim child cfg (.guess₁ a) (.guess₂ a) (n + 8)
    (by intros; rfl)
  intro b
  apply haltsWithin_control g claim child cfg (.guess₂ a b) (.guess₃ a b) (n + 7)
    (by intros; rfl)
  intro c
  apply haltsWithin_control g claim child cfg (.guess₃ a b c) (.guess₄ a b c) (n + 6)
    (by intros; rfl)
  intro d
  apply haltsWithin_control g claim child cfg (.guess₄ a b c d) (.guess₅ a b c d) (n + 5)
    (by intros; rfl)
  intro e
  apply haltsWithin_control g claim child cfg (.guess₅ a b c d e) (.guess₆ a b c d e)
    (n + 4) (by intros; rfl)
  intro f
  apply haltsWithin_succ.mpr
  intro bit
  by_cases hg : g ![a, b, c, d, e, f, bit] = claim
  · rw [next_control g claim child cfg (.guess₆ a b c d e f)
      (.choose₀ ![a, b, c, d, e, f, bit]) bit (by intros; simp [tr, hg])]
    apply haltsWithin_control g claim child cfg _ _ (n + 2) (by intros; rfl)
    intro x
    apply haltsWithin_control g claim child cfg _ _ (n + 1) (by intros; rfl)
    intro y
    apply haltsWithin_succ.mpr
    intro z
    by_cases hp : (portCode x y z).val < 7
    · rw [next_control g claim child cfg _
        (.child ⟨(portCode x y z).val, hp⟩ (![a, b, c, d, e, f, bit] ⟨(portCode x y z).val, hp⟩)
          (child ⟨(portCode x y z).val, hp⟩
            (![a, b, c, d, e, f, bit] ⟨(portCode x y z).val, hp⟩)).toPTM.toNTM.q₀) z
        (by intros; simp [tr, hp])]
      exact (haltsWithin_child g claim child _ _ n
        (cfg.withState (some (child _ _).toPTM.toNTM.q₀))).mpr (hchild _ _)
    · apply haltsWithin_of_halted
      rw [machine, next_ofTMs, MultiTapeTM.step_of_state rfl, MultiTapeTM.tr_ofTr]
      simp [tr, hp, jump, Action.apply]
  · apply haltsWithin_of_halted
    rw [machine, next_ofTMs, MultiTapeTM.step_of_state rfl, MultiTapeTM.tr_ofTr]
    simp [tr, hg, jump, Action.apply]

end Turing.MultiTapeATM.TruthTable
