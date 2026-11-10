/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
# Hand-stepped runs of machines with one work tape

Scaffolding for verifying small machines with one work tape step by step, as in
`Turing.MultiTapeTM.ZipTransducer.toTM` and `Turing.MultiTapeTM.TakeDropUnary.toTM`. A
configuration is written as `cfgAt w st p tape h o` with the input head at `p` (clamped to the
input), and a run segment `Seg tm S c c' t` records that `tm` reaches `c'` from `c` within `t`
steps while its work head stays in `S`. Segments compose, so a bound on the cells used by a whole
run follows from the bounds of its phases.

## Main definitions

* `Turing.MultiTapeTM.OneWorkTape.cfgAt`: a configuration of a machine with one work tape.
* `Turing.MultiTapeTM.OneWorkTape.Seg`: a run segment whose work head stays in a set of cells.
* `Turing.MultiTapeTM.OneWorkTape.cells`: the cells `-1, …, n`.

## Main results

* `Turing.MultiTapeTM.OneWorkTape.step_cfgAt`: one step from `cfgAt`, read off the transition
  function.
* `Turing.MultiTapeTM.OneWorkTape.Seg.refl`, `.single`, `.trans`, `.mono`: composing run segments.
-/

namespace Turing

/-- Moving right from a position before the right end cell. -/
public lemma moveInputPosNat_one {n j : ℕ} (hj : j ≤ n) : moveInputPosNat n j 1 = j + 1 := by
  simp only [moveInputPosNat, SignType.coe_one]
  omega

/-- Not moving. -/
public lemma moveInputPosNat_zero {n j : ℕ} (hj : j ≤ n + 1) : moveInputPosNat n j 0 = j := by
  simp only [moveInputPosNat, SignType.coe_zero]
  omega

/-- Moving left from a position on the input tape. -/
public lemma moveInputPosNat_neg_one {n j : ℕ} (hj : j ≤ n + 1) :
    moveInputPosNat n j (-1) = j - 1 := by
  simp only [moveInputPosNat, SignType.coe_neg_one]
  omega

/-- A move keeps the input head on the input tape. -/
private lemma moveInputPosNat_le (n j : ℕ) (d : SignType) (hj : j < n + 2) :
    moveInputPosNat n j d ≤ n + 1 := by
  have := (moveInputPos (⟨j, hj⟩ : Fin (n + 2)) d).isLt
  rw [val_moveInputPos_eq_moveInputPosNat] at this
  exact Nat.lt_succ_iff.mp this

namespace MultiTapeTM.OneWorkTape

variable {Symbol State : Type*} {w : List Symbol}

/-! ### Configurations -/

/-- The configuration in state `st` with the input head at `p` (clamped to the input), the work
tape `tape` with its head at `h`, and the output `o`. -/
@[expose] public def cfgAt (w : List Symbol) (st : Option State) (p : ℕ)
    (tape : ℤ → Option Symbol) (h : ℤ) (o : List Symbol) : Cfg 1 Symbol State w :=
  ⟨st, ⟨min p (w.length + 1), by omega⟩, fun _ => tape, fun _ => h, o⟩

/-- One step of a machine with one work tape, read off a transition function `f` on the input
symbol and the work-tape symbol. -/
public lemma step_cfgAt {tm : MultiTapeTM 1 Symbol State}
    {f : State → Option Symbol → Option Symbol → Action 1 Symbol State}
    (htr : ∀ s x y, tm.tr s x (fun _ => y) = f s x y) (s : State) (p : ℕ)
    (tape : ℤ → Option Symbol) (h : ℤ) (o : List Symbol) :
    tm.step (cfgAt w (some s) p tape h o) =
      cfgAt w (f s (inputAt w (min p (w.length + 1))) (tape h)).state
        (moveInputPosNat w.length (min p (w.length + 1))
          (f s (inputAt w (min p (w.length + 1))) (tape h)).inputTape)
        (match ((f s (inputAt w (min p (w.length + 1))) (tape h)).workTapes 0).1 with
          | none => tape
          | some x => Function.update tape h x)
        (h + (((f s (inputAt w (min p (w.length + 1))) (tape h)).workTapes 0).2 : ℤ))
        (o ++ (f s (inputAt w (min p (w.length + 1))) (tape h)).output.toList) := by
  have hw : (cfgAt w (some s) p tape h o).workTapeSymbols = fun _ => tape h := rfl
  have hp : ((cfgAt w (some s) p tape h o).inputPos : ℕ) = min p (w.length + 1) := rfl
  rw [step_of_state rfl, Cfg.inputSymbol_eq_inputAt, hw, hp, htr]
  refine Cfg.ext rfl (Fin.ext ?_) (funext fun i => ?_) (funext fun i => ?_) rfl
  · rw [Action.apply_inputPos, val_moveInputPos_eq_moveInputPosNat, hp]
    exact (min_eq_left (moveInputPosNat_le _ _ _ (by omega))).symm
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [cfgAt, Action.apply_workTapes]
    rcases ((f s (inputAt w (min p (w.length + 1))) (tape h)).workTapes 0).1 with _ | _ <;> rfl
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [cfgAt, Action.apply_workTapePos]

/-- Configurations agree when their clamped input positions and their work heads do. -/
public lemma cfgAt_congr {st : Option State} {p p' : ℕ} {tape : ℤ → Option Symbol} {h h' : ℤ}
    {o : List Symbol} (hp : min p (w.length + 1) = min p' (w.length + 1)) (hh : h = h') :
    cfgAt w st p tape h o = cfgAt w st p' tape h' o := by
  subst hh
  simp only [cfgAt, hp]

/-- The work head of `cfgAt`. -/
@[simp]
public lemma cfgAt_workTapePos (st : Option State) (p : ℕ) (tape : ℤ → Option Symbol) (h : ℤ)
    (o : List Symbol) : (cfgAt w st p tape h o).workTapePos 0 = h :=
  rfl

/-- The cells `-1, …, n`: the left end marker cell and a word of length `n`. -/
public abbrev cells (n : ℕ) : Finset ℤ := Finset.Icc (-1) n

/-- A work head between `-1` and `n` is in `cells n`. -/
public lemma cfgAt_mem_cells {n : ℕ} {st : Option State} {p : ℕ} {tape : ℤ → Option Symbol}
    {h : ℤ} {o : List Symbol} (h₀ : -1 ≤ h) (h₁ : h ≤ n) :
    (cfgAt w st p tape h o).workTapePos 0 ∈ cells n :=
  Finset.mem_Icc.mpr ⟨h₀, h₁⟩

/-! ### Runs through a set of work-head positions -/

/-- From `c`, `tm` reaches `c'` within `t` steps, its work head staying in `S`. -/
@[expose] public def Seg (tm : MultiTapeTM 1 Symbol State) (S : Finset ℤ)
    (c c' : Cfg 1 Symbol State w) (t : ℕ) : Prop :=
  ∃ n ≤ t, tm.runFrom c n = c' ∧ ∀ j ≤ n, (tm.runFrom c j).workTapePos 0 ∈ S

variable {tm : MultiTapeTM 1 Symbol State} {S : Finset ℤ} {c c' c'' : Cfg 1 Symbol State w}
  {t t' : ℕ}

/-- The empty segment. -/
public lemma Seg.refl (hc : c.workTapePos 0 ∈ S) : Seg tm S c c 0 :=
  ⟨0, le_rfl, rfl, fun j hj => by
    obtain rfl : j = 0 := by omega
    exact hc⟩

/-- A segment of one step. -/
public lemma Seg.single (hc : c.workTapePos 0 ∈ S) (h : tm.step c = c')
    (hc' : c'.workTapePos 0 ∈ S) : Seg tm S c c' 1 :=
  ⟨1, le_rfl, h, fun j hj => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · exact hc
    · rw [runFrom_one, h]
      exact hc'⟩

/-- Consecutive segments compose, adding their times. -/
public lemma Seg.trans (h₁ : Seg tm S c c' t) (h₂ : Seg tm S c' c'' t') :
    Seg tm S c c'' (t + t') := by
  obtain ⟨n₁, hn₁, hr₁, hs₁⟩ := h₁
  obtain ⟨n₂, hn₂, hr₂, hs₂⟩ := h₂
  refine ⟨n₁ + n₂, by omega, by rw [runFrom_add, hr₁, hr₂], fun j hj => ?_⟩
  rcases Nat.lt_or_ge n₁ j with h | h
  · obtain ⟨d, rfl⟩ : ∃ d, j = n₁ + d := ⟨j - n₁, by omega⟩
    rw [runFrom_add, hr₁]
    exact hs₂ d (by omega)
  · exact hs₁ j h

/-- A segment within `t` steps is within any larger number of steps. -/
public lemma Seg.mono (h : Seg tm S c c' t) (ht : t ≤ t') : Seg tm S c c' t' :=
  let ⟨n, hn, hr, hs⟩ := h
  ⟨n, hn.trans ht, hr, hs⟩

end MultiTapeTM.OneWorkTape

end Turing
