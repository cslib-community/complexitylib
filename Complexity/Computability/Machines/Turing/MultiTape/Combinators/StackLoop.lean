/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelStackLoop
import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelFacts
import Mathlib.Tactic.Ring

/-!
# Loops with a stack of frames

A stack loop (`Turing.MultiTapeTM.StackLoop`) keeps a current value and a stack of frames. While
`halt` is false at the current value, a round pops the top frame (`none` on an empty stack),
applies `round` to it and the current value, pushes the returned frames (the first one ends on
top) and continues with the returned value.

The machine keeps the stack on its own work tape, so a round touches only the current value, the
popped frame and the pushed frames: its cost does not depend on the frames deeper in the stack.
This makes recursive algorithms such as divide and conquer computable within the sum of the costs
of their calls, rather than paying for the whole recursion state on every round.

The machine is `Turing.MultiTapeTM.StackLoopKernel.stackLoopTM`; its run is
`Turing.MultiTapeTM.StackLoopKernel.runs_stackLoop`. The frames sit on the stack tape as their
framed encodings, top first, ending just before cell `0`: a push writes the new frames to the left
of the stack, and a pop moves the top frame to the front of the current value, which then is the
encoding of the round input.

## Main definitions

* `Turing.MultiTapeTM.StackLoop`: the round and the halting test of a stack loop.
* `Turing.MultiTapeTM.StackLoop.step`: one round on a value and a stack.

## Main results

* `Turing.MultiTapeTM.ComputableInO.stackLoop`: if the initial value, the halting test and
  the round are computable, so is the value at which the loop halts with an empty stack,
  within the sum over the rounds of their costs and the lengths of the words they touch.
-/

public section

namespace Turing.MultiTapeTM

/-- A loop with a stack of frames: a halting test on the current value, and a round taking the
popped top frame (`none` on an empty stack) and the current value to the frames to push, the
first one ending on top, and the next value. -/
structure StackLoop (α γ : Type) where
  /-- Whether the loop stops at the current value. -/
  halt : α → Bool
  /-- A round: from the popped frame and the current value, the pushed frames and the next
  value. -/
  round : Option γ × α → List γ × α

namespace StackLoop

variable {α γ : Type}

/-- The input of a round on the value `s.1` and the stack `s.2`, top first: the top frame, if
any, and the value. -/
@[expose] def roundInput (s : α × List γ) : Option γ × α := (s.2.head?, s.1)

/-- One round on a value and a stack, top first: pop the top frame, apply the round, push the
returned frames. -/
@[expose] def step (L : StackLoop α γ) (s : α × List γ) : α × List γ :=
  ((L.round (roundInput s)).2, (L.round (roundInput s)).1 ++ s.2.tail)

end StackLoop

open StackLoop

open StackLoopKernel in
/-- A run of a machine from and to blank stack-loop configurations is a tidy computation. -/
private theorem computesTidily_of_runsBetween {kk : ℕ} {S : Type*}
    {tm : MultiTapeTM (kk + 6) Bool S} {input y : List Bool} {t s : ℕ}
    (h : RunsBetween tm (cfgS input [] [] [] [] [] 0 0 0 0 [])
      (cfgS input [] [] [] [] [] 0 0 0 0 y) t s) :
    tm.ComputesTidilyInTimeAndSpace input y t s := by
  rw [cfgS_blank, cfgS_blank] at h
  obtain ⟨hrun, hsp⟩ := h
  rw [tapesCfg_zero_withState, tapesCfg_zero_withState] at hrun
  rw [tapesCfg_zero_withState] at hsp
  exact computesTidily_iff.mpr ⟨.ofDeterministic tm _ t, rfl, hrun, le_rfl, hsp⟩

/-- Summing bounds on the rounds, each charged to its own costs and to the next halting test. -/
private theorem sum_le_of_round {n c : ℕ} {u v w : ℕ → ℕ}
    (h : ∀ i < n, u i ≤ c * (4 * v i + w (i + 1))) :
    ∑ i ∈ Finset.range n, u i ≤
      c * (4 * ∑ i ∈ Finset.range n, v i + ∑ i ∈ Finset.range (n + 1), w i) := by
  calc ∑ i ∈ Finset.range n, u i ≤ ∑ i ∈ Finset.range n, c * (4 * v i + w (i + 1)) :=
        Finset.sum_le_sum fun i hi => h i (Finset.mem_range.mp hi)
    _ = c * (4 * ∑ i ∈ Finset.range n, v i + ∑ i ∈ Finset.range n, w (i + 1)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ c * (4 * ∑ i ∈ Finset.range n, v i + ∑ i ∈ Finset.range (n + 1), w i) := by
        refine Nat.mul_le_mul_left _ (Nat.add_le_add_left ?_ _)
        rw [Finset.sum_range_succ' w]
        exact Nat.le_add_right _ _

/-- The arithmetic of the time of one round. -/
private theorem round_time_arith {c0 cP cN cH T S Th Sh e F A A' X ri ro : ℕ}
    (hc : cP + cN + cH + 100 ≤ c0) (hri : ri = F + A) (hro : ro = 2 * X + 1 + A') (hF : 1 ≤ F) :
    cP * (T + 1) + cN * (T + 1) + cH * (Th + 1) + 9 * (F + A + A' + X + 2) + 42 + 1 ≤
      c0 * (4 * (T + S + ri + ro) + (Th + Sh + e)) := by
  have h1 : cP * (T + 1) ≤ c0 * (T + 1) := Nat.mul_le_mul_right _ (by omega)
  have h2 : cN * (T + 1) ≤ c0 * (T + 1) := Nat.mul_le_mul_right _ (by omega)
  have h3 : cH * (Th + 1) ≤ c0 * (Th + 1) := Nat.mul_le_mul_right _ (by omega)
  have h4 : 100 * (ri + ro + 1) ≤ c0 * (ri + ro + 1) := Nat.mul_le_mul_right _ (by omega)
  have h5 : c0 * (T + 1) + c0 * (T + 1) + c0 * (Th + 1) + c0 * (ri + ro + 1) ≤
      c0 * (4 * (T + S + ri + ro) + (Th + Sh + e)) := by
    rw [← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- The arithmetic of the space of one round. -/
private theorem round_space_arith {d0 cP cN cH kk kP kN kH T S Th Sh e F A A' X ri ro : ℕ}
    (hd : cP + cN + cH + 25 * kk + 300 ≤ d0) (hri : ri = F + A) (hro : ro = 2 * X + 1 + A')
    (hF : 1 ≤ F) :
    cP * (S + 1) + (kk - kP) + (cN * (S + 1) + (kk - kN)) + (cH * (Sh + 1) + (kk - kH)) +
        12 * (F + A + A' + X + 2) + 21 * kk + 220 + (kk + 6) ≤
      d0 * (4 * (T + S + ri + ro) + (Th + Sh + e)) := by
  have h1 : cP * (S + 1) ≤ d0 * (S + 1) := Nat.mul_le_mul_right _ (by omega)
  have h2 : cN * (S + 1) ≤ d0 * (S + 1) := Nat.mul_le_mul_right _ (by omega)
  have h3 : cH * (Sh + 1) ≤ d0 * (Sh + 1) := Nat.mul_le_mul_right _ (by omega)
  have h4 : (25 * kk + 300) * (ri + ro + 1) ≤ d0 * (ri + ro + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have h6 : kk ≤ kk * (ri + ro + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h7 : (25 * kk + 300) * (ri + ro + 1) = 25 * (kk * (ri + ro + 1)) + 300 * (ri + ro + 1) := by
    ring
  have h5 : d0 * (S + 1) + d0 * (S + 1) + d0 * (Sh + 1) + d0 * (ri + ro + 1) ≤
      d0 * (4 * (T + S + ri + ro) + (Th + Sh + e)) := by
    rw [← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- The arithmetic of the total time. -/
private theorem total_time_arith {K cI cH c0 Ti Si H R E A0 An T0 S0 : ℕ}
    (hK : 4 * (cI + cH + c0 + 50) ≤ K) (hS : S0 ≤ c0 * (4 * R + H)) (ha0 : A0 ≤ cI * (Si + 1))
    (hTh : T0 ≤ H) (han : An ≤ H) :
    cI * (Ti + 1) + cH * (T0 + 1) + S0 + A0 + 5 * An + 40 ≤ K * (E + Ti + Si + H + R + 1) := by
  have h1 : cI * (Ti + 1) ≤ (cI + cH + c0 + 50) * (Ti + 1) := Nat.mul_le_mul_right _ (by omega)
  have h2 : cH * (T0 + 1) ≤ (cI + cH + c0 + 50) * (H + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : c0 * (4 * R + H) ≤ (cI + cH + c0 + 50) * (4 * R + H) :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : cI * (Si + 1) ≤ (cI + cH + c0 + 50) * (Si + 1) := Nat.mul_le_mul_right _ (by omega)
  have h5 : 50 * (H + 1) ≤ (cI + cH + c0 + 50) * (H + 1) := Nat.mul_le_mul_right _ (by omega)
  have h6 : (cI + cH + c0 + 50) * (Ti + 1) + (cI + cH + c0 + 50) * (H + 1) +
      (cI + cH + c0 + 50) * (4 * R + H) + (cI + cH + c0 + 50) * (Si + 1) +
      (cI + cH + c0 + 50) * (H + 1) ≤ K * (E + Ti + Si + H + R + 1) := by
    rw [← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add]
    calc (cI + cH + c0 + 50) * (Ti + 1 + (H + 1) + (4 * R + H) + (Si + 1) + (H + 1))
        ≤ (cI + cH + c0 + 50) * (4 * (E + Ti + Si + H + R + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 4 * (cI + cH + c0 + 50) * (E + Ti + Si + H + R + 1) := by ring
      _ ≤ K * (E + Ti + Si + H + R + 1) := Nat.mul_le_mul_right _ hK
  omega

/-- The arithmetic of the total space. -/
private theorem total_space_arith {K cI cH d0 kk kI kH Ti Si H R E A0 An Sh0 S0 : ℕ}
    (hK : 8 * (cI + cH + d0 + 20 * kk + 200) ≤ K) (hS : S0 ≤ d0 * (4 * R + H))
    (ha0 : A0 ≤ cI * (Si + 1)) (hSh : Sh0 ≤ H) (han : An ≤ H) :
    cI * (Si + 1) + (kk - kI) + (cH * (Sh0 + 1) + (kk - kH)) + S0 + 4 * A0 + 3 * An +
        10 * kk + 100 ≤ K * (E + Ti + Si + H + R + 1) := by
  set C := cI + cH + d0 + 20 * kk + 200 with hC
  have h1 : cI * (Si + 1) ≤ C * (Si + 1) := Nat.mul_le_mul_right _ (by omega)
  have h2 : cH * (Sh0 + 1) ≤ C * (H + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : d0 * (4 * R + H) ≤ C * (4 * R + H) := Nat.mul_le_mul_right _ (by omega)
  have h5 : (20 * kk + 200) * (H + 1) ≤ C * (H + 1) := Nat.mul_le_mul_right _ (by omega)
  have h8 : (20 * kk + 200) * (H + 1) = 20 * (kk * (H + 1)) + 200 * (H + 1) := by ring
  have h9 : kk ≤ kk * (H + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h6 : C * (Si + 1) + C * (H + 1) + C * (4 * R + H) + 4 * (C * (Si + 1)) + C * (H + 1) ≤
      K * (E + Ti + Si + H + R + 1) := by
    rw [show 4 * (C * (Si + 1)) = C * (4 * (Si + 1)) by ring, ← Nat.mul_add, ← Nat.mul_add,
      ← Nat.mul_add, ← Nat.mul_add]
    calc C * (Si + 1 + (H + 1) + (4 * R + H) + 4 * (Si + 1) + (H + 1))
        ≤ C * (8 * (E + Ti + Si + H + R + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 8 * C * (E + Ti + Si + H + R + 1) := by ring
      _ ≤ K * (E + Ti + Si + H + R + 1) := Nat.mul_le_mul_right _ hK
  omega

/-- The tidy version of `Turing.MultiTapeTM.ComputableInO.stackLoop`. -/
private theorem ComputableTidilyInO.stackLoop {δ α γ : Type} {encIn : δ ↪ List Bool}
    {encA : α ↪ List Bool} {encG : γ ↪ List Bool} (L : StackLoop α γ)
    {init : δ → α} {Ti Si : δ → ℕ} {Th Sh : α → ℕ} {Tr Sr : Option γ × α → ℕ} (n : δ → ℕ)
    (hinit : ComputableTidilyInO init encIn encA Ti Si)
    (hhalt : ComputableTidilyInO L.halt encA encBool Th Sh)
    (hround : ComputableTidilyInO L.round (encPair (encOption encG) encA)
      (encPair (encList encG) encA) Tr Sr)
    (hrun : ∀ x, ∀ i < n x, L.halt (L.step^[i] (init x, [])).1 = false)
    (hstop : ∀ x, L.halt (L.step^[n x] (init x, [])).1 = true)
    (hempty : ∀ x, (L.step^[n x] (init x, [])).2 = []) :
    ComputableTidilyInO (fun x => (L.step^[n x] (init x, [])).1) encIn encA
      (fun x => (encIn x).length + Ti x + Si x +
        ∑ i ∈ Finset.range (n x + 1),
          (Th (L.step^[i] (init x, [])).1 + Sh (L.step^[i] (init x, [])).1 +
            (encA (L.step^[i] (init x, [])).1).length) +
        ∑ i ∈ Finset.range (n x),
          (Tr (roundInput (L.step^[i] (init x, []))) + Sr (roundInput (L.step^[i] (init x, []))) +
            (encPair (encOption encG) encA (roundInput (L.step^[i] (init x, [])))).length +
            (encPair (encList encG) encA (L.round (roundInput (L.step^[i] (init x, []))))).length))
      (fun x => (encIn x).length + Ti x + Si x +
        ∑ i ∈ Finset.range (n x + 1),
          (Th (L.step^[i] (init x, [])).1 + Sh (L.step^[i] (init x, [])).1 +
            (encA (L.step^[i] (init x, [])).1).length) +
        ∑ i ∈ Finset.range (n x),
          (Tr (roundInput (L.step^[i] (init x, []))) + Sr (roundInput (L.step^[i] (init x, []))) +
            (encPair (encOption encG) encA (roundInput (L.step^[i] (init x, [])))).length +
            (encPair (encList encG) encA
              (L.round (roundInput (L.step^[i] (init x, []))))).length)) := by
  obtain ⟨cI, ⟨kI, SI, _, tI, hI⟩, lI⟩ := hinit
  obtain ⟨cH, ⟨kH, SH, _, tH, hH⟩, -⟩ := hhalt
  obtain ⟨cP, ⟨kP, SP, _, tP, hP⟩, -⟩ := hround.fst'
  obtain ⟨cN, ⟨kN, SN, _, tN, hN⟩, -⟩ := hround.snd'
  -- the four machines, padded to a common number of work tapes
  set kk := max (max kI kH) (max kP kN) with hkk
  have hkI : kI ≤ kk := (le_max_left _ _).trans (le_max_left _ _)
  have hkH : kH ≤ kk := (le_max_right _ _).trans (le_max_left _ _)
  have hkP : kP ≤ kk := (le_max_left _ _).trans (le_max_right _ _)
  have hkN : kN ≤ kk := (le_max_right _ _).trans (le_max_right _ _)
  have key := fun x => StackLoopKernel.runs_stackLoop (kk := kk) (input := encIn x)
    (encA := encA) (encG := encG) (halt := L.halt) (round := L.round)
    (tI := tI.extendTapes (Fin.castLEEmb hkI)) (tH := tH.extendTapes (Fin.castLEEmb hkH))
    (tP := tP.extendTapes (Fin.castLEEmb hkP)) (tN := tN.extendTapes (Fin.castLEEmb hkN))
    (TH := fun a => cH * (Th a + 1)) (SH' := fun a => cH * (Sh a + 1) + (kk - kH))
    (TP := fun z => cP * (Tr z + 1)) (SP' := fun z => cP * (Sr z + 1) + (kk - kP))
    (TN := fun z => cN * (Tr z + 1)) (SN' := fun z => cN * (Sr z + 1) + (kk - kN))
    (fun a => (hH a).extendTapes (Fin.castLEEmb hkH))
    (fun z => (hP z).extendTapes (Fin.castLEEmb hkP))
    (fun z => (hN z).extendTapes (Fin.castLEEmb hkN))
    (fun i => L.step^[i] (init x, [])) (n x) ((hI x).extendTapes (Fin.castLEEmb hkI)) rfl
    (fun i => Function.iterate_succ_apply' _ _ _) (hrun x) (hstop x) (hempty x)
  set c0 := cP + cN + cH + 100 with hc0
  set d0 := cP + cN + cH + 25 * kk + 300 with hd0
  -- the costs of the halting tests and of the rounds
  have hH0 (x : δ) : Th (L.step^[0] (init x, [])).1 + Sh (L.step^[0] (init x, [])).1 +
      (encA (L.step^[0] (init x, [])).1).length ≤
      ∑ i ∈ Finset.range (n x + 1), (Th (L.step^[i] (init x, [])).1 +
        Sh (L.step^[i] (init x, [])).1 + (encA (L.step^[i] (init x, [])).1).length) :=
    Finset.single_le_sum (f := fun i => Th (L.step^[i] (init x, [])).1 +
      Sh (L.step^[i] (init x, [])).1 + (encA (L.step^[i] (init x, [])).1).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos _))
  have hHn (x : δ) : Th (L.step^[n x] (init x, [])).1 + Sh (L.step^[n x] (init x, [])).1 +
      (encA (L.step^[n x] (init x, [])).1).length ≤
      ∑ i ∈ Finset.range (n x + 1), (Th (L.step^[i] (init x, [])).1 +
        Sh (L.step^[i] (init x, [])).1 + (encA (L.step^[i] (init x, [])).1).length) :=
    Finset.single_le_sum (f := fun i => Th (L.step^[i] (init x, [])).1 +
      Sh (L.step^[i] (init x, [])).1 + (encA (L.step^[i] (init x, [])).1).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self _))
  refine ComputableTidilyInO.of_bounds ⟨kk + 6, _, by infer_instance, _,
    fun x => computesTidily_of_runsBetween (key x)⟩
    (4 * (cI + cH + c0 + 50) + 8 * (cI + cH + d0 + 20 * kk + 200) + 1) ?_ ?_ ?_
  · intro x
    have hsum := sum_le_of_round (n := n x) (c := c0)
      (u := fun i => StackLoopKernel.roundTime encA encG L.round (fun a => cH * (Th a + 1))
        (fun z => cP * (Tr z + 1)) (fun z => cN * (Tr z + 1)) (fun i => L.step^[i] (init x, []))
        i + 1)
      (v := fun i => Tr (roundInput (L.step^[i] (init x, []))) +
        Sr (roundInput (L.step^[i] (init x, []))) +
        (encPair (encOption encG) encA (roundInput (L.step^[i] (init x, [])))).length +
        (encPair (encList encG) encA (L.round (roundInput (L.step^[i] (init x, []))))).length)
      (w := fun i => Th (L.step^[i] (init x, [])).1 + Sh (L.step^[i] (init x, [])).1 +
        (encA (L.step^[i] (init x, [])).1).length)
      (fun i _ => by
        simp only [StackLoopKernel.roundTime, StackLoopKernel.zIn, roundInput,
          Function.iterate_succ_apply', StackLoop.step]
        generalize L.step^[i] (init x, []) = st
        generalize L.round (st.2.head?, st.1) = rr
        exact round_time_arith (by omega) (by simp) (length_encPair _) (by simp [length_frame]))
    have h0 := hH0 x
    have hn := hHn x
    exact total_time_arith (by omega) hsum (lI x) (by omega) (by omega)
  · intro x
    have hsum := sum_le_of_round (n := n x) (c := d0)
      (u := fun i => StackLoopKernel.roundSpace encA encG L.round
        (fun a => cH * (Sh a + 1) + (kk - kH)) (fun z => cP * (Sr z + 1) + (kk - kP))
        (fun z => cN * (Sr z + 1) + (kk - kN)) kk (fun i => L.step^[i] (init x, [])) i + (kk + 6))
      (v := fun i => Tr (roundInput (L.step^[i] (init x, []))) +
        Sr (roundInput (L.step^[i] (init x, []))) +
        (encPair (encOption encG) encA (roundInput (L.step^[i] (init x, [])))).length +
        (encPair (encList encG) encA (L.round (roundInput (L.step^[i] (init x, []))))).length)
      (w := fun i => Th (L.step^[i] (init x, [])).1 + Sh (L.step^[i] (init x, [])).1 +
        (encA (L.step^[i] (init x, [])).1).length)
      (fun i _ => by
        simp only [StackLoopKernel.roundSpace, StackLoopKernel.zIn, roundInput,
          Function.iterate_succ_apply', StackLoop.step]
        generalize L.step^[i] (init x, []) = st
        generalize L.round (st.2.head?, st.1) = rr
        exact round_space_arith (by omega) (by simp) (length_encPair _) (by simp [length_frame]))
    have h0 := hH0 x
    have hn := hHn x
    exact total_space_arith (by omega) hsum (lI x) (by omega) (by omega)
  · intro x
    have hn := hHn x
    have hK := Nat.le_mul_of_pos_left ((encIn x).length + Ti x + Si x +
        ∑ i ∈ Finset.range (n x + 1),
          (Th (L.step^[i] (init x, [])).1 + Sh (L.step^[i] (init x, [])).1 +
            (encA (L.step^[i] (init x, [])).1).length) +
        ∑ i ∈ Finset.range (n x),
          (Tr (roundInput (L.step^[i] (init x, []))) + Sr (roundInput (L.step^[i] (init x, []))) +
            (encPair (encOption encG) encA (roundInput (L.step^[i] (init x, [])))).length +
            (encPair (encList encG) encA (L.round (roundInput (L.step^[i] (init x, []))))).length) +
          1)
      (show 0 < 4 * (cI + cH + c0 + 50) + 8 * (cI + cH + d0 + 20 * kk + 200) + 1 by omega)
    omega

/-- **Stack loops.** If the initial value, the halting test and the round of a stack loop are
computable, and from the initial value with an empty stack the loop halts after `n x`
rounds with an empty stack, then the halting value is computable. The time and space are
the costs of the initialization, plus, for every round and the final halting test, the costs of
the halting test and of the round together with the lengths of the words they read and write.

The frames are kept on a separate work tape: a round pays for the popped and pushed frames only,
not for the rest of the stack. -/
theorem ComputableInO.stackLoop {δ α γ : Type} {encIn : δ ↪ List Bool}
    {encA : α ↪ List Bool} {encG : γ ↪ List Bool} (L : StackLoop α γ)
    {init : δ → α} {Ti Si : δ → ℕ} {Th Sh : α → ℕ} {Tr Sr : Option γ × α → ℕ} (n : δ → ℕ)
    (hinit : ComputableInO init encIn encA Ti Si)
    (hhalt : ComputableInO L.halt encA encBool Th Sh)
    (hround : ComputableInO L.round (encPair (encOption encG) encA)
      (encPair (encList encG) encA) Tr Sr)
    (hrun : ∀ x, ∀ i < n x, L.halt (L.step^[i] (init x, [])).1 = false)
    (hstop : ∀ x, L.halt (L.step^[n x] (init x, [])).1 = true)
    (hempty : ∀ x, (L.step^[n x] (init x, [])).2 = []) :
    ComputableInO (fun x => (L.step^[n x] (init x, [])).1) encIn encA
      (fun x => (encIn x).length + Ti x + Si x +
        ∑ i ∈ Finset.range (n x + 1),
          (Th (L.step^[i] (init x, [])).1 + Sh (L.step^[i] (init x, [])).1 +
            (encA (L.step^[i] (init x, [])).1).length) +
        ∑ i ∈ Finset.range (n x),
          (Tr (roundInput (L.step^[i] (init x, []))) + Sr (roundInput (L.step^[i] (init x, []))) +
            (encPair (encOption encG) encA (roundInput (L.step^[i] (init x, [])))).length +
            (encPair (encList encG) encA (L.round (roundInput (L.step^[i] (init x, []))))).length))
      (fun x => (encIn x).length + Ti x + Si x +
        ∑ i ∈ Finset.range (n x + 1),
          (Th (L.step^[i] (init x, [])).1 + Sh (L.step^[i] (init x, [])).1 +
            (encA (L.step^[i] (init x, [])).1).length) +
        ∑ i ∈ Finset.range (n x),
          (Tr (roundInput (L.step^[i] (init x, []))) + Sr (roundInput (L.step^[i] (init x, []))) +
            (encPair (encOption encG) encA (roundInput (L.step^[i] (init x, [])))).length +
            (encPair (encList encG) encA
              (L.round (roundInput (L.step^[i] (init x, []))))).length)) :=
  (ComputableTidilyInO.stackLoop L n hinit.tidy hhalt.tidy hround.tidy hrun hstop
    hempty).computableInO

end Turing.MultiTapeTM
