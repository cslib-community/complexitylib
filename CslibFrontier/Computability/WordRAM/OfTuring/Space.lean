/-
Copyright (c) 2026 Samuel Schlesinger, Carlos Toledo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Carlos Toledo
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.OfTuring
public import CslibFrontier.Computability.WordRAM.Time
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Word RAMs simulate space-bounded multi-tape Turing machines

`Cslib.WordRAM.OfTuring.executes_simProgram` bounds the simulated work-tape addresses by the
running time `t`, so its words must hold `simBound k m |x| t`. A run that visits at most `s` work
cells keeps every work head within `[-s, s]`, so the same simulator works when the words hold only
`simBound k m |x| s`. With polynomial work space, the word size can then stay logarithmic in the
input length while the running time is arbitrary, for example `2 ^ o(n)`.

The proof of `Cslib.WordRAM.OfTuring.executes_simProgram_of_runsInSpace` is that of
`Cslib.WordRAM.OfTuring.executes_simProgram`, with the time bound on the head positions replaced
by the space bound.

## Main results

* `Turing.MultiTapeTM.natAbs_workTapePos_runFrom_le_of_runsInSpace`: a run in space `s` keeps
  every work head within distance `s` of the origin.
* `Cslib.WordRAM.OfTuring.executes_simProgram_of_runsInSpace`: the simulator of a halting run in
  space `s`, at every word size whose words hold `simBound k m |x| s`.
* `Cslib.WordRAM.uniformDecidableInTimeLogWord_of_decidableInTimeAndSpace`: a problem decided
  by a multi-tape machine in time `t` and polynomial work space is decided by one fixed program
  over `Basis.additive` within `C * t + C` instructions, at every word size above a logarithmic
  threshold.
-/

public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Q : Type}

/-- A run in space `s` keeps every work head within distance `s` of the origin, at every step. -/
theorem natAbs_workTapePos_runFrom_le_of_runsInSpace {tm : MultiTapeTM k Bool Q}
    {inp : List Bool} {s : ℕ} (h : tm.RunsInSpace inp s) (j : ℕ) (i : Fin k) :
    ((tm.runFrom (tm.initCfg inp) j).workTapePos i).natAbs ≤ s := by
  have hwin := MultiTapeNTM.RunPath.inWindow_of_space_le
    (p := MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg inp) j) (s := s)
    (fun _ => rfl) (space_le_of_runsInSpace h j)
  exact mem_window.mp (hwin _ (RelSeries.last_mem _) i)

end Turing.MultiTapeTM

namespace Cslib.WordRAM.OfTuring

open Turing

variable {k m : ℕ} {Q : Type}

/-- **The simulator in space-bounded words.** As `Cslib.WordRAM.OfTuring.executes_simProgram`, but
the words need only hold `simBound k m |inp| s` for a space bound `s` of the run, instead of
`simBound k m |inp| t` for its running time `t`. The instruction count is still
`simTime k m t`. -/
theorem executes_simProgram_of_runsInSpace {tm : MultiTapeTM k Bool Q} {inp : List Bool}
    {δ : Q → Option Bool → (Fin k → Option Bool) → Action k Bool Q}
    (hδ : ∀ q a s, tm.tr q a s = δ q a s) (e : Q ≃ Fin m) {t s : ℕ}
    (ht : (tm.runFrom (tm.initCfg inp) t).state = none) (hs : tm.RunsInSpace inp s) {w : ℕ}
    (hw : simBound k m inp.length s < 2 ^ w)
    (hout : (tm.runFrom (tm.initCfg inp) t).output.length < w) :
    ∃ n ≤ simTime k m t, Executes w (simProgram δ tm.q₀ e) (State.init (inp.map Bool.toNat))
      (BitString.lsbValue (tm.runFrom (tm.initCfg inp) t).output) n := by
  obtain ⟨t₀, ht₀, hhalts⟩ := MultiTapeTM.exists_haltsAt ht
  have hhalt : (tm.runFrom (tm.initCfg inp) t₀).state = none := hhalts.halted
  have hrun : ∀ j < t₀, (tm.runFrom (tm.initCfg inp) j).state ≠ none :=
    fun j hj => hhalts.not_halted hj
  have hsame : tm.runFrom (tm.initCfg inp) t = tm.runFrom (tm.initCfg inp) t₀ :=
    hhalts.runFrom_eq ht₀
  have hk : 2 * k ≤ 2 * k * (s + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hbound : inp.length + 2 * k + m + 2 < 2 ^ w := by unfold simBound at hw; omega
  have hfit : ∀ j ≤ t₀, ∀ i,
      Fits w (tapeAddr k inp.length i ((tm.runFrom (tm.initCfg inp) j).workTapePos i)) := by
    intro j _ i
    have h1 := tapeAddr_lt (n := inp.length) i
      (z := (tm.runFrom (tm.initCfg inp) j).workTapePos i) (d := s)
      (MultiTapeTM.natAbs_workTapePos_runFrom_le_of_runsInSpace hs j i)
    unfold Fits; unfold simBound at hw; omega
  have hout' : ∀ j ≤ t₀, (tm.runFrom (tm.initCfg inp) j).output.length < w :=
    fun j hj => lt_of_le_of_lt (length_output_runFrom_mono _ (hj.trans ht₀)) hout
  obtain ⟨x, hx₁, hsx⟩ := setupCode_spec (e := e) (w := w) tm.q₀ inp hbound
  obtain ⟨y, hy₁, hsy⟩ := loop_spec (δ := δ) hδ e hrun hhalt hfit hbound hout' t₀ 0 x
    (by omega) hsx
  obtain ⟨n, hn, hexec⟩ := hx₁.seq hy₁
  refine ⟨n + 1, ?_, ?_⟩
  · unfold simTime
    have := Nat.mul_le_mul_right (stepCost k m + 2) ht₀
    omega
  · have h := hexec.executes rVal
    rw [hsy.val, ← hsame] at h
    exact h

end Cslib.WordRAM.OfTuring

namespace Cslib.WordRAM

open Turing Turing.MultiTapeTM OfTuring

/-- **Space-bounded Turing deciders on the word RAM.** If a multi-tape machine decides `A` within
time `t a` and work space `s a ≤ D * (|enc a| + 1) ^ e`, then one fixed program over
`Basis.additive`, run on the bits of `enc a`, decides `A` within `C * t a + C` instructions at
every word size `w ≥ logWidth k |enc a|`, for constants `C` and `k > 0`. Unlike
`Cslib.WordRAM.DTIME_subset_RAMTIME_additive`, the running time need not be polynomially bounded:
the words only hold the addresses of visited cells, which the space bound controls. -/
theorem uniformDecidableInTimeLogWord_of_decidableInTimeAndSpace {α : Type} {A : Set α}
    {enc : α ↪ List Bool} {t s : α → ℕ} (h : DecidableInTimeAndSpace A enc t s) {D e : ℕ}
    (hs : ∀ a, s a ≤ D * ((enc a).length + 1) ^ e) :
    ∃ C, UniformDecidableInTimeLogWord .additive A (fun _ a => (enc a).map Bool.toNat)
      (fun a => (enc a).length) (fun a _ => C * t a + C) := by
  obtain ⟨g, ⟨K, Q, hfin, tm, htm⟩, hg⟩ := decidableInTimeAndSpace_iff.mp h
  have := Fintype.ofFinite Q
  set M := Fintype.card Q
  set D' := 2 * K * D + 2 * K + M + 3
  refine ⟨stepCost K M + 2 + 2 * K + 13, D' + (e + 1) + 2, by omega, regs K,
    simProgram tm.tr tm.q₀ (Fintype.equivFin Q), fun a w hw _ => ?_⟩
  obtain ⟨hhalt, hout⟩ := (htm a).runFrom_of_le le_rfl
  have hsp : tm.RunsInSpace (enc a) (s a) := (htm a).2.2
  set n := (enc a).length
  have hpoly : simBound K M n (s a) ≤ D' * (n + 1) ^ (e + 1) := by
    have h1 : 1 ≤ (n + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    have h2 : (n + 1) ^ (e + 1) = (n + 1) ^ e * (n + 1) := pow_succ _ _
    have h3 : (n + 1) ^ e ≤ (n + 1) ^ (e + 1) := by
      rw [h2]; exact Nat.le_mul_of_pos_right _ (by omega)
    have h4 : n + 1 ≤ (n + 1) ^ (e + 1) := by rw [h2]; exact Nat.le_mul_of_pos_left _ h1
    have h5 : 2 * K * s a ≤ 2 * K * D * (n + 1) ^ (e + 1) := by
      rw [Nat.mul_assoc (2 * K)]
      exact Nat.mul_le_mul_left _ ((hs a).trans (Nat.mul_le_mul_left _ h3))
    have h6 : (2 * K + M + 2) * 1 ≤ (2 * K + M + 2) * (n + 1) ^ (e + 1) :=
      Nat.mul_le_mul_left _ (h1.trans h3)
    unfold simBound
    simp only [D']
    nlinarith
  have hb : simBound K M n (s a) < 2 ^ w :=
    calc _ ≤ D' * (n + 1) ^ (e + 1) := hpoly
      _ < 2 ^ logWidth (D' + (e + 1)) n := lt_two_pow_logWidth _ _ _
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num)
        ((logWidth_mono (by omega) le_rfl).trans hw)
  have hw2 : 2 ≤ w := le_trans (by unfold logWidth; nlinarith) hw
  obtain ⟨r, hr, hex⟩ := executes_simProgram_of_runsInSpace (fun _ _ _ => rfl)
    (Fintype.equivFin Q) hhalt hsp hb
    (by rw [hout]; simp only [encBool_apply, List.length_singleton]; omega)
  rw [hout, encBool_apply, BitString.lsbValue_singleton] at hex
  refine ⟨(g a).toNat, r, hex, hr.trans ?_, Bool.toNat_le _, ?_⟩
  · unfold simTime
    nlinarith [Nat.zero_le (t a * (stepCost K M + 2)), Nat.zero_le ((2 * K + 13) * t a)]
  · rw [hg a]
    cases g a <;> simp

end Cslib.WordRAM
