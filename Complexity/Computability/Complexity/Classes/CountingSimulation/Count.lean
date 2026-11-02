/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.Assembly
public import Complexity.Computability.Complexity.Classes.Time.AcceptCount
public import Complexity.Computability.Complexity.Classes.FunctionTime
public import Complexity.Computability.Complexity.Classes.SharpP.Time
import Complexity.Computability.Machines.Turing.MultiTape.Counting.ChoiceTable

/-!
# Exact counting before decision-class comparisons

The counting simulation computes a natural number, not merely a verdict. This module exposes
its exact padded acceptance counts and their joint deterministic time/workspace bounds.
Polynomial-time comparisons are postprocessing of that count and its clock; decision-class
containments are derived in `CountingSimulation.Containments`.

`NetworkFamilies` is the network-construction interface for all finite-state binary-choice
machines. The explicit block networks discharge it. A contraction algorithm is still a
hypothesis of the generic results here. Counts of padded choice strings are distinguished from
native terminal-path counts: halted choice replays ignore remaining bits, while a terminal path
is counted once. The latter is the convention of `SharpTIME`; its binary replay forces a unique zero
continuation
after each halt. The resulting exact counting theorem computes `SharpTIME` functions in binary
within the same time scale and polynomial workspace.

## Main definitions

* `Cslib.Complexity.CountingSimulation.NetworkFamilies`: network families for all machines.

## Main results

* `exists_computableInTimeAndSpace_countWith`: polynomial-time postprocessing with joint bounds.
* `exists_computableInTimeAndSpace_acceptCount`: exact padded acceptance counting, in binary.
* `exists_computableInTimeAndSpace_of_mem_SharpTIME`: joint bounds for terminal-path counting.
* `SharpTIME_subset_iUnion_FTIME`: the functional counting-class containment.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM

variable {N : Type} {encN : N ↪ List Bool} {value : N → ℕ} {Admissible : ℕ → ℕ → N → Prop}
  {α : Type} {enc : α ↪ List Bool} {T : ℕ → ℕ}

/-- **Network families for all machines**: for every finite-state fair-coin machine, a network
family (`Cslib.Complexity.CountingSimulation.NetworkFamily`) for its accept count
`Turing.MultiTapePTM.acceptCount`. This is the hypothesis supplied by the block-counting step of
#1833. -/
@[expose] def NetworkFamilies (encN : N ↪ List Bool) (value : N → ℕ)
    (Admissible : ℕ → ℕ → N → Prop) :
    Prop :=
  ∀ (k : ℕ) (State : Type) [Finite State] (M : MultiTapePTM k Bool State),
    Nonempty (NetworkFamily encN value Admissible fun x τ => M.acceptCount x τ)

/-- Polynomial-time postprocessing of the exact accepting count, with the padded clock in
unary, preserves the counting simulation's time scale and polynomial workspace. -/
theorem exists_computableInTimeAndSpace_countWith
    (hnet : NetworkFamilies encN value Admissible)
    (A : ContractionAlgorithm encN value Admissible) (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) {k : ℕ} {State : Type} [Finite State]
    (M : MultiTapePTM k Bool State) {c : ℕ} (hc : 1 ≤ c)
    {β : Type} {encOut : β ↪ List Bool} {rule : ℕ × ℕ → β}
    (hrule : ComputableInPolyTime rule (encPair encUnary encNat) encOut) :
    ∃ C d : ℕ, ComputableInTimeAndSpace
      (fun a => rule (paddedTime (c * T (enc a).length),
        M.acceptCount (enc a) (paddedTime (c * T (enc a).length)))) enc encOut
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) := by
  obtain ⟨F⟩ := hnet k State M
  obtain ⟨C, d, h⟩ := exists_computableInO_countWith F A
    (fun x τ => Complexity.acceptCount_le_two_pow) hT hTn hc hrule
  obtain ⟨K, hK, -⟩ := h.of_encIn_eq enc fun a => rfl
  refine ⟨(K + K + 1) * (C + 1), K + K + 2 * d,
    hK.mono (fun a => ?_) fun a => ?_⟩
  · have h2 : 2 ≤ T (enc a).length := (le_max_right _ _).trans (hTn _)
    have := Nat.mul_two_pow_div_sqrt_log_two_add_le (a := K) (b := K) (C := C) h2
    simp only [Function.comp_apply, Nat.mul_add, Nat.mul_one] at this ⊢
    exact this
  · have h2 : 2 ≤ T (enc a).length := (le_max_right _ _).trans (hTn _)
    have hpow : T (enc a).length ^ d ≤ (T (enc a).length + 1) ^ d :=
      Nat.pow_le_pow_left (Nat.le_succ _) d
    have := Nat.mul_add_one_pow_add_le_pow (a := K) (b := K) (d := d) h2
    simp only [Function.comp_apply]
    calc K * (T (enc a).length ^ d + 1) ≤ K * (T (enc a).length + 1) ^ d + K := by
          rw [Nat.mul_add, Nat.mul_one]
          exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hpow) _
      _ ≤ _ := this

/-- The accepting choice strings at the padded clock are counted exactly, with binary output,
by one deterministic machine carrying both the subexponential time and polynomial-space bounds. -/
theorem exists_computableInTimeAndSpace_acceptCount
    (hnet : NetworkFamilies encN value Admissible)
    (A : ContractionAlgorithm encN value Admissible) (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) {k : ℕ} {State : Type} [Finite State]
    (M : MultiTapePTM k Bool State) {c : ℕ} (hc : 1 ≤ c) :
    ∃ C d : ℕ, ComputableInTimeAndSpace
      (fun a => M.acceptCount (enc a) (paddedTime (c * T (enc a).length))) enc encNat
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) :=
  exists_computableInTimeAndSpace_countWith hnet A hT hTn M hc
    (rule := Prod.snd) (by fun_prop)

/-- Exact terminal-path counting inherits the counting simulation's subexponential time and
polynomial workspace. The binary replay chooses transition occurrences parsimoniously and
forces zero padding after a native halt, so no post-halting multiplicity is introduced. -/
theorem exists_computableInTimeAndSpace_of_mem_SharpTIME
    (hnet : NetworkFamilies encN value Admissible)
    (A : ContractionAlgorithm encN value Admissible) (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) {f : α → ℕ} (hf : f ∈ SharpTIME enc T) :
    ∃ C d : ℕ, ComputableInTimeAndSpace f enc encNat
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) := by
  obtain ⟨c₁, c₂, k, State, hfinite, machine, _, hm⟩ := hf
  obtain ⟨bound, hbound⟩ := machine.exists_branchBound
  let width := bound + 1
  have hw : 0 < width := Nat.zero_lt_succ _
  have hcodes (input : List Bool) (cfg : Cfg k Bool State input) :
      (machine.actions cfg).length ≤ 2 ^ width :=
    (hbound input cfg).trans ((Nat.le_succ bound).trans
      (show width < 2 ^ width from Nat.lt_two_pow_self).le)
  let c := width * (c₁ + c₂ + 1) + 1
  obtain ⟨C, d, h⟩ := exists_computableInTimeAndSpace_acceptCount hnet A hT hTn
    (MultiTapeCTM.CountingChoice.table hw machine) (c := c) (by omega)
  have heq : (fun a => (MultiTapeCTM.CountingChoice.table hw machine).acceptCount
      (enc a) (paddedTime (c * T (enc a).length))) = f := by
    funext a
    obtain ⟨hhalt, hcount⟩ := hm a
    have hTpos : 1 ≤ T (enc a).length :=
      (by omega : 1 ≤ max (enc a).length 2).trans (hTn _)
    have hlin : c₁ * T (enc a).length + c₂ ≤ (c₁ + c₂ + 1) * T (enc a).length := by
      nlinarith
    have hle : (c₁ * T (enc a).length + c₂) * width ≤
        paddedTime (c * T (enc a).length) := by
      calc _ ≤ ((c₁ + c₂ + 1) * T (enc a).length) * width :=
          Nat.mul_le_mul_right _ hlin
        _ ≤ c * T (enc a).length := by dsimp [c]; nlinarith
        _ ≤ _ := le_paddedTime _
    rw [MultiTapeCTM.CountingChoice.acceptCount_table_of_halts hw machine (enc a)
      (hcodes (enc a)) hhalt hle]
    exact hcount
  rw [heq] at h
  exact ⟨C, d, h⟩

/-- The functional counting counterpart of the decision-class simulations: every terminal-path
counter in `#TIME(T)` has binary output in `FTIME(2^(C T / √log T))` for some constant `C`. -/
theorem SharpTIME_subset_iUnion_FTIME
    (hnet : NetworkFamilies encN value Admissible)
    (A : ContractionAlgorithm encN value Admissible) (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) :
    SharpTIME enc T ⊆ ⋃ C : ℕ,
      FTIME enc encNat (fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n)))) := by
  intro f hf
  obtain ⟨C, d, h⟩ := exists_computableInTimeAndSpace_of_mem_SharpTIME hnet A hT hTn hf
  exact Set.mem_iUnion.mpr ⟨C, FTIME.of_computableInTimeAndSpace (s := fun n => T n ^ d) h⟩

end Cslib.Complexity.CountingSimulation
