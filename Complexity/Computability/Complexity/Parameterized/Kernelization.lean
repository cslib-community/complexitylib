/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Parameterized
public import Complexity.Computability.Complexity.Classes.Time
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Complexity.Classes.Hierarchy
import Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# Kernelization

A *kernelization* of a parameterized problem `(A, κ)` [CyganEtAl2015, Definition 2.1]
[FlumGrohe2006, Definition 9.1] is a polynomial-time map `K` from instances to instances with
`K a ∈ A ↔ a ∈ A`, whose output has encoded length and parameter at most `g (κ a)` for a function
`g` (`Cslib.Complexity.IsKernelization`). The problem *has a kernel* when it has a kernelization
(`Cslib.Complexity.HasKernel`), and a *polynomial kernel* when `g` can be chosen polynomially
bounded (`Cslib.Complexity.HasPolyKernel`). As for `Cslib.Complexity.FPT`, `g` is arbitrary,
where the cited definitions require it to be computable.

Kernels characterize fixed-parameter tractability [CaiChenDowneyFellows1997]:

* A decidable problem with a kernel is fixed-parameter tractable
  (`Cslib.Complexity.HasKernel.mem_FPT`): run the kernelization, then any decider on its output,
  whose length is bounded by a function of the parameter. Decidability is the hypothesis
  `A ∈ DTIME enc t` for some time bound `t` in the length of the encoded instance; a kernel alone
  does not make a problem decidable.
* Conversely, every fixed-parameter tractable problem over a nonempty type of instances has a
  kernel (`Cslib.Complexity.hasKernel_of_mem_FPT`). If the decider runs within
  `c (f k (L + 1) ^ e + 1)` steps, the kernelization runs it, with the universal machine
  (`Turing.MultiTapeTM.Universal.universal`), for `(c + 1) (L + 1) ^ (e + 1)` steps. If it halts,
  the kernelization outputs a fixed instance in `A` or a fixed instance outside `A` accordingly;
  if not, then `L < f k`, and the instance is its own kernel. When `A` has no instance or every
  instance, a constant map is a kernelization, so no nontriviality hypothesis is needed beyond a
  nonempty type of instances.

Problems in `P` have kernels of constant size (`Cslib.Complexity.hasPolyKernel_of_mem_P`).

## Main definitions

* `Cslib.Complexity.IsKernelization`, `Cslib.Complexity.HasKernel`,
  `Cslib.Complexity.HasPolyKernel`.

## Main results

* `Cslib.Complexity.IsKernelization.fptReducible`: every kernelization is an fpt-reduction from the
  problem to itself.
* `Cslib.Complexity.HasKernel.mem_FPT`, `Cslib.Complexity.hasKernel_of_mem_FPT`,
  `Cslib.Complexity.mem_FPT_iff_hasKernel`: a decidable problem is fixed-parameter tractable
  exactly when it has a kernel.
* `Cslib.Complexity.hasPolyKernel_of_mem_P`: problems in `P` have kernels of constant size.

## References

* [L. Cai, J. Chen, R. G. Downey, M. R. Fellows, *Advice classes of parameterized
  tractability*][CaiChenDowneyFellows1997]
* [J. Flum, M. Grohe, *Parameterized Complexity Theory*][FlumGrohe2006]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-! ### Kernels -/

section Defs

variable {α : Type*}

/-- `K` is a kernelization of the parameterized problem `(A, κ)` with size bound `g`: it is
computable in polynomial time, preserves membership in `A`, and its output has encoded length and
parameter at most `g (κ a)`. -/
structure IsKernelization (enc : α ↪ List Bool) (κ : α → ℕ) (A : Set α) (K : α → α)
    (g : ℕ → ℕ) : Prop where
  /-- The kernelization is computable in polynomial time. -/
  polyTime : ComputableInPolyTime K enc enc
  /-- The kernelization preserves membership. -/
  mem_iff : ∀ a, K a ∈ A ↔ a ∈ A
  /-- The output has encoded length bounded by a function of the parameter. -/
  length_le : ∀ a, (enc (K a)).length ≤ g (κ a)
  /-- The output has parameter bounded by a function of the parameter. -/
  parameter_le : ∀ a, κ (K a) ≤ g (κ a)

/-- The parameterized problem `(A, κ)` has a kernel: some kernelization, with some size bound. -/
def HasKernel (enc : α ↪ List Bool) (κ : α → ℕ) (A : Set α) : Prop :=
  ∃ (K : α → α) (g : ℕ → ℕ), IsKernelization enc κ A K g

/-- The parameterized problem `(A, κ)` has a polynomial kernel: a kernelization with a
polynomially bounded size bound. -/
def HasPolyKernel (enc : α ↪ List Bool) (κ : α → ℕ) (A : Set α) : Prop :=
  ∃ (K : α → α) (g : ℕ → ℕ), PolynomiallyBounded g ∧ IsKernelization enc κ A K g

theorem HasPolyKernel.hasKernel {enc : α ↪ List Bool} {κ : α → ℕ} {A : Set α}
    (h : HasPolyKernel enc κ A) : HasKernel enc κ A :=
  let ⟨K, g, _, hK⟩ := h
  ⟨K, g, hK⟩

end Defs

variable {α : Type} {enc : α ↪ List Bool} {κ : α → ℕ} {A : Set α}

/-- Every kernelization of `(A, κ)` is an fpt-reduction from `(A, κ)` to itself. -/
theorem IsKernelization.fptReducible {K : α → α} {g : ℕ → ℕ} (hK : IsKernelization enc κ A K g) :
    FPTReducible enc enc κ κ A A :=
  FPTReducible.of_computableInPolyTime hK.polyTime hK.parameter_le fun a => (hK.mem_iff a).symm

/-! ### Kernels give fixed-parameter tractability -/

/-- **A decidable problem with a kernel is fixed-parameter tractable**: run the kernelization,
then a decider on its output. -/
theorem IsKernelization.mem_FPT {K : α → α} {g : ℕ → ℕ} (hK : IsKernelization enc κ A K g)
    {t : ℕ → ℕ} (hA : A ∈ DTIME enc t) : A ∈ FPT enc κ := by
  obtain ⟨dec, tt, c, hdec, hdecA, htt⟩ :=
    (mem_DTIME_iff_decidableInTimeO.mp hA).exists_computableInO
  have hdec := hdec.tidy
  obtain ⟨d, _, hKd⟩ := hK.polyTime.tidy.exists_degree
  have htt' : ∀ a, tt (K a) ≤ c * (∑ j ∈ Finset.range (g (κ a) + 1), t j) + c := fun a => by
    have h₁ : tt (K a) ≤ c * t (enc (K a)).length + c := by exact_mod_cast htt (K a)
    have h₂ : t (enc (K a)).length ≤ ∑ j ∈ Finset.range (g (κ a) + 1), t j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (hK.length_le a)))
    have := Nat.mul_le_mul_left c h₂
    omega
  have key : ∀ a, ((enc a).length + 1) ^ d + tt (K a) ≤
      (1 + (c * (∑ j ∈ Finset.range (g (κ a) + 1), t j) + c)) * ((enc a).length + 1) ^ d := by
    intro a
    have hP : 1 ≤ ((enc a).length + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have h₁ := (htt' a).trans (Nat.le_mul_of_pos_right _ hP)
    rw [Nat.add_mul, Nat.one_mul]
    omega
  exact mem_FPT_iff_computableInFPTTime.mpr ⟨dec ∘ K,
    ComputableInO.computableInFPTTime
      (F := fun k => 1 + (c * (∑ j ∈ Finset.range (g k + 1), t j) + c)) (c := d)
      (.of_tidy ((hdec.comp hKd.inO).mono_le key key)),
    fun a => (hK.mem_iff a).symm.trans (hdecA (K a))⟩

/-- **A decidable problem with a kernel is fixed-parameter tractable.** -/
theorem HasKernel.mem_FPT (h : HasKernel enc κ A) {t : ℕ → ℕ} (hA : A ∈ DTIME enc t) :
    A ∈ FPT enc κ :=
  let ⟨_, _, hK⟩ := h
  hK.mem_FPT hA

/-! ### Fixed-parameter tractability gives kernels -/

/-- A constant map is a kernelization of a problem with no instance or every instance. -/
private theorem hasKernel_of_forall (a₀ : α) (h : ∀ a, a ∈ A ↔ a₀ ∈ A) : HasKernel enc κ A :=
  ⟨fun _ => a₀, fun _ => (enc a₀).length + κ a₀,
    ⟨.const a₀, fun a => (h a).symm, fun _ => Nat.le_add_right _ _, fun _ => Nat.le_add_left _ _⟩⟩

/-- The arithmetic of the clocked run: if `(c + 1) (L + 1) ^ (e + 1) < c (F (L + 1) ^ e) + c`,
then `L < F`. -/
private theorem lt_of_clock_lt {c e L F : ℕ}
    (h : (c + 1) * (L + 1) ^ (e + 1) < c * (F * (L + 1) ^ e) + c) : L < F := by
  by_contra hF
  have hP : 1 ≤ (L + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos L)
  have h₁ : (F + 1) * (L + 1) ^ e ≤ (L + 1) ^ (e + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm _ (L + 1)]
    exact Nat.mul_le_mul_right _ (by omega)
  have h₂ := Nat.mul_le_mul_left (c + 1) h₁
  have h₃ := Nat.mul_le_mul_left c hP
  have h₄ : (c + 1) * ((F + 1) * (L + 1) ^ e) =
      c * (F * (L + 1) ^ e) + c * (L + 1) ^ e + (F + 1) * (L + 1) ^ e := by ring
  nlinarith

/-- **Fixed-parameter tractable problems have kernels** [CaiChenDowneyFellows1997]: run the
decider with a clock `(c + 1) (L + 1) ^ (e + 1)`; on timeout the instance is short. -/
theorem hasKernel_of_mem_FPT [Nonempty α] (hA : A ∈ FPT enc κ) : HasKernel enc κ A := by
  by_cases hy : ∃ y, y ∈ A
  swap
  · simp only [not_exists] at hy
    exact hasKernel_of_forall (Classical.arbitrary α) fun a =>
      ⟨fun h => absurd h (hy a), fun h => absurd h (hy _)⟩
  by_cases hn : ∃ n, n ∉ A
  swap
  · simp only [not_exists, not_not] at hn
    exact hasKernel_of_forall (Classical.arbitrary α) fun a => ⟨fun _ => hn _, fun _ => hn a⟩
  obtain ⟨y, hyA⟩ := hy
  obtain ⟨n, hnA⟩ := hn
  obtain ⟨f, e, c, t, s, ht, k, State, hfin, tm, htm⟩ := hA
  have ht' : ∀ a, t a ≤ c * (f (κ a) * ((enc a).length + 1) ^ e) + c := fun a => by
    have := ht a
    dsimp only at this
    exact_mod_cast this
  have : Fintype State := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  -- the clock, in unary
  let N : α → ℕ := fun a => (c + 1) * ((enc a).length + 1) ^ (e + 1)
  -- the clocked run of the decider
  let r : α → List ℕ × Bool := fun a => universal (desc eS eBit tm, (enc a).map eBit, N a)
  let K : α → α := fun a => if Diagonal.verdict (r a) then (if (r a).2 then n else a) else y
  -- polynomial time
  have hN : ComputableTidilyInPolyTime N enc encUnary := by
    have hL := ComputableTidilyInPolyTime.encoding_length enc
    have hS : ComputableTidilyInPolyTime (fun a => (enc a).length + 1) enc encUnary :=
      ComputableTidilyInPolyTime.unary_add.comp (hL.prod (ComputableTidilyInPolyTime.const 1))
    have hP := (ComputableTidilyInPolyTime.unary_pow (e + 1)).comp hS
    exact ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const (c + 1)).prod hP)
  have hin : ComputableTidilyInPolyTime (fun a => (desc eS eBit tm, (enc a).map eBit, N a)) enc
      (encPair eDesc (encPair (encList encUnary) encUnary)) :=
    (ComputableTidilyInPolyTime.const _).prod
      ((Universal.computableTidilyInDegree_map_eBit.computableTidilyInPolyTime.comp
        (ComputableTidilyInPolyTime.encode enc)).prod hN)
  have hr : ComputableTidilyInPolyTime r enc eOut := computableTidilyInPolyTime_universal.comp hin
  have hverdict : ComputableTidilyInPolyTime Diagonal.verdict eOut encBool :=
    Diagonal.computableInO_verdict.tidy.computableTidilyInPolyTime
      (.of_forall_le 1 2 fun _ => by simp) (.of_forall_le 1 1 fun _ => by simp)
  have hK : ComputableTidilyInPolyTime K enc enc :=
    ComputableTidilyInPolyTime.ite' (hverdict.comp hr)
      (ComputableTidilyInPolyTime.ite'
        ((ComputableTidilyInPolyTime.snd (encList encUnary) encBool).comp hr)
        (ComputableTidilyInPolyTime.const n) ComputableTidilyInPolyTime.id')
      (ComputableTidilyInPolyTime.const y)
  -- the behaviour of the clocked run
  have hrun : ∀ a, (K a = y ∧ a ∈ A) ∨ (K a = n ∧ a ∉ A) ∨
      (K a = a ∧ (enc a).length < f (κ a)) := by
    intro a
    obtain ⟨hcomp, hrt, -⟩ := htm a
    obtain ⟨h, hht, hh⟩ := exists_haltsAt_of_runsInTime hrt
    have hr_eq : r a = ((tm.runFrom (tm.initCfg (enc a)) (N a)).output.map eBit,
        (tm.runFrom (tm.initCfg (enc a)) (N a)).state.isNone) :=
      universal_desc eS eBit tm (enc a) (N a)
    by_cases hhN : h ≤ N a
    · have hrN := hh.runFrom_eq hhN
      have hhalt : (tm.runFrom (tm.initCfg (enc a)) (N a)).state = none := by
        rw [hrN]
        exact hh.halted
      have hout : (tm.runFrom (tm.initCfg (enc a)) (N a)).output = [indicator A a] := by
        rw [hrN]
        exact output_haltsAt hcomp hh
      rw [hout, hhalt] at hr_eq
      by_cases haA : a ∈ A
      · left
        have hi : indicator A a = true := by simp [indicator, haA]
        refine ⟨?_, haA⟩
        simp only [K, hr_eq, hi, Diagonal.verdict]
        simp
      · right; left
        have hi : indicator A a = false := by simp [indicator, haA]
        refine ⟨?_, haA⟩
        simp only [K, hr_eq, hi, Diagonal.verdict]
        simp [eBit]
    · right; right
      have hnot : (tm.runFrom (tm.initCfg (enc a)) (N a)).state.isNone = false := by
        rw [Option.isNone_eq_false_iff, Option.isSome_iff_ne_none]
        exact fun h' => hhN (hh.le_of_halted h')
      rw [hnot] at hr_eq
      refine ⟨?_, lt_of_clock_lt (c := c) (lt_of_lt_of_le (not_le.mp hhN)
        (hht.trans (ht' a)))⟩
      simp only [K, hr_eq, Diagonal.verdict]
      simp
  refine ⟨K, fun k => f k + (enc y).length + (enc n).length + κ y + κ n + k,
    ⟨hK.computableInPolyTime, fun a => ?_, fun a => ?_, fun a => ?_⟩⟩
  · rcases hrun a with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, -⟩ <;> rw [h₁]
    · exact iff_of_true hyA h₂
    · exact iff_of_false hnA h₂
  · rcases hrun a with ⟨h₁, -⟩ | ⟨h₁, -⟩ | ⟨h₁, h₂⟩ <;> rw [h₁] <;> omega
  · rcases hrun a with ⟨h₁, -⟩ | ⟨h₁, -⟩ | ⟨h₁, -⟩ <;> rw [h₁] <;> omega

/-- **Kernels characterize fixed-parameter tractability** [CaiChenDowneyFellows1997]: a decidable
problem over a nonempty type of instances is fixed-parameter tractable exactly when it has a
kernel. -/
theorem mem_FPT_iff_hasKernel [Nonempty α] {t : ℕ → ℕ} (hA : A ∈ DTIME enc t) :
    A ∈ FPT enc κ ↔ HasKernel enc κ A :=
  ⟨hasKernel_of_mem_FPT, fun h => h.mem_FPT hA⟩

/-! ### Problems in `P` -/

/-- Constant size bounds are polynomially bounded. -/
private theorem polynomiallyBounded_const (C : ℕ) : PolynomiallyBounded fun _ => C :=
  polynomiallyBounded_iff_le.mpr ⟨C, 0, fun _ => by simp⟩

/-- **Problems in `P` have kernels of constant size**, over a nonempty type of instances: decide
the instance, and output a fixed instance with the same answer. -/
theorem hasPolyKernel_of_mem_P [Nonempty α] (hA : A ∈ P enc) : HasPolyKernel enc κ A := by
  have hconst : ∀ a₀ : α, (∀ a, a ∈ A ↔ a₀ ∈ A) → HasPolyKernel enc κ A := fun a₀ h =>
    ⟨fun _ => a₀, fun _ => (enc a₀).length + κ a₀, polynomiallyBounded_const _,
      ⟨.const a₀, fun a => (h a).symm, fun _ => Nat.le_add_right _ _,
        fun _ => Nat.le_add_left _ _⟩⟩
  by_cases hy : ∃ y, y ∈ A
  swap
  · simp only [not_exists] at hy
    exact hconst (Classical.arbitrary α) fun a =>
      ⟨fun h => absurd h (hy a), fun h => absurd h (hy _)⟩
  by_cases hn : ∃ n, n ∉ A
  swap
  · simp only [not_exists, not_not] at hn
    exact hconst (Classical.arbitrary α) fun a => ⟨fun _ => hn _, fun _ => hn a⟩
  obtain ⟨y, hyA⟩ := hy
  obtain ⟨n, hnA⟩ := hn
  obtain ⟨dec, hdec, hdecA⟩ := hA
  refine ⟨fun a => if dec a then y else n,
    fun _ => (enc y).length + (enc n).length + κ y + κ n, polynomiallyBounded_const _,
    ⟨by fun_prop, fun a => ?_, fun a => ?_, fun a => ?_⟩⟩
  · rw [hdecA a]
    cases dec a
    · exact iff_of_false hnA Bool.false_ne_true
    · exact iff_of_true hyA rfl
  all_goals split_ifs <;> omega

end Cslib.Complexity
