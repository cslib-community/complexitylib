/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.BruteForce
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Reduction.ManyOne
import Complexity.Computability.Complexity.Classes.Time
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Fixed-parameter tractability

A *parameterized problem* is a problem `A : Set α` with an encoding `enc : α ↪ List Bool` of its
instances and a *parameter* `κ : α → ℕ` [DowneyFellows1999] [FlumGrohe2006] [CyganEtAl2015]. The
parameter is any function of the instance: the number of variables of a formula, the size of a
solution sought, a width. Running times are measured in the parameter `k = κ a` and in the length
`L` of the encoded instance, on the multi-tape machines of `Cslib.Complexity.DecidableInTimeO`.

* `Cslib.Complexity.FPT enc κ`, **fixed-parameter tractability**: decidability within time
  `f k * (L + 1) ^ c` up to a constant factor, for some function `f : ℕ → ℕ` and constant `c`.
  The exponent of `L` does not depend on `k`.
* `Cslib.Complexity.XP enc κ`, **slicewise polynomial time**: decidability within time
  `f k * (L + 1) ^ g k`, for functions `f` and `g`.

The function `f` is arbitrary, as in the *uniform* fixed-parameter tractability of Downey and
Fellows [DowneyFellows1999, Chapter 2]. Flum and Grohe [FlumGrohe2006, Chapter 1] and Cygan et
al. [CyganEtAl2015, Chapter 1] require `f` to be computable (Downey and Fellows' *strongly
uniform* tractability); that variant is not formalized here. The function `f` may be taken
monotone (`Cslib.Complexity.mem_FPT_iff_exists_monotone`).

`Cslib.Complexity.FPTReducible encA encB κA κB A B`: `A` reduces to `B` by an *fpt-reduction*
[FlumGrohe2006, Definition 2.1] [CyganEtAl2015, Definition 13.1]: a map `f` computable by some
machine within time `F (κA a) * (L + 1) ^ c` (`Cslib.Complexity.ComputableInFPTTime`) with
`a ∈ A ↔ f a ∈ B` and `κB (f a) ≤ h (κA a)` for a function `h`. Fpt-time computability is closed
under case distinction and under composition along a function that bounds the parameter
(`Cslib.Complexity.ComputableInFPTTime.ite`, `Cslib.Complexity.ComputableInFPTTime.comp`), and
polynomial time is fpt time for every parameter
(`Turing.MultiTapeTM.ComputableInPolyTime.computableInFPTTime`). Polynomial-time
reductions with a parameter bound are fpt-reductions
(`Cslib.Complexity.FPTReducible.of_computableInPolyTime`). `FPT` and `XP` are closed under
fpt-reductions. As for `FPT`, the functions `F` and `h` are arbitrary, where the cited
definitions require them to be computable.

## Main definitions

* `Cslib.Complexity.FPT`, `Cslib.Complexity.XP`: fixed-parameter tractable and slicewise
  polynomial problems.
* `Cslib.Complexity.ComputableInFPTTime`: functions computable in fpt time.
* `Cslib.Complexity.FPTReducible`: fpt-reductions.

## Main results

* `Cslib.Complexity.mem_FPT`, `Cslib.Complexity.mem_XP`: unfolding the classes.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.computableInFPTTime`: a time bound alone gives
  fpt-time computability.
* `Turing.MultiTapeTM.ComputableInPolyTime.computableInFPTTime`,
  `Cslib.Complexity.ComputableInFPTTime.ite`, `Cslib.Complexity.ComputableInFPTTime.comp`:
  polynomial time is fpt time, and fpt time is closed under case distinction and composition.
* `Cslib.Complexity.mem_FPT_iff_computableInFPTTime`: `FPT` in terms of fpt-time computability.
* `Cslib.Complexity.P_subset_FPT`, `Cslib.Complexity.FPT_subset_XP`: `P ⊆ FPT ⊆ XP`, for every
  parameter.
* `Cslib.Complexity.FPT_eq_P_of_le`, `Cslib.Complexity.XP_eq_P_of_le`: for a bounded parameter,
  both classes are `P`.
* `Cslib.Complexity.FPT_subset_FPT_of_le_comp`, `Cslib.Complexity.XP_subset_XP_of_le_comp`: if
  `κ a ≤ h (κ' a)` then tractability in `κ` gives tractability in `κ'`.
* `Cslib.Complexity.mem_FPT_iff_exists_monotone`: the function `f` may be taken monotone.
* `Cslib.Complexity.DecidableInExpTime.mem_FPT`: time `2 ^ (δ κ a)` times a polynomial is fpt
  time; so `SAT` and `k`-SAT are fixed-parameter tractable in the number of variables
  (`Cslib.Complexity.SAT_mem_FPT`, `Cslib.Complexity.KSAT_mem_FPT`).
* `Cslib.Complexity.compl_mem_FPT`, `Cslib.Complexity.inter_mem_FPT`,
  `Cslib.Complexity.union_mem_FPT`, `Cslib.Complexity.compl_mem_XP`: Boolean closure.
* `Cslib.Complexity.FPTReducible.refl`, `Cslib.Complexity.FPTReducible.trans`: fpt-reducibility
  is a preorder; `Cslib.Complexity.FPTReducible.compl` passes to complements.
* `Cslib.Complexity.FPTReducible.mem_FPT`, `Cslib.Complexity.FPTReducible.mem_XP`: `FPT` and `XP`
  are closed under fpt-reductions.

## References

* [R. G. Downey, M. R. Fellows, *Parameterized Complexity*][DowneyFellows1999]
* [J. Flum, M. Grohe, *Parameterized Complexity Theory*][FlumGrohe2006]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Monotone majorants -/

/-- The partial sums of `f` bound `f` from above. -/
private theorem le_sum_range_succ {f : ℕ → ℕ} {i k : ℕ} (h : i ≤ k) :
    f i ≤ ∑ j ∈ Finset.range (k + 1), f j :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

/-- The partial sums of `f` are monotone. -/
private theorem monotone_sum_range_succ (f : ℕ → ℕ) :
    Monotone fun k => ∑ j ∈ Finset.range (k + 1), f j :=
  fun _ _ h => Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ h))

/-! ### The classes -/

section Classes

variable {α : Type*}

/-- **Fixed-parameter tractability.** `A ∈ FPT enc κ` when `A` is decidable within time
`f (κ a) * (|enc a| + 1) ^ c` up to a constant factor, for some function `f : ℕ → ℕ` and some
constant `c`, by a machine with a binary alphabet reading `enc a`
(`Cslib.Complexity.DecidableInTimeO`). The function `f` is arbitrary, as in the uniform
fixed-parameter tractability of [DowneyFellows1999]; [FlumGrohe2006] also requires it to be
computable. -/
def FPT (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  {A | ∃ (f : ℕ → ℕ) (c : ℕ), DecidableInTimeO A enc fun a => f (κ a) * ((enc a).length + 1) ^ c}

/-- **Slicewise polynomial time.** `A ∈ XP enc κ` when a single machine decides `A` within time
`f (κ a) * (|enc a| + 1) ^ g (κ a)` up to a constant factor, for some functions `f` and `g`
[DowneyFellows1999] [FlumGrohe2006]: in particular each slice `{a | κ a = k}` is decidable in
polynomial time, with a degree depending on `k`. The functions `f` and `g` are arbitrary, where
[FlumGrohe2006] and [CyganEtAl2015] require them to be computable. -/
def XP (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  {A | ∃ f g : ℕ → ℕ,
    DecidableInTimeO A enc fun a => f (κ a) * ((enc a).length + 1) ^ g (κ a)}

variable {enc : α ↪ List Bool} {κ κ' : α → ℕ} {A : Set α}

/-- Membership in `FPT`: decidability within time `f (κ a) * (|enc a| + 1) ^ c` up to a constant
factor, for some function `f` and constant `c`. -/
theorem mem_FPT : A ∈ FPT enc κ ↔
    ∃ (f : ℕ → ℕ) (c : ℕ), DecidableInTimeO A enc fun a => f (κ a) * ((enc a).length + 1) ^ c :=
  Iff.rfl

/-- Membership in `XP`: decidability within time `f (κ a) * (|enc a| + 1) ^ g (κ a)` up to a
constant factor, for some functions `f` and `g`. -/
theorem mem_XP : A ∈ XP enc κ ↔ ∃ f g : ℕ → ℕ,
    DecidableInTimeO A enc fun a => f (κ a) * ((enc a).length + 1) ^ g (κ a) :=
  Iff.rfl

/-- Changing the parameter and the functions of a bound of the shape of `XP`. -/
private theorem decidableInTimeO_mono_parameter {f f' g g' : ℕ → ℕ}
    (hf : ∀ a, f (κ a) ≤ f' (κ' a)) (hg : ∀ a, g (κ a) ≤ g' (κ' a))
    (h : DecidableInTimeO A enc fun a => f (κ a) * ((enc a).length + 1) ^ g (κ a)) :
    DecidableInTimeO A enc fun a => f' (κ' a) * ((enc a).length + 1) ^ g' (κ' a) := by
  refine h.mono 1 (fun a => ?_) fun a => by positivity
  have hL : (1 : ℝ) ≤ (enc a).length + 1 := by
    linarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _)]
  have h₁ : (f (κ a) : ℝ) ≤ f' (κ' a) := by exact_mod_cast hf a
  have h₂ : (((enc a).length : ℝ) + 1) ^ g (κ a) ≤ ((enc a).length + 1) ^ g' (κ' a) :=
    pow_le_pow_right₀ hL (hg a)
  have := mul_le_mul h₁ h₂ (by positivity) (by positivity)
  push_cast
  linarith

/-- **`FPT ⊆ XP`.** -/
theorem FPT_subset_XP : FPT enc κ ⊆ XP enc κ :=
  fun _ ⟨f, c, h⟩ => ⟨f, fun _ => c, h⟩

/-- **`P ⊆ FPT`**, for every parameter: a polynomial-time decider is an fpt-time decider with
`f = 1`. -/
theorem P_subset_FPT : P enc ⊆ FPT enc κ := by
  intro A hA
  obtain ⟨k, hk⟩ := mem_P_iff_exists_mem_DTIME.mp hA
  refine ⟨fun _ => 1, k,
    (mem_DTIME_iff_decidableInTimeO.mp hk).mono 1 (fun a => ?_) fun a => by positivity⟩
  have : ((enc a).length : ℝ) ^ k ≤ ((enc a).length + 1) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  push_cast
  linarith

/-- **`P ⊆ XP`**, for every parameter. -/
theorem P_subset_XP : P enc ⊆ XP enc κ :=
  P_subset_FPT.trans FPT_subset_XP

/-- **Changing the parameter.** If `κ a ≤ h (κ' a)` for a function `h`, then a problem that is
fixed-parameter tractable in `κ` is fixed-parameter tractable in `κ'`. -/
theorem FPT_subset_FPT_of_le_comp {h : ℕ → ℕ} (hκ : ∀ a, κ a ≤ h (κ' a)) :
    FPT enc κ ⊆ FPT enc κ' := fun _ ⟨f, c, hA⟩ =>
  ⟨fun k => ∑ j ∈ Finset.range (h k + 1), f j, c,
    decidableInTimeO_mono_parameter (f := f) (f' := fun k => ∑ j ∈ Finset.range (h k + 1), f j)
      (g := fun _ => c) (g' := fun _ => c) (fun a => le_sum_range_succ (hκ a)) (fun _ => le_rfl)
      hA⟩

/-- **Changing the parameter.** If `κ a ≤ h (κ' a)` for a function `h`, then a problem that is
slicewise polynomial in `κ` is slicewise polynomial in `κ'`. -/
theorem XP_subset_XP_of_le_comp {h : ℕ → ℕ} (hκ : ∀ a, κ a ≤ h (κ' a)) :
    XP enc κ ⊆ XP enc κ' := fun _ ⟨f, g, hA⟩ =>
  ⟨fun k => ∑ j ∈ Finset.range (h k + 1), f j, fun k => ∑ j ∈ Finset.range (h k + 1), g j,
    decidableInTimeO_mono_parameter (f := f) (f' := fun k => ∑ j ∈ Finset.range (h k + 1), f j)
      (g := g) (g' := fun k => ∑ j ∈ Finset.range (h k + 1), g j)
      (fun a => le_sum_range_succ (hκ a)) (fun a => le_sum_range_succ (hκ a)) hA⟩

/-- **The function of an fpt bound may be taken monotone**: replace `f` by its partial sums. -/
theorem mem_FPT_iff_exists_monotone :
    A ∈ FPT enc κ ↔ ∃ f : ℕ → ℕ, Monotone f ∧
      ∃ c : ℕ, DecidableInTimeO A enc fun a => f (κ a) * ((enc a).length + 1) ^ c := by
  refine ⟨fun ⟨f, c, hA⟩ => ⟨_, monotone_sum_range_succ f, c,
    decidableInTimeO_mono_parameter (f := f) (f' := fun k => ∑ j ∈ Finset.range (k + 1), f j)
      (g := fun _ => c) (g' := fun _ => c) (fun a => le_sum_range_succ le_rfl) (fun _ => le_rfl)
      hA⟩,
    fun ⟨f, _, c, hA⟩ => ⟨f, c, hA⟩⟩

/-- **Exponential time in the parameter is fpt time.** A decider within time `2 ^ (δ κ a)` times
a polynomial in the length of the encoded instance, for any real `δ`, is an fpt-time decider with
`f k = ⌈2 ^ δ⌉ ^ k`. -/
theorem DecidableInExpTime.mem_FPT {δ : ℝ} (h : DecidableInExpTime A enc κ δ) :
    A ∈ FPT enc κ := by
  obtain ⟨e, h⟩ := h
  refine ⟨fun k => ⌈(2 : ℝ) ^ δ⌉₊ ^ k, e, h.mono 1 (fun a => ?_) fun a => by positivity⟩
  have h₁ : (2 : ℝ) ^ (δ * κ a) = ((2 : ℝ) ^ δ) ^ (κ a) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have h₂ : ((2 : ℝ) ^ δ) ^ (κ a) ≤ (⌈(2 : ℝ) ^ δ⌉₊ : ℝ) ^ (κ a) :=
    pow_le_pow_left₀ (by positivity) (Nat.le_ceil _) _
  have := mul_le_mul_of_nonneg_right (h₁ ▸ h₂)
    (by positivity : (0 : ℝ) ≤ ((enc a).length + 1) ^ e)
  push_cast
  linarith

/-- **`SAT` is fixed-parameter tractable in the number of variables**, by exhaustive search. -/
theorem SAT_mem_FPT : SAT ∈ FPT encCNF CNF.numVars :=
  SAT_decidableInExpTime_one.mem_FPT

/-- **`k`-SAT is fixed-parameter tractable in the number of variables**, by exhaustive search. -/
theorem KSAT_mem_FPT (k : ℕ) : KSAT k ∈ FPT encCNF CNF.numVars :=
  (KSAT_decidableInExpTime_one k).mem_FPT

end Classes

/-! ### Fpt-time computability -/

section Machines

/-- `f` is computable in fpt time with respect to the parameter `κ`: some machine computes `f`
within time and space `F (κ a) * (|encA a| + 1) ^ c`, for a function `F : ℕ → ℕ` and a constant
`c`. Bounding the space by the same expression is no restriction, since a machine within time `t`
visits at most `k t + k` work-tape cells
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.computableInFPTTime`). -/
def ComputableInFPTTime {α β : Type*} (f : α → β) (encA : α ↪ List Bool)
    (encB : β ↪ List Bool) (κ : α → ℕ) : Prop :=
  ∃ (F : ℕ → ℕ) (c : ℕ), ComputableInTimeAndSpace f encA encB
    (fun a => F (κ a) * ((encA a).length + 1) ^ c) fun a => F (κ a) * ((encA a).length + 1) ^ c

section Plain

variable {α β : Type*} {f : α → β} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κ : α → ℕ}

/-- A function computable in fpt time is computed within the same bound, up to a constant factor:
the output is within the time bound, which is also the space bound. -/
private theorem ComputableInFPTTime.exists_computableInO
    (h : ComputableInFPTTime f encA encB κ) :
    ∃ (F : ℕ → ℕ) (c : ℕ), ComputableInO f encA encB
      (fun a => F (κ a) * ((encA a).length + 1) ^ c) fun a => F (κ a) * ((encA a).length + 1) ^ c :=
  let ⟨F, c, hc⟩ := h
  ⟨F, c, .of_bounds hc 1 (fun _ => by omega) (fun _ => by omega)
    fun a => (hc.length_le a).trans (by omega)⟩

/-- A computation within an fpt bound, up to a constant factor, is a computation in fpt time. -/
theorem _root_.Turing.MultiTapeTM.ComputableInO.computableInFPTTime {F : ℕ → ℕ} {c : ℕ}
    (h : ComputableInO f encA encB (fun a => F (κ a) * ((encA a).length + 1) ^ c)
      fun a => F (κ a) * ((encA a).length + 1) ^ c) :
    ComputableInFPTTime f encA encB κ := by
  obtain ⟨d, hd, -⟩ := h
  have hle (a : α) : d * (F (κ a) * ((encA a).length + 1) ^ c + 1) ≤
      d * (F (κ a) + 1) * ((encA a).length + 1) ^ c := by
    have := Nat.mul_le_mul_left d (Nat.one_le_pow c _ (Nat.succ_pos (encA a).length))
    nlinarith
  exact ⟨fun k => d * (F k + 1), c, hd.mono hle hle⟩

/-- **A time bound alone suffices.** A function computable by some machine within time
`F (κ a) * (|encA a| + 1) ^ c`, with any space bound, is computable in fpt time: a machine with `k`
work tapes within time `t` visits at most `k t + k` work-tape cells. -/
theorem _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace.computableInFPTTime {F : ℕ → ℕ}
    {c : ℕ} {s : α → ℕ}
    (h : ComputableInTimeAndSpace f encA encB (fun a => F (κ a) * ((encA a).length + 1) ^ c) s) :
    ComputableInFPTTime f encA encB κ := by
  obtain ⟨k, h⟩ := h.exists_space_linear
  have hle (a : α) (m : ℕ) (hm : m ≤ k + 1) :
      m * (F (κ a) * ((encA a).length + 1) ^ c) + m ≤
        (k + 1) * (F (κ a) + 1) * ((encA a).length + 1) ^ c := by
    have hP := Nat.one_le_pow c _ (Nat.succ_pos (encA a).length)
    have := Nat.mul_le_mul_right (F (κ a) * ((encA a).length + 1) ^ c) hm
    nlinarith
  exact ⟨fun n => (k + 1) * (F n + 1), c,
    h.mono (fun a => by dsimp only; have := hle a 1 (by omega); omega)
      fun a => by dsimp only; exact hle a k (by omega)⟩

end Plain

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {κ κA : α → ℕ} {κB : β → ℕ} {κC : γ → ℕ}

/-- A function computable in polynomial time is computable in fpt time, for every parameter. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.computableInFPTTime {f : α → β}
    (hf : ComputableInPolyTime f encA encB) (κ : α → ℕ) :
    ComputableInFPTTime f encA encB κ :=
  let ⟨d, _, hf⟩ := hf.exists_degree
  ComputableInO.computableInFPTTime (F := fun _ => 1) (c := d)
    (hf.inO.mono_le (fun _ => (one_mul _).ge) fun _ => (one_mul _).ge)

/-- **Case distinction in fpt time.** -/
theorem ComputableInFPTTime.ite {p : α → Bool} {f g : α → β}
    (hp : ComputableInFPTTime p encA encBool κ)
    (hf : ComputableInFPTTime f encA encB κ) (hg : ComputableInFPTTime g encA encB κ) :
    ComputableInFPTTime (fun a => if p a then f a else g a) encA encB κ := by
  obtain ⟨F₁, c₁, hp⟩ := ComputableInFPTTime.exists_computableInO hp
  obtain ⟨F₂, c₂, hf⟩ := ComputableInFPTTime.exists_computableInO hf
  obtain ⟨F₃, c₃, hg⟩ := ComputableInFPTTime.exists_computableInO hg
  have key : ∀ a, (F₁ (κ a) * ((encA a).length + 1) ^ c₁ +
      if p a then F₂ (κ a) * ((encA a).length + 1) ^ c₂
      else F₃ (κ a) * ((encA a).length + 1) ^ c₃) ≤
      (F₁ (κ a) + F₂ (κ a) + F₃ (κ a)) * ((encA a).length + 1) ^ (c₁ + c₂ + c₃) := by
    intro a
    have hle : ∀ c, c ≤ c₁ + c₂ + c₃ → ∀ F,
        F * ((encA a).length + 1) ^ c ≤ F * ((encA a).length + 1) ^ (c₁ + c₂ + c₃) :=
      fun c hc F => Nat.mul_le_mul_left F (Nat.pow_le_pow_right (Nat.succ_pos _) hc)
    have h₁ := hle c₁ (by omega) (F₁ (κ a))
    have h₂ := hle c₂ (by omega) (F₂ (κ a))
    have h₃ := hle c₃ (by omega) (F₃ (κ a))
    rw [Nat.add_mul, Nat.add_mul]
    split_ifs <;> omega
  exact ComputableInO.computableInFPTTime (F := fun k => F₁ k + F₂ k + F₃ k)
    (c := c₁ + c₂ + c₃) ((hp.ite hf hg).mono_le key key)

/-- The arithmetic of composition: a bound `F₂ (n + 1) ^ e` on an output of length `n` within
`l (F₁ (L + 1) ^ c₁ + 1)`, after a computation within `F₁ (L + 1) ^ c₁`. -/
private theorem comp_time_le {L F₁ c₁ l n F₂ F₂' e E : ℕ}
    (hn : n ≤ l * (F₁ * (L + 1) ^ c₁ + 1)) (hF : F₂ ≤ F₂') (he : e ≤ E) :
    F₁ * (L + 1) ^ c₁ + F₂ * (n + 1) ^ e ≤
      (F₁ + F₂' * ((l + 1) * (F₁ + 1)) ^ E) * (L + 1) ^ (c₁ + c₁ * E) := by
  have hP : 1 ≤ (L + 1) ^ c₁ := Nat.one_le_pow _ _ (Nat.succ_pos L)
  have hQ : 1 ≤ ((L + 1) ^ c₁) ^ E := Nat.one_le_pow _ _ hP
  have hlP := Nat.mul_le_mul_left l hP
  have hn' : n + 1 ≤ (l + 1) * (F₁ + 1) * (L + 1) ^ c₁ := by nlinarith
  have h₁ : (n + 1) ^ e ≤ ((l + 1) * (F₁ + 1)) ^ E * ((L + 1) ^ c₁) ^ E := by
    rw [← Nat.mul_pow]
    exact (Nat.pow_le_pow_left hn' e).trans (Nat.pow_le_pow_right (by positivity) he)
  have h₂ := Nat.mul_le_mul hF h₁
  have h₃ := Nat.mul_le_mul_left (F₂' * ((l + 1) * (F₁ + 1)) ^ E * ((L + 1) ^ c₁) ^ E) hP
  have h₄ := Nat.mul_le_mul_left (F₁ * (L + 1) ^ c₁) hQ
  rw [Nat.pow_add, Nat.pow_mul]
  calc F₁ * (L + 1) ^ c₁ + F₂ * (n + 1) ^ e
      ≤ F₁ * (L + 1) ^ c₁ * ((L + 1) ^ c₁) ^ E +
        F₂' * ((l + 1) * (F₁ + 1)) ^ E * ((L + 1) ^ c₁) ^ E * (L + 1) ^ c₁ := by
        rw [Nat.mul_one] at h₃ h₄
        rw [← Nat.mul_assoc] at h₂
        omega
    _ = _ := by ring

/-- Composition of an fpt-time function with a function computable within time
`F₂ (κB b) (|b| + 1) ^ e₂ (κB b)`, given bounds on `F₂` and `e₂` along the function. -/
private theorem computableInO_comp {f : α → β} {g : β → γ} {F₁ : ℕ → ℕ} {c₁ : ℕ}
    {F₂ e₂ F₂' E : ℕ → ℕ}
    (hg : ComputableInO g encB encC (fun b => F₂ (κB b) * ((encB b).length + 1) ^ e₂ (κB b))
      fun b => F₂ (κB b) * ((encB b).length + 1) ^ e₂ (κB b))
    (hf : ComputableInO f encA encB (fun a => F₁ (κA a) * ((encA a).length + 1) ^ c₁)
      fun a => F₁ (κA a) * ((encA a).length + 1) ^ c₁)
    (hF : ∀ a, F₂ (κB (f a)) ≤ F₂' (κA a)) (he : ∀ a, e₂ (κB (f a)) ≤ E (κA a)) :
    ∃ l, ComputableInO (g ∘ f) encA encC
      (fun a => (F₁ (κA a) + F₂' (κA a) * ((l + 1) * (F₁ (κA a) + 1)) ^ E (κA a)) *
        ((encA a).length + 1) ^ (c₁ + c₁ * E (κA a)))
      fun a => (F₁ (κA a) + F₂' (κA a) * ((l + 1) * (F₁ (κA a) + 1)) ^ E (κA a)) *
        ((encA a).length + 1) ^ (c₁ + c₁ * E (κA a)) := by
  have ⟨l, _, hl⟩ := hf
  have key := fun a => comp_time_le (hl a) (hF a) (he a)
  exact ⟨l, (hg.comp hf).mono_le key key⟩

/-- **Composition in fpt time**, along a function that bounds the parameter. -/
theorem ComputableInFPTTime.comp {f : α → β} {g : β → γ}
    (hg : ComputableInFPTTime g encB encC κB) (hf : ComputableInFPTTime f encA encB κA)
    {h : ℕ → ℕ} (hκ : ∀ a, κB (f a) ≤ h (κA a)) :
    ComputableInFPTTime (g ∘ f) encA encC κA := by
  obtain ⟨F₂, c₂, hg⟩ := ComputableInFPTTime.exists_computableInO hg
  obtain ⟨F₁, c₁, hf⟩ := ComputableInFPTTime.exists_computableInO hf
  obtain ⟨l, hgf⟩ := computableInO_comp (e₂ := fun _ => c₂)
    (F₂' := fun k => ∑ j ∈ Finset.range (h k + 1), F₂ j) (E := fun _ => c₂) hg hf
    (fun a => le_sum_range_succ (hκ a)) fun _ => le_rfl
  exact ComputableInO.computableInFPTTime
    (F := fun k => F₁ k + (∑ j ∈ Finset.range (h k + 1), F₂ j) * ((l + 1) * (F₁ k + 1)) ^ c₂)
    (c := c₁ + c₁ * c₂) hgf

/-- Bounds of the shape `T a`, cast to the reals, are `ComputableInO` bounds. -/
private theorem decidableInTimeO_natCast_iff {A : Set α} {T : α → ℕ} :
    DecidableInTimeO A encA (fun a => (T a : ℝ)) ↔
      ∃ g : α → Bool, ComputableInO g encA encBool T T ∧ ∀ a, a ∈ A ↔ g a = true := by
  constructor
  · intro h
    obtain ⟨g, t, k, hg, hA, ht⟩ := h.exists_computableInO
    have ht' : ∀ a, t a ≤ k * (T a + 1) := fun a => by
      have : (t a : ℝ) ≤ ((k * (T a + 1) : ℕ) : ℝ) := by
        push_cast
        linarith [ht a]
      exact_mod_cast this
    exact ⟨g, hg.mono k ht' ht', hA⟩
  · rintro ⟨g, hg, hA⟩
    exact DecidableInTimeO.of_computableInO hg hA fun _ => le_rfl

/-- **`FPT` in terms of fpt-time computability**: a problem is fixed-parameter tractable exactly
when a Boolean function deciding it is computable in fpt time. -/
theorem mem_FPT_iff_computableInFPTTime {A : Set α} :
    A ∈ FPT encA κ ↔
      ∃ g : α → Bool, ComputableInFPTTime g encA encBool κ ∧ ∀ a, a ∈ A ↔ g a = true := by
  have e : ∀ (f : ℕ → ℕ) (c : ℕ), (fun a => (f (κ a) : ℝ) * ((encA a).length + 1) ^ c) =
      fun a => ((f (κ a) * ((encA a).length + 1) ^ c : ℕ) : ℝ) := fun f c => by
    funext a
    push_cast
    rfl
  constructor
  · rintro ⟨f, c, h⟩
    rw [e, decidableInTimeO_natCast_iff] at h
    obtain ⟨g, hg, hA⟩ := h
    exact ⟨g, hg.computableInFPTTime, hA⟩
  · rintro ⟨g, hg, hA⟩
    obtain ⟨f, c, hg⟩ := ComputableInFPTTime.exists_computableInO hg
    refine ⟨f, c, ?_⟩
    rw [e, decidableInTimeO_natCast_iff]
    exact ⟨g, hg, hA⟩

/-- **`XP` in terms of computability within explicit bounds.** -/
theorem mem_XP_iff_exists_computableInO {A : Set α} :
    A ∈ XP encA κ ↔ ∃ (g : α → Bool) (f e : ℕ → ℕ), ComputableInO g encA encBool
      (fun a => f (κ a) * ((encA a).length + 1) ^ e (κ a))
      (fun a => f (κ a) * ((encA a).length + 1) ^ e (κ a)) ∧ ∀ a, a ∈ A ↔ g a = true := by
  have h : ∀ f e : ℕ → ℕ, (fun a => (f (κ a) : ℝ) * ((encA a).length + 1) ^ e (κ a)) =
      fun a => ((f (κ a) * ((encA a).length + 1) ^ e (κ a) : ℕ) : ℝ) := fun f e => by
    funext a
    push_cast
    rfl
  constructor
  · rintro ⟨f, e, hA⟩
    rw [h, decidableInTimeO_natCast_iff] at hA
    obtain ⟨g, hg, hA⟩ := hA
    exact ⟨g, f, e, hg, hA⟩
  · rintro ⟨g, f, e, hg, hA⟩
    refine ⟨f, e, ?_⟩
    rw [h, decidableInTimeO_natCast_iff]
    exact ⟨g, hg, hA⟩

/-- **Bounded parameters.** For a parameter bounded by a constant, `FPT` is `P`. -/
theorem FPT_eq_P_of_le {K : ℕ} (hκ : ∀ a, κ a ≤ K) : FPT encA κ = P encA := by
  refine subset_antisymm (fun A hA => ?_) P_subset_FPT
  obtain ⟨g, hg, hA⟩ :=
    mem_FPT_iff_computableInFPTTime.mp (FPT_subset_FPT_of_le_comp (κ' := fun _ => 0)
      (h := fun _ => K) hκ hA)
  obtain ⟨f, c, hg⟩ := ComputableInFPTTime.exists_computableInO hg
  exact ⟨g, hg.computableInPolyTime (.of_forall_le (f 0) c fun _ => le_rfl)
    (.of_forall_le (f 0) c fun _ => le_rfl), hA⟩

/-- **Bounded parameters.** For a parameter bounded by a constant, `XP` is `P`. -/
theorem XP_eq_P_of_le {K : ℕ} (hκ : ∀ a, κ a ≤ K) : XP encA κ = P encA := by
  refine subset_antisymm (fun A hA => ?_) P_subset_XP
  obtain ⟨g, f, e, hg, hA⟩ :=
    mem_XP_iff_exists_computableInO.mp (XP_subset_XP_of_le_comp (κ' := fun _ => 0)
      (h := fun _ => K) hκ hA)
  exact ⟨g, hg.computableInPolyTime
    (.of_forall_le (f 0) (e 0) fun _ => le_rfl)
    (.of_forall_le (f 0) (e 0) fun _ => le_rfl), hA⟩

/-! ### Boolean closure -/

/-- **`FPT` is closed under complement.** -/
theorem compl_mem_FPT {A : Set α} (hA : A ∈ FPT encA κ) : Aᶜ ∈ FPT encA κ := by
  obtain ⟨g, hg, hA⟩ := mem_FPT_iff_computableInFPTTime.mp hA
  refine mem_FPT_iff_computableInFPTTime.mpr ⟨_, hg.ite
    ((ComputableInPolyTime.const false).computableInFPTTime κ)
    ((ComputableInPolyTime.const true).computableInFPTTime κ),
      fun a => ?_⟩
  simp only [Set.mem_compl_iff, hA]
  cases g a <;> simp

/-- **`FPT` is closed under intersection.** -/
theorem inter_mem_FPT {A B : Set α} (hA : A ∈ FPT encA κ) (hB : B ∈ FPT encA κ) :
    A ∩ B ∈ FPT encA κ := by
  obtain ⟨g₁, hg₁, hA⟩ := mem_FPT_iff_computableInFPTTime.mp hA
  obtain ⟨g₂, hg₂, hB⟩ := mem_FPT_iff_computableInFPTTime.mp hB
  refine mem_FPT_iff_computableInFPTTime.mpr ⟨_, hg₁.ite hg₂
    ((ComputableInPolyTime.const false).computableInFPTTime κ),
      fun a => ?_⟩
  simp only [Set.mem_inter_iff, hA, hB]
  cases g₁ a <;> simp

/-- **`FPT` is closed under union.** -/
theorem union_mem_FPT {A B : Set α} (hA : A ∈ FPT encA κ) (hB : B ∈ FPT encA κ) :
    A ∪ B ∈ FPT encA κ := by
  obtain ⟨g₁, hg₁, hA⟩ := mem_FPT_iff_computableInFPTTime.mp hA
  obtain ⟨g₂, hg₂, hB⟩ := mem_FPT_iff_computableInFPTTime.mp hB
  refine mem_FPT_iff_computableInFPTTime.mpr ⟨_, hg₁.ite
    ((ComputableInPolyTime.const true).computableInFPTTime κ)
      hg₂, fun a => ?_⟩
  simp only [Set.mem_union, hA, hB]
  cases g₁ a <;> simp

/-- **`XP` is closed under complement.** -/
theorem compl_mem_XP {A : Set α} (hA : A ∈ XP encA κ) : Aᶜ ∈ XP encA κ := by
  obtain ⟨g, f, e, hg, hA⟩ := mem_XP_iff_exists_computableInO.mp hA
  have h := hg.ite (ComputableInO.const false : ComputableInO _ _ encBool _ _)
    (ComputableInO.const true : ComputableInO _ _ encBool _ _)
  refine mem_XP_iff_exists_computableInO.mpr ⟨_, fun k => f k + 1, fun k => e k + 1,
    h.mono_le (fun a => ?_) (fun a => ?_), fun a => ?_⟩
  rotate_left 2
  · simp only [Set.mem_compl_iff, hA]
    cases g a <;> simp
  all_goals
    dsimp only
    have h₁ : ((encA a).length + 1) ^ e (κ a) ≤ ((encA a).length + 1) ^ (e (κ a) + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ _)
    have h₂ : (encA a).length ≤ ((encA a).length + 1) ^ (e (κ a) + 1) :=
      (Nat.le_succ _).trans (Nat.le_self_pow (Nat.succ_ne_zero _) _)
    have h₃ := Nat.mul_le_mul_left (f (κ a)) h₁
    split_ifs <;> (rw [Nat.add_mul, Nat.one_mul]; omega)

end Machines

/-! ### Fpt-reductions -/

section Reduction

/-- `f` is computable in fpt time with respect to `κA` and bounds `κB (f a)` by a function of
`κA a`. -/
def ComputableInFPTWithParam {α β : Type*} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (κA : α → ℕ) (κB : β → ℕ) (f : α → β) : Prop :=
  ComputableInFPTTime f encA encB κA ∧ ∃ h : ℕ → ℕ, ∀ a, κB (f a) ≤ h (κA a)

/-- **Fpt-reductions** [FlumGrohe2006, Definition 2.1] [CyganEtAl2015, Definition 13.1]: `A`
reduces to `B` by a map `f`, computable in fpt time with respect to `κA`, with `a ∈ A ↔ f a ∈ B`,
whose parameter `κB (f a)` is bounded by a function `h` of `κA a`. This is `ManyOneReducibleBy` for
`ComputableInFPTWithParam` (`fptReducible_iff_manyOneReducibleBy`). The function `h` and the
function of the time bound are arbitrary; the cited definitions require them to be computable. -/
def FPTReducible {α β : Type*} (encA : α ↪ List Bool) (encB : β ↪ List Bool) (κA : α → ℕ)
    (κB : β → ℕ) (A : Set α) (B : Set β) : Prop :=
  ∃ f : α → β, (ComputableInFPTTime f encA encB κA ∧
    ∃ h : ℕ → ℕ, ∀ a, κB (f a) ≤ h (κA a)) ∧ ∀ a, a ∈ A ↔ f a ∈ B

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {κA : α → ℕ} {κB : β → ℕ} {κC : γ → ℕ} {A : Set α} {B : Set β} {C : Set γ}

/-- Fpt-reducibility is many-one reducibility by maps computable in fpt time with a parameter
bound. -/
theorem fptReducible_iff_manyOneReducibleBy :
    FPTReducible encA encB κA κB A B ↔
      ManyOneReducibleBy (ComputableInFPTWithParam encA encB κA κB) A B :=
  Iff.rfl

/-- **Polynomial-time reductions bounding the parameter are fpt-reductions.** -/
theorem FPTReducible.of_computableInPolyTime {f : α → β}
    (hf : ComputableInPolyTime f encA encB) {h : ℕ → ℕ} (hκ : ∀ a, κB (f a) ≤ h (κA a))
    (hfA : ∀ a, a ∈ A ↔ f a ∈ B) : FPTReducible encA encB κA κB A B :=
  ⟨f, ⟨hf.computableInFPTTime κA, h, hκ⟩, hfA⟩

/-- Every parameterized problem reduces to itself by the identity. -/
@[refl]
theorem FPTReducible.refl (encA : α ↪ List Bool) (κA : α → ℕ) (A : Set α) :
    FPTReducible encA encA κA κA A A :=
  ManyOneReducibleBy.refl
    ⟨ComputableInPolyTime.id'.computableInFPTTime κA, id, fun _ => le_rfl⟩ A

/-- **Fpt-reductions compose.** -/
@[trans]
theorem FPTReducible.trans (hAB : FPTReducible encA encB κA κB A B)
    (hBC : FPTReducible encB encC κB κC B C) : FPTReducible encA encC κA κC A C :=
  ManyOneReducibleBy.trans
    (fun _ _ ⟨hf, h₁, hκ₁⟩ ⟨hg, h₂, hκ₂⟩ => ⟨hg.comp hf hκ₁,
      fun k => ∑ j ∈ Finset.range (h₁ k + 1), h₂ j,
      fun a => (hκ₂ _).trans (le_sum_range_succ (hκ₁ a))⟩)
    hAB hBC

/-- An fpt-reduction from `A` to `B` is one from `Aᶜ` to `Bᶜ`. -/
theorem FPTReducible.compl (h : FPTReducible encA encB κA κB A B) :
    FPTReducible encA encB κA κB Aᶜ Bᶜ :=
  ManyOneReducibleBy.compl h

/-- **`FPT` is closed under fpt-reductions.** -/
theorem FPTReducible.mem_FPT (hAB : FPTReducible encA encB κA κB A B) (hB : B ∈ FPT encB κB) :
    A ∈ FPT encA κA :=
  mem_FPT_iff_computableInFPTTime.mpr
    (ManyOneReducibleBy.trans (C := {true}) (fun _ _ ⟨hf, _, hκ⟩ hg => hg.comp hf hκ)
      hAB (mem_FPT_iff_computableInFPTTime.mp hB))

/-- **`XP` is closed under fpt-reductions.** -/
theorem FPTReducible.mem_XP (hAB : FPTReducible encA encB κA κB A B) (hB : B ∈ XP encB κB) :
    A ∈ XP encA κA := by
  obtain ⟨f, ⟨hf, h, hκ⟩, hAB⟩ := hAB
  obtain ⟨F₁, c₁, hf⟩ := ComputableInFPTTime.exists_computableInO hf
  obtain ⟨g, F₂, e₂, hg, hB⟩ := mem_XP_iff_exists_computableInO.mp hB
  obtain ⟨l, hgf⟩ := computableInO_comp
    (F₂' := fun k => ∑ j ∈ Finset.range (h k + 1), F₂ j)
    (E := fun k => ∑ j ∈ Finset.range (h k + 1), e₂ j) hg hf
    (fun a => le_sum_range_succ (hκ a)) fun a => le_sum_range_succ (hκ a)
  exact mem_XP_iff_exists_computableInO.mpr ⟨g ∘ f,
    fun k => F₁ k + (∑ j ∈ Finset.range (h k + 1), F₂ j) *
      ((l + 1) * (F₁ k + 1)) ^ ∑ j ∈ Finset.range (h k + 1), e₂ j,
    fun k => c₁ + c₁ * ∑ j ∈ Finset.range (h k + 1), e₂ j, hgf,
    fun a => (hAB a).trans (hB (f a))⟩

end Reduction

end Cslib.Complexity
