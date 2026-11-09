/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BlumComplexity.Basic
import CslibFrontier.Computability.BlumComplexity.Cancellation

/-!
# Arbitrarily complex functions and the hierarchy of complexity classes

For every Blum complexity measure `Φ` and every computable bound `t`, there is a computable
`0`/`1`-valued function `f` such that every program `c` for `f` has cost `t n < Φ c n` for all
sufficiently large `n`. This is the standard measure-independent form of the theorem on
arbitrarily complex functions, in the axiomatic setting of Blum
[Blum, *A machine-independent theory of the complexity of recursive functions*][Blum1967]. The
result is commonly credited to Rabin (1960) and to Blum's paper. Neither attribution nor any
theorem locator has been checked against the original texts.

## Construction

The proof is a priority construction without the recursion theorem. A cancellation run
(`Cslib.BlumComplexity.Cancellation.canc`) calls the program numbered `i` *eligible* at stage `y`
when it halts on `y` with cost at most `t y`. By Blum's second axiom
(`Cslib.BlumComplexity.BlumMeasure.computablePred_cost_le`), eligibility is decidable. At each
stage the least eligible program not cancelled earlier is cancelled, and `f` outputs `1 - φ_i y`
there, so that `φ_i` differs from `f` at `y`. Stages without a cancellation output `0`. A program
for `f` is never cancelled, so it is eligible only finitely often
(`Cslib.BlumComplexity.Cancellation.eventually_not_eligible`).

## Strength

The lower bound `t n < Φ c n` holds almost everywhere, for every program `c` for `f`, which is the
almost-everywhere form of the source. It is strictly stronger than `f ∉ C_t`, which only says that
each program for `f` exceeds `t` infinitely often. The statement is not vacuous: `f` is computable,
so it has a program, and every program for `f` has its cost defined everywhere.

## Main results

* `Cslib.BlumComplexity.BlumMeasure.exists_arbitrarilyComplex`: arbitrarily complex `0`/`1`-valued
  functions.
* `Cslib.BlumComplexity.BlumMeasure.exists_not_mem_complexityClass`: every complexity class of a
  computable bound misses a computable `0`/`1`-valued function.
* `Cslib.BlumComplexity.BlumMeasure.not_forall_mem_complexityClass`: no complexity class of a
  computable bound contains every computable function.
* `Cslib.BlumComplexity.BlumMeasure.exists_complexityClass_ssubset`: every computable bound `t` is
  dominated by a computable bound `t'` with `C_t ⊂ C_{t'}`.

## References

* [M. Blum, *A machine-independent theory of the complexity of recursive functions*][Blum1967]
-/
public section

namespace Cslib.BlumComplexity.BlumMeasure

open Encodable Denumerable Filter Cancellation
open Nat.Partrec (Code)

variable (Φ : BlumMeasure)

namespace Hierarchy

/-- Eligibility at stage `y`: the program numbered `i` halts on `y` with cost at most `t y`. -/
private def Elig (t : ℕ → ℕ) (i y : ℕ) : Prop := ∃ m ∈ Φ.cost (ofNat Code i) y, m ≤ t y

private noncomputable def elig (t : ℕ → ℕ) (i y : ℕ) : Bool :=
  @decide (Elig Φ t i y) (Classical.dec _)

private theorem elig_eq_true {t : ℕ → ℕ} {i y : ℕ} : elig Φ t i y = true ↔ Elig Φ t i y :=
  @decide_eq_true_iff _ (Classical.dec _)

private theorem computable_elig {t : ℕ → ℕ} (ht : Computable t) :
    Computable fun p : ℕ × ℕ × ℕ => elig Φ t p.2.1 p.2.2 := by
  have h : ComputablePred fun p : ℕ × ℕ × ℕ => Elig Φ t p.2.1 p.2.2 :=
    Φ.computablePred_cost_le.comp ((((Computable.ofNat Code).comp
      (Computable.fst.comp Computable.snd)).pair (Computable.snd.comp Computable.snd)).pair
      (ht.comp (Computable.snd.comp Computable.snd))) |>.of_eq fun _ => Iff.rfl
  exact @ComputablePred.decide _ _ _ (fun _ => Classical.dec _) h

/-- The run, as a function of the stage. -/
private noncomputable def run (t : ℕ → ℕ) (y : ℕ) : Option ℕ :=
  canc (elig Φ t) (fun _ => false) 0 y

private theorem computable_run {t : ℕ → ℕ} (ht : Computable t) : Computable (run Φ t) :=
  computable_canc (α := ℕ) (E := fun _ => elig Φ t) (ov := fun _ _ => false)
    (computable_elig Φ ht) (Computable.const false).to₂ (Computable.const 0) Computable.id

/-- The program cancelled at stage `y`, or `Code.zero`. -/
private noncomputable def sel (t : ℕ → ℕ) (y : ℕ) : Code :=
  ((run Φ t y).map (ofNat Code)).getD Code.zero

/-- The output at stage `y`, given the output `w` of the selected program. -/
private noncomputable def post (t : ℕ → ℕ) (y w : ℕ) : ℕ :=
  ((run Φ t y).map fun _ => 1 - w).getD 0

/-- The diagonal function, as a partial function. -/
private noncomputable def diag (t : ℕ → ℕ) (y : ℕ) : Part ℕ :=
  ((sel Φ t y).eval y).map (post Φ t y)

private theorem partrec_diag {t : ℕ → ℕ} (ht : Computable t) : Partrec (diag Φ t) := by
  have hsel : Computable (sel Φ t) :=
    Computable.option_getD (Computable.option_map (computable_run Φ ht)
      ((Computable.ofNat Code).comp Computable.snd).to₂) (Computable.const Code.zero)
  have hpost : Computable₂ (post Φ t) :=
    (Computable.option_getD (Computable.option_map ((computable_run Φ ht).comp Computable.fst)
      (Primrec.nat_sub.to_comp.comp (Computable.const 1)
        (Computable.snd.comp Computable.fst)).to₂) (Computable.const 0)).to₂
  exact Partrec.map (Code.eval_part.comp hsel Computable.id) hpost

private theorem dom_diag (t : ℕ → ℕ) (y : ℕ) : (diag Φ t y).Dom := by
  change ((sel Φ t y).eval y).Dom
  unfold sel
  cases hc : run Φ t y with
  | none => exact trivial
  | some i =>
    obtain ⟨-, -, -, hE, -⟩ := canc_eq_some.1 hc
    obtain ⟨m, hm, -⟩ := (elig_eq_true Φ).1 hE
    exact (Φ.dom_cost_iff _ _).1 (Part.dom_iff_mem.2 ⟨m, hm⟩)

end Hierarchy

open Hierarchy

/-- **Arbitrarily complex functions**, in Blum's axiomatic setting [Blum1967]. For every
computable bound `t` there is a computable function `f` with values in `{0, 1}` such that every
program `c` for `f` has cost `t n < Φ c n` for all sufficiently large `n`. The attribution (to
Rabin and to Blum's paper) is the customary one; no theorem locator has been verified. -/
theorem exists_arbitrarilyComplex {t : ℕ → ℕ} (ht : Computable t) :
    ∃ f : ℕ → ℕ, Computable f ∧ (∀ n, f n ≤ 1) ∧
      ∀ c : Code, (∀ n, f n ∈ c.eval n) → ∀ᶠ n in atTop, ∀ m ∈ Φ.cost c n, t n < m := by
  let f : ℕ → ℕ := fun y => (diag Φ t y).get (dom_diag Φ t y)
  have hfmem : ∀ y, f y ∈ diag Φ t y := fun y => Part.get_mem _
  have hfc : ∀ y i w, run Φ t y = some i → w ∈ (ofNat Code i).eval y → f y = 1 - w := by
    intro y i w hc hw
    have h : 1 - w ∈ diag Φ t y := by
      unfold diag sel post
      rw [hc, Option.map_some, Option.getD_some]
      exact Part.mem_map_iff _ |>.2 ⟨w, hw, by rw [Option.map_some, Option.getD_some]⟩
    exact Part.mem_unique (hfmem y) h
  have hf0 : ∀ y, run Φ t y = none → f y = 0 := by
    intro y hc
    have h : 0 ∈ diag Φ t y := by
      unfold diag sel post
      rw [hc, Option.map_none, Option.getD_none]
      exact Part.mem_map_iff _ |>.2 ⟨0, Part.mem_some 0, by rw [Option.map_none, Option.getD_none]⟩
    exact Part.mem_unique (hfmem y) h
  have hf1 : ∀ y, f y ≤ 1 := by
    intro y
    cases hc : run Φ t y with
    | none => rw [hf0 y hc]; exact zero_le_one
    | some i =>
      obtain ⟨-, -, -, hE, -⟩ := canc_eq_some.1 hc
      obtain ⟨m, hm, -⟩ := (elig_eq_true Φ).1 hE
      obtain ⟨w, hw⟩ := Part.dom_iff_mem.1 ((Φ.dom_cost_iff _ _).1 (Part.dom_iff_mem.2 ⟨m, hm⟩))
      rw [hfc y i w hc hw]
      omega
  have hfcomp : Computable f := (partrec_diag Φ ht).of_eq_tot hfmem
  refine ⟨f, hfcomp, hf1, fun c hc => ?_⟩
  have hnc : ∀ y, run Φ t y ≠ some (encode c) := by
    intro y hy
    have h := hfc y (encode c) (f y) hy (by simpa using hc y)
    have := hf1 y
    omega
  filter_upwards [eventually_not_eligible hnc] with y hy m hm
  by_contra hle
  push Not at hle
  have : elig Φ t (encode c) y = true := (elig_eq_true Φ).2 ⟨m, by simpa using hm, hle⟩
  rw [hy] at this
  exact Bool.false_ne_true this

/-- For every computable bound `t`, some computable `0`/`1`-valued function lies outside
`C_t`. -/
theorem exists_not_mem_complexityClass {t : ℕ → ℕ} (ht : Computable t) :
    ∃ f : ℕ → ℕ, Computable f ∧ (∀ n, f n ≤ 1) ∧ f ∉ Φ.complexityClass t := by
  obtain ⟨f, hf, hf1, hc⟩ := Φ.exists_arbitrarilyComplex ht
  refine ⟨f, hf, hf1, fun hmem => ?_⟩
  obtain ⟨c, hcf, hev⟩ := mem_complexityClass.1 hmem
  obtain ⟨n, hn, hn'⟩ := ((hc c hcf).and hev).exists
  obtain ⟨m, hm⟩ := Part.dom_iff_mem.1 (Φ.dom_cost_of_total hcf n)
  have h1 := hn m hm
  have h2 := hn' m hm
  omega

/-- No complexity class of a computable bound contains every computable function. -/
theorem not_forall_mem_complexityClass {t : ℕ → ℕ} (ht : Computable t) :
    ¬∀ f : ℕ → ℕ, Computable f → f ∈ Φ.complexityClass t := fun h => by
  obtain ⟨f, hf, -, hn⟩ := Φ.exists_not_mem_complexityClass ht
  exact hn (h f hf)

/-- **Hierarchy**: every computable bound `t` is dominated by a computable bound `t'` with
`C_t ⊂ C_{t'}`. The bound `t'` is obtained non-uniformly, from a program for the function of
`exists_arbitrarilyComplex`; no computable map from programs for `t` to programs for `t'` is
claimed. This corollary is derived here and is not attributed to a source. -/
theorem exists_complexityClass_ssubset {t : ℕ → ℕ} (ht : Computable t) :
    ∃ t' : ℕ → ℕ, Computable t' ∧ t ≤ t' ∧ Φ.complexityClass t ⊂ Φ.complexityClass t' := by
  obtain ⟨f, hf, -, hn⟩ := Φ.exists_not_mem_complexityClass ht
  obtain ⟨t₀, ht₀, hft₀⟩ := exists_computable_mem_complexityClass (Φ := Φ) hf
  refine ⟨fun n => max (t n) (t₀ n), Primrec.nat_max.to_comp.comp ht ht₀,
    fun n => le_max_left _ _, ?_⟩
  refine (Set.ssubset_iff_of_subset (complexityClass_mono
    (Eventually.of_forall fun n => le_max_left _ _))).2 ⟨f, ?_, hn⟩
  exact complexityClass_mono (Eventually.of_forall fun n => le_max_right _ _) hft₀

end Cslib.BlumComplexity.BlumMeasure
