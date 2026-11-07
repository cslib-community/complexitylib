/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.BlumComplexity.Fuel
import Complexity.Computability.BlumComplexity.Gap
import Complexity.Computability.BlumComplexity.Hierarchy
import Complexity.Computability.BlumComplexity.RecursiveRelatedness
import Complexity.Computability.BlumComplexity.Speedup

/-!
# Blum complexity measure clients

The fuel of the constant-zero program is computed exactly. For the fuel measure, the class of the
bound `id` is empty, while the bound `n + 1` admits the constant-zero function. The class
convention is almost everywhere: a bound that fails at finitely many inputs still admits a
function. The gap theorem is instantiated with `g n = n * n` and a lower bound, and the resulting
gap class is inhabited, and the two-argument gap theorem is instantiated with the input-dependent
stretch `g n y = y ^ (n + 1)`. Recursive relatedness is instantiated for the fuel measure against
itself and, with its explicit threshold, against a second measure (fuel plus input). Blum's
speedup theorem is instantiated for the fuel measure with exponential speedup `r m = 2 ^ m`. The
resulting function has a program, so the universally quantified conclusion is not vacuous. It
is also hard: it lies outside the class of the bound `n + 1`. The speedup can be applied twice.
The arbitrarily complex function for the bound `2 ^ n` has a program, every program for it needs
fuel above `2 ^ n` almost everywhere, and the fuel class of `2 ^ n` is strictly contained in the
fuel class of a larger computable bound.
-/

namespace ComplexityTests.BlumComplexity

open Cslib.BlumComplexity Cslib.BlumComplexity.BlumMeasure Nat.Partrec Filter

/-- The constant-zero program needs fuel exactly `n + 1` on input `n`. -/
theorem evalnFuel_zero (n : ℕ) : evalnFuel Code.zero n = Part.some (n + 1) := by
  rw [Part.eq_some_iff, mem_evalnFuel_iff]
  refine ⟨by simp [Code.evaln], fun j hj => ?_⟩
  cases j with
  | zero => simp [Code.evaln]
  | succ j =>
    have hnj : ¬ n ≤ j := by omega
    simp [Code.evaln, hnj]

example : evalnFuel Code.zero 4 = Part.some 5 :=
  evalnFuel_zero 4

private theorem mem_eval_zero (n : ℕ) : 0 ∈ Code.zero.eval n := by
  rw [Code.eval]
  exact Part.mem_some 0

/-- The bound `id` is below the fuel at every input, so its class is empty. -/
example : fuelMeasure.complexityClass id = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun f hf => ?_
  obtain ⟨c, hc, hev⟩ := mem_complexityClass.1 hf
  obtain ⟨n, hn⟩ := hev.exists
  obtain ⟨k, hk⟩ :=
    Part.dom_iff_mem.1 ((dom_evalnFuel_iff c n).2 (Part.dom_iff_mem.2 ⟨_, hc n⟩))
  exact absurd (hn k hk) (not_le.2 (lt_of_mem_evalnFuel hk))

/-- The constant-zero function lies in the class of the bound `n + 1`. -/
example : (fun _ => 0) ∈ fuelMeasure.complexityClass (· + 1) := by
  refine mem_complexityClass.2 ⟨Code.zero, mem_eval_zero, Eventually.of_forall fun n m hm => ?_⟩
  rw [fuelMeasure_cost, evalnFuel_zero, Part.mem_some_iff] at hm
  exact hm.le

/-- Almost-everywhere convention: the bound `if n < 10 then 0 else n + 1` fails at the first ten
inputs for every program, yet its class still contains the constant-zero function. -/
example : (fun _ => 0) ∈ fuelMeasure.complexityClass (fun n => if n < 10 then 0 else n + 1) := by
  refine mem_complexityClass.2 ⟨Code.zero, mem_eval_zero, ?_⟩
  filter_upwards [eventually_ge_atTop 10] with n hn m hm
  rw [fuelMeasure_cost, evalnFuel_zero, Part.mem_some_iff] at hm
  have hn' : ¬ n < 10 := by omega
  simp only [hn', ↓reduceIte]
  exact hm.le

/-- The gap theorem for `g n = n * n` and the lower bound `a n = n + 1`: there is a computable
strictly increasing `t ≥ a` such that `C_{t * t} = C_t` for the fuel measure, and this class
contains the constant-zero function. -/
example : ∃ t : ℕ → ℕ, Computable t ∧ StrictMono t ∧
    fuelMeasure.complexityClass (fun n => t n * t n) = fuelMeasure.complexityClass t ∧
    (fun _ => 0) ∈ fuelMeasure.complexityClass t := by
  obtain ⟨t, ht, hmono, hat, hgap⟩ := fuelMeasure.gap_theorem (g := fun n => n * n)
    (Primrec.nat_mul.comp Primrec.id Primrec.id).to_comp Nat.le_mul_self Computable.succ
  refine ⟨t, ht, hmono, hgap, mem_complexityClass.2 ⟨Code.zero, mem_eval_zero,
    Eventually.of_forall fun n m hm => ?_⟩⟩
  rw [fuelMeasure_cost, evalnFuel_zero, Part.mem_some_iff] at hm
  exact hm.trans_le (hat n)

/-- The explicit form of the gap: past the code index, no fuel lies in `(t n, t n * t n]`. -/
example : ∃ t : ℕ → ℕ, Computable t ∧
    ∀ c : Code, ∀ n, Encodable.encode c ≤ n →
      ∀ m ∈ evalnFuel c n, m ≤ t n ∨ t n * t n < m := by
  obtain ⟨t, ht, -, -, hgap⟩ := fuelMeasure.exists_gap (g := fun n => n * n)
    (Primrec.nat_mul.comp Primrec.id Primrec.id).to_comp (Computable.const 0)
  exact ⟨t, ht, hgap⟩

/-- Recursive relatedness, instantiated for the fuel measure against itself. -/
example : ∃ r : ℕ → ℕ → ℕ, Computable₂ r ∧
    ∀ᶠ n in atTop, ∀ m ∈ evalnFuel Code.zero n, m ≤ r n m := by
  obtain ⟨r, hr, hrel⟩ := recursively_related fuelMeasure fuelMeasure
  exact ⟨r, hr, (hrel Code.zero).mono fun n hn m hm => (hn m hm m hm).1⟩

private theorem primrec_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- The two-argument gap theorem with the input-dependent stretch `g n y = y ^ (n + 1)`. -/
example : ∃ t : ℕ → ℕ, Computable t ∧
    fuelMeasure.complexityClass (fun n => t n ^ (n + 1)) = fuelMeasure.complexityClass t := by
  obtain ⟨t, ht, -, -, hgap⟩ := fuelMeasure.gap_theorem₂ (g := fun n y => y ^ (n + 1))
    (primrec_pow.comp Primrec.snd (Primrec.succ.comp Primrec.fst)).to_comp
    (fun n y => Nat.le_self_pow (Nat.succ_ne_zero n) y) (Computable.const 0)
  exact ⟨t, ht, hgap⟩

/-- A second Blum measure: the fuel plus the input. -/
private def fuelPlusInput : BlumMeasure where
  cost c n := (evalnFuel c n).map (· + n)
  dom_cost_iff c n := dom_evalnFuel_iff c n
  computablePred_mem_cost := by
    refine ((ComputablePred.nat_le (Computable.snd.comp Computable.fst) Computable.snd).and
      (fuelMeasure.computablePred_mem_cost_comp (Computable.fst.comp Computable.fst)
        (Computable.snd.comp Computable.fst)
        (Primrec.nat_sub.to_comp.comp Computable.snd
          (Computable.snd.comp Computable.fst)))).of_eq ?_
    rintro ⟨⟨c, n⟩, m⟩
    simp only [fuelMeasure_cost, Part.mem_map_iff]
    constructor
    · rintro ⟨hnm, h⟩
      exact ⟨m - n, h, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by omega, by simpa using hk⟩

/-- Recursive relatedness with its explicit threshold, for the fuel measure against
`fuelPlusInput`: at every input `n ≥ encode c`, each cost is bounded by `r n` of the other. -/
example : ∃ r : ℕ → ℕ → ℕ, Computable₂ r ∧ ∀ c : Code, ∀ n, Encodable.encode c ≤ n →
    ∀ m ∈ evalnFuel c n, m + n ≤ r n m ∧ m ≤ r n (m + n) := by
  obtain ⟨r, hr, hrel⟩ := recursively_related_of_encode_le fuelMeasure fuelPlusInput
  exact ⟨r, hr, fun c n hn m hm => hrel c n hn m hm (m + n) (Part.mem_map _ hm)⟩

/-- Blum's speedup theorem for the fuel measure with exponential speedup: some computable
`0`/`1`-valued function has a program, and each of its programs is beaten by another one that
needs exponentially less fuel almost everywhere. -/
example : ∃ f : ℕ → ℕ, Computable f ∧ (∀ n, f n ≤ 1) ∧ (∃ c : Code, ∀ n, f n ∈ c.eval n) ∧
    ∀ c : Code, (∀ n, f n ∈ c.eval n) → ∃ c' : Code, (∀ n, f n ∈ c'.eval n) ∧
      ∀ᶠ n in atTop, ∀ m ∈ evalnFuel c' n, ∀ m' ∈ evalnFuel c n, 2 ^ m < m' := by
  obtain ⟨f, hf, hf1, hsp⟩ := fuelMeasure.speedup' (r := fun m => 2 ^ m)
    (primrec_pow.comp (Primrec.const 2) Primrec.id).to_comp
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hf)
  refine ⟨f, hf, hf1, ⟨c, fun n => by rw [hc]; exact Part.mem_some _⟩, fun c hc => ?_⟩
  obtain ⟨c', hc', hev⟩ := hsp c hc
  exact ⟨c', hc', by simpa only [fuelMeasure_cost] using hev⟩

/-- The speedup function is hard: for `r = id` it lies outside the fuel class of `n + 1`. A program
within fuel `n + 1` would have a faster program, with fuel at most `n`, below the fuel lower bound
`n < evalnFuel c n`. -/
example : ∃ f : ℕ → ℕ, Computable f ∧ f ∉ fuelMeasure.complexityClass (· + 1) := by
  obtain ⟨f, hf, -, hsp⟩ := fuelMeasure.speedup' (r := id) Computable.id
  refine ⟨f, hf, fun hmem => ?_⟩
  obtain ⟨c, hc, hev⟩ := mem_complexityClass.1 hmem
  obtain ⟨c', hc', hev'⟩ := hsp c hc
  obtain ⟨n, hn, hn'⟩ := (hev.and hev').exists
  obtain ⟨m, hm⟩ := Part.dom_iff_mem.1 (fuelMeasure.dom_cost_of_total hc n)
  obtain ⟨m', hm'⟩ := Part.dom_iff_mem.1 (fuelMeasure.dom_cost_of_total hc' n)
  have h1 := hn m hm
  have h2 : m' < m := hn' m' hm' m hm
  rw [fuelMeasure_cost] at hm'
  have h3 := lt_of_mem_evalnFuel hm'
  omega

/-- The speedup can be iterated: from any program for the speedup function there are two further
programs, each faster than the previous one by `r` almost everywhere. -/
example {r : ℕ → ℕ → ℕ} (hr : Computable₂ r) : ∃ f : ℕ → ℕ, Computable f ∧
    ∀ c : Code, (∀ n, f n ∈ c.eval n) → ∃ c' c'' : Code,
      (∀ n, f n ∈ c'.eval n) ∧ (∀ n, f n ∈ c''.eval n) ∧
      ∀ᶠ n in atTop, ∀ m ∈ evalnFuel c n, ∀ m' ∈ evalnFuel c' n, ∀ m'' ∈ evalnFuel c'' n,
        r n m'' < m' ∧ r n m' < m := by
  obtain ⟨f, hf, -, hsp⟩ := fuelMeasure.speedup hr
  refine ⟨f, hf, fun c hc => ?_⟩
  obtain ⟨c', hc', hev'⟩ := hsp c hc
  obtain ⟨c'', hc'', hev''⟩ := hsp c' hc'
  refine ⟨c', c'', hc', hc'', ?_⟩
  filter_upwards [hev', hev''] with n h' h'' m hm m' hm' m'' hm''
  exact ⟨h'' m'' hm'' m' hm', h' m' hm' m hm⟩

/-- An arbitrarily complex function for the fuel measure and the bound `2 ^ n`. It has a program,
so the universally quantified lower bound is not vacuous. -/
example : ∃ f : ℕ → ℕ, Computable f ∧ (∀ n, f n ≤ 1) ∧ (∃ c : Code, ∀ n, f n ∈ c.eval n) ∧
    ∀ c : Code, (∀ n, f n ∈ c.eval n) → ∀ᶠ n in atTop, ∀ m ∈ evalnFuel c n, 2 ^ n < m := by
  obtain ⟨f, hf, hf1, hc⟩ := fuelMeasure.exists_complex (t := fun n => 2 ^ n)
    (primrec_pow.comp (Primrec.const 2) Primrec.id).to_comp
  obtain ⟨c, hcf⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hf)
  refine ⟨f, hf, hf1, ⟨c, fun n => by rw [hcf]; exact Part.mem_some _⟩, fun c hc' => ?_⟩
  simpa only [fuelMeasure_cost] using hc c hc'

/-- The fuel class of `2 ^ n` is strictly contained in the fuel class of a larger computable
bound. -/
example : ∃ t' : ℕ → ℕ, Computable t' ∧ (∀ n, 2 ^ n ≤ t' n) ∧
    fuelMeasure.complexityClass (fun n => 2 ^ n) ⊂ fuelMeasure.complexityClass t' :=
  fuelMeasure.exists_complexityClass_ssubset
    (primrec_pow.comp (Primrec.const 2) Primrec.id).to_comp

end ComplexityTests.BlumComplexity
