/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Hashing.KWise
public import Complexity.Algorithms.WordRAM.Hashing.Tabulation
public import Complexity.DataStructure.HashFamily.WordRAM.Basic
public import Complexity.Probability.KWiseIndependent.DoubleTabulation

/-!
# Self-Contained Word-RAM Double Tabulation and High-Independence Hashing (`[Thorup2013]`)

This module provides a reusable Word-RAM implementation of Mikkel Thorup's double tabulation hash
family (`Cslib.Probability.doubleTabHash c d b U M`, [Thorup2013]) over `Cslib.WordRAM.Basis.exact`
and lifts it to `Cslib.WordRAM.Basis.standard`:

1. **Flat multi-word memory layout (`space c d b = (c + 1) * d * 2 ^ b`)**:
   - The top-level table `T₁ : DoubleTabTopSeed c d b` (`Fin c → Fin d → Fin (2 ^ b) → Fin (2 ^ b)`)
     occupies `[base, base + c * d * 2 ^ b)`, storing `(T₁ i j ch).val` at
     `topAddr base c b i j ch = base + (j.val * c + i.val) * 2 ^ b + ch.val` (`b`-bit words, never
     packing an intermediate `d`-tuple `Ψ ^ d` into a single machine word).
   - The bottom-level table `T₂ : DoubleTabBotSeed d b M` (`Fin d → Fin (2 ^ b) → Fin (2 ^ M)`)
     occupies `[base + c * d * 2 ^ b, base + (c + 1) * d * 2 ^ b)`, storing `(T₂ j y).val` at
     `botAddr base c d b j y = base + c * d * 2 ^ b + j.val * 2 ^ b + y.val`.
2. **Exact uniform seed resampling (`resampleCode c d b M`)**:
   - Executes two sequential calls to `Tabulation.randFillLoop` in
     `resampleSteps c d b = 5 * space c d b + 13` instructions (`O((c + 1) * d * 2 ^ b)`),
     sampling `(T₁, T₂)` from the exact uniform distribution
     `PMF.uniformOfFintype (DoubleTabTopSeed c d b × DoubleTabBotSeed d b M)`.
3. **Register-by-register deterministic query evaluation (`evalCode c d b`)**:
   - For each output coordinate `j = 0 .. d - 1`, computes the intermediate `b`-bit character
     `y_j = ⨁_{i < c} T₁[i, j, x_i]` via an inner loop over `i = 0 .. c - 1`, then looks up
     `T₂[j, y_j]` and XORs it into the output accumulator in
     `evalSteps c d = (12 * c + 11) * d + 10` deterministic instructions (`O(c * d)`), without
     modifying memory and matching `(doubleTabHash c d b U M T₁ T₂ u).val`.
4. **Reusable `HashFamily.WordRAM.Impl` and `ObliviousSequenceImpl` certificates**:
   - `impl` and `obliviousSequenceImpl` package `doubleTabHash` as a Word-RAM hash family realizing
     `DataStructure.HashFamily.whpKWiseSpec k U (2 ^ M) δ` with failure probability
     `δ = doubleTabFailureProb c d b k`, bounded for `d = 8 * c` by
     `card_not_isKUnique_eight_mul_le`.
   - `provableImpl` and `provableObliviousSequenceImpl` combine `KWise` (`trinomialPolyHash`
     with `δ = 0` for `n_max < doubleTabThreshold c_exp`) and `DoubleTabulation`
     (`c = 2 * max c_exp 1`, `d = 8 * c`, `b = (1 + Nat.clog 2 (max n_max 4)) / 2` for
     `doubleTabThreshold c_exp ≤ n_max`), achieving `O_{c_exp, k}(1)` worst-case evaluation time
     (`provableEvalBound c_exp k`, independent of `n_max`, `U`, and `M`) and
     `O_{c_exp, k}(n_max + 1)` words of space across every `n_max : ℕ` whenever
     `U ≤ max n_max 4 ^ c_exp`.

## Main definitions

* `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.space`,
  `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.topAddr`,
  `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.botAddr`,
  `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.TopRep`,
  `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.BotRep`,
  `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.SeedRep`: memory footprint and
  representation predicates for `(T₁, T₂)`.
* `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.resampleCode`,
  `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.resampleSteps`,
  `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.evalCode`,
  `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.evalSteps`: Word-RAM resampling and query
  evaluation programs and step counts on `Data 12`.
* `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.impl`,
  `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.obliviousSequenceImpl`,
  `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.provableImpl`,
  `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.provableObliviousSequenceImpl`:
  `HashFamily.WordRAM.Impl` and `ObliviousSequenceImpl` certificates over `Basis.exact` and
  `Basis.standard`.

## Main results

* `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.resampleCode_execRand`,
  `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.map_extractSeed_eval_resampleComp`: exact
  `ExecRand` execution and product uniformity of `resampleCode`.
* `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.evalCode_exec`,
  `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.evalCode_execWithin`: deterministic
  `O(c * d)` evaluation of `doubleTabHash c d b U M T₁ T₂ u`.
* `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.doubleTabFailureProb_eight_mul_le`:
  explicit high-probability `k`-uniqueness failure bound for `d = 8 * c`.
* `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.provableImpl_evalSteps_le`,
  `Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.provableSpace_le`: uniform
  `O_{c_exp, k}(1)` evaluation time and `O_{c_exp, k}(n_max + 1)` space bounds across all
  `n_max : ℕ`.

## References

* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation,
  and High Independence*][Thorup2013]
-/

public section

namespace Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation

open Cslib.WordRAM Cslib.WordRAM.Randomized Cslib.Probability
open Cslib.DataStructure Cslib.DataStructure.WordRAM.Randomized
open Cslib.Algorithms.WordRAM.ExactLog Cslib.Algorithms.WordRAM.Hashing
open scoped ENNReal BigOperators

/-! ## Section 1: Flat memory layout, seed representations, and slice equivalences -/

/-- Number of machine words `c * d * 2 ^ b` storing the top-level table `T₁`. -/
@[expose] def topWords (c d b : ℕ) : ℕ :=
  c * d * 2 ^ b

/-- Number of machine words `d * 2 ^ b` storing the bottom-level table `T₂`. -/
@[expose] def botWords (d b : ℕ) : ℕ :=
  d * 2 ^ b

/-- Total contiguous memory footprint `(c + 1) * d * 2 ^ b` words for Double Tabulation at
`[base, base + space c d b)`. -/
@[expose] def space (c d b : ℕ) : ℕ :=
  (c + 1) * d * 2 ^ b

theorem topWords_add_botWords (c d b : ℕ) :
    topWords c d b + botWords d b = space c d b := by
  dsimp only [topWords, botWords, space]
  ring

/-- Memory address `base + (j.val * c + i.val) * 2 ^ b + ch.val` of top-table entry `T₁ i j ch`. -/
@[expose] def topAddr (base c b : ℕ) {d : ℕ} (i : Fin c) (j : Fin d) (ch : Fin (2 ^ b)) : ℕ :=
  base + (j.val * c + i.val) * 2 ^ b + ch.val

/-- Memory address `base + c * d * 2 ^ b + j.val * 2 ^ b + y.val` of bottom-table entry `T₂ j y`. -/
@[expose] def botAddr (base c d b : ℕ) (j : Fin d) (y : Fin (2 ^ b)) : ℕ :=
  base + c * d * 2 ^ b + j.val * 2 ^ b + y.val

theorem topAddr_lt_base_add_topWords (base c d b : ℕ) (i : Fin c) (j : Fin d) (ch : Fin (2 ^ b)) :
    topAddr base c b i j ch < base + topWords c d b := by
  dsimp only [topAddr, topWords]
  have h1 : j.val * c + i.val + 1 ≤ d * c := by
    calc j.val * c + i.val + 1 ≤ j.val * c + c := Nat.add_le_add_left i.isLt _
      _ = (j.val + 1) * c := by ring
      _ ≤ d * c := Nat.mul_le_mul_right c j.isLt
  calc base + (j.val * c + i.val) * 2 ^ b + ch.val
      < base + (j.val * c + i.val) * 2 ^ b + 2 ^ b := Nat.add_lt_add_left ch.isLt _
    _ = base + (j.val * c + i.val + 1) * 2 ^ b := by ring
    _ ≤ base + (d * c) * 2 ^ b := Nat.add_le_add_left (Nat.mul_le_mul_right _ h1) base
    _ = base + c * d * 2 ^ b := by ring

theorem botAddr_lt_base_add_space (base c d b : ℕ) (j : Fin d) (y : Fin (2 ^ b)) :
    botAddr base c d b j y < base + space c d b := by
  dsimp only [botAddr, space]
  calc base + c * d * 2 ^ b + j.val * 2 ^ b + y.val
      < base + c * d * 2 ^ b + j.val * 2 ^ b + 2 ^ b := Nat.add_lt_add_left y.isLt _
    _ = base + c * d * 2 ^ b + (j.val + 1) * 2 ^ b := by ring
    _ ≤ base + c * d * 2 ^ b + d * 2 ^ b :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ j.isLt) _
    _ = base + (c + 1) * d * 2 ^ b := by ring

/-- Memory representation predicate for the top-level table `T₁ : DoubleTabTopSeed c d b`. -/
@[expose] def TopRep (base c d b : ℕ) (T₁ : DoubleTabTopSeed c d b) (mem : ℕ → ℕ) : Prop :=
  ∀ (i : Fin c) (j : Fin d) (ch : Fin (2 ^ b)), mem (topAddr base c b i j ch) = (T₁ i j ch).val

/-- Memory representation predicate for the bottom-level table `T₂ : DoubleTabBotSeed d b M`. -/
@[expose] def BotRep (base c d b M : ℕ) (T₂ : DoubleTabBotSeed d b M) (mem : ℕ → ℕ) : Prop :=
  ∀ (j : Fin d) (y : Fin (2 ^ b)), mem (botAddr base c d b j y) = (T₂ j y).val

/-- Combined memory representation predicate for `(T₁, T₂)` at `[base, base + space c d b)`. -/
@[expose] def SeedRep (base c d b M : ℕ)
    (θ : DoubleTabTopSeed c d b × DoubleTabBotSeed d b M) (mem : ℕ → ℕ) : Prop :=
  TopRep base c d b θ.1 mem ∧ BotRep base c d b M θ.2 mem

/-- Linear-index equivalence `Fin c × Fin d × Fin (2 ^ b) ≃ Fin (c * d * 2 ^ b)` mapping
`(i, j, ch)` to `(j.val * c + i.val) * 2 ^ b + ch.val`. -/
@[expose] def topIndexEquiv (c d b : ℕ) :
    (Fin c × Fin d × Fin (2 ^ b)) ≃ Fin (c * d * 2 ^ b) :=
  ((Equiv.prodAssoc (Fin c) (Fin d) (Fin (2 ^ b))).symm.trans
    (Equiv.prodCongr ((Equiv.prodComm (Fin c) (Fin d)).trans finProdFinEquiv)
      (Equiv.refl (Fin (2 ^ b))))).trans
    (finProdFinEquiv.trans (finCongr (by ring)))

@[simp]
theorem val_topIndexEquiv (c d b : ℕ) (i : Fin c) (j : Fin d) (ch : Fin (2 ^ b)) :
    (topIndexEquiv c d b (i, j, ch)).val = (j.val * c + i.val) * 2 ^ b + ch.val := by
  simp only [topIndexEquiv, Equiv.trans_apply, Equiv.prodAssoc_symm_apply,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
    Equiv.refl_apply, finCongr_apply, Fin.val_cast, finProdFinEquiv_apply_val]
  ring

/-- Equivalence between flat `(c * d * 2 ^ b)`-word slices and `DoubleTabTopSeed c d b`. -/
@[expose] def topSliceEquiv (c d b : ℕ) :
    (Fin (c * d * 2 ^ b) → Fin (2 ^ b)) ≃ DoubleTabTopSeed c d b :=
  (Equiv.arrowCongr (topIndexEquiv c d b).symm (Equiv.refl (Fin (2 ^ b)))).trans
    ((Equiv.curry _ _ _).trans (Equiv.piCongrRight fun _ => Equiv.curry _ _ _))

/-- Equivalence between flat `(d * 2 ^ b)`-word slices and `DoubleTabBotSeed d b M`. -/
@[expose] def botSliceEquiv (d b M : ℕ) :
    (Fin (d * 2 ^ b) → Fin (2 ^ M)) ≃ DoubleTabBotSeed d b M :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl (Fin (2 ^ M)))).trans
    (Equiv.curry _ _ _)

/-- Extract the top-level seed `T₁ : DoubleTabTopSeed c d b` from `[base, base + c * d * 2 ^ b)`. -/
@[expose] def extractTop (base c d b : ℕ) (mem : ℕ → ℕ) : DoubleTabTopSeed c d b :=
  topSliceEquiv c d b (Tabulation.extractSlice base b (c * d * 2 ^ b) mem)

/-- Extract the bottom-level seed `T₂ : DoubleTabBotSeed d b M` from
`[base + c * d * 2 ^ b, base + (c + 1) * d * 2 ^ b)`. -/
@[expose] def extractBot (base c d b M : ℕ) (mem : ℕ → ℕ) : DoubleTabBotSeed d b M :=
  botSliceEquiv d b M (Tabulation.extractSlice (base + c * d * 2 ^ b) M (d * 2 ^ b) mem)

/-- Extract the pair `(T₁, T₂)` from `[base, base + space c d b)`. -/
@[expose] def extractSeed (base c d b M : ℕ) (mem : ℕ → ℕ) :
    DoubleTabTopSeed c d b × DoubleTabBotSeed d b M :=
  (extractTop base c d b mem, extractBot base c d b M mem)

theorem extractTop_apply (base c d b : ℕ) (mem : ℕ → ℕ)
    (i : Fin c) (j : Fin d) (ch : Fin (2 ^ b)) :
    extractTop base c d b mem i j ch =
      Tabulation.extractWord b (mem (topAddr base c b i j ch)) := by
  change Tabulation.extractWord b (mem (base + (topIndexEquiv c d b (i, j, ch)).val)) =
    Tabulation.extractWord b (mem (topAddr base c b i j ch))
  rw [val_topIndexEquiv, topAddr, Nat.add_assoc]

theorem extractBot_apply (base c d b M : ℕ) (mem : ℕ → ℕ)
    (j : Fin d) (y : Fin (2 ^ b)) :
    extractBot base c d b M mem j y =
      Tabulation.extractWord M (mem (botAddr base c d b j y)) := by
  change Tabulation.extractWord M (mem ((base + c * d * 2 ^ b) + (finProdFinEquiv (j, y)).val)) =
    Tabulation.extractWord M (mem (botAddr base c d b j y))
  rw [finProdFinEquiv_apply_val, botAddr]
  congr 2
  ring

theorem SeedRep.congr_mem {base c d b M : ℕ}
    {θ : DoubleTabTopSeed c d b × DoubleTabBotSeed d b M} {mem mem' : ℕ → ℕ}
    (hrep : SeedRep base c d b M θ mem)
    (heq : ∀ a, base ≤ a → a < base + space c d b → mem' a = mem a) :
    SeedRep base c d b M θ mem' := by
  have hsp := topWords_add_botWords c d b
  refine ⟨fun i j ch => ?_, fun j y => ?_⟩
  · have hlt := topAddr_lt_base_add_topWords base c d b i j ch
    have hge : base ≤ topAddr base c b i j ch := by dsimp only [topAddr]; omega
    rw [heq _ hge (by dsimp only [topWords, botWords] at hsp hlt; omega)]
    exact hrep.1 i j ch
  · have hlt := botAddr_lt_base_add_space base c d b j y
    have hge : base ≤ botAddr base c d b j y := by dsimp only [botAddr]; omega
    rw [heq _ hge hlt]
    exact hrep.2 j y

theorem extractSeed_congr_mem {base c d b M : ℕ} {mem mem' : ℕ → ℕ}
    (heq : ∀ a, base ≤ a → a < base + space c d b → mem' a = mem a) :
    extractSeed base c d b M mem' = extractSeed base c d b M mem := by
  have hsp := topWords_add_botWords c d b
  dsimp only [extractSeed]
  congr 1
  · funext i j ch
    rw [extractTop_apply, extractTop_apply]
    have hlt := topAddr_lt_base_add_topWords base c d b i j ch
    have hge : base ≤ topAddr base c b i j ch := by dsimp only [topAddr]; omega
    rw [heq _ hge (by dsimp only [topWords, botWords] at hsp hlt; omega)]
  · funext j y
    rw [extractBot_apply, extractBot_apply]
    have hlt := botAddr_lt_base_add_space base c d b j y
    have hge : base ≤ botAddr base c d b j y := by dsimp only [botAddr]; omega
    rw [heq _ hge hlt]

/-! ## Section 2: Register layout and randomized seed resampling (`resampleCode`) -/

/-- Register `0`: persistent base address `base`. -/
abbrev regBase : Fin 12 := 0

/-- Register `1`: input key `u.val` in `evalCode`. -/
abbrev regKey : Fin 12 := 1

/-- Register `2`: output accumulator `acc` in `evalCode`. -/
abbrev regOut : Fin 12 := 2

/-- Register `3`: top-table pointer / `randFillLoop` write pointer. -/
abbrev regTopPtr : Fin 12 := 3

/-- Register `4`: bottom-table pointer / `randFillLoop` end pointer. -/
abbrev regBotPtr : Fin 12 := 4

/-- Register `5`: bottom-table end pointer / `randFillLoop` bitmask. -/
abbrev regBotEnd : Fin 12 := 5

/-- Register `6`: remaining inner-loop count `remC` / `randFillLoop` constant `1`. -/
abbrev regRemC : Fin 12 := 6

/-- Register `7`: shifted key `curU` / `randFillLoop` sampled value. -/
abbrev regCurU : Fin 12 := 7

/-- Register `8`: inner XOR accumulator `y_j`. -/
abbrev regYJ : Fin 12 := 8

/-- Register `9`: general scratch register for masks, addresses, and loaded entries. -/
abbrev regTmp : Fin 12 := 9

/-- Register `10`: character alphabet size `2 ^ b`. -/
abbrev regPowB : Fin 12 := 10

/-- Register `11`: constant `0`. -/
abbrev regZero : Fin 12 := 11

/-- Register injection `Fin 6 → Fin 12` mapping `Tabulation.randFillLoop`'s
`(ptr, end, mask, one, val, extra)` to `(3, 4, 5, 6, 7, 0)`. -/
@[expose] def fillMap12 : Fin 6 → Fin 12
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 5
  | ⟨3, _⟩ => 6
  | ⟨4, _⟩ => 7
  | ⟨5, _⟩ => 0

theorem injective_fillMap12 : Function.Injective fillMap12 := by
  decide

/-- Setup program before the first `randFillLoop` call (`5` instructions): sets `reg 3 ← base`,
`reg 4 ← base + c * d * 2 ^ b`, `reg 5 ← 2 ^ b - 1`, and `reg 6 ← 1`. -/
@[expose] def resampleSetup1Code (c d b : ℕ) : Code .exact 12 :=
  .seq (.op (.copy 3 0))
  (.seq (.op (.const 4 (c * d * 2 ^ b)))
  (.seq (.op (.exactBin .add 4 0 4))
  (.seq (.op (.const 5 (2 ^ b - 1)))
        (.op (.const 6 1)))))

/-- State after `resampleSetup1Code c d b` from `x`. -/
@[expose] def resampleSetup1Data (base c d b : ℕ) (x : Data 12) : Data 12 :=
  ((((x.set 3 base).set 4 (c * d * 2 ^ b)).set 4 (base + c * d * 2 ^ b)).set 5 (2 ^ b - 1)).set 6 1

/-- Setup program before the second `randFillLoop` call (`4` instructions): sets
`reg 3 ← base + c * d * 2 ^ b`, `reg 4 ← base + c * d * 2 ^ b + d * 2 ^ b`, and
`reg 5 ← 2 ^ M - 1`. -/
@[expose] def resampleSetup2Code (d b M : ℕ) : Code .exact 12 :=
  .seq (.op (.copy 3 4))
  (.seq (.op (.const 5 (d * 2 ^ b)))
  (.seq (.op (.exactBin .add 4 4 5))
        (.op (.const 5 (2 ^ M - 1)))))

/-- State after `resampleSetup2Code d b M` from `x`. -/
@[expose] def resampleSetup2Data (base c d b M : ℕ) (x : Data 12) : Data 12 :=
  (((x.set 3 (base + c * d * 2 ^ b)).set 5 (d * 2 ^ b)).set 4
    (base + c * d * 2 ^ b + d * 2 ^ b)).set 5 (2 ^ M - 1)

/-- Structured Word-RAM program on `Data 12` that resamples both `T₁` and `T₂` via two sequential
`Tabulation.randFillLoop` calls. -/
@[expose] def resampleCode (c d b M : ℕ) : Code .exact 12 :=
  .seq (resampleSetup1Code c d b)
  (.seq (Tabulation.randFillLoop.rename fillMap12)
  (.seq (resampleSetup2Code d b M)
        (Tabulation.randFillLoop.rename fillMap12)))

/-- Exact instruction count `5 * space c d b + 13` of `resampleCode c d b M`. -/
@[expose] def resampleSteps (c d b : ℕ) : ℕ :=
  5 * space c d b + 13

/-- Explicit `ProbComp (Data 12 × ℕ)` induced by `resampleCode c d b M`. -/
@[expose] noncomputable def resampleComp (base c d b M : ℕ) (x : Data 12) :
    ProbComp (Data 12 × ℕ) := do
  let x1 := resampleSetup1Data base c d b x
  let z1 ← Tabulation.randFillComp b base (c * d * 2 ^ b) (x1.comap fillMap12)
  let x2 := resampleSetup2Data base c d b M (z1.1.extend fillMap12 x1)
  let z2 ← Tabulation.randFillComp M (base + c * d * 2 ^ b) (d * 2 ^ b) (x2.comap fillMap12)
  pure (z2.1.extend fillMap12 x2, 5 + (z1.2 + (4 + z2.2)))

private theorem resampleSetup1Code_exec {w base c d b : ℕ} {x : Data 12}
    (hbase : x.regs 0 = base)
    (hfit_top : Fits w (base + c * d * 2 ^ b))
    (hfit_mask_b : Fits w (2 ^ b - 1))
    (hfit_1 : Fits w 1) :
    Exec w (resampleSetup1Code c d b) x (resampleSetup1Data base c d b x) 5 := by
  have hfit_top_len : Fits w (c * d * 2 ^ b) := hfit_top.of_le (Nat.le_add_left _ _)
  set s1 := x.set 3 base
  have e1 : Exec w (.op (.copy 3 0) : Code .exact 12) x s1 1 := by
    simpa [s1, hbase] using (Exec.copy (B := .exact) (w := w) (d := 3) (s := 0) (x := x))
  set s2 := s1.set 4 (c * d * 2 ^ b)
  have e2 : Exec w (.op (.const 4 (c * d * 2 ^ b)) : Code .exact 12) s1 s2 1 :=
    Exec.const hfit_top_len
  set s3 := s2.set 4 (base + c * d * 2 ^ b)
  have e3 : Exec w (.op (.exactBin .add 4 0 4) : Code .exact 12) s2 s3 1 :=
    exec_exactBin (by simp +decide [s2, s1, hbase]) hfit_top
  set s4 := s3.set 5 (2 ^ b - 1)
  have e4 : Exec w (.op (.const 5 (2 ^ b - 1)) : Code .exact 12) s3 s4 1 :=
    Exec.const hfit_mask_b
  set s5 := s4.set 6 1
  have e5 : Exec w (.op (.const 6 1) : Code .exact 12) s4 s5 1 :=
    Exec.const hfit_1
  simpa only [resampleSetup1Code, resampleSetup1Data, s5, s4, s3, s2, s1] using
    e1.seq (e2.seq (e3.seq (e4.seq e5)))

private theorem resampleSetup2Code_exec {w base c d b M : ℕ} {x : Data 12}
    (h4 : x.regs 4 = base + c * d * 2 ^ b)
    (hfit_end : Fits w (base + c * d * 2 ^ b + d * 2 ^ b))
    (hfit_mask_M : Fits w (2 ^ M - 1)) :
    Exec w (resampleSetup2Code d b M) x (resampleSetup2Data base c d b M x) 4 := by
  have hfit_bot_len : Fits w (d * 2 ^ b) := hfit_end.of_le (by omega)
  set s1 := x.set 3 (base + c * d * 2 ^ b)
  have e1 : Exec w (.op (.copy 3 4) : Code .exact 12) x s1 1 := by
    simpa [s1, h4] using (Exec.copy (B := .exact) (w := w) (d := 3) (s := 4) (x := x))
  set s2 := s1.set 5 (d * 2 ^ b)
  have e2 : Exec w (.op (.const 5 (d * 2 ^ b)) : Code .exact 12) s1 s2 1 :=
    Exec.const hfit_bot_len
  set s3 := s2.set 4 (base + c * d * 2 ^ b + d * 2 ^ b)
  have e3 : Exec w (.op (.exactBin .add 4 4 5) : Code .exact 12) s2 s3 1 :=
    exec_exactBin (by simp +decide [s2, s1, h4]) hfit_end
  set s4 := s3.set 5 (2 ^ M - 1)
  have e4 : Exec w (.op (.const 5 (2 ^ M - 1)) : Code .exact 12) s3 s4 1 :=
    Exec.const hfit_mask_M
  simpa only [resampleSetup2Code, resampleSetup2Data, s4, s3, s2, s1] using
    e1.seq (e2.seq (e3.seq e4))

/-- **Exact `ExecRand` execution of `resampleCode c d b M`**. -/
theorem resampleCode_execRand {w base c d b M : ℕ} {x : Data 12}
    (hbase : x.regs 0 = base)
    (hfit_space : Fits w (base + space c d b))
    (hfit_mask_b : Fits w (2 ^ b - 1))
    (hfit_mask_M : Fits w (2 ^ M - 1))
    (hfit_1 : Fits w 1) :
    ExecRand w (resampleCode c d b M) x (resampleComp base c d b M x) := by
  have hsp := topWords_add_botWords c d b
  have hfit_end : Fits w (base + c * d * 2 ^ b + d * 2 ^ b) :=
    hfit_space.of_le (by dsimp only [topWords, botWords] at hsp; omega)
  have hfit_top : Fits w (base + c * d * 2 ^ b) := hfit_end.of_le (by omega)
  set x1 := resampleSetup1Data base c d b x
  have h1 := (resampleSetup1Code_exec hbase hfit_top hfit_mask_b hfit_1).execRand
  have hloop1_inner := Tabulation.randFillLoop_execRand (w := w) (bits := b) (arrBase := base)
    (c * d * 2 ^ b) (x := x1.comap fillMap12)
    (by simp +decide [x1, resampleSetup1Data, fillMap12, Data.comap])
    (by simp +decide [x1, resampleSetup1Data, fillMap12, Data.comap])
    (by simp +decide [x1, resampleSetup1Data, fillMap12, Data.comap])
    (by simp +decide [x1, resampleSetup1Data, fillMap12, Data.comap])
    hfit_top hfit_mask_b
  have hloop1 := hloop1_inner.rename injective_fillMap12
  have hrest : ∀ z1 ∈ (Tabulation.randFillComp b base (c * d * 2 ^ b)
      (x1.comap fillMap12)).support,
      ExecRand w (.seq (resampleSetup2Code d b M) (Tabulation.randFillLoop.rename fillMap12))
        (z1.1.extend fillMap12 x1) (do
          let x2 := resampleSetup2Data base c d b M (z1.1.extend fillMap12 x1)
          let z2 ← Tabulation.randFillComp M (base + c * d * 2 ^ b) (d * 2 ^ b) (x2.comap fillMap12)
          pure (z2.1.extend fillMap12 x2, 4 + z2.2)) := by
    intro z1 hz1
    obtain ⟨_, _, hend1, _, hone1, _, _, _⟩ := Tabulation.mem_support_randFillComp hz1
    set y1 := z1.1.extend fillMap12 x1
    have hy1_4 : y1.regs 4 = base + c * d * 2 ^ b := by
      change (y1.comap fillMap12).regs Tabulation.regEnd = base + c * d * 2 ^ b
      rw [Data.comap_extend injective_fillMap12, hend1]
      simp +decide [x1, resampleSetup1Data, fillMap12, Data.comap]
    have hy1_6 : y1.regs 6 = 1 := by
      change (y1.comap fillMap12).regs Tabulation.regOne = 1
      rw [Data.comap_extend injective_fillMap12, hone1]
      simp +decide [x1, resampleSetup1Data, fillMap12, Data.comap]
    set x2 := resampleSetup2Data base c d b M y1
    have h2 := (resampleSetup2Code_exec hy1_4 hfit_end hfit_mask_M).execRand
    have hloop2_inner := Tabulation.randFillLoop_execRand (w := w) (bits := M)
      (arrBase := base + c * d * 2 ^ b) (d * 2 ^ b) (x := x2.comap fillMap12)
      (by simp +decide [x2, resampleSetup2Data, fillMap12, Data.comap])
      (by simp +decide [x2, resampleSetup2Data, fillMap12, Data.comap])
      (by simp +decide [x2, resampleSetup2Data, fillMap12, Data.comap])
      (by simp +decide [x2, resampleSetup2Data, fillMap12, Data.comap, hy1_6])
      hfit_end hfit_mask_M
    have hloop2 := hloop2_inner.rename injective_fillMap12
    have hseq2 := ExecRand.seq
      (m₂ := fun z : Data 12 =>
        (fun z2 : Data 6 × ℕ => (z2.1.extend fillMap12 z, z2.2)) <$>
          Tabulation.randFillComp M (base + c * d * 2 ^ b) (d * 2 ^ b) (z.comap fillMap12))
      h2 (fun z hz => by
        cases OracleComp.eq_of_mem_supportWith_pure hz
        exact hloop2)
    simpa only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def] using hseq2
  have hseq12 := ExecRand.seq
    (m₂ := fun z : Data 12 => do
      let x2 := resampleSetup2Data base c d b M z
      let z2 ← Tabulation.randFillComp M (base + c * d * 2 ^ b) (d * 2 ^ b) (x2.comap fillMap12)
      pure (z2.1.extend fillMap12 x2, 4 + z2.2))
    hloop1 (fun z hz => by
      obtain ⟨z1, hz1, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
      exact hrest z1 hz1)
  have hall := ExecRand.seq
    (m₂ := fun z : Data 12 => do
      let z1 ← Tabulation.randFillComp b base (c * d * 2 ^ b) (z.comap fillMap12)
      let x2 := resampleSetup2Data base c d b M (z1.1.extend fillMap12 z)
      let z2 ← Tabulation.randFillComp M (base + c * d * 2 ^ b) (d * 2 ^ b) (x2.comap fillMap12)
      pure (z2.1.extend fillMap12 x2, z1.2 + (4 + z2.2)))
    h1 (fun z hz => by
      cases OracleComp.eq_of_mem_supportWith_pure hz
      simpa only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def] using hseq12)
  simpa only [resampleCode, resampleComp, bind_assoc, pure_bind, map_eq_bind_pure_comp,
    Function.comp_def] using hall

/-- Pathwise postcondition of `resampleComp`: executes in `resampleSteps c d b` instructions,
preserves `reg 0 = base`, establishes `SeedRep base c d b M (extractSeed base c d b M z.1.mem)`,
and modifies only `[base, base + space c d b)`. -/
theorem mem_support_resampleComp {base c d b M : ℕ} {x : Data 12}
    (hbase : x.regs 0 = base) {z : Data 12 × ℕ}
    (hz : z ∈ (resampleComp base c d b M x).support) :
    z.1.regs 0 = base ∧
    SeedRep base c d b M (extractSeed base c d b M z.1.mem) z.1.mem ∧
    (∀ a, (a < base ∨ base + space c d b ≤ a) → z.1.mem a = x.mem a) ∧
    z.2 = resampleSteps c d b := by
  have hsp := topWords_add_botWords c d b
  dsimp only [resampleComp] at hz
  obtain ⟨z1, hz1, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
  obtain ⟨z2, hz2, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
  cases OracleComp.eq_of_mem_supportWith_pure hpure
  obtain ⟨hsteps1, _, _, _, _, hextra1, hlt1, hframe1⟩ := Tabulation.mem_support_randFillComp hz1
  obtain ⟨hsteps2, _, _, _, _, hextra2, hlt2, hframe2⟩ := Tabulation.mem_support_randFillComp hz2
  set x1 := resampleSetup1Data base c d b x
  set y1 := z1.1.extend fillMap12 x1
  set x2 := resampleSetup2Data base c d b M y1
  set y2 := z2.1.extend fillMap12 x2
  have hy1_0 : y1.regs 0 = base := by
    change (y1.comap fillMap12).regs Tabulation.regExtra = base
    rw [Data.comap_extend injective_fillMap12, hextra1]
    simp +decide [x1, resampleSetup1Data, fillMap12, Data.comap, hbase]
  have hy2_0 : y2.regs 0 = base := by
    change (y2.comap fillMap12).regs Tabulation.regExtra = base
    rw [Data.comap_extend injective_fillMap12, hextra2]
    simp +decide [x2, resampleSetup2Data, fillMap12, Data.comap, hy1_0]
  have hmem_top : ∀ i < c * d * 2 ^ b, z2.1.mem (base + i) = z1.1.mem (base + i) := by
    intro i hi
    exact hframe2 (base + i) (Or.inl (by omega))
  refine ⟨hy2_0, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j ch
    have hidx_lt : (j.val * c + i.val) * 2 ^ b + ch.val < c * d * 2 ^ b := by
      have h := topAddr_lt_base_add_topWords base c d b i j ch
      dsimp only [topAddr, topWords] at h
      omega
    have hm_eq : z2.1.mem (topAddr base c b i j ch) = z1.1.mem (topAddr base c b i j ch) := by
      dsimp only [topAddr]
      rw [Nat.add_assoc]
      exact hmem_top _ hidx_lt
    have hlt_val : z1.1.mem (topAddr base c b i j ch) < 2 ^ b := by
      dsimp only [topAddr]
      rw [Nat.add_assoc]
      exact hlt1 _ hidx_lt
    change z2.1.mem (topAddr base c b i j ch) = (extractTop base c d b z2.1.mem i j ch).val
    rw [extractTop_apply, hm_eq, Tabulation.extractWord_val_of_lt hlt_val]
  · intro j y
    have hidx_lt : j.val * 2 ^ b + y.val < d * 2 ^ b := by
      calc j.val * 2 ^ b + y.val < j.val * 2 ^ b + 2 ^ b := Nat.add_lt_add_left y.isLt _
        _ = (j.val + 1) * 2 ^ b := by ring
        _ ≤ d * 2 ^ b := Nat.mul_le_mul_right _ j.isLt
    have hlt_val : z2.1.mem (botAddr base c d b j y) < 2 ^ M := by
      dsimp only [botAddr]
      rw [Nat.add_assoc (base + c * d * 2 ^ b)]
      exact hlt2 _ hidx_lt
    change z2.1.mem (botAddr base c d b j y) = (extractBot base c d b M z2.1.mem j y).val
    rw [extractBot_apply, Tabulation.extractWord_val_of_lt hlt_val]
  · intro a ha
    have ha2 : a < base + c * d * 2 ^ b ∨ base + c * d * 2 ^ b + d * 2 ^ b ≤ a := by
      dsimp only [topWords, botWords] at hsp
      omega
    have ha1 : a < base ∨ base + c * d * 2 ^ b ≤ a := by
      dsimp only [topWords, botWords] at hsp
      omega
    change z2.1.mem a = x.mem a
    rw [hframe2 a ha2]
    exact hframe1 a ha1
  · dsimp only [resampleSteps]
    dsimp only [topWords, botWords] at hsp
    rw [hsteps1, hsteps2, ← hsp]
    ring

/-- Bind of two independent `PMF.uniformOfFintype` distributions is `PMF.uniformOfFintype` on the
product type `α × β`. -/
theorem uniformOfFintype_bind_prodMk {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    (PMF.uniformOfFintype α).bind (fun a => (PMF.uniformOfFintype β).map (a, ·)) =
      PMF.uniformOfFintype (α × β) := by
  ext ⟨a, b⟩
  rw [Cslib.Probability.PMF.bind_map_prodMk_apply, PMF.uniformOfFintype_apply,
    PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
      (Or.inl (ENNReal.natCast_ne_top _))]

/-- **Exact product uniformity of `resampleComp`**: `extractSeed base c d b M z.1.mem` under
`resampleComp base c d b M x` has distribution
`PMF.uniformOfFintype (DoubleTabTopSeed c d b × DoubleTabBotSeed d b M)`. -/
theorem map_extractSeed_eval_resampleComp (base c d b M : ℕ) (x : Data 12) :
    ((resampleComp base c d b M x).eval).map (fun z => extractSeed base c d b M z.1.mem) =
      PMF.uniformOfFintype (DoubleTabTopSeed c d b × DoubleTabBotSeed d b M) := by
  set x1 := resampleSetup1Data base c d b x
  set m1 := Tabulation.randFillComp b base (c * d * 2 ^ b) (x1.comap fillMap12)
  have hm1_unif : m1.eval.map (fun z1 : Data 6 × ℕ => extractTop base c d b z1.1.mem) =
      PMF.uniformOfFintype (DoubleTabTopSeed c d b) := by
    have hcomp : (fun z1 : Data 6 × ℕ => extractTop base c d b z1.1.mem) =
        topSliceEquiv c d b ∘
          fun z1 : Data 6 × ℕ => Tabulation.extractSlice base b (c * d * 2 ^ b) z1.1.mem := rfl
    rw [hcomp, ← PMF.map_comp, Tabulation.map_extractSlice_eval_randFillComp,
      PMF.uniformOfFintype_map_equiv]
  have hinner : ∀ z1 : Data 6 × ℕ,
      (let x2 := resampleSetup2Data base c d b M (z1.1.extend fillMap12 x1)
       (do
         let z2 ← Tabulation.randFillComp M (base + c * d * 2 ^ b) (d * 2 ^ b) (x2.comap fillMap12)
         pure (z2.1.extend fillMap12 x2, 5 + (z1.2 + (4 + z2.2)))).eval).map
        (fun z : Data 12 × ℕ => extractSeed base c d b M z.1.mem) =
      (PMF.uniformOfFintype (DoubleTabBotSeed d b M)).map
        (fun T₂ => (extractTop base c d b z1.1.mem, T₂)) := by
    intro z1
    dsimp only
    set x2 := resampleSetup2Data base c d b M (z1.1.extend fillMap12 x1)
    set m2 := Tabulation.randFillComp M (base + c * d * 2 ^ b) (d * 2 ^ b) (x2.comap fillMap12)
    have hd : (do
        let z2 ← m2
        pure (z2.1.extend fillMap12 x2, 5 + (z1.2 + (4 + z2.2)))) =
        (fun z2 : Data 6 × ℕ => (z2.1.extend fillMap12 x2, 5 + (z1.2 + (4 + z2.2)))) <$> m2 :=
      bind_pure_comp _ _
    rw [hd, ProbComp.eval_map, PMF.map_comp]
    have hcongr :
        m2.eval.map
          ((fun z : Data 12 × ℕ => extractSeed base c d b M z.1.mem) ∘
            fun z2 : Data 6 × ℕ => (z2.1.extend fillMap12 x2, 5 + (z1.2 + (4 + z2.2)))) =
        m2.eval.map
          ((fun T₂ => (extractTop base c d b z1.1.mem, T₂)) ∘
            botSliceEquiv d b M ∘
            fun z2 : Data 6 × ℕ =>
              Tabulation.extractSlice (base + c * d * 2 ^ b) M (d * 2 ^ b) z2.1.mem) := by
      refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun z2 hz2 => ?_
      rw [ProbComp.support_eval] at hz2
      obtain ⟨_, _, _, _, _, _, _, hframe2⟩ := Tabulation.mem_support_randFillComp hz2
      have htop_eq : extractTop base c d b z2.1.mem = extractTop base c d b z1.1.mem := by
        dsimp only [extractTop]
        congr 1
        funext idx
        dsimp only [Tabulation.extractSlice]
        rw [hframe2 (base + idx.val) (Or.inl (by have := idx.isLt; omega))]
        rfl
      dsimp only [Function.comp_apply, extractSeed, extractBot, Data.extend]
      rw [htop_eq]
    rw [hcongr, ← PMF.map_comp, ← PMF.map_comp, Tabulation.map_extractSlice_eval_randFillComp,
      PMF.uniformOfFintype_map_equiv]
  dsimp only [resampleComp]
  rw [ProbComp.eval_bind, PMF.map_bind]
  have hbind : m1.eval.bind
      (fun z1 =>
        (let x2 := resampleSetup2Data base c d b M (z1.1.extend fillMap12 x1)
         (do
           let z2 ←
             Tabulation.randFillComp M (base + c * d * 2 ^ b) (d * 2 ^ b) (x2.comap fillMap12)
           pure (z2.1.extend fillMap12 x2, 5 + (z1.2 + (4 + z2.2)))).eval).map
          (fun z : Data 12 × ℕ => extractSeed base c d b M z.1.mem)) =
      m1.eval.bind
        (fun z1 =>
          (PMF.uniformOfFintype (DoubleTabBotSeed d b M)).map
            (fun T₂ => (extractTop base c d b z1.1.mem, T₂))) := by
    congr 1
    funext z1
    exact hinner z1
  rw [hbind]
  have hmap_bind :
      m1.eval.bind
        (fun z1 =>
          (PMF.uniformOfFintype (DoubleTabBotSeed d b M)).map
            (fun T₂ => (extractTop base c d b z1.1.mem, T₂))) =
      (m1.eval.map (fun z1 => extractTop base c d b z1.1.mem)).bind
        (fun T₁ => (PMF.uniformOfFintype (DoubleTabBotSeed d b M)).map (T₁, ·)) := by
    rw [PMF.bind_map]
    rfl
  rw [hmap_bind, hm1_unif, uniformOfFintype_bind_prodMk]

/-! ## Section 3: Register-by-register deterministic query evaluation (`evalCode`) -/

/-- Setup before `outerLoop c b` (`8` instructions): initializes `reg 2 ← 0`, `reg 3 ← base`,
`reg 4 ← base + c * d * 2 ^ b`, `reg 5 ← base + c * d * 2 ^ b + d * 2 ^ b`, `reg 10 ← 2 ^ b`, and
`reg 11 ← 0`. -/
@[expose] def evalSetupCode (c d b : ℕ) : Code .exact 12 :=
  .seq (.op (.const 2 0))
  (.seq (.op (.copy 3 0))
  (.seq (.op (.const 4 (c * d * 2 ^ b)))
  (.seq (.op (.exactBin .add 4 0 4))
  (.seq (.op (.const 5 (d * 2 ^ b)))
  (.seq (.op (.exactBin .add 5 4 5))
  (.seq (.op (.const 10 (2 ^ b)))
        (.op (.const 11 0))))))))

/-- State after `evalSetupCode c d b` from `x`. -/
@[expose] def evalSetupData (base c d b : ℕ) (x : Data 12) : Data 12 :=
  (((((((x.set 2 0).set 3 base).set 4 (c * d * 2 ^ b)).set 4
    (base + c * d * 2 ^ b)).set 5 (d * 2 ^ b)).set 5
    (base + c * d * 2 ^ b + d * 2 ^ b)).set 10 (2 ^ b)).set 11 0

/-- Body of the inner loop over `i = 0 .. c - 1` (`10` instructions): extracts `ch = reg 7 &&&
(2 ^ b - 1)`, loads `mem[reg 3 + ch]`, XORs into `reg 8`, shifts `reg 7` right by `b`, advances
`reg 3` by `2 ^ b` (`reg 10`), and decrements `reg 6`. -/
@[expose] def innerBody (b : ℕ) : Code .exact 12 :=
  .seq (.op (.const 9 (2 ^ b - 1)))
  (.seq (.op (.exactBin .and 9 7 9))
  (.seq (.op (.exactBin .add 9 3 9))
  (.seq (.op (.load 9 9))
  (.seq (.op (.exactBin .xor 8 8 9))
  (.seq (.op (.const 9 b))
  (.seq (.op (.exactBin .shiftRight 7 7 9))
  (.seq (.op (.exactBin .add 3 3 10))
  (.seq (.op (.const 9 1))
        (.op (.exactBin .sub 6 6 9))))))))))

/-- Inner loop computing `y_j = ⨁_{i < c} T₁[i, j, x_i]` into `reg 8`. -/
@[expose] def innerLoop (b : ℕ) : Code .exact 12 :=
  .loop (.lt 11 6) (innerBody b)

/-- Body of the outer loop over `j = 0 .. d - 1`: initializes `reg 7 ← reg 1` (`u.val`),
`reg 8 ← 0`, `reg 6 ← c`, runs `innerLoop b`, loads `T₂[j, y_j]` from `mem[reg 4 + reg 8]`, XORs
into `reg 2`, and advances `reg 4` by `2 ^ b` (`reg 10`). -/
@[expose] def outerBody (c b : ℕ) : Code .exact 12 :=
  .seq (.op (.copy 7 1))
  (.seq (.op (.const 8 0))
  (.seq (.op (.const 6 c))
  (.seq (innerLoop b)
  (.seq (.op (.exactBin .add 9 4 8))
  (.seq (.op (.load 9 9))
  (.seq (.op (.exactBin .xor 2 2 9))
        (.op (.exactBin .add 4 4 10))))))))

/-- Outer loop over `j = 0 .. d - 1` (`reg 4 < reg 5`). -/
@[expose] def outerLoop (c b : ℕ) : Code .exact 12 :=
  .loop (.lt 4 5) (outerBody c b)

/-- Complete deterministic Word-RAM evaluation program for Double Tabulation on `Data 12`. -/
@[expose] def evalCode (c d b : ℕ) : Code .exact 12 :=
  .seq (evalSetupCode c d b) (outerLoop c b)

/-- Exact instruction count `(12 * c + 11) * d + 10` of `evalCode c d b`. -/
@[expose] def evalSteps (c d : ℕ) : ℕ :=
  (12 * c + 11) * d + 10

private def innerPrefixXor {c d b U : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (u : Fin U) (j : Fin d) (i : ℕ) (hi : i ≤ c) : Fin (2 ^ b) :=
  BitString.equivFin b
    (∑ k : Fin i,
      (BitString.equivFin b).symm
        (T₁ (Fin.castLE hi k) j (charDigits c b u (Fin.castLE hi k))))

private theorem val_innerPrefixXor_zero {c d b U : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (u : Fin U) (j : Fin d) :
    (innerPrefixXor T₁ u j 0 (Nat.zero_le c)).val = 0 := by
  dsimp only [innerPrefixXor]
  rw [Finset.univ_eq_empty, Finset.sum_empty]
  exact BitString.val_equivFin_false b

private theorem val_innerPrefixXor_succ {c d b U : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (u : Fin U) (j : Fin d) {i : ℕ} (hi : i + 1 ≤ c) :
    (innerPrefixXor T₁ u j (i + 1) hi).val =
      (innerPrefixXor T₁ u j i (Nat.le_of_succ_le hi)).val ^^^
        (T₁ ⟨i, hi⟩ j (charDigits c b u ⟨i, hi⟩)).val := by
  dsimp only [innerPrefixXor]
  rw [Fin.sum_univ_castSucc, BitString.val_equivFin_add, Equiv.apply_symm_apply]
  rfl

private theorem innerPrefixXor_full {c d b U : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (u : Fin U) (j : Fin d) :
    innerPrefixXor T₁ u j c le_rfl = simpleTabTuple T₁ (charDigits c b u) j := by
  rfl

private def outerPrefixXor {c d b U M : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (T₂ : DoubleTabBotSeed d b M) (u : Fin U) (j : ℕ) (hj : j ≤ d) : Fin (2 ^ M) :=
  BitString.equivFin M
    (∑ k : Fin j,
      (BitString.equivFin M).symm
        (T₂ (Fin.castLE hj k)
          (simpleTabTuple T₁ (charDigits c b u) (Fin.castLE hj k))))

private theorem val_outerPrefixXor_zero {c d b U M : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (T₂ : DoubleTabBotSeed d b M) (u : Fin U) :
    (outerPrefixXor T₁ T₂ u 0 (Nat.zero_le d)).val = 0 := by
  dsimp only [outerPrefixXor]
  rw [Finset.univ_eq_empty, Finset.sum_empty]
  exact BitString.val_equivFin_false M

private theorem val_outerPrefixXor_succ {c d b U M : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (T₂ : DoubleTabBotSeed d b M) (u : Fin U) {j : ℕ} (hj : j + 1 ≤ d) :
    (outerPrefixXor T₁ T₂ u (j + 1) hj).val =
      (outerPrefixXor T₁ T₂ u j (Nat.le_of_succ_le hj)).val ^^^
        (T₂ ⟨j, hj⟩ (simpleTabTuple T₁ (charDigits c b u) ⟨j, hj⟩)).val := by
  dsimp only [outerPrefixXor]
  rw [Fin.sum_univ_castSucc, BitString.val_equivFin_add, Equiv.apply_symm_apply]
  rfl

private theorem outerPrefixXor_full {c d b U M : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (T₂ : DoubleTabBotSeed d b M) (u : Fin U) :
    outerPrefixXor T₁ T₂ u d le_rfl = doubleTabHash c d b U M T₁ T₂ u := by
  rfl

private theorem evalSetupCode_exec {w base c d b : ℕ} {x : Data 12}
    (hbase : x.regs 0 = base)
    (hfit_space : Fits w (base + space c d b))
    (hfit_pow_b : Fits w (2 ^ b)) :
    Exec w (evalSetupCode c d b) x (evalSetupData base c d b x) 8 := by
  have hsp := topWords_add_botWords c d b
  have hfit_end : Fits w (base + c * d * 2 ^ b + d * 2 ^ b) :=
    hfit_space.of_le (by dsimp only [topWords, botWords] at hsp; omega)
  have hfit_top : Fits w (base + c * d * 2 ^ b) := hfit_end.of_le (by omega)
  have hfit_top_len : Fits w (c * d * 2 ^ b) := hfit_top.of_le (Nat.le_add_left _ _)
  have hfit_bot_len : Fits w (d * 2 ^ b) := hfit_end.of_le (by omega)
  have hfit_0 : Fits w 0 := hfit_space.of_le (Nat.zero_le _)
  set s1 := x.set 2 0
  have e1 : Exec w (.op (.const 2 0) : Code .exact 12) x s1 1 := Exec.const hfit_0
  set s2 := s1.set 3 base
  have e2 : Exec w (.op (.copy 3 0) : Code .exact 12) s1 s2 1 := by
    simpa [s2, s1, hbase] using (Exec.copy (B := .exact) (w := w) (d := 3) (s := 0) (x := s1))
  set s3 := s2.set 4 (c * d * 2 ^ b)
  have e3 : Exec w (.op (.const 4 (c * d * 2 ^ b)) : Code .exact 12) s2 s3 1 :=
    Exec.const hfit_top_len
  set s4 := s3.set 4 (base + c * d * 2 ^ b)
  have e4 : Exec w (.op (.exactBin .add 4 0 4) : Code .exact 12) s3 s4 1 :=
    exec_exactBin (by simp +decide [s3, s2, s1, hbase]) hfit_top
  set s5 := s4.set 5 (d * 2 ^ b)
  have e5 : Exec w (.op (.const 5 (d * 2 ^ b)) : Code .exact 12) s4 s5 1 :=
    Exec.const hfit_bot_len
  set s6 := s5.set 5 (base + c * d * 2 ^ b + d * 2 ^ b)
  have e6 : Exec w (.op (.exactBin .add 5 4 5) : Code .exact 12) s5 s6 1 :=
    exec_exactBin (by simp +decide [s5, s4]) hfit_end
  set s7 := s6.set 10 (2 ^ b)
  have e7 : Exec w (.op (.const 10 (2 ^ b)) : Code .exact 12) s6 s7 1 :=
    Exec.const hfit_pow_b
  set s8 := s7.set 11 0
  have e8 : Exec w (.op (.const 11 0) : Code .exact 12) s7 s8 1 :=
    Exec.const hfit_0
  simpa only [evalSetupCode, evalSetupData, s8, s7, s6, s5, s4, s3, s2, s1] using
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))

private theorem innerLoop_exec {w base c d b U r2 r4 r5 : ℕ} {x_init : Data 12}
    {T₁ : DoubleTabTopSeed c d b}
    (htop : TopRep base c d b T₁ x_init.mem) (u : Fin U) (j : Fin d)
    (hfit_space : Fits w (base + space c d b))
    (hfit_pow_b : Fits w (2 ^ b))
    (hfit_u : Fits w u.val) :
    ∀ (rem i : ℕ) (x : Data 12) (hsum : i + rem = c),
      x.mem = x_init.mem →
      x.regs 0 = base →
      x.regs 1 = u.val →
      x.regs 2 = r2 →
      x.regs 3 = base + (j.val * c + i) * 2 ^ b →
      x.regs 4 = r4 →
      x.regs 5 = r5 →
      x.regs 6 = rem →
      x.regs 7 = u.val >>> (i * b) →
      x.regs 8 = (innerPrefixXor T₁ u j i (by omega)).val →
      x.regs 10 = 2 ^ b →
      x.regs 11 = 0 →
      ∃ y : Data 12,
        Exec w (innerLoop b) x y (12 * rem + 2) ∧
        y.mem = x_init.mem ∧
        y.regs 0 = base ∧
        y.regs 1 = u.val ∧
        y.regs 2 = r2 ∧
        y.regs 3 = base + (j.val + 1) * c * 2 ^ b ∧
        y.regs 4 = r4 ∧
        y.regs 5 = r5 ∧
        y.regs 8 = (simpleTabTuple T₁ (charDigits c b u) j).val ∧
        y.regs 10 = 2 ^ b ∧
        y.regs 11 = 0 := by
  intro rem
  induction rem with
  | zero =>
    intro i x hsum hmem h0 h1 h2 h3 h4 h5 h6 _ h8 h10 h11
    have hi_eq : i = c := by omega
    subst hi_eq
    have hc : ¬(Cond.lt 11 6).Holds x := by simp [Cond.Holds, h11, h6]
    refine ⟨x, Exec.loop_exit hc, hmem, h0, h1, h2, ?_, h4, h5, ?_, h10, h11⟩
    · rw [h3]
      ring
    · rw [h8, innerPrefixXor_full]
  | succ rem ih =>
    intro i x hsum hmem h0 h1 h2 h3 h4 h5 h6 h7 h8 h10 h11
    have hi_lt : i < c := by omega
    have hi_succ : i + 1 ≤ c := by omega
    have hc : (Cond.lt 11 6).Holds x := by simp [Cond.Holds, h11, h6]
    have hfit_mask : Fits w (2 ^ b - 1) := hfit_pow_b.of_le (Nat.pred_le _)
    have hfit_b : Fits w b := hfit_pow_b.of_le (le_of_lt Nat.lt_two_pow_self)
    have hfit_1 : Fits w 1 := hfit_pow_b.of_le Nat.one_le_two_pow
    let ch := charDigits c b u ⟨i, hi_lt⟩
    have hch_eq : (u.val >>> (i * b)) &&& (2 ^ b - 1) = ch.val := rfl
    have hfit_ch : Fits w ((u.val >>> (i * b)) &&& (2 ^ b - 1)) :=
      hfit_pow_b.of_le (by rw [hch_eq]; exact le_of_lt ch.isLt)
    have hsp := topWords_add_botWords c d b
    have haddr_lt : topAddr base c b ⟨i, hi_lt⟩ j ch < base + space c d b := by
      calc topAddr base c b ⟨i, hi_lt⟩ j ch < base + topWords c d b :=
            topAddr_lt_base_add_topWords base c d b ⟨i, hi_lt⟩ j ch
        _ ≤ base + space c d b := by omega
    have hfit_addr : Fits w (topAddr base c b ⟨i, hi_lt⟩ j ch) :=
      hfit_space.of_le (le_of_lt haddr_lt)
    have hmem_at : x.mem (topAddr base c b ⟨i, hi_lt⟩ j ch) = (T₁ ⟨i, hi_lt⟩ j ch).val := by
      rw [hmem]
      exact htop ⟨i, hi_lt⟩ j ch
    have hxor_eq := val_innerPrefixXor_succ T₁ u j hi_succ
    have hfit_xor : Fits w ((innerPrefixXor T₁ u j i (by omega)).val ^^^
        (T₁ ⟨i, hi_lt⟩ j ch).val) := by
      rw [← hxor_eq]
      exact hfit_pow_b.of_le (le_of_lt (innerPrefixXor T₁ u j (i + 1) hi_succ).isLt)
    have hshift_eq : (u.val >>> (i * b)) >>> b = u.val >>> ((i + 1) * b) := by
      rw [← Nat.shiftRight_add]
      congr 1
      ring
    have hfit_shift : Fits w ((u.val >>> (i * b)) >>> b) :=
      hfit_u.of_le ((Nat.shiftRight_le _ _).trans (Nat.shiftRight_le _ _))
    have hptr_next_le : base + (j.val * c + i) * 2 ^ b + 2 ^ b ≤ base + space c d b := by
      have h1 : j.val * c + i + 1 ≤ d * c := by
        calc j.val * c + i + 1 ≤ j.val * c + c := Nat.add_le_add_left hi_succ _
          _ = (j.val + 1) * c := by ring
          _ ≤ d * c := Nat.mul_le_mul_right c j.isLt
      have hdc_le : d * c ≤ (c + 1) * d := by
        rw [Nat.mul_comm d c]
        exact Nat.mul_le_mul_right d (Nat.le_succ c)
      calc base + (j.val * c + i) * 2 ^ b + 2 ^ b
          = base + (j.val * c + i + 1) * 2 ^ b := by ring
        _ ≤ base + (d * c) * 2 ^ b := Nat.add_le_add_left (Nat.mul_le_mul_right _ h1) base
        _ ≤ base + (c + 1) * d * 2 ^ b :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hdc_le) base
    have hfit_ptr_next : Fits w (base + (j.val * c + i) * 2 ^ b + 2 ^ b) :=
      hfit_space.of_le hptr_next_le
    have hfit_rem : Fits w (rem + 1 - 1) :=
      hfit_space.of_le (by
        have hd_pos : 1 ≤ d := by have := j.isLt; omega
        have hb_pos : 1 ≤ 2 ^ b := Nat.one_le_two_pow
        have hc_le : c ≤ (c + 1) * d * 2 ^ b :=
          calc c ≤ c + 1 := Nat.le_succ c
            _ ≤ (c + 1) * d := Nat.le_mul_of_pos_right _ hd_pos
            _ ≤ (c + 1) * d * 2 ^ b := Nat.le_mul_of_pos_right _ hb_pos
        dsimp only [space]
        omega)
    set s1 := x.set 9 (2 ^ b - 1)
    have e1 : Exec w (.op (.const 9 (2 ^ b - 1)) : Code .exact 12) x s1 1 :=
      Exec.const hfit_mask
    set s2 := s1.set 9 ch.val
    have e2 : Exec w (.op (.exactBin .and 9 7 9) : Code .exact 12) s1 s2 1 :=
      exec_exactBin (by simp +decide [s1, h7, hch_eq]) (by rwa [← hch_eq])
    set s3 := s2.set 9 (topAddr base c b ⟨i, hi_lt⟩ j ch)
    have e3 : Exec w (.op (.exactBin .add 9 3 9) : Code .exact 12) s2 s3 1 :=
      exec_exactBin (by simp +decide [s2, s1, h3, topAddr]) hfit_addr
    set s4 := s3.set 9 (T₁ ⟨i, hi_lt⟩ j ch).val
    have e4 : Exec w (.op (.load 9 9) : Code .exact 12) s3 s4 1 := by
      simpa +decide [s4, s3, s2, s1, hmem_at] using
        (Exec.load (B := .exact) (w := w) (d := 9) (a := 9) (x := s3))
    set s5 := s4.set 8 (innerPrefixXor T₁ u j (i + 1) hi_succ).val
    have e5 : Exec w (.op (.exactBin .xor 8 8 9) : Code .exact 12) s4 s5 1 :=
      exec_exactBin (by simp +decide [s4, s3, s2, s1, h8, hxor_eq, ch])
        (by rwa [hxor_eq])
    set s6 := s5.set 9 b
    have e6 : Exec w (.op (.const 9 b) : Code .exact 12) s5 s6 1 :=
      Exec.const hfit_b
    set s7 := s6.set 7 (u.val >>> ((i + 1) * b))
    have e7 : Exec w (.op (.exactBin .shiftRight 7 7 9) : Code .exact 12) s6 s7 1 :=
      exec_exactBin (by simp +decide [s6, s5, s4, s3, s2, s1, h7, hshift_eq])
        (by rwa [← hshift_eq])
    set s8 := s7.set 3 (base + (j.val * c + (i + 1)) * 2 ^ b)
    have e8 : Exec w (.op (.exactBin .add 3 3 10) : Code .exact 12) s7 s8 1 :=
      exec_exactBin
        (by
          rw [show base + (j.val * c + (i + 1)) * 2 ^ b =
            base + (j.val * c + i) * 2 ^ b + 2 ^ b by ring]
          simp +decide [s7, s6, s5, s4, s3, s2, s1, h3, h10])
        (by
          rw [show base + (j.val * c + (i + 1)) * 2 ^ b =
            base + (j.val * c + i) * 2 ^ b + 2 ^ b by ring]
          exact hfit_ptr_next)
    set s9 := s8.set 9 1
    have e9 : Exec w (.op (.const 9 1) : Code .exact 12) s8 s9 1 :=
      Exec.const hfit_1
    set s10 := s9.set 6 rem
    have e10 : Exec w (.op (.exactBin .sub 6 6 9) : Code .exact 12) s9 s10 1 :=
      exec_exactBin (by simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, h6]) hfit_rem
    have hbody := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq e10))))))))
    obtain ⟨y, hrec, hymem, hy0, hy1, hy2, hy3, hy4, hy5, hy8, hy10, hy11⟩ :=
      ih (i + 1) s10 (by omega)
        hmem
        (by simp +decide [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0])
        (by simp +decide [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h1])
        (by simp +decide [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h2])
        (by simp +decide [s10, s9, s8])
        (by simp +decide [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h4])
        (by simp +decide [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h5])
        (by simp +decide [s10])
        (by simp +decide [s10, s9, s8, s7])
        (by simp +decide [s10, s9, s8, s7, s6, s5])
        (by simp +decide [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h10])
        (by simp +decide [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h11])
    refine ⟨y, ?_, hymem, hy0, hy1, hy2, hy3, hy4, hy5, hy8, hy10, hy11⟩
    simpa only [innerLoop, innerBody,
      show 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))) + (12 * rem + 2) + 2 =
        12 * (rem + 1) + 2 by omega] using Exec.loop_iter hc hbody hrec

private theorem outerLoop_exec {w base c d b U M : ℕ} {x_init : Data 12}
    {T₁ : DoubleTabTopSeed c d b} {T₂ : DoubleTabBotSeed d b M}
    (htop : TopRep base c d b T₁ x_init.mem)
    (hbot : BotRep base c d b M T₂ x_init.mem)
    (u : Fin U)
    (hfit_space : Fits w (base + space c d b))
    (hfit_pow_b : Fits w (2 ^ b))
    (hfit_pow_M : Fits w (2 ^ M))
    (hfit_u : Fits w u.val) :
    ∀ (remD j : ℕ) (x : Data 12) (hsum : j + remD = d),
      x.mem = x_init.mem →
      x.regs 0 = base →
      x.regs 1 = u.val →
      x.regs 2 = (outerPrefixXor T₁ T₂ u j (by omega)).val →
      x.regs 3 = base + j * c * 2 ^ b →
      x.regs 4 = base + c * d * 2 ^ b + j * 2 ^ b →
      x.regs 5 = base + c * d * 2 ^ b + d * 2 ^ b →
      x.regs 10 = 2 ^ b →
      x.regs 11 = 0 →
      ∃ y : Data 12,
        Exec w (outerLoop c b) x y ((12 * c + 11) * remD + 2) ∧
        y.mem = x_init.mem ∧
        y.regs 0 = base ∧
        y.regs 1 = u.val ∧
        y.regs 2 = (doubleTabHash c d b U M T₁ T₂ u).val := by
  intro remD
  induction remD with
  | zero =>
    intro j x hsum hmem h0 h1 h2 _ h4 h5 _ _
    have hj_eq : j = d := by omega
    subst hj_eq
    have hc : ¬(Cond.lt 4 5).Holds x := by simp [Cond.Holds, h4, h5]
    refine ⟨x, Exec.loop_exit hc, hmem, h0, h1, ?_⟩
    rw [h2, outerPrefixXor_full]
  | succ remD ih =>
    intro j x hsum hmem h0 h1 h2 h3 h4 h5 h10 h11
    have hj_lt : j < d := by omega
    have hj_succ : j + 1 ≤ d := by omega
    have hpow_pos : 0 < 2 ^ b := Nat.two_pow_pos b
    have hlt_mul : j * 2 ^ b < d * 2 ^ b := Nat.mul_lt_mul_of_pos_right hj_lt hpow_pos
    have hc : (Cond.lt 4 5).Holds x := by simp [Cond.Holds, h4, h5, hlt_mul]
    have hfit_0 : Fits w 0 := hfit_space.of_le (Nat.zero_le _)
    have hfit_c : Fits w c :=
      hfit_space.of_le (by
        have hd_pos : 1 ≤ d := by omega
        have hb_pos : 1 ≤ 2 ^ b := Nat.one_le_two_pow
        have hc_le : c ≤ (c + 1) * d * 2 ^ b :=
          calc c ≤ c + 1 := Nat.le_succ c
            _ ≤ (c + 1) * d := Nat.le_mul_of_pos_right _ hd_pos
            _ ≤ (c + 1) * d * 2 ^ b := Nat.le_mul_of_pos_right _ hb_pos
        dsimp only [space]
        omega)
    set s1 := x.set 7 u.val
    have e1 : Exec w (.op (.copy 7 1) : Code .exact 12) x s1 1 := by
      simpa [s1, h1] using (Exec.copy (B := .exact) (w := w) (d := 7) (s := 1) (x := x))
    set s2 := s1.set 8 0
    have e2 : Exec w (.op (.const 8 0) : Code .exact 12) s1 s2 1 := Exec.const hfit_0
    set s3 := s2.set 6 c
    have e3 : Exec w (.op (.const 6 c) : Code .exact 12) s2 s3 1 := Exec.const hfit_c
    obtain ⟨s4, e4, hs4_mem, hs4_0, hs4_1, hs4_2, hs4_3, hs4_4, hs4_5, hs4_8, hs4_10, hs4_11⟩ :=
      innerLoop_exec
        (r2 := (outerPrefixXor T₁ T₂ u j (by omega)).val)
        (r4 := base + c * d * 2 ^ b + j * 2 ^ b)
        (r5 := base + c * d * 2 ^ b + d * 2 ^ b)
        htop u ⟨j, hj_lt⟩ hfit_space hfit_pow_b hfit_u c 0 s3 (by omega)
        hmem
        (by simp +decide [s3, s2, s1, h0])
        (by simp +decide [s3, s2, s1, h1])
        (by simp +decide [s3, s2, s1, h2])
        (by simp +decide [s3, s2, s1, h3])
        (by simp +decide [s3, s2, s1, h4])
        (by simp +decide [s3, s2, s1, h5])
        (by simp +decide [s3])
        (by simp +decide [s3, s2, s1])
        (by simp +decide [s3, s2, val_innerPrefixXor_zero])
        (by simp +decide [s3, s2, s1, h10])
        (by simp +decide [s3, s2, s1, h11])
    let yj := simpleTabTuple T₁ (charDigits c b u) ⟨j, hj_lt⟩
    have hbot_lt : botAddr base c d b ⟨j, hj_lt⟩ yj < base + space c d b :=
      botAddr_lt_base_add_space base c d b ⟨j, hj_lt⟩ yj
    have hfit_bot_addr : Fits w (botAddr base c d b ⟨j, hj_lt⟩ yj) :=
      hfit_space.of_le (le_of_lt hbot_lt)
    have hmem_bot : s4.mem (botAddr base c d b ⟨j, hj_lt⟩ yj) = (T₂ ⟨j, hj_lt⟩ yj).val := by
      rw [hs4_mem]
      exact hbot ⟨j, hj_lt⟩ yj
    have hxor_outer := val_outerPrefixXor_succ T₁ T₂ u hj_succ
    have hfit_xor_outer : Fits w ((outerPrefixXor T₁ T₂ u j (by omega)).val ^^^
        (T₂ ⟨j, hj_lt⟩ yj).val) := by
      rw [← hxor_outer]
      exact hfit_pow_M.of_le (le_of_lt (outerPrefixXor T₁ T₂ u (j + 1) hj_succ).isLt)
    have hbot_next_le : base + c * d * 2 ^ b + (j + 1) * 2 ^ b ≤ base + space c d b := by
      dsimp only [space]
      calc base + c * d * 2 ^ b + (j + 1) * 2 ^ b
          ≤ base + c * d * 2 ^ b + d * 2 ^ b :=
            Nat.add_le_add_left (Nat.mul_le_mul_right _ hj_succ) _
        _ = base + (c + 1) * d * 2 ^ b := by ring
    have hfit_bot_next : Fits w (base + c * d * 2 ^ b + (j + 1) * 2 ^ b) :=
      hfit_space.of_le hbot_next_le
    set s5 := s4.set 9 (botAddr base c d b ⟨j, hj_lt⟩ yj)
    have e5 : Exec w (.op (.exactBin .add 9 4 8) : Code .exact 12) s4 s5 1 :=
      exec_exactBin (by simp +decide [hs4_4, hs4_8, botAddr, yj]) hfit_bot_addr
    set s6 := s5.set 9 (T₂ ⟨j, hj_lt⟩ yj).val
    have e6 : Exec w (.op (.load 9 9) : Code .exact 12) s5 s6 1 := by
      simpa +decide [s6, s5, hmem_bot] using
        (Exec.load (B := .exact) (w := w) (d := 9) (a := 9) (x := s5))
    set s7 := s6.set 2 (outerPrefixXor T₁ T₂ u (j + 1) hj_succ).val
    have e7 : Exec w (.op (.exactBin .xor 2 2 9) : Code .exact 12) s6 s7 1 :=
      exec_exactBin (by simp +decide [s6, s5, hs4_2, hxor_outer, yj])
        (by rwa [hxor_outer])
    set s8 := s7.set 4 (base + c * d * 2 ^ b + (j + 1) * 2 ^ b)
    have e8 : Exec w (.op (.exactBin .add 4 4 10) : Code .exact 12) s7 s8 1 :=
      exec_exactBin
        (by
          rw [show base + c * d * 2 ^ b + (j + 1) * 2 ^ b =
            base + c * d * 2 ^ b + j * 2 ^ b + 2 ^ b by ring]
          simp +decide [s7, s6, s5, hs4_4, hs4_10])
        hfit_bot_next
    have hbody := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))
    obtain ⟨y, hrec, hymem, hy0, hy1, hy2⟩ :=
      ih (j + 1) s8 (by omega)
        hs4_mem
        (by simp +decide [s8, s7, s6, s5, hs4_0])
        (by simp +decide [s8, s7, s6, s5, hs4_1])
        (by simp +decide [s8, s7])
        (by simp +decide [s8, s7, s6, s5, hs4_3])
        (by simp +decide [s8])
        (by simp +decide [s8, s7, s6, s5, hs4_5])
        (by simp +decide [s8, s7, s6, s5, hs4_10])
        (by simp +decide [s8, s7, s6, s5, hs4_11])
    refine ⟨y, ?_, hymem, hy0, hy1, hy2⟩
    have hsteps_eq :
        1 + (1 + (1 + ((12 * c + 2) + (1 + (1 + (1 + 1)))))) +
          ((12 * c + 11) * remD + 2) + 2 = (12 * c + 11) * (remD + 1) + 2 := by ring
    simpa only [outerLoop, outerBody, hsteps_eq] using Exec.loop_iter hc hbody hrec

/-- **Exact deterministic `Exec` correctness and complexity of `evalCode c d b`**:
from `SeedRep base c d b M (T₁, T₂) x.mem`, `x.regs 0 = base`, and `x.regs 1 = u.val`,
`evalCode c d b` halts in `evalSteps c d = (12 * c + 11) * d + 10` instructions with
`y.regs 2 = (doubleTabHash c d b U M T₁ T₂ u).val`, preserving `y.regs 0 = base`,
`y.regs 1 = u.val`, and `y.mem = x.mem`. -/
theorem evalCode_exec {w base c d b U M : ℕ}
    {T₁ : DoubleTabTopSeed c d b} {T₂ : DoubleTabBotSeed d b M}
    (u : Fin U) {x : Data 12}
    (hbase : x.regs 0 = base)
    (hkey : x.regs 1 = u.val)
    (hseed : SeedRep base c d b M (T₁, T₂) x.mem)
    (hfit_space : Fits w (base + space c d b))
    (hfit_pow_b : Fits w (2 ^ b))
    (hfit_pow_M : Fits w (2 ^ M))
    (hfit_u : Fits w u.val) :
    ∃ y : Data 12,
      Exec w (evalCode c d b) x y (evalSteps c d) ∧
      y.mem = x.mem ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = (doubleTabHash c d b U M T₁ T₂ u).val := by
  have es := evalSetupCode_exec hbase hfit_space hfit_pow_b
  set x0 := evalSetupData base c d b x
  obtain ⟨y, e_out, hymem, hy0, hy1, hy2⟩ :=
    outerLoop_exec hseed.1 hseed.2 u hfit_space hfit_pow_b hfit_pow_M hfit_u d 0 x0 (by omega)
      rfl
      (by simp +decide [x0, evalSetupData, hbase])
      (by simp +decide [x0, evalSetupData, hkey])
      (by simp +decide [x0, evalSetupData, val_outerPrefixXor_zero])
      (by simp +decide [x0, evalSetupData])
      (by simp +decide [x0, evalSetupData])
      (by simp +decide [x0, evalSetupData])
      (by simp +decide [x0, evalSetupData])
      (by simp +decide [x0, evalSetupData])
  refine ⟨y, ?_, hymem, hy0, hy1, hy2⟩
  simpa only [evalCode, evalSteps,
    show 8 + ((12 * c + 11) * d + 2) = (12 * c + 11) * d + 10 by omega] using es.seq e_out

/-- `ExecWithin` corollary of `evalCode_exec`, also recording `y.Bounded w` when `x.Bounded w`. -/
theorem evalCode_execWithin {w base c d b U M : ℕ}
    {T₁ : DoubleTabTopSeed c d b} {T₂ : DoubleTabBotSeed d b M}
    (u : Fin U) {x : Data 12}
    (hbase : x.regs 0 = base)
    (hkey : x.regs 1 = u.val)
    (hseed : SeedRep base c d b M (T₁, T₂) x.mem)
    (hfit_space : Fits w (base + space c d b))
    (hfit_pow_b : Fits w (2 ^ b))
    (hfit_pow_M : Fits w (2 ^ M))
    (hfit_u : Fits w u.val) :
    ∃ y : Data 12,
      ExecWithin w (evalCode c d b) x y (evalSteps c d) ∧
      y.mem = x.mem ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = (doubleTabHash c d b U M T₁ T₂ u).val ∧
      (x.Bounded w → y.Bounded w) := by
  obtain ⟨y, hex, hymem, hy0, hy1, hy2⟩ :=
    evalCode_exec u hbase hkey hseed hfit_space hfit_pow_b hfit_pow_M hfit_u
  exact ⟨y, hex.within, hymem, hy0, hy1, hy2, fun hx => hex.bounded hx⟩

/-! ## Section 4: `Impl` and `ObliviousSequenceImpl` certificates for Double Tabulation -/

/-- Package Double Tabulation on `Data 12` into a `Cslib.DataStructure.HashFamily.WordRAM.Impl`
over `Basis.exact` with `0` initialization parameters. -/
@[expose] noncomputable def impl {w base c d b U M : ℕ}
    (hfit_space : Fits w (base + space c d b))
    (hfit_pow_b : Fits w (2 ^ b))
    (hfit_pow_M : Fits w (2 ^ M))
    (hfit_keys : ∀ u : Fin U, Fits w u.val) :
    Impl .exact 12 0 w base U (2 ^ M) Fin.elim0 where
  Seed := DoubleTabTopSeed c d b × DoubleTabBotSeed d b M
  eval θ u := doubleTabHash c d b U M θ.1 θ.2 u
  space := space c d b
  tableRep _ := True
  seedRep := SeedRep base c d b M
  baseReg := 0
  keyReg := 1
  outReg := 2
  initParams := Fin.elim0
  key_ne_base := by decide
  params_ne_base j := Fin.elim0 j
  fits_space := hfit_space
  fits_tag := hfit_pow_b.of_le Nat.one_le_two_pow
  fits_key := hfit_keys
  addReg := Op.exactBin .add
  addReg_eval _ _ _ hfit := Data.put_of_fits hfit
  initTableCode := .op (.copy 0 0)
  initTableSteps := 1
  resampleCode := resampleCode c d b M
  resampleSteps := resampleSteps c d b
  evalCode := evalCode c d b
  evalSteps := evalSteps c d
  initTable_exec {x} _ hbase _ _ := by
    refine ⟨x.set 0 (x.regs 0),
      (Exec.copy (B := .exact) (w := w) (d := 0) (s := 0) (x := x)).within,
      by simp [hbase], trivial, Modifies.refl _ _⟩
  resample_exec {x} _ hbase _ := by
    have hfit_mask_b : Fits w (2 ^ b - 1) := hfit_pow_b.of_le (Nat.pred_le _)
    have hfit_mask_M : Fits w (2 ^ M - 1) := hfit_pow_M.of_le (Nat.pred_le _)
    have hfit_1 : Fits w 1 := hfit_pow_b.of_le Nat.one_le_two_pow
    refine Impl.resample_exec_of_execRand
      (base := base) (space := space c d b) (baseReg := 0)
      (tableRep := fun _ => True) (seedRep := SeedRep base c d b M)
      (resampleSteps := resampleSteps c d b)
      (extractSeed base c d b M)
      (resampleCode_execRand hbase hfit_space hfit_mask_b hfit_mask_M hfit_1)
      (map_extractSeed_eval_resampleComp base c d b M x) ?_
    intro z hz
    obtain ⟨hz0, hseed, hframe, hsteps⟩ := mem_support_resampleComp hbase hz
    refine ⟨hz0, trivial, hseed, ?_, le_of_eq hsteps⟩
    intro a ha
    rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
    exact hframe a ha
  eval_exec θ u {x} _ hbase hkey _ hseed := by
    obtain ⟨y, hex, hymem, hy0, _, hy2, _⟩ :=
      evalCode_execWithin u hbase hkey hseed hfit_space hfit_pow_b hfit_pow_M (hfit_keys u)
    exact ⟨y, hex, hymem, hy0, hy2⟩

/-- Lift `impl` to `Basis.standard`. -/
@[expose] noncomputable def implStandard {w base c d b U M : ℕ}
    (hfit_space : Fits w (base + space c d b))
    (hfit_pow_b : Fits w (2 ^ b))
    (hfit_pow_M : Fits w (2 ^ M))
    (hfit_keys : ∀ u : Fin U, Fits w u.val) :
    Impl .standard 12 0 w base U (2 ^ M) Fin.elim0 :=
  (impl hfit_space hfit_pow_b hfit_pow_M hfit_keys).toStandard

/-- Finset of `k`-unique top-level tables `T₁ : DoubleTabTopSeed c d b`. -/
@[expose] def doubleTabGoodTop (c d b k : ℕ) : Finset (DoubleTabTopSeed c d b) :=
  Finset.univ.filter fun T₁ => IsKUnique k (simpleTabTuple T₁)

/-- Top-seed failure probability
`#{T₁ | ¬ IsKUnique k (simpleTabTuple T₁)} / |DoubleTabTopSeed c d b|` for `doubleTabHash`. -/
@[expose] noncomputable def doubleTabFailureProb (c d b k : ℕ) : ℝ≥0∞ :=
  (((Finset.univ \ doubleTabGoodTop c d b k).card : ℝ≥0∞) /
    (Fintype.card (DoubleTabTopSeed c d b) : ℝ≥0∞))

theorem sdiff_doubleTabGoodTop (c d b k : ℕ) :
    Finset.univ \ doubleTabGoodTop c d b k =
      Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => ¬ IsKUnique k (simpleTabTuple T₁) := by
  ext T₁
  simp [doubleTabGoodTop]

/-- **Explicit failure-probability bound for `doubleTabFailureProb c (8 * c) b k`
(`[Thorup2013]`, Theorem 1(a), p. 4)**:
when `1 ≤ c` and `2 * doubleTabCodeBound c (8 * c) 4 k ≤ 2 ^ (3 * b)`,
`doubleTabFailureProb c (8 * c) b k ≤ 2 * (doubleTabCodeBound c (8 * c) 4 k) ^ 2 / 2 ^ (6 * b)`. -/
theorem doubleTabFailureProb_eight_mul_le {c b k : ℕ} (hc : 1 ≤ c)
    (hbound : 2 * doubleTabCodeBound c (8 * c) 4 k ≤ 2 ^ (3 * b)) :
    doubleTabFailureProb c (8 * c) b k ≤
      ((2 * (doubleTabCodeBound c (8 * c) 4 k) ^ 2 : ℕ) : ℝ≥0∞) /
        ((2 ^ (6 * b) : ℕ) : ℝ≥0∞) := by
  dsimp only [doubleTabFailureProb]
  rw [sdiff_doubleTabGoodTop]
  have hcard := card_not_isKUnique_eight_mul_le hc hbound
  have hcast : ((2 ^ (6 * b) : ℕ) : ℝ≥0∞) *
      (((Finset.univ.filter fun T₁ : DoubleTabTopSeed c (8 * c) b =>
        ¬ IsKUnique k (simpleTabTuple T₁)).card : ℕ) : ℝ≥0∞) ≤
      ((2 * (doubleTabCodeBound c (8 * c) 4 k) ^ 2 : ℕ) : ℝ≥0∞) *
        (Fintype.card (DoubleTabTopSeed c (8 * c) b) : ℝ≥0∞) := by
    exact_mod_cast hcard
  have hN_ne_zero : (Fintype.card (DoubleTabTopSeed c (8 * c) b) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hN_ne_top : (Fintype.card (DoubleTabTopSeed c (8 * c) b) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hW_ne_zero : ((2 ^ (6 * b) : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos (6 * b)))
  have hW_ne_top : ((2 ^ (6 * b) : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [ENNReal.div_le_iff_le_mul (Or.inl hN_ne_zero) (Or.inl hN_ne_top),
    div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl hW_ne_zero) (Or.inl hW_ne_top),
    mul_comm]
  exact hcast

/-- Canonical `ObliviousSequenceImpl` certificate for `impl` realizing
`DataStructure.HashFamily.whpKWiseSpec k U (2 ^ M) (doubleTabFailureProb c d b k)` when
`U ≤ 2 ^ (c * b)`. -/
@[expose] noncomputable def obliviousSequenceImpl {w base c d b U M k : ℕ}
    (hU : U ≤ 2 ^ (c * b))
    (hfit_space : Fits w (base + space c d b))
    (hfit_pow_b : Fits w (2 ^ b))
    (hfit_pow_M : Fits w (2 ^ M))
    (hfit_keys : ∀ u : Fin U, Fits w u.val) :
    ObliviousSequenceImpl
      (impl hfit_space hfit_pow_b hfit_pow_M hfit_keys).subroutineCode
      (HashFamily.whpKWiseSpec k U (2 ^ M) (doubleTabFailureProb c d b k))
      w base Fin.elim0 :=
  (impl hfit_space hfit_pow_b hfit_pow_M hfit_keys).toWhpKWiseObliviousSequenceImpl
    (Equiv.refl _)
    (doubleTabGoodTop c d b k)
    (fun _ hT₁ =>
      isKWiseIndependentHash_doubleTabHash_of_isKUnique hU (Finset.mem_filter.mp hT₁).2)

/-- Standard-basis lifting of `obliviousSequenceImpl`. -/
@[expose] noncomputable def obliviousSequenceImplStandard {w base c d b U M k : ℕ}
    (hU : U ≤ 2 ^ (c * b))
    (hfit_space : Fits w (base + space c d b))
    (hfit_pow_b : Fits w (2 ^ b))
    (hfit_pow_M : Fits w (2 ^ M))
    (hfit_keys : ∀ u : Fin U, Fits w u.val) :
    ObliviousSequenceImpl
      (impl hfit_space hfit_pow_b hfit_pow_M hfit_keys).subroutineCode.toStandard
      (HashFamily.whpKWiseSpec k U (2 ^ M) (doubleTabFailureProb c d b k))
      w base Fin.elim0 :=
  (obliviousSequenceImpl hU hfit_space hfit_pow_b hfit_pow_M hfit_keys).toStandard

/-! ## Section 5: All-`n_max` regime-switched `provableImpl` and
`provableObliviousSequenceImpl` -/

/-- Number of characters `c = 2 * max c_exp 1` for polynomial universe `U ≤ max n_max 4 ^ c_exp`. -/
abbrev provableC (c_exp : ℕ) : ℕ :=
  2 * max c_exp 1

/-- Intermediate tuple length `d = 8 * provableC c_exp = 16 * max c_exp 1` (`q = 4`). -/
abbrev provableD (c_exp : ℕ) : ℕ :=
  8 * provableC c_exp

/-- Character bit-width `b = (1 + Nat.clog 2 (max n_max 4)) / 2` at capacity `n_max`. -/
abbrev provableB (n_max : ℕ) : ℕ :=
  (1 + Nat.clog 2 (max n_max 4)) / 2

theorem one_le_provableC (c_exp : ℕ) : 1 ≤ provableC c_exp := by
  dsimp only [provableC]
  omega

theorem one_le_provableB (n_max : ℕ) : 1 ≤ provableB n_max := by
  dsimp only [provableB]
  have h2 : 2 = Nat.clog 2 4 := by decide
  have hclog : 2 ≤ Nat.clog 2 (max n_max 4) := by
    rw [h2]
    exact Nat.clog_mono_right 2 (le_max_right n_max 4)
  omega

/-- `2 ^ provableB n_max ≤ 4 * max n_max 4` for every `n_max : ℕ`. -/
theorem two_pow_provableB_le (n_max : ℕ) : 2 ^ provableB n_max ≤ 4 * max n_max 4 := by
  have hb_le : provableB n_max ≤ Nat.log 2 (max n_max 4) + 2 := by
    dsimp only [provableB]
    have hclog : Nat.clog 2 (max n_max 4) ≤ Nat.log 2 (max n_max 4) + 1 :=
      Nat.clog_le_of_le_pow (le_of_lt (Nat.lt_pow_succ_log_self (by decide) _))
    omega
  calc 2 ^ provableB n_max
      ≤ 2 ^ (Nat.log 2 (max n_max 4) + 2) := Nat.pow_le_pow_right (by decide) hb_le
    _ = 4 * 2 ^ Nat.log 2 (max n_max 4) := by ring
    _ ≤ 4 * max n_max 4 := Nat.mul_le_mul_left 4 (Nat.pow_log_le_self 2 (by omega))

/-- Whenever `U ≤ max n_max 4 ^ c_exp`, `U ≤ 2 ^ (provableC c_exp * provableB n_max)`. -/
theorem le_two_pow_provableC_mul_provableB {c_exp n_max U : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp) :
    U ≤ 2 ^ (provableC c_exp * provableB n_max) := by
  have hclog_le : Nat.clog 2 (max n_max 4) ≤ 2 * provableB n_max := by
    dsimp only [provableB]
    omega
  have hn_le : max n_max 4 ≤ 2 ^ (2 * provableB n_max) :=
    (Nat.le_pow_clog (by decide) (max n_max 4)).trans (Nat.pow_le_pow_right (by decide) hclog_le)
  calc U ≤ max n_max 4 ^ c_exp := hU
    _ ≤ max n_max 4 ^ max c_exp 1 :=
      Nat.pow_le_pow_right (by omega) (le_max_left c_exp 1)
    _ ≤ (2 ^ (2 * provableB n_max)) ^ max c_exp 1 :=
      Nat.pow_le_pow_left hn_le (max c_exp 1)
    _ = 2 ^ (provableC c_exp * provableB n_max) := by
      rw [← Nat.pow_mul]
      congr 1
      dsimp only [provableC]
      ring

/-- Package `KWise` (`Complexity/Algorithms/WordRAM/Hashing/KWise.lean`) into an `Impl` on
`Data 18` with `3` initialization parameters `![n_max, U, M]`. -/
@[expose] noncomputable def kWiseImpl {w base n_max U M k : ℕ}
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + KWise.space n_max k))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    Impl .exact 18 3 w base U (2 ^ M) ![n_max, U, M] where
  Seed := Fin k → Fin (2 ^ trinomialDeg U M)
  eval := trinomialPolyHash (trinomialStep U M) k U M
  space := KWise.space n_max k
  tableRep := KWise.TableRep base (KWise.chunkBits n_max) U M k
  seedRep := KWise.SeedRep base U M k
  baseReg := 0
  keyReg := 1
  outReg := 2
  initParams := ![1, 2, 3]
  key_ne_base := by decide
  params_ne_base j := by fin_cases j <;> decide
  fits_space := hfit_space
  fits_tag := hfit_U.of_le (by omega)
  fits_key u := hfit_U.of_le (by have := u.isLt; omega)
  addReg := Op.exactBin .add
  addReg_eval _ _ _ hfit := Data.put_of_fits hfit
  initTableCode := KWise.initTableCode k
  initTableSteps := KWise.initTableSteps n_max U M
  resampleCode := KWise.resampleCode k
  resampleSteps := 5 * k + 10
  evalCode := KWise.evalCode k
  evalSteps := KWise.evalSteps n_max U M k
  initTable_exec {x} _ hbase hpar _ := by
    have hq_pos : 0 < trinomialDeg U M := by
      dsimp only [trinomialDeg]
      positivity
    have hfit_q : Fits w (2 ^ trinomialDeg U M) :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    obtain ⟨y, hex, htab, hy0, hmod⟩ :=
      KWise.initTableCode_execWithin hbase (hpar 0) (hpar 1) (hpar 2)
        hfit_space hfit_n hfit_U hfit_q
    refine ⟨y, hex, hy0, htab, ?_⟩
    intro a ha
    rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
    exact hmod a ha
  resample_exec {x} _ hbase htab := by
    have hq_pos : 0 < trinomialDeg U M := by
      dsimp only [trinomialDeg]
      positivity
    have hfit_q : Fits w (2 ^ trinomialDeg U M) :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    have hpow : 0 < 2 ^ (2 * KWise.chunkBits n_max) := by positivity
    have hfit_end : Fits w (base + 8 + k) :=
      hfit_space.of_le (by
        change base + 8 + k ≤ base + (8 + k + 2 ^ (2 * KWise.chunkBits n_max))
        omega)
    refine Impl.resample_exec_of_execRand
      (fun m => KWise.extractSeeds base U M k m)
      (KWise.resampleCode_execRand htab hbase hfit_end hfit_q)
      (KWise.map_extractSeeds_eval_resampleComp base U M k x) ?_
    intro z hz
    obtain ⟨⟨⟨htab', hseed'⟩, hz0, hout⟩, hsteps⟩ :=
      KWise.mem_support_resampleComp htab hbase hz
    refine ⟨hz0, htab', hseed', ?_, hsteps⟩
    intro a ha
    rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
    dsimp only [KWise.space, KWise.spaceFromB] at ha
    exact hout a (by omega)
  eval_exec θ u {x} _ hbase hkey htab hseed := by
    obtain ⟨y, hex, hy0, _, hy2, hymem⟩ :=
      KWise.evalCode_execWithin u ⟨htab, hseed⟩ hbase hkey hw hfit_space
    exact ⟨y, hex, hymem, hy0, hy2⟩

/-- Register embedding `Fin 12 → Fin 18` via `Fin.castLE`. -/
@[expose] def cast12To18 : Fin 12 → Fin 18 :=
  Fin.castLE (by decide)

theorem injective_cast12To18 : Function.Injective cast12To18 :=
  Fin.castLE_injective _

/-- Lift `impl` from `Data 12` to `Data 18` with `3` initialization parameters `params` so it
shares the exact register signature of `kWiseImpl`. -/
@[expose] noncomputable def impl18 {w base c d b U M : ℕ}
    (params : Fin 3 → ℕ)
    (hfit_space : Fits w (base + space c d b))
    (hfit_pow_b : Fits w (2 ^ b))
    (hfit_pow_M : Fits w (2 ^ M))
    (hfit_keys : ∀ u : Fin U, Fits w u.val) :
    Impl .exact 18 3 w base U (2 ^ M) params where
  Seed := DoubleTabTopSeed c d b × DoubleTabBotSeed d b M
  eval θ u := doubleTabHash c d b U M θ.1 θ.2 u
  space := space c d b
  tableRep _ := True
  seedRep := SeedRep base c d b M
  baseReg := 0
  keyReg := 1
  outReg := 2
  initParams := ![1, 2, 3]
  key_ne_base := by decide
  params_ne_base j := by fin_cases j <;> decide
  fits_space := hfit_space
  fits_tag := hfit_pow_b.of_le Nat.one_le_two_pow
  fits_key := hfit_keys
  addReg := Op.exactBin .add
  addReg_eval _ _ _ hfit := Data.put_of_fits hfit
  initTableCode := .op (.copy 0 0)
  initTableSteps := 1
  resampleCode := (resampleCode c d b M).rename cast12To18
  resampleSteps := resampleSteps c d b
  evalCode := (evalCode c d b).rename cast12To18
  evalSteps := evalSteps c d
  initTable_exec {x} _ hbase _ _ := by
    refine ⟨x.set 0 (x.regs 0),
      (Exec.copy (B := .exact) (w := w) (d := 0) (s := 0) (x := x)).within,
      by simp [hbase], trivial, Modifies.refl _ _⟩
  resample_exec {x} _ hbase _ := by
    have hfit_mask_b : Fits w (2 ^ b - 1) := hfit_pow_b.of_le (Nat.pred_le _)
    have hfit_mask_M : Fits w (2 ^ M - 1) := hfit_pow_M.of_le (Nat.pred_le _)
    have hfit_1 : Fits w 1 := hfit_pow_b.of_le Nat.one_le_two_pow
    have hbase12 : (x.comap cast12To18).regs 0 = base := hbase
    have hex18 := (resampleCode_execRand hbase12 hfit_space hfit_mask_b hfit_mask_M hfit_1).rename
      injective_cast12To18
    have hunif18 :
        (((fun z : Data 12 × ℕ => (z.1.extend cast12To18 x, z.2)) <$>
            resampleComp base c d b M (x.comap cast12To18)).eval).map
          (fun z => extractSeed base c d b M z.1.mem) =
        PMF.uniformOfFintype (DoubleTabTopSeed c d b × DoubleTabBotSeed d b M) := by
      rw [ProbComp.eval_map, PMF.map_comp]
      exact map_extractSeed_eval_resampleComp base c d b M (x.comap cast12To18)
    refine Impl.resample_exec_of_execRand
      (base := base) (space := space c d b) (baseReg := 0)
      (tableRep := fun _ => True) (seedRep := SeedRep base c d b M)
      (resampleSteps := resampleSteps c d b)
      (extractSeed base c d b M) hex18 hunif18 ?_
    intro z hz
    obtain ⟨z12, hz12, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    obtain ⟨hz0, hseed, hframe, hsteps⟩ := mem_support_resampleComp hbase12 hz12
    have hreg0 : (z12.1.extend cast12To18 x).regs 0 = base := by
      change ((z12.1.extend cast12To18 x).comap cast12To18).regs 0 = base
      rw [Data.comap_extend injective_cast12To18]
      exact hz0
    refine ⟨hreg0, trivial, hseed, ?_, le_of_eq hsteps⟩
    intro a ha
    rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
    exact hframe a ha
  eval_exec θ u {x} _ hbase hkey _ hseed := by
    obtain ⟨y12, he12, hymem, hy0, _, hy2, _⟩ :=
      evalCode_execWithin u (x := x.comap cast12To18) hbase hkey hseed
        hfit_space hfit_pow_b hfit_pow_M (hfit_keys u)
    refine ⟨y12.extend cast12To18 x, he12.rename injective_cast12To18, hymem, ?_, ?_⟩
    · change ((y12.extend cast12To18 x).comap cast12To18).regs 0 = base
      rw [Data.comap_extend injective_cast12To18]
      exact hy0
    · change ((y12.extend cast12To18 x).comap cast12To18).regs 2 =
        (doubleTabHash c d b U M θ.1 θ.2 u).val
      rw [Data.comap_extend injective_cast12To18]
      exact hy2

/-- Footprint size of `provableImpl c_exp k n_max U M`:
`KWise.space n_max k` when `n_max < doubleTabThreshold c_exp`, and
`space (provableC c_exp) (provableD c_exp) (provableB n_max)` otherwise. -/
@[expose] def provableSpace (c_exp k n_max : ℕ) : ℕ :=
  if n_max < doubleTabThreshold c_exp then
    KWise.space n_max k
  else
    space (provableC c_exp) (provableD c_exp) (provableB n_max)

/-- Failure probability `δ` of `provableObliviousSequenceImpl c_exp k n_max U M`:
`0` (`(((Finset.univ \ {()}).card : ℝ≥0∞) / Fintype.card Unit)`) when
`n_max < doubleTabThreshold c_exp`, and
`doubleTabFailureProb (provableC c_exp) (provableD c_exp) (provableB n_max) k` otherwise. -/
@[expose] noncomputable def provableFailureProb (c_exp k n_max : ℕ) : ℝ≥0∞ :=
  if n_max < doubleTabThreshold c_exp then
    (((Finset.univ \ ({()} : Finset Unit)).card : ℝ≥0∞) /
      (Fintype.card Unit : ℝ≥0∞))
  else
    doubleTabFailureProb (provableC c_exp) (provableD c_exp) (provableB n_max) k

theorem provableFailureProb_eq_zero_of_lt {c_exp k n_max : ℕ}
    (hlt : n_max < doubleTabThreshold c_exp) :
    provableFailureProb c_exp k n_max = 0 := by
  simp [provableFailureProb, hlt]

theorem provableFailureProb_eq_of_ge {c_exp k n_max : ℕ}
    (hge : doubleTabThreshold c_exp ≤ n_max) :
    provableFailureProb c_exp k n_max =
      doubleTabFailureProb (provableC c_exp) (provableD c_exp) (provableB n_max) k := by
  have hnot : ¬(n_max < doubleTabThreshold c_exp) := not_lt.mpr hge
  simp [provableFailureProb, hnot]

/-- **All-`n_max` regime-switched `Impl` (`provableImpl`)**:
uses `kWiseImpl` for `n_max < doubleTabThreshold c_exp` and `impl18`
with `c = provableC c_exp`, `d = provableD c_exp`, `b = provableB n_max` for
`doubleTabThreshold c_exp ≤ n_max`. -/
@[expose] noncomputable def provableImpl (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    Impl .exact 18 3 w base U (2 ^ M) ![n_max, U, M] :=
  if h : n_max < doubleTabThreshold c_exp then
    kWiseImpl (k := k) hw (by simpa only [provableSpace, h, ↓reduceIte] using hfit_space)
      hfit_n hfit_U
  else
    have hsp : Fits w (base + space (provableC c_exp) (provableD c_exp) (provableB n_max)) := by
      simpa only [provableSpace, h, ↓reduceIte] using hfit_space
    have hpow_b : Fits w (2 ^ provableB n_max) :=
      hsp.of_le (by
        have hc : 1 ≤ provableC c_exp := one_le_provableC c_exp
        have hd : 1 ≤ provableD c_exp := by dsimp only [provableD]; omega
        have hle : 1 * 2 ^ provableB n_max ≤
            ((provableC c_exp + 1) * provableD c_exp) * 2 ^ provableB n_max :=
          Nat.mul_le_mul_right _ (by nlinarith)
        dsimp only [space]
        omega)
    have hpow_M : Fits w (2 ^ M) := by
      have hM_le : M ≤ trinomialDeg U M := le_trinomialDeg U M
      have hdeg_pos : 0 < trinomialDeg U M := by
        dsimp only [trinomialDeg]; positivity
      exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    have hkeys : ∀ u : Fin U, Fits w u.val :=
      fun u => hfit_U.of_le (by have := u.isLt; omega)
    impl18 ![n_max, U, M] hsp hpow_b hpow_M hkeys

/-- Standard-basis lifting of `provableImpl`. -/
@[expose] noncomputable def provableImplStandard (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    Impl .standard 18 3 w base U (2 ^ M) ![n_max, U, M] :=
  (provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U).toStandard

@[simp]
theorem provableImpl_space (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    (provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U).space =
      provableSpace c_exp k n_max := by
  dsimp only [provableImpl, provableSpace]
  split_ifs <;> rfl

@[simp]
theorem provableImpl_subroutineCode_initParams (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    (provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U).subroutineCode.initParams =
      fun j => coreReg (![1, 2, 3] j) := by
  dsimp only [provableImpl]
  split_ifs <;> rfl

@[simp]
theorem provableImpl_subroutineCode_frontierReg (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    (provableImpl c_exp k n_max U M
      hw hfit_space hfit_n hfit_U).subroutineCode.frontierReg =
      frontierReg 18 := by
  dsimp only [provableImpl]
  split_ifs <;> rfl

/-- **All-`n_max` regime-switched `ObliviousSequenceImpl` (`provableObliviousSequenceImpl`)**
realizing `DataStructure.HashFamily.whpKWiseSpec k U (2 ^ M) (provableFailureProb c_exp k n_max)`
whenever `U ≤ max n_max 4 ^ c_exp`. -/
@[expose] noncomputable def provableObliviousSequenceImpl (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    ObliviousSequenceImpl
      (provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U).subroutineCode
      (HashFamily.whpKWiseSpec k U (2 ^ M) (provableFailureProb c_exp k n_max))
      w base ![n_max, U, M] := by
  dsimp only [provableImpl, provableFailureProb]
  split_ifs with h
  · letI : DecidableEq (Fin k → Fin (2 ^ trinomialDeg U M)) := inferInstance
    have hsp : Fits w (base + KWise.space n_max k) := by
      simpa only [provableSpace, h, ↓reduceIte] using hfit_space
    exact (kWiseImpl (k := k) hw hsp hfit_n hfit_U).toWhpKWiseObliviousSequenceImpl
      (Equiv.punitProd (Fin k → Fin (2 ^ trinomialDeg U M))).symm
      ({()} : Finset Unit)
      (fun _ _ =>
        isKWiseIndependentHash_trinomialPolyHash
          (le_two_pow_trinomialDeg U M) (le_trinomialDeg U M))
  · exact (impl18 ![n_max, U, M] _ _ _ _).toWhpKWiseObliviousSequenceImpl
      (Equiv.refl _)
      (doubleTabGoodTop (provableC c_exp) (provableD c_exp) (provableB n_max) k)
      (fun _ hT₁ =>
        isKWiseIndependentHash_doubleTabHash_of_isKUnique
          (le_two_pow_provableC_mul_provableB hU)
          (Finset.mem_filter.mp hT₁).2)

/-- Standard-basis lifting of `provableObliviousSequenceImpl`. -/
@[expose] noncomputable def provableObliviousSequenceImplStandard
    (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    ObliviousSequenceImpl
      (provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U).subroutineCode.toStandard
      (HashFamily.whpKWiseSpec k U (2 ^ M) (provableFailureProb c_exp k n_max))
      w base ![n_max, U, M] :=
  (provableObliviousSequenceImpl c_exp k n_max U M hU hw hfit_space hfit_n hfit_U).toStandard

/-- Explicit `O_{c_exp, k}(1)` space factor `16 + k + 16 * (provableC c_exp + 1) * provableD c_exp`
bounding `provableSpace c_exp k n_max` by `provableSpaceFactor c_exp k * (n_max + 1)` across every
`n_max : ℕ`. -/
@[expose] def provableSpaceFactor (c_exp k : ℕ) : ℕ :=
  16 + k + 16 * (provableC c_exp + 1) * provableD c_exp

/-- **All-`n_max` linear space bound for `provableSpace` (`O_{c_exp, k}(n_max + 1)`)**:
for every `c_exp, k, n_max : ℕ`,
`provableSpace c_exp k n_max ≤ provableSpaceFactor c_exp k * (n_max + 1)`. -/
theorem provableSpace_le (c_exp k n_max : ℕ) :
    provableSpace c_exp k n_max ≤ provableSpaceFactor c_exp k * (n_max + 1) := by
  have hn4 : max n_max 4 ≤ 4 * (n_max + 1) := by omega
  dsimp only [provableSpace, provableSpaceFactor]
  split_ifs
  · dsimp only [KWise.space, KWise.spaceFromB]
    have hpow : 2 ^ (2 * KWise.chunkBits n_max) ≤ 4 * (n_max + 1) := by
      have hlog_ge : 1 ≤ Nat.log 2 (max n_max 2) :=
        Nat.le_log_of_pow_le (by decide) (by omega)
      have hle : 2 * KWise.chunkBits n_max ≤ Nat.log 2 (max n_max 2) + 1 := by
        dsimp only [KWise.chunkBits]
        omega
      calc 2 ^ (2 * KWise.chunkBits n_max)
          ≤ 2 ^ (Nat.log 2 (max n_max 2) + 1) := Nat.pow_le_pow_right (by decide) hle
        _ = 2 * 2 ^ Nat.log 2 (max n_max 2) := by ring
        _ ≤ 2 * max n_max 2 := Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
        _ ≤ 4 * (n_max + 1) := by omega
    have hk : k ≤ k * (n_max + 1) := Nat.le_mul_of_pos_right k (by omega)
    calc 8 + k + 2 ^ (2 * KWise.chunkBits n_max)
        ≤ 8 * (n_max + 1) + k * (n_max + 1) + 4 * (n_max + 1) := by omega
      _ = (12 + k) * (n_max + 1) := by ring
      _ ≤ (16 + k + 16 * (provableC c_exp + 1) * provableD c_exp) * (n_max + 1) :=
          Nat.mul_le_mul_right _ (by omega)
  · dsimp only [space]
    have hpow := two_pow_provableB_le n_max
    have hpow' : 2 ^ provableB n_max ≤ 16 * (n_max + 1) := by omega
    calc (provableC c_exp + 1) * provableD c_exp * 2 ^ provableB n_max
        ≤ (provableC c_exp + 1) * provableD c_exp * (16 * (n_max + 1)) :=
          Nat.mul_le_mul_left _ hpow'
      _ = 16 * (provableC c_exp + 1) * provableD c_exp * (n_max + 1) := by ring
      _ ≤ (16 + k + 16 * (provableC c_exp + 1) * provableD c_exp) * (n_max + 1) :=
          Nat.mul_le_mul_right _ (by omega)

/-- Uniform `O(c_exp)` upper bound `21 * max c_exp 1 + 16` on `KWise.limbCount n_max U M` when
`U ≤ max n_max 4 ^ c_exp` and `M ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5`. -/
@[expose] def provableLimbBound (c_exp : ℕ) : ℕ :=
  21 * max c_exp 1 + 16

theorem limbCount_le_provableLimbBound {c_exp n_max U M : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hM : M ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5) :
    KWise.limbCount n_max U M ≤ provableLimbBound c_exp := by
  have hmaxU : max U 2 ≤ (2 ^ Nat.clog 2 (max n_max 4)) ^ max c_exp 1 := by
    have h2 : 2 ≤ max n_max 4 ^ max c_exp 1 :=
      calc 2 ≤ 4 ^ 1 := by decide
        _ ≤ max n_max 4 ^ 1 := by
          rw [Nat.pow_one, Nat.pow_one]
          exact le_max_right n_max 4
        _ ≤ max n_max 4 ^ max c_exp 1 :=
          Nat.pow_le_pow_right (by omega) (le_max_right c_exp 1)
    have hU' : U ≤ max n_max 4 ^ max c_exp 1 :=
      hU.trans (Nat.pow_le_pow_right (by omega) (le_max_left c_exp 1))
    exact (max_le hU' h2).trans
      (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _)
  have hclogU : Nat.clog 2 (max U 2) ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) := by
    rw [← Nat.pow_mul, Nat.mul_comm] at hmaxU
    exact Nat.clog_le_of_le_pow hmaxU
  have htb : trinomialTargetBits U M ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5 := by
    dsimp only [trinomialTargetBits]
    omega
  have hdeg : trinomialDeg U M ≤ 3 * (max c_exp 1 * Nat.clog 2 (max n_max 4)) + 15 := by
    have h3 := trinomialDeg_le_three_mul U M
    omega
  have hclog_chunk : Nat.clog 2 (max n_max 4) ≤ 7 * KWise.chunkBits n_max := by
    have hn4 : max n_max 4 ≤ 2 ^ (Nat.log 2 (max n_max 2) + 2) := by
      have hlt := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (max n_max 2)
      have h2 : max n_max 4 ≤ 2 * max n_max 2 := by omega
      have hpow : 2 ^ (Nat.log 2 (max n_max 2) + 2) = 2 * 2 ^ (Nat.log 2 (max n_max 2) + 1) := by
        ring
      omega
    have hclog_le := Nat.clog_le_of_le_pow hn4
    dsimp only [KWise.chunkBits]
    omega
  have hdeg_chunk : trinomialDeg U M ≤
      (21 * max c_exp 1 + 15) * KWise.chunkBits n_max := by
    calc trinomialDeg U M
        ≤ 3 * (max c_exp 1 * Nat.clog 2 (max n_max 4)) + 15 := hdeg
      _ ≤ 3 * (max c_exp 1 * (7 * KWise.chunkBits n_max)) + 15 * KWise.chunkBits n_max := by
          have hb_pos : 1 ≤ KWise.chunkBits n_max := KWise.chunkBits_pos n_max
          have hmul := Nat.mul_le_mul_left (max c_exp 1) hclog_chunk
          omega
      _ = (21 * max c_exp 1 + 15) * KWise.chunkBits n_max := by ring
  dsimp only [KWise.limbCount, KWise.limbCountFromB, provableLimbBound]
  have hb_pos : 0 < KWise.chunkBits n_max := KWise.chunkBits_pos n_max
  rw [Nat.div_le_iff_le_mul_add_pred hb_pos]
  have hrew : KWise.chunkBits n_max * (21 * max c_exp 1 + 16) =
      (21 * max c_exp 1 + 15) * KWise.chunkBits n_max + KWise.chunkBits n_max := by ring
  omega

/-- Uniform `O_{c_exp, k}(1)` evaluation instruction bound across all `n_max : ℕ`. -/
@[expose] def provableEvalBound (c_exp k : ℕ) : ℕ :=
  let L := provableLimbBound c_exp
  max (((11 * L + 12) * L + 30) * k + 19)
      (evalSteps (provableC c_exp) (provableD c_exp))

/-- **All-`n_max` constant evaluation time bound for `provableImpl` (`O_{c_exp, k}(1)`)**:
whenever `U ≤ max n_max 4 ^ c_exp` and `M ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5`,
`(provableImpl ...).evalSteps ≤ provableEvalBound c_exp k`, completely independent of
`n_max`, `U`, and `M`. -/
theorem provableImpl_evalSteps_le {c_exp k n_max U M w base : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hM : M ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5)
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    (provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U).evalSteps ≤
      provableEvalBound c_exp k := by
  dsimp only [provableImpl, provableEvalBound]
  split_ifs with h
  · refine le_trans ?_ (le_max_left _ _)
    dsimp only [kWiseImpl, KWise.evalSteps, KWise.evalStepsFromB]
    have hL : KWise.limbCountFromB (KWise.chunkBits n_max) (trinomialDeg U M) ≤
        provableLimbBound c_exp := limbCount_le_provableLimbBound hU hM
    gcongr
  · exact le_max_right _ _

end Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation

end
