/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactLog
public import Complexity.Computability.WordRAM.Randomized.Structured
public import Complexity.Probability.PairwiseIndependentHash.Shift
public import Complexity.Probability.Product
public import Complexity.Probability.Uniform
public import Mathlib.Data.Nat.Log

/-!
# Self-contained Word-RAM random tables and tabulated odd-stride generation

This file provides two self-contained Word-RAM hashing primitives over `Cslib.WordRAM.Basis.exact`,
built on a shared uniform word-slice sampler (`randFillLoop`):

1. **`RandomTable`**: `resampleCode` populates an array `Z[0 .. 2 ^ M - 1]` of `m = 2 ^ M`
   independent uniform `M`-bit words in `5 * 2 ^ M + 7` instructions and `2 ^ M` calls to
   `Code.rand`, inducing `PMF.uniformOfFintype (Fin (2 ^ M) → Fin (2 ^ M))`. `lookupCode` reads
   `Z[idx]` in `2` deterministic instructions, and `xorLookupCode` evaluates the XOR-shifted hash
   `f(u) ^^^ Z[g(u)]` in `3` deterministic instructions [Carter and Wegman][CarterWegman1979];
   [Mitzenmacher and Upfal][MitzenmacherUpfal2017].
2. **`TabulatedOddStride`**: `simpleTab` splits the low `d * b` bits of an input key `u` into `d`
   characters of `b = max 1 (Nat.log 2 (max n_max 2) / 2)` bits (`2 ^ b ≤ max 2 n_max` words per
   character table) and XORs their table entries (following the simple tabulation scheme of Zobrist
   1970 and Pătraşcu and Thorup 2012). `initCode d` samples the `d` character tables via
   `Code.rand` in `4 * Nat.log 2 (max n_max 2) + 5 * (d * 2 ^ b) + 30` instructions
   (`O(d * 2 ^ b + log n_max)`, which is `O(n_max)` for fixed `d`), and `evalCode d` evaluates
   `oddStride M (simpleTab b d M T u).val = (2 * (simpleTab b d M T u).val + 1) &&& (2 ^ M - 1)` in
   `8 * d + 21` deterministic instructions (`O(d)`). When `M > 0`, this stride `h₂(u)` is odd (at
   `M = 0` it is `0` on `Fin 1`), and for every `M` it is coprime to `2 ^ M`, so for any initial
   slot `h₁(u) : Fin (2 ^ M)` the linear probe sequence `probeSeq M h₁(u) tab i =
   (h₁(u) + i * h₂(u)) % 2 ^ M` is a bijection on `Fin (2 ^ M)` (`bijective_probeSeq`)
   [Cormen, Leiserson, Rivest, and Stein, Section 11.4][CLRS2009]. Only this full-cycle permutation
   property is proved here: no `k`-wise or 3-wise independence theorem for simple tabulation is
   claimed in this module, and `simpleTab` inspects only the low `d * b` bits of `u`.

## Main definitions

* `Cslib.Algorithms.WordRAM.Hashing.Tabulation.randFillLoop`,
  `Cslib.Algorithms.WordRAM.Hashing.Tabulation.randFillComp`,
  `Cslib.Algorithms.WordRAM.Hashing.Tabulation.extractSlice`: generic loop filling a contiguous
  memory slice with independent uniform `bits`-bit words.
* `Cslib.Algorithms.WordRAM.Hashing.Tabulation.RandomTable.resampleCode`,
  `Cslib.Algorithms.WordRAM.Hashing.Tabulation.RandomTable.lookupCode`,
  `Cslib.Algorithms.WordRAM.Hashing.Tabulation.RandomTable.xorLookupCode`: 1-D random table
  initialization/resampling and `O(1)` deterministic lookup.
* `Cslib.Algorithms.WordRAM.Hashing.Tabulation.TabulatedOddStride.charBits`,
  `Cslib.Algorithms.WordRAM.Hashing.Tabulation.TabulatedOddStride.simpleTab`,
  `Cslib.Algorithms.WordRAM.Hashing.Tabulation.TabulatedOddStride.oddStride`,
  `Cslib.Algorithms.WordRAM.Hashing.Tabulation.TabulatedOddStride.probeSeq`,
  `Cslib.Algorithms.WordRAM.Hashing.Tabulation.TabulatedOddStride.initCode`,
  `Cslib.Algorithms.WordRAM.Hashing.Tabulation.TabulatedOddStride.evalCode`: `d`-character simple
  tabulation and odd-stride permutation generator on the Word RAM.

## Main results

* `Cslib.Algorithms.WordRAM.Hashing.Tabulation.randFillLoop_execRand`,
  `Cslib.Algorithms.WordRAM.Hashing.Tabulation.map_extractSlice_eval_randFillComp`: exact execution
  and product uniformity of `randFillLoop`.
* `Cslib.Algorithms.WordRAM.Hashing.Tabulation.RandomTable.resampleCode_execRand`,
  `Cslib.Algorithms.WordRAM.Hashing.Tabulation.RandomTable.map_extractTable_eval_resampleComp`,
  `Cslib.Algorithms.WordRAM.Hashing.Tabulation.RandomTable.lookupCode_exec`,
  `Cslib.Algorithms.WordRAM.Hashing.Tabulation.RandomTable.xorLookupCode_exec`: exact execution and
  uniformity of `RandomTable`.
* `Cslib.Algorithms.WordRAM.Hashing.Tabulation.TabulatedOddStride.bijective_probeSeq`,
  `Cslib.Algorithms.WordRAM.Hashing.Tabulation.TabulatedOddStride.initCode_execRandWithin`,
  `Cslib.Algorithms.WordRAM.Hashing.Tabulation.TabulatedOddStride.evalCode_execWithin`: full-cycle
  permutation property, `O(d * 2 ^ b + log n_max)` initialization, and `O(d)` deterministic
  evaluation of `TabulatedOddStride`.

## References

* [J. L. Carter and M. N. Wegman, *Universal Classes of Hash Functions*][CarterWegman1979]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

public section

namespace Cslib.Algorithms.WordRAM.Hashing.Tabulation

open Cslib.WordRAM Cslib.Probability
open Cslib.Algorithms.WordRAM.ExactLog
open scoped ENNReal

/-! ## Section 1: Uniform random word-slice filler (`randFillLoop`) -/

/-- Register `0` of `randFillLoop`: write pointer `ptr`. -/
abbrev regPtr : Fin 6 := 0

/-- Register `1` of `randFillLoop`: end pointer `arrBase + len`. -/
abbrev regEnd : Fin 6 := 1

/-- Register `2` of `randFillLoop`: random bitmask `2 ^ bits - 1`. -/
abbrev regMask : Fin 6 := 2

/-- Register `3` of `randFillLoop`: constant `1`. -/
abbrev regOne : Fin 6 := 3

/-- Register `4` of `randFillLoop`: sampled value scratch register. -/
abbrev regVal : Fin 6 := 4

/-- Register `5` of `randFillLoop`: caller-preserved register. -/
abbrev regExtra : Fin 6 := 5

/-- Body of `randFillLoop`: samples `regVal ← rand regMask`, stores `*regPtr ← regVal`, and
advances `regPtr ← regPtr + regOne`. -/
@[expose] def randFillBody : Code .exact 6 :=
  .seq (.rand regVal regMask)
  (.seq (.op (.store regPtr regVal))
        (.op (.exactBin .add regPtr regPtr regOne)))

/-- Structured Word-RAM loop that fills `[regPtr, regEnd)` with independent uniform draws in
`[0, regMask]`. -/
@[expose] def randFillLoop : Code .exact 6 :=
  .loop (.lt regPtr regEnd) randFillBody

/-- Single-iteration state update of `randFillBody` when `Code.rand` draws `v`. -/
@[expose] def randFillStepData (arrBase v : ℕ) (x : Data 6) : Data 6 :=
  ((x.set regVal v).write arrBase v).set regPtr (arrBase + 1)

/-- Explicit `ProbComp (Data 6 × ℕ)` induced by `randFillLoop` over `len` words starting at
`arrBase`. -/
@[expose] def randFillComp (bits arrBase : ℕ) : ℕ → Data 6 → ProbComp (Data 6 × ℕ)
  | 0, x => pure (x, 2)
  | len + 1, x => do
    let k ← ProbComp.unifFin (2 ^ bits - 1)
    let z ← randFillComp bits (arrBase + 1) len (randFillStepData arrBase k.val x)
    pure (z.1, 3 + z.2 + 2)

/-- Extract a `< 2 ^ bits` word as an element of `Fin (2 ^ bits)`, defaulting to `0` out of
range. -/
@[expose] def extractWord (bits v : ℕ) : Fin (2 ^ bits) :=
  if h : v < 2 ^ bits then ⟨v, h⟩ else ⟨0, by positivity⟩

/-- Extract a contiguous slice of `len` words at `arrBase` as a tuple `Fin len → Fin (2 ^ bits)`. -/
@[expose] def extractSlice (arrBase bits len : ℕ) (mem : ℕ → ℕ) : Fin len → Fin (2 ^ bits) :=
  fun i => extractWord bits (mem (arrBase + i.val))

@[simp]
theorem extractWord_val_of_lt {bits v : ℕ} (hv : v < 2 ^ bits) :
    (extractWord bits v).val = v := by
  simp [extractWord, hv]

@[simp]
theorem extractWord_unifFin (bits : ℕ) (k : Fin (2 ^ bits - 1 + 1)) :
    extractWord bits k.val = finCongr (Nat.sub_add_cancel Nat.one_le_two_pow) k := by
  have hlt : k.val < 2 ^ bits := by
    have hpos : 1 ≤ 2 ^ bits := Nat.one_le_two_pow
    have hk := k.isLt
    omega
  apply Fin.ext
  simp [extractWord, hlt]

/-- One iteration of `randFillBody` executes in `3` instructions and `1` `rand` call. -/
theorem randFillBody_execRand {w bits arrBase : ℕ} {x : Data 6}
    (hptr : x.regs regPtr = arrBase) (hmask : x.regs regMask = 2 ^ bits - 1)
    (hone : x.regs regOne = 1) (hfit_ptr : Fits w (arrBase + 1))
    (hfit_mask : Fits w (2 ^ bits - 1)) :
    ExecRand w randFillBody x (do
      let k ← ProbComp.unifFin (2 ^ bits - 1)
      pure (randFillStepData arrBase k.val x, 3)) := by
  have hfit_src : Fits w (x.regs regMask) := by rwa [hmask]
  have h1 := ExecRand.rand (B := .exact) (w := w) (dst := regVal) (src := regMask) hfit_src
  rw [hmask] at h1
  have h23 : ∀ z ∈ (do
      let k ← ProbComp.unifFin (2 ^ bits - 1)
      pure (x.set regVal k.val, 1) : ProbComp (Data 6 × ℕ)).support,
      ExecRand w (.seq (.op (.store regPtr regVal))
        (.op (.exactBin .add regPtr regPtr regOne))) z.1
        (pure (randFillStepData arrBase (z.1.regs regVal) x, 2)) := by
    intro z hz
    obtain ⟨k, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    cases OracleComp.eq_of_mem_supportWith_pure hk
    set d1 := x.set regVal k.val
    have hd1_ptr : d1.regs regPtr = arrBase := by simp [d1, hptr, regPtr, regVal]
    have hd1_val : d1.regs regVal = k.val := by simp [d1]
    have s2 : Exec w (.op (.store regPtr regVal) : Code .exact 6)
        d1 (d1.write arrBase k.val) 1 := by
      simpa [hd1_ptr, hd1_val] using
        (Exec.store (B := .exact) (w := w) (a := regPtr) (s := regVal) (x := d1))
    set d2 := d1.write arrBase k.val
    have s3 : Exec w (.op (.exactBin .add regPtr regPtr regOne) : Code .exact 6)
        d2 (d2.set regPtr (arrBase + 1)) 1 :=
      exec_exactBin (by simp [d2, d1, hptr, hone, regPtr, regOne, regVal]) hfit_ptr
    simpa [randFillStepData, d2, d1, hd1_val] using (s2.seq s3).execRand
  have hseq := ExecRand.seq
    (m₂ := fun d => pure (randFillStepData arrBase (d.regs regVal) x, 2)) h1 h23
  simpa only [randFillBody, bind_assoc, pure_bind, Data.set_regs, Function.update_self] using hseq

/-- **Exact `ExecRand` semantics of `randFillLoop`** over `len` words starting at `arrBase`. -/
theorem randFillLoop_execRand {w bits arrBase : ℕ} (len : ℕ) {x : Data 6}
    (hptr : x.regs regPtr = arrBase) (hend : x.regs regEnd = arrBase + len)
    (hmask : x.regs regMask = 2 ^ bits - 1) (hone : x.regs regOne = 1)
    (hfit_end : Fits w (arrBase + len)) (hfit_mask : Fits w (2 ^ bits - 1)) :
    ExecRand w randFillLoop x (randFillComp bits arrBase len x) := by
  induction len generalizing arrBase x with
  | zero =>
    have hc : ¬(Cond.lt regPtr regEnd).Holds x := by
      simp [Cond.Holds, hptr, hend]
    exact ExecRand.loop_exit hc
  | succ len ih =>
    have hc : (Cond.lt regPtr regEnd).Holds x := by
      simp [Cond.Holds, hptr, hend]
    have hfit_ptr1 : Fits w (arrBase + 1) := hfit_end.of_le (by omega)
    have hb := randFillBody_execRand hptr hmask hone hfit_ptr1 hfit_mask
    have hcont : ∀ z ∈ (do
        let k ← ProbComp.unifFin (2 ^ bits - 1)
        pure (randFillStepData arrBase k.val x, 3) : ProbComp (Data 6 × ℕ)).support,
        ExecRand w randFillLoop z.1 (randFillComp bits (arrBase + 1) len z.1) := by
      intro z hz
      obtain ⟨k, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
      cases OracleComp.eq_of_mem_supportWith_pure hk
      refine ih (arrBase := arrBase + 1)
        (by simp +decide [randFillStepData, regPtr, regVal])
        (by simp +decide [randFillStepData, regEnd, regPtr, regVal, hend]; omega)
        (by simp +decide [randFillStepData, regMask, regPtr, regVal, hmask])
        (by simp +decide [randFillStepData, regOne, regPtr, regVal, hone])
        (by rwa [show arrBase + 1 + len = arrBase + (len + 1) by omega])
    have hiter := ExecRand.loop_iter hc hb hcont
    simpa only [randFillLoop, randFillComp, bind_assoc, pure_bind] using hiter

/-- `randFillComp bits arrBase len x` makes at most `len` `rand` calls. -/
theorem isQueryBounded_randFillComp (bits arrBase len : ℕ) (x : Data 6) :
    (randFillComp bits arrBase len x).IsQueryBounded len := by
  induction len generalizing arrBase x with
  | zero =>
    exact .pure _ 0
  | succ len ih =>
    dsimp only [randFillComp]
    rw [Nat.add_comm len 1]
    refine (ProbComp.isQueryBounded_unifFin (2 ^ bits - 1)).bind fun k => ?_
    simpa only [Nat.add_zero] using
      (ih (arrBase + 1) (randFillStepData arrBase k.val x)).bind fun _ => .pure _ 0

/-- Pathwise postcondition of `randFillComp`: takes `5 * len + 2` instructions, preserves registers
`regEnd`, `regMask`, `regOne`, `regExtra`, fills `[arrBase, arrBase + len)` with `< 2 ^ bits`
words, and preserves all memory outside `[arrBase, arrBase + len)`. -/
theorem mem_support_randFillComp {bits arrBase len : ℕ} {x : Data 6} {z : Data 6 × ℕ}
    (hz : z ∈ (randFillComp bits arrBase len x).support) :
    z.2 = 5 * len + 2 ∧
    z.1.regs regPtr = (if len = 0 then x.regs regPtr else arrBase + len) ∧
    z.1.regs regEnd = x.regs regEnd ∧
    z.1.regs regMask = x.regs regMask ∧
    z.1.regs regOne = x.regs regOne ∧
    z.1.regs regExtra = x.regs regExtra ∧
    (∀ i < len, z.1.mem (arrBase + i) < 2 ^ bits) ∧
    (∀ a, (a < arrBase ∨ arrBase + len ≤ a) → z.1.mem a = x.mem a) := by
  induction len generalizing arrBase x z with
  | zero =>
    dsimp only [randFillComp] at hz
    cases OracleComp.eq_of_mem_supportWith_pure hz
    refine ⟨rfl, by simp, rfl, rfl, rfl, rfl, fun _ hi => by omega, fun _ _ => rfl⟩
  | succ len ih =>
    dsimp only [randFillComp] at hz
    obtain ⟨k, -, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨z', hz', hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hpure
    obtain ⟨hsteps, hptr, hend, hmask, hone, hextra, hlt, hframe⟩ := ih hz'
    have hk_lt : k.val < 2 ^ bits := by
      have hpos : 1 ≤ 2 ^ bits := Nat.one_le_two_pow
      have hk := k.isLt
      omega
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Nat.succ_ne_zero, ↓reduceIte]
      rcases eq_or_ne len 0 with rfl | hlen
      · simp [hptr, randFillStepData]
      · rw [hptr, ite_eq_right hlen]
        omega
    · simpa [randFillStepData, regEnd, regPtr, regVal] using hend
    · simpa [randFillStepData, regMask, regPtr, regVal] using hmask
    · simpa [randFillStepData, regOne, regPtr, regVal] using hone
    · simpa [randFillStepData, regExtra, regPtr, regVal] using hextra
    · intro i hi
      rcases eq_or_ne i 0 with rfl | hi0
      · have hmem0 := hframe arrBase (Or.inl (by omega))
        simpa [randFillStepData, hmem0] using hk_lt
      · have hlt' := hlt (i - 1) (by omega)
        rwa [show arrBase + 1 + (i - 1) = arrBase + i by omega] at hlt'
    · intro a ha
      have h1 := hframe a (by omega)
      have hne : a ≠ arrBase := by omega
      simpa [randFillStepData, Function.update_of_ne hne] using h1

/-- Extracting `len + 1` words at `arrBase` after one `randFillStepData` step and the remaining
`len` steps equals `Fin.cons` of the first draw and the remaining `len`-word slice. -/
private theorem extractSlice_succ_of_support {bits arrBase len : ℕ} {x : Data 6}
    (k : Fin (2 ^ bits - 1 + 1)) {z : Data 6 × ℕ}
    (hz : z ∈ (randFillComp bits (arrBase + 1) len (randFillStepData arrBase k.val x)).support) :
    extractSlice arrBase bits (len + 1) z.1.mem =
      Fin.cons (finCongr (Nat.sub_add_cancel Nat.one_le_two_pow) k)
        (extractSlice (arrBase + 1) bits len z.1.mem) := by
  obtain ⟨-, -, -, -, -, -, -, hframe⟩ := mem_support_randFillComp hz
  funext j
  refine Fin.cases ?_ ?_ j
  · have h0 := hframe arrBase (Or.inl (by omega))
    simp [extractSlice, randFillStepData, h0]
  · intro i
    simp only [extractSlice, Fin.cons_succ, Fin.val_succ]
    congr 2
    omega

/-- **Uniformity of `randFillComp`**: the slice `extractSlice arrBase bits len z.1.mem` produced by
`randFillComp bits arrBase len x` has the exact product uniform distribution
`PMF.uniformOfFintype (Fin len → Fin (2 ^ bits))`. -/
theorem map_extractSlice_eval_randFillComp (bits arrBase len : ℕ) (x : Data 6) :
    ((randFillComp bits arrBase len x).eval).map (fun z => extractSlice arrBase bits len z.1.mem) =
      PMF.uniformOfFintype (Fin len → Fin (2 ^ bits)) := by
  induction len generalizing arrBase x with
  | zero =>
    ext f
    have heq : f = extractSlice arrBase bits 0 x.mem := Subsingleton.elim _ _
    simp [randFillComp, ProbComp.eval_pure, PMF.map, PMF.pure_apply, heq,
      PMF.uniformOfFintype_apply]
  | succ len ih =>
    let e := finCongr (Nat.sub_add_cancel (Nat.one_le_two_pow (n := bits)))
    have hstep : ((randFillComp bits arrBase (len + 1) x).eval).map
        (fun z => extractSlice arrBase bits (len + 1) z.1.mem) =
        (PMF.uniformOfFintype (Fin (2 ^ bits))).bind (fun first =>
          (PMF.uniformOfFintype (Fin len → Fin (2 ^ bits))).map (Fin.cons first)) := by
      dsimp only [randFillComp]
      rw [ProbComp.eval_bind, ProbComp.eval_unifFin, PMF.map_bind]
      have hbody : ∀ k : Fin (2 ^ bits - 1 + 1),
          ((do
            let z ← randFillComp bits (arrBase + 1) len (randFillStepData arrBase k.val x)
            pure (z.1, 3 + z.2 + 2)).eval).map
              (fun z : Data 6 × ℕ => extractSlice arrBase bits (len + 1) z.1.mem) =
            (PMF.uniformOfFintype (Fin len → Fin (2 ^ bits))).map (Fin.cons (e k)) := by
        intro k
        have hd : (do
            let z ← randFillComp bits (arrBase + 1) len (randFillStepData arrBase k.val x)
            pure (z.1, 3 + z.2 + 2)) =
            (fun z : Data 6 × ℕ => (z.1, 3 + z.2 + 2)) <$>
              randFillComp bits (arrBase + 1) len (randFillStepData arrBase k.val x) :=
          bind_pure_comp _ _
        rw [hd, ProbComp.eval_map, PMF.map_comp]
        have hcongr :
            ((randFillComp bits (arrBase + 1) len (randFillStepData arrBase k.val x)).eval).map
              ((fun z : Data 6 × ℕ => extractSlice arrBase bits (len + 1) z.1.mem) ∘
                fun z : Data 6 × ℕ => (z.1, 3 + z.2 + 2)) =
            ((randFillComp bits (arrBase + 1) len (randFillStepData arrBase k.val x)).eval).map
              (Fin.cons (e k) ∘
                fun z : Data 6 × ℕ => extractSlice (arrBase + 1) bits len z.1.mem) := by
          apply PMF.map_congr_on_support
          intro z hz
          rw [ProbComp.support_eval] at hz
          exact extractSlice_succ_of_support (z := z) k hz
        rw [hcongr, ← PMF.map_comp, ih (arrBase + 1) (randFillStepData arrBase k.val x)]
      have hbind : (PMF.uniformOfFintype (Fin (2 ^ bits - 1 + 1))).bind
          (fun a =>
            PMF.map (fun z : Data 6 × ℕ => extractSlice arrBase bits (len + 1) z.1.mem)
              (do
                let z ← randFillComp bits (arrBase + 1) len (randFillStepData arrBase a.val x)
                pure (z.1, 3 + z.2 + 2)).eval) =
          (PMF.uniformOfFintype (Fin (2 ^ bits - 1 + 1))).bind
            (fun a => (PMF.uniformOfFintype (Fin len → Fin (2 ^ bits))).map (Fin.cons (e a))) := by
        congr 1
        funext k
        exact hbody k
      rw [hbind]
      have heq := PMF.uniformOfFintype_map_equiv e
      rw [← heq, PMF.bind_map]
      rfl
    rw [hstep, ← PMF.pi_uniformOfFintype, ← PMF.pi_fin_succ, PMF.pi_uniformOfFintype]

/-! ## Section 2: `RandomTable` — 1-D random table for Cuckoo Hashing -/

namespace RandomTable

/-- Footprint size of `RandomTable M`: `2 ^ M` words at `[base, base + 2 ^ M)`. -/
@[expose] def space (M : ℕ) : ℕ := 2 ^ M

/-- Register `0`: holds the base memory address `base` of the table. -/
abbrev regBase : Fin 6 := 0

/-- Register `1`: holds `M` during `resampleCode`, or index `idx < 2 ^ M` during `lookupCode`. -/
abbrev regM : Fin 6 := 1

/-- Alias for register `1` when used as the lookup index `idx < 2 ^ M`. -/
abbrev regIdx : Fin 6 := 1

/-- Register `2`: receives `Z[idx]` in `lookupCode` or `fx ^^^ Z[idx]` in `xorLookupCode`. -/
abbrev regOut : Fin 6 := 2

/-- Register `3`: scratch register 1. -/
abbrev regT1 : Fin 6 := 3

/-- Register `4`: scratch register 2. -/
abbrev regT2 : Fin 6 := 4

/-- Register `5`: scratch register 3. -/
abbrev regT3 : Fin 6 := 5

/-- Memory representation invariant: `[base, base + 2 ^ M)` holds the entries of
`Z : Fin (2 ^ M) → Fin (2 ^ M)`. -/
def Rep (base M : ℕ) (Z : Fin (2 ^ M) → Fin (2 ^ M)) (mem : ℕ → ℕ) : Prop :=
  ∀ i : Fin (2 ^ M), mem (base + i.val) = (Z i).val

/-- Extract the random table `Z : Fin (2 ^ M) → Fin (2 ^ M)` from memory at `base`. -/
@[expose] def extractTable (base M : ℕ) (mem : ℕ → ℕ) : Fin (2 ^ M) → Fin (2 ^ M) :=
  extractSlice base M (2 ^ M) mem

/-- If every word in `[base, base + 2 ^ M)` is `< 2 ^ M`, then
`Rep base M (extractTable base M mem) mem` holds. -/
theorem rep_extractTable {base M : ℕ} {mem : ℕ → ℕ}
    (h : ∀ i < 2 ^ M, mem (base + i) < 2 ^ M) :
    Rep base M (extractTable base M mem) mem := by
  intro i
  simp [extractTable, extractSlice, h i.val i.isLt]

/-- Injective register permutation mapping `randFillLoop`'s registers into `RandomTable` so that
`regExtra` maps to `regBase` (preserving `regBase`). -/
@[expose] def fillMap : Fin 6 → Fin 6
  | 0 => regT1
  | 1 => regT2
  | 2 => regT3
  | 3 => regOut
  | 4 => regM
  | 5 => regBase

theorem injective_fillMap : Function.Injective fillMap := by
  decide

/-- Deterministic setup before `randFillLoop` in `resampleCode`: computes `2 ^ M`, `2 ^ M - 1`,
`base + 2 ^ M`, and initializes the loop registers. -/
@[expose] def setupCode : Code .exact 6 :=
  .seq (.op (.const regOut 1))
  (.seq (.op (.exactBin .shiftLeft regT2 regOut regM))
  (.seq (.op (.exactBin .sub regT3 regT2 regOut))
  (.seq (.op (.copy regT1 regBase))
        (.op (.exactBin .add regT2 regBase regT2)))))

/-- Closed-form machine data after `setupCode`. -/
@[expose] def setupData (base M : ℕ) (x : Data 6) : Data 6 :=
  ((((x.set regOut 1).set regT2 (2 ^ M)).set regT3 (2 ^ M - 1)).set regT1 base).set
    regT2 (base + 2 ^ M)

/-- Structured Word-RAM program that initializes or resamples `Z[0 .. 2 ^ M - 1]` at `base` using
`2 ^ M` calls to `Code.rand` on `2 ^ M - 1`. -/
@[expose] def resampleCode : Code .exact 6 :=
  .seq setupCode (randFillLoop.rename fillMap)

/-- Alias for `resampleCode` when used for initial table construction. -/
abbrev initCode : Code .exact 6 := resampleCode

/-- Explicit `ProbComp (Data 6 × ℕ)` induced by `resampleCode` at `(base, M)` from `x`. -/
@[expose] noncomputable def resampleComp (base M : ℕ) (x : Data 6) : ProbComp (Data 6 × ℕ) :=
  let s := setupData base M x
  (fun z => (z.1.extend fillMap s, 5 + z.2)) <$>
    randFillComp M base (2 ^ M) (s.comap fillMap)

/-- `setupCode` executes deterministically in `5` instructions when `Fits w (base + 2 ^ M)` and
`Fits w (2 ^ M)`. -/
theorem setupCode_exec {w base M : ℕ} {x : Data 6}
    (hbase : x.regs regBase = base) (hM : x.regs regM = M)
    (hfit_end : Fits w (base + 2 ^ M)) (hfit_pow : Fits w (2 ^ M)) :
    Exec w setupCode x (setupData base M x) 5 := by
  have hpos : 1 ≤ 2 ^ M := Nat.one_le_two_pow
  have hfit_1 : Fits w 1 := hfit_pow.of_le hpos
  have hfit_mask : Fits w (2 ^ M - 1) := hfit_pow.of_le (Nat.sub_le _ _)
  set d1 := x.set regOut 1
  have s1 : Exec w (.op (.const regOut 1) : Code .exact 6) x d1 1 := Exec.const hfit_1
  set d2 := d1.set regT2 (2 ^ M)
  have s2 : Exec w (.op (.exactBin .shiftLeft regT2 regOut regM) : Code .exact 6) d1 d2 1 :=
    exec_exactBin (by simp [d1, hM, regOut, regM, Nat.shiftLeft_eq]) hfit_pow
  set d3 := d2.set regT3 (2 ^ M - 1)
  have s3 : Exec w (.op (.exactBin .sub regT3 regT2 regOut) : Code .exact 6) d2 d3 1 :=
    exec_exactBin (by simp [d2, d1, hpos, regT2, regOut]) hfit_mask
  set d4 := d3.set regT1 base
  have s4 : Exec w (.op (.copy regT1 regBase) : Code .exact 6) d3 d4 1 := by
    simpa [d3, d2, d1, hbase, regBase, regT1, regT2, regT3, regOut] using
      (Exec.copy (B := .exact) (w := w) (d := regT1) (s := regBase) (x := d3))
  set d5 := d4.set regT2 (base + 2 ^ M)
  have s5 : Exec w (.op (.exactBin .add regT2 regBase regT2) : Code .exact 6) d4 d5 1 :=
    exec_exactBin (by simp [d4, d3, d2, d1, hbase, regBase, regT1, regT2, regT3, regOut]) hfit_end
  exact s1.seq (s2.seq (s3.seq (s4.seq s5)))

/-- **Exact `ExecRand` execution of `RandomTable.resampleCode`**: runs in `5 * 2 ^ M + 7`
instructions and `2 ^ M` `rand` calls. -/
theorem resampleCode_execRand {w base M : ℕ} {x : Data 6}
    (hbase : x.regs regBase = base) (hM : x.regs regM = M)
    (hfit_end : Fits w (base + 2 ^ M)) (hfit_pow : Fits w (2 ^ M)) :
    ExecRand w resampleCode x (resampleComp base M x) := by
  have h1 := setupCode_exec hbase hM hfit_end hfit_pow
  set s := setupData base M x
  have hfit_mask : Fits w (2 ^ M - 1) := hfit_pow.of_le (Nat.sub_le _ _)
  have hloop := randFillLoop_execRand (w := w) (bits := M) (arrBase := base) (len := 2 ^ M)
    (x := s.comap fillMap)
    (by simp +decide [s, setupData, fillMap, Data.comap])
    (by simp +decide [s, setupData, fillMap, Data.comap])
    (by simp +decide [s, setupData, fillMap, Data.comap])
    (by simp +decide [s, setupData, fillMap, Data.comap])
    hfit_end hfit_mask
  have hren := hloop.rename injective_fillMap
  have hseq := h1.seqRand hren
  rw [resampleCode]
  simpa only [resampleComp, s, Functor.map_map] using hseq

/-- **Uniformity of `RandomTable.resampleComp`**: the extracted table `extractTable base M z.1.mem`
is distributed according to `PMF.uniformOfFintype (Fin (2 ^ M) → Fin (2 ^ M))`. -/
theorem map_extractTable_eval_resampleComp (base M : ℕ) (x : Data 6) :
    ((resampleComp base M x).eval).map (fun z => extractTable base M z.1.mem) =
      PMF.uniformOfFintype (Fin (2 ^ M) → Fin (2 ^ M)) := by
  dsimp only [resampleComp, extractTable]
  rw [ProbComp.eval_map, PMF.map_comp]
  exact map_extractSlice_eval_randFillComp M base (2 ^ M) ((setupData base M x).comap fillMap)

/-- Hoare-style `ExecRandWithin` specification for `RandomTable.resampleCode`: runs in
`5 * 2 ^ M + 7` steps and `2 ^ M` `rand` calls, establishing `Rep`, preserving `regBase`, and
modifying only `[base, base + 2 ^ M)`. -/
theorem resampleCode_execRandWithin {w base M : ℕ} {x : Data 6}
    (hbase : x.regs regBase = base) (hM : x.regs regM = M)
    (hfit_end : Fits w (base + 2 ^ M)) (hfit_pow : Fits w (2 ^ M)) :
    ExecRandWithin w resampleCode x
      (fun y => Rep base M (extractTable base M y.mem) y.mem ∧
        y.regs regBase = base ∧
        (∀ a, (a < base ∨ base + 2 ^ M ≤ a) → y.mem a = x.mem a))
      (5 * 2 ^ M + 7) (2 ^ M) := by
  refine ⟨resampleComp base M x, resampleCode_execRand hbase hM hfit_end hfit_pow, ?_, ?_⟩
  · dsimp only [resampleComp]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      (isQueryBounded_randFillComp M base (2 ^ M) _)
  · intro z hz
    dsimp only [resampleComp] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    obtain ⟨hsteps, -, -, -, -, hextra, hlt, hframe⟩ := mem_support_randFillComp hz₀
    have hbase' : (z₀.1.extend fillMap (setupData base M x)).regs regBase = base := by
      change ((z₀.1.extend fillMap (setupData base M x)).comap fillMap).regs regExtra = base
      rw [Data.comap_extend injective_fillMap, hextra]
      simpa +decide [setupData, fillMap, Data.comap] using hbase
    exact ⟨⟨rep_extractTable hlt, hbase', hframe⟩, by omega⟩

/-- Structured Word-RAM program that reads `Z[regIdx]` at `regBase + regIdx` into `regOut` in `2`
deterministic instructions. -/
@[expose] def lookupCode : Code .exact 6 :=
  .seq (.op (.exactBin .add regT1 regBase regIdx))
        (.op (.load regOut regT1))

/-- Final machine data after `lookupCode`. -/
@[expose] def lookupData (x : Data 6) : Data 6 :=
  let addr := x.regs regBase + x.regs regIdx
  (x.set regT1 addr).set regOut (x.mem addr)

/-- `lookupCode` executes in `2` deterministic instructions, preserving memory and `regBase` and
writing `(Z idx).val` into `regOut`. -/
theorem lookupCode_exec {w base M : ℕ} {Z : Fin (2 ^ M) → Fin (2 ^ M)} {x : Data 6}
    (hrep : Rep base M Z x.mem) (idx : Fin (2 ^ M))
    (hbase : x.regs regBase = base) (hidx : x.regs regIdx = idx.val)
    (hfit_end : Fits w (base + 2 ^ M)) :
    Exec w lookupCode x (lookupData x) 2 ∧
    (lookupData x).regs regOut = (Z idx).val ∧
    (lookupData x).regs regBase = base ∧
    (lookupData x).mem = x.mem := by
  have hfit_addr : Fits w (base + idx.val) := hfit_end.of_le (by have := idx.isLt; omega)
  set d1 := x.set regT1 (base + idx.val)
  have s1 : Exec w (.op (.exactBin .add regT1 regBase regIdx) : Code .exact 6) x d1 1 :=
    exec_exactBin (by simp [hbase, hidx]) hfit_addr
  have s2 : Exec w (.op (.load regOut regT1) : Code .exact 6) d1
      (d1.set regOut (x.mem (base + idx.val))) 1 := by
    simpa [d1] using (Exec.load (B := .exact) (w := w) (d := regOut) (a := regT1) (x := d1))
  have hd : d1.set regOut (x.mem (base + idx.val)) = lookupData x := by
    simp [d1, lookupData, hbase, hidx]
  rw [hd] at s2
  refine ⟨s1.seq s2, ?_, by simp [lookupData, hbase, regBase, regT1, regOut], rfl⟩
  simp [lookupData, hbase, hidx, hrep idx]

/-- Structured Word-RAM program that computes `regOut ← regOut ^^^ Z[regIdx]` in `3` deterministic
instructions (computing `f(u) ^^^ Z[g(u)]` when `regOut` holds `f(u)` and `regIdx` holds
`g(u)`). -/
@[expose] def xorLookupCode : Code .exact 6 :=
  .seq (.op (.exactBin .add regT1 regBase regIdx))
  (.seq (.op (.load regT2 regT1))
        (.op (.exactBin .xor regOut regOut regT2)))

/-- Final machine data after `xorLookupCode`. -/
@[expose] def xorLookupData (x : Data 6) : Data 6 :=
  let addr := x.regs regBase + x.regs regIdx
  let zval := x.mem addr
  ((x.set regT1 addr).set regT2 zval).set regOut (x.regs regOut ^^^ zval)

/-- `xorLookupCode` executes in `3` deterministic instructions, preserving memory and `regBase` and
writing `fx.val ^^^ (Z idx).val < 2 ^ M` into `regOut`. -/
theorem xorLookupCode_exec {w base M : ℕ} {Z : Fin (2 ^ M) → Fin (2 ^ M)} {x : Data 6}
    (hrep : Rep base M Z x.mem) (idx fx : Fin (2 ^ M))
    (hbase : x.regs regBase = base) (hidx : x.regs regIdx = idx.val)
    (hfx : x.regs regOut = fx.val)
    (hfit_end : Fits w (base + 2 ^ M)) (hfit_pow : Fits w (2 ^ M)) :
    Exec w xorLookupCode x (xorLookupData x) 3 ∧
    (xorLookupData x).regs regOut = fx.val ^^^ (Z idx).val ∧
    (xorLookupData x).regs regOut < 2 ^ M ∧
    (xorLookupData x).regs regBase = base ∧
    (xorLookupData x).mem = x.mem := by
  have hfit_addr : Fits w (base + idx.val) := hfit_end.of_le (by have := idx.isLt; omega)
  have hxor_lt : fx.val ^^^ (Z idx).val < 2 ^ M := Nat.xor_lt_two_pow fx.isLt (Z idx).isLt
  have hfit_xor : Fits w (fx.val ^^^ (Z idx).val) := hfit_pow.of_le (le_of_lt hxor_lt)
  set d1 := x.set regT1 (base + idx.val)
  have s1 : Exec w (.op (.exactBin .add regT1 regBase regIdx) : Code .exact 6) x d1 1 :=
    exec_exactBin (by simp [hbase, hidx]) hfit_addr
  set d2 := d1.set regT2 (Z idx).val
  have s2 : Exec w (.op (.load regT2 regT1) : Code .exact 6) d1 d2 1 := by
    simpa [d1, d2, hrep idx] using
      (Exec.load (B := .exact) (w := w) (d := regT2) (a := regT1) (x := d1))
  set d3 := d2.set regOut (fx.val ^^^ (Z idx).val)
  have s3 : Exec w (.op (.exactBin .xor regOut regOut regT2) : Code .exact 6) d2 d3 1 :=
    exec_exactBin (by simp [d2, d1, hfx, regOut, regT1, regT2]) hfit_xor
  have hd3 : d3 = xorLookupData x := by
    simp [d3, d2, d1, xorLookupData, hbase, hidx, hfx, hrep idx]
  rw [hd3] at s3
  refine ⟨s1.seq (s2.seq s3), ?_, ?_,
    by simp [xorLookupData, hbase, regBase, regT1, regT2, regOut], rfl⟩
  · simp [xorLookupData, hbase, hidx, hfx, hrep idx]
  · simpa [xorLookupData, hbase, hidx, hfx, hrep idx] using hxor_lt

end RandomTable

/-! ## Section 3: `TabulatedOddStride` -/

namespace TabulatedOddStride

/-- Character bit-width `b = max 1 (⌊log₂ (max n_max 2)⌋ / 2)` for `d`-character simple tabulation,
ensuring `1 ≤ b` and `2 ^ b ≤ max 2 n_max` (`2 ^ (2 * b) ≤ max 4 n_max`). -/
@[expose] def charBits (n_max : ℕ) : ℕ :=
  max 1 (Nat.log 2 (max n_max 2) / 2)

/-- `charBits n_max` is always at least `1`. -/
theorem one_le_charBits (n_max : ℕ) : 1 ≤ charBits n_max :=
  Nat.le_max_left 1 _

/-- `charBits n_max` is always positive. -/
theorem charBits_pos (n_max : ℕ) : 0 < charBits n_max :=
  one_le_charBits n_max

/-- The character alphabet size `2 ^ charBits n_max` is at most `max 2 n_max`. -/
theorem two_pow_charBits_le (n_max : ℕ) : 2 ^ charBits n_max ≤ max 2 n_max := by
  have hlog_ge : 1 ≤ Nat.log 2 (max n_max 2) :=
    Nat.le_log_of_pow_le (by decide) (by omega)
  have hle_log : charBits n_max ≤ Nat.log 2 (max n_max 2) := by
    simp only [charBits]
    omega
  calc
    2 ^ charBits n_max ≤ 2 ^ Nat.log 2 (max n_max 2) :=
      Nat.pow_le_pow_right (by decide) hle_log
    _ ≤ max n_max 2 := Nat.pow_log_le_self 2 (by omega)
    _ = max 2 n_max := Nat.max_comm n_max 2

/-- Odd stride `(2 * tab + 1) &&& (2 ^ M - 1) = (2 * tab + 1) % 2 ^ M` in `Fin (2 ^ M)`. -/
@[expose] def oddStride (M tab : ℕ) : Fin (2 ^ M) :=
  ⟨(2 * tab + 1) &&& (2 ^ M - 1), by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos M)⟩

@[simp]
theorem val_oddStride (M tab : ℕ) : (oddStride M tab).val = (2 * tab + 1) % 2 ^ M :=
  Nat.and_two_pow_sub_one_eq_mod (2 * tab + 1) M

/-- When `0 < M`, `(oddStride M tab).val` is odd (`% 2 = 1`). -/
theorem odd_oddStride {M : ℕ} (hM : 0 < M) (tab : ℕ) : (oddStride M tab).val % 2 = 1 := by
  rw [val_oddStride]
  have hdvd : 2 ∣ 2 ^ M := by
    cases M with
    | zero => omega
    | succ m => exact ⟨2 ^ m, by ring⟩
  rw [Nat.mod_mod_of_dvd _ hdvd]
  omega

/-- `(oddStride M tab).val` is always coprime to `2 ^ M`. -/
theorem coprime_oddStride_two_pow (M tab : ℕ) : Nat.Coprime (oddStride M tab).val (2 ^ M) := by
  rw [val_oddStride, Nat.Coprime, ← Nat.gcd_rec]
  have hcop2 : Nat.Coprime 2 (2 * tab + 1) := by
    rw [Nat.coprime_two_left, Nat.odd_iff]
    omega
  exact hcop2.pow_left M

/-- Double-hashing probe sequence `probeSeq M h₁ tab i = (h₁ + i * oddStride M tab) mod 2 ^ M`
on `Fin (2 ^ M)`. -/
@[expose] def probeSeq (M h₁ tab : ℕ) (i : Fin (2 ^ M)) : Fin (2 ^ M) :=
  ⟨(h₁ + i.val * (oddStride M tab).val) % 2 ^ M, Nat.mod_lt _ (Nat.two_pow_pos M)⟩

/-- Because `oddStride M tab` is coprime to `2 ^ M`, `probeSeq M h₁ tab` is a full-cycle
bijection (permutation) of `Fin (2 ^ M)` for every `M`, initial probe `h₁`, and raw table sum
`tab`. -/
theorem bijective_probeSeq (M h₁ tab : ℕ) : Function.Bijective (probeSeq M h₁ tab) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  have hinj : ∀ i j : Fin (2 ^ M), j.val ≤ i.val →
      probeSeq M h₁ tab i = probeSeq M h₁ tab j → i = j := by
    intro i j hij heq
    have hmod : (h₁ + j.val * (oddStride M tab).val) ≡
        (h₁ + i.val * (oddStride M tab).val) [MOD 2 ^ M] := by
      simpa [probeSeq, Fin.ext_iff, Nat.ModEq] using heq.symm
    have hmul : j.val * (oddStride M tab).val ≡
        i.val * (oddStride M tab).val [MOD 2 ^ M] :=
      Nat.ModEq.add_left_cancel' h₁ hmod
    have hsub : 0 + j.val * (oddStride M tab).val ≡
        (i.val - j.val) * (oddStride M tab).val + j.val * (oddStride M tab).val [MOD 2 ^ M] := by
      simpa [Nat.zero_add, ← Nat.add_mul, Nat.sub_add_cancel hij] using hmul
    have hzero : 0 ≡ (i.val - j.val) * (oddStride M tab).val [MOD 2 ^ M] :=
      Nat.ModEq.add_right_cancel' (j.val * (oddStride M tab).val) hsub
    have hdvd_mul : 2 ^ M ∣ (i.val - j.val) * (oddStride M tab).val :=
      (Nat.modEq_zero_iff_dvd.mp hzero.symm)
    have hdvd : 2 ^ M ∣ i.val - j.val :=
      (coprime_oddStride_two_pow M tab).symm.dvd_of_dvd_mul_right hdvd_mul
    have hlt : i.val - j.val < 2 ^ M := by
      have := i.isLt
      omega
    have hdiff0 : i.val - j.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    exact Fin.ext (by omega)
  intro i j heq
  rcases le_total j.val i.val with hij | hij
  · exact hinj i j hij heq
  · exact (hinj j i hij heq.symm).symm

/-- Tail-recursive `d`-character simple tabulation accumulator from character offset `j` across
`rem` remaining characters: XORs `T[(j + k) * 2 ^ b + ((u >>> (k * b)) &&& (2 ^ b - 1))]` into
`acc`. -/
@[expose] def simpleTabAux (b d M : ℕ) (T : Fin (d * 2 ^ b) → Fin (2 ^ M)) :
    ℕ → ℕ → ℕ → Fin (2 ^ M) → Fin (2 ^ M)
  | 0, _, _, acc => acc
  | rem + 1, j, u, acc =>
    let ch := u &&& (2 ^ b - 1)
    let idx := j * 2 ^ b + ch
    let entry : Fin (2 ^ M) :=
      if h : idx < d * 2 ^ b then T ⟨idx, h⟩ else ⟨0, Nat.two_pow_pos M⟩
    simpleTabAux b d M T rem (j + 1) (u >>> b)
      ⟨acc.val ^^^ entry.val, Nat.xor_lt_two_pow acc.isLt entry.isLt⟩

/-- `d`-character simple tabulation hash `simpleTab b d M T u : Fin (2 ^ M)`, XORing the table
entries for the first `d` base-`2 ^ b` characters of `u`. -/
@[expose] def simpleTab (b d M : ℕ) (T : Fin (d * 2 ^ b) → Fin (2 ^ M)) (u : ℕ) : Fin (2 ^ M) :=
  simpleTabAux b d M T d 0 u ⟨0, Nat.two_pow_pos M⟩

/-- Tabulated odd stride `tabulatedOddStride b d M T u : Fin (2 ^ M)` obtained by mapping the
`d`-character simple tabulation hash through `oddStride M`. -/
@[expose] def tabulatedOddStride (b d M : ℕ) (T : Fin (d * 2 ^ b) → Fin (2 ^ M)) (u : ℕ) :
    Fin (2 ^ M) :=
  oddStride M (simpleTab b d M T u).val

/-- Memory footprint `4 + d * 2 ^ b` words for a `d`-character simple tabulation table with
character bit-width `b` (4 header words `(b, 2 ^ b, 2 ^ b - 1, 2 ^ M - 1)` followed by
`d * 2 ^ b` random `< 2 ^ M` words). -/
@[expose] def spaceFromB (b d : ℕ) : ℕ := 4 + d * 2 ^ b

/-- Memory footprint `4 + d * 2 ^ (charBits n_max)` words at capacity parameter `n_max`. -/
@[expose] def space (n_max d : ℕ) : ℕ := spaceFromB (charBits n_max) d

/-- Memory representation predicate for `TabulatedOddStride` at `[base, base + 4 + d * 2 ^ b)`:
header words `b`, `2 ^ b`, `2 ^ b - 1`, `2 ^ M - 1` at `base + 0 .. base + 3`, and table entries
`(T i).val` at `base + 4 + i.val` for `i : Fin (d * 2 ^ b)`. -/
@[expose] def Rep (base b d M : ℕ) (T : Fin (d * 2 ^ b) → Fin (2 ^ M)) (mem : ℕ → ℕ) : Prop :=
  mem base = b ∧
  mem (base + 1) = 2 ^ b ∧
  mem (base + 2) = 2 ^ b - 1 ∧
  mem (base + 3) = 2 ^ M - 1 ∧
  ∀ i : Fin (d * 2 ^ b), mem (base + 4 + i.val) = (T i).val

/-- Extract the flat character table `Fin (d * 2 ^ b) → Fin (2 ^ M)` from `[base + 4, ...)`. -/
@[expose] def extractTable (base b d M : ℕ) (mem : ℕ → ℕ) : Fin (d * 2 ^ b) → Fin (2 ^ M) :=
  extractSlice (base + 4) M (d * 2 ^ b) mem

/-- Register `0` of `TabulatedOddStride`: base memory address `base`. -/
abbrev regBase : Fin 9 := 0

/-- Register `1` of `TabulatedOddStride`: holds `n_max` in `initCode` or input key `u` in
`evalCode`. -/
abbrev regKey : Fin 9 := 1

/-- Register `2` of `TabulatedOddStride`: holds `M` in `initCode` or receives the odd stride in
`evalCode`. -/
abbrev regOut : Fin 9 := 2

/-- Register `3` of `TabulatedOddStride`: table pointer scratch register. -/
abbrev regPtr : Fin 9 := 3

/-- Register `4` of `TabulatedOddStride`: end pointer / mask scratch register. -/
abbrev regEnd : Fin 9 := 4

/-- Register `5` of `TabulatedOddStride`: character bit-width `b` / loop bound register. -/
abbrev regB : Fin 9 := 5

/-- Register `6` of `TabulatedOddStride`: character alphabet size `2 ^ b` / sampled value
register. -/
abbrev regPowB : Fin 9 := 6

/-- Register `7` of `TabulatedOddStride`: character mask `2 ^ b - 1` register. -/
abbrev regMaskB : Fin 9 := 7

/-- Register `8` of `TabulatedOddStride`: general scratch register. -/
abbrev regTmp : Fin 9 := 8

/-- Register injection `Fin 3 → Fin 9` mapping `log2Loop`'s `(rem, acc, one)` to
`(regPtr, regB, regTmp)`. -/
@[expose] def logMap9 : Fin 3 → Fin 9
  | ⟨0, _⟩ => regPtr
  | ⟨1, _⟩ => regB
  | ⟨2, _⟩ => regTmp

theorem injective_logMap9 : Function.Injective logMap9 := by
  decide

/-- Register injection `Fin 6 → Fin 9` mapping `randFillLoop`'s `(ptr, end, mask, one, val, extra)`
to `(regPtr, regB, regEnd, regTmp, regPowB, regBase)`. -/
@[expose] def fillMap9 : Fin 6 → Fin 9
  | ⟨0, _⟩ => regPtr
  | ⟨1, _⟩ => regB
  | ⟨2, _⟩ => regEnd
  | ⟨3, _⟩ => regTmp
  | ⟨4, _⟩ => regPowB
  | ⟨5, _⟩ => regBase

theorem injective_fillMap9 : Function.Injective fillMap9 := by
  decide

/-- Structured Word-RAM program that computes `regB ← charBits n_max`
(`= max 1 (⌊log₂ (max n_max 2)⌋ / 2)`) at runtime from `n_max` in `regKey`, using `regPtr`,
`regB`, `regTmp` as scratch registers and preserving `regBase`, `regOut`, and all memory. -/
@[expose] def charBitsCode : Code .exact 9 :=
  .seq (.op (.const regTmp 2))
  (.seq (maxCode regPtr regKey regTmp)
  (.seq (.op (.const regB 0))
  (.seq (.op (.const regTmp 1))
  (.seq (log2Loop.rename logMap9)
  (.seq (.op (.exactBin .shiftRight regB regB regTmp))
        (maxCode regB regB regTmp))))))

/-- State after `charBitsCode` starting from `n_max` in `regKey`. -/
noncomputable def charBitsData (n_max : ℕ) (x : Data 9) : Data 9 :=
  let dPre := (((x.set regTmp 2).set regPtr (max n_max 2)).set regB 0).set regTmp 1
  let dLog := (log2LoopData (max n_max 2) 0 (dPre.comap logMap9)).extend logMap9 dPre
  (dLog.set regB (Nat.log 2 (max n_max 2) / 2)).set regB (charBits n_max)

/-- `charBitsCode` executes deterministically in `4 * Nat.log 2 (max n_max 2) + 12` instructions,
setting `regB = charBits n_max` while preserving `regBase`, `regOut`, and all memory. -/
theorem charBitsCode_exec {w n_max : ℕ} {x : Data 9}
    (hn : x.regs regKey = n_max) (hfit_n : Fits w (max n_max 2)) :
    Exec w charBitsCode x (charBitsData n_max x) (4 * Nat.log 2 (max n_max 2) + 12) ∧
    (charBitsData n_max x).regs regB = charBits n_max ∧
    (charBitsData n_max x).regs regBase = x.regs regBase ∧
    (charBitsData n_max x).regs regOut = x.regs regOut ∧
    (charBitsData n_max x).mem = x.mem := by
  have hfit_2 : Fits w 2 := hfit_n.of_le (Nat.le_max_right n_max 2)
  have hfit_1 : Fits w 1 := hfit_2.of_le (by decide)
  have hfit_0 : Fits w 0 := hfit_1.of_le (by decide)
  have hlog_le : Nat.log 2 (max n_max 2) ≤ max n_max 2 := Nat.log_le_self 2 (max n_max 2)
  have hfit_log : Fits w (Nat.log 2 (max n_max 2)) := hfit_n.of_le hlog_le
  set d1 := x.set regTmp 2
  have s1 : Exec w (.op (.const regTmp 2) : Code .exact 9) x d1 1 := Exec.const hfit_2
  set d2 := d1.set regPtr (max n_max 2)
  have s2 : Exec w (maxCode regPtr regKey regTmp) d1 d2 3 := by
    simpa +decide [d2, d1, hn] using maxCode_exec (w := w) regPtr regKey regTmp d1
  set d3 := d2.set regB 0
  have s3 : Exec w (.op (.const regB 0) : Code .exact 9) d2 d3 1 := Exec.const hfit_0
  set d4 := d3.set regTmp 1
  have s4 : Exec w (.op (.const regTmp 1) : Code .exact 9) d3 d4 1 := Exec.const hfit_1
  have slog0 := log2Loop_exec (w := w) (max n_max 2) (acc := 0) (x := d4.comap logMap9)
    (by simp +decide [d4, d3, d2, logMap9, Data.comap])
    (by simp +decide [d4, d3, logMap9, Data.comap])
    (by simp +decide [d4, logMap9, Data.comap])
    hfit_n (by simpa using hfit_log)
  have slog := slog0.rename injective_logMap9
  set d5 := (log2LoopData (max n_max 2) 0 (d4.comap logMap9)).extend logMap9 d4
  have hd5_b : d5.regs regB = Nat.log 2 (max n_max 2) := by
    change (d5.comap logMap9).regs 1 = Nat.log 2 (max n_max 2)
    rw [Data.comap_extend injective_logMap9]
    simp [log2LoopData]
  have hd5_tmp : d5.regs regTmp = 1 := by
    change (d5.comap logMap9).regs 2 = 1
    rw [Data.comap_extend injective_logMap9]
    simp +decide [log2LoopData, d4, logMap9, Data.comap]
  have hshr : Nat.log 2 (max n_max 2) >>> 1 = Nat.log 2 (max n_max 2) / 2 := by
    rw [Nat.shiftRight_eq_div_pow]
  have hfit_div : Fits w (Nat.log 2 (max n_max 2) / 2) :=
    hfit_log.of_le (Nat.div_le_self _ 2)
  set d6 := d5.set regB (Nat.log 2 (max n_max 2) / 2)
  have s6 : Exec w (.op (.exactBin .shiftRight regB regB regTmp) : Code .exact 9) d5 d6 1 :=
    exec_exactBin (by simp [hd5_b, hd5_tmp, hshr]) hfit_div
  set d7 := d6.set regB (charBits n_max)
  have hcb : max (Nat.log 2 (max n_max 2) / 2) 1 = charBits n_max := Nat.max_comm _ _
  have s7 : Exec w (maxCode regB regB regTmp) d6 d7 3 := by
    simpa +decide [d7, d6, hd5_tmp, hcb] using maxCode_exec (w := w) regB regB regTmp d6
  have hall := s1.seq (s2.seq (s3.seq (s4.seq (slog.seq (s6.seq s7)))))
  have hsteps : 1 + (3 + (1 + (1 + (4 * Nat.log 2 (max n_max 2) + 2 + (1 + 3))))) =
      4 * Nat.log 2 (max n_max 2) + 12 := by omega
  rw [hsteps] at hall
  have hbase_eq : d7.regs regBase = x.regs regBase := by
    simp +decide [d7, d6, d5, Data.extend, d4, d3, d2, d1]
  have hout_eq : d7.regs regOut = x.regs regOut := by
    simp +decide [d7, d6, d5, Data.extend, d4, d3, d2, d1]
  refine ⟨hall, by simp [charBitsData], hbase_eq, hout_eq, rfl⟩

/-- Deterministic 16-instruction setup prefix of `initFromBCode d`: writes the 4 header words
`(b, 2 ^ b, 2 ^ b - 1, 2 ^ M - 1)` to `base + 0 .. base + 3` and sets registers for
`randFillLoop.rename fillMap9` on `[base + 4, base + 4 + d * 2 ^ b)`. -/
@[expose] def setupFromBCode (d : ℕ) : Code .exact 9 :=
  .seq (.op (.store regBase regB))
  (.seq (.op (.const regTmp 1))
  (.seq (.op (.exactBin .shiftLeft regPowB regTmp regB))
  (.seq (.op (.exactBin .add regPtr regBase regTmp))
  (.seq (.op (.store regPtr regPowB))
  (.seq (.op (.exactBin .sub regMaskB regPowB regTmp))
  (.seq (.op (.exactBin .add regPtr regPtr regTmp))
  (.seq (.op (.store regPtr regMaskB))
  (.seq (.op (.exactBin .shiftLeft regEnd regTmp regOut))
  (.seq (.op (.exactBin .sub regEnd regEnd regTmp))
  (.seq (.op (.exactBin .add regPtr regPtr regTmp))
  (.seq (.op (.store regPtr regEnd))
  (.seq (.op (.exactBin .add regPtr regPtr regTmp))
  (.seq (.op (.const regB d))
  (.seq (.op (.exactBin .mul regB regB regPowB))
        (.op (.exactBin .add regB regPtr regB))))))))))))))))

/-- State after `setupFromBCode d`. -/
@[expose] def setupFromBData (base b d M : ℕ) (x : Data 9) : Data 9 :=
  let m0 := (((x.write base b).write (base + 1) (2 ^ b)).write
    (base + 2) (2 ^ b - 1)).write (base + 3) (2 ^ M - 1)
  ((((((m0.set regTmp 1).set regPowB (2 ^ b)).set regPtr (base + 1)).set
    regMaskB (2 ^ b - 1)).set regPtr (base + 2)).set regEnd (2 ^ M)).set
    regEnd (2 ^ M - 1) |>.set regPtr (base + 3) |>.set regPtr (base + 4) |>.set
    regB d |>.set regB (d * 2 ^ b) |>.set regB (base + 4 + d * 2 ^ b)

/-- `setupFromBCode d` executes in `16` deterministic steps. -/
theorem setupFromBCode_exec {w base b d M : ℕ} {x : Data 9}
    (hbase : x.regs regBase = base) (hb : x.regs regB = b) (hM : x.regs regOut = M)
    (hfit_space : Fits w (base + spaceFromB b d))
    (hfit_powB : Fits w (2 ^ b)) (hfit_powM : Fits w (2 ^ M)) (hfit_d : Fits w d) :
    Exec w (setupFromBCode d) x (setupFromBData base b d M x) 16 := by
  have h1_le_b : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have h1_le_M : 1 ≤ 2 ^ M := Nat.one_le_two_pow
  have hfit_1 : Fits w 1 := hfit_powB.of_le h1_le_b
  have hfit_maskB : Fits w (2 ^ b - 1) := hfit_powB.of_le (Nat.sub_le _ 1)
  have hfit_maskM : Fits w (2 ^ M - 1) := hfit_powM.of_le (Nat.sub_le _ 1)
  have hfit_b1 : Fits w (base + 1) := hfit_space.of_le (by simp [spaceFromB]; omega)
  have hfit_b2 : Fits w (base + 2) := hfit_space.of_le (by simp [spaceFromB]; omega)
  have hfit_b3 : Fits w (base + 3) := hfit_space.of_le (by simp [spaceFromB]; omega)
  have hfit_b4 : Fits w (base + 4) := hfit_space.of_le (by simp [spaceFromB])
  have hfit_dmul : Fits w (d * 2 ^ b) := hfit_space.of_le (by simp [spaceFromB]; omega)
  have hfit_end : Fits w (base + 4 + d * 2 ^ b) :=
    hfit_space.of_le (by simp [spaceFromB]; omega)
  set s0 := x.write base b
  have e1 : Exec w (.op (.store regBase regB) : Code .exact 9) x s0 1 := by
    simpa [s0, hbase, hb] using
      (Exec.store (B := .exact) (w := w) (a := regBase) (s := regB) (x := x))
  set s1 := s0.set regTmp 1
  have e2 : Exec w (.op (.const regTmp 1) : Code .exact 9) s0 s1 1 := Exec.const hfit_1
  set s2 := s1.set regPowB (2 ^ b)
  have e3 : Exec w (.op (.exactBin .shiftLeft regPowB regTmp regB) : Code .exact 9) s1 s2 1 :=
    exec_exactBin (by simp +decide [s1, s0, hb, Nat.shiftLeft_eq]) hfit_powB
  set s3 := s2.set regPtr (base + 1)
  have e4 : Exec w (.op (.exactBin .add regPtr regBase regTmp) : Code .exact 9) s2 s3 1 :=
    exec_exactBin (by simp +decide [s2, s1, s0, hbase]) hfit_b1
  set s4 := s3.write (base + 1) (2 ^ b)
  have e5 : Exec w (.op (.store regPtr regPowB) : Code .exact 9) s3 s4 1 := by
    simpa +decide [s4, s3, s2] using
      (Exec.store (B := .exact) (w := w) (a := regPtr) (s := regPowB) (x := s3))
  set s5 := s4.set regMaskB (2 ^ b - 1)
  have e6 : Exec w (.op (.exactBin .sub regMaskB regPowB regTmp) : Code .exact 9) s4 s5 1 :=
    exec_exactBin (by simp +decide [s4, s3, s2, s1, h1_le_b]) hfit_maskB
  set s6 := s5.set regPtr (base + 2)
  have e7 : Exec w (.op (.exactBin .add regPtr regPtr regTmp) : Code .exact 9) s5 s6 1 :=
    exec_exactBin (by simp +decide [s5, s4, s3, s2, s1]) hfit_b2
  set s7 := s6.write (base + 2) (2 ^ b - 1)
  have e8 : Exec w (.op (.store regPtr regMaskB) : Code .exact 9) s6 s7 1 := by
    simpa +decide [s7, s6, s5] using
      (Exec.store (B := .exact) (w := w) (a := regPtr) (s := regMaskB) (x := s6))
  set s8 := s7.set regEnd (2 ^ M)
  have e9 : Exec w (.op (.exactBin .shiftLeft regEnd regTmp regOut) : Code .exact 9) s7 s8 1 :=
    exec_exactBin (by simp +decide [s7, s6, s5, s4, s3, s2, s1, s0, hM, Nat.shiftLeft_eq]) hfit_powM
  set s9 := s8.set regEnd (2 ^ M - 1)
  have e10 : Exec w (.op (.exactBin .sub regEnd regEnd regTmp) : Code .exact 9) s8 s9 1 :=
    exec_exactBin (by simp +decide [s8, s7, s6, s5, s4, s3, s2, s1, h1_le_M]) hfit_maskM
  set s10 := s9.set regPtr (base + 3)
  have e11 : Exec w (.op (.exactBin .add regPtr regPtr regTmp) : Code .exact 9) s9 s10 1 :=
    exec_exactBin (by simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1]) hfit_b3
  set s11 := s10.write (base + 3) (2 ^ M - 1)
  have e12 : Exec w (.op (.store regPtr regEnd) : Code .exact 9) s10 s11 1 := by
    simpa +decide [s11, s10, s9] using
      (Exec.store (B := .exact) (w := w) (a := regPtr) (s := regEnd) (x := s10))
  set s12 := s11.set regPtr (base + 4)
  have e13 : Exec w (.op (.exactBin .add regPtr regPtr regTmp) : Code .exact 9) s11 s12 1 :=
    exec_exactBin (by simp +decide [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]) hfit_b4
  set s13 := s12.set regB d
  have e14 : Exec w (.op (.const regB d) : Code .exact 9) s12 s13 1 := Exec.const hfit_d
  set s14 := s13.set regB (d * 2 ^ b)
  have e15 : Exec w (.op (.exactBin .mul regB regB regPowB) : Code .exact 9) s13 s14 1 :=
    exec_exactBin (by simp +decide [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2]) hfit_dmul
  set s15 := s14.set regB (base + 4 + d * 2 ^ b)
  have e16 : Exec w (.op (.exactBin .add regB regPtr regB) : Code .exact 9) s14 s15 1 :=
    exec_exactBin (by simp +decide [s14, s13, s12]) hfit_end
  have hs15 : s15 = setupFromBData base b d M x := by
    ext i : 2
    · fin_cases i <;> rfl
    · rfl
  rw [hs15] at e16
  exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq
    (e9.seq (e10.seq (e11.seq (e12.seq (e13.seq (e14.seq (e15.seq e16))))))))))))))

/-- Structured Word-RAM program that initializes a `d`-character simple tabulation table from
`(base, M, b)` in `(regBase, regOut, regB)`. -/
@[expose] def initFromBCode (d : ℕ) : Code .exact 9 :=
  .seq (setupFromBCode d) (randFillLoop.rename fillMap9)

/-- Explicit `ProbComp (Data 9 × ℕ)` produced by `initFromBCode d`. -/
@[expose] noncomputable def initFromBComp (base b d M : ℕ) (x : Data 9) : ProbComp (Data 9 × ℕ) :=
  let s := setupFromBData base b d M x
  (fun z => (z.1.extend fillMap9 s, 16 + z.2)) <$>
    randFillComp M (base + 4) (d * 2 ^ b) (s.comap fillMap9)

/-- Exact `ExecRand` semantics of `initFromBCode d`. -/
theorem initFromBCode_execRand {w base b d M : ℕ} {x : Data 9}
    (hbase : x.regs regBase = base) (hb : x.regs regB = b) (hM : x.regs regOut = M)
    (hfit_space : Fits w (base + spaceFromB b d))
    (hfit_powB : Fits w (2 ^ b)) (hfit_powM : Fits w (2 ^ M)) (hfit_d : Fits w d) :
    ExecRand w (initFromBCode d) x (initFromBComp base b d M x) := by
  have hsetup := setupFromBCode_exec hbase hb hM hfit_space hfit_powB hfit_powM hfit_d
  set s := setupFromBData base b d M x
  have hloop0 := randFillLoop_execRand (w := w) (bits := M) (arrBase := base + 4)
    (d * 2 ^ b) (x := s.comap fillMap9)
    (by simp +decide [s, setupFromBData, fillMap9, Data.comap])
    (by simp +decide [s, setupFromBData, fillMap9, Data.comap])
    (by simp +decide [s, setupFromBData, fillMap9, Data.comap])
    (by simp +decide [s, setupFromBData, fillMap9, Data.comap])
    (hfit_space.of_le (by simp [spaceFromB]; omega))
    (hfit_powM.of_le (Nat.sub_le _ 1))
  have hloop := hloop0.rename injective_fillMap9
  have hseq := hsetup.seqRand hloop
  have heq : ((fun z => (z.1, 16 + z.2)) <$>
      ((fun z => (z.1.extend fillMap9 s, z.2)) <$>
        randFillComp M (base + 4) (d * 2 ^ b) (s.comap fillMap9))) =
      initFromBComp base b d M x := by
    simp [initFromBComp, s, Functor.map_map]
  rwa [heq] at hseq

/-- The character table `extractTable base b d M z.1.mem` produced by `initFromBComp` is uniformly
distributed over `Fin (d * 2 ^ b) → Fin (2 ^ M)`. -/
theorem map_extractTable_eval_initFromBComp (base b d M : ℕ) (x : Data 9) :
    ((initFromBComp base b d M x).eval).map (fun z => extractTable base b d M z.1.mem) =
      PMF.uniformOfFintype (Fin (d * 2 ^ b) → Fin (2 ^ M)) := by
  dsimp only [initFromBComp, extractTable]
  rw [ProbComp.eval_map, PMF.map_comp]
  exact map_extractSlice_eval_randFillComp M (base + 4) (d * 2 ^ b)
    ((setupFromBData base b d M x).comap fillMap9)

/-- Self-contained `initCode d` that computes `b = charBits n_max` from `n_max` in `regKey` and
initializes the `d`-character simple tabulation table at `base` (`regBase`) with `M`-bit entries
(`regOut = M`). -/
@[expose] def initCode (d : ℕ) : Code .exact 9 :=
  .seq charBitsCode (initFromBCode d)

/-- Pathwise postcondition of `initFromBComp`: runs in `5 * (d * 2 ^ b) + 18` instructions and
establishes `Rep base b d M (extractTable base b d M z.1.mem) z.1.mem`, `z.1.regs regBase = base`,
and frame preservation outside `[base, base + spaceFromB b d)`. -/
theorem mem_support_initFromBComp {base b d M : ℕ} {x : Data 9} {z : Data 9 × ℕ}
    (hbase : x.regs regBase = base)
    (hz : z ∈ (initFromBComp base b d M x).support) :
    z.2 = 5 * (d * 2 ^ b) + 18 ∧
    Rep base b d M (extractTable base b d M z.1.mem) z.1.mem ∧
    z.1.regs regBase = base ∧
    (∀ a, (a < base ∨ base + spaceFromB b d ≤ a) → z.1.mem a = x.mem a) := by
  dsimp only [initFromBComp] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  obtain ⟨hsteps, -, -, -, -, hextra, hlt, hframe⟩ := mem_support_randFillComp hz₀
  set s := setupFromBData base b d M x
  have hmem0 : z₀.1.mem base = b := by
    rw [hframe base (Or.inl (by omega))]
    simp +decide [s, setupFromBData, Data.comap, Data.write, Function.update_of_ne]
  have hmem1 : z₀.1.mem (base + 1) = 2 ^ b := by
    rw [hframe (base + 1) (Or.inl (by omega))]
    simp +decide [s, setupFromBData, Data.comap, Data.write, Function.update_of_ne]
  have hmem2 : z₀.1.mem (base + 2) = 2 ^ b - 1 := by
    rw [hframe (base + 2) (Or.inl (by omega))]
    simp +decide [s, setupFromBData, Data.comap, Data.write, Function.update_of_ne]
  have hmem3 : z₀.1.mem (base + 3) = 2 ^ M - 1 := by
    rw [hframe (base + 3) (Or.inl (by omega))]
    simp +decide [s, setupFromBData, Data.comap, Data.write]
  have hrep : Rep base b d M (extractTable base b d M z₀.1.mem) z₀.1.mem := by
    refine ⟨hmem0, hmem1, hmem2, hmem3, fun i => ?_⟩
    simp [extractTable, extractSlice, hlt i.val i.isLt]
  have hbase' : (z₀.1.extend fillMap9 s).regs regBase = base := by
    change ((z₀.1.extend fillMap9 s).comap fillMap9).regs regExtra = base
    rw [Data.comap_extend injective_fillMap9, hextra]
    simpa +decide [s, setupFromBData, fillMap9, Data.comap] using hbase
  have hframe' : ∀ a, (a < base ∨ base + spaceFromB b d ≤ a) → z₀.1.mem a = x.mem a := by
    intro a ha
    have ha4 : a < base + 4 ∨ base + 4 + d * 2 ^ b ≤ a := by
      simp only [spaceFromB] at ha
      omega
    rw [hframe a ha4]
    have hne0 : a ≠ base := by simp only [spaceFromB] at ha; omega
    have hne1 : a ≠ base + 1 := by simp only [spaceFromB] at ha; omega
    have hne2 : a ≠ base + 2 := by simp only [spaceFromB] at ha; omega
    have hne3 : a ≠ base + 3 := by simp only [spaceFromB] at ha; omega
    simp [s, setupFromBData, Data.comap, Data.write,
      Function.update_of_ne hne0, Function.update_of_ne hne1,
      Function.update_of_ne hne2, Function.update_of_ne hne3]
  exact ⟨by omega, hrep, hbase', hframe'⟩

/-- Hoare-style `ExecRandWithin` specification for `initFromBCode d`. -/
theorem initFromBCode_execRandWithin {w base b d M : ℕ} {x : Data 9}
    (hbase : x.regs regBase = base) (hb : x.regs regB = b) (hM : x.regs regOut = M)
    (hfit_space : Fits w (base + spaceFromB b d))
    (hfit_powB : Fits w (2 ^ b)) (hfit_powM : Fits w (2 ^ M)) (hfit_d : Fits w d) :
    ExecRandWithin w (initFromBCode d) x
      (fun y => Rep base b d M (extractTable base b d M y.mem) y.mem ∧
        y.regs regBase = base ∧
        (∀ a, (a < base ∨ base + spaceFromB b d ≤ a) → y.mem a = x.mem a))
      (5 * (d * 2 ^ b) + 18) (d * 2 ^ b) := by
  refine ⟨initFromBComp base b d M x,
    initFromBCode_execRand hbase hb hM hfit_space hfit_powB hfit_powM hfit_d, ?_, ?_⟩
  · dsimp only [initFromBComp]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      (isQueryBounded_randFillComp M (base + 4) (d * 2 ^ b) _)
  · intro z hz
    obtain ⟨hsteps, hrep, hbase', hframe'⟩ := mem_support_initFromBComp hbase hz
    exact ⟨⟨hrep, hbase', hframe'⟩, by omega⟩

/-- Explicit `ProbComp (Data 9 × ℕ)` produced by `initCode d` from `(base, n_max, M)`. -/
@[expose] noncomputable def initComp (base n_max d M : ℕ) (x : Data 9) : ProbComp (Data 9 × ℕ) :=
  (fun z => (z.1, (4 * Nat.log 2 (max n_max 2) + 12) + z.2)) <$>
    initFromBComp base (charBits n_max) d M (charBitsData n_max x)

/-- Exact `ExecRand` semantics of `initCode d`. -/
theorem initCode_execRand {w base n_max d M : ℕ} {x : Data 9}
    (hbase : x.regs regBase = base) (hn : x.regs regKey = n_max) (hM : x.regs regOut = M)
    (hfit_n : Fits w (max n_max 2))
    (hfit_space : Fits w (base + space n_max d))
    (hfit_powM : Fits w (2 ^ M)) (hfit_d : Fits w d) :
    ExecRand w (initCode d) x (initComp base n_max d M x) := by
  obtain ⟨hcb, hb_eq, hbase_eq, hout_eq, _⟩ := charBitsCode_exec (w := w) hn hfit_n
  have hfit_powB : Fits w (2 ^ charBits n_max) := by
    have hle := two_pow_charBits_le n_max
    rw [Nat.max_comm 2 n_max] at hle
    exact hfit_n.of_le hle
  have hinit := initFromBCode_execRand
    (hbase_eq.trans hbase) hb_eq (hout_eq.trans hM) hfit_space hfit_powB hfit_powM hfit_d
  exact hcb.seqRand hinit

/-- **Uniformity of `TabulatedOddStride.initComp`**: the character table extracted from final
memory has the exact uniform distribution over `Fin (d * 2 ^ (charBits n_max)) → Fin (2 ^ M)`. -/
theorem map_extractTable_eval_initComp (base n_max d M : ℕ) (x : Data 9) :
    ((initComp base n_max d M x).eval).map
        (fun z => extractTable base (charBits n_max) d M z.1.mem) =
      PMF.uniformOfFintype (Fin (d * 2 ^ (charBits n_max)) → Fin (2 ^ M)) := by
  dsimp only [initComp]
  rw [ProbComp.eval_map, PMF.map_comp]
  exact map_extractTable_eval_initFromBComp base (charBits n_max) d M (charBitsData n_max x)

/-- Hoare-style `ExecRandWithin` specification for `TabulatedOddStride.initCode d`. -/
theorem initCode_execRandWithin {w base n_max d M : ℕ} {x : Data 9}
    (hbase : x.regs regBase = base) (hn : x.regs regKey = n_max) (hM : x.regs regOut = M)
    (hfit_n : Fits w (max n_max 2))
    (hfit_space : Fits w (base + space n_max d))
    (hfit_powM : Fits w (2 ^ M)) (hfit_d : Fits w d) :
    ExecRandWithin w (initCode d) x
      (fun y =>
        Rep base (charBits n_max) d M (extractTable base (charBits n_max) d M y.mem) y.mem ∧
        y.regs regBase = base ∧
        (∀ a, (a < base ∨ base + space n_max d ≤ a) → y.mem a = x.mem a))
      (4 * Nat.log 2 (max n_max 2) + 5 * (d * 2 ^ (charBits n_max)) + 30)
      (d * 2 ^ (charBits n_max)) := by
  refine ⟨initComp base n_max d M x,
    initCode_execRand hbase hn hM hfit_n hfit_space hfit_powM hfit_d, ?_, ?_⟩
  · dsimp only [initComp, initFromBComp]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.isCostBounded_map_iff _ _ _).mpr
        (isQueryBounded_randFillComp M (base + 4) (d * 2 ^ (charBits n_max)) _))
  · intro z hz
    dsimp only [initComp] at hz
    obtain ⟨z₁, hz₁, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    obtain ⟨-, -, hbase_cb, -, hmem_cb⟩ := charBitsCode_exec (w := w) hn hfit_n
    obtain ⟨hsteps, hrep, hbase', hframe'⟩ :=
      mem_support_initFromBComp (hbase_cb.trans hbase) hz₁
    refine ⟨⟨hrep, hbase', fun a ha => ?_⟩, by omega⟩
    rw [hframe' a ha, hmem_cb]

/-- 12-instruction deterministic setup before `tabLoop` in `evalCode d`: loads `b`, `2 ^ b`,
`2 ^ b - 1` from `base + 0 .. base + 2`, sets `regPtr = base + 4` and
`regEnd = base + 4 + d * 2 ^ b`, and zeros `regOut`. -/
@[expose] def evalSetupCode (d : ℕ) : Code .exact 9 :=
  .seq (.op (.load regB regBase))
  (.seq (.op (.const regTmp 1))
  (.seq (.op (.exactBin .add regPtr regBase regTmp))
  (.seq (.op (.load regPowB regPtr))
  (.seq (.op (.exactBin .add regPtr regPtr regTmp))
  (.seq (.op (.load regMaskB regPtr))
  (.seq (.op (.const regOut 2))
  (.seq (.op (.exactBin .add regPtr regPtr regOut))
  (.seq (.op (.const regOut d))
  (.seq (.op (.exactBin .mul regEnd regOut regPowB))
  (.seq (.op (.exactBin .add regEnd regPtr regEnd))
        (.op (.const regOut 0))))))))))))

/-- State after `evalSetupCode d`. -/
@[expose] def evalSetupData (base b d : ℕ) (x : Data 9) : Data 9 :=
  (((((((((((x.set regB b).set regTmp 1).set regPtr (base + 1)).set
    regPowB (2 ^ b)).set regPtr (base + 2)).set regMaskB (2 ^ b - 1)).set
    regOut 2).set regPtr (base + 4)).set regOut d).set regEnd (d * 2 ^ b)).set
    regEnd (base + 4 + d * 2 ^ b)).set regOut 0

/-- `evalSetupCode d` executes in `12` deterministic steps when `Rep base b d M T x.mem` holds. -/
theorem evalSetupCode_exec {w base b d M : ℕ} {T : Fin (d * 2 ^ b) → Fin (2 ^ M)} {x : Data 9}
    (hrep : Rep base b d M T x.mem) (hbase : x.regs regBase = base)
    (hfit_space : Fits w (base + spaceFromB b d)) (hfit_d : Fits w d) :
    Exec w (evalSetupCode d) x (evalSetupData base b d x) 12 := by
  obtain ⟨hm0, hm1, hm2, -, -⟩ := hrep
  have hfit_2 : Fits w 2 := hfit_space.of_le (by simp [spaceFromB]; omega)
  have hfit_1 : Fits w 1 := hfit_2.of_le (by decide)
  have hfit_0 : Fits w 0 := hfit_1.of_le (by decide)
  have hfit_b1 : Fits w (base + 1) := hfit_space.of_le (by simp [spaceFromB]; omega)
  have hfit_b2 : Fits w (base + 2) := hfit_space.of_le (by simp [spaceFromB]; omega)
  have hfit_b4 : Fits w (base + 4) := hfit_space.of_le (by simp [spaceFromB])
  have hfit_dmul : Fits w (d * 2 ^ b) := hfit_space.of_le (by simp [spaceFromB]; omega)
  have hfit_end : Fits w (base + 4 + d * 2 ^ b) := hfit_space.of_le (by simp [spaceFromB]; omega)
  set s0 := x.set regB b
  have e1 : Exec w (.op (.load regB regBase) : Code .exact 9) x s0 1 := by
    simpa [s0, hbase, hm0] using
      (Exec.load (B := .exact) (w := w) (d := regB) (a := regBase) (x := x))
  set s1 := s0.set regTmp 1
  have e2 : Exec w (.op (.const regTmp 1) : Code .exact 9) s0 s1 1 := Exec.const hfit_1
  set s2 := s1.set regPtr (base + 1)
  have e3 : Exec w (.op (.exactBin .add regPtr regBase regTmp) : Code .exact 9) s1 s2 1 :=
    exec_exactBin (by simp +decide [s1, s0, hbase]) hfit_b1
  set s3 := s2.set regPowB (2 ^ b)
  have e4 : Exec w (.op (.load regPowB regPtr) : Code .exact 9) s2 s3 1 := by
    simpa +decide [s3, s2, s1, s0, hm1] using
      (Exec.load (B := .exact) (w := w) (d := regPowB) (a := regPtr) (x := s2))
  set s4 := s3.set regPtr (base + 2)
  have e5 : Exec w (.op (.exactBin .add regPtr regPtr regTmp) : Code .exact 9) s3 s4 1 :=
    exec_exactBin (by simp +decide [s3, s2, s1]) hfit_b2
  set s5 := s4.set regMaskB (2 ^ b - 1)
  have e6 : Exec w (.op (.load regMaskB regPtr) : Code .exact 9) s4 s5 1 := by
    simpa +decide [s5, s4, s3, s2, s1, s0, hm2] using
      (Exec.load (B := .exact) (w := w) (d := regMaskB) (a := regPtr) (x := s4))
  set s6 := s5.set regOut 2
  have e7 : Exec w (.op (.const regOut 2) : Code .exact 9) s5 s6 1 := Exec.const hfit_2
  set s7 := s6.set regPtr (base + 4)
  have e8 : Exec w (.op (.exactBin .add regPtr regPtr regOut) : Code .exact 9) s6 s7 1 :=
    exec_exactBin (by simp +decide [s6, s5, s4]) hfit_b4
  set s8 := s7.set regOut d
  have e9 : Exec w (.op (.const regOut d) : Code .exact 9) s7 s8 1 := Exec.const hfit_d
  set s9 := s8.set regEnd (d * 2 ^ b)
  have e10 : Exec w (.op (.exactBin .mul regEnd regOut regPowB) : Code .exact 9) s8 s9 1 :=
    exec_exactBin (by simp +decide [s8, s7, s6, s5, s4, s3]) hfit_dmul
  set s10 := s9.set regEnd (base + 4 + d * 2 ^ b)
  have e11 : Exec w (.op (.exactBin .add regEnd regPtr regEnd) : Code .exact 9) s9 s10 1 :=
    exec_exactBin (by simp +decide [s9, s8, s7]) hfit_end
  set s11 := s10.set regOut 0
  have e12 : Exec w (.op (.const regOut 0) : Code .exact 9) s10 s11 1 := Exec.const hfit_0
  exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq
    (e7.seq (e8.seq (e9.seq (e10.seq (e11.seq e12))))))))))

/-- Body of `tabLoop` (6 instructions): extracts `ch = regKey &&& regMaskB`, loads
`T[regPtr + ch]`, XORs into `regOut`, shifts `regKey` right by `regB`, and advances `regPtr` by
`regPowB`. -/
@[expose] def tabBody : Code .exact 9 :=
  .seq (.op (.exactBin .and regTmp regKey regMaskB))
  (.seq (.op (.exactBin .add regTmp regPtr regTmp))
  (.seq (.op (.load regTmp regTmp))
  (.seq (.op (.exactBin .xor regOut regOut regTmp))
  (.seq (.op (.exactBin .shiftRight regKey regKey regB))
        (.op (.exactBin .add regPtr regPtr regPowB))))))

/-- Loop over the `d` character tables `[base + 4, base + 4 + d * 2 ^ b)`. -/
@[expose] def tabLoop : Code .exact 9 :=
  .loop (.lt regPtr regEnd) tabBody

/-- `tabLoop` executes deterministically in `8 * rem + 2` instructions from character offset `j`
with `j + rem = d`, accumulating `(simpleTabAux b d M T rem j u acc).val` into `regOut` and
preserving `regBase` and all memory. -/
theorem tabLoop_exec {w base b d M : ℕ} {T : Fin (d * 2 ^ b) → Fin (2 ^ M)} {x : Data 9}
    (hrep : Rep base b d M T x.mem)
    (hfit_space : Fits w (base + spaceFromB b d)) (hfit_powM : Fits w (2 ^ M)) :
    ∀ (rem j u : ℕ) (acc : Fin (2 ^ M)) (d0 : Data 9),
      j + rem = d →
      d0.mem = x.mem →
      d0.regs regBase = base →
      d0.regs regPtr = base + 4 + j * 2 ^ b →
      d0.regs regEnd = base + 4 + d * 2 ^ b →
      d0.regs regB = b →
      d0.regs regPowB = 2 ^ b →
      d0.regs regMaskB = 2 ^ b - 1 →
      d0.regs regKey = u →
      d0.regs regOut = acc.val →
      Fits w u →
      ∃ y : Data 9,
        Exec w tabLoop d0 y (8 * rem + 2) ∧
        y.regs regOut = (simpleTabAux b d M T rem j u acc).val ∧
        y.regs regBase = base ∧
        y.mem = x.mem := by
  intro rem
  induction rem with
  | zero =>
    intro j u acc d0 hj hmem hbase hptr hend _ _ _ _ hout _
    have hj_eq : j = d := by omega
    have hc : ¬(Cond.lt regPtr regEnd).Holds d0 := by
      simp [Cond.Holds, hptr, hend, hj_eq]
    exact ⟨d0, Exec.loop_exit hc, by simp [simpleTabAux, hout], hbase, hmem⟩
  | succ rem ih =>
    intro j u acc d0 hj hmem hbase hptr hend hb hpowB hmaskB hkey hout hfit_u
    have hj_lt : j < d := by omega
    have hpow_pos : 0 < 2 ^ b := Nat.two_pow_pos b
    have hj_mul_lt : j * 2 ^ b < d * 2 ^ b := Nat.mul_lt_mul_of_pos_right hj_lt hpow_pos
    have hc : (Cond.lt regPtr regEnd).Holds d0 := by
      simp only [Cond.Holds, hptr, hend]
      omega
    set ch := u &&& (2 ^ b - 1)
    have hch_lt : ch < 2 ^ b := by
      dsimp only [ch]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt u hpow_pos
    set idx := j * 2 ^ b + ch
    have hidx_lt : idx < d * 2 ^ b := by
      have : (j + 1) * 2 ^ b ≤ d * 2 ^ b := Nat.mul_le_mul_right (2 ^ b) (by omega)
      calc
        idx < j * 2 ^ b + 2 ^ b := by omega
        _ = (j + 1) * 2 ^ b := by ring
        _ ≤ d * 2 ^ b := this
    set entry := (T ⟨idx, hidx_lt⟩).val
    have hentry_mem : d0.mem (base + 4 + j * 2 ^ b + ch) = entry := by
      rw [hmem, show base + 4 + j * 2 ^ b + ch = base + 4 + idx by omega]
      exact hrep.2.2.2.2 ⟨idx, hidx_lt⟩
    set newAcc : Fin (2 ^ M) :=
      ⟨acc.val ^^^ entry, Nat.xor_lt_two_pow acc.isLt (T ⟨idx, hidx_lt⟩).isLt⟩
    have hfit_ch : Fits w ch := hfit_u.of_le Nat.and_le_left
    have hfit_addr : Fits w (base + 4 + j * 2 ^ b + ch) :=
      hfit_space.of_le (by simp [spaceFromB]; omega)
    have hfit_xor : Fits w newAcc.val := hfit_powM.of_le (le_of_lt newAcc.isLt)
    have hfit_shr : Fits w (u >>> b) := hfit_u.of_le (Nat.shiftRight_le u b)
    have hnext_eq : base + 4 + j * 2 ^ b + 2 ^ b = base + 4 + (j + 1) * 2 ^ b := by ring
    have hfit_next : Fits w (base + 4 + j * 2 ^ b + 2 ^ b) := by
      have : (j + 1) * 2 ^ b ≤ d * 2 ^ b := Nat.mul_le_mul_right (2 ^ b) (by omega)
      exact hfit_space.of_le (by simp [spaceFromB]; omega)
    set s1 := d0.set regTmp ch
    have e1 : Exec w (.op (.exactBin .and regTmp regKey regMaskB) : Code .exact 9) d0 s1 1 :=
      exec_exactBin (by simp [hkey, hmaskB, ch]) hfit_ch
    set s2 := s1.set regTmp (base + 4 + j * 2 ^ b + ch)
    have e2 : Exec w (.op (.exactBin .add regTmp regPtr regTmp) : Code .exact 9) s1 s2 1 :=
      exec_exactBin (by simp +decide [s1, hptr]) hfit_addr
    set s3 := s2.set regTmp entry
    have e3 : Exec w (.op (.load regTmp regTmp) : Code .exact 9) s2 s3 1 := by
      simpa +decide [s3, s2, s1, hentry_mem] using
        (Exec.load (B := .exact) (w := w) (d := regTmp) (a := regTmp) (x := s2))
    set s4 := s3.set regOut newAcc.val
    have e4 : Exec w (.op (.exactBin .xor regOut regOut regTmp) : Code .exact 9) s3 s4 1 :=
      exec_exactBin (by simp +decide [s3, s2, s1, hout, newAcc]) hfit_xor
    set s5 := s4.set regKey (u >>> b)
    have e5 : Exec w (.op (.exactBin .shiftRight regKey regKey regB) : Code .exact 9) s4 s5 1 :=
      exec_exactBin (by simp +decide [s4, s3, s2, s1, hkey, hb]) hfit_shr
    set s6 := s5.set regPtr (base + 4 + j * 2 ^ b + 2 ^ b)
    have e6 : Exec w (.op (.exactBin .add regPtr regPtr regPowB) : Code .exact 9) s5 s6 1 :=
      exec_exactBin (by simp +decide [s5, s4, s3, s2, s1, hptr, hpowB]) hfit_next
    have hbody := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))
    obtain ⟨y, hrec, hy_out, hy_base, hy_mem⟩ :=
      ih (j + 1) (u >>> b) newAcc s6 (by omega) hmem
        (by simp +decide [s6, s5, s4, s3, s2, s1, hbase])
        (by simp +decide [s6, hnext_eq])
        (by simp +decide [s6, s5, s4, s3, s2, s1, hend])
        (by simp +decide [s6, s5, s4, s3, s2, s1, hb])
        (by simp +decide [s6, s5, s4, s3, s2, s1, hpowB])
        (by simp +decide [s6, s5, s4, s3, s2, s1, hmaskB])
        (by simp +decide [s6, s5])
        (by simp +decide [s6, s5, s4])
        hfit_shr
    have hiter := Exec.loop_iter hc hbody hrec
    refine ⟨y, ?_, ?_, hy_base, hy_mem⟩
    · simpa only [tabLoop, tabBody,
        show 1 + (1 + (1 + (1 + (1 + 1)))) + (8 * rem + 2) + 2 = 8 * (rem + 1) + 2 by omega]
        using hiter
    · rw [hy_out]
      simp only [simpleTabAux, ch, idx, hidx_lt, ↓reduceDIte, entry, newAcc]

/-- 7-instruction finishing suffix of `evalCode d`: loads `2 ^ M - 1` from `base + 3` and maps
`acc` in `regOut` to `(2 * acc + 1) &&& (2 ^ M - 1)`. -/
@[expose] def evalFinishCode : Code .exact 9 :=
  .seq (.op (.const regTmp 3))
  (.seq (.op (.exactBin .add regTmp regBase regTmp))
  (.seq (.op (.load regTmp regTmp))
  (.seq (.op (.exactBin .add regOut regOut regOut))
  (.seq (.op (.const regB 1))
  (.seq (.op (.exactBin .add regOut regOut regB))
        (.op (.exactBin .and regOut regOut regTmp)))))))

/-- Complete `d`-character simple tabulation odd-stride evaluation program `evalCode d`. -/
@[expose] def evalCode (d : ℕ) : Code .exact 9 :=
  .seq (evalSetupCode d) (.seq tabLoop evalFinishCode)

/-- **`TabulatedOddStride.evalCode d` correctness and complexity**: for any character table
`T : Fin (d * 2 ^ b) → Fin (2 ^ M)` represented at `base` and key `u` with `Fits w u`,
`evalCode d` halts deterministically in `8 * d + 21 = O(d)` instructions, preserving `regBase`
and all memory and writing `(tabulatedOddStride b d M T u).val` into `regOut`. -/
theorem evalCode_execWithin {w base b d M u : ℕ} {T : Fin (d * 2 ^ b) → Fin (2 ^ M)} {x : Data 9}
    (hrep : Rep base b d M T x.mem)
    (hbase : x.regs regBase = base) (hu : x.regs regKey = u)
    (hfit_space : Fits w (base + spaceFromB b d))
    (hfit_powM : Fits w (2 * 2 ^ M)) (hfit_d : Fits w d) (hfit_u : Fits w u) :
    ∃ y : Data 9,
      ExecWithin w (evalCode d) x y (8 * d + 21) ∧
      y.regs regOut = (tabulatedOddStride b d M T u).val ∧
      y.regs regBase = base ∧
      y.mem = x.mem := by
  have hfit_M : Fits w (2 ^ M) := hfit_powM.of_le (by omega)
  have hsetup := evalSetupCode_exec hrep hbase hfit_space hfit_d
  set d0 := evalSetupData base b d x
  obtain ⟨yLoop, hloop, hy_out, hy_base, hy_mem⟩ :=
    tabLoop_exec hrep hfit_space hfit_M d 0 u ⟨0, Nat.two_pow_pos M⟩ d0
      (by omega) rfl
      (by simp +decide [d0, evalSetupData, hbase])
      (by simp +decide [d0, evalSetupData])
      (by simp +decide [d0, evalSetupData])
      (by simp +decide [d0, evalSetupData])
      (by simp +decide [d0, evalSetupData])
      (by simp +decide [d0, evalSetupData])
      (by simp +decide [d0, evalSetupData, hu])
      (by simp +decide [d0, evalSetupData])
      hfit_u
  set tab := simpleTab b d M T u
  have htab_eq : yLoop.regs regOut = tab.val := hy_out
  have hfit_3 : Fits w 3 := hfit_space.of_le (by simp [spaceFromB]; omega)
  have hfit_b3 : Fits w (base + 3) := hfit_space.of_le (by simp [spaceFromB]; omega)
  have hfit_1 : Fits w 1 := hfit_space.of_le (by simp [spaceFromB]; omega)
  have hfit_2tab : Fits w (tab.val + tab.val) :=
    hfit_powM.of_le (by have := tab.isLt; omega)
  have hfit_2tab1 : Fits w (tab.val + tab.val + 1) :=
    hfit_powM.of_le (by have := tab.isLt; omega)
  have hfit_and : Fits w ((tab.val + tab.val + 1) &&& (2 ^ M - 1)) :=
    hfit_2tab1.of_le Nat.and_le_left
  have hm3 : yLoop.mem (base + 3) = 2 ^ M - 1 := by rw [hy_mem]; exact hrep.2.2.2.1
  set f1 := yLoop.set regTmp 3
  have e1 : Exec w (.op (.const regTmp 3) : Code .exact 9) yLoop f1 1 := Exec.const hfit_3
  set f2 := f1.set regTmp (base + 3)
  have e2 : Exec w (.op (.exactBin .add regTmp regBase regTmp) : Code .exact 9) f1 f2 1 :=
    exec_exactBin (by simp +decide [f1, hy_base]) hfit_b3
  set f3 := f2.set regTmp (2 ^ M - 1)
  have e3 : Exec w (.op (.load regTmp regTmp) : Code .exact 9) f2 f3 1 := by
    simpa +decide [f3, f2, f1, hm3] using
      (Exec.load (B := .exact) (w := w) (d := regTmp) (a := regTmp) (x := f2))
  set f4 := f3.set regOut (tab.val + tab.val)
  have e4 : Exec w (.op (.exactBin .add regOut regOut regOut) : Code .exact 9) f3 f4 1 :=
    exec_exactBin (by simp +decide [f3, f2, f1, htab_eq]) hfit_2tab
  set f5 := f4.set regB 1
  have e5 : Exec w (.op (.const regB 1) : Code .exact 9) f4 f5 1 := Exec.const hfit_1
  set f6 := f5.set regOut (tab.val + tab.val + 1)
  have e6 : Exec w (.op (.exactBin .add regOut regOut regB) : Code .exact 9) f5 f6 1 :=
    exec_exactBin (by simp +decide [f5, f4]) hfit_2tab1
  set f7 := f6.set regOut ((tab.val + tab.val + 1) &&& (2 ^ M - 1))
  have e7 : Exec w (.op (.exactBin .and regOut regOut regTmp) : Code .exact 9) f6 f7 1 :=
    exec_exactBin (by simp +decide [f6, f5, f4, f3]) hfit_and
  have hfin := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))
  have hall := hsetup.seq (hloop.seq hfin)
  refine ⟨f7, ⟨12 + (8 * d + 2 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))), by omega, hall⟩,
    ?_, by simp +decide [f7, f6, f5, f4, f3, f2, f1, hy_base], hy_mem⟩
  simp +decide [f7, tabulatedOddStride, oddStride, tab, Nat.two_mul]

end TabulatedOddStride

end Cslib.Algorithms.WordRAM.Hashing.Tabulation
