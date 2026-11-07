/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Languages.Probabilistic.QueryCount.Expected
public import Mathlib.InformationTheory.Hamming

/-!
# Locally decodable codes

A code `C : (ι → Bool) → P → Γ` encodes messages, bit strings indexed by `ι`, as words over the
alphabet `Γ` indexed by the positions `P`. A **local decoder** `A : LocalDecoder ι P Γ` is, for
each message index `i`, a program with private coins (`ProbOracleComp`) that queries positions of
a received word and guesses the bit `i` of the message. The queries are genuine oracle calls, so
the decoder may be adaptive, and its query budget is the library's
`ProbOracleComp.IsQueryBounded`: on every path, whatever its coins and the symbols read.

* `IsLocalDecoder C q δ ε A`: `A` makes at most `q` queries and, from every word `y` within
  Hamming distance `δ |P|` of the codeword `C x`, outputs each bit `x i` with probability at least
  `1 / 2 + ε` [KatzTrevisan2000][KerenidisDeWolf2004][Yekhanin2012].
* `IsSmoothDecoder C q c ε A`: `A` makes at most `q` queries, decodes the codewords themselves with
  probability at least `1 / 2 + ε`, and on codewords reads each position at most `c / |P|` times
  in expectation (`Code.expectedReads`, an `OracleComp.expectedCost`). Since a position read is
  read at least once, this bounds the probability of reading it by `c / |P|` as well, so it implies
  the smoothness of Katz and Trevisan [KatzTrevisan2000][KerenidisDeWolf2004]; for
  non-adaptive decoders whose queries are distinct the two coincide.

The received word is the oracle: `Code.decodeLaw program y` answers the private coins uniformly
and each query `j` by `y j`. A decoder whose expected reads do not depend on the received word
has oblivious reads (`Code.HasObliviousReads`); every non-adaptive decoder
(`Code.nonadaptive`), which draws its queries and its decision rule before reading anything, is
one (`Code.hasObliviousReads_nonadaptive`).

## Main definitions

* `Cslib.Code.LocalDecoder`: decoders querying a received word.
* `Cslib.Code.decodeLaw`, `Cslib.Code.expectedReads`: the output distribution and the expected
  number of reads of a position, against a received word.
* `Cslib.Code.IsLocalDecoder`, `Cslib.Code.IsLocallyDecodable`: `(q, δ, ε)` local decoding.
* `Cslib.Code.IsSmoothDecoder`, `Cslib.Code.IsSmoothCode`: `(q, c, ε)` smooth decoding.
* `Cslib.Code.HasObliviousReads`: reads that do not depend on the received word.
* `Cslib.Code.readAll`, `Cslib.Code.nonadaptive`: non-adaptive decoders.

## Main results

* `Cslib.Code.sum_expectedReads_le`: a decoder making `q` queries reads `q` positions in
  expectation.
* `Cslib.Code.decodeLaw_nonadaptive`, `Cslib.Code.expectedReads_nonadaptive`: the output law and
  the reads of a non-adaptive decoder.
* `Cslib.Code.expectedReads_nonadaptive_of_uniform`: a non-adaptive decoder whose queries are each
  uniform reads every position `q / |P|` times in expectation.

## References

* [J. Katz, L. Trevisan, *On the efficiency of local decoding procedures for error-correcting
  codes*][KatzTrevisan2000]
* [I. Kerenidis, R. de Wolf, *Exponential lower bound for 2-query locally decodable codes via a
  quantum argument*][KerenidisDeWolf2004]
* [S. Yekhanin, *Locally decodable codes*][Yekhanin2012]
-/

public section

open scoped ENNReal

namespace Cslib.Code

open OracleComp ProbOracleComp Probability

/-- A local decoder for messages indexed by `ι` from words over the alphabet `Γ` indexed by the
positions `P`: for each message index `i`, a program with private coins that queries positions of
the received word and guesses the bit `i` of the message. -/
abbrev LocalDecoder (ι P Γ : Type) := ι → ProbOracleComp (fun _ : P => Γ) Bool

variable {ι P Γ α : Type}

/-- The handler answering private coins uniformly and a query of the position `j` by `y j`. -/
noncomputable abbrev wordOracle (y : P → Γ) :
    (q : ℕ ⊕ P) → PMF (probOracleSpec (fun _ : P => Γ) q) :=
  sumHandler ProbComp.unifOracle fun j => PMF.pure (y j)

/-- The output distribution of a program with private coins run against the received word `y`. -/
noncomputable def decodeLaw (program : ProbOracleComp (fun _ : P => Γ) α) (y : P → Γ) : PMF α :=
  evalWith (wordOracle y) program

/-- The cost of a call that reads the position `j`; private coins are free. -/
def readCost [DecidableEq P] (j : P) : ℕ ⊕ P → ℝ≥0∞ :=
  Sum.elim 0 fun j' => if j' = j then 1 else 0

/-- The expected number of times `program`, run against the received word `y`, reads the
position `j`. -/
noncomputable def expectedReads [DecidableEq P] (program : ProbOracleComp (fun _ : P => Γ) α)
    (y : P → Γ) (j : P) : ℝ≥0∞ :=
  expectedCost (wordOracle y) (readCost j) program

@[simp] theorem readCost_inl [DecidableEq P] (j : P) (n : ℕ) : readCost j (.inl n) = 0 := by
  rw [readCost]
  rfl

@[simp] theorem readCost_inr [DecidableEq P] (j j' : P) :
    readCost j (.inr j') = if j' = j then 1 else 0 := by
  rw [readCost]
  rfl

theorem decodeLaw_eq (program : ProbOracleComp (fun _ : P => Γ) α) (y : P → Γ) :
    decodeLaw program y = evalWith (wordOracle y) program := by
  rw [decodeLaw.eq_def]

theorem expectedReads_eq [DecidableEq P] (program : ProbOracleComp (fun _ : P => Γ) α)
    (y : P → Γ) (j : P) :
    expectedReads program y j = expectedCost (wordOracle y) (readCost j) program := by
  rw [expectedReads.eq_def]

section Defs

variable [Fintype P]

/-- `A` is a `(q, δ, ε)` local decoder for the code `C`: it makes at most `q` queries, and from
every word within Hamming distance `δ |P|` of the codeword of `x` it outputs each bit of `x` with
probability at least `1 / 2 + ε`. -/
structure IsLocalDecoder [DecidableEq Γ] (C : (ι → Bool) → P → Γ) (q : ℕ) (δ ε : ℝ)
    (A : LocalDecoder ι P Γ) : Prop where
  /-- Each bit is decoded with at most `q` queries on every path. -/
  isQueryBounded : ∀ i, (A i).IsQueryBounded q
  /-- Every bit is recovered from every word close to the codeword. -/
  correct : ∀ x y i, (hammingDist y (C x) : ℝ) ≤ δ * Fintype.card P →
    1 / 2 + ε ≤ (decodeLaw (A i) y (x i)).toReal

/-- `A` is a `(q, c, ε)` smooth decoder for the code `C`: it makes at most `q` queries, outputs
each bit of `x` from the codeword of `x` with probability at least `1 / 2 + ε`, and on codewords
reads each position at most `c / |P|` times in expectation. -/
structure IsSmoothDecoder [DecidableEq P] (C : (ι → Bool) → P → Γ) (q : ℕ) (c ε : ℝ)
    (A : LocalDecoder ι P Γ) : Prop where
  /-- Each bit is decoded with at most `q` queries on every path. -/
  isQueryBounded : ∀ i, (A i).IsQueryBounded q
  /-- Every bit is recovered from the codeword. -/
  correct : ∀ x i, 1 / 2 + ε ≤ (decodeLaw (A i) (C x) (x i)).toReal
  /-- On codewords, no position is read more than `c / |P|` times in expectation. -/
  smooth : ∀ x i j, (expectedReads (A i) (C x) j).toReal ≤ c / Fintype.card P

/-- The code `C` is a `(q, δ, ε)` locally decodable code: it has a `(q, δ, ε)` local decoder. -/
def IsLocallyDecodable [DecidableEq Γ] (C : (ι → Bool) → P → Γ) (q : ℕ) (δ ε : ℝ) : Prop :=
  ∃ A, IsLocalDecoder C q δ ε A

/-- The code `C` is a `(q, c, ε)` smooth code: it has a `(q, c, ε)` smooth decoder. -/
def IsSmoothCode [DecidableEq P] (C : (ι → Bool) → P → Γ) (q : ℕ) (c ε : ℝ) : Prop :=
  ∃ A, IsSmoothDecoder C q c ε A

theorem isLocallyDecodable_iff [DecidableEq Γ] {C : (ι → Bool) → P → Γ} {q : ℕ} {δ ε : ℝ} :
    IsLocallyDecodable C q δ ε ↔ ∃ A, IsLocalDecoder C q δ ε A := by
  rw [IsLocallyDecodable]

theorem isSmoothCode_iff [DecidableEq P] {C : (ι → Bool) → P → Γ} {q : ℕ} {c ε : ℝ} :
    IsSmoothCode C q c ε ↔ ∃ A, IsSmoothDecoder C q c ε A := by
  rw [IsSmoothCode]

theorem IsLocalDecoder.isLocallyDecodable [DecidableEq Γ] {C : (ι → Bool) → P → Γ} {q : ℕ}
    {δ ε : ℝ} {A : LocalDecoder ι P Γ} (hA : IsLocalDecoder C q δ ε A) :
    IsLocallyDecodable C q δ ε :=
  isLocallyDecodable_iff.mpr ⟨A, hA⟩

theorem IsSmoothDecoder.isSmoothCode [DecidableEq P] {C : (ι → Bool) → P → Γ} {q : ℕ} {c ε : ℝ}
    {A : LocalDecoder ι P Γ} (hA : IsSmoothDecoder C q c ε A) : IsSmoothCode C q c ε :=
  isSmoothCode_iff.mpr ⟨A, hA⟩

end Defs

/-- The program reads each position equally often in expectation against every received word. -/
def HasObliviousReads [DecidableEq P] (program : ProbOracleComp (fun _ : P => Γ) α) : Prop :=
  ∀ y y' j, expectedReads program y j = expectedReads program y' j

theorem hasObliviousReads_iff [DecidableEq P] {program : ProbOracleComp (fun _ : P => Γ) α} :
    HasObliviousReads program ↔
      ∀ y y' j, expectedReads program y j = expectedReads program y' j := by
  rw [HasObliviousReads]

/-- A program with oblivious reads reads each position as often against `y` as against `y'`. -/
theorem HasObliviousReads.expectedReads_eq [DecidableEq P]
    {program : ProbOracleComp (fun _ : P => Γ) α} (h : HasObliviousReads program)
    (y y' : P → Γ) (j : P) : expectedReads program y j = expectedReads program y' j :=
  hasObliviousReads_iff.mp h y y' j

/-! ### The output law -/

section Law

variable (y : P → Γ)

@[simp] theorem decodeLaw_pure (a : α) :
    decodeLaw (pure a : ProbOracleComp (fun _ : P => Γ) α) y = PMF.pure a := by
  rw [decodeLaw_eq, evalWith_pure]

@[simp] theorem decodeLaw_bind {β : Type} (program : ProbOracleComp (fun _ : P => Γ) α)
    (next : α → ProbOracleComp (fun _ : P => Γ) β) :
    decodeLaw (program >>= next) y = (decodeLaw program y).bind fun a => decodeLaw (next a) y := by
  simp only [decodeLaw_eq, evalWith_bind]

@[simp] theorem decodeLaw_map {β : Type} (f : α → β)
    (program : ProbOracleComp (fun _ : P => Γ) α) :
    decodeLaw (f <$> program) y = (decodeLaw program y).map f := by
  simp only [decodeLaw_eq, evalWith_map]

@[simp] theorem decodeLaw_query (j : P) :
    decodeLaw (ProbOracleComp.query (spec := fun _ : P => Γ) j) y = PMF.pure (y j) := by
  rw [decodeLaw_eq]
  exact ProbOracleComp.interpret_query _ _ _

@[simp] theorem decodeLaw_query_inl (n : ℕ) :
    decodeLaw (OracleComp.query (spec := probOracleSpec fun _ : P => Γ) (.inl n)) y =
      ProbComp.unifOracle n := by
  rw [decodeLaw_eq]
  exact evalWith_query _ _

@[simp] theorem decodeLaw_query_inr (j : P) :
    decodeLaw (OracleComp.query (spec := probOracleSpec fun _ : P => Γ) (.inr j)) y =
      PMF.pure (y j) := by
  rw [decodeLaw_eq]
  exact evalWith_query _ _

@[simp] theorem decodeLaw_sample (program : ProbComp α) :
    decodeLaw (sample (spec := fun _ : P => Γ) program) y = ProbComp.eval program := by
  rw [decodeLaw_eq]
  exact ProbOracleComp.interpret_sample _ _ _

/-- The probabilities of the two outputs of a decoder add up to one. -/
theorem toReal_decodeLaw_add_not (program : ProbOracleComp (fun _ : P => Γ) Bool) (b : Bool) :
    (decodeLaw program y b).toReal + (decodeLaw program y (!b)).toReal = 1 := by
  have h := (decodeLaw program y).tsum_coe
  rw [tsum_fintype, Fintype.sum_bool] at h
  rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  cases b
  · rw [Bool.not_false, add_comm, h, ENNReal.toReal_one]
  · rw [Bool.not_true, h, ENNReal.toReal_one]

end Law

/-! ### Expected reads -/

section Reads

variable [DecidableEq P]

theorem sum_readCost [Fintype P] :
    ∑ j, readCost (P := P) j = fun q => ((Sum.elim (fun _ => 0) (fun _ => 1) q : ℕ) : ℝ≥0∞) := by
  funext q
  cases q with
  | inl n => simp [readCost]
  | inr j' => simp [readCost, Finset.sum_apply]

/-- A decoder making at most `q` queries reads at most `q` positions in expectation. -/
theorem sum_expectedReads_le [Fintype P] {program : ProbOracleComp (fun _ : P => Γ) α} {q : ℕ}
    (hq : program.IsQueryBounded q) (y : P → Γ) : ∑ j, expectedReads program y j ≤ q := by
  simp only [expectedReads_eq]
  rw [← expectedCost_sum, sum_readCost]
  exact expectedCost_le_of_isCostBounded _ hq

/-- A decoder making at most `q` queries reads each position at most `q` times in expectation. -/
theorem expectedReads_le {program : ProbOracleComp (fun _ : P => Γ) α} {q : ℕ}
    (hq : program.IsQueryBounded q) (y : P → Γ) (j : P) : expectedReads program y j ≤ q := by
  refine (expectedCost_mono _ (fun q' => ?_) program).trans
    (expectedCost_le_of_isCostBounded (wordOracle y) hq)
  cases q' with
  | inl n => simp [readCost]
  | inr j' => by_cases h : j' = j <;> simp [readCost, h]

theorem expectedReads_ne_top {program : ProbOracleComp (fun _ : P => Γ) α} {q : ℕ}
    (hq : program.IsQueryBounded q) (y : P → Γ) (j : P) : expectedReads program y j ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top q) (expectedReads_le hq y j)

end Reads

/-! ### Non-adaptive decoders -/

/-- Read the positions `Q 0, …, Q (q - 1)` in order, returning the symbols read. -/
def readAll : {q : ℕ} → (Fin q → P) → ProbOracleComp (fun _ : P => Γ) (Fin q → Γ)
  | 0, _ => pure Fin.elim0
  | _ + 1, Q => do
    let a ← ProbOracleComp.query (Q 0)
    let rest ← readAll (Fin.tail Q)
    pure (Fin.cons a rest)

/-- The non-adaptive decoder that draws a random string `r` from `coins`, reads the positions
`Q r k` for `k < q`, and outputs `output r` of the symbols read. -/
def nonadaptive {R : Type} {q : ℕ} (coins : ProbComp R) (Q : R → Fin q → P)
    (output : R → (Fin q → Γ) → Bool) : ProbOracleComp (fun _ : P => Γ) Bool := do
  let r ← sample coins
  let a ← readAll (Q r)
  pure (output r a)

section Nonadaptive

variable {R : Type} {q : ℕ}

theorem isQueryBounded_readAll (Q : Fin q → P) :
    (readAll (Γ := Γ) Q).IsQueryBounded q := by
  induction q with
  | zero => exact .pure _ 0
  | succ q ih =>
    simp only [readAll]
    exact ((IsQueryBounded.query (Q 0)).bind fun a =>
      (ih (Fin.tail Q)).bind fun _ => .pure _ 0).mono (by omega)

theorem isQueryBounded_nonadaptive (coins : ProbComp R) (Q : R → Fin q → P)
    (output : R → (Fin q → Γ) → Bool) : (nonadaptive coins Q output).IsQueryBounded q := by
  have h := (IsQueryBounded.sample (spec := fun _ : P => Γ) coins).bind fun r =>
    (isQueryBounded_readAll (Γ := Γ) (Q r)).bind fun a => .pure (output r a) 0
  rw [Nat.zero_add, Nat.add_zero] at h
  exact h

@[simp] theorem decodeLaw_readAll (Q : Fin q → P) (y : P → Γ) :
    decodeLaw (readAll Q) y = PMF.pure (y ∘ Q) := by
  induction q with
  | zero =>
    rw [readAll, decodeLaw_pure]
    congr 1
    funext k
    exact k.elim0
  | succ q ih =>
    simp only [readAll, decodeLaw_bind, decodeLaw_query, PMF.pure_bind, ih, decodeLaw_pure]
    congr 1
    exact Fin.cons_self_tail (y ∘ Q)

theorem decodeLaw_nonadaptive (coins : ProbComp R) (Q : R → Fin q → P)
    (output : R → (Fin q → Γ) → Bool) (y : P → Γ) :
    decodeLaw (nonadaptive coins Q output) y =
      (ProbComp.eval coins).map fun r => output r (y ∘ Q r) := by
  simp only [nonadaptive, decodeLaw_bind, decodeLaw_sample, decodeLaw_readAll, PMF.pure_bind,
    decodeLaw_pure]
  rfl

@[simp] theorem expectedReads_query [DecidableEq P] (j' : P) (y : P → Γ) (j : P) :
    expectedReads (ProbOracleComp.query (spec := fun _ : P => Γ) j') y j =
      if j' = j then 1 else 0 := by
  rw [expectedReads_eq, ProbOracleComp.query, expectedCost_query]
  rfl

theorem expectedReads_bind [DecidableEq P] {β : Type}
    (program : ProbOracleComp (fun _ : P => Γ) α) (next : α → ProbOracleComp (fun _ : P => Γ) β)
    (y : P → Γ) (j : P) :
    expectedReads (program >>= next) y j =
      expectedReads program y j + ∑' a, decodeLaw program y a * expectedReads (next a) y j := by
  simp only [expectedReads_eq, decodeLaw_eq, expectedCost_bind]

@[simp] theorem expectedReads_pure [DecidableEq P] (a : α) (y : P → Γ) (j : P) :
    expectedReads (pure a : ProbOracleComp (fun _ : P => Γ) α) y j = 0 := by
  rw [expectedReads_eq, expectedCost_pure]

/-- A call reads its position, then the continuation runs on the answer. -/
theorem expectedReads_query_bind [DecidableEq P] (q' : ℕ ⊕ P)
    (cont : probOracleSpec (fun _ : P => Γ) q' → ProbOracleComp (fun _ : P => Γ) α)
    (y : P → Γ) (j : P) :
    expectedReads (OracleComp.query q' >>= cont) y j =
      readCost j q' + ∑' a, wordOracle y q' a * expectedReads (cont a) y j := by
  simp only [expectedReads_eq]
  exact expectedCost_query_bind _ _ _ _

@[simp] theorem expectedReads_sample [DecidableEq P] (program : ProbComp α) (y : P → Γ) (j : P) :
    expectedReads (sample (spec := fun _ : P => Γ) program) y j = 0 := by
  rw [expectedReads_eq, readCost]
  exact expectedCost_sample _ _ _

theorem expectedReads_readAll [DecidableEq P] (Q : Fin q → P) (y : P → Γ) (j : P) :
    expectedReads (readAll Q) y j = ∑ k, if Q k = j then 1 else 0 := by
  induction q with
  | zero => simp [readAll]
  | succ q ih =>
    simp only [readAll, expectedReads_bind, expectedReads_query, expectedReads_pure, add_zero,
      mul_zero, tsum_zero, ih, decodeLaw_query, decodeLaw_readAll]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, Fin.sum_univ_succ]
    rfl

theorem expectedReads_nonadaptive [DecidableEq P] (coins : ProbComp R) (Q : R → Fin q → P)
    (output : R → (Fin q → Γ) → Bool) (y : P → Γ) (j : P) :
    expectedReads (nonadaptive coins Q output) y j =
      ∑' r, ProbComp.eval coins r * ∑ k, if Q r k = j then 1 else 0 := by
  simp only [nonadaptive, expectedReads_bind, expectedReads_sample, zero_add, decodeLaw_sample,
    expectedReads_readAll, expectedReads_pure, mul_zero, tsum_zero, add_zero]

theorem hasObliviousReads_nonadaptive [DecidableEq P] (coins : ProbComp R) (Q : R → Fin q → P)
    (output : R → (Fin q → Γ) → Bool) : HasObliviousReads (nonadaptive coins Q output) :=
  hasObliviousReads_iff.mpr fun y y' j => by
    rw [expectedReads_nonadaptive, expectedReads_nonadaptive]

/-- A non-adaptive decoder each of whose `q` queries is a uniform position reads every position
`q / |P|` times in expectation, against every received word. -/
theorem expectedReads_nonadaptive_of_uniform [Fintype P] [Nonempty P] [DecidableEq P]
    (coins : ProbComp R) (Q : R → Fin q → P) (output : R → (Fin q → Γ) → Bool)
    (huniform : ∀ k, (ProbComp.eval coins).map (fun r => Q r k) = PMF.uniformOfFintype P)
    (y : P → Γ) (j : P) :
    expectedReads (nonadaptive coins Q output) y j = q / Fintype.card P := by
  have hk (k : Fin q) : ∑' r, ProbComp.eval coins r * (if Q r k = j then 1 else 0) =
      (Fintype.card P : ℝ≥0∞)⁻¹ := by
    have h := congrArg (fun p : PMF P => p j) (huniform k)
    simp only [PMF.map_apply, PMF.uniformOfFintype_apply] at h
    rw [← h]
    refine tsum_congr fun r => ?_
    by_cases hr : Q r k = j
    · simp [hr]
    · simp [hr, Ne.symm hr]
  rw [expectedReads_nonadaptive]
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
  simp only [hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]

/-- A non-adaptive decoder each of whose `q` queries is a uniform position is a `(q, q, ε)` smooth
decoder as soon as it decodes codewords with probability `1 / 2 + ε`. -/
theorem isSmoothDecoder_nonadaptive_of_uniform [Fintype P] [Nonempty P] [DecidableEq P]
    {C : (ι → Bool) → P → Γ} {ε : ℝ} (coins : ι → ProbComp R)
    (Q : ι → R → Fin q → P) (output : ι → R → (Fin q → Γ) → Bool)
    (huniform : ∀ i k, (ProbComp.eval (coins i)).map (fun r => Q i r k) =
      PMF.uniformOfFintype P)
    (hcorrect : ∀ x i, 1 / 2 + ε ≤
      (decodeLaw (nonadaptive (coins i) (Q i) (output i)) (C x) (x i)).toReal) :
    IsSmoothDecoder C q q ε fun i => nonadaptive (coins i) (Q i) (output i) where
  isQueryBounded i := isQueryBounded_nonadaptive _ _ _
  correct := hcorrect
  smooth x i j := by
    rw [expectedReads_nonadaptive_of_uniform _ _ _ (huniform i), ENNReal.toReal_div,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast]

end Nonadaptive

end Cslib.Code
