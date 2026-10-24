/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AtLeast
public import Complexity.Computability.Circuit.Boolean.BitBlast
public import Complexity.Computability.Circuit.ReedMullerDecoding
public import Complexity.Crypto.Computational.GoldreichLevin.Nonuniform
public import Complexity.Foundations.Data.BitString.Block

/-!
# The stages of local list decoding as De Morgan circuits

Reconstructing a worst-case hard function from a predictor for its encoding
[SudanTrevisanVadhan2001] runs three decoders in sequence, each of which queries the previous one
at computed points: Goldreich–Levin decoding of the inner Hadamard code
(`Cslib.Circuits.Boolean.glPredictor`), local list decoding of the outer Reed–Muller code along
lines with advice (`Cslib.Code.lineListDecode`), and self-correction by interpolation and majority
trees (`Cslib.Code.lagrangeDecode`, `Cslib.majTree`). This module bounds the De Morgan circuit
size of each stage given the circuit size of the previous one.

A field element is represented by `w` bits through an encoding `enc : F ≃ BitString w`, and a
function `G : (Fin m → F) → F` is *bit-synthesizable with `cost` gates*
(`Cslib.Circuits.Boolean.BitSynthesis`) if, whenever the bits of the coordinates of a point are
available, the bits of the value of `G` at that point can be made available with `cost` further
gates. The arithmetic between queries runs over the full binary basis of the field and is
bit-blasted (`Cslib.Circuits.Synthesis.bitBlast_synthesis`), at `bitBlastCost w` gates per field
operation.

* The Goldreich–Levin stage costs `glCost w K s` for a predictor of size `s` and `K` masks
  (`Cslib.Circuits.Boolean.bitSynthesis_glPredictor`).
* The line stage costs `lineCost` for a field of size `q`, in terms of the cost of its oracle
  (`Cslib.Circuits.Boolean.BitSynthesis.lineListDecode`).
* The self-correction stage costs `selfCorrectCost` in terms of the cost of its oracle
  (`Cslib.Circuits.Boolean.BitSynthesis.selfCorrect`).

## Main definitions

* `Cslib.Circuits.Boolean.pointOfBits`, `Cslib.Circuits.Boolean.bitsOfPoint`: points of `F ^ m`
  and their bits.
* `Cslib.Circuits.Boolean.BitSynthesis`: bit-synthesizable functions.
* `Cslib.Circuits.Boolean.glPredictor`, `Cslib.Circuits.Boolean.glCost`: the Goldreich–Levin
  decoder of the inner code and its gate budget.

## Main results

* `Cslib.Circuits.Boolean.bitSynthesis_glPredictor`,
  `Cslib.Circuits.Boolean.BitSynthesis.lineListDecode`,
  `Cslib.Circuits.Boolean.BitSynthesis.selfCorrect`: the costs of the three stages.

## References

* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset Cslib.Code Cslib.LinearAlgebra

variable {F : Type*} {w m : ℕ}

/-! ### Points and their bits -/

/-- The point of `F ^ m` whose coordinates have the given bits: coordinate `i` decodes block `i`
(`Cslib.BitString.block`). -/
def pointOfBits (enc : F ≃ BitString w) (y : BitString (m * w)) : Fin m → F :=
  fun i => enc.symm (BitString.block y i)

/-- The bits of the coordinates of a point of `F ^ m`, block after block
(`Cslib.BitString.blocksEquiv`). -/
def bitsOfPoint (enc : F ≃ BitString w) (x : Fin m → F) : BitString (m * w) :=
  BitString.blocksEquiv.symm fun i => enc (x i)

/-- Decoding the bits of a point gives the point back. -/
@[simp]
theorem pointOfBits_bitsOfPoint (enc : F ≃ BitString w) (x : Fin m → F) :
    pointOfBits enc (bitsOfPoint enc x) = x := by
  funext i
  simp only [pointOfBits, bitsOfPoint, ← BitString.blocksEquiv_apply, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply]

/-- Encoding the point with given bits gives the bits back. -/
@[simp]
theorem bitsOfPoint_pointOfBits (enc : F ≃ BitString w) (y : BitString (m * w)) :
    bitsOfPoint enc (pointOfBits enc y) = y := by
  simp only [pointOfBits, bitsOfPoint, Equiv.apply_symm_apply, ← BitString.blocksEquiv_apply,
    Equiv.symm_apply_apply]

/-- `G` is *bit-synthesizable with `cost` gates*: whenever the bits of the coordinates of a point
are available, the bits of the value of `G` at the point can be made available with `cost` further
De Morgan gates. -/
def BitSynthesis (enc : F ≃ BitString w) (G : (Fin m → F) → F) (cost : ℕ) : Prop :=
  ∀ (n : ℕ) (S : Set (BooleanFunction n)) (φ : Fin m → (Fin n → Bool) → F),
    (∀ i j, bitsOf enc (φ i) j ∈ S) →
      Synthesis interpretation S (Set.range fun j => bitsOf enc (fun v => G fun i => φ i v) j)
        cost

/-- A bit synthesis with `a` gates is one with any larger budget. -/
theorem BitSynthesis.mono {enc : F ≃ BitString w} {G : (Fin m → F) → F} {a b : ℕ}
    (h : BitSynthesis enc G a) (hab : a ≤ b) : BitSynthesis enc G b :=
  fun n S φ hφ => (h n S φ hφ).mono Set.Subset.rfl Set.Subset.rfl hab

/-! ### The Goldreich–Levin stage -/

/-- **The Goldreich–Levin decoder of the inner code.** At a point `x`, the corrected-majority
candidate of the predictor `r ↦ C (bits of x, r)` with fixed masks and guess, read as a field
element. -/
def glPredictor (enc : F ≃ BitString w) (C : BooleanFunction (m * w + w)) {K : ℕ}
    (masks : Fin K → BitString w) (guess : BitString K) : (Fin m → F) → F :=
  fun x => enc.symm
    (Crypto.GoldreichLevin.candidate (fun r => C (Fin.append (bitsOfPoint enc x) r)) masks guess)

/-- The gate budget of the Goldreich–Levin stage: two constants, and for each output bit,
`2 ^ K - 1` copies of the predictor, each with at most one negation, and a strict majority. -/
def glCost (w K s : ℕ) : ℕ :=
  2 + w * ((2 ^ K - 1) * (s + 1) + (2 + (2 ^ K - 1) * (2 * (2 ^ K - 1 + 2))))

private theorem append_apply {n p q : ℕ} (A : Fin p → BooleanFunction n)
    (B : Fin q → BooleanFunction n) (k : Fin (p + q)) (v : Fin n → Bool) :
    Fin.append A B k v = Fin.append (fun i => A i v) (fun i => B i v) k := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]

/-- A strict majority of the `N` votes of a finset, enumerated, is a threshold of `N` functions. -/
private theorem strictMajorityOn_eq_atLeast {n : ℕ} {ι : Type*} (T : Finset ι)
    (vote : ι → BooleanFunction n) (v : Fin n → Bool) :
    BitString.strictMajorityOn T (fun i => vote i v) =
      atLeast (fun l => if h : l < #T then vote (T.equivFin.symm ⟨l, h⟩) else fun _ => false)
        #T (#T / 2 + 1) v := by
  classical
  simp only [BitString.strictMajorityOn, atLeast]
  congr 1
  rw [Nat.lt_iff_add_one_le]
  congr 1
  refine card_bij (fun i hi => (T.equivFin ⟨i, (mem_filter.1 hi).1⟩ : ℕ)) (fun i hi => ?_)
    (fun i hi i' hi' h => ?_) (fun l hl => ?_)
  · rw [mem_filter] at hi ⊢
    refine ⟨mem_range.2 (T.equivFin _).2, ?_⟩
    rw [dite_eq_left (T.equivFin _).2]
    simpa using hi.2
  · have := T.equivFin.injective (Fin.ext h)
    exact congrArg Subtype.val this
  · rw [mem_filter, mem_range] at hl
    obtain ⟨hl, hv⟩ := hl
    rw [dite_eq_left hl] at hv
    refine ⟨T.equivFin.symm ⟨l, hl⟩, mem_filter.2 ⟨(T.equivFin.symm ⟨l, hl⟩).2, hv⟩, ?_⟩
    simp

/-- **The Goldreich–Levin stage.** If the predictor `C` has a De Morgan circuit with at most `s`
gates, the Goldreich–Levin decoder with masks `masks` and guess `guess` is bit-synthesizable with
`glCost w K s` gates. -/
theorem bitSynthesis_glPredictor (enc : F ≃ BitString w) {C : BooleanFunction (m * w + w)}
    {sC : ℕ} (hC : complexity interpretation (single C) ≤ sC) {K : ℕ}
    (masks : Fin K → BitString w) (guess : BitString K) :
    BitSynthesis enc (glPredictor enc C masks guess) (glCost w K sC) := by
  classical
  intro n S φ hφ
  obtain ⟨c, hc, hsize⟩ := complexity_le_iff.1 hC
  -- the two constants
  have hconst : Synthesis interpretation S ({fun _ => true} ∪ {fun _ => false}) 2 :=
    (Synthesis.const (s := S) true).union (Synthesis.const (s := S) false)
  set S₁ := S ∪ ({fun _ => true} ∪ {fun _ => false})
  -- the bits of the point
  let xb : Fin (m * w) → BooleanFunction n := fun k v => bitsOfPoint enc (fun i => φ i v) k
  have hxb : ∀ k, xb k ∈ S₁ := fun k =>
    Set.mem_union_left _ (hφ (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  -- one corrected vote: the predictor at a fixed query, xored with a fixed bit
  have hvote : ∀ (r : BitString w) (bit : Bool), Synthesis interpretation S₁
      {fun v => C (Fin.append (bitsOfPoint enc fun i => φ i v) r) ^^ bit} (sC + 1) := by
    intro r bit
    let g : Fin (m * w + w) → BooleanFunction n := Fin.append xb fun k _ => r k
    have hg : ∀ k, g k ∈ S₁ := by
      intro k
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · simp only [g, Fin.append_left]
        exact hxb i
      · simp only [g, Fin.append_right]
        cases r i
        · exact Set.mem_union_right _ (Set.mem_union_right _ rfl)
        · exact Set.mem_union_right _ (Set.mem_union_left _ rfl)
    have hcirc := Synthesis.circuit (I := interpretation) c g hg
    have heval : (fun v => c.eval interpretation (fun k => g k v) 0) =
        fun v => C (Fin.append (bitsOfPoint enc fun i => φ i v) r) := by
      funext v
      rw [hc]
      simp only [single_apply]
      congr 1
      funext k
      change Fin.append xb (fun k _ => r k) k v = _
      rw [append_apply]
    have h1 : Synthesis interpretation S₁
        {fun v => C (Fin.append (bitsOfPoint enc fun i => φ i v) r)} sC :=
      hcirc.mono Set.Subset.rfl (Set.singleton_subset_iff.2 ⟨0, heval⟩) hsize
    cases bit
    · simpa using h1.mono Set.Subset.rfl Set.Subset.rfl (Nat.le_succ _)
    · simpa using h1.not
  -- the strict majority for each output bit
  set T := Crypto.GoldreichLevin.nonemptySubsets K
  let V : Fin w → Finset (Fin K) → BooleanFunction n := fun j t v =>
    C (Fin.append (bitsOfPoint enc fun i => φ i v) (Pi.single j 1 + ∑ l ∈ t, masks l)) ^^
      ∑ l ∈ t, guess l
  have hbit : ∀ j, Synthesis interpretation S₁
      {bitsOf enc (fun v => glPredictor enc C masks guess fun i => φ i v) j}
      (#T * (sC + 1) + (2 + #T * (2 * (#T + 2)))) := by
    intro j
    have hvotes := Synthesis.biUnion (I := interpretation) (s := S₁) T (fun t => {V j t})
      (fun _ => sC + 1) fun t _ => hvote _ _
    set S₂ := S₁ ∪ ⋃ t ∈ T, {V j t}
    have hmaj := synthesis_atLeast (s := S₂) (k := #T) (j := #T / 2 + 1)
      (fun l => if h : l < #T then V j (T.equivFin.symm ⟨l, h⟩) else fun _ => false)
      (fun l hl => by
        rw [dite_eq_left hl]
        exact Set.mem_union_right _ (Set.mem_biUnion (T.equivFin.symm ⟨l, hl⟩).2 rfl))
      (by omega)
    refine (hvotes.trans hmaj).mono Set.Subset.rfl (Set.singleton_subset_iff.2 ?_) ?_
    · change _ = _
      funext v
      rw [← strictMajorityOn_eq_atLeast T (V j) v]
      simp only [bitsOf, glPredictor, Equiv.apply_symm_apply, Crypto.GoldreichLevin.candidate,
        V, T]
      rfl
    · simp only [sum_const, smul_eq_mul]
      exact le_rfl
  have hall := Synthesis.iUnion (I := interpretation) (s := S₁)
    (fun j => {bitsOf enc (fun v => glPredictor enc C masks guess fun i => φ i v) j})
    (fun _ => #T * (sC + 1) + (2 + #T * (2 * (#T + 2)))) hbit
  refine (hconst.trans hall).mono Set.Subset.rfl ?_ ?_
  · rintro _ ⟨j, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, rfl⟩
  · simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, glCost, T,
      Crypto.GoldreichLevin.card_nonemptySubsets]
    exact le_rfl

/-! ### The line stage -/

/-- The gate budget of the line stage over a field with `q` elements, for points in `m`
variables, `M` monomials, `Y`-degrees up to `ℓ`, degree `d` and an oracle of cost `SG`: the points
of the line and the decoding with a hint are bit-blasted, and the oracle is queried at the `q`
points of the line. -/
def lineCost (w q m M ℓ d SG : ℕ) : ℕ :=
  ((q + 5) * m + 2 + (1 + hintDecodeCost q q M ℓ d)) * bitBlastCost w + q * SG

variable [Field F] [Fintype F] [DecidableEq F]

/-- **The line stage.** If `G` is bit-synthesizable with `SG` gates, then the local list decoder
`lineListDecode G d D z a` is bit-synthesizable with `lineCost` gates. -/
theorem BitSynthesis.lineListDecode {enc : F ≃ BitString w} {G : (Fin m → F) → F} {SG : ℕ}
    (hG : BitSynthesis enc G SG) (d D : ℕ) (z : Fin m → F) (a : F) :
    BitSynthesis enc (Code.lineListDecode G d D z a)
      (lineCost w (Fintype.card F) m #(Sudan.monomials d D) (D / d) d SG) := by
  intro n S φ hφ
  set q := Fintype.card F
  -- the points of the line and the hint position
  let ΨA : Option (F × Fin m) → (Fin m → F) → F := fun o v => match o with
    | none => firstNonzero (z - fun i => v i)
    | some (t, i) =>
      ((fun i => v i) + t • (firstNonzero (z - fun i => v i))⁻¹ • (z - fun i => v i)) i
  have hA : Synthesis (fullInterpretation (k := 2)) (inputs m) (Set.range ΨA)
      ((q + 5) * m + 2) :=
    Synthesis.full_linePoints (s := inputs m) (fun i v => v i) (fun i => ⟨i, rfl⟩) z
  have hA' := Synthesis.bitBlast_synthesis enc ΨA hA φ hφ
  set TA := Set.range fun oj : Option (F × Fin m) × Fin w =>
    bitsOf enc (fun x => ΨA oj.1 fun i => φ i x) oj.2
  -- the oracle at the points of the line
  let pt : F → Fin m → (Fin n → Bool) → F := fun t i x => ΨA (some (t, i)) fun k => φ k x
  have hB : Synthesis interpretation (S ∪ TA)
      (⋃ t : F, Set.range fun j => bitsOf enc (fun x => G fun i => pt t i x) j) (q * SG) := by
    have := Synthesis.iUnion (I := interpretation) (s := S ∪ TA)
      (fun t : F => Set.range fun j => bitsOf enc (fun x => G fun i => pt t i x) j)
      (fun _ => SG) (fun t => hG n (S ∪ TA) (pt t) fun i j =>
        Set.mem_union_right _ ⟨(some (t, i), j), rfl⟩)
    simpa [q] using this
  set TB := ⋃ t : F, Set.range fun j => bitsOf enc (fun x => G fun i => pt t i x) j
  -- decoding with the hint
  let e := Fintype.equivFin F
  let ΨC : Unit → (Fin (q + 1) → F) → F := fun _ v =>
    hintDecode id (fun t => v (Fin.castSucc (e t))) d D (v (Fin.last q)) a
  have hC : Synthesis (fullInterpretation (k := 2)) (inputs (q + 1)) (Set.range ΨC)
      (1 + hintDecodeCost q q #(Sudan.monomials d D) (D / d) d) := by
    have hconst := Synthesis.full_const (k := 2) (s := inputs (q + 1)) a
    have hdec := Synthesis.full_hintDecode (s := inputs (q + 1) ∪ {fun _ => a}) (ι := F) id
      (fun t v => v (Fin.castSucc (e t)))
      (fun t => Set.mem_union_left _ (⟨Fin.castSucc (e t), rfl⟩ :
        (fun v : Fin (q + 1) → F => v (Fin.castSucc (e t))) ∈ inputs (q + 1)))
      (τ := fun v => v (Fin.last q)) (Set.mem_union_left _ (⟨Fin.last q, rfl⟩ :
        (fun v : Fin (q + 1) → F => v (Fin.last q)) ∈ inputs (q + 1)))
      (Set.mem_union_right _ rfl) d D
    refine (hconst.trans hdec).mono Set.Subset.rfl ?_ le_rfl
    rintro _ ⟨u, rfl⟩
    rfl
  let φC : Fin (q + 1) → (Fin n → Bool) → F :=
    Fin.lastCases (fun x => ΨA none fun i => φ i x) fun k x => G fun i => pt (e.symm k) i x
  have hφC : ∀ k j, bitsOf enc (φC k) j ∈ (S ∪ TA) ∪ TB := by
    intro k j
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp only [φC, Fin.lastCases_last]
      exact Set.mem_union_left _ (Set.mem_union_right _ ⟨(none, j), rfl⟩)
    · simp only [φC, Fin.lastCases_castSucc]
      exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨e.symm k, j, rfl⟩)
  have hC' := Synthesis.bitBlast_synthesis enc ΨC hC φC hφC
  refine (hA'.trans (hB.comp hC')).mono Set.Subset.rfl ?_ ?_
  · rintro _ ⟨j, rfl⟩
    refine Or.inr ⟨((), j), funext fun x => ?_⟩
    simp only [bitsOf, ΨC, φC, Fin.lastCases_last, Fin.lastCases_castSucc, Equiv.symm_apply_apply,
      Code.lineListDecode, pt, ΨA]
  · unfold lineCost
    nlinarith

/-! ### The self-correction stage -/

/-- The gate budget of the self-correction stage, for points in `m` variables, `d + 1` nodes, a
majority tree of depth `L` and an oracle of cost `S1`: the points of the lines and the
interpolation and majorities are bit-blasted, and the oracle is queried at `3 ^ L * (d + 1)`
points. -/
def selfCorrectCost (w m d L S1 : ℕ) : ℕ :=
  (m * (3 ^ L * (d + 1)) + (3 ^ L * (2 * (d + 1) + 1) + (2 * 3 ^ L - 2))) * bitBlastCost w +
    3 ^ L * (d + 1) * S1

omit [Fintype F] in
/-- **The self-correction stage.** If `C1` is bit-synthesizable with `S1` gates, then the majority
tree of depth `L` of the interpolations of `C1` along the lines through `x` in the directions
`V τ` is bit-synthesizable with `selfCorrectCost` gates. -/
theorem BitSynthesis.selfCorrect {enc : F ≃ BitString w} {C1 : (Fin m → F) → F} {S1 : ℕ}
    (hC1 : BitSynthesis enc C1 S1) {d : ℕ} (ν : Fin (d + 1) ↪ F) {L : ℕ}
    (V : Fin (3 ^ L) → Fin m → F) :
    BitSynthesis enc (fun x => majTree L fun τ => lagrangeDecode ν C1 x (V τ))
      (selfCorrectCost w m d L S1) := by
  intro n S φ hφ
  -- the points of the lines
  let ΨA : (Fin (3 ^ L) × Fin (d + 1)) × Fin m → (Fin m → F) → F := fun o v =>
    v o.2 + ν o.1.2 * V o.1.1 o.2
  have hA : Synthesis (fullInterpretation (k := 2)) (inputs m) (Set.range ΨA)
      (m * (3 ^ L * (d + 1))) := by
    have := Synthesis.family (I := fullInterpretation (k := 2)) (s := inputs m) ΨA (fun _ => 1)
      (fun o => Synthesis.full_unary (fun a => a + ν o.1.2 * V o.1.1 o.2)
        (⟨o.2, rfl⟩ : (fun v : Fin m → F => v o.2) ∈ inputs m))
    simpa [Fintype.card_prod, mul_comm, mul_left_comm, mul_assoc] using this
  have hA' := Synthesis.bitBlast_synthesis enc ΨA hA φ hφ
  set TA := Set.range fun oj : ((Fin (3 ^ L) × Fin (d + 1)) × Fin m) × Fin w =>
    bitsOf enc (fun x => ΨA oj.1 fun i => φ i x) oj.2
  -- the oracle at the points
  let pt : Fin (3 ^ L) × Fin (d + 1) → Fin m → (Fin n → Bool) → F := fun τi k x =>
    ΨA (τi, k) fun i => φ i x
  have hB : Synthesis interpretation (S ∪ TA)
      (⋃ τi : Fin (3 ^ L) × Fin (d + 1),
        Set.range fun j => bitsOf enc (fun x => C1 fun k => pt τi k x) j)
      (3 ^ L * (d + 1) * S1) := by
    have := Synthesis.iUnion (I := interpretation) (s := S ∪ TA)
      (fun τi : Fin (3 ^ L) × Fin (d + 1) =>
        Set.range fun j => bitsOf enc (fun x => C1 fun k => pt τi k x) j)
      (fun _ => S1) (fun τi => hC1 n (S ∪ TA) (pt τi) fun k j =>
        Set.mem_union_right _ ⟨((τi, k), j), rfl⟩)
    simpa [Fintype.card_prod, mul_comm, mul_left_comm, mul_assoc] using this
  set TB := ⋃ τi : Fin (3 ^ L) × Fin (d + 1),
    Set.range fun j => bitsOf enc (fun x => C1 fun k => pt τi k x) j
  -- interpolation and majorities
  let ΨC : Unit → (Fin (3 ^ L * (d + 1)) → F) → F := fun _ v =>
    majTree L fun τ => ∑ i, lagrangeWeight ν i * v (finProdFinEquiv (τ, i))
  have hC : Synthesis (fullInterpretation (k := 2)) (inputs (3 ^ L * (d + 1))) (Set.range ΨC)
      (3 ^ L * (2 * (d + 1) + 1) + (2 * 3 ^ L - 2)) := by
    have hsums := Synthesis.family (I := fullInterpretation (k := 2))
      (s := inputs (3 ^ L * (d + 1)))
      (fun τ v => ∑ i, lagrangeWeight ν i * v (finProdFinEquiv (τ, i)))
      (fun _ => 2 * (d + 1) + 1)
      (fun τ => by
        simpa using Synthesis.full_weightedSum (s := inputs (3 ^ L * (d + 1))) (lagrangeWeight ν)
          (fun i v => v (finProdFinEquiv (τ, i))) (fun i => ⟨_, rfl⟩))
    have htree := Synthesis.full_majTree (s := inputs (3 ^ L * (d + 1)) ∪
        Set.range fun τ (v : Fin (3 ^ L * (d + 1)) → F) =>
          ∑ i, lagrangeWeight ν i * v (finProdFinEquiv (τ, i))) L
      (fun τ v => ∑ i, lagrangeWeight ν i * v (finProdFinEquiv (τ, i)))
      (fun τ => Set.mem_union_right _ ⟨τ, rfl⟩)
    refine (hsums.trans htree).mono Set.Subset.rfl ?_ ?_
    · rintro _ ⟨u, rfl⟩
      rfl
    · simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
      exact le_rfl
  let φC : Fin (3 ^ L * (d + 1)) → (Fin n → Bool) → F := fun k x =>
    C1 fun i => pt (finProdFinEquiv.symm k) i x
  have hφC : ∀ k j, bitsOf enc (φC k) j ∈ (S ∪ TA) ∪ TB := fun k j =>
    Set.mem_union_right _ (Set.mem_iUnion.2 ⟨finProdFinEquiv.symm k, j, rfl⟩)
  have hC' := Synthesis.bitBlast_synthesis enc ΨC hC φC hφC
  refine (hA'.trans (hB.comp hC')).mono Set.Subset.rfl ?_ ?_
  · rintro _ ⟨j, rfl⟩
    refine Or.inr ⟨((), j), funext fun x => ?_⟩
    simp only [bitsOf, ΨC, φC, Equiv.symm_apply_apply, lagrangeDecode, pt, ΨA]
    rfl
  · unfold selfCorrectCost
    nlinarith

end Cslib.Circuits.Boolean
