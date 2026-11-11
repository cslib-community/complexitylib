/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.XorPowerListSize
public import CslibFrontier.Computability.MCSP.PartialHardness.Construction
import CslibFrontier.Foundations.Combinatorics.HybridPrediction
import CslibFrontier.Foundations.Data.BitString.Block
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Knowledge sets of a circuit for the CMMSA table

The deterministic core of No soundness for the library's reduction from `GapCMMSA Δ g 1` to
partial MCSP (issue #4362, route B, milestone H4). The table `FromCMMSA.toInstance I Δ k λ P f`
comes from `CslibFrontier.Computability.MCSP.PartialHardness.Construction`; its Yes completeness
is `CslibFrontier.Computability.MCSP.PartialHardness.Completeness`. The analysis is the library's
own; [Hirahara2022] fixes only the problem shape.

**Candidates.** A circuit `h` on the table's inputs determines, for each variable `v`, a set
`cand h v` of Boolean functions on `ℓ v` inputs (`FromCMMSA.cand`). The set depends on `h`, never
on `f`. A function `g` is a candidate when, for some advice, the guess `z ↦ c + h (x[z])` agrees
with `g^{⊕k}` on at least a `1 / 2 + 1 / (2 Δ)` fraction of the words `z ∈ {0,1}^{k ℓ v}`. The
advice is an input `x`, a slot `(t, q)` and a bit `c`. Here `x[z]` writes the blocks of `z` into
the low `ℓ v` bits of the `k` seeds of slot `(t, q)` of `x` and zeroes their other bits. With
`2 ^ A` inputs, `Δ ²` slots and two bits, there are `2 ^ (A + 1) Δ ²` choices of advice. For
each one, the list-size bound of the `k`-fold XOR code
(`Cslib.Circuits.Boolean.card_filter_xorPower_mul_two_mul_sq_le_exp`) leaves at most
`2 Δ ² exp (2 ^ ℓ H(δ₀))` candidates when `k` is odd and `(1 - 2 δ₀) ^ k ≤ 1 / (2 Δ ²)`. Hence
`#cand h v ≤ 4 Δ⁴ 2 ^ A exp (2 ^ ℓ H(δ₀))` (`FromCMMSA.card_cand_le`).

**The knowledge set is heavy.** Let `I` be a No instance and let `h` agree with the table for
`f`. Then the variables `v` with `f v ∈ cand h v` weigh more than `g θ`
(`FromCMMSA.lt_weight_cand`). Suppose they do not. The No condition at `σ = 1` gives a formula
`φ_j` that this set of variables falsifies, so every term `τ` of `φ_j` (`T ≤ Δ` of them) has a
literal at a position `q_τ` whose variable `v_τ` has `f v_τ ∉ cand h v_τ`.
- Base points have formula index `j`. They carry a word `z_τ` and a mask bit `y_τ` at the slot
  `(τ, q_τ)` of each term, and zero at every other slot.
- So the other slots of term `τ` contribute a constant `R_τ`, and term `τ` has parity
  `y_τ + E_τ(z_τ)`, where `E_τ(z) = (f v_τ)^{⊕k}(z) + R_τ`.
- When every `y_τ = E_τ(z_τ) + b`, all terms have parity `b`, so the entry is `b` and `h`
  returns `b`. The bit `b` is thus XOR-shared across the `T` channels `E_τ`.
- The hybrid argument with fixed coins (`Cslib.exists_card_add_decode_update_eq`) finds a
  channel `τ`, values at the other slots and a bit `y₀`. For these, `y₀ + h(…)` predicts `E_τ`
  on a `1 / 2 + 1 / (2 T) ≥ 1 / 2 + 1 / (2 Δ)` fraction of the words.
- The constant `R_τ` goes into the advice bit `c = y₀ + R_τ`, so `f v_τ ∈ cand h v_τ`. This is a
  contradiction.

The union bound over circuits and the probability over `f` are the next milestone of #4362.

## Main definitions

* `Cslib.PartialMCSP.FromCMMSA.cand`: the candidates for `f v` determined by a circuit `h`.

## Main results

* `Cslib.PartialMCSP.FromCMMSA.card_cand_le`: there are at most
  `4 Δ⁴ 2 ^ A exp (2 ^ ℓ v H(δ₀))` candidates.
* `Cslib.PartialMCSP.FromCMMSA.lt_weight_cand`: for a No instance, the variables whose function
  is a candidate weigh more than `g θ`.

## References

* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
* [A. C. Yao, *Theory and Application of Trapdoor Functions*][Yao1982]
-/

public section

namespace Cslib.PartialMCSP.FromCMMSA

open Cslib.Complexity Cslib.Logic.PL Cslib.Circuits.Boolean Finset Function

variable {I : CMMSAInstance} {Δ k lam : ℕ}

/-! ### Splitting an input into its parts -/

variable (I Δ k lam) in
/-- An input of the table, split into its parts. -/
@[ext] private structure Parts where
  /-- The formula-index bits. -/
  index : BitString (indexWidth I)
  /-- The `k` seeds of each slot `(t, q)`. -/
  seeds : Fin Δ × Fin Δ → Fin k → BitString (seedWidth I lam)
  /-- The mask bit of each slot `(t, q)`. -/
  masks : Fin Δ × Fin Δ → Bool

variable (I Δ k lam) in
/-- The parts as a triple. -/
private def Parts.equivProd : Parts I Δ k lam ≃
    BitString (indexWidth I) × (Fin Δ × Fin Δ → Fin k → BitString (seedWidth I lam)) ×
      (Fin Δ × Fin Δ → Bool) where
  toFun p := (p.index, p.seeds, p.masks)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : Fintype (Parts I Δ k lam) := Fintype.ofEquiv _ (Parts.equivProd I Δ k lam).symm

/-- The input with the given parts. -/
private def Parts.toInput (p : Parts I Δ k lam) : BitString (inputLength I Δ k lam) :=
  Fin.append p.index fun s =>
    Fin.snoc (α := fun _ => Bool)
      (fun r : Fin (k * seedWidth I lam) =>
        p.seeds (finProdFinEquiv.symm (finProdFinEquiv.symm s).1)
          (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2)
      (p.masks (finProdFinEquiv.symm (finProdFinEquiv.symm s).1)) (finProdFinEquiv.symm s).2

@[simp] private theorem Parts.toInput_indexPos (p : Parts I Δ k lam) (i : Fin (indexWidth I)) :
    p.toInput (indexPos I Δ k lam i) = p.index i := by
  simp [Parts.toInput, indexPos]

@[simp] private theorem Parts.toInput_seedPos (p : Parts I Δ k lam) (t q : Fin Δ) (i : Fin k)
    (r : Fin (seedWidth I lam)) : p.toInput (seedPos I Δ k lam t q i r) = p.seeds (t, q) i r := by
  simp only [Parts.toInput, seedPos, slotPos, Fin.append_right, Equiv.symm_apply_apply]
  exact (Fin.snoc_castSucc (α := fun _ => Bool) ..).trans (by rw [Equiv.symm_apply_apply])

@[simp] private theorem Parts.toInput_maskPos (p : Parts I Δ k lam) (t q : Fin Δ) :
    p.toInput (maskPos I Δ k lam t q) = p.masks (t, q) := by
  simp only [Parts.toInput, maskPos, slotPos, Fin.append_right, Equiv.symm_apply_apply]
  exact Fin.snoc_last (α := fun _ => Bool) ..

@[simp] private theorem Parts.formulaIndex_toInput (p : Parts I Δ k lam) :
    formulaIndex p.toInput = BitString.equivFin _ p.index := by
  simp [formulaIndex]

@[simp] private theorem Parts.seed_toInput (p : Parts I Δ k lam) (t q : Fin Δ) (i : Fin k) :
    seed p.toInput t q i = p.seeds (t, q) i := by
  funext r
  simp [seed]

private theorem Parts.slotBit_toInput (f : VarFunctions I lam) (p : Parts I Δ k lam) (t q : Fin Δ) :
    slotBit f p.toInput t q =
      p.masks (t, q) + ∑ i : Fin k,
        evalVar f (var I (BitString.equivFin _ p.index) t q) (p.seeds (t, q) i) := by
  simp [slotBit]

private theorem card_parts : Fintype.card (Parts I Δ k lam) = 2 ^ inputLength I Δ k lam := by
  simp only [Fintype.card_congr (Parts.equivProd I Δ k lam), Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool, inputLength, slotWidth]
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

/-! ### Seeds carrying a word -/

/-- The `k` seeds whose low `ℓ` bits are the blocks of `z` and whose other bits are zero. -/
private def seedsOf {ℓ : ℕ} (z : BitString (k * ℓ)) (i : Fin k) : BitString (seedWidth I lam) :=
  BitString.zeroExtend (BitString.block z i)

/-- **The bridge to the `k`-fold XOR.** Evaluating `f v` on the seeds that carry `z` gives
`xorPower (f v) k z`. -/
private theorem sum_evalVar_seedsOf (f : VarFunctions I lam) (v : Fin I.weights.length)
    (z : BitString (k * varLength I lam v)) :
    ∑ i : Fin k, evalVar f v (seedsOf (I := I) (lam := lam) z i) = xorPower (f v) k z := by
  rw [xorPower_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hle := varLength_le_seedWidth (I := I) (lam := lam) v.isLt
  simp only [evalVar, v.isLt, dite_true, seedsOf]
  congr 1
  funext r
  simp [BitString.zeroExtend, r.isLt, lt_of_lt_of_le r.isLt hle]

/-- Writing the word `z` into the seeds of slot `tq`. -/
private def Parts.write (p : Parts I Δ k lam) (tq : Fin Δ × Fin Δ) {ℓ : ℕ} (z : BitString (k * ℓ)) :
    Parts I Δ k lam :=
  { p with seeds := update p.seeds tq (seedsOf z) }

/-! ### Candidates -/

open Classical in
/-- **The candidates for `f v`.** The Boolean functions `g` on `ℓ v` inputs whose `k`-fold XOR,
plus a constant bit `c`, agrees with the guess `z ↦ h (write p tq z)` on at least a
`1 / 2 + 1 / (2 Δ)` fraction of the words `z`, for some parts `p`, slot `tq` and bit `c`. -/
noncomputable def cand (h : BooleanFunction (inputLength I Δ k lam)) (v : Fin I.weights.length) :
    Finset (BooleanFunction (varLength I lam v)) :=
  univ.filter fun g => ∃ (p : Parts I Δ k lam) (tq : Fin Δ × Fin Δ) (c : Bool),
    (1 / 2 + 1 / (2 * Δ) : ℝ) * 2 ^ (k * varLength I lam v) ≤
      #{z : BitString (k * varLength I lam v) | xorPower g k z = c + h (p.write tq z).toInput}

/-- **There are few candidates.** For odd `k` with `(1 - 2 δ₀) ^ k ≤ 1 / (2 Δ ^ 2)`, at most
`4 Δ ^ 4 2 ^ A exp (2 ^ ℓ H(δ₀))` functions are candidates for `f v`, where `A` is the input length
and `ℓ = ℓ v`. -/
theorem card_cand_le (hk : Odd k) (hΔ : 0 < Δ) {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) (hδ₀' : δ₀ ≤ 1 / 2)
    (hkδ : (1 - 2 * δ₀) ^ k ≤ 1 / (2 * Δ ^ 2)) (h : BooleanFunction (inputLength I Δ k lam))
    (v : Fin I.weights.length) :
    (#(cand h v) : ℝ) ≤
      4 * Δ ^ 4 * 2 ^ inputLength I Δ k lam *
        Real.exp (2 ^ varLength I lam v * Real.binEntropy δ₀) := by
  classical
  have hΔ' : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hε0 : (0 : ℝ) ≤ 1 / (2 * Δ) := by positivity
  have h2ε : 2 * (1 / (2 * Δ) : ℝ) ^ 2 = 1 / (2 * Δ ^ 2) := by field_simp
  -- the candidates of one choice of advice
  let L : Parts I Δ k lam × (Fin Δ × Fin Δ) × Bool →
      Finset (BooleanFunction (varLength I lam v)) := fun a =>
    univ.filter fun g => (1 / 2 + 1 / (2 * Δ) : ℝ) * 2 ^ (k * varLength I lam v) ≤
      #{z : BitString (k * varLength I lam v) |
        xorPower g k z = a.2.2 + h (a.1.write a.2.1 z).toInput}
  have hsub : cand h v ⊆ univ.biUnion L := by
    intro g hg
    obtain ⟨p, tq, c, hp⟩ := (mem_filter.1 hg).2
    exact mem_biUnion.2 ⟨(p, tq, c), mem_univ _, mem_filter.2 ⟨mem_univ _, hp⟩⟩
  have hL (a : Parts I Δ k lam × (Fin Δ × Fin Δ) × Bool) :
      (#(L a) : ℝ) ≤ 2 * Δ ^ 2 * Real.exp (2 ^ varLength I lam v * Real.binEntropy δ₀) := by
    have := card_filter_xorPower_mul_two_mul_sq_le_exp (n := varLength I lam v) hk
      (fun z => a.2.2 + h (a.1.write a.2.1 z).toInput) hε0 hδ₀ hδ₀' (h2ε ▸ hkδ)
    rw [h2ε] at this
    have h2 : (0 : ℝ) < 1 / (2 * Δ ^ 2) := by positivity
    calc (#(L a) : ℝ) = #(L a) * (1 / (2 * Δ ^ 2)) * (2 * Δ ^ 2) := by field_simp
      _ ≤ Real.exp (2 ^ varLength I lam v * Real.binEntropy δ₀) * (2 * Δ ^ 2) := by
          gcongr
      _ = _ := by ring
  have hcard : Fintype.card (Parts I Δ k lam × (Fin Δ × Fin Δ) × Bool) =
      2 ^ inputLength I Δ k lam * (Δ ^ 2 * 2) := by
    rw [Fintype.card_prod, card_parts, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool]
    ring
  calc (#(cand h v) : ℝ) ≤ #(univ.biUnion L) := by exact_mod_cast card_le_card hsub
    _ ≤ ∑ a, (#(L a) : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _a : Parts I Δ k lam × (Fin Δ × Fin Δ) × Bool,
          2 * Δ ^ 2 * Real.exp (2 ^ varLength I lam v * Real.binEntropy δ₀) :=
        sum_le_sum fun a _ => hL a
    _ = _ := by
        rw [sum_const, card_univ, hcard, nsmul_eq_mul]
        push_cast
        ring

/-! ### The knowledge set is heavy -/

/-- The parity of a term, split at one of its occupied slots `q₀`. -/
private theorem termParity_eq_add {f : VarFunctions I lam} {x : BitString (inputLength I Δ k lam)}
    {t q₀ : Fin Δ} (hq₀ : (q₀ : ℕ) < (term I (formulaIndex x) t).length) :
    termParity f x t = slotBit f x t q₀ +
      ∑ q ∈ univ.erase q₀,
        if (q : ℕ) < (term I (formulaIndex x) t).length then slotBit f x t q else 0 := by
  unfold termParity
  rw [← Finset.add_sum_erase _ _ (mem_univ q₀), ite_eq_left hq₀]

/-- **The knowledge set of a circuit is heavy** (the core of No soundness). Let `I` be a No
instance of `GapCMMSA Δ g 1`, and let `h` agree with the table of `I` for the functions `f`. Then
the variables `v` with `f v ∈ cand h v` have total weight above `g θ`. -/
theorem lt_weight_cand {g : ℝ} (hI : I ∈ (GapCMMSA Δ g 1).no) (P : ℕ) (f : VarFunctions I lam)
    (h : BooleanFunction (inputLength I Δ k lam)) (hh : (toInstance I Δ k lam P f).AgreesWith h) :
    g * I.threshold <
      I.weight ((univ.filter fun v : Fin I.weights.length => f v ∈ cand h v).map Fin.valEmbedding)
    := by
  classical
  obtain ⟨hwf, -, hno⟩ := mem_no_GapCMMSA_one.1 hI
  set K := (univ.filter fun v : Fin I.weights.length => f v ∈ cand h v).map Fin.valEmbedding
    with hK
  by_contra hlt
  obtain ⟨φ', hφ'mem, hφ'⟩ := hno K (fun v hv => by
    obtain ⟨u, -, rfl⟩ := mem_map.1 hv
    exact mem_range.2 u.isLt) (not_lt.1 hlt)
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hφ'mem
  set φ := I.formulas[j] with hφ
  set T := φ.length with hT
  have hTΔ : T ≤ Δ := hwf.length_le hφ'mem
  have hT0 : 0 < T := List.length_pos_iff.2 (hwf.formula_ne_nil _ hφ'mem)
  -- every term has a literal whose variable lies outside `K`
  have hlit (τ : Fin T) : ∃ q : ℕ, ∃ hq : q < φ[(τ : ℕ)].length,
      ∃ hv : φ[(τ : ℕ)][q].1 < I.weights.length, f ⟨_, hv⟩ ∉ cand h ⟨_, hv⟩ := by
    have hτ : φ[(τ : ℕ)] ∈ φ := List.getElem_mem _
    have hfalse : Term.eval (fun i => decide (i ∈ K)) φ[(τ : ℕ)] = false := by
      have := hφ'
      simp only [DNF.eval, List.any_eq_false] at this
      simpa using this _ hτ
    have : ∃ l ∈ φ[(τ : ℕ)], decide (l.1 ∈ K) ≠ l.2 := by
      by_contra hall
      push Not at hall
      rw [(Term.eval_eq_true_iff (fun i => decide (i ∈ K)) _).2 hall] at hfalse
      exact Bool.noConfusion hfalse
    obtain ⟨l, hl, hlK⟩ := this
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hl
    have hv := hwf.var_lt _ hφ'mem _ hτ _ hl
    refine ⟨q, hq, hv, fun hmem => hlK ?_⟩
    rw [hwf.monotone _ hφ'mem _ hτ _ hl, decide_eq_true_iff, hK]
    exact mem_map.2 ⟨⟨_, hv⟩, mem_filter.2 ⟨mem_univ _, hmem⟩, rfl⟩
  choose qs hqs hvs hqK using hlit
  have hTΔ' (τ : Fin T) : (τ : ℕ) < Δ := lt_of_lt_of_le τ.isLt hTΔ
  have hqΔ (τ : Fin T) : qs τ < Δ :=
    lt_of_lt_of_le (hqs τ) (hwf.length_term_le hφ'mem (List.getElem_mem _))
  let vs (τ : Fin T) : Fin I.weights.length := ⟨_, hvs τ⟩
  let sl (τ : Fin T) : Fin Δ × Fin Δ := (⟨τ, hTΔ' τ⟩, ⟨qs τ, hqΔ τ⟩)
  -- the term chosen at a slot, if any
  obtain ⟨inv, hinv_sl, hinv_none, hinv_ne⟩ : ∃ inv : Fin Δ × Fin Δ → Option (Fin T),
      (∀ τ, inv (sl τ) = some τ) ∧ (∀ τ q, q ≠ (sl τ).2 → inv ((sl τ).1, q) = none) ∧
      (∀ τ tq, tq ≠ sl τ → inv tq ≠ some τ) := by
    refine ⟨fun tq => if ht : (tq.1 : ℕ) < T then
      if (tq.2 : ℕ) = qs ⟨tq.1, ht⟩ then some ⟨tq.1, ht⟩ else none else none, ?_, ?_, ?_⟩
    · intro τ
      simp [sl, τ.isLt]
    · intro τ q hq
      have hq' : (q : ℕ) ≠ qs τ := fun he => hq (Fin.ext he)
      simp [sl, τ.isLt, hq']
    · intro τ tq htq he
      simp only at he
      split_ifs at he with h1 h2
      cases he
      exact htq (Prod.ext (Fin.ext rfl) (Fin.ext h2))
  -- the formula-index bits of `j`
  have hjW : j < 2 ^ indexWidth I := lt_of_lt_of_le hj (Nat.le_pow_clog one_lt_two _)
  let a : BitString (indexWidth I) := (BitString.equivFin _).symm ⟨j, hjW⟩
  have ha : (BitString.equivFin _ a : ℕ) = j := by simp [a]
  -- the parts carrying the words `w τ` at the chosen slots, with every other slot zero
  let mk (w : ∀ τ : Fin T, BitString (k * varLength I lam (vs τ)) × Bool) : Parts I Δ k lam :=
    { index := a
      seeds tq := (inv tq).elim (fun _ _ => false) fun τ => seedsOf (w τ).1
      masks tq := (inv tq).elim false fun τ => (w τ).2 }
  have hmk_idx (w) : formulaIndex (mk w).toInput = j := by
    rw [Parts.formulaIndex_toInput]; exact ha
  -- the contribution of the other slots of term `τ`, which are zero
  let R (τ : Fin T) : Bool := ∑ q ∈ univ.erase (sl τ).2,
    if (q : ℕ) < (term I j (sl τ).1).length then
      ∑ _i : Fin k, evalVar f (var I j (sl τ).1 q) (fun _ : Fin (seedWidth I lam) => false)
    else 0
  let E (τ : Fin T) (z : BitString (k * varLength I lam (vs τ))) : Bool :=
    xorPower (f (vs τ)) k z + R τ
  let D (w : ∀ τ : Fin T, BitString (k * varLength I lam (vs τ)) × Bool) : Bool :=
    h (mk w).toInput
  -- `h` decodes the XOR-shared bit
  have hD (z : ∀ τ : Fin T, BitString (k * varLength I lam (vs τ))) (b : Bool) :
      D (fun τ => (z τ, E τ (z τ) + b)) = b := by
    set w : ∀ τ : Fin T, BitString (k * varLength I lam (vs τ)) × Bool :=
      fun τ => (z τ, E τ (z τ) + b) with hw
    have hidx := hmk_idx w
    apply hh
    change entry f ((BitString.equivFin _).symm (BitString.equivFin _ (mk w).toInput)) = some b
    rw [Equiv.symm_apply_apply]
    have hlen : (I.formulas.getD j []).length = T := by
      simp [List.getD_eq_getElem?_getD, hj, hT, hφ]
    refine entry_eq_some_of_forall_termParity (by rw [hidx]; exact hj)
      ⟨⟨0, lt_of_lt_of_le hT0 hTΔ⟩, by rw [hidx, hlen]; exact hT0⟩ ?_
    intro t ht
    rw [hidx, hlen] at ht
    obtain ⟨τ, rfl⟩ : ∃ τ : Fin T, (sl τ).1 = t := ⟨⟨t, ht⟩, Fin.ext rfl⟩
    have hterm : term I j (sl τ).1 = φ[(τ : ℕ)] := term_eq_getElem hj τ.isLt
    have hq₀ : ((sl τ).2 : ℕ) < (term I (formulaIndex (mk w).toInput) (sl τ).1).length := by
      rw [hidx, hterm]; exact hqs τ
    have hvar : var I j (sl τ).1 (sl τ).2 = (vs τ : ℕ) := by
      simp only [var, hterm, List.getD_eq_getElem?_getD]
      simp [sl, vs, hqs τ]
    have hfirst : slotBit f (mk w).toInput (sl τ).1 (sl τ).2 =
        E τ (z τ) + b + xorPower (f (vs τ)) k (z τ) := by
      rw [Parts.slotBit_toInput, ha, hvar]
      simp only [mk, hinv_sl, Option.elim_some, hw]
      rw [sum_evalVar_seedsOf]
    have hrest : (∑ q ∈ univ.erase (sl τ).2,
        if (q : ℕ) < (term I (formulaIndex (mk w).toInput) (sl τ).1).length then
          slotBit f (mk w).toInput (sl τ).1 q else 0) = R τ := by
      rw [hidx]
      refine sum_congr rfl fun q hq => ?_
      have hnone := hinv_none τ q (ne_of_mem_erase hq)
      split_ifs
      · rw [Parts.slotBit_toInput, ha]
        simp only [mk, hnone, Option.elim_none]
        exact zero_add _
      · rfl
    rw [termParity_eq_add hq₀, hfirst, hrest]
    simp only [E]
    generalize xorPower (f (vs τ)) k (z τ) = x
    generalize R τ = r
    cases x <;> cases r <;> cases b <;> rfl
  -- the hybrid argument finds a channel `h` predicts
  obtain ⟨τ, base, y₀, hcount⟩ := exists_card_add_decode_update_eq E D hD
  set p₀ : Parts I Δ k lam := { mk base with masks := update (mk base).masks (sl τ) y₀ }
    with hp₀
  have hwrite (z : BitString (k * varLength I lam (vs τ))) :
      p₀.write (sl τ) z = mk (update base τ (z, y₀)) := by
    simp only [Parts.write, hp₀, mk]
    refine Parts.ext rfl ?_ ?_ <;> funext tq <;> dsimp only <;>
      by_cases htq : tq = sl τ
    · subst htq
      simp [hinv_sl]
    · rw [update_of_ne htq]
      cases hi : inv tq with
      | none => simp
      | some τ' =>
        have hτ' : τ' ≠ τ := fun he => hinv_ne τ tq htq (he ▸ hi)
        simp [update_of_ne hτ']
    · subst htq
      simp [hinv_sl]
    · rw [update_of_ne htq]
      cases hi : inv tq with
      | none => simp
      | some τ' =>
        have hτ' : τ' ≠ τ := fun he => hinv_ne τ tq htq (he ▸ hi)
        simp [update_of_ne hτ']
  have hmem : f (vs τ) ∈ cand h (vs τ) := by
    refine mem_filter.2 ⟨mem_univ _, p₀, sl τ, y₀ + R τ, ?_⟩
    have hcard : #{z : BitString (k * varLength I lam (vs τ)) |
          xorPower (f (vs τ)) k z = y₀ + R τ + h (p₀.write (sl τ) z).toInput} =
        #{z : BitString (k * varLength I lam (vs τ)) |
          y₀ + D (update base τ (z, y₀)) = E τ z} := by
      congr 1
      refine filter_congr fun z _ => ?_
      rw [hwrite]
      simp only [D, E]
      generalize h (mk (update base τ (z, y₀))).toInput = u
      generalize xorPower (f (vs τ)) k z = x
      generalize R τ = r
      cases u <;> cases x <;> cases r <;> cases y₀ <;> decide
    rw [hcard]
    have hc : (2 : ℝ) ^ (k * varLength I lam (vs τ)) * (T + 1) ≤
        2 * T * #{z : BitString (k * varLength I lam (vs τ)) |
          y₀ + D (update base τ (z, y₀)) = E τ z} := by
      have := hcount
      rw [BitString.card] at this
      exact_mod_cast this
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT0
    have hTΔ' : (T : ℝ) ≤ Δ := by exact_mod_cast hTΔ
    calc (1 / 2 + 1 / (2 * Δ) : ℝ) * 2 ^ (k * varLength I lam (vs τ))
        ≤ (1 / 2 + 1 / (2 * T)) * 2 ^ (k * varLength I lam (vs τ)) := by gcongr
      _ = 2 ^ (k * varLength I lam (vs τ)) * (T + 1) / (2 * T) := by field_simp
      _ ≤ _ := by rw [div_le_iff₀ (by positivity)]; linarith
  exact hqK τ hmem

end Cslib.PartialMCSP.FromCMMSA
