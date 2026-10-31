/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BQP
public import Complexity.Computability.Circuit.Quantum.Counter
public import Complexity.Computability.Circuit.Quantum.Parallel
import Complexity.Foundations.Combinatorics.MajorityVote.Weighted
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Error reduction for `BQP`

The error `1 / 3` in the definition of `BQP` (`Cslib.Complexity.BQP`) can be made exponentially
small: `A ∈ BQP enc` exactly when for every polynomial `q` some uniform family accepts members with
probability at least `1 - 2^{-q(n)}` and other instances with probability at most `2^{-q(n)}`, where
`n` is the length of the encoded instance (`Cslib.Complexity.mem_BQP_iff_forall_errorExponent`).

This is the majority-vote error reduction of `BPP`
(`Cslib.Complexity.mem_BPP_iff_forall_decidesWithErrorExponent`), carried out inside a quantum
circuit, since acceptance is the measurement of a single qubit at the end. The amplified family
(`Cslib.Quantum.UniformCircuitFamily.amplify`) runs `2 r` copies of the circuit side by side and
takes a reversible majority vote of their answers. On inputs of length `n` its register holds the
input, `2 r` blocks of the original width `w`, and the ancillas of a threshold counter:

1. CNOT gates copy the input into each block (`Cslib.Quantum.Amplify.copyCodes`);
2. each block runs the original circuit, with its qubit numbers shifted
   (`Cslib.Quantum.Amplify.copiesCodes`);
3. a reversible counter computes whether more than `r` of the blocks' first qubits are one
   (`Cslib.Quantum.Counter.codes`);
4. three CNOT gates swap that answer into qubit `0` (`Cslib.Quantum.GateCode.swapCodes`).

The copies act on disjoint blocks, so their measurement outcomes are independent
(`Cslib.Quantum.Circuit.matrix_flatMap_mapWires`), and the classical steps permute the outcomes. The
acceptance probability of the amplified family is therefore the probability that a strict majority
of `2 r` independent trials succeed, each with the original acceptance probability
(`Cslib.Quantum.UniformCircuitFamily.acceptProb_amplify`). The exponential-moment bound
`Cslib.sum_prod_le_of_card_filter_le` makes the error at most `(8 / 9) ^ r`, and `r = 6 q` gives
`2^{-q}`.

## Main definitions

* `Cslib.Quantum.Amplify.codes`, `Cslib.Quantum.Amplify.width`: the amplified circuit.
* `Cslib.Quantum.UniformCircuitFamily.amplify`: the amplified family.

## Main results

* `Cslib.Quantum.UniformCircuitFamily.acceptProb_amplify`: the acceptance probability of the
  amplified family is that of a strict majority of independent copies.
* `Cslib.Complexity.mem_BQP_iff_forall_errorExponent`: error reduction for `BQP`.

The argument is the standard one; no source locator is claimed for it. `BQP` itself follows
[Bernstein, Vazirani][BernsteinVazirani1997] and [Arora, Barak][AroraBarak09] (see
`Cslib.Complexity.BQP`).

## References

* [E. Bernstein, U. Vazirani, *Quantum complexity theory*][BernsteinVazirani1997]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Quantum

open Finset GateCode Turing.MultiTapeTM

namespace Amplify

/-- CNOT gates copying the first `n` qubits into the blocks `1, …, k` of width `w`. -/
def copyCodes (n w k : ℕ) : List GateCode :=
  (List.range k).flatMap fun j => (List.range n).map fun i => (false, i + (j + 1) * w, [i])

/-- The circuit `gs` on each of the blocks `1, …, k` of width `w`. -/
def copiesCodes (w k : ℕ) (gs : List GateCode) : List GateCode :=
  (List.range k).flatMap fun j => gs.map (shift ((j + 1) * w))

/-- The first ancilla of the counter, after the input block and `2 r` copies of width `w`. -/
def base (w r : ℕ) : ℕ := (2 * r + 1) * w

/-- The register width of the amplified circuit: the blocks and the counter's ancillas. -/
def width (w r : ℕ) : ℕ := base w r + 1 + (2 * r + 1) * (r + 1)

/-- The counter's qubit that reads whether more than `r` of the `2 r` copies accept. -/
def answer (w r : ℕ) : ℕ := Counter.level (base w r) (r + 1) (2 * r) r

/-- **The amplified circuit**: copy the input of length `n` into `2 r` blocks of width `w`, run
the circuit `gs` on each, count the blocks whose first qubit is one, and swap the strict majority
into qubit `0`. -/
def codes (n w r : ℕ) (gs : List GateCode) : List GateCode :=
  copyCodes n w (2 * r) ++ (copiesCodes w (2 * r) gs ++
    (Counter.codes (base w r) (r + 1) (fun s => (s + 1) * w) (2 * r) ++ swapCodes (answer w r)))

variable {n w r : ℕ}

theorem base_eq (w r : ℕ) : base w r = 2 * r * w + w := by
  unfold base
  rw [Nat.add_mul, Nat.one_mul]

theorem block_lt {j i : ℕ} (hj : j < 2 * r) (hi : i < w) :
    i + (j + 1) * w < base w r := by
  have := Nat.mul_le_mul_right w (show j + 1 ≤ 2 * r by omega)
  rw [base_eq]
  omega

theorem base_lt_width : base w r < width w r := by
  unfold width
  omega

theorem answer_lt_width : answer w r < width w r := by
  unfold answer width Counter.level
  have : 2 * r * (r + 1) + r < (2 * r + 1) * (r + 1) := by
    rw [Nat.add_mul (2 * r), Nat.one_mul]
    omega
  omega

theorem base_le_answer : base w r ≤ answer w r := by
  unfold answer Counter.level
  omega

/-- The blocks `1, …, 2 r` of the amplified register. -/
def blocks (w r : ℕ) : Fin (2 * r) × Fin w ↪ Fin (width w r) where
  toFun p := ⟨p.2 + (p.1 + 1) * w, (block_lt p.1.2 p.2.2).trans base_lt_width⟩
  inj' p p' h := by
    have h' : (p.2 : ℕ) + (p.1 + 1) * w = p'.2 + (p'.1 + 1) * w := congrArg Fin.val h
    have hw : 0 < w := Nat.lt_of_le_of_lt (Nat.zero_le _) p.2.2
    have hmod := congrArg (· % w) h'
    have hdiv := congrArg (· / w) h'
    simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.2.2,
      Nat.mod_eq_of_lt p'.2.2] at hmod
    simp only [Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt p.2.2,
      Nat.div_eq_of_lt p'.2.2] at hdiv
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext hmod)

@[simp] theorem blocks_apply_val (p : Fin (2 * r) × Fin w) :
    (blocks w r p : ℕ) = p.2 + (p.1 + 1) * w := rfl

theorem block_le_width {j : ℕ} (hj : j < 2 * r) : (j + 1) * w + w ≤ width w r := by
  have := Nat.mul_le_mul_right w (show j + 1 ≤ 2 * r by omega)
  have : base w r < width w r := base_lt_width
  rw [base_eq] at this
  omega

/-- Block `j` of the amplified register. -/
def block (j : Fin (2 * r)) : Fin w ↪ Fin (width w r) :=
  blockEmb ((j + 1) * w) (block_le_width j.2)

theorem block_apply (j : Fin (2 * r)) (i : Fin w) : block j i = blocks w r (j, i) := rfl

/-! ### The classical steps -/

theorem isClassical_copyCodes (hn : n ≤ w) (hw : 0 < w) :
    IsClassical (width w r) (copyCodes n w (2 * r)) := by
  refine IsClassical.flatMap fun j hj => fun g hg => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
  have hj : j < 2 * r := List.mem_range.mp hj
  have hi : i < n := List.mem_range.mp hi
  have hlt := (block_lt (r := r) hj (show i < w by omega)).trans base_lt_width
  have : 0 < (j + 1) * w := Nat.mul_pos (by omega) hw
  refine ⟨rfl, by simp, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      not_false_eq_true, and_true]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    omega

/-- **The copy step puts the input in every block**, and leaves the other qubits unchanged. -/
theorem readBit_classicalRun_copyCodes (hn : n ≤ w) (hw : 0 < w) (X : Fin (width w r) → Bool)
    (hX : ∀ p, n ≤ p → readBit X p = false) (p : ℕ) :
    readBit (classicalRun (copyCodes n w (2 * r)) X) p =
      if ∃ j < 2 * r, ∃ i < w, p = i + (j + 1) * w then readBit X (p % w) else readBit X p := by
  have hread : ∀ g ∈ copyCodes n w (2 * r), ∀ g' ∈ copyCodes n w (2 * r), g.2.1 ∉ g'.2.2 := by
    intro g hg g' hg'
    simp only [copyCodes, List.mem_flatMap, List.mem_map, List.mem_range] at hg hg'
    obtain ⟨j, hj, i, hi, rfl⟩ := hg
    obtain ⟨j', hj', i', hi', rfl⟩ := hg'
    have : w ≤ (j + 1) * w := Nat.le_mul_of_pos_left w (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  rw [readBit_classicalRun_of_forall_notMem (isClassical_copyCodes hn hw) hread, copyCodes,
    List.foldl_flatMap]
  -- each block contributes the exclusive or of its copies of the input bits
  have hinner (b : Bool) (j : ℕ) :
      ((List.range n).map fun i => ((false, i + (j + 1) * w, [i]) : GateCode)).foldl
        (fun b g => b ^^ (decide (p = g.2.1) && g.2.2.all (readBit X))) b =
      (b ^^ (decide (∃ i < n, p = i + (j + 1) * w) && readBit X (p % w))) := by
    rw [List.foldl_map]
    by_cases hp : ∃ i < n, p = i + (j + 1) * w
    · obtain ⟨i₀, hi₀, rfl⟩ := hp
      rw [foldl_xor_range n i₀ _ _ fun i _ hne => by simp [Ne.symm hne]]
      simp [hi₀, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (show i₀ < w by omega)]
    · have hp' : ∀ i < n, p ≠ i + (j + 1) * w := fun i hi h => hp ⟨i, hi, h⟩
      rw [foldl_xor_range n n _ _ fun i hi _ => by simp [hp' i hi]]
      simp [hp]
  simp only [hinner]
  by_cases hp : ∃ j < 2 * r, ∃ i < w, p = i + (j + 1) * w
  · obtain ⟨j₀, hj₀, i₀, hi₀, rfl⟩ := hp
    rw [ite_eq_left ⟨j₀, hj₀, i₀, hi₀, rfl⟩, foldl_xor_range (2 * r) j₀ _ _ fun j _ hne => ?_]
    · have hw' : w ≤ (j₀ + 1) * w := Nat.le_mul_of_pos_left w (by omega)
      rw [hX _ (by omega), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi₀]
      by_cases hi : i₀ < n
      · simp [hj₀, hi]
      · simp [hj₀, hi, hX i₀ (by omega)]
    · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      left
      rintro ⟨i, hi, h⟩
      have hmod := congrArg (· / w) h
      simp only [Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hi₀,
        Nat.div_eq_of_lt (show i < w by omega)] at hmod
      omega
  · rw [ite_eq_right hp, foldl_xor_range (2 * r) (2 * r) _ _ fun j hj _ => ?_]
    · simp
    · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      exact Or.inl fun ⟨i, hi, h⟩ => hp ⟨j, hj, i, by omega, h⟩

theorem isClassical_counter_swap (hw : 0 < w) :
    IsClassical (width w r) (Counter.codes (base w r) (r + 1) (fun s => (s + 1) * w) (2 * r) ++
      swapCodes (answer w r)) := by
  refine IsClassical.append.mpr ⟨Counter.isClassical_codes (fun s hs => ?_) le_rfl,
    isClassical_swapCodes ?_ answer_lt_width⟩
  · have := block_lt (r := r) hs hw
    omega
  · have : 0 < base w r := Nat.mul_pos (by omega) hw
    have := base_le_answer (w := w) (r := r)
    omega

/-- **The classical steps accept by strict majority**: on a register whose qubits from the counter
on are zero, the counter and the swap leave in qubit `0` whether more than `r` of the blocks' first
qubits are one. -/
theorem readBit_classicalRun_counter_swap (hw : 0 < w) (Y : Fin (width w r) → Bool)
    (hY : ∀ p, base w r ≤ p → readBit Y p = false) :
    readBit (classicalRun (Counter.codes (base w r) (r + 1) (fun s => (s + 1) * w) (2 * r) ++
      swapCodes (answer w r)) Y) 0 =
      decide (r < Counter.count Y (fun s => (s + 1) * w) (2 * r)) := by
  rw [classicalRun_append, readBit_classicalRun_swapCodes _ answer_lt_width]
  · exact (Counter.readBit_classicalRun_codes (fun s hs => by
      have := block_lt (r := r) hs hw; omega) le_rfl Y hY).2 r (by omega)
  · have : 0 < base w r := Nat.mul_pos (by omega) hw
    have := base_le_answer (w := w) (r := r)
    omega

/-! ### The parallel copies -/

theorem ofCodes_copiesCodes {gs : List GateCode} (hgs : ∀ g ∈ gs, WellFormed w g) :
    Circuit.ofCodes (width w r) (copiesCodes w (2 * r) gs) =
      ((List.finRange (2 * r)).map block).flatMap (Circuit.mapWires · (Circuit.ofCodes w gs)) := by
  rw [copiesCodes, Circuit.ofCodes_flatMap, ← List.map_coe_finRange_eq_range, List.flatMap_map,
    List.flatMap_map]
  congr 1
  funext j
  exact Circuit.ofCodes_map_shift _ hgs

theorem pairwise_block :
    ((List.finRange (2 * r)).map (block (w := w))).Pairwise fun e e' => ∀ i i', e i ≠ e' i' := by
  rw [List.pairwise_map]
  refine (List.nodup_finRange _).imp fun {j j'} hjj' i i' h => hjj' ?_
  rw [block_apply, block_apply] at h
  exact congrArg Prod.fst ((blocks w r).injective h)

end Amplify

/-! ### Acceptance probability of the amplified circuit -/

/-- Grouping a sum over tuples by a function of their entries. -/
private theorem sum_mul_prod_fiberwise {α κ R : Type*} [Fintype α] [Fintype κ] [DecidableEq κ]
    [CommSemiring R] {k : ℕ} (φ : α → κ) (f : α → R) (G : (Fin k → κ) → R) :
    ∑ y : Fin k → α, G (fun j => φ (y j)) * ∏ j, f (y j) =
      ∑ b : Fin k → κ, G b * ∏ j, ∑ z ∈ univ.filter (fun z => φ z = b j), f z := by
  simp_rw [prod_univ_sum, mul_sum]
  rw [← sum_fiberwise univ (fun y : Fin k → α => fun j => φ (y j))]
  refine sum_congr rfl fun b _ => ?_
  have hset : Fintype.piFinset (fun j => univ.filter fun z => φ z = b j) =
      univ.filter fun y : Fin k → α => (fun j => φ (y j)) = b := by
    ext y
    simp [Fintype.mem_piFinset, funext_iff]
  rw [hset]
  refine sum_congr rfl fun y hy => ?_
  rw [(mem_filter.mp hy).2]

open Amplify in
/-- **The acceptance probability of the amplified circuit** is the probability that more than `r`
of `2 r` independent runs of the original circuit accept. -/
theorem acceptProb_amplify_codes {n w r : ℕ} {gs : List GateCode} (hw : 0 < w) (hn : n ≤ w)
    (hgs : ∀ g ∈ gs, WellFormed w g) (x : List Bool) (hx : x.length = n) :
    acceptProb (width w r) (codes n w r gs) x =
      ∑ b : Fin (2 * r) → Bool with r < (univ.filter fun j => b j = true).card,
        ∏ j, if b j then acceptProb w gs x else 1 - acceptProb w gs x := by
  set N := width w r
  set C := Circuit.ofCodes w gs
  set a : (Fin w → Bool) → ℂ := fun z => (Circuit.run C (inputState w x)).ofLp z
  set X := classicalRun (copyCodes n w (2 * r)) (inputState N x) with hXdef
  have hgetD (p : ℕ) (hp : n ≤ p) : x.getD p false = false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  have hX₀ (p : ℕ) : readBit (inputState N x) p = x.getD p false := by
    by_cases hp : p < N
    · rw [readBit_of_lt _ hp]
      rfl
    · rw [readBit_of_le _ (not_lt.mp hp), hgetD]
      have := (base_lt_width (w := w) (r := r))
      have : w ≤ base w r := by unfold base; exact Nat.le_mul_of_pos_left w (by omega)
      omega
  have hXbit (p : ℕ) := readBit_classicalRun_copyCodes (r := r) hn hw (inputState N x)
    (fun p hp => by rw [hX₀, hgetD p hp]) p
  -- the copy step puts the input in every block and keeps zeros from the counter on
  have hXblock (j : Fin (2 * r)) : X ∘ block j = inputState w x := by
    funext i
    have h := hXbit (i + (j + 1) * w)
    rw [ite_eq_left ⟨j, j.2, i, i.2, rfl⟩, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt i.2, hX₀] at h
    rw [Function.comp_apply, show X (block j i) = readBit X (block j i) from
      (readBit_fin _ _).symm, block_apply, blocks_apply_val, h]
    rfl
  have hXhigh (p : ℕ) (hp : base w r ≤ p) : readBit X p = false := by
    rw [hXbit, ite_eq_right, hX₀, hgetD]
    · have : w ≤ base w r := by unfold base; exact Nat.le_mul_of_pos_left w (by omega)
      omega
    · rintro ⟨j, hj, i, hi, rfl⟩
      exact absurd hp (not_le.mpr (block_lt hj hi))
  -- the amplitudes of the copies are products
  have hamp (Y : Fin N → Bool) :
      (Circuit.eval (Circuit.ofCodes N (copiesCodes w (2 * r) gs)) (ket X)).ofLp Y =
        if AgreeOff (blocks w r) Y X then ∏ j, a (Y ∘ block j) else 0 := by
    rw [Circuit.eval_ket_apply, ofCodes_copiesCodes hgs,
      Circuit.matrix_flatMap_mapWires _ _ pairwise_block]
    have hcond : (∀ p, (∀ e ∈ (List.finRange (2 * r)).map block, ∀ i, e i ≠ p) → Y p = X p) ↔
        AgreeOff (blocks w r) Y X := by
      simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
        forall_apply_eq_imp_iff, AgreeOff, Prod.forall, block_apply]
    rw [if_congr hcond rfl rfl, List.map_map, ← Fin.prod_univ_def]
    refine if_congr Iff.rfl (prod_congr rfl fun j _ => ?_) rfl
    simp only [Function.comp_apply, hXblock, a, Circuit.run, Circuit.eval_ket_apply]
    rfl
  -- the acceptance probability as a sum over the blocks' outcomes
  unfold acceptProb
  rw [codes, Circuit.ofCodes_append, Circuit.ofCodes_append, Circuit.run, Circuit.eval_append,
    Circuit.eval_append, Circuit.eval_ofCodes_ket (isClassical_copyCodes hn hw),
    Circuit.measureProb_eval_ofCodes (isClassical_counter_swap hw), ← hXdef]
  simp only [hamp]
  have hterm (Y : Fin N → Bool) :
      (if classicalRun (Counter.codes (base w r) (r + 1) (fun s => (s + 1) * w) (2 * r) ++
          swapCodes (answer w r)) Y ∈ accepting N then
        ‖(if AgreeOff (blocks w r) Y X then ∏ j, a (Y ∘ block j) else 0)‖ ^ 2 else 0) =
      if AgreeOff (blocks w r) Y X then
        (if r < (univ.filter fun j : Fin (2 * r) => (Y ∘ blocks w r) (j, ⟨0, hw⟩) = true).card
          then (1 : ℝ) else 0) * ∏ j, ‖a (fun i => (Y ∘ blocks w r) (j, i))‖ ^ 2
      else 0 := by
    by_cases hY : AgreeOff (blocks w r) Y X
    · have hYhigh (p : ℕ) (hp : base w r ≤ p) : readBit Y p = false := by
        rw [← hXhigh p hp]
        by_cases hpN : p < N
        · rw [readBit_of_lt _ hpN, readBit_of_lt _ hpN]
          refine hY _ fun q h => ?_
          have := congrArg Fin.val h
          simp only [blocks_apply_val] at this
          exact absurd hp (not_le.mpr (this ▸ block_lt q.1.2 q.2.2))
        · rw [readBit_of_le _ (not_lt.mp hpN), readBit_of_le _ (not_lt.mp hpN)]
      have hbit (j : Fin (2 * r)) : readBit Y ((j + 1) * w) = (Y ∘ blocks w r) (j, ⟨0, hw⟩) := by
        rw [Function.comp_apply, ← readBit_fin Y (blocks w r (j, ⟨0, hw⟩)), blocks_apply_val]
        simp only [Nat.zero_add]
      have hcount : Counter.count Y (fun s => (s + 1) * w) (2 * r) =
          (univ.filter fun j : Fin (2 * r) => (Y ∘ blocks w r) (j, ⟨0, hw⟩) = true).card := by
        unfold Counter.count
        rw [← card_map Fin.valEmbedding]
        congr 1
        ext s
        simp only [mem_filter, mem_range, mem_map, mem_univ, true_and, Fin.valEmbedding_apply,
          Function.comp_apply]
        constructor
        · rintro ⟨hs, h⟩
          exact ⟨⟨s, hs⟩, (hbit ⟨s, hs⟩).symm.trans h, rfl⟩
        · rintro ⟨j, h, rfl⟩
          exact ⟨j.2, (hbit j).trans h⟩
      have hacc : (classicalRun (Counter.codes (base w r) (r + 1) (fun s => (s + 1) * w) (2 * r) ++
          swapCodes (answer w r)) Y ∈ accepting N) ↔
          r < (univ.filter fun j : Fin (2 * r) => (Y ∘ blocks w r) (j, ⟨0, hw⟩) = true).card := by
        have h0 : 0 < N := by have := base_lt_width (w := w) (r := r); omega
        rw [mem_accepting h0, ← readBit_fin (classicalRun _ Y) (⟨0, h0⟩ : Fin N)]
        change readBit _ 0 = true ↔ _
        rw [readBit_classicalRun_counter_swap hw Y hYhigh, hcount, decide_eq_true_iff]
      simp only [hY, ite_true, hacc, norm_prod, ← prod_pow]
      split_ifs <;> simp [block_apply, Function.comp_def]
    · simp [hY]
  simp only [hterm]
  rw [sum_agreeOff_comp (blocks w r) X fun z =>
    (if r < (univ.filter fun j : Fin (2 * r) => z (j, ⟨0, hw⟩) = true).card then (1 : ℝ) else 0) *
      ∏ j, ‖a (fun i => z (j, i))‖ ^ 2]
  rw [Fintype.sum_equiv (Equiv.curry (Fin (2 * r)) (Fin w) Bool) (fun z =>
    (if r < (univ.filter fun j => z (j, ⟨0, hw⟩) = true).card then (1 : ℝ) else 0) *
      ∏ j, ‖a (fun i => z (j, i))‖ ^ 2) (fun y =>
    (if r < (univ.filter fun j => y j ⟨0, hw⟩ = true).card then (1 : ℝ) else 0) *
      ∏ j, ‖a (y j)‖ ^ 2) fun z => rfl]
  refine (sum_mul_prod_fiberwise (fun z : Fin w → Bool => z ⟨0, hw⟩) (fun z => ‖a z‖ ^ 2)
    fun b => if r < (univ.filter fun j => b j = true).card then (1 : ℝ) else 0).trans ?_
  -- the outcome probabilities of one copy
  have hone : ∑ z, ‖a z‖ ^ 2 = 1 := by
    rw [← measureProb, measureProb_univ, Circuit.norm_run, one_pow]
  have htrue : ∑ z ∈ univ.filter (fun z : Fin w → Bool => z ⟨0, hw⟩ = true), ‖a z‖ ^ 2 =
      acceptProb w gs x := by
    unfold acceptProb measureProb
    congr 1
    ext z
    simp [mem_accepting hw]
  have hfalse : ∑ z ∈ univ.filter (fun z : Fin w → Bool => z ⟨0, hw⟩ = false), ‖a z‖ ^ 2 =
      1 - acceptProb w gs x := by
    rw [← hone, ← htrue, ← sum_filter_add_sum_filter_not univ (fun z : Fin w → Bool =>
      z ⟨0, hw⟩ = true)]
    simp
  rw [sum_filter]
  refine sum_congr rfl fun b _ => ?_
  rw [ite_mul, one_mul, zero_mul]
  refine if_congr Iff.rfl (prod_congr rfl fun j _ => ?_) rfl
  cases b j
  · exact hfalse
  · exact htrue

namespace Amplify

/-! ### The amplified circuit is constructed in polynomial time -/

variable {γ : Type} {enc : γ ↪ List Bool}

theorem computableInPolyTime_copyCodes {n w k : γ → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hw : ComputableInPolyTime w enc encUnary)
    (hk : ComputableInPolyTime k enc encUnary) :
    ComputableInPolyTime (fun c => copyCodes (n c) (w c) (k c)) enc (encList encGateCode) := by
  unfold copyCodes
  fun_prop

theorem computableInPolyTime_copiesCodes {w k : γ → ℕ} {gs : γ → List GateCode}
    (hw : ComputableInPolyTime w enc encUnary) (hk : ComputableInPolyTime k enc encUnary)
    (hgs : ComputableInPolyTime gs enc (encList encGateCode)) :
    ComputableInPolyTime (fun c => copiesCodes (w c) (k c) (gs c)) enc (encList encGateCode) := by
  have hshift (o : ℕ) : shift o = fun g => (g.1, g.2.1 + o, g.2.2.map (· + o)) := rfl
  simp only [copiesCodes, hshift]
  fun_prop

theorem computableInPolyTime_stage {base T b s : γ → ℕ}
    (hbase : ComputableInPolyTime base enc encUnary) (hT : ComputableInPolyTime T enc encUnary)
    (hb : ComputableInPolyTime b enc encUnary) (hs : ComputableInPolyTime s enc encUnary) :
    ComputableInPolyTime (fun c => Counter.stage (base c) (T c) (b c) (s c)) enc
      (encList encGateCode) := by
  simp only [Counter.stage, Counter.level, Counter.below]
  fun_prop

theorem computableInPolyTime_counter {w r : γ → ℕ}
    (hw : ComputableInPolyTime w enc encUnary) (hr : ComputableInPolyTime r enc encUnary) :
    ComputableInPolyTime (fun c => Counter.codes (base (w c) (r c)) (r c + 1)
      (fun s => (s + 1) * w c) (2 * r c)) enc (encList encGateCode) := by
  have hstage := computableInPolyTime_stage (enc := encPair enc encUnary)
    (base := fun p => base (w p.1) (r p.1)) (T := fun p => r p.1 + 1)
    (b := fun p => (p.2 + 1) * w p.1) (s := fun p => p.2)
    (by unfold base; fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hbase : ComputableInPolyTime (fun c => base (w c) (r c)) enc encUnary := by
    unfold base
    fun_prop
  unfold Counter.codes
  fun_prop

theorem computableInPolyTime_codes {n w r : γ → ℕ} {gs : γ → List GateCode}
    (hn : ComputableInPolyTime n enc encUnary) (hw : ComputableInPolyTime w enc encUnary)
    (hr : ComputableInPolyTime r enc encUnary)
    (hgs : ComputableInPolyTime gs enc (encList encGateCode)) :
    ComputableInPolyTime (fun c => codes (n c) (w c) (r c) (gs c)) enc (encList encGateCode) := by
  have h₁ := computableInPolyTime_copyCodes hn hw (k := fun c => 2 * r c) (by fun_prop)
  have h₂ := computableInPolyTime_copiesCodes hw (k := fun c => 2 * r c) (by fun_prop) hgs
  have h₃ := computableInPolyTime_counter hw hr
  have h₄ : ComputableInPolyTime (fun c => swapCodes (answer (w c) (r c))) enc
      (encList encGateCode) := by
    simp only [swapCodes, answer, Counter.level, base]
    fun_prop
  unfold codes
  fun_prop

end Amplify

namespace UniformCircuitFamily

open Amplify

/-- **The amplified family**: on inputs of length `n`, `2 r(n)` copies of the family's circuit run
side by side, and a reversible majority vote of their answers is measured. -/
def amplify (F : UniformCircuitFamily) (r : ℕ → ℕ)
    (hr : ComputableInPolyTime r encUnary encUnary) : UniformCircuitFamily where
  width n := Amplify.width (F.width n) (r n)
  gates n := codes n (F.width n) (r n) (F.gates n)
  computableInPolyTime_width := by
    have := F.computableInPolyTime_width
    simp only [Amplify.width, base]
    fun_prop
  computableInPolyTime_gates :=
    computableInPolyTime_codes (by fun_prop) F.computableInPolyTime_width hr
      F.computableInPolyTime_gates
  le_width n := by
    have := F.le_width n
    have : F.width n ≤ base (F.width n) (r n) := Nat.le_mul_of_pos_left _ (by omega)
    have := base_lt_width (w := F.width n) (r := r n)
    omega
  width_pos n := Nat.lt_of_le_of_lt (Nat.zero_le _) base_lt_width
  wellFormed n g hg := by
    have hw := F.width_pos n
    rcases List.mem_append.mp hg with hg | hg
    · exact (isClassical_copyCodes (F.le_width n) hw g hg).2
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨j, hj, hg⟩ := List.mem_flatMap.mp hg
      obtain ⟨g, hg', rfl⟩ := List.mem_map.mp hg
      exact (F.wellFormed n g hg').shift (block_le_width (List.mem_range.mp hj))
    · exact (isClassical_counter_swap hw g hg).2

/-- **The acceptance probability of the amplified family** is the probability that more than
`r(n)` of `2 r(n)` independent runs of the family accept, on inputs of length `n`. -/
theorem acceptProb_amplify (F : UniformCircuitFamily) {r : ℕ → ℕ}
    (hr : ComputableInPolyTime r encUnary encUnary) (x : List Bool) :
    (F.amplify r hr).acceptProb x =
      ∑ b : Fin (2 * r x.length) → Bool with r x.length < (univ.filter fun j => b j = true).card,
        ∏ j, if b j then F.acceptProb x else 1 - F.acceptProb x :=
  acceptProb_amplify_codes (F.width_pos _) (F.le_width _) (F.wellFormed _) x rfl

/-- The trials of the majority vote: success with probability `p`. -/
private theorem sum_bernoulli (p : ℝ) : ∑ c : Bool, (if c then p else 1 - p) = 1 := by
  simp

/-- **Amplifying acceptance**: a family accepting with probability at least `2 / 3` gives a family
accepting with probability at least `1 - (8 / 9) ^ r(n)`. -/
theorem one_sub_le_acceptProb_amplify (F : UniformCircuitFamily) {r : ℕ → ℕ}
    (hr : ComputableInPolyTime r encUnary encUnary) {x : List Bool}
    (hx : 2 / 3 ≤ F.acceptProb x) :
    1 - (8 / 9) ^ r x.length ≤ (F.amplify r hr).acceptProb x := by
  set p := F.acceptProb x
  set R := r x.length
  have hq : ∀ c : Bool, 0 ≤ if c then p else 1 - p := fun c => by
    have := F.acceptProb_le_one x
    cases c <;> simp <;> linarith
  have hbad := sum_prod_le_of_card_filter_le (fun c : Bool => if c then p else 1 - p) hq
    (sum_bernoulli p) {true} (by simpa using (by linarith : (2 : ℝ) ≤ 3 * p)) R
  simp only [mem_singleton] at hbad
  have htotal := (Fintype.sum_pow (fun c : Bool => if c then p else 1 - p) (2 * R)).symm
  rw [sum_bernoulli, one_pow, ← sum_filter_add_sum_filter_not univ
    (fun b : Fin (2 * R) → Bool => R < (univ.filter fun j => b j = true).card)] at htotal
  simp only [not_lt] at htotal
  rw [acceptProb_amplify]
  linarith

/-- **Amplifying rejection**: a family accepting with probability at most `1 / 3` gives a family
accepting with probability at most `(8 / 9) ^ r(n)`. -/
theorem acceptProb_amplify_le (F : UniformCircuitFamily) {r : ℕ → ℕ}
    (hr : ComputableInPolyTime r encUnary encUnary) {x : List Bool}
    (hx : F.acceptProb x ≤ 1 / 3) :
    (F.amplify r hr).acceptProb x ≤ (8 / 9) ^ r x.length := by
  set p := F.acceptProb x
  have hq : ∀ c : Bool, 0 ≤ if c then p else 1 - p := fun c => by
    have := F.acceptProb_nonneg x
    cases c <;> simp <;> linarith
  have hbad := sum_prod_le_of_card_filter_le (fun c : Bool => if c then p else 1 - p) hq
    (sum_bernoulli p) {false} (by simpa using (by linarith : (2 : ℝ) ≤ 3 * (1 - p))) (r x.length)
  simp only [mem_singleton] at hbad
  rw [acceptProb_amplify]
  refine le_trans (sum_le_sum_of_subset_of_nonneg (fun b hb => ?_)
    fun b _ _ => prod_nonneg fun j _ => hq _) hbad
  rw [mem_filter] at hb ⊢
  refine ⟨mem_univ _, ?_⟩
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * r x.length))))
    (fun j => b j = true)
  have e : (univ.filter fun j => ¬b j = true) = univ.filter fun j => b j = false := by
    ext j
    simp
  rw [e, card_univ, Fintype.card_fin] at this
  omega

end UniformCircuitFamily

end Cslib.Quantum

namespace Cslib.Complexity

open Quantum Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- `(8 / 9) ^ (6 m) ≤ 2 ^ (-m)`, since `2 * 8 ^ 6 < 9 ^ 6`. -/
private theorem eight_ninths_pow_le (m : ℕ) : ((8 : ℝ) / 9) ^ (6 * m) ≤ ((2 : ℝ) ^ m)⁻¹ := by
  rw [pow_mul, ← inv_pow]
  exact pow_le_pow_left₀ (by positivity) (by norm_num) m

/-- **Error reduction for `BQP`**: a problem is in `BQP` exactly when, for every polynomial `q`,
some polynomial-time uniform family accepts the encodings of members with probability at least
`1 - 2^{-q(n)}` and those of other instances with probability at most `2^{-q(n)}`, where `n` is the
length of the encoding. -/
theorem mem_BQP_iff_forall_errorExponent {A : Set α} :
    A ∈ BQP enc ↔ ∀ q : Polynomial ℕ, ∃ F : UniformCircuitFamily, ∀ a,
      (a ∈ A → 1 - ((2 : ℝ) ^ q.eval (enc a).length)⁻¹ ≤ F.acceptProb (enc a)) ∧
      (a ∉ A → F.acceptProb (enc a) ≤ ((2 : ℝ) ^ q.eval (enc a).length)⁻¹) := by
  constructor
  · rintro ⟨F, hF⟩ q
    have hr : ComputableInPolyTime (fun n => 6 * q.eval n) encUnary encUnary := by fun_prop
    refine ⟨F.amplify _ hr, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
    · exact le_trans (by linarith [eight_ninths_pow_le (q.eval (enc a).length)])
        (F.one_sub_le_acceptProb_amplify hr ((hF a).1 ha))
    · exact (F.acceptProb_amplify_le hr ((hF a).2 ha)).trans (eight_ninths_pow_le _)
  · intro h
    obtain ⟨F, hF⟩ := h (Polynomial.C 2)
    refine ⟨F, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
    · have := (hF a).1 ha
      simp only [Polynomial.eval_C] at this
      norm_num at this ⊢
      linarith
    · have := (hF a).2 ha
      simp only [Polynomial.eval_C] at this
      norm_num at this ⊢
      linarith

end Cslib.Complexity
