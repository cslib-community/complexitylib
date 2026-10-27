/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.FullArithmetic
public import Complexity.Foundations.LinearAlgebra.KernelVector
import Complexity.Tactic.Synthesis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Circuits for kernel vectors

The elimination procedure `Cslib.LinearAlgebra.kernelVec`, which returns a nonzero vector in the
kernel of a matrix whenever there is one, is a fixed arithmetic computation with tests for zero.
Over the full binary basis of a field, where every operation on at most two field elements is one
gate, it costs `O((r + 1) * n ^ 2)` gates for a matrix with `r` rows and `n` columns: the indicator
of the first nonzero entry of a vector of length `n` costs `2 * n + 1` gates
(`Cslib.Circuits.Synthesis.full_firstFlags`), one elimination step at most `8 * (n + 1) ^ 2`
(`Cslib.Circuits.Synthesis.full_kernelStep`) and the whole procedure at most
`kernelVecCost r n = 8 * (r + 1) * (n + 1) ^ 2` (`Cslib.Circuits.Synthesis.full_kernelVec`).
The entries of the matrix may be arbitrary available functions of the circuit's inputs.

## Main definitions

* `Cslib.Circuits.kernelVecCost`: the gate budget of the elimination procedure.

## Main results

* `Cslib.Circuits.Synthesis.full_firstFlags`: the first nonzero entry.
* `Cslib.Circuits.Synthesis.full_nonzero`: the indicator of a nonzero vector.
* `Cslib.Circuits.Synthesis.full_kernelStep`: one elimination step.
* `Cslib.Circuits.Synthesis.full_kernelVec`: a kernel vector.

## References

* [P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity Theory*]
  [BurgisserClausenShokrollahi1997]
* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
-/

@[expose] public section

namespace Cslib.Circuits

/-- The gate budget of the elimination procedure for `r` rows and `n` columns over the full binary
basis. -/
def kernelVecCost (r n : ℕ) : ℕ := 8 * (r + 1) * (n + 1) ^ 2

namespace Synthesis

open Finset Cslib.LinearAlgebra

variable {F : Type*} [Field F] [DecidableEq F] {N n r : ℕ} {s : Set ((Fin N → F) → F)}

/-- One if the first `i` entries of `b` are zero, and zero otherwise. -/
private def prefixZero (b : Fin n → F) (i : ℕ) : F :=
  if ∀ i' : Fin n, (i' : ℕ) < i → b i' = 0 then 1 else 0

private theorem prefixZero_succ (b : Fin n → F) {i : ℕ} (h : i < n) :
    prefixZero b (i + 1) = if b ⟨i, h⟩ = 0 then prefixZero b i else 0 := by
  unfold prefixZero
  by_cases hb : b ⟨i, h⟩ = 0
  · rw [ite_eq_left hb]
    congr 1
    refine propext ⟨fun h' i' hi' => h' i' (Nat.lt_succ_of_lt hi'), fun h' i' hi' => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | hi'
    · exact h' i' hi'
    · rw [show i' = ⟨i, h⟩ from Fin.ext hi']
      exact hb
  · rw [ite_eq_right hb, ite_eq_right]
    exact fun h' => hb (h' ⟨i, h⟩ (Nat.lt_succ_self i))

private theorem firstFlags_eq_prefixZero (b : Fin n → F) (i : Fin n) :
    firstFlags b i = if b i = 0 then 0 else prefixZero b i := by
  unfold firstFlags prefixZero
  by_cases hb : b i = 0
  · simp [hb]
  · simp only [ne_eq, hb, not_false_eq_true, true_and, ite_false]
    rfl

/-- **The first nonzero entry.** The indicators `firstFlags b i` of the first nonzero entry of a
vector of `n` available functions cost `2 * n + 1` gates of the full binary basis. -/
theorem full_firstFlags (b : Fin n → (Fin N → F) → F) (hb : ∀ i, b i ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s
      (Set.range fun i x => firstFlags (fun j => b j x) i) (2 * n + 1) := by
  let g : ℕ → (Fin N → F) → F := fun i => if h : i < n then b ⟨i, h⟩ else fun _ => 0
  let op : ℕ → F → F → F := fun _ z bi => if bi = 0 then z else 0
  have hchain := full_chain (s := s) (1 : F) op g n fun i hi => by
    simp only [g, dite_eq_left hi]
    exact hb _
  have hval (i : ℕ) (hi : i ≤ n) (x : Fin N → F) :
      chainValue 1 op g i x = prefixZero (fun j => b j x) i := by
    induction i with
    | zero => simp [chainValue, prefixZero]
    | succ i ih =>
      have hi' : i < n := hi
      change op i (chainValue 1 op g i x) (g i x) = _
      rw [ih (Nat.le_of_succ_le hi), prefixZero_succ _ hi]
      simp only [op, g, dite_eq_left hi']
  have hsel := family (I := fullInterpretation (k := 2))
    (s := s ∪ Set.range fun i : Fin (n + 1) => chainValue 1 op g i)
    (fun i : Fin n => fun x => (fun z bi => if bi = 0 then 0 else z) (chainValue 1 op g i x)
      (b i x)) (fun _ => 1)
    (fun i => full_binary_mem (f := fun x => chainValue 1 op g i x) (g := b i)
      (fun z bi => if bi = 0 then 0 else z) (Set.mem_union_right s
      (⟨i.castSucc, rfl⟩ : _ ∈ Set.range fun i : Fin (n + 1) => chainValue 1 op g i))
      (Set.mem_union_left _ (hb i)))
  refine (hchain.trans hsel).mono Set.Subset.rfl ?_
    (by simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]; omega)
  rintro _ ⟨i, rfl⟩
  refine ⟨i, funext fun x => ?_⟩
  simp only [firstFlags_eq_prefixZero, hval i i.2.le]

/-- The indicator that a vector of `n` available functions is nonzero costs `n + 1` gates of the
full binary basis. -/
theorem full_nonzero (v : Fin n → (Fin N → F) → F) (hv : ∀ l, v l ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s
      {fun x => if (fun l => v l x) = 0 then 0 else 1} (n + 1) := by
  let g : ℕ → (Fin N → F) → F := fun i => if h : i < n then v ⟨i, h⟩ else fun _ => 0
  let op : ℕ → F → F → F := fun _ acc vi => if vi = 0 then acc else 1
  have hchain := full_chain (s := s) (0 : F) op g n fun i hi => by
    simp only [g, dite_eq_left hi]
    exact hv _
  have hval (i : ℕ) (hi : i ≤ n) (x : Fin N → F) :
      chainValue 0 op g i x =
        if ∀ l : Fin n, (l : ℕ) < i → v l x = 0 then 0 else 1 := by
    induction i with
    | zero => simp [chainValue]
    | succ i ih =>
      have hi' : i < n := hi
      change op i (chainValue 0 op g i x) (g i x) = _
      rw [ih (Nat.le_of_succ_le hi)]
      simp only [op, g, dite_eq_left hi']
      by_cases hvi : v ⟨i, hi⟩ x = 0
      · rw [ite_eq_left hvi]
        congr 1
        refine propext ⟨fun h' l hl => ?_, fun h' l hl => h' l (Nat.lt_succ_of_lt hl)⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | hl
        · exact h' l hl
        · rw [show l = ⟨i, hi⟩ from Fin.ext hl]
          exact hvi
      · rw [ite_eq_right hvi, ite_eq_right]
        exact fun h' => hvi (h' ⟨i, hi⟩ (Nat.lt_succ_self i))
  refine hchain.mono Set.Subset.rfl (Set.singleton_subset_iff.2 ⟨Fin.last n, ?_⟩) le_rfl
  funext x
  change chainValue 0 op g (Fin.last n : ℕ) x = _
  rw [Fin.val_last, hval n le_rfl x]
  congr 1
  exact propext ⟨fun h => funext fun l => h l l.2, fun h l _ => congrFun h l⟩

omit [DecidableEq F] in
/-- A dot product of two vectors of `n` available functions costs `2 * n + 1` gates. -/
private theorem full_dot_univ (u v : Fin n → (Fin N → F) → F)
    (hu : ∀ l, u l ∈ s) (hv : ∀ l, v l ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s {fun x => ∑ l, u l x * v l x} (2 * n + 1) := by
  simpa only [card_univ, Fintype.card_fin] using
    full_dot (s := s) univ u v (fun l _ => hu l) (fun l _ => hv l)

/-- The budget of one elimination step. -/
private theorem kernelStep_budget (n : ℕ) :
    n * (2 * n + 1) + (2 * n + 1) + n * (2 * n + 1) + (2 * n + 1) + n + n * n + n * n ≤
      8 * (n + 1) ^ 2 := by
  nlinarith

/-- **One elimination step.** If the entries of the row `a` and of the family `Nv` are available,
the entries of `kernelStep a Nv` cost at most `8 * (n + 1) ^ 2` gates of the full binary basis. -/
theorem full_kernelStep (a : Fin n → (Fin N → F) → F) (Nv : Fin n → Fin n → (Fin N → F) → F)
    (ha : ∀ l, a l ∈ s) (hN : ∀ i l, Nv i l ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s
      (Set.range fun il : Fin n × Fin n =>
        fun x => kernelStep (fun l => a l x) (fun i l => Nv i l x) il.1 il.2)
      (8 * (n + 1) ^ 2) := by
  let build := Builder.start (fullInterpretation (k := 2)) s
  -- the row values
  let b : Fin n → (Fin N → F) → F := fun i x => ∑ l, a l x * Nv i l x
  let build := build.add (family (I := fullInterpretation (k := 2)) (s := build.wires)
    b (fun _ => 2 * n + 1) fun i =>
      full_dot_univ a (Nv i) (by synthesis_available) (by synthesis_available))
  -- the pivot flags
  let sel : Fin n → (Fin N → F) → F := fun i x => firstFlags (fun j => b j x) i
  synthesis_step build using full_firstFlags b
  -- the pivot vector
  let P : Fin n → (Fin N → F) → F := fun l x => ∑ j, sel j x * Nv j l x
  let build := build.add (family (I := fullInterpretation (k := 2)) (s := build.wires)
    P (fun _ => 2 * n + 1) fun l =>
      full_dot_univ sel (fun j => Nv j l) (by synthesis_available) (by synthesis_available))
  -- the pivot value
  let β : (Fin N → F) → F := fun x => ∑ l, a l x * P l x
  let build := build.add (full_dot_univ a P (by synthesis_available) (by synthesis_available))
  -- the ratios
  let ρ : Fin n → (Fin N → F) → F := fun i x => b i x / β x
  let build := build.add (family (I := fullInterpretation (k := 2)) (s := build.wires)
    ρ (fun _ => 1) fun i =>
      full_binary_mem (· / ·) (by synthesis_available) (by synthesis_available))
  -- the corrections
  let t : Fin n × Fin n → (Fin N → F) → F := fun il x => ρ il.1 x * P il.2 x
  let build := build.add (family (I := fullInterpretation (k := 2)) (s := build.wires)
    t (fun _ => 1) fun il =>
      full_binary_mem (· * ·) (by synthesis_available) (by synthesis_available))
  -- the new family
  let N' : Fin n × Fin n → (Fin N → F) → F := fun il x => Nv il.1 il.2 x - t il x
  let build := build.add (family (I := fullInterpretation (k := 2)) (s := build.wires)
    N' (fun _ => 1) fun il =>
      full_binary_mem (· - ·) (by synthesis_available) (by synthesis_available))
  refine build.finish ?_ ?_
  · rintro _ ⟨⟨i, l⟩, rfl⟩
    have hmem : N' (i, l) ∈ build.wires := by synthesis_available
    convert hmem using 1
    funext x
    simp only [N', t, ρ, β, P, sel, b, kernelStep, rowValues, pivotVec, dotProduct,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rfl
  · dsimp +zetaDelta [Builder.add, Builder.start]
    simp only [sum_const, card_univ, Fintype.card_fin, Fintype.card_prod, smul_eq_mul, mul_one]
    linarith [kernelStep_budget n]

/-- The entries of the family after processing the first `k` rows cost at most
`(n + 1) ^ 2 + k * 8 * (n + 1) ^ 2` gates of the full binary basis. -/
private theorem full_kernelBasisUpTo (A : Fin r → Fin n → (Fin N → F) → F)
    (hA : ∀ k l, A k l ∈ s) (k : ℕ) :
    Synthesis (fullInterpretation (k := 2)) s
      (Set.range fun il : Fin n × Fin n =>
        fun x => kernelBasisUpTo (fun k l => A k l x) k il.1 il.2)
      ((n + 1) ^ 2 + k * (8 * (n + 1) ^ 2)) := by
  induction k with
  | zero =>
    have h := family (I := fullInterpretation (k := 2)) (s := s)
      (fun il : Fin n × Fin n => fun _ : Fin N → F => (Pi.single il.1 1 : Fin n → F) il.2)
      (fun _ => 1) (fun il => full_const _)
    refine h.mono Set.Subset.rfl ?_ ?_
    · rintro _ ⟨il, rfl⟩
      exact ⟨il, rfl⟩
    · simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul,
        mul_one, zero_mul, add_zero]
      nlinarith
  | succ k ih =>
    by_cases hk : k < r
    · have hstep := full_kernelStep
        (s := s ∪ Set.range fun il : Fin n × Fin n =>
          fun x => kernelBasisUpTo (fun k l => A k l x) k il.1 il.2)
        (A ⟨k, hk⟩) (fun i l x => kernelBasisUpTo (fun k l => A k l x) k i l)
        (fun l => Set.mem_union_left _ (hA _ l))
        (fun i l => Set.mem_union_right _ ⟨(i, l), rfl⟩)
      refine (ih.trans hstep).mono Set.Subset.rfl ?_ (le_of_eq (by ring))
      rintro _ ⟨il, rfl⟩
      refine ⟨il, funext fun x => ?_⟩
      simp only [kernelBasisUpTo, dite_eq_left hk]
    · refine ih.mono Set.Subset.rfl ?_ (by nlinarith)
      rintro _ ⟨il, rfl⟩
      refine ⟨il, funext fun x => ?_⟩
      simp only [kernelBasisUpTo, dite_eq_right hk]

/-- **A kernel vector by a circuit.** If the entries of a matrix with `r` rows and `n` columns are
available, the entries of `kernelVec A` cost at most `kernelVecCost r n = 8 * (r + 1) * (n + 1) ^ 2`
gates of the full binary basis. -/
theorem full_kernelVec (A : Fin r → Fin n → (Fin N → F) → F) (hA : ∀ k l, A k l ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s
      (Set.range fun l x => kernelVec (fun k l => A k l x) l) (kernelVecCost r n) := by
  let K : Fin n → Fin n → (Fin N → F) → F := fun i l x => kernelBasis (fun k l => A k l x) i l
  have h₁ := full_kernelBasisUpTo A hA r
  set s₁ := s ∪ Set.range fun il : Fin n × Fin n =>
    fun x => kernelBasisUpTo (fun k l => A k l x) r il.1 il.2
  have hK : ∀ i l, K i l ∈ s₁ := fun i l => Set.mem_union_right _ ⟨(i, l), rfl⟩
  -- the nonzero indicators of the members
  let c : Fin n → (Fin N → F) → F := fun i x => if (fun l => K i l x) = 0 then 0 else 1
  have h₂ := family (I := fullInterpretation (k := 2)) (s := s₁) c (fun _ => n + 1)
    (fun i => full_nonzero (K i) (hK i))
  set s₂ := s₁ ∪ Set.range c
  -- their first nonzero entry
  let sel : Fin n → (Fin N → F) → F := fun i x => firstFlags (fun j => c j x) i
  have h₃ := full_firstFlags (s := s₂) c fun i => Set.mem_union_right _ ⟨i, rfl⟩
  set s₃ := s₂ ∪ Set.range sel
  -- the selected member
  have h₄ := family (I := fullInterpretation (k := 2)) (s := s₃)
    (fun l x => ∑ i, sel i x * K i l x) (fun _ => 2 * n + 1)
    (fun l => by
      simpa [card_univ] using full_dot (s := s₃) univ sel (fun i => K i l)
        (fun i _ => Set.mem_union_right _ ⟨i, rfl⟩)
        (fun i _ => Set.mem_union_left _ (Set.mem_union_left _ (hK i l))))
  have htotal := h₁.trans (h₂.trans (h₃.trans h₄))
  refine htotal.mono Set.Subset.rfl ?_ ?_
  · rintro _ ⟨l, rfl⟩
    refine ⟨l, funext fun x => ?_⟩
    have hc : (fun j => c j x) = fun i => if kernelBasis (fun k l => A k l x) i = 0 then 0 else 1 :=
      rfl
    simp only [sel, K, kernelVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc]
  · simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, kernelVecCost]
    nlinarith

end Synthesis

end Cslib.Circuits
