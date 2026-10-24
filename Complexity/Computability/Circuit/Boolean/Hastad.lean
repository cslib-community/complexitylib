/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Unbounded
public import Complexity.Computability.Circuit.Formula
public import Complexity.Computability.DecisionTree.Parity
public import Complexity.Computability.DecisionTree.Restrict
public import Complexity.Computability.DecisionTree.Switching
import Complexity.Computability.Circuit.Depth
import Complexity.Foundations.Data.Nat.Choose
import Complexity.Foundations.Data.Nat.Div
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Håstad's theorem: parity needs large circuits of constant depth

**Håstad's theorem** for circuits with unbounded fan-in: a circuit of depth `d` with fewer than
`2 ^ s` gates that computes the parity of `n` bits has `n < s (16 s + 1) ^ d`, for every `s ≥ 2`.
So such circuits, and formulas (`Formula.toCircuit`), have size `2 ^ Ω(n ^ (1 / (d + 1)))`
[FurstSaxeSipser1984], [Ajtai1983], [Hastad1986], [Jukna, Chapter 12][Jukna2012]. The exponent
`1 / (d + 1)` is weaker than Håstad's `1 / (d - 1)`: each stage below leaves a `1 / (16 s + 1)`
fraction of the free bits rather than `1 / (10 s)` with a final DNF stage. Depth counts every gate
on a path, negations included, and size counts every gate.

The proof restricts the circuit `d` times by random restrictions (partial assignments,
`BitString.PartialAssignment`). After stage `j`, every gate of depth at most `j`
computes, under the restriction so far, a function of decision tree complexity below `s`
(`Shallow`). A gate of depth `j + 1` then computes, up to negation, a formula in disjunctive normal
form whose terms have fewer than `s` literals (`exists_dnf_of_shallow`), and the switching lemma
shows that at most a `2 ^ (-s)` fraction of the extensions of the restriction fail to make it
shallow (`two_pow_mul_card_filter_not_shallow_le`). Drawing a restriction with fewer free bits by
first drawing one with more free bits and then an extension of it
(`PartialAssignment.mul_card_filter_withFree_le`), at most a `G / 2 ^ s` fraction of the
restrictions leaving `n / (16 s + 1) ^ j` bits free make some gate of depth at most `j` deep, where
`G` is the number of those gates (`two_pow_mul_card_filter_exists_not_shallow_le`). With fewer than
`2 ^ s` gates, some restriction makes the output shallow, while the restricted parity needs to query
every free bit. The counted form also bounds the Fourier tails of small circuits of constant depth
[Linial, Mansour and Nisan][LinialMansourNisan1993].

## Main definitions

* `Cslib.Circuits.Boolean.Shallow`: a function has, under a restriction, small decision tree
  complexity.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.exists_dnf_of_shallow`: an operation applied to shallow
  functions computes a narrow formula in disjunctive normal form, up to negation.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_mul_card_filter_not_shallow_le`: the switching lemma
  for one operation applied to shallow functions.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_mul_card_filter_not_shallow_le_of_ne_not`: the
  switching lemma for a conjunction or disjunction of functions of decision tree depth at most
  `k`, leaving a `1 / (16 k + 1)` fraction of the free bits.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_mul_card_filter_exists_not_shallow_le`: random
  restrictions make small circuits of constant depth shallow.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity`: Håstad's theorem for
  circuits.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_formula_computes_parity`: Håstad's theorem
  for formulas.

## References

* [M. Furst, J. B. Saxe, M. Sipser, *Parity, circuits, and the polynomial-time
  hierarchy*][FurstSaxeSipser1984]
* [M. Ajtai, *Σ¹₁-formulae on finite structures*][Ajtai1983]
* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Cslib.BitString Cslib.DecisionTree Cslib.Logic.PL Finset

variable {n s : ℕ} {ρ ρ' : PartialAssignment (Fin n)}

/-! ### Shallow functions -/

/-- `f` is `s`-shallow under `ρ`: the function it computes under `ρ` has decision tree complexity
below `s`. -/
def Shallow (s : ℕ) (ρ : PartialAssignment (Fin n)) (f : BitString n → Bool) : Prop :=
  DecisionTree.complexity (fun x => f (ρ.fill x)) < s

/-- Classical decidability of `Shallow s ρ f`. -/
noncomputable instance (s : ℕ) (ρ : PartialAssignment (Fin n)) (f : BitString n → Bool) :
    Decidable (Shallow s ρ f) :=
  inferInstanceAs (Decidable (_ < s))

/-- Restricting further keeps a function shallow. -/
theorem Shallow.mono {f : BitString n → Bool} (hf : Shallow s ρ f) (h : ρ'.Extends ρ) :
    Shallow s ρ' f := by
  refine lt_of_le_of_lt ?_ hf
  have : DecisionTree.complexity (fun x => f (ρ.fill (ρ'.fill x))) ≤
      DecisionTree.complexity fun y => f (ρ.fill y) :=
    complexity_comp_fill_le ρ' fun y => f (ρ.fill y)
  simpa only [PartialAssignment.fill_fill_of_extends h] using this

/-- A function shallow for one bound is shallow for every larger bound. -/
theorem Shallow.of_le {f : BitString n → Bool} {s' : ℕ} (h : Shallow s ρ f) (hs : s ≤ s') :
    Shallow s' ρ f :=
  lt_of_lt_of_le h hs

/-- The input bits are shallow. -/
theorem shallow_proj (hs : 2 ≤ s) (ρ : PartialAssignment (Fin n)) (i : Fin n) :
    Shallow s ρ fun x => x i := by
  have h₁ : DecisionTree.complexity (fun x : BitString n => x i) ≤ 1 :=
    DecisionTree.complexity_le_iff.2 ⟨DecisionTree.node i (.leaf false) (.leaf true),
      fun x => by cases h : x i <;> simp [h], by simp⟩
  exact lt_of_le_of_lt ((complexity_comp_fill_le ρ fun x : BitString n => x i).trans h₁)
    (by omega)

/-- The negation of a shallow function is shallow. -/
theorem Shallow.not {f : BitString n → Bool} (h : Shallow s ρ f) : Shallow s ρ fun x => !f x :=
  (complexity_not fun x => f (ρ.fill x)).trans_lt h

/-- Shallow functions have decision trees of depth below `s`. -/
theorem Shallow.exists_tree {f : BitString n → Bool} (h : Shallow s ρ f) :
    ∃ t : DecisionTree (Fin n) Bool, (∀ y, t.eval y = f (ρ.fill y)) ∧ t.depth < s := by
  obtain ⟨t, ht, hd⟩ := DecisionTree.complexity_le_iff.1
    (le_refl (DecisionTree.complexity fun x => f (ρ.fill x)))
  exact ⟨t, ht, hd.trans_lt h⟩

/-- Restricted parity is not shallow when at least `s` bits are free. -/
theorem not_shallow_parity (h : s ≤ #ρ.free) : ¬ Shallow s ρ (parity n) :=
  fun hshallow => absurd ((card_free_le_complexity_parity_fill ρ).trans_lt hshallow) (by omega)

namespace Unbounded

/-! ### One stage of restrictions -/

/-- The disjunction of the paths of decision trees of depth below `s` to leaves other than `c`. -/
private theorem exists_dnf_of_trees {m : ℕ} (c : Bool) (t : Fin m → DecisionTree (Fin n) Bool)
    (hd : ∀ j, (t j).depth < s) :
    ∃ D : DNF (Fin n), (∀ u ∈ D, u.length < s ∧ (u.map Prod.fst).Nodup) ∧
      ∀ y, DNF.eval y D = decide (∃ j, ((t j).eval y != c) = true) := by
  refine ⟨(List.ofFn fun j => ((t j).map (· != c)).toDNF).flatten, fun u hu => ?_, fun y => ?_⟩
  · obtain ⟨_, hl, hu⟩ := List.mem_flatten.1 hu
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl
    exact ⟨(length_le_depth_of_mem_toDNF hu).trans_lt (by rw [depth_map]; exact hd j),
      nodup_of_mem_toDNF hu⟩
  · rw [Bool.eq_iff_iff, DNF.eval_eq_true_iff, decide_eq_true_iff]
    simp only [List.mem_flatten, List.mem_ofFn]
    constructor
    · rintro ⟨u, ⟨_, ⟨j, rfl⟩, hu⟩, hux⟩
      refine ⟨j, ?_⟩
      rw [← eval_map (· != c), ← eval_toDNF, DNF.eval_eq_true_iff]
      exact ⟨u, hu, hux⟩
    · rintro ⟨j, hj⟩
      rw [← eval_map (· != c), ← eval_toDNF, DNF.eval_eq_true_iff] at hj
      obtain ⟨u, hu, hux⟩ := hj
      exact ⟨u, ⟨_, ⟨j, rfl⟩, hu⟩, hux⟩

/-- **Operations applied to shallow functions are narrow formulas in disjunctive normal form**, up
to negation: a disjunction is the disjunction of the paths to `true` of decision trees for its
arguments, and the negation of a conjunction is the disjunction of their paths to `false`. -/
theorem exists_dnf_of_shallow {op : Op} (hop : op ≠ .not) {args : Fin op.arity → BitString n → Bool}
    (h : ∀ j, Shallow s ρ (args j)) :
    ∃ (D : DNF (Fin n)) (b : Bool), (∀ t ∈ D, t.length < s ∧ (t.map Prod.fst).Nodup) ∧
      ∀ y, DNF.eval y D = (interpretation op (fun j => args j (ρ.fill y)) != b) := by
  choose t ht hd using fun j => (h j).exists_tree
  cases op with
  | not => exact absurd rfl hop
  | and m =>
    obtain ⟨D, hD, heval⟩ := exists_dnf_of_trees true t hd
    refine ⟨D, true, hD, fun y => ?_⟩
    rw [heval, Bool.eq_iff_iff]
    simp [ht]
  | or m =>
    obtain ⟨D, hD, heval⟩ := exists_dnf_of_trees false t hd
    exact ⟨D, false, hD, fun y => by simp [heval, ht]⟩

/-- **The switching step for a conjunction or disjunction.** If the arguments of a conjunction or
disjunction have decision tree depth at most `k` under `ρ`, at most `#E(ℓ - s) (4k)^s` of the
extensions of `ρ` with `ℓ` free bits leave it `s`-deep, where `E(m)` are the extensions of `ρ` with
`m` free bits. -/
private theorem card_filter_not_shallow_le_of_ne_not {op : Op} (hop : op ≠ .not) {k : ℕ}
    {args : Fin op.arity → BitString n → Bool} (h : ∀ j, Shallow (k + 1) ρ (args j)) (ℓ s : ℕ) :
    #{ρ' ∈ ρ.extensions ℓ | ¬ Shallow s ρ' fun x => interpretation op fun j => args j x} ≤
      #(ρ.extensions (ℓ - s)) * (4 * k) ^ s := by
  obtain ⟨D, b, hD, heval⟩ := exists_dnf_of_shallow hop h
  refine (card_le_card fun ρ' hρ' => ?_).trans (DNF.card_switching_le
    (fun t ht => Nat.lt_succ_iff.1 (hD t ht).1) (fun t ht => (hD t ht).2) ρ ℓ s)
  obtain ⟨hρ', hdeep⟩ := mem_filter.1 hρ'
  refine mem_filter.2 ⟨hρ', ?_⟩
  have hext := (PartialAssignment.mem_extensions.1 hρ').1
  have : (fun x => DNF.eval (ρ'.fill x) D) =
      (· != b) ∘ fun x => interpretation op (fun j => args j (ρ.fill (ρ'.fill x))) := by
    funext x
    rw [heval, Function.comp_apply]
  rw [this, complexity_comp_of_injective (by cases b <;> decide)]
  simpa only [PartialAssignment.fill_fill_of_extends hext] using not_lt.1 hdeep

/-- **The switching step for one operation.** If the arguments of an operation are shallow under
`ρ`, few extensions of `ρ` leave it deep. -/
private theorem card_filter_not_shallow_le {op : Op} {args : Fin op.arity → BitString n → Bool}
    (h : ∀ j, Shallow s ρ (args j)) (ℓ : ℕ) :
    #{ρ' ∈ ρ.extensions ℓ | ¬ Shallow s ρ' fun x => interpretation op fun j => args j x} ≤
      #(ρ.extensions (ℓ - s)) * (4 * s) ^ s := by
  by_cases hop : op = .not
  · subst hop
    have hG : Shallow s ρ fun x => interpretation .not fun j => args j x := (h 0).not
    rw [filter_false_of_mem fun ρ' hρ' => not_not.2 (hG.mono
      (PartialAssignment.mem_extensions.1 hρ').1)]
    simp
  exact card_filter_not_shallow_le_of_ne_not hop (fun j => (h j).of_le s.le_succ) ℓ s

/-- At most `#E(ℓ - s) (4k)^s` extensions of `ρ` are at most a `2 ^ (-s)` fraction of those with
`ℓ` free bits, when `s ≤ ℓ` and `ℓ` is at most a `1 / (16 k + 1)` fraction of the free bits of
`ρ`. -/
private theorem two_pow_mul_le_card_extensions {X k ℓ : ℕ}
    (hX : X ≤ #(ρ.extensions (ℓ - s)) * (4 * k) ^ s) (hsℓ : s ≤ ℓ)
    (hℓ : (16 * k + 1) * ℓ ≤ #ρ.free) : 2 ^ s * X ≤ #(ρ.extensions ℓ) := by
  refine (Nat.mul_le_mul_left _ hX).trans ?_
  rw [PartialAssignment.card_extensions, PartialAssignment.card_extensions]
  set m := #ρ.free
  have hℓm : ℓ ≤ m := le_trans (Nat.le_mul_of_pos_left ℓ (by omega)) hℓ
  have h2 : 2 ^ (m - (ℓ - s)) = 2 ^ (m - ℓ) * 2 ^ s := by
    rw [← pow_add]
    congr 1
    omega
  calc 2 ^ s * (m.choose (ℓ - s) * 2 ^ (m - (ℓ - s)) * (4 * k) ^ s)
      = (16 * k) ^ s * m.choose (ℓ - s) * 2 ^ (m - ℓ) := by
        rw [h2, show (16 * k) ^ s = 2 ^ s * 2 ^ s * (4 * k) ^ s by
          rw [← mul_pow, ← mul_pow]; ring_nf]
        ring
    _ ≤ m.choose ℓ * 2 ^ (m - ℓ) :=
        Nat.mul_le_mul_right _ (Nat.pow_mul_choose_sub_le_choose_of_mul_le hsℓ hℓ)

/-- **The switching fraction for a conjunction or disjunction**: if its arguments have decision
tree depth at most `k` under `ρ`, at most a `2 ^ (-s)` fraction of the extensions of `ρ` with `ℓ`
free bits leave it `s`-deep, when `s ≤ ℓ` and `ℓ` is at most a `1 / (16 k + 1)` fraction of the
free bits of `ρ`. For arguments that are literals, `k = 1` and the fraction is `1 / 17`. -/
theorem two_pow_mul_card_filter_not_shallow_le_of_ne_not {op : Op} (hop : op ≠ .not) {k : ℕ}
    {args : Fin op.arity → BitString n → Bool} (h : ∀ j, Shallow (k + 1) ρ (args j)) {ℓ : ℕ}
    (hsℓ : s ≤ ℓ) (hℓ : (16 * k + 1) * ℓ ≤ #ρ.free) :
    2 ^ s * #{ρ' ∈ ρ.extensions ℓ | ¬ Shallow s ρ' fun x => interpretation op fun j => args j x} ≤
      #(ρ.extensions ℓ) :=
  two_pow_mul_le_card_extensions (card_filter_not_shallow_le_of_ne_not hop h ℓ s) hsℓ hℓ

/-- **The switching fraction for one operation**: if the arguments of an operation are shallow
under `ρ`, at most a `2 ^ (-s)` fraction of the extensions of `ρ` with `ℓ` free bits leave it
deep, when `s ≤ ℓ` and `ℓ` is at most a `1 / (16 s + 1)` fraction of the free bits of `ρ`. -/
theorem two_pow_mul_card_filter_not_shallow_le {op : Op} {args : Fin op.arity → BitString n → Bool}
    (h : ∀ j, Shallow s ρ (args j)) {ℓ : ℕ} (hsℓ : s ≤ ℓ) (hℓ : (16 * s + 1) * ℓ ≤ #ρ.free) :
    2 ^ s * #{ρ' ∈ ρ.extensions ℓ | ¬ Shallow s ρ' fun x => interpretation op fun j => args j x} ≤
      #(ρ.extensions ℓ) :=
  two_pow_mul_le_card_extensions (card_filter_not_shallow_le h ℓ) hsℓ hℓ

/-! ### Programs -/

variable {g : ℕ}

/-- If every gate of depth at most `j` is shallow under `ρ`, so is every argument of a gate of
depth at most `j + 1`. -/
private theorem shallow_trace_wires {p : Program signature n g} (hs : 2 ≤ s) {j : ℕ}
    (hρ : ∀ k, p.depths k ≤ j → Shallow s ρ fun x => p.eval interpretation x k) {k : Fin g}
    (hk : p.depths k ≤ j + 1) (a : Fin (p.lines k).op.arity) :
    Shallow s ρ fun x => p.trace interpretation x ((p.lines k).wires a) := by
  have hlt := p.wireDepths_lines_lt k a
  cases hw : (p.lines k).wires a with
  | input i => exact shallow_proj hs ρ i
  | gate k' =>
    rw [hw, Program.wireDepths_gateWire] at hlt
    exact hρ k' (by omega)

/-- **One stage, counted**: if every gate of depth at most `j` is shallow under `ρ`, at most an
`H / 2 ^ s` fraction of the extensions of `ρ` with `ℓ'` free bits make some gate of depth at most
`j + 1` deep, where `H` is the number of gates of depth `j + 1`. -/
private theorem two_pow_mul_card_filter_extensions_le {p : Program signature n g} (hs : 2 ≤ s)
    {j ℓ' : ℕ} (hsℓ' : s ≤ ℓ') (hℓ : (16 * s + 1) * ℓ' ≤ #ρ.free)
    (hgood : ∀ k, p.depths k ≤ j → Shallow s ρ fun x => p.eval interpretation x k) :
    2 ^ s * #{ρ' ∈ ρ.extensions ℓ' |
        ∃ k, p.depths k ≤ j + 1 ∧ ¬ Shallow s ρ' fun x => p.eval interpretation x k} ≤
      #{k | p.depths k = j + 1} * #(ρ.extensions ℓ') := by
  set T : Finset (Fin g) := {k | p.depths k = j + 1}
  -- a bad extension makes a gate of depth exactly `j + 1` deep
  have hsub : {ρ' ∈ ρ.extensions ℓ' |
      ∃ k, p.depths k ≤ j + 1 ∧ ¬ Shallow s ρ' fun x => p.eval interpretation x k} ⊆
      T.biUnion fun k => {ρ' ∈ ρ.extensions ℓ' |
        ¬ Shallow s ρ' fun x => p.eval interpretation x k} := by
    intro ρ' hρ'
    obtain ⟨hext, k, hk, hdeep⟩ := mem_filter.1 hρ'
    refine mem_biUnion.2 ⟨k, mem_filter.2 ⟨mem_univ k, ?_⟩, mem_filter.2 ⟨hext, hdeep⟩⟩
    by_contra hk'
    exact hdeep ((hgood k (by omega)).mono (PartialAssignment.mem_extensions.1 hext).1)
  calc 2 ^ s * #{ρ' ∈ ρ.extensions ℓ' |
        ∃ k, p.depths k ≤ j + 1 ∧ ¬ Shallow s ρ' fun x => p.eval interpretation x k}
      ≤ 2 ^ s * ∑ k ∈ T, #{ρ' ∈ ρ.extensions ℓ' |
          ¬ Shallow s ρ' fun x => p.eval interpretation x k} :=
        Nat.mul_le_mul_left _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ k ∈ T, 2 ^ s * #{ρ' ∈ ρ.extensions ℓ' |
          ¬ Shallow s ρ' fun x => p.eval interpretation x k} := mul_sum _ _ _
    _ ≤ ∑ _k ∈ T, #(ρ.extensions ℓ') := sum_le_sum fun k hk => by
        -- gate `k` is its operation on shallow wires
        have hgate : (fun x => p.eval interpretation x k) = fun x =>
            interpretation (p.lines k).op fun a => p.trace interpretation x ((p.lines k).wires a) :=
          funext fun x => (p.lines_eval interpretation x k).symm
        rw [hgate]
        exact two_pow_mul_card_filter_not_shallow_le
          (shallow_trace_wires hs hgood (mem_filter.1 hk).2.le) hsℓ' hℓ
    _ = #T * #(ρ.extensions ℓ') := by rw [sum_const, smul_eq_mul]

/-- **Random restrictions make small circuits of constant depth shallow.** For a program with
gates of depth at most `d`, `s ≥ 2` and `s (16 s + 1) ^ d ≤ n`, after `j ≤ d` stages at most a
`G / 2 ^ s` fraction of the restrictions leaving `n / (16 s + 1) ^ j` bits free make some gate of
depth at most `j` deep, where `G` is the number of gates of depth at most `j`. -/
theorem two_pow_mul_card_filter_exists_not_shallow_le {p : Program signature n g} (hs : 2 ≤ s)
    {d : ℕ} (hn : s * (16 * s + 1) ^ d ≤ n) (j : ℕ) (hj : j ≤ d) :
    2 ^ s * #{ρ ∈ PartialAssignment.withFree (Fin n) (n / (16 * s + 1) ^ j) |
        ∃ k, p.depths k ≤ j ∧ ¬ Shallow s ρ fun x => p.eval interpretation x k} ≤
      #{k | p.depths k ≤ j} * #(PartialAssignment.withFree (Fin n) (n / (16 * s + 1) ^ j)) := by
  induction j with
  | zero =>
    rw [filter_false_of_mem fun ρ _ => fun ⟨k, hk, _⟩ => absurd hk (by
      have := p.depths_pos k
      omega)]
    simp
  | succ j ih =>
    have ih := ih (by omega)
    set ℓ := n / (16 * s + 1) ^ j
    set ℓ' := n / (16 * s + 1) ^ (j + 1)
    have hsℓ' : s ≤ ℓ' := Nat.le_div_pow_of_mul_pow_le (by omega) hj hn
    have hℓ : (16 * s + 1) * ℓ' ≤ ℓ := Nat.mul_div_pow_succ_le n _ j
    have hℓ'ℓ : ℓ' ≤ ℓ := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hℓ
    -- the gates of depth at most `j + 1`
    have hG : #{k | p.depths k ≤ j} + #{k | p.depths k = j + 1} ≤ #{k | p.depths k ≤ j + 1} := by
      rw [← card_union_of_disjoint (disjoint_filter.2 fun k _ h₁ h₂ => by omega)]
      refine card_le_card fun k hk => ?_
      simp only [mem_filter, mem_univ, true_and, mem_union] at hk ⊢
      omega
    -- each restriction with `ℓ` free bits has few bad extensions, unless it is bad itself
    refine PartialAssignment.mul_card_filter_withFree_le hℓ'ℓ (Nat.div_le_self _ _) ih
      (fun ρ hρ hb => ?_) hG
    refine two_pow_mul_card_filter_extensions_le hs hsℓ'
      ((PartialAssignment.mem_withFree.1 hρ).symm ▸ hℓ) fun k hk => ?_
    by_contra h
    exact hb ⟨k, hk, h⟩

/-! ### Circuits -/

/-- If every gate of depth at most the depth of a circuit is shallow under `ρ`, so is its output. -/
theorem shallow_output {C : Circuit signature n 1} (hs : 2 ≤ s)
    (hρ : ∀ k, C.program.depths k ≤ C.depth →
      Shallow s ρ fun x => C.program.eval interpretation x k) :
    Shallow s ρ fun x => C.program.trace interpretation x (C.outputs 0) := by
  cases hw : C.outputs 0 with
  | input i => exact shallow_proj hs ρ i
  | gate k =>
    refine hρ k ?_
    have := C.outputDepths_le_depth 0
    simpa only [Circuit.outputDepths, Function.comp_apply, hw, Program.wireDepths_gateWire]
      using this

/-- **Håstad's theorem** for circuits with unbounded fan-in. A circuit of depth `d` computing the
parity of `n` bits has at least `2 ^ s` gates, for every `s ≥ 2` with `s (16 s + 1) ^ d ≤ n`. -/
theorem two_pow_le_size_of_computes_parity {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) (hs : 2 ≤ s)
    (hn : s * (16 * s + 1) ^ C.depth ≤ n) : 2 ^ s ≤ C.size := by
  by_contra! hS
  set ℓ := n / (16 * s + 1) ^ C.depth
  have hsℓ : s ≤ ℓ := Nat.le_div_pow_of_mul_pow_le (by omega) le_rfl hn
  -- fewer than all restrictions leaving `ℓ` bits free make some gate deep
  have h := two_pow_mul_card_filter_exists_not_shallow_le (p := C.program) hs hn C.depth le_rfl
  have hW : 0 < #(PartialAssignment.withFree (Fin n) ℓ) := by
    rw [PartialAssignment.card_withFree, Fintype.card_fin]
    exact Nat.mul_pos (Nat.choose_pos (Nat.div_le_self _ _)) (by positivity)
  have hlt : #{ρ ∈ PartialAssignment.withFree (Fin n) ℓ | ∃ k, C.program.depths k ≤ C.depth ∧
      ¬ Shallow s ρ fun x => C.program.eval interpretation x k} <
      #(PartialAssignment.withFree (Fin n) ℓ) := by
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ s) (h.trans_lt ?_)
    exact Nat.mul_lt_mul_of_pos_right ((card_filter_le _ _).trans_lt (by simpa using hS)) hW
  obtain ⟨ρ, hρ, hgood⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hall : ∀ k, C.program.depths k ≤ C.depth →
      Shallow s ρ fun x => C.program.eval interpretation x k := fun k hk => by
    by_contra hdeep
    exact hgood (mem_filter.2 ⟨hρ, k, hk, hdeep⟩)
  have hout := shallow_output hs hall
  have heq : (fun x => C.program.trace interpretation x (C.outputs 0)) = parity n :=
    funext fun x => congrFun (hC x) 0
  rw [heq] at hout
  exact not_shallow_parity ((PartialAssignment.mem_withFree.1 hρ).symm ▸ hsℓ) hout

/-- **Håstad's theorem** for formulas with unbounded fan-in. A formula of depth `d` computing the
parity of `n` bits has at least `2 ^ s` operation nodes, for every `s ≥ 2` with
`s (16 s + 1) ^ d ≤ n`. -/
theorem two_pow_le_size_of_formula_computes_parity {F : Formula signature n}
    (hF : F.Computes interpretation (parity n)) (hs : 2 ≤ s)
    (hn : s * (16 * s + 1) ^ F.depth ≤ n) : 2 ^ s ≤ F.size :=
  F.size_toCircuit ▸ two_pow_le_size_of_computes_parity hF.toCircuit hs
    ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) F.depth_toCircuit_le)).trans hn)

end Unbounded

end Cslib.Circuits.Boolean
