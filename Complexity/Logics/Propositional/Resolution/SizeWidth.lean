/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Resolution.Proof
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Foundations.Data.List.Counting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The size–width tradeoff for resolution

[Ben-Sasson and Wigderson][BenSassonWigderson2001] showed that short resolution refutations can be
made narrow: a formula whose clauses have width at most `k`, over `N` variables, with a refutation
of `s` lines has a refutation of width at most `k + O(√(N log s))`
(`Cslib.Logic.PL.CNF.exists_refutableInWidth_le_of_refutableInSize`). Lower bounds on width thus
give lower bounds on size.

The proof fixes variables one at a time. Its core is a lemma about a single variable
(`Cslib.Logic.PL.CNF.RefutableInWidth.of_restrict`): if fixing `v` to `b` leaves a formula
refutable in width `w`, and fixing `v` to `!b` leaves one refutable in width `w + 1`, then the
formula is refutable in width `w + 1`, provided its clauses have width at most `w + 1`. Lifting the
first refutation derives the unit clause of `v` with the value `!b`, at the cost of one more
literal per line, or the empty clause outright. Resolving that unit clause with the clauses
containing `v` with the value `b` derives the clauses of the second restricted formula, and the
second refutation then replays on top.

A line of a refutation is *wide* when its width exceeds a threshold `d`. If a refutation has `f`
wide lines, some literal occurs in at least a `d / 2N` fraction of them, and fixing it to be true
satisfies those lines and leaves a refutation of the restricted formula with at most
`f (1 - d / 2N)` wide lines; fixing it to be false leaves at most `f` of them, over fewer variables.
By induction, if `f (2N - d) ^ b < (2N) ^ b` then the formula is refutable in width `max d k + b`
(`Cslib.Logic.PL.CNF.RefutableInWidth.of_refutableInSize`). Choosing `d` and `b` of order
`√(N log s)` gives the tradeoff.

## Main results

* `Cslib.Logic.PL.CNF.RefutableInWidth.of_restrict`: the key lemma on fixing one variable.
* `Cslib.Logic.PL.CNF.RefutableInWidth.of_refutableInSize`: refutations with few wide lines can be
  made narrow.
* `Cslib.Logic.PL.CNF.exists_refutableInWidth_le_of_refutableInSize`: **the size–width
  tradeoff**: a formula with clauses of width at most `k` over `N` variables, refutable with `s`
  lines, is refutable in width at most `k + 2 √(2 N log s) + 2`.
* `Cslib.Logic.PL.CNF.exp_le_of_refutableInSize`: the same as a size lower bound: if refutations
  need width `W ≥ k + 2`, they need `exp ((W - k - 2)² / 8N)` lines.

## References

* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow—resolution made
  simple*][BenSassonWigderson2001]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V : Type*} [DecidableEq V]

namespace CNF

variable {φ : CNF V}

/-! ### Fixing one variable -/

/-- Lines resolved from lines of a proof, or clauses of the formula, extend the proof. -/
theorem IsProof.append_of_forall {ls es : List (Clause V)} (h : φ.IsProof ls)
    (hes : ∀ e ∈ es, e ∈ φ ∨ ∃ c₁ ∈ ls, ∃ c₂ ∈ ls, ∃ u, (u, true) ∈ c₁ ∧ (u, false) ∈ c₂ ∧
      e = c₁.resolvent c₂ u) :
    φ.IsProof (es ++ ls) := by
  induction es with
  | nil => exact h
  | cons e es ih =>
    have ih := ih fun e he => hes e (List.mem_cons_of_mem _ he)
    rcases hes e List.mem_cons_self with he | ⟨c₁, h₁, c₂, h₂, u, hu₁, hu₂, rfl⟩
    · exact ih.mem he
    · exact ih.resolvent u (List.mem_append_right _ h₁) (List.mem_append_right _ h₂) hu₁ hu₂

/-- Clauses of a formula, listed in any order, form a proof from it. -/
theorem IsProof.of_forall_mem {es : List (Clause V)} (hes : ∀ e ∈ es, e ∈ φ) : φ.IsProof es := by
  simpa using IsProof.nil.append_of_forall (φ := φ) fun e he => Or.inl (hes e he)

/-- Fixing a variable does not widen clauses. -/
theorem width_le_of_mem_restrict {v : V} {b : Bool} {k : ℕ} (hk : ∀ c ∈ φ, c.width ≤ k)
    {c : Clause V} (hc : c ∈ φ.restrict v b) : c.width ≤ k := by
  obtain ⟨d, hd, -, rfl⟩ := mem_restrict.1 hc
  exact (Clause.width_le_width fun l hl => (List.mem_filter.1 hl).1).trans (hk d hd)

/-- **Fixing one variable** [Ben-Sasson and Wigderson, Lemma 3.2][BenSassonWigderson2001]. If the
clauses of `φ` have width at most `w + 1`, `φ` with `v` fixed to `b` is refutable in width `w`, and
`φ` with `v` fixed to `!b` is refutable in width `w + 1`, then `φ` is refutable in width `w + 1`. -/
theorem RefutableInWidth.of_restrict {v : V} {b : Bool} {w : ℕ}
    (hφ : ∀ c ∈ φ, c.width ≤ w + 1) (h₁ : (φ.restrict v b).RefutableInWidth w)
    (h₂ : (φ.restrict v (!b)).RefutableInWidth (w + 1)) : φ.RefutableInWidth (w + 1) := by
  obtain ⟨ls₁, hp₁, hnil₁, hw₁⟩ := h₁
  obtain ⟨ls, hp, hup, hdown⟩ := hp₁.lift
  have hw : ∀ c ∈ ls, c.width ≤ w + 1 := fun c hc => by
    obtain ⟨c', hc', hsub⟩ := hdown c hc
    exact (Clause.width_le_width_add_one hsub).trans (Nat.succ_le_succ (hw₁ c' hc'))
  -- lifting the first refutation derives a clause `c₀` whose literals are all `(v, !b)`
  obtain ⟨c₀, hc₀, -, hc₀v⟩ := hup [] hnil₁
  have hc₀v : ∀ l ∈ c₀, l = (v, !b) := fun l hl => (hc₀v l hl).resolve_left List.not_mem_nil
  by_cases hx : (v, !b) ∈ c₀
  swap
  · have : c₀ = [] := List.eq_nil_iff_forall_not_mem.2 fun l hl => hx (hc₀v l hl ▸ hl)
    exact ⟨ls, hp, this ▸ hc₀, hw⟩
  have hfilter : c₀.filter (· ≠ (v, !b)) = [] :=
    List.filter_eq_nil_iff.2 fun l hl => by simpa using hc₀v l hl
  -- the clauses of the second restricted formula are clauses of `φ` or resolvents with `c₀`
  have hψ : φ.IsProof (φ.restrict v (!b) ++ (φ ++ ls)) := by
    refine ((IsProof.of_forall_mem fun e he => he).append hp).append_of_forall fun e he => ?_
    obtain ⟨d, hd, -, rfl⟩ := mem_restrict.1 he
    by_cases hvd : (v, b) ∈ d
    · refine Or.inr ?_
      cases b
      · refine ⟨c₀, List.mem_append_right _ hc₀, d, List.mem_append_left _ hd, v, hx, hvd, ?_⟩
        simp only [Clause.resolvent, Bool.not_false, Bool.not_true] at hfilter ⊢
        rw [hfilter, List.nil_append]
      · refine ⟨d, List.mem_append_left _ hd, c₀, List.mem_append_right _ hc₀, v, hvd, hx, ?_⟩
        simp only [Clause.resolvent, Bool.not_true, Bool.not_false] at hfilter ⊢
        rw [hfilter, List.append_nil]
    · refine Or.inl ?_
      rw [Bool.not_not, List.filter_eq_self.2 fun l hl => by
        simp only [ne_eq, decide_eq_true_eq]
        rintro rfl
        exact hvd hl]
      exact hd
  obtain ⟨ls₂, hp₂, hnil₂, hw₂⟩ := h₂
  obtain ⟨ls'', hp'', hup'', hdown''⟩ := hp₂.comp hψ fun c hc => List.mem_append_left _ hc
  refine ⟨_, hp'', hup'' _ hnil₂, fun c hc => ?_⟩
  rcases List.mem_append.1 hc with hc | hc
  · exact hw₂ c (hdown'' c hc)
  rcases List.mem_append.1 hc with hc | hc
  · exact width_le_of_mem_restrict hφ hc
  rcases List.mem_append.1 hc with hc | hc
  exacts [hφ c hc, hw c hc]

/-! ### Wide lines -/

/-- **Double counting**: summing over literals the number of clauses of a list containing them
gives the total width, when the literals of the clauses are among the summed literals. -/
private theorem sum_countP_mem_eq_sum_width (U : Finset (Literal V)) :
    ∀ F : List (Clause V), (∀ c ∈ F, ∀ l ∈ c, l ∈ U) →
      ∑ l ∈ U, F.countP (fun c => l ∈ c) = (F.map Clause.width).sum
  | [], _ => by simp
  | c :: F, hF => by
    simp only [List.countP_cons, Finset.sum_add_distrib, List.map_cons, List.sum_cons]
    rw [sum_countP_mem_eq_sum_width U F fun c hc => hF c (List.mem_cons_of_mem _ hc), add_comm]
    congr 1
    rw [Finset.sum_boole, Nat.cast_id, Clause.width]
    congr 1
    ext l
    simp only [decide_eq_true_eq, Finset.mem_filter, List.mem_toFinset, and_iff_right_iff_imp]
    exact hF c List.mem_cons_self l

/-- **Some literal lies in many wide lines.** If the lines of a nonempty list are wider than `d`
and their literals are among the literals `U`, some literal of `U` occurs in more than a
`d / |U|` fraction of the lines. -/
private theorem exists_lt_countP_mem (U : Finset (Literal V)) (d : ℕ) (F : List (Clause V))
    (hF : ∀ c ∈ F, ∀ l ∈ c, l ∈ U) (hwide : ∀ c ∈ F, d < c.width) (hne : F ≠ []) :
    ∃ l ∈ U, d * F.length < F.countP (fun c => l ∈ c) * U.card := by
  by_contra! h
  have hsum := sum_countP_mem_eq_sum_width U F hF
  have hle : (F.map Clause.width).sum * U.card ≤ U.card * (d * F.length) := by
    rw [← hsum, Finset.sum_mul]
    exact (Finset.sum_le_sum h).trans (by simp)
  have hge : F.length * (d + 1) ≤ (F.map Clause.width).sum := by
    have := List.sum_le_sum (l := F) (f := fun _ => d + 1) (g := Clause.width)
      fun c hc => hwide c hc
    simpa using this
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil F hne
  have hU : 0 < U.card := by
    obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil c fun hnil => by
      have := hwide c hc
      simp [hnil] at this
    exact Finset.card_pos.2 ⟨l, hF c hc l hl⟩
  have hlen : 0 < F.length := List.length_pos_iff.2 hne
  have key := (Nat.mul_le_mul_right U.card hge).trans hle
  have := Nat.mul_pos hlen hU
  nlinarith

/-- The literals of the lines of a proof from `φ` are literals of variables of `φ`. -/
private theorem mem_literals_of_isProof {ls : List (Clause V)} (h : φ.IsProof ls) :
    ∀ c ∈ ls, ∀ l ∈ c, l ∈ φ.vars.toFinset ×ˢ (Finset.univ : Finset Bool) :=
  fun _ hc _ hl => Finset.mem_product.2 ⟨List.mem_toFinset.2 (h.fst_mem_vars hc hl),
    Finset.mem_univ _⟩

/-- The induction behind `RefutableInWidth.of_refutableInSize`, on a bound `n` on the number of
variables. -/
private theorem refutableInWidth_of_countP_wide (N d k : ℕ) :
    ∀ (n : ℕ) (φ : CNF V) (ls : List (Clause V)) (b : ℕ), φ.vars.toFinset.card ≤ n → n ≤ N →
      φ.IsProof ls → [] ∈ ls → (∀ c ∈ φ, c.width ≤ k) →
      ls.countP (fun c => d < c.width) * (2 * N - d) ^ b < (2 * N) ^ b →
      φ.RefutableInWidth (max d k + b) := by
  intro n
  induction n with
  | zero =>
    intro φ ls b hn _ h hnil _ _
    refine ⟨ls, h, hnil, fun c hc => ?_⟩
    have := h.width_le hc
    omega
  | succ n ih =>
    intro φ ls b hn hnN h hnil hk hcount
    set f := ls.countP (fun c => d < c.width) with hf
    rcases Nat.eq_zero_or_pos f with hf0 | hfpos
    · -- no wide lines
      refine ⟨ls, h, hnil, fun c hc => ?_⟩
      have := List.countP_eq_zero.1 hf0 c hc
      simp only [decide_eq_true_eq, not_lt] at this
      omega
    -- the wide lines, and a literal `(v, β)` occurring in many of them
    set F := ls.filter (fun c => d < c.width)
    have hFlen : F.length = f := by rw [hf, List.countP_eq_length_filter]
    have hFne : F ≠ [] := by
      intro hF
      rw [hF, List.length_nil] at hFlen
      omega
    obtain ⟨⟨v, β⟩, hU, hmany⟩ := exists_lt_countP_mem _ d F
      (fun c hc => mem_literals_of_isProof h c (List.mem_filter.1 hc).1)
      (fun c hc => by simpa using (List.mem_filter.1 hc).2) hFne
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, hFlen] at hmany
    have hv : v ∈ φ.vars.toFinset := (Finset.mem_product.1 hU).1
    -- there are wide lines, so `d < 2N`, and `b` is positive
    have hdN : d < 2 * N := by
      obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil F hFne
      have h1 := (List.mem_filter.1 hc)
      have := h.width_le h1.1
      simp only [decide_eq_true_eq] at h1
      omega
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := by
      rcases b with _ | b
      · simp only [pow_zero, mul_one, Nat.lt_one_iff] at hcount
        omega
      · exact ⟨b, rfl⟩
    have hvars (γ : Bool) : (φ.restrict v γ).vars.toFinset.card ≤ n := by
      have := (Finset.card_le_card (vars_restrict_subset (b := γ))).trans_eq
        (Finset.card_erase_of_mem hv)
      omega
    have hk' (γ : Bool) : ∀ c ∈ φ.restrict v γ, c.width ≤ k := fun c hc =>
      width_le_of_mem_restrict hk hc
    -- the restrictions of the refutation
    have hres (γ : Bool) : ∃ ls', (φ.restrict v γ).IsProof ls' ∧ [] ∈ ls' ∧
        ls'.countP (fun c => d < c.width) ≤
          ls.countP (fun c => (v, γ) ∉ c ∧ d < c.width) := by
      obtain ⟨ls', h', -, hsub, hcount'⟩ := h.restrict v γ
      obtain ⟨c', hc', hsub'⟩ := hsub [] hnil List.not_mem_nil
      have : c' = [] := List.eq_nil_iff_forall_not_mem.2 fun l hl => List.not_mem_nil (hsub' l hl)
      exact ⟨ls', h', this ▸ hc', hcount' d⟩
    -- fixing the literal to be true removes the many wide lines containing it
    obtain ⟨ls₁, h₁, hnil₁, hcount₁⟩ := hres β
    have hsplit := List.countP_and_not_add_countP_and (fun c => d < Clause.width c)
      (fun c => (v, β) ∈ c) ls
    have hcnt : F.countP (fun c => (v, β) ∈ c) = ls.countP (fun c => d < c.width ∧ (v, β) ∈ c) := by
      rw [List.countP_filter]
      congr 1
      funext c
      simp [Bool.and_comm]
    rw [hcnt] at hmany
    have hpow : (2 * N - d) * (2 * N) ^ b ≤ (2 * N) ^ (b + 1) := by
      rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have hwidth₁ : (φ.restrict v β).RefutableInWidth (max d k + b) := by
      refine ih _ ls₁ b (hvars β) (by omega) h₁ hnil₁ (hk' β) ?_
      -- `f₁ * 2N < f * (2N - d)`, hence `f₁ (2N - d)^b < (2N)^b`
      have hf₁ : ls₁.countP (fun c => d < c.width) * (2 * N) < f * (2 * N - d) := by
        have h₂ : ls₁.countP (fun c => d < c.width) +
            ls.countP (fun c => d < c.width ∧ (v, β) ∈ c) ≤ f := by
          simp only [hf]
          omega
        rw [Nat.mul_sub, Nat.lt_sub_iff_add_lt]
        nlinarith
      have hpos : 0 < 2 * N := by omega
      refine Nat.lt_of_mul_lt_mul_right (a := 2 * N) ?_
      calc ls₁.countP (fun c => d < c.width) * (2 * N - d) ^ b * (2 * N)
          = ls₁.countP (fun c => d < c.width) * (2 * N) * (2 * N - d) ^ b := by ring
        _ < f * (2 * N - d) * (2 * N - d) ^ b :=
          Nat.mul_lt_mul_of_pos_right hf₁ (Nat.pow_pos (by omega))
        _ = f * (2 * N - d) ^ (b + 1) := by ring
        _ < (2 * N) ^ (b + 1) := hcount
        _ = (2 * N) ^ b * (2 * N) := pow_succ _ _
    -- fixing it to be false keeps at most the same wide lines, over fewer variables
    obtain ⟨ls₀, h₀, hnil₀, hcount₀⟩ := hres (!β)
    have hwidth₀ : (φ.restrict v (!β)).RefutableInWidth (max d k + (b + 1)) := by
      refine ih _ ls₀ (b + 1) (hvars _) (by omega) h₀ hnil₀ (hk' _) ?_
      refine lt_of_le_of_lt (Nat.mul_le_mul_right _ ?_) hcount
      exact hcount₀.trans (List.countP_mono_left fun c _ hc => by
        simp only [decide_eq_true_eq] at hc ⊢
        exact hc.2)
    exact RefutableInWidth.of_restrict (w := max d k + b) (fun c hc => (hk c hc).trans (by omega))
      hwidth₁ hwidth₀

/-- **Refutations with few wide lines can be made narrow** [Ben-Sasson and Wigderson, Theorem 3.5]
[BenSassonWigderson2001]. Let the clauses of `φ` have width at most `k`, and let `φ` have at most
`N` variables. If `φ` has a refutation of `s` lines, and `s (2N - d) ^ b < (2N) ^ b`, then `φ` is
refutable in width at most `max d k + b`. -/
theorem RefutableInWidth.of_refutableInSize {k s N d b : ℕ} (hk : ∀ c ∈ φ, c.width ≤ k)
    (hN : φ.vars.toFinset.card ≤ N) (hs : φ.RefutableInSize s)
    (hsdb : s * (2 * N - d) ^ b < (2 * N) ^ b) : φ.RefutableInWidth (max d k + b) := by
  obtain ⟨ls, h, hnil, hlen⟩ := hs
  refine refutableInWidth_of_countP_wide N d k N φ ls b hN le_rfl h hnil hk ?_
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (List.countP_le_length.trans hlen)) hsdb

/-! ### The size–width tradeoff -/

/-- **The size–width tradeoff** [Ben-Sasson and Wigderson, Theorem 3.5 and Corollary 3.6]
[BenSassonWigderson2001].
A formula whose clauses have width at most `k`, with at most `N` variables, that has a refutation
of `s` lines has a refutation of width at most `k + 2 √(2 N log s) + 2`. Equivalently, a formula
that needs width `w ≥ k + 2`, with `N > 0`, needs refutations of at least
`exp ((w - k - 2)² / 8N)` lines. -/
theorem exists_refutableInWidth_le_of_refutableInSize {k s N : ℕ} (hk : ∀ c ∈ φ, c.width ≤ k)
    (hN : φ.vars.toFinset.card ≤ N) (hs : φ.RefutableInSize s) :
    ∃ w : ℕ, φ.RefutableInWidth w ∧
      (w : ℝ) ≤ k + 2 * √(2 * N * Real.log s) + 2 := by
  obtain ⟨ls, h, hnil, hlen⟩ := hs
  have hL : 0 ≤ 2 * (N : ℝ) * Real.log s := by
    have : (1 : ℝ) ≤ s := by
      have := List.length_pos_of_mem hnil
      exact_mod_cast this.trans_le hlen
    have := Real.log_nonneg this
    positivity
  have hpos : 0 ≤ k + 2 * √(2 * N * Real.log s) + 2 := by positivity
  -- without variables or with a single line, every line of the refutation is empty
  by_cases htriv : N = 0 ∨ s ≤ 1
  · refine ⟨0, ⟨ls, h, hnil, fun c hc => ?_⟩, by exact_mod_cast hpos⟩
    rcases htriv with hN0 | hs1
    · have := h.width_le hc
      omega
    · obtain rfl : ls = [[]] := by
        rcases ls with _ | ⟨c₀, _ | ⟨c₁, ls⟩⟩
        · simp at hnil
        · simpa using hnil
        · simp only [List.length_cons] at hlen
          omega
      simp_all
  push Not at htriv
  obtain ⟨hN0, hs1⟩ := htriv
  set L := 2 * (N : ℝ) * Real.log s with hLdef
  have hLpos : 0 < L := by
    have : 0 < Real.log s := Real.log_pos (by exact_mod_cast hs1)
    positivity
  set d := ⌈√L⌉₊ with hd
  set b := ⌊L / d⌋₊ + 1 with hb
  have hsqrt : 0 < √L := Real.sqrt_pos.2 hLpos
  have hdpos : (0 : ℝ) < d := hsqrt.trans_le (Nat.le_ceil _)
  have hLd : L / d ≤ √L := by
    rw [div_le_iff₀ hdpos]
    calc L = √L * √L := (Real.mul_self_sqrt hLpos.le).symm
      _ ≤ √L * d := mul_le_mul_of_nonneg_left (Nat.le_ceil _) hsqrt.le
  -- `s (2N - d)^b < (2N)^b`, from `(1 - d/2N)^b ≤ exp (-db/2N) < 1/s`
  have hsdb : s * (2 * N - d) ^ b < (2 * N) ^ b := by
    rcases le_or_gt (2 * N) d with hdN | hdN
    · rw [Nat.sub_eq_zero_of_le hdN, zero_pow (by omega), mul_zero]
      positivity
    have hN' : (0 : ℝ) < 2 * N := by positivity
    have hdb : L < d * b := by
      rw [← div_lt_iff₀' hdpos]
      exact_mod_cast Nat.lt_floor_add_one (L / d)
    have h1 : ((2 * N - d : ℕ) : ℝ) = 2 * N * (1 - d / (2 * N)) := by
      rw [Nat.cast_sub hdN.le]
      field_simp
      push_cast
      ring
    have hx0 : 0 ≤ 1 - (d : ℝ) / (2 * N) := by
      rw [sub_nonneg, div_le_one hN']
      exact_mod_cast hdN.le
    have hx1 : 1 - (d : ℝ) / (2 * N) ≤ Real.exp (-(d / (2 * N))) := by
      linarith [Real.add_one_le_exp (-((d : ℝ) / (2 * N)))]
    have hexp : ((2 * N - d : ℕ) : ℝ) ^ b ≤ (2 * N) ^ b * Real.exp (b * -(d / (2 * N))) := by
      rw [h1, mul_pow, Real.exp_nat_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx1 b) (by positivity)
    have hlt : (s : ℝ) * Real.exp (b * -(d / (2 * N))) < 1 := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < s), ← Real.exp_add, Real.exp_lt_one_iff]
      have : Real.log s < d * b / (2 * N) := by
        rw [lt_div_iff₀ hN']
        linarith
      have h2 : (b : ℝ) * -(d / (2 * N)) = -(d * b / (2 * N)) := by ring
      linarith
    have : (s : ℝ) * ((2 * N - d : ℕ) : ℝ) ^ b < (2 * N) ^ b := by
      calc (s : ℝ) * ((2 * N - d : ℕ) : ℝ) ^ b
          ≤ s * ((2 * N) ^ b * Real.exp (b * -(d / (2 * N)))) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = (2 * N) ^ b * (s * Real.exp (b * -(d / (2 * N)))) := by ring
        _ < (2 * N) ^ b * 1 := mul_lt_mul_of_pos_left hlt (by positivity)
        _ = (2 * N) ^ b := mul_one _
    exact_mod_cast this
  refine ⟨_, RefutableInWidth.of_refutableInSize hk hN ⟨ls, h, hnil, hlen⟩ hsdb, ?_⟩
  -- `max d k + b ≤ k + (√L + 1) + (√L + 1)`
  have hd' : (d : ℝ) ≤ √L + 1 := (Nat.ceil_lt_add_one (Real.sqrt_nonneg L)).le
  have hb' : (b : ℝ) ≤ √L + 1 := by
    rw [hb, Nat.cast_add, Nat.cast_one]
    linarith [(Nat.floor_le (div_nonneg hLpos.le hdpos.le)).trans hLd]
  have hmax : ((max d k + b : ℕ) : ℝ) ≤ d + k + b := by
    push_cast
    have := max_le_add_of_nonneg (Nat.cast_nonneg (α := ℝ) d) (Nat.cast_nonneg (α := ℝ) k)
    linarith
  linarith

/-- **Width lower bounds give size lower bounds** [Ben-Sasson and Wigderson, Corollary 3.6]
[BenSassonWigderson2001]. Let the clauses of `φ` have width at most `k`, and let `φ` have at most
`N` variables. If every resolution refutation of `φ` has width at least `W ≥ k + 2`, then every
resolution refutation of `φ` has at least `exp ((W - k - 2)² / 8N)` lines. -/
theorem exp_le_of_refutableInSize {k N W s : ℕ} (hk : ∀ c ∈ φ, c.width ≤ k)
    (hN : φ.vars.toFinset.card ≤ N) (hW : ∀ w, φ.RefutableInWidth w → W ≤ w)
    (hkW : k + 2 ≤ W) (hs : φ.RefutableInSize s) :
    Real.exp (((W : ℝ) - k - 2) ^ 2 / (8 * N)) ≤ s := by
  obtain ⟨w, hw, hwle⟩ := exists_refutableInWidth_le_of_refutableInSize hk hN hs
  have he : (W : ℝ) ≤ w := by exact_mod_cast hW w hw
  have hs1 : (1 : ℝ) ≤ s := by
    obtain ⟨ls, -, hnil, hlen⟩ := hs
    exact_mod_cast (List.length_pos_of_mem hnil).trans_le hlen
  have hlog := Real.log_nonneg hs1
  have hkW' : (k : ℝ) + 2 ≤ W := by exact_mod_cast hkW
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · simpa using hs1
  rw [← Real.exp_log (by linarith : (0 : ℝ) < s), Real.exp_le_exp,
    div_le_iff₀ (by positivity)]
  -- `W - k - 2 ≤ 2 √(2 N log s)`
  have hx : (W : ℝ) - k - 2 ≤ 2 * √(2 * N * Real.log s) := by linarith
  have hsq := pow_le_pow_left₀ (by linarith) hx 2
  rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
  nlinarith

end CNF

end Cslib.Logic.PL
