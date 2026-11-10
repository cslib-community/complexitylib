/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.BooleanClone.Classification
public import Complexity.Logics.BooleanClone.Generated
public import Complexity.Foundations.Data.BitString.Affine
import Mathlib.Tactic.FinCases

/-!
# Post's functional completeness criterion

A family of positive-arity Boolean operations generates every positive-arity Boolean function
exactly when it is contained in none of the five classes: preserving false, preserving true,
monotone, self-dual, and affine. This is [PelletierMartin1990], the theorem on printed p. 466.
Families may be infinite and operation arities are unbounded. Constants are unary constant
functions, as in the shared Schaefer clone API; no nullary gate is synthesized.

The affine class uses `Cslib.BitString.IsAffine`, preservation of sums of three points over
`𝔽₂`, equivalently a constant plus a parity of selected inputs. The source's "counting"
functions have exactly this meaning. NOT and constants follow the source's Lemmas 1–2,
pp. 466–467. The remainder is an original combination of the shared four-generator Boolean
clone classification with a binary affine-witness construction, followed by truth-table
normalization and disjunctive normal form. The full lattice of Boolean clones is not asserted.

## Main definitions

* `Cslib.Logic.BooleanClone.PostCriterion`: a witness outside each of the five closed classes.

## Main results

* `Cslib.Logic.BooleanClone.isComplete_iff_postCriterion`: the criterion for a Boolean clone.
* `Cslib.Logic.BooleanClone.functionallyComplete_iff`: Post's criterion for a generating family.

## References

* [F. J. Pelletier and N. M. Martin, *Post's Functional Completeness Theorem*][PelletierMartin1990],
  printed pp. 466–469.
-/

public section

namespace Cslib.Logic.BooleanClone

/-- Unary negation. -/
@[expose] def notOp (a : Fin 1 → Bool) : Bool := !(a 0)

/-- A positive-arity witness outside each of Post's five composition-closed classes.
Witnesses may have different arities and the same operation may serve several clauses. -/
@[expose] def PostCriterion (G : (n : ℕ) → Set ((Fin n → Bool) → Bool)) : Prop :=
  (∃ n, 0 < n ∧ ∃ f ∈ G n, f (fun _ => false) ≠ false) ∧
  (∃ n, 0 < n ∧ ∃ f ∈ G n, f (fun _ => true) ≠ true) ∧
  (∃ n, 0 < n ∧ ∃ f ∈ G n, ¬ Monotone f) ∧
  (∃ n, 0 < n ∧ ∃ f ∈ G n, ¬ ∀ a, f (fun i => !(a i)) = !(f a)) ∧
  (∃ n, 0 < n ∧ ∃ f ∈ G n, ¬ BitString.IsAffine f)

/-- Enlarging the positive-arity generators preserves the five witnesses. -/
theorem PostCriterion.mono {G H : (n : ℕ) → Set ((Fin n → Bool) → Bool)}
    (hG : PostCriterion G) (h : ∀ n, 0 < n → G n ⊆ H n) : PostCriterion H := by
  rcases hG with ⟨hzero, hone, hmono, hself, haff⟩
  have lift {P : (n : ℕ) → ((Fin n → Bool) → Bool) → Prop}
      (hP : ∃ n, 0 < n ∧ ∃ f ∈ G n, P n f) : ∃ n, 0 < n ∧ ∃ f ∈ H n, P n f := by
    obtain ⟨n, hn, f, hf, hbad⟩ := hP
    exact ⟨n, hn, f, h n hn hf, hbad⟩
  exact ⟨lift hzero, lift hone, lift hmono, lift hself, lift haff⟩

variable (C : BooleanClone)

/-- Substitute an available operation into unary negation. -/
theorem comp_not {n : ℕ} (hnot : notOp ∈ C.operations 1)
    {f : (Fin n → Bool) → Bool} (hf : f ∈ C.operations n) :
    (fun a => !(f a)) ∈ C.operations n :=
  C.comp (by decide) (C.arity_pos hf) hnot (fun _ => hf)

/-- Apply an available binary conjunction to two available operations. -/
theorem comp_and {n : ℕ} (hand : andOp ∈ C.operations 2)
    {f g : (Fin n → Bool) → Bool} (hf : f ∈ C.operations n) (hg : g ∈ C.operations n) :
    (fun a => f a && g a) ∈ C.operations n := by
  exact C.comp (by decide) (C.arity_pos hf) (g := ![f, g]) hand (Fin.forall_fin_two.mpr ⟨hf, hg⟩)

/-- Apply an available binary disjunction to two available operations. -/
theorem comp_or {n : ℕ} (hor : orOp ∈ C.operations 2)
    {f g : (Fin n → Bool) → Bool} (hf : f ∈ C.operations n) (hg : g ∈ C.operations n) :
    (fun a => f a || g a) ∈ C.operations n := by
  exact C.comp (by decide) (C.arity_pos hf) (g := ![f, g]) hor (Fin.forall_fin_two.mpr ⟨hf, hg⟩)

/-- A unary constant supplies the same constant at every positive arity. -/
theorem const_mem {n : ℕ} (hn : 0 < n) {b : Bool}
    (hb : (fun _ : Fin 1 → Bool => b) ∈ C.operations 1) :
    (fun _ : Fin n → Bool => b) ∈ C.operations n :=
  C.minor (by decide) hn hb (fun _ => ⟨0, hn⟩)

/-- Failure of preservation of both constants and of monotonicity generates NOT.
This is Lemma 1 of [PelletierMartin1990], printed pp. 466–467. -/
theorem not_mem_of_witnesses
    (hzero : ∃ n, 0 < n ∧ ∃ f ∈ C.operations n, f (fun _ => false) ≠ false)
    (hone : ∃ n, 0 < n ∧ ∃ f ∈ C.operations n, f (fun _ => true) ≠ true)
    (hmono : ∃ n, 0 < n ∧ ∃ f ∈ C.operations n, ¬ Monotone f) :
    notOp ∈ C.operations 1 := by
  obtain ⟨n, hn, f, hf, hf0⟩ := hzero
  obtain ⟨m, hm, g, hg, hg1⟩ := hone
  have hf0' : f (fun _ => false) = true := by cases h0 : f (fun _ => false) <;> simp_all
  have hg1' : g (fun _ => true) = false := by cases h1 : g (fun _ => true) <;> simp_all
  by_cases hf1 : f (fun _ => true) = false
  · convert C.diagonal hn hf using 1
    funext a
    cases ha : a 0 <;> simp [notOp, ha, hf0', hf1]
  by_cases hg0 : g (fun _ => false) = true
  · convert C.diagonal hm hg using 1
    funext a
    cases ha : a 0 <;> simp [notOp, ha, hg0, hg1']
  have hfalse : (fun _ : Fin 1 → Bool => false) ∈ C.operations 1 := by
    convert C.diagonal hm hg using 1
    funext a
    cases ha : a 0 <;> simp [hg0, hg1']
  have htrue : (fun _ : Fin 1 → Bool => true) ∈ C.operations 1 := by
    convert C.diagonal hn hf using 1
    funext a
    cases ha : a 0 <;> simp [hf0', hf1]
  obtain ⟨k, hk, h, hh, hnonmono⟩ := hmono
  simp only [Monotone, not_forall] at hnonmono
  obtain ⟨a, b, hab, hbad⟩ := hnonmono
  have hvals := Bool.lt_iff.mp (lt_of_not_ge hbad)
  have ha : h a = true := hvals.2
  have hb : h b = false := hvals.1
  let args (i : Fin k) (x : Fin 1 → Bool) : Bool :=
    if a i then true else if b i then x 0 else false
  have hargs (i) : args i ∈ C.operations 1 := by
    cases hai : a i <;> cases hbi : b i
    · simpa [args, hai, hbi] using hfalse
    · simpa [args, hai, hbi] using C.projection (0 : Fin 1)
    · simpa [args, hai] using htrue
    · simpa [args, hai] using htrue
  convert C.comp hk (by decide) hh hargs using 1
  funext x
  cases hx : x 0
  · have he : (fun i => args i x) = a := by
      funext i
      simp only [args, hx]
      cases a i <;> cases b i <;> rfl
    simp [notOp, hx, he, ha]
  · have he : (fun i => args i x) = b := by
      funext i
      have hi := hab i
      cases hai : a i <;> cases hbi : b i <;> simp_all [args, Bool.le_iff_imp]
    simp [notOp, hx, he, hb]

/-- NOT and failure of self-duality supply both unary constant functions.
This is Lemma 2 of [PelletierMartin1990], printed p. 467. -/
theorem constants_mem_of_not_selfDual (hnot : notOp ∈ C.operations 1)
    (hself : ∃ n, 0 < n ∧ ∃ f ∈ C.operations n,
      ¬ ∀ a, f (fun i => !(a i)) = !(f a)) :
    ∀ b, (fun _ : Fin 1 → Bool => b) ∈ C.operations 1 := by
  obtain ⟨n, hn, f, hf, hself⟩ := hself
  push Not at hself
  obtain ⟨a, ha⟩ := hself
  have he : f (fun i => !(a i)) = f a := by
    cases h0 : f a <;> cases h1 : f (fun i => !(a i)) <;> simp_all
  let args (i : Fin n) (x : Fin 1 → Bool) : Bool := if a i then x 0 else !(x 0)
  have hargs (i) : args i ∈ C.operations 1 := by
    dsimp only [args]
    cases a i <;> first | exact hnot | exact C.projection 0
  have hc : (fun _ : Fin 1 → Bool => f a) ∈ C.operations 1 := by
    convert C.comp hn (by decide) hf hargs using 1
    funext x
    cases hx : x 0
    · have he' : (fun i => args i x) = fun i => !(a i) := by
        funext i; cases hai : a i <;> simp [args, hx, hai]
      exact ((congrArg f he').trans he).symm
    · congr 1
      funext i; cases hai : a i <;> simp [args, hx, hai]
  intro b
  cases hfa : f a <;> cases b
  · simpa only [hfa] using hc
  · simpa only [hfa, Bool.not_false] using C.comp_not hnot hc
  · simpa only [hfa, Bool.not_true] using C.comp_not hnot hc
  · simpa only [hfa] using hc

/-- Compose two operations with available XOR. -/
theorem comp_xor {n : ℕ} (hxor : Cslib.parity 2 ∈ C.operations 2)
    {f g : (Fin n → Bool) → Bool} (hf : f ∈ C.operations n) (hg : g ∈ C.operations n) :
    (fun a => f a ^^ g a) ∈ C.operations n := by
  have hx : (fun a : Fin 2 → Bool => a 0 ^^ a 1) ∈ C.operations 2 := by
    convert hxor using 1
    decide
  exact C.comp (by decide) (C.arity_pos hf) (g := ![f, g]) hx
    (Fin.forall_fin_two.mpr ⟨hf, hg⟩)

/-- Any binary truth table of odd parity generates AND in the presence of NOT. -/
theorem and_mem_of_odd_binary (hnot : notOp ∈ C.operations 1)
    {f : (Fin 2 → Bool) → Bool} (hf : f ∈ C.operations 2)
    (hodd : (f ![false, false] ^^ f ![false, true] ^^ f ![true, false] ^^ f ![true, true]) = true) :
    andOp ∈ C.operations 2 := by
  have hnorm : ∃ p q r : Bool, ∀ a : Fin 2 → Bool,
      (f ![a 0 ^^ p, a 1 ^^ q] ^^ r) = andOp a := by
    rw [binaryTable_eq f] at hodd ⊢
    generalize f ![false, false] = b00 at *
    generalize f ![false, true] = b01 at *
    generalize f ![true, false] = b10 at *
    generalize f ![true, true] = b11 at *
    cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;>
      first | contradiction | decide
  obtain ⟨p, q, r, hr⟩ := hnorm
  have hargs (i : Fin 2) : (fun a : Fin 2 → Bool => a i ^^ (![p, q] : Fin 2 → Bool) i)
      ∈ C.operations 2 := by
    cases h : (![p, q] : Fin 2 → Bool) i
    · simpa only [h, Bool.xor_false] using C.projection i
    · simpa only [h, Bool.xor_true] using C.comp_not hnot (C.projection i)
  have hcomp := C.comp (by decide) (by decide) hf hargs
  have he : (fun a : Fin 2 → Bool => f (fun i => a i ^^ (![p, q] : Fin 2 → Bool) i)) =
      fun a => f ![a 0 ^^ p, a 1 ^^ q] := by
    funext a
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [he] at hcomp
  have hout : (fun a => f ![a 0 ^^ p, a 1 ^^ q] ^^ r) ∈ C.operations 2 := by
    cases r
    · simpa only [Bool.xor_false] using hcomp
    · simpa only [Bool.xor_true] using C.comp_not hnot hcomp
  simpa only [hr] using hout

private theorem square_mem (hnot : notOp ∈ C.operations 1)
    (hconst : ∀ b, (fun _ : Fin 1 → Bool => b) ∈ C.operations 1)
    (hxor : Cslib.parity 2 ∈ C.operations 2) (b c d : Bool) :
    (fun a : Fin 2 → Bool => b ^^ (a 0 && c) ^^ (a 1 && d)) ∈ C.operations 2 := by
  have hf := C.const_mem (by decide : 0 < 2) (hconst false)
  have ht := C.const_mem (by decide : 0 < 2) (hconst true)
  have hx := C.projection (0 : Fin 2)
  have hy := C.projection (1 : Fin 2)
  have hnx := C.comp_not hnot hx
  have hny := C.comp_not hnot hy
  have hnxy := C.comp_not hnot hxor
  cases b <;> cases c <;> cases d <;>
    first
    | (convert hf using 1; decide)
    | (convert ht using 1; decide)
    | (convert hx using 1; decide)
    | (convert hy using 1; decide)
    | (convert hnx using 1; decide)
    | (convert hny using 1; decide)
    | (convert hxor using 1; decide)
    | (convert hnxy using 1; decide)

/-- With XOR, NOT and constants, a failure of affinity gives an odd binary truth table,
hence AND. This reduces an arbitrary-arity affine witness directly to its four square values. -/
theorem and_mem_of_xor_of_not_affine (hnot : notOp ∈ C.operations 1)
    (hconst : ∀ b, (fun _ : Fin 1 → Bool => b) ∈ C.operations 1)
    (hxor : Cslib.parity 2 ∈ C.operations 2)
    {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : f ∈ C.operations n)
    (haff : ¬ BitString.IsAffine f) : andOp ∈ C.operations 2 := by
  simp only [BitString.IsAffine, not_forall] at haff
  obtain ⟨x, y, z, hbad⟩ := haff
  let args (i : Fin n) (a : Fin 2 → Bool) : Bool :=
    x i ^^ (a 0 && (x i ^^ y i)) ^^ (a 1 && (x i ^^ z i))
  have hg := C.comp (C.arity_pos hf) (by decide) hf
    (fun i => C.square_mem hnot hconst hxor (x i) (x i ^^ y i) (x i ^^ z i))
  change (fun a => f (fun i => args i a)) ∈ C.operations 2 at hg
  apply C.and_mem_of_odd_binary hnot hg
  have h00 : (fun i => args i ![false, false]) = x := by
    funext i
    cases hx : x i <;> cases hy : y i <;> cases hz : z i <;>
      simp [args, hx, hy, hz]
  have h01 : (fun i => args i ![false, true]) = z := by
    funext i
    cases hx : x i <;> cases hy : y i <;> cases hz : z i <;>
      simp [args, hx, hy, hz]
  have h10 : (fun i => args i ![true, false]) = y := by
    funext i
    cases hx : x i <;> cases hy : y i <;> cases hz : z i <;>
      simp [args, hx, hy, hz]
  have h11 : (fun i => args i ![true, true]) = x + y + z := by
    funext i
    cases hx : x i <;> cases hy : y i <;> cases hz : z i <;>
      simp only [args, Pi.add_apply, hx, hy, hz]
    all_goals decide
  rw [h00, h01, h10, h11]
  cases hx : f x <;> cases hy : f y <;> cases hz : f z <;>
    cases hs : f (x + y + z) <;> simp_all [Bool.add_eq_xor]

/-- The shared Schaefer classification supplies AND, using a non-affine witness to handle
its minority branch. -/
theorem and_mem_of_not_affine (hnot : notOp ∈ C.operations 1)
    (hconst : ∀ b, (fun _ : Fin 1 → Bool => b) ∈ C.operations 1)
    {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : f ∈ C.operations n)
    (haff : ¬ BitString.IsAffine f) : andOp ∈ C.operations 2 := by
  rcases C.classification with hunary | hand | hor | hmaj | hmin
  · obtain ⟨i, u, hu⟩ := hunary n (C.arity_pos hf) f hf
    apply False.elim (haff ?_)
    intro x y z
    simp only [hu, Pi.add_apply]
    exact (show ∀ u : Bool → Bool, BitString.IsAffine u by decide) u (x i) (y i) (z i)
  · exact hand
  · have h := C.comp_not hnot (C.comp_or hor
      (C.comp_not hnot (C.projection (0 : Fin 2)))
      (C.comp_not hnot (C.projection (1 : Fin 2))))
    convert h using 1
    decide
  · have h := C.comp (by decide) (by decide) (g := ![(fun a : Fin 2 → Bool => a 0),
        (fun a => a 1), (fun _ => false)]) hmaj
      (Fin.forall_fin_succ.mpr ⟨C.projection 0,
        Fin.forall_fin_two.mpr ⟨C.projection 1, C.const_mem (by decide) (hconst false)⟩⟩)
    convert h using 1
    decide
  · have hx : Cslib.parity 2 ∈ C.operations 2 := by
      have h := C.comp (by decide) (by decide) (g := ![(fun a : Fin 2 → Bool => a 0),
          (fun a => a 1), (fun _ => false)]) hmin
        (Fin.forall_fin_succ.mpr ⟨C.projection 0,
          Fin.forall_fin_two.mpr ⟨C.projection 1, C.const_mem (by decide) (hconst false)⟩⟩)
      convert h using 1
      decide
    exact C.and_mem_of_xor_of_not_affine hnot hconst hx hf haff

/-- NOT, AND and the unary constants generate every positive-arity Boolean operation.
The construction is disjunctive normal form, with one conjunction per accepted assignment. -/
theorem isComplete_of_not_and (hnot : notOp ∈ C.operations 1)
    (hand : andOp ∈ C.operations 2)
    (hconst : ∀ b, (fun _ : Fin 1 → Bool => b) ∈ C.operations 1) : C.IsComplete := by
  have hor : orOp ∈ C.operations 2 := by
    convert C.comp_not hnot (C.comp_and hand
      (C.comp_not hnot (C.projection (0 : Fin 2)))
      (C.comp_not hnot (C.projection (1 : Fin 2)))) using 1
    decide
  intro n hn f
  classical
  have hpoint (point : Fin n → Bool) :
      (fun a : Fin n → Bool => decide (a = point)) ∈ C.operations n := by
    have step (s : Finset (Fin n)) :
        (fun a : Fin n → Bool => decide (∀ i ∈ s, a i = point i)) ∈ C.operations n := by
      induction s using Finset.induction_on with
      | empty => simpa using C.const_mem hn (hconst true)
      | @insert i s hi ih =>
        have hlit : (fun a : Fin n → Bool => decide (a i = point i)) ∈ C.operations n := by
          cases hb : point i
          · convert C.comp_not hnot (C.projection i) using 1
            funext a; cases a i <;> simp
          · convert C.projection i using 1
            funext a; cases a i <;> simp
        simpa [Finset.mem_insert] using C.comp_and hand hlit ih
    simpa only [Finset.mem_univ, forall_const, ← funext_iff] using step Finset.univ
  have htable (s : Finset (Fin n → Bool)) :
      (fun a => if a ∈ s then f a else false) ∈ C.operations n := by
    induction s using Finset.induction_on with
    | empty => simpa using C.const_mem hn (hconst false)
    | @insert point s hp ih =>
      have hrow : (fun a => if a = point then f point else false) ∈ C.operations n := by
        cases hb : f point
        · simpa only [hb, ite_self] using C.const_mem hn (hconst false)
        · convert hpoint point using 1
          funext a
          by_cases he : a = point <;> simp [he]
      convert C.comp_or hor hrow ih using 1
      funext a
      by_cases he : a = point <;> by_cases hs : a ∈ s <;> simp_all
  simpa using htable Finset.univ

/-- Post's five-class criterion for a positive-arity Boolean clone. -/
theorem isComplete_iff_postCriterion : C.IsComplete ↔ PostCriterion C.operations := by
  constructor
  · intro h
    have hnand := h 2 (by decide) (fun a => !(a 0 && a 1))
    refine ⟨⟨2, by decide, _, hnand, by decide⟩,
      ⟨2, by decide, _, hnand, by decide⟩,
      ⟨2, by decide, _, hnand, by decide⟩,
      ⟨2, by decide, _, hnand, by decide⟩,
      ⟨2, by decide, _, hnand, by decide⟩⟩
  · rintro ⟨hzero, hone, hmono, hself, haff⟩
    have hnot := C.not_mem_of_witnesses hzero hone hmono
    have hc := C.constants_mem_of_not_selfDual hnot hself
    obtain ⟨n, _, f, hf, hnonaff⟩ := haff
    exact C.isComplete_of_not_and hnot (C.and_mem_of_not_affine hnot hc hf hnonaff) hc

private theorem generated_witness (G : (n : ℕ) → Set ((Fin n → Bool) → Bool))
    (h : FunctionallyComplete G) (P : (n : ℕ) → ((Fin n → Bool) → Bool) → Prop)
    (hproj : ∀ n (i : Fin n), P n (fun a => a i))
    (hcomp : ∀ m n, 0 < m → 0 < n → ∀ (f : (Fin m → Bool) → Bool)
      (g : Fin m → (Fin n → Bool) → Bool), P m f → (∀ i, P n (g i)) →
        P n (fun a => f (fun i => g i a)))
    (hnand : ¬ P 2 (fun a => !(a 0 && a 1))) :
    ∃ n, 0 < n ∧ ∃ f ∈ G n, ¬ P n f := by
  by_contra hn
  push Not at hn
  have hgen := h 2 (by decide) (fun a => !(a 0 && a 1))
  apply hnand
  change Generated G (fun a => !(a 0 && a 1)) at hgen
  have hall {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : Generated G f) : P n f := by
    induction hf with
    | of_mem hp hf => exact hn _ hp _ hf
    | projection i => exact hproj _ i
    | comp hm hp f g ihf ihg => exact hcomp _ _ hm hp _ _ ihf ihg
  exact hall hgen

/-- **Post's functional completeness theorem.** An arbitrary family of positive-arity
Boolean operations is complete iff it has a witness outside each of the five closed classes.
There is no finiteness or common-arity assumption on the family. -/
theorem functionallyComplete_iff (G : (n : ℕ) → Set ((Fin n → Bool) → Bool)) :
    FunctionallyComplete G ↔ PostCriterion G := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply generated_witness G h (fun _ f => f (fun _ => false) = false)
      · intro n i; rfl
      · intro m n hm hn f g hf hg
        change f (fun i => g i (fun _ => false)) = false
        rw [show (fun i => g i (fun _ => false)) = (fun _ => false) from funext hg]
        exact hf
      · decide
    · apply generated_witness G h (fun _ f => f (fun _ => true) = true)
      · intro n i; rfl
      · intro m n hm hn f g hf hg
        change f (fun i => g i (fun _ => true)) = true
        rw [show (fun i => g i (fun _ => true)) = (fun _ => true) from funext hg]
        exact hf
      · decide
    · apply generated_witness G h (fun _ f => Monotone f)
      · intro n i a b hab; exact hab i
      · intro m n hm hn f g hf hg a b hab
        exact hf (fun i => hg i hab)
      · decide
    · apply generated_witness G h (fun _ f => ∀ a, f (fun i => !(a i)) = !(f a))
      · intro n i a; rfl
      · intro m n hm hn f g hf hg a
        change f (fun i => g i (fun j => !(a j))) = _
        rw [show (fun i => g i (fun j => !(a j))) = (fun i => !(g i a)) from
          funext (fun i => hg i a)]
        exact hf _
      · decide
    · apply generated_witness G h (fun _ f => BitString.IsAffine f)
      · intro n i a b c; rfl
      · intro m n hm hn f g hf hg
        exact hf.comp (fun a b c => funext (fun i => hg i a b c))
      · decide
  · intro hG
    apply ((generated G).isComplete_iff_postCriterion).mpr
    exact hG.mono (fun _ hn _ hf => Generated.of_mem hn hf)

end Cslib.Logic.BooleanClone
