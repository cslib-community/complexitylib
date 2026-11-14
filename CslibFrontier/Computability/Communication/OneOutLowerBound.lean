/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.OneOutLargeRectangle
public import CslibFrontier.Foundations.Combinatorics.MajorityTree
import CslibFrontier.Probability.Minimax
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-!
# Solving one of many instances is almost as hard as solving one

[ChukhinKulikovMihajlinSmal2026], Theorem 1.2 (printed pp. 1, 9; PDF pp. 2, 10): for a total
relation `R` on finite nonempty sets with `|A|, |B| ≤ 2ⁿ`,
`CC(R) ≤ max {CC(OneOut_k(R)), ⌈log₂ |O|⌉} + O(log k + log n)`, and Theorem 1.1, its
specialization to Boolean functions. Here the constant is explicit:
`ecomplexity_le_oneOut` bounds the additive term by `18 ⌈log₂ k⌉ + 3 ⌈log₂ (n + 1)⌉ + 3`.

The proof follows the source. A `SolvableRectangle R d` is a rectangle together with a protocol
of depth at most `d` solving `R` on it. By Lemma 5.2 (`exists_large_solvable_rectangle`) and the
minimax theorem, some distribution over solvable rectangles covers every input of either player
with probability at least `1/2 + 1/(4k²)` (`exists_covering_distribution`). Valiant's
amplification (`Cslib.exists_forall_majTree_majTree_eq`, the source's Lemma 3.7, over the
majority trees `Cslib.majTree` weighted by that distribution) gives a majority tree of majority
trees of rectangle sides whose majority covers every input. The players walk down the trees as in
the Karchmer–Wigderson game of the monotone majority formula, with three bits per level, to a leaf
rectangle containing both inputs (`walk`, `walk_solves`), where they run its protocol.

Majority gates are walked directly rather than through `Circuits.Formula.monotoneKWProtocol`,
because leaves are rectangles carrying protocols, not formula variables.

## Main definitions

* `Cslib.Communication.OneOut.SolvableRectangle`: a rectangle with a protocol solving `R` on it.
* `Cslib.Communication.OneOut.walk`: the protocol walking a majority tree whose leaves carry
  protocols.

## Main results

* `Cslib.Communication.OneOut.exists_covering_distribution`: the minimax step.
* `Cslib.Communication.OneOut.exists_solves_depth_le`: the amplified protocol for one `p`.
* `Cslib.Communication.OneOut.ecomplexity_le_oneOut`: Theorem 1.2.
* `Cslib.Communication.OneOut.ecomplexityFun_le_oneOut`: the lower bound of Theorem 1.1.
-/

public section

namespace Cslib.Communication.OneOut

open Protocol

variable {X Y Z : Type*} {k : ℕ}

/-- A rectangle `alice × bob` together with a protocol of depth at most `d` solving `R` on it:
the source's solvable rectangles, with the depth bound made explicit. -/
structure SolvableRectangle (R : X → Y → Z → Prop) (d : ℕ) where
  /-- Alice's side of the rectangle. -/
  alice : Set X
  /-- Bob's side of the rectangle. -/
  bob : Set Y
  /-- A protocol solving `R` on the rectangle. -/
  protocol : Protocol X Y Z
  /-- The protocol sends at most `d` bits. -/
  depth_le : protocol.depth ≤ d
  /-- The protocol solves `R` on the rectangle. -/
  solves : protocol.Solves R alice bob

variable {R : X → Y → Z → Prop} {d : ℕ}

/-- A solvable rectangle covers an input of either player when the input lies on its side. -/
@[expose] def SolvableRectangle.Covers (r : SolvableRectangle R d) : X ⊕ Y → Prop :=
  Sum.elim (fun x => x ∈ r.alice) (fun y => y ∈ r.bob)

open scoped Classical in
/-- Against a distribution `π` on the inputs of both players, some solvable rectangle covers an
input drawn from `π` with probability at least `1/2 + 1/(4k²)`: the trivial rectangles if one
player's inputs have that much mass, and otherwise the rectangle of Lemma 5.2 for the conditional
distributions on the two sides. -/
private theorem exists_covers_ge [Finite X] [Finite Y] [Fintype Z] (z₀ : Z)
    (htotal : ∀ x y, ∃ z, R x y z)
    {p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z)}
    (hp : p.Solves (Relation R) Set.univ Set.univ) (π : PMF (X ⊕ Y)) :
    ∃ r : SolvableRectangle R (max p.depth (Nat.clog 2 (Fintype.card Z))),
      1 / 2 + ((k : ℝ) ^ 2)⁻¹ / 4 ≤ (π.toOuterMeasure {z | r.Covers z}).toReal := by
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  set D := max p.depth (Nat.clog 2 (Fintype.card Z))
  set e : ℝ := ((k : ℝ) ^ 2)⁻¹
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [e, hk]
    · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hk))
  set a : X → ℝ := fun x => (π (.inl x)).toReal
  set b : Y → ℝ := fun y => (π (.inr y)).toReal
  have ha0 (x : X) : 0 ≤ a x := ENNReal.toReal_nonneg
  have hb0 (y : Y) : 0 ≤ b y := ENNReal.toReal_nonneg
  set l := ∑ x, a x
  have hsum : l + ∑ y, b y = 1 := by
    rw [← Fintype.sum_sum_type (f := fun z => (π z).toReal)]
    exact Cslib.Probability.PMF.sum_toReal π
  -- The covered mass of a rectangle splits into Alice's and Bob's parts.
  have hcover (r : SolvableRectangle R D) : (π.toOuterMeasure {z | r.Covers z}).toReal =
      (∑ x, if x ∈ r.alice then a x else 0) + ∑ y, if y ∈ r.bob then b y else 0 := by
    rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal, Fintype.sum_sum_type]
    rfl
  obtain ⟨z₀'⟩ : Nonempty Z := ⟨z₀⟩
  by_cases hl : 1 / 2 + e / 4 ≤ l
  · refine ⟨⟨Set.univ, ∅, .output z₀, Nat.zero_le _, fun _ _ _ hy => hy.elim⟩, ?_⟩
    rw [hcover]
    simpa using hl
  by_cases hr : 1 / 2 + e / 4 ≤ 1 - l
  · refine ⟨⟨∅, Set.univ, .output z₀, Nat.zero_le _, fun _ hx _ _ => hx.elim⟩, ?_⟩
    rw [hcover]
    simp only [Set.mem_empty_iff_false, ite_false, Finset.sum_const_zero, Set.mem_univ,
      ite_true, zero_add]
    linarith
  push Not at hl hr
  have hl0 : 0 < l := by linarith
  have hl1 : 0 < 1 - l := by linarith
  -- The conditional distributions of `π` on the two sides.
  have hμsum : ∑ x, ENNReal.ofReal (a x / l) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => div_nonneg (ha0 x) hl0.le, ← Finset.sum_div,
      div_self hl0.ne', ENNReal.ofReal_one]
  have hνsum : ∑ y, ENNReal.ofReal (b y / (1 - l)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => div_nonneg (hb0 y) hl1.le, ← Finset.sum_div,
      show ∑ y, b y = 1 - l by linarith, div_self hl1.ne', ENNReal.ofReal_one]
  set μ := PMF.ofFintype _ hμsum
  set ν := PMF.ofFintype _ hνsum
  obtain ⟨A', B', q, hq, hs, hm⟩ := exists_large_solvable_rectangle μ ν p htotal hp
  refine ⟨⟨A', B', q, hq, hs⟩, ?_⟩
  set SA := ∑ x, if x ∈ A' then a x else 0
  set SB := ∑ y, if y ∈ B' then b y else 0
  have hμA : (μ.toOuterMeasure A').toReal = SA / l := by
    rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal, Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp [μ, ENNReal.toReal_ofReal (div_nonneg (ha0 x) hl0.le)]
  have hνB : (ν.toOuterMeasure B').toReal = SB / (1 - l) := by
    rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal, Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp [ν, ENNReal.toReal_ofReal (div_nonneg (hb0 y) hl1.le)]
  have hSA : SA ≤ l := Finset.sum_le_sum fun x _ => by split_ifs <;> simp [ha0]
  have hSB : SB ≤ 1 - l := by
    rw [show 1 - l = ∑ y, b y by linarith]
    exact Finset.sum_le_sum fun y _ => by split_ifs <;> simp [hb0]
  set u := SA / l
  set w := SB / (1 - l)
  have hu1 : u ≤ 1 := (div_le_one hl0).mpr hSA
  have hw1 : w ≤ 1 := (div_le_one hl1).mpr hSB
  have hu0 : 0 ≤ u := div_nonneg (Finset.sum_nonneg fun x _ => by split_ifs <;> simp [ha0])
    hl0.le
  have hw0 : 0 ≤ w := div_nonneg (Finset.sum_nonneg fun y _ => by split_ifs <;> simp [hb0])
    hl1.le
  have hSAu : SA = l * u := by
    change SA = l * (SA / l)
    field_simp
  have hSBw : SB = (1 - l) * w := by
    change SB = (1 - l) * (SB / (1 - l))
    field_simp
  have hdev : -(e / 4) ≤ (l - 1 / 2) * (u - w) := by
    nlinarith [mul_nonneg (show 0 ≤ e / 4 + (l - 1 / 2) by linarith)
        (show 0 ≤ 1 + (u - w) by linarith),
      mul_nonneg (show 0 ≤ e / 4 - (l - 1 / 2) by linarith) (show 0 ≤ 1 - (u - w) by linarith)]
  rw [hcover]
  change 1 / 2 + e / 4 ≤ SA + SB
  rw [hμA, hνB] at hm
  nlinarith

section Walk

variable {H : Type*} (leaf : H → Protocol X Y Z) (a : X → H → Bool) (b : Y → H → Bool)

/-- The `j`-th of the three subtrees of a majority tree of depth `L + 1`. -/
private def block {L : ℕ} (V : Fin (3 ^ (L + 1)) → H) (j : Fin 3) : Fin (3 ^ L) → H :=
  fun i => V (tripleEquiv L (j, i))

private theorem majTree_succ_comp {L : ℕ} (g : H → Bool) (V : Fin (3 ^ (L + 1)) → H) :
    majTree (L + 1) (g ∘ V) =
      maj3 (majTree L (g ∘ block V 0)) (majTree L (g ∘ block V 1)) (majTree L (g ∘ block V 2)) :=
  rfl

/-- Walk the majority tree `majTree L` over the leaves `V`. Alice's leaf value `a x h` says that
her input is inside leaf `h`, and Bob's leaf value `b y h` that his input is outside it. At a
majority of three subtrees, Alice holds at least two subtrees whose majority contains her input,
and Bob at most one whose majority excludes his input. Alice says whether her two are the first
two and, if not, whether the first is one of them; Bob then names one of her two candidates that he
does not exclude. At a leaf the players run its protocol. -/
def walk : (L : ℕ) → (Fin (3 ^ L) → H) → Protocol X Y Z
  | 0, V => leaf (V ⟨0, by simp⟩)
  | L + 1, V =>
    .alice (fun x => majTree L (a x ∘ block V 0) && majTree L (a x ∘ block V 1))
      (.alice (fun x => majTree L (a x ∘ block V 0))
        (.bob (fun y => majTree L (b y ∘ block V 1)) (walk L (block V 1)) (walk L (block V 2)))
        (.bob (fun y => majTree L (b y ∘ block V 0)) (walk L (block V 0)) (walk L (block V 2))))
      (.bob (fun y => majTree L (b y ∘ block V 0)) (walk L (block V 0)) (walk L (block V 1)))

/-- The walk sends three bits per level, then runs a leaf protocol. -/
theorem depth_walk_le {d : ℕ} (hleaf : ∀ h, (leaf h).depth ≤ d) :
    ∀ (L : ℕ) (V : Fin (3 ^ L) → H), (walk leaf a b L V).depth ≤ 3 * L + d
  | 0, V => by simpa [walk] using hleaf _
  | L + 1, V => by
    have h0 := depth_walk_le hleaf L (block V 0)
    have h1 := depth_walk_le hleaf L (block V 1)
    have h2 := depth_walk_le hleaf L (block V 2)
    simp only [walk, depth_alice, depth_bob]
    omega

/-- If the majority of Alice's leaf values is `true` and the majority of Bob's is `false`, and
every leaf protocol solves `R` where both leaf values say so, then the walk solves `R`. -/
theorem walk_solves {R : X → Y → Z → Prop}
    (hleaf : ∀ h x y, a x h = true → b y h = false → R x y ((leaf h).run x y)) :
    ∀ (L : ℕ) (V : Fin (3 ^ L) → H) (x : X) (y : Y), majTree L (a x ∘ V) = true →
      majTree L (b y ∘ V) = false → R x y ((walk leaf a b L V).run x y)
  | 0, V, x, y, hx, hy => hleaf _ x y hx hy
  | L + 1, V, x, y, hx, hy => by
    have ih (j : Fin 3) := walk_solves hleaf L (block V j) x y
    rw [majTree_succ_comp] at hx hy
    cases hea : majTree L (a x ∘ block V 0) <;> cases heb : majTree L (a x ∘ block V 1) <;>
      cases hec : majTree L (a x ∘ block V 2) <;> cases hfa : majTree L (b y ∘ block V 0) <;>
      cases hfb : majTree L (b y ∘ block V 1) <;> cases hfc : majTree L (b y ∘ block V 2) <;>
      simp only [hea, heb, hec, hfa, hfb, hfc] at hx hy <;>
      first
        | exact absurd hx (by decide)
        | exact absurd hy (by decide)
        | (simp only [walk, run_alice, run_bob, hea, heb, hfa, hfb, Bool.and_true, Bool.and_false,
            Bool.cond_true, Bool.cond_false]
           first | exact ih 0 hea hfa | exact ih 1 heb hfb | exact ih 2 hec hfc)

end Walk

open scoped Classical in
/-- **The minimax step** of the proof of Theorem 1.2. Some distribution over solvable
rectangles of depth `max p.depth ⌈log₂ |Z|⌉` covers every input of Alice and every input of Bob
with probability at least `1/2 + 1/(4k²)`. -/
theorem exists_covering_distribution [Finite X] [Finite Y] [Fintype Z] [Nonempty Z]
    (htotal : ∀ x y, ∃ z, R x y z)
    {p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z)}
    (hp : p.Solves (Relation R) Set.univ Set.univ) :
    ∃ Λ : PMF (SolvableRectangle R (max p.depth (Nat.clog 2 (Fintype.card Z)))),
      (∀ x, 1 / 2 + ((k : ℝ) ^ 2)⁻¹ / 4 ≤ (Λ.toOuterMeasure {r | x ∈ r.alice}).toReal) ∧
      ∀ y, 1 / 2 + ((k : ℝ) ^ 2)⁻¹ / 4 ≤ (Λ.toOuterMeasure {r | y ∈ r.bob}).toReal := by
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  set D := max p.depth (Nat.clog 2 (Fintype.card Z))
  set δ : ℝ := 1 / 2 + ((k : ℝ) ^ 2)⁻¹ / 4
  obtain ⟨z₀⟩ := ‹Nonempty Z›
  have : Nonempty (SolvableRectangle R D) :=
    ⟨⟨Set.univ, ∅, .output z₀, Nat.zero_le _, fun _ _ _ hy => hy.elim⟩⟩
  obtain ⟨Λ, -, hΛ⟩ := Cslib.Probability.PMF.exists_forall_toOuterMeasure_le
    (fun (r : SolvableRectangle R D) z => ¬ r.Covers z) (ε := 1 - δ) fun π => by
      obtain ⟨r, hr⟩ := exists_covers_ge z₀ htotal hp π
      refine ⟨r, ?_⟩
      have hc := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl π {z | r.Covers z}
      simp only [Set.compl_ofPred] at hc
      linarith [show δ = 1 / 2 + ((k : ℝ) ^ 2)⁻¹ / 4 from rfl]
  have hcov (z : X ⊕ Y) : δ ≤ (Λ.toOuterMeasure {r | r.Covers z}).toReal := by
    have hc := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl Λ {r | r.Covers z}
    have := hΛ z
    simp only [Set.compl_ofPred] at hc
    linarith
  exact ⟨Λ, fun x => hcov (.inl x), fun y => hcov (.inr y)⟩

/-- The number of amplification levels used for arity `k` and `N = |X| + |Y|` inputs:
`3 ⌈log₂ k²⌉ + 1` inner levels push the error below `1/6`, and `⌈log₂ ⌈log₂ N⌉⌉` outer levels
correct all `N` inputs at once. -/
@[expose] def levels (k N : ℕ) : ℕ := 3 * Nat.clog 2 (k ^ 2) + 1 + Nat.clog 2 (Nat.clog 2 N)

/-- `(11/8)^(3 ⌈log₂ k²⌉)` is at least `k²`. -/
private theorem sq_le_eleven_eighths_pow (k : ℕ) :
    ((k : ℝ) ^ 2) ≤ (11 / 8) ^ (3 * Nat.clog 2 (k ^ 2)) := by
  have h2 : ((k : ℝ) ^ 2) ≤ 2 ^ Nat.clog 2 (k ^ 2) := by
    exact_mod_cast Nat.le_pow_clog one_lt_two (k ^ 2)
  refine h2.trans ?_
  rw [pow_mul]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) _

open scoped Classical in
/-- **The amplified protocol** (proof of [ChukhinKulikovMihajlinSmal2026], Theorem 1.2, printed
pp. 11–12; PDF pp. 12–13). If `p` solves the one-out-of-`k` problem for a total relation `R` on
finite nonempty types, some protocol of depth at most `max p.depth ⌈log₂ |Z|⌉ + 3 · levels k N`,
with `N = |X| + |Y|`, solves `R` on all inputs. The leaves are the finitely many sides of solvable
rectangles, weighted by the covering distribution; `exists_forall_majTree_majTree_eq` amplifies
it, and the players walk the two nested majority trees. -/
theorem exists_solves_depth_le [Fintype X] [Fintype Y] [Fintype Z] [Nonempty X] [Nonempty Y]
    (htotal : ∀ x y, ∃ z, R x y z)
    {p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z)}
    (hp : p.Solves (Relation R) Set.univ Set.univ) :
    ∃ q : Protocol X Y Z, q.Solves R Set.univ Set.univ ∧
      q.depth ≤ max p.depth (Nat.clog 2 (Fintype.card Z)) +
        3 * levels k (Fintype.card X + Fintype.card Y) := by
  have hk : 0 < k := (p.leafOutput ⟨0, p.leafCount_pos⟩).index.pos
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have : Nonempty Z := ⟨(htotal x₀ y₀).choose⟩
  set D := max p.depth (Nat.clog 2 (Fintype.card Z))
  obtain ⟨Λ, hA, hB⟩ := exists_covering_distribution htotal hp
  -- Leaves: the finitely many sides of solvable rectangles, each with a chosen protocol.
  let sides : SolvableRectangle R D → Set X × Set Y := fun r => (r.alice, r.bob)
  let I := Set.range sides
  have : Fintype I := Fintype.ofFinite I
  let rep : I → SolvableRectangle R D := fun i => i.2.choose
  have hrep (i : I) : sides (rep i) = i.1 := i.2.choose_spec
  let Λ' : PMF I := Λ.map fun r => ⟨sides r, r, rfl⟩
  let w : I → ℝ := fun i => (Λ' i).toReal
  -- The weight of the leaves outside `{i | P (sides i)}` is one minus the covered mass.
  have hmiss (P : Set X × Set Y → Prop) [DecidablePred P] :
      ∑ i with ¬ P i.1, w i = 1 - (Λ.toOuterMeasure {r | P (sides r)}).toReal := by
    have hc := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl Λ' {i | P i.1}
    rw [PMF.toOuterMeasure_map_apply] at hc
    have hsum : (Λ'.toOuterMeasure {i | P i.1}ᶜ).toReal = ∑ i with ¬ P i.1, w i := by
      rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal, Finset.sum_filter]
      exact Finset.sum_congr rfl fun i _ => by unfold w; split_ifs <;> simp_all
    rw [← hsum]
    exact eq_sub_of_add_eq' hc
  let a : X → I → Bool := fun x i => decide (x ∈ i.1.1)
  let b : Y → I → Bool := fun y i => decide (y ∉ i.1.2)
  let val : X ⊕ Y → I → Bool := Sum.elim a b
  let f : X ⊕ Y → Bool := Sum.elim (fun _ => true) (fun _ => false)
  set m₁ := 3 * Nat.clog 2 (k ^ 2)
  set m₂ := Nat.clog 2 (Nat.clog 2 (Fintype.card (X ⊕ Y)))
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  obtain ⟨V, hV⟩ := exists_forall_majTree_majTree_eq (w := w) (fun _ => ENNReal.toReal_nonneg)
    (Cslib.Probability.PMF.sum_toReal Λ') Finset.univ val f (ε := ((k : ℝ) ^ 2)⁻¹ / 4)
    (by positivity)
    (fun z _ => by
      rcases z with x | y
      · simp only [val, f, a, Sum.elim_inl, ne_eq, decide_eq_true_eq]
        rw [hmiss (fun s => x ∈ s.1)]
        linarith [hA x]
      · simp only [val, f, b, Sum.elim_inr, ne_eq, Bool.not_eq_false, decide_eq_true_eq]
        rw [hmiss (fun s => y ∈ s.2)]
        linarith [hB y])
    (m₁ := m₁) (m₂ := m₂)
    (by
      have := sq_le_eleven_eighths_pow k
      have hpos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
      calc (1 / 4 : ℝ) = (k : ℝ) ^ 2 * ((k : ℝ) ^ 2)⁻¹ / 4 := by field_simp
        _ ≤ (11 / 8) ^ m₁ * (((k : ℝ) ^ 2)⁻¹ / 4) := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_right this (by positivity))
    (by
      rw [Finset.card_univ]
      calc Fintype.card (X ⊕ Y) ≤ 2 ^ Nat.clog 2 (Fintype.card (X ⊕ Y)) :=
            Nat.le_pow_clog one_lt_two _
        _ ≤ 2 ^ 2 ^ m₂ := Nat.pow_le_pow_right two_pos (Nat.le_pow_clog one_lt_two _))
  have hleaf (i : I) (x : X) (y : Y) (hx : a x i = true) (hy : b y i = false) :
      R x y ((rep i).protocol.run x y) := by
    simp only [a, b, decide_eq_true_eq, decide_eq_false_iff_not, not_not] at hx hy
    have h := hrep i
    exact (rep i).solves x (by rw [show (rep i).alice = i.1.1 from congrArg Prod.fst h]; exact hx)
      y (by rw [show (rep i).bob = i.1.2 from congrArg Prod.snd h]; exact hy)
  let inner : (Fin (3 ^ (m₁ + 1)) → I) → Protocol X Y Z := walk (fun i => (rep i).protocol) a b
    (m₁ + 1)
  refine ⟨walk inner (fun x U => majTree (m₁ + 1) (a x ∘ U))
    (fun y U => majTree (m₁ + 1) (b y ∘ U)) m₂ V, fun x _ y _ => walk_solves _ _ _
      (fun U x y hx hy => walk_solves _ _ _ hleaf _ U x y hx hy)
      m₂ V x y (hV (.inl x) (Finset.mem_univ _)) (hV (.inr y) (Finset.mem_univ _)), ?_⟩
  have hdepth := depth_walk_le inner (fun x U => majTree (m₁ + 1) (a x ∘ U))
    (fun y U => majTree (m₁ + 1) (b y ∘ U))
    (fun U => depth_walk_le _ a b (fun i => (rep i).depth_le) (m₁ + 1) U) m₂ V
  have hm₂ : m₂ = Nat.clog 2 (Nat.clog 2 (Fintype.card X + Fintype.card Y)) := by
    simp only [m₂, Fintype.card_sum]
  unfold levels
  omega

/-- The additive term of Theorem 1.2 in terms of `k` and an `n` with `|X|, |Y| ≤ 2ⁿ`. -/
private theorem three_mul_levels_le {N n : ℕ} (hN : N ≤ 2 ^ (n + 1)) (k : ℕ) :
    3 * levels k N ≤ 18 * Nat.clog 2 k + 3 * Nat.clog 2 (n + 1) + 3 := by
  have hk : Nat.clog 2 (k ^ 2) ≤ 2 * Nat.clog 2 k := by
    refine Nat.clog_le_of_le_pow ?_
    rw [pow_mul, sq]
    have := Nat.le_pow_clog one_lt_two k
    rw [show (2 : ℕ) ^ 2 = 4 from rfl] at *
    calc k * k ≤ 2 ^ Nat.clog 2 k * 2 ^ Nat.clog 2 k := Nat.mul_le_mul this this
      _ = 4 ^ Nat.clog 2 k := by rw [← mul_pow]; norm_num
  have hN' : Nat.clog 2 (Nat.clog 2 N) ≤ Nat.clog 2 (n + 1) :=
    Nat.clog_mono_right 2 (Nat.clog_le_of_le_pow hN)
  unfold levels
  omega

/-- **[ChukhinKulikovMihajlinSmal2026], Theorem 1.2.** Let `R` be a total relation on finite
nonempty types with `|X|, |Y| ≤ 2ⁿ`. Then
`CC(R) ≤ max {CC(OneOut_k(R)), ⌈log₂ |Z|⌉} + 18 ⌈log₂ k⌉ + 3 ⌈log₂ (n + 1)⌉ + 3`,
which is the source's `O(log k + log n)` with explicit constants. The source's hypothesis
`1 ≤ k ≤ min {|A|, |B|}` is not needed. For `k = 0` there are no answers, so
`CC(OneOut_k(R)) = ⊤`. For `k > min {|X|, |Y|}` there are no `k` distinct inputs on one side, so
`CC(OneOut_k(R)) = 0`; the bound still holds because the heavy-atom case of Lemma 5.2 covers that
side's inputs. -/
theorem ecomplexity_le_oneOut [Fintype X] [Fintype Y] [Fintype Z] [Nonempty X] [Nonempty Y]
    (htotal : ∀ x y, ∃ z, R x y z) {n : ℕ} (hX : Fintype.card X ≤ 2 ^ n)
    (hY : Fintype.card Y ≤ 2 ^ n) :
    ecomplexity R Set.univ Set.univ ≤
      max (ecomplexity (Relation (k := k) R) Set.univ Set.univ) (Nat.clog 2 (Fintype.card Z)) +
        (18 * Nat.clog 2 k + 3 * Nat.clog 2 (n + 1) + 3 : ℕ) := by
  by_cases h : ∃ p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z),
      p.Solves (Relation R) Set.univ Set.univ
  · obtain ⟨p, hp, hpd⟩ := exists_solves_depth_eq_ecomplexity h
    obtain ⟨q, hq, hqd⟩ := exists_solves_depth_le htotal hp
    have hl := three_mul_levels_le (N := Fintype.card X + Fintype.card Y) (n := n)
      (by rw [pow_succ]; omega) k
    rw [← hpd]
    refine (ecomplexity_le_depth hq).trans ?_
    have : q.depth ≤ max p.depth (Nat.clog 2 (Fintype.card Z)) +
        (18 * Nat.clog 2 k + 3 * Nat.clog 2 (n + 1) + 3) := by omega
    have hcast : (q.depth : ℕ∞) ≤ ((max p.depth (Nat.clog 2 (Fintype.card Z)) +
        (18 * Nat.clog 2 k + 3 * Nat.clog 2 (n + 1) + 3) : ℕ) : ℕ∞) := Nat.cast_le.mpr this
    have hmax : ((max p.depth (Nat.clog 2 (Fintype.card Z)) : ℕ) : ℕ∞) =
        max (p.depth : ℕ∞) (Nat.clog 2 (Fintype.card Z) : ℕ) :=
      (Monotone.map_max (fun _ _ h => Nat.cast_le.mpr h))
    rw [Nat.cast_add, hmax] at hcast
    exact hcast
  · rw [← ecomplexity_ne_top_iff, not_not] at h
    simp [h]

/-- **[ChukhinKulikovMihajlinSmal2026], Theorem 1.1, lower bound.** For a Boolean function `F` on
finite nonempty types with `|X|, |Y| ≤ 2ⁿ`,
`CC(F) ≤ CC(OneOut_k(F)) + 18 ⌈log₂ k⌉ + 3 ⌈log₂ (n + 1)⌉ + 4`. The upper bound
`CC(OneOut_k(F)) ≤ CC(F)` is `OneOut.ecomplexity_le`. -/
theorem ecomplexityFun_le_oneOut [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (F : X → Y → Bool) {n : ℕ} (hX : Fintype.card X ≤ 2 ^ n) (hY : Fintype.card Y ≤ 2 ^ n) :
    ecomplexityFun F ≤ ecomplexity (Relation (k := k) fun x y z => F x y = z) Set.univ Set.univ +
      (18 * Nat.clog 2 k + 3 * Nat.clog 2 (n + 1) + 4 : ℕ) := by
  have h := ecomplexity_le_oneOut (k := k) (R := fun x y z => F x y = z)
    (fun x y => ⟨_, rfl⟩) hX hY
  rw [Fintype.card_bool, show Nat.clog 2 2 = 1 by simpa using Nat.clog_pow 2 1 one_lt_two] at h
  refine h.trans ?_
  set E := ecomplexity (Relation (k := k) fun x y z => F x y = z) Set.univ Set.univ
  have hmax : max E ((1 : ℕ) : ℕ∞) ≤ E + 1 :=
    max_le le_self_add (by simp)
  calc max E ((1 : ℕ) : ℕ∞) + ((18 * Nat.clog 2 k + 3 * Nat.clog 2 (n + 1) + 3 : ℕ) : ℕ∞)
      ≤ E + 1 + ((18 * Nat.clog 2 k + 3 * Nat.clog 2 (n + 1) + 3 : ℕ) : ℕ∞) := by gcongr
    _ = E + ((18 * Nat.clog 2 k + 3 * Nat.clog 2 (n + 1) + 4 : ℕ) : ℕ∞) := by
      rw [add_assoc]; congr 1; push_cast; ring

end Cslib.Communication.OneOut
