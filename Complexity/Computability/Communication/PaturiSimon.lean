/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.SignRank
public import Complexity.Computability.Communication.UnboundedError
import Complexity.Foundations.Data.BitString.Basic

/-!
# The Paturi–Simon theorem

The unbounded-error communication complexity of a Boolean function `f` on finite sets is
determined, up to an additive constant, by the sign-rank of `f`
[Paturi and Simon][PaturiSimon1986]: in the form of
[Sherstov and Wu, Theorem 2.16][SherstovWu2019], `log rk±(f) ≤ UPP(f) ≤ log rk±(f) + 2`. Here
`⌈log₂ (signRank f)⌉ ≤ uppComplexityFun f ≤ ⌊log₂ (signRank f)⌋ + 2`
(`PrivateCoin.clog_signRank_le_uppComplexityFun_le`).

*Lower bound.* For a private-coin protocol, the number of random strings `(s, t)` on which it
reaches a leaf factors as a product of a count depending on Alice's input and one depending on
Bob's. Hence the signed vote `∑ s, ∑ t, ±1` of the protocol is a matrix of rank at most the number
of leaves (`Protocol.rank_sum_comp_run_le`), and when the error is less than `1 / 2` it
sign-represents `f` (`PrivateCoin.errorProb_lt_half_iff`). So a protocol of depth `d` has
`signRank f ≤ 2 ^ d` (`PrivateCoin.signRank_le_leafCount`,
`PrivateCoin.clog_signRank_le_uppComplexityFun`). The lower bound needs only Bob's inputs to be
finite.

*Upper bound.* Take an integer sign-representation `U * V` through `r = signRank f` dimensions
(`exists_int_mul_signRepresents`). Alice draws an index from `Option (Fin r)` with dyadic
probabilities affine in her row of `U`, and sends it in `⌈log₂ (r + 1)⌉` bits; Bob answers `true`
with a dyadic probability affine in his column of `V`. The bias of the answer is a positive multiple
of `(U * V) x y`, so it has the right sign (`PrivateCoin.exists_solvesUnbounded_depth_le`,
`PrivateCoin.uppComplexityFun_le_log_signRank_add_two`). All probabilities are dyadic, so finitely
many private random bits suffice; the lower bound holds for any finite number of them.

As a consequence equality on a finite set `X`, which needs `⌈log₂ |X|⌉ + 1` bits deterministically
when `|X| ≥ 2` (`ecomplexityFun_equality`), needs at most three with unbounded error
(`PrivateCoin.uppComplexityFun_equality_le_three`).

The cost model is that of `PrivateCoin`: the depth of the protocol tree, with the output at the
leaves known to both players and private random strings of finite, unbounded length. Sherstov and
Wu allow unlimited private random bits; the bounds proved here are stated for protocols with
finitely many.

## Main results

* `Cslib.Communication.Protocol.rank_sum_comp_run_le`: the rank bound for averaged protocols.
* `Cslib.Communication.PrivateCoin.errorProb_lt_half_iff`: unbounded-error correctness as a sign
  condition on the signed vote.
* `Cslib.Communication.PrivateCoin.signRank_le_leafCount`,
  `Cslib.Communication.PrivateCoin.clog_signRank_le_uppComplexityFun`: the lower bound.
* `Cslib.Communication.PrivateCoin.exists_solvesUnbounded_depth_le`,
  `Cslib.Communication.PrivateCoin.uppComplexityFun_le_log_signRank_add_two`: the upper bound.
* `Cslib.Communication.PrivateCoin.clog_signRank_le_uppComplexityFun_le`: the Paturi–Simon theorem.
* `Cslib.Communication.PrivateCoin.uppComplexityFun_equality_le_three`: equality costs at most
  three bits with unbounded error.

## References

* [R. Paturi and J. Simon, *Probabilistic communication complexity*][PaturiSimon1986]
* [A. A. Sherstov and P. Wu, *Near-optimal lower bounds on the threshold degree and sign-rank of
  AC⁰*][SherstovWu2019]
-/

open Finset Matrix

public section

namespace Cslib.Communication

variable {X Y X' Y' Z : Type*}

namespace Protocol

/-- **The rank bound for averaged protocols.** For a protocol `p`, finite sets `S` and `T` of
random choices, maps `α` and `β` into Alice's and Bob's inputs and a relabelling `g` of the
outputs, the matrix with entry `∑ s, ∑ t, g (p.run (α x s) (β y t))` at `x` and `y` has rank at
most the number of leaves of `p`: on each leaf rectangle the sum factors as the number of `s` with
`α x s` on Alice's side times the number of `t` with `β y t` on Bob's side. -/
theorem rank_sum_comp_run_le {S T : Type*} [Fintype S] [Fintype T] [Fintype Y]
    (p : Protocol X' Y' Z) (α : X → S → X') (β : Y → T → Y') (g : Z → ℝ) :
    (Matrix.of fun x y => ∑ s, ∑ t, g (p.run (α x s) (β y t))).rank ≤ p.leafCount := by
  classical
  let U : Matrix X (Fin p.leafCount) ℝ := Matrix.of fun x i => #{s | α x s ∈ p.leafAlice i}
  let V : Matrix (Fin p.leafCount) Y ℝ :=
    Matrix.of fun i y => #{t | β y t ∈ p.leafBob i} * g (p.leafOutput i)
  have hUV : (Matrix.of fun x y => ∑ s, ∑ t, g (p.run (α x s) (β y t))) = U * V := by
    ext x y
    have key : ∀ s t, g (p.run (α x s) (β y t)) = ∑ i, (if α x s ∈ p.leafAlice i then (1 : ℝ)
        else 0) * ((if β y t ∈ p.leafBob i then 1 else 0) * g (p.leafOutput i)) := by
      intro s t
      simp only [ite_mul, one_mul, zero_mul, ← ite_and, ← leaf_eq_iff, sum_ite_eq, mem_univ,
        ite_true]
      rw [run_eq_leafOutput_leaf]
    simp only [Matrix.of_apply, Matrix.mul_apply, U, V, key, natCast_card_filter, sum_mul,
      mul_sum]
    exact ((sum_congr rfl fun s _ => sum_comm).trans sum_comm).trans
      (sum_congr rfl fun i _ => sum_comm)
  rw [hUV]
  exact (rank_mul_le_left U V).trans ((rank_le_card_width U).trans_eq (Fintype.card_fin _))

end Protocol

private theorem exists_le_two_pow (K : ℤ) : ∃ α : ℕ, K ≤ 2 ^ α :=
  ⟨K.toNat, (Int.self_le_toNat K).trans (by exact_mod_cast (Nat.lt_two_pow_self).le)⟩

/-- **Weights from an integer factorization.** From integer matrices `U` and `V` through `r`
dimensions, build weights `w x j ≥ 0` summing to `2 ^ α` over `j : Option (Fin r)` and thresholds
`0 ≤ c y j ≤ 2 ^ β` with `∑ j, w x j * (2 ^ β - 2 * c y j) = 2 ^ (α + 1) * (U * V) x y`. With `T`
and `Q` bounding the entries of `U` and `V`, take `w x (some i) = U x i + T`, put the remaining
weight on `none`, and let `c y j` be `2 ^ L + T * ∑ i, V i y`, minus `2 ^ α * V i y` when
`j = some i`. -/
private theorem exists_int_weights [Finite X] [Finite Y] {r : ℕ} (U : Matrix X (Fin r) ℤ)
    (V : Matrix (Fin r) Y ℤ) :
    ∃ (α β : ℕ) (w : X → Option (Fin r) → ℤ) (c : Y → Option (Fin r) → ℤ),
      (∀ x j, 0 ≤ w x j) ∧ (∀ x, ∑ j, w x j = 2 ^ α) ∧ (∀ y j, 0 ≤ c y j ∧ c y j ≤ 2 ^ β) ∧
      ∀ x y, ∑ j, w x j * (2 ^ β - 2 * c y j) = 2 ^ (α + 1) * (U * V) x y := by
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  set T : ℤ := ∑ x, ∑ i, |U x i| with hT
  set Q : ℤ := ∑ i, ∑ y, |V i y| with hQ
  have hT0 : 0 ≤ T := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  have hUT : ∀ x i, |U x i| ≤ T := fun x i =>
    (single_le_sum (f := fun i => |U x i|) (fun _ _ => abs_nonneg _) (mem_univ i)).trans
      (single_le_sum (f := fun x => ∑ i, |U x i|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ x))
  have hVQ : ∀ i y, |V i y| ≤ Q := fun i y =>
    (single_le_sum (f := fun y => |V i y|) (fun _ _ => abs_nonneg _) (mem_univ y)).trans
      (single_le_sum (f := fun i => ∑ y, |V i y|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ i))
  have hSQ : ∀ y, |∑ i, V i y| ≤ Q := fun y =>
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ =>
      single_le_sum (f := fun y => |V i y|) (fun _ _ => abs_nonneg _) (mem_univ y))
  have hQ0 : 0 ≤ Q := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨α, hα⟩ := exists_le_two_pow (2 * r * T)
  obtain ⟨L, hL⟩ := exists_le_two_pow (T * Q + 2 ^ α * Q)
  let S : Y → ℤ := fun y => ∑ i, V i y
  refine ⟨α, L + 1,
    fun x j => Option.elim j (2 ^ α - ∑ i, (U x i + T)) fun i => U x i + T,
    fun y j => Option.elim j (2 ^ L + T * S y) fun i => 2 ^ L + T * S y - 2 ^ α * V i y,
    ?_, ?_, ?_, ?_⟩
  · intro x j
    cases j with
    | none =>
      have : ∑ i, (U x i + T) ≤ ∑ _i : Fin r, 2 * T := sum_le_sum fun i _ => by
        linarith [(abs_le.mp (hUT x i)).2]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      simp only [Option.elim]
      linarith
    | some i =>
      simp only [Option.elim]
      linarith [(abs_le.mp (hUT x i)).1]
  · intro x
    rw [Fintype.sum_option]
    simp only [Option.elim]
    ring
  · intro y j
    have h1 := abs_le.mp (hSQ y)
    have h2 : -(T * Q) ≤ T * S y ∧ T * S y ≤ T * Q :=
      ⟨by nlinarith [h1.1], mul_le_mul_of_nonneg_left h1.2 hT0⟩
    have hα0 : (0 : ℤ) ≤ 2 ^ α := by positivity
    rw [pow_succ]
    cases j with
    | none =>
      simp only [Option.elim]
      constructor <;> nlinarith
    | some i =>
      have h3 := abs_le.mp (hVQ i y)
      have h4 : -(2 ^ α * Q) ≤ 2 ^ α * V i y ∧ 2 ^ α * V i y ≤ 2 ^ α * Q :=
        ⟨by nlinarith [h3.1], mul_le_mul_of_nonneg_left h3.2 hα0⟩
      simp only [Option.elim]
      constructor <;> nlinarith
  · intro x y
    rw [Fintype.sum_option]
    simp only [Option.elim]
    have e1 : ∀ i, (U x i + T) * (2 ^ (L + 1) - 2 * (2 ^ L + T * S y - 2 ^ α * V i y)) =
        (U x i + T) * -(2 * T * S y) +
          (2 ^ (α + 1) * (U x i * V i y) + 2 ^ (α + 1) * T * V i y) := fun i => by ring
    simp only [e1, sum_add_distrib, ← sum_mul, ← mul_sum, Matrix.mul_apply]
    simp only [S]
    ring

namespace PrivateCoin

variable {a b : ℕ}

/-- **The bias identity.** For a private-coin protocol computing a Boolean value, the number of
random strings on which it answers `false`, minus the number on which it answers `true`, multiplied
by the sign of `f x y`, is `2 ^ a * 2 ^ b * (1 - 2 * errorProb)`. -/
theorem signMatrix_mul_sum (P : PrivateCoin a b X Y Bool) (f : X → Y → Bool) (x : X) (y : Y) :
    signMatrix ℝ f x y * ∑ s, ∑ t, BitString.signVal (P.run (x, s) (y, t)) =
      2 ^ a * 2 ^ b * (1 - 2 * P.errorProb (fun x y z => f x y = z) x y) := by
  have h : ∀ s t, signMatrix ℝ f x y * BitString.signVal (P.run (x, s) (y, t)) =
      1 - 2 * (if ¬f x y = P.run (x, s) (y, t) then 1 else 0) := by
    intro s t
    rw [signMatrix_apply_eq_signVal, BitString.signVal_mul_signVal]
    split_ifs <;> norm_num
  rw [errorProb_eq_card, mul_sum]
  simp only [mul_sum, h]
  rw [← Fintype.sum_prod_type' (f := fun s t => 1 - 2 * (if ¬f x y = P.run (x, s) (y, t) then
    (1 : ℝ) else 0)), sum_sub_distrib, ← mul_sum, sum_boole, sum_const, card_univ,
    Fintype.card_prod, BitString.card, BitString.card, nsmul_eq_mul, mul_one]
  have : (0 : ℝ) < 2 ^ a * 2 ^ b := by positivity
  push_cast
  field_simp

/-- A private-coin protocol for `f` has error less than `1 / 2` on `x` and `y` exactly when its
signed vote `∑ s, ∑ t, ±1` has the sign of `signMatrix ℝ f x y`. -/
theorem errorProb_lt_half_iff (P : PrivateCoin a b X Y Bool) (f : X → Y → Bool) (x : X) (y : Y) :
    P.errorProb (fun x y z => f x y = z) x y < 1 / 2 ↔
      0 < signMatrix ℝ f x y * ∑ s, ∑ t, BitString.signVal (P.run (x, s) (y, t)) := by
  rw [signMatrix_mul_sum]
  have : (0 : ℝ) < 2 ^ a * 2 ^ b := by positivity
  rw [mul_pos_iff_of_pos_left this]
  constructor <;> intro h <;> linarith

/-- **Paturi–Simon, lower bound (leaf form).** A private-coin protocol computing `f` with
unbounded error has at least `signRank f` leaves: the signed votes form a matrix that
sign-represents `f` and has rank at most the number of leaves (`Protocol.rank_sum_comp_run_le`). -/
theorem signRank_le_leafCount [Fintype Y] {f : X → Y → Bool} (P : PrivateCoin a b X Y Bool)
    (hP : P.SolvesUnbounded (fun x y z => f x y = z) Set.univ Set.univ) :
    signRank f ≤ P.leafCount := by
  refine (signRank_le_rank (A := Matrix.of fun x y => ∑ s, ∑ t,
    BitString.signVal (P.run (x, s) (y, t))) fun x y => ?_).trans
    (Protocol.rank_sum_comp_run_le (X := X) (Y := Y) (p := P) (fun x s => (x, s))
      (fun y t => (y, t)) BitString.signVal)
  exact (errorProb_lt_half_iff P f x y).mp (hP x trivial y trivial)

/-- A private-coin protocol computing `f` with unbounded error sends at least
`⌈log₂ (signRank f)⌉` bits. -/
theorem clog_signRank_le_depth [Fintype Y] {f : X → Y → Bool} (P : PrivateCoin a b X Y Bool)
    (hP : P.SolvesUnbounded (fun x y z => f x y = z) Set.univ Set.univ) :
    Nat.clog 2 (signRank f) ≤ P.depth :=
  Nat.clog_le_of_le_pow
    ((signRank_le_leafCount P hP).trans (Protocol.leafCount_le_two_pow_depth P))

/-- **Paturi–Simon, lower bound**: the unbounded-error complexity of `f` is at least
`⌈log₂ (signRank f)⌉` [Sherstov and Wu, Theorem 2.16][SherstovWu2019]. -/
theorem clog_signRank_le_uppComplexityFun [Fintype Y] (f : X → Y → Bool) :
    (Nat.clog 2 (signRank f) : ℕ∞) ≤ uppComplexityFun f :=
  le_uppComplexityFun_iff.mpr fun _ _ P hP => by exact_mod_cast clog_signRank_le_depth P hP

/-! ### Upper bound -/

/-- **Sampling with dyadic weights.** Weights `w` summing to `2 ^ α` are realized by a map from
`α` random bits: each `i` has exactly `w i` preimages. -/
private theorem exists_sampler {ι : Type*} [Fintype ι] {α : ℕ} (w : ι → ℕ)
    (hw : ∑ i, w i = 2 ^ α) :
    ∃ σ : BitString α → ι, ∀ F : ι → ℝ, ∑ s, F (σ s) = ∑ i, (w i : ℝ) * F i := by
  have hcard : Fintype.card (BitString α) = Fintype.card (Σ i, Fin (w i)) := by
    rw [BitString.card, Fintype.card_sigma]
    simp only [Fintype.card_fin, hw]
  let e := Fintype.equivOfCardEq hcard
  refine ⟨fun s => (e s).1, fun F => ?_⟩
  rw [e.sum_comp (fun p => F p.1), Fintype.sum_sigma]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Simulating weights by a protocol.** Alice draws `i` with probability `w x i / 2 ^ α` and
sends it in `n` bits; Bob answers `true` with probability `c y i / 2 ^ β`. The signed vote of the
protocol is `∑ i, w x i * (2 ^ β - 2 * c y i)`. -/
private theorem exists_protocol_of_weights {ι : Type*} [Fintype ι] [Nonempty ι] {n α β : ℕ}
    (hι : Fintype.card ι ≤ 2 ^ n) (w : X → ι → ℕ) (hw : ∀ x, ∑ i, w x i = 2 ^ α)
    (c : Y → ι → ℕ) (hc : ∀ y i, c y i ≤ 2 ^ β) :
    ∃ P : PrivateCoin α β X Y Bool, P.depth ≤ n + 1 ∧ ∀ x y,
      ∑ s, ∑ t, BitString.signVal (P.run (x, s) (y, t)) =
        ∑ i, (w x i : ℝ) * (2 ^ β - 2 * c y i) := by
  classical
  choose σ hσ using fun x => exists_sampler (w x) (hw x)
  choose τ hτ using fun y i => exists_sampler (α := β)
    (fun b : Bool => if b then c y i else 2 ^ β - c y i)
    (by rw [Fintype.sum_bool]; simp only [ite_true, Bool.false_eq_true, ite_false]
        have := hc y i; omega)
  obtain ⟨e⟩ : Nonempty (ι ↪ BitString n) :=
    Function.Embedding.nonempty_of_card_le (by rwa [BitString.card])
  refine ⟨Protocol.aliceSend n (fun xs => e (σ xs.1 xs.2)) fun m =>
    Protocol.bob (fun yt => τ yt.1 (Function.invFun e m) yt.2) (.output false) (.output true),
    ?_, fun x y => ?_⟩
  · exact Protocol.depth_aliceSend_le fun m => by simp
  · simp only [Protocol.run_aliceSend, Protocol.run_bob, Protocol.run_output,
      Function.leftInverse_invFun e.injective _]
    have hb : ∀ i, ∑ t, BitString.signVal (cond (τ y i t) true false) = 2 ^ β - 2 * c y i := by
      intro i
      have := hτ y i BitString.signVal
      simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false,
        BitString.signVal_true, BitString.signVal_false] at this
      rw [Nat.cast_sub (hc y i)] at this
      have hcond : ∀ b : Bool, cond b true false = b := fun b => by cases b <;> rfl
      simp only [hcond]
      rw [this]
      push_cast
      ring
    simp only [hb]
    exact hσ x fun i => 2 ^ β - 2 * (c y i : ℝ)

/-- **Paturi–Simon, upper bound (protocol form).** On finite inputs, `f` has a private-coin
protocol with unbounded error that sends at most `⌈log₂ (signRank f + 1)⌉ + 1` bits: Alice sends
an index in `Option (Fin (signRank f))` drawn according to her row of an integer sign-representation
and Bob answers with one biased bit. -/
theorem exists_solvesUnbounded_depth_le [Finite X] [Fintype Y] (f : X → Y → Bool) :
    ∃ (a b : ℕ) (P : PrivateCoin a b X Y Bool),
      P.SolvesUnbounded (fun x y z => f x y = z) Set.univ Set.univ ∧
        P.depth ≤ Nat.clog 2 (signRank f + 1) + 1 := by
  obtain ⟨U₀, V₀, h₀⟩ := exists_mul_signRepresents f
  obtain ⟨U, V, hUV⟩ := exists_int_mul_signRepresents h₀
  obtain ⟨α, β, w, c, hw0, hw, hc, hid⟩ := exists_int_weights U V
  have hcard : Fintype.card (Option (Fin (signRank f))) ≤ 2 ^ Nat.clog 2 (signRank f + 1) := by
    rw [Fintype.card_option, Fintype.card_fin]
    exact Nat.le_pow_clog one_lt_two _
  obtain ⟨P, hdepth, hrun⟩ := exists_protocol_of_weights hcard (fun x j => (w x j).toNat)
    (fun x => by
      have : ((∑ j, (w x j).toNat : ℕ) : ℤ) = ((2 ^ α : ℕ) : ℤ) := by
        push_cast
        rw [← hw x]
        exact sum_congr rfl fun j _ => Int.toNat_of_nonneg (hw0 x j)
      exact_mod_cast this)
    (fun y j => (c y j).toNat)
    (fun y j => by
      have : (((c y j).toNat : ℕ) : ℤ) ≤ ((2 ^ β : ℕ) : ℤ) := by grind
      exact_mod_cast this)
  refine ⟨α, β, P, fun x _ y _ => ?_, hdepth⟩
  rw [errorProb_lt_half_iff, hrun]
  have hid' : ∑ j, ((w x j).toNat : ℝ) * (2 ^ β - 2 * ((c y j).toNat : ℝ)) =
      2 ^ (α + 1) * ((U * V) x y : ℝ) := by
    have : ∑ j, ((w x j : ℤ) : ℝ) * (2 ^ β - 2 * ((c y j : ℤ) : ℝ)) =
        2 ^ (α + 1) * ((U * V) x y : ℝ) := by exact_mod_cast hid x y
    rw [← this]
    refine sum_congr rfl fun j _ => ?_
    rw [← Int.cast_natCast, ← Int.cast_natCast (R := ℝ) (c y j).toNat,
      Int.toNat_of_nonneg (hw0 x j), Int.toNat_of_nonneg (hc y j).1]
  rw [hid', mul_left_comm]
  exact mul_pos (by positivity) (hUV x y)

/-- **Paturi–Simon, upper bound**: on finite inputs, the unbounded-error complexity of `f` is at
most `⌊log₂ (signRank f)⌋ + 2` [Sherstov and Wu, Theorem 2.16][SherstovWu2019]. -/
theorem uppComplexityFun_le_log_signRank_add_two [Finite X] [Fintype Y] (f : X → Y → Bool) :
    uppComplexityFun f ≤ Nat.log 2 (signRank f) + 2 := by
  obtain ⟨a, b, P, hP, hd⟩ := exists_solvesUnbounded_depth_le f
  refine (uppComplexityFun_le_depth hP).trans ?_
  have : Nat.clog 2 (signRank f + 1) ≤ Nat.log 2 (signRank f) + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self one_lt_two _)
  exact_mod_cast hd.trans (by omega)

/-- **The Paturi–Simon theorem**: on finite inputs, the unbounded-error communication complexity
of a Boolean function lies between `⌈log₂ (signRank f)⌉` and `⌊log₂ (signRank f)⌋ + 2`
[Sherstov and Wu, Theorem 2.16][SherstovWu2019]. -/
theorem clog_signRank_le_uppComplexityFun_le [Finite X] [Fintype Y] (f : X → Y → Bool) :
    (Nat.clog 2 (signRank f) : ℕ∞) ≤ uppComplexityFun f ∧
      uppComplexityFun f ≤ Nat.log 2 (signRank f) + 2 :=
  ⟨clog_signRank_le_uppComplexityFun f, uppComplexityFun_le_log_signRank_add_two f⟩

/-- **Equality is cheap with unbounded error**: on any finite set, three bits suffice, since
equality has sign-rank at most three. Deterministically it needs `⌈log₂ |X|⌉ + 1` bits when
`|X| ≥ 2` (`ecomplexityFun_equality`). -/
theorem uppComplexityFun_equality_le_three [Finite X] [DecidableEq X] :
    uppComplexityFun (equality (X := X)) ≤ 3 := by
  have := Fintype.ofFinite X
  obtain ⟨a, b, P, hP, hd⟩ := exists_solvesUnbounded_depth_le (equality (X := X))
  refine (uppComplexityFun_le_depth hP).trans ?_
  have h4 : Nat.clog 2 (signRank (equality (X := X)) + 1) ≤ 2 :=
    Nat.clog_le_of_le_pow (by have := signRank_equality_le_three (Y := X); omega)
  exact_mod_cast hd.trans (by omega)

end PrivateCoin

end Cslib.Communication

end
