/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Games
import CslibFrontier.Probability.PMF.Bind

/-!
# Indistinguishability and simulation security of garbling schemes

The relations between the indistinguishability and the simulation notions of privacy and
obliviousness of [BellareHoangRogaway2012], Section 4, by explicit reductions.

* Simulation security implies indistinguishability security with a factor of two: from a
  `prv.ind` adversary `A` the reduction `prvIndToSim` builds a `prv.sim` adversary that picks a
  hidden bit `c`, submits `(f_c, x_c)` and checks whether `A` recovers `c`. Against the real
  garbling it plays the hidden-bit `PrvInd` game with `A`; against any simulator its view does not
  depend on `c`, as the simulator only sees `Φ(f_c)` and `ev(f_c, x_c)`, which a valid query makes
  the same for both values of `c`. Hence `Adv^prv.ind(A) = 2 · Adv^prv.sim(prvIndToSim A)`
  against every simulator.
* Indistinguishability security implies simulation security when the side information is
  efficiently invertible: an `ev`-inverter `M` for `Φ` yields a simulator `prvSimFromInverter`
  that garbles `M(Φ(f), ev(f, x))`, and against it the `prv.sim` game on `B` is the `prv.ind` game
  on the adversary `prvSimToInd` that queries `(M(Φ(f), ev(f, x)), (f, x))`.

The same reductions, without the output `ev(f, x)` and the decoding information `d`, relate
`obv.ind` and `obv.sim`, with an inverter of `Φ` in place of an `ev`-inverter.

## Main definitions

* `Cslib.Crypto.Garbling.prvIndToSim`, `Cslib.Crypto.Garbling.obvIndToSim`: the reductions from
  indistinguishability to simulation adversaries.
* `Cslib.Crypto.Garbling.prvSimFromInverter`, `Cslib.Crypto.Garbling.obvSimFromInverter`: the
  simulators built from inverters, and `Cslib.Crypto.Garbling.prvSimToInd`,
  `Cslib.Crypto.Garbling.obvSimToInd`, the corresponding reductions from simulation to
  indistinguishability adversaries.

## Main results

* `Cslib.Crypto.Garbling.prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim`,
  `Cslib.Crypto.Garbling.obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim`: the
  indistinguishability advantage is twice the simulation advantage of the reduction, against
  every simulator ([BellareHoangRogaway2012], Propositions 2 and 3).
* `Cslib.Crypto.Garbling.prvSimAdvantage_prvSimFromInverter_eq`,
  `Cslib.Crypto.Garbling.obvSimAdvantage_obvSimFromInverter_eq`: against the simulator built from
  an inverter, the simulation advantage is the indistinguishability advantage of the reduction
  ([BellareHoangRogaway2012], Propositions 2 and 3).

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

@[expose] public section

namespace Cslib.Crypto.Garbling

open Probability
open scoped NNReal ENNReal

variable {Fn Λ σ : Type}

/-! ## The reductions -/

/-- The state of the reductions from indistinguishability to simulation adversaries: the state
of the indistinguishability adversary, the hidden bit chosen by the reduction and the query. -/
structure IndToSimState (Fn σ : Type) where
  /-- The state of the indistinguishability adversary. -/
  state : σ
  /-- The hidden bit chosen by the reduction. -/
  bit : Bool
  /-- The first function of the query. -/
  fn₀ : Fn
  /-- The second function of the query. -/
  fn₁ : Fn
  /-- The first input of the query. -/
  input₀ : List Bool
  /-- The second input of the query. -/
  input₁ : List Bool

/-- The `prv.sim` adversary built from a `prv.ind` adversary `A` ([BellareHoangRogaway2012],
Proposition 2): it picks a hidden bit `c`, submits `(f_c, x_c)` when the query of `A` is valid
and `(f₀, x₀)` otherwise, and outputs whether `A` recovers `c`. -/
noncomputable def prvIndToSim (G : Scheme Fn) (Φ : SideInfo Fn Λ) [DecidableEq Λ]
    (A : PrvIndAdversary Fn σ) : PrvSimAdversary Fn (IndToSimState Fn σ) where
  choose k := do
    let ((f₀, f₁, x₀, x₁), st) ← A.choose k
    let c ← ProbComp.uniform Bool
    let query :=
      if prvIndValid G Φ f₀ f₁ x₀ x₁ then (if c then f₁ else f₀, if c then x₁ else x₀)
      else (f₀, x₀)
    pure (query, ⟨st, c, f₀, f₁, x₀, x₁⟩)
  guess k s answer := do
    let guess ← A.guess k s.state
      (if prvIndValid G Φ s.fn₀ s.fn₁ s.input₀ s.input₁ then answer else none)
    pure (guess == s.bit)

/-- The `prv.sim` simulator built from an `ev`-inverter `M` for the side information
([BellareHoangRogaway2012], Section 4.2): it garbles the function and encodes the input
produced by `M` from `Φ(f)` and `ev(f, x)`. -/
noncomputable def prvSimFromInverter (G : Scheme Fn) (M : Λ → List Bool → Fn × List Bool) :
    PrvSimulator Λ := fun k y φ => do
  let (f₀, x₀) := M φ y
  let g ← G.garble k f₀
  pure (g.fn, G.encode g.encInfo x₀, g.decInfo)

/-- The `prv.ind` adversary built from a `prv.sim` adversary `B` and an `ev`-inverter `M`
([BellareHoangRogaway2012], Proposition 2): it queries the pair of `M(Φ(f), ev(f, x))` and the
query `(f, x)` of `B`, and guesses as `B` does. -/
def prvSimToInd (G : Scheme Fn) (Φ : SideInfo Fn Λ) (M : Λ → List Bool → Fn × List Bool)
    (B : PrvSimAdversary Fn σ) : PrvIndAdversary Fn σ where
  choose k := do
    let ((f₁, x₁), st) ← B.choose k
    let (f₀, x₀) := M (Φ.phi f₁) (G.ev f₁ x₁)
    pure ((f₀, f₁, x₀, x₁), st)
  guess := B.guess

/-- The `obv.sim` adversary built from an `obv.ind` adversary `A` ([BellareHoangRogaway2012],
Proposition 3): it picks a hidden bit `c`, submits `(f_c, x_c)` when the query of `A` is valid
and `(f₀, x₀)` otherwise, and outputs whether `A` recovers `c`. -/
noncomputable def obvIndToSim (G : Scheme Fn) (Φ : SideInfo Fn Λ) [DecidableEq Λ]
    (A : ObvIndAdversary Fn σ) : ObvSimAdversary Fn (IndToSimState Fn σ) where
  choose k := do
    let ((f₀, f₁, x₀, x₁), st) ← A.choose k
    let c ← ProbComp.uniform Bool
    let query :=
      if obvIndValid G Φ f₀ f₁ x₀ x₁ then (if c then f₁ else f₀, if c then x₁ else x₀)
      else (f₀, x₀)
    pure (query, ⟨st, c, f₀, f₁, x₀, x₁⟩)
  guess k s answer := do
    let guess ← A.guess k s.state
      (if obvIndValid G Φ s.fn₀ s.fn₁ s.input₀ s.input₁ then answer else none)
    pure (guess == s.bit)

/-- The `obv.sim` simulator built from an inverter `M` of the side information
([BellareHoangRogaway2012], Section 4.3): it garbles the function produced by `M` from `Φ(f)`
and encodes the all-zero input. -/
noncomputable def obvSimFromInverter (G : Scheme Fn) (M : Λ → Fn) : ObvSimulator Λ :=
  fun k φ => do
    let f₀ := M φ
    let g ← G.garble k f₀
    pure (g.fn, G.encode g.encInfo (List.replicate (G.inLen f₀) false))

/-- The `obv.ind` adversary built from an `obv.sim` adversary `B` and an inverter `M` of the
side information ([BellareHoangRogaway2012], Proposition 3): it queries the pair of
`M(Φ(f))` on the all-zero input and the query `(f, x)` of `B`, and guesses as `B` does. -/
def obvSimToInd (G : Scheme Fn) (Φ : SideInfo Fn Λ) (M : Λ → Fn) (B : ObvSimAdversary Fn σ) :
    ObvIndAdversary Fn σ where
  choose k := do
    let ((f₁, x₁), st) ← B.choose k
    let f₀ := M (Φ.phi f₁)
    pure ((f₀, f₁, List.replicate (G.inLen f₀) false, x₁), st)
  guess := B.guess

/-! ## Guessing an independent hidden bit -/

/-- Guessing a uniform hidden bit with a guess drawn independently of it succeeds with
probability one half. -/
private theorem succProbability_uniform_bool_beq_const (m : PMF Bool) :
    Game.succProbability
      ((PMF.uniformOfFintype Bool).bind fun c => m.map (fun guess => guess == c)) = 1 / 2 := by
  apply NNReal.coe_injective
  rw [Game.succProbability_uniform_bool_beq (fun _ => m), NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat]
  ring

/-- A game that guesses a uniform hidden bit independently of the bit outputs `true` with
probability one half. -/
private theorem apply_true_eq_half_of_exists {game : Game}
    (h : ∃ m : PMF Bool,
      game = (PMF.uniformOfFintype Bool).bind fun c => m.map (fun guess => guess == c)) :
    game true = ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨m, rfl⟩ := h
  rw [← succProbability_uniform_bool_beq_const m]
  exact (ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)).symm

/-- The difference of two success probabilities is twice the bias of the hidden-bit game
built from them. -/
private theorem abs_sub_eq_two_mul_abs_half_sub (a b : ℝ) :
    |a - b| = 2 * |1 / 2 - (1 - a + b) / 2| := by
  rw [show (1 : ℝ) / 2 - (1 - a + b) / 2 = (a - b) / 2 by ring, abs_div, Nat.abs_ofNat]
  ring

/-! ## Privacy -/

section Privacy

variable (G : Scheme Fn) (Φ : SideInfo Fn Λ) [DecidableEq Λ]

/-- Against any simulator, the reduction `prvIndToSim` outputs `true` with probability exactly
one half: the simulator's view does not depend on the hidden bit. -/
private theorem succProbability_prvSimExp_false_prvIndToSim (hCompat : Φ.Compatible G)
    (A : PrvIndAdversary Fn σ) (S : PrvSimulator Λ) (k : ℕ) :
    Game.succProbability (ProbComp.eval (prvSimExp G Φ S false (prvIndToSim G Φ A) k)) =
      1 / 2 := by
  rw [show (1 / 2 : ℝ≥0) = ((1 / 2 : ℝ≥0) : ℝ≥0∞).toNNReal from (ENNReal.toNNReal_coe _).symm]
  simp only [prvSimExp, prvIndToSim, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  refine congrArg ENNReal.toNNReal (Probability.PMF.bind_apply_of_forall _ ?_)
  rintro ⟨⟨f₀, f₁, x₀, x₁⟩, st⟩
  refine apply_true_eq_half_of_exists ?_
  by_cases hV : prvIndValid G Φ f₀ f₁ x₀ x₁
  · have ⟨hphi, hx₀, hx₁, hev⟩ := hV
    have hlen₁ : x₁.length = G.inLen f₁ := hx₁.trans (hCompat.inLen_eq hphi)
    refine ⟨(ProbComp.eval (S k (G.ev f₁ x₁) (Φ.phi f₁))).bind fun answer =>
      ProbComp.eval (A.guess k st (some answer)), ?_⟩
    congr 1 with c : 1
    cases c <;> simp [hV, hx₀, hlen₁, hphi, hev, ProbComp.eval_bind, PMF.map, Function.comp_def]
  · refine ⟨ProbComp.eval (A.guess k st none), ?_⟩
    congr 1 with c : 1
    by_cases hx₀ : x₀.length = G.inLen f₀ <;>
      simp [hV, hx₀, ProbComp.eval_bind, PMF.bind_const, PMF.map, Function.comp_def]

/-- Against the real garbling, the reduction `prvIndToSim` plays the hidden-bit `PrvInd` game
with `A`. -/
private theorem eval_prvSimExp_true_prvIndToSim (hCompat : Φ.Compatible G)
    (A : PrvIndAdversary Fn σ) (S : PrvSimulator Λ) (k : ℕ) :
    ProbComp.eval (prvSimExp G Φ S true (prvIndToSim G Φ A) k) =
      (PMF.uniformOfFintype Bool).bind fun c =>
        (ProbComp.eval (prvIndExp G Φ c A k)).map (fun guess => guess == c) := by
  simp only [prvSimExp, prvIndToSim, prvIndExp, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind]
  rw [PMF.bind_comm]
  congr 1 with c : 1
  congr 1
  funext ⟨⟨f₀, f₁, x₀, x₁⟩, st⟩
  by_cases hV : prvIndValid G Φ f₀ f₁ x₀ x₁
  · have ⟨hphi, hx₀, hx₁, _⟩ := hV
    have hlen₁ : x₁.length = G.inLen f₁ := hx₁.trans (hCompat.inLen_eq hphi)
    cases c <;> simp [hV, hx₀, hlen₁, ProbComp.eval_bind, PMF.map, Function.comp_def]
  · by_cases hx₀ : x₀.length = G.inLen f₀ <;>
      simp [hV, hx₀, ProbComp.eval_bind, PMF.bind_const, PMF.map, Function.comp_def]

/-- The `prv.ind` advantage of `A` is twice the `prv.sim` advantage of the reduction
`prvIndToSim` against every simulator ([BellareHoangRogaway2012], Proposition 2). -/
theorem prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim (hCompat : Φ.Compatible G)
    (A : PrvIndAdversary Fn σ) (S : PrvSimulator Λ) (k : ℕ) :
    prvIndAdvantage G Φ A k = 2 * prvSimAdvantage G Φ S (prvIndToSim G Φ A) k := by
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_ofNat, prvIndAdvantage, prvSimAdvantage, Game.coe_advantage,
    Game.coe_advantage, succProbability_prvSimExp_false_prvIndToSim G Φ hCompat A S k,
    eval_prvSimExp_true_prvIndToSim G Φ hCompat A S k, Game.succProbability_uniform_bool_beq,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  exact abs_sub_eq_two_mul_abs_half_sub _ _

/-- Simulation privacy implies indistinguishability privacy with a factor of two
([BellareHoangRogaway2012], Proposition 2). -/
theorem prvIndAdvantage_le_two_mul_prvSimAdvantage_prvIndToSim (hCompat : Φ.Compatible G)
    (A : PrvIndAdversary Fn σ) (S : PrvSimulator Λ) (k : ℕ) :
    prvIndAdvantage G Φ A k ≤ 2 * prvSimAdvantage G Φ S (prvIndToSim G Φ A) k :=
  (prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim G Φ hCompat A S k).le

/-- Against the simulator built from an `ev`-inverter `M`, the `prv.sim` game on `B` is the
`prv.ind` game on the reduction `prvSimToInd`. -/
theorem eval_prvSimExp_prvSimFromInverter (hCompat : Φ.Compatible G)
    {M : Λ → List Bool → Fn × List Bool} (hInv : Φ.IsEvInverter G M) (b : Bool)
    (B : PrvSimAdversary Fn σ) (k : ℕ) :
    ProbComp.eval (prvSimExp G Φ (prvSimFromInverter G M) b B k) =
      ProbComp.eval (prvIndExp G Φ b (prvSimToInd G Φ M B) k) := by
  simp only [prvSimExp, prvIndExp, prvSimFromInverter, prvSimToInd, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext ⟨⟨f₁, x₁⟩, st⟩
  have hvalid_iff :
      prvIndValid G Φ (M (Φ.phi f₁) (G.ev f₁ x₁)).1 f₁ (M (Φ.phi f₁) (G.ev f₁ x₁)).2 x₁ ↔
        x₁.length = G.inLen f₁ := by
    constructor
    · rintro ⟨hphi, -, hx₁, -⟩
      exact hx₁.trans (hCompat.inLen_eq hphi)
    · intro hx₁
      obtain ⟨hphi, hx₀, hev⟩ := hInv f₁ x₁ hx₁ _ _ rfl
      exact ⟨hphi, hx₀, hx₁.trans (hCompat.inLen_eq hphi.symm), hev⟩
  by_cases hx₁ : x₁.length = G.inLen f₁
  · have hV := hvalid_iff.mpr hx₁
    cases b <;> simp [hx₁, hV, ProbComp.eval_bind]
  · have hV := mt hvalid_iff.mp hx₁
    simp [hx₁, hV]

/-- Against the simulator built from an `ev`-inverter `M`, the `prv.sim` advantage of `B` is the
`prv.ind` advantage of the reduction `prvSimToInd` ([BellareHoangRogaway2012],
Proposition 2). -/
theorem prvSimAdvantage_prvSimFromInverter_eq (hCompat : Φ.Compatible G)
    {M : Λ → List Bool → Fn × List Bool} (hInv : Φ.IsEvInverter G M) (B : PrvSimAdversary Fn σ)
    (k : ℕ) :
    prvSimAdvantage G Φ (prvSimFromInverter G M) B k =
      prvIndAdvantage G Φ (prvSimToInd G Φ M B) k := by
  rw [prvSimAdvantage, prvIndAdvantage, eval_prvSimExp_prvSimFromInverter G Φ hCompat hInv,
    eval_prvSimExp_prvSimFromInverter G Φ hCompat hInv]

/-- Indistinguishability privacy implies simulation privacy for side information with an
`ev`-inverter ([BellareHoangRogaway2012], Proposition 2). -/
theorem prvSimAdvantage_prvSimFromInverter_le (hCompat : Φ.Compatible G)
    {M : Λ → List Bool → Fn × List Bool} (hInv : Φ.IsEvInverter G M) (B : PrvSimAdversary Fn σ)
    (k : ℕ) :
    prvSimAdvantage G Φ (prvSimFromInverter G M) B k ≤
      prvIndAdvantage G Φ (prvSimToInd G Φ M B) k :=
  (prvSimAdvantage_prvSimFromInverter_eq G Φ hCompat hInv B k).le

end Privacy

/-! ## Obliviousness -/

section Obliviousness

variable (G : Scheme Fn) (Φ : SideInfo Fn Λ) [DecidableEq Λ]

/-- Against any simulator, the reduction `obvIndToSim` outputs `true` with probability exactly
one half: the simulator's view does not depend on the hidden bit. -/
private theorem succProbability_obvSimExp_false_obvIndToSim (hCompat : Φ.Compatible G)
    (A : ObvIndAdversary Fn σ) (S : ObvSimulator Λ) (k : ℕ) :
    Game.succProbability (ProbComp.eval (obvSimExp G Φ S false (obvIndToSim G Φ A) k)) =
      1 / 2 := by
  rw [show (1 / 2 : ℝ≥0) = ((1 / 2 : ℝ≥0) : ℝ≥0∞).toNNReal from (ENNReal.toNNReal_coe _).symm]
  simp only [obvSimExp, obvIndToSim, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  refine congrArg ENNReal.toNNReal (Probability.PMF.bind_apply_of_forall _ ?_)
  rintro ⟨⟨f₀, f₁, x₀, x₁⟩, st⟩
  refine apply_true_eq_half_of_exists ?_
  by_cases hV : obvIndValid G Φ f₀ f₁ x₀ x₁
  · have ⟨hphi, hx₀, hx₁⟩ := hV
    have hlen₁ : x₁.length = G.inLen f₁ := hx₁.trans (hCompat.inLen_eq hphi)
    refine ⟨(ProbComp.eval (S k (Φ.phi f₁))).bind fun answer =>
      ProbComp.eval (A.guess k st (some answer)), ?_⟩
    congr 1 with c : 1
    cases c <;> simp [hV, hx₀, hlen₁, hphi, ProbComp.eval_bind, PMF.map, Function.comp_def]
  · refine ⟨ProbComp.eval (A.guess k st none), ?_⟩
    congr 1 with c : 1
    by_cases hx₀ : x₀.length = G.inLen f₀ <;>
      simp [hV, hx₀, ProbComp.eval_bind, PMF.bind_const, PMF.map, Function.comp_def]

/-- Against the real garbling, the reduction `obvIndToSim` plays the hidden-bit `ObvInd` game
with `A`. -/
private theorem eval_obvSimExp_true_obvIndToSim (hCompat : Φ.Compatible G)
    (A : ObvIndAdversary Fn σ) (S : ObvSimulator Λ) (k : ℕ) :
    ProbComp.eval (obvSimExp G Φ S true (obvIndToSim G Φ A) k) =
      (PMF.uniformOfFintype Bool).bind fun c =>
        (ProbComp.eval (obvIndExp G Φ c A k)).map (fun guess => guess == c) := by
  simp only [obvSimExp, obvIndToSim, obvIndExp, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind]
  rw [PMF.bind_comm]
  congr 1 with c : 1
  congr 1
  funext ⟨⟨f₀, f₁, x₀, x₁⟩, st⟩
  by_cases hV : obvIndValid G Φ f₀ f₁ x₀ x₁
  · have ⟨hphi, hx₀, hx₁⟩ := hV
    have hlen₁ : x₁.length = G.inLen f₁ := hx₁.trans (hCompat.inLen_eq hphi)
    cases c <;> simp [hV, hx₀, hlen₁, ProbComp.eval_bind, PMF.map, Function.comp_def]
  · by_cases hx₀ : x₀.length = G.inLen f₀ <;>
      simp [hV, hx₀, ProbComp.eval_bind, PMF.bind_const, PMF.map, Function.comp_def]

/-- The `obv.ind` advantage of `A` is twice the `obv.sim` advantage of the reduction
`obvIndToSim` against every simulator ([BellareHoangRogaway2012], Proposition 3). -/
theorem obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim (hCompat : Φ.Compatible G)
    (A : ObvIndAdversary Fn σ) (S : ObvSimulator Λ) (k : ℕ) :
    obvIndAdvantage G Φ A k = 2 * obvSimAdvantage G Φ S (obvIndToSim G Φ A) k := by
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_ofNat, obvIndAdvantage, obvSimAdvantage, Game.coe_advantage,
    Game.coe_advantage, succProbability_obvSimExp_false_obvIndToSim G Φ hCompat A S k,
    eval_obvSimExp_true_obvIndToSim G Φ hCompat A S k, Game.succProbability_uniform_bool_beq,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  exact abs_sub_eq_two_mul_abs_half_sub _ _

/-- Simulation obliviousness implies indistinguishability obliviousness with a factor of two
([BellareHoangRogaway2012], Proposition 3). -/
theorem obvIndAdvantage_le_two_mul_obvSimAdvantage_obvIndToSim (hCompat : Φ.Compatible G)
    (A : ObvIndAdversary Fn σ) (S : ObvSimulator Λ) (k : ℕ) :
    obvIndAdvantage G Φ A k ≤ 2 * obvSimAdvantage G Φ S (obvIndToSim G Φ A) k :=
  (obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim G Φ hCompat A S k).le

/-- Against the simulator built from an inverter `M` of the side information, the `obv.sim`
game on `B` is the `obv.ind` game on the reduction `obvSimToInd`. -/
theorem eval_obvSimExp_obvSimFromInverter (hCompat : Φ.Compatible G) {M : Λ → Fn}
    (hInv : Φ.IsInverter M) (b : Bool) (B : ObvSimAdversary Fn σ) (k : ℕ) :
    ProbComp.eval (obvSimExp G Φ (obvSimFromInverter G M) b B k) =
      ProbComp.eval (obvIndExp G Φ b (obvSimToInd G Φ M B) k) := by
  simp only [obvSimExp, obvIndExp, obvSimFromInverter, obvSimToInd, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext ⟨⟨f₁, x₁⟩, st⟩
  have hvalid_iff :
      obvIndValid G Φ (M (Φ.phi f₁)) f₁ (List.replicate (G.inLen (M (Φ.phi f₁))) false) x₁ ↔
        x₁.length = G.inLen f₁ := by
    constructor
    · rintro ⟨hphi, -, hx₁⟩
      exact hx₁.trans (hCompat.inLen_eq hphi)
    · intro hx₁
      exact ⟨hInv f₁, List.length_replicate, hx₁.trans (hCompat.inLen_eq (hInv f₁).symm)⟩
  by_cases hx₁ : x₁.length = G.inLen f₁
  · have hV := hvalid_iff.mpr hx₁
    cases b <;> simp [hx₁, hV, ProbComp.eval_bind]
  · have hV := mt hvalid_iff.mp hx₁
    simp [hx₁, hV]

/-- Against the simulator built from an inverter `M` of the side information, the `obv.sim`
advantage of `B` is the `obv.ind` advantage of the reduction `obvSimToInd`
([BellareHoangRogaway2012], Proposition 3). -/
theorem obvSimAdvantage_obvSimFromInverter_eq (hCompat : Φ.Compatible G) {M : Λ → Fn}
    (hInv : Φ.IsInverter M) (B : ObvSimAdversary Fn σ) (k : ℕ) :
    obvSimAdvantage G Φ (obvSimFromInverter G M) B k =
      obvIndAdvantage G Φ (obvSimToInd G Φ M B) k := by
  rw [obvSimAdvantage, obvIndAdvantage, eval_obvSimExp_obvSimFromInverter G Φ hCompat hInv,
    eval_obvSimExp_obvSimFromInverter G Φ hCompat hInv]

/-- Indistinguishability obliviousness implies simulation obliviousness for invertible side
information ([BellareHoangRogaway2012], Proposition 3). -/
theorem obvSimAdvantage_obvSimFromInverter_le (hCompat : Φ.Compatible G) {M : Λ → Fn}
    (hInv : Φ.IsInverter M) (B : ObvSimAdversary Fn σ) (k : ℕ) :
    obvSimAdvantage G Φ (obvSimFromInverter G M) B k ≤
      obvIndAdvantage G Φ (obvSimToInd G Φ M B) k :=
  (obvSimAdvantage_obvSimFromInverter_eq G Φ hCompat hInv B k).le

end Obliviousness

end Cslib.Crypto.Garbling
