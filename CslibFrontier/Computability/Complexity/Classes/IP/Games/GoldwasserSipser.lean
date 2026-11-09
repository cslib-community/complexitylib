/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.IP.Games.Emulation
public import CslibFrontier.Computability.Complexity.Classes.IP.Games.Repetition
public import CslibFrontier.Computability.Complexity.Classes.NP.Advice
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.RoundCollapse

import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Advice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Foundations.Data.Nat.Asymptotics
import CslibFrontier.Foundations.Data.Nat.PowClog

/-!
# Private coins versus public coins: `IP[k] ⊆ AM[k + 2]`

The theorem of [Goldwasser and Sipser][GoldwasserSipser1986] that private coins can be replaced
by public coins with two extra moves, [Arora and Barak, Theorem 8.8][AroraBarak07]. A private-coin
game verifier of `IPGameClass enc π` becomes a public-coin game verifier of
`AMGameClass enc (Emulation.pattern (π ++ [.verifier]))`: every verifier move becomes an Arthur
move and a Merlin move, and the coins are revealed by a last verifier move.

The proof applies the emulation of
`CslibFrontier.Computability.Complexity.Classes.IP.Games.Emulation`
to the count of accepted coins:

* The private coins are revealed by a last verifier move
  (`Cslib.Complexity.Emulation.revealPayoff`).
  The count of the game with this move, on the payoff that the coins agree with the transcript
  and accept it, is the count of coins accepted against an optimal prover
  (`Cslib.Complexity.Emulation.countFrom_revealPayoff`).
* The verifier is first repeated `R(n)` times in parallel
  (`Cslib.Complexity.IPGame.countAt_repeat`), which turns the yes/no gap `2` into `2 ^ R(n)`.
* With `B(n)` bits of claims, the threshold `K = B + ⌈log₂ (6 c (B + 1))⌉`
  (`Cslib.Complexity.Emulation.threshold`) and the initial claim `ρ(n) - R(n)`, Arthur accepts with
  probability at least `5 / 6` on a member (`Cslib.Complexity.Emulation.two_le_three_mul_value`)
  and at most `1 / 3` on a non-member (`Cslib.Complexity.Emulation.three_mul_value_le_one`). The
  soundness error has a factor `μ ^ c` for a polynomial `μ` and the constant number `c` of
  verifier moves, which the gap `2 ^ R(n)` beats for `R` a large multiple of the game size.

With round collapse [Babai and Moran][BabaiMoran1988] (`Cslib.Complexity.AMk_eq_AM`) this gives
`IP[k] ⊆ AM[k + 2]` and `IP[k] = AM` for every constant `k ≥ 2`. Merging adjacent Merlin moves,
the pattern of the emulation alternates in `k + 2` moves for an even `k` and in `k + 3` moves for
an odd `k`; there the bound `k + 2` comes from round collapse.

## Main definitions

* `Cslib.Complexity.Emulation.threshold`: the threshold `K` of the emulation.
* `Cslib.Complexity.Emulation.revealPayoff`: the payoff of a private-coin verifier that reveals
  its coins.
* `Cslib.Complexity.Emulation.amVerifier`: the public-coin verifier.

## Main results

* `Cslib.Complexity.Emulation.two_le_three_mul_value`,
  `Cslib.Complexity.Emulation.three_mul_value_le_one`: completeness and soundness of the
  emulation with the default threshold.
* `Cslib.Complexity.Emulation.countFrom_revealPayoff`: revealing the coins.
* `Cslib.Complexity.IPGameClass_subset_AMGameClass`: **private coins versus public coins**.
* `Cslib.Complexity.IPk_subset_AMk`: `IP[k] ⊆ AM[k + 2]`.
* `Cslib.Complexity.IPk_eq_AM`: `IP[k] = AM` for `k ≥ 2`.
* `Cslib.Complexity.IPGameClass_subset_NPPoly`: private-coin games are in `NP/poly`.

## References

* [L. Babai, S. Moran, *Arthur-Merlin games: a randomized proof system, and a hierarchy of
  complexity classes*][BabaiMoran1988]
* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM Filter

variable {α : Type}

namespace IPGame

@[simp] theorem evalShape_nil (n : ℕ) : evalShape [] n = [] := rfl

theorem evalShape_cons (v : IPMove) (p : Polynomial ℕ) (G : List (IPMove × Polynomial ℕ)) (n : ℕ) :
    evalShape ((v, p) :: G) n = (v, p.eval n) :: evalShape G n := rfl

theorem evalShape_append (G H : List (IPMove × Polynomial ℕ)) (n : ℕ) :
    evalShape (G ++ H) n = evalShape G n ++ evalShape H n := by
  simp [evalShape]

theorem verifierBits_append (g h : List (IPMove × ℕ)) :
    verifierBits (g ++ h) = verifierBits g + verifierBits h := by
  induction g with
  | nil => simp [verifierBits, AMGame.arthurBits]
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · rw [List.cons_append, verifierBits_verifier, verifierBits_verifier, ih, Nat.add_assoc]
    · rw [List.cons_append, verifierBits_prover, verifierBits_prover, ih]

theorem verifierBits_le_transcriptLength (g : List (IPMove × ℕ)) :
    verifierBits g ≤ transcriptLength g := by
  rw [← transcriptLength_toAM, transcriptLength_eq_arthurBits_add_merlinBits]
  exact Nat.le_add_right _ _

theorem verifierMoves_evalShape (G : List (IPMove × Polynomial ℕ)) (n : ℕ) :
    verifierMoves (evalShape G n) = (G.map Prod.fst).count .verifier := by
  simp [verifierMoves, evalShape, Function.comp_def]

end IPGame

namespace Emulation

open IPGame

/-! ### The default threshold -/

/-- The threshold `K = B + ⌈log₂ (6 c (B + 1))⌉` of the emulation of a shape with `c` verifier
moves and `B` bits of claims: the completeness error `c (B + 1) 2 ^ B / 2 ^ K` is at most `1 / 6`
and the factor `μ = 6 c (B + 1) 2 ^ (K - B)` of the soundness error is polynomial. -/
def threshold (c B : ℕ) : ℕ := B + Nat.clog 2 (6 * c * (B + 1))

private theorem one_lt_six_mul (c B : ℕ) (hc : 0 < c) : 1 < 6 * c * (B + 1) := by
  have : 1 ≤ c * (B + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hc.ne' (Nat.succ_ne_zero B))
  rw [Nat.mul_assoc]
  omega

private theorem clog_bounds (X : ℕ) (hX : 1 < X) :
    X ≤ 2 ^ Nat.clog 2 X ∧ 2 ^ Nat.clog 2 X < 2 * X ∧ Nat.clog 2 X < 2 * X := by
  have h1 := Nat.le_pow_clog one_lt_two X
  have h2 := Nat.pow_clog_lt_mul one_lt_two (by omega : X ≠ 0)
  have h4 := Nat.lt_two_pow_self (n := Nat.clog 2 X)
  omega

theorem threshold_le (c B : ℕ) (hc : 0 < c) : threshold c B < B + 2 * (6 * c * (B + 1)) := by
  have := (clog_bounds _ (one_lt_six_mul c B hc)).2.2
  unfold threshold
  omega

private theorem complete_arith (c B : ℕ) (hc : 0 < c) :
    (c : ℚ) * ((B + 1) * 2 ^ B / 2 ^ threshold c B) ≤ 1 / 6 := by
  obtain ⟨h1, -, -⟩ := clog_bounds _ (one_lt_six_mul c B hc)
  unfold threshold
  generalize Nat.clog 2 (6 * c * (B + 1)) = e at h1 ⊢
  have h1' : ((6 * c * (B + 1) : ℕ) : ℚ) ≤ 2 ^ e := by exact_mod_cast h1
  push_cast at h1'
  have h2 : ((B : ℚ) + 1) * 2 ^ B / 2 ^ (B + e) = (B + 1) / 2 ^ e := by
    rw [pow_add]
    field_simp
  rw [h2, mul_div_assoc', div_le_iff₀ (by positivity)]
  linarith

private theorem sound_arith (c B N κ : ℕ) (hc : 0 < c)
    (hN : 6 * (72 * c ^ 2 * (B + 1) ^ 2) ^ c * N ≤ 2 ^ κ) :
    (c : ℚ) * ((B + 1) * 2 ^ threshold c B / ((6 * c * (B + 1) * 2 ^ (threshold c B - B) : ℕ) *
        2 ^ B)) + ((6 * c * (B + 1) * 2 ^ (threshold c B - B) : ℕ) : ℚ) ^ c * N / 2 ^ κ ≤
      1 / 3 := by
  obtain ⟨-, h2, -⟩ := clog_bounds _ (one_lt_six_mul c B hc)
  have hK : threshold c B - B = Nat.clog 2 (6 * c * (B + 1)) := by unfold threshold; omega
  rw [hK]
  unfold threshold
  generalize Nat.clog 2 (6 * c * (B + 1)) = e at h2 ⊢
  have hμ : 6 * c * (B + 1) * 2 ^ e ≤ 72 * c ^ 2 * (B + 1) ^ 2 := by
    calc 6 * c * (B + 1) * 2 ^ e ≤ 6 * c * (B + 1) * (2 * (6 * c * (B + 1))) :=
          Nat.mul_le_mul_left _ h2.le
      _ = 72 * c ^ 2 * (B + 1) ^ 2 := by ring
  have hN' : 6 * ((6 * c * (B + 1) * 2 ^ e) ^ c * N) ≤ 2 ^ κ :=
    calc 6 * ((6 * c * (B + 1) * 2 ^ e) ^ c * N) ≤ 6 * ((72 * c ^ 2 * (B + 1) ^ 2) ^ c * N) := by
          gcongr
      _ = 6 * (72 * c ^ 2 * (B + 1) ^ 2) ^ c * N := (Nat.mul_assoc _ _ _).symm
      _ ≤ 2 ^ κ := hN
  have hN'' : (6 : ℚ) * (((6 * c * (B + 1) * 2 ^ e : ℕ) : ℚ) ^ c * N) ≤ 2 ^ κ := by
    exact_mod_cast hN'
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have h1 : (c : ℚ) * ((B + 1) * 2 ^ (B + e) / ((6 * c * (B + 1) * 2 ^ e : ℕ) * 2 ^ B)) =
      1 / 6 := by
    push_cast
    rw [pow_add]
    field_simp
  have h2' : (((6 * c * (B + 1) * 2 ^ e : ℕ) : ℚ) ^ c * N) / 2 ^ κ ≤ 1 / 6 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  rw [h1]
  linarith

/-- **Completeness with the default threshold**: with `c > 0` verifier moves of at most `B` bits
in total, the padding `Z ≥ 2 (B + 6 c (B + 1))` and an initial claim `κ ≤ B` with `2 ^ κ` at most
the count, Merlin wins the public-coin game with probability at least `2 / 3` (in fact `5 / 6`). -/
theorem two_le_three_mul_value (B Z : ℕ) (V : List Bool → Bool) (g : List (IPMove × ℕ))
    (hc : 0 < verifierMoves g) (hZ : 2 * (B + 6 * verifierMoves g * (B + 1)) ≤ Z)
    (hg : verifierBits g ≤ B) (κ : ℕ) (hκ : κ ≤ B) (hN : 2 ^ κ ≤ countFrom g V []) :
    2 ≤ 3 * AMGame.value true (shape B Z g)
      (fun t => ((check B Z (threshold (verifierMoves g) B) V g κ [] t).toNat : ℚ)) := by
  have hK := threshold_le (verifierMoves g) B hc
  have h := one_sub_le_value B Z (threshold (verifierMoves g) B) (by unfold threshold; omega)
    (by omega) V g hg κ hκ [] hN
  have := complete_arith (verifierMoves g) B hc
  linarith

/-- **Soundness with the default threshold**: with `c > 0` verifier moves, an initial claim
`κ ≤ B` and a count `N` with `6 (72 c² (B + 1)²) ^ c N ≤ 2 ^ κ`, Merlin wins the public-coin game
with probability at most `1 / 3`. -/
theorem three_mul_value_le_one (B Z : ℕ) (V : List Bool → Bool) (g : List (IPMove × ℕ))
    (hc : 0 < verifierMoves g) (κ : ℕ) (hκ : κ ≤ B)
    (hN : 6 * (72 * verifierMoves g ^ 2 * (B + 1) ^ 2) ^ verifierMoves g * countFrom g V [] ≤
      2 ^ κ) :
    3 * AMGame.value true (shape B Z g)
      (fun t => ((check B Z (threshold (verifierMoves g) B) V g κ [] t).toNat : ℚ)) ≤ 1 := by
  have h := value_le B Z (threshold (verifierMoves g) B)
    (6 * verifierMoves g * (B + 1) * 2 ^ (threshold (verifierMoves g) B - B))
    (by unfold threshold; omega) (by positivity) V g κ (by unfold threshold; omega) []
  have := sound_arith (verifierMoves g) B (countFrom g V []) κ hc hN
  linarith

theorem computableInPolyTime_threshold {γ : Type} {encIn : γ ↪ List Bool} (c : ℕ) {B : γ → ℕ}
    (hB : ComputableInPolyTime B encIn encUnary) :
    ComputableInPolyTime (fun x => threshold c (B x)) encIn encUnary :=
  ComputableInPolyTime.unary_add' hB ((ComputableInPolyTime.unary_clog_const 2).comp
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const (6 * c))
      (ComputableInPolyTime.unary_add' hB (ComputableInPolyTime.const 1))))

/-! ### Revealing the coins -/

/-- The payoff of a private-coin verifier `msg`, `dec` on the shape `g` followed by a verifier
move that reveals its coins: the transcript `t` of `L` bits followed by the coins `c` is accepted
when the coins agree with `t` and accept it. -/
def revealPayoff (msg : List Bool → ℕ → List Bool → List Bool) (dec : List Bool → List Bool → Bool)
    (g : List (IPMove × ℕ)) (L : ℕ) (w : List Bool) : Bool :=
  agrees (msg (w.drop L)) g 0 [] (w.take L) && dec (w.drop L) (w.take L)

/-- **Revealing the coins**: the count of the shape followed by a verifier move of `ρ` bits, on
the payoff `Cslib.Complexity.Emulation.revealPayoff`, is the number of coins accepted against an
optimal prover. -/
theorem countFrom_revealPayoff (msg : List Bool → ℕ → List Bool → List Bool)
    (dec : List Bool → List Bool → Bool) (g : List (IPMove × ℕ)) {L : ℕ}
    (hL : transcriptLength g = L) (ρ : ℕ) :
    countFrom (g ++ [(.verifier, ρ)]) (revealPayoff msg dec g L) [] =
      bestCount (ρ := ρ) (fun c => msg (List.ofFn c)) (fun c => dec (List.ofFn c)) g := by
  unfold countFrom bestCount
  rw [count_append]
  refine count_congr_of_length g fun t ht => ?_
  rw [count_verifier, acceptedCoins, card_filter]
  refine sum_congr rfl fun c _ => ?_
  have h1 : (t ++ (List.ofFn c ++ [])).take L = t := by
    rw [List.append_nil]; exact List.take_left' (ht.trans hL)
  have h2 : (t ++ (List.ofFn c ++ [])).drop L = List.ofFn c := by
    rw [List.append_nil]; exact List.drop_left' (ht.trans hL)
  simp only [count_nil, List.nil_append, revealPayoff, h1, h2]
  cases agrees (msg (List.ofFn c)) g 0 [] t && dec (List.ofFn c) t <;> rfl

theorem computableInPolyTime_agrees {γ : Type} {encIn : γ ↪ List Bool}
    (G : List (IPMove × Polynomial ℕ)) {len : γ → ℕ} {msg : γ × ℕ × List Bool → List Bool}
    (hlen : ComputableInPolyTime len encIn encUnary)
    (hmsg : ComputableInPolyTime msg (encPair encIn (encPair encUnary encBits)) encBits)
    {j : γ → ℕ} {p t : γ → List Bool} (hj : ComputableInPolyTime j encIn encUnary)
    (hp : ComputableInPolyTime p encIn encBits) (ht : ComputableInPolyTime t encIn encBits) :
    ComputableInPolyTime (fun x => agrees (fun j p => msg (x, j, p)) (evalShape G (len x)) (j x)
      (p x) (t x)) encIn encBool := by
  induction G generalizing j p t with
  | nil => exact (ComputableInPolyTime.const true).of_enc_eq fun x => rfl
  | cons y G ih =>
    obtain ⟨_ | _, q⟩ := y
    · have hn : ComputableInPolyTime (fun x => q.eval (len x)) encIn encUnary :=
        (ComputableInPolyTime.unary_eval q).comp hlen
      have htake := ComputableInPolyTime.bitsTakeWithInput ht hn
      have hm := ComputableInPolyTime.bitsRowWithInput hn (ComputableInPolyTime.const 0)
        (hmsg.comp (ComputableInPolyTime.id'.prod (hj.prod hp)))
      have hrec := ih (ComputableInPolyTime.unary_add' hj (ComputableInPolyTime.const 1))
        (ComputableInPolyTime.bitsAppend hp htake) (ComputableInPolyTime.bitsDropWithInput ht hn)
      refine (ComputableInPolyTime.bool_and' (ComputableInPolyTime.decide_eq' htake hm)
        hrec).of_enc_eq fun x => ?_
      simp only [evalShape, List.map_cons, agrees, BitString.listRow_zero]
      rfl
    · have hn : ComputableInPolyTime (fun x => q.eval (len x)) encIn encUnary :=
        (ComputableInPolyTime.unary_eval q).comp hlen
      exact (ih (ComputableInPolyTime.unary_add' hj (ComputableInPolyTime.const 1))
        (ComputableInPolyTime.bitsAppend hp (ComputableInPolyTime.bitsTakeWithInput ht hn))
        (ComputableInPolyTime.bitsDropWithInput ht hn)).of_enc_eq fun x => rfl

theorem computableInPolyTime_revealPayoff {γ : Type} {encIn : γ ↪ List Bool}
    (G : List (IPMove × Polynomial ℕ)) {len L : γ → ℕ}
    {msg : γ × List Bool × ℕ × List Bool → List Bool} {dec : γ × List Bool × List Bool → Bool}
    (hlen : ComputableInPolyTime len encIn encUnary) (hL : ComputableInPolyTime L encIn encUnary)
    (hmsg : ComputableInPolyTime msg (encPair encIn (encPair encBits (encPair encUnary encBits)))
      encBits)
    (hdec : ComputableInPolyTime dec (encPair encIn (encPair encBits encBits)) encBool)
    {w : γ → List Bool} (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun x => revealPayoff (fun c j p => msg (x, c, j, p))
      (fun c t => dec (x, c, t)) (evalShape G (len x)) (L x) (w x)) encIn encBool := by
  have hc := ComputableInPolyTime.bitsDropWithInput hw hL
  have ht := ComputableInPolyTime.bitsTakeWithInput hw hL
  have hmsg' : ComputableInPolyTime (fun y : γ × ℕ × List Bool => msg (y.1, w y.1 |>.drop (L y.1),
      y.2.1, y.2.2)) (encPair encIn (encPair encUnary encBits)) encBits :=
    hmsg.comp ((ComputableInPolyTime.fst _ _).prod ((hc.comp (.fst _ _)).prod (.snd _ _)))
  have hag := computableInPolyTime_agrees G hlen hmsg' (ComputableInPolyTime.const 0)
    (ComputableInPolyTime.const []) ht
  have hd := hdec.comp (ComputableInPolyTime.id'.prod (hc.prod ht))
  exact (ComputableInPolyTime.bool_and' hag hd).of_enc_eq fun x => rfl

/-! ### The public-coin verifier -/

/-- The count of the shape `G` followed by a verifier move revealing `ρ(n)` coins, on the payoff
`Cslib.Complexity.Emulation.revealPayoff`, is the count of the private-coin verifier. -/
theorem countFrom_revealPayoff_eq_countAt (enc : α ↪ List Bool) (G : List (IPMove × Polynomial ℕ))
    (ρ : Polynomial ℕ) (msg : α × List Bool × ℕ × List Bool → List Bool)
    (dec : α × List Bool × List Bool → Bool) (a : α) :
    countFrom (evalShape (G ++ [(.verifier, ρ)]) (enc a).length)
        (revealPayoff (fun c j p => msg (a, c, j, p)) (fun c t => dec (a, c, t))
          (evalShape G (enc a).length) (transcriptLength (evalShape G (enc a).length))) [] =
      countAt enc G ρ msg dec a := by
  rw [evalShape_append, evalShape_cons, evalShape_nil]
  exact countFrom_revealPayoff _ _ _ rfl _

/-- The public-coin verifier emulating the private-coin verifier `msg`, `dec` of shape `G` with
`ρ(n)` coins, where `n` is the length of the encoded instance: it runs
`Cslib.Complexity.Emulation.check` with `B(n)` bits of claims, padding `Z(n)`, the default
threshold and the initial claim `ρ(n) - T(n)`, on the shape `G` followed by a verifier move that
reveals the coins. With `T(n)` parallel copies of a verifier accepting two thirds of the coins on
a member, the initial claim `κ` satisfies the one-sided bound `2 ^ κ ≤ (3 / 4) ^ T(n) N` for the
count `N`. -/
def amVerifier (enc : α ↪ List Bool) (G : List (IPMove × Polynomial ℕ)) (ρ B Z T : Polynomial ℕ)
    (msg : α × List Bool × ℕ × List Bool → List Bool) (dec : α × List Bool × List Bool → Bool)
    (x : α × List Bool) : Bool :=
  check (B.eval (enc x.1).length) (Z.eval (enc x.1).length)
    (threshold ((G.map Prod.fst).count .verifier + 1) (B.eval (enc x.1).length))
    (revealPayoff (fun c j p => msg (x.1, c, j, p)) (fun c t => dec (x.1, c, t))
      (evalShape G (enc x.1).length) (transcriptLength (evalShape G (enc x.1).length)))
    (evalShape (G ++ [(.verifier, ρ)]) (enc x.1).length)
    (ρ.eval (enc x.1).length - T.eval (enc x.1).length) [] x.2

theorem computableInPolyTime_amVerifier {enc : α ↪ List Bool} (G : List (IPMove × Polynomial ℕ))
    (ρ B Z T : Polynomial ℕ) {msg : α × List Bool × ℕ × List Bool → List Bool}
    {dec : α × List Bool × List Bool → Bool}
    (hmsg : ComputableInPolyTime msg (encMsgInput enc) encBits)
    (hdec : ComputableInPolyTime dec (encDecInput enc) encBool) :
    ComputableInPolyTime (amVerifier enc G ρ B Z T msg dec) (encPair enc encBits) encBool := by
  have hn : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length) (encPair enc encBits)
      encUnary := (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
  have hB := (ComputableInPolyTime.unary_eval B).comp hn
  have hL : ComputableInPolyTime (fun x : α × List Bool =>
      transcriptLength (evalShape G (enc x.1).length)) (encPair enc encBits) encUnary := by
    refine ((ComputableInPolyTime.unary_eval
      (AMGame.transcriptLengthPoly (G.map fun x => (x.1.toAM, x.2)))).comp hn).of_enc_eq
      fun x => ?_
    simp only [Function.comp_apply, ← AMGame.transcriptLength_evalShape, ← toAM_evalShape,
      transcriptLength_toAM]
  have hmsg' : ComputableInPolyTime (fun y : (α × List Bool) × List Bool × ℕ × List Bool =>
      msg (y.1.1, y.2)) (encPair (encPair enc encBits) (encPair encBits (encPair encUnary encBits)))
      encBits :=
    hmsg.comp (((ComputableInPolyTime.fst _ _).comp (.fst _ _)).prod (.snd _ _))
  have hdec' : ComputableInPolyTime (fun y : (α × List Bool) × List Bool × List Bool =>
      dec (y.1.1, y.2)) (encPair (encPair enc encBits) (encPair encBits encBits)) encBool :=
    hdec.comp (((ComputableInPolyTime.fst _ _).comp (.fst _ _)).prod (.snd _ _))
  exact computableInPolyTime_check (G ++ [(.verifier, ρ)]) (B := fun x => B.eval (enc x.1).length)
    (Z := fun x => Z.eval (enc x.1).length)
    (K := fun x => threshold ((G.map Prod.fst).count .verifier + 1) (B.eval (enc x.1).length))
    (len := fun x => (enc x.1).length)
    (V := fun x => revealPayoff (fun c j p => msg (x.1, c, j, p)) (fun c t => dec (x.1, c, t))
      (evalShape G (enc x.1).length) (transcriptLength (evalShape G (enc x.1).length)))
    hB ((ComputableInPolyTime.unary_eval Z).comp hn) (computableInPolyTime_threshold _ hB) hn
    (fun hq => computableInPolyTime_revealPayoff G hn hL hmsg' hdec' hq)
    (ComputableInPolyTime.unary_sub' ((ComputableInPolyTime.unary_eval ρ).comp hn)
      ((ComputableInPolyTime.unary_eval T).comp hn)) (ComputableInPolyTime.const [])
    (ComputableInPolyTime.snd _ _)

end Emulation

/-! ### Private coins versus public coins -/

open IPGame Emulation

private theorem le_two_pow_sub {x r ρ : ℕ} (h : x * 2 ^ r ≤ 2 ^ ρ) : x ≤ 2 ^ (ρ - r) := by
  rcases le_or_gt r ρ with hr | hr
  · rw [← Nat.sub_add_cancel hr, pow_add] at h
    exact Nat.le_of_mul_le_mul_right h (Nat.two_pow_pos r)
  · have hlt : 2 ^ ρ < 2 ^ r := Nat.pow_lt_pow_right one_lt_two hr
    have hx : x = 0 := by
      by_contra hx
      have : 2 ^ r ≤ x * 2 ^ r := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hx)
      omega
    rw [hx]
    exact Nat.zero_le _

private theorem two_pow_sub_le {N r ρ : ℕ} (h : 2 ^ r * 2 ^ ρ ≤ 3 ^ r * N) :
    2 ^ (ρ - r) ≤ N := by
  have h3 : 3 ^ r ≤ 2 ^ r * 2 ^ r := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) r
  rcases le_or_gt r ρ with hr | hr
  · have : 2 ^ r * (2 ^ r * 2 ^ (ρ - r)) ≤ 2 ^ r * (2 ^ r * N) := by
      calc 2 ^ r * (2 ^ r * 2 ^ (ρ - r)) = 2 ^ r * 2 ^ ρ := by
            rw [← pow_add, Nat.add_sub_cancel' hr]
        _ ≤ 3 ^ r * N := h
        _ ≤ 2 ^ r * 2 ^ r * N := Nat.mul_le_mul_right _ h3
        _ = 2 ^ r * (2 ^ r * N) := Nat.mul_assoc _ _ _
    exact Nat.le_of_mul_le_mul_left (Nat.le_of_mul_le_mul_left this (Nat.two_pow_pos r))
      (Nat.two_pow_pos r)
  · rw [Nat.sub_eq_zero_of_le hr.le, pow_zero]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · rw [hN, mul_zero] at h
      have := Nat.mul_pos (Nat.two_pow_pos r) (Nat.two_pow_pos ρ)
      omega
    · exact hN

/-- `D r ^ d 2 ^ r ≤ 3 ^ r` for all large `r`. -/
private theorem eventually_mul_pow_mul_two_pow_le (D d : ℕ) :
    ∀ᶠ r : ℕ in atTop, D * r ^ d * 2 ^ r ≤ 3 ^ r := by
  filter_upwards [Nat.eventually_mul_pow_le_pow_div D d 2 one_lt_two two_pos] with r hr
  have h89 : (2 ^ (r + r / 2)) ^ 2 ≤ (3 ^ r) ^ 2 := by
    calc (2 ^ (r + r / 2)) ^ 2 = 2 ^ (2 * r + 2 * (r / 2)) := by rw [← pow_mul]; ring_nf
      _ ≤ 2 ^ (3 * r) := Nat.pow_le_pow_right two_pos (by omega)
      _ = 8 ^ r := by rw [pow_mul]; norm_num
      _ ≤ 9 ^ r := Nat.pow_le_pow_left (by norm_num) r
      _ = (3 ^ r) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h89' : 2 ^ (r + r / 2) ≤ 3 ^ r := (Nat.pow_le_pow_iff_left two_ne_zero).1 h89
  calc D * r ^ d * 2 ^ r ≤ 2 ^ (r / 2) * 2 ^ r := Nat.mul_le_mul_right _ hr
    _ = 2 ^ (r + r / 2) := by rw [← pow_add, Nat.add_comm]
    _ ≤ 3 ^ r := h89'

/-- **Private coins versus public coins** [Goldwasser and Sipser][GoldwasserSipser1986],
[Arora and Barak, Theorem 8.8][AroraBarak07]: a problem with a
polynomial-time private-coin game verifier of pattern `π` has a polynomial-time public-coin game
verifier in which every verifier move becomes an Arthur move followed by a Merlin move, followed
by one more Arthur move and Merlin move. -/
theorem IPGameClass_subset_AMGameClass {enc : α ↪ List Bool} (π : List IPMove) :
    IPGameClass enc π ⊆ AMGameClass enc (pattern (π ++ [.verifier])) := by
  rintro A ⟨G₀, ρ₀, msg₀, dec₀, hG₀, hmsg₀, hdec₀, hA⟩
  -- the constant number of verifier moves of the emulated shape
  obtain ⟨c, hc⟩ : ∃ c, (G₀.map Prod.fst).count .verifier + 1 = c := ⟨_, rfl⟩
  have hc0 : 0 < c := by omega
  -- the size of the game
  obtain ⟨W, hW⟩ : ∃ W : Polynomial ℕ,
      W = AMGame.transcriptLengthPoly (G₀.map fun x => (x.1.toAM, x.2)) + ρ₀ + 1 := ⟨_, rfl⟩
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.1
    (eventually_mul_pow_mul_two_pow_le (6 * (288 * c ^ 2) ^ c) (4 * c))
  -- `r = A w` copies and `b = r w` bits of claims, for the game size `w`
  obtain ⟨R, hR⟩ : ∃ R : Polynomial ℕ, R = Polynomial.C (max A₀ 1) * W := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Polynomial ℕ, B = R * W := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Polynomial ℕ, Z = 2 * (B + 6 * Polynomial.C c * (B + 1)) := ⟨_, rfl⟩
  have hGfst : (repeatShapePoly R G₀).map Prod.fst = G₀.map Prod.fst := by
    simp [repeatShapePoly]
  refine ⟨shapePoly B Z (repeatShapePoly R G₀ ++ [(.verifier, R * ρ₀)]),
    amVerifier enc (repeatShapePoly R G₀) (R * ρ₀) B Z R (repeatVerifierMsg enc G₀ R ρ₀ msg₀)
      (repeatVerifierDec enc G₀ R ρ₀ dec₀), ?_,
    computableInPolyTime_amVerifier _ _ _ _ _ (computableInPolyTime_repeatVerifierMsg G₀ R ρ₀ hmsg₀)
      (computableInPolyTime_repeatVerifierDec G₀ R ρ₀ hdec₀), ?_⟩
  · rw [map_fst_shapePoly, List.map_append, hGfst, hG₀]
    simp only [List.map_cons, List.map_nil]
  rw [isAMGameVerifier_iff_value]
  intro a
  obtain ⟨h1, h2⟩ := hA a
  simp only [amVerifier, evalShape_shapePoly]
  rw [hGfst, hc]
  have hN := countFrom_revealPayoff_eq_countAt enc (repeatShapePoly R G₀) (R * ρ₀)
    (repeatVerifierMsg enc G₀ R ρ₀ msg₀) (repeatVerifierDec enc G₀ R ρ₀ dec₀) a
  rw [countAt_repeat] at hN
  generalize countAt enc G₀ ρ₀ msg₀ dec₀ a = N₀ at hN h1 h2
  generalize (enc a).length = n at hN h1 h2 ⊢
  -- the evaluated parameters
  have hc' : verifierMoves (evalShape (repeatShapePoly R G₀ ++ [(.verifier, R * ρ₀)]) n) = c := by
    rw [verifierMoves_evalShape, List.map_append, hGfst, ← hc]
    simp
  have hRn : R.eval n = max A₀ 1 * W.eval n := by simp [hR]
  have hBn : B.eval n = R.eval n * W.eval n := by simp [hB]
  have hZn : Z.eval n = 2 * (B.eval n + 6 * c * (B.eval n + 1)) := by simp [hZ]
  have hWn : W.eval n = transcriptLength (evalShape G₀ n) + ρ₀.eval n + 1 := by
    simp only [hW, Polynomial.eval_add, Polynomial.eval_one, ← AMGame.transcriptLength_evalShape,
      ← toAM_evalShape, transcriptLength_toAM]
  have hκ : (R * ρ₀).eval n - R.eval n ≤ B.eval n := by
    rw [Polynomial.eval_mul, hBn]
    exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_left _ (by omega))
  have hg : verifierBits (evalShape (repeatShapePoly R G₀ ++ [(.verifier, R * ρ₀)]) n) ≤
      B.eval n := by
    rw [evalShape_append, verifierBits_append, evalShape_repeatShapePoly, verifierBits_repeatShape,
      evalShape_cons, evalShape_nil, verifierBits_verifier, Polynomial.eval_mul, hBn]
    have := verifierBits_le_transcriptLength (evalShape G₀ n)
    have hnil : verifierBits [] = 0 := rfl
    rw [hnil, Nat.add_zero, ← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by omega)
  -- the gap beats the soundness factor
  have hgap : 6 * (72 * c ^ 2 * (B.eval n + 1) ^ 2) ^ c * 2 ^ R.eval n ≤ 3 ^ R.eval n := by
    have hw1 : 1 ≤ W.eval n := by omega
    have hr : W.eval n ≤ R.eval n ∧ A₀ ≤ R.eval n ∧ 1 ≤ R.eval n := by
      rw [hRn]
      refine ⟨Nat.le_mul_of_pos_left _ (by omega), ?_, ?_⟩
      · exact (le_max_left A₀ 1).trans (Nat.le_mul_of_pos_right _ hw1)
      · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    have hb : B.eval n + 1 ≤ 2 * R.eval n ^ 2 := by
      rw [hBn]
      have : R.eval n * W.eval n ≤ R.eval n * R.eval n := Nat.mul_le_mul_left _ hr.1
      have : 1 ≤ R.eval n * R.eval n := Nat.mul_le_mul hr.2.2 hr.2.2
      nlinarith
    have hM : 72 * c ^ 2 * (B.eval n + 1) ^ 2 ≤ 288 * c ^ 2 * R.eval n ^ 4 := by
      have := Nat.pow_le_pow_left hb 2
      nlinarith
    calc 6 * (72 * c ^ 2 * (B.eval n + 1) ^ 2) ^ c * 2 ^ R.eval n
        ≤ 6 * (288 * c ^ 2 * R.eval n ^ 4) ^ c * 2 ^ R.eval n := by gcongr
      _ = 6 * (288 * c ^ 2) ^ c * R.eval n ^ (4 * c) * 2 ^ R.eval n := by
          rw [mul_pow, ← pow_mul]; ring
      _ ≤ 3 ^ R.eval n := hA₀ _ hr.2.1
  rw [← hc']
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · refine two_le_three_mul_value _ _ _ _ (by omega) (by rw [hc', hZn]) hg _ hκ ?_
    rw [hN]
    refine two_pow_sub_le ?_
    calc 2 ^ R.eval n * 2 ^ (R * ρ₀).eval n = (2 * 2 ^ ρ₀.eval n) ^ R.eval n := by
          rw [Polynomial.eval_mul, mul_pow, pow_mul']
      _ ≤ (3 * N₀) ^ R.eval n := Nat.pow_le_pow_left (h1 ha) _
      _ = 3 ^ R.eval n * N₀ ^ R.eval n := mul_pow _ _ _
  · refine three_mul_value_le_one _ _ _ _ (by omega) _ hκ ?_
    rw [hN, hc']
    refine le_two_pow_sub ?_
    calc 6 * (72 * c ^ 2 * (B.eval n + 1) ^ 2) ^ c * N₀ ^ R.eval n * 2 ^ R.eval n
        = 6 * (72 * c ^ 2 * (B.eval n + 1) ^ 2) ^ c * 2 ^ R.eval n * N₀ ^ R.eval n := by ring
      _ ≤ 3 ^ R.eval n * N₀ ^ R.eval n := Nat.mul_le_mul_right _ hgap
      _ = (3 * N₀) ^ R.eval n := (mul_pow _ _ _).symm
      _ ≤ (2 ^ ρ₀.eval n) ^ R.eval n := Nat.pow_le_pow_left (h2 ha) _
      _ = 2 ^ (R * ρ₀).eval n := by rw [Polynomial.eval_mul, ← pow_mul, mul_comm]

/-- **Private coins versus public coins** in terms of `AM`: every fixed-pattern private-coin game
is in `AM`. -/
theorem IPGameClass_subset_AM {enc : α ↪ List Bool} (π : List IPMove) :
    IPGameClass enc π ⊆ AM enc :=
  (IPGameClass_subset_AMGameClass π).trans (AMGameClass_subset_AM _)

/-- **`IP[k] ⊆ AM[k + 2]`** [Goldwasser and Sipser][GoldwasserSipser1986], [Arora and
Barak, Theorem 8.8][AroraBarak07], for every constant `k`. The proof
goes through round collapse [Babai and Moran][BabaiMoran1988]: with adjacent Merlin moves merged,
the pattern of the emulation has `k + 2` moves for an even `k` and `k + 3` moves for an odd `k`. -/
theorem IPk_subset_AMk {enc : α ↪ List Bool} (k : ℕ) : IPk enc k ⊆ AMk enc (k + 2) := by
  rw [AMk_eq_AM (by omega)]
  exact IPGameClass_subset_AM _

/-- **`IP[k] = AM`** for every constant `k ≥ 2` [Goldwasser and Sipser][GoldwasserSipser1986],
[Babai and Moran][BabaiMoran1988]. -/
theorem IPk_eq_AM {enc : α ↪ List Bool} {k : ℕ} (hk : 2 ≤ k) : IPk enc k = AM enc :=
  le_antisymm (IPGameClass_subset_AM _) (by rw [← AMk_eq_AM hk]; exact AMk_subset_IPk k)

/-- **Private-coin games are in `NP/poly`**: a problem with a polynomial-time private-coin game
verifier of any fixed pattern is in `AM` (`Cslib.Complexity.IPGameClass_subset_AM`), which is
contained in `NP/poly` (`Cslib.Complexity.AM_subset_NPPoly`). In particular `IP[k] ⊆ NP/poly`. -/
theorem IPGameClass_subset_NPPoly {enc : α ↪ List Bool} (π : List IPMove) :
    IPGameClass enc π ⊆ NPPoly enc :=
  (IPGameClass_subset_AM π).trans AM_subset_NPPoly

end Cslib.Complexity
