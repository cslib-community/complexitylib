/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Hybrids
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.Product.Split
import CslibFrontier.Tactic.PMFSwap

/-!
# Re-indexing the random oracles of `FO-notbot`

The eager game with decoupled implicit-rejection keys (`Scheme.eagerFbGame`) and the eager coupled
game (`Scheme.eagerCoupledGame`) have the same output distribution. For fixed `G`, `pk` and `sk`,
the tables `H : Bool × M × CT → K` and `Hfb : CT → K` are read off independent tables
`Hq : CT → K`, `Hraw : Bool × M × CT → K` and `Hfb' : CT → K`:

* `H(false, m, c) = Hq c` when `c = Enc(pk, m; G(m))` and `Dec(sk, c) = some m`, and
  `H(x) = Hraw x` otherwise;
* `Hfb c = Hq c` when `decT` rejects `c`, and `Hfb c = Hfb' c` otherwise.

Since `Dec` is deterministic, each entry `Hq c` is read at most once, so the read-off tables
again have independent coordinates with the original `sampleKey` law (`pi_map_comp_injective`).
Under this re-indexing every
decapsulation query `c ≠ c*` is answered by `Hq c`, whether `decT` accepts `c` or not. This is the
re-randomization step of the proof of the IND-CCA theorem for `U-notbot` in
[HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated 2 November 2021, §3.2.2),
with the plaintext-checking oracle replaced by the re-encryption and decryption test of `T`.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerCoupledGame_eq_eagerFbGame`: the two eager
  games have the same output distribution.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021).
-/

public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability
open Probability.PMF
open scoped ENNReal NNReal

variable {PK SK M R CT K : Type}

/-- An independent product over a sum of index types is the product of the two independent
products over the summands. -/
private theorem bind_pi_sum {I J γ β : Type} [Fintype I] [Fintype J] [Finite γ] (μ : PMF γ)
    (F : (I → γ) → (J → γ) → PMF β) :
    (pi fun _ : I ⊕ J => μ).bind (fun f => F (fun i => f (Sum.inl i)) fun j => f (Sum.inr j)) =
      (pi fun _ : I => μ).bind fun a => (pi fun _ : J => μ).bind fun b => F a b := by
  have hsplit :
      (pi fun _ : I ⊕ J => μ).map (Equiv.sumArrowEquivProdArrow I J γ) =
        (pi fun _ : I => μ).bind fun a => (pi fun _ : J => μ).map (a, ·) := by
    ext ⟨a, b⟩
    rw [map_equiv_apply, bind_map_prodMk_apply, pi_apply, pi_apply, pi_apply,
      Fintype.prod_sum_type]
    rfl
  have h := congrArg (fun p => p.bind fun ab => F ab.1 ab.2) hsplit
  simp only [PMF.bind_bind, PMF.map, PMF.pure_bind, Function.comp_def] at h
  exact h

namespace Scheme

variable [DecidableEq M] [DecidableEq CT]

/-- Re-indexed implicit-rejection table: `Hq c` when `decT` rejects `c`, and `Hfb' c` otherwise. -/
private def coupledFb (S : Scheme PK SK M R CT K) (G : M → R) (Hq Hfb' : CT → K) (pk : PK)
    (sk : SK) (c : CT) : K :=
  if decT S.pke G pk sk c = none then Hq c else Hfb' c

/-- The coordinate of the independent tables `(Hq, Hraw, Hfb')` read by each coordinate of the
re-indexed tables `(H, Hfb)`. -/
private def readIndex (S : Scheme PK SK M R CT K) (G : M → R) (pk : PK) (sk : SK) :
    (Bool × M × CT) ⊕ CT → CT ⊕ ((Bool × M × CT) ⊕ CT)
  | .inl (false, m, c) =>
    if S.pke.encDet pk m (G m) = c ∧ S.pke.dec sk c = some m then .inl c
    else .inr (.inl (false, m, c))
  | .inl (true, m, c) => .inr (.inl (true, m, c))
  | .inr c => if decT S.pke G pk sk c = none then .inl c else .inr (.inr c)

/-- Each coordinate of `(Hq, Hraw, Hfb')` is read at most once: `Hq c` is read by
`H(false, m, c)` only for the unique `m` with `Dec(sk, c) = some m`, and by `Hfb c` only when `decT`
rejects `c`, in which case no such `H(false, m, c)` reads it. -/
private theorem readIndex_injective (S : Scheme PK SK M R CT K) (G : M → R) (pk : PK) (sk : SK) :
    Function.Injective (S.readIndex G pk sk) := by
  rintro (⟨_ | _, m, c⟩ | c) (⟨_ | _, m', c'⟩ | c') h <;>
    simp only [readIndex] at h <;> (try split_ifs at h) <;>
    simp_all [decT, encT]

/-- Reading the independent tables `(Hq, Hraw, Hfb')` through `readIndex` gives independent tables
`(H, Hfb)`. -/
private theorem bind_pi_reindex [Fintype M] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (G : M → R) (pk : PK) (sk : SK) {β : Type}
    (F : (Bool × M × CT → K) → (CT → K) → PMF β) :
    ((pi fun _ : Bool × M × CT => ProbComp.eval S.sampleKey).bind fun H =>
      (pi fun _ : CT => ProbComp.eval S.sampleKey).bind fun Hfb => F H Hfb) =
    (pi fun _ : CT => ProbComp.eval S.sampleKey).bind fun Hq =>
      (pi fun _ : Bool × M × CT => ProbComp.eval S.sampleKey).bind fun Hraw =>
        (pi fun _ : CT => ProbComp.eval S.sampleKey).bind fun Hfb' =>
          F (S.coupledH G Hq Hraw pk sk) (S.coupledFb G Hq Hfb' pk sk) := by
  set μ := ProbComp.eval S.sampleKey
  have hR : ((pi fun _ : CT => μ).bind fun Hq =>
      (pi fun _ : Bool × M × CT => μ).bind fun Hraw =>
        (pi fun _ : CT => μ).bind fun Hfb' =>
          F (S.coupledH G Hq Hraw pk sk) (S.coupledFb G Hq Hfb' pk sk)) =
      (pi fun _ : CT ⊕ ((Bool × M × CT) ⊕ CT) => μ).bind fun f =>
        F (S.coupledH G (fun c => f (.inl c)) (fun x => f (.inr (.inl x))) pk sk)
          (S.coupledFb G (fun c => f (.inl c)) (fun c => f (.inr (.inr c))) pk sk) := by
    refine Eq.symm ((bind_pi_sum μ fun (Hq : CT → K) (g : (Bool × M × CT) ⊕ CT → K) =>
      F (S.coupledH G Hq (fun x => g (Sum.inl x)) pk sk)
        (S.coupledFb G Hq (fun c => g (Sum.inr c)) pk sk)).trans ?_)
    congr 1 with Hq : 1
    exact bind_pi_sum μ fun Hraw Hfb' =>
      F (S.coupledH G Hq Hraw pk sk) (S.coupledFb G Hq Hfb' pk sk)
  rw [hR, ← bind_pi_sum μ F,
    ← pi_map_comp_injective (fun _ : CT ⊕ ((Bool × M × CT) ⊕ CT) => μ)
      (S.readIndex_injective G pk sk),
    PMF.bind_map]
  congr 1 with f : 1
  simp only [Function.comp_apply]
  refine congrArg₂ F ?_ ?_
  · funext x
    rcases x with ⟨_ | _, m, c⟩
    · simp only [readIndex, coupledH]
      split_ifs <;> rfl
    · rfl
  · funext c
    simp only [readIndex, coupledFb]
    split_ifs <;> rfl

/-- Reading the independent tables `(Hq, Hraw)` through `coupledH` gives an independent table
`H`. -/
theorem bind_pi_coupledH [Fintype M] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (G : M → R) (pk : PK) (sk : SK) {β : Type}
    (F : (Bool × M × CT → K) → PMF β) :
    ((pi fun _ : Bool × M × CT => ProbComp.eval S.sampleKey).bind fun H => F H) =
    (pi fun _ : CT => ProbComp.eval S.sampleKey).bind fun Hq =>
      (pi fun _ : Bool × M × CT => ProbComp.eval S.sampleKey).bind fun Hraw =>
        F (S.coupledH G Hq Hraw pk sk) := by
  simpa only [PMF.bind_const] using S.bind_pi_reindex G pk sk (fun H _ => F H)

/-- Under the re-indexing, the oracle of `eagerFbGame` is the oracle of `eagerCoupledGame`. -/
private theorem eagerFbHandler_reindex (S : Scheme PK SK M R CT K) (G : M → R) (Hq Hfb' : CT → K)
    (Hraw : Bool × M × CT → K) (pk : PK) (sk : SK) (s : M) (cStar : CT) (q : ROQuery M CT) :
    S.eagerFbHandler G (S.coupledH G Hq Hraw pk sk) (S.coupledFb G Hq Hfb' pk sk)
        { sk := sk, pk := pk, fallback := s } cStar q =
      S.eagerCoupledHandler G Hq Hraw pk sk cStar q := by
  cases q with
  | G m => rfl
  | H x => rfl
  | decaps c =>
    simp only [eagerFbHandler, eagerCoupledHandler]
    by_cases hc : c = cStar
    · simp [hc]
    · simp only [hc, ↓reduceIte]
      cases hd : decT S.pke G pk sk c with
      | none => simp [coupledFb, hd]
      | some m' =>
        have henc := encT_of_decT_eq_some hd
        have hdec := dec_of_decT_eq_some hd
        simp only [encT] at henc
        simp [coupledH, henc, hdec]

/-- **Re-indexing the random oracles of `FO-notbot`**: the eager coupled game and the eager game
with decoupled implicit-rejection keys have the same output distribution. -/
theorem eagerCoupledGame_eq_eagerFbGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    S.eagerCoupledGame A b = S.eagerFbGame A b := by
  simp only [eagerCoupledGame, eagerFbGame, keyGenNotBot, encapsNotBot, encapsBot,
    Probability.PMF.monad_bind_eq_bind, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
    PMF.pure_bind]
  congr 1 with ⟨pk, sk⟩ : 1
  dsimp only
  symm
  calc _ = (ProbComp.eval S.sampleMsg).bind fun _ =>
        (pi fun _ : M => ProbComp.eval S.pke.sampleCoins).bind fun G =>
          (pi fun _ : CT => ProbComp.eval S.sampleKey).bind fun Hq =>
            (pi fun _ : Bool × M × CT => ProbComp.eval S.sampleKey).bind fun Hraw =>
              (pi fun _ : CT => ProbComp.eval S.sampleKey).bind fun _ =>
                (ProbComp.eval S.sampleMsg).bind fun mStar =>
                  (ProbComp.eval S.sampleKey).bind fun kRand =>
                    OracleComp.interpret
                      (S.eagerCoupledHandler G Hq Hraw pk sk (encT S.pke G pk mStar))
                      (A (pk, encT S.pke G pk mStar, if b = true then kRand else
                        S.coupledH G Hq Hraw pk sk (false, mStar, encT S.pke G pk mStar))) := by
        congr 1 with s : 1
        congr 1 with G : 1
        rw [bind_pi_reindex S G pk sk]
        congr 1 with Hq : 1
        congr 1 with Hraw : 1
        congr 1 with Hfb' : 1
        congr 1 with mStar : 1
        congr 1 with kRand : 1
        congr 1
        funext q
        exact S.eagerFbHandler_reindex G Hq Hfb' Hraw pk sk s _ q
    _ = _ := by simp only [PMF.bind_const]

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto
