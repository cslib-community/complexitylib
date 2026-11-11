/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Hybrids
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Languages.Probabilistic.UntilBad.TwoCost
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Probability.PMF.Event

/-!
# The challenge hop of the `FO-notbot` IND-CCA proof

The last hop of the ROM IND-CCA proof for `FO-notbot` ([HofheinzHoevelmannsKiltz2017], proof of
the §3.1 theorem for `T` combined with the proof of the §3.2.2 IND-CCA theorem for `U-notbot`)
bounds the distinguishing advantage of the keyless simulator game `Scheme.simGame` of
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Hybrids` by the IND-CPA advantage of
`Scheme.romCpaReduction`.

In `simGame b` the simulator starts with `G(m*) = r*` and `Hq(c*) = kq` already cached, and the
adversary receives `kq` (`b = false`) or an independent `kRand` (`b = true`). Both games are
compared with the run of the same simulator from empty caches, which is the run inside
`romCpaReduction`:

1. A preset cache entry is the same as a lazily programmed sampler point: the simulator run from
   the preset caches has the output law of the run from empty caches whose `G` sampler returns
   `r*` at `m*` and whose `Hq` sampler returns `kq` at `c*`.
2. The programmed and the unprogrammed simulators are identical until `G(m*)` or `Hq(c*)` is
   cached, for either input key.
3. In the unprogrammed run `Hq(c*)` is cached only after some cached coin `G(m)` re-encrypts `m`
   to `c*`, which by `γ`-spreadness has probability at most `(qG + qH) · 2^(-γ)`; caching `G(m*)`
   for a uniform `m*` has the probability bounded by
   `Scheme.avg_simHitProb_le_indCpaAdvantage_romCpaReduction`.

Each simulator game is within `Pr[G(m*) cached] + (qG + qH) 2^(-γ)` of the empty-cache run, so the
two bits are within twice that, giving `2 (Adv_CPA + (qG + qH)/|M|) + 2 (qG + qH) 2^(-γ)`.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.advantage_simGame_le`: the advantage between
  `simGame A false` and `simGame A true` is at most
  `2 Adv_CPA(romCpaReduction A m₀ m₁) + 2 (qG + qH)/|M| + 2 (qG + qH) 2^(-γ)` for some distinct
  messages `m₀ ≠ m₁`, when the message sampler is uniform and the PKE is `γ`-spread.

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

/-! ### Association lists with one programmed entry -/

section Ens

variable {α β : Type} [DecidableEq α]

/-- Drop every entry for `x` and append `(x, v)`: the list that a memoized cache would hold if
`(x, v)` had been stored before every other entry. -/
private def ens (x : α) (v : β) (L : List (α × β)) : List (α × β) :=
  L.filter (fun e => e.1 != x) ++ [(x, v)]

private theorem lookup_filter_ne (x y : α) (L : List (α × β)) (hy : y ≠ x) :
    (L.filter (fun e => e.1 != x)).lookup y = L.lookup y := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨a, b⟩ := e
    by_cases ha : a = x
    · subst ha
      simp [List.lookup_cons, ih, beq_eq_false_iff_ne.mpr hy]
    · by_cases hya : y = a
      · subst hya
        simp [ha]
      · simp [List.lookup_cons, ha, ih, beq_eq_false_iff_ne.mpr hya]

private theorem lookup_filter_self (x : α) (L : List (α × β)) :
    (L.filter (fun e => e.1 != x)).lookup x = none := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨a, b⟩ := e
    by_cases ha : a = x
    · subst ha
      simp [ih]
    · simp [List.lookup_cons, ha, ih, beq_eq_false_iff_ne.mpr (Ne.symm ha)]

private theorem lookup_ens (x : α) (v : β) (L : List (α × β)) (y : α) :
    (ens x v L).lookup y = if y = x then some v else L.lookup y := by
  unfold ens
  by_cases hy : y = x
  · subst hy
    simp [List.lookup_append, lookup_filter_self]
  · simp only [List.lookup_append, lookup_filter_ne x y L hy, hy, ↓reduceIte]
    cases L.lookup y <;> simp [hy]

private theorem ens_cons_ne (x : α) (v : β) (L : List (α × β)) (y : α) (w : β) (hy : y ≠ x) :
    ens x v ((y, w) :: L) = (y, w) :: ens x v L := by
  simp [ens, hy]

private theorem ens_cons_self (x : α) (v w : β) (L : List (α × β)) :
    ens x v ((x, w) :: L) = ens x v L := by
  simp [ens]

/-- Memoizing with `x` programmed to `v`, then moving `(x, v)` to the end, is memoizing on the list
in which `(x, v)` is already stored. -/
private theorem memoize_ens (d : PMF β) (x : α) (v : β) (y : α) (L : List (α × β))
    (hL : L.lookup x = none ∨ L.lookup x = some v) :
    (memoize (fun _ => if y = x then PMF.pure v else d) y L).map
        (fun p => (p.1, ens x v p.2)) =
      memoize (fun _ => d) y (ens x v L) := by
  by_cases hy : y = x
  · subst hy
    rw [memoize_of_some (fun _ => d) y (ens y v L) v (by rw [lookup_ens]; simp)]
    rcases hL with hL | hL
    · rw [memoize_of_none _ _ _ hL]
      simp [ens_cons_self, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    · rw [memoize_of_some _ _ _ v hL]
      simp [PMF.monad_pure_eq_pure]
  · have hlook : (ens x v L).lookup y = L.lookup y := by rw [lookup_ens]; simp [hy]
    cases h : L.lookup y with
    | some w =>
      rw [memoize_of_some _ _ _ w h, memoize_of_some _ _ _ w (hlook.trans h)]
      simp [PMF.monad_pure_eq_pure]
    | none =>
      rw [memoize_of_none _ _ _ h, memoize_of_none _ _ _ (hlook.trans h)]
      simp [hy, ens_cons_ne _ _ _ _ _ hy, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.map_bind]

private theorem isSome_lookup_of_suffix {L₁ L₂ : List (α × β)} (h : L₁ <:+ L₂) (x : α)
    (hx : (L₁.lookup x).isSome) : (L₂.lookup x).isSome := by
  by_contra hnone
  exact Option.not_isSome_iff_eq_none.mpr
    (h.lookup_eq_none (Option.not_isSome_iff_eq_none.mp hnone)) hx

end Ens

namespace Scheme

variable [DecidableEq M] [DecidableEq CT]

/-- The keyless simulator `simHandler pk cStar`, evaluated to `PMF`, run on `A (pk, cStar, k)`
from the state `st`. -/
private noncomputable def simRun (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    (pk : PK) (cStar : CT) (k : K) (st : SimState M R CT K) : PMF (Bool × SimState M R CT K) :=
  (OracleComp.interpret (m := StateT (SimState M R CT K) PMF)
    (fun q s => ProbComp.eval (S.simHandler pk cStar q s)) (A (pk, cStar, k))).run st

omit [DecidableEq CT] in
/-- A supported transition of `simHashG` records its answer, keeps the old `gCache` entries and
does not touch `hqCache`. -/
private theorem simHashG_support {sc : ProbComp R} {m : M} {st : SimState M R CT K}
    {z : R × SimState M R CT K} (hz : z ∈ (ProbComp.eval (simHashG sc m st)).support) :
    (m, z.1) ∈ z.2.gCache ∧ st.gCache ⊆ z.2.gCache ∧ z.2.hqCache = st.hqCache := by
  rw [simHashG, RandomOracle.eval_zoomStateT_memoize, PMF.mem_support_map_iff] at hz
  obtain ⟨⟨r, c'⟩, hc', rfl⟩ := hz
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hc' with ⟨hl, hnext⟩ | ⟨-, -, hnext⟩
  · dsimp only at hl hnext ⊢
    subst hnext
    obtain ⟨l₁, l₂, hlist, -⟩ := List.lookup_eq_some_iff.mp hl
    exact ⟨by simp [hlist], List.Subset.refl _, rfl⟩
  · dsimp only at hnext ⊢
    subst hnext
    exact ⟨by simp, List.subset_cons_self _ _, rfl⟩

omit [DecidableEq M] in
/-- A supported transition of `simHashHq c` keeps `gCache` and only adds the key `c` to
`hqCache`. -/
private theorem simHashHq_support {sk : ProbComp K} {c cStar : CT} {st : SimState M R CT K}
    {z : K × SimState M R CT K} (hz : z ∈ (ProbComp.eval (simHashHq sk c st)).support) :
    z.2.gCache = st.gCache ∧
      ((z.2.hqCache.lookup cStar).isSome → c = cStar ∨ (st.hqCache.lookup cStar).isSome) := by
  rw [simHashHq, RandomOracle.eval_zoomStateT_memoize, PMF.mem_support_map_iff] at hz
  obtain ⟨⟨r, c'⟩, hc', rfl⟩ := hz
  refine ⟨rfl, fun h => ?_⟩
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hc' with ⟨-, hnext⟩ | ⟨-, -, hnext⟩
  · dsimp only at hnext h
    exact Or.inr (hnext ▸ h)
  · dsimp only at hnext h
    rw [hnext, List.lookup_isSome_iff] at h
    obtain ⟨p, hp, hpk⟩ := h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inl (eq_of_beq hpk).symm
    · exact Or.inr (List.lookup_isSome_iff.mpr ⟨p, hp, hpk⟩)

/-- A supported transition of `simHashHRaw` keeps `gCache` and `hqCache`. -/
private theorem simHashHRaw_support {sk : ProbComp K} {x : Bool × M × CT}
    {st : SimState M R CT K} {z : K × SimState M R CT K}
    (hz : z ∈ (ProbComp.eval (simHashHRaw sk x st)).support) :
    z.2.gCache = st.gCache ∧ z.2.hqCache = st.hqCache := by
  rw [simHashHRaw, RandomOracle.eval_zoomStateT_memoize, PMF.mem_support_map_iff] at hz
  obtain ⟨⟨_, _⟩, -, rfl⟩ := hz
  exact ⟨rfl, rfl⟩

/-- A supported transition of `simHandler` keeps the old `gCache` entries, and records `cStar` in
`hqCache` only if `cStar` already was there or re-encrypts an entry of the new `gCache`. -/
private theorem simHandler_step (S : Scheme PK SK M R CT K) (pk : PK) (cStar : CT)
    (q : ROQuery M CT) (st : SimState M R CT K) (res : ROResp R K q) (st' : SimState M R CT K)
    (hmem : (res, st') ∈ (ProbComp.eval (S.simHandler pk cStar q st)).support) :
    st.gCache ⊆ st'.gCache ∧
      ((st'.hqCache.lookup cStar).isSome → (st.hqCache.lookup cStar).isSome ∨
        ∃ p ∈ st'.gCache, S.pke.encDet pk p.1 p.2 = cStar) := by
  cases q with
  | G m =>
    obtain ⟨-, hsub, hhq⟩ := simHashG_support (z := (res, st')) hmem
    exact ⟨hsub, fun h => Or.inl (hhq ▸ h)⟩
  | H x =>
    rcases x with ⟨isFb, m, c⟩
    cases isFb
    · dsimp only [simHandler, simHashH] at hmem
      change (res, st') ∈ (ProbComp.eval (simHashG S.pke.sampleCoins m st >>= fun z =>
        (if S.pke.encDet pk m z.fst = c then
          simHashHq S.sampleKey c
        else
          simHashHRaw S.sampleKey (false, m, c)) z.snd)).support at hmem
      rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hmem
      obtain ⟨z, hz, hmem₂⟩ := hmem
      obtain ⟨hmz, hsub, hhq⟩ := simHashG_support hz
      by_cases henc : S.pke.encDet pk m z.fst = c
      · simp only [henc, ↓reduceIte] at hmem₂
        obtain ⟨hg, hq'⟩ := simHashHq_support (cStar := cStar) (z := (res, st')) hmem₂
        refine ⟨hg ▸ hsub, fun h => ?_⟩
        rcases hq' h with rfl | h'
        · exact Or.inr ⟨(m, z.1), hg ▸ hmz, henc⟩
        · exact Or.inl (hhq ▸ h')
      · simp only [henc, ↓reduceIte] at hmem₂
        obtain ⟨hg, hq'⟩ := simHashHRaw_support (z := (res, st')) hmem₂
        exact ⟨hg ▸ hsub, fun h => Or.inl (hhq ▸ hq' ▸ h)⟩
    · dsimp only [simHandler, simHashH] at hmem
      obtain ⟨hg, hq'⟩ := simHashHRaw_support (z := (res, st')) hmem
      exact ⟨hg ▸ List.Subset.refl _, fun h => Or.inl (hq' ▸ h)⟩
  | decaps c =>
    dsimp only [simHandler] at hmem
    by_cases hc : c = cStar
    · simp only [hc, ↓reduceIte] at hmem
      change (res, st') ∈ (ProbComp.eval (pure (none, st))).support at hmem
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨-, rfl⟩
      exact ⟨List.Subset.refl _, Or.inl⟩
    · simp only [hc, ↓reduceIte] at hmem
      change (res, st') ∈ (ProbComp.eval (simHashHq S.sampleKey c st >>= fun a =>
        pure (some a.fst, a.snd))).support at hmem
      rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hmem
      obtain ⟨z, hz, hmem₂⟩ := hmem
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem₂
      rcases hmem₂ with ⟨-, rfl⟩
      obtain ⟨hg, hq'⟩ := simHashHq_support (cStar := cStar) hz
      exact ⟨hg ▸ List.Subset.refl _, fun h => Or.inl ((hq' h).resolve_left hc)⟩

omit [DecidableEq M] [DecidableEq CT] in
/-- A distribution whose supported states all keep the `gCache` of a state `st` outside a
`gCache` event reaches that event with probability zero. -/
private theorem toOuterMeasure_gCache_eq_zero {α : Type} (p : PMF (α × SimState M R CT K))
    (st : SimState M R CT K) (P : List (M × R) → Prop) (hst : ¬P st.gCache)
    (h : ∀ x ∈ p.support, x.2.gCache = st.gCache) : p.toOuterMeasure {x | P x.2.gCache} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro x hx hP
  exact hst (h x hx ▸ hP)

omit [DecidableEq CT] in
/-- From a state where no `gCache` entry re-encrypts to `cStar`, one `simHashG` call creates such
an entry with probability at most `2^(-γ)`. -/
private theorem simHashG_reEnc_le (S : Scheme PK SK M R CT K) {γ : ℝ} (hγ : S.pke.GammaSpread γ)
    {pk : PK} {sk : SK} (hpk : (pk, sk) ∈ (ProbComp.eval S.pke.keyGen).support) (m : M)
    (cStar : CT) (st : SimState M R CT K)
    (hst : ¬∃ p ∈ st.gCache, S.pke.encDet pk p.1 p.2 = cStar) :
    (ProbComp.eval (simHashG S.pke.sampleCoins m st)).toOuterMeasure
        {z | ∃ p ∈ z.2.gCache, S.pke.encDet pk p.1 p.2 = cStar} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-γ)) := by
  rw [simHashG, RandomOracle.eval_zoomStateT_memoize, PMF.toOuterMeasure_map_apply]
  cases h : st.gCache.lookup m with
  | some v =>
    simp only [memoize, h, PMF.monad_pure_eq_pure, PMF.toOuterMeasure_pure_apply]
    split_ifs with hmem
    · exact absurd hmem (by simpa using hst)
    · exact bot_le
  | none =>
    simp only [memoize, h, PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind]
    change ((ProbComp.eval S.pke.sampleCoins).map
      fun v => (v, (m, v) :: st.gCache)).toOuterMeasure _ ≤ _
    rw [PMF.toOuterMeasure_map_apply]
    refine (PMF.toOuterMeasure_mono _ fun r hr => ?_).trans
      ((ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _) (by positivity)).mpr
        (hγ pk sk hpk m cStar))
    have hr := hr.1
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, List.mem_cons] at hr
    obtain ⟨p, hp | hp, he⟩ := hr
    · subst hp; exact he
    · exact absurd ⟨p, hp, he⟩ hst

/-- From a state where no `gCache` entry re-encrypts to `cStar`, one `simHandler` call creates such
an entry with probability at most `2^(-γ)` for each `G` or `H` query it makes. -/
private theorem simHandler_reEnc_le (S : Scheme PK SK M R CT K) {γ : ℝ}
    (hγ : S.pke.GammaSpread γ) {pk : PK} {sk : SK}
    (hpk : (pk, sk) ∈ (ProbComp.eval S.pke.keyGen).support) (cStar : CT) (q : ROQuery M CT)
    (st : SimState M R CT K) (hst : ¬∃ p ∈ st.gCache, S.pke.encDet pk p.1 p.2 = cStar) :
    (ProbComp.eval (S.simHandler pk cStar q st)).toOuterMeasure
        {x | ∃ p ∈ x.2.gCache, S.pke.encDet pk p.1 p.2 = cStar} ≤
      (q.gCost : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ)) +
        (q.hCost : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ)) := by
  cases q with
  | G m =>
    change (ProbComp.eval (simHashG S.pke.sampleCoins m st)).toOuterMeasure _ ≤ _
    simpa only [ROQuery.gCost, ROQuery.hCost, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul,
      add_zero] using S.simHashG_reEnc_le hγ hpk m cStar st hst
  | H x =>
    rcases x with ⟨isFb, m, c⟩
    simp only [ROQuery.gCost, ROQuery.hCost, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul,
      zero_add]
    cases isFb
    · dsimp only [simHandler, simHashH]
      change (ProbComp.eval (simHashG S.pke.sampleCoins m st >>= fun z =>
        (if S.pke.encDet pk m z.fst = c then
          simHashHq S.sampleKey c
        else
          simHashHRaw S.sampleKey (false, m, c)) z.snd)).toOuterMeasure _ ≤ _
      rw [ProbComp.eval_bind]
      refine (Probability.PMF.toOuterMeasure_bind_le_add _ _
        {z | ∃ p ∈ z.2.gCache, S.pke.encDet pk p.1 p.2 = cStar} _ 0 fun z _ hz => ?_).trans
        (by simpa only [add_zero] using S.simHashG_reEnc_le hγ hpk m cStar st hst)
      refine (toOuterMeasure_gCache_eq_zero _ z.2
        (fun g => ∃ p ∈ g, S.pke.encDet pk p.1 p.2 = cStar) hz fun y hy => ?_).le
      by_cases henc : S.pke.encDet pk m z.fst = c
      · simp only [henc, ↓reduceIte] at hy
        exact (simHashHq_support (cStar := cStar) hy).1
      · simp only [henc, ↓reduceIte] at hy
        exact (simHashHRaw_support hy).1
    · dsimp only [simHandler, simHashH]
      exact (toOuterMeasure_gCache_eq_zero _ st
        (fun g => ∃ p ∈ g, S.pke.encDet pk p.1 p.2 = cStar) hst fun y hy =>
        (simHashHRaw_support hy).1).trans_le zero_le
  | decaps c =>
    simp only [ROQuery.gCost, ROQuery.hCost, Nat.cast_zero, zero_mul, add_zero]
    refine (toOuterMeasure_gCache_eq_zero _ st
      (fun g => ∃ p ∈ g, S.pke.encDet pk p.1 p.2 = cStar) hst fun y hy => ?_).le
    dsimp only [simHandler] at hy
    exact gCache_eq_of_mem_support_decaps _ _ _ _ _ hy

/-- **Bad-event split**: from the empty state, the simulator records `mStar` in
`gCache` or `cStar` in `hqCache` with probability at most that of recording `mStar`, plus
`(qG + qH) · 2^(-γ)` for a fresh coin re-encrypting to `cStar`. -/
private theorem simRun_bad_le (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    {qG qH : ℕ} (hq : ROQueryBounds A qG qH) {γ : ℝ} (hγ : S.pke.GammaSpread γ)
    {pk : PK} {sk : SK} (hpk : (pk, sk) ∈ (ProbComp.eval S.pke.keyGen).support)
    (mStar : M) (cStar : CT) (k : K) :
    (S.simRun A pk cStar k {}).toOuterMeasure
        {x | (x.2.gCache.lookup mStar).isSome ∨ (x.2.hqCache.lookup cStar).isSome} ≤
      (S.simRun A pk cStar k {}).toOuterMeasure {x | (x.2.gCache.lookup mStar).isSome} +
        ((qG + qH : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ)) := by
  set ε := ENNReal.ofReal ((2 : ℝ) ^ (-γ))
  set P := S.simRun A pk cStar k {}
  have hinv : ∀ x ∈ P.support, (x.2.hqCache.lookup cStar).isSome →
      ∃ p ∈ x.2.gCache, S.pke.encDet pk p.1 p.2 = cStar := by
    intro x hx
    refine OracleComp.run_interpret_invariant _ (fun st : SimState M R CT K =>
        (st.hqCache.lookup cStar).isSome → ∃ p ∈ st.gCache, S.pke.encDet pk p.1 p.2 = cStar)
      (fun q s hs a s' h hq' => ?_) _ _ (by simp) x.1 x.2 hx
    obtain ⟨hsub, hhq⟩ := S.simHandler_step pk cStar q s a s' h
    rcases hhq hq' with h₁ | h₁
    · obtain ⟨p, hp, he⟩ := hs h₁
      exact ⟨p, hsub hp, he⟩
    · exact h₁
  have hF : P.toOuterMeasure {x | ∃ p ∈ x.2.gCache, S.pke.encDet pk p.1 p.2 = cStar} ≤
      ((qG + qH : ℕ) : ℝ≥0∞) * ε := by
    refine (Cslib.OracleComp.toOuterMeasure_bad_le_two
      (bad := fun st : SimState M R CT K => ∃ p ∈ st.gCache, S.pke.encDet pk p.1 p.2 = cStar)
      ROQuery.gCost ROQuery.hCost (fun _ => ε) 0 0 ε
      (fun q s hs => S.simHandler_reEnc_le hγ hpk cStar q s hs) (fun _ _ _ _ _ _ => by simp)
      (hq (pk, cStar, k)).1 (hq (pk, cStar, k)).2 (s := {}) (by simp)).trans_eq ?_
    push_cast
    ring
  calc P.toOuterMeasure
        {x | (x.2.gCache.lookup mStar).isSome ∨ (x.2.hqCache.lookup cStar).isSome}
      ≤ P.toOuterMeasure ({x | (x.2.gCache.lookup mStar).isSome} ∪
          {x | ∃ p ∈ x.2.gCache, S.pke.encDet pk p.1 p.2 = cStar}) := by
        refine PMF.toOuterMeasure_mono P fun x ⟨hx, hsupp⟩ => ?_
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (hinv x hsupp hx)
    _ ≤ _ := MeasureTheory.measure_union_le _ _
    _ ≤ _ := by gcongr

/-- `simHitProb A m m` as the hit probability of the simulator run on a fresh encryption of
`m`. -/
private theorem simHitProb_self_eq (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    (m : M) :
    S.simHitProb A m m = (((ProbComp.eval S.pke.keyGen).bind fun keys =>
      (ProbComp.eval S.pke.sampleCoins).bind fun r =>
      (ProbComp.eval S.sampleKey).bind fun k =>
        (S.simRun A keys.1 (S.pke.encDet keys.1 m r) k {}).map
          fun x => (x.2.gCache.lookup m).isSome) true).toReal := by
  simp only [simHitProb, simRun, ExplicitCoinPKE.indCpaGame, ExplicitCoinPKE.encrypt,
    romCpaReduction, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
    OracleComp.map_run_interpret ProbComp.isMonadHom_eval, PMF.map, PMF.bind_bind,
    PMF.pure_bind, Function.comp_def]

/-- **Averaging**: with a uniform message sampler, the probability that the
simulator run from the empty state on an encryption of a fresh message `m` records `m` in
`gCache` is the diagonal average of `simHitProb`. -/
private theorem avg_simRun_hit [Fintype M] [Nonempty M] (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K)
    (hmsg : ProbComp.eval S.sampleMsg = PMF.uniformOfFintype M) :
    (((ProbComp.eval S.pke.keyGen).bind fun keys =>
      (ProbComp.eval S.sampleMsg).bind fun m =>
      (ProbComp.eval S.pke.sampleCoins).bind fun r =>
      (ProbComp.eval S.sampleKey).bind fun k =>
        (S.simRun A keys.1 (S.pke.encDet keys.1 m r) k {}).map
          fun x => (x.2.gCache.lookup m).isSome) true).toReal =
      (∑ m : M, S.simHitProb A m m) / (Fintype.card M : ℝ) := by
  rw [PMF.bind_comm, hmsg, PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum fun _ _ =>
      ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _), Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [simHitProb_self_eq, ENNReal.toReal_mul, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, div_eq_inv_mul]

/-! ### Simulators with lazily programmed points -/

/-- Lazy `G` on `gCache`, sampling `gs m` at a fresh query `m`. -/
private def genHashG (gs : M → ProbComp R) (m : M) : StateT (SimState M R CT K) ProbComp R :=
  RandomOracle.zoomStateT (fun st => st.gCache) (fun st c => { st with gCache := c })
    (memoize (fun _ => gs m) m)

/-- Lazy `Hq` on `hqCache`, sampling `hs c` at a fresh query `c`. -/
private def genHashHq (hs : CT → ProbComp K) (c : CT) : StateT (SimState M R CT K) ProbComp K :=
  RandomOracle.zoomStateT SimState.hqCache (fun st c' => { st with hqCache := c' })
    (memoize (fun _ => hs c) c)

/-- The keyless simulator with per-point samplers `gs` for `G` and `hs` for `Hq`. -/
private def genHandler (S : Scheme PK SK M R CT K) (gs : M → ProbComp R) (hs : CT → ProbComp K)
    (pk : PK) (cStar : CT) (q : ROQuery M CT) :
    StateT (SimState M R CT K) ProbComp (ROResp R K q) :=
  match q with
  | .G m => genHashG gs m
  | .H (false, m, c) => do
    let r ← genHashG gs m
    if S.pke.encDet pk m r = c then genHashHq hs c else simHashHRaw S.sampleKey (false, m, c)
  | .H (true, m, c) => simHashHRaw S.sampleKey (true, m, c)
  | .decaps c =>
    if c = cStar then
      return none
    else do
      let k ← genHashHq hs c
      return some k

private theorem simHandler_eq_genHandler (S : Scheme PK SK M R CT K) (pk : PK) (cStar : CT) :
    S.simHandler pk cStar =
      S.genHandler (fun _ => S.pke.sampleCoins) (fun _ => S.sampleKey) pk cStar := by
  funext q
  rcases q with m | ⟨_ | _, m, c⟩ | c <;> rfl

omit [DecidableEq CT] in
private theorem eval_genHashG (gs : M → ProbComp R) (m : M) (s : SimState M R CT K) :
    ProbComp.eval (genHashG gs m s) =
      (memoize (fun _ => ProbComp.eval (gs m)) m s.gCache).map
        (fun p => (p.1, { s with gCache := p.2 })) :=
  RandomOracle.eval_zoomStateT_memoize _ _ _ _ _

omit [DecidableEq M] in
private theorem eval_genHashHq (hs : CT → ProbComp K) (c : CT) (s : SimState M R CT K) :
    ProbComp.eval (genHashHq hs c s) =
      (memoize (fun _ => ProbComp.eval (hs c)) c s.hqCache).map
        (fun p => (p.1, { s with hqCache := p.2 })) :=
  RandomOracle.eval_zoomStateT_memoize _ _ _ _ _

private theorem eval_simHashHRaw (sampleKey : ProbComp K) (x : Bool × M × CT)
    (s : SimState M R CT K) :
    ProbComp.eval (simHashHRaw sampleKey x s) =
      (memoize (fun _ => ProbComp.eval sampleKey) x s.hCache).map
        (fun p => (p.1, { s with hCache := p.2 })) :=
  RandomOracle.eval_zoomStateT_memoize _ _ _ _ _

private theorem eval_genHandler_H_false (S : Scheme PK SK M R CT K) (gs : M → ProbComp R)
    (hs : CT → ProbComp K) (pk : PK) (cStar : CT) (m : M) (c : CT) (s : SimState M R CT K) :
    ProbComp.eval (S.genHandler gs hs pk cStar (.H (false, m, c)) s) =
      (ProbComp.eval (genHashG gs m s)).bind fun z =>
        if S.pke.encDet pk m z.1 = c then ProbComp.eval (genHashHq hs c z.2)
        else ProbComp.eval (simHashHRaw S.sampleKey (false, m, c) z.2) := by
  change ProbComp.eval (genHashG gs m s >>= fun z =>
    (if S.pke.encDet pk m z.1 = c then genHashHq hs c
      else simHashHRaw S.sampleKey (false, m, c)) z.2) = _
  rw [ProbComp.eval_bind]
  congr 1 with z : 1
  split_ifs <;> rfl

private theorem eval_genHandler_decaps (S : Scheme PK SK M R CT K) (gs : M → ProbComp R)
    (hs : CT → ProbComp K) (pk : PK) (cStar c : CT) (hc : c ≠ cStar) (s : SimState M R CT K) :
    ProbComp.eval (S.genHandler gs hs pk cStar (.decaps c) s) =
      (ProbComp.eval (genHashHq hs c s)).map fun z => (some z.1, z.2) := by
  change ProbComp.eval ((if c = cStar then (return none : StateT (SimState M R CT K) ProbComp
    (Option K)) else do let k ← genHashHq hs c; return some k) s) = _
  simp only [hc, ↓reduceIte]
  change ProbComp.eval (genHashHq hs c s >>= fun z => pure (some z.1, z.2)) = _
  rw [ProbComp.eval_bind]
  simp only [ProbComp.eval_pure, PMF.map]
  rfl

private theorem eval_genHandler_decaps_self (S : Scheme PK SK M R CT K) (gs : M → ProbComp R)
    (hs : CT → ProbComp K) (pk : PK) (cStar : CT) (s : SimState M R CT K) :
    ProbComp.eval (S.genHandler gs hs pk cStar (.decaps cStar) s) = PMF.pure (none, s) := by
  change ProbComp.eval ((if cStar = cStar then (return none : StateT (SimState M R CT K)
    ProbComp (Option K)) else do let k ← genHashHq hs cStar; return some k) s) = _
  simp only [↓reduceIte]
  exact ProbComp.eval_pure _

/-! ### Cache growth -/

private theorem suffix_of_mem_support_memoize {α β : Type} [BEq α] (d : α → PMF β) (y : α)
    (L : List (α × β)) (p : β × List (α × β)) (hp : p ∈ (memoize d y L).support) : L <:+ p.2 := by
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hp with ⟨-, h⟩ | ⟨-, -, h⟩
  · rw [h]
  · rw [h]
    exact List.suffix_cons _ _

omit [DecidableEq CT] in
private theorem genHashG_mono (gs : M → ProbComp R) (m : M) (s : SimState M R CT K)
    (x : R × SimState M R CT K) (hx : x ∈ (ProbComp.eval (genHashG gs m s)).support) :
    s.gCache <:+ x.2.gCache ∧ x.2.hqCache = s.hqCache := by
  rw [eval_genHashG, PMF.mem_support_map_iff] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨suffix_of_mem_support_memoize _ _ _ p hp, rfl⟩

omit [DecidableEq M] in
private theorem genHashHq_mono (hs : CT → ProbComp K) (c : CT) (s : SimState M R CT K)
    (x : K × SimState M R CT K) (hx : x ∈ (ProbComp.eval (genHashHq hs c s)).support) :
    x.2.gCache = s.gCache ∧ s.hqCache <:+ x.2.hqCache := by
  rw [eval_genHashHq, PMF.mem_support_map_iff] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨rfl, suffix_of_mem_support_memoize _ _ _ p hp⟩

private theorem simHashHRaw_mono (sampleKey : ProbComp K) (y : Bool × M × CT)
    (s : SimState M R CT K) (x : K × SimState M R CT K)
    (hx : x ∈ (ProbComp.eval (simHashHRaw sampleKey y s)).support) :
    x.2.gCache = s.gCache ∧ x.2.hqCache = s.hqCache := by
  rw [eval_simHashHRaw, PMF.mem_support_map_iff] at hx
  obtain ⟨p, -, rfl⟩ := hx
  exact ⟨rfl, rfl⟩

/-- Every supported step of `genHandler` only prepends to `gCache` and `hqCache`. -/
private theorem genHandler_mono (S : Scheme PK SK M R CT K) (gs : M → ProbComp R)
    (hs : CT → ProbComp K) (pk : PK) (cStar : CT) (q : ROQuery M CT) (s : SimState M R CT K)
    (x : ROResp R K q × SimState M R CT K)
    (hx : x ∈ (ProbComp.eval (S.genHandler gs hs pk cStar q s)).support) :
    s.gCache <:+ x.2.gCache ∧ s.hqCache <:+ x.2.hqCache := by
  rcases q with m | ⟨_ | _, m, c⟩ | c
  · obtain ⟨h₁, h₂⟩ := genHashG_mono gs m s x hx
    exact ⟨h₁, h₂ ▸ List.suffix_refl _⟩
  · rw [eval_genHandler_H_false, PMF.mem_support_bind_iff] at hx
    obtain ⟨z, hz, hx⟩ := hx
    obtain ⟨hz₁, hz₂⟩ := genHashG_mono gs m s z hz
    split_ifs at hx
    · obtain ⟨h₁, h₂⟩ := genHashHq_mono hs c z.2 x hx
      exact ⟨h₁ ▸ hz₁, hz₂ ▸ h₂⟩
    · obtain ⟨h₁, h₂⟩ := simHashHRaw_mono S.sampleKey (false, m, c) z.2 x hx
      exact ⟨h₁ ▸ hz₁, h₂ ▸ hz₂ ▸ List.suffix_refl _⟩
  · obtain ⟨h₁, h₂⟩ := simHashHRaw_mono S.sampleKey (true, m, c) s x hx
    exact ⟨h₁ ▸ List.suffix_refl _, h₂ ▸ List.suffix_refl _⟩
  · by_cases hc : c = cStar
    · subst hc
      rw [eval_genHandler_decaps_self, PMF.mem_support_pure_iff] at hx
      subst hx
      exact ⟨List.suffix_refl _, List.suffix_refl _⟩
    · rw [eval_genHandler_decaps _ _ _ _ _ _ hc, PMF.mem_support_map_iff] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨h₁, h₂⟩ := genHashHq_mono hs c s z hz
      exact ⟨h₁ ▸ List.suffix_refl _, h₂⟩

/-! ### Programmed and unprogrammed simulators agree until a programmed point is cached -/

/-- The simulator state has cached `G(mStar)` or `Hq(cStar)`. -/
private def progBad (mStar : M) (cStar : CT) (s : SimState M R CT K) : Prop :=
  (s.gCache.lookup mStar).isSome ∨ (s.hqCache.lookup cStar).isSome

/-- Binds whose first stages agree on good states, and whose continuations agree on good inputs
and outputs and keep bad states bad, agree on good outputs. -/
private theorem bind_apply_eq_of_good {α β σ : Type} {bad : σ → Prop} {p₁ p₂ : PMF (α × σ)}
    {f₁ f₂ : α × σ → PMF (β × σ)} (hp : ∀ x, ¬bad x.2 → p₁ x = p₂ x)
    (hf : ∀ x, ¬bad x.2 → ∀ y, ¬bad y.2 → f₁ x y = f₂ x y)
    (h₁ : ∀ x, bad x.2 → ∀ y ∈ (f₁ x).support, bad y.2)
    (h₂ : ∀ x, bad x.2 → ∀ y ∈ (f₂ x).support, bad y.2) (y : β × σ) (hy : ¬bad y.2) :
    (p₁.bind f₁) y = (p₂.bind f₂) y := by
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : bad x.2
  · rw [(PMF.apply_eq_zero_iff _ _).mpr fun hm => hy (h₁ x hx y hm),
      (PMF.apply_eq_zero_iff _ _).mpr fun hm => hy (h₂ x hx y hm), mul_zero, mul_zero]
  · rw [hp x hx, hf x hx y hy]

/-- A fresh memoized query for `x` caches `x`. -/
private theorem lookup_isSome_of_mem_support_memoize {α β : Type} [BEq α] [LawfulBEq α]
    (d : α → PMF β) (x : α) (L : List (α × β)) (hL : L.lookup x = none)
    (p : β × List (α × β)) (hp : p ∈ (memoize d x L).support) : (p.2.lookup x).isSome := by
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hp with ⟨h, -⟩ | ⟨-, -, h⟩
  · rw [hL] at h; cases h
  · rw [h]; simp

omit [DecidableEq CT] in
private theorem genHashG_agree {gs₁ gs₂ : M → ProbComp R} {mStar : M}
    (hgs : ∀ m, m ≠ mStar → gs₁ m = gs₂ m) (m : M) (s : SimState M R CT K)
    (hs : s.gCache.lookup mStar = none) (z : R × SimState M R CT K)
    (hz : z.2.gCache.lookup mStar = none) :
    ProbComp.eval (genHashG gs₁ m s) z = ProbComp.eval (genHashG gs₂ m s) z := by
  by_cases hm : m = mStar
  · subst hm
    have hzero (gs : M → ProbComp R) : ProbComp.eval (genHashG gs m s) z = 0 := by
      refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_
      rw [eval_genHashG, PMF.mem_support_map_iff] at hmem
      obtain ⟨p, hp, rfl⟩ := hmem
      have h := lookup_isSome_of_mem_support_memoize _ _ _ hs p hp
      dsimp only at hz
      rw [hz] at h
      exact absurd h (by simp)
    rw [hzero, hzero]
  · rw [eval_genHashG, eval_genHashG, hgs m hm]

omit [DecidableEq M] in
private theorem genHashHq_agree {hs₁ hs₂ : CT → ProbComp K} {cStar : CT}
    (hhs : ∀ c, c ≠ cStar → hs₁ c = hs₂ c) (c : CT) (s : SimState M R CT K)
    (hs : s.hqCache.lookup cStar = none) (z : K × SimState M R CT K)
    (hz : z.2.hqCache.lookup cStar = none) :
    ProbComp.eval (genHashHq hs₁ c s) z = ProbComp.eval (genHashHq hs₂ c s) z := by
  by_cases hc : c = cStar
  · subst hc
    have hzero (hs' : CT → ProbComp K) : ProbComp.eval (genHashHq hs' c s) z = 0 := by
      refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_
      rw [eval_genHashHq, PMF.mem_support_map_iff] at hmem
      obtain ⟨p, hp, rfl⟩ := hmem
      have h := lookup_isSome_of_mem_support_memoize _ _ _ hs p hp
      dsimp only at hz
      rw [hz] at h
      exact absurd h (by simp)
    rw [hzero, hzero]
  · rw [eval_genHashHq, eval_genHashHq, hhs c hc]

private theorem not_progBad {mStar : M} {cStar : CT} {s : SimState M R CT K} :
    ¬progBad mStar cStar s ↔ s.gCache.lookup mStar = none ∧ s.hqCache.lookup cStar = none := by
  simp only [progBad, not_or, Option.not_isSome_iff_eq_none]

private theorem progBad_of_suffix {mStar : M} {cStar : CT} {s s' : SimState M R CT K}
    (hg : s.gCache <:+ s'.gCache) (hq : s.hqCache <:+ s'.hqCache) (hs : progBad mStar cStar s) :
    progBad mStar cStar s' :=
  hs.imp (isSome_lookup_of_suffix hg mStar) (isSome_lookup_of_suffix hq cStar)

/-- Simulators whose samplers differ only at `G(mStar)` and `Hq(cStar)` agree until one of these
points is cached. -/
private theorem identicalUntilBad_genHandler (S : Scheme PK SK M R CT K)
    {gs₁ gs₂ : M → ProbComp R} {hs₁ hs₂ : CT → ProbComp K} (pk : PK) {mStar : M} (cStar : CT)
    (hgs : ∀ m, m ≠ mStar → gs₁ m = gs₂ m) (hhs : ∀ c, c ≠ cStar → hs₁ c = hs₂ c) :
    OracleComp.IdenticalUntilBad
      (fun q s => ProbComp.eval (S.genHandler gs₁ hs₁ pk cStar q s))
      (fun q s => ProbComp.eval (S.genHandler gs₂ hs₂ pk cStar q s)) (progBad mStar cStar) where
  agree q s hs a s' hs' := by
    obtain ⟨hsg, hsq⟩ := not_progBad.mp hs
    obtain ⟨hsg', hsq'⟩ := not_progBad.mp hs'
    rcases q with m | ⟨_ | _, m, c⟩ | c
    · exact genHashG_agree hgs m s hsg (a, s') hsg'
    · rw [eval_genHandler_H_false, eval_genHandler_H_false]
      refine bind_apply_eq_of_good (bad := progBad mStar cStar) ?_ ?_ ?_ ?_ (a, s') hs'
      · intro z hz
        exact genHashG_agree hgs m s hsg z (not_progBad.mp hz).1
      · intro z hz y hy
        split_ifs
        · exact genHashHq_agree hhs c z.2 (not_progBad.mp hz).2 y (not_progBad.mp hy).2
        · rfl
      all_goals
        intro z hz y hy
        split_ifs at hy
        · obtain ⟨h₁, h₂⟩ := genHashHq_mono _ c z.2 y hy
          exact progBad_of_suffix (h₁ ▸ List.suffix_refl _) h₂ hz
        · obtain ⟨h₁, h₂⟩ := simHashHRaw_mono _ _ z.2 y hy
          exact progBad_of_suffix (h₁ ▸ List.suffix_refl _) (h₂ ▸ List.suffix_refl _) hz
    · rfl
    · by_cases hc : c = cStar
      · subst hc
        rw [eval_genHandler_decaps_self, eval_genHandler_decaps_self]
      · rw [eval_genHandler_decaps _ _ _ _ _ _ hc, eval_genHandler_decaps _ _ _ _ _ _ hc]
        simp only [PMF.map]
        refine bind_apply_eq_of_good (bad := progBad mStar cStar) ?_ ?_ ?_ ?_ (a, s') hs'
        · intro z hz
          exact genHashHq_agree hhs c s hsq z (not_progBad.mp hz).2
        · intro z _ y _
          rfl
        all_goals
          intro z hz y hy
          simp only [Function.comp_apply, PMF.mem_support_pure_iff] at hy
          subst hy
          exact hz
  absorb_first q s hs x hx :=
    have h := S.genHandler_mono gs₁ hs₁ pk cStar q s x hx
    progBad_of_suffix h.1 h.2 hs
  absorb_second q s hs x hx :=
    have h := S.genHandler_mono gs₂ hs₂ pk cStar q s x hx
    progBad_of_suffix h.1 h.2 hs

/-! ### Preset cache entries as lazily programmed points -/

/-- Coin sampler for `G` with `G(mStar)` programmed to `rStar`. -/
private def progG (S : Scheme PK SK M R CT K) (mStar : M) (rStar : R) (m : M) : ProbComp R :=
  if m = mStar then pure rStar else S.pke.sampleCoins

/-- Key sampler for `Hq` with `Hq(cStar)` programmed to `kq`. -/
private def progHq (S : Scheme PK SK M R CT K) (cStar : CT) (kq : K) (c : CT) : ProbComp K :=
  if c = cStar then pure kq else S.sampleKey

/-- A lookup at `x` is either missing or equal to `v`. -/
private def LookupNoneOr {α β : Type} [BEq α] (x : α) (v : β) (L : List (α × β)) : Prop :=
  L.lookup x = none ∨ L.lookup x = some v

private theorem lookupNoneOr_memoize {α β : Type} [DecidableEq α] (d : PMF β) (x : α) (v : β)
    (y : α) (L : List (α × β)) (hL : LookupNoneOr x v L) (p : β × List (α × β))
    (hp : p ∈ (memoize (fun _ => if y = x then PMF.pure v else d) y L).support) :
    LookupNoneOr x v p.2 := by
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hp with ⟨-, h⟩ | ⟨-, hw, h⟩
  · rw [h]; exact hL
  · rw [h]
    by_cases hy : y = x
    · subst hy
      simp only [↓reduceIte, PMF.mem_support_pure_iff] at hw
      right
      simp [hw]
    · have hxy : (x == y) = false := beq_eq_false_iff_ne.mpr (Ne.symm hy)
      simpa [LookupNoneOr, List.lookup_cons, hxy] using hL

/-- Moving the programmed entries to the end of their caches. -/
private def presetState (mStar : M) (rStar : R) (cStar : CT) (kq : K)
    (s : SimState M R CT K) : SimState M R CT K :=
  { s with gCache := ens mStar rStar s.gCache, hqCache := ens cStar kq s.hqCache }

/-- The programmed caches agree with the programmed values wherever they are defined. -/
private def PresetInv (mStar : M) (rStar : R) (cStar : CT) (kq : K)
    (s : SimState M R CT K) : Prop :=
  LookupNoneOr mStar rStar s.gCache ∧ LookupNoneOr cStar kq s.hqCache

omit [DecidableEq CT] in
private theorem eval_progG (S : Scheme PK SK M R CT K) (mStar : M) (rStar : R) (m : M) :
    ProbComp.eval (S.progG mStar rStar m) =
      if m = mStar then PMF.pure rStar else ProbComp.eval S.pke.sampleCoins := by
  unfold progG; split_ifs <;> simp [ProbComp.eval_pure]

omit [DecidableEq M] in
private theorem eval_progHq (S : Scheme PK SK M R CT K) (cStar : CT) (kq : K) (c : CT) :
    ProbComp.eval (S.progHq cStar kq c) =
      if c = cStar then PMF.pure kq else ProbComp.eval S.sampleKey := by
  unfold progHq; split_ifs <;> simp [ProbComp.eval_pure]

private theorem presetInv_genHashG (S : Scheme PK SK M R CT K) (mStar : M) (rStar : R)
    (cStar : CT) (kq : K) (m : M) (s : SimState M R CT K)
    (hs : PresetInv mStar rStar cStar kq s) (x : R × SimState M R CT K)
    (hx : x ∈ (ProbComp.eval (genHashG (S.progG mStar rStar) m s)).support) :
    PresetInv mStar rStar cStar kq x.2 := by
  rw [eval_genHashG, eval_progG, PMF.mem_support_map_iff] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨lookupNoneOr_memoize _ _ _ _ _ hs.1 p hp, hs.2⟩

private theorem presetInv_genHashHq (S : Scheme PK SK M R CT K) (mStar : M) (rStar : R)
    (cStar : CT) (kq : K) (c : CT) (s : SimState M R CT K)
    (hs : PresetInv mStar rStar cStar kq s) (x : K × SimState M R CT K)
    (hx : x ∈ (ProbComp.eval (genHashHq (S.progHq cStar kq) c s)).support) :
    PresetInv mStar rStar cStar kq x.2 := by
  rw [eval_genHashHq, eval_progHq, PMF.mem_support_map_iff] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨hs.1, lookupNoneOr_memoize _ _ _ _ _ hs.2 p hp⟩

private theorem presetInv_genHandler (S : Scheme PK SK M R CT K) (pk : PK) (mStar : M)
    (rStar : R) (cStar : CT) (kq : K) (q : ROQuery M CT) (s : SimState M R CT K)
    (hs : PresetInv mStar rStar cStar kq s) (a : ROResp R K q) (s' : SimState M R CT K)
    (hx : (a, s') ∈ (ProbComp.eval
      (S.genHandler (S.progG mStar rStar) (S.progHq cStar kq) pk cStar q s)).support) :
    PresetInv mStar rStar cStar kq s' := by
  rcases q with m | ⟨_ | _, m, c⟩ | c
  · exact S.presetInv_genHashG mStar rStar cStar kq m s hs _ hx
  · rw [eval_genHandler_H_false, PMF.mem_support_bind_iff] at hx
    obtain ⟨z, hz, hx⟩ := hx
    have hz' := S.presetInv_genHashG mStar rStar cStar kq m s hs z hz
    split_ifs at hx
    · exact S.presetInv_genHashHq mStar rStar cStar kq c z.2 hz' _ hx
    · obtain ⟨h₁, h₂⟩ := simHashHRaw_mono _ _ z.2 _ hx
      exact ⟨h₁ ▸ hz'.1, h₂ ▸ hz'.2⟩
  · obtain ⟨h₁, h₂⟩ := simHashHRaw_mono _ _ s _ hx
    exact ⟨h₁ ▸ hs.1, h₂ ▸ hs.2⟩
  · by_cases hc : c = cStar
    · subst hc
      rw [eval_genHandler_decaps_self, PMF.mem_support_pure_iff] at hx
      cases hx
      exact hs
    · rw [eval_genHandler_decaps _ _ _ _ _ _ hc, PMF.mem_support_map_iff] at hx
      obtain ⟨z, hz, hx⟩ := hx
      cases hx
      exact S.presetInv_genHashHq mStar rStar cStar kq c s hs z hz

private theorem genHashG_presetState (S : Scheme PK SK M R CT K) (mStar : M) (rStar : R)
    (cStar : CT) (kq : K) (m : M) (s : SimState M R CT K)
    (hs : LookupNoneOr mStar rStar s.gCache) :
    (ProbComp.eval (genHashG (S.progG mStar rStar) m s)).map
        (fun x => (x.1, presetState mStar rStar cStar kq x.2)) =
      ProbComp.eval (genHashG (fun _ => S.pke.sampleCoins) m
        (presetState mStar rStar cStar kq s)) := by
  rw [eval_genHashG, eval_genHashG, eval_progG]
  rw [show (presetState mStar rStar cStar kq s).gCache = ens mStar rStar s.gCache from rfl]
  rw [← memoize_ens _ _ _ _ _ hs, PMF.map_comp, PMF.map_comp]
  rfl

private theorem genHashHq_presetState (S : Scheme PK SK M R CT K) (mStar : M) (rStar : R)
    (cStar : CT) (kq : K) (c : CT) (s : SimState M R CT K)
    (hs : LookupNoneOr cStar kq s.hqCache) :
    (ProbComp.eval (genHashHq (S.progHq cStar kq) c s)).map
        (fun x => (x.1, presetState mStar rStar cStar kq x.2)) =
      ProbComp.eval (genHashHq (fun _ => S.sampleKey) c
        (presetState mStar rStar cStar kq s)) := by
  rw [eval_genHashHq, eval_genHashHq, eval_progHq]
  rw [show (presetState mStar rStar cStar kq s).hqCache = ens cStar kq s.hqCache from rfl]
  rw [← memoize_ens _ _ _ _ _ hs, PMF.map_comp, PMF.map_comp]
  rfl

private theorem simHashHRaw_presetState (sampleKey : ProbComp K) (mStar : M) (rStar : R)
    (cStar : CT) (kq : K) (y : Bool × M × CT) (s : SimState M R CT K) :
    (ProbComp.eval (simHashHRaw sampleKey y s)).map
        (fun x => (x.1, presetState mStar rStar cStar kq x.2)) =
      ProbComp.eval (simHashHRaw sampleKey y (presetState mStar rStar cStar kq s)) := by
  rw [eval_simHashHRaw, eval_simHashHRaw, PMF.map_comp]
  rfl

private theorem genHandler_presetState (S : Scheme PK SK M R CT K) (pk : PK) (mStar : M)
    (rStar : R) (cStar : CT) (kq : K) (q : ROQuery M CT) (s : SimState M R CT K)
    (hs : PresetInv mStar rStar cStar kq s) :
    (ProbComp.eval
        (S.genHandler (S.progG mStar rStar) (S.progHq cStar kq) pk cStar q s)).map
        (fun x => (x.1, presetState mStar rStar cStar kq x.2)) =
      ProbComp.eval (S.simHandler pk cStar q (presetState mStar rStar cStar kq s)) := by
  rw [simHandler_eq_genHandler]
  rcases q with m | ⟨_ | _, m, c⟩ | c
  · exact S.genHashG_presetState mStar rStar cStar kq m s hs.1
  · rw [eval_genHandler_H_false, eval_genHandler_H_false, PMF.map_bind,
      ← S.genHashG_presetState mStar rStar cStar kq m s hs.1, PMF.bind_map]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun z hz => ?_
    have hz' := S.presetInv_genHashG mStar rStar cStar kq m s hs z hz
    dsimp only [Function.comp_apply]
    split_ifs
    · exact S.genHashHq_presetState mStar rStar cStar kq c z.2 hz'.2
    · exact simHashHRaw_presetState _ mStar rStar cStar kq _ z.2
  · exact simHashHRaw_presetState _ mStar rStar cStar kq _ s
  · by_cases hc : c = cStar
    · subst hc
      rw [eval_genHandler_decaps_self, eval_genHandler_decaps_self, PMF.pure_map]
    · rw [eval_genHandler_decaps _ _ _ _ _ _ hc, eval_genHandler_decaps _ _ _ _ _ _ hc,
        ← S.genHashHq_presetState mStar rStar cStar kq c s hs.2, PMF.map_comp, PMF.map_comp]
      rfl

/-- Running the simulator from caches preset with `G(mStar) = rStar` and `Hq(cStar) = kq` has the
same output law as running it from empty caches with these points lazily programmed. -/
private theorem simRun_preset_eq (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    (pk : PK) (mStar : M) (rStar : R) (cStar : CT) (kq k : K) :
    (S.simRun A pk cStar k { gCache := [(mStar, rStar)], hqCache := [(cStar, kq)] }).map
        Prod.fst =
      ((OracleComp.interpret (m := StateT (SimState M R CT K) PMF)
        (fun q s => ProbComp.eval
          (S.genHandler (S.progG mStar rStar) (S.progHq cStar kq) pk cStar q s))
        (A (pk, cStar, k))).run {}).map Prod.fst := by
  have h := OracleComp.run_interpret_map_state_of_invariant
    (fun q s => ProbComp.eval
      (S.genHandler (S.progG mStar rStar) (S.progHq cStar kq) pk cStar q s))
    (fun q s => ProbComp.eval (S.simHandler pk cStar q s))
    (presetState mStar rStar cStar kq) (PresetInv mStar rStar cStar kq)
    (S.presetInv_genHandler pk mStar rStar cStar kq)
    (fun q s hs => S.genHandler_presetState pk mStar rStar cStar kq q s hs)
    (A (pk, cStar, k)) {} ⟨Or.inl rfl, Or.inl rfl⟩
  have hfst := congrArg (PMF.map Prod.fst) h
  rw [PMF.map_comp] at hfst
  exact hfst.symm

/-! ### Unfolding `simGame` -/

/-- The real-key computation of `simGame` stores fresh `kq` at `Hq(c*)` and returns it. -/
private theorem eval_simHashH_init (S : Scheme PK SK M R CT K) (pk : PK) (mStar : M)
    (rStar : R) :
    ProbComp.eval ((S.simHashH pk (false, mStar, S.pke.encDet pk mStar rStar)).run
        { gCache := [(mStar, rStar)] }) =
      (ProbComp.eval S.sampleKey).map fun kq =>
        (kq, ({ gCache := [(mStar, rStar)], hqCache := [(S.pke.encDet pk mStar rStar, kq)] } :
          SimState M R CT K)) := by
  change ProbComp.eval (simHashG S.pke.sampleCoins mStar { gCache := [(mStar, rStar)] } >>=
    fun z => (if S.pke.encDet pk mStar z.1 = S.pke.encDet pk mStar rStar then
      simHashHq S.sampleKey (S.pke.encDet pk mStar rStar)
      else simHashHRaw S.sampleKey (false, mStar, S.pke.encDet pk mStar rStar)) z.2) = _
  rw [ProbComp.eval_bind, simHashG, RandomOracle.eval_zoomStateT_memoize,
    memoize_of_some _ _ _ rStar (by simp)]
  simp only [Probability.PMF.monad_pure_eq_pure, PMF.pure_map, PMF.pure_bind, ↓reduceIte]
  rw [simHashHq, RandomOracle.eval_zoomStateT_memoize, memoize_of_none _ _ _ (by rfl)]
  simp only [Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map]
  rfl

private theorem eval_simGame (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    (b : Bool) :
    ProbComp.eval (S.simGame A b) =
      (ProbComp.eval S.pke.keyGen).bind fun keys =>
      (ProbComp.eval S.sampleMsg).bind fun mStar =>
      (ProbComp.eval S.pke.sampleCoins).bind fun rStar =>
      (ProbComp.eval S.sampleKey).bind fun kq =>
      (ProbComp.eval S.sampleKey).bind fun kRand =>
        (S.simRun A keys.1 (S.pke.encDet keys.1 mStar rStar) (if b then kRand else kq)
          { gCache := [(mStar, rStar)],
            hqCache := [(S.pke.encDet keys.1 mStar rStar, kq)] }).map Prod.fst := by
  simp only [simGame, ProbComp.eval_bind, ProbComp.eval_pure]
  congr 1 with keys : 1
  congr 1 with mStar : 1
  congr 1 with rStar : 1
  rw [eval_simHashH_init, PMF.bind_map]
  congr 1 with kq : 1
  dsimp only [Function.comp_apply]
  congr 1 with kRand : 1
  rw [OracleComp.map_run_interpret ProbComp.isMonadHom_eval]
  rfl

/-! ### The challenge hop -/

/-- The outer randomness of `simGame`: key pair, challenge message and coins, real and random
keys. -/
private noncomputable def chalOuter (S : Scheme PK SK M R CT K) :
    PMF ((PK × SK) × M × R × K × K) :=
  (ProbComp.eval S.pke.keyGen).bind fun keys =>
  (ProbComp.eval S.sampleMsg).bind fun mStar =>
  (ProbComp.eval S.pke.sampleCoins).bind fun rStar =>
  (ProbComp.eval S.sampleKey).bind fun kq =>
  (ProbComp.eval S.sampleKey).bind fun kRand => PMF.pure (keys, mStar, rStar, kq, kRand)

omit [DecidableEq M] [DecidableEq CT] in
private theorem mem_support_chalOuter (S : Scheme PK SK M R CT K)
    (t : (PK × SK) × M × R × K × K) (ht : t ∈ S.chalOuter.support) :
    t.1 ∈ (ProbComp.eval S.pke.keyGen).support := by
  simp only [chalOuter, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at ht
  obtain ⟨keys, hk, _, _, _, _, _, _, _, _, rfl⟩ := ht
  exact hk

private theorem simRun_eq_genHandler (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    (pk : PK) (cStar : CT) (k : K) (st : SimState M R CT K) :
    S.simRun A pk cStar k st =
      (OracleComp.interpret (m := StateT (SimState M R CT K) PMF)
        (fun q s => ProbComp.eval
          (S.genHandler (fun _ => S.pke.sampleCoins) (fun _ => S.sampleKey) pk cStar q s))
        (A (pk, cStar, k))).run st := by
  simp only [simRun, simHandler_eq_genHandler]

/-- For one draw of the outer randomness, the simulator run from the preset `simGame` caches is
close to the run from empty caches, within the probability of caching `G(mStar)` plus the
`γ`-spreadness term. -/
private theorem closeTo_simRun_preset (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    {qG qH : ℕ} (hq : ROQueryBounds A qG qH) {γ : ℝ} (hγ : S.pke.GammaSpread γ)
    {pk : PK} {sk : SK} (hpk : (pk, sk) ∈ (ProbComp.eval S.pke.keyGen).support)
    (mStar : M) (rStar : R) (cStar : CT) (kq k : K) :
    CloseTo
      ((S.simRun A pk cStar k { gCache := [(mStar, rStar)], hqCache := [(cStar, kq)] }).map
        Prod.fst)
      ((S.simRun A pk cStar k {}).map Prod.fst)
      (((S.simRun A pk cStar k {}).map fun x => (x.2.gCache.lookup mStar).isSome) true +
        ((qG + qH : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ))) := by
  rw [simRun_preset_eq]
  have hiub := S.identicalUntilBad_genHandler (gs₁ := S.progG mStar rStar)
    (gs₂ := fun _ => S.pke.sampleCoins) (hs₁ := S.progHq cStar kq)
    (hs₂ := fun _ => S.sampleKey) (mStar := mStar) pk cStar (fun m hm => by simp [progG, hm])
    (fun c hc => by simp [progHq, hc])
  have h := (hiub.closeTo_run (A (pk, cStar, k)) {}).map Prod.fst
  rw [hiub.bad_eq, ← simRun_eq_genHandler] at h
  refine h.mono ((S.simRun_bad_le A hq hγ hpk mStar cStar k).trans (le_of_eq ?_))
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

/-- **Challenge hop of the `FO-notbot` IND-CCA proof**: if the message sampler is uniform on a
message space with at least two elements and the PKE is `γ`-spread, then for every adversary
making at most `qG` queries to `G` and `qH` queries to `H`, some distinct messages `m₀ ≠ m₁` bound
the advantage between the keyless simulator games `simGame A false` and `simGame A true` by
`2 Adv_CPA(romCpaReduction A m₀ m₁) + 2 (qG + qH)/|M| + 2 (qG + qH) 2^(-γ)`. -/
theorem advantage_simGame_le [Fintype M] [Nonempty M]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) {qG qH : ℕ}
    (hq : ROQueryBounds A qG qH) (hM : 2 ≤ Fintype.card M)
    (hmsg : ProbComp.eval S.sampleMsg = PMF.uniformOfFintype M) {γ : ℝ}
    (hγ : S.pke.GammaSpread γ) :
    ∃ m₀ m₁ : M, m₀ ≠ m₁ ∧
      (Game.advantage (ProbComp.eval (S.simGame A false))
          (ProbComp.eval (S.simGame A true)) : ℝ) ≤
        2 * (S.pke.indCpaAdvantage m₀ m₁ (S.romCpaReduction A m₀ m₁) : ℝ) +
          2 * (((qG : ℝ) + qH) / Fintype.card M) +
            2 * (((qG : ℝ) + qH) * (2 : ℝ) ^ (-γ)) := by
  classical
  obtain ⟨m₀, m₁, hne, havg⟩ := S.avg_simHitProb_le_indCpaAdvantage_romCpaReduction A hM hq
  refine ⟨m₀, m₁, hne, ?_⟩
  set ε : ℝ≥0∞ := ((qG + qH : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ)) with hε
  set H : ℝ≥0∞ := ((ProbComp.eval S.pke.keyGen).bind fun keys =>
      (ProbComp.eval S.sampleMsg).bind fun m =>
      (ProbComp.eval S.pke.sampleCoins).bind fun r =>
      (ProbComp.eval S.sampleKey).bind fun k =>
        (S.simRun A keys.1 (S.pke.encDet keys.1 m r) k {}).map
          fun x => (x.2.gCache.lookup m).isSome) true with hH
  set W : Game := (ProbComp.eval S.pke.keyGen).bind fun keys =>
      (ProbComp.eval S.sampleMsg).bind fun m =>
      (ProbComp.eval S.pke.sampleCoins).bind fun r =>
      (ProbComp.eval S.sampleKey).bind fun k =>
        (S.simRun A keys.1 (S.pke.encDet keys.1 m r) k {}).map Prod.fst with hW
  have hclose (b : Bool) : CloseTo (ProbComp.eval (S.simGame A b)) W (H + ε) := by
    have hS : ProbComp.eval (S.simGame A b) = S.chalOuter.bind fun t =>
        (S.simRun A t.1.1 (S.pke.encDet t.1.1 t.2.1 t.2.2.1)
          (if b then t.2.2.2.2 else t.2.2.2.1)
          { gCache := [(t.2.1, t.2.2.1)],
            hqCache := [(S.pke.encDet t.1.1 t.2.1 t.2.2.1, t.2.2.2.1)] }).map Prod.fst := by
      simp only [eval_simGame, chalOuter, PMF.bind_bind, PMF.pure_bind]
    have hW' : W = S.chalOuter.bind fun t =>
        (S.simRun A t.1.1 (S.pke.encDet t.1.1 t.2.1 t.2.2.1)
          (if b then t.2.2.2.2 else t.2.2.2.1) {}).map Prod.fst := by
      cases b <;> simp only [W, chalOuter, PMF.bind_bind, PMF.pure_bind, Bool.false_eq_true,
        ↓reduceIte, PMF.bind_const]
    have hH' : (∑' t, S.chalOuter t *
        (((S.simRun A t.1.1 (S.pke.encDet t.1.1 t.2.1 t.2.2.1)
          (if b then t.2.2.2.2 else t.2.2.2.1) {}).map
            fun x => (x.2.gCache.lookup t.2.1).isSome) true + ε)) = H + ε := by
      simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
        ← PMF.bind_apply]
      congr 1
      cases b <;> simp only [H, chalOuter, PMF.bind_bind, PMF.pure_bind, Bool.false_eq_true,
        ↓reduceIte, PMF.bind_const]
    rw [hS, hW', ← hH']
    exact CloseTo.bind_right_tsum _ fun t ht =>
      S.closeTo_simRun_preset A hq hγ (S.mem_support_chalOuter t ht) _ _ _ _ _
  have h₀ := Game.closeTo_iff_coe_advantage_le.mp (hclose false)
  have h₁ := Game.closeTo_iff_coe_advantage_le.mp (hclose true)
  have htri : Game.advantage (ProbComp.eval (S.simGame A false))
      (ProbComp.eval (S.simGame A true)) ≤
      Game.advantage (ProbComp.eval (S.simGame A false)) W +
        Game.advantage (ProbComp.eval (S.simGame A true)) W := by
    simp only [Game.advantage]
    rw [nndist_comm (Game.succProbability (ProbComp.eval (S.simGame A true)))]
    exact nndist_triangle _ _ _
  have hle : (Game.advantage (ProbComp.eval (S.simGame A false))
      (ProbComp.eval (S.simGame A true)) : ℝ≥0∞) ≤ 2 * (H + ε) := by
    calc _ ≤ (Game.advantage (ProbComp.eval (S.simGame A false)) W : ℝ≥0∞) +
          (Game.advantage (ProbComp.eval (S.simGame A true)) W : ℝ≥0∞) := by
          exact_mod_cast htri
      _ ≤ (H + ε) + (H + ε) := add_le_add h₀ h₁
      _ = 2 * (H + ε) := (two_mul _).symm
  have hHtop : H ≠ ⊤ := PMF.apply_ne_top _ _
  have hεtop : ε ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (ENNReal.add_ne_top.mpr ⟨hHtop, hεtop⟩)) hle
  rw [ENNReal.coe_toReal, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_add hHtop hεtop, hH,
    S.avg_simRun_hit A hmsg, hε, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (by norm_num) _)] at hreal
  rw [Nat.cast_add] at hreal
  linarith

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto
