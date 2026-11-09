/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Probabilistic.Memoize
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.Product

/-!
# Several independent keys of a pseudorandom function

A pseudorandom function stays pseudorandom when an adversary may query `t` independently keyed
copies at once, for every fixed number `t` of keys. [BonehShoup2023], Exercise 4.26, allows any
polynomially bounded number of keys; the asymptotic statement here covers only constant `t`, while
the concrete bound holds for every `t`. The real game `prfMultiRealGame` samples one
`t * n`-bit key and answers channel `i : Fin t` with the family under the `i`-th `n`-bit block
`keyBlock n i key`; the ideal game `prfMultiIdealGame` answers the channels with `t` independent
uniform random functions.

The proof is the standard hybrid argument. In the `j`-th hybrid the channels below `j` are random
and the others are keyed. The reduction `prfMultiReduction family t j adversary` samples its own
key, forwards channel `j` to its PRF challenger, simulates the random channels below `j` lazily
with an ordinary list cache, and evaluates the keyed channels above `j` itself. Against the real
PRF game it is the `j`-th hybrid and against the ideal PRF game the `(j + 1)`-st, so the multi-key
advantage is at most the sum of the `t` PRF advantages
(`advantage_prfMultiRealGame_prfMultiIdealGame_le`). The reduction is oracle PPT
(`isOraclePPT_prfMultiReduction`), which gives the asymptotic statement
`PseudorandomFunction.multiKey`.

## Main definitions

* `Cslib.Crypto.keyBlock`: the `i`-th `n`-bit block of a word.
* `Cslib.Crypto.MultiKeyDistinguisher`: an adaptive test with `t` word channels.
* `Cslib.Crypto.prfMultiRealGame`, `Cslib.Crypto.prfMultiIdealGame`: the multi-key experiments.
* `Cslib.Crypto.prfMultiHandler`, `Cslib.Crypto.prfMultiReduction`: the hybrid reduction.

## Main results

* `Cslib.Crypto.isOraclePPT_prfMultiReduction`: the hybrid reduction is oracle PPT.
* `Cslib.Crypto.advantage_prfMultiRealGame_prfMultiIdealGame_le`: the multi-key advantage is at
  most the sum of the PRF advantages of the `t` hybrid reductions.
* `Cslib.Crypto.PseudorandomFunction.multiKey`: independently keyed copies of a pseudorandom
  function are indistinguishable from independent random functions.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Exercise 4.26 (printed pp. 174–175), the `n`-wise parallel composition of a PRF for
  polynomially bounded `n`, which the proof of Theorem 4.9 (equation (4.24) on p. 144 and
  equation (4.25) on p. 145) uses for the three Feistel round keys. Only constant `t` is covered
  asymptotically here.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- The `i`-th block of `n` bits of a word, that is, its bits `i * n` to `i * n + n - 1`. -/
@[expose] def keyBlock (n i : ℕ) (key : List Bool) : List Bool := (key.drop (i * n)).take n

/-- Blocks of a word of `t` blocks have exactly `n` bits. -/
theorem length_keyBlock {n t i : ℕ} {key : List Bool} (hkey : key.length = t * n) (hi : i < t) :
    (keyBlock n i key).length = n := by
  have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at this
  simp only [keyBlock, List.length_take, List.length_drop, hkey]
  omega

/-- An adaptive test with a unary parameter, an auxiliary word and `t` word channels. -/
abbrev MultiKeyDistinguisher (t : ℕ) := ℕ → List Bool → WordOracleComp (Fin t) Bool

/-- The real multi-key experiment: one `t * n`-bit key, whose `i`-th block keys channel `i`. -/
@[expose] noncomputable def prfMultiRealGame (family : List Bool → List Bool → List Bool) (t : ℕ)
    (adversary : MultiKeyDistinguisher t) (n : ℕ) : ProbComp Bool := do
  let key ← BitString.sampleList (t * n)
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifFin (fun request =>
      pure (prfOracle family n (keyBlock n request.1 key) request.2)))
    (adversary n [])

/-- The ideal multi-key experiment: `t` independent uniform random functions. -/
@[expose] noncomputable def prfMultiIdealGame (t : ℕ) (adversary : MultiKeyDistinguisher t)
    (n : ℕ) : ProbComp Bool := do
  let tables ← ProbComp.uniform (Fin t → BitString n → BitString n)
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifFin (fun request =>
      pure (randomFunctionOracle n (tables request.1) request.2)))
    (adversary n [])

/-- The cache of the hybrid reduction, keyed by channel and query. -/
abbrev MultiKeyCache (t : ℕ) := List ((Fin t × List Bool) × List Bool)

/-- One call of the `j`-th hybrid reduction with its own `key`. Channels below `j` are lazily
sampled random functions; channel `j` is forwarded to the external oracle; channels above `j` are
keyed by blocks of `key`. Replies of the last two kinds are cut at `n` bits, which changes nothing
for keys and replies of the declared lengths and keeps the reduction polynomial on all inputs. -/
@[expose] noncomputable def prfMultiHandler (family : List Bool → List Bool → List Bool)
    (t j n : ℕ) (key : List Bool) (request : Fin t × List Bool) (cache : MultiKeyCache t) :
    WordOracleComp Unit (List Bool × MultiKeyCache t) :=
  match request with
  | (i, query) =>
    if i.val < j then
      if query.length = n then
        ProbOracleComp.sample (memoize (fun _ => BitString.sampleList n) (i, query) cache)
      else pure ([], cache)
    else if i.val = j then
      (fun reply => (reply, cache)) <$> (List.take n <$> ProbOracleComp.query ((), query))
    else pure ((prfOracle family n (keyBlock n i key) query).take n, cache)

/-- The `j`-th hybrid reduction: sample a `t * n`-bit key, then run the multi-key adversary with
`prfMultiHandler`, starting from the empty cache. -/
@[expose] noncomputable def prfMultiReduction (family : List Bool → List Bool → List Bool)
    (t j : ℕ) (adversary : MultiKeyDistinguisher t) : OracleDistinguisher := fun n aux => do
  let key ← ProbOracleComp.sample (BitString.sampleList (t * n))
  Prod.fst <$> (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (prfMultiHandler family t j n key)) (adversary n aux)).run []

/-! ### Efficiency of the hybrid reduction -/

section Efficiency

variable {family : List Bool → List Bool → List Bool}

/-- The encoding of the reduction's cache. -/
private abbrev cacheEncoding (t : ℕ) : MultiKeyCache t ↪ List Bool :=
  encList (encPair (encPair (encFinEnum (Fin t)) encBits) encBits)

/-- The input of one handler call: the caller `((n, aux), key)`, the request and the cache. -/
private abbrev HandlerInput (t : ℕ) :=
  ((ℕ × List Bool) × List Bool) × (Fin t × List Bool) × MultiKeyCache t

/-- The encoding of `HandlerInput`. -/
private abbrev handlerInputEncoding (t : ℕ) : HandlerInput t ↪ List Bool :=
  encPair (encPair (encPair encUnary encBits) encBits)
    (encPair (encPair (encFinEnum (Fin t)) encBits) (cacheEncoding t))

/-- A guarded reply cut at a computed length is efficient when its guard and value are. -/
private theorem computableInPolyTime_take_ite {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    {query value : α → List Bool} (hn : ComputableInPolyTime n input encUnary)
    (hquery : ComputableInPolyTime query input encBits)
    (hvalue : ComputableInPolyTime value input encBits) :
    ComputableInPolyTime (fun a => (if (query a).length = n a then value a else []).take (n a))
      input encBits :=
  ((hquery.length_bits_comp.unary_eq' hn).ite_decide hvalue (.const [])).bitsTakeWithInput hn

/-- One handler call is oracle PPT in the caller `((n, aux), key)`, the request and the cache. -/
private theorem isOraclePPTOn_prfMultiHandler (hfamily : PseudorandomFunction family) (t j : ℕ) :
    IsOraclePPTOn (handlerInputEncoding t) (encPair encBits (cacheEncoding t))
      (fun x : HandlerInput t => prfMultiHandler family t j x.1.1.1 x.1.2 x.2.1 x.2.2) := by
  let h1 := ComputableInPolyTime.fst (encPair (encPair encUnary encBits) encBits)
    (encPair (encPair (encFinEnum (Fin t)) encBits) (cacheEncoding t))
  let h2 := ComputableInPolyTime.snd (encPair (encPair encUnary encBits) encBits)
    (encPair (encPair (encFinEnum (Fin t)) encBits) (cacheEncoding t))
  let hn := h1.fst'.fst'
  let hquery := h2.fst'.snd'
  let hcache := h2.snd'
  refine IsOraclePPTOn.finite_cases' (tagEncoding := encFinEnum (Fin t))
    (tag := fun x : HandlerInput t => x.2.1.1)
    (branch := fun i x => prfMultiHandler family t j x.1.1.1 x.1.2 (i, x.2.1.2) x.2.2)
    h2.fst'.fst' fun i => ?_
  by_cases hlt : i.val < j
  · simp only [prfMultiHandler, hlt, ↓reduceIte]
    refine IsOraclePPTOn.ite' (hquery.length_bits_comp.unary_eq' hn) ?_ ?_
    · exact (IsPPTOn.memoize (input := handlerInputEncoding t)
        (keyEncoding := encPair (encFinEnum (Fin t)) encBits) (valueEncoding := encBits)
        (compute := fun (x : HandlerInput t) (_ : Fin t × List Bool) =>
          BitString.sampleList x.1.1.1)
        (query := fun x : HandlerInput t => (i, x.2.1.2)) (cache := fun x => x.2.2)
        hn.sampleList ((ComputableInPolyTime.const i).prod hquery) hcache).isOraclePPTOn
    · exact (ComputableInPolyTime.isPPTOn
        (((ComputableInPolyTime.const ([] : List Bool)).prod hcache))).isOraclePPTOn
  by_cases heq : i.val = j
  · simp only [prfMultiHandler, heq, ↓reduceIte, lt_irrefl]
    exact (IsOraclePPTOn.query_take' () hquery hn).map_with'
      (f := fun (x : HandlerInput t) reply => (reply, x.2.2))
      ((ComputableInPolyTime.snd _ _).prod (hcache.comp (ComputableInPolyTime.fst _ _)))
  · simp only [prfMultiHandler, hlt, heq, ↓reduceIte]
    let hblock := (h1.snd'.bitsDropWithInput
      (ComputableInPolyTime.unary_mul' (.const i.val) hn)).bitsTakeWithInput hn
    have hreply := computableInPolyTime_take_ite hn hquery
      (hfamily.polyTime.comp (hblock.prod hquery))
    exact (ComputableInPolyTime.isPPTOn (hreply.prod hcache)).isOraclePPTOn

/-- The hybrid reduction is oracle PPT whenever the multi-key adversary is. -/
theorem isOraclePPT_prfMultiReduction (hfamily : PseudorandomFunction family) (t j : ℕ)
    {adversary : MultiKeyDistinguisher t} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (prfMultiReduction family t j adversary) := by
  let hcaller := ComputableInPolyTime.fst (encPair (encPair encUnary encBits) encBits) encBits
  let hq := ComputableInPolyTime.snd (encPair (encPair encUnary encBits) encBits) encBits
  let hres := (((ComputableInPolyTime.const (8 * t)).unary_add'
    (ComputableInPolyTime.unary_mul' (.const 4) hq.length_bits_comp)).unary_add'
    (ComputableInPolyTime.unary_mul' (.const 2) hcaller.fst'.fst')).unary_add' (.const 8)
  have hrun := hadversary.run_interpret_preprocess_open' (External := Unit)
    (State := MultiKeyCache t) (input := encPair (encPair encUnary encBits) encBits)
    (operationEncoding := encFinEnum (Fin t)) (stateEncoding := cacheEncoding t)
    (handler := fun (caller : (ℕ × List Bool) × List Bool) request cache =>
      prfMultiHandler family t j caller.1.1 caller.2 request cache)
    (prepare := fun caller => caller.1) (initial := fun _ => [])
    (resources := fun caller query => 8 * t + 4 * query.length + 2 * caller.1.1 + 8)
    (ComputableInPolyTime.fst _ _) (isOraclePPTOn_prfMultiHandler hfamily t j) (.const [])
    (fun caller cache => ∀ entry ∈ cache, entry.2.length ≤ caller.1.1) (fun _ => by simp)
    hres ?_
  · exact (((ComputableInPolyTime.const t).unary_mul'
      (.fst _ _)).sampleList.isOraclePPTOn.bind_with
      (hrun.map' (ComputableInPolyTime.fst _ _))).isOraclePPT
  intro caller ⟨i, query⟩ cache hcache result hresult
  dsimp only [cacheEncoding]
  have hkeyLength : (encPair (encFinEnum (Fin t)) encBits (i, query)).length ≤
      2 * t + 1 + query.length := by
    have := length_encFinEnum_lt i
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    rw [length_encPair]
    simp only [encBits_apply]
    omega
  simp only [prfMultiHandler] at hresult
  split_ifs at hresult with hlt hlength heq
  · rw [ProbOracleComp.support_sample, ProbComp.eval_memoize] at hresult
    obtain ⟨hreply, hcache', hgrowth⟩ := memoize_call_size_le
      (encPair (encFinEnum (Fin t)) encBits) encBits
      (fun _ => ProbComp.eval (BitString.sampleList caller.1.1)) (i, query) cache caller.1.1
      (by simpa only [encBits_apply] using hcache) (fun value hvalue => by
        rw [BitString.eval_sampleList] at hvalue
        exact (BitString.length_of_mem_support_uniformList hvalue).le) result hresult
    exact ⟨by simpa only [encBits_apply] using hcache',
      by simp only [encBits_apply] at hreply; omega, by omega⟩
  · simp only [OracleComp.support, OracleComp.supportWith_pure, Set.mem_singleton_iff]
      at hresult
    subst hresult
    exact ⟨hcache, by simp, by dsimp only; omega⟩
  · simp only [OracleComp.mem_supportWith_map_iff] at hresult
    obtain ⟨reply, ⟨raw, _, rfl⟩, rfl⟩ := hresult
    have := List.length_take_le caller.1.1 raw
    exact ⟨hcache, by dsimp only; omega, by dsimp only; omega⟩
  · simp only [OracleComp.support, OracleComp.supportWith_pure, Set.mem_singleton_iff]
      at hresult
    subst hresult
    have := List.length_take_le caller.1.1
      (prfOracle family caller.1.1 (keyBlock caller.1.1 i caller.2) query)
    exact ⟨hcache, by dsimp only; omega, by dsimp only; omega⟩

end Efficiency

/-! ### Correctness of the hybrid reduction -/

section Correctness

variable {family : List Bool → List Bool → List Bool} {t : ℕ}

/-- The reduction's handler after evaluating its private samples, against a deterministic external
channel `external`. -/
private noncomputable def semanticHandler (family : List Bool → List Bool → List Bool)
    (t j n : ℕ) (key : List Bool) (external : List Bool → List Bool)
    (request : Fin t × List Bool) : StateT (MultiKeyCache t) PMF (List Bool) := fun cache =>
  match request with
  | (i, query) =>
    if i.val < j then
      if query.length = n then memoize (fun _ => BitString.uniformList n) (i, query) cache
      else PMF.pure ([], cache)
    else if i.val = j then PMF.pure ((external query).take n, cache)
    else PMF.pure ((prfOracle family n (keyBlock n i key) query).take n, cache)

/-- Against a deterministic external channel, the reduction samples its key and runs the adversary
against `semanticHandler`. -/
private theorem interpret_prfMultiReduction (family : List Bool → List Bool → List Bool)
    (t j n : ℕ) (adversary : MultiKeyDistinguisher t) (external : List Bool → List Bool) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
        (fun request : Unit × List Bool => PMF.pure (external request.2)))
      (prfMultiReduction family t j adversary n []) =
    (BitString.uniformList (t * n)).bind fun key =>
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (semanticHandler family t j n key external)) (adversary n [])).run []).map Prod.fst := by
  simp only [prfMultiReduction, OracleComp.interpret_bind, ProbOracleComp.interpret_sample,
    OracleComp.interpret_map]
  rw [show OracleComp.interpret ProbComp.unifOracle (BitString.sampleList (t * n)) =
    ProbComp.eval (BitString.sampleList (t * n)) from rfl, BitString.eval_sampleList,
    Probability.PMF.monad_bind_eq_bind]
  congr 1 with key : 1
  have hhom : IsMonadHom (ProbOracleComp (fun _ : Unit × List Bool => List Bool)) PMF
      (OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
        (fun request : Unit × List Bool => PMF.pure (external request.2)))) :=
    OracleComp.isMonadHom_evalWith _
  rw [OracleComp.map_run_interpret hhom, PMF.monad_map_eq_map]
  congr 3 with q cache : 2
  rcases q with k | ⟨i, query⟩
  · simp [StateT.lift, ProbOracleComp.interpret_sample, ProbComp.unifFin, PMF.map,
      Function.comp_def]
  · simp only [OracleComp.sumHandler, prfMultiHandler, semanticHandler]
    split_ifs
    · rw [ProbOracleComp.interpret_sample]
      exact (ProbComp.eval_memoize _ _ _).trans (by simp only [BitString.eval_sampleList])
    · simp
    · simp [PMF.monad_map_eq_map]
    · simp

/-- The deterministic answers of the reduction when the random channels below `j` read eager tables
and the keyed channels above `j` use the given blocks. -/
private def eagerOracle (family : List Bool → List Bool → List Bool) (t j n : ℕ)
    (blocks : Fin t → List Bool) (external : List Bool → List Bool)
    (tables : Fin t → BitString n → BitString n) (request : Fin t × List Bool) : List Bool :=
  match request with
  | (i, query) =>
    if i.val < j then randomFunctionOracle n (tables i) query
    else if i.val = j then (external query).take n
    else (prfOracle family n (blocks i) query).take n

/-- The lazy cache of `semanticHandler` is equivalent to eager uniform tables for the channels
below `j`. -/
private theorem run_semanticHandler (family : List Bool → List Bool → List Bool) (t j n : ℕ)
    (key : List Bool) (external : List Bool → List Bool) (program : WordOracleComp (Fin t) Bool) :
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (semanticHandler family t j n key external)) program).run []).map Prod.fst =
    (PMF.uniformOfFintype (Fin t → BitString n → BitString n)).bind fun tables =>
      OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (fun request =>
        PMF.pure (eagerOracle family t j n (fun i => keyBlock n i key) external tables request)))
        program := by
  classical
  let adapter (request : Fin t × List Bool) :
      ProbOracleComp (fun _ : Fin t × BitString n => List Bool) (List Bool) :=
    if request.1.val < j then
      if request.2.length = n then ProbOracleComp.query (request.1, BitString.ofList n request.2)
      else pure []
    else pure (if request.1.val = j then (external request.2).take n
      else (prfOracle family n (keyBlock n request.1 key) request.2).take n)
  let adapted := OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k)) adapter) program
  let keyMap : Fin t × BitString n ↪ Fin t × List Bool :=
    ⟨fun x => (x.1, List.ofFn x.2), fun x y h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (List.ofFn_injective h.2)⟩
  have h := RandomOracle.interpret_prob_eq_memoize_map keyMap List.ofFn
    (fun _ => PMF.uniformOfFintype (BitString n)) (fun _ => BitString.uniformList n)
    (fun _ => rfl) adapted
  -- the memoized side is the semantic handler
  have hlazy : (fun q => OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun key' => memoize (fun _ => BitString.uniformList n) (keyMap key')))
      (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k)) adapter q)) =
      OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (semanticHandler family t j n key external) := by
    funext q
    rcases q with k | ⟨i, query⟩
    · simp [OracleComp.sumHandler, ProbOracleComp.interpret_sample, ProbComp.unifFin]
    · funext cache
      simp only [OracleComp.sumHandler, adapter, semanticHandler]
      split_ifs with hlt hlength heq
      · rw [ProbOracleComp.interpret_query]
        change memoize (fun _ => BitString.uniformList n)
          (i, List.ofFn (BitString.ofList n query)) cache = _
        rw [BitString.ofFn_ofList hlength]
      · rfl
      · rfl
      · rfl
  -- the eager side reads the curried table
  have heager (table : Fin t × BitString n → BitString n) :
      (fun q => OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (fun key' => PMF.pure (List.ofFn (table key'))))
        (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k)) adapter q)) =
      OracleComp.sumHandler ProbComp.unifOracle (fun request => PMF.pure
        (eagerOracle family t j n (fun i => keyBlock n i key) external (Function.curry table)
          request)) := by
    funext q
    rcases q with k | ⟨i, query⟩
    · simp [OracleComp.sumHandler, ProbOracleComp.interpret_sample, ProbComp.unifFin]
    · simp only [OracleComp.sumHandler, adapter, eagerOracle, randomFunctionOracle]
      split_ifs <;> simp [Function.curry]
  simp only [adapted, OracleComp.interpret_interpret, hlazy, heager] at h
  rw [← h, PMF.pi_uniformOfFintype,
    ← PMF.uniformOfFintype_map_equiv (Equiv.curry (Fin t) (BitString n) (BitString n)),
    PMF.bind_map]
  rfl

/-- The blocks of a uniform `t * n`-bit word are independent uniform `n`-bit words. -/
private theorem uniformList_bind_keyBlock {β : Type} (t n : ℕ) (f : (Fin t → List Bool) → PMF β) :
    (BitString.uniformList (t * n)).bind (fun key => f (fun i => keyBlock n i key)) =
      (PMF.uniformOfFintype (Fin t → BitString n)).bind
        (fun keys => f (fun i => List.ofFn (keys i))) := by
  let e : BitString (t * n) ≃ (Fin t → BitString n) :=
    (finProdFinEquiv.arrowCongr (Equiv.refl Bool)).symm.trans (Equiv.curry (Fin t) (Fin n) Bool)
  rw [← PMF.uniformOfFintype_map_equiv e, PMF.bind_map, BitString.uniformList, PMF.bind_map]
  congr 1 with w : 1
  simp only [Function.comp_apply]
  congr 1 with i : 1
  apply List.ext_getElem
  · simp only [keyBlock, List.length_take, List.length_drop, List.length_ofFn]
    have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    omega
  · intro r h₁ h₂
    have hr : r < n := by simpa only [List.length_ofFn] using h₂
    simp only [keyBlock, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    change w _ = w (finProdFinEquiv (i, ⟨r, hr⟩))
    congr 1
    ext
    simp only [finProdFinEquiv_apply_val]
    ring

/-- Keyed replies to valid queries have the key's length. -/
private theorem length_prfOracle_le (hfamily : PseudorandomFunction family) {n : ℕ}
    {key : List Bool} (hkey : key.length = n) (query : List Bool) :
    (prfOracle family n key query).length ≤ n := by
  unfold prfOracle
  split_ifs with hquery
  · exact (hfamily.length_eq key query (hquery.trans hkey.symm)).trans hkey |>.le
  · exact Nat.zero_le _

/-- Table replies have at most `n` bits. -/
private theorem length_randomFunctionOracle_le {n : ℕ} (table : BitString n → BitString n)
    (query : List Bool) : (randomFunctionOracle n table query).length ≤ n := by
  unfold randomFunctionOracle
  split_ifs
  · exact (List.length_ofFn).le
  · exact Nat.zero_le _

/-- The answers of the `j`-th hybrid: random tables below `j`, keyed blocks from `j` on. -/
private def hybridOracle (family : List Bool → List Bool → List Bool) (t j n : ℕ)
    (keys : Fin t → List Bool) (tables : Fin t → BitString n → BitString n)
    (request : Fin t × List Bool) : List Bool :=
  if request.1.val < j then randomFunctionOracle n (tables request.1) request.2
  else prfOracle family n (keys request.1) request.2

/-- The `j`-th hybrid experiment, with eager keys and tables. -/
private noncomputable def hybridGame (family : List Bool → List Bool → List Bool) (t j : ℕ)
    (adversary : MultiKeyDistinguisher t) (n : ℕ) : PMF Bool := do
  let keys ← PMF.uniformOfFintype (Fin t → BitString n)
  let tables ← PMF.uniformOfFintype (Fin t → BitString n → BitString n)
  OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (fun request =>
    PMF.pure (hybridOracle family t j n (fun i => List.ofFn (keys i)) tables request)))
    (adversary n [])

private theorem eval_prfMultiRealGame (family : List Bool → List Bool → List Bool)
    (adversary : MultiKeyDistinguisher t) (n : ℕ) :
    ProbComp.eval (prfMultiRealGame family t adversary n) = hybridGame family t 0 adversary n := by
  simp only [prfMultiRealGame, ProbComp.eval_bind, BitString.eval_sampleList,
    ProbOracleComp.eval_interpret, ProbComp.eval_pure]
  refine (uniformList_bind_keyBlock t n (fun blocks =>
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
      (fun request : Fin t × List Bool =>
        PMF.pure (prfOracle family n (blocks request.1) request.2))) (adversary n []))).trans ?_
  simp only [hybridGame, PMF.monad_bind_eq_bind, hybridOracle, Nat.not_lt_zero, ↓reduceIte,
    PMF.bind_const]

private theorem eval_prfMultiIdealGame (family : List Bool → List Bool → List Bool)
    (adversary : MultiKeyDistinguisher t) (n : ℕ) :
    ProbComp.eval (prfMultiIdealGame t adversary n) = hybridGame family t t adversary n := by
  simp only [pmf_norm, prfMultiIdealGame, hybridGame, hybridOracle, Fin.is_lt, ↓reduceIte,
    PMF.bind_const, ProbComp.eval_uniform, ProbOracleComp.eval_interpret]

/-- Against the real PRF game, the `j`-th reduction is the `j`-th hybrid. -/
private theorem eval_prfRealGame_prfMultiReduction (hfamily : PseudorandomFunction family)
    {j : ℕ} (hj : j < t) (adversary : MultiKeyDistinguisher t) (n : ℕ) :
    ProbComp.eval (prfRealGame family (prfMultiReduction family t j adversary) n) =
      hybridGame family t j adversary n := by
  classical
  simp only [prfRealGame, ProbComp.eval_bind, BitString.eval_sampleList,
    ProbOracleComp.eval_interpret, ProbComp.eval_pure, interpret_prfMultiReduction,
    run_semanticHandler]
  simp only [hybridGame, PMF.monad_bind_eq_bind]
  rw [PMF.bind_uniformOfFintype_update ⟨j, hj⟩, BitString.uniformList, PMF.bind_map]
  congr 1 with value : 1
  refine (uniformList_bind_keyBlock t n (fun blocks =>
    (PMF.uniformOfFintype (Fin t → BitString n → BitString n)).bind fun tables =>
      OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
        (fun request : Fin t × List Bool =>
          PMF.pure (eagerOracle family t j n blocks (prfOracle family n (List.ofFn value)) tables
            request))) (adversary n []))).trans ?_
  congr 1; funext keys; congr 1; funext tables; congr 2; funext req; obtain ⟨i, query⟩ := req
  simp only [eagerOracle, hybridOracle]
  split_ifs with hlt heq
  · rfl
  · have hi : i = ⟨j, hj⟩ := Fin.ext heq
    subst hi
    rw [Function.update_self, List.take_of_length_le
      (length_prfOracle_le hfamily List.length_ofFn query)]
  · have hi : i ≠ ⟨j, hj⟩ := fun h => heq (congrArg Fin.val h)
    rw [Function.update_of_ne hi, List.take_of_length_le
      (length_prfOracle_le hfamily List.length_ofFn query)]

/-- Against the ideal PRF game, the `j`-th reduction is the `(j + 1)`-st hybrid. -/
private theorem eval_prfIdealGame_prfMultiReduction (hfamily : PseudorandomFunction family)
    {j : ℕ} (hj : j < t) (adversary : MultiKeyDistinguisher t) (n : ℕ) :
    ProbComp.eval (prfIdealGame (prfMultiReduction family t j adversary) n) =
      hybridGame family t (j + 1) adversary n := by
  classical
  simp only [prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbOracleComp.eval_interpret, ProbComp.eval_pure, interpret_prfMultiReduction,
    run_semanticHandler]
  simp only [hybridGame, PMF.monad_bind_eq_bind]
  conv_rhs =>
    arg 2
    ext keys
    rw [PMF.bind_uniformOfFintype_update ⟨j, hj⟩]
  conv_rhs => rw [PMF.bind_comm]
  congr 1 with table : 1
  refine (uniformList_bind_keyBlock t n (fun blocks =>
    (PMF.uniformOfFintype (Fin t → BitString n → BitString n)).bind fun tables =>
      OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
        (fun request : Fin t × List Bool =>
          PMF.pure (eagerOracle family t j n blocks (randomFunctionOracle n table) tables
            request))) (adversary n []))).trans ?_
  congr 1; funext keys; congr 1; funext tables; congr 2; funext req; obtain ⟨i, query⟩ := req
  simp only [eagerOracle, hybridOracle]
  by_cases hlt : i.val < j
  · have hi : i ≠ ⟨j, hj⟩ := fun h => by
      subst h
      exact Nat.lt_irrefl j hlt
    have hlt' : i.val < j + 1 := by omega
    simp only [hlt, hlt', ↓reduceIte, Function.update_of_ne hi]
  · by_cases heq : i.val = j
    · have hi : i = ⟨j, hj⟩ := Fin.ext heq
      subst hi
      simp only [lt_irrefl, lt_add_one, ↓reduceIte, Function.update_self]
      rw [List.take_of_length_le (length_randomFunctionOracle_le _ _)]
    · have hlt' : ¬i.val < j + 1 := by omega
      simp only [hlt, heq, hlt', ↓reduceIte]
      rw [List.take_of_length_le (length_prfOracle_le hfamily List.length_ofFn query)]

/-- **Multi-key PRF hybrid** ([BonehShoup2023], Exercise 4.26): the advantage of a multi-key
adversary is at most the sum of the PRF advantages of the `t` hybrid reductions. -/
theorem advantage_prfMultiRealGame_prfMultiIdealGame_le (hfamily : PseudorandomFunction family)
    (adversary : MultiKeyDistinguisher t) (n : ℕ) :
    Game.advantage (ProbComp.eval (prfMultiRealGame family t adversary n))
        (ProbComp.eval (prfMultiIdealGame t adversary n)) ≤
      ∑ j ∈ Finset.range t,
        Game.advantage
          (ProbComp.eval (prfRealGame family (prfMultiReduction family t j adversary) n))
          (ProbComp.eval (prfIdealGame (prfMultiReduction family t j adversary) n)) := by
  rw [eval_prfMultiRealGame family adversary n, eval_prfMultiIdealGame family adversary n]
  refine (Game.advantage_hybrid_le_sum (fun j => hybridGame family t j adversary n) t).trans
    (Finset.sum_le_sum fun j hj => le_of_eq ?_)
  have hj : j < t := Finset.mem_range.mp hj
  rw [eval_prfRealGame_prfMultiReduction hfamily hj, eval_prfIdealGame_prfMultiReduction hfamily hj]

/-- **Independently keyed copies of a pseudorandom function are pseudorandom**
([BonehShoup2023], Exercise 4.26, for a constant number of keys): for every fixed number `t` of
keys, no oracle-PPT adversary distinguishes `t` keyed copies from `t` independent uniform random
functions. The exercise allows a polynomially bounded number of keys; this statement does not. -/
theorem PseudorandomFunction.multiKey (hfamily : PseudorandomFunction family) (t : ℕ) :
    Game.Indistinguishable
      (fun adversary n => ProbComp.eval (prfMultiRealGame family t adversary n))
      (fun adversary n => ProbComp.eval (prfMultiIdealGame t adversary n))
      (IsOraclePPT encBool) := by
  intro adversary hadversary
  refine negligible_of_le (Negligible.sum (Finset.range t) fun j _ =>
    hfamily.secure _ (isOraclePPT_prfMultiReduction hfamily t j hadversary)) fun n => ?_
  simpa only [Finset.sum_apply] using
    advantage_prfMultiRealGame_prfMultiIdealGame_le hfamily adversary n

end Correctness

end Cslib.Crypto
