/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Computability/RecursiveIn.lean`)

public import CslibFrontier.Init
public import Mathlib.Computability.TuringDegree
public import Mathlib.Data.Set.Countable

/-!
# Codes for oracle computations

Mathlib defines `Nat.RecursiveIn O f` inductively, as the closure of the basic functions and the
oracles in `O` under pairing, composition, primitive recursion and unbounded search. That is the
right notion of relative computability, but diagonal constructions need an enumeration of the
oracle computations together with finite, stage-bounded approximations. This file supplies both:
an oracle analogue `Nat.RecursiveIn.Code` of Mathlib's `Nat.Partrec.Code`, with evaluation
`Code.eval g` relative to an oracle `g` and stage-bounded evaluation `Code.evaln σ k` against a
finite oracle prefix `σ : List ℕ`.

The stage-bounded evaluator queries the oracle only below the stage: at stage `k` it reads at most
the first `k` entries of `σ` (`Code.evaln_take`). Its completeness for total oracles gives the
*use principle* (`Code.exists_use`): a convergent oracle computation depends on only finitely many
oracle values.

## Main definitions

* `Nat.RecursiveIn.Code`: codes for oracle computations, with a `Denumerable` instance.
* `Nat.RecursiveIn.Code.eval`: evaluation of a code relative to a partial oracle.
* `Nat.RecursiveIn.Code.evaln`: stage-bounded evaluation against a finite oracle prefix.
* `Nat.RecursiveIn.Code.prefixOf`: the finite prefix of length `N` of a total oracle.

## Main results

* `Nat.RecursiveIn.Code.exists_code`: `Nat.RecursiveIn {g} f` holds if and only if `f` is the
  evaluation of some code relative to `g`.
* `Nat.RecursiveIn.Code.turingReducible_iff_exists_code`: the same statement for `f ≤ᵀ g`.
* `Nat.RecursiveIn.Code.evaln_sound`, `Nat.RecursiveIn.Code.evaln_complete`: stage-bounded
  evaluation is sound for any oracle agreeing with the prefix, and complete for total oracles.
* `Nat.RecursiveIn.Code.evaln_take`: a stage-`k` computation reads only the first `k` oracle
  values.
* `Nat.RecursiveIn.Code.exists_use`: the use principle.
* `Nat.RecursiveIn.countable_setOf_turingReducible`, `TuringDegree.countable_Iic`: a function
  or degree has only countably many predecessors.

## Implementation notes

The open Mathlib PR
[mathlib4#38973](https://github.com/leanprover-community/mathlib4/pull/38973)
(`Mathlib/Computability/SingleOracle`) proposes overlapping infrastructure: oracle codes
`Oracle.Single.Code` with `eval` and a relativized `evaln`, a code for `evaln`, and the jump,
related back to `RecursiveIn`. Its oracles are total functions and its `evaln` reads the whole
oracle. This file instead builds on merged Mathlib's `Nat.RecursiveIn` with partial oracles, and
its `evaln` runs against a finite prefix `List ℕ`, which gives `evaln_take` and `exists_use`
directly. Upstreaming must be reconciled with that PR (see `UPSTREAM.md`).

## References

* [S. C. Kleene and E. L. Post, *The upper semi-lattice of degrees of recursive
  unsolvability*][KleenePost1954]
* [R. I. Soare, *Recursively Enumerable Sets and Degrees*][Soare1987]
-/

public section

open Encodable Denumerable

namespace Nat.RecursiveIn

/-- Codes for computations relative to an oracle. The constructors mirror the constructors of
`Nat.RecursiveIn`, with `oracle` standing for the single oracle `g` passed to `Code.eval`. The
`rfind'` constructor follows Mathlib's `Nat.Partrec.Code.rfind'`. -/
inductive Code : Type
  | zero : Code
  | succ : Code
  | left : Code
  | right : Code
  | oracle : Code
  | pair : Code → Code → Code
  | comp : Code → Code → Code
  | prec : Code → Code → Code
  | rfind' : Code → Code

namespace Code

instance instInhabited : Inhabited Code := ⟨zero⟩

/-- The Gödel numbering of oracle codes, following `Nat.Partrec.Code.encodeCode` with the extra
atomic code `oracle` numbered `4`. -/
@[expose] def encodeCode : Code → ℕ
  | zero => 0
  | succ => 1
  | left => 2
  | right => 3
  | oracle => 4
  | pair cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 5
  | comp cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg) + 1) + 5
  | prec cf cg => (2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 1) + 5
  | rfind' cf => (2 * (2 * encodeCode cf + 1) + 1) + 5

/-- The inverse of `encodeCode`. -/
@[expose] def ofNatCode : ℕ → Code
  | 0 => zero
  | 1 => succ
  | 2 => left
  | 3 => right
  | 4 => oracle
  | n + 5 =>
    let m := n.div2.div2
    have hm : m < n + 5 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    match n.bodd, n.div2.bodd with
    | false, false => pair (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | false, true => comp (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true, false => prec (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true, true => rfind' (ofNatCode m)

private theorem encode_ofNatCode : ∀ n, encodeCode (ofNatCode n) = n
  | 0 => by simp [ofNatCode, encodeCode]
  | 1 => by simp [ofNatCode, encodeCode]
  | 2 => by simp [ofNatCode, encodeCode]
  | 3 => by simp [ofNatCode, encodeCode]
  | 4 => by simp [ofNatCode, encodeCode]
  | n + 5 => by
    let m := n.div2.div2
    have hm : m < n + 5 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    have IH := encode_ofNatCode m
    have IH1 := encode_ofNatCode m.unpair.1
    have IH2 := encode_ofNatCode m.unpair.2
    conv_rhs => rw [← Nat.bit_bodd_div2 n, ← Nat.bit_bodd_div2 n.div2]
    simp only [ofNatCode.eq_6]
    cases n.bodd <;> cases n.div2.bodd <;>
      simp [m, encodeCode, IH, IH1, IH2, Nat.bit_val]

/-- Oracle codes are denumerable, via `encodeCode` and `ofNatCode`. -/
instance instDenumerable : Denumerable Code :=
  mk'
    { toFun := encodeCode
      invFun := ofNatCode
      left_inv c := by induction c <;> simp [encodeCode, ofNatCode, Nat.div2_val, *]
      right_inv := private encode_ofNatCode }

theorem encodeCode_eq : encode = encodeCode :=
  rfl

theorem ofNatCode_eq : ofNat Code = ofNatCode :=
  rfl

/-- The evaluation of an oracle code relative to the oracle `g`. Apart from the `oracle` case,
which returns `g`, this is Mathlib's `Nat.Partrec.Code.eval`. -/
@[expose] def eval (g : ℕ →. ℕ) : Code → ℕ →. ℕ
  | zero => pure 0
  | succ => Nat.succ
  | left => ↑fun n : ℕ => n.unpair.1
  | right => ↑fun n : ℕ => n.unpair.2
  | oracle => g
  | pair cf cg => fun n => Nat.pair <$> eval g cf n <*> eval g cg n
  | comp cf cg => fun n => eval g cg n >>= eval g cf
  | prec cf cg =>
    Nat.unpaired fun a n =>
      n.rec (eval g cf a) fun y IH => do
        let i ← IH
        eval g cg (Nat.pair a (Nat.pair y i))
  | rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun m => m = 0) <$> eval g cf (Nat.pair a (n + m))).map (· + m)

/-- Stage-bounded evaluation of an oracle code against the finite oracle prefix `σ`.
`evaln σ k c n` is defined only for inputs `n < k`, it runs with recursion depth bounded by `k`,
and an oracle query at `n` returns `σ[n]?`, so it fails if `σ` is too short. This is Mathlib's
`Nat.Partrec.Code.evaln` with an `oracle` case. -/
@[expose] def evaln (σ : List ℕ) : ℕ → Code → ℕ → Option ℕ
  | 0, _ => fun _ => Option.none
  | k + 1, zero => fun n => do
    guard (n ≤ k)
    return 0
  | k + 1, succ => fun n => do
    guard (n ≤ k)
    return (Nat.succ n)
  | k + 1, left => fun n => do
    guard (n ≤ k)
    return n.unpair.1
  | k + 1, right => fun n => do
    guard (n ≤ k)
    pure n.unpair.2
  | k + 1, oracle => fun n => do
    guard (n ≤ k)
    σ[n]?
  | k + 1, pair cf cg => fun n => do
    guard (n ≤ k)
    Nat.pair <$> evaln σ (k + 1) cf n <*> evaln σ (k + 1) cg n
  | k + 1, comp cf cg => fun n => do
    guard (n ≤ k)
    let x ← evaln σ (k + 1) cg n
    evaln σ (k + 1) cf x
  | k + 1, prec cf cg => fun n => do
    guard (n ≤ k)
    n.unpaired fun a n =>
      n.casesOn (evaln σ (k + 1) cf a) fun y => do
        let i ← evaln σ k (prec cf cg) (Nat.pair a y)
        evaln σ (k + 1) cg (Nat.pair a (Nat.pair y i))
  | k + 1, rfind' cf => fun n => do
    guard (n ≤ k)
    n.unpaired fun a m => do
      let x ← evaln σ (k + 1) cf (Nat.pair a m)
      if x = 0 then
        pure m
      else
        evaln σ k (rfind' cf) (Nat.pair a (m + 1))

/-- A stage-`k` computation is defined only on inputs below `k`. -/
theorem evaln_bound {σ : List ℕ} : ∀ {k c n x}, x ∈ evaln σ k c n → n < k
  | 0, c, n, x, h => by simp [evaln] at h
  | k + 1, c, n, x, h => by
    suffices ∀ {o : Option ℕ}, x ∈ do { guard (n ≤ k); o } → n < k + 1 by
      cases c <;> rw [evaln] at h <;> exact this h
    simpa [Option.bind_eq_some_iff] using Nat.lt_succ_of_le

/-- Monotonicity of stage-bounded evaluation in the stage and the oracle prefix, where the larger
prefix need only agree with the smaller one below the smaller stage. -/
theorem evaln_mono_of_agree {σ₁ σ₂ : List ℕ} {K : ℕ}
    (hσ : ∀ i < K, ∀ y, σ₁[i]? = some y → σ₂[i]? = some y) :
    ∀ {k₁ k₂ c n x}, k₁ ≤ K → k₁ ≤ k₂ → x ∈ evaln σ₁ k₁ c n → x ∈ evaln σ₂ k₂ c n
  | 0, k₂, c, n, x, _, _, h => by simp [evaln] at h
  | k + 1, k₂ + 1, c, n, x, hK, hl, h => by
    have hl' := Nat.le_of_succ_le_succ hl
    have hK' : k ≤ K := Nat.le_of_succ_le hK
    have :
      ∀ {k k₂ n x : ℕ} {o₁ o₂ : Option ℕ},
        k ≤ k₂ → (n ≤ k → x ∈ o₁ → x ∈ o₂) →
          x ∈ do { guard (n ≤ k); o₁ } → x ∈ do { guard (n ≤ k₂); o₂ } := by
      simp only [Option.mem_def, bind, Option.bind_eq_some_iff, Option.guard_eq_some',
        exists_and_left, exists_const, and_imp]
      introv h h₁ h₂ h₃
      exact ⟨le_trans h₂ h, h₁ h₂ h₃⟩
    simp only [Option.mem_def] at h ⊢
    induction c generalizing x n <;> rw [evaln] at h ⊢ <;> refine this hl' (fun hn h => ?_) h
    on_goal 1 2 3 4 => exact h
    case oracle => exact hσ n (by omega) x h
    case pair cf cg hf hg _ =>
      simp only [Seq.seq, Option.map_eq_map, Option.mem_def, Option.bind_eq_some_iff,
          Option.map_eq_some_iff, exists_exists_and_eq_and] at h ⊢
      exact h.imp fun a => And.imp (hf _ _) <| Exists.imp fun b => And.imp_left (hg _ _)
    case comp cf cg hf hg _ =>
      simp only [bind, Option.mem_def, Option.bind_eq_some_iff] at h ⊢
      exact h.imp fun a => And.imp (hg _ _) (hf _ _)
    case prec cf cg hf hg _ =>
      revert h
      simp only [unpaired, bind, Option.mem_def]
      induction n.unpair.2 with
      | zero => apply hf
      | succ _ _ =>
        simp only [Option.bind_eq_some_iff, forall_exists_index, and_imp]
        exact fun y h₁ h₂ ↦ ⟨y, evaln_mono_of_agree hσ hK' hl' h₁, hg _ _ h₂⟩
    case rfind' cf hf _ =>
      simp only [unpaired, bind, pair_unpair, Option.pure_def, Option.mem_def,
          Option.bind_eq_some_iff] at h ⊢
      refine h.imp fun x => And.imp (hf _ _) ?_
      by_cases x0 : x = 0 <;> simp only [x0, ↓reduceIte, Option.some.injEq, imp_self]
      exact evaln_mono_of_agree hσ hK' hl'

/-- Stage-bounded evaluation is monotone in the stage and in the oracle prefix. -/
theorem evaln_mono {σ₁ σ₂ : List ℕ} (hσ : σ₁ <+: σ₂) {k₁ k₂ c n x} (hl : k₁ ≤ k₂)
    (h : x ∈ evaln σ₁ k₁ c n) : x ∈ evaln σ₂ k₂ c n :=
  evaln_mono_of_agree (K := k₁) (fun i _ y hy => by
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hy
    exact List.prefix_iff_getElem?.1 hσ i hi) le_rfl hl h

/-- The use of a stage-`k` computation is below `k`: it reads only the first `k` oracle values. -/
theorem evaln_take (σ : List ℕ) (k : ℕ) (c : Code) (n : ℕ) :
    evaln (σ.take k) k c n = evaln σ k c n := by
  refine Option.ext fun x => ⟨fun h => ?_, fun h => ?_⟩
  · exact evaln_mono (List.take_prefix k σ) le_rfl h
  · refine evaln_mono_of_agree (K := k) (fun i hi y hy => ?_) le_rfl le_rfl h
    rwa [List.getElem?_take_of_lt hi]

-- As in Mathlib's `Nat.Partrec.Code.evaln_sound`: the `simp` calls unfold `PFun` coercions.
set_option backward.isDefEq.respectTransparency false in
/-- Soundness of stage-bounded evaluation: a result computed against the prefix `σ` is a value of
the evaluation relative to every oracle `g` extending `σ`. -/
theorem evaln_sound {g : ℕ →. ℕ} {σ : List ℕ} (hσ : ∀ i (h : i < σ.length), σ[i] ∈ g i) :
    ∀ {k c n x}, x ∈ evaln σ k c n → x ∈ eval g c n
  | 0, _, n, x, h => by simp [evaln] at h
  | k + 1, c, n, x, h => by
    induction c generalizing x n <;>
    simp only [eval, evaln, Option.bind_eq_bind, Option.mem_def, Option.bind_eq_some_iff,
      Option.guard_eq_some', exists_const] at h ⊢
    case zero => simpa [pure, PFun.pure] using h.2.symm
    case succ => simpa using h.2.symm
    case left => simpa using h.2.symm
    case right => simpa using h.2.symm
    case oracle =>
      obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.1 h.2
      exact hσ n hn
    case pair cf cg hf hg =>
      simp_rw [Seq.seq, Option.bind_eq_some_iff, Option.map_eq_map, Option.map_eq_some_iff,
        exists_exists_and_eq_and] at h
      simp_rw [Seq.seq, Part.map_eq_map, Part.bind_map, Part.mem_bind_iff, Part.mem_map_iff]
      obtain ⟨_, ⟨y, ef, z, eg, rfl⟩⟩ := h
      exact ⟨_, hf _ _ ef, _, hg _ _ eg, rfl⟩
    case comp cf cg hf hg =>
      simp only [Part.bind_eq_bind, Part.mem_bind_iff]
      obtain ⟨_, ⟨y, eg, ef⟩⟩ := h
      exact ⟨_, hg _ _ eg, hf _ _ ef⟩
    case prec cf cg hf hg =>
      simp only [unpaired, Part.bind_eq_bind] at h ⊢
      obtain ⟨_, h⟩ := h
      revert h
      induction n.unpair.2 generalizing x with
      | zero =>
        simp only [rec_zero]
        apply hf
      | succ m IH =>
        simp only [Option.bind_eq_some_iff, Part.mem_bind_iff, forall_exists_index, and_imp]
        refine fun y h₁ h₂ ↦ ⟨y, IH _ ?_, hg _ _ h₂⟩
        have := evaln_mono (List.prefix_refl σ) k.le_succ h₁
        simp only [evaln, unpaired, unpair_pair, Option.bind_eq_bind, Option.mem_def,
          Option.bind_eq_some_iff, Option.guard_eq_some', exists_const] at this
        exact this.2
    case rfind' cf hf =>
      simp only [Part.map_eq_map, Part.mem_map_iff, Nat.mem_rfind]
      obtain ⟨_, ⟨m, h₁, h₂⟩⟩ := h
      split_ifs at h₂ with m0
      · exact ⟨0, ⟨by simpa [m0] using hf _ _ h₁, fun {m} ↦ (Nat.not_lt_zero _).elim⟩,
          by simpa using h₂⟩
      · have := evaln_sound hσ h₂
        simp only [eval, Part.map_eq_map, Part.mem_map_iff, Nat.mem_rfind] at this
        rcases this with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
        refine
          ⟨y + 1, ⟨by simpa [add_comm, add_left_comm] using hy₁, fun {i} im => ?_⟩, by
            simp [add_comm, add_left_comm]⟩
        rcases i with - | i
        · exact ⟨m, by simpa using hf _ _ h₁, by simp [m0]⟩
        · rcases hy₂ (Nat.lt_of_succ_lt_succ im) with ⟨z, hz, z0⟩
          exact ⟨z, by simpa [add_comm, add_left_comm] using hz, by simp [z0]⟩

/-- The prefix of length `N` of a total oracle `f`, as a list of values `f 0, …, f (N - 1)`. -/
@[expose] def prefixOf (f : ℕ → ℕ) (N : ℕ) : List ℕ := (List.range N).map f

@[simp]
theorem length_prefixOf (f : ℕ → ℕ) (N : ℕ) : (prefixOf f N).length = N := by
  simp [prefixOf]

@[simp]
theorem getElem_prefixOf (f : ℕ → ℕ) {N i : ℕ} (h : i < (prefixOf f N).length) :
    (prefixOf f N)[i] = f i := by
  simp [prefixOf]

theorem prefixOf_prefix (f : ℕ → ℕ) {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) :
    prefixOf f N₁ <+: prefixOf f N₂ := by
  rw [List.prefix_iff_eq_take]
  simp [prefixOf, ← List.map_take, List.take_range, min_eq_left h]

/-- Every total oracle extends each of its prefixes. -/
theorem prefixOf_mem (f : ℕ → ℕ) (N : ℕ) :
    ∀ i (h : i < (prefixOf f N).length), (prefixOf f N)[i] ∈ (f : ℕ →. ℕ) i := by
  intro i h
  rw [getElem_prefixOf]
  exact Part.mem_some _

-- As in Mathlib's `Nat.Partrec.Code.evaln_complete`: the `simp` calls unfold `PFun` coercions.
set_option backward.isDefEq.respectTransparency false in
/-- Completeness of stage-bounded evaluation for total oracles: every convergent computation
relative to `f` converges at some stage against some finite prefix of `f`. -/
theorem evaln_complete {f : ℕ → ℕ} {c n x} :
    x ∈ eval (f : ℕ →. ℕ) c n ↔ ∃ N k, x ∈ evaln (prefixOf f N) k c n := by
  refine ⟨fun h => ?_, fun ⟨N, k, h⟩ => evaln_sound (prefixOf_mem f N) h⟩
  rsuffices ⟨N, k, h⟩ : ∃ N k, x ∈ evaln (prefixOf f N) (k + 1) c n
  · exact ⟨N, k + 1, h⟩
  induction c generalizing n x with
  | oracle =>
    refine ⟨n + 1, n, ?_⟩
    simp only [eval, PFun.coe_val, Part.mem_some_iff] at h
    subst h
    simp [evaln, prefixOf]
  | pair cf cg hf hg =>
    simp only [eval, Seq.seq, Part.map_eq_map, Part.mem_bind_iff, Part.mem_map_iff,
      evaln, Option.map_eq_map, Option.bind_eq_bind, Option.mem_def, Option.bind_eq_some_iff,
      Option.guard_eq_some', Option.map_eq_some_iff, exists_exists_and_eq_and,
      exists_const] at h ⊢
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    obtain ⟨N₁, k₁, hk₁⟩ := hf hx; obtain ⟨N₂, k₂, hk₂⟩ := hg hy
    exact ⟨max N₁ N₂, max k₁ k₂, ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁, _,
      evaln_mono (prefixOf_prefix f (le_max_left _ _)) (Nat.succ_le_succ <| le_max_left _ _) hk₁,
      _,
      evaln_mono (prefixOf_prefix f (le_max_right _ _)) (Nat.succ_le_succ <| le_max_right _ _)
        hk₂, rfl⟩⟩
  | comp cf cg hf hg =>
    simp only [eval, Part.bind_eq_bind, Part.mem_bind_iff, evaln, Option.bind_eq_bind,
      Option.mem_def, Option.bind_eq_some_iff, Option.guard_eq_some', exists_const] at h ⊢
    obtain ⟨y, hy, hx⟩ := h
    obtain ⟨N₁, k₁, hk₁⟩ := hg hy; obtain ⟨N₂, k₂, hk₂⟩ := hf hx
    exact ⟨max N₁ N₂, max k₁ k₂, ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁, _,
      evaln_mono (prefixOf_prefix f (le_max_left _ _)) (Nat.succ_le_succ <| le_max_left _ _) hk₁,
      evaln_mono (prefixOf_prefix f (le_max_right _ _)) (Nat.succ_le_succ <| le_max_right _ _)
        hk₂⟩⟩
  | prec cf cg hf hg =>
    simp only [eval, unpaired, evaln, Option.bind_eq_bind, Option.mem_def,
      Option.bind_eq_some_iff, Option.guard_eq_some', exists_const] at h ⊢
    revert h
    generalize n.unpair.1 = n₁; generalize n.unpair.2 = n₂
    induction n₂ generalizing x n with
    | zero =>
      intro h
      obtain ⟨N, k, hk⟩ := hf h
      exact ⟨N, _, le_max_left _ _,
        evaln_mono (List.prefix_refl _) (Nat.succ_le_succ <| le_max_right _ _) hk⟩
    | succ m IH =>
      simp only [Part.bind_eq_bind, Part.mem_bind_iff, forall_exists_index, and_imp,
        Option.bind_eq_some_iff]
      intro y hy hx
      rcases IH hy with ⟨N₁, k₁, nk₁, hk₁⟩
      rcases hg hx with ⟨N₂, k₂, hk₂⟩
      refine
        ⟨max N₁ N₂, (max k₁ k₂).succ,
          Nat.le_succ_of_le <| le_max_of_le_left <|
            le_trans (le_max_left _ (Nat.pair n₁ m)) nk₁, y,
          evaln_mono (prefixOf_prefix f (le_max_left _ _))
            (Nat.succ_le_succ <| le_max_left _ _) ?_,
          evaln_mono (prefixOf_prefix f (le_max_right _ _))
            (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_right _ _) hk₂⟩
      simp only [evaln, bind, unpaired, unpair_pair, Option.mem_def, Option.bind_eq_some_iff,
        Option.guard_eq_some', exists_and_left, exists_const]
      exact ⟨le_trans (le_max_right _ _) nk₁, hk₁⟩
  | rfind' cf hf =>
    simp only [eval, Part.map_eq_map, Part.mem_map_iff, Nat.mem_rfind,
      decide_eq_false_iff_not] at h ⊢
    rcases h with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    suffices ∃ N k, y + n.unpair.2 ∈
        evaln (prefixOf f N) (k + 1) (rfind' cf) (Nat.pair n.unpair.1 n.unpair.2) by
      simpa [evaln, Option.bind_eq_some_iff]
    revert hy₁ hy₂
    generalize n.unpair.2 = m
    intro hy₁ hy₂
    induction y generalizing m with simp only [evaln, unpair_pair, Option.bind_eq_bind,
      Option.mem_def, Option.bind_eq_some_iff, Option.guard_eq_some', exists_const]
    | zero =>
      simp only [zero_add, decide_eq_true_eq, exists_eq_right] at hy₁
      rcases hf hy₁ with ⟨N, k, hk⟩
      exact ⟨N, _, Nat.le_of_lt_succ <| evaln_bound hk, _, hk, by simp⟩
    | succ y IH =>
      rcases hy₂ (Nat.succ_pos _) with ⟨a, ha, a0⟩
      rcases hf ha with ⟨N₁, k₁, hk₁⟩
      rcases IH m.succ (by simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using hy₁)
        fun {i} hi ↦ by
          simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using
            hy₂ (Nat.succ_lt_succ hi) with ⟨N₂, k₂, hk₂⟩
      use max N₁ N₂, (max k₁ k₂).succ
      rw [zero_add] at hk₁
      use Nat.le_succ_of_le <| le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁
      use a
      use evaln_mono (prefixOf_prefix f (le_max_left _ _))
        (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_left _ _) hk₁
      simpa [a0, add_comm, add_left_comm] using
        evaln_mono (prefixOf_prefix f (le_max_right _ _)) (Nat.succ_le_succ <| le_max_right _ _)
          hk₂
  | _ =>
    refine ⟨0, ?_⟩
    simp only [eval, evaln, pure, PFun.pure, PFun.coe_val, Part.mem_some_iff, Option.bind_eq_bind,
      Option.mem_def, Option.bind_eq_some_iff, Option.guard_eq_some', Option.some.injEq,
      exists_const, exists_and_right] at h ⊢
    exact ⟨⟨_, le_rfl⟩, h.symm⟩

/-- Completeness with a single stage parameter: a convergent computation relative to the total
oracle `f` converges at some stage `s` against the prefix of `f` of length `s`. -/
theorem mem_eval_iff_exists_evaln {f : ℕ → ℕ} {c n x} :
    x ∈ eval (f : ℕ →. ℕ) c n ↔ ∃ s, x ∈ evaln (prefixOf f s) s c n := by
  refine ⟨fun h => ?_, fun ⟨s, h⟩ => evaln_complete.2 ⟨s, s, h⟩⟩
  obtain ⟨N, k, h⟩ := evaln_complete.1 h
  exact ⟨max N k, evaln_mono (prefixOf_prefix f (le_max_left _ _)) (le_max_right _ _) h⟩

/-- Evaluation relative to a total oracle is the limit of the stage-bounded approximations. -/
theorem eval_eq_rfindOpt (f : ℕ → ℕ) (c : Code) (n : ℕ) :
    eval (f : ℕ →. ℕ) c n = Nat.rfindOpt fun s => evaln (prefixOf f s) s c n :=
  Part.ext fun x => by
    refine mem_eval_iff_exists_evaln.trans (Nat.rfindOpt_mono ?_).symm
    intro a m n hl
    exact evaln_mono (prefixOf_prefix f hl) hl

/-- The use principle: if a computation relative to the total oracle `f` converges, then there is
a bound `N` such that the computation converges to the same value relative to every total oracle
agreeing with `f` below `N`. -/
theorem exists_use {f : ℕ → ℕ} {c n x} (h : x ∈ eval (f : ℕ →. ℕ) c n) :
    ∃ N, ∀ g : ℕ → ℕ, (∀ i < N, g i = f i) → x ∈ eval (g : ℕ →. ℕ) c n := by
  obtain ⟨N, k, hk⟩ := evaln_complete.1 h
  refine ⟨N, fun g hg => evaln_sound (fun i hi => ?_) hk⟩
  have hiN : i < N := by simpa using hi
  rw [getElem_prefixOf, ← hg i hiN]
  exact Part.mem_some _

end Code

open Code

/-- `Nat.RecursiveIn O` is closed under the unbounded search with offset used by
`Code.rfind'`. -/
theorem rfind' {O : Set (ℕ →. ℕ)} {f : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) :
    Nat.RecursiveIn O
      (Nat.unpaired fun a m =>
        (Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + m))).map (· + m)) := by
  have hq : Nat.Primrec fun p => Nat.pair p.unpair.1.unpair.1 (p.unpair.2 + p.unpair.1.unpair.2) :=
    Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.left)
      ((Nat.Primrec.add.comp (Nat.Primrec.pair Nat.Primrec.right
        (Nat.Primrec.right.comp Nat.Primrec.left))).of_eq fun n => by simp)
  have h1 := hf.comp hq.recursiveIn
  have h2 := Nat.RecursiveIn.rfind h1
  have hadd : Nat.Primrec fun p => p.unpair.1 + p.unpair.2.unpair.2 :=
    (Nat.Primrec.add.comp (Nat.Primrec.pair Nat.Primrec.left
      (Nat.Primrec.right.comp Nat.Primrec.right))).of_eq fun n => by simp
  have h3 := hadd.recursiveIn.comp (h2.pair (Nat.Primrec.id.recursiveIn (O := O)))
  have hb : ∀ x, (Part.some x >>= f) = f x := fun x => Part.bind_some x f
  refine h3.of_eq fun n => ?_
  simp [Seq.seq, Nat.unpaired, Part.map_eq_map, Part.bind_eq_bind, hb,
    Part.bind_some_eq_map, Part.map_map, Function.comp_def]

namespace Code

/-- A partial function is recursive in the single oracle `g` if and only if it is the evaluation
of some oracle code relative to `g`. This is the oracle analogue of
`Nat.Partrec.Code.exists_code`. -/
theorem exists_code {g f : ℕ →. ℕ} : Nat.RecursiveIn {g} f ↔ ∃ c : Code, eval g c = f := by
  refine ⟨fun h => ?_, ?_⟩
  · induction h with
    | zero => exact ⟨zero, rfl⟩
    | succ => exact ⟨succ, rfl⟩
    | left => exact ⟨left, rfl⟩
    | right => exact ⟨right, rfl⟩
    | oracle g' hg' =>
      rw [Set.mem_singleton_iff.1 hg']
      exact ⟨oracle, rfl⟩
    | pair pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨pair cf cg, rfl⟩
    | comp pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨comp cf cg, rfl⟩
    | prec pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨prec cf cg, rfl⟩
    | rfind pf hf =>
      rcases hf with ⟨cf, rfl⟩
      refine ⟨comp (rfind' cf) (pair (pair left right) zero), ?_⟩
      funext n
      simp [eval, Seq.seq, pure, PFun.pure, Part.map_id']
  · rintro ⟨c, rfl⟩
    induction c with
    | zero => exact .zero
    | succ => exact .succ
    | left => exact .left
    | right => exact .right
    | oracle => exact .oracle g rfl
    | pair cf cg pf pg => exact pf.pair pg
    | comp cf cg pf pg => exact pf.comp pg
    | prec cf cg pf pg => exact pf.prec pg
    | rfind' cf pf => exact Nat.RecursiveIn.rfind' pf

open scoped Computability in
/-- `f ≤ᵀ g` holds if and only if `f` is the evaluation of some oracle code relative to `g`. -/
theorem turingReducible_iff_exists_code {f g : ℕ →. ℕ} : f ≤ᵀ g ↔ ∃ c : Code, eval g c = f :=
  RecursiveIn.iff_nat.trans exists_code

end Code

open scoped Computability in
/-- Only countably many partial functions are Turing reducible to a given oracle. -/
theorem countable_setOf_turingReducible (g : ℕ →. ℕ) : {f | f ≤ᵀ g}.Countable := by
  have : {f | f ≤ᵀ g} = Set.range (eval g) := by
    ext f
    exact turingReducible_iff_exists_code
  rw [this]
  exact Set.countable_range _

end Nat.RecursiveIn

/-- A Turing degree has only countably many degrees below it. -/
theorem TuringDegree.countable_Iic (d : TuringDegree) : (Set.Iic d).Countable := by
  induction d using Antisymmetrization.ind with
  | _ g =>
  refine ((Nat.RecursiveIn.countable_setOf_turingReducible g).image
    (toAntisymmetrization _)).mono ?_
  intro d hd
  induction d using Antisymmetrization.ind with
  | _ f => exact ⟨f, hd, rfl⟩
