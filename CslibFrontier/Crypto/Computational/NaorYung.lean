/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Crypto.Computational.TargetCollisionResistant
public import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Tactic.PolyTime.Init
import CslibFrontier.Probability.PMF.Finiteness
import CslibFrontier.Crypto.Game.Order

/-!
# Naor–Yung universal one-way hash functions from one-way permutations

Naor and Yung ([NaorYung1989], Section 3; §§2.1–2.3 in the March 13, 1995 manuscript revision;
see also [Goldreich2004], Section 6.4.3.2, June 2003 chapter draft Construction 6.4.20 and
Proposition 6.4.21) construct a universal one-way (target collision-resistant) hash family from any
one-way permutation `f` without collision-free trapdoors.
Rather than pairing `f` with an `(m - 1) × m` affine/Toeplitz universal hash, this module uses a
direct `{0, δ}`-coset pivot-deletion quotient on `m`-bit shift keys `δ` so that the single-step
reduction has exact loss `1` and zero additive error:

1. **One-bit quotient (`m → m - 1`)**: given a shift `δ ∈ {0, 1}^m` whose first `true` coordinate is
   `p < m` (`0` when `δ = 0^m`), quotient `{0, 1}^m` by `{0, δ}` by XORing with `δ` whenever bit `p`
   is `true` (`naorYungCanon`) and deleting bit `p` (`naorYungShrink`). When `δ ≠ 0^m`, every
   nontrivial collision `y₀ ≠ y₁` under `naorYungShrink m δ` forces `y₁ = y₀ ⊕ δ`.
2. **Single-step `(n + 2) → (n + 1)` UOWHF (`naorYungStep f`)**: composing `f` on `(n + 2)`-bit
   inputs with `naorYungShrink (n + 2) δ` yields a `1`-bit shrinking target collision-resistant
   family. Given a random challenge `y = f x*` in `inversionGame f _ (n + 2)` and the adversary's
   committed target `w₀`, planting `δ := f w₀ ⊕ y` produces an exact uniform `(n + 2)`-bit key, and
   any valid target collision `w₁ ≠ w₀` satisfies either `f w₀ = y` (`δ = 0^{n+2}`) or
   `f w₁ = f w₀ ⊕ δ = y` (`δ ≠ 0^{n+2}`), inverting `y` with security loss `1`.
3. **Iterated `2(n + 1) → (n + 1)` compression (`naorYungCompression`) and arbitrary-length hashing
   (`naorYungHash`)**: cascading `n + 1` steps with independent `(n + 2)`-bit subkeys compresses
   `2(n + 1)` bits to `n + 1` bits (`KeyedCompressionFamily`), and composing with
   `KeyedCompressionFamily.treeHash` yields an unrestricted target collision-resistant
   `KeyedHashFamily` on all `List Bool` (within `treeHash`'s `< 2 ^ n` finite-parameter tree
   capacity, which covers all strict-PPT adversaries asymptotically).

## Main definitions

* `Cslib.Crypto.naorYungPivot`, `Cslib.Crypto.naorYungCanon`, `Cslib.Crypto.naorYungShrink`:
  pivot index, canonical `{0, δ}`-coset representative, and `(m) → (m - 1)` quotient map.
* `Cslib.Crypto.naorYungStep`, `Cslib.Crypto.naorYungStepInverter`: single-step `(n + 2) → (n + 1)`
  hash from a permutation `f` and its zero-loss reduction to `inversionGame`.
* `Cslib.Crypto.naorYungCascade`, `Cslib.Crypto.naorYungCompressionEval`,
  `Cslib.Crypto.naorYungCompression`: `(n + 1)`-step `2(n + 1) → (n + 1)` `KeyedCompressionFamily`.
* `Cslib.Crypto.naorYungCascadeInput`, `Cslib.Crypto.naorYungCascadeAdversary`: step-input
  extractor and planted-subkey reduction from `naorYungCompression` to `naorYungStep`.
* `Cslib.Crypto.naorYungHash`: unrestricted `KeyedHashFamily` on `List Bool` obtained via
  `KeyedCompressionFamily.treeHash`.

## Main results

* `Cslib.Crypto.naorYungShrink_collision_eq_listXor`: every distinct `m`-bit collision under a
  nonzero shift `δ` satisfies `y₁ = BitString.listXor m [y₀, δ]`.
* `Cslib.Crypto.succProbability_targetCollisionGame_naorYungStep_le`: single-step target-collision
  success at parameter `n` is bounded by `inversionGame` success at length `n + 2`.
* `Cslib.Crypto.OneWayPermutation.targetCollisionResistantOn_naorYungStep`: `naorYungStep f` is
  target collision-resistant on `(n + 2)`-bit inputs whenever `f` is a `OneWayPermutation`.
* `Cslib.Crypto.exists_naorYungCascadeInput_collision`,
  `Cslib.Crypto.succProbability_targetCollisionGame_naorYungCompressionEval_le`: deterministic
  step-collision extraction and `dyadicSize (n + 1)` reduction bound for `naorYungCompressionEval`.
* `Cslib.Crypto.OneWayPermutation.targetCollisionResistant_naorYungCompression`,
  `Cslib.Crypto.OneWayPermutation.targetCollisionResistant_naorYungHash`,
  `Cslib.Crypto.OneWayPermutation.exists_targetCollisionResistant_keyedHashFamily`: every
  `OneWayPermutation` yields a target collision-resistant `KeyedCompressionFamily` and unrestricted
  `KeyedHashFamily`.

## References

* [M. Naor, M. Yung, *Universal One-Way Hash Functions and their Cryptographic
  Applications*][NaorYung1989], Section 3 in the 1989 proceedings; §§2.1–2.3 (Lemma 2.1/Theorem 1,
  Lemma 2.2, and succinct block hashing) in the March 13, 1995 manuscript revision.
* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 6.4.3.2 (Constructions 6.4.20–6.4.26 and Propositions 6.4.21–6.4.27 in the June 2003
  chapter draft).
-/

public section

namespace Cslib.Crypto

open ProbComp Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### One-bit coset quotient `m → m - 1` -/

/-- First coordinate `< m` at which `δ` is `true`, defaulting to `0` when the `m`-bit prefix of `δ`
is all `false`. -/
@[expose]
def naorYungPivot (m : ℕ) (δ : List Bool) : ℕ :=
  ((List.range m).filter (fun i => δ.getD i false)).headD 0

theorem naorYungPivot_lt {m : ℕ} (hm : 1 ≤ m) (δ : List Bool) :
    naorYungPivot m δ < m := by
  unfold naorYungPivot
  cases h : (List.range m).filter (fun i => δ.getD i false) with
  | nil => simp only [List.headD_nil]; omega
  | cons a rest =>
    exact List.mem_range.mp (List.mem_of_mem_filter (h ▸ List.mem_cons_self ..))

theorem getD_naorYungPivot_of_exists {m : ℕ} {δ : List Bool}
    (h : ∃ i < m, δ.getD i false = true) :
    δ.getD (naorYungPivot m δ) false = true := by
  unfold naorYungPivot
  rcases h with ⟨i, hi_lt, hi_true⟩
  have hmem : i ∈ (List.range m).filter (fun j => δ.getD j false) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr hi_lt, hi_true⟩
  cases hlist : (List.range m).filter (fun j => δ.getD j false) with
  | nil => rw [hlist] at hmem; cases hmem
  | cons a rest =>
    have ha : a ∈ (List.range m).filter (fun j => δ.getD j false) := hlist ▸ List.mem_cons_self ..
    simpa only [List.headD_cons] using (List.mem_filter.mp ha).2

private theorem computableTidilyInPolyTime_naorYungPivot
    {γ : Type} {encIn : γ ↪ List Bool} {m : γ → ℕ} {δ : γ → List Bool}
    (hm : ComputableTidilyInPolyTime m encIn encUnary)
    (hδ : ComputableTidilyInPolyTime δ encIn encBits) :
    ComputableTidilyInPolyTime (fun a => naorYungPivot (m a) (δ a)) encIn encUnary :=
  (ComputableTidilyInPolyTime.headD (encA := encUnary) (encL := encList encUnary) 0).comp
    (ComputableTidilyInPolyTime.filterWithInput (test := fun a i => (δ a).getD i false)
      (ComputableTidilyInPolyTime.range.comp hm)
      (ComputableTidilyInPolyTime.bitsGetDWithInput
        (hδ.comp (ComputableTidilyInPolyTime.fst encIn encUnary))
        (ComputableTidilyInPolyTime.snd encIn encUnary) false))

/-- Computing `naorYungPivot` is plain polynomial-time on unary `m` and raw bit string `δ`. -/
@[program_certificate, fun_prop]
theorem computableInPolyTime_naorYungPivot
    {γ : Type} {encIn : γ ↪ List Bool} {m : γ → ℕ} {δ : γ → List Bool}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hδ : ComputableInPolyTime δ encIn encBits) :
    ComputableInPolyTime (fun a => naorYungPivot (m a) (δ a)) encIn encUnary :=
  .of_tidy (computableTidilyInPolyTime_naorYungPivot hm.tidy hδ.tidy)

/-- Canonical `{0, δ}`-coset representative of `y` at width `m`: normalize `y` to width `m` and XOR
with `δ` when coordinate `naorYungPivot m δ` is `true`. -/
@[expose]
def naorYungCanon (m : ℕ) (δ y : List Bool) : List Bool :=
  let p := naorYungPivot m δ
  let y₀ := BitString.listRow m 0 y
  if y₀.getD p false then BitString.listXor m [y₀, δ] else y₀

@[simp]
theorem length_naorYungCanon (m : ℕ) (δ y : List Bool) :
    (naorYungCanon m δ y).length = m := by
  unfold naorYungCanon; dsimp only; split_ifs
  · exact BitString.length_listXor m _
  · exact BitString.length_listRow m 0 y

private theorem getD_naorYungCanon_pivot {m : ℕ} {δ : List Bool}
    (hδ : ∃ i < m, δ.getD i false = true) (y : List Bool) :
    (naorYungCanon m δ y).getD (naorYungPivot m δ) false = false := by
  rcases hδ with ⟨i₀, hi₀_lt, hi₀_true⟩
  have hp_lt : naorYungPivot m δ < m := naorYungPivot_lt (by omega) δ
  have hp_true : δ.getD (naorYungPivot m δ) false = true :=
    getD_naorYungPivot_of_exists ⟨i₀, hi₀_lt, hi₀_true⟩
  unfold naorYungCanon; dsimp only; split_ifs with hy
  · rw [BitString.getD_listXor_pair m _ δ (naorYungPivot m δ) hp_lt, hy, hp_true, Bool.xor_self]
  · exact Bool.eq_false_iff.mpr hy

private theorem computableTidilyInPolyTime_naorYungCanon
    {γ : Type} {encIn : γ ↪ List Bool} {m : γ → ℕ} {δ y : γ → List Bool}
    (hm : ComputableTidilyInPolyTime m encIn encUnary)
    (hδ : ComputableTidilyInPolyTime δ encIn encBits)
    (hy : ComputableTidilyInPolyTime y encIn encBits) :
    ComputableTidilyInPolyTime (fun a => naorYungCanon (m a) (δ a) (y a)) encIn encBits := by
  have hp := computableTidilyInPolyTime_naorYungPivot hm hδ
  have hy₀ := ComputableTidilyInPolyTime.bitsRowWithInput hm (.const 0) hy
  exact ComputableTidilyInPolyTime.ite' (ComputableTidilyInPolyTime.bitsGetDWithInput hy₀ hp false)
    (ComputableTidilyInPolyTime.bitsXorWithInput hm
      (ComputableTidilyInPolyTime.cons' hy₀ (ComputableTidilyInPolyTime.cons' hδ (.const [])))) hy₀

/-- Computing `naorYungCanon` is plain polynomial-time on unary `m` and raw bit strings `δ, y`. -/
@[program_certificate, fun_prop]
theorem computableInPolyTime_naorYungCanon
    {γ : Type} {encIn : γ ↪ List Bool} {m : γ → ℕ} {δ y : γ → List Bool}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hδ : ComputableInPolyTime δ encIn encBits)
    (hy : ComputableInPolyTime y encIn encBits) :
    ComputableInPolyTime (fun a => naorYungCanon (m a) (δ a) (y a)) encIn encBits :=
  .of_tidy (computableTidilyInPolyTime_naorYungCanon hm.tidy hδ.tidy hy.tidy)

/-- **Naor–Yung 1-bit quotient** `m → m - 1`: canonicalize bit `p := naorYungPivot m δ` via
`naorYungCanon m δ y` and delete coordinate `p`. -/
@[expose]
def naorYungShrink (m : ℕ) (δ y : List Bool) : List Bool :=
  let p := naorYungPivot m δ
  let c := naorYungCanon m δ y
  c.take p ++ c.drop (p + 1)

@[simp]
theorem length_naorYungShrink (m : ℕ) (δ y : List Bool) :
    (naorYungShrink m δ y).length = m - 1 := by
  cases m with
  | zero =>
    unfold naorYungShrink; dsimp only
    simp [List.length_eq_zero_iff.mp (length_naorYungCanon 0 δ y)]
  | succ m' =>
    have hp : naorYungPivot (m' + 1) δ < m' + 1 := naorYungPivot_lt (by omega) δ
    unfold naorYungShrink; dsimp only
    rw [List.length_append, List.length_take, List.length_drop, length_naorYungCanon]; omega

private theorem computableTidilyInPolyTime_naorYungShrink
    {γ : Type} {encIn : γ ↪ List Bool} {m : γ → ℕ} {δ y : γ → List Bool}
    (hm : ComputableTidilyInPolyTime m encIn encUnary)
    (hδ : ComputableTidilyInPolyTime δ encIn encBits)
    (hy : ComputableTidilyInPolyTime y encIn encBits) :
    ComputableTidilyInPolyTime (fun a => naorYungShrink (m a) (δ a) (y a)) encIn encBits := by
  have hp := computableTidilyInPolyTime_naorYungPivot hm hδ
  have hc := computableTidilyInPolyTime_naorYungCanon hm hδ hy
  exact ComputableTidilyInPolyTime.bitsAppend (ComputableTidilyInPolyTime.bitsTakeWithInput hc hp)
    (ComputableTidilyInPolyTime.bitsDropWithInput hc
      (ComputableTidilyInPolyTime.unary_add.comp (hp.prod (.const 1))))

/-- Computing `naorYungShrink` is plain polynomial-time on unary `m` and raw bit strings `δ, y`. -/
@[program_certificate, fun_prop]
theorem computableInPolyTime_naorYungShrink
    {γ : Type} {encIn : γ ↪ List Bool} {m : γ → ℕ} {δ y : γ → List Bool}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hδ : ComputableInPolyTime δ encIn encBits)
    (hy : ComputableInPolyTime y encIn encBits) :
    ComputableInPolyTime (fun a => naorYungShrink (m a) (δ a) (y a)) encIn encBits :=
  .of_tidy (computableTidilyInPolyTime_naorYungShrink hm.tidy hδ.tidy hy.tidy)

private theorem eq_of_take_append_drop_eq {m p : ℕ} (hp : p < m) {c₀ c₁ : List Bool}
    (hc₀ : c₀.length = m) (hc₁ : c₁.length = m)
    (hp₀ : c₀.getD p false = false) (hp₁ : c₁.getD p false = false)
    (heq : c₀.take p ++ c₀.drop (p + 1) = c₁.take p ++ c₁.drop (p + 1)) :
    c₀ = c₁ := by
  apply List.ext_getElem (hc₀.trans hc₁.symm)
  intro i hi₀ hi₁
  have htake₀ : (c₀.take p).length = p := by rw [List.length_take, hc₀]; omega
  have htake₁ : (c₁.take p).length = p := by rw [List.length_take, hc₁]; omega
  rcases lt_trichotomy i p with hlt | rfl | hgt
  · have hlen_L : i < (c₀.take p ++ c₀.drop (p + 1)).length := by
      rw [List.length_append, htake₀]; omega
    have hlen_R : i < (c₁.take p ++ c₁.drop (p + 1)).length := by
      rw [List.length_append, htake₁]; omega
    have hget := congrArg (fun l => l[i]?) heq
    rwa [List.getElem?_eq_getElem hlen_L, List.getElem?_eq_getElem hlen_R, Option.some.injEq,
      List.getElem_append_left (by omega), List.getElem_append_left (by omega),
      List.getElem_take, List.getElem_take] at hget
  · simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₀,
      List.getElem?_eq_getElem hi₁, Option.getD_some] using hp₀.trans hp₁.symm
  · have hget := congrArg (fun l => l[i - 1]?) heq
    rwa [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      htake₀, htake₁, List.getElem?_drop, List.getElem?_drop,
      show p + 1 + (i - 1 - p) = i by omega, List.getElem?_eq_getElem hi₀,
      List.getElem?_eq_getElem hi₁, Option.some.injEq] at hget

private theorem listRow_zero_eq_self {m : ℕ} {y : List Bool} (hy : y.length = m) :
    BitString.listRow m 0 y = y := by
  rw [BitString.listRow_zero, BitString.ofFn_ofList hy]

/-- **Collision characterization for `naorYungShrink`**: if `δ` has a `true` coordinate below `m`,
any two distinct `m`-bit strings `y₀ ≠ y₁` colliding under `naorYungShrink m δ` differ by `δ`, i.e.,
`y₁ = BitString.listXor m [y₀, δ]`. -/
theorem naorYungShrink_collision_eq_listXor {m : ℕ} {δ y₀ y₁ : List Bool}
    (hδ : ∃ i < m, δ.getD i false = true)
    (hy₀ : y₀.length = m) (hy₁ : y₁.length = m) (hne : y₀ ≠ y₁)
    (hcol : naorYungShrink m δ y₀ = naorYungShrink m δ y₁) :
    y₁ = BitString.listXor m [y₀, δ] := by
  rcases hδ with ⟨i₀, hi₀_lt, hi₀_true⟩
  have hp : naorYungPivot m δ < m := naorYungPivot_lt (by omega) δ
  have hc_eq : naorYungCanon m δ y₀ = naorYungCanon m δ y₁ :=
    eq_of_take_append_drop_eq hp (length_naorYungCanon m δ y₀) (length_naorYungCanon m δ y₁)
      (getD_naorYungCanon_pivot ⟨i₀, hi₀_lt, hi₀_true⟩ y₀)
      (getD_naorYungCanon_pivot ⟨i₀, hi₀_lt, hi₀_true⟩ y₁) hcol
  unfold naorYungCanon at hc_eq; dsimp only at hc_eq
  rw [listRow_zero_eq_self hy₀, listRow_zero_eq_self hy₁] at hc_eq
  split_ifs at hc_eq with hb₀ hb₁
  · exfalso; apply hne
    have hx := congrArg (fun z => BitString.listXor m [δ, z]) hc_eq
    rwa [BitString.listXor_pair_comm m y₀ δ, BitString.listXor_pair_comm m y₁ δ,
      BitString.listXor_pair_self_left_of_length δ hy₀,
      BitString.listXor_pair_self_left_of_length δ hy₁] at hx
  · exact hc_eq.symm
  · have hx := congrArg (fun z => BitString.listXor m [δ, z]) hc_eq
    rw [BitString.listXor_pair_comm m y₁ δ, BitString.listXor_pair_self_left_of_length δ hy₁,
      BitString.listXor_pair_comm m δ y₀] at hx
    exact hx.symm
  · exact False.elim (hne hc_eq)

/-! ### Single-step `(n + 2) → (n + 1)` UOWHF from a one-way permutation -/

/-- Single-step Naor–Yung `(n + 2) → (n + 1)` hash from `f`: normalize `w` to `n + 2` bits, evaluate
`f`, and apply `naorYungShrink (n + 2) δ`. -/
@[expose]
def naorYungStep (f : List Bool → List Bool) (n : ℕ) (δ w : List Bool) : List Bool :=
  naorYungShrink (n + 2) δ (f (BitString.listRow (n + 2) 0 w))

@[simp]
theorem length_naorYungStep (f : List Bool → List Bool) (n : ℕ) (δ w : List Bool) :
    (naorYungStep f n δ w).length = n + 1 := by
  simp [naorYungStep]

private theorem computableTidilyInPolyTime_naorYungStep
    {f : List Bool → List Bool} (hf : ComputableTidilyInPolyTime f encBits encBits)
    {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ} {δ w : γ → List Bool}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hδ : ComputableTidilyInPolyTime δ encIn encBits)
    (hw : ComputableTidilyInPolyTime w encIn encBits) :
    ComputableTidilyInPolyTime (fun a => naorYungStep f (n a) (δ a) (w a)) encIn encBits := by
  have hn2 := ComputableTidilyInPolyTime.unary_add.comp (hn.prod (.const 2))
  exact computableTidilyInPolyTime_naorYungShrink hn2 hδ
    (hf.comp (ComputableTidilyInPolyTime.bitsRowWithInput hn2 (.const 0) hw))

/-- Evaluating `naorYungStep f` is plain polynomial-time whenever `f` is plain polynomial-time. -/
@[program_certificate, fun_prop]
theorem computableInPolyTime_naorYungStep
    {f : List Bool → List Bool} (hf : ComputableInPolyTime f encBits encBits)
    {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ} {δ w : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hδ : ComputableInPolyTime δ encIn encBits)
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun a => naorYungStep f (n a) (δ a) (w a)) encIn encBits :=
  .of_tidy (computableTidilyInPolyTime_naorYungStep hf.tidy hn.tidy hδ.tidy hw.tidy)

/-- Zero-loss preimage reduction from `naorYungStep f` to `inversionGame f` (adapting
[NaorYung1989], Section 3; [Goldreich2004], Section 6.4.3.2, June 2003 draft Proposition 6.4.21): at
challenge length `m ≥ 2`, set `n := m - 2`, run `adversary.choose n` to obtain a target `w₀`
(normalized to `n + 2` bits), plant `δ := f w₀ ⊕ y`, run `adversary.find n state δ` to obtain `w₁`,
and output whichever of `w₁` or `w₀` maps to `y` under `f`. -/
noncomputable def naorYungStepInverter
    (f : List Bool → List Bool) (adversary : TargetCollisionFinder) : Inverter :=
  fun m y =>
    if m < 2 then pure []
    else do
      let n := m - 2
      let choice ← adversary.choose n
      let w₀ := BitString.listRow (n + 2) 0 choice.1
      let δ := BitString.listXor (n + 2) [f w₀, y]
      let w₁ ← adversary.find n choice.2 δ
      return if f w₁ == y then w₁ else w₀

/-- `naorYungStepInverter` is uniformly strict PPT whenever `f` is plain polynomial-time and
`adversary` is strict PPT. -/
theorem isPPT_naorYungStepInverter
    {f : List Bool → List Bool} {adversary : TargetCollisionFinder}
    (hf : ComputableInPolyTime f encBits encBits) (ha : adversary.IsPPT) :
    IsPPT encBits (naorYungStepInverter f adversary) := by
  let E0 := encPair encUnary encBits
  let E1 := encPair E0 (encPair encBits encBits)
  have hft := hf.tidy
  have hm := ComputableTidilyInPolyTime.fst encUnary encBits
  have hn0 := ComputableTidilyInPolyTime.unary_sub.comp (hm.prod (.const 2))
  have hq := ComputableTidilyInPolyTime.id' (encIn := E1)
  have hn1 := hn0.comp hq.fst'
  have hn1_2 := ComputableTidilyInPolyTime.unary_add.comp (hn1.prod (.const 2))
  have hw₀1 := ComputableTidilyInPolyTime.bitsRowWithInput hn1_2 (.const 0) hq.snd'.fst'
  have hδ1 := ComputableTidilyInPolyTime.bitsXorWithInput hn1_2
    (ComputableTidilyInPolyTime.cons' (hft.comp hw₀1)
      (ComputableTidilyInPolyTime.cons' hq.fst'.snd' (.const [])))
  have hr := ComputableTidilyInPolyTime.id' (encIn := encPair E1 encBits)
  have hcb := ComputableTidilyInPolyTime.ite'
    (ComputableTidilyInPolyTime.beq (hft.comp hr.snd') hr.fst'.fst'.snd')
    hr.snd' (hw₀1.comp hr.fst')
  change IsPPTOn E0 encBits (fun p => naorYungStepInverter f adversary p.1 p.2)
  exact IsPPTOn.ite (hm.unary_lt' (.const 2)) (ComputableTidilyInPolyTime.const []).isPPTOn
    ((ha.choose.preprocess (.of_tidy hn0)).bind_with
      ((ha.find.preprocess (.of_tidy (hn1.prod (hq.snd'.snd'.prod hδ1)))).bind_with hcb.isPPTOn))

private def xorFixedWidth (u y : List Bool) : List Bool :=
  if y.length = u.length then BitString.listXor u.length [u, y] else y

private theorem length_xorFixedWidth (u y : List Bool) :
    (xorFixedWidth u y).length = y.length := by
  unfold xorFixedWidth; split_ifs with h
  · rw [BitString.length_listXor, h]
  · rfl

private theorem involutive_xorFixedWidth (u : List Bool) :
    Function.Involutive (xorFixedWidth u) := by
  intro y; unfold xorFixedWidth
  by_cases h : y.length = u.length
  · simp [h, BitString.length_listXor, BitString.listXor_pair_self_left_of_length u h]
  · simp [h]

private theorem uniformList_map_listXor {m : ℕ} {u : List Bool} (hu : u.length = m) :
    (BitString.uniformList m).map (fun y => BitString.listXor m [u, y]) =
      BitString.uniformList m := by
  have heq : (BitString.uniformList m).map (fun y => BitString.listXor m [u, y]) =
      (BitString.uniformList m).map (xorFixedWidth u) := by
    refine PMF.bind_congr_on_support _ _ _ fun y hy => ?_
    simp [xorFixedWidth, BitString.length_of_mem_support_uniformList hy, hu]
  exact heq.trans (BitString.uniformList_map_of_bijective (xorFixedWidth u)
    (involutive_xorFixedWidth u).bijective (length_xorFixedWidth u) m)

private theorem exists_true_listXor_of_ne {m : ℕ} {u v : List Bool}
    (hu : u.length = m) (hv : v.length = m) (hne : u ≠ v) :
    ∃ i < m, (BitString.listXor m [u, v]).getD i false = true := by
  by_contra hall
  simp only [not_exists, not_and] at hall
  apply hne (List.ext_getElem (hu.trans hv.symm) fun i hi_u hi_v => ?_)
  have hi_m : i < m := by omega
  have hzero := Bool.eq_false_iff.mpr (hall i hi_m)
  rw [BitString.getD_listXor_pair m u v i hi_m] at hzero
  have heq_bit : u.getD i false = v.getD i false := by
    cases h1 : u.getD i false <;> cases h2 : v.getD i false <;> simp_all
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_u,
    List.getElem?_eq_getElem hi_v, Option.getD_some] using heq_bit

private theorem naorYungStep_inversion_eval_eq
    {f : List Bool → List Bool} (hf_len : ∀ w, (f w).length = w.length)
    (hf_bij : Function.Bijective f) (adversary : TargetCollisionFinder) (n : ℕ) :
    ProbComp.eval (inversionGame f (naorYungStepInverter f adversary) (n + 2)) =
      (ProbComp.eval (adversary.choose n)).bind (fun choice =>
        let w₀ := BitString.listRow (n + 2) 0 choice.1
        (BitString.uniformList (n + 2)).bind (fun δ =>
          (ProbComp.eval (adversary.find n choice.2 δ)).bind (fun w₁ =>
            let y := BitString.listXor (n + 2) [f w₀, δ]
            PMF.pure (f (if f w₁ == y then w₁ else w₀) == y)))) := by
  have hlt_false : ¬ (n + 2 < 2) := by omega
  have hsub : n + 2 - 2 = n := by omega
  simp only [inversionGame, naorYungStepInverter, hlt_false, ↓reduceIte, hsub,
    ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_bind,
    PMF.pure_bind]
  trans ((BitString.uniformList (n + 2)).map f).bind (fun y =>
    (ProbComp.eval (adversary.choose n)).bind (fun choice =>
      let w₀ := BitString.listRow (n + 2) 0 choice.1
      let δ := BitString.listXor (n + 2) [f w₀, y]
      (ProbComp.eval (adversary.find n choice.2 δ)).bind (fun w₁ =>
        PMF.pure (f (if f w₁ == y then w₁ else w₀) == y))))
  · rw [PMF.bind_map]; rfl
  · rw [BitString.uniformList_map_of_bijective f hf_bij hf_len (n + 2), PMF.bind_comm]
    refine PMF.bind_congr_on_support _ _ _ fun choice _ => ?_
    let w₀ := BitString.listRow (n + 2) 0 choice.1
    have hfw₀ : (f w₀).length = n + 2 :=
      (hf_len w₀).trans (BitString.length_listRow (n + 2) 0 choice.1)
    conv_rhs => rw [← uniformList_map_listXor hfw₀, PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun y hy => ?_
    dsimp only [Function.comp_def, w₀] at hfw₀ ⊢
    simp only [BitString.listXor_pair_self_left_of_length _
      (BitString.length_of_mem_support_uniformList hy)]

/-- **Single-step Naor–Yung security bound**: for any length-preserving bijection `f`, the
target-collision success probability of `adversary` against `naorYungStep f` at parameter `n` is at
most the preimage-finding success probability of `naorYungStepInverter f adversary` against `f` at
challenge length `n + 2` (with factor `1` and zero additive error). -/
theorem succProbability_targetCollisionGame_naorYungStep_le
    {f : List Bool → List Bool} (hf_len : ∀ w, (f w).length = w.length)
    (hf_bij : Function.Bijective f)
    (adversary : TargetCollisionFinder) (n : ℕ) :
    Game.succProbability
      (ProbComp.eval
        (targetCollisionGame (fun m => m + 2) (naorYungStep f)
          (fun m w => w.length == m + 2) adversary n)) ≤
      Game.succProbability
        (ProbComp.eval (inversionGame f (naorYungStepInverter f adversary) (n + 2))) := by
  let validStep (m : ℕ) (w : List Bool) : Bool := w.length == m + 2
  apply Game.succProbability_mono
  rw [naorYungStep_inversion_eval_eq hf_len hf_bij adversary n]
  simp only [targetCollisionGame, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
  apply PMF.bind_apply_mono_on_support; intro choice _
  apply PMF.bind_apply_mono_on_support; intro δ hδ
  apply PMF.bind_apply_mono_on_support; intro w₁ _
  have hδ_len : δ.length = n + 2 := BitString.length_of_mem_support_uniformList hδ
  cases hcol : isCollision (naorYungStep f n) validStep n δ choice.1 w₁
  · simp
  · rw [isCollision_eq_true_iff] at hcol
    obtain ⟨hw₀_valid, hw₁_valid, hne, hstep_eq⟩ := hcol
    have hw₀_len : choice.1.length = n + 2 := beq_iff_eq.mp hw₀_valid
    have hw₁_len : w₁.length = n + 2 := beq_iff_eq.mp hw₁_valid
    let w₀ := BitString.listRow (n + 2) 0 choice.1
    have hw₀_eq : w₀ = choice.1 := listRow_zero_eq_self hw₀_len
    let y := BitString.listXor (n + 2) [f w₀, δ]
    have hfw₀_len : (f w₀).length = n + 2 :=
      (hf_len w₀).trans (BitString.length_listRow (n + 2) 0 choice.1)
    have hfw₁_len : (f w₁).length = n + 2 := (hf_len w₁).trans hw₁_len
    have hy_len : y.length = n + 2 := BitString.length_listXor (n + 2) [f w₀, δ]
    have hwin : (f (if f w₁ == y then w₁ else w₀) == y) = true := by
      by_cases hfy : f w₀ = y
      · by_cases hcheck : (f w₁ == y) = true <;> simp_all
      · have hδ_eq : δ = BitString.listXor (n + 2) [f w₀, y] :=
          (BitString.listXor_pair_self_left_of_length (f w₀) hδ_len).symm
        have hδ_nz : ∃ i < n + 2, δ.getD i false = true :=
          hδ_eq ▸ exists_true_listXor_of_ne hfw₀_len hy_len hfy
        have hstep_eq' : naorYungShrink (n + 2) δ (f w₀) = naorYungShrink (n + 2) δ (f w₁) := by
          have hraw : naorYungShrink (n + 2) δ (f (BitString.listRow (n + 2) 0 choice.1)) =
              naorYungShrink (n + 2) δ (f (BitString.listRow (n + 2) 0 w₁)) := hstep_eq
          rwa [listRow_zero_eq_self hw₁_len] at hraw
        have hfw₁_eq : f w₁ = y :=
          naorYungShrink_collision_eq_listXor hδ_nz hfw₀_len hfw₁_len
            (fun heq => hne (hw₀_eq ▸ hf_bij.1 heq)) hstep_eq'
        simp only [hfw₁_eq, beq_self_eq_true, ↓reduceIte]
    change PMF.pure true true ≤ PMF.pure (f (if f w₁ == y then w₁ else w₀) == y) true
    rw [hwin]

/-- **Single-step Naor–Yung UOWHF theorem** (adapting [NaorYung1989], Section 3; [Goldreich2004],
Section 6.4.3.2, June 2003 draft Construction 6.4.20 and Proposition 6.4.21): if `f` is a
`OneWayPermutation`, `naorYungStep f` is target collision-resistant on `(n + 2)`-bit inputs under
`(n + 2)`-bit keys. -/
theorem OneWayPermutation.targetCollisionResistantOn_naorYungStep
    {f : List Bool → List Bool} (hf : OneWayPermutation f) :
    TargetCollisionResistantOn (fun n => n + 2) (naorYungStep f)
      (fun n w => w.length == n + 2) := by
  apply TargetCollisionResistantOn.of_negligible
  intro adversary hadversary
  have hinv_neg :=
    (hf.oneWay.inversion_negligible (naorYungStepInverter f adversary)
      (isPPT_naorYungStepInverter hf.oneWay.polyTime hadversary)).shift 2
  refine negligible_of_le hinv_neg fun n => ?_
  exact succProbability_targetCollisionGame_naorYungStep_le hf.length_eq hf.bijective adversary n

/-! ### `(n + 1)`-step cascade `2(n + 1) → (n + 1)` (`naorYungCompression`) -/

/-- One step of the Naor–Yung compression cascade: absorb the next bit `acc.2.headD false` into the
`(n + 1)`-bit state `acc.1` via `naorYungStep f n δ` and advance `acc.2` by one bit. -/
@[expose]
def naorYungCascadeStep (f : List Bool → List Bool) (n : ℕ)
    (acc : List Bool × List Bool) (δ : List Bool) : List Bool × List Bool :=
  (naorYungStep f n δ (acc.1 ++ [acc.2.headD false]), acc.2.drop 1)

/-- Fold `naorYungCascadeStep f n` across `subkeys` starting from `(state, rest)` and return the
final `(n + 1)`-bit state. -/
@[expose]
def naorYungCascade (f : List Bool → List Bool) (n : ℕ)
    (subkeys : List (List Bool)) (state rest : List Bool) : List Bool :=
  (subkeys.foldl (naorYungCascadeStep f n) (state, rest)).1

private theorem snd_foldl_naorYungCascadeStep (f : List Bool → List Bool) (n : ℕ)
    (subkeys : List (List Bool)) (state rest : List Bool) :
    (subkeys.foldl (naorYungCascadeStep f n) (state, rest)).2 = rest.drop subkeys.length := by
  induction subkeys generalizing state rest with
  | nil => simp
  | cons δ ks ih =>
    simp only [List.foldl_cons, naorYungCascadeStep, ih, List.drop_drop, List.length_cons]
    rw [Nat.add_comm 1 ks.length]

theorem length_naorYungCascade (f : List Bool → List Bool) (n : ℕ)
    (subkeys : List (List Bool)) {state : List Bool} (hstate : state.length = n + 1)
    (rest : List Bool) :
    (naorYungCascade f n subkeys state rest).length = n + 1 := by
  induction subkeys generalizing state rest with
  | nil => exact hstate
  | cons δ ks ih =>
    exact ih (length_naorYungStep f n δ _) (rest.drop 1)

private theorem length_naorYungCascade_le (f : List Bool → List Bool) (n : ℕ)
    (subkeys : List (List Bool)) (state rest : List Bool) :
    (naorYungCascade f n subkeys state rest).length ≤ state.length + (n + 1) := by
  cases subkeys with
  | nil => simp [naorYungCascade]
  | cons δ ks =>
    have h := length_naorYungCascade f n ks
      (length_naorYungStep f n δ (state ++ [rest.headD false])) (rest.drop 1)
    simp only [naorYungCascade, List.foldl_cons, naorYungCascadeStep] at h ⊢; omega

theorem naorYungCascade_append_singleton (f : List Bool → List Bool) (n : ℕ)
    (ks : List (List Bool)) (δ state rest : List Bool) :
    naorYungCascade f n (ks ++ [δ]) state rest =
      naorYungStep f n δ (naorYungCascade f n ks state rest ++ [rest.getD ks.length false]) := by
  have hhead : (rest.drop ks.length).headD false = rest.getD ks.length false := by
    rw [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
  simp only [naorYungCascade, List.foldl_append, List.foldl_cons, List.foldl_nil,
    naorYungCascadeStep, snd_foldl_naorYungCascadeStep, hhead]

private theorem computableTidilyInPolyTime_naorYungCascade
    {f : List Bool → List Bool} (hf : ComputableTidilyInPolyTime f encBits encBits)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {subkeys : γ → List (List Bool)} {state rest : γ → List Bool}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hsubkeys : ComputableTidilyInPolyTime subkeys encIn (encList encBits))
    (hstate : ComputableTidilyInPolyTime state encIn encBits)
    (hrest : ComputableTidilyInPolyTime rest encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => naorYungCascade f (n a) (subkeys a) (state a) (rest a))
      encIn encBits := by
  let EStep := encPair (encPair encUnary (encPair encBits encBits)) encBits
  have hp := ComputableTidilyInPolyTime.id' (encIn := EStep)
  have hhead := (ComputableTidilyInPolyTime.headD
    (encA := encBool) (encL := encBits) false).comp hp.fst'.snd'.snd'
  have hw := ComputableTidilyInPolyTime.bitsAppend hp.fst'.snd'.fst'
    (ComputableTidilyInPolyTime.bitsCons hhead (.const []))
  have hstep := (computableTidilyInPolyTime_naorYungStep hf hp.fst'.fst' hp.snd' hw).prod
    (ComputableTidilyInPolyTime.bitsDropWithInput hp.fst'.snd'.snd' (.const 1))
  let stateBound (a : γ) : ℕ := 2 * ((state a).length + (n a + 1)) + 1 + (rest a).length
  have hpoly : PolyBounded (fun a => (encIn a).length) stateBound := by
    have hs := hstate.polyBounded_length
    have hr := hrest.polyBounded_length
    have hn_b := hn.polyBounded_length
    simp only [encBits_apply, encUnary_apply, List.length_replicate] at hs hr hn_b
    exact (((PolyBounded.const 2).mul (hs.add (hn_b.add (.const 1)))).add (.const 1)).add hr
  refine (ComputableTidilyInPolyTime.foldlWith
    (encA := encBits) (encL := encList encBits) (encP := encUnary) (encB := encPair encBits encBits)
    (par := n) (step := naorYungCascadeStep f)
    hn hsubkeys (hstate.prod hrest) hstep (B := stateBound) hpoly fun a i _ => ?_).fst'
  let pair := ((subkeys a).take i).foldl (naorYungCascadeStep f (n a)) (state a, rest a)
  change (encPair encBits encBits pair).length ≤ stateBound a
  have h1 : pair.1.length ≤ (state a).length + (n a + 1) :=
    length_naorYungCascade_le f (n a) ((subkeys a).take i) (state a) (rest a)
  have h2 : pair.2.length ≤ (rest a).length := by
    have heq := snd_foldl_naorYungCascadeStep f (n a) ((subkeys a).take i) (state a) (rest a)
    change ((subkeys a).take i |>.foldl (naorYungCascadeStep f (n a)) (state a, rest a)).2.length
      ≤ (rest a).length
    rw [heq, List.length_drop]; omega
  simp only [length_encPair, encBits_apply, stateBound]; omega

/-- Folding `naorYungCascade` is computable in plain polynomial time whenever `f` is computable in
plain polynomial time. -/
@[program_certificate, fun_prop]
theorem computableInPolyTime_naorYungCascade
    {f : List Bool → List Bool} (hf : ComputableInPolyTime f encBits encBits)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {subkeys : γ → List (List Bool)} {state rest : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hsubkeys : ComputableInPolyTime subkeys encIn (encList encBits))
    (hstate : ComputableInPolyTime state encIn encBits)
    (hrest : ComputableInPolyTime rest encIn encBits) :
    ComputableInPolyTime
      (fun a => naorYungCascade f (n a) (subkeys a) (state a) (rest a))
      encIn encBits :=
  .of_tidy (computableTidilyInPolyTime_naorYungCascade
    hf.tidy hn.tidy hsubkeys.tidy hstate.tidy hrest.tidy)

/-- **Naor–Yung `2(n + 1) → (n + 1)` compression evaluator** ([NaorYung1989], Section 3;
[Goldreich2004], Section 6.4.3.2): split `x` into two `(n + 1)`-bit halves and absorb the second
half one bit at a time across `n + 1` independent `(n + 2)`-bit subkeys from `K`. -/
@[expose]
def naorYungCompressionEval (f : List Bool → List Bool) (n : ℕ) (K x : List Bool) : List Bool :=
  naorYungCascade f n (BitString.listRows (n + 1) (n + 2) K)
    (BitString.listRow (n + 1) 0 x) (BitString.listRow (n + 1) 1 x)

@[simp]
theorem length_naorYungCompressionEval (f : List Bool → List Bool) (n : ℕ) (K x : List Bool) :
    (naorYungCompressionEval f n K x).length = n + 1 :=
  length_naorYungCascade f n _ (BitString.length_listRow (n + 1) 0 x) _

/-- Evaluating `naorYungCompressionEval f` is plain polynomial-time on `(1^n, K, x)` whenever `f`
is plain polynomial-time. -/
@[program_certificate]
theorem computableInPolyTime_naorYungCompressionEval
    {f : List Bool → List Bool} (hf : ComputableInPolyTime f encBits encBits) :
    ComputableInPolyTime
      (fun ⟨n, K, x⟩ => naorYungCompressionEval f n K x)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  have hp := ComputableTidilyInPolyTime.id' (encIn := encPair encUnary (encPair encBits encBits))
  have hn1 := ComputableTidilyInPolyTime.unary_add.comp (hp.fst'.prod (.const 1))
  have hn2 := ComputableTidilyInPolyTime.unary_add.comp (hp.fst'.prod (.const 2))
  exact .of_tidy (computableTidilyInPolyTime_naorYungCascade hf.tidy hp.fst'
    (ComputableTidilyInPolyTime.bitsRowsWithInput hn1 hn2 hp.snd'.fst')
    (ComputableTidilyInPolyTime.bitsRowWithInput hn1 (.const 0) hp.snd'.snd')
    (ComputableTidilyInPolyTime.bitsRowWithInput hn1 (.const 1) hp.snd'.snd'))

/-- Step-`i` `(n + 2)`-bit input fed to subkey `i` during `naorYungCompressionEval f n`, computed
using only the prefix `front` containing subkeys `< i`. -/
@[expose]
def naorYungCascadeInput (f : List Bool → List Bool) (n i : ℕ) (front x : List Bool) : List Bool :=
  let tail := BitString.listRow (n + 1) 1 x
  naorYungCascade f n (BitString.listRows i (n + 2) front)
    (BitString.listRow (n + 1) 0 x) tail ++ [tail.getD i false]

@[simp]
theorem length_naorYungCascadeInput (f : List Bool → List Bool) (n i : ℕ) (front x : List Bool) :
    (naorYungCascadeInput f n i front x).length = n + 2 := by
  simp only [naorYungCascadeInput, List.length_append, List.length_singleton,
    length_naorYungCascade f n _ (BitString.length_listRow (n + 1) 0 x)]

private theorem computableTidilyInPolyTime_naorYungCascadeInput
    {f : List Bool → List Bool} (hf : ComputableTidilyInPolyTime f encBits encBits)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n i : γ → ℕ} {front x : γ → List Bool}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hi : ComputableTidilyInPolyTime i encIn encUnary)
    (hfront : ComputableTidilyInPolyTime front encIn encBits)
    (hx : ComputableTidilyInPolyTime x encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => naorYungCascadeInput f (n a) (i a) (front a) (x a))
      encIn encBits := by
  have hn1 := ComputableTidilyInPolyTime.unary_add.comp (hn.prod (.const 1))
  have hn2 := ComputableTidilyInPolyTime.unary_add.comp (hn.prod (.const 2))
  have htail := ComputableTidilyInPolyTime.bitsRowWithInput hn1 (.const 1) hx
  have hcasc := computableTidilyInPolyTime_naorYungCascade hf hn
    (ComputableTidilyInPolyTime.bitsRowsWithInput hi hn2 hfront)
    (ComputableTidilyInPolyTime.bitsRowWithInput hn1 (.const 0) hx) htail
  exact ComputableTidilyInPolyTime.bitsAppend hcasc
    (ComputableTidilyInPolyTime.bitsCons
      (ComputableTidilyInPolyTime.bitsGetDWithInput htail hi false)
      (ComputableTidilyInPolyTime.const []))

@[program_certificate, fun_prop]
theorem computableInPolyTime_naorYungCascadeInput
    {f : List Bool → List Bool} (hf : ComputableInPolyTime f encBits encBits)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n i : γ → ℕ} {front x : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hfront : ComputableInPolyTime front encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime
      (fun a => naorYungCascadeInput f (n a) (i a) (front a) (x a))
      encIn encBits :=
  .of_tidy (computableTidilyInPolyTime_naorYungCascadeInput
    hf.tidy hn.tidy hi.tidy hfront.tidy hx.tidy)

private theorem listRow_lt_take {width count j : ℕ} (hj : j < count) (word : List Bool) :
    BitString.listRow width j (word.take (count * width)) = BitString.listRow width j word := by
  apply List.ext_getElem (by simp)
  intro col h₁ h₂
  have hcol : col < width := by simpa only [BitString.length_listRow] using h₁
  rw [BitString.getElem_listRow hcol, BitString.getElem_listRow hcol]
  have hidx_lt : j * width + col < count * width := by
    calc
      j * width + col < j * width + width := by omega
      _ = (j + 1) * width := by ring
      _ ≤ count * width := Nat.mul_le_mul_right width (by omega)
  by_cases hlt : j * width + col < word.length
  · have hlt_take : j * width + col < (word.take (count * width)).length := by
      rw [List.length_take]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
      List.getElem?_eq_getElem hlt_take, List.getElem_take]
  · have hge_w : word.length ≤ j * width + col := by omega
    have hge_take : (word.take (count * width)).length ≤ j * width + col := by
      rw [List.length_take]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge_w,
      List.getElem?_eq_none hge_take]

theorem naorYungCascadeInput_take_eq (f : List Bool → List Bool) {n i : ℕ}
    (K x : List Bool) :
    naorYungCascadeInput f n i (K.take (i * (n + 2))) x = naorYungCascadeInput f n i K x := by
  have hrows :
      BitString.listRows i (n + 2) (K.take (i * (n + 2))) = BitString.listRows i (n + 2) K := by
    unfold BitString.listRows
    apply List.map_congr_left
    intro j hj
    exact listRow_lt_take (List.mem_range.mp hj) K
  simp only [naorYungCascadeInput, hrows]

private theorem eq_listRow_zero_append_one {M : ℕ} {x : List Bool} (hx : x.length = 2 * M) :
    BitString.listRow M 0 x ++ BitString.listRow M 1 x = x := by
  have h0 : BitString.listRow M 0 x = x.take M := by
    unfold BitString.listRow
    simp only [Nat.zero_mul, List.drop_zero]
    exact List.take_append_of_le_length (by omega)
  have h1 : BitString.listRow M 1 x = x.drop M := by
    unfold BitString.listRow
    simp only [Nat.one_mul]
    have hdrop_len : (x.drop M).length = M := by rw [List.length_drop, hx]; omega
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  rw [h0, h1, List.take_append_drop]

/-- **Deterministic step-collision extraction for `naorYungCompressionEval`**: if two distinct
`2(n + 1)`-bit inputs `x₀ ≠ x₁` collide under `naorYungCompressionEval f n K`, there exists a step
`i < n + 1` where their `(n + 2)`-bit step inputs `naorYungCascadeInput f n i K` are distinct yet
collide under `naorYungStep f n (BitString.listRow (n + 2) i K)`. -/
theorem exists_naorYungCascadeInput_collision
    {f : List Bool → List Bool} {n : ℕ} {K x₀ x₁ : List Bool}
    (hx₀ : x₀.length = 2 * (n + 1)) (hx₁ : x₁.length = 2 * (n + 1))
    (hne : x₀ ≠ x₁)
    (hcol : naorYungCompressionEval f n K x₀ = naorYungCompressionEval f n K x₁) :
    ∃ i < n + 1,
      naorYungCascadeInput f n i K x₀ ≠ naorYungCascadeInput f n i K x₁ ∧
      naorYungStep f n (BitString.listRow (n + 2) i K) (naorYungCascadeInput f n i K x₀) =
        naorYungStep f n (BitString.listRow (n + 2) i K) (naorYungCascadeInput f n i K x₁) := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  let S (x : List Bool) (j : ℕ) : List Bool :=
    naorYungCascade f n (BitString.listRows j (n + 2) K)
      (BitString.listRow (n + 1) 0 x) (BitString.listRow (n + 1) 1 x)
  have hstep_S : ∀ (x : List Bool) (j : ℕ),
      S x (j + 1) =
        naorYungStep f n (BitString.listRow (n + 2) j K) (naorYungCascadeInput f n j K x) := by
    intro x j
    have hrows_succ : BitString.listRows (j + 1) (n + 2) K =
        BitString.listRows j (n + 2) K ++ [BitString.listRow (n + 2) j K] := by
      simp [BitString.listRows, List.range_succ]
    dsimp only [S, naorYungCascadeInput]
    rw [hrows_succ, naorYungCascade_append_singleton, BitString.length_listRows]
  have hback : ∀ t ≤ n + 1,
      S x₀ (n + 1 - t) = S x₁ (n + 1 - t) ∧
      ∀ j, n + 1 - t ≤ j → j < n + 1 →
        (BitString.listRow (n + 1) 1 x₀).getD j false =
          (BitString.listRow (n + 1) 1 x₁).getD j false := by
    intro t ht
    induction t with
    | zero =>
      refine ⟨hcol, fun j hj_ge hj_lt => ?_⟩
      omega
    | succ t ih =>
      obtain ⟨hS_prev, hbits_prev⟩ := ih (by omega)
      let i := n - t
      have hi_lt : i < n + 1 := by omega
      have hsucc_eq : i + 1 = n + 1 - t := by omega
      have hsub_eq : n + 1 - (t + 1) = i := by omega
      have hstep_eq :
          naorYungStep f n (BitString.listRow (n + 2) i K) (naorYungCascadeInput f n i K x₀) =
            naorYungStep f n (BitString.listRow (n + 2) i K) (naorYungCascadeInput f n i K x₁) := by
        rw [← hstep_S x₀ i, ← hstep_S x₁ i, hsucc_eq, hS_prev]
      have hinp_eq : naorYungCascadeInput f n i K x₀ = naorYungCascadeInput f n i K x₁ := by
        by_contra hinp_ne
        exact hno i hi_lt hinp_ne hstep_eq
      have hlen_S₀ : (S x₀ i).length = n + 1 :=
        length_naorYungCascade f n _ (BitString.length_listRow (n + 1) 0 x₀) _
      have hlen_S₁ : (S x₁ i).length = n + 1 :=
        length_naorYungCascade f n _ (BitString.length_listRow (n + 1) 0 x₁) _
      obtain ⟨hSi_eq, hbit_i⟩ :=
        List.append_inj hinp_eq (hlen_S₀.trans hlen_S₁.symm)
      rw [List.singleton_inj] at hbit_i
      rw [hsub_eq]
      refine ⟨hSi_eq, fun j hj_ge hj_lt => ?_⟩
      rcases eq_or_lt_of_le hj_ge with rfl | hj_gt
      · exact hbit_i
      · exact hbits_prev j (by omega) hj_lt
  obtain ⟨hS0, hbits_all⟩ := hback (n + 1) le_rfl
  simp only [Nat.sub_self, S, BitString.listRows, List.range_zero, List.map_nil, naorYungCascade,
    List.foldl_nil] at hS0 hbits_all
  have hrow1_eq : BitString.listRow (n + 1) 1 x₀ = BitString.listRow (n + 1) 1 x₁ := by
    apply List.ext_getElem (by simp)
    intro j hj₀ hj₁
    have hj_lt : j < n + 1 := by simpa only [BitString.length_listRow] using hj₀
    have hget := hbits_all j (Nat.zero_le j) hj_lt
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj₀,
      List.getElem?_eq_getElem hj₁, Option.getD_some] using hget
  apply hne
  rw [← eq_listRow_zero_append_one hx₀, ← eq_listRow_zero_append_one hx₁, hS0, hrow1_eq]

private abbrev CascadeState := Bool × ℕ × List Bool × List Bool

private abbrev encCascadeState : CascadeState ↪ List Bool :=
  encPair encBool (encPair encUnary (encPair encBits encBits))

private def cascadeStateDecoder : Decoder encCascadeState :=
  Decoder.pair Decoder.bool (Decoder.pair Decoder.unary (Decoder.pair Decoder.bits Decoder.bits))

/-- Planted-subkey reduction from `naorYungCompressionEval f` to `naorYungStep f`: guess a dyadic
slot `slot < n + 1`, sample `slot` prefix `(n + 2)`-bit subkeys `front` before seeing the challenge
subkey `δStar`, commit to the step-`slot` target input `naorYungCascadeInput f n slot front x₀`, and
complete `K := front ++ δStar ++ back` in Stage 2. -/
noncomputable def naorYungCascadeAdversary
    (f : List Bool → List Bool) (adversary : TargetCollisionFinder) : TargetCollisionFinder where
  choose n := do
    let slot ← sampleDyadicIndex (n + 1)
    let choice ← adversary.choose n
    let active := decide (slot < n + 1)
    let i := if active then slot else 0
    let front ← BitString.sampleList (i * (n + 2))
    let w₀ := naorYungCascadeInput f n i front choice.1
    return (w₀, encCascadeState (active, i, front, choice.2))
  find n savedState δStar := do
    let s := cascadeStateDecoder.decode savedState
    let i := min n s.2.1
    let back ← BitString.sampleList ((n - i) * (n + 2))
    let x₁ ← adversary.find n s.2.2.2 (s.2.2.1 ++ δStar ++ back)
    return if s.1 then naorYungCascadeInput f n i s.2.2.1 x₁ else []

/-- `naorYungCascadeAdversary` is a uniform strict PPT `TargetCollisionFinder` whenever `f` is plain
polynomial-time and `adversary` is strict PPT. -/
theorem isPPT_naorYungCascadeAdversary
    {f : List Bool → List Bool} {adversary : TargetCollisionFinder}
    (hf : ComputableInPolyTime f encBits encBits) (ha : adversary.IsPPT) :
    (naorYungCascadeAdversary f adversary).IsPPT := by
  have hft := hf.tidy
  have hdec_t := cascadeStateDecoder.computableInPolyTime.tidy
  constructor
  · let E1 := encPair encUnary encUnary
    let E2 := encPair E1 (encPair encBits encBits)
    have hq := ComputableTidilyInPolyTime.id' (encIn := E2)
    have hact2 := hq.fst'.snd'.unary_lt'
      (ComputableTidilyInPolyTime.unary_add.comp (hq.fst'.fst'.prod (.const 1)))
    have hi2 := ComputableTidilyInPolyTime.ite' hact2 hq.fst'.snd' (.const 0)
    have hfront_len := ComputableTidilyInPolyTime.unary_mul.comp
      (hi2.prod (ComputableTidilyInPolyTime.unary_add.comp (hq.fst'.fst'.prod (.const 2))))
    have hr := ComputableTidilyInPolyTime.id' (encIn := encPair E2 encBits)
    have hw₀3 := computableTidilyInPolyTime_naorYungCascadeInput hft
      hr.fst'.fst'.fst' (hi2.comp hr.fst') hr.snd' hr.fst'.snd'.fst'
    have hst3 := ((hact2.comp hr.fst').prod ((hi2.comp hr.fst').prod
      (hr.snd'.prod hr.fst'.snd'.snd'))).encoded
    have hch := ha.choose.preprocess (.of_tidy (ComputableTidilyInPolyTime.fst encUnary encUnary))
    exact (isPPTOn_sampleDyadicIndex (.of_tidy (ComputableTidilyInPolyTime.unary_add.comp
      (ComputableTidilyInPolyTime.id'.prod (.const 1))))).bind_with
      (hch.bind_with ((isPPTOn_sampleList.preprocess (.of_tidy hfront_len)).bind_with
        (hw₀3.prod hst3).isPPTOn))
  · let EF0 := encPair encUnary (encPair encBits encBits)
    let EF1 := encPair EF0 encBits
    have hp := ComputableTidilyInPolyTime.id' (encIn := EF0)
    have hs0 := hdec_t.comp hp.snd'.fst'
    have hi0 := ComputableTidilyInPolyTime.unary_min.comp (hp.fst'.prod hs0.snd'.fst')
    have hback_len := ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.unary_sub.comp (hp.fst'.prod hi0)).prod
        (ComputableTidilyInPolyTime.unary_add.comp (hp.fst'.prod (.const 2))))
    have hq := ComputableTidilyInPolyTime.id' (encIn := EF1)
    have hK1 := ComputableTidilyInPolyTime.bitsAppend
      (ComputableTidilyInPolyTime.bitsAppend (hs0.snd'.snd'.fst'.comp hq.fst')
        hq.fst'.snd'.snd') hq.snd'
    have hfind_in := hq.fst'.fst'.prod ((hs0.snd'.snd'.snd'.comp hq.fst').prod hK1)
    have hr := ComputableTidilyInPolyTime.id' (encIn := encPair EF1 encBits)
    have hr0 := hr.fst'.fst'
    have hret := ComputableTidilyInPolyTime.ite' (hs0.fst'.comp hr0)
      (computableTidilyInPolyTime_naorYungCascadeInput hft
        hr0.fst' (hi0.comp hr0) (hs0.snd'.snd'.fst'.comp hr0) hr.snd')
      (.const [])
    exact (isPPTOn_sampleList.preprocess (.of_tidy hback_len)).bind_with
      ((ha.find.preprocess (.of_tidy hfind_in)).bind_with hret.isPPTOn)

private noncomputable def naorYungCascadeSlotTrial
    (f : List Bool → List Bool) (adversary : TargetCollisionFinder) (n slot : ℕ) : Game := do
  let choice ← ProbComp.eval (adversary.choose n)
  let active := decide (slot < n + 1)
  let i := if active then slot else 0
  let front ← BitString.uniformList (i * (n + 2))
  let w₀ := naorYungCascadeInput f n i front choice.1
  let s := cascadeStateDecoder.decode (encCascadeState (active, i, front, choice.2))
  let i' := min n s.2.1
  let δStar ← BitString.uniformList (n + 2)
  let back ← BitString.uniformList ((n - i') * (n + 2))
  let x₁ ← ProbComp.eval (adversary.find n s.2.2.2 (s.2.2.1 ++ δStar ++ back))
  let w₁ := if s.1 then naorYungCascadeInput f n i' s.2.2.1 x₁ else []
  return isCollision (naorYungStep f n) (fun m w => w.length == m + 2) n δStar w₀ w₁

private theorem naorYungCascadeSlotTrial_eq
    (f : List Bool → List Bool) (adversary : TargetCollisionFinder) (n j : ℕ)
    (hs : j < n + 1) :
    naorYungCascadeSlotTrial f adversary n j =
      ((ProbComp.eval (adversary.choose n)).bind fun choice =>
        (BitString.uniformList ((n + 1) * (n + 2))).bind fun K =>
          (ProbComp.eval (adversary.find n choice.2 K)).map fun x₁ => (choice, K, x₁)).map
        (fun t =>
          if j < n + 1 then
            isCollision (naorYungStep f n) (fun m w => w.length == m + 2) n
              (BitString.listRow (n + 2) j t.2.1)
              (naorYungCascadeInput f n j t.2.1 t.1.1)
              (naorYungCascadeInput f n j t.2.1 t.2.2)
          else false) := by
  let κ := n + 2
  let validStep (m : ℕ) (w : List Bool) : Bool := w.length == m + 2
  have hi_le : j ≤ n := by omega
  have hlen_sum : j * κ + (κ + (n - j) * κ) = (n + 1) * κ := by
    rw [show j * κ + (κ + (n - j) * κ) = (j + 1 + (n - j)) * κ by ring,
      show j + 1 + (n - j) = n + 1 by omega]
  simp only [naorYungCascadeSlotTrial, hs, decide_true, ↓reduceIte,
    cascadeStateDecoder.decode_enc, Nat.min_eq_right hi_le, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  refine PMF.bind_congr_on_support _ _ _ fun choice _ => ?_
  trans (BitString.uniformList (j * κ)).bind (fun front =>
    (BitString.uniformList (κ + (n - j) * κ)).bind (fun rest =>
      (ProbComp.eval (adversary.find n choice.2
        (front ++ rest.take κ ++ rest.drop κ))).bind fun x₁ =>
        PMF.pure
          (isCollision (naorYungStep f n) validStep n (rest.take κ)
            (naorYungCascadeInput f n j front choice.1)
            (naorYungCascadeInput f n j front x₁))))
  · refine PMF.bind_congr_on_support _ _ _ fun front _ => ?_
    exact (BitString.uniformList_bind_split κ ((n - j) * κ) _).symm
  · rw [← BitString.uniformList_bind_split (j * κ) (κ + (n - j) * κ), hlen_sum]
    refine PMF.bind_congr_on_support _ _ _ fun K hK => ?_
    have hK_len : K.length = (n + 1) * κ := BitString.length_of_mem_support_uniformList hK
    have hrejoin : K.take (j * κ) ++ (K.drop (j * κ)).take κ ++ (K.drop (j * κ)).drop κ = K := by
      rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
    have hrow : (K.drop (j * κ)).take κ = BitString.listRow κ j K := by
      have hrem : κ ≤ (K.drop (j * κ)).length := by
        rw [List.length_drop, hK_len]
        have : (j + 1) * κ ≤ (n + 1) * κ := Nat.mul_le_mul_right κ (by omega)
        have : j * κ + κ = (j + 1) * κ := by ring
        omega
      unfold BitString.listRow
      rw [List.take_append_of_le_length hrem]
    rw [hrejoin, hrow, naorYungCascadeInput_take_eq f K choice.1]
    refine PMF.bind_congr_on_support _ _ _ fun x₁ _ => ?_
    rw [naorYungCascadeInput_take_eq f K x₁]

/-- **Concrete security bound for `naorYungCompressionEval`**: the target-collision success
probability of `adversary` against `naorYungCompressionEval f` at security parameter `n` is at most
`dyadicSize (n + 1)` times that of `naorYungCascadeAdversary f adversary` against
`naorYungStep f`. -/
theorem succProbability_targetCollisionGame_naorYungCompressionEval_le
    {f : List Bool → List Bool} (adversary : TargetCollisionFinder) (n : ℕ) :
    Game.succProbability
      (ProbComp.eval
        (targetCollisionGame (fun m => (m + 1) * (m + 2))
          (naorYungCompressionEval f) (fun m x => x.length == 2 * (m + 1)) adversary n)) ≤
      (dyadicSize (n + 1) : ℝ≥0) *
        Game.succProbability
          (ProbComp.eval
            (targetCollisionGame (fun m => m + 2) (naorYungStep f)
              (fun m w => w.length == m + 2) (naorYungCascadeAdversary f adversary) n)) := by
  let κ := n + 2
  let validComp (m : ℕ) (x : List Bool) : Bool := x.length == 2 * (m + 1)
  let validStep (m : ℕ) (w : List Bool) : Bool := w.length == m + 2
  let μ : PMF ((List Bool × List Bool) × List Bool × List Bool) :=
    (ProbComp.eval (adversary.choose n)).bind fun choice =>
      (BitString.uniformList ((n + 1) * κ)).bind fun K =>
        (ProbComp.eval (adversary.find n choice.2 K)).map fun x₁ => (choice, K, x₁)
  let W (t : (List Bool × List Bool) × List Bool × List Bool) : Bool :=
    isCollision (naorYungCompressionEval f n) validComp n t.2.1 t.1.1 t.2.2
  let slotTrial := naorYungCascadeSlotTrial f adversary n
  have hred_eq :
      ProbComp.eval
        (targetCollisionGame (fun m => m + 2) (naorYungStep f) validStep
          (naorYungCascadeAdversary f adversary) n) =
        (PMF.uniformOfFintype (Fin (dyadicSize (n + 1)))).bind (fun s => slotTrial s.val) := by
    simp only [targetCollisionGame, naorYungCascadeAdversary, slotTrial,
      naorYungCascadeSlotTrial, ProbComp.eval_bind,
      ProbComp.eval_pure, eval_sampleDyadicIndex, BitString.eval_sampleList,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
      PMF.bind_map, Function.comp_def, validStep]
  have hcomp_eq :
      ProbComp.eval
        (targetCollisionGame (fun m => (m + 1) * (m + 2))
          (naorYungCompressionEval f) validComp adversary n) =
        μ.map W := by
    simp only [targetCollisionGame, μ, W, ProbComp.eval_bind, ProbComp.eval_pure,
      BitString.eval_sampleList, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, κ]
  let Wi (s : Fin (dyadicSize (n + 1)))
      (t : (List Bool × List Bool) × List Bool × List Bool) : Bool :=
    if s.val < n + 1 then
      isCollision (naorYungStep f n) validStep n (BitString.listRow κ s.val t.2.1)
        (naorYungCascadeInput f n s.val t.2.1 t.1.1)
        (naorYungCascadeInput f n s.val t.2.1 t.2.2)
    else false
  have hcover :
      ∀ t ∈ μ.support, W t = true → ∃ s : Fin (dyadicSize (n + 1)), Wi s t = true := by
    rintro ⟨choice, K, x₁⟩ ht hW
    simp only [μ, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at ht
    obtain ⟨choice', _, K', _, ⟨x₁', _, htuple⟩⟩ := ht
    injection htuple with h1 h23
    injection h23 with h2 h3
    subst h1 h2 h3
    rw [isCollision_eq_true_iff] at hW
    obtain ⟨hx₀_v, hx₁_v, hne, hcol⟩ := hW
    obtain ⟨i, hi_lt, hw_ne, hw_col⟩ :=
      exists_naorYungCascadeInput_collision (beq_iff_eq.mp hx₀_v) (beq_iff_eq.mp hx₁_v) hne hcol
    refine ⟨⟨i, hi_lt.trans (lt_dyadicSize (n + 1))⟩, ?_⟩
    simp only [Wi, hi_lt, ↓reduceIte, isCollision_eq_true_iff, validStep, beq_iff_eq,
      length_naorYungCascadeInput, true_and, κ]
    exact ⟨hw_ne, hw_col⟩
  have hsum_le : (μ.map W) true ≤ ∑ s : Fin (dyadicSize (n + 1)), (slotTrial s.val) true := by
    let F (j : ℕ) (t : (List Bool × List Bool) × List Bool × List Bool) : Bool :=
      if hj : j < dyadicSize (n + 1) then Wi ⟨j, hj⟩ t else false
    have hmono :
        (μ.map W) true ≤
          (μ.map (fun t => (List.range (dyadicSize (n + 1))).any (fun j => F j t))) true := by
      refine PMF.map_true_mono μ fun t ht hW => ?_
      obtain ⟨⟨j, hj⟩, hs⟩ := hcover t ht hW
      refine List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
      simpa only [F, hj, ↓reduceDIte] using hs
    refine (hmono.trans (PMF.map_any_range_true_le_sum μ (dyadicSize (n + 1)) F)).trans ?_
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj_lt : j < dyadicSize (n + 1) := Finset.mem_range.mp hj
    have hF : F j = Wi ⟨j, hj_lt⟩ := funext fun t => by simp only [F, hj_lt, ↓reduceDIte]
    simp only [hF, hj_lt, ↓reduceDIte]
    by_cases hs : j < n + 1
    · dsimp only [slotTrial]
      rw [naorYungCascadeSlotTrial_eq f adversary n j hs]
    · have hWi : Wi ⟨j, hj_lt⟩ = fun _ => false := funext fun t => by
        simp only [Wi, hs, ↓reduceIte]
      rw [hWi]
      simp
  have hpos : (0 : ℝ≥0) < dyadicSize (n + 1) := by exact_mod_cast dyadicSize_pos (n + 1)
  rw [hcomp_eq, hred_eq, Game.succProbability_uniform, Fintype.card_fin,
    mul_div_cancel₀ _ hpos.ne']
  have hmono := ENNReal.toNNReal_mono (by finiteness) hsum_le
  rwa [ENNReal.toNNReal_sum fun s _ => PMF.apply_ne_top _ _] at hmono

/-- **Naor–Yung `KeyedCompressionFamily`** ([NaorYung1989], Section 3; [Goldreich2004],
Section 6.4.3.2): compresses `2(n + 1)`-bit blocks to `(n + 1)`-bit blocks under
`((n + 1) * (n + 2))`-bit keys using any plain polynomial-time function `f`. -/
@[expose]
def naorYungCompression {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) : KeyedCompressionFamily where
  keyLen n := (n + 1) * (n + 2)
  blockLen n := n + 1
  eval := naorYungCompressionEval f
  keyLen_polyTime := by
    exact .of_tidy (ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.unary_add.comp
        (ComputableTidilyInPolyTime.id'.prod (.const 1))).prod
        (ComputableTidilyInPolyTime.unary_add.comp
          (ComputableTidilyInPolyTime.id'.prod (.const 2)))))
  blockLen_polyTime := by exact ComputableInPolyTime.unary_succ
  polyTime := computableInPolyTime_naorYungCompressionEval hf
  le_blockLen n := Nat.le_succ n
  length_eq n K x _ _ := length_naorYungCompressionEval f n K x

/-- **Naor–Yung compression theorem** ([NaorYung1989], Section 3; [Goldreich2004],
Section 6.4.3.2): if `f` is a `OneWayPermutation`, `naorYungCompression hf.oneWay.polyTime` is a
target collision-resistant `KeyedCompressionFamily`. -/
theorem OneWayPermutation.targetCollisionResistant_naorYungCompression
    {f : List Bool → List Bool} (hf : OneWayPermutation f) :
    (naorYungCompression hf.oneWay.polyTime).TargetCollisionResistant := by
  apply TargetCollisionResistantOn.of_negligible
  intro adversary hadversary
  have hstep_tcr := hf.targetCollisionResistantOn_naorYungStep
  have hredPPT : (naorYungCascadeAdversary f adversary).IsPPT :=
    isPPT_naorYungCascadeAdversary hf.oneWay.polyTime hadversary
  have hloss_pb : PolynomiallyBounded (fun n => dyadicSize (n + 1)) :=
    (ComputableInPolyTime.unary_dyadicSize.tidy.comp
      (ComputableTidilyInPolyTime.unary_add.comp
        (ComputableTidilyInPolyTime.id'.prod (.const 1)))).polynomiallyBounded
  refine negligible_of_le
    ((hstep_tcr.negligible (naorYungCascadeAdversary f adversary) hredPPT).polynomiallyBounded_mul
      hloss_pb)
    fun n => ?_
  exact succProbability_targetCollisionGame_naorYungCompressionEval_le adversary n

/-- **Naor–Yung unrestricted `KeyedHashFamily`** ([NaorYung1989], 1995 revision, Sections 2.3 and
3): hashes arbitrary-length bit strings `List Bool` to `(n + 1)`-bit digests under
`(n + 1)^2 * (n + 2)`-bit keys via `(naorYungCompression hf).treeHash` (inheriting `treeHash`'s
`< 2 ^ n` finite-parameter tree capacity). -/
@[expose]
def naorYungHash {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) : KeyedHashFamily :=
  (naorYungCompression hf).treeHash

/-- **Naor–Yung UOWHF theorem** ([NaorYung1989], 1995 revision, Sections 2.3 and 3;
[Goldreich2004], Section 6.4.3.2): if `f` is a `OneWayPermutation`,
`naorYungHash hf.oneWay.polyTime` is unrestrictedly target collision-resistant on all `List Bool`.
-/
theorem OneWayPermutation.targetCollisionResistant_naorYungHash
    {f : List Bool → List Bool} (hf : OneWayPermutation f) :
    (naorYungHash hf.oneWay.polyTime).TargetCollisionResistant :=
  KeyedCompressionFamily.targetCollisionResistant_treeHash
    hf.targetCollisionResistant_naorYungCompression

/-- Every `OneWayPermutation` yields an unrestricted target collision-resistant `KeyedHashFamily`
on `List Bool`. -/
theorem OneWayPermutation.exists_targetCollisionResistant_keyedHashFamily
    {f : List Bool → List Bool} (hf : OneWayPermutation f) :
    ∃ H : KeyedHashFamily, H.TargetCollisionResistant :=
  ⟨naorYungHash hf.oneWay.polyTime, hf.targetCollisionResistant_naorYungHash⟩

end Cslib.Crypto
