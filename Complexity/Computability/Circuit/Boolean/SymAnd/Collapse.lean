/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.SymAnd
public import Complexity.Computability.Circuit.Boolean.SymAnd.Mobius
import Complexity.Foundations.BooleanAnalysis.LowDegree.Polynomial
import Complexity.Foundations.Data.Polynomial.ModulusAmplifier
import Mathlib.Data.ZMod.Basic

/-!
# Collapsing towers of modular polynomial layers into `SYM ∘ AND`

A modular polynomial layer on a finite set `T` of slots (`Circuits.Boolean.ModPolyLayer`) has a
modulus `p` and assigns to each slot `t` an integer polynomial `q t` of the previous values; it
updates slot `t` to whether `q t ≢ 0 (mod p)` (`ModPolyLayer.step`). A list of layers is run from
the last to the first (`ModPolyLayer.run`). These are the stratified modular polynomial circuits
of Beigel and Tarui [BeigelTarui1994, Section 2.2], with every slot evaluated at every level.

**Collapse.** A `SYM ∘ AND` circuit on top of such a layer, with prime `p`, collapses into a
single `SYM ∘ AND` circuit (`SymAnd.exists_eval_eq_eval_step`). With `M = p ^ k` above the size of
the top circuit, the modulus-amplified bits `h_t = 1 - p_k(q_t ^ (p - 1))` agree with the layer's
outputs modulo `M` (`Polynomial.one_sub_parityAmplifier_eval_pow_modEq`). Hence
`∑_{S ∈ gates} ∏_{t ∈ S} h_t` is a low-degree integer function congruent modulo `M` to the
number of satisfied gates, which is below `M` (`SymAnd.amplifiedCount_modEq`). The canonical
circuit of that function modulo `M` (`SymAnd.ofLowDegree`, with AND multiplicities its subset
Möbius coefficients) is the collapsed circuit (`SymAnd.collapseStep`), and its symmetric gate reads
its argument modulo `M`. This is the inductive step of [BeigelTarui1994, Lemma 2.8] with their
Fact 2.7 (Section 2.4).

Iterating over `L` layers whose primes, slot-polynomial degrees and `log₂(|T| + 1)` are at most
`B`, starting from a circuit of fan-in at most `B` and size at most `2 ^ B`, gives a
`SYM ∘ AND` circuit of fan-in at most `(2B) ^ (5 ^ L)` and size at most `2 ^ ((2B) ^ (5 ^ L))`
(`SymAnd.collapseRun`, `SymAnd.exists_eval_eq_eval_run`). Reading one slot of the tower is the
special case `SymAnd.exists_eval_eq_run_apply`. For a fixed number of layers and `B`
polylogarithmic, this is the quasi-polynomial size and polylogarithmic fan-in of
[BeigelTarui1994, Theorem 1.1].

The source states the collapse for one arbitrary modulus `m` per level, requiring each level
polynomial to be `0` or `1` modulo `m`. Here each level has a prime modulus, and Fermat's little
theorem normalizes arbitrary integer values, so no `0`/`1` promise is needed. Composite moduli
reduce to prime moduli through prime-power digits ([BeigelTarui1994, Lemma 2.1]). That reduction,
and the passage from ACC⁰ circuits (`Circuits.Boolean.AC0Mod`) to towers of these layers, are in
`Complexity.Computability.Circuit.Boolean.SymAnd.ACC0`. The collapsed circuit reads all slots of
`T`; restricting the non-input slots to their initial value `false` and dropping the AND gates
that meet them (`SymAnd.restrict`) gives a circuit over the inputs alone.

## Main definitions

* `Cslib.Circuits.Boolean.ModPolyLayer`: a layer of modular polynomial gates.
* `Cslib.Circuits.Boolean.ModPolyLayer.step`, `ModPolyLayer.run`.
* `Cslib.Circuits.Boolean.SymAnd.collapseStep`, `SymAnd.collapseRun`: the explicit collapse of one
  layer and of a tower.

## Main results

* `Cslib.Circuits.Boolean.SymAnd.eval_collapseStep`, `SymAnd.eval_collapseRun`: what the explicit
  collapses compute, with their fan-in and size bounds.
* `Cslib.Circuits.Boolean.SymAnd.exists_eval_eq_eval_step`: one layer collapses into the
  `SYM ∘ AND` circuit above it.
* `Cslib.Circuits.Boolean.SymAnd.exists_eval_eq_eval_run`: a tower of layers collapses, with
  explicit fan-in and size bounds.
* `Cslib.Circuits.Boolean.SymAnd.exists_eval_eq_run_apply`: every slot of a tower is computed by
  a `SYM ∘ AND` circuit.

## References

* [R. Beigel, J. Tarui, *On ACC*][BeigelTarui1994]
-/

public section

namespace Cslib.Circuits.Boolean

open Finset BitString Polynomial

/-- A layer of modular polynomial gates on slots `T`: slot `t` becomes whether the integer
polynomial `q t` of the previous slot values is nonzero modulo `p`. Degrees and primality are
hypotheses of the theorems using a layer. -/
structure ModPolyLayer (T : Type*) where
  /-- The modulus of the layer. -/
  p : ℕ
  /-- The integer polynomial read by each slot, as a function of the previous slot values. -/
  q : T → (T → Bool) → ℤ

namespace ModPolyLayer

variable {T : Type*}

/-- One step: every slot `t` becomes whether `q t v` is nonzero modulo `p`. -/
@[expose] def step (L : ModPolyLayer T) (v : T → Bool) : T → Bool :=
  fun t => decide (L.q t v % L.p ≠ 0)

/-- Run a list of layers on `v`, from the last layer to the first. -/
@[expose] def run (Ls : List (ModPolyLayer T)) (v : T → Bool) : T → Bool :=
  Ls.foldr step v

/-- Running no layers returns the input. -/
@[simp] theorem run_nil (v : T → Bool) : run [] v = v := rfl

/-- Running `L :: Ls` applies `L` after `Ls`. -/
@[simp] theorem run_cons (L : ModPolyLayer T) (Ls : List (ModPolyLayer T)) (v : T → Bool) :
    run (L :: Ls) v = L.step (run Ls v) := rfl

/-- Running `Ls ++ Ls'` runs `Ls` after `Ls'`. -/
theorem run_append (Ls Ls' : List (ModPolyLayer T)) (v : T → Bool) :
    run (Ls ++ Ls') v = run Ls (run Ls' v) := by
  simp only [run, List.foldr_append]

end ModPolyLayer

namespace SymAnd

variable {T : Type*}

/-- Sums over the sets of `G` of products of degree-`E` functions have degree `F * E` when every
set has at most `F` elements. -/
private theorem sum_prod_mem_lowDegree {G : Multiset (Finset T)} {F E : ℕ}
    (hG : ∀ S ∈ G, #S ≤ F) {g : T → (T → Bool) → ℤ} (hg : ∀ t, g t ∈ lowDegree ℤ T E) :
    (fun v => (G.map fun S => ∏ t ∈ S, g t v).sum) ∈ lowDegree ℤ T (F * E) := by
  induction G using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.sum_zero]
    exact Submodule.zero_mem (lowDegree ℤ T (F * E))
  | cons S G ih =>
    have hS : (fun v => ∏ t ∈ S, g t v) ∈ lowDegree ℤ T (F * E) := by
      have := prod_mem_lowDegree S fun t _ => hg t
      rw [Finset.prod_fn] at this
      exact lowDegree_mono (Nat.mul_le_mul_right E (hG S (Multiset.mem_cons_self S G))) this
    have hrest := ih fun S' hS' => hG S' (Multiset.mem_cons_of_mem hS')
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact Submodule.add_mem _ hS hrest

/-- The modulus-amplified count of `C` after the layer `L`: the sum over the gates `S` of `C` of
`∏_{t ∈ S} (1 - p_k(q_t ^ (p - 1)))`. Modulo `p ^ k` it is the number of gates of `C` satisfied
after `L` (`SymAnd.amplifiedCount_modEq`). -/
noncomputable def amplifiedCount (C : SymAnd T) (L : ModPolyLayer T) (k : ℕ) (v : T → Bool) : ℤ :=
  (C.gates.map fun S => ∏ t ∈ S, (1 - (parityAmplifier k).eval (L.q t v ^ (L.p - 1)))).sum

/-- The amplified count has degree at most `C.fanIn * (2k - 1)(p - 1)D` when the slot polynomials
have degree at most `D`. -/
theorem amplifiedCount_mem_lowDegree (C : SymAnd T) (L : ModPolyLayer T) {D : ℕ}
    (hq : ∀ t, L.q t ∈ lowDegree ℤ T D) (k : ℕ) :
    amplifiedCount C L k ∈ lowDegree ℤ T (C.fanIn * ((2 * k - 1) * ((L.p - 1) * D))) := by
  refine sum_prod_mem_lowDegree (fun S hS => card_le_fanIn hS) fun t => ?_
  have h1 : (fun v => L.q t v ^ (L.p - 1)) ∈ lowDegree ℤ T ((L.p - 1) * D) :=
    pow_mem_lowDegree (hq t) _
  exact one_sub_mem_lowDegree (polynomial_eval_mem_lowDegree h1 (natDegree_parityAmplifier_le k))

/-- For a prime modulus, the amplified count is the number of gates of `C` satisfied after `L`,
modulo `p ^ k` [BeigelTarui1994, Fact 2.7]. -/
theorem amplifiedCount_modEq (C : SymAnd T) (L : ModPolyLayer T) (hp : L.p.Prime) (k : ℕ)
    (v : T → Bool) :
    amplifiedCount C L k v ≡ C.count (L.step v) [ZMOD ((L.p ^ k : ℕ) : ℤ)] := by
  rw [natCast_count_eq_sum, ← ZMod.intCast_eq_intCast_iff]
  simp only [amplifiedCount, Int.cast_multiset_sum, Multiset.map_map, Function.comp_def,
    Int.cast_prod, BitString.monomial]
  congr 1
  refine Multiset.map_congr rfl fun S _ => Finset.prod_congr rfl fun t _ => ?_
  refine (ZMod.intCast_eq_intCast_iff _ _ _).2 ?_
  have := one_sub_parityAmplifier_eval_pow_modEq hp k (L.q t v)
  simp only [ModPolyLayer.step, bitVal, decide_eq_true_eq, Nat.cast_pow]
  exact this

/-- **One explicit collapse step** [BeigelTarui1994, Lemma 2.8]: the canonical circuit
(`SymAnd.ofLowDegree`) of the amplified count `amplifiedCount C L k` modulo `p ^ k`, up to its
degree bound `C.fanIn * (2k - 1)(p - 1)D`, below the symmetric gate of `C`. -/
noncomputable def collapseStep [Fintype T] [DecidableEq T] (C : SymAnd T) (L : ModPolyLayer T)
    (k D : ℕ) : SymAnd T :=
  ofLowDegree (C.fanIn * ((2 * k - 1) * ((L.p - 1) * D))) (L.p ^ k) (amplifiedCount C L k) C.out

/-- **What the collapse step computes**: `C` after `L`, when `p` is prime, the slot polynomials have
degree at most `D` and `C.size < p ^ k`. -/
theorem eval_collapseStep [Fintype T] [DecidableEq T] (C : SymAnd T) (L : ModPolyLayer T)
    (hp : L.p.Prime) {D : ℕ} (hq : ∀ t, L.q t ∈ lowDegree ℤ T D) {k : ℕ} (hk : C.size < L.p ^ k)
    (v : T → Bool) : (collapseStep C L k D).eval v = C.eval (L.step v) := by
  rw [collapseStep, eval_ofLowDegree (amplifiedCount_mem_lowDegree C L hq k) (pow_pos hp.pos k)]
  have h1 : amplifiedCount C L k v % ((L.p ^ k : ℕ) : ℤ) =
      ((C.count (L.step v) : ℕ) : ℤ) % ((L.p ^ k : ℕ) : ℤ) := amplifiedCount_modEq C L hp k v
  rw [h1, ← Int.natCast_mod, Nat.mod_eq_of_lt ((C.count_le_size _).trans_lt hk),
    Int.toNat_natCast]
  rfl

/-- The collapse step has fan-in at most `C.fanIn * (2k - 1)(p - 1)D`. -/
theorem fanIn_collapseStep_le [Fintype T] [DecidableEq T] (C : SymAnd T) (L : ModPolyLayer T)
    (k D : ℕ) : (collapseStep C L k D).fanIn ≤ C.fanIn * ((2 * k - 1) * ((L.p - 1) * D)) :=
  fanIn_ofLowDegree_le _ _ _ _

/-- The collapse step has at most `p ^ k * (|T| + 1) ^ F` AND gates, where
`F = C.fanIn * (2k - 1)(p - 1)D` is its fan-in bound. -/
theorem size_collapseStep_le [Fintype T] [DecidableEq T] (C : SymAnd T) (L : ModPolyLayer T)
    (hp : 0 < L.p) (k D : ℕ) :
    (collapseStep C L k D).size ≤
      L.p ^ k * (Fintype.card T + 1) ^ (C.fanIn * ((2 * k - 1) * ((L.p - 1) * D))) :=
  size_ofLowDegree_le _ (pow_pos hp k) _ _

/-- **Collapsing one modular layer** [BeigelTarui1994, Lemma 2.8]. Let `C` be a `SYM ∘ AND`
circuit on slots `T` and `L` a layer with prime modulus `p` whose slot polynomials have degree at
most `D`. If `C.size < p ^ k`, then some `SYM ∘ AND` circuit computes `C` after `L`, with fan-in at
most `F = C.fanIn * (2k - 1)(p - 1)D` and at most `p ^ k * (|T| + 1) ^ F` AND gates, where the
exponent `F` is this new fan-in bound. The circuit is `SymAnd.collapseStep C L k D`. -/
theorem exists_eval_eq_eval_step [Fintype T] (C : SymAnd T) (L : ModPolyLayer T)
    (hp : L.p.Prime) {D : ℕ} (hq : ∀ t, L.q t ∈ lowDegree ℤ T D) {k : ℕ}
    (hk : C.size < L.p ^ k) :
    ∃ C' : SymAnd T, (∀ v, C'.eval v = C.eval (L.step v)) ∧
      C'.fanIn ≤ C.fanIn * ((2 * k - 1) * ((L.p - 1) * D)) ∧
      C'.size ≤ L.p ^ k * (Fintype.card T + 1) ^ (C.fanIn * ((2 * k - 1) * ((L.p - 1) * D))) := by
  classical
  exact ⟨collapseStep C L k D, eval_collapseStep C L hp hq hk, fanIn_collapseStep_le C L k D,
    size_collapseStep_le C L hp.pos k D⟩

private theorem tower_fanIn_le {B F p : ℕ} (hF : F ≤ B) (hp : p ≤ B) :
    F * ((2 * (B + 1) - 1) * ((p - 1) * B)) ≤ 3 * B ^ 4 := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp only [Nat.le_zero] at hF
    simp [hF]
  have h1 : 2 * (B + 1) - 1 ≤ 3 * B := by omega
  have h2 : (p - 1) * B ≤ B * B := Nat.mul_le_mul_right B (by omega)
  calc F * ((2 * (B + 1) - 1) * ((p - 1) * B)) ≤ B * (3 * B * (B * B)) := by gcongr
    _ = 3 * B ^ 4 := by ring

private theorem tower_log_size_le {B e : ℕ} (hB : 1 ≤ B) (he : e ≤ 3 * B ^ 4) :
    B * (B + 1) + B * e ≤ 5 * B ^ 5 := by
  have h1 : B ^ 1 ≤ B ^ 5 := Nat.pow_le_pow_right hB (by norm_num)
  have h2 : B ^ 2 ≤ B ^ 5 := Nat.pow_le_pow_right hB (by norm_num)
  have h3 : B * e ≤ B * (3 * B ^ 4) := Nat.mul_le_mul_left B he
  have h4 : B * (3 * B ^ 4) = 3 * B ^ 5 := by ring
  have h5 : B * (B + 1) = B ^ 2 + B ^ 1 := by ring
  rw [h5]
  linarith

private theorem tower_size_le {B B' p N e : ℕ} (hpB : p ≤ 2 ^ B) (hN : N ≤ 2 ^ B)
    (hle : B * (B + 1) + B * e ≤ B') : p ^ (B + 1) * N ^ e ≤ 2 ^ B' :=
  calc p ^ (B + 1) * N ^ e ≤ (2 ^ B) ^ (B + 1) * (2 ^ B) ^ e := by gcongr
    _ = 2 ^ (B * (B + 1) + B * e) := by rw [← pow_mul, ← pow_mul, ← pow_add]
    _ ≤ 2 ^ B' := Nat.pow_le_pow_right (by norm_num) hle

/-- **The explicit collapse of a tower**: collapse the layers of `Ls` one at a time from the
outermost, with `k = B + 1` and degree bound `B` at the first layer and `5 B ^ 5` in place of `B`
afterwards. -/
noncomputable def collapseRun [Fintype T] [DecidableEq T] (C : SymAnd T) :
    List (ModPolyLayer T) → ℕ → SymAnd T
  | [], _ => C
  | L :: Ls, B => collapseRun (collapseStep C L (B + 1) B) Ls (5 * B ^ 5)

private theorem collapseRun_spec [Fintype T] [DecidableEq T] (C : SymAnd T)
    (Ls : List (ModPolyLayer T)) {B : ℕ}
    (hLs : ∀ L ∈ Ls, L.p.Prime ∧ L.p ≤ B ∧ ∀ t, L.q t ∈ lowDegree ℤ T B)
    (hT : Fintype.card T + 1 ≤ 2 ^ B) (hf : C.fanIn ≤ B) (hs : C.size ≤ 2 ^ B) :
    (∀ v, (collapseRun C Ls B).eval v = C.eval (ModPolyLayer.run Ls v)) ∧
      (collapseRun C Ls B).fanIn ≤ (2 * B) ^ 5 ^ Ls.length ∧
      (collapseRun C Ls B).size ≤ 2 ^ (2 * B) ^ 5 ^ Ls.length := by
  induction Ls generalizing C B with
  | nil =>
    refine ⟨fun v => rfl, ?_, ?_⟩
    · simp only [collapseRun, List.length_nil, pow_zero, pow_one]
      omega
    · simp only [collapseRun, List.length_nil, pow_zero, pow_one]
      exact hs.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  | cons L Ls ih =>
    obtain ⟨hp, hpB, hq⟩ := hLs L List.mem_cons_self
    have hB : 1 ≤ B := le_trans hp.one_lt.le hpB
    have hk : C.size < L.p ^ (B + 1) :=
      calc C.size ≤ 2 ^ B := hs
        _ < 2 ^ (B + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self B)
        _ ≤ L.p ^ (B + 1) := Nat.pow_le_pow_left hp.two_le _
    have he := tower_fanIn_le hf hpB
    have h45 : 3 * B ^ 4 ≤ 5 * B ^ 5 := by gcongr <;> omega
    have hB₁ : B ≤ 5 * B ^ 5 := by
      have : B ^ 1 ≤ B ^ 5 := Nat.pow_le_pow_right hB (by norm_num)
      rw [pow_one] at this
      omega
    obtain ⟨hC', hf', hs'⟩ := ih (collapseStep C L (B + 1) B) (B := 5 * B ^ 5)
      (fun L' hL' =>
        have h := hLs L' (List.mem_cons_of_mem L hL')
        ⟨h.1, h.2.1.trans hB₁, fun t => lowDegree_mono hB₁ (h.2.2 t)⟩)
      (hT.trans (Nat.pow_le_pow_right (by norm_num) hB₁))
      ((fanIn_collapseStep_le C L (B + 1) B).trans (he.trans h45))
      ((size_collapseStep_le C L hp.pos (B + 1) B).trans
        (tower_size_le (hpB.trans Nat.lt_two_pow_self.le) hT (tower_log_size_le hB he)))
    have hbase : 2 * (5 * B ^ 5) ≤ (2 * B) ^ 5 :=
      calc 2 * (5 * B ^ 5) = 10 * B ^ 5 := by ring
        _ ≤ 32 * B ^ 5 := Nat.mul_le_mul_right _ (by norm_num)
        _ = (2 * B) ^ 5 := by ring
    have hexp : (2 * (5 * B ^ 5)) ^ 5 ^ Ls.length ≤ (2 * B) ^ 5 ^ (L :: Ls).length := by
      have h5 : 5 ^ (L :: Ls).length = 5 * 5 ^ Ls.length := by
        rw [List.length_cons, pow_succ']
      rw [h5, pow_mul]
      exact Nat.pow_le_pow_left hbase _
    refine ⟨fun v => by rw [collapseRun, hC', ModPolyLayer.run_cons,
      eval_collapseStep C L hp hq hk], hf'.trans hexp,
      hs'.trans (Nat.pow_le_pow_right (by norm_num) hexp)⟩

/-- **What the explicit tower collapse computes**: under the hypotheses of
`SymAnd.exists_eval_eq_eval_run`, `collapseRun C Ls B` computes `C` after running `Ls`. -/
theorem eval_collapseRun [Fintype T] [DecidableEq T] (C : SymAnd T) (Ls : List (ModPolyLayer T))
    {B : ℕ} (hLs : ∀ L ∈ Ls, L.p.Prime ∧ L.p ≤ B ∧ ∀ t, L.q t ∈ lowDegree ℤ T B)
    (hT : Fintype.card T + 1 ≤ 2 ^ B) (hf : C.fanIn ≤ B) (hs : C.size ≤ 2 ^ B) (v : T → Bool) :
    (collapseRun C Ls B).eval v = C.eval (ModPolyLayer.run Ls v) :=
  (collapseRun_spec C Ls hLs hT hf hs).1 v

/-- The explicit tower collapse has fan-in at most `(2B) ^ (5 ^ L)`. -/
theorem fanIn_collapseRun_le [Fintype T] [DecidableEq T] (C : SymAnd T)
    (Ls : List (ModPolyLayer T)) {B : ℕ}
    (hLs : ∀ L ∈ Ls, L.p.Prime ∧ L.p ≤ B ∧ ∀ t, L.q t ∈ lowDegree ℤ T B)
    (hT : Fintype.card T + 1 ≤ 2 ^ B) (hf : C.fanIn ≤ B) (hs : C.size ≤ 2 ^ B) :
    (collapseRun C Ls B).fanIn ≤ (2 * B) ^ 5 ^ Ls.length :=
  (collapseRun_spec C Ls hLs hT hf hs).2.1

/-- The explicit tower collapse has at most `2 ^ ((2B) ^ (5 ^ L))` AND gates. -/
theorem size_collapseRun_le [Fintype T] [DecidableEq T] (C : SymAnd T)
    (Ls : List (ModPolyLayer T)) {B : ℕ}
    (hLs : ∀ L ∈ Ls, L.p.Prime ∧ L.p ≤ B ∧ ∀ t, L.q t ∈ lowDegree ℤ T B)
    (hT : Fintype.card T + 1 ≤ 2 ^ B) (hf : C.fanIn ≤ B) (hs : C.size ≤ 2 ^ B) :
    (collapseRun C Ls B).size ≤ 2 ^ (2 * B) ^ 5 ^ Ls.length :=
  (collapseRun_spec C Ls hLs hT hf hs).2.2

/-- **Collapsing a tower of modular layers** [BeigelTarui1994, Lemma 2.8]. Let every layer of
`Ls` have a prime modulus at most `B` and slot polynomials of degree at most `B`, with
`|T| + 1 ≤ 2 ^ B`. A `SYM ∘ AND` circuit of fan-in at most `B` and size at most `2 ^ B`, applied
after running `Ls`, is computed by a single `SYM ∘ AND` circuit of fan-in at most
`(2B) ^ (5 ^ L)` and size at most `2 ^ ((2B) ^ (5 ^ L))`, where `L` is the number of layers. The
circuit is `SymAnd.collapseRun C Ls B`. -/
theorem exists_eval_eq_eval_run [Fintype T] (C : SymAnd T) (Ls : List (ModPolyLayer T)) {B : ℕ}
    (hLs : ∀ L ∈ Ls, L.p.Prime ∧ L.p ≤ B ∧ ∀ t, L.q t ∈ lowDegree ℤ T B)
    (hT : Fintype.card T + 1 ≤ 2 ^ B) (hf : C.fanIn ≤ B) (hs : C.size ≤ 2 ^ B) :
    ∃ C' : SymAnd T, (∀ v, C'.eval v = C.eval (ModPolyLayer.run Ls v)) ∧
      C'.fanIn ≤ (2 * B) ^ 5 ^ Ls.length ∧ C'.size ≤ 2 ^ (2 * B) ^ 5 ^ Ls.length := by
  classical
  exact ⟨collapseRun C Ls B, eval_collapseRun C Ls hLs hT hf hs,
    fanIn_collapseRun_le C Ls hLs hT hf hs, size_collapseRun_le C Ls hLs hT hf hs⟩

/-- **Every slot of a tower is a `SYM ∘ AND` circuit.** Under the hypotheses of
`exists_eval_eq_eval_run`, slot `t` after running `Ls` is computed by a `SYM ∘ AND` circuit of
fan-in at most `(2B) ^ (5 ^ L)` and size at most `2 ^ ((2B) ^ (5 ^ L))`. -/
theorem exists_eval_eq_run_apply [Fintype T] (Ls : List (ModPolyLayer T)) (t : T) {B : ℕ}
    (hLs : ∀ L ∈ Ls, L.p.Prime ∧ L.p ≤ B ∧ ∀ t, L.q t ∈ lowDegree ℤ T B)
    (hT : Fintype.card T + 1 ≤ 2 ^ B) :
    ∃ C : SymAnd T, (∀ v, C.eval v = ModPolyLayer.run Ls v t) ∧
      C.fanIn ≤ (2 * B) ^ 5 ^ Ls.length ∧ C.size ≤ 2 ^ (2 * B) ^ 5 ^ Ls.length := by
  have hB : 1 ≤ B := by
    rcases Nat.eq_zero_or_pos B with rfl | hB
    · have : 0 < Fintype.card T := Fintype.card_pos_iff.2 ⟨t⟩
      simp only [pow_zero] at hT
      omega
    · exact hB
  obtain ⟨C, hC, hf, hs⟩ := exists_eval_eq_eval_run (slot t) Ls hLs hT
    (by rw [fanIn_slot]; exact hB) (by rw [size_slot]; exact Nat.one_le_two_pow)
  exact ⟨C, fun v => by rw [hC, eval_slot], hf, hs⟩

end SymAnd

end Cslib.Circuits.Boolean
