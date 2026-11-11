/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.MINKT
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Foundations.Data.Option

/-!
# Partial-string time-bounded Kolmogorov complexity (`MINKT*`)

`MINKT*` is the partial-string variant of `MINKT` [Hirahara2022, Section I, p. 971]. An instance
is a partial string `x ∈ {0, 1, *}*` with a time bound `t` and a size threshold `s`, and it is a
yes-instance when some total string `y` that is *consistent* with `x`, meaning that every bit of
`x` is `*` or equal to the bit of `y` at the same position [Hirahara2022, footnote 5], satisfies
`K^t(y) ≤ s`. Here `K^t` is the library's `timeBoundedAt`, the same measure as for `MINKT`. It is a
variant of the source's measure, which charges the running time as in KT complexity, with oracle
access to the description of the machine [Hirahara2022, footnote 6, p. 971]: `timeBoundedAt`
counts the steps of the described machine, which outputs the whole string.

This file defines the problem, its encoding and its witness check, and proves that it lies in `NP`
and that `MINKT` reduces to it. NP-hardness under randomized reductions
[Hirahara2022, Theorem I.2] is `MINKTStar.rpHard`, in the `Hardness` submodule.

## Encoding

`MINKTStar.enc` writes the partial string as the framed list of its entries, `*` (`none`) as the
empty word and a bit `b` as `[true, b]` (`encList (encOption encBool)`, the scheme of
`Cslib.PartialMCSP.encTable`), followed by `1^time` and `1^size` in unary as for `MINKT.enc`.

## Main definitions

* `Cslib.Kolmogorov.MINKTStar.Consistent`: a total string is consistent with a partial string.
* `Cslib.Kolmogorov.MINKTStar.Instance`, `Cslib.Kolmogorov.MINKTStar`,
  `Cslib.Kolmogorov.MINKTStar.enc`: instances, yes-instances and encoding.
* `Cslib.Kolmogorov.MINKTStar.check`: polynomial-time witness check.
* `Cslib.Kolmogorov.MINKTStar.ofTotal`: the instance with no `*` entries.

## Main results

* `Cslib.Kolmogorov.MINKTStar.consistent_iff`: consistency as equal lengths and agreement on the
  specified positions.
* `Cslib.Kolmogorov.MINKTStar.mem_iff_exists_program`: membership via a short program.
* `Cslib.Kolmogorov.MINKTStar.mem_of_size_le`, `Cslib.Kolmogorov.MINKTStar.mem_of_time_le`:
  monotonicity in the thresholds.
* `Cslib.Kolmogorov.MINKTStar.mem_NP`: `MINKTStar ∈ NP MINKTStar.enc`.
* `Cslib.Kolmogorov.MINKTStar.polyTimeReducible_MINKT_MINKTStar`: `MINKT` reduces to `MINKTStar`
  in polynomial time, by `ofTotal`.

## References

* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
* [K.-I. Ko, *On the Complexity of Learning Minimum Time-Bounded Turing Machines*][Ko1991]
-/

public section

namespace Cslib.Kolmogorov

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal
open Cslib.Complexity DescriptionMethod

namespace MINKTStar

/-- A total string `y` is **consistent** with a partial string `x` when they have the same length
and every specified bit of `x` equals the bit of `y` at the same position
[Hirahara2022, footnote 5]. -/
@[expose]
def Consistent (x : List (Option Bool)) (y : List Bool) : Prop :=
  List.Forall₂ (fun o b => ∀ c ∈ o, c = b) x y

instance (x : List (Option Bool)) (y : List Bool) : Decidable (Consistent x y) :=
  inferInstanceAs (Decidable (List.Forall₂ _ x y))

/-- Consistency is equal length together with agreement at every specified position. -/
theorem consistent_iff {x : List (Option Bool)} {y : List Bool} :
    Consistent x y ↔ x.length = y.length ∧ ∀ i (hx : i < x.length) (hy : i < y.length) b,
      x[i] = some b → b = y[i] := by
  simp only [Consistent, List.forall₂_iff_get, List.get_eq_getElem, Option.mem_def]

/-- A consistent string has the length of the partial string. -/
theorem Consistent.length_eq {x : List (Option Bool)} {y : List Bool} (h : Consistent x y) :
    x.length = y.length :=
  List.Forall₂.length_eq h

/-- The only string consistent with a fully specified string is that string. -/
@[simp]
theorem consistent_map_some_iff {x y : List Bool} : Consistent (x.map some) y ↔ x = y := by
  simp only [Consistent, List.forall₂_map_left_iff, Option.mem_def, Option.some.injEq,
    forall_eq', List.forall₂_eq_eq_eq]

/-- An instance of `MINKT*`: a partial string `pattern ∈ {0, 1, *}*` (`none` is `*`), a step bound
`time` and a program size threshold `size` [Hirahara2022, Section I, p. 971]. -/
structure Instance where
  /-- The partial string `x`. -/
  pattern : List (Option Bool)
  /-- The step bound `t` for the described multi-tape machine. -/
  time : ℕ
  /-- The maximum allowed program length `s`. -/
  size : ℕ
  deriving DecidableEq

end MINKTStar

/-- **The partial-string Minimum Time-Bounded Kolmogorov Complexity Problem (`MINKT*`)**
[Hirahara2022, Section I, p. 971]: the instances `(x, t, s)` such that some string `y` consistent
with `x` has `timeBoundedAt t y ≤ s`. -/
@[expose]
def MINKTStar : Set MINKTStar.Instance :=
  {i | ∃ y, MINKTStar.Consistent i.pattern y ∧ timeBoundedAt i.time y ≤ i.size}

namespace MINKTStar

/-- Encoding of `MINKTStar.Instance`: the framed list of entries of the partial string
(`encList (encOption encBool)`), followed by `1^time` and `1^size` in unary. -/
enc_structure enc : Instance where
  pattern : (encList (encOption encBool)), time : encUnary, size : encUnary

/-- The unary size threshold is at most the encoded instance length. -/
theorem size_le_length_enc (i : Instance) : i.size ≤ (enc i).length := by
  simp only [enc_apply, length_encPair, encUnary_apply, List.length_replicate]
  omega

/-- The unary time bound is at most the encoded instance length. -/
theorem time_le_length_enc (i : Instance) : i.time ≤ (enc i).length := by
  simp only [enc_apply, length_encPair, encUnary_apply, List.length_replicate]
  omega

/-- The length of the partial string is at most the encoded instance length. -/
theorem length_pattern_le_length_enc (i : Instance) : i.pattern.length ≤ (enc i).length := by
  have h := SizedListEncoding.length_le (encA := encOption encBool)
    (encL := encList (encOption encBool)) i.pattern
  simp only [enc_apply, length_encPair]
  omega

/-- An instance belongs to `MINKT*` iff some consistent string has `K^t` at most the threshold. -/
theorem mem_iff {i : Instance} :
    i ∈ MINKTStar ↔ ∃ y, Consistent i.pattern y ∧ timeBoundedAt i.time y ≤ i.size :=
  Iff.rfl

/-- `⟨x, t, s⟩ ∈ MINKT*` iff some string consistent with `x` has `timeBoundedAt t y ≤ s`. -/
@[simp]
theorem mk_mem_iff {x : List (Option Bool)} {t s : ℕ} :
    (⟨x, t, s⟩ : Instance) ∈ MINKTStar ↔ ∃ y, Consistent x y ∧ timeBoundedAt t y ≤ s :=
  Iff.rfl

/-- An instance belongs to `MINKT*` iff some program of length at most `i.size` outputs, within
`i.time` steps, a string consistent with `i.pattern`. -/
theorem mem_iff_exists_program {i : Instance} :
    i ∈ MINKTStar ↔ ∃ y p : List Bool, Consistent i.pattern y ∧ p.length ≤ i.size ∧
      y ∈ (universalTM.run p).runFor i.time := by
  simp only [mem_iff, timeBoundedAt_le_natCast_iff]
  constructor
  · rintro ⟨y, hy, p, hp, hrun⟩
    exact ⟨y, p, hy, hp, hrun⟩
  · rintro ⟨y, p, hy, hp, hrun⟩
    exact ⟨y, hy, p, hp, hrun⟩

/-- Monotonicity of `MINKT*` in the size threshold. -/
theorem mem_of_size_le {x : List (Option Bool)} {t s₁ s₂ : ℕ}
    (h : (⟨x, t, s₁⟩ : Instance) ∈ MINKTStar) (hs : s₁ ≤ s₂) :
    (⟨x, t, s₂⟩ : Instance) ∈ MINKTStar :=
  let ⟨y, hy, hK⟩ := h
  ⟨y, hy, hK.trans (Nat.cast_le.mpr hs)⟩

/-- Monotonicity of `MINKT*` in the time budget. -/
theorem mem_of_time_le {x : List (Option Bool)} {t₁ t₂ s : ℕ}
    (h : (⟨x, t₁, s⟩ : Instance) ∈ MINKTStar) (ht : t₁ ≤ t₂) :
    (⟨x, t₂, s⟩ : Instance) ∈ MINKTStar :=
  let ⟨y, hy, hK⟩ := h
  ⟨y, hy, (timeBoundedAt_anti ht).trans hK⟩

/-! ### Witness check and `NP` membership -/

/-- Boolean consistency test: equal lengths and agreement at the specified positions. -/
def consistentCheck (x : List (Option Bool)) (y : List Bool) : Bool :=
  decide (x.length = y.length) && (x.zip y).all fun p => p.1.getD p.2 == p.2

/-- `consistentCheck` decides `Consistent`. -/
theorem consistentCheck_eq_true_iff {x : List (Option Bool)} {y : List Bool} :
    consistentCheck x y = true ↔ Consistent x y := by
  rw [Consistent, List.forall₂_iff_zip]
  simp only [consistentCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Option.getD_beq_self_eq_true_iff, Prod.forall, Option.mem_def]
  exact and_congr_right fun _ => forall₃_congr fun _ _ _ => forall₂_congr fun _ _ => eq_comm

/-- The consistency test is computable in polynomial time. -/
theorem computableInPolyTime_consistentCheck :
    ComputableInPolyTime (fun p : List (Option Bool) × List Bool => consistentCheck p.1 p.2)
      (encPair (encList (encOption encBool)) encBits) encBool := by
  open ComputableInPolyTime in
  have hx := fst (encList (encOption encBool)) encBits
  have hy := snd (encList (encOption encBool)) encBits
  have hyl : ComputableInPolyTime (fun p : List (Option Bool) × List Bool => p.2)
      (encPair (encList (encOption encBool)) encBits) (encList encBool) :=
    (bits_encList_polyTime encBool).1.comp hy
  have hzip := (zip (encOption encBool) encBool).comp (hx.prod hyl)
  have hall : ComputableInPolyTime
      (fun p : List (Option Bool) × List Bool =>
        (p.1.zip p.2).all fun q => q.1.getD q.2 == q.2)
      (encPair (encList (encOption encBool)) encBits) encBool :=
    .of_tidy (ComputableTidilyInPolyTime.allWithInput hzip.tidy
      ((ComputableTidilyInPolyTime.of_finite (fun q : Option Bool × Bool => q.1.getD q.2 == q.2)
        (encA := encPair (encOption encBool) encBool) (encB := encBool)).comp
        (ComputableTidilyInPolyTime.snd _ _)))
  have hlen := unary_eq' ((length_list (encOption encBool)).comp hx) (length_bits.comp hy)
  exact bool_and.comp (hlen.prod hall)

/-- The witness check for `MINKT*`: given an instance `i` and a pair `(y, p)` of a candidate
string and program, checks that `y` is consistent with `i.pattern` and that `p` witnesses
`⟨y, i.time, i.size⟩ ∈ MINKT` (`MINKT.check`). -/
def check : Instance × (List Bool × List Bool) → Bool
  | (i, (y, p)) => consistentCheck i.pattern y && MINKT.check (⟨y, i.time, i.size⟩, p)

/-- `check (i, (y, p)) = true` iff `y` is consistent with `i.pattern`, `p.length ≤ i.size` and `p`
outputs `y` within `i.time` steps. -/
theorem check_eq_true_iff {i : Instance} {y p : List Bool} :
    check (i, (y, p)) = true ↔
      Consistent i.pattern y ∧ p.length ≤ i.size ∧ y ∈ (universalTM.run p).runFor i.time := by
  simp only [check, Bool.and_eq_true, consistentCheck_eq_true_iff, MINKT.check_eq_true_iff]

/-- The witness check for `MINKT*` is computable in polynomial time. -/
theorem computableInPolyTime_check :
    ComputableInPolyTime check (encPair enc (encPair encBits encBits)) encBool := by
  open ComputableInPolyTime in
  have hi := fst enc (encPair encBits encBits)
  have hw := snd enc (encPair encBits encBits)
  have hy := (fst encBits encBits).comp hw
  have hp := (snd encBits encBits).comp hw
  have hcons := computableInPolyTime_consistentCheck.comp ((enc_pattern_polyTime hi).prod hy)
  have hinst := MINKT.Instance.computableInPolyTime_mk.comp
    (hy.prod ((enc_time_polyTime hi).prod (enc_size_polyTime hi)))
  have hmink := MINKT.computableInPolyTime_check.comp (hinst.prod hp)
  exact bool_and.comp (hcons.prod hmink)

/-- **`MINKT*` is in `NP`**: a witness for `(x, 1^t, 1^s)` is a string `y` consistent with `x`
(so `|y| = |x|`) together with a program of length at most `s`, verified in polynomial time by
`check`. -/
theorem mem_NP : MINKTStar ∈ NP enc := by
  have h := mem_NP_of_witness (enc := enc) (p := 3 * Polynomial.X + 1)
    (R := fun i (w : List Bool × List Bool) => Consistent i.pattern w.1 ∧ w.2.length ≤ i.size ∧
      w.1 ∈ (universalTM.run w.2).runFor i.time)
    (Decoder.pair Decoder.bits Decoder.bits) computableInPolyTime_check
    (fun i w => check_eq_true_iff)
    fun i w hw => ⟨w, hw, by
      have hy := hw.1.length_eq
      have hpat := length_pattern_le_length_enc i
      have hsize := size_le_length_enc i
      have hp := hw.2.1
      simp only [length_encPair, encBits_apply, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
      omega⟩
  convert h using 1
  ext i
  simp only [mem_iff_exists_program, Set.mem_ofPred_eq, Prod.exists]

/-! ### Reduction from `MINKT` -/

/-- The `MINKT*` instance of a `MINKT` instance: the fully specified partial string. -/
@[expose]
def ofTotal (i : MINKT.Instance) : Instance :=
  ⟨i.string.map some, i.time, i.size⟩

/-- `ofTotal i ∈ MINKT*` iff `i ∈ MINKT`. -/
@[simp]
theorem ofTotal_mem_iff {i : MINKT.Instance} : ofTotal i ∈ MINKTStar ↔ i ∈ MINKT := by
  simp [ofTotal, MINKT.mem_iff]

/-- `ofTotal` is computable in polynomial time. -/
theorem computableInPolyTime_ofTotal : ComputableInPolyTime ofTotal MINKT.enc enc := by
  open ComputableInPolyTime in
  have hstr := MINKT.Instance.computableInPolyTime_string
  have hlist := (bits_encList_polyTime encBool).1.comp hstr
  have hmap : ComputableInPolyTime (fun i : MINKT.Instance => i.string.map some) MINKT.enc
      (encList (encOption encBool)) :=
    .of_tidy ((ComputableTidilyInPolyTime.map
      (ComputableTidilyInPolyTime.optionSome encBool)).comp hlist.tidy)
  exact enc_mk_polyTime hmap MINKT.Instance.computableInPolyTime_time
    MINKT.Instance.computableInPolyTime_size

/-- `MINKT` reduces to `MINKT*` in polynomial time via `ofTotal`. -/
theorem polyTimeReducible_MINKT_MINKTStar :
    PolyTimeReducible MINKT.enc enc MINKT MINKTStar :=
  ⟨ofTotal, computableInPolyTime_ofTotal, fun _ => ofTotal_mem_iff.symm⟩

end MINKTStar

end Cslib.Kolmogorov
