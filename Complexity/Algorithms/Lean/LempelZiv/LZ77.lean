/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Find
public import Mathlib.Logic.Function.Iterate

import Mathlib.Data.List.Infix

/-!
# Lempel–Ziv sliding-window parsing (LZ77) and the exhaustive history (LZ76)

A phrase `u` is *reproducible* from the text `h` already written, within window `W`, if it can be
written by copying symbols one at a time from `d` positions back, for some `1 ≤ d ≤ W` with
`d ≤ |h|`. The copy may run into `u` itself: `aaaa` is reproducible from `a` with `d = 1`. A
*history* of `x` is a factorization `x = u₁ ⋯ u_c` into nonempty phrases each of which is
reproducible from `u₁ ⋯ u_{i-1}` except possibly for its last symbol ([LempelZiv1976], where the
window is unbounded; [ZivLempel1977] with a finite window).

The greedy (*exhaustive*) parse takes as each phrase the longest reproducible prefix of the rest
of the input followed by one more symbol (or the whole rest, if it is reproducible). For example,
with an unbounded window, `ABBABBABBBAABABAA` parses as `A, B, BA, BBABBB, AA, BABA, A`, and
`aaaaaaaa` as `a, aaaaaaa` (an overlapping copy). Each phrase is encoded as a triple
`(d, ℓ, a)`: copy `ℓ` symbols from distance `d`, then write `a`.

Scope: the window bounds only how far back a copy may start. As in [LempelZiv1976], a copy may be
arbitrarily long; the lookahead buffer of [ZivLempel1977], which also bounds the phrase length, and
its fixed-width codewords are not modelled. The functions are list-based reference
implementations, and no running time is claimed.

## Main definitions

* `Cslib.Algorithms.Lean.LempelZiv.LZ77.Reproducible`: `u` is a copy from the text `h`, within the
  window `W`, possibly overlapping itself.
* `Cslib.Algorithms.Lean.LempelZiv.LZ77.IsHistory`: a sequence of nonempty phrases, each
  reproducible except for its last symbol.
* `Cslib.Algorithms.Lean.LempelZiv.LZ77.IsExhaustive`: no phrase but the last is reproducible.
* `Cslib.Algorithms.Lean.LempelZiv.LZ77.parse`: the greedy parse.
* `Cslib.Algorithms.Lean.LempelZiv.LZ77.encode`, `Cslib.Algorithms.Lean.LempelZiv.LZ77.decode`:
  the (distance, length, symbol) code. The decoder copies symbol by symbol and does not depend on
  the window.
* `Cslib.Algorithms.Lean.LempelZiv.LZ77.complexity`: the Lempel–Ziv complexity, the number of
  phrases of the greedy parse with an unbounded window.

## Main results

* `Cslib.Algorithms.Lean.LempelZiv.LZ77.flatten_parse`,
  `Cslib.Algorithms.Lean.LempelZiv.LZ77.isHistory_parse`,
  `Cslib.Algorithms.Lean.LempelZiv.LZ77.isExhaustive_parse`: the greedy parse is an exhaustive
  history of its input.
* `Cslib.Algorithms.Lean.LempelZiv.LZ77.decode_encode`: the code is lossless.
* `Cslib.Algorithms.Lean.LempelZiv.LZ77.length_parse_le_of_isHistory`: the greedy parse has the
  fewest phrases among all histories with the same window ([LempelZiv1976]).
* `Cslib.Algorithms.Lean.LempelZiv.LZ77.parse_eq_of_isExhaustive`: the exhaustive history is
  unique.

## References

* [A. Lempel and J. Ziv, *On the complexity of finite sequences*][LempelZiv1976]
* [J. Ziv and A. Lempel, *A universal algorithm for sequential data compression*][ZivLempel1977]
-/

public section

namespace Cslib.Algorithms.Lean.LempelZiv.LZ77

variable {α : Type*}

/-! ## The decoder -/

/-- Append the symbol `d` positions before the end (nothing if there is none). -/
@[expose] def copyStep (d : ℕ) (h : List α) : List α :=
  match h[h.length - d]? with
  | some a => h ++ [a]
  | none => h

/-- Decode one triple: copy `ℓ` symbols from distance `d`, then write `a`. -/
@[expose] def decodeStep (h : List α) (t : ℕ × ℕ × α) : List α :=
  (copyStep t.1)^[t.2.1] h ++ [t.2.2]

/-- Decode a sequence of (distance, length, symbol) triples. -/
@[expose] def decode (ts : List (ℕ × ℕ × α)) : List α := ts.foldl decodeStep []

/-- Copying `|v|` symbols from distance `d` writes `v`, if `v` is a copy from that distance. -/
theorem iterate_copyStep {d : ℕ} (hd : 0 < d) :
    ∀ (h v : List α), d ≤ h.length → v <+: (h ++ v).drop (h.length - d) →
      (copyStep d)^[v.length] h = h ++ v
  | h, [], _, _ => by simp
  | h, a :: v, hdh, hv => by
    have hlt : h.length - d < h.length := by omega
    have hdrop : (h ++ a :: v).drop (h.length - d) = h.drop (h.length - d) ++ a :: v :=
      List.drop_append_of_le_length (by omega)
    rw [hdrop, List.drop_eq_getElem_cons hlt, List.cons_append, List.cons_prefix_cons] at hv
    have hstep : copyStep d h = h ++ [a] := by
      rw [copyStep, List.getElem?_eq_getElem hlt, ← hv.1]
    have hlen : (h ++ [a]).length - d = h.length - d + 1 := by
      rw [List.length_append, List.length_singleton]; omega
    have hv' : v <+: (h ++ [a] ++ v).drop ((h ++ [a]).length - d) := by
      rw [hlen, List.append_assoc, List.singleton_append,
        List.drop_append_of_le_length (by omega)]
      exact hv.2
    have hdh' : d ≤ (h ++ [a]).length := by
      rw [List.length_append, List.length_singleton]; omega
    rw [List.length_cons, Function.iterate_succ_apply, hstep,
      iterate_copyStep hd (h ++ [a]) v hdh' hv', List.append_assoc, List.singleton_append]

/-! ## Reproduction and histories -/

/-- `u` is *reproducible* from the text `h` within window `W`: it is empty, or it is a copy that
starts `d` symbols back, for some `1 ≤ d ≤ W` with `d ≤ |h|`; the copy may run into `u` itself.
This is reproduction `h → h u` of [LempelZiv1976] with the copy's start restricted to the last
`W` positions of `h`. -/
def Reproducible (W : ℕ) (h u : List α) : Prop :=
  u = [] ∨ ∃ d, 0 < d ∧ d ≤ W ∧ d ≤ h.length ∧ u <+: (h ++ u).drop (h.length - d)

instance [DecidableEq α] (W : ℕ) (h u : List α) : Decidable (Reproducible W h u) :=
  decidable_of_iff (u = [] ∨ ∃ d ∈ List.range' 1 (min W h.length),
      u <+: (h ++ u).drop (h.length - d)) (by
    unfold Reproducible
    refine or_congr Iff.rfl ⟨fun ⟨d, hd, hu⟩ => ?_, fun ⟨d, h0, hW, hh, hu⟩ => ?_⟩
    · rw [List.mem_range'_1] at hd
      exact ⟨d, by omega, by omega, by omega, hu⟩
    · exact ⟨d, List.mem_range'_1.2 (by omega), hu⟩)

/-- A *history* of the text `h ++ ws.flatten` from `h`, within window `W`: every phrase is
nonempty and reproducible from the text before it except for its last symbol (production
`⇒` in [LempelZiv1976]). -/
def IsHistory (W : ℕ) : List α → List (List α) → Prop
  | _, [] => True
  | h, u :: ws => u ≠ [] ∧ Reproducible W h u.dropLast ∧ IsHistory W (h ++ u) ws

@[simp] theorem isHistory_nil (W : ℕ) (h : List α) : IsHistory W h [] := trivial

@[simp] theorem isHistory_cons (W : ℕ) (h u : List α) (ws : List (List α)) :
    IsHistory W h (u :: ws) ↔
      u ≠ [] ∧ Reproducible W h u.dropLast ∧ IsHistory W (h ++ u) ws :=
  Iff.rfl

/-- A history is *exhaustive* if no phrase but the last is reproducible from the text before
it ([LempelZiv1976]). -/
def IsExhaustive (W : ℕ) : List α → List (List α) → Prop
  | _, [] => True
  | h, u :: ws => (ws ≠ [] → ¬ Reproducible W h u) ∧ IsExhaustive W (h ++ u) ws

@[simp] theorem isExhaustive_nil (W : ℕ) (h : List α) : IsExhaustive W h [] := trivial

@[simp] theorem isExhaustive_cons (W : ℕ) (h u : List α) (ws : List (List α)) :
    IsExhaustive W h (u :: ws) ↔
      (ws ≠ [] → ¬ Reproducible W h u) ∧ IsExhaustive W (h ++ u) ws :=
  Iff.rfl

/-- The empty phrase is reproducible. -/
theorem reproducible_nil (W : ℕ) (h : List α) : Reproducible W h [] := Or.inl rfl

/-- Reproducibility is closed under prefixes. -/
theorem Reproducible.of_prefix {W : ℕ} {h u v : List α} (hu : Reproducible W h u)
    (hvu : v <+: u) : Reproducible W h v := by
  rcases hu with rfl | ⟨d, h0, hW, hh, hu⟩
  · exact Or.inl (List.prefix_nil.1 hvu)
  · refine Or.inr ⟨d, h0, hW, hh, ?_⟩
    have hk : h.length - d ≤ h.length := Nat.sub_le _ _
    rw [List.drop_append_of_le_length hk] at hu ⊢
    exact List.prefix_of_prefix_length_le (hvu.trans hu)
      ((List.prefix_append_right_inj _).2 hvu) (by simp)

/-- Moving the first `k` symbols of a reproducible phrase into the text keeps the rest
reproducible. -/
theorem Reproducible.drop {W : ℕ} {h v : List α} (hv : Reproducible W h v) (k : ℕ) :
    Reproducible W (h ++ v.take k) (v.drop k) := by
  rcases hv with rfl | ⟨d, h0, hW, hh, hv⟩
  · exact Or.inl (by simp)
  · refine Or.inr ⟨d, h0, hW, by rw [List.length_append]; omega, ?_⟩
    have hlen : (h ++ v.take k).length - d = h.length - d + (v.take k).length := by
      simp only [List.length_append]; omega
    rw [List.append_assoc, List.take_append_drop, hlen, ← List.drop_drop]
    have hdk : v.drop (v.take k).length = v.drop k := by
      rw [List.length_take]
      rcases le_total k v.length with hk | hk
      · rw [Nat.min_eq_left hk]
      · rw [Nat.min_eq_right hk, List.drop_length, List.drop_eq_nil_of_le hk]
    rw [← hdk]
    exact hv.drop _

/-- Every infix of the text is reproducible when the window covers the whole text. -/
theorem reproducible_of_infix {W : ℕ} {h u : List α} (hhW : h.length ≤ W) (hu : u <:+: h) :
    Reproducible W h u := by
  rcases eq_or_ne u [] with rfl | hne
  · exact reproducible_nil W h
  · obtain ⟨s, t, rfl⟩ := hu
    have hpos : 0 < u.length := List.length_pos_iff.2 hne
    simp only [List.length_append] at hhW
    refine Or.inr ⟨u.length + t.length, by omega, by omega,
      by simp only [List.length_append]; omega, ?_⟩
    have hk : (s ++ u ++ t).length - (u.length + t.length) = s.length := by simp
    rw [hk, List.append_assoc, List.append_assoc, List.drop_left]
    exact List.prefix_append _ _

/-! ## The greedy parse -/

section DecidableEq

variable [DecidableEq α]

/-- The length of the longest reproducible prefix of `r`. -/
@[expose] def copyLen (W : ℕ) (h r : List α) : ℕ :=
  Nat.findGreatest (fun ℓ => Reproducible W h (r.take ℓ)) r.length

/-- The greedy parse of `r` after the text `h`: the next phrase is the longest reproducible
prefix of `r` followed by one more symbol (all of `r` if `r` is reproducible). -/
@[expose] def parseAux (W : ℕ) : ℕ → List α → List α → List (List α)
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | n + 1, h, a :: r =>
    (a :: r).take (copyLen W h (a :: r) + 1) ::
      parseAux W n (h ++ (a :: r).take (copyLen W h (a :: r) + 1))
        ((a :: r).drop (copyLen W h (a :: r) + 1))

/-- The greedy (exhaustive) parse of `x` with window `W`. -/
@[expose] def parse (W : ℕ) (x : List α) : List (List α) := parseAux W x.length [] x

/-- The Lempel–Ziv complexity of `x` ([LempelZiv1976]): the number of phrases of its exhaustive
history with an unbounded window. Copies never start before the beginning of the text, so the
window `|x|` is unbounded for `x`. -/
@[expose] def complexity (x : List α) : ℕ := (parse x.length x).length

/-- The longest reproducible prefix of `r` is no longer than `r`. -/
theorem copyLen_le_length (W : ℕ) (h r : List α) : copyLen W h r ≤ r.length :=
  Nat.findGreatest_le _

/-- The prefix of length `copyLen` is reproducible. -/
theorem reproducible_take_copyLen (W : ℕ) (h r : List α) :
    Reproducible W h (r.take (copyLen W h r)) :=
  Nat.findGreatest_spec (P := fun ℓ => Reproducible W h (r.take ℓ)) (Nat.zero_le _)
    (reproducible_nil W h)

/-- Every reproducible prefix of `r` is at most `copyLen` long. -/
theorem le_copyLen {W : ℕ} {h r u : List α} (hu : Reproducible W h u) (hur : u <+: r) :
    u.length ≤ copyLen W h r := by
  have htake : r.take u.length = u := (List.prefix_iff_eq_take.1 hur).symm
  refine Nat.le_findGreatest hur.length_le ?_
  rw [htake]
  exact hu

private theorem parseAux_nil (W n : ℕ) (h : List α) : parseAux W n h [] = [] := by
  cases n <;> rfl

private theorem flatten_parseAux (W : ℕ) :
    ∀ (n : ℕ) (h r : List α), r.length ≤ n → (parseAux W n h r).flatten = r
  | 0, h, r, hr => by
    rw [List.eq_nil_of_length_eq_zero (by omega : r.length = 0)]; rfl
  | n + 1, h, [], _ => rfl
  | n + 1, h, a :: r, hr => by
    rw [parseAux, List.flatten_cons, flatten_parseAux W n _ _
      (by simp only [List.length_drop, List.length_cons] at hr ⊢; omega),
      List.take_append_drop]

/-- The phrases of the greedy parse concatenate to the input. -/
@[simp] theorem flatten_parse (W : ℕ) (x : List α) : (parse W x).flatten = x :=
  flatten_parseAux W _ _ _ le_rfl

private theorem isHistory_parseAux (W : ℕ) :
    ∀ (n : ℕ) (h r : List α), IsHistory W h (parseAux W n h r)
  | 0, h, r => trivial
  | n + 1, h, [] => trivial
  | n + 1, h, a :: r => by
    rw [parseAux, isHistory_cons]
    refine ⟨by simp, ?_, isHistory_parseAux W n _ _⟩
    refine (reproducible_take_copyLen W h (a :: r)).of_prefix ?_
    refine List.prefix_of_prefix_length_le ((List.dropLast_prefix _).trans
      (List.take_prefix _ _)) (List.take_prefix _ _) ?_
    simp only [List.length_dropLast, List.length_take]
    omega

/-- The greedy parse is a history of its input. -/
theorem isHistory_parse (W : ℕ) (x : List α) : IsHistory W [] (parse W x) :=
  isHistory_parseAux W _ _ _

private theorem isExhaustive_parseAux (W : ℕ) :
    ∀ (n : ℕ) (h r : List α), IsExhaustive W h (parseAux W n h r)
  | 0, h, r => trivial
  | n + 1, h, [] => trivial
  | n + 1, h, a :: r => by
    rw [parseAux, isExhaustive_cons]
    refine ⟨fun hne hrep => ?_, isExhaustive_parseAux W n _ _⟩
    have hlt : copyLen W h (a :: r) + 1 < (a :: r).length := by
      by_contra hge
      apply hne
      rw [List.drop_eq_nil_of_le (by omega), parseAux_nil]
    have := le_copyLen hrep (List.take_prefix _ _)
    rw [List.length_take] at this
    omega

/-- The greedy parse is exhaustive: no phrase but the last is reproducible. -/
theorem isExhaustive_parse (W : ℕ) (x : List α) : IsExhaustive W [] (parse W x) :=
  isExhaustive_parseAux W _ _ _

/-! ## Optimality -/

/-- One step of the exchange argument: a phrase `u` of a history that starts no later than the
greedy phrase (after `h`) also ends no later. -/
theorem length_add_length_le {W : ℕ} {h h' r u s : List α} (heq : h ++ r = h' ++ (u ++ s))
    (hh : h'.length ≤ h.length) (hrep : Reproducible W h' u.dropLast) :
    h'.length + u.length ≤ h.length + min (copyLen W h r + 1) r.length := by
  have hlen := congrArg List.length heq
  simp only [List.length_append] at hlen
  rcases Nat.lt_or_ge h.length (h'.length + u.length) with hlt | hle
  swap
  · omega
  obtain ⟨k, hk⟩ : ∃ k, k = h.length - h'.length := ⟨_, rfl⟩
  have hku : k < u.length := by omega
  have hsplit : h = h' ++ u.take k ∧ r = u.drop k ++ s := by
    have h1 : h' ++ (u ++ s) = (h' ++ u.take k) ++ (u.drop k ++ s) := by
      rw [List.append_assoc, ← List.append_assoc (u.take k), List.take_append_drop]
    rw [h1] at heq
    exact List.append_inj heq (by simp only [List.length_append, List.length_take]; omega)
  obtain ⟨rfl, rfl⟩ := hsplit
  have htk : u.dropLast.take k = u.take k := by
    rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left (by omega)]
  have hrep' := hrep.drop k
  rw [htk] at hrep'
  have hpre : u.dropLast.drop k <+: u.drop k ++ s :=
    ((List.dropLast_prefix u).drop k).trans (List.prefix_append _ _)
  have := le_copyLen hrep' hpre
  simp only [List.length_drop, List.length_dropLast, List.length_append,
    List.length_take] at this ⊢
  omega

private theorem length_parseAux_le (W : ℕ) :
    ∀ (ws : List (List α)) (n : ℕ) (h h' r : List α), r.length ≤ n →
      h ++ r = h' ++ ws.flatten → h'.length ≤ h.length → IsHistory W h' ws →
      (parseAux W n h r).length ≤ ws.length
  | [], n, h, h', r, _, heq, hh, _ => by
    have hlen := congrArg List.length heq
    simp only [List.flatten_nil, List.append_nil, List.length_append] at hlen
    rw [List.eq_nil_of_length_eq_zero (by omega : r.length = 0), parseAux_nil]
  | u :: ws, 0, h, h', r, _, _, _, _ => by simp [parseAux]
  | u :: ws, n + 1, h, h', [], _, _, _, _ => by simp [parseAux]
  | u :: ws, n + 1, h, h', a :: r, hr, heq, hh, hhist => by
    rw [isHistory_cons] at hhist
    obtain ⟨_, hrep, hws⟩ := hhist
    rw [List.flatten_cons] at heq
    have hstep := length_add_length_le heq hh hrep
    rw [parseAux, List.length_cons, List.length_cons]
    refine Nat.succ_le_succ (length_parseAux_le W ws n _ (h' ++ u) _
      (by simp only [List.length_drop, List.length_cons] at hr ⊢; omega) ?_ ?_ hws)
    · rw [List.append_assoc, List.take_append_drop, heq, List.append_assoc]
    · simp only [List.length_append, List.length_take] at hstep ⊢
      omega

/-- **Optimality of the exhaustive history** ([LempelZiv1976]): the greedy parse of `x` has no
more phrases than any history of `x` with the same window. -/
theorem length_parse_le_of_isHistory {W : ℕ} {x : List α} {ws : List (List α)}
    (hx : ws.flatten = x) (hws : IsHistory W [] ws) : (parse W x).length ≤ ws.length :=
  length_parseAux_le W ws _ [] [] x le_rfl (by simp [hx]) le_rfl hws

/-- The Lempel–Ziv complexity is the least number of phrases of a history. -/
theorem complexity_le_of_isHistory {x : List α} {ws : List (List α)} (hx : ws.flatten = x)
    (hws : IsHistory x.length [] ws) : complexity x ≤ ws.length :=
  length_parse_le_of_isHistory hx hws

private theorem parseAux_eq_of_isExhaustive (W : ℕ) :
    ∀ (ws : List (List α)) (n : ℕ) (h : List α), ws.flatten.length ≤ n →
      IsHistory W h ws → IsExhaustive W h ws → parseAux W n h ws.flatten = ws
  | [], n, h, _, _, _ => parseAux_nil W n h
  | u :: ws, n, h, hn, hhist, hex => by
    rw [isHistory_cons] at hhist
    rw [isExhaustive_cons] at hex
    obtain ⟨hne, hrep, hws⟩ := hhist
    obtain ⟨hnr, hex⟩ := hex
    obtain ⟨a, u', rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, by simp only [List.flatten_cons, List.length_append, List.length_cons] at hn; omega⟩
    rw [List.flatten_cons, List.cons_append, parseAux, ← List.cons_append]
    have hlow : (a :: u').length - 1 ≤ copyLen W h ((a :: u') ++ ws.flatten) := by
      have := le_copyLen (r := (a :: u') ++ ws.flatten) hrep
        ((List.dropLast_prefix _).trans (List.prefix_append _ _))
      rwa [List.length_dropLast] at this
    have htake : ((a :: u') ++ ws.flatten).take (copyLen W h ((a :: u') ++ ws.flatten) + 1) =
        a :: u' := by
      rcases eq_or_ne ws [] with rfl | hws0
      · rw [List.flatten_nil, List.append_nil]
        exact List.take_of_length_le
          (by simp only [List.flatten_nil, List.append_nil, List.length_cons] at hlow ⊢; omega)
      · have hup : copyLen W h ((a :: u') ++ ws.flatten) < (a :: u').length := by
          by_contra hge
          refine hnr hws0 ((reproducible_take_copyLen W h ((a :: u') ++ ws.flatten)).of_prefix ?_)
          exact List.prefix_of_prefix_length_le (List.prefix_append _ _) (List.take_prefix _ _)
            (by simp only [List.length_take, List.length_append, List.length_cons] at hge ⊢; omega)
        rw [show copyLen W h ((a :: u') ++ ws.flatten) + 1 = (a :: u').length by
          simp only [List.length_cons] at hlow hup ⊢; omega]
        exact List.take_left
    have hdrop : ((a :: u') ++ ws.flatten).drop (copyLen W h ((a :: u') ++ ws.flatten) + 1) =
        ws.flatten := by
      have := List.take_append_drop (copyLen W h ((a :: u') ++ ws.flatten) + 1)
        ((a :: u') ++ ws.flatten)
      rw [htake] at this
      exact List.append_cancel_left this
    rw [htake, hdrop, parseAux_eq_of_isExhaustive W ws n _
      (by simp only [List.flatten_cons, List.length_append, List.length_cons] at hn; omega) hws hex]

/-- **Uniqueness of the exhaustive history** ([LempelZiv1976]): an exhaustive history of `x` is
its greedy parse. -/
theorem parse_eq_of_isExhaustive {W : ℕ} {x : List α} {ws : List (List α)}
    (hx : ws.flatten = x) (hws : IsHistory W [] ws) (hex : IsExhaustive W [] ws) :
    parse W x = ws := by
  subst hx
  exact parseAux_eq_of_isExhaustive W ws _ [] le_rfl hws hex

/-! ## The (distance, length, symbol) code -/

/-- The smallest distance from which `u` is a copy, within window `W`; `0` if `u` is empty or
there is no such distance. -/
@[expose] def bestDist (W : ℕ) (h u : List α) : ℕ :=
  if u = [] then 0 else
    ((List.range' 1 (min W h.length)).find?
      (fun d => decide (u <+: (h ++ u).drop (h.length - d)))).getD 0

/-- If `u` is a copy from some distance within the window, then `bestDist` is such a distance
(or `u` is empty). -/
theorem bestDist_spec {W : ℕ} {h u : List α} {d : ℕ} (h0 : 0 < d) (hW : d ≤ W)
    (hh : d ≤ h.length) (hu : u <+: (h ++ u).drop (h.length - d)) :
    u = [] ∨ 0 < bestDist W h u ∧ bestDist W h u ≤ h.length ∧
      u <+: (h ++ u).drop (h.length - bestDist W h u) := by
  rcases eq_or_ne u [] with rfl | hne
  · exact Or.inl rfl
  refine Or.inr ?_
  unfold bestDist
  rw [ite_eq_right hne]
  cases hf : (List.range' 1 (min W h.length)).find?
      (fun d => decide (u <+: (h ++ u).drop (h.length - d))) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (decide_eq_true hu) (hf d (List.mem_range'_1.2 (by omega)))
  | some e =>
    have hmem := List.mem_range'_1.1 (List.mem_of_find?_eq_some hf)
    have hp := List.find?_some hf
    rw [decide_eq_true_eq] at hp
    exact ⟨by simp only [Option.getD_some]; omega, by simp only [Option.getD_some]; omega,
      by simpa only [Option.getD_some] using hp⟩

/-- Encode each nonempty phrase `u` after the text `h` as (distance, `|u| - 1`, last symbol of
`u`). Empty phrases are skipped. -/
@[expose] def encodeAux (W : ℕ) : List α → List (List α) → List (ℕ × ℕ × α)
  | _, [] => []
  | h, u :: ws =>
    match u.getLast? with
    | some a => (bestDist W h u.dropLast, u.length - 1, a) :: encodeAux W (h ++ u) ws
    | none => encodeAux W (h ++ u) ws

/-- The LZ77 code of `x` with window `W`. -/
@[expose] def encode (W : ℕ) (x : List α) : List (ℕ × ℕ × α) := encodeAux W [] (parse W x)

private theorem decodeStep_phrase {W : ℕ} {h u : List α} (hne : u ≠ [])
    (hrep : Reproducible W h u.dropLast) :
    decodeStep h (bestDist W h u.dropLast, u.length - 1, u.getLast hne) = h ++ u := by
  have hlen : u.length - 1 = u.dropLast.length := List.length_dropLast.symm
  have hcopy : (copyStep (bestDist W h u.dropLast))^[u.dropLast.length] h = h ++ u.dropLast := by
    rcases hrep with h0 | ⟨d, h0, hW, hh, hu⟩
    · rw [h0, List.length_nil, Function.iterate_zero_apply, List.append_nil]
    · rcases bestDist_spec h0 hW hh hu with h0 | ⟨hpos, hle, hpre⟩
      · rw [h0, List.length_nil, Function.iterate_zero_apply, List.append_nil]
      · exact iterate_copyStep hpos h _ hle hpre
  rw [decodeStep, hlen, hcopy, List.append_assoc, List.dropLast_append_getLast]

private theorem foldl_decodeStep_encodeAux {W : ℕ} :
    ∀ (h : List α) (ws : List (List α)), IsHistory W h ws →
      (encodeAux W h ws).foldl decodeStep h = h ++ ws.flatten
  | h, [], _ => by simp [encodeAux]
  | h, u :: ws, hhist => by
    rw [isHistory_cons] at hhist
    obtain ⟨hne, hrep, hws⟩ := hhist
    rw [encodeAux, List.getLast?_eq_some_getLast hne, List.foldl_cons, decodeStep_phrase hne hrep,
      foldl_decodeStep_encodeAux (h ++ u) ws hws, List.flatten_cons, List.append_assoc]

/-- Decoding a history's code gives the text back. -/
theorem decode_encodeAux {W : ℕ} {ws : List (List α)} (hws : IsHistory W [] ws) :
    decode (encodeAux W [] ws) = ws.flatten := by
  rw [decode, foldl_decodeStep_encodeAux [] ws hws, List.nil_append]

/-- **The LZ77 code is lossless.** The decoder does not need the window. -/
theorem decode_encode (W : ℕ) (x : List α) : decode (encode W x) = x := by
  rw [encode, decode_encodeAux (isHistory_parse W x), flatten_parse]

private theorem length_encodeAux {W : ℕ} :
    ∀ (h : List α) (ws : List (List α)), (∀ u ∈ ws, u ≠ []) →
      (encodeAux W h ws).length = ws.length
  | h, [], _ => rfl
  | h, u :: ws, hne => by
    rw [encodeAux, List.getLast?_eq_some_getLast (hne u List.mem_cons_self), List.length_cons,
      length_encodeAux (h ++ u) ws (fun v hv => hne v (List.mem_cons_of_mem _ hv)),
      List.length_cons]

/-- The phrases of the greedy parse are nonempty. -/
theorem ne_nil_of_mem_parse {W : ℕ} {x u : List α} (hu : u ∈ parse W x) : u ≠ [] := by
  have key : ∀ (n : ℕ) (h r : List α), ∀ u ∈ parseAux W n h r, u ≠ [] := by
    intro n
    induction n with
    | zero => intro h r u hu; simp [parseAux] at hu
    | succ n ih =>
      intro h r u hu
      rcases r with _ | ⟨a, r⟩
      · simp [parseAux] at hu
      · rw [parseAux, List.mem_cons] at hu
        rcases hu with rfl | hu
        · simp
        · exact ih _ _ u hu
  exact key _ _ _ u hu

/-- The code has one triple per phrase. -/
theorem length_encode (W : ℕ) (x : List α) : (encode W x).length = (parse W x).length :=
  length_encodeAux [] _ (fun _ hu => ne_nil_of_mem_parse hu)

end DecidableEq

end Cslib.Algorithms.Lean.LempelZiv.LZ77
