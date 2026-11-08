/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.LempelZiv.DistinctParsing

import Mathlib.Data.List.Infix

/-!
# Lempel–Ziv incremental parsing (LZ78)

The incremental parsing of [ZivLempel1978] cuts a word into phrases from left to right: each
phrase is the shortest prefix of the remaining input that is not an earlier phrase. When the
input runs out first, the last phrase is the whole (nonempty) remainder, which may repeat an
earlier phrase. For example ([CoverThomas2006], Ch. 13),
`ABBABBABBBAABABAA` parses as `A, B, BA, BB, AB, BBA, ABA, BAA`.

Every phrase is an earlier phrase (or `[]`) followed by one symbol, so the parse is encoded by
(pointer, symbol) pairs: the pair `(j, a)` stands for phrase `j` (with phrase `0` being `[]`)
followed by `a`. The example above becomes
`(0,A) (0,B) (2,A) (2,B) (1,B) (4,A) (5,A) (3,A)`.

This file defines the parse, the pair encoder and decoder, proves that the code is lossless, and
specializes the distinct-parsing bound to the parse. The bit-level code and its length bound are
in `Complexity.Algorithms.Lean.LempelZiv.LZ78Bits`. The functions are reference implementations
with quadratic dictionary lookups; no running time is claimed.

## Main definitions

* `Cslib.Algorithms.Lean.LempelZiv.LZ78.splitPhrase`: the next phrase and the remaining input.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.parse`: the LZ78 incremental parsing.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.IsTreeStructured`: every phrase is an earlier phrase or
  `[]` followed by one symbol.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.encode`, `Cslib.Algorithms.Lean.LempelZiv.LZ78.decode`:
  the (pointer, symbol) code.

## Main results

* `Cslib.Algorithms.Lean.LempelZiv.LZ78.flatten_parse`: the phrases concatenate to the input.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.ne_nil_of_mem_parse`: every phrase is nonempty.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.prefix_mem_take_parse`,
  `Cslib.Algorithms.Lean.LempelZiv.LZ78.getElem_parse_notMem_take`: each phrase is the shortest
  new prefix: its nonempty proper prefixes are earlier phrases, and it is itself new unless it is
  the last phrase.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.nodup_dropLast_parse`: the phrases before the last are
  pairwise distinct.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.nodup_parse_of_getLast_notMem`: all phrases are pairwise
  distinct when the last phrase is new.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.isTreeStructured_parse`: the parse is tree structured.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.decode_encode`: the pair code is lossless.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.mul_length_parse_le`,
  `Cslib.Algorithms.Lean.LempelZiv.LZ78.length_parse_mul_log_le`,
  `Cslib.Algorithms.Lean.LempelZiv.LZ78.length_parse_mul_logb_sub_le`,
  `Cslib.Algorithms.Lean.LempelZiv.LZ78.length_parse_le_div`: the number of phrases `c(n)` of an
  input of length `n` over an alphabet of size `k ≥ 2` satisfies `c log_k c ≤ n + 2c` and
  `c(n) ≤ n / ((1 - ε_n) log_k n)` with `ε_n → 0` ([CoverThomas2006], Lemma 13.5.3).

## References

* [ZivLempel1978] J. Ziv and A. Lempel, *Compression of individual sequences via variable-rate
  coding*, IEEE Trans. Inf. Theory 24(5), 1978.
* [CoverThomas2006] T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed.,
  2006, Ch. 13.
-/

public section

namespace Cslib.Algorithms.Lean.LempelZiv.LZ78

variable {α : Type*} [DecidableEq α]

/-! ## Parsing -/

/-- Extend the current phrase `acc` symbol by symbol while it is in the dictionary. Returns the
phrase and the remaining input. -/
@[expose] def splitPhraseAux (dict : List (List α)) : List α → List α → List α × List α
  | acc, [] => (acc, [])
  | acc, a :: x =>
    if acc ++ [a] ∈ dict then splitPhraseAux dict (acc ++ [a]) x else (acc ++ [a], x)

/-- The next LZ78 phrase of `x` against the dictionary `dict` of earlier phrases, and the
remaining input: the shortest prefix of `x` not in `dict`, or all of `x` if every nonempty prefix
of `x` is in `dict`. -/
@[expose] def splitPhrase (dict : List (List α)) (x : List α) : List α × List α :=
  splitPhraseAux dict [] x

private theorem splitPhraseAux_append (dict : List (List α)) (acc x : List α) :
    (splitPhraseAux dict acc x).1 ++ (splitPhraseAux dict acc x).2 = acc ++ x := by
  induction x generalizing acc with
  | nil => simp [splitPhraseAux]
  | cons a x ih =>
    simp only [splitPhraseAux]
    split_ifs
    · rw [ih]; simp
    · simp

/-- The phrase and the remaining input concatenate to the input. -/
theorem splitPhrase_append (dict : List (List α)) (x : List α) :
    (splitPhrase dict x).1 ++ (splitPhrase dict x).2 = x :=
  splitPhraseAux_append dict [] x

private theorem prefix_splitPhraseAux (dict : List (List α)) (acc x : List α) :
    acc <+: (splitPhraseAux dict acc x).1 := by
  induction x generalizing acc with
  | nil => simp [splitPhraseAux]
  | cons a x ih =>
    simp only [splitPhraseAux]
    split_ifs
    · exact (List.prefix_append acc [a]).trans (ih _)
    · exact List.prefix_append acc [a]

/-- On nonempty input, the phrase consumes at least one symbol. -/
theorem length_splitPhrase_snd_lt (dict : List (List α)) (a : α) (x : List α) :
    (splitPhrase dict (a :: x)).2.length < (a :: x).length := by
  have h := congrArg List.length (splitPhrase_append dict (a :: x))
  have hpre : [a] <+: (splitPhrase dict (a :: x)).1 := by
    simp only [splitPhrase, splitPhraseAux]
    split_ifs
    · exact prefix_splitPhraseAux _ _ _
    · exact List.prefix_refl _
  have h' := hpre.length_le
  simp only [List.length_append, List.length_cons] at h h' ⊢
  omega

private theorem splitPhraseAux_notMem (dict : List (List α)) (acc x : List α)
    (h : (splitPhraseAux dict acc x).2 ≠ []) : (splitPhraseAux dict acc x).1 ∉ dict := by
  induction x generalizing acc with
  | nil => simp [splitPhraseAux] at h
  | cons a x ih =>
    simp only [splitPhraseAux] at h ⊢
    split_ifs at h ⊢ with ha
    · exact ih _ h
    · exact ha

/-- If input remains after the phrase, the phrase is new. -/
theorem splitPhrase_notMem (dict : List (List α)) (x : List α)
    (h : (splitPhrase dict x).2 ≠ []) : (splitPhrase dict x).1 ∉ dict :=
  splitPhraseAux_notMem dict [] x h

private theorem splitPhraseAux_prefix (dict : List (List α)) (acc x : List α)
    (hacc : ∀ q, q <+: acc → q ≠ [] → q ∈ dict) :
    ∀ q, q <+: (splitPhraseAux dict acc x).1 → q ≠ [] →
      q ≠ (splitPhraseAux dict acc x).1 → q ∈ dict := by
  induction x generalizing acc with
  | nil => intro q hq hne _; exact hacc q (by simpa [splitPhraseAux] using hq) hne
  | cons a x ih =>
    simp only [splitPhraseAux]
    split_ifs with ha
    · refine ih _ fun q hq hne => ?_
      rcases List.prefix_concat_iff.1 hq with rfl | hq
      · exact ha
      · exact hacc q hq hne
    · intro q hq hne hne'
      rcases List.prefix_concat_iff.1 hq with h | hq
      · exact absurd h hne'
      · exact hacc q hq hne

/-- Every nonempty proper prefix of the phrase is in the dictionary, so the phrase is the
shortest prefix of the input that is not. -/
theorem splitPhrase_prefix (dict : List (List α)) (x : List α) :
    ∀ q, q <+: (splitPhrase dict x).1 → q ≠ [] → q ≠ (splitPhrase dict x).1 → q ∈ dict :=
  splitPhraseAux_prefix dict [] x fun _ hq hne => absurd (List.prefix_nil.1 hq) hne

/-- LZ78 parsing of `x` against the dictionary `dict` of earlier phrases, with `fuel` steps.
Each step consumes at least one symbol, so `fuel = x.length` suffices. -/
@[expose] def parseAux : ℕ → List (List α) → List α → List (List α)
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, dict, a :: x =>
    (splitPhrase dict (a :: x)).1 ::
      parseAux fuel (dict ++ [(splitPhrase dict (a :: x)).1]) (splitPhrase dict (a :: x)).2

/-- **LZ78 incremental parsing** ([ZivLempel1978]): cut `x` into phrases, each the shortest
prefix of the remaining input that is not an earlier phrase (the last phrase may repeat an
earlier one). -/
@[expose] def parse (x : List α) : List (List α) := parseAux x.length [] x

@[simp] theorem parse_nil : parse ([] : List α) = [] := rfl

private theorem flatten_parseAux (fuel : ℕ) (dict : List (List α)) (x : List α)
    (hx : x.length ≤ fuel) : (parseAux fuel dict x).flatten = x := by
  induction fuel generalizing dict x with
  | zero => simp_all [parseAux]
  | succ fuel ih =>
    rcases x with _ | ⟨a, x⟩
    · simp [parseAux]
    · have hlt := length_splitPhrase_snd_lt dict a x
      simp only [parseAux, List.flatten_cons]
      rw [ih _ _ (by simp only [List.length_cons] at hx hlt ⊢; omega), splitPhrase_append]

/-- The LZ78 phrases concatenate to the input. -/
@[simp] theorem flatten_parse (x : List α) : (parse x).flatten = x :=
  flatten_parseAux _ _ _ le_rfl

private theorem ne_nil_of_mem_parseAux (fuel : ℕ) (dict : List (List α)) (x : List α) :
    ∀ w ∈ parseAux fuel dict x, w ≠ [] := by
  induction fuel generalizing dict x with
  | zero => simp [parseAux]
  | succ fuel ih =>
    rcases x with _ | ⟨a, x⟩
    · simp [parseAux]
    · intro w hw
      simp only [parseAux, List.mem_cons] at hw
      rcases hw with rfl | hw
      · intro h
        have h1 := splitPhrase_append dict (a :: x)
        have h2 := length_splitPhrase_snd_lt dict a x
        rw [h, List.nil_append] at h1
        rw [h1] at h2
        exact lt_irrefl _ h2
      · exact ih _ _ w hw

/-- Every LZ78 phrase is nonempty. -/
theorem ne_nil_of_mem_parse {x : List α} : ∀ w ∈ parse x, w ≠ [] :=
  ne_nil_of_mem_parseAux _ _ _

/-- The number of phrases is at most the input length. -/
theorem length_parse_le (x : List α) : (parse x).length ≤ x.length := by
  conv_rhs => rw [← flatten_parse x]
  rw [List.length_flatten]
  have h : ∀ ws : List (List α), (∀ w ∈ ws, w ≠ []) → ws.length ≤ (ws.map List.length).sum := by
    intro ws hws
    induction ws with
    | nil => simp
    | cons w ws ih =>
      have := List.length_pos_iff.2 (hws w List.mem_cons_self)
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have := ih fun v hv => hws v (List.mem_cons_of_mem _ hv)
      omega
  exact h _ fun w hw => ne_nil_of_mem_parse w hw

private theorem parseAux_eq_nil_of_nil (fuel : ℕ) (dict : List (List α)) :
    parseAux fuel dict [] = [] := by
  rcases fuel with _ | _ <;> rfl

private theorem prefix_mem_parseAux (fuel : ℕ) (dict : List (List α)) (x : List α) (i : ℕ)
    (hi : i < (parseAux fuel dict x).length) (q : List α)
    (hq : q <+: (parseAux fuel dict x)[i]) (hne : q ≠ [])
    (hne' : q ≠ (parseAux fuel dict x)[i]) : q ∈ dict ++ (parseAux fuel dict x).take i := by
  induction fuel generalizing dict x i with
  | zero => simp [parseAux] at hi
  | succ fuel ih =>
    rcases x with _ | ⟨a, x⟩
    · simp [parseAux] at hi
    · rcases i with _ | i
      · simp only [parseAux, List.getElem_cons_zero] at hq hne' ⊢
        exact List.mem_append_left _ (splitPhrase_prefix dict _ q hq hne hne')
      · simp only [parseAux, List.getElem_cons_succ, List.take_succ_cons] at hq hne' hi ⊢
        have := ih _ _ i (by simpa using hi) hq hne'
        simpa [List.append_assoc] using this

/-- **Prefix closure.** Every nonempty proper prefix of an LZ78 phrase is an earlier phrase. -/
theorem prefix_mem_take_parse (x : List α) (i : ℕ) (hi : i < (parse x).length) (q : List α)
    (hq : q <+: (parse x)[i]) (hne : q ≠ []) (hne' : q ≠ (parse x)[i]) :
    q ∈ (parse x).take i := by
  have h := prefix_mem_parseAux x.length [] x i hi q hq hne hne'
  rwa [List.nil_append] at h

private theorem notMem_parseAux (fuel : ℕ) (dict : List (List α)) (x : List α) (i : ℕ)
    (hi : i + 1 < (parseAux fuel dict x).length) :
    (parseAux fuel dict x)[i] ∉ dict ++ (parseAux fuel dict x).take i := by
  induction fuel generalizing dict x i with
  | zero => simp [parseAux] at hi
  | succ fuel ih =>
    rcases x with _ | ⟨a, x⟩
    · simp [parseAux] at hi
    · rcases i with _ | i
      · simp only [parseAux, List.getElem_cons_zero, List.take_zero, List.append_nil]
        refine splitPhrase_notMem dict _ fun h0 => ?_
        simp only [parseAux, List.length_cons, h0, parseAux_eq_nil_of_nil, List.length_nil] at hi
        omega
      · simp only [parseAux, List.getElem_cons_succ, List.take_succ_cons] at hi ⊢
        have := ih _ _ i (by simpa using hi)
        simpa [List.append_assoc] using this

/-- **Novelty.** Every LZ78 phrase except the last is different from all earlier phrases. -/
theorem getElem_parse_notMem_take (x : List α) (i : ℕ) (hi : i + 1 < (parse x).length) :
    (parse x)[i] ∉ (parse x).take i := by
  have h := notMem_parseAux x.length [] x i hi
  rwa [List.nil_append] at h

private theorem nodup_parseAux (fuel : ℕ) (dict : List (List α)) (x : List α)
    (hd : dict.Nodup) : (dict ++ (parseAux fuel dict x).dropLast).Nodup := by
  induction fuel generalizing dict x with
  | zero => simpa [parseAux] using hd
  | succ fuel ih =>
    rcases x with _ | ⟨a, x⟩
    · simpa [parseAux] using hd
    · simp only [parseAux]
      set p := (splitPhrase dict (a :: x)).1
      set r := (splitPhrase dict (a :: x)).2
      rcases hr : parseAux fuel (dict ++ [p]) r with _ | ⟨w, R⟩
      · simpa using hd
      · rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)]
        have hpr : r ≠ [] := by
          intro h0
          rw [h0, parseAux_eq_nil_of_nil] at hr
          exact List.cons_ne_nil _ _ hr.symm
        have hp : p ∉ dict := splitPhrase_notMem dict _ hpr
        have hd' : (dict ++ [p]).Nodup := List.nodup_append.2 ⟨hd, List.nodup_singleton _,
          fun b hb c hc => by
            rintro rfl
            rw [List.mem_singleton] at hc
            exact hp (hc ▸ hb)⟩
        have := ih (dict ++ [p]) r hd'
        rw [hr] at this
        simpa using this

/-- The LZ78 phrases before the last are pairwise distinct. -/
theorem nodup_dropLast_parse (x : List α) : (parse x).dropLast.Nodup := by
  have h := nodup_parseAux x.length [] x List.nodup_nil
  rw [List.nil_append] at h
  exact h

/-- All LZ78 phrases are pairwise distinct when the last phrase is new. -/
theorem nodup_parse_of_getLast_notMem (x : List α)
    (h : ∀ w ∈ (parse x).getLast?, w ∉ (parse x).dropLast) : (parse x).Nodup := by
  have hd := nodup_dropLast_parse x
  rcases List.eq_nil_or_concat (parse x) with h0 | ⟨vs, w, hw⟩
  · rw [h0]
    exact List.nodup_nil
  · rw [hw, List.concat_eq_append, List.dropLast_concat] at hd
    rw [hw, List.concat_eq_append, List.dropLast_concat, List.getLast?_concat] at h
    rw [hw, List.concat_eq_append, List.nodup_append]
    refine ⟨hd, List.nodup_singleton _, fun a ha b hb hab => h w rfl ?_⟩
    rw [List.mem_singleton] at hb
    rw [hab, hb] at ha
    exact ha

/-- A phrase sequence is *tree structured* over the dictionary `dict` if every phrase is an
earlier phrase, a dictionary entry, or `[]`, followed by one symbol. LZ78 parses are tree
structured over `[]` ([CoverThomas2006], Ch. 13). -/
def IsTreeStructured : List (List α) → List (List α) → Prop
  | _, [] => True
  | dict, w :: ws => (∃ q ∈ [] :: dict, ∃ a, w = q ++ [a]) ∧ IsTreeStructured (dict ++ [w]) ws

omit [DecidableEq α] in
@[simp] theorem isTreeStructured_nil (dict : List (List α)) : IsTreeStructured dict [] :=
  trivial

omit [DecidableEq α] in
@[simp] theorem isTreeStructured_cons (dict : List (List α)) (w : List α) (ws : List (List α)) :
    IsTreeStructured dict (w :: ws) ↔
      (∃ q ∈ [] :: dict, ∃ a, w = q ++ [a]) ∧ IsTreeStructured (dict ++ [w]) ws :=
  Iff.rfl

private theorem isTreeStructured_parseAux (fuel : ℕ) (dict : List (List α)) (x : List α) :
    IsTreeStructured dict (parseAux fuel dict x) := by
  induction fuel generalizing dict x with
  | zero => simp [parseAux]
  | succ fuel ih =>
    rcases x with _ | ⟨a, x⟩
    · simp [parseAux]
    · simp only [parseAux, isTreeStructured_cons]
      refine ⟨?_, ih _ _⟩
      set p := (splitPhrase dict (a :: x)).1 with hp
      have hne : p ≠ [] := ne_nil_of_mem_parseAux (fuel + 1) dict (a :: x) p
        (by simp [parseAux, hp])
      refine ⟨p.dropLast, ?_, p.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
      by_cases h : p.dropLast = []
      · rw [h]; exact List.mem_cons_self
      · refine List.mem_cons_of_mem _ (splitPhrase_prefix dict (a :: x) _
          (List.dropLast_prefix p) h ?_)
        intro heq
        have h1 : p.dropLast.length = p.length := congrArg List.length heq
        have h2 : 0 < p.length := List.length_pos_iff.2 hne
        rw [List.length_dropLast] at h1
        omega

/-- The LZ78 parse is tree structured. -/
theorem isTreeStructured_parse (x : List α) : IsTreeStructured [] (parse x) :=
  isTreeStructured_parseAux _ _ _

/-! ## The (pointer, symbol) code -/

/-- Encode each nonempty phrase `w` as the index of `w.dropLast` in `[] :: dict` (the
dictionary grows by every encoded phrase) and the last symbol of `w`. Empty phrases are
skipped. -/
@[expose] def encodePhrases : List (List α) → List (List α) → List (ℕ × α)
  | _, [] => []
  | dict, w :: ws =>
    match w.getLast? with
    | none => encodePhrases dict ws
    | some a => (([] :: dict).idxOf w.dropLast, a) :: encodePhrases (dict ++ [w]) ws

/-- **LZ78 encoder** ([ZivLempel1978]): the (pointer, symbol) pairs of the LZ78 parse. Pointer
`0` is the empty phrase and pointer `j ≥ 1` the `j`-th phrase. -/
@[expose] def encode (x : List α) : List (ℕ × α) := encodePhrases [] (parse x)

/-- Decode (pointer, symbol) pairs against the dictionary `dict` of earlier phrases. An
out-of-range pointer is read as the empty phrase. -/
@[expose] def decodePairs : List (List α) → List (ℕ × α) → List (List α)
  | _, [] => []
  | dict, (j, a) :: ps =>
    (([] :: dict).getD j [] ++ [a]) :: decodePairs (dict ++ [([] :: dict).getD j [] ++ [a]]) ps

/-- **LZ78 decoder**: rebuild the phrases from the pairs and concatenate them. -/
@[expose] def decode (ps : List (ℕ × α)) : List α := (decodePairs [] ps).flatten

theorem decodePairs_encodePhrases (dict ws : List (List α)) (ht : IsTreeStructured dict ws) :
    decodePairs dict (encodePhrases dict ws) = ws := by
  induction ws generalizing dict with
  | nil => simp [encodePhrases, decodePairs]
  | cons w ws ih =>
    obtain ⟨⟨q, hq, a, rfl⟩, ht⟩ := (isTreeStructured_cons _ _ _).1 ht
    simp only [encodePhrases, List.getLast?_concat, List.dropLast_concat, decodePairs]
    have hidx : ([] :: dict).getD (([] :: dict).idxOf q) [] = q := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hq),
        Option.getD_some, List.getElem_idxOf]
    rw [hidx, ih _ ht]

/-- **The LZ78 code is lossless.** -/
@[simp] theorem decode_encode (x : List α) : decode (encode x) = x := by
  rw [decode, encode, decodePairs_encodePhrases _ _ (isTreeStructured_parse x), flatten_parse]

theorem length_encodePhrases (dict ws : List (List α)) (ht : IsTreeStructured dict ws) :
    (encodePhrases dict ws).length = ws.length := by
  induction ws generalizing dict with
  | nil => simp [encodePhrases]
  | cons w ws ih =>
    obtain ⟨⟨q, -, a, rfl⟩, ht⟩ := (isTreeStructured_cons _ _ _).1 ht
    simp only [encodePhrases, List.getLast?_concat, List.length_cons, ih _ ht]

/-- There is one pair per phrase. -/
@[simp] theorem length_encode (x : List α) : (encode x).length = (parse x).length :=
  length_encodePhrases _ _ (isTreeStructured_parse x)

/-! ## The number of phrases -/

variable [Fintype α]

/-- The distinct-parsing inequality for LZ78: `m * c ≤ n + 2 * k ^ m` for every `m`, where `c` is
the number of phrases, `n` the input length and `k ≥ 2` the alphabet size. -/
theorem mul_length_parse_le (hα : 2 ≤ Fintype.card α) (x : List α) (m : ℕ) :
    m * (parse x).length ≤ x.length + 2 * Fintype.card α ^ m := by
  have := mul_length_le_of_nodup_dropLast hα (fun w hw => ne_nil_of_mem_parse w hw)
    (nodup_dropLast_parse x) m
  rwa [flatten_parse] at this

/-- The number `c` of LZ78 phrases of an input of length `n` over an alphabet of size `k`
satisfies `c * ⌊log_k c⌋ ≤ n + 2 * c`. -/
theorem length_parse_mul_log_le (x : List α) :
    (parse x).length * Nat.log (Fintype.card α) (parse x).length ≤
      x.length + 2 * (parse x).length :=
  mul_log_le_of_forall_mul_le fun hk m => mul_length_parse_le hk x m

/-- The number `c` of LZ78 phrases of an input of length `n` over an alphabet of size `k ≥ 2`
satisfies `c * (log_k n - log_k log_k n - 4) ≤ n` ([CoverThomas2006], Lemma 13.5.3). -/
theorem length_parse_mul_logb_sub_le (hα : 2 ≤ Fintype.card α) (x : List α) :
    ((parse x).length : ℝ) * (Real.logb (Fintype.card α) x.length -
      Real.logb (Fintype.card α) (Real.logb (Fintype.card α) x.length) - 4) ≤ x.length :=
  mul_logb_sub_le_of_forall_mul_le hα fun m => mul_length_parse_le hα x m

/-- **The number of LZ78 phrases** ([CoverThomas2006], Lemma 13.5.3, for an alphabet of size
`k ≥ 2`): `c(n) ≤ n / ((1 - ε_n) log_k n)`, where `ε_n → 0` (`tendsto_epsilon`). -/
theorem length_parse_le_div (hα : 2 ≤ Fintype.card α) (x : List α) (hn : 2 ≤ x.length)
    (hε : epsilon (Fintype.card α) x.length < 1) :
    ((parse x).length : ℝ) ≤
      x.length / ((1 - epsilon (Fintype.card α) x.length) *
        Real.logb (Fintype.card α) x.length) :=
  le_div_of_forall_mul_le hα (fun m => mul_length_parse_le hα x m) hε hn

end Cslib.Algorithms.Lean.LempelZiv.LZ78
