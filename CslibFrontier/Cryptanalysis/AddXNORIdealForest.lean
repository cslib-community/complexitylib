/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORIdealChain
import Mathlib.Data.Finset.Card
import CslibFrontier.Probability.PMF.Uniform

/-!
# Rooted paths in collision-free fresh-query ledgers

The forest-counting argument of [WangLvShenZhang2027], Lemma 12 (PDF p. 27), must
be derived from fresh answers rather than supplied as an invariant. A ledger here stores only
cache misses. `NoCollision` is the local fresh-answer condition: the answer differs from all
previously seen words, public roots, and the current query argument.

`paths` computes one rooted label string per reachable word. Forward fresh answers extend that
string; an inverse fresh answer creates an unreachable predecessor. The transport invariant is
proved from the ledger. Consequently distinct nonempty queried label strings have distinct
endpoints, and their number is at most the number of fresh entries.

`AddXNORIdealLedger` derives these ledgers from the actual oracle sampler, and
`AddXNORIdealCollisions` bounds their collision/covering analysis event. That old-ledger
event alone does not bound a hidden-cut hit. `AddXNORIdealReveal` and `AddXNORIdealCutBounds`
add a charged hidden-path reveal while retaining the old covering ledger.
`AddXNORIdealSecurity` supplies the resulting decision and weaker-constant search bounds.

## Main definitions

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Forest.Record`: a fresh indexed query and its answer.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Forest.NoCollision`: the local fresh-answer condition.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Forest.paths`, `born`: computed rooted witnesses and keys.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Forest.Follows`: a path using actual recorded entries.

## Main results

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Forest.follows_witness`: paths get their exact
  label string.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Forest.covered_card_le_selected`: covering
  charged only to forward births in the final-label class.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Forest.covered_card_le`: the derived forest
  covering count.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Forest.follows_of_suffix_of_seen`: collision-free
  reveals recover paths already present at old seen words.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Forest.uniform_two_sided_covered_le`: both
  directional hidden-word covering fractions from the same fresh ledger.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain.Forest

open RandomPermutation
open scoped ENNReal

/-- One cache-miss query. Its answer is the newly sampled endpoint, in either direction. -/
structure Record (Index Word : Type) where
  /-- Independent permutation label. -/
  label : Index
  /-- Actual directed request. -/
  query : PermQuery Word
  /-- Actual fresh answer. -/
  answer : Word

namespace Record

/-- The oriented permutation entry, reusing the bidirectional oracle's cache convention. -/
abbrev entry {Index Word : Type} (r : Record Index Word) : Word × Word :=
  PermQuery.toCacheEntry ⟨r.query, r.answer⟩
/-- The entry's domain point. -/
abbrev source {Index Word : Type} (r : Record Index Word) : Word := r.entry.1
/-- The entry's image point. -/
abbrev target {Index Word : Type} (r : Record Index Word) : Word := r.entry.2
/-- The point supplied by the caller, before receiving the fresh answer. -/
@[expose] def known {Index Word : Type} (r : Record Index Word) : Word :=
  r.query.argument

/-- Reverse the interpretation of each recorded permutation, preserving query/answer timing. -/
@[expose] def reverse {Index Word : Type} (r : Record Index Word) : Record Index Word :=
  ⟨r.label, match r.query with
    | .forward point => .inverse point
    | .inverse point => .forward point, r.answer⟩

/-- Reversing a request swaps the oriented cache entry. -/
theorem reverse_entry {Index Word : Type} (r : Record Index Word) :
    r.reverse.entry = r.entry.swap := by
  cases r with | mk label query answer => cases query <;> rfl

end Record

variable {Index Word : Type} [DecidableEq Word]

/-- All public roots and endpoints of earlier fresh entries. The newest entry comes first. -/
@[expose] def seen (initial : Finset Word) : List (Record Index Word) → Finset Word
  | [] => initial
  | r :: rest => insert r.answer (insert r.known (seen initial rest))

/-- No fresh answer equals an old seen value or the argument just queried. Cache hits are
excluded from this ledger; their repeated answers must not be classified as fresh collisions. -/
@[expose] def NoCollision (initial : Finset Word) : List (Record Index Word) → Prop
  | [] => True
  | r :: rest => NoCollision initial rest ∧ r.answer ∉ insert r.known (seen initial rest)

/-- Reversing all permutation directions preserves the complete seen-word set. -/
theorem seen_reverse (initial : Finset Word) (records : List (Record Index Word)) :
    seen initial (records.map Record.reverse) = seen initial records := by
  induction records with
  | nil => rfl
  | cons r rest ih =>
    cases r with | mk label query answer => cases query <;>
      simp [seen, Record.reverse, Record.known, PermQuery.argument, ih]

/-- The fresh-collision condition is unchanged by reversing every permutation direction. -/
theorem noCollision_reverse (initial : Finset Word) (records : List (Record Index Word)) :
    NoCollision initial (records.map Record.reverse) ↔ NoCollision initial records := by
  induction records with
  | nil => rfl
  | cons r rest ih =>
    cases r with | mk label query answer => cases query <;>
      simp [NoCollision, Record.reverse, Record.known, PermQuery.argument, seen_reverse, ih]

/-- Compute the unique rooted path string at each discovered word. Inverse fresh entries
have a new predecessor and cannot add a path from the already seen root. -/
@[expose] def paths (seed : Word) : List (Record Index Word) → Word → Option (List Index)
  | [] => fun point => if point = seed then some [] else none
  | r :: rest => match r.query with
    | .forward point => Function.update (paths seed rest) r.answer
        ((paths seed rest point).map (· ++ [r.label]))
    | .inverse _ => paths seed rest

/-- Candidate keys born at forward fresh answers. Some may remain unreachable; retaining
such keys only makes the counting upper bound larger. -/
@[expose] def born : List (Record Index Word) → Finset Word
  | [] => ∅
  | r :: rest => match r.query with
    | .forward _ => insert r.answer (born rest)
    | .inverse _ => born rest

/-- The seen set contains each endpoint of every recorded entry. -/
theorem endpoints_seen (initial : Finset Word) (records : List (Record Index Word))
    (r : Record Index Word) (hr : r ∈ records) :
    r.source ∈ seen initial records ∧ r.target ∈ seen initial records := by
  induction records with
  | nil => simp at hr
  | cons head rest ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · cases r with | mk label query answer => cases query <;>
        simp [seen, Record.known, Record.source, Record.target, Record.entry,
          PermQuery.toCacheEntry, PermQuery.argument]
    · obtain ⟨hs, ht⟩ := ih hr
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hs),
        Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ht)⟩

/-- All initial public words remain seen. -/
theorem initial_seen (initial : Finset Word) (records : List (Record Index Word)) :
    initial ⊆ seen initial records := by
  induction records with
  | nil => exact Finset.Subset.refl _
  | cons r rest ih =>
    exact fun _ hw => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ih hw))

/-- A fresh entry adds at most its query argument and its answer to the seen set. -/
theorem seen_card_le (initial : Finset Word) (records : List (Record Index Word)) :
    (seen initial records).card ≤ initial.card + 2 * records.length := by
  induction records with
  | nil => simp [seen]
  | cons r rest ih =>
    have h₁ := Finset.card_insert_le r.answer (insert r.known (seen initial rest))
    have h₂ := Finset.card_insert_le r.known (seen initial rest)
    simp only [seen, List.length_cons]
    omega

private structure Facts (initial : Finset Word) (seed : Word) (records : List (Record Index Word))
    where
  roots : ∀ point ∈ initial, paths seed records point = if point = seed then some [] else none
  support : ∀ point labels, paths seed records point = some labels → point ∈ seen initial records
  transport : ∀ r ∈ records, ∀ labels, paths seed records r.source = some labels →
    paths seed records r.target = some (labels ++ [r.label])
  keys : ∀ point labels, paths seed records point = some labels → labels ≠ [] → point ∈ born records

private theorem facts (initial : Finset Word) (seed : Word) (hs : seed ∈ initial)
    (records : List (Record Index Word)) (hc : NoCollision initial records) :
    Facts initial seed records := by
  induction records with
  | nil =>
    refine ⟨fun _ _ => rfl, ?_, ?_, ?_⟩
    · intro point labels hp
      simp only [paths] at hp
      split at hp
      · subst point; exact hs
      · contradiction
    · simp
    · intro point labels hp hn
      simp only [paths] at hp
      split at hp
      · cases hp; exact (hn rfl).elim
      · contradiction
  | cons head rest ih =>
    obtain ⟨hc, hfresh⟩ := hc
    have old := ih hc
    have hseen : head.answer ∉ seen initial rest := fun hm =>
      hfresh (Finset.mem_insert_of_mem hm)
    have hknown : head.known ≠ head.answer := fun he =>
      hfresh (he ▸ Finset.mem_insert_self _ _)
    have hroot : ∀ point ∈ initial, point ≠ head.answer := fun point hp he =>
      hseen (he ▸ initial_seen initial rest hp)
    have hold : ∀ r ∈ rest, r.source ≠ head.answer ∧ r.target ≠ head.answer := by
      intro r hr
      obtain ⟨hu, hv⟩ := endpoints_seen initial rest r hr
      exact ⟨fun he => hseen (he ▸ hu), fun he => hseen (he ▸ hv)⟩
    obtain ⟨label, query, answer⟩ := head
    cases query with
    | forward point =>
      change point ≠ answer at hknown
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro word hw
        simpa only [paths, Function.update_of_ne (hroot word hw)] using old.roots word hw
      · intro word labels hw
        by_cases he : word = answer
        · subst word; exact Finset.mem_insert_self _ _
        · have ho : paths seed rest word = some labels := by
            simpa only [paths, Function.update_of_ne he] using hw
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (old.support _ _ ho))
      · intro r hr labels hw
        rcases List.mem_cons.mp hr with rfl | hr
        · change Function.update (paths seed rest) answer
              ((paths seed rest point).map (· ++ [label])) point = some labels at hw
          rw [Function.update_of_ne hknown] at hw
          simp only [paths, Record.target, Record.entry, PermQuery.toCacheEntry_forward,
            Function.update_self, hw, Option.map_some]
        · obtain ⟨hu, hv⟩ := hold r hr
          have ho : paths seed rest r.source = some labels := by
            simpa only [paths, Function.update_of_ne hu] using hw
          simpa only [paths, Function.update_of_ne hv] using old.transport r hr labels ho
      · intro word labels hw hn
        by_cases he : word = answer
        · subst word; exact Finset.mem_insert_self _ _
        · have ho : paths seed rest word = some labels := by
            simpa only [paths, Function.update_of_ne he] using hw
          exact Finset.mem_insert_of_mem (old.keys _ _ ho hn)
    | inverse point =>
      refine ⟨old.roots, ?_, ?_, old.keys⟩
      · intro word labels hw
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (old.support _ _ hw))
      · intro r hr labels hw
        rcases List.mem_cons.mp hr with rfl | hr
        · exact (hseen (old.support _ _ hw)).elim
        · exact old.transport r hr labels hw

/-- At most one new candidate key is inserted per fresh entry. -/
theorem born_card_le (records : List (Record Index Word)) :
    (born records).card ≤ records.length := by
  induction records with
  | nil => simp [born]
  | cons r rest ih =>
    cases hq : r.query <;> simp only [born, hq, List.length_cons]
    · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ih 1)
    · omega

/-- A queried forward path consists only of actual oriented ledger entries. -/
inductive Follows (records : List (Record Index Word)) : Word → List Index → Word → Prop
  | nil (seed : Word) : Follows records seed [] seed
  | cons (r : Record Index Word) (hr : r ∈ records) {labels : List Index} {endpoint : Word}
      (tail : Follows records r.target labels endpoint) :
      Follows records r.source (r.label :: labels) endpoint

omit [DecidableEq Word] in
/-- Adding ledger entries preserves every existing path. -/
theorem Follows.mono {records more : List (Record Index Word)} (hm : records ⊆ more)
    {start endpoint : Word} {labels : List Index}
    (path : Follows records start labels endpoint) : Follows more start labels endpoint := by
  induction path with
  | nil => exact .nil _
  | cons r hr tail ih => exact .cons r (hm hr) ih

omit [DecidableEq Word] in
/-- Concatenating paths concatenates their exact label strings. -/
theorem Follows.append {records : List (Record Index Word)} {start middle endpoint : Word}
    {left right : List Index} (hl : Follows records start left middle)
    (hr : Follows records middle right endpoint) :
    Follows records start (left ++ right) endpoint := by
  induction hl with
  | nil => exact hr
  | cons r hm tail ih => exact .cons r hm (ih hr)

/-- Every stored computed witness is an actual path, not merely a semantic label assignment. -/
theorem paths_sound (seed : Word) (records : List (Record Index Word))
    {endpoint : Word} {labels : List Index} (hp : paths seed records endpoint = some labels) :
    Follows records seed labels endpoint := by
  induction records generalizing endpoint labels with
  | nil =>
    simp only [paths] at hp
    split at hp
    · rename_i heq
      subst endpoint
      cases Option.some.inj hp
      exact .nil _
    · contradiction
  | cons r rest ih =>
    cases hq : r.query with
    | inverse point =>
      simp only [paths, hq] at hp
      exact (ih hp).mono (fun _ h => List.mem_cons_of_mem _ h)
    | forward point =>
      simp only [paths, hq] at hp
      by_cases he : endpoint = r.answer
      · subst endpoint
        rw [Function.update_self, Option.map_eq_some_iff] at hp
        obtain ⟨stem, hstem, rfl⟩ := hp
        have heq : r.source = point ∧ r.target = r.answer := by
          cases r with
          | mk label query answer =>
            cases query <;> simp_all [Record.source, Record.target, Record.entry,
              PermQuery.toCacheEntry]
        have hedge : Follows (r :: rest) point [r.label] r.answer := by
          simpa only [heq.1, heq.2] using
            (Follows.cons r (List.mem_cons_self ..) (Follows.nil r.target))
        exact ((ih hstem).mono (fun _ h => List.mem_cons_of_mem _ h)).append hedge
      · rw [Function.update_of_ne he] at hp
        exact (ih hp).mono (fun _ h => List.mem_cons_of_mem _ h)

/-- Every followed path transports the computed witness string by exactly its labels. -/
private theorem transport_follows (initial : Finset Word) (seed : Word) (hs : seed ∈ initial)
    (records : List (Record Index Word)) (hc : NoCollision initial records)
    {start endpoint : Word} {labels stem : List Index}
    (path : Follows records start labels endpoint) (hp : paths seed records start = some stem) :
    paths seed records endpoint = some (stem ++ labels) := by
  have h := facts initial seed hs records hc
  induction path generalizing stem with
  | nil => simpa only [List.append_nil] using hp
  | cons r hr tail ih =>
    have hn := h.transport r hr stem hp
    simpa only [List.append_assoc, List.singleton_append] using ih hn

/-- Rooted paths have their exact full label string in the constructed witness table. -/
theorem follows_witness (initial : Finset Word) (seed : Word) (hs : seed ∈ initial)
    (records : List (Record Index Word)) (hc : NoCollision initial records)
    {endpoint : Word} {labels : List Index} (path : Follows records seed labels endpoint) :
    paths seed records endpoint = some labels := by
  have root := (facts initial seed hs records hc).roots seed hs
  simp only at root
  simpa only [List.nil_append] using transport_follows initial seed hs records hc path root

/-- A nonempty queried path cannot end at any initially protected public word, including
returning to the seed itself. No assumption that the public roots are distinct is needed. -/
theorem no_nonempty_initial_path (initial : Finset Word) (seed : Word) (hs : seed ∈ initial)
    (records : List (Record Index Word)) (hc : NoCollision initial records)
    {endpoint : Word} (he : endpoint ∈ initial) {labels : List Index} (hn : labels ≠ []) :
    ¬Follows records seed labels endpoint := by
  intro hp
  have hw := follows_witness initial seed hs records hc hp
  have hr := (facts initial seed hs records hc).roots endpoint he
  rw [hr] at hw
  split at hw
  · exact hn (Option.some.inj hw).symm
  · contradiction

/-- Appending older entries preserves their seen words. -/
theorem seen_append (initial : Finset Word) (newer older : List (Record Index Word)) :
    seen initial older ⊆ seen initial (newer ++ older) := by
  induction newer with
  | nil => exact Finset.Subset.refl _
  | cons r rest ih =>
    exact fun _ hw => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ih hw))

/-- Collision freedom of the full ledger implies collision freedom of an earlier suffix. -/
theorem noCollision_append_right (initial : Finset Word)
    (newer older : List (Record Index Word)) (hc : NoCollision initial (newer ++ older)) :
    NoCollision initial older := by
  induction newer with
  | nil => exact hc
  | cons r rest ih => exact ih hc.1

/-- A collision-free continuation cannot change the rooted witness at an already seen word.
This includes a previously unreachable word, whose witness remains `none`. -/
theorem paths_append_of_seen (initial : Finset Word) (seed : Word)
    (newer older : List (Record Index Word)) (hc : NoCollision initial (newer ++ older))
    (point : Word) (hp : point ∈ seen initial older) :
    paths seed (newer ++ older) point = paths seed older point := by
  induction newer with
  | nil => rfl
  | cons r rest ih =>
    have hn : point ≠ r.answer := fun he =>
      hc.2 (Finset.mem_insert_of_mem (he ▸ seen_append initial rest older hp))
    cases hq : r.query <;>
      simpa only [List.cons_append, paths, hq, Function.update_of_ne hn] using ih hc.1

/-- Revealing a path ending at an old seen word cannot discover a new rooted path without a
fresh collision. The old path is reconstructed from the preserved computed witness. -/
theorem follows_of_append_of_seen (initial : Finset Word) (seed : Word) (hs : seed ∈ initial)
    (newer older : List (Record Index Word)) (hc : NoCollision initial (newer ++ older))
    {point : Word} (hp : point ∈ seen initial older) {labels : List Index}
    (hpath : Follows (newer ++ older) seed labels point) : Follows older seed labels point := by
  have hw := follows_witness initial seed hs (newer ++ older) hc hpath
  rw [paths_append_of_seen initial seed newer older hc point hp] at hw
  exact paths_sound seed older hw

/-- The path-recovery rule for an earlier suffix of a collision-free ledger. -/
theorem follows_of_suffix_of_seen (initial : Finset Word) (seed : Word) (hs : seed ∈ initial)
    (older newer : List (Record Index Word)) (hsub : older <:+ newer)
    (hc : NoCollision initial newer) {point : Word} (hp : point ∈ seen initial older)
    {labels : List Index} (hpath : Follows newer seed labels point) :
    Follows older seed labels point := by
  obtain ⟨more, he⟩ := hsub
  apply follows_of_append_of_seen initial seed hs more older (by simpa only [he] using hc) hp
  simpa only [he] using hpath

open scoped Classical in
/-- The finite set of label words whose complete paths have been queried. -/
@[expose] noncomputable def covered {Words : Type} [Fintype Words]
    (records : List (Record Index Word)) (seed : Word)
    (labels : Words → List Index) : Finset Words :=
  Finset.univ.filter fun word => ∃ endpoint, Follows records seed (labels word) endpoint

/-- Distinct queried label words inject into any finite set containing their endpoints.
The required endpoint membership is normally discharged from the computed rooted witnesses. -/
theorem covered_card_le_of_endpoint_mem {Words : Type} [Fintype Words]
    (initial : Finset Word) (seed : Word) (hs : seed ∈ initial)
    (records : List (Record Index Word)) (hc : NoCollision initial records)
    (labels : Words → List Index) (hinj : Function.Injective labels) (keys : Finset Word)
    (hkeys : ∀ word endpoint, Follows records seed (labels word) endpoint → endpoint ∈ keys) :
    (covered records seed labels).card ≤ keys.card := by
  classical
  let ends (word : Words) : Word :=
    if hw : word ∈ covered records seed labels then
      Classical.choose (Finset.mem_filter.mp hw).2 else seed
  have follows (word : Words) (hw : word ∈ covered records seed labels) :
      Follows records seed (labels word) (ends word) := by
    simpa only [ends, dite_eq_left hw] using Classical.choose_spec (Finset.mem_filter.mp hw).2
  apply Finset.card_le_card_of_injOn ends
  · intro word hw
    exact hkeys word _ (follows word hw)
  · intro left hl right hr heq
    apply hinj
    have hw₁ := follows_witness initial seed hs records hc (follows left hl)
    have hw₂ := follows_witness initial seed hs records hc (follows right hr)
    rw [heq] at hw₁
    exact Option.some.inj (hw₁.symm.trans hw₂)

/-- The covering count is derived from the fresh ledger and computed witnesses. Each nonempty
queried label word injects into a key born at a forward fresh answer, of which there are at most
as many as fresh entries. No forest-uniqueness or cardinality conclusion is a premise. -/
theorem covered_card_le {Words : Type} [Fintype Words]
    (initial : Finset Word) (seed : Word) (hs : seed ∈ initial)
    (records : List (Record Index Word)) (hc : NoCollision initial records)
    (labels : Words → List Index) (hinj : Function.Injective labels)
    (hne : ∀ word, labels word ≠ []) : (covered records seed labels).card ≤ records.length := by
  have hb := covered_card_le_of_endpoint_mem initial seed hs records hc labels hinj
    (born records) (fun word endpoint hf =>
      (facts initial seed hs records hc).keys _ _
        (follows_witness initial seed hs records hc hf) (hne word))
  exact hb.trans (born_card_le records)

/-- Every nonempty computed path ends at a forward fresh entry bearing its last label.
This is a property of the actual computed witness, even before collision freedom is used. -/
theorem paths_last_birth (seed : Word) (records : List (Forest.Record Index Word))
    (endpoint : Word) (labels : List Index) (hne : labels ≠ [])
    (hw : Forest.paths seed records endpoint = some labels) :
    ∃ r ∈ records, (∃ input, r.query = .forward input) ∧ r.answer = endpoint ∧
      ∃ stem, labels = stem ++ [r.label] := by
  induction records with
  | nil =>
    simp only [Forest.paths] at hw
    split at hw
    · exact (hne (Option.some.inj hw).symm).elim
    · contradiction
  | cons r rest ih =>
    cases hq : r.query with
    | inverse point =>
      obtain ⟨r', hr, hrest⟩ := ih (by simpa only [Forest.paths, hq] using hw)
      exact ⟨r', List.mem_cons_of_mem _ hr, hrest⟩
    | forward point =>
      by_cases he : endpoint = r.answer
      · subst endpoint
        simp only [Forest.paths, hq, Function.update_self, Option.map_eq_some_iff] at hw
        obtain ⟨stem, _, heq⟩ := hw
        exact ⟨r, List.mem_cons_self, ⟨point, hq⟩, rfl, stem, heq.symm⟩
      · obtain ⟨r', hr, hrest⟩ := ih
          (by simpa only [Forest.paths, hq, Function.update_of_ne he] using hw)
        exact ⟨r', List.mem_cons_of_mem _ hr, hrest⟩

/-- Entries that can birth a rooted path ending in a selected label class. Inverse entries
are excluded, since their answer is a predecessor rather than a newly reached endpoint. -/
@[expose] def selected (P : Index → Bool) (r : Forest.Record Index Word) : Bool :=
  P r.label && match r.query with | .forward _ => true | .inverse _ => false

/-- Covered words inject into actual forward births of the appropriate last-label class. -/
theorem covered_card_le_selected {Words : Type} [Fintype Words]
    (initial : Finset Word) (seed : Word) (hs : seed ∈ initial)
    (records : List (Forest.Record Index Word)) (hc : Forest.NoCollision initial records)
    (labels : Words → List Index) (hinj : Function.Injective labels)
    (hne : ∀ word, labels word ≠ []) (P : Index → Bool)
    (hlast : ∀ word stem label, labels word = stem ++ [label] → P label = true) :
    (Forest.covered records seed labels).card ≤ (records.filter (selected P)).length := by
  classical
  let keys := ((records.filter (selected P)).map Forest.Record.answer).toFinset
  have hkeys := Forest.covered_card_le_of_endpoint_mem initial seed hs records hc labels hinj
    keys (fun word endpoint hf => by
      obtain ⟨r, hr, ⟨input, hq⟩, he, stem, hp⟩ := paths_last_birth seed records endpoint
        (labels word) (hne word) (Forest.follows_witness initial seed hs records hc hf)
      have hP := hlast word stem r.label hp
      simp only [keys, List.mem_toFinset, List.mem_map, List.mem_filter]
      exact ⟨r, ⟨hr, by simp [selected, hq, hP]⟩, he⟩)
  exact hkeys.trans ((List.toFinset_card_le _).trans (by simp))

/-- The layer-labelled representation of a binary operator prefix. The layer map may also
list a reversed suffix for backward covering; injectivity of this encoding uses the bit field. -/
@[expose] def binaryLabels {q h : ℕ} (layer : Fin h → Fin q) (bits : Operators h) :
    List (Label q) := List.ofFn fun i => (layer i, bits i)

/-- Distinct binary words have distinct layer-labelled strings. -/
theorem binaryLabels_injective {q h : ℕ} (layer : Fin h → Fin q) :
    Function.Injective (binaryLabels layer) := by
  intro left right heq
  have hbits := congrArg (List.map Prod.snd) heq
  simp only [binaryLabels, List.map_ofFn, Function.comp_def] at hbits
  exact List.ofFn_injective hbits

/-- Conditional on any collision-free visible fresh ledger, an independent hidden binary
prefix is covered with probability at most the actual entry count divided by `2^h`. -/
theorem uniform_binary_covered_le {q h : ℕ} (hh : 0 < h) (layer : Fin h → Fin q)
    (initial : Finset Word) (seed : Word) (hs : seed ∈ initial)
    (records : List (Record (Label q) Word)) (hc : NoCollision initial records) :
    (Probability.PMF.uniformOfFintype (Operators h)).toOuterMeasure
        {word | ∃ endpoint, Follows records seed (binaryLabels layer word) endpoint} ≤
      (records.length : ℝ≥0∞) / 2 ^ h := by
  classical
  rw [Probability.PMF.toOuterMeasure_uniformOfFintype]
  have hb := covered_card_le initial seed hs records hc (binaryLabels layer)
    (binaryLabels_injective layer) (fun word => by
      intro heq
      have he := congrArg List.length heq
      simp only [binaryLabels, List.length_ofFn, List.length_nil] at he
      omega)
  have hcard : Fintype.card (Operators h) = 2 ^ h := by simp [Operators]
  simp only [hcard, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hb) zero_le

/-- Both sides of an independent hidden word are covered with probability at most the sum
of the two forest fractions. Reversed entries are the same actual fresh draws, not a second
independent transcript. -/
theorem uniform_two_sided_covered_le {q h d : ℕ} (hh : 0 < h) (hd : 0 < d)
    (left : Fin h → Fin q) (right : Fin d → Fin q)
    (initial : Finset Word) (seed target : Word) (hs : seed ∈ initial) (ht : target ∈ initial)
    (records : List (Record (Label q) Word)) (hc : NoCollision initial records) :
    (Probability.PMF.uniformOfFintype (Operators h × Operators d)).toOuterMeasure
      {words | (∃ endpoint, Follows records seed (binaryLabels left words.1) endpoint) ∨
        ∃ endpoint, Follows (records.map Record.reverse) target
          (binaryLabels right words.2) endpoint} ≤
      (records.length : ℝ≥0∞) / 2 ^ h + records.length / 2 ^ d := by
  let dist := Probability.PMF.uniformOfFintype (Operators h × Operators d)
  let forward : Set (Operators h) :=
    {word | ∃ endpoint, Follows records seed (binaryLabels left word) endpoint}
  let backward : Set (Operators d) :=
    {word | ∃ endpoint, Follows (records.map Record.reverse) target
      (binaryLabels right word) endpoint}
  have hf : dist.toOuterMeasure (Prod.fst ⁻¹' forward) ≤
      (records.length : ℝ≥0∞) / 2 ^ h := by
    rw [← PMF.toOuterMeasure_map_apply]
    change ((Probability.PMF.uniformOfFintype (Operators h × Operators d)).map
      Prod.fst).toOuterMeasure forward ≤ _
    rw [Probability.PMF.uniformOfFintype_prod_map_fst]
    exact uniform_binary_covered_le hh left initial seed hs records hc
  have hm : dist.map Prod.snd = Probability.PMF.uniformOfFintype (Operators d) := by
    have he := Probability.PMF.uniformOfFintype_map_equiv
      (Equiv.prodComm (Operators h) (Operators d))
    have hp := congrArg (PMF.map Prod.fst) he
    simpa only [dist, PMF.map_comp, Function.comp_def, Equiv.prodComm_apply,
      Prod.fst_swap, Probability.PMF.uniformOfFintype_prod_map_fst] using hp
  have hb : dist.toOuterMeasure (Prod.snd ⁻¹' backward) ≤
      (records.length : ℝ≥0∞) / 2 ^ d := by
    rw [← PMF.toOuterMeasure_map_apply, hm]
    simpa only [List.length_map] using uniform_binary_covered_le hd right initial target ht
      (records.map Record.reverse) ((noCollision_reverse initial records).mpr hc)
  exact (MeasureTheory.measure_union_le (Prod.fst ⁻¹' forward)
    (Prod.snd ⁻¹' backward)).trans
    (add_le_add hf hb)

end Cslib.Cryptanalysis.AddXNOR.IdealChain.Forest
