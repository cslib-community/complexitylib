/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# The sponge construction

The sponge construction ([BertoniDaemenPeetersVanAssche2008]; [KatzLindell2020], Section 7.3.3
and Construction 7.6) builds a hash function from a single unkeyed permutation `P` of an
`ℓ`-bit state split into a rate part of `r` bits and a capacity part of `c` bits, `r + c = ℓ`.
Starting from the all-zero state, each `r`-bit message block is added (XORed) into the rate part
and the state is permuted (*absorbing*); afterwards the hash outputs part of the state, permutes,
and repeats (*squeezing*).

We write the state as a pair `(rate, capacity) : R × C`, with the rate part `R` an additive group
(for bits, `BitString r`, where `+` is exclusive or). This is the source's `ℓ`-bit state with
`y ⊕ (m ‖ 0^c)` read as `(y.1 + m, y.2)`. Each squeezing step outputs `out y` for an arbitrary
output map `out`; Construction 7.6 takes the first `v` bits of the state, and the results below
hold for every `out`.

Theorem 7.7 bounds the collision probability when `P` is a random permutation by splitting
collisions into three bad events on the attacker's permutation queries (Claim 7.8). We prove the
deterministic core of Claim 7.8 for permutation queries: if two distinct block sequences have
equal first output, then among the permutation inputs evaluated while hashing them either two
distinct inputs have images with equal output (event E1), some image has zero capacity part
(event E2), or two distinct inputs have images with equal capacity part (event E3). Inverse
queries and the probability bound of Claim 7.9 are not formalized here. Conversely, a collision
in the capacity part always extends to a full collision, which is why the capacity governs
security; we use this to solve [KatzLindell2020], Exercise 7.26.

## Main definitions

* `Cslib.Crypto.Sponge.absorb`, `Cslib.Crypto.Sponge.squeeze`,
  `Cslib.Crypto.Sponge.hashBlocks`: the absorbing and squeezing phases on block sequences.
* `Cslib.Crypto.Sponge.pad`, `Cslib.Crypto.Sponge.toBlocks`, `Cslib.Crypto.Sponge.hash`:
  padding `m ↦ m ‖ 1 ‖ 0^*`, parsing into `r`-bit blocks, and the hash of Construction 7.6.
* `Cslib.Crypto.Sponge.IsInput`: the permutation inputs evaluated while absorbing.
* `Cslib.Crypto.Sponge.ImageCollision`, `Cslib.Crypto.Sponge.ZeroCapacity`: the bad events of
  Claim 7.8 on a set of evaluated permutation inputs.

## Main results

* `Cslib.Crypto.Sponge.badEvent_of_hash_eq`: every collision between distinct messages triggers
  one of the events E1, E2, E3 among the evaluated permutation inputs (Claim 7.8, forward
  queries).
* `Cslib.Crypto.Sponge.hash_eq_of_capacity_eq`: a capacity collision between equal-length
  full-block messages extends to a hash collision.
* `Cslib.Crypto.Sponge.hash_prodCongr_collision`: a permutation that acts separately on the rate
  and capacity parts gives an explicit collision ([KatzLindell2020], Exercise 7.26).
* `Cslib.Crypto.Sponge.pad_injective`, `Cslib.Crypto.Sponge.toBlocks_pad_injective`: distinct
  messages have distinct padded block sequences.

## References

* [G. Bertoni, J. Daemen, M. Peeters, G. Van Assche, *On the Indifferentiability of the Sponge
  Construction*][BertoniDaemenPeetersVanAssche2008]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Section 7.3.3,
  Construction 7.6, Theorem 7.7, Claim 7.8 and Exercise 7.26.
-/

public section

namespace Cslib.Crypto.Sponge

/-! ### Absorbing and squeezing -/

section Blocks

variable {R C O : Type*} [AddGroup R] [Zero C]

/-- One absorbing step: add the block `m` to the rate part of the state `y`, then permute,
`y ↦ P (y.1 + m, y.2)`. -/
@[expose]
def absorbStep (P : Equiv.Perm (R × C)) (y : R × C) (m : R) : R × C :=
  P (y.1 + m, y.2)

/-- The absorbing phase: absorb the blocks `ms` in order, starting from the zero state. -/
@[expose]
def absorb (P : Equiv.Perm (R × C)) (ms : List R) : R × C :=
  ms.foldl (absorbStep P) 0

/-- The squeezing phase: output `out y`, replace `y` by `P y`, and repeat, `k` outputs in
total. -/
@[expose]
def squeeze (P : Equiv.Perm (R × C)) (out : R × C → O) : ℕ → R × C → List O
  | 0, _ => []
  | k + 1, y => out y :: squeeze P out k (P y)

/-- The sponge hash of a block sequence with `k` squeezing outputs. -/
@[expose]
def hashBlocks (P : Equiv.Perm (R × C)) (out : R × C → O) (k : ℕ) (ms : List R) : List O :=
  squeeze P out k (absorb P ms)

@[simp]
theorem absorb_nil (P : Equiv.Perm (R × C)) : absorb P [] = 0 := rfl

theorem absorb_append (P : Equiv.Perm (R × C)) (a b : List R) :
    absorb P (a ++ b) = b.foldl (absorbStep P) (absorb P a) := by
  simp [absorb, List.foldl_append]

@[simp]
theorem absorb_concat (P : Equiv.Perm (R × C)) (a : List R) (m : R) :
    absorb P (a ++ [m]) = P ((absorb P a).1 + m, (absorb P a).2) := by
  simp [absorb_append, absorbStep]

omit [AddGroup R] [Zero C] in
@[simp]
theorem length_squeeze (P : Equiv.Perm (R × C)) (out : R × C → O) (k : ℕ) (y : R × C) :
    (squeeze P out k y).length = k := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih => simp [squeeze, ih]

theorem hashBlocks_succ (P : Equiv.Perm (R × C)) (out : R × C → O) (k : ℕ) (ms : List R) :
    hashBlocks P out (k + 1) ms = out (absorb P ms) :: squeeze P out k (P (absorb P ms)) := rfl

/-- `x` is one of the permutation inputs `x_i = (y_{i-1}.1 + m_i, y_{i-1}.2)` evaluated while
absorbing `ms`. -/
@[expose]
def IsInput (P : Equiv.Perm (R × C)) (ms : List R) (x : R × C) : Prop :=
  ∃ a m b, ms = a ++ m :: b ∧ x = ((absorb P a).1 + m, (absorb P a).2)

theorem IsInput.append_right {P : Equiv.Perm (R × C)} {a : List R} {x : R × C}
    (h : IsInput P a x) (b : List R) : IsInput P (a ++ b) x := by
  obtain ⟨a₀, m, b₀, rfl, rfl⟩ := h
  exact ⟨a₀, m, b₀ ++ b, by simp, rfl⟩

theorem isInput_concat (P : Equiv.Perm (R × C)) (a : List R) (m : R) :
    IsInput P (a ++ [m]) ((absorb P a).1 + m, (absorb P a).2) :=
  ⟨a, m, [], rfl, rfl⟩

/-- Two distinct inputs in `Q` whose images under `P` agree under `f`. With `f = out` this is
event E1 of [KatzLindell2020], Claim 7.8; with `f = Prod.snd` (the capacity part) it is
event E3. -/
@[expose]
def ImageCollision {D : Type*} (P : Equiv.Perm (R × C)) (f : R × C → D)
    (Q : R × C → Prop) : Prop :=
  ∃ x x', Q x ∧ Q x' ∧ x ≠ x' ∧ f (P x) = f (P x')

/-- Some input in `Q` whose image under `P` has zero capacity part: event E2 of
[KatzLindell2020], Claim 7.8. -/
@[expose]
def ZeroCapacity (P : Equiv.Perm (R × C)) (Q : R × C → Prop) : Prop :=
  ∃ x, Q x ∧ (P x).2 = 0

omit [AddGroup R] [Zero C] in
theorem ImageCollision.mono {D : Type*} {P : Equiv.Perm (R × C)} {f : R × C → D}
    {Q Q' : R × C → Prop} (h : ImageCollision P f Q) (hQ : ∀ x, Q x → Q' x) :
    ImageCollision P f Q' := by
  obtain ⟨x, x', hx, hx', hne, heq⟩ := h
  exact ⟨x, x', hQ x hx, hQ x' hx', hne, heq⟩

omit [AddGroup R] in
theorem ZeroCapacity.mono {P : Equiv.Perm (R × C)} {Q Q' : R × C → Prop}
    (h : ZeroCapacity P Q) (hQ : ∀ x, Q x → Q' x) : ZeroCapacity P Q' := by
  obtain ⟨x, hx, h0⟩ := h
  exact ⟨x, hQ x hx, h0⟩

/-- Distinct block sequences with equal capacity part after absorbing trigger event E3 or E2
among their evaluated permutation inputs. -/
theorem capacityCollision_or_zeroCapacity (P : Equiv.Perm (R × C)) :
    ∀ ms ms' : List R, ms ≠ ms' → (absorb P ms).2 = (absorb P ms').2 →
      ImageCollision P Prod.snd (fun x => IsInput P ms x ∨ IsInput P ms' x) ∨
        ZeroCapacity P (fun x => IsInput P ms x ∨ IsInput P ms' x) := by
  intro ms
  induction ms using List.reverseRecOn with
  | nil =>
    intro ms' hne h
    obtain rfl | ⟨a', m', rfl⟩ := List.eq_nil_or_concat ms'
    · exact absurd rfl hne
    rw [List.concat_eq_append] at *
    · exact Or.inr ⟨_, Or.inr (isInput_concat P a' m'), by simpa using h.symm⟩
  | append_singleton a m ih =>
    intro ms' hne h
    obtain rfl | ⟨a', m', rfl⟩ := List.eq_nil_or_concat ms'
    · exact Or.inr ⟨_, Or.inl (isInput_concat P a m), by simpa using h⟩
    rw [List.concat_eq_append] at *
    by_cases hx : ((absorb P a).1 + m, (absorb P a).2) = ((absorb P a').1 + m', (absorb P a').2)
    · have ha : a ≠ a' := by
        rintro rfl
        exact hne (by rw [add_left_cancel (Prod.ext_iff.1 hx).1])
      have hQ : ∀ x, (IsInput P a x ∨ IsInput P a' x) →
          IsInput P (a ++ [m]) x ∨ IsInput P (a' ++ [m']) x :=
        fun x hx => hx.imp (·.append_right _) (·.append_right _)
      exact (ih a' ha (Prod.ext_iff.1 hx).2).imp (·.mono hQ) (·.mono hQ)
    · exact Or.inl ⟨_, _, Or.inl (isInput_concat P a m), Or.inr (isInput_concat P a' m'), hx,
        by simpa using h⟩

/-- **Claim 7.8 for forward queries** ([KatzLindell2020], Section 7.3.3): if two distinct
nonempty block sequences have equal first output, then among the permutation inputs evaluated
while absorbing them, event E1 (two distinct inputs whose images have equal output), event E2
(an image with zero capacity part) or event E3 (two distinct inputs whose images have equal
capacity part) occurs. -/
theorem badEvent_of_out_eq (P : Equiv.Perm (R × C)) (out : R × C → O) {ms ms' : List R}
    (hms : ms ≠ []) (hms' : ms' ≠ []) (hne : ms ≠ ms')
    (h : out (absorb P ms) = out (absorb P ms')) :
    ImageCollision P out (fun x => IsInput P ms x ∨ IsInput P ms' x) ∨
      ZeroCapacity P (fun x => IsInput P ms x ∨ IsInput P ms' x) ∨
      ImageCollision P Prod.snd (fun x => IsInput P ms x ∨ IsInput P ms' x) := by
  by_cases hy : absorb P ms = absorb P ms'
  · exact Or.inr ((capacityCollision_or_zeroCapacity P ms ms' hne (by rw [hy])).symm)
  obtain ⟨a, m, rfl⟩ := (List.eq_nil_or_concat ms).resolve_left hms
  obtain ⟨a', m', rfl⟩ := (List.eq_nil_or_concat ms').resolve_left hms'
  simp only [List.concat_eq_append] at *
  refine Or.inl ⟨_, _, Or.inl (isInput_concat P a m), Or.inr (isInput_concat P a' m'), ?_,
    by simpa using h⟩
  intro hx
  exact hy (by simp only [absorb_concat, hx])

/-- **A capacity collision extends to a full collision.** If `a` and `a'` reach states with
equal capacity part, then appending `m` to `a` and the corrected block
`-(absorb P a').1 + ((absorb P a).1 + m)` to `a'` reaches the same state, so any common
suffix gives equal hashes. -/
theorem absorb_eq_of_capacity_eq (P : Equiv.Perm (R × C)) {a a' : List R}
    (h : (absorb P a).2 = (absorb P a').2) (m : R) (s : List R) :
    absorb P (a ++ m :: s) =
      absorb P (a' ++ (-(absorb P a').1 + ((absorb P a).1 + m)) :: s) := by
  rw [absorb_append, absorb_append, List.foldl_cons, List.foldl_cons]
  congr 1
  simp only [absorbStep, add_neg_cancel_left, h]

end Blocks

/-! ### Padding and parsing -/

/-- Padding of Construction 7.6: append a `1` and then the fewest zeros making the length a
multiple of `r`. -/
@[expose]
def pad (r : ℕ) (msg : List Bool) : List Bool :=
  msg ++ true :: List.replicate ((r - (msg.length + 1) % r) % r) false

/-- Parse a bit string into its consecutive `r`-bit blocks, dropping any incomplete final
block. -/
@[expose]
def toBlocks (r : ℕ) (l : List Bool) : List (BitString r) :=
  (List.range (l.length / r)).map fun b i => l.getD (b * r + i) false

private theorem replicate_false_append_true_inj :
    ∀ (k k' : ℕ) (a b : List Bool),
      List.replicate k false ++ true :: a = List.replicate k' false ++ true :: b → a = b
  | 0, 0, a, b, h => by simpa using h
  | k + 1, 0, a, b, h => by simp [List.replicate_succ] at h
  | 0, k' + 1, a, b, h => by simp [List.replicate_succ] at h
  | k + 1, k' + 1, a, b, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    exact replicate_false_append_true_inj k k' a b h

/-- Padding is injective: distinct messages have distinct padded strings. -/
theorem pad_injective (r : ℕ) : Function.Injective (pad r) := by
  intro a b h
  have h' := congrArg List.reverse h
  simp only [pad, List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.append_assoc, List.singleton_append] at h'
  simpa using congrArg List.reverse (replicate_false_append_true_inj _ _ _ _ h')

theorem dvd_length_pad {r : ℕ} (hr : 0 < r) (msg : List Bool) : r ∣ (pad r msg).length := by
  have h1 := Nat.mod_lt (msg.length + 1) hr
  have hlen : (pad r msg).length = (msg.length + 1) + (r - (msg.length + 1) % r) % r := by
    simp only [pad, List.length_append, List.length_cons, List.length_replicate]
    omega
  rw [hlen, Nat.dvd_iff_mod_eq_zero]
  rcases Nat.eq_zero_or_pos ((msg.length + 1) % r) with h | h
  · rw [h, Nat.sub_zero, Nat.mod_self, Nat.add_zero, h]
  · rw [Nat.mod_eq_of_lt (by omega : r - (msg.length + 1) % r < r), Nat.add_mod,
      Nat.mod_eq_of_lt (by omega : r - (msg.length + 1) % r < r), Nat.add_sub_cancel' h1.le,
      Nat.mod_self]

/-- On a message whose length is a multiple of `r`, padding appends one full block
`1 ‖ 0^(r - 1)`. -/
theorem pad_of_dvd {r : ℕ} (hr : 0 < r) {msg : List Bool} (h : r ∣ msg.length) :
    pad r msg = msg ++ true :: List.replicate (r - 1) false := by
  obtain ⟨k, hk⟩ := h
  have : (r - (msg.length + 1) % r) % r = r - 1 := by
    rw [hk, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
    rcases Nat.lt_or_ge 1 r with h1 | h1
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)]
    · obtain rfl : r = 1 := by omega
      rfl
  simp only [pad, this]

@[simp]
theorem length_toBlocks (r : ℕ) (l : List Bool) : (toBlocks r l).length = l.length / r := by
  simp [toBlocks]

theorem getElem?_toBlocks (r : ℕ) (l : List Bool) (b : ℕ) :
    (toBlocks r l)[b]? =
      if b < l.length / r then some (fun i : Fin r => l.getD (b * r + i) false) else none := by
  by_cases hb : b < l.length / r <;> simp [toBlocks, hb]

private theorem getD_eq_of_toBlocks_eq {r : ℕ} (hr : 0 < r) {l l' : List Bool}
    (h : toBlocks r l = toBlocks r l') {n : ℕ} (hn : n / r < l.length / r) :
    l.getD n false = l'.getD n false := by
  have hn' : n / r < l'.length / r := by
    have := congrArg List.length h
    simp only [length_toBlocks] at this
    rwa [← this]
  have e := congrArg (fun L => (L[n / r]?).map (· ⟨n % r, Nat.mod_lt n hr⟩)) h
  simp only [getElem?_toBlocks, hn, hn', ↓reduceIte, Option.map_some, Option.some.injEq] at e
  rwa [Nat.div_add_mod'] at e

/-- Parsing is injective on strings whose lengths are multiples of `r`. -/
theorem toBlocks_injOn {r : ℕ} (hr : 0 < r) {l l' : List Bool} (hl : r ∣ l.length)
    (hl' : r ∣ l'.length) (h : toBlocks r l = toBlocks r l') : l = l' := by
  have hlen : l.length = l'.length := by
    have := congrArg List.length h
    simp only [length_toBlocks] at this
    rw [← Nat.div_mul_cancel hl, ← Nat.div_mul_cancel hl', this]
  refine List.ext_getElem hlen fun n hn hn' => ?_
  have hd : n / r < l.length / r := by
    rw [Nat.div_lt_iff_lt_mul hr, Nat.div_mul_cancel hl]
    exact hn
  have := getD_eq_of_toBlocks_eq hr h hd
  rwa [List.getD_eq_getElem _ _ hn, List.getD_eq_getElem _ _ hn'] at this

/-- Distinct messages have distinct padded block sequences. -/
theorem toBlocks_pad_injective {r : ℕ} (hr : 0 < r) :
    Function.Injective fun msg => toBlocks r (pad r msg) := fun _ _ h =>
  pad_injective r (toBlocks_injOn hr (dvd_length_pad hr _) (dvd_length_pad hr _) h)

theorem toBlocks_pad_ne_nil {r : ℕ} (hr : 0 < r) (msg : List Bool) :
    toBlocks r (pad r msg) ≠ [] := by
  have hpos : 0 < (pad r msg).length := by simp [pad]
  refine List.ne_nil_of_length_pos ?_
  rw [length_toBlocks]
  exact Nat.div_pos (Nat.le_of_dvd hpos (dvd_length_pad hr msg)) hr

theorem toBlocks_append {r : ℕ} (hr : 0 < r) {a : List Bool} (ha : r ∣ a.length)
    (b : List Bool) : toBlocks r (a ++ b) = toBlocks r a ++ toBlocks r b := by
  obtain ⟨k, hk⟩ := ha
  have hka : (toBlocks r a).length = k := by
    rw [length_toBlocks, hk, Nat.mul_div_cancel_left _ hr]
  refine List.ext_getElem? fun j => ?_
  rcases Nat.lt_or_ge j k with hj | hj
  · rw [List.getElem?_append_left (by rw [hka]; exact hj), getElem?_toBlocks, getElem?_toBlocks,
      List.length_append, hk, Nat.mul_add_div hr, Nat.mul_div_cancel_left _ hr]
    simp only [Nat.lt_add_right _ hj, hj, ↓reduceIte, Option.some.injEq]
    funext i
    exact List.getD_append _ _ _ _ (by
      rw [hk]; nlinarith [i.isLt, Nat.mul_le_mul_right r (show j + 1 ≤ k from hj)])
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [List.getElem?_append_right (by rw [hka]; exact hj), hka, Nat.add_sub_cancel_left,
      getElem?_toBlocks, getElem?_toBlocks, List.length_append, hk, Nat.mul_add_div hr]
    simp only [Nat.add_lt_add_iff_left]
    split_ifs
    · congr 1
      funext i
      rw [List.getD_append_right a b false ((k + d) * r + i) (by rw [hk]; nlinarith), hk,
        show (k + d) * r + i - r * k = d * r + i by
          rw [add_mul, mul_comm k r, Nat.add_assoc, Nat.add_sub_cancel_left]]
    · rfl

@[simp]
theorem toBlocks_ofFn {r : ℕ} (hr : 0 < r) (m : BitString r) :
    toBlocks r (List.ofFn m) = [m] := by
  refine List.ext_getElem? fun j => ?_
  rw [getElem?_toBlocks, List.length_ofFn, Nat.div_self hr]
  rcases j with _ | j
  · simp only [Nat.zero_lt_one, ↓reduceIte, zero_mul, zero_add, List.getElem?_cons_zero,
      Option.some.injEq]
    funext i
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  · simp

/-! ### The sponge hash on messages -/

section Messages

variable {r c : ℕ} {O : Type*}

/-- The sponge hash of Construction 7.6 with `k` squeezing outputs: pad the message, parse it
into `r`-bit blocks and run `hashBlocks`. The output is the list `[h₁, …, h_k]`; with
`out` the first `v` bits of the state, its flattening is `h₁ ‖ ⋯ ‖ h_k`. -/
@[expose]
def hash (P : Equiv.Perm (BitString r × BitString c)) (out : BitString r × BitString c → O)
    (k : ℕ) (msg : List Bool) : List O :=
  hashBlocks P out k (toBlocks r (pad r msg))

/-- **Claim 7.8 for forward queries, on messages**: a collision between distinct messages
triggers event E1, E2 or E3 among the permutation inputs evaluated while absorbing their padded
block sequences. -/
theorem badEvent_of_hash_eq (hr : 0 < r) (P : Equiv.Perm (BitString r × BitString c))
    (out : BitString r × BitString c → O) (k : ℕ) {msg msg' : List Bool} (hne : msg ≠ msg')
    (h : hash P out (k + 1) msg = hash P out (k + 1) msg') :
    ImageCollision P out (fun x => IsInput P (toBlocks r (pad r msg)) x ∨
        IsInput P (toBlocks r (pad r msg')) x) ∨
      ZeroCapacity P (fun x => IsInput P (toBlocks r (pad r msg)) x ∨
        IsInput P (toBlocks r (pad r msg')) x) ∨
      ImageCollision P Prod.snd (fun x => IsInput P (toBlocks r (pad r msg)) x ∨
        IsInput P (toBlocks r (pad r msg')) x) := by
  refine badEvent_of_out_eq P out (toBlocks_pad_ne_nil hr msg) (toBlocks_pad_ne_nil hr msg')
    ((toBlocks_pad_injective hr).ne hne) ?_
  simpa [hash, hashBlocks_succ] using congrArg List.head? h

/-- Hashing a full-block message `u` followed by one more block `m` absorbs `u`'s blocks, then
`m`, then the padding block. -/
theorem toBlocks_pad_append_ofFn (hr : 0 < r) {u : List Bool} (hu : r ∣ u.length)
    (m : BitString r) :
    toBlocks r (pad r (u ++ List.ofFn m)) =
      toBlocks r u ++ m :: toBlocks r (true :: List.replicate (r - 1) false) := by
  have hum : r ∣ (u ++ List.ofFn m).length := by
    simpa using Nat.dvd_add hu (dvd_refl r)
  rw [pad_of_dvd hr hum, List.append_assoc, toBlocks_append hr hu,
    toBlocks_append hr (a := List.ofFn m) (by simp), toBlocks_ofFn hr]
  rfl

/-- **Generic capacity-collision attack**: if distinct full-block messages `u ≠ u'` of equal
length reach states with equal capacity part, then extending them by one block each (`m`, and the
corrected block for `u'`) gives two distinct messages with equal hashes, for every output map
and number of squeezing outputs. -/
theorem hash_eq_of_capacity_eq (hr : 0 < r) (P : Equiv.Perm (BitString r × BitString c))
    {u u' : List Bool} (hu : r ∣ u.length) (hlen : u.length = u'.length) (hne : u ≠ u')
    (h : (absorb P (toBlocks r u)).2 = (absorb P (toBlocks r u')).2) (m : BitString r)
    (out : BitString r × BitString c → O) (k : ℕ) :
    u ++ List.ofFn m ≠
        u' ++ List.ofFn (-(absorb P (toBlocks r u')).1 + ((absorb P (toBlocks r u)).1 + m)) ∧
      hash P out k (u ++ List.ofFn m) =
        hash P out k (u' ++
          List.ofFn (-(absorb P (toBlocks r u')).1 + ((absorb P (toBlocks r u)).1 + m))) := by
  have hu' : r ∣ u'.length := hlen ▸ hu
  refine ⟨fun heq => hne (List.append_inj heq hlen).1, ?_⟩
  simp only [hash, hashBlocks, toBlocks_pad_append_ofFn hr hu, toBlocks_pad_append_ofFn hr hu',
    absorb_eq_of_capacity_eq P h]

/-- **Exercise 7.26** ([KatzLindell2020], Section 7.3.3): if the permutation acts separately on
the rate and capacity parts, `P = S × T`, the capacity part after absorbing never depends on the
message, so the one-block messages `0^r` and `1^r` already have equal capacity part and extend
to an explicit collision. (The exercise's `P = S₁ ‖ ⋯ ‖ S₈` with `r = c = 4n` is such a
product.) -/
theorem hash_prodCongr_collision (hr : 0 < r) (S : Equiv.Perm (BitString r))
    (T : Equiv.Perm (BitString c)) (m : BitString r) (out : BitString r × BitString c → O)
    (k : ℕ) :
    List.ofFn (fun _ => false : BitString r) ++ List.ofFn m ≠
        List.ofFn (fun _ => true : BitString r) ++
          List.ofFn (-S (fun _ => true) + (S (fun _ => false) + m)) ∧
      hash (S.prodCongr T) out k (List.ofFn (fun _ => false : BitString r) ++ List.ofFn m) =
        hash (S.prodCongr T) out k (List.ofFn (fun _ => true : BitString r) ++
          List.ofFn (-S (fun _ => true) + (S (fun _ => false) + m))) := by
  have hne : List.ofFn (fun _ => false : BitString r) ≠
      List.ofFn (fun _ => true : BitString r) := by
    intro h
    simpa using congrFun (List.ofFn_injective h) ⟨0, hr⟩
  have hc (x : BitString r) :
      absorb (S.prodCongr T) (toBlocks r (List.ofFn x)) = (S x, T 0) := by
    rw [toBlocks_ofFn hr]
    simp [absorb, absorbStep]
  have h := hash_eq_of_capacity_eq hr (S.prodCongr T) (by simp) (by simp) hne
    (by rw [hc, hc]) m out k
  rwa [hc, hc] at h

end Messages

end Cslib.Crypto.Sponge
