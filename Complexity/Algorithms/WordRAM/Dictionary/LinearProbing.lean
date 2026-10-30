/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.Dictionary
public import Complexity.Algorithms.WordRAM.Hashing.KWise
public import Complexity.Algorithms.WordRAM.Dictionary.LinearProbing.FiveWise
public import Complexity.Computability.WordRAM.Randomized.Subroutine

/-!
# Open-Addressed Linear Probing on the Randomized Word RAM

This file implements a self-contained open-addressed linear-probing hash table realizing
`Cslib.Algorithms.Lean.Dictionary.spec U V n_max` on the randomized Word RAM
(`Cslib.WordRAM.Randomized.SubroutineDS`), adapting [Pagh, Pagh and Ružić, *Linear Probing with
Constant Independence*, *SIAM J. Comput.* 39(3):1107–1120, 2009, Section 2.3 (Lemma 2.1,
pp. 1110–1111) and Section 4 (Lemma 4.1, Theorem 4.3, and Theorem 4.5,
pp. 1114–1118)][PaghPaghRuzic2009]; [Cormen, Leiserson, Rivest and Stein, *Introduction to
Algorithms*, Section 11.4][CLRS2009].

## Design

1. **Power-of-$2$ open-addressed layout ($O(n_{\max})$ words, zero tombstones):**
   For capacity bound $n_{\max}$, we set $M = \mathrm{tableLog}(n_{\max}) =
   \lceil \log_2 \max(8 n_{\max}, 8) \rceil$ and table size $m = 2^M$ (`tableSize n_max`), so that
   $8 n_{\max} \le 2^M < 16 \max(n_{\max}, 1)$ (load factor $\alpha \le 1/8$). Memory at `base`
   consists of:
   - `[base, base + KWise.space n_max 5)`: embedded $5$-wise independent trinomial-field hash state
     (`Cslib.Algorithms.WordRAM.Hashing.KWise`);
   - `[usedBase, usedBase + 2^M)`: occupancy flags `used[0 .. 2^M - 1]` (`0` = empty, `1` =
     occupied, so zero-initialized memory is immediately a valid empty table);
   - `[keyBase, keyBase + 2^M)`: stored keys `key[0 .. 2^M - 1]`;
   - `[valBase, valBase + 2^M)`: stored values `val[0 .. 2^M - 1]`.
   Total footprint is `space n_max = KWise.space n_max 5 + 3 * tableSize n_max = O(n_max)` words.

2. **Self-contained operations (`initSetup`, `get`, `insert`):**
   - `initSetup`: runs `KWise.initCode 5` ($O(n_{\max})$ deterministic Four-Russians carryless
     multiplication table setup plus $5$ `Code.rand` calls, with zero caller-supplied primes).
   - `get u` and `insert u v`: evaluate $b = h_\theta(u) \in \mathrm{Fin}(2^M)$ via
     `KWise.evalCode 5` in $O(L^2 + 1)$ deterministic steps ($L = \mathrm{limbCount}(n_{\max}, U, M)
     = O(1)$ when $U \le n_{\max}^c$), then scan $(b + d) \bmod 2^M$ until reaching the first slot
     `p` where `used[p] = 0` or `key[p] = u`. Because at most $n_{\max} \le 2^M / 8$ slots are
     occupied, at least $7/8$ of all slots are empty and the probe loop terminates deterministically
     in $\le n_{\max} < 2^M$ iterations on every seed.

3. **Expected $O(1)$ probe bound under $5$-wise independence:**
   If probing for $u$ from $b = h_\theta(u)$ steps over $t \ge 1$ slots occupied by keys in
   $S = \mathrm{dom}(s) \setminus \{u\}$, walking backwards from $b$ to the nearest preceding empty
   slot yields a contiguous cyclic interval `cyclicInterval M b a ℓ` of length
   $\ell = a + t \in [t, \#S]$ whose $\ell$ stored keys in $S$ all hash into
   `cyclicInterval M b a ℓ` (`TableInv.hasClusterWitness_probeLen`, adapting the occupied-run
   argument in the proof of Lemma 4.1, p. 1114 of `[PaghPaghRuzic2009]`). Applying
   `tsum_uniform_probe_le_of_cluster_witness` from
   `Complexity.Algorithms.WordRAM.Dictionary.LinearProbing.FiveWise` bounds the expected number of
   skipped occupied slots `TableInv.probeLen` by $288 = O(1)$ (`tsum_probeLen_le`).

## Source mapping, specialization, and cost scope

In `[PaghPaghRuzic2009]`, Section 4 (Theorems 4.3 and 4.5, pp. 1115–1118, built on Lemma 2.1,
pp. 1110–1111, and Lemma 4.1, p. 1114) proves that for any sequence of insertions, deletions, and
lookups in a linear-probing hash table of size $r$ using a hash function chosen uniformly at random
from a $5$-wise independent family $\mathcal{H} : U \to [r]$ with maximum load $\bar{\alpha} < 1$,
the expected number of probes made during an operation is $O((1 - \bar{\alpha})^{-5/2})$
(Theorem 4.3) and $O((1 - \bar{\alpha})^{-13/6})$ (Theorem 4.5), which is $O(1)$ for bounded load
factor. The declarations in this module and `LinearProbing.FiveWise` map to `[PaghPaghRuzic2009]` as
follows:
- **Hash family (`isKWiseIndependentHash_hashFn`):**
  Uniform $5$-wise independent trinomial-field polynomial family `hashFn U n_max`
  (`trinomialPolyHash` over $\mathbb{F}_{2^q}$ projected to $M$ bits, initialized and evaluated on
  the Word RAM via `KWise.initCode 5` and `KWise.evalCode 5`), realizing exact uniform $5$-wise
  independence (`IsKWiseIndependentHash 5`) with maximum load $\bar{\alpha} = \alpha = \#S / 2^M$.
- **Operation history and oblivious adversary (`ValidHistory`, `seq_expected_amortized`):**
  An admissible operation sequence `ops : List (Dictionary.Op U)` fixed independently of the sampled
  hash seed $\theta \sim \mathrm{seedLaw}\ U\ n_{\max}$, matching the fixed-set / oblivious
  operation model of `[PaghPaghRuzic2009]`, Section 4.
- **Load-factor specialization ($\alpha \le 1/8$):**
  While `[PaghPaghRuzic2009]` Theorems 4.3 and 4.5 apply to any maximum load $\bar{\alpha} < 1$, we
  fix $M = \mathrm{tableLog}(n_{\max}) = \lceil \log_2 \max(8 n_{\max}, 8) \rceil$ so that
  $\alpha = \#\mathrm{dom}(s) / 2^M \le n_{\max} / 2^M \le 1/8$ (`eight_mul_le_tableSize`) and
  `space n_max = O(n_max)` (`space_le`).
- **Probe count (`TableInv.probeLen`) vs. executable Word-RAM body charge (`charge`):**
  Whereas `[PaghPaghRuzic2009]` Section 4 (p. 1114) counts
  $1 + \max\{l \mid h(x) + [l] \subseteq P\}$ table probes, `TableInv.probeLen` counts the number of
  skipped occupied slots before the stopping slot ($\mathbb{E}[\mathrm{probeLen}] \le 288$ via
  `tsum_probeLen_le`). The final stopping-slot inspection, loop/branch overhead ($12 t + 27$
  instructions for $t$ skipped slots), and embedded `KWise.evalCode 5` hash evaluation
  (`KWise.evalSteps n_max U (tableLog n_max) 5`) are all included in the executable Word-RAM
  operation charge
  `charge U n_max = KWise.evalSteps n_max U (tableLog n_max) 5 + 12 * 288 + 27 =
  KWise.evalSteps n_max U (tableLog n_max) 5 + 3483` (`opCode_execWithin`).
- **Original proof adaptation and explicit constants (`288` and `3483`):**
  Rather than formalizing the interval-grid decompositions of Lemmas 4.2 and 4.4 in
  `[PaghPaghRuzic2009]`, `LinearProbing.FiveWise` uses an original simplified proof adaptation at
  load $\le 1/8$ that covers any length-$\ell$ cyclic interval containing $b$ ($2^{j-1} \le \ell <
  2^j$) by a single centered dyadic-scale window `scaleWindow M b j` of size at most $2^{j+1}$
  (`card_scaleWindow_le`), yielding the explicit scale-$j$ overload bound
  $18 / (2^{j-2})^2 = 288 / 4^j$ (`expect_scaleOverload_le`), the probe-step bound $288$, and the
  instruction constant $12 \cdot 288 + 27 = 3483$.
- **Fixed-parameter program specialization and charged-body scope (`initParams = Fin.elim0`):**
  For fixed `(U, V, n_max)` on an admissible external machine word width `w`
  (`2 * trinomialDeg U (tableLog n_max) ≤ w`, `Fits w (base + space n_max)`, `Fits w V`),
  `subroutineCode U n_max` specializes configuration constants as instruction literals. Expected
  instruction bounds (`subroutineDS`, `subroutineDSStandard`, and `seq_expected_amortized`) charge
  fresh initialization (`initFresh`) and subroutine operation bodies (`SubroutineDS.ExecSteps`),
  excluding caller argument delivery, caller control/dispatch loops, and host-level code
  construction.
- **Insert-only dictionary specification vs. source deletions:**
  Whereas `[PaghPaghRuzic2009]` Section 1 (p. 1107) and Section 4 (Theorems 4.3 and 4.5) include
  deletions via greedy backward-shift rearrangement, `Dictionary.spec U V n_max` specifies an
  insert-only bounded dictionary (`get` and `insert` with at most `n_max` distinct keys and no
  deletion operation), so open-addressed slots use `{0, 1}` occupancy flags (`0` = empty, `1` =
  occupied) with zero tombstones.

## References

* [A. Pagh, R. Pagh and M. Ružić, *Linear Probing with Constant Independence*][PaghPaghRuzic2009]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 11.4][CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.Dictionary.LinearProbing

open Cslib.WordRAM Cslib.WordRAM.Randomized Cslib.Probability
open Cslib.Algorithms.Lean
open Cslib.Algorithms.WordRAM.ExactLog
open Cslib.Algorithms.WordRAM.Hashing
open Finset
open scoped BigOperators ENNReal

/-! ## Section 1: Parameters, memory layout, and cyclic probe geometry -/

/-- Latent seed type for the embedded $5$-wise independent trinomial-field hash family:
$5$ coefficients in $\mathrm{Fin}(2^{\mathrm{trinomialDeg}(U, \mathrm{tableLog}(n_{\max}))})$. -/
abbrev Seed (U n_max : ℕ) : Type :=
  Fin 5 → Fin (2 ^ trinomialDeg U (tableLog n_max))

/-- Uniform reference distribution over `Seed U n_max`. -/
@[expose] noncomputable def seedLaw (U n_max : ℕ) : PMF (Seed U n_max) :=
  PMF.uniformOfFintype (Seed U n_max)

/-- The $5$-wise independent hash function $h_\theta : \mathrm{Fin}\,U \to \mathrm{Fin}(2^M)$
associated with seed $\theta$. -/
@[expose] noncomputable def hashFn (U n_max : ℕ) (θ : Seed U n_max) (u : Fin U) :
    Fin (2 ^ tableLog n_max) :=
  trinomialPolyHash (trinomialStep U (tableLog n_max)) 5 U (tableLog n_max) θ u

/-- `hashFn U n_max` is a $5$-wise independent hash family. -/
theorem isKWiseIndependentHash_hashFn (U n_max : ℕ) :
    IsKWiseIndependentHash 5 (hashFn U n_max) :=
  isKWiseIndependentHash_trinomialPolyHash
    (le_two_pow_trinomialDeg U (tableLog n_max))
    (le_trinomialDeg U (tableLog n_max))

/-- Base address of the occupancy array `used[0 .. 2^M - 1]`. -/
@[expose] def usedBase (base n_max : ℕ) : ℕ :=
  base + KWise.space n_max 5

/-- Base address of the key array `key[0 .. 2^M - 1]`. -/
@[expose] def keyBase (base n_max : ℕ) : ℕ :=
  usedBase base n_max + tableSize n_max

/-- Base address of the value array `val[0 .. 2^M - 1]`. -/
@[expose] def valBase (base n_max : ℕ) : ℕ :=
  keyBase base n_max + tableSize n_max

/-- Total contiguous memory footprint of the linear-probing dictionary (in words):
`KWise.space n_max 5 + 3 * tableSize n_max = O(n_max)`. -/
@[expose] def space (n_max : ℕ) : ℕ :=
  KWise.space n_max 5 + 3 * tableSize n_max

/-- `space n_max` is $O(n_{\max})$: specifically `space n_max ≤ 49 * max n_max 4 + 13`. -/
theorem space_le (n_max : ℕ) : space n_max ≤ 49 * max n_max 4 + 13 := by
  dsimp only [space, KWise.space, KWise.spaceFromB]
  have h1 := KWise.two_pow_two_mul_chunkBits_le n_max
  have h2 := tableSize_le_sixteen_mul n_max
  omega

/-- Slot probed at offset `d` from starting bucket `b : Fin (2 ^ M)`: `(b.val + d) mod 2 ^ M`. -/
@[expose] def probeSlot (M : ℕ) (b : Fin (2 ^ M)) (d : ℕ) : Fin (2 ^ M) :=
  cyclicSlotMod M (b.val + d)

/-- Slot located `a` positions cyclically before `b : Fin (2 ^ M)`: `(b.val - a) mod 2 ^ M`. -/
@[expose] def backSlot (M : ℕ) (b : Fin (2 ^ M)) (a : ℕ) : Fin (2 ^ M) :=
  cyclicSlotMod M (b.val + 2 ^ M * (a + 1) - a)

@[simp]
theorem probeSlot_zero {M : ℕ} (b : Fin (2 ^ M)) : probeSlot M b 0 = b := by
  apply Fin.ext
  simp [probeSlot, cyclicSlotMod, Nat.mod_eq_of_lt b.isLt]

theorem probeSlot_add {M : ℕ} (b : Fin (2 ^ M)) (d₁ d₂ : ℕ) :
    probeSlot M (probeSlot M b d₁) d₂ = probeSlot M b (d₁ + d₂) := by
  apply Fin.ext
  simp [probeSlot, cyclicSlotMod, Nat.add_assoc]

theorem probeSlot_backSlot_eq {M : ℕ} (b : Fin (2 ^ M)) (a idx : ℕ) :
    probeSlot M (backSlot M b a) idx =
      cyclicSlotMod M (b.val + 2 ^ M * (a + 1) - a + idx) := by
  apply Fin.ext
  simp [probeSlot, backSlot, cyclicSlotMod]

theorem cyclicInterval_eq_image_probeSlot {M : ℕ} (b : Fin (2 ^ M)) (a len : ℕ) :
    cyclicInterval M b a len =
      (Finset.range len).image (probeSlot M (backSlot M b a)) := by
  ext y
  simp [cyclicInterval, probeSlot_backSlot_eq]

theorem probeSlot_backSlot_add {M : ℕ} (b : Fin (2 ^ M)) (a d : ℕ) :
    probeSlot M (backSlot M b a) (a + d) = probeSlot M b d := by
  apply Fin.ext
  simp only [probeSlot, backSlot, cyclicSlotMod]
  have h1 : a ≤ 2 ^ M * (a + 1) := by
    have : 1 ≤ 2 ^ M := Nat.one_le_two_pow
    calc a ≤ 1 * (a + 1) := by omega
      _ ≤ 2 ^ M * (a + 1) := Nat.mul_le_mul_right (a + 1) this
  have heq : (b.val + 2 ^ M * (a + 1) - a) % 2 ^ M + (a + d) =
      (b.val + 2 ^ M * (a + 1) - a) % 2 ^ M + a + d := by omega
  rw [Nat.mod_add_mod, show b.val + 2 ^ M * (a + 1) - a + (a + d) =
      b.val + d + 2 ^ M * (a + 1) by omega, Nat.add_mul_mod_self_left]

theorem probeSlot_backSlot_sub {M : ℕ} (b : Fin (2 ^ M)) {a idx : ℕ} (hidx : idx ≤ a) :
    probeSlot M (backSlot M b a) idx = backSlot M b (a - idx) := by
  apply Fin.ext
  simp only [probeSlot, backSlot, cyclicSlotMod]
  have h1 : 1 ≤ 2 ^ M := Nat.one_le_two_pow
  have ha_le : a ≤ 2 ^ M * (a + 1) := by
    calc a ≤ 1 * (a + 1) := by omega
      _ ≤ 2 ^ M * (a + 1) := Nat.mul_le_mul_right (a + 1) h1
  have hsub_le : a - idx ≤ 2 ^ M * (a - idx + 1) := by
    calc a - idx ≤ 1 * (a - idx + 1) := by omega
      _ ≤ 2 ^ M * (a - idx + 1) := Nat.mul_le_mul_right (a - idx + 1) h1
  have hmul : 2 ^ M * (a + 1) = 2 ^ M * (a - idx + 1) + 2 ^ M * idx := by
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [Nat.mod_add_mod, show b.val + 2 ^ M * (a + 1) - a + idx =
      (b.val + 2 ^ M * (a - idx + 1) - (a - idx)) + 2 ^ M * idx by omega,
    Nat.add_mul_mod_self_left]

theorem probeSlot_injOn_range {M : ℕ} (b : Fin (2 ^ M)) {len : ℕ} (hlen : len ≤ 2 ^ M) :
    Set.InjOn (probeSlot M b) (Finset.range len) := by
  intro i hi j hj hij
  simp only [Finset.mem_coe, Finset.mem_range] at hi hj
  have hval : (b.val + i) % 2 ^ M = (b.val + j) % 2 ^ M := congrArg Fin.val hij
  have hb : b.val < 2 ^ M := b.isLt
  have hi_mod : (b.val + i) % 2 ^ M =
      if b.val + i < 2 ^ M then b.val + i else b.val + i - 2 ^ M := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have hj_mod : (b.val + j) % 2 ^ M =
      if b.val + j < 2 ^ M then b.val + j else b.val + j - 2 ^ M := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hi_mod, hj_mod] at hval
  split_ifs at hval <;> omega

theorem card_cyclicInterval {M : ℕ} (b : Fin (2 ^ M)) (a : ℕ) {len : ℕ} (hlen : len ≤ 2 ^ M) :
    #(cyclicInterval M b a len) = len := by
  rw [cyclicInterval_eq_image_probeSlot,
    Finset.card_image_of_injOn (probeSlot_injOn_range (backSlot M b a) hlen), Finset.card_range]

/-! ## Section 2: Open-addressed table invariant, termination, and cluster witness -/

/-- Occupancy flag `used[p]` at slot `p : Fin (2 ^ tableLog n_max)`. -/
@[expose] def usedAt (base n_max : ℕ) (mem : ℕ → ℕ) (p : Fin (2 ^ tableLog n_max)) : ℕ :=
  mem (usedBase base n_max + p.val)

/-- Stored key `key[p]` at slot `p : Fin (2 ^ tableLog n_max)`. -/
@[expose] def keyAt (base n_max : ℕ) (mem : ℕ → ℕ) (p : Fin (2 ^ tableLog n_max)) : ℕ :=
  mem (keyBase base n_max + p.val)

/-- Stored value `val[p]` at slot `p : Fin (2 ^ tableLog n_max)`. -/
@[expose] def valAt (base n_max : ℕ) (mem : ℕ → ℕ) (p : Fin (2 ^ tableLog n_max)) : ℕ :=
  mem (valBase base n_max + p.val)

/-- Linear-probing table invariant at `(base, n_max)` coupling abstract state
`s : Dictionary.State U` and seed `θ : Seed U n_max` with concrete memory `mem`:
1. `(Dictionary.dom s).card ≤ n_max` and `Dictionary.ValuesBounded V s`;
2. every slot `p` has `usedAt p ∈ {0, 1}`;
3. every occupied slot `p` (`usedAt p = 1`) stores a valid key `keyAt p < U` and value
   `valAt p < V` matching `s ⟨keyAt p, _⟩ = some (valAt p)`;
4. occupied slots store pairwise distinct keys;
5. every present key `u` with `s u = some v` resides at some probe offset `k < 2 ^ M` from
   `hashFn U n_max θ u` such that all preceding probe offsets `j < k` are occupied (`usedAt = 1`);
6. conversely, every occupied slot `p` (`usedAt p = 1`) is reachable from its key's home bucket
   `hashFn U n_max θ ⟨keyAt p, _⟩` at some offset `k < 2 ^ M` along an entirely occupied prefix
   (`∀ j < k, usedAt = 1`). -/
structure TableInv (U V n_max base : ℕ) (θ : Seed U n_max) (s : Dictionary.State U)
    (mem : ℕ → ℕ) : Prop where
  /-- Number of stored keys is at most `n_max`. -/
  card_dom_le : (Dictionary.dom s).card ≤ n_max
  /-- Every stored value in `s` is strictly less than `V`. -/
  values_bounded : Dictionary.ValuesBounded V s
  /-- Every occupancy entry is `0` or `1`. -/
  used_bit : ∀ p : Fin (2 ^ tableLog n_max),
    usedAt base n_max mem p = 0 ∨ usedAt base n_max mem p = 1
  /-- Every occupied slot holds a key `< U`. -/
  occupied_key_lt : ∀ p : Fin (2 ^ tableLog n_max),
    usedAt base n_max mem p = 1 → keyAt base n_max mem p < U
  /-- Every occupied slot agrees with the abstract dictionary `s`. -/
  occupied_state : ∀ (p : Fin (2 ^ tableLog n_max)) (u : Fin U),
    usedAt base n_max mem p = 1 → keyAt base n_max mem p = u.val →
    s u = some (valAt base n_max mem p)
  /-- Distinct occupied slots hold distinct keys. -/
  occupied_inj : ∀ p₁ p₂ : Fin (2 ^ tableLog n_max),
    usedAt base n_max mem p₁ = 1 → usedAt base n_max mem p₂ = 1 →
    keyAt base n_max mem p₁ = keyAt base n_max mem p₂ → p₁ = p₂
  /-- Every present key `u` with `s u = some v` is stored at some offset `k < 2 ^ M` from its hash
  bucket with all intermediate probe slots `j < k` occupied. -/
  present_slot : ∀ (u : Fin U) (v : ℕ), s u = some v →
    ∃ k < 2 ^ tableLog n_max,
      let p := probeSlot (tableLog n_max) (hashFn U n_max θ u) k
      usedAt base n_max mem p = 1 ∧
      keyAt base n_max mem p = u.val ∧
      valAt base n_max mem p = v ∧
      ∀ j < k, usedAt base n_max mem (probeSlot (tableLog n_max) (hashFn U n_max θ u) j) = 1
  /-- Every occupied slot `p` has a contiguous occupied probe prefix from its key's hash bucket. -/
  occupied_prefix : ∀ (p : Fin (2 ^ tableLog n_max)) (u : Fin U),
    usedAt base n_max mem p = 1 → keyAt base n_max mem p = u.val →
    ∃ k < 2 ^ tableLog n_max,
      p = probeSlot (tableLog n_max) (hashFn U n_max θ u) k ∧
      ∀ j < k, usedAt base n_max mem (probeSlot (tableLog n_max) (hashFn U n_max θ u) j) = 1

/-- Any finset of occupied slots `A` whose keys belong to `K : Finset (Fin U)` has cardinality
`#A ≤ #K`. -/
theorem TableInv.card_slots_le {U V n_max base : ℕ} {θ : Seed U n_max} {s : Dictionary.State U}
    {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (A : Finset (Fin (2 ^ tableLog n_max))) (K : Finset (Fin U))
    (hused : ∀ p ∈ A, usedAt base n_max mem p = 1)
    (hkey : ∀ p (hp : p ∈ A), ⟨keyAt base n_max mem p, hinv.occupied_key_lt p (hused p hp)⟩ ∈ K) :
    #A ≤ #K := by
  have hU_pos : 0 < U ∨ A = ∅ := by
    by_cases hA : A = ∅
    · exact Or.inr hA
    · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hA
      exact Or.inl (Nat.lt_of_le_of_lt (Nat.zero_le _) (hinv.occupied_key_lt p (hused p hp)))
  rcases hU_pos with hU | rfl
  · let f : Fin (2 ^ tableLog n_max) → Fin U := fun p =>
      if h : keyAt base n_max mem p < U then ⟨keyAt base n_max mem p, h⟩ else ⟨0, hU⟩
    refine Finset.card_le_card_of_injOn f (fun p hp => ?_) (fun p₁ hp₁ p₂ hp₂ heq => ?_)
    · have hlt := hinv.occupied_key_lt p (hused p hp)
      simpa [f, hlt] using hkey p hp
    · simp only [Finset.mem_coe] at hp₁ hp₂
      have hlt₁ := hinv.occupied_key_lt p₁ (hused p₁ hp₁)
      have hlt₂ := hinv.occupied_key_lt p₂ (hused p₂ hp₂)
      have hval : keyAt base n_max mem p₁ = keyAt base n_max mem p₂ := by
        have := congrArg Fin.val heq
        simpa [f, hlt₁, hlt₂] using this
      exact hinv.occupied_inj p₁ p₂ (hused p₁ hp₁) (hused p₂ hp₂) hval
  · simp

/-- Every occupied slot `p` with `keyAt p ≠ u.val` maps to a key in `(Dictionary.dom s).erase u`. -/
theorem TableInv.key_mem_erase_of_ne {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    {p : Fin (2 ^ tableLog n_max)} (hp : usedAt base n_max mem p = 1) (u : Fin U)
    (hne : keyAt base n_max mem p ≠ u.val) :
    ⟨keyAt base n_max mem p, hinv.occupied_key_lt p hp⟩ ∈ (Dictionary.dom s).erase u := by
  rw [Finset.mem_erase]
  refine ⟨?_, ?_⟩
  · intro heq
    exact hne (congrArg Fin.val heq)
  · rw [Dictionary.mem_dom_iff]
    exact ⟨valAt base n_max mem p,
      hinv.occupied_state p ⟨keyAt base n_max mem p, hinv.occupied_key_lt p hp⟩ hp rfl⟩

/-- Probing for key `u` from bucket `b` continues past offset `d` when slot `probeSlot M b d` is
occupied (`used = 1`) by a key different from `u`. -/
@[expose] def probeContinue (base n_max : ℕ) (mem : ℕ → ℕ) (u : ℕ)
    (b : Fin (2 ^ tableLog n_max)) (d : ℕ) : Prop :=
  usedAt base n_max mem (probeSlot (tableLog n_max) b d) = 1 ∧
  keyAt base n_max mem (probeSlot (tableLog n_max) b d) ≠ u

instance instDecidableProbeContinue (base n_max : ℕ) (mem : ℕ → ℕ) (u : ℕ)
    (b : Fin (2 ^ tableLog n_max)) (d : ℕ) :
    Decidable (probeContinue base n_max mem u b d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- If probing for `u : Fin U` from `b` continues across all `i < d` (`d ≤ 2 ^ M`), then
`d ≤ #((Dictionary.dom s).erase u)`. -/
theorem TableInv.probeContinue_prefix_le {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) {d : ℕ} (hd : d ≤ 2 ^ tableLog n_max)
    (hcont : ∀ i < d, probeContinue base n_max mem u.val b i) :
    d ≤ #((Dictionary.dom s).erase u) := by
  set A := (Finset.range d).image (probeSlot (tableLog n_max) b)
  have hcardA : #A = d := by
    rw [Finset.card_image_of_injOn (probeSlot_injOn_range b hd), Finset.card_range]
  rw [← hcardA]
  refine hinv.card_slots_le A ((Dictionary.dom s).erase u) (fun p hp => ?_) (fun p hp => ?_)
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact (hcont i (Finset.mem_range.mp hi)).1
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    have hi' := Finset.mem_range.mp hi
    exact hinv.key_mem_erase_of_ne (hcont i hi').1 u (hcont i hi').2

/-- Under `TableInv`, probing for any `u : Fin U` from any `b` stops within
`#((Dictionary.dom s).erase u)` steps. -/
theorem TableInv.exists_not_probeContinue {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) :
    ∃ d ≤ #((Dictionary.dom s).erase u), ¬probeContinue base n_max mem u.val b d := by
  by_contra! h
  set K := #((Dictionary.dom s).erase u)
  have hK_le : K ≤ n_max := (Finset.card_erase_le).trans hinv.card_dom_le
  have h8 : 8 * n_max ≤ 2 ^ tableLog n_max := eight_mul_le_tableSize n_max
  have h8' : 8 ≤ 2 ^ tableLog n_max := eight_le_tableSize n_max
  have hd_le : K + 1 ≤ 2 ^ tableLog n_max := by omega
  have hle := hinv.probeContinue_prefix_le u b hd_le (fun i hi => h i (by omega))
  omega

/-- Number of probe steps from `b` before reaching an empty slot or key `u`. -/
@[expose] noncomputable def TableInv.probeLen {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) : ℕ :=
  Nat.find (hinv.exists_not_probeContinue u b)

theorem TableInv.probeLen_congr {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem₁ mem₂ : ℕ → ℕ}
    (h₁ : TableInv U V n_max base θ s mem₁) (h₂ : TableInv U V n_max base θ s mem₂)
    (hmem : mem₁ = mem₂) (u : Fin U) (b : Fin (2 ^ tableLog n_max)) :
    h₁.probeLen u b = h₂.probeLen u b := by
  subst hmem
  rfl

theorem TableInv.probeLen_le_card_erase {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) :
    hinv.probeLen u b ≤ #((Dictionary.dom s).erase u) :=
  (Nat.find_spec (hinv.exists_not_probeContinue u b)).1

theorem TableInv.probeLen_le_n_max {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) :
    hinv.probeLen u b ≤ n_max :=
  (hinv.probeLen_le_card_erase u b).trans (Finset.card_erase_le.trans hinv.card_dom_le)

theorem TableInv.probeLen_lt_tableSize {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) :
    hinv.probeLen u b < 2 ^ tableLog n_max :=
  lt_of_le_of_lt (hinv.probeLen_le_n_max u b) (n_max_lt_tableSize n_max)

theorem TableInv.not_probeContinue_probeLen {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) :
    ¬probeContinue base n_max mem u.val b (hinv.probeLen u b) :=
  (Nat.find_spec (hinv.exists_not_probeContinue u b)).2

theorem TableInv.probeContinue_of_lt_probeLen {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) {d : ℕ} (hd : d < hinv.probeLen u b) :
    probeContinue base n_max mem u.val b d := by
  by_contra hnot
  exact Nat.find_min (hinv.exists_not_probeContinue u b) hd
    ⟨(le_of_lt hd).trans (hinv.probeLen_le_card_erase u b), hnot⟩

/-- Exact characterization of the stopping slot `p = probeSlot M (hashFn U n_max θ u) t` where
`t = hinv.probeLen u (hashFn U n_max θ u)`:
- if `usedAt p = 0`, then `s u = none`;
- if `usedAt p = 1`, then `keyAt p = u.val` and `s u = some (valAt p)`. -/
theorem TableInv.probeStop_spec {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) :
    let b := hashFn U n_max θ u
    let t := hinv.probeLen u b
    let p := probeSlot (tableLog n_max) b t
    (usedAt base n_max mem p = 0 ∧ s u = none) ∨
    (usedAt base n_max mem p = 1 ∧ keyAt base n_max mem p = u.val ∧
      s u = some (valAt base n_max mem p)) := by
  set b := hashFn U n_max θ u
  set t := hinv.probeLen u b
  set p := probeSlot (tableLog n_max) b t
  have hstop := hinv.not_probeContinue_probeLen u b
  rcases hinv.used_bit p with hp0 | hp1
  · left
    refine ⟨hp0, ?_⟩
    by_contra! hne
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨k, hk_lt, hk_used, hk_key, _, hk_pref⟩ := hinv.present_slot u v hv
    rcases lt_trichotomy k t with hlt | rfl | hgt
    · have hcont := hinv.probeContinue_of_lt_probeLen u b hlt
      exact hcont.2 hk_key
    · exact absurd hp0 (by rw [hk_used]; decide)
    · have hused_t := hk_pref t hgt
      exact absurd hp0 (by rw [hused_t]; decide)
  · right
    have hkey : keyAt base n_max mem p = u.val := by
      dsimp only [probeContinue, p] at hstop
      tauto
    exact ⟨hp1, hkey, hinv.occupied_state p u hp1 hkey⟩

/-- If a slot `p` has `usedAt p = 1` and `keyAt p = u.val`, then `p` is the stopping slot
`probeSlot M (hashFn U n_max θ u) (hinv.probeLen u (hashFn U n_max θ u))`. -/
theorem TableInv.eq_probeStop_of_key_eq {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) {p : Fin (2 ^ tableLog n_max)}
    (hp1 : usedAt base n_max mem p = 1) (hkey : keyAt base n_max mem p = u.val) :
    p = probeSlot (tableLog n_max) (hashFn U n_max θ u)
      (hinv.probeLen u (hashFn U n_max θ u)) := by
  have hst := hinv.occupied_state p u hp1 hkey
  rcases hinv.probeStop_spec u with ⟨_, hnone⟩ | ⟨hstop1, hstop_key, _⟩
  · rw [hnone] at hst
    cases hst
  · exact hinv.occupied_inj p _ hp1 hstop1 (hkey.trans hstop_key.symm)

/-- Zeroed occupancy array `∀ p, usedAt base n_max mem p = 0` satisfies `TableInv` for
`Dictionary.empty U`. -/
theorem tableInv_empty (U V n_max base : ℕ) (θ : Seed U n_max) {mem : ℕ → ℕ}
    (hzero : ∀ p : Fin (2 ^ tableLog n_max), usedAt base n_max mem p = 0) :
    TableInv U V n_max base θ (Dictionary.empty U) mem where
  card_dom_le := by simp [Dictionary.dom_empty]
  values_bounded := Dictionary.valuesBounded_empty U V
  used_bit p := Or.inl (hzero p)
  occupied_key_lt p hp := by rw [hzero p] at hp; cases hp
  occupied_state p _ hp _ := by rw [hzero p] at hp; cases hp
  occupied_inj p₁ _ hp₁ _ _ := by rw [hzero p₁] at hp₁; cases hp₁
  present_slot _ _ h := by simp [Dictionary.empty] at h
  occupied_prefix p _ hp _ := by rw [hzero p] at hp; cases hp

/-- Memory update performed by `insert u v` once the stopping slot `p` has been located:
writes `used[p] ← 1`, `key[p] ← u`, and `val[p] ← v`. -/
@[expose] def insertMem (base n_max : ℕ) (mem : ℕ → ℕ)
    (p : Fin (2 ^ tableLog n_max)) (u v : ℕ) : ℕ → ℕ :=
  Function.update
    (Function.update
      (Function.update mem (usedBase base n_max + p.val) 1)
      (keyBase base n_max + p.val) u)
    (valBase base n_max + p.val) v

theorem usedAt_insertMem (base n_max : ℕ) (mem : ℕ → ℕ)
    (p q : Fin (2 ^ tableLog n_max)) (u v : ℕ) :
    usedAt base n_max (insertMem base n_max mem p u v) q =
      if q = p then 1 else usedAt base n_max mem q := by
  dsimp only [usedAt, insertMem, usedBase, keyBase, valBase, tableSize]
  have hp := p.isLt
  have hq := q.isLt
  have hne1 : base + KWise.space n_max 5 + q.val ≠
      base + KWise.space n_max 5 + 2 ^ tableLog n_max + 2 ^ tableLog n_max + p.val := by omega
  have hne2 : base + KWise.space n_max 5 + q.val ≠
      base + KWise.space n_max 5 + 2 ^ tableLog n_max + p.val := by omega
  rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
  by_cases hqp : q = p
  · subst hqp
    simp
  · have hval_ne : q.val ≠ p.val := fun h => hqp (Fin.ext h)
    rw [ite_eq_right_iff.mpr (fun h => absurd h hqp), Function.update_of_ne (by omega)]

theorem keyAt_insertMem (base n_max : ℕ) (mem : ℕ → ℕ)
    (p q : Fin (2 ^ tableLog n_max)) (u v : ℕ) :
    keyAt base n_max (insertMem base n_max mem p u v) q =
      if q = p then u else keyAt base n_max mem q := by
  dsimp only [keyAt, insertMem, usedBase, keyBase, valBase, tableSize]
  have hp := p.isLt
  have hq := q.isLt
  have hne1 : base + KWise.space n_max 5 + 2 ^ tableLog n_max + q.val ≠
      base + KWise.space n_max 5 + 2 ^ tableLog n_max + 2 ^ tableLog n_max + p.val := by omega
  have hne2 : base + KWise.space n_max 5 + 2 ^ tableLog n_max + q.val ≠
      base + KWise.space n_max 5 + p.val := by omega
  rw [Function.update_of_ne hne1]
  by_cases hqp : q = p
  · subst hqp
    simp
  · have hval_ne : q.val ≠ p.val := fun h => hqp (Fin.ext h)
    rw [ite_eq_right_iff.mpr (fun h => absurd h hqp),
      Function.update_of_ne (by omega), Function.update_of_ne hne2]

theorem valAt_insertMem (base n_max : ℕ) (mem : ℕ → ℕ)
    (p q : Fin (2 ^ tableLog n_max)) (u v : ℕ) :
    valAt base n_max (insertMem base n_max mem p u v) q =
      if q = p then v else valAt base n_max mem q := by
  dsimp only [valAt, insertMem, usedBase, keyBase, valBase, tableSize]
  have hp := p.isLt
  have hq := q.isLt
  have hne1 : base + KWise.space n_max 5 + 2 ^ tableLog n_max + 2 ^ tableLog n_max + q.val ≠
      base + KWise.space n_max 5 + 2 ^ tableLog n_max + p.val := by omega
  have hne2 : base + KWise.space n_max 5 + 2 ^ tableLog n_max + 2 ^ tableLog n_max + q.val ≠
      base + KWise.space n_max 5 + p.val := by omega
  by_cases hqp : q = p
  · subst hqp
    simp
  · have hval_ne : q.val ≠ p.val := fun h => hqp (Fin.ext h)
    rw [ite_eq_right_iff.mpr (fun h => absurd h hqp), Function.update_of_ne (by omega),
      Function.update_of_ne hne1, Function.update_of_ne hne2]

/-- Writing `(1, u.val, v)` at the stopping slot `p = probeSlot M (hashFn U n_max θ u) t`
preserves `TableInv` for `Function.update s u (some v)` whenever `.insert u v` is admissible. -/
theorem TableInv.insert_mem {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (v : ℕ) (hvalid : (Dictionary.spec U V n_max).valid s (.insert u v)) :
    let b := hashFn U n_max θ u
    let t := hinv.probeLen u b
    let p := probeSlot (tableLog n_max) b t
    TableInv U V n_max base θ (Function.update s u (some v))
      (insertMem base n_max mem p u.val v) := by
  set b := hashFn U n_max θ u
  set t := hinv.probeLen u b
  set p := probeSlot (tableLog n_max) b t
  set mem' := insertMem base n_max mem p u.val v
  have ht_lt : t < 2 ^ tableLog n_max := hinv.probeLen_lt_tableSize u b
  have hstop_spec := hinv.probeStop_spec u
  have hused_ge : ∀ q, usedAt base n_max mem q = 1 → usedAt base n_max mem' q = 1 := by
    intro q hq
    rw [usedAt_insertMem]
    split_ifs <;> [rfl; exact hq]
  have hkey_ne_u : ∀ q, q ≠ p → usedAt base n_max mem q = 1 →
      keyAt base n_max mem q ≠ u.val := by
    intro q hne hq heq
    exact hne (hinv.eq_probeStop_of_key_eq u hq heq)
  refine
    { card_dom_le := Dictionary.card_dom_step_le_of_valid hinv.card_dom_le (o := .insert u v) hvalid
      values_bounded :=
        Dictionary.valuesBounded_step_of_valid hinv.values_bounded (o := .insert u v) hvalid
      used_bit := fun q => by
        rw [usedAt_insertMem]
        split_ifs
        · exact Or.inr rfl
        · exact hinv.used_bit q
      occupied_key_lt := fun q hq => by
        rw [keyAt_insertMem]
        rw [usedAt_insertMem] at hq
        split_ifs at hq ⊢ with hqp
        · exact u.isLt
        · exact hinv.occupied_key_lt q hq
      occupied_state := fun q u' hq hkey => by
        change usedAt base n_max (insertMem base n_max mem p u.val v) q = 1 at hq
        change keyAt base n_max (insertMem base n_max mem p u.val v) q = u'.val at hkey
        change Function.update s u (some v) u' =
          some (valAt base n_max (insertMem base n_max mem p u.val v) q)
        rw [usedAt_insertMem] at hq
        rw [keyAt_insertMem] at hkey
        rw [valAt_insertMem]
        by_cases hqp : q = p
        · simp only [hqp, ↓reduceIte] at hkey ⊢
          have hu' : u' = u := Fin.ext hkey.symm
          simp [hu']
        · simp only [hqp, ↓reduceIte] at hq hkey ⊢
          have hne_u := hkey_ne_u q hqp hq
          have hu' : u' ≠ u := fun h => hne_u (hkey.trans (congrArg Fin.val h))
          rw [Function.update_of_ne hu']
          exact hinv.occupied_state q u' hq hkey
      occupied_inj := fun q₁ q₂ hq₁ hq₂ hkey => by
        change usedAt base n_max (insertMem base n_max mem p u.val v) q₁ = 1 at hq₁
        change usedAt base n_max (insertMem base n_max mem p u.val v) q₂ = 1 at hq₂
        change keyAt base n_max (insertMem base n_max mem p u.val v) q₁ =
          keyAt base n_max (insertMem base n_max mem p u.val v) q₂ at hkey
        rw [usedAt_insertMem] at hq₁ hq₂
        rw [keyAt_insertMem, keyAt_insertMem] at hkey
        by_cases h1 : q₁ = p <;> by_cases h2 : q₂ = p
        · rw [h1, h2]
        · simp only [h1, h2, ↓reduceIte] at hq₂ hkey
          exact absurd hkey.symm (hkey_ne_u q₂ h2 hq₂)
        · simp only [h1, h2, ↓reduceIte] at hq₁ hkey
          exact absurd hkey (hkey_ne_u q₁ h1 hq₁)
        · simp only [h1, h2, ↓reduceIte] at hq₁ hq₂ hkey
          exact hinv.occupied_inj q₁ q₂ hq₁ hq₂ hkey
      present_slot := fun u' v' hst' => by
        by_cases hu' : u' = u
        · subst hu'
          rw [Function.update_self, Option.some.injEq] at hst'
          subst hst'
          refine ⟨t, ht_lt, ?_, ?_, ?_, ?_⟩
          · change usedAt base n_max (insertMem base n_max mem p u'.val v) p = 1
            rw [usedAt_insertMem]
            simp
          · change keyAt base n_max (insertMem base n_max mem p u'.val v) p = u'.val
            rw [keyAt_insertMem]
            simp
          · change valAt base n_max (insertMem base n_max mem p u'.val v) p = v
            rw [valAt_insertMem]
            simp
          · intro j hj
            exact hused_ge _ (hinv.probeContinue_of_lt_probeLen u' b hj).1
        · rw [Function.update_of_ne hu'] at hst'
          obtain ⟨k, hk_lt, hk_used, hk_key, hk_val, hk_pref⟩ := hinv.present_slot u' v' hst'
          set q := probeSlot (tableLog n_max) (hashFn U n_max θ u') k
          have hqp : q ≠ p := by
            intro heq
            rcases hstop_spec with ⟨hp0, _⟩ | ⟨_, hp_key, _⟩
            · rw [heq, hp0] at hk_used
              cases hk_used
            · rw [heq, hp_key] at hk_key
              exact hu' (Fin.ext hk_key.symm)
          refine ⟨k, hk_lt, hused_ge q hk_used, ?_, ?_, fun j hj => hused_ge _ (hk_pref j hj)⟩
          · change keyAt base n_max (insertMem base n_max mem p u.val v) q = u'.val
            rw [keyAt_insertMem]
            simp [hqp, hk_key]
          · change valAt base n_max (insertMem base n_max mem p u.val v) q = v'
            rw [valAt_insertMem]
            simp [hqp, hk_val]
      occupied_prefix := fun q u' hq hkey => by
        change usedAt base n_max (insertMem base n_max mem p u.val v) q = 1 at hq
        change keyAt base n_max (insertMem base n_max mem p u.val v) q = u'.val at hkey
        rw [usedAt_insertMem] at hq
        rw [keyAt_insertMem] at hkey
        by_cases hqp : q = p
        · simp only [hqp, ↓reduceIte] at hkey
          have hu' : u' = u := Fin.ext hkey.symm
          subst hu'
          exact ⟨t, ht_lt, hqp, fun j hj =>
            hused_ge _ (hinv.probeContinue_of_lt_probeLen u' b hj).1⟩
        · simp only [hqp, ↓reduceIte] at hq hkey
          obtain ⟨k, hk_lt, hk_eq, hk_pref⟩ := hinv.occupied_prefix q u' hq hkey
          exact ⟨k, hk_lt, hk_eq, fun j hj => hused_ge _ (hk_pref j hj)⟩ }

private theorem probeSlot_backSlot_pred {M : ℕ} (b : Fin (2 ^ M)) (a : ℕ) :
    probeSlot M (backSlot M b a) (2 ^ M - 1) = backSlot M b (a + 1) := by
  apply Fin.ext
  simp only [probeSlot, backSlot, cyclicSlotMod]
  have h1 : 1 ≤ 2 ^ M := Nat.one_le_two_pow
  have ha_le : a ≤ 2 ^ M * (a + 1) := by
    calc a ≤ 1 * (a + 1) := by omega
      _ ≤ 2 ^ M * (a + 1) := Nat.mul_le_mul_right (a + 1) h1
  have hmul : 2 ^ M * (a + 1 + 1) = 2 ^ M * (a + 1) + 2 ^ M := by ring
  rw [Nat.mod_add_mod, hmul]
  congr 1
  omega

private theorem probeSlot_sub_mod {M : ℕ} (o b₀ : Fin (2 ^ M)) :
    probeSlot M o ((b₀.val + 2 ^ M - o.val) % 2 ^ M) = b₀ := by
  apply Fin.ext
  simp only [probeSlot, cyclicSlotMod]
  have ho := o.isLt
  have hb := b₀.isLt
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
    show o.val + (b₀.val + 2 ^ M - o.val) = b₀.val + 2 ^ M by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hb]

private theorem TableInv.backSlot_interval_used_ne {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (a : ℕ)
    (hback : ∀ r, 1 ≤ r → r ≤ a →
      usedAt base n_max mem (backSlot (tableLog n_max) (hashFn U n_max θ u) r) = 1 ∧
      keyAt base n_max mem (backSlot (tableLog n_max) (hashFn U n_max θ u) r) ≠ u.val)
    {idx : ℕ} (hidx : idx < a + hinv.probeLen u (hashFn U n_max θ u)) :
    usedAt base n_max mem
      (probeSlot (tableLog n_max) (backSlot (tableLog n_max) (hashFn U n_max θ u) a) idx) = 1 ∧
    keyAt base n_max mem
      (probeSlot (tableLog n_max) (backSlot (tableLog n_max) (hashFn U n_max θ u) a) idx) ≠
      u.val := by
  by_cases hlt : idx < a
  · rw [probeSlot_backSlot_sub (hashFn U n_max θ u) (by omega)]
    exact hback (a - idx) (by omega) (by omega)
  · have hge : a ≤ idx := le_of_not_gt hlt
    have heq : idx = a + (idx - a) := by omega
    rw [heq, probeSlot_backSlot_add]
    exact hinv.probeContinue_of_lt_probeLen u (hashFn U n_max θ u) (by omega)

/-- **Left-anchored cluster witness theorem**: if probing key `u` from `b = hashFn U n_max θ u`
takes `t = hinv.probeLen u b ≥ 1` steps, there is a contiguous cyclic interval
`cyclicInterval M b a ℓ` (`a < ℓ`, `t ≤ ℓ ≤ #((Dictionary.dom s).erase u)`) into which at least
`ℓ` keys of `(Dictionary.dom s).erase u` hash. -/
theorem TableInv.hasClusterWitness_probeLen {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (ht : 1 ≤ hinv.probeLen u (hashFn U n_max θ u)) :
    ∃ a ℓ, a < ℓ ∧
      hinv.probeLen u (hashFn U n_max θ u) ≤ ℓ ∧
      ℓ ≤ #((Dictionary.dom s).erase u) ∧
      ℓ ≤ #(((Dictionary.dom s).erase u).filter fun x =>
        hashFn U n_max θ x ∈ cyclicInterval (tableLog n_max) (hashFn U n_max θ u) a ℓ) := by
  have ht_le_S : hinv.probeLen u (hashFn U n_max θ u) ≤ #((Dictionary.dom s).erase u) :=
    hinv.probeLen_le_card_erase u (hashFn U n_max θ u)
  have hS_le_n : #((Dictionary.dom s).erase u) ≤ n_max :=
    Finset.card_erase_le.trans hinv.card_dom_le
  have h8n : 8 * n_max ≤ 2 ^ tableLog n_max := eight_mul_le_tableSize n_max
  have h8 : 8 ≤ 2 ^ tableLog n_max := eight_le_tableSize n_max
  have hex_empty : ∃ r, 1 ≤ r ∧
      r ≤ #((Dictionary.dom s).erase u) + 1 - hinv.probeLen u (hashFn U n_max θ u) ∧
      ¬(usedAt base n_max mem (backSlot (tableLog n_max) (hashFn U n_max θ u) r) = 1 ∧
        keyAt base n_max mem (backSlot (tableLog n_max) (hashFn U n_max θ u) r) ≠ u.val) := by
    by_contra! hall
    set a_max := #((Dictionary.dom s).erase u) + 1 - hinv.probeLen u (hashFn U n_max θ u)
    set A := cyclicInterval (tableLog n_max) (hashFn U n_max θ u) a_max
      (#((Dictionary.dom s).erase u) + 1)
    have hcardA : #A = #((Dictionary.dom s).erase u) + 1 :=
      card_cyclicInterval (hashFn U n_max θ u) a_max (by omega)
    have hA_le : #A ≤ #((Dictionary.dom s).erase u) := by
      refine hinv.card_slots_le A ((Dictionary.dom s).erase u) (fun q hq => ?_) (fun q hq => ?_)
      · dsimp only [A] at hq
        rw [cyclicInterval_eq_image_probeSlot] at hq
        obtain ⟨idx, hidx, rfl⟩ := Finset.mem_image.mp hq
        have hidx' : idx < a_max + hinv.probeLen u (hashFn U n_max θ u) := by
          have := Finset.mem_range.mp hidx
          omega
        exact (hinv.backSlot_interval_used_ne u a_max (fun r hr1 hr2 => hall r hr1 hr2) hidx').1
      · dsimp only [A] at hq
        rw [cyclicInterval_eq_image_probeSlot] at hq
        obtain ⟨idx, hidx, rfl⟩ := Finset.mem_image.mp hq
        have hidx' : idx < a_max + hinv.probeLen u (hashFn U n_max θ u) := by
          have := Finset.mem_range.mp hidx
          omega
        have hboth :=
          hinv.backSlot_interval_used_ne u a_max (fun r hr1 hr2 => hall r hr1 hr2) hidx'
        exact hinv.key_mem_erase_of_ne hboth.1 u hboth.2
    omega
  set r₀ := Nat.find hex_empty
  obtain ⟨hr₀_ge, hr₀_le, hr₀_not⟩ := Nat.find_spec hex_empty
  set a := r₀ - 1
  set ℓ := a + hinv.probeLen u (hashFn U n_max θ u)
  have ha1 : a + 1 = r₀ := by omega
  have hℓ_le_S : ℓ ≤ #((Dictionary.dom s).erase u) := by omega
  have hback_occ : ∀ r, 1 ≤ r → r ≤ a →
      usedAt base n_max mem (backSlot (tableLog n_max) (hashFn U n_max θ u) r) = 1 ∧
      keyAt base n_max mem (backSlot (tableLog n_max) (hashFn U n_max θ u) r) ≠ u.val := by
    intro r hr1 hra
    have hr_lt : r < r₀ := by omega
    have hmin := Nat.find_min hex_empty hr_lt
    push Not at hmin
    exact hmin hr1 (by omega)
  have hprev_zero :
      usedAt base n_max mem (backSlot (tableLog n_max) (hashFn U n_max θ u) (a + 1)) = 0 := by
    rcases hinv.used_bit (backSlot (tableLog n_max) (hashFn U n_max θ u) (a + 1)) with h0 | h1
    · exact h0
    · exfalso
      have hkey_u :
          keyAt base n_max mem (backSlot (tableLog n_max) (hashFn U n_max θ u) (a + 1)) =
            u.val := by
        rw [ha1] at h1 ⊢
        tauto
      have heq_stop := hinv.eq_probeStop_of_key_eq u h1 hkey_u
      have h0_eq :
          backSlot (tableLog n_max) (hashFn U n_max θ u) (a + 1) =
            probeSlot (tableLog n_max) (backSlot (tableLog n_max) (hashFn U n_max θ u) (a + 1)) 0 :=
        (probeSlot_zero _).symm
      have ht_eq :
          probeSlot (tableLog n_max) (hashFn U n_max θ u) (hinv.probeLen u (hashFn U n_max θ u)) =
            probeSlot (tableLog n_max) (backSlot (tableLog n_max) (hashFn U n_max θ u) (a + 1))
              (a + 1 + hinv.probeLen u (hashFn U n_max θ u)) :=
        (probeSlot_backSlot_add (hashFn U n_max θ u) (a + 1) _).symm
      rw [h0_eq, ht_eq] at heq_stop
      have hinj := probeSlot_injOn_range
        (backSlot (tableLog n_max) (hashFn U n_max θ u) (a + 1))
        (len := 2 ^ tableLog n_max) le_rfl
        (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)))
        (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) heq_stop
      omega
  refine ⟨a, ℓ, by omega, by omega, hℓ_le_S, ?_⟩
  set J := cyclicInterval (tableLog n_max) (hashFn U n_max θ u) a ℓ
  have hcardJ : #J = ℓ := card_cyclicInterval (hashFn U n_max θ u) a (by omega)
  rw [← hcardJ]
  have hJ_occ : ∀ q ∈ J, usedAt base n_max mem q = 1 ∧ keyAt base n_max mem q ≠ u.val := by
    intro q hq
    dsimp only [J] at hq
    rw [cyclicInterval_eq_image_probeSlot] at hq
    obtain ⟨idx, hidx, rfl⟩ := Finset.mem_image.mp hq
    exact hinv.backSlot_interval_used_ne u a hback_occ (Finset.mem_range.mp hidx)
  refine hinv.card_slots_le J (((Dictionary.dom s).erase u).filter fun x => hashFn U n_max θ x ∈ J)
    (fun q hq => (hJ_occ q hq).1) (fun q hq => ?_)
  rw [Finset.mem_filter]
  refine ⟨hinv.key_mem_erase_of_ne (hJ_occ q hq).1 u (hJ_occ q hq).2, ?_⟩
  set x_q : Fin U := ⟨keyAt base n_max mem q, hinv.occupied_key_lt q (hJ_occ q hq).1⟩
  obtain ⟨k, hk_lt, hq_eq, hk_pref⟩ := hinv.occupied_prefix q x_q (hJ_occ q hq).1 rfl
  set b₀ := hashFn U n_max θ x_q
  set o := backSlot (tableLog n_max) (hashFn U n_max θ u) a
  have hq_mem : q ∈ J := hq
  dsimp only [J] at hq_mem
  rw [cyclicInterval_eq_image_probeSlot] at hq_mem
  obtain ⟨idx, hidx_mem, hq_idx⟩ := Finset.mem_image.mp hq_mem
  have hidx_lt : idx < ℓ := Finset.mem_range.mp hidx_mem
  set r := (b₀.val + 2 ^ tableLog n_max - o.val) % 2 ^ tableLog n_max
  have hr_lt : r < 2 ^ tableLog n_max := Nat.mod_lt _ (by positivity)
  have hb₀_eq : probeSlot (tableLog n_max) o r = b₀ := probeSlot_sub_mod o b₀
  by_cases hr_lt_ℓ : r < ℓ
  · dsimp only [J]
    rw [cyclicInterval_eq_image_probeSlot, Finset.mem_image]
    exact ⟨r, Finset.mem_range.mpr hr_lt_ℓ, hb₀_eq⟩
  · exfalso
    have hq_rk : q = probeSlot (tableLog n_max) o ((r + k) % 2 ^ tableLog n_max) := by
      rw [hq_eq, ← hb₀_eq, probeSlot_add]
      apply Fin.ext
      simp [probeSlot, cyclicSlotMod]
    have hrk_eq_idx : (r + k) % 2 ^ tableLog n_max = idx := by
      refine probeSlot_injOn_range o (len := 2 ^ tableLog n_max) le_rfl
        (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))))
        (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) ?_
      rw [← hq_rk, hq_idx]
    have hge : 2 ^ tableLog n_max ≤ r + k := by
      by_contra hlt
      have hmod0 : (r + k) % 2 ^ tableLog n_max = r + k := Nat.mod_eq_of_lt (not_le.mp hlt)
      omega
    have hmod : (r + k) % 2 ^ tableLog n_max = r + k - 2 ^ tableLog n_max := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    have hrk_sum : r + k = 2 ^ tableLog n_max + idx := by omega
    set j := 2 ^ tableLog n_max - 1 - r
    have hj_lt_k : j < k := by omega
    have hused_j := hk_pref j hj_lt_k
    have hslot_j : probeSlot (tableLog n_max) b₀ j =
        backSlot (tableLog n_max) (hashFn U n_max θ u) (a + 1) := by
      rw [← hb₀_eq, probeSlot_add, show r + j = 2 ^ tableLog n_max - 1 by omega]
      exact probeSlot_backSlot_pred (hashFn U n_max θ u) a
    rw [hslot_j, hprev_zero] at hused_j
    cases hused_j

noncomputable instance instDecidablePredHasClusterWitness (U n_max : ℕ) (S : Finset (Fin U))
    (u : Fin U) (θ : Seed U n_max) :
    DecidablePred (HasClusterWitness (hashFn U n_max) S u θ) :=
  Classical.decPred _

/-- Maximum `t ≤ #S` satisfying `HasClusterWitness (hashFn U n_max) S u θ t` (depends only on
`θ`). -/
@[expose] noncomputable def maxWitnessProbe (U n_max : ℕ) (S : Finset (Fin U)) (u : Fin U)
    (θ : Seed U n_max) : ℕ :=
  have h0 : 0 ∈ (Finset.range (#S + 1)).filter (HasClusterWitness (hashFn U n_max) S u θ) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), fun h => by omega⟩
  ((Finset.range (#S + 1)).filter (HasClusterWitness (hashFn U n_max) S u θ)).max' ⟨0, h0⟩

theorem le_maxWitnessProbe {U n_max : ℕ} {S : Finset (Fin U)} {u : Fin U}
    {θ : Seed U n_max} {t : ℕ} (ht_le : t ≤ #S)
    (hwit : HasClusterWitness (hashFn U n_max) S u θ t) :
    t ≤ maxWitnessProbe U n_max S u θ := by
  dsimp only [maxWitnessProbe]
  exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hwit⟩)

theorem hasClusterWitness_maxWitnessProbe (U n_max : ℕ) (S : Finset (Fin U)) (u : Fin U)
    (θ : Seed U n_max) :
    HasClusterWitness (hashFn U n_max) S u θ (maxWitnessProbe U n_max S u θ) := by
  dsimp only [maxWitnessProbe]
  exact (Finset.mem_filter.mp (Finset.max'_mem _ _)).2

/-- For any coupled state distribution `ν : PMF (Seed U n_max × α)` whose seed marginal is bounded
by `seedLaw U n_max`, any step counter `T_probe : Seed U n_max × α → ℕ` bounded by `hinv.probeLen`
on `ν.support` has expected value at most `288`. -/
theorem tsum_probeLen_le {α : Type*} {U V n_max base : ℕ}
    {s : Dictionary.State U}
    (u : Fin U) (ν : PMF (Seed U n_max × α))
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ seedLaw U n_max θ)
    (T_probe : Seed U n_max × α → ℕ)
    (hT : ∀ p ∈ ν.support, ∃ (mem : ℕ → ℕ) (hinv : TableInv U V n_max base p.1 s mem),
      T_probe p ≤ hinv.probeLen u (hashFn U n_max p.1 u)) :
    (∑' p, ν p * (T_probe p : ℝ≥0∞)) ≤ 288 := by
  obtain ⟨p₀, hp₀⟩ := ν.support_nonempty
  obtain ⟨_, hinv₀, _⟩ := hT p₀ hp₀
  have hdom_le : (Dictionary.dom s).card ≤ n_max := hinv₀.card_dom_le
  set S := (Dictionary.dom s).erase u
  have hu : u ∉ S := Finset.notMem_erase u _
  have hS : #S ≤ n_max := Finset.card_erase_le.trans hdom_le
  have hM : 8 * n_max ≤ 2 ^ tableLog n_max := eight_mul_le_tableSize n_max
  have hh := isKWiseIndependentHash_hashFn U n_max
  have hpt : ∀ p, ν p * (T_probe p : ℝ≥0∞) ≤
      ν p * (maxWitnessProbe U n_max S u p.1 : ℝ≥0∞) := by
    intro p
    by_cases hp : p ∈ ν.support
    · obtain ⟨mem, hinv, hle⟩ := hT p hp
      have hwit_p : HasClusterWitness (hashFn U n_max) S u p.1
          (hinv.probeLen u (hashFn U n_max p.1 u)) :=
        fun ht => hinv.hasClusterWitness_probeLen u ht
      have hle_max := le_maxWitnessProbe
        (hinv.probeLen_le_card_erase u (hashFn U n_max p.1 u)) hwit_p
      gcongr
      exact hle.trans hle_max
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hp, zero_mul, zero_mul]
  calc (∑' p, ν p * (T_probe p : ℝ≥0∞))
      ≤ ∑' p, ν p * (maxWitnessProbe U n_max S u p.1 : ℝ≥0∞) :=
        tsum_le_tsum hpt
    _ = ∑' θ, (ν.map Prod.fst) θ * (maxWitnessProbe U n_max S u θ : ℝ≥0∞) :=
        (Cslib.Probability.PMF.tsum_map_mul ν Prod.fst
          (fun θ => (maxWitnessProbe U n_max S u θ : ℝ≥0∞))).symm
    _ ≤ ∑' θ, seedLaw U n_max θ * (maxWitnessProbe U n_max S u θ : ℝ≥0∞) :=
        tsum_le_tsum (fun θ => mul_le_mul_of_nonneg_right (hseed θ) zero_le)
    _ ≤ 288 :=
        tsum_uniform_probe_le_of_cluster_witness hh S hu hS hM
          (maxWitnessProbe U n_max S u) (hasClusterWitness_maxWitnessProbe U n_max S u)

/-! ## Section 3: Word-RAM register layout, programs, and operational execution -/

open Cslib.Algorithms.WordRAM.Hashing.Tabulation

/-- Total number of registers used by the linear-probing subroutine (`0 .. 17` for `KWise` and
probe scratch, `18 .. 23` for allocation, zero-fill, and operation arguments). -/
abbrev rLP : ℕ := 24

/-- Register embedding `Fin 18 → Fin 24` mapping `KWise` registers `0 .. 17` to `0 .. 17`. -/
@[expose] def kwiseMap : Fin 18 → Fin 24 :=
  Fin.castLE (by decide)

theorem injective_kwiseMap : Function.Injective kwiseMap :=
  Fin.castLE_injective (by decide)

/-- Allocation span program: copies `frontierReg` (`18`) to `baseReg` (`0`) and advances
`frontierReg` by `space n_max`. -/
@[expose] def allocSpan (n_max : ℕ) : Code .exact 24 :=
  .seq (.op (.copy 0 18))
  (.seq (.op (.const 3 (space n_max)))
        (.op (.exactBin .add 18 0 3)))

/-- `18`-register initialization program setting `(n_max, U, tableLog n_max)` in registers
`1, 2, 3` and invoking `KWise.initCode 5`. -/
@[expose] def initSetup18 (U n_max : ℕ) : Code .exact 18 :=
  .seq (.op (.const 1 n_max))
  (.seq (.op (.const 2 U))
  (.seq (.op (.const 3 (tableLog n_max)))
        (KWise.initCode 5)))

/-- `24`-register initialization program. -/
@[expose] def initSetup (U n_max : ℕ) : Code .exact 24 :=
  (initSetup18 U n_max).rename kwiseMap

/-- Single-slot probe inspection program: given current slot `pos` in `reg 2`, loads
`used[pos]` into `reg 9` (`cellReg`) and sets `reg 7` (`contReg`) to `1` if
`used[pos] = 1 ∧ key[pos] ≠ u.val`, or `0` otherwise. -/
@[expose] def probeCheckCode : Code .exact 24 :=
  .seq (.op (.exactBin .add 8 4 2))
  (.seq (.op (.load 9 8))
        (.branch (.eq 9 10)
          (.seq (.op (.exactBin .add 8 5 2))
          (.seq (.op (.load 8 8))
                (.branch (.eq 8 1)
                  (.op (.const 7 0))
                  (.op (.const 7 1)))))
          (.op (.const 7 0))))

/-- Probe setup program: initializes `maskReg` (`3`), `usedBaseReg` (`4`), `keyBaseReg` (`5`),
`valBaseReg` (`6`), and `cOneReg` (`10`), then inspects the home slot `pos = (h u).val` (`reg 2`).
-/
@[expose] def probeSetupCode (n_max : ℕ) : Code .exact 24 :=
  .seq (.op (.const 3 (tableSize n_max - 1)))
  (.seq (.op (.const 4 (KWise.space n_max 5)))
  (.seq (.op (.exactBin .add 4 0 4))
  (.seq (.op (.const 5 (tableSize n_max)))
  (.seq (.op (.exactBin .add 5 4 5))
  (.seq (.op (.const 6 (tableSize n_max)))
  (.seq (.op (.exactBin .add 6 5 6))
  (.seq (.op (.const 10 1))
        probeCheckCode)))))))

/-- Probe loop body: advances `pos ← (pos + 1) &&& (2 ^ M - 1)` in `reg 2` and inspects the new
slot via `probeCheckCode`. -/
@[expose] def probeBody : Code .exact 24 :=
  .seq (.op (.exactBin .add 2 2 10))
  (.seq (.op (.exactBin .and 2 2 3))
        probeCheckCode)

/-- Linear probe loop `while contReg == 1 do probeBody`. -/
@[expose] def probeLoop : Code .exact 24 :=
  .loop (.eq 7 10) probeBody

/-- Insertion suffix after `probeLoop` halts at slot `pos` (`reg 2`): stores `used[pos] ← 1`,
`key[pos] ← u.val` (`reg 1`), `val[pos] ← v` (`reg 23`), and sets `outReg` (`reg 2`) to `0`. -/
@[expose] def insertFinishCode : Code .exact 24 :=
  .seq (.op (.exactBin .add 8 4 2))
  (.seq (.op (.store 8 10))
  (.seq (.op (.exactBin .add 8 5 2))
  (.seq (.op (.store 8 1))
  (.seq (.op (.exactBin .add 8 6 2))
  (.seq (.op (.store 8 23))
        (.op (.const 2 0)))))))

/-- Lookup suffix after `probeLoop` halts at slot `pos` (`reg 2`) with `used[pos]` in `reg 9`:
if `reg 9 == 1`, loads `val[pos]` and writes `val[pos] + 1` into `reg 2`; otherwise writes `0`
into `reg 2`. -/
@[expose] def getFinishCode : Code .exact 24 :=
  .branch (.eq 9 10)
    (.seq (.op (.exactBin .add 8 6 2))
    (.seq (.op (.load 2 8))
          (.op (.exactBin .add 2 2 10))))
    (.op (.const 2 0))

/-- Unified operation program for `get u` (`opReg = 0`) and `insert u v` (`opReg = 1`). -/
@[expose] def opCode (n_max : ℕ) : Code .exact 24 :=
  .seq ((KWise.evalCode 5).rename kwiseMap)
  (.seq (probeSetupCode n_max)
  (.seq probeLoop
        (.branch (.eq 22 10) insertFinishCode getFinishCode)))

/-- `SubroutineCode` bundle for linear probing. -/
@[expose] def subroutineCode (U n_max : ℕ) : SubroutineCode .exact rLP 0 where
  allocSpan := allocSpan n_max
  initSetup := initSetup U n_max
  code := opCode n_max
  baseReg := 0
  frontierReg := 18
  zeroReg := 19
  oneReg := 20
  curReg := 21
  incCur := .exactBin .add 21 21 20
  initParams := Fin.elim0
  input i := decide (i = 1 ∨ i = 22 ∨ i = 23)
  output := 2

/-- Standalone argument encoding for `Dictionary.Op U`. -/
@[expose] def encodeOp {U : ℕ} (o : Dictionary.Op U) (i : Fin rLP) : ℕ :=
  match o with
  | .get u =>
    if i = 1 then u.val else 0
  | .insert u v =>
    if i = 1 then u.val else if i = 22 then 1 else if i = 23 then v else 0

/-- Argument-matching predicate for `Dictionary.Op U`. -/
@[expose] def argMatchOp {U : ℕ} (o : Dictionary.Op U) (regs : Fin rLP → ℕ) : Prop :=
  match o with
  | .get u => regs 1 = u.val ∧ regs 22 = 0
  | .insert u v => regs 1 = u.val ∧ regs 22 = 1 ∧ regs 23 = v

/-- Output decoder for `Dictionary.Op U`: for `get u`, `0` decodes to `none` and `k + 1` decodes to
`some k`; for `insert u v`, decodes to `some ()`. -/
@[expose] def decodeOp {U V n_max : ℕ} (o : (Dictionary.spec U V n_max).Op)
    (regs : Fin rLP → ℕ) : Option ((Dictionary.spec U V n_max).Result o) :=
  match o with
  | .get _ => some (if regs 2 = 0 then none else some (regs 2 - 1))
  | .insert _ _ => some ()

/-- Expected instruction count for `initSetup U n_max`:
`KWise.initTableSteps n_max U (tableLog n_max) + 38 = O(n_max + log U)`. -/
@[expose] def setupTime (U n_max : ℕ) : ℕ :=
  KWise.initTableSteps n_max U (tableLog n_max) + 38

/-- Expected instruction charge per dictionary operation:
`KWise.evalSteps n_max U (tableLog n_max) 5 + 3483 = O(L ^ 2 + 1)`. -/
@[expose] def charge (U n_max : ℕ) : ℕ :=
  KWise.evalSteps n_max U (tableLog n_max) 5 + 12 * 288 + 27

/-- Full seed-coupled representation invariant `Rep U V n_max w base θ s x` for linear probing. -/
structure Rep (U V n_max w base : ℕ) (θ : Seed U n_max) (s : Dictionary.State U)
    (x : Data rLP) : Prop where
  /-- Machine configuration is word-bounded at width `w`. -/
  bounded : x.Bounded w
  /-- Persistent base register `reg 0` holds `base`. -/
  reg_base : x.regs 0 = base
  /-- Embedded `5`-wise independent hash representation at `[base, base + KWise.space n_max 5)`. -/
  kwise_rep : KWise.Rep base (KWise.chunkBits n_max) U (tableLog n_max) 5 θ x.mem
  /-- Open-addressed linear-probing table invariant at `[usedBase, valBase + tableSize n_max)`. -/
  table_inv : TableInv U V n_max base θ s x.mem

theorem Rep.unique {U V n_max w base : ℕ} {θ : Seed U n_max}
    {s₁ s₂ : Dictionary.State U} {x : Data rLP}
    (h₁ : Rep U V n_max w base θ s₁ x) (h₂ : Rep U V n_max w base θ s₂ x) :
    s₁ = s₂ := by
  funext u
  rcases h₁.table_inv.probeStop_spec u with ⟨hp0, hnone₁⟩ | ⟨hp1, hkey₁, hsome₁⟩
  · rcases h₂.table_inv.probeStop_spec u with ⟨_, hnone₂⟩ | ⟨hp1', hkey₂, _⟩
    · rw [hnone₁, hnone₂]
    · have heq := h₁.table_inv.eq_probeStop_of_key_eq u hp1' hkey₂
      rw [← heq, hp1'] at hp0
      cases hp0
  · rcases h₂.table_inv.probeStop_spec u with ⟨hp0', _⟩ | ⟨hp1', hkey₂, hsome₂⟩
    · have heq := h₂.table_inv.eq_probeStop_of_key_eq u hp1 hkey₁
      rw [← heq, hp1] at hp0'
      cases hp0'
    · have heq := h₁.table_inv.occupied_inj _ _ hp1 hp1' (hkey₁.trans hkey₂.symm)
      rw [hsome₁, hsome₂, heq]

/-- `KWise.Rep` depends only on addresses in `[base, base + KWise.space n_max 5)`. -/
private theorem kwise_rep_congr {U n_max base : ℕ} {θ : Seed U n_max} {mem mem' : ℕ → ℕ}
    (hrep : KWise.Rep base (KWise.chunkBits n_max) U (tableLog n_max) 5 θ mem)
    (heq : ∀ a, a < base + KWise.space n_max 5 → base ≤ a → mem' a = mem a) :
    KWise.Rep base (KWise.chunkBits n_max) U (tableLog n_max) 5 θ mem' := by
  have hk_mem : ∀ offset < KWise.space n_max 5, mem' (base + offset) = mem (base + offset) :=
    fun offset hlt => heq (base + offset) (by omega) (Nat.le_add_right _ _)
  have hsp : KWise.space n_max 5 = 8 + 5 + 2 ^ (2 * KWise.chunkBits n_max) := rfl
  have hpow_pos : 0 < 2 ^ (2 * KWise.chunkBits n_max) := by positivity
  rcases hrep with ⟨htab, hseed⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have := hk_mem 0 (by omega); rw [Nat.add_zero] at this; rw [this]; exact htab.1
  · rw [hk_mem 1 (by omega)]; exact htab.2.1
  · rw [hk_mem 2 (by omega)]; exact htab.2.2.1
  · rw [hk_mem 3 (by omega)]; exact htab.2.2.2.1
  · rw [hk_mem 4 (by omega)]; exact htab.2.2.2.2.1
  · rw [hk_mem 5 (by omega)]; exact htab.2.2.2.2.2.1
  · rw [hk_mem 6 (by omega)]; exact htab.2.2.2.2.2.2.1
  · rw [hk_mem 7 (by omega)]; exact htab.2.2.2.2.2.2.2.1
  · intro idx hidx
    have h1 : base + 8 + 5 + idx = base + (8 + 5 + idx) := by omega
    rw [h1, hk_mem (8 + 5 + idx) (by omega), ← h1]
    exact htab.2.2.2.2.2.2.2.2 idx hidx
  · intro j
    have hj := j.isLt
    have h1 : base + 8 + j.val = base + (8 + j.val) := by omega
    rw [h1, hk_mem (8 + j.val) (by omega), ← h1]
    exact hseed j

/-- `TableInv` depends only on addresses in `[base, base + space n_max)`. -/
private theorem tableInv_congr {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem mem' : ℕ → ℕ}
    (hinv : TableInv U V n_max base θ s mem)
    (heq : ∀ a ∈ (Block.mk base (space n_max)).footprint, mem' a = mem a) :
    TableInv U V n_max base θ s mem' := by
  have hused : ∀ p : Fin (2 ^ tableLog n_max),
      usedAt base n_max mem' p = usedAt base n_max mem p := by
    intro p
    have hp := p.isLt
    apply heq
    rw [Block.mem_footprint, Block.Owns]
    dsimp only [usedAt, usedBase, space, tableSize]
    exact ⟨by omega, by omega⟩
  have hkey : ∀ p : Fin (2 ^ tableLog n_max),
      keyAt base n_max mem' p = keyAt base n_max mem p := by
    intro p
    have hp := p.isLt
    apply heq
    rw [Block.mem_footprint, Block.Owns]
    dsimp only [keyAt, keyBase, usedBase, space, tableSize]
    exact ⟨by omega, by omega⟩
  have hval : ∀ p : Fin (2 ^ tableLog n_max),
      valAt base n_max mem' p = valAt base n_max mem p := by
    intro p
    have hp := p.isLt
    apply heq
    rw [Block.mem_footprint, Block.Owns]
    dsimp only [valAt, valBase, keyBase, usedBase, space, tableSize]
    exact ⟨by omega, by omega⟩
  refine
    { card_dom_le := hinv.card_dom_le
      values_bounded := hinv.values_bounded
      used_bit := fun p => by rw [hused]; exact hinv.used_bit p
      occupied_key_lt := fun p hp => by rw [hkey]; rw [hused] at hp; exact hinv.occupied_key_lt p hp
      occupied_state := fun p u hp hk => by
        rw [hused] at hp
        rw [hkey] at hk
        rw [hval]
        exact hinv.occupied_state p u hp hk
      occupied_inj := fun p q hp hq hk => by
        rw [hused] at hp hq
        rw [hkey, hkey] at hk
        exact hinv.occupied_inj p q hp hq hk
      present_slot := fun u v hsu => by
        obtain ⟨k, hk_lt, hp, hk, hv, hpref⟩ := hinv.present_slot u v hsu
        refine ⟨k, hk_lt, by rwa [hused], by rwa [hkey], by rwa [hval], fun j hj => ?_⟩
        rw [hused]
        exact hpref j hj
      occupied_prefix := fun p u hp hk => by
        rw [hused] at hp
        rw [hkey] at hk
        obtain ⟨k, hk_lt, hp_eq, hpref⟩ := hinv.occupied_prefix p u hp hk
        refine ⟨k, hk_lt, hp_eq, fun j hj => ?_⟩
        rw [hused]
        exact hpref j hj }

theorem Rep.supported {U V n_max w base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {x x' : Data rLP}
    (hregs : ∀ i, (subroutineCode U n_max).input i = false → x'.regs i = x.regs i)
    (hmem : ∀ a ∈ (Block.mk base (space n_max)).footprint, x'.mem a = x.mem a)
    (hbdd : x'.Bounded w)
    (hrep : Rep U V n_max w base θ s x) :
    Rep U V n_max w base θ s x' := by
  have h0 : x'.regs 0 = base := by
    rw [hregs 0 rfl, hrep.reg_base]
  refine ⟨hbdd, h0, kwise_rep_congr hrep.kwise_rep fun a hlt hge => ?_,
    tableInv_congr hrep.table_inv hmem⟩
  apply hmem
  rw [Block.mem_footprint, Block.Owns]
  dsimp only [space]
  exact ⟨hge, by omega⟩

private theorem extend_kwiseMap_regs {y : Data 18} {x : Data 24} {j : Fin 24} (hj : 18 ≤ j.val) :
    (y.extend kwiseMap x).regs j = x.regs j := by
  change Function.extend kwiseMap y.regs x.regs j = x.regs j
  apply Function.extend_apply'
  rintro ⟨i, rfl⟩
  have := i.isLt
  dsimp only [kwiseMap, Fin.val_castLE] at hj
  omega

private theorem fits_q_of_hw {w U n_max : ℕ}
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w) :
    Fits w (2 ^ trinomialDeg U (tableLog n_max)) := by
  set q := trinomialDeg U (tableLog n_max)
  have hq_pos : 2 ≤ q := by
    dsimp only [q, trinomialDeg]
    have : 1 ≤ 3 ^ trinomialStep U (tableLog n_max) := Nat.one_le_pow _ 3 (by decide)
    omega
  change 2 ^ q < 2 ^ w
  exact (Nat.pow_lt_pow_iff_right one_lt_two).mpr (by omega)

private theorem fits_max_U_add_one_of_hw {w U n_max : ℕ}
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w) :
    Fits w (max U 2 + 1) := by
  set q := trinomialDeg U (tableLog n_max)
  have hq_pos : 2 ≤ q := by
    dsimp only [q, trinomialDeg]
    have : 1 ≤ 3 ^ trinomialStep U (tableLog n_max) := Nat.one_le_pow _ 3 (by decide)
    omega
  have hU_le : U ≤ 2 ^ q := le_two_pow_trinomialDeg U (tableLog n_max)
  have hpow_ge : 4 ≤ 2 ^ q :=
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by decide) hq_pos
  have hmax_le : max U 2 ≤ 2 ^ q := max_le hU_le (by omega)
  have hlt_2q : 2 ^ q + 1 < 2 ^ (2 * q) := by
    have hle_succ : 2 ^ (q + 1) ≤ 2 ^ (2 * q) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ] at hle_succ
    omega
  have hle_w : 2 ^ (2 * q) ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  change max U 2 + 1 < 2 ^ w
  omega

private theorem fits_U_of_hw {w U n_max : ℕ}
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w) :
    Fits w U :=
  (fits_max_U_add_one_of_hw hw).of_le (by omega)

private theorem fits_tableLog_of_hw {w U n_max : ℕ}
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w) :
    Fits w (tableLog n_max) := by
  have hle : tableLog n_max ≤ trinomialDeg U (tableLog n_max) :=
    le_trinomialDeg U (tableLog n_max)
  have hlt : trinomialDeg U (tableLog n_max) < 2 ^ trinomialDeg U (tableLog n_max) :=
    Nat.lt_two_pow_self
  exact (fits_q_of_hw hw).of_le (by omega)

private theorem fits_max_n_max_of_space {w base n_max : ℕ}
    (hfit : Fits w (base + space n_max)) :
    Fits w (max n_max 2) := by
  have h1 : max n_max 2 ≤ max (8 * n_max) 8 := by omega
  have h2a := eight_mul_le_tableSize n_max
  have h2b := eight_le_tableSize n_max
  have h3 : tableSize n_max ≤ base + space n_max := by
    dsimp only [space]
    omega
  exact hfit.of_le (by omega)

/-- `allocSpan n_max` executes in `3` steps, copying `frontierReg` (`18`) to `baseReg` (`0`) and
advancing `frontierReg` to `base + space n_max`. -/
theorem allocSpan_execWithin {w base n_max : ℕ} {x : Data rLP}
    (hfr : x.regs 18 = base) (hfit : Fits w (base + space n_max)) :
    ∃ x₁ : Data rLP,
      ExecWithin w (allocSpan n_max) x x₁ 3 ∧
      x₁.mem = x.mem ∧
      x₁.regs 0 = base ∧
      x₁.regs 18 = base + space n_max := by
  have hfit_sp : Fits w (space n_max) := hfit.of_le (by omega)
  set s1 := x.set 0 base
  have e1 : Exec w (.op (.copy 0 18) : Code .exact 24) x s1 1 := by
    simpa +decide [s1, hfr] using (Exec.copy (B := .exact) (w := w) (d := 0) (s := 18) (x := x))
  set s2 := s1.set 3 (space n_max)
  have e2 : Exec w (.op (.const 3 (space n_max)) : Code .exact 24) s1 s2 1 :=
    Exec.const hfit_sp
  set s3 := s2.set 18 (base + space n_max)
  have e3 : Exec w (.op (.exactBin .add 18 0 3) : Code .exact 24) s2 s3 1 :=
    exec_exactBin (by simp +decide [s2, s1]) hfit
  exact ⟨s3, ⟨3, le_rfl, e1.seq (e2.seq e3)⟩, rfl, by simp +decide [s3, s2, s1],
    by simp +decide [s3]⟩

/-- `initSetup U n_max` initializes the `5`-wise independent hash table and leaves the zeroed
linear-probing arrays representing the empty dictionary in at most `setupTime U n_max` expected
instructions. -/
theorem initSetup_exec {U V n_max w base : ℕ} {x₁ : Data rLP}
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w)
    (hfit_space : Fits w (base + space n_max))
    (hx₁ : x₁.Bounded w)
    (hb : x₁.regs 0 = base)
    (hfr : x₁.regs 18 = base + space n_max)
    (hz : ∀ a ∈ (Block.mk base (space n_max)).footprint, x₁.mem a = 0) :
    ∃ ν₀ : PMF (Seed U n_max × Data rLP),
      ExecCodeDist w (initSetup U n_max) x₁ (ν₀.map Prod.snd) (setupTime U n_max) ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ 1 * seedLaw U n_max θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs 18 = base + space n_max ∧
        Rep U V n_max w base p.1 (Dictionary.empty U) p.2 ∧
        0 ≤ 0 ∧
        Modifies (Block.mk base (space n_max)).footprint x₁.mem p.2.mem := by
  have hfit_kwise : Fits w (base + KWise.space n_max 5) :=
    hfit_space.of_le (by dsimp only [space]; omega)
  have hfit_n : Fits w (max n_max 2) := fits_max_n_max_of_space hfit_space
  have hfit_n_val : Fits w n_max := hfit_n.of_le (le_max_left _ _)
  have hfit_U1 : Fits w (max U 2 + 1) := fits_max_U_add_one_of_hw hw
  have hfit_U : Fits w U := fits_U_of_hw hw
  have hfit_M : Fits w (tableLog n_max) := fits_tableLog_of_hw hw
  have hfit_q : Fits w (2 ^ trinomialDeg U (tableLog n_max)) := fits_q_of_hw hw
  set x₀ : Data 18 := x₁.comap kwiseMap
  have hx₀_0 : x₀.regs 0 = base := hb
  set s1 := x₀.set 1 n_max
  have e1 : Exec w (.op (.const 1 n_max) : Code .exact 18) x₀ s1 1 := Exec.const hfit_n_val
  set s2 := s1.set 2 U
  have e2 : Exec w (.op (.const 2 U) : Code .exact 18) s1 s2 1 := Exec.const hfit_U
  set s3 := s2.set 3 (tableLog n_max)
  have e3 : Exec w (.op (.const 3 (tableLog n_max)) : Code .exact 18) s2 s3 1 :=
    Exec.const hfit_M
  obtain ⟨dTab, hdTab_exec, htab, hdTab_0, hdTab_out⟩ :=
    KWise.initTableCode_execWithin (x := s3)
      (by simp +decide [s3, s2, s1, hx₀_0])
      (by simp +decide [s3, s2, s1])
      (by simp +decide [s3, s2])
      (by simp +decide [s3])
      hfit_kwise hfit_n hfit_U1 hfit_q
  have hsp_k : KWise.space n_max 5 = 8 + 5 + 2 ^ (2 * KWise.chunkBits n_max) := rfl
  have hpow_pos : 0 < 2 ^ (2 * KWise.chunkBits n_max) := by positivity
  have hfit_end : Fits w (base + 8 + 5) := hfit_kwise.of_le (by omega)
  set m := KWise.resampleComp base U (tableLog n_max) 5 dTab
  have he_rand : ExecRand w (KWise.resampleCode 5) dTab m :=
    KWise.resampleCode_execRand htab hdTab_0 hfit_end hfit_q
  obtain ⟨m', he_rand', _, hsupp⟩ :=
    KWise.resampleCode_execRandWithin htab hdTab_0 hfit_end hfit_q
  obtain rfl := he_rand.unique he_rand'
  have hexp_le : ProbComp.expect m (fun z => (z.2 : ℝ≥0∞)) ≤ 35 := by
    calc ProbComp.expect m (fun z => (z.2 : ℝ≥0∞))
        ≤ ProbComp.expect m (fun _ => (35 : ℝ≥0∞)) :=
          ProbComp.expect_mono_on_support (fun z hz => Nat.cast_le.mpr (hsupp z hz).2)
      _ = 35 := ProbComp.expect_const m 35
  have hdist_res : ExecCodeDist w (KWise.resampleCode 5) dTab (m.eval.map Prod.fst) 35 := by
    have h0 := (ExecCodeDist.of_execRand he_rand).mono hexp_le
    rwa [ProbComp.eval_map] at h0
  have hdist_initCode : ExecCodeDist w (KWise.initCode 5) s3 (m.eval.map Prod.fst)
      (KWise.initTableSteps n_max U (tableLog n_max) + 35) :=
    (ExecCodeDist.of_execWithin hdTab_exec).seq_pure hdist_res
  have hdist_18 : ExecCodeDist w (initSetup18 U n_max) x₀ (m.eval.map Prod.fst)
      (setupTime U n_max) := by
    have h123 :=
      (ExecCodeDist.of_exec e1).seq_pure
        ((ExecCodeDist.of_exec e2).seq_pure
          ((ExecCodeDist.of_exec e3).seq_pure hdist_initCode))
    refine h123.mono ?_
    dsimp only [setupTime]
    norm_cast
    omega
  have hdist_24 := hdist_18.rename injective_kwiseMap
  let pairFn : Data 18 × ℕ → Seed U n_max × Data rLP := fun z =>
    (KWise.extractSeeds base U (tableLog n_max) 5 z.1.mem, z.1.extend kwiseMap x₁)
  refine ⟨m.eval.map pairFn, ?_, ?_, ?_⟩
  · refine hdist_24.congr_dist ?_ le_rfl
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  · intro θ
    have hmap : (m.eval.map pairFn).map Prod.fst = seedLaw U n_max := by
      rw [PMF.map_comp]
      exact KWise.map_extractSeeds_eval_resampleComp base U (tableLog n_max) 5 dTab
    rw [hmap, one_mul]
  · intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨z, hz_eval, rfl⟩ := hp
    rw [ProbComp.support_eval] at hz_eval
    obtain ⟨⟨hkrep, hz_0, hz_out⟩, _⟩ := hsupp z hz_eval
    have hp_mem_snd : z.1.extend kwiseMap x₁ ∈
        ((m.eval.map Prod.fst).map (fun y => y.extend kwiseMap x₁)).support := by
      rw [PMF.mem_support_map_iff]
      refine ⟨z.1, ?_, rfl⟩
      rw [PMF.mem_support_map_iff]
      exact ⟨z, (ProbComp.support_eval m).symm ▸ hz_eval, rfl⟩
    have hbdd_p : (z.1.extend kwiseMap x₁).Bounded w := hdist_24.bounded hx₁ _ hp_mem_snd
    have hfr_p : (z.1.extend kwiseMap x₁).regs 18 = base + space n_max := by
      rw [extend_kwiseMap_regs (by decide), hfr]
    have hbase_p : (z.1.extend kwiseMap x₁).regs 0 = base := by
      change ((z.1.extend kwiseMap x₁).comap kwiseMap).regs 0 = base
      rw [Data.comap_extend injective_kwiseMap]
      exact hz_0
    have hmem_above : ∀ a, base + KWise.space n_max 5 ≤ a → z.1.mem a = x₁.mem a := by
      intro a ha
      rw [hz_out a (Or.inr (by omega)), hdTab_out a (Or.inr ha)]
      rfl
    have hempty_used : ∀ j : Fin (2 ^ tableLog n_max),
        usedAt base n_max (z.1.extend kwiseMap x₁).mem j = 0 := by
      intro j
      have hj := j.isLt
      change z.1.mem (usedBase base n_max + j.val) = 0
      rw [hmem_above (usedBase base n_max + j.val) (by dsimp only [usedBase]; omega)]
      apply hz
      rw [Block.mem_footprint, Block.Owns]
      dsimp only [usedAt, usedBase, space, tableSize]
      exact ⟨by omega, by omega⟩
    have htable_p : TableInv U V n_max base
        (KWise.extractSeeds base U (tableLog n_max) 5 z.1.mem)
        (Dictionary.empty U) (z.1.extend kwiseMap x₁).mem :=
      tableInv_empty U V n_max base _ hempty_used
    have hmod_p : Modifies (Block.mk base (space n_max)).footprint x₁.mem
        (z.1.extend kwiseMap x₁).mem := by
      intro a ha
      rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
      change z.1.mem a = x₁.mem a
      have ha_k : a < base ∨ base + KWise.space n_max 5 ≤ a := by
        dsimp only [space] at ha
        omega
      have ha_s : a < base + 8 ∨ base + 8 + 5 ≤ a := by omega
      rw [hz_out a ha_s, hdTab_out a ha_k]
      rfl
    exact ⟨hfr_p, ⟨hbdd_p, hbase_p, hkrep, htable_p⟩, le_rfl, hmod_p⟩

/-- Single-slot inspection `probeCheckCode` executes in at most `8` deterministic steps, loading
`usedAt base n_max x.mem pos` into `reg 9` and setting `reg 7` to `1` iff
`usedAt base n_max x.mem pos = 1 ∧ keyAt base n_max x.mem pos ≠ u.val`. -/
theorem probeCheckCode_execWithin {U w base n_max : ℕ} (u : Fin U)
    (pos : Fin (2 ^ tableLog n_max)) {x : Data rLP}
    (h0 : x.regs 0 = base)
    (h1 : x.regs 1 = u.val)
    (h2 : x.regs 2 = pos.val)
    (h3 : x.regs 3 = tableSize n_max - 1)
    (h4 : x.regs 4 = usedBase base n_max)
    (h5 : x.regs 5 = keyBase base n_max)
    (h6 : x.regs 6 = valBase base n_max)
    (h10 : x.regs 10 = 1)
    (hfit_space : Fits w (base + space n_max)) :
    ∃ y : Data rLP,
      ExecWithin w probeCheckCode x y 8 ∧
      y.mem = x.mem ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = pos.val ∧
      y.regs 3 = tableSize n_max - 1 ∧
      y.regs 4 = usedBase base n_max ∧
      y.regs 5 = keyBase base n_max ∧
      y.regs 6 = valBase base n_max ∧
      y.regs 7 = (if usedAt base n_max x.mem pos = 1 ∧
        keyAt base n_max x.mem pos ≠ u.val then 1 else 0) ∧
      y.regs 9 = usedAt base n_max x.mem pos ∧
      y.regs 10 = 1 ∧
      y.regs 22 = x.regs 22 ∧
      y.regs 23 = x.regs 23 := by
  have hpos_lt : pos.val < tableSize n_max := pos.isLt
  have hfit_uaddr : Fits w (usedBase base n_max + pos.val) :=
    hfit_space.of_le (by dsimp only [usedBase, space]; omega)
  have hfit_kaddr : Fits w (keyBase base n_max + pos.val) :=
    hfit_space.of_le (by dsimp only [keyBase, usedBase, space]; omega)
  have hfit_0 : Fits w 0 := hfit_space.of_le (Nat.zero_le _)
  have hfit_1 : Fits w 1 :=
    hfit_space.of_le (by dsimp only [space]; have := tableSize_pos n_max; omega)
  set s1 := x.set 8 (usedBase base n_max + pos.val)
  have e1 : Exec w (.op (.exactBin .add 8 4 2) : Code .exact 24) x s1 1 :=
    exec_exactBin (by simp +decide [h4, h2]) hfit_uaddr
  set s2 := s1.set 9 (usedAt base n_max x.mem pos)
  have e2 : Exec w (.op (.load 9 8) : Code .exact 24) s1 s2 1 := by
    simpa +decide [s2, s1, usedAt] using
      (Exec.load (B := .exact) (w := w) (d := 9) (a := 8) (x := s1))
  by_cases hused : usedAt base n_max x.mem pos = 1
  · have hc_outer : (Cond.eq (9 : Fin 24) 10).Holds s2 := by
      simp +decide [Cond.Holds, s2, s1, h10, hused]
    set s3 := s2.set 8 (keyBase base n_max + pos.val)
    have e3 : Exec w (.op (.exactBin .add 8 5 2) : Code .exact 24) s2 s3 1 :=
      exec_exactBin (by simp +decide [s2, s1, h5, h2]) hfit_kaddr
    set s4 := s3.set 8 (keyAt base n_max x.mem pos)
    have e4 : Exec w (.op (.load 8 8) : Code .exact 24) s3 s4 1 := by
      simpa +decide [s4, s3, s2, s1, keyAt] using
        (Exec.load (B := .exact) (w := w) (d := 8) (a := 8) (x := s3))
    by_cases hkey : keyAt base n_max x.mem pos = u.val
    · have hc_inner : (Cond.eq (8 : Fin 24) 1).Holds s4 := by
        simp +decide [Cond.Holds, s4, s3, s2, s1, h1, hkey]
      set s5 := s4.set 7 0
      have e5 : Exec w (.op (.const 7 0) : Code .exact 24) s4 s5 1 := Exec.const hfit_0
      have hall : Exec w probeCheckCode x s5 7 :=
        e1.seq (e2.seq (Exec.branch_pos hc_outer (e3.seq (e4.seq (Exec.branch_pos hc_inner e5)))))
      refine ⟨s5, ⟨7, by decide, hall⟩, rfl,
        by simp +decide [s5, s4, s3, s2, s1, h0],
        by simp +decide [s5, s4, s3, s2, s1, h1],
        by simp +decide [s5, s4, s3, s2, s1, h2],
        by simp +decide [s5, s4, s3, s2, s1, h3],
        by simp +decide [s5, s4, s3, s2, s1, h4],
        by simp +decide [s5, s4, s3, s2, s1, h5],
        by simp +decide [s5, s4, s3, s2, s1, h6],
        by simp [s5, hused, hkey],
        by simp +decide [s5, s4, s3, s2],
        by simp +decide [s5, s4, s3, s2, s1, h10],
        by simp +decide [s5, s4, s3, s2, s1],
        by simp +decide [s5, s4, s3, s2, s1]⟩
    · have hc_inner : ¬(Cond.eq (8 : Fin 24) 1).Holds s4 := by
        simp +decide [Cond.Holds, s4, s3, s2, s1, h1, hkey]
      set s5 := s4.set 7 1
      have e5 : Exec w (.op (.const 7 1) : Code .exact 24) s4 s5 1 := Exec.const hfit_1
      have hall : Exec w probeCheckCode x s5 8 :=
        e1.seq (e2.seq (Exec.branch_pos hc_outer (e3.seq (e4.seq (Exec.branch_neg hc_inner e5)))))
      refine ⟨s5, ⟨8, le_rfl, hall⟩, rfl,
        by simp +decide [s5, s4, s3, s2, s1, h0],
        by simp +decide [s5, s4, s3, s2, s1, h1],
        by simp +decide [s5, s4, s3, s2, s1, h2],
        by simp +decide [s5, s4, s3, s2, s1, h3],
        by simp +decide [s5, s4, s3, s2, s1, h4],
        by simp +decide [s5, s4, s3, s2, s1, h5],
        by simp +decide [s5, s4, s3, s2, s1, h6],
        by simp [s5, hused, hkey],
        by simp +decide [s5, s4, s3, s2],
        by simp +decide [s5, s4, s3, s2, s1, h10],
        by simp +decide [s5, s4, s3, s2, s1],
        by simp +decide [s5, s4, s3, s2, s1]⟩
  · have hc_outer : ¬(Cond.eq (9 : Fin 24) 10).Holds s2 := by
      simp +decide [Cond.Holds, s2, s1, h10, hused]
    set s3 := s2.set 7 0
    have e3 : Exec w (.op (.const 7 0) : Code .exact 24) s2 s3 1 := Exec.const hfit_0
    have hall : Exec w probeCheckCode x s3 5 :=
      e1.seq (e2.seq (Exec.branch_neg hc_outer e3))
    refine ⟨s3, ⟨5, by decide, hall⟩, rfl,
      by simp +decide [s3, s2, s1, h0],
      by simp +decide [s3, s2, s1, h1],
      by simp +decide [s3, s2, s1, h2],
      by simp +decide [s3, s2, s1, h3],
      by simp +decide [s3, s2, s1, h4],
      by simp +decide [s3, s2, s1, h5],
      by simp +decide [s3, s2, s1, h6],
      by simp [s3, hused],
      by simp +decide [s3, s2],
      by simp +decide [s3, s2, s1, h10],
      by simp +decide [s3, s2, s1],
      by simp +decide [s3, s2, s1]⟩

/-- `probeSetupCode n_max` executes in at most `16` deterministic steps, initializing registers
`3, 4, 5, 6, 10` and running `probeCheckCode` on the initial hash bucket `pos`. -/
theorem probeSetupCode_execWithin {U w base n_max : ℕ} (u : Fin U)
    (pos : Fin (2 ^ tableLog n_max)) {x : Data rLP}
    (h0 : x.regs 0 = base)
    (h1 : x.regs 1 = u.val)
    (h2 : x.regs 2 = pos.val)
    (hfit_space : Fits w (base + space n_max)) :
    ∃ y : Data rLP,
      ExecWithin w (probeSetupCode n_max) x y 16 ∧
      y.mem = x.mem ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = pos.val ∧
      y.regs 3 = tableSize n_max - 1 ∧
      y.regs 4 = usedBase base n_max ∧
      y.regs 5 = keyBase base n_max ∧
      y.regs 6 = valBase base n_max ∧
      y.regs 7 = (if usedAt base n_max x.mem pos = 1 ∧
        keyAt base n_max x.mem pos ≠ u.val then 1 else 0) ∧
      y.regs 9 = usedAt base n_max x.mem pos ∧
      y.regs 10 = 1 ∧
      y.regs 22 = x.regs 22 ∧
      y.regs 23 = x.regs 23 := by
  have hts_pos : 0 < tableSize n_max := tableSize_pos n_max
  have hfit_mask : Fits w (tableSize n_max - 1) :=
    hfit_space.of_le (by dsimp only [space]; omega)
  have hfit_ksp : Fits w (KWise.space n_max 5) :=
    hfit_space.of_le (by dsimp only [space]; omega)
  have hfit_ub : Fits w (usedBase base n_max) :=
    hfit_space.of_le (by dsimp only [usedBase, space]; omega)
  have hfit_ts : Fits w (tableSize n_max) :=
    hfit_space.of_le (by dsimp only [space]; omega)
  have hfit_kb : Fits w (keyBase base n_max) :=
    hfit_space.of_le (by dsimp only [keyBase, usedBase, space]; omega)
  have hfit_vb : Fits w (valBase base n_max) :=
    hfit_space.of_le (by dsimp only [valBase, keyBase, usedBase, space]; omega)
  have hfit_1 : Fits w 1 :=
    hfit_space.of_le (by dsimp only [space]; omega)
  set s1 := x.set 3 (tableSize n_max - 1)
  have e1 : Exec w (.op (.const 3 (tableSize n_max - 1)) : Code .exact 24) x s1 1 :=
    Exec.const hfit_mask
  set s2 := s1.set 4 (KWise.space n_max 5)
  have e2 : Exec w (.op (.const 4 (KWise.space n_max 5)) : Code .exact 24) s1 s2 1 :=
    Exec.const hfit_ksp
  set s3 := s2.set 4 (usedBase base n_max)
  have e3 : Exec w (.op (.exactBin .add 4 0 4) : Code .exact 24) s2 s3 1 :=
    exec_exactBin (by simp +decide [s2, s1, h0, usedBase]) hfit_ub
  set s4 := s3.set 5 (tableSize n_max)
  have e4 : Exec w (.op (.const 5 (tableSize n_max)) : Code .exact 24) s3 s4 1 :=
    Exec.const hfit_ts
  set s5 := s4.set 5 (keyBase base n_max)
  have e5 : Exec w (.op (.exactBin .add 5 4 5) : Code .exact 24) s4 s5 1 :=
    exec_exactBin (by simp +decide [s4, s3, keyBase]) hfit_kb
  set s6 := s5.set 6 (tableSize n_max)
  have e6 : Exec w (.op (.const 6 (tableSize n_max)) : Code .exact 24) s5 s6 1 :=
    Exec.const hfit_ts
  set s7 := s6.set 6 (valBase base n_max)
  have e7 : Exec w (.op (.exactBin .add 6 5 6) : Code .exact 24) s6 s7 1 :=
    exec_exactBin (by simp +decide [s6, s5, valBase]) hfit_vb
  set s8 := s7.set 10 1
  have e8 : Exec w (.op (.const 10 1) : Code .exact 24) s7 s8 1 :=
    Exec.const hfit_1
  obtain ⟨y, ⟨m, hm, he9⟩, hymem, hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7, hy9, hy10, hy22, hy23⟩ :=
    probeCheckCode_execWithin u pos (x := s8)
      (by simp +decide [s8, s7, s6, s5, s4, s3, s2, s1, h0])
      (by simp +decide [s8, s7, s6, s5, s4, s3, s2, s1, h1])
      (by simp +decide [s8, s7, s6, s5, s4, s3, s2, s1, h2])
      (by simp +decide [s8, s7, s6, s5, s4, s3, s2, s1])
      (by simp +decide [s8, s7, s6, s5, s4, s3])
      (by simp +decide [s8, s7, s6, s5])
      (by simp +decide [s8, s7])
      (by simp +decide [s8])
      hfit_space
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq he9)))))))
  exact ⟨y, ⟨_, by omega, hall⟩, hymem, hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7, hy9, hy10,
    by simpa +decide [s8, s7, s6, s5, s4, s3, s2, s1] using hy22,
    by simpa +decide [s8, s7, s6, s5, s4, s3, s2, s1] using hy23⟩

/-- One iteration of `probeBody` advances `pos` to `probeSlot (tableLog n_max) pos 1` and inspects
the new slot in at most `10` deterministic steps. -/
theorem probeBody_execWithin {U w base n_max : ℕ} (u : Fin U)
    (pos : Fin (2 ^ tableLog n_max)) {x : Data rLP}
    (h0 : x.regs 0 = base)
    (h1 : x.regs 1 = u.val)
    (h2 : x.regs 2 = pos.val)
    (h3 : x.regs 3 = tableSize n_max - 1)
    (h4 : x.regs 4 = usedBase base n_max)
    (h5 : x.regs 5 = keyBase base n_max)
    (h6 : x.regs 6 = valBase base n_max)
    (h10 : x.regs 10 = 1)
    (hfit_space : Fits w (base + space n_max)) :
    let pos' := probeSlot (tableLog n_max) pos 1
    ∃ y : Data rLP,
      ExecWithin w probeBody x y 10 ∧
      y.mem = x.mem ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = pos'.val ∧
      y.regs 3 = tableSize n_max - 1 ∧
      y.regs 4 = usedBase base n_max ∧
      y.regs 5 = keyBase base n_max ∧
      y.regs 6 = valBase base n_max ∧
      y.regs 7 = (if usedAt base n_max x.mem pos' = 1 ∧
        keyAt base n_max x.mem pos' ≠ u.val then 1 else 0) ∧
      y.regs 9 = usedAt base n_max x.mem pos' ∧
      y.regs 10 = 1 ∧
      y.regs 22 = x.regs 22 ∧
      y.regs 23 = x.regs 23 := by
  set pos' := probeSlot (tableLog n_max) pos 1
  have hpos_lt : pos.val < tableSize n_max := pos.isLt
  have hpos'_lt : pos'.val < tableSize n_max := pos'.isLt
  have hfit_p1 : Fits w (pos.val + 1) :=
    hfit_space.of_le (by dsimp only [space]; omega)
  have hfit_pos' : Fits w pos'.val :=
    hfit_space.of_le (by dsimp only [space]; omega)
  have hand_eq : (pos.val + 1) &&& (tableSize n_max - 1) = pos'.val := by
    dsimp only [tableSize, pos', probeSlot, cyclicSlotMod]
    exact Nat.and_two_pow_sub_one_eq_mod (pos.val + 1) (tableLog n_max)
  set s1 := x.set 2 (pos.val + 1)
  have e1 : Exec w (.op (.exactBin .add 2 2 10) : Code .exact 24) x s1 1 :=
    exec_exactBin (by simp +decide [h2, h10]) hfit_p1
  set s2 := s1.set 2 pos'.val
  have e2 : Exec w (.op (.exactBin .and 2 2 3) : Code .exact 24) s1 s2 1 :=
    exec_exactBin (by simp +decide [s1, h3, hand_eq]) hfit_pos'
  obtain ⟨y, ⟨m, hm, he3⟩, hymem, hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7, hy9, hy10, hy22, hy23⟩ :=
    probeCheckCode_execWithin u pos' (x := s2)
      (by simp +decide [s2, s1, h0])
      (by simp +decide [s2, s1, h1])
      (by simp +decide [s2])
      (by simp +decide [s2, s1, h3])
      (by simp +decide [s2, s1, h4])
      (by simp +decide [s2, s1, h5])
      (by simp +decide [s2, s1, h6])
      (by simp +decide [s2, s1, h10])
      hfit_space
  exact ⟨y, ⟨_, by omega, e1.seq (e2.seq he3)⟩, hymem, hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7,
    hy9, hy10,
    by simpa +decide [s2, s1] using hy22,
    by simpa +decide [s2, s1] using hy23⟩

/-- `probeLoop` halts deterministically at the stopping slot
`p = probeSlot (tableLog n_max) b (hinv.probeLen u b)` in at most
`12 * (hinv.probeLen u b) + 2` instructions. -/
theorem probeLoop_execWithin {U V w base n_max : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {x : Data rLP}
    (hinv : TableInv U V n_max base θ s x.mem)
    (u : Fin U)
    (h0 : x.regs 0 = base)
    (h1 : x.regs 1 = u.val)
    (h2 : x.regs 2 = (hashFn U n_max θ u).val)
    (h3 : x.regs 3 = tableSize n_max - 1)
    (h4 : x.regs 4 = usedBase base n_max)
    (h5 : x.regs 5 = keyBase base n_max)
    (h6 : x.regs 6 = valBase base n_max)
    (h7 : x.regs 7 = (if usedAt base n_max x.mem (hashFn U n_max θ u) = 1 ∧
      keyAt base n_max x.mem (hashFn U n_max θ u) ≠ u.val then 1 else 0))
    (h9 : x.regs 9 = usedAt base n_max x.mem (hashFn U n_max θ u))
    (h10 : x.regs 10 = 1)
    (hfit_space : Fits w (base + space n_max)) :
    let b := hashFn U n_max θ u
    let t := hinv.probeLen u b
    let p := probeSlot (tableLog n_max) b t
    ∃ y : Data rLP,
      ExecWithin w probeLoop x y (12 * t + 2) ∧
      y.mem = x.mem ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = p.val ∧
      y.regs 4 = usedBase base n_max ∧
      y.regs 5 = keyBase base n_max ∧
      y.regs 6 = valBase base n_max ∧
      y.regs 9 = usedAt base n_max x.mem p ∧
      y.regs 10 = 1 ∧
      y.regs 22 = x.regs 22 ∧
      y.regs 23 = x.regs 23 := by
  set b := hashFn U n_max θ u
  set t := hinv.probeLen u b
  set p := probeSlot (tableLog n_max) b t
  suffices hmain : ∀ rem k (d : Data rLP),
      k + rem = t →
      d.mem = x.mem →
      d.regs 0 = base →
      d.regs 1 = u.val →
      d.regs 2 = (probeSlot (tableLog n_max) b k).val →
      d.regs 3 = tableSize n_max - 1 →
      d.regs 4 = usedBase base n_max →
      d.regs 5 = keyBase base n_max →
      d.regs 6 = valBase base n_max →
      d.regs 7 = (if usedAt base n_max x.mem (probeSlot (tableLog n_max) b k) = 1 ∧
        keyAt base n_max x.mem (probeSlot (tableLog n_max) b k) ≠ u.val then 1 else 0) →
      d.regs 9 = usedAt base n_max x.mem (probeSlot (tableLog n_max) b k) →
      d.regs 10 = 1 →
      d.regs 22 = x.regs 22 →
      d.regs 23 = x.regs 23 →
      ∃ y : Data rLP,
        ExecWithin w probeLoop d y (12 * rem + 2) ∧
        y.mem = x.mem ∧
        y.regs 0 = base ∧
        y.regs 1 = u.val ∧
        y.regs 2 = p.val ∧
        y.regs 4 = usedBase base n_max ∧
        y.regs 5 = keyBase base n_max ∧
        y.regs 6 = valBase base n_max ∧
        y.regs 9 = usedAt base n_max x.mem p ∧
        y.regs 10 = 1 ∧
        y.regs 22 = x.regs 22 ∧
        y.regs 23 = x.regs 23 by
    exact hmain t 0 x (Nat.zero_add t) rfl h0 h1
      (by rw [probeSlot_zero, h2]) h3 h4 h5 h6
      (by rw [probeSlot_zero, h7]) (by rw [probeSlot_zero, h9]) h10 rfl rfl
  intro rem
  induction rem with
  | zero =>
    intro k d hkr hdmem hd0 hd1 hd2 _ hd4 hd5 hd6 hd7 hd9 hd10 hd22 hd23
    have hkt : k = t := by omega
    subst hkt
    have hstop : ¬(usedAt base n_max x.mem p = 1 ∧ keyAt base n_max x.mem p ≠ u.val) := by
      rcases hinv.probeStop_spec u with ⟨hp0, _⟩ | ⟨_, hkey, _⟩
      · rintro ⟨hp1, _⟩
        rw [hp0] at hp1
        cases hp1
      · rintro ⟨_, hne⟩
        exact hne hkey
    have hd7_0 : d.regs 7 = 0 := by simp [hd7, p, hstop]
    have hc : ¬(Cond.eq (7 : Fin 24) 10).Holds d := by
      simp [Cond.Holds, hd7_0, hd10]
    exact ⟨d, ⟨2, le_rfl, Exec.loop_exit hc⟩, hdmem, hd0, hd1, hd2, hd4, hd5, hd6, hd9, hd10,
      hd22, hd23⟩
  | succ rem ih =>
    intro k d hkr hdmem hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd9 hd10 hd22 hd23
    have hkt : k < t := by omega
    have hcont : usedAt base n_max x.mem (probeSlot (tableLog n_max) b k) = 1 ∧
        keyAt base n_max x.mem (probeSlot (tableLog n_max) b k) ≠ u.val :=
      hinv.probeContinue_of_lt_probeLen u b hkt
    have hd7_1 : d.regs 7 = 1 := by simp [hd7, hcont]
    have hc : (Cond.eq (7 : Fin 24) 10).Holds d := by
      simp [Cond.Holds, hd7_1, hd10]
    obtain ⟨d', ⟨nb, hnb, heb⟩, hd'mem, hd'0, hd'1, hd'2, hd'3, hd'4, hd'5, hd'6, hd'7,
        hd'9, hd'10, hd'22, hd'23⟩ :=
      probeBody_execWithin u (probeSlot (tableLog n_max) b k) (x := d)
        hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd10 hfit_space
    have hslot_succ : probeSlot (tableLog n_max) (probeSlot (tableLog n_max) b k) 1 =
        probeSlot (tableLog n_max) b (k + 1) :=
      probeSlot_add b k 1
    rw [hslot_succ] at hd'2 hd'7 hd'9
    rw [hdmem] at hd'7 hd'9
    obtain ⟨y, ⟨nl, hnl, hel⟩, hymem, hy0, hy1, hy2, hy4, hy5, hy6, hy9, hy10, hy22, hy23⟩ :=
      ih (k + 1) d' (by omega) (hd'mem.trans hdmem) hd'0 hd'1 hd'2 hd'3 hd'4 hd'5 hd'6
        hd'7 hd'9 hd'10 (hd'22.trans hd22) (hd'23.trans hd23)
    exact ⟨y, ⟨nb + nl + 2, by omega, Exec.loop_iter hc heb hel⟩,
      hymem, hy0, hy1, hy2, hy4, hy5, hy6, hy9, hy10, hy22, hy23⟩

/-- `insertFinishCode` executes in `7` deterministic steps, writing `(1, u.val, v)` at slot `p`
(`insertMem base n_max x.mem p u.val v`) and setting `reg 2` (`outReg`) to `0`. -/
theorem insertFinishCode_execWithin {U w base n_max : ℕ} (u : Fin U) (v : ℕ)
    (p : Fin (2 ^ tableLog n_max)) {x : Data rLP}
    (h0 : x.regs 0 = base)
    (h1 : x.regs 1 = u.val)
    (h2 : x.regs 2 = p.val)
    (h4 : x.regs 4 = usedBase base n_max)
    (h5 : x.regs 5 = keyBase base n_max)
    (h6 : x.regs 6 = valBase base n_max)
    (h10 : x.regs 10 = 1)
    (h23 : x.regs 23 = v)
    (hfit_space : Fits w (base + space n_max)) :
    ∃ y : Data rLP,
      ExecWithin w insertFinishCode x y 7 ∧
      y.mem = insertMem base n_max x.mem p u.val v ∧
      y.regs 0 = base ∧
      y.regs 2 = 0 := by
  have hp_lt : p.val < tableSize n_max := p.isLt
  have hfit_uaddr : Fits w (usedBase base n_max + p.val) :=
    hfit_space.of_le (by dsimp only [usedBase, space]; omega)
  have hfit_kaddr : Fits w (keyBase base n_max + p.val) :=
    hfit_space.of_le (by dsimp only [keyBase, usedBase, space]; omega)
  have hfit_vaddr : Fits w (valBase base n_max + p.val) :=
    hfit_space.of_le (by dsimp only [valBase, keyBase, usedBase, space]; omega)
  have hfit_0 : Fits w 0 := hfit_space.of_le (Nat.zero_le _)
  set s1 := x.set 8 (usedBase base n_max + p.val)
  have e1 : Exec w (.op (.exactBin .add 8 4 2) : Code .exact 24) x s1 1 :=
    exec_exactBin (by simp +decide [h4, h2]) hfit_uaddr
  set s2 := s1.write (usedBase base n_max + p.val) 1
  have e2 : Exec w (.op (.store 8 10) : Code .exact 24) s1 s2 1 := by
    simpa +decide [s2, s1, h10] using
      (Exec.store (B := .exact) (w := w) (a := 8) (s := 10) (x := s1))
  set s3 := s2.set 8 (keyBase base n_max + p.val)
  have e3 : Exec w (.op (.exactBin .add 8 5 2) : Code .exact 24) s2 s3 1 :=
    exec_exactBin (by simp +decide [s2, s1, h5, h2]) hfit_kaddr
  set s4 := s3.write (keyBase base n_max + p.val) u.val
  have e4 : Exec w (.op (.store 8 1) : Code .exact 24) s3 s4 1 := by
    simpa +decide [s4, s3, s2, s1, h1] using
      (Exec.store (B := .exact) (w := w) (a := 8) (s := 1) (x := s3))
  set s5 := s4.set 8 (valBase base n_max + p.val)
  have e5 : Exec w (.op (.exactBin .add 8 6 2) : Code .exact 24) s4 s5 1 :=
    exec_exactBin (by simp +decide [s4, s3, s2, s1, h6, h2]) hfit_vaddr
  set s6 := s5.write (valBase base n_max + p.val) v
  have e6 : Exec w (.op (.store 8 23) : Code .exact 24) s5 s6 1 := by
    simpa +decide [s6, s5, s4, s3, s2, s1, h23] using
      (Exec.store (B := .exact) (w := w) (a := 8) (s := 23) (x := s5))
  set s7 := s6.set 2 0
  have e7 : Exec w (.op (.const 2 0) : Code .exact 24) s6 s7 1 :=
    Exec.const hfit_0
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))
  exact ⟨s7, ⟨7, le_rfl, hall⟩, rfl, by simp +decide [s7, s6, s5, s4, s3, s2, s1, h0],
    by simp +decide [s7]⟩

/-- `getFinishCode` executes in at most `4` deterministic steps, writing `val[p] + 1` into `reg 2`
when `s u = some (val[p])` (`used[p] = 1`) and `0` into `reg 2` when `s u = none` (`used[p] = 0`).
-/
theorem getFinishCode_execWithin {U V w base n_max : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {x : Data rLP}
    (hinv : TableInv U V n_max base θ s x.mem)
    (u : Fin U)
    (h0 : x.regs 0 = base)
    (h2 : x.regs 2 = (probeSlot (tableLog n_max) (hashFn U n_max θ u)
      (hinv.probeLen u (hashFn U n_max θ u))).val)
    (h6 : x.regs 6 = valBase base n_max)
    (h9 : x.regs 9 = usedAt base n_max x.mem
      (probeSlot (tableLog n_max) (hashFn U n_max θ u)
        (hinv.probeLen u (hashFn U n_max θ u))))
    (h10 : x.regs 10 = 1)
    (hfit_space : Fits w (base + space n_max))
    (hfit_V : Fits w V) :
    ∃ y : Data rLP,
      ExecWithin w getFinishCode x y 4 ∧
      y.mem = x.mem ∧
      y.regs 0 = base ∧
      decodeOp (V := V) (n_max := n_max) (.get u) y.regs = some (s u) := by
  set p := probeSlot (tableLog n_max) (hashFn U n_max θ u) (hinv.probeLen u (hashFn U n_max θ u))
  have hp_lt : p.val < tableSize n_max := p.isLt
  have hfit_vaddr : Fits w (valBase base n_max + p.val) :=
    hfit_space.of_le (by dsimp only [valBase, keyBase, usedBase, space]; omega)
  have hfit_0 : Fits w 0 := hfit_space.of_le (Nat.zero_le _)
  rcases hinv.probeStop_spec u with ⟨hp0, hnone⟩ | ⟨hp1, _, hsome⟩
  · have hc : ¬(Cond.eq (9 : Fin 24) 10).Holds x := by
      simp [Cond.Holds, h9, p, hp0, h10]
    set s1 := x.set 2 0
    have e1 : Exec w (.op (.const 2 0) : Code .exact 24) x s1 1 := Exec.const hfit_0
    have ebr : Exec w getFinishCode x s1 3 := Exec.branch_neg hc e1
    refine ⟨s1, ⟨3, by decide, ebr⟩, rfl, by simp +decide [s1, h0], ?_⟩
    have hs1_2 : s1.regs 2 = 0 := by simp +decide [s1]
    simp only [decodeOp, hs1_2, ↓reduceIte, hnone]
    rfl
  · have hc : (Cond.eq (9 : Fin 24) 10).Holds x := by
      simp [Cond.Holds, h9, p, hp1, h10]
    have hv_lt : valAt base n_max x.mem p < V := hinv.values_bounded u _ hsome
    have hfit_vp1 : Fits w (valAt base n_max x.mem p + 1) := hfit_V.of_le (by omega)
    set s1 := x.set 8 (valBase base n_max + p.val)
    have e1 : Exec w (.op (.exactBin .add 8 6 2) : Code .exact 24) x s1 1 :=
      exec_exactBin (by simp +decide [h6, h2, p]) hfit_vaddr
    set s2 := s1.set 2 (valAt base n_max x.mem p)
    have e2 : Exec w (.op (.load 2 8) : Code .exact 24) s1 s2 1 := by
      simpa +decide [s2, s1, valAt, p] using
        (Exec.load (B := .exact) (w := w) (d := 2) (a := 8) (x := s1))
    set s3 := s2.set 2 (valAt base n_max x.mem p + 1)
    have e3 : Exec w (.op (.exactBin .add 2 2 10) : Code .exact 24) s2 s3 1 :=
      exec_exactBin (by simp +decide [s2, s1, h10]) hfit_vp1
    have ebr : Exec w getFinishCode x s3 4 := Exec.branch_pos hc (e1.seq (e2.seq e3))
    refine ⟨s3, ⟨4, le_rfl, ebr⟩, rfl, by simp +decide [s3, s2, s1, h0], ?_⟩
    have hs3_2 : s3.regs 2 = valAt base n_max x.mem p + 1 := by simp +decide [s3]
    simp only [decodeOp, hs3_2, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hsome, p]
    rfl

/-- The key queried or updated by dictionary operation `o`. -/
@[expose] def opKey {U : ℕ} : Dictionary.Op U → Fin U
  | .get u => u
  | .insert u _ => u

/-- `opCode n_max` executes any admissible operation `o` from `Rep U V n_max w base θ s x` and
`argMatchOp o x.regs` in at most
`KWise.evalSteps n_max U (tableLog n_max) 5 + 12 * t + 27` deterministic instructions (where
`t = hrep.table_inv.probeLen (opKey o) (hashFn U n_max θ (opKey o))`), preserving `Rep` for
`((Dictionary.spec U V n_max).step s o).1`, decoding to
`some ((Dictionary.spec U V n_max).step s o).2`, and modifying only
`(Block.mk base (space n_max)).footprint`. -/
theorem opCode_execWithin {U V w base n_max : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {x : Data rLP}
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w)
    (hfit_space : Fits w (base + space n_max))
    (hfit_V : Fits w V)
    (hrep : Rep U V n_max w base θ s x)
    (o : (Dictionary.spec U V n_max).Op)
    (hvalid : (Dictionary.spec U V n_max).valid s o)
    (harg : argMatchOp o x.regs) :
    let u := opKey o
    let b := hashFn U n_max θ u
    let t := hrep.table_inv.probeLen u b
    ∃ y : Data rLP,
      ExecWithin w (opCode n_max) x y
        (KWise.evalSteps n_max U (tableLog n_max) 5 + 12 * t + 27) ∧
      decodeOp (V := V) (n_max := n_max) o y.regs =
        some ((Dictionary.spec U V n_max).step s o).2 ∧
      Rep U V n_max w base θ ((Dictionary.spec U V n_max).step s o).1 y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem := by
  set u := opKey o
  set b := hashFn U n_max θ u
  set t := hrep.table_inv.probeLen u b
  set p := probeSlot (tableLog n_max) b t
  have hfit_kwise : Fits w (base + KWise.space n_max 5) :=
    hfit_space.of_le (by dsimp only [space]; omega)
  have hx1_key : x.regs 1 = u.val := by
    cases o with
    | get u₀ => exact harg.1
    | insert u₀ v => exact harg.1
  obtain ⟨y₀, heval₀, hy₀_0, hy₀_1, hy₀_2, hy₀_mem⟩ :=
    KWise.evalCode_execWithin u (x := x.comap kwiseMap) hrep.kwise_rep
      hrep.reg_base hx1_key hw hfit_kwise
  have heval1 := heval₀.rename injective_kwiseMap
  set x₁ := y₀.extend kwiseMap x
  have hx₁_mem : x₁.mem = x.mem := hy₀_mem
  have hx₁_0 : x₁.regs 0 = base := by
    change (x₁.comap kwiseMap).regs 0 = base
    rw [Data.comap_extend injective_kwiseMap]
    exact hy₀_0
  have hx₁_1 : x₁.regs 1 = u.val := by
    change (x₁.comap kwiseMap).regs 1 = u.val
    rw [Data.comap_extend injective_kwiseMap]
    exact hy₀_1
  have hx₁_2 : x₁.regs 2 = b.val := by
    change (x₁.comap kwiseMap).regs 2 = b.val
    rw [Data.comap_extend injective_kwiseMap]
    exact hy₀_2
  have hx₁_22 : x₁.regs 22 = x.regs 22 := extend_kwiseMap_regs (by decide)
  have hx₁_23 : x₁.regs 23 = x.regs 23 := extend_kwiseMap_regs (by decide)
  obtain ⟨x₂, he2, hx₂_mem, hx₂_0, hx₂_1, hx₂_2, hx₂_3, hx₂_4, hx₂_5, hx₂_6, hx₂_7,
      hx₂_9, hx₂_10, hx₂_22, hx₂_23⟩ :=
    probeSetupCode_execWithin u b (x := x₁) hx₁_0 hx₁_1 hx₁_2 hfit_space
  have hx₂_mem_eq : x₂.mem = x.mem := hx₂_mem.trans hx₁_mem
  rw [hx₁_mem] at hx₂_7 hx₂_9
  obtain ⟨x₃, he3, hx₃_mem, hx₃_0, hx₃_1, hx₃_2, hx₃_4, hx₃_5, hx₃_6, hx₃_9, hx₃_10,
      hx₃_22, hx₃_23⟩ :=
    probeLoop_execWithin (hinv := hx₂_mem_eq.symm ▸ hrep.table_inv) u
      hx₂_0 hx₂_1 hx₂_2 hx₂_3 hx₂_4 hx₂_5 hx₂_6
      (by simpa only [hx₂_mem_eq] using hx₂_7)
      (by simpa only [hx₂_mem_eq] using hx₂_9)
      hx₂_10 hfit_space
  have hx₃_mem_eq : x₃.mem = x.mem := hx₃_mem.trans hx₂_mem_eq
  have hx₃_22_eq : x₃.regs 22 = x.regs 22 := hx₃_22.trans (hx₂_22.trans hx₁_22)
  have hx₃_23_eq : x₃.regs 23 = x.regs 23 := hx₃_23.trans (hx₂_23.trans hx₁_23)
  have ht_eq : (hx₂_mem_eq.symm ▸ hrep.table_inv).probeLen u b = t :=
    TableInv.probeLen_congr _ hrep.table_inv hx₂_mem_eq u b
  rw [ht_eq] at he3 hx₃_2 hx₃_9
  rw [hx₂_mem_eq] at hx₃_9
  obtain ⟨n1, hn1, hex1⟩ := heval1
  obtain ⟨n2, hn2, hex2⟩ := he2
  obtain ⟨n3, hn3, hex3⟩ := he3
  cases o with
  | get u₀ =>
    have hu₀ : u₀ = u := rfl
    have hc_br : ¬(Cond.eq (22 : Fin 24) 10).Holds x₃ := by
      simp [Cond.Holds, hx₃_22_eq, harg.2, hx₃_10]
    have ht_eq3 : (hx₃_mem_eq.symm ▸ hrep.table_inv).probeLen u (hashFn U n_max θ u) = t :=
      TableInv.probeLen_congr _ hrep.table_inv hx₃_mem_eq u b
    obtain ⟨y, ⟨n4, hn4, hex4⟩, hymem, hy0, hdec⟩ :=
      getFinishCode_execWithin (hinv := hx₃_mem_eq.symm ▸ hrep.table_inv) u
        hx₃_0
        (by simpa only [ht_eq3] using hx₃_2)
        hx₃_6
        (by simpa only [ht_eq3, hx₃_mem_eq] using hx₃_9)
        hx₃_10 hfit_space hfit_V
    have he_br : Exec w (.branch (.eq 22 10) insertFinishCode getFinishCode) x₃ y (n4 + 2) :=
      Exec.branch_neg hc_br hex4
    have hall : Exec w (opCode n_max) x y (n1 + (n2 + (n3 + (n4 + 2)))) :=
      hex1.seq (hex2.seq (hex3.seq he_br))
    have hex_within : ExecWithin w (opCode n_max) x y
        (KWise.evalSteps n_max U (tableLog n_max) 5 + 12 * t + 27) :=
      ⟨_, by omega, hall⟩
    have hymem_x : y.mem = x.mem := hymem.trans hx₃_mem_eq
    refine ⟨y, hex_within, hdec,
      ⟨hex_within.bounded hrep.bounded, hy0, hymem_x ▸ hrep.kwise_rep,
        hymem_x ▸ hrep.table_inv⟩, ?_⟩
    intro a _
    exact hymem_x.symm ▸ rfl
  | insert u₀ v =>
    have hu₀ : u₀ = u := rfl
    have hc_br : (Cond.eq (22 : Fin 24) 10).Holds x₃ := by
      simp [Cond.Holds, hx₃_22_eq, harg.2.1, hx₃_10]
    obtain ⟨y, ⟨n4, hn4, hex4⟩, hymem, hy0, _⟩ :=
      insertFinishCode_execWithin u v p
        hx₃_0 hx₃_1 hx₃_2 hx₃_4 hx₃_5 hx₃_6 hx₃_10
        (hx₃_23_eq.trans harg.2.2) hfit_space
    have he_br : Exec w (.branch (.eq 22 10) insertFinishCode getFinishCode) x₃ y (n4 + 1) :=
      Exec.branch_pos hc_br hex4
    have hall : Exec w (opCode n_max) x y (n1 + (n2 + (n3 + (n4 + 1)))) :=
      hex1.seq (hex2.seq (hex3.seq he_br))
    have hex_within : ExecWithin w (opCode n_max) x y
        (KWise.evalSteps n_max U (tableLog n_max) 5 + 12 * t + 27) :=
      ⟨_, by omega, hall⟩
    have hymem_x : y.mem = insertMem base n_max x.mem p u.val v := by
      rw [hymem, hx₃_mem_eq]
    have hp_lt : p.val < tableSize n_max := p.isLt
    have hkrep_y : KWise.Rep base (KWise.chunkBits n_max) U (tableLog n_max) 5 θ y.mem :=
      kwise_rep_congr hrep.kwise_rep fun a ha _ => by
        rw [hymem_x]
        dsimp only [insertMem, usedBase, keyBase, valBase, tableSize]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
    have htable_y : TableInv U V n_max base θ (Function.update s u₀ (some v)) y.mem := by
      rw [hu₀, hymem_x]
      exact hrep.table_inv.insert_mem u v (by simpa only [hu₀] using hvalid)
    have hmod_y : Modifies (Block.mk base (space n_max)).footprint x.mem y.mem := by
      intro a ha
      rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
      rw [hymem_x]
      dsimp only [insertMem, usedBase, keyBase, valBase, space, tableSize] at ha ⊢
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
    exact ⟨y, hex_within, rfl, ⟨hex_within.bounded hrep.bounded, hy0, hkrep_y, htable_y⟩, hmod_y⟩

/-! ## Section 4: `SubroutineDS` certificate and expected-time sequence theorem -/

/-- **`SubroutineDS` certificate for open-addressed linear probing on the randomized Word RAM**
over `Cslib.WordRAM.Basis.exact`:
- **Space**: `space n_max = KWise.space n_max 5 + 3 * 2 ^ (tableLog n_max) = O(n_max)` words;
- **Initialization time**: `setupTime U n_max = KWise.initTableSteps n_max U (tableLog n_max) + 38
  = O(n_max + log U)` expected instructions;
- **Operation charge**: `charge U n_max = KWise.evalSteps n_max U (tableLog n_max) 5 + 3483
  = O(L ^ 2 + 1)` expected instructions per `get` or `insert`, which is `O(1)` whenever
  `U ≤ n_max ^ c` for any constant `c`;
- **Potential**: `0` (`seedSlack := 1`). -/
@[expose] noncomputable def subroutineDS (U V n_max w base : ℕ)
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w)
    (hfit_space : Fits w (base + space n_max))
    (hfit_V : Fits w V) :
    Cslib.WordRAM.Randomized.SubroutineDS (subroutineCode U n_max)
      (Dictionary.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) where
  Seed := Seed U n_max
  seedLaw := seedLaw U n_max
  seedSlack := 1
  space := space n_max
  spanTime := 3
  setupTime := setupTime U n_max
  initPotential := 0
  charge _ _ := charge U n_max
  rep θ s x := Rep U V n_max w base θ s x
  potential _ _ := 0
  encode := encodeOp
  argMatch := argMatchOp
  decode := decodeOp
  bounded h := h.bounded
  rep_unique h₁ h₂ := h₁.unique h₂
  arguments_fit {s} o hvalid i hi := by
    have hfit_U : Fits w U := fits_U_of_hw hw
    have hfit_1 : Fits w 1 :=
      hfit_space.of_le (by dsimp only [space]; have := tableSize_pos n_max; omega)
    have hfit_0 : Fits w 0 := hfit_space.of_le (Nat.zero_le _)
    cases o with
    | get u =>
      dsimp only [encodeOp]
      split_ifs
      · exact hfit_U.of_le (le_of_lt u.isLt)
      · exact hfit_0
    | insert u v =>
      dsimp only [encodeOp]
      split_ifs
      · exact hfit_U.of_le (le_of_lt u.isLt)
      · exact hfit_1
      · exact hfit_V.of_le (le_of_lt hvalid.2)
      · exact hfit_0
  encode_matches o regs := by
    cases o with
    | get u =>
      exact ⟨rfl, rfl⟩
    | insert u v =>
      exact ⟨rfl, rfl, rfl⟩
  rep_supported hregs hmem hbdd hrep := hrep.supported hregs hmem hbdd
  potential_supported _ _ _ := rfl
  clear_nodup := by
    change ([21, 19, 20, 0, 18] : List (Fin 24)).Nodup
    decide
  params_not_clear j := j.elim0
  incCur_eval {x} h20 hfit := by
    have h20' : x.regs 20 = 1 := h20
    have hev : BinOp.add.evalExact (x.regs 21) (x.regs 20) = some (x.regs 21 + 1) := by
      simp [BinOp.evalExact, h20']
    change (Op.exactBin .add 21 21 20).eval w x = some (x.set 21 (x.regs 21 + 1))
    rw [Op.eval_exactBin, hev]
    exact Data.put_of_fits hfit
  span_exec _ hfr _ := by
    obtain ⟨x₁, hex, hmem, hb, hfr'⟩ := allocSpan_execWithin hfr hfit_space
    exact ⟨x₁, hex, hmem, hb, hfr', fun j => j.elim0⟩
  setup_exec hx₁ hb hfr _ hz :=
    initSetup_exec hw hfit_space hx₁ hb hfr hz
  step_exec {s} o ν hvalid hseed hsupp := by
    classical
    let u := opKey o
    let hasInv : Seed U n_max × Data rLP → Prop := fun p =>
      Rep U V n_max w base p.1 s p.2 ∧ argMatchOp o p.2.regs
    let y : Seed U n_max × Data rLP → Data rLP := fun p =>
      if hp : hasInv p then
        Classical.choose (opCode_execWithin hw hfit_space hfit_V hp.1 o hvalid hp.2)
      else p.2
    let T_probe : Seed U n_max × Data rLP → ℕ := fun p =>
      if hp : hasInv p then
        hp.1.table_inv.probeLen u (hashFn U n_max p.1 u)
      else 0
    let T_step : Seed U n_max × Data rLP → ℝ≥0∞ := fun p =>
      (KWise.evalSteps n_max U (tableLog n_max) 5 + 12 * T_probe p + 27 : ℕ)
    refine ⟨fun p => PMF.pure (p.1, y p), T_step, ?_, ?_, ?_⟩
    · intro p hp_mem
      have hp : hasInv p := hsupp p hp_mem
      have hspec := Classical.choose_spec
        (opCode_execWithin hw hfit_space hfit_V hp.1 o hvalid hp.2)
      rcases hspec with ⟨hex, hdec, hrep', hmod⟩
      have hy_eq : y p =
          Classical.choose (opCode_execWithin hw hfit_space hfit_V hp.1 o hvalid hp.2) := by
        simp only [y, hp, ↓reduceDIte]
      have hT_eq : T_probe p = hp.1.table_inv.probeLen u (hashFn U n_max p.1 u) := by
        simp only [T_probe, hp, ↓reduceDIte]
      refine ⟨?_, ?_⟩
      · have hdist := ExecCodeDist.of_execWithin hex
        refine hdist.congr_dist ?_ ?_
        · simp [hy_eq]
        · dsimp only [T_step]
          rw [hT_eq]
      · intro q hq
        rw [PMF.support_pure, Set.mem_singleton_iff] at hq
        subst hq
        exact ⟨by simpa only [hy_eq] using hdec,
          by simpa only [hy_eq] using hrep',
          by simpa only [hy_eq] using hmod⟩
    · intro θ'
      have hmap_eq : (ν.bind fun p => PMF.pure (p.1, y p)).map Prod.fst = ν.map Prod.fst := by
        rw [PMF.map_bind]
        simp only [PMF.pure_map]
        rfl
      rw [hmap_eq]
      exact hseed θ'
    · simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero]
      have htsum_probe : (∑' p, ν p * (T_probe p : ℝ≥0∞)) ≤ 288 := by
        apply tsum_probeLen_le (V := V) (base := base) (s := s) u ν
        · intro θ
          simpa only [one_mul] using hseed θ
        · intro p hp_mem
          have hp : hasInv p := hsupp p hp_mem
          exact ⟨p.2.mem, hp.1.table_inv, by simp only [T_probe, hp, ↓reduceDIte, le_rfl]⟩
      calc (∑' p, ν p * T_step p)
          = ∑' p, ν p *
              ((KWise.evalSteps n_max U (tableLog n_max) 5 + 27 : ℝ≥0∞) +
                12 * (T_probe p : ℝ≥0∞)) := by
            refine tsum_congr fun p => ?_
            dsimp only [T_step]
            simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
            ring_nf
        _ = (∑' p, ν p * (KWise.evalSteps n_max U (tableLog n_max) 5 + 27 : ℝ≥0∞)) +
              12 * (∑' p, ν p * (T_probe p : ℝ≥0∞)) := by
            simp_rw [mul_add, tsum_add, ← mul_assoc, mul_comm (ν _) 12, mul_assoc,
              ENNReal.tsum_mul_left]
        _ = (KWise.evalSteps n_max U (tableLog n_max) 5 + 27 : ℝ≥0∞) +
              12 * (∑' p, ν p * (T_probe p : ℝ≥0∞)) := by
            rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
        _ ≤ (KWise.evalSteps n_max U (tableLog n_max) 5 + 27 : ℝ≥0∞) + 12 * 288 := by
            gcongr
        _ = (charge U n_max : ℝ≥0∞) := by
            dsimp only [charge]
            simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
            ring_nf

/-- Standard-basis (`Basis.standard`) `SubroutineDS` certificate for linear probing, transported
from `subroutineDS` via `SubroutineDS.toStandard`. -/
noncomputable def subroutineDSStandard (U V n_max w base : ℕ)
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w)
    (hfit_space : Fits w (base + space n_max))
    (hfit_V : Fits w V) :
    Cslib.WordRAM.Randomized.SubroutineDS
      (subroutineCode U n_max).toStandard
      (Dictionary.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) :=
  (subroutineDS U V n_max w base hw hfit_space hfit_V).toStandard

/-- **Expected amortized multi-operation theorem for linear probing**: for any admissible sequence
`ops : List (Dictionary.Op U)` starting from the empty dictionary on fresh zeroed memory and fixed
independently of the sampled hash seed (oblivious adversary), `initFresh` followed by the
subroutine operation bodies (`SubroutineDS.ExecSteps`) executes with total expected instruction
count at most `3 + setupTime U n_max + ops.length * charge U n_max` (excluding caller argument
delivery, caller dispatch loops, and host-level code specialization). -/
theorem seq_expected_amortized (U V n_max w base : ℕ)
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w)
    (hfit_space : Fits w (base + space n_max))
    (hfit_V : Fits w V)
    {x₀ : Data rLP}
    (hx₀ : x₀.Bounded w)
    (hfr : x₀.regs 18 = base)
    (hz : ∀ a ∈ (Block.mk base (space n_max)).footprint, x₀.mem a = 0)
    (ops : List (Dictionary.Op U))
    (hvalid : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    ∃ (ν₀ ν_f : PMF (Seed U n_max × Data rLP))
      (T_ops : ℝ≥0∞),
      ExecCodeDist w (subroutineCode U n_max).initFresh x₀
        (ν₀.map Prod.snd) (3 + setupTime U n_max : ℕ) ∧
      (subroutineDS U V n_max w base hw hfit_space hfit_V).ExecSteps
        (Dictionary.empty U) ops ν₀ ν_f T_ops ∧
      (3 + setupTime U n_max : ℕ) + T_ops ≤
        (3 + setupTime U n_max + ops.length * charge U n_max : ℕ) := by
  let C := subroutineDS U V n_max w base hw hfit_space hfit_V
  obtain ⟨ν₀, ν_f, T_ops, hinit, hsteps, _, _, hbound⟩ :=
    C.seq_expected_amortized ops hx₀ hfr (fun j => Fin.elim0 j) hz hvalid
  have htotal : (Dictionary.spec U V n_max).totalCost C.charge (Dictionary.empty U) ops =
      ops.length * charge U n_max := by
    have hconst : ∀ s (l : List (Dictionary.Op U)),
        (Dictionary.spec U V n_max).totalCost (fun _ _ => charge U n_max) s l =
          l.length * charge U n_max := by
      intro s l
      induction l generalizing s with
      | nil => simp [Stateful.Spec.totalCost]
      | cons o tl ih =>
        simp only [Stateful.Spec.totalCost, ih, List.length_cons]
        ring
    exact hconst (Dictionary.empty U) ops
  have hinitTime : C.initTime = ((3 + setupTime U n_max : ℕ) : ℝ≥0∞) := by
    dsimp only [Cslib.WordRAM.Randomized.SubroutineDS.initTime, C, subroutineDS]
    push_cast
    rfl
  rw [hinitTime] at hinit hbound
  have hpot0 : (∑' q, ν_f q * (C.potential q.1 q.2 : ℝ≥0∞)) = 0 := by
    simp [C, subroutineDS]
  have hinitPot0 : (C.initPotential : ℝ≥0∞) = 0 := Nat.cast_zero
  rw [htotal, hpot0, hinitPot0, add_zero, add_zero] at hbound
  have hbound' : ((3 + setupTime U n_max : ℕ) : ℝ≥0∞) + T_ops ≤
      (3 + setupTime U n_max + ops.length * charge U n_max : ℕ) := by
    simpa only [← Nat.cast_add] using hbound
  exact ⟨ν₀, ν_f, T_ops, hinit, hsteps, hbound'⟩

end Cslib.Algorithms.WordRAM.Dictionary.LinearProbing
