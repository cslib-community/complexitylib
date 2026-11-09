/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeDictionary

/-!
# Retaining native bucket hits directly in a reusable dictionary

The retained side of the dissection consumes each actual linked bucket hit,
evaluates the full second quarter, and immediately inserts its state and packed
witnesses into the native sparse dictionary. No output array is materialized.
The dictionary's release chain is derived from these inserts and can be freed
with `Dictionary.release_exec`. This is one bucket consumer, not the full class
iterator or an original-input dissection endpoint. The sparse-RAM model and
its difference from the source's sorted-list implementation are documented in
`AddXNORNativeDictionary`.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Load one actual first-quarter hit and retain its full second-quarter state. -/
@[expose] def retainBody : Code .standard 32 :=
  .seq (ram[ address ← link + one; state ← *address; address ← address + one;
    firstOperators ← *address; link ← *link ]) (.seq evaluate Dictionary.put)

/-- Consume exactly the matching bucket's linked hits. -/
@[expose] def retainLoop : Code .standard 32 := .loop (.lt zero link) retainBody

/-- The semantic records of the hits; these records are proof observers, never
inputs to a native instruction. Equal full states may replace stored witnesses. -/
def retainedEntries {m : ℕ} (as : List (BitVec m)) (v : ℕ) (rs : List (ℕ × ℕ)) :
    List Dictionary.Entry := rs.map fun (s, u) =>
  ⟨(eval ((decode as.length v).zip as) (BitVec.ofNat m s)).toNat, u, v⟩

/-- The actual retained dictionary exposes a single originating bucket record,
not two unrelated existential witnesses. This derives payload correctness from
the insertion stream; the bucket's original-quarter semantics are still separate. -/
theorem retained_provenance {m : ℕ} (D t q : ℕ) (mem : ℕ → ℕ)
    (as : List (BitVec m)) (v : ℕ) (rs : List (ℕ × ℕ))
    (hzero : mem (Dictionary.slot D q) = 0)
    (hit : Dictionary.filledMemory D (retainedEntries as v rs) mem t
      (Dictionary.slot D q) ≠ 0) :
    ∃ r ∈ rs,
      (eval ((decode as.length v).zip as) (BitVec.ofNat m r.1)).toNat = q ∧
      Dictionary.filledMemory D (retainedEntries as v rs) mem t
        (Dictionary.slot D q) = r.2 + 1 ∧
      Dictionary.filledMemory D (retainedEntries as v rs) mem t
        (Dictionary.slot D q + 1) = v := by
  obtain ⟨e, he, hq, hu, hv⟩ :=
    Dictionary.filledMemory_provenance D (retainedEntries as v rs) mem t q hzero hit
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
  exact ⟨r, hr, hq, hu, hv⟩

/-- Direct native retention, without the materializing emitter. The bucket and
operand cells lie below the sparse dictionary, so insertion preserves all later
reads. Index bounds come from first-quarter preparation. All chain evaluations,
lookup/address/admin operations, stores and loop control are charged. -/
theorem retainLoop_exec {W m a b boundary ptr D t v : ℕ} (as : List (BitVec m))
    (rs : List (ℕ × ℕ)) (x : Data 32)
    (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (hv : x.regs operators = v) (hfv : Fits W v)
    (hl : x.regs link = ptr) (hD : x.regs Dictionary.table = D)
    (ht : x.regs Dictionary.top = t) (hone : x.regs one = 1) (hz : x.regs zero = 0)
    (hlinked : Linked x.mem boundary ptr rs) (hboundary : boundary ≤ D)
    (hinputEnd : b + as.length ≤ D)
    (hinput : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hstates : ∀ r ∈ rs, r.1 < 2 ^ m)
    (hindices : ∀ r ∈ rs, r.2 < 2 ^ a)
    (hfit : Fits W (D + boundary + b + as.length + 8 * 2 ^ m + 2 ^ a + 4)) :
    ∃ y, ExecWithin W retainLoop x y (rs.length * (11 * as.length + 30) + 2) ∧
      y.mem = Dictionary.filledMemory D (retainedEntries as v rs) x.mem t ∧
      y.regs Dictionary.top = Dictionary.filledTop D (retainedEntries as v rs) x.mem t ∧
      y.regs link = 0 ∧ y.regs one = 1 ∧ y.regs zero = 0 := by
  induction rs generalizing x ptr t with
  | nil =>
    cases hlinked
    refine ⟨x, ?_, rfl, ht, hl, hone, hz⟩
    simpa only [List.length_nil, Nat.zero_mul, Nat.zero_add, retainLoop] using
      (ExecWithin.loop_exit (w := W) (x := x) (cond := .lt zero link) (body := retainBody)
        (by simp [Cond.holds_lt, hz, hl]))
  | cons r rs ih =>
    obtain ⟨s, u⟩ := r
    cases hlinked with
    | cons hp hnode hs hu htail =>
      have hsLt := hstates (s, u) List.mem_cons_self
      have huLt := hindices (s, u) List.mem_cons_self
      have ha1 : Fits W (ptr + 1) := hfit.of_le (by omega)
      have ha2 : Fits W (ptr + 2) := hfit.of_le (by omega)
      let loaded := x.set address (ptr + 1) |>.set state s |>.set address (ptr + 2)
        |>.set firstOperators u |>.set link (x.mem ptr)
      have heLoad : ExecWithin (B := .standard) W
          (ram[ address ← link + one; state ← *address; address ← address + one;
            firstOperators ← *address; link ← *link ]) x loaded 5 := by
        ram_eval [loaded, hl, hone, hs, hu, ha1, ha2, address, link, one, state,
          firstOperators, Fin.mk.injEq, Nat.add_assoc]
      obtain ⟨z, heEval, zs, _, _, zm, _, _⟩ := evaluate_exec as (BitVec.ofNatLT s hsLt) loaded
        (v := v)
        (by simpa +decide [loaded, base, address, state, firstOperators, link] using hb)
        (by simpa +decide [loaded, count, address, state, firstOperators, link] using hc)
        (by simpa +decide [loaded, modulus, address, state, firstOperators, link] using hn)
        (by simp +decide [loaded, state, address, firstOperators, link])
        (by simpa +decide [loaded, operators, address, state, firstOperators, link] using hv) hfv
        hinput (hfit.of_le (by omega))
      have frame (r : Fin 32) (hr : evaluate.Preserves r) : z.regs r = loaded.regs r :=
        heEval.regs_eq hr
      let result := eval ((decode as.length v).zip as) (BitVec.ofNat m s)
      have zr : z.regs state = result.toNat := by
        simpa only [result, BitVec.ofNatLT_eq_ofNat] using zs
      have zu : z.regs firstOperators = u := by
        rw [frame firstOperators (by decide)]
        simp +decide [loaded, firstOperators, link]
      have zv : z.regs operators = v := by
        rw [frame operators (by decide)]
        simpa +decide [loaded, operators, address, state, firstOperators, link] using hv
      have zD : z.regs Dictionary.table = D := by
        rw [frame Dictionary.table (by decide)]
        simpa +decide [loaded, Dictionary.table, address, state, firstOperators, link] using hD
      have zt : z.regs Dictionary.top = t := by
        rw [frame Dictionary.top (by decide)]
        simpa +decide [loaded, Dictionary.top, address, state, firstOperators, link] using ht
      obtain ⟨next, hePut, nm, nt, no, nz⟩ := Dictionary.put_exec z zD zt zr zu zv
        (hfit.of_le (by have := result.isLt; omega))
      have heBody : ExecWithin W retainBody x next (11 * as.length + 28) :=
        (heLoad.seq (heEval.seq hePut)).mono (by omega)
      have nmem : next.mem = Dictionary.putMemory x.mem D t result.toNat u v := by
        simpa only [zm, loaded, Data.set_mem] using nm
      have ntop : next.regs Dictionary.top =
          (if x.mem (Dictionary.slot D result.toNat) = 0 then result.toNat + 1 else t) := by
        simpa only [zm, loaded, Data.set_mem] using nt
      have memoryFrame (q : ℕ) (hq : q < D) : next.mem q = x.mem q := by
        rw [nmem, Dictionary.putMemory_below _ _ _ _ _ _ _ hq]
      have nlinked : Linked next.mem boundary (x.mem ptr) rs :=
        htail.frame (fun q hq => memoryFrame q (by omega))
      have ninput : ∀ i (hi : i < as.length), next.mem (b + i) = as[i].toNat := by
        intro i hi
        rw [memoryFrame _ (by omega)]
        exact hinput i hi
      obtain ⟨y, heTail, ym, yt, yl, yo, yz⟩ := ih next
        ((heBody.regs_eq (by decide)).trans hb)
        ((heBody.regs_eq (by decide)).trans hc)
        ((heBody.regs_eq (by decide)).trans hn)
        ((heBody.regs_eq (by decide)).trans hv)
        (by
          rw [hePut.regs_eq (by decide), frame link (by decide)]
          simp [loaded])
        ((heBody.regs_eq (by decide)).trans hD) ntop no nz nlinked ninput
        (fun r hr => hstates r (List.mem_cons_of_mem _ hr))
        (fun r hr => hindices r (List.mem_cons_of_mem _ hr))
      refine ⟨y, ?_, ?_, ?_, yl, yo, yz⟩
      · exact (ExecWithin.loop_iter (by simp only [Cond.holds_lt, hz, hl]; exact hp)
          heBody heTail).mono (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)
      · simpa only [retainedEntries, List.map_cons, Dictionary.filledMemory, nmem, result] using ym
      · simpa only [retainedEntries, List.map_cons, Dictionary.filledTop, nmem, result] using yt

/-- A valid dictionary and its release chain are produced from the hit stores.
No assumption about the final chain or final distinct-state count is needed. -/
theorem retained_valid {m D t : ℕ} {mem : ℕ → ℕ} {ks : List ℕ}
    (h : Dictionary.Valid mem D t ks) (as : List (BitVec m)) (v : ℕ) (rs : List (ℕ × ℕ)) :
    ∃ keys, Dictionary.Valid
        (Dictionary.filledMemory D (retainedEntries as v rs) mem t) D
        (Dictionary.filledTop D (retainedEntries as v rs) mem t) keys ∧
      keys.length ≤ ks.length + rs.length := by
  obtain ⟨keys, hk, hl, _⟩ := Dictionary.filled_valid h (retainedEntries as v rs)
  exact ⟨keys, hk, by simpa only [retainedEntries, List.length_map] using hl⟩

/-- A complete retained-bucket lifetime. Release visits only distinct stored
states and restores all original memory, including unread input. -/
@[expose] def retainLifetime : Code .standard 32 := .seq retainLoop Dictionary.release

/-- Native retention and release have an output-sensitive unconditional cost.
The original record list is a semantic observer of the native bucket; no final
correctness, release-stack or resource conclusion is a hypothesis. -/
theorem retainLifetime_exec {W m a b boundary ptr D v : ℕ} (as : List (BitVec m))
    (rs : List (ℕ × ℕ)) (x : Data 32)
    (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (hv : x.regs operators = v) (hfv : Fits W v)
    (hl : x.regs link = ptr) (hD : x.regs Dictionary.table = D)
    (ht : x.regs Dictionary.top = 0) (hone : x.regs one = 1) (hz : x.regs zero = 0)
    (hlinked : Linked x.mem boundary ptr rs) (hboundary : boundary ≤ D)
    (hinputEnd : b + as.length ≤ D)
    (hinput : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hstates : ∀ r ∈ rs, r.1 < 2 ^ m) (hindices : ∀ r ∈ rs, r.2 < 2 ^ a)
    (hzero : ∀ q, D ≤ q → x.mem q = 0)
    (hfit : Fits W (D + boundary + b + as.length + 8 * 2 ^ m + 2 ^ a + 4)) :
    ∃ y, ExecWithin W retainLifetime x y (rs.length * (11 * as.length + 42) + 7) ∧
      y.mem = x.mem ∧ y.regs Dictionary.top = 0 := by
  obtain ⟨z, he, zm, zt, _⟩ := retainLoop_exec as rs x hb hc hn hv hfv hl hD ht hone hz
    hlinked hboundary hinputEnd hinput hstates hindices hfit
  obtain ⟨keys, hk, hlen, hkeys, hrestore⟩ := Dictionary.filled_release
    (retainedEntries as v rs) hzero
  have zk : Dictionary.Valid z.mem D (z.regs Dictionary.top) keys := by rwa [zm, zt]
  obtain ⟨y, hy, ym, yt⟩ := Dictionary.release_exec (W := W) (D := D) keys z
    ((he.regs_eq (by decide)).trans hD) rfl zk.chain zk.nodup (hfit.of_le (by
      have := Nat.two_pow_pos m
      have := Nat.two_pow_pos a
      omega))
    (by
      intro q hq
      obtain ⟨e, he, rfl⟩ := hkeys q hq
      obtain ⟨⟨s, u⟩, _, rfl⟩ := List.mem_map.mp he
      have hs := (eval ((decode as.length v).zip as) (BitVec.ofNat m s)).isLt
      exact hfit.of_le (by
        dsimp only
        have := Nat.two_pow_pos m
        have := Nat.two_pow_pos a
        omega))
  refine ⟨y, (he.seq hy).mono ?_, ?_, yt⟩
  · simp only [retainedEntries, List.length_map] at hlen
    nlinarith
  · rw [ym, zm]
    exact hrestore

/-- Every continuing prefix of one native retained-bucket lifetime has bounded
words and finite occupied support, linear in this bucket's hit count. Memory
is exactly restored at the boundary. This is not a peak bound for an unproved
all-class execution or a multitape bit-time theorem. -/
theorem retainLifetime_resources {W m a b boundary ptr D v : ℕ} (as : List (BitVec m))
    (rs : List (ℕ × ℕ)) (x : Data 32) (S : Finset ℕ)
    (hx : x.Bounded W) (hS : ∀ q, x.mem q ≠ 0 → q ∈ S)
    (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (hv : x.regs operators = v) (hfv : Fits W v)
    (hl : x.regs link = ptr) (hD : x.regs Dictionary.table = D)
    (ht : x.regs Dictionary.top = 0) (hone : x.regs one = 1) (hz : x.regs zero = 0)
    (hlinked : Linked x.mem boundary ptr rs) (hboundary : boundary ≤ D)
    (hinputEnd : b + as.length ≤ D)
    (hinput : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hstates : ∀ r ∈ rs, r.1 < 2 ^ m) (hindices : ∀ r ∈ rs, r.2 < 2 ^ a)
    (hzero : ∀ q, D ≤ q → x.mem q = 0)
    (hfit : Fits W (D + boundary + b + as.length + 8 * 2 ^ m + 2 ^ a + 4)) :
    let T := rs.length * (11 * as.length + 42) + 7
    ∃ y n ts, n + 1 ≤ T + 1 ∧ TraceExec W retainLifetime x y n ts ∧
      Executes W (retainLifetime.program Dictionary.top) ⟨0, x⟩ 0 (n + 1) ∧
      y.mem = x.mem ∧ ∀ k u, Runs W (retainLifetime.program Dictionary.top) ⟨0, x⟩ u k →
        k ≤ n → u.data.Bounded W ∧ ∃ live : Finset ℕ,
          (∀ q, u.data.mem q ≠ 0 ↔ q ∈ live) ∧
          (live.card + 32) * W ≤ (S.card + T + 32) * W := by
  dsimp only
  obtain ⟨y, ⟨n, hnTime, he⟩, hm, ht⟩ := retainLifetime_exec as rs x hb hc hn hv hfv hl hD ht
    hone hz hlinked hboundary hinputEnd hinput hstates hindices hzero hfit
  obtain ⟨ts, htrace⟩ := he.exists_trace
  refine ⟨y, n, ts, by omega, htrace, ?_, hm, ?_⟩
  · simpa only [ht] using he.executes Dictionary.top
  · intro k u hu hk
    obtain ⟨cover, hcard, hcover⟩ := hu.exists_memorySupport S hS
    refine ⟨hu.bounded hx, cover.filter (fun q => u.data.mem q ≠ 0), ?_, ?_⟩
    · intro q
      simp only [Finset.mem_filter]
      exact ⟨fun hq => ⟨hcover q hq, hq⟩, And.right⟩
    · apply Nat.mul_le_mul_right
      have := Finset.card_filter_le cover (fun q => u.data.mem q ≠ 0)
      omega

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
