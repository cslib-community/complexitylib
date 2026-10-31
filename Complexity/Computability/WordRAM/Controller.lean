/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Dynamic
public import Complexity.Foundations.Semantics.Stateful.Hoare

/-!
# Machine certificates for stateful controllers

`Refines` relates a mathematical free-monad client to a fixed structured RAM program. Unlike
an operation-count contract, its budget bounds an actual execution, including controller
instructions and argument preparation. The final halt is added by `Refines.executes_demonic`
(and `Refines.executes` for deterministic specifications).

The intermediate assertions record how answers are represented in registers or memory. The
bind rule uses one continuation code fragment for every intermediate answer: Lean's semantic
continuation is not an uncharged machine computation. Likewise returning a pure answer requires
an execution certificate. Initialization is supplied as code using `Refines.prepend`.

## Main definitions

* `Refines`: demonic caller admissibility, angelic client run semantics, and bounded RAM execution
  with a relational postcondition.

## Main results

* `refines_iff_ofFn`: equivalence with the functional `runClient` formulation on deterministic
  specifications (`[D.HasStepFn f]`).
* `Refines.bind`, `Refines.bind_ofFn`, `Refines.branch`: sequential and conditional controller
  certificates.
* `Refines.call`: inlining a dynamic operation after charged register preparation.
* `Refines.executes_demonic`, `Refines.executes`: a complete flat-program run, including its final
  halt.

## References

The clients reuse Quang Dao's upstream `PFunctor.FreeM`. Machine execution and assembly reuse
the word-RAM calculus based on the lean-trominoes formalization; see `WordRAM.Defs`.
-/

@[expose] public section

namespace Cslib.WordRAM

universe u v z a

variable {D : Stateful.Spec.{u, v, z}} {α β : Type a} {B : Basis} {r w : ℕ}

/-- A fixed machine fragment certifies that the client `p` is demonically admissible
(`D.DemonicValid`) and implements a permitted `D.ClientRun` and its result/state representation,
within a bound depending on the initial abstract and concrete states.
As for `ExecWithin`, word boundedness is an entry assertion obligation: include `Data.Bounded`
in `pre` when reasoning about arbitrary machine data. Standard `Data.init` inputs are bounded
whenever `InputFits` holds. -/
def Refines (w : ℕ) (pre : D.State → Data r → Prop) (p : D.Client α)
    (post : α → D.State → Data r → Prop) (budget : D.State → Data r → ℕ)
    (code : Code B r) : Prop :=
  ∀ s x, pre s x →
    D.DemonicValid s p ∧
      ∃ y a s' tr, D.ClientRun s p a s' tr ∧
        ExecWithin w code x y (budget s x) ∧
        post a s' y

/-- On a deterministic specification (`[D.HasStepFn f]`), `Refines` is equivalent to
`D.ValidHistory s (D.clientHistory s p)` and `post (D.clientResult s p) (D.clientState s p) y`. -/
theorem refines_iff_ofFn {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (w : ℕ) (pre : D.State → Data r → Prop) (p : D.Client α)
    (post : α → D.State → Data r → Prop) (budget : D.State → Data r → ℕ)
    (code : Code B r) :
    Refines w pre p post budget code ↔
      ∀ s x, pre s x → D.ValidHistory s (D.clientHistory s p) ∧
        ∃ y, ExecWithin w code x y (budget s x) ∧
          post (D.clientResult s p) (D.clientState s p) y := by
  refine forall_congr' fun s => forall_congr' fun x => imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨_, y, a, s', tr, hrun, he, hy⟩
    obtain ⟨hv, rfl, rfl, _⟩ := (D.clientRun_iff_runClient s p a s' tr).mp hrun
    exact ⟨hv, y, he, hy⟩
  · rintro ⟨hv, y, he, hy⟩
    exact ⟨(D.demonicValid_iff_validHistory_runClient s p).mpr hv,
      y, _, _, _, D.clientRun_canonical s p hv, he, hy⟩

namespace Refines

variable {pre pre' : D.State → Data r → Prop} {post post' : α → D.State → Data r → Prop}
  {p : D.Client α} {code : Code B r} {budget budget' : D.State → Data r → ℕ}

/-- Construct a `Refines` proof on a deterministic specification (`[D.HasStepFn f]`) from
`D.ValidHistory` and `D.clientResult` / `D.clientState` / `D.clientHistory`. -/
theorem ofFn {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (h : ∀ s x, pre s x → D.ValidHistory s (D.clientHistory s p) ∧
      ∃ y, ExecWithin w code x y (budget s x) ∧
        post (D.clientResult s p) (D.clientState s p) y) :
    Refines w pre p post budget code :=
  (refines_iff_ofFn w pre p post budget code).mpr h

/-- Unpack a `Refines` proof on a deterministic specification (`[D.HasStepFn f]`) into
`D.ValidHistory` and `D.clientResult` / `D.clientState` / `D.clientHistory`. -/
theorem toOfFn {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (h : Refines w pre p post budget code) {s : D.State} {x : Data r} (hx : pre s x) :
    D.ValidHistory s (D.clientHistory s p) ∧
      ∃ y, ExecWithin w code x y (budget s x) ∧
        post (D.clientResult s p) (D.clientState s p) y :=
  (refines_iff_ofFn w pre p post budget code).mp h s x hx

/-- Strengthen an entry assertion, weaken the exit assertion, or increase the instruction bound. -/
theorem consequence (h : Refines w pre p post budget code)
    (hp : ∀ s x, pre' s x → pre s x)
    (hq : ∀ a s x, post a s x → post' a s x)
    (ht : ∀ s x, pre' s x → budget s x ≤ budget' s x) :
    Refines w pre' p post' budget' code := by
  intro s x hx
  obtain ⟨hvp, y, a, s', tr, hrun, he, hy⟩ := h s x (hp s x hx)
  exact ⟨hvp, y, a, s', tr, hrun, he.mono (ht s x hx), hq a s' y hy⟩

/-- Even a pure semantic computation needs actual code realizing its output assertion. -/
theorem pure (a : α)
    (h : ∀ s x, pre s x → ∃ y, ExecWithin w code x y (budget s x) ∧ post a s y) :
    Refines w pre (.pure a) post budget code := by
  intro s x hx
  obtain ⟨y, he, hy⟩ := h s x hx
  exact ⟨.pure s a, y, a, s, [], .pure s a, he, hy⟩

/-- Compose with one fixed continuation fragment valid for every represented intermediate answer.
The continuation budget is evaluated at the state actually reached by the first fragment, while
`hvalid` ensures demonic continuation admissibility across all permitted specification outcomes of
`p`. -/
theorem bind {mid : α → D.State → Data r → Prop} {post : β → D.State → Data r → Prop}
    {k : α → D.Client β} {first : D.State → Data r → ℕ}
    {next : α → D.State → Data r → ℕ} {c₁ c₂ : Code B r}
    (hp : Refines w pre p mid first c₁)
    (hk : ∀ a, Refines w (mid a) (k a) post (next a) c₂)
    (ht : ∀ s x, pre s x → ∀ a s' y, mid a s' y →
      first s x + next a s' y ≤ budget s x)
    (hvalid : ∀ s x, pre s x → ∀ a s' tr, D.ClientRun s p a s' tr → D.DemonicValid s' (k a)) :
    Refines w pre (p.bind k) post budget (.seq c₁ c₂) := by
  intro s x hx
  obtain ⟨hvp, y, a, s₁, tr₁, hrun₁, he₁, hy⟩ := hp s x hx
  obtain ⟨_, z, b, s₂, tr₂, hrun₂, he₂, hz⟩ := hk a s₁ y hy
  exact ⟨hvp.bind (hvalid s x hx), z, b, s₂, tr₁ ++ tr₂, hrun₁.bind hrun₂,
    (he₁.seq he₂).mono (ht s x hx a s₁ y hy), hz⟩

/-- On a deterministic specification (`[D.HasStepFn f]`), sequential composition automatically
discharges demonic continuation admissibility from `hk` at the unique reached outcome. -/
theorem bind_ofFn {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {mid : α → D.State → Data r → Prop} {post : β → D.State → Data r → Prop}
    {k : α → D.Client β} {first : D.State → Data r → ℕ}
    {next : α → D.State → Data r → ℕ} {c₁ c₂ : Code B r}
    (hp : Refines w pre p mid first c₁)
    (hk : ∀ a, Refines w (mid a) (k a) post (next a) c₂)
    (ht : ∀ s x, pre s x → ∀ a s' y, mid a s' y →
      first s x + next a s' y ≤ budget s x) :
    Refines w pre (p.bind k) post budget (.seq c₁ c₂) := by
  refine bind hp hk ht fun s x hx a s' tr hrun => ?_
  obtain ⟨_, y, a₁, s₁, tr₁, hrun₁, _, hy⟩ := hp s x hx
  obtain ⟨_, rfl, rfl, _⟩ := (D.clientRun_iff_runClient s p a s' tr).mp hrun
  obtain ⟨_, rfl, rfl, _⟩ := (D.clientRun_iff_runClient s p a₁ s₁ tr₁).mp hrun₁
  exact (hk _ _ y hy).1

/-- A machine branch must test the same proposition as the semantic client. Both paths include
all their control instructions; the common bound allows the larger two-instruction overhead. -/
theorem branch (b : Prop) [Decidable b] {cond : Cond r} {yes no : D.Client α}
    {pos neg : Code B r}
    (hc : ∀ s x, pre s x → (cond.Holds x ↔ b))
    (hp : Refines w (fun s x => pre s x ∧ b) yes post budget pos)
    (hn : Refines w (fun s x => pre s x ∧ ¬b) no post budget neg) :
    Refines w pre (if b then yes else no) post (fun s x => budget s x + 2)
      (.branch cond pos neg) := by
  intro s x hx
  by_cases hb : b
  · obtain ⟨hvp, y, a, s', tr, hrun, he, hy⟩ := hp s x ⟨hx, hb⟩
    refine ⟨by simpa only [ite_eq_left hb] using hvp,
      y, a, s', tr, by simpa only [ite_eq_left hb] using hrun,
      (he.branch_pos ((hc s x hx).mpr hb)).mono (by dsimp only; omega), hy⟩
  · obtain ⟨hvn, y, a, s', tr, hrun, he, hy⟩ := hn s x ⟨hx, hb⟩
    refine ⟨by simpa only [ite_eq_right hb] using hvn,
      y, a, s', tr, by simpa only [ite_eq_right hb] using hrun,
      he.branch_neg (fun h => hb ((hc s x hx).mp h)), hy⟩

/-- Charge initialization or argument computation preceding a certified client. The prefix
preserves the abstract initial state, while establishing its concrete entry representation. -/
theorem prepend {entry : D.State → Data r → Prop} {init : Code B r}
    {setup : D.State → Data r → ℕ}
    (hinit : ∀ s x, pre s x → ∃ y, ExecWithin w init x y (setup s x) ∧ entry s y)
    (h : Refines w entry p post budget code)
    (ht : ∀ s x, pre s x → ∀ y, entry s y → setup s x + budget s y ≤ budget' s x) :
    Refines w pre p post budget' (.seq init code) := by
  intro s x hx
  obtain ⟨y, hi, hy⟩ := hinit s x hx
  obtain ⟨hvp, z, a, s', tr, hrun, he, hz⟩ := h s y hy
  exact ⟨hvp, z, a, s', tr, hrun, (hi.seq he).mono (ht s x hx y hy), hz⟩

/-- Discharge a client's abstract postcondition using an independently proved semantic contract. -/
theorem hoare {abstractPre : D.State → Prop} {abstractPost : α → D.State → Prop}
    (h : Refines w pre p post budget code) (hspec : D.Hoare abstractPre p abstractPost)
    (hp : ∀ s x, pre s x → abstractPre s) :
    Refines w pre p (fun a s y => post a s y ∧ abstractPost a s) budget code := by
  intro s x hx
  obtain ⟨hvp, y, a, s', tr, hrun, he, hy⟩ := h s x hx
  exact ⟨hvp, y, a, s', tr, hrun, he, hy, (hspec s (hp s x hx)).2 a s' tr hrun⟩

/-- A certificate produces a real halting machine execution realizing a valid `D.ClientRun`. -/
theorem executes_demonic (h : Refines w pre p post budget code) (out : Fin r) (encode : α → ℕ)
    (hout : ∀ a s y, post a s y → y.regs out = encode a) {s : D.State} {x : Data r}
    (hx : pre s x) :
    ∃ a s' tr n, D.ClientRun s p a s' tr ∧
      Executes w (code.program out) ⟨0, x⟩ (encode a) n ∧
      n ≤ budget s x + 1 := by
  obtain ⟨_, y, a, s', tr, hrun, ⟨n, hn, he⟩, hy⟩ := h s x hx
  refine ⟨a, s', tr, n + 1, hrun, ?_, Nat.add_le_add_right hn 1⟩
  simpa only [hout a s' y hy] using he.executes out

/-- On a deterministic specification (`[D.HasStepFn f]`), a certificate produces a real halting
machine execution returning `encode (D.clientResult s p)`. -/
theorem executes {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (h : Refines w pre p post budget code) (out : Fin r) (encode : α → ℕ)
    (hout : ∀ a s y, post a s y → y.regs out = encode a) {s : D.State} {x : Data r}
    (hx : pre s x) :
    ∃ n, Executes w (code.program out) ⟨0, x⟩ (encode (D.clientResult s p)) n ∧
      n ≤ budget s x + 1 := by
  obtain ⟨a, s', tr, n, hrun, hexec, hn⟩ := h.executes_demonic out encode hout hx
  obtain ⟨_, rfl, _, _⟩ := (D.clientRun_iff_runClient s p a s' tr).mp hrun
  exact ⟨n, hexec, hn⟩

/-- Inline a dynamic operation after a machine-certified preparation fragment. The body bound
excludes a halt because execution continues in the caller; only the complete program halts. -/
theorem call {P : DynamicProgram D r} (C : DynamicCertificate P w) (o : D.Op)
    {prep : Code .standard r} {setup body : D.State → Data r → ℕ}
    (hp : ∀ s x, pre s x → C.rep s x ∧ D.valid s o)
    (hprep : ∀ s x, pre s x →
      ExecWithin w prep x (P.prepare o x) (setup s x))
    (hbody : ∀ s x, pre s x → ∀ y n, Exec w P.code (P.prepare o x) y n → n ≤ body s x) :
    Refines w pre (.liftBind o fun a => .pure a)
      (fun a s y => C.rep s y ∧ P.decode o y.regs = some a)
      (fun s x => setup s x + body s x) (.seq prep P.code) := by
  intro s x hx
  obtain ⟨hr, hv⟩ := hp s x hx
  obtain ⟨y, s', a, n, he, hstep, ha, hy⟩ := C.execute o hr hv
  exact ⟨.liftBind o (fun a => .pure a) hv (fun s'' a' _ => .pure s'' a'),
    y, a, s', [⟨o, a, s'⟩],
    .liftBind o (fun a => .pure a) a hv hstep (.pure s' a),
    (hprep s x hx).seq ⟨n, hbody s x hx y n he, he⟩, hy, ha⟩

end Refines
end Cslib.WordRAM
