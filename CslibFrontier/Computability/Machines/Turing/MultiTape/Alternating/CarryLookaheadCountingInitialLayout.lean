/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCounting
public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.CountingInput

/-!
# The words constructed before a native count-bit evaluation

Seven derived words begin blank beside the preserved predicate context. Five native projections
install the count, width, routing metadata, control header and root status. Native depth
preparation then installs the binary height and unary depth. The completed layout is exactly
the existing evaluator's initial configuration, with every head at zero and no emitted output.
-/

public section

namespace Turing.MultiTapeATM.CarryLookaheadCountingInitialLayout

open MultiTapeTM Cslib.Circuits.Boolean.CarryLookahead.Query
open CarryLookaheadCountingLayout (size)

/-- The seven words that preparation derives from the raw binary parameters. -/
structure Fields where
  /-- Binary height of the carry-save counting tree. -/
  height : List Bool := []
  /-- Unary frontier for the same tree depth. -/
  unary : List Bool := []
  /-- Binary number of predicate values to count. -/
  count : List Bool := []
  /-- Binary arithmetic width. -/
  width : List Bool := []
  /-- The encoded initial carry-lookahead routing position. -/
  metadata : List Bool := []
  /-- The native word-game control header. -/
  header : List Bool := []
  /-- The root status word, initially blank and later `[false]`. -/
  status : List Bool := []
  deriving DecidableEq

/-- Read one of the five words produced directly from the raw parameter record. -/
@[expose] def Fields.get (fields : Fields) : CountingInput.Field → List Bool
  | .count => fields.count
  | .width => fields.width
  | .metadata => fields.metadata
  | .header => fields.header
  | .status => fields.status

/-- Replace one projected word, retaining the other fields and both depth counters. -/
@[expose] def Fields.set (fields : Fields) : CountingInput.Field → List Bool → Fields
  | .count, word => { fields with count := word }
  | .width, word => { fields with width := word }
  | .metadata, word => { fields with metadata := word }
  | .header, word => { fields with header := word }
  | .status, word => { fields with status := word }

/-- A projected field update affects exactly the selected field. -/
@[simp] theorem Fields.get_set (fields : Fields) (field other : CountingInput.Field)
    (word : List Bool) :
    (fields.set field word).get other = if other = field then word else fields.get other := by
  cases field <;> cases other <;> rfl

/-- The raw root layout permits the status word to be blank before its native installation. -/
@[expose] def rootWords (k : ℕ) (context : List Bool) (fields : Fields)
    (i : Fin (k + 12)) : List Bool :=
  if i.val = 0 then fields.height else if i.val = 3 then fields.status
  else if i.val = 4 then fields.unary else if i.val = 6 then context
  else if i.val = 7 then fields.count else if i.val = 8 then fields.width else []

/-- The root, terminal preparation, and routing blocks with every unspecified word blank. -/
@[expose] def words (k r q : ℕ) (context : List Bool) (fields : Fields) :
    Fin (size k r q) → List Bool :=
  Fin.append
    (Fin.append (rootWords k context fields)
      (Fin.append (fun _ : Fin (r + 1) => []) ![fields.metadata, []]))
    (WordGameRound.tapeWords q fields.header [] [])

/-- The binary height occupies root tape zero. -/
abbrev height (k r q : ℕ) : Fin (size k r q) := 0

/-- The unary depth occupies root tape four. -/
abbrev unary (k r q : ℕ) : Fin (size k r q) :=
  ⟨4, by unfold size CountingTerminalLayout.size; omega⟩

/-- The predicate context is preserved on root tape six. -/
abbrev contextTape (k r q : ℕ) : Fin (size k r q) :=
  ⟨6, by unfold size CountingTerminalLayout.size; omega⟩

/-- The five projection destinations use the evaluator's actual root and controller coordinates. -/
@[expose] def destination (k r q : ℕ) : CountingInput.Field → Fin (size k r q)
  | .count => ⟨7, by unfold size CountingTerminalLayout.size; omega⟩
  | .width => ⟨8, by unfold size CountingTerminalLayout.size; omega⟩
  | .metadata => CarryLookaheadCountingLayout.metadata k r q
  | .header => CarryLookaheadCountingLayout.control k r q
  | .status => ⟨3, by unfold size CountingTerminalLayout.size; omega⟩

/-- The complete root block is the explicit layout with its mutable status word. -/
@[simp] theorem words_root (k r q : ℕ) (context : List Bool) (fields : Fields)
    (i : Fin (k + 12)) :
    words k r q context fields ((i.castAdd (r + 1 + 2)).castAdd (q + 4)) =
      rootWords k context fields i := by
  simp only [words, Fin.append_left]

/-- Reading a projection destination gives its named field. -/
@[simp] theorem words_destination (k r q : ℕ) (context : List Bool) (fields : Fields)
    (field : CountingInput.Field) :
    words k r q context fields (destination k r q field) = fields.get field := by
  cases field with
  | count =>
    change words k r q context fields
      (((⟨7, by omega⟩ : Fin (k + 12)).castAdd (r + 1 + 2)).castAdd (q + 4)) = fields.count
    rw [words_root]
    simp [rootWords]
  | width =>
    change words k r q context fields
      (((⟨8, by omega⟩ : Fin (k + 12)).castAdd (r + 1 + 2)).castAdd (q + 4)) = fields.width
    rw [words_root]
    simp [rootWords]
  | status =>
    change words k r q context fields
      (((⟨3, by omega⟩ : Fin (k + 12)).castAdd (r + 1 + 2)).castAdd (q + 4)) = fields.status
    rw [words_root]
    simp [rootWords]
  | metadata | header =>
    simp [words, destination, Fields.get, CarryLookaheadCountingLayout.metadata,
      CarryLookaheadCountingLayout.control, CarryLookaheadCountingLayout.terminalEmbedding,
      CarryLookaheadCountingLayout.roundControl, CountingTerminalLayout.metadata,
      CountingTerminalPrepare.metadata,
      WordGameRound.tapeWords]

/-- Reading the height tape gives its current binary word. -/
@[simp] theorem words_height (k r q : ℕ) (context : List Bool) (fields : Fields) :
    words k r q context fields (height k r q) = fields.height := by
  change words k r q context fields
    (((⟨0, by omega⟩ : Fin (k + 12)).castAdd (r + 1 + 2)).castAdd (q + 4)) = fields.height
  rw [words_root]
  simp [rootWords]

/-- Reading the depth tape gives its current unary word. -/
@[simp] theorem words_unary (k r q : ℕ) (context : List Bool) (fields : Fields) :
    words k r q context fields (unary k r q) = fields.unary := by
  change words k r q context fields
    (((⟨4, by omega⟩ : Fin (k + 12)).castAdd (r + 1 + 2)).castAdd (q + 4)) = fields.unary
  rw [words_root]
  simp [rootWords]

/-- The long predicate context is independent of every derived field. -/
@[simp] theorem words_context (k r q : ℕ) (context : List Bool) (fields : Fields) :
    words k r q context fields (contextTape k r q) = context := by
  change words k r q context fields
    (((⟨6, by omega⟩ : Fin (k + 12)).castAdd (r + 1 + 2)).castAdd (q + 4)) = context
  rw [words_root]
  simp [rootWords]

/-- A projection changes exactly its selected physical word. -/
theorem words_update_field (k r q : ℕ) (context : List Bool) (fields : Fields)
    (field : CountingInput.Field) (word : List Bool) :
    Function.update (words k r q context fields) (destination k r q field) word =
      words k r q context (fields.set field word) := by
  apply Function.update_eq_iff.mpr
  constructor
  · rw [words_destination, Fields.get_set]
    simp
  · intro i hi
    have hv : i.val ≠ (destination k r q field).val := fun h => hi (Fin.ext h)
    cases field <;> cases i using Fin.addCases with
    | left i =>
      cases i using Fin.addCases with
      | left i =>
        simp_all [words, rootWords, Fields.set, destination]
      | right i =>
        cases i using Fin.addCases with
        | left i => simp [words, Fields.set]
        | right i =>
          fin_cases i <;>
            simp_all [words, Fields.set, destination, CarryLookaheadCountingLayout.metadata,
              CountingTerminalLayout.metadata,
              CountingTerminalPrepare.metadata]
    | right i =>
      cases i using Fin.addCases with
      | left i => simp [words, Fields.set, WordGameRound.tapeWords]
      | right i =>
        fin_cases i <;>
          simp_all [words, Fields.set, destination, WordGameRound.tapeWords,
            CarryLookaheadCountingLayout.control, CarryLookaheadCountingLayout.roundControl]

/-- Lift one root-word update to the complete evaluator block, preserving routing metadata
and the separate controller header. -/
theorem words_update_root (k r q : ℕ) (context : List Bool) (fields fields' : Fields)
    (i : Fin (k + 12)) (word : List Bool)
    (hvalue : word = rootWords k context fields' i)
    (hother : ∀ j ≠ i, rootWords k context fields j = rootWords k context fields' j)
    (hmetadata : fields.metadata = fields'.metadata) (hheader : fields.header = fields'.header) :
    Function.update (words k r q context fields) ((i.castAdd (r + 1 + 2)).castAdd (q + 4))
      word = words k r q context fields' := by
  have hroot : Function.update (rootWords k context fields) i word =
      rootWords k context fields' := Function.update_eq_iff.mpr ⟨hvalue, hother⟩
  funext j
  cases j using Fin.addCases with
  | left j =>
    cases j using Fin.addCases with
    | left j =>
      simpa [words, Function.update_apply] using congrFun hroot j
    | right j =>
      simp [words, hmetadata, (Fin.castAdd_ne_natAdd i j).symm]
  | right j =>
    simp [words, hheader,
      (Fin.castAdd_ne_natAdd (i.castAdd (r + 1 + 2)) j).symm]

/-- Native binary-height preparation changes only root tape zero. -/
theorem words_update_height (k r q : ℕ) (context : List Bool) (fields : Fields)
    (word : List Bool) :
    Function.update (words k r q context fields) (height k r q) word =
      words k r q context { fields with height := word } := by
  refine words_update_root k r q context fields { fields with height := word }
    ⟨0, by omega⟩ word rfl ?_ rfl rfl
  intro i hi
  have hv : i.val ≠ 0 := fun h => hi (Fin.ext h)
  simp [rootWords, hv]

/-- Native unary-depth preparation changes only root tape four. -/
theorem words_update_unary (k r q : ℕ) (context : List Bool) (fields : Fields)
    (word : List Bool) :
    Function.update (words k r q context fields) (unary k r q) word =
      words k r q context { fields with unary := word } := by
  refine words_update_root k r q context fields { fields with unary := word }
    ⟨4, by omega⟩ word rfl ?_ rfl rfl
  intro i hi
  have hv : i.val ≠ 4 := fun h => hi (Fin.ext h)
  simp [rootWords, hv]

/-- Depth preparation reads the projected binary count from root tape seven. -/
@[simp] theorem words_count (k r q : ℕ) (context : List Bool) (fields : Fields) :
    words k r q context fields ⟨7, by unfold size CountingTerminalLayout.size; omega⟩ =
      fields.count := words_destination k r q context fields .count

/-- Distinct projected fields occupy distinct physical tapes. -/
theorem destination_injective (k r q : ℕ) : Function.Injective (destination k r q) := by
  intro field other h
  have hv := congrArg Fin.val h
  clear h
  cases field <;> cases other <;> try rfl
  all_goals
    simp only [destination, CarryLookaheadCountingLayout.metadata,
      CarryLookaheadCountingLayout.terminalEmbedding, Fin.castAddEmb_apply,
      CarryLookaheadCountingLayout.control, CarryLookaheadCountingLayout.roundControl,
      CountingTerminalLayout.metadata,
      CountingTerminalPrepare.metadata, CountingTerminalLayout.size,
      Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero] at hv
    omega

/-- Before preparation every word outside the context tape is blank. -/
theorem words_empty_of_ne_context (k r q : ℕ) (context : List Bool)
    (i : Fin (size k r q)) (hi : i ≠ contextTape k r q) :
    words k r q context {} i = [] := by
  have hv : i.val ≠ 6 := fun h => hi (Fin.ext h)
  cases i using Fin.addCases with
  | left i =>
    cases i using Fin.addCases with
    | left i =>
      simp only [Fin.val_castAdd] at hv
      simp [words, rootWords, hv]
    | right i =>
      cases i using Fin.addCases with
      | left i => simp [words]
      | right i => fin_cases i <;> simp [words]
  | right i =>
    cases i using Fin.addCases with
    | left i => simp [words, WordGameRound.tapeWords]
    | right i => fin_cases i <;> simp [words, WordGameRound.tapeWords]

/-- The raw evaluator block contains only the separately supplied predicate context. -/
theorem words_empty (k r q : ℕ) (context : List Bool) :
    words k r q context {} = Function.update (fun _ => []) (contextTape k r q) context := by
  funext i
  by_cases hi : i = contextTape k r q
  · subst i
    rw [words_context, Function.update_self]
  · rw [words_empty_of_ne_context k r q context i hi, Function.update_of_ne hi]

/-- The completed words are determined by the raw binary count and query parameters. -/
@[expose] def canonical (a : CountingInput.Input) : Fields where
  height := encNat (Nat.clog 2 a.count)
  unary := encUnary (Nat.clog 2 a.count)
  count := encNat a.count
  width := encNat a.query.width
  metadata := Routing.encPosition (Initial.position a.query)
  header := [a.query.claim, false]
  status := [false]

private theorem rootWords_canonical (k : ℕ) (context : List Bool) (a : CountingInput.Input) :
    rootWords k context (canonical a) =
      CarrySaveLeafLayout.words k context (encNat a.count) (encNat a.query.width)
        (encNat (Nat.clog 2 a.count)) [] [] (encUnary (Nat.clog 2 a.count)) false := by
  funext i
  simp only [rootWords, canonical, CarrySaveLeafLayout.words]
  split_ifs <;> first | rfl | omega

private theorem prep_words (r : ℕ) (p : Routing.Position) :
    CountingTerminalPrepare.words r p [] =
      Fin.append (fun _ : Fin (r + 1) => []) ![Routing.encPosition p, []] := by
  funext i
  cases i using Fin.addCases with
  | left i =>
    have hne := Fin.castAdd_ne_natAdd i (0 : Fin 2)
    simp [CountingTerminalPrepare.words, CountingTerminalPrepare.metadata,
      CountingTerminalPrepare.flags, Function.update_apply, hne]
  | right i =>
    have hne := (Fin.castAdd_ne_natAdd (Fin.last r) i).symm
    simp only [CountingTerminalPrepare.words, CountingTerminalPrepare.flags,
      Function.update_of_ne hne, CountingTerminalPrepare.metadata, Fin.append_right]
    fin_cases i <;>
      simp

private theorem root_initial (k : ℕ) (input context : List Bool) (a : CountingInput.Input) :
    CarrySaveCountingRoot.initial k input context a.count a.query.width 0 =
      { tapesCfg input (rootWords k context (canonical a)) 0 0 [] with inputPos := 0 } := by
  rw [CarrySaveCountingRoot.initial, CarrySaveLeafLayout.initial_nil_eq_tapesCfg,
    rootWords_canonical]
  rfl

private theorem storage_eq_tapesCfg (k r q : ℕ) (input context : List Bool)
    (a : CountingInput.Input) :
    CarryLookaheadCountingLayout.storage k r q input context a.count a.query.width
      (Initial.position a.query) =
      { tapesCfg input (words k r q context { canonical a with header := [] }) 0 0 []
          with inputPos := 0 } := by
  unfold CarryLookaheadCountingLayout.storage CountingTerminalLayout.storage
  rw [root_initial]
  apply Cfg.ext <;> try rfl
  · funext i z
    cases i using Fin.addCases with
    | left i =>
      cases i using Fin.addCases with
      | left i => simp [words, rootWords, tapesCfg]
      | right i =>
        simp [words, CountingTerminalPrepare.config, prep_words, tapesCfg, canonical]
    | right i =>
      simp [words, WordGameRound.config, WordGameRound.queryConfig, tapesCfg]
  · funext i
    cases i using Fin.addCases with
    | left i =>
      cases i using Fin.addCases <;> simp [CountingTerminalPrepare.config, tapesCfg]
    | right i => simp [WordGameRound.config, WordGameRound.queryConfig, tapesCfg]

/-- Completing all seven derived words yields exactly the actual evaluator's initial storage. -/
theorem initial_eq_tapesCfg (k r q : ℕ) (input context : List Bool) (a : CountingInput.Input) :
    CarryLookaheadCounting.initial k r q input context a.count a.query.width a.query.bit
      a.query.claim =
      { tapesCfg input (words k r q context (canonical a)) 0 0 [] with inputPos := 0 } := by
  change WordGameLeaf.config (CarryLookaheadCountingLayout.control k r q) none
    (wordGameHeader (Routing.player (Initial.position a.query))) 0
    (CarryLookaheadCountingLayout.storage k r q input context a.count a.query.width
      (Initial.position a.query)) = _
  rw [Initial.header_position, storage_eq_tapesCfg]
  apply Cfg.ext <;> try rfl
  · funext i z
    have hwords := congrFun (words_update_field k r q context
      { canonical a with header := [] } .header [a.query.claim, false]) i
    have ht := congrArg (fun word => tapeOfList word z) hwords
    by_cases hi : i = CarryLookaheadCountingLayout.control k r q <;>
      simpa [WordGameLeaf.config, tapesCfg, Function.update_apply, destination, Fields.set,
        canonical, hi] using ht
  · funext i
    simp [WordGameLeaf.config, tapesCfg]

end Turing.MultiTapeATM.CarryLookaheadCountingInitialLayout
