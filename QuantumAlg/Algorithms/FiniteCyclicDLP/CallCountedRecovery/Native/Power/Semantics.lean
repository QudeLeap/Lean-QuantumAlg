/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Power
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Store.Ext
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization.Restricted

/-!
# Full records and values of the actual declared group-power scan

The square writes before the branch reads its candidate bit. This order is
preserved even for aliased references. The mathematical exponent invariant
uses structural separation only where a stable candidate value is needed;
the actual full-state equation and caller frame require no encoded input.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G] {ctx : RuntimeCtx .quantum} {width : Nat}

/-- The declared square writes its computed word in the same actual store. -/
def squareStore (A : Access G width) (accumulator : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) : Store ctx :=
  store.write accumulator (A.square (store.read (powerRead accumulator)))

/-- The declared multiplication uses the same encoder and captured generator. -/
def multiplyStore (A : Access G width) (generator : G)
    (accumulator : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  store.write accumulator (A.multiply (store.read (powerRead accumulator)) (A.encode generator))

private theorem square_execute (A : Access G width)
    (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (squareCall A accumulator writable).execute Reference state =
      state.mapClassical (fun entry => (squareStore A accumulator entry.1,
          (entry.2, (() : (squareCall A accumulator writable).Path)))) := by
  change state.mapClassical _ = _
  congr 1

private theorem multiply_execute (A : Access G width) (generator : G)
    (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (multiplyCall A generator accumulator writable).execute Reference state =
      state.mapClassical (fun entry =>
        (multiplyStore A generator accumulator entry.1,
          (entry.2, (() : (multiplyCall A generator accumulator writable).Path)))) := by
  change state.mapClassical _ = _
  congr 1

/-- Actual multiplication choice and its real selected-arm path. -/
def powerChoiceRecord (A : Access G width) (generator : G)
    (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (powerChoice A generator accumulator writable value).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => (multiplyStore A generator accumulator store, ())

private theorem choice_execute (A : Access G width) (generator : G)
    (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (powerChoice A generator accumulator writable value).execute Reference state =
      state.mapClassical (fun entry =>
        ((powerChoiceRecord A generator accumulator writable value entry.1).1,
          (entry.2, (powerChoiceRecord A generator accumulator writable value entry.1).2))) := by
  cases value with
  | bit value =>
      cases value
      · refine (Circuit.execute_id_mapClassical Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · refine (multiply_execute A generator accumulator writable Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _

/-- The branch reads the actual store returned by the preceding square. -/
def powerStepRecord (A : Access G width) (generator : G) (bit : CInputRef ctx .bit)
    (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (store : Store ctx) : Store ctx × (powerStep A generator bit accumulator writable).Path :=
  let squared := squareStore A accumulator store
  let value := squared.read bit
  let selected := powerChoiceRecord A generator accumulator writable value squared
  (selected.1, ((), ⟨value, selected.2⟩))

/-- Every reference matrix block follows the actual square, read and selected multiplication. -/
theorem groupPowerStep_execute (A : Access G width) (generator : G) (bit : CInputRef ctx .bit)
    (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (powerStep A generator bit accumulator writable).execute Reference state =
      state.mapClassical (fun entry =>
        ((powerStepRecord A generator bit accumulator writable entry.1).1,
          (entry.2, (powerStepRecord A generator bit accumulator writable entry.1).2))) := by
  exact Circuit.execute_sequenceRecord (squareCall A accumulator writable)
    (.branch bit (powerChoice A generator accumulator writable))
    (fun store => (squareStore A accumulator store, ()))
    (fun store =>
      let value := store.read bit
      let chosen := powerChoiceRecord A generator accumulator writable value store
      (chosen.1, ⟨value, chosen.2⟩))
    (by
      intro Reference History finite state
      refine (square_execute A accumulator writable Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (Circuit.execute_branch_mapClassical bit _ (powerChoiceRecord A generator accumulator writable)
      (choice_execute A generator accumulator writable)) Reference state

/-- The original range record retains every actual intermediate store and branch value. -/
def powerRangeRecord (A : Access G width) (generator : G) (count : Nat)
    (bits : Fin count → CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (store : Store ctx) :
    Store ctx × (powerRange A generator count bits accumulator writable).Path :=
  Circuit.forRangeRecord count
    (fun index => powerStep A generator (bits index) accumulator writable)
    (fun index => powerStepRecord A generator (bits index) accumulator writable) store

/-- The full actual scan records all existing quantum, reference, store and history correlations. -/
theorem groupPowerRange_execute (A : Access G width) (generator : G) (count : Nat)
    (bits : Fin count → CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (powerRange A generator count bits accumulator writable).execute Reference state =
      state.mapClassical (fun entry =>
        ((powerRangeRecord A generator count bits accumulator writable entry.1).1,
          (entry.2, (powerRangeRecord A generator count bits accumulator writable entry.1).2))) :=
  Circuit.execute_forRangeRecord count _ _
    (fun index => groupPowerStep_execute A generator (bits index) accumulator writable)
    Reference state

/-- The single step frames every structural read outside its actual accumulator key. -/
theorem groupPowerStep_preserves_read (A : Access G width) (generator : G)
    (bit : CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (separate : accumulator.key ∉ other.storageKeys) :
    (powerStepRecord A generator bit accumulator writable store).1.read other =
      store.read other := by
  change (powerChoiceRecord A generator accumulator writable
    ((squareStore A accumulator store).read bit) (squareStore A accumulator store)).1.read other = _
  generalize (squareStore A accumulator store).read bit = value
  cases value with
  | bit value =>
      cases value
      · exact Store.read_write_of_not_mem_storageKeys store accumulator _ other separate
      · exact (Store.read_write_of_not_mem_storageKeys _ accumulator _ other separate).trans
          (Store.read_write_of_not_mem_storageKeys store accumulator _ other separate)

/-- No position of the complete scan modifies any other actual caller observation. -/
theorem groupPowerRange_preserves_read (A : Access G width) (generator : G) (count : Nat)
    (bits : Fin count → CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (separate : accumulator.key ∉ other.storageKeys) :
    (powerRangeRecord A generator count bits accumulator writable store).1.read other =
      store.read other := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      exact (ih (fun index => bits index.succ)
        (powerStepRecord A generator (bits 0) accumulator writable store).1).trans
          (groupPowerStep_preserves_read A generator (bits 0) accumulator writable
            store other separate)

/-- On encoded data, one actual stable-bit step advances the exponent by its MSB digit. -/
theorem groupPowerStep_encode (A : Access G width) (generator : G)
    (bit : CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (store : Store ctx) (exponent : Nat)
    (encoded : store.read (powerRead accumulator) = A.encode (generator ^ exponent))
    (separate : accumulator.key ∉ bit.storageKeys) :
    (powerStepRecord A generator bit accumulator writable store).1.read (powerRead accumulator) =
      A.encode (generator ^ (2 * exponent + (store.read bit).toBool.toNat)) := by
  have bitSame : (squareStore A accumulator store).read bit = store.read bit :=
    Store.read_write_of_not_mem_storageKeys store accumulator _ bit separate
  change (powerChoiceRecord A generator accumulator writable
    ((squareStore A accumulator store).read bit) (squareStore A accumulator store)).1.read
      (powerRead accumulator) = _
  rw [bitSame]
  have original := GroupPowerRecovery.step_encode A.groupPowerAccess generator exponent
    (store.read bit).toBool
  have output : (powerChoiceRecord A generator accumulator writable (store.read bit)
      (squareStore A accumulator store)).1.read (powerRead accumulator) =
      GroupPowerRecovery.step A.groupPowerAccess generator
        (store.read (powerRead accumulator)) (store.read bit).toBool := by
    generalize store.read bit = value
    cases value with
    | bit value =>
        cases value <;>
          simp [powerChoiceRecord, squareStore, multiplyStore, powerRead,
            GroupPowerRecovery.step, Access.groupPowerAccess, Store.read_write_same,
            CShape.Value.toBool]
  rw [output, encoded]
  exact original.trans (by
    congr 2
    cases (store.read bit).toBool <;> rfl)

/-- The actual ordered scan computes the original MSB accumulator fold on encoded data. -/
theorem groupPowerRange_encode (A : Access G width) (generator : G) (count : Nat)
    (bits : Fin count → CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (store : Store ctx) (exponent : Nat)
    (encoded : store.read (powerRead accumulator) = A.encode (generator ^ exponent))
    (separate : ∀ index, accumulator.key ∉ (bits index).storageKeys) :
    (powerRangeRecord A generator count bits accumulator writable store).1.read
        (powerRead accumulator) =
      A.encode (generator ^ ClassicalAlgorithms.TerminalDecode.accumulatorFold count exponent
        (fun index => (store.read (bits index)).toBool)) := by
  induction count generalizing exponent store with
  | zero => exact encoded
  | succ count ih =>
      have first := groupPowerStep_encode A generator (bits 0) accumulator writable
        store exponent encoded (separate 0)
      have remaining := ih (fun index => bits index.succ)
        (powerStepRecord A generator (bits 0) accumulator writable store).1
        (2 * exponent + (store.read (bits 0)).toBool.toNat) first
        (fun index => separate index.succ)
      have reads :
          (fun index : Fin count =>
            ((powerStepRecord A generator (bits 0) accumulator writable store).1.read
              (bits index.succ)).toBool) =
            (fun index : Fin count => (store.read (bits index.succ)).toBool) := by
        funext index
        rw [groupPowerStep_preserves_read A generator (bits 0) accumulator writable
          store (bits index.succ) (separate index.succ)]
      rw [reads] at remaining
      exact remaining

private theorem tail_fold (size : Nat) (positive : 0 < size)
    (word : CShape.Value (.unsignedWord size))
    (leading : (word.wordBitGet ⟨0, positive⟩).toBool = false) :
    ClassicalAlgorithms.TerminalDecode.accumulatorFold (size - 1) 0
      (fun index => (word.wordBitGet (tailIndex size index)).toBool) = word.toNat := by
  cases size with
  | zero => omega
  | succ tail => exact word_tailAccumulatorFold_eq_toNat tail word leading

/-- A raw-range word has the omitted zero MSB by the original capacity theorem. -/
theorem groupPowerScan_encode (P : Parameters G)
    (candidate : CInputRef ctx (.unsignedWord P.width))
    (accumulator : CWriteRef ctx (.unsignedWord P.width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (store : Store ctx)
    (encoded : store.read (powerRead accumulator) = P.access.encode 1)
    (separate : accumulator.key ∉ candidate.storageKeys)
    (candidateBound : (store.read candidate).toNat < P.spec.modulus) :
    (powerRangeRecord P.access P.generator (P.width - 1)
      (fun index => .wordBitGet candidate (tailIndex P.width index))
      accumulator writable store).1.read (powerRead accumulator) =
        P.access.encode (P.generator ^ (store.read candidate).toNat) := by
  have computed := groupPowerRange_encode P.access P.generator (P.width - 1)
    (fun index => .wordBitGet candidate (tailIndex P.width index)) accumulator writable store 0
    (by simpa only [pow_zero] using encoded) (fun _ => separate)
  have leading := P.candidate_leadingBit_false (store.read candidate) candidateBound
  have folded := tail_fold P.width P.width_pos (store.read candidate) leading
  exact computed.trans (congrArg (fun value => P.access.encode (P.generator ^ value)) folded)

/-- Actual fresh allocation supplies the identity and separates all original candidate reads. -/
theorem groupPowerAccumulator_initialized {inner : RuntimeCtx .quantum}
    (P : Parameters G) (candidate : CInputRef ctx (.unsignedWord P.width))
    (cells : Cells inner [.unsignedWord P.width]) (transport : Transport ctx inner)
    (separated : cells.TransportSeparated transport) (store : Store inner)
    (initialized : cells.Initialized store)
    (candidateBound : (store.read (transport.liftInput candidate)).toNat < P.spec.modulus) :
    let actual := powerRangeRecord P.access P.generator (P.width - 1)
      (fun index => .wordBitGet (transport.liftInput candidate) (tailIndex P.width index))
      cells.head.ref (Or.inl cells.head.role) store
    actual.1.read (powerRead cells.head.ref) =
        P.access.encode (P.generator ^ (store.read (transport.liftInput candidate)).toNat) ∧
      transport.restrict actual.1 = transport.restrict store := by
  have identity : store.read (powerRead cells.head.ref) = P.access.encode 1 := by
    cases cells with
    | cons cell rest => exact initialized.1.trans P.access.encode_one.symm
  have avoids : ∀ {shape : CShape} (input : CInputRef ctx shape),
      cells.head.ref.key ∉ (transport.liftInput input).storageKeys := by
    cases cells with
    | cons cell rest => exact separated.1
  refine ⟨groupPowerScan_encode P (transport.liftInput candidate) cells.head.ref
    (Or.inl cells.head.role) store identity (avoids candidate) candidateBound, ?_⟩
  apply transport.workspaceTransport_readsAs_restrict_iff.mp
  intro shape other
  exact (groupPowerRange_preserves_read P.access P.generator (P.width - 1)
    (fun index => .wordBitGet (transport.liftInput candidate) (tailIndex P.width index))
    cells.head.ref (Or.inl cells.head.role) store (transport.liftInput other) (avoids other)).trans
      (transport.workspaceTransport_restrict_readsAs store other)

/-- The lexical accumulator and its continuation have one actual full-state record.

The continuation supplies its own real execution equation. Initialization and
release are performed by the existing workspace instruction; no caller store
is assumed to contain a zero accumulator or an encoded candidate.
-/
theorem groupPowerAccumulator_actualRecord (A : Access G width) (generator : G)
    (candidate : CInputRef ctx (.unsignedWord width))
    (body : ∀ {inner : RuntimeCtx .quantum}, CInputRef inner (.unsignedWord width) →
      Transport ctx inner → Circuit inner inner)
    (bodyRecords : ∀ {inner : RuntimeCtx .quantum}
      (input : CInputRef inner (.unsignedWord width)) (transport : Transport ctx inner),
      Store inner → Store inner × (body input transport).Path)
    (bodyEquations : ∀ {inner : RuntimeCtx .quantum}
      (input : CInputRef inner (.unsignedWord width)) (transport : Transport ctx inner)
      (Reference : Register) {History : Type} [Fintype History]
      (state : State inner Reference History),
      (body input transport).execute Reference state = state.mapClassical (fun entry =>
        ((bodyRecords input transport entry.1).1,
          (entry.2, (bodyRecords input transport entry.1).2)))) :
    ∃ record : Store ctx → Store ctx × (withPowerAccumulator A generator candidate body).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withPowerAccumulator A generator candidate body).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2))) := by
  obtain ⟨record, equation, _⟩ :=
    withCells_actualRecord_initialized_restricted_post ctx [.unsignedWord width]
      (fun cells _ transport _ =>
        .seq (powerScan A generator (transport.liftInput candidate) cells.head.ref
          (Or.inl cells.head.role)) (body (powerRead cells.head.ref) transport))
      (fun _ _ => True) (by
        intro inner cells _distinct transport _separated
        let scan := powerScan A generator (transport.liftInput candidate)
          cells.head.ref (Or.inl cells.head.role)
        let first := powerRangeRecord A generator (width - 1)
          (fun index => .wordBitGet (transport.liftInput candidate) (tailIndex width index))
          cells.head.ref (Or.inl cells.head.role)
        refine ⟨Circuit.sequenceRecord scan (body (powerRead cells.head.ref) transport) first
          (bodyRecords (powerRead cells.head.ref) transport), ?_, by intros; trivial⟩
        exact Circuit.execute_sequenceRecord scan (body (powerRead cells.head.ref) transport)
          first (bodyRecords (powerRead cells.head.ref) transport)
          (groupPowerRange_execute A generator (width - 1)
            (fun index => .wordBitGet (transport.liftInput candidate) (tailIndex width index))
            cells.head.ref (Or.inl cells.head.role))
          (bodyEquations (powerRead cells.head.ref) transport))
  exact ⟨record, equation⟩

end

end QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native
