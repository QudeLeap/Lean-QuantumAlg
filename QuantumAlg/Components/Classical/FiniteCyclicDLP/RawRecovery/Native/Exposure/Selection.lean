/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Copy
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Selection.Semantics
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization

/-!
# Actual selected three-cell exposure

The real status controls the existing normalized recovery. Actual payload
initialization supplies the failure values; successful recovery supplies its
computed candidate and reconstruction bit. The three native copies then
write their exact values in order, preserving every other caller entry.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalWorkspace NormalizedRecovery.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual selected branch either writes its computed payload or leaves the old one intact. -/
theorem selectedRecoveryChoice_value
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width)) (value : CShape.Value .bit)
    (before : Store ctx) :
    (selectedRecoveryChoiceStep input modulus payload value before).1.read (scaleRead payload) =
      if value.toBool then recoveryValue (before.read (.first input))
        (before.read (.first (.second input))) (before.read (.second (.second input)))
        (before.read modulus) else before.read (scaleRead payload) := by
  cases value with
  | bit flag =>
    cases flag
    · rfl
    · exact withRecovery_value input modulus payload before

/-- Actual branch selection and the three real copies return their complete Store and path. -/
def exposureBodyStep (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) (before : Store ctx) :
    Store ctx × (exposureBody input modulus success payload inverseSuccess candidate
      reconstruction).Path :=
  let selected := before.read success
  let chosen := selectedRecoveryChoiceStep input modulus payload selected before
  (exposureCopyStore success (.first (scaleRead payload)) (.second (scaleRead payload))
    inverseSuccess candidate reconstruction chosen.1,
    (⟨selected, chosen.2⟩, ((), ((), ()))))

/-- Real selection and copying preserve complete quantum-reference matrices and original history. -/
theorem exposureBody_execute (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (exposureBody input modulus success payload inverseSuccess candidate reconstruction).execute
      Reference state = state.mapClassical (fun entry =>
        ((exposureBodyStep input modulus success payload inverseSuccess candidate reconstruction
          entry.1).1, (entry.2, (exposureBodyStep input modulus success payload inverseSuccess
            candidate reconstruction entry.1).2))) := by
  let selectedStep : Store ctx → Store ctx ×
      (Circuit.branch success (selectedRecoveryChoice input modulus payload)).Path := fun before =>
    let value := before.read success
    let chosen := selectedRecoveryChoiceStep input modulus payload value before
    (chosen.1, ⟨value, chosen.2⟩)
  refine (Circuit.execute_seq_mapClassical
    (.branch success (selectedRecoveryChoice input modulus payload))
    (exposureCopyBody success (.first (scaleRead payload)) (.second (scaleRead payload))
      inverseSuccess candidate reconstruction) selectedStep
    (fun before => (exposureCopyStore success (.first (scaleRead payload))
      (.second (scaleRead payload)) inverseSuccess candidate reconstruction before,
      ((), ((), ()))))
    (fun reference {_} _ initial => Circuit.execute_branch_mapClassical success _
      (selectedRecoveryChoiceStep input modulus payload)
      (selectedRecoveryChoice_execute input modulus payload) reference initial)
    (fun reference {_} _ initial => by
      refine (exposureCopyBody_execute success (.first (scaleRead payload))
        (.second (scaleRead payload)) inverseSuccess candidate reconstruction reference
        initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private theorem payload_initialized (cells : Cells ctx [FiniteCyclicDLP.OutputShape width])
    (before : Store ctx) (initialized : cells.Initialized before) :
    before.read (scaleRead cells.head.ref) =
      CShape.initialValue (FiniteCyclicDLP.OutputShape width) := by
  cases cells with
  | cons payload rest =>
    cases rest
    exact initialized.1

private theorem payload_input_free {outer : RuntimeCtx kind}
    (cells : Cells ctx [FiniteCyclicDLP.OutputShape width]) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) {shape : CShape}
    (input : CInputRef outer shape) :
    cells.head.ref.key ∉ (transport.liftInput input).storageKeys := by
  cases cells with
  | cons payload rest =>
    cases rest
    exact separated.1 input

private theorem output_payload_free {outer : RuntimeCtx kind}
    (cells : Cells ctx [FiniteCyclicDLP.OutputShape width]) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) {shape : CShape}
    (output : CWriteRef outer shape) :
    (transport.liftWrite output).key ∉ (scaleRead cells.head.ref).storageKeys := by
  have sourceAvoids := payload_input_free cells transport separated (.storage output.toCStorageRef)
  have different : cells.head.ref.key ≠ output.key := by
    simpa only [transport.liftInput_storageKeys, CInputRef.storageKeys, List.mem_singleton]
      using sourceAvoids
  simpa only [transport.liftWrite_key, scaleRead, CInputRef.storageKeys, List.mem_singleton]
    using different.symm

private theorem withSelectedExposure_eq_cells
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) :
    withSelectedExposure input modulus success inverseSuccess candidate reconstruction =
      withCells ctx [FiniteCyclicDLP.OutputShape width]
        (fun cells _ transport _ => exposureBody (transport.liftInput input)
          (transport.liftInput modulus) (transport.liftInput success) cells.head.ref
          (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
          (transport.liftWrite reconstruction)) := by
  simp only [withSelectedExposure, withCells, withCellsFrom,
    Transport.liftInput_underWorkspace, Transport.liftInput_id]
  rfl

/-- Actual fresh payload storage returns three writes, including caller destination aliases. -/
theorem withSelectedExposure_actualRecord
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) :
    ∃ record : Store ctx → Store ctx ×
        (withSelectedExposure input modulus success inverseSuccess candidate reconstruction).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withSelectedExposure input modulus success inverseSuccess candidate
          reconstruction).execute Reference state = state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx, (record before).1 =
        exposureWrite inverseSuccess candidate reconstruction before
          (.product (before.read success) (if (before.read success).toBool then
            recoveryValue (before.read (.first input)) (before.read (.first (.second input)))
              (before.read (.second (.second input))) (before.read modulus)
            else CShape.initialValue (FiniteCyclicDLP.OutputShape width))) := by
  rw [withSelectedExposure_eq_cells]
  apply withCells_actualRecord_initialized_post ctx [FiniteCyclicDLP.OutputShape width]
    (fun cells _ transport _ => exposureBody (transport.liftInput input)
      (transport.liftInput modulus) (transport.liftInput success) cells.head.ref
      (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
      (transport.liftWrite reconstruction))
    (fun before after => after = exposureWrite inverseSuccess candidate reconstruction before
      (.product (before.read success) (if (before.read success).toBool then
        recoveryValue (before.read (.first input)) (before.read (.first (.second input)))
          (before.read (.second (.second input))) (before.read modulus)
        else CShape.initialValue (FiniteCyclicDLP.OutputShape width))))
  intro inner cells _distinct transport separated
  refine ⟨exposureBodyStep (transport.liftInput input) (transport.liftInput modulus)
    (transport.liftInput success) cells.head.ref (transport.liftWrite inverseSuccess)
    (transport.liftWrite candidate) (transport.liftWrite reconstruction),
    exposureBody_execute _ _ _ _ _ _ _, ?_⟩
  intro source before reads initialized
  let chosen := selectedRecoveryChoiceStep (transport.liftInput input)
    (transport.liftInput modulus) cells.head.ref (before.read (transport.liftInput success)) before
  have chosenReads : transport.ReadsAs source chosen.1 := by
    intro shape other
    exact (selectedRecoveryChoice_read_other (transport.liftInput input)
      (transport.liftInput modulus) cells.head.ref _ (transport.liftInput other)
      (payload_input_free cells transport separated other) before).trans (reads other)
  have payloadRead := selectedRecoveryChoice_value (transport.liftInput input)
    (transport.liftInput modulus) cells.head.ref
    (before.read (transport.liftInput success)) before
  change chosen.1.read (scaleRead cells.head.ref) = _ at payloadRead
  have payloadRead := payloadRead.trans (show
      (if (before.read (transport.liftInput success)).toBool then
        recoveryValue (before.read (.first (transport.liftInput input)))
          (before.read (.first (.second (transport.liftInput input))))
          (before.read (.second (.second (transport.liftInput input))))
          (before.read (transport.liftInput modulus))
        else before.read (scaleRead cells.head.ref)) =
      (if (source.read success).toBool then recoveryValue (source.read (.first input))
        (source.read (.first (.second input))) (source.read (.second (.second input)))
        (source.read modulus) else CShape.initialValue (FiniteCyclicDLP.OutputShape width)) by
    change (if (before.read (transport.liftInput success)).toBool then
      recoveryValue (before.read (transport.liftInput input)).first
        (before.read (transport.liftInput input)).second.first
        (before.read (transport.liftInput input)).second.second
        (before.read (transport.liftInput modulus))
      else before.read (scaleRead cells.head.ref)) = _
    rw [payload_initialized cells before initialized, reads success, reads input, reads modulus]
    rfl)
  let value := CShape.Value.product (source.read success)
    (if (source.read success).toBool then recoveryValue (source.read (.first input))
      (source.read (.first (.second input))) (source.read (.second (.second input)))
      (source.read modulus) else CShape.initialValue (FiniteCyclicDLP.OutputShape width))
  refine ⟨exposureWrite inverseSuccess candidate reconstruction source value, rfl, ?_⟩
  have copied := exposureCopyStore_write (transport.liftInput success)
    (.first (scaleRead cells.head.ref)) (.second (scaleRead cells.head.ref))
    (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
    (transport.liftWrite reconstruction) chosen.1
    (output_payload_free cells transport separated inverseSuccess)
    (output_payload_free cells transport separated inverseSuccess)
    (output_payload_free cells transport separated candidate)
  change transport.ReadsAs (exposureWrite inverseSuccess candidate reconstruction source value)
    (exposureCopyStore (transport.liftInput success) (.first (scaleRead cells.head.ref))
      (.second (scaleRead cells.head.ref)) (transport.liftWrite inverseSuccess)
      (transport.liftWrite candidate) (transport.liftWrite reconstruction) chosen.1)
  rw [copied]
  have coordinates : CShape.Value.product (chosen.1.read (transport.liftInput success))
      (.product (chosen.1.read (.first (scaleRead cells.head.ref)))
        (chosen.1.read (.second (scaleRead cells.head.ref)))) = value := by
    change CShape.Value.product (chosen.1.read (transport.liftInput success))
      (.product (chosen.1.read (scaleRead cells.head.ref)).first
        (chosen.1.read (scaleRead cells.head.ref)).second) = _
    rw [chosenReads success, payloadRead]
    dsimp only [value]
    cases (if (source.read success).toBool then
      recoveryValue (source.read (.first input)) (source.read (.first (.second input)))
        (source.read (.second (.second input))) (source.read modulus)
      else CShape.initialValue (FiniteCyclicDLP.OutputShape width))
    rfl
  rw [coordinates]
  intro shape other
  exact exposureWrite_readsAs transport inverseSuccess candidate reconstruction source chosen.1
    chosenReads value other

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
