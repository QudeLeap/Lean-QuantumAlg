/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Construction
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Layout.Scope
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Complete actual order-recovery execution

The body record follows its real initialization store, every stored-activity
iteration and the actual final option encoder. The enclosing execution theorem
composes that proved body with its genuine field allocations and releases,
preserving complete density blocks and their correlated finite paths.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {modulusWidth phaseBits : Nat}

private theorem mapDecision {C D : Type} [Fintype C] [Fintype D] {R : Register}
    (first second : DecidableEq D) (state : ExecutionState C R) (update : C → D) :
    @ExecutionState.mapClassical C D _ _ R first state update =
      @ExecutionState.mapClassical C D _ _ R second state update :=
  congrArg (fun decision : DecidableEq D =>
    @ExecutionState.mapClassical C D _ _ R decision state update)
      (Subsingleton.elim first second)

/-- Concrete initialization, actual finite scan paths and the final real option write. -/
def recoveryBodyStep
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits))
    (output : CWriteRef ctx (outputShape phaseBits))
    (store : Store (recoveryContext ctx modulusWidth (phaseBits + 1))) :
    Store (recoveryContext ctx modulusWidth (phaseBits + 1)) ×
      (recoveryBody (model := model) spec base sample output).Path :=
  let initialized := initializeScanStep (model := model) ctx modulusWidth phaseBits sample store
  let next := scanSlotStep (model := model) spec.modulusSpec
    (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
    (recoveryCells ctx modulusWidth (phaseBits + 1))
  let fuel := ClassicalAlgorithms.OrderRecovery.finiteCandidateFuel phaseBits
  let scanned := (fun value => (next value).1)^[fuel] initialized.1
  let paths := fun index : Fin fuel =>
    (next ((fun value => (next value).1)^[index.val] initialized.1)).2
  let packed := BitWord.instructionStep (execution := model) (packRecoveredOp output) scanned
  (packed.1, (initialized.2, (paths, packed.2)))

/-- Every actual body path is tied to the same initialization and final-store record. -/
theorem nativeRecovery_body_execute
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits))
    (output : CWriteRef ctx (outputShape phaseBits)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (recoveryContext ctx modulusWidth (phaseBits + 1))
      Reference (model.HiddenState × History)) :
    (recoveryBody (model := model) spec base sample output).execute Reference state =
      state.mapClassical (fun entry =>
        ((recoveryBodyStep (model := model) spec base sample output entry.1).1,
          (entry.2.1, (entry.2.2,
            (recoveryBodyStep (model := model) spec base sample output entry.1).2)))) := by
  let actualScan := scan (model := model) spec.modulusSpec
    (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
    (recoveryCells ctx modulusWidth (phaseBits + 1))
    (ClassicalAlgorithms.OrderRecovery.finiteCandidateFuel phaseBits)
  let scanStep := fun before :
      Store (recoveryContext ctx modulusWidth (phaseBits + 1)) × model.HiddenState =>
    let next := scanSlotStep (model := model) spec.modulusSpec
      (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
      (recoveryCells ctx modulusWidth (phaseBits + 1))
    let fuel := ClassicalAlgorithms.OrderRecovery.finiteCandidateFuel phaseBits
    (((fun store => (next store).1)^[fuel] before.1, before.2),
      fun index : Fin fuel => (next ((fun store => (next store).1)^[index.val] before.1)).2)
  let pack := BitWord.instruction (execution := model)
    (packRecoveredOp (modulusWidth := modulusWidth) output)
  let packStep := fun before :
      Store (recoveryContext ctx modulusWidth (phaseBits + 1)) × model.HiddenState =>
    let next := BitWord.instructionStep (execution := model)
      (packRecoveredOp (modulusWidth := modulusWidth) output) before.1
    ((next.1, before.2), next.2)
  have scanEquation (reference : Register) {H : Type} [Fintype H]
      (initial : State (recoveryContext ctx modulusWidth (phaseBits + 1))
        reference (model.HiddenState × H)) :
      actualScan.execute reference initial = initial.mapClassical (fun entry =>
        let next := scanStep (entry.1, entry.2.1)
        (next.1.1, (next.1.2, (entry.2.2, next.2)))) := by
    refine (nativeScan_execute spec.modulusSpec _ _ _ reference initial).trans ?_
    exact mapDecision _ _ initial _
  have packEquation (reference : Register) {H : Type} [Fintype H]
      (initial : State (recoveryContext ctx modulusWidth (phaseBits + 1))
        reference (model.HiddenState × H)) :
      pack.execute reference initial = initial.mapClassical (fun entry =>
        let next := packStep (entry.1, entry.2.1)
        (next.1.1, (next.1.2, (entry.2.2, next.2)))) := by
    refine (BitWord.bitWord_instruction_execute
      (packRecoveredOp (modulusWidth := modulusWidth) output) initial).trans ?_
    exact mapDecision _ _ initial _
  let tailStep := fun before :
      Store (recoveryContext ctx modulusWidth (phaseBits + 1)) × model.HiddenState =>
    let scanned := scanStep before
    let packed := packStep scanned.1
    (packed.1, (scanned.2, packed.2))
  have tailEquation (reference : Register) {H : Type} [Fintype H]
      (initial : State (recoveryContext ctx modulusWidth (phaseBits + 1))
        reference (model.HiddenState × H)) :
      (Circuit.seq actualScan pack).execute reference initial =
        initial.mapClassical (fun entry =>
          let next := tailStep (entry.1, entry.2.1)
          (next.1.1, (next.1.2, (entry.2.2, next.2)))) := by
    refine (Circuit.execute_sequenceRecord actualScan pack scanStep packStep
      ?_ ?_ reference initial).trans ?_
    · intro reference history _ current
      exact (scanEquation reference current).trans (mapDecision _ _ current _)
    · intro reference history _ current
      exact (packEquation reference current).trans (mapDecision _ _ current _)
    · exact mapDecision _ _ initial _
  refine (Circuit.execute_sequenceRecord
    (initializeScan (model := model) ctx modulusWidth phaseBits sample)
    (Circuit.seq actualScan pack)
    (fun before =>
      let next := initializeScanStep (model := model) ctx modulusWidth phaseBits sample before.1
      ((next.1, before.2), next.2)) tailStep
    ?_ ?_ Reference state).trans ?_
  · intro reference history _ current
    exact (nativeRecovery_initialize_execute ctx modulusWidth phaseBits sample
      reference current).trans (mapDecision _ _ current _)
  · intro reference history _ current
    exact (tailEquation reference current).trans (mapDecision _ _ current _)
  · exact mapDecision _ _ state _

/-- The actual outer record after all recovery workspaces have been matched and released. -/
def intoStep (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits))
    (output : CWriteRef ctx (outputShape phaseBits)) (store : Store ctx) :
    Store ctx × (into (model := model) spec base sample output).Path :=
  scopeRecoveryStep ctx modulusWidth (phaseBits + 1) recoveryFields
    (recoveryBody (model := model) spec base sample output)
    (recoveryBodyStep (model := model) spec base sample output) store

/-- Complete native recovery follows the sole interpreter on every full reference block. -/
theorem nativeRecovery_into_execute
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits))
    (output : CWriteRef ctx (outputShape phaseBits)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) spec base sample output).execute Reference state =
      state.mapClassical (fun entry =>
        ((intoStep (model := model) spec base sample output entry.1).1,
          (entry.2.1, (entry.2.2,
            (intoStep (model := model) spec base sample output entry.1).2)))) := by
  refine (nativeRecovery_scope_execute ctx modulusWidth (phaseBits + 1) recoveryFields
    (recoveryBody (model := model) spec base sample output)
    (recoveryBodyStep (model := model) spec base sample output)
    (nativeRecovery_body_execute spec base sample output) Reference state).trans ?_
  exact mapDecision _ _ state (fun entry =>
    ((intoStep (model := model) spec base sample output entry.1).1,
      (entry.2.1, (entry.2.2, (intoStep (model := model) spec base sample output entry.1).2))))

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
