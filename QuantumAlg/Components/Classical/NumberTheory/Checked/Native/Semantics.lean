/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization.Restricted

/-!
# Complete actual checked-inverse execution

Four genuine fresh cells discharge every internal separation condition.
On each original canonical denominator, the actual success bit is the unit
decision and the successful output is the original deterministic inverse.
Failure preserves the caller's prior inverse word. The complete execution
record retains all other caller reads and every quantum-reference block.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular SignedReduction XGCD.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The original canonical input domain suffices for the actual complete checked inverse. -/
lemma withCheckedInverse_actualRecord (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width)) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
        (withCheckedInverse (model := model) spec denominator success inverse).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withCheckedInverse (model := model) spec denominator success inverse).execute
          environment Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState,
        (∀ {shape : CShape} (other : CInputRef ctx shape),
          success.key ∉ other.storageKeys → inverse.key ∉ other.storageKeys →
            (record before).1.1.read other = before.1.read other) ∧
        ∀ semantic : Residue spec, (before.1.read denominator).toNat = semantic.val →
          (record before).1.1.read (decisionRead success) =
            .bit (Engine.unitDecision spec semantic) ∧
          (Engine.unitDecision spec semantic = true →
            ((record before).1.1.read (decisionRead inverse)).toNat =
              (Engine.inverseCoefficient spec semantic).val) ∧
          (Engine.unitDecision spec semantic = false →
            (record before).1.1.read (decisionRead inverse) =
              before.1.read (decisionRead inverse)) := by
  let Post (before after : Store ctx) : Prop :=
    (∀ {shape : CShape} (other : CInputRef ctx shape),
      success.key ∉ other.storageKeys → inverse.key ∉ other.storageKeys →
        after.read other = before.read other) ∧
    ∀ semantic : Residue spec, (before.read denominator).toNat = semantic.val →
      after.read (decisionRead success) = .bit (Engine.unitDecision spec semantic) ∧
      (Engine.unitDecision spec semantic = true →
        (after.read (decisionRead inverse)).toNat = (Engine.inverseCoefficient spec semantic).val) ∧
      (Engine.unitDecision spec semantic = false →
        after.read (decisionRead inverse) = before.read (decisionRead inverse))
  refine withCells_actualRecord_initialized_restricted_post
    (environment := environment) ctx (checkedInverseShapes width)
    (fun cells _ transport _ => checkedInverseBody (model := model) spec
      (transport.liftInput denominator)
      (checkedModulusCell cells) (checkedRawOutputs cells)
      (transport.liftWrite success) (transport.liftWrite inverse)) Post ?_
  intro inner cells distinct transport separated
  have free : ∀ {shape : CShape} (input : CInputRef ctx shape) (index : Fin 4),
      (cellAt cells index).ref.key ∉ (transport.liftInput input).storageKeys :=
    fun input index => Cells.workspaceCells_cellAt_transport_avoids
      cells transport separated input index
  have keyInjective := workspaceCells_cellAt_key_injective cells distinct
  have different : ∀ (left right : Fin 4), left ≠ right →
      (cellAt cells left).ref.key ≠ (cellAt cells right).ref.key :=
    fun _ _ notSame same => notSame (keyInjective same)
  have outputFree : ∀ {shape : CShape} (output : CWriteRef ctx shape) (index : Fin 4),
      (cellAt cells index).ref.key ≠ (transport.liftWrite output).key := by
    intro shape output index
    simpa only [decisionRead, transport.liftInput_storageKeys, CInputRef.storageKeys,
      List.mem_singleton, transport.liftWrite_key] using free (decisionRead output) index
  have rawDistinct : (checkedRawOutputs cells).Distinct :=
    ⟨different ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide),
      different ⟨2, by decide⟩ ⟨0, by decide⟩ (by decide),
      different ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide)⟩
  obtain ⟨record, equation, correct⟩ := checkedInverseBody_actualRecord (model := model) spec
    (transport.liftInput denominator) (checkedModulusCell cells) (checkedRawOutputs cells)
    (transport.liftWrite success) (transport.liftWrite inverse) rawDistinct
    (free denominator ⟨3, by decide⟩)
    (different ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide))
    (different ⟨1, by decide⟩ ⟨3, by decide⟩ (by decide))
    (different ⟨0, by decide⟩ ⟨3, by decide⟩ (by decide))
    (outputFree success ⟨0, by decide⟩).symm (outputFree success ⟨3, by decide⟩).symm
    (outputFree inverse ⟨3, by decide⟩) (outputFree inverse ⟨2, by decide⟩)
    (outputFree inverse ⟨1, by decide⟩) (outputFree inverse ⟨0, by decide⟩)
  refine ⟨record, equation, ?_⟩
  intro before _initialized
  have entered : transport.ReadsAs (transport.restrict before.1) before.1 :=
    transport.workspaceTransport_restrict_readsAs before.1
  have returned : transport.ReadsAs (transport.restrict (record before).1.1) (record before).1.1 :=
    transport.workspaceTransport_restrict_readsAs (record before).1.1
  constructor
  · intro shape other successFree inverseFree
    have frame := (correct before).1 (transport.liftInput other)
      (free other ⟨3, by decide⟩) (free other ⟨2, by decide⟩)
      (free other ⟨1, by decide⟩) (free other ⟨0, by decide⟩)
      (by simpa only [transport.liftWrite_key, transport.liftInput_storageKeys] using successFree)
      (by simpa only [transport.liftWrite_key, transport.liftInput_storageKeys] using inverseFree)
    exact (returned other).symm.trans (frame.trans (entered other))
  · intro semantic represented
    have actual := (correct before).2 semantic
      ((congrArg CShape.Value.toNat (entered denominator)).trans represented)
    have successRead : (record before).1.1.read (decisionRead (transport.liftWrite success)) =
        (transport.restrict (record before).1.1).read (decisionRead success) := by
      simpa only [decisionRead, transport.liftWrite_input] using returned (decisionRead success)
    have inverseRead : (record before).1.1.read (decisionRead (transport.liftWrite inverse)) =
        (transport.restrict (record before).1.1).read (decisionRead inverse) := by
      simpa only [decisionRead, transport.liftWrite_input] using returned (decisionRead inverse)
    have oldInverse : before.1.read (decisionRead (transport.liftWrite inverse)) =
        (transport.restrict before.1).read (decisionRead inverse) := by
      simpa only [decisionRead, transport.liftWrite_input] using entered (decisionRead inverse)
    exact ⟨successRead.symm.trans actual.1,
      fun successValue => (congrArg CShape.Value.toNat inverseRead.symm).trans
        (actual.2.1 successValue),
      fun failureValue => inverseRead.symm.trans ((actual.2.2 failureValue).trans oldInverse)⟩

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native
