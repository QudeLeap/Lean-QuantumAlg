/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Raw.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Selection.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Trace
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space

/-!
# Original actual checked-inverse resource bounds

The original exact modulus-loader trace is charged once inside this call.
One resize, the independent raw-XGCD allowance and the stored-status-selected
signed allowance follow in that order. All four persistent cells coexist
with the larger active lexical scope. Bounds remain bounds; each actual path
separately has exactly the serial duration of its own native events.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular SignedReduction XGCD.Native

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Original exact loader events followed by unchanged independent arithmetic allowances. -/
def checkedInverseEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (spec : ModulusSpec width) : ResourcePool model :=
  ResourcePool.ofList (ConstantWord.loaderTrace model (width + 1)
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))) +
      ((ResourcePool.ofList [.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordResize width (width + 1)))] +
        rawEnvelope model (width + 1)) + checkedSelectionEnvelope model width)

/-- Original serial durations retain the exact compiled modulus loader and real decision. -/
def checkedInverseDepthLimit (spec : ModulusSpec width)
    (duration : Resource.Event model → Nat) : Nat :=
  ((ConstantWord.loaderTrace model (width + 1)
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))).map duration).sum +
      ((duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordResize width (width + 1)))) +
        rawDepthLimit (width + 1) duration) + checkedSelectionDepthLimit width duration)

/-- Widened XGCD and the later decision/signed phases have successive lexical lifetimes. -/
def checkedInverseActiveSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.max (SpacePool.ofShape (.unsignedWord (width + 1)) + rawScratchSpace kind (width + 1))
    (checkedSelectionSpaceLimit kind width)

private lemma checked_body_pool_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (path : (checkedInverseBody (model := model) spec denominator modulus outputs success
      inverse).Path) :
    (checkedInverseBody (model := model) spec denominator modulus outputs success
      inverse).resourcePool path ≤
      checkedInverseEnvelope model spec := by
  have loaded := congrArg ResourcePool.ofList (ConstantWord.constantFold_eventTrace modulus
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) path.1)
  change ResourcePool.ofList ((ConstantWord.circuit (model := model) modulus
    spec.modulus).eventTrace path.1 ++
    ((withWidenedXgcd (model := model) denominator (decisionRead modulus) outputs).eventTrace
      path.2.1 ++
      (checkedCoefficientSelection (model := model) (decisionRead outputs.gcd)
        (decisionRead outputs.rightCoefficient) (decisionRead modulus) success inverse).eventTrace
          path.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add loaded.le (add_le_add (withWidenedXgcd_pool_le _ _ _ path.2.1)
    (checkedCoefficientSelection_pool_le _ _ _ _ _ path.2.2))

/-- Every actual complete checked execution fits the original independent syntax envelope. -/
lemma withCheckedInverse_pool_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (path : (withCheckedInverse (model := model) spec denominator success inverse).Path) :
    (withCheckedInverse (model := model) spec denominator success inverse).resourcePool path ≤
      checkedInverseEnvelope model spec := by
  exact withCellsFrom_pool_le (Transport.id ctx) (checkedInverseShapes width)
    (fun cells _ transport _ => checkedInverseBody (model := model) spec (transport.liftInput
      denominator)
      (checkedModulusCell cells) (checkedRawOutputs cells)
      (transport.liftWrite success) (transport.liftWrite inverse))
    (checkedInverseEnvelope model spec)
    (fun cells _ transport _ selected => checked_body_pool_le _ _ _ _ _ _ selected) path

private lemma checked_body_duration_trace (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event model → Nat)
    (path : (checkedInverseBody (model := model) spec denominator modulus outputs success
      inverse).Path) :
    (checkedInverseBody (model := model) spec denominator modulus outputs success inverse).depth
      duration path =
      (((checkedInverseBody (model := model) spec denominator modulus outputs success
        inverse).eventTrace path).map
        duration).sum := by
  have loaded := (ConstantWord.constantFold_depth modulus _ duration path.1).trans
    (congrArg (fun events => (events.map duration).sum)
      (ConstantWord.constantFold_eventTrace modulus _ path.1)).symm
  have widened := withWidenedXgcd_duration_eventTrace denominator (decisionRead modulus)
    outputs duration path.2.1
  have selected := checkedCoefficientSelection_duration_eventTrace (decisionRead outputs.gcd)
    (decisionRead outputs.rightCoefficient) (decisionRead modulus) success inverse duration path.2.2
  change (ConstantWord.circuit (model := model) modulus spec.modulus).depth duration path.1 +
    ((withWidenedXgcd (model := model) denominator (decisionRead modulus) outputs).depth duration
      path.2.1 +
      (checkedCoefficientSelection (model := model) (decisionRead outputs.gcd)
        (decisionRead outputs.rightCoefficient) (decisionRead modulus) success inverse).depth
          duration path.2.2) = _
  refine (congrArg₂ Nat.add loaded (congrArg₂ Nat.add widened selected)).trans ?_
  change _ = (((ConstantWord.circuit (model := model) modulus spec.modulus).eventTrace path.1 ++
    ((withWidenedXgcd (model := model) denominator (decisionRead modulus) outputs).eventTrace
      path.2.1 ++
      (checkedCoefficientSelection (model := model) (decisionRead outputs.gcd)
        (decisionRead outputs.rightCoefficient) (decisionRead modulus) success inverse).eventTrace
          path.2.2)).map duration).sum
  simp only [List.map_append, List.sum_append]
  rfl

/-- Every actual complete path has exactly the serial duration of its own emitted instructions. -/
lemma withCheckedInverse_duration_eventTrace (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event model → Nat)
    (path : (withCheckedInverse (model := model) spec denominator success inverse).Path) :
    (withCheckedInverse (model := model) spec denominator success inverse).depth duration path =
      (((withCheckedInverse (model := model) spec denominator success inverse).eventTrace path).map
        duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (checkedInverseShapes width)
    (fun cells _ transport _ => checkedInverseBody (model := model) spec (transport.liftInput
      denominator)
      (checkedModulusCell cells) (checkedRawOutputs cells)
      (transport.liftWrite success) (transport.liftWrite inverse))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((code.eventTrace selected).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => checked_body_duration_trace _ _ _ _ _ _ duration selected)
    path

private lemma checked_body_depth_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event model → Nat)
    (path : (checkedInverseBody (model := model) spec denominator modulus outputs success
      inverse).Path) :
    (checkedInverseBody (model := model) spec denominator modulus outputs success inverse).depth
      duration path ≤
      checkedInverseDepthLimit spec duration :=
  Nat.add_le_add (ConstantWord.constantFold_depth modulus _ duration path.1).le
    (Nat.add_le_add (withWidenedXgcd_depth_le _ _ _ duration path.2.1)
      (checkedCoefficientSelection_depth_le _ _ _ _ _ duration path.2.2))

/-- The original independent duration allowance bounds the actual complete checked program. -/
lemma withCheckedInverse_depth_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event model → Nat)
    (path : (withCheckedInverse (model := model) spec denominator success inverse).Path) :
    (withCheckedInverse (model := model) spec denominator success inverse).depth duration path ≤
      checkedInverseDepthLimit spec duration := by
  exact withCellsFrom_depth_le (Transport.id ctx) (checkedInverseShapes width)
    (fun cells _ transport _ => checkedInverseBody (model := model) spec (transport.liftInput
      denominator)
      (checkedModulusCell cells) (checkedRawOutputs cells)
      (transport.liftWrite success) (transport.liftWrite inverse)) duration
    (checkedInverseDepthLimit spec duration)
    (fun cells _ transport _ selected => checked_body_depth_le _ _ _ _ _ _ duration selected) path

private lemma checked_body_resident_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (path : (checkedInverseBody (model := model) spec denominator modulus outputs success
      inverse).Path) :
    (checkedInverseBody (model := model) spec denominator modulus outputs success
      inverse).peakResidentSpace path ≤
      checkedInverseActiveSpace model.kind width + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (ConstantWord.constantWord_resident_le _ _ path.1).trans le_add_self
  · refine (Circuit.peakResidentSpace_seq _ _ path.2).le.trans (SpacePool.max_le ?_ ?_)
    · exact (withWidenedXgcd_resident_le _ _ _ path.2.1).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    · exact (checkedCoefficientSelection_resident_le _ _ _ _ _ path.2.2).trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)

private lemma checked_body_auxiliary_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (path : (checkedInverseBody (model := model) spec denominator modulus outputs success
      inverse).Path) :
    (checkedInverseBody (model := model) spec denominator modulus outputs success
      inverse).peakAuxiliarySpace path ≤
      checkedInverseActiveSpace model.kind width + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (ConstantWord.constantWord_auxiliary_le _ _ path.1).trans le_add_self
  · refine (Circuit.peakAuxiliarySpace_seq _ _ path.2).le.trans (SpacePool.max_le ?_ ?_)
    · exact (withWidenedXgcd_auxiliary_le _ _ _ path.2.1).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    · exact (checkedCoefficientSelection_auxiliary_le _ _ _ _ _ path.2.2).trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- All four original persistent cells and the active lexical allowance are genuinely charged. -/
lemma withCheckedInverse_resident_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (path : (withCheckedInverse (model := model) spec denominator success inverse).Path) :
    (withCheckedInverse (model := model) spec denominator success inverse).peakResidentSpace path ≤
      ((checkedInverseShapes width).map SpacePool.ofShape).sum +
        checkedInverseActiveSpace model.kind width + ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (checkedInverseShapes width)
    (fun cells _ transport _ => checkedInverseBody (model := model) spec (transport.liftInput
      denominator)
      (checkedModulusCell cells) (checkedRawOutputs cells)
      (transport.liftWrite success) (transport.liftWrite inverse))
    (checkedInverseActiveSpace model.kind width)
    (fun cells _ transport _ selected => checked_body_resident_le _ _ _ _ _ _ selected) path

/-- Auxiliary ownership includes the same real internal lifetimes and every caller context cell. -/
lemma withCheckedInverse_auxiliary_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (path : (withCheckedInverse (model := model) spec denominator success inverse).Path) :
    (withCheckedInverse (model := model) spec denominator success inverse).peakAuxiliarySpace path ≤
      ((checkedInverseShapes width).map SpacePool.ofShape).sum +
        checkedInverseActiveSpace model.kind width + ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (checkedInverseShapes width)
    (fun cells _ transport _ => checkedInverseBody (model := model) spec (transport.liftInput
      denominator)
      (checkedModulusCell cells) (checkedRawOutputs cells)
      (transport.liftWrite success) (transport.liftWrite inverse))
    (checkedInverseActiveSpace model.kind width)
    (fun cells _ transport _ selected => checked_body_auxiliary_le _ _ _ _ _ _ selected) path

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native
