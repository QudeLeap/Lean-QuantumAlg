/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Coefficient
import all QuantumAlg.Components.Classical.ConstantWord.Trace
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Raw.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Bounds
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space

/-!
# Original actual total field-coefficient resource bounds

The original loader precedes the actual widened raw engine and unconditional
signed reduction. Their independent original syntax allowances compose in
that order. All four persistent cells coexist with the larger active lexical
scope. Exact selected durations are proved from the same actual native trace.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open NumberTheory.XGCD.Native
open NumberTheory.Checked.Native
open NumberTheory.Checked.SignedReduction.Native

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original loader and independent raw-engine and signed-reduction syntax allowances. -/
def coefficientEnvelope (kind : ProblemKind) (spec : ModulusSpec width) : ResourcePool kind :=
  ResourcePool.ofList (ConstantWord.loaderTrace kind (width + 1)
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))) +
      ((ResourcePool.ofList [.classicalOperation (.wordResize width (width + 1))] +
        rawEnvelope kind (width + 1)) + signedReductionEnvelope kind width)

/-- Original serial allowance retains the real constant-loader and widening durations. -/
def coefficientDepthLimit (spec : ModulusSpec width) (duration : Resource.Event kind → Nat) : Nat :=
  ((ConstantWord.loaderTrace kind (width + 1)
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))).map duration).sum +
      ((duration (.classicalOperation (.wordResize width (width + 1))) +
        rawDepthLimit (width + 1) duration) + signedReductionDepthLimit width duration)

/-- The original widened engine and signed reduction occupy disjoint successive lexical scopes. -/
def coefficientActiveSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.max (SpacePool.ofShape (.unsignedWord (width + 1)) + rawScratchSpace kind (width + 1))
    (signedReductionSpaceLimit kind width)

private theorem coefficientBody_pool_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width)) (scratch : CoefficientScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientBody spec denominator scratch output).Path) :
    (coefficientBody spec denominator scratch output).resourcePool path ≤
      coefficientEnvelope kind spec := by
  have loaded := congrArg ResourcePool.ofList (ConstantWord.constantFold_eventTrace scratch.modulus
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) path.1)
  change ResourcePool.ofList
    ((ConstantWord.circuit scratch.modulus spec.modulus).eventTrace path.1 ++
    ((withWidenedXgcd denominator (coefficientRead scratch.modulus) scratch.outputs).eventTrace
      path.2.1 ++ (withSignedReduction (coefficientRead scratch.outputs.rightCoefficient)
        (coefficientRead scratch.modulus) output).eventTrace path.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add loaded.le (add_le_add (withWidenedXgcd_pool_le _ _ _ path.2.1)
    (withSignedReduction_pool_le _ _ _ path.2.2))

/-- All actual selected native counts satisfy the original total coefficient syntax allowance. -/
theorem coefficientIntoWord_pool_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientIntoWord spec denominator output).Path) :
    (coefficientIntoWord spec denominator output).resourcePool path ≤
      coefficientEnvelope kind spec := by
  exact withCellsFrom_property (Transport.id ctx) (coefficientShapes width)
    (fun cells _ transport _ => coefficientBody spec (transport.liftInput denominator)
      (coefficientScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.resourcePool selected ≤ coefficientEnvelope kind spec)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => coefficientBody_pool_le _ _ _ _ selected) path

private theorem coefficientBody_duration_eventTrace (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width)) (scratch : CoefficientScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (coefficientBody spec denominator scratch output).Path) :
    (coefficientBody spec denominator scratch output).depth duration path =
      (((coefficientBody spec denominator scratch output).eventTrace path).map duration).sum := by
  have loaded : (ConstantWord.circuit scratch.modulus spec.modulus).depth duration path.1 =
      (((ConstantWord.circuit scratch.modulus spec.modulus).eventTrace path.1).map
        duration).sum := by
    have trace := ConstantWord.constantFold_eventTrace scratch.modulus
      (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) path.1
    exact (ConstantWord.constantFold_depth scratch.modulus _ duration path.1).trans
      (congrArg (fun events => (events.map duration).sum) trace.symm)
  have signed : (withSignedReduction (coefficientRead scratch.outputs.rightCoefficient)
      (coefficientRead scratch.modulus) output).depth duration path.2.2 =
      (((withSignedReduction (coefficientRead scratch.outputs.rightCoefficient)
        (coefficientRead scratch.modulus) output).eventTrace path.2.2).map duration).sum := by
    exact (withSignedReduction_durationDepth _ _ _ duration path.2.2).trans
      (congrArg (fun events => (events.map duration).sum)
        (withSignedReduction_eventTrace _ _ _ path.2.2).symm)
  change _ + (_ + _) = (List.map duration
    ((ConstantWord.circuit scratch.modulus spec.modulus).eventTrace path.1 ++
      ((withWidenedXgcd denominator (coefficientRead scratch.modulus) scratch.outputs).eventTrace
        path.2.1 ++ (withSignedReduction (coefficientRead scratch.outputs.rightCoefficient)
          (coefficientRead scratch.modulus) output).eventTrace path.2.2))).sum
  rw [List.map_append, List.sum_append, List.map_append, List.sum_append]
  exact congrArg₂ Nat.add loaded
    (congrArg₂ Nat.add (withWidenedXgcd_duration_eventTrace _ _ _ duration path.2.1) signed)

/-- Selected durations equal the same actual native trace through every persistent scope. -/
theorem coefficientIntoWord_duration_eventTrace (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (coefficientIntoWord spec denominator output).Path) :
    (coefficientIntoWord spec denominator output).depth duration path =
      (((coefficientIntoWord spec denominator output).eventTrace path).map duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (coefficientShapes width)
    (fun cells _ transport _ => coefficientBody spec (transport.liftInput denominator)
      (coefficientScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((code.eventTrace selected).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected =>
      coefficientBody_duration_eventTrace _ _ _ _ duration selected) path

private theorem coefficientBody_depth_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width)) (scratch : CoefficientScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (coefficientBody spec denominator scratch output).Path) :
    (coefficientBody spec denominator scratch output).depth duration path ≤
      coefficientDepthLimit spec duration :=
  Nat.add_le_add (ConstantWord.constantFold_depth scratch.modulus _ duration path.1).le
    (Nat.add_le_add (withWidenedXgcd_depth_le _ _ _ duration path.2.1)
      (withSignedReduction_depth_le _ _ _ duration path.2.2))

/-- The original independent serial allowance bounds every actual selected coefficient path. -/
theorem coefficientIntoWord_depth_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (coefficientIntoWord spec denominator output).Path) :
    (coefficientIntoWord spec denominator output).depth duration path ≤
      coefficientDepthLimit spec duration := by
  exact withCellsFrom_property (Transport.id ctx) (coefficientShapes width)
    (fun cells _ transport _ => coefficientBody spec (transport.liftInput denominator)
      (coefficientScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.depth duration selected ≤ coefficientDepthLimit spec duration)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => coefficientBody_depth_le _ _ _ _ duration selected) path

private theorem coefficientBody_resident_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width)) (scratch : CoefficientScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientBody spec denominator scratch output).Path) :
    (coefficientBody spec denominator scratch output).peakResidentSpace path ≤
      coefficientActiveSpace kind width + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (ConstantWord.constantWord_resident_le _ _ path.1).trans le_add_self
  · refine (Circuit.peakResidentSpace_seq _ _ path.2).le.trans (SpacePool.max_le ?_ ?_)
    · exact (withWidenedXgcd_resident_le _ _ _ path.2.1).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    · exact (withSignedReduction_resident_le _ _ _ path.2.2).trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)

private theorem coefficientBody_auxiliary_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width)) (scratch : CoefficientScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientBody spec denominator scratch output).Path) :
    (coefficientBody spec denominator scratch output).peakAuxiliarySpace path ≤
      coefficientActiveSpace kind width + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (ConstantWord.constantWord_auxiliary_le _ _ path.1).trans le_add_self
  · refine (Circuit.peakAuxiliarySpace_seq _ _ path.2).le.trans (SpacePool.max_le ?_ ?_)
    · exact (withWidenedXgcd_auxiliary_le _ _ _ path.2.1).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    · exact (withSignedReduction_auxiliary_le _ _ _ path.2.2).trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- The original four persistent cells coexist with the larger actual arithmetic allowance. -/
theorem coefficientIntoWord_resident_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientIntoWord spec denominator output).Path) :
    (coefficientIntoWord spec denominator output).peakResidentSpace path ≤
      ((coefficientShapes width).map SpacePool.ofShape).sum +
        coefficientActiveSpace kind width + ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (coefficientShapes width)
    (fun cells _ transport _ => coefficientBody spec (transport.liftInput denominator)
      (coefficientScratch cells) (transport.liftWrite output))
    (coefficientActiveSpace kind width)
    (fun cells _ transport _ selected => coefficientBody_resident_le _ _ _ _ selected) path

/-- Auxiliary ownership counts those same original cells and all caller context entries. -/
theorem coefficientIntoWord_auxiliary_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientIntoWord spec denominator output).Path) :
    (coefficientIntoWord spec denominator output).peakAuxiliarySpace path ≤
      ((coefficientShapes width).map SpacePool.ofShape).sum +
        coefficientActiveSpace kind width + ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (coefficientShapes width)
    (fun cells _ transport _ => coefficientBody spec (transport.liftInput denominator)
      (coefficientScratch cells) (transport.liftWrite output))
    (coefficientActiveSpace kind width)
    (fun cells _ transport _ selected => coefficientBody_auxiliary_le _ _ _ _ selected) path

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
