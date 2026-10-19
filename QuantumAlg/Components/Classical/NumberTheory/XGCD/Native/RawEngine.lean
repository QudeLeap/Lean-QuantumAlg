/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.ActiveStep
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Initialization
import all QuantumAlg.Util.Classical.NumberTheory.Euclidean

/-!
# Actual shared raw extended-Euclidean engine

An independent fresh zero word surrounds the seven actual state cells, as in
the original raw engine. Initialization precedes the original width-derived
guarded iteration schedule. Three final native copies expose the gcd and both
execution-width coefficients before all internal cells are released.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The three actual caller-owned raw results remain live after the engine returns. -/
structure RawOutputs (ctx : RuntimeCtx kind) (width : Nat) where
  gcd : CWriteRef ctx (.unsignedWord width)
  leftCoefficient : CWriteRef ctx (.unsignedWord (PureXGCD.executionCoefficientWidth width))
  rightCoefficient : CWriteRef ctx (.unsignedWord (PureXGCD.executionCoefficientWidth width))

/-- Internal callers obtain this separation by allocating their three result cells. -/
def RawOutputs.Distinct (outputs : RawOutputs ctx width) : Prop :=
  outputs.gcd.key ≠ outputs.leftCoefficient.key ∧
    outputs.gcd.key ≠ outputs.rightCoefficient.key ∧
      outputs.leftCoefficient.key ≠ outputs.rightCoefficient.key

/-- Structural transport keeps the same three physical output identities. -/
def RawOutputs.transport {outer : RuntimeCtx kind} (outputs : RawOutputs outer width)
    (transport : Transport outer ctx) : RawOutputs ctx width where
  gcd := transport.liftWrite outputs.gcd
  leftCoefficient := transport.liftWrite outputs.leftCoefficient
  rightCoefficient := transport.liftWrite outputs.rightCoefficient

/-- Lift the three results past the actual fresh zero-word allocation. -/
def RawOutputs.underZero (outputs : RawOutputs ctx width) :
    RawOutputs (ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh) width where
  gcd := outputs.gcd.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh
  leftCoefficient := outputs.leftCoefficient.underWorkspace ctx.canonicalFreshKey
    (.unsignedWord width) ctx.canonicalFreshKey_fresh
  rightCoefficient := outputs.rightCoefficient.underWorkspace ctx.canonicalFreshKey
    (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- The original final copies read the previous remainder and its two coefficients. -/
def copyRawOutputs {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (outputs : RawOutputs ctx width) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model)
    (.wordUnary .copy width ctx (GCD.cellRead (secondCell cells)) outputs.gcd))
    (.seq (BitWord.instruction (execution := model)
      (.wordUnary .copy (PureXGCD.executionCoefficientWidth width) ctx
      (GCD.cellRead (secondLeftCell cells)) outputs.leftCoefficient))
      (BitWord.instruction (execution := model)
        (.wordUnary .copy (PureXGCD.executionCoefficientWidth width) ctx
        (GCD.cellRead (secondRightCell cells)) outputs.rightCoefficient)))

/-- The original final copies retain their actual three native results. -/
def copyRawOutputsStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (outputs : RawOutputs ctx width) (store : Store ctx) :
    Store ctx × (copyRawOutputs (model := model) cells outputs).Path :=
  let gcd := BitWord.instructionStep (execution := model)
    (.wordUnary .copy width ctx (GCD.cellRead (secondCell cells)) outputs.gcd) store
  let left := BitWord.instructionStep (execution := model)
    (.wordUnary .copy (PureXGCD.executionCoefficientWidth width) ctx
      (GCD.cellRead (secondLeftCell cells)) outputs.leftCoefficient) gcd.1
  let right := BitWord.instructionStep (execution := model)
    (.wordUnary .copy (PureXGCD.executionCoefficientWidth width) ctx
      (GCD.cellRead (secondRightCell cells)) outputs.rightCoefficient) left.1
  (right.1, (gcd.2, (left.2, right.2)))

/-- The independent original three output-copy events at their actual widths. -/
def rawOutputEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy (PureXGCD.executionCoefficientWidth width))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy (PureXGCD.executionCoefficientWidth width)))]

/-- The actual output instruction sequence has exactly the original three native events. -/
lemma xgcdNativeCopyRawOutputs_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (outputs : RawOutputs ctx width) (path : (copyRawOutputs (model := model) cells outputs).Path) :
    (copyRawOutputs (model := model) cells outputs).eventTrace path =
      rawOutputEvents model width := by
  change (BitWord.instruction (execution := model)
    (.wordUnary .copy width ctx (GCD.cellRead (secondCell cells)) outputs.gcd)).eventTrace path.1 ++
    ((BitWord.instruction (execution := model)
      (.wordUnary .copy (PureXGCD.executionCoefficientWidth width) ctx
        (GCD.cellRead (secondLeftCell cells)) outputs.leftCoefficient)).eventTrace path.2.1 ++
      (BitWord.instruction (execution := model)
        (.wordUnary .copy (PureXGCD.executionCoefficientWidth width) ctx
          (GCD.cellRead (secondRightCell cells)) outputs.rightCoefficient)).eventTrace path.2.2) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The original schedule reads the real active bit on each iteration, then copies all results. -/
def scheduledRawBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width) :
    Circuit model ctx ctx :=
  .seq (initializationBody (model := model) cells input zero)
    (.seq (.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (guardedActive (model := model) cells zero)) (copyRawOutputs (model := model) cells outputs))

/-- Seven fresh state cells enclose the same initialized, guarded, and copied actual schedule. -/
def withRawState {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width) :
    Circuit model ctx ctx :=
  withStateCells ctx width fun cells _ transport _ =>
    scheduledRawBody (model := model) cells (transport.liftInput input) (transport.liftInput zero)
      (outputs.transport transport)

/-- The original independent zero allocation supplies initialization without a caller promise. -/
def rawEngine {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (withRawState (model := model)
      (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)
      (GCD.cellRead (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)) outputs.underZero)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
