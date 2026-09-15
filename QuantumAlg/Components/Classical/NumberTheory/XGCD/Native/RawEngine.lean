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
def copyRawOutputs (cells : Cells ctx (stateShapes width))
    (outputs : RawOutputs ctx width) : Circuit ctx ctx :=
  .seq (.classical (.wordUnary .copy width ctx (GCD.cellRead (secondCell cells)) outputs.gcd))
    (.seq (.classical (.wordUnary .copy (PureXGCD.executionCoefficientWidth width) ctx
      (GCD.cellRead (secondLeftCell cells)) outputs.leftCoefficient))
      (.classical (.wordUnary .copy (PureXGCD.executionCoefficientWidth width) ctx
        (GCD.cellRead (secondRightCell cells)) outputs.rightCoefficient)))

/-- The independent original three output-copy events at their actual widths. -/
def rawOutputEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordUnary .copy width),
    .classicalOperation (.wordUnary .copy (PureXGCD.executionCoefficientWidth width)),
    .classicalOperation (.wordUnary .copy (PureXGCD.executionCoefficientWidth width))]

/-- The actual output instruction sequence has exactly the original three native events. -/
theorem xgcdNativeCopyRawOutputs_eventTrace (cells : Cells ctx (stateShapes width))
    (outputs : RawOutputs ctx width) (path : (copyRawOutputs cells outputs).Path) :
    (copyRawOutputs cells outputs).eventTrace path = rawOutputEvents kind width := rfl

/-- The original schedule reads the real active bit on each iteration, then copies all results. -/
def scheduledRawBody (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width) :
    Circuit ctx ctx :=
  .seq (initializationBody cells input zero)
    (.seq (.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (guardedActive cells zero)) (copyRawOutputs cells outputs))

/-- Seven fresh state cells enclose the same initialized, guarded, and copied actual schedule. -/
def withRawState
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width) :
    Circuit ctx ctx :=
  withStateCells ctx width fun cells _ transport _ =>
    scheduledRawBody cells (transport.liftInput input) (transport.liftInput zero)
      (outputs.transport transport)

/-- The original independent zero allocation supplies initialization without a caller promise. -/
def rawEngine
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (withRawState
      (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)
      (GCD.cellRead (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)) outputs.underZero)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
