/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Echelon
import all QuantumAlg.Components.Classical.GF2.Native.Candidate
import all QuantumAlg.Components.Classical.GF2.Native.Validation

/-!
# Actual complete GF(2) recovery in the original caller context

The real loading and reduction prefix is followed by the original pivot-mask
complement, single success NOT, free-mask decision and three success-controlled
stages. The original packOption instruction reads the final actual latches.
The same-context circuit assumes no initial latch values: the original fresh
layout supplies those values at its separate allocation boundary.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- The original success-controlled stages share the same literal false identity arm. -/
private def successChoice (body : Circuit ctx ctx) : CShape.Value .bit → Circuit ctx ctx
  | .bit false => .id ctx
  | .bit true => body

/-- Each original conditional reads the current actual success cell before selecting its body. -/
private def whenSuccessful (success : CWriteRef ctx .bit) (body : Circuit ctx ctx) :
    Circuit ctx ctx :=
  .branch (.storage success.toCStorageRef) (successChoice body)

/-- The original pivot-mask complement retains its actual fixed machine width. -/
def complementPivotMaskOp (columns : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .complement width ctx (.storage columns.toCStorageRef) columns

/-- The original final packOption reads the real current success and candidate cells. -/
def packOutput (success : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.option (.unsignedWord width))) : Circuit ctx ctx :=
  .classical (.packOption ctx
    (.product (.storage success.toCStorageRef) (.storage candidate.toCStorageRef)) output)

variable (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
  (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
  (used : CWriteRef ctx (.unsignedWord rowCount))
  (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
  (columns candidate zero : CWriteRef ctx (.unsignedWord width))
  (success : CWriteRef ctx .bit) (output : CWriteRef ctx (.option (.unsignedWord width)))

/-- Every original recovery stage runs in its original order on the same actual caller cells. -/
def into : Circuit ctx ctx :=
  .seq (loadAndReduce input matrix used rows columns)
    (.seq (.classical (complementPivotMaskOp columns))
      (.seq (.classical (pivotFoundOp success))
        (.seq (selectUniqueFree columns zero success)
          (.seq (whenSuccessful success (buildCandidate matrix rows columns candidate zero))
            (.seq (whenSuccessful success (checkCandidateNonzero candidate zero success))
              (.seq (whenSuccessful success (validateSamples input candidate success))
                (packOutput success candidate output)))))))

end QuantumAlg.ClassicalRoutines.GF2.Native
