/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Generic
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Doubling
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Infinity

/-!
# Actual original complete point-addition circuit

The original real classifier precedes its original complete case selection.
Both infinity copies, inverse or vertical output, finite doubling and generic
addition are actual native programs. Each arithmetic branch owns its original
constant loads and lexical storage; the caller provides only point references
and the destination, including any legal destination alias.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Every original selected case executes its corresponding actual complete native arm. -/
def additionArm (spec : CurveSpec width) (classifier : Classifier ctx width)
    (output : CWriteRef ctx (PointShape width)) : Case → Circuit ctx ctx
  | .leftInfinity => repackRawInto (classifierRead classifier.rightRaw) output
  | .rightInfinity => repackRawInto (classifierRead classifier.leftRaw) output
  | .vertical => infinityInto output
  | .doubling => doublingInto spec (classifierRead classifier.leftRaw) output
  | .generic => genericInto spec.field (classifierRead classifier.leftRaw)
      (classifierRead classifier.rightRaw) output

/-- Actual total point addition with original classification, branches, loaders and work scopes. -/
def addInto (spec : CurveSpec width) (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx (PointShape width)) : Circuit ctx ctx :=
  withClassification left right fun classifier transport =>
    dispatch classifier (additionArm spec classifier (transport.liftWrite output))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
