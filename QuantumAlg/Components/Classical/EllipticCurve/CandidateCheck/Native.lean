/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.ScalarMul.Native
import all QuantumAlg.Components.Classical.EllipticCurve.PointEquality.Native

/-!
# Actual original elliptic-curve recovery candidate verification

The candidate word supplies its original most-significant-first scalar bits.
The actual complete scalar multiplication runs even on raw-recovery failure,
then the actual full point comparison checks the target. Its real stored
decision is conjoined first with inverse success, then with reconstruction
success. The first-success selector is the subsequent separate program stage.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- The original stored candidate is read structurally in most-significant-first order. -/
def candidateBits (candidate : CInputRef ctx (.unsignedWord scalarWidth)) :
    CInputRef ctx (.fixedVector scalarWidth .bit) :=
  .fixedVector fun index => .wordBitGet candidate index

/-- Original in-place Boolean conjunction into the actual point-acceptance cell. -/
def conjunctionOp (flag : CInputRef ctx .bit) (accepted : CWriteRef ctx .bit) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (.storage accepted.toCStorageRef) flag) accepted

/-- Four original actual stages, retaining the same scalar and acceptance destinations. -/
def verificationStage {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit) :
    Fin 4 → Circuit model ctx ctx := ![
      ScalarMul.Native.scalarInto spec (candidateBits candidate) base scalarResult,
      PointEquality.Native.compareInto (.storage scalarResult.toCStorageRef) target accepted,
      BitWord.instruction (execution := model) (conjunctionOp inverseSuccess accepted),
      BitWord.instruction (execution := model) (conjunctionOp reconstruction accepted)]

/-- The original scalar, target comparison and two success conjunctions all actually execute. -/
def verifyInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit) :
    Circuit model ctx ctx :=
  Circuit.forRange 4
    (verificationStage spec candidate base target inverseSuccess reconstruction
      scalarResult accepted)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
