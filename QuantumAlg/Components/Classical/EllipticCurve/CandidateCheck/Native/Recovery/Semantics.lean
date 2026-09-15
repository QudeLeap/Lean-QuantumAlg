/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Recovery
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Semantics
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Semantics
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Complete actual recovery and verification record

The exact three chronological recovery writes feed the real verification
record on the resulting store. The full-state equation follows the original
sequence instruction and preserves every quantum-reference block and prior
history. It holds for all actual caller aliases, including their real overwrite
effects, without a caller initialization, inverse or secret witness.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- Actual recovery writes precede the original complete verification store update. -/
def recoveryStore (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (before : Store ctx) : Store ctx :=
  (verifyStep curve (.storage candidate.toCStorageRef) base target
    (.storage inverseSuccess.toCStorageRef) (.storage reconstruction.toCStorageRef)
    scalarResult accepted
    (FiniteCyclicDLP.RawRecovery.Native.exposureWrite inverseSuccess candidate reconstruction before
      (FiniteCyclicDLP.RawRecovery.outputCells modulus
        (FiniteCyclicDLP.RawRecovery.Native.preparationInput (before.read sample))))).1

/-- The original five stages have one full-state record on their genuine intermediate store. -/
theorem recoveryInto_actualRecord (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit) :
    ∃ record : Store ctx → Store ctx ×
        (recoveryInto curve modulus sample base target inverseSuccess candidate reconstruction
          scalarResult accepted).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (recoveryInto curve modulus sample base target inverseSuccess candidate reconstruction
          scalarResult accepted).execute Reference state = state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx, (record before).1 =
        recoveryStore curve modulus sample base target inverseSuccess candidate reconstruction
          scalarResult accepted before := by
  obtain ⟨rawRecord, rawEquation, rawStore⟩ :=
    FiniteCyclicDLP.RawRecovery.Native.singleIntoCells_actualRecord
      modulus sample inverseSuccess candidate reconstruction
  let checked := verifyStep curve (.storage candidate.toCStorageRef) base target
    (.storage inverseSuccess.toCStorageRef) (.storage reconstruction.toCStorageRef)
    scalarResult accepted
  refine ⟨Circuit.sequenceRecord _ _ rawRecord checked, ?_, ?_⟩
  · intro Reference History _ state
    exact Circuit.execute_sequenceRecord _ _ rawRecord checked rawEquation
      (verifyInto_execute curve (.storage candidate.toCStorageRef) base target
        (.storage inverseSuccess.toCStorageRef) (.storage reconstruction.toCStorageRef)
        scalarResult accepted) Reference state
  · intro before
    rw [Circuit.sequenceRecord_store, rawStore]
    rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
