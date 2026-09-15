/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Recovery.Semantics
import all QuantumAlg.Components.Classical.FirstAccepted.Placement.Semantics

/-!
# Complete actual six-stage attempt record

The first-success selector reads the acceptance and candidate produced by the
actual recovery and verification. Its conditional writes operate on that real
intermediate store, then release both decision bits. The original caller,
complete quantum-reference blocks and all prior history remain in one actual
record. No success, initialization or non-aliasing premise is needed for this
exact execution statement.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- The original selector consumes the real recovery and verification store. -/
def attemptStore (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (targetAccepted : CWriteRef ctx .bit)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord scalarWidth))
    (before : Store ctx) : Store ctx :=
  FirstAccepted.selectionWrite
    ⟨.storage targetAccepted.toCStorageRef, .storage candidate.toCStorageRef⟩ accepted selected
    (recoveryStore curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted before)

/-- One actual record preserves the original six stages, their complete store and actual paths. -/
theorem attemptInto_actualRecord (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (targetAccepted : CWriteRef ctx .bit)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord scalarWidth)) :
    ∃ record : Store ctx → Store ctx ×
        (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
          scalarResult targetAccepted accepted selected).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
          scalarResult targetAccepted accepted selected).execute Reference state =
            state.mapClassical (fun entry =>
              ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx, (record before).1 =
        attemptStore curve modulus sample base target inverseSuccess candidate reconstruction
          scalarResult targetAccepted accepted selected before := by
  obtain ⟨recoveryRecord, recoveryEquation, recoveryStored⟩ :=
    recoveryInto_actualRecord curve modulus sample base target inverseSuccess candidate
      reconstruction scalarResult targetAccepted
  obtain ⟨selectionRecord, selectionEquation, selectionStored⟩ :=
    FirstAccepted.withSelection_actualRecord
      ⟨.storage targetAccepted.toCStorageRef, .storage candidate.toCStorageRef⟩ accepted selected
  refine ⟨Circuit.sequenceRecord _ _ recoveryRecord selectionRecord,
    Circuit.execute_sequenceRecord _ _ _ _ recoveryEquation selectionEquation, ?_⟩
  intro before
  rw [Circuit.sequenceRecord_store, selectionStored, recoveryStored]
  rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
