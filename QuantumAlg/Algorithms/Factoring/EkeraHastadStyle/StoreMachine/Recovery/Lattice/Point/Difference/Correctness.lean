/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Difference

/-!
# Actual point subtraction correctness

Original source-versus-output and output-versus-output separation preserve
all reads used by later subtractions. No signed range or scratch-value premise
is required for the exact modular representation, including width zero.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePointDifferenceMachine

open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem source_frame (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (written : DifferenceCell) (source : SourceCell) :
    (store.applyOp (differenceOp refs written)).read (sourceInput refs source) =
      store.read (sourceInput refs source) :=
  Store.read_applyOp_of_not_mem_storageKeys store (differenceOp refs written) _
    (separation.sourceAvoidsDifference source written)

private theorem output_frame (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (written saved : DifferenceCell) (different : written ≠ saved) :
    (store.applyOp (differenceOp refs written)).read (writeInput (differenceRef refs saved)) =
      store.read (writeInput (differenceRef refs saved)) := by
  apply Store.read_applyOp_of_not_mem_storageKeys
  change differenceKey refs written ∉ [differenceKey refs saved]
  simp only [List.mem_singleton]
  intro equal
  exact different (separation.differenceInjective equal)

private theorem coordinate_correct (refs : Refs ctx width) (cell : DifferenceCell)
    (store : Store ctx) (left right : Int)
    (leftRep : RawSignedRepresents (store.read (sourceInput refs (pointSource cell))) left)
    (rightRep : RawSignedRepresents (store.read (sourceInput refs (targetSource cell))) right) :
    RawSignedRepresents ((store.applyOp (differenceOp refs cell)).read
      (writeInput (differenceRef refs cell))) (left - right) := by
  change RawSignedRepresents ((store.applyOp (differenceOp refs cell)).read
    (.storage (differenceOp refs cell).outputRef.toCStorageRef)) _
  rw [Store.read_applyOp_output]
  exact rawSignedWordRepresents_sub (store.read (sourceInput refs (pointSource cell)))
    (store.read (sourceInput refs (targetSource cell))) left right leftRep rightRep

/-- The three actual stored coordinates represent the original integer point difference. -/
theorem pointDifferenceInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (point target : NumberTheory.IntegerPoint3)
    (pointRep : LatticeArithmetic.PointRawRepresents store refs.point point)
    (targetRep : LatticeArithmetic.PointRawRepresents store refs.target target) :
    LatticeArithmetic.PointRawRepresents (differenceStore refs store) refs.difference
      (point.sub target) := by
  unfold differenceStore
  refine ⟨?_, ?_, ?_⟩
  · rw [output_frame refs separation _ .third .first (by decide),
      output_frame refs separation _ .second .first (by decide)]
    apply coordinate_correct refs .first
    · exact pointRep.1
    · exact targetRep.1
  · rw [output_frame refs separation _ .third .second (by decide)]
    apply coordinate_correct refs .second
    · rw [source_frame refs separation _ .first .pointSecond]
      exact pointRep.2.1
    · rw [source_frame refs separation _ .first .targetSecond]
      exact targetRep.2.1
  · apply coordinate_correct refs .third
    · rw [source_frame refs separation _ .second .pointThird,
        source_frame refs separation _ .first .pointThird]
      exact pointRep.2.2
    · rw [source_frame refs separation _ .second .targetThird,
        source_frame refs separation _ .first .targetThird]
      exact targetRep.2.2

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePointDifferenceMachine
