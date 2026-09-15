/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Recovery.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Restoration
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Deterministic recovery of the actual native batch stores

The retained factor equals the original pure batch value when the actual
shared parameter is stored. Every previous classical read and the complete
quantum-reference state survive the allocated classical tail.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

-- Retained allocation changes no register; the original bank need not be unfolded here.
attribute [local irreducible] NativeBatch.context

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Every original structural read survives both real allocation and complete recovery. -/
theorem tail_callerFrame (input : Input N) (before : Store (NativeBatch.context base noQuantum N))
    {shape : CShape} (other : CInputRef (NativeBatch.context base noQuantum N) shape) :
    (step base noQuantum input before).1.read (liftInput base noQuantum N other) =
      before.read other :=
  (LatticeFixedBatchRecoveryMachine.into_callerFrame input (sourceParameter base noQuantum N)
    (terminals base noQuantum N) (resultRef base noQuantum N) _
    (liftInput base noQuantum N other) (result_avoids_input base noQuantum N other)).trans
      (Store.read_pushRetained_underRetained before _ _ _ other)

private theorem batchValue_allocated (sample : Fin (2 ^ residueSamplingBits N))
    (before : Store (NativeBatch.context base noQuantum N)) :
    LatticeFixedBatchRecoveryMachine.batchValue sample (terminals base noQuantum N)
      (before.pushRetained (resultKey base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N)
        (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh) =
      LatticeFixedBatchRecoveryMachine.batchValue sample (sourceTerminals base noQuantum N)
        before := by
  unfold LatticeFixedBatchRecoveryMachine.batchValue
  congr 2
  apply List.Vector.ext
  intro index
  simp only [LatticePairRecoveryBatch.preparedSamples, List.Vector.get_map,
    List.Vector.get_ofFn]
  congr 1
  funext bit
  unfold BatchMachine.sourceBits
  exact congrArg CShape.Value.toBool
    (Store.read_pushRetained_underRetained before _ _ _
      (.bitsGet (sourceTerminals base noQuantum N index) bit))

/-- The retained output is the exact original batch value of the actual sixteen source results. -/
theorem tail_output (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (before : Store (NativeBatch.context base noQuantum N))
    (parameterStored : before.read (NativeBatch.finalParameter base noQuantum N) =
      Canonical.parameterValue input sample) :
    (step base noQuantum input before).1.read
        (.storage (resultRef base noQuantum N).toCStorageRef) =
      LatticeFixedBatchRecoveryMachine.batchValue sample (sourceTerminals base noQuantum N)
        before := by
  have initialized : LatticeFixedBatchRecoveryMachine.InitialConditions input sample
      (before.pushRetained (resultKey base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N)
        (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh)
      (sourceParameter base noQuantum N) :=
    ⟨(Store.read_pushRetained_underRetained before _ _ _
      (NativeBatch.finalParameter base noQuantum N)).trans parameterStored⟩
  exact (LatticeFixedBatchRecoveryMachine.into_correct input sample
    (sourceParameter base noQuantum N) (terminals base noQuantum N) (resultRef base noQuantum N)
    _ initialized).output.trans (batchValue_allocated base noQuantum sample before)

/-- The complete output observes that same actual retained factor. -/
theorem run_output (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (before : Store (NativeBatch.context base noQuantum N))
    (parameterStored : before.read (NativeBatch.finalParameter base noQuantum N) =
      Canonical.parameterValue input sample) :
    (run base noQuantum input).output.eval (step base noQuantum input before).1 =
      LatticeFixedBatchRecoveryMachine.batchValue sample (sourceTerminals base noQuantum N)
        before :=
  tail_output base noQuantum input sample before parameterStored

/-- Recovery preserves the sampled residue in its original cell. -/
theorem tail_sample (input : Input N) (before : Store (NativeBatch.context base noQuantum N)) :
    (step base noQuantum input before).1.read (sourceSample base noQuantum N) =
      before.read (NativeBatch.finalSample base noQuantum N) :=
  tail_callerFrame base noQuantum input before _

/-- Recovery preserves the complete shared parameter in its original cell. -/
theorem tail_parameter (input : Input N) (before : Store (NativeBatch.context base noQuantum N)) :
    (step base noQuantum input before).1.read (sourceParameter base noQuantum N) =
      before.read (NativeBatch.finalParameter base noQuantum N) :=
  tail_callerFrame base noQuantum input before _

/-- Recovery preserves all sixteen actual source outcome cells together. -/
theorem tail_results (input : Input N) (before : Store (NativeBatch.context base noQuantum N)) :
    (step base noQuantum input before).1.read (sourceResults base noQuantum N) =
      before.read (NativeBatch.finalResults base noQuantum N) :=
  tail_callerFrame base noQuantum input before _

/-- The original complete classical source result survives as one joint structured value. -/
theorem tail_sourceOutput (input : Input N)
    (before : Store (NativeBatch.context base noQuantum N)) :
    (step base noQuantum input before).1.read
        (.product (sourceSample base noQuantum N)
          (.product (sourceParameter base noQuantum N) (sourceResults base noQuantum N))) =
      (NativeBatch.run base noQuantum N).output.eval before :=
  tail_callerFrame base noQuantum input before
    (.product (NativeBatch.finalSample base noQuantum N)
      (.product (NativeBatch.finalParameter base noQuantum N)
        (NativeBatch.finalResults base noQuantum N)))

/-- The tail leaves the entire actual bank jointly with an arbitrary reference unchanged. -/
theorem tail_quantumMarginal (input : Input N) :
    Circuit.RetainedQuantumPreserved (tail base noQuantum input) :=
  Circuit.RetainedRecord.quantumPreserved (tail base noQuantum input)
    (step base noQuantum input) (tail_execute base noQuantum input)

/-- Complete recovery preserves exactly the native source's outgoing quantum-reference state. -/
theorem code_quantumMarginal (input : Input N) :
    Circuit.RetainedTailQuantumPreserved (NativeBatch.code base noQuantum N)
      (tail base noQuantum input) :=
  Circuit.RetainedTailRecord.quantumPreserved (NativeBatch.code base noQuantum N)
    (tail base noQuantum input) (step base noQuantum input) (code_execute base noQuantum input)

/-- The allocated tail restores all borrowed classical, quantum and reference correlations. -/
theorem tail_borrowedRestored (input : Input N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (NativeBatch.context base noQuantum N) Reference History) :
    (tail base noQuantum input).BorrowedRestored Reference state
      ((tail base noQuantum input).execute Reference state) := by
  unfold tail
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_retain _ _ _ state
  · exact LatticeFixedBatchRecoveryMachine.into_borrowedRestored input
      (sourceParameter base noQuantum N) (terminals base noQuantum N)
      (resultRef base noQuantum N) Reference _

/-- The original first batch and complete recovery restore the same borrowed interface jointly. -/
theorem code_borrowedRestored (input : Input N) (Reference : Register)
    {History : Type} [Fintype History] (state : State base Reference History) :
    (code base noQuantum input).BorrowedRestored Reference state
      ((code base noQuantum input).execute Reference state) := by
  unfold code
  apply Circuit.borrowedRestored_seq
  · exact NativeBatch.nativeBatch_borrowedRestored base noQuantum N Reference state
  · exact tail_borrowedRestored base noQuantum input Reference _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery
