/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Program
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Deterministic recovery of the actual native batch stores

The retained factor equals the original pure batch value when the actual
shared parameter is stored. Every previous classical read and the complete
quantum-reference state survive the allocated classical tail.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

-- Retained allocation changes no register; the original bank need not be unfolded here.
attribute [local irreducible] NativeBatchReuse.context

variable (base : RuntimeCtx .quantum) {N : Nat}
  (sameWires : base.quantumWires =
    (ShortDLP.CompiledMAU.runtimeLayout
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
  (originalCells : Fin (measurementBits N) → CWriteRef base (.finite 2))

/-- Every original structural read survives both real allocation and complete recovery. -/
theorem tail_callerFrame (input : Input N) (before : Store (NativeBatchReuse.context base N))
    {shape : CShape} (other : CInputRef (NativeBatchReuse.context base N) shape) :
    (step base input before).1.read (liftInput base N other) =
      before.read other :=
  (LatticeFixedBatchRecoveryMachine.into_callerFrame input (sourceParameter base N)
    (terminals base N) (resultRef base N) _
    (liftInput base N other) (result_avoids_input base N other)).trans
      (Store.read_pushRetained_underRetained before _ _ _ other)

private theorem batchValue_allocated (sample : Fin (2 ^ residueSamplingBits N))
    (before : Store (NativeBatchReuse.context base N)) :
    LatticeFixedBatchRecoveryMachine.batchValue sample (terminals base N)
      (before.pushRetained (resultKey base N) (LatticeBatchRecoveryOutput.OutputShape N)
        (NativeBatchReuse.context base N).canonicalFreshKey_fresh) =
      LatticeFixedBatchRecoveryMachine.batchValue sample (sourceTerminals base N)
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
      (.bitsGet (sourceTerminals base N index) bit))

/-- The retained output is the exact original batch value of the actual sixteen source results. -/
theorem tail_output (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (before : Store (NativeBatchReuse.context base N))
    (parameterStored : before.read (NativeBatchReuse.finalParameter base N) =
      Canonical.parameterValue input sample) :
    (step base input before).1.read
        (.storage (resultRef base N).toCStorageRef) =
      LatticeFixedBatchRecoveryMachine.batchValue sample (sourceTerminals base N)
        before := by
  have initialized : LatticeFixedBatchRecoveryMachine.InitialConditions input sample
      (before.pushRetained (resultKey base N) (LatticeBatchRecoveryOutput.OutputShape N)
        (NativeBatchReuse.context base N).canonicalFreshKey_fresh)
      (sourceParameter base N) :=
    ⟨(Store.read_pushRetained_underRetained before _ _ _
      (NativeBatchReuse.finalParameter base N)).trans parameterStored⟩
  exact (LatticeFixedBatchRecoveryMachine.into_correct input sample
    (sourceParameter base N) (terminals base N) (resultRef base N)
    _ initialized).output.trans (batchValue_allocated base sample before)

/-- The complete output observes that same actual retained factor. -/
theorem run_output (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (before : Store (NativeBatchReuse.context base N))
    (parameterStored : before.read (NativeBatchReuse.finalParameter base N) =
      Canonical.parameterValue input sample) :
    (run base sameWires originalCells input).output.eval (step base input before).1 =
      LatticeFixedBatchRecoveryMachine.batchValue sample (sourceTerminals base N)
        before :=
  tail_output base input sample before parameterStored

/-- Recovery preserves the sampled residue in its original cell. -/
theorem tail_sample (input : Input N) (before : Store (NativeBatchReuse.context base N)) :
    (step base input before).1.read (sourceSample base N) =
      before.read (NativeBatchReuse.finalSample base N) :=
  tail_callerFrame base input before _

/-- Recovery preserves the complete shared parameter in its original cell. -/
theorem tail_parameter (input : Input N) (before : Store (NativeBatchReuse.context base N)) :
    (step base input before).1.read (sourceParameter base N) =
      before.read (NativeBatchReuse.finalParameter base N) :=
  tail_callerFrame base input before _

/-- Recovery preserves all sixteen actual source outcome cells together. -/
theorem tail_results (input : Input N) (before : Store (NativeBatchReuse.context base N)) :
    (step base input before).1.read (sourceResults base N) =
      before.read (NativeBatchReuse.finalResults base N) :=
  tail_callerFrame base input before _

/-- The original complete classical source result survives as one joint structured value. -/
theorem tail_sourceOutput (input : Input N)
    (before : Store (NativeBatchReuse.context base N)) :
    (step base input before).1.read
        (.product (sourceSample base N)
          (.product (sourceParameter base N) (sourceResults base N))) =
      (NativeBatchReuse.run base N sameWires originalCells).output.eval before :=
  tail_callerFrame base input before
    (.product (NativeBatchReuse.finalSample base N)
      (.product (NativeBatchReuse.finalParameter base N)
        (NativeBatchReuse.finalResults base N)))

/-- The tail leaves the entire actual bank jointly with an arbitrary reference unchanged. -/
theorem tail_quantumMarginal (input : Input N) :
    Circuit.RetainedQuantumPreserved (tail base input) :=
  Circuit.RetainedRecord.quantumPreserved (tail base input)
    (step base input) (tail_execute base input)

/-- Complete recovery preserves exactly the native source's outgoing quantum-reference state. -/
theorem code_quantumMarginal (input : Input N) :
    Circuit.RetainedTailQuantumPreserved (NativeBatchReuse.code base N sameWires originalCells)
      (tail base input) :=
  Circuit.RetainedTailRecord.quantumPreserved (NativeBatchReuse.code base N sameWires originalCells)
    (tail base input) (step base input) (code_execute base sameWires originalCells input)

/-- The allocated tail restores all borrowed classical, quantum and reference correlations. -/
theorem tail_borrowedRestored (input : Input N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (NativeBatchReuse.context base N) Reference History) :
    (tail base input).BorrowedRestored Reference state
      ((tail base input).execute Reference state) := by
  unfold tail
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_retain _ _ _ state
  · exact LatticeFixedBatchRecoveryMachine.into_borrowedRestored input
      (sourceParameter base N) (terminals base N)
      (resultRef base N) Reference _

/-- The owned original bank and complete recovery restore the same borrowed interface jointly. -/
theorem code_borrowedRestored (input : Input N)
    (noBorrowed : base.borrowedQuantumWires = []) (Reference : Register)
    {History : Type} [Fintype History] (state : State base Reference History) :
    (code base sameWires originalCells input).BorrowedRestored Reference state
      ((code base sameWires originalCells input).execute Reference state) := by
  unfold code
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (NativeBatchReuse.code base N sameWires originalCells) noBorrowed Reference state
  · exact tail_borrowedRestored base input Reference _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery
