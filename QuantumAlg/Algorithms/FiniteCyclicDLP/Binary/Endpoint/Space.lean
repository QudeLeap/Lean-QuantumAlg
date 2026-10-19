/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Run
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Context
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.Trivial.Native.Resources
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.Trivial.Native
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Resources
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.CheckedSelection.Resources
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Selection.Resources
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.NormalizedRecovery.Native.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Selection.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Bounds
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Correction.Resources
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Space
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# One binary quantum bank throughout the complete finite-cyclic execution

Every actual classical workspace and retained result has zero quantum-system
coordinates. Projecting the complete same-path resident allowance therefore
leaves precisely the one binary bank, including order one and zero group width.
No abstract group element is assigned an unimplemented quantum representation
[Sho95, source.tex:1713-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

private lemma classicalShapes_qubits (shapes : List CShape) :
    SpacePool.count (.quantumSystems 2)
      ((shapes.map SpacePool.ofShape).sum : SpacePool .quantum) = 0 := by
  induction shapes with
  | nil => rfl
  | cons shape shapes ih =>
    simpa only [List.map_cons, List.sum_cons, SpacePool.count_add,
      SpacePool.count_quantumSystems_ofShape, zero_add] using ih

/-- The real recovery scratch comprises only classical shapes. -/
public lemma recoveryScratchBudget_qubits (P : KnownOrderProblem G) :
    SpacePool.count (.quantumSystems 2) (recoveryScratchBudget P) = 0 := by
  simp [recoveryScratchBudget,
    ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroActiveSpace,
    OrderRecovery.Native.recoveryScratchSpace, OrderRecovery.Native.selectionAttemptSpace,
    OrderRecovery.Native.attemptActiveSpace,
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.singleExposureActiveSpace,
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.checkedExposurePersistentSpace,
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.checkedRecoveryActiveSpace,
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.selectedRecoveryScratchSpace,
    ClassicalRoutines.FiniteCyclicDLP.NormalizedRecovery.Native.recoveryScratchSpace_eq_bits,
    ClassicalRoutines.NumberTheory.Checked.Native.checkedInverseActiveSpace,
    ClassicalRoutines.NumberTheory.Checked.Native.checkedSelectionSpaceLimit,
    ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native.signedReductionSpaceLimit,
    ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native.signedReductionScratchSpace,
    ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native.signedReductionArithmeticSpace,
    ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native.negativeCorrectionScratchSpace,
    ClassicalRoutines.NumberTheory.XGCD.Native.rawScratchSpace, classicalShapes_qubits]

omit [Fintype G] in
/-- Retaining the final optional word adds no quantum wire. -/
public lemma outputContext_qubits (P : KnownOrderProblem G) :
    SpacePool.count (.quantumSystems 2) (outputContext P).residentSpace =
      Reusable.bankWidth P := by
  rw [outputContext, RuntimeCtx.residentSpace_addRetained, SpacePool.count_add,
    SpacePool.count_quantumSystems_ofShape, zero_add]
  exact Reusable.context_qubits P (sampleCount P)

/-- The independently certified complete-run allowance has exactly the one actual bank. -/
public lemma residentBudget_qubits (P : KnownOrderProblem G) :
    SpacePool.count (.quantumSystems 2) (residentBudget P) =
      Reusable.bankWidth P := by
  rw [residentBudget, SpacePool.count_add, recoveryScratchBudget_qubits,
    outputContext_qubits, zero_add]

/-- Every actual endpoint path, including recovery, uses at most `2t + n` physical qubits. -/
public lemma code_qubits_le (P : KnownOrderProblem G) (path : (code P).Path) :
    SpacePool.count (.quantumSystems 2) ((code P).peakResidentSpace path) ≤
      2 * OrderPreparation.width P + Binary.groupWidth P := by
  have bound := SpacePool.le_iff_count.mp (binaryEndpoint_code_resident_le P path)
    (.quantumSystems 2)
  rw [residentBudget_qubits] at bound
  simpa only [Reusable.bankWidth, Reusable.sampleWidth, two_mul] using bound

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint
