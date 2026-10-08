/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Cleanup
public import QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout
import all QuantumAlg.Core.Execution.Pure.Selection
import all QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Primitives.ZReset.Bank

/-!
# Physical restart of the actual allocation-free declared-query ECDLP round

The same intrinsic bank has no borrowed quantum wire. Every actual round
measures physical systems, restores the complete original borrowed interface
and prepares a predetermined zero seed on every owned system in every complete
record. This physical certificate alone grants no completed-protocol cycle cut.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

namespace Sampling.Reuse

noncomputable section

open Execution

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private theorem cells_noBorrowed {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (dimension : ℕ+) (count : Nat) :
    (MeasurementCells.context ctx dimension count).borrowedQuantumWires =
      ctx.borrowedQuantumWires := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [MeasurementCells.context, RuntimeCtx.borrowedQuantumWires_addRetained]
        using ih

/-- The original point inputs are classical; the entire intrinsic quantum bank is owned. -/
theorem ecdlpReuse_noBorrowedQuantum (I : ECDLPInstance E) :
    (context I).borrowedQuantumWires = [] := by
  have original : (Sampling.pre I).borrowedQuantumWires = [] := rfl
  simpa only [context, RuntimeCtx.borrowedQuantumWires_addRetained, Sampling.post,
    cells_noBorrowed, Sampling.bankContext, RuntimeCtx.borrowedQuantumWires_addOwnedLayout]
      using original

/-- Every reused bank is nonempty because the original point encoding retains its infinity tag. -/
public theorem ecdlpReuse_systemCount_pos (I : ECDLPInstance E) : 0 < (context I).systemCount := by
  have positive : 0 < Layout.totalQubits I := by
    unfold Layout.totalQubits Layout.pointWidth
    omega
  let source : Fin (Layout.totalQubits I) := ⟨0, positive⟩
  let actual : Fin (context I).systemCount := Sampling.wireEquiv I source
  exact lt_of_le_of_lt (Nat.zero_le actual.val) actual.isLt

/-- Restrict the same predetermined full zero label to the actual owned output systems. -/
public def zeroSeed (I : ECDLPInstance E) :
    (context I).quantumLayout.SelectedBasis (context I).borrowedSelectionᶜ :=
  (context I).quantumLayout.restrictSelectedBasis (context I).borrowedSelectionᶜ
    (context I).quantumLayout.zeroLabel

/-- Every complete actual sample record has the same zero state on every owned physical wire. -/
public theorem ecdlpReuse_code_reinitializedAt (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    Circuit.ReinitializedAt (code I A expansion) (zeroSeed I) := by
  have empty : (context I).borrowedSelection = ∅ := by
    ext wire
    simp [RuntimeCtx.mem_borrowedSelection, ecdlpReuse_noBorrowedQuantum I]
  have all : (context I).borrowedSelectionᶜ = Finset.univ := by simp [empty]
  unfold Circuit.ReinitializedAt zeroSeed
  rw [all]
  intro Reference History _ state record
  exact StatePromise.pureKet_fullSelection_of_localMarginal (context I).quantumLayout
    (((code I A expansion).execute Reference state).block record)
    (context I).quantumLayout.zeroLabel (ecdlpReuse_code_block_pure I A expansion state record)

/-- The same full sample circuit has its own physical measurement/restoration/restart evidence. -/
public theorem ecdlpReuse_code_restartCleanup (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    Circuit.RestartCleanup (code I A expansion) where
  measured := by
    intro path
    obtain ⟨dimension, present⟩ := ZReset.Bank.zResetBank_measured
      (oracles := model I A) (ecdlpReuse_qubits I) (scratch I) BitWord.model
      (ecdlpReuse_systemCount_pos I) path.1
    exact ⟨dimension, List.mem_append.mpr (Or.inl present)⟩
  restores := by
    intro Reference History _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum (code I A expansion)
      (ecdlpReuse_noBorrowedQuantum I) Reference state
  reinitialized := ⟨zeroSeed I, ecdlpReuse_code_reinitializedAt I A expansion⟩

end

end Sampling.Reuse

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
