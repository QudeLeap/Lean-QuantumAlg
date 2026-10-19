/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Cleanup
public import QuantumAlg.Core.Execution.Classical.Predicate
public import QuantumAlg.Core.Execution.Restart
public import QuantumAlg.Core.Execution.Input.Successor
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout
import all QuantumAlg.Core.Execution.Pure.Selection
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
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

private lemma cells_noBorrowed {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (dimension : ℕ+) (count : Nat) :
    (MeasurementCells.context ctx dimension count).borrowedQuantumWires =
      ctx.borrowedQuantumWires := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [MeasurementCells.context, RuntimeCtx.borrowedQuantumWires_addRetained]
        using ih

/-- The original point inputs are classical; the entire intrinsic quantum bank is owned. -/
lemma ecdlpReuse_noBorrowedQuantum (I : ECDLPInstance E) :
    (context I).borrowedQuantumWires = [] := by
  have original : (Sampling.pre I).borrowedQuantumWires = [] := rfl
  simpa only [context, RuntimeCtx.borrowedQuantumWires_addRetained, Sampling.post,
    cells_noBorrowed, Sampling.bankContext, RuntimeCtx.borrowedQuantumWires_addOwnedLayout]
      using original

/-- Every reused bank is nonempty because the original point encoding retains its infinity tag. -/
public lemma ecdlpReuse_systemCount_pos (I : ECDLPInstance E) : 0 < (context I).systemCount := by
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
public lemma ecdlpReuse_code_reinitializedAt {allowAllocation : Bool}
    (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    Circuit.ReinitializedAt (code (allowAllocation := allowAllocation) I expansion)
      (sourceEnvironment I A) (zeroSeed I)
        := by
  have empty : (context I).borrowedSelection = ∅ := by
    ext wire
    simp [RuntimeCtx.mem_borrowedSelection, ecdlpReuse_noBorrowedQuantum I]
  have all : (context I).borrowedSelectionᶜ = Finset.univ := by simp [empty]
  unfold Circuit.ReinitializedAt zeroSeed
  rw [all]
  intro Reference History _ state record
  exact StatePromise.pureKet_fullSelection_of_localMarginal (context I).quantumLayout
    (((code (allowAllocation := allowAllocation) I expansion).execute (sourceEnvironment I A)
      Reference state).block
        record)
    (context I).quantumLayout.zeroLabel (ecdlpReuse_code_block_pure
        (allowAllocation := allowAllocation) I A expansion state record)

/-- The same full sample circuit has its own physical measurement/restoration/restart evidence. -/
public lemma ecdlpReuse_code_restartCleanup {allowAllocation : Bool}
    (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    Circuit.RestartCleanup (code (allowAllocation := allowAllocation) I expansion)
      (sourceEnvironment I A) where
  measured := by
    intro path
    obtain ⟨dimension, present⟩ := ZReset.Bank.zResetBank_measured
        (allowAllocation := allowAllocation) (services := .empty)
      (oracles := model I) (ecdlpReuse_qubits I) (scratch I) BitWord.model
      (ecdlpReuse_systemCount_pos I) path.1
    exact ⟨dimension, List.mem_append.mpr (Or.inl present)⟩
  restores := by
    intro Reference History _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum (code (allowAllocation := allowAllocation)
      I expansion)
      (sourceEnvironment I A) (ecdlpReuse_noBorrowedQuantum I) Reference state
  reinitialized := ⟨zeroSeed I, ecdlpReuse_code_reinitializedAt (allowAllocation := allowAllocation)
      I A expansion⟩

end

end Sampling.Reuse

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
