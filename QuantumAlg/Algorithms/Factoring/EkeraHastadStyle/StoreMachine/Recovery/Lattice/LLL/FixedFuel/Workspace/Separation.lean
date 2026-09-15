/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Workspace.Separation.Second

/-!
# Physical separation for the complete fixed-fuel LLL driver
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelScratchWorkspaceSeparation

open ClassicalRoutines
open ClassicalRoutines.NumberTheory
open Execution

noncomputable section

/-- Each named Gram word is the corresponding unified driver key. -/
theorem metricCellKey_eq_driverKey {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N)
    (cell : LatticeMetricMachine.MetricCell) :
    LatticeMetricMachine.metricCellKey
        (LatticeFixedFuelScratchWorkspaceViews.metricRefs scratch) cell =
      driverKey state scratch (.inr (metricCell cell)) := by
  cases cell <;> rfl

/-- The physical state and reusable scratch packages satisfy the complete
fixed-fuel driver separation contract. -/
theorem driverSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    LatticeFixedFuelMachine.Separation
      (LatticeFixedFuelScratchWorkspaceViews.driverRefs
        state scratch) := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.driverRefs
    state scratch
  have keyInjective : Function.Injective
      (driverKey state scratch) :=
    driverKey_injective certificates
  have secondPhaseAvoids (target : DriverCell)
      (different : (Sum.inl .secondPhase : DriverCell) ≠ target) :
      (driverKey state scratch target) ∉
        (LatticeFixedFuelMachine.phaseInput refs.machine.secondPhase).storageKeys := by
    apply storageRead_avoids_of_key_ne
    change driverKey state scratch (.inl .secondPhase) ≠
      driverKey state scratch target
    intro equal
    exact different (keyInjective equal)
  have doneAvoids (target : DriverCell)
      (different : (Sum.inl .done : DriverCell) ≠ target) :
      (driverKey state scratch target) ∉
        (LatticeFixedFuelMachine.phaseInput refs.machine.done).storageKeys := by
    apply storageRead_avoids_of_key_ne
    change driverKey state scratch (.inl .done) ≠
      driverKey state scratch target
    intro equal
    exact different (keyInjective equal)
  refine {
    machine := machineSeparated certificates
    metric := metricSeparation certificates
    first := firstSeparation certificates
    second := secondSeparation certificates
    secondPhaseMetric := ?_
    secondPhaseFirst := ?_
    secondPhaseSecond := ?_
    doneMetric := ?_
    doneFirst := ?_
    doneSecond := ?_ }
  · intro cell
    change
      (LatticeMetricMachine.metricCellKey
          (LatticeFixedFuelScratchWorkspaceViews.metricRefs scratch) cell) ∉
            (LatticeFixedFuelMachine.phaseInput refs.machine.secondPhase).storageKeys
    rw [metricCellKey_eq_driverKey]
    exact secondPhaseAvoids (.inr (metricCell cell)) (by
      cases cell <;> decide)
  · intro cell
    simpa only [refs, LatticeFixedFuelScratchWorkspaceViews.driverRefs,
      firstCellKey_eq_driverKey] using
      secondPhaseAvoids (firstTransitionCell cell) (by
        cases cell <;> decide)
  · intro cell
    change
      (LatticeSecondPairFullMachine.cellKey
          (LatticeFixedFuelScratchWorkspaceViews.secondRefs
            state scratch) cell) ∉
              (LatticeFixedFuelMachine.phaseInput refs.machine.secondPhase).storageKeys
    rw [secondFullCellKey_eq_driverKey]
    exact secondPhaseAvoids (secondFullCell cell)
      (secondPhase_ne_secondFullCell cell)
  · intro cell
    change (LatticeMetricMachine.metricCellKey
        (LatticeFixedFuelScratchWorkspaceViews.metricRefs scratch) cell) ∉
          (LatticeFixedFuelMachine.phaseInput refs.machine.done).storageKeys
    rw [metricCellKey_eq_driverKey]
    exact doneAvoids (.inr (metricCell cell)) (by
      cases cell <;> decide)
  · intro cell
    simpa only [refs, LatticeFixedFuelScratchWorkspaceViews.driverRefs,
      firstCellKey_eq_driverKey] using
      doneAvoids (firstTransitionCell cell) (by
        cases cell <;> decide)
  · intro cell
    change (LatticeSecondPairFullMachine.cellKey
        (LatticeFixedFuelScratchWorkspaceViews.secondRefs
          state scratch) cell) ∉ (LatticeFixedFuelMachine.phaseInput refs.machine.done).storageKeys
    rw [secondFullCellKey_eq_driverKey]
    exact doneAvoids (secondFullCell cell) (done_ne_secondFullCell cell)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelScratchWorkspaceSeparation
