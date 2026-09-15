/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FirstPair.Program.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FirstPair.Program.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Program.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Program.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Gram.Program.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Gram.Program.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Phase
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Bounds.Step
import all QuantumAlg.Core.Execution.Classical.Iteration

/-!
# Original fixed-fuel LLL allocation and invariant

The original two phase bits and shared basis/Gram wiring are unchanged. The
invariant now describes the actual store at each iteration of the circuit.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine

open Execution

noncomputable section

/-- References for the fixed-fuel driver, including its shared package wiring. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Nested references for the machine stage. -/
  machine : LatticeState.MachineRefs ctx width
  /-- Nested references for the metric stage. -/
  metric : LatticeMetricMachine.Refs ctx width
  /-- Nested references for the first stage. -/
  first : LatticeFirstPairMachine.Refs ctx width
  /-- Nested references for the second stage. -/
  second : LatticeSecondPairFullMachine.Refs ctx width
  firstBasis : first.basis = machine.basis
  firstMetric : first.metric = metric
  secondBasis : second.machine.basis = machine.basis
  secondMetric : second.machine.metric = metric

/-- Read the actual caller-owned phase bit. -/
def phaseInput {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (phase : CWriteRef ctx .bit) : CInputRef ctx .bit :=
  .storage phase.toCStorageRef

/--
Package-local separation plus the phase-bit caller frames required by each
non-terminal package.  It intentionally does not assert cross-package scratch
separation beyond these structural phase reads.
-/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  machine : refs.machine.Separated
  metric : LatticeMetricMachine.Separation refs.machine.basis refs.metric
  first : LatticeFirstPairMachine.Separation refs.first
  second : LatticeSecondPairFullMachine.Separation refs.second
  secondPhaseMetric : ∀ cell : LatticeMetricMachine.MetricCell,
    LatticeMetricMachine.metricCellKey refs.metric cell ∉ (phaseInput
      refs.machine.secondPhase).storageKeys
  secondPhaseFirst : ∀ cell : LatticeFirstPairMachine.TransitionCell,
    LatticeFirstPairMachine.cellKey refs.first cell ∉ (phaseInput
      refs.machine.secondPhase).storageKeys
  secondPhaseSecond : ∀ cell : LatticeSecondPairFullMachine.Cell,
    LatticeSecondPairFullMachine.cellKey refs.second cell ∉ (phaseInput
      refs.machine.secondPhase).storageKeys
  doneMetric : ∀ cell : LatticeMetricMachine.MetricCell,
    LatticeMetricMachine.metricCellKey refs.metric cell ∉ (phaseInput refs.machine.done).storageKeys
  doneFirst : ∀ cell : LatticeFirstPairMachine.TransitionCell,
    LatticeFirstPairMachine.cellKey refs.first cell ∉ (phaseInput refs.machine.done).storageKeys
  doneSecond : ∀ cell : LatticeSecondPairFullMachine.Cell,
    LatticeSecondPairFullMachine.cellKey refs.second cell ∉ (phaseInput
      refs.machine.done).storageKeys

/-- The raw-store facts carried by one fixed-fuel lattice-machine state. -/
structure StoreInvariant {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (input : NumberTheory.IntegerBasis3)
    (observation : Store ctx) (state : NumberTheory.LLLState3) : Prop where
  basis : LatticeMetricMachine.BasisRawRepresents observation refs.machine.basis state.basis
  phase : refs.machine.PhaseRepresents observation state.phase
  gram : LatticeMetricMachine.GramRawRepresents observation refs.metric state.basis
  bounded : state.BoundedFrom input
  capacity :
    Nat.size (256 * (NumberTheory.lllStateEnvelope3 input + 1) ^ 8) + 1 ≤ width
  stepFits : LatticeStepBounds.StepFits width state.basis


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine
