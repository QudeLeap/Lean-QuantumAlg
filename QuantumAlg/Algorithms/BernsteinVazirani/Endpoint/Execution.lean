/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.BernsteinVazirani.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.BernsteinVazirani.Construction
import all QuantumAlg.Algorithms.BernsteinVazirani.Specification
import all QuantumAlg.Primitives.WalshHadamard.Readout.Geometry
import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution
import all QuantumAlg.Primitives.WalshHadamard.Readout.Distribution
import all QuantumAlg.Primitives.WalshHadamard.Readout.Restoration
import all QuantumAlg.Primitives.WalshHadamard.Readout.Resources
import all QuantumAlg.Primitives.WalshHadamard.Readout.Space
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Measure.Distribution

/-!
# Complete native Bernstein-Vazirani recovery

The hidden string supplies only the inner-product oracle. The common
Walsh-Hadamard execution prepares its own quantum input and computes the
answer from actual Z writes and finite-bit packing. Its complete Output
retains every live entry. The exact mathematical recovery theorem is
connected to the same execution's final block probabilities, and its paths
satisfy the independent native budgets for every width, including zero.
-/

namespace QuantumAlg.BernsteinVazirani

open WalshHadamard.Readout

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The shared actual execution with the hidden-string oracle and complete live Output. -/
public def algorithm (n : Nat) :
    Algorithm (model n) pre (post n) (.bits n) where
  run := WalshHadamard.Readout.run n

private lemma actual_success {n : Nat} (hidden : Fin (2 ^ n))
    {Reference : Register}
    (input : Execution.OracleInput ClassicalOracleModel.empty pre Reference) :
    ((WalshHadamard.Readout.run n).relationalDistribution
      (environment (oracle hidden)) input).toOuterMeasure
      {pair | accepts hidden pair.1 pair.2} = 1 := by
  have projection :
      ((WalshHadamard.Readout.run n).relationalDistribution
        (environment (oracle hidden)) input).toOuterMeasure
        {pair | accepts hidden pair.1 pair.2} =
      ((WalshHadamard.Readout.run n).outputDistribution
        (environment (oracle hidden)) input).toOuterMeasure
        {result | match result with | .bits outcome => outcome = measurementOutcome n hidden} := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection, WalshHadamard.Readout.outputDistribution_eq,
    PMF.toOuterMeasure_map_apply]
  change ((measurement n).outcomePMF
    (WalshHadamard.Readout.evolvedState (oracle hidden))).toOuterMeasure
        {measurementOutcome n hidden} = 1
  have normalized :
      (WalshHadamard.Readout.evolvedState (oracle hidden)).normalized =
          (evolvedState hidden).normalized := rfl
  rw [TerminalZMeasure.outcomePMF_congr_normalized (measurement n) normalized,
    PMF.toOuterMeasure_apply_singleton]
  exact measurementOutcome_probability_one hidden

end

end QuantumAlg.BernsteinVazirani
