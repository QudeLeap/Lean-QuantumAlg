/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.WalshHadamard.Readout.Distribution
import all QuantumAlg.Algorithms.DeutschJozsa.Construction
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Algorithms.DeutschJozsa.Specification
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.WalshHadamard

/-!
# Exact decision probability of the native execution

The distribution below is obtained from the actual final Store blocks.
The original mathematical Born distribution is used only on the right of a
proved equality, after actual preparation, measurement writes and packing
have already determined every block mass.
-/

namespace QuantumAlg.DeutschJozsa

open WalshHadamard.Readout

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution

/-- Under the original promise the actual relational result makes the correct decision surely. -/
lemma actual_success {n : Nat} (f : WalshHadamard.Oracle n) (promised : Promise f)
    {Reference : Register} (input : OracleInput ClassicalOracleModel.empty pre Reference) :
    ((run n).relationalDistribution (environment f) input).toOuterMeasure
      {pair | accepts f pair.1 pair.2} = 1 := by
  have projection :
      ((run n).relationalDistribution (environment f) input).toOuterMeasure
        {pair | accepts f pair.1 pair.2} =
      ((run n).outputDistribution (environment f) input).toOuterMeasure
        {result | match result with | .bits outcome => CorrectDecision f outcome} := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection, outputDistribution_eq f input, PMF.toOuterMeasure_map_apply]
  exact correctDecision_probability_one f promised

end

end QuantumAlg.DeutschJozsa
