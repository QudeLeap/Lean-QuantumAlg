/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA2048.Measured.Success
import all QuantumAlg.Algorithms.Factoring.RSA2048.Measured.Contract
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Endpoint

/-!
# Conditional relational success of the actual measured four-batch program

The complete actual original-input/factor relation observes the same actual
optional output. The original twenty-member calibration supplies its fixed
ninety-nine-percent floor [EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA2048.Measured

noncomputable section

open Execution EkeraHastadStyle.Canonical

attribute [local instance] RSA.Configuration.rsa2048

/-- The fixed probability floor applies to the same original relational factor event. -/
lemma rsaMeasured2048_relational_twentyByFour_success_ge_99
    {environment : ShortDLP.CompiledMAU.Recycling.model.Environment}
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    {N : Nat} (specification : Input N) (model : NativeRSA2048.FixedKeyModel N)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference) :
    ENNReal.ofReal ((99 : Real) / 100) ≤
      ((RSA.Measured.Program.algorithm base noQuantum specification
        RSA.Configuration.rsa2048Batches).relationalDistribution environment input).toOuterMeasure
        {pair | (RSA.Measured.Program.fixedRoundProblem base noQuantum N
          RSA.Configuration.rsa2048Batches).accepts environment model.1 pair.1 pair.2} := by
  rw [RSA.Measured.Program.rsaMeasuredParent_relational_probability
    (environment := environment) base noQuantum specification model.1
    RSA.Configuration.rsa2048Batches input]
  exact rsaMeasured2048_run_twentyByFour_success_ge_99 base noQuantum specification model input

end

end QuantumAlg.Factoring.RSA2048.Measured
