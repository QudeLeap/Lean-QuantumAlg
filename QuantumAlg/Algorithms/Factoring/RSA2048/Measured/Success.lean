/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Success
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.KeyAverage
import all QuantumAlg.Algorithms.Factoring.RSA.Configuration
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Count
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Calibration

/-!
# Twenty-member, four-batch success of the actual measured RSA execution

The fixed static configuration selects twenty real members and every one of
its 190 recovery pairs. The original ordered-key distribution is unchanged;
its exceptional mass is charged once, outside the four conditional failures.
-/

namespace QuantumAlg.Factoring.RSA2048.Measured

noncomputable section

open Execution
open EkeraHastadStyle.Canonical

attribute [local instance] RSA.Configuration.rsa2048

private lemma rsaMeasured2048_model_strongTradeoff {N : Nat} (model : NativeRSA2048.FixedKeyModel
    N) :
    (registerParameters N).m + 1 ≤ 2 * (registerParameters N).ell := by
  change shortLogBits N + 1 ≤ 2 * tradeoffBits N
  exact NativeRSA2048.model_strongTradeoff model.widthModel

/-- The actual twenty-member batch has the exact calibrated conditional failure ceiling. -/
lemma rsaMeasured2048_batchFailure_twenty_le {N : Nat} (model : NativeRSA2048.FixedKeyModel N) :
    sampledBatchOutputPMFAtCount model.1.input RSA.membersPerBatch none ≤
      NativeRSA2048.Calibration.twentyBatchFailure := by
  change sampledBatchOutputPMFAtCount model.1.input 20 none ≤ _
  have bounded := NativeBatchSuccess.sampled_twenty_none_le model.1
    (rsaMeasured2048_model_strongTradeoff model)
  rw [model.2] at bounded
  exact bounded.trans_eq
    NativeRSA2048.Calibration.twentyBatchFailure_eq_one_sub_successFloor.symm

attribute [local irreducible] sampledBatchOutputPMFAtCount fixedBatchOutputPMFAtCount

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- Every original good RSA-2048 key has success at least 99 percent on the actual four batches. -/
lemma rsaMeasured2048_run_twentyByFour_success_ge_99
    {environment : ShortDLP.CompiledMAU.Recycling.model.Environment}
    {N : Nat} (specification : Input N) (model : NativeRSA2048.FixedKeyModel N)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference) :
    ENNReal.ofReal ((99 : Real) / 100) ≤
      ((RSA.Measured.Program.run base noQuantum N specification
        RSA.Configuration.rsa2048Batches).outputDistribution environment input).toOuterMeasure
          {output | output ≠ CShape.Value.optionNone} := by
  rw [RSA.Measured.Program.rsaMeasuredParent_run_successProbability]
  have sameFailure := congrArg
    (fun proof : Input N => sampledBatchOutputPMFAtCount proof RSA.membersPerBatch none)
    (Subsingleton.elim specification model.1.input)
  rw [sameFailure]
  have conditional : ENNReal.ofReal ((99 : Real) / 100) ≤
      1 - NativeRSA2048.Calibration.twentyBatchFailure ^ 4 :=
    NativeRSA2048.Calibration.combinedSuccess_twentyByFour_ge_99.trans
      (tsub_le_tsub_left (le_add_of_nonneg_left zero_le) 1)
  exact conditional.trans
    (tsub_le_tsub_left (pow_le_pow_left' (rsaMeasured2048_batchFailure_twenty_le model) 4) 1)

private lemma rsaMeasured2048_keygen_twentyByFour_successFloor
    {environment : ShortDLP.CompiledMAU.Recycling.model.Environment}
    (populated : Nonempty (QuantumAlg.RSA.RSAKeyPairBits 1024))
    {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits 1024 →
      OracleInput ClassicalOracleModel.empty base Reference) :
    1 - (ENNReal.ofReal (QuantumAlg.RSA.GeneratorOrder.keyFailureBound 1024) +
      NativeRSA2048.Calibration.twentyBatchFailure ^ 4) ≤
      RSA.Measured.Program.KeyAverage.successMass (environment := environment)
        base noQuantum 1024 populated RSA.Configuration.rsa2048Batches inputs := by
  have effective : QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits ≤ 1024 := by
    norm_num [QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits]
  have actual :=
    RSA.Measured.Program.KeyAverage.rsaMeasuredKeyAverage_success_ge_rounds_of_batchBound
    (environment := environment) base noQuantum 1024 populated 4 inputs effective
    NativeRSA2048.Calibration.twentyBatchFailure (fun pair good => by
      let key : GoodKeyModel pair.modulus := ⟨1024, pair, rfl, effective, good⟩
      exact rsaMeasured2048_batchFailure_twenty_le (⟨key, rfl⟩ : NativeRSA2048.FixedKeyModel
    pair.modulus))
  exact actual

/-- The original ordered-key law has success at least 99 percent for the same actual execution. -/
lemma rsaMeasured2048_keygen_twentyByFour_success_ge_99
    {environment : ShortDLP.CompiledMAU.Recycling.model.Environment}
    (populated : Nonempty (QuantumAlg.RSA.RSAKeyPairBits 1024))
    {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits 1024 →
      OracleInput ClassicalOracleModel.empty base Reference) :
    ENNReal.ofReal ((99 : Real) / 100) ≤
      RSA.Measured.Program.KeyAverage.successMass (environment := environment)
        base noQuantum 1024 populated RSA.Configuration.rsa2048Batches inputs :=
  NativeRSA2048.Calibration.combinedSuccess_twentyByFour_ge_99.trans
    (rsaMeasured2048_keygen_twentyByFour_successFloor (environment := environment) base noQuantum
    populated inputs)

/-- Total failure on the original ordered-key law is strictly below one percent. -/
lemma rsaMeasured2048_keygen_twentyByFour_failure_lt_onePercent
    {environment : ShortDLP.CompiledMAU.Recycling.model.Environment}
    (populated : Nonempty (QuantumAlg.RSA.RSAKeyPairBits 1024))
    {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits 1024 →
      OracleInput ClassicalOracleModel.empty base Reference) :
    1 - RSA.Measured.Program.KeyAverage.successMass (environment := environment)
        base noQuantum 1024 populated RSA.Configuration.rsa2048Batches inputs <
      ENNReal.ofReal ((1 : Real) / 100) := by
  have actual := rsaMeasured2048_keygen_twentyByFour_successFloor (environment := environment)
    base noQuantum populated inputs
  have bounded :
      1 - RSA.Measured.Program.KeyAverage.successMass (environment := environment)
          base noQuantum 1024 populated RSA.Configuration.rsa2048Batches inputs ≤
        ENNReal.ofReal (QuantumAlg.RSA.GeneratorOrder.keyFailureBound 1024) +
          NativeRSA2048.Calibration.twentyBatchFailure ^ 4 := by
    apply tsub_le_iff_right.mpr
    exact tsub_le_iff_left.mp actual
  exact bounded.trans_lt NativeRSA2048.Calibration.keygenFailure_twentyByFour_lt_onePercent

end

end QuantumAlg.Factoring.RSA2048.Measured
