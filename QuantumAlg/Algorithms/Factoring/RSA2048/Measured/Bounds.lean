/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA2048.Measured.Resources
import all QuantumAlg.Algorithms.Factoring.RSA2048.Measured.Space
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Endpoint

/-!
# Fixed native bounds on the actual complete measured RSA-2048 execution

Every original exact-width key supplies oddness and the arithmetic width
internally. The same actual path retains all measured arithmetic, feedback,
packing, reset/reload, pair recovery and selection. The closed numerals
bound paths; they do not assert equality on every adaptive native branch
[G25, main.tex:199-295,354-360; EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA2048.Measured

noncomputable section

attribute [local instance] RSA.Configuration.rsa2048

open Execution EkeraHastadStyle.Canonical

private lemma fixedWidth_large {N : Nat} (model : NativeRSA2048.FixedWidthModel N) :
    5 ≤ arithmeticBits N := by
  rw [NativeRSA2048.model_arithmeticBits_eq model]
  norm_num [NativeRSA2048.modulusBits, NativeRSA2048.primeBits]

private lemma fixedWidth_odd {N : Nat} (model : NativeRSA2048.FixedWidthModel N) : Odd N := by
  rw [model.modulus_eq]
  exact RSA.Measured.measuredRSA_orderedKey_odd model.pair

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}
  (model : NativeRSA2048.FixedWidthModel N) (input : Input N)
  (path : (RSA.Measured.Program.run base noQuantum N input
    RSA.Configuration.rsa2048Batches).code.Path)

include model

/-- All three native gate coordinates of the actual eighty-member execution obey their caps. -/
lemma rsaMeasured2048_run_gateCount_le (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := ShortDLP.CompiledMAU.Recycling.model) (.gate coordinate)
      ((RSA.Measured.Program.run base noQuantum N input
        RSA.Configuration.rsa2048Batches).code.resourcePool path) ≤ gateCountBound coordinate :=
  (RSA.Measured.Program.rsaMeasuredParent_run_gateCount_le base noQuantum input
    RSA.Configuration.rsa2048Batches (fixedWidth_large model) (fixedWidth_odd model)
    path coordinate).trans_eq (rsaMeasured2048_model_gateCountLimit_eq model coordinate)

/-- Actual arithmetic/control/full-bank measurements remain a separately bounded coordinate. -/
lemma rsaMeasured2048_run_measurementCount_le :
    ResourcePool.count (model := ShortDLP.CompiledMAU.Recycling.model) (.measurement (2 : ℕ+))
      ((RSA.Measured.Program.run base noQuantum N input
        RSA.Configuration.rsa2048Batches).code.resourcePool path) ≤ measurementBound :=
  (ResourcePool.le_iff_count.mp
    (RSA.Measured.Program.rsaMeasuredParent_run_pool_le base noQuantum N input
      (fixedWidth_large model) (fixedWidth_odd model) RSA.Configuration.rsa2048Batches path)
    (.measurement (2 : ℕ+))).trans_eq (rsaMeasured2048_model_measurementLimit_eq model)

/-- The actual scheduled quantum time has the independent weighted-native-work upper bound. -/
lemma rsaMeasured2048_run_quantumTime_le :
    (RSA.Measured.Program.run base noQuantum N input
      RSA.Configuration.rsa2048Batches).code.quantumTime path ≤ quantumTimeBound :=
  (RSA.Measured.Program.rsaMeasuredParent_run_quantumTime_le base noQuantum input
    (fixedWidth_large model) (fixedWidth_odd model) RSA.Configuration.rsa2048Batches path).trans_eq
      (rsaMeasured2048_model_quantumTimeLimit_eq model)

/-- Literal classical operations stay separate from every quantum coordinate of the same path. -/
lemma rsaMeasured2048_run_classicalOperation_le :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((RSA.Measured.Program.run base noQuantum N input
        RSA.Configuration.rsa2048Batches).code.resourcePool path) ≤ classicalOperationBound :=
  (RSA.Measured.Program.rsaMeasuredParent_run_classicalOperation_le base noQuantum input
    RSA.Configuration.rsa2048Batches (fixedWidth_large model) (fixedWidth_odd model) path).trans
      (rsaMeasured2048_model_classicalOperationLimit_le model)

end

end QuantumAlg.Factoring.RSA2048.Measured
