/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Parameters
import all QuantumAlg.Core.Measure

/-!
# Original sampled base and terminal word for intrinsic order recovery

The original deterministic source interpretation is independent of the
quantum circuit implementation that produced the stored measurement.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery

noncomputable section

/-- The concrete order-recovery semantic input determined by one retained
sampler word and one terminal measurement.  Its base is the unit physically
prepared by the sampler, including the rejection path where the prepared unit
is the canonical fallback. -/
def sampledSemanticInput {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (measurement : TerminalZMeasure.Outcome (phaseBits N)) :
    ClassicalAlgorithms.OrderRecovery.Input
      (recoverySpec input) := by
  let : NeZero N := input.neZero
  let prepared := RSA.prepareResidueFromBits N (modulusBits N)
    residueProposalCount sample
  exact
    { base := ⟨(prepared.unit : ZMod N).val,
        lt_of_lt_of_le (ZMod.val_lt (prepared.unit : ZMod N)) input.register_fits⟩
      baseInDomain := ZMod.val_lt (prepared.unit : ZMod N)
      baseCoprime := ZMod.val_coe_unit_coprime prepared.unit
      terminalBits := measurement }

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery
