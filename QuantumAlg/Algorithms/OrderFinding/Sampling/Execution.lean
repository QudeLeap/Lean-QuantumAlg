/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Oracle
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Storage
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Execution

/-!
# Empty-input execution of the common order-finding sampler

The empty-input endpoint specializes the single Framed sampler.
-/

namespace QuantumAlg.OrderFinding.Sampling

noncomputable section

open QuantumAlg.Execution

/-- The single actual sampler with the original empty input. -/
def code {N x t n : Nat} (A : ModExpOracleAccess N x t n) : Circuit pre (post t n) :=
  Framed.code pre pre_quantumWires A

/-- The same complete run reads its actual packed phase bits. -/
def run {N x t n : Nat} (A : ModExpOracleAccess N x t n) :
    AlgorithmRun pre (post t n) (.bits t) := Framed.run pre pre_quantumWires A

theorem run_result {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (record : (run A).Record) :
    (run A).result record = record.1.read (.storage (resultRef t n).toCStorageRef) := rfl

theorem run_output_listing {N x t n : Nat} (A : ModExpOracleAccess N x t n) :
    (run A).output.listing = (post t n).keys := rfl

end

end QuantumAlg.OrderFinding.Sampling
