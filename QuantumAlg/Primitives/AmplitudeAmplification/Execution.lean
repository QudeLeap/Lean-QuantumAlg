/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.AmplitudeAmplification.Model
import all QuantumAlg.Primitives.AmplitudeAmplification.Program
import all QuantumAlg.Primitives.AmplitudeAmplification.Context
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# One complete native amplitude-amplification execution

One basis preparation creates the complete owned register. The actual source
queries and elementary known reflections then act on that same register.
The explicit Output keeps every source and helper system and returns unit.
-/

namespace QuantumAlg.AmplitudeAmplification

noncomputable section

/-- The source program in the coordinates of the actual physical register. -/
def nativeProgram {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    UnitaryCircuit (post n k).register :=
  UnitaryCircuit.reindex (preparedBasisEquiv n k).symm
    (Native.program M.preparation M.good k)

theorem nativeProgram_placement {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) : (nativeProgram M k).physical_idx = (post n k).physicalIdx := by
  change (Native.program M.preparation M.good k).physical_idx = _
  rw [Native.program_physical_idx, post_physicalIdx]

def preparationCode (n k : Nat) : Circuit pre (post n k) :=
  .prepare pre ⟨0⟩ (runtimeLayout n k) preparationFresh
    (preparationDisjoint n k) (inputPreparation n k)

/-- The sole executed circuit, including the charged initial basis preparation. -/
def code {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    Circuit pre (post n k) :=
  .seq (preparationCode n k) (.unitary (nativeProgram M k) (nativeProgram_placement M k))

/-- Every final live system appears in the explicit complete manifest. -/
def run {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    AlgorithmRun pre (post n k) .unit where
  code := code M k
  output := Output.all (post n k) .unit

theorem run_output_listing {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    (run M k).output.listing = (post n k).keys := rfl

end

end QuantumAlg.AmplitudeAmplification
