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
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
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

/-- Default native gates with the source route's explicitly granted ordinary inverse access. -/
abbrev model {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) : ExecutionModel :=
  .quantum AlgorithmGate.model (Native.oracles M.preparation M.good)

/-- The same native word acts on the runtime register's identical ordered physical wires. -/
def nativeProgram {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    UnitaryCircuit AlgorithmGate.model (Native.oracles M.preparation M.good)
      (post n k).quantumLayout :=
  Execution.unitaryOfEqualWires
    (QuantumSignature.qubits (ZeroReflection.Workspace.totalQubits n k)).canonicalPlacement.layout
    (post n k).quantumLayout (post_canonical_wires n k) (Native.program M.preparation M.good k)

/-- Charge one zero preparation for every newly owned source and helper qubit. -/
def preparationCode {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    Circuit (model M) pre (post n k) :=
  .prepareZero pre ⟨0⟩ (runtimeLayout n k) preparationFresh (preparationDisjoint n k)

/-- The sole execution contains zero preparation followed by the actual source/gate sequence. -/
def code {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    Circuit (model M) pre (post n k) :=
  .seq (preparationCode M k) (.unitary (nativeProgram M k))

/-- Every final live system appears in the explicit complete manifest. -/
def run {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    AlgorithmRun (model M) pre (post n k) .unit where
  code := code M k
  output := Output.all (post n k) .unit

theorem run_output_listing {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    (run M k).output.listing = (post n k).keys := rfl

end

end QuantumAlg.AmplitudeAmplification
