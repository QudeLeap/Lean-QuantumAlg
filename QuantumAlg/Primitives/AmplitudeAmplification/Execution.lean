/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.AmplitudeAmplification.Model
public import QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Primitives.AmplitudeAmplification.Model
public import QuantumAlg.Primitives.AmplitudeAmplification.Program
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
public abbrev model (n : Nat) : ExecutionModel :=
  .quantum AlgorithmGate.model (Native.oracles n)

/-- The source witness supplies only the runtime oracle interpretation. -/
@[expose] public def environment {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) :
    (model n).Environment :=
  ⟨Native.interpretation M.preparation M.good, ()⟩

/-- With no classical service, the source query interpretation fixes the whole environment. -/
lemma environment_eq_of_quantum {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (actual : (model n).Environment)
    (same : actual.quantum = Native.interpretation M.preparation M.good) :
    actual = environment M := by
  cases actual with
  | mk quantum classical =>
      cases same
      cases classical
      rfl

/-- The same native word acts on the runtime register's identical ordered physical wires. -/
def nativeProgram (n : Nat) (k : Nat) :
    UnitaryCircuit AlgorithmGate.model (Native.oracles n)
      (post n k).quantumLayout :=
  Execution.unitaryOfEqualWires
    (QuantumSignature.qubits (ZeroReflection.Workspace.totalQubits n k)).canonicalPlacement.layout
    (post n k).quantumLayout (post_canonical_wires n k) (Native.program n k)

/-- Charge one zero preparation for every newly owned source and helper qubit. -/
def preparationCode (n : Nat) (k : Nat) :
    Circuit (model n) pre (post n k) :=
  .prepareZero pre ⟨0⟩ (runtimeLayout n k) preparationFresh (preparationDisjoint n k)

/-- The sole execution contains zero preparation followed by the actual source/gate sequence. -/
def code (n : Nat) (k : Nat) :
    Circuit (model n) pre (post n k) :=
  .seq (preparationCode n k) (.unitary (nativeProgram n k))

/-- Every final live system appears in the explicit complete manifest. -/
def run (n : Nat) (k : Nat) :
    AlgorithmRun (model n) pre (post n k) .unit where
  code := code n k
  output := Output.all (post n k) .unit

lemma run_output_listing (n : Nat) (k : Nat) :
    (run n k).output.listing = (post n k).keys := rfl

end

end QuantumAlg.AmplitudeAmplification
