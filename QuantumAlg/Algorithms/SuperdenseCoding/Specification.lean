/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.SuperdenseCoding.Readout
public import QuantumAlg.Algorithms.SuperdenseCoding.Resources
public import QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Algorithms.SuperdenseCoding.Readout
import all QuantumAlg.Algorithms.SuperdenseCoding.Matrix
import all QuantumAlg.Core.Algorithm.Unitary.Requirement

/-!
# Independent superdense-coding input and complete-state obligations

The caller supplies n shared Bell pairs and the real 2n-bit classical
message. Admissibility inspects only their local density and stored values;
all external reference extensions of that input remain admitted. The final
quantum-reference target is the source's exact encoding-and-decoding operator
on the original input. Actual Z measurements implement its deterministic
basis readout [dW19, qcnotes.tex:879-890].
-/

namespace QuantumAlg.SuperdenseCoding.Execution
noncomputable section

open QuantumAlg.Execution

/-- Local Bell initialization and the actual, immutable classical source input. -/
public def admissible (count : Nat) (bits : SuperdenseMessage count)
    (localState : ExecutionState (Store (context count)) (context count).register) : Prop :=
  localState.quantumMarginal = DensityOperator.ofPure (initialState count) ∧
    ∀ stored, (localState.block stored).mass ≠ 0 →
      stored.read (messageInput count) = messageValue bits

/-- The complete source operator, including arbitrary-reference coherences on all live systems. -/
public def stateRequirement (count : Nat) (bits : SuperdenseMessage count) :
    StateRequirement (context count) (context count) :=
  .unitary (physicalOperator count bits)

end
end QuantumAlg.SuperdenseCoding.Execution
