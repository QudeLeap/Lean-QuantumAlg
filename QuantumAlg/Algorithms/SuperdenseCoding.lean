/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.SuperdenseCoding.Results
public import QuantumAlg.Algorithms.SuperdenseCoding.Resources
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.SuperdenseCoding.Results
import all QuantumAlg.Algorithms.SuperdenseCoding.Specification
import all QuantumAlg.Algorithms.SuperdenseCoding.Construction
import all QuantumAlg.Algorithms.SuperdenseCoding.Resources

/-!
# Actual superdense-coding execution

The complete execution reads the original message storage, applies the
source encoding and decoding, and writes each real Z outcome to its own
result cell. The mathematical support module separately retains the source
communication profile of n shared Bell pairs and n transmitted qubits.
-/

namespace QuantumAlg.SuperdenseCoding
noncomputable section

open _root_.QuantumAlg.SuperdenseCoding.Execution

/-- **Input.** n supplied Bell pairs and the original 2n-bit message in borrowed
classical storage. Only local density and actual stored values restrict admission;
all external-reference extensions are included. The 2n owned result cells may
initially contain arbitrary values.

**Output.** The actual measured bit pairs equal the input message, while the
entire original quantum frame has its source-defined decoded state jointly
with the untouched reference. Every borrowed classical value is restored.

**Resource budget.** At most 3n native one-qubit gates, n CNOTs and 2n Z
measurements; exactly 4n resident classical bits and 2n supplied qubits, of
which 2n classical result bits are auxiliary. Quantum computation time is
at most four for a nonempty parallel bank and zero for the empty bank.

**Success.** Probability one for reading the complete message from the actual
measurement cells.

**Source.** Bennett-Wiesner superdense coding [dW19, qcnotes.tex:879-890]. -/
@[expose] public def problem (count : Nat) :
    Problem model (context count) (context count) (messageShape count) where
  Witness := SuperdenseMessage count
  valid := fun _ bits => admissible count bits
  initialization := fun _ _ _ => True
  accepts := fun _ bits _ output => output = messageValue bits
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ bits => [stateRequirement count bits]
  resources := {
    events := eventBudget count
    resident := residentBudget count
    auxiliary := auxiliaryBudget count }
  quantumTimeLimit := timeBudget count

/-- One complete actual circuit solves the independent deterministic decoding problem. -/
public theorem main (count : Nat) :
    ∃ candidate : Algorithm model (context count) (context count) (messageShape count) false,
      candidate.Solves (problem count) := by
  refine ⟨algorithm count, ?_⟩
  constructor
  · intro environment bits Reference input valid _initialization
    exact superdense_success environment count bits input valid
  · intro environment bits Reference input valid _initialization requirement present
    have same : requirement = stateRequirement count bits := List.mem_singleton.mp present
    subst requirement
    exact superdense_states environment count bits input valid
  · intro environment bits Reference input _valid _initialization
    exact superdense_borrowed environment count input
  · intro _environment _bits _Reference _input _valid _initialization path _supported
    exact superdense_code_events count path
  · intro _environment _bits _Reference _input _valid _initialization path _supported
    exact le_of_eq (superdense_code_space count path).1
  · intro _environment _bits _Reference _input _valid _initialization path _supported
    exact le_of_eq (superdense_code_space count path).2
  · intro _environment _bits _Reference _input _valid _initialization path _supported
    exact superdense_code_time count path

end
end QuantumAlg.SuperdenseCoding
