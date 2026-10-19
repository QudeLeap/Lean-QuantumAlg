/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Context
import all QuantumAlg.Core.Execution.Basis.Reference
import all QuantumAlg.Core.Execution.State.Requirement

/-!
# Independent full-state specification for every finite EH batch count

Zero batches preserve the original joint quantum-reference state at the real
optional result read. Positive batches require the zero bank jointly with the
entire original reference. Every requirement selects all actual wires and
conditions on the actual optional result, including impossible output blocks.
These targets and requirements are independent of an execution proof.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] Retry.context

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The independent positive-count target is the zero bank and the entire original reference. -/
def stateTarget {Reference : Register} (original : Execution.Input base Reference) :
    DensityOperator (Register.prod (Retry.context base noQuantum N).register Reference) :=
  BasisReference.target (R := (Retry.context base noQuantum N).register)
    (Retry.context base noQuantum N).quantumLayout.zeroLabel
    original.state.referenceMarginal

/-- The original normalized reference gives a normalized full positive-count target. -/
lemma stateTarget_normalized {Reference : Register}
    (original : Execution.Input base Reference) :
    (stateTarget base noQuantum N original).IsNormalized :=
  BasisReference.target_normalized (R := (Retry.context base noQuantum N).register)
    (Retry.context base noQuantum N).quantumLayout.zeroLabel
    original.state.referenceMarginal
    ((ExecutionState.referenceMarginal_mass original.state).trans original.normalized)

private def zeroStateRequirement : StateRequirement base (Finite.zeroContext base N) :=
  .jointReference Finset.univ (.read (.storage (Finite.zeroRef base N).toCStorageRef))
    (fun Reference original _ => .mixed
      (DensityOperator.observeSelectionWithReference
        (Finite.zeroContext base N).quantumLayout Finset.univ Reference
        original.state.quantumMarginal)
      ((DensityOperator.observeSelectionWithReference_mass
        (Finite.zeroContext base N).quantumLayout Finset.univ Reference
        original.state.quantumMarginal).trans
          ((ExecutionState.quantumMarginal_mass original.state).trans original.normalized)))

private def positiveStateRequirement : StateRequirement base (Retry.context base noQuantum N) :=
  .jointReference Finset.univ
    (.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef))
    (fun Reference original _ => .mixed
      (DensityOperator.observeSelectionWithReference
        (Retry.context base noQuantum N).quantumLayout Finset.univ Reference
        (stateTarget base noQuantum N original))
      ((DensityOperator.observeSelectionWithReference_mass
        (Retry.context base noQuantum N).quantumLayout Finset.univ Reference
        (stateTarget base noQuantum N original)).trans
          (stateTarget_normalized base noQuantum N original)))

/-- Every finite count has an independent promise on all wires jointly with the full reference. -/
def stateRequirement : (count : Nat) →
    StateRequirement base (Finite.context base noQuantum N count)
  | 0 => zeroStateRequirement base N
  | _ + 1 => positiveStateRequirement base noQuantum N

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
