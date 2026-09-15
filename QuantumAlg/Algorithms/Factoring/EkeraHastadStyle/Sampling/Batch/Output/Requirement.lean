/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Run.State
import all QuantumAlg.Core.Execution.SelectionAll.Reference
import all QuantumAlg.Core.Execution.State.Requirement

/-!
# Independent complete bank state required after the actual batch

The requirement observes every final quantum wire and the actual stored
source, parameter and sixteen outcomes. For each result it promises the
source-defined reloaded basis seed tensor the entire incoming reference
density. Its target uses no execution or resource projection. Impossible
results retain zero mass, without conditional normalization by division.

The separate complete borrowed-storage obligation preserves all original
classical-reference correlations as well as this full quantum-state promise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The specification reads the actual retained source, parameter and chronological outcomes. -/
def resultRead : OutputRead (context base noQuantum N) (resultShape N) :=
  .read (.product (finalSample base noQuantum N)
    (.product (finalParameter base noQuantum N) (finalResults base noQuantum N)))

private def fullTarget (Reference : Register) (input : Execution.Input base Reference) :
    DensityOperator (Register.prod
      ((context base noQuantum N).quantumLayout.selectedRegister Finset.univ) Reference) :=
  DensityOperator.observeSelectionWithReference (context base noQuantum N).quantumLayout
    Finset.univ Reference
    (BasisReference.target (restoredSeed base noQuantum N) input.state.referenceMarginal)

private theorem fullTarget_normalized (Reference : Register)
    (input : Execution.Input base Reference) :
    (fullTarget base noQuantum N Reference input).IsNormalized :=
  (DensityOperator.observeSelectionWithReference_mass
    (context base noQuantum N).quantumLayout Finset.univ Reference _).trans
      ((BasisReference.target_mass (restoredSeed base noQuantum N)
        input.state.referenceMarginal).trans
          ((ExecutionState.referenceMarginal_mass input.state).trans input.normalized))

/-- Every actual output fiber specifies the complete still-live bank jointly with its reference. -/
def requirement : StateRequirement base (context base noQuantum N) :=
  .jointReference Finset.univ (resultRead base noQuantum N) fun Reference input _ =>
    .mixed (fullTarget base noQuantum N Reference input)
      (fullTarget_normalized base noQuantum N Reference input)

/-- The real sixteen-round run satisfies the independent complete state requirement. -/
theorem nativeBatch_requirement_holds (specification : Input N)
    {Reference : Register} (input : Execution.Input base Reference) :
    (requirement base noQuantum N).Holds input
      ((run base noQuantum N).finalState Reference input.state) := by
  intro selected
  let actual :=
    (((run base noQuantum N).finalState Reference input.state).mapClassical
      (run base noQuantum N).output.eval).block selected
  have referenceNormalized : input.state.referenceMarginal.IsNormalized :=
    (ExecutionState.referenceMarginal_mass input.state).trans input.normalized
  have joint := BasisReference.promise_of_entries (restoredSeed base noQuantum N)
    input.state.referenceMarginal referenceNormalized actual
    (sourceDistribution specification selected).toReal
    (fun left right leftRef rightRef =>
      nativeBatch_run_output_joint_entry base noQuantum specification input selected
        left right leftRef rightRef)
  exact StatePromise.mixed_fullSelection (context base noQuantum N).quantumLayout Reference
    (BasisReference.target (restoredSeed base noQuantum N) input.state.referenceMarginal)
    (BasisReference.target_normalized (restoredSeed base noQuantum N)
      input.state.referenceMarginal referenceNormalized) actual joint

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
