/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Prepared.Probability
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Weights.Probability
import all QuantumAlg.Core.Execution.Basis.Reference
import all QuantumAlg.Core.Execution.Basis.Seeded

/-!
# Complete reusable-bank state of the actual prepared Shor batch

Every observed tuple-vector block contains the original seed on the one real
bank, its original source probability and the complete incoming reference
density. Preparation and every reset belong to the same actual code. The
joint entry formula imposes no seed or independence condition on the input.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativePreparedBatch

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = []) (N count : Nat)

/-- The independent original source seed on the actual single bank's final coordinates. -/
def restoredSeed : (context ctx noQuantum N count).register.Index :=
  (NativePlacement.basisEquiv N (quantumWires ctx noQuantum N count)).symm
    (NativeQuantum.seedLabel N)

/-- The original source's finite repeated distribution expressed in the stored tuple convention. -/
def sourceDistribution (source : Input N) :
    PMF (CShape.fixedVector count (NativeIteration.resultShape N)).Value :=
  (PMF.independentReplicateVector (sourceOutcomePMF source) count).map
    (fun outcomes => CShape.Value.fixedVector
      (fun index => NativeBatch.sourceValue source (outcomes.get index)))

/-- Every actual output block retains the exact seed jointly with the entire incoming reference. -/
theorem output_joint_entry (source : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (selected : (CShape.fixedVector count (NativeIteration.resultShape N)).Value)
    (left right : (context ctx noQuantum N count).register.Index)
    (leftRef rightRef : Reference.Index) :
    ((((code ctx noQuantum N count).execute Reference state).mapClassical
      (fun entry => (run ctx noQuantum N count).output.eval entry.1)).block selected).matrix
        (left, leftRef) (right, rightRef) =
      if left = restoredSeed ctx noQuantum N count ∧ right = restoredSeed ctx noQuantum N count then
        ((sourceDistribution N count source selected).toReal : ℂ) *
          state.referenceMarginal.matrix leftRef rightRef
      else 0 := by
  have observed := BasisSeeded.readout_entry (restoredSeed ctx noQuantum N count)
    ((code ctx noQuantum N count).execute Reference state)
    (code_seeded ctx noQuantum N count state)
    (fun store => (run ctx noQuantum N count).output.eval store) selected
    left right leftRef rightRef
  have actual := code_referenceFiberSum_result ctx noQuantum source count state
    (fun value => if value = selected then 1 else 0) leftRef rightRef
  have probability := SourceWeights.batch_indicator source count
    (fun outcomes => CShape.Value.fixedVector
      (fun index => NativeBatch.sourceValue source (outcomes index))) selected
  have scalar := actual.trans
    ((congrArg (fun coefficient : ℂ => ExecutionState.referenceFiberSum state
      (fun _ _ => coefficient) leftRef rightRef) probability).trans
      (ExecutionState.referenceFiberSum_constant_eq state
        ((sourceDistribution N count source selected).toReal : ℂ) leftRef rightRef))
  exact observed.trans (congrArg (fun coefficient : ℂ =>
    if left = restoredSeed ctx noQuantum N count ∧ right = restoredSeed ctx noQuantum N count
      then coefficient else 0) scalar)

/-- The independent seed-reference promise holds even for an impossible observed output. -/
theorem output_statePromise (source : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (normalized : state.IsNormalized)
    (selected : (CShape.fixedVector count (NativeIteration.resultShape N)).Value) :
    (StatePromise.mixed
      (BasisReference.target (restoredSeed ctx noQuantum N count) state.referenceMarginal)
      (BasisReference.target_normalized (restoredSeed ctx noQuantum N count) state.referenceMarginal
        ((ExecutionState.referenceMarginal_mass state).trans normalized))).Holds
      ((((code ctx noQuantum N count).execute Reference state).mapClassical
        (fun entry => (run ctx noQuantum N count).output.eval entry.1)).block selected) :=
  BasisReference.promise_of_entries (restoredSeed ctx noQuantum N count) state.referenceMarginal
    ((ExecutionState.referenceMarginal_mass state).trans normalized) _
    (sourceDistribution N count source selected).toReal
    (output_joint_entry ctx noQuantum N count source state selected)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativePreparedBatch
