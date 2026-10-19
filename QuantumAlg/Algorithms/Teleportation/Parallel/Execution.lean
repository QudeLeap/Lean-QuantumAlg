/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Parallel.Readout
import all QuantumAlg.Algorithms.Teleportation.Parallel.Readout
import all QuantumAlg.Algorithms.Teleportation.Parallel.Construction
import all QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
import all QuantumAlg.Core.Execution.Measured.FeedForward
import all QuantumAlg.Core.Execution.Store.Blocks

/-!
# Full store and reference entries of the actual teleportation execution

This equation observes the single native interpreter. Its initial native
word, actual projective writes, complete final store and selected correction
all come from that same circuit [dW19, qcnotes.tex:790,802,804]. The reference
indices remain arbitrary, and no diagonalization of the unknown state is
performed. The stored selector is subsequently identified with the actual
measurement path by the readout lemmas.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Every final store retains the full quantum-reference matrix of its actual measured branch. -/
lemma code_store_entry
    (environment : model.Environment) (count : Nat) {Reference : Register} {History : Type}
    [Fintype History] (state : State (context count) Reference (model.HiddenState × History))
    (stored : Store (context count)) (left right : (context count).register.Index)
    (leftRef rightRef : Reference.Index) :
    (ExecutionState.filterClassical (((code count).execute environment) Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      let alice : State (context count) Reference (model.HiddenState × (History × Unit)) :=
        ((Circuit.unitary (allowAllocation := false) (operations := .empty)
          (classicalOracles := .empty) (onContext count (aliceWord count))).execute environment)
            Reference state
      ∑ column : (context count).register.Index,
        (∑ row : (context count).register.Index,
          ((selectedCorrection count (stored.read (resultInput count))).matrix
            environment.quantum) left row *
            (if Circuit.measurementLabelsAgree (readouts count) row column then
              ExecutionState.weightedMatrixEntry alice (fun original =>
                if writtenStore count original.1 row = stored then 1 else 0)
                  (row, leftRef) (column, rightRef)
            else 0)) *
          star (((selectedCorrection count (stored.read (resultInput count))).matrix
            environment.quantum) right column)
    := by
  let first : Circuit model (context count) (context count) false :=
    .unitary (onContext count (aliceWord count))
  let second : Circuit model (context count) (context count) false :=
    .seq (Circuit.measurementSequence (readouts count))
      (.branch (resultInput count) (fun value => .unitary (selectedCorrection count value)))
  have actual := congrArg
    (fun density : DensityOperator ((context count).register.prod Reference) =>
      density.matrix (left, leftRef) (right, rightRef))
    (Circuit.seq_store_marginal first second environment state stored)
  exact actual.trans (Circuit.measuredSelectedUnitary_store_entry
    (allowAllocation := false) (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := .empty) (classicalOracles := .empty)
    (readouts count) (resultInput count) (selectedCorrection count) environment
    ((first.execute environment) Reference state) stored left right leftRef rightRef)

end

end QuantumAlg.QuantumTeleportation.Parallel
