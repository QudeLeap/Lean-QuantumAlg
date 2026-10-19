/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Runtime
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Placement
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Packed
import all QuantumAlg.Core.Execution.Measured.FeedForward
import all QuantumAlg.Core.Execution.Measurement.Matrix
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Selected.Store
import all QuantumAlg.Core.Execution.Store.Blocks
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Actual old parameter selection, measured Store and charged packing in full matrix entries

The prefix below consists only of existing
RuntimeRound.selected and measuredPacking: the real placed compiled member,
real Z writes and real BitWord packing instruction. Its full matrix formula
retains arbitrary mixed/reference entries, all original Store/hidden/history
correlations and collisions of actual writes. It does not trace out the partner.
No cleanliness or instrument certificate is assumed. Clean-carrier substitution
uses the separately derived actual operator bridges, not a new source premise.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordMeasurement

noncomputable section

variable {environment : RuntimeRound.model.Environment}

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- Grouping by complete actual stores forgets no quantum-reference matrix entry. -/
private lemma weighted_store {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (weight : Store ctx → ℂ)
    (left right : (ctx.register.prod Reference).Index) :
    ExecutionState.weightedMatrixEntry state (fun entry => weight entry.1) left right =
      ∑ original : Store ctx, weight original *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          left right := by
  simp only [← BasisSeeded.store_matrix, ExecutionState.mapClassical_block_matrix,
    Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply, Finset.mul_sum,
    mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rfl

/-- Exactly the existing runtime round prefix before its separate whole-bank reset/reload. -/
def selectedMeasuredPacking {shape : CShape} (parameter : CInputRef ctx shape) (N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (RuntimeRound.resultBits m ell width))) :
    Circuit RuntimeRound.model ctx ctx :=
  .seq (RuntimeRound.selected m ell width sameWires parameter N generator target)
    (RuntimeRound.measuredPacking m ell width sameWires cells result)

/-- The actual paid measured prefix retains every local-partner/reference entry of each Store. -/
lemma selectedMeasuredPacking_store_entry {shape : CShape}
    (parameter : CInputRef ctx shape) (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (RuntimeRound.resultBits m ell width)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (RuntimeRound.model.HiddenState × History))
    (stored : Store ctx) (left right : ctx.register.Index)
    (leftRef rightRef : Reference.Index) :
    (((selectedMeasuredPacking m ell width sameWires parameter N generator target
      cells result).execute environment Reference state).filterClassical
        (fun entry => entry.1 = stored)).quantumMarginal.matrix
          (left, leftRef) (right, rightRef) =
      if Circuit.measurementLabelsAgree (RuntimeRound.readouts m ell width sameWires cells)
          left right then
        ∑ original : Store ctx,
          if RuntimeRound.packedBasisStore m ell width sameWires cells result original left =
              stored then
            let operator := UnitaryOperator.prodTensor
              ((RuntimePlacement.memberProgram m ell width sameWires N
                (generator (original.read parameter)) (target (original.read parameter))).matrix
                  environment.quantum)
              (1 : UnitaryOperator Reference)
            ((operator : HilbertOperator (ctx.register.prod Reference)) *
              (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (operator : HilbertOperator (ctx.register.prod Reference)).conjTranspose)
                (left, leftRef) (right, rightRef)
          else 0
      else 0 := by
  have composed := congrArg
    (fun density : DensityOperator (ctx.register.prod Reference) =>
      density.matrix (left, leftRef) (right, rightRef))
    (Circuit.seq_store_marginal (environment := environment)
      (RuntimeRound.selected m ell width sameWires parameter N generator target)
      (RuntimeRound.measuredPacking m ell width sameWires cells result) state stored)
  refine composed.trans ?_
  rw [ExecutionState.filterClassical_matrix_weighted,
    RuntimeRound.measuredPacking, Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.weightedMatrixEntry_mapClassical]
  rw [BitWord.bitWord_instruction_execute]
  simp only [ExecutionState.weightedMatrixEntry_mapClassical]
  rw [Circuit.measurementSequence_weightedMatrixEntry]
  change (if Circuit.measurementLabelsAgree (RuntimeRound.readouts m ell width sameWires cells)
      left right then
    ExecutionState.weightedMatrixEntry
      ((RuntimeRound.selected m ell width sameWires parameter N generator target).execute
        environment
        Reference state)
      (fun original => if RuntimeRound.packedBasisStore m ell width sameWires cells result
        original.1 left = stored then 1 else 0) (left, leftRef) (right, rightRef)
    else 0) = _
  let selectedState :=
    (RuntimeRound.selected m ell width sameWires parameter N generator target).execute environment
      Reference state
  let weight : Store ctx → ℂ := fun original =>
    if RuntimeRound.packedBasisStore m ell width sameWires cells result original left = stored
      then 1 else 0
  let unitary (original : Store ctx) : UnitaryOperator (ctx.register.prod Reference) :=
    UnitaryOperator.prodTensor
      ((RuntimePlacement.memberProgram m ell width sameWires N
        (generator (original.read parameter)) (target (original.read parameter))).matrix
          environment.quantum)
      (1 : UnitaryOperator Reference)
  change (if Circuit.measurementLabelsAgree (RuntimeRound.readouts m ell width sameWires cells)
      left right then
    ExecutionState.weightedMatrixEntry selectedState (fun entry => weight entry.1)
      (left, leftRef) (right, rightRef)
    else 0) =
    if Circuit.measurementLabelsAgree (RuntimeRound.readouts m ell width sameWires cells)
        left right then
      ∑ original : Store ctx,
        if RuntimeRound.packedBasisStore m ell width sameWires cells result original left = stored
          then
            ((unitary original : HilbertOperator (ctx.register.prod Reference)) *
              (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (unitary original : HilbertOperator (ctx.register.prod Reference)).conjTranspose)
                (left, leftRef) (right, rightRef)
          else 0
    else 0
  have grouped := weighted_store selectedState weight (left, leftRef) (right, rightRef)
  refine (congrArg (fun value : ℂ =>
    if Circuit.measurementLabelsAgree (RuntimeRound.readouts m ell width sameWires cells)
      left right then value else 0) grouped).trans ?_
  refine congrArg (fun value : ℂ =>
    if Circuit.measurementLabelsAgree (RuntimeRound.readouts m ell width sameWires cells)
      left right then value else 0) ?_
  refine Finset.sum_congr rfl ?_
  intro original _
  have branchMatrix :
      (selectedState.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix =
        (unitary original : HilbertOperator (ctx.register.prod Reference)) *
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
          (unitary original : HilbertOperator (ctx.register.prod Reference)).conjTranspose :=
    (Circuit.selectedUnitary_store_matrix (environment := environment) (allowAllocation := true)
      (operations := BitWord.model) (classicalOracles := .empty) parameter
      (fun value => RuntimePlacement.memberProgram m ell width sameWires N
        (generator value) (target value)) state original).trans
      (DensityOperator.applyUnitary_matrix (unitary original)
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal)
  have entry := congrArg
    (fun matrix : HilbertOperator (ctx.register.prod Reference) =>
      matrix (left, leftRef) (right, rightRef)) branchMatrix
  rw [entry]
  simp only [weight, ite_mul, one_mul, zero_mul]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordMeasurement
