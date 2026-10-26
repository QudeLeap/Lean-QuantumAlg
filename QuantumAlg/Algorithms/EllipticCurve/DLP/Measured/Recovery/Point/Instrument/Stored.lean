/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Correctness
import all QuantumAlg.Core.Execution.Context.Embedding.Framing
import all QuantumAlg.Core.Execution.Store.MarginalSum
import all QuantumAlg.Core.Execution.Store.History
import all QuantumAlg.Core.Execution.Unitary.StoreFilter
import all QuantumAlg.Core.Base.Tensor.Reference

/-!
# Stored point instrument and reference factor

Native context embeddings retain the actual point execution and both measured reset
calls. Complete stored matrices and arbitrary reference correlations are retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point
namespace Instrument

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.Execution.ContextUnion
open QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

private instance selectorStoreSubsingleton (width : Nat) :
    Subsingleton (Store (selectorContext width)) :=
  ⟨fun first second => by
    apply congrArg Store.mk
    exact Subsingleton.elim (α := Unit × Unit) first.cells second.cells⟩

private def emptySelectorStore (width : Nat) : Store (selectorContext width) := ⟨((), ())⟩

/-- The real resident selector adds no classical outcome cell. -/
def storeCoordinates (width : Nat) :
    Store (context width) ≃ Store (InPlaceControlled.context width) where
  toFun stored := (ContextUnion.storeEquiv (selector_disjoint width) stored).1
  invFun stored := (ContextUnion.storeEquiv (selector_disjoint width)).symm
    (stored, emptySelectorStore width)
  left_inv stored := by
    apply (ContextUnion.storeEquiv (selector_disjoint width)).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext rfl (Subsingleton.elim _ _)
  right_inv stored :=
    congrArg Prod.fst ((ContextUnion.storeEquiv (selector_disjoint width)).apply_symm_apply
      (stored, emptySelectorStore width))

/-- Splitting the actual selector frame retains each entire stored matrix block. -/
lemma split_store_matrix (width : Nat) {Reference : Register} {History : Type}
    [Fintype History] (state : State (context width) Reference History)
    (stored : Store (context width)) :
    ((ContextUnion.splitState (InPlaceControlled.context width) (selectorContext width)
      (selector_disjoint width) state).filterClassical
        (fun entry => entry.1 = storeCoordinates width stored)).quantumMarginal.matrix =
      (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix.submatrix
        (ContextUnion.referenceBasis (InPlaceControlled.context width) (selectorContext width)
          (selector_disjoint width) Reference).symm
        (ContextUnion.referenceBasis (InPlaceControlled.context width) (selectorContext width)
          (selector_disjoint width) Reference).symm := by
  have regroup :
      (ContextUnion.splitState (InPlaceControlled.context width) (selectorContext width)
        (selector_disjoint width) state).mapClassical (fun entry => entry.1) =
      ((state.mapClassical (fun entry => entry.1)).mapClassical (storeCoordinates width)).reindex
        (ContextUnion.referenceBasis (InPlaceControlled.context width) (selectorContext width)
          (selector_disjoint width) Reference) := by
    rw [ContextUnion.splitState, ExecutionState.coordinate_reindex_mapClassical,
      ExecutionState.executionState_mapClassical_comp,
      ExecutionState.executionState_mapClassical_comp]
    rfl
  rw [← BasisSeeded.store_matrix, regroup]
  ext row column
  rw [ExecutionState.reindex_block_entry, ExecutionState.coordinate_mapClassical_block,
    Equiv.symm_apply_apply, BasisSeeded.store_matrix]
  rfl

/-- This is the existing measured operator pulled back through the real selector framing. -/
def arithmeticOperator (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register) (stored : Store (context modulus.size)) :
    HilbertOperator (Register.prod (context modulus.size).register Reference) :=
  (InPlaceControlled.actualOperator environment.quantum operation modulus prime
    (Register.prod (selectorContext modulus.size).register Reference)
    (storeCoordinates modulus.size stored)).submatrix
      (ContextUnion.referenceBasis (InPlaceControlled.context modulus.size)
        (selectorContext modulus.size) (selector_disjoint modulus.size) Reference)
      (ContextUnion.referenceBasis (InPlaceControlled.context modulus.size)
        (selectorContext modulus.size) (selector_disjoint modulus.size) Reference)

attribute [local irreducible] InPlaceControlled.body

/-- The actual framed arithmetic has this exact stored instrument on arbitrary input states. -/
lemma arithmetic_store_matrix (operation : InPlaceTarget.Operation)
  (modulus : Nat)
    (prime : Nat.Prime modulus) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context modulus.size))
    (allowAllocation : Bool := true) :
    (((arithmetic operation modulus prime allowAllocation).execute environment Reference
      state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      arithmeticOperator (environment := environment) operation modulus prime Reference stored *
        state.quantumMarginal.matrix *
        (arithmeticOperator (environment := environment) operation modulus prime Reference
          stored).conjTranspose := by
  let coordinates := ContextUnion.referenceBasis (InPlaceControlled.context modulus.size)
    (selectorContext modulus.size) (selector_disjoint modulus.size) Reference
  let localState := ContextUnion.splitServiceState (InPlaceControlled.context modulus.size)
    (selectorContext modulus.size) (selector_disjoint modulus.size) state
  have natural := Circuit.union_embed_execute (environment := environment) (allowAllocation :=
    allowAllocation)
    (InPlaceControlled.body operation modulus prime false) (selectorContext modulus.size)
    (selector_disjoint modulus.size) Reference state
  have block := congrArg
    (fun result => (result.filterClassical
      (fun entry => entry.1 = storeCoordinates modulus.size stored)).quantumMarginal.matrix) natural
  simp only [ContextUnion.splitServiceState] at block
  rw [InPlaceControlled.history_store_matrix, split_store_matrix] at block
  have erased := congrArg DensityOperator.matrix
    (State.mapHistory_store_marginal
      ((InPlaceControlled.body operation modulus prime false).execute environment (Register.prod
        (selectorContext modulus.size).register Reference) localState)
      (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))
      (storeCoordinates modulus.size stored))
  have actual := InPlaceControlled.body_matrix (environment := environment) operation modulus
    prime localState
    (storeCoordinates modulus.size stored) false
  have localMarginal : localState.quantumMarginal = state.quantumMarginal.reindex coordinates := by
    exact MeasuredPointAddition.splitService_marginal modulus.size state
  rw [localMarginal] at actual
  have joined := block.trans (erased.trans actual)
  exact InPlaceControlled.pullback_conjugation coordinates state.quantumMarginal.matrix
    (((arithmetic operation modulus prime allowAllocation).execute environment Reference
      state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix
    (InPlaceControlled.actualOperator environment.quantum operation modulus prime
      (Register.prod (selectorContext modulus.size).register Reference)
      (storeCoordinates modulus.size stored)) joined

/-- Summing the first call's actual overwritten stores reconstructs its quantum marginal. -/
lemma arithmetic_marginal_matrix (operation :
  InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (allowAllocation : Bool := true) :
    ((arithmetic operation modulus prime allowAllocation).execute environment Reference
      state).quantumMarginal.matrix =
      ∑ stored : Store (context modulus.size),
        arithmeticOperator (environment := environment) operation modulus prime Reference stored *
          state.quantumMarginal.matrix *
          (arithmeticOperator (environment := environment) operation modulus prime Reference
            stored).conjTranspose := by
  rw [← Execution.sum_store_matrices
    ((arithmetic operation modulus prime allowAllocation).execute environment Reference state)]
  apply Finset.sum_congr rfl
  intro stored _
  exact arithmetic_store_matrix (environment := environment) operation modulus prime state stored
    allowAllocation

/-- A real two-measurement branch keeps the final multiplication store and the summed old store. -/
def pointKraus {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register)
    (divisionStore finalStore : Store (context p.size)) :
    HilbertOperator (Register.prod (context p.size).register Reference) :=
  (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
    (afterMultiplication E Q) :
      HilbertOperator (Register.prod (context p.size).register Reference)) *
    arithmeticOperator (environment := environment) .multiplication p Fact.out Reference
      finalStore *
    (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
      (beforeMultiplication Q) :
      HilbertOperator (Register.prod (context p.size).register Reference)) *
    arithmeticOperator (environment := environment) .division p Fact.out Reference divisionStore *
    (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
      (beforeDivision Q) :
      HilbertOperator (Register.prod (context p.size).register Reference))

/-- The literal five-stage interpreter yields a sum over the first overwritten outcome only. -/
lemma body_store_matrix {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (finalStore : Store (context p.size))
    (allowAllocation : Bool := true) :
    (((MeasuredPointAddition.body E Q allowAllocation).execute environment Reference
      state).filterClassical
      (fun entry => entry.1 = finalStore)).quantumMarginal.matrix =
      ∑ divisionStore : Store (context p.size),
        pointKraus (environment := environment) E Q Reference divisionStore finalStore *
          state.quantumMarginal.matrix *
          (pointKraus (environment := environment) E Q Reference divisionStore
            finalStore).conjTranspose := by
  let before := nativeCode p.size (beforeDivision Q) allowAllocation
  let divided := arithmetic .division p Fact.out allowAllocation
  let middle := nativeCode p.size (beforeMultiplication Q) allowAllocation
  let multiplied := arithmetic .multiplication p Fact.out allowAllocation
  let after := nativeCode p.size (afterMultiplication E Q) allowAllocation
  let beforeState := before.execute environment Reference state
  let dividedState := divided.execute environment Reference beforeState
  let middleState := middle.execute environment Reference dividedState
  let multipliedState := multiplied.execute environment Reference middleState
  have first := Circuit.seq_store_marginal (environment := environment) before
    (.seq divided (.seq middle (.seq multiplied after))) state finalStore
  refine (congrArg DensityOperator.matrix first).trans ?_
  have second := Circuit.seq_store_marginal (environment := environment) divided (.seq middle
    (.seq multiplied after))
    beforeState finalStore
  refine (congrArg DensityOperator.matrix second).trans ?_
  have third := Circuit.seq_store_marginal (environment := environment) middle (.seq multiplied
    after)
    dividedState finalStore
  refine (congrArg DensityOperator.matrix third).trans ?_
  have fourth := Circuit.seq_store_marginal (environment := environment) multiplied after
    middleState finalStore
  refine (congrArg DensityOperator.matrix fourth).trans ?_
  have last := Circuit.unitary_store_filter (environment := environment) (allowAllocation :=
    allowAllocation)
    (operations := .empty) (services := .empty)
    (runtimeProgram p.size (afterMultiplication E Q)) multipliedState
    (fun stored => stored = finalStore)
  have terminalMatrix := (congrArg DensityOperator.matrix last).trans
    (DensityOperator.applyUnitary_matrix
      (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
        (afterMultiplication E Q))
      (multipliedState.filterClassical (fun entry => entry.1 = finalStore)).quantumMarginal)
  refine terminalMatrix.trans ?_
  have multiplicationMatrix := arithmetic_store_matrix (environment := environment)
    .multiplication p Fact.out
    middleState finalStore allowAllocation
  have middleMatrix := (congrArg DensityOperator.matrix
    (MeasuredPointAddition.nativeCode_density (environment := environment) p.size
      (beforeMultiplication Q)
      dividedState allowAllocation)).trans
    (DensityOperator.applyUnitary_matrix
      (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
        (beforeMultiplication Q))
      dividedState.quantumMarginal)
  have divisionMatrix := arithmetic_marginal_matrix (environment := environment) .division p
    Fact.out
    beforeState allowAllocation
  have beforeMatrix := (congrArg DensityOperator.matrix
    (MeasuredPointAddition.nativeCode_density (environment := environment) p.size (beforeDivision Q)
      state allowAllocation)).trans
    (DensityOperator.applyUnitary_matrix
      (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
        (beforeDivision Q))
      state.quantumMarginal)
  rw [multiplicationMatrix, middleMatrix, divisionMatrix, beforeMatrix]
  simp only [pointKraus, Finset.mul_sum, Finset.sum_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

end

end Instrument
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point
namespace Instrument

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
open scoped Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma projector_tensor_identity {Local Reference : Register} {Outcome : Type}
    [DecidableEq Outcome] (readout : Local.Index → Outcome) (outcome : Outcome) :
    ZMeasurement.projector
        (fun entry : (Register.prod Local Reference).Index => readout entry.1) outcome =
      ZMeasurement.projector readout outcome ⊗ₖ (1 : HilbertOperator Reference) := by
  ext row column
  let rowPair : Local.Index × Reference.Index := row
  let columnPair : Local.Index × Reference.Index := column
  change (if (rowPair.1, rowPair.2) = (columnPair.1, columnPair.2) then
      (if readout rowPair.1 = outcome then (1 : Complex) else 0) else 0) =
    (if rowPair.1 = columnPair.1 then
      (if readout rowPair.1 = outcome then (1 : Complex) else 0) else 0) *
      (if rowPair.2 = columnPair.2 then 1 else 0)
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The actual union framing changes only the local coordinates, beside the same reference. -/
private lemma framed_tensor_identity {kind : ProblemKind}
    (left right : RuntimeCtx kind) (separate : RuntimeCtx.StorageDisjoint left right)
    (operator : HilbertOperator left.register) (Reference : Register) :
    (operator ⊗ₖ (1 : HilbertOperator (Register.prod right.register Reference))).submatrix
        (ContextUnion.referenceBasis left right separate Reference)
        (ContextUnion.referenceBasis left right separate Reference) =
      ((operator ⊗ₖ (1 : HilbertOperator right.register)).submatrix
        (ContextUnion.unionBasisEquiv left right separate)
        (ContextUnion.unionBasisEquiv left right separate)) ⊗ₖ
          (1 : HilbertOperator Reference) := by
  ext row column
  let rowPair : (left.disjointUnion right separate).register.Index × Reference.Index := row
  let columnPair : (left.disjointUnion right separate).register.Index × Reference.Index := column
  let rowLocal := ContextUnion.unionBasisEquiv left right separate rowPair.1
  let columnLocal := ContextUnion.unionBasisEquiv left right separate columnPair.1
  change operator rowLocal.1 columnLocal.1 *
      (if (rowLocal.2, rowPair.2) = (columnLocal.2, columnPair.2) then (1 : Complex) else 0) =
    (operator rowLocal.1 columnLocal.1 *
      (if rowLocal.2 = columnLocal.2 then (1 : Complex) else 0)) *
      (if rowPair.2 = columnPair.2 then 1 else 0)
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The literal H/projector/stored-X reset has one reference-independent dirty-bank matrix. -/
private lemma reset_reference_factor (width : Nat)
    (stored : Store (NumeratorMeasurement.context width)) :
    ∃ localKernel : HilbertOperator (NumeratorMeasurement.context width).register,
      ∀ Reference : Register,
        NumeratorResetConjugation.operator environment.quantum width Reference stored =
          localKernel ⊗ₖ (1 : HilbertOperator Reference) := by
  let correction : HilbertOperator (NumeratorMeasurement.context width).register :=
    ((NumeratorRuntime.program width
      (NumeratorReset.member width (stored.read (NumeratorMeasurement.input width)))).matrix
        environment.quantum)
  let detector : HilbertOperator (NumeratorMeasurement.context width).register :=
    ZMeasurement.projector (NumeratorObservation.word width)
      (NumeratorReset.outcome (stored.read (NumeratorMeasurement.input width)))
  let hadamard : HilbertOperator (NumeratorMeasurement.context width).register :=
    ((NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).matrix
      environment.quantum)
  refine ⟨correction * detector * hadamard, ?_⟩
  intro Reference
  have tensor_mul
      (A B : HilbertOperator (NumeratorMeasurement.context width).register) :
      (A * B) ⊗ₖ (1 : HilbertOperator Reference) =
        (A ⊗ₖ (1 : HilbertOperator Reference)) *
          (B ⊗ₖ (1 : HilbertOperator Reference)) := by
    simpa only [Matrix.one_mul] using
      (Matrix.mul_kronecker_mul A B
        (1 : HilbertOperator Reference) (1 : HilbertOperator Reference))
  have detector_factor :=
    projector_tensor_identity
      (Local := (NumeratorMeasurement.context width).register)
      (Reference := Reference) (NumeratorObservation.word width)
      (NumeratorReset.outcome (stored.read (NumeratorMeasurement.input width)))
  simp only [NumeratorResetConjugation.operator, unitaryOperator_prodTensor_identity]
  erw [detector_factor]
  change (correction ⊗ₖ (1 : HilbertOperator Reference)) *
      (detector ⊗ₖ (1 : HilbertOperator Reference)) *
      (hadamard ⊗ₖ (1 : HilbertOperator Reference)) =
    (correction * detector * hadamard) ⊗ₖ (1 : HilbertOperator Reference)
  rw [tensor_mul (correction * detector) hadamard, tensor_mul correction detector]

/-- The supplied-control framing retains exactly that reference identity. -/
private lemma framedReset_reference_factor (width : Nat)
    (stored : Store (InPlaceControlled.context width)) :
    ∃ localKernel : HilbertOperator (InPlaceControlled.context width).register,
      ∀ Reference : Register,
        InPlaceControlled.framedResetOperator environment.quantum width Reference stored =
          localKernel ⊗ₖ (1 : HilbertOperator Reference) := by
  obtain ⟨reset, reset_factor⟩ :=
    reset_reference_factor (environment := environment) width (InPlaceControlled.storeCoordinates
      width stored)
  refine ⟨(reset ⊗ₖ
      (1 : HilbertOperator (InPlaceControlled.controlContext width).register)).submatrix
    (ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
      (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width))
    (ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
      (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width)), ?_⟩
  intro Reference
  unfold InPlaceControlled.framedResetOperator
  rw [reset_factor (Register.prod (InPlaceControlled.controlContext width).register Reference)]
  exact framed_tensor_identity (NumeratorMeasurement.context width)
    (InPlaceControlled.controlContext width)
    (InPlaceControlled.control_disjoint width) reset Reference

/-- The actual arithmetic prefix/reset/stored-suffix word acts trivially on every reference. -/
private lemma controlled_reference_factor (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (stored : Store (InPlaceControlled.context modulus.size)) :
    ∃ localKernel : HilbertOperator (InPlaceControlled.context modulus.size).register,
      ∀ Reference : Register,
        InPlaceControlled.actualOperator environment.quantum operation modulus prime Reference
          stored =
          localKernel ⊗ₖ (1 : HilbertOperator Reference) := by
  obtain ⟨reset, reset_factor⟩ := framedReset_reference_factor (environment := environment)
    modulus.size stored
  let before : HilbertOperator (InPlaceControlled.context modulus.size).register :=
    ((InPlaceControlled.runtimeProgram modulus.size
      (InPlaceControlled.beforeReset operation modulus prime)).matrix environment.quantum)
  let after : HilbertOperator (InPlaceControlled.context modulus.size).register :=
    ((InPlaceControlled.runtimeProgram modulus.size
      (InPlaceControlled.suffix operation modulus prime
        (stored.read (InPlaceControlled.resultInput modulus.size)))).matrix environment.quantum)
  refine ⟨after * reset * before, ?_⟩
  intro Reference
  unfold InPlaceControlled.actualOperator
  rw [reset_factor Reference]
  have tensor_mul
      (A B : HilbertOperator (InPlaceControlled.context modulus.size).register) :
      (A * B) ⊗ₖ (1 : HilbertOperator Reference) =
        (A ⊗ₖ (1 : HilbertOperator Reference)) *
          (B ⊗ₖ (1 : HilbertOperator Reference)) := by
    simpa only [Matrix.one_mul] using
      (Matrix.mul_kronecker_mul A B
        (1 : HilbertOperator Reference) (1 : HilbertOperator Reference))
  simp only [InPlaceControlled.nativeJoint, unitaryOperator_prodTensor_identity]
  change (after ⊗ₖ (1 : HilbertOperator Reference)) *
      (reset ⊗ₖ (1 : HilbertOperator Reference)) *
      (before ⊗ₖ (1 : HilbertOperator Reference)) =
    (after * reset * before) ⊗ₖ (1 : HilbertOperator Reference)
  rw [tensor_mul (after * reset) before, tensor_mul after reset]

/-- The second actual framing preserves the same reference factor through the resident N. -/
private lemma arithmetic_reference_factor (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (stored : Store (context modulus.size)) :
    ∃ localKernel : HilbertOperator (context modulus.size).register,
      ∀ Reference : Register,
        arithmeticOperator (environment := environment) operation modulus prime Reference stored =
          localKernel ⊗ₖ (1 : HilbertOperator Reference) := by
  obtain ⟨arithmetic, arithmetic_factor⟩ :=
    controlled_reference_factor (environment := environment) operation modulus prime
      (storeCoordinates modulus.size stored)
  refine ⟨(arithmetic ⊗ₖ (1 : HilbertOperator (selectorContext modulus.size).register)).submatrix
    (ContextUnion.unionBasisEquiv (InPlaceControlled.context modulus.size)
      (selectorContext modulus.size) (selector_disjoint modulus.size))
    (ContextUnion.unionBasisEquiv (InPlaceControlled.context modulus.size)
      (selectorContext modulus.size) (selector_disjoint modulus.size)), ?_⟩
  intro Reference
  unfold arithmeticOperator
  rw [arithmetic_factor (Register.prod (selectorContext modulus.size).register Reference)]
  exact framed_tensor_identity (InPlaceControlled.context modulus.size)
    (selectorContext modulus.size) (selector_disjoint modulus.size) arithmetic Reference

-- Native words are already certified. Their matrices stay opaque during reference algebra.
attribute [local irreducible] MeasuredPointAddition.runtimeProgram
  beforeDivision beforeMultiplication afterMultiplication

/-- The original five factors keep their order and both actual retained stores. -/
lemma pointKraus_reference_factor {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (divisionStore finalStore : Store (context p.size)) :
    ∃ localKernel : HilbertOperator (context p.size).register,
      ∀ Reference : Register,
        pointKraus (environment := environment) E Q Reference divisionStore finalStore =
          localKernel ⊗ₖ (1 : HilbertOperator Reference) := by
  obtain ⟨divided, divided_factor⟩ :=
    arithmetic_reference_factor (environment := environment) .division p Fact.out divisionStore
  obtain ⟨multiplied, multiplied_factor⟩ :=
    arithmetic_reference_factor (environment := environment) .multiplication p Fact.out finalStore
  let before : HilbertOperator (context p.size).register :=
    ((MeasuredPointAddition.runtimeProgram p.size (beforeDivision Q)).matrix environment.quantum)
  let middle : HilbertOperator (context p.size).register :=
    ((MeasuredPointAddition.runtimeProgram p.size (beforeMultiplication Q)).matrix
      environment.quantum)
  let after : HilbertOperator (context p.size).register :=
    ((MeasuredPointAddition.runtimeProgram p.size (afterMultiplication E Q)).matrix
      environment.quantum)
  refine ⟨after * multiplied * middle * divided * before, ?_⟩
  intro Reference
  unfold pointKraus
  rw [multiplied_factor Reference, divided_factor Reference]
  simp only [MeasuredPointAddition.nativeJoint, unitaryOperator_prodTensor_identity]
  change (after ⊗ₖ (1 : HilbertOperator Reference)) *
      (multiplied ⊗ₖ (1 : HilbertOperator Reference)) *
      (middle ⊗ₖ (1 : HilbertOperator Reference)) *
      (divided ⊗ₖ (1 : HilbertOperator Reference)) *
      (before ⊗ₖ (1 : HilbertOperator Reference)) =
    (after * multiplied * middle * divided * before) ⊗ₖ (1 : HilbertOperator Reference)
  simp only [HilbertOperator.kronecker_identity_mul]

end

end Instrument
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point
