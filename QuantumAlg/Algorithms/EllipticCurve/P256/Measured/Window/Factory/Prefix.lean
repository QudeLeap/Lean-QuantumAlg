/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Run
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Initialization
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Borrowed
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Order
import all QuantumAlg.Core.Execution.Circuit.Support.Sequence
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Support.Sequence
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Specification

/-! # Actual paid-prefix support for the unchanged finalized sampler -/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

open QuantumAlg.Execution QuantumAlg.Execution.ClassicalWorkspace
open QuantumAlg.ClassicalRoutines.EllipticCurve
open QuantumAlg.ClassicalAlgorithms.EllipticCurve
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open WindowTables.Outer.Preparation

noncomputable section
local instance {α : Type} : DecidableEq α := Classical.decEq α
variable {services : ClassicalOracleModel}

attribute [local irreducible] WindowTables.Outer.Frame.ofRetainedCells RetainedCells.references
attribute [local irreducible] Signed.prepare prepareWithTables originalInputAfterTables Store.read
attribute [local irreducible] Circuit.execute Circuit.pathFintype
attribute [local irreducible] originalStoreAfterTables PointRepresents

private lemma allocated_input_support (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (I : DomainParameters.PublicKeyInstance)
    (basePoint targetPoint : CInputRef base (PointShape 256))
    (readsBorrowed : ∀ first second : Store base,
      first.readBorrowedClassical = second.readBorrowedClassical →
      first.read basePoint = second.read basePoint ∧
        first.read targetPoint = second.read targetPoint)
    (environment : (ExecutionModel.quantum AlgorithmGate.model OracleModel.empty
      BitWord.model services).Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State base Reference ((ExecutionModel.quantum AlgorithmGate.model
      OracleModel.empty BitWord.model services).HiddenState × History))
    (points : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents (actualCurveSpec I) (entry.1.read basePoint)
          (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib ∧
        PointRepresents (actualCurveSpec I) (entry.1.read targetPoint) I.publicKey.toMathlib)
    (initial : Store (tableContext base noQuantum) ×
      ((ExecutionModel.quantum AlgorithmGate.model OracleModel.empty BitWord.model
        services).HiddenState ×
        (History × (prepareWithTables (services := services) base noQuantum).Path)))
    (positive : 0 < (((prepareWithTables (services := services) base noQuantum).execute
      environment Reference state).block initial).mass) :
    PointRepresents (actualCurveSpec I)
        (initial.1.read (originalInputAfterTables base noQuantum basePoint))
        (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib ∧
      PointRepresents (actualCurveSpec I)
        (initial.1.read (originalInputAfterTables base noQuantum targetPoint))
        I.publicKey.toMathlib ∧
      (initial.1.read (.storage (tableFrame base noQuantum).zero.toCStorageRef)).toNat = 0 ∧
      (initial.1.read (.storage (tableFrame base noQuantum).one.toCStorageRef)).toNat = 0 := by
  have represented := prepareWithTables_read_pair_on_support base noQuantum
    basePoint targetPoint readsBorrowed
    (fun firstValue secondValue =>
      PointRepresents (actualCurveSpec I) firstValue
          (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib ∧
        PointRepresents (actualCurveSpec I) secondValue I.publicKey.toMathlib)
    environment Reference state points initial positive
  have zeroOne := prepareWithTables_zero_one_on_support base noQuantum
    environment Reference state initial positive
  exact ⟨represented.1, represented.2, zeroOne.1, zeroOne.2⟩

/-- The same actual prefix creates all constants and rows and retains the two original points. -/
lemma paidPrefix_post_on_support (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (I : DomainParameters.PublicKeyInstance)
    (basePoint targetPoint : CInputRef base (PointShape 256))
    (readsBorrowed : ∀ first second : Store base,
      first.readBorrowedClassical = second.readBorrowedClassical →
      first.read basePoint = second.read basePoint ∧
        first.read targetPoint = second.read targetPoint)
    (environment : (ExecutionModel.quantum AlgorithmGate.model OracleModel.empty
      BitWord.model services).Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State base Reference ((ExecutionModel.quantum AlgorithmGate.model
      OracleModel.empty BitWord.model services).HiddenState × History))
    (points : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents (actualCurveSpec I) (entry.1.read basePoint)
          (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib ∧
        PointRepresents (actualCurveSpec I) (entry.1.read targetPoint) I.publicKey.toMathlib)
    (value : Store (tableContext base noQuantum) ×
      ((ExecutionModel.quantum AlgorithmGate.model OracleModel.empty
        BitWord.model services).HiddenState ×
        (History ×
          (paidPrefix (services := services) base noQuantum I basePoint targetPoint).Path)))
    (positive : 0 <
      (((paidPrefix (services := services) base noQuantum I basePoint targetPoint).execute
        environment Reference state).block value).mass) :
    Signed.Constants (tableFrame base noQuantum) (actualCurveSpec I) value.1 ∧
      Signed.pairedRows (actualCurveSpec I) (tableFrame base noQuantum)
        (DomainParameters.basePoint I.curveCert I.baseCert) I.publicKey value.1 ∧
      PointRepresents (actualCurveSpec I)
        (value.1.read (originalInputAfterTables base noQuantum basePoint))
        (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib ∧
      PointRepresents (actualCurveSpec I)
        (value.1.read (originalInputAfterTables base noQuantum targetPoint))
        I.publicKey.toMathlib := by
  exact Signed.prepare_after_post_on_support
    (prepareWithTables (services := services) base noQuantum)
    (tableFrame base noQuantum) (actualCurveSpec I)
    (originalInputAfterTables base noQuantum basePoint)
    (originalInputAfterTables base noQuantum targetPoint) environment
    (DomainParameters.basePoint I.curveCert I.baseCert) I.publicKey
    DomainParameters.subgroupOrder I.subgroupCert.prime subgroupOrder_large
    (basePoint_addOrderOf I) (targetPoint_addOrderOf I) (by decide)
    (tableFrame_original_inputFree base noQuantum basePoint)
    (tableFrame_original_inputFree base noQuantum targetPoint)
    Reference state
    (allocated_input_support base noQuantum I basePoint targetPoint
      readsBorrowed environment Reference state points) value positive

private lemma readConditions_of_post {ctx : RuntimeCtx .quantum}
    (original : Sampling.Storage.Inputs ctx)
    (first second : PrimeFieldShortWeierstrass.AffinePoint original.curve.curve)
    (store : Store ctx) (constants : Signed.Constants original.frame original.curve store)
    (rows : Signed.pairedRows original.curve original.frame first second store)
    (baseRep : PointRepresents original.curve (store.read original.base) first.toMathlib)
    (targetRep : PointRepresents original.curve (store.read original.target) second.toMathlib) :
    Sampling.Storage.Conditional.readConditions original first.toMathlib second.toMathlib
      (fun input => store.read input) := by
  refine ⟨⟨baseRep, targetRep⟩, constants.modulus, constants.zero, constants.one,
    constants.curveA, ?_⟩
  have readRow {length : Nat} (array : CWriteRef ctx (.fixedVector length (.unsignedWord 256)))
      (index : Fin length) : store.read (WindowTables.rowRead array index) =
        (store.read (.storage array.toCStorageRef)).get index := by
    simpa only [Transport.liftInput_id] using
      Sampling.Storage.Conditional.actual_row_read (Transport.id ctx) array store index
  constructor
  · intro index
    have row := rows.1 index
    rw [readRow, readRow] at row
    exact row
  · intro index
    have row := rows.2 index
    rw [readRow, readRow] at row
    exact row

/-- The actual paid prefix supplies the existing finalized-recovery input condition. -/
lemma paidPrefix_inputsSupported (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (I : DomainParameters.PublicKeyInstance)
    (basePoint targetPoint : CInputRef base (PointShape 256))
    (readsBorrowed : ∀ first second : Store base,
      first.readBorrowedClassical = second.readBorrowedClassical →
      first.read basePoint = second.read basePoint ∧
        first.read targetPoint = second.read targetPoint)
    (environment : (ExecutionModel.quantum AlgorithmGate.model OracleModel.empty
      BitWord.model services).Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State base Reference ((ExecutionModel.quantum AlgorithmGate.model
      OracleModel.empty BitWord.model services).HiddenState × History))
    (points : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents (actualCurveSpec I) (entry.1.read basePoint)
          (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib ∧
        PointRepresents (actualCurveSpec I) (entry.1.read targetPoint) I.publicKey.toMathlib) :
    Sampling.Storage.Conditional.inputsSupported
      (retainedInputs base noQuantum I basePoint targetPoint)
      (Transport.id (tableContext base noQuantum))
      (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib
      ((paidPrefix (services := services) base noQuantum I basePoint targetPoint).execute
        environment Reference state) := by
  intro value positive
  have post := paidPrefix_post_on_support base noQuantum I basePoint targetPoint readsBorrowed
    environment Reference state points value positive
  have actual := readConditions_of_post (retainedInputs base noQuantum I basePoint targetPoint)
    (DomainParameters.basePoint I.curveCert I.baseCert) I.publicKey value.1
    post.1 post.2.1 post.2.2.1 post.2.2.2
  apply (Sampling.Storage.Conditional.readConditions_congr
    (retainedInputs base noQuantum I basePoint targetPoint)
    (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib
    (fun input => value.1.read input)
    (fun input => value.1.read ((Transport.id (tableContext base noQuantum)).liftInput input))
    (fun input => congrArg value.1.read (Transport.liftInput_id input).symm)).mp
  exact actual

end
end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
