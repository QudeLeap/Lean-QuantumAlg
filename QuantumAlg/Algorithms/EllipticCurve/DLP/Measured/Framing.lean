/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Exponents
import all QuantumAlg.Core.Execution.Unitary.Local

/-!
# Original exponent preparation beside the supplied coordinate words

The actual program tensors identity on the supplied coordinates with the
physically placed original exponent gates. The established input union basis
puts this tensor on exactly the original caller context. No coordinate is
allocated, relabelled or exchanged.

Complete input-label matrix entries expose the unchanged coordinate factor,
and actual execution retains arbitrary quantum-reference correlations and
each original classical block. Native trace, cost and depth remain original.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation MAU.Inversion.SharedEEA

private def coordinateIdentity (width : Nat) :
    UnitaryCircuit (InversePreparation.before width).register :=
  .identity (InversePreparation.before width).register
    (InversePreparation.before width).physicalIdx (InversePreparation.before width).identitiesNodup

private theorem beforeExponentMerge (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    PhysicalLayout.DisjointMerge (coordinateIdentity modulus.size).physical_idx
      (placedExponentProgram modulus exponentWidth program physical).physical_idx := by
  refine ⟨(coordinateIdentity modulus.size).physical_idx_nodup,
    (placedExponentProgram modulus exponentWidth program physical).physical_idx_nodup, ?_⟩
  change List.Disjoint (InversePreparation.before modulus.size).physicalIdx _
  rw [placedExponentProgram_physical]
  exact (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp
    (input_disjoint modulus.size (2 * exponentWidth)).2

private def beforeExponentBasis (modulus exponentWidth : Nat) :=
  ContextUnion.unionBasisEquiv (InversePreparation.before modulus.size)
    (exponents modulus.size (2 * exponentWidth))
    (input_disjoint modulus.size (2 * exponentWidth))

/-- Real coordinate identity and original exponent gates act on the original supplied context. -/
def beforeExponentProgram (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    UnitaryCircuit (before modulus.size (2 * exponentWidth)).register :=
  UnitaryCircuit.reindex (beforeExponentBasis modulus exponentWidth).symm
    (UnitaryCircuit.tensor (coordinateIdentity modulus.size)
      (placedExponentProgram modulus exponentWidth program physical)
      (beforeExponentMerge modulus exponentWidth program physical))

/-- The actual program lists exactly the original coordinates followed by the exponent systems. -/
theorem beforeExponentProgram_physical (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    (beforeExponentProgram modulus exponentWidth program physical).physical_idx =
      (before modulus.size (2 * exponentWidth)).physicalIdx := by
  change (InversePreparation.before modulus.size).physicalIdx ++
    (placedExponentProgram modulus exponentWidth program physical).physical_idx = _
  rw [placedExponentProgram_physical, RuntimeCtx.physicalIdx_disjointUnion]

private theorem beforeExponentProgram_matrix (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (row column : (before modulus.size (2 * exponentWidth)).register.Index) :
    (beforeExponentProgram modulus exponentWidth program physical).matrix row column =
      (if (beforeExponentBasis modulus exponentWidth row).1 =
        (beforeExponentBasis modulus exponentWidth column).1 then 1 else 0) *
      (placedExponentProgram modulus exponentWidth program physical).matrix
        (beforeExponentBasis modulus exponentWidth row).2
        (beforeExponentBasis modulus exponentWidth column).2 := by
  change (UnitaryOperator.prodTensor
    (1 : UnitaryOperator (InversePreparation.before modulus.size).register)
    (placedExponentProgram modulus exponentWidth program physical).matrix)
      (beforeExponentBasis modulus exponentWidth row)
      (beforeExponentBasis modulus exponentWidth column) = _
  rw [UnitaryOperator.prodTensor_apply]
  rfl

/-- Complete original input labels retain both coordinate words in every complex matrix entry. -/
theorem beforeExponentProgram_inputLabel (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (row column : (exponents modulus.size (2 * exponentWidth)).register.Index)
    (rowX rowY columnX columnY : Fin (2 ^ modulus.size)) :
    (beforeExponentProgram modulus exponentWidth program physical).matrix
      (inputLabel modulus.size (2 * exponentWidth) row rowX rowY)
      (inputLabel modulus.size (2 * exponentWidth) column columnX columnY) =
      (if (rowX, rowY) = (columnX, columnY) then 1 else 0) *
        (placedExponentProgram modulus exponentWidth program physical).matrix row column := by
  rw [beforeExponentProgram_matrix]
  simp only [beforeExponentBasis, inputLabel, Equiv.apply_symm_apply,
    (InversePreparation.inputBasisEquiv modulus.size).symm.injective.eq_iff]

/-- Original paired labels expose the unchanged original exponent matrix and coordinate identity. -/
theorem beforeExponentProgram_paired_entry (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (row column : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (rowX rowY columnX columnY : Fin (2 ^ modulus.size)) :
    (beforeExponentProgram modulus exponentWidth program physical).matrix
      (inputLabel modulus.size (2 * exponentWidth)
        (pairedExponentInput modulus exponentWidth row) rowX rowY)
      (inputLabel modulus.size (2 * exponentWidth)
        (pairedExponentInput modulus exponentWidth column) columnX columnY) =
      (if (rowX, rowY) = (columnX, columnY) then 1 else 0) *
        program.matrix (prodEquiv row) (prodEquiv column) := by
  rw [beforeExponentProgram_inputLabel, placedExponentProgram_branch_matrix]

/-- The unchanged original native event list is emitted beside the real coordinate frame. -/
theorem beforeExponentProgram_trace (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    (beforeExponentProgram modulus exponentWidth program physical).eventTrace =
      program.eventTrace := by
  change [] ++ (placedExponentProgram modulus exponentWidth program physical).eventTrace = _
  rw [List.nil_append, placedExponentProgram_trace]

/-- The framed original exponent action is an actual instruction on the original caller input. -/
def beforeExponentCircuit (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    Circuit (before modulus.size (2 * exponentWidth))
      (before modulus.size (2 * exponentWidth)) :=
  .unitary (beforeExponentProgram modulus exponentWidth program physical)
    (beforeExponentProgram_physical modulus exponentWidth program physical)

/-- All reference systems remain beside the exact original-coordinate exponent operator. -/
def beforeExponentOperator (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (Reference : Register) :
    UnitaryOperator (Register.prod (before modulus.size (2 * exponentWidth)).register Reference) :=
  UnitaryOperator.prodTensor (beforeExponentProgram modulus exponentWidth program physical).matrix
    (1 : UnitaryOperator Reference)

/-- Actual framed execution has its complete quantum and arbitrary-reference density. -/
theorem beforeExponentCircuit_density (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size (2 * exponentWidth)) Reference H) :
    ((beforeExponentCircuit modulus exponentWidth program physical).execute
      Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (beforeExponentOperator modulus exponentWidth program physical Reference)
        state.quantumMarginal :=
  Circuit.unitary_jointDensity (beforeExponentProgram modulus exponentWidth program physical)
    (beforeExponentProgram_physical modulus exponentWidth program physical) state

/-- Every original classical store and history keeps its own exact transformed quantum block. -/
theorem beforeExponentCircuit_block (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size (2 * exponentWidth)) Reference H)
    (stored : Store (before modulus.size (2 * exponentWidth))) (history : H) :
    ((beforeExponentCircuit modulus exponentWidth program physical).execute Reference state).block
      (stored, (history, ())) =
      DensityOperator.applyUnitary
        (beforeExponentOperator modulus exponentWidth program physical Reference)
        (state.block (stored, history)) :=
  Circuit.execute_unitary_block state (beforeExponentProgram modulus exponentWidth program physical)
    (beforeExponentProgram_physical modulus exponentWidth program physical) stored history

/-- The complete actual instruction retains the original native resource pool. -/
theorem beforeExponentCircuit_cost (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (path : (beforeExponentCircuit modulus exponentWidth program physical).Path) :
    (beforeExponentCircuit modulus exponentWidth program physical).resourcePool path =
      program.eventCost := by
  change ResourcePool.ofList
    (beforeExponentProgram modulus exponentWidth program physical).eventTrace = _
  rw [beforeExponentProgram_trace]
  exact UnitaryCircuit.ofList_eventTrace_eq_eventCost program

/-- The actual coordinate identity contributes no depth for any native duration assignment. -/
theorem beforeExponentCircuit_depth (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (duration : Resource.Event .quantum → Nat)
    (path : (beforeExponentCircuit modulus exponentWidth program physical).Path) :
    (beforeExponentCircuit modulus exponentWidth program physical).depth duration path =
      program.evaluatedEventDepth duration := by
  change max 0
    ((placedExponentProgram modulus exponentWidth program physical).evaluatedEventDepth
      duration) = _
  rw [Nat.zero_max]
  change DepthExpr.depthEval duration
    (placedExponentProgram modulus exponentWidth program physical).eventDepth = _
  rw [placedExponentProgram_depth]
  rfl

universe u

/-- The original exponent preparation executes before actual scalar-work initialization. -/
def beforeExponentPreparation {G : Type u} [Group G] (modulus : Nat)
    (problem : FiniteCyclicDLP.KnownOrderProblem G) :
    Circuit (before modulus.size (2 * FiniteCyclicDLP.orderWidth problem))
      (before modulus.size (2 * FiniteCyclicDLP.orderWidth problem)) :=
  beforeExponentCircuit modulus (FiniteCyclicDLP.orderWidth problem)
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit problem)
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit_physical_idx problem)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
