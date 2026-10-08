/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Exponents
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Circuit.Exponents
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

private def beforeExponentBasis (modulus exponentWidth : Nat) :=
  ContextUnion.unionBasisEquiv (InversePreparation.before modulus.size)
    (exponents modulus.size (2 * exponentWidth))
    (input_disjoint modulus.size (2 * exponentWidth))

/-- Real coordinate identity and original exponent gates act on the original supplied context. -/
def beforeExponentProgram (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout) :
    UnitaryCircuit AlgorithmGate.model .empty
      (before modulus.size (2 * exponentWidth)).quantumLayout :=
  ContextUnion.frameRightUnitary (InversePreparation.before modulus.size)
    (exponents modulus.size (2 * exponentWidth))
    (input_disjoint modulus.size (2 * exponentWidth))
    (placedExponentProgram modulus exponentWidth program)

private theorem beforeExponentProgram_matrix (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    (row column : (before modulus.size (2 * exponentWidth)).register.Index) :
    (beforeExponentProgram modulus exponentWidth program).matrix row column =
      (if (beforeExponentBasis modulus exponentWidth row).1 =
        (beforeExponentBasis modulus exponentWidth column).1 then 1 else 0) *
      (placedExponentProgram modulus exponentWidth program).matrix
        (beforeExponentBasis modulus exponentWidth row).2
        (beforeExponentBasis modulus exponentWidth column).2 := by
  exact ContextUnion.contextUnion_frameRightUnitary_entry
    (InversePreparation.before modulus.size)
    (exponents modulus.size (2 * exponentWidth))
    (input_disjoint modulus.size (2 * exponentWidth))
    (placedExponentProgram modulus exponentWidth program) row column

/-- Complete original input labels retain both coordinate words in every complex matrix entry. -/
theorem beforeExponentProgram_inputLabel (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    (row column : (exponents modulus.size (2 * exponentWidth)).register.Index)
    (rowX rowY columnX columnY : Fin (2 ^ modulus.size)) :
    (beforeExponentProgram modulus exponentWidth program).matrix
      (inputLabel modulus.size (2 * exponentWidth) row rowX rowY)
      (inputLabel modulus.size (2 * exponentWidth) column columnX columnY) =
      (if (rowX, rowY) = (columnX, columnY) then 1 else 0) *
        (placedExponentProgram modulus exponentWidth program).matrix row column := by
  rw [beforeExponentProgram_matrix]
  simp only [beforeExponentBasis, inputLabel, Equiv.apply_symm_apply,
    (InversePreparation.inputBasisEquiv modulus.size).symm.injective.eq_iff]

/-- Original paired labels expose the unchanged original exponent matrix and coordinate identity. -/
theorem beforeExponentProgram_paired_entry (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    (row column : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (rowX rowY columnX columnY : Fin (2 ^ modulus.size)) :
    (beforeExponentProgram modulus exponentWidth program).matrix
      (inputLabel modulus.size (2 * exponentWidth)
        (pairedExponentInput modulus exponentWidth row) rowX rowY)
      (inputLabel modulus.size (2 * exponentWidth)
        (pairedExponentInput modulus exponentWidth column) columnX columnY) =
      (if (rowX, rowY) = (columnX, columnY) then 1 else 0) *
        program.binaryMatrix (prodEquiv row) (prodEquiv column) := by
  rw [beforeExponentProgram_inputLabel, placedExponentProgram_branch_matrix]

/-- The unchanged original native event list is emitted beside the real coordinate frame. -/
theorem beforeExponentProgram_trace (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout) :
    (beforeExponentProgram modulus exponentWidth program).eventTrace =
      program.eventTrace := by
  rw [beforeExponentProgram, ContextUnion.contextUnion_frameRightUnitary_eventTrace,
    placedExponentProgram_trace]

/-- The framed original exponent action is an actual instruction on the original caller input. -/
def beforeExponentCircuit (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (before modulus.size (2 * exponentWidth))
      (before modulus.size (2 * exponentWidth)) :=
  .unitary (beforeExponentProgram modulus exponentWidth program)

/-- All reference systems remain beside the exact original-coordinate exponent operator. -/
def beforeExponentOperator (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    (Reference : Register) :
    UnitaryOperator (Register.prod (before modulus.size (2 * exponentWidth)).register Reference) :=
  UnitaryOperator.prodTensor (beforeExponentProgram modulus exponentWidth program).matrix
    (1 : UnitaryOperator Reference)

/-- Actual framed execution has its complete quantum and arbitrary-reference density. -/
theorem beforeExponentCircuit_density (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size (2 * exponentWidth)) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ((beforeExponentCircuit modulus exponentWidth program).execute
      Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (beforeExponentOperator modulus exponentWidth program Reference)
        state.quantumMarginal :=
  Circuit.unitary_jointDensity (beforeExponentProgram modulus exponentWidth program) state

/-- Every original classical store and history keeps its own exact transformed quantum block. -/
theorem beforeExponentCircuit_block (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size (2 * exponentWidth)) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (stored : Store (before modulus.size (2 * exponentWidth)))
    (hidden : ClassicalOracleModel.empty.HiddenState) (history : H) :
    ((beforeExponentCircuit modulus exponentWidth program).execute Reference state).block
      (stored, (hidden, (history, ()))) =
      DensityOperator.applyUnitary
        (beforeExponentOperator modulus exponentWidth program Reference)
        (state.block (stored, (hidden, history))) :=
  Circuit.execute_unitary_block state (beforeExponentProgram modulus exponentWidth program)
    stored hidden history

/-- The complete actual instruction retains the original native resource pool. -/
theorem beforeExponentCircuit_cost (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    (path : (beforeExponentCircuit modulus exponentWidth program).Path) :
    (beforeExponentCircuit modulus exponentWidth program).resourcePool path =
      program.eventCost := by
  change ResourcePool.ofList
    (beforeExponentProgram modulus exponentWidth program).eventTrace = _
  rw [beforeExponentProgram_trace]
  exact UnitaryCircuit.ofList_eventTrace_eq_eventCost program

/-- The actual coordinate identity contributes no depth for any native duration assignment. -/
theorem beforeExponentCircuit_depth (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat)
    (path : (beforeExponentCircuit modulus exponentWidth program).Path) :
    (beforeExponentCircuit modulus exponentWidth program).depth duration path =
      program.evaluatedEventDepth duration := by
  change max 0
    ((placedExponentProgram modulus exponentWidth program).evaluatedEventDepth
      duration) = _
  rw [Nat.zero_max]
  change DepthExpr.depthEval duration
    (placedExponentProgram modulus exponentWidth program).eventDepth = _
  rw [placedExponentProgram_depth]
  rfl

universe u

/-- The original exponent preparation executes before actual scalar-work initialization. -/
def beforeExponentPreparation {G : Type u} [Group G] (modulus : Nat)
    (problem : FiniteCyclicDLP.KnownOrderProblem G) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (before modulus.size (2 * FiniteCyclicDLP.orderWidth problem))
      (before modulus.size (2 * FiniteCyclicDLP.orderWidth problem)) :=
  beforeExponentCircuit modulus (FiniteCyclicDLP.orderWidth problem)
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit problem)

/-- The actual framed ECC preparation inherits the generic symbolic width bounds. -/
theorem beforeExponentPreparation_widthBounds {G : Type u} [Group G]
    (modulus : Nat) (problem : FiniteCyclicDLP.KnownOrderProblem G)
    (path : (beforeExponentPreparation modulus problem).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        ((beforeExponentPreparation modulus problem).resourcePool path) ≤
        22 * FiniteCyclicDLP.orderWidth problem ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        ((beforeExponentPreparation modulus problem).resourcePool path) ≤
        6 * FiniteCyclicDLP.orderWidth problem ∧
      (beforeExponentPreparation modulus problem).depth (fun _ => 1) path ≤
        10 * FiniteCyclicDLP.orderWidth problem + 1 := by
  have source := FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit_widthBounds
    problem .empty
  constructor
  · calc
      _ = ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
            (.gate .singleQubit)
            (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit
              problem).eventCost := by
          exact congrArg
            (ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
              (.gate .singleQubit))
            (beforeExponentCircuit_cost modulus (FiniteCyclicDLP.orderWidth problem)
              (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit problem) path)
      _ ≤ _ := source.1
  constructor
  · calc
      _ = ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
            (.gate .cnot)
            (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit
              problem).eventCost := by
          exact congrArg
            (ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot))
            (beforeExponentCircuit_cost modulus (FiniteCyclicDLP.orderWidth problem)
              (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit problem) path)
      _ ≤ _ := source.2.1
  · calc
      _ = (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit
            problem).evaluatedEventDepth (fun _ => 1) := by
          exact beforeExponentCircuit_depth modulus (FiniteCyclicDLP.orderWidth problem)
            (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit problem)
            (fun _ => 1) path
      _ ≤ _ := source.2.2

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
