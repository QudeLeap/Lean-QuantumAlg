/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Circuit.Exponents
import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Trajectory.Branch
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Execution.Trace

/-!
# Original exponent programs on the actual measured-scalar systems

The original consecutive exponent circuit is physically relabelled by the
same frame offset used by the actual owned exponent wires. Relabeling rewrites
every gate placement. The logical basis uses the established exact paired
big-endian equivalence, including exponent width zero.

Original consecutive exponent programs become actual unitary instructions
on these systems. Their construction, native trace, cost and dependency
depth are retained without an added resource allowance.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation

/-- Original consecutive binary labels denote exactly the actual paired exponent values. -/
def exponentProgramBasis (modulus exponentWidth : Nat) :
    (Qubits (exponentWidth + exponentWidth)).Index ≃
      (exponents modulus.size (2 * exponentWidth)).register.Index :=
  (prodEquiv (m := exponentWidth) (n := exponentWidth)).symm.trans
    (pairedExponentEquiv modulus exponentWidth)

/-- The unchanged original pair is placed in its exact supplied exponent basis. -/
theorem exponentProgramBasis_branch (modulus exponentWidth : Nat)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth)) :
    exponentProgramBasis modulus exponentWidth (prodEquiv branch) =
      pairedExponentInput modulus exponentWidth branch := by
  change pairedExponentEquiv modulus exponentWidth
    ((prodEquiv (m := exponentWidth) (n := exponentWidth)).symm (prodEquiv branch)) = _
  rw [Equiv.symm_apply_apply, pairedExponentEquiv_apply]

/-- The basis correspondence carries each original selection on that same physical wire. -/
theorem exponentProgramBasis_physical_value (modulus exponentWidth : Nat)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (index : Fin (2 * exponentWidth)) :
    (exponentProgramBasis modulus exponentWidth (prodEquiv branch)
      (rangePosition modulus.size (2 * exponentWidth) index)).val =
      (BinaryLabelEncoding.bool.encode
        (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch index)).val := by
  rw [exponentProgramBasis_branch]
  exact exponentInput_physical_value modulus (2 * exponentWidth) _ index

/-- Every source qubit names the corresponding resident exponent wire. -/
private def exponentPosition (modulus exponentWidth : Nat) :
    Fin (exponentWidth + exponentWidth) ≃
      Fin (exponents modulus.size (2 * exponentWidth)).systemCount :=
  (finCongr (show exponentWidth + exponentWidth = 2 * exponentWidth by omega)).trans
    ((finCongr List.length_range).symm.trans
      (indexedPositions modulus.size (List.range (2 * exponentWidth)) List.nodup_range))

private theorem exponentPosition_dimensions (modulus exponentWidth : Nat)
    (index : Fin (exponentWidth + exponentWidth)) :
    (((QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout).wire
      index).dimension =
    ((exponents modulus.size (2 * exponentWidth)).quantumLayout.wire
      (exponentPosition modulus exponentWidth index)).dimension := by
  change 2 = _
  have same : exponentPosition modulus exponentWidth index =
      rangePosition modulus.size (2 * exponentWidth)
        (finCongr (show exponentWidth + exponentWidth = 2 * exponentWidth by omega) index) := rfl
  rw [same, rangePosition_wire]

/-- The placed native word uses the actual owned exponent wires in their original order. -/
def placedExponentProgram (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout) :
    UnitaryCircuit AlgorithmGate.model .empty
      (exponents modulus.size (2 * exponentWidth)).quantumLayout :=
  UnitaryCircuit.placeAt _ _ (exponentPosition modulus exponentWidth).toEmbedding
    (exponentPosition_dimensions modulus exponentWidth) program

private theorem bigEndian_cast {sourceWidth targetWidth : Nat}
    (same : sourceWidth = targetWidth) (bits : Fin targetWidth → Fin 2)
    (index : Fin sourceWidth) :
    (BinaryBasis.bigEndianEquiv sourceWidth).symm
      (Fin.cast (congrArg (fun width : Nat => 2 ^ width) same.symm)
        (BinaryBasis.bigEndianEquiv targetWidth bits)) index =
      bits (Fin.cast same index) := by
  subst targetWidth
  simp

private theorem exponentProgramBasis_selected (modulus exponentWidth : Nat)
    (basis : (exponents modulus.size (2 * exponentWidth)).register.Index) :
    UnitaryCircuit.selectedInput
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout
      (exponents modulus.size (2 * exponentWidth)).quantumLayout
      (exponentPosition modulus exponentWidth).toEmbedding
      (exponentPosition_dimensions modulus exponentWidth) basis =
    (QuantumSignature.qubitsIndexEquiv (exponentWidth + exponentWidth)).symm
      ((exponentProgramBasis modulus exponentWidth).symm basis) := by
  funext index
  apply Fin.ext
  change (basis (exponentPosition modulus exponentWidth index)).val = _
  rw [show exponentPosition modulus exponentWidth index =
      rangePosition modulus.size (2 * exponentWidth)
        (finCongr (show exponentWidth + exponentWidth = 2 * exponentWidth by omega)
          index) from rfl, ← rangeBasis_value]
  simp only [exponentProgramBasis, pairedExponentEquiv,
    QuantumSignature.qubitsIndexEquiv, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply]
  exact congrArg Fin.val
    (bigEndian_cast
      (show exponentWidth + exponentWidth = 2 * exponentWidth by omega)
      (rangeBasis modulus.size (2 * exponentWidth) basis) index).symm

/-- Every matrix entry is the original program entry under the exact same exponent values. -/
theorem placedExponentProgram_matrix (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    (row column : (exponents modulus.size (2 * exponentWidth)).register.Index) :
    (placedExponentProgram modulus exponentWidth program).matrix row column =
      program.binaryMatrix ((exponentProgramBasis modulus exponentWidth).symm row)
        ((exponentProgramBasis modulus exponentWidth).symm column) := by
  rw [placedExponentProgram, UnitaryCircuit.placeAt_matrix,
    UnitaryCircuit.operatorAt_entry]
  rw [exponentProgramBasis_selected, exponentProgramBasis_selected]
  have complete :
      (exponents modulus.size (2 * exponentWidth)).quantumLayout.restrictComplementBasis
        (Finset.univ.map (exponentPosition modulus exponentWidth).toEmbedding) row =
      (exponents modulus.size (2 * exponentWidth)).quantumLayout.restrictComplementBasis
        (Finset.univ.map (exponentPosition modulus exponentWidth).toEmbedding) column := by
    funext index
    exact False.elim (Finset.mem_compl.mp index.property
      (by
        obtain ⟨source, same⟩ := (exponentPosition modulus exponentWidth).surjective index.val
        rw [← same]
        exact Finset.mem_map_of_mem _ (Finset.mem_univ source)))
  rw [if_pos complete, mul_one]
  rfl

/-- Actual original paired input and output labels retain the original complex matrix entry. -/
theorem placedExponentProgram_branch_matrix (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    (row column : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth)) :
    (placedExponentProgram modulus exponentWidth program).matrix
      (pairedExponentInput modulus exponentWidth row)
      (pairedExponentInput modulus exponentWidth column) =
      program.binaryMatrix (prodEquiv row) (prodEquiv column) := by
  rw [← exponentProgramBasis_branch, ← exponentProgramBasis_branch,
    placedExponentProgram_matrix, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Normalized original amplitudes use the bijective actual exponent basis without rescaling. -/
def exponentProgramState (modulus exponentWidth : Nat)
    (state : NormalizedVector (Qubits (exponentWidth + exponentWidth))) :
    NormalizedVector (exponents modulus.size (2 * exponentWidth)).register :=
  let transport := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (exponentProgramBasis modulus exponentWidth)
  NormalizedVector.ofVector (transport state.vec)
    ((transport.norm_map state.vec).trans state.norm_eq_one)

/-- The state correspondence retains each exact original amplitude. -/
theorem exponentProgramState_value (modulus exponentWidth : Nat)
    (state : NormalizedVector (Qubits (exponentWidth + exponentWidth)))
    (row : (exponents modulus.size (2 * exponentWidth)).register.Index) :
    exponentProgramState modulus exponentWidth state row =
      state ((exponentProgramBasis modulus exponentWidth).symm row) := rfl

/-- Every original basis state becomes the identical physically supplied exponent value. -/
theorem exponentProgramState_ket (modulus exponentWidth : Nat)
    (label : (Qubits (exponentWidth + exponentWidth)).Index) :
    exponentProgramState modulus exponentWidth (NormalizedVector.ket label) =
      NormalizedVector.ket (exponentProgramBasis modulus exponentWidth label) := by
  apply NormalizedVector.ext
  intro row
  simp only [exponentProgramState_value, NormalizedVector.ket_apply,
    Equiv.symm_apply_eq]

/-- The actual physically placed program has the exact original normalized state action. -/
theorem placedExponentProgram_normalized (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    (state : NormalizedVector (Qubits (exponentWidth + exponentWidth))) :
    (placedExponentProgram modulus exponentWidth program).applyNormalized
      (exponentProgramState modulus exponentWidth state) =
      exponentProgramState modulus exponentWidth (program.binaryMatrix.apply state) := by
  apply NormalizedVector.ext
  intro row
  change (∑ column,
    (placedExponentProgram modulus exponentWidth program).matrix row column *
      state ((exponentProgramBasis modulus exponentWidth).symm column)) =
    ∑ column, program.binaryMatrix
      ((exponentProgramBasis modulus exponentWidth).symm row) column *
      state column
  simp_rw [placedExponentProgram_matrix]
  exact (exponentProgramBasis modulus exponentWidth).symm.sum_comp
    (fun column : (Qubits (exponentWidth + exponentWidth)).Index =>
      program.binaryMatrix
        ((exponentProgramBasis modulus exponentWidth).symm row) column * state column)

/-- Physical and logical placement preserve every original native event in order. -/
theorem placedExponentProgram_trace (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout) :
    (placedExponentProgram modulus exponentWidth program).eventTrace =
      program.eventTrace := by
  exact UnitaryCircuit.placeAt_eventTrace _ _ _ _ program

/-- Placement introduces no additional native event cost. -/
theorem placedExponentProgram_cost (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout) :
    (placedExponentProgram modulus exponentWidth program).eventCost =
      program.eventCost := by
  exact UnitaryCircuit.placeAt_eventCost _ _ _ _ program

/-- Placement preserves the exact original dependency-depth expression. -/
theorem placedExponentProgram_depth (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout) :
    (placedExponentProgram modulus exponentWidth program).eventDepth =
      program.eventDepth := by
  exact UnitaryCircuit.placeAt_eventDepth _ _ _ _ program

/-- The placed original exponent program is an actual instruction on the owned exponent context. -/
def placedExponentCircuit (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (exponents modulus.size (2 * exponentWidth))
      (exponents modulus.size (2 * exponentWidth)) :=
  .unitary (placedExponentProgram modulus exponentWidth program)

/-- The actual instruction emits exactly the original native event trace. -/
theorem placedExponentCircuit_trace (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    (path : (placedExponentCircuit modulus exponentWidth program).Path) :
    (placedExponentCircuit modulus exponentWidth program).eventTrace path =
      program.eventTrace := placedExponentProgram_trace modulus exponentWidth program

/-- The resource pool comes from the exact same actual native trace. -/
theorem placedExponentCircuit_cost (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    (path : (placedExponentCircuit modulus exponentWidth program).Path) :
    (placedExponentCircuit modulus exponentWidth program).resourcePool path =
      program.eventCost := by
  rw [Circuit.resourcePool, placedExponentCircuit_trace]
  exact UnitaryCircuit.ofList_eventTrace_eq_eventCost program

/-- The actual instruction retains the original dependency depth for every duration assignment. -/
theorem placedExponentCircuit_depth (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat)
    (path : (placedExponentCircuit modulus exponentWidth program).Path) :
    (placedExponentCircuit modulus exponentWidth program).depth duration path =
      program.evaluatedEventDepth duration := by
  change DepthExpr.depthEval duration
    (placedExponentProgram modulus exponentWidth program).eventDepth = _
  rw [placedExponentProgram_depth]
  rfl

universe u

/-- The unchanged original exact range preparation runs on the same owned exponent systems. -/
def placedExponentPreparation {G : Type u} [Group G] (modulus : Nat)
    (problem : FiniteCyclicDLP.KnownOrderProblem G) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (exponents modulus.size (2 * FiniteCyclicDLP.orderWidth problem))
      (exponents modulus.size (2 * FiniteCyclicDLP.orderWidth problem)) :=
  placedExponentCircuit modulus (FiniteCyclicDLP.orderWidth problem)
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit problem)

/-- The unchanged original pair of inverse QFTs runs on those same owned exponent systems. -/
def placedExponentReadout {G : Type u} [Group G] (modulus : Nat)
    (problem : FiniteCyclicDLP.KnownOrderProblem G) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (exponents modulus.size (2 * FiniteCyclicDLP.orderWidth problem))
      (exponents modulus.size (2 * FiniteCyclicDLP.orderWidth problem)) :=
  placedExponentCircuit modulus (FiniteCyclicDLP.orderWidth problem)
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentReadoutCircuit problem)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
