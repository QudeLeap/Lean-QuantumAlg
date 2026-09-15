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

/-- The physical map used to rewrite the original gates names the actual owned exponent systems. -/
def exponentProgramPlacement (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    PhysicalLayout.Relabeling program.physical_idx
      (exponents modulus.size (2 * exponentWidth)).physicalIdx where
  toFun := fun index => InPlaceControlled.frameWidth modulus.size + index
  map_layout := by
    rw [physical, indexedContext_physical]
    rw [show exponentWidth + exponentWidth = 2 * exponentWidth by omega]
  old_nodup := program.physical_idx_nodup
  new_nodup := (exponents modulus.size (2 * exponentWidth)).identitiesNodup

/-- Gate placement uses precisely the wire whose value is read by the paired basis map. -/
theorem exponentProgramPlacement_wire (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (index : Fin (2 * exponentWidth)) :
    (exponentProgramPlacement modulus exponentWidth program physical).toFun index.val =
      ((exponents modulus.size (2 * exponentWidth)).quantumLayout.wire
        (rangePosition modulus.size (2 * exponentWidth) index)).identity := by
  rw [rangePosition_wire]
  rfl

/-- Rewrite every original gate placement and use the exact original paired logical values. -/
def placedExponentProgram (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    UnitaryCircuit (exponents modulus.size (2 * exponentWidth)).register :=
  UnitaryCircuit.reindex (exponentProgramBasis modulus exponentWidth)
    (program.relabel (exponentProgramPlacement modulus exponentWidth program physical))

/-- The actual construction recursively rewrites gate addresses before its basis reindexing. -/
theorem placedExponentProgram_sequence (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    (placedExponentProgram modulus exponentWidth program physical).sequence =
      .reindex (exponentProgramBasis modulus exponentWidth)
        (program.sequence.rewriteSystemIdx
          (fun index => InPlaceControlled.frameWidth modulus.size + index)) := rfl

/-- The placed program occupies exactly the actual exponent context. -/
theorem placedExponentProgram_physical (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    (placedExponentProgram modulus exponentWidth program physical).physical_idx =
      (exponents modulus.size (2 * exponentWidth)).physicalIdx := rfl

/-- Every matrix entry is the original program entry under the exact same exponent values. -/
theorem placedExponentProgram_matrix (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (row column : (exponents modulus.size (2 * exponentWidth)).register.Index) :
    (placedExponentProgram modulus exponentWidth program physical).matrix row column =
      program.matrix ((exponentProgramBasis modulus exponentWidth).symm row)
        ((exponentProgramBasis modulus exponentWidth).symm column) := by
  change (program.relabel (exponentProgramPlacement modulus exponentWidth program physical)).matrix
    ((exponentProgramBasis modulus exponentWidth).symm row)
    ((exponentProgramBasis modulus exponentWidth).symm column) = _
  exact congrArg (fun matrix : HilbertOperator (Qubits (exponentWidth + exponentWidth)) =>
    matrix ((exponentProgramBasis modulus exponentWidth).symm row)
      ((exponentProgramBasis modulus exponentWidth).symm column))
    (UnitaryCircuit.relabel_matrix program
      (exponentProgramPlacement modulus exponentWidth program physical))

/-- Actual original paired input and output labels retain the original complex matrix entry. -/
theorem placedExponentProgram_branch_matrix (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (row column : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth)) :
    (placedExponentProgram modulus exponentWidth program physical).matrix
      (pairedExponentInput modulus exponentWidth row)
      (pairedExponentInput modulus exponentWidth column) =
      program.matrix (prodEquiv row) (prodEquiv column) := by
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
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (state : NormalizedVector (Qubits (exponentWidth + exponentWidth))) :
    (placedExponentProgram modulus exponentWidth program physical).applyNormalized
      (exponentProgramState modulus exponentWidth state) =
      exponentProgramState modulus exponentWidth (program.applyNormalized state) := by
  apply NormalizedVector.ext
  intro row
  change (∑ column,
    (placedExponentProgram modulus exponentWidth program physical).matrix row column *
      state ((exponentProgramBasis modulus exponentWidth).symm column)) =
    ∑ column, program.matrix ((exponentProgramBasis modulus exponentWidth).symm row) column *
      state column
  simp_rw [placedExponentProgram_matrix]
  exact (exponentProgramBasis modulus exponentWidth).symm.sum_comp
    (fun column : (Qubits (exponentWidth + exponentWidth)).Index =>
      program.matrix ((exponentProgramBasis modulus exponentWidth).symm row) column * state column)

/-- Physical and logical placement preserve every original native event in order. -/
theorem placedExponentProgram_trace (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    (placedExponentProgram modulus exponentWidth program physical).eventTrace =
      program.eventTrace := by
  rw [placedExponentProgram, UnitaryCircuit.reindex_eventTrace, UnitaryCircuit.relabel_eventTrace]

/-- Placement introduces no additional native event cost. -/
theorem placedExponentProgram_cost (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    (placedExponentProgram modulus exponentWidth program physical).eventCost =
      program.eventCost := by
  rw [placedExponentProgram, UnitaryCircuit.reindex_eventCost, UnitaryCircuit.relabel_eventCost]

/-- Placement preserves the exact original dependency-depth expression. -/
theorem placedExponentProgram_depth (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    (placedExponentProgram modulus exponentWidth program physical).eventDepth =
      program.eventDepth := by
  rw [placedExponentProgram, UnitaryCircuit.reindex_eventDepth, UnitaryCircuit.relabel_eventDepth]

/-- The placed original exponent program is an actual instruction on the owned exponent context. -/
def placedExponentCircuit (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    Circuit (exponents modulus.size (2 * exponentWidth))
      (exponents modulus.size (2 * exponentWidth)) :=
  .unitary (placedExponentProgram modulus exponentWidth program physical)
    (placedExponentProgram_physical modulus exponentWidth program physical)

/-- The actual instruction emits exactly the original native event trace. -/
theorem placedExponentCircuit_trace (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (path : (placedExponentCircuit modulus exponentWidth program physical).Path) :
    (placedExponentCircuit modulus exponentWidth program physical).eventTrace path =
      program.eventTrace := placedExponentProgram_trace modulus exponentWidth program physical

/-- The resource pool comes from the exact same actual native trace. -/
theorem placedExponentCircuit_cost (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (path : (placedExponentCircuit modulus exponentWidth program physical).Path) :
    (placedExponentCircuit modulus exponentWidth program physical).resourcePool path =
      program.eventCost := by
  rw [Circuit.resourcePool, placedExponentCircuit_trace]
  exact UnitaryCircuit.ofList_eventTrace_eq_eventCost program

/-- The actual instruction retains the original dependency depth for every duration assignment. -/
theorem placedExponentCircuit_depth (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (duration : Resource.Event .quantum → Nat)
    (path : (placedExponentCircuit modulus exponentWidth program physical).Path) :
    (placedExponentCircuit modulus exponentWidth program physical).depth duration path =
      program.evaluatedEventDepth duration := by
  change DepthExpr.depthEval duration
    (placedExponentProgram modulus exponentWidth program physical).eventDepth = _
  rw [placedExponentProgram_depth]
  rfl

universe u

/-- The unchanged original exact range preparation runs on the same owned exponent systems. -/
def placedExponentPreparation {G : Type u} [Group G] (modulus : Nat)
    (problem : FiniteCyclicDLP.KnownOrderProblem G) :
    Circuit (exponents modulus.size (2 * FiniteCyclicDLP.orderWidth problem))
      (exponents modulus.size (2 * FiniteCyclicDLP.orderWidth problem)) :=
  placedExponentCircuit modulus (FiniteCyclicDLP.orderWidth problem)
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit problem)
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit_physical_idx problem)

/-- The unchanged original pair of inverse QFTs runs on those same owned exponent systems. -/
def placedExponentReadout {G : Type u} [Group G] (modulus : Nat)
    (problem : FiniteCyclicDLP.KnownOrderProblem G) :
    Circuit (exponents modulus.size (2 * FiniteCyclicDLP.orderWidth problem))
      (exponents modulus.size (2 * FiniteCyclicDLP.orderWidth problem)) :=
  placedExponentCircuit modulus (FiniteCyclicDLP.orderWidth problem)
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentReadoutCircuit problem)
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentReadoutCircuit_physical_idx problem)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
