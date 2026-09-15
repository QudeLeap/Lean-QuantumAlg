/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Framing
import all QuantumAlg.Core.Execution.State.Coordinates

/-!
# Prescribed public inputs in the original complete quantum input

The original public problem fixes the borrowed base and target values before
execution. Joining those actual input cells preserves every original quantum
input store. The complete quantum wire list is unchanged, so its exact basis
correspondence retains arbitrary quantum-reference coherences and input mass.

These definitions prescribe the initial input to the real framed circuit.
They emit no instruction and never add public data at an intermediate state.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement FiniteCyclicDLP

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat)

/-- Read the original public base already present in the initial framed context. -/
def initialBaseRef : CInputRef (before E exponentWidth)
    (Canonical.Runtime.Context.PointShape E) :=
  inputRight (before_disjoint E exponentWidth) (baseRef E exponentWidth)

/-- Read the original public target already present in the initial framed context. -/
def initialTargetRef : CInputRef (before E exponentWidth)
    (Canonical.Runtime.Context.PointShape E) :=
  inputRight (before_disjoint E exponentWidth) (targetRef E exponentWidth)

/-- The public problem supplies both borrowed input values alongside the original quantum input. -/
def initialStore (problem : KnownOrderProblem E.GroupPoint)
    (original : Store (Allocation.before p.size (2 * exponentWidth))) :
    Store (before E exponentWidth) :=
  join (before_disjoint E exponentWidth) original (store E exponentWidth problem)

/-- Every original structural quantum-input read keeps its exact original value. -/
theorem initialStore_read (problem : KnownOrderProblem E.GroupPoint)
    (original : Store (Allocation.before p.size (2 * exponentWidth)))
    {shape : CShape} (input : CInputRef (Allocation.before p.size (2 * exponentWidth)) shape) :
    (initialStore E exponentWidth problem original).read
      (inputLeft (before_disjoint E exponentWidth) input) = original.read input :=
  contextUnion_read_join_left _ _ _ input

/-- The initial base is exactly the original identity-inclusive public point value. -/
theorem initialStore_base (problem : KnownOrderProblem E.GroupPoint)
    (original : Store (Allocation.before p.size (2 * exponentWidth))) :
    (initialStore E exponentWidth problem original).read (initialBaseRef E exponentWidth) =
      Canonical.Runtime.Context.pointValue E problem.generator.toMathlib :=
  (contextUnion_read_join_right _ _ _ (baseRef E exponentWidth)).trans
    (store_base E exponentWidth problem)

/-- The initial target is exactly the original identity-inclusive public point value. -/
theorem initialStore_target (problem : KnownOrderProblem E.GroupPoint)
    (original : Store (Allocation.before p.size (2 * exponentWidth))) :
    (initialStore E exponentWidth problem original).read (initialTargetRef E exponentWidth) =
      Canonical.Runtime.Context.pointValue E problem.target.toMathlib :=
  (contextUnion_read_join_right _ _ _ (targetRef E exponentWidth)).trans
    (store_target E exponentWidth problem)

/-- Original base representation follows from its prescribed input, without a caller promise. -/
theorem initialStore_base_represents (problem : KnownOrderProblem E.GroupPoint)
    (original : Store (Allocation.before p.size (2 * exponentWidth))) :
    ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
      ((initialStore E exponentWidth problem original).read (initialBaseRef E exponentWidth))
      problem.generator.toMathlib := by
  rw [initialStore_base]
  exact publicPoint_represents E problem.generator

/-- Original target representation follows from its prescribed input, without a caller promise. -/
theorem initialStore_target_represents (problem : KnownOrderProblem E.GroupPoint)
    (original : Store (Allocation.before p.size (2 * exponentWidth))) :
    ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
      ((initialStore E exponentWidth problem original).read (initialTargetRef E exponentWidth))
      problem.target.toMathlib := by
  rw [initialStore_target]
  exact publicPoint_represents E problem.target

/-- Prescribing the fixed public inputs does not identify distinct original input stores. -/
theorem initialStore_injective (problem : KnownOrderProblem E.GroupPoint) :
    Function.Injective (initialStore E exponentWidth problem) := by
  intro first second same
  have splitSame := congrArg (fun value => (split (before_disjoint E exponentWidth) value).1)
    same
  simpa only [initialStore, split_join_store] using splitSame

/-- The entire original quantum input wire list keeps its identities, dimensions and order. -/
theorem before_quantumWires : (before E exponentWidth).quantumWires =
    (Allocation.before p.size (2 * exponentWidth)).quantumWires := by
  rw [before, RuntimeCtx.quantumWires_disjointUnion, frame_quantumWires, List.append_nil]

/-- The complete final original quantum wire list remains beside the two classical inputs. -/
theorem terminal_quantumWires : (terminal E exponentWidth).quantumWires =
    (exponentMeasurementContext p exponentWidth).quantumWires := by
  rw [terminal, RuntimeCtx.quantumWires_disjointUnion, frame_quantumWires, List.append_nil]

/-- Initial resident space includes exactly both original borrowed point shapes. -/
theorem before_resident : (before E exponentWidth).residentSpace =
    (Allocation.before p.size (2 * exponentWidth)).residentSpace +
      2 • SpacePool.ofShape (Canonical.Runtime.Context.PointShape E) := by
  rw [before, RuntimeCtx.residentSpace_disjointUnion, frame_resident]

/-- Final resident space still includes both borrowed point inputs and every original result. -/
theorem terminal_resident : (terminal E exponentWidth).residentSpace =
    (exponentMeasurementContext p exponentWidth).residentSpace +
      2 • SpacePool.ofShape (Canonical.Runtime.Context.PointShape E) := by
  rw [terminal, RuntimeCtx.residentSpace_disjointUnion, frame_resident]

/-- The borrowed public inputs add no owned auxiliary space to the original input. -/
theorem before_auxiliary : (before E exponentWidth).auxiliarySpace =
    (Allocation.before p.size (2 * exponentWidth)).auxiliarySpace := by
  rw [before, RuntimeCtx.auxiliarySpace_disjointUnion, frame_auxiliary, add_zero]

/-- The same borrowed roles add no owned auxiliary space to the complete terminal context. -/
theorem terminal_auxiliary : (terminal E exponentWidth).auxiliarySpace =
    (exponentMeasurementContext p exponentWidth).auxiliarySpace := by
  rw [terminal, RuntimeCtx.auxiliarySpace_disjointUnion, frame_auxiliary, add_zero]

/-- Exact original quantum coordinates in the initial context with the two public inputs. -/
def beforeBasisEquiv : (Allocation.before p.size (2 * exponentWidth)).register.Index ≃
    (before E exponentWidth).register.Index :=
  basisOfEqualWires _ _ (by
    rw [RuntimeCtx.quantumLayout_wires, RuntimeCtx.quantumLayout_wires, before_quantumWires])

/-- Every original quantum coordinate remains joint with the same arbitrary external reference. -/
def beforeJointBasisEquiv (Reference : Register) :
    (Register.prod (Allocation.before p.size (2 * exponentWidth)).register Reference).Index ≃
      (Register.prod (before E exponentWidth).register Reference).Index :=
  (beforeBasisEquiv E exponentWidth).prodCongr (Equiv.refl Reference.Index)

/-- Prescribe both original public inputs without changing the original joint quantum input. -/
def initialState (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (original : ExecutionState (Store (Allocation.before p.size (2 * exponentWidth)))
      (Register.prod (Allocation.before p.size (2 * exponentWidth)).register Reference)) :
    ExecutionState (Store (before E exponentWidth))
      (Register.prod (before E exponentWidth).register Reference) :=
  (original.mapClassical (initialStore E exponentWidth problem)).reindex
    (beforeJointBasisEquiv E exponentWidth Reference)

/-- Supplying the original public input values preserves all incoming probability mass. -/
theorem initialState_mass (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (original : ExecutionState (Store (Allocation.before p.size (2 * exponentWidth)))
      (Register.prod (Allocation.before p.size (2 * exponentWidth)).register Reference)) :
    (initialState E exponentWidth problem original).mass = original.mass := by
  rw [initialState, ExecutionState.reindex_mass, ExecutionState.mapClassical_mass]

/-- Each actual prescribed classical block retains its complete original reference matrix. -/
theorem initialState_block_entry (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (original : ExecutionState (Store (Allocation.before p.size (2 * exponentWidth)))
      (Register.prod (Allocation.before p.size (2 * exponentWidth)).register Reference))
    (value : Store (Allocation.before p.size (2 * exponentWidth)))
    (row column :
      (Register.prod (Allocation.before p.size (2 * exponentWidth)).register Reference).Index) :
    ((initialState E exponentWidth problem original).block
      (initialStore E exponentWidth problem value)).matrix
        (beforeJointBasisEquiv E exponentWidth Reference row)
        (beforeJointBasisEquiv E exponentWidth Reference column) =
          (original.block value).matrix row column := by
  rw [initialState, ExecutionState.reindex_block_entry,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  simp only [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply, Matrix.ite_apply,
    Matrix.zero_apply]
  simp only [(initialStore_injective E exponentWidth problem).eq_iff]
  simp

/-- The complete quantum marginal keeps every original coherence with the external reference. -/
theorem initialState_quantumMarginal (problem : KnownOrderProblem E.GroupPoint)
    {Reference : Register}
    (original : ExecutionState (Store (Allocation.before p.size (2 * exponentWidth)))
      (Register.prod (Allocation.before p.size (2 * exponentWidth)).register Reference)) :
    (initialState E exponentWidth problem original).quantumMarginal =
      original.quantumMarginal.reindex (beforeJointBasisEquiv E exponentWidth Reference) := by
  apply DensityOperator.ext
  ext row column
  have same := congrArg
    (fun density : DensityOperator
        (Register.prod (Allocation.before p.size (2 * exponentWidth)).register Reference) =>
      density.matrix ((beforeJointBasisEquiv E exponentWidth Reference).symm row)
        ((beforeJointBasisEquiv E exponentWidth Reference).symm column))
    (ExecutionState.mapClassical_quantumMarginal original (initialStore E exponentWidth problem))
  simpa only [initialState, ExecutionState.quantumMarginal, ExecutionState.reindex,
    DensityOperator.reindex, Matrix.submatrix_apply, Matrix.sum_apply] using same

/-- A normalized original input supplies a normalized actual input with both public values. -/
def initialInput (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * exponentWidth)) Reference) :
    Input (before E exponentWidth) Reference where
  state := initialState E exponentWidth problem original.state
  normalized := (initialState_mass E exponentWidth problem original.state).trans original.normalized

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput
