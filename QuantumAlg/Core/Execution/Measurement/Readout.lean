/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Measurement.Distribution
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Reindex
import Mathlib.Data.List.Nodup

/-!
# The actual values retained by sequential Z measurements

The ordered measurement path updates the real store through the existing
typed writes. Keys absent from the sequence retain their old values. When
the written keys are distinct, reading a measured cell obtains exactly its
wire's computational-basis value. These are storage laws used with the
separate actual-interpreter Born-fiber formula, not a replacement execution
distribution.
-/

namespace QuantumAlg.Circuit

variable {allowAllocation : Bool}

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

open Execution

variable {ctx : RuntimeCtx .quantum}

/-- A sequence of actual measurement writes preserves any cell whose key it never writes. -/
lemma writeMeasurementPath_read_unwritten (readouts : List (ZReadout ctx))
    {shape : CShape} (observed : CStorageRef ctx shape)
    (different : ∀ item ∈ readouts, item.output.key ≠ observed.key)
    (store : Store ctx) (path : (measurementSequence (allowAllocation := allowAllocation) (gates :=
      gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services)
      readouts).Path) :
    (writeMeasurementPath (allowAllocation := allowAllocation) (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) readouts store path).read
      (.storage observed) =
      store.read (.storage observed) := by
  induction readouts generalizing store with
  | nil => rfl
  | cons head tail ih =>
      change (writeMeasurementPath (allowAllocation := allowAllocation) (gates := gates) (oracles :=
        oracles)
      (operations := operations) (classicalOracles := services) tail
        (store.write head.output (.finite path.1)) path.2).read (.storage observed) = _
      rw [ih (fun item present => different item (.tail head present))]
      exact Store.read_write_other store head.output observed (.finite path.1)
        (different head (.head _))

/-- Distinct actual result cells retain the exact values measured from their named wires. -/
lemma writeMeasurementBasis_read (readouts : List (ZReadout ctx))
    (distinct : (readouts.map (fun item => item.output.key)).Nodup)
    (observed : ZReadout ctx) (present : observed ∈ readouts)
    (store : Store ctx) (basis : ctx.register.Index) :
    (writeMeasurementPath (allowAllocation := allowAllocation) (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) readouts store
      (measurementBasisPath (allowAllocation := allowAllocation) (gates := gates) (oracles :=
        oracles)
      (operations := operations) (classicalOracles := services) readouts basis)).read
      (.storage observed.output.toCStorageRef) = .finite (basis observed.wire) := by
  induction readouts generalizing store with
  | nil => cases present
  | cons head tail ih =>
      change (head.output.key :: tail.map (fun item => item.output.key)).Nodup at distinct
      obtain ⟨freshHead, distinctTail⟩ := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp present with same | inTail
      · subst observed
        change (writeMeasurementPath (allowAllocation := allowAllocation) (gates := gates) (oracles
          := oracles)
      (operations := operations) (classicalOracles := services) tail
          (store.write head.output (.finite (basis head.wire)))
          (measurementBasisPath (allowAllocation := allowAllocation) (gates := gates) (oracles :=
            oracles)
      (operations := operations) (classicalOracles := services) tail basis)).read (.storage
            head.output.toCStorageRef) = _
        rw [writeMeasurementPath_read_unwritten (allowAllocation := allowAllocation)
          (gates := gates) (oracles := oracles)
          (operations := operations) (services := services) tail head.output.toCStorageRef
          (fun item member same => freshHead (List.mem_map.mpr ⟨item, member, same⟩))]
        exact Store.read_write_same store head.output (.finite (basis head.wire))
      · exact ih distinctTail inTail (store.write head.output (.finite (basis head.wire)))

end QuantumAlg.Circuit

namespace QuantumAlg.ExecutionState

noncomputable section

/-- A diagonal observation of local wires sums every actual classical and reference block. -/
lemma diagonalSum_localMarginal {C : Type} [Fintype C] {R Reference : Register}
    (state : ExecutionState C (Register.prod R Reference)) (weight : R.Index → ℂ) :
    diagonalSum state (fun _ basis => weight basis.1) =
      ∑ basis : R.Index,
        weight basis * state.quantumMarginal.marginalLeft.matrix basis basis := by
  let entry (value : C) (basis : R.Index × Reference.Index) : ℂ :=
    (state.block value).matrix basis basis
  have marginalEntry (basis : R.Index) :
      state.quantumMarginal.marginalLeft.matrix basis basis =
        ∑ reference : Reference.Index, ∑ value : C, entry value (basis, reference) :=
    (DensityOperator.marginalLeft_matrix state.quantumMarginal basis basis).trans
      (Finset.sum_congr rfl fun reference _ =>
        Matrix.sum_apply (basis, reference) (basis, reference) Finset.univ
          (fun value : C => (state.block value).matrix))
  calc
    _ = ∑ basis : R.Index, ∑ reference : Reference.Index, ∑ value : C,
        weight basis * entry value (basis, reference) :=
      Fintype.sum_prod_type (fun basis : R.Index × Reference.Index =>
        ∑ value : C, weight basis.1 * entry value basis)
    _ = _ := by simp only [marginalEntry, Finset.mul_sum]

end

end QuantumAlg.ExecutionState

namespace QuantumAlg.DensityOperator

noncomputable section

/-- Relabeling actual local coordinates beside the reference commutes with tracing the reference. -/
public lemma reindex_prod_marginalLeft {R S Reference : Register}
    (state : DensityOperator (Register.prod R Reference)) (basisEquiv : R.Index ≃ S.Index) :
    (state.reindex (S := Register.prod S Reference)
      (basisEquiv.prodCongr (Equiv.refl Reference.Index))).marginalLeft =
        state.marginalLeft.reindex (S := S) basisEquiv := by
  apply DensityOperator.ext
  ext row column
  calc
    _ = ∑ reference : Reference.Index,
        state.matrix (basisEquiv.symm row, reference) (basisEquiv.symm column, reference) := by
      rw [marginalLeft_matrix]
      apply Finset.sum_congr rfl
      intro reference _
      rfl
    _ = _ :=
      (marginalLeft_matrix state (basisEquiv.symm row) (basisEquiv.symm column)).symm

end

end QuantumAlg.DensityOperator
