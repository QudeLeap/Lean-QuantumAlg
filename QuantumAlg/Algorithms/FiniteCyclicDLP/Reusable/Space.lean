/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Program
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Context
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Execution.Trace.Preparation
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Primitives.ZReset.Bank

/-!
# Actual live space of one reused finite-cyclic DLP bank

No round allocates another quantum system. The complete runtime retains the
one binary bank, every measured exponent sample and one shared reset cell.
The statements bound both resident and auxiliary roles on every actual path
[Sho95, source.tex:1713-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable

noncomputable section

open Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

private lemma measurement_resident {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx))
    {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
    {services : ClassicalOracleModel}
    (path : (QuantumAlg.Circuit.measurementSequence (allowAllocation := true)
      (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) readouts).Path) :
    (QuantumAlg.Circuit.measurementSequence (allowAllocation := true)
      readouts).peakResidentSpace path =
      ctx.residentSpace := by
  induction readouts with
  | nil => exact QuantumAlg.Circuit.peakResidentSpace_id path
  | cons head tail ih =>
      change SpacePool.max ctx.residentSpace
        ((QuantumAlg.Circuit.measurementSequence (allowAllocation := true)
          tail).peakResidentSpace path.2) = _
      rw [ih, SpacePool.max_self]

private lemma measurement_auxiliary {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx))
    {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
    {services : ClassicalOracleModel}
    (path : (QuantumAlg.Circuit.measurementSequence (allowAllocation := true)
      (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) readouts).Path) :
    (QuantumAlg.Circuit.measurementSequence (allowAllocation := true)
      readouts).peakAuxiliarySpace path =
      ctx.auxiliarySpace := by
  induction readouts with
  | nil => exact QuantumAlg.Circuit.peakAuxiliarySpace_id path
  | cons head tail ih =>
      change SpacePool.max ctx.auxiliarySpace
        ((QuantumAlg.Circuit.measurementSequence (allowAllocation := true)
          tail).peakAuxiliarySpace path.2) = _
      rw [ih, SpacePool.max_self]

/-- A complete measured and physically reset round has exactly its incoming resident context. -/
public lemma round_resident (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) (path : (round P slot expansion).Path) :
    (round P slot expansion).peakResidentSpace path = (context P count).residentSpace := by
  unfold round at path ⊢
  rcases path with ⟨nativePath, readoutPath, resetPath⟩
  rw [QuantumAlg.Circuit.peakResidentSpace_seq, QuantumAlg.Circuit.peakResidentSpace_seq,
    QuantumAlg.Circuit.peakResidentSpace_unitary, measurement_resident]
  have resetSpace := ZReset.Bank.zResetBank_peakResidentSpace
    (services := ClassicalFiniteGroupOracle.model G) (oracles := Binary.Oracle.model P)
    (operations := BitWord.model) (qubits P count) (scratch P count) resetPath
  change (reset P count).peakResidentSpace resetPath =
    (context P count).residentSpace at resetSpace
  rw [resetSpace, SpacePool.max_self, SpacePool.max_self]

/-- The same absence of allocation holds in the auxiliary-role ledger. -/
public lemma round_auxiliary (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) (path : (round P slot expansion).Path) :
    (round P slot expansion).peakAuxiliarySpace path = (context P count).auxiliarySpace := by
  unfold round at path ⊢
  rcases path with ⟨nativePath, readoutPath, resetPath⟩
  rw [QuantumAlg.Circuit.peakAuxiliarySpace_seq, QuantumAlg.Circuit.peakAuxiliarySpace_seq,
    QuantumAlg.Circuit.peakAuxiliarySpace_unitary, measurement_auxiliary]
  have resetSpace := ZReset.Bank.zResetBank_peakAuxiliarySpace
    (services := ClassicalFiniteGroupOracle.model G) (oracles := Binary.Oracle.model P)
    (operations := BitWord.model) (qubits P count) (scratch P count) resetPath
  change (reset P count).peakAuxiliarySpace resetPath =
    (context P count).auxiliarySpace at resetSpace
  rw [resetSpace, SpacePool.max_self, SpacePool.max_self]

omit [Fintype G] in
private lemma sample_resident_le (P : KnownOrderProblem G) (count : Nat) :
    (sampleContext P count).residentSpace ≤ (context P count).residentSpace := by
  rw [context, RuntimeCtx.residentSpace_addRetained]
  intro axis
  exact Nat.le_add_left _ _

omit [Fintype G] in
private lemma sample_auxiliary_le (P : KnownOrderProblem G) (count : Nat) :
    (sampleContext P count).auxiliarySpace ≤ (context P count).auxiliarySpace := by
  rw [context, RuntimeCtx.auxiliarySpace_addRetained]
  intro axis
  exact Nat.le_add_left _ _

/-- The actual one-time allocation prefix fits the final retained resident context. -/
public lemma initialCode_resident_le (P : KnownOrderProblem G) (count : Nat)
    (path : (initialCode P count).Path) :
    (initialCode P count).peakResidentSpace path ≤ (context P count).residentSpace := by
  refine (QuantumAlg.Circuit.peakResidentSpace_seq
    (preparationCode P) (allocationCode P count) path).trans_le (SpacePool.max_le ?_ ?_)
  · have prepared : (preparationCode P).peakResidentSpace path.1 =
        (bankContext P).residentSpace :=
      QuantumAlg.Circuit.prepare_peakResidentSpace _ _ _ _ _ path.1
    exact prepared.trans_le ((MeasurementCells.context_residentSpace_mono
      (bankContext P) 2 (Nat.zero_le (count * sampleWidth P))).trans
        (sample_resident_le P count))
  · refine (QuantumAlg.Circuit.peakResidentSpace_seq
      (MeasurementCells.allocate (model := model P) (bankContext P) 2 (count * sampleWidth P))
      (QuantumAlg.Circuit.retain (model := model P) (sampleContext P count)
        (sampleContext P count).canonicalFreshKey (.finite 2)
        (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (sampleContext P count)))
      path.2).trans_le (SpacePool.max_le ?_ ?_)
    · exact (MeasurementCells.allocate_peakResidentSpace (model := model P)
        (bankContext P) 2 (count * sampleWidth P) path.2.1).trans
          (sample_resident_le P count)
    · exact (QuantumAlg.Circuit.peakResidentSpace_retain _ _ _ path.2.2).le

/-- Auxiliary roles are bounded on those same actual prefix contexts. -/
public lemma initialCode_auxiliary_le (P : KnownOrderProblem G) (count : Nat)
    (path : (initialCode P count).Path) :
    (initialCode P count).peakAuxiliarySpace path ≤ (context P count).auxiliarySpace := by
  refine (QuantumAlg.Circuit.peakAuxiliarySpace_seq
    (preparationCode P) (allocationCode P count) path).trans_le (SpacePool.max_le ?_ ?_)
  · have prepared : (preparationCode P).peakAuxiliarySpace path.1 =
        (bankContext P).auxiliarySpace :=
      QuantumAlg.Circuit.prepare_peakAuxiliarySpace _ _ _ _ _ path.1
    exact prepared.trans_le ((MeasurementCells.context_auxiliarySpace_mono
      (bankContext P) 2 (Nat.zero_le (count * sampleWidth P))).trans
        (sample_auxiliary_le P count))
  · refine (QuantumAlg.Circuit.peakAuxiliarySpace_seq
      (MeasurementCells.allocate (model := model P) (bankContext P) 2 (count * sampleWidth P))
      (QuantumAlg.Circuit.retain (model := model P) (sampleContext P count)
        (sampleContext P count).canonicalFreshKey (.finite 2)
        (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (sampleContext P count)))
      path.2).trans_le (SpacePool.max_le ?_ ?_)
    · exact (MeasurementCells.allocate_peakAuxiliarySpace (model := model P)
        (bankContext P) 2 (count * sampleWidth P) path.2.1).trans
          (sample_auxiliary_le P count)
    · exact (QuantumAlg.Circuit.peakAuxiliarySpace_retain _ _ _ path.2.2).le

/-- The complete real sampler never exceeds its one final resident context. -/
public lemma reusableDLP_code_resident_le (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (path : (code P count expansion).Path) :
    (code P count expansion).peakResidentSpace path ≤ (context P count).residentSpace := by
  refine (QuantumAlg.Circuit.peakResidentSpace_seq
    (initialCode P count) (rounds P count expansion) path).trans_le
      (SpacePool.max_le (initialCode_resident_le P count path.1) ?_)
  exact QuantumAlg.Circuit.forRange_resident_le count (fun slot => round P slot expansion)
    (context P count).residentSpace le_rfl
    (fun slot selected => (round_resident P slot expansion selected).le) path.2

/-- Auxiliary space comes from the same complete visited contexts on the same execution path. -/
public lemma reusableDLP_code_auxiliary_le (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (path : (code P count expansion).Path) :
    (code P count expansion).peakAuxiliarySpace path ≤ (context P count).auxiliarySpace := by
  refine (QuantumAlg.Circuit.peakAuxiliarySpace_seq
    (initialCode P count) (rounds P count expansion) path).trans_le
      (SpacePool.max_le (initialCode_auxiliary_le P count path.1) ?_)
  exact QuantumAlg.Circuit.forRange_auxiliary_le count (fun slot => round P slot expansion)
    (context P count).auxiliarySpace le_rfl
    (fun slot selected => (round_auxiliary P slot expansion selected).le) path.2

omit [Fintype G] in
/-- The physical quantum ledger contains exactly the single binary bank's qubits. -/
public lemma context_qubits (P : KnownOrderProblem G) (count : Nat) :
    SpacePool.count (.quantumSystems 2) (context P count).residentSpace = bankWidth P := by
  rw [reusableDLP_context_resident]
  simp [SpacePool.count, SpacePool.ofShape, SpacePool.ofQuantumLayout,
    QuantumLayout.dimensionCount, QuantumLayout.dimensions, Binary.Oracle.layout_qubits]

end

end QuantumAlg.FiniteCyclicDLP.Reusable
