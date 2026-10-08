/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Born
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling
import all QuantumAlg.Core.Execution.Preparation.Seed
import all QuantumAlg.Core.Execution.Prepared.LayoutAgreement
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Unitary.StoreFilter
import all QuantumAlg.Core.Execution.Store.Blocks
import all QuantumAlg.Core.Execution.Measured.FeedForward
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# Complete stored-reference law of actual intrinsic ECDLP sampling

Real zero allocation establishes the seed for every complete store, including
arbitrary off-diagonal external-reference entries. The actual native word
has the independent source amplitudes. Actual measurement writes select the
same full matrix blocks; borrowed input/reference observations are restored.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling

noncomputable section

open QuantumAlg.Execution

attribute [local instance] Classical.decEq

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private theorem prepared_zero (I : ECDLPInstance E) :
    preparedEmptyBasisEquiv (pre I) (pre I).canonicalFreshKey (layout I)
        (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (pre I)) (bankDisjoint I) (by rfl)
        (layout I).zeroLabel = (bankContext I).quantumLayout.zeroLabel := by
  have wires : (layout I).wires = (bankContext I).quantumLayout.wires :=
    ((bankContext I).quantumLayout_wires.trans (bankContext_wires I)).symm
  rw [preparedEmptyBasisEquiv_eq_basisOfEqualWires
    (pre I) (pre I).canonicalFreshKey (layout I)
    (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (pre I)) (bankDisjoint I) (by rfl) wires]
  funext target
  obtain ⟨index, rfl⟩ :=
    (positionsOfEqualWires (layout I) (bankContext I).quantumLayout wires).surjective target
  apply Fin.ext
  exact basisOfEqualWires_value (layout I) (bankContext I).quantumLayout wires
    (layout I).zeroLabel index

private theorem cells_zero (ctx : RuntimeCtx .quantum) (count : Nat) :
    MeasurementCells.basisEquiv ctx 2 count ctx.quantumLayout.zeroLabel =
      (MeasurementCells.context ctx 2 count).quantumLayout.zeroLabel := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

/-- Real allocation establishes the complete zero seed without an input-state premise. -/
private theorem initialCode_seeded (I : ECDLPInstance E) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre I) Reference ((executionModel I A).HiddenState × History)) :
    BasisSeeded.Holds (post I).quantumLayout.zeroLabel
      ((initialCode I A).execute Reference state) := by
  have prepared := Circuit.prepareZero_empty_seeded
    (gates := AlgorithmGate.model) (oracles := model I A)
    (operations := BitWord.model) (services := ClassicalOracleModel.empty)
    (pre I).canonicalFreshKey (layout I) (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (pre I))
    (bankDisjoint I) (by rfl) state
  change BasisSeeded.Holds
    (preparedEmptyBasisEquiv (pre I) (pre I).canonicalFreshKey (layout I)
      (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (pre I)) (bankDisjoint I) (by rfl)
      (layout I).zeroLabel)
    ((preparationCode I A).execute Reference state) at prepared
  rw [prepared_zero] at prepared
  have allocated := MeasurementCells.allocate_seeded (model := executionModel I A)
    (bankContext I) 2 (sampleWidth I) (bankContext I).quantumLayout.zeroLabel
    ((preparationCode I A).execute Reference state) prepared
  rw [cells_zero] at allocated
  exact BasisSeeded.seq (preparationCode I A) (allocationCode I A)
    (post I).quantumLayout.zeroLabel state allocated

/-- Equal-wire transport takes the runtime zero back to the same source zero. -/
public theorem basisEquiv_zero (I : ECDLPInstance E) :
    basisEquiv I (post I).quantumLayout.zeroLabel = (layout I).zeroLabel := by
  let forward := basisOfEqualWires (layout I) (post I).quantumLayout (sourceWires I)
  have mapped : forward (layout I).zeroLabel = (post I).quantumLayout.zeroLabel := by
    funext target
    obtain ⟨index, rfl⟩ := (wireEquiv I).surjective target
    apply Fin.ext
    exact basisOfEqualWires_value (layout I) (post I).quantumLayout (sourceWires I)
      (layout I).zeroLabel index
  change forward.symm _ = _
  rw [← mapped, Equiv.symm_apply_apply]

/-- The runtime native word has exactly the independent source state's zero amplitudes. -/
public theorem nativeProgram_zero_amplitude (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (row : (post I).register.Index) :
    (nativeProgram I A expansion).matrix row (post I).quantumLayout.zeroLabel =
      sourceState I A ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I))
        (basisEquiv I row)) := by
  rw [nativeProgram, Execution.unitaryOfEqualWires_matrix]
  change ((initializer I A).seq (circuit I A expansion)).matrix
    (basisEquiv I row) (basisEquiv I (post I).quantumLayout.zeroLabel) = _
  rw [basisEquiv_zero, initializedCircuit_zero_amplitude]

/-- Actual coherent execution keeps every stored reference coefficient and both source phases. -/
private theorem nativeProgram_store_entry (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (post I) Reference ((executionModel I A).HiddenState × History))
    (seeded : BasisSeeded.Holds (post I).quantumLayout.zeroLabel state)
    (stored : Store (post I)) (left right : (post I).register.Index)
    (leftRef rightRef : Reference.Index) :
    (((Circuit.unitary (operations := BitWord.model)
      (classicalOracles := ClassicalOracleModel.empty)
      (nativeProgram I A expansion)).execute Reference state).filterClassical
        (fun record => record.1 = stored)).quantumMarginal.matrix
          (left, leftRef) (right, rightRef) =
      sourceState I A ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I))
        (basisEquiv I left)) *
      (state.filterClassical (fun record => record.1 = stored)).quantumMarginal.matrix
        ((post I).quantumLayout.zeroLabel, leftRef)
        ((post I).quantumLayout.zeroLabel, rightRef) *
      star (sourceState I A ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I))
        (basisEquiv I right))) := by
  rw [Circuit.unitary_store_filter (operations := BitWord.model)
    (services := ClassicalOracleModel.empty) (nativeProgram I A expansion) state
    (fun original => original = stored)]
  exact (BasisSeeded.unitary_entry (post I).quantumLayout.zeroLabel state seeded
    (nativeProgram I A expansion).matrix stored left right leftRef rightRef).trans
    (congrArg₂ (fun first second : ℂ => first *
      (state.filterClassical (fun record => record.1 = stored)).quantumMarginal.matrix
        ((post I).quantumLayout.zeroLabel, leftRef)
        ((post I).quantumLayout.zeroLabel, rightRef) * star second)
      (nativeProgram_zero_amplitude I A expansion left)
      (nativeProgram_zero_amplitude I A expansion right))

/-- The real preparation-to-query prefix has the source state in every complete store block. -/
public theorem beforeMeasurement_store_entry (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre I) Reference ((executionModel I A).HiddenState × History))
    (stored : Store (post I)) (left right : (post I).register.Index)
    (leftRef rightRef : Reference.Index) :
    ((((beforeMeasurement I A expansion).execute Reference state).mapClassical
      (fun record => record.1)).block stored).matrix
        (left, leftRef) (right, rightRef) =
      sourceState I A ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I))
        (basisEquiv I left)) *
      ((((initialCode I A).execute Reference state).mapClassical
        (fun record => record.1)).block stored).matrix
          ((post I).quantumLayout.zeroLabel, leftRef)
          ((post I).quantumLayout.zeroLabel, rightRef) *
      star (sourceState I A ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I))
        (basisEquiv I right))) := by
  rw [BasisSeeded.store_matrix, BasisSeeded.store_matrix,
    beforeMeasurement, Circuit.seq_store_marginal]
  exact nativeProgram_store_entry I A expansion ((initialCode I A).execute Reference state)
    (initialCode_seeded I A state) stored left right leftRef rightRef

/-- The complete sampler restores both borrowed point inputs jointly with the reference. -/
public theorem run_restoresBorrowed (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) {Reference : Register}
    (original : OracleInput (executionModel I A).classicalOracles (pre I) Reference) :
    (run I A expansion).RestoresBorrowed original := by
  apply AlgorithmRun.restoresBorrowed_of_circuit
  intro reference history _ state
  exact Circuit.borrowedRestored_of_noBorrowedQuantum (code I A expansion)
    (by rfl) reference state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling
