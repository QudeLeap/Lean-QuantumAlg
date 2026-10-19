/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Model
public import QuantumAlg.Algorithms.AmplitudeEstimation.Basic
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Components.Classical.Model.BitWord
public import QuantumAlg.Components.Oracle.AmplitudeAmplification
public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Algorithms.AmplitudeEstimation.Construction
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Construction
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.ProgramLaws
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Reindex

/-!
# Internally prepared phase and source registers

Amplitude estimation has no supplied runtime quantum input. Per-system zero
preparation creates all phase, explicit work, and source systems. The source-query
unitary performs the actual preparation, phase-estimation ladder and readout
[Lin22, appqpe.tex:189-219]. Every system remains live after Z measurement.
-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

/-- The explicit source grants and width-indexed native classical operations. -/
public abbrev model (n : Nat) : ExecutionModel :=
  .quantum AlgorithmGate.model
    (AmplitudeAmplificationSource.model n true true)
    BitWord.model .empty

/-- A source witness supplies the independently interpreted preparation and recognizer. -/
@[expose] public def sourceEnvironment {n : Nat} (E : GeneralAmplitudeEstimationInput n) :
    (model n).Environment where
  quantum := AmplitudeAmplificationSource.interpretation
    E.source.preparation E.source.good true true
  classical := ()

/-- With no classical service, agreeing on the quantum source determines the environment. -/
public lemma sourceEnvironment_eq {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (environment : (model n).Environment)
    (same : environment.quantum = AmplitudeAmplificationSource.interpretation
      E.source.preparation E.source.good true true) :
    environment = sourceEnvironment E := by
  rcases environment with ⟨quantum, classical⟩
  change quantum = _ at same
  subst quantum
  cases classical
  rfl

/-- The original empty runtime input context. -/
@[reducible] public def pre : RuntimeCtx .quantum := RuntimeCtx.empty

lemma pre_systemCount : pre.systemCount = 0 := rfl

/-- Original phase wires, any actual work position, and source wires, all dimension two. -/
abbrev runtimeLayout (t n : Nat) : QuantumLayout (t + (Elementary.helperWidth t n + n)) :=
  (QuantumSignature.qubits (t + (Elementary.helperWidth t n + n))).canonicalPlacement.layout

lemma preparationFresh : (⟨0⟩ : StorageKey) ∉ pre.keys := by decide

lemma preparationDisjoint (t n : Nat) :
    List.Disjoint (runtimeLayout t n).identities pre.physicalIdx :=
  List.disjoint_nil_right _

/-- The complete owned phase and source register after actual preparation. -/
@[implicit_reducible]
def preparedContext (t n : Nat) : RuntimeCtx .quantum :=
  pre.addOwnedLayout ⟨0⟩ (runtimeLayout t n) preparationFresh (preparationDisjoint t n)

lemma preparedContext_quantumWires (t n : Nat) :
    (preparedContext t n).quantumWires = (runtimeLayout t n).wires := by
  change (runtimeLayout t n).wires ++ [] = _
  exact List.append_nil _

lemma preparedContext_physicalIdx (t n : Nat) :
    (preparedContext t n).physicalIdx = List.range (t + (Elementary.helperWidth t n + n)) := by
  rw [RuntimeCtx.physicalIdx, preparedContext_quantumWires]
  change (List.ofFn fun index : Fin (t + (Elementary.helperWidth t n + n)) =>
    (runtimeLayout t n).wire index).map QuantumWire.identity = _
  rw [List.map_ofFn]
  exact qpeLayout_systemIdx t (Elementary.helperWidth t n + n)

/-- Exact physical-value coordinates of the newly prepared quantum register. -/
def preparedLayoutEquiv (t n : Nat) :
    (runtimeLayout t n).register.Index ≃ (preparedContext t n).register.Index :=
  Execution.preparedEmptyBasisEquiv pre ⟨0⟩ (runtimeLayout t n)
    preparationFresh (preparationDisjoint t n) pre_systemCount

/-- Canonical binary labels of those same physical values. -/
def preparedBasisEquiv (t n : Nat) :
    (preparedContext t n).register.Index ≃ (Qubits (t + (Elementary.helperWidth t n + n))).Index :=
  (preparedLayoutEquiv t n).symm.trans
    (QuantumSignature.qubitsIndexEquiv (t + (Elementary.helperWidth t n + n)))

/-- The mathematical zero state corresponding to actual per-system preparation. -/
def inputPreparation (t n : Nat) : BasisPreparation (runtimeLayout t n) :=
  ⟨(QuantumSignature.qubitsIndexEquiv (t + (Elementary.helperWidth t n + n))).symm
    (0 : Fin (2 ^ (t + (Elementary.helperWidth t n + n))))⟩

/-- The basis vector prepared on the entire actual physical register. -/
def preparedInput (t n : Nat) :
    NormalizedVector (Qubits (t + (Elementary.helperWidth t n + n))) :=
  NormalizedVector.ket (R := Qubits (t + (Elementary.helperWidth t n + n))) 0

/-- The actual preparation is exactly the source's all-zero input in its physical coordinates. -/
lemma inputPreparation_density (t n : Nat) :
    (DensityOperator.ofPure (inputPreparation t n).normalized).reindex
      (S := (preparedContext t n).register) (preparedLayoutEquiv t n) =
        (DensityOperator.ofPure (preparedInput t n)).reindex
          (S := (preparedContext t n).register) (preparedBasisEquiv t n).symm := by
  have preparedEntry (basis : (runtimeLayout t n).register.Index) :
      (inputPreparation t n).normalized basis =
        preparedInput t n
          ((QuantumSignature.qubitsIndexEquiv (t + (Elementary.helperWidth t n + n))) basis) := by
    dsimp only [preparedInput]
    change NormalizedVector.ket
      ((QuantumSignature.qubitsIndexEquiv (t + (Elementary.helperWidth t n + n))).symm
      (0 : Fin (2 ^ (t + (Elementary.helperWidth t n + n))))) basis =
        NormalizedVector.ket (R := Qubits (t + (Elementary.helperWidth t n + n)))
          (0 : Fin (2 ^ (t + (Elementary.helperWidth t n + n)))) _
    rw [NormalizedVector.ket_apply, NormalizedVector.ket_apply]
    simp only [Equiv.eq_symm_apply]
  apply DensityOperator.ext
  ext row column
  rw [DensityOperator.reindex_entry, DensityOperator.reindex_entry,
    DensityOperator.ofPure_matrix, DensityOperator.ofPure_matrix, preparedEntry, preparedEntry]
  rfl

/-- The original width reassociation preserves the complete actual native word. -/
def runtimeProgram (n : Nat) (t : Nat) :
    UnitaryCircuit AlgorithmGate.model (Elementary.oracles n)
      (runtimeLayout t n) :=
  Elementary.castCircuit (Elementary.oracles n)
    (Nat.add_assoc t (Elementary.helperWidth t n) n)
    (Elementary.program n t)

/-- The source word and the prepared runtime enumerate exactly the same physical wires. -/
lemma prepared_canonical_wires (t n : Nat) :
    (runtimeLayout t n).wires = (preparedContext t n).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires, preparedContext_quantumWires]

/-- The actual source word in the prepared runtime, retaining every wire identity and value. -/
def nativeProgram (n : Nat) (t : Nat) :
    UnitaryCircuit AlgorithmGate.model (Elementary.oracles n)
      (preparedContext t n).quantumLayout :=
  Execution.unitaryOfEqualWires (runtimeLayout t n)
    (preparedContext t n).quantumLayout (prepared_canonical_wires t n) (runtimeProgram n t)

end

end QuantumAlg.AmplitudeEstimation
