/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.AmplitudeAmplification.Circuit
import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace
import all QuantumAlg.Core.Base.UnitaryCircuit.IdleSuffix
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# The actual source-query amplitude-amplification program

One initial preparation query is followed by k occurrences of the source
recognizer, inverse preparation, elementary positive zero reflection, and
preparation. The selected work suffix remains part of the full register.
The program is defined at every width and iteration count.
-/

namespace QuantumAlg.AmplitudeAmplification.Native

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

private theorem preparation_within {n : Nat} (U : UnitaryOperator (Qubits n)) :
    (AmplitudeAmplificationSource.Circuit.preparation 0 U).physical_idx ⊆ List.range n := by
  simpa only [AmplitudeAmplificationSource.Circuit.preparation_physical_idx,
    List.range_eq_range'] using (List.Subset.refl (List.range' 0 n))

private theorem inverse_within {n : Nat} (U : UnitaryOperator (Qubits n)) :
    (AmplitudeAmplificationSource.Circuit.inversePreparation 0 U).physical_idx ⊆
      List.range n := by
  simpa only [AmplitudeAmplificationSource.Circuit.inversePreparation_physical_idx,
    List.range_eq_range'] using (List.Subset.refl (List.range' 0 n))

private theorem good_within {n : Nat} (good : NormalizedVector (Qubits n)) :
    (AmplitudeAmplificationSource.Circuit.goodReflection 0 good).physical_idx ⊆ List.range n := by
  simpa only [AmplitudeAmplificationSource.Circuit.goodReflection_physical_idx,
    List.range_eq_range'] using (List.Subset.refl (List.range' 0 n))

/-- A source preparation query beside every actual work value. -/
def preparation {n : Nat} (U : UnitaryOperator (Qubits n)) (k : Nat) :
    UnitaryCircuit (Qubits (totalQubits n k)) :=
  (AmplitudeAmplificationSource.Circuit.preparation 0 U).idleSuffix
    (preparation_within U) (helperWidth n k)

/-- An inverse-source query on the same original positions. -/
def inversePreparation {n : Nat} (U : UnitaryOperator (Qubits n)) (k : Nat) :
    UnitaryCircuit (Qubits (totalQubits n k)) :=
  (AmplitudeAmplificationSource.Circuit.inversePreparation 0 U).idleSuffix
    (inverse_within U) (helperWidth n k)

/-- The source's ordinary good-state phase-reflection query. -/
def goodReflection {n : Nat} (good : NormalizedVector (Qubits n)) (k : Nat) :
    UnitaryCircuit (Qubits (totalQubits n k)) :=
  (AmplitudeAmplificationSource.Circuit.goodReflection 0 good).idleSuffix
    (good_within good) (helperWidth n k)

/-- Literal execution order of one source iterate, including the elementary S0 sign. -/
def step {n : Nat} (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n))
    (k : Nat) (nonzero : k ≠ 0) : UnitaryCircuit (Qubits (totalQubits n k)) :=
  (((goodReflection good k).seq (inversePreparation U k)).seq
    (ZeroReflection.Workspace.reflection n k nonzero)).seq (preparation U k)

/-- Empty schedules contain the initial source preparation and no work system. -/
def body {n : Nat} (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n))
    (k : Nat) : UnitaryCircuit (Qubits (totalQubits n k)) :=
  if zero : k = 0 then preparation U k
  else (preparation U k).seq (UnitaryCircuit.iterate k (step U good k zero))

/-- The complete unitary retains each live physical position in canonical order. -/
def program {n : Nat} (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n))
    (k : Nat) : UnitaryCircuit (Qubits (totalQubits n k)) :=
  (body U good k).seq (UnitaryCircuit.identity (Qubits (totalQubits n k))
    (List.range (totalQubits n k)) List.nodup_range)

theorem preparation_contained {n : Nat} (U : UnitaryOperator (Qubits n)) (k : Nat) :
    (preparation U k).physical_idx ⊆ List.range (totalQubits n k) :=
  UnitaryCircuit.idleSuffix_physical_idx_subset_range _ _ _

theorem inversePreparation_contained {n : Nat} (U : UnitaryOperator (Qubits n)) (k : Nat) :
    (inversePreparation U k).physical_idx ⊆ List.range (totalQubits n k) :=
  UnitaryCircuit.idleSuffix_physical_idx_subset_range _ _ _

theorem goodReflection_contained {n : Nat} (good : NormalizedVector (Qubits n)) (k : Nat) :
    (goodReflection good k).physical_idx ⊆ List.range (totalQubits n k) :=
  UnitaryCircuit.idleSuffix_physical_idx_subset_range _ _ _

theorem step_contained {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) (nonzero : k ≠ 0) :
    (step U good k nonzero).physical_idx ⊆ List.range (totalQubits n k) :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (UnitaryCircuit.seq_physical_idx_subset _ _
      (UnitaryCircuit.seq_physical_idx_subset _ _ (goodReflection_contained good k)
        (inversePreparation_contained U k))
      (ZeroReflection.Workspace.reflection_contained n k nonzero))
    (preparation_contained U k)

theorem body_contained {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    (body U good k).physical_idx ⊆ List.range (totalQubits n k) := by
  unfold body
  split
  · exact preparation_contained U k
  · exact UnitaryCircuit.seq_physical_idx_subset _ _ (preparation_contained U k)
      (UnitaryCircuit.iterate_physical_idx_subset _ _ (step_contained U good k _))

theorem program_physical_idx {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    (program U good k).physical_idx = List.range (totalQubits n k) :=
  UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset _ _ (body_contained U good k)

end

end QuantumAlg.AmplitudeAmplification.Native
