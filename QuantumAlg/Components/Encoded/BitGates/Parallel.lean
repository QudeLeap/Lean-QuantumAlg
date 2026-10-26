/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Core.Base.UnitaryCircuit.Layer.Native

/-!
# Parallel layers of independent encoded-bit gates

The independence premise checks the actual native placement, including every
control wire. The compiled layer retains the original ordered word's full
operator and native ledger; only its genuine dependency structure changes.
-/

namespace QuantumAlg.EncodedBit.GateSpec

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- The gate specification's actual native application on the supplied physical bank. -/
def nativeApplication (physical : QubitLayout encoding.width) (gate : GateSpec encoding) :
    GateModel.Application AlgorithmGate.model physical.toQuantum :=
  QubitPrimitive.nativeApplication physical gate.primitive

/-- All control and target positions of the actual native occurrence. -/
def physicalSupport (physical : QubitLayout encoding.width) (gate : GateSpec encoding) :
    Finset (Fin encoding.width) := (nativeApplication physical gate).embedding.selection

/-- An actual X instruction touches exactly its one target position. -/
lemma physicalSupport_x (physical : QubitLayout encoding.width) (target : EncodedBit encoding) :
    physicalSupport physical (.x target) = {target.wire} := by
  ext index
  unfold physicalSupport
  rw [QuantumLayout.Embedding.selection, Finset.mem_map]
  simp only [Finset.mem_univ, true_and]
  change (∃ _ : Fin 1, target.wire = index) ↔ _
  simp only [exists_const, Finset.mem_singleton]
  exact eq_comm

/-- A CNOT's actual support includes its control and its target. -/
lemma physicalSupport_cnot (physical : QubitLayout encoding.width)
    (control target : EncodedBit encoding) (different : control.wire ≠ target.wire) :
    physicalSupport physical (.cnot control target different) = {control.wire, target.wire} := by
  ext index
  unfold physicalSupport
  rw [QuantumLayout.Embedding.selection, Finset.mem_map]
  simp only [Finset.mem_univ, true_and]
  change (∃ j : Fin 2, ![control.wire, target.wire] j = index) ↔ _
  simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Finset.mem_insert, Finset.mem_singleton]
  exact or_congr eq_comm eq_comm

/-- Compile one actual parallel node for a list of physically independent instructions. -/
def parallelProgramList (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (gates : List (GateSpec encoding))
    (separate : gates.Pairwise (fun first second =>
      Disjoint (physicalSupport physical first) (physicalSupport physical second))) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  UnitaryCircuit.nativeLayer (gates.map (nativeApplication physical))
    (List.pairwise_map.mpr separate)

private lemma nativeApplication_event (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (gate : GateSpec encoding) :
    (Resource.Event.gate (nativeApplication physical gate).coordinate :
      Resource.Event (.quantum AlgorithmGate.model oracles)) = event oracles gate := by
  cases gate <;> rfl

/-- The actual parallel word retains the source instruction order in its event ledger. -/
lemma parallelProgramList_eventTrace (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (gates : List (GateSpec encoding))
    (separate : gates.Pairwise (fun first second =>
      Disjoint (physicalSupport physical first) (physicalSupport physical second))) :
    (parallelProgramList physical oracles gates separate).eventTrace =
      (programList physical oracles gates).eventTrace := by
  rw [parallelProgramList, UnitaryCircuit.nativeLayer_eventTrace, programList_eventTrace]
  simp only [List.map_map, Function.comp_def, nativeApplication_event]

/-- Native counts are unchanged by actual parallel construction. -/
lemma parallelProgramList_eventCost (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (gates : List (GateSpec encoding))
    (separate : gates.Pairwise (fun first second =>
      Disjoint (physicalSupport physical first) (physicalSupport physical second))) :
    (parallelProgramList physical oracles gates separate).eventCost =
      (programList physical oracles gates).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    parallelProgramList_eventTrace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]

private lemma serial_matrix (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (gates : List (GateSpec encoding)) (environment : oracles.Interpretation) :
    (programList physical oracles gates).matrix environment =
      ((gates.map fun gate =>
        (gate.program physical oracles).matrix environment).reverse).prod := by
  induction gates with
  | nil => rfl
  | cons first rest ih =>
      simp only [programList, UnitaryCircuit.seq_matrix, List.map_cons, List.reverse_cons,
        List.prod_append, List.prod_cons, List.prod_nil, mul_one, ih]

/-- Splitting a source word preserves the actual execution order of both parts. -/
lemma gateSpec_programList_append_matrix (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (first second : List (GateSpec encoding))
    (environment : oracles.Interpretation) :
    (programList physical oracles (first ++ second)).matrix environment =
      (programList physical oracles second).matrix environment *
        (programList physical oracles first).matrix environment := by
  induction first with
  | nil => simp [programList]
  | cons gate rest ih =>
      simp only [List.cons_append, programList, UnitaryCircuit.seq_matrix, ih, mul_assoc]

/-- All amplitudes and relative phases agree with the source word on the full bank. -/
lemma parallelProgramList_matrix (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (gates : List (GateSpec encoding))
    (separate : gates.Pairwise (fun first second =>
      Disjoint (physicalSupport physical first) (physicalSupport physical second)))
    (environment : oracles.Interpretation) :
    (parallelProgramList physical oracles gates separate).matrix environment =
      (programList physical oracles gates).matrix environment := by
  rw [parallelProgramList, UnitaryCircuit.nativeLayer_matrix, serial_matrix]
  simp only [List.map_map, Function.comp_def]
  rfl

/-- Parallel scheduling preserves the same encoded all-input action. -/
lemma parallelProgramList_realizes (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (gates : List (GateSpec encoding))
    (separate : gates.Pairwise (fun first second =>
      Disjoint (physicalSupport physical first) (physicalSupport physical second)))
    (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding (parallelProgramList physical oracles gates separate)
      environment (stepList gates) where
  apply_encoded_ket := by
    intro input
    simpa only [UnitaryCircuit.applyNormalized, parallelProgramList_matrix] using
      (realizesList physical oracles gates environment).apply_encoded_ket input

/-- An empty native layer is idle; every nonempty independent native layer takes one step. -/
lemma parallelProgramList_quantumTime (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (gates : List (GateSpec encoding))
    (separate : gates.Pairwise (fun first second =>
      Disjoint (physicalSupport physical first) (physicalSupport physical second))) :
    (parallelProgramList physical oracles gates separate).evaluatedEventDepth
      Resource.Event.quantumDuration = if gates = [] then 0 else 1 := by
  rw [parallelProgramList, UnitaryCircuit.nativeLayer_quantumTime]
  simp only [List.map_eq_nil_iff]

/-- Unit event durations give the same single-layer depth for these native instructions. -/
lemma parallelProgramList_unitDepth (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (gates : List (GateSpec encoding))
    (separate : gates.Pairwise (fun first second =>
      Disjoint (physicalSupport physical first) (physicalSupport physical second))) :
    (parallelProgramList physical oracles gates separate).evaluatedEventDepth
      (fun _ => 1) = if gates = [] then 0 else 1 := by
  rw [parallelProgramList, UnitaryCircuit.nativeLayer_unitDepth]
  simp only [List.map_eq_nil_iff]

end

end QuantumAlg.EncodedBit.GateSpec
