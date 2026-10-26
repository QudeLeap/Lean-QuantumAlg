/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.FTQC.CliffordLayers
import all QuantumAlg.Primitives.FTQC.CliffordLayers
import all QuantumAlg.Analysis.FTQC.CliffordT.Word
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Parallel
import all QuantumAlg.Core.Base.Gate.Placement.Construction
import all QuantumAlg.Components.GateModel.CliffordT
import Mathlib.Tactic

/-! # Accounting for the actual strict-model parallel layers -/

namespace QuantumAlg.FTQC

open CliffordT UnitaryCircuit

noncomputable section

private lemma sequenceList_cost {oracles : OracleModel} {n : Nat}
    (cs : List (CliffordCircuit oracles n)) (start : CliffordCircuit oracles n) :
    (sequenceList start cs).eventCost = start.eventCost + (cs.map eventCost).sum := by
  induction cs generalizing start with
  | nil => simp [sequenceList]
  | cons circuit cs ih =>
      change (sequenceList (seq start circuit) cs).eventCost = _
      rw [ih, seq_eventCost]
      simp only [List.map_cons, List.sum_cons, add_assoc]

@[simp] public lemma blocks_eventCost {oracles : OracleModel} {n : Nat}
    (cs : List (CliffordCircuit oracles n)) :
    (blocks cs).eventCost = (cs.map eventCost).sum := by
  rw [blocks, sequenceList_cost, identity_eventCost, zero_add]

@[simp] public lemma layer2_eventCost (oracles : OracleModel) (a b : List Letter) :
    (layer2 oracles a b).eventCost = (ofWord oracles a).eventCost +
      (ofWord oracles b).eventCost := parallelBinary_eventCost _ _

@[simp] public lemma layer3_eventCost (oracles : OracleModel) (a b c : List Letter) :
    (layer3 oracles a b c).eventCost = (ofWord oracles a).eventCost +
      (ofWord oracles b).eventCost + (ofWord oracles c).eventCost := by
  rw [layer3, parallelBinary_eventCost, layer2_eventCost]

@[simp] public lemma cx_eventCost (oracles : OracleModel) {n : Nat}
    (a b : Fin n) (h : a ≠ b) :
    (cx oracles a b h).eventCost =
      ResourcePool.singleton (model := .quantum CliffordTGate.model oracles) (.gate .cnot) := by
  rw [cx, native_eventCost, GateModel.Application.gateApplication_ofPositions_coordinate,
    CliffordTGate.coordinate_identity]

private lemma sequenceList_depth {oracles : OracleModel} {n : Nat}
    (duration : Resource.Event (.quantum CliffordTGate.model oracles) → Nat)
    (cs : List (CliffordCircuit oracles n)) (start : CliffordCircuit oracles n) :
    (sequenceList start cs).evaluatedEventDepth duration =
      start.evaluatedEventDepth duration + (cs.map (evaluatedEventDepth duration)).sum := by
  induction cs generalizing start with
  | nil => simp [sequenceList]
  | cons circuit cs ih =>
      change (sequenceList (seq start circuit) cs).evaluatedEventDepth duration = _
      rw [ih, evaluatedEventDepth_seq]
      simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

@[simp] public lemma blocks_evaluatedEventDepth {oracles : OracleModel} {n : Nat}
    (duration : Resource.Event (.quantum CliffordTGate.model oracles) → Nat)
    (cs : List (CliffordCircuit oracles n)) :
    (blocks cs).evaluatedEventDepth duration = (cs.map (evaluatedEventDepth duration)).sum := by
  rw [blocks, sequenceList_depth, evaluatedEventDepth_identity, Nat.zero_add]

@[simp] public lemma layer2_evaluatedEventDepth (oracles : OracleModel) (a b : List Letter)
    (duration : Resource.Event (.quantum CliffordTGate.model oracles) → Nat) :
    (layer2 oracles a b).evaluatedEventDepth duration =
      max ((ofWord oracles a).evaluatedEventDepth duration)
        ((ofWord oracles b).evaluatedEventDepth duration) :=
  parallelBinary_evaluatedEventDepth _ _ _

@[simp] public lemma layer3_evaluatedEventDepth (oracles : OracleModel) (a b c : List Letter)
    (duration : Resource.Event (.quantum CliffordTGate.model oracles) → Nat) :
    (layer3 oracles a b c).evaluatedEventDepth duration =
      max (max ((ofWord oracles a).evaluatedEventDepth duration)
        ((ofWord oracles b).evaluatedEventDepth duration))
        ((ofWord oracles c).evaluatedEventDepth duration) := by
  rw [layer3, parallelBinary_evaluatedEventDepth, layer2_evaluatedEventDepth]

@[simp] public lemma cx_evaluatedEventDepth (oracles : OracleModel) {n : Nat}
    (a b : Fin n) (h : a ≠ b)
    (duration : Resource.Event (.quantum CliffordTGate.model oracles) → Nat) :
    (cx oracles a b h).evaluatedEventDepth duration = duration (.gate .cnot) := by
  rw [cx, evaluatedEventDepth_native,
    GateModel.Application.gateApplication_ofPositions_coordinate, CliffordTGate.coordinate_identity]

@[simp] public lemma letter_evaluatedEventDepth (oracles : OracleModel) (letter : Letter)
    (duration : Resource.Event (.quantum CliffordTGate.model oracles) → Nat) :
    (letter.circuit oracles).evaluatedEventDepth duration =
      duration (letter.event oracles) := by
  cases letter <;> rfl

end
end QuantumAlg.FTQC
