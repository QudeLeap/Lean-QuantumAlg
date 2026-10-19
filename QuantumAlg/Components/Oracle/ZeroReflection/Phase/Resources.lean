/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Resources
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Resources
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Reflection.Resources
import all QuantumAlg.Components.Encoded.BitGates.Reflection.Resources
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.Small.PhaseProgram
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Coordinates
import all QuantumAlg.Core.Base.Accounting.Weighted
import Mathlib.Tactic.IntervalCases

/-!
# Independent elementary budgets of controlled positive source reflection

A source of width zero, one or two uses zero, three or eight gates and no
work position. Larger sources borrow one different actual phase position;
the exact restored action uses 2n X gates, two H gates, one control Z and
the balanced n-control Toffoli schedule. The independent formulas are
proved equal to the actual native event pool and sequential depth.
-/

namespace QuantumAlg.ZeroReflection

noncomputable section

open EncodedBit.Word.OneDirtyLayout

/-- Native elementary multiplicities of the selected controlled source synthesis. -/
def controlledElementaryEventPool (oracles : OracleModel) (width : Nat)
    (operations : ClassicalOpModel := .empty) (services : ClassicalOracleModel := .empty) :
    ResourcePool (.quantum AlgorithmGate.model oracles operations services) :=
  match width with
  | 0 => 0
  | 1 => 2 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .singleQubit) +
      ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .cnot)
  | 2 => 7 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .singleQubit) +
      ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .toffoli)
  | extra + 3 => (2 * (extra + 3) + 3) • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .singleQubit) +
      gateCount (extra + 3) • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .toffoli)

/-- Independent count and unit-event depth, including the exact controlled global minus. -/
public def controlledElementaryGateCount : Nat → Nat
  | 0 => 0
  | 1 => 3
  | 2 => 8
  | extra + 3 => 2 * (extra + 3) + gateCount (extra + 3) + 3

/-- Independent single-qubit multiplicity of the controlled source reflection. -/
public def controlledElementarySingleQubitCount : Nat → Nat
  | 0 => 0
  | 1 => 2
  | 2 => 7
  | extra + 3 => 2 * (extra + 3) + 3

/-- Only a one-qubit source uses a CNOT in its controlled reflection. -/
public def controlledElementaryCNOTCount : Nat → Nat
  | 1 => 1
  | _ => 0

/-- Independent Toffoli multiplicity of the controlled source reflection. -/
public def controlledElementaryToffoliCount : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | extra + 3 => gateCount (extra + 3)

/-- The controlled reflection Toffoli count has an explicit formula at every width. -/
public lemma zeroReflection_controlledElementaryToffoliCount_table (width : Nat) :
    controlledElementaryToffoliCount width = match width with
      | 0 | 1 => 0
      | 2 => 1
      | 3 => 4
      | 4 => 10
      | extra + 5 => 8 * (extra + 2) := by
  match width with
  | 0 | 1 | 2 | 3 | 4 => decide
  | extra + 5 =>
      change gateCount (extra + 5) = 8 * (extra + 2)
      rw [gateCount_of_five_le (by omega)]
      omega

/-- The controlled reflection single-qubit count is explicit at every width. -/
public lemma zeroReflection_controlledElementarySingleQubitCount_table (width : Nat) :
    controlledElementarySingleQubitCount width = match width with
      | 0 => 0
      | 1 => 2
      | 2 => 7
      | extra + 3 => 2 * (extra + 3) + 3 := by
  rfl

/-- A controlled source reflection uses one CNOT exactly at source width one. -/
public lemma zeroReflection_controlledElementaryCNOTCount_table (width : Nat) :
    controlledElementaryCNOTCount width = if width = 1 then 1 else 0 := by
  match width with
  | 0 | 1 | extra + 2 => simp [controlledElementaryCNOTCount]

/-- The empty controlled reflection is the identity and has no gate occurrences. -/
@[simp] public lemma controlledElementaryGateCount_zero :
    controlledElementaryGateCount 0 = 0 := by decide

/-- One source qubit uses the actual three-gate positive controlled reflection. -/
@[simp] public lemma controlledElementaryGateCount_one :
    controlledElementaryGateCount 1 = 3 := by decide

/-- Two source qubits use the actual eight-gate controlled reflection. -/
@[simp] public lemma controlledElementaryGateCount_two :
    controlledElementaryGateCount 2 = 8 := by decide

/-- Three source qubits use thirteen elementary occurrences, including the controlled sign. -/
@[simp] public lemma controlledElementaryGateCount_three :
    controlledElementaryGateCount 3 = 13 := by decide

/-- Four source qubits use twenty-one elementary occurrences. -/
@[simp] public lemma controlledElementaryGateCount_four :
    controlledElementaryGateCount 4 = 21 := by decide

/-- From five source qubits onward the actual independent count has this linear formula. -/
public lemma controlledElementaryGateCount_of_five_le {width : Nat} (large : 5 ≤ width) :
    controlledElementaryGateCount width = 10 * width - 21 := by
  obtain ⟨extra, rfl⟩ : ∃ extra, width = extra + 5 := ⟨width - 5, by omega⟩
  rw [controlledElementaryGateCount, gateCount_of_five_le (by omega)]
  omega

namespace SmallPhase

lemma program_eventCost (oracles : OracleModel) (phases width : Nat)
    (physical : QubitLayout (phases + width)) (small : width ≤ 2) (control : Fin phases) :
    (program oracles phases width physical small control).eventCost =
      controlledElementaryEventPool oracles width := by
  interval_cases width
  · rfl
  · exact (PhaseWorkspace.phaseBit phases 0 control).controlledZ_eventCost physical oracles
      (PhaseWorkspace.sourceBit phases 0 0)
      (PhaseWorkspace.phaseBit_ne_sourceBit phases 0 control 0)
  · exact (PhaseWorkspace.phaseBit phases 1 control).controlledTwoWireZeroReflection_eventCost
      physical oracles (PhaseWorkspace.sourceBit phases 1 0)
      (PhaseWorkspace.sourceBit phases 1 1)
      (PhaseWorkspace.phaseBit_ne_sourceBit phases 1 control 0)
      (PhaseWorkspace.phaseBit_ne_sourceBit phases 1 control 1) (source_two_ne phases)

lemma program_unitDepth (oracles : OracleModel) (phases width : Nat)
    (physical : QubitLayout (phases + width)) (small : width ≤ 2) (control : Fin phases) :
    (program oracles phases width physical small control).evaluatedEventDepth
        (fun _ => 1) = controlledElementaryGateCount width := by
  interval_cases width
  · rfl
  · exact (PhaseWorkspace.phaseBit phases 0 control).controlledZ_unitDepth physical oracles
      (PhaseWorkspace.sourceBit phases 0 0)
      (PhaseWorkspace.phaseBit_ne_sourceBit phases 0 control 0)
  · exact (PhaseWorkspace.phaseBit phases 1 control).controlledTwoWireZeroReflection_unitDepth
      physical oracles (PhaseWorkspace.sourceBit phases 1 0)
      (PhaseWorkspace.sourceBit phases 1 1)
      (PhaseWorkspace.phaseBit_ne_sourceBit phases 1 control 0)
      (PhaseWorkspace.phaseBit_ne_sourceBit phases 1 control 1) (source_two_ne phases)

end SmallPhase

namespace PhaseWorkspace

lemma program_eventCost (oracles : OracleModel) (phases controls : Nat)
    (physical : QubitLayout (phases + (controls + 1))) (large : 2 ≤ controls)
    (control work : Fin phases) (different : control ≠ work) :
    (program oracles phases controls physical control work different).eventCost =
      controlledElementaryEventPool oracles (controls + 1) := by
  obtain ⟨extra, rfl⟩ : ∃ extra, controls = extra + 2 := ⟨controls - 2, by omega⟩
  have actual := (layout phases (extra + 2) work).controlledZeroReflectionProgram_eventCost
    physical oracles
    (phaseBit phases (extra + 2) control)
    (control_source_ne phases (extra + 2) control work)
    (control_output_ne phases (extra + 2) control work)
    (control_work_ne phases (extra + 2) control work different)
  change (program oracles phases (extra + 2) physical control work different).eventCost =
    _ at actual
  rw [gatePool, if_neg (by omega), if_neg (by omega)] at actual
  exact actual

lemma program_unitDepth (oracles : OracleModel) (phases controls : Nat)
    (physical : QubitLayout (phases + (controls + 1))) (large : 2 ≤ controls)
    (control work : Fin phases) (different : control ≠ work) :
    (program oracles phases controls physical control work different).evaluatedEventDepth
        (fun _ => 1) = controlledElementaryGateCount (controls + 1) := by
  obtain ⟨extra, rfl⟩ : ∃ extra, controls = extra + 2 := ⟨controls - 2, by omega⟩
  have actual := (layout phases (extra + 2) work).controlledZeroReflectionProgram_unitDepth
    physical oracles
    (phaseBit phases (extra + 2) control)
    (control_source_ne phases (extra + 2) control work)
    (control_output_ne phases (extra + 2) control work)
    (control_work_ne phases (extra + 2) control work different)
  change (program oracles phases (extra + 2) physical control work different).evaluatedEventDepth
    (fun _ => 1) = _ at actual
  exact actual

end PhaseWorkspace

/-- Every occurrence in the independent controlled-reflection pool is an elementary gate. -/
lemma controlledElementaryEventPool_gateCount (oracles : OracleModel) (width : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) (controlledElementaryEventPool oracles width) =
      controlledElementaryGateCount width := by
  match width with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | extra + 3 =>
      simp only [controlledElementaryEventPool, controlledElementaryGateCount,
        ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
        ResourcePool.weightedCount_singleton, mul_one]
      omega

/-- The elementary controlled reflection invokes no opaque source query. -/
lemma controlledElementaryEventPool_queryCount (oracles : OracleModel) (width : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .oracle _ => 1 | _ => 0) (controlledElementaryEventPool oracles width) = 0 := by
  match width with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | extra + 3 =>
      simp only [controlledElementaryEventPool, ResourcePool.weightedCount_add,
        ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton,
        mul_zero, add_zero]

/-- The selected controlled synthesis has a uniform linear elementary count. -/
lemma controlledElementaryGateCount_le (width : Nat) :
    controlledElementaryGateCount width ≤ 10 * width + 3 := by
  match width with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | extra + 5 =>
      rw [controlledElementaryGateCount, gateCount_of_five_le (by omega)]
      omega

end

end QuantumAlg.ZeroReflection
