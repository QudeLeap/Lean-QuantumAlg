/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Resources
import all QuantumAlg.Components.Oracle.ZeroReflection.Small.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.OneDirty.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.OneDirty.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.Reflection.Resources
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Resources
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.UnitaryCircuit
import Mathlib.Tactic.IntervalCases

/-!
# Independent elementary source-reflection budgets

Widths at most three use the actual work-free constructions. Wider source
registers use the actual one-dirty construction, including both complements,
both Hadamards and the exact global-minus correction. The formulas below
contain only widths and native elementary coordinates; circuit theorems
establish their equality with the execution's own ledger and depth.
-/

namespace QuantumAlg.ZeroReflection

noncomputable section

open EncodedBit.Word.OneDirtyLayout

/-- Native elementary multiplicities of the selected minimal-work source reflection. -/
def elementaryEventPool (oracles : OracleModel) (width : Nat)
    (operations : ClassicalOpModel := .empty) (services : ClassicalOracleModel := .empty) :
    ResourcePool (.quantum AlgorithmGate.model oracles operations services) :=
  match width with
  | 0 => 0
  | 1 => ResourcePool.singleton
      (model := .quantum AlgorithmGate.model oracles operations services) (.gate .singleQubit)
  | 2 => 4 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .singleQubit) +
      ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .cnot)
  | 3 => 9 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .singleQubit) +
      ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .toffoli)
  | extra + 4 => (2 * (extra + 4) + 3) • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .singleQubit) +
      gateCount (extra + 3) • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .toffoli)

/-- Independent total elementary count, also the sequential reflection depth. -/
public def elementaryGateCount : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 5
  | 3 => 10
  | extra + 4 => 2 * (extra + 4) + gateCount (extra + 3) + 3

/-- Independent single-qubit multiplicity of the selected source reflection. -/
public def elementarySingleQubitCount : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 9
  | extra + 4 => 2 * (extra + 4) + 3

/-- Only the width-two source reflection uses a CNOT. -/
public def elementaryCNOTCount : Nat → Nat
  | 2 => 1
  | _ => 0

/-- Independent Toffoli multiplicity of the selected source reflection. -/
public def elementaryToffoliCount : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | extra + 4 => gateCount (extra + 3)

/-- The native reflection Toffoli count has an explicit width-by-width formula. -/
public lemma zeroReflection_elementaryToffoliCount_table (width : Nat) :
    elementaryToffoliCount width = match width with
      | 0 | 1 | 2 => 0
      | 3 => 1
      | 4 => 4
      | 5 => 10
      | extra + 6 => 8 * (extra + 2) := by
  match width with
  | 0 | 1 | 2 | 3 | 4 | 5 => decide
  | extra + 6 =>
      change gateCount (extra + 5) = 8 * (extra + 2)
      rw [gateCount_of_five_le (by omega)]
      omega

/-- The native reflection single-qubit count is explicit at every width. -/
public lemma zeroReflection_elementarySingleQubitCount_table (width : Nat) :
    elementarySingleQubitCount width = match width with
      | 0 => 0
      | 1 => 1
      | 2 => 4
      | 3 => 9
      | extra + 4 => 2 * (extra + 4) + 3 := by
  rfl

/-- A native source reflection uses one CNOT exactly at width two. -/
public lemma zeroReflection_elementaryCNOTCount_table (width : Nat) :
    elementaryCNOTCount width = if width = 2 then 1 else 0 := by
  match width with
  | 0 | 1 | 2 | extra + 3 => simp [elementaryCNOTCount]

namespace Small

lemma program_eventCost (oracles : OracleModel) (width : Nat) (physical : QubitLayout width)
    (small : width ≤ 3) :
    (program oracles width physical small).eventCost = elementaryEventPool oracles width := by
  interval_cases width
  · rfl
  · exact (BinaryLabelEncoding.finIdentityBit 1 0).pauliZ_eventCost physical oracles
  · exact (BinaryLabelEncoding.finIdentityBit 2 0).twoWireZeroReflection_eventCost
      physical oracles (BinaryLabelEncoding.finIdentityBit 2 1) (by decide)
  · exact (BinaryLabelEncoding.finIdentityBit 3 0).threeWireZeroReflection_eventCost
      physical oracles (BinaryLabelEncoding.finIdentityBit 3 1)
      (BinaryLabelEncoding.finIdentityBit 3 2) (by decide) (by decide) (by decide)

lemma program_unitDepth (oracles : OracleModel) (width : Nat) (physical : QubitLayout width)
    (small : width ≤ 3) :
    (program oracles width physical small).evaluatedEventDepth (fun _ => 1) =
      elementaryGateCount width := by
  interval_cases width
  · rfl
  · exact (BinaryLabelEncoding.finIdentityBit 1 0).pauliZ_unitDepth physical oracles
  · exact (BinaryLabelEncoding.finIdentityBit 2 0).twoWireZeroReflection_unitDepth
      physical oracles (BinaryLabelEncoding.finIdentityBit 2 1) (by decide)
  · exact (BinaryLabelEncoding.finIdentityBit 3 0).threeWireZeroReflection_unitDepth
      physical oracles (BinaryLabelEncoding.finIdentityBit 3 1)
      (BinaryLabelEncoding.finIdentityBit 3 2) (by decide) (by decide) (by decide)

end Small

namespace OneDirty

lemma program_eventCost (oracles : OracleModel) (controls : Nat)
    (physical : QubitLayout (controls + 1 + 1)) (large : 3 ≤ controls) :
    (program oracles controls physical).eventCost = elementaryEventPool oracles (controls + 1) := by
  obtain ⟨extra, rfl⟩ : ∃ extra, controls = extra + 3 := ⟨controls - 3, by omega⟩
  have actual := (layout (extra + 3)).zeroReflectionProgram_eventCost physical oracles
  change (program oracles (extra + 3) physical).eventCost =
    _ at actual
  rw [gatePool, if_neg (by omega), if_neg (by omega)] at actual
  exact actual

lemma program_unitDepth (oracles : OracleModel) (controls : Nat)
    (physical : QubitLayout (controls + 1 + 1)) (large : 3 ≤ controls) :
    (program oracles controls physical).evaluatedEventDepth (fun _ => 1) =
      elementaryGateCount (controls + 1) := by
  obtain ⟨extra, rfl⟩ : ∃ extra, controls = extra + 3 := ⟨controls - 3, by omega⟩
  have actual := (layout (extra + 3)).zeroReflectionProgram_unitDepth physical oracles
  change (program oracles (extra + 3) physical).evaluatedEventDepth (fun _ => 1) = _ at actual
  change _ = 2 * (extra + 4) + gateCount (extra + 3) + 3
  omega

end OneDirty

/-- No opaque subroutine coordinate occurs in the independent elementary reflection budget. -/
lemma elementaryEventPool_queryCount (oracles : OracleModel) (width : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .oracle _ => 1 | _ => 0) (elementaryEventPool oracles width) = 0 := by
  match width with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | extra + 4 =>
      simp only [elementaryEventPool, ResourcePool.weightedCount_add,
        ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton,
        mul_zero, add_zero]

/-- Every counted occurrence belongs to the actual elementary gate family. -/
lemma elementaryEventPool_gateCount (oracles : OracleModel) (width : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) (elementaryEventPool oracles width) = elementaryGateCount width := by
  match width with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | extra + 4 =>
      simp only [elementaryEventPool, elementaryGateCount, ResourcePool.weightedCount_add,
        ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton, mul_one]
      omega

/-- The selected elementary source synthesis has a uniform linear gate bound. -/
lemma elementaryGateCount_le (width : Nat) : elementaryGateCount width ≤ 10 * width + 9 := by
  match width with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | extra + 4 =>
      by_cases first : extra = 0
      · subst extra
        decide
      · by_cases second : extra = 1
        · subst extra
          decide
        · have count := gateCount_of_five_le (by omega : 5 ≤ extra + 3)
          simp only [elementaryGateCount, count]
          omega

end

end QuantumAlg.ZeroReflection
