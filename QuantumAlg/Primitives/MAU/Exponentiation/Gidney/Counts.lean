/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Oracle.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Controlled.Counts

/-!
# Exact native coordinates of the actual pushed selected-power execution

Every selected stage executes the same two controlled MACs and swap.
Its X count is zero. Its CNOT budget follows the actual bi-flip CNOT
ledger, independently of the Toffoli allowance [G17, paper.tex:276-293,319-334].
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section


open EncodedBit GateSpec QuantumAlg.Nat.FixedWidth.UnitExponentiation

/-- The native multiplicity of one emitted X, CNOT, or Toffoli instruction. -/
def selectedGateMultiplicity {Data : Type} {carrier : BinaryLabelEncoding Data}
    (coordinate : AlgorithmGate.Coordinate) (gate : GateSpec carrier) : Nat :=
  match coordinate with
  | .singleQubit => xMultiplicity gate
  | .cnot => cnotMultiplicity gate
  | .toffoli => toffoliMultiplicity gate

/-- Exact finite sum over the emitted selected-power stages, with no assumed zero coordinate. -/
def selectedPowerCount (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) (coordinate : AlgorithmGate.Coordinate) : Nat :=
  ((List.ofFn fun bit : Fin exponentWidth => bit).map fun bit =>
    ((stageGates exponentWidth width modulus base bit).map
      (selectedGateMultiplicity coordinate)).sum).sum

private lemma selectedStage_native_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (coordinate : AlgorithmGate.Coordinate) (bit : Fin exponentWidth) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
        (stageProgram exponentWidth width modulus base bit).eventCost =
      ((stageGates exponentWidth width modulus base bit).map
        (selectedGateMultiplicity coordinate)).sum := by
  cases coordinate with
  | singleQubit => exact programList_x_count_eq_sum _ _ _
  | cnot => exact programList_cnot_count_eq_sum _ _ _
  | toffoli => exact programList_toffoli_count_eq_sum _ _ _

private lemma selectedBits_native_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (coordinate : AlgorithmGate.Coordinate) (bits : List (Fin exponentWidth)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
        (programForBits exponentWidth width modulus base bits).eventCost =
      (bits.map fun bit => ((stageGates exponentWidth width modulus base bit).map
        (selectedGateMultiplicity coordinate)).sum).sum := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      change ResourcePool.count _ ((stageProgram exponentWidth width modulus base bit).seq
        (programForBits exponentWidth width modulus base bits)).eventCost = _
      rw [UnitaryCircuit.seq_eventCost, ResourcePool.count_add, selectedStage_native_count, ih]
      rfl

/-- Every selected-power coordinate is read back from the same executed new stages. -/
lemma gidneyExponent_native_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
      (program exponentWidth width modulus base).eventCost =
        selectedPowerCount exponentWidth width modulus base coordinate :=
  selectedBits_native_count exponentWidth width modulus base coordinate _

/-- An independent CNOT allowance for the actual selected-power fold. -/
def selectedPowerCnotBound (exponentWidth width : Nat) : Nat :=
  exponentWidth * Multiplication.Gidney.controlledCnotBound width

private lemma selectedStage_singleQubit_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (stageProgram exponentWidth width modulus base bit).eventCost = 0 := by
  rw [selectedStage_native_count]
  exact Multiplication.Gidney.gidneyControlledUnitMultiplication_xCount
    exponentWidth width bit modulus (stageUnit base bit)

private lemma selectedBits_singleQubit_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (bits : List (Fin exponentWidth)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (programForBits exponentWidth width modulus base bits).eventCost = 0 := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      change ResourcePool.count _ ((stageProgram exponentWidth width modulus base bit).seq
        (programForBits exponentWidth width modulus base bits)).eventCost = 0
      rw [UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        selectedStage_singleQubit_count, ih, Nat.zero_add]

/-- The actual selected-power arithmetic retains its original zero-X contract. -/
lemma gidneyExponent_singleQubit_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (program exponentWidth width modulus base).eventCost = 0 :=
  selectedBits_singleQubit_count exponentWidth width modulus base _

/-- The exact selected-power finite sum has zero single-qubit multiplicity. -/
lemma selectedPowerCount_singleQubit (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    selectedPowerCount exponentWidth width modulus base .singleQubit = 0 := by
  rw [← gidneyExponent_native_count]
  exact gidneyExponent_singleQubit_count exponentWidth width modulus base

private lemma selectedBits_cnot_count_le (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (bits : List (Fin exponentWidth)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (programForBits exponentWidth width modulus base bits).eventCost ≤
      bits.length * Multiplication.Gidney.controlledCnotBound width := by
  induction bits with
  | nil => exact Nat.zero_le _
  | cons bit bits ih =>
      have current := (Multiplication.Gidney.gidneyControlledUnitMultiplication_native_counts
        exponentWidth width bit modulus (stageUnit base bit)).2
      change ResourcePool.count _ ((stageProgram exponentWidth width modulus base bit).seq
        (programForBits exponentWidth width modulus base bits)).eventCost ≤ _
      rw [UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        List.length_cons, Nat.succ_mul]
      exact (Nat.add_le_add current ih).trans_eq (Nat.add_comm _ _)

/-- The exact selected-power CNOT sum meets an independent width-only budget. -/
lemma selectedPowerCount_cnot_le (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    selectedPowerCount exponentWidth width modulus base .cnot ≤
      selectedPowerCnotBound exponentWidth width := by
  rw [← gidneyExponent_native_count]
  simpa only [program, List.length_ofFn, selectedPowerCnotBound] using
    selectedBits_cnot_count_le exponentWidth width modulus base (List.ofFn fun bit => bit)

/-- Both actual selected-power CNOT ledgers surround the width-CNOT XOR copy. -/
lemma gidneyExponentOracle_cnot_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (oracleProgram exponentWidth width modulus base).eventCost =
        2 * selectedPowerCount exponentWidth width modulus base .cnot + width := by
  simp only [gidneyExponentOracle_eventCost, ResourcePool.count_add,
    gidneyExponent_native_count, copyNativeBudget, ResourcePool.count_ofList,
    List.count_replicate_self]
  omega

/-- Compute, copy and uncompute retain the zero-X arithmetic contract. -/
lemma gidneyExponentOracle_singleQubit_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (oracleProgram exponentWidth width modulus base).eventCost = 0 := by
  simp [gidneyExponentOracle_eventCost, ResourcePool.count_add,
    gidneyExponent_singleQubit_count, copyNativeBudget,
    ResourcePool.count_ofList, List.count_replicate]

end

end QuantumAlg.MAU.Exponentiation.Gidney
