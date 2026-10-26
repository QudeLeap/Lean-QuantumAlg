/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Parallel.Counts
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Arithmetic
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Arithmetic.Toggle.Resources
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Arithmetic.Sign.Resources
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Prepared.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Prepared.Inverse.Resources

/-!
# Direct native coordinates of actual paired selected arithmetic

The real selected guards, the actual new remainder body or unchanged
coefficient body, and the real Sign word are counted chronologically.
Every resource witness follows those same native programs; no old
remainder or complete old selected-instruction ledger is transferred.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel

noncomputable section

open EncodedBit

lemma instructionProgram_quantumTime (width : Nat) (positive : 1 ≤ width)
    (signed coefficient : Bool) :
    (instructionProgram width positive signed coefficient).evaluatedEventDepth
        Resource.Event.quantumDuration =
      2 * (ControlledArithmeticToggle.program width positive signed coefficient).evaluatedEventDepth
          Resource.Event.quantumDuration +
        (arithmeticBody width positive signed coefficient).evaluatedEventDepth
          Resource.Event.quantumDuration := by
  change (ControlledArithmeticToggle.program width positive signed coefficient).evaluatedEventDepth
      Resource.Event.quantumDuration +
    ((arithmeticBody width positive signed coefficient).evaluatedEventDepth
      Resource.Event.quantumDuration +
      (ControlledArithmeticToggle.program width positive signed coefficient).evaluatedEventDepth
        Resource.Event.quantumDuration) = _
  omega

/-- Fixed caps retain all guard and arithmetic occurrences, including both native adjoints. -/
def p256_instructionTimeBound (signed coefficient : Bool) : Nat :=
  if signed then if coefficient then 22843 else 41209
  else if coefficient then 22037 else 43435

/-- The two actual selected guards retain the full native body prefix between them. -/
lemma instructionProgram_nativePool (width : Nat) (positive : 1 ≤ width)
    (signed coefficient : Bool) :
    (instructionProgram width positive signed coefficient).eventCost =
      2 • (ControlledArithmeticToggle.program width positive signed coefficient).eventCost +
        (arithmeticBody width positive signed coefficient).eventCost := by
  change (ControlledArithmeticToggle.program width positive signed coefficient).eventCost +
      ((arithmeticBody width positive signed coefficient).eventCost +
        (ControlledArithmeticToggle.program width positive signed coefficient).eventCost) = _
  abel

private lemma body_toffoli_direct (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (arithmeticBody 256 (by decide) signed coefficient).eventCost ≤
        (if coefficient then 696 else 9432) + (if signed then 7839 else 6545) := by
  cases coefficient <;> cases signed
  · exact RemainderAddress.Parallel.p256_program_toffoli_direct false
  · change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (RemainderAddress.Parallel.inverseProgram 256 (by decide) true).eventCost ≤ _
    rw [RemainderAddress.Parallel.inverseProgram_nativePool]
    exact RemainderAddress.Parallel.p256_program_toffoli_direct true
  · change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (CoefficientAddress.inverseProgram 256 (by decide) false).eventCost ≤ 696 + 6545
    rw [CoefficientAddress.inverseProgram_eventCost, CoefficientAddress.p256_program_toffoli_count]
    exact le_rfl
  · exact (CoefficientAddress.p256_program_toffoli_count true).le

private lemma body_cnot_direct (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (arithmeticBody 256 (by decide) signed coefficient).eventCost ≤
        if coefficient then 3160 else 22068 := by
  cases coefficient <;> cases signed
  · exact RemainderAddress.Parallel.p256_program_cnot_direct false
  · change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (RemainderAddress.Parallel.inverseProgram 256 (by decide) true).eventCost ≤ _
    rw [RemainderAddress.Parallel.inverseProgram_nativePool]
    exact RemainderAddress.Parallel.p256_program_cnot_direct true
  · change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (CoefficientAddress.inverseProgram 256 (by decide) false).eventCost ≤ 3160
    rw [CoefficientAddress.inverseProgram_eventCost, CoefficientAddress.p256_program_cnot_count]
  · exact (CoefficientAddress.p256_program_cnot_count true).le

private lemma body_singleQubit_direct (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (arithmeticBody 256 (by decide) signed coefficient).eventCost =
        3196 := by
  cases coefficient <;> cases signed
  · exact RemainderAddress.Parallel.p256_program_singleQubit_direct false
  · change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (RemainderAddress.Parallel.inverseProgram 256 (by decide) true).eventCost = _
    rw [RemainderAddress.Parallel.inverseProgram_nativePool]
    exact RemainderAddress.Parallel.p256_program_singleQubit_direct true
  · change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (CoefficientAddress.inverseProgram 256 (by decide) false).eventCost = 3196
    rw [CoefficientAddress.inverseProgram_eventCost,
      CoefficientAddress.p256_program_singleQubit_count]
  · exact CoefficientAddress.p256_program_singleQubit_count true

private lemma body_quantumTime_direct (signed coefficient : Bool) :
    (arithmeticBody 256 (by decide) signed coefficient).evaluatedEventDepth
      Resource.Event.quantumDuration ≤
        (if coefficient then 704 else 18922) + (if signed then 14187 else 12893) := by
  cases coefficient <;> cases signed
  · exact RemainderAddress.Parallel.p256_program_quantumTime_direct false
  · change ((RemainderAddress.Parallel.program 256 (by decide) true).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).evaluatedEventDepth
        Resource.Event.quantumDuration ≤ 18922 + 14187
    rw [AlgorithmGate.algorithmGate_emptyAdjoints_quantumTime]
    exact RemainderAddress.Parallel.p256_program_quantumTime_direct true
  · change (CoefficientAddress.inverseProgram 256 (by decide) false).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ 704 + 12893
    rw [CoefficientAddress.inverseProgram_quantumTime,
      CoefficientAddress.p256_program_quantumTime]
    simp
  · exact (CoefficientAddress.p256_program_quantumTime true).le

/-- Independent original four-case native Toffoli caps. -/
def p256_instructionToffoliBound (signed coefficient : Bool) : Nat :=
  if signed then if coefficient then 12227 else 20679
  else if coefficient then 11397 else 22665

/-- Independent original four-case native CNOT caps. -/
def p256_instructionCnotBound (signed coefficient : Bool) : Nat :=
  if signed then if coefficient then 5276 else 24844
  else if coefficient then 5300 else 25084

lemma p256_instructionProgram_toffoli_direct (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (instructionProgram 256 (by decide) signed coefficient).eventCost ≤
        p256_instructionToffoliBound signed coefficient := by
  have body := body_toffoli_direct signed coefficient
  rw [instructionProgram_nativePool, ResourcePool.count_add, ResourcePool.count_nsmul,
    ControlledArithmeticToggle.p256_program_toffoli_count]
  cases signed <;> cases coefficient <;>
    simp only [p256_instructionToffoliBound, ArithmeticGuard.p256_phaseToffoli,
      Bool.false_eq_true, if_false, if_true] at * <;> omega

lemma p256_instructionProgram_cnot_direct (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (instructionProgram 256 (by decide) signed coefficient).eventCost ≤
        p256_instructionCnotBound signed coefficient := by
  have body := body_cnot_direct signed coefficient
  rw [instructionProgram_nativePool, ResourcePool.count_add, ResourcePool.count_nsmul,
    ControlledArithmeticToggle.p256_program_cnot_count]
  cases signed <;> cases coefficient <;>
    simp only [p256_instructionCnotBound, ArithmeticGuard.p256_phaseSingleQubit,
      Bool.false_eq_true, if_false, if_true] at * <;> omega

lemma p256_instructionProgram_singleQubit_direct (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (instructionProgram 256 (by decide) signed coefficient).eventCost = 5340 := by
  rw [instructionProgram_nativePool, ResourcePool.count_add, ResourcePool.count_nsmul,
    ControlledArithmeticToggle.p256_program_singleQubit_count, body_singleQubit_direct]

lemma p256_instructionProgram_quantumTime_direct (signed coefficient : Bool) :
    (instructionProgram 256 (by decide) signed coefficient).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ p256_instructionTimeBound signed coefficient := by
  have toggle := ControlledArithmeticToggle.p256_program_quantumTime_le signed coefficient
  have body := body_quantumTime_direct signed coefficient
  rw [instructionProgram_quantumTime]
  cases signed <;> cases coefficient <;>
    simp only [p256_instructionTimeBound, ArithmeticGuard.p256_phaseSingleQubit,
      ArithmeticGuard.p256_phaseToffoli, Bool.false_eq_true, if_false, if_true] at * <;> omega

/-- Both source instructions and the actual selected Sign word occur in this exact order. -/
lemma arithmeticProgram_nativePool (width : Nat) (positive : 1 ≤ width) (coefficient : Bool) :
    (arithmeticProgram width positive coefficient).eventCost =
      (instructionProgram width positive (!coefficient) coefficient).eventCost +
        ((ControlledSourceWord.program width
          (ControlledArithmeticBlocks.signGates width coefficient)).eventCost +
            (instructionProgram width positive coefficient coefficient).eventCost) := rfl

lemma p256_arithmeticProgram_toffoli_direct (coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (arithmeticProgram 256 (by decide) coefficient).eventCost ≤
        if coefficient then 23625 else 43348 := by
  have first := p256_instructionProgram_toffoli_direct (!coefficient) coefficient
  have last := p256_instructionProgram_toffoli_direct coefficient coefficient
  rw [arithmeticProgram_nativePool, ResourcePool.count_add, ResourcePool.count_add,
    ControlledArithmeticBlocks.sign_program_toffoli_count]
  cases coefficient <;>
    simp only [p256_instructionToffoliBound, Bool.false_eq_true, if_false, if_true,
      Bool.not_false, Bool.not_true] at * <;> omega

lemma p256_arithmeticProgram_cnot_direct (coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (arithmeticProgram 256 (by decide) coefficient).eventCost ≤
        if coefficient then 10576 else 49930 := by
  have first := p256_instructionProgram_cnot_direct (!coefficient) coefficient
  have last := p256_instructionProgram_cnot_direct coefficient coefficient
  rw [arithmeticProgram_nativePool, ResourcePool.count_add, ResourcePool.count_add,
    ControlledArithmeticBlocks.sign_program_cnot_count]
  cases coefficient <;>
    simp only [p256_instructionCnotBound, Bool.false_eq_true, if_false, if_true,
      Bool.not_false, Bool.not_true] at * <;> omega

lemma p256_arithmeticProgram_singleQubit_direct (coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (arithmeticProgram 256 (by decide) coefficient).eventCost = 10680 := by
  rw [arithmeticProgram_nativePool, ResourcePool.count_add, ResourcePool.count_add,
    p256_instructionProgram_singleQubit_direct, p256_instructionProgram_singleQubit_direct,
    ControlledSourceWord.program_singleQubit_count]

lemma p256_arithmeticProgram_quantumTime_direct (coefficient : Bool) :
    (arithmeticProgram 256 (by decide) coefficient).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ if coefficient then 44881 else 84650 := by
  have first := p256_instructionProgram_quantumTime_direct (!coefficient) coefficient
  have last := p256_instructionProgram_quantumTime_direct coefficient coefficient
  rw [arithmeticProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, ControlledArithmeticBlocks.sign_program_quantumTime]
  cases coefficient <;>
    simp only [p256_instructionTimeBound, Bool.false_eq_true, if_false, if_true,
      Bool.not_false, Bool.not_true] at * <;> omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel
