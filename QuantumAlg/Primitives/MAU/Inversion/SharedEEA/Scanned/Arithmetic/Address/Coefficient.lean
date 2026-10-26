/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Remainder

/-!
# Actual coefficient length-minus-one with conjunction kept separate

The fixed phase-three body adds complete coefficient metadata to the
address. The fixed phase-four body loads physical width minus one and
subtracts complete divisor and shift. Native arithmetic retains the
complete prefix, separate conjunction, and every original source bit.
Coherent selection between source phases requires additional actual
controls; neither fixed body is selected from a host input value.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The fixed phase-four address offset is physically loaded through actual native X gates. -/
def coefficientConstant (width : Nat) : BitVec (ScanMetadata.addressWidth width) :=
  BitVec.ofNat (ScanMetadata.addressWidth width) (width + 3 - 1)

/-- Both fixed source-phase programs contain only actual native address arithmetic. -/
def coefficientProgram (width : Nat) (positive : 1 ≤ width) (deshift : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  if deshift then (constantProgram width (coefficientConstant width)).seq
    ((subtractProgram width positive .divisor).seq (subtractProgram width positive .shift))
  else program width positive .coefficient

/-- Full finite physical-frame action of either fixed source-phase address program. -/
def coefficientStep (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (state : Data width) : Data width :=
  if deshift then subtractStep width positive .shift
    (subtractStep width positive .divisor (constantStep width (coefficientConstant width) state))
  else step width positive .coefficient state

/-- The actual native execution preserves coherent amplitudes and the whole physical complement. -/
lemma coefficientProgram_realizes (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (coefficientProgram width positive deshift)
      environment (coefficientStep width positive deshift) := by
  cases deshift with
  | false => exact program_realizes width positive .coefficient environment
  | true =>
      have tail := UnitaryCircuit.Realizes.seq
        (subtractProgram_realizes width positive .divisor environment)
        (subtractProgram_realizes width positive .shift environment)
      have complete := UnitaryCircuit.Realizes.seq
        (constantProgram_realizes width (coefficientConstant width) environment) tail
      exact complete

/-- All original payload and complete metadata survive both native address preparations. -/
lemma coefficientStep_source (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (state : Data width) : (coefficientStep width positive deshift state).1 = state.1 := by
  cases deshift <;> simp only [coefficientStep, Bool.false_eq_true, if_false, if_true,
    step_source, subtractStep_source, constantStep_source]

/-- Conjunction and the whole prefix retain their incoming values on every finite label. -/
lemma coefficientStep_workspace (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (state : Data width) : (coefficientStep width positive deshift state).2.2 = state.2.2 := by
  cases deshift <;> simp only [coefficientStep, Bool.false_eq_true, if_false, if_true,
    step_workspace, subtractStep_workspace, constantStep_workspace]

/-- The actual address satisfies the complete finite modular equation, with no dropped padding. -/
lemma coefficientStep_address (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (state : Data width) :
    (coefficientStep width positive deshift state).2.1 =
      if deshift then (state.2.1 ^^^ coefficientConstant width) -
        sourceValue width positive .divisor state - sourceValue width positive .shift state
      else sourceValue width positive .coefficient state + state.2.1 := by
  cases deshift with
  | false => exact step_address width positive .coefficient state
  | true =>
      simp only [coefficientStep, if_true, subtractStep_address, constantStep_address,
        sourceValue, prefixBit_get, ArithmeticGeometry.fieldValue, subtractStep_source,
        constantStep_source,
        congrArg Prod.fst (subtractStep_workspace width positive .divisor
          (constantStep width (coefficientConstant width) state)),
        congrArg Prod.fst (constantStep_workspace width (coefficientConstant width) state)]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress
