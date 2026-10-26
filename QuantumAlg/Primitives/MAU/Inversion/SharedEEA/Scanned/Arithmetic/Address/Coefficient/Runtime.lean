/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Native
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Frame
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Choice

/-!
# Paid coherent coefficient address retaining the separate conjunction

Original Phase2 selects actual native address words through two real
controlled lists and two real X masks. The original operand bit used
as dirty work is restored within every source instruction. Every
prefix position and the separate conjunction remain untouched, so the
actual unary arithmetic traversal can use them afterwards.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress

noncomputable section

open EncodedBit ArithmeticGuard NumberTheory.SharedEEA

private lemma phase_outside (width : Nat) :
    ArithmeticGeometry.outsideMetadata width (phase2Bit width) := by
  right
  rw [phase2Bit_wire]
  omega

private lemma work_outside (width : Nat) :
    ArithmeticGeometry.outsideMetadata width (firstWordBit width ⟨0, by omega⟩) := by
  left
  change 0 < 2 * (width + 3)
  omega

private lemma control_disjoint (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (gate : GateSpec (encoding width))
    (present : gate ∈ nativeCoefficientGates width positive deshift) :
    GateSpec.bitDisjoint (flag width 1) gate :=
  nativeCoefficientGates_bitDisjoint width positive deshift _ (phase_outside width) gate present

private lemma work_disjoint (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (gate : GateSpec (encoding width))
    (present : gate ∈ nativeCoefficientGates width positive deshift) :
    GateSpec.bitDisjoint (work width) gate :=
  nativeCoefficientGates_bitDisjoint width positive deshift _ (work_outside width) gate present

/-- All actual native source-phase arithmetic and control masks execute in the original frame. -/
def runtimeCoefficientGates (width : Nat) (positive : 1 ≤ width) :
    List (GateSpec (encoding width)) :=
  GateSpec.choiceGates (flag width 1) (work width)
    (nativeCoefficientGates width positive false) (nativeCoefficientGates width positive true)
    (control_disjoint width positive false) (work_disjoint width positive false)
    (control_disjoint width positive true) (work_disjoint width positive true)
    (flag_work_ne width 1)

/-- Independent finite address action retains the whole original source and workspace. -/
def runtimeCoefficientStep (width : Nat) (positive : 1 ≤ width) (state : Data width) : Data width :=
  if state.1.flags.second then coefficientStep width positive true state
  else coefficientStep width positive false state

/-- The actual native controlled choice has exactly the original source-phase address action. -/
lemma runtimeCoefficientGates_step (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    GateSpec.stepList (runtimeCoefficientGates width positive) state =
      runtimeCoefficientStep width positive state := by
  rw [runtimeCoefficientGates, GateSpec.choiceGates_step]
  simp only [nativeCoefficientGates_step]
  rfl

/-- Compile the same literal word without allocating any system from or outside the shared pool. -/
def runtimeCoefficientProgram (width : Nat) (positive : 1 ≤ width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (runtimeCoefficientGates width positive)

/-- Every complete finite input and arbitrary reference amplitude follows the same physical word. -/
lemma runtimeCoefficientProgram_realizes (width : Nat) (positive : 1 ≤ width)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (runtimeCoefficientProgram width positive) environment
      (runtimeCoefficientStep width positive) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (runtimeCoefficientGates_step width positive) environment

/-- All original work words, finite metadata, phases, Sign, Ctrl and arbitrary Iter survive. -/
lemma runtimeCoefficientStep_source (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    (runtimeCoefficientStep width positive state).1 = state.1 := by
  unfold runtimeCoefficientStep
  split <;> exact coefficientStep_source width positive _ state

/-- The entire unary prefix and the separate conjunction retain arbitrary incoming values. -/
lemma runtimeCoefficientStep_workspace (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    (runtimeCoefficientStep width positive state).2.2 = state.2.2 := by
  unfold runtimeCoefficientStep
  split <;> exact coefficientStep_workspace width positive _ state

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress
