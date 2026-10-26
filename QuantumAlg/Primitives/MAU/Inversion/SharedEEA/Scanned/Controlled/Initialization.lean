/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Action
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.SourceWord
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.PortProgram
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.MacroFrame

/-!
# Actual selected constant loading, input folding and initial length computation

Only the public modulus determines these original native words. External
selection is lowered gate by gate using the real C/W wires. The complete
pool and arbitrary external work are retained. All-label realization is
separate from the original positive-input source-trajectory refinement.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledInitialization

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The actual original fixed-X load is emitted under the supplied external control. -/
def loadProgram (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding modulus.size).width).toQuantum :=
  ControlledSourceWord.program modulus.size
    (Work1Constant.gates modulus.size (InitialPortProgram.constant modulus))

/-- Every input label receives only the fixed constant load, retaining all other physical fields. -/
lemma loadProgram_initial (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (environment : OracleModel.empty.Interpretation) (pool : Pool modulus.size)
    (flags : Bool × Bool) :
    (loadProgram modulus).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding modulus.size).encode
            ((InitialPortProgram.inputFrame modulus input, pool), flags)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding modulus.size).encode
          ((if flags.1 then InitialFrame.initial modulus input
            else InitialPortProgram.inputFrame modulus input, pool), flags))) := by
  have actual := (ControlledSourceWord.program_realizes modulus.size
    (Work1Constant.gates modulus.size (InitialPortProgram.constant modulus))
    environment).apply_encoded_ket ((InitialPortProgram.inputFrame modulus input, pool), flags)
  rw [InitialPortProgram.gates_initial] at actual
  exact actual

def gates (modulus : Nat) : List (GateSpec (SharedEEA.encoding modulus.size)) :=
  FoldProgram.gates modulus ++ InitialLengthWrite.gates modulus.size

def sourceStep (modulus : Nat) (state : Registers modulus.size) : Registers modulus.size :=
  GateSpec.stepList (InitialLengthWrite.gates modulus.size) (FoldProgram.step modulus state)

/-- Both complete original native initial words receive honest external gate lowering. -/
def program (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding modulus.size).width).toQuantum :=
  ControlledSourceWord.program modulus.size (gates modulus)

/-- All incoming source and work values have the exact selected complete original source action. -/
lemma program_realizes (modulus : Nat) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (ControlledFrame.encoding modulus.size) (program modulus) environment
      (ControlledSource.step modulus.size (sourceStep modulus)) := by
  apply (ControlledSourceWord.program_realizes modulus.size (gates modulus) environment).congrStep
  intro state
  rw [gates, GateSpec.stepList_append, FoldProgram.foldProgram_gates_step]
  rfl

/-- Only the active source refinement uses the unchanged original positive-residue assumptions. -/
lemma program_initial_active (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (environment : OracleModel.empty.Interpretation) (pool : Pool modulus.size)
    (flags : Bool × Bool) (selected : flags.1 = true)
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (program modulus).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding modulus.size).encode
            ((InitialFrame.initial modulus input, pool), flags)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding modulus.size).encode
          ((MacroBoundary.frame
            (IterationState.initial modulus (foldInput modulus input.val).2) modulus
            (folded_initial_admissible modulus input.val positive bounded)
            (IterationState.initial_balance modulus (foldInput modulus input.val).2)
            (foldInput modulus input.val).1, pool), flags))) := by
  have actual := (program_realizes modulus environment).apply_encoded_ket
    ((InitialFrame.initial modulus input, pool), flags)
  change (program modulus).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding modulus.size).encode
          ((InitialFrame.initial modulus input, pool), flags)))) =
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((ControlledFrame.encoding modulus.size).encode
        ((if flags.1 then InitialFrame.result modulus input
          else InitialFrame.initial modulus input, pool), flags))) at actual
  simpa only [selected, ↓reduceIte,
    InitialMacroFrame.result_eq_frame modulus input positive bounded] using actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledInitialization
