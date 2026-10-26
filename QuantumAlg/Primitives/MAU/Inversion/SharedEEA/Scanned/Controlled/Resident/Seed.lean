/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.ResidentSeed.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Resident

/-!
# Actual small-seed preparation on the complete resident frame

The fixed original Work1 tail and coefficient-length one are loaded by
the proved native X layer. Complete Work2, the original pool, Y and all
three supplied C/N/W systems are retained, including their correlations.
The existing complete placement reverses Work2's numerical convention
without executing a wire permutation or selecting a program from input.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResidentSeed

noncomputable section

private def groupedProgram (width : Nat) (positive : 0 < width.size) (tail : BitVec 3) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledResidentFrame.groupedEncoding width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (prefixWidth := (ControlledFrame.encoding width).width)
    (ControlledResidentFrame.savedEncoding width).width
    (ControlledFrame.liftProgram width
      (UnitaryCircuit.onBinaryPrefix (prefixWidth := (SharedEEA.encoding width).width)
        (poolEncoding width).width
        (ResidentSeed.program width positive tail)))

private def groupedStep (width : Nat) (positive : 0 < width.size) (tail : BitVec 3)
    (state : ControlledResidentFrame.Grouped width) : ControlledResidentFrame.Grouped width :=
  (((ResidentSeed.step width positive tail state.1.1.1, state.1.1.2), state.1.2), state.2)

private lemma groupedProgram_realizes (width : Nat) (positive : 0 < width.size)
    (tail : BitVec 3) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (ControlledResidentFrame.groupedEncoding width)
      (groupedProgram width positive tail) environment (groupedStep width positive tail) := by
  have pooled : UnitaryCircuit.Realizes
      (layout := QubitLayout.canonical (Scanned.encoding width).width) (Scanned.encoding width)
      (UnitaryCircuit.onBinaryPrefix (prefixWidth := (SharedEEA.encoding width).width)
        (poolEncoding width).width
        (ResidentSeed.program width positive tail)) environment
      (fun state => (ResidentSeed.step width positive tail state.1, state.2)) :=
    (ResidentSeed.program_realizes width positive tail environment).onBinaryPrefix
      (right := poolEncoding width)
  exact (ControlledFrame.liftProgram_realizes width _ _ environment pooled).onBinaryPrefix
    (right := ControlledResidentFrame.savedEncoding width)

/-- The same fixed X layer is placed on the existing complete resident frame. -/
def program (width : Nat) (positive : 0 < width.size) (tail : BitVec 3) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledResidentFrame.encoding width).width).toQuantum :=
  (ControlledResidentFrame.layout width).place (groupedProgram width positive tail)

/-- Original zero source work beside a complete arbitrary quantum input and complement. -/
def blank (width : Nat) (input : BitVec (width + 3)) (pool : Pool width)
    (flags : ControlledResidentFrame.Flags) (numerator : Fin (2 ^ width)) :
    ControlledResidentFrame.Data width :=
  ControlledResidentFrame.reassemble width
    (((ResidentSeed.blank width input, pool), (flags.1, flags.2.2)), (numerator, flags.2.1))

/-- Exactly the initialized original source, with the entire same physical complement. -/
def seeded (width : Nat) (tail : BitVec 3) (input : BitVec (width + 3)) (pool : Pool width)
    (flags : ControlledResidentFrame.Flags) (numerator : Fin (2 ^ width)) :
    ControlledResidentFrame.Data width :=
  ControlledResidentFrame.reassemble width
    (((ResidentSeed.source width tail input, pool), (flags.1, flags.2.2)), (numerator, flags.2.1))

/-- Exact complete-frame preparation retains every arbitrary original complement label. -/
lemma program_blank (width : Nat) (positive : 0 < width.size) (tail : BitVec 3)
    (environment : OracleModel.empty.Interpretation) (input : BitVec (width + 3))
    (pool : Pool width) (flags : ControlledResidentFrame.Flags) (numerator : Fin (2 ^ width)) :
    (program width positive tail).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledResidentFrame.encoding width).encode
            (blank width input pool flags numerator)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledResidentFrame.encoding width).encode
          (seeded width tail input pool flags numerator))) := by
  have actual := (groupedProgram_realizes width positive tail environment).apply_encoded_ket
    (((ResidentSeed.blank width input, pool), (flags.1, flags.2.2)), (numerator, flags.2.1))
  simp only [groupedStep, ResidentSeed.step_blank] at actual
  have placed := (ControlledResidentFrame.layout width).place_ket_of_eq _ _ _ actual
  simpa only [program, blank, seeded, ControlledResidentFrame.layout_reassemble] using placed

/-- A fixed modulus alone selects the three original tail bits. -/
def tail (modulus : Nat) : BitVec 3 :=
  (InitialPortProgram.inputFrame modulus 0).firstWord.setWidth 3

/-- The same full seeded boundary is the actual resident inversion's complete initial boundary. -/
lemma seeded_initial (modulus : Nat) (input numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    seeded modulus.size (tail modulus) (InitialPortProgram.inputFrame modulus input).secondWord
        pool flags numerator = ControlledResident.initial modulus input numerator pool flags := by
  have source := ResidentSeed.source_inputFrame modulus input
  change ResidentSeed.source modulus.size (tail modulus)
    (InitialPortProgram.inputFrame modulus input).secondWord = _ at source
  unfold seeded ControlledResident.initial
  rw [source]

/-- The full physical placement retains precisely the original native X ledger. -/
lemma program_eventTrace (width : Nat) (positive : 0 < width.size) (tail : BitVec 3) :
    (program width positive tail).eventTrace =
      (ResidentSeed.program width positive tail).eventTrace := by
  rw [program, EncodedBit.FullPlacement.place_eventTrace]
  rfl

/-- Existing complete-frame placement preserves the proved actual parallel depth. -/
lemma program_quantumTime_le (width : Nat) (positive : 0 < width.size) (tail : BitVec 3) :
    (program width positive tail).evaluatedEventDepth Resource.Event.quantumDuration ≤ 1 := by
  rw [program, EncodedBit.FullPlacement.place_evaluatedEventDepth]
  exact ResidentSeed.program_quantumTime_le width positive tail

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResidentSeed
