/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Microstep.Prefix
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Microstep.Arithmetic
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Boundary.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Microstep

/-!
# Actual complete scanned shared-EEA microstep in the original eight-block order

The native pre-shift, remainder, corrected Sign/quotient, coefficient,
post-shift, two phase blocks and complete terminal boundary execute on
one resident physical frame. Every scanned block returns the entire
pool before the next block. The only original control premise is the
existing internal Ctrl-zero invariant. All original work, metadata,
phase and dirty Iter labels remain admitted [LYL+26, sec_EEA/sub_opt.tex:37-84].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep

noncomputable section

open EncodedBit

private lemma positive_of_enough (width : Nat) (enough : 2 ≤ width.size) : 1 ≤ width := by
  by_contra small
  have zero : width = 0 := by omega
  subst width
  norm_num at enough

/-- The complete eight actual native blocks, including every preparation and adjoint cleanup. -/
def program (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (shiftProgram width false).seq
    ((ArithmeticBlocks.remainderProgram width (positive_of_enough width enough)).seq
      ((SignQuotient.program width).seq
        ((ArithmeticBlocks.coefficientProgram width (positive_of_enough width enough)).seq
          ((shiftProgram width true).seq
            ((controlProgram width enough).seq
              ((zeroProgram width enough).seq (TerminalBoundary.program width enough)))))))

/-- Complete original eight-block ket action with the same entire clean pool returned. -/
lemma program_apply_source (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation)
    (state : Data width) (prefixZero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (borrowZero : state.2.2.2 = false) (control : state.1.control = false) :
    (program width enough).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (SharedEEA.NativeMicrostep.step width state.1, state.2))) := by
  let first : Data width := (GuardedShift.step false state.1, state.2)
  let second : Data width :=
    (SharedEEA.ArithmeticBlocks.remainderStep width first.1, state.2)
  let third : Data width := (SharedEEA.SignQuotient.step width second.1, state.2)
  let fourth : Data width :=
    (SharedEEA.ArithmeticBlocks.coefficientStep width third.1, state.2)
  let fifth : Data width := (GuardedShift.step true fourth.1, state.2)
  let sixth : Data width := (NativeControl.step fifth.1, state.2)
  let seventh : Data width := (ZeroShiftControl.step sixth.1, state.2)
  let eighth : Data width := (SharedEEA.TerminalBoundary.step seventh.1, state.2)
  let ket (value : Data width) := NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
    ((encoding width).encode value))
  have firstControl : first.1.control = false :=
    (GuardedShift.step_control width false state.1).trans control
  have secondControl : second.1.control = false :=
    (SharedEEA.ArithmeticBlocks.remainderStep_control width first.1).trans firstControl
  have thirdControl : third.1.control = false :=
    (SharedEEA.SignQuotient.step_control width second.1).trans secondControl
  have firstActual := (shiftProgram_realizes width false environment).apply_encoded_ket state
  have secondActual := remainderProgram_apply_original width (positive_of_enough width enough)
    environment first prefixZero borrowZero addressZero firstControl
  have thirdActual := signProgram_apply_original width environment second addressZero prefixZero
    secondControl
  have fourthActual := coefficientProgram_apply_original width (positive_of_enough width enough)
    environment third prefixZero borrowZero addressZero thirdControl
  have fifthActual := (shiftProgram_realizes width true environment).apply_encoded_ket fourth
  have sixthActual := (controlProgram_realizes width enough environment).apply_encoded_ket fifth
  have seventhActual := (zeroProgram_realizes width enough environment).apply_encoded_ket sixth
  have eighthActual := TerminalBoundary.program_apply_source width enough environment seventh
    prefixZero addressZero borrowZero
  change (shiftProgram width false).applyNormalized environment (ket state) =
    ket first at firstActual
  change (ArithmeticBlocks.remainderProgram width (positive_of_enough width enough)).applyNormalized
    environment (ket first) = ket second at secondActual
  change (SignQuotient.program width).applyNormalized environment (ket second) =
    ket third at thirdActual
  change
    (ArithmeticBlocks.coefficientProgram width (positive_of_enough width enough)).applyNormalized
      environment (ket third) = ket fourth at fourthActual
  change (shiftProgram width true).applyNormalized environment (ket fourth) =
    ket fifth at fifthActual
  change (controlProgram width enough).applyNormalized environment (ket fifth) =
    ket sixth at sixthActual
  change (zeroProgram width enough).applyNormalized environment (ket sixth) =
    ket seventh at seventhActual
  change (TerminalBoundary.program width enough).applyNormalized environment (ket seventh) =
    ket eighth at eighthActual
  change (program width enough).applyNormalized environment (ket state) =
    ket (SharedEEA.NativeMicrostep.step width state.1, state.2)
  rw [program, UnitaryCircuit.applyNormalized_seq, firstActual,
    UnitaryCircuit.applyNormalized_seq, secondActual, UnitaryCircuit.applyNormalized_seq,
    thirdActual, UnitaryCircuit.applyNormalized_seq, fourthActual,
    UnitaryCircuit.applyNormalized_seq, fifthActual, UnitaryCircuit.applyNormalized_seq,
    sixthActual, UnitaryCircuit.applyNormalized_seq, seventhActual, eighthActual]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep
