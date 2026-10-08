/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.IterationLaws
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.MacroFrame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Trajectory

/-!
# Exact native execution of the complete active shared-register trajectory

The actual preprocessing circuit folds the input, records Iter, and writes
the folded input's length. Repeating the same native eight-block microstep
then reaches the entire terminal frame with its retained iteration bit
[LYL+26, sec_EEA/sub_4phase.tex:107-125;
LYL+26, sec_EEA/sub_regshare.tex:275-313].

These are equations for the existing symbolic circuit repetition, including
its exact normalized ket amplitudes. The input-dependent quotient weight
locates the active prefix inside the eventual independent schedule; it is
not a runtime choice of a loop length. Terminal padding and extraction of
the inverse still require their actual gates, with all forward history
retained for the inverse circuit.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.NativeActiveProgram

noncomputable section

open NumberTheory.SharedEEA

/-- The actual symbolic repetition realizes the same complete native frame iteration. -/
theorem iterate_realizes (width count : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit.Realizes (encoding width)
      (UnitaryCircuit.iterate count (NativeMicrostep.program width enough))
      ((NativeMicrostep.step width)^[count]) :=
  (NativeMicrostep.program_realizes width enough).iterate count

/-- Every coprime positive residue reaches the full terminal frame with exact ket amplitude. -/
theorem folded_apply (modulus input : Nat) (nontrivial : 1 < modulus)
    (coprime : Nat.Coprime input modulus) (positive : 0 < input) (bounded : input < modulus) :
    (UnitaryCircuit.iterate (QuotientSchedule.phaseWeight modulus input)
      (NativeMicrostep.program modulus.size
        (PredicateLayout.modulus_length_width modulus nontrivial))).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
            ((encoding modulus.size).encode
              (MacroBoundary.frame
                (IterationState.initial modulus (foldInput modulus input).2) modulus
                (folded_initial_admissible modulus input positive bounded)
                (IterationState.initial_balance modulus (foldInput modulus input).2)
                (foldInput modulus input).1)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
          ((encoding modulus.size).encode
            (MacroBoundary.frame (TerminalPadding.finalState modulus input) modulus
              (TerminalPadding.final_admissible modulus input positive bounded)
              (TerminalPadding.final_balance modulus input)
              (SignedTrajectory.finalIteration modulus input)))) := by
  rw [(iterate_realizes modulus.size (QuotientSchedule.phaseWeight modulus input)
    (PredicateLayout.modulus_length_width modulus nontrivial)).apply_encoded_ket,
    NativeTrajectory.folded_frame modulus input coprime positive bounded]

/-- Actual folding, length computation, and active repetition compose without a supplied state. -/
theorem preprocessed_apply (modulus : Nat) (nontrivial : 1 < modulus)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    ((InitialFrame.program modulus).seq
      (UnitaryCircuit.iterate (QuotientSchedule.phaseWeight modulus input.val)
        (NativeMicrostep.program modulus.size
          (PredicateLayout.modulus_length_width modulus nontrivial)))).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
            ((encoding modulus.size).encode (InitialFrame.initial modulus input)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
          ((encoding modulus.size).encode
            (MacroBoundary.frame (TerminalPadding.finalState modulus input.val) modulus
              (TerminalPadding.final_admissible modulus input.val positive bounded)
              (TerminalPadding.final_balance modulus input.val)
              (SignedTrajectory.finalIteration modulus input.val)))) := by
  rw [UnitaryCircuit.applyNormalized_seq,
    InitialMacroFrame.program_initial modulus input positive bounded]
  exact folded_apply modulus input.val nontrivial coprime positive bounded

end

end QuantumAlg.MAU.Inversion.SharedEEA.NativeActiveProgram
