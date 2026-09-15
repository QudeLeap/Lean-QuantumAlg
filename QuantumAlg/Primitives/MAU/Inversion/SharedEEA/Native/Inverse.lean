/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.CorrectedSchedule
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Output.Copy
import all QuantumAlg.Util.NumberTheory.SharedEEA.InverseOutput

/-!
# Actual shared-EEA inverse with complete forward-history restoration

The native circuit executes the fixed shared-EEA computation and its
actual decoder and correction, XORs the corrected word into the arbitrary
output, and runs the adjoint of that same complete computation. Both
shared words, all finite counters, every phase/parity bit, Ctrl, and the
original input return to their prepared values. No part of Gamma is
silently discarded [LYL+26, sec_EEA/sub_4phase.tex:105,123-128].

The exact normalized-ket theorem covers coprime positive residues for
every nontrivial modulus, including even moduli, and every initial output word. It is
therefore suitable for coherent input/reference extensions. Preparation
of the fixed auxiliary bits and runtime placement remain separate from
this original-frame native program.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.NativeInverse

noncomputable section

open NumberTheory.SharedEEA

/-- The complete actual forward computation acts before the separate original-width XOR target. -/
def forwardProgram (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit (Qubits (OutputCopy.encoding modulus.size).width) :=
  UnitaryCircuit.prodLeft (n := modulus.size) (CorrectedSchedule.program modulus nontrivial)

/-- Execute, copy by the actual CNOT list, then reverse every emitted forward operation. -/
def program (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit (Qubits (OutputCopy.encoding modulus.size).width) :=
  (forwardProgram modulus nontrivial).seq
    ((OutputCopy.program modulus.size).seq (forwardProgram modulus nontrivial).dagger)

private theorem copied_value (modulus input : Nat)
    (positive : 0 < input) (bounded : input < modulus) :
    OutputCopy.value (CorrectedSchedule.result modulus input positive bounded) =
      InverseOutput.word modulus input positive bounded := by
  apply Fin.ext
  rw [OutputCopy.value_of_fits _
    (CorrectedSchedule.result_fits_output modulus input positive bounded),
    CorrectedSchedule.result_value]
  rfl

/-- The arbitrary output word receives the independent mathematical inverse by XOR. -/
def output (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus)
    (target : Fin (2 ^ modulus.size)) : Fin (2 ^ modulus.size) :=
  ⟨target.val ^^^ (InverseOutput.word modulus input positive bounded).val,
    Nat.xor_lt_two_pow target.isLt (InverseOutput.word modulus input positive bounded).isLt⟩

/-- The exact actual circuit restores the entire initial frame and retains only the XOR output. -/
theorem program_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (input target : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val)
    (bounded : input.val < modulus) :
    (program modulus nontrivial).applyNormalized
        (NormalizedVector.ket (R := Qubits (OutputCopy.encoding modulus.size).width)
          ((OutputCopy.encoding modulus.size).encode
            (InitialFrame.initial modulus input, target))) =
      NormalizedVector.ket (R := Qubits (OutputCopy.encoding modulus.size).width)
        ((OutputCopy.encoding modulus.size).encode
          (InitialFrame.initial modulus input,
            output modulus input.val positive bounded target)) := by
  let initial := InitialFrame.initial modulus input
  let computed := CorrectedSchedule.result modulus input.val positive bounded
  let toggled := output modulus input.val positive bounded target
  have forward (value : Fin (2 ^ modulus.size)) :
      (forwardProgram modulus nontrivial).applyNormalized
          (NormalizedVector.ket
            ((OutputCopy.encoding modulus.size).encode (initial, value))) =
        NormalizedVector.ket ((OutputCopy.encoding modulus.size).encode (computed, value)) :=
    UnitaryCircuit.Realizes.prodLeft_applyNormalized_encoded_ket_of_eq
      (encoding modulus.size) (BinaryLabelEncoding.finIdentity modulus.size)
      (CorrectedSchedule.program modulus nontrivial) initial computed value
      (CorrectedSchedule.program_initial modulus nontrivial input coprime positive bounded)
  have copied :
      (OutputCopy.program modulus.size).applyNormalized
          (NormalizedVector.ket
            ((OutputCopy.encoding modulus.size).encode (computed, target))) =
        NormalizedVector.ket ((OutputCopy.encoding modulus.size).encode (computed, toggled)) := by
    rw [(OutputCopy.program_realizes modulus.size).apply_encoded_ket]
    have value := copied_value modulus input.val positive bounded
    change OutputCopy.value computed =
      InverseOutput.word modulus input.val positive bounded at value
    have fields : OutputCopy.step (computed, target) = (computed, toggled) := by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        exact congrArg (fun word : Fin (2 ^ modulus.size) => target.val ^^^ word.val) value
    rw [fields]
  have restored :
      (forwardProgram modulus nontrivial).dagger.applyNormalized
          (NormalizedVector.ket
            ((OutputCopy.encoding modulus.size).encode (computed, toggled))) =
        NormalizedVector.ket ((OutputCopy.encoding modulus.size).encode (initial, toggled)) :=
    (congrArg (forwardProgram modulus nontrivial).dagger.applyNormalized
      (forward toggled)).symm.trans
      (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
        (forwardProgram modulus nontrivial)
        (NormalizedVector.ket ((OutputCopy.encoding modulus.size).encode (initial, toggled))))
  exact UnitaryCircuit.applyNormalized_seq_of_eq (forward target)
    (UnitaryCircuit.applyNormalized_seq_of_eq copied restored)

/-- Zero output yields the mathematical inverse while every original compute field is restored. -/
theorem program_initial_zero (modulus : Nat) (nontrivial : 1 < modulus)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (program modulus nontrivial).applyNormalized
        (NormalizedVector.ket (R := Qubits (OutputCopy.encoding modulus.size).width)
          ((OutputCopy.encoding modulus.size).encode (InitialFrame.initial modulus input, 0))) =
      NormalizedVector.ket (R := Qubits (OutputCopy.encoding modulus.size).width)
        ((OutputCopy.encoding modulus.size).encode
          (InitialFrame.initial modulus input,
            InverseOutput.word modulus input.val positive bounded)) := by
  have actual := program_initial modulus nontrivial input 0 coprime positive bounded
  have zero : output modulus input.val positive bounded 0 =
      InverseOutput.word modulus input.val positive bounded := by
    apply Fin.ext
    exact Nat.zero_xor _
  rw [zero] at actual
  exact actual

/-- The emitted native trace includes the complete inverse, with no dropped history operations. -/
theorem program_eventTrace (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventTrace =
      (CorrectedSchedule.program modulus nontrivial).eventTrace ++
        ((OutputCopy.program modulus.size).eventTrace ++
          (CorrectedSchedule.program modulus nontrivial).eventTrace.reverse) := by
  have forward : (forwardProgram modulus nontrivial).eventTrace =
      (CorrectedSchedule.program modulus nontrivial).eventTrace :=
    UnitaryCircuit.prodLeft_eventTrace (n := modulus.size)
      (CorrectedSchedule.program modulus nontrivial)
  have backward : (forwardProgram modulus nontrivial).dagger.eventTrace =
      (CorrectedSchedule.program modulus nontrivial).eventTrace.reverse :=
    (UnitaryCircuit.dagger_eventTrace (forwardProgram modulus nontrivial)).trans
      (congrArg List.reverse forward)
  have suffix := UnitaryCircuit.seq_eventTrace (OutputCopy.program modulus.size)
    (forwardProgram modulus nontrivial).dagger
  have suffixTrace := suffix.trans
    (congrArg (fun events => (OutputCopy.program modulus.size).eventTrace ++ events) backward)
  exact (UnitaryCircuit.seq_eventTrace (forwardProgram modulus nontrivial)
    ((OutputCopy.program modulus.size).seq (forwardProgram modulus nontrivial).dagger)).trans
      (congrArg₂ List.append forward suffixTrace)

end

end QuantumAlg.MAU.Inversion.SharedEEA.NativeInverse
