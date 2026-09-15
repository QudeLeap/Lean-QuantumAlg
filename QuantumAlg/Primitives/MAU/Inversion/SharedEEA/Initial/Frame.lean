/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.Length.Frame

/-!
# Actual input folding followed by actual divisor-length computation

The initial basis specification is the source's Work1 `100,p`, Work2
`000,x`, coefficient length one, and zero quotient length, shift, phase
flags, retained Iter, and Ctrl [LYL+26, sec_EEA/sub_4phase.tex:104-117].
The divisor length also starts at zero, and the native length writer runs
on the actual Work2 after the native fold. This corrects the source's
initial ordering: at `p=17,x=16`, computing length before folding would
leave five although the folded divisor is one.

Only the modulus selects the program. The input below is an encoded
basis label used to prove the action of that fixed program, not an
input-dependent preparation parameter. Allocation of the fixed auxiliary
state beside an arbitrary quantum input remains an execution-boundary
obligation; these exact all-frame native program laws supply its coherent
arithmetic component.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InitialFrame

noncomputable section

open EncodedBit InitialLengthSemantics

/-- Embed the original input word in the existing Work2, with three leading zero bits. -/
def inputWord (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    Fin (2 ^ FoldSourceProgram.wordWidth modulus) :=
  ⟨input.val, input.isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (by unfold FoldSourceProgram.wordWidth; omega))⟩

/-- The literal initial basis frame; no input-dependent value is prepared in a length register. -/
def initial (modulus : Nat) (input : Fin (2 ^ modulus.size)) : Registers modulus.size :=
  { firstWord := BitVec.ofNat (modulus.size + 3) (4 * 2 ^ modulus.size + modulus)
    secondWord := BitVec.equivFin.symm (inputWord modulus input)
    coefficientLength := BitVec.ofNat modulus.size.size 1
    quotientLength := 0#modulus.size.size
    divisorLength := 0#modulus.size.size
    shift := 0#modulus.size.size
    flags := ⟨false, false, false, false⟩
    control := false }

/-- The entire padded input word has the original value, not a truncated or recomputed input. -/
theorem initial_secondWord (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    (initial modulus input).secondWord.toNat = input.val := rfl

/-- The source's fixed Work1 pattern fits in its real word for every modulus. -/
theorem initial_firstWord (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    (initial modulus input).firstWord.toNat = 4 * 2 ^ modulus.size + modulus := by
  have modulusFits := Nat.lt_size_self modulus
  have positive := Nat.two_pow_pos modulus.size
  have fits : 4 * 2 ^ modulus.size + modulus < 2 ^ (modulus.size + 3) := by
    rw [Nat.pow_add]
    norm_num
    omega
  exact Nat.mod_eq_of_lt fits

/-- The first stage is the actual full-frame fold, retaining the complement history. -/
def folded (modulus : Nat) (input : Fin (2 ^ modulus.size)) : Registers modulus.size :=
  FoldProgram.step modulus (initial modulus input)

/-- The second stage is exactly the step list of the actual length writer. -/
def result (modulus : Nat) (input : Fin (2 ^ modulus.size)) : Registers modulus.size :=
  GateSpec.stepList (InitialLengthWrite.gates modulus.size) (folded modulus input)

/-- One fixed actual native program folds Work2 before computing its current divisor length. -/
def program (modulus : Nat) : UnitaryCircuit (Qubits (encoding modulus.size).width) :=
  (FoldProgram.program modulus).seq (InitialLengthWrite.program modulus.size)

/-- Complete action on all frames, including arbitrary incoming fields outside the input domain. -/
theorem program_realizes (modulus : Nat) :
    UnitaryCircuit.Realizes (encoding modulus.size) (program modulus)
      (fun state => GateSpec.stepList (InitialLengthWrite.gates modulus.size)
        (FoldProgram.step modulus state)) :=
  (FoldProgram.program_realizes modulus).seq
    (GateSpec.realizesList (InitialLengthWrite.gates modulus.size))

/-- The encoded initial basis is sent to the actual two-stage result with exact amplitudes. -/
theorem program_initial (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    (program modulus).applyNormalized
        (NormalizedVector.ket (R := Qubits (encoding modulus.size).width)
          ((encoding modulus.size).encode (initial modulus input))) =
      NormalizedVector.ket (R := Qubits (encoding modulus.size).width)
        ((encoding modulus.size).encode (result modulus input)) :=
  (program_realizes modulus).apply_encoded_ket (initial modulus input)

/-- The actual fold produces both the mathematical folded value and its retained history bit. -/
theorem folded_record_value (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (bounded : input.val < modulus) :
    ((folded modulus input).flags.iteration, (folded modulus input).secondWord.toNat) =
      NumberTheory.SharedEEA.foldInput modulus input.val :=
  FoldSourceProgram.step_foldInput modulus (inputWord modulus input) false bounded

private theorem folded_value_fits (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (bounded : input.val < modulus) :
    (NumberTheory.SharedEEA.foldInput modulus input.val).2 < 2 ^ modulus.size := by
  by_cases complemented : modulus / 2 < input.val
  · simp only [NumberTheory.SharedEEA.foldInput, if_pos complemented]
    exact (Nat.sub_le modulus input.val).trans_lt (Nat.lt_size_self modulus)
  · simp only [NumberTheory.SharedEEA.foldInput, if_neg complemented]
    exact (Nat.le_of_lt bounded).trans_lt (Nat.lt_size_self modulus)

/-- Reading the actual low payload after folding gives the same complete folded residue. -/
theorem folded_payload (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (bounded : input.val < modulus) :
    payloadValue (folded modulus input) =
      (NumberTheory.SharedEEA.foldInput modulus input.val).2 := by
  have value := congrArg (fun pair : Bool × Nat => pair.2)
    (folded_record_value modulus input bounded)
  change (folded modulus input).secondWord.toNat = _ at value
  change (folded modulus input).secondWord.toNat % 2 ^ modulus.size = _
  rw [value]
  exact Nat.mod_eq_of_lt (folded_value_fits modulus input bounded)

/-- The entire result differs from the actual folded frame only by the newly computed length. -/
theorem result_eq (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    result modulus input =
      { folded modulus input with
        divisorLength := BitVec.ofNat modulus.size.size
          (payloadValue (folded modulus input)).size } := by
  rw [result, InitialLengthFrame.gates_step_eq]
  have zero : (folded modulus input).divisorLength = 0#modulus.size.size := rfl
  rw [zero, BitVec.zero_xor]

/-- The actual length writer retains the folded divisor and its complement history together. -/
theorem result_record_value (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (bounded : input.val < modulus) :
    ((result modulus input).flags.iteration, (result modulus input).secondWord.toNat) =
      NumberTheory.SharedEEA.foldInput modulus input.val := by
  rw [result_eq]
  exact folded_record_value modulus input bounded

/-- The stored divisor length is computed from the actual folded value, including equality. -/
theorem result_divisorLength (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (bounded : input.val < modulus) :
    (result modulus input).divisorLength = BitVec.ofNat modulus.size.size
      (NumberTheory.SharedEEA.foldInput modulus input.val).2.size := by
  rw [result_eq]
  change BitVec.ofNat modulus.size.size (payloadValue (folded modulus input)).size = _
  rw [folded_payload modulus input bounded]

/-- The exact current length fits in its original finite field, without modular truncation. -/
theorem result_divisorLength_toNat (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (bounded : input.val < modulus) :
    (result modulus input).divisorLength.toNat =
      (NumberTheory.SharedEEA.foldInput modulus input.val).2.size := by
  have sizeBound := Nat.size_le.mpr (folded_value_fits modulus input bounded)
  rw [result_divisorLength modulus input bounded, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (sizeBound.trans_lt (Nat.lt_size_self modulus.size))

/-- The actual first word remains the original fixed source pattern after both native stages. -/
theorem result_firstWord (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    (result modulus input).firstWord = (initial modulus input).firstWord := by
  rw [result_eq]
  exact FoldProgram.step_firstWord modulus (initial modulus input)

/-- The original source domain alone gives the invariant needed by the later four-phase loop. -/
theorem result_initial_admissible (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (NumberTheory.SharedEEA.IterationState.initial modulus
      (result modulus input).secondWord.toNat).Admissible := by
  have value := congrArg (fun pair : Bool × Nat => pair.2)
    (result_record_value modulus input bounded)
  change (result modulus input).secondWord.toNat = _ at value
  rw [value]
  exact NumberTheory.SharedEEA.folded_initial_admissible modulus input.val positive bounded

/-- The history and the actual folded residue reconstruct the original residue exactly. -/
theorem result_unfoldInput (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (bounded : input.val < modulus) :
    NumberTheory.SharedEEA.unfoldInput modulus
      ((result modulus input).flags.iteration, (result modulus input).secondWord.toNat) =
        input.val := by
  rw [result_record_value modulus input bounded]
  exact NumberTheory.SharedEEA.unfoldInput_foldInput modulus input.val (Nat.le_of_lt bounded)

/-- Both real native stages remain in the actual trace in the required data-dependency order. -/
theorem program_eventTrace (modulus : Nat) :
    (program modulus).eventTrace = (FoldSourceProgram.program modulus).eventTrace ++
      (InitialLengthWrite.program modulus.size).eventTrace := by
  rw [program, UnitaryCircuit.seq_eventTrace, FoldProgram.program_eventTrace]

end

end QuantumAlg.MAU.Inversion.SharedEEA.InitialFrame
