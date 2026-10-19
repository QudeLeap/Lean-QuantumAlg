/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.PortProgram
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.CorrectedSchedule
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Output.PortProgram
import all QuantumAlg.Util.NumberTheory.SharedEEA.InverseOutput

/-!
# Actual shared-EEA forward interface with its large port returned to zero

In-place division reuses its original two large registers and keeps the
small EEA history until the same inverse is applied using the reset
measurement register as the large workspace
[LYL+26, sec_point_add/sec_point_add.tex:45-79].

The actual program below first loads the source's fixed constants into
the supplied zero large port, then runs the proved fixed shared schedule,
then executes the real output SWAPs and terminal constant X gates.
Its inverse is on the original Work2 input port. Work1's first n physical
positions return to zero, its two high clock positions retain the full
displacement history, and no extra n-bit output bank is used.

Every coprime positive residue below a nontrivial modulus is covered. Exact
normalized-ket equalities retain all amplitudes and supply coherent
reference extensions; no additional cleanliness or fit condition is
imposed on the arithmetic input domain.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InPlaceForward

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open NumberTheory.SharedEEA

/-- Fixed load, the same actual corrected schedule, and literal output-port operations. -/
def program (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding modulus.size).width).toQuantum :=
  (InitialPortProgram.program modulus).seq
    ((CorrectedSchedule.program modulus nontrivial).seq (OutputPortProgram.program modulus))

/-- Full final physical state retains every component of the actual small forward history. -/
def result (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    Registers modulus.size :=
  OutputPortProgram.step modulus (CorrectedSchedule.result modulus input positive bounded)

/-- The exact actual forward ket from the zero large port for coprime positive residues. -/
lemma program_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
            ((encoding modulus.size).encode (InitialPortProgram.inputFrame modulus input)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
          ((encoding modulus.size).encode (result modulus input.val positive bounded))) := by
  rw [program, UnitaryCircuit.applyNormalized_seq,
    InitialPortProgram.program_initial, UnitaryCircuit.applyNormalized_seq,
    CorrectedSchedule.program_initial modulus nontrivial input coprime positive bounded,
    (OutputPortProgram.program_realizes modulus).apply_encoded_ket]
  rfl

private lemma corrected_workspace (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    let before := CorrectedSchedule.result modulus input positive bounded
    PaddingClock.main before.firstWord = PaddingClock.main (TerminalPadding.terminalWord modulus) ∧
      PaddingClock.last before.firstWord =
        PaddingClock.last (TerminalPadding.terminalWord modulus) := by
  let terminal := NativeSchedule.terminalFrame modulus input positive bounded
  have terminalWord : terminal.firstWord = TerminalPadding.terminalWord modulus :=
    TerminalPadding.final_firstWord modulus input coprime positive bounded
  have retained : (CorrectedSchedule.result modulus input positive bounded).firstWord =
      (TerminalPosition.frame terminal (QuotientSchedule.padding modulus input)).firstWord :=
    (CorrectedSchedule.result_retained modulus input positive bounded).1
  have complement := TerminalPosition.frame_untouched terminal
    (QuotientSchedule.padding modulus input)
  exact ⟨((congrArg PaddingClock.main retained).trans complement.1).trans
      (congrArg PaddingClock.main terminalWord),
    ((congrArg PaddingClock.last retained).trans complement.2).trans
      (congrArg PaddingClock.last terminalWord)⟩

/-- Exact whole Work1 is zero main, retained two-bit history, and an unloaded last bit. -/
lemma result_firstWord (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    (result modulus input positive bounded).firstWord =
      ((0#modulus.size ++
        PaddingClock.high (CorrectedSchedule.result modulus input positive bounded).firstWord) ++
          0#1) :=
  WordUnloading.unload_terminal modulus
    (CorrectedSchedule.result modulus input positive bounded).firstWord
    (corrected_workspace modulus input coprime positive bounded).1
    (corrected_workspace modulus input coprime positive bounded).2

/-- The n physically reusable Work1 positions are all zero on every coprime positive input. -/
lemma result_large_zero (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    PaddingClock.main (result modulus input positive bounded).firstWord = 0#modulus.size := by
  rw [result_firstWord modulus input coprime positive bounded]
  simp only [PaddingClock.main, BitVec.extractLsb'_append_eq_left]

/-- Each actual large-workspace wire reads zero; this is not a dimension-only port assertion. -/
lemma result_large_bit (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) (index : Fin modulus.size) :
    (result modulus input positive bounded).firstWord.getMsbD index.val = false := by
  rw [WordUnloading.main_bit _ _ index.isLt,
    result_large_zero modulus input coprime positive bounded]
  exact BitVec.getMsbD_zero

/-- The two original high-counter bits retain their exact forward values. -/
lemma result_high_clock (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    PaddingClock.high (result modulus input positive bounded).firstWord =
      PaddingClock.high (CorrectedSchedule.result modulus input positive bounded).firstWord := by
  rw [result_firstWord modulus input coprime positive bounded]
  simp only [PaddingClock.high, BitVec.extractLsb'_append_eq_left,
    BitVec.extractLsb'_append_eq_right]

/-- Every original length, low counter, phase flag, parity bit, and Ctrl is retained. -/
lemma result_retained (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    let before := CorrectedSchedule.result modulus input positive bounded
    let after := result modulus input positive bounded
    after.coefficientLength = before.coefficientLength ∧
      after.quotientLength = before.quotientLength ∧
      after.divisorLength = before.divisorLength ∧ after.shift = before.shift ∧
      after.flags = before.flags ∧ after.control = before.control :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The complete high-plus-low clock is retained, without discarding either reused position. -/
lemma result_clock (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    ExtendedClockRegisters.clock (result modulus input positive bounded) =
      ExtendedClockRegisters.clock (CorrectedSchedule.result modulus input positive bounded) := by
  change PaddingClock.high (result modulus input positive bounded).firstWord ++
    (CorrectedSchedule.result modulus input positive bounded).shift = _
  rw [result_high_clock modulus input coprime positive bounded]
  rfl

/-- The output's numerical value is the independent exact finite-word modular inverse. -/
lemma result_value (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    (result modulus input positive bounded).secondWord.toNat =
      (InverseOutput.word modulus input positive bounded).val :=
  CorrectedSchedule.result_value modulus input positive bounded

/-- Entire Work2 agrees with the original padded input port now holding the inverse. -/
lemma result_input_port (modulus input : Nat)
    (positive : 0 < input) (bounded : input < modulus) :
    (result modulus input positive bounded).secondWord =
      (InitialFrame.initial modulus
        (InverseOutput.word modulus input positive bounded)).secondWord :=
  BitVec.eq_of_toNat_eq (result_value modulus input positive bounded)

/-- The actual returned same-port value is an inverse for every coprime positive input. -/
lemma result_product (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    (input : ZMod modulus) * ((result modulus input positive bounded).secondWord.toNat :
      ZMod modulus) = 1 :=
  CorrectedSchedule.result_product modulus input coprime positive bounded

/-- The same complete adjoint recovers the original input and its fixed small initialization. -/
lemma dagger_result (modulus : Nat) (nontrivial : 1 < modulus)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    ((program modulus nontrivial).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
            ((encoding modulus.size).encode (result modulus input.val positive bounded)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
          ((encoding modulus.size).encode (InitialPortProgram.inputFrame modulus input))) := by
  have forward := program_initial
    (environment := environment) modulus nontrivial input coprime positive bounded
  exact (congrArg (fun state => ((program modulus nontrivial).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment state)
        forward).symm.trans
    (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
      (program modulus nontrivial)
      ((program modulus nontrivial).dagger (AlgorithmGate.oracleFreeAdjoints .empty))
      (by rw [UnitaryCircuit.dagger_matrix,
      Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
        environment]; exact Unitary.star_eq_inv _) _)

end

end QuantumAlg.MAU.Inversion.SharedEEA.InPlaceForward
