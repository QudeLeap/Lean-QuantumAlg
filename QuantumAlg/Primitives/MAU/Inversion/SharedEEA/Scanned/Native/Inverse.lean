/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.Corrected
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.Copy
import all QuantumAlg.Util.NumberTheory.SharedEEA.InverseOutput

/-!
# Actual pruned inverse with complete original-frame and pool restoration

Execute the new actual forward loop, decoder and correction. Copy the
corrected original Work2 word into the arbitrary target with actual
CNOTs. Execute the literal native adjoint of that same whole forward
program. Every original history bit and every pool bit returns to its
initial state; only the mathematical inverse is xored into the target.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeInverse

noncomputable section

open NumberTheory.SharedEEA

/-- The complete actual forward computation precedes the arbitrary output word. -/
def forwardProgram (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).toQuantum :=
  UnitaryCircuit.prodLeft (n := modulus.size) (CorrectedSchedule.program modulus nontrivial)

/-- The same complete actual forward computation is reversed after the literal output CNOTs. -/
def program (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).toQuantum :=
  (forwardProgram modulus nontrivial).seq ((OutputCopy.program modulus.size).seq
    ((forwardProgram modulus nontrivial).dagger (AlgorithmGate.oracleFreeAdjoints .empty)))

/-- The independent mathematical inverse is xored into an arbitrary original target value. -/
def output (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus)
    (target : Fin (2 ^ modulus.size)) : Fin (2 ^ modulus.size) :=
  ⟨target.val ^^^ (InverseOutput.word modulus input positive bounded).val,
    Nat.xor_lt_two_pow target.isLt (InverseOutput.word modulus input positive bounded).isLt⟩

private lemma copied_value (modulus input : Nat)
    (positive : 0 < input) (bounded : input < modulus) :
    SharedEEA.OutputCopy.value (SharedEEA.CorrectedSchedule.result modulus input positive bounded) =
      InverseOutput.word modulus input positive bounded := by
  apply Fin.ext
  rw [SharedEEA.OutputCopy.value_of_fits _
    (SharedEEA.CorrectedSchedule.result_fits_output modulus input positive bounded),
    SharedEEA.CorrectedSchedule.result_value]
  rfl

/-- Every original compute field and the same entire pool are restored beside the inverse XOR. -/
lemma program_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (input target : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false) :
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((OutputCopy.encoding modulus.size).encode
            ((InitialFrame.initial modulus input, pool), target)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((OutputCopy.encoding modulus.size).encode
          ((InitialFrame.initial modulus input, pool),
            output modulus input.val positive bounded target))) := by
  let initial : Data modulus.size := (InitialFrame.initial modulus input, pool)
  let computed : Data modulus.size :=
    (SharedEEA.CorrectedSchedule.result modulus input.val positive bounded, pool)
  let toggled := output modulus input.val positive bounded target
  let ket (value : OutputCopy.Data modulus.size) :=
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((OutputCopy.encoding modulus.size).encode value))
  have forward (value : Fin (2 ^ modulus.size)) :
      (forwardProgram modulus nontrivial).applyNormalized environment (ket (initial, value)) =
        ket (computed, value) :=
    UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
      (encoding modulus.size) (BinaryLabelEncoding.finIdentity modulus.size)
      (CorrectedSchedule.program modulus nontrivial) initial computed value
      (CorrectedSchedule.program_initial modulus nontrivial environment input coprime positive
        bounded pool addressZero prefixZero borrowZero)
  have copied : (OutputCopy.program modulus.size).applyNormalized environment
      (ket (computed, target)) = ket (computed, toggled) := by
    rw [(OutputCopy.program_realizes modulus.size).apply_encoded_ket]
    have value := copied_value modulus input.val positive bounded
    have fields : OutputCopy.step (computed, target) = (computed, toggled) := by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        exact congrArg (fun word : Fin (2 ^ modulus.size) => target.val ^^^ word.val) value
    rw [fields]
  have restored : ((forwardProgram modulus nontrivial).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment
        (ket (computed, toggled)) = ket (initial, toggled) :=
    (congrArg (fun state => ((forwardProgram modulus nontrivial).dagger
        (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment state)
      (forward toggled)).symm.trans
      (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
        (forwardProgram modulus nontrivial)
        ((forwardProgram modulus nontrivial).dagger (AlgorithmGate.oracleFreeAdjoints .empty))
        (by
          rw [UnitaryCircuit.dagger_matrix,
            Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
              environment]
          exact Unitary.star_eq_inv _)
        (ket (initial, toggled)))
  exact UnitaryCircuit.applyNormalized_seq_of_eq (forward target)
    (UnitaryCircuit.applyNormalized_seq_of_eq copied restored)

/-- Zero output receives the mathematical inverse with every source and pool field restored. -/
lemma program_initial_zero (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false) :
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((OutputCopy.encoding modulus.size).encode
            ((InitialFrame.initial modulus input, pool), 0)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((OutputCopy.encoding modulus.size).encode
          ((InitialFrame.initial modulus input, pool),
            InverseOutput.word modulus input.val positive bounded))) := by
  have actual := program_initial modulus nontrivial environment input 0 coprime positive bounded
    pool addressZero prefixZero borrowZero
  have zero : output modulus input.val positive bounded 0 =
      InverseOutput.word modulus input.val positive bounded := by
    apply Fin.ext
    exact Nat.zero_xor _
  rw [zero] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeInverse
