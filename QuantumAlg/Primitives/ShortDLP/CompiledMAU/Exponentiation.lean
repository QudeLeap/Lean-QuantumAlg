/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Layout
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Seeded

/-!
# Actual selected-power member on the exact shared short-DLP workspace

Every fitting positive modulus uses the proved Gidney selected-unit gate
sequence on exactly the public word width. Invalid compilation parameters
have a total identity extension. The source factoring domain selects the
valid branch internally, and the quantum caller supplies no new hypothesis
[VBE95, 9511018.tex:372-416].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth

/-- The exponent word precedes the existing two-word shared arithmetic layout. -/
@[implicit_reducible]
def exponentiationEncoding (bits width : Nat) :
    BinaryLabelEncoding (Fin (2 ^ bits) × WorkspaceRegisters width) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity bits) (workspaceEncoding width)

/-- The actual selected-power program, with a same-carrier total invalid-parameter extension. -/
def exponentiationProgram (bits width N : Nat) (unit : (ZMod N)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (bits + workspaceBits width)).toQuantum :=
  if _positive : 0 < N then
    if fitted : N ≤ 2 ^ width then
      MAU.Exponentiation.Gidney.program bits width ⟨N, Nat.lt_succ_of_le fitted⟩ unit
    else UnitaryCircuit.identity AlgorithmGate.model .empty
      (QubitLayout.canonical (bits + workspaceBits width)).toQuantum
  else UnitaryCircuit.identity AlgorithmGate.model .empty
    (QubitLayout.canonical (bits + workspaceBits width)).toQuantum

/-- Valid compilation parameters select the literal gate program at its declared carrier. -/
lemma exponentiationProgram_valid (bits width N : Nat) (positive : 0 < N)
    (fitted : N ≤ 2 ^ width) (unit : (ZMod N)ˣ) :
    exponentiationProgram bits width N unit =
      MAU.Exponentiation.Gidney.program bits width ⟨N, Nat.lt_succ_of_le fitted⟩ unit := by
  unfold exponentiationProgram
  exact (dif_pos positive).trans (dif_pos fitted)

/-- An oversized modulus selects the literal zero-event identity program. -/
lemma exponentiationProgram_unfitted (bits width N : Nat) (positive : 0 < N)
    (unfitted : ¬ N ≤ 2 ^ width) (unit : (ZMod N)ˣ) :
    exponentiationProgram bits width N unit =
      UnitaryCircuit.identity AlgorithmGate.model .empty
        (QubitLayout.canonical (bits + workspaceBits width)).toQuantum := by
  unfold exponentiationProgram
  exact (dif_pos positive).trans (dif_neg unfitted)

/-- A nonpositive modulus selects the literal zero-event identity program. -/
lemma exponentiationProgram_nonpositive (bits width N : Nat) (nonpositive : ¬ 0 < N)
    (unit : (ZMod N)ˣ) :
    exponentiationProgram bits width N unit =
      UnitaryCircuit.identity AlgorithmGate.model .empty
        (QubitLayout.canonical (bits + workspaceBits width)).toQuantum :=
  dif_neg nonpositive

/-- Total finite selected-unit arithmetic on the same three fields. -/
def exponentiationRawStep (bits width N : Nat) (unit : (ZMod N)ˣ)
    (input : Fin (2 ^ bits) × WorkspaceRegisters width) :
    Fin (2 ^ bits) × WorkspaceRegisters width :=
  if _positive : 0 < N then
    if fitted : N ≤ 2 ^ width then
      MAU.Exponentiation.Gidney.outputForBits ⟨N, Nat.lt_succ_of_le fitted⟩ unit
        (List.ofFn fun bit : Fin bits => bit) input
    else input
  else input

/-- The admitted parameter branch selects the exact all-label arithmetic function. -/
lemma exponentiationRawStep_valid (bits width N : Nat) (positive : 0 < N)
    (fitted : N ≤ 2 ^ width) (unit : (ZMod N)ˣ) :
    exponentiationRawStep bits width N unit =
      MAU.Exponentiation.Gidney.outputForBits ⟨N, Nat.lt_succ_of_le fitted⟩ unit
        (List.ofFn fun bit : Fin bits => bit) := by
  funext input
  exact (dif_pos positive).trans (dif_pos fitted)

/-- The oversized-modulus action is the identity on every complete register label. -/
lemma exponentiationRawStep_unfitted (bits width N : Nat) (positive : 0 < N)
    (unfitted : ¬ N ≤ 2 ^ width) (unit : (ZMod N)ˣ) :
    exponentiationRawStep bits width N unit = id := by
  funext input
  exact (dif_pos positive).trans (dif_neg unfitted)

/-- The nonpositive-modulus action is the identity on every complete register label. -/
lemma exponentiationRawStep_nonpositive (bits width N : Nat) (nonpositive : ¬ 0 < N)
    (unit : (ZMod N)ˣ) : exponentiationRawStep bits width N unit = id := by
  funext input
  exact dif_neg nonpositive

/-- The literal selected-power gate sequence realizes its complete finite action. -/
lemma exponentiationRaw_realizes (bits width N : Nat) (unit : (ZMod N)ˣ) :
    UnitaryCircuit.Realizes (exponentiationEncoding bits width)
      (exponentiationProgram bits width N unit) environment
      (exponentiationRawStep bits width N unit) := by
  by_cases positive : 0 < N
  · by_cases fitted : N ≤ 2 ^ width
    · rw [exponentiationProgram_valid bits width N positive fitted unit,
        exponentiationRawStep_valid bits width N positive fitted unit]
      exact MAU.Exponentiation.Gidney.gidneyExponent_realizes bits width
        ⟨N, Nat.lt_succ_of_le fitted⟩ unit
    · rw [exponentiationProgram_unfitted bits width N positive fitted unit,
        exponentiationRawStep_unfitted bits width N positive fitted unit]
      exact UnitaryCircuit.Realizes.identity AlgorithmGate.model .empty
        (exponentiationEncoding bits width) environment
  · rw [exponentiationProgram_nonpositive bits width N positive unit,
      exponentiationRawStep_nonpositive bits width N positive unit]
    exact UnitaryCircuit.Realizes.identity AlgorithmGate.model .empty
      (exponentiationEncoding bits width) environment

/-- Any canonical unit seed is multiplied exactly and the same shared auxiliary is returned. -/
lemma exponentiationProgram_seeded (bits width N : Nat) (positive : 0 < N)
    (fitted : N ≤ 2 ^ width) (unit seed : (ZMod N)ˣ) (exponent : Fin (2 ^ bits)) :
    (exponentiationProgram bits width N unit).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (bits + workspaceBits width)).basisEquiv.symm
            ((exponentiationEncoding bits width).encode
              (exponent, cleanWorkspace width N seed)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (bits + workspaceBits width)).basisEquiv.symm
          ((exponentiationEncoding bits width).encode
            (exponent, cleanWorkspace width N (unit ^ exponent.val * seed)))) := by
  rw [exponentiationProgram_valid bits width N positive fitted unit]
  simp only [cleanWorkspace_valid width N positive fitted]
  exact MAU.Exponentiation.Gidney.gidneyExponent_seeded bits width
    ⟨N, Nat.lt_succ_of_le fitted⟩ positive unit seed exponent

/-- The semantic all-label action has the same canonical seed endpoint. -/
lemma exponentiationRawStep_cleanEndpoint (bits width N : Nat) (unit seed : (ZMod N)ˣ)
    (exponent : Fin (2 ^ bits)) (nontrivial : 1 < N) (fits : N < 2 ^ width) :
    exponentiationRawStep bits width N unit (exponent, cleanWorkspace width N seed) =
      (exponent, cleanWorkspace width N (unit ^ exponent.val * seed)) := by
  have actual := (exponentiationRaw_realizes (environment := OracleModel.emptyInterpretation)
    bits width N unit).apply_encoded_ket
    (exponent, cleanWorkspace width N seed)
  have canonical := exponentiationProgram_seeded
    (environment := OracleModel.emptyInterpretation) bits width N
    (Nat.zero_lt_of_lt nontrivial) (Nat.le_of_lt fits) unit seed exponent
  have same := actual.symm.trans canonical
  exact (exponentiationEncoding bits width).encode_injective
    ((QubitLayout.canonical (bits + workspaceBits width)).basisEquiv.symm.injective
      (NormalizedVector.ket_injective same))

end

end QuantumAlg.ShortDLP.CompiledMAU
