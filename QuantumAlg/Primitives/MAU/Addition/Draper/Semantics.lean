/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.MAU.Addition.WordTranslation
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Primitives.MAU.Addition.Draper.Correctness
import all QuantumAlg.Primitives.MAU.Addition.WordTranslation

/-!
# Independent modular translation and the actual Draper operator

The target permutation adds the compiled constant modulo the full word
capacity. It is defined solely from finite-word addition. Equality of the
actual Fourier circuit with this operator extends its basis action to every
superposition, mixed state and external reference [D00, paper.tex:352-365].
-/

namespace QuantumAlg.MAU.Addition.Draper

noncomputable section

/-- The actual QFT/phase/inverse-QFT construction equals the independent translation operator. -/
theorem draperAddition_matrix (width constant : Nat) :
    (additionProgram width constant).matrix = wordTranslation width constant := by
  apply Subtype.ext
  ext output input
  have circuit := congrArg (fun state : NormalizedVector (Qubits width) => state output)
    (draperAddition_apply_ket width constant input)
  have semantic := congrArg (fun state : NormalizedVector (Qubits width) => state output)
    (wordTranslation_ket width constant input)
  simpa only [UnitaryCircuit.applyNormalized, UnitaryOperator.apply_coe,
    UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] using circuit.trans semantic.symm

end

end QuantumAlg.MAU.Addition.Draper
