/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Signed.Trajectory

/-!
# Finite original-width encoding of the signed EEA inverse

The retained terminal coefficient and Iter select the source's output
[LYL+26, sec_EEA/sub_4phase.tex:123-125]. Its bound follows from the
original macro invariant and conserved modulus. Thus the original n-bit
output encoding needs no additional caller fit assumption. This is a
pure arithmetic encoding and does not stand for a circuit operation.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.InverseOutput

/-- The original mathematical signed coefficient fits the input word's full binary capacity. -/
theorem value_fits (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    SignedInvariant.output modulus (TerminalPadding.finalState modulus input)
      (SignedTrajectory.finalIteration modulus input) < 2 ^ modulus.size := by
  have coefficient := (Capacity.iteration_fields_le _ modulus
    (TerminalPadding.final_admissible modulus input positive bounded)
    (TerminalPadding.final_balance modulus input)).2.2.2
  apply lt_of_le_of_lt _ (Nat.lt_size_self modulus)
  unfold SignedInvariant.output
  split
  · exact coefficient
  · exact Nat.sub_le _ _

/-- The source's corrected mathematical output in the original n-bit finite word. -/
def word (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    Fin (2 ^ modulus.size) :=
  ⟨SignedInvariant.output modulus (TerminalPadding.finalState modulus input)
    (SignedTrajectory.finalIteration modulus input), value_fits modulus input positive bounded⟩

/-- The encoded mathematical word is an inverse on the coprime positive-residue domain. -/
theorem word_product (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    (input : ZMod modulus) * ((word modulus input positive bounded).val : ZMod modulus) = 1 :=
  SignedTrajectory.final_product modulus input coprime positive bounded

end QuantumAlg.NumberTheory.SharedEEA.InverseOutput
