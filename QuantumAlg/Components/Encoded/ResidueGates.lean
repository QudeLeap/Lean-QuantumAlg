/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Components.Encoded.BasisMap.Contract

/-!
# Circuit witnesses for encoded residue basis maps

This module connects residue-register basis-map contracts to actual Core
circuits.  The contract still owns the valid-label and padding policy; the
witness records the circuit whose unitary action on encoded basis kets is the
contract permutation.  Modules that require an X/CNOT/Toffoli decomposition
must carry that stronger local provenance separately.
-/

section

namespace QuantumAlg
namespace EncodedResidueBasisMap

noncomputable section

variable {N n : Nat} {E : BinaryResidueEncoding N n}

/-- A same-object circuit witness for an encoded residue basis-map contract.

The program acts on the full raw `Fin (2^n)` label space.  The contract supplies
the separate proof that canonical labels remain canonical and follow the stated
residue-level action. -/
structure BaseGateWitness (contract : EncodedResidueBasisMap E) where
  /-- Actual circuit implementing the raw permutation. -/
  program : UnitaryCircuit (Qubits n)
  /-- Correctness of the program on the raw computational-basis label space. -/
  realizesPerm :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.finIdentity n) program contract.perm

namespace BaseGateWitness

variable {contract : EncodedResidueBasisMap E}

/-- Empty base-gate witness for the identity residue-register contract. -/
def identity (E : BinaryResidueEncoding N n) :
    BaseGateWitness (EncodedResidueBasisMap.identity E) where
  program := UnitaryCircuit.identity (Qubits n) [] (by simp)
  realizesPerm := UnitaryCircuit.Realizes.identity (BinaryLabelEncoding.finIdentity n)

/-- Sequentially compose two base-gate witnesses over the same residue
register.  The resulting program applies `first` and then `second`, matching
`EncodedResidueBasisMap.sequential`. -/
def sequential {first second : EncodedResidueBasisMap E}
    (firstWitness : BaseGateWitness first)
    (secondWitness : BaseGateWitness second) :
    BaseGateWitness (EncodedResidueBasisMap.sequential first second) where
  program := UnitaryCircuit.seq firstWitness.program secondWitness.program
  realizesPerm := by
    simpa [EncodedResidueBasisMap.sequential, Function.comp_def] using
      UnitaryCircuit.Realizes.seq firstWitness.realizesPerm secondWitness.realizesPerm

/-- Reverse a base-gate witness to implement the inverse residue-register
contract. -/
def inverse (w : BaseGateWitness contract) :
    BaseGateWitness (EncodedResidueBasisMap.inverse contract) where
  program := w.program.dagger
  realizesPerm :=
    UnitaryCircuit.Realizes.dagger_of_rightInverse w.realizesPerm (by
      intro x
      simp [EncodedResidueBasisMap.inverse_perm])

/-- The actual circuit action is the contract permutation on all raw basis
labels. -/
theorem applyNormalized_ket_eq_perm (w : BaseGateWitness contract)
    (x : Fin (2 ^ n)) :
    w.program.applyNormalized (NormalizedVector.ket x) =
      NormalizedVector.ket (contract.perm x) :=
  w.realizesPerm.apply_encoded_ket x

/-- The same actual circuit realizes the residue-level action on canonical
encoded inputs. -/
theorem canonicalRealizes (w : BaseGateWitness contract) :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.ofResidueEncoding E)
      w.program contract.residueMap where
  apply_encoded_ket := by
    intro z
    calc
      w.program.applyNormalized (NormalizedVector.ket (E.encode z)) =
          NormalizedVector.ket (contract.perm (E.encode z)) :=
        w.applyNormalized_ket_eq_perm (E.encode z)
      _ = NormalizedVector.ket (E.encode (contract.residueMap z)) := by
        rw [contract.perm_encode_eq]

/-- Pointwise canonical-input form of `canonicalRealizes`. -/
theorem applyNormalized_encode_eq (w : BaseGateWitness contract) (z : ZMod N) :
    w.program.applyNormalized (NormalizedVector.ket (E.encode z)) =
      NormalizedVector.ket (E.encode (contract.residueMap z)) :=
  w.canonicalRealizes.apply_encoded_ket z

end BaseGateWitness

end

end EncodedResidueBasisMap
end QuantumAlg

end
