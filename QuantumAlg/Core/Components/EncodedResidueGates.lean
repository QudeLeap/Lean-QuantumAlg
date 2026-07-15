/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.EncodedBitGates
public import QuantumAlg.Core.Components.BaseGateRealization
public import QuantumAlg.Core.EncodedBasisMap

/-!
# Base-gate witnesses for encoded residue basis maps

This module connects residue-register basis-map contracts to concrete
wire-addressed X/CNOT/Toffoli programs.  The contract still owns the valid-label
and padding policy; the witness adds a `BaseGateProgram` whose raw label action
is the contract permutation.  The folded circuit is therefore the same object
used for canonical-label correctness and resource accounting.
-/

@[expose] public section

namespace QuantumAlg
namespace EncodedResidueBasisMap

noncomputable section

variable {N n : Nat} {E : BinaryResidueEncoding N n}

/-- A same-object base-gate witness for an encoded residue basis-map contract.

The program acts on the full raw `Fin (2^n)` label space.  The contract supplies
the separate proof that canonical labels remain canonical and follow the stated
residue-level action. -/
structure BaseGateWitness (contract : EncodedResidueBasisMap E) where
  /-- Wire-addressed X/CNOT/Toffoli program implementing the raw permutation. -/
  program : BaseGateProgram n
  /-- Correctness of the program on the raw computational-basis label space. -/
  realizesPerm :
    BaseGateProgram.Realizes (BinaryLabelEncoding.finIdentity n) program contract.perm

namespace BaseGateWitness

variable {contract : EncodedResidueBasisMap E}

/-- Empty base-gate witness for the identity residue-register contract. -/
def identity (E : BinaryResidueEncoding N n) :
    BaseGateWitness (EncodedResidueBasisMap.identity E) where
  program := []
  realizesPerm := by
    exact
      { applyLabel_eq := by
          intro x
          rfl }

/-- Sequentially compose two base-gate witnesses over the same residue
register.  The resulting program applies `first` and then `second`, matching
`EncodedResidueBasisMap.sequential`. -/
def sequential {first second : EncodedResidueBasisMap E}
    (firstWitness : BaseGateWitness first)
    (secondWitness : BaseGateWitness second) :
    BaseGateWitness (EncodedResidueBasisMap.sequential first second) where
  program := BaseGateProgram.append firstWitness.program secondWitness.program
  realizesPerm := by
    exact
      { applyLabel_eq := by
          intro x
          change
            BaseGateProgram.applyLabel
                (BaseGateProgram.append firstWitness.program secondWitness.program) x =
              (EncodedResidueBasisMap.sequential first second).perm x
          have hfirst :
              BaseGateProgram.applyLabel firstWitness.program x = first.perm x := by
            simpa using firstWitness.realizesPerm.applyLabel_eq x
          have hsecond :
              BaseGateProgram.applyLabel secondWitness.program (first.perm x) =
                second.perm (first.perm x) := by
            simpa using secondWitness.realizesPerm.applyLabel_eq (first.perm x)
          rw [BaseGateProgram.applyLabel_append]
          rw [hfirst]
          rw [hsecond]
          rfl }

/-- Reverse a base-gate witness to implement the inverse residue-register
contract. -/
def inverse (w : BaseGateWitness contract) :
    BaseGateWitness (EncodedResidueBasisMap.inverse contract) where
  program := BaseGateProgram.inverse w.program
  realizesPerm :=
    BaseGateProgram.Realizes.inverse_of_rightInverse w.realizesPerm (by
      intro x
      simp [EncodedResidueBasisMap.inverse_perm])

/-- Same-Circuit witness over the raw residue-register label space. -/
def rawWitness (w : BaseGateWitness contract) :
    BaseGateSameCircuitWitness (Fin (2 ^ n)) contract.perm where
  encoding := BinaryLabelEncoding.finIdentity n
  program := w.program
  realizes := w.realizesPerm

/-- The program action is the contract permutation on all raw labels. -/
theorem applyLabel_eq_perm (w : BaseGateWitness contract) (x : Fin (2 ^ n)) :
    BaseGateProgram.applyLabel w.program x = contract.perm x :=
  w.realizesPerm.applyLabel_eq x

/-- On canonical residue labels, the same program realizes the contract's
residue-level action. -/
theorem applyLabel_encode_eq (w : BaseGateWitness contract) (z : ZMod N) :
    BaseGateProgram.applyLabel w.program (E.encode z) =
      E.encode (contract.residueMap z) := by
  rw [w.applyLabel_eq_perm]
  exact contract.perm_encode_eq z

/-- Same-Circuit witness over canonical residue labels.  The same raw
wire-addressed program is reused, while the contract supplies the valid-label
and padding policy needed to interpret canonical inputs as residues. -/
def canonicalWitness (w : BaseGateWitness contract) :
    BaseGateSameCircuitWitness (ZMod N) contract.residueMap where
  encoding := BinaryLabelEncoding.ofResidueEncoding E
  program := w.program
  realizes := by
    exact
      { applyLabel_eq := by
          intro z
          simpa using w.applyLabel_encode_eq z }

/-- Lift a canonical residue-register witness into the left component of a
product encoding. -/
def prodLeftCanonicalWitness {Right : Type} (w : BaseGateWitness contract)
    (right : BinaryLabelEncoding Right) :
    BaseGateSameCircuitWitness (ZMod N × Right)
      (fun x : ZMod N × Right => (contract.residueMap x.1, x.2)) :=
  BaseGateSameCircuitWitness.prodLeft w.canonicalWitness right

/-- Lift a canonical residue-register witness into the right component of a
product encoding. -/
def prodRightCanonicalWitness {Left : Type} (left : BinaryLabelEncoding Left)
    (w : BaseGateWitness contract) :
    BaseGateSameCircuitWitness (Left × ZMod N)
      (fun x : Left × ZMod N => (x.1, contract.residueMap x.2)) :=
  BaseGateSameCircuitWitness.prodRight left w.canonicalWitness

/-- The folded witness circuit acts correctly on canonical residue labels. -/
theorem apply_canonical_ket (w : BaseGateWitness contract) (z : ZMod N) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.rawWitness)
        ((PureState.ket (R := Qubits n) (E.encode z) :
          PureState (Qubits n)) :
          StateVector (Qubits n)) =
      (PureState.ket (R := Qubits n) (E.encode (contract.residueMap z)) :
        StateVector (Qubits n)) := by
  have hraw := BaseGateSameCircuitWitness.apply_encoded_ket w.rawWitness (E.encode z)
  rw [contract.perm_encode_eq z] at hraw
  simpa [rawWitness] using hraw

/-- Resource counters are projected from the same folded base-gate program. -/
theorem resources_eq (w : BaseGateWitness contract) :
    (BaseGateSameCircuitWitness.circuit w.rawWitness).resources =
      (BaseGateSameCircuitWitness.profile w.rawWitness).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.rawWitness

/-- Circuit depth is projected from the same folded base-gate program. -/
theorem depth_eq (w : BaseGateWitness contract) :
    (BaseGateSameCircuitWitness.circuit w.rawWitness).depth =
      (BaseGateSameCircuitWitness.profile w.rawWitness).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.rawWitness

/-- Query depth is projected from the same folded base-gate program. -/
theorem queryDepth_eq (w : BaseGateWitness contract) :
    (BaseGateSameCircuitWitness.circuit w.rawWitness).queryDepth =
      (BaseGateSameCircuitWitness.profile w.rawWitness).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.rawWitness

end BaseGateWitness

end

end EncodedResidueBasisMap
end QuantumAlg
