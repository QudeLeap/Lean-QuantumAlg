/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Access.Specification
import Mathlib.Logic.Equiv.Fintype

/-!
# Canonical ideal elliptic-curve DLP access

The mathematical `U_{P,Q}` action is an injective map on the encoded semantic
basis.  This module extends that map to a permutation of the complete qubit
basis and packages the resulting permutation unitary as the canonical opaque
ECDLP access.  The construction fixes ideal oracle semantics only; a
generic-domain gate implementation and its exceptional-trace analysis remain
separate concerns [PZ03, ecc.tex:448-466,495-556].
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ECDLP
namespace Canonical
namespace IdealAccess

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Basis labels for either oversampled exponent register. -/
abbrev ExponentLabel (I : ECDLPInstance E) :=
  Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I))

/-- Semantic inputs on which the ideal group action is prescribed. -/
abbrev OracleDomain (I : ECDLPInstance E) :=
  (ExponentLabel I × ExponentLabel I) × GroupPoint E

/-- Computational basis of the intrinsic ECDLP register. -/
abbrev OracleBasis (I : ECDLPInstance E) :=
  Fin (2 ^ Layout.totalQubits I)

/-- Encoded source label of one semantic oracle input. -/
def sourceLabel (I : ECDLPInstance E) (input : OracleDomain I) :
    OracleBasis I :=
  basisIndex I input.1.1 input.1.2 input.2

/-- Encoded target label after the prescribed elliptic-curve group shift. -/
def targetLabel (I : ECDLPInstance E) (input : OracleDomain I) :
    OracleBasis I :=
  basisIndex I input.1.1 input.1.2
    (input.2 * (problem I).toSourceScope.oracleMultiplier
      input.1.1.val input.1.2.val)

/-- The canonical semantic encoding is injective. -/
lemma sourceLabel_injective (I : ECDLPInstance E) :
    Function.Injective (sourceLabel I) := by
  intro left right equality
  apply (Layout.fullEncoding I).encode_injective
  apply Fin.ext
  exact Fin.ext_iff.mp equality

/-- The target group shift is injective on the semantic domain. -/
lemma targetLabel_injective (I : ECDLPInstance E) :
    Function.Injective (targetLabel I) := by
  rintro ⟨⟨leftA, leftB⟩, leftPoint⟩
    ⟨⟨rightA, rightB⟩, rightPoint⟩ equality
  have outerEquality :
      ((leftA, leftB),
          leftPoint * (problem I).toSourceScope.oracleMultiplier
            leftA.val leftB.val) =
        ((rightA, rightB),
          rightPoint * (problem I).toSourceScope.oracleMultiplier
            rightA.val rightB.val) :=
    (Layout.fullEncoding I).encode_injective (by
      apply Fin.ext
      exact Fin.ext_iff.mp equality)
  have exponentEquality : (leftA, leftB) = (rightA, rightB) :=
    congrArg Prod.fst outerEquality
  cases exponentEquality
  have pointEquality :
      leftPoint * (problem I).toSourceScope.oracleMultiplier
          leftA.val leftB.val =
        rightPoint * (problem I).toSourceScope.oracleMultiplier
          leftA.val leftB.val :=
    congrArg Prod.snd outerEquality
  have : leftPoint = rightPoint := mul_right_cancel pointEquality
  cases this
  rfl

noncomputable instance instFiniteOracleDomain (I : ECDLPInstance E) :
    Finite (OracleDomain I) :=
  Finite.of_injective (sourceLabel I) (sourceLabel_injective I)

/-- A full-basis permutation extending the prescribed semantic action. -/
def oraclePermutation (I : ECDLPInstance E) : Equiv.Perm (OracleBasis I) :=
  Classical.choose
    (Equiv.Perm.exists_extending_pair (sourceLabel I) (targetLabel I)
      (sourceLabel_injective I) (targetLabel_injective I))

/-- The extension agrees with the source action on every semantic label. -/
lemma oraclePermutation_sourceLabel (I : ECDLPInstance E)
    (input : OracleDomain I) :
    oraclePermutation I (sourceLabel I input) = targetLabel I input :=
  (Classical.choose_spec
    (Equiv.Perm.exists_extending_pair (sourceLabel I) (targetLabel I)
      (sourceLabel_injective I) (targetLabel_injective I))) input

/-- Ideal `U_{P,Q}` operator induced by the complete basis permutation. -/
def operator (I : ECDLPInstance E) :
    UnitaryOperator (Qubits (Layout.totalQubits I)) :=
  UnitaryOperator.ofPerm (oraclePermutation I).symm

/-- The permutation operator has the canonical group-action basis semantics. -/
lemma operator_basisAction (I : ECDLPInstance E)
    (left right : ExponentLabel I) (workspace : GroupPoint E) :
    (operator I).apply
        (NormalizedVector.ket (R := Qubits (Layout.totalQubits I))
          (basisIndex I left right workspace)) =
      NormalizedVector.ket (R := Qubits (Layout.totalQubits I))
        (basisIndex I left right
          (workspace *
            (problem I).toSourceScope.oracleMultiplier left.val right.val)) := by
  rw [operator, UnitaryOperator.ofPerm_apply_ket]
  simpa [sourceLabel, targetLabel] using congrArg
    (fun index : OracleBasis I =>
      NormalizedVector.ket (R := Qubits (Layout.totalQubits I)) index)
    (oraclePermutation_sourceLabel I ((left, right), workspace))

/-- Canonical ideal access built only from the certified ECDLP instance. -/
def access (I : ECDLPInstance E) : Access I where
  operator := operator I
  basisAction := operator_basisAction I

end

end IdealAccess
end Canonical
end ECDLP
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
