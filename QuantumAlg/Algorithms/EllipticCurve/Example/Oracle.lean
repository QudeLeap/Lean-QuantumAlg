/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Access.Specification
import all QuantumAlg.Algorithms.EllipticCurve.Example.Curve
import Mathlib.Logic.Equiv.Fintype

/-!
# Intrinsic small-curve ECDLP oracle

The fixed example supplies only the sealed U_{P,Q} permutation. Register
width and point encoding come from the canonical identity-inclusive ECDLP
layout rather than caller-selected workspace data.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace Example

open PrimeFieldShortWeierstrass

noncomputable section

/-! ## Intrinsic fixed-width encoding and compiled access -/

/- The point representation and its injectivity are owned by
`ECDLP.Canonical.Layout`; this example supplies only the `U_{P,Q}` operator. -/

/-- Basis labels for each oversampled exponent register. -/
abbrev WorkspaceLabel :=
  Fin (2 ^ orderWidth)

/-- Semantic oracle inputs before extending their action to the full basis. -/
abbrev OracleDomain :=
  (WorkspaceLabel × WorkspaceLabel) × GroupPoint curve

/-- Computational basis of the complete fixed ECDLP circuit register. -/
abbrev OracleBasis :=
  Fin (2 ^ totalQubits)

/-- Encoded source basis label of one semantic oracle input. -/
def sourceLabel (x : OracleDomain) : OracleBasis :=
  ECDLP.Canonical.basisIndex ecdLPInstance x.1.1 x.1.2 x.2

/-- Encoded target basis label after the actual elliptic-curve group action. -/
def targetLabel (x : OracleDomain) : OracleBasis :=
  ECDLP.Canonical.basisIndex ecdLPInstance x.1.1 x.1.2
    (x.2 * canonicalProblem.toSourceScope.oracleMultiplier
      x.1.1.val x.1.2.val)

theorem sourceLabel_injective : Function.Injective sourceLabel := by
  intro left right equality
  apply (ECDLP.Canonical.Layout.fullEncoding ecdLPInstance).encode_injective
  apply Fin.ext
  exact Fin.ext_iff.mp equality

theorem targetLabel_injective : Function.Injective targetLabel := by
  rintro ⟨⟨a, b⟩, y⟩ ⟨⟨a', b'⟩, y'⟩ h
  have houter :
      ((a, b), y * canonicalProblem.toSourceScope.oracleMultiplier a.val b.val) =
        ((a', b'),
          y' * canonicalProblem.toSourceScope.oracleMultiplier a'.val b'.val) :=
    (ECDLP.Canonical.Layout.fullEncoding ecdLPInstance).encode_injective (by
      apply Fin.ext
      exact Fin.ext_iff.mp h)
  have hab : (a, b) = (a', b') :=
    congrArg Prod.fst houter
  cases hab
  have hmul :
      y * canonicalProblem.toSourceScope.oracleMultiplier a.val b.val =
        y' * canonicalProblem.toSourceScope.oracleMultiplier a.val b.val :=
    congrArg Prod.snd houter
  have hy : y = y' := mul_right_cancel hmul
  cases hy
  rfl

noncomputable instance instFiniteOracleDomain : Finite OracleDomain :=
  Finite.of_injective sourceLabel sourceLabel_injective

/-- Full-basis permutation extending the injective semantic oracle action. -/
def oraclePermutation : Equiv.Perm OracleBasis :=
  Classical.choose
    (Equiv.Perm.exists_extending_pair sourceLabel targetLabel
      sourceLabel_injective targetLabel_injective)

theorem oraclePermutation_sourceLabel (x : OracleDomain) :
    oraclePermutation (sourceLabel x) = targetLabel x :=
  (Classical.choose_spec
    (Equiv.Perm.exists_extending_pair sourceLabel targetLabel
      sourceLabel_injective targetLabel_injective)) x

theorem oracleOperator_basisAction (x : OracleDomain) :
    (UnitaryOperator.ofPerm (R := Qubits totalQubits)
        oraclePermutation.symm).apply
        (NormalizedVector.ket (sourceLabel x)) =
      NormalizedVector.ket (targetLabel x) := by
  rw [UnitaryOperator.ofPerm_apply_ket]
  simpa using congrArg
    (fun z : OracleBasis =>
      NormalizedVector.ket
        (R := Qubits totalQubits) z)
    (oraclePermutation_sourceLabel x)

/-- Fixed full-basis access supplies the operator and its original action law;
the generic declared model owns its sole query coordinate and placement. -/
def access : ECDLP.Canonical.Access ecdLPInstance where
  operator := UnitaryOperator.ofPerm oraclePermutation.symm
  basisAction := fun left right workspace =>
    oracleOperator_basisAction ((left, right), workspace)

end

end Example
end EllipticCurve
end QuantumAlg

end
