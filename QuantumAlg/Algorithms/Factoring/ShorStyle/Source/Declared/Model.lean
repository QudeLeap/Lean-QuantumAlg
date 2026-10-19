/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Oracle
import all QuantumAlg.Core.Base.Oracle.Model

/-!
# A fixed modular-exponentiation query family for Shor sampling

The declaration fixes the register sizes. Its interpreter supplies the public
modulus, and a runtime base word selects the ordinary XOR-exponentiation query.
The base need not be a unit, and the modulus need not be odd. No controlled
or inverse access form is granted [dW19, qcnotes.tex:2203-2225].
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource

noncomputable section

/-- Exactly the arithmetic conditions needed to store every modular power. -/
structure RegisterBounds (N width : Nat) : Prop where
  /-- Modular exponentiation has a positive modulus. -/
  modulus_pos : 0 < N
  /-- Every residue fits the declared target word. -/
  register_fits : N ≤ 2 ^ width

/-- A stored base selects the existing mathematical XOR permutation. -/
lemma RegisterBounds.access {N width : Nat} (bounds : RegisterBounds N width)
    (phaseBits : Nat) (base : Fin (2 ^ width)) :
    OrderFinding.ModExpOracleAccess N base.val phaseBits width where
  modulus_pos := bounds.modulus_pos
  register_fits := bounds.register_fits

/-- Ordinary modular exponentiation is the only granted query coordinate. -/
inductive Coordinate where
  | modularExponentiation
  deriving DecidableEq

/-- Fixed register sizes declare the same query interface for every stored base word. -/
@[implicit_reducible]
def model (width phaseBits : Nat) : OracleModel where
  Query := Fin (2 ^ width)
  Coordinate := Coordinate
  coordinateDecidableEq := inferInstance
  signature _ := QuantumSignature.qubits (phaseBits + width)
  coordinate _ := .modularExponentiation

/-- The interpreter supplies the modular XOR action for each available stored base. -/
def interpretation {N width : Nat} (bounds : RegisterBounds N width)
    (phaseBits : Nat) : (model width phaseBits).Interpretation where
  operator base :=
    UnitaryOperator.reindex
      (QuantumSignature.qubitsIndexEquiv (phaseBits + width)).symm
      (OrderFinding.modExpOracle (bounds.access phaseBits base))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource
