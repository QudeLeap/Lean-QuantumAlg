/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.PNat.Defs

/-!
# Finite quantum registers

`Register` is the finite-dimensional basis interface shared by states, gates,
operators, measurements, and circuits.  `Qubits n` is the specialization whose
basis labels are the current big-endian `Fin (2^n)` computational basis.
-/

section

namespace QuantumAlg

/-- A finite-dimensional quantum register. -/
public structure Register where
  /-- Basis labels for the register. -/
  Index : Type
  /-- The basis is finite. -/
  fintype : Fintype Index
  /-- Basis labels have decidable equality. -/
  decEq : DecidableEq Index

attribute [instance] Register.fintype Register.decEq

namespace Register

/-- Product/tensor register. -/
@[expose, implicit_reducible]
public def prod (left right : Register) : Register := by
  letI : Fintype left.Index := left.fintype
  letI : DecidableEq left.Index := left.decEq
  letI : Fintype right.Index := right.fintype
  letI : DecidableEq right.Index := right.decEq
  exact
    { Index := left.Index × right.Index
      fintype := inferInstance
      decEq := inferInstance }

/-- The explicit product type is canonically equivalent to the index type of
the product register. -/
@[expose]
public def prodIndexEquiv (left right : Register) :
    left.Index × right.Index ≃ (prod left right).Index := by
  unfold prod
  exact Equiv.refl _

end Register

/-- One positive-dimensional quantum system with its computational basis.
The dimension labels one physical system; it is not a number of qubits. -/
public abbrev Qudit (dimension : ℕ+) : Register where
  Index := Fin dimension
  fintype := inferInstance
  decEq := inferInstance

/-- The `n`-qubit register with big-endian computational basis labels. -/
public abbrev Qubits (n : Nat) : Register where
  Index := Fin (2 ^ n)
  fintype := inferInstance
  decEq := inferInstance

end QuantumAlg

end
