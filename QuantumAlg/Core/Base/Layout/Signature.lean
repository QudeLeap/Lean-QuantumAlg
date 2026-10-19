/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum
import all QuantumAlg.Core.Base.Layout.Quantum
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Physical system signatures

A signature fixes the number and ordered dimensions of the systems on which
an operation acts. Physical identities are supplied separately by a layout.
The signature's register is the product of its individual computational bases;
equal total Hilbert dimension alone does not identify two signatures.
-/

namespace QuantumAlg

/-- Ordered positive dimensions, independent of physical wire identities. -/
public structure QuantumSignature where
  /-- Number of systems touched by the operation. -/
  systemCount : Nat
  /-- Computational-basis dimension of each system. -/
  dimension : Fin systemCount → ℕ+

namespace QuantumSignature

/-- Computational-basis labels retain one value for every system. -/
public abbrev Basis (signature : QuantumSignature) :=
  (index : Fin signature.systemCount) → Fin (signature.dimension index)

/-- The register determined by the ordered physical dimensions. -/
@[expose, implicit_reducible]
public def register (signature : QuantumSignature) : Register where
  Index := signature.Basis
  fintype := inferInstance
  decEq := inferInstance

/-- A signature of exactly the stated number of dimension-two systems. -/
@[expose, implicit_reducible]
public def qubits (width : Nat) : QuantumSignature where
  systemCount := width
  dimension := fun _ => 2

/-- Fixed big-endian coordinates for a qubit signature. -/
public def qubitsIndexEquiv (width : Nat) :
    (qubits width).register.Index ≃ (Qubits width).Index :=
  BinaryBasis.bigEndianEquiv width

/-- A placement for exactly these dimensions; identity injectivity comes from
the layout itself. -/
public structure Placement (signature : QuantumSignature) where
  /-- The actual physical systems, in gate-argument order. -/
  layout : QuantumLayout signature.systemCount
  /-- Each argument is placed on a system of the declared dimension. -/
  dimension_eq : ∀ index, (layout.wire index).dimension = signature.dimension index

namespace Placement

/-- Transport each local value by its certified dimension equality. Physical
placement does not permit a caller-selected permutation of basis values. -/
@[expose]
public def indexEquiv {signature : QuantumSignature} (placement : Placement signature) :
    placement.layout.register.Index ≃ signature.register.Index where
  toFun basis index := Fin.cast (congrArg PNat.val (placement.dimension_eq index)) (basis index)
  invFun basis index :=
    Fin.cast (congrArg PNat.val (placement.dimension_eq index).symm) (basis index)
  left_inv basis := by
    funext index
    apply Fin.ext
    rfl
  right_inv basis := by
    funext index
    apply Fin.ext
    rfl

/-- Placement preserves the represented value of each gate argument. -/
@[simp] public lemma indexEquiv_apply_val {signature : QuantumSignature}
    (placement : Placement signature) (basis : placement.layout.register.Index)
    (index : Fin signature.systemCount) :
    (placement.indexEquiv basis index).val = (basis index).val := rfl

end Placement

/-- Place the signature on any injective assignment of physical identities. -/
@[expose, implicit_reducible]
public def place (signature : QuantumSignature) (identity : Fin signature.systemCount → Nat)
    (injective : Function.Injective identity) : Placement signature where
  layout :=
    { wire := fun index => ⟨identity index, signature.dimension index⟩
      identityInjective := injective }
  dimension_eq := fun _ => rfl

/-- Canonical local placement uses each argument's position as its identity. -/
@[expose, implicit_reducible]
public def canonicalPlacement (signature : QuantumSignature) : Placement signature :=
  signature.place Fin.val Fin.val_injective

end QuantumSignature

namespace QuantumLayout

/-- Forget only physical identities while retaining ordered system dimensions. -/
@[expose]
public def signature {systemCount : Nat} (layout : QuantumLayout systemCount) :
    QuantumSignature where
  systemCount := systemCount
  dimension := fun index => (layout.wire index).dimension

/-- Forgetting identities does not change computational-basis coordinates. -/
public lemma signature_register {systemCount : Nat} (layout : QuantumLayout systemCount) :
    layout.signature.register = layout.register := rfl

/-- Every layout is a legal placement of its own physical signature. -/
@[expose]
public def signaturePlacement {systemCount : Nat} (layout : QuantumLayout systemCount) :
    layout.signature.Placement where
  layout := layout
  dimension_eq := fun _ => rfl

end QuantumLayout

end QuantumAlg
