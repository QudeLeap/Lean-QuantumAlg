/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Addition.VBE.Circuit
import Mathlib.Tactic
import all QuantumAlg.Components.Encoded.BasisMap
import all QuantumAlg.Util.ModularMultiplicationDomain
import all QuantumAlg.Util.ZModUnits
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate
import all QuantumAlg.Primitives.MAU.Multiplication
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Accumulate
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.VBECircuit

/-!
# Modular multiplication operators

This module lifts the modular multiplication permutation on `(ZMod N)^x` into a
register-polymorphic `UnitaryOperator.ofPerm`. The carrier uses the inverse permutation
because the matrix convention sends `|x>` to `|sigma^-1 x>` for
`UnitaryOperator.ofPerm sigma`. The exported basis-action lemma is
therefore stated in the source-facing direction `|x> -> |a*x>`.

The source-facing action is the modular multiplication unitary used as the
order-finding oracle in Shor's period-finding route [Sho95,
source.tex:1124-1134] [dW19, qcnotes.tex:2469-2475].
-/

section

namespace QuantumAlg

namespace MAU.MultiplicationGate

open ModularMultiplicationDomain

/-- Register whose basis labels are the selected unit-group carrier. -/
@[implicit_reducible]
def unitRegister {N n : ℕ} (D : ModularMultiplicationDomain N n) : Register := by
  haveI : NeZero N := ⟨ne_of_gt D.modulus_pos⟩
  exact
    { Index := UnitCarrier D
      fintype := inferInstance
      decEq := inferInstance }

/-- The modular multiplication operator `U_a` on the selected unit carrier. -/
def multiplicationOp {N n : ℕ} (D : ModularMultiplicationDomain N n)
    (a : UnitCarrier D) : UnitaryOperator (unitRegister D) :=
  UnitaryOperator.ofPerm (D.multiplicationPerm a).symm

/-- Basis action of the modular multiplication gate:
`U_a |x> = |a*x>`. -/
theorem multiplicationOp_apply_ket {N n : ℕ}
    (D : ModularMultiplicationDomain N n) (a x : UnitCarrier D) :
    (multiplicationOp D a).apply
        (NormalizedVector.ket (R := unitRegister D) x) =
      NormalizedVector.ket (R := unitRegister D) (D.multiplyUnit a x) := by
  rw [multiplicationOp, UnitaryOperator.ofPerm_apply_ket]
  change NormalizedVector.ket (R := unitRegister D) (D.multiplicationPerm a x) =
    NormalizedVector.ket (R := unitRegister D) (D.multiplyUnit a x)
  simp [multiplyUnit]

theorem multiplicationOp_applyVec {N n : ℕ}
    (D : ModularMultiplicationDomain N n) (a : UnitCarrier D)
    (ψ : HilbertVector (unitRegister D)) (x : UnitCarrier D) :
    (multiplicationOp D a).applyVec ψ x =
      ψ (D.multiplyUnit a⁻¹ x) := by
  rw [multiplicationOp, UnitaryOperator.ofPerm_applyVec]
  rfl

/-! ### Same-circuit realization -/

/-- An ideal-carrier circuit contract for domain-specific modular
multiplication. Ancilla-extended physical implementations use
`EncodedCircuitRealization` below and do not identify their register carrier
with `unitRegister D`. -/
structure CircuitRealization {N n : ℕ}
    (D : ModularMultiplicationDomain N n) (a : UnitCarrier D) where
  /-- The executable typed circuit. -/
  circuit : UnitaryCircuit (unitRegister D)
  /-- The circuit implements the source-facing multiplication operator. -/
  matrix_eq : circuit.matrix = multiplicationOp D a

namespace CircuitRealization

variable {N n : ℕ} {D : ModularMultiplicationDomain N n} {a : UnitCarrier D}

/-- Ordered strict events derived from the ideal-carrier realization. -/
def eventTrace (realization : CircuitRealization D a) :
    List (Resource.Event .quantum) :=
  realization.circuit.eventTrace

/-- Strict event pool derived from the ideal-carrier realization. -/
def eventCost (realization : CircuitRealization D a) : ResourcePool .quantum :=
  realization.circuit.eventCost

/-- Strict symbolic event critical path of the ideal-carrier realization. -/
def eventDepth (realization : CircuitRealization D a) :
    DepthExpr (Resource.Event .quantum) :=
  realization.circuit.eventDepth

/-- Literal depth of one strict event coordinate in the ideal-carrier circuit. -/
def eventQueryDepth (realization : CircuitRealization D a)
    (focus : Resource.Event .quantum) : Nat :=
  realization.circuit.eventQueryDepth focus

/-- Exact multiplicity of one gate coordinate in the ideal-carrier circuit. -/
def eventGateCount (realization : CircuitRealization D a)
    (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) realization.circuit.eventCost

/-- Linearizing ideal-carrier event depth recovers the exact event pool. -/
theorem resourcesFromEventDepth_eq_eventCost
    (realization : CircuitRealization D a) :
    realization.circuit.resourcesFromEventDepth = realization.circuit.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost realization.circuit





/-- Intrinsically normalized basis action of the realized multiplication
circuit. -/
theorem applyNormalized_ket (realization : CircuitRealization D a)
    (x : UnitCarrier D) :
    realization.circuit.applyNormalized
        (NormalizedVector.ket (R := unitRegister D) x) =
      NormalizedVector.ket (R := unitRegister D) (D.multiplyUnit a x) := by
  change realization.circuit.matrix.apply
      (NormalizedVector.ket (R := unitRegister D) x) = _
  rw [realization.matrix_eq]
  exact multiplicationOp_apply_ket D a x

/-- Raw linear action of the same circuit, retained for arbitrary
superpositions and eigenvector calculations. -/
theorem applyVec (realization : CircuitRealization D a)
    (ψ : HilbertVector (unitRegister D)) (x : UnitCarrier D) :
    realization.circuit.applyVec ψ x = ψ (D.multiplyUnit a⁻¹ x) := by
  change realization.circuit.matrix.applyVec ψ x = _
  rw [realization.matrix_eq]
  exact multiplicationOp_applyVec D a ψ x

end CircuitRealization

/-! ### Ancilla-extended encoded realization -/

/-- A concrete base-gate realization on a larger physical register, restricted
to the clean encoding of the selected unit carrier. The object owns the exact
program and its clean endpoint; circuit and resource projections are derived
from that program rather than supplied by the caller. -/
structure EncodedCircuitRealization {N n : ℕ}
    (D : ModularMultiplicationDomain N n) (a : UnitCarrier D) where
  /-- Supplied physical semantic carrier, including explicit work registers. -/
  Physical : Type
  /-- Faithful binary encoding of the supplied physical carrier. -/
  encoding : BinaryLabelEncoding Physical
  /-- Clean embedding of one ideal unit-carrier label into the physical layout. -/
  cleanEmbedding : UnitCarrier D → Physical
  /-- The clean embedding does not identify distinct ideal inputs. -/
  cleanEmbedding_injective : Function.Injective cleanEmbedding
  /-- Exact circuit on the physical layout. -/
  program : UnitaryCircuit (Qubits encoding.width)
  /-- The exact program maps every clean input to the clean encoding of
  multiplication by `a`. -/
  applyNormalized_clean : ∀ x,
    program.applyNormalized
        (NormalizedVector.ket (encoding.encode (cleanEmbedding x))) =
      NormalizedVector.ket
        (encoding.encode (cleanEmbedding (D.multiplyUnit a x)))

namespace EncodedCircuitRealization

variable {N n : ℕ} {D : ModularMultiplicationDomain N n}
  {a : UnitCarrier D}

/-- Clean-subspace binary encoding induced by the supplied physical layout. -/
def cleanEncoding (realization : EncodedCircuitRealization D a) :
    BinaryLabelEncoding (UnitCarrier D) where
  width := realization.encoding.width
  encode := fun x => realization.encoding.encode (realization.cleanEmbedding x)
  encode_injective := by
    intro x y hxy
    apply realization.cleanEmbedding_injective
    exact realization.encoding.encode_injective hxy

/-- Direct semantic realization on the clean unit-carrier encoding. -/
theorem cleanRealizes (realization : EncodedCircuitRealization D a) :
    UnitaryCircuit.Realizes realization.cleanEncoding realization.program
      (D.multiplyUnit a) where
  apply_encoded_ket := realization.applyNormalized_clean

/-- Typed circuit folded from the exact physical base-gate program. -/
def circuit (realization : EncodedCircuitRealization D a) :
    UnitaryCircuit (Qubits realization.encoding.width) :=
  realization.program

/-- Ordered strict events derived from the exact physical circuit. -/
def eventTrace (realization : EncodedCircuitRealization D a) :
    List (Resource.Event .quantum) :=
  realization.circuit.eventTrace

/-- Strict event pool derived from the exact physical circuit. -/
def eventCost (realization : EncodedCircuitRealization D a) :
    ResourcePool .quantum :=
  realization.circuit.eventCost

/-- Strict symbolic event critical path of the exact physical circuit. -/
def eventDepth (realization : EncodedCircuitRealization D a) :
    DepthExpr (Resource.Event .quantum) :=
  realization.circuit.eventDepth

/-- Evaluated strict event depth under literal event durations. -/
def evaluatedEventDepth (realization : EncodedCircuitRealization D a)
    (assign : Resource.Event .quantum → Nat) : Nat :=
  realization.circuit.evaluatedEventDepth assign

/-- Literal depth of one strict event coordinate in the physical circuit. -/
def eventQueryDepth (realization : EncodedCircuitRealization D a)
    (focus : Resource.Event .quantum) : Nat :=
  realization.circuit.eventQueryDepth focus

/-- Exact multiplicity of one gate coordinate in the physical event pool. -/
def eventGateCount (realization : EncodedCircuitRealization D a)
    (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) realization.circuit.eventCost











/-- Width of the supplied physical encoding. -/
def qubitCount (realization : EncodedCircuitRealization D a) : Nat :=
  realization.encoding.width

/-- Normalized clean-subspace endpoint of the exact physical circuit. -/
theorem applyNormalized_clean_ket
    (realization : EncodedCircuitRealization D a) (x : UnitCarrier D) :
    realization.circuit.applyNormalized
        (NormalizedVector.ket (realization.cleanEncoding.encode x)) =
      NormalizedVector.ket
        (realization.cleanEncoding.encode (D.multiplyUnit a x)) :=
  realization.cleanRealizes.apply_encoded_ket x



/-- Linearizing physical event depth recovers the exact strict event pool. -/
theorem resourcesFromEventDepth_eq_eventCost
    (realization : EncodedCircuitRealization D a) :
    realization.circuit.resourcesFromEventDepth = realization.circuit.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost realization.circuit

end EncodedCircuitRealization

end MAU.MultiplicationGate

end QuantumAlg

end
