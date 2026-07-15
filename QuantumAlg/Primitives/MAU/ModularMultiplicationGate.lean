/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Circuit
public import QuantumAlg.Util.ModularMultiplicationDomain

/-!
# Modular multiplication gates

This module lifts the modular multiplication permutation on `(ZMod N)^x` into a
register-polymorphic `Gate.ofPerm`. The wrapper uses the inverse permutation
when calling `Gate.ofPerm`, because the matrix convention sends `|x>` to
`|sigma^-1 x>` for `Gate.ofPerm sigma`. The exported basis-action lemma is
therefore stated in the source-facing direction `|x> -> |a*x>`.

The source-facing action is the modular multiplication unitary used as the
order-finding oracle in Shor's period-finding route [Sho95,
source.tex:1124-1134] [dW19, qcnotes.tex:2469-2475].
-/

@[expose] public section

namespace QuantumAlg

namespace ModularMultiplicationDomain

/-- Register whose basis labels are the selected unit-group carrier. -/
def unitRegister {N n : ℕ} (D : ModularMultiplicationDomain N n) : Register := by
  haveI : NeZero N := ⟨ne_of_gt D.modulus_pos⟩
  exact
    { Index := UnitCarrier D
      fintype := inferInstance
      decEq := inferInstance }

/-- The modular multiplication gate `U_a` on the selected unit carrier. -/
def multiplicationGate {N n : ℕ} (D : ModularMultiplicationDomain N n)
    (a : UnitCarrier D) : Gate D.unitRegister :=
  Gate.ofPerm (D.multiplicationPerm a).symm

/-- The modular multiplication gate is unitary by construction as a
permutation gate. -/
private theorem multiplicationGate_mem_unitaryGroup {N n : ℕ}
    (D : ModularMultiplicationDomain N n) (a : UnitCarrier D) :
    ((D.multiplicationGate a : Gate D.unitRegister) : HilbertOperator D.unitRegister)
      ∈ Matrix.unitaryGroup D.unitRegister.Index ℂ :=
  Gate.ofPerm_mem_unitaryGroup _

/-- Basis action of the modular multiplication gate:
`U_a |x> = |a*x>`. -/
theorem multiplicationGate_apply_ket {N n : ℕ}
    (D : ModularMultiplicationDomain N n) (a x : UnitCarrier D) :
    (D.multiplicationGate a).apply
        (PureState.ket (R := D.unitRegister) x) =
      PureState.ket (R := D.unitRegister) (D.multiplyUnit a x) := by
  rw [multiplicationGate, Gate.ofPerm_apply_ket]
  change PureState.ket (R := D.unitRegister) (D.multiplicationPerm a x) =
    PureState.ket (R := D.unitRegister) (D.multiplyUnit a x)
  simp [multiplyUnit]

theorem multiplicationGate_applyVec {N n : ℕ}
    (D : ModularMultiplicationDomain N n) (a : UnitCarrier D)
    (psi : StateVector D.unitRegister) (x : UnitCarrier D) :
    (D.multiplicationGate a).applyVec psi x =
      psi (D.multiplyUnit a⁻¹ x) := by
  rw [multiplicationGate, Gate.ofPerm_applyVec]
  rfl

/-! ### Circuit wrapper -/

/-- Typed circuit wrapper for the domain-specific modular multiplication gate
`U_a`. The caller supplies the resource counters for the selected implementation
or oracle model. -/
noncomputable def multiplicationCircuit {N n : ℕ}
    (D : ModularMultiplicationDomain N n) (a : UnitCarrier D)
    (resources : ResourceProfile) (depth queryDepth : ℕ) : Circuit D.unitRegister :=
  Circuit.ofGate "modular-multiplication-domain" (D.multiplicationGate a)
    resources depth queryDepth

@[simp] theorem multiplicationCircuit_resources {N n : ℕ}
    (D : ModularMultiplicationDomain N n) (a : UnitCarrier D)
    (resources : ResourceProfile) (depth queryDepth : ℕ) :
    (D.multiplicationCircuit a resources depth queryDepth).resources = resources :=
  rfl

@[simp] theorem multiplicationCircuit_depth {N n : ℕ}
    (D : ModularMultiplicationDomain N n) (a : UnitCarrier D)
    (resources : ResourceProfile) (depth queryDepth : ℕ) :
    (D.multiplicationCircuit a resources depth queryDepth).depth = depth :=
  rfl

@[simp] theorem multiplicationCircuit_queryDepth {N n : ℕ}
    (D : ModularMultiplicationDomain N n) (a : UnitCarrier D)
    (resources : ResourceProfile) (depth queryDepth : ℕ) :
    (D.multiplicationCircuit a resources depth queryDepth).queryDepth = queryDepth :=
  rfl

/-- Basis action of the typed modular-multiplication circuit wrapper. -/
theorem multiplicationCircuit_apply_ket {N n : ℕ}
    (D : ModularMultiplicationDomain N n) (a x : UnitCarrier D)
    (resources : ResourceProfile) (depth queryDepth : ℕ) :
    Circuit.apply (D.multiplicationCircuit a resources depth queryDepth)
      (PureState.ket (R := D.unitRegister) x : StateVector D.unitRegister) =
      (PureState.ket (R := D.unitRegister) (D.multiplyUnit a x) :
        StateVector D.unitRegister) := by
  simpa [multiplicationCircuit, Circuit.apply_ofGate, Gate.apply_coe] using
    congrArg (fun psi : PureState D.unitRegister => (psi : StateVector D.unitRegister))
      (D.multiplicationGate_apply_ket a x)

@[simp] theorem multiplicationCircuit_applyVec {N n : ℕ}
    (D : ModularMultiplicationDomain N n) (a : UnitCarrier D)
    (resources : ResourceProfile) (depth queryDepth : ℕ)
    (psi : StateVector D.unitRegister) (x : UnitCarrier D) :
    Circuit.apply (D.multiplicationCircuit a resources depth queryDepth) psi x =
      psi (D.multiplyUnit a⁻¹ x) := by
  change (D.multiplicationGate a).applyVec psi x = psi (D.multiplyUnit a⁻¹ x)
  exact D.multiplicationGate_applyVec a psi x

/-- Correctness/resource proof package for a domain-specific modular
multiplication circuit wrapper. -/
noncomputable def multiplicationCircuitResourceCorrectWitness {N n : ℕ}
    (D : ModularMultiplicationDomain N n) (a : UnitCarrier D)
    (resources : ResourceProfile) (depth queryDepth : ℕ) :
    ResourceCorrectWitness (R := D.unitRegister)
      (∀ x : UnitCarrier D,
        Circuit.apply (D.multiplicationCircuit a resources depth queryDepth)
          (PureState.ket (R := D.unitRegister) x : StateVector D.unitRegister) =
          (PureState.ket (R := D.unitRegister) (D.multiplyUnit a x) :
            StateVector D.unitRegister))
      ((D.multiplicationCircuit a resources depth queryDepth).resources = resources ∧
        (D.multiplicationCircuit a resources depth queryDepth).depth = depth ∧
        (D.multiplicationCircuit a resources depth queryDepth).queryDepth = queryDepth) := by
  exact
    { circuit := D.multiplicationCircuit a resources depth queryDepth
      correctness := fun x => D.multiplicationCircuit_apply_ket a x resources depth queryDepth
      resources := ⟨rfl, rfl, rfl⟩ }

end ModularMultiplicationDomain

end QuantumAlg
