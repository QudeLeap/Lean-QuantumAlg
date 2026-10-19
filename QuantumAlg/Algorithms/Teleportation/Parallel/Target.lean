/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates
public import QuantumAlg.Core.Execution.State.Requirement

import all QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates
import all QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
import all QuantumAlg.Core.Execution.Reference.Preparation
import all QuantumAlg.Core.Execution.SelectionAll.Reference
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.Input

namespace QuantumAlg.QuantumTeleportation.Parallel

noncomputable section

namespace Target

open Execution

/-- The supplied unknown input and the entire reference precede only the traced Bell resource. -/
def inputReferenceBasis (count : Nat) (Reference : Register) :
    ((context count).register.prod Reference).Index ≃
      (((inputRegister count).prod Reference).prod (bellRegister count)).Index where
  toFun entry := (((inputBellBasis count entry.1).1, entry.2),
    (inputBellBasis count entry.1).2)
  invFun entry := ((inputBellBasis count).symm (entry.1.1, entry.2), entry.1.2)
  left_inv entry := by
    obtain ⟨basis, reference⟩ := entry
    exact congrArg (fun actual => (actual, reference))
      ((inputBellBasis count).symm_apply_apply basis)
  right_inv entry := by
    obtain ⟨⟨basis, reference⟩, resource⟩ := entry
    change (((inputBellBasis count ((inputBellBasis count).symm
      (basis, resource))).1, reference),
        (inputBellBasis count ((inputBellBasis count).symm (basis, resource))).2) = _
    rw [Equiv.apply_symm_apply]

/-- The original full n-input/reference density, independent of every candidate execution. -/
def originalInput (count : Nat) {Reference : Register}
    (input : Input (context count) Reference) :
    DensityOperator ((inputRegister count).prod Reference) :=
  (input.state.quantumMarginal.reindex
    (S := ((inputRegister count).prod Reference).prod (bellRegister count))
    (inputReferenceBasis count Reference)).marginalLeft

lemma originalInput_normalized (count : Nat) {Reference : Register}
    (input : Input (context count) Reference) : (originalInput count input).IsNormalized := by
  change (originalInput count input).mass = 1
  rw [originalInput, DensityOperator.marginalLeft_mass, DensityOperator.reindex_mass,
    ExecutionState.quantumMarginal_mass]
  exact input.normalized

/-- Alice's two original positions remain first; Bob's original position remains last. -/
def outputTriple : (Fin 3 → Fin 2) ≃ Fin 4 × Fin 2 where
  toFun basis := ((finProdFinEquiv (m := 2) (n := 2)) (basis 0, basis 1), basis 2)
  invFun basis := ![((finProdFinEquiv (m := 2) (n := 2)).symm basis.1).1,
    ((finProdFinEquiv (m := 2) (n := 2)).symm basis.1).2, basis.2]
  left_inv basis := by
    funext index
    fin_cases index
    · exact congrArg Prod.fst
        ((finProdFinEquiv (m := 2) (n := 2)).symm_apply_apply (basis 0, basis 1))
    · exact congrArg Prod.snd
        ((finProdFinEquiv (m := 2) (n := 2)).symm_apply_apply (basis 0, basis 1))
    · rfl
  right_inv basis := by
    obtain ⟨alice, bob⟩ := basis
    apply Prod.ext
    · exact (finProdFinEquiv (m := 2) (n := 2)).apply_symm_apply alice
    · rfl

def outputBank (count : Nat) : (Fin count → Fin 3 → Fin 2) ≃
    (bellRegister count).Index × (inputRegister count).Index where
  toFun basis := (fun block => (outputTriple (basis block)).1,
    fun block => (outputTriple (basis block)).2)
  invFun basis block := outputTriple.symm (basis.1 block, basis.2 block)
  left_inv basis := by
    funext block
    exact outputTriple.symm_apply_apply (basis block)
  right_inv basis := by
    apply Prod.ext
    · funext block
      exact congrArg Prod.fst (outputTriple.apply_symm_apply (basis.1 block, basis.2 block))
    · funext block
      exact congrArg Prod.snd (outputTriple.apply_symm_apply (basis.1 block, basis.2 block))

def outputBasis (count : Nat) : (context count).register.Index ≃
    ((bellRegister count).prod (inputRegister count)).Index :=
  ((basisOfEqualWires (layout count) (context count).quantumLayout
    (context_wires count)).symm.trans (tripleBasis count)).trans (outputBank count)

def outputReferenceBasis (count : Nat) (Reference : Register) :
    ((context count).register.prod Reference).Index ≃
      ((bellRegister count).prod ((inputRegister count).prod Reference)).Index :=
  ((outputBasis count).prodCongr (Equiv.refl Reference.Index)).trans
    (Equiv.prodAssoc _ _ _)

/-- This label is read from the actual result value, rather than supplied as a hidden outcome. -/
def aliceLabel {count : Nat} (value : CShape.Value (resultShape count)) :
    (bellRegister count).Index := fun block =>
  (finProdFinEquiv (m := 2) (n := 2))
    ((value.get block).first.toFin, (value.get block).second.toFin)

/-- The complete promised density keeps Alice's measured systems and Bob/reference coherences. -/
def target (count : Nat) {Reference : Register} (input : Input (context count) Reference)
    (value : CShape.Value (resultShape count)) :
    DensityOperator ((context count).register.prod Reference) :=
  (prependPrepared (originalInput count input)
    (NormalizedVector.ket (R := bellRegister count) (aliceLabel value))).reindex
      (S := (context count).register.prod Reference)
      (outputReferenceBasis count Reference).symm

lemma target_normalized (count : Nat) {Reference : Register}
    (input : Input (context count) Reference) (value : CShape.Value (resultShape count)) :
    (target count input value).IsNormalized := by
  change (target count input value).mass = 1
  rw [target, DensityOperator.reindex_mass, prependPrepared_mass]
  exact originalInput_normalized count input

/-- One independent full quantum/reference promise, grouped by the real written result cells. -/
public def requirement (count : Nat) : StateRequirement (context count) (context count) :=
  .jointReference Finset.univ (.read (resultInput count)) (fun Reference input value =>
    .mixed (DensityOperator.observeSelectionWithReference
      (context count).quantumLayout Finset.univ Reference (target count input value))
      ((DensityOperator.observeSelectionWithReference_mass
        (context count).quantumLayout Finset.univ Reference (target count input value)).trans
        (target_normalized count input value)))

end Target

end

end QuantumAlg.QuantumTeleportation.Parallel
