/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
public import QuantumAlg.Algorithms.Teleportation.Parallel.Channel
import all QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Base.Layout.Signature
import Mathlib.Data.Fin.VecNotation

/-!
# Original input and shared-resource coordinates of the live register

The explicit regrouping reads each source triple in the physical order
input, Alice's Bell half, Bob's Bell half [dW19, qcnotes.tex:785,789]. It
retains every wire and every basis value. These independent coordinates
specify the supplied Bell resource without mentioning an external reference
or inspecting a candidate execution.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel

noncomputable section

open Execution

/-- The joint basis of all shared Bell pairs, keeping both halves of every pair. -/
public abbrev bellRegister (count : Nat) : Register where
  Index := Fin count → Fin 4
  fintype := inferInstance
  decEq := inferInstance

/-- Group only consecutive physical positions; no basis cardinality choice is used. -/
def tripleBasis (count : Nat) :
    (layout count).register.Index ≃ (Fin count → Fin 3 → Fin 2) where
  toFun basis block side := basis (wireIndex block side)
  invFun basis index :=
    let coordinates := finProdFinEquiv.symm (Fin.cast (width_eq count) index)
    basis coordinates.1 coordinates.2
  left_inv basis := by
    funext index
    let coordinates :=
      (finProdFinEquiv (m := count) (n := 3)).symm (Fin.cast (width_eq count) index)
    have same : wireIndex coordinates.1 coordinates.2 = index := by
      apply Fin.ext
      change ((finProdFinEquiv (m := count) (n := 3)) coordinates).val = index.val
      exact congrArg Fin.val
        ((finProdFinEquiv (m := count) (n := 3)).apply_symm_apply
          (Fin.cast (width_eq count) index))
    apply Fin.ext
    exact congrArg (fun position : Fin (width count) => (basis position).val) same
  right_inv basis := by
    funext block side
    change basis (finProdFinEquiv.symm (finProdFinEquiv (block, side))).1
      (finProdFinEquiv.symm (finProdFinEquiv (block, side))).2 = basis block side
    rw [Equiv.symm_apply_apply]

/-- Separate one actual input label from its two actual Bell-resource labels. -/
def splitTriple : (Fin 3 → Fin 2) ≃ Fin 2 × Fin 4 where
  toFun basis := (basis 0, (finProdFinEquiv (m := 2) (n := 2)) (basis 1, basis 2))
  invFun basis := ![basis.1, ((finProdFinEquiv (m := 2) (n := 2)).symm basis.2).1,
    ((finProdFinEquiv (m := 2) (n := 2)).symm basis.2).2]
  left_inv basis := by
    funext index
    fin_cases index
    · rfl
    · exact congrArg Prod.fst
        ((finProdFinEquiv (m := 2) (n := 2)).symm_apply_apply (basis 1, basis 2))
    · exact congrArg Prod.snd
        ((finProdFinEquiv (m := 2) (n := 2)).symm_apply_apply (basis 1, basis 2))
  right_inv basis := by
    obtain ⟨input, bellLabel⟩ := basis
    apply Prod.ext
    · rfl
    · exact (finProdFinEquiv (m := 2) (n := 2)).apply_symm_apply bellLabel

/-- The whole bank is regrouped into arbitrary joint input labels and Bell-resource labels. -/
def splitBank (count : Nat) : (Fin count → Fin 3 → Fin 2) ≃
    (inputRegister count).Index × (bellRegister count).Index where
  toFun basis := (fun block => (splitTriple (basis block)).1,
    fun block => (splitTriple (basis block)).2)
  invFun basis block := splitTriple.symm (basis.1 block, basis.2 block)
  left_inv basis := by
    funext block
    exact splitTriple.symm_apply_apply (basis block)
  right_inv basis := by
    apply Prod.ext
    · funext block
      exact congrArg Prod.fst (splitTriple.apply_symm_apply (basis.1 block, basis.2 block))
    · funext block
      exact congrArg Prod.snd (splitTriple.apply_symm_apply (basis.1 block, basis.2 block))

/-- Full context coordinates identify exactly the original input and supplied shared resource. -/
def inputBellBasis (count : Nat) : (context count).register.Index ≃
    ((inputRegister count).prod (bellRegister count)).Index :=
  ((basisOfEqualWires (layout count) (context count).quantumLayout
    (context_wires count)).symm.trans (tripleBasis count)).trans (splitBank count)

end

end QuantumAlg.QuantumTeleportation.Parallel
