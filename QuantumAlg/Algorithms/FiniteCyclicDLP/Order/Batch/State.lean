/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.BornBridge.State
public import QuantumAlg.Core.Base.Tensor.Certified
public import QuantumAlg.Core.Base.Gate.Unitary.Reindex
public import Mathlib.Data.Fin.Tuple.Basic
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Product state of the fresh native-dimensional sample banks

The full family basis is equivalent to a vector of source-bank bases.  The
normalized family state is therefore the exact tensor product of the source
circuit state, with one factor for every physical bank.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderBatch

noncomputable section

open scoped BigOperators

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Abstract product register containing one source basis for every bank. -/
@[expose, implicit_reducible] public def familyRegister (P : KnownOrderProblem G)
    (count : Nat) : Register where
  Index := Fin count → (OrderOracle.layout P).Basis
  fintype := inferInstance
  decEq := inferInstance

/-- Flatten an ordered family of source-bank bases into the physical family layout. -/
@[expose] public def joinFamilyBasis (P : KnownOrderProblem G) (count : Nat)
    (family : (familyRegister P count).Index) : (layout P count).Basis :=
  fun flat => by
    let pair := finProdFinEquiv.symm flat
    simpa only [layout, pair, Equiv.apply_symm_apply] using family pair.1 pair.2

/-- Splitting a physical basis into its complete ordered bank family is an exact
finite-basis equivalence. -/
@[expose] public def familyBasisEquiv (P : KnownOrderProblem G) (count : Nat) :
    (layout P count).Basis ≃ (familyRegister P count).Index where
  toFun basis slot := bankBasis P slot basis
  invFun := joinFamilyBasis P count
  left_inv basis := by
    funext flat
    apply Fin.ext
    change (bankBasis P (finProdFinEquiv.symm flat).1 basis
      (finProdFinEquiv.symm flat).2).val = (basis flat).val
    rw [bankBasis_value]
    change (basis (finProdFinEquiv (finProdFinEquiv.symm flat))).val =
      (basis flat).val
    rw [Equiv.apply_symm_apply]
  right_inv family := by
    funext slot index
    apply Fin.ext
    change (bankBasis P slot (joinFamilyBasis P count family) index).val =
      (family slot index).val
    rw [bankBasis_value]
    change (family (finProdFinEquiv.symm (finProdFinEquiv (slot, index))).1
      (finProdFinEquiv.symm (finProdFinEquiv (slot, index))).2).val =
        (family slot index).val
    rw [Equiv.symm_apply_apply]

/-- Split the first factor from a nonempty homogeneous family register. -/
public def familyConsEquiv (P : KnownOrderProblem G) (count : Nat) :
    (Register.prod (OrderOracle.layout P).register (familyRegister P count)).Index ≃
      (familyRegister P (count + 1)).Index :=
  Fin.consEquiv (fun _ : Fin (count + 1) => (OrderOracle.layout P).Basis)

/-- Normalized tensor power of the one-cycle circuit state. -/
@[expose] public def independentState (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    (count : Nat) → NormalizedVector (familyRegister P count)
  | 0 => NormalizedVector.ket (fun index => Fin.elim0 index)
  | count + 1 =>
      NormalizedVector.reindex (familyConsEquiv P count)
        (NormalizedVector.prodTensor (OrderBornBridge.evolvedState P expansion)
          (independentState P expansion count))

/-- Every family amplitude is the product of its actual source-bank amplitudes. -/
public lemma independentState_apply (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) (count : Nat)
    (family : (familyRegister P count).Index) :
    independentState P expansion count family =
      ∏ slot : Fin count, OrderBornBridge.evolvedState P expansion (family slot) := by
  induction count with
  | zero =>
      let empty : (familyRegister P 0).Index := fun index => Fin.elim0 index
      have unique : family = empty := by
        funext index
        exact Fin.elim0 index
      subst family
      change (NormalizedVector.ket (R := familyRegister P 0) empty) empty = 1
      rw [NormalizedVector.ket_apply, if_pos rfl]
  | succ count induction =>
      rw [independentState, NormalizedVector.reindex_apply,
        NormalizedVector.prodTensor_apply]
      change OrderBornBridge.evolvedState P expansion (family 0) *
        independentState P expansion count (Fin.tail family) = _
      rw [induction (Fin.tail family), Fin.prod_univ_succ]
      rfl

/-- The same normalized tensor state in the actual physical family basis. -/
@[expose] public def physicalIndependentState (P : KnownOrderProblem G)
    (count : Nat) (expansion : OrderExpansion P.order) :
    NormalizedVector (layout P count).register :=
  NormalizedVector.reindex (familyBasisEquiv P count).symm
    (independentState P expansion count)

/-- Physical family amplitudes factor through the exact bank restrictions. -/
public lemma physicalIndependentState_apply (P : KnownOrderProblem G)
    (count : Nat) (expansion : OrderExpansion P.order)
    (basis : (layout P count).Basis) :
    physicalIndependentState P count expansion basis =
      ∏ slot : Fin count,
        OrderBornBridge.evolvedState P expansion (bankBasis P slot basis) := by
  rw [physicalIndependentState, NormalizedVector.reindex_apply,
    Equiv.symm_symm, independentState_apply]
  rfl

end

end QuantumAlg.FiniteCyclicDLP.OrderBatch
