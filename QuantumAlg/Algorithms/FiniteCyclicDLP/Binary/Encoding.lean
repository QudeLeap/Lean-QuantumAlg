/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Subgroup
public import QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Oracle
import all QuantumAlg.Components.BinaryLabelEncoding

/-!
# Identity-anchored minimal binary encoding of the finite cyclic workspace

The actual generated subgroup has `N` elements. Its existing identity-anchored
basis enumeration is injected into `ceil(log₂ N)` qubits. In particular, the
identity is physical zero and `N = 1` requires no group wire. This mathematical
encoding specifies the granted oracle representation; it is not a free
runtime conversion from a native-dimensional system [Sho95, source.tex:1704-1784].
-/

namespace QuantumAlg.FiniteCyclicDLP.Binary

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The minimal width of the actual cyclic-subgroup register. -/
@[expose] public def groupWidth (P : KnownOrderProblem G) : Nat := Nat.clog 2 P.order

/-- Every group label fits in that actual binary register. -/
public lemma order_le_groupCapacity (P : KnownOrderProblem G) :
    P.order ≤ 2 ^ groupWidth P :=
  Nat.le_pow_clog (by norm_num) P.order

/-- The old subgroup basis has precisely the known positive order. -/
public lemma subgroupDimension_eq (P : KnownOrderProblem G) :
    (OrderOracle.workspaceDimension (Carrier P) : Nat) = P.order :=
  carrier_card P

/-- Inject the identity-anchored subgroup basis without changing any numeric label. -/
public def groupLabel (P : KnownOrderProblem G) :
    Fin (OrderOracle.workspaceDimension (Carrier P)) ↪ Fin (2 ^ groupWidth P) where
  toFun label := ⟨label.val, label.isLt.trans_le (by
    rw [subgroupDimension_eq P]
    exact order_le_groupCapacity P)⟩
  inj' := by
    intro left right same
    exact Fin.ext
      (congrArg (fun label : Fin (2 ^ groupWidth P) => label.val) same)

/-- The source identity needs no initialization X gate under the chosen encoding. -/
@[simp] public lemma groupLabel_zero (P : KnownOrderProblem G) :
    groupLabel P 0 = 0 := by
  apply Fin.ext
  rfl

/-- The semantic group element carried by an occupied binary label. -/
public def encodeGroup (P : KnownOrderProblem G) (element : Carrier P) :
    Fin (2 ^ groupWidth P) :=
  groupLabel P ((OrderOracle.groupBasisEquiv (G := Carrier P)).symm element)

/-- Different group elements have different actual binary labels. -/
public lemma encodeGroup_injective (P : KnownOrderProblem G) :
    Function.Injective (encodeGroup P) :=
  (groupLabel P).injective.comp (OrderOracle.groupBasisEquiv (G := Carrier P)).symm.injective

/-- The identity is encoded by the all-zero bit string, even for a zero-width register. -/
@[simp] public lemma encodeGroup_one (P : KnownOrderProblem G) :
    encodeGroup P 1 = 0 := by
  unfold encodeGroup
  have identity : (OrderOracle.groupBasisEquiv (G := Carrier P)).symm 1 = 0 := by
    apply (OrderOracle.groupBasisEquiv (G := Carrier P)).injective
    rw [Equiv.apply_symm_apply, OrderOracle.groupBasisEquiv_zero]
  rw [identity]
  exact groupLabel_zero P

/-- The degenerate group occupies no quantum group wire. -/
public lemma groupWidth_order_one (P : KnownOrderProblem G) (trivial : P.order = 1) :
    groupWidth P = 0 := by simp [groupWidth, trivial]

/-- Zero-width encoding still has its single valid identity basis label. -/
public lemma encodeGroup_order_one (P : KnownOrderProblem G) (trivial : P.order = 1)
    (element : Carrier P) : encodeGroup P element = 0 := by
  apply Fin.ext
  have capacity : 2 ^ groupWidth P = 1 := by
    rw [groupWidth_order_one P trivial, pow_zero]
  have bound : (encodeGroup P element).val < 1 :=
    lt_of_lt_of_le (encodeGroup P element).isLt (le_of_eq capacity)
  simpa using Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound)

end

end QuantumAlg.FiniteCyclicDLP.Binary
