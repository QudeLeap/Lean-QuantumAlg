/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Arithmetic
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Clean.Subspace
import all QuantumAlg.Components.Encoded.StateEmbedding
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Unitary.Permutation
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Word

/-!
# Actual single-control arithmetic and one-qubit gates on the clean unit carrier

The carrier includes both control values
and any modular-unit seed, with the actual arithmetic auxiliary word zero.
Exact native ket action supplies the arithmetic intertwiner. The native
leading-wire matrix supplies the H/phase intertwiner. Neither is an input
certificate of the public problem. Modulus one and zero arithmetic width are
retained whenever the existing fitted positive-modulus program admits them.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Carrier

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth

abbrev units (N : Nat) [NeZero N] : Register where
  Index := (ZMod N)ˣ
  fintype := inferInstance
  decEq := inferInstance

abbrev full (N : Nat) [NeZero N] : Register := (Qubits 1).prod (units N)

abbrev physical (width : Nat) : Register := (Arithmetic.layout width).toQuantum.register

variable {width : Nat} (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]
  (positive : 0 < modulus.val)

/-- The actual power/zero-auxiliary word is injective on all units of this modulus. -/
def workspaceWord : (units modulus.val).Index ↪ Fin (2 ^ (workspaceEncoding width).width) where
  toFun seed := (workspaceEncoding width).encode (unitResidueWord modulus positive seed, 0)
  inj' := by
    intro left right same
    have pair := (workspaceEncoding width).encode_injective same
    have values := congrArg (fun words : WorkspaceRegisters width => words.1.val) pair
    apply Units.ext
    exact ZMod.val_injective modulus.val values

/-- Physical labels keep the actual control and actual native arithmetic workspace. -/
def embedding : (full modulus.val).Index ↪ (physical width).Index where
  toFun label := (Arithmetic.layout width).basisEquiv.symm
    (prodEquiv (label.1, workspaceWord modulus positive label.2))
  inj' := by
    intro left right same
    have words := prodEquiv.injective ((Arithmetic.layout width).basisEquiv.symm.injective same)
    have controls : left.1 = right.1 :=
      congrArg (fun pair : Fin 2 × Fin (2 ^ (workspaceEncoding width).width) => pair.1) words
    have workspaces : workspaceWord modulus positive left.2 =
        workspaceWord modulus positive right.2 :=
      congrArg (fun pair : Fin 2 × Fin (2 ^ (workspaceEncoding width).width) => pair.2) words
    exact Prod.ext controls ((workspaceWord modulus positive).injective workspaces)

/-- The encoded control is the actual first native physical wire. -/
lemma embedding_control (label : (full modulus.val).Index) :
    embedding modulus positive label (0 : Fin (1 + (workspaceEncoding width).width)) =
      label.1 := by
  change ((QuantumSignature.qubitsIndexEquiv (1 + (workspaceEncoding width).width)).symm
    (prodEquiv (label.1, workspaceWord modulus positive label.2)))
      ⟨0, by change 0 < 1 + (workspaceEncoding width).width; omega⟩ = label.1
  exact Gate.firstDecoded (workspaceEncoding width).width label.1
    (workspaceWord modulus positive label.2)

/-- Only the internally prepared/reset control-zero subspace is used between stages. -/
def zeroEmbedding : (units modulus.val).Index ↪ (physical width).Index :=
  (⟨fun seed => ((0 : Fin 2), seed), fun _ _ same => congrArg Prod.snd same⟩ :
      (units modulus.val).Index ↪ (full modulus.val).Index).trans
    (embedding modulus positive)

/-- The actual native control selects multiplication by the coefficient or identity. -/
def controlledAction (coefficient : (ZMod modulus.val)ˣ) :
    Equiv.Perm (full modulus.val).Index :=
  Equiv.prodCongrRight fun bit =>
    Equiv.mulLeft (if bit.val.testBit 0 then coefficient else 1)

/-- Translation of the same unit seed, with its full coherent phase. -/
def translation (coefficient : (ZMod modulus.val)ˣ) : UnitaryOperator (units modulus.val) :=
  UnitaryOperator.ofPerm (Equiv.mulLeft coefficient).symm

/-- The existing actual arithmetic program preserves this whole coherent clean carrier. -/
lemma arithmetic_intertwines (coefficient : (ZMod modulus.val)ˣ) :
    (((Arithmetic.program modulus coefficient).matrix environment) :
        HilbertOperator (physical width)) *
        BasisEmbedding.matrix (embedding modulus positive) =
      BasisEmbedding.matrix (embedding modulus positive) *
        (UnitaryOperator.ofPerm (controlledAction modulus coefficient).symm :
          HilbertOperator (full modulus.val)) := by
  apply CleanSubspace.intertwines_of_kets
  intro label
  exact Arithmetic.program_clean_unit modulus positive coefficient label.2 label.1

/-- Place the exact one-qubit operator at the existing first physical control wire. -/
def oneQubit (operator : UnitaryOperator (Qubits 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (Arithmetic.layout width).toQuantum :=
  Gate.singleQubitAt (Arithmetic.layout width).toQuantum .empty operator
    ⟨0, by
      rw [Arithmetic.width_eq]
      exact Nat.add_pos_left Nat.zero_lt_one (2 * width)⟩ rfl

/-- The actual native leading-wire operator acts beside identity on the clean unit seed. -/
lemma oneQubit_intertwines (operator : UnitaryOperator (Qubits 1)) :
    (((oneQubit (width := width) operator).matrix environment) : HilbertOperator (physical width)) *
        BasisEmbedding.matrix (embedding modulus positive) =
      BasisEmbedding.matrix (embedding modulus positive) *
        (UnitaryOperator.prodTensor operator (1 : UnitaryOperator (units modulus.val)) :
          HilbertOperator (full modulus.val)) := by
  classical
  apply BasisEmbedding.intertwines_of_columns
  intro row column
  obtain ⟨⟨rowControl, rowWorkspace⟩, decomposed⟩ :=
    (prodEquiv (m := 1) (n := (workspaceEncoding width).width)).surjective
      ((Arithmetic.layout width).basisEquiv row)
  have rowEquation : row = (Arithmetic.layout width).basisEquiv.symm
      (prodEquiv (rowControl, rowWorkspace)) := by
    rw [decomposed, Equiv.symm_apply_apply]
  subst row
  have native := congrArg
    (fun actual : UnitaryOperator (Qubits (1 + (workspaceEncoding width).width)) =>
      actual (prodEquiv (rowControl, rowWorkspace))
        (prodEquiv (column.1, workspaceWord modulus positive column.2)))
    (Gate.singleQubitAt_first_binaryMatrix .empty (workspaceEncoding width).width
      operator environment)
  change ((oneQubit (width := width) operator).matrix environment)
      ((Arithmetic.layout width).basisEquiv.symm (prodEquiv (rowControl, rowWorkspace)))
      (embedding modulus positive column) = _ at native
  rw [native, UnitaryOperator.tensor_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  change
    (operator : Matrix (Fin 2) (Fin 2) Complex) rowControl column.1 *
        (if rowWorkspace = workspaceWord modulus positive column.2 then 1 else 0) =
      ∑ index : Fin 2 × (units modulus.val).Index,
        if embedding modulus positive index =
            (Arithmetic.layout width).basisEquiv.symm (prodEquiv (rowControl, rowWorkspace)) then
          (operator : Matrix (Fin 2) (Fin 2) Complex) index.1 column.1 *
            (if index.2 = column.2 then 1 else 0) else 0
  rw [Fintype.sum_prod_type]
  have seedSum (bit : Fin 2) :
      (∑ seed : (units modulus.val).Index,
        if embedding modulus positive (bit, seed) =
            (Arithmetic.layout width).basisEquiv.symm (prodEquiv (rowControl, rowWorkspace)) then
          (operator : Matrix (Fin 2) (Fin 2) Complex) bit column.1 *
            (if seed = column.2 then 1 else 0) else 0) =
      if embedding modulus positive (bit, column.2) =
          (Arithmetic.layout width).basisEquiv.symm (prodEquiv (rowControl, rowWorkspace)) then
        (operator : Matrix (Fin 2) (Fin 2) Complex) bit column.1 else 0 := by
    rw [Finset.sum_eq_single column.2]
    · simp only [if_true, mul_one]
    · intro seed _ different
      simp only [if_neg different, mul_zero, ite_self]
    · intro absent
      exact False.elim (absent (Finset.mem_univ _))
  simp_rw [seedSum]
  have labels (bit : Fin 2) :
      embedding modulus positive (bit, column.2) =
          (Arithmetic.layout width).basisEquiv.symm (prodEquiv (rowControl, rowWorkspace)) ↔
        bit = rowControl ∧ workspaceWord modulus positive column.2 = rowWorkspace := by
    exact (Arithmetic.layout width).basisEquiv.symm.injective.eq_iff.trans
      (prodEquiv.injective.eq_iff.trans
        ⟨fun same => Prod.mk.inj same, fun same => Prod.ext same.1 same.2⟩)
  simp_rw [labels]
  by_cases sameWorkspace : workspaceWord modulus positive column.2 = rowWorkspace
  · simp only [sameWorkspace, and_true, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [mul_one]
  · have reversed : rowWorkspace ≠ workspaceWord modulus positive column.2 := Ne.symm sameWorkspace
    simp only [sameWorkspace, reversed, and_false, if_false, mul_zero, Finset.sum_const_zero]

/-- Every clean coherent vector with an untouched reference follows the actual arithmetic. -/
lemma arithmetic_coherent_reference (coefficient : (ZMod modulus.val)ˣ)
    (Reference : Register) (state : HilbertVector ((full modulus.val).prod Reference)) :
    (UnitaryOperator.prodTensor ((Arithmetic.program modulus coefficient).matrix environment)
        (1 : UnitaryOperator Reference)).applyVec
      (Effect.extensionVector
        (BasisEmbedding.withReference (embedding modulus positive) Reference) state) =
    Effect.extensionVector
      (BasisEmbedding.withReference (embedding modulus positive) Reference)
      ((UnitaryOperator.prodTensor
        (UnitaryOperator.ofPerm (controlledAction modulus coefficient).symm)
        (1 : UnitaryOperator Reference)).applyVec state) :=
  BasisEmbedding.applyVec_extension _ _ _
    (BasisEmbedding.reference_intertwines _ _ _
      (arithmetic_intertwines modulus positive coefficient) Reference) state

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Carrier
