/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Carrier
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.PhaseOperator
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Components.Encoded.StateEmbedding
import all QuantumAlg.Core.Measure.Instrument
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact half-sum operator of a clean one-control native arithmetic stage

This is matrix algebra for the actual
leading-wire H/phase programs and actual clean selected arithmetic. The
carrier calculation retains exact phase and all source columns. The phase
parameter is an ordinary native gate parameter; no matrix or instrument
certificate is a premise. Integration of the finite store-selected feedback
prefix and equal-wire context placement is a separate remaining bridge.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.ControlKraus

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open NormalizedVector

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {S : Register}

def controlledBlock (operator : HilbertOperator S) : HilbertOperator ((Qubits 1).prod S) :=
  fun row column => if row.1 = column.1 then
    if column.1 = 0 then (1 : HilbertOperator S) row.2 column.2
    else operator row.2 column.2 else 0

def phaseBlock (phase : ℂ) : HilbertOperator ((Qubits 1).prod S) :=
  fun row column => if row.1 = column.1 then
    (if row.1 = 0 then 1 else phase) * (1 : HilbertOperator S) row.2 column.2 else 0

def resetBlock (outcome : Fin 2) : HilbertOperator ((Qubits 1).prod S) :=
  fun row column => if row.1 = 0 ∧ column.1 = outcome then
    (1 : HilbertOperator S) row.2 column.2 else 0

def hadamard : UnitaryOperator ((Qubits 1).prod S) :=
  UnitaryOperator.prodTensor Gate.HOp (1 : UnitaryOperator S)

def branch (operator : HilbertOperator S) (phase : ℂ) (outcome : Fin 2) :
    HilbertOperator ((Qubits 1).prod S) :=
  resetBlock outcome * (hadamard (S := S) : HilbertOperator ((Qubits 1).prod S)) *
    phaseBlock phase * controlledBlock operator *
      (hadamard (S := S) : HilbertOperator ((Qubits 1).prod S))

/-- The unnormalized branch acts on the persistent accumulator, never on a fresh seed. -/
def halfSum (operator : HilbertOperator S) (phase : ℂ) (outcome : Fin 2) :
    HilbertOperator S :=
  (2 : ℂ)⁻¹ • (1 + ((-1 : ℂ) ^ outcome.val * phase) • operator)

def zeroInjection : S.Index ↪ ((Qubits 1).prod S).Index :=
  ⟨fun seed => (0, seed), fun _ _ same => congrArg Prod.snd same⟩

/-- Exact zero-control input columns of H, controlled arithmetic, phase, H and reset. -/
lemma branch_zero_column (operator : HilbertOperator S) (phase : ℂ) (outcome : Fin 2)
    (row : ((Qubits 1).prod S).Index) (column : S.Index) :
    branch operator phase outcome row (0, column) =
      if row.1 = 0 then halfSum operator phase outcome row.2 column else 0 := by
  let op : Matrix S.Index S.Index Complex := operator
  let h : Matrix (Fin 2 × S.Index) (Fin 2 × S.Index) Complex := fun row column =>
    (Gate.HOp : Matrix (Fin 2) (Fin 2) Complex) row.1 column.1 *
      (if row.2 = column.2 then 1 else 0)
  let c : Matrix (Fin 2 × S.Index) (Fin 2 × S.Index) Complex := fun row column =>
    if row.1 = column.1 then
      if column.1 = 0 then (if row.2 = column.2 then 1 else 0)
      else op row.2 column.2 else 0
  let p : Matrix (Fin 2 × S.Index) (Fin 2 × S.Index) Complex := fun row column =>
    if row.1 = column.1 then
      (if row.1 = 0 then 1 else phase) * (if row.2 = column.2 then 1 else 0) else 0
  let reset : Matrix (Fin 2 × S.Index) (Fin 2 × S.Index) Complex := fun row column =>
    if row.1 = 0 ∧ column.1 = outcome then (if row.2 = column.2 then 1 else 0) else 0
  rcases row with ⟨bit, seed⟩
  change (reset * h * p * c * h) (bit, seed) (0, column) =
    if bit = 0 then
      ((2 : Complex)⁻¹ • (1 + ((-1 : Complex) ^ outcome.val * phase) • op) :
        Matrix S.Index S.Index Complex) seed column else 0
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
    smul_eq_mul]
  fin_cases bit <;> fin_cases outcome <;>
    simp [reset, h, p, c, Gate.HOp, UnitaryOperator.coe_ofMatrix,
      Fintype.sum_prod_type, Fin.sum_univ_two, mul_ite, ite_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq'] <;>
    ring_nf <;> simp only [invSqrt2_sq] <;> split_ifs <;> ring

/-- Full rectangular intertwiner: phase and coherent seed superpositions are preserved. -/
lemma branch_intertwines (operator : HilbertOperator S) (phase : ℂ) (outcome : Fin 2) :
    branch operator phase outcome * BasisEmbedding.matrix (zeroInjection (S := S)) =
      BasisEmbedding.matrix (zeroInjection (S := S)) * halfSum operator phase outcome := by
  classical
  let native : Matrix (Fin 2 × S.Index) (Fin 2 × S.Index) Complex :=
    branch operator phase outcome
  let source : Matrix S.Index S.Index Complex := halfSum operator phase outcome
  have columns (row : Fin 2 × S.Index) (column : S.Index) :
      native row (0, column) = if row.1 = 0 then source row.2 column else 0 :=
    branch_zero_column operator phase outcome row column
  ext row column
  change
    (∑ index : Fin 2 × S.Index,
      native row index * (if (0, column) = index then 1 else 0)) =
      ∑ index : S.Index, (if (0, index) = row then 1 else 0) * source index column
  simp only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
  rw [Fintype.sum_ite_eq, columns]
  rcases row with ⟨bit, seed⟩
  by_cases zero : bit = 0
  · subst bit
    simp only [Prod.mk.injEq, true_and, if_true]
    exact (Fintype.sum_ite_eq' seed (fun index => source index column)).symm
  · simp only [zero, if_false, Prod.mk.injEq, Ne.symm zero, false_and,
      Finset.sum_const_zero]

/-- Generic rectangular Kraus conjugation, used only after an actual intertwiner is proved. -/
private lemma conjugation_intertwines {R : Register}
    (injection : S.Index ↪ R.Index) (native : HilbertOperator R) (source : HilbertOperator S)
    (derived : native * BasisEmbedding.matrix injection = BasisEmbedding.matrix injection * source)
    (density : HilbertOperator S) :
    native * (BasisEmbedding.matrix injection * density *
        (BasisEmbedding.matrix injection).conjTranspose) * native.conjTranspose =
      BasisEmbedding.matrix injection * (source * density * source.conjTranspose) *
        (BasisEmbedding.matrix injection).conjTranspose := by
  have adjoint := congrArg Matrix.conjTranspose derived
  simp only [Matrix.conjTranspose_mul] at adjoint
  calc
    _ = (native * BasisEmbedding.matrix injection) * density *
        ((BasisEmbedding.matrix injection).conjTranspose * native.conjTranspose) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [derived, adjoint]; simp only [Matrix.mul_assoc]

/-- Arbitrary unnormalized mixed matrices obey the same complete branch equation. -/
lemma branch_mixed (operator : HilbertOperator S) (phase : ℂ) (outcome : Fin 2)
    (density : HilbertOperator S) :
    branch operator phase outcome *
        (BasisEmbedding.matrix (zeroInjection (S := S)) * density *
          (BasisEmbedding.matrix (zeroInjection (S := S))).conjTranspose) *
        (branch operator phase outcome).conjTranspose =
      BasisEmbedding.matrix (zeroInjection (S := S)) *
        (halfSum operator phase outcome * density *
          (halfSum operator phase outcome).conjTranspose) *
        (BasisEmbedding.matrix (zeroInjection (S := S))).conjTranspose :=
  conjugation_intertwines _ _ _ (branch_intertwines operator phase outcome) density

variable {width : Nat} (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]
  (positive : 0 < modulus.val)

/-- The real clean selected arithmetic is exactly the controlled translation block. -/
lemma controlledAction_matrix (coefficient : (ZMod modulus.val)ˣ) :
    (UnitaryOperator.ofPerm (Carrier.controlledAction modulus coefficient).symm :
      HilbertOperator (Carrier.full modulus.val)) =
    controlledBlock (Carrier.translation modulus coefficient :
      HilbertOperator (Carrier.units modulus.val)) := by
  have pairEq (leftBit rightBit : (Qubits 1).Index)
      (leftSeed rightSeed : (Carrier.units modulus.val).Index) :
      (((leftBit, leftSeed) : (Carrier.full modulus.val).Index) =
        (rightBit, rightSeed)) ↔ leftBit = rightBit ∧ leftSeed = rightSeed := by
    constructor
    · intro same
      exact ⟨congrArg (fun label : (Carrier.full modulus.val).Index => label.1) same,
        congrArg (fun label : (Carrier.full modulus.val).Index => label.2) same⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  ext row column
  rcases row with ⟨rowBit, rowSeed⟩
  rcases column with ⟨columnBit, columnSeed⟩
  simp only [controlledBlock, Carrier.translation, UnitaryOperator.ofPerm_entry,
    Matrix.one_apply, Equiv.symm_apply_eq]
  fin_cases rowBit <;> fin_cases columnBit
  · simp only [Nat.reducePow, Fin.zero_eta, Fin.isValue, Carrier.controlledAction,
      Equiv.prodCongrRight,
      Nat.testBit_zero, decide_eq_true_eq, Equiv.coe_mulLeft, ite_mul, one_mul,
      Equiv.mulLeft_symm, Equiv.coe_fn_mk,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_ne_one, ↓reduceIte, pairEq, true_and]
  · simp only [Nat.reducePow, Fin.zero_eta, Fin.isValue, Carrier.controlledAction,
      Equiv.prodCongrRight,
      Nat.testBit_zero, decide_eq_true_eq, Equiv.coe_mulLeft, ite_mul, one_mul,
      Equiv.mulLeft_symm, Fin.mk_one,
      Equiv.coe_fn_mk, Fin.coe_ofNat_eq_mod, Nat.mod_succ, ↓reduceIte, pairEq, zero_ne_one,
      false_and]
  · simp only [Nat.reducePow, Fin.mk_one, Fin.isValue, Carrier.controlledAction,
      Equiv.prodCongrRight,
      Nat.testBit_zero, decide_eq_true_eq, Equiv.coe_mulLeft, ite_mul, one_mul,
      Equiv.mulLeft_symm, Fin.zero_eta,
      Equiv.coe_fn_mk, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_ne_one, ↓reduceIte, pairEq,
      one_ne_zero, false_and]
  · simp only [Nat.reducePow, Fin.mk_one, Fin.isValue, Carrier.controlledAction,
      Equiv.prodCongrRight,
      Nat.testBit_zero, decide_eq_true_eq, Equiv.coe_mulLeft, ite_mul, one_mul,
      Equiv.mulLeft_symm, Equiv.coe_fn_mk,
      Fin.coe_ofNat_eq_mod, Nat.mod_succ, ↓reduceIte, pairEq, true_and, one_ne_zero]
    split_ifs with same
    · exact (if_pos same).symm
    · exact (if_neg same).symm

/-- Exact source matrix of the actual phase gate beside the untouched unit carrier. -/
lemma phase_matrix (angle : ℝ) :
    (UnitaryOperator.prodTensor (phaseGateOp angle)
      (1 : UnitaryOperator (Carrier.units modulus.val)) :
        HilbertOperator (Carrier.full modulus.val)) =
      phaseBlock (Complex.exp ((angle : ℂ) * Complex.I)) := by
  ext row column
  rcases row with ⟨rowBit, rowSeed⟩
  rcases column with ⟨columnBit, columnSeed⟩
  fin_cases rowBit <;> fin_cases columnBit <;>
    simp [phaseBlock, phaseGateOp, UnitaryOperator.coe_ofMatrix]

/-- This is a literal native one-control prefix, before its real measurement/reset. -/
def nativePreparation (coefficient : (ZMod modulus.val)ˣ) (angle : ℝ) :=
  (Carrier.oneQubit (width := width) Gate.HOp).seq
    ((Arithmetic.program modulus coefficient).seq
      ((Carrier.oneQubit (width := width) (phaseGateOp angle)).seq
        (Carrier.oneQubit (width := width) Gate.HOp)))

def sourcePreparation (coefficient : (ZMod modulus.val)ˣ) (angle : ℝ) :
    UnitaryOperator (Carrier.full modulus.val) :=
  (hadamard * UnitaryOperator.prodTensor (phaseGateOp angle) (1 : UnitaryOperator _)) *
    UnitaryOperator.ofPerm (Carrier.controlledAction modulus coefficient).symm * hadamard

/-- Native H/arithmetic/phase/H supplies this matrix equality, rather than assumes it. -/
lemma nativePreparation_intertwines (coefficient : (ZMod modulus.val)ˣ) (angle : ℝ) :
    (((nativePreparation modulus coefficient angle).matrix environment) :
        HilbertOperator (Carrier.physical width)) *
      BasisEmbedding.matrix (Carrier.embedding modulus positive) =
    BasisEmbedding.matrix (Carrier.embedding modulus positive) *
      (sourcePreparation modulus coefficient angle : HilbertOperator (Carrier.full modulus.val)) :=
    by
  let j := BasisEmbedding.matrix (Carrier.embedding modulus positive)
  let hNative : HilbertOperator (Carrier.physical width) :=
    ((Carrier.oneQubit (width := width) Gate.HOp).matrix environment)
  let cNative : HilbertOperator (Carrier.physical width) :=
    ((Arithmetic.program modulus coefficient).matrix environment)
  let pNative : HilbertOperator (Carrier.physical width) :=
    ((Carrier.oneQubit (width := width) (phaseGateOp angle)).matrix environment)
  let hSource : HilbertOperator (Carrier.full modulus.val) :=
    hadamard (S := Carrier.units modulus.val)
  let cSource : HilbertOperator (Carrier.full modulus.val) :=
    UnitaryOperator.ofPerm (Carrier.controlledAction modulus coefficient).symm
  let pSource : HilbertOperator (Carrier.full modulus.val) :=
    UnitaryOperator.prodTensor (phaseGateOp angle)
      (1 : UnitaryOperator (Carrier.units modulus.val))
  have h : hNative * j = j * hSource :=
    Carrier.oneQubit_intertwines modulus positive Gate.HOp
  have p : pNative * j = j * pSource :=
    Carrier.oneQubit_intertwines modulus positive (phaseGateOp angle)
  have c : cNative * j = j * cSource :=
    Carrier.arithmetic_intertwines modulus positive coefficient
  simp only [nativePreparation, UnitaryCircuit.seq_matrix, sourcePreparation,
    Submonoid.coe_mul]
  change (hNative * pNative * cNative * hNative) * j =
    j * (((hSource * pSource) * cSource) * hSource)
  calc
    _ = hNative * (pNative * (cNative * (hNative * j))) := by
      simp only [Matrix.mul_assoc]
    _ = hNative * (pNative * (cNative * (j * hSource))) := by rw [h]
    _ = hNative * (pNative * ((cNative * j) * hSource)) := by
      simp only [Matrix.mul_assoc]
    _ = hNative * (pNative * ((j * cSource) * hSource)) := by rw [c]
    _ = hNative * ((pNative * j) * (cSource * hSource)) := by
      simp only [Matrix.mul_assoc]
    _ = hNative * ((j * pSource) * (cSource * hSource)) := by rw [p]
    _ = (hNative * j) * (pSource * (cSource * hSource)) := by
      simp only [Matrix.mul_assoc]
    _ = (j * hSource) * (pSource * (cSource * hSource)) := by rw [h]
    _ = _ := by simp only [Matrix.mul_assoc]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.ControlKraus
