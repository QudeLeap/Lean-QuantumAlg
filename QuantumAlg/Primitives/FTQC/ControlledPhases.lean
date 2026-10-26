/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.FTQC.Toffoli7T.Realization
import all QuantumAlg.Primitives.FTQC.CliffordLayers
import all QuantumAlg.Primitives.FTQC.Toffoli7T.Realization
import all QuantumAlg.Primitives.FTQC.Toffoli7T.Resources
import all QuantumAlg.Analysis.FTQC.CliffordT.Word
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.Gates
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.QubitPrimitive
import all QuantumAlg.Components.QubitPrimitive.Operator
import all QuantumAlg.Core.Base.WireAddress
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Core.Base
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Util.FinPow
import all QuantumAlg.Util.Matrix.Diagonal
import all QuantumAlg.Util.Sum
import all QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import Mathlib.Tactic

/-!
# Exact controlled phases over Clifford+T

Controlled-S uses the integer identity a+b-(a xor b)=2ab. Controlled-controlled-Z
is obtained by conjugating the target of the seven-T Toffoli by Hadamards.
These phase-exact identities use the gate conventions of Nielsen and Chuang,
Chapter 4 (citation-only).
-/

public section

namespace QuantumAlg.FTQC

open CliffordT Gate UnitaryCircuit

open NormalizedVector

noncomputable section

/-- Controlled-S on the big-endian two-qubit interface, active at control one. -/
def controlledSOp : UnitaryOperator (Qubits 2) :=
  UnitaryOperator.reindex (prodEquiv (m := 1) (n := 1))
    (UnitaryOperator.controlled (Qubits 1) 1 SOp)

/-- Three T gates; the one adjoint is expanded to three additional S gates. -/
def controlledSCircuit (oracles : OracleModel) : CliffordCircuit oracles 2 := blocks
  [layer2 oracles [.t] [.t], cx oracles 0 1 (by decide),
    layer2 oracles [] tDaggerWord, cx oracles 0 1 (by decide)]

-- Normalize bit permutations only after a finite index has been instantiated.
local macro "phaseScalar" : tactic =>
  `(tactic| norm_num [Nat.shiftRight_eq_div_pow, Matrix.submatrix_apply,
    QubitPrimitive.perm, WireAddress.cnotPerm, WireAddress.toffoliPerm,
    WireAddress.cnotMap, WireAddress.toffoliMap, WireAddress.flipBit,
    WireAddress.bitIndex, prodEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
    Nat.testBit])

private lemma sqrtTwo_inv_mul_self :
    (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← pow_two, Toffoli7TProof.sqrtTwo_inv_sq]

lemma controlledS_matrix (oracles : OracleModel) (environment : oracles.Interpretation) :
    (controlledSCircuit oracles).binaryMatrix environment = controlledSOp := by
  simp only [controlledSCircuit, blocks_matrix, List.foldl_cons, List.foldl_nil,
    layer2_matrix, cx_matrix]
  apply Subtype.ext
  simp only [tDaggerWord, evalOp, Letter.op, mul_one, one_mul]
  simp only [Matrix.UnitaryGroup.mul_apply, Matrix.UnitaryGroup.one_apply,
    UnitaryOperator.coe_tensor, Toffoli7TProof.sOp_diagonal,
    Toffoli7TProof.tOp_diagonal,
    ← Matrix.diagonal_one, Matrix.diagonal_mul_diagonal]
  repeat' rw [tensor_diagonal]
  simp only [QubitPrimitive.operator,
    UnitaryOperator.ofPerm, UnitaryOperator.coe_ofMatrix,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  simp only [diagonal_mul_matrix, Matrix.submatrix_apply]
  try simp only [id_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [controlledSCircuit, controlledSOp, blocks, sequenceList, layer2,
      word_matrix, cx, tDaggerWord, evalOp, Letter.op,
      seq_matrix, identity_matrix, UnitaryOperator.coe_tensor,
      SOp, Toffoli7TProof.tOp_entries, QubitPrimitive.operator,
      UnitaryOperator.ofPerm,
      UnitaryOperator.controlled_apply, UnitaryOperator.coe_reindex,
      HilbertOperator.tensor_apply, prodEquiv,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply] <;>
    phaseScalar <;>
    ring_nf <;>
    (norm_num [Toffoli7TProof.sqrtTwo_sq, Real.sq_sqrt, Complex.I_sq];
      try ring)

/-- Phase-exact strict-model controlled-S realization. -/
def controlledS (oracles : OracleModel) :
    UnitaryCircuit.ExactRealization CliffordTGate.model oracles
      (QuantumSignature.qubits 2).canonicalPlacement.layout
      (fun _ =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2).symm controlledSOp) where
  circuit := controlledSCircuit oracles
  matrix_eq environment := matrix_of_binaryMatrix_eq _ _ environment
    (controlledS_matrix oracles environment)

lemma controlledS_tCount (oracles : OracleModel) :
    circuitTCount (controlledSCircuit oracles) = 3 := by
  simp [circuitTCount, controlledSCircuit, tDaggerWord, Letter.circuit_eventCost,
    ResourcePool.count, ResourcePool.singleton, Letter.event]

/-- Independent controlled-controlled-Z specification. -/
def cczOp : UnitaryOperator (Qubits 3) :=
  UnitaryOperator.ofMatrix (Matrix.diagonal (fun i : Fin 8 => if i = 7 then -1 else 1))
    (by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Fin.ext_iff])

/-- Hadamard conjugation of the same seven-T Toffoli realization. -/
def cczCircuit (oracles : OracleModel) : CliffordCircuit oracles 3 := blocks
  [layer3 oracles [] [] [.h], toffoli7TCircuit oracles, layer3 oracles [] [] [.h]]

set_option maxHeartbeats 2000000 in
-- Bound the finite arithmetic needed for this exact three-qubit matrix.
lemma ccz_matrix (oracles : OracleModel) (environment : oracles.Interpretation) :
    (cczCircuit oracles).binaryMatrix environment = cczOp := by
  simp only [cczCircuit, blocks_matrix, List.foldl_cons, List.foldl_nil,
    layer3_matrix, toffoli7T_matrix]
  apply Subtype.ext
  simp only [Matrix.UnitaryGroup.mul_apply, Matrix.UnitaryGroup.one_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cczCircuit, blocks, sequenceList, toffoli7T_matrix,
      toffoliOp, layer3, layer2, word_matrix, evalOp, Letter.op,
      seq_matrix, identity_matrix, UnitaryOperator.coe_tensor, HOp, cczOp,
      QubitPrimitive.operator, UnitaryOperator.ofPerm,
      HilbertOperator.tensor_apply, prodEquiv,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply, invSqrt2] <;>
    (first |
      (rw [sumFinEightOfCard]
       all_goals first
         | decide +kernel
         | phaseScalar)) <;>
    (conv =>
      lhs
      lhs
      rhs
      rw [sumFinEightOfCard]) <;>
    (conv =>
      lhs
      rhs
      rhs
      rw [sumFinEightOfCard]) <;>
    simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMul, Fin.isValue,
      Fin.cast_eq_self, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.zero_div,
      zero_ne_one, OfNat.zero_ne_ofNat, ↓reduceIte, Nat.one_mod,
      Nat.reduceDiv, add_zero, Nat.reduceMod, Order.lt_two_iff, zero_le,
      Nat.div_self, Nat.mod_self, OfNat.one_ne_ofNat, Nat.succ_ne_self,
      Nat.reduceEqDiff, Fin.zero_eta, Matrix.cons_val_zero, zero_add,
      Fin.reduceEq, Nat.mod_succ, Fin.mk_one, Matrix.cons_val_one, mul_neg,
      neg_neg, Fin.reduceFinMk] <;>
    (try ring_nf
     all_goals try rw [Toffoli7TProof.sqrtTwo_inv_sq]
     all_goals norm_num [Toffoli7TProof.sqrtTwo_sq,
       Toffoli7TProof.sqrtTwo_inv_sq, sqrtTwo_inv_mul_self,
       Real.sq_sqrt, Fin.ext_iff])

/-- Exact strict-model CCZ, retaining every native instruction. -/
def ccz (oracles : OracleModel) :
    UnitaryCircuit.ExactRealization CliffordTGate.model oracles
      (QuantumSignature.qubits 3).canonicalPlacement.layout
      (fun _ => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 3).symm cczOp) where
  circuit := cczCircuit oracles
  matrix_eq environment := matrix_of_binaryMatrix_eq _ _ environment
    (ccz_matrix oracles environment)

lemma ccz_tCount (oracles : OracleModel) :
    circuitTCount (cczCircuit oracles) = 7 := by
  simp [circuitTCount, cczCircuit, toffoli7T_eventCost, toffoli7TEvents,
    Letter.circuit_eventCost, ResourcePool.count, ResourcePool.singleton, Letter.event]

end

end QuantumAlg.FTQC
