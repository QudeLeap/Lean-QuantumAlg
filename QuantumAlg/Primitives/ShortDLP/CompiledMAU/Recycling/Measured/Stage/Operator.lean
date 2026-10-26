/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Readout.Matrix
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Feedback.Carrier
import all
  QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument.Reference
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Placement.Zero

/-!
# Actual chronological operators of the complete measured exponent stage

The recorded branch uses the actual measured arithmetic word, the feedback
selected by its real output Store, and the actual final H/MZ/reset branch.
The chronological measurement outcomes remain distinct even when the same
arithmetic cells are overwritten [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured
open MAU.Addition.Gidney.Measured.Instruction EncodedBit.MeasuredUncompute
open scoped Kronecker

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]

/-- Every physical arithmetic measurement outcome of this original exponent position. -/
abbrev stageArithmeticOutcomes (wide : 2 ≤ width) (unit : (ZMod modulus.toNat)ˣ)
    {bits : Nat} (position : Fin bits) :=
  WordOutcomes (Physical.qubits width) (context_wires base noQuantum m ell width)
    ((Physical.layout width).multiplicationWord wide modulus
      ((unit ^ (2 ^ position.rev.val) : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val
      (((unit ^ (2 ^ position.rev.val))⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val)

/-- The actual arithmetic output Store and full path preceding the feedback prefix. -/
def stageArithmeticRecord (wide : 2 ≤ width) (unit : (ZMod modulus.toNat)ˣ)
    {bits : Nat} (position : Fin bits) (store : Store (Context base noQuantum m ell width))
    (measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position) :
    Store (Context base noQuantum m ell width) ×
      (arithmetic base noQuantum m ell width wide modulus
        (unit ^ (2 ^ position.rev.val))).Path :=
  wordActualRecord (oracles := .empty) (operations := BitWord.model) (services := .empty)
    (Physical.qubits width) (context_wires base noQuantum m ell width)
    (ventCell base noQuantum m ell width)
    ((Physical.layout width).multiplicationWord wide modulus
      ((unit ^ (2 ^ position.rev.val) : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val
      (((unit ^ (2 ^ position.rev.val))⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val)
    store measured

/-- The arithmetic segment's actual chronological native matrices for the original exponent bit. -/
def stageArithmeticKraus (wide : 2 ≤ width) {bits : Nat}
    (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits) (environment : model.Environment)
    (store : Store (Context base noQuantum m ell width))
    (measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position)
    (Reference : Register) :
    HilbertOperator ((Context base noQuantum m ell width).register.prod Reference) :=
  wordActualKraus (oracles := .empty) (operations := BitWord.model) (services := .empty)
      (Physical.qubits width) (context_wires base noQuantum m ell width)
      (ventCell base noQuantum m ell width) environment.quantum Reference
      ((Physical.layout width).multiplicationWord wide modulus
        ((unit ^ (2 ^ position.rev.val) : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val
        (((unit ^ (2 ^ position.rev.val))⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val)
      store measured

/-- The chronological native matrix product of one actual complete measured stage record. -/
def stageActualKraus (wide : 2 ≤ width) (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits) (environment : model.Environment)
    (store : Store (Context base noQuantum m ell width))
    (measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position)
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) (Reference : Register) :
    HilbertOperator ((Context base noQuantum m ell width).register.prod Reference) :=
  krausOperator (oracles := .empty) (control base noQuantum m ell width)
      (control_qubit base noQuantum m ell width) environment.quantum outcome Reference *
    (UnitaryOperator.prodTensor
      (feedbackAction base noQuantum m ell width environment.quantum inverse outputs position
        position.val le_rfl
        (stageArithmeticRecord base noQuantum m ell width modulus wide unit position store
          measured).1) (1 : UnitaryOperator Reference) :
            HilbertOperator ((Context base noQuantum m ell width).register.prod Reference)) *
    stageArithmeticKraus base noQuantum m ell width modulus wide unit position environment store
      measured Reference *
    (UnitaryOperator.prodTensor
      ((single base noQuantum m ell width Gate.HOp).matrix environment.quantum)
      (1 : UnitaryOperator Reference) :
        HilbertOperator ((Context base noQuantum m ell width).register.prod Reference))

/-- The actual first H has the full logical H action beside the untouched reference. -/
lemma hadamard_reference_intertwines (environment : OracleModel.empty.Interpretation)
    (Reference : Register) :
    (UnitaryOperator.prodTensor
      ((single base noQuantum m ell width Gate.HOp).matrix environment)
      (1 : UnitaryOperator Reference) :
        HilbertOperator ((Context base noQuantum m ell width).register.prod Reference)) *
      BasisEmbedding.matrix
        (arithmeticJointEmbedding base noQuantum m ell width modulus Reference) =
    BasisEmbedding.matrix
        (arithmeticJointEmbedding base noQuantum m ell width modulus Reference) *
      sourceWithReference
        (Recycling.ControlKraus.hadamard (S := Recycling.Carrier.units modulus.toNat) :
          HilbertOperator (Recycling.Carrier.full modulus.toNat)) Reference := by
  have derived := Recycling.NativeBranch.reference_intertwines _ _ _
    (Placement.hadamard_intertwines base noQuantum m ell width modulus environment) Reference
  simpa only [unitaryOperator_prodTensor_identity, arithmeticJointEmbedding,
    Recycling.ControlKraus.hadamard, sourceWithReference_kronecker] using derived

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
