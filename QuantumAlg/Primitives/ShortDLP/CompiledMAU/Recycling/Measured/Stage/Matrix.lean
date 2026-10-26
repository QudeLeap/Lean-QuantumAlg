/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Operator

/-!
# Common-alpha action of the complete actual measured stage

The actual first H, measured arithmetic, Store-selected paid feedback and
last H/MZ/reset are composed on the same original unit accumulator. The
rectangular identity includes arbitrary external-reference coherences and
every physical arithmetic outcome [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured
open MAU.Addition.Gidney.Measured.Instruction EncodedBit.MeasuredUncompute
open scoped Kronecker

private lemma sourceWithReference_mul {Local : Register}
    (first second : HilbertOperator Local) (Reference : Register) :
    sourceWithReference first Reference * sourceWithReference second Reference =
      sourceWithReference (first * second) Reference := by
  simpa only [sourceWithReference_kronecker] using
    (HilbertOperator.kronecker_identity_mul (Reference := Reference) first second)

private lemma readoutSource_reference {Local : Register} (outcome : Fin 2)
    (Reference : Register) :
    readoutSource (S := Local) outcome Reference =
      sourceWithReference
        (Recycling.ControlKraus.resetBlock outcome *
          (Recycling.ControlKraus.hadamard (S := Local) :
            HilbertOperator ((Qubits 1).prod Local))) Reference := rfl

private lemma four_intertwines {R S : Register}
    (embedding : Matrix R.Index S.Index ℂ)
    (last feedback arithmetic first : HilbertOperator R)
    (lastSource feedbackSource arithmeticSource firstSource : HilbertOperator S) (scalar : ℂ)
    (lastAction : last * embedding = embedding * lastSource)
    (feedbackAction : feedback * embedding = embedding * feedbackSource)
    (arithmeticAction : arithmetic * embedding = scalar • (embedding * arithmeticSource))
    (firstAction : first * embedding = embedding * firstSource) :
    (last * feedback * arithmetic * first) * embedding =
      scalar • (embedding * (lastSource * feedbackSource * arithmeticSource * firstSource)) := by
  calc
    _ = last * (feedback * (arithmetic * (first * embedding))) := by
      simp only [Matrix.mul_assoc]
    _ = last * (feedback * (arithmetic * (embedding * firstSource))) := by rw [firstAction]
    _ = last * (feedback * ((arithmetic * embedding) * firstSource)) := by
      simp only [Matrix.mul_assoc]
    _ = last * (feedback * ((scalar • (embedding * arithmeticSource)) * firstSource)) := by
      rw [arithmeticAction]
    _ = scalar • ((last * (feedback * embedding)) * (arithmeticSource * firstSource)) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = scalar • ((embedding * lastSource * feedbackSource) *
        (arithmeticSource * firstSource)) := by
      rw [feedbackAction, ← Matrix.mul_assoc last embedding feedbackSource, lastAction]
    _ = _ := by simp only [Matrix.mul_assoc]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]

/-- Full physical stage columns have one arithmetic scalar and the independent logical branch. -/
lemma stageActualKraus_full_matrix (wide : 2 ≤ width) (positive : 0 < modulus.toNat)
    (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits) (environment : model.Environment)
    (store : Store (Context base noQuantum m ell width))
    (measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position)
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) (Reference : Register) :
    stageActualKraus base noQuantum m ell width modulus wide inverse outputs unit position
        environment store measured outcome Reference *
      BasisEmbedding.matrix
        (arithmeticJointEmbedding base noQuantum m ell width modulus Reference) =
    arithmeticAlpha width modulus (unit ^ (2 ^ position.rev.val)) •
      (BasisEmbedding.matrix
          (arithmeticJointEmbedding base noQuantum m ell width modulus Reference) *
        sourceWithReference (Recycling.ControlKraus.branch
          (unitTranslation modulus (unit ^ (2 ^ position.rev.val)) :
            HilbertOperator (Recycling.Carrier.units modulus.toNat))
          (feedbackScalar base noQuantum m ell width inverse outputs position position.val le_rfl
            (stageArithmeticRecord base noQuantum m ell width modulus wide unit position store
              measured).1)
          (placedOutcome (Physical.layout width).control (Physical.qubits width)
            (Context base noQuantum m ell width) (context_wires base noQuantum m ell width)
            outcome)) Reference) := by
  have arithmeticAction := measuredArithmetic_record_matrix base noQuantum m ell width modulus
    wide positive (unit ^ (2 ^ position.rev.val)) environment store measured Reference
  rw [arithmeticReference_matrix, controlledAction_matrix] at arithmeticAction
  have composed := four_intertwines _ _ _ _ _
    (readoutSource (S := Recycling.Carrier.units modulus.toNat)
      (placedOutcome (Physical.layout width).control (Physical.qubits width)
        (Context base noQuantum m ell width) (context_wires base noQuantum m ell width) outcome)
      Reference)
    (sourceWithReference (Recycling.ControlKraus.phaseBlock
      (S := Recycling.Carrier.units modulus.toNat)
      (feedbackScalar base noQuantum m ell width inverse outputs position position.val le_rfl
        (stageArithmeticRecord base noQuantum m ell width modulus wide unit position store
          measured).1)) Reference)
    (sourceWithReference (Recycling.ControlKraus.controlledBlock
      (unitTranslation modulus (unit ^ (2 ^ position.rev.val)) :
        HilbertOperator (Recycling.Carrier.units modulus.toNat))) Reference)
    (sourceWithReference (Recycling.ControlKraus.hadamard
      (S := Recycling.Carrier.units modulus.toNat) :
        HilbertOperator (Recycling.Carrier.full modulus.toNat)) Reference) _
    (readout_record_matrix base noQuantum m ell width modulus environment.quantum outcome Reference)
    (feedbackAction_reference base noQuantum m ell width modulus inverse outputs position
      position.val le_rfl environment.quantum
      (stageArithmeticRecord base noQuantum m ell width modulus wide unit position store
        measured).1 Reference)
    (by simpa only [sourceWithReference_kronecker] using arithmeticAction)
    (hadamard_reference_intertwines base noQuantum m ell width modulus
      environment.quantum Reference)
  refine composed.trans ?_
  congr 1
  congr 1
  rw [readoutSource_reference, sourceWithReference_mul, sourceWithReference_mul,
    sourceWithReference_mul]
  rfl

/-- The original zero-control accumulator is restored and receives the exact logical half-sum. -/
lemma stageActualKraus_zero_matrix (wide : 2 ≤ width) (positive : 0 < modulus.toNat)
    (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits) (environment : model.Environment)
    (store : Store (Context base noQuantum m ell width))
    (measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position)
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) (Reference : Register) :
    stageActualKraus base noQuantum m ell width modulus wide inverse outputs unit position
        environment store measured outcome Reference *
      BasisEmbedding.matrix (zeroJointEmbedding base noQuantum m ell width modulus Reference) =
    arithmeticAlpha width modulus (unit ^ (2 ^ position.rev.val)) •
      (BasisEmbedding.matrix (zeroJointEmbedding base noQuantum m ell width modulus Reference) *
        sourceWithReference (Recycling.ControlKraus.halfSum
          (unitTranslation modulus (unit ^ (2 ^ position.rev.val)) :
            HilbertOperator (Recycling.Carrier.units modulus.toNat))
          (feedbackScalar base noQuantum m ell width inverse outputs position position.val le_rfl
            (stageArithmeticRecord base noQuantum m ell width modulus wide unit position store
              measured).1)
          (placedOutcome (Physical.layout width).control (Physical.qubits width)
            (Context base noQuantum m ell width) (context_wires base noQuantum m ell width)
            outcome)) Reference) := by
  rw [zeroJointEmbedding_matrix, ← Matrix.mul_assoc, stageActualKraus_full_matrix base noQuantum
    m ell width modulus wide positive, Matrix.smul_mul, Matrix.mul_assoc]
  have logical := Recycling.NativeBranch.reference_intertwines _ _ _
    (Recycling.ControlKraus.branch_intertwines
      (unitTranslation modulus (unit ^ (2 ^ position.rev.val)) :
        HilbertOperator (Recycling.Carrier.units modulus.toNat))
      (feedbackScalar base noQuantum m ell width inverse outputs position position.val le_rfl
        (stageArithmeticRecord base noQuantum m ell width modulus wide unit position store
          measured).1)
      (placedOutcome (Physical.layout width).control (Physical.qubits width)
        (Context base noQuantum m ell width) (context_wires base noQuantum m ell width) outcome))
    Reference
  simp only [sourceWithReference_kronecker]
  rw [logical]
  simp only [Matrix.mul_assoc]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
