/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Circuit
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Stages
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Clean.Subspace
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Carrier
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Primitives.ShortDLP.Layout
import all QuantumAlg.Primitives.ShortDLP.Oracle.Mathematics
import all QuantumAlg.Components.Encoded.StateEmbedding
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Complete physical old-bank branch around the same retained partner

The conditional columns are obtained by
selecting actual output exponent labels of the existing compiledCircuit.
All physical workspace rows are considered, including rows outside the clean
unit image. Their vanishing is derived from the old actual circuit, not assumed.
The resulting factorization retains the old measured exponent banks around the
complete partner/reference posterior. It is a mathematical basis comparison,
not a physical extraction, free packing instruction or executed measurement.
Actual runtime placement and measurement execution still require their bridges.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordExtraction

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open QuantumFourierTransform.Semiclassical
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (m ell width : Nat) (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]
  (nontrivial : 1 < modulus.val) (fits : modulus.val < 2 ^ width)

private abbrev Physical := Qubits (totalQubits (registerParameters m ell width))

/-- Both measured exponent frequencies remain actual physical output coordinates. -/
def frequency (output : (Physical m ell width).Index) :
    Fin (2 ^ (ell + m)) × Fin (2 ^ ell) :=
  ((tripleEquiv (registerParameters m ell width)).symm output).1

def workspace (output : (Physical m ell width).Index) : Fin (2 ^ workspaceBits width) :=
  ((tripleEquiv (registerParameters m ell width)).symm output).2

/-- The real old exponent banks stay at their measured frequencies; both arithmetic words stay. -/
def outputEmbedding (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    (Carrier.units modulus.val).Index ↪ (Physical m ell width).Index where
  toFun value := cleanLabel m ell width modulus.val first second value
  inj' := by
    intro left right same
    have words : (((first, second), cleanWorkspace width modulus.val left) :
        GroupRegisters m ell width) =
        ((first, second), cleanWorkspace width modulus.val right) :=
      (groupEncoding m ell width).encode_injective same
    apply cleanUnitLabel_injective width modulus.val nontrivial fits
    exact congrArg
      (fun label : GroupRegisters m ell width => (workspaceEncoding width).encode label.2) words

lemma frequency_outputEmbedding (first : Fin (2 ^ (ell + m)))
    (second : Fin (2 ^ ell)) (value : (ZMod modulus.val)ˣ) :
    frequency m ell width (outputEmbedding m ell width modulus nontrivial fits first second value) =
      (first, second) := by
  change ((tripleEquiv (registerParameters m ell width)).symm
    ((tripleEquiv (registerParameters m ell width))
      ((first, second), cleanUnitLabel width modulus.val value))).1 = _
  rw [Equiv.symm_apply_apply]

lemma workspace_outputEmbedding (first : Fin (2 ^ (ell + m)))
    (second : Fin (2 ^ ell)) (value : (ZMod modulus.val)ˣ) :
    workspace m ell width (outputEmbedding m ell width modulus nontrivial fits first second value) =
      cleanUnitLabel width modulus.val value := by
  change ((tripleEquiv (registerParameters m ell width)).symm
    ((tripleEquiv (registerParameters m ell width))
      ((first, second), cleanUnitLabel width modulus.val value))).2 = _
  rw [Equiv.symm_apply_apply]

include nontrivial fits in
omit [NeZero modulus.val] in
/-- All non-clean physical workspace rows vanish for every unit-partner input column. -/
lemma compiled_outside_clean (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell))
    (output : Fin (2 ^ workspaceBits width)) (seed : (ZMod modulus.val)ˣ)
    (outside : output ∉ Set.range (cleanUnitLabel width modulus.val)) :
    ((compiledCircuit m ell width modulus.val generator target).binaryMatrix environment)
        (tripleIndex (registerParameters m ell width) first second output)
        (cleanLabel m ell width modulus.val 0 0 seed) = 0 := by
  rw [FullWordCircuit.compiled_column m ell width modulus.val nontrivial fits]
  apply Finset.sum_eq_zero
  intro sourceFirst _
  apply Finset.sum_eq_zero
  intro sourceSecond _
  rw [cleanLabel_eq_tripleIndex, FullWordStages.readout_entry]
  have different : output ≠ cleanUnitLabel width modulus.val
      (oracleValue generator target sourceFirst.val sourceSecond.val * seed) :=
    fun same => outside ⟨_, same.symm⟩
  simp only [different, if_false, mul_zero]

/-- The actual compiled columns conditioned on both physical exponent outcomes. -/
def conditionalColumns (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    Matrix (Physical m ell width).Index (Carrier.units modulus.val).Index ℂ :=
  fun output seed => if frequency m ell width output = (first, second) then
    ((compiledCircuit m ell width modulus.val generator target).binaryMatrix environment) output
      (cleanLabel m ell width modulus.val 0 0 seed) else 0

/-- Every physical branch row is retained by the frequency/clean-unit embedding. -/
lemma conditionalColumns_factor (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    conditionalColumns (environment := environment) m ell width modulus generator target first
      second =
      BasisEmbedding.matrix
        (outputEmbedding m ell width modulus nontrivial fits first second) *
          FullWordCircuit.actualKraus (environment := environment) m ell width modulus generator
            target first second := by
  ext output seed
  unfold conditionalColumns
  by_cases selected : frequency m ell width output = (first, second)
  · rw [if_pos selected]
    by_cases clean : workspace m ell width output ∈ Set.range (cleanUnitLabel width modulus.val)
    · obtain ⟨value, encoded⟩ := clean
      have same : output =
          outputEmbedding m ell width modulus nontrivial fits first second value := by
        apply (tripleEquiv (registerParameters m ell width)).symm.injective
        apply Prod.ext
        · exact selected.trans
            (frequency_outputEmbedding m ell width modulus nontrivial fits first second value).symm
        · exact encoded.symm.trans
            (workspace_outputEmbedding m ell width modulus nontrivial fits first second value).symm
      subst output
      simp only [Matrix.mul_apply, BasisEmbedding.matrix,
        (outputEmbedding m ell width modulus nontrivial fits first second).injective.eq_iff,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rfl
    · have decomposition : output = tripleIndex (registerParameters m ell width)
          first second (workspace m ell width output) := by
        have tuple : (tripleEquiv (registerParameters m ell width)).symm output =
            ((first, second), workspace m ell width output) := Prod.ext selected rfl
        exact ((tripleEquiv (registerParameters m ell width)).apply_symm_apply output).symm.trans
          (congrArg (tripleEquiv (registerParameters m ell width)) tuple)
      have zero := compiled_outside_clean (environment := environment) m ell width modulus
        nontrivial fits generator target
        first second (workspace m ell width output) seed clean
      have nativeZero : ((compiledCircuit m ell width modulus.val generator target).binaryMatrix
        environment)
          output (cleanLabel m ell width modulus.val 0 0 seed) = 0 := by
        simpa only [← decomposition] using zero
      rw [nativeZero]
      have different (value : (ZMod modulus.val)ˣ) :
          outputEmbedding m ell width modulus nontrivial fits first second value ≠ output := by
        intro same
        apply clean
        refine ⟨value, ?_⟩
        have canonical :=
          workspace_outputEmbedding m ell width modulus nontrivial fits first second value
        exact canonical.symm.trans (congrArg (workspace m ell width) same)
      simp only [Matrix.mul_apply, BasisEmbedding.matrix, different, if_false, zero_mul,
        Finset.sum_const_zero]
  · rw [if_neg selected]
    have different (value : (ZMod modulus.val)ˣ) :
        outputEmbedding m ell width modulus nontrivial fits first second value ≠ output := by
      intro same
      apply selected
      exact (congrArg (frequency m ell width) same).symm.trans
        (frequency_outputEmbedding m ell width modulus nontrivial fits first second value)
    simp only [Matrix.mul_apply, BasisEmbedding.matrix, different, if_false, zero_mul,
      Finset.sum_const_zero]

/-- Mixed/reference branch on the actual old physical bank, without a purity premise. -/
def conditionalState (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) (Reference : Register)
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    HilbertOperator ((Physical m ell width).prod Reference) :=
  let kraus : Matrix ((Physical m ell width).prod Reference).Index
      ((Carrier.units modulus.val).prod Reference).Index ℂ :=
    conditionalColumns (environment := environment) m ell width modulus generator target first
      second ⊗ₖ
      (1 : HilbertOperator Reference)
  kraus * density * kraus.conjTranspose

/-- The old bank is separately embedded around the entire common-reference sigma_y. -/
lemma conditionalState_factor (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) (Reference : Register)
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    conditionalState (environment := environment) m ell width modulus generator target first second
      Reference density =
      let embedding := BasisEmbedding.withReference
        (outputEmbedding m ell width modulus nontrivial fits first second) Reference
      BasisEmbedding.matrix embedding *
        FullWordCircuit.actualSigma (environment := environment) m ell width modulus generator
          target first second Reference
          density * (BasisEmbedding.matrix embedding).conjTranspose := by
  let embedding : Matrix (Physical m ell width).Index (Carrier.units modulus.val).Index ℂ :=
    BasisEmbedding.matrix
      (outputEmbedding m ell width modulus nontrivial fits first second)
  let action : HilbertOperator (Carrier.units modulus.val) :=
    FullWordCircuit.actualKraus (environment := environment) m ell width modulus generator target
      first second
  let framedEmbedding : Matrix ((Physical m ell width).prod Reference).Index
      ((Carrier.units modulus.val).prod Reference).Index ℂ :=
    BasisEmbedding.matrix (BasisEmbedding.withReference
      (outputEmbedding m ell width modulus nontrivial fits first second) Reference)
  let framedAction : HilbertOperator ((Carrier.units modulus.val).prod Reference) :=
    action ⊗ₖ (1 : HilbertOperator Reference)
  let framedColumns : Matrix ((Physical m ell width).prod Reference).Index
      ((Carrier.units modulus.val).prod Reference).Index ℂ :=
    conditionalColumns (environment := environment) m ell width modulus generator target first
      second ⊗ₖ
      (1 : HilbertOperator Reference)
  have factor : conditionalColumns (environment := environment) m ell width modulus generator
    target first second =
      embedding * action :=
    conditionalColumns_factor m ell width modulus nontrivial fits generator target first second
  have reference : framedEmbedding = embedding ⊗ₖ (1 : HilbertOperator Reference) :=
    BasisEmbedding.reference_matrix
      (outputEmbedding m ell width modulus nontrivial fits first second) Reference
  have lifted : framedColumns = (embedding * action) ⊗ₖ (1 : HilbertOperator Reference) :=
    congrArg
      (fun operator : Matrix (Physical m ell width).Index (Carrier.units modulus.val).Index ℂ =>
        operator ⊗ₖ (1 : HilbertOperator Reference)) factor
  have product : (embedding * action) ⊗ₖ (1 : HilbertOperator Reference) =
      (embedding ⊗ₖ (1 : HilbertOperator Reference)) *
        (action ⊗ₖ (1 : HilbertOperator Reference)) := by
    simpa only [Matrix.one_mul] using
      Matrix.mul_kronecker_mul embedding action
        (1 : HilbertOperator Reference) (1 : HilbertOperator Reference)
  have tensor : framedColumns = framedEmbedding * framedAction :=
    lifted.trans (product.trans (congrArg
      (fun operator : Matrix ((Physical m ell width).prod Reference).Index
          ((Carrier.units modulus.val).prod Reference).Index ℂ => operator * framedAction)
      reference.symm))
  change framedColumns * density * framedColumns.conjTranspose =
    framedEmbedding * (framedAction * density * framedAction.conjTranspose) *
      framedEmbedding.conjTranspose
  rw [tensor]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordExtraction
