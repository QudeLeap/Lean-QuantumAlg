/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Extraction
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Circuit
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Carrier
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Placement
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit
import all QuantumAlg.Components.Encoded.StateEmbedding
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The old actual placed member retains the same complete conditional columns

The operator here is the preexisting
RuntimePlacement.memberProgram on its actual runtime wires. Its original
matrix-entry theorem supplies the execution connection to compiledCircuit.
Both the initial partner seed and output-bank embedding are transported by
the same existing basis equivalence. No replacement circuit, extra resource
projection, caller quantum-state assumption or physical conversion is added.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordRuntime

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
  (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]
  (nontrivial : 1 < modulus.val) (fits : modulus.val < 2 ^ width)

/-- Actual measured old banks and arithmetic words, expressed in runtime physical coordinates. -/
def outputEmbedding (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    (Carrier.units modulus.val).Index ↪ ctx.register.Index :=
  (FullWordExtraction.outputEmbedding m ell width modulus nontrivial fits first second).trans
    (RuntimePlacement.basisEquiv m ell width sameWires).symm.toEmbedding

/-- Literal runtime matrix columns conditioned on the same two real exponent frequencies. -/
def conditionalColumns (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    Matrix ctx.register.Index (Carrier.units modulus.val).Index ℂ :=
  fun output seed =>
    if FullWordExtraction.frequency m ell width
        (RuntimePlacement.basisEquiv m ell width sameWires output) = (first, second) then
      ((RuntimePlacement.memberProgram m ell width sameWires modulus.val generator target).matrix
        environment)
        output ((RuntimePlacement.basisEquiv m ell width sameWires).symm
          (cleanLabel m ell width modulus.val 0 0 seed))
    else 0

/-- Every actual placed member entry agrees with the compiled source at the same physical basis. -/
lemma conditionalColumns_source (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    conditionalColumns (environment := environment) m ell width sameWires modulus generator target
      first second =
      Matrix.submatrix
        (FullWordExtraction.conditionalColumns (environment := environment) m ell width modulus
          generator target first second)
        (RuntimePlacement.basisEquiv m ell width sameWires) id := by
  ext output seed
  unfold conditionalColumns FullWordExtraction.conditionalColumns
  rw [RuntimePlacement.shortDLP_runtimeMember_matrix_entry]
  simp only [Equiv.apply_symm_apply]
  rfl

/-- Full runtime-bank conditional columns retain exactly the old source's same partner Kraus. -/
lemma conditionalColumns_factor (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    conditionalColumns (environment := environment) m ell width sameWires modulus generator target
      first second =
      BasisEmbedding.matrix
        (outputEmbedding m ell width sameWires modulus nontrivial fits first second) *
          FullWordCircuit.actualKraus (environment := environment) m ell width modulus generator
            target first second := by
  rw [conditionalColumns_source,
    FullWordExtraction.conditionalColumns_factor m ell width modulus nontrivial fits]
  ext output seed
  simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_apply, BasisEmbedding.matrix,
    outputEmbedding, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.symm_apply_eq]

/-- The actual old runtime bank's entire mixed/reference branch before its reset. -/
def conditionalState (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) (Reference : Register)
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    HilbertOperator (ctx.register.prod Reference) :=
  let kraus : Matrix (ctx.register.prod Reference).Index
      ((Carrier.units modulus.val).prod Reference).Index ℂ :=
    conditionalColumns (environment := environment) m ell width sameWires modulus generator target
      first second ⊗ₖ
      (1 : HilbertOperator Reference)
  kraus * density * kraus.conjTranspose

/-- Placement preserves every unnormalized partner/reference matrix entry and branch mass. -/
lemma conditionalState_factor (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) (Reference : Register)
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    conditionalState (environment := environment) m ell width sameWires modulus generator target
      first second Reference
        density =
      let embedding := BasisEmbedding.withReference
        (outputEmbedding m ell width sameWires modulus nontrivial fits first second) Reference
      BasisEmbedding.matrix embedding *
        FullWordCircuit.actualSigma (environment := environment) m ell width modulus generator
          target first second Reference
          density * (BasisEmbedding.matrix embedding).conjTranspose := by
  let embedding : Matrix ctx.register.Index (Carrier.units modulus.val).Index ℂ :=
    BasisEmbedding.matrix
      (outputEmbedding m ell width sameWires modulus nontrivial fits first second)
  let action : HilbertOperator (Carrier.units modulus.val) :=
    FullWordCircuit.actualKraus (environment := environment) m ell width modulus generator target
      first second
  let framedEmbedding : Matrix (ctx.register.prod Reference).Index
      ((Carrier.units modulus.val).prod Reference).Index ℂ :=
    BasisEmbedding.matrix (BasisEmbedding.withReference
      (outputEmbedding m ell width sameWires modulus nontrivial fits first second) Reference)
  let framedAction : HilbertOperator ((Carrier.units modulus.val).prod Reference) :=
    action ⊗ₖ (1 : HilbertOperator Reference)
  let framedColumns : Matrix (ctx.register.prod Reference).Index
      ((Carrier.units modulus.val).prod Reference).Index ℂ :=
    conditionalColumns (environment := environment) m ell width sameWires modulus generator target
      first second ⊗ₖ
      (1 : HilbertOperator Reference)
  have factor : conditionalColumns (environment := environment) m ell width sameWires modulus
    generator target first second =
      embedding * action :=
    conditionalColumns_factor m ell width sameWires modulus nontrivial fits
      generator target first second
  have reference : framedEmbedding = embedding ⊗ₖ (1 : HilbertOperator Reference) :=
    BasisEmbedding.reference_matrix
      (outputEmbedding m ell width sameWires modulus nontrivial fits first second) Reference
  have lifted : framedColumns = (embedding * action) ⊗ₖ (1 : HilbertOperator Reference) :=
    congrArg
      (fun operator : Matrix ctx.register.Index (Carrier.units modulus.val).Index ℂ =>
        operator ⊗ₖ (1 : HilbertOperator Reference)) factor
  have product : (embedding * action) ⊗ₖ (1 : HilbertOperator Reference) =
      (embedding ⊗ₖ (1 : HilbertOperator Reference)) *
        (action ⊗ₖ (1 : HilbertOperator Reference)) := by
    simpa only [Matrix.one_mul] using
      Matrix.mul_kronecker_mul embedding action
        (1 : HilbertOperator Reference) (1 : HilbertOperator Reference)
  have tensor : framedColumns = framedEmbedding * framedAction :=
    lifted.trans (product.trans (congrArg
      (fun operator : Matrix (ctx.register.prod Reference).Index
          ((Carrier.units modulus.val).prod Reference).Index ℂ => operator * framedAction)
      reference.symm))
  change framedColumns * density * framedColumns.conjTranspose =
    framedEmbedding * (framedAction * density * framedAction.conjTranspose) *
      framedEmbedding.conjTranspose
  rw [tensor]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordRuntime
