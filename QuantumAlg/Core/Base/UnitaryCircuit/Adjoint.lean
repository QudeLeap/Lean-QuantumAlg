/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization.Placement
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Adjoint
import all QuantumAlg.Core.Base.Gate.Placement
import all QuantumAlg.Core.Base.Oracle.Placement

/-!
# Constructing adjoints from explicitly available native implementations

Each source gate and granted query is replaced by an actual target-language
inverse word. Sequencing is reversed, disjoint parallel branches remain
parallel, and all macro bodies are expanded through the same transformation.
The resulting circuit determines its own events, storage and depth.

An oracle adjoint requires a supplied realization using the target declaration's
actual queries. No inverse access is inferred from a source query's operator.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

/-- Actual inverse implementations for source gates and queries in a specified target language. -/
public structure AdjointRealizations (sourceGates : GateModel) (sourceOracles : OracleModel)
    (targetGates : GateModel) (targetOracles : OracleModel) where
  /-- A native inverse may expand into several target instructions. -/
  native : {count : Nat} → {layout : QuantumLayout count} →
    (application : GateModel.Application sourceGates layout) →
      ExactRealization targetGates targetOracles layout (star application.operator)
  /-- Any inverse query access must be implemented by actual granted target instructions. -/
  query : {count : Nat} → {layout : QuantumLayout count} →
    (application : OracleModel.Application sourceOracles layout) →
      ExactRealization targetGates targetOracles layout (star application.operator)

variable {sourceGates targetGates : GateModel} {sourceOracles targetOracles : OracleModel}

private def inverseLeaf
    (implementations : AdjointRealizations sourceGates sourceOracles targetGates targetOracles)
    {count : Nat} {layout : QuantumLayout count}
    (leaf : UnitaryLeaf sourceGates sourceOracles layout) :
    ExactRealization targetGates targetOracles layout (star leaf.operator) :=
  match leaf with
  | .gate application => implementations.native application
  | .oracle application => implementations.query application

private def reverseWords {count : Nat} {layout : QuantumLayout count}
    (words : List (UnitaryCircuit targetGates targetOracles layout)) :
    UnitaryCircuit targetGates targetOracles layout :=
  words.foldr (fun next accumulated => accumulated.seq next)
    (identity targetGates targetOracles layout)

private theorem reverseWords_matrix {count : Nat} {layout : QuantumLayout count}
    (words : List (UnitaryCircuit targetGates targetOracles layout)) :
    (reverseWords words).matrix = (words.map matrix).prod := by
  induction words with
  | nil => rfl
  | cons next rest ih =>
      change (reverseWords rest |>.seq next).matrix = _
      rw [seq_matrix, ih, List.map_cons, List.prod_cons]

private theorem star_foldl_reverseMul {R : Register} (operators : List (UnitaryOperator R))
    (start : UnitaryOperator R) :
    star (operators.foldl (fun accumulated next => next * accumulated) start) =
      star start * (operators.map star).prod := by
  induction operators generalizing start with
  | nil => simp
  | cons next rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.prod_cons]
      rw [ih, star_mul, mul_assoc]

private def inverseSequence
    (implementations : AdjointRealizations sourceGates sourceOracles targetGates targetOracles) :
    {count : Nat} → {layout : QuantumLayout count} →
      (sequence : UnitarySequence sourceGates sourceOracles layout) →
        ExactRealization targetGates targetOracles layout (star sequence.toUnitary)
  | _, layout, .id _ =>
      { circuit := identity targetGates targetOracles layout
        matrix_eq := by simp [UnitarySequence.toUnitary] }
  | _, _, .leaf leaf => inverseLeaf implementations leaf
  | _, _, .seq left right =>
      { circuit := (inverseSequence implementations right).circuit.seq
          (inverseSequence implementations left).circuit
        matrix_eq := by
          rw [seq_matrix, (inverseSequence implementations left).matrix_eq,
            (inverseSequence implementations right).matrix_eq]
          exact (star_mul _ _).symm }
  | _, _, .embed placement body =>
      { circuit := (inverseSequence implementations body).circuit.embed placement
        matrix_eq := by
          rw [embed_matrix, (inverseSequence implementations body).matrix_eq]
          exact QuantumLayout.Embedding.embedding_liftOperator_star placement body.toUnitary }
  | _, _, .parallel left right leftPlacement rightPlacement disjoint =>
      { circuit := parallel (inverseSequence implementations right).circuit
          (inverseSequence implementations left).circuit rightPlacement leftPlacement
          disjoint.symm
        matrix_eq := by
          change leftPlacement.liftOperator (inverseSequence implementations left).circuit.matrix *
            rightPlacement.liftOperator (inverseSequence implementations right).circuit.matrix = _
          rw [(inverseSequence implementations left).matrix_eq,
            (inverseSequence implementations right).matrix_eq,
            QuantumLayout.Embedding.embedding_liftOperator_star,
            QuantumLayout.Embedding.embedding_liftOperator_star]
          exact (star_mul _ _).symm }
  | _, _, .iterate repetitions body =>
      { circuit := iterate repetitions (inverseSequence implementations body).circuit
        matrix_eq := by
          rw [iterate_matrix, (inverseSequence implementations body).matrix_eq]
          exact (star_pow _ _).symm }
  | _, _, .indexedProduct _label _steps start step =>
      { circuit := (reverseWords (List.ofFn fun index =>
          (inverseSequence implementations (step index)).circuit)).seq
            (inverseSequence implementations start).circuit
        matrix_eq := by
          rw [seq_matrix, reverseWords_matrix,
            (inverseSequence implementations start).matrix_eq]
          change star start.toUnitary * _ =
            star ((List.ofFn fun index => (step index).toUnitary).foldl
              (fun accumulated next => next * accumulated) start.toUnitary)
          rw [star_foldl_reverseMul]
          congr 1
          simp only [List.map_ofFn]
          apply congrArg List.prod
          apply congrArg List.ofFn
          funext index
          exact (inverseSequence implementations (step index)).matrix_eq }
  | _, _, .macroCall name body =>
      { circuit := macroCall name (inverseSequence implementations body).circuit
        matrix_eq := by
          rw [macroCall_matrix]
          exact (inverseSequence implementations body).matrix_eq }

/-- Reverse the actual construction using explicitly supplied inverse gate and query words. -/
public def dagger {count : Nat} {layout : QuantumLayout count}
    (circuit : UnitaryCircuit sourceGates sourceOracles layout)
    (implementations : AdjointRealizations sourceGates sourceOracles targetGates targetOracles) :
    UnitaryCircuit targetGates targetOracles layout :=
  (inverseSequence implementations circuit.sequence).circuit

/-- The generated native circuit has the exact adjoint matrix, including global phase. -/
public theorem dagger_matrix {count : Nat} {layout : QuantumLayout count}
    (circuit : UnitaryCircuit sourceGates sourceOracles layout)
    (implementations : AdjointRealizations sourceGates sourceOracles targetGates targetOracles) :
    (circuit.dagger implementations).matrix = star circuit.matrix :=
  (inverseSequence implementations circuit.sequence).matrix_eq

end

end QuantumAlg.UnitaryCircuit
