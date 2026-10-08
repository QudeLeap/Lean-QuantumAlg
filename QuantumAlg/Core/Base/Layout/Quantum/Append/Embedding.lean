/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum.Append
public import QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum

/-!
# Physical embeddings of disjoint layout segments

Appending layouts preserves each original wire's identity and dimension.
The two segment embeddings select disjoint actual positions, including when
one segment is empty or the systems have different dimensions.
-/

namespace QuantumAlg.QuantumLayout

variable {leftCount rightCount : Nat}

/-- The left segment retains its original wires in the appended layout. -/
public def appendLeftEmbedding (left : QuantumLayout leftCount)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities) :
    Embedding left (append left right disjoint) where
  position := ⟨Fin.castAdd rightCount, Fin.castAdd_injective leftCount rightCount⟩
  wire_eq := by intro index; simp [append]

/-- The right segment retains its original wires after the left segment. -/
public def appendRightEmbedding (left : QuantumLayout leftCount)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities) :
    Embedding right (append left right disjoint) where
  position := ⟨Fin.natAdd leftCount, Fin.natAdd_injective rightCount leftCount⟩
  wire_eq := by intro index; simp [append]

/-- Appended segments occupy disjoint positions in the joint physical layout. -/
public theorem appendEmbedding_selections_disjoint (left : QuantumLayout leftCount)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities) :
    Disjoint (appendLeftEmbedding left right disjoint).selection
      (appendRightEmbedding left right disjoint).selection := by
  apply Finset.disjoint_left.mpr
  intro index inLeft inRight
  obtain ⟨leftIndex, _, leftEq⟩ := Finset.mem_map.mp inLeft
  obtain ⟨rightIndex, _, rightEq⟩ := Finset.mem_map.mp inRight
  have same := congrArg Fin.val (leftEq.trans rightEq.symm)
  change leftIndex.val = leftCount + rightIndex.val at same
  omega

end QuantumAlg.QuantumLayout
