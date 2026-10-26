/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init

/-!
# Static member counts for chronological RSA batches

A configuration is a public construction parameter. It selects the real
terminal allocation, member loop and complete unordered-pair recovery scan.
It adds no runtime register or classical instruction.
-/

namespace QuantumAlg.Factoring.RSA

/-- A batch has two required members followed by this many additional members. -/
public class Configuration where
  /-- Members following the two mandatory samples in the actual batch. -/
  additionalMembers : Nat
  originalMembers : 14 ≤ additionalMembers

/-- The generic RSA construction retains its original sixteen-member batch. -/
public instance defaultConfiguration : Configuration := ⟨14, by decide⟩

/-- Number of actual chronological members selected by the public configuration. -/
@[expose] public def membersPerBatch [configuration : Configuration] : Nat :=
  configuration.additionalMembers + 2

/-- The RSA-2048 construction executes twenty members in every batch. -/
@[expose, instance_reducible] public def Configuration.rsa2048 : Configuration := ⟨18, by decide⟩

/-- The RSA-2048 construction performs four complete batches. -/
@[expose] public def Configuration.rsa2048Batches : Nat := 4

end QuantumAlg.Factoring.RSA
