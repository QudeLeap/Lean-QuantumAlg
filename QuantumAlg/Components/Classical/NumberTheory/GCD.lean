/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.NumberTheory.GCD.Encoding
public import QuantumAlg.Components.Classical.NumberTheory.GCD.Step
public import QuantumAlg.Components.Classical.NumberTheory.GCD.RemainderSemantics
public import QuantumAlg.Components.Classical.NumberTheory.GCD.StateLayout
public import QuantumAlg.Components.Classical.NumberTheory.GCD.Construction
public import QuantumAlg.Components.Classical.NumberTheory.GCD.LayoutSemantics
public import QuantumAlg.Components.Classical.NumberTheory.GCD.ScopedRemainder
public import QuantumAlg.Components.Classical.NumberTheory.GCD.GuardedRemainder
public import QuantumAlg.Components.Classical.NumberTheory.GCD.InitializationSemantics
public import QuantumAlg.Components.Classical.NumberTheory.GCD.LoopSemantics
public import QuantumAlg.Components.Classical.NumberTheory.GCD.ScheduledSemantics
public import QuantumAlg.Components.Classical.NumberTheory.GCD.LexicalSemantics
public import QuantumAlg.Components.Classical.NumberTheory.GCD.RetainedSemantics
public import QuantumAlg.Components.Classical.NumberTheory.GCD.Preservation
public import QuantumAlg.Components.Classical.NumberTheory.GCD.Resources
public import QuantumAlg.Components.Classical.NumberTheory.GCD.EventCounts
public import QuantumAlg.Components.Classical.NumberTheory.GCD.Depth
public import QuantumAlg.Components.Classical.NumberTheory.GCD.Space

/-!
# Total native fixed-width greatest common divisor

The individual owners provide intrinsic operands, the actual Euclidean
instruction schedule, complete state and borrowed-reference semantics,
independent native resources and all live storage, including the retained result.
-/
