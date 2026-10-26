/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word38Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word38State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word38Step0 :
    word38Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word38State1 := by decide +kernel

private def word38Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word38State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word38Step1 :
    word38Chunk1.foldl (fun acc a => a.applyPacked acc)
      word38State1 = word38State2 := by decide +kernel

private def word38Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word38State3 : PackedMat2 :=
    ⟨⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word38Step2 :
    word38Chunk2.foldl (fun acc a => a.applyPacked acc)
      word38State2 = word38State3 := by decide +kernel

private def word38Chunk3 : List Letter := [.s, .h, .s, .t, .h, .s, .t, .h]
private def word38State4 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word38Step3 :
    word38Chunk3.foldl (fun acc a => a.applyPacked acc)
      word38State3 = word38State4 := by decide +kernel

private def word38Chunk4 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word38State5 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-5 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((5 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word38Step4 :
    word38Chunk4.foldl (fun acc a => a.applyPacked acc)
      word38State4 = word38State5 := by decide +kernel

private def word38Chunk5 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word38State6 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((-7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word38Step5 :
    word38Chunk5.foldl (fun acc a => a.applyPacked acc)
      word38State5 = word38State6 := by decide +kernel

private def word38Chunk6 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word38State7 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((7 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-11 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((15 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((9 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word38Step6 :
    word38Chunk6.foldl (fun acc a => a.applyPacked acc)
      word38State6 = word38State7 := by decide +kernel

private def word38Chunk7 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word38State8 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 3),
        ((-7 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((5 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 5),
        ((9 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word38Step7 :
    word38Chunk7.foldl (fun acc a => a.applyPacked acc)
      word38State7 = word38State8 := by decide +kernel

private def word38Chunk8 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word38State9 : PackedMat2 :=
    ⟨⟨⟨((-13 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-27 : Dyadic) * half ^ 6),
        ((9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((17 : Dyadic) * half ^ 6),
        ((-11 : Dyadic) * half ^ 6)⟩,
       ⟨((23 : Dyadic) * half ^ 6),
        ((27 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((-19 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((11 : Dyadic) * half ^ 5),
        ((-7 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word38Step8 :
    word38Chunk8.foldl (fun acc a => a.applyPacked acc)
      word38State8 = word38State9 := by decide +kernel

private def word38Chunk9 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word38State10 : PackedMat2 :=
    ⟨⟨⟨((35 : Dyadic) * half ^ 7),
        ((-9 : Dyadic) * half ^ 6)⟩,
       ⟨((5 : Dyadic) * half ^ 7),
        ((-69 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-65 : Dyadic) * half ^ 7),
        ((-15 : Dyadic) * half ^ 7)⟩,
       ⟨((-17 : Dyadic) * half ^ 7),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((65 : Dyadic) * half ^ 7),
        ((15 : Dyadic) * half ^ 7)⟩,
       ⟨((-17 : Dyadic) * half ^ 7),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((35 : Dyadic) * half ^ 7),
        ((-9 : Dyadic) * half ^ 6)⟩,
       ⟨((-5 : Dyadic) * half ^ 7),
        ((69 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word38Step9 :
    word38Chunk9.foldl (fun acc a => a.applyPacked acc)
      word38State9 = word38State10 := by decide +kernel

private def word38Chunk10 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word38State11 : PackedMat2 :=
    ⟨⟨⟨((13 : Dyadic) * half ^ 7),
        ((63 : Dyadic) * half ^ 7)⟩,
       ⟨((-9 : Dyadic) * half ^ 5),
        ((15 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((59 : Dyadic) * half ^ 7),
        ((3 : Dyadic) * half ^ 7)⟩,
       ⟨((3 : Dyadic) * half ^ 5),
        ((-19 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((41 : Dyadic) * half ^ 7),
        ((47 : Dyadic) * half ^ 8)⟩,
       ⟨((35 : Dyadic) * half ^ 7),
        ((-71 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-49 : Dyadic) * half ^ 8)⟩,
       ⟨((39 : Dyadic) * half ^ 6),
        ((-23 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word38Step10 :
    word38Chunk10.foldl (fun acc a => a.applyPacked acc)
      word38State10 = word38State11 := by decide +kernel

private def word38Chunk11 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word38State12 : PackedMat2 :=
    ⟨⟨⟨((53 : Dyadic) * half ^ 8),
        ((185 : Dyadic) * half ^ 9)⟩,
       ⟨((135 : Dyadic) * half ^ 8),
        ((-77 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 7),
        ((-187 : Dyadic) * half ^ 9)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-89 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 7),
        ((187 : Dyadic) * half ^ 9)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-89 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((53 : Dyadic) * half ^ 8),
        ((185 : Dyadic) * half ^ 9)⟩,
       ⟨((-135 : Dyadic) * half ^ 8),
        ((77 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word38Step11 :
    word38Chunk11.foldl (fun acc a => a.applyPacked acc)
      word38State11 = word38State12 := by decide +kernel

private def word38Chunk12 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word38State13 : PackedMat2 :=
    ⟨⟨⟨((99 : Dyadic) * half ^ 9),
        ((257 : Dyadic) * half ^ 10)⟩,
       ⟨((-81 : Dyadic) * half ^ 8),
        ((477 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 6),
        ((-45 : Dyadic) * half ^ 10)⟩,
       ⟨((-169 : Dyadic) * half ^ 9),
        ((-279 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((117 : Dyadic) * half ^ 9),
        ((65 : Dyadic) * half ^ 10)⟩,
       ⟨((81 : Dyadic) * half ^ 8),
        ((273 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((55 : Dyadic) * half ^ 8),
        ((-261 : Dyadic) * half ^ 10)⟩,
       ⟨((367 : Dyadic) * half ^ 9),
        ((-63 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word38Step12 :
    word38Chunk12.foldl (fun acc a => a.applyPacked acc)
      word38State12 = word38State13 := by decide +kernel

private def word38Chunk13 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word38State14 : PackedMat2 :=
    ⟨⟨⟨((35 : Dyadic) * half ^ 9),
        ((-51 : Dyadic) * half ^ 8)⟩,
       ⟨((395 : Dyadic) * half ^ 9),
        ((-5 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((125 : Dyadic) * half ^ 8),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((135 : Dyadic) * half ^ 9),
        ((-51 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((135 : Dyadic) * half ^ 9),
        ((-51 : Dyadic) * half ^ 10)⟩,
       ⟨((125 : Dyadic) * half ^ 8),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-395 : Dyadic) * half ^ 9),
        ((5 : Dyadic) * half ^ 10)⟩,
       ⟨((-35 : Dyadic) * half ^ 9),
        ((51 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word38Step13 :
    word38Chunk13.foldl (fun acc a => a.applyPacked acc)
      word38State13 = word38State14 := by decide +kernel

private def word38Chunk14 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word38State15 : PackedMat2 :=
    ⟨⟨⟨((-1185 : Dyadic) * half ^ 11),
        ((115 : Dyadic) * half ^ 9)⟩,
       ⟨((175 : Dyadic) * half ^ 11),
        ((701 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((67 : Dyadic) * half ^ 11),
        ((121 : Dyadic) * half ^ 11)⟩,
       ⟨((597 : Dyadic) * half ^ 11),
        ((347 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-815 : Dyadic) * half ^ 11),
        ((-83 : Dyadic) * half ^ 9)⟩,
       ⟨((573 : Dyadic) * half ^ 11),
        ((265 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((1161 : Dyadic) * half ^ 11),
        ((-505 : Dyadic) * half ^ 11)⟩,
       ⟨((-241 : Dyadic) * half ^ 11),
        ((-85 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word38Step14 :
    word38Chunk14.foldl (fun acc a => a.applyPacked acc)
      word38State14 = word38State15 := by decide +kernel

private def word38Chunk15 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word38State16 : PackedMat2 :=
    ⟨⟨⟨((339 : Dyadic) * half ^ 11),
        ((-2007 : Dyadic) * half ^ 12)⟩,
       ⟨((407 : Dyadic) * half ^ 11),
        ((1329 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-385 : Dyadic) * half ^ 10),
        ((-167 : Dyadic) * half ^ 12)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((17 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-385 : Dyadic) * half ^ 10),
        ((-167 : Dyadic) * half ^ 12)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((-17 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-339 : Dyadic) * half ^ 11),
        ((2007 : Dyadic) * half ^ 12)⟩,
       ⟨((407 : Dyadic) * half ^ 11),
        ((1329 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word38Step15 :
    word38Chunk15.foldl (fun acc a => a.applyPacked acc)
      word38State15 = word38State16 := by decide +kernel

private def word38Chunk16 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word38State17 : PackedMat2 :=
    ⟨⟨⟨((-527 : Dyadic) * half ^ 10),
        ((-1659 : Dyadic) * half ^ 13)⟩,
       ⟨((-1011 : Dyadic) * half ^ 11),
        ((2021 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((465 : Dyadic) * half ^ 12),
        ((-2125 : Dyadic) * half ^ 13)⟩,
       ⟨((1245 : Dyadic) * half ^ 12),
        ((1267 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-465 : Dyadic) * half ^ 12),
        ((2125 : Dyadic) * half ^ 13)⟩,
       ⟨((1245 : Dyadic) * half ^ 12),
        ((1267 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-527 : Dyadic) * half ^ 10),
        ((-1659 : Dyadic) * half ^ 13)⟩,
       ⟨((1011 : Dyadic) * half ^ 11),
        ((-2021 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word38Step16 :
    word38Chunk16.foldl (fun acc a => a.applyPacked acc)
      word38State16 = word38State17 := by decide +kernel

private def word38Chunk17 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word38State18 : PackedMat2 :=
    ⟨⟨⟨((-33 : Dyadic) * half ^ 12),
        ((-4527 : Dyadic) * half ^ 14)⟩,
       ⟨((-1783 : Dyadic) * half ^ 13),
        ((-6483 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-3551 : Dyadic) * half ^ 13),
        ((3793 : Dyadic) * half ^ 14)⟩,
       ⟨((893 : Dyadic) * half ^ 11),
        ((451 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1671 : Dyadic) * half ^ 13),
        ((-7123 : Dyadic) * half ^ 14)⟩,
       ⟨((-1061 : Dyadic) * half ^ 12),
        ((-21 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-489 : Dyadic) * half ^ 12),
        ((-1717 : Dyadic) * half ^ 14)⟩,
       ⟨((-5505 : Dyadic) * half ^ 13),
        ((-1849 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word38Step17 :
    word38Chunk17.foldl (fun acc a => a.applyPacked acc)
      word38State17 = word38State18 := by decide +kernel

private def word38Chunk18 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word38State19 : PackedMat2 :=
    ⟨⟨⟨((807 : Dyadic) * half ^ 14),
        ((1279 : Dyadic) * half ^ 14)⟩,
       ⟨((-2977 : Dyadic) * half ^ 14),
        ((-3821 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((155 : Dyadic) * half ^ 14),
        ((-755 : Dyadic) * half ^ 11)⟩,
       ⟨((-1317 : Dyadic) * half ^ 14),
        ((4355 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1317 : Dyadic) * half ^ 14),
        ((4355 : Dyadic) * half ^ 13)⟩,
       ⟨((155 : Dyadic) * half ^ 14),
        ((-755 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((2977 : Dyadic) * half ^ 14),
        ((3821 : Dyadic) * half ^ 14)⟩,
       ⟨((-807 : Dyadic) * half ^ 14),
        ((-1279 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word38Step18 :
    word38Chunk18.foldl (fun acc a => a.applyPacked acc)
      word38State18 = word38State19 := by decide +kernel

private def word38Chunk19 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word38State20 : PackedMat2 :=
    ⟨⟨⟨((20285 : Dyadic) * half ^ 15),
        ((973 : Dyadic) * half ^ 13)⟩,
       ⟨((-4165 : Dyadic) * half ^ 15),
        ((-2279 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-5663 : Dyadic) * half ^ 15),
        ((-6663 : Dyadic) * half ^ 15)⟩,
       ⟨((20117 : Dyadic) * half ^ 15),
        ((-49 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((5663 : Dyadic) * half ^ 15),
        ((6663 : Dyadic) * half ^ 15)⟩,
       ⟨((20117 : Dyadic) * half ^ 15),
        ((-49 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((20285 : Dyadic) * half ^ 15),
        ((973 : Dyadic) * half ^ 13)⟩,
       ⟨((4165 : Dyadic) * half ^ 15),
        ((2279 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word38Step19 :
    word38Chunk19.foldl (fun acc a => a.applyPacked acc)
      word38State19 = word38State20 := by decide +kernel

private def word38Chunk20 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word38State21 : PackedMat2 :=
    ⟨⟨⟨((36063 : Dyadic) * half ^ 16),
        ((18141 : Dyadic) * half ^ 16)⟩,
       ⟨((-5765 : Dyadic) * half ^ 16),
        ((4677 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((29225 : Dyadic) * half ^ 16),
        ((-4047 : Dyadic) * half ^ 14)⟩,
       ⟨((-12489 : Dyadic) * half ^ 16),
        ((5867 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((29225 : Dyadic) * half ^ 16),
        ((-4047 : Dyadic) * half ^ 14)⟩,
       ⟨((12489 : Dyadic) * half ^ 16),
        ((-5867 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-36063 : Dyadic) * half ^ 16),
        ((-18141 : Dyadic) * half ^ 16)⟩,
       ⟨((-5765 : Dyadic) * half ^ 16),
        ((4677 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word38Step20 :
    word38Chunk20.foldl (fun acc a => a.applyPacked acc)
      word38State20 = word38State21 := by decide +kernel

private def word38Chunk21 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word38State22 : PackedMat2 :=
    ⟨⟨⟨((8909 : Dyadic) * half ^ 14),
        ((1167 : Dyadic) * half ^ 17)⟩,
       ⟨((5373 : Dyadic) * half ^ 13),
        ((6509 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-27975 : Dyadic) * half ^ 16),
        ((5217 : Dyadic) * half ^ 17)⟩,
       ⟨((17597 : Dyadic) * half ^ 16),
        ((-9969 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-7593 : Dyadic) * half ^ 16),
        ((11393 : Dyadic) * half ^ 15)⟩,
       ⟨((-297 : Dyadic) * half ^ 13),
        ((-5189 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-2671 : Dyadic) * half ^ 16),
        ((-1837 : Dyadic) * half ^ 15)⟩,
       ⟨((-1919 : Dyadic) * half ^ 15),
        ((-19655 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word38Step21 :
    word38Chunk21.foldl (fun acc a => a.applyPacked acc)
      word38State21 = word38State22 := by decide +kernel

private def word38Chunk22 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word38State23 : PackedMat2 :=
    ⟨⟨⟨((-31847 : Dyadic) * half ^ 16),
        ((-24993 : Dyadic) * half ^ 18)⟩,
       ⟨((-31485 : Dyadic) * half ^ 17),
        ((78495 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-25013 : Dyadic) * half ^ 17),
        ((-47329 : Dyadic) * half ^ 18)⟩,
       ⟨((-653 : Dyadic) * half ^ 10),
        ((3641 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-25485 : Dyadic) * half ^ 17),
        ((58571 : Dyadic) * half ^ 18)⟩,
       ⟨((5461 : Dyadic) * half ^ 15),
        ((108597 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((1617 : Dyadic) * half ^ 12),
        ((32209 : Dyadic) * half ^ 18)⟩,
       ⟨((26751 : Dyadic) * half ^ 17),
        ((-95179 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word38Step22 :
    word38Chunk22.foldl (fun acc a => a.applyPacked acc)
      word38State22 = word38State23 := by decide +kernel

private def word38Chunk23 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word38State24 : PackedMat2 :=
    ⟨⟨⟨((31505 : Dyadic) * half ^ 18),
        ((-79277 : Dyadic) * half ^ 18)⟩,
       ⟨((-68783 : Dyadic) * half ^ 18),
        ((-42161 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-27439 : Dyadic) * half ^ 18),
        ((-19665 : Dyadic) * half ^ 17)⟩,
       ⟨((10113 : Dyadic) * half ^ 18),
        ((-2289 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((10113 : Dyadic) * half ^ 18),
        ((-2289 : Dyadic) * half ^ 12)⟩,
       ⟨((-27439 : Dyadic) * half ^ 18),
        ((-19665 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((68783 : Dyadic) * half ^ 18),
        ((42161 : Dyadic) * half ^ 18)⟩,
       ⟨((-31505 : Dyadic) * half ^ 18),
        ((79277 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word38Step23 :
    word38Chunk23.foldl (fun acc a => a.applyPacked acc)
      word38State23 = word38State24 := by decide +kernel

private def word38Chunk24 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word38State25 : PackedMat2 :=
    ⟨⟨⟨((10275 : Dyadic) * half ^ 19),
        ((12543 : Dyadic) * half ^ 18)⟩,
       ⟨((-48589 : Dyadic) * half ^ 19),
        ((-95085 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((193275 : Dyadic) * half ^ 19),
        ((209211 : Dyadic) * half ^ 19)⟩,
       ⟨((-254883 : Dyadic) * half ^ 19),
        ((44445 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-386991 : Dyadic) * half ^ 19),
        ((7701 : Dyadic) * half ^ 17)⟩,
       ⟨((-31431 : Dyadic) * half ^ 19),
        ((-224079 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-69999 : Dyadic) * half ^ 19),
        ((-19157 : Dyadic) * half ^ 19)⟩,
       ⟨((120171 : Dyadic) * half ^ 19),
        ((3679 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word38Step24 :
    word38Chunk24.foldl (fun acc a => a.applyPacked acc)
      word38State24 = word38State25 := by decide +kernel

private def word38Chunk25 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word38State26 : PackedMat2 :=
    ⟨⟨⟨((23491 : Dyadic) * half ^ 16),
        ((35105 : Dyadic) * half ^ 19)⟩,
       ⟨((-63527 : Dyadic) * half ^ 19),
        ((15581 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((226287 : Dyadic) * half ^ 18),
        ((2473 : Dyadic) * half ^ 17)⟩,
       ⟨((-106605 : Dyadic) * half ^ 19),
        ((16685 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((226287 : Dyadic) * half ^ 18),
        ((2473 : Dyadic) * half ^ 17)⟩,
       ⟨((106605 : Dyadic) * half ^ 19),
        ((-16685 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-23491 : Dyadic) * half ^ 16),
        ((-35105 : Dyadic) * half ^ 19)⟩,
       ⟨((-63527 : Dyadic) * half ^ 19),
        ((15581 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word38Step25 :
    word38Chunk25.foldl (fun acc a => a.applyPacked acc)
      word38State25 = word38State26 := by decide +kernel

private def word38Chunk26 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word38State27 : PackedMat2 :=
    ⟨⟨⟨((77767 : Dyadic) * half ^ 19),
        ((941617 : Dyadic) * half ^ 21)⟩,
       ⟨((27457 : Dyadic) * half ^ 17),
        ((389305 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-47909 : Dyadic) * half ^ 20),
        ((457059 : Dyadic) * half ^ 21)⟩,
       ⟨((-256469 : Dyadic) * half ^ 20),
        ((819083 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((47909 : Dyadic) * half ^ 20),
        ((-457059 : Dyadic) * half ^ 21)⟩,
       ⟨((-256469 : Dyadic) * half ^ 20),
        ((819083 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((77767 : Dyadic) * half ^ 19),
        ((941617 : Dyadic) * half ^ 21)⟩,
       ⟨((-27457 : Dyadic) * half ^ 17),
        ((-389305 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word38Step26 :
    word38Chunk26.foldl (fun acc a => a.applyPacked acc)
      word38State26 = word38State27 := by decide +kernel

private def word38Chunk27 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word38State28 : PackedMat2 :=
    ⟨⟨⟨((902973 : Dyadic) * half ^ 21),
        ((-286797 : Dyadic) * half ^ 22)⟩,
       ⟨((591455 : Dyadic) * half ^ 20),
        ((1076551 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((247421 : Dyadic) * half ^ 19),
        ((-979023 : Dyadic) * half ^ 22)⟩,
       ⟨((105713 : Dyadic) * half ^ 21),
        ((-431069 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-273977 : Dyadic) * half ^ 21),
        ((883971 : Dyadic) * half ^ 22)⟩,
       ⟨((352523 : Dyadic) * half ^ 20),
        ((-1095397 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((340837 : Dyadic) * half ^ 20),
        ((279937 : Dyadic) * half ^ 22)⟩,
       ⟨((394877 : Dyadic) * half ^ 21),
        ((2085883 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word38Step27 :
    word38Chunk27.foldl (fun acc a => a.applyPacked acc)
      word38State27 = word38State28 := by decide +kernel

private def word38Chunk28 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word38State29 : PackedMat2 :=
    ⟨⟨⟨((-1520767 : Dyadic) * half ^ 21),
        ((-23215 : Dyadic) * half ^ 20)⟩,
       ⟨((409993 : Dyadic) * half ^ 21),
        ((-186431 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-171925 : Dyadic) * half ^ 20),
        ((160875 : Dyadic) * half ^ 19)⟩,
       ⟨((286901 : Dyadic) * half ^ 21),
        ((1316663 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((286901 : Dyadic) * half ^ 21),
        ((1316663 : Dyadic) * half ^ 22)⟩,
       ⟨((-171925 : Dyadic) * half ^ 20),
        ((160875 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-409993 : Dyadic) * half ^ 21),
        ((186431 : Dyadic) * half ^ 22)⟩,
       ⟨((1520767 : Dyadic) * half ^ 21),
        ((23215 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word38Step28 :
    word38Chunk28.foldl (fun acc a => a.applyPacked acc)
      word38State28 = word38State29 := by decide +kernel

private def word38Chunk29 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word38State30 : PackedMat2 :=
    ⟨⟨⟨((-3453111 : Dyadic) * half ^ 23),
        ((-2304203 : Dyadic) * half ^ 23)⟩,
       ⟨((-1741317 : Dyadic) * half ^ 23),
        ((742033 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1699373 : Dyadic) * half ^ 23),
        ((-11217 : Dyadic) * half ^ 19)⟩,
       ⟨((-904221 : Dyadic) * half ^ 23),
        ((3420845 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1699373 : Dyadic) * half ^ 23),
        ((11217 : Dyadic) * half ^ 19)⟩,
       ⟨((-904221 : Dyadic) * half ^ 23),
        ((3420845 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-3453111 : Dyadic) * half ^ 23),
        ((-2304203 : Dyadic) * half ^ 23)⟩,
       ⟨((1741317 : Dyadic) * half ^ 23),
        ((-742033 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word38Step29 :
    word38Chunk29.foldl (fun acc a => a.applyPacked acc)
      word38State29 = word38State30 := by decide +kernel

private def word38Chunk30 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word38State31 : PackedMat2 :=
    ⟨⟨⟨((-8229671 : Dyadic) * half ^ 24),
        ((5154265 : Dyadic) * half ^ 24)⟩,
       ⟨((4271059 : Dyadic) * half ^ 24),
        ((618941 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-7218813 : Dyadic) * half ^ 24),
        ((-1221785 : Dyadic) * half ^ 22)⟩,
       ⟨((-5425149 : Dyadic) * half ^ 24),
        ((633269 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-4253871 : Dyadic) * half ^ 24),
        ((-6321981 : Dyadic) * half ^ 24)⟩,
       ⟨((-5520409 : Dyadic) * half ^ 24),
        ((-14013 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-7630029 : Dyadic) * half ^ 24),
        ((989653 : Dyadic) * half ^ 23)⟩,
       ⟨((-2678501 : Dyadic) * half ^ 24),
        ((6250365 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word38Step30 :
    word38Chunk30.foldl (fun acc a => a.applyPacked acc)
      word38State30 = word38State31 := by decide +kernel

private def word38Chunk31 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word38State32 : PackedMat2 :=
    ⟨⟨⟨((3314071 : Dyadic) * half ^ 23),
        ((-5818295 : Dyadic) * half ^ 25)⟩,
       ⟨((-2175823 : Dyadic) * half ^ 23),
        ((10058593 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-6289401 : Dyadic) * half ^ 24),
        ((-2697817 : Dyadic) * half ^ 25)⟩,
       ⟨((-5111667 : Dyadic) * half ^ 24),
        ((-12788053 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((6289401 : Dyadic) * half ^ 24),
        ((2697817 : Dyadic) * half ^ 25)⟩,
       ⟨((-5111667 : Dyadic) * half ^ 24),
        ((-12788053 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((3314071 : Dyadic) * half ^ 23),
        ((-5818295 : Dyadic) * half ^ 25)⟩,
       ⟨((2175823 : Dyadic) * half ^ 23),
        ((-10058593 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word38Step31 :
    word38Chunk31.foldl (fun acc a => a.applyPacked acc)
      word38State31 = word38State32 := by decide +kernel

private def word38Chunk32 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word38State33 : PackedMat2 :=
    ⟨⟨⟨((7332389 : Dyadic) * half ^ 24),
        ((439441 : Dyadic) * half ^ 23)⟩,
       ⟨((871123 : Dyadic) * half ^ 24),
        ((17568633 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((1260083 : Dyadic) * half ^ 23),
        ((972757 : Dyadic) * half ^ 23)⟩,
       ⟨((4340871 : Dyadic) * half ^ 24),
        ((-8753793 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((4862765 : Dyadic) * half ^ 25),
        ((-6861037 : Dyadic) * half ^ 25)⟩,
       ⟨((-12644821 : Dyadic) * half ^ 25),
        ((1820705 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((19326397 : Dyadic) * half ^ 25),
        ((1025439 : Dyadic) * half ^ 22)⟩,
       ⟨((-15810869 : Dyadic) * half ^ 25),
        ((3230633 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word38Step32 :
    word38Chunk32.foldl (fun acc a => a.applyPacked acc)
      word38State32 = word38State33 := by decide +kernel

private def word38Chunk33 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word38State34 : PackedMat2 :=
    ⟨⟨⟨((-1799933 : Dyadic) * half ^ 22),
        ((17457085 : Dyadic) * half ^ 26)⟩,
       ⟨((-8338461 : Dyadic) * half ^ 25),
        ((1170657 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1707397 : Dyadic) * half ^ 22),
        ((27791967 : Dyadic) * half ^ 26)⟩,
       ⟨((1158643 : Dyadic) * half ^ 23),
        ((-5410519 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((1158643 : Dyadic) * half ^ 23),
        ((-5410519 : Dyadic) * half ^ 25)⟩,
       ⟨((1707397 : Dyadic) * half ^ 22),
        ((27791967 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((8338461 : Dyadic) * half ^ 25),
        ((-1170657 : Dyadic) * half ^ 23)⟩,
       ⟨((1799933 : Dyadic) * half ^ 22),
        ((-17457085 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word38Step33 :
    word38Chunk33.foldl (fun acc a => a.applyPacked acc)
      word38State33 = word38State34 := by decide +kernel

private def word38Chunk34 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word38State35 : PackedMat2 :=
    ⟨⟨⟨((62836823 : Dyadic) * half ^ 27),
        ((-21852191 : Dyadic) * half ^ 26)⟩,
       ⟨((42018687 : Dyadic) * half ^ 27),
        ((13145871 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((18702431 : Dyadic) * half ^ 27),
        ((-17311581 : Dyadic) * half ^ 27)⟩,
       ⟨((63819065 : Dyadic) * half ^ 27),
        ((9862417 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-22138087 : Dyadic) * half ^ 27),
        ((-10315187 : Dyadic) * half ^ 25)⟩,
       ⟨((56761249 : Dyadic) * half ^ 27),
        ((22558317 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-30558511 : Dyadic) * half ^ 27),
        ((52427755 : Dyadic) * half ^ 27)⟩,
       ⟨((-56850253 : Dyadic) * half ^ 27),
        ((2602267 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word38Step34 :
    word38Chunk34.foldl (fun acc a => a.applyPacked acc)
      word38State34 = word38State35 := by decide +kernel

private def word38Chunk35 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word38State36 : PackedMat2 :=
    ⟨⟨⟨((-74064941 : Dyadic) * half ^ 27),
        ((67002533 : Dyadic) * half ^ 28)⟩,
       ⟨((76473815 : Dyadic) * half ^ 27),
        ((37763973 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-8901351 : Dyadic) * half ^ 26),
        ((-64451619 : Dyadic) * half ^ 28)⟩,
       ⟨((6947885 : Dyadic) * half ^ 25),
        ((33361613 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-8901351 : Dyadic) * half ^ 26),
        ((-64451619 : Dyadic) * half ^ 28)⟩,
       ⟨((-6947885 : Dyadic) * half ^ 25),
        ((-33361613 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((74064941 : Dyadic) * half ^ 27),
        ((-67002533 : Dyadic) * half ^ 28)⟩,
       ⟨((76473815 : Dyadic) * half ^ 27),
        ((37763973 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word38Step35 :
    word38Chunk35.foldl (fun acc a => a.applyPacked acc)
      word38State35 = word38State36 := by decide +kernel

private def word38Chunk36 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word38State37 : PackedMat2 :=
    ⟨⟨⟨((6073721 : Dyadic) * half ^ 28),
        ((-195882693 : Dyadic) * half ^ 29)⟩,
       ⟨((787853 : Dyadic) * half ^ 24),
        ((265544405 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-19929953 : Dyadic) * half ^ 27),
        ((-66558143 : Dyadic) * half ^ 29)⟩,
       ⟨((30178191 : Dyadic) * half ^ 28),
        ((-159407295 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((30178191 : Dyadic) * half ^ 28),
        ((-159407295 : Dyadic) * half ^ 29)⟩,
       ⟨((-19929953 : Dyadic) * half ^ 27),
        ((-66558143 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-787853 : Dyadic) * half ^ 24),
        ((-265544405 : Dyadic) * half ^ 29)⟩,
       ⟨((-6073721 : Dyadic) * half ^ 28),
        ((195882693 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word38Step36 :
    word38Chunk36.foldl (fun acc a => a.applyPacked acc)
      word38State36 = word38State37 := by decide +kernel

private def word38Chunk37 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word38State38 : PackedMat2 :=
    ⟨⟨⟨((-24956207 : Dyadic) * half ^ 29),
        ((-143746757 : Dyadic) * half ^ 30)⟩,
       ⟨((-109539897 : Dyadic) * half ^ 28),
        ((87424599 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-4868771 : Dyadic) * half ^ 26),
        ((-633345143 : Dyadic) * half ^ 30)⟩,
       ⟨((-146445631 : Dyadic) * half ^ 29),
        ((62161707 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-347753425 : Dyadic) * half ^ 29),
        ((107495463 : Dyadic) * half ^ 30)⟩,
       ⟨((142795859 : Dyadic) * half ^ 28),
        ((185395799 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((57792839 : Dyadic) * half ^ 28),
        ((-194123587 : Dyadic) * half ^ 30)⟩,
       ⟨((-28161079 : Dyadic) * half ^ 29),
        ((-244036001 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word38Step37 :
    word38Chunk37.foldl (fun acc a => a.applyPacked acc)
      word38State37 = word38State38 := by decide +kernel

private def word38Chunk38 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word38State39 : PackedMat2 :=
    ⟨⟨⟨((-35556297 : Dyadic) * half ^ 29),
        ((-37587653 : Dyadic) * half ^ 30)⟩,
       ⟨((1469889 : Dyadic) * half ^ 26),
        ((-37976609 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-133909859 : Dyadic) * half ^ 29),
        ((-113743321 : Dyadic) * half ^ 30)⟩,
       ⟨((24083873 : Dyadic) * half ^ 29),
        ((-48905603 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((24083873 : Dyadic) * half ^ 29),
        ((-48905603 : Dyadic) * half ^ 27)⟩,
       ⟨((-133909859 : Dyadic) * half ^ 29),
        ((-113743321 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-1469889 : Dyadic) * half ^ 26),
        ((37976609 : Dyadic) * half ^ 26)⟩,
       ⟨((35556297 : Dyadic) * half ^ 29),
        ((37587653 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word38Step38 :
    word38Chunk38.foldl (fun acc a => a.applyPacked acc)
      word38State38 = word38State39 := by decide +kernel

private def word38Chunk39 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word38State40 : PackedMat2 :=
    ⟨⟨⟨((-376195033 : Dyadic) * half ^ 31),
        ((347253441 : Dyadic) * half ^ 30)⟩,
       ⟨((-1791352227 : Dyadic) * half ^ 31),
        ((-123895415 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((294383703 : Dyadic) * half ^ 31),
        ((76109697 : Dyadic) * half ^ 31)⟩,
       ⟨((-405095969 : Dyadic) * half ^ 31),
        ((-20889195 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-294383703 : Dyadic) * half ^ 31),
        ((-76109697 : Dyadic) * half ^ 31)⟩,
       ⟨((-405095969 : Dyadic) * half ^ 31),
        ((-20889195 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-376195033 : Dyadic) * half ^ 31),
        ((347253441 : Dyadic) * half ^ 30)⟩,
       ⟨((1791352227 : Dyadic) * half ^ 31),
        ((123895415 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word38Step39 :
    word38Chunk39.foldl (fun acc a => a.applyPacked acc)
      word38State39 = word38State40 := by decide +kernel

private def word38Chunk40 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word38State41 : PackedMat2 :=
    ⟨⟨⟨((180373893 : Dyadic) * half ^ 28),
        ((-328409315 : Dyadic) * half ^ 32)⟩,
       ⟨((-128635229 : Dyadic) * half ^ 29),
        ((-1138623735 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((90560165 : Dyadic) * half ^ 31),
        ((1030668975 : Dyadic) * half ^ 32)⟩,
       ⟨((1001089575 : Dyadic) * half ^ 31),
        ((-205090857 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((154469979 : Dyadic) * half ^ 29),
        ((-455264705 : Dyadic) * half ^ 31)⟩,
       ⟨((-412789059 : Dyadic) * half ^ 31),
        ((-272912435 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-202553605 : Dyadic) * half ^ 30),
        ((-489383015 : Dyadic) * half ^ 30)⟩,
       ⟨((-733516525 : Dyadic) * half ^ 31),
        ((232112557 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word38Step40 :
    word38Chunk40.foldl (fun acc a => a.applyPacked acc)
      word38State40 = word38State41 := by decide +kernel

private def word38Chunk41 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word38State42 : PackedMat2 :=
    ⟨⟨⟨((-1524432593 : Dyadic) * half ^ 32),
        ((3629655967 : Dyadic) * half ^ 33)⟩,
       ⟨((566727685 : Dyadic) * half ^ 31),
        ((707995673 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-247077685 : Dyadic) * half ^ 30),
        ((-2874731263 : Dyadic) * half ^ 33)⟩,
       ⟨((945250793 : Dyadic) * half ^ 32),
        ((1999000257 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((945250793 : Dyadic) * half ^ 32),
        ((1999000257 : Dyadic) * half ^ 33)⟩,
       ⟨((-247077685 : Dyadic) * half ^ 30),
        ((-2874731263 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-566727685 : Dyadic) * half ^ 31),
        ((-707995673 : Dyadic) * half ^ 33)⟩,
       ⟨((1524432593 : Dyadic) * half ^ 32),
        ((-3629655967 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word38Step41 :
    word38Chunk41.foldl (fun acc a => a.applyPacked acc)
      word38State41 = word38State42 := by decide +kernel

private def word38Chunk42 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word38State43 : PackedMat2 :=
    ⟨⟨⟨((1720725695 : Dyadic) * half ^ 32),
        ((-878930301 : Dyadic) * half ^ 33)⟩,
       ⟨((-451186915 : Dyadic) * half ^ 31),
        ((755458861 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-2476718713 : Dyadic) * half ^ 32),
        ((-2341808705 : Dyadic) * half ^ 33)⟩,
       ⟨((1267561055 : Dyadic) * half ^ 32),
        ((-1153471411 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((4648751527 : Dyadic) * half ^ 33),
        ((604578829 : Dyadic) * half ^ 32)⟩,
       ⟨((34865883 : Dyadic) * half ^ 33),
        ((468034971 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((631987421 : Dyadic) * half ^ 33),
        ((818351865 : Dyadic) * half ^ 33)⟩,
       ⟨((-2389848023 : Dyadic) * half ^ 33),
        ((2623099525 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word38Step42 :
    word38Chunk42.foldl (fun acc a => a.applyPacked acc)
      word38State42 = word38State43 := by decide +kernel

private def word38Chunk43 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word38State44 : PackedMat2 :=
    ⟨⟨⟨((4695638585 : Dyadic) * half ^ 34),
        ((1569845663 : Dyadic) * half ^ 33)⟩,
       ⟨((6498152717 : Dyadic) * half ^ 34),
        ((1060601807 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-6586752099 : Dyadic) * half ^ 34),
        ((-1828142739 : Dyadic) * half ^ 34)⟩,
       ⟨((-11957171093 : Dyadic) * half ^ 34),
        ((1408206465 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-6586752099 : Dyadic) * half ^ 34),
        ((-1828142739 : Dyadic) * half ^ 34)⟩,
       ⟨((11957171093 : Dyadic) * half ^ 34),
        ((-1408206465 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-4695638585 : Dyadic) * half ^ 34),
        ((-1569845663 : Dyadic) * half ^ 33)⟩,
       ⟨((6498152717 : Dyadic) * half ^ 34),
        ((1060601807 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word38Step43 :
    word38Chunk43.foldl (fun acc a => a.applyPacked acc)
      word38State43 = word38State44 := by decide +kernel

private def word38Chunk44 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word38State45 : PackedMat2 :=
    ⟨⟨⟨((8235402139 : Dyadic) * half ^ 35),
        ((-3685351827 : Dyadic) * half ^ 34)⟩,
       ⟨((22678558551 : Dyadic) * half ^ 35),
        ((1721056521 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-6877300273 : Dyadic) * half ^ 35),
        ((-2460456145 : Dyadic) * half ^ 35)⟩,
       ⟨((-20600071103 : Dyadic) * half ^ 35),
        ((-115250375 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((2690956895 : Dyadic) * half ^ 35),
        ((1717335711 : Dyadic) * half ^ 32)⟩,
       ⟨((2229955395 : Dyadic) * half ^ 35),
        ((-6861385415 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-5649647133 : Dyadic) * half ^ 35),
        ((15456980345 : Dyadic) * half ^ 35)⟩,
       ⟨((-9091760175 : Dyadic) * half ^ 35),
        ((-3610789103 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word38Step44 :
    word38Chunk44.foldl (fun acc a => a.applyPacked acc)
      word38State44 = word38State45 := by decide +kernel

private def word38Chunk45 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word38State46 : PackedMat2 :=
    ⟨⟨⟨((-4204973689 : Dyadic) * half ^ 34),
        ((210776449 : Dyadic) * half ^ 31)⟩,
       ⟨((9277407727 : Dyadic) * half ^ 35),
        ((8884155521 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((9589429341 : Dyadic) * half ^ 34),
        ((-2462871501 : Dyadic) * half ^ 35)⟩,
       ⟨((448550183 : Dyadic) * half ^ 35),
        ((-15215615451 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((6376371975 : Dyadic) * half ^ 34),
        ((18730308499 : Dyadic) * half ^ 36)⟩,
       ⟨((2209810869 : Dyadic) * half ^ 32),
        ((-19627408865 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((5511732337 : Dyadic) * half ^ 35),
        ((17687355105 : Dyadic) * half ^ 36)⟩,
       ⟨((12256578705 : Dyadic) * half ^ 35),
        ((867460349 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word38Step45 :
    word38Chunk45.foldl (fun acc a => a.applyPacked acc)
      word38State45 = word38State46 := by decide +kernel

private def word38Chunk46 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word38State47 : PackedMat2 :=
    ⟨⟨⟨((-15285305309 : Dyadic) * half ^ 36),
        ((-53318514297 : Dyadic) * half ^ 37)⟩,
       ⟨((-1040015411 : Dyadic) * half ^ 33),
        ((44927070687 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-5443012761 : Dyadic) * half ^ 35),
        ((51101593161 : Dyadic) * half ^ 37)⟩,
       ⟨((-23508950925 : Dyadic) * half ^ 36),
        ((-4896102985 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-23508950925 : Dyadic) * half ^ 36),
        ((-4896102985 : Dyadic) * half ^ 37)⟩,
       ⟨((-5443012761 : Dyadic) * half ^ 35),
        ((51101593161 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((1040015411 : Dyadic) * half ^ 33),
        ((-44927070687 : Dyadic) * half ^ 37)⟩,
       ⟨((15285305309 : Dyadic) * half ^ 36),
        ((53318514297 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word38Step46 :
    word38Chunk46.foldl (fun acc a => a.applyPacked acc)
      word38State46 = word38State47 := by decide +kernel

private def word38Chunk47 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word38State48 : PackedMat2 :=
    ⟨⟨⟨((-89637459849 : Dyadic) * half ^ 37),
        ((-17884524053 : Dyadic) * half ^ 38)⟩,
       ⟨((-3356764461 : Dyadic) * half ^ 33),
        ((84532874507 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-18285580801 : Dyadic) * half ^ 36),
        ((-62723472475 : Dyadic) * half ^ 38)⟩,
       ⟨((23863818143 : Dyadic) * half ^ 37),
        ((26949485795 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-44836479135 : Dyadic) * half ^ 37),
        ((-60434979745 : Dyadic) * half ^ 38)⟩,
       ⟨((4471748335 : Dyadic) * half ^ 35),
        ((12707343459 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((3200543705 : Dyadic) * half ^ 33),
        ((35929228473 : Dyadic) * half ^ 38)⟩,
       ⟨((33324175227 : Dyadic) * half ^ 37),
        ((-143345691225 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word38Step47 :
    word38Chunk47.foldl (fun acc a => a.applyPacked acc)
      word38State47 = word38State48 := by decide +kernel

private def word38Chunk48 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word38State49 : PackedMat2 :=
    ⟨⟨⟨((2989972295 : Dyadic) * half ^ 36),
        ((-1135770625 : Dyadic) * half ^ 31)⟩,
       ⟨((7866644065 : Dyadic) * half ^ 36),
        ((-31288757165 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-70147760997 : Dyadic) * half ^ 37),
        ((-3889733623 : Dyadic) * half ^ 37)⟩,
       ⟨((-12407391957 : Dyadic) * half ^ 35),
        ((-16440180121 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-12407391957 : Dyadic) * half ^ 35),
        ((-16440180121 : Dyadic) * half ^ 38)⟩,
       ⟨((-70147760997 : Dyadic) * half ^ 37),
        ((-3889733623 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-7866644065 : Dyadic) * half ^ 36),
        ((31288757165 : Dyadic) * half ^ 38)⟩,
       ⟨((-2989972295 : Dyadic) * half ^ 36),
        ((1135770625 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word38Step48 :
    word38Chunk48.foldl (fun acc a => a.applyPacked acc)
      word38State48 = word38State49 := by decide +kernel

private def word38Chunk49 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word38State50 : PackedMat2 :=
    ⟨⟨⟨((-96914948589 : Dyadic) * half ^ 39),
        ((-37968234997 : Dyadic) * half ^ 38)⟩,
       ⟨((297811870269 : Dyadic) * half ^ 39),
        ((-159134586379 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-33789457445 : Dyadic) * half ^ 39),
        ((-142405373115 : Dyadic) * half ^ 39)⟩,
       ⟨((-236255481345 : Dyadic) * half ^ 39),
        ((-74540047099 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((291485467313 : Dyadic) * half ^ 39),
        ((135022469395 : Dyadic) * half ^ 39)⟩,
       ⟨((-6674721083 : Dyadic) * half ^ 39),
        ((-50616505975 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-235071056373 : Dyadic) * half ^ 39),
        ((12556057605 : Dyadic) * half ^ 36)⟩,
       ⟨((83198116385 : Dyadic) * half ^ 39),
        ((-197363409429 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word38Step49 :
    word38Chunk49.foldl (fun acc a => a.applyPacked acc)
      word38State49 = word38State50 := by decide +kernel

private def word38Chunk50 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word38State51 : PackedMat2 :=
    ⟨⟨⟨((86893331009 : Dyadic) * half ^ 39),
        ((172730116339 : Dyadic) * half ^ 40)⟩,
       ⟨((-318236298157 : Dyadic) * half ^ 39),
        ((82413565275 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((10412150875 : Dyadic) * half ^ 38),
        ((493166940103 : Dyadic) * half ^ 40)⟩,
       ⟨((-1455331757 : Dyadic) * half ^ 38),
        ((-325711157741 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((10412150875 : Dyadic) * half ^ 38),
        ((493166940103 : Dyadic) * half ^ 40)⟩,
       ⟨((1455331757 : Dyadic) * half ^ 38),
        ((325711157741 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-86893331009 : Dyadic) * half ^ 39),
        ((-172730116339 : Dyadic) * half ^ 40)⟩,
       ⟨((-318236298157 : Dyadic) * half ^ 39),
        ((82413565275 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word38Step50 :
    word38Chunk50.foldl (fun acc a => a.applyPacked acc)
      word38State50 = word38State51 := by decide +kernel

private def word38Chunk51 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word38State52 : PackedMat2 :=
    ⟨⟨⟨((407238523315 : Dyadic) * half ^ 40),
        ((73459458507 : Dyadic) * half ^ 41)⟩,
       ⟨((-120066076319 : Dyadic) * half ^ 39),
        ((-487477445239 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((77956180553 : Dyadic) * half ^ 37),
        ((136016794093 : Dyadic) * half ^ 41)⟩,
       ⟨((-259728580459 : Dyadic) * half ^ 40),
        ((892475242241 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-259728580459 : Dyadic) * half ^ 40),
        ((892475242241 : Dyadic) * half ^ 41)⟩,
       ⟨((77956180553 : Dyadic) * half ^ 37),
        ((136016794093 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((120066076319 : Dyadic) * half ^ 39),
        ((487477445239 : Dyadic) * half ^ 41)⟩,
       ⟨((-407238523315 : Dyadic) * half ^ 40),
        ((-73459458507 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word38Step51 :
    word38Chunk51.foldl (fun acc a => a.applyPacked acc)
      word38State51 = word38State52 := by decide +kernel

private def word38Chunk52 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word38State53 : PackedMat2 :=
    ⟨⟨⟨((1088614618847 : Dyadic) * half ^ 41),
        ((484656636761 : Dyadic) * half ^ 42)⟩,
       ⟨((192019348879 : Dyadic) * half ^ 39),
        ((-925205719823 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((143069344915 : Dyadic) * half ^ 39),
        ((631763667159 : Dyadic) * half ^ 42)⟩,
       ⟨((-89706366787 : Dyadic) * half ^ 41),
        ((1990034405597 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-679135369219 : Dyadic) * half ^ 41),
        ((661983746447 : Dyadic) * half ^ 42)⟩,
       ⟨((-655449518189 : Dyadic) * half ^ 40),
        ((-482571012873 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-176232794573 : Dyadic) * half ^ 39),
        ((-320537223331 : Dyadic) * half ^ 42)⟩,
       ⟨((-220274541531 : Dyadic) * half ^ 41),
        ((1856692014363 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word38Step52 :
    word38Chunk52.foldl (fun acc a => a.applyPacked acc)
      word38State52 = word38State53 := by decide +kernel

private def word38Chunk53 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word38State54 : PackedMat2 :=
    ⟨⟨⟨((-915448102645 : Dyadic) * half ^ 41),
        ((177883756605 : Dyadic) * half ^ 40)⟩,
       ⟨((-605318177289 : Dyadic) * half ^ 41),
        ((1391991679037 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-29166211881 : Dyadic) * half ^ 36),
        ((-285043943705 : Dyadic) * half ^ 40)⟩,
       ⟨((876304120647 : Dyadic) * half ^ 41),
        ((490496144399 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((876304120647 : Dyadic) * half ^ 41),
        ((490496144399 : Dyadic) * half ^ 42)⟩,
       ⟨((-29166211881 : Dyadic) * half ^ 36),
        ((-285043943705 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((605318177289 : Dyadic) * half ^ 41),
        ((-1391991679037 : Dyadic) * half ^ 42)⟩,
       ⟨((915448102645 : Dyadic) * half ^ 41),
        ((-177883756605 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word38Step53 :
    word38Chunk53.foldl (fun acc a => a.applyPacked acc)
      word38State53 = word38State54 := by decide +kernel

private def word38Chunk54 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word38State55 : PackedMat2 :=
    ⟨⟨⟨((1984026776997 : Dyadic) * half ^ 43),
        ((-800757457 : Dyadic) * half ^ 31)⟩,
       ⟨((-677584766435 : Dyadic) * half ^ 43),
        ((-2308724228997 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-6136486496391 : Dyadic) * half ^ 43),
        ((-836367424849 : Dyadic) * half ^ 43)⟩,
       ⟨((-205188618969 : Dyadic) * half ^ 43),
        ((461281195915 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-86194966981 : Dyadic) * half ^ 43),
        ((198177347355 : Dyadic) * half ^ 39)⟩,
       ⟨((1758929816679 : Dyadic) * half ^ 43),
        ((2965648938711 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-5588626772869 : Dyadic) * half ^ 43),
        ((653221005281 : Dyadic) * half ^ 43)⟩,
       ⟨((-971178314875 : Dyadic) * half ^ 43),
        ((332701442929 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word38Step54 :
    word38Chunk54.foldl (fun acc a => a.applyPacked acc)
      word38State54 = word38State55 := by decide +kernel

private def word38Chunk55 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word38State56 : PackedMat2 :=
    ⟨⟨⟨((-3043704470139 : Dyadic) * half ^ 43),
        ((81489271841 : Dyadic) * half ^ 38)⟩,
       ⟨((-2192477044347 : Dyadic) * half ^ 42),
        ((-1198463683789 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-394980732147 : Dyadic) * half ^ 43),
        ((-593790582403 : Dyadic) * half ^ 41)⟩,
       ⟨((-383019317 : Dyadic) * half ^ 30),
        ((1119173250027 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-394980732147 : Dyadic) * half ^ 43),
        ((-593790582403 : Dyadic) * half ^ 41)⟩,
       ⟨((383019317 : Dyadic) * half ^ 30),
        ((-1119173250027 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((3043704470139 : Dyadic) * half ^ 43),
        ((-81489271841 : Dyadic) * half ^ 38)⟩,
       ⟨((-2192477044347 : Dyadic) * half ^ 42),
        ((-1198463683789 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word38Step55 :
    word38Chunk55.foldl (fun acc a => a.applyPacked acc)
      word38State55 = word38State56 := by decide +kernel

private def word38Chunk56 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word38State57 : PackedMat2 :=
    ⟨⟨⟨((10856256566103 : Dyadic) * half ^ 44),
        ((2239120771889 : Dyadic) * half ^ 45)⟩,
       ⟨((-542902953207 : Dyadic) * half ^ 41),
        ((-6297308292281 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-700950541513 : Dyadic) * half ^ 43),
        ((-10456966523181 : Dyadic) * half ^ 45)⟩,
       ⟨((6847949834397 : Dyadic) * half ^ 44),
        ((-9684463530397 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((48281437049 : Dyadic) * half ^ 41),
        ((8249850917423 : Dyadic) * half ^ 45)⟩,
       ⟨((-10070715026789 : Dyadic) * half ^ 44),
        ((5446048751371 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((4268214532085 : Dyadic) * half ^ 44),
        ((15199480191759 : Dyadic) * half ^ 45)⟩,
       ⟨((507273440049 : Dyadic) * half ^ 42),
        ((-6513032940447 : Dyadic) * half ^ 45)⟩⟩⟩
private lemma word38Step56 :
    word38Chunk56.foldl (fun acc a => a.applyPacked acc)
      word38State56 = word38State57 := by decide +kernel

private def word38Chunk57 : List Letter := [.t, .h, .s, .t, .h, .t, .h]
private def word38State58 : PackedMat2 :=
    ⟨⟨⟨((7984245480571 : Dyadic) * half ^ 45),
        ((9616696986917 : Dyadic) * half ^ 44)⟩,
       ⟨((11406898108219 : Dyadic) * half ^ 45),
        ((-4032947502455 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((-6448659791475 : Dyadic) * half ^ 45),
        ((4559891068117 : Dyadic) * half ^ 45)⟩,
       ⟨((-6743140987767 : Dyadic) * half ^ 45),
        ((4768120718947 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((6448659791475 : Dyadic) * half ^ 45),
        ((-4559891068117 : Dyadic) * half ^ 45)⟩,
       ⟨((-6743140987767 : Dyadic) * half ^ 45),
        ((4768120718947 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((7984245480571 : Dyadic) * half ^ 45),
        ((9616696986917 : Dyadic) * half ^ 44)⟩,
       ⟨((-11406898108219 : Dyadic) * half ^ 45),
        ((4032947502455 : Dyadic) * half ^ 44)⟩⟩⟩
private lemma word38Step57 :
    word38Chunk57.foldl (fun acc a => a.applyPacked acc)
      word38State57 = word38State58 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word38_check : check word38 38 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word38 = word38State58.toMatrix := by
    unfold evalRingPacked
    change ((
      word38Chunk0 ++ word38Chunk1 ++ word38Chunk2 ++ word38Chunk3 ++
      word38Chunk4 ++ word38Chunk5 ++ word38Chunk6 ++ word38Chunk7 ++
      word38Chunk8 ++ word38Chunk9 ++ word38Chunk10 ++ word38Chunk11 ++
      word38Chunk12 ++ word38Chunk13 ++ word38Chunk14 ++ word38Chunk15 ++
      word38Chunk16 ++ word38Chunk17 ++ word38Chunk18 ++ word38Chunk19 ++
      word38Chunk20 ++ word38Chunk21 ++ word38Chunk22 ++ word38Chunk23 ++
      word38Chunk24 ++ word38Chunk25 ++ word38Chunk26 ++ word38Chunk27 ++
      word38Chunk28 ++ word38Chunk29 ++ word38Chunk30 ++ word38Chunk31 ++
      word38Chunk32 ++ word38Chunk33 ++ word38Chunk34 ++ word38Chunk35 ++
      word38Chunk36 ++ word38Chunk37 ++ word38Chunk38 ++ word38Chunk39 ++
      word38Chunk40 ++ word38Chunk41 ++ word38Chunk42 ++ word38Chunk43 ++
      word38Chunk44 ++ word38Chunk45 ++ word38Chunk46 ++ word38Chunk47 ++
      word38Chunk48 ++ word38Chunk49 ++ word38Chunk50 ++ word38Chunk51 ++
      word38Chunk52 ++ word38Chunk53 ++ word38Chunk54 ++ word38Chunk55 ++
      word38Chunk56 ++ word38Chunk57
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word38Step0, word38Step1, word38Step2, word38Step3, word38Step4,
      word38Step5, word38Step6, word38Step7, word38Step8, word38Step9,
      word38Step10, word38Step11, word38Step12, word38Step13, word38Step14,
      word38Step15, word38Step16, word38Step17, word38Step18, word38Step19,
      word38Step20, word38Step21, word38Step22, word38Step23, word38Step24,
      word38Step25, word38Step26, word38Step27, word38Step28, word38Step29,
      word38Step30, word38Step31, word38Step32, word38Step33, word38Step34,
      word38Step35, word38Step36, word38Step37, word38Step38, word38Step39,
      word38Step40, word38Step41, word38Step42, word38Step43, word38Step44,
      word38Step45, word38Step46, word38Step47, word38Step48, word38Step49,
      word38Step50, word38Step51, word38Step52, word38Step53, word38Step54,
      word38Step55, word38Step56, word38Step57]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
