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
private def word19Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word19State1 : PackedMat2 :=
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
private lemma word19Step0 :
    word19Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word19State1 := by decide +kernel

private def word19Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word19State2 : PackedMat2 :=
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
private lemma word19Step1 :
    word19Chunk1.foldl (fun acc a => a.applyPacked acc)
      word19State1 = word19State2 := by decide +kernel

private def word19Chunk2 : List Letter := [.h, .s, .h, .s, .s, .h, .h, .s]
private def word19State3 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word19Step2 :
    word19Chunk2.foldl (fun acc a => a.applyPacked acc)
      word19State2 = word19State3 := by decide +kernel

private def word19Chunk3 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word19State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word19Step3 :
    word19Chunk3.foldl (fun acc a => a.applyPacked acc)
      word19State3 = word19State4 := by decide +kernel

private def word19Chunk4 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word19State5 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word19Step4 :
    word19Chunk4.foldl (fun acc a => a.applyPacked acc)
      word19State4 = word19State5 := by decide +kernel

private def word19Chunk5 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word19State6 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word19Step5 :
    word19Chunk5.foldl (fun acc a => a.applyPacked acc)
      word19State5 = word19State6 := by decide +kernel

private def word19Chunk6 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word19State7 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 3),
        ((9 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((-9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((-13 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((9 : Dyadic) * half ^ 5)⟩,
       ⟨((9 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-7 : Dyadic) * half ^ 5)⟩,
       ⟨((-9 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word19Step6 :
    word19Chunk6.foldl (fun acc a => a.applyPacked acc)
      word19State6 = word19State7 := by decide +kernel

private def word19Chunk7 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word19State8 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 5),
        ((17 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((9 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((-5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word19Step7 :
    word19Chunk7.foldl (fun acc a => a.applyPacked acc)
      word19State7 = word19State8 := by decide +kernel

private def word19Chunk8 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word19State9 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((5 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((27 : Dyadic) * half ^ 6)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((27 : Dyadic) * half ^ 6)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((5 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word19Step8 :
    word19Chunk8.foldl (fun acc a => a.applyPacked acc)
      word19State8 = word19State9 := by decide +kernel

private def word19Chunk9 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word19State10 : PackedMat2 :=
    ⟨⟨⟨((7 : Dyadic) * half ^ 7),
        ((1 : Dyadic) * half ^ 6)⟩,
       ⟨((-3 : Dyadic) * half ^ 7),
        ((57 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((71 : Dyadic) * half ^ 7),
        ((-9 : Dyadic) * half ^ 6)⟩,
       ⟨((41 : Dyadic) * half ^ 7),
        ((35 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((53 : Dyadic) * half ^ 7),
        ((-15 : Dyadic) * half ^ 7)⟩,
       ⟨((17 : Dyadic) * half ^ 7),
        ((7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-55 : Dyadic) * half ^ 7),
        ((5 : Dyadic) * half ^ 7)⟩,
       ⟨((-59 : Dyadic) * half ^ 7),
        ((-1 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word19Step9 :
    word19Chunk9.foldl (fun acc a => a.applyPacked acc)
      word19State9 = word19State10 := by decide +kernel

private def word19Chunk10 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word19State11 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((81 : Dyadic) * half ^ 7),
        ((17 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-35 : Dyadic) * half ^ 7),
        ((19 : Dyadic) * half ^ 7)⟩,
       ⟨((9 : Dyadic) * half ^ 4),
        ((-17 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 4),
        ((17 : Dyadic) * half ^ 7)⟩,
       ⟨((35 : Dyadic) * half ^ 7),
        ((-19 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((81 : Dyadic) * half ^ 7),
        ((17 : Dyadic) * half ^ 7)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word19Step10 :
    word19Chunk10.foldl (fun acc a => a.applyPacked acc)
      word19State10 = word19State11 := by decide +kernel

private def word19Chunk11 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word19State12 : PackedMat2 :=
    ⟨⟨⟨((-149 : Dyadic) * half ^ 8),
        ((9 : Dyadic) * half ^ 9)⟩,
       ⟨((1 : Dyadic) * half ^ 6),
        ((167 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-67 : Dyadic) * half ^ 8),
        ((-149 : Dyadic) * half ^ 9)⟩,
       ⟨((-35 : Dyadic) * half ^ 7),
        ((133 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-67 : Dyadic) * half ^ 8),
        ((-149 : Dyadic) * half ^ 9)⟩,
       ⟨((35 : Dyadic) * half ^ 7),
        ((-133 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((149 : Dyadic) * half ^ 8),
        ((-9 : Dyadic) * half ^ 9)⟩,
       ⟨((1 : Dyadic) * half ^ 6),
        ((167 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word19Step11 :
    word19Chunk11.foldl (fun acc a => a.applyPacked acc)
      word19State11 = word19State12 := by decide +kernel

private def word19Chunk12 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word19State13 : PackedMat2 :=
    ⟨⟨⟨((-225 : Dyadic) * half ^ 9),
        ((-143 : Dyadic) * half ^ 10)⟩,
       ⟨((39 : Dyadic) * half ^ 8),
        ((-411 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 9),
        ((-39 : Dyadic) * half ^ 10)⟩,
       ⟨(0 : Dyadic),
        ((469 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-215 : Dyadic) * half ^ 9),
        ((-3 : Dyadic) * half ^ 10)⟩,
       ⟨((127 : Dyadic) * half ^ 8),
        ((-3 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-277 : Dyadic) * half ^ 9),
        ((-147 : Dyadic) * half ^ 10)⟩,
       ⟨((67 : Dyadic) * half ^ 8),
        ((-303 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word19Step12 :
    word19Chunk12.foldl (fun acc a => a.applyPacked acc)
      word19State12 = word19State13 := by decide +kernel

private def word19Chunk13 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word19State14 : PackedMat2 :=
    ⟨⟨⟨((-221 : Dyadic) * half ^ 10),
        ((-127 : Dyadic) * half ^ 9)⟩,
       ⟨((-639 : Dyadic) * half ^ 10),
        ((13 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((39 : Dyadic) * half ^ 10),
        ((-437 : Dyadic) * half ^ 10)⟩,
       ⟨((247 : Dyadic) * half ^ 10),
        ((-91 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-173 : Dyadic) * half ^ 9),
        ((-13 : Dyadic) * half ^ 7)⟩,
       ⟨((33 : Dyadic) * half ^ 6),
        ((-143 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((35 : Dyadic) * half ^ 7),
        ((-209 : Dyadic) * half ^ 10)⟩,
       ⟨((-57 : Dyadic) * half ^ 8),
        ((-215 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word19Step13 :
    word19Chunk13.foldl (fun acc a => a.applyPacked acc)
      word19State13 = word19State14 := by decide +kernel

private def word19Chunk14 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word19State15 : PackedMat2 :=
    ⟨⟨⟨((333 : Dyadic) * half ^ 11),
        ((33 : Dyadic) * half ^ 7)⟩,
       ⟨((151 : Dyadic) * half ^ 11),
        ((-273 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-1271 : Dyadic) * half ^ 11),
        ((225 : Dyadic) * half ^ 10)⟩,
       ⟨((-957 : Dyadic) * half ^ 11),
        ((-457 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-957 : Dyadic) * half ^ 11),
        ((-457 : Dyadic) * half ^ 11)⟩,
       ⟨((-1271 : Dyadic) * half ^ 11),
        ((225 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-151 : Dyadic) * half ^ 11),
        ((273 : Dyadic) * half ^ 11)⟩,
       ⟨((-333 : Dyadic) * half ^ 11),
        ((-33 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word19Step14 :
    word19Chunk14.foldl (fun acc a => a.applyPacked acc)
      word19State14 = word19State15 := by decide +kernel

private def word19Chunk15 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word19State16 : PackedMat2 :=
    ⟨⟨⟨((-255 : Dyadic) * half ^ 12),
        ((-339 : Dyadic) * half ^ 12)⟩,
       ⟨((985 : Dyadic) * half ^ 12),
        ((-87 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((281 : Dyadic) * half ^ 12),
        ((115 : Dyadic) * half ^ 12)⟩,
       ⟨((-19 : Dyadic) * half ^ 12),
        ((-1385 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((2885 : Dyadic) * half ^ 12),
        ((75 : Dyadic) * half ^ 11)⟩,
       ⟨((2655 : Dyadic) * half ^ 12),
        ((-131 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((165 : Dyadic) * half ^ 12),
        ((155 : Dyadic) * half ^ 10)⟩,
       ⟨((-513 : Dyadic) * half ^ 12),
        ((365 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word19Step15 :
    word19Chunk15.foldl (fun acc a => a.applyPacked acc)
      word19State15 = word19State16 := by decide +kernel

private def word19Chunk16 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word19State17 : PackedMat2 :=
    ⟨⟨⟨((-551 : Dyadic) * half ^ 10),
        ((331 : Dyadic) * half ^ 13)⟩,
       ⟨((945 : Dyadic) * half ^ 11),
        ((257 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-921 : Dyadic) * half ^ 12),
        ((2651 : Dyadic) * half ^ 13)⟩,
       ⟨((-1229 : Dyadic) * half ^ 12),
        ((-2185 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((233 : Dyadic) * half ^ 12),
        ((-1075 : Dyadic) * half ^ 12)⟩,
       ⟨((1209 : Dyadic) * half ^ 11),
        ((77 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-147 : Dyadic) * half ^ 11),
        ((157 : Dyadic) * half ^ 12)⟩,
       ⟨((-37 : Dyadic) * half ^ 12),
        ((2047 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word19Step16 :
    word19Chunk16.foldl (fun acc a => a.applyPacked acc)
      word19State16 = word19State17 := by decide +kernel

private def word19Chunk17 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word19State18 : PackedMat2 :=
    ⟨⟨⟨((-285 : Dyadic) * half ^ 12),
        ((-2031 : Dyadic) * half ^ 14)⟩,
       ⟨((-2571 : Dyadic) * half ^ 13),
        ((1945 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1693 : Dyadic) * half ^ 11),
        ((-489 : Dyadic) * half ^ 14)⟩,
       ⟨((2431 : Dyadic) * half ^ 13),
        ((2943 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1227 : Dyadic) * half ^ 13),
        ((-9203 : Dyadic) * half ^ 14)⟩,
       ⟨((429 : Dyadic) * half ^ 11),
        ((-4341 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-43 : Dyadic) * half ^ 13),
        ((-3141 : Dyadic) * half ^ 14)⟩,
       ⟨((-497 : Dyadic) * half ^ 11),
        ((2001 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word19Step17 :
    word19Chunk17.foldl (fun acc a => a.applyPacked acc)
      word19State17 = word19State18 := by decide +kernel

private def word19Chunk18 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word19State19 : PackedMat2 :=
    ⟨⟨⟨((-1891 : Dyadic) * half ^ 14),
        ((-1507 : Dyadic) * half ^ 13)⟩,
       ⟨((-5397 : Dyadic) * half ^ 14),
        ((-1671 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-5491 : Dyadic) * half ^ 14),
        ((6273 : Dyadic) * half ^ 14)⟩,
       ⟨((9145 : Dyadic) * half ^ 14),
        ((1171 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-5491 : Dyadic) * half ^ 14),
        ((6273 : Dyadic) * half ^ 14)⟩,
       ⟨((-9145 : Dyadic) * half ^ 14),
        ((-1171 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1891 : Dyadic) * half ^ 14),
        ((1507 : Dyadic) * half ^ 13)⟩,
       ⟨((-5397 : Dyadic) * half ^ 14),
        ((-1671 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word19Step18 :
    word19Chunk18.foldl (fun acc a => a.applyPacked acc)
      word19State18 = word19State19 := by decide +kernel

private def word19Chunk19 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word19State20 : PackedMat2 :=
    ⟨⟨⟨((6295 : Dyadic) * half ^ 15),
        ((-2145 : Dyadic) * half ^ 15)⟩,
       ⟨((-13107 : Dyadic) * half ^ 15),
        ((-459 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1795 : Dyadic) * half ^ 15),
        ((10271 : Dyadic) * half ^ 15)⟩,
       ⟨((443 : Dyadic) * half ^ 15),
        ((1111 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((443 : Dyadic) * half ^ 15),
        ((1111 : Dyadic) * half ^ 11)⟩,
       ⟨((-1795 : Dyadic) * half ^ 15),
        ((10271 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((13107 : Dyadic) * half ^ 15),
        ((459 : Dyadic) * half ^ 13)⟩,
       ⟨((-6295 : Dyadic) * half ^ 15),
        ((2145 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word19Step19 :
    word19Chunk19.foldl (fun acc a => a.applyPacked acc)
      word19State19 = word19State20 := by decide +kernel

private def word19Chunk20 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word19State21 : PackedMat2 :=
    ⟨⟨⟨((17275 : Dyadic) * half ^ 15),
        ((6503 : Dyadic) * half ^ 15)⟩,
       ⟨((1979 : Dyadic) * half ^ 14),
        ((-2417 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-543 : Dyadic) * half ^ 14),
        ((-805 : Dyadic) * half ^ 11)⟩,
       ⟨((13059 : Dyadic) * half ^ 15),
        ((-8941 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((21821 : Dyadic) * half ^ 15),
        ((-11973 : Dyadic) * half ^ 16)⟩,
       ⟨((3939 : Dyadic) * half ^ 15),
        ((14145 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((2043 : Dyadic) * half ^ 14),
        ((21233 : Dyadic) * half ^ 16)⟩,
       ⟨((1115 : Dyadic) * half ^ 12),
        ((13317 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word19Step20 :
    word19Chunk20.foldl (fun acc a => a.applyPacked acc)
      word19State20 = word19State21 := by decide +kernel

private def word19Chunk21 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word19State22 : PackedMat2 :=
    ⟨⟨⟨((-12773 : Dyadic) * half ^ 16),
        ((51357 : Dyadic) * half ^ 17)⟩,
       ⟨((4251 : Dyadic) * half ^ 15),
        ((6777 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-42905 : Dyadic) * half ^ 16),
        ((-5523 : Dyadic) * half ^ 17)⟩,
       ⟨((-1743 : Dyadic) * half ^ 12),
        ((-12959 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-42905 : Dyadic) * half ^ 16),
        ((-5523 : Dyadic) * half ^ 17)⟩,
       ⟨((1743 : Dyadic) * half ^ 12),
        ((12959 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((12773 : Dyadic) * half ^ 16),
        ((-51357 : Dyadic) * half ^ 17)⟩,
       ⟨((4251 : Dyadic) * half ^ 15),
        ((6777 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word19Step21 :
    word19Chunk21.foldl (fun acc a => a.applyPacked acc)
      word19State21 = word19State22 := by decide +kernel

private def word19Chunk22 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word19State23 : PackedMat2 :=
    ⟨⟨⟨((30279 : Dyadic) * half ^ 17),
        ((-47213 : Dyadic) * half ^ 17)⟩,
       ⟨((17033 : Dyadic) * half ^ 17),
        ((55551 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((52221 : Dyadic) * half ^ 17),
        ((6185 : Dyadic) * half ^ 16)⟩,
       ⟨((4809 : Dyadic) * half ^ 17),
        ((-16907 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-5773 : Dyadic) * half ^ 14),
        ((-11853 : Dyadic) * half ^ 16)⟩,
       ⟨((-5361 : Dyadic) * half ^ 15),
        ((28515 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-25691 : Dyadic) * half ^ 15),
        ((6623 : Dyadic) * half ^ 17)⟩,
       ⟨((-4169 : Dyadic) * half ^ 16),
        ((-2957 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word19Step22 :
    word19Chunk22.foldl (fun acc a => a.applyPacked acc)
      word19State22 = word19State23 := by decide +kernel

private def word19Chunk23 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word19State24 : PackedMat2 :=
    ⟨⟨⟨((-145267 : Dyadic) * half ^ 18),
        ((-35529 : Dyadic) * half ^ 18)⟩,
       ⟨((73805 : Dyadic) * half ^ 18),
        ((-33369 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-27879 : Dyadic) * half ^ 18),
        ((-10401 : Dyadic) * half ^ 18)⟩,
       ⟨((-4311 : Dyadic) * half ^ 18),
        ((15239 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-132313 : Dyadic) * half ^ 18),
        ((-1473 : Dyadic) * half ^ 15)⟩,
       ⟨((-111511 : Dyadic) * half ^ 18),
        ((16095 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-31209 : Dyadic) * half ^ 18),
        ((3423 : Dyadic) * half ^ 13)⟩,
       ⟨((-102267 : Dyadic) * half ^ 18),
        ((-35731 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word19Step23 :
    word19Chunk23.foldl (fun acc a => a.applyPacked acc)
      word19State23 = word19State24 := by decide +kernel

private def word19Chunk24 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word19State25 : PackedMat2 :=
    ⟨⟨⟨((-52457 : Dyadic) * half ^ 17),
        ((-20617 : Dyadic) * half ^ 19)⟩,
       ⟨((-29373 : Dyadic) * half ^ 16),
        ((-4515 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((95105 : Dyadic) * half ^ 18),
        ((-112677 : Dyadic) * half ^ 19)⟩,
       ⟨((34457 : Dyadic) * half ^ 18),
        ((232831 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((60077 : Dyadic) * half ^ 18),
        ((64781 : Dyadic) * half ^ 18)⟩,
       ⟨((-86377 : Dyadic) * half ^ 17),
        ((7581 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((6283 : Dyadic) * half ^ 17),
        ((111203 : Dyadic) * half ^ 18)⟩,
       ⟨((8051 : Dyadic) * half ^ 18),
        ((-6289 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word19Step24 :
    word19Chunk24.foldl (fun acc a => a.applyPacked acc)
      word19State24 = word19State25 := by decide +kernel

private def word19Chunk25 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word19State26 : PackedMat2 :=
    ⟨⟨⟨((-54277 : Dyadic) * half ^ 18),
        ((136343 : Dyadic) * half ^ 19)⟩,
       ⟨((-115255 : Dyadic) * half ^ 19),
        ((-32905 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-102877 : Dyadic) * half ^ 19),
        ((50937 : Dyadic) * half ^ 18)⟩,
       ⟨((-8783 : Dyadic) * half ^ 17),
        ((71995 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((8783 : Dyadic) * half ^ 17),
        ((-71995 : Dyadic) * half ^ 18)⟩,
       ⟨((102877 : Dyadic) * half ^ 19),
        ((-50937 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-115255 : Dyadic) * half ^ 19),
        ((-32905 : Dyadic) * half ^ 16)⟩,
       ⟨((-54277 : Dyadic) * half ^ 18),
        ((136343 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word19Step25 :
    word19Chunk25.foldl (fun acc a => a.applyPacked acc)
      word19State25 = word19State26 := by decide +kernel

private def word19Chunk26 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word19State27 : PackedMat2 :=
    ⟨⟨⟨((345825 : Dyadic) * half ^ 20),
        ((241627 : Dyadic) * half ^ 21)⟩,
       ⟨((-440449 : Dyadic) * half ^ 19),
        ((180185 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-160703 : Dyadic) * half ^ 20),
        ((-500435 : Dyadic) * half ^ 21)⟩,
       ⟨((29103 : Dyadic) * half ^ 19),
        ((-90325 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-160703 : Dyadic) * half ^ 20),
        ((-500435 : Dyadic) * half ^ 21)⟩,
       ⟨((-29103 : Dyadic) * half ^ 19),
        ((90325 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-345825 : Dyadic) * half ^ 20),
        ((-241627 : Dyadic) * half ^ 21)⟩,
       ⟨((-440449 : Dyadic) * half ^ 19),
        ((180185 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word19Step26 :
    word19Chunk26.foldl (fun acc a => a.applyPacked acc)
      word19State26 = word19State27 := by decide +kernel

private def word19Chunk27 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word19State28 : PackedMat2 :=
    ⟨⟨⟨((480911 : Dyadic) * half ^ 20),
        ((5515 : Dyadic) * half ^ 21)⟩,
       ⟨((116951 : Dyadic) * half ^ 19),
        ((-357461 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-452233 : Dyadic) * half ^ 20),
        ((-118177 : Dyadic) * half ^ 20)⟩,
       ⟨((-565963 : Dyadic) * half ^ 20),
        ((-101919 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((134435 : Dyadic) * half ^ 21),
        ((-56865 : Dyadic) * half ^ 20)⟩,
       ⟨((-338273 : Dyadic) * half ^ 21),
        ((-254549 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((720437 : Dyadic) * half ^ 21),
        ((247009 : Dyadic) * half ^ 21)⟩,
       ⟨((709407 : Dyadic) * half ^ 21),
        ((-714813 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word19Step27 :
    word19Chunk27.foldl (fun acc a => a.applyPacked acc)
      word19State27 = word19State28 := by decide +kernel

private def word19Chunk28 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word19State29 : PackedMat2 :=
    ⟨⟨⟨((-1841115 : Dyadic) * half ^ 22),
        ((854497 : Dyadic) * half ^ 22)⟩,
       ⟨((-1119855 : Dyadic) * half ^ 22),
        ((74931 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((1434153 : Dyadic) * half ^ 22),
        ((1166925 : Dyadic) * half ^ 22)⟩,
       ⟨((-1072635 : Dyadic) * half ^ 22),
        ((-579073 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((2325071 : Dyadic) * half ^ 22),
        ((626697 : Dyadic) * half ^ 21)⟩,
       ⟨((-8779 : Dyadic) * half ^ 22),
        ((-180759 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((344399 : Dyadic) * half ^ 22),
        ((180315 : Dyadic) * half ^ 21)⟩,
       ⟨((2053393 : Dyadic) * half ^ 22),
        ((-1480485 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word19Step28 :
    word19Chunk28.foldl (fun acc a => a.applyPacked acc)
      word19State28 = word19State29 := by decide +kernel

private def word19Chunk29 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word19State30 : PackedMat2 :=
    ⟨⟨⟨((2131501 : Dyadic) * half ^ 22),
        ((-936543 : Dyadic) * half ^ 22)⟩,
       ⟨((12729 : Dyadic) * half ^ 16),
        ((223197 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((327975 : Dyadic) * half ^ 19),
        ((868901 : Dyadic) * half ^ 22)⟩,
       ⟨((-1000997 : Dyadic) * half ^ 22),
        ((646593 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-1000997 : Dyadic) * half ^ 22),
        ((646593 : Dyadic) * half ^ 22)⟩,
       ⟨((327975 : Dyadic) * half ^ 19),
        ((868901 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-12729 : Dyadic) * half ^ 16),
        ((-223197 : Dyadic) * half ^ 21)⟩,
       ⟨((-2131501 : Dyadic) * half ^ 22),
        ((936543 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word19Step29 :
    word19Chunk29.foldl (fun acc a => a.applyPacked acc)
      word19State29 = word19State30 := by decide +kernel

private def word19Chunk30 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word19State31 : PackedMat2 :=
    ⟨⟨⟨((-5330091 : Dyadic) * half ^ 23),
        ((3590329 : Dyadic) * half ^ 24)⟩,
       ⟨((26957 : Dyadic) * half ^ 16),
        ((1918085 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-2215151 : Dyadic) * half ^ 23),
        ((-298979 : Dyadic) * half ^ 24)⟩,
       ⟨((1504395 : Dyadic) * half ^ 22),
        ((3940505 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-1820763 : Dyadic) * half ^ 23),
        ((-793639 : Dyadic) * half ^ 24)⟩,
       ⟨((1059871 : Dyadic) * half ^ 22),
        ((5223941 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((2754207 : Dyadic) * half ^ 23),
        ((-1879595 : Dyadic) * half ^ 24)⟩,
       ⟨((418061 : Dyadic) * half ^ 22),
        ((-8780587 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word19Step30 :
    word19Chunk30.foldl (fun acc a => a.applyPacked acc)
      word19State30 = word19State31 := by decide +kernel

private def word19Chunk31 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word19State32 : PackedMat2 :=
    ⟨⟨⟨((-1037659 : Dyadic) * half ^ 23),
        ((-6438623 : Dyadic) * half ^ 24)⟩,
       ⟨((-1605199 : Dyadic) * half ^ 22),
        ((204713 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((1011161 : Dyadic) * half ^ 23),
        ((-747571 : Dyadic) * half ^ 21)⟩,
       ⟨((2587925 : Dyadic) * half ^ 23),
        ((3818343 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((1011161 : Dyadic) * half ^ 23),
        ((-747571 : Dyadic) * half ^ 21)⟩,
       ⟨((-2587925 : Dyadic) * half ^ 23),
        ((-3818343 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((1037659 : Dyadic) * half ^ 23),
        ((6438623 : Dyadic) * half ^ 24)⟩,
       ⟨((-1605199 : Dyadic) * half ^ 22),
        ((204713 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word19Step31 :
    word19Chunk31.foldl (fun acc a => a.applyPacked acc)
      word19State31 = word19State32 := by decide +kernel

private def word19Chunk32 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word19State33 : PackedMat2 :=
    ⟨⟨⟨((-840059 : Dyadic) * half ^ 25),
        ((-498845 : Dyadic) * half ^ 21)⟩,
       ⟨((6393767 : Dyadic) * half ^ 25),
        ((-1517611 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-7391071 : Dyadic) * half ^ 25),
        ((-789903 : Dyadic) * half ^ 21)⟩,
       ⟨((23417879 : Dyadic) * half ^ 25),
        ((-3860869 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((23417879 : Dyadic) * half ^ 25),
        ((-3860869 : Dyadic) * half ^ 25)⟩,
       ⟨((-7391071 : Dyadic) * half ^ 25),
        ((-789903 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-6393767 : Dyadic) * half ^ 25),
        ((1517611 : Dyadic) * half ^ 25)⟩,
       ⟨((840059 : Dyadic) * half ^ 25),
        ((498845 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word19Step32 :
    word19Chunk32.foldl (fun acc a => a.applyPacked acc)
      word19State32 = word19State33 := by decide +kernel

private def word19Chunk33 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word19State34 : PackedMat2 :=
    ⟨⟨⟨((-14258467 : Dyadic) * half ^ 25),
        ((6947811 : Dyadic) * half ^ 25)⟩,
       ⟨((-3188817 : Dyadic) * half ^ 23),
        ((-9545765 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-1913157 : Dyadic) * half ^ 23),
        ((-420503 : Dyadic) * half ^ 24)⟩,
       ⟨((-20422179 : Dyadic) * half ^ 25),
        ((1426369 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-585363 : Dyadic) * half ^ 25),
        ((28074807 : Dyadic) * half ^ 26)⟩,
       ⟨((2267375 : Dyadic) * half ^ 25),
        ((-12769551 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-1298977 : Dyadic) * half ^ 24),
        ((-27013735 : Dyadic) * half ^ 26)⟩,
       ⟨((2061697 : Dyadic) * half ^ 22),
        ((-1503199 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word19Step33 :
    word19Chunk33.foldl (fun acc a => a.applyPacked acc)
      word19State33 = word19State34 := by decide +kernel

private def word19Chunk34 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word19State35 : PackedMat2 :=
    ⟨⟨⟨((27236253 : Dyadic) * half ^ 26),
        ((-37500211 : Dyadic) * half ^ 27)⟩,
       ⟨((-8904343 : Dyadic) * half ^ 24),
        ((1154637 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((21338121 : Dyadic) * half ^ 26),
        ((8855741 : Dyadic) * half ^ 27)⟩,
       ⟨((-10646733 : Dyadic) * half ^ 25),
        ((-41023171 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((21338121 : Dyadic) * half ^ 26),
        ((8855741 : Dyadic) * half ^ 27)⟩,
       ⟨((10646733 : Dyadic) * half ^ 25),
        ((41023171 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-27236253 : Dyadic) * half ^ 26),
        ((37500211 : Dyadic) * half ^ 27)⟩,
       ⟨((-8904343 : Dyadic) * half ^ 24),
        ((1154637 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word19Step34 :
    word19Chunk34.foldl (fun acc a => a.applyPacked acc)
      word19State34 = word19State35 := by decide +kernel

private def word19Chunk35 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word19State36 : PackedMat2 :=
    ⟨⟨⟨((9727641 : Dyadic) * half ^ 26),
        ((31086805 : Dyadic) * half ^ 27)⟩,
       ⟨((12421089 : Dyadic) * half ^ 25),
        ((-8463973 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((1456477 : Dyadic) * half ^ 26),
        ((15149953 : Dyadic) * half ^ 25)⟩,
       ⟨((-27651211 : Dyadic) * half ^ 26),
        ((-16288277 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-76888089 : Dyadic) * half ^ 27),
        ((-3638461 : Dyadic) * half ^ 24)⟩,
       ⟨((44311535 : Dyadic) * half ^ 27),
        ((-13097367 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((64942697 : Dyadic) * half ^ 27),
        ((-15114537 : Dyadic) * half ^ 27)⟩,
       ⟨((2769087 : Dyadic) * half ^ 27),
        ((-34569819 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word19Step35 :
    word19Chunk35.foldl (fun acc a => a.applyPacked acc)
      word19State35 = word19State36 := by decide +kernel

private def word19Chunk36 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word19State37 : PackedMat2 :=
    ⟨⟨⟨((89377343 : Dyadic) * half ^ 28),
        ((41209431 : Dyadic) * half ^ 27)⟩,
       ⟨((-92568037 : Dyadic) * half ^ 28),
        ((106965895 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((111559349 : Dyadic) * half ^ 28),
        ((4289471 : Dyadic) * half ^ 25)⟩,
       ⟨((-32432687 : Dyadic) * half ^ 28),
        ((39867209 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((32432687 : Dyadic) * half ^ 28),
        ((-39867209 : Dyadic) * half ^ 28)⟩,
       ⟨((-111559349 : Dyadic) * half ^ 28),
        ((-4289471 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-92568037 : Dyadic) * half ^ 28),
        ((106965895 : Dyadic) * half ^ 28)⟩,
       ⟨((89377343 : Dyadic) * half ^ 28),
        ((41209431 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word19Step36 :
    word19Chunk36.foldl (fun acc a => a.applyPacked acc)
      word19State36 = word19State37 := by decide +kernel

private def word19Chunk37 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word19State38 : PackedMat2 :=
    ⟨⟨⟨((112486537 : Dyadic) * half ^ 28),
        ((22278657 : Dyadic) * half ^ 29)⟩,
       ⟨((207434241 : Dyadic) * half ^ 28),
        ((24166593 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((48408065 : Dyadic) * half ^ 27),
        ((-35273755 : Dyadic) * half ^ 29)⟩,
       ⟨((12739553 : Dyadic) * half ^ 26),
        ((-80535781 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-452381 : Dyadic) * half ^ 21),
        ((73887171 : Dyadic) * half ^ 28)⟩,
       ⟨((22631013 : Dyadic) * half ^ 28),
        ((22928959 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-23222625 : Dyadic) * half ^ 28),
        ((-159960389 : Dyadic) * half ^ 28)⟩,
       ⟨((29499 : Dyadic) * half ^ 23),
        ((11868463 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word19Step37 :
    word19Chunk37.foldl (fun acc a => a.applyPacked acc)
      word19State37 = word19State38 := by decide +kernel

private def word19Chunk38 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word19State39 : PackedMat2 :=
    ⟨⟨⟨((127542799 : Dyadic) * half ^ 28),
        ((-225836035 : Dyadic) * half ^ 30)⟩,
       ⟨((13664135 : Dyadic) * half ^ 25),
        ((49829551 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-264378897 : Dyadic) * half ^ 29),
        ((-268738735 : Dyadic) * half ^ 30)⟩,
       ⟨((-93495225 : Dyadic) * half ^ 29),
        ((260284669 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((93495225 : Dyadic) * half ^ 29),
        ((-260284669 : Dyadic) * half ^ 30)⟩,
       ⟨((264378897 : Dyadic) * half ^ 29),
        ((268738735 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((13664135 : Dyadic) * half ^ 25),
        ((49829551 : Dyadic) * half ^ 30)⟩,
       ⟨((127542799 : Dyadic) * half ^ 28),
        ((-225836035 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word19Step38 :
    word19Chunk38.foldl (fun acc a => a.applyPacked acc)
      word19State38 = word19State39 := by decide +kernel

private def word19Chunk39 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word19State40 : PackedMat2 :=
    ⟨⟨⟨((-315922701 : Dyadic) * half ^ 30),
        ((-70692563 : Dyadic) * half ^ 31)⟩,
       ⟨((22032493 : Dyadic) * half ^ 25),
        ((-472750591 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-430196303 : Dyadic) * half ^ 30),
        ((-661061491 : Dyadic) * half ^ 31)⟩,
       ⟨((31315935 : Dyadic) * half ^ 28),
        ((212259157 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-430196303 : Dyadic) * half ^ 30),
        ((-661061491 : Dyadic) * half ^ 31)⟩,
       ⟨((-31315935 : Dyadic) * half ^ 28),
        ((-212259157 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((315922701 : Dyadic) * half ^ 30),
        ((70692563 : Dyadic) * half ^ 31)⟩,
       ⟨((22032493 : Dyadic) * half ^ 25),
        ((-472750591 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word19Step39 :
    word19Chunk39.foldl (fun acc a => a.applyPacked acc)
      word19State39 = word19State40 := by decide +kernel

private def word19Chunk40 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word19State41 : PackedMat2 :=
    ⟨⟨⟨((-45599173 : Dyadic) * half ^ 31),
        ((-1736960271 : Dyadic) * half ^ 32)⟩,
       ⟨((-129194775 : Dyadic) * half ^ 30),
        ((-1596067499 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((99143599 : Dyadic) * half ^ 31),
        ((-712290543 : Dyadic) * half ^ 32)⟩,
       ⟨((299516643 : Dyadic) * half ^ 29),
        ((-351392883 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((531841713 : Dyadic) * half ^ 31),
        ((-1297210171 : Dyadic) * half ^ 32)⟩,
       ⟨((90224415 : Dyadic) * half ^ 30),
        ((1098922973 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1666513885 : Dyadic) * half ^ 31),
        ((-303988723 : Dyadic) * half ^ 32)⟩,
       ⟨((-35223193 : Dyadic) * half ^ 30),
        ((212790377 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word19Step40 :
    word19Chunk40.foldl (fun acc a => a.applyPacked acc)
      word19State40 = word19State41 := by decide +kernel

private def word19Chunk41 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word19State42 : PackedMat2 :=
    ⟨⟨⟨((-689713561 : Dyadic) * half ^ 31),
        ((396289305 : Dyadic) * half ^ 32)⟩,
       ⟨((-709933311 : Dyadic) * half ^ 30),
        ((-237793311 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-932378971 : Dyadic) * half ^ 31),
        ((71457511 : Dyadic) * half ^ 28)⟩,
       ⟨((-255319417 : Dyadic) * half ^ 31),
        ((43887551 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-932378971 : Dyadic) * half ^ 31),
        ((71457511 : Dyadic) * half ^ 28)⟩,
       ⟨((255319417 : Dyadic) * half ^ 31),
        ((-43887551 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((689713561 : Dyadic) * half ^ 31),
        ((-396289305 : Dyadic) * half ^ 32)⟩,
       ⟨((-709933311 : Dyadic) * half ^ 30),
        ((-237793311 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word19Step41 :
    word19Chunk41.foldl (fun acc a => a.applyPacked acc)
      word19State41 = word19State42 := by decide +kernel

private def word19Chunk42 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word19State43 : PackedMat2 :=
    ⟨⟨⟨((72338699 : Dyadic) * half ^ 32),
        ((766901303 : Dyadic) * half ^ 32)⟩,
       ⟨((-100605925 : Dyadic) * half ^ 29),
        ((-2667989289 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((395284391 : Dyadic) * half ^ 31),
        ((1139019257 : Dyadic) * half ^ 33)⟩,
       ⟨((41445661 : Dyadic) * half ^ 28),
        ((-297711973 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-395284391 : Dyadic) * half ^ 31),
        ((-1139019257 : Dyadic) * half ^ 33)⟩,
       ⟨((41445661 : Dyadic) * half ^ 28),
        ((-297711973 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((72338699 : Dyadic) * half ^ 32),
        ((766901303 : Dyadic) * half ^ 32)⟩,
       ⟨((100605925 : Dyadic) * half ^ 29),
        ((2667989289 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word19Step42 :
    word19Chunk42.foldl (fun acc a => a.applyPacked acc)
      word19State42 = word19State43 := by decide +kernel

private def word19Chunk43 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word19State44 : PackedMat2 :=
    ⟨⟨⟨((2201323079 : Dyadic) * half ^ 34),
        ((4608302451 : Dyadic) * half ^ 34)⟩,
       ⟨((-6993070449 : Dyadic) * half ^ 34),
        ((1376009393 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-3514173297 : Dyadic) * half ^ 34),
        ((5822307577 : Dyadic) * half ^ 34)⟩,
       ⟨((-4604706909 : Dyadic) * half ^ 34),
        ((-3209899903 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((12242107383 : Dyadic) * half ^ 34),
        ((272633403 : Dyadic) * half ^ 33)⟩,
       ⟨((597492229 : Dyadic) * half ^ 34),
        ((4059440103 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1856283665 : Dyadic) * half ^ 34),
        ((-1149299191 : Dyadic) * half ^ 32)⟩,
       ⟨((7360321237 : Dyadic) * half ^ 34),
        ((-2395873685 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word19Step43 :
    word19Chunk43.foldl (fun acc a => a.applyPacked acc)
      word19State43 = word19State44 := by decide +kernel

private def word19Chunk44 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word19State45 : PackedMat2 :=
    ⟨⟨⟨((2465481081 : Dyadic) * half ^ 32),
        ((-1593250821 : Dyadic) * half ^ 33)⟩,
       ⟨((1550326871 : Dyadic) * half ^ 34),
        ((-2201141951 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((9225322571 : Dyadic) * half ^ 34),
        ((29351285 : Dyadic) * half ^ 27)⟩,
       ⟨((-2340175615 : Dyadic) * half ^ 33),
        ((-767209059 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-2340175615 : Dyadic) * half ^ 33),
        ((-767209059 : Dyadic) * half ^ 34)⟩,
       ⟨((9225322571 : Dyadic) * half ^ 34),
        ((29351285 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-1550326871 : Dyadic) * half ^ 34),
        ((2201141951 : Dyadic) * half ^ 33)⟩,
       ⟨((-2465481081 : Dyadic) * half ^ 32),
        ((1593250821 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word19Step44 :
    word19Chunk44.foldl (fun acc a => a.applyPacked acc)
      word19State44 = word19State45 := by decide +kernel

private def word19Chunk45 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word19State46 : PackedMat2 :=
    ⟨⟨⟨((-4251255331 : Dyadic) * half ^ 34),
        ((6329886755 : Dyadic) * half ^ 36)⟩,
       ⟨((5516117705 : Dyadic) * half ^ 35),
        ((-25023586659 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((13378676773 : Dyadic) * half ^ 34),
        ((7220315135 : Dyadic) * half ^ 36)⟩,
       ⟨((-1529529069 : Dyadic) * half ^ 35),
        ((878404845 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-13378676773 : Dyadic) * half ^ 34),
        ((-7220315135 : Dyadic) * half ^ 36)⟩,
       ⟨((-1529529069 : Dyadic) * half ^ 35),
        ((878404845 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-4251255331 : Dyadic) * half ^ 34),
        ((6329886755 : Dyadic) * half ^ 36)⟩,
       ⟨((-5516117705 : Dyadic) * half ^ 35),
        ((25023586659 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word19Step45 :
    word19Chunk45.foldl (fun acc a => a.applyPacked acc)
      word19State45 = word19State46 := by decide +kernel

private def word19Chunk46 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word19State47 : PackedMat2 :=
    ⟨⟨⟨((-5392181007 : Dyadic) * half ^ 35),
        ((-70019100825 : Dyadic) * half ^ 37)⟩,
       ⟨((20056417077 : Dyadic) * half ^ 36),
        ((-49946299063 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-508255471 : Dyadic) * half ^ 35),
        ((9766722147 : Dyadic) * half ^ 37)⟩,
       ⟨((19148442775 : Dyadic) * half ^ 36),
        ((13398502281 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((5791306107 : Dyadic) * half ^ 35),
        ((18131931833 : Dyadic) * half ^ 37)⟩,
       ⟨((-1815890067 : Dyadic) * half ^ 36),
        ((-20164953717 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((7497837493 : Dyadic) * half ^ 33),
        ((-9272055063 : Dyadic) * half ^ 37)⟩,
       ⟨((10036400881 : Dyadic) * half ^ 36),
        ((30840779091 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word19Step46 :
    word19Chunk46.foldl (fun acc a => a.applyPacked acc)
      word19State46 = word19State47 := by decide +kernel

private def word19Chunk47 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word19State48 : PackedMat2 :=
    ⟨⟨⟨((-102406091249 : Dyadic) * half ^ 37),
        ((-7233169633 : Dyadic) * half ^ 36)⟩,
       ⟨((21124346011 : Dyadic) * half ^ 37),
        ((-8619958385 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-68565041447 : Dyadic) * half ^ 37),
        ((11886103381 : Dyadic) * half ^ 37)⟩,
       ⟨((9911421019 : Dyadic) * half ^ 37),
        ((6244699527 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((68565041447 : Dyadic) * half ^ 37),
        ((-11886103381 : Dyadic) * half ^ 37)⟩,
       ⟨((9911421019 : Dyadic) * half ^ 37),
        ((6244699527 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-102406091249 : Dyadic) * half ^ 37),
        ((-7233169633 : Dyadic) * half ^ 36)⟩,
       ⟨((-21124346011 : Dyadic) * half ^ 37),
        ((8619958385 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word19Step47 :
    word19Chunk47.foldl (fun acc a => a.applyPacked acc)
      word19State47 = word19State48 := by decide +kernel

private def word19Chunk48 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word19State49 : PackedMat2 :=
    ⟨⟨⟨((-182388031085 : Dyadic) * half ^ 38),
        ((-1679504867 : Dyadic) * half ^ 34)⟩,
       ⟨((-32730198065 : Dyadic) * half ^ 38),
        ((932942443 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-39221313547 : Dyadic) * half ^ 38),
        ((-14541309975 : Dyadic) * half ^ 36)⟩,
       ⟨((-166701115531 : Dyadic) * half ^ 38),
        ((42902694875 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((166701115531 : Dyadic) * half ^ 38),
        ((-42902694875 : Dyadic) * half ^ 38)⟩,
       ⟨((39221313547 : Dyadic) * half ^ 38),
        ((14541309975 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-32730198065 : Dyadic) * half ^ 38),
        ((932942443 : Dyadic) * half ^ 38)⟩,
       ⟨((-182388031085 : Dyadic) * half ^ 38),
        ((-1679504867 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word19Step48 :
    word19Chunk48.foldl (fun acc a => a.applyPacked acc)
      word19State48 = word19State49 := by decide +kernel

private def word19Chunk49 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word19State50 : PackedMat2 :=
    ⟨⟨⟨((-76238557669 : Dyadic) * half ^ 39),
        ((9774222543 : Dyadic) * half ^ 38)⟩,
       ⟨((16443042117 : Dyadic) * half ^ 39),
        ((-114705995799 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-353558016321 : Dyadic) * half ^ 39),
        ((55062259749 : Dyadic) * half ^ 38)⟩,
       ⟨((-238868680299 : Dyadic) * half ^ 39),
        ((-177134429625 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-287258949123 : Dyadic) * half ^ 39),
        ((57344668011 : Dyadic) * half ^ 39)⟩,
       ⟨((-67009910127 : Dyadic) * half ^ 39),
        ((-148106674155 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((134254440885 : Dyadic) * half ^ 39),
        ((-46340799893 : Dyadic) * half ^ 39)⟩,
       ⟨((95157550713 : Dyadic) * half ^ 39),
        ((1868609861 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word19Step49 :
    word19Chunk49.foldl (fun acc a => a.applyPacked acc)
      word19State49 = word19State50 := by decide +kernel

private def word19Chunk50 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word19State51 : PackedMat2 :=
    ⟨⟨⟨((-46604496343 : Dyadic) * half ^ 39),
        ((106161418831 : Dyadic) * half ^ 40)⟩,
       ⟨((-127424530313 : Dyadic) * half ^ 39),
        ((-191856665201 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((253485021657 : Dyadic) * half ^ 38),
        ((-36675557777 : Dyadic) * half ^ 40)⟩,
       ⟨((-21635423859 : Dyadic) * half ^ 38),
        ((20943358589 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((21635423859 : Dyadic) * half ^ 38),
        ((-20943358589 : Dyadic) * half ^ 40)⟩,
       ⟨((-253485021657 : Dyadic) * half ^ 38),
        ((36675557777 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-127424530313 : Dyadic) * half ^ 39),
        ((-191856665201 : Dyadic) * half ^ 40)⟩,
       ⟨((-46604496343 : Dyadic) * half ^ 39),
        ((106161418831 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word19Step50 :
    word19Chunk50.foldl (fun acc a => a.applyPacked acc)
      word19State50 = word19State51 := by decide +kernel

private def word19Chunk51 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word19State52 : PackedMat2 :=
    ⟨⟨⟨((204776490961 : Dyadic) * half ^ 40),
        ((648888563547 : Dyadic) * half ^ 41)⟩,
       ⟨((-115297530975 : Dyadic) * half ^ 39),
        ((-612386837391 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-142413752075 : Dyadic) * half ^ 40),
        ((912176694069 : Dyadic) * half ^ 41)⟩,
       ⟨((242532889359 : Dyadic) * half ^ 39),
        ((-297246279869 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-142413752075 : Dyadic) * half ^ 40),
        ((912176694069 : Dyadic) * half ^ 41)⟩,
       ⟨((-242532889359 : Dyadic) * half ^ 39),
        ((297246279869 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-204776490961 : Dyadic) * half ^ 40),
        ((-648888563547 : Dyadic) * half ^ 41)⟩,
       ⟨((-115297530975 : Dyadic) * half ^ 39),
        ((-612386837391 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word19Step51 :
    word19Chunk51.foldl (fun acc a => a.applyPacked acc)
      word19State51 = word19State52 := by decide +kernel

private def word19Chunk52 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word19State53 : PackedMat2 :=
    ⟨⟨⟨((173573254513 : Dyadic) * half ^ 41),
        ((1953553604915 : Dyadic) * half ^ 42)⟩,
       ⟨((-117979345881 : Dyadic) * half ^ 40),
        ((333682805255 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((434275366485 : Dyadic) * half ^ 41),
        ((-614144936293 : Dyadic) * half ^ 42)⟩,
       ⟨((-724251937 : Dyadic) * half ^ 39),
        ((-2194926267865 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1404535602079 : Dyadic) * half ^ 41),
        ((-431378358737 : Dyadic) * half ^ 42)⟩,
       ⟨((-395195332893 : Dyadic) * half ^ 40),
        ((-437172374233 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1143618205085 : Dyadic) * half ^ 41),
        ((-62385437249 : Dyadic) * half ^ 42)⟩,
       ⟨((404967699915 : Dyadic) * half ^ 40),
        ((409531946275 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word19Step52 :
    word19Chunk52.foldl (fun acc a => a.applyPacked acc)
      word19State52 = word19State53 := by decide +kernel

private def word19Chunk53 : List Letter := [.t, .h, .s]
private def word19State54 : PackedMat2 :=
    ⟨⟨⟨((1037119968195 : Dyadic) * half ^ 40),
        ((176470262261 : Dyadic) * half ^ 42)⟩,
       ⟨((236956935387 : Dyadic) * half ^ 40),
        ((-670234058247 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-140231065519 : Dyadic) * half ^ 41),
        ((198316674723 : Dyadic) * half ^ 42)⟩,
       ⟨((-120686331475 : Dyadic) * half ^ 41),
        ((170676246765 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((140231065519 : Dyadic) * half ^ 41),
        ((-198316674723 : Dyadic) * half ^ 42)⟩,
       ⟨((-120686331475 : Dyadic) * half ^ 41),
        ((170676246765 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1037119968195 : Dyadic) * half ^ 40),
        ((176470262261 : Dyadic) * half ^ 42)⟩,
       ⟨((-236956935387 : Dyadic) * half ^ 40),
        ((670234058247 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word19Step53 :
    word19Chunk53.foldl (fun acc a => a.applyPacked acc)
      word19State53 = word19State54 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word19_check : check word19 19 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word19 = word19State54.toMatrix := by
    unfold evalRingPacked
    change ((
      word19Chunk0 ++ word19Chunk1 ++ word19Chunk2 ++ word19Chunk3 ++
      word19Chunk4 ++ word19Chunk5 ++ word19Chunk6 ++ word19Chunk7 ++
      word19Chunk8 ++ word19Chunk9 ++ word19Chunk10 ++ word19Chunk11 ++
      word19Chunk12 ++ word19Chunk13 ++ word19Chunk14 ++ word19Chunk15 ++
      word19Chunk16 ++ word19Chunk17 ++ word19Chunk18 ++ word19Chunk19 ++
      word19Chunk20 ++ word19Chunk21 ++ word19Chunk22 ++ word19Chunk23 ++
      word19Chunk24 ++ word19Chunk25 ++ word19Chunk26 ++ word19Chunk27 ++
      word19Chunk28 ++ word19Chunk29 ++ word19Chunk30 ++ word19Chunk31 ++
      word19Chunk32 ++ word19Chunk33 ++ word19Chunk34 ++ word19Chunk35 ++
      word19Chunk36 ++ word19Chunk37 ++ word19Chunk38 ++ word19Chunk39 ++
      word19Chunk40 ++ word19Chunk41 ++ word19Chunk42 ++ word19Chunk43 ++
      word19Chunk44 ++ word19Chunk45 ++ word19Chunk46 ++ word19Chunk47 ++
      word19Chunk48 ++ word19Chunk49 ++ word19Chunk50 ++ word19Chunk51 ++
      word19Chunk52 ++ word19Chunk53
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word19Step0, word19Step1, word19Step2, word19Step3, word19Step4,
      word19Step5, word19Step6, word19Step7, word19Step8, word19Step9,
      word19Step10, word19Step11, word19Step12, word19Step13, word19Step14,
      word19Step15, word19Step16, word19Step17, word19Step18, word19Step19,
      word19Step20, word19Step21, word19Step22, word19Step23, word19Step24,
      word19Step25, word19Step26, word19Step27, word19Step28, word19Step29,
      word19Step30, word19Step31, word19Step32, word19Step33, word19Step34,
      word19Step35, word19Step36, word19Step37, word19Step38, word19Step39,
      word19Step40, word19Step41, word19Step42, word19Step43, word19Step44,
      word19Step45, word19Step46, word19Step47, word19Step48, word19Step49,
      word19Step50, word19Step51, word19Step52, word19Step53]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
