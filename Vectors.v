(**
 Helper library: vectors.

 This is a wrapper around the [Vector] module from the standard library.
 
 © 2017 Johannes Kloos

 This library requires Coq 8.6. *)
 (*
 This library is free software; you can redistribute it and/or
 modify it under the terms of the GNU Lesser General Public
 License as published by the Free Software Foundation; either
 version 2.1 of the License, or (at your option) any later version.

 This library is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 Lesser General Public License for more details.

 You should have received a copy of the GNU Lesser General Public
 License along with this library; if not, write to the Free Software
 Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 
 *)
From Coq.Vectors Require Fin Vector.
From Coq Require Import Utf8.

Module Import VectorNotations.
  Infix "^" := Vector.t: type_scope.
  Notation "[# ]" := (Vector.nil _).
  Notation "x ::: v" := (Vector.cons _ x _ v) (at level 50).
  Notation "[# x1 ; .. ; xn ]" := (x1 ::: .. (xn ::: [# ]) ..).
  Notation "#Forall" := Vector.Forall.
  Notation "#Exists" := Vector.Exists.
  Notation "#In" := Vector.In.
End VectorNotations.
Hint Constructors Vector.Forall Vector.Exists Vector.In.
Lemma vector_map_map {A B C} f (g: B → C) {n} (v: A^n):
  Vector.map g (Vector.map f v) = Vector.map (λ x, g (f x)) v.
Proof. induction v; cbn; f_equal; auto. Qed.
Lemma vector_map_Forall {A B} (f₁ f₂: A → B) {n} (v: A^n):
  Vector.Forall (λ x, f₁ x = f₂ x) v → Vector.map f₁ v = Vector.map f₂ v.
Proof. induction 1; cbn; f_equal; auto. Qed.
Lemma vector_In_invert {A n} x (v: A^n): #In x v → match v return Prop with
  | y ::: v => x = y ∨ #In x v
  | [#] => False
  end.
Proof. destruct 1; auto. Qed.

Lemma vector_Forall_forall {A} (P: A → Prop) {n} (v: A^n):
  Vector.Forall P v ↔ ∀ x, Vector.In x v → P x.
Proof.
  split.
  - induction 1; intros y [ ]%vector_In_invert; subst; auto.
  - induction v as [|n x v IH]; constructor; auto.
Qed.

Lemma vector_map_ext {A B} (f₁ f₂: A → B) (ext: ∀ x, f₁ x = f₂ x) {n} (v: A^n):
  Vector.map f₁ v = Vector.map f₂ v.
Proof. apply vector_map_Forall, vector_Forall_forall; auto. Qed.

Lemma vector_Forall_invert {A} (P: A → Prop) {n} (v: A^n): #Forall P v →
  match v return Prop with
  | [#] => True
  | x:::v => P x ∧ #Forall P v
  end.
Proof. destruct 1; auto. Qed.

Lemma vector_Forall_cons {A} (P: A → Prop) {n} x (v: A^n):
  #Forall P (x:::v) ↔ P x ∧ #Forall P v.
Proof.
  split.
  - now intros ?%vector_Forall_invert.
  - intros [??]; auto.
Qed.

Lemma vector_Forall_impl {A} (P Q: A → Prop) {n} (v: A^n) (imp: ∀ x, P x → Q x):
  #Forall P v → #Forall Q v.
Proof. induction 1; auto. Qed.

Lemma vector_Forall_impl' {A} (P Q: A → Prop) {n} (v: A^n):
  #Forall P v → #Forall (λ x, P x → Q x) v → #Forall Q v.
Proof.
  induction 1; auto.
  intros [implx IH]%vector_Forall_invert.
  auto.
Qed.

Lemma vector_map_id {A n} (v: A^n): Vector.map id v = v.
Proof. now induction v; cbn; f_equal. Qed.