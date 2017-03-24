(**
 Consequences of classical logic and setoid choice.

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
From Coq.Logic Require Import ChoiceFacts.
From Coq.Logic Require Export Classical.
From Coq.Classes Require Import Equivalence.
From misc Require Zorn CantorBernsteinSchroeder.

(** * Reification principle. *)

(** Taken from Coq trunk; this will be in the standard library. *)

Definition SetoidFunctionalChoice_on A B :=
  forall R : A -> A -> Prop,
  forall T : A -> B -> Prop,
  Equivalence R ->
  (forall x x' y, R x x' -> T x y -> T x' y) ->
  (forall x, exists y, T x y) ->
  exists f : A -> B, forall x : A, T x (f x) /\
    (forall x' : A, R x x' -> f x = f x').
Notation SetoidFunctionalChoice := (forall A B, SetoidFunctionalChoice_on A B).

(** * The choice axiom. *)

Axiom setoid_choice: SetoidFunctionalChoice.

(** * Derived results. *)

Definition gen_setoid_rel_choice A B :=
  Zorn.gen_setoid_fun_choice_imp_gen_setoid_rel_choice A B (setoid_choice A B).
Definition zorns_lemma {A} R {preR} :=
  Zorn.zorns_lemma classic gen_setoid_rel_choice (A:=A) R (preR := preR).
Definition well_ordering_theorem {A} eqA {equA} :=
  Zorn.well_ordering_theorem classic gen_setoid_rel_choice
    (A:=A) eqA (equA := equA).
Definition setoid_fun_rel_reification A B :=
  CantorBernsteinSchroeder.setoid_fun_choice_imp_setoid_fun_rel_reification A B
    (setoid_choice A B).
Definition cantor_bernstein_schröder {A} Ae {Aequ: @Equivalence A Ae}
  {B} Be {Bequ: @Equivalence B Be} f f_proper f_inj g g_proper g_inj :=
  @CantorBernsteinSchroeder.cantor_bernstein_schröder A Ae Aequ B Be Bequ
    f f_proper f_inj g g_proper g_inj classic (setoid_fun_rel_reification A B).
