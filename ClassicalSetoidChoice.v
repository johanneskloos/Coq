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
From Coq.Logic Require Export SetoidChoice.
From Coq.Classes Require Import Equivalence.
From misc Require Import MoreChoice ChoiceResults.
From misc Require Zorn CantorBernsteinSchroeder.

(** * Derived results. *)

Definition gen_setoid_rel_choice A B :=
  gen_setoid_fun_choice_imp_gen_setoid_rel_choice A B (setoid_choice A B).
Definition zorns_lemma {A} R {preR} :=
  Zorn.zorns_lemma classic gen_setoid_rel_choice (A:=A) R (preR := preR).
Definition well_ordering_theorem {A} eqA {equA} :=
  Zorn.well_ordering_theorem classic gen_setoid_rel_choice
    (A:=A) eqA (equA := equA).
Definition setoid_fun_rel_reification A B :=
  setoid_fun_choice_imp_setoid_fun_rel_reification A B
    (setoid_choice A B).
Definition cantor_bernstein_schröder {A} Ae {Aequ: @Equivalence A Ae}
  {B} Be {Bequ: @Equivalence B Be} f f_proper f_inj g g_proper g_inj :=
  @CantorBernsteinSchroeder.cantor_bernstein_schröder A Ae Aequ B Be Bequ
    f f_proper f_inj g g_proper g_inj classic (setoid_fun_rel_reification A B).
Definition dependent_zorn := dependent_zorn (@zorns_lemma).
Definition dependent_nonempty_zorn := dependent_nonempty_zorn classic (@zorns_lemma).
Notation Filter := Filter.
Notation ProperFilter := ProperFilter.
Notation Ultrafilter := Ultrafilter.
Definition ultrafilter {L} Lle := ultrafilter L Lle classic (@zorns_lemma).
Definition ultrafilter_prime {L} Lle {Lpre: PreOrder Lle} := ultrafilter_prime L Lle classic.
