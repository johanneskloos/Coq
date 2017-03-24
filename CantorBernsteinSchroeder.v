(**
 The Cantor-Bernstein-Schröder theorem.

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
From Coq.Relations Require Import Relations.
From Coq.Classes Require Import Equivalence Morphisms RelationClasses.
From Coq.Logic Require Import ChoiceFacts ClassicalFacts.

(** * Reification principle. *)
(** This functional reification principle is missing from the standard library.
  It follows easily from existing principles, e.g., AC_fun_repr+AC!.
  But since AC_fun_setoid = AC! + AC_fun_repr, we just derive it from
  AC_fun_setoid. *)
Definition SetoidFunctionalRelReification_on A B :=
  forall R : A -> A -> Prop,
  forall S : B -> B -> Prop,
  forall T : A -> B -> Prop,
  Equivalence R ->
  Equivalence S ->
  (forall x x' y y', R x x' -> S y y' -> T x y -> T x' y') ->
  (forall x, exists y, T x y) ->
  (forall x y y', T x y -> T x y' -> S y y') ->
  exists f : A -> B,
    forall x : A, T x (f x) /\ (forall x' : A, R x x' -> S (f x) (f x')).
(** Taken from Coq trunk; this will be in the standard library. *)
Definition SetoidFunctionalChoice_on A B :=
  forall R : A -> A -> Prop,
  forall T : A -> B -> Prop,
  Equivalence R ->
  (forall x x' y, R x x' -> T x y -> T x' y) ->
  (forall x, exists y, T x y) ->
  exists f : A -> B, forall x : A, T x (f x) /\
    (forall x' : A, R x x' -> f x = f x').
(** The reification principle follows from AC_fun_setoid. *)
Lemma setoid_fun_choice_imp_setoid_fun_rel_reification A B:
  SetoidFunctionalChoice_on A B -> SetoidFunctionalRelReification_on A B.
Proof.
  intros choice R S T Req Seq Tproper Tfull Tunique.
  destruct (choice R T) as [f Hf]; auto.
  { now intros * eqx; apply Tproper. }
  exists f.
  intros x; destruct (Hf x) as [x_good x_unique].
  split; trivial.
  now intros x' ->%x_unique.
Qed.

(** * The proof of Cantor-Bernstein-Schröder. *)
(** We keep things as constructive as possible. The relational part
  is partly fully constructive (partial injective function), but the\
  proof that the relation represents a bijection needs excluded middle.
  
  For the actual statement, we also need setoid functional relation
  reification. *)
Section CantorBernsteinSchroeder.
  (** Given two setoids... *)
  Context {A} (Ae: relation A) {Aequiv: Equivalence Ae}.
  Context {B} (Be: relation B) {Bequiv: Equivalence Be}.
  Local Infix "=A" := Ae (at level 70).
  Local Infix "=B" := Be (at level 70).
  (** ... and two injections from one to the other ... *)
  Context f (f_proper: Proper (Ae ==> Be) f).
  Context (f_inj: forall x y, f x =B f y -> x =A y).
  Context g (g_proper: Proper (Be ==> Ae) g).
  Context (g_inj: forall x y, g x =A g y -> x =B y).
  
  (** define a bijective relation between them. First, we define
   a sequence [C_i] of sets, where [C_0] is the complement of im g. *)
  Let C0 x := ~exists y, g y =A x.
  Local Instance C0_proper: Proper (Ae ==> iff) C0.
  Proof. unfold C0; solve_proper. Qed.
  
  (** C_{i+1} = (g ○ f)⁻¹(C_i) *)
  Let Csucc (C: A -> Prop) x :=
    exists x', C x' /\ x =A g (f x').
  Local Instance Csucc_proper: Proper ((Ae ==> iff) ==> Ae ==> iff) Csucc.
  Proof.
    unfold Csucc.
    intros C1 C2 eqC x1 x2 eqx.
    setoid_rewrite eqx.
    enough (forall x, C1 x <-> C2 x) as eqC' by now setoid_rewrite eqC'.
    now intro; apply eqC.
  Qed.
  
  Local Fixpoint Cn n := match n with
    | 0 => C0
    | S n => Csucc (Cn n)
    end.
  Local Instance Cn_proper n: Proper (Ae ==> iff) (Cn n).
  Proof.
    induction n; cbn; [apply _|].
    apply Csucc_proper, IHn.
  Qed.
  
  (** C = ⋃ { C_i | i ≥ 0 } *)
  Let C x := exists n, Cn n x.
  Local Instance C_proper: Proper (Ae ==> iff) C.
  Proof. unfold C; solve_proper. Qed.
  
  (** Define the bijective relation. *)
  Definition cantor_bernstein_schroeder_rel x y :=
    (C x /\ f x =B y) \/
    (~C x /\ g y =A x).
  Notation H := cantor_bernstein_schroeder_rel.
  
  (** It is well-defined, ... *)
  Instance cbs_rel_proper: Proper (Ae ==> Be ==> iff) H.
  Proof.
    unfold H.
    solve_proper.
  Qed.
  
  (** a partial function, ... *)
  Lemma cbs_rel_functional: forall x y y', H x y -> H x y' -> y =B y'.
  Proof.
    intros ??? [[in1 case1]|[in1 case1]] [[in2 case2]|[in2 case2]];
      try contradiction.
    - now rewrite <- case1, <- case2.
    - apply g_inj.
      now rewrite case1, case2.
  Qed.
  
  (** injective. *)
  Lemma cbs_rel_injective: forall x x' y, H x y -> H x' y -> x =A x'.
  Proof.
    intros * [[inx eqy]|[notinx eqy]] [[inx' eqy']|[notinx' eqy']].
    - now apply f_inj; transitivity y.
    - destruct inx as [n inx].
      contradict notinx'; exists (S n); cbn; red.
      exists x; split; trivial.
      now rewrite <- eqy', <- eqy.
    - destruct inx' as [n inx'].
      contradict notinx; exists (S n); cbn; red.
      exists x'; split; trivial.
      now rewrite <- eqy, <- eqy'.
    - now rewrite <- eqy, <- eqy'.
  Qed.
  
  (** For totality and surjectivity, we need excluded middle. *)
  Hypothesis EM: excluded_middle.
  (** It is also total... *)
  Lemma cbs_rel_total: forall x, exists y, H x y.
  Proof.
    intro; unfold H.
    destruct (EM (C x)) as [case|case].
    - now exists (f x); left; split.
    - destruct (EM (exists y, g y =A x)) as [[y eqx]|contra].
      + exists y; auto.
      + contradict case; exists 0; trivial.
  Qed.
  
  (** and surjective. *)
  Lemma cbs_rel_surjective: forall y, exists x, H x y.
  Proof.
    intro; unfold H.
    destruct (EM (C (g y))) as [[n iny]|notiny].
    - induction n as [|n IH]; hnf in iny.
      + now contradict iny; exists y.
      + destruct iny as [x' [inx' eqy%g_inj]].
        exists x'; left; split; try easy.
        exists n; trivial.
    - now exists (g y); right; split.
  Qed.
  
  (** Using relational reification, we can even give an explicit
    bijective function. *)
  Hypothesis pfr: SetoidFunctionalRelReification_on A B.

  (** This is the classical Cantor-Bernstein-Schröder theorem:
    Given injections A ↪ B and B ↪ A, we can define a bijection
    A ≅ B. *)
  Lemma cantor_bernstein_schröder: exists h,
    Proper (Ae ==> Be) h /\
    (forall y, exists x, h x =B y) /\
    forall x x', h x =B h x' -> x =A x'.
  Proof.
    destruct (pfr Ae Be H _ _) as [h h_spec];
      eauto using cbs_rel_total, cbs_rel_functional.
    { now intros * eqx eqy; apply cbs_rel_proper. }
    exists h.
    repeat (split; trivial); intros *.
    - intros x x'; apply h_spec.
    - destruct (cbs_rel_surjective y) as [x Hxy].
      exists x.
      now rewrite (cbs_rel_functional x y (h x)); auto; apply h_spec.
    - intro eqh.
      apply cbs_rel_injective with (y := h x); auto.
      + apply h_spec.
      + rewrite eqh; apply h_spec.
  Qed.
End CantorBernsteinSchroeder.
Notation cantor_bernstein_schroeder := cantor_bernstein_schröder (only parsing).
