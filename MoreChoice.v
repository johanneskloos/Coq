(**
 More choice principles.

 This describes a choice principle that isn't given in [ChoiceFacts] yet.

 © 2017 Johannes Kloos

 This library requires Coq 8.7. *)
From Coq.Classes Require Import Equivalence Morphisms.
From Coq Require Import Utf8 Setoid ChoiceFacts.

(** This is in the standard library since 8.7. If you want to use 8.6, uncomment
    this definition. *)

(*
Definition SetoidFunctionalChoice_on A B :=
  forall R : A -> A -> Prop,
  forall T : A -> B -> Prop,
  Equivalence R ->
  (forall x x' y, R x x' -> T x y -> T x' y) ->
  (forall x, exists y, T x y) ->
  exists f : A -> B, forall x : A, T x (f x) /\
    (forall x' : A, R x x' -> f x = f x').
Notation SetoidFunctionalChoice := (forall A B, SetoidFunctionalChoice_on A B).
*)
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

(** * Setoid relational choice.

  It generalizes [RelationalChoice_on] in that it provides choice on
  setoids, and is a weaker companion to [GeneralizedSetoidFunctionalChoice_on]
  from Coq trunk.
  *)

Definition GeneralizedSetoidRelationalChoice_on A B :=
  ∀ Ae Be
  (equA: Equivalence Ae) (equB: Equivalence Be)
  (R: A → B → Prop) (Rproper: Proper (Ae ==> Be ==> iff) R)
  (Rfull: ∀ x, ∃ y, R x y),
  ∃ (R': A → B → Prop),
  (∀ x y, R' x y → R x y) ∧
  Proper (Ae ==> Be ==> iff) R' ∧
  (∀ x, ∃ y, R' x y) ∧
  ∀ x y y', R' x y → R' x y' → Be y y'.

Notation GeneralizedSetoidRelationalChoice :=
  (∀ A B, GeneralizedSetoidRelationalChoice_on A B).

(** [GeneralizedSetoidRelationalChoice],
 follows from the standard library principle
 [SetoidFunctionalChoice]. *)

Lemma gen_setoid_fun_choice_imp_gen_setoid_rel_choice A B:
  SetoidFunctionalChoice_on A B →
  GeneralizedSetoidRelationalChoice_on A B.
Proof.
  intros choice Ae Be Aeequ Beequ R Rproper Rfull.
  destruct (choice Ae R _) as [f f_spec].
  - intros * eqx.
    now apply Rproper.
  - trivial.
  - exists (λ a b, Be (f a) b).
    split. { intros * <-; apply f_spec. }
    split. {
      intros a₁ a₂ eqa b₁ b₂ eqb.
      destruct (f_spec a₁) as [_ eqfa].
      rewrite (eqfa a₂ eqa).
      now rewrite eqb.
    }
    split.
    + now intro; exists (f x).
    + now intros * <- <-.
Qed.


