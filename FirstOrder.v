(**
 First-order logic.

 This provides a deep embedding of first-order logic, with the semantics
 given by a direct translation to Coq.
 
 © 2017 Johannes Kloos

 This library requires Coq 8.6. *)
From Coq.Classes Require Import Equivalence Morphisms SetoidClass.
From Coq Require Import Utf8 ChoiceFacts ClassicalFacts Relations List.
From Coq Require Import PeanoNat Eqdep_dec Psatz.
From misc Require Import Vectors Zorn MoreChoice ChoiceResults.
Import VectorNotations.

Lemma forall_iff {A} (P Q: A → Prop):
  (∀ v, P v ↔ Q v) → (∀ v, P v) ↔ (∀ v, Q v).
Proof. firstorder. Qed.
Lemma exists_iff {A} (P Q: A → Prop):
  (∀ v, P v ↔ Q v) → (∃ v, P v) ↔ (∃ v, Q v).
Proof. firstorder. Qed.

Record language := {
  Var: Type;
  Func: Type;
  Pred: Type;
  VarSet: Type;
  var_set_empty: VarSet;
  var_set_union: VarSet → VarSet → VarSet;
  var_set_inter: VarSet → VarSet → VarSet;
  var_set_diff: VarSet → VarSet → VarSet;
  var_set_singleton: Var → VarSet;
  var_set_In: Var → VarSet → Prop;
  var_set_empty_spec: ∀ x, ¬var_set_In x var_set_empty;
  var_set_union_spec: ∀ x s₁ s₂,
    var_set_In x (var_set_union s₁ s₂) ↔ var_set_In x s₁ ∨ var_set_In x s₂;
  var_set_inter_spec: ∀ x s₁ s₂,
    var_set_In x (var_set_inter s₁ s₂) ↔ var_set_In x s₁ ∧ var_set_In x s₂;
  var_set_diff_spec: ∀ x s₁ s₂,
    var_set_In x (var_set_diff s₁ s₂) ↔ var_set_In x s₁ ∧ ¬var_set_In x s₂;
  var_set_singleton_spec: ∀ x y, var_set_In x (var_set_singleton y) ↔ x = y;
  var_eqb: Var → Var → bool;
  var_eq_spec: ∀ v₁ v₂, BoolSpec (v₁ = v₂) (v₁ ≠ v₂) (var_eqb v₁ v₂);
  Func_arity: Func → nat;
  Pred_arity: Pred → nat
}.

Section FirstOrderLogic.
  Context (lang: language).
  Notation V := (Var lang).
  Notation F := (Func lang).
  Notation P := (Pred lang).
  Notation Vs := (VarSet lang).
  Coercion func_arity := Func_arity lang.
  Coercion pred_arity := Pred_arity lang.
  Notation "∅" := (var_set_empty lang).
  Infix "∪" := (var_set_union lang) (at level 50, left associativity).
  Notation "(∪)" := (var_set_union lang) (only parsing).
  Infix "∩" := (var_set_inter lang) (at level 40, left associativity).
  Notation "(∩)" := (var_set_inter lang) (only parsing).
  Infix "∖" := (var_set_diff lang) (at level 40, left associativity).
  Notation "(∖)" := (var_set_diff lang) (only parsing).
  Notation "{[ x ]}" := (var_set_singleton lang x).
  Notation "{[ x1 ; .. ; xn ; y ]}" := ({[ x1 ]} ∪ .. ({[ xn ]} ∪ {[ y ]}) ..).
  Infix "∈" := (var_set_In lang) (at level 70).
  Notation "(∈)" := (var_set_In lang) (only parsing).
  Notation "(∉)" := (λ x y, ¬x ∈ y).
  Infix "∉" := (∉) (at level 70).
  Infix "=?" := (var_eqb lang) (at level 70).
  
  Lemma set_empty x: x ∉ ∅.
  Proof. apply var_set_empty_spec. Qed.
  Lemma set_union x s₁ s₂: x ∈ s₁ ∪ s₂ ↔ x ∈ s₁ ∨ x ∈ s₂.
  Proof. apply var_set_union_spec. Qed.
  Lemma set_inter x s₁ s₂: x ∈ s₁ ∩ s₂ ↔ x ∈ s₁ ∧ x ∈ s₂.
  Proof. apply var_set_inter_spec. Qed.
  Lemma set_diff x s₁ s₂: x ∈ s₁ ∖ s₂ ↔ x ∈ s₁ ∧ x ∉ s₂.
  Proof. apply var_set_diff_spec. Qed.
  Lemma set_singleton x y: x ∈ {[ y ]} ↔ x = y.
  Proof. apply var_set_singleton_spec. Qed.
  Lemma var_eq x y: BoolSpec (x = y) (x ≠ y) (x =? y).
  Proof. apply var_eq_spec. Qed.
  
  Unset Elimination Schemes.
  Inductive term :=
    | tvar (v: V)
    | tfunc (f: F) (a: term^func_arity f).
  Set Elimination Schemes.
  Fixpoint term_rect (P: term → Type) (Pv: ∀ n, term^n → Type)
    (case_var: ∀ v, P (tvar v))
    (case_func: ∀ f a (IHa: Pv (func_arity f) a), P (tfunc f a))
    (case_nil: Pv 0 [#])
    (case_cons: ∀ t n a (IHx: P t) (IHa: Pv n a), Pv (S n) (t:::a))
    t: P t :=
    match t return P t with
    | tfunc f a =>
      let fix go n a: Pv n a := match a return Pv _ a with
        | [#] => case_nil
        | t:::a =>
          case_cons t _ a
            (term_rect P Pv case_var case_func case_nil case_cons t)
            (go _ a)
        end
      in case_func f a (go _ a)
    | tvar v => case_var v
    end.
  Definition term_rec (P: term → Set) (Pv: ∀ n, term^n → Set) := term_rect P Pv.
  Definition term_ind (P: term → Prop) case_var case_func :=
    term_rect P (@Vector.Forall _ P) case_var case_func
      (Vector.Forall_nil P) (λ t n a, Vector.Forall_cons P t a).
  Coercion tvar: V >-> term.
  Coercion tfunc: F >-> Funclass.
  
  Class Free A := free: A → Vs.
  Class Bound A := bound: A → Vs.
  Class Subst A := subst: (V → option term) → A → A.
  Global Instance term_free: Free term := fix f t := match t with
    | tfunc _ a =>
      let fix fa n (a: term^n) := match a with
      | [#] => ∅
      | t:::a => f t ∪ fa _ a
      end in fa _ a
    | tvar x => {[ x ]}
    end.
  Global Instance term_bound: Bound term := λ _, ∅.
  Global Instance term_subst: Subst term := fix s σ t := match t with
    | tfunc f a => tfunc f (Vector.map (s σ) a)
    | tvar x => match σ x with
      | Some t => t
      | None => tvar x
      end
    end.
  
  Lemma free_func f a (P: V → Prop): (∀ x, x ∈ free (tfunc f a) → P x) ↔
    #Forall (λ t, ∀ x, x ∈ free t → P x) a.
  Proof.
    cbn.
    induction a as [|t n a IH].
    - rewrite vector_Forall_forall.
      split.
      + intros _ y [ ]%vector_In_invert.
      + intros _ x [ ]%set_empty.
    - rewrite vector_Forall_cons, <- IH.
      setoid_rewrite set_union.
      firstorder.
  Qed.
  
  Lemma term_subst_local t: ∀ σ₁ σ₂ (local: ∀ x, x ∈ free t → σ₁ x = σ₂ x),
    subst σ₁ t = subst σ₂ t.
  Proof.
    induction t; intros; cbn.
    - rewrite local; [trivial|now apply set_singleton].
    - f_equal.
      apply vector_map_Forall,
        (vector_Forall_impl' (λ t, ∀ x, x ∈ free t → σ₁ x = σ₂ x)).
      + now rewrite <- free_func. 
      + eapply vector_Forall_impl; [|apply IHa]; auto.
  Qed.
  
  Definition merge_subst σ₁ σ₂ v :=
    match σ₁ v with
    | Some t => Some (subst σ₂ t)
    | None => σ₂ v
    end.
  Lemma term_subst_subst σ₁ σ₂ t:
    subst σ₂ (subst σ₁ t) = subst (merge_subst σ₁ σ₂) t.
  Proof.
    induction t; cbn.
    - unfold merge_subst.
      destruct (σ₁ v); trivial.
    - f_equal.
      rewrite vector_map_map.
      now apply vector_map_Forall.
  Qed.
  
  Lemma term_subst_empty t: subst (λ _, None) t = t.
  Proof.
    induction t; cbn; trivial.
    f_equal.
    apply vector_map_Forall in IHa.
    now rewrite IHa, vector_map_id.
  Qed.
  
  Inductive formula :=
    | fpred p (a: term^pred_arity p)
    | fand (φ₁ φ₂: formula)
    | for_ (φ₁ φ₂: formula)
    | fimp (φ₁ φ₂: formula)
    | fnot (φ: formula)
    | fbot
    | fforall (v: V) (φ: formula)
    | fexists (v: V) (φ: formula).
  Coercion fpred: P >-> Funclass.
  Infix "'∧" := fand (at level 50).
  Infix "'∨" := for_ (at level 50).
  Infix "'→" := fimp (at level 55).
  Notation "'¬ φ" := (fnot φ) (at level 40).
  Notation "'∀ x , φ" := (fforall x φ) (at level 60).
  Notation "'∃ x , φ" := (fexists x φ) (at level 60).
  Notation "'⊥" := fbot.
  
  Global Instance formula_free: Free formula := fix f φ := match φ with
    | fpred _ a =>
      let fix f n a := match a with
        | t:::a => free t ∪ f _ a
        | [#] => ∅
        end
      in f _ a
    | φ₁ '∧ φ₂ | φ₁ '∨ φ₂ | φ₁ '→ φ₂ => f φ₁ ∪ f φ₂
    | '¬ φ => f φ
    | '∀ x, φ | '∃ x, φ => f φ ∖ {[ x ]}
    | '⊥ => ∅
    end.
  Global Instance formula_bound: Bound formula := fix b φ := match φ with
    | φ₁ '∧ φ₂ | φ₁ '∨ φ₂ | φ₁ '→ φ₂ => b φ₁ ∪ b φ₂
    | '¬ φ => b φ
    | '∀ x, φ | '∃ x, φ => b φ ∪ {[ x ]}
    | fpred _ _ | '⊥ => ∅
    end.
  Definition remove x (σ: V → option term) v := if x =? v then None else σ v.
  Global Instance formula_subst: Subst formula := fix s σ φ := match φ with
    | fpred p a => fpred p (Vector.map (subst σ) a)
    | φ₁ '∧ φ₂ => s σ φ₁ '∧ s σ φ₂
    | φ₁ '∨ φ₂ => s σ φ₁ '∨ s σ φ₂
    | φ₁ '→ φ₂ => s σ φ₁ '→ s σ φ₂
    | '¬ φ => '¬ s σ φ
    | '⊥ => '⊥
    | '∀ x, φ => '∀ x, s (remove x σ) φ
    | '∃ x, φ => '∃ x, s (remove x σ) φ
    end.

  Lemma free_pred p a (P: V → Prop): (∀ x, x ∈ free (fpred p a) → P x) ↔
    #Forall (λ t, ∀ x, x ∈ free t → P x) a.
  Proof.
    cbn.
    induction a as [|t n a IH].
    - rewrite vector_Forall_forall.
      split.
      + intros _ y [ ]%vector_In_invert.
      + intros _ x [ ]%set_empty.
    - rewrite vector_Forall_cons, <- IH.
      setoid_rewrite set_union.
      firstorder.
  Qed.
  
  Lemma formula_subst_local φ: ∀ σ₁ σ₂ (local: ∀ x, x ∈ free φ → σ₁ x = σ₂ x),
    subst σ₁ φ = subst σ₂ φ.
  Proof.
    induction φ; intros; cbn; try solve
      [f_equal; auto
      |f_equal; [apply IHφ1|apply IHφ2]; intros x inx;
        apply local, set_union; auto].
    - f_equal.
      rewrite free_pred in local.
      apply vector_map_Forall.
      revert local; apply vector_Forall_impl.
      intro; apply term_subst_local.
    - f_equal; apply IHφ.
      intros x inx; unfold remove.
      destruct (var_eq v x) as [<-|neq]; auto.
      apply local; cbn.
      rewrite set_diff, set_singleton; intuition.
    - f_equal; apply IHφ.
      intros x inx; unfold remove.
      destruct (var_eq v x) as [<-|neq]; auto.
      apply local; cbn.
      rewrite set_diff, set_singleton; intuition.
  Qed.
  
  Lemma formula_subst_subst: ∀ φ σ₁ σ₂
    (no_collision: ∀ x y t, σ₁ x = Some t → y ∈ bound φ → y ∉ free t),
    subst σ₂ (subst σ₁ φ) = subst (merge_subst σ₁ σ₂) φ.
  Proof.
    assert (∀ v φ σ₁ σ₂
      (no_collision: ∀ x y t, σ₁ x = Some t → y ∈ bound φ ∪ {[ v ]} → y ∉ free t)
      (IH: ∀ σ₁ σ₂, (∀ x y t, σ₁ x = Some t → y ∈ bound φ → ¬ y ∈ free t) →
        subst σ₂ (subst σ₁ φ) = subst (merge_subst σ₁ σ₂) φ),
      subst (remove v σ₂) (subst (remove v σ₁) φ) =
      subst (remove v (merge_subst σ₁ σ₂)) φ) as binder_case. {
      intros.
      rewrite IH.
      - apply formula_subst_local.
        intros x inx.
        unfold merge_subst, remove.
        destruct (var_eq v x) as [<-|neqx]; trivial.
        destruct (σ₁ x) as [t|] eqn:eqt; trivial.
        f_equal.
        apply term_subst_local.
        intros y iny.
        destruct (var_eq v y) as [<-|neqy]; trivial.
        apply (no_collision x v t) in iny; [contradiction|auto|].
        rewrite set_union, set_singleton; auto.
      - unfold remove.
        intros *.
        destruct (var_eq v x) as [<-|neq]; [discriminate|].
        intros mtx iny.
        apply (no_collision x y t); auto.
        rewrite set_union; auto.
    }
    induction φ; cbn; intros; try solve
      [f_equal; auto
      |f_equal; [apply IHφ1|apply IHφ2]; intros;
        apply (no_collision x y t); auto; apply set_union; auto].
    rewrite vector_map_map.
    f_equal.
    apply vector_map_ext.
    intro; apply term_subst_subst.
  Qed.
  
  Lemma formula_subst_empty φ: subst (λ _, None) φ = φ.
  Proof.
    induction φ; cbn; try solve [f_equal; auto].
    - rewrite <- (vector_map_id a) at 2.
      f_equal; apply vector_map_ext.
      intro; apply term_subst_empty.
    - f_equal.
      rewrite <- IHφ at 2.
      apply formula_subst_local.
      unfold remove; intros.
      destruct (v =? x); trivial.
    - f_equal.
      rewrite <- IHφ at 2.
      apply formula_subst_local.
      unfold remove; intros.
      destruct (v =? x); trivial.
  Qed.
  
  Record structure := {
    universe: Type;
    interpret_func: ∀ f, universe^func_arity f → universe;
    interpret_pred: ∀ p, universe^pred_arity p → Prop;
  }.
  Section Interpret.
    Context (struc: structure).
    Notation U := (universe struc).
    Notation If := (interpret_func struc).
    Notation Ip := (interpret_pred struc).
    
    Fixpoint interpret_term ν t := match t with
      | tvar x => ν x
      | tfunc f a => If f (Vector.map (interpret_term ν) a)
      end.
    Lemma interpret_term_local (t: term) ν₁ ν₂
      (local: ∀ x, x ∈ free t → ν₁ x = ν₂ x):
      interpret_term ν₁ t = interpret_term ν₂ t.
    Proof.
      induction t; cbn.
      - now apply local, set_singleton.
      - f_equal.
        apply vector_map_Forall.
        refine (vector_Forall_impl' _ _ _ _ IHa).
        apply free_func, local.
    Qed.
    
    Definition interpret_subst ν σ v := match σ v with
      | Some t => interpret_term ν t
      | None => ν v
      end.
    Lemma interpret_term_subst ν σ t:
      interpret_term ν (subst σ t) = interpret_term (interpret_subst ν σ) t.
    Proof.
      induction t; cbn.
      - unfold interpret_subst.
        destruct (σ v); trivial.
      - f_equal.
        rewrite vector_map_map.
        now apply vector_map_Forall.
    Qed.
    
    Definition update x v (ν: V → U) y := if x =? y then v else ν y.
    Fixpoint interpret_formula ν φ := match φ with
      | fpred p a => Ip p (Vector.map (interpret_term ν) a)
      | φ₁ '∧ φ₂ => interpret_formula ν φ₁ ∧ interpret_formula ν φ₂
      | φ₁ '∨ φ₂ => interpret_formula ν φ₁ ∨ interpret_formula ν φ₂
      | φ₁ '→ φ₂ => interpret_formula ν φ₁ → interpret_formula ν φ₂
      | '¬ φ => ¬interpret_formula ν φ
      | '⊥ => False
      | '∀ x, φ => ∀ v, interpret_formula (update x v ν) φ
      | '∃ x, φ => ∃ v, interpret_formula (update x v ν) φ
      end.

    Lemma interpret_formula_local: ∀  (φ: formula)ν₁ ν₂
      (local: ∀ x, x ∈ free φ → ν₁ x = ν₂ x),
      interpret_formula ν₁ φ ↔ interpret_formula ν₂ φ.
    Proof.
      assert (∀ v φ
        (IH: ∀ ν₁ ν₂, (∀ x, x ∈ free φ → ν₁ x = ν₂ x) →
          interpret_formula ν₁ φ ↔ interpret_formula ν₂ φ)
        ν₁ ν₂ (local: ∀ x, x ∈ free φ ∖ {[ v ]} → ν₁ x = ν₂ x), ∀ y,
        interpret_formula (update v y ν₁) φ ↔
        interpret_formula (update v y ν₂) φ)
        as binder_case. {
        intros.
        apply IH.
        intros x inx.
        unfold update.
        destruct (var_eq v x) as [<-|neq]; trivial.
        apply local; cbn.
        rewrite set_diff, set_singleton.
        intuition.
      }
      induction φ; intros; cbn; try solve
        [reflexivity
        |cbn; rewrite (IHφ1 ν₁ ν₂), (IHφ2 ν₁ ν₂);
          [tauto|intros; apply local, set_union; auto..]].
      - f_equiv.
        apply vector_map_Forall.
        rewrite free_pred in local.
        eapply vector_Forall_impl; [|apply local].
        intro; apply interpret_term_local.
      - now rewrite IHφ.
      - specialize (binder_case _ _ IHφ _ _ local); firstorder.
      - specialize (binder_case _ _ IHφ _ _ local); firstorder.
    Qed.
    
    Lemma interpret_formula_subst: ∀ φ ν σ
      (no_collisions: ∀ y, y ∈ bound φ → ∀ x t, σ x = Some t → y ∉ free t),
      interpret_formula ν (subst σ φ) ↔
      interpret_formula (interpret_subst ν σ) φ.
    Proof.
      assert (binder_case: ∀ φ v σ ν
        (IH: ∀ ν σ, (∀ y, y ∈ bound φ → ∀ x t, σ x = Some t → ¬y ∈ free t) →
          interpret_formula ν (subst σ φ) ↔
          interpret_formula (interpret_subst ν σ) φ)
        (no_collisions: ∀ y, y ∈ bound φ ∪ {[ v ]} → ∀ x t, σ x = Some t →
          ¬y ∈ free t) w,
        interpret_formula (update v w ν) (subst (remove v σ) φ) ↔
        interpret_formula (update v w (interpret_subst ν σ)) φ). {
        intros.
        rewrite IH. {
          apply interpret_formula_local.
          intros x inx.
          unfold interpret_subst, update, remove.
          destruct (var_eq v x) as [|neqx]; trivial.
          destruct (σ x) eqn:eqx; trivial.
          apply interpret_term_local.
          intros y iny.
          destruct (var_eq v y) as [<-|]; trivial.
          apply (no_collisions v) in eqx; [contradiction|].
          cbn; rewrite set_union, set_singleton; auto.
        } {
          intros y iny x t int.
          unfold remove in int.
          destruct (var_eq v x) as [<-|neq]; [discriminate|].
          revert int; apply no_collisions.
          cbn; rewrite set_union; auto.
        }
      }
      induction φ; intros; cbn; try solve
        [reflexivity
        |rewrite IHφ1, IHφ2;
          [tauto|intros y iny; apply no_collisions, set_union; auto..]].
      - f_equiv.
        rewrite vector_map_map.
        apply vector_map_ext.
        intro; apply interpret_term_subst.
      - now rewrite IHφ.
      - now apply forall_iff, binder_case.
      - now apply exists_iff, binder_case.
    Qed.
    
    (* α-renaming, key lemma *)
    Definition replace_var (x y v: V) := if x =? v then Some (tvar y) else None.
    Lemma alpha_toplevel φ x y ν v
      (y_not_bound: y ∉ (bound φ ∪ (free φ ∖ {[x]}))):
      interpret_formula (update x v ν) φ ↔
      interpret_formula (update y v ν) (subst (replace_var x y) φ).
    Proof.
      rewrite interpret_formula_subst. {
        apply interpret_formula_local.
        intros z inz.
        unfold interpret_subst, update, replace_var.
        destruct (var_eq x z) as [<-|neq]; cbn.
        - destruct (var_eq y y); congruence.
        - destruct (var_eq y z) as [<-|neq']; trivial.
          red in y_not_bound.
          rewrite set_union, set_diff, set_singleton in y_not_bound.
          intuition.
      } {
        intros a ina b t.
        unfold replace_var.
        destruct (var_eq x b) as [<-|neq]; [|discriminate].
        injection 1 as <-.
        cbn; rewrite set_singleton.
        intros ->.
        red in y_not_bound.
        rewrite set_union in y_not_bound.
        intuition.
      }
    Qed.
  End Interpret.
  Definition equivalence φ₁ φ₂ :=
     ∀ σ ν, interpret_formula σ ν φ₁ ↔ interpret_formula σ ν φ₂.
  Global Instance equivalence_Equivalence: Equivalence equivalence.
  Proof.
    split.
    - now intros φ σ ν.
    - intros φ₁ φ₂ eqφ σ ν.
      now rewrite (eqφ σ ν).
    - intros φ₁ φ₂ φ₃ eqφ eqφ' σ ν.
      now rewrite (eqφ σ ν), (eqφ' σ ν).
  Qed.
  Infix "≡" := equivalence (at level 70).
  Notation "(≡)" := equivalence (only parsing).
  Global Instance and_proper: Proper ((≡) ==> (≡) ==> (≡)) fand.
  Proof.
    intros φ₁ φ₁' eqφ₁ φ₂ φ₂' eqφ₂ σ ν.
    now cbn; rewrite (eqφ₁ σ ν), (eqφ₂ σ ν).
  Qed.
  Global Instance or_proper: Proper ((≡) ==> (≡) ==> (≡)) for_.
  Proof.
    intros φ₁ φ₁' eqφ₁ φ₂ φ₂' eqφ₂ σ ν.
    now cbn; rewrite (eqφ₁ σ ν), (eqφ₂ σ ν).
  Qed.
  Global Instance imp_proper: Proper ((≡) ==> (≡) ==> (≡)) fimp.
  Proof.
    intros φ₁ φ₁' eqφ₁ φ₂ φ₂' eqφ₂ σ ν.
    now cbn; rewrite (eqφ₁ σ ν), (eqφ₂ σ ν).
  Qed.
  Global Instance not_proper: Proper ((≡) ==> (≡)) fnot.
  Proof.
    intros φ₁ φ₁' eqφ₁ σ ν.
    now cbn; rewrite (eqφ₁ σ ν).
  Qed.
  Global Instance forall_proper: Proper (eq ==> (≡) ==> (≡)) fforall.
  Proof.
    intros x ? <- φ φ' eqφ σ ν; cbn.
    apply forall_iff.
    intro.
    apply eqφ.
  Qed.
  Global Instance exists_proper: Proper (eq ==> (≡) ==> (≡)) fexists.
  Proof.
    intros x ? <- φ φ' eqφ σ ν; cbn.
    apply exists_iff.
    intro.
    apply eqφ.
  Qed.
  
  Inductive αstep: formula → formula → Prop :=
    | αandl φ₁ φ₁' φ₂: αstep φ₁ φ₁' → αstep (φ₁ '∧ φ₂) (φ₁' '∧ φ₂)
    | αorl φ₁ φ₁' φ₂: αstep φ₁ φ₁' → αstep (φ₁ '∨ φ₂) (φ₁' '∨ φ₂)
    | αimpl φ₁ φ₁' φ₂: αstep φ₁ φ₁' → αstep (φ₁ '→ φ₂) (φ₁' '→ φ₂)
    | αandr φ₁ φ₂ φ₂': αstep φ₂ φ₂' → αstep (φ₁ '∧ φ₂) (φ₁ '∧ φ₂')
    | αorr φ₁ φ₂ φ₂': αstep φ₂ φ₂' → αstep (φ₁ '∨ φ₂) (φ₁ '∨ φ₂')
    | αimpr φ₁ φ₂ φ₂': αstep φ₂ φ₂' → αstep (φ₁ '→ φ₂) (φ₁ '→ φ₂')
    | αneg φ φ': αstep φ φ' → αstep ('¬ φ) ('¬ φ')
    | αforall x φ φ': αstep φ φ' → αstep ('∀ x, φ) ('∀ x, φ')
    | αexists x φ φ': αstep φ φ' → αstep ('∃ x, φ) ('∃ x, φ')
    | αforall_rename x y φ (no_collision: y ∉ (bound φ ∪ free φ ∖ {[ x ]})):
      αstep ('∀ x, φ) ('∀ y, subst (replace_var x y) φ)
    | αexists_rename x y φ (no_collision: y ∉ (bound φ ∪ free φ ∖ {[ x ]})):
      αstep ('∃ x, φ) ('∃ y, subst (replace_var x y) φ).
  Lemma αstep_equivalence: subrelation αstep equivalence.
  Proof.
    induction 1; try now rewrite IHαstep.
    - intros σ ν; cbn.
      apply forall_iff; intro.
      rewrite alpha_toplevel; [reflexivity|assumption].
    - intros σ ν; cbn.
      apply exists_iff; intro.
      rewrite alpha_toplevel; [reflexivity|assumption].
  Qed.
  
  Definition αrenaming := clos_refl_sym_trans formula αstep.
  Global Instance αrenaming_equivalence: subrelation αrenaming equivalence.
  Proof.
    induction 1.
    - now apply αstep_equivalence.
    - reflexivity.
    - now symmetry.
    - now transitivity y.
  Qed.
  Global Instance αrenaming_equiv: Equivalence αrenaming.
  Proof.
    split.
    - constructor 2.
    - now constructor 3.
    - intros x y z; now constructor 4 with y.
  Qed.
  
  Section MappedInterpretation.
    Context (σ₁ σ₂: structure) (mu: universe σ₁ → universe σ₂).
    Context (map_f: ∀ f a,
      mu (interpret_func σ₁ f a) =
      interpret_func σ₂ f (Vector.map mu a)).
    Context (map_p: ∀ p a,
      interpret_pred σ₁ p a ↔ interpret_pred σ₂ p (Vector.map mu a)).
    Context (sur: ∀ y, ∃ x, mu x = y).
    Notation "f · g" := (λ x, f (g x)) (at level 60).
    Lemma map_interpret_term ν t:
      mu (interpret_term σ₁ ν t) = interpret_term σ₂ (mu · ν) t.
    Proof.
      induction t; cbn; trivial.
      rewrite map_f.
      rewrite vector_map_map.
      f_equal.
      now apply vector_map_Forall.
    Qed.
    
    Lemma map_interpretation ν φ:
      interpret_formula σ₁ ν φ ↔
      interpret_formula σ₂ (λ v, mu (ν v)) φ.
    Proof.
      revert ν.
      induction φ; intros; cbn; try now rewrite ?IHφ, ?IHφ1, ?IHφ2.
      - rewrite map_p, vector_map_map.
        f_equiv; apply vector_map_ext.
        apply map_interpret_term.
      - transitivity (∀ w, interpret_formula σ₂ (update σ₂ v (mu w) (mu · ν)) φ).
        + apply forall_iff; intro w.
          rewrite IHφ.
          apply interpret_formula_local.
          intros x _.
          unfold update.
          destruct (v =? x); trivial.
        + split; intros pre w; auto.
          destruct (sur w) as [w' <-]; auto.
      -  transitivity (∃ w, interpret_formula σ₂ (update σ₂ v (mu w) (mu · ν)) φ).
        + apply exists_iff; intro w.
          rewrite IHφ.
          apply interpret_formula_local.
          intros x _.
          unfold update.
          destruct (v =? x); trivial.
        + split; intros [w pre]; eauto.
          destruct (sur w) as [w' <-]; eauto.
    Qed.
  End MappedInterpretation.
  
  Class EM := em: excluded_middle.
  Lemma and_assoc φ₁ φ₂ φ₃: φ₁ '∧ (φ₂ '∧ φ₃) ≡ (φ₁ '∧ φ₂) '∧ φ₃.
  Proof. intros ??; cbn; tauto. Qed.
  Lemma or_assoc φ₁ φ₂ φ₃: φ₁ '∨ (φ₂ '∨ φ₃) ≡ (φ₁ '∨ φ₂) '∨ φ₃.
  Proof. intros ??; cbn; tauto. Qed.
  Lemma and_comm φ₁ φ₂: φ₁ '∧ φ₂ ≡ φ₂ '∧ φ₁.
  Proof. intros ??; cbn; tauto. Qed.
  Lemma or_comm φ₁ φ₂: φ₁ '∨ φ₂ ≡ φ₂ '∨ φ₁.
  Proof. intros ??; cbn; tauto. Qed.
  Lemma and_or_l φ₁ φ₂ φ₃: φ₁ '∧ (φ₂ '∨ φ₃) ≡ (φ₁ '∧ φ₂) '∨ (φ₁ '∧ φ₃).
  Proof. intros ??; cbn; tauto. Qed.
  Lemma and_or_r φ₁ φ₂ φ₃: (φ₁ '∨ φ₂) '∧ φ₃ ≡ (φ₁ '∧ φ₃) '∨ (φ₂ '∧ φ₃).
  Proof. intros ??; cbn; tauto. Qed.
  Lemma or_and_l φ₁ φ₂ φ₃: φ₁ '∨ (φ₂ '∧ φ₃) ≡ (φ₁ '∨ φ₂) '∧ (φ₁ '∨ φ₃).
  Proof. intros ??; cbn; tauto. Qed.
  Lemma or_and_r φ₁ φ₂ φ₃: (φ₁ '∧ φ₂) '∨ φ₃ ≡ (φ₁ '∨ φ₃) '∧ (φ₂ '∨ φ₃).
  Proof. intros ??; cbn; tauto. Qed.
  Lemma and_or_absorb_l φ₁ φ₂: φ₁ '∧ (φ₁ '∨ φ₂) ≡ φ₁.
  Proof. intros ??; cbn; tauto. Qed.
  Lemma and_or_absorb_r φ₁ φ₂: (φ₁ '∨ φ₂) '∧ φ₁ ≡ φ₁.
  Proof. intros ??; cbn; tauto. Qed.
  Lemma or_and_absorb_l φ₁ φ₂: φ₁ '∨ (φ₁ '∧ φ₂) ≡ φ₁.
  Proof. intros ??; cbn; tauto. Qed.
  Lemma or_and_absorb_r φ₁ φ₂: (φ₁ '∧ φ₂) '∨ φ₁ ≡ φ₁.
  Proof. intros ??; cbn; tauto. Qed.
  Lemma and_idem φ: φ '∧ φ ≡ φ.
  Proof. intros ??; cbn; tauto. Qed.
  Lemma or_idem φ: φ '∨ φ ≡ φ.
  Proof. intros ??; cbn; tauto. Qed.
  
  Notation "'⊤" := ('¬ '⊥).
  Lemma imp_diag φ: φ '→ φ ≡ '⊤.
  Proof. intros ??; cbn; tauto. Qed.
  Lemma imp_and_l φ₁ φ₂ φ₃: (φ₁ '∧ φ₂) '→ φ₃ ≡ φ₁ '→ (φ₂ '→ φ₃).
  Proof. intros ??; cbn; tauto. Qed.
  Lemma imp_or_l φ₁ φ₂ φ₃: (φ₁ '∨ φ₂) '→ φ₃ ≡ (φ₁ '→ φ₃) '∧ (φ₂ '→ φ₃).
  Proof. intros ??; cbn; tauto. Qed.
  Lemma imp_and_r φ₁ φ₂ φ₃: φ₁ '→ (φ₂ '∧ φ₃) ≡ (φ₁ '→ φ₂) '∧ (φ₁ '→ φ₃).
  Proof. intros ??; cbn; tauto. Qed.
  
  Lemma holds `{EM} σ ν φ: interpret_formula σ ν φ ∨ ¬interpret_formula σ ν φ.
  Proof. apply em. Qed.
  
  Lemma imp_or_r `{EM} φ₁ φ₂ φ₃: φ₁ '→ (φ₂ '∨ φ₃) ≡ (φ₁ '→ φ₂) '∨ (φ₁ '→ φ₃).
  Proof.
    intros ??; cbn; intuition.
    destruct (holds σ ν φ₂); tauto.
  Qed.
  Lemma de_morgan_and φ₁ φ₂: ('¬ φ₁) '∧ ('¬ φ₂) ≡ '¬ (φ₁ '∨ φ₂).
  Proof. intros ??; cbn; intuition. Qed.
  Lemma de_morgan_or `{EM} φ₁ φ₂: ('¬ φ₁) '∨ ('¬ φ₂) ≡ '¬ (φ₁ '∧ φ₂).
  Proof.
    intros ??; cbn; intuition.
    destruct (holds σ ν φ₁); tauto.
  Qed.
  Lemma imp_spec `{EM} φ₁ φ₂: φ₁ '→ φ₂ ≡ ('¬φ₁) '∨ φ₂.
  Proof.
    intros ??; cbn; intuition.
    destruct (holds σ ν φ₁); tauto.
  Qed.
  Lemma neg_neg `{EM} φ: '¬ ('¬φ) ≡ φ.
  Proof. intros ??; cbn; destruct (holds σ ν φ); tauto. Qed.
  Lemma and_spec `{EM} φ₁ φ₂: φ₁ '∧ φ₂ ≡ '¬ (('¬ φ₁) '∨ ('¬ φ₂)).
  Proof. now rewrite de_morgan_or, neg_neg. Qed.
  
  Lemma neg_exists x φ: ('¬ '∃ x, φ) ≡ '∀ x, '¬ φ.
  Proof. intros ??; cbn; firstorder. Qed.
  Lemma neg_forall `{EM} x φ: ('¬ '∀ x, φ) ≡ '∃ x, '¬ φ.
  Proof.
    intros ??; cbn.
    split; [|firstorder].
    intro.
    destruct (em (∃ v, ¬interpret_formula σ (update σ x v ν) φ)); trivial.
    contradict H0.
    intro.
    destruct (holds σ (update σ x v ν) φ); auto.
    contradict H1; eauto.
  Qed.
  Lemma forall_spec `{EM} x φ: '∀ x, φ ≡ '¬ ('∃ x, '¬ φ).
  Proof. now rewrite <- neg_forall, neg_neg. Qed.
  
  Inductive qff: formula → Prop :=
    | qff_pred p a: qff (fpred p a)
    | qff_and φ₁ φ₂: qff φ₁ → qff φ₂ → qff (φ₁ '∧ φ₂)
    | qff_or φ₁ φ₂: qff φ₁ → qff φ₂ → qff (φ₁ '∨ φ₂)
    | qff_impl φ₁ φ₂: qff φ₁ → qff φ₂ → qff (φ₁ '→ φ₂)
    | qff_not φ: qff φ → qff ('¬ φ)
    | qff_bot: qff '⊥.
  
  Lemma formula_ind_or_not_bot_exists `{EM} (P: formula → Prop)
    (case_proper: ∀ φ φ', φ ≡ φ' → P φ → P φ')
    (case_pred: ∀ p a, P (fpred p a))
    (case_or: ∀ φ₁ φ₂ (IH₁: P φ₁) (IH₂: P φ₂), P (φ₁ '∨ φ₂))
    (case_not: ∀ φ (IH: P φ), P ('¬ φ))
    (case_bot: P '⊥)
    (case_exists: ∀ x φ (IH: P φ), P ('∃ x, φ))
    φ: P φ.
  Proof.
    assert (Proper ((≡) ==> iff) P) as P_proper.
    { apply proper_sym_impl_iff; [apply _..|assumption]. }
    induction φ; auto.
    - rewrite and_spec; auto.
    - rewrite imp_spec; auto.
    - rewrite forall_spec; auto.
  Qed.
  
  Hint Constructors qff.
  Lemma formula_ind_or_not_bot_qff `{EM} (P: formula → Prop)
    (case_proper: ∀ φ φ', φ ≡ φ' → qff φ' → qff φ → P φ → P φ')
    (case_pred: ∀ p a, P (fpred p a))
    (case_or: ∀ φ₁ φ₂ (IH₁: P φ₁) (IH₂: P φ₂), P (φ₁ '∨ φ₂))
    (case_not: ∀ φ (IH: P φ), P ('¬ φ))
    (case_bot: P '⊥)
    φ: qff φ → P φ.
  Proof.
    induction 1; auto.
    - apply (case_proper ('¬ (('¬ φ₁) '∨ ('¬ φ₂)))); auto.
      now rewrite and_spec.
    - apply (case_proper (('¬ φ₁) '∨ φ₂)); auto.
      now rewrite imp_spec.
  Qed.
  
  Section Ultraproduct.
    Context {I U} {HU: @Ultrafilter (I → Prop) sub U}.
    Lemma uf_sub: Proper (sub ++> Basics.impl) U.
    Proof. apply filt_uc, _. Qed.
    Lemma uf_wd: Proper (pointwise_relation I iff ==> iff) U.
    Proof.
      intros s s' eqs.
      split; apply (filt_uc (I → Prop) sub); intro; apply eqs.
    Qed.
    Lemma uf_min: ¬U (λ _, False).
    Proof.
      destruct (filt_proper (I → Prop) sub) as [b contra].
      contradict contra.
      eapply (filt_uc (I → Prop) sub); eauto.
      destruct 1.
    Qed.
    Lemma uf_inter s₁ s₂: U s₁ → U s₂ → U (λ x, s₁ x ∧ s₂ x).
    Proof.
      intros in₁ in₂.
      destruct (filt_dir (I → Prop) sub s₁ s₂) as [w [inw [sub₁ sub₂]]]; auto.
      apply (filt_uc (I → Prop) sub w); auto.
      split; auto.
    Qed.
    Lemma uf_not_complement s: U s → U (λ x, ¬s x) → False.
    Proof.
      intros ins incs.
      apply uf_min, (uf_wd (λ x, s x ∧ ¬s x)).
      - firstorder.
      - now apply uf_inter.
    Qed.
    Context (i: I).
    Lemma uf_ultra `{EM} s: U s ∨ U (λ x, ¬s x).
    Proof.
      apply (ultrafilter_prime (I → Prop) sub em
        (λ s₁ s₂ x, s₁ x ∨ s₂ x) (λ s₁ s₂ x, s₁ x ∧ s₂ x)).
      - now left.
      - now right.
      - now intros ??? [].
      - now intros ??? [].
      - intros ?????? [|]; auto.
      - split; auto.
      - intros; split; intros ?; tauto.
      - apply _.
      - apply (filt_ultra (I → Prop) sub (λ s', (∀ x, s' x) ∨ U s'));
          [|now right|auto].
        split. split.
        + intros s₁ s₂ ssub [case|case]; auto.
          right.
          apply (filt_uc (I → Prop) sub s₁); auto.
        + intros s₁ s₂ [case₁|case₁] [case₂|case₂].
          * unfold sub; exists s₁; eauto.
          * exists s₂; unfold sub; eauto.
          * exists s₁; unfold sub; eauto.
          * destruct (filt_dir (I → Prop) sub s₁ s₂) as [s₃ [ins₃ [sub₁ sub₂]]];
              eauto.
        + exists (λ _, False).
          intros [case|case].
          * exact (case i).
          * destruct (filt_proper (I → Prop) sub) as [s' contra].
            contradict contra.
            apply (uf_sub (λ _, False)); firstorder.
    Qed.
    
    Context (models: I → structure).
    Definition ultraproduct := {|
      universe := ∀ i, universe (models i);
      interpret_func :=
        λ f a i, interpret_func (models i) f (Vector.map (λ x, x i) a);
      interpret_pred :=
        λ p a, U (λ i, interpret_pred (models i) p (Vector.map (λ x, x i) a))
    |}.
    
    Definition extent ν φ i := interpret_formula (models i) (λ x, ν x i) φ.
    Let good φ ν := interpret_formula ultraproduct ν φ ↔ U (extent ν φ).
    
    Lemma up_pred p a ν: good (fpred p a) ν.
    Proof.
      cbn; unfold good, extent.
      apply uf_wd; intro j.
      rewrite vector_map_map; cbn.
      f_equiv.
      apply vector_map_ext.
      induction x; cbn; trivial.
      f_equal.
      rewrite vector_map_map.
      apply vector_map_Forall; trivial.
    Qed.
    
    Lemma up_or `{EM}
      φ₁ φ₂ ν (IH₁: good φ₁ ν) (IH₂: good φ₂ ν): good (φ₁ '∨ φ₂) ν.
    Proof.
      unfold good, extent in *.
      cbn; rewrite IH₁, IH₂.
      split.
      - intros [case|case].
        + eapply uf_sub; [|apply case]; auto.
          now left.
        + eapply uf_sub; [|apply case]; auto.
          now right.
      - intro pre.
        fold (extent ν φ₁) in *.
        fold (extent ν φ₂) in *.
        destruct (uf_ultra (extent ν φ₁)); auto.
        destruct (uf_ultra (extent ν φ₂)); auto.
        apply uf_not_complement in pre; [contradiction|].
        apply (uf_wd (λ i, ¬extent ν φ₁ i ∧ ¬extent ν φ₂ i)).
        + intro; tauto.
        + now apply uf_inter.
    Qed.
    
    Lemma up_not `{EM} φ ν (IH: good φ ν): good ('¬ φ) ν.
    Proof.
      unfold good in *; cbn.
      rewrite IH.
      destruct (uf_ultra (extent ν φ)) as [case|case].
      - intuition.
        apply uf_not_complement in H0; auto.
      - intuition.
        apply uf_not_complement in H1; auto.
    Qed.
    
    Lemma up_bot ν: good '⊥ ν.
    Proof.
      unfold good, extent; cbn.
      split; [tauto|].
      intros []%uf_min.
    Qed.
    
    Lemma up_exists x φ ν `{EM} (choice: DependentFunctionalChoice)
      (IH: ∀ v, good φ (update ultraproduct x v ν)): good ('∃ x, φ) ν.
    Proof.
      unfold good in *; cbn.
      split. {
        intros [v pre].
        rewrite IH in pre.
        revert pre.
        apply uf_sub.
        intros j.
        unfold extent; cbn.
        intro pre.
        exists (v j).
        revert pre; apply interpret_formula_local.
        intros y iny.
        unfold update.
        destruct (x =? y); trivial.
      } {
        intro pre.
        set (int i v :=
          interpret_formula (models i) (update (models i) x v (λ y, ν y i)) φ).
        destruct (choice _ _ (λ i u, int i u ∨ ∀ v, ¬int i v))
          as [v v_spec].
        { intro j; cbn.
          destruct (em (∃ y, int j y)) as [[y spec]|noy]; eauto.
          exists (ν x j).
          right; firstorder. }
        exists v.
        apply IH.
        revert pre.
        apply uf_sub.
        unfold extent.
        intros j [w holds]; cbn in *.
        destruct (v_spec j) as [case|case].
        - revert case; apply interpret_formula_local.
          intros y iny.
          unfold update.
          destruct (x =? y); trivial.
        - destruct (case w); apply holds.
      }
    Qed.
    
    Instance extend_proper: Proper (eq ==> (≡) ==> eq ==> iff) extent.
    Proof.
      unfold extent.
      intros ν ? <- φ φ' eqφ ?? <-.
      apply eqφ.
    Qed.
    Instance good_proper: Proper ((≡) ==> eq ==> iff) good.
    Proof.
      unfold good.
      intros φ φ' eqφ ν ? <-.
      rewrite (eqφ ultraproduct ν).
      enough (U (extent ν φ) ↔ U (extent ν φ')) by tauto.
      apply uf_wd; intro.
      now rewrite eqφ.
    Qed.
    
    Theorem łoś_qff `{EM} φ (qffφ: qff φ): ∀ ν, good φ ν.
    Proof.
      induction qffφ using formula_ind_or_not_bot_qff; intro;
        auto using up_pred, up_or, up_not, up_bot.
      now rewrite <- H0.
    Qed.
    Theorem łoś `{EM} (choice: DependentFunctionalChoice)
      φ: ∀ ν, good φ ν.
    Proof.
      induction φ using formula_ind_or_not_bot_exists; intro;
        auto using up_pred, up_or, up_not, up_bot, up_exists.
      now rewrite <- H0.
    Qed.
  End Ultraproduct.
  
  Section Compactness.
    Context {I: Type} (Φ: I → formula).
    Definition sat := ∃ σ, ∀ ν, ∀ i, interpret_formula σ ν (Φ i).
    Definition finite_sat := ∀ L, ∃ σ, ∀ ν,
      Forall (λ i, interpret_formula σ ν (Φ i)) L.
    
    Lemma compactness_forward: sat → finite_sat.
    Proof.
      intros [σ all_sat] L.
      exists σ.
      intro.
      apply Forall_forall; auto.
    Qed.
    
    Context `{EM}.
    Context (choice: ∀ A B, SetoidFunctionalChoice_on A B).
    Lemma functional_choice: FunctionalChoice.
    Proof.
      intros A B R R_nonempty.
      destruct (choice A B eq R _) as [f f_spec]; eauto.
      - now intros ??? <-.
      - exists f.
        intro; destruct (f_spec x); trivial.
    Qed.
    Lemma dependent_functional_choice: DependentFunctionalChoice.
    Proof.
      apply non_dep_dep_functional_choice, functional_choice.
    Qed.
    
    Section Backward.
      Notation J := (list I).
      Context (M: J → structure).
      Context (M_spec: ∀ j ν, Forall (λ i, interpret_formula (M j) ν (Φ i)) j).
      Section Ultrafilter.
        Context (U: (J → Prop) → Prop) (Uuf: Ultrafilter (J → Prop) sub U).
        Context (U_spec: ∀ j, U (λ k, incl j k)).
        Lemma satisfies_each_formula i: ∀ ν,
          interpret_formula (ultraproduct (U:=U) M) ν (Φ i).
        Proof.
          intro.
          apply łoś; auto using dependent_functional_choice.
          { exact (i::nil). }
          unfold extent.
          apply (uf_sub (λ j, incl (i::nil) j)); auto.
          intros x inx.
          specialize (M_spec x (λ y, ν y x)).
          rewrite Forall_forall in M_spec.
          apply M_spec, inx; left; trivial.
        Qed.
      End Ultrafilter.
      
      Definition setoid_rel_choice A B :=
        gen_setoid_fun_choice_imp_gen_setoid_rel_choice A B (choice A B).

      Lemma proper_filter_in_ultrafilter U (Uprop: ProperFilter (J → Prop) sub U):
        ∃ U', Ultrafilter _ sub U' ∧ ∀ x, U x → U' x.
      Proof.
        apply (ultrafilter _ _ H
          (@zorns_lemma H setoid_rel_choice) (λ _, False)); auto.
        destruct 1.
      Qed.
      
      Corollary model_exists: ∃ σ, ∀ ν i, interpret_formula σ ν (Φ i).
      Proof.
        set (filt (p: J → Prop) := ∃ j, ∀ k, incl j k → p k).
        assert (filt_proper: ProperFilter _ sub filt). {
          split. split.
          - intros ?? sub [j j_spec].
            exists j.
            firstorder.
          - intros * [j₁ spec₁] [j₂ spec₂].
            exists (λ k, x k ∧ y k).
            split; [|firstorder].
            exists (j₁ ++ j₂).
            intros k incl.
            split.
            + apply spec₁.
              intros u inu.
              apply incl, in_app_iff; auto.
            + apply spec₂.
              intros u inu.
              apply incl, in_app_iff; auto.
          - exists (λ _, False).
            intros [j jspec].
            apply (jspec j), incl_refl.
        }
        destruct (proper_filter_in_ultrafilter filt filt_proper) as
          [U [Uultra Uspec]].
        exists (ultraproduct (U:=U) M).
        intros.
        apply (satisfies_each_formula U Uultra).
        intro.
        apply Uspec; red.
        exists j; auto.
      Qed.
    End Backward.
    
    Theorem compactness: sat ↔ finite_sat.
    Proof.
      split; auto using compactness_forward.
      unfold finite_sat; intro fsat.
      destruct (functional_choice (list I) structure
        (λ j M, ∀ ν, Forall (λ i, interpret_formula M ν (Φ i)) j) fsat)
        as [M M_spec].
      apply (model_exists M), M_spec.
    Qed.
    
    Lemma not_forall {A} (P: A → Prop): (¬∀ x, P x) ↔ ∃ x, ¬P x.
    Proof.
      split.
      - intro contra; destruct (em (∃ x, ¬P x)) as [|none]; auto.
        contradict contra; intro.
        destruct (em (P x)); auto.
        destruct none; eauto.
      - intros [x notx] contra; firstorder.
    Qed.
    Lemma not_exists {A} (P: A → Prop): (¬∃ x, P x) ↔ ∀ x, ¬P x.
    Proof. firstorder. Qed.
    
    Corollary compactness_unsat:
      (∀ σ, ∃ ν i, ¬interpret_formula σ ν (Φ i)) ↔
      (∃ L, ∀ σ, ∃ ν i, In i L ∧ ¬interpret_formula σ ν (Φ i)).
    Proof.
      transitivity (¬sat). {
        unfold sat.
        rewrite not_exists.
        setoid_rewrite not_forall.
        setoid_rewrite not_forall.
        reflexivity.
      }
      rewrite compactness.
      unfold finite_sat.
      rewrite not_forall.
      setoid_rewrite not_exists.
      setoid_rewrite not_forall.
      apply exists_iff; intro L.
      apply forall_iff; intro σ.
      apply exists_iff; intro ν.
      rewrite <- Exists_Forall_neg by (intro; apply em).
      now rewrite <- Exists_exists.
    Qed.
  End Compactness.
End FirstOrderLogic.

Module Import Notation.
  Infix "'∧" := (fand _) (at level 50).
  Infix "'∨" := (for_ _) (at level 50).
  Infix "'→" := (fimp _) (at level 55).
  Notation "'¬ φ" := (fnot _ φ) (at level 40).
  Notation "'∀ x , φ" := (fforall _ x φ) (at level 60).
  Notation "'∃ x , φ" := (fexists _ x φ) (at level 60).
  Notation "'⊥" := (fbot _).
  Infix "=?" := (var_eqb _) (at level 70).
  Notation "∅" := (var_set_empty _).
  Infix "∪" := (var_set_union _) (at level 50, left associativity).
  Notation "(∪)" := (var_set_union _) (only parsing).
  Infix "∩" := (var_set_inter _) (at level 40, left associativity).
  Notation "(∩)" := (var_set_inter _) (only parsing).
  Infix "∖" := (var_set_diff _) (at level 40, left associativity).
  Notation "(∖)" := (var_set_diff _) (only parsing).
  Notation "{[ x ]}" := (var_set_singleton _ x).
  Notation "{[ x1 ; .. ; xn ; y ]}" := ({[ x1 ]} ∪ .. ({[ xn ]} ∪ {[ y ]}) ..).
  Infix "∈" := (var_set_In _) (at level 70).
  Notation "(∈)" := (var_set_In _) (only parsing).
  Notation "(∉)" := (λ x y, ¬x ∈ y).
  Infix "∉" := (∉) (at level 70).
  Infix "=?" := (var_eqb _) (at level 70).
End Notation.
Arguments free {_ _ _} _.
Arguments bound {_ _ _} _.
Arguments subst {_ _ _} _ _.
Arguments αrenaming {_} _ _.
Arguments interpret_term {_} _ _ _.
Arguments interpret_formula {_} _ _ _.
Arguments update {_} _ _ _ _.
Arguments var_eq {_} _ _.
Arguments universe {_} _.
Arguments interpret_func {_} _.
Arguments interpret_pred {_} _.

Section NameBinding.
  (* The horror! *)
  Context {ℓ: language}.
  Definition set_eq s₁ s₂ := ∀ x: Var ℓ, x ∈ s₁ ↔ x ∈ s₂.
  Definition subset s₁ s₂ := ∀ x: Var ℓ, x ∈ s₁ → x ∈ s₂.
  Global Instance: Equivalence set_eq.
  Proof. split; red; unfold set_eq; firstorder trivial. Qed.
  Global Instance: PreOrder subset.
  Proof. split; red; unfold subset; firstorder trivial. Qed.
  Global Instance: PartialOrder set_eq subset.
  Proof. cbv; firstorder. Qed.
  Global Instance: Proper (set_eq ==> set_eq ==> set_eq) (∪).
  Proof.
    unfold set_eq; intros ???????; rewrite !set_union; firstorder trivial.
  Qed.
  
  Global Instance αfree: Proper (αrenaming ==> set_eq) free.
  Proof.
    induction 1; [|reflexivity|easy|etransitivity; eauto].
    induction H; cbn.
  Qed.
End NameBinding.

Section ExtendLang.
  Context {ℓ₁ ℓ₂: language}.
  Context (fv: Var ℓ₁ → Var ℓ₂) (ff: Func ℓ₁ → Func ℓ₂) (fp: Pred ℓ₁ → Pred ℓ₂).
  Context (af: ∀ f, Func_arity ℓ₁ f = Func_arity ℓ₂ (ff f)).
  Context (ap: ∀ p, Pred_arity ℓ₁ p = Pred_arity ℓ₂ (fp p)).
  Definition cast_func {A} f a := eq_rect (Func_arity ℓ₁ f) (Vector.t A) a
    (Func_arity ℓ₂ (ff f)) (af f).
  Definition cast_pred {A} p a := eq_rect (Pred_arity ℓ₁ p) (Vector.t A) a
    (Pred_arity ℓ₂ (fp p)) (ap p).
  Fixpoint map_term (t: term ℓ₁) {struct t}: term ℓ₂ :=
    match t return term ℓ₂ with
    | tvar _ v => tvar ℓ₂ (fv v)
    | tfunc _ f a => tfunc ℓ₂ (ff f) (cast_func f (Vector.map map_term a))
    end.
  Fixpoint map_formula (φ: formula ℓ₁): formula ℓ₂ := match φ with
    | fpred _ p a => fpred ℓ₂ (fp p) (cast_pred p (Vector.map map_term a))
    | φ₁ '∧ φ₂ => map_formula φ₁ '∧ map_formula φ₂
    | φ₁ '∨ φ₂ => map_formula φ₁ '∨ map_formula φ₂
    | φ₁ '→ φ₂ => map_formula φ₁ '→ map_formula φ₂
    | '¬ φ => '¬ map_formula φ
    | '∀ x, φ => '∀ (fv x), map_formula φ
    | '∃ x, φ => '∃ (fv x), map_formula φ
    | '⊥ => '⊥
    end.
  
  Context (σ₁: structure ℓ₁) (σ₂: structure ℓ₂).
  Context (fU: universe σ₁ → universe σ₂).
  Context (preserves_f:
    ∀ f a, fU (interpret_func σ₁ f a) =
      interpret_func σ₂ (ff f) (cast_func f (Vector.map fU a))).
  Context (preserves_p:
    ∀ p a, interpret_pred σ₁ p a ↔
      interpret_pred σ₂ (fp p) (cast_pred p (Vector.map fU a))).
  Lemma push_cast {A B n n'} (f: A → B) (H: n = n') v:
    eq_rect n (Vector.t B) (Vector.map f v) n' H =
    Vector.map f (eq_rect n (Vector.t A) v n' H).
  Proof. destruct H; trivial. Qed.
  Lemma preserves_term t ν₁ ν₂ (preserves_ν: ∀ v, fU (ν₁ v) = ν₂ (fv v)):
    fU (interpret_term σ₁ ν₁ t) = interpret_term σ₂ ν₂ (map_term t).
  Proof.
    induction t; cbn; auto.
    rewrite preserves_f.
    f_equal.
    unfold cast_func.
    rewrite <- push_cast; f_equal.
    rewrite !vector_map_map.
    apply vector_map_Forall; trivial.
  Qed.
  
  Context (fU_sur: ∀ y, ∃ x, fU x = y).
  Context (fv_inj: ∀ v₁ v₂, (v₁ =? v₂) = (fv v₁ =? fv v₂)).
  Lemma preserves_interpret φ: ∀ ν₁ ν₂
    (preserves_ν: ∀ v, fU (ν₁ v) = ν₂ (fv v)),
    interpret_formula σ₁ ν₁ φ ↔ interpret_formula σ₂ ν₂ (map_formula φ).
  Proof.
    induction φ; intros; cbn;
      try now rewrite ?IHφ, ?IHφ1, ?IHφ2.
    - rewrite preserves_p.
      unfold cast_pred.
      rewrite <- push_cast.
      f_equiv; f_equal.
      rewrite !vector_map_map.
      apply vector_map_ext.
      intro t; apply preserves_term, preserves_ν.
    - split.
      + intros pre w₂.
        destruct (fU_sur w₂) as [w₁ <-].
        apply (IHφ (update σ₁ v w₁ ν₁)); auto.
        intros w.
        unfold update.
        rewrite <- fv_inj.
        destruct (v =? w); auto.
      + intros pre w₁.
        apply (IHφ _ (update σ₂ (fv v) (fU w₁) ν₂)); auto.
        intros w.
        unfold update.
        rewrite <- fv_inj.
        destruct (v =? w); auto.
    - split.
      + intros [w₁ pre].
        exists (fU w₁).
        apply (IHφ (update σ₁ v w₁ ν₁)); auto.
        intros w.
        unfold update.
        rewrite <- fv_inj.
        destruct (v =? w); auto.
      + intros [w₂ pre].
        destruct (fU_sur w₂) as [w₁ <-].
        exists w₁.
        apply (IHφ _ (update σ₂ (fv v) (fU w₁) ν₂)); auto.
        intros w.
        unfold update.
        rewrite <- fv_inj.
        destruct (v =? w); auto.
  Qed.
End ExtendLang.

Lemma map_term_ext ℓ₁ ℓ₂ fv₁ fv₂ ff₁ ff₂ ffa₁ ffa₂
  (eqfv: ∀ v, fv₁ v = fv₂ v) (eqff: ∀ f, ff₁ f = ff₂ f) t:
  @map_term ℓ₁ ℓ₂ fv₁ ff₁ ffa₁ t = map_term fv₂ ff₂ ffa₂ t.
Proof.
  induction t; cbn; try congruence.
  unfold cast_func.
  generalize (ffa₁ f) as n₁, (ffa₂ f) as n₂.
  rewrite <- (eqff f).
  intros; f_equal.
  revert n₂.
  rewrite <- n₁.
  apply K_dec. { apply Nat.eq_decidable. }
  cbn.
  apply vector_map_Forall, IHa.
Qed.

Lemma map_formula_ext ℓ₁ ℓ₂ fv₁ fv₂ ff₁ ff₂ ffa₁ ffa₂ fp₁ fp₂ fpa₁ fpa₂
  (eqfv: ∀ v, fv₁ v = fv₂ v) (eqff: ∀ f, ff₁ f = ff₂ f)
  (eqfp: ∀ p, fp₁ p = fp₂ p) φ:
  @map_formula ℓ₁ ℓ₂ fv₁ ff₁ fp₁ ffa₁ fpa₁ φ =
  map_formula fv₂ ff₂ fp₂ ffa₂ fpa₂ φ.
Proof.
  induction φ; cbn; try congruence.
  f_equal.
  unfold cast_pred.
  generalize (fpa₁ p) as n₁, (fpa₂ p) as n₂.
  rewrite <- (eqfp p).
  intros; f_equal.
  revert n₂.
  rewrite <- n₁.
  apply K_dec. { apply Nat.eq_decidable. }
  cbn.
  apply vector_map_ext.
  intro t.
  apply map_term_ext; auto.
Qed.

Section ExtendLangKeepVar.
  Context {ℓ: language} {F₂ P₂: Type} (FA₂: F₂ → nat) (PA₂: P₂ → nat).
  
  Definition extend_lang := {|
    Var := Var ℓ;
    Func := F₂;
    Pred := P₂;
    VarSet := VarSet ℓ;
    var_set_empty := var_set_empty ℓ;
    var_set_union := var_set_union ℓ;
    var_set_inter := var_set_inter ℓ;
    var_set_diff := var_set_diff ℓ;
    var_set_singleton := var_set_singleton ℓ;
    var_set_In := var_set_In ℓ;
    var_set_empty_spec := var_set_empty_spec ℓ;
    var_set_union_spec := var_set_union_spec ℓ;
    var_set_inter_spec := var_set_inter_spec ℓ;
    var_set_diff_spec := var_set_diff_spec ℓ;
    var_set_singleton_spec := var_set_singleton_spec ℓ;
    var_eqb := var_eqb ℓ;
    var_eq_spec := var_eq_spec ℓ;
    Func_arity := FA₂;
    Pred_arity := PA₂
  |}.
  Context (ff: Func ℓ → F₂) (af: ∀ f, Func_arity ℓ f = FA₂ (ff f)).
  Definition extend_term := @map_term ℓ extend_lang id ff af.
  Context (fp: Pred ℓ → P₂) (ap: ∀ p, Pred_arity ℓ p = PA₂ (fp p)).
  Definition extend_formula := @map_formula ℓ extend_lang id ff fp af ap.
  
  Context (σ₁: structure ℓ) (σ₂: structure extend_lang).
  Context (fU: universe σ₁ → universe σ₂).
  Context (preserves_f:
    ∀ f a, fU (interpret_func σ₁ f a) =
      interpret_func σ₂ (ff f)
      (cast_func (ℓ₂ := extend_lang) ff af f (Vector.map fU a))).
  Context (preserves_p:
    ∀ p a, interpret_pred σ₁ p a ↔
      interpret_pred σ₂ (fp p)
      (cast_pred (ℓ₂ := extend_lang) fp ap p (Vector.map fU a))).

  Lemma extend_preserves_term t ν₁ ν₂ (preserves_ν: ∀ v, fU (ν₁ v) = ν₂ v):
    fU (interpret_term σ₁ ν₁ t) = interpret_term σ₂ ν₂ (extend_term t).
  Proof. now apply preserves_term. Qed.
  
  Context (fU_sur: ∀ y, ∃ x, fU x = y).
  Lemma extend_preserves_interpret φ ν₁ ν₂
    (preserves_ν: ∀ v, fU (ν₁ v) = ν₂ v):
    interpret_formula σ₁ ν₁ φ ↔ interpret_formula σ₂ ν₂ (extend_formula φ).
  Proof. apply preserves_interpret with fU; auto. Qed.
End ExtendLangKeepVar.

Section Deduction.
  Section Defs.
    Context {ℓ: language}.
    Definition inst x t (φ: formula ℓ) :=
      subst (λ y, if x =? y then Some t else None) φ.
    Inductive hilbert_axioms: formula ℓ → Prop :=
      | hconst φ₁ φ₂: hilbert_axioms (φ₁ '→ (φ₂ '→ φ₁))
      | hshort φ₁ φ₂ φ₃:
        hilbert_axioms ((φ₁ '→ (φ₂ '→ φ₃)) '→ ((φ₁ '→ φ₂) '→ (φ₁ '→ φ₃)))
      | hcontra φ₁ φ₂: hilbert_axioms ((('¬ φ₂) '→ ('¬ φ₁)) '→ (φ₁ '→ φ₂))
      | hbot φ: hilbert_axioms ('⊥ '→ φ)
      | hinc φ: hilbert_axioms (φ '→ (('¬ φ) '→ '⊥))
      | handl φ₁ φ₂: hilbert_axioms ((φ₁ '∧ φ₂) '→ φ₁)
      | handr φ₁ φ₂: hilbert_axioms ((φ₁ '∧ φ₂) '→ φ₂)
      | handi φ₁ φ₂: hilbert_axioms (φ₁ '→ (φ₂ '→ (φ₁ '∧ φ₂)))
      | hore φ₁ φ₂ φ₃:
        hilbert_axioms ((φ₁ '→ φ₃) '→ ((φ₂ '→ φ₃) '→ ((φ₁ '∨ φ₂) '→ φ₃)))
      | horl φ₁ φ₂: hilbert_axioms (φ₁ '→ (φ₁ '∨ φ₂))
      | horr φ₁ φ₂: hilbert_axioms (φ₂ '→ (φ₁ '∨ φ₂))
      | halli x φ (not_free: x ∉ free φ): hilbert_axioms (φ '→ '∀ x, φ)
      | halle x t φ (good: ∀ y, y ∈ free t → y ∈ bound φ → False): 
        hilbert_axioms (('∀ x, φ) '→ inst x t φ)
      | hallm x φ₁ φ₂:
        hilbert_axioms (('∀ x, φ₁ '→ φ₂) '→ (('∀ x, φ₁) '→ '∀ x, φ₂))
      | hexi x t φ (good: ∀ y, y ∈ free t → y ∈ bound φ → False):
        hilbert_axioms (inst x t φ '→ '∃ x, φ)
      | hexe x φ₁ φ₂ (not_free: x ∉ free φ₂):
        hilbert_axioms (('∀ x, (φ₁ '→ φ₂)) '→ (('∃ x, φ₁) '→ φ₂))
      | hgen x φ: hilbert_axioms φ → hilbert_axioms ('∀ x, φ).
    Inductive hilbert (Φ: formula ℓ → Prop): formula ℓ → Prop :=
      | hassum φ (assumed: Φ φ): hilbert Φ φ
      | haxiom φ (axiom: hilbert_axioms φ): hilbert Φ φ
      | hmp φ₁ φ₂ (der₁: hilbert Φ (φ₁ '→ φ₂)) (der₂: hilbert Φ φ₁): hilbert Φ φ₂
      | halpha φ₁ φ₂ (α: αrenaming φ₁ φ₂): hilbert Φ φ₁ → hilbert Φ φ₂.
      
    Lemma interpret_inst σ ν x (t: term ℓ) φ
      (good: ∀ y, y ∈ free t → y ∈ bound φ → False):
      interpret_formula σ ν (inst x t φ) ↔
      interpret_formula σ (update σ x (interpret_term σ ν t) ν) φ.
    Proof.
      unfold inst.
      rewrite interpret_formula_subst.
      - apply interpret_formula_local.
        intros y iny.
        unfold interpret_subst, update.
        destruct (x =? y); trivial.
      - intros y iny x' t'.
        destruct (var_eq x x') as [<-|]; intros [=<-]; eauto.
    Qed.
    
    Definition models (Φ: formula ℓ → Prop) φ :=
      ∀ σ ν, (∀ φ', Φ φ' → interpret_formula σ ν φ') →
      interpret_formula σ ν φ.
    Theorem hilbert_sound `{EM} Φ φ: hilbert Φ φ → models Φ φ.
    Proof.
      induction 1; try solve [intros ???; cbn; auto; tauto].
      - intros ?? _.
        revert ν.
        induction axiom; intro; try solve [cbn; auto; tauto].
        + destruct (em (interpret_formula σ ν φ₂)); cbn; tauto.
        + intros holds v.
          revert holds.
          apply interpret_formula_local.
          intros y iny.
          unfold update.
          now destruct (var_eq_spec ℓ x y) as [<-|neq].
        + intros holds; rewrite interpret_inst; auto.
        + intros holds.
          rewrite interpret_inst in holds; auto.
          cbn; eauto.
        + intros func [v holds].
          apply (interpret_formula_local ℓ σ φ₂ (update σ x v ν)).
          * intros y iny.
            unfold update.
            now destruct (var_eq_spec ℓ x y) as [<-|neq].
          * apply func, holds.
      - intros σ ν pre.
        apply (IHhilbert1 σ ν pre).
        apply (IHhilbert2 σ ν pre).
      - intros ν σ pre%IHhilbert.
        revert pre.
        apply αrenaming_equivalence in α.
        apply α.
    Qed.
    
    Hint Constructors hilbert hilbert_axioms.
    Lemma deduce_id Φ φ: hilbert Φ (φ '→ φ).
    Proof.
      apply (hmp Φ (φ '→ ((φ '→ φ) '→ φ))); [|auto].
      apply (hmp Φ (φ '→ (((φ '→ φ) '→ φ) '→ φ))); auto.
    Qed.
    
    Lemma weaken Φ φ: hilbert Φ φ → ∀ (Φ': _ → Prop),
       (∀ ψ, Φ ψ → Φ' ψ) → hilbert Φ' φ.
    Proof.
      induction 1; auto; eauto.
    Qed.
    
    Lemma deduction_step_fw Φ φ ψ:
      hilbert Φ (φ '→ ψ) → hilbert (λ χ, Φ χ ∨ φ = χ) ψ.
    Proof.
      intro pre.
      eapply (hmp _ φ); [|eauto].
      eapply weaken; try eassumption.
      left; trivial.
    Qed.
    
    Theorem deduction_step_bw Φ ξ ψ:
      hilbert (λ χ, Φ χ ∨ ξ = χ) ψ → hilbert Φ (ξ '→ ψ).
    Proof.
      induction 1; [eauto 3..].
      - destruct assumed as [?|<-].
        + eapply hmp; [apply haxiom, hconst|auto].
        + apply deduce_id.
      - eapply hmp; [apply haxiom, hconst|auto].
      - apply (hmp Φ (ξ '→ φ₁)); trivial.
        apply (hmp Φ (ξ '→ (φ₁ '→ φ₂))); auto.
      - revert IHhilbert; apply halpha.
        clear -α.
        induction α.
        + constructor.
          apply αimpr, H.
        + constructor 2.
        + constructor 3; trivial.
        + econstructor 4; eauto.
    Qed.
    
    Lemma deduction_step Φ φ ψ:
      hilbert Φ (φ '→ ψ) ↔ hilbert (λ χ, Φ χ ∨ φ = χ) ψ.
    Proof. split; auto using deduction_step_bw, deduction_step_fw. Qed.
    
    Lemma hilbert_local Φ φ: hilbert Φ φ → ∃ L, Forall Φ L ∧
      hilbert (λ φ, In φ L) φ.
    Proof.
      induction 1; try solve [exists nil; auto].
      - exists (φ :: nil); cbn; auto using Forall.
      - destruct IHhilbert1 as [L₁ [all₁ IH₁]], IHhilbert2 as [L₂ [all₂ IH₂]].
        exists (L₁ ++ L₂).
        split.
        + rewrite Forall_forall in *.
          intros x [?|?]%in_app_iff; auto.
        + apply (hmp _ φ₁).
          * apply (weaken (λ φ, In φ L₁)); auto.
            intros; apply in_or_app; auto.
          * apply (weaken (λ φ, In φ L₂)); auto.
            intros; apply in_or_app; auto.
      - destruct IHhilbert as [L [all ded]].
        exists L; split; trivial.
        revert ded; apply halpha, α.
    Qed.
    
    Corollary hilbert_reduce_to_local Φ φ: hilbert Φ φ ↔ ∃ L, Forall Φ L ∧
      hilbert (λ φ, In φ L) φ.
    Proof.
      split.
      - apply hilbert_local.
      - intros [L [Lsub pre]].
        apply (weaken (λ φ, In φ L)); auto.
        rewrite Forall_forall in Lsub; auto.
    Qed.
    
    Lemma hilbert_wd: Proper (pointwise_relation _ iff ==> eq ==> iff)
      hilbert.
    Proof.
      apply proper_sym_impl_iff_2; [apply _..|].
      intros Φ Φ' eqΦ φ ? <-.
      intro; eapply weaken; eauto.
      intro; apply eqΦ.
    Qed.

    Lemma deduction_core Φ L φ:
      hilbert Φ (fold_right (@fimp ℓ) φ L) ↔ hilbert (λ x, Φ x ∨ In x L) φ.
    Proof.
      revert Φ φ.
      induction L as [|ψ L IH]; intros; cbn.
      - apply hilbert_wd; hnf; intuition.
      - rewrite deduction_step, IH.
        apply hilbert_wd; hnf; intuition.
    Qed.
    
    Theorem deduction Φ φ:
      hilbert Φ φ ↔
      ∃ L, Forall Φ L ∧ hilbert (λ _, False) (fold_right (@fimp ℓ) φ L).
    Proof.
      rewrite hilbert_reduce_to_local.
      apply exists_iff; intro L.
      apply and_iff_compat_l.
      rewrite deduction_core.
      apply hilbert_wd; hnf; intuition.
    Qed.
    
    Lemma model_alt `{EM} Φ φ:
      models Φ φ ↔ models (λ ψ, Φ ψ ∨ '¬ φ = ψ) '⊥.
    Proof.
      split; intros pre σ ν holds.
      - assert (interpret_formula σ ν φ) as pos.
        { apply pre; auto. }
        assert (interpret_formula σ ν ('¬ φ)) as neg.
        { apply holds; auto. }
        contradiction.
      - destruct (em (interpret_formula σ ν φ)) as [|contra]; trivial.
        destruct (pre σ ν).
        intros ψ [case|case]; auto.
        subst; trivial.
    Qed.
    
    Lemma hilbert_alt Φ φ:
      hilbert Φ φ → hilbert (λ ψ, Φ ψ ∨ '¬ φ = ψ) '⊥.
    Proof.
      intro der.
      apply (hmp _ ('¬φ)); [|auto].
      apply (hmp _ φ); auto.
      eapply weaken; eauto.
    Qed.
  End Defs.
End Deduction.

Module Type DeductionCompleteSpec.
  Parameter hilbert_complete: EM → SetoidFunctionalChoice →
    ∀ ℓ (Φ: formula ℓ → Prop) (φ: formula ℓ), models Φ φ → hilbert Φ φ.
End DeductionCompleteSpec.

Module DeductionComplete: DeductionCompleteSpec.
  (** Part 1: Henkin sets for the infinite variable case. *)
  Section Henkin.
    Context {ℓ: language} (Φ: formula ℓ → Prop) {has_em: EM}.
    Context (fresh: VarSet ℓ → Var ℓ).
    Context (is_fresh: ∀ S, ¬fresh S ∈ S).
    Record good (Ψ: formula ℓ → Prop) := {
      good_contains_Φ: ∀ φ, Φ φ → Ψ φ;
      good_consistent: ¬hilbert Ψ '⊥
    }.
    
    Record henkin (Ψ: formula ℓ → Prop) := {
      henkin_good :> good Ψ;
      henkin_deductive: ∀ φ, hilbert Ψ φ → Ψ φ;
      henkin_complete: ∀ φ, Ψ φ ∨ Ψ ('¬ φ);
      henkin_witnesses: ∀ x φ, Ψ ('∃ x, φ) ↔
        ∃ t, (∀ x, ¬x ∈ free t) ∧ Ψ (inst x t φ)
    }.
    Arguments good_contains_Φ {_}.
    Arguments good_consistent {_}.
    Arguments henkin_deductive {_}.
    Arguments henkin_complete {_}.
    
    Lemma henkin_not_both Ψ φ (H: henkin Ψ): Ψ φ → Ψ ('¬ φ) → False.
    Proof.
      intros pos neg.
      destruct (good_consistent H).
      eapply (hilbert_wd (λ ψ, Ψ ψ ∨ '¬ φ = ψ)); [|reflexivity|].
      + intro ψ; intuition (subst; trivial).
      + apply hilbert_alt.
        constructor; trivial.
    Qed.
    
    Lemma henkin_cases Ψ φ (H: henkin Ψ):
      (Ψ φ ∧ ¬Ψ ('¬ φ)) ∨
      (¬Ψ φ ∧ Ψ ('¬ φ)).
    Proof.
      destruct (henkin_complete H φ) as [case|case];
        eauto using henkin_not_both.
    Qed.
    
    Program Definition henkin_structure Ψ :=
      Build_structure ℓ { t: term ℓ | ∀ x, x ∉ free t }
        (λ f a, tfunc ℓ f (Vector.map (@proj1_sig _ _) a))
        (λ p a, Ψ (fpred ℓ p (Vector.map (@proj1_sig _ _) a))).
    Next Obligation.
      revert x; unfold not.
      apply free_func.
      induction a as [|[a Ha] k v]; cbn; constructor; trivial.
    Qed.
    
    Lemma henkin_term Ψ t ν:
      proj1_sig (interpret_term (henkin_structure Ψ) ν t) =
      subst (λ v, Some (proj1_sig (ν v))) t.
    Proof.
      induction t; cbn; trivial.
      f_equal.
      rewrite vector_map_map.
      apply vector_map_Forall; trivial.
    Qed.
    
    Lemma henkin_terms Ψ n (t: (term ℓ)^n) ν:
      Vector.map (λ t, proj1_sig (interpret_term (henkin_structure Ψ) ν t)) t =
      Vector.map (subst (λ v, Some (proj1_sig (ν v)))) t.
    Proof.
      apply vector_map_ext.
      intro; apply henkin_term.
    Qed.
    
    Definition var' Ψ (ν: Var ℓ → universe (henkin_structure Ψ)) v :=
      Some (proj1_sig (ν v)).
    Definition var Ψ (ν: Var ℓ → universe (henkin_structure Ψ)) (φ: formula ℓ) :=
      subst (var' Ψ ν) φ.

    Lemma inst_remove Ψ v x (t: universe (henkin_structure Ψ)) ν:
      inst v (proj1_sig t) (subst (remove ℓ v (var' Ψ ν)) x) =
      var Ψ (update (henkin_structure Ψ) v t ν) x.
    Proof.
      unfold var, update, remove, inst, var'.
      rewrite formula_subst_subst.
      - apply formula_subst_local.
        intros y _.
        unfold merge_subst.
        destruct (var_eq_spec ℓ v y) as [<-|neq]; trivial.
        f_equal.
        rewrite <- (term_subst_empty ℓ (proj1_sig (ν y))) at 2.
        apply term_subst_local.
        intros ? []%(proj2_sig (ν y)).
      - intros y z t'.
        destruct (v =? y); intros [=] _; subst.
        apply (proj2_sig (ν y)).
    Qed.
    
    Lemma inst_noop x φ: inst x (tvar ℓ x) φ = φ.
    Proof.
      unfold inst.
      induction φ; cbn in *; try congruence.
      - f_equal.
        induction a; cbn; f_equal; trivial.
        clear.
        induction h; cbn; f_equal.
        + destruct (var_eq_spec ℓ x v) as [<-|]; trivial.
        + rewrite <- (vector_map_id a) at 2.
          apply vector_map_Forall, IHa.
      - f_equal.
        destruct (var_eq_spec ℓ x v) as [<-|neq].
        + rewrite <- (formula_subst_empty ℓ φ) at 2.
          apply formula_subst_local.
          intros y _.
          unfold remove.
          destruct var_eqb; trivial.
        + rewrite <- IHφ at 2.
          apply formula_subst_local.
          intros y _.
          unfold remove.
          destruct (var_eq_spec ℓ v y) as [<-|neq']; trivial.
          destruct (var_eq_spec ℓ x v); congruence.
      - f_equal.
        destruct (var_eq_spec ℓ x v) as [<-|neq].
        + rewrite <- (formula_subst_empty ℓ φ) at 2.
          apply formula_subst_local.
          intros y _.
          unfold remove.
          destruct var_eqb; trivial.
        + rewrite <- IHφ at 2.
          apply formula_subst_local.
          intros y _.
          unfold remove.
          destruct (var_eq_spec ℓ v y) as [<-|neq']; trivial.
          destruct (var_eq_spec ℓ x v); congruence.
    Qed.
    
  End Henkin.
End DeductionComplete.