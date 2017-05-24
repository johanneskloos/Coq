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
