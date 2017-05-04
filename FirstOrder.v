(**
 First-order logic.

 This provides a deep embedding of first-order logic, with the semantics
 given by a direct translation to Coq.
 
 © 2017 Johannes Kloos

 This library requires Coq 8.6. *)
From Coq.Classes Require Import Equivalence Morphisms SetoidClass.
From Coq Require Import Utf8 ChoiceFacts ClassicalFacts Relations.
From misc Require Import Vectors.
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
  Infix "=?" := (var_eqb lang) (at level 60).
  
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
  Instance αrenaming_equivalence: subrelation αrenaming equivalence.
  Proof.
    induction 1.
    - now apply αstep_equivalence.
    - reflexivity.
    - now symmetry.
    - now transitivity y.
  Qed.
  
  
End FirstOrderLogic.