(**
 A proof of Zorn's Lemma and the Well-Ordering Theorem.

 Based on Kneser's short proof.

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
From Coq Require Import
  Relations Equivalence Morphisms Utf8 ChoiceFacts ClassicalFacts.
From Coq.Program Require Import Basics.
From misc Require Import MoreChoice.

(** * The types of the statements *)
(** The statement of Zorn's Lemma. *)

Definition ZornsLemma
  {A} (R: relation A) {preR: PreOrder R}
  (chains_have_upper_bounds:
    ∀ (C: A → Prop), (∀ x y, C x → C y → R x y ∨ R y x) →
    ∃ m, ∀ x, C x → R x m) :=
    ∃ m, ∀ x, R m x → R x m.

(** The definition of a well-order. *)

Record well_order {A} (eqA ltA: relation A) := {
  eqA_equiv :> Equivalence eqA;
  ltA_strict :> StrictOrder ltA;
  ltA_wellfounded: well_founded ltA;
  ltA_proper :> Proper (eqA ==> eqA ==> iff) ltA;
  ltA_total: ∀ x y, eqA x y ∨ ltA x y ∨ ltA y x
}.

(** This module contains the proofs.

 Since they are long and the lemmas are not very useful outside
 the proofs, we encapsulate them away. *)

Module Type Proofs.
  Record well_ordered {A} (le equ: relation A) (X: { S | Proper (equ ==> iff) S }) :=
    { wo_total: ∀ x y, proj1_sig X x → proj1_sig X y → le x y ∨ le y x;
      wo_minima: ∀ (Y: { S | Proper (equ ==> iff) S }),
          (∀ x, proj1_sig Y x → proj1_sig X x) →
          (∃ x, proj1_sig Y x) →
          ∃ m, proj1_sig Y m ∧ ∀ x, proj1_sig Y x → le m x }.
  Axiom zorns_lemma: ∀ {A} (le equ lt: relation A),
    PreOrder le →
    (∀ x y, equ x y ↔ le x y ∧ le y x) →
    (∀ x y, lt x y ↔ le x y ∧ ¬le y x) →
    excluded_middle →
    GeneralizedSetoidRelationalChoice →
    (∀ (F: { S | Proper (equ ==> iff) S }),
           well_ordered le equ F →
           ∃ m, ∀ x, proj1_sig F x → le x m) →
    ∃ m, ∀ x, le m x → le x m.
  Axiom well_ordering_from_zorns_lemma:
    excluded_middle →
    (∀ A (R: relation A) (pre: PreOrder R)
       (chub: ∀ (C: A → Prop), (∀ x y, C x → C y → R x y ∨ R y x) →
                               ∃ m, ∀ x, C x → R x m),
        ZornsLemma R chub) →
    ∀ {A} (eqA: relation A), Equivalence eqA → ∃ ltA, well_order eqA ltA.
End Proofs.

Module Private: Proofs.
  (* begin hide *)
  Class Le A := le: relation A.
  Class Lt A := lt: relation A.
  Class Equiv A := equ: relation A.
  Infix "≤" := le.
  Infix "<" := lt.
  Infix "≡" := equ (at level 70).
  
  (* Some facts about orders. *)
  Section Orders.
    Context {A} (leA: Le A).
    Definition default_lt: Lt A := λ x y, x ≤ y ∧ ¬y ≤ x.
    Definition default_eq: Equiv A := λ x y, x ≤ y ∧ y ≤ x.
    Context (ltA: Lt A) (equA: Equiv A) {leA_pre: PreOrder le}.
    Hypothesis lt_spec: ∀ x y, x < y ↔ default_lt x y.
    Hypothesis equ_spec: ∀ x y, x ≡ y ↔ default_eq x y.
    
    Instance equ_equivalence: Equivalence equ.
    Proof.
      split; red; intros *; rewrite !equ_spec; unfold default_eq;
        intuition auto with *; etransitivity; eassumption.
    Qed.
    
    Instance partial_order: PartialOrder equ le := equ_spec.
    
    Lemma lt_le_trans x y z: x < y → y ≤ z → x < z.
    Proof.
      rewrite !lt_spec.
      intros [lexy ngexy] leyz; split; [|contradict ngexy];
        etransitivity; eassumption.
    Qed.
    
    Lemma le_lt_trans x y z: x ≤ y → y < z → x < z.
    Proof.
      rewrite !lt_spec.
      intros leyz [lexy ngexy]; split; [|contradict ngexy];
        etransitivity; eassumption.
    Qed.
    
    Instance lt_proper: Proper (equ ==> equ ==> iff) lt.
    Proof.
      apply proper_sym_impl_iff_2; [apply _..|].
      intros x x' [lex gex]%equ_spec y y' [ley gey]%equ_spec ltxy.
      eauto using lt_le_trans, le_lt_trans.
    Qed.
    
    Instance lt_strict: StrictOrder lt.
    Proof.
      split.
      - now intros ? [??]%lt_spec.
      - intros x y z [lexy _]%lt_spec.
        apply le_lt_trans, lexy.
    Qed.
  End Orders.
  
  Section Proof.
    (* We have a partially ordered set, with strict order and equivalence. *)
    Context {A} (leA: Le A) (eqA: Equiv A) (ltA: Lt A).
    Context {preA: PreOrder le} (eqA_spec: ∀ x y, x ≡ y ↔ x ≤ y ∧ y ≤ x).
    Context (ltA_spec: ∀ x y, x < y ↔ x ≤ y ∧ ¬y ≤ x).
    Hypothesis classical: excluded_middle.
    Hypothesis choice: GeneralizedSetoidRelationalChoice.
    
    (* Instantiate facts about the order. *)
    Instance: Equivalence equ := equ_equivalence leA eqA eqA_spec.
    Instance: PartialOrder equ le := partial_order leA eqA eqA_spec.
    Instance: Proper (equ ==> equ ==> iff) lt :=
      lt_proper leA ltA eqA ltA_spec eqA_spec.
    Instance: StrictOrder lt := lt_strict leA ltA ltA_spec.
    
    (* Sets. *)
    Definition set := { S: A → Prop | Proper (equ ==> iff) S }.
    Definition In x (s: set) := proj1_sig s x.
    Infix "∈" := In (at level 70).
    Definition Subset s₁ s₂ := ∀ x, x ∈ s₁ → x ∈ s₂.
    Infix "⊆" := Subset (at level 70).
    
    (* Closed subsets. *)
    Record closed_subset s₁ s₂ := {
      cs_subset: s₁ ⊆ s₂;
      cs_closed: ∀ x y, x ∈ s₂ → y ∈ s₁ → x ≤ y → x ∈ s₁
    }.
    Instance set_le: Le set := closed_subset.
    Instance set_lt: Lt set := default_lt set_le.
    Instance set_eq: Equiv set := default_eq set_le.
    Instance set_le_pre: @PreOrder set le.
    Proof. firstorder eauto. Qed.
    
    Instance: Equivalence equ :=
      equ_equivalence set_le set_eq (λ _ _, reflexivity _).
    Instance: PartialOrder (A:=set) equ le  :=
      partial_order le equ (λ _ _, reflexivity _).
    Instance: Proper (equ ==> equ ==> iff) lt :=
      lt_proper set_le set_lt set_eq (λ _ _, reflexivity _) (λ _ _, reflexivity _).
    Instance: StrictOrder lt :=
      lt_strict set_le set_lt (λ _ _, reflexivity _).
    
    Instance In_le_proper: Proper (equ ==> le ++> impl) In.
    Proof.
      intros x x' eqx [X Xprop] X' subX inx.
      apply subX; cbn in *.
      rewrite <- eqx; trivial.
    Qed.
    Instance: Proper (equ ==> equ ==> iff) In.
    Proof.
      intros x x' eqx X X' [sub sup].
      split; apply In_le_proper; easy.
    Qed.
    Instance: subrelation (A:=set) lt le.
    Proof. firstorder. Qed.
    
    Definition inhabited X := ∃ x, x ∈ X.
    Instance: Proper (equ ==> iff) inhabited.
    Proof. unfold inhabited; solve_proper. Qed.
    Instance: Proper (equ ==> equ ==> iff) Subset.
    Proof. unfold Subset; solve_proper. Qed.
    
    Lemma subset_equ X Y (sub: X ⊆ Y) (sup: Y ⊆ X): X ≡ Y.
    Proof. firstorder. Qed.
    
    (* Well-ordered subsets. *)
    Record well_ordered X := {
      wo_total: ∀ x y, x ∈ X → y ∈ X → x ≤ y ∨ y ≤ x;
      wo_minima: ∀ Y, Y ⊆ X → inhabited Y → ∃ m, m ∈ Y ∧ ∀ x, x ∈ Y → m ≤ x
    }.
    
    Instance: Proper (equ ==> iff) well_ordered.
    Proof.
      apply proper_sym_impl_iff; [apply _|].
      intros X X' eqX [total minima].
      split; setoid_rewrite <- eqX; auto.
    Qed.
    
    Lemma wo_lt_ge X (Xwo: well_ordered X) x y (inx: x ∈ X) (iny: y ∈ X):
      x < y ∨ y ≤ x.
    Proof.
      destruct (classical (y ≤ x)); auto.
      destruct (wo_total X Xwo x y); auto.
      rewrite ltA_spec; auto.
    Qed.
    
    (* The initial prefix lemma. *)
    Program Definition restrict x (X: set): set := λ y, y ∈ X ∧ y < x.
    Next Obligation. Proof. solve_proper. Qed.
    
    #[local] Hint Constructors closed_subset: core.
    
    Lemma initial_prefix X Y (Xwo: well_ordered X) (sub: Y < X):
      ∃ x, x ∈ X ∧ ¬x ∈ Y ∧ Y ≡ restrict x X.
    Proof.
      assert (Proper (equ ==> iff) (λ x, x ∈ X ∧ ¬x ∈ Y)) as diff_impl
        by solve_proper.
      set (exist _ _ diff_impl: set) as diff.
      destruct (wo_minima X Xwo diff) as [m [[inX notinY] lb]].
      - firstorder.
      - destruct (classical (∃ x, x ∈ diff)) as [|none]; trivial.
        destruct sub as [sub [ ]].
        split; [|firstorder].
        intros x inx.
        destruct (classical (x ∈ Y)); trivial.
        contradict none; exists x; split; trivial.
      - exists m; do 2 (split; trivial).
        destruct sub as [[sub closed] neq].
        apply subset_equ; intros y iny.
        + split; auto.
          destruct (wo_lt_ge X Xwo y m) as [|contra]; auto.
          now eapply cs_closed in contra; eauto.
        + destruct iny as [iny bound].
          destruct (classical (y ∈ Y)) as [|contra]; auto.
          enough (y < y) as [ ]%irreflexivity.
          eapply lt_le_trans; eauto.
          apply lb; split; trivial.
    Qed.
    
    Instance: Proper (equ ==> equ ==> equ) restrict.
    Proof.
      unfold restrict.
      intros x x' eqx X X' eqX.
      apply subset_equ; intro y; cbn; rewrite eqx, eqX; trivial.
    Qed.
    
    (* The union of a prefix chain of wo sets is a wo set,
     * and each element of the chain is a prefix of the union. *)
    Section ChainUnion.
      Variable F: set → Prop.
      Hypothesis chain: ∀ S S', F S → F S' → S ≤ S' ∨ S' ≤ S.
      Hypothesis wo: ∀ S, F S → well_ordered S.
      
      Program Definition union: set := λ x, ∃ S, F S ∧ x ∈ S.
      Next Obligation. Proof. solve_proper. Qed.
      
      Lemma prefix_union S (inS: F S): S ≤ union.
      Proof.
        split.
        - exists S; auto.
        - intros ?? [S' [inS' inx]] iny lexy.
          destruct (chain S S') as [[sub cl]|[sub cl]]; eauto.
      Qed.
      
      Lemma union_wo: well_ordered union.
      Proof.
        assert (total: ∀ x y : A, x ∈ union → y ∈ union → x ≤ y ∨ y ≤ x). {
          intros ?? [Sx [inSx inx]] [Sy [inSy iny]].
          destruct (chain Sx Sy) as [[sub _]|[sub _]]; auto;
            [apply (wo_total Sy)|apply (wo_total Sx)]; auto.
        }
        split; trivial.
        intros ? sub [y inh].
        destruct (sub y inh) as [Sy [inSy iny]].
        assert (Proper (equ ==> iff) (λ x, x ∈ Y ∧ x ∈ Sy)) as inter_spec
          by solve_proper.
        set (exist _ _ inter_spec) as inter.
        destruct (wo_minima Sy (wo Sy inSy) inter) as [m [[inm inm'] min]];
          [firstorder..|].
        exists m; split; auto.
        intros x inx.
        destruct (sub x inx) as [Z [inSz inx']].
        destruct (chain Sy Z) as [[sub' cl']|[??]]; eauto;
          [|apply min; split; auto].
        destruct (total m x) as [case|case]; [apply sub; trivial..|auto|].
        apply cl' in case; auto.
        apply min; split; auto.
      Qed.
      
      Lemma union_ub B (bound: ∀ S, F S → S ≤ B): union ≤ B.
      Proof.
        split.
        - intros x [S [inS inx]]; apply (bound S inS), inx.
        - intros ?? inx [S [inS inY]] lexy.
          exists S; split; trivial.
          eapply cs_closed; eauto.
          apply bound, inS.
      Qed.
    End ChainUnion.
    
    Notation "⋃ F" := (union F) (at level 55).
    
    Lemma restrict_well_ordered b X (wo: well_ordered X):
      well_ordered (restrict b X).
    Proof. firstorder. Qed.
    
    (* Theory of g-sets *)
    Section GSets.
      Variable g: set → A → Prop.
      Hypothesis unique: ∀ S b b', g S b → g S b' → b ≡ b'.
      Context (proper: Proper (equ ==> equ ==> iff) g).
      Hypothesis domain: ∀ S, well_ordered S → ∃ b, g S b.
      Hypothesis upper_bound: ∀ S b x, well_ordered S → g S b → x ∈ S → x < b.
      
      Record gset C := {
        C_wo:> well_ordered C;
        C_bounds: ∀ c, c ∈ C → g (restrict c C) c
      }.
      
      Instance gset_proper: Proper (equ ==> iff) gset.
      Proof.
        apply proper_sym_impl_iff; [apply _|].
        intros S S' eqS [wo bounds].
        split; setoid_rewrite <- eqS; trivial.
      Qed.
      
      (* Suspending sets *)
      Program Definition suspend S x: set := λ y, y ∈ S ∨ x ≡ y.
      Next Obligation. Proof. solve_proper. Qed.
      Instance: Proper (equ ==> equ ==> equ) suspend.
      Proof.
        intros S S' eqS x x' eqx.
        apply subset_equ; intro y; unfold suspend; cbn;
          rewrite eqS, eqx; trivial.
      Qed.
      
      Lemma suspend_bound_gset S x (Sg: gset S) (bound: g S x):
        gset (suspend S x).
      Proof.
        split. split.
        - intros y z [iny|iny] [inz|inz].
          + apply (wo_total S); auto using C_wo.
          + rewrite <- inz; left.
            apply ltA_spec, (upper_bound S); auto using C_wo.
          + rewrite <- iny; right.
            apply ltA_spec, (upper_bound S); auto using C_wo.
          + now rewrite <- iny, <- inz; left.
        - intros Y Ysub inh.
          destruct (classical (inhabited (restrict x Y))) as [case|case].
          + destruct (wo_minima S Sg (restrict x Y)) as [m [[inm neq] bound']];
              auto.
            * intros z [[inz|eqz]%Ysub ltz]; auto.
              rewrite eqz in ltz; apply irreflexivity in ltz; contradiction.
            * exists m; split; trivial.
              intros z inz.
              destruct (classical (z < x)) as [case'|case'];
                [apply bound'; split; trivial|].
              apply Ysub in inz.
              apply ltA_spec.
              destruct inz as [inz|<-]; trivial.
              now eapply upper_bound in inz; eauto using C_wo.
          + assert (∀ y, y ∈ Y ↔ x ≡ y). {
              split.
              - intro iny.
                unfold restrict, inhabited in case; cbn in case.
                assert (¬y < x) as bound' by firstorder.
                apply Ysub in iny; destruct iny as [iny|]; trivial.
                now eapply upper_bound in iny; eauto using C_wo.
              - intros <-.
                destruct inh as [z inz].
                destruct (classical (x ∈ Y)) as [|notinx]; trivial.
                contradict case; exists z.
                split; trivial.
                eapply upper_bound; eauto using C_wo.
                destruct (Ysub _ inz) as [|eqy]; trivial.
                now rewrite eqy in notinx.
            }
            setoid_rewrite H.
            exists x; split; [|intros ? <-]; reflexivity.
        - intros c inc.
          assert (restrict c (suspend S x) ≡ restrict c S) as ->.
          + apply subset_equ.
            * intros y [[iny|<-] lty]; [split; trivial|].
              apply (lt_le_trans _ _ ltA_spec x c x), irreflexivity in lty;
                [contradiction|].
              destruct inc as [inc| ->]; [|reflexivity].
              eapply ltA_spec, upper_bound; eauto using C_wo.
            * intros y [iny bound']; split; trivial.
              left; trivial.
          + destruct inc as [inc|<-]; trivial.
            * apply C_bounds; trivial.
            * enough (restrict x S ≡ S) as -> by trivial.
              apply subset_equ; [destruct 1; trivial|].
              intros y iny; split; trivial.
              eapply upper_bound; eauto using C_wo.
      Qed.
      
      Section GSetsComparableFacts.
        Variables C D: set.
        Hypothesis Cg: gset C.
        Hypothesis Dg: gset D.
        Definition common S := S ≤ C ∧ S ≤ D.
        Definition W := ⋃ common.
        Variables c d: A.
        Hypothesis Wc: W ≡ restrict c C.
        Hypothesis Wd: W ≡ restrict d D.
        Hypothesis inc: c ∈ C.
        Hypothesis ind: d ∈ D.

        Fact eq_c_d: c ≡ d.
        Proof.
          apply (unique W); [rewrite Wc|rewrite Wd]; apply C_bounds; trivial.
        Qed.
        
        Let W' := suspend W c.
        
        Lemma restrict_mono: Proper (le ++> eq ==> le) restrict.
        Proof.
          intros x y lexy S ? <-.
          split.
          - intros z [inz ltz]; split; trivial.
            eapply lt_le_trans; eauto.
          - intros x' y' [inx' ltx'] [iny' lty'] ltx'y'.
            split; trivial.
            clear ltx'.
            eapply le_lt_trans; eauto.
        Qed.
        
        Lemma common_comparable S S' (Sc: common S) (Sc': common S'):
          S ≤ S' ∨ S' ≤ S.
        Proof.
          destruct Sc as [subc _], Sc' as [subc' _].
          destruct (classical (C ≤ S)) as [leC|ltS];
            [right; etransitivity; eauto|].
          destruct (classical (C ≤ S')) as [leC|ltS'];
            [left; etransitivity; eauto|].
          destruct (initial_prefix C S) as [x [inx [notinx prefix]]];
            [auto using C_wo|split; auto|].
          destruct (initial_prefix C S') as [x' [inx' [notinx' prefix']]];
            [auto using C_wo|split; auto|].
          rewrite prefix, prefix'.
          now destruct (wo_total C (C_wo _ Cg) x x' inx inx') as [case|case];
            [left|right]; apply restrict_mono.
        Qed.
        
        Lemma common_wo S (Sc: common S): well_ordered S.
        Proof.
          destruct Sc as [[sub _] _], Cg as [[total wo] _].
          clear -sub total wo.
          split; firstorder.
        Qed.
        
        Lemma W_le_C: W ≤ C.
        Proof.
          apply union_ub.
          destruct 1; trivial.
        Qed.
        
        Lemma W_le_D: W ≤ D.
        Proof.
          apply union_ub.
          destruct 1; trivial.
        Qed.
        
        Lemma W_wo: well_ordered W.
        Proof.
          apply union_wo; auto using common_wo, common_comparable.
        Qed.
        
        Lemma W_gset: gset W.
        Proof.
          split; auto using W_wo.
          intros b inb.
          rewrite Wc.
          enough (restrict b (restrict c C) ≡ restrict b C) as ->. {
            apply C_bounds; auto.
            destruct inb as [X [[[subX _] _] inb]].
            apply subX in inb; trivial.
          }
          apply subset_equ.
          - clear; firstorder.
          - intro x; intros [inx ltb]; repeat (split; trivial).
            rewrite ltb.
            apply upper_bound with W; auto using W_wo.
            rewrite Wc.
            apply C_bounds; auto.
        Qed.
        
        Corollary W'_gset: gset W'.
        Proof.
          apply suspend_bound_gset; auto using W_gset.
          rewrite Wc; apply C_bounds; trivial.
        Qed.
        
        Lemma W'_common: common W'.
        Proof.
          assert (suspend_restrict: ∀ X x, x ∈ X →
            suspend (restrict x X) x ≤ X). {
            intros * inx.
            split.
            - intros y [[iny _]| <-]; trivial.
            - intros y z iny [[inz ltx]|<-] ley.
              + left; split; trivial.
                eapply le_lt_trans; eauto.
              + destruct (classical (x ≤ y)) as [case|case].
                * right; apply eqA_spec; auto.
                * left; split; trivial.
                  apply ltA_spec; auto.
          }
          split; unfold W'.
          - rewrite Wc; apply suspend_restrict; auto.
          - rewrite Wd, eq_c_d; apply suspend_restrict; auto.
        Qed.
        
        Corollary W'_le_W: W' ≤ W.
        Proof.
          apply prefix_union; auto using common_comparable, W'_common.
        Qed.
        
        Corollary incomparable_C_D_inconsistent: False.
        Proof.
          enough (c ∈ W) as contra. {
            rewrite Wc in contra.
            destruct contra as [_ [ ]%irreflexivity].
          }
          apply W'_le_W.
          now right.
        Qed.
      End GSetsComparableFacts.
      
      Lemma gsets_comparable C D (Cg: gset C) (Dg: gset D): C ≤ D ∨ D ≤ C.
      Proof.
        pose proof (W_le_C C D) as leC.
        pose proof (W_le_D C D) as leD.
        assert (W C D ≡ C ∨ W C D < C) as [<-|ltC]; auto. {
          unfold lt, set_lt, default_lt, equ, set_eq, default_eq.
          destruct (classical (C ≤ W C D)); auto.
        }
        assert (W C D ≡ D ∨ W C D < D) as [<-|ltD]; auto. {
          unfold lt, set_lt, default_lt, equ, set_eq, default_eq.
          destruct (classical (D ≤ W C D)); auto.
        }
        clear leC leD.
        destruct (initial_prefix C (W C D)) as [c [inc [notinc eqc]]];
          auto using C_wo.
        destruct (initial_prefix D (W C D)) as [d [ind [notind eqd]]];
          auto using C_wo.
        destruct (incomparable_C_D_inconsistent C D Cg Dg c d eqc eqd inc ind).
      Qed.
      
      Definition maxgset := ⋃ gset.
      Lemma maxgset_gset: gset maxgset.
      Proof.
        split.
        - apply union_wo.
          + apply gsets_comparable.
          + destruct 1; trivial.
        - intros c [S [inS inc]].
          enough (restrict c maxgset ≡ restrict c S) as ->
            by now apply C_bounds.
          apply subset_equ.
          + intros x [[S' [inS' sub]] ltc].
            split; trivial.
            destruct (gsets_comparable S S') as [case|case]; auto.
            * eapply cs_closed; eauto.
              apply ltA_spec, ltc.
            * eapply cs_subset; eauto.
          + intros x [inx ltc]; split; trivial.
            exists S; auto.
      Qed.
      
      Lemma maxgset_suspend b (b_bound: g maxgset b): gset (suspend maxgset b).
      Proof.
        apply suspend_bound_gset; auto using maxgset_gset.
      Qed.
      
      Corollary gsets_inconsistent: False.
      Proof.
        destruct (domain maxgset (C_wo _ maxgset_gset)) as [b b_bound].
        enough (b ∈ maxgset) as contra.
        - eapply upper_bound in contra; eauto using C_wo, maxgset_gset.
          now apply irreflexivity in contra.
        - eapply prefix_union; eauto using  gsets_comparable, maxgset_suspend.
          now right.
      Qed.
    End GSets.
    
    Corollary must_have_included_bound
      (g: set → A → Prop) (unique: ∀ S b b', g S b → g S b' → b ≡ b')
      (proper: Proper (equ ==> equ ==> iff) g)
      (domain: ∀ S, well_ordered S → ∃ b, g S b)
      (upper_bound: ∀ S b x, well_ordered S → g S b → x ∈ S → x ≤ b)
      (strong_upper_bounds: ∀ S b, well_ordered S → g S b →
        (∃ b', ∀ x, x ∈ S → x < b') → ¬b ∈ S):
      ∃ S b, well_ordered S ∧ g S b ∧ b ∈ S.
    Proof.
      destruct (classical (∃ S b, well_ordered S ∧ g S b ∧ b ∈ S)) as [|contra];
        trivial.
      destruct (gsets_inconsistent g unique proper domain).
      intros * woS b_bound inx.
      apply ltA_spec.
      split; [eapply upper_bound; eauto|].
      intro leb.
      assert (b ≡ x) as eqb. {
        apply eqA_spec; split; trivial.
        eapply upper_bound; eauto.
      }
      rewrite eqb in *; clear b eqb.
      eapply strong_upper_bounds in inx; eauto.
      destruct (classical (∃ b', ∀ y, y ∈ S → y < b')) as [|contra']; trivial.
      contradict contra.
      exists S, x.
      repeat (split; trivial).
    Qed.
    
    Definition bound_relation (W: { W | well_ordered W }) b :=
      let S := proj1_sig W in
      (∀ x, x ∈ S → x ≤ b) ∧
      ((∃ b', ∀ x, x ∈ S → x < b') → ¬b ∈ S).
    Instance: Equiv { W | well_ordered W } := λ W W', proj1_sig W ≡ proj1_sig W'.
    Instance: @Equivalence { W | well_ordered W } equ.
    Proof.
      split.
      - now intros [S W]; change (S ≡ S).
      - intros [S₁ W₁] [S₂ W₂] ?.
        now change (S₂ ≡ S₁).
      - intros [S₁ W₁] [S₂ W₂] [S₃ W₃] ??.
        change (S₁ ≡ S₃); transitivity S₂; trivial.
    Qed.
    
    Theorem zorns_lemma (all_chains_bounded: ∀ F, well_ordered F →
      ∃ m, ∀ x, x ∈ F → x ≤ m):
      ∃ m: A, ∀ x, m ≤ x → x ≤ m.
    Proof.
      destruct (choice _ _ _ _ _ _ bound_relation)
        as [g [g_sub [g_proper [g_complete g_unique]]]]. {
        unfold bound_relation.
        intros [S Swo] [S' S'wo] eqS b b' eqb.
        change (S ≡ S') in eqS.
        cbn.
        setoid_rewrite eqS.
        now setoid_rewrite eqb.
      } {
        intros [S Swo].
        unfold bound_relation; cbn.
        destruct (all_chains_bounded S Swo) as [m m_bound].
        destruct (classical (∃ b, ∀ x, x ∈ S → x < b)) as
          [[b b_bound]|no_strong_bound].
        - exists b; split.
          + intros; apply ltA_spec; auto.
          + intros _ [ ]%b_bound%irreflexivity.
        - exists m; tauto.
      } {
        destruct (must_have_included_bound (λ S b, ∃ W, g (exist _ S W) b))
          as [S [b [Swo [[W bbound] inb]]]].
        - intros S b b' [W bbound] [W' b'bound].
          eapply g_unique; eauto.
          eapply g_proper; eauto.
          now change (S ≡ S).
        - apply proper_sym_impl_iff_2; [firstorder|apply _|].
          intros S S' eqS b b' eqb [W bound].
          assert (well_ordered S') as W' by now rewrite <- eqS.
          exists W'.
          now revert bound; apply g_proper; [change (S' ≡ S)|].
        - intros S Swo.
          destruct (g_complete (exist _ S Swo)) as [b rel].
          eauto.
        - intros ??? Swo [W [bound _]%g_sub] inx.
          apply bound; trivial.
        - intros S b Swo [W [_ strong]%g_sub] strong_bound.
          apply strong; trivial.
        - exists b; intros x lb.
          destruct (classical (x ≤ b)) as [|contra]; trivial.
          apply g_sub in bbound.
          destruct bbound as [bound strong]; cbn in strong.
          apply strong in inb; [contradiction|].
          exists x.
          intros y iny%bound.
          eapply le_lt_trans; eauto.
          rewrite ltA_spec; auto.
      }
    Qed.
  End Proof.
  
  Section WellOrderingTheorem.
    Context {A} (eqA: relation A) {equA: Equivalence eqA}.
    Record ordered_subset (S: A → Prop) (R: relation A) := {
      S_proper:: Proper (eqA ==> iff) S;
      R_strict:: StrictOrder R;
      R_wellfounded: well_founded R;
      R_proper:: Proper (eqA ==> eqA ==> iff) R;
      R_carrier_correct: ∀ x y, R x y → S x ∧ S y;
      R_carrier_complete: ∀ x y, S x → S y → eqA x y ∨ R x y ∨ R y x
    }.
    Record continues_raw (S S': A → Prop) (R R': relation A) := {
      S_sub: ∀ x, S x → S' x;
      S_closed: ∀ x y, S' x → S y → R' x y → S x;
      R_coincides: ∀ x y, S x → S y → (R x y ↔ R' x y)
    }.
    Definition order := { O | ordered_subset (fst O) (snd O) }.
    Notation "o .S" := (fst (proj1_sig o)) (at level 30).
    Notation "o .R" := (snd (proj1_sig o)) (at level 30).
    Notation "o .good" := (proj2_sig o) (at level 30).
    Instance: ∀ o: order, Proper (eqA ==> iff) (o.S).
    Proof. intro; apply (o.good). Qed.
    Instance: ∀ o: order, Proper (eqA ==> eqA ==> iff) (o.R).
    Proof. intro; apply (o.good). Qed.
    Instance: ∀ o: order, StrictOrder (o.R).
    Proof. intro; apply (o.good). Qed.
    
    Definition continues (o₁ o₂: order) :=
      continues_raw (o₁.S) (o₂.S) (o₁.R) (o₂.R).
    
    Instance continues_preorder: PreOrder continues.
    Proof.
      split.
      - intros [[S R] good]; red; cbn.
        split; intuition auto.
      - intros [[S₁ R₁] good₁] [[S₂ R₂] good₂] [[S₃ R₃] good₃];
          unfold continues; cbn.
        intros [sub₁₂ closed₁₂ coincides₁₂] [sub₂₃ closed₂₃ coincides₂₃].
        split; [firstorder|..].
        + intros ?? inx iny rel.
          eapply closed₁₂; eauto.
          apply coincides₂₃; auto.
          eapply closed₂₃; eauto.
        + intros * inx iny.
          rewrite coincides₁₂; auto.
    Qed.
    
    Local Infix "≤" := continues.
    
    Hypothesis classical: excluded_middle.
    
    Definition suspend_S S x y := S y ∨ eqA x y.
    Definition suspend_R S (R: relation A) x y z := R y z ∨ S y ∧ eqA x z.
    Lemma suspend_good S R x (x_not_in: ¬S x):
      ordered_subset S R → ordered_subset (suspend_S S x) (suspend_R S R x).
    Proof.
      intros [sproper strict wf proper correct complete].
      unfold suspend_S, suspend_R.
      split. 2:split.
      - solve_proper.
      - intros y [[ ]%irreflexivity|[iny eqz]].
        now rewrite <- eqz in iny.
      - intros a b c [ltab|[ina eqb]] [ltbc|[inb eqc]].
        + left; transitivity b; trivial.
        + right; split; trivial.
          apply correct in ltab; tauto.
        + apply correct in ltbc.
          rewrite <- eqb in ltbc; tauto.
        + auto.
      - assert (∀ y, ¬eqA x y → Acc (λ y z, R y z ∨ S y ∧ eqA x z) y).
        + induction y as [y IH] using (well_founded_ind wf).
          intro neq; constructor; intros z [ltz|[inz eqy]]; [|contradiction].
          apply IH; trivial.
          apply correct in ltz.
          intro contra; rewrite <- contra in ltz; tauto.
        + intro y.
          destruct (classical (eqA x y)) as [eqxy|neq]; auto.
          constructor.
          intros z [ltz|[inz eqy]].
          * apply H.
            intro contra; rewrite <- contra, eqxy in ltz.
            apply irreflexivity in ltz; contradiction.
          * apply H.
            now intro contra; rewrite contra in x_not_in.
      - solve_proper.
      - intros y z [relyz|[iny eqxz]]; [|tauto].
        apply correct in relyz; tauto.
      - intros y z [iny|eqy] [inz|eqz]; auto.
        + destruct (complete y z) as [?|[?|?]]; auto.
        + rewrite <- eqz, eqy; auto.
          now left.
    Qed.
    
    Definition suspend' (o: order) x (x_not_in: ¬o.S x): order :=
      exist _ (suspend_S (o.S) x, suspend_R (o.S) (o.R) x)
        (suspend_good (o.S) (o.R) x x_not_in (o.good)).
    
    Lemma maximal_continuation_total o (o_max: ∀ o', o ≤ o' → o' ≤ o):
      ∀ x y, eqA x y ∨ o.R x y ∨ o.R y x.
    Proof.
      enough (∀ x, o.S x)
        by (intros; eapply R_carrier_complete; [apply (o.good)|auto..]).
      intro.
      destruct (classical (o.S x)) as [|notinx]; trivial.
      apply (o_max (suspend' o x notinx)); [|now right].
      split; cbn; auto.
      - now left.
      - intros y z [iny|eqy] inz [rel|[iny' eqz]]; eauto.
        destruct (o.good) as [_ _ _ _ correct _].
        apply correct in rel.
        rewrite eqy in notinx; tauto.
      - intros y z iny inz.
        unfold suspend_R.
        split; [tauto|].
        intros [|[_ eqxz]]; auto.
        clear -notinx inz eqxz.
        destruct o as [[S R] []]; cbn in *.
        now rewrite eqxz in notinx.
    Qed.
    
    Definition union_S (F: order → Prop) x := ∃ o, F o ∧ o.S x.
    Definition union_R (F: order → Prop) x y := ∃ o, F o ∧ o.R x y.
    
    Lemma continuation_subrelation o o' (cont: o ≤ o'):
      subrelation (o.R) (o'.R).
    Proof.
      destruct cont as [sub cont coincide].
      intros x y rel.
      destruct (o.good) as [_ _ _ _ correct _].
      apply coincide; trivial; apply correct in rel; tauto.
    Qed.
    
    Lemma union_good (F: order → Prop)
      (F_chain: ∀ o o', F o → F o' → o ≤ o' ∨ o' ≤ o):
      ordered_subset (union_S F) (union_R F).
    Proof.
      unfold union_S, union_R.
      split. 2:split.
      - solve_proper.
      - intros x [o [_ [ ]%irreflexivity]].
      - intros x y z [o [ino sto]] [o' [ino' sto']].
        destruct (F_chain _ _ ino ino') as [case|case].
        + exists o'; split; trivial; transitivity y; trivial.
          apply continuation_subrelation in case.
          apply case, sto.
        + exists o; split; trivial; transitivity y; trivial.
          apply continuation_subrelation in case.
          apply case, sto'.
      - intro a.
        constructor.
        intros b [o [ino rel]].
        destruct (o.good) as [sproper rstrict rwf rproper rcorrect rcomplete].
        apply rcorrect in rel.
        destruct rel as [inb _]; clear a.
        induction b as [a IH] using (well_founded_ind rwf).
        constructor.
        intros b [o' [ino' rel]].
        destruct (F_chain _ _ ino ino') as [case|case].
        + destruct case as [sub closed coincides].
          rewrite <- coincides in rel; auto.
          * apply IH; trivial.
            apply rcorrect in rel; tauto.
          * eapply closed; eauto.
            destruct (o'.good) as [_ _ _ _ correct _].
            apply correct in rel; tauto.
        + apply IH.
          * apply continuation_subrelation in case.
            apply case, rel.
          * apply continuation_subrelation in case.
            apply case in rel.
            destruct (o.good) as [_ _ _ _ correct _].
            apply correct in rel; tauto.
      - solve_proper.
      - intros x y [o [ino relo]].
        destruct (o.good) as [_ _ _ _ correct _].
        apply correct in relo.
        destruct relo; split; eauto.
      - intros x y [o [ino relo]] [o' [ino' relo']].
        destruct (F_chain o o' ino ino') as [case|case].
        + destruct (case) as [S_sub _ _].
          apply S_sub in relo.
          destruct (o'.good) as [_ _ _ _ _ complete].
          destruct (complete x y) as [?|[?|?]]; eauto.
        + destruct (case) as [S_sub _ _].
          apply S_sub in relo'.
          destruct (o.good) as [_ _ _ _ _ complete].
          destruct (complete x y) as [?|[?|?]]; eauto.
    Qed.
  End WellOrderingTheorem.
  
  Notation "o .S" := (fst (proj1_sig o)) (at level 30).
  Notation "o .R" := (snd (proj1_sig o)) (at level 30).
  Notation "o .good" := (proj2_sig o) (at level 30).

  Theorem well_ordering_from_zorns_lemma
    (classical: excluded_middle)
    (zl: ∀ A R preR chub, @ZornsLemma A R preR chub)
    {A} (eqA: relation A) {equA: Equivalence eqA}:
    ∃ ltA, well_order eqA ltA.
  Proof.
    pose proof (zl _ (continues eqA) (continues_preorder eqA)) as zl'.
    unfold ZornsLemma in zl'.
    destruct zl' as [o omax].
    - intros C Cchain.
      exists (exist _ (union_S eqA C, union_R eqA C)
        (union_good eqA C Cchain): order eqA).
      intros o ino.
      split; cbn.
      + intros x inx; exists o; auto.
      + intros ?? [o' [ino' inx]] iny [o'' [ino'' rel']].
        destruct (Cchain o' o ino' ino) as [[ ]|[sub cl co]]; auto.
        pose proof (sub _ iny) as iny'.
        destruct (Cchain o'' o' ino'' ino') as [[sub' cl' co']|[sub' cl' co']].
        * destruct (o''.good) as [_ _ _ _ correct _].
          destruct (correct _ _ rel') as [inx'' iny''].
          rewrite co' in rel'; auto.
          destruct (o'.good); eauto.
        * rewrite <- co' in rel'; trivial.
          destruct (o'.good); eauto.
      + intros ?? inx iny; split; [exists o; auto|].
        intros [o' [ino' rel]].
        destruct (Cchain _ _ ino ino') as [[sub cl co]|[sub cl co]];
          [now apply co|].
        destruct (o'.good) as [_ _ _ _ correct _].
        destruct (correct _ _ rel).
        now apply co.
    - exists (o.R).
      pose proof (maximal_continuation_total eqA classical o omax) as total.
      clear omax.
      destruct o as [[S R] [sproper strict wf rproper correct complete]].
      now split.
  Qed.
  (* end hide *)   
End Private.


(** * The key theorems *)

Section Theorems.
  Hypothesis classical: excluded_middle.

  (** The classical formulation of Zorn's lemma. *)

  Theorem zorns_lemma (choice: GeneralizedSetoidRelationalChoice)
    {A} R {preR: PreOrder R}
    (chains_have_upper_bounds: ∀ (C: A → Prop),
      (∀ x y, C x → C y → R x y ∨ R y x) → ∃ m, ∀ x, C x → R x m):
    ∃ m: A, ∀ x, R m x → R x m.
  Proof.
    apply Private.zorns_lemma with
      (equ := λ x y, R x y ∧ R y x)
      (lt := λ x y, R x y ∧ ¬R y x);
      auto;
      [reflexivity..|].
    intros [C Cset] [total _]; cbn in *.
    apply chains_have_upper_bounds, total.
  Qed.

  (** Zorn's lemma proves the well-ordering theorem. *)

  Theorem zorns_lemma_imp_well_ordering_theorem
    (zl: ∀ A R preR chub, @ZornsLemma A R preR chub)
    {A} (eqA: relation A) {equA: Equivalence eqA}:
    ∃ ltA, well_order eqA ltA.
  Proof.
    now apply Private.well_ordering_from_zorns_lemma.
  Qed.
  
  (** Deriving the well-ordering theorem from choice. *)

  Corollary well_ordering_theorem
    (choice: GeneralizedSetoidRelationalChoice)
    {A} (eqA: relation A) {equA: Equivalence eqA}:
    ∃ ltA, well_order eqA ltA.
  Proof.
    apply zorns_lemma_imp_well_ordering_theorem; trivial.
    apply zorns_lemma, choice.
  Qed.
  
  (** The well-ordering theorem implies choice, closing the circle. *)

  Theorem well_ordering_theorem_imp_axiom_of_choice
    (wo: ∀ {A} (eqA: relation A) {equA: Equivalence eqA},
      ∃ ltA, well_order eqA ltA):
    GeneralizedSetoidRelationalChoice.
  Proof.
    intros A B eqA eqB equA equB R Rproper Rfull.
    destruct (wo B eqB equB) as [ltB [_ ltB_strict ltB_wf ltB_proper ltB_total]].
    exists (λ a b, R a b ∧ ∀ b', R a b' → ¬ltB b' b).
    split; [tauto|].
    split; [solve_proper|].
    split. {
      intro.
      destruct (Rfull x) as [y rel].
      induction y as [y IH] using (well_founded_ind ltB_wf).
      destruct (classical (∃ y', R x y' ∧ ltB y' y)) as [[y' [rel' lt']]|none].
      - now apply (IH y').
      - exists y; split; trivial.
        firstorder.
    } {
      intros ??? [rel min] [rel' min'].
      apply min in rel'.
      apply min' in rel.
      destruct (ltB_total y y'); tauto.
    }
  Qed.
End Theorems.
