(**
 Some choice principles.

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
From misc Require Import MoreChoice Zorn.
From Coq Require Import Relations Equivalence Morphisms Utf8 ClassicalFacts.
From Coq.Program Require Import Basics.

(** A useful corollary of Zorn's lemma: The dependent Zorn's lemma. *)
Lemma dependent_zorn (H: ∀ A R RPre chain, @ZornsLemma A R RPre chain)
  A (P: A → Prop) (R: relation A) (Rpre: PreOrder R)
  (chains: ∀ (C: A → Prop), (∀ x, C x → P x) →
    (∀ x y, C x → C y → R x y ∨ R y x) →
    ∃ m, P m ∧ ∀ x, C x → R x m):
  ∃ m, P m ∧ ∀ x, P x → R m x → R x m.
Proof.
  set (R' (x y: sig P) := R (proj1_sig x) (proj1_sig y)).
  assert (R'_pre: PreOrder R'). {
    split.
    - intro; apply Rpre.
    - intros ???; apply Rpre.
  }
  assert (chain': ∀ (C: sig P → Prop), (∀ x y, C x → C y → R' x y ∨ R' y x) →
    ∃ m, ∀ x, C x → R' x m). {
    intros C C_chain.
    destruct (chains (λ x, ∃ (H: P x), C (exist _ x H)))
      as [m [inm maxm]].
    - intros x [Hx _]; trivial.
    - intros x y [Hx inx] [Hy iny].
      apply (C_chain (exist P x Hx) (exist P y Hy)); trivial.
    - exists (exist P m inm).
      intros [x Hx] inx.
      apply maxm.
      exists Hx; trivial.
  }
  destruct (H (sig P) R' R'_pre chain') as [[x Hx] maxx].
  exists x.
  split; trivial.
  intros y iny.
  apply (maxx (exist P y iny)).
Qed.

Corollary dependent_nonempty_zorn (em: excluded_middle)
  (H: ∀ A R RPre chain, @ZornsLemma A R RPre chain)
  A (P: A → Prop) a₀ (R: relation A) (H₀: P a₀) (Rpre: PreOrder R)
  (nonempty_chains: ∀ (C: A → Prop) a, C a → (∀ x, C x → P x) →
    (∀ x y, C x → C y → R x y ∨ R y x) →
    ∃ m, P m ∧ ∀ x, C x → R x m):
  ∃ m, P m ∧ ∀ x, P x → R m x → R x m.
Proof.
  apply dependent_zorn; auto.
  intros C C_good C_chain.
  destruct (em (∃ a, C a)) as [[a ina]|noa]; [eauto|].
  exists a₀.
  split; trivial.
  firstorder.
Qed.

Definition sub {A} (s₁ s₂: A → Prop) := ∀ x, s₁ x → s₂ x.
Local Infix "⊆" := sub (at level 70).
Instance sub_pre A: PreOrder (@sub A).
Proof. firstorder. Qed.

Section Ultrafilter.
  Context L (Lle: relation L) {pre: PreOrder Lle}.
  Infix "≤" := Lle.
  
  Class Filter (F: L → Prop) := {
    filt_uc: Proper (Lle ++> impl) F;
    filt_dir: ∀ x y, F x → F y → ∃ z, F z ∧ z ≤ x ∧ z ≤ y
  }.
  Class ProperFilter (F: L → Prop) := {
    pfilt_filt :> Filter F;
    filt_proper: ∃ x, ¬F x
  }.
  Class Ultrafilter (F: L → Prop) := {
    ufilt_pfilt :> ProperFilter F;
    filt_ultra: ∀ F', ProperFilter F' → F ⊆ F' → F' ⊆ F
  }.
  
  Context (em: excluded_middle)
    (zorn: ∀ A R RPre chain, @ZornsLemma A R RPre chain)
    (b: L) (min: ∀ x, b ≤ x).
  Lemma ultrafilter F (Fprop: ProperFilter F): ∃ U, Ultrafilter U ∧ F ⊆ U.
  Proof.
    destruct (dependent_nonempty_zorn em zorn (L → Prop)
      (λ F', ProperFilter F' ∧ F ⊆ F') F sub)
      as [U [[Uproper Usub] Umax]].
    - split; auto; reflexivity.
    - apply _.
    - intros ?? ina C_good C_chain.
      exists (λ x, ∃ s, C s ∧ s x).
      repeat split.
      + intros x x' lex [s [ins inx]].
        exists s; split; trivial.
        destruct (C_good s ins) as [s_proper _].
        apply (filt_uc x); trivial.
      + intros ?? [sx [insx inx]] [sy [insy iny]].
        destruct (C_chain sx sy) as [case|case]; auto.
        * destruct (C_good sy insy) as [y_proper _].
          destruct (filt_dir x y) as [z [inz [lex ley]]]; eauto.
          exists z; eauto.
        * destruct (C_good sx insx) as [x_proper _].
          destruct (filt_dir x y) as [z [inz [lex ley]]]; eauto.
          exists z; eauto.
      + exists b.
        intros [s [ins inb]].
        destruct (C_good s ins) as [s_proper _].
        destruct filt_proper as [n notinn].
        contradict notinn.
        apply (filt_uc b); auto.
      + intros x inx.
        exists a.
        split; auto.
        apply (C_good a); trivial.
      + intros s ins x inx; eauto.
    - exists U.
      split; trivial.
      split; trivial.
      intros ? proper sub.
      apply Umax; auto.
      split; trivial.
      transitivity U; trivial.
  Qed.
  
  Context (join meet: L → L → L).
  Infix "⊓" := meet (at level 50).
  Infix "⊔" := join (at level 50).
  Context (join_l: ∀ x y, x ≤ x ⊔ y).
  Context (join_r: ∀ x y, y ≤ x ⊔ y).
  Context (meet_l: ∀ x y, x ⊓ y ≤ x).
  Context (meet_r: ∀ x y, x ⊓ y ≤ y).
  Context (join_lub: ∀ x y z, x ≤ z → y ≤ z → x ⊔ y ≤ z).
  Context (meet_glb: ∀ x y z, z ≤ x → z ≤ y → z ≤ x ⊓ y).
  Definition Leq x y := x ≤ y ∧ y ≤ x.
  Instance Leq_equiv: Equivalence Leq.
  Proof. firstorder. Qed.
  Instance Lle_proper: Proper (Leq ==> Leq ==> iff) Lle.
  Proof.
    intros x x' [lex gex] y y' [ley gey]; split; intro lexy.
    - now rewrite gex, lexy.
    - now rewrite lex, lexy.
  Qed.
  Infix "≡" := Leq (at level 70).
  
  Context (distr: ∀ x y z, x ⊔ (y ⊓ z) ≡ (x ⊔ y) ⊓ (x ⊔ z)).
  
  Lemma ultrafilter_prime F (FUlt: Ultrafilter F) x y:
    F (x ⊔ y) ↔ F x ∨ F y.
  Proof.
    split.
    2: intros [case|case]; [eapply filt_uc; [|apply case]; auto..].
    intro injoin.
    destruct (em (F x)) as [|notinx]; auto.
    right.
    apply (filt_ultra (λ a, F (x ⊔ a))).
    split. split.
    - intros u v leuv inu.
      apply (filt_uc (x ⊔ u)); trivial.
      apply join_lub; auto.
      rewrite <- join_r; auto.
    - intros u v inu inv.
      destruct (filt_dir (x ⊔ u) (x ⊔ v)) as [w [inw [leu lev]]]; auto.
      exists (u ⊓ v).
      split; auto.
      apply (filt_uc w); auto.
      rewrite distr; auto.
    - exists x.
      contradict notinx.
      apply (filt_uc (x ⊔ x)); auto.
      now apply join_lub.
    - intros z inz.
      apply (filt_uc z); auto.
    - trivial.
  Qed.
End Ultrafilter.