(**
 The clasical pigeonhole principle.

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
From Coq Require Import List.

Theorem pigeonhole_principle {A} (lobjects lboxes: list A)
  (objects_in_boxes: incl lobjects lboxes)
  (no_two_objects_in_same_box: NoDup lobjects):
  length lobjects <= length lboxes.
Proof.
  revert lboxes objects_in_boxes.
  induction no_two_objects_in_same_box as [|obj lobjects obj_alone _ IH].
  - cbn; auto with arith.
  - intros ??.
    assert (exists lboxes', Add obj lboxes' lboxes) as [lboxes' add]
      by apply Add_inv, objects_in_boxes, in_eq.
    rewrite (Add_length add); cbn.
    enough (incl lobjects lboxes') by auto with arith.
    intros obj' in_obj.
    assert (In obj' lboxes) as in_obj'
      by apply objects_in_boxes, in_cons, in_obj.
    rewrite (Add_in add) in in_obj'; cbn in in_obj'.
    now destruct in_obj' as [<-|].
Qed.
