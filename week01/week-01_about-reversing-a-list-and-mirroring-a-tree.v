(* week-01_about-reversing-a-list-and-mirroring-a-tree.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 15 Aug 2024 *)

(* ********** *)

(* This warmup exercise is a study of list reversal and tree mirroring. *)

(* About style:

   - when you use the Light of Inductil,
     make sure to provide the argument(s) of the induction hypothesis when you apply it

   - there is no need to provide the arguments of most of the other lemmas you apply,
     unless you feel that

     + it is necessary, or

     + it makes the proof clearer. *)

(* Note:
   The point of this warmup exercise is not to do everything in a stressed hurry.
   The point is to do well what you have the time to do, and to re-acquire basic tCPA reflexes. *)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

(* Background material, Part I/II: lists.

   list_append, list_reverse, and list_reverse_alt,
   their associated fold-unfold lemmas,
   and some of their properties *)

(* ***** *)

Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s with
    nil =>
    match v2s with
      nil =>
      true
    | v2 :: v2s' =>
      false
    end
  | v1 :: v1s' =>
    match v2s with
      nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end
  end.

Definition test_list_append (candidate : forall V : Type, list V -> list V -> list V) : bool :=
  (eqb_list
     nat
     Nat.eqb
     (candidate nat nil nil)
     nil)
  &&
  (eqb_list
     nat
     Nat.eqb
     (candidate nat nil (1 :: nil))
     (1 :: nil))
  &&
  (eqb_list
     nat
     Nat.eqb
     (candidate nat (1 :: 2 :: nil) (3 :: 4 :: nil))
     (1 :: 2 :: 3 :: 4 :: nil))
  (* etc. *)
  .

Fixpoint list_append (V : Type) (v1s v2s : list V) : list V :=
  match v1s with
    nil =>
    v2s
  | v1 :: v1s' =>
    v1 :: list_append V v1s' v2s
  end.

Compute (test_list_append list_append).

Lemma fold_unfold_list_append_nil :
  forall (V : Type)
         (v2s : list V),
    list_append V nil v2s =
    v2s.
Proof.
  fold_unfold_tactic list_append.
Qed.

Lemma fold_unfold_list_append_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' v2s : list V),
    list_append V (v1 :: v1s') v2s =
    v1 :: list_append V v1s' v2s.
Proof.
  fold_unfold_tactic list_append.
Qed.

Property nil_is_left_neutral_for_list_append :
  forall (V : Type)
         (vs : list V),
    list_append V nil vs = vs.
Proof.
  intros V vs.
  rewrite -> fold_unfold_list_append_nil.
  reflexivity.

  Restart.

  exact fold_unfold_list_append_nil.
Qed. (* was proved in the FPP/LPP midterm project *)

Property nil_is_right_neutral_for_list_append :
  forall (V : Type)
         (vs : list V),
    list_append V vs nil = vs.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  * rewrite -> fold_unfold_list_append_nil.
    reflexivity.
  * rewrite -> fold_unfold_list_append_cons.
    rewrite -> IHvs'.
    reflexivity.
Qed. (* was proved in the FPP/LPP midterm project *)

Property list_append_is_associative :
  forall (V : Type)
         (v1s v2s v3s : list V),
    list_append V v1s (list_append V v2s v3s) =
      list_append V (list_append V v1s v2s) v3s.
Proof.
  intros V v1s v2s v3s.
  induction v1s as [ | v1 v1s' IHv1s'].
  * rewrite ->2 fold_unfold_list_append_nil.
    reflexivity.
  * rewrite -> (fold_unfold_list_append_cons V v1 v1s' (list_append V v2s v3s)).
    rewrite -> (fold_unfold_list_append_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_list_append_cons V v1 (list_append V v1s' v2s) v3s).
    rewrite -> IHv1s'.
    reflexivity.
Qed. (* was proved in the FPP/LPP midterm project *)

Property about_applying_list_append_to_a_singleton_list :
  forall (V : Type)
         (v1 : V)
         (v2s : list V),
    list_append V (v1 :: nil) v2s = v1 :: v2s.
Proof.
  intros V v1 v2s.
  rewrite -> fold_unfold_list_append_cons.
  rewrite -> fold_unfold_list_append_nil.
  reflexivity.
Qed.

(* ***** *)

Definition test_list_reverse (candidate : forall V : Type, list V -> list V) : bool :=
  (eqb_list
     nat
     Nat.eqb
     (candidate nat nil)
     nil)
  &&
  (eqb_list
     nat
     Nat.eqb
     (candidate nat (1 :: nil))
     (1 :: nil))
  &&
  (eqb_list
     nat
     Nat.eqb
     (candidate nat (1 :: 2 :: nil))
     (2 :: 1 :: nil))
  (* etc. *)
  .

Fixpoint list_reverse (V : Type) (vs : list V) : list V :=
  match vs with
    nil =>
    nil
  | v :: vs' =>
    list_append V (list_reverse V vs') (v :: nil)
  end.

Compute (test_list_reverse list_reverse).

Lemma fold_unfold_list_reverse_nil :
  forall (V : Type),
    list_reverse V nil =
    nil.
Proof.
  fold_unfold_tactic list_reverse.
Qed.

Lemma fold_unfold_list_reverse_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    list_reverse V (v :: vs') =
    list_append V (list_reverse V vs') (v :: nil).
Proof.
  fold_unfold_tactic list_reverse.
Qed.

Property about_applying_list_reverse_to_a_singleton_list :
  forall (V : Type)
         (v : V),
    list_reverse V (v :: nil) = v :: nil.
Proof.
  intros V v.
  rewrite -> fold_unfold_list_reverse_cons.
  rewrite -> fold_unfold_list_reverse_nil.
  rewrite -> fold_unfold_list_append_nil.
  reflexivity.
Qed.

Property list_append_and_list_reverse_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    list_reverse V (list_append V v1s v2s) =
    list_append V (list_reverse V v2s) (list_reverse V v1s).
Proof.
  intros V v1s v2s.
  induction v1s as [ | v1 v1s' IHv1s'].
  - rewrite -> (fold_unfold_list_append_nil V v2s).
    rewrite -> (fold_unfold_list_reverse_nil V).
    rewrite -> (nil_is_right_neutral_for_list_append V (list_reverse V v2s)).
    reflexivity.
  - rewrite -> (fold_unfold_list_reverse_cons V v1 v1s').
    rewrite -> (fold_unfold_list_append_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_list_reverse_cons V v1 (list_append V v1s' v2s)).
    rewrite -> IHv1s'.
    rewrite -> (list_append_is_associative V
                 (list_reverse V v2s)
                 (list_reverse V v1s')
                 (v1 :: nil)).
    reflexivity.
Qed. (* was proved in the FPP/LPP midterm project *)

(* ***** *)

Fixpoint list_reverse_acc (V : Type) (v1s a : list V) : list V :=
  match v1s with
    nil =>
    a
  | v1 :: v1s' =>
    list_reverse_acc V v1s' (v1 :: a)
  end.

Lemma fold_unfold_list_reverse_acc_nil :
  forall (V : Type)
         (a : list V),
    list_reverse_acc V nil a =
    a.
Proof.
  fold_unfold_tactic list_reverse_acc.
Qed.

Lemma fold_unfold_list_reverse_acc_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' a : list V),
    list_reverse_acc V (v1 :: v1s') a =
    list_reverse_acc V v1s' (v1 :: a).
Proof.
  fold_unfold_tactic list_reverse_acc.
Qed.

Definition list_reverse_alt (V : Type) (vs : list V) : list V :=
  list_reverse_acc V vs nil.

Compute (test_list_reverse list_reverse).

Property about_applying_list_reverse_acc_to_a_singleton_list :
  forall (V : Type)
         (v : V)
         (a : list V),
    list_reverse_acc V (v :: nil) a = v :: a.
Proof.
  intros V v a.
  rewrite -> fold_unfold_list_reverse_acc_cons.
  rewrite -> fold_unfold_list_reverse_acc_nil.
  reflexivity.
Qed.

Lemma list_reverse_acc_reset:
  forall (V : Type)
         (vs a: list V),
    list_reverse_acc V vs a =
      list_append V (list_reverse_acc V vs nil) a.
Proof.
  induction vs as [ | v vs' IHvs'].
  * intros a.
    rewrite -> (fold_unfold_list_reverse_acc_nil V a).
    reflexivity.
  * intros a.
    rewrite -> (fold_unfold_list_reverse_acc_cons V v vs' nil).
    rewrite -> (fold_unfold_list_reverse_acc_cons V v vs' a).
    rewrite -> (IHvs' (v :: a)).
    rewrite -> (IHvs' (v :: nil)).
    rewrite <- list_append_is_associative.
    rewrite -> (fold_unfold_list_append_cons V v nil a).
    rewrite -> (fold_unfold_list_append_nil V a).
    reflexivity.
Qed.

Property list_append_and_list_reverse_acc_commute_with_each_other :
  forall (V : Type)
         (v1s v2s a : list V),
    list_reverse_acc V (list_append V v1s v2s) a =
      list_reverse_acc V v2s (list_reverse_acc V v1s a).
Proof.
  intros V v1s v2s.
  induction v1s as [ | v1 v1s' IHv1s'].
  * intros a.
    rewrite -> (fold_unfold_list_append_nil V v2s).
    rewrite -> (fold_unfold_list_reverse_acc_nil V a).
    reflexivity.
  * intros a.
    rewrite -> (fold_unfold_list_append_cons V v1 v1s').
    rewrite -> (fold_unfold_list_reverse_acc_cons V v1 v1s' a).
    rewrite -> (fold_unfold_list_reverse_acc_cons V v1 (list_append V v1s' v2s) a).
    exact (IHv1s' (v1::a)).
Qed. (* was proved in the FPP/LPP midterm project *)

(* ********** *)

(* Background material, Part II/II: binary trees.

   mirror, flatten, and flatten_alt
   and their associated fold-unfold lemmas *)

(* ***** *)

Inductive binary_tree (V : Type) : Type :=
  Leaf : V -> binary_tree V
| Node : binary_tree V -> binary_tree V -> binary_tree V.

Fixpoint eqb_binary_tree (V : Type) (eqb_V : V -> V -> bool) (t1 t2 : binary_tree V) : bool :=
  match t1 with
  | Leaf _ v1 =>
    match t2 with
    | Leaf _ v2 =>
      eqb_V v1 v2
    | Node _ t21 t22 =>
      false
    end
  | Node _ t11 t12 =>
    match t2 with
    | Leaf _ v2 =>
      false
    | Node _ t21 t22 =>
      eqb_binary_tree V eqb_V t11 t21 && eqb_binary_tree V eqb_V t12 t22
    end
  end.

(* ***** *)

Definition test_binary_tree_mirror (candidate : forall V : Type, binary_tree V -> binary_tree V) : bool :=
  (eqb_binary_tree
     nat
     Nat.eqb
     (candidate
        nat
        (Leaf nat 1))
     (Leaf nat 1))
  &&
  (eqb_binary_tree
     nat
     Nat.eqb
     (candidate
        nat
        (Node nat (Leaf nat 1) (Leaf nat 2)))
     (Node nat (Leaf nat 2) (Leaf nat 1)))
  &&
  (eqb_binary_tree
     nat
     Nat.eqb
     (candidate
        nat
        (Node nat
           (Node nat (Leaf nat 1) (Leaf nat 2))
           (Leaf nat 3)))
     (Node nat
           (Leaf nat 3)
           (Node nat (Leaf nat 2) (Leaf nat 1))))
  (* etc. *)
  .

Fixpoint binary_tree_mirror (V : Type) (t : binary_tree V) : binary_tree V :=
  match t with
    Leaf _ v =>
    Leaf V v
  | Node _ t1 t2 =>
    Node V (binary_tree_mirror V t2) (binary_tree_mirror V t1)
  end.

Compute (test_binary_tree_mirror binary_tree_mirror).

Lemma fold_unfold_binary_tree_mirror_Leaf :
  forall (V : Type)
         (v : V),
    binary_tree_mirror V (Leaf V v) =
    Leaf V v.
Proof.
  fold_unfold_tactic binary_tree_mirror.
Qed.

Lemma fold_unfold_binary_tree_mirror_Node :
  forall (V : Type)
         (t1 t2 : binary_tree V),
    binary_tree_mirror V (Node V t1 t2) =
    Node V (binary_tree_mirror V t2) (binary_tree_mirror V t1).
Proof.
  fold_unfold_tactic binary_tree_mirror.
Qed.

(* ***** *)

Definition test_binary_tree_flatten (candidate : forall V : Type, binary_tree V -> list V) : bool :=
  (eqb_list
     nat
     Nat.eqb
     (candidate
        nat
        (Leaf nat 1))
     (1 :: nil))
  &&
  (eqb_list
     nat
     Nat.eqb
     (candidate
        nat
        (Node nat (Leaf nat 1) (Leaf nat 2)))
     (1 :: 2 :: nil))
  &&
  (eqb_list
     nat
     Nat.eqb
     (candidate
        nat
        (Node nat
           (Node nat (Leaf nat 1) (Leaf nat 2))
           (Node nat (Leaf nat 3) (Leaf nat 4))))
     (1 :: 2 :: 3 :: 4 :: nil))
  (* etc. *)
  .

Fixpoint binary_tree_flatten (V : Type) (t : binary_tree V) : list V :=
  match t with
    Leaf _ v =>
    v :: nil
  | Node _ t1 t2 =>
    list_append V (binary_tree_flatten V t1) (binary_tree_flatten V t2)
  end.

Compute (test_binary_tree_flatten binary_tree_flatten).

Lemma fold_unfold_binary_tree_flatten_Leaf :
  forall (V : Type)
         (v : V),
    binary_tree_flatten V (Leaf V v) =
    v :: nil.
Proof.
  fold_unfold_tactic binary_tree_flatten.
Qed.

Lemma fold_unfold_binary_tree_flatten_Node :
  forall (V : Type)
         (t1 t2 : binary_tree V),
    binary_tree_flatten V (Node V t1 t2) =
    list_append V (binary_tree_flatten V t1) (binary_tree_flatten V t2).
Proof.
  fold_unfold_tactic binary_tree_flatten.
Qed.

(* ***** *)

Fixpoint binary_tree_flatten_acc (V : Type) (t : binary_tree V) (a : list V) : list V :=
  match t with
    Leaf _ v =>
    v :: a
  | Node _ t1 t2 =>
    binary_tree_flatten_acc V t1 (binary_tree_flatten_acc V t2 a)
  end.

Lemma fold_unfold_binary_tree_flatten_acc_Leaf :
  forall (V : Type)
         (v : V)
         (a : list V),
    binary_tree_flatten_acc V (Leaf V v) a =
    v :: a.
Proof.
  fold_unfold_tactic binary_tree_flatten_acc.
Qed.

Lemma fold_unfold_binary_tree_flatten_acc_Node :
  forall (V : Type)
         (t1 t2 : binary_tree V)
         (a : list V),
    binary_tree_flatten_acc V (Node V t1 t2) a =
    binary_tree_flatten_acc V t1 (binary_tree_flatten_acc V t2 a).
Proof.
  fold_unfold_tactic binary_tree_flatten.
Qed.

Definition binary_tree_flatten_alt (V : Type) (t : binary_tree V) : list V :=
  binary_tree_flatten_acc V t nil.

Compute (test_binary_tree_flatten binary_tree_flatten_alt).

Property about_binary_tree_flatten_acc :
  forall (V : Type)
         (t : binary_tree V)
         (a1 a2 : list V),
    binary_tree_flatten_acc V t (list_append V a1 a2) =
    list_append V (binary_tree_flatten_acc V t a1) a2.
Proof.
  Compute (let V := nat in
           let t := Node nat
                         (Node nat (Leaf nat 1) (Leaf nat 2))
                         (Node nat (Leaf nat 3) (Leaf nat 4)) in
           let a1 := 10 :: 20 :: nil in
           let a2 := 30 :: 40 :: nil in
           binary_tree_flatten_acc V t (list_append V a1 a2) =
             list_append V (binary_tree_flatten_acc V t a1) a2).
  intros V t.
  induction t as [v | t1 IHt1 t2 IHt2]; intros a1 a2.
  - rewrite ->2 fold_unfold_binary_tree_flatten_acc_Leaf.
    rewrite -> fold_unfold_list_append_cons.
    reflexivity.
  - rewrite ->2 fold_unfold_binary_tree_flatten_acc_Node.
    rewrite -> (IHt2 a1 a2).
    rewrite -> (IHt1 (binary_tree_flatten_acc V t2 a1) a2).
    reflexivity.
Qed.

(* ********** *)

(* 0. Concisely describe
      list_append, list_reverse, and list_reverse_alt
      and
      mirror, flatten, and flatten_alt
      as well as their associated properties. *)

(* TODO *)

(* ********** *)

(* 1.a Explain the following theorem. *)

(* This theorem states flattening a mirrored binary tree
   is equivalent to the reverse of the flattened binary tree. *)
Theorem about_mirroring_and_flattening_v1 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten V (binary_tree_mirror V t) =
    list_reverse V (binary_tree_flatten V t).
Proof.
   Compute (let V := nat in
            let t1 := Node V (Leaf V 1) (Leaf V 2) in
            let t2 := Node V (Leaf V 3) (Leaf V 4) in
            let t := Node V t1 t2 in
            binary_tree_flatten V (binary_tree_mirror V t) =
            list_reverse V (binary_tree_flatten V t)).
Abort. (* Don't prove this theorem, you will do that just below. *)

(* ***** *)

(* 1.b Prove Theorem about_mirroring_and_flattening_v1. *)

Theorem about_mirroring_and_flattening_v1 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten V (binary_tree_mirror V t) =
    list_reverse V (binary_tree_flatten V t).
Proof.
  intros V t.
  induction t as [v | t1 IHt1 t2 IHt2].
  - rewrite -> fold_unfold_binary_tree_mirror_Leaf.
    rewrite -> fold_unfold_binary_tree_flatten_Leaf.
    rewrite -> about_applying_list_reverse_to_a_singleton_list.
    reflexivity.
  - rewrite -> fold_unfold_binary_tree_mirror_Node.
    rewrite ->2 fold_unfold_binary_tree_flatten_Node.
    rewrite -> IHt1.
    rewrite -> IHt2.
    rewrite -> list_append_and_list_reverse_commute_with_each_other.
    reflexivity.
Qed.


(* ********** *)

(* 2.a Explain the following theorem. *)

Theorem about_mirroring_and_flattening_v2 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten V (binary_tree_mirror V t) =
      list_reverse_alt V (binary_tree_flatten V t).
Proof.
  Compute (let V := nat in
           let t1 := Node V (Leaf V 1) (Leaf V 2) in
           let t2 := Node V (Leaf V 3) (Leaf V 4) in
           let t := Node V t1 t2 in
           binary_tree_flatten V (binary_tree_mirror V t) =
           list_reverse_alt V (binary_tree_flatten V t)).
Abort. (* Don't prove this theorem, you will do that just below. *)

(* ***** *)

(* 2.b Prove Theorem about_mirroring_and_flattening_v2. *)

Lemma about_mirroring_and_flattening_v2_aux_v1 :
  forall (V : Type)
         (t : binary_tree V)
         (a : list V),
    list_append V (binary_tree_flatten V (binary_tree_mirror V t)) a =
      list_reverse_acc V (binary_tree_flatten V t) a.
Proof.
  intros V t.
  induction t as [n | t1 IHt1 t2 IHt2]; intros a.
  - rewrite -> fold_unfold_binary_tree_mirror_Leaf.
    rewrite -> fold_unfold_binary_tree_flatten_Leaf.
    Search list_append.
    rewrite -> about_applying_list_append_to_a_singleton_list.
    rewrite -> about_applying_list_reverse_acc_to_a_singleton_list.
    reflexivity.
  - rewrite -> fold_unfold_binary_tree_mirror_Node.
    rewrite ->2 fold_unfold_binary_tree_flatten_Node.
    Search list_reverse_acc.
    rewrite -> list_append_and_list_reverse_acc_commute_with_each_other.
    rewrite <- list_append_is_associative.
    Check (IHt1 a).
    rewrite -> (IHt1 a).
    Check (IHt2 (list_reverse_acc V (binary_tree_flatten V t1) a)).
    rewrite -> (IHt2 (list_reverse_acc V (binary_tree_flatten V t1) a)).
    reflexivity.
Qed.

Lemma about_mirroring_and_flattening_v2_aux_v2 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten V (binary_tree_mirror V t) =
      list_reverse_acc V (binary_tree_flatten V t) nil.
Proof.
  intros V t.
  induction t as [v | t1 IHt1 t2 IHt2].
  - rewrite -> fold_unfold_binary_tree_mirror_Leaf.
    rewrite -> fold_unfold_binary_tree_flatten_Leaf.
    rewrite -> fold_unfold_list_reverse_acc_cons.
    rewrite -> fold_unfold_list_reverse_acc_nil.
    reflexivity.
  - rewrite -> fold_unfold_binary_tree_mirror_Node.
    rewrite ->2 fold_unfold_binary_tree_flatten_Node.
    rewrite -> IHt1.
    rewrite -> IHt2.
    rewrite -> list_append_and_list_reverse_acc_commute_with_each_other.
    (* accummulator reset lemma *)
    rewrite -> (list_reverse_acc_reset V
                  (binary_tree_flatten V t2)
                  (list_reverse_acc V (binary_tree_flatten V t1) nil)).
    reflexivity.
Qed.

Theorem about_mirroring_and_flattening_v2 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten V (binary_tree_mirror V t) =
      list_reverse_alt V (binary_tree_flatten V t).
Proof.
  unfold list_reverse_alt.
  exact about_mirroring_and_flattening_v2_aux_v2.

  Restart.

  unfold list_reverse_alt.
  intros V t.
  Check (about_mirroring_and_flattening_v2_aux_v1).
  Check (about_mirroring_and_flattening_v2_aux_v1 V t).
  Check (about_mirroring_and_flattening_v2_aux_v1 V t nil).
  assert (H := about_mirroring_and_flattening_v2_aux_v1 V t nil).
  rewrite -> nil_is_right_neutral_for_list_append in H.
  exact H.
Qed.

(* Of course you can also prove about_mirroring_and_flattening_v2
   as a corollary of about_mirroring_and_flattening_v1
   but that is not the point: the point is to make you reason
   about functions that use an accumulator. *)

(* ********** *)

(* 3.a Explain the following theorem. *)

Theorem about_mirroring_and_flattening_v3 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten_alt V (binary_tree_mirror V t) =
      list_reverse_alt V (binary_tree_flatten_alt V t).
Proof.
  Compute (let V := nat in
           let t1 := Node V (Leaf V 1) (Leaf V 2) in
           let t2 := Node V (Leaf V 3) (Leaf V 4) in
           let t := Node V t1 t2 in
           binary_tree_flatten_alt V (binary_tree_mirror V t) =
           list_reverse_alt V (binary_tree_flatten_alt V t)).
Abort. (* Don't prove this theorem, you will do that just below. *)

(* ***** *)

(* 3.b Prove Theorem about_mirroring_and_flattening_v3. *)

Print binary_tree_flatten_acc.

Lemma binary_tree_flatten_acc_reset :
  forall (V : Type)
         (t : binary_tree V)
         (a : list V),
    binary_tree_flatten_acc V t a =
      list_append V (binary_tree_flatten_acc V t nil) a.
Proof.
  intros V.
  induction t as [v | t1 IHt1 t2 IHt2]; intro a.
  - rewrite ->2 fold_unfold_binary_tree_flatten_acc_Leaf.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
  - rewrite ->2 fold_unfold_binary_tree_flatten_acc_Node.
    rewrite -> (IHt1 (binary_tree_flatten_acc V t2 a)).
    rewrite -> (IHt1 (binary_tree_flatten_acc V t2 nil)).
    rewrite -> (IHt2 a).
    rewrite -> list_append_is_associative.
    reflexivity.
Qed.

Lemma about_mirroring_and_flattening_v3_aux_v1 :
  forall (V : Type)
         (t : binary_tree V)
         (a : list V),
    binary_tree_flatten_acc V (binary_tree_mirror V t) a =
      list_reverse_acc V (binary_tree_flatten_acc V t nil) a.
Proof.
  intros V t.
  induction t as [n | t1 IHt1 t2 IHt2]; intros a.
  - rewrite -> fold_unfold_binary_tree_mirror_Leaf.
    rewrite -> fold_unfold_binary_tree_flatten_acc_Leaf.
    rewrite -> fold_unfold_binary_tree_flatten_acc_Leaf.
    rewrite -> about_applying_list_reverse_acc_to_a_singleton_list.
    reflexivity.
  - rewrite -> fold_unfold_binary_tree_mirror_Node.
    rewrite -> fold_unfold_binary_tree_flatten_acc_Node.
    rewrite -> fold_unfold_binary_tree_flatten_acc_Node.
    Check (IHt1 a).
    rewrite -> (IHt1 a).
    Check (IHt2 (list_reverse_acc V (binary_tree_flatten_acc V t1 nil) a)).
    rewrite -> (IHt2 (list_reverse_acc V (binary_tree_flatten_acc V t1 nil) a)).
    Search (list_reverse_acc).
    rewrite <- list_append_and_list_reverse_acc_commute_with_each_other.
    Search (binary_tree_flatten_acc).
    Check (binary_tree_flatten_acc_reset).
    Check (binary_tree_flatten_acc_reset V).
    Check (binary_tree_flatten_acc_reset V t1).
    Check (binary_tree_flatten_acc_reset V t1 (binary_tree_flatten_acc V t2 nil)).
    rewrite -> (binary_tree_flatten_acc_reset V t1 (binary_tree_flatten_acc V t2 nil)).
    reflexivity.
Qed.

(* Spark of brilliance - not sure whether we can structurally comes up
   with this lemma *)
Lemma about_mirroring_and_flattening_v3_aux_v2 :
  forall (V : Type)
         (t : binary_tree V)
         (a1 a2 : list V),
    list_reverse_acc V a1 (binary_tree_flatten_acc V (binary_tree_mirror V t) a2) =
      list_reverse_acc V (binary_tree_flatten_acc V t a1) a2.
Proof.
  intros V t.
  induction t as [n | t1 IHt1 t2 IHt2]; intros a1 a2.
  - rewrite -> fold_unfold_binary_tree_mirror_Leaf.
    rewrite -> fold_unfold_binary_tree_flatten_acc_Leaf.
    rewrite -> fold_unfold_binary_tree_flatten_acc_Leaf.
    Search list_reverse_acc.
    rewrite -> fold_unfold_list_reverse_acc_cons.
    reflexivity.
  - rewrite -> fold_unfold_binary_tree_mirror_Node.
    rewrite -> fold_unfold_binary_tree_flatten_acc_Node.
    rewrite -> fold_unfold_binary_tree_flatten_acc_Node.
    Check (IHt2 a1).
    Check (IHt2 a1 (binary_tree_flatten_acc V (binary_tree_mirror V t1) a2)).
    rewrite -> (IHt2 a1 (binary_tree_flatten_acc V (binary_tree_mirror V t1) a2)).
    rewrite -> IHt1.
    reflexivity.
Qed.

Lemma about_mirroring_and_flattening_v3_aux_v3 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten_acc V (binary_tree_mirror V t) nil =
      list_reverse_acc V (binary_tree_flatten_acc V t nil) nil.
Proof.
  intros V t.
  induction t as [v | t1 IHt1 t2 IHt2].
  - rewrite -> fold_unfold_binary_tree_mirror_Leaf.
    rewrite -> fold_unfold_binary_tree_flatten_acc_Leaf.
    rewrite -> fold_unfold_list_reverse_acc_cons.
    rewrite -> fold_unfold_list_reverse_acc_nil.
    reflexivity.
  - rewrite -> fold_unfold_binary_tree_mirror_Node.
    rewrite ->2 fold_unfold_binary_tree_flatten_acc_Node.
    rewrite -> IHt1.
    rewrite -> binary_tree_flatten_acc_reset.
    rewrite -> (binary_tree_flatten_acc_reset
                  V t1 (binary_tree_flatten_acc V t2 nil)).
    rewrite -> IHt2.
    rewrite -> list_append_and_list_reverse_acc_commute_with_each_other.
    rewrite -> list_reverse_acc_reset.
    rewrite -> (list_reverse_acc_reset V
                  (binary_tree_flatten_acc V t2 nil)
                  (list_reverse_acc V (binary_tree_flatten_acc V t1 nil) nil)).
    rewrite -> nil_is_right_neutral_for_list_append.
    reflexivity.
Qed.

Theorem about_mirroring_and_flattening_v3 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten_alt V (binary_tree_mirror V t) =
      list_reverse_alt V (binary_tree_flatten_alt V t).
Proof.
  unfold binary_tree_flatten_alt.
  unfold list_reverse_alt.
  exact about_mirroring_and_flattening_v3_aux_v3.

  Restart.

  unfold list_reverse_alt, binary_tree_flatten_alt.
  intros V t.
  assert (H := about_mirroring_and_flattening_v3_aux_v2 V t nil nil).
  rewrite -> fold_unfold_list_reverse_acc_nil in H.
  exact H.

  Restart.

  unfold list_reverse_alt, binary_tree_flatten_alt.
  intros V t.
  exact (about_mirroring_and_flattening_v3_aux_v1 V t nil).
Qed.

(* Of course you can also prove about_mirroring_and_flattening_v3
   as a corollary of about_mirroring_and_flattening_v1 or of about_mirroring_and_flattening_v2
   but that is not the point: the point is to make you reason
   about functions that use an accumulator. *)

(* ********** *)

(* 4.a Explain the following theorem. *)

Theorem about_mirroring_and_flattening_v4 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten_alt V (binary_tree_mirror V t) =
      list_reverse V (binary_tree_flatten_alt V t).
Proof.
  Compute (let V := nat in
           let t1 := Node V (Leaf V 1) (Leaf V 2) in
           let t2 := Node V (Leaf V 3) (Leaf V 4) in
           let t := Node V t1 t2 in
           binary_tree_flatten_alt V (binary_tree_mirror V t) =
           list_reverse V (binary_tree_flatten_alt V t)).
Abort. (* Don't prove this theorem, you will do that just below. *)

(* ***** *)

(* 4.b Prove Theorem about_mirroring_and_flattening_v4. *)

Lemma about_mirroring_and_flattening_v4_aux :
  forall (V : Type)
         (t : binary_tree V)
         (a : list V),
    binary_tree_flatten_acc V (binary_tree_mirror V t) a =
      list_append V (list_reverse V (binary_tree_flatten_acc V t nil)) a.
Proof.
  intros V t.
  induction t as [n | t1 IHt1 t2 IHt2]; intros a.
  - rewrite -> fold_unfold_binary_tree_mirror_Leaf.
    rewrite ->2 fold_unfold_binary_tree_flatten_acc_Leaf.
    rewrite -> about_applying_list_reverse_to_a_singleton_list.
    rewrite -> about_applying_list_append_to_a_singleton_list.
    reflexivity.
  - rewrite -> fold_unfold_binary_tree_mirror_Node.
    rewrite -> fold_unfold_binary_tree_flatten_acc_Node.
    rewrite -> fold_unfold_binary_tree_flatten_acc_Node.
    rewrite -> (IHt1 a).
    rewrite -> (IHt2 (list_append V (list_reverse V (binary_tree_flatten_acc V t1 nil)) a)).
    rewrite -> (binary_tree_flatten_acc_reset V t1 (binary_tree_flatten_acc V t2 nil)).
    rewrite -> list_append_and_list_reverse_commute_with_each_other.
    rewrite -> list_append_is_associative.
    reflexivity.
Qed.

Theorem about_mirroring_and_flattening_v4 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten_alt V (binary_tree_mirror V t) =
      list_reverse V (binary_tree_flatten_alt V t).
Proof.
  unfold binary_tree_flatten_alt.
  intros V t.
  Check (about_mirroring_and_flattening_v4_aux V t nil).
  assert (H := about_mirroring_and_flattening_v4_aux V t nil).
  rewrite -> nil_is_right_neutral_for_list_append in H.
  exact H.
Qed.

(* Of course you can also prove about_mirroring_and_flattening_v4
   as a corollary of about_mirroring_and_flattening_v1 or of about_mirroring_and_flattening_v2 or of about_mirroring_and_flattening_v3
   but that is not the point: the point is to make you reason
   about functions that use an accumulator. *)

(* ********** *)

(* end of week-01_about-reversing-a-list-and-mirroring-a-tree.v *)
