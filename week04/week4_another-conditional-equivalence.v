(* week-04_another-conditional-equivalence.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 05 Sep 2024 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Nat Arith Bool List.

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Simpler error messages than string encoding. *)

Inductive msg : Type :=
  Numerical_underflow : nat -> msg.

Inductive expressible_value : Type :=
  Expressible_nat : nat -> expressible_value
| Expressible_msg : msg -> expressible_value.

Fixpoint evaluate_ltr (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
    Expressible_nat n
  | Plus e1 e2 =>
    match evaluate_ltr e1 with
    | Expressible_nat n1 =>
      match evaluate_ltr e2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end
  | Minus e1 e2 =>
    match evaluate_ltr e1 with
    | Expressible_nat n1 =>
      match evaluate_ltr e2 with
      | Expressible_nat n2 =>
        if n1 <? n2
        then Expressible_msg (Numerical_underflow (n2 - n1))
        else Expressible_nat (n1 - n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end
  end.

Lemma fold_unfold_evaluate_ltr_Literal :
  forall n : nat,
    evaluate_ltr (Literal n) =
    Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Lemma fold_unfold_evaluate_ltr_Plus :
  forall e1 e2 : arithmetic_expression,
    evaluate_ltr (Plus e1 e2) =
    match evaluate_ltr e1 with
    | Expressible_nat n1 =>
      match evaluate_ltr e2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Lemma fold_unfold_evaluate_ltr_Minus :
  forall e1 e2 : arithmetic_expression,
    evaluate_ltr (Minus e1 e2) =
    match evaluate_ltr e1 with
    | Expressible_nat n1 =>
      match evaluate_ltr e2 with
      | Expressible_nat n2 =>
        if n1 <? n2
        then Expressible_msg (Numerical_underflow (n2 - n1))
        else Expressible_nat (n1 - n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

(* ********** *)

(* Task 1: Prove the following observational inequivalence. *)

Proposition Minus_is_not_associative_sort_of :
  exists ae1 ae2 ae3 : arithmetic_expression,
    evaluate_ltr (Minus (Minus ae1 ae2) ae3)
    <>
    evaluate_ltr (Minus ae1 (Plus ae2 ae3)).
Proof.
  exists (Literal 0), (Literal 1), (Literal 100).
  compute.
  intros H_absurd.
  discriminate H_absurd.
Qed.

(* ********** *)

(* Task 2: Complete and prove the following conditional observational equivalence. *)

Proposition Minus_is_conditionally_associative_sort_of :
  forall ae1 ae2 ae3 : arithmetic_expression,
    evaluate_ltr (Minus (Minus ae1 ae2) ae3) =
    evaluate_ltr (Minus ae1 (Plus ae2 ae3)).
Proof.
  intros ae1 ae2 ae3.
  rewrite ->3 fold_unfold_evaluate_ltr_Minus.
  rewrite -> fold_unfold_evaluate_ltr_Plus.
  destruct (evaluate_ltr ae1) as [n1 | s1].
  - destruct (evaluate_ltr ae2) as [n2 | s2].
    + destruct (evaluate_ltr ae3) as [n3 | s3].
      * destruct (n1 <? n2) eqn:H_n1_n2.
        {
          destruct (n1 <? n2 + n3) eqn:H_n1_n2_add_n3.
          { (* ae1, ae2, ae3 ok *)
            (* n1 <? n2 = true *)
            (* n1 <? n2 + n3 = true *)
            (* req: n2 - n1 = n2 + n3 - n1 *)
            (* req: n3 = 0 *)
            admit. }
          { (* n1 <? n2 = true *)
            (* n1 <? n2 + n3 = false *)
            (* absurd *)
            (* can be proven *)
            admit. }
        }
        { (* n1 <? n2 = false *)
          destruct (n1 - n2 <? n3) eqn:H_n1_n2_lt_n3.
          {
            destruct (n1 <? n2 + n3) eqn:H_n1_n2_add_n3.
            { (* ae1, ae2, ae3 ok *)
              (* n1 <? n2 = false *)
              (* n1 - n2 <? n3 = true => n1 <? n2 + n3 = true *)
              (* n1 <? n2 + n3 = true *)
              (* req: n3 - (n1 - n2) = n2 + n3 - n1 *)
              (* can be proven *)
              admit. }
            { (* ae1, ae2, ae3 ok *)
              (* n1 <? n2 = false *)
              (* n1 - n2 <? n3 = true => n1 <? n2 + n3 = true *)
              (* n1 <? n2 + n3 = false *)
              (* absurd *)
              (* can be proven *)
              admit. }
          }
          {
            destruct (n1 <? n2 + n3) eqn:H_n1_lt_n2_add_n3.
            { (* ae1, ae2, ae3 ok *)
              (* n1 <? n2 = false *)
              (* n1 - n2 <? n3 = false => n1 <? n2 + n3 = false *)
              (* n1 <? n2 + n3 = true *)
              (* absurd *)
              (* can be proven *)
              admit. }
            { (* no err at all! *)
              (* can definitely be proven *)
              admit. }
          }
        }
      * (* ae3 -> err *)
        destruct (n1 <? n2) eqn:H_n1_lt_n2.
        { (* n1 <? n2 = true *)
          (* ae3 err *)
          (* req: s3 = Numerical_underflow (n2 - n1) *)
          admit. }
        { (* n1 <? n2 = false *)
          (* ae3 err *)
          reflexivity. }
    + reflexivity.
  - reflexivity.
Abort.

(*
   In summary, we need:
   - ae1 err
   - ae2 err
   - ae1 ok, ae2 ok
     + ae3 ok
       * n1 <? n2 = true; n3 = 0
       * n1 <? n2 = false
     + ae3 err
       * n1 <? n2 = true; s3 = Numerical_underflow (n2 - n1)
       * n1 <? n2 = false

   Rewrite the last case:
   - ae1 ok, ae2 ok
     + n1 <? n2 = true (ae1 - ae2 err)
       * ae3 ok; n3 = 0
       * ae3 err; s3 = Numerical_underflow (n2 - n1)
     + n1 <? n2 = false (ae1 - ae2 ok)
 *)

Lemma le_le_sub_r_le_add_l_r :
  forall x y z : nat,
    z <= y ->
    x <= y - z ->
    x + z <= y.
Proof.
  intros x y z H_z_y H_x_y_sub_z.
  Search (_ - _ + _).
  Check (Nat.sub_add z y H_z_y).
  rewrite <- (Nat.sub_add z y H_z_y).
  Search (_ <= _ -> _ + _ <= _ + _).
  Check (add_le_mono_r_proj_l2r).
  Check (add_le_mono_r_proj_l2r x).
  Check (add_le_mono_r_proj_l2r x (y - z)).
  Check (add_le_mono_r_proj_l2r x (y - z) z H_x_y_sub_z).
  exact (add_le_mono_r_proj_l2r x (y - z) z H_x_y_sub_z).
Qed.

Lemma le_le_sub_r_le_add_l_l :
  forall x y z : nat,
    z <= y ->
    x <= y - z ->
    z + x <= y.
Proof.
  intros x y z H_z_y H_x_y_sub_z.
  rewrite -> Nat.add_comm.
  exact (le_le_sub_r_le_add_l_r _ _ _ H_z_y H_x_y_sub_z).
Qed.

Theorem sub_sub_assoc :
  forall x y z : nat,
    z <= y ->
    x - (y - z) = x + z - y.
Proof.
  intros x y z H_z_y.
  induction x as [| x'].
  - rewrite <- (Nat.sub_0_le z y) in H_z_y.
    rewrite -> Nat.sub_0_l.
    rewrite -> Nat.add_0_l.
    symmetry.
    exact H_z_y.
  - Search (S _ - _).
    Search (_ <= _).
    Check (le_lt_dec (y - z) x').
    destruct (le_lt_dec (y - z) x') as [H_y_sub_z_x' | H_x'_y_sub_z].
    + Check (Nat.sub_succ_l _ _ H_y_sub_z_x').
      rewrite -> (Nat.sub_succ_l _ _ H_y_sub_z_x').
      rewrite -> Nat.add_succ_l.
      Search (_ - _ <= _).
      Check (Nat.le_sub_le_add_r).
      Check (Nat.le_sub_le_add_r y).
      Check (Nat.le_sub_le_add_r y x').
      Check (Nat.le_sub_le_add_r y x' z).
      destruct (Nat.le_sub_le_add_r y x' z) as [H_y_x'_add_z _].
      assert (H_y_x'_add_z := H_y_x'_add_z H_y_sub_z_x').
      rewrite -> (Nat.sub_succ_l _ _ H_y_x'_add_z).
      apply f_equal.
      exact IHx'.
    + Search (S _ <= _).
      Check (Nat.le_succ_l).
      Check (Nat.le_succ_l x').
      Check (Nat.le_succ_l x' (y - z)).
      destruct (Nat.le_succ_l x' (y - z)) as [_ H_Sx'_y_sub_z].
      assert (H_Sx'_y_sub_z := H_Sx'_y_sub_z H_x'_y_sub_z).
      assert (H_Sx'_add_z_y := le_le_sub_r_le_add_l_r _ _ _ H_z_y H_Sx'_y_sub_z).
      destruct (Nat.sub_0_le (S x') (y - z)) as [_ H_lhs].
      destruct (Nat.sub_0_le (S x' + z) y) as [_ H_rhs].
      rewrite -> (H_lhs H_Sx'_y_sub_z).
      rewrite -> (H_rhs H_Sx'_add_z_y).
      reflexivity.
Qed.

Lemma ltb_sub_l_true_ltb_add_r_l_true :
  forall x y z : nat,
    x - y <? z = true ->
    x <? y + z = true.
Proof.
  intros x y z H_x_sub_y_z.
  rewrite -> Nat.ltb_lt in H_x_sub_y_z.
  rewrite -> Nat.ltb_lt.
  Search (_ -> _ < _ + _).
  Check (Nat.lt_sub_lt_add_l _ _ _ H_x_sub_y_z).
  exact (Nat.lt_sub_lt_add_l _ _ _ H_x_sub_y_z).
Qed.

Lemma ltb_true_ltb_add_r_r_true :
  forall x y z : nat,
    x <? y = true ->
    x <? y + z = true.
Proof.
  intros x y z H_x_y.
  rewrite -> Nat.ltb_lt in H_x_y.
  rewrite -> Nat.ltb_lt.
  exact (Nat.lt_lt_add_r x y z H_x_y).
Qed.

Lemma ltb_false_ltb_sub_l_false_ltb_add_r_l_false :
  forall x y z : nat,
    x <? y = false ->
    x - y <? z = false ->
    x <? y + z = false.
Proof.
  intros x y z H_x_y H_z_x_sub_y.
  rewrite -> Nat.ltb_ge in H_x_y.
  rewrite -> Nat.ltb_ge in H_z_x_sub_y.
  rewrite -> Nat.ltb_ge.
  Check (le_le_sub_r_le_add_l_r _ _ _ H_x_y H_z_x_sub_y).
  exact (le_le_sub_r_le_add_l_l _ _ _ H_x_y H_z_x_sub_y).
Qed.

Proposition Minus_is_conditionally_associative_sort_of :
  forall ae1 ae2 ae3 : arithmetic_expression,
    (exists s1 : msg, evaluate_ltr ae1 = Expressible_msg s1)
    \/
    (exists s2 : msg, evaluate_ltr ae2 = Expressible_msg s2)
    \/
    (exists n1 n2 : nat,
        evaluate_ltr ae1 = Expressible_nat n1 /\
        evaluate_ltr ae2 = Expressible_nat n2 /\
        ((n1 <? n2 = true /\ evaluate_ltr ae3 = Expressible_nat 0) \/
         (n1 <? n2 = true /\ evaluate_ltr ae3 = Expressible_msg (Numerical_underflow (n2 - n1))) \/
         (n1 <? n2 = false)))
    <->
    evaluate_ltr (Minus (Minus ae1 ae2) ae3) =
    evaluate_ltr (Minus ae1 (Plus ae2 ae3)).
Proof.
  intros ae1 ae2 ae3.
  split.
  {
    intros H.
    rewrite ->3 fold_unfold_evaluate_ltr_Minus.
    rewrite -> fold_unfold_evaluate_ltr_Plus.
    destruct H as [[s1 H_ae1] | H].
    { rewrite -> H_ae1.
      reflexivity. }
    destruct H as [[s2 H_ae2] | H].
    { rewrite -> H_ae2.
      destruct (evaluate_ltr ae1) as [n1 | s1].
      - reflexivity.
      - reflexivity. }
    destruct H as [n1 [n2 [H_ae1 [H_ae2 H]]]].
    rewrite -> H_ae1.
    rewrite -> H_ae2.
    destruct H as [[H_n1_n2 H_ae3] | [[H_n1_n2 H_ae3] | H_n1_n2]].
    { rewrite -> H_ae3.
      rewrite -> Nat.add_0_r.
      rewrite -> H_n1_n2.
      reflexivity. }
    { rewrite -> H_ae3.
      rewrite -> H_n1_n2.
      reflexivity. }
    {
      rewrite -> H_n1_n2.
      destruct (evaluate_ltr ae3) as [n3 | s3].
      - destruct (n1 - n2 <? n3) eqn:H_n1_sub_n2_n3.
        + rewrite -> (ltb_sub_l_true_ltb_add_r_l_true _ _ _ H_n1_sub_n2_n3).
          rewrite -> Nat.add_comm.
          rewrite -> Nat.ltb_ge in H_n1_n2.
          rewrite -> (sub_sub_assoc _ _ _ H_n1_n2).
          reflexivity.
        + rewrite -> (ltb_false_ltb_sub_l_false_ltb_add_r_l_false _ _ _ H_n1_n2 H_n1_sub_n2_n3).
          rewrite -> Nat.sub_add_distr.
          reflexivity.
      - reflexivity.
    }
  }
  {
    intros H.
    rewrite ->3 fold_unfold_evaluate_ltr_Minus in H.
    rewrite -> fold_unfold_evaluate_ltr_Plus in H.
    destruct (evaluate_ltr ae1) as [n1 | s1].
    - destruct (evaluate_ltr ae2) as [n2 | s2].
      + right. right.
        exists n1, n2.
        split.
        { reflexivity. }
        split.
        { reflexivity. }
        destruct (n1 <? n2) eqn:H_n1_n2.
        {
          destruct (evaluate_ltr ae3) as [n3 | s3].
          - rewrite -> (ltb_true_ltb_add_r_r_true _ _ n3 H_n1_n2) in H.
            injection H as H.
            rewrite -> Nat.ltb_lt in H_n1_n2.
            assert (H_n1_n2' := Nat.lt_le_incl _ _ H_n1_n2).
            rewrite <- (Nat.add_0_r (n2 - n1)) in H.
            rewrite -> (Nat.add_sub_swap _ _ _ H_n1_n2') in H.
            Check (Nat.add_cancel_l).
            Check (Nat.add_cancel_l 0).
            Check (Nat.add_cancel_l 0 n3).
            Check (Nat.add_cancel_l 0 n3 (n2 - n1)).
            rewrite -> (Nat.add_cancel_l 0 n3 (n2 - n1)) in H.
            left.
            split.
            + reflexivity.
            + rewrite -> H.
              reflexivity.
          - right. left.
            split.
            + reflexivity.
            + symmetry.
              exact H.
        }
        { right. right.
          reflexivity. }
      + right. left.
        exists s2.
        exact H.
    - left.
      exists s1.
      exact H.
  }
Qed.

(* Reminder: The treatment of errors is simplified. *)

(* ********** *)

(* end of week-04_another-conditional-equivalence.v *)
