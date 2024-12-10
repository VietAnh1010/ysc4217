Require Import Nat Arith Bool List.

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Times : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

Fixpoint arithmetic_expression_eqb (ae1 ae2 : arithmetic_expression) : bool :=
  match ae1, ae2 with
  | Literal n1, Literal n2 =>
    Nat.eqb n1 n2
  | Plus ae11 ae12, Plus ae21 ae22 =>
    arithmetic_expression_eqb ae11 ae21
    &&
    arithmetic_expression_eqb ae12 ae22
  | Minus ae11 ae12, Minus ae21 ae22 =>
    arithmetic_expression_eqb ae11 ae21
    &&
    arithmetic_expression_eqb ae12 ae22
  | Times ae11 ae12, Times ae21 ae22 =>
    arithmetic_expression_eqb ae11 ae21
    &&
    arithmetic_expression_eqb ae12 ae22
  | _, _ =>
    false
  end.

Inductive msg : Type :=
  Numerical_underflow : nat -> msg.

Inductive expressible_value : Type :=
  Expressible_nat : nat -> expressible_value
| Expressible_msg : msg -> expressible_value.

Fixpoint evaluate_ltr (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
    Expressible_nat n
  | Plus ae1 ae2 =>
    match evaluate_ltr ae1 with
    | Expressible_nat n1 =>
      match evaluate_ltr ae2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end
  | Minus ae1 ae2 =>
    match evaluate_ltr ae1 with
    | Expressible_nat n1 =>
      match evaluate_ltr ae2 with
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
  | Times ae1 ae2 =>
    match evaluate_ltr ae1 with
    | Expressible_nat n1 =>
      match evaluate_ltr ae2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 * n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end
  end.

Lemma fold_unfold_evaluate_ltr_Literal :
  forall (n : nat),
    evaluate_ltr (Literal n) =
    Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Lemma fold_unfold_evaluate_ltr_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_ltr (Plus ae1 ae2) =
    match evaluate_ltr ae1 with
      Expressible_nat n1 =>
      match evaluate_ltr ae2 with
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
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_ltr (Minus ae1 ae2) =
    match evaluate_ltr ae1 with
    | Expressible_nat n1 =>
      match evaluate_ltr ae2 with
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

Lemma fold_unfold_evaluate_ltr_Times :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_ltr (Times ae1 ae2) =
    match evaluate_ltr ae1 with
      Expressible_nat n1 =>
      match evaluate_ltr ae2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 * n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Definition test_simplify (candidate : arithmetic_expression -> arithmetic_expression) : bool :=
  (arithmetic_expression_eqb
     (candidate (Literal 0))
     (Literal 0))
  &&
  (arithmetic_expression_eqb
     (candidate (Literal 1))
     (Literal 1))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Literal 0)
           (Literal 1)))
     (Literal 1))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Literal 1)
           (Literal 0)))
     (Literal 1))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Literal 0)
           (Plus
              (Literal 0)
              (Literal 1))))
     (Literal 1))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Literal 1)
           (Plus
              (Literal 0)
              (Literal 1))))
     (Plus
        (Literal 1)
        (Literal 1)))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Plus
              (Literal 1)
              (Literal 0))
           (Plus
              (Literal 0)
              (Literal 0))))
     (Literal 1))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Minus
           (Literal 0)
           (Literal 1)))
     (Minus
        (Literal 0)
        (Literal 1)))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Minus
           (Literal 1)
           (Literal 0)))
     (Literal 1))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Minus
           (Minus
              (Literal 1)
              (Literal 0))
           (Plus
              (Literal 0)
              (Literal 0))))
     (Literal 1))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Minus
           (Plus
              (Literal 0)
              (Literal 1))
           (Minus
              (Literal 1)
              (Literal 0))))
     (Minus
        (Literal 1)
        (Literal 1)))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Minus
           (Plus
              (Literal 1)
              (Literal 2))
           (Minus
              (Literal 1)
              (Minus
                 (Literal 0)
                 (Literal 0)))))
     (Minus
        (Plus
           (Literal 1)
           (Literal 2))
        (Literal 1)))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Times
           (Literal 0)
           (Literal 2)))
     (Times
        (Literal 0)
        (Literal 2)))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Times
           (Literal 1)
           (Literal 2)))
     (Literal 2))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Times
           (Literal 2)
           (Literal 1)))
     (Literal 2))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Literal 1)
           (Times
              (Literal 2)
              (Literal 1))))
     (Plus
        (Literal 1)
        (Literal 2)))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Literal 1)
           (Times
              (Literal 1)
              (Literal 2))))
     (Plus
        (Literal 1)
        (Literal 2)))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Literal 1)
           (Times
              (Literal 1)
              (Literal 0))))
     (Literal 1))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Times
              (Literal 1)
              (Literal 0))
           (Literal 2)))
     (Literal 2))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Times
              (Literal 3)
              (Literal 9))
           (Literal 1)))
     (Plus
        (Times
           (Literal 3)
           (Literal 9))
        (Literal 1)))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Times
           (Minus
              (Literal 1)
              (Plus
                 (Literal 0)
                 (Literal 0)))
           (Plus
              (Literal 1)
              (Literal 2))))
     (Plus
        (Literal 1)
        (Literal 2)))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Times
           (Minus
              (Literal 1)
              (Plus
                 (Literal 1)
                 (Literal 0)))
           (Minus
              (Literal 1)
              (Plus
                 (Literal 0)
                 (Literal 0)))))
     (Minus
        (Literal 1)
        (Literal 1))).

Fixpoint simplify_0 (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
    Literal n
  | Plus ae1 ae2 =>
    let ae1' := simplify_0 ae1 in
    let ae2' := simplify_0 ae2 in
    match ae1', ae2' with
    | Literal 0, _ =>
      ae2'
    | _, Literal 0 =>
      ae1'
    | _, _ =>
      Plus ae1' ae2'
    end
  | Minus ae1 ae2 =>
    let ae1' := simplify_0 ae1 in
    let ae2' := simplify_0 ae2 in
    match ae2' with
    | Literal 0 =>
      ae1'
    | _ =>
      Minus ae1' ae2'
    end
  | Times ae1 ae2 =>
    let ae1' := simplify_0 ae1 in
    let ae2' := simplify_0 ae2 in
    match ae1', ae2' with
    | Literal 1, _ =>
      ae2'
    | _, Literal 1 =>
      ae1'
    | _, _ =>
      Times ae1' ae2'
    end
  end.

Compute (test_simplify simplify_0).

Inductive simplification_result : Type :=
  Zero : simplification_result
| One : simplification_result
| Partial : arithmetic_expression -> simplification_result.

Fixpoint simplify_aux (ae : arithmetic_expression) : simplification_result :=
  match ae with
  | Literal n =>
    match n with
    | 0 =>
      Zero
    | 1 =>
      One
    | S (S _) =>
      Partial (Literal n)
    end
  | Plus ae1 ae2 =>
    match simplify_aux ae1 with
    | Zero =>
      simplify_aux ae2
    | One =>
      match simplify_aux ae2 with
      | Zero =>
        One
      | One =>
        Partial (Plus (Literal 1) (Literal 1))
      | Partial ae2' =>
        Partial (Plus (Literal 1) ae2')
      end
    | Partial ae1' =>
      match simplify_aux ae2 with
      | Zero =>
        Partial ae1'
      | One =>
        Partial (Plus ae1' (Literal 1))
      | Partial ae2' =>
        Partial (Plus ae1' ae2')
      end
    end
  | Minus ae1 ae2 =>
    match simplify_aux ae1 with
    | Zero =>
      match simplify_aux ae2 with
      | Zero =>
        Zero
      | One =>
        Partial (Minus (Literal 0) (Literal 1))
      | Partial ae' =>
        Partial (Minus (Literal 0) ae')
      end
    | One =>
      match simplify_aux ae2 with
      | Zero =>
        One
      | One =>
        Partial (Minus (Literal 1) (Literal 1))
      | Partial ae2' =>
        Partial (Minus (Literal 1) ae2')
      end
    | Partial ae1' =>
      match simplify_aux ae2 with
      | Zero =>
        Partial ae1'
      | One =>
        Partial (Minus ae1' (Literal 1))
      | Partial ae2' =>
        Partial (Minus ae1' ae2')
      end
    end
  | Times ae1 ae2 =>
    match simplify_aux ae1 with
    | Zero =>
      match simplify_aux ae2 with
      | Zero =>
        Partial (Times (Literal 0) (Literal 0))
      | One =>
        Zero
      | Partial ae' =>
        Partial (Times (Literal 0) ae')
      end
    | One =>
      simplify_aux ae2
    | Partial ae1' =>
      match simplify_aux ae2 with
      | Zero =>
        Partial (Times ae1' (Literal 0))
      | One =>
        Partial ae1'
      | Partial ae2' =>
        Partial (Times ae1' ae2')
      end
    end
  end.

Definition arithmetic_expression_from_simplification_result (se : simplification_result) : arithmetic_expression :=
  match se with
  | Zero =>
    Literal 0
  | One =>
    Literal 1
  | Partial ae =>
    ae
  end.

Definition simplify (ae : arithmetic_expression) : arithmetic_expression :=
  arithmetic_expression_from_simplification_result (simplify_aux ae).

Compute (test_simplify simplify).

Lemma fold_unfold_simplify_aux_Literal :
  forall (n : nat),
    simplify_aux (Literal n) =
    match n with
    | 0 =>
      Zero
    | 1 =>
      One
    | S (S _) =>
      Partial (Literal n)
    end.
Proof.
  fold_unfold_tactic simplify_aux.
Qed.

Lemma fold_unfold_simplify_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    simplify_aux (Plus ae1 ae2) =
    match simplify_aux ae1 with
    | Zero =>
      simplify_aux ae2
    | One =>
      match simplify_aux ae2 with
      | Zero =>
        One
      | One =>
        Partial (Plus (Literal 1) (Literal 1))
      | Partial ae2' =>
        Partial (Plus (Literal 1) ae2')
      end
    | Partial ae1' =>
      match simplify_aux ae2 with
      | Zero =>
        Partial ae1'
      | One =>
        Partial (Plus ae1' (Literal 1))
      | Partial ae2' =>
        Partial (Plus ae1' ae2')
      end
    end.
Proof.
  fold_unfold_tactic simplify_aux.
Qed.

Lemma fold_unfold_simplify_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    simplify_aux (Minus ae1 ae2) =
    match simplify_aux ae1 with
    | Zero =>
      match simplify_aux ae2 with
      | Zero =>
        Zero
      | One =>
        Partial (Minus (Literal 0) (Literal 1))
      | Partial ae' =>
        Partial (Minus (Literal 0) ae')
      end
    | One =>
      match simplify_aux ae2 with
      | Zero =>
        One
      | One =>
        Partial (Minus (Literal 1) (Literal 1))
      | Partial ae2' =>
        Partial (Minus (Literal 1) ae2')
      end
    | Partial ae1' =>
      match simplify_aux ae2 with
      | Zero =>
        Partial ae1'
      | One =>
        Partial (Minus ae1' (Literal 1))
      | Partial ae2' =>
        Partial (Minus ae1' ae2')
      end
    end.
Proof.
  fold_unfold_tactic simplify_aux.
Qed.

Lemma fold_unfold_simplify_aux_Times :
  forall (ae1 ae2 : arithmetic_expression),
    simplify_aux (Times ae1 ae2) =
    match simplify_aux ae1 with
    | Zero =>
      match simplify_aux ae2 with
      | Zero =>
        Partial (Times (Literal 0) (Literal 0))
      | One =>
        Zero
      | Partial ae' =>
        Partial (Times (Literal 0) ae')
      end
    | One =>
      simplify_aux ae2
    | Partial ae1' =>
      match simplify_aux ae2 with
      | Zero =>
        Partial (Times ae1' (Literal 0))
      | One =>
        Partial ae1'
      | Partial ae2' =>
        Partial (Times ae1' ae2')
      end
    end.
Proof.
  fold_unfold_tactic simplify_aux.
Qed.

Lemma simplify_is_idempotent_aux :
  forall (ae : arithmetic_expression),
    simplify_aux (arithmetic_expression_from_simplification_result (simplify_aux ae)) =
    simplify_aux ae.
Proof.
  intros ae.
  induction ae as
    [ n
    | ae1 IHae1 ae2 IHae2
    | ae1 IHae1 ae2 IHae2
    | ae1 IHae1 ae2 IHae2
    ].
  - rewrite -> fold_unfold_simplify_aux_Literal.
    unfold arithmetic_expression_from_simplification_result.
    destruct n as [| [| n'']].
    + rewrite -> fold_unfold_simplify_aux_Literal.
      reflexivity.
    + rewrite -> fold_unfold_simplify_aux_Literal.
      reflexivity.
    + rewrite -> fold_unfold_simplify_aux_Literal.
      reflexivity.
  - rewrite -> fold_unfold_simplify_aux_Plus.
    destruct (simplify_aux ae1) as [| | ae1'].
    + exact IHae2.
    + destruct (simplify_aux ae2) as [| | ae2'].
      * exact IHae1.
      * unfold arithmetic_expression_from_simplification_result.
        rewrite -> fold_unfold_simplify_aux_Plus.
        rewrite -> fold_unfold_simplify_aux_Literal.
        reflexivity.
      * unfold arithmetic_expression_from_simplification_result.
        unfold arithmetic_expression_from_simplification_result in IHae2.
        rewrite -> fold_unfold_simplify_aux_Plus.
        rewrite -> fold_unfold_simplify_aux_Literal.
        rewrite -> IHae2.
        reflexivity.
    + destruct (simplify_aux ae2) as [| | ae2'].
      * exact IHae1.
      * unfold arithmetic_expression_from_simplification_result.
        unfold arithmetic_expression_from_simplification_result in IHae1.
        rewrite -> fold_unfold_simplify_aux_Plus.
        rewrite -> IHae1.
        rewrite -> fold_unfold_simplify_aux_Literal.
        reflexivity.
      * unfold arithmetic_expression_from_simplification_result.
        unfold arithmetic_expression_from_simplification_result in IHae1.
        unfold arithmetic_expression_from_simplification_result in IHae2.
        rewrite -> fold_unfold_simplify_aux_Plus.
        rewrite -> IHae1.
        rewrite -> IHae2.
        reflexivity.
  - rewrite -> fold_unfold_simplify_aux_Minus.
    destruct (simplify_aux ae1) as [| | ae1'].
    + destruct (simplify_aux ae2) as [| | ae2'].
      * exact IHae2.
      * unfold arithmetic_expression_from_simplification_result.
        rewrite -> fold_unfold_simplify_aux_Minus.
        rewrite -> fold_unfold_simplify_aux_Literal.
        rewrite -> fold_unfold_simplify_aux_Literal.
        reflexivity.
      * unfold arithmetic_expression_from_simplification_result.
        unfold arithmetic_expression_from_simplification_result in IHae2.
        rewrite -> fold_unfold_simplify_aux_Minus.
        rewrite -> fold_unfold_simplify_aux_Literal.
        rewrite -> IHae2.
        reflexivity.
    + destruct (simplify_aux ae2) as [| | ae2'].
      * exact IHae1.
      * unfold arithmetic_expression_from_simplification_result.
        rewrite -> fold_unfold_simplify_aux_Minus.
        rewrite -> fold_unfold_simplify_aux_Literal.
        reflexivity.
      * unfold arithmetic_expression_from_simplification_result.
        unfold arithmetic_expression_from_simplification_result in IHae2.
        rewrite -> fold_unfold_simplify_aux_Minus.
        rewrite -> fold_unfold_simplify_aux_Literal.
        rewrite -> IHae2.
        reflexivity.
    + destruct (simplify_aux ae2) as [| | ae2'].
      * exact IHae1.
      * unfold arithmetic_expression_from_simplification_result.
        unfold arithmetic_expression_from_simplification_result in IHae1.
        rewrite -> fold_unfold_simplify_aux_Minus.
        rewrite -> fold_unfold_simplify_aux_Literal.
        rewrite -> IHae1.
        reflexivity.
      * unfold arithmetic_expression_from_simplification_result.
        unfold arithmetic_expression_from_simplification_result in IHae1.
        unfold arithmetic_expression_from_simplification_result in IHae2.
        rewrite -> fold_unfold_simplify_aux_Minus.
        rewrite -> IHae1.
        rewrite -> IHae2.
        reflexivity.
  - rewrite -> fold_unfold_simplify_aux_Times.
    destruct (simplify_aux ae1) as [| | ae1'].
    + destruct (simplify_aux ae2) as [| | ae2'].
      * unfold arithmetic_expression_from_simplification_result.
        rewrite -> fold_unfold_simplify_aux_Times.
        rewrite -> fold_unfold_simplify_aux_Literal.
        reflexivity.
      * exact IHae1.
      * unfold arithmetic_expression_from_simplification_result.
        unfold arithmetic_expression_from_simplification_result in IHae2.
        rewrite -> fold_unfold_simplify_aux_Times.
        rewrite -> fold_unfold_simplify_aux_Literal.
        rewrite -> IHae2.
        reflexivity.
    + exact IHae2.
    + destruct (simplify_aux ae2) as [| | ae2'].
      * unfold arithmetic_expression_from_simplification_result.
        unfold arithmetic_expression_from_simplification_result in IHae1.
        rewrite -> fold_unfold_simplify_aux_Times.
        rewrite -> fold_unfold_simplify_aux_Literal.
        rewrite -> IHae1.
        reflexivity.
      * exact IHae1.
      * unfold arithmetic_expression_from_simplification_result.
        unfold arithmetic_expression_from_simplification_result in IHae1.
        unfold arithmetic_expression_from_simplification_result in IHae2.
        rewrite -> fold_unfold_simplify_aux_Times.
        rewrite -> IHae1.
        rewrite -> IHae2.
        reflexivity.
Qed.

Theorem simplify_is_idempotent :
  forall (ae : arithmetic_expression),
    simplify (simplify ae) =
    simplify ae.
Proof.
  intros ae.
  unfold simplify.
  rewrite -> simplify_is_idempotent_aux.
  reflexivity.
Qed.

Proposition Literal_0_is_neutral_for_Plus_on_the_left_ltr :
  forall (ae : arithmetic_expression),
    evaluate_ltr (Plus (Literal 0) ae) =
    evaluate_ltr ae.
Proof.
  intros ae.
  rewrite -> fold_unfold_evaluate_ltr_Plus.
  rewrite -> fold_unfold_evaluate_ltr_Literal.
  destruct (evaluate_ltr ae) as [n | s].
  * rewrite -> plus_O_n.
    reflexivity.
  * reflexivity.
Qed.

Proposition Literal_0_is_neutral_for_Plus_on_the_right_ltr :
  forall (ae : arithmetic_expression),
    evaluate_ltr (Plus ae (Literal 0)) =
    evaluate_ltr ae.
Proof.
  intros ae.
  rewrite -> fold_unfold_evaluate_ltr_Plus.
  rewrite -> fold_unfold_evaluate_ltr_Literal.
  destruct (evaluate_ltr ae) as [n | s].
  * rewrite <- plus_n_O.
    reflexivity.
  * reflexivity.
Qed.

Proposition Literal_1_is_neutral_for_Times_on_the_left_ltr :
  forall (ae : arithmetic_expression),
    evaluate_ltr (Times (Literal 1) ae) =
    evaluate_ltr ae.
Proof.
  intros ae.
  rewrite -> fold_unfold_evaluate_ltr_Times.
  rewrite -> fold_unfold_evaluate_ltr_Literal.
  destruct (evaluate_ltr ae) as [n | s].
  * rewrite -> Nat.mul_1_l.
    reflexivity.
  * reflexivity.
Qed.

Proposition Literal_1_is_neutral_for_Times_on_the_right_ltr :
  forall (ae : arithmetic_expression),
    evaluate_ltr (Times ae (Literal 1)) =
    evaluate_ltr ae.
Proof.
  intros ae.
  rewrite -> fold_unfold_evaluate_ltr_Times.
  rewrite -> fold_unfold_evaluate_ltr_Literal.
  destruct (evaluate_ltr ae) as [n | s].
  * rewrite -> Nat.mul_1_r.
    reflexivity.
  * reflexivity.
Qed.

Proposition Literal_0_is_neutral_for_Minus_on_the_right_ltr :
  forall (ae : arithmetic_expression),
    evaluate_ltr (Minus ae (Literal 0)) =
    evaluate_ltr ae.
Proof.
  intros ae.
  rewrite -> fold_unfold_evaluate_ltr_Minus.
  rewrite -> fold_unfold_evaluate_ltr_Literal.
  destruct (evaluate_ltr ae) as [n | s].
  * assert (n_not_lt_0 : n <? 0 = false).
    { rewrite -> Nat.ltb_ge.
      exact (Nat.le_0_l n). }
    rewrite -> n_not_lt_0.
    rewrite -> Nat.sub_0_r.
    reflexivity.
  * reflexivity.
Qed.

Lemma simplifying_preserves_evaluation_ltr_aux :
  forall (ae : arithmetic_expression),
    evaluate_ltr (arithmetic_expression_from_simplification_result (simplify_aux ae)) =
    evaluate_ltr ae.
Proof.
  intros ae.
  induction ae as
    [ n
    | ae1 IHae1 ae2 IHae2
    | ae1 IHae1 ae2 IHae2
    | ae1 IHae1 ae2 IHae2
    ].
  - rewrite -> fold_unfold_simplify_aux_Literal.
    unfold arithmetic_expression_from_simplification_result.
    destruct n as [| [| n'']].
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - rewrite -> fold_unfold_simplify_aux_Plus.
    rewrite -> fold_unfold_evaluate_ltr_Plus.
    destruct (simplify_aux ae1) as [| | ae1'].
    + unfold arithmetic_expression_from_simplification_result in IHae1.
      rewrite <- IHae1.
      rewrite <- fold_unfold_evaluate_ltr_Plus.
      rewrite -> Literal_0_is_neutral_for_Plus_on_the_left_ltr.
      exact IHae2.
    + destruct (simplify_aux ae2) as [| | ae2'].
      * unfold arithmetic_expression_from_simplification_result in IHae2.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Plus.
        rewrite -> Literal_0_is_neutral_for_Plus_on_the_right_ltr.
        exact IHae1.
      * rewrite <- IHae1.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Plus.
        unfold arithmetic_expression_from_simplification_result.
        reflexivity.
      * rewrite <- IHae1.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Plus.
        unfold arithmetic_expression_from_simplification_result.
        reflexivity.
    + destruct (simplify_aux ae2) as [| | ae2'].
      * unfold arithmetic_expression_from_simplification_result in IHae2.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Plus.
        rewrite -> Literal_0_is_neutral_for_Plus_on_the_right_ltr.
        exact IHae1.
      * rewrite <- IHae1.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Plus.
        unfold arithmetic_expression_from_simplification_result.
        reflexivity.
      * rewrite <- IHae1.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Plus.
        unfold arithmetic_expression_from_simplification_result.
        reflexivity.
  - rewrite -> fold_unfold_simplify_aux_Minus.
    rewrite -> fold_unfold_evaluate_ltr_Minus.
    destruct (simplify_aux ae1) as [| | ae1'].
    + destruct (simplify_aux ae2) as [| | ae2'].
      * unfold arithmetic_expression_from_simplification_result in IHae2.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Minus.
        rewrite -> Literal_0_is_neutral_for_Minus_on_the_right_ltr.
        exact IHae1.
      * rewrite <- IHae1.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Minus.
        unfold arithmetic_expression_from_simplification_result.
        reflexivity.
      * rewrite <- IHae1.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Minus.
        unfold arithmetic_expression_from_simplification_result.
        reflexivity.
    + destruct (simplify_aux ae2) as [| | ae2'].
      * unfold arithmetic_expression_from_simplification_result in IHae2.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Minus.
        rewrite -> Literal_0_is_neutral_for_Minus_on_the_right_ltr.
        exact IHae1.
      * rewrite <- IHae1.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Minus.
        unfold arithmetic_expression_from_simplification_result.
        reflexivity.
      * rewrite <- IHae1.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Minus.
        unfold arithmetic_expression_from_simplification_result.
        reflexivity.
    + destruct (simplify_aux ae2) as [| | ae2'].
      * unfold arithmetic_expression_from_simplification_result in IHae2.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Minus.
        rewrite -> Literal_0_is_neutral_for_Minus_on_the_right_ltr.
        exact IHae1.
      * rewrite <- IHae1.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Minus.
        unfold arithmetic_expression_from_simplification_result.
        reflexivity.
      * rewrite <- IHae1.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Minus.
        unfold arithmetic_expression_from_simplification_result.
        reflexivity.
  - rewrite -> fold_unfold_simplify_aux_Times.
    rewrite -> fold_unfold_evaluate_ltr_Times.
    destruct (simplify_aux ae1) as [| | ae1'].
    + destruct (simplify_aux ae2) as [| | ae2'].
      * rewrite <- IHae1.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Times.
        unfold arithmetic_expression_from_simplification_result.
        reflexivity.
      * unfold arithmetic_expression_from_simplification_result in IHae2.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Times.
        rewrite -> Literal_1_is_neutral_for_Times_on_the_right_ltr.
        exact IHae1.
      * rewrite <- IHae1.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Times.
        unfold arithmetic_expression_from_simplification_result.
        reflexivity.
    + unfold arithmetic_expression_from_simplification_result in IHae1.
      rewrite <- IHae1.
      rewrite <- fold_unfold_evaluate_ltr_Times.
      rewrite -> Literal_1_is_neutral_for_Times_on_the_left_ltr.
      exact IHae2.
    + destruct (simplify_aux ae2) as [| | ae2'].
      * rewrite <- IHae1.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Times.
        unfold arithmetic_expression_from_simplification_result.
        reflexivity.
      * unfold arithmetic_expression_from_simplification_result in IHae2.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Times.
        rewrite -> Literal_1_is_neutral_for_Times_on_the_right_ltr.
        exact IHae1.
      * rewrite <- IHae1.
        rewrite <- IHae2.
        rewrite <- fold_unfold_evaluate_ltr_Times.
        unfold arithmetic_expression_from_simplification_result.
        reflexivity.
Qed.

Theorem simplifying_preserves_evaluation_ltr :
  forall (ae : arithmetic_expression),
    evaluate_ltr (simplify ae) =
    evaluate_ltr ae.
Proof.
  unfold simplify.
  exact simplifying_preserves_evaluation_ltr_aux.
Qed.
