(* week-04_refactoring-typefully.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 05 Sep 2024 *)

(* ********** *)

(* The new points below are delimited with \begin{NEW} and \end{NEW}. *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* \begin{NEW} *)
(* Simpler error messages than string encoding. *)

Inductive msg : Type :=
  Numerical_underflow : nat -> msg.

Inductive expressible_value : Type :=
  Expressible_nat : nat -> expressible_value
| Expressible_msg : msg -> expressible_value.
(* \end{NEW} *)

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
  forall (n : nat),
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

Fixpoint super_refactor_right (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
    Literal n =>
    Literal n
  | Plus ae1 ae2 =>
    super_refactor_right_aux ae1 (super_refactor_right ae2)
  | Minus ae1 ae2 =>
    Minus (super_refactor_right ae1) (super_refactor_right ae2)
  end
  with super_refactor_right_aux (ae1 a : arithmetic_expression) : arithmetic_expression :=
    match ae1 with
      Literal n =>
      Plus (Literal n) a
    | Plus ae1 ae2 =>
      super_refactor_right_aux ae1 (super_refactor_right_aux ae2 a)
    | Minus ae1 ae2 =>
      Plus (Minus (super_refactor_right ae1) (super_refactor_right ae2)) a
    end.

Lemma fold_unfold_super_refactor_right_Literal :
  forall (n : nat),
    super_refactor_right (Literal n) =
    Literal n.
Proof.
  fold_unfold_tactic super_refactor_right.
Qed.

Lemma fold_unfold_super_refactor_right_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    super_refactor_right (Plus ae1 ae2) =
    super_refactor_right_aux ae1 (super_refactor_right ae2).
Proof.
  fold_unfold_tactic super_refactor_right.
Qed.

Lemma fold_unfold_super_refactor_right_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    super_refactor_right (Minus ae1 ae2) =
    Minus (super_refactor_right ae1) (super_refactor_right ae2).
Proof.
  fold_unfold_tactic super_refactor_right.
Qed.

Lemma fold_unfold_super_refactor_right_aux_Literal :
  forall (n : nat)
         (a : arithmetic_expression),
    super_refactor_right_aux (Literal n) a =
    Plus (Literal n) a.
Proof.
  fold_unfold_tactic super_refactor_right_aux.
Qed.

Lemma fold_unfold_super_refactor_right_aux_Plus :
  forall (ae1 ae2 a : arithmetic_expression),
    super_refactor_right_aux (Plus ae1 ae2) a =
    super_refactor_right_aux ae1 (super_refactor_right_aux ae2 a).
Proof.
  fold_unfold_tactic super_refactor_right_aux.
Qed.

Lemma fold_unfold_super_refactor_right_aux_Minus :
  forall (ae1 ae2 a : arithmetic_expression),
    super_refactor_right_aux (Minus ae1 ae2) a =
    Plus (Minus (super_refactor_right ae1) (super_refactor_right ae2)) a.
Proof.
  fold_unfold_tactic super_refactor_right_aux.
Qed.

(* ********** *)

(* \begin{NEW} *)

(* Task 1: What does super_refactor_right do?
   Capture the effect of super_refactor_right into a predicate. *)

Definition test_super_refactored_rightp (candidate : arithmetic_expression -> bool) : bool :=
  Bool.eqb (candidate (Literal 0)) true
  &&
  Bool.eqb (candidate (Plus (Literal 0) (Literal 1))) true
  &&
  Bool.eqb (candidate (Minus (Literal 0) (Literal 1))) true
  &&
  Bool.eqb
    (candidate
       (Plus
          (Plus (Literal 0) (Literal 1))
          (Literal 2)))
    false
  &&
  Bool.eqb
    (candidate
       (Plus
          (Minus (Literal 0) (Literal 1))
          (Literal 2)))
    true
  &&
  Bool.eqb
    (candidate
       (Plus
          (Literal 0)
          (Plus (Literal 1) (Literal 2))))
    true
  &&
  Bool.eqb
    (candidate
       (Plus
          (Literal 0)
          (Minus (Literal 1) (Literal 2))))
    true
  &&
  Bool.eqb
    (candidate
       (Minus
          (Plus (Literal 0) (Literal 1))
          (Literal 2)))
    true
  &&
  Bool.eqb
    (candidate
       (Minus
          (Literal 0)
          (Plus (Literal 1) (Literal 2))))
    true
  &&
  Bool.eqb
    (candidate
       (Minus
          (Plus
             (Plus (Literal 0) (Literal 1))
             (Literal 2))
          (Literal 3)))
    false
  &&
  Bool.eqb
    (candidate
       (Plus
          (Literal 0)
          (Plus
             (Plus (Literal 1) (Literal 2))
             (Literal 3))))
    false
  &&
  Bool.eqb
    (candidate
       (Minus
          (Literal 0)
          (Plus
             (Plus (Literal 1) (Literal 2))
             (Literal 3))))
    false.

Fixpoint super_refactored_rightp (ae : arithmetic_expression) : bool :=
  match ae with
    Literal n =>
    true
  | Plus ae1 ae2 =>
    match ae1 with
      Literal n1 =>
      super_refactored_rightp ae2
    | Plus ae11 ae12 =>
      false
    | Minus ae11 ae12 =>
      super_refactored_rightp ae11
      &&
      super_refactored_rightp ae12
      &&
      super_refactored_rightp ae2
    end
  | Minus ae1 ae2 =>
    super_refactored_rightp ae1
    &&
    super_refactored_rightp ae2
  end.

Compute (test_super_refactored_rightp super_refactored_rightp).

Lemma fold_unfold_super_refactor_rightp_Literal :
  forall (n : nat),
    super_refactored_rightp (Literal n) =
    true.
Proof.
  fold_unfold_tactic super_refactored_rightp.
Qed.

Lemma fold_unfold_super_refactor_rightp_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    super_refactored_rightp (Plus ae1 ae2) =
    match ae1 with
      Literal n1 =>
      super_refactored_rightp ae2
    | Plus ae11 ae12 =>
      false
    | Minus ae11 ae12 =>
      super_refactored_rightp ae11
      &&
      super_refactored_rightp ae12
      &&
      super_refactored_rightp ae2
    end.
Proof.
  fold_unfold_tactic super_refactored_rightp.
Qed.

Lemma fold_unfold_super_refactor_rightp_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    super_refactored_rightp (Minus ae1 ae2) =
    super_refactored_rightp ae1
    &&
    super_refactored_rightp ae2.
Proof.
  fold_unfold_tactic super_refactored_rightp.
Qed.

Lemma super_refactor_right_yields_super_refactored_right_results_aux :
  forall (ae : arithmetic_expression),
    super_refactored_rightp (super_refactor_right ae) = true
    /\
    (forall (a : arithmetic_expression),
        super_refactored_rightp (super_refactor_right_aux ae a) =
        super_refactored_rightp a).
Proof.
  intros ae.
  induction ae as
    [ n
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    ]; split.
  - rewrite -> fold_unfold_super_refactor_right_Literal.
    rewrite -> fold_unfold_super_refactor_rightp_Literal.
    reflexivity.
  - intros a.
    rewrite -> fold_unfold_super_refactor_right_aux_Literal.
    rewrite -> fold_unfold_super_refactor_rightp_Plus.
    reflexivity.
  - rewrite -> fold_unfold_super_refactor_right_Plus.
    rewrite -> (IHae1_aux (super_refactor_right ae2)).
    exact IHae2.
  - intros a.
    rewrite -> fold_unfold_super_refactor_right_aux_Plus.
    rewrite -> (IHae1_aux (super_refactor_right_aux ae2 a)).
    exact (IHae2_aux a).
  - rewrite -> fold_unfold_super_refactor_right_Minus.
    rewrite -> fold_unfold_super_refactor_rightp_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    Search (_ && _).
    exact (andb_diag true).
  - intros a.
    rewrite -> fold_unfold_super_refactor_right_aux_Minus.
    rewrite -> fold_unfold_super_refactor_rightp_Plus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    Search (_ && _).
    rewrite -> andb_diag.
    exact (andb_true_l (super_refactored_rightp a)).
Qed.

Theorem super_refactor_right_yields_super_refactored_right_results :
  forall (ae : arithmetic_expression),
    super_refactored_rightp (super_refactor_right ae) =
    true.
Proof.
  intros ae.
  destruct (super_refactor_right_yields_super_refactored_right_results_aux ae) as [ly _].
  exact ly.
Qed.

(* ********** *)

(* A structurally recursive implementation. *)

Inductive intermediate_result : Type :=
  OK_Literal_or_Minus : intermediate_result
| OK_Plus : intermediate_result
| KO : intermediate_result.

Fixpoint super_refactor_rightp'_aux (ae : arithmetic_expression) : intermediate_result :=
  match ae with
    Literal n =>
    OK_Literal_or_Minus
  | Plus ae1 ae2 =>
    match super_refactor_rightp'_aux ae1 with
      OK_Literal_or_Minus =>
      match super_refactor_rightp'_aux ae2 with
        OK_Literal_or_Minus =>
        OK_Plus
      | OK_Plus =>
        OK_Plus
      | KO =>
        KO
      end
    | OK_Plus =>
      KO
    | KO =>
      KO
    end
  | Minus ae1 ae2 =>
    match super_refactor_rightp'_aux ae1 with
      OK_Literal_or_Minus =>
      match super_refactor_rightp'_aux ae2 with
        OK_Literal_or_Minus =>
        OK_Literal_or_Minus
      | OK_Plus =>
        OK_Literal_or_Minus
      | KO =>
        KO
      end
    | OK_Plus =>
      match super_refactor_rightp'_aux ae2 with
        OK_Literal_or_Minus =>
        OK_Literal_or_Minus
      | OK_Plus =>
        OK_Literal_or_Minus
      | KO =>
        KO
      end
    | KO =>
      KO
    end
  end.

Definition super_refactor_rightp' (ae : arithmetic_expression) : bool :=
  match super_refactor_rightp'_aux ae with
    OK_Literal_or_Minus =>
    true
  | OK_Plus =>
    true
  | KO =>
    false
  end.

Compute (test_super_refactored_rightp super_refactor_rightp').

Lemma fold_unfold_super_refactor_rightp'_aux_Literal :
  forall (n : nat),
    super_refactor_rightp'_aux (Literal n) =
    OK_Literal_or_Minus.
Proof.
  fold_unfold_tactic super_refactor_rightp'_aux.
Qed.

Lemma fold_unfold_super_refactor_rightp'_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    super_refactor_rightp'_aux (Plus ae1 ae2) =
    match super_refactor_rightp'_aux ae1 with
      OK_Literal_or_Minus =>
      match super_refactor_rightp'_aux ae2 with
        OK_Literal_or_Minus =>
        OK_Plus
      | OK_Plus =>
        OK_Plus
      | KO =>
        KO
      end
    | OK_Plus =>
      KO
    | KO =>
      KO
    end.
Proof.
  fold_unfold_tactic super_refactor_rightp'_aux.
Qed.

Lemma fold_unfold_super_refactor_rightp'_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    super_refactor_rightp'_aux (Minus ae1 ae2) =
    match super_refactor_rightp'_aux ae1 with
      OK_Literal_or_Minus =>
      match super_refactor_rightp'_aux ae2 with
        OK_Literal_or_Minus =>
        OK_Literal_or_Minus
      | OK_Plus =>
        OK_Literal_or_Minus
      | KO =>
        KO
      end
    | OK_Plus =>
      match super_refactor_rightp'_aux ae2 with
        OK_Literal_or_Minus =>
        OK_Literal_or_Minus
      | OK_Plus =>
        OK_Literal_or_Minus
      | KO =>
        KO
      end
    | KO =>
      KO
    end.
Proof.
  fold_unfold_tactic super_refactor_rightp'_aux.
Qed.

Lemma super_refactor_right_yields_super_refactored_right_results'_aux :
  forall (ae : arithmetic_expression),
    (super_refactor_rightp'_aux (super_refactor_right ae) = OK_Literal_or_Minus
     \/
     super_refactor_rightp'_aux (super_refactor_right ae) = OK_Plus)
    /\
    (forall (a : arithmetic_expression),
        super_refactor_rightp'_aux (super_refactor_right_aux ae a) =
        match super_refactor_rightp'_aux a with
          OK_Literal_or_Minus =>
          OK_Plus
        | OK_Plus =>
          OK_Plus
        | KO =>
          KO
        end).
Proof.
  intros ae.
  induction ae as
    [ n
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    ]; split.
  - left.
    rewrite -> fold_unfold_super_refactor_right_Literal.
    rewrite -> fold_unfold_super_refactor_rightp'_aux_Literal.
    reflexivity.
  - intros a.
    rewrite -> fold_unfold_super_refactor_right_aux_Literal.
    rewrite -> fold_unfold_super_refactor_rightp'_aux_Plus.
    rewrite -> fold_unfold_super_refactor_rightp'_aux_Literal.
    reflexivity.
  - right.
    rewrite -> fold_unfold_super_refactor_right_Plus.
    rewrite -> (IHae1_aux (super_refactor_right ae2)).
    destruct IHae2 as [IHae2 | IHae2];
      (rewrite -> IHae2;
       reflexivity).
  - intros a.
    rewrite -> fold_unfold_super_refactor_right_aux_Plus.
    rewrite -> (IHae1_aux (super_refactor_right_aux ae2 a)).
    rewrite -> (IHae2_aux a).
    destruct (super_refactor_rightp'_aux a);
      reflexivity.
  - left.
    rewrite -> fold_unfold_super_refactor_right_Minus.
    rewrite -> fold_unfold_super_refactor_rightp'_aux_Minus.
    destruct IHae1 as [IHae1 | IHae1], IHae2 as [IHae2 | IHae2];
      (rewrite -> IHae1;
       rewrite -> IHae2;
       reflexivity).
  - intros a.
    rewrite -> fold_unfold_super_refactor_right_aux_Minus.
    rewrite -> fold_unfold_super_refactor_rightp'_aux_Plus.
    rewrite -> fold_unfold_super_refactor_rightp'_aux_Minus.
    destruct IHae1 as [IHae1 | IHae1], IHae2 as [IHae2 | IHae2];
      (rewrite -> IHae1;
       rewrite -> IHae2;
       reflexivity).
Qed.

Theorem super_refactor_right_yields_super_refactored_right_results' :
  forall (ae : arithmetic_expression),
    super_refactor_rightp' (super_refactor_right ae) =
    true.
Proof.
  intros ae.
  unfold super_refactor_rightp'.
  destruct (super_refactor_right_yields_super_refactored_right_results'_aux ae) as [[H_ae | H_ae] _];
    (rewrite -> H_ae;
     reflexivity).
Qed.

(* ********** *)

(* A typeful take: characterizing refactored expressions with a type. *)

Inductive arithmetic_expression_right : Type :=
  Literal_right : nat -> arithmetic_expression_right
| Plus_right_Literal : nat -> arithmetic_expression_right -> arithmetic_expression_right
| Plus_right_Minus : arithmetic_expression_right * arithmetic_expression_right -> arithmetic_expression_right -> arithmetic_expression_right
| Minus_right : arithmetic_expression_right -> arithmetic_expression_right -> arithmetic_expression_right.

Fixpoint ae_from_aer (aer : arithmetic_expression_right) : arithmetic_expression :=
  match aer with
    Literal_right n =>
    Literal n
  | Plus_right_Literal n1 aer2 =>
    Plus (Literal n1) (ae_from_aer aer2)
  | Plus_right_Minus (aer11, aer12) aer2 =>
    Plus
      (Minus (ae_from_aer aer11) (ae_from_aer aer12))
      (ae_from_aer aer2)
  | Minus_right aer1 aer2 =>
    Minus
      (ae_from_aer aer1)
      (ae_from_aer aer2)
  end.

Lemma fold_unfold_ae_from_aer_Literal_right :
  forall (n : nat),
    ae_from_aer (Literal_right n) =
    Literal n.
Proof.
  fold_unfold_tactic ae_from_aer.
Qed.

Lemma fold_unfold_ae_from_aer_Plus_right_Literal :
  forall (n1 : nat)
         (aer2 : arithmetic_expression_right),
    ae_from_aer (Plus_right_Literal n1 aer2) =
    Plus (Literal n1) (ae_from_aer aer2).
Proof.
  fold_unfold_tactic ae_from_aer.
Qed.

Lemma fold_unfold_ae_from_aer_Plus_right_Minus :
  forall (aer11 aer12 aer2 : arithmetic_expression_right),
    ae_from_aer (Plus_right_Minus (aer11, aer12) aer2) =
    Plus
      (Minus (ae_from_aer aer11) (ae_from_aer aer12))
      (ae_from_aer aer2).
Proof.
  fold_unfold_tactic ae_from_aer.
Qed.

Lemma fold_unfold_ae_from_aer_Minus_right :
  forall (aer1 aer2 : arithmetic_expression_right),
    ae_from_aer (Minus_right aer1 aer2) =
    Minus
      (ae_from_aer aer1)
      (ae_from_aer aer2).
Proof.
  fold_unfold_tactic ae_from_aer.
Qed.

Fixpoint super_refactor_right' (ae : arithmetic_expression) : arithmetic_expression_right :=
  match ae with
    Literal n =>
    Literal_right n
  | Plus ae1 ae2 =>
    super_refactor_right'_aux ae1 (super_refactor_right' ae2)
  | Minus ae1 ae2 =>
    Minus_right (super_refactor_right' ae1) (super_refactor_right' ae2)
  end
  with super_refactor_right'_aux (ae1 : arithmetic_expression) (a : arithmetic_expression_right) : arithmetic_expression_right :=
    match ae1 with
      Literal n =>
      Plus_right_Literal n a
    | Plus ae1 ae2 =>
      super_refactor_right'_aux ae1 (super_refactor_right'_aux ae2 a)
    | Minus ae1 ae2 =>
      Plus_right_Minus (super_refactor_right' ae1, super_refactor_right' ae2) a
    end.

Lemma fold_unfold_super_refactor_right'_Literal :
  forall (n : nat),
    super_refactor_right' (Literal n) =
    Literal_right n.
Proof.
  fold_unfold_tactic super_refactor_right'.
Qed.

Lemma fold_unfold_super_refactor_right'_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    super_refactor_right' (Plus ae1 ae2) =
    super_refactor_right'_aux ae1 (super_refactor_right' ae2).
Proof.
  fold_unfold_tactic super_refactor_right'.
Qed.

Lemma fold_unfold_super_refactor_right'_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    super_refactor_right' (Minus ae1 ae2) =
    Minus_right (super_refactor_right' ae1) (super_refactor_right' ae2).
Proof.
  fold_unfold_tactic super_refactor_right'.
Qed.

Lemma fold_unfold_super_refactor_right'_aux_Literal :
  forall (n : nat)
         (a : arithmetic_expression_right),
    super_refactor_right'_aux (Literal n) a =
    Plus_right_Literal n a.
Proof.
  fold_unfold_tactic super_refactor_right'_aux.
Qed.

Lemma fold_unfold_super_refactor_right'_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : arithmetic_expression_right),
    super_refactor_right'_aux (Plus ae1 ae2) a =
    super_refactor_right'_aux ae1 (super_refactor_right'_aux ae2 a).
Proof.
  fold_unfold_tactic super_refactor_right'_aux.
Qed.

Lemma fold_unfold_super_refactor_right'_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : arithmetic_expression_right),
    super_refactor_right'_aux (Minus ae1 ae2) a =
    Plus_right_Minus (super_refactor_right' ae1, super_refactor_right' ae2) a.
Proof.
  fold_unfold_tactic super_refactor_right'_aux.
Qed.

Lemma equivalence_of_super_refactor_right_and_super_refactor_right'_aux :
  forall (ae : arithmetic_expression),
    super_refactor_right ae =
    ae_from_aer (super_refactor_right' ae)
    /\
    (forall (a : arithmetic_expression_right),
        super_refactor_right_aux ae (ae_from_aer a) =
        ae_from_aer (super_refactor_right'_aux ae a)).
Proof.
  intros ae.
  induction ae as
    [ n
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    ]; split.
  - rewrite -> fold_unfold_super_refactor_right_Literal.
    rewrite -> fold_unfold_super_refactor_right'_Literal.
    rewrite -> fold_unfold_ae_from_aer_Literal_right.
    reflexivity.
  - intros a.
    rewrite -> fold_unfold_super_refactor_right_aux_Literal.
    rewrite -> fold_unfold_super_refactor_right'_aux_Literal.
    rewrite -> fold_unfold_ae_from_aer_Plus_right_Literal.
    reflexivity.
  - rewrite -> fold_unfold_super_refactor_right_Plus.
    rewrite -> fold_unfold_super_refactor_right'_Plus.
    rewrite -> IHae2.
    rewrite -> (IHae1_aux (super_refactor_right' ae2)).
    reflexivity.
  - intros a.
    rewrite -> fold_unfold_super_refactor_right_aux_Plus.
    rewrite -> fold_unfold_super_refactor_right'_aux_Plus.
    rewrite -> (IHae2_aux a).
    rewrite -> (IHae1_aux (super_refactor_right'_aux ae2 a)).
    reflexivity.
  - rewrite -> fold_unfold_super_refactor_right_Minus.
    rewrite -> fold_unfold_super_refactor_right'_Minus.
    rewrite -> fold_unfold_ae_from_aer_Minus_right.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  - intros a.
    rewrite -> fold_unfold_super_refactor_right_aux_Minus.
    rewrite -> fold_unfold_super_refactor_right'_aux_Minus.
    rewrite -> fold_unfold_ae_from_aer_Plus_right_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
Qed.

Theorem equivalence_of_super_refactor_right_and_super_refactor_right' :
  forall (ae : arithmetic_expression),
    super_refactor_right ae =
    ae_from_aer (super_refactor_right' ae).
Proof.
  intros ae.
  destruct (equivalence_of_super_refactor_right_and_super_refactor_right'_aux ae) as [ly _].
  exact ly.
Qed.

Theorem super_refactor_right'_yields_super_refactored_right_results :
  forall (ae : arithmetic_expression),
    super_refactored_rightp (ae_from_aer (super_refactor_right' ae)) =
    true.
Proof.
  intros ae.
  rewrite <- (equivalence_of_super_refactor_right_and_super_refactor_right' ae).
  exact (super_refactor_right_yields_super_refactored_right_results ae).
Qed.

(* ********** *)

(* \end{NEW} *)

(* end of week-04_refactoring-typefully.v *)
