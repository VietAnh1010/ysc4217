(* week2_refactoring.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 22 Aug 2024 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List String Ascii.

(* caution: only use natural numbers up to 5000 -- caveat emptor *)
Definition string_of_nat (q0 : nat) : string :=
  let s0 := String (ascii_of_nat (48 + (q0 mod 10))) EmptyString
  in if q0 <? 10
     then s0
     else let q1 := q0 / 10
          in let s1 := String (ascii_of_nat (48 + (q1 mod 10))) s0
             in if q1 <? 10
                then s1
                else let q2 := q1 / 10
                     in let s2 := String (ascii_of_nat (48 + (q2 mod 10))) s1
                        in if q2 <? 10
                           then s2
                           else let q3 := q2 / 10
                                in let s2 := String (ascii_of_nat (48 + (q3 mod 10))) s2
                                   in if q3 <? 10
                                      then s2
                                      else "00000".

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

Inductive expressible_value : Type :=
  Expressible_nat : nat -> expressible_value
| Expressible_msg : string -> expressible_value.

Fixpoint evaluate (ae : arithmetic_expression) : expressible_value :=
  match ae with
    Literal n =>
    Expressible_nat n
  | Plus ae1 ae2 =>
    match evaluate ae1 with
      Expressible_nat n1 =>
      match evaluate ae2 with
        Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end
  | Minus ae1 ae2 =>
    match evaluate ae1 with
      Expressible_nat n1 =>
      match evaluate ae2 with
        Expressible_nat n2 =>
        match n1 <? n2 with
          true =>
          Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
        | false =>
          Expressible_nat (n1 - n2)
        end
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end
  end.

Lemma fold_unfold_evaluate_Literal :
  forall n : nat,
    evaluate (Literal n) = Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Plus :
  forall ae1 ae2 : arithmetic_expression,
    evaluate (Plus ae1 ae2) =
    match evaluate ae1 with
      Expressible_nat n1 =>
      match evaluate ae2 with
        Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Minus :
  forall ae1 ae2 : arithmetic_expression,
    evaluate (Minus ae1 ae2) =
    match evaluate ae1 with
      Expressible_nat n1 =>
      match evaluate ae2 with
        Expressible_nat n2 =>
        match n1 <? n2 with
          true =>
          Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
        | false =>
          Expressible_nat (n1 - n2)
        end
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

(* ********** *)

Fixpoint refactor_aux (ae a : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
    Plus (Literal n) a
  | Plus ae1 ae2 =>
    refactor_aux ae1 (refactor_aux ae2 a)
  | Minus ae1 ae2 =>
    Plus (Minus (refactor_aux ae1 (Literal 0)) (refactor_aux ae2 (Literal 0))) a
  end.

Lemma fold_unfold_refactor_aux_Literal :
  forall (n : nat)
         (a : arithmetic_expression),
    refactor_aux (Literal n) a =
    Plus (Literal n) a.
Proof.
  fold_unfold_tactic refactor_aux.
Qed.

Lemma fold_unfold_refactor_aux_Plus :
  forall ae1 ae2 a : arithmetic_expression,
    refactor_aux (Plus ae1 ae2) a =
    refactor_aux ae1 (refactor_aux ae2 a).
Proof.
  fold_unfold_tactic refactor_aux.
Qed.

Lemma fold_unfold_refactor_aux_Minus :
  forall ae1 ae2 a : arithmetic_expression,
    refactor_aux (Minus ae1 ae2) a =
    Plus (Minus (refactor_aux ae1 (Literal 0)) (refactor_aux ae2 (Literal 0))) a.
Proof.
  fold_unfold_tactic refactor_aux.
Qed.

Definition refactor (ae : arithmetic_expression) : arithmetic_expression :=
  refactor_aux ae (Literal 0).

(* Task 1: What does refactor do?
   It's linearize addtions. Any tree is flatten to a very skewed tree
   (basically a list).

   Why do we want this? Because skewed tree (basically a list) is very
   efficient for computation.

   Consider the tree ((1 + 2) + (3 + 4)):
   -> Push 1, Push 2, Add, Push 3, Push 4, Add, Add
   -> maximum 3 elements on the stask

   Whereas (1 + (2 + (3 + 4))):
   -> Push 3, Push 4, Add, Push 2, Add, Push 1, Add
   -> maximum 2 elements on the stack
   -> no "deffered" addition

   => We save space! And in a sense this is similar to tail-recursion
   vs naive recursion, whereas for tail-recursion there is no deffered
   operation and therefore we can do the computation in just constant
   space.

   Capture your observations into a unit-test function. *)

Fixpoint arithmetic_expression_eqb (ae1 ae2 : arithmetic_expression) : bool :=
  match ae1 with
  | Literal n1 =>
    match ae2 with
    | Literal n2 =>
      Nat.eqb n1 n2
    | _ =>
      false
    end
  | Plus ae11 ae12 =>
    match ae2 with
    | Plus ae21 ae22 =>
      (arithmetic_expression_eqb ae11 ae21) && (arithmetic_expression_eqb ae12 ae22)
    | _ =>
      false
    end
  | Minus ae11 ae12 =>
    match ae2 with
    | Minus ae21 ae22 =>
      (arithmetic_expression_eqb ae11 ae21) && (arithmetic_expression_eqb ae12 ae22)
    | _ =>
      false
    end
  end.

Compute (refactor (Literal 1)).
Compute (refactor
           (Plus
              (Literal 1)
              (Literal 2))).
Compute (refactor
           (Plus
              (Plus
                 (Literal 1)
                 (Literal 2))
              (Plus
                 (Literal 3)
                 (Literal 4)))).

(*
      Plus
      /  \
   Plus   Plus
   /  \   /  \
   3  4   1  2

   Plus
   /  \
   3  Plus
      /  \
      4  Plus
         /  \
         1  Plus
            /  \
            2  0

How about the minus?
Here we use "-" and "+" as Minus and Plus constructors respectively.

                  -
               /     \
              +       +
             / \     / \
            +   2   3   +
           / \         / \
          1   5       6   7

===> be refactored into

                     +
                    / \
                 -     0
              /      \
             +        +
            / \      / \
           1   +    3   +
              / \      / \
             5   +    6   +
                / \      / \
               2   0    7   0
 *)

Definition test_refactor (candidate : arithmetic_expression -> arithmetic_expression) : bool :=
  (let input := (Plus
                   (Plus
                      (Literal 3)
                      (Literal 4))
                   (Plus
                      (Literal 1)
                      (Literal 2))) in
   let expected := (Plus
                      (Literal 3)
                      (Plus
                         (Literal 4)
                         (Plus
                            (Literal 1)
                            (Plus
                               (Literal 2)
                               (Literal 0))))) in
   arithmetic_expression_eqb (candidate input) expected)
  &&
  (let input := (Minus
                   (Plus
                      (Plus
                         (Literal 1)
                         (Literal 5))
                      (Literal 2))
                   (Plus
                      (Literal 3)
                      (Plus
                         (Literal 6)
                         (Literal 7)))) in
   let expected := (Plus
                      (Minus
                         (Plus
                            (Literal 1)
                            (Plus
                               (Literal 5)
                               (Plus
                                  (Literal 2)
                                  (Literal 0))))
                         (Plus
                            (Literal 3)
                            (Plus
                               (Literal 6)
                               (Plus
                                  (Literal 7)
                                  (Literal 0)))))
                      (Literal 0)) in
   arithmetic_expression_eqb (candidate input) expected)
  &&
  (arithmetic_expression_eqb
     (candidate (Literal 1))
     (Plus (Literal 1) (Literal 0)))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Literal 1)
           (Literal 2)))
     (Plus
        (Literal 1)
        (Plus
           (Literal 2)
           (Literal 0))))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Plus
              (Literal 1)
              (Literal 2))
           (Plus
              (Literal 3)
              (Literal 4))))
     (Plus
        (Literal 1)
        (Plus
           (Literal 2)
           (Plus
              (Literal 3)
              (Plus
                 (Literal 4)
                 (Literal 0))))))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Minus
           (Plus
              (Literal 1)
              (Literal 2))
           (Plus
              (Literal 3)
              (Literal 4))))
     (Plus
        (Minus
           (Plus
              (Literal 1)
              (Plus
                 (Literal 2)
                 (Literal 0)))
           (Plus
              (Literal 3)
              (Plus
                 (Literal 4)
                 (Literal 0))))
        (Literal 0))).

Compute (test_refactor refactor).

(* ********** *)

(* Task 2: Prove that refactoring preserves evaluation. *)

Proposition Literal_0_is_neutral_for_Plus_on_the_left :
  forall ae : arithmetic_expression,
    evaluate (Plus (Literal 0) ae) = evaluate ae.
Proof.
  intros ae.
  rewrite -> fold_unfold_evaluate_Plus.
  rewrite -> fold_unfold_evaluate_Literal.
  destruct (evaluate ae) as [n | s].
  * rewrite -> plus_O_n.
    reflexivity.
  * reflexivity.
Qed.

Proposition Literal_0_is_neutral_for_Plus_on_the_right :
  forall ae : arithmetic_expression,
    evaluate (Plus ae (Literal 0)) = evaluate ae.
Proof.
  intros ae.
  rewrite -> fold_unfold_evaluate_Plus.
  rewrite -> fold_unfold_evaluate_Literal.
  destruct (evaluate ae) as [n | s].
  * Search (_ + 0).
    rewrite <- plus_n_O.
    reflexivity.
  * reflexivity.
Qed.

Proposition Plus_is_associative :
  forall ae1 ae2 ae3 : arithmetic_expression,
    evaluate (Plus (Plus ae1 ae2) ae3) =
    evaluate (Plus ae1 (Plus ae2 ae3)).
Proof.
  intros ae1 ae2 ae3.
  rewrite ->4 fold_unfold_evaluate_Plus.
  destruct (evaluate ae1) as [n1 | s1].
  - destruct (evaluate ae2) as [n2 | s2].
    + destruct (evaluate ae3) as [n3 | s3].
      * rewrite <- Nat.add_assoc.
        reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma refactoring_preserves_evaluation_aux :
  forall (ae a : arithmetic_expression),
    evaluate (refactor_aux ae a) =
    evaluate (Plus ae a).
Proof.
  intros ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro a.
  - rewrite -> fold_unfold_refactor_aux_Literal.
    reflexivity.
  - rewrite -> fold_unfold_refactor_aux_Plus.
    rewrite -> (IHae1 (refactor_aux ae2 a)).
    rewrite ->2 fold_unfold_evaluate_Plus.
    rewrite -> (IHae2 a).
    rewrite ->2 fold_unfold_evaluate_Plus.
    case (evaluate ae1) as [n1 | s1].
    + case (evaluate ae2) as [n2 | s2].
      ++ case (evaluate a) as [na | sa].
         +++ rewrite -> Nat.add_assoc.
             reflexivity.
         +++ reflexivity.
      ++ reflexivity.
    + reflexivity.
  - rewrite -> fold_unfold_refactor_aux_Minus.
    rewrite ->2 fold_unfold_evaluate_Plus.
    rewrite ->2 fold_unfold_evaluate_Minus.
    rewrite -> (IHae1 (Literal 0)).
    rewrite -> (IHae2 (Literal 0)).
    rewrite ->2 Literal_0_is_neutral_for_Plus_on_the_right.
    reflexivity.

  Restart.

  intros ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intros a.
  - rewrite -> fold_unfold_refactor_aux_Literal.
    reflexivity.
  - rewrite -> fold_unfold_refactor_aux_Plus.
    rewrite -> (IHae1 (refactor_aux ae2 a)).
    rewrite -> fold_unfold_evaluate_Plus.
    rewrite -> (IHae2 a).
    rewrite <- fold_unfold_evaluate_Plus.
    rewrite -> Plus_is_associative.
    reflexivity.
  - rewrite -> fold_unfold_refactor_aux_Minus.
    rewrite -> fold_unfold_evaluate_Plus.
    rewrite -> fold_unfold_evaluate_Minus.
    rewrite -> (IHae1 (Literal 0)).
    rewrite -> (IHae2 (Literal 0)).
    rewrite ->2 Literal_0_is_neutral_for_Plus_on_the_right.
    rewrite <- fold_unfold_evaluate_Minus.
    rewrite <- fold_unfold_evaluate_Plus.
    reflexivity.
Qed.

Theorem refactoring_preserves_evaluation :
  forall ae : arithmetic_expression,
    evaluate ae = evaluate (refactor ae).
Proof.
  unfold refactor.
  intro ae.
  rewrite -> refactoring_preserves_evaluation_aux.
  rewrite -> Literal_0_is_neutral_for_Plus_on_the_right.
  reflexivity.
Qed.

(* ********** *)

Fixpoint super_refactor (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
    Literal n
  | Plus ae1 ae2 =>
    super_refactor_aux ae1 (super_refactor ae2)
  | Minus ae1 ae2 =>
    Minus (super_refactor ae1) (super_refactor ae2)
  end
  with super_refactor_aux (ae1 a : arithmetic_expression) : arithmetic_expression :=
    match ae1 with
    | Literal n =>
      Plus (Literal n) a
    | Plus ae1 ae2 =>
      super_refactor_aux ae1 (super_refactor_aux ae2 a)
    | Minus ae1 ae2 =>
      Plus (Minus (super_refactor ae1) (super_refactor ae2)) a
    end.

Definition fold_unfold_super_refactor_Literal :
  forall n : nat,
    super_refactor (Literal n) = Literal n.
Proof.
  fold_unfold_tactic super_refactor.
Qed.

Definition fold_unfold_super_refactor_Plus :
  forall ae1 ae2 : arithmetic_expression,
    super_refactor (Plus ae1 ae2) =
    super_refactor_aux ae1 (super_refactor ae2).
Proof.
  fold_unfold_tactic super_refactor.
Qed.

Definition fold_unfold_super_refactor_Minus :
  forall ae1 ae2 : arithmetic_expression,
    super_refactor (Minus ae1 ae2) =
    Minus (super_refactor ae1) (super_refactor ae2).
Proof.
  fold_unfold_tactic super_refactor.
Qed.

Definition fold_unfold_super_refactor_aux_Literal :
  forall (n : nat)
         (a : arithmetic_expression),
    super_refactor_aux (Literal n) a = Plus (Literal n) a.
Proof.
  fold_unfold_tactic super_refactor_aux.
Qed.

Definition fold_unfold_super_refactor_aux_Plus :
  forall ae1 ae2 a : arithmetic_expression,
    super_refactor_aux (Plus ae1 ae2) a =
    super_refactor_aux ae1 (super_refactor_aux ae2 a).
Proof.
  fold_unfold_tactic super_refactor_aux.
Qed.

Definition fold_unfold_super_refactor_aux_Minus :
  forall ae1 ae2 a : arithmetic_expression,
    super_refactor_aux (Minus ae1 ae2) a =
    Plus (Minus (super_refactor ae1) (super_refactor ae2)) a.
Proof.
  fold_unfold_tactic super_refactor_aux.
Qed.

(* Task 3: What does super_refactor do?

   Also linearize add additions, but better than `refactor` as there will
   be no redundant addition with `Literal 0`.

   Capture your observations into a unit-test function.

          Plus
         /    \
     Plus      Plus
    /    \    /    \
   3      4  1      2

   Plus
   /  \
  3    Plus
     /  \
    4    Plus
        /   \
       1     2

How about the minus?
Here we use "-" and "+" as Minus and Plus constructors respectively.

                  -
                /  \
              +      +
            /  \    / \
           +    2  3   +
         /  \         / \
       1     5       6   7

===> be super refactored into

                  -
               /     \
             +        +
            / \      / \
           1   +    3   +
              / \      / \
             5   2    6   7
 *)

Definition test_super_refactor (candidate : arithmetic_expression -> arithmetic_expression) : bool :=
  (let input := (Plus
                   (Plus
                      (Literal 3)
                      (Literal 4))
                   (Plus
                      (Literal 1)
                      (Literal 2))) in
   let expected := (Plus
                      (Literal 3)
                      (Plus
                         (Literal 4)
                         (Plus
                            (Literal 1)
                            (Literal 2)))) in
   arithmetic_expression_eqb (candidate input) expected)
  &&
  (let input := (Minus
                   (Plus
                      (Plus
                         (Literal 1)
                         (Literal 5))
                      (Literal 2))
                   (Plus
                      (Literal 3)
                      (Plus
                         (Literal 6)
                         (Literal 7)))) in
   let expected := (Minus
                      (Plus
                         (Literal 1)
                         (Plus
                            (Literal 5)
                            (Literal 2)))
                      (Plus
                         (Literal 3)
                         (Plus
                            (Literal 6)
                            (Literal 7))))in
   arithmetic_expression_eqb (candidate input) expected)
  &&
  (arithmetic_expression_eqb
     (candidate (Literal 1))
     (Literal 1))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Literal 1)
           (Literal 2)))
     (Plus
        (Literal 1)
        (Literal 2)))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Plus
              (Literal 1)
              (Literal 2))
           (Plus
              (Literal 3)
              (Literal 4))))
     (Plus
        (Literal 1)
        (Plus
           (Literal 2)
           (Plus
              (Literal 3)
              (Literal 4)))))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Minus
           (Plus
              (Literal 1)
              (Literal 2))
           (Plus
              (Literal 3)
              (Literal 4))))
     (Minus
        (Plus
           (Literal 1)
           (Literal 2))
        (Plus
           (Literal 3)
           (Literal 4)))).

Compute (test_super_refactor super_refactor).

(* Task 4: Prove that super-refactoring preserves evaluation. *)

Lemma super_refactoring_preserves_evaluation_aux :
  forall ae : arithmetic_expression,
    evaluate (super_refactor ae) = evaluate ae
    /\
    (forall a : arithmetic_expression,
        evaluate (super_refactor_aux ae a) = evaluate (Plus ae a)).
Proof.
  intros ae.
  induction ae as [n | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux] | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]].
  - split.
    -- rewrite -> fold_unfold_super_refactor_Literal.
       reflexivity.
    -- intro a.
       rewrite -> fold_unfold_super_refactor_aux_Literal.
       reflexivity.
  - split.
    -- rewrite -> fold_unfold_super_refactor_Plus.
       rewrite -> (IHae1_aux (super_refactor ae2)).
       rewrite ->2 fold_unfold_evaluate_Plus.
       rewrite -> IHae2.
       reflexivity.
    -- intro a.
       rewrite -> fold_unfold_super_refactor_aux_Plus.
       rewrite ->2 fold_unfold_evaluate_Plus.
       rewrite -> (IHae1_aux (super_refactor_aux ae2 a)).
       rewrite -> fold_unfold_evaluate_Plus.
       rewrite -> (IHae2_aux a).
       rewrite -> fold_unfold_evaluate_Plus.
       case (evaluate ae1) as [n1 | s1].
       --- case (evaluate ae2) as [n2 | s2].
           ---- case (evaluate a) as [n3 | s3].
                ----- rewrite -> Nat.add_assoc; reflexivity.
                ----- reflexivity.
           ---- reflexivity.
       --- reflexivity.
  - split.
    -- rewrite -> fold_unfold_super_refactor_Minus.
       rewrite -> fold_unfold_evaluate_Minus.
       rewrite -> IHae1.
       rewrite -> IHae2.
       rewrite -> fold_unfold_evaluate_Minus.
       reflexivity.
    -- intro a.
       rewrite -> fold_unfold_super_refactor_aux_Minus.
       rewrite -> fold_unfold_evaluate_Plus.
       rewrite -> fold_unfold_evaluate_Minus.
       rewrite -> IHae1.
       rewrite -> IHae2.
       rewrite -> fold_unfold_evaluate_Plus.
       rewrite -> fold_unfold_evaluate_Minus.
       case (evaluate ae1) as [n1 | s1].
       --- case (evaluate ae2) as [n2 | s2].
           ---- case (evaluate a) as [n3 | s3].
                ----- case (n1 <? n2); reflexivity.
                ----- reflexivity.
           ---- reflexivity.
       --- reflexivity.

  Restart.

  intros ae.
  induction ae as [n | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux] | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]]; split.
  - rewrite -> fold_unfold_super_refactor_Literal.
    reflexivity.
  - intros a.
    rewrite -> fold_unfold_super_refactor_aux_Literal.
    reflexivity.
  - rewrite -> fold_unfold_super_refactor_Plus.
    rewrite -> (IHae1_aux (super_refactor ae2)).
    rewrite -> fold_unfold_evaluate_Plus.
    rewrite -> IHae2.
    rewrite <- fold_unfold_evaluate_Plus.
    reflexivity.
  - intros a.
    rewrite -> fold_unfold_super_refactor_aux_Plus.
    rewrite -> (IHae1_aux (super_refactor_aux ae2 a)).
    rewrite -> fold_unfold_evaluate_Plus.
    rewrite -> (IHae2_aux a).
    rewrite <- fold_unfold_evaluate_Plus.
    rewrite -> Plus_is_associative.
    reflexivity.
  - rewrite -> fold_unfold_super_refactor_Minus.
    rewrite -> fold_unfold_evaluate_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    rewrite <- fold_unfold_evaluate_Minus.
    reflexivity.
  - intros a.
    rewrite -> fold_unfold_super_refactor_aux_Minus.
    rewrite -> fold_unfold_evaluate_Plus.
    rewrite -> fold_unfold_evaluate_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    rewrite <- fold_unfold_evaluate_Minus.
    rewrite <- fold_unfold_evaluate_Plus.
    reflexivity.
Qed.

Theorem super_refactoring_preserves_evaluation :
  forall ae : arithmetic_expression,
    evaluate ae = evaluate (super_refactor ae).
Proof.
  intros ae.
  destruct (super_refactoring_preserves_evaluation_aux ae) as [ly _].
  symmetry.
  exact ly.
Qed.

(* ********** *)

(* Extra tasks *)

Proposition equivalence_of_the_two_lemmas_about_refactor_aux :
  forall ae : arithmetic_expression,
    (forall s : string,
        evaluate ae = Expressible_msg s ->
        forall a : arithmetic_expression,
          evaluate (refactor_aux ae a) = Expressible_msg s)
    /\
    (forall (n : nat)
            (s : string),
        evaluate ae = Expressible_nat n ->
        forall a : arithmetic_expression,
          evaluate a = Expressible_msg s ->
          evaluate (refactor_aux ae a) = Expressible_msg s)
    /\
    (forall n1 n2 : nat,
        evaluate ae = Expressible_nat n1 ->
        forall a : arithmetic_expression,
          evaluate a = Expressible_nat n2 ->
          evaluate (refactor_aux ae a) = Expressible_nat (n1 + n2))
    <->
    (forall a : arithmetic_expression,
        evaluate (refactor_aux ae a) = evaluate (Plus ae a)).
Proof.
  intros ae.
  split.
  { intros [H_s1 [H_n1_s2 H_n1_n2]] a.
    rewrite -> fold_unfold_evaluate_Plus.
    destruct (evaluate ae) as [n1 | s1].
    - destruct (evaluate a) as [n2 | s2] eqn:H_a.
      + exact (H_n1_n2 n1 n2 eq_refl a H_a).
      + exact (H_n1_s2 n1 s2 eq_refl a H_a).
    - exact (H_s1 s1 eq_refl a). }
  { intros H.
    split.
    { intros s1 H_ae a.
      assert (ly := H a).
      rewrite -> fold_unfold_evaluate_Plus in ly.
      rewrite -> H_ae in ly.
      exact ly. }
    split.
    { intros n1 s2 H_ae a H_a.
      assert (ly := H a).
      rewrite -> fold_unfold_evaluate_Plus in ly.
      rewrite -> H_ae in ly.
      rewrite -> H_a in ly.
      exact ly. }
    { intros n1 n2 H_ae a H_a.
      assert (ly := H a).
      rewrite -> fold_unfold_evaluate_Plus in ly.
      rewrite -> H_ae in ly.
      rewrite -> H_a in ly.
      exact ly. } }
Qed.

Proposition equivalence_of_the_two_lemmas_about_super_refactor_aux :
  forall ae : arithmetic_expression,
    (forall s : string,
        evaluate ae = Expressible_msg s ->
        forall a : arithmetic_expression,
          evaluate (super_refactor_aux ae a) = Expressible_msg s)
    /\
    (forall (n : nat)
            (s : string),
        evaluate ae = Expressible_nat n ->
        forall a : arithmetic_expression,
          evaluate a = Expressible_msg s ->
          evaluate (super_refactor_aux ae a) = Expressible_msg s)
    /\
    (forall n1 n2 : nat,
        evaluate ae = Expressible_nat n1 ->
        forall a : arithmetic_expression,
          evaluate a = Expressible_nat n2 ->
          evaluate (super_refactor_aux ae a) = Expressible_nat (n1 + n2))
    <->
    (forall a : arithmetic_expression,
        evaluate (super_refactor_aux ae a) = evaluate (Plus ae a)).
Proof.
  intros ae.
  split.
  { intros [H_s1 [H_n1_s2 H_n1_n2]] a.
    rewrite -> fold_unfold_evaluate_Plus.
    destruct (evaluate ae) as [n1 | s1].
    - destruct (evaluate a) as [n2 | s2] eqn:H_a.
      + exact (H_n1_n2 n1 n2 eq_refl a H_a).
      + exact (H_n1_s2 n1 s2 eq_refl a H_a).
    - exact (H_s1 s1 eq_refl a). }
  { intros H.
    split.
    { intros s1 H_ae a.
      assert (ly := H a).
      rewrite -> fold_unfold_evaluate_Plus in ly.
      rewrite -> H_ae in ly.
      exact ly. }
    split.
    { intros n1 s2 H_ae a H_a.
      assert (ly := H a).
      rewrite -> fold_unfold_evaluate_Plus in ly.
      rewrite -> H_ae in ly.
      rewrite -> H_a in ly.
      exact ly. }
    { intros n1 n2 H_ae a H_a.
      assert (ly := H a).
      rewrite -> fold_unfold_evaluate_Plus in ly.
      rewrite -> H_ae in ly.
      rewrite -> H_a in ly.
      exact ly. } }
Qed.

Compute (refactor (refactor (Literal 0)) = refactor (Literal 0)).

Theorem refactor_is_not_idempotent :
  exists ae : arithmetic_expression,
    refactor (refactor ae) <> refactor ae.
Proof.
  exists (Literal 0).
  compute.
  intros H_absurd.
  discriminate H_absurd.
Qed.

(*
   Under no condition will refactor be idempotent.
   `refactor` will add extra 0s into the expression tree.
 *)

Compute (super_refactor (super_refactor (Literal 0)) = super_refactor (Literal 0)).
Compute (super_refactor (super_refactor (Plus (Literal 0) (Literal 1))) = super_refactor (Plus (Literal 0) (Literal 1))).
Compute (super_refactor (super_refactor (Minus (Literal 0) (Literal 1))) = super_refactor (Minus (Literal 0) (Literal 1))).

Lemma super_refactor_is_idempotent_aux :
  forall (ae : arithmetic_expression),
    (super_refactor (super_refactor ae) = super_refactor ae)
    /\
    (forall a : arithmetic_expression,
        super_refactor (super_refactor_aux ae a) =
        super_refactor_aux ae (super_refactor a)).
Proof.
  intros ae.
  induction ae as [
      n
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    ]; split.
  - rewrite ->2 fold_unfold_super_refactor_Literal.
    reflexivity.
  - intros a.
    rewrite ->2 fold_unfold_super_refactor_aux_Literal.
    rewrite -> fold_unfold_super_refactor_Plus.
    rewrite -> fold_unfold_super_refactor_aux_Literal.
    reflexivity.
  - rewrite -> fold_unfold_super_refactor_Plus.
    rewrite -> (IHae1_aux (super_refactor ae2)).
    rewrite -> IHae2.
    reflexivity.
  - intros a.
    rewrite ->2 fold_unfold_super_refactor_aux_Plus.
    rewrite -> (IHae1_aux (super_refactor_aux ae2 a)).
    rewrite -> (IHae2_aux a).
    reflexivity.
  - rewrite ->2 fold_unfold_super_refactor_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  - intros a.
    rewrite ->2 fold_unfold_super_refactor_aux_Minus.
    rewrite -> fold_unfold_super_refactor_Plus.
    rewrite -> fold_unfold_super_refactor_aux_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
Qed.

Theorem super_refactor_is_idempotent :
  forall ae : arithmetic_expression,
    super_refactor (super_refactor ae) = super_refactor ae.
Proof.
  intros ae.
  destruct (super_refactor_is_idempotent_aux ae) as [ly _].
  exact ly.
Qed.

(* ********** *)

(* Preview of Week 03 (out of scope of Week 02, but maybe some of you are Very Fast): *)

(* Design and implement a function
     simplify : arithmetic_expression -> arithmetic_expression
   that exploits the following properties:

   forall ae : arithmetic_expression, evaluate (Plus (Literal 0) ae) = evaluate ae

   forall ae : arithmetic_expression, evaluate (Plus ae (Literal 0)) = evaluate ae

   forall ae : arithmetic_expression, evaluate (Minus ae (Literal 0)) = evaluate ae

   (assuming that the last property holds -- does it?)

   So in a simplified expression,

   * there should be no occurrence of Literal 0 as a first argument of Plus,

   * there should be no occurrence of Literal 0 as a second argument of Plus, and

   * there should be no occurrence of Literal 0 as a second argument of Minus.

   Misc. questions:

   * is simplify idempotent?

   * does simplification preserve evaluation?
*)

Compute (let ae := Minus (Literal 0) (Literal 1) in
         evaluate (Minus ae (Literal 0)) = evaluate ae).

Compute (let ae := Literal 1 in
         evaluate (Minus ae (Literal 0)) = evaluate ae).

Proposition Literal_0_is_neutral_for_Minus_on_the_right :
  forall ae : arithmetic_expression,
    evaluate (Minus ae (Literal 0)) = evaluate ae.
Proof.
  intros ae.
  rewrite -> fold_unfold_evaluate_Minus.
  rewrite -> fold_unfold_evaluate_Literal.
  destruct (evaluate ae) as [n | s].
  * assert (about_n_lt_0 : n <? 0 = false).
    { Search (_ <? _).
      rewrite -> Nat.ltb_ge.
      Search (0 <= _).
      exact (Nat.le_0_l n). }
    rewrite -> about_n_lt_0.
    rewrite -> Nat.sub_0_r.
    reflexivity.
  * reflexivity.
Qed.

Definition test_simplify (candidate : arithmetic_expression -> arithmetic_expression) :=
  (arithmetic_expression_eqb
     (candidate (Literal 0))
     (Literal 0))
  &&
  (arithmetic_expression_eqb
     (candidate (Plus (Literal 0) (Literal 1)))
     (Literal 1))
  &&
  (arithmetic_expression_eqb
     (candidate (Plus (Literal 1) (Literal 0)))
     (Literal 1))
  &&
  (arithmetic_expression_eqb
     (candidate (Minus (Literal 1) (Literal 0)))
     (Literal 1))
  &&
  (arithmetic_expression_eqb
     (candidate (Minus
                   (Plus (Literal 0) (Literal 0))
                   (Minus 
                      (Literal 0)
                      (Minus (Literal 0) (Literal 0)))))
     (Literal 0))
  &&
  (arithmetic_expression_eqb
     (candidate (Plus
                   (Minus (Literal 0) (Literal 0))
                   (Plus (Literal 1) (Literal 0))))
     (Literal 1)).

Fixpoint simplify (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
    Literal n
  | Plus ae1 ae2 =>
    let ae1_simpl := simplify ae1 in
    let ae2_simpl := simplify ae2 in
    match ae1_simpl, ae2_simpl with
    | Literal 0, _ =>
      ae2_simpl
    | _, Literal 0 =>
      ae1_simpl
    | _, _ =>
      Plus ae1_simpl ae2_simpl
    end
  | Minus ae1 ae2 =>
    let ae1_simpl := simplify ae1 in
    let ae2_simpl := simplify ae2 in
    match ae2_simpl with
    | Literal 0 =>
      ae1_simpl
    | _ =>
      Minus ae1_simpl ae2_simpl
    end
  end.
(* Is there a better way to write this function? *)

Compute (test_simplify simplify).

Definition fold_unfold_simplify_Literal :
  forall n : nat,
    simplify (Literal n) = Literal n.
Proof.
  fold_unfold_tactic simplify.
Qed.

Definition fold_unfold_simplify_Plus :
  forall ae1 ae2 : arithmetic_expression,
    simplify (Plus ae1 ae2) =
    let ae1_simpl := simplify ae1 in
    let ae2_simpl := simplify ae2 in
    match ae1_simpl, ae2_simpl with
    | Literal 0, _ =>
      ae2_simpl
    | _, Literal 0 =>
      ae1_simpl
    | _, _ =>
        Plus ae1_simpl ae2_simpl
    end.
Proof.
  fold_unfold_tactic simplify.
Qed.

Definition fold_unfold_simplify_Minus :
  forall ae1 ae2 : arithmetic_expression,
    simplify (Minus ae1 ae2) =
    let ae1_simpl := simplify ae1 in
    let ae2_simpl := simplify ae2 in
    match ae2_simpl with
    | Literal 0 =>
      ae1_simpl
    | _ =>
      Minus ae1_simpl ae2_simpl
    end.
Proof.
  fold_unfold_tactic simplify.
Qed.

Lemma nat_eq_or_nat_neq :
  forall n m : nat,
    n = m \/ n <> m.
Proof.
  intros n m.
  destruct (n =? m) eqn:ly.
  - Search (_ =? _ = true).
    rewrite -> Nat.eqb_eq in ly.
    left. exact ly.
  - Search (_ =? _ = false).
    rewrite -> Nat.eqb_neq in ly.
    right. exact ly.
Qed.

Proposition simplifying_preserves_evaluation :
  forall ae : arithmetic_expression,
    evaluate (simplify ae) =
    evaluate ae.
Proof.
  intros ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  - rewrite -> fold_unfold_simplify_Literal.
    reflexivity.
  - rewrite -> fold_unfold_simplify_Plus.
    rewrite -> fold_unfold_evaluate_Plus.
    rewrite <- IHae1.
    rewrite <- IHae2.
    destruct (simplify ae1) as [n | ae11 ae12 | ae11 ae12].
    + destruct (nat_eq_or_nat_neq n 0) as [n_eq_0 | n_neq_0].
      * rewrite -> n_eq_0.
        admit.
Admitted.

(* ********** *)

(* end of week2_refactoring.v *)
