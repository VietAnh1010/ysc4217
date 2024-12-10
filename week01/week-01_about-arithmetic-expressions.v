(* week-01_about-arithmetic-expressions.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 12 Apr 2024 *)

(* ********** *)

(* members of the group:
   Kwangjoo Park <e0425762@u.nus.edu>
   Nguyen Viet Anh <e0851472@u.nus.edu>
   Sanjay Adhith <sanjay.adhith@u.nus.edu>
 *)

(* Three language processors for arithmetic expressions. *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List String Ascii.

(* ***** *)

Check (1 =? 2).
Check Nat.eqb.
Check (Nat.eqb 1 2).

Check (1 <=? 2).
Check Nat.leb.
Check (Nat.leb 1 2).

Check (1 <? 2).
Check Nat.ltb.
Check (Nat.ltb 1 2).

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

(* ********** *)

Lemma fold_unfold_list_append_nil :
  forall (V : Type)
         (v2s : list V),
    nil ++ v2s = v2s.
Proof.
  fold_unfold_tactic List.app.
Qed.

Lemma fold_unfold_list_append_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' v2s : list V),
    (v1 :: v1s') ++ v2s = v1 :: v1s' ++ v2s.
Proof.
  fold_unfold_tactic List.app.
Qed.

(* ********** *)

(* Arithmetic expressions: *)

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Times : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Source programs: *)

Inductive source_program : Type :=
  Source_program : arithmetic_expression -> source_program.

(* ********** *)

(* Semantics: *)

Inductive expressible_value : Type :=
  Expressible_nat : nat -> expressible_value
| Expressible_msg : string -> expressible_value.

(* ********** *)

Definition specification_of_evaluate (evaluate : arithmetic_expression -> expressible_value) :=
  (forall n : nat,
      evaluate (Literal n) = Expressible_nat n)
  /\
    ((forall (ae1 ae2 : arithmetic_expression)
             (s1 : string),
         evaluate ae1 = Expressible_msg s1 ->
         evaluate (Plus ae1 ae2) = Expressible_msg s1)
     /\
       (forall (ae1 ae2 : arithmetic_expression)
               (n1 : nat)
               (s2 : string),
           evaluate ae1 = Expressible_nat n1 ->
           evaluate ae2 = Expressible_msg s2 ->
           evaluate (Plus ae1 ae2) = Expressible_msg s2)
     /\
       (forall (ae1 ae2 : arithmetic_expression)
               (n1 n2 : nat),
           evaluate ae1 = Expressible_nat n1 ->
           evaluate ae2 = Expressible_nat n2 ->
           evaluate (Plus ae1 ae2) = Expressible_nat (n1 + n2)))
  /\
    ((forall (ae1 ae2 : arithmetic_expression)
             (s1 : string),
         evaluate ae1 = Expressible_msg s1 ->
         evaluate (Minus ae1 ae2) = Expressible_msg s1)
     /\
       (forall (ae1 ae2 : arithmetic_expression)
               (n1 : nat)
               (s2 : string),
           evaluate ae1 = Expressible_nat n1 ->
           evaluate ae2 = Expressible_msg s2 ->
           evaluate (Minus ae1 ae2) = Expressible_msg s2)
     /\
       (forall (ae1 ae2 : arithmetic_expression)
               (n1 n2 : nat),
           evaluate ae1 = Expressible_nat n1 ->
           evaluate ae2 = Expressible_nat n2 ->
           n1 <? n2 = true ->
           evaluate (Minus ae1 ae2) = Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
     /\
       (forall (ae1 ae2 : arithmetic_expression)
               (n1 n2 : nat),
           evaluate ae1 = Expressible_nat n1 ->
           evaluate ae2 = Expressible_nat n2 ->
           n1 <? n2 = false ->
           evaluate (Minus ae1 ae2) = Expressible_nat (n1 - n2)))
  /\
    ((forall (ae1 ae2 : arithmetic_expression)
             (s1 : string),
         evaluate ae1 = Expressible_msg s1 ->
         evaluate (Times ae1 ae2) = Expressible_msg s1)
     /\
       (forall (ae1 ae2 : arithmetic_expression)
               (n1 : nat)
               (s2 : string),
           evaluate ae1 = Expressible_nat n1 ->
           evaluate ae2 = Expressible_msg s2 ->
           evaluate (Times ae1 ae2) = Expressible_msg s2)
     /\
       (forall (ae1 ae2 : arithmetic_expression)
               (n1 n2 : nat),
           evaluate ae1 = Expressible_nat n1 ->
           evaluate ae2 = Expressible_nat n2 ->
           evaluate (Times ae1 ae2) = Expressible_nat (n1 * n2))).

Definition specification_of_interpret (interpret : source_program -> expressible_value) :=
  forall evaluate : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate ->
    forall ae : arithmetic_expression,
      interpret (Source_program ae) = evaluate ae.

(* Task 1:
   a. time permitting, prove that each of the definitions above specifies at most one function;
   b. implement these two functions; and
   c. verify that each of your functions satisfies its specification.
 *)

Fixpoint evaluate (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
      Expressible_nat n
  | Plus ae1 ae2 =>
      match (evaluate ae1) with
      | Expressible_msg s1 =>
          Expressible_msg s1
      | Expressible_nat n1 =>
          match (evaluate ae2) with
          | Expressible_msg s2 =>
              Expressible_msg s2
          | Expressible_nat n2 =>
              Expressible_nat (n1 + n2)
          end
      end
  | Minus ae1 ae2 =>
      match (evaluate ae1) with
      | Expressible_msg s1 =>
          Expressible_msg s1
      | Expressible_nat n1 =>
          match (evaluate ae2) with
          | Expressible_msg s2 =>
              (Expressible_msg s2)
          | Expressible_nat n2 =>
              match (n1 <? n2) with
              | true =>
                  Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              | false =>
                  Expressible_nat (n1 - n2)
              end
          end
      end
  | Times ae1 ae2 =>
      match (evaluate ae1) with
      | Expressible_msg s1 =>
          Expressible_msg s1
      | Expressible_nat n1 =>
          match (evaluate ae2) with
          | Expressible_msg s2 =>
              Expressible_msg s2
          | Expressible_nat n2 =>
              Expressible_nat (n1 * n2)
          end
      end
  end.

Lemma fold_unfold_evaluate_Literal :
  forall n : nat,
    evaluate (Literal n) = Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Plus ae1 ae2) =
      match (evaluate ae1) with
      | Expressible_nat n1 =>
          match (evaluate ae2) with
          | Expressible_nat n2 =>
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
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Minus ae1 ae2) =
      match (evaluate ae1) with
      | Expressible_nat n1 =>
          match (evaluate ae2) with
          | Expressible_nat n2 =>
              match (n1 <? n2) with
              | true =>
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

Lemma fold_unfold_evaluate_Times :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Times ae1 ae2) =
      match (evaluate ae1) with
      | Expressible_nat n1 =>
          match (evaluate ae2) with
          | Expressible_nat n2 =>
              Expressible_nat (n1 * n2)
          | Expressible_msg s2 =>
              Expressible_msg s2
          end
      | Expressible_msg s1 =>
          Expressible_msg s1
      end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Definition Expressible_value_eqb (v1 v2 : expressible_value) :=
  match v1 with
  | Expressible_nat n1 => match v2 with
                          | Expressible_nat n2 => Nat.eqb n1 n2
                          | Expressible_msg s2 => false
                          end
  | Expressible_msg s1 => match v2 with
                          | Expressible_nat n2 => false
                          | Expressible_msg s2 => String.eqb s1 s2
                          end
  end.

Definition test_evaluate (candidate : arithmetic_expression -> expressible_value) :=
  (Expressible_value_eqb
     (evaluate (Literal 3))
     (Expressible_nat 3))
  &&
    (Expressible_value_eqb
       (evaluate (Literal 0))
       (Expressible_nat 0))
  &&
    (Expressible_value_eqb
       (evaluate (Plus (Literal 12) (Literal 3)))
       (Expressible_nat 15))
  &&
    (Expressible_value_eqb
       (evaluate (Plus (Literal 0) (Literal 4)))
       (Expressible_nat 4))
  &&
    (Expressible_value_eqb
       (evaluate (Minus (Literal 12) (Literal 3)))
       (Expressible_nat 9))
  &&
    (Expressible_value_eqb
       (evaluate (Minus (Literal 1) (Literal 2)))
       (Expressible_msg (String.append "numerical underflow: -" (string_of_nat 1))))
  &&
    (Expressible_value_eqb
       (evaluate (Minus (Literal 29) (Literal 17)))
       (Expressible_nat 12))
  &&
    (Expressible_value_eqb
       (evaluate (Minus (Literal 34) (Literal 48)))
       (Expressible_msg ((String.append "numerical underflow: -" (string_of_nat 14)))))
  &&
    (Expressible_value_eqb
       (evaluate (Minus (Literal 3) (Literal 3)))
       (Expressible_nat 0))
  &&
    (Expressible_value_eqb
       (evaluate (Minus (Literal 0) (Literal 3)))
       (Expressible_msg ((String.append "numerical underflow: -" (string_of_nat 3))))).

Compute test_evaluate evaluate.

Theorem evaluate_satisfies_the_specification_of_evaluate :
  specification_of_evaluate evaluate.
Proof.
  unfold specification_of_evaluate.
  split.
  { intros n.
    rewrite -> fold_unfold_evaluate_Literal.
    reflexivity. }
  split.
  { (* This is for Plus *)
    split.
    { intros ae1 ae2 s1 H_s1.
      rewrite -> fold_unfold_evaluate_Plus.
      rewrite -> H_s1.
      reflexivity. }

    split.
    { intros ae1 ae2 n1 s2 H_n1 H_s2.
      rewrite -> fold_unfold_evaluate_Plus.
      rewrite -> H_n1.
      rewrite -> H_s2.
      reflexivity. }

    { intros ae1 ae2 n1 n2 H_n1 H_n2.
      rewrite -> fold_unfold_evaluate_Plus.
      rewrite -> H_n1.
      rewrite -> H_n2.
      reflexivity. }
  }
  split.
  { (* This is for Minus *)
    split.
    { intros ae1 ae2 s1 H_s1.
      rewrite -> fold_unfold_evaluate_Minus.
      rewrite -> H_s1.
      reflexivity. }

    split.
    { intros ae1 ae2 n1 s1 H_n1 H_s2.
      rewrite -> fold_unfold_evaluate_Minus.
      rewrite -> H_n1.
      rewrite -> H_s2.
      reflexivity. }

    split.
    { intros ae1 ae2 n1 n2 H_ae1 H_ae2 H_n1_lte_n2.
      rewrite -> fold_unfold_evaluate_Minus.
      rewrite -> H_ae1.
      rewrite -> H_ae2.
      rewrite -> H_n1_lte_n2.
      reflexivity. }

    { intros ae1 ae2 n1 n2 H_ae1 H_ae2 H_n1_gte_n2.
      rewrite -> fold_unfold_evaluate_Minus.
      rewrite -> H_ae1.
      rewrite -> H_ae2.
      rewrite -> H_n1_gte_n2.
      reflexivity. }
  }
  { (* This is for Times *)
    split.
    { intros ae1 ae2 s1 H_s1.
      rewrite -> fold_unfold_evaluate_Times.
      rewrite -> H_s1.
      reflexivity. }

    split.
    { intros ae1 ae2 n1 s2 H_n1 H_s2.
      rewrite -> fold_unfold_evaluate_Times.
      rewrite -> H_n1.
      rewrite -> H_s2.
      reflexivity. }

    { intros ae1 ae2 n1 n2 H_n1 H_n2.
      rewrite -> fold_unfold_evaluate_Times.
      rewrite -> H_n1.
      rewrite -> H_n2.
      reflexivity. }
  }
Qed.

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

Proposition Plus_is_commutative :
  forall ae1 ae2 : arithmetic_expression,
    evaluate (Plus ae1 ae2) = evaluate (Plus ae2 ae1).
Proof.
  intros ae1 ae2.
  rewrite ->2 fold_unfold_evaluate_Plus.
  destruct (evaluate ae1) as [n1 | s1].
  - destruct (evaluate ae2) as [n2 | s2].
    + Search (_ + _ = _ + _).
      rewrite -> Nat.add_comm.
      reflexivity.
    + reflexivity.
  - destruct (evaluate ae2) as [n2 | s2].
    + reflexivity.
    + (* cannot be proved *)
Abort.

Compute evaluate (Plus
                    (Minus (Literal 1) (Literal 5))
                    (Minus (Literal 2) (Literal 4))).
Compute evaluate (Plus
                    (Minus (Literal 2) (Literal 4))
                    (Minus (Literal 1) (Literal 5))).

Proposition Plus_is_not_commutative :
  exists ae1 ae2 : arithmetic_expression,
    evaluate (Plus ae1 ae2) <>
      evaluate (Plus ae2 ae1).

Proof.
  exists (Minus (Literal 1) (Literal 5)).
  exists (Minus (Literal 2) (Literal 5)).
  compute.
  intros H_absurd.
  discriminate H_absurd.
Qed.

Proposition Plus_is_commutative_conditionally :
  forall (ae1 ae2 : arithmetic_expression),
    (exists n1 : nat, evaluate ae1 = Expressible_nat n1)
    \/ (exists n2 : nat, evaluate ae2 = Expressible_nat n2)
    \/ (exists s : string,
           evaluate ae1 = Expressible_msg s
           /\ evaluate ae2 = Expressible_msg s) ->
    evaluate (Plus ae1 ae2) = evaluate (Plus ae2 ae1).
Proof.
  intros ae1 ae2 H.
  rewrite ->2 fold_unfold_evaluate_Plus.
  destruct (evaluate ae1) as [n1 | s1].
  - destruct (evaluate ae2) as [n2 | s2].
    + rewrite -> Nat.add_comm.
      reflexivity.
    + reflexivity.
  - destruct (evaluate ae2) as [n2 | s2].
    + reflexivity.
    + destruct H as [[n1 H1] | [[n2 H2] | [s H3]]].
      { discriminate H1. }
      { discriminate H2. }
      { destruct H3 as [Hs1 Hs2].
        rewrite -> Hs1.
        rewrite -> Hs2.
        reflexivity. }
Qed.

Proposition when_Plus_is_commutative :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Plus ae1 ae2) = evaluate (Plus ae2 ae1) ->
    (exists n1 : nat, evaluate ae1 = Expressible_nat n1)
    \/ (exists n2 : nat, evaluate ae2 = Expressible_nat n2)
    \/ (exists s : string,
           evaluate ae1 = Expressible_msg s
           /\ evaluate ae2 = Expressible_msg s).
Proof.
  intros ae1 ae2 H.
  rewrite ->2 fold_unfold_evaluate_Plus in H.
  destruct (evaluate ae1) as [n1 | s1].
  - left.
    exists n1.
    reflexivity.
  - destruct (evaluate ae2) as [n2 | s2].
    + right. left.
      exists n2.
      reflexivity.
    + right. right.
      exists s2.
      split; [exact H | reflexivity].
Qed.

Proposition equivalence_about_Plus_is_commutative :
  forall (ae1 ae2 : arithmetic_expression),
    (exists n1 : nat, evaluate ae1 = Expressible_nat n1)
    \/ (exists n2 : nat, evaluate ae2 = Expressible_nat n2)
    \/ (exists s : string,
           evaluate ae1 = Expressible_msg s
           /\ evaluate ae2 = Expressible_msg s) <->
      evaluate (Plus ae1 ae2) = evaluate (Plus ae2 ae1).
Proof.
  intros ae1 ae2.
  split.
  - exact (Plus_is_commutative_conditionally ae1 ae2).
  - exact (when_Plus_is_commutative ae1 ae2).
Qed.

(* Same structure as Plus *)
Proposition Times_is_not_commutative :
  exists ae1 ae2 : arithmetic_expression,
    evaluate (Times ae1 ae2) <>
      evaluate (Times ae2 ae1).
Proof.
  exists (Minus (Literal 1) (Literal 5)).
  exists (Minus (Literal 2) (Literal 5)).
  compute.
  intro H_absurd.
  discriminate H_absurd.
Qed.

Proposition Times_is_commutative_conditionally :
  forall (ae1 ae2 : arithmetic_expression),
    (exists n1 : nat, evaluate ae1 = Expressible_nat n1)
    \/ (exists n2 : nat, evaluate ae2 = Expressible_nat n2)
    \/ (exists s : string,
           evaluate ae1 = Expressible_msg s
           /\ evaluate ae2 = Expressible_msg s) ->
    evaluate (Times ae1 ae2) = evaluate (Times ae2 ae1).
Proof.
  intros ae1 ae2 H.
  rewrite ->2 fold_unfold_evaluate_Times.
  destruct (evaluate ae1) as [n1 | s1].
  - destruct (evaluate ae2) as [n2 | s2].
    + rewrite -> Nat.mul_comm.
      reflexivity.
    + reflexivity.
  - destruct (evaluate ae2) as [n2 | s2].
    + reflexivity.
    + destruct H as [[n1 H1] | [[n2 H2] | [s H3]]].
      { discriminate H1. }
      { discriminate H2. }
      { destruct H3 as [Hs1 Hs2].
        rewrite -> Hs1.
        rewrite -> Hs2.
        reflexivity. }
Qed.

Proposition when_Times_is_commutative :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Times ae1 ae2) = evaluate (Times ae2 ae1) ->
    (exists n1 : nat, evaluate ae1 = Expressible_nat n1)
    \/ (exists n2 : nat, evaluate ae2 = Expressible_nat n2)
    \/ (exists s : string,
           evaluate ae1 = Expressible_msg s
           /\ evaluate ae2 = Expressible_msg s).
Proof.
  intros ae1 ae2 H.
  rewrite ->2 fold_unfold_evaluate_Times in H.
  destruct (evaluate ae1) as [n1 | s1].
  - left.
    exists n1.
    reflexivity.
  - destruct (evaluate ae2) as [n2 | s2].
    + right. left.
      exists n2.
      reflexivity.
    + right. right.
      exists s2.
      split; [exact H | reflexivity].
Qed.

Proposition equivalence_about_Times_is_commutative :
  forall (ae1 ae2 : arithmetic_expression),
    (exists n1 : nat, evaluate ae1 = Expressible_nat n1)
    \/ (exists n2 : nat, evaluate ae2 = Expressible_nat n2)
    \/ (exists s : string,
           evaluate ae1 = Expressible_msg s
           /\ evaluate ae2 = Expressible_msg s) <->
      evaluate (Times ae1 ae2) = evaluate (Times ae2 ae1).
Proof.
  intros ae1 ae2.
  split.
  - exact (Times_is_commutative_conditionally ae1 ae2).
  - exact (when_Times_is_commutative ae1 ae2).
Qed.

Proposition Literal_1_is_neutral_for_Times_on_the_left :
  forall ae : arithmetic_expression,
    evaluate (Times (Literal 1) ae) = evaluate ae.
Proof.
  intros ae.
  rewrite -> fold_unfold_evaluate_Times.
  rewrite -> fold_unfold_evaluate_Literal.
  destruct (evaluate ae) as [n | s].
  Search (_ * 1 = _).
  * rewrite -> Nat.mul_1_l.
    reflexivity.
  * reflexivity.
Qed.

Proposition Literal_1_is_neutral_for_Times_on_the_right :
  forall ae : arithmetic_expression,
    evaluate (Times ae (Literal 1)) = evaluate ae.
Proof.
  intros ae.
  rewrite -> fold_unfold_evaluate_Times.
  rewrite -> fold_unfold_evaluate_Literal.
  destruct (evaluate ae) as [n | s].
  Search (_ * 1 = _).
  * rewrite -> Nat.mul_1_r.
    reflexivity.
  * reflexivity.
Qed.

Proposition Literal_0_is_absorbing_for_Times_on_the_left :
  forall ae : arithmetic_expression,
    evaluate (Times (Literal 0) ae) = evaluate (Literal 0).
Proof.
  intros ae.
  rewrite -> fold_unfold_evaluate_Times.
  rewrite -> fold_unfold_evaluate_Literal.
  destruct (evaluate ae) as [n | s].
  - rewrite -> Nat.mul_0_l.
    reflexivity.
  - (* cannot be proven *)
Abort.

Proposition Literal_0_is_not_absorbing_for_Times_on_the_left :
  exists ae : arithmetic_expression,
    evaluate (Times (Literal 0) ae) <> evaluate (Literal 0).
Proof.
  exists (Minus (Literal 1) (Literal 2)).
  compute.
  intros H_absurd.
  discriminate H_absurd.
Qed.

Proposition equivalence_about_Literal_0_is_absorbing_for_Times_on_the_left :
  forall ae : arithmetic_expression,
    (exists n : nat, evaluate ae = Expressible_nat n) <->
      evaluate (Times (Literal 0) ae) = evaluate (Literal 0).
Proof.
  intros ae.
  rewrite -> fold_unfold_evaluate_Times.
  rewrite -> fold_unfold_evaluate_Literal.
  split.
  { intros [n H].
    rewrite -> H.
    rewrite -> Nat.mul_0_l.
    reflexivity. }
  { destruct (evaluate ae) as [n | s].
    - intros _.
      exists n.
      reflexivity.
    - intros H_absurd.
      discriminate H_absurd. }
Qed.

Proposition Literal_0_is_not_absorbing_for_Times_on_the_right :
  exists ae : arithmetic_expression,
    evaluate (Times ae (Literal 0)) <> evaluate (Literal 0).
Proof.
  exists (Minus (Literal 1) (Literal 2)).
  compute.
  intros H_absurd.
  discriminate H_absurd.
Qed.

Proposition equivalence_about_Literal_0_is_absorbing_for_Times_on_the_right :
  forall ae : arithmetic_expression,
    (exists n : nat, evaluate ae = Expressible_nat n) <->
      evaluate (Times ae (Literal 0)) = evaluate (Literal 0).
Proof.
  intros ae.
  rewrite -> fold_unfold_evaluate_Times.
  rewrite -> fold_unfold_evaluate_Literal.
  split.
  { intros [n H].
    rewrite -> H.
    rewrite -> Nat.mul_0_r.
    reflexivity. }
  { destruct (evaluate ae) as [n | s].
    - intros _.
      exists n.
      reflexivity.
    - intros H_absurd.
      discriminate H_absurd. }
Qed.

Proposition Times_is_associative :
  forall ae1 ae2 ae3 : arithmetic_expression,
    evaluate (Times (Times ae1 ae2) ae3) =
      evaluate (Times ae1 (Times ae2 ae3)).
Proof.
  intros ae1 ae2 ae3.
  rewrite ->4 fold_unfold_evaluate_Times.
  destruct (evaluate ae1) as [n1 | s1].
  - destruct (evaluate ae2) as [n2 | s2].
    + destruct (evaluate ae3) as [n3 | s3].
      * rewrite <- Nat.mul_assoc.
        reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Compute (evaluate
           (Times
              (Minus (Literal 0) (Literal 1))
              (Plus (Literal 4) (Literal 5)))).

Compute (evaluate
           (Plus
              (Times
                 (Minus
                    (Literal 0)
                    (Literal 1))
                 (Literal 4))
              (Times
                 (Minus
                    (Literal 0)
                    (Literal 1))
                 (Literal 5)))).

Proposition Times_distributes_over_Plus_on_the_left :
  forall ae1 ae2 ae3 : arithmetic_expression,
    evaluate (Times ae1 (Plus ae2 ae3)) =
      evaluate (Plus (Times ae1 ae2) (Times ae1 ae3)).
Proof.
  intros ae1 ae2 ae3.
  rewrite -> fold_unfold_evaluate_Times.
  rewrite ->2 fold_unfold_evaluate_Plus.
  rewrite ->2 fold_unfold_evaluate_Times.
  destruct (evaluate ae1) as [n1 | s1].
  - destruct (evaluate ae2) as [n2 | s2].
    + destruct (evaluate ae3) as [n3 | s3].
      * Search (_ * (_ + _)).
        rewrite -> Nat.mul_add_distr_l.
        reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Proposition Times_distributes_over_Plus_on_the_right :
  forall ae1 ae2 ae3 : arithmetic_expression,
    evaluate (Times (Plus ae1 ae2) ae3) =
      evaluate (Plus (Times ae1 ae3) (Times ae2 ae3)).
Proof.
  intros ae1 ae2 ae3.
  rewrite -> fold_unfold_evaluate_Times.
  rewrite ->2 fold_unfold_evaluate_Plus.
  rewrite ->2 fold_unfold_evaluate_Times.
  destruct (evaluate ae1) as [n1 | s1].
  - destruct (evaluate ae2) as [n2 | s2].
    + destruct (evaluate ae3) as [n3 | s3].
      * rewrite -> Nat.mul_add_distr_r.
        reflexivity.
      * reflexivity.
    + destruct (evaluate ae3) as [n3 | s3].
      * reflexivity.
      * (* ae1 ok, ae2 err, ae3 err.
           order of evaluation is different:
           - ae1 -> ae2 -> ae3
           - ae1 -> ae3 -> ae1 -> ae2
         *)
        admit.
  - reflexivity.
Abort.

Proposition Times_does_not_distribute_over_Plus_on_the_right :
  exists ae1 ae2 ae3 : arithmetic_expression,
    evaluate (Times (Plus ae1 ae2) ae3) <>
      evaluate (Plus (Times ae1 ae3) (Times ae2 ae3)).
Proof.
  exists (Literal 2).
  exists (Minus (Literal 1) (Literal 2)).
  exists (Minus (Literal 3) (Literal 9)).
  compute.
  intro H_absurd.
  discriminate H_absurd.
Qed.

Proposition Times_distributes_over_Plus_on_the_right_conditionally :
  forall ae1 ae2 ae3 : arithmetic_expression,
    (exists s1 : string, evaluate ae1 = Expressible_msg s1)
    \/ (exists n2 : nat, evaluate ae2 = Expressible_nat n2)
    \/ (exists n3 : nat, evaluate ae3 = Expressible_nat n3)
    \/ (exists s : string,
           evaluate ae2 = Expressible_msg s
           /\ evaluate ae3 = Expressible_msg s) ->
    evaluate (Times (Plus ae1 ae2) ae3) =
      evaluate (Plus (Times ae1 ae3) (Times ae2 ae3)).
Proof.
  intros ae1 ae2 ae3 H.
  rewrite -> fold_unfold_evaluate_Times.
  rewrite ->2 fold_unfold_evaluate_Plus.
  rewrite ->2 fold_unfold_evaluate_Times.
  destruct (evaluate ae1) as [n1 | s1].
  - destruct (evaluate ae2) as [n2 | s2].
    + destruct (evaluate ae3) as [n3 | s3].
      * rewrite -> Nat.mul_add_distr_r.
        reflexivity.
      * reflexivity.
    + destruct (evaluate ae3) as [n3 | s3].
      * reflexivity.
      * destruct H as [[s1 H1] | [[n2 H2] | [[n3 H3] | [s H4]]]].
        { discriminate H1. }
        { discriminate H2. }
        { discriminate H3. }
        { destruct H4 as [Hs2 Hs3].
          rewrite -> Hs2.
          rewrite -> Hs3.
          reflexivity. }
  - reflexivity.
Qed.

Proposition when_Times_distributes_over_Plus_on_the_right :
  forall ae1 ae2 ae3 : arithmetic_expression,
    evaluate (Times (Plus ae1 ae2) ae3) =
      evaluate (Plus (Times ae1 ae3) (Times ae2 ae3)) ->
    (exists s1 : string, evaluate ae1 = Expressible_msg s1)
    \/ (exists n2 : nat, evaluate ae2 = Expressible_nat n2)
    \/ (exists n3 : nat, evaluate ae3 = Expressible_nat n3)
    \/ (exists s : string,
           evaluate ae2 = Expressible_msg s
           /\ evaluate ae3 = Expressible_msg s).
Proof.
  intros ae1 ae2 ae3 H.
  rewrite -> fold_unfold_evaluate_Times in H.
  rewrite ->2 fold_unfold_evaluate_Plus in H.
  rewrite ->2 fold_unfold_evaluate_Times in H.
  destruct (evaluate ae1) as [n1 | s1].
  - destruct (evaluate ae2) as [n2 | s2].
    + right. left.
      exists n2.
      reflexivity.
    + destruct (evaluate ae3) as [n3 | s3].
      * right. right. left.
        exists n3.
        reflexivity.
      * right. right. right.
        exists s3.
        split; [exact H | reflexivity].
  - left.
    exists s1.
    reflexivity.
Qed.

Proposition equivalence_about_Times_distributes_over_Plus_on_the_right :
  forall ae1 ae2 ae3 : arithmetic_expression,
    (exists s1 : string, evaluate ae1 = Expressible_msg s1)
    \/ (exists n2 : nat, evaluate ae2 = Expressible_nat n2)
    \/ (exists n3 : nat, evaluate ae3 = Expressible_nat n3)
    \/ (exists s : string,
           evaluate ae2 = Expressible_msg s
           /\ evaluate ae3 = Expressible_msg s) <->
      evaluate (Times (Plus ae1 ae2) ae3) =
        evaluate (Plus (Times ae1 ae3) (Times ae2 ae3)).
Proof.
  intros ae1 ae2 ae3.
  split.
  - exact (Times_distributes_over_Plus_on_the_right_conditionally ae1 ae2 ae3).
  - exact (when_Times_distributes_over_Plus_on_the_right ae1 ae2 ae3).
Qed.

(* Not as general compared to the previous version *)
Proposition Times_distributes_over_Plus_on_the_right_conditionally_alt :
  forall ae1 ae2 ae3 : arithmetic_expression,
    (exists n2 : nat, evaluate ae2 = Expressible_nat n2)
    \/ (exists n3 : nat, evaluate ae3 = Expressible_nat n3)
    \/ (exists s : string,
           evaluate ae2 = Expressible_msg s
           /\ evaluate ae3 = Expressible_msg s) ->
    evaluate (Times (Plus ae1 ae2) ae3) =
      evaluate (Plus (Times ae1 ae3) (Times ae2 ae3)).
Admitted.

(* And this cannot be proven *)
Proposition when_Times_distributes_over_Plus_on_the_right_alt :
  forall ae1 ae2 ae3 : arithmetic_expression,
    evaluate (Times (Plus ae1 ae2) ae3) =
      evaluate (Plus (Times ae1 ae3) (Times ae2 ae3)) ->
    (exists n2 : nat, evaluate ae2 = Expressible_nat n2)
    \/ (exists n3 : nat, evaluate ae3 = Expressible_nat n3)
    \/ (exists s : string,
           evaluate ae2 = Expressible_msg s
           /\ evaluate ae3 = Expressible_msg s).
Proof.
  intros ae1 ae2 ae3 H.
  rewrite -> fold_unfold_evaluate_Times in H.
  rewrite ->2 fold_unfold_evaluate_Plus in H.
  rewrite ->2 fold_unfold_evaluate_Times in H.
  destruct (evaluate ae1) as [n1 | s1].
  - destruct (evaluate ae2) as [n2 | s2].
    + left.
      exists n2.
      reflexivity.
    + destruct (evaluate ae3) as [n3 | s3].
      * right. left.
        exists n3.
        reflexivity.
      * right. right.
        exists s3.
        split; [exact H | reflexivity].
  - destruct (evaluate ae2) as [n2 | s2].
    + left.
      exists n2.
      reflexivity.
    + destruct (evaluate ae3) as [n3 | s3].
      * right. left.
        exists n3.
        reflexivity.
      * right. right.
        exists s3.
        admit. (* cannot be proven *)
(* We need the clause `exists s1 : string, evaluate ae1 = Expressible_msg s1`
   to proof the last case.

   Without this clause, when considering the case `evaluate ae1 = Expressible_msg s1`,
   the hypothesis becomes useless to prove `Expressible_msg s2 = Expressible_msg s3`
   and we cannot proceed. *)
Abort.
