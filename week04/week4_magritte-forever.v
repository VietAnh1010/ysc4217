(* week-04_magritte-forever.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 05 Sep 2024 *)

From Coq Require Import List String.
Import ListNotations.

(*

A Magritte take on the term project

-----

Say that the target interpreter is a "Magritte" one: instead of a
data stack of natural numbers, it has a data stack of syntactic
representations of natural numbers, namely arithmetic expressions.

So instead of pushing a natural number n, it pushes the syntactic
representation of a natural number, i.e., Literal n.

And instead of popping off two natural numbers and pushing the
result of adding these two natural numbers, it pops off two
representations of natural numbers and pushes the syntactic
representation of the addition of two arithmetic expressions
using the Plus constructor.

And likewise with the Minus constructor (and no error can occur,
since no subtraction is performed; instead, the representation
of a subtraction is constructed).

1. Implement this Magritte target interpreter.

     Definition Magritte_data_stack := list arithmetic_expression.

     Fixpoint Magritte_fetch_decode_execute_loop (bcis : list byte_code_instruction) (ds : Magritte_data_stack) : Magritte_data_stack :=
       ...

     Lemma about_Magritte_fetch_decode_execute_loop :
       forall (ae : arithmetic_expression)
              (ds : Magritte_data_stack),
	 exists ae' : arithmetic_expression,
           Magritte_fetch_decode_execute_loop (compile_aux ae) ds = ae' :: ds.

     Definition Magritte_run (t : target_program) : option arithmetic_expression :=
       match t with
         Target_program bcis =>
           match Magritte_fetch_decode_execute_loop bcis nil with
             OK nil => None
           | OK (ae :: nil) => Some ae
           | OK (ae :: ae'' :: ds'') => None
           end
       end.

     Corollary about_Magritte_run :
       forall sp : source_program,
         exists ae' : arithmetic_expression,
           Magritte_run (compile ae) = Some ae'.

2. Likewise, implement a Magritte source interpreter
   so that its result is not a natural number or an error message,
   it is the syntactic representation of a natural number.

3. A commuting diagram also holds about Magritte_interpret, compile, and Magritte_run.
   State and prove the Magritte analogue of the capstone theorem.

4. What does the Magritte analogue of the capstone theorem tell us
   about the Magritte target interpreter?
*)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Lemma fold_unfold_app_nil :
  forall (V : Type)
         (v2s : list V),
    nil ++ v2s = v2s.
Proof.
  fold_unfold_tactic app.
Qed.

Lemma fold_unfold_app_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' v2s : list V),
    (v1 :: v1s') ++ v2s = v1 :: v1s' ++ v2s.
Proof.
  fold_unfold_tactic List.app.
Qed.

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

Inductive source_program : Type :=
  Source_program : arithmetic_expression -> source_program.

(* ********** *)

(* Abstract syntax of target programs: *)

Inductive byte_code_instruction : Type :=
  PUSH : nat -> byte_code_instruction
| ADD : byte_code_instruction
| SUB : byte_code_instruction.

Inductive target_program : Type :=
  Target_program : list byte_code_instruction -> target_program.

(* ********** *)

(* The Magritte interpreter *)

Fixpoint Magritte_evaluate_ltr (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
    Literal n =>
    Literal n
  | Plus ae1 ae2 =>
    Plus (Magritte_evaluate_ltr ae1) (Magritte_evaluate_ltr ae2)
  | Minus ae1 ae2 =>
    Minus (Magritte_evaluate_ltr ae1) (Magritte_evaluate_ltr ae2)
  end.

Lemma fold_unfold_Magritte_evaluate_ltr_Literal :
  forall (n : nat),
    Magritte_evaluate_ltr (Literal n) =
    Literal n.
Proof.
  fold_unfold_tactic Magritte_evaluate_ltr.
Qed.

Lemma fold_unfold_Magritte_evaluate_ltr_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    Magritte_evaluate_ltr (Plus ae1 ae2) =
    Plus (Magritte_evaluate_ltr ae1) (Magritte_evaluate_ltr ae2).
Proof.
  fold_unfold_tactic Magritte_evaluate_ltr.
Qed.

Lemma fold_unfold_Magritte_evaluate_ltr_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    Magritte_evaluate_ltr (Minus ae1 ae2) =
    Minus (Magritte_evaluate_ltr ae1) (Magritte_evaluate_ltr ae2).
Proof.
  fold_unfold_tactic Magritte_evaluate_ltr.
Qed.

Definition Magritte_source_expressible_value : Type :=
  source_program.

Definition Magritte_interpret_ltr (sp : source_program) : Magritte_source_expressible_value :=
  match sp with
    Source_program ae =>
    Source_program (Magritte_evaluate_ltr ae)
  end.

(* ********** *)

(* The compiler: *)

Fixpoint compile_ltr_aux (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
    Literal n =>
    PUSH n :: nil
  | Plus ae1 ae2 =>
    compile_ltr_aux ae1 ++ compile_ltr_aux ae2 ++ ADD :: nil
  | Minus ae1 ae2 =>
    compile_ltr_aux ae1 ++ compile_ltr_aux ae2 ++ SUB :: nil
  end.

Lemma fold_unfold_compile_ltr_aux_Literal :
  forall (n : nat),
    compile_ltr_aux (Literal n) =
    PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_ltr_aux.
Qed.

Lemma fold_unfold_compile_ltr_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_ltr_aux (Plus ae1 ae2) =
    compile_ltr_aux ae1 ++ compile_ltr_aux ae2 ++ ADD :: nil.
Proof.
  fold_unfold_tactic compile_ltr_aux.
Qed.

Lemma fold_unfold_compile_ltr_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_ltr_aux (Minus ae1 ae2) =
    compile_ltr_aux ae1 ++ compile_ltr_aux ae2 ++ SUB :: nil.
Proof.
  fold_unfold_tactic compile_ltr_aux.
Qed.

Definition compile_ltr (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_ltr_aux ae)
  end.

(* ********** *)

(* The Magritte virtual machine (decompiler): *)

Definition Magritte_data_stack : Type :=
  list arithmetic_expression.

Definition Magritte_result_of_decoding_and_execution : Type :=
  option Magritte_data_stack.

Definition Magritte_decode_execute_ltr (bci : byte_code_instruction) (ds : Magritte_data_stack) : Magritte_result_of_decoding_and_execution :=
  match bci with
    PUSH n =>
    Some (Literal n :: ds)
  | ADD =>
    match ds with
      nil =>
      None
    | ae2 :: nil =>
      None
    | ae2 :: ae1 :: ds'' =>
      Some (Plus ae1 ae2 :: ds'')
    end
  | SUB =>
    match ds with
      nil =>
      None
    | ae2 :: nil =>
      None
    | ae2 :: ae1 :: ds'' =>
      Some (Minus ae1 ae2 :: ds'')
    end
  end.

Fixpoint Magritte_fetch_decode_execute_loop_ltr (bcis : list byte_code_instruction) (ds : Magritte_data_stack) : Magritte_result_of_decoding_and_execution :=
  match bcis with
    nil =>
    Some ds
  | bci :: bcis' =>
    match Magritte_decode_execute_ltr bci ds with
      Some ds' =>
      Magritte_fetch_decode_execute_loop_ltr bcis' ds'
    | None =>
      None
    end
  end.

Lemma fold_unfold_Magritte_fetch_decode_execute_loop_ltr_nil :
  forall (ds : Magritte_data_stack),
    Magritte_fetch_decode_execute_loop_ltr nil ds =
    Some ds.
Proof.
  fold_unfold_tactic Magritte_fetch_decode_execute_loop_ltr.
Qed.

Lemma fold_unfold_Magritte_fetch_decode_execute_loop_ltr_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : Magritte_data_stack),
    Magritte_fetch_decode_execute_loop_ltr (bci :: bcis') ds =
    match Magritte_decode_execute_ltr bci ds with
      Some ds' =>
      Magritte_fetch_decode_execute_loop_ltr bcis' ds'
    | None =>
      None
    end.
Proof.
  fold_unfold_tactic Magritte_fetch_decode_execute_loop_ltr.
Qed.

Definition Magritte_target_expressible_value : Type :=
  option source_program.

Definition Magritte_run_ltr (tp : target_program) : Magritte_target_expressible_value :=
  match tp with
    Target_program bcis =>
    match Magritte_fetch_decode_execute_loop_ltr bcis nil with
      Some nil =>
      None
    | Some (ae :: nil) =>
      Some (Source_program ae)
    | Some (ae :: _ :: _) =>
      None
    | None =>
      None
    end
  end.

Lemma about_Magritte_fetch_decode_execute_loop_ltr_and_app :
  forall (bcis1 bcis2 : list byte_code_instruction)
         (ds : Magritte_data_stack),
    (forall (ds' : Magritte_data_stack),
        Magritte_fetch_decode_execute_loop_ltr bcis1 ds = Some ds' ->
        Magritte_fetch_decode_execute_loop_ltr (bcis1 ++ bcis2) ds =
        Magritte_fetch_decode_execute_loop_ltr bcis2 ds')
    /\
    (Magritte_fetch_decode_execute_loop_ltr bcis1 ds = None ->
     Magritte_fetch_decode_execute_loop_ltr (bcis1 ++ bcis2) ds =
     None).
Proof.
  intros bcis1 bcis2.
  induction bcis1 as [| bci1 bcis1' IH_bcis1']; intros ds.
  - split.
    + intros ds' H_bcis1.
      rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_nil in H_bcis1.
      injection H_bcis1 as H_ds.
      rewrite -> H_ds.
      rewrite -> fold_unfold_app_nil.
      reflexivity.
    + intros H_bcis1.
      rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_nil in H_bcis1.
      discriminate H_bcis1.
  - split.
    + intros ds' H_bcis1.
      rewrite -> fold_unfold_app_cons.
      rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_cons.
      rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_cons in H_bcis1.
      destruct (Magritte_decode_execute_ltr bci1 ds) as [ds'' |].
      * destruct (IH_bcis1' ds'') as [IH_bcis1'_Some _].
        exact (IH_bcis1'_Some ds' H_bcis1).
      * discriminate H_bcis1.
    + intros H_bcis1.
      rewrite -> fold_unfold_app_cons.
      rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_cons.
      rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_cons in H_bcis1.
      destruct (Magritte_decode_execute_ltr bci1 ds) as [ds'' |].
      * destruct (IH_bcis1' ds'') as [_ IH_bcis1'_None].
        exact (IH_bcis1'_None H_bcis1).
      * reflexivity.

  Restart.

  intros bcis1 bcis2 ds.
  split.
  - intros ds'.
    revert ds.
    induction bcis1 as [| bci1 bcis1' IH_bcis1']; intros ds H_bcis1.
    + rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_nil in H_bcis1.
      injection H_bcis1 as H_ds.
      rewrite -> H_ds.
      rewrite -> fold_unfold_app_nil.
      reflexivity.
    + rewrite -> fold_unfold_app_cons.
      rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_cons.
      rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_cons in H_bcis1.
      destruct (Magritte_decode_execute_ltr bci1 ds) as [ds'' |].
      * exact (IH_bcis1' ds'' H_bcis1).
      * discriminate H_bcis1.
  - revert ds.
    induction bcis1 as [| bci1 bcis1' IH_bcis1']; intros ds H_bcis1.
    + rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_nil in H_bcis1.
      discriminate H_bcis1.
    + rewrite -> fold_unfold_app_cons.
      rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_cons.
      rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_cons in H_bcis1.
      destruct (Magritte_decode_execute_ltr bci1 ds) as [ds'' |].
      * exact (IH_bcis1' ds'' H_bcis1).
      * reflexivity.
Qed.

Lemma about_Magritte_fetch_decode_execute_loop_ltr_and_app_Some :
  forall (bcis1 bcis2 : list byte_code_instruction)
         (ds ds' : Magritte_data_stack),
    Magritte_fetch_decode_execute_loop_ltr bcis1 ds = Some ds' ->
    Magritte_fetch_decode_execute_loop_ltr (bcis1 ++ bcis2) ds =
    Magritte_fetch_decode_execute_loop_ltr bcis2 ds'.
Proof.
  intros bcis1 bcis2 ds.
  destruct (about_Magritte_fetch_decode_execute_loop_ltr_and_app bcis1 bcis2 ds) as [ly _].
  exact ly.
Qed.

Lemma about_Magritte_fetch_decode_execute_loop_ltr_and_compile_ltr_aux :
  forall (ae : arithmetic_expression)
         (ds : Magritte_data_stack),
    Magritte_fetch_decode_execute_loop_ltr (compile_ltr_aux ae) ds =
    Some (ae :: ds).
Proof.
  intros ae.
  induction ae as [n | ae1 IH_ae1 ae2 IH_ae2 | ae1 IH_ae1 ae2 IH_ae2]; intros ds.
  - rewrite -> fold_unfold_compile_ltr_aux_Literal.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_cons.
    unfold Magritte_decode_execute_ltr.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_nil.
    reflexivity.
  - rewrite -> fold_unfold_compile_ltr_aux_Plus.
    Check (about_Magritte_fetch_decode_execute_loop_ltr_and_app_Some
             (compile_ltr_aux ae1)
             (compile_ltr_aux ae2 ++ [ADD])).
    Check (about_Magritte_fetch_decode_execute_loop_ltr_and_app_Some
             (compile_ltr_aux ae1)
             (compile_ltr_aux ae2 ++ [ADD])
             ds (ae1 :: ds)
             (IH_ae1 ds)).
    rewrite -> (about_Magritte_fetch_decode_execute_loop_ltr_and_app_Some
                  (compile_ltr_aux ae1)
                  (compile_ltr_aux ae2 ++ [ADD])
                  ds (ae1 :: ds)
                  (IH_ae1 ds)).
    rewrite -> (about_Magritte_fetch_decode_execute_loop_ltr_and_app_Some
                  (compile_ltr_aux ae2)
                  [ADD]
                  (ae1 :: ds) (ae2 :: ae1 :: ds)
                  (IH_ae2 (ae1 :: ds))).
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_cons.
    unfold Magritte_decode_execute_ltr.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_nil.
    reflexivity.
  - rewrite -> fold_unfold_compile_ltr_aux_Minus.
    rewrite -> (about_Magritte_fetch_decode_execute_loop_ltr_and_app_Some
                  (compile_ltr_aux ae1)
                  (compile_ltr_aux ae2 ++ [SUB])
                  ds (ae1 :: ds)
                  (IH_ae1 ds)).
    rewrite -> (about_Magritte_fetch_decode_execute_loop_ltr_and_app_Some
                  (compile_ltr_aux ae2)
                  [SUB]
                  (ae1 :: ds) (ae2 :: ae1 :: ds)
                  (IH_ae2 (ae1 :: ds))).
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_cons.
    unfold Magritte_decode_execute_ltr.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_ltr_nil.
    reflexivity.
Qed.

Corollary about_Magritte_run_ltr :
  forall (sp : source_program),
    Magritte_run_ltr (compile_ltr sp) =
    Some sp.
Proof.
  intros [ae].
  unfold Magritte_run_ltr, compile_ltr.
  Check (about_Magritte_fetch_decode_execute_loop_ltr_and_compile_ltr_aux ae []).
  rewrite -> (about_Magritte_fetch_decode_execute_loop_ltr_and_compile_ltr_aux ae []).
  reflexivity.
Qed.

Lemma about_Magritte_evaluate_ltr :
  forall (ae : arithmetic_expression),
    Magritte_evaluate_ltr ae =
    ae.
Proof.
  intros ae.
  induction ae as [n | ae1 IH_ae1 ae2 IH_ae2 | ae1 IH_ae1 ae2 IH_ae2].
  - rewrite -> fold_unfold_Magritte_evaluate_ltr_Literal.
    reflexivity.
  - rewrite -> fold_unfold_Magritte_evaluate_ltr_Plus.
    rewrite -> IH_ae1.
    rewrite -> IH_ae2.
    reflexivity.
  - rewrite -> fold_unfold_Magritte_evaluate_ltr_Minus.
    rewrite -> IH_ae1.
    rewrite -> IH_ae2.
    reflexivity.
Qed.

Corollary about_Magritte_interpret_ltr :
  forall (sp : source_program),
    Magritte_interpret_ltr sp =
    sp.
Proof.
  intros [ae].
  unfold Magritte_interpret_ltr.
  apply (f_equal (fun z => Source_program z)).
  exact (about_Magritte_evaluate_ltr ae).
Qed.

Theorem the_Magritte_commuting_diagram :
  forall (sp : source_program),
    Magritte_run_ltr (compile_ltr sp) =
    Some (Magritte_interpret_ltr sp).
Proof.
  intros sp.
  rewrite -> (about_Magritte_run_ltr sp).
  rewrite -> (about_Magritte_interpret_ltr sp).
  reflexivity.
Qed.

(* end of week-04_magritte-forever.v *)
