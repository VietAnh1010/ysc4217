(* term-project.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Nguyen Viet Anh <e0851472@u.nus.edu> *)
(* Adapted from Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Fri 22 Nov 2024 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List String Ascii.

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
  fold_unfold_tactic app.
Qed.

(* ********** *)

(* Abstract syntax of source programs: *)

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Name : string -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

Inductive source_program : Type :=
  Source_program : arithmetic_expression -> source_program.

(* ********** *)

(* Equality predicates: *)

Definition string_eqb (s1 s2 : string) : bool :=
  match String.string_dec s1 s2 with
    left _ =>
    true
  | right _ =>
    false
  end.

(* ********** *)

(* The abstract data type of environments: *)

Definition environment (denotable : Type) : Type :=
  list (string * denotable).

Definition mt (denotable : Type) : environment denotable :=
  nil.

Definition extend (denotable : Type) (x : string) (d : denotable) (e : environment denotable) : environment denotable :=
  (x , d) :: e.

Fixpoint lookup (denotable : Type) (x : string) (e : environment denotable) : option denotable :=
  match e with
    nil =>
    None
  | (x', d) :: e' =>
    if string_eqb x x'
    then Some d
    else lookup denotable x e'
  end.

(* ********** *)

(* The source interpreter: *)

Inductive source_msg : Type :=
  Source_undeclared_name : string -> source_msg.

Inductive source_expressible_value : Type :=
  Source_expressible_nat : nat -> source_expressible_value
| Source_expressible_msg : source_msg -> source_expressible_value.

Fixpoint evaluate_ltr (ae : arithmetic_expression) (e : environment nat) : source_expressible_value :=
  match ae with
    Literal n =>
    Source_expressible_nat n
  | Name x =>
    match lookup nat x e with
      Some n =>
      Source_expressible_nat n
    | None =>
      Source_expressible_msg (Source_undeclared_name x)
    end
  | Plus ae1 ae2 =>
    match evaluate_ltr ae1 e with
      Source_expressible_nat n1 =>
      match evaluate_ltr ae2 e with
        Source_expressible_nat n2 =>
        Source_expressible_nat (n1 + n2)
      | Source_expressible_msg s2 =>
        Source_expressible_msg s2
      end
    | Source_expressible_msg s1 =>
      Source_expressible_msg s1
    end
  end.

Definition interpret_ltr (sp : source_program) (e : environment nat) : source_expressible_value :=
  match sp with
    Source_program ae =>
    evaluate_ltr ae e
  end.

Lemma fold_unfold_evaluate_ltr_Literal :
  forall (n : nat)
         (e : environment nat),
    evaluate_ltr (Literal n) e =
    Source_expressible_nat n.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Lemma fold_unfold_evaluate_ltr_Name :
  forall (x : string)
         (e : environment nat),
    evaluate_ltr (Name x) e =
    match lookup nat x e with
      Some n =>
      Source_expressible_nat n
    | None =>
      Source_expressible_msg (Source_undeclared_name x)
    end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Lemma fold_unfold_evaluate_ltr_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (e : environment nat),
    evaluate_ltr (Plus ae1 ae2) e =
    match evaluate_ltr ae1 e with
      Source_expressible_nat n1 =>
      match evaluate_ltr ae2 e with
        Source_expressible_nat n2 =>
        Source_expressible_nat (n1 + n2)
      | Source_expressible_msg s2 =>
        Source_expressible_msg s2
      end
    | Source_expressible_msg s1 =>
      Source_expressible_msg s1
    end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

(* ********** *)

(* Abstract syntax of target programs: *)

Inductive byte_code_instruction : Type :=
  PUSH : nat -> byte_code_instruction
| LOOKUP : string -> byte_code_instruction
| ADD : byte_code_instruction.

Inductive target_program : Type :=
  Target_program : list byte_code_instruction -> target_program.

(* ********** *)

(* The compiler: *)

Fixpoint compile_ltr_aux (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
    Literal n =>
    PUSH n :: nil
  | Name x =>
    LOOKUP x :: nil
  | Plus ae1 ae2 =>
    compile_ltr_aux ae1 ++ compile_ltr_aux ae2 ++ ADD :: nil
  end.

Definition compile_ltr (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_ltr_aux ae)
  end.

Lemma fold_unfold_compile_ltr_aux_Literal :
  forall (n : nat),
    compile_ltr_aux (Literal n) =
    PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_ltr_aux.
Qed.

Lemma fold_unfold_compile_ltr_aux_Name :
  forall (x : string),
    compile_ltr_aux (Name x) =
    LOOKUP x :: nil.
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

(* ********** *)

(* The target interpreter (a.k.a. virtual machine): *)

Definition data_stack : Type :=
  list nat.

Inductive result_msg : Type :=
  Result_undeclared_name : string -> result_msg
| Result_stack_underflow : byte_code_instruction -> result_msg.

Inductive result_of_decoding_and_execution : Type :=
  OK : data_stack -> result_of_decoding_and_execution
| KO : result_msg -> result_of_decoding_and_execution.

Definition decode_execute_ltr (bci : byte_code_instruction) (e : environment nat) (ds : data_stack) : result_of_decoding_and_execution :=
  match bci with
    PUSH n =>
    OK (n :: ds)
  | LOOKUP x =>
    match lookup nat x e with
      Some n =>
      OK (n :: ds)
    | None =>
      KO (Result_undeclared_name x)
    end
  | ADD =>
    match ds with
      nil =>
      KO (Result_stack_underflow ADD)
    | n2 :: nil =>
      KO (Result_stack_underflow ADD)
    | n2 :: n1 :: ds'' =>
      OK (n1 + n2 :: ds'')
    end
  end.

Fixpoint fetch_decode_execute_loop_ltr (bcis : list byte_code_instruction) (e : environment nat) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
    nil =>
    OK ds
  | bci :: bcis' =>
    match decode_execute_ltr bci e ds with
      OK ds' =>
      fetch_decode_execute_loop_ltr bcis' e ds'
    | KO m =>
      KO m
    end
  end.

Lemma fold_unfold_fetch_decode_execute_loop_ltr_nil :
  forall (e : environment nat)
         (ds : data_stack),
    fetch_decode_execute_loop_ltr nil e ds =
    OK ds.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_ltr.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_ltr_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (e : environment nat)
         (ds : data_stack),
    fetch_decode_execute_loop_ltr (bci :: bcis') e ds =
    match decode_execute_ltr bci e ds with
      OK ds' =>
      fetch_decode_execute_loop_ltr bcis' e ds'
    | KO m =>
      KO m
    end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_ltr.
Qed.

Inductive target_msg : Type :=
  Target_undeclared_name : string -> target_msg
| Target_stack_underflow : byte_code_instruction -> target_msg
| Target_stack_O : target_msg
| Target_stack_SS : target_msg.

Inductive target_expressible_value : Type :=
  Target_expressible_nat : nat -> target_expressible_value
| Target_expressible_msg : target_msg -> target_expressible_value.

Definition run_ltr (tp : target_program) (e : environment nat) : target_expressible_value :=
  match tp with
    Target_program bcis =>
    match fetch_decode_execute_loop_ltr bcis e nil with
      OK nil =>
      Target_expressible_msg Target_stack_O
    | OK (n :: nil) =>
      Target_expressible_nat n
    | OK (n :: _ :: _) =>
      Target_expressible_msg Target_stack_SS
    | KO (Result_undeclared_name x) =>
      Target_expressible_msg (Target_undeclared_name x)
    | KO (Result_stack_underflow bci) =>
      Target_expressible_msg (Target_stack_underflow bci)
    end
  end.

(* ********** *)

Definition same_results (sev : source_expressible_value) (tev : target_expressible_value) : Prop :=
  (exists (n : nat),
      sev = Source_expressible_nat n /\
      tev = Target_expressible_nat n)
  \/
  (exists (s : string),
      sev = Source_expressible_msg (Source_undeclared_name s) /\
      tev = Target_expressible_msg (Target_undeclared_name s)).

Theorem the_commuting_diagram_ltr :
  forall (sp : source_program)
         (e : environment nat),
    same_results
      (interpret_ltr sp e)
      (run_ltr (compile_ltr sp) e).
Admitted.

(* ********** *)

(* compile_curiouser *)

Fixpoint compile_curiouser1_aux
  (ae : arithmetic_expression)
  (c : nat -> list byte_code_instruction)
  (k : list byte_code_instruction -> list byte_code_instruction) : list byte_code_instruction :=
  match ae with
    Literal n =>
    c n
  | Name x =>
    k (LOOKUP x :: nil)
  | Plus ae1 ae2 =>
    compile_curiouser1_aux ae1
      (fun n1 => compile_curiouser1_aux ae2
                   (fun n2 => c (n1 + n2))
                   (fun bcis2 => k (PUSH n1 :: bcis2 ++ ADD :: nil)))
      (fun bcis1 => compile_curiouser1_aux ae2
                      (fun n2 => k (bcis1 ++ PUSH n2 :: ADD :: nil))
                      (fun bcis2 => k (bcis1 ++ bcis2 ++ ADD :: nil)))
  end.

Lemma fold_unfold_compile_curiouser1_aux_Literal :
  forall (n : nat)
         (c : nat -> list byte_code_instruction)
         (k : list byte_code_instruction -> list byte_code_instruction),
    compile_curiouser1_aux (Literal n) c k =
    c n.
Proof.
  fold_unfold_tactic compile_curiouser1_aux.
Qed.

Lemma fold_unfold_compile_curiouser1_aux_Name :
  forall (x : string)
         (c : nat -> list byte_code_instruction)
         (k : list byte_code_instruction -> list byte_code_instruction),
    compile_curiouser1_aux (Name x) c k =
    k (LOOKUP x :: nil).
Proof.
  fold_unfold_tactic compile_curiouser1_aux.
Qed.

Lemma fold_unfold_compile_curiouser1_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (c : nat -> list byte_code_instruction)
         (k : list byte_code_instruction -> list byte_code_instruction),
    compile_curiouser1_aux (Plus ae1 ae2) c k =
    compile_curiouser1_aux ae1
      (fun n1 => compile_curiouser1_aux ae2
                   (fun n2 => c (n1 + n2))
                   (fun bcis2 => k (PUSH n1 :: bcis2 ++ ADD :: nil)))
      (fun bcis1 => compile_curiouser1_aux ae2
                      (fun n2 => k (bcis1 ++ PUSH n2 :: ADD :: nil))
                      (fun bcis2 => k (bcis1 ++ bcis2 ++ ADD :: nil))).
Proof.
  fold_unfold_tactic compile_curiouser1_aux.
Qed.

Definition compile_curiouser1 (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_curiouser1_aux ae (fun n => PUSH n :: nil) (fun bcis => bcis))
  end.

(* ********** *)

Fixpoint curiouser1_aux
  (ae : arithmetic_expression)
  (c : nat -> arithmetic_expression)
  (k : arithmetic_expression -> arithmetic_expression) : arithmetic_expression :=
  match ae with
    Literal n =>
    c n
  | Name x =>
    k (Name x)
  | Plus ae1 ae2 =>
    curiouser1_aux ae1
      (fun n1 => curiouser1_aux ae2
                   (fun n2 => c (n1 + n2))
                   (fun ae2' => k (Plus (Literal n1) ae2')))
      (fun ae1' => curiouser1_aux ae2
                     (fun n2 => k (Plus ae1' (Literal n2)))
                     (fun ae2' => k (Plus ae1' ae2')))
  end.

Lemma fold_unfold_curiouser1_aux_Literal :
  forall (n : nat)
         (c : nat -> arithmetic_expression)
         (k : arithmetic_expression -> arithmetic_expression),
    curiouser1_aux (Literal n) c k =
    c n.
Proof.
  fold_unfold_tactic curiouser1_aux.
Qed.

Lemma fold_unfold_curiouser1_aux_Name :
  forall (x : string)
         (c : nat -> arithmetic_expression)
         (k : arithmetic_expression -> arithmetic_expression),
    curiouser1_aux (Name x) c k =
    k (Name x).
Proof.
  fold_unfold_tactic curiouser1_aux.
Qed.

Lemma fold_unfold_curiouser1_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (c : nat -> arithmetic_expression)
         (k : arithmetic_expression -> arithmetic_expression),
    curiouser1_aux (Plus ae1 ae2) c k =
    curiouser1_aux ae1
      (fun n1 => curiouser1_aux ae2
                   (fun n2 => c (n1 + n2))
                   (fun ae2' => k (Plus (Literal n1) ae2')))
      (fun ae1' => curiouser1_aux ae2
                     (fun n2 => k (Plus ae1' (Literal n2)))
                     (fun ae2' => k (Plus ae1' ae2'))).
Proof.
  fold_unfold_tactic curiouser1_aux.
Qed.

Definition curiouser1 (sp : source_program) : source_program :=
  match sp with
    Source_program ae =>
    Source_program (curiouser1_aux ae (fun n => Literal n) (fun ae' => ae'))
  end.

Definition compile_curiouser1_alt (sp : source_program) : target_program :=
  compile_ltr (curiouser1 sp).

(* ********** *)

Inductive source_C_or_K : Type :=
  Source_C : nat -> source_C_or_K
| Source_K : arithmetic_expression -> source_C_or_K.

Fixpoint curiouser2_aux (ae : arithmetic_expression) : source_C_or_K :=
  match ae with
    Literal n =>
    Source_C n
  | Name x =>
    Source_K (Name x)
  | Plus ae1 ae2 =>
    match curiouser2_aux ae1 with
      Source_C n1 =>
      match curiouser2_aux ae2 with
        Source_C n2 =>
        Source_C (n1 + n2)
      | Source_K ae2' =>
        Source_K (Plus (Literal n1) ae2')
      end
    | Source_K ae1' =>
      match curiouser2_aux ae2 with
        Source_C n2 =>
        Source_K (Plus ae1' (Literal n2))
      | Source_K ae2' =>
        Source_K (Plus ae1' ae2')
      end
    end
  end.

Lemma fold_unfold_curiouser2_aux_Literal :
  forall (n : nat),
    curiouser2_aux (Literal n) =
    Source_C n.
Proof.
  fold_unfold_tactic curiouser2_aux.
Qed.

Lemma fold_unfold_curiouser2_aux_Name :
  forall (x : string),
    curiouser2_aux (Name x) =
    Source_K (Name x).
Proof.
  fold_unfold_tactic curiouser2_aux.
Qed.

Lemma fold_unfold_curiouser2_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    curiouser2_aux (Plus ae1 ae2) =
    match curiouser2_aux ae1 with
      Source_C n1 =>
      match curiouser2_aux ae2 with
        Source_C n2 =>
        Source_C (n1 + n2)
      | Source_K ae2' =>
        Source_K (Plus (Literal n1) ae2')
      end
    | Source_K ae1' =>
      match curiouser2_aux ae2 with
        Source_C n2 =>
        Source_K (Plus ae1' (Literal n2))
      | Source_K ae2' =>
        Source_K (Plus ae1' ae2')
      end
    end.
Proof.
  fold_unfold_tactic curiouser2_aux.
Qed.

Definition curiouser2 (sp : source_program) : source_program :=
  match sp with
    Source_program ae =>
    Source_program (match curiouser2_aux ae with
                      Source_C n =>
                      Literal n
                    | Source_K ae' =>
                      ae'
                    end)
  end.

Definition compile_curiouser2_alt (sp : source_program) : target_program :=
  compile_ltr (curiouser2 sp).

(* ********** *)

Lemma equivalence_of_curiouser1_and_curiouser2_aux :
  forall (ae : arithmetic_expression)
         (c : nat -> arithmetic_expression)
         (k : arithmetic_expression -> arithmetic_expression),
    (forall (n : nat),
        curiouser2_aux ae = Source_C n ->
        curiouser1_aux ae c k = c n)
    /\
    (forall (ae' : arithmetic_expression),
        curiouser2_aux ae = Source_K ae' ->
        curiouser1_aux ae c k = k ae').
Proof.
  intros ae.
  induction ae as [n | x | ae1 IHae1 ae2 IHae2]; intros c k.
  {
    split.
    - intros n' H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Literal in H_ae.
      rewrite -> fold_unfold_curiouser1_aux_Literal.
      injection H_ae as H_eq.
      rewrite -> H_eq.
      reflexivity.
    - intros ae' H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Literal in H_ae.
      discriminate H_ae.
  }
  {
    split.
    - intros n H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Name in H_ae.
      discriminate H_ae.
    - intros ae' H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Name in H_ae.
      rewrite -> fold_unfold_curiouser1_aux_Name.
      injection H_ae as H_eq.
      rewrite -> H_eq.
      reflexivity.
  }
  {
    split.
    - intros n H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Plus in H_ae.
      rewrite -> fold_unfold_curiouser1_aux_Plus.
      assert (IHae1 := IHae1
                         (fun n1 => curiouser1_aux ae2
                                      (fun n2 => c (n1 + n2))
                                      (fun ae2' => k (Plus (Literal n1) ae2')))
                         (fun ae1' => curiouser1_aux ae2
                                        (fun n2 => k (Plus ae1' (Literal n2)))
                                        (fun ae2' => k (Plus ae1' ae2')))).
      destruct IHae1 as [IHae1_C IHae1_K].
      destruct (curiouser2_aux ae1) as [n1 | ae1'].
      + rewrite -> (IHae1_C n1 eq_refl).
        assert (IHae2 := IHae2
                           (fun n2 => c (n1 + n2))
                           (fun ae2' => k (Plus (Literal n1) ae2'))).
        destruct IHae2 as [IHae2_C IHae2_K].
        destruct (curiouser2_aux ae2) as [n2 | ae2'].
        * rewrite -> (IHae2_C n2 eq_refl).
          injection H_ae as H_eq.
          rewrite -> H_eq.
          reflexivity.
        * discriminate H_ae.
      + destruct (curiouser2_aux ae2) as [n2 | ae2'].
        * discriminate H_ae.
        * discriminate H_ae.
    - intros ae' H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Plus in H_ae.
      rewrite -> fold_unfold_curiouser1_aux_Plus.
      assert (IHae1 := IHae1
                         (fun n1 => curiouser1_aux ae2
                                      (fun n2 => c (n1 + n2))
                                      (fun ae2' => k (Plus (Literal n1) ae2')))
                         (fun ae1' => curiouser1_aux ae2
                                        (fun n2 => k (Plus ae1' (Literal n2)))
                                        (fun ae2' => k (Plus ae1' ae2')))).
      destruct IHae1 as [IHae1_C IHae1_K].
      destruct (curiouser2_aux ae1) as [n1 | ae1'].
      + rewrite -> (IHae1_C n1 eq_refl).
        assert (IHae2 := IHae2
                           (fun n2 => c (n1 + n2))
                           (fun ae2' => k (Plus (Literal n1) ae2'))).
        destruct IHae2 as [IHae2_C IHae2_K].
        destruct (curiouser2_aux ae2) as [n2 | ae2'].
        * discriminate H_ae.
        * rewrite -> (IHae2_K ae2' eq_refl).
          injection H_ae as H_eq.
          rewrite -> H_eq.
          reflexivity.
      + rewrite -> (IHae1_K ae1' eq_refl).
        assert (IHae2 := IHae2
                           (fun n2 => k (Plus ae1' (Literal n2)))
                           (fun ae2' => k (Plus ae1' ae2'))).
        destruct IHae2 as [IHae2_C IHae2_K].
        destruct (curiouser2_aux ae2) as [n2 | ae2'].
        * rewrite -> (IHae2_C n2 eq_refl).
          injection H_ae as H_eq.
          rewrite -> H_eq.
          reflexivity.
        * rewrite -> (IHae2_K ae2' eq_refl).
          injection H_ae as H_eq.
          rewrite -> H_eq.
          reflexivity.
  }
Qed.

Theorem equivalence_of_curiouser1_and_curiouser2 :
  forall (sp : source_program),
    curiouser1 sp =
    curiouser2 sp.
Proof.
  intros [ae].
  unfold curiouser1, curiouser2.
  apply (f_equal (fun z => Source_program z)).
  destruct (equivalence_of_curiouser1_and_curiouser2_aux ae
              (fun n => Literal n)
              (fun ae' => ae'))
    as [H_C H_K].
  destruct (curiouser2_aux ae) as [n | ae'].
  - exact (H_C n eq_refl).
  - exact (H_K ae' eq_refl).
Qed.

(* ********** *)

Lemma curiouser2_preserves_evaluation_aux :
  forall (ae : arithmetic_expression)
         (e : environment nat),
    (forall (n : nat),
        curiouser2_aux ae = Source_C n ->
        Source_expressible_nat n = evaluate_ltr ae e)
    /\
    (forall (ae' : arithmetic_expression),
        curiouser2_aux ae = Source_K ae' ->
        evaluate_ltr ae' e = evaluate_ltr ae e).
Proof.
  intros ae e.
  induction ae as [n | x | ae1 [IHae1_C IHae1_K] ae2 [IHae2_C IHae2_K]].
  {
    split.
    - intros n' H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Literal in H_ae.
      rewrite -> fold_unfold_evaluate_ltr_Literal.
      injection H_ae as H_eq.
      rewrite -> H_eq.
      reflexivity.
    - intros ae' H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Literal in H_ae.
      discriminate H_ae.
  }
  {
    split.
    - intros n H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Name in H_ae.
      discriminate H_ae.
    - intros ae' H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Name in H_ae.
      injection H_ae as H_eq.
      rewrite -> H_eq.
      reflexivity.
  }
  {
    split.
    - intros n H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Plus in H_ae.
      rewrite -> fold_unfold_evaluate_ltr_Plus.
      destruct (curiouser2_aux ae1) as [n1 | ae1'].
      + rewrite <- (IHae1_C n1 eq_refl).
        destruct (curiouser2_aux ae2) as [n2 | ae2'].
        * rewrite <- (IHae2_C n2 eq_refl).
          injection H_ae as H_eq.
          rewrite -> H_eq.
          reflexivity.
        * discriminate H_ae.
      + destruct (curiouser2_aux ae2) as [n2 | ae2'].
        * discriminate H_ae.
        * discriminate H_ae.
    - intros ae' H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Plus in H_ae.
      rewrite -> fold_unfold_evaluate_ltr_Plus.
      destruct (curiouser2_aux ae1) as [n1 | ae1'].
      + rewrite <- (IHae1_C n1 eq_refl).
        destruct (curiouser2_aux ae2) as [n2 | ae2'].
        * discriminate H_ae.
        * rewrite <- (IHae2_K ae2' eq_refl).
          injection H_ae as H_eq.
          rewrite <- H_eq.
          rewrite -> fold_unfold_evaluate_ltr_Plus.
          rewrite -> fold_unfold_evaluate_ltr_Literal.
          reflexivity.
      + rewrite <- (IHae1_K ae1' eq_refl).
        destruct (curiouser2_aux ae2) as [n2 | ae2'].
        * rewrite <- (IHae2_C n2 eq_refl).
          injection H_ae as H_eq.
          rewrite <- H_eq.
          rewrite -> fold_unfold_evaluate_ltr_Plus.
          rewrite -> fold_unfold_evaluate_ltr_Literal.
          reflexivity.
        * rewrite <- (IHae2_K ae2' eq_refl).
          rewrite <- fold_unfold_evaluate_ltr_Plus.
          injection H_ae as H_eq.
          rewrite -> H_eq.
          reflexivity.
  }
Qed.

Theorem curiouser2_preserves_evaluation :
  forall (sp : source_program)
         (e : environment nat),
    interpret_ltr (curiouser2 sp) e =
    interpret_ltr sp e.
Proof.
  intros [ae] e.
  unfold interpret_ltr, curiouser2.
  destruct (curiouser2_preserves_evaluation_aux ae e) as [H_C H_K].
  destruct (curiouser2_aux ae) as [n | ae'].
  - rewrite -> fold_unfold_evaluate_ltr_Literal.
    exact (H_C n eq_refl).
  - exact (H_K ae' eq_refl).
Qed.

Theorem curiouser1_preserves_evaluation :
  forall (sp : source_program)
         (e : environment nat),
    interpret_ltr (curiouser1 sp) e =
    interpret_ltr sp e.
Proof.
  intros sp e.
  rewrite -> (equivalence_of_curiouser1_and_curiouser2 sp).
  exact (curiouser2_preserves_evaluation sp e).
Qed.

(* ********** *)

Theorem equivalence_of_compile_curiouser1_alt_and_compile_curiouser2_alt :
  forall (sp : source_program),
    compile_curiouser1_alt sp =
    compile_curiouser2_alt sp.
Proof.
  intros sp.
  unfold compile_curiouser1_alt, compile_curiouser2_alt.
  rewrite -> (equivalence_of_curiouser1_and_curiouser2 sp).
  reflexivity.
Qed.

(* ********** *)

Inductive target_C_or_K : Type :=
  Target_C : nat -> target_C_or_K
| Target_K : list byte_code_instruction -> target_C_or_K.

Fixpoint compile_curiouser2_aux (ae : arithmetic_expression) : target_C_or_K :=
  match ae with
    Literal n =>
    Target_C n
  | Name x =>
    Target_K (LOOKUP x :: nil)
  | Plus ae1 ae2 =>
    match compile_curiouser2_aux ae1 with
      Target_C n1 =>
      match compile_curiouser2_aux ae2 with
        Target_C n2 =>
        Target_C (n1 + n2)
      | Target_K bcis2 =>
        Target_K (PUSH n1 :: bcis2 ++ ADD :: nil)
      end
    | Target_K bcis1 =>
      match compile_curiouser2_aux ae2 with
        Target_C n2 =>
        Target_K (bcis1 ++ PUSH n2 :: ADD :: nil)
      | Target_K bcis2 =>
        Target_K (bcis1 ++ bcis2 ++ ADD :: nil)
      end
    end
  end.

Lemma fold_unfold_compile_curiouser2_aux_Literal :
  forall (n : nat),
    compile_curiouser2_aux (Literal n) =
    Target_C n.
Proof.
  fold_unfold_tactic compile_curiouser2_aux.
Qed.

Lemma fold_unfold_compile_curiouser2_aux_Name :
  forall (x : string),
    compile_curiouser2_aux (Name x) =
    Target_K (LOOKUP x :: nil).
Proof.
  fold_unfold_tactic compile_curiouser2_aux.
Qed.

Lemma fold_unfold_compile_curiouser2_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_curiouser2_aux (Plus ae1 ae2) =
    match compile_curiouser2_aux ae1 with
      Target_C n1 =>
      match compile_curiouser2_aux ae2 with
        Target_C n2 =>
        Target_C (n1 + n2)
      | Target_K bcis2 =>
        Target_K (PUSH n1 :: bcis2 ++ ADD :: nil)
      end
    | Target_K bcis1 =>
      match compile_curiouser2_aux ae2 with
        Target_C n2 =>
        Target_K (bcis1 ++ PUSH n2 :: ADD :: nil)
      | Target_K bcis2 =>
        Target_K (bcis1 ++ bcis2 ++ ADD :: nil)
      end
    end.
Proof.
  fold_unfold_tactic compile_curiouser2_aux.
Qed.

Definition compile_curiouser2 (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (match compile_curiouser2_aux ae with
                      Target_C n =>
                      PUSH n :: nil
                    | Target_K bcis =>
                      bcis
                    end)
  end.

(* ********** *)

Lemma equivalence_of_compile_curiouser1_and_compile_curiouser2_aux :
  forall (ae : arithmetic_expression)
         (c : nat -> list byte_code_instruction)
         (k : list byte_code_instruction -> list byte_code_instruction),
    (forall (n : nat),
        compile_curiouser2_aux ae = Target_C n ->
        compile_curiouser1_aux ae c k = c n)
    /\
    (forall (bcis : list byte_code_instruction),
        compile_curiouser2_aux ae = Target_K bcis ->
        compile_curiouser1_aux ae c k = k bcis).
Proof.
  intros ae.
  induction ae as [n | x | ae1 IHae1 ae2 IHae2]; intros c k.
  {
    split.
    - intros n' H_ae.
      rewrite -> fold_unfold_compile_curiouser2_aux_Literal in H_ae.
      rewrite -> fold_unfold_compile_curiouser1_aux_Literal.
      injection H_ae as H_eq.
      rewrite -> H_eq.
      reflexivity.
    - intros bcis H_ae.
      rewrite -> fold_unfold_compile_curiouser2_aux_Literal in H_ae.
      discriminate H_ae.
  }
  {
    split.
    - intros n H_ae.
      rewrite -> fold_unfold_compile_curiouser2_aux_Name in H_ae.
      discriminate H_ae.
    - intros bcis H_ae.
      rewrite -> fold_unfold_compile_curiouser2_aux_Name in H_ae.
      rewrite -> fold_unfold_compile_curiouser1_aux_Name.
      injection H_ae as H_eq.
      rewrite -> H_eq.
      reflexivity.
  }
  {
    split.
    - intros n H_ae.
      rewrite -> fold_unfold_compile_curiouser2_aux_Plus in H_ae.
      rewrite -> fold_unfold_compile_curiouser1_aux_Plus.
      assert (IHae1 := IHae1
                         (fun n1 => compile_curiouser1_aux ae2
                                      (fun n2 => c (n1 + n2))
                                      (fun bcis2 => k (PUSH n1 :: bcis2 ++ ADD :: nil)))
                         (fun bcis1 => compile_curiouser1_aux ae2
                                         (fun n2 => k (bcis1 ++ PUSH n2 :: ADD :: nil))
                                         (fun bcis2 => k (bcis1 ++ bcis2 ++ ADD :: nil)))).
      destruct IHae1 as [IHae1_C IHae1_K].
      destruct (compile_curiouser2_aux ae1) as [n1 | bcis1].
      + rewrite -> (IHae1_C n1 eq_refl).
        assert (IHae2 := IHae2
                           (fun n2 => c (n1 + n2))
                           (fun bcis2 => k (PUSH n1 :: bcis2 ++ ADD :: nil))).
        destruct IHae2 as [IHae2_C IHae2_K].
        destruct (compile_curiouser2_aux ae2) as [n2 | bcis2].
        * rewrite -> (IHae2_C n2 eq_refl).
          injection H_ae as H_eq.
          rewrite -> H_eq.
          reflexivity.
        * discriminate H_ae.
      + destruct (compile_curiouser2_aux ae2) as [n2 | bcis2].
        * discriminate H_ae.
        * discriminate H_ae.
    - intros bcis H_ae.
      rewrite -> fold_unfold_compile_curiouser2_aux_Plus in H_ae.
      rewrite -> fold_unfold_compile_curiouser1_aux_Plus.
      assert (IHae1 := IHae1
                         (fun n1 => compile_curiouser1_aux ae2
                                      (fun n2 => c (n1 + n2))
                                      (fun bcis2 => k (PUSH n1 :: bcis2 ++ ADD :: nil)))
                         (fun bcis1 => compile_curiouser1_aux ae2
                                         (fun n2 => k (bcis1 ++ PUSH n2 :: ADD :: nil))
                                         (fun bcis2 => k (bcis1 ++ bcis2 ++ ADD :: nil)))).
      destruct IHae1 as [IHae1_C IHae1_K].
      destruct (compile_curiouser2_aux ae1) as [n1 | bcis1].
      + rewrite -> (IHae1_C n1 eq_refl).
        assert (IHae2 := IHae2
                           (fun n2 => c (n1 + n2))
                           (fun bcis2 => k (PUSH n1 :: bcis2 ++ ADD :: nil))).
        destruct IHae2 as [IHae2_C IHae2_K].
        destruct (compile_curiouser2_aux ae2) as [n2 | bcis2].
        * discriminate H_ae.
        * rewrite -> (IHae2_K bcis2 eq_refl).
          injection H_ae as H_eq.
          rewrite -> H_eq.
          reflexivity.
      + rewrite -> (IHae1_K bcis1 eq_refl).
        assert (IHae2 := IHae2
                           (fun n2 => k (bcis1 ++ PUSH n2 :: ADD :: nil))
                           (fun bcis2 => k (bcis1 ++ bcis2 ++ ADD :: nil))).
        destruct IHae2 as [IHae2_C IHae2_K].
        destruct (compile_curiouser2_aux ae2) as [n2 | bcis2].
        * rewrite -> (IHae2_C n2 eq_refl).
          injection H_ae as H_eq.
          rewrite -> H_eq.
          reflexivity.
        * rewrite -> (IHae2_K bcis2 eq_refl).
          injection H_ae as H_eq.
          rewrite -> H_eq.
          reflexivity.
  }
Qed.

Theorem equivalence_of_compile_curiouser1_and_compile_curiouser2 :
  forall (sp : source_program),
    compile_curiouser1 sp =
    compile_curiouser2 sp.
Proof.
  intros [ae].
  unfold compile_curiouser1, compile_curiouser2.
  apply (f_equal (fun z => Target_program z)).
  destruct (equivalence_of_compile_curiouser1_and_compile_curiouser2_aux ae
              (fun n => PUSH n :: nil)
              (fun bcis => bcis))
    as [H_C H_K].
  destruct (compile_curiouser2_aux ae) as [n | bcis].
  - exact (H_C n eq_refl).
  - exact (H_K bcis eq_refl).
Qed.

(* ********** *)

Lemma equivalence_of_compile_curiouser2_and_compile_curiouser2_alt_aux :
  forall (ae : arithmetic_expression),
    (forall (n : nat),
        curiouser2_aux ae = Source_C n ->
        compile_curiouser2_aux ae = Target_C n)
    /\
    (forall (ae' : arithmetic_expression),
        curiouser2_aux ae = Source_K ae' ->
        compile_curiouser2_aux ae = Target_K (compile_ltr_aux ae')).
Proof.
  intros ae.
  induction ae as [n | x | ae1 [IHae1_C IHae1_K] ae2 [IHae2_C IHae2_K]].
  {
    split.
    - intros n' H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Literal in H_ae.
      rewrite -> fold_unfold_compile_curiouser2_aux_Literal.
      injection H_ae as H_eq.
      rewrite -> H_eq.
      reflexivity.
    - intros ae' H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Literal in H_ae.
      discriminate H_ae.
  }
  {
    split.
    - intros n H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Name in H_ae.
      discriminate H_ae.
    - intros ae' H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Name in H_ae.
      rewrite -> fold_unfold_compile_curiouser2_aux_Name.
      injection H_ae as H_eq.
      rewrite <- H_eq.
      rewrite -> fold_unfold_compile_ltr_aux_Name.
      reflexivity.
  }
  {
    split.
    - intros n H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Plus in H_ae.
      rewrite -> fold_unfold_compile_curiouser2_aux_Plus.
      destruct (curiouser2_aux ae1) as [n1 | ae1'].
      + rewrite -> (IHae1_C n1 eq_refl).
        destruct (curiouser2_aux ae2) as [n2 | ae2'].
        * rewrite -> (IHae2_C n2 eq_refl).
          injection H_ae as H_eq.
          rewrite -> H_eq.
          reflexivity.
        * discriminate H_ae.
      + destruct (curiouser2_aux ae2) as [n2 | ae2'].
        * discriminate H_ae.
        * discriminate H_ae.
    - intros ae' H_ae.
      rewrite -> fold_unfold_curiouser2_aux_Plus in H_ae.
      rewrite -> fold_unfold_compile_curiouser2_aux_Plus.
      destruct (curiouser2_aux ae1) as [n1 | ae1'].
      + rewrite -> (IHae1_C n1 eq_refl).
        destruct (curiouser2_aux ae2) as [n2 | ae2'].
        * discriminate H_ae.
        * rewrite -> (IHae2_K ae2' eq_refl).
          injection H_ae as H_eq.
          rewrite <- H_eq.
          rewrite -> fold_unfold_compile_ltr_aux_Plus.
          rewrite -> fold_unfold_compile_ltr_aux_Literal.
          rewrite -> fold_unfold_app_cons.
          rewrite -> fold_unfold_app_nil.
          reflexivity.
      + rewrite -> (IHae1_K ae1' eq_refl).
        destruct (curiouser2_aux ae2) as [n2 | ae2'].
        * rewrite -> (IHae2_C n2 eq_refl).
          injection H_ae as H_eq.
          rewrite <- H_eq.
          rewrite -> fold_unfold_compile_ltr_aux_Plus.
          rewrite -> fold_unfold_compile_ltr_aux_Literal.
          rewrite -> fold_unfold_app_cons.
          rewrite -> fold_unfold_app_nil.
          reflexivity.
        * rewrite -> (IHae2_K ae2' eq_refl).
          injection H_ae as H_eq.
          rewrite <- H_eq.
          rewrite -> fold_unfold_compile_ltr_aux_Plus.
          reflexivity.
  }
Qed.

Theorem equivalence_of_compile_curiouser2_and_compile_curiouser2_alt :
  forall (sp : source_program),
    compile_curiouser2 sp =
    compile_curiouser2_alt sp.
Proof.
  intros [ae].
  unfold compile_curiouser2, compile_curiouser2_alt, compile_ltr, curiouser2.
  apply (f_equal (fun z => Target_program z)).
  destruct (equivalence_of_compile_curiouser2_and_compile_curiouser2_alt_aux ae) as [H_C H_K].
  destruct (curiouser2_aux ae) as [n | ae'].
  - rewrite -> fold_unfold_compile_ltr_aux_Literal.
    rewrite -> (H_C n eq_refl).
    reflexivity.
  - rewrite -> (H_K ae' eq_refl).
    reflexivity.
Qed.

(* ********** *)

Theorem equivalence_of_compile_curiouser1_and_compile_curiouser1_alt :
  forall (sp : source_program),
    compile_curiouser1 sp =
    compile_curiouser1_alt sp.
Proof.
  intros sp.
  rewrite -> (equivalence_of_compile_curiouser1_alt_and_compile_curiouser2_alt sp).
  rewrite -> (equivalence_of_compile_curiouser1_and_compile_curiouser2 sp).
  exact (equivalence_of_compile_curiouser2_and_compile_curiouser2_alt sp).
Qed.

(* ********** *)

Theorem compile_curiouser1_alt_preserves_execution :
  forall (sp : source_program)
         (e : environment nat),
    run_ltr (compile_curiouser1_alt sp) e =
    run_ltr (compile_ltr sp) e.
Proof.
  intros sp e.
  unfold compile_curiouser1_alt.
  assert (H_curiouser1 := curiouser1_preserves_evaluation sp e).
  assert (H_commuting := the_commuting_diagram_ltr sp e).
  assert (H_commuting' := the_commuting_diagram_ltr (curiouser1 sp) e).
  unfold same_results in H_commuting, H_commuting'.
  destruct H_commuting as [[n [H_interpret H_run]] | [s [H_interpret H_run]]].
  - rewrite -> H_interpret in H_curiouser1.
    rewrite -> H_run.
    destruct H_commuting' as [[n' [H_interpret' H_run']] | [s' [H_interpret' H_run']]].
    + rewrite -> H_interpret' in H_curiouser1.
      rewrite -> H_run'.
      injection H_curiouser1 as H_eq.
      rewrite -> H_eq.
      reflexivity.
    + rewrite -> H_interpret' in H_curiouser1.
      discriminate H_curiouser1.
  - rewrite -> H_interpret in H_curiouser1.
    rewrite -> H_run.
    destruct H_commuting' as [[n' [H_interpret' H_run']] | [s' [H_interpret' H_run']]].
    + rewrite -> H_interpret' in H_curiouser1.
      discriminate H_curiouser1.
    + rewrite -> H_interpret' in H_curiouser1.
      rewrite -> H_run'.
      injection H_curiouser1 as H_eq.
      rewrite -> H_eq.
      reflexivity.
Qed.

Theorem compile_curiouser1_preserves_execution :
  forall (sp : source_program)
         (e : environment nat),
    run_ltr (compile_curiouser1 sp) e =
    run_ltr (compile_ltr sp) e.
Proof.
  intros sp e.
  rewrite -> (equivalence_of_compile_curiouser1_and_compile_curiouser1_alt sp).
  exact (compile_curiouser1_alt_preserves_execution sp e).
Qed.

Theorem compile_curiouser2_preserves_execution :
  forall (sp : source_program)
         (e : environment nat),
    run_ltr (compile_curiouser2 sp) e =
    run_ltr (compile_ltr sp) e.
Proof.
  intros sp e.
  rewrite <- (equivalence_of_compile_curiouser1_and_compile_curiouser2 sp).
  exact (compile_curiouser1_preserves_execution sp e).
Qed.

Theorem compile_curiouser2_alt_preserves_execution :
  forall (sp : source_program)
         (e : environment nat),
    run_ltr (compile_curiouser2_alt sp) e =
    run_ltr (compile_ltr sp) e.
Proof.
  intros sp e.
  rewrite <- (equivalence_of_compile_curiouser2_and_compile_curiouser2_alt sp).
  exact (compile_curiouser2_preserves_execution sp e).
Qed.

(* ********** *)

(* Relational reasoning: *)

Inductive cont_k :
  (list byte_code_instruction -> list byte_code_instruction) ->
  (arithmetic_expression -> arithmetic_expression) ->
  Prop :=
  Cont_K0 : cont_k
              (fun bcis => bcis)
              (fun ae' => ae')
| Cont_K1 : forall (ae2 : arithmetic_expression)
                   (tk : list byte_code_instruction -> list byte_code_instruction)
                   (sk : arithmetic_expression -> arithmetic_expression),
    (* "t" stands for "target", "s" stands for "source" *)
    cont_k tk sk ->
    cont_k
      (fun bcis1 => compile_curiouser1_aux ae2
                      (fun n2 => tk (bcis1 ++ PUSH n2 :: ADD :: nil))
                      (fun bcis2 => tk (bcis1 ++ bcis2 ++ ADD :: nil)))
      (fun ae1' => curiouser1_aux ae2
                     (fun n2 => sk (Plus ae1' (Literal n2)))
                     (fun ae2' => sk (Plus ae1' ae2')))
| Cont_K2 : forall (n1 : nat)
                   (tk : list byte_code_instruction -> list byte_code_instruction)
                   (sk : arithmetic_expression -> arithmetic_expression),
    cont_k tk sk ->
    cont_k
      (fun bcis2 => tk (PUSH n1 :: bcis2 ++ ADD :: nil))
      (fun ae2' => sk (Plus (Literal n1) ae2'))
| Cont_K3 : forall (bcis1 : list byte_code_instruction)
                   (ae1' : arithmetic_expression)
                   (tk : list byte_code_instruction -> list byte_code_instruction)
                   (sk : arithmetic_expression -> arithmetic_expression),
    cont_k tk sk ->
    cont_k
      (fun bcis2 => tk (bcis1 ++ bcis2 ++ ADD :: nil))
      (fun ae2' => sk (Plus ae1' ae2')).

Inductive cont_c :
  (nat -> list byte_code_instruction) ->
  (nat -> arithmetic_expression) ->
  Prop :=
  Cont_C0 : cont_c
              (fun n => PUSH n :: nil)
              (fun n => Literal n)
| Cont_C1 : forall (ae2 : arithmetic_expression)
                   (tc : nat -> list byte_code_instruction)
                   (tk : list byte_code_instruction -> list byte_code_instruction)
                   (sc : nat -> arithmetic_expression)
                   (sk : arithmetic_expression -> arithmetic_expression),
    cont_c tc sc ->
    cont_k tk sk ->
    cont_c
      (fun n1 => compile_curiouser1_aux ae2
                   (fun n2 => tc (n1 + n2))
                   (fun bcis2 => tk (PUSH n1 :: bcis2 ++ ADD :: nil)))
      (fun n1 => curiouser1_aux ae2
                   (fun n2 => sc (n1 + n2))
                   (fun ae2' => sk (Plus (Literal n1) ae2')))
| Cont_C2 : forall (n1 : nat)
                   (tc : nat -> list byte_code_instruction)
                   (sc : nat -> arithmetic_expression),
    cont_c tc sc ->
    cont_c
      (fun n2 => tc (n1 + n2))
      (fun n2 => sc (n1 + n2))
| Cont_C3 : forall (bcis1 : list byte_code_instruction)
                   (ae1' : arithmetic_expression)
                   (tk : list byte_code_instruction -> list byte_code_instruction)
                   (sk : arithmetic_expression -> arithmetic_expression),
    cont_k tk sk ->
    cont_c
      (fun n2 => tk (bcis1 ++ PUSH n2 :: ADD :: nil))
      (fun n2 => sk (Plus ae1' (Literal n2))).

Lemma equivalence_of_compile_curiouser1_and_compile_curiouser1_alt'_aux :
  forall (ae : arithmetic_expression)
         (tc : nat -> list byte_code_instruction)
         (tk : list byte_code_instruction -> list byte_code_instruction)
         (sc : nat -> arithmetic_expression)
         (sk : arithmetic_expression -> arithmetic_expression),
    cont_c tc sc ->
    cont_k tk sk ->
    (forall (n : nat), tc n = compile_ltr_aux (sc n)) ->
    (forall (ae' : arithmetic_expression), tk (compile_ltr_aux ae') = compile_ltr_aux (sk ae')) ->
    compile_curiouser1_aux ae tc tk = compile_ltr_aux (curiouser1_aux ae sc sk).
Proof.
  intros ae.
  induction ae as [n | x | ae1 IHae1 ae2 IHae2]; intros tc tk sc sk C_tc_sc C_tk_sk H_tc_sc H_tk_sk.
  - rewrite -> fold_unfold_compile_curiouser1_aux_Literal.
    rewrite -> fold_unfold_curiouser1_aux_Literal.
    (* if we have a property that states:
       ```
       tc n = compile_ltr_aux (sc n)
       ```
       then this goal can be proven
     *)
    exact (H_tc_sc n).
  - rewrite -> fold_unfold_compile_curiouser1_aux_Name.
    rewrite -> fold_unfold_curiouser1_aux_Name.
    (* if we have a property that states:
       ```
       tk (compile_ltr_aux ae') = compile_ltr_aux (sk ae')
       ```
       then this goal can be proven
     *)
    rewrite <- fold_unfold_compile_ltr_aux_Name.
    exact (H_tk_sk (Name x)).
  - rewrite -> fold_unfold_compile_curiouser1_aux_Plus.
    rewrite -> fold_unfold_curiouser1_aux_Plus.
    apply IHae1.
    + exact (Cont_C1 _ _ _ _ _ C_tc_sc C_tk_sk).
    + exact (Cont_K1 _ _ _ C_tk_sk).
    + intros n.
      apply IHae2.
      * exact (Cont_C2 _ _ _ C_tc_sc).
      * exact (Cont_K2 _ _ _ C_tk_sk).
      * intros n'.
        exact (H_tc_sc (n + n')).
      * intros ae'.
        assert (ly := H_tk_sk (Plus (Literal n) ae')).
        rewrite -> fold_unfold_compile_ltr_aux_Plus in ly.
        rewrite -> fold_unfold_compile_ltr_aux_Literal in ly.
        rewrite -> fold_unfold_app_cons in ly.
        rewrite -> fold_unfold_app_nil in ly.
        exact ly.
    + intros ae'.
      apply IHae2.
      * exact (Cont_C3 _ _ _ _ C_tk_sk).
      * exact (Cont_K3 _ _ _ _ C_tk_sk).
      * intros n.
        assert (ly := H_tk_sk (Plus ae' (Literal n))).
        rewrite -> fold_unfold_compile_ltr_aux_Plus in ly.
        rewrite -> fold_unfold_compile_ltr_aux_Literal in ly.
        rewrite -> fold_unfold_app_cons in ly.
        rewrite -> fold_unfold_app_nil in ly.
        exact ly.
      * intros ae''.
        rewrite <- fold_unfold_compile_ltr_aux_Plus.
        exact (H_tk_sk (Plus ae' ae'')).
Qed.

Theorem equivalence_of_compile_curiouser1_and_compile_curiouser1_alt' :
  forall (sp : source_program),
    compile_curiouser1 sp =
    compile_curiouser1_alt sp.
Proof.
  intros [ae].
  unfold compile_curiouser1, compile_curiouser1_alt, compile_ltr, curiouser1.
  apply (f_equal (fun z => Target_program z)).
  Check (equivalence_of_compile_curiouser1_and_compile_curiouser1_alt'_aux).
  Check (equivalence_of_compile_curiouser1_and_compile_curiouser1_alt'_aux ae
           (fun n => PUSH n :: nil)
           (fun bcis => bcis)
           (fun n => Literal n)
           (fun ae' => ae')).
  Check (equivalence_of_compile_curiouser1_and_compile_curiouser1_alt'_aux ae
           (fun n => PUSH n :: nil)
           (fun bcis => bcis)
           (fun n => Literal n)
           (fun ae' => ae')
           Cont_C0 Cont_K0).
  assert (H_C : forall (n : nat), PUSH n :: nil = compile_ltr_aux (Literal n)).
  { intros n.
    rewrite -> fold_unfold_compile_ltr_aux_Literal.
    reflexivity. }
  Check (equivalence_of_compile_curiouser1_and_compile_curiouser1_alt'_aux ae
           (fun n => PUSH n :: nil)
           (fun bcis => bcis)
           (fun n => Literal n)
           (fun ae' => ae')
           Cont_C0 Cont_K0 H_C).
  assert (H_K : forall (ae' : arithmetic_expression), compile_ltr_aux ae' = compile_ltr_aux ae').
  { intros ae'.
    reflexivity. }
  Check (equivalence_of_compile_curiouser1_and_compile_curiouser1_alt'_aux ae
           (fun n => PUSH n :: nil)
           (fun bcis => bcis)
           (fun n => Literal n)
           (fun ae' => ae')
           Cont_C0 Cont_K0 H_C H_K).
  exact (equivalence_of_compile_curiouser1_and_compile_curiouser1_alt'_aux ae
           (fun n => PUSH n :: nil)
           (fun bcis => bcis)
           (fun n => Literal n)
           (fun ae' => ae')
           Cont_C0 Cont_K0 H_C H_K).
Qed.

(* ********** *)

(* The commuting diagrams *)

Theorem the_commuting_diagram_ltr_for_curiouser1 :
  forall (sp : source_program)
         (e : environment nat),
    same_results
      (interpret_ltr (curiouser1 sp) e)
      (run_ltr (compile_curiouser1 sp) e).
Proof.
  intros sp e.
  rewrite -> (curiouser1_preserves_evaluation sp e).
  rewrite -> (compile_curiouser1_preserves_execution sp e).
  exact (the_commuting_diagram_ltr sp e).
Qed.

Theorem the_commuting_diagram_ltr_for_curiouser1_alt :
  forall (sp : source_program)
         (e : environment nat),
    same_results
      (interpret_ltr (curiouser1 sp) e)
      (run_ltr (compile_curiouser1_alt sp) e).
Proof.
  intros sp e.
  rewrite -> (curiouser1_preserves_evaluation sp e).
  rewrite -> (compile_curiouser1_alt_preserves_execution sp e).
  exact (the_commuting_diagram_ltr sp e).

  Restart.

  intros sp e.
  unfold compile_curiouser1_alt.
  exact (the_commuting_diagram_ltr (curiouser1 sp) e).
Qed.

Theorem the_commuting_diagram_ltr_for_curiouser2 :
  forall (sp : source_program)
         (e : environment nat),
    same_results
      (interpret_ltr (curiouser2 sp) e)
      (run_ltr (compile_curiouser2 sp) e).
Proof.
  intros sp e.
  rewrite -> (curiouser2_preserves_evaluation sp e).
  rewrite -> (compile_curiouser2_preserves_execution sp e).
  exact (the_commuting_diagram_ltr sp e).
Qed.

Theorem the_commuting_diagram_ltr_for_curiouser2_alt :
  forall (sp : source_program)
         (e : environment nat),
    same_results
      (interpret_ltr (curiouser2 sp) e)
      (run_ltr (compile_curiouser2_alt sp) e).
Proof.
  intros sp e.
  rewrite -> (curiouser2_preserves_evaluation sp e).
  rewrite -> (compile_curiouser2_alt_preserves_execution sp e).
  exact (the_commuting_diagram_ltr sp e).

  Restart.

  intros sp e.
  unfold compile_curiouser2_alt.
  exact (the_commuting_diagram_ltr (curiouser2 sp) e).
Qed.

(* end of term-project.v *)
