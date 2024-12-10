(* midterm-project.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Was originally version of Sat 08 Nov 2024 (Inital Submission) *)
(* Version of 18 Nov 2024 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List String Ascii.

(* ********** *)

(* Equality predicates: *)

Definition String_eqb (s1 s2 : string) : bool :=
  match String.string_dec s1 s2 with
    left _ =>
    true
  | right _ =>
    false
  end.

Definition option_eqb (V : Type) (v_eqb : V -> V -> bool) (v1o v2o : option V) : bool :=
  match v1o with
    Some v1 =>
    match v2o with
      Some v2 =>
      v_eqb v1 v2
    | None =>
      false
    end
  | None =>
    match v2o with
      Some v =>
      false
    | None =>
      true
    end
  end.

Fixpoint list_eqb (V : Type) (v_eqb : V -> V -> bool) (v1s v2s : list V) : bool :=
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
      v_eqb v1 v2 && list_eqb V v_eqb v1s' v2s'
    end
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
    if String_eqb x x'
    then Some d
    else lookup denotable x e'
  end.

(* ********** *)

(* Abstract syntax of source programs: *)

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Name : string -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Times : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

Inductive source_program : Type :=
  Source_program : arithmetic_expression -> source_program.

Fixpoint arithmetic_expression_eqb (ae1 ae2 : arithmetic_expression) : bool :=
  match ae1 with
    Literal n1 =>
    match ae2 with
      Literal n2 =>
      Nat.eqb n1 n2
    | _ =>
      false
    end
  | Name x1 =>
    match ae2 with
      Name x2 =>
      String_eqb x1 x2
    | _ =>
      false
    end
  | Plus ae11 ae12 =>
    match ae2 with
      Plus ae21 ae22 =>
      arithmetic_expression_eqb ae11 ae21 && arithmetic_expression_eqb ae12 ae22
    | _ =>
      false
    end
  | Times ae11 ae12 =>
    match ae2 with
      Times ae21 ae22 =>
      arithmetic_expression_eqb ae11 ae21 && arithmetic_expression_eqb ae12 ae22
    | _ =>
      false
    end
  end.

Definition source_program_eqb (sp1 sp2 : source_program) : bool :=
  match sp1 with
    Source_program ae1 =>
    match sp2 with
      Source_program ae2 =>
      arithmetic_expression_eqb ae1 ae2
    end
  end.

(* ********** *)

Inductive source_msg : Type :=
  Source_undeclared_name : string -> source_msg.

Inductive source_expressible_value : Type :=
  Source_expressible_nat : nat -> source_expressible_value
| Source_expressible_msg : source_msg -> source_expressible_value.

(* ********** *)

(* The source interpreter: *)

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
  | Times ae1 ae2 =>
    match evaluate_ltr ae1 e with
      Source_expressible_nat n1 =>
      match evaluate_ltr ae2 e with
        Source_expressible_nat n2 =>
        Source_expressible_nat (n1 * n2)
      | Source_expressible_msg s2 =>
        Source_expressible_msg s2
      end
    | Source_expressible_msg s1 =>
      Source_expressible_msg s1
    end
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

Lemma fold_unfold_evaluate_ltr_Times :
  forall (ae1 ae2 : arithmetic_expression)
         (e : environment nat),
    evaluate_ltr (Times ae1 ae2) e =
    match evaluate_ltr ae1 e with
      Source_expressible_nat n1 =>
      match evaluate_ltr ae2 e with
        Source_expressible_nat n2 =>
        Source_expressible_nat (n1 * n2)
      | Source_expressible_msg s2 =>
        Source_expressible_msg s2
      end
    | Source_expressible_msg s1 =>
      Source_expressible_msg s1
    end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Definition interpret_ltr (sp : source_program) (e : environment nat) : source_expressible_value :=
  match sp with
    Source_program ae =>
    evaluate_ltr ae e
  end.

(* ********** *)

(* Abstract syntax of target programs: *)

Inductive byte_code_instruction : Type :=
  PUSH : nat -> byte_code_instruction
| LOOKUP : string -> byte_code_instruction
| ADD : byte_code_instruction
| MUL : byte_code_instruction.

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
  | Times ae1 ae2 =>
    compile_ltr_aux ae1 ++ compile_ltr_aux ae2 ++ MUL :: nil
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

Lemma fold_unfold_compile_ltr_aux_Times :
  forall (ae1 ae2 : arithmetic_expression),
    compile_ltr_aux (Times ae1 ae2) =
    compile_ltr_aux ae1 ++ compile_ltr_aux ae2 ++ MUL :: nil.
Proof.
  fold_unfold_tactic compile_ltr_aux.
Qed.

Definition compile_ltr (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_ltr_aux ae)
  end.

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
  | MUL =>
    match ds with
      nil =>
      KO (Result_stack_underflow MUL)
    | n2 :: nil =>
      KO (Result_stack_underflow MUL)
    | n2 :: n1 :: ds'' =>
      OK (n1 * n2 :: ds'')
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

Theorem the_commuting_diagram_ltr :
  forall (sp : source_program)
         (e : environment nat),
    (forall n : nat,
        interpret_ltr sp e = Source_expressible_nat n <->
        run_ltr (compile_ltr sp) e = Target_expressible_nat n)
    /\
    (forall s : string,
        interpret_ltr sp e = Source_expressible_msg (Source_undeclared_name s) <->
        run_ltr (compile_ltr sp) e = Target_expressible_msg (Target_undeclared_name s)).
Proof.
Admitted.

(* ********** *)

Definition Magritte_data_stack : Type :=
  list arithmetic_expression.

Definition Magritte_result_of_decoding_and_execution : Type :=
  option Magritte_data_stack.

Definition Magritte_decode_execute_ltr (bci : byte_code_instruction) (ds : Magritte_data_stack) : Magritte_result_of_decoding_and_execution :=
  match bci with
    PUSH n =>
    Some (Literal n :: ds)
  | LOOKUP x =>
    Some (Name x :: ds)
  | ADD =>
    match ds with
      nil =>
      None
    | ae2 :: nil =>
      None
    | ae2 :: ae1 :: ds'' =>
      Some (Plus ae1 ae2 :: ds'')
    end
  | MUL =>
    match ds with
      nil =>
      None
    | ae2 :: nil =>
      None
    | ae2 :: ae1 :: ds'' =>
      Some (Times ae1 ae2 :: ds'')
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

Definition Magritte_target_expressible_value_eqb (mtev1 mtev2 : Magritte_target_expressible_value) : bool :=
  option_eqb source_program source_program_eqb mtev1 mtev2.

(* ********** *)

(* Definition:
   A _constant expression_ is an expression that does not contain any name.
   We say that it is "constant" because evaluating it always yields the same expressible nat.
 *)

(* Task 1:
   Formalize a simplifier that replaces all constant expressions by the corresponding literal.
*)

(* Task 1a:
   Expand the unit-test function just above with more tests
   and argue that your tests cover all possible cases.
*)

Inductive constant_or_not_constant : Type :=
  C : nat -> constant_or_not_constant
| NC : arithmetic_expression -> constant_or_not_constant.

(* case Literal *)
Definition test_in_simplify_ltr_Literal : arithmetic_expression :=
  Literal 0.

Definition intermediate_simplify_ltr_Literal : constant_or_not_constant :=
  C 0.

Definition result_simplify_ltr_Literal: arithmetic_expression :=
  Literal 0.

(* case Name *)
Definition test_in_simplify_ltr_Name : arithmetic_expression :=
  Name "x"%string.

Definition intermediate_simplify_ltr_Name : constant_or_not_constant :=
  NC (Name "x"%string).

Definition result_simplify_ltr_Name : arithmetic_expression :=
  Name "x"%string.

(* case Plus C C *)
Definition test_in_simplify_ltr_Plus_C_C : arithmetic_expression :=
  Plus (Literal 1) (Literal 10).

Definition intermediate_simplify_ltr_Plus_C_C : constant_or_not_constant :=
  C 11.

Definition result_simplify_ltr_Plus_C_C: arithmetic_expression :=
  Literal 11.

(* case Plus C NC *)
Definition test_in_simplify_ltr_Plus_C_NC: arithmetic_expression :=
  Plus (Literal 1) (Name "x"%string).

Definition intermediate_simplify_ltr_Plus_C_NC: constant_or_not_constant :=
  NC (Plus (Literal 1) (Name "x"%string)).

Definition result_simplify_ltr_Plus_C_NC: arithmetic_expression :=
  Plus (Literal 1) (Name "x"%string).

(* case Plus NC C *)
Definition test_in_simplify_ltr_Plus_NC_C: arithmetic_expression :=
  Plus (Name "x"%string) (Literal 1).

Definition intermediate_simplify_ltr_Plus_NC_C: constant_or_not_constant :=
  NC (Plus (Name "x"%string) (Literal 1)).

Definition result_simplify_ltr_Plus_NC_C: arithmetic_expression :=
  Plus (Name "x"%string) (Literal 1).

(* case Plus NC NC *)
Definition test_in_simplify_ltr_Plus_NC_NC : arithmetic_expression :=
  Plus (Name "x"%string) (Name "y"%string).

Definition intermediate_simplify_ltr_Plus_NC_NC : constant_or_not_constant :=
  NC (Plus (Name "x"%string) (Name "y"%string)).

Definition result_simplify_ltr_Plus_NC_NC : arithmetic_expression :=
  Plus (Name "x"%string) (Name "y"%string).

(* Times versions, really just the Plus versions mutatis mutandis *)
(* case Times C C *)
Definition test_in_simplify_ltr_Times_C_C : arithmetic_expression :=
  Times (Literal 1) (Literal 10).

Definition intermediate_simplify_ltr_Times_C_C : constant_or_not_constant :=
  C 10.

Definition result_simplify_ltr_Times_C_C: arithmetic_expression :=
  Literal 10.

(* case Times C NC *)
Definition test_in_simplify_ltr_Times_C_NC: arithmetic_expression :=
  Times (Literal 1) (Name "x"%string).

Definition intermediate_simplify_ltr_Times_C_NC: constant_or_not_constant :=
  NC (Times (Literal 1) (Name "x"%string)).

Definition result_simplify_ltr_Times_C_NC: arithmetic_expression :=
  Times (Literal 1) (Name "x"%string).

(* case Times NC C *)
Definition test_in_simplify_ltr_Times_NC_C: arithmetic_expression :=
  Times (Name "x"%string) (Literal 1).

Definition intermediate_simplify_ltr_Times_NC_C: constant_or_not_constant :=
  NC (Times (Name "x"%string) (Literal 1)).

Definition result_simplify_ltr_Times_NC_C: arithmetic_expression :=
  Times (Name "x"%string) (Literal 1).

(* case Times NC NC *)
Definition test_in_simplify_ltr_Times_NC_NC : arithmetic_expression :=
  Times (Name "x"%string) (Name "y"%string).

Definition intermediate_simplify_ltr_Times_NC_NC : constant_or_not_constant :=
  NC (Times (Name "x"%string) (Name "y"%string)).

Definition result_simplify_ltr_Times_NC_NC : arithmetic_expression :=
  Times (Name "x"%string) (Name "y"%string).

(* Task 1b:
   Implement a simplifier and verify that it satisfies the unit-test function.
*)

Definition constant_or_not_constant_eqb (cnc1 cnc2 : constant_or_not_constant) :  bool :=
  match cnc1 with
    C n1 =>
    match cnc2 with
      C n2 =>
      Nat.eqb n1 n2
    | NC _ =>
      false
    end
  | NC ae1 =>
    match cnc2 with
      C n2 =>
      false
    | NC ae2 =>
      arithmetic_expression_eqb ae1 ae2
    end
  end.

Definition make_test_simplify_ltr_aux
  (candidate : arithmetic_expression -> constant_or_not_constant)
  (input : arithmetic_expression)
  (expected : constant_or_not_constant) : bool :=
  constant_or_not_constant_eqb (candidate input) expected.

Definition test_simplify_ltr_aux (candidate : arithmetic_expression -> constant_or_not_constant) : bool :=
  make_test_simplify_ltr_aux candidate test_in_simplify_ltr_Literal intermediate_simplify_ltr_Literal &&
  make_test_simplify_ltr_aux candidate test_in_simplify_ltr_Name intermediate_simplify_ltr_Name &&
  make_test_simplify_ltr_aux candidate test_in_simplify_ltr_Plus_C_C intermediate_simplify_ltr_Plus_C_C &&
  make_test_simplify_ltr_aux candidate test_in_simplify_ltr_Plus_C_NC intermediate_simplify_ltr_Plus_C_NC &&
  make_test_simplify_ltr_aux candidate test_in_simplify_ltr_Plus_NC_C intermediate_simplify_ltr_Plus_NC_C &&
  make_test_simplify_ltr_aux candidate test_in_simplify_ltr_Plus_NC_NC intermediate_simplify_ltr_Plus_NC_NC &&
  make_test_simplify_ltr_aux candidate test_in_simplify_ltr_Times_C_C intermediate_simplify_ltr_Times_C_C &&
  make_test_simplify_ltr_aux candidate test_in_simplify_ltr_Times_C_NC intermediate_simplify_ltr_Times_C_NC &&
  make_test_simplify_ltr_aux candidate test_in_simplify_ltr_Times_NC_C intermediate_simplify_ltr_Times_NC_C &&
  make_test_simplify_ltr_aux candidate test_in_simplify_ltr_Times_NC_NC intermediate_simplify_ltr_Times_NC_NC.

Definition ae_from_cnc (cnc : constant_or_not_constant) : arithmetic_expression :=
  match cnc with
    C n =>
    Literal n
  | NC ae =>
    ae
  end.

Definition make_test_simplify_ltr
  (candidate : arithmetic_expression -> arithmetic_expression)
  (input : arithmetic_expression)
  (expected : constant_or_not_constant) : bool :=
  arithmetic_expression_eqb (candidate input) (ae_from_cnc expected).

Definition test_simplify_ltr (candidate : arithmetic_expression -> arithmetic_expression) : bool :=
  make_test_simplify_ltr candidate test_in_simplify_ltr_Literal intermediate_simplify_ltr_Literal &&
  make_test_simplify_ltr candidate test_in_simplify_ltr_Name intermediate_simplify_ltr_Name &&
  make_test_simplify_ltr candidate test_in_simplify_ltr_Plus_C_C intermediate_simplify_ltr_Plus_C_C &&
  make_test_simplify_ltr candidate test_in_simplify_ltr_Plus_C_NC intermediate_simplify_ltr_Plus_C_NC &&
  make_test_simplify_ltr candidate test_in_simplify_ltr_Plus_NC_C intermediate_simplify_ltr_Plus_NC_C &&
  make_test_simplify_ltr candidate test_in_simplify_ltr_Plus_NC_NC intermediate_simplify_ltr_Plus_NC_NC &&
  make_test_simplify_ltr candidate test_in_simplify_ltr_Times_C_C intermediate_simplify_ltr_Times_C_C &&
  make_test_simplify_ltr candidate test_in_simplify_ltr_Times_C_NC intermediate_simplify_ltr_Times_C_NC &&
  make_test_simplify_ltr candidate test_in_simplify_ltr_Times_NC_C intermediate_simplify_ltr_Times_NC_C &&
  make_test_simplify_ltr candidate test_in_simplify_ltr_Times_NC_NC intermediate_simplify_ltr_Times_NC_NC.

Fixpoint simplify_ltr_aux (ae : arithmetic_expression) : constant_or_not_constant :=
  match ae with
    Literal n =>
    C n
  | Name x =>
    NC (Name x)
  | Plus ae1 ae2 =>
    match simplify_ltr_aux ae1 with
      C n1 =>
      match simplify_ltr_aux ae2 with
        C n2 =>
        C (n1 + n2)
      | NC ae2 =>
        NC (Plus (Literal n1) ae2)
      end
    | NC ae1 =>
      match simplify_ltr_aux ae2 with
        C n2 =>
        NC (Plus ae1 (Literal n2))
      | NC ae2 =>
        NC (Plus ae1 ae2)
      end
    end
  | Times ae1 ae2 =>
    match simplify_ltr_aux ae1 with
      C n1 =>
      match simplify_ltr_aux ae2 with
        C n2 =>
        C (n1 * n2)
      | NC ae2 =>
        NC (Times (Literal n1) ae2)
      end
    | NC ae1 =>
      match simplify_ltr_aux ae2 with
        C n2 =>
        NC (Times ae1 (Literal n2))
      | NC ae2 =>
        NC (Times ae1 ae2)
      end
    end
  end.

Compute (test_simplify_ltr_aux simplify_ltr_aux).

Lemma fold_unfold_simplify_ltr_aux_Literal :
  forall (n : nat),
    simplify_ltr_aux (Literal n) =
    C n.
Proof.
  fold_unfold_tactic simplify_ltr_aux.
Qed.

Lemma fold_unfold_simplify_ltr_aux_Name :
  forall (x : string),
    simplify_ltr_aux (Name x) =
    NC (Name x).
Proof.
  fold_unfold_tactic simplify_ltr_aux.
Qed.

Lemma fold_unfold_simplify_ltr_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    simplify_ltr_aux (Plus ae1 ae2) =
    match simplify_ltr_aux ae1 with
      C n1 =>
      match simplify_ltr_aux ae2 with
        C n2 =>
        C (n1 + n2)
      | NC ae2 =>
        NC (Plus (Literal n1) ae2)
      end
    | NC ae1 =>
      match simplify_ltr_aux ae2 with
        C n2 =>
        NC (Plus ae1 (Literal n2))
      | NC ae2 =>
        NC (Plus ae1 ae2)
      end
    end.
Proof.
  fold_unfold_tactic simplify_ltr_aux.
Qed.

Lemma fold_unfold_simplify_ltr_aux_Times :
  forall (ae1 ae2 : arithmetic_expression),
    simplify_ltr_aux (Times ae1 ae2) =
    match simplify_ltr_aux ae1 with
      C n1 =>
      match simplify_ltr_aux ae2 with
        C n2 =>
        C (n1 * n2)
      | NC ae2 =>
        NC (Times (Literal n1) ae2)
      end
    | NC ae1 =>
      match simplify_ltr_aux ae2 with
        C n2 =>
        NC (Times ae1 (Literal n2))
      | NC ae2 =>
        NC (Times ae1 ae2)
      end
    end.
Proof.
  fold_unfold_tactic simplify_ltr_aux.
Qed.

Definition simplify_ltr (ae : arithmetic_expression) : arithmetic_expression :=
  match simplify_ltr_aux ae with
    C n =>
    Literal n
  | NC ae =>
    ae
  end.

Compute (test_simplify_ltr simplify_ltr).

Fixpoint simplify_ltr_aux_c
  (ae : arithmetic_expression)
  (kc : nat -> arithmetic_expression)
  (knc : arithmetic_expression -> arithmetic_expression) : arithmetic_expression :=
  match ae with
    Literal n =>
    kc n
  | Name x =>
    knc (Name x)
  | Plus ae1 ae2 =>
    simplify_ltr_aux_c ae1
      (fun n1 => simplify_ltr_aux_c ae2
                   (fun n2 => kc (n1 + n2))
                   (fun ae2' => knc (Plus (Literal n1) ae2')))
      (fun ae1' => simplify_ltr_aux_c ae2
                     (fun n2 => knc (Plus ae1' (Literal n2)))
                     (fun ae2' => knc (Plus ae1' ae2')))
  | Times ae1 ae2 =>
    simplify_ltr_aux_c ae1
      (fun n1 => simplify_ltr_aux_c ae2
                   (fun n2 => kc (n1 * n2))
                   (fun ae2' => knc (Times (Literal n1) ae2')))
      (fun ae1' => simplify_ltr_aux_c ae2
                     (fun n2 => knc (Times ae1' (Literal n2)))
                     (fun ae2' => knc (Times ae1' ae2')))
  end.

Definition simplify_ltr_c (ae : arithmetic_expression) : arithmetic_expression :=
  simplify_ltr_aux_c ae (fun n => Literal n) (fun ae' => ae').

Compute (test_simplify_ltr simplify_ltr_c).

(*
  Food for thought: in the definition of simplify_ltr_aux_c, we can change the domain of answers to be
  arithmetic_expression instead of constant_or_not_constant. That's possible because all calls are tail
  calls and so the codomain doesn't matter (it could be a polymorphic type).
*)

(* Task 1c:
   Argue that your unit tests provide code coverage.
   (And if they don't, expand test_simplify so that they do.)
*)

(*
  The strategy was to write a test case for each possible case of arithmetic expressions
  where the simplifier is provided a literal, a name, and an arithmetic expression where
  the root node is a plus and where the root node is a times.
  
  The test cases for literals and names are straightforward. In the case where the arithmetic expression
  has plus as the root node, we provide a test case for when plus is applied to constants on the LHS and
  RHS, a constant on the LHS and a non-constant on the RHS, a constant on RHS and a non-constant in the
  LHS, and finally non-constants on the LHS and RHS. We similarly repeat this for when the root node of
  an arithmetic expression is times. This way, we ensure that our unit test function provides code coverage.
*)

(* Task 1d:
   Prove that your simplifier is idempotent: Once an expression is simplified, it contains no constant sub-expressions.
*)

Lemma simplify_ltr_is_idempotent_aux :
  forall ae ae' : arithmetic_expression,
    simplify_ltr_aux ae = NC ae' ->
    simplify_ltr_aux ae' = NC ae'.
Proof.
  intro ae.
  induction ae as [n | x | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro ae'.
  - intro H_absurd.
    rewrite -> fold_unfold_simplify_ltr_aux_Literal in H_absurd.
    discriminate H_absurd.
  - intro H_ae.
    rewrite -> fold_unfold_simplify_ltr_aux_Name in H_ae.
    injection H_ae as H_ae.
    rewrite <- H_ae.
    rewrite -> fold_unfold_simplify_ltr_aux_Name.
    reflexivity.
  - intro H_ae.
    rewrite -> fold_unfold_simplify_ltr_aux_Plus in H_ae.
    destruct (simplify_ltr_aux ae1) as [n1 | ae1'].
    + destruct (simplify_ltr_aux ae2) as [n2 | ae2'].
      * discriminate H_ae.
      * injection H_ae as H_ae.
        rewrite <- H_ae.
        rewrite -> fold_unfold_simplify_ltr_aux_Plus.
        rewrite -> fold_unfold_simplify_ltr_aux_Literal.
        rewrite -> (IHae2 ae2' eq_refl).
        reflexivity.
    + destruct (simplify_ltr_aux ae2) as [n2 | ae2'].
      * injection H_ae as H_ae.
        rewrite <- H_ae.
        rewrite -> fold_unfold_simplify_ltr_aux_Plus.
        rewrite -> (IHae1 ae1' eq_refl).
        rewrite -> fold_unfold_simplify_ltr_aux_Literal.
        reflexivity.
      * injection H_ae as H_ae.
        rewrite <- H_ae.
        rewrite -> fold_unfold_simplify_ltr_aux_Plus.
        rewrite -> (IHae1 ae1' eq_refl).
        rewrite -> (IHae2 ae2' eq_refl).
        reflexivity.
  - intro H_ae.
    rewrite -> fold_unfold_simplify_ltr_aux_Times in H_ae.
    destruct (simplify_ltr_aux ae1) as [n1 | ae1'].
    + destruct (simplify_ltr_aux ae2) as [n2 | ae2'].
      * discriminate H_ae.
      * injection H_ae as H_ae.
        rewrite <- H_ae.
        rewrite -> fold_unfold_simplify_ltr_aux_Times.
        rewrite -> fold_unfold_simplify_ltr_aux_Literal.
        rewrite -> (IHae2 ae2' eq_refl).
        reflexivity.
    + destruct (simplify_ltr_aux ae2) as [n2 | ae2'].
      * injection H_ae as H_ae.
        rewrite <- H_ae.
        rewrite -> fold_unfold_simplify_ltr_aux_Times.
        rewrite -> (IHae1 ae1' eq_refl).
        rewrite -> fold_unfold_simplify_ltr_aux_Literal.
        reflexivity.
      * injection H_ae as H_ae.
        rewrite <- H_ae.
        rewrite -> fold_unfold_simplify_ltr_aux_Times.
        rewrite -> (IHae1 ae1' eq_refl).
        rewrite -> (IHae2 ae2' eq_refl).
        reflexivity.
Qed.

Theorem simplify_ltr_is_idempotent :
  forall (ae : arithmetic_expression),
    simplify_ltr ae =
    simplify_ltr (simplify_ltr ae).
Proof.
  intro ae.
  unfold simplify_ltr.
  destruct (simplify_ltr_aux ae) as [n | ae'] eqn:H_simplify_aux.
  - rewrite -> fold_unfold_simplify_ltr_aux_Literal.
    reflexivity.
  - rewrite -> (simplify_ltr_is_idempotent_aux ae ae' H_simplify_aux).
    reflexivity.
Qed.

(* Task 1e:
   Prove that your simplifier is meaning-preserving,
   i.e., that evaluating an expression and a simplified expression always yield the same expressible value.
*)

Lemma simplify_ltr_preserves_evaluation_aux :
  forall (ae : arithmetic_expression)
         (e : environment nat),
    (forall n : nat,
        simplify_ltr_aux ae = C n ->
        evaluate_ltr ae e = Source_expressible_nat n)
    /\
    (forall ae' : arithmetic_expression,
        simplify_ltr_aux ae = NC ae' ->
        evaluate_ltr ae e = evaluate_ltr ae' e).
Proof.
  intros ae e.
  induction ae as [n | x | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  - split.
    + intros n' H_ae.
      rewrite -> fold_unfold_simplify_ltr_aux_Literal in H_ae.
      injection H_ae as H_ae.
      rewrite -> fold_unfold_evaluate_ltr_Literal.
      rewrite -> H_ae.
      reflexivity.
    + intros ae' H_ae.
      rewrite -> fold_unfold_simplify_ltr_aux_Literal in H_ae.
      discriminate H_ae.
  - split.
    + intros n H_ae.
      rewrite -> fold_unfold_simplify_ltr_aux_Name in H_ae.
      discriminate H_ae.
    + intros ae' H_ae.
      rewrite -> fold_unfold_simplify_ltr_aux_Name in H_ae.
      injection H_ae as H_ae.
      rewrite -> H_ae.
      reflexivity.
  - split.
    + intros n H_ae.
      rewrite -> fold_unfold_simplify_ltr_aux_Plus in H_ae.
      destruct (simplify_ltr_aux ae1) as [n1 | ae1'].
      * destruct (simplify_ltr_aux ae2) as [n2 | ae2'].
        -- injection H_ae as H_ae.
           rewrite <- H_ae.
           rewrite -> fold_unfold_evaluate_ltr_Plus.
           destruct IHae1 as [IHae1_c _].
           destruct IHae2 as [IHae2_c _].
           rewrite -> (IHae1_c n1 eq_refl).
           rewrite -> (IHae2_c n2 eq_refl).
           reflexivity.
        -- discriminate H_ae.
      * destruct (simplify_ltr_aux ae2) as [n2 | ae2'].
        -- discriminate H_ae.
        -- discriminate H_ae.
    + intros ae' H_ae.
      rewrite -> fold_unfold_simplify_ltr_aux_Plus in H_ae.
      destruct (simplify_ltr_aux ae1) as [n1 | ae1'].
      * destruct (simplify_ltr_aux ae2) as [n2 | ae2'].
        -- discriminate H_ae.
        -- injection H_ae as H_ae.
           rewrite <- H_ae.
           rewrite ->2 fold_unfold_evaluate_ltr_Plus.
           rewrite -> fold_unfold_evaluate_ltr_Literal.
           destruct IHae1 as [IHae1_c _].
           destruct IHae2 as [_ IHae2_nc].
           rewrite -> (IHae1_c n1 eq_refl).
           rewrite -> (IHae2_nc ae2' eq_refl).
           reflexivity.
      * destruct (simplify_ltr_aux ae2) as [n2 | ae2'].
        -- injection H_ae as H_ae.
           rewrite <- H_ae.
           rewrite ->2 fold_unfold_evaluate_ltr_Plus.
           rewrite -> fold_unfold_evaluate_ltr_Literal.
           destruct IHae1 as [_ IHae1_nc].
           destruct IHae2 as [IHae2_c _].
           rewrite -> (IHae1_nc ae1' eq_refl).
           rewrite -> (IHae2_c n2 eq_refl).
           reflexivity.
        -- injection H_ae as H_ae.
           rewrite <- H_ae.
           rewrite ->2 fold_unfold_evaluate_ltr_Plus.
           destruct IHae1 as [_ IHae1_nc].
           destruct IHae2 as [_ IHae2_nc].
           rewrite -> (IHae1_nc ae1' eq_refl).
           rewrite -> (IHae2_nc ae2' eq_refl).
           reflexivity.
  - split.
    + intros n H_ae.
      rewrite -> fold_unfold_simplify_ltr_aux_Times in H_ae.
      destruct (simplify_ltr_aux ae1) as [n1 | ae1'].
      * destruct (simplify_ltr_aux ae2) as [n2 | ae2'].
        -- injection H_ae as H_ae.
           rewrite <- H_ae.
           rewrite -> fold_unfold_evaluate_ltr_Times.
           destruct IHae1 as [IHae1_c _].
           destruct IHae2 as [IHae2_c _].
           rewrite -> (IHae1_c n1 eq_refl).
           rewrite -> (IHae2_c n2 eq_refl).
           reflexivity.
        -- discriminate H_ae.
      * destruct (simplify_ltr_aux ae2) as [n2 | ae2'].
        -- discriminate H_ae.
        -- discriminate H_ae.
    + intros ae' H_ae.
      rewrite -> fold_unfold_simplify_ltr_aux_Times in H_ae.
      destruct (simplify_ltr_aux ae1) as [n1 | ae1'].
      * destruct (simplify_ltr_aux ae2) as [n2 | ae2'].
        -- discriminate H_ae.
        -- injection H_ae as H_ae.
           rewrite <- H_ae.
           rewrite ->2 fold_unfold_evaluate_ltr_Times.
           rewrite -> fold_unfold_evaluate_ltr_Literal.
           destruct IHae1 as [IHae1_c _].
           destruct IHae2 as [_ IHae2_nc].
           rewrite -> (IHae1_c n1 eq_refl).
           rewrite -> (IHae2_nc ae2' eq_refl).
           reflexivity.
      * destruct (simplify_ltr_aux ae2) as [n2 | ae2'].
        -- injection H_ae as H_ae.
           rewrite <- H_ae.
           rewrite ->2 fold_unfold_evaluate_ltr_Times.
           rewrite -> fold_unfold_evaluate_ltr_Literal.
           destruct IHae1 as [_ IHae1_nc].
           destruct IHae2 as [IHae2_c _].
           rewrite -> (IHae1_nc ae1' eq_refl).
           rewrite -> (IHae2_c n2 eq_refl).
           reflexivity.
        -- injection H_ae as H_ae.
           rewrite <- H_ae.
           rewrite ->2 fold_unfold_evaluate_ltr_Times.
           destruct IHae1 as [_ IHae1_nc].
           destruct IHae2 as [_ IHae2_nc].
           rewrite -> (IHae1_nc ae1' eq_refl).
           rewrite -> (IHae2_nc ae2' eq_refl).
           reflexivity.
Qed.

Theorem simplify_ltr_preserves_evaluation :
  forall (ae : arithmetic_expression)
         (e : environment nat),
    evaluate_ltr (simplify_ltr ae) e =
    evaluate_ltr ae e.
Proof.
  intros ae e.
  unfold simplify_ltr.
  Check (simplify_ltr_preserves_evaluation_aux ae e).
  destruct (simplify_ltr_preserves_evaluation_aux ae e) as [H_ae_C H_ae_NC].
  destruct (simplify_ltr_aux ae) as [n | ae'].
  - rewrite -> fold_unfold_evaluate_ltr_Literal.
    rewrite -> (H_ae_C n eq_refl).
    reflexivity.
  - rewrite -> (H_ae_NC ae' eq_refl).
    reflexivity.
Qed.

(* Task 1e:
   Prove that your simplifier is simpifying,
   i.e., there are no constant-foldable terms left in each branch.
*)

Definition option_bool_eqb (b1o b2o : option bool) : bool :=
  option_eqb bool Bool.eqb b1o b2o.

Definition test_simplifiedp_aux (candidate : arithmetic_expression -> option bool) : bool :=
  option_bool_eqb (candidate (Literal 1)) (Some true)
  && option_bool_eqb (candidate (Name "x"%string)) (Some false)
  && option_bool_eqb (candidate (Plus (Literal 0) (Name "x"%string))) (Some false)
  && option_bool_eqb (candidate (Plus (Name "x"%string) (Literal 0))) (Some false)
  && option_bool_eqb (candidate (Plus (Name "x"%string) (Name "y"%string))) (Some false)
  && option_bool_eqb (candidate (Times (Literal 0) (Name "x"%string))) (Some false)
  && option_bool_eqb (candidate (Times (Name "x"%string) (Literal 0))) (Some false)
  && option_bool_eqb (candidate (Times (Name "x"%string) (Name "y"%string))) (Some false)
  && option_bool_eqb (candidate (Plus
                                   (Plus
                                      (Name "x"%string)
                                      (Literal 0))
                                   (Plus
                                      (Name "y"%string)
                                      (Literal 1)))) (Some false)
  && option_bool_eqb (candidate (Plus
                                   (Plus
                                      (Literal 0)
                                      (Name "x"%string))
                                   (Plus
                                      (Literal 1)
                                      (Name "y"%string)))) (Some false)
  && option_bool_eqb (candidate (Plus
                                   (Plus
                                      (Name "x"%string)
                                      (Literal 0))
                                   (Plus
                                      (Literal 1)
                                      (Name "y"%string)))) (Some false)
  && option_bool_eqb (candidate (Times
                                   (Times
                                      (Name "x"%string)
                                      (Literal 0))
                                   (Times
                                      (Name "y"%string)
                                      (Literal 1)))) (Some false)
  && option_bool_eqb (candidate (Times
                                   (Times
                                      (Literal 0)
                                      (Name "x"%string))
                                   (Times
                                      (Literal 1)
                                      (Name "y"%string)))) (Some false)
  && option_bool_eqb (candidate (Times
                                   (Times
                                      (Name "x"%string)
                                      (Literal 0))
                                   (Times
                                      (Literal 1)
                                      (Name "y"%string)))) (Some false)
  && option_bool_eqb (candidate (Plus (Literal 0) (Literal 1))) None
  && option_bool_eqb (candidate (Times (Literal 0) (Literal 1))) None
  && option_bool_eqb (candidate (Plus (Plus (Literal 0) (Literal 1)) (Literal 2))) None
  && option_bool_eqb (candidate (Plus (Literal 2) (Plus (Literal 0) (Literal 1)))) None
  && option_bool_eqb (candidate (Times (Literal 0) (Literal 1))) None
  && option_bool_eqb (candidate (Times (Literal 0) (Literal 1))) None
  && option_bool_eqb (candidate (Times (Times (Literal 0) (Literal 1)) (Literal 2))) None
  && option_bool_eqb (candidate (Times (Literal 2) (Times (Literal 0) (Literal 1)))) None.

Fixpoint simplifiedp_aux (ae : arithmetic_expression) : option bool :=
  match ae with
    Literal _ =>
    Some true
  | Name _ =>
    Some false
  | Plus ae1 ae2 =>
    match simplifiedp_aux ae1 with
      Some true =>
      match simplifiedp_aux ae2 with
        Some true =>
        None
      | Some false =>
        Some false
      | None =>
        None
      end
    | Some false =>
      match simplifiedp_aux ae2 with
        Some true =>
        Some false
      | Some false =>
        Some false
      | None =>
        None
      end
    | None =>
      None
    end
  | Times ae1 ae2 =>
    match simplifiedp_aux ae1 with
      Some true =>
      match simplifiedp_aux ae2 with
        Some true =>
        None
      | Some false =>
        Some false
      | None =>
        None
      end
    | Some false =>
      match simplifiedp_aux ae2 with
        Some true =>
        Some false
      | Some false =>
        Some false
      | None =>
        None
      end
    | None =>
      None
    end
  end.

Compute (test_simplifiedp_aux simplifiedp_aux).

Lemma fold_unfold_simplifiedp_aux_Literal :
  forall (n : nat),
    simplifiedp_aux (Literal n) =
    Some true.
Proof.
  fold_unfold_tactic simplifiedp_aux.
Qed.

Lemma fold_unfold_simplifiedp_aux_Name :
  forall (x : string),
    simplifiedp_aux (Name x) =
    Some false.
Proof.
  fold_unfold_tactic simplifiedp_aux.
Qed.

Lemma fold_unfold_simplifiedp_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    simplifiedp_aux (Plus ae1 ae2) =
    match simplifiedp_aux ae1 with
      Some true =>
      match simplifiedp_aux ae2 with
        Some true =>
        None
      | Some false =>
        Some false
      | None =>
        None
      end
    | Some false =>
      match simplifiedp_aux ae2 with
        Some true =>
        Some false
      | Some false =>
        Some false
      | None =>
        None
      end
    | None =>
      None
    end.
Proof.
  fold_unfold_tactic simplifiedp_aux.
Qed.

Lemma fold_unfold_simplifiedp_aux_Times :
  forall ae1 ae2 : arithmetic_expression,
    simplifiedp_aux (Times ae1 ae2) =
    match simplifiedp_aux ae1 with
      Some true =>
      match simplifiedp_aux ae2 with
        Some true =>
        None
      | Some false =>
        Some false
      | None =>
        None
      end
    | Some false =>
      match simplifiedp_aux ae2 with
        Some true =>
        Some false
      | Some false =>
        Some false
      | None =>
        None
      end
    | None =>
      None
    end.    
Proof.
  fold_unfold_tactic simplifiedp_aux.
Qed.

Definition simplifiedp (ae : arithmetic_expression) : bool :=
  match simplifiedp_aux ae with
  | Some _ =>
    true
  | None =>
    false
  end.

Fixpoint simplifiedp_aux_c (ae : arithmetic_expression) (kc knc : unit -> bool) : bool :=
  match ae with
    Literal _ =>
    kc tt
  | Name _ =>
    knc tt
  | Plus ae1 ae2 =>
    simplifiedp_aux_c ae1
      (fun _ => simplifiedp_aux_c ae2 (fun _ => false) knc)
      (fun _ => simplifiedp_aux_c ae2 knc knc)
  | Times ae1 ae2 =>
    simplifiedp_aux_c ae1
      (fun _ => simplifiedp_aux_c ae2 (fun _ => false) knc)
      (fun _ => simplifiedp_aux_c ae2 knc knc)
  end.

Definition simplifiedp_c (ae : arithmetic_expression) : bool :=
  simplifiedp_aux_c ae (fun _ => true) (fun _ => true).

Lemma soundness_of_simplify_ltr_aux :
  forall (ae ae' : arithmetic_expression),
    simplify_ltr_aux ae = NC ae' ->
    simplifiedp_aux ae' = Some false.
Proof.
  intro ae.
  induction ae as [n | x | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intros ae' H_simplify.
  - rewrite -> fold_unfold_simplify_ltr_aux_Literal in H_simplify.
    discriminate H_simplify.
  - rewrite -> fold_unfold_simplify_ltr_aux_Name in H_simplify.
    injection H_simplify as H_eq.
    rewrite <- H_eq.
    rewrite -> fold_unfold_simplifiedp_aux_Name.
    reflexivity.
  - rewrite -> fold_unfold_simplify_ltr_aux_Plus in H_simplify.
    case (simplify_ltr_aux ae1) as [n1 | ae1'] eqn:H_simplify_ae1.
    + case (simplify_ltr_aux ae2) as [n2 | ae2'] eqn:H_simplify_ae2.
      * discriminate H_simplify.
      * injection H_simplify as H_eq.
        rewrite <- H_eq.
        rewrite -> fold_unfold_simplifiedp_aux_Plus.
        rewrite -> fold_unfold_simplifiedp_aux_Literal.
        rewrite -> (IHae2 ae2' eq_refl).
        reflexivity.
    + case (simplify_ltr_aux ae2) as [n2 | ae2'] eqn:H_simplify_ae2.
      * injection H_simplify as H_eq.
        rewrite <- H_eq.
        rewrite -> fold_unfold_simplifiedp_aux_Plus.
        rewrite -> fold_unfold_simplifiedp_aux_Literal.
        rewrite -> (IHae1 ae1' eq_refl).
        reflexivity.
      * injection H_simplify as H_eq.
        rewrite <- H_eq.
        rewrite -> fold_unfold_simplifiedp_aux_Plus.
        rewrite -> (IHae1 ae1' eq_refl).
        rewrite -> (IHae2 ae2' eq_refl).
        reflexivity.
  - rewrite -> fold_unfold_simplify_ltr_aux_Times in H_simplify.
    case (simplify_ltr_aux ae1) as [n1 | ae1'] eqn:H_simplify_ae1.
    + case (simplify_ltr_aux ae2) as [n2 | ae2'] eqn:H_simplify_ae2.
      * discriminate H_simplify.
      * injection H_simplify as H_eq.
        rewrite <- H_eq.
        rewrite -> fold_unfold_simplifiedp_aux_Times.
        rewrite -> fold_unfold_simplifiedp_aux_Literal.
        rewrite -> (IHae2 ae2' eq_refl).
        reflexivity.
    + case (simplify_ltr_aux ae2) as [n2 | ae2'] eqn:H_simplify_ae2.
      * injection H_simplify as H_eq.
        rewrite <- H_eq.
        rewrite -> fold_unfold_simplifiedp_aux_Times.
        rewrite -> fold_unfold_simplifiedp_aux_Literal.
        rewrite -> (IHae1 ae1' eq_refl).
        reflexivity.
      * injection H_simplify as H_eq.
        rewrite <- H_eq.
        rewrite -> fold_unfold_simplifiedp_aux_Times.
        rewrite -> (IHae1 ae1' eq_refl).
        rewrite -> (IHae2 ae2' eq_refl).
        reflexivity.
Qed.

Theorem soundness_of_simplify_ltr :
  forall ae ae' : arithmetic_expression,
    simplify_ltr ae = ae' ->
    simplifiedp ae' = true.
Proof.
  unfold simplify_ltr, simplifiedp.
  intros ae ae' H_simplify.
  case (simplify_ltr_aux ae) as [n | ae''] eqn:H_simplify'.
  - rewrite <- H_simplify.
    rewrite -> fold_unfold_simplifiedp_aux_Literal.
    reflexivity.
  - rewrite <- H_simplify.
    rewrite -> (soundness_of_simplify_ltr_aux ae ae'' H_simplify').
    reflexivity.
Qed.

Lemma simplify_simplifies :
  forall (ae : arithmetic_expression),
    simplifiedp (simplify_ltr ae) = true.
Proof.
  intro ae.
  Check (soundness_of_simplify_ltr ae (simplify_ltr ae) (eq_refl (simplify_ltr ae))).
  rewrite -> (soundness_of_simplify_ltr ae (simplify_ltr ae) (eq_refl (simplify_ltr ae))).
  reflexivity.
Qed.

(* completeness of soundness *)

Lemma completeness_of_simplify_aux :
  forall ae : arithmetic_expression,
    (simplifiedp_aux ae = Some true ->
     exists n : nat,
       ae = Literal n)
     /\
     (simplifiedp_aux ae = Some false ->
       simplify_ltr_aux ae = NC ae).
Proof.
  intro ae.
  induction ae as [ n | x | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2];
    split.

  - intros _.
    exists n.
    reflexivity.

  - intro H_absurd.
    rewrite -> fold_unfold_simplifiedp_aux_Literal in H_absurd.
    discriminate H_absurd.

  - intro H_absurd.
    rewrite -> fold_unfold_simplifiedp_aux_Name in H_absurd.
    discriminate H_absurd.

  - intros _.
    rewrite -> fold_unfold_simplify_ltr_aux_Name.
    reflexivity.

  - rewrite -> (fold_unfold_simplifiedp_aux_Plus ae1 ae2).
    case (simplifiedp_aux ae1) as [ [ | ] | ] eqn: C_ae1; case (simplifiedp_aux ae2) as [ [ | ] | ] eqn:C_ae2.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       injection H_absurd as H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       injection H_absurd as H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       injection H_absurd as H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.

  - rewrite -> (fold_unfold_simplifiedp_aux_Plus ae1 ae2).
    case (simplifiedp_aux ae1) as [ [ | ] | ] eqn: C_ae1; case (simplifiedp_aux ae2) as [ [ | ] | ] eqn:C_ae2.

    + intro H_absurd.
       discriminate H_absurd.

    + intros _.
       rewrite -> (fold_unfold_simplify_ltr_aux_Plus ae1 ae2).
       destruct IHae1 as [IHae1 _ ].
       destruct IHae2 as [_ IHae2 ].
       assert (IHae2 := IHae2 (eq_refl (Some false))).
       assert (IHae1 := IHae1 (eq_refl (Some true))).
       destruct IHae1 as [n1 IHae1'].
       rewrite -> IHae2.
       rewrite -> IHae1'.
       rewrite -> (fold_unfold_simplify_ltr_aux_Literal n1).
       reflexivity.


    + intro H_absurd.
       discriminate H_absurd.

    + intros _.
       rewrite -> (fold_unfold_simplify_ltr_aux_Plus ae1 ae2).
       destruct IHae1 as [_ IHae1].
       destruct IHae2 as [IHae2 _].
       assert (IHae2 := IHae2 (eq_refl (Some true))).
       assert (IHae1 := IHae1 (eq_refl (Some false))).
       destruct IHae2 as [n2 IHae2'].
       rewrite -> IHae2'.
       rewrite -> IHae1.
       rewrite -> (fold_unfold_simplify_ltr_aux_Literal n2).
       reflexivity.

    + intros _.
       rewrite -> (fold_unfold_simplify_ltr_aux_Plus ae1 ae2).
       destruct IHae1 as [_ IHae1].
       destruct IHae2 as [_ IHae2].
       assert (IHae2 := IHae2 (eq_refl (Some false))).
       assert (IHae1 := IHae1 (eq_refl (Some false))).
       rewrite -> IHae2.
       rewrite -> IHae1.
       reflexivity.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.

  - rewrite -> (fold_unfold_simplifiedp_aux_Times ae1 ae2).
    case (simplifiedp_aux ae1) as [ [ | ] | ] eqn: C_ae1; case (simplifiedp_aux ae2) as [ [ | ] | ] eqn:C_ae2.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       injection H_absurd as H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       injection H_absurd as H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       injection H_absurd as H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.

  - rewrite -> (fold_unfold_simplifiedp_aux_Times ae1 ae2).
    case (simplifiedp_aux ae1) as [ [ | ] | ] eqn: C_ae1; case (simplifiedp_aux ae2) as [ [ | ] | ] eqn:C_ae2.

    + intro H_absurd.
       discriminate H_absurd.

    + intros _.
       rewrite -> (fold_unfold_simplify_ltr_aux_Times ae1 ae2).
       destruct IHae1 as [IHae1 _ ].
       destruct IHae2 as [_ IHae2 ].
       assert (IHae2 := IHae2 (eq_refl (Some false))).
       assert (IHae1 := IHae1 (eq_refl (Some true))).
       destruct IHae1 as [n1 IHae1'].
       rewrite -> IHae2.
       rewrite -> IHae1'.
       rewrite -> (fold_unfold_simplify_ltr_aux_Literal n1).
       reflexivity.

    + intro H_absurd.
       discriminate H_absurd.

    + intros _.
       rewrite -> (fold_unfold_simplify_ltr_aux_Times ae1 ae2).
       destruct IHae1 as [_ IHae1].
       destruct IHae2 as [IHae2 _].
       assert (IHae2 := IHae2 (eq_refl (Some true))).
       assert (IHae1 := IHae1 (eq_refl (Some false))).
       destruct IHae2 as [n2 IHae2'].
       rewrite -> IHae2'.
       rewrite -> IHae1.
       rewrite -> (fold_unfold_simplify_ltr_aux_Literal n2).
       reflexivity.

    + intros _.
       rewrite -> (fold_unfold_simplify_ltr_aux_Times ae1 ae2).
       destruct IHae1 as [_ IHae1].
       destruct IHae2 as [_ IHae2].
       assert (IHae2 := IHae2 (eq_refl (Some false))).
       assert (IHae1 := IHae1 (eq_refl (Some false))).
       rewrite -> IHae2.
       rewrite -> IHae1.
       reflexivity.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.

    + intro H_absurd.
       discriminate H_absurd.
Qed.

Theorem completeness_of_simplify :
  forall ae : arithmetic_expression,
    simplifiedp ae = true ->
    simplify_ltr ae = ae.
Proof.
  intro ae.
  unfold simplifiedp, simplify_ltr.
  case (simplifiedp_aux ae) as [ [ | ] | ] eqn: C_simpae.
  - intros _.
    Check (completeness_of_simplify_aux ae).
    destruct (completeness_of_simplify_aux ae) as [H_aux_Sometrue _].
    Check (H_aux_Sometrue C_simpae).
    destruct (H_aux_Sometrue C_simpae) as [n H_ae].
    rewrite -> H_ae.
    rewrite -> (fold_unfold_simplify_ltr_aux_Literal n).
    reflexivity.

  - intros _.
    Check(completeness_of_simplify_aux ae).
    destruct (completeness_of_simplify_aux ae) as [_ H_aux_Somefalse].
    Check (H_aux_Somefalse C_simpae).
    rewrite -> (H_aux_Somefalse C_simpae).
    reflexivity.

  - intro H_absurd.
    discriminate H_absurd.
Qed.

(* ********** *)

(* Task
 2:
   Each of the following "optimizing" compilers exploits a semantic property of arithmetic expressions.
   Your task is to identify this property for each compiler.

   You should proceed in two separate ways:
   - take a "black box" approach and figure out what the compiler does by feeding it with appropriate source programs and then analyzing the corresponding target programs;
   - take a "white box" approach and figure out what the compiler does by reading its code.

   Unless you absolutely want to, no theorems and no proofs are required here, just examples and narrative clarity.
*)

(* Relevant quote:
   "It is not forbidden to think."
   -- Carmen
*)

(* For example, if the optimization is a transformation (e.g., simplifying "1 * e" into "e"),
   for source programs where the transformation has been done already (here, source programs with no occurrence of "1 * e"),
   then the optimizing compiler gives the same result as the standard compiler.
*)

(* ***** *)

(* Here is a worked-out example for compile_peculiar, which is defined just below. *)

Fixpoint compile_peculiar_aux (ae : arithmetic_expression) (a : list byte_code_instruction) : list byte_code_instruction :=
  match ae with
    Literal n =>
    PUSH n :: a
  | Name x =>
    LOOKUP x :: a
  | Plus ae1 ae2 =>
    compile_peculiar_aux ae2 (compile_peculiar_aux ae1 (ADD :: a))
  | Times ae1 ae2 =>
    compile_peculiar_aux ae2 (compile_peculiar_aux ae1 (MUL :: a))
  end.

Definition compile_peculiar (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_peculiar_aux ae nil)
  end.

(* Both the black-box approach and the white-box approach suggest that
   compile_peculiar commutes additions and multiplications.
   However, this commutation is not semantically correct for left-to-right evaluation,
   and therefore this optimizing compiler is incorrect.
*)

(* Counter-example: *)

Compute (let sp1 := Source_program (Plus (Name "x"%string) (Name "y"%string)) in
         let tp1 := compile_peculiar sp1 in
         (interpret_ltr sp1 nil, run_ltr tp1 nil)).

(* In words,
   interpreting sp1 yields Source_expressible_msg (Source_undeclared_name "x")
   whereas
   interpreting tp1 yields Target_expressible_msg (Target_undeclared_name "y"),
   which are not the same error messages. *)

(* This worked-out example illustrates
   that you also need to assess the correctness each optimizing compiler.
*)

(* ***** *)

(* nice stuff *)
Definition bci_eqb (bci1 bci2 : byte_code_instruction) : bool :=
  match bci1 with
  | PUSH n1 =>
      match bci2 with
      | PUSH n2 =>
          Nat.eqb n1 n2
      | _ =>
          false
      end
  | LOOKUP x1 =>
      match bci2 with
      | LOOKUP x2 =>
          String.eqb x1 x2
      | _ =>
          false
      end
  | ADD =>
      match bci2 with
      | ADD =>
          true
      | _ =>
          false
      end
  | MUL =>
      match bci2 with
      | MUL =>
          true
      | _ =>
          false
      end
  end.

Definition target_program_eqb (tp1 tp2 : target_program) : bool :=
  match tp1 with
  | Target_program bci1s =>
      match tp2 with
      | Target_program bci2s =>
          list_eqb byte_code_instruction bci_eqb bci1s bci2s
      end
  end.


Definition apply_candidate (candidate : source_program -> target_program)
  (ae : arithmetic_expression) :=
  candidate (Source_program ae).

Compute (apply_candidate compile_peculiar test_in_simplify_ltr_Literal).

Compute (apply_candidate compile_peculiar test_in_simplify_ltr_Name).

Compute (apply_candidate compile_peculiar test_in_simplify_ltr_Plus_C_C).

Compute (apply_candidate compile_peculiar test_in_simplify_ltr_Plus_C_NC).

Compute (apply_candidate compile_peculiar test_in_simplify_ltr_Plus_NC_C).

Compute (apply_candidate compile_peculiar test_in_simplify_ltr_Plus_NC_NC).

Compute (apply_candidate compile_peculiar test_in_simplify_ltr_Times_C_C).

Compute (apply_candidate compile_peculiar test_in_simplify_ltr_Times_C_NC).

Compute (apply_candidate compile_peculiar test_in_simplify_ltr_Times_NC_C).

Compute (apply_candidate compile_peculiar test_in_simplify_ltr_Times_NC_NC).

(* commuting diagram checker *)
Definition source_target_eqb (sev : source_expressible_value) (tev : target_expressible_value) : bool :=
  match sev with
  | Source_expressible_nat sn =>
      match tev with
      | Target_expressible_nat tn =>
          Nat.eqb sn tn
      | Target_expressible_msg tm =>
          false
      end
  | Source_expressible_msg (Source_undeclared_name sm) =>
      match tev with
      | Target_expressible_nat tn =>
          false
      | Target_expressible_msg (Target_undeclared_name tm) =>
          String.eqb sm tm
      | _ =>
          false
      end
  end.

Definition source_expressible_value_eqb (sev1 sev2 : source_expressible_value) : bool :=
  match sev1 with
  | Source_expressible_nat n1 =>
      match sev2 with
      | Source_expressible_nat n2 =>
          Nat.eqb n1 n2
      | Source_expressible_msg m2 =>
          false
      end
  | Source_expressible_msg (Source_undeclared_name s1) =>
      match sev2 with
      | Source_expressible_nat n2 =>
          false
      | Source_expressible_msg (Source_undeclared_name s2) =>
          String.eqb s1 s2
      end
  end.

Definition target_msg_eqb (tm1 tm2 : target_msg) : bool :=
  match tm1 with
  | Target_undeclared_name s1 =>
      match tm2 with
      | Target_undeclared_name s2 =>
          String.eqb s1 s2
      | _ =>
          false
      end
  | Target_stack_underflow bci1 =>
      match tm2 with
      | Target_stack_underflow bci2 =>
          bci_eqb bci1 bci2
      | _ =>
          false
      end
  | Target_stack_O =>
      match tm2 with
      | Target_stack_O =>
          true
      | _ =>
          false
      end
  | Target_stack_SS =>
      match tm2 with
      | Target_stack_SS =>
          true
      | _ =>
          false
      end
  end.

Definition target_expressible_value_eqb (tev1 tev2 : target_expressible_value) : bool :=
  match tev1 with
  | Target_expressible_nat n1 =>
      match tev2 with
      | Target_expressible_nat n2 =>
          Nat.eqb n1 n2
      | Target_expressible_msg tm2 =>
          false
      end
  | Target_expressible_msg tm1 =>
      match tev2 with
      | Target_expressible_nat n2 =>
          false
      | Target_expressible_msg tm2 =>
          target_msg_eqb tm1 tm2
      end
  end.

Definition candidate_optimizer_behaves_as_compile_ltr_with_test_case (candidate : source_program -> target_program) (ae : arithmetic_expression) : bool :=
  target_program_eqb (apply_candidate compile_ltr ae) (apply_candidate candidate ae).

Definition decompile_candidate_optimizer_and_compare (candidate : source_program -> target_program) (ae : arithmetic_expression) : (source_program * source_program) :=
  match Magritte_run_ltr (compile_ltr (Source_program ae)) with
  | Some ae_vanilla =>
      match Magritte_run_ltr (candidate (Source_program ae)) with
      | Some ae_not_vanilla =>
          (ae_vanilla, ae_not_vanilla)
      | None =>
          (ae_vanilla, Source_program (Name "Should never occur"%string))
      end
  | None =>
      (Source_program (Name "Should never occur"%string), Source_program (Name "Should never occur"%string))
  end.

Definition candidate_optimizer_preserves_correctness_of_run (candidate : source_program -> target_program) (ae : arithmetic_expression) : bool :=
  source_target_eqb (interpret_ltr (Source_program ae) nil) (run_ltr (candidate (Source_program ae)) nil).

(* ***** test cases ***** *)

Definition test_ae1 : arithmetic_expression :=
  Plus
    (Literal 1)
    (Literal 10).

Definition test_ae2 : arithmetic_expression :=
  Plus
    (Literal 1)
    (Name "x"%string).

Definition test_ae3 : arithmetic_expression :=
  Times
    (Literal 2)
    (Literal 3).

Definition test_ae4 : arithmetic_expression :=
  Times
    (Literal 2)
    (Name "y"%string).

Definition test_ae5 : arithmetic_expression :=
  Plus
    (Plus
       (Literal 1)
       (Literal 2))
    (Plus
       (Literal 3)
       (Name "x"%string)).

Definition test_ae6 : arithmetic_expression :=
  Plus
    (Times
       (Literal 2)
       (Literal 3))
    (Name "z"%string).

Definition test_ae7 : arithmetic_expression :=
  Plus
    (Name "x"%string)
    (Name "y"%string).

Definition test_ae8 : arithmetic_expression :=
  Times
    (Name "x"%string)
    (Name "y"%string).

Definition test_ae9 : arithmetic_expression :=
  Plus
    (Plus
       (Literal 2)
       (Name "x"%string))
    (Literal 3).

Definition test_ae10 : arithmetic_expression :=
  Times
    (Times
       (Literal 4)
       (Name "y"%string))
    (Literal 5).

Definition test_ae11 : arithmetic_expression :=
  Plus
    (Times
       (Literal 2)
       (Name "a"%string))
    (Plus
       (Times
          (Literal 3)
          (Name "b"%string))
       (Literal 5)).

Definition test_ae12 : arithmetic_expression :=
  Times
    (Plus
       (Literal 1)
       (Name "x"%string))
    (Plus
       (Name "y"%string)
       (Literal 2)).

Definition test_ae13 : arithmetic_expression :=
  (Plus
     (Plus
        (Literal 1)
        (Literal 2))
     (Plus
        (Name "x"%string)
        (Literal 3))).

Definition test_ae14 : arithmetic_expression :=
  (Times
     (Times
        (Literal 1)
        (Literal 2))
     (Times
        (Name "x"%string)
        (Literal 3))).

Definition test_ae15 : arithmetic_expression :=
  Plus
    (Plus
       (Literal 1)
       (Literal 2))
    (Times
       (Literal 3)
       (Name "x"%string)).

Definition test_ae16 : arithmetic_expression :=
  Plus
    (Plus
       (Literal 2)
        (Plus
           (Literal 1)
           (Literal 2)))
    (Times
       (Literal 3)
       (Name "x"%string)).

Definition test_ae_Plus_edge01 : arithmetic_expression :=
  Plus
    (Literal 0)
    (Literal 1).

Definition test_ae_Plus_edge10 : arithmetic_expression :=
  Plus
    (Literal 1)
    (Literal 0).

Definition test_ae_Plus_edge0x : arithmetic_expression :=
  Plus
    (Literal 0)
    (Name "x"%string).

Definition test_ae_Plus_edgex0 : arithmetic_expression :=
  Plus
    (Name "x"%string)
    (Literal 0).

Definition test_ae_Times_edge01 : arithmetic_expression :=
  Times
    (Literal 0)
    (Literal 1).

Definition test_ae_Times_edge10 : arithmetic_expression :=
  Times
    (Literal 1)
    (Literal 0).

Definition test_ae_Times_edge0x : arithmetic_expression :=
  Times
    (Literal 0)
    (Name "x"%string).

Definition test_ae_Times_edgex0 : arithmetic_expression :=
  Times
    (Name "x"%string)
    (Literal 0).

Definition test_ae_Times_edge12 : arithmetic_expression :=
  Times
    (Literal 1)
    (Literal 2).

Definition test_ae_Times_edge21 : arithmetic_expression :=
  Times
    (Literal 2)
    (Literal 1).

Definition test_ae_Times_edge1x : arithmetic_expression :=
  Times
    (Literal 1)
    (Name "x"%string).

Definition test_ae_Times_edgex1 : arithmetic_expression :=
  Times
    (Name "x"%string)
    (Literal 1).

(* ***** *)

(* compile_bizarre *)

Fixpoint compile_bizarre_aux_Plus
  (ae : arithmetic_expression)
  (k : list byte_code_instruction -> list byte_code_instruction -> list byte_code_instruction)
  (a : list byte_code_instruction) : list byte_code_instruction :=
  match ae with
    Literal n =>
    k (PUSH n :: nil) a
  | Name x =>
    k (LOOKUP x :: nil) a
  | Plus ae1 ae2 =>
    compile_bizarre_aux_Plus ae1 (fun bcis1 a1 => bcis1 ++ compile_bizarre_aux_Plus ae2 k a1) (ADD :: a)
  | Times ae1 ae2 =>
    k (compile_bizarre_aux_Times ae1 (fun bcis1 a1 => bcis1 ++ compile_bizarre_aux_Times ae2 (fun bcis2 a2 => bcis2 ++ a2) a1) (MUL :: nil)) a
  end
with compile_bizarre_aux_Times
       (ae : arithmetic_expression)
       (k : list byte_code_instruction -> list byte_code_instruction -> list byte_code_instruction)
       (a : list byte_code_instruction) : list byte_code_instruction :=
       match ae with
         Literal n =>
         k (PUSH n :: nil) a
       | Name x =>
         k (LOOKUP x :: nil) a
       | Plus ae1 ae2 =>
         k (compile_bizarre_aux_Plus ae1 (fun bcis1 a1 => bcis1 ++ compile_bizarre_aux_Plus ae2 (fun bcis2 a2 => bcis2 ++ a2) a1) (ADD :: nil)) a
       | Times ae1 ae2 =>
         compile_bizarre_aux_Times ae1 (fun bcis1 a1 => bcis1 ++ compile_bizarre_aux_Times ae2 k a1) (MUL :: a)
       end.

Definition compile_bizarre_aux (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
    Literal n =>
    PUSH n :: nil
  | Name x =>
    LOOKUP x :: nil
  | Plus ae1 ae2 =>
    compile_bizarre_aux_Plus ae1 (fun bcis1 a1 => bcis1 ++ compile_bizarre_aux_Plus ae2 (fun bcis2 a2 => bcis2 ++ a2) a1) (ADD :: nil)
  | Times ae1 ae2 =>
    compile_bizarre_aux_Times ae1 (fun bcis1 a1 => bcis1 ++ compile_bizarre_aux_Times ae2 (fun bcis2 ae2 => bcis2 ++ ae2) a1) (MUL :: nil)
  end.

Definition compile_bizarre (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_bizarre_aux ae)
  end.

(* VietAnh1010's white-box observations:

   This compiler is indeed bizarre. Continuation and accumulator at the
   same time?!

   The aux functions for Plus and Times look somewhat similar to
   `super_refactor` - it's likely that they combine `super_refactor`
   with the compilation process, re-associating both Plus and Times to the right.

   Also, it seems like the accumulator is to accumulate "the
   instructions at the end" - those instructions will eventually be
   appended to the list of instructions:

   `(fun bcis1 a1 => bcis1 ++ ... (fun bcis2 a2 => bcis2 ++ a2) a1)`:
   bcis1 ... bcis2 ... a2 ... a1.

   Let's investigate `compile_bizarre_aux_Plus`. We can look at Times
   case first - the logic is easy: we compile the Times expression
   using the sibling `compile_bizarre_aux_Times`, and then prepend the
   instructions of that expression before the accumulator, using `k`.

   Now the harder case: Plus. The continuation to be applied after
   compiling ae1 is `fun bcis1 a1 => bcis1 ++ ...`. As we encounter
   more Plus nodes, those continuations will accumulate, and we have
   bcis1 ++ bcis2 ++ ... ++ bcisn ++ ..., effectively we "flatten"
   the Plus, using right associativity of Plus (this is similar to
   how `super_refactor` modifies the expression tree). At runtime,
   we will have maximal stack usage with this transformation!

   The same arguement should also work for Times.

   Therefore, the compiler returns correct results, but the code
   emitted by the compiler with maximize the stack usage of the program
   (which, should be called as a "de-optimization"?).

   In conclusion, compiler_bizarre reassociates both Plus and Times to
   the right, its "optimization" is what super_refactor_right achieves.

   "compiler_bizarre is super_refactor_right with a (spurious)
   accumulator."
 *)

(* Black Box testing - part 1: checking how compile bizarre is different from compile ltr *)

Definition compile_bizarre_behaves_as_compile_ltr_with_test_case (ae : arithmetic_expression) : bool :=
  candidate_optimizer_behaves_as_compile_ltr_with_test_case compile_bizarre ae.

Definition compile_bizarre_preserves_correctness_of_run_with_test_case (ae : arithmetic_expression) : bool :=
  candidate_optimizer_preserves_correctness_of_run compile_bizarre ae.

Definition decompile_compile_bizarre_ae_and_compare (ae : arithmetic_expression) : (source_program * source_program) :=
  decompile_candidate_optimizer_and_compare compile_bizarre ae.

Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae1).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae2).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae3).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae4).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae5).
(* test_ae5 does not compile the same way *)

Compute (arithmetic_expression_eqb
           test_ae5
           (Plus
              (Plus
                 (Literal 1)
                 (Literal 2))
              (Plus
                 (Literal 3)
                 (Name "x"%string)))).

Compute target_program_eqb
  (apply_candidate compile_ltr test_ae5)
  (Target_program
     (PUSH 1
        :: PUSH 2
        :: ADD
        :: PUSH 3
        :: LOOKUP "x"
        :: ADD
        :: ADD
        :: nil)).

Compute target_program_eqb
  (apply_candidate compile_bizarre test_ae5)
  (Target_program
     (PUSH 1
        :: PUSH 2
        :: PUSH 3
        :: LOOKUP "x"
        :: ADD
        :: ADD
        :: ADD
        :: nil)).

Compute (decompile_compile_bizarre_ae_and_compare
           test_ae5).

Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae6).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae7).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae8).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae9).
(* test_ae9 does not compile the same way *)

Compute (arithmetic_expression_eqb
           test_ae9
           (Plus
              (Plus
                 (Literal 2)
                 (Name "x"%string))
              (Literal 3))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae9)
           (Target_program
              (PUSH 2
                 :: LOOKUP "x"
                 :: ADD
                 :: PUSH 3
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_bizarre test_ae9)
         (Target_program
            (PUSH 2
               :: LOOKUP "x"
               :: PUSH 3
               :: ADD
               :: ADD
               :: nil))).

Compute (decompile_compile_bizarre_ae_and_compare
           test_ae9).

Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae10).
(* test_ae10 does not compile the same way *)

Compute (arithmetic_expression_eqb
           (test_ae10)
           (Times
              (Times
                 (Literal 4)
                 (Name "y"%string))
              (Literal 5))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae10)
           (Target_program
              (PUSH 4
                 :: LOOKUP "y"
                 :: MUL
                 :: PUSH 5
                 :: MUL
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_bizarre test_ae10)
           (Target_program
              (PUSH 4
                 :: LOOKUP "y"
                 :: PUSH 5
                 :: MUL
                 :: MUL
                 :: nil))).

Compute (decompile_compile_bizarre_ae_and_compare
           test_ae10).

Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae11).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae12).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae13).
(* test_ae13 does not compile the same way *)

Compute (arithmetic_expression_eqb
           test_ae13
           (Plus
              (Plus
                 (Literal 1)
                 (Literal 2))
              (Plus
                 (Name "x"%string)
                 (Literal 3)))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae13)
           (Target_program
              (PUSH 1
                 :: PUSH 2
                 :: ADD
                 :: LOOKUP "x"
                 :: PUSH 3
                 :: ADD
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_bizarre test_ae13)
           (Target_program
              (PUSH 1
                 :: PUSH 2
                 :: LOOKUP "x"
                 :: PUSH 3
                 :: ADD
                 :: ADD
                 :: ADD
                 :: nil))).

Compute (decompile_compile_bizarre_ae_and_compare
           test_ae13).

Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae14).
(* test_ae14 does not compile the same way *)

Compute (arithmetic_expression_eqb
           test_ae14
           (Times
              (Times
                 (Literal 1)
                 (Literal 2))
              (Times
                 (Name "x"%string)
                 (Literal 3)))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae14)
           (Target_program
              (PUSH 1
                 :: PUSH 2
                 :: MUL
                 :: LOOKUP "x"
                 :: PUSH 3
                 :: MUL
                 :: MUL
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_bizarre test_ae14)
           (Target_program
              (PUSH 1
                 :: PUSH 2
                 :: LOOKUP "x"
                 :: PUSH 3
                 :: MUL
                 :: MUL
                 :: MUL
                 :: nil))).

Compute (decompile_compile_bizarre_ae_and_compare
           test_ae14).

Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae15).
(* test_ae15 does not compute the same way *)

Compute (arithmetic_expression_eqb
           test_ae15
           (Plus
              (Plus
                 (Literal 1)
                 (Literal 2))
              (Times
                 (Literal 3)
                 (Name "x"%string)))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae15)
           (Target_program
              (PUSH 1
                 :: PUSH 2
                 :: ADD
                 :: PUSH 3
                 :: LOOKUP "x"
                 :: MUL
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_bizarre test_ae15)
           (Target_program
              (PUSH 1
                 :: PUSH 2
                 :: PUSH 3
                 :: LOOKUP "x"
                 :: MUL
                 :: ADD
                 :: ADD
                 :: nil))).

Compute (decompile_compile_bizarre_ae_and_compare
           test_ae15).

Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae16).
(* test_ae16 does not compile the same way *)

Compute (arithmetic_expression_eqb
           test_ae16
           (Plus
              (Plus
                 (Literal 2)
                 (Plus
                    (Literal 1)
                    (Literal 2)))
              (Times
                 (Literal 3)
                 (Name "x"%string)))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae16)
           (Target_program
              (PUSH 2
                 :: PUSH 1
                 :: PUSH 2
                 :: ADD
                 :: ADD
                 :: PUSH 3
                 :: LOOKUP "x"
                 :: MUL
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_bizarre test_ae16)
           (Target_program
              (PUSH 2
                 :: PUSH 1
                 :: PUSH 2
                 :: PUSH 3
                 :: LOOKUP "x"
                 :: MUL
                 :: ADD
                 :: ADD
                 :: ADD
                 :: nil))).

Compute (decompile_compile_bizarre_ae_and_compare
           test_ae16).

Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge01).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge10).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge0x).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae_Plus_edgex0).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae_Times_edge01).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae_Times_edge10).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae_Times_edge0x).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae_Times_edgex0).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae_Times_edge12).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae_Times_edge21).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae_Times_edge1x).
Compute (compile_bizarre_behaves_as_compile_ltr_with_test_case test_ae_Times_edgex1).

(* Black Box testing - part 2: checking if compile bizarre preserves correctness *)

Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae1).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae2).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae3).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae4).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae5).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae6).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae7).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae8).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae9).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae10).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae11).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae12).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae13).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae14).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae15).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae16).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae_Plus_edge01).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae_Plus_edge10).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae_Plus_edge0x).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae_Plus_edgex0).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae_Times_edge01).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae_Times_edge10).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae_Times_edge0x).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae_Times_edgex0).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae_Times_edge12).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae_Times_edge21).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae_Times_edge1x).
Compute (compile_bizarre_preserves_correctness_of_run_with_test_case test_ae_Times_edgex1).

(* all good *)

(* Black-box observations *)
(* compile_bizarre does not match compile_ltr for test_ae5, 9, 10, 13, 14, 15, 16 *)

(* what compile_ltr outputs -> what compile_bizarre outputs
ae5 :
(1 + 2) + (3 + x) -> 1  + (2 + (3 + x))

ae9 :
(2 + x) + 3 -> 2 + (x + 3)

ae10 :
(4 * y) * 5 -> 4 * (y * 5)

ae13:
(1 + 2) + (x + 3) -> 1 + (2 + (x + 3))

ae14:
(1 * 2) * (x * 3) -> 1 * (2 * (x * 3))

ae15:
(1 + 2) + (3 * x) -> 1 + (2 + (3 * x))

ae16:
(2 + (1 + 2)) + (3 * x) -> 2 + (1 + (2 + (3 * x)))

What if?
((2 * 3) + 5) + (7 * 11)) -> ?

Expected: (2 * 3) + (5 + (7 * 11))

*)

Definition test_ae_bizarre1 : arithmetic_expression :=
  Plus
    (Plus
       (Times
          (Literal 2)
          (Literal 3))
       (Literal 5))
    (Times
       (Literal 7)
       (Literal 11)).

Definition expected_tp_bizarre1 : target_program :=
  Target_program
    (PUSH 2
       :: PUSH 3
       :: MUL
       :: PUSH 5
       :: PUSH 7
       :: PUSH 11
       :: MUL
       :: ADD
       :: ADD
       :: nil).

Compute (target_program_eqb
           (apply_candidate compile_bizarre test_ae_bizarre1)
           expected_tp_bizarre1).

Compute (decompile_compile_bizarre_ae_and_compare
           test_ae_bizarre1).
(*
What if?
((2 * (3 + 4)) + 5) + (7 * 11) -> ?

Expected: (2 * (3 + 4)) + (5 + (7 * 11))
 *)

Definition test_ae_bizarre2 : arithmetic_expression :=
  Plus
    (Plus
       (Times
          (Literal 2)
          (Plus
             (Literal 3)
             (Literal 4)))
          (Literal 5))
    (Times
       (Literal 7)
       (Literal 11)).

Compute (decompile_compile_bizarre_ae_and_compare
           test_ae_bizarre2).

(* Black-box findings:

From our testing, compile_bizarre re-associates all consecutive applications of those operations to the right. This results in the largest possible data stack while maintaining correctness. Thus it actually un-optimizes the byte-code. *)

(* ***** *)

(* compile_quaint *)

Fixpoint compile_quaint_aux
  (ae : arithmetic_expression)
  (k : list byte_code_instruction -> list byte_code_instruction) : list byte_code_instruction :=
  match ae with
    Literal n =>
    k (PUSH n :: nil)
  | Name x =>
    k (LOOKUP x :: nil)
  | Plus ae1 ae2 =>
    compile_quaint_aux ae1 k ++ compile_quaint_aux ae2 k ++ ADD :: nil
  | Times ae1 ae2 =>
    compile_quaint_aux ae1 (fun bcis1 => compile_quaint_aux ae2 (fun bcis2 => k (bcis1 ++ bcis2 ++ MUL :: nil)))
  end.

Definition compile_quaint (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_quaint_aux ae (fun bcis => bcis))
  end.

(* VietAnh1010's white-box observations:

   This compiler looks quite similar to the standard CPS implementation.
   The Plus case stands out: the continuation is passed into both
   the left and the right recursive calls, without any modification.

   Consider possible values of the continuation, it's either:
   - The identity function.
   - fun bcis1 => ... (calculate the RHS, and multiply, and continue)
   - fun bcis2 => ... (the LHS is calculated. Multiply, and continue)

   If the continuation is the identity function, then
   `compile_quaint_aux ae k` are just instructions to compute ae.

   If the continuation is `fun bcis1 => ...`, then
   `compile_quaint_aux ae1 k ++ compile_quaint_aux ae2 k ++ ADD` are
   instructions that first compute ae1 * RHS, then ae2 * RHS, then
   add them together. It looks like the compiler exploits
   distributivity on the left: ((a + b) * c = ac + bc).

   If the continuation is `fun bcis2 => ...`, then
   `compile_quaint_aux ae1 k ++ compile_quaint_aux ae2 k ++ ADD` are
   instructions that first compute LHS * ae1, then LHS * ae2, then
   add them together. The compiler tries to exploit distributivity,
   on the right (a * (b + c) = ab + ac).

   Harking back to our study of observational equivalence in Week 01,
   we remember that distributivity on the left is not valid in
   our arithmetic expressions, due to possibility of errors arising
   in different orders:
   - (a + b) * c => order: a b c.
   - ac + bc => order a c b c.

   Let's consider an example: suppose running instructions for b cause
   an error due to a missing name "b", and running instructions for c
   causes an error due to another missing name "c", then the final
   results are different.

   Therefore, this compiler returns incorrect results.
 *)

(* Counter example *)
Compute (
    let ae :=
      (Times
         (Plus
            (Literal 1)
            (Name "b"%string))
         (Name "c"%string))
    in
    let sp := Source_program ae in
    let tp_correct := compile_ltr sp in
    let tp_incorrect := compile_quaint sp in
    (run_ltr tp_correct nil, run_ltr tp_incorrect nil)).

(* Black Box testing - part 1: checking how compile quaint is different from compile ltr *)

Definition compile_quaint_behaves_as_compile_ltr_with_test_case (ae : arithmetic_expression) :=
  candidate_optimizer_behaves_as_compile_ltr_with_test_case compile_quaint ae.

Definition decompile_compile_quaint_and_compare (ae : arithmetic_expression) : (source_program * source_program) :=
  decompile_candidate_optimizer_and_compare compile_quaint ae.

Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae1).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae2).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae3).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae4).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae5).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae6).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae7).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae8).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae9).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae10).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae11).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae12).
(* test_ae12 does not compile the same way *)

Compute (arithmetic_expression_eqb
           test_ae12
           (Times
              (Plus
                 (Literal 1)
                 (Name "x"%string))
              (Plus
                 (Name "y"%string)
                 (Literal 2)))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae12)
           (Target_program
              (PUSH 1
                 :: LOOKUP "x"
                 :: ADD
                 :: LOOKUP "y"
                 :: PUSH 2
                 :: ADD
                 :: MUL
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_quaint test_ae12)
           (Target_program
              (PUSH 1
                 :: LOOKUP "y"
                 :: MUL
                 :: PUSH 1
                 :: PUSH 2
                 :: MUL
                 :: ADD
                 :: LOOKUP "x"
                 :: LOOKUP "y"
                 :: MUL
                 :: LOOKUP "x"
                 :: PUSH 2
                 :: MUL
                 :: ADD
                 :: ADD
                 :: nil))).

Compute (decompile_compile_quaint_and_compare test_ae12).

Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae13).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae14).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae15).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae16).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge01).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge10).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge0x).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae_Plus_edgex0).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae_Times_edge01).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae_Times_edge10).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae_Times_edge0x).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae_Times_edgex0).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae_Times_edge12).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae_Times_edge21).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae_Times_edge1x).
Compute (compile_quaint_behaves_as_compile_ltr_with_test_case test_ae_Times_edgex1).

(* Black Box testing - part 2: checking if compile quaint preserves correctness *)

Definition compile_quaint_preserves_correctness_of_run_with_test_case (ae : arithmetic_expression) : bool :=
  candidate_optimizer_preserves_correctness_of_run compile_quaint ae.

Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae1).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae2).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae3).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae4).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae5).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae6).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae7).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae8).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae9).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae10).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae11).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae12).
(* test_ae12 results in a different value when run after being compiled with compile_quaint *)

Compute (target_expressible_value_eqb
           (run_ltr (apply_candidate compile_ltr test_ae12) nil)
           (Target_expressible_msg
              (Target_undeclared_name "x"))).

Compute (target_expressible_value_eqb
           (run_ltr (apply_candidate compile_quaint test_ae12) nil)
           (Target_expressible_msg
              (Target_undeclared_name "y"))).

Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae13).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae14).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae15).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae16).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae_Plus_edge01).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae_Plus_edge10).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae_Plus_edge0x).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae_Plus_edgex0).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae_Times_edge01).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae_Times_edge10).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae_Times_edge0x).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae_Times_edgex0).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae_Times_edge12).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae_Times_edge21).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae_Times_edge1x).
Compute (compile_quaint_preserves_correctness_of_run_with_test_case test_ae_Times_edgex1).

(* black-box observations *)

(* The compiler gave a different target program in ae12:

(1 + x) * (y + 2) -> (1 * y) + (1 * 2) + (x * y) + (x * 2)

which looks a lot like distribution of multiplication over addition on the left.

To check:

2 * (3 + 5) -> ? Expected: (2 * 3) + (2 * 5)

We should also check if it distributes if the mul is on the right

(3 + 5) * 2 -> ? Expected: (3 * 2) + (5 * 2) if distr_r, (3 + 5) * 2 otherwise

*)

Definition test_ae_quaint1 : arithmetic_expression :=
  Times
    (Literal 2)
    (Plus
       (Literal 3)
       (Literal 5)).

Definition expected_ae_quaint1 : target_program :=
  Target_program
    (PUSH 2
       :: PUSH 3
       :: MUL
       :: PUSH 2
       :: PUSH 5
       :: MUL
       :: ADD
       :: nil).

Compute (target_program_eqb
           (apply_candidate compile_quaint test_ae_quaint1)
           expected_ae_quaint1).

Compute (decompile_compile_quaint_and_compare test_ae_quaint1).

Definition test_ae_quaint2: arithmetic_expression :=
  Times
    (Plus
       (Literal 3)
       (Literal 5))
    (Literal 2).

Definition expected_ae_quaint2_distr_r : target_program :=
  Target_program
    (PUSH 3
       :: PUSH 2
       :: MUL
       :: PUSH 5
       :: PUSH 2
       :: MUL
       :: ADD
       :: nil).

Definition expected_ae_quaint2_otherwise : target_program :=
  Target_program
    (PUSH 3
       :: PUSH 5
       :: ADD
       :: PUSH 2
       :: MUL
       :: nil).

Compute (target_program_eqb
           (apply_candidate compile_quaint test_ae_quaint2)
           expected_ae_quaint2_distr_r).

Compute (negb
           (target_program_eqb
              (apply_candidate compile_quaint test_ae_quaint2)
              expected_ae_quaint2_otherwise)).

Compute (decompile_compile_quaint_and_compare test_ae_quaint2).
Compute (Magritte_run_ltr expected_ae_quaint2_distr_r).
Compute (Magritte_run_ltr expected_ae_quaint2_otherwise).

(* So compile_quaint does is to distribute multiplication over addition. This results in the optimizer returning incorrect results due to the order in which expressions are evaluated are different than the original order.

Example:
test_ae12 := (1 + x) * (y + 2) -> (1 * y) + (1 * 2) + (x * y) + (x * 2)

When the compiled version of the arithmetic expression (compiled with compile_ltr) is run left-to-right in an environment where both "x" and "y" are not declared, the result is that "x" is undeclared,

whereas

when the compiled version of the arithmetic expression (compiled with compile_quaint) is run left-to-rgith in an environment where both "x" and "y" are not declared, the result is that "y" is undeclared.

The result is still incorect even if we ran the compiled versions right-to-left in an enviroment where both "x" and "y" are not declared. The result of running the compiled version using compile_ltr right-to-left is that "y" is undeclared, whereas the result of running the compiled version using compile_quaint is that "x" is undeclared.

Furthermore, the compiler cannot be considered and optimizer because it also does not optimize the bite code by reducing the max stack size. Thus, not only the program is inefficient, but it is also incorrect. *)

(* ***** *)

(* compile_curious *)

Fixpoint compile_curious_aux
  (ae : arithmetic_expression)
  (k : list byte_code_instruction -> list byte_code_instruction) : list byte_code_instruction :=
  match ae with
    Literal n =>
    k (PUSH n :: nil)
  | Name x =>
    k (LOOKUP x :: nil)
  | Plus ae1 ae2 =>
    compile_curious_aux ae1 k ++ compile_curious_aux ae2 k ++ ADD :: nil
  | Times ae1 ae2 =>
    compile_curious_aux ae2 (fun bcis2 => compile_curious_aux ae1 (fun bcis1 => k (bcis1 ++ bcis2 ++ MUL :: nil)))
  end.

Definition compile_curious (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_curious_aux ae (fun bcis => bcis))
  end.

(* VietAnh1010's white-box observations:

   This compiler looks ... extremely similar to `compile_quant`.
   Took me around 15 seconds to realize the differences
   (bcis1 vs bcis2).

   The main difference is that, in the Times case, ae2 is compiled
   first before ae1 is compiled. Well, the compiler still relies on
   distributivity on the left, and that property does not hold...

   Therefore, this compiler is faulty as well. Let's try the same
   counter as with `compile_quant`.
 *)

(* Counter example *)
Compute (
    let ae :=
      (Times
         (Plus
            (Literal 1)
            (Name "b"%string))
         (Name "c"%string))
    in
    let sp := Source_program ae in
    let tp_correct := compile_ltr sp in
    let tp_incorrect := compile_curious sp in
    (run_ltr tp_correct nil, run_ltr tp_incorrect nil)).

(* And voila (emacs does not accept the diacritic TT), the counter
   example still works!
 *)

(* TODO: refactor above as a boolean-returning test *)

(* Black Box testing - part 1: checking how compile curious is different from compile ltr *)

Definition compile_curious_behaves_as_compile_ltr_with_test_case (ae : arithmetic_expression) : bool :=
  candidate_optimizer_behaves_as_compile_ltr_with_test_case compile_curious ae.

Definition decompile_compile_curious_and_compare (ae : arithmetic_expression) : (source_program * source_program) :=
  decompile_candidate_optimizer_and_compare compile_curious ae.

Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae1).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae2).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae3).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae4).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae5).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae6).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae7).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae8).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae9).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae10).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae11).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae12).
(* test_ae12 does not compile the same way *)

Compute (arithmetic_expression_eqb
           test_ae12
           (Times
              (Plus
                 (Literal 1)
                 (Name "x"%string))
              (Plus
                 (Name "y"%string)
                 (Literal 2)))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae12)
           (Target_program
              (PUSH 1
                 :: LOOKUP "x"
                 :: ADD
                 :: LOOKUP "y"
                 :: PUSH 2
                 :: ADD
                 :: MUL
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_curious test_ae12)
           (Target_program
              (PUSH 1
                 :: LOOKUP "y"
                 :: MUL
                 :: LOOKUP "x"
                 :: LOOKUP "y"
                 :: MUL
                 :: ADD
                 :: PUSH 1
                 :: PUSH 2
                 :: MUL
                 :: LOOKUP "x"
                 :: PUSH 2
                 :: MUL
                 :: ADD
                 :: ADD
                 :: nil))).

Compute (decompile_compile_curious_and_compare test_ae12).

Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae13).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae14).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae15).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae16).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge01).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge10).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge0x).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae_Plus_edgex0).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae_Times_edge01).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae_Times_edge10).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae_Times_edge0x).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae_Times_edgex0).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae_Times_edge12).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae_Times_edge21).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae_Times_edge1x).
Compute (compile_curious_behaves_as_compile_ltr_with_test_case test_ae_Times_edgex1).

(* Black Box testing - part 2: checking if compile curious preserves correctness *)

Definition compile_curious_preserves_correctness_of_run_with_test_case (ae : arithmetic_expression) : bool :=
  candidate_optimizer_preserves_correctness_of_run compile_curious ae.

Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae1).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae2).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae3).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae4).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae5).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae6).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae7).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae8).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae9).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae10).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae11).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae12).
(* test_ae12 results in a different value when run after being compiled with compile_curious *)

Compute (target_expressible_value_eqb
           (run_ltr (apply_candidate compile_ltr test_ae12) nil)
           (Target_expressible_msg
              (Target_undeclared_name "x"))).

Compute (target_expressible_value_eqb
           (run_ltr (apply_candidate compile_curious test_ae12) nil)
           (Target_expressible_msg
              (Target_undeclared_name "y"))).

Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae13).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae14).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae15).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae16).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae_Plus_edge01).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae_Plus_edge10).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae_Plus_edge0x).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae_Plus_edgex0).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae_Times_edge01).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae_Times_edge10).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae_Times_edge0x).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae_Times_edgex0).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae_Times_edge12).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae_Times_edge21).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae_Times_edge1x).
Compute (compile_curious_preserves_correctness_of_run_with_test_case test_ae_Times_edgex1).

(* Black-box observations *)

(* for test_ae12:

(1 + x) * (y + 2) -> ((1 * y) + (x * y)) + ((1 * 2) + (x * 2))

which looks a lot like distributivity, but slightly different from quaint, in that the right-distributivity is prioritized before left distributivity. In other words, curious does

(1 + x) * (y + 2)
-> ((1 + x) * y) + ((1 + x) * 2)
-> ((1 * y) + (x * y)) + ((1 * 2) + (x * 2))

while quaint does

(1 + x) * (y + 2)
-> (1 * (y + 2)) + (x * (y + 2))
-> ((1 * y) + (1 * 2)) + ((x * y) + (x * 2))

For good measure, let's test the same

2 * (3 + 5) -> ? Expected : (2 * 3) + (2 * 5)
(3 * 5) + 2 -> ? Expected : (3 * 2) + (5 * 2)

 *)

Definition test_ae_curious1 : arithmetic_expression :=
  Times
    (Literal 2)
    (Plus
       (Literal 3)
       (Literal 5)).

Definition expected_ae_curious1 : target_program :=
  Target_program
    (PUSH 2
       :: PUSH 3
       :: MUL
       :: PUSH 2
       :: PUSH 5
       :: MUL
       :: ADD
       :: nil).

Compute (target_program_eqb
           (apply_candidate compile_curious test_ae_curious1)
           expected_ae_curious1).

Compute (decompile_compile_curious_and_compare test_ae_curious1).

Definition test_ae_curious2 : arithmetic_expression :=
  Times
    (Plus
       (Literal 3)
       (Literal 5))
    (Literal 2).

Definition expected_ae_curious2 : target_program :=
  Target_program
    (PUSH 3
       :: PUSH 2
       :: MUL
       :: PUSH 5
       :: PUSH 2
       :: MUL
       :: ADD
       :: nil).

Compute (target_program_eqb
           (apply_candidate compile_curious test_ae_curious2)
           expected_ae_curious2).

(* According to black-box testing, compile_curious just applies distributivity of multiplication over addition.

The main difference between compile_curious and compile_quaint is how it orders distributivity in the presence of both left and right distributivity.

However, this still means, as shown in test_ae12, that the compiler is incorrect, as it introduces a different evaluation order from compile_ltr, which produces different errors if undefined names are looked up on the environment *)

(* ***** *)

(* compile_surprising *)

Fixpoint compile_surprising_aux
  (ae : arithmetic_expression)
  (k0 k1 : unit -> list byte_code_instruction)
  (k : list byte_code_instruction -> list byte_code_instruction)
  : list byte_code_instruction :=
  match ae with
    Literal 0 =>
    k0 tt
  | Literal 1 =>
    k1 tt
  | Literal n =>
    k (PUSH n :: nil)
  | Name x =>
    k (LOOKUP x :: nil)
  | Plus ae1 ae2 =>
    compile_surprising_aux ae1
      (fun _ => compile_surprising_aux ae2 k0 k1 k)
      (fun _ => compile_surprising_aux ae2
                  k1
                  (fun _ => k (PUSH 1 :: PUSH 1 :: ADD :: nil))
                  (fun bcis2 => k (PUSH 1 :: bcis2 ++ ADD :: nil)))
      (fun bcis1 => compile_surprising_aux ae2
                      (fun _ => k bcis1)
                      (fun _ => k (bcis1 ++ PUSH 1 :: ADD :: nil))
                      (fun bcis2 => k (bcis1 ++ bcis2 ++ ADD :: nil)))
  | Times ae1 ae2 =>
    compile_surprising_aux ae1
      k0
      (fun _ => compile_surprising_aux ae2 k0 k1 k)
      (fun bcis1 => compile_surprising_aux ae2
                      k0
                      (fun _ => k bcis1)
                      (fun bcis2 => k (bcis1 ++ bcis2 ++ MUL :: nil)))
  end.

Definition compile_surprising (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_surprising_aux ae (fun _ => PUSH 0 :: nil) (fun _ => PUSH 1 :: nil) (fun bcis => bcis))
  end.

(* VietAnh1010's white-box observations:

   NOTE: I completely missed this compiler in my first pass.
   This is the white-box observations AFTER I have worked on
   `compile_unexpected` - this compiler is quite similar to that
   other compiler. Anyway, here is the observations:

   The function is in CPS, with three continuations:

   k0: what to do when the result of the compilation is 0.
   k1: what to do when the result of the compilation is 1.
   k: what to do when none of the above holds.

   In Plus case, if ae1 compiles to 0, then we only retain the
   instructions of ae2 (all continuations are unchaged). If ae1
   compiles to 1, then we compiles ae2, if ae2 compiles to 0 we will
   continue with 1, otherwise we push the instructions for ae1, ae2,
   ADD and continue with k. And similar, for the last case of Plus.

   So for Plus, the compiler optimizes addtion with 0, both on the left
   and on the right.

   In Times case, if ae1 compiles to 0, then we DO NOT compile ae2,
   and instead immediately continue with 0. If ae1 compiles to 1,
   we only retain the instructions of ae2. Otherwise, we apply
   the same logic symmetrically on ae2.

   In general, for Times, the compiler optimizes multiplication with
   0 and 1, both on the left and on the right.

   So overall, the compiler:
   1. Eliminate addition with 0.
   2. Eliminate multiplication with 1.
   3. Eliminate multiplication with 0,
   AND replace this multiplication with 0 DIRECTLY.

   Now consider the multiplication a*0, if `a` causes an error,
   then the instructions emitted by the normal compiler will raise
   this error when they are executed by the virtual machine.
   However, the instructions emitted by `compile_surprising`
   will skip the evaluation of `a`, and instead "return" with 0
   DIRECTLY, thus the error is no longer raised. Therefore,
   `compile_surprising` is faulty.
 *)

(* black-box testing *)

(* Black Box testing - part 1: checking how compile surprising is different from compile ltr *)

Definition compile_surprising_behaves_as_compile_ltr_with_test_case (ae : arithmetic_expression) : bool :=
  candidate_optimizer_behaves_as_compile_ltr_with_test_case compile_surprising ae.

Definition decompile_compile_surprising_and_compare (ae : arithmetic_expression) : (source_program * source_program) :=
  decompile_candidate_optimizer_and_compare compile_surprising ae.

Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae1).
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae2).
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae3).
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae4).
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae5).
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae6).
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae7).
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae8).
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae9).
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae10).
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae11).
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae12).
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae13).
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae14).
(* compile_surprising gives a different result for test_ae14 *)

Compute (arithmetic_expression_eqb
           test_ae14
           (Times
              (Times
                 (Literal 1)
                 (Literal 2))
              (Times
                 (Name "x"%string)
                 (Literal 3)))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae14)
           (Target_program
              (PUSH 1
                 :: PUSH 2
                 :: MUL
                 :: LOOKUP "x"
                 :: PUSH 3
                 :: MUL
                 :: MUL
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_surprising test_ae14)
           (Target_program
              (PUSH 2
                 :: LOOKUP "x"
                 :: PUSH 3
                 :: MUL
                 :: MUL
                 :: nil))).

Compute (decompile_compile_surprising_and_compare test_ae14).

Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae15).
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae16).
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge01).
(* compile_surprising gives a different result for test_ae_Plus_edge01 *)

Compute (arithmetic_expression_eqb
           (test_ae_Plus_edge01)
           (Plus
              (Literal 0)
              (Literal 1))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae_Plus_edge01)
           (Target_program
              (PUSH 0
                 :: PUSH 1
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_surprising test_ae_Plus_edge01)
           (Target_program
              (PUSH 1
                 :: nil))).

Compute (decompile_compile_surprising_and_compare test_ae_Plus_edge01).

Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge10).
(* compile_surprising gives a different result for test_ae_Plus_edge10 *)

Compute (arithmetic_expression_eqb
           (test_ae_Plus_edge10)
           (Plus
              (Literal 1)
              (Literal 0))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae_Plus_edge10)
           (Target_program
              (PUSH 1
                 :: PUSH 0
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_surprising test_ae_Plus_edge10)
           (Target_program
              (PUSH 1
                 :: nil))).

Compute (decompile_compile_surprising_and_compare test_ae_Plus_edge10).

Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge0x).
(* compile_surprising gives a different result for test_ae_Plus_edge0x *)

Compute (arithmetic_expression_eqb
           (test_ae_Plus_edge0x)
           (Plus
              (Literal 0)
              (Name "x"%string))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae_Plus_edge0x)
           (Target_program
              (PUSH 0
                 :: LOOKUP "x"
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_surprising test_ae_Plus_edge0x)
           (Target_program
              (LOOKUP "x"
                 :: nil))).

Compute (decompile_compile_surprising_and_compare test_ae_Plus_edge0x).

Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae_Plus_edgex0).
(* compile_surprising gives a different result for test_ae_Plus_edgex0 *)

Compute (decompile_compile_surprising_and_compare test_ae_Plus_edgex0).

Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae_Times_edge01).
(* compile_surprising gives a different result for test_ae_Times_edge01 *)

Compute (arithmetic_expression_eqb
           (test_ae_Times_edge01)
           (Times
              (Literal 0)
              (Literal 1))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae_Times_edge01)
           (Target_program
              (PUSH 0
                 :: PUSH 1
                 :: MUL
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_surprising test_ae_Times_edge01)
           (Target_program
              (PUSH 0
                 :: nil))).

Compute (decompile_compile_surprising_and_compare test_ae_Times_edge01).

Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae_Times_edge10).
(* compile_surprising gives a different result for test_ae_Times_edge10 *)

Compute (arithmetic_expression_eqb
           (test_ae_Times_edge10)
           (Times
              (Literal 1)
              (Literal 0))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae_Times_edge10)
           (Target_program
              (PUSH 1
                 :: PUSH 0
                 :: MUL
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_surprising test_ae_Times_edge10)
           (Target_program
              (PUSH 0
                 :: nil))).

Compute (decompile_compile_surprising_and_compare test_ae_Times_edge10).

Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae_Times_edge0x).
(* compile_surprising gives a different result for test_ae_Times_edge0x *)

Compute (arithmetic_expression_eqb
           (test_ae_Times_edge0x)
           (Times
              (Literal 0)
              (Name "x"%string))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae_Times_edge0x)
           (Target_program
              (PUSH 0
                 :: LOOKUP "x"
                 :: MUL
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_surprising test_ae_Times_edge0x)
           (Target_program
              (PUSH 0
                 :: nil))).

Compute (decompile_compile_surprising_and_compare test_ae_Times_edge0x). (* eh? *)

Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae_Times_edgex0).
(* compile_surprising gives a different result for test_ae_Times_edgex0 *)

Compute (decompile_compile_surprising_and_compare test_ae_Times_edgex0). (* eh? *)

Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae_Times_edge12).
(* compile_surprising gives a different result for test_ae_Times_edge12 *)
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae_Times_edge21).
(* compile_surprising gives a different result for test_ae_Times_edge21 *)
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae_Times_edge1x).
(* compile_surprising gives a different result for test_ae_Times_edge1x *)
Compute (compile_surprising_behaves_as_compile_ltr_with_test_case test_ae_Times_edgex1).
(* compile_surprising gives a different result for test_ae_Times_edgex1 *)

(* Black Box testing - part 2: checking if compile surprising preserves correctness *)

Definition compile_surprising_preserves_correctness_of_run_with_test_case (ae : arithmetic_expression) : bool :=
  candidate_optimizer_preserves_correctness_of_run compile_surprising ae.

Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae1).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae2).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae3).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae4).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae5).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae6).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae7).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae8).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae9).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae10).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae11).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae12).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae13).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae14).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae15).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae16).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae_Plus_edge01).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae_Plus_edge10).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae_Plus_edge0x).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae_Plus_edgex0).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae_Times_edge01).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae_Times_edge10).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae_Times_edge0x).

(* test_ae_Times_edge0x results in a different value when run after being compiled with compile_surprising *)

Compute (target_expressible_value_eqb
           (run_ltr (apply_candidate compile_ltr test_ae_Times_edge0x) nil)
           (Target_expressible_msg
              (Target_undeclared_name "x"))).

Compute (target_expressible_value_eqb
           (run_ltr (apply_candidate compile_surprising test_ae_Times_edge0x) nil)
           (Target_expressible_nat 0)).

Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae_Times_edgex0).

(* test_ae_Times_edgex0 results in a different value when run after being compiled with compile_surprising *)

Compute (target_expressible_value_eqb
           (run_ltr (apply_candidate compile_ltr test_ae_Times_edgex0) nil)
           (Target_expressible_msg
              (Target_undeclared_name "x"))).

Compute (target_expressible_value_eqb
           (run_ltr (apply_candidate compile_surprising test_ae_Times_edgex0) nil)
           (Target_expressible_nat 0)).

Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae_Times_edge12).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae_Times_edge21).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae_Times_edge1x).
Compute (compile_surprising_preserves_correctness_of_run_with_test_case test_ae_Times_edgex1).

(* Black-box observations *)

(* compile_surprising applies the following three properties whenever it is possible. 'a' can be either a nat or a name :

- adding 0 (neutral property of 0 for addition)
i.e. 0 + a -> a AND a + 0 -> a

- multiplying by 0 (absorbing property of 0 for multiplication)
i.e. 0 * a -> 0 AND a * 0 -> 0

- multiplying by 1 (netural property of 1 for addition)
i.e. 1 * a -> a AND a * 1 -> a

And these are the exact simplifications we saw from test_ae14, and all the test cases.

This optimizer does not preserve the correctness of run because if the mult-by-zero simplification case is present in any of the subexpressions including an undefined name, the lookup and the resulting error message is overridden. Here's an example to illustrate the problem with that simplification:
 *)

Compute (let test_ae_times_edge_a0 := (Times (Name "a"%string) (Literal 0)) in
         let test_ae_times_edge_0x := (Times (Literal 0) (Name "x"%string)) in
         target_expressible_value_eqb
           (run_ltr (compile_surprising (Source_program test_ae_times_edge_a0)) nil)
           (run_ltr (compile_surprising (Source_program test_ae_times_edge_0x)) nil)).

(* ***** *)

(* compile_unexpected *)

Fixpoint compile_unexpected_aux
  (ae : arithmetic_expression)
  (k0 k1 : unit -> list byte_code_instruction)
  (k : list byte_code_instruction -> list byte_code_instruction)
  : list byte_code_instruction :=
  match ae with
    Literal 0 =>
    k0 tt
  | Literal 1 =>
    k1 tt
  | Literal n =>
    k (PUSH n :: nil)
  | Name x =>
    k (LOOKUP x :: nil)
  | Plus ae1 ae2 =>
    compile_unexpected_aux ae1
      (fun _ => compile_unexpected_aux ae2 k0 k1 k)
      (fun _ => compile_unexpected_aux ae2
                  k1
                  (fun _ => k (PUSH 1 :: PUSH 1 :: ADD :: nil))
                  (fun bcis2 => k (PUSH 1 :: bcis2 ++ ADD :: nil)))
      (fun bcis1 => compile_unexpected_aux ae2
                      (fun _ => k bcis1)
                      (fun _ => k (bcis1 ++ PUSH 1 :: ADD :: nil))
                      (fun bcis2 => k (bcis1 ++ bcis2 ++ ADD :: nil)))
  | Times ae1 ae2 =>
    compile_unexpected_aux ae1
      (fun _ => compile_unexpected_aux ae2
                  (fun _ => k (PUSH 0 :: nil))
                  (fun _ => k (PUSH 0 :: nil))
                  (fun bcis2 => k (PUSH 0 :: bcis2 ++ MUL :: nil)))
      (fun _ => compile_unexpected_aux ae2
                  (fun _ => k (PUSH 0 :: nil))
                  k1 k)
      (fun bcis1 => compile_unexpected_aux ae2
                      (fun _ => bcis1 ++ PUSH 0 :: MUL :: nil)
                      (fun _ => k bcis1)
                      (fun bcis2 => k (bcis1 ++ bcis2 ++ MUL :: nil)))
  end.

Definition compile_unexpected (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_unexpected_aux ae (fun _ => PUSH 0 :: nil) (fun _ => PUSH 1 :: nil) (fun bcis => bcis))
  end.

(* VietAnh1010's white-box observations:

   The function is in CPS, with three continuations:

   k0: is applied directly when we encounter Literal 0,
   therefore it should be the continuation that dictates
   what to do when the result of the compilation is 0.
   k1: what to do when the result of the compilation is 1.
   k: what to do when none of the above holds.

   In Plus case we compile ae1 as bcis1
      If bcis1 is 0, then we continue after compiling ae2 as bcis2,
      If bcis1 is 1, then we compile ae2 as bcis2,
         if bcis2 is 0, then we continue with 1,
         if bcis2 is 1, then we continue with 1 + 1,
         else, we continue with 1 + bcis2.
      Else, we compile ae2 as bcis2
        if bcis2 is 0, then we continue with bcis1 ,
        if bcis2 is 1, then we continue with bcis1 + 1
        else, we continue with bcis1 + bcis2.

   In Times case we compile ae1 as bcis1
      If bcis1 is 0, then we compile ae2 as bcis2,
         if bcis2 is 0, then we contine with 0,
         if bcis2 is 1, then we continue with 0,
         else, we continue with 0 * bcis2
      If bcis1 is 1, then we compile ae2 as bcis2,
         if bcis2 is 0, then we continue with 0,
         else, we continue the continuation as is.
      Else, we compile ae2 as bcis2,
        if bcis2 is 0, then we stop the continuation after pusing bcis1 * 0,
        if bcis2 is 1, then we continue with bcis1
        else, we continue with bcis1 + bcis2.

   So, we apply the neutral property of 0 for addition on the left
   and right, the absorbing property of 0 for multiplication on the
   left and right, and the neutral property of 1 for multiplication on the
   left and right.

   Yet, the optimizing compiler does not return a correct result of
   bcis1 compiles to something else than 0 and 1 and if bcis2 compiles to
   something 0, as all previous continuations are overriden.

   Changing
   (fun _ => bcis1 ++ PUSH 0 :: MUL :: nil)
   to
   k (fun _ => bcis1 ++ PUSH 0 :: MUL :: nil)
   resolves this issue.
 *)

Compute (compile_unexpected
           (Source_program
              (Plus
                 (Times (Literal 0) (Literal 1))
                 (Literal 1)))).

(* Notice that 0*1 -> 0, but this 0 is pushed into the list and not
   eliminated *)

Compute (compile_unexpected
           (Source_program
              (Plus
                 (Times (Literal 0) (Literal 0))
                 (Literal 1)))).

(* Again, 0*0 -> 0, and PUSH 0 is pushed into the list.

   EDIT: I realized that the continuation is not called in one case:
   `fun _ => bcis1 ++ PUSH 0 :: MUL :: nil`. This discards the
   instructions correspond to upper (level) binary operators. Hence,
   the compiler may return incorrect result.
 *)

(* Counter example: *)
Compute (
    let ae :=
      Plus
        (Plus
           (Literal 42)
           (Literal 42))
        (Times
           (Literal 42)
           (Literal 0))
    in
    let sp := Source_program ae in
    let tp_correct := compile_ltr sp in
    let tp_incorrect := compile_unexpected sp in
    (run_ltr tp_correct nil, run_ltr tp_incorrect nil)).

(* Black Box testing - part 1: checking how compile unexpected is different from compile ltr *)

Definition compile_unexpected_behaves_as_compile_ltr_with_test_case (ae : arithmetic_expression) :=
  candidate_optimizer_behaves_as_compile_ltr_with_test_case compile_unexpected ae.

Definition decompile_compile_unexpected_and_compare (ae : arithmetic_expression) : (source_program * source_program) :=
  decompile_candidate_optimizer_and_compare compile_unexpected ae.

Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae1).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae2).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae3).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae4).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae5).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae6).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae7).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae8).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae9).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae10).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae11).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae12).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae13).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae14).
(* test_ae14 does not compile the same way *)

Compute (arithmetic_expression_eqb
           test_ae14
           (Times
              (Times
                 (Literal 1)
                 (Literal 2))
              (Times
                 (Name "x"%string)
                 (Literal 3)))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae14)
           (Target_program
              (PUSH 1
                 :: PUSH 2
                 :: MUL
                 :: LOOKUP "x"
                 :: PUSH 3
                 :: MUL
                 :: MUL
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_unexpected test_ae14)
           (Target_program
              (PUSH 2
                 :: LOOKUP "x"
                 :: PUSH 3
                 :: MUL
                 :: MUL
                 :: nil))).

Compute (decompile_compile_unexpected_and_compare test_ae14).

Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae15).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae16).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge01).
(* test_ae_Plus_edge01 does not compile the same way *)

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae_Plus_edge01)
           (Target_program
              (PUSH 0
                 :: PUSH 1
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_unexpected test_ae_Plus_edge01)
           (Target_program
              (PUSH 1
                 :: nil))).

Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge10).

Compute (decompile_compile_unexpected_and_compare test_ae_Plus_edge01).

(* test_ae_Plus_edge10 does not compile the same way *)

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae_Plus_edge10)
           (Target_program
              (PUSH 1
                 :: PUSH 0
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_unexpected test_ae_Plus_edge10)
           (Target_program
              (PUSH 1
                 :: nil))).

Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge0x).
(* test_ae_Plus_edge0x does not compile the same way *)

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae_Plus_edge0x)
           (Target_program
              (PUSH 0
                 :: LOOKUP "x"%string
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_unexpected test_ae_Plus_edge0x)
           (Target_program
              (LOOKUP "x"%string
                 :: nil))).

Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae_Plus_edgex0).
(* test_ae_Plus_edgex0 does not compile the same way *)

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae_Plus_edgex0)
           (Target_program
              (LOOKUP "x"%string
                 :: PUSH 0
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_unexpected test_ae_Plus_edgex0)
           (Target_program
              (LOOKUP "x"%string
                 :: nil))).

Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae_Times_edge01).
(* test_ae_Times_edge01 does not compile the same way *)

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae_Times_edge01)
           (Target_program
              (PUSH 0
                 :: PUSH 1
                 :: MUL
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_unexpected test_ae_Times_edge01)
           (Target_program
              (PUSH 0
                 :: nil))).

Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae_Times_edge10).
(* test_ae_Times_edge10 does not compile the same way *)

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae_Times_edge10)
           (Target_program
              (PUSH 1
                 :: PUSH 0
                 :: MUL
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_unexpected test_ae_Times_edge10)
           (Target_program
              (PUSH 0
                 :: nil))).

Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae_Times_edge0x).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae_Times_edgex0).

(* Good, the problem of simplifying 0 * x and x * 0 to 0 is resolved. *)

(* The following four does not compile the same way *)

Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae_Times_edge12).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae_Times_edge21).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae_Times_edge1x).
Compute (compile_unexpected_behaves_as_compile_ltr_with_test_case test_ae_Times_edgex1).

(* Black Box testing - part 2: checking if compile unexpected preserves correctness *)

Definition compile_unexpected_preserves_correctness_of_run_with_test_case (ae : arithmetic_expression) : bool :=
  candidate_optimizer_preserves_correctness_of_run compile_unexpected ae.

Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae1).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae2).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae3).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae4).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae5).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae6).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae7).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae8).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae9).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae10).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae11).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae12).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae13).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae14).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae15).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae16).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae_Plus_edge01).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae_Plus_edge10).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae_Plus_edge0x).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae_Plus_edgex0).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae_Times_edge01).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae_Times_edge10).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae_Times_edge0x).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae_Times_edgex0).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae_Times_edge12).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae_Times_edge21).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae_Times_edge1x).
Compute (compile_unexpected_preserves_correctness_of_run_with_test_case test_ae_Times_edgex1).

(* all clear *)

(* compile_unexpected is similar to compile_surprising in that it applies neutral property of 0 for addition, neutral property of 1 for multiplication, and absorbing property of 0 for multiplication, but it does not apply the absorbing property of 0 for multiplication if the expression involves a name. We have discussed the issue with applying the zero property of multiplication if a name is present above.

With the problem of applying the absorbing property of 0 for multiplication resolved, compile_unexpected preserves the correctness of run_ltr. *)

(* After discussing with WB: *)

(* (42 * 0) + 0 -> 42 * 0 *)
Compute (let ae := (Plus
                      (Times
                         (Literal 42)
                         (Literal 0))
                      (Literal 0)) in
         decompile_compile_unexpected_and_compare ae).

(* (42 + 0) * 0 -> 42 * 0 *)
Compute (let ae := (Times
                      (Plus
                         (Literal 42)
                         (Literal 0))
                      (Literal 0)) in
         decompile_compile_unexpected_and_compare ae).

(* (42 + 42) + (42 * 0) -> 42 * 0 *)
Compute (let ae :=
           Plus
             (Plus
                (Literal 42)
                (Literal 42))
             (Times
                (Literal 42)
                (Literal 0)) in
         decompile_compile_unexpected_and_compare ae).

(* ((((1 + 2) * 0) * 0) + (42 * 0) -> (1 + 2) * 0 *)
Compute (let ae :=
           Plus
             (Times
                (Times
                   (Plus
                      (Literal 1)
                      (Literal 2))
                   (Literal 0))
                (Literal 0))
             (Times
                (Literal 42)
                (Literal 0)) in
         decompile_compile_unexpected_and_compare ae).

(* So no, compile_unexpected does not preserves the correctness of run_ltr. Why? The first instance of multiplication with 0 on the RHS is pushed on to the top of the stack and the continuation is discontinued! *)

(* ***** *)

(* compile_curiouser *)

Fixpoint compile_curiouser_aux
  (ae : arithmetic_expression)
  (c : nat -> list byte_code_instruction)
  (k : list byte_code_instruction -> list byte_code_instruction)
  : list byte_code_instruction :=
  match ae with
    Literal n =>
    c n
  | Name x =>
    k (LOOKUP x :: nil)
  | Plus ae1 ae2 =>
    compile_curiouser_aux ae1
      (fun n1 => compile_curiouser_aux ae2
                   (fun n2 => c (n1 + n2))
                   (fun bcis2 => match n1 with
                                   O => k bcis2
                                 | _ => k (PUSH n1 :: bcis2 ++ ADD :: nil)
                                 end))
      (fun bcis1 => compile_curiouser_aux ae2
                      (fun n2 => match n2 with
                                   O => k bcis1
                                 | _ => k (bcis1 ++ PUSH n2 :: ADD :: nil)
                                 end)
                      (fun bcis2 => k (bcis1 ++ bcis2 ++ ADD :: nil)))
  | Times ae1 ae2 =>
    compile_curiouser_aux ae1
      (fun n1 => compile_curiouser_aux ae2
                   (fun n2 => c (n1 * n2))
                   (fun bcis2 => match n1 with
                                   1 => k bcis2
                                 | _ => k (PUSH n1 :: bcis2 ++ MUL :: nil)
                                 end))
      (fun bcis1 => compile_curiouser_aux ae2
                      (fun n2 => match n2 with
                                   1 => k bcis1
                                 | _ => k (bcis1 ++ PUSH n2 :: MUL :: nil)
                                 end)
                      (fun bcis2 => k (bcis1 ++ bcis2 ++ MUL :: nil)))
  end.

Definition compile_curiouser (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_curiouser_aux ae (fun n => PUSH n :: nil) (fun bcis => bcis))
  end.

(* VietAnh1010's white-box observations:
   The function is in CPS, with two continuations:

   c: what to do when the result of the compilation is a constant.
   k: what to do when the case above does not hold.

   It is quite obvious what is the optimization this compiler
   applies: constant folding. Apart from constant folding, we observe
   that the compiler does a case analysis when the result of
   compilation is a constant. Special treatment is given for 0 in the
   Plus case and 1 in the Times case, thus the compiler also eliminates
   addition with 0 and multiplication with 1, on both sides.
 *)


(* black-box testing *)

(* Black Box testing - part 1: checking how compile curiouser is different from compile ltr *)

Definition compile_curiouser_behaves_as_compile_ltr_with_test_case (ae : arithmetic_expression) : bool :=
  candidate_optimizer_behaves_as_compile_ltr_with_test_case compile_curiouser ae.

Definition decompile_compile_curiouser_and_compare (ae : arithmetic_expression) : (source_program * source_program) :=
  decompile_candidate_optimizer_and_compare compile_curiouser ae.

Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae1).
(* compile_curiouser gives a different result for test_ae1 *)

Compute (arithmetic_expression_eqb
           test_ae1
           (Plus
              (Literal 1)
              (Literal 10))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae1)
           (Target_program
              (PUSH 1
                 :: PUSH 10
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_curiouser test_ae1)
           (Target_program
              (PUSH 11
                 :: nil))).

Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae2).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae3).
(* compile_curiouser gives a different result for test_ae3 *)

Compute (arithmetic_expression_eqb
           test_ae3
           (Times
              (Literal 2)
              (Literal 3))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae3)
           (Target_program
              (PUSH 2
                 :: PUSH 3
                 :: MUL
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_curiouser test_ae3)
           (Target_program
              (PUSH 6
                 :: nil))).

Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae4).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae5).
(* compile_curiouser gives a different result for test_ae5 *)

Compute (arithmetic_expression_eqb
           test_ae5
           (Plus
              (Plus
                 (Literal 1)
                 (Literal 2))
              (Plus
                 (Literal 3)
                 (Name "x"%string)))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae5)
           (Target_program
              (PUSH 1
                 :: PUSH 2
                 :: ADD
                 :: PUSH 3
                 :: LOOKUP "x"
                 :: ADD
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_curiouser test_ae5)
           (Target_program
              (PUSH 3
                 :: PUSH 3
                 :: LOOKUP "x"
                 :: ADD
                 :: ADD
                 :: nil))).

Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae6).
(* compile_curiouser gives a different result for test_ae6 *)

Compute (arithmetic_expression_eqb
           test_ae6
           (Plus
              (Times
                 (Literal 2)
                 (Literal 3))
              (Name "z"%string))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae6)
           (Target_program
              (PUSH 2
                 :: PUSH 3
                 :: MUL
                 :: LOOKUP "z"
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_curiouser test_ae6)
           (Target_program
              (PUSH 6
                 :: LOOKUP "z"
                 :: ADD
                 :: nil))).

Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae7).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae8).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae9).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae10).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae11).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae12).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae13).
(* compile_curiouser gives a different result for test_ae13 *)

Compute (arithmetic_expression_eqb
           test_ae13
           (Plus
              (Plus
                 (Literal 1)
                 (Literal 2))
              (Plus
                 (Name "x"%string)
                 (Literal 3)))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae13)
           (Target_program
              (PUSH 1
                 :: PUSH 2
                 :: ADD
                 :: LOOKUP "x"
                 :: PUSH 3
                 :: ADD
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_curiouser test_ae13)
           (Target_program
              (PUSH 3
                 :: LOOKUP "x"
                 :: PUSH 3
                 :: ADD
                 :: ADD
                 :: nil))).

Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae14).
(* compile_curiouser gives a different result for test_ae14 *)

Compute (arithmetic_expression_eqb
           test_ae14
           (Times
              (Times
                 (Literal 1)
                 (Literal 2))
              (Times
                 (Name "x"%string)
                 (Literal 3)))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae14)
           (Target_program
              (PUSH 1
                 :: PUSH 2
                 :: MUL
                 :: LOOKUP "x"
                 :: PUSH 3
                 :: MUL
                 :: MUL
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_curiouser test_ae14)
           (Target_program
              (PUSH 2
                 :: LOOKUP "x"
                 :: PUSH 3
                 :: MUL
                 :: MUL
                 :: nil))).

Compute (decompile_compile_curiouser_and_compare test_ae14).

Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae15).
(* compile_curiouser gives a different result for test_ae15 *)

Compute (arithmetic_expression_eqb
           test_ae15
           (Plus
              (Plus
                 (Literal 1)
                 (Literal 2))
              (Times
                 (Literal 3)
                 (Name "x"%string)))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae15)
           (Target_program
              (PUSH 1
                 :: PUSH 2
                 :: ADD
                 :: PUSH 3
                 :: LOOKUP "x"
                 :: MUL
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_curiouser test_ae15)
           (Target_program
              (PUSH 3
                 :: PUSH 3
                 :: LOOKUP "x"
                 :: MUL
                 :: ADD
                 :: nil))).

Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae15).

Compute (decompile_compile_curiouser_and_compare test_ae15).

(* compile_curiouser gives a different result for test_ae16 *)

Compute (arithmetic_expression_eqb
           test_ae16
           (Plus
              (Plus
                 (Literal 2)
                 (Plus
                    (Literal 1)
                    (Literal 2)))
              (Times
                 (Literal 3)
                 (Name "x"%string)))).

Compute (target_program_eqb
           (apply_candidate compile_ltr test_ae16)
           (Target_program
              (PUSH 2
                 :: PUSH 1
                 :: PUSH 2
                 :: ADD
                 :: ADD
                 :: PUSH 3
                 :: LOOKUP "x"
                 :: MUL
                 :: ADD
                 :: nil))).

Compute (target_program_eqb
           (apply_candidate compile_curiouser test_ae16)
           (Target_program
              (PUSH 5
                 :: PUSH 3
                 :: LOOKUP "x"
                 :: MUL
                 :: ADD
                 :: nil))).

(* The following six test ae produce different results than compile_ltr*)
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge01).

Compute (decompile_compile_curiouser_and_compare test_ae_Plus_edge01).

Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge10).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae_Plus_edge0x).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae_Plus_edgex0).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae_Times_edge01).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae_Times_edge10).

Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae_Times_edge0x).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae_Times_edgex0).

(* The following four test ae produce different results than compile_ltr*)
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae_Times_edge12).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae_Times_edge21).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae_Times_edge1x).
Compute (compile_curiouser_behaves_as_compile_ltr_with_test_case test_ae_Times_edgex1).

Compute (decompile_compile_curiouser_and_compare
           (Times
              (Times
                 (Literal 0)
                 (Literal 1))
              (Times
                 (Literal 1)
                 (Literal 4)))).

(* Black Box testing - part 2: checking if compile curiouser preserves correctness *)

Definition compile_curiouser_preserves_correctness_of_run_with_test_case (ae : arithmetic_expression) : bool :=
  candidate_optimizer_preserves_correctness_of_run compile_curiouser ae.

Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae1).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae2).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae3).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae4).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae5).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae6).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae7).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae8).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae9).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae10).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae11).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae12).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae13).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae14).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae15).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae16).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae_Plus_edge01).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae_Plus_edge10).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae_Plus_edge0x).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae_Plus_edgex0).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae_Times_edge01).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae_Times_edge10).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae_Times_edge0x).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae_Times_edgex0).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae_Times_edge12).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae_Times_edge21).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae_Times_edge1x).
Compute (compile_curiouser_preserves_correctness_of_run_with_test_case test_ae_Times_edgex1).

(* preserves correctness *)

(* Black-box observations *)
(* compile_curiouser does not match compile_ltr for test cases that contain NC expressions, as one part of the simplification is constant folding. The other part of the simplification involves applying neutral property of 0 and 1 for addition and multiplication, repectively, and absorbing  property of 0 for multiplication to constant expressions. *)

(* (42 * 0) + 0 -> 0 *)
Compute (let ae := (Plus
                      (Times
                         (Literal 42)
                         (Literal 0))
                      (Literal 0)) in
         decompile_compile_curiouser_and_compare ae).

(* (42 + 0) * 0 ->  0 *)
Compute (let ae := (Times
                      (Plus
                         (Literal 42)
                         (Literal 0))
                      (Literal 0)) in
         decompile_compile_curiouser_and_compare ae).

(* (42 + 42) + (42 * 0) -> 84 *)
Compute (let ae :=
           Plus
             (Plus
                (Literal 42)
                (Literal 42))
             (Times
                (Literal 42)
                (Literal 0)) in
         decompile_compile_curiouser_and_compare ae).

(* ((((1 + 2) * 0) * 0) + (42 * 0) -> 0 *)
Compute (let ae :=
           Plus
             (Times
                (Times
                   (Plus
                      (Literal 1)
                      (Literal 2))
                   (Literal 0))
                (Literal 0))
             (Times
                (Literal 42)
                (Literal 0)) in
         decompile_compile_curiouser_and_compare ae).

(* And the issue with the multiplication with 0 on the RHS we saw in unexpected is now resolved *)

(* ********** *)

(* end of midterm-project.v *)
