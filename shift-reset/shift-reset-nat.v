Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List String Ascii.

(* ********** *)

(* Abstract syntax of programs: *)

Inductive term : Type :=
  TNat : nat -> term
| TPlus : term -> term -> term
| TMult : term -> term -> term
| TApp : (nat -> nat) -> term -> term
| TReset : term -> term
| TShift : ((nat -> nat) -> term) -> term.

(* ********** *)

Fixpoint eval_aux (t : term) (k : nat -> nat) : nat :=
  match t with
    TNat n =>
    k n
  | TPlus t1 t2 =>
    eval_aux t1 (fun n1 => eval_aux t2 (fun n2 => k (n1 + n2)))
  | TMult t1 t2 =>
    eval_aux t1 (fun n1 => eval_aux t2 (fun n2 => k (n1 * n2)))
  | TApp f t =>
    eval_aux t (fun n => k (f n))
  | TReset t =>
    k (eval_aux t (fun n => n))
  | TShift f =>
    eval_aux (f k) (fun n => n)
  end.

Definition eval (t : term) : nat :=
  eval_aux t (fun n => n).

Lemma fold_unfold_eval_aux_TNat :
  forall (n : nat)
         (k : nat -> nat),
    eval_aux (TNat n) k =
    k n.
Proof.
  fold_unfold_tactic eval_aux.
Qed.

Lemma fold_unfold_eval_aux_TPlus :
  forall (t1 t2 : term)
         (k : nat -> nat),
    eval_aux (TPlus t1 t2) k =
    eval_aux t1 (fun n1 => eval_aux t2 (fun n2 => k (n1 + n2))).
Proof.
  fold_unfold_tactic eval_aux.
Qed.

Lemma fold_unfold_eval_aux_TMult :
  forall (t1 t2 : term)
         (k : nat -> nat),
    eval_aux (TMult t1 t2) k =
    eval_aux t1 (fun n1 => eval_aux t2 (fun n2 => k (n1 * n2))).
Proof.
  fold_unfold_tactic eval_aux.
Qed.

Lemma fold_unfold_eval_aux_TApp :
  forall (f : nat -> nat)
         (t : term)
         (k : nat -> nat),
    eval_aux (TApp f t) k =
    eval_aux t (fun n => k (f n)).
Proof.
  fold_unfold_tactic eval_aux.
Qed.

Lemma fold_unfold_eval_aux_TReset :
  forall (t : term)
         (k : nat -> nat),
    eval_aux (TReset t) k =
    k (eval_aux t (fun n => n)).
Proof.
  fold_unfold_tactic eval_aux.
Qed.

Lemma fold_unfold_eval_aux_TShift :
  forall (f : (nat -> nat) -> term)
         (k : nat -> nat),
    eval_aux (TShift f) k =
    eval_aux (f k) (fun n => n).
Proof.
  fold_unfold_tactic eval_aux.
Qed.

Module TestPrograms.

  Definition program1 : term :=
    (TReset
       (TPlus
          (TNat 1)
          (TShift
             (fun k =>
                TPlus
                  (TApp k (TNat 1))
                  (TApp k (TNat 2)))))).

  Compute eval program1.

  Lemma eval_aux_program1 :
    forall (k : nat -> nat), eval_aux program1 k = k 5.
  Proof.
    intro k.
    unfold program1.
    rewrite -> fold_unfold_eval_aux_TReset.
    rewrite -> fold_unfold_eval_aux_TPlus.
    rewrite -> fold_unfold_eval_aux_TNat.
    rewrite -> fold_unfold_eval_aux_TShift.
    rewrite -> fold_unfold_eval_aux_TPlus.
    rewrite -> fold_unfold_eval_aux_TApp.
    rewrite -> fold_unfold_eval_aux_TNat.
    rewrite -> fold_unfold_eval_aux_TApp.
    rewrite -> fold_unfold_eval_aux_TNat.
    reflexivity.
  Qed.

  Goal eval program1 = 5.
  Proof.
    unfold eval.
    exact (eval_aux_program1 (fun n => n)).
  Qed.

  Definition program2 : term :=
    TPlus (TNat 1) program1.

  Compute eval program2.

  Lemma eval_aux_program2 :
    forall (k : nat -> nat), eval_aux program2 k = k 6.
  Proof.
    intro k.
    unfold program2.
    rewrite -> fold_unfold_eval_aux_TPlus.
    rewrite -> fold_unfold_eval_aux_TNat.
    rewrite -> (eval_aux_program1 (fun n2 => k (1 + n2))).
    reflexivity.
  Qed.

  Goal eval program2 = 6.
  Proof.
    unfold eval.
    exact (eval_aux_program2 (fun n => n)).
  Qed.

  Definition program3 : term :=
    TReset
      (TPlus
         (TShift (fun k => TApp k (TNat 1)))
         (TShift (fun k => TApp k (TNat 2)))).

  Compute eval program3.

  Lemma eval_aux_program3 :
    forall (k : nat -> nat), eval_aux program3 k = k 3.
  Proof.
    intro k.
    unfold program3.
    rewrite -> fold_unfold_eval_aux_TReset.
    rewrite -> fold_unfold_eval_aux_TPlus.
    rewrite -> fold_unfold_eval_aux_TShift.
    rewrite -> fold_unfold_eval_aux_TApp.
    rewrite -> fold_unfold_eval_aux_TNat.
    rewrite -> fold_unfold_eval_aux_TShift.
    rewrite -> fold_unfold_eval_aux_TApp.
    rewrite -> fold_unfold_eval_aux_TNat.
    reflexivity.
  Qed.

  Goal eval program3 = 3.
  Proof.
    unfold eval.
    exact (eval_aux_program3 (fun n => n)).
  Qed.

  Definition program4 : term :=
    TReset
      (TPlus
         (TPlus
            (TNat 1)
            (TShift (fun k => TApp k (TNat 1))))
         (TReset
            (TMult
               (TNat 2)
               (TShift
                  (fun k =>
                     TMult
                       (TApp k (TNat 1))
                       (TApp k (TNat 2))))))).

  Compute eval program4.

  Lemma eval_aux_program4 :
    forall (k : nat -> nat), eval_aux program4 k = k 10.
  Proof.
    intro k.
    unfold program4.
    rewrite -> fold_unfold_eval_aux_TReset.
    rewrite -> fold_unfold_eval_aux_TPlus.
    rewrite -> fold_unfold_eval_aux_TPlus.
    rewrite -> fold_unfold_eval_aux_TNat.
    rewrite -> fold_unfold_eval_aux_TShift.
    rewrite -> fold_unfold_eval_aux_TApp.
    rewrite -> fold_unfold_eval_aux_TNat.
    rewrite -> fold_unfold_eval_aux_TReset.
    rewrite -> fold_unfold_eval_aux_TMult.
    rewrite -> fold_unfold_eval_aux_TNat.
    rewrite -> fold_unfold_eval_aux_TShift.
    rewrite -> fold_unfold_eval_aux_TMult.
    rewrite -> fold_unfold_eval_aux_TApp.
    rewrite -> fold_unfold_eval_aux_TNat.
    rewrite -> fold_unfold_eval_aux_TApp.
    rewrite -> fold_unfold_eval_aux_TNat.
    reflexivity.
  Qed.

  Goal eval program4 = 10.
  Proof.
    unfold eval.
    exact (eval_aux_program4 (fun n => n)).
  Qed.

End TestPrograms.
