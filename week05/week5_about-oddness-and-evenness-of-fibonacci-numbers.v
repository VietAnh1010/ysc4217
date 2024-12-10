Fixpoint fib_v3 (n : nat) : nat :=
  match n with
    0 => 0
  | S n' => match n' with
              0 => 1
            | S n'' => fib_v3 n' + fib_v3 n''
            end
:q
  end.
