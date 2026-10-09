From Datalog Require Import Default.

Declare Scope option_monad_scope.

Notation "' pat <- c1 ;; c2" :=
  (match c1 with
   | pat => c2
   | _ => default
   end)
  (at level 60, pat pattern, c1 at next level, right associativity) : option_monad_scope.

Notation "'assert' c1 ;; c2" :=
  (match c1 with
   | true => c2
   | false => default
   end)
  (at level 60, right associativity) : option_monad_scope.
