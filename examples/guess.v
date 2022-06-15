From Coq Require Import Arith String.
From FreeSpec.Core Require Import Core.

Open Scope nat_scope.

(** * Specifying the Guess Game *)

Inductive CONSOLE : interface :=
| ReadNat : unit -> CONSOLE nat
| Write : string -> CONSOLE unit.

Inductive GAME_ST : interface := 
| Win :CONSOLE nat -> GAME_ST string
| Lose : CONSOLE nat -> GAME_ST string
| Continue : CONSOLE nat -> GAME_ST (CONSOLE nat).

Generalizable All Variables.

Definition read_nat `{Provide ix CONSOLE} (u : unit) : impure ix nat :=
  request (ReadNat u).

Definition write `{Provide ix CONSOLE} (s : string) : impure ix unit :=
  request (Write s).

Fixpoint guess `{Provide ix CONSOLE} (target max_attempt : nat)
  : impure ix unit :=
  match max_attempt with 
  | 0 => write "Game Over: max attempt limit exceeded"
  | S m =>
    let* _ := write "Guess the number:" in
    let* g := read_nat tt in 
      if g =? target then 
        write "Won !"
      else if g <? target then 
        write "The target is greater";;
        guess target m
      else 
        write "The target is smaller";;
        guess target m
  end.
