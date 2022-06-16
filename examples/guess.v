From Coq Require Import Arith String Streams.
From FreeSpec.Core Require Import Core.

Open Scope nat_scope.

(** * Specifying the Guess Game *)

Inductive CONSOLE : interface :=
| ReadNat : unit -> CONSOLE nat
| Write : string -> CONSOLE unit.

Generalizable All Variables.

Definition read_nat `{Provide ix CONSOLE} (u : unit) : impure ix nat :=
  request (ReadNat u).

Definition write `{Provide ix CONSOLE} (s : string) : impure ix unit :=
  request (Write s).

(* definition of a semantic for the [CONSOLE] interface *)
CoFixpoint console (in_flow : Stream nat) (out_flow : list string): semantics (CONSOLE) :=
  mk_semantics (fun α (e : CONSOLE α) =>
                  match e with
                  | ReadNat _ => (Streams.hd in_flow, console (Streams.tl in_flow) out_flow)
                  | Write s => (tt, console in_flow (s :: out_flow))
                  end).

(* the guess game loop logic *)                  
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

(* aux functions to generate infinite flows *)
CoFixpoint rep_inf {A : Type} (n:A) : Stream A := 
  Cons n (rep_inf n).

CoFixpoint nat_inf (n:nat) : Stream nat := 
  Cons n (nat_inf (S n)).

Compute (exec_impure (console (rep_inf 10) []) (guess 10 20)).
(* >> out_flow: ["Won !"; "Guess the number:"] *)

Compute (exec_impure (console (rep_inf 10) []) (guess 30 20)).
(* >> out_flow: ["The target is greater";...] *)

Compute (exec_impure (console (nat_inf 20) []) (guess 15 10)).
(* >> out_flow: ["Game Over: max attempt limit exceeded";...] *)