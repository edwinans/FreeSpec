From FreeSpec Require Import Core.

Class Into (α β : Type) :=
  { into : α -> β
  }.

Instance refl_Into (α : Type) : Into α α :=
  { into := fun x => x
  }.

Inductive RAISE (α : Type) : interface :=
| Raise {β} (x : α) : RAISE α β.

Arguments Raise [α β] x.

Definition raise `{Into δ α, Provide ix (RAISE α)} {β} (x : δ) : impure ix β :=
  request (Raise (into x)).

Definition try `{Into δ α, Provide ix (RAISE α)} {β} (p : impure ix (δ + β)) : impure ix β :=
  do let* res := p in
     match res with
     | inl e => raise e
     | inr x => pure x
     end
  end.

Fixpoint recover {ix α β} (p : impure (ix + RAISE α) β) (h : α -> impure ix β) : impure ix β :=
  match p with
  | local x => local x
  | request_then (in_right (Raise e)) _ => h e
  | request_then (in_left e) f => request_then e (fun x => recover (f x) h)
  end.

Declare Scope raise_scope.

Notation "'recover' p 'with'  v 'of' t '=>' h 'end'" :=
  (recover p (fun (v : t) => h)) : raise_scope.

Open Scope raise_scope.
