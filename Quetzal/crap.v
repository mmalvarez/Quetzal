(* Used to define until in LTL.v, but this is a bad way to do it! *)
Fixpoint snoc {T : Type} (x : T) (l : list T) : list T :=
  match l with
  | nil => cons x nil
  | cons h t => cons h (snoc x t)
  end.

Inductive StreamPref {T : Type} :
  Stream T -> list T -> Stream T -> Prop :=
| SpNil : forall s, StreamPref s nil s 
| SpCons : forall s (n : T) t s',
    StreamPref s t (scons T n s') ->
    StreamPref s (snoc n t) s'.

