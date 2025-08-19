Inductive bool : Type := 
  | true 
  | false.

Definition negb (b : bool) : bool := 
  match b with
  | true => false
  | false => true
  end.

compute(negb true). 

(*  *)