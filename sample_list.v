Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | [ ] => l2
  | x :: l =>  x :: (app l l2)
  end.

Definition bag := natlist.

Fixpoint eqb (n1 n2 : nat) : bool :=
  match n1, n2 with
  | O , O => true
  | S _ , O => false
  | O , S _ => false
  | S n, S m => eqb n m
  end.

Fixpoint count (v : nat) (l : bag) : nat :=
  match l with
  | [ ] => 0
  | x::l' =>  match (eqb v x) with
              | true => 1 + count v l'
              | false => count v l'
              end
  end.

Fixpoint member (v : nat) (l : bag) : bool :=
  match l with
  | [ ] => false
  | x::l' =>  match (eqb v x) with
              | true => true
              | false => member v l'
              end
  end.

Fixpoint rev (l : bag) : bag :=
  match l with
  | [ ] => [ ]
  | x::l' => app (rev l') [x]
  end.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

Theorem one : forall l : bag, app [ ] l = l.
Proof.
  intros. simpl. reflexivity.
Qed.

Fixpoint length (l:natlist) : nat :=
  match l with
  | [ ] => O 
  | x::l' => S (length l')
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | [ ] => [ ] 
  | x::l' => l'
  end.

Theorem two : forall l : natlist,
  pred (length l) = length (tl l).
Proof.
  intros. destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.