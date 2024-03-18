Require Import Vectors.Vector.
Import VectorNotations.
Require Import Coq.Arith.Arith.
Import Fin.
Definition vector := Vector.t.
Import Nat.

Inductive tree (n : nat) : nat -> Type :=
| max_index : Fin.t n -> tree n 1 
| comp {m : nat} : vector (Fin.t n) (S (S m)) -> tree n (S m) -> tree n (S m) -> tree n (S (S m)).

Arguments max_index {n} _ .
Arguments comp {n} {m} _ _ _ .
(*Working on tree_gen *)

Definition incr_index {n} (i : Fin.t n) : Fin.t (S n) :=
  match i with
  | x => FS x
  end.
    
Fixpoint gen_vector (n : nat): vector (Fin.t n) n:=
  match n with
  | 0 => []
  | S n1 => @F1 n1  :: (map incr_index (gen_vector n1) )
  end.

Compute (gen_vector 8).

Fixpoint tree_gen {n m} :  vector (Fin.t n) (S m) -> tree n (S m):=
  match  m with
  | 0 => fun v => max_index (hd v)
  | (S m') => fun v => comp v (tree_gen (tl v)) (tree_gen ((hd v)::(tl (tl v))))
  end.

Compute (tree_gen (gen_vector 3)).

Print lt_dec.
Check nth.

(*Fixpoint compute_max {n m} (v : tree (S n) (S m)) : vector *)

Fixpoint c_max {n} (t : tree n 1): Fin.t n :=
  match t with
  | max_index i => i
  end.
          

Fixpoint compute_max {n m} :tree (S n) (S m) -> vector nat (S n) -> Fin.t (S n) :=
  match m with
  | 0 => fun t: tree (S n) 1 => match t with
        | max_index i => fun _ => i
        end
  | S m1 => fun t: tree (S n) (S (S (m1))) => match t with
                                        | comp v t1 t2 => match v with
                                                         | x :: x1 :: xs => x
                                                         end
                                        end
  end.



              
  

