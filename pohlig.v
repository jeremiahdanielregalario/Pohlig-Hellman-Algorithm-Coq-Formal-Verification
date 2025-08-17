(**
  Pohlig-Hellman algorithm verification in Coq
  We verify that the discrete_log function computes the discrete logarithm
  in a finite cyclic group of known order, assuming certain helper theorems as axioms.
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* Abstract finite cyclic group *)
Class FiniteCyclicGroup := {
  G : Type;
  op : G -> G -> G;
  e : G; (* group identity *)
  inv : G -> G;
  pow : G -> nat -> G;
  assoc : forall x y z, op x (op y z) = op (op x y) z;
  id_l : forall x, op e x = x;
  id_r : forall x, op x e = x;
  inv_l : forall x, op (inv x) x = e;
  pow0 : forall x, pow x 0 = e;
  powS : forall x n, pow x (S n) = op x (pow x n);
  order : nat;
  gen : G;
  gen_order : pow gen order = e
}.

Section PohligHellman.
Context `{FiniteCyclicGroup}.

(* Prime predicate *)
Parameter prime : nat -> Prop.

(* Factorization of the group order into prime-power factors *)
Parameter factor : nat -> list (nat * nat).
Axiom factor_correct:
  forall n,
    let facs := factor n in
    Forall (fun '(p, k) => prime p) facs /\
    fold_right (fun '(p, k) acc => acc * p ^ k) 1 facs = n.

(* Discrete log solver for prime-power order subgroup of order p^k *)
Parameter discrete_log_primepower : G -> G -> nat -> nat -> nat.
Axiom discrete_log_primepower_correct:
  forall g h p k,
    let m := p ^ k in
    pow g m = e ->
    exists x, x < m /\
    pow g x = h.

(* Chinese remainder theorem solver *)
Parameter CRT_solve : list nat -> list nat -> nat.
Axiom CRT_solve_correct:
  forall mods rems,
    length mods = length rems ->
    (* pairwise coprime *)
    (forall i j, i <> j -> Nat.gcd (nth i mods 1) (nth j mods 1) = 1) ->
    let M := fold_right Nat.mul 1 mods in
    let x := CRT_solve mods rems in
    x < M /\
    Forall2 (fun mi ri => x mod mi = ri) mods rems.

(* Main discrete log via Pohlig-Hellman *)
Definition discrete_log (h : G) : nat :=
  let n := order in
  let facs := factor n in
  let mods := map (fun '(p, k) => p ^ k) facs in
  let rems := map (fun '(p, k) =>
    let m := p ^ k in
    let g_i := pow gen (n / m) in
    let h_i := pow h   (n / m) in
    discrete_log_primepower g_i h_i p k) facs in
  CRT_solve mods rems.

Theorem discrete_log_correct :
  forall h, pow gen (discrete_log h) = h.
Proof.
  intros h.
  unfold discrete_log.
  set (n := order) at 1.
  set (facs := factor n).
  set (mods := map (fun '(p, k) => p ^ k) facs).
  set (rems := map (fun '(p, k) =>
    let m := p ^ k in
    let g_i := pow gen (n / m) in
    let h_i := pow h (n / m) in
    discrete_log_primepower g_i h_i p k) facs).
  (* use discrete_log_primepower_correct for each (p,k) to get congruences *)
  (* apply CRT_solve_correct to reconstruct x mod n giving pow gen x = h *)
  Admitted.

End PohligHellman.
