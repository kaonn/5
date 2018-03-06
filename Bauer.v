(** An attempt to formalize graphs. *)

Require Import Arith.
Require Import List.
Require Export Coq.omega.Omega.
Require Import synth.

Import ListNotations.

Extraction Language Haskell.


(** In order to avoid the intricacies of constructive mathematics,
    we consider finite simple graphs whose sets of vertices are
    natural numbers 0, 1, , ..., n-1 and the edges form a decidable
    relation.  *)

(** We shall work a lot with statements of the form
    [forall i : nat, i < V -> P i], so we introduce a
    notatation for them, and similarly for existentials. *)
Notation "'all' i : V , P" := (forall i : nat, i < V -> P) (at level 20, i at level 99).
Notation "'some' i : V , P" := (exists i : nat, i < V /\ P) (at level 20, i at level 99).

Definition is_some {X : Type} (o : option X) : Prop := 
match o with 
| None => False
| _ => True
end.

Definition is_someb {X : Type} (o : option X) : bool := 
match o with 
| None => false
| _ => true
end.

Record Graph := {
  V :> S.t ; (* The number of vertices. So the vertices are numbers 0, 1, ..., V-1. *)
  E :> nat -> nat -> option nat (* The edge relation *)
(*   E_irreflexive : all x : V, (E x x = None);
  E_symmetric : all x : V, all y : V, (is_some (E x y) -> is_some (E y x)) *)
}.

Recursive Extraction Graph.

Check V.
(** Let us define some graphs. *)

(* Empty graph on [n] vertices *)
Definition Empty (n : nat) : Graph.
Proof.
  refine {| V := tabulate (fun i => i) n ;
            E := (fun x y => None)
         |} ; auto.
Defined.

(* Complete graph on [n] vertices *)
Definition K (n : nat) : Graph.
Proof.
  refine {| V := tabulate (fun i => i) n ;
            E := (fun x y => if x =? y then None else Some 0)
         |}.
(*   - intros.
    destruct (x =? x) eqn:e. tauto. pose (Nat.eqb_refl x). rewrite e in e0. inversion e0.
  - intros. unfold is_some in H1. destruct (x =? y) eqn:e. 
    + apply beq_nat_true in e. inversion H1.
    + apply beq_nat_false in e. destruct (y =? x) eqn:f. 
      * apply beq_nat_true in f. omega. 
      * simpl. tauto. *)
Defined.

(** Path on [n] vertices. *)
(* Definition Path (n : nat) : Graph.
Proof.
  (* We will do this proof very slowly by hand to practice. *)
  refine {| V := n ;
            E := fun x y => S x = y \/ x = S y
         |}.
  - intros.
    destruct (eq_nat_dec (S x) y).
    + tauto.
    + destruct (eq_nat_dec x (S y)).
      * tauto.
      * { right.
          intros [ ? | ? ].
          - absurd (S x = y) ; assumption.
          - absurd (x = S y) ; assumption.
        }
  - (* This case we do by using a powerful tactic "firstorder".
       We tell it to use the statement [n_Sn] from the [Arith] library.
       To see what [n_Sn] is, run command [Check n_Sn].
       To find [n_Sn], we ran the command [Search (?m <> S ?m)]. *)
    firstorder using n_Sn.
  - intros ? ? ? ? [?|?].
    + right ; now symmetry.
    + left; now symmetry.
Defined.

(** [Cycle n] is the cycle on [n+3] vertices. We define it in a way
    which avoids modular arithmetic. *)
Definition Cycle (n : nat) : Graph.
Proof.
  refine {| V := 3 + n ; (* Do not forget: we have [3+n] vertices 0, 1, ..., n+2 *)
            E := fun x y =>
                 (S x = y \/ x = S y \/ (x = 0 /\ y = 2 + n) \/ (x = 2 + n /\ y = 0))
         |}.
  - intros.
    destruct (eq_nat_dec (S x) y) ;
    destruct (eq_nat_dec x (S y)) ;
    destruct (eq_nat_dec x 0) ;
    destruct (eq_nat_dec y 0) ;
    destruct (eq_nat_dec x (2 + n)) ;
    destruct (eq_nat_dec y (2 + n)) ;
    tauto.
  - intros ? ? H.
    destruct H as [?|[?|[[? ?]|[? ?]]]].
    + firstorder using Nat.neq_succ_diag_l.
    + firstorder using Nat.neq_succ_diag_r.
    + apply (Nat.neq_succ_0 (S n)) ; transitivity x.
      * now symmetry.
      * assumption.
    + apply (Nat.neq_succ_0 (S n)) ; transitivity x.
      * now symmetry.
      * assumption.
  - intros ? ? ? ? [?|[?|[[? ?]|[? ?]]]].
    + right ; left ; now symmetry.
    + left ; now symmetry.
    + tauto.
    + tauto.
Defined.

(* We work towards a general theorem: the number of vertices with odd degree is odd. *)

(** Given a decidable predicate [P] on [nat], we can count how many numbers up to [n] satisfy [P]. *)
Definition count:
  forall P : nat -> Prop,
    (forall x, {P x} + {~ P x}) -> nat -> nat.
Proof.
  intros P D n.
  induction n.
  - exact 0.
  - destruct (D n).
    + exact (1 + IHn).
    + exact IHn.
Defined.

(** Given a function [f : nat -> nat] and number [n], compute
    the sum of [f 0, f 1, ..., f (n-1)]. *)
Fixpoint sum (f : nat -> nat) (n : nat) :=
  match n with
  | 0 => 0
  | S m => f m + sum f m
  end.

(** The number of edges in a graph. *)
Definition edges (G : Graph) : nat :=
  sum (fun x => sum (fun y => if E_decidable G x y then 1 else 0) x) (V G).

(* An example: calculate how many edges are in various graphs. *)
Eval compute in edges (Cycle 2). (* NB: This is a cycle on 5 vertices. *)
Eval compute in edges (K 5).
Eval compute in edges (Empty 10).

(** The degree of a vertex. We define it so that it
    return 0 if we give it a number which is not
    a vertex. *)
Definition degree (G : Graph) (x : nat) : nat.
Proof.
  destruct (lt_dec x (V G)) as [ Hx | ? ].
  - { apply (count (fun y => y < G /\ G x y)).
      - intro z.
        destruct (lt_dec z G) as [Hz|?].
        + destruct (E_decidable G x z).
          * left ; tauto.
          * right ; tauto.
        + right ; tauto.
      - exact (V G). }
  - exact 0.
Defined.

(* Let us compute the degree of a vertex. *)
Eval compute in degree (K 6) 4.
Eval compute in degree (Cycle 4) 0.
Eval compute in degree (Cycle 4) 2.

(* If we sum up all the degress we get twice the edges. *)
Theorem sum_degrees (G : Graph) : sum (degree G) (V G) = 2 * (edges G).
Proof.
  (* We give up and go to lunch. *)
Admitted. 
*)

Definition vertex := nat.
Definition vertex_list := list nat.

Check hd.
Check ((hd true []) = true).

Inductive walk (g : Graph) : vertex_list -> Prop :=
| null : walk g []
| one : forall (u v : vertex), is_some (E g u v) -> walk g [u;v]
| step : forall (u v w : vertex) (p p' : vertex_list), 
  walk g p -> is_some (E g u v) -> p = w::p' -> v = w -> walk g (u::p).

Compute last [] 0.
Compute hd 0 [] .
Definition path g p := walk g p /\ NoDup p.
Definition cycle g p := walk g p /\ (hd 0 p = last p 0).

Fixpoint walkb g p := 
match p with 
| [] => true
| x::xs =>
  match xs with 
  | [] => S.mem x (V g)
  | y::ys => andb (is_someb (E g x y)) (walkb g xs)
  end
end.


Class Eq A : Type := 
  { 
    eqb : A -> A -> bool
  }.

Instance eqNat : Eq nat := 
  { eqb := Nat.eqb }.

Instance eqPair {A B : Type} `{Eq A} `{Eq B} : Eq (A * B) :=
  {|
    eqb p1 p2 :=
      let (p1a,p1b) := p1 : A * B in
      let (p2a,p2b) := p2 : A * B in
      andb (eqb p1a p2a) (eqb p1b p2b)
  |}.

Class EqDec {A : Type} `{Eq A} : Type :=
  {
    eqb_eq : forall x y, eqb x y = true <-> x = y 
  }.

Definition elem {X : Type} `{Eq X} (x : X) l := 
existsb (fun x' => eqb x x') l.

Check find.

Compute (elem ((2,2),3) []).
Open Scope bool.

Fixpoint NoDupb (l : list nat) := 
match l with 
| [] => true
| x::xs => 
  negb (elem x xs) && NoDupb xs
end.

Definition pathb g p := andb (walkb g p) (NoDupb p).

Compute pathb (K 3) [0;1;2].

Goal (walk (K 5) [1;2;3;4]).
Proof.
apply (step (K 5) 1 2 2 [2;3;4] [3;4]).
- apply (step (K 5) 2 3 3 [3;4] [4]). 
  + apply one. simpl. reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.

Definition subgraph g g' := 
S.subset (V g') (V g) &&
S.for_all (fun v1 => S.for_all (
  fun v2 => if is_someb (E g' v1 v2) then is_someb (E g v1 v2) else true)
   (V g')) (V g').

(* Definition from_list : list ((nat * nat) * nat) -> Graph := 
fun l => 
{|
  V := S.empty;
  E := fun x y => 
    match find (fun x => match x with (e,w) => eqb (x,y) e end) l with
    | Some (_,w) => Some w 
    | _ => None end
|}. 
  

Check from_list. 

 *)
  