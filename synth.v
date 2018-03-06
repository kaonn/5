Require Import List.
Require Import MSets Arith.
Require Import Coq.Numbers.NaryFunctions.
Import ListNotations.

Extraction Language Haskell.

Inductive Ind (A : Type) (n : nat) : Type :=
{
  initial : A;
  arity : list (sigT (fun t => Ind t n) * sigT (fun t => t)) % type
}.

Check flat_map.
Compute list_power [1;2;3] [4;5].
Fixpoint IndNat (n : nat) : Ind nat := 
{| initial := 0;  
   arity := [
    (existT (fun t => Ind t) (nat) (IndNat 0), existT (fun t => t) (nat -> nat) S)
  ]
|}.

Instance IndProd {A B : Set} `{Ind A} `{Ind B} : Ind (prod A B)  := 
{
  initial := (initial, initial);
  arity := 
  let indA := arity in 
  let indB := arity in 
  
  flat_map (fun c1 : {x : Type & x} => map (fun c2 : {x : Type & x} => 
      existT (fun t => t) (prod (projT1 c1) (projT1 c2)) (projT2 c1, projT2 c2)
  ) indB) indA
}. 

Fixpoint enumerate {A : Type} `{Ind A} (n : nat ) : list A := 
let indA := arity in 
let f := 
  fix pay n acc := 
    if n =? 0 then acc
    else   
  

Class Eq A :=
  {
    eqb: A -> A -> bool;
  }.

Class Ord A `{Eq A} : Type :=
  {
    le : A -> A -> bool
  }.

Module S := Make Nat_as_OT.

Module SP := WPropertiesOn Nat_as_OT S.

Module SF := WFactsOn Nat_as_OT S.

Fixpoint tabulate f n := 
match n with 
| 0 => S.empty
| S n => S.add (f n) (tabulate f n)
end.

Fixpoint tabulate_list {X : Type} (f : nat -> X) n := 
match n with 
| 0 => []
| S n => cons (f n) (tabulate_list f n)
end.

Definition list_max {X : Type} (f : X -> X -> bool) l d := fold_left (fun acc e => if f acc e then acc else e) l d.

Fixpoint all_subset (s : S.t) := 
S.fold (fun e subsets => subsets ++ (map (fun s => S.add e s) subsets)) s [S.empty].


Definition split_i {X : Type} (i : nat) (l : list X) := (firstn i l, skipn i l).

Fixpoint all_perm {X : Type} (l : list X) :=
match l with 
| [] => [[]]
| [x] => [[x]]
| x::xs => 
  let perms := all_perm xs in 
  fold_left (fun ps perm => 
    let perms' :=  
      tabulate_list (fun i => 
       let (a,b) := split_i i perm in a ++ [x] ++ b
      ) (1 + length perm)
    in ps ++ perms') perms []
end.

Definition algorithm (instance solution metric : Type) f 
 (verifier : instance -> solution -> Prop)
 (eval : solution -> metric) 
 (better : metric -> metric -> Prop) := 
forall (I : instance) (Sol Cand : solution), 
  (f I = Some Sol -> verifier I Sol /\ ((verifier I Cand) -> better (eval Sol) (eval Cand)))
/\
  (f I = None -> ~exists Cand', verifier I Cand').

Definition synthesize (instance : Type) (solution : Type) (metric : Type)
(checker : instance -> solution -> bool) 
(eval : solution -> metric) 
(better : metric -> metric -> bool) 
(gen_space : instance -> list solution) 
: instance -> option solution := 
fun I => 
let candidates := filter (checker I) (gen_space I) in 
let ranks := map (fun cand => (eval cand, cand)) candidates in 
match ranks with 
| [] => None
| x::xs => Some (snd (list_max (fun e1 e2 => match e1, e2 with | (s1,_), (s2,_) => better s1 s2 end) xs x))
end.