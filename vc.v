Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Bool_nat.
Require Import Init.Nat.
Import ListNotations.

Definition vertex := nat.
Definition edge := prod vertex vertex.
Record graph := Graph
{
  v_list : list vertex;
  e_list : list edge;
}. 

Definition cover := list edge.

Definition size (c : cover) := length c.

Definition gt n m := negb (n <=? m).

Definition empty : graph := Graph [] [].

Definition incident (v : vertex) (e : edge) := 
match e with 
| (x,y) => x = v \/ y = v
end.

Definition incident_b (v : vertex) (e : edge) := 
match e with 
| (x,y) => orb (x =? v) (y =? v)
end.

Definition is_cover (es : cover) (g : graph) := 
incl es (e_list g) /\
forall v : vertex, In v (v_list g) -> 
  ex (fun e => In e (e_list g) /\ incident v e).

Fixpoint elem {X : Type} (f : X -> X -> bool) e l := 
match l with 
| [] => false
| x::xs => if f e x then true else elem f e xs
end.

Definition incl_b {X : Type} f (l m : list X) := forallb (fun x => elem f x m) l.
Definition is_cover_b (es : cover) (g : graph) := 
andb 
(incl_b (fun e1 e2 => match (e1,e2) with ((x1,y1),(x2,y2)) => andb (eqb x1 x2) (eqb y1 y2) end)
 es (e_list g))
(forallb (fun v => existsb (incident_b v) es) (v_list g)).

Theorem trivial_cover : forall c : cover,  is_cover c empty.
Proof.
intros.
compute.
intros.

inversion H.
Qed.

Fixpoint split_i {X : Type} (i : nat) (l : list X) :=
if i =? 0 then ([], l) else
match l with 
| [] => ([],[])
| x::xs => 
  let (u,v) := split_i (i - 1) xs in 
  (x::u,v)
end.

Compute (split_i 10 [1;2;3;4;2]). 
Compute 4 - 5.

Fixpoint fold_l_i {X Y : Type} (init : nat) (f : nat -> Y -> X -> Y) (y : Y) (l : list X) :=
let i := init - (length l) in 
match l with 
| [] => y 
| x::xs => fold_l_i init f (f i y x) xs
end.

Compute (fold_l_i 5 (fun i y x => i::y) [] [9;0;0;0;0]).

Fixpoint tabulate {X : Type} (len : nat) (f : nat -> X) : list X := 
let fix tab (i : nat) := 
  match i with 
  | 0 => []
  | S i' => f (len - i) :: tab i'
end
in
tab len.

Compute tabulate 5 (fun i => i).

Check map.
Check fold_left.

Definition flatten {X : Type} (l : list (list X)) := fold_left (fun x y => app x y) [] l. 

Fixpoint all_perm {X : Type} (l : list X) :=
match l with 
| [] => [[]]
| [x] => [[x]]
| x::xs => 
  let perms := all_perm xs in 
  fold_left (fun ps perm => 
    let perms' :=  
      tabulate (1 + length perm) (fun i => 
       let (a,b) := split_i i perm in a ++ [x] ++ b
      )
    in ps ++ perms') perms []
end.

Compute all_perm [1;2;3]. 
Compute list_power [1;2;3] [4;5].

Fixpoint all_subset {X : Type} (l : list X) := 
match l with 
| [] => [[]]
| x::xs => 
  let subsets := all_subset xs in 
  subsets ++ (map (fun e => x::e) subsets)
end.

Compute all_subset [1;2;3].
Check option.

Search (False -> _).
Check fold_left.
Definition min (l : list nat) d := fold_left (fun acc x => if x <? acc then x else acc) l d.

Fixpoint min_vc (g : graph) : option nat := 
let covers := filter (fun c => is_cover_b c g) (all_subset (e_list g)) in 
match covers with 
| [] => None
| x::xs => 
  let k := min (map (fun c => length c) covers) (length x) in 
    Some k
end.

Compute min_vc (Graph [1;2;3;4;5] [(1,2);(3,2);(3,4);(5,4)]). 

Theorem min_vc_correct : forall (k : nat) (g : graph), 
min_vc g = Some k -> ~ ex (fun c => is_cover c g /\  size c <= k).