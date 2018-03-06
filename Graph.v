Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Bool_nat.
Require Import Init.Nat.
Import ListNotations.

Definition vertex := nat.
Definition edge := prod vertex vertex.

Inductive graph {X : Type} : Set :=
| Empty : graph
| Add_node : forall (x : X) (g : graph), x 

Check " :> ".
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
Proof.
Admitted.