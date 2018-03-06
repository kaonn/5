Require Import Bauer.
Require Import List.
Require Import synth.

Import ListNotations.


(* We can make a set out of an ordered type *)


Definition instance := Graph.
Definition solution := S.t.

Definition metric := nat.
Definition eval := S.cardinal.
Definition better (m1 m2 : metric) := m1 <=? m2.

Definition verifier (I : instance) (S : solution) :=  
S.For_all (fun v1 => S.For_all (fun v2 => is_some (E I v1 v2) -> S.In v1 S \/ S.In v2 S) (V I)) (V I).

Fixpoint checker (I : instance) (S : solution) := 
let v_set := V I in 
S.for_all (fun v1 => S.for_all (
  fun v2 => match (E I v1 v2) with Some _ => orb (S.mem v1 S) (S.mem v2 S) | _ =>  true end)
   v_set) v_set .

Definition gen_space := fun I => all_subset (V I).

Definition min_Vc_brute_force := synthesize instance solution metric checker eval better gen_space.

Compute S.elements (match min_Vc_brute_force (K 3) with | None => S.empty | Some s => s end).
