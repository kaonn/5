Require Import List.
Require Import MSets Arith.
Require Import Coq.Numbers.NaryFunctions.
From Template Require Import All.
Import ListNotations MonadNotation.
Require Export Coq.Strings.String.
Require Import Ascii.
Extraction Language Haskell.

Definition printInductive (name  : ident): TemplateMonad unit :=
  (tmBind (tmQuoteInductive name) tmPrint).

Run TemplateProgram (t <- tmQuoteInductive "nat";; tmPrint t).
Run TemplateProgram (r <- tmQuote nat;; tmPrint r).


Inductive a : Type := 
| A : a.

Inductive b : Type := 
| B : b
| Ba : a -> b
| Baa : a -> b -> b.

Run TemplateProgram (t <- tmQuoteInductive "b";; tmPrint t).

Run TemplateProgram (t<- (tmQuote (nat -> nat));; t <- tmUnquoteTyped Set t;; tmPrint t).

Definition str_eq s1 s2 := match string_dec s1 s2 with left _ => true | _ => false end. 
Definition ascii_eq c1 c2 := match ascii_dec c1 c2 with left _ => true | _ => false end. 

Fixpoint map_ {A B} (f : A -> TemplateMonad B) (l : list A) : TemplateMonad (list B) :=
match l with 
| [] => tmReturn []
| x::xs => r <- f x ;; rs <- map_ f xs ;; tmReturn (r::rs)
end.

Fixpoint split_until (f : ascii -> bool) s :=
match s with 
| EmptyString => (EmptyString, EmptyString)
| String c xs => 
  if f c then (String c EmptyString, xs)
  else
  let (a,b) := split_until f xs in 
  (String c a,b)
end.

Compute split_until (ascii_eq ".") "fd.a".
Fixpoint strip s dummy {struct dummy} := 
let (a,b) := split_until (ascii_eq ".") s in
match b with 
| EmptyString => s
| _ => match dummy with 
  | 0 => EmptyString
  | S n' => strip b n'
  end
end.

Compute strip "Coq.Init.Datatypes.nat" 100.
 
Check fold_left.

Fixpoint enumerate (ind : Type) (n : nat) : TemplateMonad (list ind) := 
tm <- tmQuote ind;; match tm with 
| tInd ind' _ => 
let qualified := inductive_mind ind' in
let indName := strip qualified (length qualified) in
decl <- tmQuoteInductive indName ;;
indBody <- 
  match find (fun body => str_eq (ind_name body) indName) (ind_bodies decl) with 
  | Some e => tmReturn e
  | _ => tmFail (append "fail" indName)
  end;;
let find_base := (fun body => 
  let cstrs := ind_ctors body in 
  filter (fun cstr => match cstr with (_,_,0) => true | _ => false end) cstrs)
in
let find_ind := 
  (fun body => 
  let cstrs := ind_ctors body in 
  filter (fun cstr => match cstr with (_,_,0) => false | _ => true end) cstrs)
in 
(match n with 
| 0 => map_ (fun cstr => match cstr with (tn,_,_) => tmUnquoteTyped ind (tConstruct (mkInd indName 0) 0 [])  end) 
    (find_base indBody)
| S n' => 
  let cstrs := find_ind indBody in 
  let flatten := fix f tm' := 
    match tm' with 
    | tRel _ => [tm]
    | tInd ind _ => tm'
    | tProd _ tm1 tm2 => f tm1 ++ f tm2
    end
  in
  let get_args l := removelast (flatten l) in
  map_ (fun acc cstr => match cstr with 
    | (name, tm, arity) => 
      all_args <- map_ (fun arg => ty <- tmUnquote arg;; enumerate (projT2 ty) n') (get_args tm);;
      let combined := map (fun args => 
          
    end) cstrs 
end)
| _ => tmFail "non inductive type"
end.
  
Check enumerate.
Run TemplateProgram (r <- enumerate nat 0;; tmPrint r).

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