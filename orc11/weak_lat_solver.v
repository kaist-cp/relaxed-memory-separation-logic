From Ltac2 Require Import Ltac2 Printf.
Set Default Proof Mode "Classic".

From orc11 Require Import base view.
From diaframe.steps Require Import ltac2_store ipm_hyp_utils.

(* general graph stuff *)
Ltac2 Type rec graph_node := {
  value : constr;
  above : (constr, graph_node) store.t
}.

Ltac2 Type graph := {
  node_map : (constr, graph_node) store.t
}.


Ltac2 new_graph () : graph :=
  { node_map := store.new Constr.equal }.

Ltac2 new_graph_node (c : constr) : graph_node :=
  { value := c; above := store.new Constr.equal }.

Ltac2 get_or_create_node_for (g : graph) (n : constr) : graph_node :=
  store.get_or_set (g.(node_map)) n new_graph_node.

Ltac2 add_graph_edge (g : graph) (l : constr) (r : constr) : unit :=
  let l_node := get_or_create_node_for g l in
  let r_node := get_or_create_node_for g r in
  store.set (l_node.(above)) r r_node.

Ltac2 store_iter (s : ('k, 'v) store.t) (f : 'k -> 'v -> unit) : unit :=
  List.iter (fun pr =>
    let (k, v) := pr in
    f k v
  ) (store.to_list s).

Ltac2 pop_first (s : ('k, 'v) store.t) : ('k * 'v) option :=
  match s.(store.the_store) with
  | None => None
  | Some s' =>
    let key := (s'.(store.key)) in
    let value := (s'.(store.value)) in
    store.remove s key;
    Some (key, value)
  end.


Ltac2 rec get_above_int (g : graph)
  (result : (constr, constr list) store.t)
  (queue : (constr, constr list) store.t) : unit :=
  match pop_first queue with
  | None => ()
  | Some pr =>
    let (l, p) := pr in
    match store.get (g.(node_map)) l with
    | None => () (* can happen if goal is unrelated to lat hyps *)
    | Some n' =>
      store_iter (n'.(above)) (fun r rn =>
        match store.get result r with
        | Some _ => ()
        | None =>
          store.set result r (p);
          store.set queue r (r :: p)
        end
      );
      get_above_int g result queue
    end
  end.

Ltac2 get_above (g : graph) (l : constr) : (constr, constr list) store.t :=
  let result := store.new Constr.equal in
  let queue := store.new Constr.equal in
  store.set queue l [];
  get_above_int g result queue;
  result.



(* now for the lattice specific stuff: add support for meets (but not for the universal property) *)

Ltac2 rec add_meet_edge (g : graph) (m : constr) :=
  lazy_match! m with
  | ?l ⊔ ?r =>
    add_graph_edge g l m;
    add_graph_edge g r m;
    add_meet_edge g l;
    add_meet_edge g r
  | _ => ()
  end.

Ltac2 add_meet_edges (g : graph) : unit :=
  let meets := List.filter (fun c =>
    lazy_match! c with
    | ?l ⊔ ?r => true
    | _ => false
    end
  ) (List.map (fun pr => let (c, _) := pr in c) (store.to_list (g.(node_map)))) in
  List.iter (fun c => add_meet_edge g c) meets.

Ltac2 construct_lat_graph_from_hyps () : graph :=
  let result := new_graph () in
  List.iter (fun pr =>
    let (_, _, type) := pr in
    lazy_match! type with
    | ?l ⊑ ?r =>
      add_graph_edge result l r
    | _ => ()
    end
  ) (Control.hyps ());
  add_meet_edges result;
  result.


Ltac prove_easy_lat_ineq :=
  assumption || apply lat_join_sqsubseteq_l || apply lat_join_sqsubseteq_r.


(* we provide some ad-hoc support for proving things like
  [a ⊔ b ⊑ a ⊔ b ⊔ c]
  this cannot currently be done directly, since we do not encode the lub property
  of meets.
  The approach is: simply apply [lat_join_lub] if we meet a goal of this shape
*)

Ltac2 base_weak_lat_solver (g : graph) :=
  lazy_match! goal with
  | [ |- ?l ⊑ ?r ] =>
    add_meet_edge g l;
    add_meet_edge g r;
    let above_store := (get_above g l) in
    let result := (store.get above_store r) in
    match result with
    | None => ltac1:(prove_easy_lat_ineq) (* fallback option *)
    | Some p =>
      List.iter (fun c =>
        ltac1:(pel |- trans pel; [prove_easy_lat_ineq | ]) (Ltac1.of_constr c)
      ) (List.rev p); ltac1:(prove_easy_lat_ineq)
    end
  end.


Ltac2 rec divide_toplevel_meets (g : graph) :=
  lazy_match! goal with
  | [ |- ?l1 ⊔ ?l2 ⊑ ?r ] =>
    apply lat_join_lub > [ divide_toplevel_meets g | divide_toplevel_meets g]
  | [ |- ?l ⊑ ?r ] =>
    base_weak_lat_solver g
  end.


Ltac weak_lat_solver :=
  (* this solver is weaker since it is not set up to use the universal property of meets,
    i.e. it cannot derive [X ⊑ Z → Y ⊑ Z → X ⊔ Y ⊑ Z]. But it should be much faster than
    [solve_lat], especially when [solve_lat] fails *)
  ltac2:(
    lazy_match! goal with
    | [ |- ?l ⊑ ?l] => reflexivity
    | [ |- ?l ⊑ ?r] =>
      first [solve [ltac1:(prove_easy_lat_ineq)] | (
        let g := construct_lat_graph_from_hyps () in
        divide_toplevel_meets g
      )]
    end
  ).


Lemma test (V x5 x6 x12 x14 x25 x10 x28 x9 : view) :
  (V ⊑ x5) →
  (x5 ⊑ x6) →
  (x6 ⊑ x12) →
  (x12 ⊑ x14) →
  (x14 ⊑ x25) →
  (x25 ⊔ x10 ⊑ x28) →
  (x28 ⊑ x9) →
  (x5 ⊑ x9).
Proof. intros. weak_lat_solver. Qed.

Lemma test_graceful_failure (V1 V2 : view) : V1 ⊑ V2 ∨ True.
Proof. (left; weak_lat_solver) || (right; exact I). Qed.

Lemma test_toplevel_meet_works (V x5 x6 x12 x14 x25 x10 x28 x9 : view) :
  (V ⊔ x5) ⊔ x6 ⊑ V ⊔ (x5 ⊔ x12) ⊔ (x25 ⊔ x6).
Proof. weak_lat_solver. Qed.


