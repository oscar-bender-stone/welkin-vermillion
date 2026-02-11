(* SPDX-FileCopyrightText: 2026 Oscar Bender-Stone <oscar-bender-stone@protonmail.com> *)
(* SPDX-FileContributor: Gemini (Google) *)
(* SPDX-License-Identifier: BSD-3-Clause*)


Require Import String.
Require Import Ascii.
Require Import List.
Require Import Grammar.
Require Import Main.
Require Import Generator.

Import ListNotations.
Open Scope string_scope.

(* ========================================================================== *)
(* 1. AST: THE GRAPH                                                          *)
(* ========================================================================== *)

(* An Edge connects two names via an operator *)
Inductive Edge := 
| Link (op : string) (src : string) (dst : string).

(* A Graph is a recursive structure containing Sub-Graphs and Edges *)
Inductive Graph := 
| Def (name : string) (depth : nat) (subs : list Graph) (edges : list Edge).

(* Helper: Flattening two results (lists of graphs and edges) *)
Definition merge_results (r1 r2 : (list Graph * list Edge)) :=
  match r1, r2 with
  | (g1, e1), (g2, e2) => (g1 ++ g2, e1 ++ e2)
  end.

(* Helper: Create a basic Graph (node) from a path. 
   Note: The created graph starts with empty subs/edges. *)
Fixpoint make_graph (depth : nat) (path : list string) : Graph :=
  match path with
  | [] => Def "" 0 [] []
  | [x] => Def x depth [] []
  | x :: xs => Def x depth [make_graph 0 xs] []
  end.

(* Helper: Extract name for linking *)
Definition get_name (g : Graph) : string :=
  match g with
  | Def n _ _ _ => n
  end.

(* ========================================================================== *)
(* 2. GRAMMAR SYMBOLS                                                         *)
(* ========================================================================== *)

Inductive terminal_def :=
| Id | Dot | Comma      
| Hyphen   (* -  *)
| RArrow   (* -> *)
| LArrow.  (* <- *)

Inductive nonterminal_def :=
| Welkin        (* Root: Returns the final Graph *)
| Body          (* The content: returns (list Graph * list Edge) *)
| Chain         (* A sequence *)
| Path          (* A specific node path *)
| Prefix        (* Leading dots *)
| Suffix        (* Trailing segments *)
| Segment       (* Identifier *)
(* --- Directional State Machine --- *)
| ChainNeutral  (* Saw '-', can go Left or Right next *)
| ChainRight    (* Saw '->', locked into Rightward flow *)
| ChainLeft.    (* Saw '<-', locked into Leftward flow *)

(* ========================================================================== *)
(* 3. SEMANTICS                                                               *)
(* ========================================================================== *)

Definition t_semty_def (a : terminal_def) : Type :=
  match a with
  | Id => string
  | _  => unit
  end.

(* Context Types:
   - Welkin returns a single Graph.
   - Body/Chain return the raw lists (Payload).
   - Chain States take the *Previous Graph* and return the rest of the Payload.
*)
Definition Payload := (list Graph * list Edge).

Definition nt_semty_def (x : nonterminal_def) : Type :=
  match x with
  | Welkin       => Graph
  | Body         => Payload
  | Chain        => Payload
  | Path         => (nat * list string)
  | Prefix       => nat
  | Suffix       => list string
  | Segment      => string
  (* Flow Control: Takes the previous node, returns the resulting payload *)
  | ChainNeutral => Graph -> Payload
  | ChainRight   => Graph -> Payload
  | ChainLeft    => Graph -> Payload
  end.

(* Boilerplate *)
Lemma t_eq_dec_def : forall (t t' : terminal_def), {t = t'} + {t <> t'}.
Proof. decide equality. Defined.
Lemma nt_eq_dec_def : forall (nt nt' : nonterminal_def), {nt = nt'} + {nt <> nt'}.
Proof. decide equality. Defined.

(* ========================================================================== *)
(* 4. MODULE CONFIGURATION                                                    *)
(* ========================================================================== *)

Module Welkin_Types <: SYMBOL_TYPES 
  with Definition terminal := terminal_def
  with Definition nonterminal := nonterminal_def
  with Definition t_semty := t_semty_def
  with Definition nt_semty := nt_semty_def.

  Definition terminal := terminal_def.
  Definition nonterminal := nonterminal_def.
  Definition t_semty := t_semty_def.
  Definition nt_semty := nt_semty_def.
  Definition t_eq_dec := t_eq_dec_def.
  Definition nt_eq_dec := nt_eq_dec_def.

  Definition showT (a : terminal) : string := 
    match a with 
    | Id => "Id" | Dot => "." | Comma => ","
    | Hyphen => "-" | RArrow => "->" | LArrow => "<-"
    end.
  Definition showNT (x : nonterminal) : string := "nt".
End Welkin_Types.

Module Export G <: Grammar.T 
  with Module SymTy := Welkin_Types.
  Module Export SymTy := Welkin_Types.
  Module Export Defs  := DefsFn SymTy.
End G.
Module Export Gen := GeneratorFn G.

(* ========================================================================== *)
(* 5. GRAMMAR RULES                                                           *)
(* ========================================================================== *)

Definition rule := existT action_ty.

Definition grammar_def : grammar :=
  {| start := Welkin;
     prods := [
       (* --- ROOT --- *)
       (* Wraps the parsed lists into a single "Root" Graph *)
       rule (Welkin, [NT Body])
            (fun args => match args with (subs, edges) => 
                           Def "root" 0 subs edges 
                         end);

       (* --- BODY (Comma Separated) --- *)
       rule (Body, [NT Chain; T Comma; NT Body])
            (fun args => match args with (head_p, (_, (tail_p, _))) => 
                           merge_results head_p tail_p
                         end);
       rule (Body, []) (fun _ => ([], []));

       (* --- CHAIN START --- *)
       (* Path -> Graph -> Neutral State *)
       rule (Chain, [NT Path; NT ChainNeutral])
            (fun args => match args with ((d, p), (rest_fn, _)) => 
                           let start_node := make_graph d p in
                           let (rest_nodes, rest_edges) := rest_fn start_node in
                           (start_node :: rest_nodes, rest_edges)
                         end);

       (* =================================================================== *)
       (* FLOW CONTROL: NEUTRAL                                               *)
       (* Can transition to Hyphen, Right, or Left                            *)
       (* =================================================================== *)
       
       (* 1. Hyphen (-). Stay Neutral. *)
       rule (ChainNeutral, [T Hyphen; NT Path; NT ChainNeutral])
            (fun args => match args with (_, ((d, p), (next_fn, _))) => 
               fun prev =>
                 let curr := make_graph d p in
                 let edge := Link "-" (get_name prev) (get_name curr) in
                 let (rest_g, rest_e) := next_fn curr in
                 (curr :: rest_g, edge :: rest_e)
             end);

       (* 2. RArrow (->). Lock to Right. *)
       rule (ChainNeutral, [T RArrow; NT Path; NT ChainRight])
            (fun args => match args with (_, ((d, p), (next_fn, _))) => 
               fun prev =>
                 let curr := make_graph d p in
                 let edge := Link "->" (get_name prev) (get_name curr) in
                 let (rest_g, rest_e) := next_fn curr in
                 (curr :: rest_g, edge :: rest_e)
             end);

       (* 3. LArrow (<-). Lock to Left. *)
       rule (ChainNeutral, [T LArrow; NT Path; NT ChainLeft])
            (fun args => match args with (_, ((d, p), (next_fn, _))) => 
               fun prev =>
                 let curr := make_graph d p in
                 let edge := Link "<-" (get_name curr) (get_name prev) in
                 let (rest_g, rest_e) := next_fn curr in
                 (curr :: rest_g, edge :: rest_e)
             end);

       rule (ChainNeutral, []) (fun _ => fun _ => ([], []));

       (* =================================================================== *)
       (* FLOW CONTROL: RIGHT ONLY (->, -)                                    *)
       (* Rejects LArrow                                                      *)
       (* =================================================================== *)
       
       rule (ChainRight, [T RArrow; NT Path; NT ChainRight])
            (fun args => match args with (_, ((d, p), (next_fn, _))) => 
               fun prev =>
                 let curr := make_graph d p in
                 let edge := Link "->" (get_name prev) (get_name curr) in
                 let (rest_g, rest_e) := next_fn curr in
                 (curr :: rest_g, edge :: rest_e)
             end);

       rule (ChainRight, [T Hyphen; NT Path; NT ChainRight])
            (fun args => match args with (_, ((d, p), (next_fn, _))) => 
               fun prev =>
                 let curr := make_graph d p in
                 let edge := Link "-" (get_name prev) (get_name curr) in
                 let (rest_g, rest_e) := next_fn curr in
                 (curr :: rest_g, edge :: rest_e)
             end);

       rule (ChainRight, []) (fun _ => fun _ => ([], []));

       (* =================================================================== *)
       (* FLOW CONTROL: LEFT ONLY (<-, -)                                     *)
       (* Rejects RArrow                                                      *)
       (* =================================================================== *)

       rule (ChainLeft, [T LArrow; NT Path; NT ChainLeft])
            (fun args => match args with (_, ((d, p), (next_fn, _))) => 
               fun prev =>
                 let curr := make_graph d p in
                 let edge := Link "<-" (get_name curr) (get_name prev) in
                 let (rest_g, rest_e) := next_fn curr in
                 (curr :: rest_g, edge :: rest_e)
             end);

       rule (ChainLeft, [T Hyphen; NT Path; NT ChainLeft])
            (fun args => match args with (_, ((d, p), (next_fn, _))) => 
               fun prev =>
                 let curr := make_graph d p in
                 let edge := Link "-" (get_name curr) (get_name prev) in
                 let (rest_g, rest_e) := next_fn curr in
                 (curr :: rest_g, edge :: rest_e)
             end);

       rule (ChainLeft, []) (fun _ => fun _ => ([], []));

       (* --- PATH HELPERS --- *)
       rule (Path, [NT Prefix; NT Segment; NT Suffix])
            (fun args => match args with (d, (s, (tail, _))) => (d, s :: tail) end);

       rule (Prefix, [T Dot; NT Prefix])
            (fun args => match args with (_, (n, _)) => S n end);
       rule (Prefix, []) (fun _ => 0);

       rule (Suffix, [T Dot; NT Segment; NT Suffix])
            (fun args => match args with (_, (s, (tail, _))) => s :: tail end);
       rule (Suffix, []) (fun _ => []);

       rule (Segment, [T Id]) (fun args => match args with (s, _) => s end)
     ]
  |}.

(* ========================================================================== *)
(* 6. SCANNER                                                                 *)
(* ========================================================================== *)

Definition mk_tok (a : terminal) (v : t_semty a) : token :=
  existT _ a v.

Definition is_delim (c : ascii) : bool :=
  let n := nat_of_ascii c in
  if (n =? 46)%nat then true      (* . *)
  else if (n =? 44)%nat then true (* , *)
  else if (n =? 45)%nat then true (* - *)
  else if (n =? 62)%nat then true (* > *)
  else if (n =? 60)%nat then true (* < *)
  else if (n =? 32)%nat then true (* Space *)
  else if (n =? 9)%nat  then true (* Tab *)
  else if (n =? 10)%nat then true (* LF *)
  else if (n =? 13)%nat then true (* CR *)
  else false.

Fixpoint span_ident (s : string) : string * string :=
  match s with
  | EmptyString => ("", "")
  | String c rest =>
      if is_delim c then ("", s)
      else 
        let (id, remaining) := span_ident rest in
        (String c id, remaining)
  end.

Fixpoint tokenize_aux (fuel : nat) (s : string) : list token :=
  match fuel with
  | 0 => []
  | S n =>
    match s with
    | EmptyString => []
    | String c rest =>
        let code := nat_of_ascii c in
        if (code =? 32)%nat then tokenize_aux n rest
        else if (code =? 9)%nat  then tokenize_aux n rest
        else if (code =? 10)%nat then tokenize_aux n rest
        else if (code =? 13)%nat then tokenize_aux n rest
        else if (code =? 46)%nat then mk_tok Dot tt :: tokenize_aux n rest
        else if (code =? 44)%nat then mk_tok Comma tt :: tokenize_aux n rest
        else if (code =? 45)%nat then 
             match rest with
             | String c2 rest2 => 
               if (nat_of_ascii c2 =? 62)%nat 
               then mk_tok RArrow tt :: tokenize_aux n rest2
               else mk_tok Hyphen tt :: tokenize_aux n rest
             | EmptyString => mk_tok Hyphen tt :: []
             end
        else if (code =? 60)%nat then
             match rest with
             | String c2 rest2 =>
               if (nat_of_ascii c2 =? 45)%nat
               then mk_tok LArrow tt :: tokenize_aux n rest2
               else tokenize_aux n rest 
             | EmptyString => []
             end
        else 
          let (id, remaining) := span_ident s in
          mk_tok Id id :: tokenize_aux n remaining
    end
  end.

Definition tokenize (s : string) : list token :=
  tokenize_aux (String.length s) s.

Module Import PG := Make G.

(* ========================================================================== *)
(* 7. DEMONSTRATION                                                           *)
(* ========================================================================== *)

(* Valid Input:
   1. a - b -> c  (Neutral -> Right)
   2. d <- e - f  (Left -> Left_via_hyphen)
*)
Definition input : string := "a - b -> c, d <- e - f,"%string.

Compute (match parseTableOf grammar_def with
         | inl msg => inl msg
         | inr tbl => inr (parse tbl (NT Welkin) (tokenize input))
         end).
