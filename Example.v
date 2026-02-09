(* SPDX-FileCopyrightText: 2026 Oscar Bender-Stone <oscar-bender-stone@protonmail.com> *)
(* SPDX-FileContributor: Gemini (Google) *)
(* SPDX-License-Identifier: BSD-3-Clause*)


Require Import String.
Require Import Ascii.
Require Import List.
Require Import ZArith.
Require Import PeanoNat.
Require Import Grammar.
Require Import Main.
Require Import Generator.

Import ListNotations.
Open Scope string_scope.

(* ========================================================================== *)
(* 1. AST                                                                     *)
(* ========================================================================== *)

(* A Node represents a hierarchical path element (e.g., ...std.io) *)
Inductive Node :=
| Def (name : string) (depth : nat) (contents : list Node).

(* An Entry is a single resulting object in our list (a standalone Node or an Edge) *)
Inductive Entry :=
| Atom    (n : Node)
| Connect (op : string) (src : Node) (dst : Node).

(* Helper to convert path parts into a Node *)
Fixpoint make_node (depth : nat) (path : list string) : Node :=
  match path with
  | [] => Def "" 0 [] 
  | [x] => Def x depth []
  | x :: xs => Def x depth [make_node 0 xs]
  end.

(* ========================================================================== *)
(* 2. GRAMMAR SYMBOLS                                                         *)
(* ========================================================================== *)

Inductive terminal_def :=
| Id | Dot | Comma      (* Basic *)
| Hyphen                (* -  *)
| RArrow                (* -> *)
| LArrow.               (* <- *)

Inductive nonterminal_def :=
| Welkin        (* Root *)
| Entries       (* List of comma-separated entries *)
| Chain         (* A sequence: A -> B <- C *)
| Link          (* The recursive link in a chain *)
| Operator      (* The arrow symbol *)
| Path          (* A full path: ...a.b *)
| Prefix        (* Leading dots *)
| Suffix        (* Trailing segments *)
| Segment.      (* Single identifier *)

(* ========================================================================== *)
(* 3. SEMANTICS                                                               *)
(* ========================================================================== *)

Definition t_semty_def (a : terminal_def) : Type :=
  match a with
  | Id => string
  | _  => unit
  end.

(* Link is a function:
   It takes the 'previous' Node (context) and returns a list of resulting Entries.
*)
Definition nt_semty_def (x : nonterminal_def) : Type :=
  match x with
  | Welkin    => list Entry
  | Entries   => list Entry
  | Chain     => list Entry
  | Link      => Node -> list Entry
  | Operator  => string 
  | Path      => (nat * list string)
  | Prefix    => nat
  | Suffix    => list string
  | Segment   => string
  end.

Lemma t_eq_dec_def : forall (t t' : terminal_def), {t = t'} + {t <> t'}.
Proof. decide equality. Defined.

Lemma nt_eq_dec_def : forall (nt nt' : nonterminal_def), {nt = nt'} + {nt <> nt'}.
Proof. decide equality. Defined.

(* ========================================================================== *)
(* 4. MODULE BOILERPLATE                                                      *)
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
       rule (Welkin, [NT Entries])
            (fun args => match args with (l, _) => l end);

       (* --- ENTRIES (Comma Separated) --- *)
       rule (Entries, [NT Chain; T Comma; NT Entries])
            (fun args => match args with (head, (_, (tail, _))) => 
                           head ++ tail 
                         end);

       rule (Entries, []) (fun _ => []);

       (* --- CHAIN --- *)
       (* Chain -> Path Link *)
       rule (Chain, [NT Path; NT Link])
            (fun args => match args with ((d, p), (link_fn, _)) => 
                           let start := make_node d p in
                           (Atom start) :: (link_fn start)
                         end);

       (* --- LINK (Recursive Arrow Logic) --- *)
       (* Link -> Operator Path Link *)
       rule (Link, [NT Operator; NT Path; NT Link])
            (fun args => match args with (op, ((d, p), (next_link_fn, _))) => 
                           fun prev =>
                             let curr := make_node d p in
                             
                             (* Determine direction based on operator *)
                             let edge := 
                               if string_dec op "<-" 
                               then Connect "<-" curr prev (* B -> A *)
                               else Connect "->" prev curr (* A -> B *)
                             in
                             
                             (* Result: Edge + Atom(curr) + Recursion *)
                             edge :: (Atom curr) :: (next_link_fn curr)
                         end);

       rule (Link, [])
            (fun _ => fun _ => []);

       (* --- OPERATORS --- *)
       rule (Operator, [T Hyphen]) (fun _ => "-"%string);
       rule (Operator, [T RArrow]) (fun _ => "->"%string);
       rule (Operator, [T LArrow]) (fun _ => "<-"%string);

       (* --- PATH --- *)
       rule (Path, [NT Prefix; NT Segment; NT Suffix])
            (fun args => match args with (d, (s, (tail, _))) => (d, s :: tail) end);

       (* --- PREFIX (...) --- *)
       rule (Prefix, [T Dot; NT Prefix])
            (fun args => match args with (_, (n, _)) => S n end);
       rule (Prefix, []) (fun _ => 0);

       (* --- SUFFIX (.b.c) --- *)
       rule (Suffix, [T Dot; NT Segment; NT Suffix])
            (fun args => match args with (_, (s, (tail, _))) => s :: tail end);
       rule (Suffix, []) (fun _ => []);

       (* --- PRIMITIVES --- *)
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
        (* SKIP WHITESPACE *)
        if (code =? 32)%nat then tokenize_aux n rest
        else if (code =? 9)%nat  then tokenize_aux n rest
        else if (code =? 10)%nat then tokenize_aux n rest
        else if (code =? 13)%nat then tokenize_aux n rest
        
        (* SYMBOLS *)
        else if (code =? 46)%nat then mk_tok Dot tt :: tokenize_aux n rest
        else if (code =? 44)%nat then mk_tok Comma tt :: tokenize_aux n rest
        
        (* ARROWS *)
        (* - or -> *)
        else if (code =? 45)%nat then 
             match rest with
             | String c2 rest2 => 
               if (nat_of_ascii c2 =? 62)%nat 
               then mk_tok RArrow tt :: tokenize_aux n rest2 (* -> *)
               else mk_tok Hyphen tt :: tokenize_aux n rest (* - *)
             | EmptyString => mk_tok Hyphen tt :: []
             end
        (* <- *)
        else if (code =? 60)%nat then
             match rest with
             | String c2 rest2 =>
               if (nat_of_ascii c2 =? 45)%nat
               then mk_tok LArrow tt :: tokenize_aux n rest2 (* <- *)
               else tokenize_aux n rest (* < alone is ignored or error, skipping here *)
             | EmptyString => []
             end
        
        (* IDENTIFIERS *)
        else 
          let (id, remaining) := span_ident s in
          mk_tok Id id :: tokenize_aux n remaining
    end
  end.

Definition tokenize (s : string) : list token :=
  tokenize_aux (String.length s) s.

Module Import PG := Make G.

(* --- Execution --- *)

(* Input: "a -> b <- c, d," *)
(* Logic: 
   1. a -> b (Connect a to b)
   2. b <- c (Connect c to b)
   3. d (Atom)
*)
Definition input : string := "a -> b <- c, d,"%string.

Compute (match parseTableOf grammar_def with
         | inl msg => inl msg
         | inr tbl => inr (parse tbl (NT Welkin) (tokenize input))
         end).
