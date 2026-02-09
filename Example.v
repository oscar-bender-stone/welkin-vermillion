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

(* Renamed WGraph -> WIG (Welkin Import Graph) *)
(* depth: counts the number of leading dots (relative import) *)
Inductive WIG :=
| MkWIG (name : string) (depth : nat) (contents : list WIG).

(* Renamed Welem -> WStmt (Welkin Statement) *)
Inductive WStmt :=
| WNode (g : WIG)
| WArc  (op : string) (src : WIG) (dst : WIG).

(* Helper to construct WIG from path data *)
(* d: depth, p: list of segments *)
Fixpoint path_to_wig (d : nat) (p : list string) : WIG :=
  match p with
  | [] => MkWIG "" 0 [] (* Should not happen in valid parse *)
  | [x] => MkWIG x d []
  | x :: xs => MkWIG x d [path_to_wig 0 xs]
  end.

(* ========================================================================== *)
(* 2. GRAMMAR SYMBOLS                                                         *)
(* ========================================================================== *)

Inductive terminal_def :=
| TokId       (* Identifiers *)
| TokDot      (* . *)
| TokHyphen   (* - *)
| TokArrow    (* -> *)
| TokComma.   (* , *)

Inductive nonterminal_def :=
| NtRoot        (* Start symbol *)
| NtStmtList    (* Comma-separated list *)
| NtChain       (* A path sequence: a -> b -> c *)
| NtChainTail   (* Recursive tail of chain *)
| NtPath        (* Full path: ...a.b *)
| NtRelPrefix   (* Leading dots: ... *)
| NtPathTail    (* Trailing path: .b.c *)
| NtSegment     (* Single identifier *)
| NtEdgeOp.     (* - or -> *)

(* ========================================================================== *)
(* 3. SEMANTICS                                                               *)
(* ========================================================================== *)

Definition t_semty_def (a : terminal_def) : Type :=
  match a with
  | TokId => string
  | _     => unit
  end.

(* NtChainTail is a function:
   It receives the WIG node parsed *immediately before* it.
   It returns a list of WStmts (the Arcs connecting to the next node).
*)
Definition nt_semty_def (x : nonterminal_def) : Type :=
  match x with
  | NtRoot        => list WStmt
  | NtStmtList    => list WStmt
  | NtChain       => list WStmt
  | NtChainTail   => WIG -> list WStmt
  | NtPath        => (nat * list string)
  | NtRelPrefix   => nat
  | NtPathTail    => list string
  | NtSegment     => string
  | NtEdgeOp      => string
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
    | TokId => "Id" | TokDot => "." | TokHyphen => "-" 
    | TokArrow => "->" | TokComma => "," 
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

Definition welkin_grammar : grammar :=
  {| start := NtRoot;
     prods := [
       (* --- ROOT --- *)
       (* Root -> StmtList *)
       rule (NtRoot, [NT NtStmtList])
            (fun args => match args with (l, _) => l end);

       (* --- STATEMENT LIST --- *)
       (* StmtList -> Chain , StmtList *)
       (* NOTE: Requires trailing comma for the last element or separated list *)
       rule (NtStmtList, [NT NtChain; T TokComma; NT NtStmtList])
            (fun args => match args with (head_stmts, (_, (rest, _))) => 
                           head_stmts ++ rest 
                         end);

       (* StmtList -> epsilon *)
       rule (NtStmtList, []) (fun _ => []);

       (* --- CHAIN --- *)
       (* Chain -> Path ChainTail *)
       (* Example: "a -> b". Path parses "a". ChainTail uses "a" to link "b". *)
       rule (NtChain, [NT NtPath; NT NtChainTail])
            (fun args => match args with ((d, p), (tail_fn, _)) => 
                           let start_wig := path_to_wig d p in
                           (* The result is the Start Node + any Arcs/Nodes generated by the tail *)
                           (WNode start_wig) :: (tail_fn start_wig)
                         end);

       (* --- CHAIN TAIL --- *)
       (* ChainTail -> EdgeOp Path ChainTail *)
       rule (NtChainTail, [NT NtEdgeOp; NT NtPath; NT NtChainTail])
            (fun args => match args with (op, ((d, p), (tail_fn, _))) => 
                           fun prev_wig =>
                             let curr_wig := path_to_wig d p in
                             let arc := WArc op prev_wig curr_wig in
                             (* Return: Arc(prev,curr) :: Node(curr) :: Recurse(curr) *)
                             arc :: (WNode curr_wig) :: (tail_fn curr_wig)
                         end);

       (* ChainTail -> epsilon *)
       rule (NtChainTail, [])
            (fun _ => fun _ => []);

       (* --- PATH --- *)
       (* Path -> RelPrefix Segment PathTail *)
       rule (NtPath, [NT NtRelPrefix; NT NtSegment; NT NtPathTail])
            (fun args => match args with (d, (s, (tail, _))) => (d, s :: tail) end);

       (* --- RELATIVE PREFIX --- *)
       (* Recursively count dots at the start *)
       rule (NtRelPrefix, [T TokDot; NT NtRelPrefix])
            (fun args => match args with (_, (n, _)) => S n end);
            
       rule (NtRelPrefix, []) (fun _ => 0);

       (* --- PATH TAIL --- *)
       (* Parses .b.c -- STRICTLY one dot per segment *)
       rule (NtPathTail, [T TokDot; NT NtSegment; NT NtPathTail])
            (fun args => match args with (_, (s, (tail, _))) => s :: tail end);
            
       rule (NtPathTail, []) (fun _ => []);

       (* --- HELPERS --- *)
       rule (NtEdgeOp, [T TokHyphen]) (fun _ => "-"%string);
       rule (NtEdgeOp, [T TokArrow])  (fun _ => "->"%string);
       
       rule (NtSegment, [T TokId]) (fun args => match args with (s, _) => s end)
     ]
  |}.

(* ========================================================================== *)
(* 6. SCANNER (IGNORING WHITESPACE)                                           *)
(* ========================================================================== *)

Definition tok (a : terminal) (v : t_semty a) : token :=
  existT _ a v.

(* Characters that break a string of identifiers *)
Definition is_delim (c : ascii) : bool :=
  let n := nat_of_ascii c in
  if (n =? 46)%nat then true      (* . *)
  else if (n =? 44)%nat then true (* , *)
  else if (n =? 45)%nat then true (* - *)
  else if (n =? 62)%nat then true (* > *)
  else if (n =? 32)%nat then true (* Space *)
  else if (n =? 9)%nat  then true (* Tab *)
  else if (n =? 10)%nat then true (* LF *)
  else if (n =? 13)%nat then true (* CR *)
  else false.

(* Helper to consume an alphanumeric identifier *)
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
        (* WHITESPACE: Skip and Recurse *)
        if (code =? 32)%nat then tokenize_aux n rest
        else if (code =? 9)%nat  then tokenize_aux n rest
        else if (code =? 10)%nat then tokenize_aux n rest
        else if (code =? 13)%nat then tokenize_aux n rest
        
        (* SYMBOLS *)
        else if (code =? 46)%nat then tok TokDot tt :: tokenize_aux n rest
        else if (code =? 44)%nat then tok TokComma tt :: tokenize_aux n rest
        (* HYPHEN or ARROW *)
        else if (code =? 45)%nat then 
             match rest with
             | String c2 rest2 => 
               if (nat_of_ascii c2 =? 62)%nat 
               then tok TokArrow tt :: tokenize_aux n rest2 (* -> *)
               else tok TokHyphen tt :: tokenize_aux n rest (* - *)
             | EmptyString => tok TokHyphen tt :: []
             end
        
        (* IDENTIFIERS *)
        else 
          let (id, remaining) := span_ident s in
          match id with
          | EmptyString => tokenize_aux n rest (* Should be covered by delim check, but safety *)
          | _ => tok TokId id :: tokenize_aux n remaining
          end
    end
  end.

Definition tokenize (s : string) : list token :=
  tokenize_aux (String.length s) s.

Module Import PG := Make G.

(* --- Execution --- *)

(* Input: "a - b -> c, d," 
   Note: Whitespace is now irrelevant.
*)
Definition input : string := "a - b -> c, d,"%string.

Compute (match parseTableOf welkin_grammar with
         | inl msg => inl msg
         | inr tbl => inr (parse tbl (NT NtRoot) (tokenize input))
         end).
