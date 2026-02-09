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

Definition path := list string.

Inductive graph_elem :=
| GNode (p : path)
| GArc  (src : path) (dst : path).

Definition graph := list graph_elem.

(* ========================================================================== *)
(* 2. INTERFACE                                                               *)
(* ========================================================================== *)

Inductive terminal_def :=
| TokId
| Dot | Comma | Hyphen | Arrow 
| Space | Tab | CR | LF.

Inductive nonterminal_def :=
| Terms | TermsTail 
| Term  | TermTail  
| Path  | PathTail  
| Unit
| Identifier
| WS.

Definition t_semty_def (a : terminal_def) : Type :=
  match a with
  | TokId => string
  | _     => unit
  end.

Definition nt_semty_def (x : nonterminal_def) : Type :=
  match x with
  | Terms          => graph
  | TermsTail      => graph
  | Term           => graph_elem
  | TermTail       => option path 
  | Path           => path
  | PathTail       => path
  | Unit           => string
  | Identifier     => string
  | WS             => unit
  end.

Lemma t_eq_dec_def : forall (t t' : terminal_def), {t = t'} + {t <> t'}.
Proof. decide equality. Defined.

Lemma nt_eq_dec_def : forall (nt nt' : nonterminal_def), {nt = nt'} + {nt <> nt'}.
Proof. decide equality. Defined.

(* ========================================================================== *)
(* 3. MODULE CONFIGURATION                                                    *)
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

  (* Better debug printing to avoid confusing "tok" messages *)
  Definition showT (a : terminal) : string := 
    match a with 
    | TokId => "Id" 
    | Dot => "." | Comma => "," | Hyphen => "-" | Arrow => "->"
    | Space => "SPC" | Tab => "TAB" | CR => "CR" | LF => "LF"
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
(* 4. GRAMMAR DEFINITION                                                      *)
(* ========================================================================== *)

Definition rule := existT action_ty.

Definition welkin_grammar : grammar :=
  {| start := Terms;
     prods := [
       (* --- WS --- *)
       (* Standard greedy whitespace consumer *)
       rule (WS, [T Space; NT WS]) (fun _ => tt);
       rule (WS, [T Tab; NT WS])   (fun _ => tt);
       rule (WS, [T CR; NT WS])    (fun _ => tt);
       rule (WS, [T LF; NT WS])    (fun _ => tt);
       rule (WS, [])               (fun _ => tt);

       (* --- TERMS --- *)
       (* Structure: WS (Term WS)* *)
       (* This avoids the "WS WS" collision by ensuring WS only appears AFTER a term in the loop *)

       (* Terms -> WS TermsTail *)
       rule (Terms, [NT WS; NT TermsTail])
            (fun args => match args with (_, (tail, _)) => tail end);

       (* TermsTail -> Term WS TermsTail *)
       (* Recursively eat Term then WS *)
       rule (TermsTail, [NT Term; NT WS; NT TermsTail]) 
            (fun args => match args with (t, (_, (ts, _))) => t :: ts end);
       
       (* TermsTail -> epsilon *)
       rule (TermsTail, []) 
            (fun _ => []);

       (* --- TERM --- *)
       (* Term -> Path TermTail *)
       rule (Term, [NT Path; NT TermTail]) 
            (fun args => match args with (p1, (tail, _)) => 
                           match tail with
                           | Some p2 => GArc p1 p2
                           | None    => GNode p1
                           end
                         end);

       (* TermTail -> -> Path *)
       rule (TermTail, [T Hyphen; T Arrow; NT Path])
            (fun args => match args with (_, (_, (p2, _))) => Some p2 end);

       (* TermTail -> epsilon *)
       rule (TermTail, [])
            (fun _ => None);

       (* --- PATH --- *)
       (* Path -> Unit PathTail *)
       rule (Path, [NT Unit; NT PathTail])
            (fun args => match args with (u, (tail, _)) => u :: tail end);

       (* PathTail -> . Path *)
       (* Note: Reusing Path here works because Path handles the next unit *)
       rule (PathTail, [T Dot; NT Path])
            (fun args => match args with (_, (p, _)) => p end);
            
       (* PathTail -> epsilon *)
       rule (PathTail, [])
            (fun _ => []);

       (* --- PRIMITIVES --- *)
       rule (Unit, [NT Identifier]) 
            (fun args => match args with (s, _) => s end);

       rule (Identifier, [T TokId]) 
            (fun args => match args with (s, _) => s end)
     ]
  |}.

(* ========================================================================== *)
(* 5. SCANNER IMPLEMENTATION                                                  *)
(* ========================================================================== *)

Definition tok (a : terminal) (v : t_semty a) : token :=
  existT _ a v.

Definition is_structure (c : ascii) : bool :=
  let n := nat_of_ascii c in
  if (n =? 46)%nat then true
  else if (n =? 44)%nat then true
  else if (n =? 45)%nat then true
  else if (n =? 62)%nat then true
  else if (n =? 32)%nat then true
  else if (n =? 9)%nat  then true
  else if (n =? 10)%nat then true
  else if (n =? 13)%nat then true
  else false.

Fixpoint span_ident (s : string) : string * string :=
  match s with
  | EmptyString => ("", "")
  | String c rest =>
      if is_structure c then ("", s)
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
        if (code =? 46)%nat then tok Dot tt :: tokenize_aux n rest
        else if (code =? 44)%nat then tok Comma tt :: tokenize_aux n rest
        else if (code =? 45)%nat then tok Hyphen tt :: tokenize_aux n rest
        else if (code =? 62)%nat then tok Arrow tt :: tokenize_aux n rest
        else if (code =? 32)%nat then tok Space tt :: tokenize_aux n rest
        else if (code =? 9)%nat  then tok Tab tt :: tokenize_aux n rest
        else if (code =? 10)%nat then tok LF tt :: tokenize_aux n rest
        else if (code =? 13)%nat then tok CR tt :: tokenize_aux n rest
        else 
          let (id, remaining) := span_ident s in
          match id with
          | EmptyString => tokenize_aux n rest
          | _ => tok TokId id :: tokenize_aux n remaining
          end
    end
  end.

Definition tokenize (s : string) : list token :=
  tokenize_aux (String.length s) s.

Module Import PG := Make G.

(* --- Execution --- *)

Definition input : string := "std.io --> sys.net"%string.

(* Should now return (inr [...]) with the parsed graph *)
Compute (match parseTableOf welkin_grammar with
         | inl msg => inl msg
         | inr tbl => inr (parse tbl (NT Terms) (tokenize input))
         end).
