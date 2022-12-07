(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Tds
open Ast
open Type
open Tam
open Code

type t1 = AstPlacement.programme
type t2 = string

(* analyse_code_expression : tds -> AstPlacement.expression -> AstType.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'expression
en une expression de type AstType.expression *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_code_expression e =
  match e with
  | AstType.AppelFonction(ia, le) ->
    List.fold_left (^) "" (List.map analyse_code_expression le)
    ^ call "SB" (get_nom_fun_info_ast ia)
  | AstType.Ident(ia) ->
    let (depl, base) = get_adresse_var_info_ast ia in
    let taille = getTaille(get_type_var_info_ast ia) in
    loada depl base
    ^ loadi taille
  | AstType.Booleen(b) ->
    if b then loadl_int 1
    else loadl_int 0
  | AstType.Entier(i) -> loadl_int i
  | AstType.Unaire(op, e) ->
    analyse_code_expression e
    ^ (match op with
      | AstType.Numerateur -> pop 0 1
      | AstType.Denominateur -> pop 1 1)
  | AstType.Binaire(op, e1, e2) ->
    analyse_code_expression e1
    ^ analyse_code_expression e2
    ^ (match op with
      | AstType.Fraction -> ""
      | AstType.PlusInt -> subr "IAdd"
      | AstType.PlusRat -> call "SB" "RAdd"
      | AstType.MultInt -> subr "IMul"
      | AstType.MultRat -> call "SB" "RMul"
      | AstType.EquInt -> subr "IEq"
      | AstType.EquBool -> subr "IEq"
      | AstType.Inf -> subr "ILss")

(* analyse_code_bloc : tds -> info_ast option -> AstPlacement.bloc -> AstType.bloc *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc en un bloc de type AstType.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_code_bloc (li, taille) =
  (* TODO: Rajouter commentaire *)
  push taille
  ^ List.fold_left (^) "" (List.map (analyse_code_instruction) li)
  ^ pop 0 taille
(* analyse_code_instruction : tds -> info_ast option -> AstPlacement.instruction -> AstType.instruction *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstType.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_code_instruction i =
  match i with
  | AstPlacement.Declaration(ia, e) | AstPlacement.Affectation (ia,e) ->
    let (dep, base) = get_adresse_var_info_ast ia in
    let taille = getTaille (get_type_var_info_ast ia) in
    analyse_code_expression e
    ^ loada dep base
    ^ storei taille
    | AstPlacement.AffichageBool e ->
      analyse_code_expression e
      ^ subr "BOut"
    | AstPlacement.AffichageInt e ->
      analyse_code_expression e
      ^ subr "IOut"
    | AstPlacement.AffichageRat e ->
      analyse_code_expression e
      ^ call "SB" "ROut"
  | AstPlacement.Conditionnelle (c,bt,be) ->
    let lelse = getEtiquette() in
    let lend = getEtiquette() in
    analyse_code_expression c
    ^ jumpif 0 lelse
    ^ analyse_code_bloc bt
    ^ jump lend
    ^ label lelse
    ^ analyse_code_bloc be
    ^ label lend
  | AstPlacement.TantQue (c, b) ->
    let lbeg = getEtiquette() in
    let lend = getEtiquette() in
    label lbeg
    ^ analyse_code_expression c
    ^ jumpif 0 lend
    ^ analyse_code_bloc b
    ^ jump lbeg
    ^ label lend
  | AstPlacement.Retour (e, tret, tparam) ->
    analyse_code_expression e
    (* Inutile de dépiler les variables locales à la fonction car le RETURN s'en charge *)
    ^ return tret tparam
  | AstPlacement.Empty -> ""


(* TODO: commentaires *)
(* analyse_code_fonction : tds -> AstPlacement.fonction -> AstType.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstType.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_code_fonction (AstPlacement.Fonction(ia,_,b)) =
  label (get_nom_fun_info_ast ia)
  ^ analyse_code_bloc b
  ^ halt (* PERMET D'EMPECHER BOUCLE INIFINE -> A REMPLACER PAR VERIFICATION RETURN DANS FUNC *)

(* analyser : AstPlacement.programme -> AstType.programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstType.programme *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstPlacement.Programme (fonctions, prog)) =
  getEntete()
  ^ List.fold_left (^) "" (List.map (analyse_code_fonction) fonctions)
  ^ label "main"
  ^ analyse_code_bloc prog
  ^ halt
