(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Tds
open Exceptions
open Ast
open Type

type t1 = Ast.AstTds.programme
type t2 = Ast.AstType.programme

(* analyse_type_expression : tds -> AstTds.expression -> AstType.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'expression
en une expression de type AstType.expression *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_type_expression e =
  match e with
  | AstTds.AppelFonction(ia, le) ->
    let (tf, ltf) = get_type_fun_info_ast ia in
    let nle = List.map (analyse_type_expression) le in
    let lte = List.map (fun x -> fst x) nle in
    let nlet = List.map (fun x -> snd x) nle in
    if (est_compatible_list lte ltf) then (tf, AstType.AppelFonction(ia, nlet))
    else raise (TypesParametresInattendus(lte, ltf))
  | AstTds.Ident(ia) -> (get_type_var_info_ast ia, AstType.Ident(ia))
  | AstTds.Booleen(b) -> (Bool, AstType.Booleen(b))
  | AstTds.Entier(i) -> (Int, AstType.Entier(i))
  | AstTds.Unaire(op, e) ->
    let (te, ne) = analyse_type_expression e in
    if (te = Rat) then
      let (t_ret, nop) =
      begin
        match op with
        | AstSyntax.Numerateur -> (Int, AstType.Numerateur)
        | AstSyntax.Denominateur -> (Int, AstType.Denominateur)
        | _ -> failwith "Internal error: analyse_type_expression"
      end in
      (t_ret, AstType.Unaire(nop, ne))
    else raise (TypeInattendu(te, Rat))
  | AstTds.Binaire(op, e1, e2) ->
    let (te1, ne1) = analyse_type_expression e1 in
    let (te2, ne2) = analyse_type_expression e2 in
    let (t_ret, nop) =
    begin
      match op with
      | AstSyntax.Fraction ->
        begin
          match te1, te2 with
          | Int, Int -> (Rat, AstType.Fraction)
          | _ -> raise (TypeBinaireInattendu(op, te1, te2))
        end
      | AstSyntax.Plus ->
        begin
          match te1, te2 with
          | Int, Int -> (Int, AstType.PlusInt)
          | Rat, Rat -> (Rat, AstType.PlusRat)
          | _ -> raise (TypeBinaireInattendu(op, te1, te2))
        end
      | AstSyntax.Mult ->
        begin
          match te1, te2 with
          | Int, Int -> (Int, AstType.MultInt)
          | Rat, Rat -> (Rat, AstType.MultRat)
          | _ -> raise (TypeBinaireInattendu(op, te1, te2))
        end
      | AstSyntax.Equ ->
        begin
          match te1, te2 with
          | Int, Int -> (Bool, AstType.EquInt)
          | Bool, Bool -> (Bool, AstType.EquBool)
          | _ -> raise (TypeBinaireInattendu(op, te1, te2))
        end
      | AstSyntax.Inf -> if (est_compatible te1 Int) then (Bool, AstType.Inf) else raise (TypeBinaireInattendu(op, te1, te2))
    end in
    (t_ret, AstType.Binaire(nop, ne1, ne2))
  | _ -> failwith "Internal error: analyse_type_expression"

(* analyse_type_bloc : tds -> info_ast option -> AstTds.bloc -> AstType.bloc *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc en un bloc de type AstType.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_type_bloc li =
  (* TODO: Rajouter commentaire *)
  List.map (analyse_type_instruction) li
(* analyse_type_instruction : tds -> info_ast option -> AstTds.instruction -> AstType.instruction *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstType.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_type_instruction i =
  match i with
  | AstTds.Declaration(t, ia, e) ->
    let (te, ne) = analyse_type_expression e in
    if (t = te) then
      begin
        modifier_type_variable t ia;
        AstType.Declaration(ia, ne)
      end
    else raise (TypeInattendu(te, t))
  | AstTds.Affectation (ia,e) ->
    let (te, ne) = analyse_type_expression e in
    let t = get_type_var_info_ast ia in
    if (t = te) then AstType.Affectation(ia, ne)
    else (raise (TypeInattendu(te, t)))
  | AstTds.Affichage e ->
    let (te, ne) = analyse_type_expression e in
    begin
      match te with
      | Bool -> AstType.AffichageBool(ne)
      | Int -> AstType.AffichageInt(ne)
      | Rat -> AstType.AffichageRat(ne)
      | Undefined -> failwith "Internal error: analyse_type_instruction"
    end
  | AstTds.Conditionnelle (c,tia,eia) ->
    let (tc, nc) = analyse_type_expression c in
    if (tc = Bool) then
      let nbt = analyse_type_bloc tia in
      let nbe = analyse_type_bloc eia in
      AstType.Conditionnelle(nc, nbt, nbe)
    else raise (TypeInattendu(tc, Bool))
  | AstTds.TantQue (c,bast) ->
    let (tc, nc) = analyse_type_expression c in
    if (tc = Bool) then
      let nb = analyse_type_bloc bast in
      AstType.TantQue(nc, nb)
    else raise (TypeInattendu(tc, Bool))
  | AstTds.Retour (e, ia) ->
    let (te, ne) = analyse_type_expression e in
    let (t_ret, _) = get_type_fun_info_ast ia in
    if (te = t_ret) then
      AstType.Retour(ne, ia)
    else raise (TypeInattendu(te, t_ret))
  | AstTds.Empty -> AstType.Empty


(* TODO: commentaires *)
(* analyse_type_parametre : tds -> (typ * string) -> (typ * info_ast) *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre (t, n) : type (t) et nom (n) du paramètre à analyser *)
(* Vérifie la bonne utilisation du paramètre et le tranforme en paramètre de type (typ * info_ast) *)
let analyse_type_parametre (t, ia) =
  modifier_type_variable t ia;
  ia

(* TODO: commentaires *)
(* analyse_type_fonction : tds -> AstTds.fonction -> AstType.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstType.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_type_fonction (AstTds.Fonction(t,ia,lp,b)) =
  let lpia = List.map (analyse_type_parametre) lp in
  let ltp = List.map (fun x -> fst x) lp in
  modifier_type_fonction t ltp ia;
  let nb = analyse_type_bloc b in
  AstType.Fonction(ia, lpia, nb)

(* analyser : AstTds.programme -> AstType.programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstType.programme *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstTds.Programme (fonctions, prog)) =
  let nlf = List.map (analyse_type_fonction) fonctions in
  let nb = analyse_type_bloc prog in
  AstType.Programme (nlf,nb)
