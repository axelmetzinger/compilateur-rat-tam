(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Tds
open Exceptions
open Ast
open Type

type t1 = Ast.AstTds.programme
type t2 = Ast.AstType.programme

(* analyse_type_expression : AstTds.expression -> AstType.expression *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie le bon typage des identifiants et transforme l'expression
en une expression de type AstType.expression *)
(* Erreur si type utilisé innatendu *)
let rec analyse_type_expression e =
  match e with
  | AstTds.AppelFonction(ia, le) ->
    (* Récupération du type de retour de la fonction et des types de ses paramètres attendus *)
    let (tf, ltf) = get_type_fun_info_ast ia in
    (* TODO: Les 3 lignes suivantes sont refactorable en un fold *)
    (* Analyse des expression corresopndant aux paramètres d'appel *)
    let nle = List.map (analyse_type_expression) le in
    (* Récupération de la liste des types d'appel *)
    let lte = List.map (fun x -> fst x) nle in
    (* Récupration de la liste des expressions traitées *)
    let nlet = List.map (fun x -> snd x) nle in
    (* Renvoie d'un couple composé du type de retour de la fonction et du nouvel
       AppelFonction si les types d'appel et attendus sont compatibles *)
    if (est_compatible_list lte ltf) then (tf, AstType.AppelFonction(ia, nlet))
    (* Si les types ne sont pas compatibes, levée de l'exception TypesParametresInattendus *)
    else raise (TypesParametresInattendus(lte, ltf))
  | AstTds.Ident(ia) ->
    (* Renvoie d'un couple composé du type de l'identifiant et du nouvel Ident *)
    (get_type_var_info_ast ia, AstType.Ident(ia))
  | AstTds.Booleen(b) ->
    (* Renvoie d'un couple composé du type (Bool) et du nouveau Booléen *)
    (Bool, AstType.Booleen(b))
  | AstTds.Entier(i) ->
    (* Renvoie d'un couple composé du type (Int) et du nouvel Entier *)
    (Int, AstType.Entier(i))
  | AstTds.Unaire(op, e) ->
    (* Analyse de l'expression *)
    let (te, ne) = analyse_type_expression e in
    (* Si l'expression est de type Rat et que l'opérateur est Numerateur ou Denominateur,
       renvoie d'un couple composé du type (Int) et du nouvel Unaire *)
    let (t_ret, nop) =
    begin
      match te, op with
      | Rat, AstSyntax.Numerateur -> (Int, AstType.Numerateur)
      | Rat, AstSyntax.Denominateur -> (Int, AstType.Denominateur)
      | _ ->
        (* Sinon, levée de l'exception TypeInattendu *)
        raise (TypeInattendu(te, Rat))
    end in
    (t_ret, AstType.Unaire(nop, ne))
  | AstTds.Binaire(op, e1, e2) ->
    (* Analyse des expressions *)
    let (te1, ne1) = analyse_type_expression e1 in
    let (te2, ne2) = analyse_type_expression e2 in
    (* Récupération du type de retour d'une opération binaire
       et de la nouvelle opération surchargée en fonction des types utilisés *)
    let (t_ret, nop) =
    begin
      match op, te1, te2 with
      | AstSyntax.Fraction, Int, Int -> (Rat, AstType.Fraction)
      | AstSyntax.Plus, Int, Int -> (Int, AstType.PlusInt)
      | AstSyntax.Plus, Rat, Rat -> (Rat, AstType.PlusRat)
      | AstSyntax.Mult, Int, Int -> (Int, AstType.MultInt)
      | AstSyntax.Mult, Rat, Rat -> (Rat, AstType.MultRat)
      | AstSyntax.Equ, Int, Int -> (Bool, AstType.EquInt)
      | AstSyntax.Equ, Bool, Bool -> (Bool, AstType.EquBool)
      | AstSyntax.Inf, Int, Int -> (Bool, AstType.Inf)
      | _ -> raise (TypeBinaireInattendu(op, te1, te2))
    end in
    (* Renvoie un couple composé du type de retour de l'expression binaire
       et du nouveau Binaire surchargé *)
    (t_ret, AstType.Binaire(nop, ne1, ne2))


(* analyse_type_bloc : AstTds.bloc -> AstType.bloc *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne compatibilité de types et surcharge les opérations si nécessaire
   et transforme le bloc en un bloc de type AstType.bloc *)
let rec analyse_type_bloc li =
  (* Analyse de la liste des instruction *)
  List.map (analyse_type_instruction) li

(* analyse_type_instruction : AstTds.instruction -> AstType.instruction *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie le bon typage des instructions et transforme l'instruction
en une instruction de type AstType.instruction *)
(* Erreur si le type utilisé est innatendu (ou incompatible) *)
and analyse_type_instruction i =
  match i with
  | AstTds.Declaration(t, ia, e) ->
    (* Analyse de l'expression *)
    let (te, ne) = analyse_type_expression e in
    (* Si le type de l'expression est compatible avec le type de la déclaration,
       modification du type dans la TDS et renvoie d'un nouveau Declaration *)
    if (t = te) then
      begin
        modifier_type_variable t ia;
        AstType.Declaration(ia, ne)
      end
    (* Sinon, levée de l'exception TypeInattendu *)
    else raise (TypeInattendu(te, t))
  | AstTds.Affectation (ia,e) ->
    (* Analyse de l'expression *)
    let (te, ne) = analyse_type_expression e in
    (* Récupération du type de l'identifiant attendu *)
    let t = get_type_var_info_ast ia in
    (* Si le type de l'expression est compatible avec le type de l'identifiant,
       renvoie d'une nouvelle Affectation *)
    if (t = te) then AstType.Affectation(ia, ne)
    (* Sinon, levée de l'exception TypeInattendu *)
    else (raise (TypeInattendu(te, t)))
  | AstTds.Affichage e ->
    (* Analyse de l'expression *)
    let (te, ne) = analyse_type_expression e in
    (* Renvoie d'un nouveau Affichage surchargé en fonction du type de l'expression *)
    begin
      match te with
      | Bool -> AstType.AffichageBool(ne)
      | Int -> AstType.AffichageInt(ne)
      | Rat -> AstType.AffichageRat(ne)
      | Undefined -> failwith "Internal error: analyse_type_instruction"
    end
  | AstTds.Conditionnelle (c,tia,eia) ->
    (* Analyse de l'expression - condition *)
    let (tc, nc) = analyse_type_expression c in
    (* Si le type de l'expression est Booléen, analyse des blocs
       et renvoie d'une nouvelle Conditionnelle *)
    if (tc = Bool) then
      let nbt = analyse_type_bloc tia in
      let nbe = analyse_type_bloc eia in
      AstType.Conditionnelle(nc, nbt, nbe)
    (* Sinon, levée de l'exception TypeInattendu *)
    else raise (TypeInattendu(tc, Bool))
  | AstTds.TantQue (c,bast) ->
    (* Analyse de l'expression - condition *)
    let (tc, nc) = analyse_type_expression c in
    (* Si le type de l'expression est Booléen, analyse du bloc
       et renvoie d'un nouveau TantQue *)
    if (tc = Bool) then
      let nb = analyse_type_bloc bast in
      AstType.TantQue(nc, nb)
    (* Sinon, levée de l'exception TypeInattendu *)
    else raise (TypeInattendu(tc, Bool))
  | AstTds.Retour (e, ia) ->
    (* Analyse de l'expression *)
    let (te, ne) = analyse_type_expression e in
    (* Récupération du type de retour attendu *)
    let (t_ret, _) = get_type_fun_info_ast ia in
    (* Si le type de l'expression est compatible avec le type de retour,
       renvoie d'un nouveau Retour *)
    if (te = t_ret) then
      AstType.Retour(ne, ia)
    (* Sinon, levée de l'exception TypeInattendu *)
    else raise (TypeInattendu(te, t_ret))
  | AstTds.Empty -> AstType.Empty (* Renvoie d'un nouvel Empty *)


(* analyse_type_parametre : (typ * info_ast) -> info_ast *)
(* Paramètre (t, n) : type (t) et nom (n) du paramètre à analyser *)
(* Modifie le type de la variable associé au paramètre et le transforme en paramètre de type : info_ast *)
let analyse_type_parametre (t, ia) =
  (* Modifie le type du paramètre *)
  modifier_type_variable t ia;
  (* Renvoie de l'info_ast mis à jour *)
  ia

(* analyse_type_fonction : AstTds.fonction -> AstType.fonction *)
(* Paramètre : la fonction à analyser *)
(* Vérifie le bon typage des paramètres et de son bloc et transforme la fonction
    en une fonction de type AstType.fonction *)
let analyse_type_fonction (AstTds.Fonction(t,ia,lp,b)) =
  (* Analyse des paramètres *)
  let lpia = List.map (analyse_type_parametre) lp in
  (* Récupération des types des paramètres *)
  let ltp = List.map (fun x -> fst x) lp in
  (* Modification du type des paramètres *)
  modifier_type_fonction t ltp ia;
  (* Analyse du bloc *)
  let nb = analyse_type_bloc b in
  (* Renvoie d'une nouvelle Fonction *)
  AstType.Fonction(ia, lpia, nb)

(* analyser : AstTds.programme -> AstType.programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des types et transforme le programme
en un programme de type AstType.programme *)
(* Erreur si mauvaise utilisation des types *)
let analyser (AstTds.Programme (fonctions, prog)) =
  let nlf = List.map (analyse_type_fonction) fonctions in
  let nb = analyse_type_bloc prog in
  AstType.Programme (nlf,nb)
