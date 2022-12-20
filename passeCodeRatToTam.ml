(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Tds
open Ast
open Type
open Tam
open Code

type t1 = AstPlacement.programme
type t2 = string

(* analyse_code_affectable : AstPlacement.affectable -> string *)
(* Paramètre e : l'expression à analyser *)
(* Tranforme l'expression en chaîne d'instructions en code TAM représentant l'expression *)
let rec analyse_code_affecable a ecriture =
  match a with
  | AstType.Ident ia ->
    (* Récupération de l'adresse de la variable *)
    let (depl, base) = get_adresse_var_info_ast ia in
    (* Récupération de la taille de la variable *)
    let taille = getTaille(get_type_var_info_ast ia) in
    (* Récupèration du type de la variable *)
    let t = get_type_var_info_ast ia in
    (* Si ce type est compatible avec un pointeur ou n'est pas en écriture *)
    if ((est_compatible t (Pointeur(Undefined)))
      || not ecriture)
    (* Alors on charge en mémoire la variable *)
    then load taille depl base
    (* Sinon on stock la valeur chargée dans la pile dans la variable *)
    else store taille depl base
  | AstType.Const(_, v) ->
    (* Charge la constante dans la pile *)
    loadl_int v
  | AstType.DeRef da ->
    (* Analyse de l'expression correspondant à l'affectable *)
    analyse_code_affecable da ecriture
    (* Si on est en écriture alors écrit à l'adresse en haut de la pile *)
    ^ (if ecriture then storei 1
    (* Sinon charge la valeur pointée par l'adresse en haut de la pile *)
    else loadi 1)

(* analyse_code_expression : AstPlacement.expression -> string *)
(* Paramètre e : l'expression à analyser *)
(* Tranforme l'expression en chaîne d'instructions en code TAM représentant l'expression *)
let rec analyse_code_expression e =
  match e with
  | AstType.AppelFonction(ia, le) ->
    (* Analyse des expressions correspondant aux paramètres de la fonction *)
    List.fold_left (^) "" (List.map analyse_code_expression le)
    (* Appel de la fonction *)
    ^ call "SB" (get_nom_fun_info_ast ia)
  | AstType.Affectable(a) ->
    (* Analyse de l'affectable *)
    analyse_code_affecable a false
  | AstType.Booleen(b) ->
    (* Charge 1 dans la pile si le booléen est vrai et 0 sinon *)
    if b then loadl_int 1
    else loadl_int 0
  | AstType.Entier(i) -> loadl_int i  (* Charge l'entier dans la pile *)
  | AstType.Unaire(op, e) ->
    (* Analyse de l'expression du paramètre de l'opération *)
    analyse_code_expression e
    (* Exécution du code correspondant à l'opération *)
    ^ (match op with
      | AstType.Numerateur -> pop 0 1
      | AstType.Denominateur -> pop 1 1)
  | AstType.Binaire(op, e1, e2) ->
    (* Analyse des expressions des paramètres de l'opération *)
    analyse_code_expression e1
    ^ analyse_code_expression e2
    (* Exécution du code correspondant à l'opération *)
    ^ (match op with
      | AstType.Fraction -> ""
      | AstType.PlusInt -> subr "IAdd"
      | AstType.PlusRat -> call "SB" "RAdd"
      | AstType.MultInt -> subr "IMul"
      | AstType.MultRat -> call "SB" "RMul"
      | AstType.EquInt -> subr "IEq"
      | AstType.EquBool -> subr "IEq"
      | AstType.Inf -> subr "ILss")
  | AstType.Ternaire (c, e1, e2) ->
    (* Génération d'une étiquette pour référencer
    l'expression "sinon" de l'opérateur ternaire *)
    let lelse = getEtiquette() in
    (* Génération d'une étiquette pour référencer
      la fin de l'opérateur ternaire *)
    let lend = getEtiquette() in
    (* Analyse de l'expression - condition *)
    analyse_code_expression c
    (* Saut conditionnel vers le bloc "sinon" si la condition est fausse *)
    ^ jumpif 0 lelse
    (* Analyse de l'expression "alors" *)
    ^ analyse_code_expression e1
    (* Saut inconditionnel vers la fin de l'opérateur *)
    ^ jump lend
    (* Etiquette correspondant à l'expression "sinon" *)
    ^ label lelse
    (* Analyse de l'expression "sinon" *)
    ^ analyse_code_expression e2
    (* Etiquette correspondant à la fin de l'opérateur *)
    ^ label lend
  | AstType.New t ->
    (* Allocation de la mémoire pour le pointeur *)
    let taille = getTaille t in
    loadl_int taille
    ^ subr "MAlloc"
  | AstType.Adresse ia ->
    (* Récupération de l'adresse de la variable *)
    let (depl, reg) = get_adresse_var_info_ast ia in
    (* Charge en mémoire l'adresse de la variable *)
    loada depl reg
  | AstType.Null ->
    loadl_int 0 (* Charge l'adresse nulle dans la pile *)


(* analyse_code_bloc : AstPlacement.bloc -> string *)
(* Paramètre li : liste d'instructions à analyser *)
(* Paramètre taille : taille des variables locales au bloc en mémoire (pile) *)
(* Tranforme le bloc en une chaîne d'instructions correspondant au bloc *)
let rec analyse_code_bloc lloop (li, taille) =
  (* Réservation d'espace mémoire pour toutes les variables locales au bloc *)
  push taille
  (* Analyse de chaque instruction du bloc *)
  ^ List.fold_left (^) "" (List.map (analyse_code_instruction lloop) li)
  (* Libération de l'espace mémoire réservé pour les variables locales au bloc *)
  ^ pop 0 taille

(* analyse_code_instruction : AstPlacement.instruction -> string *)
(* Paramètre i : l'instruction à analyser *)
(* Tranforme l'instruction en une chaîne correspondant à l'instruction *)
and analyse_code_instruction lloop i =
  match i with
  (* Même traitement pour la déclaration et l'affectation
     car mémoire réservé à la création du bloc *)
  | AstPlacement.Declaration(ia, e) ->
    (* Récupération de l'adresse de la variable *)
    let (depl, base) = get_adresse_var_info_ast ia in
    (* Récupération de la taille de la variable *)
    let taille = getTaille (get_type_var_info_ast ia) in
    (* Analyse de l'expression à affecter *)
    analyse_code_expression e
    (* Affectation de la valeur à la variable *)
    ^ store taille depl base
    | AstPlacement.Affectation (a,e) ->
      (* Analyse de l'expression à affecter *)
      analyse_code_expression e
      (* Analyse de l'affectable *)
      ^ analyse_code_affecable a true
    | AstPlacement.AffichageBool e ->
      (* Analyse de l'expression à afficher *)
      analyse_code_expression e
      (* Appel de la fonction d'affichage pour les booléens *)
      ^ subr "BOut"
    | AstPlacement.AffichageInt e ->
      (* Analyse de l'expression à afficher *)
      analyse_code_expression e
      (* Appel de la fonction d'affichage pour les entiers *)
      ^ subr "IOut"
    | AstPlacement.AffichageRat e ->
      (* Analyse de l'expression à afficher *)
      analyse_code_expression e
      (* Appel de la fonction d'affichage pour les rationnels *)
      ^ call "SB" "ROut"
    | AstPlacement.AffichagePointeur e ->
      (* Affichage du pointeur au format '0x@' avec @ l'adresse du pointeur *)
      loadl_int 0
      ^ subr "IOut"
      ^ loadl_char 'x'
      ^ subr "COut"
      ^ analyse_code_expression e
      ^ subr "IOut"
  | AstPlacement.Conditionnelle (c,bt,be) ->
    begin
      match be with
      | [], _ ->
        (* Génération d'une étiquette pour référencer
           la fin de la conditionnelle *)
        let lend = getEtiquette() in
        (* Analyse de l'expression - condition *)
        analyse_code_expression c
        (* Saut conditionnel vers la fin du "si" si la condition est fausse *)
        ^ jumpif 0 lend
        (* Analyse du bloc "alors" *)
        ^ analyse_code_bloc lloop bt
        (* Etiquette correspondant à la fin du "si" *)
        ^ label lend
      | _ ->
        (* Génération d'une étiquette pour référencer
          le bloc "sinon" de la conditionnelle *)
        let lelse = getEtiquette() in
        (* Génération d'une étiquette pour référencer
          la fin de la conditionnelle *)
        let lend = getEtiquette() in
        (* Analyse de l'expression - condition *)
        analyse_code_expression c
        (* Saut conditionnel vers le bloc "sinon" si la condition est fausse *)
        ^ jumpif 0 lelse
        (* Analyse du bloc "alors" *)
        ^ analyse_code_bloc lloop bt
        (* Saut inconditionnel vers la fin du "si" *)
        ^ jump lend
        (* Etiquette correspondant au bloc "sinon" *)
        ^ label lelse
        (* Analyse du bloc "sinon" *)
        ^ analyse_code_bloc lloop be
        (* Etiquette correspondant à la fin du "si" *)
        ^ label lend
    end
  | AstPlacement.TantQue (c, b) ->
    (* Génération d'une étiquette pour référencer
       le début de la boucle *)
    let lbeg = getEtiquette() in
    (* Génération d'une étiquette pour référencer
       la fin de la boucle *)
    let lend = getEtiquette() in
    (* Etiquette correspondant au début de la boucle *)
    label lbeg
    (* Analyse de l'expression - condition *)
    ^ analyse_code_expression c
    (* Saut conditionnel vers la fin de la boucle si la condition est fausse *)
    ^ jumpif 0 lend
    (* Analyse du bloc de la boucle *)
    ^ analyse_code_bloc lloop b
    (* Saut inconditionnel vers le début de la boucle *)
    ^ jump lbeg
    (* Etiquette correspondant à la fin de la boucle *)
    ^ label lend
  | AstPlacement.Loop (n, li) ->
    (* Génération d'une étiquette pour référencer
       la fin de la boucle *)
    let lend = getEtiquette() in
    (* L'étiquette désignant le début de la boucle
       correspond au nom de la boucle concaténé à l'étiquette de fin *)
    let lbeg = n ^ lend in
    (* Etiquette correspondant au début de la boucle *)
    label lbeg
    (* Analyse du bloc de la boucle *)
    ^ analyse_code_bloc ((n, lend)::lloop) li
    (* Saut inconditionnel vers le début de la boucle *)
    ^ jump lbeg
    (* Etiquette correspondant à la fin de la boucle *)
    ^ label lend
  | AstPlacement.Continue (n) ->
    (* Récupération de l'étiquette de début de la boucle *)
    let (_, lend) = List.find (fun x -> (fst x) = n) lloop in
    (* Saut inconditionnel vers le début de la boucle *)
    jump (n ^ lend)
  | AstPlacement.Break (n) ->
    (* Récupération de l'étiquette de fin de la boucle *)
    let (_, lend) = List.find (fun x -> (fst x) = n) lloop in
    (* Saut inconditionnel vers la fin de la boucle *)
    jump (lend)
  | AstPlacement.Retour (e, tret, tparam) ->
    (* Analyse de l'expression à retourner *)
    analyse_code_expression e
    (* Inutile de dépiler les variables locales à la fonction car le RETURN s'en charge *)
    (* Appel à la méthode de retour de TAM *)
    ^ return tret tparam
  | AstPlacement.Empty -> ""  (* Ne rien faire *)


(* analyse_code_fonction : AstPlacement.fonction -> string *)
(* Paramètre : la fonction à analyser *)
(* Tranforme la fonction en chaîne d'instructions correpsondant à la fonction *)
let analyse_code_fonction (AstPlacement.Fonction(ia,_,b)) =
  (* Etiquette correspondant au début de la fonction *)
  label (get_nom_fun_info_ast ia)
  (* Analyse du bloc de la fonction *)
  ^ analyse_code_bloc [] b

(* analyser : AstPlacement.programme -> string *)
(* Paramètre : le programme à analyser *)
(* Tranforme le programme en une chaîne d'instruction TAM correspondant au programme *)
let analyser (AstPlacement.Programme (fonctions, prog)) =
  (* Génération de l'en-tête du programme *)
  getEntete()
  (* Génération du code des fonctions *)
  ^ List.fold_left (^) "" (List.map (analyse_code_fonction) fonctions)
  (* Etiquette correspondant au début du programme principal *)
  ^ label "main"
  (* Analyse du bloc du programme principal *)
  ^ analyse_code_bloc [] prog
  (* Appel à la fonction d'arrêt du programme *)
  ^ halt
