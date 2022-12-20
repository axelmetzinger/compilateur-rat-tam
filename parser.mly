/* Imports. */

%{
open Type
open Ast.AstSyntax
%}


%token <int> ENTIER
%token <string> ID
%token RETURN
%token PV
%token DP
%token AO
%token AF
%token PF
%token PO
%token EQUAL
%token CONST
%token PRINT
%token IF
%token ELSE
%token WHILE
%token BOOL
%token INT
%token RAT
%token CALL 
%token CO
%token CF
%token SLASH
%token NUM
%token DENOM
%token TRUE
%token FALSE
%token PLUS
%token ASTER
%token INF
%token EOF
%token NULL
%token NEW
%token ADDR
%token QUESTION
%token LOOP
%token CONTINUE
%token BREAK

(* Type de l'attribut synthétisé des non-terminaux *)
%type <programme> prog
%type <instruction list> bloc
%type <fonction> fonc
%type <instruction> i
%type <typ> typ
%type <typ*string> param
%type <affectable> a
%type <expression> e 

(* Type et définition de l'axiome *)
%start <Ast.AstSyntax.programme> main

%%

main : lfi=prog EOF     {lfi}

prog : lf=fonc* ID li=bloc  {Programme (lf,li)}

fonc : t=typ n=ID PO lp=param* PF li=bloc {Fonction(t,n,lp,li)}

param : t=typ n=ID  {(t,n)}

bloc : AO li=i* AF      {li}

i :
| t=typ n=ID EQUAL e1=e PV          {Declaration (t,n,e1)}
| aff=a EQUAL e1=e PV               {Affectation (aff,e1)}
| CONST n=ID EQUAL e=ENTIER PV      {Constante (n,e)}
| PRINT e1=e PV                     {Affichage (e1)}
| IF exp=e li=bloc                  {Conditionnelle (exp,li,[])}
| IF exp=e li1=bloc ELSE li2=bloc   {Conditionnelle (exp,li1,li2)}
| WHILE exp=e li=bloc               {TantQue (exp,li)}
| LOOP li=bloc                      {Loop ("_", li)}
| n=ID DP LOOP li=bloc              {Loop (n, li)}
| CONTINUE PV                       {Continue ("")}
| CONTINUE n=ID                     {Continue (n)}
| BREAK PV                          {Break ("")}
| BREAK n=ID PV                     {Break (n)}
| RETURN exp=e PV                   {Retour (exp)}

typ :
| BOOL                      {Bool}
| INT                       {Int}
| RAT                       {Rat}
| t=typ ASTER               {Pointeur (t)}
| PO t=typ PF               {t}

a :
| n=ID                      {Ident n}
| ASTER aff=a               {DeRef(aff)}
| PO aff=a PF               {aff}

e : 
| CALL n=ID PO lp=e* PF                 {AppelFonction (n,lp)}
| TRUE                                  {Booleen true}
| FALSE                                 {Booleen false}
| e=ENTIER                              {Entier e}
| NUM e1=e                              {Unaire (Numerateur, e1)}
| DENOM e1=e                            {Unaire (Denominateur, e1)}
| CO e1=e SLASH e2=e CF                 {Binaire (Fraction, e1, e2)}
| e1=e PLUS e2=e                        {Binaire (Plus, e1, e2)}
| e1=e ASTER e2=e                       {Binaire (Mult, e1, e2)}
| e1=e EQUAL e2=e                       {Binaire (Equ, e1, e2)}
| e1=e INF e2=e                         {Binaire (Inf, e1, e2)}
| PO ec=e QUESTION ev=e DP ef=e PF      {Ternaire(ec, ev, ef)}
| aff=a                                 {Affectable(aff)}
| NULL                                  {Null}
| PO NEW t=typ PF                       {New t}
| ADDR n=ID                             {Adresse n}
| PO exp=e PF                           {exp}


