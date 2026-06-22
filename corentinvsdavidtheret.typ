//
#import "style.typ": conf, afficherTitre, theorem, proposition, proof, definition, remark, example, propdef, lemma, numbered_eq, rappel
#import "shortcut.typ":*
#import "todo.typ" : *

#import "@preview/ouset:0.2.0":* //o=pour les over/underset
#import "@preview/realhats:0.1.0": hat, realhats-list
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.8": pdv, taylorterm, dv, iprod

#import "@preview/quick-maths:0.2.1" : shorthands

// Propriétés du document

#let titre = "Corentin vs David Théret"
#show: doc => conf(doc,titre)
#set heading(numbering: "I.1")
#set-page-properties(margin-left: 2cm)
#afficherTitre(titre)

#show math.equation: set text(font: "Luciole Math")
#show "tq" : "tel que"
#show "tqe" : "telle que"
#show "tqs" : "tels que"
#show "Mq" : "Montrer que"
#show "mq" : "montrer que"
#show "Mq il" : "Montrer qu'il"
#show "mq il" : "montrer qu'il"
#show "mph" : "morphisme"
#show "càd" : "c'est-à-dire"
#show " ev " : " espace vectoriel "
#show "sev" : "sous-espace vectoriel"
#show "dims" : "dimension"
#show "dimss" : "dimensions"
#show " ssi" : " si et seulement si"
#show: shorthands.with(
  ($+-$, $plus.minus$),
  ($!>$, math.mapsto),
  ($=<$, math.arrow.l.double)
)

#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#show: thmrules.with(qed-symbol: $square$)

#import "@preview/fleck:0.1.0": *

#coffee-a(angle: 95deg, dy: 10pt, scale: 10%)
#coffee-b(where: top, angle: 95deg, opacity: 50%)
#coffee-c(where: bottom + left, dx: 10% + 5pt)
#coffee-d(where: right + top, angle: 95deg, opacity: 50%)

#outline()

#colbreak()

#legende(todo_types)
#note-outline(title:"Todos")



= Corentin vs Victor Maslov et Johannes Jisse Duistermaat


== Indice de Maslov

=== Rappels sur la Grassmannienne Lagrangienne

On fixe dans cette section $(FF, ss)$ ev symplectique de dimension $2n in NN$ et l'on notera $"Sym"(FF)$ le groupe des symplectomorphismes de $FF$.

#definition[ On appelle *Grassmannienne Lagrangienne* associée à $FF$ l'ensemble $Lambda(n)$ des sous-espaces Lagrangiens de $FF$.
  De plus; Pour $aa in Lambda(n)$ et $k in NN$ on pose $ Lambda^k (aa):= {bb in Lambda(n) | "dim" aa inter bb = k} $ l'ensemble des Lagrangiens de $FF$ dont l'intersection avec $aa$ est de dimension $k$.]

#propdef[Soient $aa, bb in Lambda(n)$ et $gg$ sev de $FF$ de dimension $n$. Supposons $aa$ et $gg$ transverses à $bb$. Alors il existe une unique application linéaire $C : aa to bb$ appelée *cadre lagrangien* tqe $gg = {u +C u; u in aa}$. De plus, la forme $ Q(aa,bb;gg) : & aa times  aa &to &RR;\ & (u,v) &!> &sigma(C u, v) $ est symétrique ssi $gg$ est Lagrangien.]<defC>

#proof[
Par transversalité de $bb$ et $gg$ on a $FF = bb plus.o gg$, ce qui donne l'unicité. Puis par transversalité de $bb$ et $aa$ la projection $pi : aa to gg$ parallèlement à $bb$ est injective donc un isomorphisme. Ainsi, l'application $C = pi-Id_aa in aa to bb$ convient.

Pour tous $u,v in aa$, en utilisant que $aa$ et $bb$ sont Lagrangiens :
$ 
Q(aa,bb;gg) (u,v) &= sigma(C u, v)\
                  &= sigma(C u, v +C v)  \ //" car "bb" est Lagrangien" \
                  &= sigma(u + C u, v + C v) - ss(u, v + C v) \
                  &= sigma(u + C u, v + C v) + Q(aa,bb;gg) (v,u) + ss(v, u)\
                  &= sigma(u + C u, v + C v) + Q(aa,bb;gg) (v,u). // & "car "aa" est Lagrangien" \
$

Ainsi, $Q(aa,bb;gg)$ est symétrique ssi $sigma(u + C u, v + C v)=0$ pour tous $u,v in aa$ càd ssi $gg$ est Lagrangien par définition de $C$.
]

#proposition[ Soient $aa,bb in Lambda(n)$ transverses.
+ L'application $Q(aa,bb) : gg in Lambda^0(bb) to Q(aa,bb;gg) in S(aa)$ est une bijection de $Lambda^0(bb)$ dans l'espace $S(aa)$ des formes bilinéaire symétriques sur $aa$.
+ Si $gg in Lambda^0(aa) inter Lambda^0(bb)$ alors $Q(aa,bb;gg)$ et $Q(bb,gg;aa)$ sont conjuguées. ]<propQabc>

#proof[
+ Par transversalité de $aa$ et $bb$, Lagrangiens et par le fait que $ss$ soit non dégénérée $w in bb !>ss(w, dot )_(|aa) in aa^*$ est un isomorphisme qui induit un second isomorphisme $(aa to bb) sim.eq (aa to aa^*)$. On obtient alors le diagramme suivant :

  #diagram( spacing : 5mm, $ Lambda^0(bb)  edge(, "hook->") & (aa to bb) edge(sim.eq,"->") & (aa to aa^*)\ gamma edge(,|->) & C edge(,|->) & Q(aa,bb;gg) $)

  l'injectivité de la première flèche découle l'unicité dans la @defC et donne celle de $Q(aa,bb)$.


  Soit maintenant $S in S(aa)$. On obtient $C : aa to bb$ tq $S = ss(C, dot )_(|aa)$ par l'isomorphisme ci-dessus. Posons $gg := {u + C u ; u in aa}$qui est de dimension $n$ et transverse à $bb$ par transversalité de $aa$ et $bb$ et $gg cc gg^ss$ par symétrie de $S$ donc $gg in Lambda^0(bb)$. On vérifie sans mal que $Q(aa,bb;gg) = S$.

+ Soit $gg in Lambda^0(aa) inter Lambda^0(bb)$. On dispose de $C : aa to bb$ et $C':bb to gg$ cadres Lagrangiens pour $gg$ et $aa$. Alors fixons $v in bb$ et posons $u:=v + C'v in aa$. En remarquant que $C'v = u + C u in gg$ on obtient :

$ Q(bb,gg;aa)(v) &= ss(C'v,v)\
                 &= ss(C'v,u-C'v)\
                 &= ss(C'v,u)\
                 &= ss(u+C u, u)\
                 &= ss(C' u,u)\
                 &= QQ(u). $

Or l'application $v!>u$ est la restriction $bb$ de la projection sur $aa$ parallèlement à $gg$ qui est un isomorphisme. D'où le résultat. 


#todo[est-ce que $S$ est orienté en $+-1$. Est-ce que la Emmanuel interprétation marche ?]
  //Soient $gg,gg' in Lambda^0(bb)$ et $C,C' : aa to bb$ tq $gg^( (')) = {u+ C ^( (')) u ; u in aa}$. On a alors, par hypothèse, $sigma(C u, dot)= sigma(C' u, dot )$ pour tout $ u in aa$. Or, $bb to aa^*; w !> omega(w, dot )$ est un isomorphisme donc $C=C'$ et par suite 

]
Fixons maintenant $aa,bb,gg in Lambda(n)$ tqs $bb trans gg$. On généralise désormais par réduction symplectique la définition de $QQ$ au cas où $aa$ et $bb$ ne sont pas transverses. 

Les Lagrangiens $aa$ et $bb$ étant isotropes, $aa inter bb$ le sera également et l'image par $pi : aa+ bb to (aa+bb) slash (aa inter bb)$ d'un Lagrangien $FF$ intersecté avec $aa+bb$ sera un Lagrangien de $aa+bb slash (aa inter bb)$. On pose donc dans ce cas
#numbered_eq[$ QQ := Q(pi aa, pi bb; pi gg )$]<eqformequadquotient>

#proposition[Si $gg$ est également transverse à $aa$ alors les formes $QQ$ et $Q(bb,gg;aa')$ vue comme une forme bilinéaire sur $bb slash (aa inter bb)$ sont conjuguées (donc en particulier de même signature).]

#proof[Soit $C : bb to gg$ cadre Lagrangien pour $aa$. On montre facilement que $pi C$ descend au quotient en une application $tilde(C) : pi bb to pi gg$ qui est un cadre Lagrangien pour $pi aa$. Ainsi, $Q(bb,gg;aa)$ restreinte à $pi bb$ est égale à $Q(pi bb, pi gg; pi aa)$ qui est conjuguée à $ QQ := Q(pi aa, pi bb; pi gg )$ par le point 2. de la proposition @propQabc.]



#proposition[$Lambda(n)$ est une variété différentielle de dimension $1/2 n (n+1)$ dont un atlas est donné par les $(Q(aa,bb))_(aa trans bb)$. De plus, la différentielle de $Q(aa,bb)$ en $aa$ ne dépend pas de $bb$ offrant une identification canonique entre de $lk_aa Lambda(n)$ et $S(aa)$.]

#proof[
  #tosource[$Lambda(n)$ est une variété]
  Soient $bb,bb'$ 
]



#lemma[Pour tout $gg in Lambda^k(aa)$ il existe une submersion $R$ définie sur un voisinage ouvert $cal(U)$ de $gg$ et à valeur dans $S(aa inter gg)$ tqe :
+ pour tout $gg' in cal(u), dim ker R(gg') =  dim aa inter gg'$
+ $dd(R)(gg) =: q_(aa inter gg) $ soit la restriction de $S(aa) to S(aa inter gg)$.] #todo[ pas sur de garder la notation $q_(aa inter gg)$]


#proof[Soit $gg in Lambda^k(aa)$ et $bb in Lambda^0(aa) inter Lambda^0(bb)$. Dans une base adaptée de $aa$ on a :
$ QQ = mat(A,0;0,0) $ pour une certaine matrice $A in "GL"_(n-k) (RR)$. Si $gg' in Lambda(n)$ est suffisamment proche de $gg$ alors $gg' in Lambda^0(bb)$ et $ Q(aa,bb;gg')=mat(B,C; C^T,D) $ avec $C,D$ petites et $B$ proche de $A$ (donc inversible). 

Alors : $ mat(I,0;-C^T B^mm, I)mat(B,C; C^T,D) mat(I, - B^mm C; 0,I) = mat(B, 0 ; 0, D- C^T B^mm C). $Posons $R(gg'):=D-C^T B^mm C$. La fonction $R$ ainsi définie est clairement une submersion qui vérifie 1.
Puis, par le calcul, dans les coordonnés $(B,C,D)$ : $dd(R)(gg) = dd(D)$. Ce qui correspond à la restriction demandée.
]

#lemma[Soient $L : [0,1] to Lambda(n)$ courbe différentiable, $t_0 in [0,1]$ tq $ q_(aa inter gg(t_0))(dot(L)_(t_0))!=0$ soit non dégénérée, et $bb in Lambda^0 inter Lambda^0(L_(t_0))$ alors :
$ sgn Q(aa,bb;L_(t)) = sgn Q(aa,bb;L_(t_0)) + sgn q_(aa inter L_(t_0)) (dot(L)_(t_0)) $
pour $t >t_0$ suffisamment proche de $t_0$.]

#proof[Par construction de $R$ dans le lemme précédent en $gg=L_(t_0)$, et non dégénérescence de $q_(aa inter L_(t_0)) (dot(L)_(t_0))$ on a pour $t$ suffisamment proche de $t_0$ $sgn Q(aa,bb;L_(t)) = sgn Q(aa, bb; L) + sgn R(L_(t))$. Or, pour $t$ suffisamment proche de $t_0$ $sgn R (L_(t)) = sgn (R(L_(t_0)) + (t-t_0) dd(R) (L_(t_0))) = sgn q_(a inter L_(t_0)) (dot(L) (t_0))$. La dernière égalité découle de $t>t_0$ et $R(L_(t_0))=0$.]

#inline-note[blabla on définit le Maslov]

#propdef[Soit $L : [0,1] -> Lambda(n)$ chemin continu de Lagrangiens. Fixons $aa in Lambda^0(L_0) inter Lambda^0(L_1)$ et $L' : [0,1] -> Lambda^0(aa)$ reliant $L_1$ à $L_0$. L'entier $[L:aa]:= ind(L*L')$ ne dépend pas du choix de $L'$ et est appelé *nombre d'intersection de $L$ avec $aa$*.]<propdefLaa>

#proof[Le fait que $[L:aa]$ ne dépende pas du choix de $L'$ est une conséquence immédiate de la simple connexité de $Lambda^0(aa)$.]

Notons tout de suite quelques propriétés immédiates du nombres d'indice ainsi défini.
#proposition[Soit $L : [0,1] -> Lambda(n)$ chemin continu et $aa in Lambda^0(L_0) inter Lambda^0(L_1)$.
  + Si $L_0=L_1$ alors $L$ est un lacet et $[L:aa]=ind(L)$
+ Si l'on fixe $0=t_0 < t_1 < ... < t_(j)=1$ tqs $L(t_i) in Lambda^0 (aa)$ et l'on note $L_i$ la restriction de $L$ à $[t_i, t_(i+1)]$ pour $i=0,...,j-1$ alors $[L:aa] = sum_(i=0)^(j-1) [L_(i), aa]$.] <propLaa>


On cherche désormais à obtenir un indice indépendant de $aa$ pour les chemins, ce que ne permet pas la @propdefLaa.

#definition[Pour $aa,aa';bb,bb' in Lambda(n)$ tels que $aa,aa'$ soient transverses à $bb,bb'$ on note $s(aa,aa';bb,bb')$ l'indice de Maslov d'un boucle reliant $bb$ à $bb'$ en]
#todo[introduire $s$]

#proposition[Pour $aa,aa in Lambda(n)$ et $bb,bb' in Lambda^0(aa) inter Lambda^0 (aa')$ :
$ s(aa,aa';bb,bb') = 1/2 (sgn Q(aa,aa';bb) - sgn Q (aa,aa' ;bb)) $] <propcalculsaabb>

#remark[Dans la proposition ci-dessus $aa$ et $aa'$ ne sont _a priori_ pas transverses. Les formes quadratiques $Q(aa,aa';bb)$ et $Q(aa,aa';bb)$ sont à prendre au sens de @eqformequadquotient.]
#proof[Tout d'abord, remarquons que $s(aa,aa';bb,bb') = [hat(L):aa]$ où $hat(L)$ est un chemin dans $Lambda^0(aa)$ reliant $bb$ à $bb'$, que l'on supposera intersecter $Sigma(aa)$ uniquement en $Lambda^1(aa)$ et transversalement.

Par le point 2. de @propLaa, quitte à subdiviser $[0,1]$, on peut supposer que $hat(L)$ intersecte exactement une fois $Lambda^1(aa)$ (le cas où $L$ ne rencontre pas $Lambda^1(aa)$ étant trivial).

Notons alors $t_0$ l'instant où $hat(L)$ rencontre $Lambda^1(aa)$. 


Remarquons tout d'abord, que pour tout $t in [0,1]backslash{t_0}$, $ker Q(pi aa,pi aa'; pi hat(L)_t) = hat(L)_t inter aa = 0 $ donc $sgn Q(pi aa,pi aa' ; pi hat(L))$ est constant sur $[0,t_0[$ et $]t_0,1]$. Ainsi, $ sgn Q(aa,aa';bb) - sgn Q(aa,aa';bb') &= sgn Q(pi aa,pi aa'; pi hat(L)_(t_0-eps))-sgn Q(pi aa, pi aa';pi hat(L)_(t_0+eps))\ &=2 sgn q_(pi aa inter pi hat(L)_(t_0)) (dot(pi hat(L))_t_0) $, #tolink[par formule reliant machin à chose]. 
 
Il suffit de montrer que $sgn q_(pi aa inter pi hat(L)_(t_0)) (dot(pi hat(L))_t_0) = sgn q_( aa inter  hat(L)_(t_0)) (dot( hat(L))_t_0)$.

Soit $gg in Lambda^0(aa) inter Lambda^0(aa') inter Lambda^0(hat(L)_t_0)$.
Par continuité $gg$ est transverse à $hat(L)_(t)$ pour $t$ suffisamment proche de $t_0$. On a par #tolink[montrer le lien pour la définition de positivité] que $dv(Q(aa,gg;hat(L)_t)_(|aa inter hat(L_t_0)),t)_(|t=t_0) = q_(aa inter hat(L)_(t_0)) dot(hat(L)_t_0)$. 



Si l'on suppose que $gg cc aa +aa' $ alors on démontre facilement #toprove[conjugaison de ces trusc] que $Q(aa,gg; hat(L_t))_(|aa inter hat(L)_t_0) = Q(pi aa,pi gg; pi hat(L_t))_(|aa inter hat(L)_t_0) circ pi_(aa inter hat(L)_(t_0))$ donc $sgn q_(pi aa inter pi hat(L)_(t_0)) (dot(pi hat(L))_t_0) = sgn q_( aa inter  hat(L)_(t_0)) (dot( hat(L))_t_0)$. Ce qui conclut.

#todraw[Ce qui se trame à MaslovLand]
#toprove[Invariance modulo indice].
]

#proposition[L'indice $s$ est antisymétrique. Soient $aa,aa' in Lambda(n)$ et $ bb,bb' in Lambda^0(aa) inter Lambda^0(aa'), s(aa, aa' ; bb, bb') = - s(bb,bb';aa,aa'). $] #tosource[Hormander, antisymétrie ]

#proof[Soient $C_1 : aa to bb$ et $C_2 : bb to aa$ cadres Lagrangiens pour $aa'$ et $bb'$ respectivement. Choisissons $(x,y)$ coordonnées sur $FF$ adaptées à la décomposition $aa plus.o bb$ et considérons le symplectomorphisme $ phi : & FF & to & FF \ & (x,y) & !> & (-y,x). $
qui permute $aa <-> bb$ et $aa' <-> bb'$ et conjugue $C_1$ et $C_2$. Par suite, $Q(aa,bb;aa') = ss(C_1, dot)_(|aa) = ss(phi C_1, phi )_(|aa) sim.eq ss(C_2, dot)_(|bb) = Q(bb,aa;bb')$. Or par #tolink[lien avec la permutation de $QQ$], $sgn Q(bb,aa;bb') = sgn Q(bb,aa; bb')$. Cette formule restant vraie en remplaçant $aa$ par $aa'$, par la @propcalculsaabb on trouve 
$ 
s(aa,aa';bb,bb') &= 1/2(Q(aa,aa';bb)-Q(aa,aa';bb'))\
                 &= -1/2 (Q(aa',bb;aa) - Q(aa',bb';aa))\
                 &= -1/2 (sgn Q(bb,aa'; bb')-sgn Q())\
                 &= -1/2 (sgn Q(bb,bb';aa') - sgn Q(bb,bb';aa))\
                 &= -s(bb,bb';aa,aa')
$
] #todo[I'm too tired for this shit]

#propdef[Soit $L:[0,1] to Lambda(n)$ et $aa in Lambda^0(L_0) inter Lambda^0(L_1)$. L'entier $ ind (L) := [L:aa] + ind Q(L_1,aa;L_0)$ ne dépend pas du choix de $aa$. On l'appelle *indice de Maslov-Duistermaat de $L$*.
]<defMD>

#proof[Soit $aa' in Lambda(n)$ transverse à $L_0$ et $L_1$. La forme quadratique $Q(L_1,aa;L_0)$ étant non dégénérée, $ind Q(L_1,aa;L_0)= n - 1/2 sgn Q(L_1,aa;L_0)$. Ainsi, par #tolink[Oui le calcul]

$[L:aa']-ind Q(L_1,aa';L_0) &= [L:aa] + s(aa,aa';L_0,L_1) + ind Q(L_1,aa';L_0)\
                          &= [L:aa'] - s(L_0,L_1;aa,aa') + ind Q(L_1,aa';L_0)\
                          &= [L:aa'] +n - 1/2(sgn Q(L_1,aa;L_0) - sgn Q(L_1, aa';L_0) + Q(L_1,aa';L_0))\
                          &= [L:aa'] + ind Q(L_1,aa;L_0)
$
] 


=== Indice de Maslov Duistermaat

/*On pose $[L:aa] = ind(L*L')$ qui ne dépend pas du choix de $L'$ par invariance par homotopie de $ind$ et simple connexité de $Lambda^0(aa) sim.eq S_n (RR)$. 



On cherche maintenant à éliminer la dépendance en $aa$. Pour ce faire, par transversalité de $L_0$ et $L_1$ avec $aa$, on a $C:L_1 to aa$ linéaire tq $L_0={u+C u ; u in L_1}$.


On considère alors la forme quadratique$ Q(L_1, aa; L_0) : & L_1 &to & RR \ & u & !> & sigma(C u, u). $

#definition[On appelle *indice de Maslov-Duistermaat* et on note $ind(L)$ la quantité $ind(L) := [L:aa]- ind Q(L_1,aa;L_0)$.]*/

#remark[Si $L$ est une boucle les indices de Maslov et Maslov-Duistermaat coïncident : il suffit de prendre $L' eq.triple L_0=L_1$ et de remarquer que $ind (L_0,aa;L_0)=0$.]

//De plus, $aa$ étant Lagrangien et transverse à $L_0$ et $L_1$ on obtient deux isomorphismes $L_0 to aa^*$ et $L_1 to aa^*$ définis par $x in L_(0,1) mapsto sigma(x,dot )_(|aa)$. Or, on a de plus que si $v in L_0$ s'écrit $v= u + a in L_1 plus.o aa$ alors $sigma(v,dot )_(|aa)=sigma(u,dot )_(|aa)$. Ainsi

#proposition[Soit $L: [0,1] to Lambda(n)$ chemin continu.
  + L'entier $ind(L)$ ne dépend que de la classe d'homotopie de $L$ (a extrémités fixées).
  + L'indice est invariant par l'action de $"Sym"(F)$.
  + Si $M : SS_1 to Lambda(n)$ est une boucle tqe $M_0=L_1$ alors $ind(L*M) = ind(L) + ind(M)$. ]<propMD>

  #proof[
    Fixons $aa in Lambda(n)$ transverse à $L_0$ et $L_1$ et $L' : [0,1] to Lambda(n)$ tq $L_0'=L_1$ et $L_1'=L_0$.
  + Soit $M : [0,1] to Lambda(n)$ homotope à $L$ et de mêmes extrémités. Alors les boucles $L*L'$ et $L*L'$ sont homotopes donc $[L:aa]=[M:aa]$ par invariance par homotopie de l'indice de Maslov pour les boucles.
  + Soit $A in "Sym"(FF,sigma)$. L'invariance de l'indice de Maslov par l'action de $"Sym"(FF)$ donne $[L:aa]=ind(L*L')=ind(A L *A L' ) = [A L', A aa]$. Puis $Q(L_1,aa;L_0)$ et $Q(A L_1, A aa; A L_0)$ sont clairement conjugués donc de même indice. Ce qui conclut.
  + On a par additivité de l'indice de Maslov $[L*M:aa] = ind(L*M*L') = ind(L'*L*M)=ind(L*L') + ind(M)$. Puis du fait que $ind Q(L_1,aa;L_0)$ ne dépende que des extrémités du chemin considéré et par 1., on trouve $ind(L*M) = ind(L)+ind(M)$.
]

#remark[Le troisième point de la proposition précédente ne marche pas si $M$ n'est pas un lacet. #todo[contrexemple de l'additivité de la concaténation des chemins]]

#proposition[ Soient $A : SS_1 to "Sym"(FF)$ et $L,L' : [0,1] to Lambda(n)$. Alors en notant $A L:= (A_t L_t)$ on a l'égalité suivante :
$ ind(A L)- ind(A L') = ind(L)-ind(L'). $]<propegalacet>

#proof[Le chemin $A L$ est homotope au chemin $A_0 L * A L_1$. Ainsi par les points 2. et 3. de la @propMD on trouve (car $A L_1$ est un lacet) $ind(A L) = ind(L) + ind(A L_1)$. Enfin par le point 1. de @propMD et par connexité de $Lambda(n)$ on a $ind(A L_1) = ind(A L_1')$ d'où l'égalité.]

=== Indice de Maslov-Duistermaat pour les fibrés symplectiques sur le cercles

Soit $E to SS_1$ fibré symplectique de fibre $(FF, sigma)$. On considère alors $V$ un sous-fibré Lagrangien de $E$ et $R : [0,1] to Lambda(E)$ un chemin de Lagrangiens tq $R_t cc E_t$ pour tout $t in SS_1$ (sans avoir nécessairement $R_0=R_1$).

#propdef[Le fibré symplectique $E$ est trivialisable et si $tau : E sim.eq SS_1 times FF$ en est une trivialisation alors en identifiant $tau(V)$ à une boucle et $tau(R)$ un chemin dans $Lambda(n)$ on trouve que la quantité 
$ ind_V(R) := ind(tau(R)) - ind(tau(V)) $
ne dépend pas de $tau$. On l'appelle *indice de Maslov de $R$ relativement à $V$*.] <defMDfibré>

#proof[La trivialisabilité de $E$ est une conséquence immédiate de la connexité de $"Sym"(FF)$.

#tosource[$E to SS_1$ trivialisable]

Soient $tau,tau' : E sim.eq SS_1 times FF$ des trivialisations de $E$. On pose $ A : & SS_1 & to & Sym\ &t &!> & tau'_t tau_t^(-1). $#todo[pas sur que ce soit très bien...]On a alors $tau'(R) = A tau(R)$ et $tau'(V) = A tau(V)$. Ainsi, par la @propegalacet, $ind(tau(R))-ind(tau(V)) = ind(tau'(T))-ind(tau'(V))$.
]
=== GF-time !!

On se place dans $RR^(2m)$ muni de sa forme symplectique canonique et on fixe $k in NN$.

#definition[Une forme quadratique $Q : RR^(2m) times  RR^k$ est dite *génératrice* si c'est une fonction génératrice au sens de #tolink[définition fonction génératrice]. Si l'on écrit $Q(X)=1/2 X^T B X$ avec $X = vec(w, xi)$ et $B = mat(a,b;b^T,c)$  dans les bases canoniques de $RR^(2m)$ et $RR^k$, alors $Q$ est génératrice ssi $(b^T space c)$ est de rang maximal $k$. 

Dans ce cas on pose comme dans #tolink[partie fonction génératrice], $Sigma_Q = {(w,xi) in RR^(2m) times  RR^k; b^T w+c xi =0}$ et $ i_Q : & Sigma_Q & to & RR^(2m) sim.eq lk^* RR^m \ & (w,xi) & !> & (w, a w + b xi) $
définit un plongement linéaire Lagrangien. On dit que $L = im(i_Q)$ est engendré par $Q$.]

#example[Si $W$ est un Lagrangien de $RR^(2m)$ admettant une fonction génératrice $S$, $z$ un point de $W$ et $(w,xi)$ le point correspondant dans $Sigma_Q$ alors $dc(S)(w,xi)$ est une forme quadratique génératrice pour $T_z W$.]

#theorem[Soit $L : [0,1] to Lambda(2m)$. Il existe $(Q_t)_(t in [0,1])$ chemin continu de formes quadratiques tq $Q_t$ engendre $L_t$ pour tout $t in [0,1]$.]

#proof[ #toprove[existence des fonctions génératrices linéaires]]

#propdef[Si $L$ et $(Q_(t))_(t in [0,1])$ sont comme dans le théorème ci-dessus, alors l'entier $ind_gf (L) := ind Q_1 - ind Q_0 $ ne dépend que de $L$. On l'appelle *indice gf* de $L$.]

#proof[ #toprove[définition de l'indice gf] ]

#proposition[ Si $L$ est un lacet de Lagrangiens de $RR^(2m)$ alors $ind_gf (L) =ind(L)$.]<propcoinclacet>

#proof[#toprove[ind gf et Maslov coïncident sur les lacets]]

#definition[Soit $A: [0,1] to "Sym"(RR^(2n))$ chemin continu de symplectomorphismes. Alors par l'identification #tolink[identification] on obtient $L := I("graph" A)$ chemin de Lagrangiens de $lk^* RR^(2n) sim.eq RR^(2m)$ avec $m=2n$. On définit alors *l'indice gf* de $A$ comme $ind_gf (A) := ind_gf (L)$.]

#proposition[Soit $Phi$ isotopie hamiltonienne de $RR^(2n)$ à support compact et $S$ une famille de fonction génératrice quadratique à l'infini associée. #tolink[fonctions génératrices] Soit $z in RR^(2n)$ un point fixe de $Phi_1$ et $(z,xi)$ le point critique de $S_1$ associé. Alors en posant $A = (dd(Phi_t)(z))_(t in [0,1])$ on a l'égalité :
$ ind_gf (A) = ind dc(S_1) (z,xi) - ind Q_oo. $
]<propeqgfQinf>

#proof[
On considère $Psi$ l'isotopie hamiltonienne de $lk RR^(2n)$ donnée par $Psi_t = I Phi_t I^(-1)$. Par construction des fonctions génératrices, on dispose de $(w_t, xi_t)_(t in [0,1])$ chemin continu dans $RR^(2n)times RR^k$ tq $i_(Q_t) (w_t, xi_t) = Psi_t (z,0)$. On a alors que $Q_t := dc(S_t) (w_t, xi_t)$ est une fonction génératrice de $lk_Psi_t (z,0) tilde(Gamma)_t = I("graph" A_t)$. Ainsi par définition de $ind_gf (A)$ on a $ind_gf (A) = ind Q_1 - ind Q_0$.

Montrons maintenant que $ind Q_0 =ind Q_oo$. Or $Psi_0$ étant l'identité, par #tolink[théorème liant les noyaux de $dc(S)$ et $dd(Phi)-Id$], la dimension de $ker dc(S_0)$ est constante : $dim ker dc(S_0)(w,xi)=dim ker dd(Psi_0)(w)-Id =2n$ pour tout $(w,xi) in RR^(2n)times RR^k$. Par conséquent, l'indice de $dc(S_0)$ est lui aussi constant sur $Sigma_S_0 $ et $S_0$ étant égal à $Q_oo$ en dehors d'un compact, $ind dc(S_0) (w_0,xi_0)=ind Q_oo$.

D'où, finalement, $ind_gf (A) = ind dc(S_0)(w,z) - ind Q_oo$.

//$d S_0$ est nulle sur $Sigma_S_0$ donc $dc(S_0_(|Sigma_S_0)) =0$ et par #todo[le lien] on a pour tout $(w,xi ) in Sigma_(S_0)$, $ker dc(S_0) (w,xi) = ker dc(S_0)(w,xi)_(|T_( (w,xi)) Sigma_S_0) = lk _( (w,xi)) Sigma_S_0$. Ainsi $(w,z) !> dim ker dc(S_0) (w,z)$ est constant sur $Sigma_S_0$ donc il en va de même pour $ind dc(S_0)$. Or par hypothèse $S_0=Q_oo$ en dehors d'un compact, d'où $ind dc(S_0) (w_0,xi_0) = ind Q_oo $ et l'égalité demandée.
]

#theorem[Soit $A : [0,1] to "Sp"(RR^(2n))$ un chemin de symplectomorphismes. Si $A_0 = Id$ alors $ind_gf (A) = ind I("graph" A).$]


#proof[
Remarquons tout d'abord que puisque :
+ l'on dispose d'une décomposition $RR^(2n) = F plus.o F'$, en sous-espaces symplectiques, stables par $A_1$ tqe le spectre de $A_(1|F)$ ne contienne pas $-1$ et que celui de $A_(1|F')$ soit réduit à $-1$,
+ le groupe des symplectomorphismes d'un espace vectoriel est connexe,
+ les deux indices considérés sont additifs vis-à-vis de la somme directe #toprove[Les indices sont additifs vis-à-vis de la somme directe]
on peut supposer que le spectre de $A_1$ ne contienne pas $-1$ ou soit réduit à $-1$.

Dans le premier cas, cela signifie que $aa:=0 times  RR^(2n) $ est transverse à $L_1$ et $aa trans L_0 = RR^(2n) times 0$ par hypothèse. Soit alors $L' [0,1] to Lambda^0(aa)$ reliant $L_1$ à $L_0$. Alors, par définition $[L:aa]=ind(L*L')$. Or par la @propcoinclacet, $ind_gf (L*L')=ind(L*L')$. Puis par additivité de $ind_gf$ #todo[modifier la propriété @propcoinclacet], on obtient $[L:aa] = ind_gf (L) + ind_gf (L')$.

Ensuite puisque $L'_t  trans RR^(2n) times 0 $ pour tout $t in [0,1]$. Soit $C_t : L'_1 to aa $ le cadre lagrangien associé à $aa,L'_1$ et $L_t$. Alors $Q'_t : w !> 1/2 chevron.l C'_t w,w chevron.r$ est une forme quadratique génératrice pour $L'_t$ #todo[vérifier que la déf est bonne]. On a en particulier $C'_1=0$ et donc $Q'_1=0$. Ainsi $ind_gf (L')=ind_gf (Q'_1)-ind_gf (Q'_0) = -ind_gf Q'_0$.

Puis considérons $C : L_1 to aa$ tq $L_0={u +C u ; u in L_1}$. Si $u in L_1 = L'_0$ alors $u = v + C'_1 v$ pour un certain $v in L_0$. Ainsi, par unicité de la décomposition $L_0 plus.o alpha$, nécessairement, $C u= - C'_1 v$. #todo[move that so next line is more natural]
Par suite, $Q(L_1,aa;L_0)(u)=omega_(RR^(2n))(C u,u)=-omega(C'_1 v, v) = Q'_0(v)$.

Ainsi, $ind Q'_0=ind Q(L_1, aa;L_0)$ et donc
$ 
ind (L) &=[L:aa]+ind Q(L_1,aa;L_0)\ 
        &= ind_gf (L) + ind_gf (L') + ind Q(L_1,aa;L_0)\
        &= ind_gf (L) - ind Q'_0 + ind Q'_0\
        &= ind_gf (L).
$

Supposons maintenant que le spectre $A_1$ soit réduit à $-1$. On pose $aa = I("graph" B) = {(a/2,b/2,b,a) ; a,b in RR^(n)}$ où $B = mat(0,I;-I,0)$. Alors $aa$ est transverse à $L_0$ et $L_1$ et 

l'on peut joindre $A_1$ à $-Id$ par des symplectomorphismes ayant $-1$ comme seule valeur  propre.







]<propindgfId>

= Le système hamiltonien 

Soit $L$ variété fermée de dims $n$ et $j : L arrow.hook RR^(2n)$. On munit $TLL$ de ses coordonnées locales cotangentes $(q,p) $, de $ww = dd(q) and dd(p)$ forme symplectique canonique. Fixons alors une métrique $norm(dot)$ sur $TL$ qui induit une métrique sur $TLL$ et un isomorphisme $TLL sim.eq TL$. On pose $B_rho := {(q,p) in TLL | norm(p) <= rho}$.

On considère $h : [0,+oo] -> [-oo,0]$ vérifiant :
+ $h eq.triple -a$ sur $[0,eps/2]$
+ $h$ est convexe et strictement croissante sur $[eps/2,eps]$
+ $h' eq.triple c$ sur $[eps,rho-eps]$
+ $h$ est concave et strictement décroissante sur $[rho - eps, rho-eps/2]$
+ $h eq.triple 0$ sur $[rho-eps/2, +oo]$
avec $a > c_"gf"(V) $ et $c>0$ distinct de la longueur de toute géodésique close et $eps>0$ petit. #todraw[dessin de l'hamiltonien]

On considère alors l'hamiltonien à support compact $H : TLL -> RR$ défini par $H(q,p) := h(norm(p)) $ et on note $(phi_t)_(t in [0,1])$ l'isotopie hamiltonienne correspondante.

#proposition[Le flot $phi$ est une reparamétrisation du flot cogéodésique (voir @defCogeod) $g$ et si $z = (p,q)$ est un point fixe de $phi_1$ alors la projection $gg$ de sa $phi$-orbite sur $L$ est une géodésique fermée de longueur $ell(gg) = h'(norm(p))$.]<propPhiCogeod>

#proof[
D'après, la @propCogeodHam le flot cogéodésique est généré par l'hamiltonien $K : (q,p) !> norm(p)^2 /2$, qui est lié à $H$ par la relation $H = a (K)$ où $a : s !> h(sqrt(2s))$. Ainsi, en posant $c : z = (q,p) mapsto a'(K(z)) (h'(norm(p)))/norm(p)$, on obtient que $X_H (z) = c(z) X_K (z)$.

Par conséquent, pour tout $z in TLL$,
$ dv(g_(c(z)t) (z),t) = c(z) K(g_(c(z)t)(z)) = H( g_(c(z)t) (z)) $
et donc $phi_t (z) = g_(c(z)t) (z)$pour tout $t in [0,1]$. Ce qui prouve la première assertion.

  Si $z$ est un point fixe de $Phi_1$, le fait que $gg := (pi_L (phi_t (z)))_(t in [0,1])$ soit une géodésique fermée découle immédiatement du résultat précédent et enfin, une géodésique étant de vitesse constante :
  $ ell(gg) = int_0 ^1 norm(dot(gg)_t) dd(t) = int_0^1 norm( dv(g_(c(z)t)(z),t)) = int_0^1 c(z) norm(p) dd(t) = c(z) norm(p) = h'(norm(p)). $
]
Fixons $z =(p,q)$ un point fixe de $phi_1$.
On considèrera alors le fibré symplectique $E to SS_1$ dont la fibre $E_t$ au point $t in SS_1$ est donnée par

$ E_t := tilde(TTLL(z)) times TTLL(phi_t (z)) $
et munie de la forme symplectique $omega_E := - pi_1^* omega_L + pi_2^* omega_L$. On notera $V$ le sous-fibré lagrangien de $E$ de fibre en $t$ donnée par $ V_t = vert(z) plus.o vert(phi_t (z)) $
où $vert(x)$ désigne le sous espace vertical en $x in TLL$ du fibré $TLL to L$.

#definition[La fonction $t!> dd(phi_t (z)) : TTLL(z) to TTLL(phi_t (z))$ définit un chemin continu $Gamma : [0,1] to Lambda(E)$ de sev lagrangiens. On notera alors $ind_phi (z)$ l'indice $ind_V (Gamma)$ définit à la @defMDfibré.]


Notons $gg$ la géodésique associée au point fixe $z$ dans la @propPhiCogeod et $i(gg)$ son indice de Morse. On peut alors relier ce dernier à l'indice $ind_phi (z)$ définit ci-dessus via :

#proposition[$ind_phi (z) = cases(
   i(z)+n "si h convexe en " norm(p), i(z)  + n -1 "si h concave en " norm(p)
)$] <propMorseMaslov>

#proof[La preuve du cas convexe se trouve dans #tosource[Duistermaat]. 
Déduisons-en la preuve dans le cas concave.

]


== Faits sur le flot cogéodésique



#propdef("Flot cogéodésique")[Soit $hat(z) in TL$. Il existe une unique géodésique $gg$ sur $L$ tqe $(gg_0, dot(gg)_0) = hat(z)$. On appelle alors *flot géodésique*#footnote[Lequel est bien défini car _L_ est compact donc complet.] l'application 
$ hat(g) : &TL times [0,1] &to &TL \
           &(z,t) & !> & (gg_t,dot(gg)_t)  $
et *flot cogéodésique*, noté $g : TLL times [0,1] to TLL$ son conjugué par l'isomorphisme $TLL sim.eq TL$.]<defCogeod>

Le fibré $TTL$, muni la connexion de Levi-Civita associée à la métrique $norm(dot)$ admet une décomposition 
#numbered_eq[$ TTL = hor plus.o vert $]<eqDecompHorVert>
en sous-fibrés horizontal et vertical. Ces derniers sont alors canoniquement isomorphes à $TLL$ et sont donc munis d'un produit scalaire canonique.

#proposition[Soit $(q,U)$ système de coordonnées normales sur $L$ en $pi_L (z)$ sont on déduit les coordonnés symplectiques $((q,p), U times RR^(2n)$ sur $T^*L$. Alors $(q, partial q, p, partial p)$ est un système de coordonnées sur $TTL$ sur lequel 
$ TTL = hor plus.o vert = ker dd(p) plus.o ker dd(q).$]

#proof[Dans le système de coordonnées ci-dessus, $pi_L : (q,p) !> q$ donc $dd(pi_L)=dd(q)$ et par suite $vert :=ker dd(pi_L) = ker dd(q)$.

Ensuite, $ hor(z) = Im dd(s)_(pi_L (z))$ où $s$ est une section du fibré $TLL to L$telle que $s( pi_L (z))=z$ et $nabla_X s =0$ pour tout $X in T_(pi_L (z)) L$, $nabla$ étant la connexion de Levi-Civita associée à $norm(dot)$. Or remarquons que si l'on note $(q_0,p_0)$ les coordonnés en $z$, $s : (p,q) !> p_0 dd(q) $ convient. En effet, $sigma(pi_L (z))= z$ et tout $X in T_(pi_L (z)) L$ s'écrit $X = sum_(i=1)^n X_(i) dd(q_i)$ donc $nabla_X s = sum_(i=1)^n sum_(j=1)^n p^j_0 X_j nabla_(dd(q_i))dd(q_j)$. Or $nabla_(dd(q_i))dd(q_j)$ est l'image par l'isomorphisme $TLL sim.eq TL$ de $nabla_(partial q_i) partial q_j = 0$ par le choix des coordonnées normales. 
Ainsi, $hor (z) = im dd(s)_(pi_L (z))$ et lu dans les coordonnées $dd(s)_(q_0,p_0) = (q_0, dd(q)_(z), p_0,0)$. Ainsi, $hor(z) = ker dd(q)$.
]#todo[Clarifier les 40 identifications dans les coordonnées.]

#proposition[Dans la décomposition $TTL = "Hor" plus.o "Vert"$, la forme symplectique $omega_L$ s'écrit  $ omega_L (z) (delta z, delta z') = chevron.l delta_h z, delta_v z' chevron.r - chevron.l delta_v z, delta_h z' chevron.r  $]<propDescriptionOmega>

#proof[La formule est définie de manière intrinsèque. Il suffit donc de vérifier l'égalité dans un système de coordonnées. Supposons que $(q, U)$ est un système coordonnées locales normales en $z$ auquel on associe $(q, partial q, p, partial p)$ système de coordonnées sur $TTL$ comme précédemment. Par ce qui précède, si l'on note $pi_h : TTL to hor$ et $pi_v : TTL to vert$ les projections sur les espaces vertical et horizontal alors, par ce qui précède $pi_h = dd(q)$ et $pi_v = dd(p)$. Ainsi, $omega_L = sum_(i=1)^n dd(p_i) and dd(q_i) = sum_(i=1)^n pi_v and pi_h$ ce qui donne l'égalité demandée.

// On pose $v_(i)=dot(u)_i$ on a alors que $(u,v)$ forment des coordonnées locales pour $TLL$. Dans ces coordonnées $omega_L = sum dd(u_(i)) and dd(v_(i))$ donc à association près $omega_L = sum dd(u_(i))and dd(dot(u)_(i)) $.

//Puis par le calcul c'est égal à ce que l'on souhaite car on est en coordonnées normales. 
]

#proposition[Le flot cogéodésique est engendré par l'hamiltonien 
$ K : & TLL &-> &RR\
  &z=(q,p) &mapsto & norm(p)/2. $
qui a pour gradient symplectique le champ de vecteurs qui en $z = (p,q)$ vaut $X_K (z)=(p,0) in hor plus.o vert sim.eq TLL plus.o TLL$.]<propCogeodHam>

#proof[On se place dans $q$ coordonnées normales. On a que $K(z)=sum p_i^2 /2 $ donc $dd(K) (z) = sum p_i dd(p_(i)) = chevron.l p, dd(p) chevron.r = omega_L ( (p,0), dot )$ en identifiant $p$ à son image dans $hor(z)$. Ainsi, on a bien $X_K (z) = (p,0)$.] 

Ainsi on en déduit que si $gg$ est une géodésique alors $dd(dot(c)(t))/dd(t)= (dot(c)(t), 0) = X_K (dot(c(t))). $ Ainsi, $c(t)=g_t (c(0))$.

#proposition[Les champs de vecteurs $g-$invariants le long de $gg$ géodésique sont en bijection avec les champs de Jacobi.]<bijginvJacobs>

#proof[Soient $eta_0 in T_z TLL$. Alors $eta_t := dd(g_t)(eta_0)$ est un champ de vecteur $g$-invariant.

Soit $k$ courbe sur $TLL$ tqe $pdv(k,s)_(| s=0) = eta_(0)$. Posons $eta_t := pdv(g_t k_s,s)_(|s=0)$. Puis remarquons que par la proposition précédente :
$ pdv(,t) pi_L g_t (k_s)=T pi_L.(pdv(,t) g_t (k_s))=T pi_L.(g_t (k_s),0)=g_t (k_s). $

Donc pour tout $s$, $t !> pi_L g_t (k_s)$ est une géodésique. Ainsi la partie horizontale de $eta_t$ : 

$ pi_h (eta_(t) ) = T pi_L pdv(g_t (k_s),s)_(|s=0) = pdv(,s) pi_L g_t (k_s)_(|s=0) $ est un champ de Jacobi.

Puis, en utilisant que $nabla/dd(t) g_t (k_s)_(|s=0) = K. pdv(,s) g_t (k_s) _(|s=0) $ et $nabla/dd(s) pdv(,t) = nabla/dd(t) pdv(,s) $ on obtient :
$ eta_t &= pdv(,s) g_t (k_s)_0 \ 
        &= (T pi_L pdv(,s) g_t (k_s)_0, pi_h pdv(,s) g_t (k_s)_0 )\ 
        &= (T pi_L pdv(,s) g_t (k_s)_0, nabla/dd(s) g_t (k_s)_0 )\ 
        &= (eta_(t,h), nabla/dd(s) pdv(,t) pi_L g_t (k_s)_0)\ 
        &= (eta_(t,h), nabla/(dd(t)) eta_(t,v)). $]

#let fibrator = $E$

#rappel[Si $eta$ est un champ de Jacobi le long d'une géodésique $gg$ tel que $eta_0 = aa dot(gg)_0$ et $nabla eta_0 = bb dot(gg)_0$ pour deux réels $aa,bb$, alors $eta_t = (aa+bb t) dot(gg)_t$.]<rappelJacobs>

#proof[#tosource[Parellèlisme des Jacobs]]


Puisque $z=(q,p)$ et $"T"_q L sim.eq "T"_q^*L = RR p plus.o p^perp$, on obtient par @eqDecompHorVert deux décompositions $hor = hor' plus.o hor''$ et $vert = vert' plus.o vert''$. On pose alors $fibrator':=hor' plus.o vert'$, et $fibrator'':= hor'' plus.o vert''$, sous-fibrés symplectiques orthogonaux et de dimension respectives $2$ et $2n-2$.

#proposition[Le flot cogéodésique préserve cette décomposition. De plus, le sous-fibré $fibrator'$ est trivial et pour $t in RR$, l'isomorphisme de fibré induit $T (g_t) : fibrator' to fibrator'$ s'écrit dans les bases naturelles :
$ mat(1,t;0,1). $
]<propSplitStable>

#proof[
  Tout d'abord, par la @propDescriptionOmega $omega((p,0),(0,p)) !=0$ et $fibrator'$ est l'orthogonal symplectique de $fibrator''$. Or par la @propCogeodHam il suffit donc de montrer que $fibrator'$ est invariant. 
  D'abord, dans la décomposition $TTLL(z) = "T"^*_z L plus.o "T"^*_z L$ prise en $z=(p,q)$, par la @propCogeodHam
  $ T_z phi_t (p,0) &= T_z g_t X_K (z)\
                    &= pdv(,s)g_t circ g_s (z)_(|s=0)\
                    &= X_K (g_t (z)) in hor'( phi_t (z)). $
  Puis, d'après, la @bijginvJacobs, $t !> T_z g_t (0,p)$ est un champ de vecteurs $g$-invariant le long de $t!> g_t (z)$. Il s'écrit donc $T_z g (0,p) = (eta, nabla eta)$ où $eta$ est un champ de Jacobi le long de $t!> g_t(z)$. Or $eta_0 = 0$ et $nabla eta = p$. Ainsi, par le @rappelJacobs, $eta_t = t g_t (z) $ et donc $T_z g.(0,p) = (t g_t (z), g_t (z)) in fibrator'$. #todo[rewrite the proof to make it more coherent. ]

Enfin, la trivialisation est donnée par les identifications $hor'(z) sim.eq RR p$ et $vert'(z) sim.eq RR p$ en $z=(q,p)$ qui permettent d'obtenir $fibrator' sim.eq L times RR^2$ et les calculs ci-dessus donnent la forme de $T_z phi_t $ dans les bases naturelles.
]
== Fin de la preuve

#proof[En différentiant la formule obtenue dans la preuve de la @propPhiCogeod en $z$ on obtient :
#numbered_eq[$T_z phi_t = T_z g_(c(z)t)  + [t T_z c ] X_K ( phi_t (z)).$]<eqDiffPhi>

Remarquons que si $v in fibrator''_z$ alors $T_z c.v= 0 $. Ainsi sur $fibrator''$, $T_z (phi_t) = T_z g_t$ ne dépend pas de la concavité ou convexité de $h$ en $z$.

  La décomposition $TTL = fibrator' plus.o fibrator''$ nous permet de séparer $E$ $E = E' plus.o E''$, somme symplectique et nous donne $V=V'plus.o V''$ et $Gamma = Gamma' plus.o Gamma''$ décomposition en sous-fibrés Lagrangiens de $E'$ et $E''$. Ainsi, par additivité #tolink[additivité du Maslov nouveau], $ind_phi (gg)=ind_V (Gamma) = ind_V' (Gamma') + ind_V''(Gamma'')$. Par ce qui précède, seul $ind_V' (Gamma')$ dépend du caractère connexe ou convexe de $h$ en $z$. On s'attèlera donc à le calculer.


  Si $v=(aa, bb) in fibrator_z' = hor'(z) plus.o vert'(z) sim.eq RR^2$ alors par la @propSplitStable et l'équation @eqDiffPhi, la matrice  $ T_z phi_t v$ dans les bases naturelles est : 
  $ mat(1, c(z)t; 0,1) + t (0, h''(norm(p))- c(z)) vec( 1,0) 
  &= mat(1, h''(norm(p))t ; 0,1). $

  La @propSplitStable nous offre les trivialisations de $E' sim.eq overline(RR^2) times RR^2$, dans laquelle $V' sim.eq (0times RR) times (0times RR)$ et $Gamma_t = "graph" (A_t)$ où $A_t$ est l'endomorphisme canoniquement associé à la matrice ci-dessus. Posons $aa := (0 times RR) times(0 times RR) in Lambda(2)$ cet espace est transverse à $Gamma_t$ à tout temps $t in [0,1]$ donc par la @defMD $ind(L) = ind Q(Gamma_1,aa ; Gamma_0)$. Or $Q(Gamma_1, aa; Gamma_0) = - Q(Gamma_0, aa; Gamma_1) $ donc $ind(L) = "coind" Q(Gamma_0,aa:Gamma_1)$.
  Soit $C : Gamma_0 to aa$ le cadre lagrangien associé à $Gamma_1$. L'espace $Gamma_0$ étant la diagonale, on en déduit par un simple calcul que
  $C : (u_1,u_2; u_1,u_2) in Gamma_0 !> (-h''(norm(p)) u_2,0;0,0) in aa. $
  Ainsi, pour tout $u = (u_1,u_2;u_1,u_2) in overline(RR^2)times RR^2$ 
  $ Q(Gamma_0,aa;Gamma_1) u &= (-omega_(RR^2) plus.o omega_(R^2)) (C(u),u)\
                            &= - omega_(RR^2) ( (-h''(norm(p))u_2, 0), (u_1,u_2)) + 0 \
                            &= h''(r) u_2^2. $

Par suite, par la @defMDfibré, $
  ind_V' (Gamma') &= ind Gamma' - ind V'\ 
                  &= "coind" Q(Gamma_0,aa; Gamma_1)\
                  &= cases(
                             1 & " si " h''(norm(p))>0,
                              0 & " si " h''(norm(p))<0
                          ) $
Ainsi, $ind_phi^"concave" z = ind_phi^"convexe" z -1$. Ce qui conclut la preuve @propMorseMaslov.
]


= La vraie vie c'est dans $RR^(2n)$

Soit $(V,J)$ voisinage tubulaire de $j(L)$ dans $RR^(2n)$. On défini un nouveau hamiltonien $HH$ de flux $Phi$ via : 
$ cases(
    HH = H circ J^(-1)& "sur V", HH eq.triple 0 & "en dehors"
) $.

#proposition[Si $a>c_"gf"(V)$ et $c>0$ est distinct de la longueur de toute géodésique fermée, alors il existe $z=(p,q)$ point fixe de $phi_1$ tq $h$ est strictement convexe ou concave en $norm(p)$.]


#proof[On a que $c_-(HH) = 0$ car $HH<=0$ donc $c_+(HH)>0$ car $Phi_1$ n'est pas l'identité #y. Par suite on a $z$ pt fixe de $Phi_1$ tq $0< cal(A)_HH (z)=c_+(HH)<= c_"gf"(V)$ donc $z in V$ et $HH(z) != a$ car sur cet ensemble $cal(A)_HH = a >c_"gf"(HH)$. Posons $(q,p) :=J^(-1) (z)$ qui est un point fixe de $phi_1$ tq $norm(p) in ]eps/2, rho-eps/2[$ mais par ce qui précède, $h'(norm(p))$ est la longueur d'une géodésique fermée (celle associée à $z$) donc nécessairement $h$ convexe en $norm(p)$.]

#definition[L'entier $ind_gf space z:=ind "d"^2 S_1 (z,xi)-ind Q_oo$ ne dépend pas du choix de $S_1$ mais uniquement de $Phi_1$.] #y

#proposition[Le point fixe du lemme précédent peut-être choisi de sorte à ce que $2n-nu(z)<= ind_"gf" space z <=2n$ où $nu(z):= dim (ker dd(phi_1)(z)-I d)$. On remarquera que #todo[$nu(z)=nu(gamma)+1$.]] <propeqindice1>

#proof[Soit $z$ un tel point fixe. On lui fait correspondre $(z,xi)$ point critique de $S_1$ tel que $c=S_1(z,xi)$ mais par construction $H^(2n+ind Q_oo)(S_1^(c+-eta))!=0$. Ainsi par théorie de Morse-Bott #todo[Faire le lien entre homologie et points critique] on a un point critique $(z,xi)$ de $S_1$ tq $ind "d"^2S_1 (z,xi) <= 2n+Q_oo <= "d"^2 S_1(z, xi)+ dim ker "d"^2 S_1(z,xi)$.

Ensuite, montrons que $ker "Id"-dd(Phi_1) sim.eq ker "d"^2 S_1 (z,xi)$. Posons $Sigma:=Sigma_1$. L'application 
$ i : & Sigma & to  & tilde(Gamma)_t <= "T"^*RR^(2n) sim.eq RR^(2n) times  RR^(2n) \
      & e=(w,xi) & !> & (w, pdv(S,w)(w,z)) $ est un plongement.

  Tout d'abord, si $V in ker dc(S_1 (z,xi))$ alors $V in ker dd(pdv(S_1,xi))(w,xi) = lk_((w,xi)) Sigma$. Il suffit donc d'étudier $dc(S_1)(w,xi)_(|T_( (w,xi)) Sigma) = dd(pdv(S_1,w))(w,xi)_(|T_( (w,xi)) Sigma) = dd(pi_2) circ dd(i) (w,xi)$.

#diagram($ RR^(2n) edge(sim,->)  & tilde(Gamma)_t \ //<= TS RR^(2n) sim.eq RR^(2n)  times  RR^(2n)\
Sigma edge("u", e, -->) edge("ur", i, ->)
 $)

 On en déduit l'existence d'un difféo $e = (w,xi) : RR^(2n) -> Sigma$ tel que $( (z+Phi_1(z))/2, z- Phi_1(z)) = (w(z), pdv(S_1,w) (w(z), xi(z)))$ (à identification près). Ainsi on a $Id-dd(Phi_1)= d pdv(S_1,w) circ dd(e)=dc(S_1)circ dd(e)$. D'où par ce qui précède $ker Id- dd(Phi_t)( z) overset(sim.eq, dd(i)(z)) ker dc(S_1)(z,xi).$
]

#proposition[On a $inf_gf space z = ind_phi space z + (mu(j), gamma)$]<propeqindice2>

#proof[

  Tout d'abord, remarquons que l'application $tau : E to SS_1 times ( RR^(2n) times RR^(2n))$ définie par $tau (t,v,w) := (t, dd(J)(z).v, dd(J)(phi_t (z)).w)$ est une trivialisation de $E$. De plus, elle vérifie $Gamma'=tau(Gamma)$. On pose alors $C := tau^mm (SS_1 times (RR^n times 0) times (RR^n times 0))$, sous-fibré Lagrangien de $E$.\
  D'après la @defMDfibré, $ ind_C (Gamma) &= ind(tau(Gamma)) - ind(tau(C))\ &= ind(Gamma')-ind(t!> (RR^n times 0) times (RR^n times 0))\
  &= ind(Gamma'). $
  //Puis, par les @propindgfId (puisque $dd(Psi_0)=Id$) et @propeqgfQinf, $ind_C (Gamma) = ind_gf (z)$. Or 
$ 
ind_C (Gamma) &= ind(tau(Gamma)) - ind(tau(V))+ ind (tau(V)) - ind(tau(C))\
              &= ind_V (Gamma)- ind_C (V)\
              &= ind_phi (z) - ind_C (V).$

Or par invariance de l'indice de #toprove[jsp trop quoi]

La métrique $norm(dot)$ équipe $hor(z)$ et $hor(phi_t (z))$ d'un isomorphisme pour tout $t in SS_1$.
$ind_C (V) &= ind (tau(V))\
           &= ind (t !> j^*(lk_(z) L) plus.o dd(J)(phi_t (z))^mm ())

$


#todo[something about superscript]
  #toprove[Proposition 2.x de Théret]
]

#proposition[On a :
$ c(H)= norm(p)h'(norm(p)) - h(norm(p)) + int_gamma j^* ll_(RR^(2n)). $


On obtient finalement:
#numbered_eq[$ (mu(j), gamma) in cases(
    [n - i (gamma) - nu(z), n - i(gamma) ] &"dans le cas convexe", 
    [n-i(gamma) - nu(z)-1, n - i(gamma) +1] & "dans le cas concave"
)  $]<eqencadrementmujgg>
]<propencadrement>
#proof[On a $c(H)=c(HH)=cal(A)_HH (z)= int_(t!>Phi_t (z)) ll_(RR^(2n))-HH dd(t)$. Mais $HH$ est constant le long de l'orbite de $Phi$ et égal à $HH(z)=h(norm(p))$ donc $c(H) = int_(t!> Phi_t (z)) ll_(RR^(2n)) -h(norm(p)) $.

    Puis $H$ étant radial, on a nécessairement $norm(Phi_t (z)) = norm(p)$ pour tout $t in [0,1]$. Notons $C$ le cylindre reliant $gamma$ (vu dans la section nulle de $TLL$) à l'image de $t!> phi_t (z)$. On obtient d'une part, par la formule de Stokes et la nullité de $ll_L$ sur la section nulle $ int_C omega_"can" = int_C dd(ll_L) = int_(t!>phi_t (z)) ll_L - int_gamma ll_L = int_(t!> phi_t (z)) ll_L. $
    Puis $J$ étant un symplectomorphisme, $int_C omega_"can" = int_(J_* C) J^* dd(ll_(RR^(2n))) = int_(t!>Phi_t (z)) ll_(RR^(2n) )-int_(gamma) j^*ll_(RR^(2n)). $

    #todraw[Cylindre]
    Or $int_(t!>Phi_t (z)) ll_L = int_0^1 norm(p) dot(q)_t =  norm(p) ell(gg) = norm(p) h'(norm(p))$.
    
    Enfin, $c(H) = norm(p) h'(norm(p))-h(norm(p)) + int_gg j^* ll_(RR^(2n)).$

//Puis on a par la formule de Stokes et car $ll_L$ est nul sur la section nulle $int_(t !> Phi_(t)(z)) ll_(RR^(2n))= int_(t!> phi_(t)(z)) J^* ll_(RR^(2n) ) = int_C dd(omega) + int_gamma J^* ll_(RR^(2n) )= int_(t!> phi_t (z)) ll_L - int_(gg) ll_L + int_gamma j^* ll_L = int_(t!> phi_t (z)) ll_L + int_gamma j^* ll_L$. Puis $int_(t!>phi_t (z)) ll_L = $
    //
    //

   L'équation @eqencadrementmujgg découle de l'égalité précédente et de la @propeqindice1, la @propeqindice2 et la @propMorseMaslov.
]
= Passage à la limite

Les fonctions $h$ et $H$ définies précédemment dépendent des paramètres $rho,c$ et $eps$. Dans cette, partie nous supposons les deux premiers fixés et faisons tendres $eps$ vers 0. Notons $h_eps$ (resp. $H_eps$) la fonction $h$ (resp. $h$) associées au paramètre $eps >0$.

#propdef[La quantité $ K(rho,c) = lim_(eps to 0) c(H_eps) $ est bien définie.]

#proof[Les fonctions $eps !> H_eps$ et $H !> c(H)$ sont décroissantes ( d'après la #tosource[La capacité est décroissante.] pour la seconde) donc $lim_(eps to 0) c(H_eps) = sup_(eps >0) c(H_eps) $ qui est majoré par $c_"gf"(V))$.]

#proposition[Il existe une géodésique fermée $gg$ sur $L$ vérifiant @eqencadrementmujgg tqe $K (rho,c)$ vérifie :

$ K(rho,c) = cases(
    rho c + int_gg j^* ll_(RR^(2n)) & "dans le cas convexe",
    rho ell(gg) + int_(gg) j^* ll_(RR^(2n)) & "dans le cas concave"
) $]<propKrhoc>

#proof[Fixons $(eps_m)_(m in NN)$ suite de réels décroissants vers $0$. Par la @propencadrement on obtient, pour tout $m in NN$, une géodésique fermée $gg_m$, et un réel $r_m in ]eps_m/2,eps_m[ union ]rho- eps_m, rho_eps_m/2[$ tq 

#numbered_eq[$ c(H_(eps_m))=r_m h'(r_m) - h(r_m) + int_(gg_m) j^* ll_(RR^(2n)). $]<eqrm>

Quitte à extraire, on peut supposer $forall m in NN, r_m in ]eps_m/2,eps_m[$ (cas convexe) ou $forall m in NN, r_m in ]rho- eps_m, rho_eps_m/2[$.

Dans les deux cas, on a $gg_m = h'(r_m) <= c$ #tolink[majoration de la longueur]. Ainsi par #tosource[compacité de l'ensemble des géodésiques de longueur bornée par $c$] on peut supposer que la suite $(gg_m)_(m in NN)$ converge vers une géodésique fermée $gg$ (qui vérifie donc @eqencadrementmujgg).
 
Dans le cas convexe, $r_m ->0$, $sup_(m in NN) h'(r_m) <=c <oo$ et $h_(eps_m) (eps_m) = h_(rho-eps) - c(rho _ 2 eps_m) to - c rho$ et dans le cas concave, on a $r_m to rho$, $h'(r_m) = ell(gg_m) to ell(gg)$.et $h_(eps_m)(r_m) to 0$. L'égalité demandée découle du passage à la limite dans @eqrm.
]

= Démo du théorème

== C'est la vraie preuve du théorème let's gooooooo !!!

#definition[On appelle *capacité des fonctions génératrices* #todo[trouver un nom convenable pour la gf capacity] et l'on note $c_"gf" (L)$ la borne inférieur des capacités gf #todo[idem] des voisinages ouvert de $j(L)$ dans $RR^(2n)$.]

#propdef[
  Le célèbre théorème de #tosource[Weinstein], nous permet d'étendre le plongement $j : L to.hook RR^(2n)$ en un plongement $J : U to RR^(2n)$ où $U$ défini sur un voisinage ouvert $U$ de $L$ dans $TLL$. Le couple $(U,J)$ est appelé *voisinage de Weinstein*.
]

#definition[Soit $mu$ un représentant de la classe de Maslov #todo[Why is Maslov Class] de $j$ et $(U,J)$ un voisinage de Weinstein. On appelle *$mu$-épaisseur de $U$* la quantité 
$ norm(U)_mu := sup {s >=0 ; - s mu(L) cc U} $
où $mu(L)={mu_x | x in L} cc TLL$.

  On note de plus $ w(L,j) := sup_(mu, U) norm(U)_mu. $
]

#remark[La quantité $norm(U)_mu$ dépend du choix du représentant $mu$ de la classe de Maslov.]

#theorem[Soit $L$ variété de dimension $n$ et $j to.hook RR^(2n)$ plongement Lagrangien, pour $n>=2$.
+ Si $L=TT^n$ la capacité #todo[trouver nom gfc] vérifie :
$ c_"gf" (TT^n,j) >=2 w(TT^n,j) > 0. $
+ Si $L$ admet une métrique de courbure sectionnelle strictement négative alors 
$ c_"gf" (L) >= (n-1) w(L,j)>0. $

+ Plus généralement, si $(L_1,j_1),...,(L_m,j_m)$ sont des plongements Lagrangiens $L =L_1 times ... times L_n$ et $j = (j_1,..., j_n)$ alors 
$ c_"gf" (L) >= (n-m) w (L,j)>0. $

]

Ce résultat permet immédiatement de prouver le résultat suivant : 
#theorem("Chameau Lagrangien")[Si $j : L to RR^(2n)_-$ est l'un des plongements ci-dessus, alors pour tout $eta in [0, c_"gf" (L)]$ il n'existe pas d'isotopie symplectique $(Phi_t)_(t in [0,1])$ à support compact dans $Sigma_eta := {z in RR^(2n) | y_n =0 " et " norm(z)>= eta}$ tqe $Phi_1(j(L)) cc RR^(2n)_+$.]

#proof[Une telle isotopie $Phi$ déplacerait nécessairement l'image $J(U)$ d'un voisinage de Weinstein $(J,U)$ de $j$. Laquelle est de capacité  $c(J(U)) >= c_"gf" (L)$ ce qui est impossible par le #tolink[Chameau symplectique].]

== Oui bonjour serait-il possible d'obtenir un titre pour cette partie


#todo[fixer $mu$]
On note $ss$ la classe de Liouville du plongement $j$. $ss(gg):=int_gg j^* ll_(RR^(2n))$ la classe de Liouville.

Soit $rho >0$ suffisamment petit pour que $B_(rho)cc U$. On pose :
$ norm(U)_(mu,rho) = sup {s>=0, -s mu(L) + B_(rho) cc U}$.

#todraw[moving crown].

Pour $s in [0, norm(U)_(mu,rho)]$ on considère le symplectomorphisme
$ T_s :& TLL & to &TLL \
       & (q,p) &!> &(q,p-s mu(q)) $
 qui permet de définit le plongement lagrangien 
 $ j_s := J circ (T_s)_(L) : L to.hook RR^(2n) $

 qui s'étend en $J_s : BB_rho to.hook RR^(2n)$.

 Par la @propKrhoc, on obtient une application $s in [0, norm(U)_(mu,rho)] !> K_s (rho,c) in RR$, continue par #tolink[La capacité est continue]. On dispose, de plus, de $gg_s$ géodésique fermée de longueur $ell(gg_s) <= c$ tqe

$ K_s(rho, c) = cases(
    rho ell( gg_s) + ss(gg_s) - s mu(gg_s) & "dans le cas convexe",
    rho c + ss(gg_s) - s mu(gg_s) & "dans le cas concave".
) $

En effet, par le même argument qu'utilisé dans la preuve de @propencadrement, sur le cylindre délimité par $gg_s$ et $T_s(gg_s)$ dans le fibré cotangent $int_gg_s j_s^* ll_(RR^(2n)) - int_gg_s j^* ll_(RR^(2n)) = int_(gg_s) T_s^* (J^* ll_(RR^(2n))) - int_(gg_s) J^* ll_(RR^(2n)) = int_(gg_s) T_s^* ll_L - int_(gg_s)  ll_L = - s mu(gg_s)$.

== Cas courbure strictement négative

Si $L$ admet une métrique de courbure strictement négative alors pour toute géodésique fermée $gg$, $i(gg)=nu(gg)=0$ #y. Ainsi pour notre point fixe $z$, $nu(z)=1$ et donc par @eqencadrementmujgg :
$ cases(
    mu(gg) in [n-1,n] & "dans le cas convexe",
    mu(gg) in [n,n+1] & "dans le cas concave".
)  $

Mais par compacité de l'ensemble des géodésiques de longueur majorée par $c$, les quantités $ell(gg_s)$ et $ss(gg_s)$ ne prenne qu'un nombre fini de valeurs #y. Ainsi, la fonction $s !> K_s (rho,c)$ est affine par morceaux de pentes $<=-(n-1)$. Par suite $0< K_s (rho,c)<=K_0(rho,c) - (n-1)s$ pour tout $s in [0, norm(U)_(mu,rho)[$. En particulier,  $ K_0(rho,c)>= (n-1) norm(U)_(mu,rho))$. Par suite, puisque $norm(U)_(mu,rho) to norm(U)_mu$ quand $rho$ tends vers $0$ :

$ K(j):=lim_(rho to 0) lim_(c to oo) K(rho,c) >= (n-1) norm(U)_mu. $

On peut alors prouver le théorème. Par la formule ci-dessus, on a pour tout $delta>0$, deux nombres réels $rho>0$ et $c>0$ tqs $J(B_rho) cc V$ et $K_0(rho,c)>(n-1) norm(U)_mu - delta$. On a donc, par définition de $K_0(rho,c)$, un hamiltonien $HH$ à support compact et inclus dans $V$ de capacité $c(HH)>=(n-1)norm(U)-2delta$. D'où finalement :
$ c_"gf" (V)>= (n-1)norm(U)_(mu). $

On obtient alors le résultat souhaité par passage à la borne supérieure :

$ c_"gf" (L,j) >= (n-1) w(L,j) >0. $
== Cas d'un produit de sous-variétés de courbure strictement négative

Plus généralement, si $(L_1,j_1),...,(L_m,j_m)$ sont des plongements Lagrangiens de variétés ademettant une métrique de courbure strictement négative et que $(L,j)$ est le plongement produit. Alors comme précédemment l'indice de Morse de tout géodésique $i(gg)$ est nul mais leur nullité vaut $nu(gg)=m-1>0$. #y
Ainsi 

$ cases(
    mu(gamma) in [n-m,n] &"dans le cas convexe",
    mu(gamma) in [n-m+1,n+1] &"dans le cas concave"
). $

On procède alors comme précédemment et puisque $m<n$ pour obtenir $c_"gf" (V) >= (n-m) norm(U)_mu$, et passage à la borne supérieures :

$ c_"gf" (L,j) >= (n-m) w(L,j) >0. $

== Cas du tore

Tout d'abord, muni de la métrique plate le tore vérifie  $i(gamma)=0$ et $nu(gamma)=0$ pour toutes les géodésiques closes #y. Ainsi on a : 
$ cases(
    mu(gamma) in [0,n] &"dans le cas convexe",
    mu(gamma) in [1,n+1] &"dans le cas concave"
)  $

La formule importante est $ K_s(rho,c) = cases(
  rho l(gg_s)+ss(gg_s)-s mu (gg_s) &"dans le cas convexe",
  rho c + ss(gg_s)-s mu (gg_s) & "dans le cas concave")
$
#remark[Puisque $TT^n$ est orientable, on a nécessairement $mu(gamma) in 2 ZZ$ donc ] #y

Fixons $rho$ et étudiions les variations de $K(rho,c)$ en fonction de $c$.

On pose :
- $C' = {c>0 | K(rho,c) " s'écrit " rho c + sigma(gamma) " uniquement."}$
- $C'' = {c>0 | K(rho,c) " s'écrit " rho ell(gamma)+ sigma(gamma) " uniquement."}$
- $C''$ leur complémentaire dans $RR_+^*$.

Remarquons que $C'$ est $C''$ sont des ouverts et que $C''$ est un ensemble de points isolé. En effet, si $c in C''$ alors on a 
$K(rho,c)=rho c + ss (gg_1) = rho ell (gg_2)+ss(gg_2)$. #y

On a $K(rho,c)= rho c+ "cst"$ sur $C'$ et $K(rho,c)= "cst"$ sur $C''$. Ainsi nécessairement $ll(C')<=c_"gf"(V)/rho$.


Un point $c_s in C_s '''$ s'écrit $c_0+s(mu(gg_1)-mu(gg_2))$ avec $c_0 in C'''$, par existence.
