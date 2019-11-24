(*<*) 
theory Sintaxis
  imports 
    Main 
    "HOL-Library.LaTeXsugar" 
    "HOL-Library.OptionalSugar"
    "HOL-Library.Countable"
begin
(*>*) 

section \<open>Sintaxis\<close>

notation insert ("_ \<triangleright> _" [56,55] 55)

text \<open>En este apartado vamos a desarrollar los elementos de la sintaxis junto con varios resultados 
sobre los mismos. La lógica proposicional cuenta, fundamentalmente con:
\begin{description}
    \item[Alfabeto:] Se trata de una lista infinita de variables proposicionales, consideradas como 
expresiones cuya estructura interna no vamos a analizar.
    \item[Conectivas:] Conectores que interactúan con los elementos del alfabeto. Pueden ser 
    monarias que afectan a un único elemento o binarias que afectan a dos. En el primer grupo se 
    encuentra le negación (\<open>\<not>\<close>) y en el segundo vamos a considerar la conjunción (\<open>\<and>\<close>), la 
    disyunción (\<open>\<or>\<close>) y la implicación (\<open>\<longrightarrow>\<close>).
\end{description}

De este modo, informalmente diremos que una fórmula es el resultado de relacionar los elementos del 
alfabeto mediante las conectivas definidas anteriormente. En primer lugar, podemos definir las 
fórmulas atómicas como el tipo de fórmulas más básico, formadas únicamente por una variable 
porposicional del alfabeto. Por abuso de notación llamaremos \<open>átomos\<close> a las variables 
proposicionales del alfabeto. Aunque son intuitivamente equivalentes a las fórmulas atómicas, 
debemos recalcar su diferencia, pues los átomos son los elementos del alfabeto y las fórmulas 
atómicas son construcciones básicas de ellos. Este apunte es fundamental para entender el tipo 
correspondiente de fórmulas en nuestro programa.\<close>

text\<open>En Isabelle, las fórmulas son entendidas como un árbol con distintos tipos de nodos, que
son las conectivas, y hojas, que serán las fórmulas atómicas. De este modo, se define el tipo de 
las fórmulas como sigue.\<close>

datatype (atoms: 'a) formula = 
    Atom 'a
  | Bot                              ("\<bottom>")  
  | Not "'a formula"                 ("\<^bold>\<not>")
  | And "'a formula" "'a formula"    (infix "\<^bold>\<and>" 68)
  | Or "'a formula" "'a formula"     (infix "\<^bold>\<or>" 68)
  | Imp "'a formula" "'a formula"    (infixr "\<^bold>\<rightarrow>" 68)

text\<open>Como podemos observar en la definición, @{term "formula"} es un tipo de datos recursivo que se 
entiende como un árbol que relaciona elementos de un tipo \<open>'a\<close> cualquiera del alfabeto 
proposicional. En ella aparecen los siguientes elementos:
\begin{description}
\item[Constructores]:  
  \begin{enumerate} 
  \item \<open>Atom :: 'a formula\<close>  
  \item \<open>Not :: 'a \<Rightarrow> 'a formula \<Rightarrow> 'a formula\<close>
  \item \<open>And :: 'a \<Rightarrow> 'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula\<close>
  \item \<open>Or :: 'a \<Rightarrow> 'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula\<close>
  \item \<open>Imp :: 'a \<Rightarrow> 'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula\<close>
  \item \<open>Bot :: 'a formula\<close>
  \end{enumerate}
\item[Función de conjunto]: \<open>atoms :: ′a formula \<Rightarrow> ′a set\<close>
\end{description}

Podemos observar que se define simultáneamente la función @{term "atoms"} de modo que al aplicarla 
sobre una fórmula nos devuelve el conjunto de los átomos que la componen.
En particular, \<open>Atom 'a\<close> es la construcción de las fórmulas atómicas. \<open>Bot\<close> es un constructor que 
para cada tipo \<open>'a\<close> cualquiera construye la fórmula falsa cuyo símbolo queda retratado en la 
definición. Observemos que para emplear \<open>Bot\<close> en solitario es necesario especificar el tipo \<open>'a\<close>. \<close>

value"(Bot::nat formula)"

text\<open>Veamos ejemplos de obtención del conjunto de las variables proposicionales de las fórmulas 
mediante la función @{term "atoms"}.\<close>

value "atoms (Atom p) = {p}"

value "atoms (Not (Atom p)) = {p}"

text\<open>En particular, al aplicar @{term "atoms"} sobre la construcción \<open>Bot\<close> nos devuelve el conjunto
vacío, pues como hemos señalado, no contiene ninguna variable del alfabeto.\<close>

lemma "atoms Bot = {}"
 (*<*)  by auto (*>*)

lemma "atoms (Or (Atom p) Bot) = {p}"
 (*<*)  by auto (*>*)

text\<open>El resto de elementos que aparecen son equivalentes a las conectivas binarias y la negación. 
Cabe señalar que el término \<open>infix\<close> que precede al símbolo de notación de los nodos nos señala que 
son infijos, y \<open>infixr\<close> se trata de un infijo asociado a la derecha.
A continuación vamos a incluir el ejemplo de fórmula: \<open>(p \<longrightarrow> q) \<or> r\<close> y su árbol de formación 
correspondiente.
\<close>

value "Or (Imp (Atom p) (Atom q)) (Atom r)"

text\<open>
(Aquí debería salir el árbol pero no sé hacerlo)
\<close>

text\<open>Por otro lado, veamos cómo actúa la función @{term "atoms"} sobre fórmulas construidas con 
conectivas binarias, señalando los casos en que interactúan variables distintas y repetidas. 
Como se observa, por definición de conjunto, no contiene elementos repetidos.\<close>

lemma "atoms (Or (Imp (Atom p) (Atom q)) (Atom r)) = {p,q,r}"
 (*<*)  by auto (*>*) 

lemma "atoms (Or (Imp (Atom r) (Atom p)) (Atom r)) = {p,r}"
 (*<*)  by auto (*>*) 

text\<open>En esta sección, para demostrar los distintos resultados utilizaremos la táctica 
@{term "induction"}, que hace uso del esquema de indución. Para el tipo de las fórmulas, el esquema 
inductivo se aplicará en cada uno de los casos de los constructores, desglosándose así seis casos 
correspondientes a las distintas conectivas, fórmula atómica y \<open>Bot\<close>. Además, todas las 
demostraciones sobre casos de conectivas binarias son equivalentes en esta sección, pues la 
construcción sintáctica de fórmulas es idéntica entre ellas. Estas se
diferencian esencialmente en la connotación semántica, que veremos más adelante. Por tanto, para
simplificar algunas demostraciones sintácticas más extensas, expondremos la prueba
estructurada únicamente para uno de los casos de conectivas binarias.
\<close>

text\<open>Llegamos así al primer resultado de este apartado:
 \begin{lema}
    Los átomos de cualquier fórmula conforman un conjunto finito.
  \end{lema}
\<close>

text\<open>En Isabelle, se traduce del siguiente modo.\<close>

lemma atoms_finite[simp,intro!]: "finite (atoms F)"
  oops

text\<open>El lema anterior contiene la notación \<open>simp,intro!\<close> a continuación del título para incluir 
este resultado en las tácticas automática (mediante \<open>intro!\<close>) y de simplificación (mediante \<open>simp\<close>). 
Esto ocurrirá en varios resultados de esta sección.\<close>

text\<open>Por otro lado, el enunciado contiene la defición @{term "finite S"}, perteneciente a la teoría 
\href{https://n9.cl/x86r}{FiniteSet.thy}. Se trata de una definición
inductiva que nos permite la demostración del lema por simplificacion pues dentro de ella,
las reglas que especifica se han añadido como tácticas de \<open>simp\<close> e \<open>intro!\<close>.
\\
\<open>inductive finite :: "'a set \<Rightarrow> bool"\<close>\\
\<open>where\<close>\\
\<open>emptyI [simp, intro!]: "finite {}"\<close>\\
\<open>| insertI [simp, intro!]: "finite A \<Longrightarrow> finite (insert a A)"\<close>\\
\<close>

text\<open>Veamos la prueba detallada del resultado que, aunque se resulve 
fácilmente por simplificación, nos muestra un ejemplo claro de la estructura inductiva
que nos acompañará en las siguientes demostraciones.\<close>

lemma atoms_finite_detallada: "finite (atoms F)"
proof (induction F)
case (Atom x)
then show ?case by simp
next
case Bot
  then show ?case by simp
next
  case (Not F)
  then show ?case by simp
next
  case (And F1 F2)
  then show ?case by simp
next
  case (Or F1 F2)
  then show ?case by simp
next
  case (Imp F1 F2)
  then show ?case by simp
qed
  
text\<open>Las demostraciones aplicativa y automática son las siguientes respectivamente.\<close>

lemma atoms_finite_aplicativa: "finite (atoms F)" 
  apply (induction F)
  apply simp_all
 done

lemma atoms_finite[simp,intro!]: "finite (atoms F)" 
  by (induction F; simp)

subsection\<open>Subfórmulas\<close>

text\<open>Otra construcción natural a partir de la definición de fórmulas son las subfórmulas.

  \begin{definicion}
La lista de las subfórmulas de una fórmula F (\<open>Subf(F)\<close>) se define recursivamente por:
    \begin{enumerate}
      \item \<open>[\<bottom>]\<close> si \<open>F\<close> es \<open>\<bottom>\<close>.
      \item \<open>[F]\<close> si \<open>F\<close> es atómica.
      \item \<open>F#Subf(G)\<close> si \<open>F\<close> es \<open>\<not>G\<close>.
      \item \<open>F#Subf(G)@Subf(H)\<close> si \<open>F\<close> es \<open>G*H\<close> donde \<open>*\<close> es cualquier conectiva binaria.
    \end{enumerate}
  \end{definicion}\<close>

text\<open>En la definición anterior, \<open>#\<close> es el operador que añade un elemento al comienzo de una lista
y \<open>@\<close> concatena varias listas.
Análogamente, vamos a definir la función primitiva recursiva @{term "subformulae"}, que nos dará
una lista de todas las subfórmulas de una fórmula original obtenidas recursivamente.\<close>
 
primrec subformulae :: "'a formula \<Rightarrow> 'a formula list" where
"subformulae \<bottom> = [\<bottom>]" |
"subformulae (Atom k) = [Atom k]" |
"subformulae (Not F) = Not F # subformulae F" |
"subformulae (And F G) = And F G # subformulae F @ subformulae G" |
"subformulae (Imp F G) = Imp F G # subformulae F @ subformulae G" |
"subformulae (Or F G) = Or F G # subformulae F @ subformulae G"
 
text\<open>Siguiendo con los ejemplos, observemos cómo actúa @{term subformulae} en las distintas 
fórmulas.\<close>

value "subformulae (Atom p) = [Atom p]"

value "subformulae (Not (Atom p)) = [Not (Atom p), Atom p]"

value "subformulae (Or (Imp (Atom p) (Atom q)) (Atom r)) = 
  [(Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r, Atom p \<^bold>\<rightarrow> Atom q, Atom p, Atom q, Atom r]"

value "subformulae (And (Atom p) Bot) = 
  [And (Atom p) Bot, Atom p, Bot]"

text\<open>En particular, al tratarse de una lista pueden aparecer elementos repetidos como se muestra a
continuación.\<close>

value "subformulae (Or (Atom p) (Atom p)) =  
  [Or (Atom p) (Atom p), Atom p, Atom p]"

value "subformulae (Or (Atom p) (Atom p)) =  
  [Or (Atom p) (Atom p), Atom p] = False"

text\<open>A partir de esta definición, aparecen varios resultados sencillos que demostraremos siguiendo 
tácticas similares a las empleadas en el lema anterior. Para ello, trabajaremos
con conjuntos en vez de listas, pues poseen ventajas como la eliminación de elementos repetidos
o las operaciones propias.
De este modo, definimos @{term setSubformulae}, que convierte en un tipo conjunto la lista de 
subfórmulas anterior.\<close>

abbreviation setSubformulae :: "'a formula \<Rightarrow> 'a formula set" where
"setSubformulae F \<equiv> set (subformulae F)"

text\<open>Debemos señalar que la elección de @{term "abbreviation"} para definirlo no es arbitraria,
pues en caso contrario no permite la inclusión en las tácticas de simplificación de los lemas en los
que actúa. Este hecho queda explicado en ... .\<close>

text\<open>Por otra parte, observemos la diferencia de repetición con el ejemplo anterior.\<close>

value "setSubformulae (Or (Atom p) (Atom p)) =  {Or (Atom p) (Atom p), Atom p}"

lemma "setSubformulae (Or (Imp (Atom p) (Atom q)) (Atom r)) = 
  {(Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r, Atom p \<^bold>\<rightarrow> Atom q, Atom p, Atom q, Atom r}"
 (*<*)  by auto (*>*)

text\<open>Como hemos señalado, utilizaremos varios resultados de la teoría de conjuntos definida en 
Isabelle como \href{https://n9.cl/qatp}{Set.thy}.
Voy a especificar el esquema de las usadas en esta sección que no están incluidas en las tácticas de
simplificación para aclarar las demostraciones detalladas que presentaré en este apartado.\\
 \begin{itemize}
  \item[] @{thm[mode=Rule] subset_trans[no_vars]} \hfill (@{text subset_trans})
  \end{itemize}

 \begin{itemize}
  \item[] @{thm[mode=Rule] rev_subsetD[no_vars]} \hfill (@{text rev_subsetD})
  \end{itemize}

 \begin{itemize}
  \item[] @{thm[mode=Rule] Un_mono[no_vars]} \hfill (@{text Un_mono})
  \end{itemize}

 \begin{itemize}
  \item[] @{thm[mode=Rule] Un_upper1[no_vars]} \hfill (@{text Un_upper1})
  \end{itemize}

 \begin{itemize}
  \item[] @{thm[mode=Rule] Un_upper2[no_vars]} \hfill (@{text Un_upper2})
  \end{itemize}

Además, definiré alguna propiedad más que no aparece en la teoría de Isabelle y que utilizaremos
con frecuencia. Su demostración será la automática.\<close>

 (*<*)find_theorems "_\<subseteq>_" -name:List name:Set(*>*)

lemma subContUnionRev1: "A \<union> B \<subseteq> C \<Longrightarrow> A \<subseteq> C"
 (*<*)  by auto (*>*)

lemma subContUnionRev2: "A \<union> B \<subseteq> C \<Longrightarrow> B \<subseteq> C"
 (*<*)  by auto (*>*)

text\<open>Una vez aclarada la nueva función de conjuntos, vamos a demostrar el siguiente lema 
sirviéndonos de ella.

 \begin{lema}
    El conjunto de los átomos de una fórmula está contenido en el conjunto de subfórmulas de la 
    misma, es decir, las fórmulas atómicas son subfórmulas.
  \end{lema}

En Isabelle, se especifica como sigue.
\<close>

lemma atoms_are_subformulae: "Atom ` atoms F \<subseteq> setSubformulae F"
  oops

text\<open>Este resultado es especialmente interesante para aclarar la naturaleza de la función 
@{term "atoms"} aplicada a una fórmula. De este modo, \<open>Atom ` atoms F\<close> se encarga de 
construir las fórmulas atómicas a partir de cada uno de los elementos del conjunto de átomos de la 
fórmula \<open>F\<close>, creando un conjunto de fórmulas atómicas. Para ello emplea el infijo \<open>`\<close> definido como 
notación abreviada de @{term "image"} que calcula la imagen de un conjunto en la teoría 
\href{https://n9.cl/qatp}{Set.thy}.

 \begin{itemize}
  \item[] @{thm[mode=Def] image_def[no_vars]} \hfill (@{text image_def})
  \end{itemize}

Para aclarar su funcionamiento, veamos ejemplos para distintos casos de fórmulas.\<close>

value "Atom `atoms (Or (Atom p) Bot) = {Atom p}"

lemma "Atom `atoms (Or (Imp (Atom p) (Atom q)) (Atom r)) = {Atom p, Atom q, Atom r}"
 (*<*)  by auto (*>*)

lemma "Atom `atoms (Or (Imp (Atom p) (Atom p)) (Atom r)) = {Atom p, Atom r}"
 (*<*)  by auto (*>*)

text\<open>Además, esta función tiene la siguiente propiedad sobre la unión de conjuntos que utilizaré
en la demostración.\\
 \begin{itemize}
  \item[] @{thm[mode=Rule] image_Un[no_vars]} \hfill (@{text image_Un})
  \end{itemize}
\<close>
text\<open>Una vez hecha la aclaración anterior, comencemos la demostración estructurada. 
Esta seguirá el esquema inductivo señalado con anterioridad. Debido a la extensión de la prueba
demostraré de manera detallada únicamente uno de los casos de conectivas binarias. El resto son
totalmente equivalentes y los dejaré indicados de manera automática. Además, en esta primera 
prueba voy a demostrar dcon detalle los casos básicos de @{term "Atom x"} y @{term "Bot"}, 
señalando las reglas y definiciones usadas. Sin embargo, podrían demostrarse de manera directa
únicamente con simplificación.\<close>

lemma atoms_are_subformulae_detallada: "Atom ` atoms F \<subseteq> setSubformulae F"
proof (induction F)
  case (Atom x)
  have "Atom ` atoms (Atom x) = Atom ` {x}" by simp
  also have "\<dots> = {Atom x}" by simp
  also have "\<dots> \<subseteq> {Atom x}" by simp
  also have "\<dots> = setSubformulae (Atom x)" by simp
  finally show ?case by simp  
next
  case Bot
  have "Atom ` atoms (Bot) = Atom ` {}" by simp
  also have "\<dots> = {}" by simp
  also have "\<dots> \<subseteq> {}" by simp
  finally show ?case by simp 
next
  case (Not F)
  assume H:"Atom ` atoms F \<subseteq> setSubformulae F"
  show "Atom ` atoms (Not F) \<subseteq> setSubformulae (Not F)"
  proof -
    have "{Not F} \<union> setSubformulae F= setSubformulae (Not F)" by simp
    have "setSubformulae F \<subseteq> {Not F} \<union> setSubformulae F" by (rule Un_upper2)
    then have 1:"setSubformulae F \<subseteq> setSubformulae (Not F)" by simp
    have "Atom ` atoms F = Atom ` atoms (Not F)" by simp 
    then have "Atom ` atoms (Not F) \<subseteq> setSubformulae F" using H by simp 
    then show ?case using 1 by (rule subset_trans)
  qed
next
  case (And F1 F2)
  assume H1:"Atom ` atoms F1 \<subseteq> setSubformulae F1"
  assume H2:"Atom ` atoms F2 \<subseteq> setSubformulae F2"
  show "Atom ` atoms (And F1 F2) \<subseteq> setSubformulae (And F1 F2)"
  proof -
    have 2:"(Atom ` atoms F1) \<union> (Atom ` atoms F2) \<subseteq> setSubformulae F1 \<union> setSubformulae F2" 
      using H1 H2 by (rule Un_mono)
    have "setSubformulae (And F1 F2) = {And F1 F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)" 
      by simp
    have "setSubformulae F1 \<union> setSubformulae F2 \<subseteq> 
      {And F1 F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)" by (rule Un_upper2)
    then have 3:"setSubformulae F1 \<union> setSubformulae F2 \<subseteq> setSubformulae (And F1 F2)"
      by simp 
    then have "setSubformulae F1 \<subseteq> setSubformulae (And F1 F2)" by simp
    have "setSubformulae F2 \<subseteq> setSubformulae (And F1 F2)" using 3 by simp
    also have "atoms (And F1 F2) = atoms F1 \<union> atoms F2" by simp
    then have "Atom ` atoms (And F1 F2) = Atom ` (atoms F1 \<union> atoms F2)" by simp
    also have "... = Atom ` atoms F1 \<union> Atom ` atoms F2" by (rule image_Un)
    then have "Atom ` atoms (And F1 F2) = Atom ` atoms F1 \<union> Atom ` atoms F2" by simp
    then have "Atom ` atoms (And F1 F2) \<subseteq> setSubformulae F1 \<union> setSubformulae F2" using 2 by simp
    then show "Atom ` atoms (And F1 F2) \<subseteq> setSubformulae (And F1 F2)" using 3
      by (rule subset_trans)
  qed
next
  case (Or F1 F2)
  then show ?case by auto 
next
  case (Imp F1 F2)
  then show ?case by auto
qed

text\<open>Mostremos también la demostración automática con la definición original.\<close>

lemma atoms_are_subformulae: "Atom ` atoms F \<subseteq> setSubformulae F"
  by (induction F) auto

text\<open>Otro resultado de esta sección es la propia pertenencia de una fórmula en el conjunto 
de sus subfórmulas. 

\begin{lema}
    La propia fórmula pertence al conjunto de sus subfórmulas, es decir: \<open>F \<in> SubfSet(F)\<close>.
  \end{lema}
Para que la propiedad esté bien definida para conjuntos, considero \<open>SubfSet(·)\<close> equivalente
a @{term setSubformulae}, tal que al aplicarlo a la lista \<open>Subf(F)\<close> nos devuelva el conjunto
de sus subfórmulas.

A continuación incluimos el enunciado del lema con su demostración automática. Las demostraciones 
detallada y aplicativa son análogas a las del primer lema de la sección, utilizando únicamente 
inducción y simplificación. Para facilitar pruebas posteriores, vamos a añadir la regla a las 
tácticas de simplificación.\<close>

lemma subformulae_self[simp,intro]: "F \<in> setSubformulae F"
  by (induction F) simp_all 

text\<open>La siguiente propiedad declara que el conjunto de átomos de una subfórmula está contenido en el
conjunto de átomos de la propia fórmula.
\begin{lema}
    Sea \<open>G \<in> set(Subf(F))\<close>, entonces el conjunto de los átomos de \<open>G\<close> está contenido en los de \<open>F\<close>.
  \end{lema}

Traducido a Isabelle:\<close>

lemma subformula_atoms: "G \<in> setSubformulae F \<Longrightarrow> atoms G \<subseteq> atoms F"
  oops

text\<open>Veamos su demostración estructurada. Desarrollaré uno de los casos de conectivas binarias,
pues los demás son equivalentes.\<close>

lemma subformula_atoms_estructurada_s: "G \<in> setSubformulae F \<Longrightarrow> atoms G \<subseteq> atoms F"
proof (induction F)
  case (Atom x)
  then show ?case by simp 
next
  case Bot
  then show ?case by simp
next
  case (Not F)
  assume H1: "G \<in> setSubformulae (Not F)"
  assume H2: "G \<in> setSubformulae F \<Longrightarrow> atoms G \<subseteq> atoms F"
  show "atoms G \<subseteq> atoms (Not F)"
  proof (cases "G = Not F")
    case True 
    then have "G = Not F" by simp
    then show "atoms G \<subseteq> atoms (Not F)" by simp
  next
    case False
    then have 1:"G \<noteq> Not F" by simp
    have "setSubformulae (Not F) = {Not F} \<union> setSubformulae F" by simp
    then have 2:"G \<in> setSubformulae F" using 1 H1 by simp
    have "atoms F = atoms (Not F)" by simp
    then show "atoms G \<subseteq> atoms (Not F)" using 2 H2 by simp
  qed 
next
  case (And F1 F2)
  then show ?case by auto
next
  case (Or F1 F2)
  assume H3: "G \<in> setSubformulae (Or F1 F2)"
  assume H4: "G \<in> setSubformulae F1 \<Longrightarrow> atoms G \<subseteq> atoms F1"
  assume H5: "G \<in> setSubformulae F2 \<Longrightarrow> atoms G \<subseteq> atoms F2"
  then show "atoms G \<subseteq> atoms (Or F1 F2)"
  proof (cases "G = Or F1 F2")
    case True
    then have "G = Or F1 F2" by simp
    then show "atoms G \<subseteq> atoms (Or F1 F2)" by simp
  next
    case False
    then have 3:"G \<noteq> Or F1 F2" by simp
    have "setSubformulae (Or F1 F2) = {Or F1 F2} \<union> setSubformulae F1 \<union> setSubformulae F2" by simp
    then have 4:"G \<in> setSubformulae F1 \<union> setSubformulae F2" using 3 H3 by simp
    have "atoms (Or F1 F2) = atoms F1 \<union> atoms F2" by simp
    then show "atoms G \<subseteq> atoms (Or F1 F2)"
    proof (cases "G \<in> setSubformulae F1")
      case True
      then have "G \<in> setSubformulae F1" by simp
      then have 5:"atoms G \<subseteq> atoms F1" using H4 by simp
      have "atoms F1 \<subseteq> atoms F1 \<union> atoms F2" by (rule Un_upper1)
      then have 6:"atoms F1 \<subseteq> atoms (Or F1 F2)" by simp
      show "atoms G \<subseteq> atoms (Or F1 F2)" using 5 6 by (rule subset_trans)
    next
      case False
      then have "G \<notin> setSubformulae F1" by simp
      then have "G \<in> setSubformulae F2" using 4 by simp
      then have 7:"atoms G \<subseteq> atoms F2" using H5 by simp
      have 8:"atoms F2 \<subseteq> atoms (Or F1 F2)" by simp
      show "atoms G \<subseteq> atoms (Or F1 F2)" using 7 8 by (rule subset_trans)
    qed
  qed
next
  case (Imp F1 F2)
  then show ?case by auto
qed

text\<open>Por último, su demostración aplicativa y automática con la definición no simplificada.\<close>

lemma subformula_atoms_aplicativa: "G \<in> setSubformulae F \<Longrightarrow> atoms G \<subseteq> atoms F"
  apply (induction F)
  apply auto
 done

lemma subformula_atoms: "G \<in> setSubformulae F \<Longrightarrow> atoms G \<subseteq> atoms F"
  by (induction F) auto

text\<open>A continuación voy a introducir un lema que no pertenece a la teoría original de Isabelle pero
facilita las siguientes demostraciones detalladas mediante contenciones en cadena.

\begin{lema}
    Sea \<open>G \<in> SubfSet(F)\<close>, entonces \<open>SubfSet(G) \<subseteq> SubSet(F)\<close>.
  \end{lema} 

Veamos sus demostraciones según las distintas tácticas.\<close>

lemma subsubformulae_estructurada: 
    "G \<in> setSubformulae F \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F"
proof (induction F)
  case (Atom x)
  then show ?case by simp
next
  case Bot
  then show ?case by simp
next
  case (Not F)
  assume H1:"G \<in> setSubformulae F \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F"
  assume H2:"G \<in> setSubformulae (Not F)"
  then show "setSubformulae G \<subseteq> setSubformulae (Not F)"
  proof (cases "G = Not F")
    case True
    then show ?thesis by simp
  next
    case False
    then have "G \<noteq> Not F" by simp
    then have "G \<in> setSubformulae F" using H2 by simp
    then have 1:"setSubformulae G \<subseteq> setSubformulae F" using H1 by simp
    have "setSubformulae (Not F) = {Not F} \<union> setSubformulae F" by simp
    have "setSubformulae F \<subseteq> {Not F} \<union> setSubformulae F" by (rule Un_upper2)
    then have 2:"setSubformulae F \<subseteq> setSubformulae (Not F)" by simp
    show "setSubformulae G \<subseteq> setSubformulae (Not F)" using 1 2 by (rule subset_trans)
  qed
next
  case (And F1 F2)
  then show ?case by auto
next
  case (Or F1 F2)
  then show ?case by auto
next
  case (Imp F1 F2)
  assume H3:"G \<in> setSubformulae F1 \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F1"
  assume H4:"G \<in> setSubformulae F2 \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F2"
  assume H5:"G \<in> setSubformulae (Imp F1 F2)"
  have 4:"setSubformulae (Imp F1 F2) = {Imp F1 F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)" 
    by simp
  then show "setSubformulae G \<subseteq> setSubformulae (Imp F1 F2)"
  proof (cases "G = Imp F1 F2")
    case True
    then show ?thesis by simp
  next
    case False
    then have 5:"G \<noteq> Imp F1 F2" by simp
    have "setSubformulae F1 \<union> setSubformulae F2 \<subseteq> 
      {Imp F1 F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)" by (rule Un_upper2)
    then have 6:"setSubformulae F1 \<union> setSubformulae F2 \<subseteq> setSubformulae (Imp F1 F2)" by simp
    then show "setSubformulae G \<subseteq> setSubformulae (Imp F1 F2)"
    proof (cases "G \<in> setSubformulae F1")
      case True
      then have "G \<in> setSubformulae F1" by simp
      then have 7:"setSubformulae G \<subseteq> setSubformulae F1" using H3 by simp
      have 8:"setSubformulae F1 \<subseteq> setSubformulae (Imp F1 F2)" using 6 by (rule subContUnionRev1)  
      show "setSubformulae G \<subseteq> setSubformulae (Imp F1 F2)" using 7 8 by (rule subset_trans)
    next
      case False
      then have 9:"G \<notin> setSubformulae F1" by simp
      have "G \<in> setSubformulae F1 \<union> setSubformulae F2" using 5 H5 by simp
      then have "G \<in> setSubformulae F2" using 9 by simp
      then have 10:"setSubformulae G \<subseteq> setSubformulae F2" using H4 by simp
      have 11:"setSubformulae F2 \<subseteq> setSubformulae (Imp F1 F2)" using 6 by simp
      show "setSubformulae G \<subseteq> setSubformulae (Imp F1 F2)" using 10 11 by (rule subset_trans)
    qed
  qed
qed



lemma subformulae_setSubformulae:"G \<in> setSubformulae F \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F"
  by (induction F) auto
  
text\<open>El siguiente lema nos da la noción de transitividad de contención en cadena de las subfórmulas, 
de modo que la subfórmula de una subfórmula es del mismo modo subfórmula de la mayor. 
Es un resultado sencillo derivado de la estructura de árbol de formación que siguen las fórmulas 
según las hemos definido.

\begin{lema}
    Sea \<open>G \<in> SubfSet(F)\<close> y \<open>H \<in> SubfSet(G)\<close>, entonces \<open>H \<in> SubfSet(F)\<close>.
  \end{lema}

La demostración estructurada se hace de manera sencilla con el resultado introducido anteriormente. 
Veamos su prueba según las distintas tácticas.\<close>

lemma subsubformulae_estruct:
  assumes "G \<in> setSubformulae F" 
          "H \<in> setSubformulae G"
    shows "H \<in> setSubformulae F"
proof -
  have 1:"setSubformulae G \<subseteq> setSubformulae F" using assms(1) by (rule subformulae_setSubformulae)
  have "setSubformulae H \<subseteq> setSubformulae G" using assms(2) by (rule subformulae_setSubformulae)
  then have 2:"setSubformulae H \<subseteq> setSubformulae F" using 1 by (rule subset_trans)
  have "H \<in> setSubformulae H" by simp
  then show "H \<in> setSubformulae F" using 2 by (rule rev_subsetD)
qed

lemma subsubformulae_aplic: 
  "G \<in> setSubformulae F \<Longrightarrow> H \<in> setSubformulae G \<Longrightarrow> H \<in> setSubformulae F"
  oops
  
lemma subsubformulae: "G \<in> setSubformulae F \<Longrightarrow> H \<in> setSubformulae G \<Longrightarrow> H \<in> setSubformulae F"
  by (induction F; force)

text\<open>A continuación presentamos otro resultado que relaciona los conjuntos de subfórmulas 
según las conectivas que operen.\<close>

lemma subformulas_in_subformulas:
  "G \<^bold>\<and> H \<in> setSubformulae F \<Longrightarrow> G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
  "G \<^bold>\<or> H \<in> setSubformulae F \<Longrightarrow> G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
  "G \<^bold>\<rightarrow> H \<in> setSubformulae F \<Longrightarrow> G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
  "\<^bold>\<not> G \<in> setSubformulae F \<Longrightarrow> G \<in> setSubformulae F"
  oops

text\<open>Como podemos observar, el resultado es análogo en todas las conectivas binarias aunque
aparezcan definidas por separado, por tanto haré la demostración estructurada para
una de ellas pues el resto son equivalentes. 
Nos basaremos en el lema anterior @{term "subsubformulae"}.\<close>

lemma subformulas_in_subformulas_conjuncion_estructurada:
  assumes "And G H \<in> setSubformulae F" 
  shows "G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
proof (rule conjI)
  have 1:"setSubformulae (And G H) = {And G H} \<union> setSubformulae G \<union> setSubformulae H" by simp
  then have 2:"G \<in> setSubformulae (And G H)" by simp
  have 3:"H \<in> setSubformulae (And G H)" using 1 by simp
  show "G \<in> setSubformulae F" using assms 2 by (rule subsubformulae)
  show "H \<in> setSubformulae F" using assms 3 by (rule subsubformulae)
qed

lemma subformulas_in_subformulas_negacion_estructurada:
  assumes "Not G \<in> setSubformulae F"
  shows "G \<in> setSubformulae F"
proof -
  have "setSubformulae (Not G) = {Not G} \<union> setSubformulae G" by simp 
  then have 1:"G \<in> setSubformulae (Not G)" by simp
  show "G \<in> setSubformulae F" using assms 1 by (rule subsubformulae)
qed

text\<open>Mostremos ahora la demostración aplicativa y automática para el lema completo.\<close>

lemma subformulas_in_subformulas_aplicativa_s:
  "And G H \<in> setSubformulae F \<Longrightarrow> G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
  "Or G H \<in> setSubformulae F \<Longrightarrow> G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
  "Imp G H \<in> setSubformulae F \<Longrightarrow> G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
  "Not G \<in> setSubformulae F \<Longrightarrow> G \<in> setSubformulae F"
   apply ((rule conjI)+, (erule subsubformulae,simp)+)+
  done

lemma subformulas_in_subformulas:
  "G \<^bold>\<and> H \<in> setSubformulae F \<Longrightarrow> G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
  "G \<^bold>\<or> H \<in> setSubformulae F \<Longrightarrow> G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
  "G \<^bold>\<rightarrow> H \<in> setSubformulae F \<Longrightarrow> G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
  "\<^bold>\<not> G \<in> setSubformulae F \<Longrightarrow> G \<in> setSubformulae F"
  by (fastforce elim: subsubformulae)+

text\<open>HASTA AQUÍ HE TRABAJADO: 24/11/19\<close>

text\<open>Concluimos la sección de subfórmulas con un resultado que relaciona varias funciones
sobre la longitud de la lista \<open>subformulae F\<close> de una fórmula \<open>F\<close> cualquiera.\<close>

lemma length_subformulae: "length (subformulae F) = size F" 
  oops

text \<open>En prime lugar aparece la clase @{term "size"} de la teoría de números naturales ....
Vamos a definir @{term size1} de manera idéntica a como aparace @{term size} en la teoría.\<close>

class size1 =
  fixes size1 :: "'a \<Rightarrow> nat" 

instantiation nat :: size1
begin

definition size1_nat where [simp, code]: "size1 (n::nat) = n"

instance ..

end

text\<open>Como podemos observar, se trata de una clase que actúa sobre un parámetro global
de tipo \<open>'a\<close> cualquiera. Por otro lado, \<open>instantation\<close> define una clase de
parámetros, en este caso los números naturales \<open>nat\<close> que devuelve como resultado. Incluye
una definición concreta del operador \<open>size1\<close> sobre dichos parámetros. Además, el 
último \<open>instance\<close> abre una prueba que afirma que los parámetros dados conforman la clase 
especificada en la definición. Esta prueba que nos afirma que está bien definida la clase aparece
omitida utilizando \<open>..\<close> .
\\
En particular,
sobre una fórmula nos devuelve el número de elementos de la lista cuyos elementos son los nodos
y las hojas de su árbol de formación.\<close>

          
value "size(n::nat) = n"
value"size(5::nat) = 5"
(*value"(5::nat) = {1,2,3,4,5}" que es eso*)

text\<open>Por otro lado, la función @{term "length"} de la teoría \href{http://cort.as/-Stfm}{List.thy}
nos indica la longitud de una lista cualquiera de elementos, definiéndose utilizando el comando
@{term "size"} visto anteriormente.\<close>

abbreviation length :: "'a list \<Rightarrow> nat" where
"length \<equiv> size"

text\<open>Las demostración del resultado se vuelve a basar en la inducción que nos despliega seis casos. 
La prueba estructurada no resulta interesante, pues todos los casos son
inmediatos por simplificación como en el primer lema de esta sección. 
Incluimos a continuación la prueba aplicativa y 
automática.\<close>

lemma length_subformulae_aplicativa: "length (subformulae F) = size F" 
  apply (induction F) 
  apply simp_all
 done

lemma length_subformulae: "length (subformulae F) = size F" 
  by (induction F; simp)

subsection\<open>Conectivas derivadas\<close>

text\<open>En esta sección definiremos nuevas conectivas y elementos a partir de los ya definidos en el
apartado anterior. Además veremos varios resultados sobre los mismos.\<close>

text\<open>En primer lugar, vamos a definir \<open>Top:: 'a formula \<Rightarrow> bool\<close> como la constante  que devuelve
el booleano contrario a \<open>Bot\<close>. Se trata, por tanto, de una constante de la misma naturaleza que
la ya definida para \<open>Bot\<close>. De este modo, \<open>Top\<close> será equivalente a \<open>Verdadero\<close>, y \<open>Bot\<close> a \<open>Falso\<close>,
según se muestra en la siguiente ecuación. Su símbolo queda igualmente retratado a continuación.
\<close>

definition Top ("\<top>") where
"\<top> \<equiv> \<bottom> \<^bold>\<rightarrow> \<bottom>"
 (*meter doble implicacion en conectivas derivadas*)
text\<open>Por la propia definición y naturaleza de \<open>Top\<close>, verifica que no contiene ninguna variable del
alfabeto, como ya sabíamos análogamente para \<open>Bot\<close>. Tenemos así la siguiente propiedad.\<close>

lemma top_atoms_simp[simp]: "atoms \<top> = {}" 
  unfolding Top_def by simp

text\<open>A continuación vamos a definir dos conectivas que generalizarán la conjunción y la disyunción
para una lista finita de fórmulas. .\<close>

primrec BigAnd :: "'a formula list \<Rightarrow> 'a formula" ("\<^bold>\<And>_") where
  "\<^bold>\<And>Nil = (\<^bold>\<not>\<bottom>)" 
| "\<^bold>\<And>(F#Fs) = F \<^bold>\<and> \<^bold>\<And>Fs"

primrec BigOr :: "'a formula list \<Rightarrow> 'a formula" ("\<^bold>\<Or>_") where
  "\<^bold>\<Or>Nil = \<bottom>" 
| "\<^bold>\<Or>(F#Fs) = F \<^bold>\<or> \<^bold>\<Or>Fs"

text\<open>Ambas nuevas conectivas se caracterizarán por ser del tipo funciones primitivas recursivas. Por
tanto, sus definiciones se basan en dos casos:
  \begin{description}
  \item[Lista vacía:] Representada como \<open>Nil\<close>. En este caso, la conjunción plural aplicada a la lista
vacía nos devuelve la negación de \<open>Bot\<close>, es decir, \<open>Verdadero\<close>, y la disyunción plural sobre la lista
vacía nos da simplemente \<open>Bot\<close>, luego \<open>Falso\<close>. 
  \item[Lista recursiva:] En este caso actúa sobre \<open>F#Fs\<close> donde \<open>F\<close> es una fórmula concatenada a la
lista de fórmulas \<open>Fs\<close>. Como es lógico, @{term BigAnd} nos devuelve la conjunción de todas las fórmulas
de la lista y @{term BigOr} nos devuelve su disyunción.
  \end{description}
Además, se observa en cada función el símbolo de notación que aparece entre paréntesis.
La conjunción plural nos da el siguiente resultado.
\<close>

lemma atoms_BigAnd[simp]: "atoms (\<^bold>\<And>Fs) = \<Union>(atoms ` set Fs)"
  by(induction Fs; simp)


(*<*)
end
(*>*) 