(*<*) 
theory Sintaxis
  imports 
    Main 
    "HOL-Library.LaTeXsugar" 
    "HOL-Library.OptionalSugar"
    "HOL-Library.Countable"
begin
(*>*) 

(* chapter \<open>Sintaxis\<close> *)

section \<open>Fórmulas\<close>

text \<open>\comentario{Explicar la siguiente notación y recolocarla donde se
  use por primera vez.}\<close>

notation insert ("_ \<triangleright> _" [56,55] 55)

text \<open>En esta sección presentaremos una formalización en Isabelle de la 
  sintaxis de la lógica proposicional, junto con resultados y pruebas 
  sobre la misma. En líneas generales, primero daremos las nociones de 
  forma clásica y, a continuación, su correspondiente formalización.

  En primer lugar, supondremos que disponemos de los siguientes 
  elementos:
  \begin{description}
    \item[Alfabeto:] Es una lista infinita de variables proposicionales. 
      También pueden ser llamadas átomos o símbolos proposicionales.
    \item[Conectivas:] Conjunto finito cuyos elementos interactúan con 
      las variables. Pueden ser monarias que afectan a un único elemento 
      o binarias que afectan a dos. En el primer grupo se encuentra le 
      negación (\<open>\<not>\<close>) y en el segundo la conjunción (\<open>\<and>\<close>), la disyunción 
      (\<open>\<or>\<close>) y la implicación (\<open>\<longrightarrow>\<close>).
  \end{description}

  A continuación definiremos la estructura de fórmula sobre los 
  elementos anteriores. Para ello daremos una definición recursiva 
  basada en dos elementos: un conjunto de fórmulas básicas y una serie 
  de procedimientos de definición de fórmulas a partir de otras. El 
  conjunto de las fórmulas será el menor conjunto de estructuras 
  sinctáticas con dicho alfabeto y conectivas que contiene a las básicas 
  y es cerrado mediante los procedimientos de definición que mostraremos 
  a continuación.

  \begin{definicion}
    El conjunto de las fórmulas proposicionales está formado por las 
    siguientes:
    \begin{itemize}
      \item Las fórmulas atómicas, constituidas únicamente por una 
        variable del alfabeto. 
      \item La constante \<open>\<bottom>\<close>.
      \item Dada una fórmula \<open>F\<close>, la negación \<open>\<not> F\<close> es una fórmula.
      \item Dadas dos fórmulas \<open>F\<close> y \<open>G\<close>, la conjunción \<open>F \<and> G\<close> es una
        fórmula.
      \item Dadas dos fórmulas \<open>F\<close> y \<open>G\<close>, la disyunción \<open>F \<or> G\<close> es una
        fórmula.
      \item Dadas dos fórmulas \<open>F\<close> y \<open>G\<close>, la implicación \<open>F \<longrightarrow> G\<close> es 
        una fórmula.
    \end{itemize}
  \end{definicion}

  Intuitivamente, las fórmulas proposicionales son entendidas como un 
  tipo de árbol sintáctico cuyos nodos son las conectivas y sus hojas
  las fórmulas atómicas.

  \comentario{Incluir el árbol de formación.}

  A continuación, veamos su representación en Isabelle\<close>

datatype (atoms: 'a) formula = 
  Atom 'a
| Bot                              ("\<bottom>")  
| Not "'a formula"                 ("\<^bold>\<not>")
| And "'a formula" "'a formula"    (infix "\<^bold>\<and>" 68)
| Or "'a formula" "'a formula"     (infix "\<^bold>\<or>" 68)
| Imp "'a formula" "'a formula"    (infixr "\<^bold>\<rightarrow>" 68)

text \<open>Como podemos observar representamos las fórmulas proposicionales
  mediante un tipo de dato recursivo, @{term "formula"}, con los 
  siguientes constructores sobre un tipo cualquiera:

  \begin{description}
    \item[Fórmulas básicas]:
      \begin{itemize}
        \item @{const_typ Atom}
        \item @{const_typ Bot}
      \end{itemize}
    \item [Fórmulas compuestas]:
      \begin{itemize}
        \item @{const_typ Not}
        \item @{const_typ And}
        \item @{const_typ Or}
        \item @{const_typ Imp}
      \end{itemize}
  \end{description}

  Cabe señalar que los términos \<open>infix\<close> e \<open>infixr\<close> nos señalan que 
  los constructores que representan a las conectivas se pueden usar de
  forma infija. En particular, \<open>infixr\<close> se trata de un infijo asociado a 
  la derecha.

  Además se define simultáneamente la función @{const_typ atoms}, que 
  obtiene el conjunto de variables proposicionales de una fórmula. 

  Por otro lado, la definición de @{term "formula"} genera 
  automáticamente los siguientes lemas sobre la función de conjuntos 
  @{term "atoms"} en Isabelle.
  
text\<open> \comentario {Por otro lado, la definición de @{term "formula"} 
genera automáticamente los siguientes lemas sobre la función 
@{term "atoms"}, que obtiene el conjunto de átomos de una fórmula.}
\<close>

  \begin{itemize}
    \item[] @{thm formula.set}
  \end{itemize} 

  A continuación veremos varios ejemplos de fórmulas y el conjunto de 
  sus variables proposicionales obtenido mediante @{term "atoms"}. Se 
  observa que, por definición de conjunto, no contiene 
  elementos repetidos.\<close>

text\<open> \comentario { Se observa que, por ser conjuntos, no contienen 
  elementos repetidos.}
\<close>
notepad 
begin
  fix p q r :: 'a

  have "atoms (Atom p) = {p}"
    by (simp only: formula.set)

  have "atoms (\<^bold>\<not> (Atom p)) = {p}"
    by (simp only: formula.set)

  have "atoms ((Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r) = {p,q,r}"
    by auto

  have "atoms ((Atom p \<^bold>\<rightarrow> Atom p) \<^bold>\<or> Atom r) = {p,r}"
    by auto  
end

text \<open>En particular, el conjunto de símbolos proposicionales de la 
  fórmula \<open>Bot\<close> es vacío. Además, para calcular esta constante es 
  necesario especificar el tipo sobre el que se construye la fórmula.\<close>

notepad 
begin
  fix p :: 'a

  have "atoms \<bottom> = \<emptyset>"
    by (simp only: formula.set)

  have "atoms (Atom p \<^bold>\<or> \<bottom>) = {p}"
  proof -
    have "atoms (Atom p \<^bold>\<or> \<bottom>) = atoms (Atom p) \<union> atoms Bot"
      by (simp only: formula.set(5))
    also have "\<dots> = {p} \<union> atoms Bot"
      by (simp only: formula.set(1))
    also have "\<dots> = {p} \<union> \<emptyset>"
      by (simp only: formula.set(2))
    also have "\<dots> = {p}"
      by (simp only: Un_empty_right)
    finally show "atoms (Atom p \<^bold>\<or> \<bottom>) = {p}"
      by this
  qed

  have "atoms (Atom p \<^bold>\<or> \<bottom>) = {p}"
    by (simp only: formula.set Un_empty_right)
end

value "(Bot::nat formula)"

text \<open>Una vez definida la estructura de las fórmulas, vamos a introducir 
  el método de demostración que seguirán los resultados que aquí 
  presentaremos, tanto en la teoría clásica como en Isabelle. 

  Según la definición recursiva de las fórmulas, dispondremos de un 
  esquema de inducción sobre las mismas:

  \begin{definicion}
    Sea \<open>\<P>\<close> una propiedad sobre fórmulas que verifica las siguientes 
    condiciones:
    \begin{itemize}
      \item Las fórmulas atómicas la cumplen.
      \item La constante \<open>\<bottom>\<close> la cumple.
      \item Dada \<open>F\<close> fórmula que la cumple, entonces \<open>\<not> F\<close> la cumple.
      \item Dadas \<open>F\<close> y \<open>G\<close> fórmulas que la cumplen, entonces \<open>F * G\<close> la 
        cumple, donde \<open>*\<close> simboliza cualquier conectiva binaria.
    \end{itemize}
    Entonces, todas las fórmulas proposicionales tienen la propiedad 
    \<open>\<P>\<close>.
  \end{definicion}

  \comentario{Lo anterior no es una definición.}
  \comentario{Principio de inducción sobre fórmulas.}

  Análogamente, como las fórmulas proposicionales están definidas 
  mediante un tipo de datos recursivo, Isabelle genera de forma 
  automática el esquema de inducción correspondiente. De este modo, en 
  las pruebas formalizadas utilizaremos la táctica @{term "induction"}, 
  que corresponde al siguiente esquema.

  \comentario{Poner bien cada regla.}

  \begin{itemize}
    \item[] @{thm[mode=Rule] formula.induct}
  \end{itemize} 

  Como hemos señalado, el esquema inductivo se aplicará en cada uno de 
  los casos de los constructores, desglosándose así seis casos distintos 
  como se muestra anteriormente. Además, todas las demostraciones sobre 
  casos de conectivas binarias son equivalentes en esta sección, pues la 
  construcción sintáctica de fórmulas es idéntica entre ellas. Estas se 
  diferencian esencialmente en la connotación semántica que veremos más 
  adelante.

  Llegamos así al primer resultado de este apartado:
  \comentario {Suprimir la frase: Llegamos...}

  \begin{lema}
    El conjunto de los átomos de una fórmula proposicional es finito.
  \end{lema}

  Para proceder a la demostración, vamos a dar una definición inductiva 
  de conjunto finito. Cabe añadir que la demostración seguirá el esquema 
  inductivo relativo a la estructura de fórmula, y no el que induce esta
  última definición.

  \comentario{Para proceder a la demostración, consideremos la siguiente
   definición inductiva de conjunto finito.}

  \begin{definicion}
    Los conjuntos finitos son:
      \begin{itemize}
        \item El vacío.
        \item Dado un conjunto finito \<open>A\<close> y un elemento cualquiera \<open>a\<close>, 
          entonces \<open>{a} \<union> A\<close> es finito.
      \end{itemize}
  \end{definicion}

  \comentario{Comentar que esa es precísamente la definición en
 Isabelle de conjunto finito y mostrarla, pero no finite' pues no se
 usa en los lemas.}


  En Isabelle, podemos formalizar el lema como sigue.\<close>

lemma "finite (atoms F)"
  oops

text \<open>Análogamente, el enunciado formalizado contiene la definición 
  @{term "finite S"}, perteneciente a la teoría 
  \href{https://n9.cl/x86r}{FiniteSet.thy}.\<close>

inductive finite' :: "'a set \<Rightarrow> bool" where
  emptyI' [simp, intro!]: "finite' {}"
| insertI' [simp, intro!]: "finite' A \<Longrightarrow> finite' (insert a A)"

text \<open>Observemos que la definición anterior corresponde a 
  @{term finite'}. Sin embargo, es análoga a @{term finite} de la 
  teoría original. Este cambio de notación es necesario para no definir 
  dos veces de manera idéntica la misma noción en Isabelle. Por otra 
  parte, esta definición permitiría la demostración del lema por 
  simplificacion pues, dentro de ella las reglas que especifica se han 
  añadido como tácticas de \<open>simp\<close> e \<open>intro!\<close>. Sin embargo, conforme al 
  objetivo de este análisis, detallaremos dónde es usada cada una de las 
  reglas en la prueba detallada. 

 \comentario{No son necesarios los comentarios a finite'.}

  A continuación, veamos en primer lugar la demostración clásica del 
  lema. 

  \begin{demostracion}
  La prueba es por inducción sobre el tipo recursivo de las fórmulas. 
  Veamos cada caso.
  
  Consideremos una fórmula atómica \<open>p\<close> cualquiera. Entonces, 
  su conjunto de variables proposicionales es \<open>{p}\<close>, finito.

  Sea la fórmula \<open>\<bottom>\<close>. Entonces, su conjunto de átomos es vacío y, por 
  lo tanto, finito.
  
  Sea \<open>F\<close> una fórmula cuyo conjunto de variables proposicionales sea 
  finito. Entonces, por definición, \<open>\<not> F\<close> y \<open>F\<close> tienen igual conjunto de
  átomos y, por hipótesis de inducción, es finito.

  Consideremos las fórmulas \<open>F\<close> y \<open>G\<close> cuyos conjuntos de átomos son 
  finitos. Por construcción, el conjunto de variables de \<open>F*G\<close> es la 
  unión de sus respectivos conjuntos de átomos para cualquier \<open>*\<close> 
  conectiva binaria. Por lo tanto, usando la hipótesis de inducción, 
  dicho conjunto es finito. 
  \end{demostracion} 

  Veamos ahora la prueba detallada en Isabelle. Mostraremos con detalle 
  todos los casos de conectivas binarias, aunque se puede observar que 
  son completamente análogos. Para facilitar la lectura, primero 
  demostraremos por separado cada uno de los casos según el esquema 
  inductivo de fórmulas, y finalmente añadiremos la prueba para una 
  fórmula cualquiera a partir de los anteriores.\<close>

lemma atoms_finite_atom:
  "finite (atoms (Atom x))"
proof -
  have "finite \<emptyset>"
    by (simp only: finite.emptyI)
  then have "finite {x}"
    by (simp only: finite_insert)
  then show "finite (atoms (Atom x))"
    by (simp only: formula.set(1)) 
qed

lemma atoms_finite_bot:
  "finite (atoms \<bottom>)"
proof -
  have "finite \<emptyset>"
    by (simp only: finite.emptyI)
  then show "finite (atoms \<bottom>)"
    by (simp only: formula.set(2)) 
qed

lemma atoms_finite_not:
  assumes "finite (atoms F)" 
  shows   "finite (atoms (\<^bold>\<not> F))"
  using assms
  by (simp only: formula.set(3)) 

lemma atoms_finite_and:
  assumes "finite (atoms F1)"
          "finite (atoms F2)"
  shows   "finite (atoms (F1 \<^bold>\<and> F2))"
proof -
  have "finite (atoms F1 \<union> atoms F2)"
    using assms
    by (simp only: finite_UnI)
  then show "finite (atoms (F1 \<^bold>\<and> F2))"  
    by (simp only: formula.set(4))
qed

lemma atoms_finite_or:
  assumes "finite (atoms F1)"
          "finite (atoms F2)"
  shows   "finite (atoms (F1 \<^bold>\<or> F2))"
proof -
  have "finite (atoms F1 \<union> atoms F2)"
    using assms
    by (simp only: finite_UnI)
  then show "finite (atoms (F1 \<^bold>\<or> F2))"  
    by (simp only: formula.set(5))
qed

lemma atoms_finite_imp:
  assumes "finite (atoms F1)"
          "finite (atoms F2)"
  shows   "finite (atoms (F1 \<^bold>\<rightarrow> F2))"
proof -
  have "finite (atoms F1 \<union> atoms F2)"
    using assms
    by (simp only: finite_UnI)
  then show "finite (atoms (F1 \<^bold>\<rightarrow> F2))"  
    by (simp only: formula.set(6))
qed

lemma atoms_finite: "finite (atoms F)"
proof (induction F)
  case (Atom x)
  then show ?case by (simp only: atoms_finite_atom)
next
  case Bot
  then show ?case by (simp only: atoms_finite_bot)
next
  case (Not F)
  then show ?case by (simp only: atoms_finite_not)
next
  case (And F1 F2)
  then show ?case by (simp only: atoms_finite_and)
next
  case (Or F1 F2)
  then show ?case by (simp only: atoms_finite_or)
next
  case (Imp F1 F2)
  then show ?case by (simp only: atoms_finite_imp)
qed

text \<open>\comentario{Usar símbolos lógicos en la demostración anterior.}\<close>

text \<open>Su demostración automática es la siguiente.\<close>

lemma "finite (atoms F)" 
  by (induction F) simp_all 

section \<open>Subfórmulas\<close>

text \<open>Veamos la noción de subfórmulas.

  \begin{definicion}
  El conjunto de subfórmulas de una fórmula \<open>F\<close>, notada \<open>Subf(F)\<close>, se 
  define recursivamente como:
    \begin{itemize}
      \item \<open>{F}\<close> si \<open>F\<close> es una fórmula atómica.
      \item \<open>{\<bottom>}\<close> si \<open>F\<close> es \<open>\<bottom>\<close>.
      \item \<open>{F} \<union> Subf(G)\<close> si \<open>F\<close> es \<open>\<not>G\<close>.
      \item \<open>{F} \<union> Subf(G) \<union> Subf(H)\<close> si \<open>F\<close> es \<open>G*H\<close> donde \<open>*\<close> es 
        cualquier conectiva binaria.
    \end{itemize}
  \end{definicion}

  Para proceder a la formalización de Isabelle, seguiremos dos etapas. 
  En primer lugar, definimos la función primitiva recursiva 
  @{term "subformulae"}. Esta nos devolverá la lista de todas las 
  subfórmulas de una fórmula original obtenidas recursivamente.\<close>
 
primrec subformulae :: "'a formula \<Rightarrow> 'a formula list" where
  "subformulae (Atom k) = [Atom k]" 
| "subformulae \<bottom>        = [\<bottom>]" 
| "subformulae (\<^bold>\<not> F)    = (\<^bold>\<not> F) # subformulae F" 
| "subformulae (F \<^bold>\<and> G)  = (F \<^bold>\<and> G) # subformulae F @ subformulae G" 
| "subformulae (F \<^bold>\<or> G)  = (F \<^bold>\<or> G) # subformulae F @ subformulae G"
| "subformulae (F \<^bold>\<rightarrow> G) = (F \<^bold>\<rightarrow> G) # subformulae F @ subformulae G"
 
text \<open>Observemos que, en la definición anterior, \<open>#\<close> es el operador que 
  añade un elemento al comienzo de una lista y \<open>@\<close> concatena varias 
  listas. Siguiendo con los ejemplos, apliquemos @{term subformulae} en 
  las distintas fórmulas. En particular, al tratarse de una lista pueden 
  aparecer elementos repetidos como se muestra a continuación.

  \comentario{Corte de línea de la palabra siguiendo.}
\<close>

notepad
begin
  fix p :: 'a

  have "subformulae (Atom p) = [Atom p]"
    by simp

  have "subformulae (\<^bold>\<not> (Atom p)) = [\<^bold>\<not> (Atom p), Atom p]"
    by simp

  have "subformulae ((Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r) = 
       [(Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r, Atom p \<^bold>\<rightarrow> Atom q, Atom p, 
        Atom q, Atom r]"
    by simp

  have "subformulae (Atom p \<^bold>\<and> \<bottom>) = [Atom p \<^bold>\<and> \<bottom>, Atom p, \<bottom>]"
    by simp

  have "subformulae (Atom p \<^bold>\<or> Atom p) = 
       [Atom p \<^bold>\<or> Atom p, Atom p, Atom p]"
    by simp
end

text \<open>En la segunda etapa de formalización, definimos 
  @{term "setSubformulae"}, que convierte al tipo conjunto la lista de 
  subfórmulas anterior.\<close>

abbreviation setSubformulae :: "'a formula \<Rightarrow> 'a formula set" where
  "setSubformulae F \<equiv> set (subformulae F)"

text \<open>De este modo, la función \<open>setSubformulae\<close> es la formalización
  en Isabelle de \<open>Subf(·)\<close>. En Isabelle, primero hemos definido la lista 
  de subfórmulas pues, en algunos casos, es más sencilla la prueba de 
  resultados sobre este tipo. Sin embargo, el tipo de conjuntos facilita
  las pruebas de los resultados de esta sección. Algunas de las
  ventajas del tipo conjuntos son la eliminación de elementos repetidos 
  o las operaciones propias de teoría de conjuntos. Observemos los 
  siguientes ejemplos con el tipo de conjuntos.

  \comentario{Borrar "Sin embargo..." pues se contradice con la frase
 anterior.}

\<close>

notepad
begin
  fix p q r :: 'a

  have "setSubformulae (Atom p \<^bold>\<or> Atom p) = {Atom p \<^bold>\<or> Atom p, Atom p}"
    by simp
  
  have "setSubformulae ((Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r) =
        {(Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r, Atom p \<^bold>\<rightarrow> Atom q, Atom p, 
         Atom q, Atom r}"
  by auto   
end

text \<open>Por otro lado, debemos señalar que el uso de 
  @{term "abbreviation"} para definir @{term "setSubformulae"} no es 
  arbitrario. Esta elección se debe a que el tipo @{term "abbreviation"} 
  se trata de un sinónimo para una expresión cuyo tipo ya existe (en 
  nuestro caso, convertir en conjunto la lista obtenida con 
  @{term "subformulae"}). No es una definición propiamente dicha, sino 
  una forma de nombrar la composición de las funciones @{term "set"} y 
  @{term "subformulae"}.

  \comentario{Borrar la frase "Esta elección...".}

  En primer lugar, veamos que @{term "setSubformulae"} es una
  formalización de @{term "Subf"} en Isabelle. Para ello 
  utilizaremos el siguiente resultado sobre listas, probado como sigue.\<close>

lemma set_insert: "set (x # ys) = {x} \<union> set ys"
  by (simp only: list.set(2) Un_insert_left sup_bot.left_neutral)

text \<open>Por tanto, obtenemos la equivalencia como resultado de los 
  siguientes lemas, que aparecen demostrados de manera detallada.\<close>

lemma setSubformulae_atom:
  "setSubformulae (Atom p) = {Atom p}"
    by (simp only: subformulae.simps(1) list.set)

lemma setSubformulae_bot:
  "setSubformulae (\<bottom>) = {\<bottom>}"
    by (simp only: subformulae.simps(2) list.set)

lemma setSubformulae_not:
  shows "setSubformulae (\<^bold>\<not> F) = {\<^bold>\<not> F} \<union> setSubformulae F"
proof -
  have "setSubformulae (\<^bold>\<not> F) = set (\<^bold>\<not> F # subformulae F)"
    by (simp only: subformulae.simps(3))
  also have "\<dots> = {\<^bold>\<not> F} \<union> set (subformulae F)"
    by (simp only: set_insert)
  finally show ?thesis
    by this
qed

lemma setSubformulae_and: 
  "setSubformulae (F1 \<^bold>\<and> F2) 
   = {F1 \<^bold>\<and> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
proof -
  have "setSubformulae (F1 \<^bold>\<and> F2) 
        = set ((F1 \<^bold>\<and> F2) # (subformulae F1 @ subformulae F2))"
    by (simp only: subformulae.simps(4))
  also have "\<dots> = {F1 \<^bold>\<and> F2} \<union> (set (subformulae F1 @ subformulae F2))"
    by (simp only: set_insert)
  also have "\<dots> = {F1 \<^bold>\<and> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    by (simp only: set_append)
  finally show ?thesis
    by this
qed

lemma setSubformulae_or: 
  "setSubformulae (F1 \<^bold>\<or> F2) 
   = {F1 \<^bold>\<or> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
proof -
  have "setSubformulae (F1 \<^bold>\<or> F2) 
        = set ((F1 \<^bold>\<or> F2) # (subformulae F1 @ subformulae F2))"
    by (simp only: subformulae.simps(5))
  also have "\<dots> = {F1 \<^bold>\<or> F2} \<union> (set (subformulae F1 @ subformulae F2))"
    by (simp only: set_insert)
  also have "\<dots> = {F1 \<^bold>\<or> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    by (simp only: set_append)
  finally show ?thesis
    by this
qed

lemma setSubformulae_imp: 
  "setSubformulae (F1 \<^bold>\<rightarrow> F2) 
   = {F1 \<^bold>\<rightarrow> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
proof -
  have "setSubformulae (F1 \<^bold>\<rightarrow> F2) 
        = set ((F1 \<^bold>\<rightarrow> F2) # (subformulae F1 @ subformulae F2))"
    by (simp only: subformulae.simps(6))
  also have "\<dots> = {F1 \<^bold>\<rightarrow> F2} \<union> (set (subformulae F1 @ subformulae F2))"
    by (simp only: set_insert)
  also have "\<dots> = {F1 \<^bold>\<rightarrow> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    by (simp only: set_append)
  finally show ?thesis
    by this
qed

text \<open>Una vez probada la equivalencia, comencemos con los resultados 
  correspondientes a las subfórmulas. En primer lugar, tenemos la 
  siguiente propiedad como consecuencia directa de la equivalencia de 
  funciones anterior.

  \comentario{Reescribir el siguiente enunciado y su demostración.}

  \begin{lema}
    \<open>F \<in> Subf(F)\<close>.
  \end{lema}

  \begin{demostracion}
    Por inducción en la estructura de las fórmulas. Se tienen los
    siguientes casos:
  
    Sea \<open>p\<close> fórmula atómica cualquiera. Por definición de \<open>Subf\<close> tenemos 
    que \<open>Subf(p) = {p}\<close>, luego se tiene la propiedad.
  
    Sea la fórmula \<open>\<bottom>\<close>. Como \<open>Subf(\<bottom>) = {\<bottom>}\<close>, se verifica el resultado.

    Por definición del conjunto de subfórmulas de \<open>Subf(\<not> F)\<close> se tiene 
    la propiedad para este caso, pues 
    \<open>Subf(\<not> F) = {\<not> F} \<union> Subf(F) \<Longrightarrow> \<not> F \<in> Subf(\<not> F)\<close> como queríamos 
    ver.

    Análogamente, para cualquier conectiva binaria \<open>*\<close> y fórmulas \<open>F\<close> y 
    \<open>G\<close> se cumple \<open>Subf(F*G) = {F*G} \<union> Subf(F) \<union> Subf(G)\<close>, luego se 
    cumple la propiedad.
  \end{demostracion}
  
  \comentario{La redacción de la demostración debe ser como la
 demostración de que el conjunto de átomos de una fórmula es finito, en
 la que en cada caso se expresa claramente las hipótesis de inducción y
 dónde se usan.}


  Formalicemos ahora el lema con su correspondiente demostración 
  detallada.\<close>

lemma subformulae_self: "F \<in> setSubformulae F"
proof (induction F) 
  case (Atom x) 
  then show ?case 
    by (simp only: singletonI setSubformulae_atom)
next
  case Bot
  then show ?case 
    by (simp only: singletonI setSubformulae_bot)
next
  case (Not F)
  then show ?case 
    by (simp add: insertI1 setSubformulae_not) \<comment> \<open>Pendiente\<close>
next
case (And F1 F2)
  then show ?case 
    by (simp add: insertI1 setSubformulae_and) \<comment> \<open>Pendiente\<close>
next
case (Or F1 F2)
  then show ?case 
    by (simp add: insertI1 setSubformulae_or) \<comment> \<open>Pendiente\<close>
next
case (Imp F1 F2)
  then show ?case 
    by (simp add: insertI1 setSubformulae_imp) \<comment> \<open>Pendiente\<close>
qed

text \<open>\comentario{Completar la demostración anterior y usar los símbolos 
lógicos.}\<close>

text \<open>La demostración automática es la siguiente.\<close>

lemma "F \<in> setSubformulae F"
  by (induction F) simp_all

text \<open>Procedamos con los demás resultados de la sección. Como hemos 
  señalado con anterioridad, utilizaremos varias propiedades de 
  conjuntos pertenecientes a la teoría 
  \href{https://n9.cl/qatp}{Set.thy} de Isabelle, que apareceran en 
  el glosario final. 

  Además, definiremos dos reglas adicionales que utilizaremos con 
  frecuencia.\<close>

lemma subContUnionRev1: 
  assumes "A \<union> B \<subseteq> C" 
  shows   "A \<subseteq> C"
proof -
  have "A \<subseteq> C \<and> B \<subseteq> C"
    using assms
    by (simp only: sup.bounded_iff)
  then show "A \<subseteq> C"
    by (rule conjunct1)
qed

lemma subContUnionRev2: 
  assumes "A \<union> B \<subseteq> C" 
  shows   "B \<subseteq> C"
proof -
  have "A \<subseteq> C \<and> B \<subseteq> C"
    using assms
    by (simp only: sup.bounded_iff)
  then show "B \<subseteq> C"
    by (rule conjunct2)
qed

text \<open>Sus correspondientes demostraciones automáticas se muestran a 
  continuación.\<close>

lemma "A \<union> B \<subseteq> C \<Longrightarrow> A \<subseteq> C"
  by simp

lemma "A \<union> B \<subseteq> C \<Longrightarrow> B \<subseteq> C"
  by simp

text \<open>Veamos ahora los distintos resultados sobre subfórmulas.

  \comentario{Reescribir el siguiente enunciado y su demostración.}

  \begin{lema}
    Sean \<open>F\<close> una fórmula proposicional y \<open>A\<^sub>F\<close> el conjunto de las 
    fórmulas atómicas formadas a partir de cada elemento del conjunto 
    de variables proposicionales de \<open>F\<close>. 
    Entonces, \<open>A\<^sub>F \<subseteq> Subf(F)\<close>.

    Por tanto, las fórmulas atómicas son subfórmulas.
  \end{lema}

  \begin{demostracion}
    La prueba seguirá el esquema inductivo para la estructura de 
    fórmulas. Veamos cada caso:
  
    Consideremos la fórmula atómica \<open>p\<close> cualquiera. Entonces, su
    conjunto de átomos es \<open>{p}\<close>. De este modo, el conjunto \<open>A\<^sub>p\<close> 
    correspondiente será \<open>A\<^sub>p = {p} \<subseteq> {p} = Subf(Atom p)\<close> como 
    queríamos 
    demostrar.

    Sea la fórmula \<open>\<bottom>\<close>. Como su connjunto de átomos es vacío, es claro 
    que \<open>A\<^sub>\<bottom> = \<emptyset> \<subseteq> Subf(\<bottom>) = \<emptyset>\<close>.

    Sea la fórmula \<open>F\<close> tal que \<open>A\<^sub>F \<subseteq> Subf(F)\<close>. Probemos el resultado 
    para \<open>\<not> F\<close>. Por definición tenemos que los conjunto de variables 
    proposicionales de \<open>F\<close> y \<open>\<not> F\<close> coinciden, luego \<open>A\<^sub>\<not>\<^sub>F = A\<^sub>F\<close>. Además, 
    \<open>Subf(\<not> F) = {\<not> F} \<union> Subf(F)\<close>. Por tanto, por hipótesis de 
    inducción tenemos:
    \<open>A\<^sub>\<not>\<^sub>F = A\<^sub>F \<subseteq> Subf(F) \<subseteq> {\<not> F} \<union> Subf(F) = Subf(\<not> F)\<close>, luego
    \<open>A\<^sub>\<not>\<^sub>F \<subseteq> Subf(\<not> F)\<close>.

    Sean las fórmulas \<open>F\<close> y \<open>G\<close> tales que \<open>A\<^sub>F \<subseteq> Subf(F)\<close> y 
    \<open>A\<^sub>G \<subseteq> Subf(G)\<close>. Probemos ahora \<open>A\<^sub>F\<^sub>*\<^sub>G \<subseteq> Subf(F*G)\<close> para cualquier 
    conectiva binaria \<open>*\<close>. Por un lado, el conjunto de átomos de \<open>F*G\<close>
    es la unión de sus correspondientes conjuntos de átomos, luego 
    \<open>A\<^sub>F\<^sub>*\<^sub>G = A\<^sub>F \<union> A\<^sub>G\<close>. Por tanto, por hipótesis de inducción y definición 
    del conjunto de subfórmulas, se tiene:
    \<open>A\<^sub>F\<^sub>*\<^sub>G = A\<^sub>F \<union> A\<^sub>G \<subseteq> Subf(F) \<union> Subf(G) \<subseteq> 
    {F*G} \<union> Subf(F) \<union> Subf(G) = Subf(F*G)\<close>
    Luego, \<open>A\<^sub>F\<^sub>*\<^sub>G \<subseteq> Subf(F*G)\<close> como queríamos demostrar.  
  \end{demostracion}

  \comentario{En la redacción de la demostración: seguir el esquema de
 la demostración de que el conjunto de átomos es finito y, en cada caso,
 seguir el esquema de la prueba en Isabelle en la que se especifican
 claramente las hipótesis de inducción y cómo se usan.}

  En Isabelle, se especifica como sigue.\<close>

lemma "Atom ` atoms F \<subseteq> setSubformulae F"
  oops

text \<open>Debemos observar que \<open>Atom ` atoms F\<close> construye las fórmulas 
  atómicas a partir de cada uno de los elementos de \<open>atoms F\<close>, creando 
  un conjunto de fórmulas atómicas. Dicho conjunto es equivalente al 
  conjunto \<open>A\<^sub>F\<close> del enunciado del lema. Para ello emplea el infijo \<open>`\<close> 
  definido como notación abreviada de @{term "image"} que calcula la 
  imagen de un conjunto en la teoría \href{https://n9.cl/qatp}{Set.thy}.

  \begin{itemize}
    \item[] @{thm[mode=Def] image_def} 
      \hfill (@{text image_def})
  \end{itemize}

  Para aclarar su funcionamiento, veamos ejemplos para distintos casos 
  de fórmulas.\<close>

notepad
begin
  fix p q r :: 'a

  have "Atom `atoms (Atom p \<^bold>\<or> \<bottom>) = {Atom p}"
    by simp

  have "Atom `atoms ((Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r) = 
       {Atom p, Atom q, Atom r}"
    by auto 

  have "Atom `atoms ((Atom p \<^bold>\<rightarrow> Atom p) \<^bold>\<or> Atom r) = 
       {Atom p, Atom r}"
    by auto
end

text \<open>Además, esta función tiene las siguientes propiedades sobre 
  conjuntos que utilizaremos en la demostración.

  \begin{itemize}
    \item[] @{thm[mode=Rule] image_Un[no_vars]} 
      \hfill (@{text image_Un})
    \item[] @{thm[mode=Rule] image_insert[no_vars]} 
      \hfill (@{text image_insert})
    \item[] @{thm[mode=Rule] image_empty[no_vars]} 
      \hfill (@{text image_empty})
  \end{itemize}

  Una vez hechas las aclaraciones necesarias, comencemos la demostración 
  estructurada. Esta seguirá el esquema inductivo señalado con 
  anterioridad.\<close>

lemma atoms_are_subformulae_atom: 
  "Atom ` atoms (Atom x) \<subseteq> setSubformulae (Atom x)" 
proof -
  have "Atom ` atoms (Atom x) = Atom ` {x}"
    by (simp only: formula.set(1))
  also have "\<dots> = {Atom x}"
    by (simp only: image_insert image_empty)
  also have "\<dots> = set [Atom x]"
    by (simp only: list.set(1) list.set(2))
  also have "\<dots> = set (subformulae (Atom x))"
    by (simp only: subformulae.simps(1))
  finally have "Atom ` atoms (Atom x) = set (subformulae (Atom x))"
    by this
  then show ?thesis 
    by (simp only: subset_refl)
qed

lemma atoms_are_subformulae_bot: 
  "Atom ` atoms \<bottom> \<subseteq> setSubformulae \<bottom>"  
proof -
  have "Atom ` atoms \<bottom> = Atom ` \<emptyset>"
    by (simp only: formula.set(2))
  also have "\<dots> = \<emptyset>"
    by (simp only: image_empty)
  also have "\<dots> \<subseteq> setSubformulae \<bottom>"
    by (simp only: empty_subsetI)
  finally show ?thesis
    by this
qed

lemma atoms_are_subformulae_not: 
  assumes "Atom ` atoms F \<subseteq> setSubformulae F" 
  shows   "Atom ` atoms (\<^bold>\<not> F) \<subseteq> setSubformulae (\<^bold>\<not> F)"
proof -
  have "Atom ` atoms (\<^bold>\<not> F) = Atom ` atoms F"
    by (simp only: formula.set(3))
  also have "\<dots> \<subseteq> setSubformulae F"
    by (simp only: assms)
  also have "\<dots> \<subseteq> {\<^bold>\<not> F} \<union> setSubformulae F"
    by (simp only: Un_upper2)
  also have "\<dots> = setSubformulae (\<^bold>\<not> F)"
    by (simp only: setSubformulae_not)
  finally show ?thesis
    by this
qed

lemma atoms_are_subformulae_and: 
  assumes "Atom ` atoms F1 \<subseteq> setSubformulae F1"
          "Atom ` atoms F2 \<subseteq> setSubformulae F2"
  shows   "Atom ` atoms (F1 \<^bold>\<and> F2) \<subseteq> setSubformulae (F1 \<^bold>\<and> F2)"
proof -
  have "Atom ` atoms (F1 \<^bold>\<and> F2) = Atom ` (atoms F1 \<union> atoms F2)"
    by (simp only: formula.set(4))
  also have "\<dots> = Atom ` atoms F1 \<union> Atom ` atoms F2" 
    by (rule image_Un)
  also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
    using assms
    by (rule Un_mono)
  also have "\<dots> \<subseteq> {F1 \<^bold>\<and> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    by (simp only: Un_upper2)
  also have "\<dots> = setSubformulae (F1 \<^bold>\<and> F2)"
    by (simp only: setSubformulae_and)
  finally show ?thesis
    by this
qed

lemma atoms_are_subformulae_or: 
  assumes "Atom ` atoms F1 \<subseteq> setSubformulae F1"
          "Atom ` atoms F2 \<subseteq> setSubformulae F2"
  shows   "Atom ` atoms (F1 \<^bold>\<or> F2) \<subseteq> setSubformulae (F1 \<^bold>\<or> F2)"
proof -
  have "Atom ` atoms (F1 \<^bold>\<or> F2) = Atom ` (atoms F1 \<union> atoms F2)"
    by (simp only: formula.set(5))
  also have "\<dots> = Atom ` atoms F1 \<union> Atom ` atoms F2" 
    by (rule image_Un)
  also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
    using assms
    by (rule Un_mono)
  also have "\<dots> \<subseteq> {F1 \<^bold>\<or> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    by (simp only: Un_upper2)
  also have "\<dots> = setSubformulae (F1 \<^bold>\<or> F2)"
    by (simp only: setSubformulae_or)
  finally show ?thesis
    by this
qed

lemma atoms_are_subformulae_imp: 
  assumes "Atom ` atoms F1 \<subseteq> setSubformulae F1"
          "Atom ` atoms F2 \<subseteq> setSubformulae F2"
  shows   "Atom ` atoms (F1 \<^bold>\<rightarrow> F2) \<subseteq> setSubformulae (F1 \<^bold>\<rightarrow> F2)"
proof -
  have "Atom ` atoms (F1 \<^bold>\<rightarrow> F2) = Atom ` (atoms F1 \<union> atoms F2)"
    by (simp only: formula.set(6))
  also have "\<dots> = Atom ` atoms F1 \<union> Atom ` atoms F2" 
    by (rule image_Un)
  also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
    using assms
    by (rule Un_mono)
  also have "\<dots> \<subseteq> {F1 \<^bold>\<rightarrow> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    by (simp only: Un_upper2)
  also have "\<dots> = setSubformulae (F1 \<^bold>\<rightarrow> F2)"
    by (simp only: setSubformulae_imp)
  finally show ?thesis
    by this
qed

lemma atoms_are_subformulae: 
  "Atom ` atoms F \<subseteq> setSubformulae F"
proof (induction F)
  case (Atom x)
  then show ?case by (simp only: atoms_are_subformulae_atom) 
next
  case Bot
  then show ?case by (simp only: atoms_are_subformulae_bot) 
next
  case (Not F)
  then show ?case by (simp only: atoms_are_subformulae_not) 
next
  case (And F1 F2)
  then show ?case by (simp only: atoms_are_subformulae_and) 
next
  case (Or F1 F2)
  then show ?case by (simp only: atoms_are_subformulae_or)
next
  case (Imp F1 F2)
  then show ?case by (simp only: atoms_are_subformulae_imp)
qed

text \<open>\comentario{Usar símbolos lógicos en la demostración anterior.}\<close>

text \<open>La demostración automática queda igualmente expuesta a 
  continuación.\<close>

lemma "Atom ` atoms F \<subseteq> setSubformulae F"
  by (induction F)  auto

text \<open>La siguiente propiedad declara que el conjunto de átomos de una 
  subfórmula está contenido en el conjunto de átomos de la propia 
  fórmula.

  \begin{lema}
    Sea \<open>G \<in> Subf(F)\<close>, entonces el conjunto de átomos de \<open>G\<close> está
    contenido en el de \<open>F\<close>.
  \end{lema}

  \comentario{Reescribir el enunciado anterior.}

  \begin{demostracion}
  Procedemos mediante inducción en la estructura de las fórmulas según 
  los distintos casos:

  Sea \<open>p\<close> una fórmula atómica cualquiera. Si \<open>G \<in> Subf(p)\<close>, 
  como su conjunto de variables es \<open>{p}\<close>, se tiene \<open>G = p\<close>. 
  Por tanto, se tiene el resultado.

  Sea la fórmula \<open>\<bottom>\<close>. Si \<open>G \<in> Subf(\<bottom>)\<close>, como  su conjunto de átomos es
  \<open>{\<bottom>}\<close>, se tiene \<open>G = \<bottom>\<close>. Por tanto, se cumple la propiedad.

  Sea la fórmula \<open>F\<close> cualquiera tal que para cualquier subfórmula 
  \<open>G \<in> Subf(F)\<close> se verifica que el conjunto de átomos de \<open>G\<close> está 
  contenido en el de \<open>F\<close>. Supongamos \<open>G' \<in> Subf(\<not> F)\<close> cualquiera, 
  probemos que \<open>conjAtoms(G') \<subseteq> conjAtoms(\<not> F)\<close>.
  Por definición, tenemos que \<open>Subf(\<not> F) = {\<not> F} \<union> Subf(F)\<close>. De este 
  modo, tenemos dos opciones:
  \<open>G' \<in> {\<not> F}\<close> o \<open>G' \<in> Subf(F)\<close>. Del primer caso se deduce \<open>G' = \<not> F\<close> 
  y, por tanto, se verifica el resultado. Observando el segundo caso, 
  por hipótesis de inducción, se tiene que el conjunto de átomos de \<open>G'\<close>
  está contenido en el de \<open>F\<close>. Además, como el conjunto de átomos de 
  \<open>F\<close> y \<open>\<not> F\<close> coinciden, se verifica el resultado.

  Sea \<open>F1\<close> fórmula proposicional tal que para cualquier \<open>G \<in> Subf(F1)\<close> 
  se tiene que el conjunto de átomos de \<open>G\<close> está contenido en el de 
  \<open>F1\<close>. Sea también \<open>F2\<close> tal que dada \<open>G \<in> Subf(F2)\<close> cualquiera se 
  verifica también la hipótesis de inducción en su caso. Supongamos 
  \<open>G' \<in> Subf(F1*F2)\<close> donde \<open>*\<close> es cualquier conectiva binaria. Vamos a 
  probar que el conjunto de átomos de \<open>G\<close> está contenido en el de 
  \<open>F1*F2\<close>.

  En primer lugar, como 
  \<open>Subf(F1*F2) = {F1*F2} \<union> (Subf(F1) \<union> Subf(F2))\<close>, se desglosan tres
  casos posibles para \<open>G'\<close>:
  Si \<open>G' \<in> {F1*F2}\<close>, entonces \<open>G' = F1*F2\<close> y se tiene la propiedad.
  Si \<open>G' \<in> Subf(F1) \<union> Subf(F2)\<close>, entonces por propiedades de 
  conjuntos:
  \<open>G' \<in> Subf(F1)\<close> o \<open>G' \<in> Subf(F2)\<close>. Si \<open>G' \<in> Subf(F1)\<close>, por hipótesis 
  de inducción se tiene el resultado. Como el conjunto de átomos de
  \<open>F1*F2\<close> es la unión de los conjuntos de átomos de \<open>F1\<close> y \<open>F2\<close>, se 
  obtiene el resultado como consecuencia de la transitividad de 
  contención para conjuntos. El caso \<open>G' \<in> Subf(F2)\<close> se demuestra de la 
  misma forma.      
  \end{demostracion}

  \comentario{Reescribir la demostración anterior. Cuidado con los 
cortes de línea.}

  Formalizado en Isabelle:\<close>

lemma "G \<in> setSubformulae F \<Longrightarrow> atoms G \<subseteq> atoms F"
  oops

text \<open>Veamos su demostración estructurada.\<close>

lemma subformulas_atoms_atom:
  assumes "G \<in> setSubformulae (Atom x)" 
  shows   "atoms G \<subseteq> atoms (Atom x)"
proof -
  have "G \<in> {Atom x}"
    using assms
    by (simp only: setSubformulae_atom)
  then have "G = Atom x"
    by (simp only: singletonD)
  then show ?thesis
    by (simp only: subset_refl)
qed

lemma subformulas_atoms_bot:
  assumes "G \<in> setSubformulae \<bottom>" 
  shows   "atoms G \<subseteq> atoms \<bottom>"
proof -
  have "G \<in> {\<bottom>}"
    using assms
    by (simp only: setSubformulae_bot)
  then have "G = \<bottom>"
    by (simp only: singletonD)
  then show ?thesis
    by (simp only: subset_refl)
qed

lemma subformulas_atoms_not:
  assumes "G \<in> setSubformulae F \<Longrightarrow> atoms G \<subseteq> atoms F"
          "G \<in> setSubformulae (\<^bold>\<not> F)"
  shows   "atoms G \<subseteq> atoms (\<^bold>\<not> F)"
proof -
  have "G \<in> {\<^bold>\<not> F} \<union> setSubformulae F"
    using assms(2)
    by (simp only: setSubformulae_not) 
  then have "G \<in> {\<^bold>\<not> F} \<or> G \<in> setSubformulae F"
    by (simp only: Un_iff)
  then show "atoms G \<subseteq> atoms (\<^bold>\<not> F)"
  proof (rule disjE)
    assume "G \<in> {\<^bold>\<not> F}"
    then have "G = \<^bold>\<not> F"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F"
    then have "atoms G \<subseteq> atoms F"
      by (simp only: assms(1))
    also have "\<dots> = atoms (\<^bold>\<not> F)"
      by (simp only: formula.set(3))
    finally show ?thesis
      by this
  qed
qed

text \<open>\comentario{Añadir disjE al glosario.}\<close>

lemma subformulas_atoms_and:
  assumes "G \<in> setSubformulae F1 \<Longrightarrow> atoms G \<subseteq> atoms F1"
          "G \<in> setSubformulae F2 \<Longrightarrow> atoms G \<subseteq> atoms F2"
          "G \<in> setSubformulae (F1 \<^bold>\<and> F2)"
  shows   "atoms G \<subseteq> atoms (F1 \<^bold>\<and> F2)"
proof -
  have "G \<in> {F1 \<^bold>\<and> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    using assms(3) 
    by (simp only: setSubformulae_and)
  then have "G \<in> {F1 \<^bold>\<and> F2} \<or> G \<in> setSubformulae F1 \<union> setSubformulae F2"
    by (simp only: Un_iff)
  then show ?thesis
  proof (rule disjE)
    assume "G \<in> {F1 \<^bold>\<and> F2}"
    then have "G = F1 \<^bold>\<and> F2"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F1 \<union> setSubformulae F2"
    then have "G \<in> setSubformulae F1 \<or> G \<in> setSubformulae F2"  
      by (simp only: Un_iff)
    then show ?thesis
    proof (rule disjE)
      assume "G \<in> setSubformulae F1"
      then have "atoms G \<subseteq> atoms F1"
        by (rule assms(1))
      also have "\<dots> \<subseteq> atoms F1 \<union> atoms F2"
        by (simp only: Un_upper1)
      also have "\<dots> = atoms (F1 \<^bold>\<and> F2)"
        by (simp only: formula.set(4))
      finally show ?thesis
        by this
    next
      assume "G \<in> setSubformulae F2"
      then have "atoms G \<subseteq> atoms F2"
        by (rule assms(2))
      also have "\<dots> \<subseteq> atoms F1 \<union> atoms F2"
        by (simp only: Un_upper2)
      also have "\<dots> = atoms (F1 \<^bold>\<and> F2)"
        by (simp only: formula.set(4))
      finally show ?thesis
        by this
    qed
  qed
qed

lemma subformulas_atoms_or:
  assumes "G \<in> setSubformulae F1 \<Longrightarrow> atoms G \<subseteq> atoms F1"
          "G \<in> setSubformulae F2 \<Longrightarrow> atoms G \<subseteq> atoms F2"
          "G \<in> setSubformulae (F1 \<^bold>\<or> F2)"
  shows   "atoms G \<subseteq> atoms (F1 \<^bold>\<or> F2)"
proof -
  have "G \<in> {F1 \<^bold>\<or> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    using assms(3) 
    by (simp only: setSubformulae_or)
  then have "G \<in> {F1 \<^bold>\<or> F2} \<or> G \<in> setSubformulae F1 \<union> setSubformulae F2"
    by (simp only: Un_iff)
  then show ?thesis
  proof (rule disjE)
    assume "G \<in> {F1 \<^bold>\<or> F2}"
    then have "G = F1 \<^bold>\<or> F2"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F1 \<union> setSubformulae F2"
    then have "G \<in> setSubformulae F1 \<or> G \<in> setSubformulae F2"  
      by (simp only: Un_iff)
    then show ?thesis
    proof (rule disjE)
      assume "G \<in> setSubformulae F1"
      then have "atoms G \<subseteq> atoms F1"
        by (rule assms(1))
      also have "\<dots> \<subseteq> atoms F1 \<union> atoms F2"
        by (simp only: Un_upper1)
      also have "\<dots> = atoms (F1 \<^bold>\<or> F2)"
        by (simp only: formula.set(5))
      finally show ?thesis
        by this
    next
      assume "G \<in> setSubformulae F2"
      then have "atoms G \<subseteq> atoms F2"
        by (rule assms(2))
      also have "\<dots> \<subseteq> atoms F1 \<union> atoms F2"
        by (simp only: Un_upper2)
      also have "\<dots> = atoms (F1 \<^bold>\<or> F2)"
        by (simp only: formula.set(5))
      finally show ?thesis
        by this
    qed
  qed
qed

lemma subformulas_atoms_imp:
  assumes "G \<in> setSubformulae F1 \<Longrightarrow> atoms G \<subseteq> atoms F1"
          "G \<in> setSubformulae F2 \<Longrightarrow> atoms G \<subseteq> atoms F2"
          "G \<in> setSubformulae (F1 \<^bold>\<rightarrow> F2)"
  shows   "atoms G \<subseteq> atoms (F1 \<^bold>\<rightarrow> F2)"
proof -
  have "G \<in> {F1 \<^bold>\<rightarrow> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    using assms(3) 
    by (simp only: setSubformulae_imp)
  then have "G \<in> {F1 \<^bold>\<rightarrow> F2} \<or> G \<in> setSubformulae F1 \<union> setSubformulae F2"
    by (simp only: Un_iff)
  then show ?thesis
  proof (rule disjE)
    assume "G \<in> {F1 \<^bold>\<rightarrow> F2}"
    then have "G = F1 \<^bold>\<rightarrow> F2"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F1 \<union> setSubformulae F2"
    then have "G \<in> setSubformulae F1 \<or> G \<in> setSubformulae F2"  
      by (simp only: Un_iff)
    then show ?thesis
    proof (rule disjE)
      assume "G \<in> setSubformulae F1"
      then have "atoms G \<subseteq> atoms F1"
        by (rule assms(1))
      also have "\<dots> \<subseteq> atoms F1 \<union> atoms F2"
        by (simp only: Un_upper1)
      also have "\<dots> = atoms (F1 \<^bold>\<rightarrow> F2)"
        by (simp only: formula.set(6))
      finally show ?thesis
        by this
    next
      assume "G \<in> setSubformulae F2"
      then have "atoms G \<subseteq> atoms F2"
        by (rule assms(2))
      also have "\<dots> \<subseteq> atoms F1 \<union> atoms F2"
        by (simp only: Un_upper2)
      also have "\<dots> = atoms (F1 \<^bold>\<rightarrow> F2)"
        by (simp only: formula.set(6))
      finally show ?thesis
        by this
    qed
  qed
qed

lemma subformulae_atoms: 
  "G \<in> setSubformulae F \<Longrightarrow> atoms G \<subseteq> atoms F"
proof (induction F)
  case (Atom x)
  then show ?case by (simp only: subformulas_atoms_atom) 
next
  case Bot
  then show ?case by (simp only: subformulas_atoms_bot)
next
  case (Not F)
  then show ?case by (simp only: subformulas_atoms_not)
next
  case (And F1 F2)
  then show ?case by (simp only: subformulas_atoms_and)
next
  case (Or F1 F2)
  then show ?case by (simp only: subformulas_atoms_or)
next
  case (Imp F1 F2)
  then show ?case by (simp only: subformulas_atoms_imp)
qed

text \<open>\comentario{Usar símbolos lógicos en la demostración anterior.}\<close>

text \<open>Por último, su demostración aplicativa automática.\<close>

lemma "G \<in> setSubformulae F \<Longrightarrow> atoms G \<subseteq> atoms F"
  by (induction F) auto

text \<open>A continuación voy a introducir un lema que no pertenece a la 
  teoría original de Isabelle pero facilita las siguientes 
  demostraciones detalladas mediante contenciones en cadena.

 \comentario{cambiar voy por vamos.}

  \begin{lema}
    Sea \<open>G\<close> una subfórmula de \<open>F\<close>, entonces el conjunto de subfórmulas 
    de \<open>G\<close> está contenido en el de \<open>F\<close>.
  \end{lema} 

  \begin{demostracion}
  La prueba es por inducción en la estructura de fórmula.
  
  Sea \<open>p\<close> una fórmula atómica cualquiera. Entonces, bajo las
  condiciones del lema se tiene que \<open>G = p\<close>. Por lo tanto, tienen igual
  conjunto de subfórmulas.

  Sea la fórmula \<open>\<bottom>\<close>. Entonces, \<open>G = \<bottom>\<close> y tienen igual conjunto de
  subfórmulas.

  Sea una fórmula \<open>F\<close> tal que para toda subfórmula \<open>G\<close>, se tiene que el
  conjunto de subfórmulas de \<open>G\<close> está contenido en el de \<open>F\<close>. Veamos la
  propiedad para \<open>\<not> F\<close>. Sea \<open>G' \<in> Subf(\<not> F) = {\<not> F} \<union> Subf(F)\<close>. 
  Entonces \<open>G' \<in> {\<not> F}\<close> o \<open>G' \<in> Subf(F)\<close>. 
  Del primer caso se obtiene que \<open>G' = \<not> F\<close> y, por tanto, tienen igual 
  conjunto de subfórmulas. Del segundo caso se tiene \<open>G' \<in> Subf(F)\<close> y, 
  por hipótesis de inducción, el conjunto de subfórmulas de \<open>G'\<close> está 
  contenido en el de \<open>F\<close>. Como, a su vez, el conjunto de subfórmulas 
  de \<open>F\<close> está contenido en el de \<open>\<not> F\<close> por definición, se verifica la
  propiedad como consecuencia de la transitividad de la contención.

  Sean las fórmulas \<open>F1\<close> y \<open>F2\<close> tales que para cualquier subfórmula \<open>G1\<close>
  de \<open>F1\<close> el conjunto de subfórmulas de \<open>G1\<close> está contenido en el de 
  \<open>F1\<close>, y para cualquier subfórmula \<open>G2\<close> de \<open>F2\<close> el conjunto de 
  subfórmulas de \<open>G2\<close> está contenido en el de \<open>F2\<close>. Veamos que se 
  verifica la propiedad para \<open>F1*F2\<close> donde \<open>*\<close> es cualquier conectiva 
  binaria. 
  Sea \<open>G' \<in> Subf(F1*F2) = {F1*F2} \<union> Subf(F1) \<union> Subf(F2)\<close>. De este modo,
  tenemos tres casos: \<open>G' \<in> {F1*F2}\<close> o \<open>G' \<in> Subf(F1)\<close> o 
  \<open>G' \<in> Subf(F2)\<close>. De la primera opción se deduce \<open>G' = F1*F2\<close> y, por
  tanto, tienen igual conjunto de subfórmulas. Por otro lado, si 
  \<open>G' \<in> Subf(F1)\<close>, por hipótesis de inducción se tiene que el conjunto
  de subfórmulas de \<open>G'\<close> está contenido en el de \<open>F1\<close>. Por tanto, 
  como el conjunto de subfórmulas de \<open>F1\<close> está a su vez contenido en el 
  de \<open>F1*F2\<close>, se verifica la propiedad por la transitividad de la 
  contención en cadena. El caso \<open>G' \<in> Subf(F2)\<close> es análogo cambiando el 
  índice de la fórmula.   
  \end{demostracion}

  \comentario{Reescribir la demostración anterior.}\<close>

text \<open>Veamos su formalización en Isabelle junto con su demostración 
  estructurada.\<close>

lemma subContsubformulae_atom: 
  assumes "G \<in> setSubformulae (Atom x)" 
  shows "setSubformulae G \<subseteq> setSubformulae (Atom x)"
proof - 
  have "G \<in> {Atom x}" using assms 
    by (simp only: setSubformulae_atom)
  then have "G = Atom x"
    by (simp only: singletonD)
  then show ?thesis
    by (simp only: subset_refl)
qed

lemma subContsubformulae_bot:
  assumes "G \<in> setSubformulae \<bottom>" 
  shows   "setSubformulae G \<subseteq> setSubformulae \<bottom>"
proof -
  have "G \<in> {\<bottom>}"
    using assms
    by (simp only: setSubformulae_bot)
  then have "G = \<bottom>"
    by (simp only: singletonD)
  then show ?thesis
    by (simp only: subset_refl)
qed

lemma subContsubformulae_not:
  assumes "G \<in> setSubformulae F \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F"
          "G \<in> setSubformulae (\<^bold>\<not> F)"
  shows   "setSubformulae G \<subseteq> setSubformulae (\<^bold>\<not> F)"
proof -
  have "G \<in> {\<^bold>\<not> F} \<union> setSubformulae F"
    using assms(2)
    by (simp only: setSubformulae_not) 
  then have "G \<in> {\<^bold>\<not> F} \<or> G \<in> setSubformulae F"
    by (simp only: Un_iff)
  then show "setSubformulae G \<subseteq> setSubformulae (\<^bold>\<not> F)"
  proof
    assume "G \<in> {\<^bold>\<not> F}"
    then have "G = \<^bold>\<not> F"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F"
    then have "setSubformulae G \<subseteq> setSubformulae F"
      by (simp only: assms(1))
    also have "setSubformulae F \<subseteq> setSubformulae (\<^bold>\<not> F)"
      by (simp only: setSubformulae_not Un_upper2)
    finally show ?thesis 
      by this
  qed
qed

lemma subContsubformulae_and:
  assumes "G \<in> setSubformulae F1 
            \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F1"
          "G \<in> setSubformulae F2 
            \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F2"
          "G \<in> setSubformulae (F1 \<^bold>\<and> F2)"
  shows   "setSubformulae G \<subseteq> setSubformulae (F1 \<^bold>\<and> F2)"
proof -
  have "G \<in> {F1 \<^bold>\<and> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    using assms(3) 
    by (simp only: setSubformulae_and)
  then have "G \<in> {F1 \<^bold>\<and> F2} \<or> G \<in> setSubformulae F1 \<union> setSubformulae F2"
    by (simp only: Un_iff)
  then show ?thesis
  proof (rule disjE)
    assume "G \<in> {F1 \<^bold>\<and> F2}"
    then have "G = F1 \<^bold>\<and> F2"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F1 \<union> setSubformulae F2"
    then have "G \<in> setSubformulae F1 \<or> G \<in> setSubformulae F2"  
      by (simp only: Un_iff)
    then show ?thesis
    proof 
      assume "G \<in> setSubformulae F1"
      then have "setSubformulae G \<subseteq> setSubformulae F1"
        by (simp only: assms(1))
      also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
        by (simp only: Un_upper1)
      also have "\<dots> \<subseteq> setSubformulae (F1 \<^bold>\<and> F2)"
        by (simp only: setSubformulae_and Un_upper2)
      finally show ?thesis
        by this
    next
      assume "G \<in> setSubformulae F2"
      then have "setSubformulae G \<subseteq> setSubformulae F2"
        by (rule assms(2))
      also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
        by (simp only: Un_upper2)
      also have "\<dots> \<subseteq> setSubformulae (F1 \<^bold>\<and> F2)"
        by (simp only: setSubformulae_and Un_upper2)
      finally show ?thesis
        by this
    qed
  qed
qed

lemma subContsubformulae_or:
  assumes "G \<in> setSubformulae F1 
            \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F1"
          "G \<in> setSubformulae F2 
            \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F2"
          "G \<in> setSubformulae (F1 \<^bold>\<or> F2)"
  shows   "setSubformulae G \<subseteq> setSubformulae (F1 \<^bold>\<or> F2)"
proof -
  have "G \<in> {F1 \<^bold>\<or> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    using assms(3) 
    by (simp only: setSubformulae_or)
  then have "G \<in> {F1 \<^bold>\<or> F2} \<or> G \<in> setSubformulae F1 \<union> setSubformulae F2"
    by (simp only: Un_iff)
  then show ?thesis
  proof (rule disjE)
    assume "G \<in> {F1 \<^bold>\<or> F2}"
    then have "G = F1 \<^bold>\<or> F2"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F1 \<union> setSubformulae F2"
    then have "G \<in> setSubformulae F1 \<or> G \<in> setSubformulae F2"  
      by (simp only: Un_iff)
    then show ?thesis
    proof (rule disjE)
      assume "G \<in> setSubformulae F1"
      then have "setSubformulae G \<subseteq> setSubformulae F1"
        by (simp only: assms(1))
      also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
        by (simp only: Un_upper1)
      also have "\<dots> \<subseteq> setSubformulae (F1 \<^bold>\<or> F2)"
        by (simp only: setSubformulae_or Un_upper2)
      finally show ?thesis
        by this
    next
      assume "G \<in> setSubformulae F2"
      then have "setSubformulae G \<subseteq> setSubformulae F2"
        by (rule assms(2))
      also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
        by (simp only: Un_upper2)
      also have "\<dots> \<subseteq> setSubformulae (F1 \<^bold>\<or> F2)"
        by (simp only: setSubformulae_or Un_upper2)
      finally show ?thesis
        by this
    qed
  qed
qed

lemma subContsubformulae_imp:
  assumes "G \<in> setSubformulae F1 
            \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F1"
          "G \<in> setSubformulae F2 
            \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F2"
          "G \<in> setSubformulae (F1 \<^bold>\<rightarrow> F2)"
  shows   "setSubformulae G \<subseteq> setSubformulae (F1 \<^bold>\<rightarrow> F2)"
proof -
  have "G \<in> {F1 \<^bold>\<rightarrow> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    using assms(3) 
    by (simp only: setSubformulae_imp)
  then have "G \<in> {F1 \<^bold>\<rightarrow> F2} \<or> G \<in> setSubformulae F1 \<union> setSubformulae F2"
    by (simp only: Un_iff)
  then show ?thesis
  proof (rule disjE)
    assume "G \<in> {F1 \<^bold>\<rightarrow> F2}"
    then have "G = F1 \<^bold>\<rightarrow> F2"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F1 \<union> setSubformulae F2"
    then have "G \<in> setSubformulae F1 \<or> G \<in> setSubformulae F2"  
      by (simp only: Un_iff)
    then show ?thesis
    proof (rule disjE)
      assume "G \<in> setSubformulae F1"
      then have "setSubformulae G \<subseteq> setSubformulae F1"
        by (simp only: assms(1))
      also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
        by (simp only: Un_upper1)
      also have "\<dots> \<subseteq> setSubformulae (F1 \<^bold>\<rightarrow> F2)"
        by (simp only: setSubformulae_imp Un_upper2)
      finally show ?thesis
        by this
    next
      assume "G \<in> setSubformulae F2"
      then have "setSubformulae G \<subseteq> setSubformulae F2"
        by (rule assms(2))
      also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
        by (simp only: Un_upper2)
      also have "\<dots> \<subseteq> setSubformulae (F1 \<^bold>\<rightarrow> F2)"
        by (simp only: setSubformulae_imp Un_upper2)
      finally show ?thesis
        by this
    qed
  qed
qed

lemma
  "G \<in> setSubformulae F \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F"
proof (induction F)
  case (Atom x)
  then show ?case by (rule subContsubformulae_atom)
next
  case Bot
  then show ?case by (rule subContsubformulae_bot)
next
  case (Not F)
  then show ?case by (rule subContsubformulae_not)
next
  case (And F1 F2)
  then show ?case by (rule subContsubformulae_and)
next
  case (Or F1 F2)
  then show ?case by (rule subContsubformulae_or)
next
  case (Imp F1 F2)
  then show ?case by (rule subContsubformulae_imp)
qed

text \<open>\comentario{Usar símbolos lógicos en la demostración anterior.}\<close>

text \<open>Finalmente, su demostración automática se muestra a continuación.\<close>

lemma subContsubformulae:
  "G \<in> setSubformulae F \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F"
  by (induction F) auto
  
text \<open>El siguiente lema nos da la noción de transitividad de contención 
  en cadena de las subfórmulas, de modo que la subfórmula de una 
  subfórmula es del mismo modo subfórmula de la mayor.

  \begin{lema}
    Sean \<open>G\<close> una subfórmula de \<open>F\<close> y \<open>H\<close> una subfórmula de \<open>G\<close>, entonces 
    \<open>H\<close> es subfórmula de \<open>F\<close>.
  \end{lema}

  \comentario{La transitividad de lee mejor si se escribe en este
 orden: Sean \<open>H\<close> una subfórmula de \<open>G\<close> y \<open>G\<close> una subfórmula de \<open>F\<close>, 
 entonces \<open>H\<close> es subfórmula de \<open>F\<close>.}


  \begin{demostracion}
  La prueba está basada en el lema anterior. Hemos demostrado que como 
  \<open>G\<close> es subfórmula de \<open>F\<close>, entonces el conjunto de átomos de \<open>G\<close> está
  contenido en el de \<open>F\<close>. Del mismo modo, como \<open>H\<close> es subfórmula de
  \<open>G\<close>, su conjunto de átomos está contenido en el de \<open>G\<close>. Por la
  transitividad de la contención, tenemos que el conjunto de átomos de 
  \<open>H\<close> está contenido en el de \<open>F\<close>. Por otro lema anterior, tenemos que
  \<open>H\<close> pertenece a su propio conjunto de subfórmulas. Por tanto,
  \<open>H \<in> Subf(H) \<subseteq> Subf(F) \<Longrightarrow> H \<in> Subf(F)\<close>.
  \end{demostracion}

  \comentario{Reescribir la demostración anterior.}

  Veamos su formalización y prueba estructurada en Isabelle.

  Veamos su prueba según las distintas tácticas.\<close>

lemma
  assumes "G \<in> setSubformulae F" 
          "H \<in> setSubformulae G"
  shows   "H \<in> setSubformulae F"
proof -
  have 1: "setSubformulae G \<subseteq> setSubformulae F" 
    using assms(1) 
    by (rule subContsubformulae)
  have "setSubformulae H \<subseteq> setSubformulae G" 
    using assms(2) 
    by (rule subContsubformulae)
  then have 2: "setSubformulae H \<subseteq> setSubformulae F" 
    using 1 
    by (rule subset_trans)
  have "H \<in> setSubformulae H" 
    by (simp only: subformulae_self)
  then show "H \<in> setSubformulae F" 
    using 2 
    by (rule rev_subsetD)
qed

lemma subsubformulae: 
  "G \<in> setSubformulae F 
   \<Longrightarrow> H \<in> setSubformulae G 
   \<Longrightarrow> H \<in> setSubformulae F"
  apply (drule  subContsubformulae)
  apply (erule subsetD, assumption)
  done
(*  using subContsubformulae by blast *)

text \<open>\comentario{Ver la demostración sin blast.}\<close>

text \<open>\comentario{Explicar el cambio de enunciado}\<close>

text \<open>A continuación presentamos otro resultado que relaciona los 
  conjuntos de subfórmulas según las conectivas que operen.\<close>

lemma subformulas_in_subformulas:
  "G \<^bold>\<and> H \<in> setSubformulae F 
  \<Longrightarrow> G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
  "G \<^bold>\<or> H \<in> setSubformulae F 
  \<Longrightarrow> G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
  "G \<^bold>\<rightarrow> H \<in> setSubformulae F 
  \<Longrightarrow> G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
  "\<^bold>\<not> G \<in> setSubformulae F \<Longrightarrow> G \<in> setSubformulae F"
  oops

text \<open>Como podemos observar, el resultado es análogo en todas las 
  conectivas binarias aunque aparezcan definidas por separado, por tanto 
  haré la demostración estructurada para una de ellas pues el resto son 
  análogas. 

  Nos basaremos en el lema anterior @{term "subsubformulae"}.\<close>

lemma subformulas_in_subformulas_not:
  assumes "Not G \<in> setSubformulae F"
  shows "G \<in> setSubformulae F"
proof -
  have "setSubformulae (Not G) = {Not G} \<union> setSubformulae G" 
    by simp \<comment> \<open>Pendiente\<close>
  then have 1:"G \<in> setSubformulae (Not G)" 
    by (simp add: subformulae_self) \<comment> \<open>Pendiente\<close>
  show "G \<in> setSubformulae F" using assms 1 
    by (rule subsubformulae)
qed

text \<open>\comentario{Completar la demostración anterior.}\<close>

lemma subformulas_in_subformulas_and:
  assumes "G \<^bold>\<and> H \<in> setSubformulae F" 
  shows "G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
proof (rule conjI)
  have 1: "setSubformulae (G \<^bold>\<and> H) = 
          {G \<^bold>\<and> H} \<union> (setSubformulae G \<union> setSubformulae H)" 
    by (simp only: setSubformulae_and)
  then have 2: "G \<in> setSubformulae (G \<^bold>\<and> H)" 
    by (simp add: subformulae_self) \<comment> \<open>Pendiente\<close> 
  have 3: "H \<in> setSubformulae (G \<^bold>\<and> H)" 
    using 1 
    by (simp add: subformulae_self) \<comment> \<open>Pendiente\<close> 
  show "G \<in> setSubformulae F" using assms 2 by (rule subsubformulae)
  show "H \<in> setSubformulae F" using assms 3 by (rule subsubformulae)
qed

text \<open>\comentario{Completar la demostración anterior.}\<close>

text \<open>Mostremos ahora la demostración automática.\<close>

lemma subformulas_in_subformulas:
  "G \<^bold>\<and> H \<in> setSubformulae F 
   \<Longrightarrow> G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
  "G \<^bold>\<or> H \<in> setSubformulae F 
   \<Longrightarrow> G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
  "G \<^bold>\<rightarrow> H \<in> setSubformulae F 
   \<Longrightarrow> G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
  "\<^bold>\<not> G \<in> setSubformulae F \<Longrightarrow> G \<in> setSubformulae F"
     apply (rule conjI)
      apply (drule subformulas_in_subformulas_and)
      apply (erule conjunct1)
       apply (drule subformulas_in_subformulas_and)
     apply (erule conjunct2)
    prefer 3
     apply (drule subformulas_in_subformulas_not, assumption)  
  oops 

  text\<open>
 \comentario{Probar cada uno de los casos (faltan 2) por separado para 
usarlos en la prueba del lema.} 
\<close>

text \<open>\comentario{Completar la prueba anterior.}\<close>

text \<open>\comentario{Pendiente de revisar a partir de aquí.}\<close>

text \<open>\comentario{Completar la demostración anterior.}\<close>

text \<open>Concluimos la sección de subfórmulas con un resultado que
  relaciona varias funciones sobre la longitud de la lista 
  \<open>subformulae F\<close> de una fórmula \<open>F\<close> cualquiera.\<close>

lemma length_subformulae: "length (subformulae F) = size F" 
  oops

text \<open>En primer lugar aparece la clase @{term "size"} de la teoría de 
  números naturales ....

  Vamos a definir @{term size1} de manera idéntica a como aparece 
  @{term size} en la teoría.\<close>

class size1 =
  fixes size1 :: "'a \<Rightarrow> nat" 

instantiation nat :: size1
begin

definition size1_nat where [simp, code]: "size1 (n::nat) = n"

instance ..

end

text \<open>Como podemos observar, se trata de una clase que actúa sobre un 
  parámetro global de tipo \<open>'a\<close> cualquiera. Por otro lado, 
  \<open>instantation\<close> define una clase de parámetros, en este caso los 
  números naturales \<open>nat\<close> que devuelve como resultado. Incluye una 
  definición concreta del operador \<open>size1\<close> sobre dichos parámetros. 
  Además, el último \<open>instance\<close> abre una prueba que afirma que los 
  parámetros dados conforman la clase especificada en la definición. 
  Esta prueba que nos afirma que está bien definida la clase aparece
  omitida utilizando \<open>..\<close> .

  En particular, sobre una fórmula nos devuelve el número de elementos 
  de la lista cuyos elementos son los nodos y las hojas de su árbol de 
  formación.\<close>
          
value "size (n::nat) = n"
value "size (5::nat) = 5"
(* value "(5::nat) = {1,2,3,4,5}" que es eso*)

text \<open>Por otro lado, la función @{term "length"} de la teoría 
  \href{http://cort.as/-Stfm}{List.thy} nos indica la longitud de una 
  lista cualquiera de elementos, definiéndose utilizando el comando
  @{term "size"} visto anteriormente.\<close>

abbreviation length' :: "'a list \<Rightarrow> nat" where
  "length' \<equiv> size"

text \<open>Las demostración del resultado se vuelve a basar en la inducción 
  que nos despliega seis casos. 

  La prueba estructurada no resulta interesante, pues todos los casos 
  son inmediatos por simplificación como en el primer lema de esta 
  sección. 

  Incluimos a continuación la prueba automática.\<close>

lemma length_subformulae: "length (subformulae F) = size F" 
  by (induction F; simp)

text \<open>\comentario{Hacer la prueba detallada para mostrar los teoremas 
  utilizados.}\<close>

section \<open>Conectivas derivadas\<close>

text \<open>En esta sección definiremos nuevas conectivas y fórmulas a partir 
  de los ya definidos en el apartado anterior, junto con varios 
  resultados sobre los mismos. Veamos el primero.

  \begin{definicion}
    Se define la fórmula \<open>\<top>\<close> como la implicación \<open>\<bottom> \<longrightarrow> \<bottom>\<close>.
  \end{definicion}

  Se formaliza del siguiente modo.\<close>

definition Top ("\<top>") where
  "\<top> \<equiv> \<bottom> \<^bold>\<rightarrow> \<bottom>"

text \<open>Como podemos observar, se define mediante una relación de 
  equivalencia con otra fórmula ya conocida. El uso de dicha 
  equivalencia justifica el tipo @{term "definition"} empleado en este 
  caso. 

  Por la propia definición, es claro que \<open>\<top>\<close> no contiene ninguna
  variable proposicional, como se verifica a continuación en Isabelle.\<close>

lemma "atoms \<top> = \<emptyset>"
   by (simp only: Top_def formula.set Un_absorb)

text \<open>\comentario{Añadir regla al glosario.}\<close>

text \<open>\comentario{Añadir la doble implicación como conectiva derivada.}\<close>

text \<open>A continuación vamos a definir dos conectivas que generalizan la 
  conjunción y la disyunción para una lista finita de fórmulas. En
  particular, al ser aplicadas a listas, se definen conforme a la 
  estructura recursiva de las mismas que se muestra a continuación. 
  
  \begin{definicion}
    Las listas de fórmulas se definen recursivamente como sigue.
    \begin{itemize}
      \item La lista vacía es una lista.
      \item Sea \<open>F\<close> una fórmula y \<open>Fs\<close> una lista de fórmulas. Entonces,
        \<open>F#Fs\<close> es una lista de fórmulas.
    \end{itemize}
  \end{definicion} 

\comentario{Esta definición es un caso particular de listas. 
  No se si incluir la definicion de estructura e inducción general}

  De este modo, se definen las conectivas plurales de acuerdo a la 
  estructura recursiva anterior. Notemos que al referirnos simplemente 
  a disyunción o conjunción nos referiremos a la de dos elementos.

  \begin{definicion}
  La conjunción plural de una lista de fórmulas se define recursivamente
  como:
    \begin{itemize}
      \item La conjunción plural de la lista vacía es \<open>\<not>\<bottom>\<close>.
      \item Sea \<open>F\<close> una fórmula y \<open>Fs\<close> una lista de fórmulas. Entonces,
  la conjunción plural de \<open>F#Fs\<close> es la conjunción de \<open>F\<close> con la 
  conjunción plural de \<open>Fs\<close>.
    \end{itemize}
  \end{definicion}

  \begin{definicion}
  La disyunción plural de una lista de fórmulas se define recursivamente
  como:
    \begin{itemize}
      \item La disyunción plural de la lista vacía es \<open>\<not>\<bottom>\<close>.
      \item Sea \<open>F\<close> una fórmula y \<open>Fs\<close> una lista de fórmulas. Entonces,
  la disyunción plural de \<open>F#Fs\<close> es la disyunción de \<open>F\<close> con la 
  disyunción plural de \<open>Fs\<close>.
    \end{itemize}
  \end{definicion}

  Su formalización en Isabelle es la siguiente.

  \comentario{Da error que no localizo}\<close>

(*primrec BigAnd :: "'a formula list \<Rightarrow> 'a formula" ("\<^bold>\<And>_") where
  "\<^bold>\<And>Nil = (\<^bold>\<not>\<bottom>)" 
| "\<^bold>\<And>(F#Fs) = F \<^bold>\<and> \<^bold>\<And>Fs"

primrec BigOr :: "'a formula list \<Rightarrow> 'a formula" ("\<^bold>\<Or>_") where
  "\<^bold>\<Or>Nil = \<bottom>" 
| "\<^bold>\<Or>(F#Fs) = F \<^bold>\<or> \<^bold>\<Or>Fs"*)

text \<open>Ambas nuevas conectivas se definen con el tipo funciones 
  primitivas recursivas. Estas se basan en los dos casos descritos
  anteriormente: la lista vacía representada como \<open>Nil\<close> y la lista
  construida añadiendo una fórmula a una lista de fórmulas. 
  Además, se observa en cada conectiva plural el nuevo símbolo de 
  notación que aparece entre paréntesis.

  Por otro lado, como es habitual, estas definiciones recursivas llevan
  asociado el correspondiente esquema inductivo de demostración. En
  este caso, se trata de la inducción para la estructura de lista de 
  fórmulas.

  \begin{definicion}
    Sea \<open>\<P>\<close> una propiedad sobre lista de fórmulas proposicionales que 
    verifica las siguientes condiciones:
    \begin{itemize}
     \item La lista vacía la verifica.
     \item Dada una fórmula \<open>F\<close> y una lista de fórmulas \<open>Fs\<close> que la
      verifican, entonces \<open>F#Fs\<close> la verifica.
    \end{itemize}
    Entonces, todas las listas de fórmulas proposicionales tienen la 
    propiedad \<open>\<P>\<close>. 
  \end{definicion}

  La conjunción plural nos da el siguiente resultado.

\comentario{Añadir lema a mano y demostración. Falta demostración en Isabelle.}\<close>

(*lemma "atoms (\<^bold>\<And>Fs) = \<Union>(atoms ` set Fs)"
proof (induction Fs)
  case Nil
    have "atoms (\<^bold>\<And>Nil) = atoms (\<^bold>\<not>\<bottom>)" 
      by (simp only: BigAnd.simps(1))
    also have "\<dots> = atoms \<bottom>" 
      by (simp only: formula.set(3))
    also have "\<dots> = \<emptyset>" 
      by (simp only: formula.set)
    also have "\<dots> =  \<Union> atoms ` \<emptyset>" 
      by (simp only: list.set) 
  then show ?case 
next
case (Cons a Fs)
  assume H:"atoms (\<^bold>\<And>Fs) = \<Union>(atoms ` set Fs)" 
  show "atoms
  then show ?case sorry
qed*)

(*text \<open>Su demostración automática es la siguiente.\<close>

lemma atoms_BigAnd: "atoms (\<^bold>\<And>Fs) = \<Union>(atoms ` set Fs)"
  by (induction Fs; simp)*)

(*<*)
end
(*>*) 
