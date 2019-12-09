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

subsection \<open>Fórmulas\<close>

notation insert ("_ \<triangleright> _" [56,55] 55)

text \<open>En esta sección presentaremos una formalización en Isabelle de la sintaxis de la lógica 
  proposicional, junto con resultados y pruebas sobre la misma. En líneas generales, primero daremos
  las nociones de forma clásica y, a continuación, su correspondiente formalización.

  En primer lugar, supondremos que disponemos de los siguientes elementos:
  \begin{description}
    \item[Alfabeto:] Es una lista infinita de variables proposicionales. También pueden ser
    llamadas átomos o símbolos proposicionales.
    \item[Conectivas:] Conjunto finito cuyos elementos interactúan con las variables. Pueden ser 
    monarias que afectan a un único elemento o binarias que afectan a dos. En el primer grupo se 
    encuentra le negación (\<open>\<not>\<close>) y en el segundo la conjunción (\<open>\<and>\<close>), la 
    disyunción (\<open>\<or>\<close>) y la implicación (\<open>\<longrightarrow>\<close>).
  \end{description}

  A continuación definiremos la estructura de fórmula sobre los elementos anteriores.
  Para ello daremos una definición recursiva basada en dos elementos: un 
  conjunto de fórmulas básicas y una serie de procedimientos de definición de fórmulas a partir de 
  otras. El conjunto de las fórmulas será el menor conjunto de estructuras sinctáticas con dicho 
  alfabeto y conectivas que contiene a las básicas y es cerrado mediante los procedimientos de 
  definición que mostraremos a continuación.

  \begin{definicion}
    El conjunto de las fórmulas está formado por las siguientes:
    \begin{itemize}
      \item Las fórmulas atómicas, constituidas únicamente por una variable del alfabeto. Para 
      evitar confusiones, las notaremos como \<open>Atom p\<close>, donde \<open>p\<close> es un símbolo proposicional
      cualquiera.
      \item La constante \<open>\<bottom>\<close>.
      \item Dada una fórmula \<open>F\<close>, la negación de la misma es una fórmula: \<open>\<not> F\<close>.
      \item Dadas dos fórmulas \<open>F\<close> y \<open>G\<close>, la conjunción de ambas es una fórmula: \<open>F \<and> G\<close>.
      \item Dadas dos fórmulas \<open>F\<close> y \<open>G\<close>, la disyunción de ambas es una fórmula: \<open>F \<or> G\<close>.
      \item Dadas dos fórmulas \<open>F\<close> y \<open>G\<close>, la implicación \<open>F \<longrightarrow> G\<close> es una fórmula.
    \end{itemize}
  \end{definicion}

 Intuitivamente, las fórmulas proposicionales son entendidas como un tipo de árbol sintáctico 
  cuyos nodos son las conectivas y sus hojas las fórmulas atómicas.

        aquí va el arbol !!!!!!

  A continuación, veamos su representación en Isabelle.\<close>

datatype (atoms: 'a) formula = 
    Atom 'a
  | Bot                              ("\<bottom>")  
  | Not "'a formula"                 ("\<^bold>\<not>")
  | And "'a formula" "'a formula"    (infix "\<^bold>\<and>" 68)
  | Or "'a formula" "'a formula"     (infix "\<^bold>\<or>" 68)
  | Imp "'a formula" "'a formula"    (infixr "\<^bold>\<rightarrow>" 68)

text \<open>Como podemos observar en la definición, @{term "formula"} es un tipo de datos recursivo que se 
  entiende como un árbol que relaciona elementos de un tipo \<open>'a\<close> cualquiera del alfabeto 
  proposicional. En ella, los constructores del tipo son los siguientes:

  \begin{description}
    \item[Fórmulas básicas]:  
      \begin{itemize}
        \item @{const_typ Atom}
        \item @{const_typ Bot}
      \end{itemize}
    \item [Procedimientos de definición]:
      \begin{itemize}
        \item @{const_typ Not}
        \item @{const_typ And}
        \item @{const_typ Or}
        \item @{const_typ Imp}
      \end{itemize}
  \end{description}

  Cabe señalar que el término \<open>infix\<close> que precede al símbolo de notación de los nodos nos señala que 
  son infijos, e \<open>infixr\<close> se trata de un infijo asociado a la derecha.

  Además se define simultáneamente la función @{const_typ atoms}, que obtiene el conjunto de 
  variables proposicionales de una fórmula. De manera equivalente, daremos la siguiente definición.

  \begin{definicion}
    Sea \<open>F\<close> una fórmula proposicional. Entonces, se define \<open>conjAtoms(F)\<close> como el conjunto de 
    los átomos que aparecen en \<open>F\<close>.
  \end{definicion}

  Por otro lado, la definición de @{term "formula"} genera automáticamente los siguientes lemas 
  sobre la función de conjuntos @{term "atoms"} en Isabelle.
  
  \begin{itemize}
    \item[] @{thm formula.set[no_vars]}
  \end{itemize} 

  A continuación veremos varios ejemplos de fórmulas y el conjunto de sus variables proposicionales
  obtenido mediante @{term "atoms"}. Se observa que, por definición de conjunto, no contiene 
  elementos repetidos.\<close>

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

text \<open>En particular, el conjunto de símbolos proposicionales de la fórmula \<open>Bot\<close> es vacío. Además,
  para calcular esta constante es necesario especificar el tipo sobre el que se construye la 
  fórmula.\<close>

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

text \<open>Una vez definida la estructura de las fórmulas, vamos a introducir el método de demostración 
  que seguirán los resultados que aquí presentaremos, tanto en la teoría clásica como en Isabelle. 

  Según la definición recursiva de las fórmulas, dispondremos de un esquema de
  inducción sobre las mismas:

  \begin{definicion}
    Sea \<open>\<phi>\<close> una propiedad sobre fórmulas que verifica las siguientes condiciones:
    \begin{itemize}
      \item Las fórmulas atómicas la cumplen.
      \item La constante \<open>\<bottom>\<close> la cumple.
      \item Dada \<open>F\<close> fórmula que la cumple, entonces \<open>\<not> F\<close> la cumple.
      \item Dadas \<open>F\<close> y \<open>G\<close> fórmulas que la cumplen, entonces \<open>F * G\<close> la cumple, donde \<open>*\<close> simboliza
      cualquier conectiva binaria.
    \end{itemize}
    Entonces, todas las fórmulas proposicionales tienen la propiedad \<open>\<phi>\<close>.
  \end{definicion}

  Análogamente, como las fórmulas proposicionales están definidas mediante un tipo de datos 
  recursivo, Isabelle genera de forma automática el esquema de inducción correspondiente. De este
  modo, en las pruebas formalizadas utilizaremos la táctica @{term "induction"}, que corresponde al 
  siguiente esquema.

  \begin{itemize}
    \item[] @{thm formula.induct[no_vars]}
  \end{itemize} 

  Como hemos señalado, el esquema inductivo se aplicará en cada uno de los casos de los 
  constructores, desglosándose así seis casos distintos como se muestra anteriormente. 
  Además, todas las demostraciones sobre casos de conectivas binarias
  son equivalentes en esta sección, pues la construcción sintáctica de fórmulas es idéntica entre 
  ellas. Estas se diferencian esencialmente en la connotación semántica que veremos más adelante. 
  Por tanto, para simplificar algunas demostraciones sintácticas más extensas, expondremos la prueba
  estructurada únicamente para uno de los casos de conectivas binarias.

  Llegamos así al primer resultado de este apartado:

    \begin{lema}
      El conjunto de los átomos de una fórmula proposicional es finito.
    \end{lema}

  Para proceder a la demostración, vamos a dar una definición inductiva de conjunto 
  finito que tendrá la clave de la prueba del lema. Cabe añadir que la demostración seguirá el 
  esquema inductivo relativo a la estructura de fórmula, y no el que resulta de esta definición.

  \begin{definicion}
    Los conjuntos finitos son:
      \begin{itemize}
        \item El vacío.
        \item Dado un conjunto finito \<open>A\<close> y un elemento cualquiera \<open>a\<close>, entonces \<open>{a} \<union> A\<close> es 
        finito.
      \end{itemize}
  \end{definicion}


  En Isabelle, podemos formalizar el lema como sigue.\<close>

lemma "finite (atoms F)"
  oops

text \<open>Análogamente, el enunciado formalizado contiene la defición @{term "finite S"}, 
  perteneciente a la teoría \href{https://n9.cl/x86r}{FiniteSet.thy}.\<close>

inductive finite' :: "'a set \<Rightarrow> bool" where
  emptyI' [simp, intro!]: "finite' {}"
| insertI' [simp, intro!]: "finite' A \<Longrightarrow> finite' (insert a A)"

text \<open>Observemos que la definición anterior corresponde a @{term finite'}. Sin embargo, es 
  equivalente a @{term finite} de la teoría original. Este cambio de notación es necesario para 
  no definir dos veces de manera idéntica la misma noción en Isabelle. Por otra parte, esta
  definición permitiría la demostración del lema por 
  simplificacion pues, dentro de ella las reglas que especifica se han añadido como tácticas de 
  \<open>simp\<close> e \<open>intro!\<close>. Sin embargo, conforme al objetivo de este análisis, detallaremos dónde es usada
  cada una de las reglas en la prueba detallada. 
 
  A continuación, veamos en primer lugar la demostración clásica del lema. 

 \begin{demostracion}
  La prueba es por inducción sobre el tipo recursivo de las fórmulas. Veamos cada caso.\\
  Consideremos una fórmula atómica \<open>Atom p\<close> cualquiera. Entonces, 
  \<open>conjAtoms(Atom p) = {p} = {p} \<union> \<emptyset>\<close> es finito.\\
  Sea la fórmula \<open>\<bottom>\<close>. Entonces, \<open>conjAtoms(\<bottom>) = \<emptyset>\<close> y, por lo tanto, finito.\\
  Sea \<open>F\<close> una fórmula tal que \<open>conjAtoms(F)\<close> es finito. Entonces, por definición, 
  \<open>conjAtoms(\<not> F) = conjAtoms(F)\<close> y, por hipótesis de inducción, es finito.\\
  Consideremos las fórmulas \<open>F\<close> y \<open>G\<close> cuyos conjuntos de átomos \<open>conjAtoms(F)\<close> y 
  \<open>conjAtoms(G)\<close> son finitos. Por construcción, \<open>conjAtoms(F*G) = conjAtoms(F) \<union> conjAtoms(G)\<close> 
  para cualquier \<open>*\<close> conectiva binaria. Por lo tanto, por hipótesis de inducción, 
  \<open>conjAtoms(F*G)\<close> es finito. 
 \end{demostracion} 

  Veamos ahora la prueba detallada en Isabelle del resultado que, aunque es sencillo, nos muestra 
  un ejemplo claro de la estructura inductiva que nos acompañará en las siguientes demostraciones.
  En este primer lema mostraré con detalle de todos los casos de conectivas binarias, 
  aunque se puede observar que son completamente equivalentes. Para facilitar la lectura, primero
  demostraré por separado cada uno de los casos según el esquema inductivo de fórmulas, y finalmente
  añadiré la prueba para una fórmula cualquiera a partir de los anteriores.\<close>

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
  
text \<open>Su demostración automática es la siguiente.\<close>

lemma "finite (atoms F)" 
  by (induction F) simp_all 

subsection\<open>Subfórmulas\<close>

text \<open>Veamos la noción de subfórmulas.

  \begin{definicion}
  El conjunto de subfórmulas de una fórmula \<open>F\<close>, notada \<open>Subf(F)\<close>, se define recursivamente como:
    \begin{itemize}
      \item \<open>{\<bottom>}\<close> si \<open>F\<close> es \<open>\<bottom>\<close>.
      \item \<open>{F}\<close> si \<open>F\<close> es una fórmula atómica.
      \item \<open>{F} \<union> Subf(G)\<close> si \<open>F\<close> es \<open>\<not>G\<close>.
      \item \<open>{F} \<union> Subf(G) \<union> Subf(H)\<close> si \<open>F\<close> es \<open>G*H\<close> donde \<open>*\<close> es cualquier conectiva binaria.
    \end{itemize}
  \end{definicion}\<close>

text \<open>Para proceder a la formalización de Isabelle, seguiremos dos etapas. En primer lugar, 
  definimos la función primitiva recursiva @{term "subformulae"}. Esta nos devolverá
  la lista de todas las subfórmulas de una fórmula original obtenidas recursivamente.\<close>
 
primrec subformulae :: "'a formula \<Rightarrow> 'a formula list" where
  "subformulae (Atom k) = [Atom k]" 
| "subformulae \<bottom>        = [\<bottom>]" 
| "subformulae (\<^bold>\<not> F)    = (\<^bold>\<not> F) # subformulae F" 
| "subformulae (F \<^bold>\<and> G)  = (F \<^bold>\<and> G) # subformulae F @ subformulae G" 
| "subformulae (F \<^bold>\<or> G)  = (F \<^bold>\<or> G) # subformulae F @ subformulae G"
| "subformulae (F \<^bold>\<rightarrow> G) = (F \<^bold>\<rightarrow> G) # subformulae F @ subformulae G"
 
text \<open>Observemos que, en la definición anterior, \<open>#\<close> es el operador que añade un elemento al 
  comienzo de una lista y \<open>@\<close> concatena varias listas. Siguiendo con los ejemplos, apliquemos
  @{term subformulae} en las distintas fórmulas. En particular, al tratarse de una 
  lista pueden aparecer elementos repetidos como se muestra a continuación.\<close>

notepad
begin
  fix p :: 'a

  have "subformulae (Atom p) = [Atom p]"
    by simp

  have "subformulae (\<^bold>\<not> (Atom p)) = [\<^bold>\<not> (Atom p), Atom p]"
    by simp

  have "subformulae ((Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r) = 
       [(Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r, Atom p \<^bold>\<rightarrow> Atom q, Atom p, Atom q, 
        Atom r]"
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

text \<open>De este modo, \<open>Subf(·)\<close> es equivalente a esta nueva definición. La justificación para este 
  cambio en el tipo reside en las propiedades sobre conjuntos que facilitan las demostraciones
  de los resultados que mostraremos a continuación, frente a las listas. Algunas de estas ventajas 
  son la eliminación de elementos repetidos o las operaciones propias de teoría de conjuntos. 
  Observemos los siguientes ejemplos con el tipo de conjuntos.\<close>

notepad
begin
  fix p q r :: 'a

  have "setSubformulae (Atom p \<^bold>\<or> Atom p) = {Atom p \<^bold>\<or> Atom p, Atom p}"
    by simp
  
  have "setSubformulae ((Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r) =
        {(Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r, Atom p \<^bold>\<rightarrow> Atom q, Atom p, Atom q, Atom r}"
  by auto   
end

text \<open>Por otro lado, debemos señalar que el uso de @{term "abbreviation"} para definir 
  @{term "setSubformulae"} no es arbitrario. Esta elección se debe a que el tipo 
  @{term "abbreviation"} se trata de un sinónimo para una expresión cuyo tipo ya existe (en nuestro 
  caso, convertir en conjunto la lista obtenida con @{term "subformulae"}). 
  No es una definición propiamente dicha, sino una forma de nombrar la composición de las 
  funciones @{term "set"} y @{term "subformulae"}.\\

  En primer lugar, vamos a probar que @{term "setSubformulae"} es equivalente a @{term "Subf"} en
  Isabelle.
  Para ello utilizaremos el siguiente resultado sobre listas, probado automáticamente
  como sigue.\<close>

lemma set_insert: "set (x # ys) = {x} \<union> set ys"
  by (simp only: list.set(2) Un_insert_left sup_bot.left_neutral)

text \<open>Por tanto, obtenemos la equivalencia como resultado de los siguientes lemas, que aparecen 
  demostrados de manera detallada.\<close>

lemma setSubformulae_atom:
  "setSubformulae (Atom p) = {Atom p}"
    by (simp only: subformulae.simps(1), simp only: list.set)

lemma setSubformulae_bot:
  "setSubformulae (\<bottom>) = {\<bottom>}"
    by (simp only: subformulae.simps(2), simp only: list.set)

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

text \<open>Una vez probada la equivalencia, comencemos con los resultados correspondientes a 
  las subfórmulas. En primer lugar, tenemos la siguiente propiedad como consecuencia directa
  de la equivalencia de funciones anterior.

  \begin{lema}
    \<open>F \<in> Subf(F)\<close>.
  \end{lema}

  \begin{demostracion}
    Procedamos por inducción sobre la estructura de fórmula probando los correspondientes tipos.\\
    Sea \<open>Atom p\<close> fórmula atómica para \<open>p\<close> variable proposicional cualquiera. Por definición
    de \<open>Subf\<close> tenemos que \<open>Subf(Atom p) = {Atom p}\<close>, luego se tiene la propiedad.\\
    Sea la fórmula \<open>\<bottom>\<close>. Como \<open>Subf(\<bottom>) = {\<bottom>}\<close>, se verifica el resultado.\\
    Por definición del conjunto de subfórmulas de \<open>Subf(\<not> F)\<close> se tiene la propiedad 
    para este caso, pues \<open>Subf(\<not> F) = {\<not> F} \<union> Subf(F) \<Longrightarrow> \<not> F \<in> Subf(\<not> F)\<close> como queríamos ver.\\
    Análogamente, para cualquier conectiva binaria \<open>*\<close> y fórmulas \<open>F\<close> y \<open>G\<close> se cumple
    \<open>Subf(F*G) = {F*G} \<union> Subf(F) \<union> Subf(G)\<close>, luego se verifica análogamente.
  \end{demostracion}

  Formalicemos ahora el lema con su correspondiente demostración detallada.\<close>

 (*<*)find_theorems "_\<in>_" -name:List name:Set(*>*)

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
    by (simp add: insertI1 setSubformulae_not)
next
case (And F1 F2)
  then show ?case 
    by (simp add: insertI1 setSubformulae_and)
next
case (Or F1 F2)
  then show ?case 
    by (simp add: insertI1 setSubformulae_or)
next
case (Imp F1 F2)
  then show ?case 
    by (simp add: insertI1 setSubformulae_imp)
qed

text \<open>La demostración automática es la siguiente.\<close>

lemma "F \<in> setSubformulae F"
  by (induction F) simp_all

text \<open>Procedamos con los demás resultados de la sección. Como hemos señalado con anterioridad, 
  utilizaremos varias propiedades de conjuntos pertenecientes a la teoría 
  \href{https://n9.cl/qatp}{Set.thy} de Isabelle, que apareceran en el glosario final. 

  Además, definiremos dos reglas adicionales que utilizaremos con frecuencia.\<close>

 (*<*)find_theorems "_\<subseteq>_" -name:List name:Set(*>*)

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

text \<open>Sus correspondientes demostraciones automáticas se muestran a continuación.\<close>

lemma "A \<union> B \<subseteq> C \<Longrightarrow> A \<subseteq> C"
  by simp

lemma "A \<union> B \<subseteq> C \<Longrightarrow> B \<subseteq> C"
  by simp

text \<open>Veamos ahora los distintos resultados sobre subfórmulas.

  \begin{lema}
    Sea \<open>F\<close> una fórmula proposicional y \<open>conjAtoms(F)\<close> el conjunto de sus variables proposicionales.
    Sea \<open>A\<^sub>F\<close> el conjunto de las fórmulas atómicas formadas a partir de cada elemento de 
    \<open>conjAtoms(F)\<close>. Entonces, \<open>A\<^sub>F \<subseteq> Subf(F)\<close>.\\ 
    Por tanto, las fórmulas atómicas son subfórmulas.
  \end{lema}

  \begin{demostracion}
    La prueba seguirá el esquema inductivo para la estructura de fórmulas. Veamos cada caso:\\
    Consideremos la fórmula atómica \<open>Atom p\<close> para \<open>p\<close> una variable cualquiera. Entonces, 
    \<open>conjAtoms(Atom p) = {p}\<close>. De este modo, el conjunto \<open>A\<^sub>A\<^sub>t\<^sub>o\<^sub>m \<^sub>p\<close> correspondiente será 
    \<open>A\<^sub>A\<^sub>t\<^sub>o\<^sub>m \<^sub>p = {Atom p} \<subseteq> {Atom p} = Subf(Atom p)\<close> como queríamos demostrar.\\
    Sea la fórmula \<open>\<bottom>\<close>. Como \<open>conjAtoms(\<bottom>) = \<emptyset>\<close>, es claro que \<open>A\<^sub>\<bottom> = \<emptyset> \<subseteq> Subf(\<bottom>) = \<emptyset>\<close>.\\
    Sea la fórmula \<open>F\<close> tal que \<open>A\<^sub>F \<subseteq> Subf(F)\<close>. Probemos el resultado para \<open>\<not> F\<close>. Por 
    definición tenemos que \<open>conjAtoms(\<not> F) = conjAtoms(F)\<close>, luego \<open>A\<^sub>\<not>\<^sub>F = A\<^sub>F\<close>. Además, 
    \<open>Subf(\<not> F) = {\<not> F} \<union> Subf(F)\<close>. Por tanto, por hipótesis de inducción tenemos:\\
    \<open>A\<^sub>\<not>\<^sub>F = A\<^sub>F \<subseteq> Subf(F) \<subseteq> {\<not> F} \<union> Subf(F) = Subf(\<not> F) \<Longrightarrow> A\<^sub>\<not>\<^sub>F \<subseteq> Subf(\<not> F)\<close>\\
    Sean las fórmulas \<open>F\<close> y \<open>G\<close> tales que \<open>A\<^sub>F \<subseteq> Subf(F)\<close> y \<open>A\<^sub>G \<subseteq> Subf(G)\<close>. Probemos ahora
    \<open>A\<^sub>F\<^sub>*\<^sub>G \<subseteq> Subf(F*G)\<close> para cualquier conectiva binaria \<open>*\<close>. Por un lado, 
    \<open>conjAtoms(F*G) = conjAtoms(F) \<union> conjAtoms(G)\<close>, luego \<open>A\<^sub>F\<^sub>*\<^sub>G = A\<^sub>F \<union> A\<^sub>G\<close>. Por tanto, por 
    hipótesis de inducción y definición del conjunto de subfórmulas, se tiene:\\
    \<open>A\<^sub>F\<^sub>*\<^sub>G = A\<^sub>F \<union> A\<^sub>G \<subseteq> conjAtoms(F) \<union> conjAtoms(G) \<subseteq> {F*G} \<union> conjAtoms(F) \<union> conjAtoms(G) = 
    conjAtoms(F*G)\<close>\\
    Luego, \<open>A\<^sub>F\<^sub>*\<^sub>G \<subseteq> conjAtoms(F*G)\<close> como queríamos demostrar.  
  \end{demostracion}

  En Isabelle, se especifica como sigue.\<close>

lemma atoms_are_subformulae: "Atom ` atoms F \<subseteq> setSubformulae F"
  oops

text \<open>Debemos observar que \<open>Atom ` atoms F\<close> construye las fórmulas atómicas a partir de cada uno de 
  los elementos de \<open>atoms F\<close>, creando un conjunto de fórmulas atómicas. Dicho conjunto es 
  equivalente al conjunto \<open>A\<^sub>F\<close> del enunciado del lema. Para ello emplea el infijo \<open>`\<close> definido como 
  notación abreviada de @{term "image"} que calcula la imagen de un conjunto en la teoría 
  \href{https://n9.cl/qatp}{Set.thy}.

  \begin{itemize}
    \item[] @{thm[mode=Def] image_def[no_vars]} \hfill (@{text image_def})
  \end{itemize}

  Para aclarar su funcionamiento, veamos ejemplos para distintos casos de fórmulas.\<close>

notepad
begin
  fix p q r :: 'a

  have "Atom `atoms (Atom p \<^bold>\<or> \<bottom>) = {Atom p}"
    by simp

  have "Atom `atoms ((Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r) = 
       {Atom p, Atom q, Atom r}"
    by auto 

  have "Atom `atoms ((Atom p \<^bold>\<rightarrow> Atom p) \<^bold>\<or> Atom r) = {Atom p, Atom r}"
    by auto
end

text \<open>Además, esta función tiene las siguientes propiedades sobre conjuntos que utilizaremos
  en la demostración.

  \begin{itemize}
    \item[] @{thm[mode=Rule] image_Un[no_vars]} 
      \hfill (@{text image_Un})
    \item[] @{thm[mode=Rule] image_insert[no_vars]} 
      \hfill (@{text image_insert})
    \item[] @{thm[mode=Rule] image_empty[no_vars]} 
      \hfill (@{text image_empty})
  \end{itemize}

  Una vez hechas las aclaraciones necesarias, comencemos la demostración estructurada.
  Esta seguirá el esquema inductivo señalado con anterioridad. Debido a la extensión de la prueba
  demostraremos de manera detallada únicamente el caso de conectiva binaria de la conjunción. 
  El resto son totalmente equivalentes y los dejaré indicados
  de manera automática. Observemos que los casos básicos de @{term "Atom x"} y @{term "Bot"} 
  podrían demostrarse de manera directa únicamente mediante simplificación.\<close>

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
  then show ?case by auto
next
  case (Imp F1 F2)
  then show ?case by auto
qed

text \<open>La demostración automática queda igualmente expuesta a continuación.\<close>

lemma "Atom ` atoms F \<subseteq> setSubformulae F"
  by (induction F)  auto

text \<open>La siguiente propiedad declara que el conjunto de átomos de una subfórmula está contenido 
  en el conjunto de átomos de la propia fórmula.
  \begin{lema}
    Sea \<open>G \<in> Subf(F)\<close>, entonces el \<open>conjAtoms(G) \<subseteq> conjAtoms(F)\<close>.
  \end{lema}

  \begin{demostracion}
  Procedemos mediante inducción en la estructura de las fórmulas según los distintos casos:\\
    Sea \<open>Atom p\<close> una fórmula atómica cualquiera. Si \<open>G \<in> Subf(Atom p)\<close>, como
    \<open>conjAtoms(Atom p) = {Atom p}\<close>, se tiene \<open>G = Atom p\<close>. Por tanto, 
    \<open>conjAtoms(G) = conjAtoms(Atom p) \<subseteq> conjAtoms(Atom p)\<close>.\\
    Sea la fórmula \<open>\<bottom>\<close>. Si \<open>G \<in> Subf(\<bottom>)\<close>, como
    \<open>conjAtoms(\<bottom>) = {\<bottom>}\<close>, se tiene \<open>G = \<bottom>\<close>. Por tanto, 
    \<open>conjAtoms(G) = conjAtoms(\<bottom>) \<subseteq> conjAtoms(\<bottom>)\<close>.\\
    Sea la fórmula \<open>F\<close> cualquiera tal que para cualquier subfórmula \<open>G \<in> Subf(F)\<close> se 
    verifica \<open>conjAtoms(G) \<subseteq> conjAtoms(F)\<close>. Supongamos \<open>G' \<in> Subf(\<not> F)\<close> cualquiera, probemos que 
    \<open>conjAtoms(G') \<subseteq> conjAtoms(\<not> F)\<close>.\\
    Por definición, tenemos que \<open>Subf(\<not> F) = {\<not> F} \<union> Subf(F)\<close>. De este modo, tenemos dos opciones:
    \<open>G' \<in> {\<not> F}\<close> o \<open>G' \<in> Subf(F)\<close>. Del primer caso se deduce \<open>G' = \<not> F\<close> y, por tanto, se tiene el
    resultado. Observando el segundo caso, por hipótesis de inducción, se tiene 
    \<open>conjAtoms(G') \<subseteq> conjAtoms(F)\<close>. Además, como \<open>conjAtoms(\<not> F) = conjAtoms(F)\<close>, se obtiene
    \<open>conjAtoms(G') \<subseteq> conjAtoms(\<not> F)\<close> como queríamos probar.\\
    Sea \<open>F1\<close> fórmula proposicional tal que para cualquier \<open>G \<in> Subf(F1)\<close> se tiene 
    \<open>conjAtoms(G) \<subseteq> conjAtoms(F1)\<close>. Sea también \<open>F2\<close> tal que dada \<open>G \<in> Subf(F2)\<close> cualquiera se 
    tiene también \<open>conjAtoms(G) \<subseteq> conjAtoms(F2)\<close>. Supongamos \<open>G' \<in> Subf(F1*F2)\<close> donde \<open>*\<close> es 
    cualquier conectiva binaria. Vamos a probar que \<open>conjAtoms(G') \<subseteq> conjAtoms(F1*F2)\<close>.\\
    En primer lugar, como \<open>Subf(F1*F2) = {F1*F2} \<union> (Subf(F1) \<union> Subf(F2))\<close>, se desglosan tres
    casos posibles para \<open>G'\<close>:\\
    Si \<open>G' \<in> {F1*F2}\<close>, entonces \<open>G' = F1*F2\<close> y se tiene la propiedad.\\
    Si \<open>G' \<in> Subf(F1) \<union> Subf(F2)\<close>, entonces por propiedades de conjuntos:
    \<open>G' \<in> Subf(F1) \<or> G' \<in> Subf(F2)\<close>. Si \<open>G' \<in> Subf(F1)\<close>, por hipótesis de inducción se tiene 
    \<open>conjAtoms(G') \<subseteq> conjAtoms(F1)\<close>. Como \<open>conjAtoms(F1*F2) = conjAtoms(F1) \<union> conjAtoms(F2)\<close>, se 
    obtiene el resultado como consecuencia de la transitividad de contención para conjuntos. El 
    caso \<open>G' \<in> Subf(F2)\<close> se demuestra de la misma forma.      
  \end{demostracion}

  Formalizado en Isabelle:\<close>

lemma subformula_atoms: "G \<in> setSubformulae F \<Longrightarrow> atoms G \<subseteq> atoms F"
  oops

text \<open>Veamos su demostración estructurada. Desarrollaré la disyunción como representante del caso
  de las conectivas binarias, pues los demás son equivalentes.\<close>

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
  proof
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
  proof 
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
    proof 
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

lemma subformulas_atoms:
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
  then show ?case by auto
next
  case (Or F1 F2)
  then show ?case by (simp only: subformulas_atoms_or)
next
  case (Imp F1 F2)
  then show ?case by auto
qed

text\<open>Por último, su demostración aplicativa automática.\<close>

lemma subformula_atoms: "G \<in> setSubformulae F \<Longrightarrow> atoms G \<subseteq> atoms F"
  by (induction F) auto

text\<open>CORREGIDO HASTA AQUÍ\<close>
(*
text\<open>A continuación introduciremos un lema que facilitará
  las posteriores demostraciones detalladas mediante contenciones en cadena.

  \begin{lema}
    Sea \<open>G \<in> Subf(F)\<close>, entonces \<open>Subf(G) \<subseteq> Subf(F)\<close>.
  \end{lema} 

  \begin{demostracion}
    Vamos a probarlo siguiendo el esquema inductivo habitual viendo los distintos casos:\\
    Sea una fórmula atómica cualquiera \<open>Atom p\<close>. 
  \end{demostracion}

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
    Sea \<open>G \<in> Subf(F)\<close> y \<open>H \<in> Subf(G)\<close>, entonces \<open>H \<in> SubfSet(F)\<close>.
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
  have "H \<in> setSubformulae H" by (rule subformulae_self)
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
*)

(*<*)
end
(*>*) 