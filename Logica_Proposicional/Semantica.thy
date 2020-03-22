(*<*) 
theory Semantica
  imports 
    Sintaxis
begin
(*>*)

section \<open>Semántica\<close>

text \<open>En esta sección presentaremos la semántica de las fórmulas
  proposicionales y su formalización en Isabelle/HOL. 

  \begin{definicion}
  Una interpretación es una aplicación del conjunto de variables
  proposicionales en el conjunto \<open>\<BB>\<close> de los booleanos.
  \end{definicion}

  De este modo, las interpretaciones asignan valores de verdad a las 
  variables proposicionales.

  En Isabelle, se formaliza como sigue.\<close> 

type_synonym 'a valuation = "'a \<Rightarrow> bool"

  text \<open>Como podemos observar, \<open>'a valuation\<close> representa
  una función entre elementos de tipo \<open>'a\<close> cualquiera que conforman los
  átomos de una fórmula proposicional a los que les asigna un booleano. 
  Se define mediante el tipo \<open>type_synonym\<close>, pues consiste en renombrar 
  una construcción ya existente en Isabelle.

  Dada una interpretación, vamos a definir el valor de verdad de una 
  fórmula proposicional en dicha interpretación.

  \begin{definicion}
  Para cada interpretación \<open>\<A>\<close> existe una única aplicación \<open>\<I>\<^sub>\<A>\<close> desde 
  el conjunto de fórmulas al conjunto \<open>\<BB>\<close> de los booleanos definida 
  recursivamente sobre la estructura de las fórmulas como sigue:\\
  Sea \<open>F\<close> una fórmula cualquiera,
    \begin{itemize}
      \item Si \<open>F\<close> es una fórmula atómica de la forma \<open>p\<close>, entonces \\ 
        \<open>\<I>\<^sub>\<A>(F) = \<A>(p)\<close>.
      \item Si \<open>F\<close> es la fórmula \<open>\<bottom>\<close>, entonces \<open>\<I>\<^sub>\<A>(F) = False\<close>.
      \item Si \<open>F\<close> es de la forma \<open>\<not> G\<close> para cierta fórmula \<open>G\<close>, 
        entonces\\ \<open>\<I>\<^sub>\<A>(F) = \<not> \<I>\<^sub>\<A>(G)\<close>.
      \item Si \<open>F\<close> es de la forma \<open>G \<and> H\<close> para ciertas fórmulas \<open>G\<close> y 
        \<open>H\<close>, entonces\\ \<open>\<I>\<^sub>\<A>(F)= \<I>\<^sub>\<A>(G) \<and> \<I>\<^sub>\<A>(H)\<close>.
      \item Si \<open>F\<close> es de la forma \<open>G \<or> H\<close> para ciertas fórmulas \<open>G\<close> y 
        \<open>H\<close>, entonces\\ \<open>\<I>\<^sub>\<A>(F)= \<I>\<^sub>\<A>(G) \<or> \<I>\<^sub>\<A>(H)\<close>.
      \item Si \<open>F\<close> es de la forma \<open>G \<longrightarrow> H\<close> para ciertas fórmulas \<open>G\<close> y 
        \<open>H\<close>, entonces\\ \<open>\<I>\<^sub>\<A>(F)= \<I>\<^sub>\<A>(G) \<longrightarrow> \<I>\<^sub>\<A>(H)\<close>.
    \end{itemize}
  En estas condiciones se dice que \<open>\<I>\<^sub>\<A>(F)\<close> es el valor de la fórmula 
  \<open>F\<close> en la interpretación \<open>\<A>\<close>.
  \end{definicion}

  En Isabelle, dada una interpretación \<open>\<A>\<close> y una fórmula \<open>F\<close>, vamos a 
  definir \<open>\<I>\<^sub>\<A>(F)\<close> mediante la función \<open>formula_semantics \<A> F\<close>, 
  notado como \<open>\<A> \<Turnstile> F\<close>.\<close>

primrec formula_semantics :: 
  "'a valuation \<Rightarrow> 'a formula \<Rightarrow> bool" (infix "\<Turnstile>" 51) where
  "\<A> \<Turnstile> Atom k = \<A> k" 
| "\<A> \<Turnstile> \<bottom> = False" 
| "\<A> \<Turnstile> Not F = (\<not> \<A> \<Turnstile> F)" 
| "\<A> \<Turnstile> And F G = (\<A> \<Turnstile> F \<and> \<A> \<Turnstile> G)" 
| "\<A> \<Turnstile> Or F G = (\<A> \<Turnstile> F \<or> \<A> \<Turnstile> G)" 
| "\<A> \<Turnstile> Imp F G = (\<A> \<Turnstile> F \<longrightarrow> \<A> \<Turnstile> G)"

text \<open>Como podemos observar, \<open>formula_semantics\<close> es una función
  primitiva recursiva, como indica el tipo \<open>primrec\<close>, notada con el 
  símbolo infijo \<open>\<Turnstile>\<close>. De este modo, dada una interpretación \<open>\<A>\<close> sobre 
  variables proposicionales de un tipo \<open>'a\<close> cualquiera y una fórmula,
  se define el valor de la fórmula en la interpretación \<open>\<A>\<close> como se 
  muestra. Veamos algunos ejemplos.\<close>

notepad
begin
  fix \<A> :: "nat valuation"

have "(\<A> (1 := True, 2 := False, 3 := True) 
            \<Turnstile> (\<^bold>\<not> ((Atom 1 \<^bold>\<or> Atom 2)) \<^bold>\<rightarrow> Atom 3)) = True" 
  by simp
  
  have "(\<A> (1 := True) \<Turnstile> Atom 1) = True"
    by simp

  have "(\<A> (1 := True) \<Turnstile> \<^bold>\<not> (Atom 1)) = False"
    by simp

  have "(\<A> (1 := True, 2 := False) \<Turnstile> \<^bold>\<not> (Atom 1) \<^bold>\<and> (Atom 2)) = False"
    by simp

  have "(\<A> (1 := True, 2 := False, 3 := False) 
            \<Turnstile> (\<^bold>\<not> ((Atom 1 \<^bold>\<and> Atom 2)) \<^bold>\<rightarrow> Atom 3)) = False" 
    by simp

end

text \<open>En los ejemplos anteriores se ha usado la notación para
  funciones\\ \<open>f (a := b)\<close>. Dicha notación abreviada se corresponde con 
  la definción de \<open>fun_upd f a b\<close>.

  \begin{itemize}
    \item[] @{thm[mode=Def] fun_upd_def} 
      \hfill (@{text fun_upd_def})
  \end{itemize}

  Es decir, \<open>f (a:=b)\<close> es la función que para cualquier valor \<open>x\<close> del 
  dominio, si \<open>x = a\<close>, entonces devuelve \<open>b\<close>. En caso contrario, 
  devuelve el valor \<open>f x\<close>.

  A continuación veamos una serie de definiciones sobre fórmulas e 
  interpretaciones, en primer lugar, la noción de modelo de una 
  fórmula.

  \begin{definicion}
  Una interpretación \<open>\<A>\<close> es modelo de una fórmula \<open>F\<close> si\\
  \<open>\<I>\<^sub>\<A>(F) = True\<close>. 
  \end{definicion}

  En Isabelle se formaliza de la siguiente manera.\<close>

definition "isModel \<A> F \<equiv> \<A> \<Turnstile> F"

text \<open>Veamos cuáles de las interpretaciones de los ejemplos anteriores
  son modelos de las fórmulas dadas.\<close>

notepad
begin
  fix p q r :: 'a

  have "isModel (\<A> (p := True)) (Atom p)"
    by (simp add: isModel_def)

  have "\<not> isModel (\<A> (p := True)) (\<^bold>\<not> (Atom p))"
    by (simp add: isModel_def)

  have "\<not> isModel (\<A> (p := True, q := False)) (\<^bold>\<not> (Atom p) \<^bold>\<and> (Atom q))"
    by (simp add: isModel_def)

  have "\<not> isModel (\<A> (p := True, q := False, r := False)) 
          (\<^bold>\<not> ((Atom p \<^bold>\<and> Atom q)) \<^bold>\<rightarrow> Atom r)"
    by (simp add: isModel_def)

  have "isModel (\<A> (p := True, q := False, r := True)) 
          (\<^bold>\<not> ((Atom p \<^bold>\<or> Atom q)) \<^bold>\<rightarrow> Atom r)"
    by (simp add: isModel_def)

end

text \<open>Demos ahora la noción de fórmula satisfacible.

  \begin{definicion}
    Una fórmula es satisfacible si tiene algún modelo.
  \end{definicion}

  Se concreta en Isabelle como sigue.\<close>

definition "satF(F) \<equiv> \<exists>\<A>. \<A> \<Turnstile> F"

text \<open>Mostremos ejemplos de fórmulas satisfacibles y no satisfacibles.
  Estas últimas son también llamadas contradicciones, pues son
  falsas para cualquier interpretación.\<close>

notepad
begin
  fix p :: 'a

  have "satF (Atom p)"
    by (meson formula_semantics.simps(1) satF_def)

  have "satF (Atom p \<^bold>\<and> Atom q)" 
    using satF_def by force

  have "\<not> satF (Atom p \<^bold>\<and> (\<^bold>\<not> (Atom p)))"
    using satF_def by force

end

text \<open>Como podemos observar, \<open>isModel\<close> y \<open>satF\<close> se han 
  formalizado usando el tipo \<open>definition\<close> pues, en ambos casos, hemos
  renombrado una construcción no recursiva ya existente en Isabelle/HOL.

  Continuemos con la noción de fórmula válida o tautología.

  \begin{definicion} 
  \<open>F\<close> es una fórmula válida o tautología (\<open>\<Turnstile> F\<close>) si toda interpretación 
  es modelo de \<open>F\<close>. 
  \end{definicion}

  Es decir, una tautología es una fórmula que es verdadera para 
  cualquier interpretación. En Isabelle se formaliza de la siguiente 
  manera.\<close>

abbreviation valid ("\<Turnstile> _" 51) where
  "\<Turnstile> F \<equiv> \<forall>\<A>. \<A> \<Turnstile> F"

text \<open>Por otro lado, podemos observar que se ha definido mediante el 
  tipo \<open>abbreviation\<close>, pues no se trata de una definición propiamente 
  dicha, sino de un mecanismo en Isabelle/HOl para nombrar
  ciertas macros sintácticas. En este caso, introduce una nueva notación 
  para una construcción compleja formada por un cuantificador 
  universal aplicado a uno de los argumentos de \<open>formula_semantics\<close>.

  Veamos un ejemplo clásico de tautología: el principio del tercio
  excluso.\<close>

notepad
begin
  fix p :: 'a

  have "\<Turnstile> (Atom p \<^bold>\<or> (\<^bold>\<not> (Atom p)))"
    by simp

end

text \<open>Una vez presentados los conceptos anteriores, mostremos el 
  primer lema de la sección.

  \begin{lema}
  Dadas una interpretación \<open>\<A>\<close> y una fórmula \<open>F\<close> de modo que \<open>A\<close>
  es una variable proposicional que no pertenece al conjunto de átomos
  de \<open>F\<close>. Sea la interpretación \<open>\<A>'\<close> la función que devuelve \<open>\<A>(q)\<close>
  para cualquier variable proposicional \<open>q\<close> distinta de \<open>A\<close>, y \<open>V\<close> en 
  caso contrario.

  Entonces, la fórmula \<open>F\<close> tiene el mismo valor para las 
  interpretaciones \<open>\<A>\<close> y \<open>\<A>'\<close>.
  \end{lema}

  En Isabelle se formaliza de la siguiente manera empleando la notación
  de \<open>fun_upd\<close>.\<close> 

lemma "A \<notin> atoms F \<Longrightarrow> (\<A>(A := V)) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
  oops

text\<open>Veamos ahora la prueba del lema.

  \begin{demostracion}
  Vamos a probar el resultado por inducción en la estructura recursiva
  de las fórmulas. De este modo, demostremos los siguientes casos.

  Sea \<open>p\<close> una fórmula atómica cualquiera tal que \<open>A\<close> no pertenece
  al conjunto de sus átomos \<open>{p}\<close>. De este modo, se tiene \<open>p \<noteq> A\<close>. 
  Por definición, el valor de la fórmula atómica \<open>p\<close> dada la 
  interpretación \<open>\<A>'\<close>, es \<open>\<A>'(p)\<close>. Como hemos visto que \<open>p \<noteq> A\<close>, 
  tenemos a su vez \<open>\<A>'(p) = \<A>(p)\<close> según la definición de \<open>\<A>'\<close>. A su
  vez, \<open>\<A>(p)\<close> es el valor de la fórmula atómica \<open>p\<close> dada la 
  interpretación \<open>\<A>\<close>, luego se tiene finalmente que ambos valores
  coinciden. 

  Sea la fórmula \<open>\<bottom>\<close>. Por definición, el valor de dicha fórmula es 
  \<open>Falso\<close> dada cualquier interpretación, luego se verifica el
  resultado en particular.

  Sea \<open>F\<close> una fórmula tal que para cualquier variable que no pertenezca
  al conjunto de sus átomos, entonces el valor de \<open>F\<close> dada la 
  interpretación \<open>\<A>\<close> coincide con su valor dada la interpretación \<open>\<A>'\<close> 
  construida como se indica en el enunciado. Vamos a demostrar el 
  resultado para la fórmula \<open>\<not> F\<close> considerando una variable \<open>A\<close> 
  cualquiera que no pertenezca al conjunto de átomos de \<open>\<not> F\<close>. Como 
  los conjuntos de átomos de \<open>F\<close> y \<open>\<not> F\<close> son el mismo, entonces \<open>A\<close> 
  tampoco pertenece al conjunto de átomos de \<open>F\<close>. De este modo, por 
  hipótesis de inducción, el valor de la fórmula \<open>F\<close> dada la 
  interpretación \<open>\<A>\<close> coincide con su valor dada la interpretación 
  \<open>\<A>'\<close>. Por otro lado, por definición tenemos que el valor de la 
  fórmula \<open>\<not> F\<close> dada \<open>\<A>\<close> es \<open>\<not> \<I>\<^sub>\<A>(F)\<close>. Por lo visto anteriormente
  según la hipótesis de inducción, esto es igual a \<open>\<not> \<I>\<^sub>\<A>\<^sub>'(F)\<close>. 
  Por último, por definición es igual al valor de \<open>\<not> F\<close> dada \<open>\<A>'\<close>, 
  como quería demostrar.

  Sean ahora las fórmulas \<open>G\<close> y \<open>H\<close> tales que, para cada una, su valor
  por la interpretación \<open>\<A>\<close> coincide con su valor dada la
  interpretación \<open>\<A>'\<close> construida como se indica en el enunciado a 
  partir de una variable que no pertenezca al conjunto de sus átomos. 
  Veamos que se verifica el resultado para la fórmula \<open>G \<and> H\<close>.
  Sea \<open>A\<close> una variable proposicional que no pertenece al conjunto de
  átomos de \<open>G \<and> H\<close>. Por definición, dicho conjunto es igual a la unión
  del conjunto de átomos de \<open>G\<close> y el conjunto de átomos de \<open>H\<close>.
  Por tanto, en particular \<open>A\<close> no pertenece al conjunto de átomos de
  \<open>G\<close> y, por hipótesis de inducción, el valor de \<open>G\<close> dada la
  interpretación \<open>\<A>\<close> coincide con su valor dada la
  interpretación \<open>\<A>'\<close>. Por el mismo motivo, \<open>A\<close> no pertenece al
  conjunto de átomos de \<open>H\<close> y, por hipótesis de inducción,
  el valor de \<open>H\<close> es el mismo dadas las interpretaciones \<open>\<A>\<close> y \<open>\<A>'\<close>. 
  Aclaradas estas observaciones, se tiene por definición que el valor 
  de la fórmula \<open>G \<and> H\<close> dada la interpretación \<open>\<A>'\<close> es 
  \<open>\<I>\<^sub>\<A>\<^sub>'(G) \<and> \<I>\<^sub>\<A>\<^sub>'(H)\<close>. Por lo demostrado anteriormente según las hipótesis
  de inducción, esto es igual a \<open>\<I>\<^sub>\<A>(G) \<and> \<I>\<^sub>\<A>(H)\<close> que, por definición, es 
  el valor de \<open>G \<and> H\<close> dada la interpretación \<open>\<A>\<close>. Por tanto, queda 
  probada la equivalencia en este caso.

  Sean las fórmulas \<open>G\<close> y \<open>H\<close> cumpliendo las hipótesis supuestas
  para el caso anterior. Veamos que el resultado se verifica para la
  fórmula \<open>G \<or> H\<close>. Sea \<open>A\<close> una variable proposicional que no pertenece
  al conjunto de átomos de \<open>G \<or> H\<close>. Por definición, dicho conjunto es
  la unión de los conjuntos de átomos de \<open>G\<close> y \<open>H\<close>. Por tanto, como se
  ha probado en el caso anterior, tenemos que \<open>A\<close> no pertenece al
  conjunto de átomos de \<open>G\<close>. Por tanto, aplicando la hipótesis de 
  inducción se tiene que el valor de \<open>G\<close> dada la interpretación \<open>\<A>\<close> 
  coincide con su valor dada la interpretación \<open>\<A>'\<close>. Análogamente 
  ocurre para la fórmula \<open>H\<close> como vimos en el caso anterior.
  Veamos la equivalencia. Por definición tenemos que el valor de la 
  fórmula \<open>G \<or> H\<close> dada la interpretación \<open>\<A>'\<close> es \<open>\<I>\<^sub>\<A>\<^sub>'(G) \<or> \<I>\<^sub>\<A>\<^sub>'(H)\<close>. Por 
  lo probado anteriormente según las hipótesis de inducicón, esto es 
  igual a \<open>\<I>\<^sub>\<A>(G) \<or> \<I>\<^sub>\<A>(H)\<close> . Por definición, se verifica que es igual al 
  valor de \<open>G \<or> H\<close> dada la interpretación \<open>\<A>\<close>, como queríamos 
  demostrar.

  Demostremos finalmente el último caso considerando las fórmulas \<open>G\<close> y
  \<open>H\<close> bajo las condiciones de los dos casos anteriores. Sea \<open>A\<close> una 
  variable proposicional que no pertenece al conjunto de átomos de 
  \<open>G \<rightarrow> H\<close>. Como dicho conjunto es la unión del conjunto de átomos de
  \<open>G\<close> y el de \<open>H\<close>, \<open>A\<close> no pertenece ni al conjunto de átomos de \<open>G\<close> ni
  al de \<open>H\<close>. Por lo tanto, por hipótesis de inducción, el valor de \<open>G\<close> 
  es el mismo dadas las interpretaciones \<open>\<A>\<close> y \<open>\<A>'\<close>, y lo mismo ocurre 
  para \<open>H\<close>. Veamos ahora la cadena de equivalencias. Por definición 
  tenemos que el valor de la fórmula \<open>G \<rightarrow> H\<close> dada la interpretación 
  \<open>\<A>'\<close> es \<open>\<I>\<^sub>\<A>\<^sub>'(G) \<rightarrow> \<I>\<^sub>\<A>\<^sub>'(H)\<close>. Análogamente a los casos anteriores por 
  las hipótesis de inducción, esto es igual a \<open>\<I>\<^sub>\<A>(G) \<rightarrow> \<I>\<^sub>\<A>(H)\<close>. Por
  definición, es igual al valor de \<open>G \<rightarrow> H\<close> dada la interpretación \<open>\<A>\<close>,
  probando así la equivalencia.
  \end{demostracion}

  Veamos a continuación la demostración detallada del lema en\\ 
  Isabelle/HOL. Para facilitar la lectura, inicialmente se ha
  probado el resultado para cada caso de la estructura de las fórmulas
  como es habitual. Además, se han empleado los lemas auxiliares 
  \<open>irrelevant_atom_atomic_l1\<close>, \<open>irrelevant_atom_not_l1\<close>,
  \<open>irrelevant_atom_and_l1\<close>, \<open>irrelevant_atom_or_l1\<close> e 
  \<open>irrelevant_atom_imp_l1\<close> para mostrar resultados sobre la no
  pertenencia a los conjuntos de átomos en cada caso. Es fácil observar 
  que no ha sido necesario el uso de lemas auxiliares en el caso de la 
  fórmula \<open>\<bottom>\<close>, pues su conjunto de átomos es el vacío.\<close>

lemma irrelevant_atom_atomic_l1:
  assumes "A \<notin> atoms (Atom x)" 
  shows "x \<noteq> A"
proof (rule notI)
  assume "x = A"
  then have "A \<in> {x}" 
    by (simp only: singleton_iff)
  also have "\<dots> = atoms (Atom x)"
    by (simp only: formula.set(1))
  finally have "A \<in> atoms (Atom x)"
    by this 
  with assms show "False"  
    by (rule notE)
qed

lemma irrelevant_atom_atomic:
  assumes "A \<notin> atoms (Atom x)" 
  shows "(\<A>(A := V)) \<Turnstile> (Atom x) \<longleftrightarrow> \<A> \<Turnstile> (Atom x)"
proof -
  have "x \<noteq> A"
    using assms
    by (rule irrelevant_atom_atomic_l1)
  have "(\<A>(A := V)) \<Turnstile> (Atom x) = (\<A>(A := V)) x"
    by (simp only: formula_semantics.simps(1))
  also have "\<dots> = \<A> x"
    using \<open>x \<noteq> A\<close>
    by (rule fun_upd_other)
  also have "\<dots> = \<A> \<Turnstile> (Atom x)"
    by (simp only: formula_semantics.simps(1))
  finally show ?thesis
    by this
qed

lemma irrelevant_atom_bot:
  assumes "A \<notin> atoms \<bottom>" 
  shows "(\<A>(A := V)) \<Turnstile> \<bottom> \<longleftrightarrow> \<A> \<Turnstile> \<bottom>"
  by (simp only: formula_semantics.simps(2))

lemma irrelevant_atom_not_l1:
  assumes "A \<notin> atoms (\<^bold>\<not> F)"
  shows   "A \<notin> atoms F"
proof
  assume "A \<in> atoms F"
  then have "A \<in> atoms (\<^bold>\<not> F)"
    by (simp only: formula.set(3)) 
  with assms show False
    by (rule notE)
qed

lemma irrelevant_atom_not:
  assumes "A \<notin> atoms F \<Longrightarrow> \<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
          "A \<notin> atoms (\<^bold>\<not> F)"
 shows "\<A>(A := V) \<Turnstile> \<^bold>\<not> F \<longleftrightarrow> \<A> \<Turnstile> \<^bold>\<not> F"
proof -
  have "A \<notin> atoms F"
    using assms(2) by (rule irrelevant_atom_not_l1)
  then have "\<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
    by (rule assms(1))
  have "\<A>(A := V) \<Turnstile> \<^bold>\<not> F = (\<not> \<A>(A := V) \<Turnstile> F)"
    by (simp only: formula_semantics.simps(3))
  also have "\<dots> = (\<not> \<A> \<Turnstile> F)"
    by (simp only: \<open>\<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F\<close>)
  also have "\<dots> = \<A> \<Turnstile> \<^bold>\<not> F"
    by (simp only: formula_semantics.simps(3))
  finally show "\<A>(A := V) \<Turnstile> \<^bold>\<not> F \<longleftrightarrow> \<A> \<Turnstile> \<^bold>\<not> F"
    by this
qed

lemma irrelevant_atom_and_l1:
  assumes "A \<notin> atoms (F \<^bold>\<and> G)"
  shows   "A \<notin> atoms F"
proof 
  assume "A \<in> atoms F"
  then have "A \<in> atoms F \<union> atoms G"
    by (rule UnI1)
  then have "A \<in> atoms (F \<^bold>\<and> G)"
    by (simp only: formula.set(4))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_and_l2:
  assumes "A \<notin> atoms (F \<^bold>\<and> G)"
  shows   "A \<notin> atoms G"
proof 
  assume "A \<in> atoms G"
  then have "A \<in> atoms F \<union> atoms G"
    by (rule UnI2)
  then have "A \<in> atoms (F \<^bold>\<and> G)"
    by (simp only: formula.set(4))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_and:
  assumes "A \<notin> atoms F \<Longrightarrow> \<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
          "A \<notin> atoms G \<Longrightarrow> \<A>(A := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
          "A \<notin> atoms (F \<^bold>\<and> G)"
  shows "\<A>(A := V) \<Turnstile> (F \<^bold>\<and> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<and> G)"
proof -
  have "A \<notin> atoms F"
    using assms(3)
    by (rule irrelevant_atom_and_l1)
  then have HF: "\<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
    by (rule assms(1))
  have "A \<notin> atoms G"
    using assms(3)
    by (rule irrelevant_atom_and_l2)
  then have HG: "\<A>(A := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
    by (rule assms(2))
  have "\<A>(A := V) \<Turnstile> (F \<^bold>\<and> G) = (\<A>(A := V) \<Turnstile> F \<and> \<A>(A := V) \<Turnstile> G)"
    by (simp only: formula_semantics.simps(4))
  also have "\<dots> = (\<A> \<Turnstile> F \<and> \<A> \<Turnstile> G)"
    by (simp only: HF HG)
  also have "\<dots> = \<A> \<Turnstile> (F \<^bold>\<and> G)"
    by (simp only: formula_semantics.simps(4))
  finally show "\<A>(A := V) \<Turnstile> (F \<^bold>\<and> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<and> G)"
    by this
qed

lemma irrelevant_atom_or_l1:
  assumes "A \<notin> atoms (F \<^bold>\<or> G)"
  shows   "A \<notin> atoms F"
proof 
  assume "A \<in> atoms F"
  then have "A \<in> atoms F \<union> atoms G"
    by (rule UnI1)
  then have "A \<in> atoms (F \<^bold>\<or> G)"
    by (simp only: formula.set(5))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_or_l2:
  assumes "A \<notin> atoms (F \<^bold>\<or> G)"
  shows   "A \<notin> atoms G"
proof 
  assume "A \<in> atoms G"
  then have "A \<in> atoms F \<union> atoms G"
    by (rule UnI2)
  then have "A \<in> atoms (F \<^bold>\<or> G)"
    by (simp only: formula.set(5))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_or:
  assumes "A \<notin> atoms F \<Longrightarrow> \<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
          "A \<notin> atoms G \<Longrightarrow> \<A>(A := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
          "A \<notin> atoms (F \<^bold>\<or> G)"
  shows   "\<A>(A := V) \<Turnstile> (F \<^bold>\<or> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<or> G)"
proof -
  have "A \<notin> atoms F"
    using assms(3)
    by (rule irrelevant_atom_or_l1)
  then have HF: "\<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
    by (rule assms(1))
  have "A \<notin> atoms G"
    using assms(3)
    by (rule irrelevant_atom_or_l2)
  then have HG: "\<A>(A := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
    by (rule assms(2))
  have "\<A>(A := V) \<Turnstile> (F \<^bold>\<or> G) = (\<A>(A := V) \<Turnstile> F \<or> \<A>(A := V) \<Turnstile> G)"
    by (simp only: formula_semantics.simps(5))
  also have "\<dots> = (\<A> \<Turnstile> F \<or> \<A> \<Turnstile> G)"
    by (simp only: HF HG)
  also have "\<dots> = \<A> \<Turnstile> (F \<^bold>\<or> G)"
    by (simp only: formula_semantics.simps(5))
  finally show "\<A>(A := V) \<Turnstile> (F \<^bold>\<or> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<or> G)"
    by this
qed

lemma irrelevant_atom_imp_l1:
  assumes "A \<notin> atoms (F \<^bold>\<rightarrow> G)"
  shows   "A \<notin> atoms F"
proof 
  assume "A \<in> atoms F"
  then have "A \<in> atoms F \<union> atoms G"
    by (rule UnI1)
  then have "A \<in> atoms (F \<^bold>\<rightarrow> G)"
    by (simp only: formula.set(6))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_imp_l2:
  assumes "A \<notin> atoms (F \<^bold>\<rightarrow> G)"
  shows   "A \<notin> atoms G"
proof 
  assume "A \<in> atoms G"
  then have "A \<in> atoms F \<union> atoms G"
    by (rule UnI2)
  then have "A \<in> atoms (F \<^bold>\<rightarrow> G)"
    by (simp only: formula.set(6))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_imp:
  assumes "A \<notin> atoms F \<Longrightarrow> \<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
          "A \<notin> atoms G \<Longrightarrow> \<A>(A := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
          "A \<notin> atoms (F \<^bold>\<rightarrow> G)"
  shows "\<A>(A := V) \<Turnstile> (F \<^bold>\<rightarrow> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<rightarrow> G)"
proof -
  have "A \<notin> atoms F"
    using assms(3)
    by (rule irrelevant_atom_imp_l1)
  then have HF: "\<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
    by (rule assms(1))
  have "A \<notin> atoms G"
    using assms(3)
    by (rule irrelevant_atom_imp_l2)
  then have HG: "\<A>(A := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
    by (rule assms(2))
  have "\<A>(A := V) \<Turnstile> (F \<^bold>\<rightarrow> G) = (\<A>(A := V) \<Turnstile> F \<longrightarrow> \<A>(A := V) \<Turnstile> G)"
    by (simp only: formula_semantics.simps(6))
  also have "\<dots> = (\<A> \<Turnstile> F \<longrightarrow> \<A> \<Turnstile> G)"
    by (simp only: HF HG)
  also have "\<dots> = \<A> \<Turnstile> (F \<^bold>\<rightarrow> G)"
    by (simp only: formula_semantics.simps(6))
  finally show "\<A>(A := V) \<Turnstile> (F \<^bold>\<rightarrow> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<rightarrow> G)"
    by this
qed

lemma "A \<notin> atoms F \<Longrightarrow> (\<A>(A := V)) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
proof (induction F)
  case (Atom x)
  then show ?case by (rule irrelevant_atom_atomic)
next
  case Bot
  then show ?case by (rule irrelevant_atom_bot)
next
  case (Not F)
  then show ?case by (rule irrelevant_atom_not)
next
  case (And F1 F2)
  then show ?case by (rule irrelevant_atom_and)
next
  case (Or F1 F2)
  then show ?case by (rule irrelevant_atom_or)
next
  case (Imp F1 F2)
  then show ?case by (rule irrelevant_atom_imp)
qed

text \<open>Por último, su demostración automática.\<close>

lemma irrelevant_atom: 
  "A \<notin> atoms F \<Longrightarrow> (\<A>(A := V)) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
  by (induction F) simp_all

text \<open>Procedamos con el siguiente resultado de la sección.

  \begin{lema}
    Si dos interpretaciones coinciden sobre el conjunto de átomos de una 
    fórmula, entonces dicha fórmula tiene el mismo valor para ambas
    interpretaciones. 
  \end{lema}

  Su formalización en Isabelle es la siguiente.\<close>

lemma "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
  oops

text \<open>Vamos a probar el resultado.

  \begin{demostracion}
    La prueba sigue el esquema de inducción sobre la estructura de las
    fórmulas. De este modo, procedamos con la demostración de cada
    caso.

    En primer lugar sea una fórmula atómica \<open>p\<close>, donde \<open>p\<close> es una 
    variable proposicional cualquiera. Sean las interpretaciones
    \<open>\<A>\<^sub>1\<close> y \<open>\<A>\<^sub>2\<close> tales que toman los mismos valores sobre el conjunto de
    átomos de \<open>p\<close>. Veamos que el valor de \<open>p\<close> dada \<open>\<A>\<^sub>1\<close> coincide con
    su valor dada \<open>\<A>\<^sub>2\<close>. Por definición, el valor de \<open>p\<close> dada la
    interpretación \<open>\<A>\<^sub>1\<close> es \<open>\<A>\<^sub>1(p)\<close>. Como el conjunto de átomos de
    \<open>p\<close> es \<open>{p}\<close>, se tiene por hipótesis que \<open>\<A>\<^sub>1(p) = \<A>\<^sub>2(p)\<close>.
    Finalmente, aplicando la definición, esto es igual al valor de la 
    fórmula \<open>p\<close> dada la interpretación \<open>\<A>\<^sub>2\<close>, como queríamos probar.

    Consideremos ahora la fórmula \<open>\<bottom>\<close> y dos interpretaciones en las 
    condiciones del enunciado. Es fácil observar que, como el valor de 
    \<open>\<bottom>\<close> es \<open>Falso\<close> dada cualquier interpretación, se tiene en 
    particular el resultado.

    Sea una fórmula \<open>F\<close> tal que, si dos interpretaciones coinciden sobre
    el conjunto de átomos de \<open>F\<close>, entonces el valor de \<open>F\<close> es el mismo
    para ambas interpretaciones. Sean dos interpretaciones cualesquiera
    \<open>\<A>\<^sub>1\<close> y \<open>\<A>\<^sub>2\<close> que toman los mismos valores sobre el conjunto de
    átomos de \<open>\<not> F\<close>. Vamos a probar que el valor de \<open>\<not> F\<close> dada \<open>\<A>\<^sub>1\<close>
    coincide con su valor dada \<open>\<A>\<^sub>2\<close>.
    Observemos que, como el conjunto de átomos de \<open>F\<close> y \<open>\<not> F\<close>
    coinciden, se tiene por hipótesis de inducción que el valor de \<open>F\<close>
    dada \<open>\<A>\<^sub>1\<close> coincide con su valor dada \<open>\<A>\<^sub>2\<close>. Por otro lado, por
    definición, el valor de \<open>\<not> F\<close> dada \<open>\<A>\<^sub>1\<close> es la negación del valor
    de \<open>F\<close> dada \<open>\<A>\<^sub>1\<close>. Por la observación anterior, esto es igual a la
    negación del valor de \<open>F\<close> dada \<open>\<A>\<^sub>2\<close> que, por definición, es el
    valor de \<open>\<not> F\<close> dada \<open>\<A>\<^sub>2\<close>, probando así el resultado.

    Consideremos las fórmulas \<open>F\<close> y \<open>G\<close> con las mismas hipótesis que
    la fórmula del caso anterior. Sean las interpretaciones \<open>\<A>\<^sub>1\<close> y \<open>\<A>\<^sub>2\<close> 
    tales que coinciden sobre el conjunto de átomos de \<open>F \<and> G\<close>. Vamos a
    probar que el valor de \<open>F \<and> G\<close> dada \<open>\<A>\<^sub>1\<close> es el mismo que dada \<open>\<A>\<^sub>2\<close>.
    Como el conjunto de átomos de \<open>F \<and> G\<close> es la unión del conjunto de
    átomos de \<open>F\<close> y el conjunto de átomos de \<open>G\<close>, tenemos que \<open>\<A>\<^sub>1\<close> y 
    \<open>\<A>\<^sub>2\<close> coinciden sobre los elementos de dicha unión. En particular,
    coinciden sobre los elementos del conjunto de átomos de \<open>F\<close> y, por
    hipótesis de inducción, tenemos que el valor de \<open>F\<close> dada \<open>\<A>\<^sub>1\<close> 
    coincide con su valor dada \<open>\<A>\<^sub>2\<close>. Del mismo modo, las
    interpretaciones anteriores coinciden también sobre los elementos
    del conjunto de átomos de \<open>G\<close> luego, aplicando análogamente la 
    hipótesis de inducción, tenemos que el valor de \<open>G\<close> es el mismo 
    para las interpretaciones \<open>\<A>\<^sub>1\<close> y \<open>\<A>\<^sub>2\<close>. Veamos ahora que el valor
    de \<open>F \<and> G\<close> también coincide para dichas interpretaciones.
    Por definición, el valor de \<open>F \<and> G\<close> dada \<open>\<A>\<^sub>1\<close> es la conjunción
    del valor de \<open>F\<close> dada \<open>\<A>\<^sub>1\<close> y el valor de \<open>G\<close> dada \<open>\<A>\<^sub>1\<close>. Por lo 
    obtenido anteriormente por las hipótesis de inducción, tenemos que
    esto es igual a la conjunción del valor de \<open>F\<close> dada \<open>\<A>\<^sub>2\<close> y el
    valor de \<open>G\<close> dada \<open>\<A>\<^sub>2\<close>. Por último se tiene que esto es igual al
    valor de \<open>F \<and> G\<close> dada \<open>\<A>\<^sub>2\<close> tras aplicar la definición.

    Volvamos a considerar \<open>F\<close> y \<open>G\<close> en las condiciones anteriores y
    dos interpretaciones \<open>\<A>\<^sub>1\<close> y \<open>\<A>\<^sub>2\<close> que coinciden sobre el
    conjunto de átomos de \<open>F \<or> G\<close>. Vamos a probar que el valor de dicha
    fórmula es el mismo para ambas interpretaciones.
    De manera análoga al caso anterior, como el conjunto de átomos de
    \<open>F \<or> G\<close> es la unión del conjunto de átomos de \<open>F\<close> y el conjunto de
    átomos de \<open>G\<close>, tenemos que las interpretaciones coinciden sobre los
    elementos de esta unión. En particular, coinciden sobre el conjunto
    de átomos de \<open>F\<close>. Por tanto, por hipótesis de inducción, el valor
    de \<open>F\<close> dada \<open>\<A>\<^sub>1\<close> coincide con su valor dada \<open>\<A>\<^sub>2\<close>. Igualmente 
    obtenemos que las interpretaciones coinciden sobre el conjunto de
    átomos de \<open>G\<close> y, aplicando de nuevo hipótesis de inducción, el 
    valor de \<open>G\<close> es el mismo para ambas interpretaciones. 
    Por otra parte, por definición tenemos que le valor de \<open>F \<or> G\<close> dada
    la interpretación \<open>\<A>\<^sub>1\<close> es la disyunción entre el valor de \<open>F\<close> dada
    \<open>\<A>\<^sub>1\<close> y el valor de \<open>G\<close> dada \<open>\<A>\<^sub>1\<close>. Por las observaciones
    anteriores derivadas de las hipótesis de inducción, tenemos que
    esto es igual a la disyunción entre el valor de \<open>F\<close> dada \<open>\<A>\<^sub>2\<close> y
    el valor de \<open>G\<close> dada \<open>\<A>\<^sub>2\<close>. Por definición, esto es el valor de 
    \<open>F \<or> G\<close> dada \<open>\<A>\<^sub>2\<close>, como queríamos demostrar.

    Veamos el último caso de las fórmulas. Sean \<open>F\<close> y \<open>G\<close> fórmulas en 
    las condiciones de los casos anteriores. Consideremos las
    interpretaciones \<open>\<A>\<^sub>1\<close> y \<open>\<A>\<^sub>2\<close> que coinciden sobre los elementos
    del conjunto de átomos de \<open>F \<rightarrow> G\<close>. Probemos que el valor de 
    \<open>F \<rightarrow> G\<close> es el mismo para ambas interpretaciones.
    Por definición, el conjunto de átomos de \<open>F \<rightarrow> G\<close> es la unión de los
    conjuntos de átomos de \<open>F\<close> y \<open>G\<close>. Por tanto, dichas
    interpretaciones coinciden sobre los elementos de dicha unión. 
    Como hemos visto en casos anteriores, en particular coinciden sobre
    los átomos de \<open>F\<close> luego, por hipótesis de inducción, el valor de 
    \<open>F\<close> dada \<open>\<A>\<^sub>1\<close> coincide con su valor dada \<open>\<A>\<^sub>2\<close>. Análogamente, las
    interpretaciones coinciden sobre los átomos de \<open>G\<close> y, por hipótesis
    de inducción, el valor de \<open>G\<close> es el mismo para ambas
    interpretaciones. Probemos que también coincide el valor de \<open>F \<rightarrow> G\<close>
    para \<open>\<A>\<^sub>1\<close> y \<open>\<A>\<^sub>2\<close>.
    Por definición, el valor de \<open>F \<rightarrow> G\<close> dada \<open>\<A>\<^sub>1\<close> es la implicación
    entre el valor de \<open>F\<close> dada \<open>\<A>\<^sub>1\<close> y el valor de \<open>G\<close> dada \<open>\<A>\<^sub>1\<close>. De
    esta manera, por las observaciones anteriores tenemos que esto es
    igual a la implicación entre el valor de \<open>F\<close> dada \<open>\<A>\<^sub>2\<close> y el valor
    de \<open>G\<close> dada \<open>\<A>\<^sub>2\<close>. Finalmente, por definición, esto es el valor de
    \<open>F \<rightarrow> G\<close> dada la interpretación \<open>\<A>\<^sub>2\<close>, probando así el resultado.    
  \end{demostracion}

  Probemos ahora el lema de forma detallada en Isabelle, haciendo cada
  caso de la estructura de las fórmulas por separado y empleando lemas
  auxiliares sobre la pertenencia a los conjuntos de átomos cuando sea 
  necesario.\<close>

lemma relevant_atoms_same_semantics_atomic_l1:
  "x \<in> atoms (Atom x)"
proof 
  show "x \<in> {x}"
    by (simp only: singleton_iff)
next
  show "{x} \<subseteq> atoms (Atom x)"
    by (simp only: formula.set(1))
qed

lemma relevant_atoms_same_semantics_atomic: 
  assumes "\<forall>k \<in> atoms (Atom x). \<A>\<^sub>1 k = \<A>\<^sub>2 k"
  shows   "\<A>\<^sub>1 \<Turnstile> Atom x \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> Atom x"
proof -
  have "\<A>\<^sub>1 \<Turnstile> Atom x = \<A>\<^sub>1 x"
    by (simp only: formula_semantics.simps(1))
  also have "\<dots> = \<A>\<^sub>2 x"
    using  assms(1)
    by (simp only: relevant_atoms_same_semantics_atomic_l1)
  also have "\<dots> = \<A>\<^sub>2 \<Turnstile> Atom x"
    by (simp only: formula_semantics.simps(1))
  finally show ?thesis
    by this
qed

text \<open>Para las fórmulas atómicas, se observa el uso del lema 
  auxiliar\\ \<open>relevant_atoms_same_semantics_atomic_l\<close>. Sigamos con los
  siguientes casos.\<close>

lemma relevant_atoms_same_semantics_bot: 
  assumes "\<forall>k \<in> atoms \<bottom>. \<A>\<^sub>1 k = \<A>\<^sub>2 k"
  shows "\<A>\<^sub>1 \<Turnstile> \<bottom> \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> \<bottom>"
  by (simp only: formula_semantics.simps(2))

lemma relevant_atoms_same_semantics_not: 
  assumes "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
          "\<forall>k \<in> atoms (\<^bold>\<not> F). \<A>\<^sub>1 k = \<A>\<^sub>2 k"
        shows "\<A>\<^sub>1 \<Turnstile> (\<^bold>\<not> F) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (\<^bold>\<not> F)"
proof -
  have "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(2)
    by (simp only: formula.set(3))
  then have H:"\<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
    by (simp only: assms(1))
  have "\<A>\<^sub>1 \<Turnstile> (\<^bold>\<not> F) = (\<not> \<A>\<^sub>1 \<Turnstile> F)"
    by (simp only: formula_semantics.simps(3))
  also have "\<dots> = (\<not> \<A>\<^sub>2 \<Turnstile> F)"
    using H by (rule arg_cong)
  also have "\<dots> = \<A>\<^sub>2 \<Turnstile> (\<^bold>\<not> F)"
    by (simp only: formula_semantics.simps(3))
  finally show ?thesis
    by this
qed

text \<open>Para los casos de la fórmula \<open>\<bottom>\<close> y la negación \<open>\<not> F\<close> no han sido
  necesarios los lemas auxiliares pues, en el primer caso, el conjunto
  de átomos es el vacío y, en el segundo caso, el conjunto de átomos de
  \<open>\<not> F\<close> coincide con el de \<open>F\<close>. Finalmente, introducimos los siguientes 
  lemas auxiliares para facilitar las demostraciones detalladas en 
  Isabelle de los casos correspondientes a las conectivas binarias.\<close>

lemma forall_union1: 
  assumes "\<forall>x \<in> A \<union> B. P x"
  shows "\<forall>x \<in> A. P x"
proof (rule ballI)
  fix x
  assume "x \<in> A"
  then have "x \<in> A \<union> B" 
    by (simp only: UnI1)
  then show "P x" 
    by (simp only: assms)
qed

lemma forall_union2:
  assumes "\<forall>x \<in> A \<union> B. P x"
  shows "\<forall>x \<in> B. P x"
proof (rule ballI)
  fix x
  assume "x \<in> B"
  then have "x \<in> A \<union> B" 
    by (simp only: UnI2)
  then show "P x" 
    by (simp only: assms)
qed

text \<open>Empleando dichos resultados veamos las demostraciones detalladas
  de los tres últimos casos y, por último, la demostración detallada
  del lema completo en Isabelle.\<close>

lemma relevant_atoms_same_semantics_and: 
  assumes "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
          "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G"
          "\<forall>k \<in> atoms (F \<^bold>\<and> G). \<A>\<^sub>1 k = \<A>\<^sub>2 k"
        shows "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<and> G) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (F \<^bold>\<and> G)"
proof -
  have H:"\<forall>k \<in> atoms F \<union> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(3)
    by (simp only: formula.set(4))
  then have "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k"
    by (rule forall_union1)
  then have H1:"\<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
    by (simp only: assms(1))
  have "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k"
    using H by (rule forall_union2)
  then have H2:"\<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G"
    by (simp only: assms(2))
  have "\<A>\<^sub>1 \<Turnstile> F \<^bold>\<and> G = (\<A>\<^sub>1 \<Turnstile> F \<and> \<A>\<^sub>1 \<Turnstile> G)"
    by (simp only: formula_semantics.simps(4))
  also have "\<dots> = (\<A>\<^sub>2 \<Turnstile> F \<and> \<A>\<^sub>2 \<Turnstile> G)"
    using H1 H2 by (rule arg_cong2)
  also have "\<dots> = \<A>\<^sub>2 \<Turnstile> F \<^bold>\<and> G"
    by (simp only: formula_semantics.simps(4))
  finally show ?thesis 
    by this
qed

lemma relevant_atoms_same_semantics_or: 
  assumes "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
          "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G"
          "\<forall>k \<in> atoms (F \<^bold>\<or> G). \<A>\<^sub>1 k = \<A>\<^sub>2 k"
     shows "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<or> G) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (F \<^bold>\<or> G)"
proof -
  have H:"\<forall>k \<in> atoms F \<union> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(3)
    by (simp only: formula.set(5))
  then have "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k"
    by (rule forall_union1)
  then have H1:"\<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
    by (simp only: assms(1))
  have "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k"
    using H by (rule forall_union2)
  then have H2:"\<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G"
    by (simp only: assms(2))
  have "\<A>\<^sub>1 \<Turnstile> F \<^bold>\<or> G = (\<A>\<^sub>1 \<Turnstile> F \<or> \<A>\<^sub>1 \<Turnstile> G)"
    by (simp only: formula_semantics.simps(5))
  also have "\<dots> = (\<A>\<^sub>2 \<Turnstile> F \<or> \<A>\<^sub>2 \<Turnstile> G)"
    using H1 H2 by (rule arg_cong2)
  also have "\<dots> = \<A>\<^sub>2 \<Turnstile> F \<^bold>\<or> G"
    by (simp only: formula_semantics.simps(5))
  finally show ?thesis 
    by this
qed

lemma relevant_atoms_same_semantics_imp: 
  assumes "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
          "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G"
          "\<forall>k \<in> atoms (F \<^bold>\<rightarrow> G). \<A>\<^sub>1 k = \<A>\<^sub>2 k"
     shows "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<rightarrow> G) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (F \<^bold>\<rightarrow> G)"
proof -
  have H:"\<forall>k \<in> atoms F \<union> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(3)
    by (simp only: formula.set(6))
  then have "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k"
    by (rule forall_union1)
  then have H1:"\<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
    by (simp only: assms(1))
  have "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k"
    using H by (rule forall_union2)
  then have H2:"\<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G"
    by (simp only: assms(2))
  have "\<A>\<^sub>1 \<Turnstile> F \<^bold>\<rightarrow> G = (\<A>\<^sub>1 \<Turnstile> F \<longrightarrow> \<A>\<^sub>1 \<Turnstile> G)"
    by (simp only: formula_semantics.simps(6))
  also have "\<dots> = (\<A>\<^sub>2 \<Turnstile> F \<longrightarrow> \<A>\<^sub>2 \<Turnstile> G)"
    using H1 H2 by (rule arg_cong2)
  also have "\<dots> = \<A>\<^sub>2 \<Turnstile> F \<^bold>\<rightarrow> G"
    by (simp only: formula_semantics.simps(6))
  finally show ?thesis 
    by this
qed

lemma "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
proof (induction F)
case (Atom x)
  then show ?case by (rule relevant_atoms_same_semantics_atomic)
next
  case Bot
then show ?case by (rule relevant_atoms_same_semantics_bot)
next
  case (Not F)
then show ?case by (rule relevant_atoms_same_semantics_not)
next
  case (And F1 F2)
  then show ?case by (rule relevant_atoms_same_semantics_and)
next
case (Or F1 F2)
  then show ?case by (rule relevant_atoms_same_semantics_or)
next
  case (Imp F1 F2)
  then show ?case by (rule relevant_atoms_same_semantics_imp)
qed

text \<open>Su demostración automática es la siguiente.\<close>

lemma relevant_atoms_same_semantics: 
   "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
  by (induction F) simp_all

section \<open>Semántica de fórmulas con conectivas generalizadas\<close>

text \<open>Por último mostraremos varios resultados relativos a la semántica
  de las fórmulas construidas con conectivas generalizadas.

  \begin{lema}
    La fórmula \<open>\<top>\<close> es una tautología.
  \end{lema}

  En otras palabras, toda interpretación es modelo de la fórmula \<open>\<top>\<close>. 
  Veamos su prueba.

  \begin{demostracion}
    Sea una interpretación cualquiera \<open>\<A>\<close>. Es obvio que, aplicando la
    propiedad reflexiva de la implicación, tenemos que es \<open>Verdadero\<close>
    semánticamente que valor de \<open>\<bottom>\<close> dada \<open>\<A>\<close> se implique a sí mismo. 
    Por definición, se tiene que la implicación anterior es, a su vez, 
    equivalente al valor de la fórmula \<open>\<bottom> \<rightarrow> \<bottom>\<close> dada la interpretación 
    \<open>\<A>\<close>. Según la definición de \<open>\<top>\<close>, tenemos que esto es
    equivalente al valor de la fórmula \<open>\<top>\<close> dada la interpretación \<open>\<A>\<close>.
    Finalmente, mediante esta cadena de equivalencias se observa que
    el valor de \<open>\<top>\<close> dada una interpretación \<open>\<A>\<close> cualquiera es 
    \<open>Verdadero\<close> como queríamos probar.    
  \end{demostracion}

  En Isabelle se enuncia y demuestra de manera detallada como sigue.\<close>

lemma "\<A> \<Turnstile> \<top>" 
proof -
 have "\<A> \<Turnstile> \<bottom> \<longrightarrow> \<A> \<Turnstile> \<bottom>" 
   by (rule imp_refl)
 then have "\<A> \<Turnstile> (\<bottom> \<^bold>\<rightarrow> \<bottom>)"
   by (simp only: formula_semantics.simps(6))
 thus "\<A> \<Turnstile> \<top>" unfolding Top_def by this
qed

text \<open>Asimismo se muestra su demostración automática.\<close>
  
lemma top_semantics: 
  "\<A> \<Turnstile> \<top>" 
  unfolding Top_def 
  by simp 

text \<open>Veamos ahora resultados relativos a la semántica de la conjunción
  y disyunción generalizadas.

  \begin{lema}
    Una interpretación es modelo de la conjunción generalizada de una 
    lista de fórmulas si y solo si es modelo de cada fórmula de la
    lista.
  \end{lema}

  Su formalización en Isabelle es la siguiente.\<close>

lemma "\<A> \<Turnstile> \<^bold>\<And>Fs \<longleftrightarrow> (\<forall>f \<in> set Fs. \<A> \<Turnstile> f)"
  oops

text \<open>Como podemos observar, en el enunciado de la derecha hemos
  empleado \<open>set\<close> para cambiar al tipo conjuntos la lista de fórmulas,
  pues esto permite emplear el cuantificador universal.

  Procedamos con la prueba del lema.

  \begin{demostracion}
   La prueba se basa en el esquema de inducción sobre listas de
   fórmulas. Para ello, demostraremos el resultado mediante cadenas de
   equivalencias en los siguientes casos.

   En primer lugar, lo probamos para la lista vacía de fórmulas. Sea la
   interpretación \<open>\<A>\<close> tal que es modelo de la conjunción generalizada
   de la lista vacía. Por definición de la conjunción generalizada,
   \<open>\<A>\<close> es modelo de \<open>\<not> \<bottom>\<close>. Aplicando la definición del valor de una
   fórmula dada una interpretación para el caso de la negación,
   tenemos que esto es equivalente a que \<open>\<A>\<close> no es modelo de \<open>\<bottom>\<close>.
   Análogamente, como sabemos que el valor de \<open>\<bottom>\<close> es \<open>Falso\<close> para 
   cualquier interpretación, se tiene que lo anterior es equivalente a
   \<open>\<not> Falso\<close>, es decir, \<open>Verdad\<close>. Por otro lado, por propiedades
   del conjunto vacío, se tiene que toda propiedad sobre sus elementos
   es verdadera. Por tanto, lo anterior es equivalente a decir que \<open>\<A>\<close> 
   es modelo de todos los elementos del conjunto vacío. Es decir, \<open>\<A>\<close>
   es modelo de todos los elementos de la lista vacía, como queríamos
   demostrar. 

   Consideramos ahora la interpretación \<open>\<A>\<close> y el conjunto de fórmulas
   \<open>Fs\<close> de modo que \<open>\<A>\<close> es modelo de \<open>Fs\<close> si y solo si es modelo de 
   cada fórmula de \<open>Fs\<close>. Veamos ahora que se verifica la propiedad para
   la lista \<open>F#Fs\<close> formada al añadir la fórmula \<open>F\<close>.
   En primer lugar, si \<open>\<A>\<close> es modelo de la conjunción generalizada de
   \<open>F#Fs\<close>, por definición de dicha conjunción, esto es equivalente a
   que \<open>\<A>\<close> es modelo de la conjunción de \<open>F\<close> y la conjunción
   generalizada de \<open>Fs\<close>. Según el valor de una fórmula dada una
   interpretación, esto es a su vez equivalente a la conjunción de
   "\<open>\<A>\<close> es modelo de \<open>F\<close>" y "\<open>\<A>\<close> es modelo de la conjunción 
   generalizada de \<open>Fs\<close>". Aplicando la hipótesis de inducción sobre el 
   segundo término de la conjunción, es equivalente a la conjunción de 
   "\<open>\<A>\<close> es  modelo de \<open>F\<close>" y "\<open>\<A>\<close> es modelo de toda fórmula del 
   conjunto formado por los elementos de \<open>Fs\<close>". Equivalentemente, \<open>\<A>\<close> 
   es modelo de toda fórmula del conjunto formado por la unión de \<open>{F}\<close> 
   y el conjunto de los elementos de \<open>Fs\<close>. Es decir, \<open>\<A>\<close> es modelo de 
   toda fórmula del conjunto formado por los elementos de \<open>F#Fs\<close>, 
   probando así el resultado.
  \end{demostracion}

  Veamos ahora su demostración detallada en Isabelle. Primero se
  probarán los dos casos correspondientes a la estructura de listas por
  separado.\<close>

lemma BigAnd_semantics_nil: "\<A> \<Turnstile> \<^bold>\<And>[] \<longleftrightarrow> (\<forall>f \<in> set []. \<A> \<Turnstile> f)"
proof - 
  have "\<A> \<Turnstile> \<^bold>\<And>[] = \<A> \<Turnstile> (\<^bold>\<not>\<bottom>)"
    by (simp only: BigAnd.simps(1))
  also have "\<dots> = (\<not> \<A> \<Turnstile> \<bottom>)"
    by (simp only: formula_semantics.simps(3))
  also have "\<dots> = (\<not> False)"
    by (simp only: formula_semantics.simps(2))
  also have "\<dots> = True"
    by (simp only: not_False_eq_True)
  also have "\<dots> = (\<forall>f \<in> \<emptyset>. \<A> \<Turnstile> f)"
    by (simp only: ball_empty) 
  also have "\<dots> = (\<forall>f \<in> set []. \<A> \<Turnstile> f)"
    by (simp only: list.set)
  finally show ?thesis
    by this
qed

text \<open>\comentario{DUDA: Bigprop1 es el enunciado de ball simps(7), un 
  lema de Isabelle que debería permitir la demostración.
  Sin embargo, da error. De hecho, ni siquiera puedo demostrar Bigprop1
  usando dicho lema porque también da error.}\<close>

find_theorems name: ball_simps

lemma Bigprop1: "(\<forall>x\<in>{a} \<union> B. P x) = (P a \<and> (\<forall>x\<in>B. P x))"
  by simp

lemma BigAnd_semantics_cons: 
  assumes "\<A> \<Turnstile> \<^bold>\<And>Fs \<longleftrightarrow> (\<forall>f \<in> set Fs. \<A> \<Turnstile> f)"
  shows "\<A> \<Turnstile> \<^bold>\<And>(F#Fs) \<longleftrightarrow> (\<forall>f \<in> set (F#Fs). \<A> \<Turnstile> f)"
proof -
  have "\<A> \<Turnstile> \<^bold>\<And>(F#Fs) = \<A> \<Turnstile> F \<^bold>\<and> \<^bold>\<And>Fs"
    by (simp only: BigAnd.simps(2))
  also have "\<dots> = (\<A> \<Turnstile> F \<and> \<A> \<Turnstile> \<^bold>\<And>Fs)"
    by (simp only: formula_semantics.simps(4))
  also have "\<dots> = (\<A> \<Turnstile> F \<and> (\<forall>f \<in> set Fs. \<A> \<Turnstile> f))"
    by (simp only: assms)
  also have "\<dots> = (\<forall>f \<in> ({F} \<union> set Fs). \<A> \<Turnstile> f)"
    by (simp only: Bigprop1)
  also have "\<dots> = (\<forall>f \<in> set (F#Fs). \<A> \<Turnstile> f)"
    by (simp only: set_insert)
  finally show ?thesis
    by this
qed

lemma "\<A> \<Turnstile> \<^bold>\<And>Fs \<longleftrightarrow> (\<forall>f \<in> set Fs. \<A> \<Turnstile> f)"
proof (induction Fs)
  case Nil
  then show ?case by (rule BigAnd_semantics_nil)
next
  case (Cons a Fs)
  then show ?case by (rule BigAnd_semantics_cons)
qed

text \<open>Su demostración automática es la siguiente.\<close>

lemma BigAnd_semantics: 
  "\<A> \<Turnstile> \<^bold>\<And>Fs \<longleftrightarrow> (\<forall>f \<in> set Fs. \<A> \<Turnstile> f)"
  by (induction Fs; simp)

text \<open>Finalmente un resultado sobre la disyunción generalizada.

  \begin{lema}
    Una interpretación es modelo de la disyunción generalizada de una 
    lista de fórmulas si y solo si es modelo de cada fórmula de la
    lista.
  \end{lema}

  Su formalización en Isabelle es la siguiente.\<close>

lemma "\<A> \<Turnstile> \<^bold>\<Or>Fs \<longleftrightarrow> (\<exists>f \<in> set Fs. \<A> \<Turnstile> f)" 
  oops

text \<open>Procedamos con la demostración del resultado.

  \begin{demostracion}
    La prueba sigue el esquema de inducción sobre la estructura de
    listas. Vamos a probar los dos casos mediante cadenas de 
    equivalencias.

    Sea la lista vacía de fórmulas y una interpretación cualquiera
    \<open>\<A>\<close>. Por definición de la disyunción generalizada, si \<open>\<A>\<close> es
    modelo de la disyunción generalizada de la lista vacía,
    equivalentemente tenemos que es modelo de \<open>\<bottom>\<close>, es decir, \<open>Falso\<close>.
    Llegados a esta contradicción, en particular, es equivalente a
    suponer que existe una fórmula en el conjunto vacío tal que \<open>\<A>\<close> es
    modelo suyo.

    Consideremos ahora la lista de fórmulas \<open>Fs\<close> y una interpretación
    \<open>\<A>\<close> tal que es modelo de \<open>Fs\<close> si y solo si es modelo de cada
    fórmula del conjunto formado por los elementos de \<open>Fs\<close>. Vamos a
    probar el resultado para la lista \<open>F#Fs\<close> dada cualquier fórmula
    \<open>F\<close>. Si \<open>\<A>\<close> es modelo de la disyunción generalizada de \<open>F#Fs\<close>, por
    definición, es equivalente a la disyunción de "\<open>\<A>\<close> es modelo de
    \<open>F\<close>" y "\<open>\<A>\<close> es modelo de la disyunción generalizada de \<open>Fs\<close>". 
    Aplicando la hipótesis de inducción, tenemos equivalentemente la
    disyunción de "\<open>\<A>\<close> es modelo de \<open>F\<close>" y "existe una fórmula
    perteneciente al conjunto de elementos de \<open>Fs\<close> tal que \<open>\<A>\<close> es
    modelo suyo". Por tanto, por propiedades de la disyunción, esto es 
    equivalente a que exista una fórmula perteneciente a la unión de
    \<open>{F}\<close> y el conjunto de los elementos de \<open>Fs\<close> que tiene a \<open>\<A>\<close> como 
    modelo. Finalmente, tenemos que esto ocurre si y solo si
    existe una fórmula del conjunto de los elementos de \<open>F#Fs\<close> tal que
    \<open>\<A>\<close> sea modelo suyo, como queríamos demostrar.
  \end{demostracion}

  A continuación lo probamos de manera detallada con Isabelle/HOL, 
  haciendo previamente cada paso por separado.\<close>

lemma BigOr_semantics_nil: "\<A> \<Turnstile> \<^bold>\<Or>[] \<longleftrightarrow> (\<exists>f \<in> set []. \<A> \<Turnstile> f)" 
proof -
  have "\<A> \<Turnstile> \<^bold>\<Or>[] = \<A> \<Turnstile> \<bottom>"
    by (simp only: BigOr.simps(1))
  also have "\<dots> = False"
    by (simp only: formula_semantics.simps(2))
  also have "\<dots> = (\<exists>f \<in> \<emptyset>. \<A> \<Turnstile> f)"
    by (simp only: bex_empty)
  also have "\<dots> = (\<exists>f \<in> set []. \<A> \<Turnstile> f)"
    by (simp only: list.set)
  finally show ?thesis
    by this
qed

text \<open>\comentario{DUDA: Análogamente, Bigprop2 es el enunciado de 
  bex simps(5), un lema de Isabelle que debería permitir la 
  demostración. Sin embargo, da error. De hecho, ni siquiera puedo 
  demostrar Bigprop2 usando dicho lema porque también da error.}\<close>

find_theorems name: bex_simps

lemma Bigprop2: "(\<exists>x\<in>{a} \<union> B. P x) = (P a \<or> (\<exists>x\<in>B. P x))"
  by simp

lemma BigOr_semantics_cons: 
  assumes "\<A> \<Turnstile> \<^bold>\<Or>Fs \<longleftrightarrow> (\<exists>f \<in> set Fs. \<A> \<Turnstile> f)" 
  shows "\<A> \<Turnstile> \<^bold>\<Or>(F#Fs) \<longleftrightarrow> (\<exists>f \<in> set (F#Fs). \<A> \<Turnstile> f)" 
proof -
  have "\<A> \<Turnstile> \<^bold>\<Or>(F#Fs) = \<A> \<Turnstile> F \<^bold>\<or> \<^bold>\<Or>Fs"
    by (simp only: BigOr.simps(2))
  also have "\<dots> = (\<A> \<Turnstile> F \<or> \<A> \<Turnstile> \<^bold>\<Or>Fs)"
    by (simp only: formula_semantics.simps(5))
  also have "\<dots> = (\<A> \<Turnstile> F \<or> (\<exists>f \<in> set Fs. \<A> \<Turnstile> f))"
    by (simp only: assms)
  also have "\<dots> = (\<exists>f \<in> ({F} \<union> set Fs). \<A> \<Turnstile> f)"
    by (simp only: Bigprop2)
  also have "\<dots> = (\<exists>f \<in> set (F#Fs). \<A> \<Turnstile> f)"
    by (simp only: set_insert)
  finally show ?thesis
    by this
qed

text \<open>\comentario{Añadir ball empty, list set, not False eq True,
 bex empty al glosario.}\<close>

lemma "\<A> \<Turnstile> \<^bold>\<Or>Fs \<longleftrightarrow> (\<exists>f \<in> set Fs. \<A> \<Turnstile> f)" 
proof (induction Fs)
case Nil
  then show ?case by (rule BigOr_semantics_nil)
next
  case (Cons a Fs)
then show ?case by (rule BigOr_semantics_cons)
qed

lemma BigOr_semantics: 
  "\<A> \<Turnstile> \<^bold>\<Or>Fs \<longleftrightarrow> (\<exists>f \<in> set Fs. \<A> \<Turnstile> f)" 
  by (induction Fs; simp)

section \<open>Semántica de conjuntos de fórmulas\<close>
    
text \<open>Veamos definiciones y resultados relativos a la semántica de un
  conjunto de fórmulas.
  
  En primer lugar, extendamos la noción de modelo a un conjunto de 
  fórmulas.

  \begin{definicion}
  Una interpretación es modelo de un conjunto de fórmulas si es modelo
  de todas las fórmulas del conjunto.
  \end{definicion}

  Su formalización en Isabelle es la siguiente.\<close>

definition "isModelSet \<A> S \<equiv> \<forall>F. (F\<in> S \<longrightarrow> \<A> \<Turnstile> F)"

text \<open>Continuando con los ejemplos anteriores, veamos una interpretación
  que es modelo de un conjunto de fórmulas.\<close>

notepad
begin
  fix p :: 'a

  have "isModelSet (\<A> (p := True))
     {Atom p, (Atom p \<^bold>\<and> Atom p) \<^bold>\<rightarrow> Atom p}"
    by (simp add: isModelSet_def)

end

text \<open>El siguiente resultado relaciona los conceptos de modelo de 
  una fórmula y modelo de un conjunto de fórmulas en Isabelle.
  La equivalencia se demostrará fácilmente mediante las definiciones
  de \<open>isModel\<close> e\\ \<open>isModelSet\<close>.\<close>

lemma modelSet:
  "isModelSet \<A> S \<equiv> \<forall>F. (F\<in> S \<longrightarrow> isModel \<A> F)" 
  by (simp only: isModelSet_def isModel_def)

text\<open>Veamos la noción de satisfacibilidad para un conjunto de fórmulas.

  \begin{definicion}
    Un conjunto de fórmulas es satisfacible si tiene algún modelo.
  \end{definicion}

  En otras palabras, la satisfacibilidad de un conjunto de fórmulas 
  depende de la existencia de una interpretación que sea modelo de dicho 
  conjunto, es decir, que sea modelo de todas las fórmulas del conjunto.

  En Isabelle se formaliza de la siguiente manera.\<close>

definition "sat S \<equiv> \<exists>\<A>. \<forall>F \<in> S. \<A> \<Turnstile> F" 

text \<open>En particular, se puede definir un conjunto de fórmulas 
  finitamente satisfacible.

  \begin{definicion}
    Un conjunto de fórmulas es finitamente satisfacible si todo
    subconjunto finito suyo es satisfacible.
  \end{definicion}

  Su formalización en Isabelle se muestra a continuación.\<close>

definition "fin_sat S \<equiv> (\<forall>s \<subseteq> S. finite s \<longrightarrow> sat s)"

text \<open>Veamos la noción de consecuencia lógica.

  \begin{definicion}
    Una fórmula es consecuencia lógica de un conjunto de fórmulas si
    todos los modelos del conjunto son modelos de la fórmula.
  \end{definicion}

  Teniendo en cuenta la definicón de modelo de una fórmula y modelo de
  un conjunto de fórmulas, su formalización en Isabelle es la 
  siguiente.\<close>

definition entailment :: 
  "'a formula set \<Rightarrow> 'a formula \<Rightarrow> bool" ("(_ \<TTurnstile>/ _)" 
    (* \TTurnstile *) [53,53] 53) where
  "\<Gamma> \<TTurnstile> F \<equiv> (\<forall>\<A>. ((\<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G) \<longrightarrow> (\<A> \<Turnstile> F)))"
 
text \<open>Hagamos varias observaciones sobre esta definición. En primer
  lugar, hemos usado el tipo \<open>definition\<close> para renombrar una 
  construcción no recursiva ya existente en Isabelle. Por otro
  lado, no hemos empleado \<open>isModel\<close> ni \<open>isModelSet\<close> para su definición
  ya que, de este modo, no tenemos que desplegar dichas definiciones 
  en las demostraciones detalladas y automáticas de los lemas 
  posteriores. Finalmente se puede observar la notación \<open>\<TTurnstile>\<close>. 
  En la teoría clásica no se suele emplear una nueva notación ya que se
  diferencia por el contexto, mientras que en Isabelle/HOL es 
  imprescindible.

  Llegamos así al último lema de la sección.

  \begin{lema}
    Un conjunto de fórmulas es inconsistente si y sólo si \<open>\<bottom>\<close> es
    consecuencia lógica de dicho conjunto.
  \end{lema}

  Su formalización en Isabelle es la siguiente.\<close>

lemma "\<not> sat \<Gamma> \<longleftrightarrow> \<Gamma> \<TTurnstile> \<bottom>" 
  oops

text\<open>Comencemos las demostraciones del resultado.

  \begin{demostracion}
    Vamos a probar la doble implicación mediante una cadena de
    equivalencias.

    Sea un conjunto de fórmulas \<open>\<Gamma>\<close> tal que la fórmula \<open>\<bottom>\<close> es
    consecuencia lógica de dicho conjunto. Por definición, esto es
    equivalente a decir que para toda interpretación, si esta modelo de
    \<open>\<Gamma>\<close>, entonces es a su vez modelo de \<open>\<bottom>\<close>. Por otro lado, el valor 
    de \<open>\<bottom>\<close> es \<open>Falso\<close> para cualquier interpretación. Tenemos así que 
    para toda interpretación, si es modelo de \<open>\<Gamma>\<close>, entonces implica
    \<open>Falso\<close>. Es decir, por definición de negación, para toda 
    interpretación se verifica que esta no es modelo del conjunto. En 
    otras palabras, no existe una interpretación que sea modelo de \<open>\<Gamma>\<close>. 
    Según la definición, esto es equivalente a decir que dicho conjunto 
    es insatisfacible, como queríamos demostrar.
  \end{demostracion}

  Procedamos con las pruebas en Isabelle/HOL. Como se puede observar,
  hemos enunciado la doble implicación de distinta forma para reducir 
  la demostración detallada, pues asumimos la propiedad reflexiva de 
  la doble implicación.\<close>

lemma "\<Gamma> \<TTurnstile> \<bottom> \<longleftrightarrow> \<not> sat \<Gamma>" 
proof -
  have "\<Gamma> \<TTurnstile> \<bottom> = (\<forall>\<A>. ((\<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G) \<longrightarrow> \<A> \<Turnstile> \<bottom>))"
    by (simp only: entailment_def)
  also have "\<dots> = (\<forall>\<A>. ((\<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G) \<longrightarrow> False))"
    by (simp only: formula_semantics.simps(2))
  also have "\<dots> = (\<forall>\<A>. \<not>(\<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G))"
    by (simp only: not_def)
  also have "\<dots> =  (\<not>(\<exists>\<A>. \<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G))"
    by (simp only: not_ex) 
  also have "\<dots> = (\<not> sat \<Gamma>)"
    by (simp only: sat_def)
  finally show ?thesis
    by this
qed

text \<open>Finalmente su demostración automática es la siguiente.\<close>

lemma entail_sat: 
  "\<Gamma> \<TTurnstile> \<bottom> \<longleftrightarrow> \<not> sat \<Gamma>" 
  unfolding sat_def entailment_def 
  by simp

(*<*)
end
(*>*) 
